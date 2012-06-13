{- |
Module      : Control.Monad.Catana
Copyright   : (c) Dustin DeWeese 2011-2012
License     : BSD3
Maintainer  : dustin.deweese@gmail.com
Stability   : experimental
Portability : portable

[Computation type:] Computations that both consume and produce elements lazily with support for advanced control flow using continuations, recursion, and parallel and serial composition.

[Binding Strategy:] Binding a function to a monadic value produces a continuation which is represented as a 'Step' that either 'Wait's for input or 'Yield's a value, and returns the next 'Step'.

[Useful for:] Lazily processing a list with complex control structures.

[Zero and plus:] mzero consumes all input with producing any output, mplus combines output of two Catana's in parallel

[Example type:] @'Catana' i o b a@

The Catana monad represents computations that are both catamorphisms and anamorphisms; they both consume and produce values.  In addition, the Catana monad represents the computation in continuation-passing style, and implements callCC.
-}

module Control.Monad.Catana (
    -- * The Catana monad
    Catana(..),
    consume,
    top,
    push,
    produce,
    stop,
    execCatana,
    runCatana,
    parallelB,
    parallelE,
    serial
    -- * Example 1: Basic usage of the Catana monad
    -- $catanaExample1

    -- * Example 2: An Example using serial and parallel data flow
    -- $catanaExample2

    -- * Example 3: An Example using recursion
    -- $fibTest
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Cont
import Control.Monad.Fix
import Data.Either
import Data.Maybe
import System.IO.Unsafe
import Control.Concurrent.MVar
import Data.Monoid

{- $catanaExample1

An example of complex control structure using Catana:

>catanaExample1 =
>  forever $ do
>    z <- callCC $ \exit -> do
>      (x, y) <- (,) <$> consume <*> consume
>      produce (x + y)
>      produce (x * y)
>      if x > 1
>        then exit 0
>        else do
>          produce (x - y)
>          produce (x / y)
>          return 1
>    produce z

Catana monads can be converted into a function over lists using 'execCatana'.

>>> execCatana catanaExample1 [1..4]
[3.0,2.0,-1.0,0.5,1.0,7.0,12.0,0.0] 

-}

{- $catanaExample2

An example using serial and parallel data flow:

>catanaExample2 = sq `serial` (ev `parallelB` od)
>  where od = forever $ do
>               x <- consume
>               when (odd x) .
>                 produce $ x * 2
>        ev = forever $ do
>               x <- consume
>               when (even x) .
>                 produce $ x + 3
>        sq = forever $ do
>               x <- consume
>               produce x
>               produce $ x ^ 2

>>> let l = 1 : execCatana catanaExample2 l
>>> take 10 l
[1,2,4,5,25,7,49,10,100,50]

-}

{- $fibTest

An example using recursion:

>fibTest :: Catana Int Int b a
>fibTest = do
>  rec fib <- return $ \x ->
>        if x <= 1
>          then produce x >> return x
>          else do f1 <- fib (x-1)
>                  f2 <- fib (x-2)
>                  produce (f1+f2)
>                  return (f1+f2)
>  forever $ consume >>= fib

>>> execCatana fibTest [3,5,7]
[1,0,1,1,2,1,0,1,1,2,1,0,1,3,1,0,1,1,2,5,1,0,1,1,2,1,0,1,3,1,0,1,1,2,5,1,0,1,1,2,1,0,1,3,8,1,0,1,1,2,1,0,1,3,1,0,1,1,2,5,13]

-}

data Catana i o b a = Catana { step :: (a -> Step i o b) -> Step i o b }

data Step i o a = Yield o (Step i o a)
                | Wait (i -> Step i o a)
                | Done a

instance Functor (Catana i o b) where
  fmap f (Catana l) = Catana $ l . (. f)

instance Applicative (Catana i o b) where
  f <*> x = Catana $ step f . flip (step . (<$> x))
  pure = Catana . flip ($)

instance Monad (Catana i o b) where
  return = pure
  m >>= f = Catana $ step m . flip (step . f)

instance MonadCont (Catana i o b) where
  callCC f = Catana $ \k -> step (f $ Catana . const . k) k

instance MonadFix (Catana i o b) where
  -- ugly and devious, but it works
  mfix f = unsafePerformIO $ do
             m <- newEmptyMVar
             return $ do
               x <- f . unsafePerformIO $ readMVar m
               unsafePerformIO (tryPutMVar m x) `seq` return x

instance MonadPlus (Catana i o b) where
  mzero = forever consume
  a `mplus` b = a `parallel` b

instance Monoid (Catana i o b a) where
  mempty = mzero
  mappend = mplus

-- |Consumes an element from the input list, returning it
-- If there is no more input, the chain of continuations ends
-- immediately; no more computations will be processed
consume :: Catana i o a i
consume = Catana Wait

-- |Returns the next input without consuming it
top :: Catana i o a i
top = Catana $ \k -> Wait (\i -> feed i (k i))

-- |Feeds an input into the next Wait step
feed :: i -> Step i o a -> Step i o a
feed i (Yield o s) = Yield o (feed i s)
feed i (Wait s) = s i
feed _ (Done x) = Done x

-- |Stops computation, ending the continuation chain
stop :: b -> Catana i o b a
stop = Catana . const . Done

-- |Pushes 'x' into the input
push :: i -> Catana i o a ()
push x = Catana $ feed x . ($())

-- |Produces 'x' in the output
produce :: o -> Catana i o a ()
produce x = Catana $ Yield x . ($())

-- |Converts a Catana monad into a function over lists
execCatana :: Catana i o a a -> [i] -> [o]
execCatana c = execSteps (step c Done)

-- |Helper for execCatana, runs the steps
execSteps :: Step i o a -> [i] -> [o]
execSteps (Yield o s) i = o : execSteps s i
execSteps (Wait f) (i:is) = execSteps (f i) is
execSteps (Wait _) [] = []
execSteps (Done x) _ = []

-- |Evaluates a Catana monad over a list returning the result and output
runCatana :: Catana i o a a -> [i] -> (Maybe a, [o])
runCatana c i = (listToMaybe x, o)
  where (x, o) = partitionEithers $ runSteps (step c Done) i

-- |Helper for runCatana, runs the steps
runSteps :: Step i o a -> [i] -> [Either a o]
runSteps (Yield o s) i = Right o : runSteps s i
runSteps (Wait f) (i:is) = runSteps (f i) is
runSteps (Wait _) [] = []
runSteps (Done x) _ = [Left x]

-- |Helper for parallelB, combine steps to consume the same input at the same time, using k as the continuation
parStepsB :: Step i o a -> Step i o b -> ((a,b) -> Step i o c) -> Step i o c

-- Yield when possible
parStepsB (Yield oA sA) (Yield oB sB) k = Yield oA . Yield oB $ parStepsB sA sB k
parStepsB (Yield oA sA) sB k = Yield oA $ parStepsB sA sB k
parStepsB sA (Yield oB sB) k = Yield oB $ parStepsB sA sB k

-- Wait for input
parStepsB (Wait fA) (Wait fB) k = Wait $ \i -> parStepsB (fA i) (fB i) k
parStepsB (Wait fA) sB k = Wait $ \i -> parStepsB (fA i) sB k
parStepsB sA (Wait fB) k = Wait $ \i -> parStepsB sA (fB i) k

-- Apply continuation to results
parStepsB (Done xA) (Done xB) k = k (xA, xB)

-- |Combine two monads to run in parallel, consuming the same input
parallelB :: Catana i o a a -> Catana i o b b -> Catana i o c (a, b)
parallelB a b = Catana $ parStepsB (step a Done) (step b Done)

-- |Helper for parallelB, combine steps to consume the same input at the same time, using k as the continuation
parStepsE :: Step i o a -> Step i o b -> (Either a b -> Step i o c) -> Step i o c

-- Yield when possible
parStepsE (Yield oA sA) (Yield oB sB) k = Yield oA . Yield oB $ parStepsE sA sB k
parStepsE (Yield oA sA) sB k = Yield oA $ parStepsE sA sB k
parStepsE sA (Yield oB sB) k = Yield oB $ parStepsE sA sB k

-- Apply continuation to result
parStepsE (Done xA) _ k = k (Left xA)
parStepsE _ (Done xB) k = k (Right xB)

-- Wait for input
parStepsE (Wait fA) (Wait fB) k = Wait $ \i -> parStepsE (fA i) (fB i) k

-- |Combine two monads to run in parallel, consuming the same input, stopping when either of them finish.
parallelE :: Catana i o a a -> Catana i o b b -> Catana i o c (Either a b)
parallelE a b = Catana $ parStepsE (step a Done) (step b Done)

-- |Combine two Catana's of the same type, at least one of which should never terminate
parallel a b = Catana $ \k -> parStepsB (step a k)
                                        (step b k) (error "parallel ran out")

serSteps :: Step io o a -> Step i io b -> (Either a b -> Step i o c) -> Step i o c

-- Yield when possible
serSteps (Yield oA sA) sB k = Yield oA $ serSteps sA sB k

-- Apply continuation to results
serSteps (Done xA) _ k = k (Left xA)
serSteps _ (Done xB) k = k (Right xB)

-- Pass output from B to A
serSteps (Wait fA) (Yield oB sB) k = serSteps (fA oB) sB k

-- Wait for input to B
serSteps sA (Wait fB) k = Wait $ \i -> serSteps sA (fB i) k

-- |Combine two monads to run in serial, the first consuming the output of the second
serial :: Catana io o a a -> Catana i io b b -> Catana i o c (Either a b)
serial a b = Catana $ serSteps (step a Done) (step b Done)
