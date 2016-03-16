{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}

module Main where

--------------------------------------------------------------------------------

import qualified Data.Map  as M
import qualified Data.Set  as S

import           Data.List (foldl')
import           Prelude   hiding (succ)

--------------------------------------------------------------------------------
-- * Syntax

type Var = String

type Label = Int

data Ref  = Ref Label Var
  deriving (Show)

data Lam  = Lam Label [Var] Call
  deriving (Show)

-- Both constant-time, trivially evaluable expressions.
data Exp  = RefE Ref | LamE Lam
  deriving (Show)

data Call = Call Label Exp [Exp]
  deriving (Show)

-- A lambda-term which accepts the top-level halt continuation.
type Pr = Lam

--------------------------------------------------------------------------------
-- * Syntactic functions

freeExp :: Exp -> S.Set Var
freeExp (RefE (Ref _ v))
  = S.singleton v
freeExp (LamE (Lam _ as call))
  = freeCall call `S.difference` S.fromList as

freeCall :: Call -> S.Set Var
freeCall (Call _ e1 es)
  = S.unions (freeExp e1 : map freeExp es)

-- Not easily implementable, we need some state?
binds :: Label -> S.Set Var
binds = undefined

--------------------------------------------------------------------------------
-- * Configuration for the concrete semantics

-- aka. "concrete contour set"
type Time = Int -- actually Nat

-- "The variable v when bound at time t". In effect, represents a specific
-- instance of variable.
type Bind = (Var, Time)

type BEnv = M.Map Var Time

data Clo = Clo Lam BEnv

data Proc = CloProc Clo | Halt

type Val = Proc

-- Denotable values
type D   = Val

type Conf = VEnv
type VEnv = M.Map Bind D

data State = EvalState Eval | ApplyState Apply

data Eval  = Eval Call BEnv Conf Time
data Apply = Apply Proc [D] Conf Time

--------------------------------------------------------------------------------
-- * Concrete semantics

-- State is not used as we use Nat for Time. The invariant that needs to hold
-- is:
--
--   t < succ st t
--
succ :: State -> Time -> Time
succ _ t = t + 1

-- 'A' in the thesis
evalArg :: Exp -> BEnv -> VEnv -> Maybe D
evalArg (RefE (Ref _ v)) benv venv
  = do bt <- M.lookup v benv
       M.lookup (v, bt) venv
evalArg (LamE lam) benv _
  = Just (CloProc (Clo lam benv))

-- 'I' in the thesis
programToState :: Pr -> State
programToState pr = ApplyState (Apply (CloProc (Clo pr M.empty)) [Halt] M.empty 0)

-- Fat arrow in the thesis
nextState :: State -> Maybe State
nextState st@(EvalState (Eval (Call _lbl f as) be ve t))
  = do proc <- evalArg f be ve
       as'  <- mapM (\a -> evalArg a be ve) as
       return (ApplyState (Apply proc as' ve (succ st t)))

nextState st@(ApplyState (Apply (CloProc (Clo (Lam _lbl as body) be)) as' ve t))
  = do let t'  = succ st t
       let be' = foldl' (\m k -> M.insert k t' m)     be as
       let ve' = foldl' (\m (k, v) -> M.insert k v m) ve (zip (zip as (repeat t')) as')
       return (EvalState (Eval body be' ve' t'))

nextState (ApplyState (Apply Halt _ _ _))
  = Nothing -- we should probably report this differently

--------------------------------------------------------------------------------
-- * Configuration for the abstract semantics

-- | A finite set of abstract times/contours. Singleton (e.g. Unit) means 0CFA.
-- 'Call' means 1CFA.
--
-- From the thesis: "Empirical evaluation finds that most of the benefits of an
-- environment analysis seems to be capturable with a 0CFA contour set, and that
-- running time in creases markedly with even a 1CFA contour set."
type Time' a = a

-- Apart from the Time type, the only difference is that D is now a set of
-- abstract values. (previously it was a concrete value: 'Val')

type Bind' a = (Var, Time' a)

type BEnv' a = M.Map Var (Time' a)

data Clo' a = Clo' Lam (BEnv' a)

data Proc' a = CloProc' (Clo' a) | Halt'

type Val' a = Proc' a

-- Denotable values
type D' a = S.Set (Val' a)

type Conf' a = VEnv' a
type VEnv' a = M.Map (Bind' a) (D' a)

data State' a = EvalState' (Eval' a) | ApplyState' (Apply' a)

data Eval'  a = Eval' Call (BEnv' a) (Conf' a) (Time' a)
data Apply' a = Apply' (Proc' a) [D' a] (Conf' a) (Time' a)

--------------------------------------------------------------------------------
-- * Abstracting concrete configurations

type AbstractTime a = Time -> Time' a

abstractState :: (Ord (Time' a), Ord (Val' (Time' a)))
              => AbstractTime a -> State -> State' a
abstractState at (EvalState eval)
  = EvalState' (abstractEval at eval)
abstractState at (ApplyState apply)
  = ApplyState' (abstractApply at apply)

abstractEval :: (Ord (Time' a), Ord (Val' (Time' a)))
             => AbstractTime a -> Eval -> Eval' a
abstractEval at (Eval call be conf t)
  = Eval' call (abstractBEnv at be) (abstractConf at conf) (at t)

abstractApply :: (Ord (Time' a), Ord (Val' (Time' a)))
              => AbstractTime a -> Apply -> Apply' a
abstractApply at (Apply proc as conf t)
  = Apply' (abstractProc at proc) (map (abstractD at) as) (abstractConf at conf) (at t)

abstractBEnv :: AbstractTime a -> BEnv -> BEnv' a
abstractBEnv = M.map

abstractConf :: forall a . (Ord (Time' a), Ord (Val' a))
             => AbstractTime a -> Conf -> Conf' a
abstractConf at venv =
    let
      heap :: [((Var, Time), D)]
      heap = M.toList venv

      -- TODO: It seems like a concrete time can abstract to multiple abstract
      -- times. I don't support this in this code. But multiple concrete times
      -- can abstract to same abstract times. (TODO: isn't this always the case?)

      heap' :: [((Var, Time' a), D' a)]
      heap' = map (\((v, t), d) -> ((v, at t), abstractD at d)) heap
     in
      M.fromListWith lubD' heap'

abstractProc :: AbstractTime a -> Proc -> Proc' a
abstractProc _ Halt
  = Halt'
abstractProc at (CloProc clo)
  = CloProc' (abstractClo at clo)

abstractClo :: AbstractTime a -> Clo -> Clo' a
abstractClo at (Clo lam benv) = Clo' lam (abstractBEnv at benv)

abstractD :: AbstractTime a -> D -> D' a
abstractD at val = S.singleton (abstractVal at val)

abstractVal :: AbstractTime a -> Val -> Val' a
abstractVal = abstractProc

lubD' :: Ord (Val' a) => D' a -> D' a -> D' a
lubD' = S.union

--------------------------------------------------------------------------------
-- * Abstract semantics

evalArg' :: Ord (Time' a) => Exp -> BEnv' a -> VEnv' a -> Maybe (D' a)
evalArg' (RefE (Ref _ v)) benv venv
  = do bt <- M.lookup v benv
       M.lookup (v, bt) venv
evalArg' (LamE lam) benv _
  = Just (S.singleton (CloProc' (Clo' lam benv)))

nextState' :: Ord (Time' a) => (State' a -> Time' a -> Time' a) -> State' a -> Maybe [State' a]
nextState' succ' st@(EvalState' (Eval' (Call _lbl f as) be ve t))
  = do let t' = succ' st t
       proc ::  D' a  <- evalArg' f be ve
       as'  :: [D' a] <- mapM (\a -> evalArg' a be ve) as
       return (map (\p -> ApplyState' (Apply' p as' ve t')) (S.toList proc))

nextState' succ' st@(ApplyState' (Apply' (CloProc' (Clo' (Lam _lbl as body) be)) as' ve t))
  = do let t'  = succ' st t
       let be' = foldl' (\m k -> M.insert k t' m)     be as
       let ve' = foldl' (\m (k, v) -> M.insert k v m) ve (zip (zip as (repeat t')) as')
       return [EvalState' (Eval' body be' ve' t')]
