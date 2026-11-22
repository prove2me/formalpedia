-- Prove2me | Definitions.Def_Csg_Skirmish
-- name    : Csg_Skirmish
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:41:45.853805+00:00
-- url     : https://prove2.me/theorems/018c8977-3794-47a4-bd99-ab318dfd7d01
-- title:
--   Skirmish
-- statement:
--   Definitions and structural lemmas for Skirmish, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Skirmish.lean

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
set_option autoImplicit true
namespace Csg
inductive SoldierMove
  | hide
  | run
  deriving DecidableEq, Inhabited
instance : Fintype SoldierMove where
  elems := {SoldierMove.hide, .run}
  complete := by intro a; cases a <;> decide
inductive SniperMove
  | wait
  | throw
  deriving DecidableEq, Inhabited
instance : Fintype SniperMove where
  elems := {SniperMove.wait, .throw}
  complete := by intro a; cases a <;> decide
inductive SkirmishPos
  | hide
  | wet
  | home
  deriving DecidableEq, Inhabited
instance : Fintype SkirmishPos where
  elems := {SkirmishPos.hide, .wet, .home}
  complete := by intro s; cases s <;> decide
noncomputable def skirmishK : SkirmishPos → SoldierMove → SniperMove → PMF SkirmishPos
  | .wet, _, _ => PMF.pure .wet
  | .home, _, _ => PMF.pure .hide
  | .hide, .hide, .wait => PMF.pure .hide
  | .hide, .hide, .throw => PMF.pure .home
  | .hide, .run, .wait => PMF.pure .home
  | .hide, .run, .throw => PMF.pure .wet
noncomputable def skirmishR : SkirmishPos → SoldierMove → SniperMove → ℝ := fun _ _ _ => 0
noncomputable def skirmishCSG : CSG SkirmishPos SoldierMove SniperMove where
  K := skirmishK
  r := skirmishR
end Csg


