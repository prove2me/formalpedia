-- Prove2me | Definitions.Def_Csg_IntrusionDetection
-- name    : Csg_IntrusionDetection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:42:23.881942+00:00
-- url     : https://prove2.me/theorems/55955b16-ee2d-453e-b5ef-cde57f812569
-- title:
--   Intrusion Detection
-- statement:
--   Definitions and structural lemmas for Intrusion Detection, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
set_option autoImplicit true
namespace Csg
inductive IDSState
  | healthy
  | compromised
  deriving DecidableEq, Inhabited
instance : Fintype IDSState where
  elems := {IDSState.healthy, IDSState.compromised}
  complete := by intro s; cases s <;> decide
inductive PolicyAction
  | defend1
  | defend2
  deriving DecidableEq, Inhabited
instance : Fintype PolicyAction where
  elems := {PolicyAction.defend1, PolicyAction.defend2}
  complete := by intro a; cases a <;> decide
inductive AttackAction
  | attack1
  | attack2
  deriving DecidableEq, Inhabited
instance : Fintype AttackAction where
  elems := {AttackAction.attack1, AttackAction.attack2}
  complete := by intro a; cases a <;> decide
noncomputable def idsK : IDSState → PolicyAction → AttackAction → PMF IDSState
  | _, .defend1, .attack1 => PMF.pure .healthy
  | _, .defend1, .attack2 => PMF.pure .compromised
  | _, .defend2, .attack1 => PMF.pure .compromised
  | _, .defend2, .attack2 => PMF.pure .healthy
noncomputable def idsR : IDSState → PolicyAction → AttackAction → ℝ
  | .healthy, .defend1, .attack1 => 0
  | .healthy, .defend1, .attack2 => 1
  | .healthy, .defend2, .attack1 => 1 / 2
  | .healthy, .defend2, .attack2 => 0
  | .compromised, .defend1, .attack1 => 1
  | .compromised, .defend1, .attack2 => 2
  | .compromised, .defend2, .attack1 => 3 / 2
  | .compromised, .defend2, .attack2 => 1
noncomputable def idsCSG : CSG IDSState PolicyAction AttackAction where
  K := idsK
  r := idsR
noncomputable def idsV1 : IDSState → ℝ
  | .healthy => 1 / 3
  | .compromised => 4 / 3
noncomputable def idsP : PolicyAction → ℝ
  | .defend1 => 1 / 3
  | .defend2 => 2 / 3
noncomputable def idsQ : AttackAction → ℝ
  | .attack1 => 2 / 3
  | .attack2 => 1 / 3
def idsNext : PolicyAction → AttackAction → IDSState
  | .defend1, .attack1 => .healthy
  | .defend1, .attack2 => .compromised
  | .defend2, .attack1 => .compromised
  | .defend2, .attack2 => .healthy
noncomputable def idsV2 : IDSState → ℝ
  | .healthy => 25 / 21
  | .compromised => 46 / 21
noncomputable def idsP2 : PolicyAction → ℝ
  | .defend1 => 3 / 7
  | .defend2 => 4 / 7
noncomputable def idsQ2 : AttackAction → ℝ
  | .attack1 => 4 / 7
  | .attack2 => 3 / 7
end Csg


