-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryCoverOutputCap
-- name    : Submission_ThreeSum_TernaryCoverOutputCap
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:52:38.576202+00:00
-- url     : https://prove2.me/theorems/45fde8f3-ed70-42b3-bf2c-57496a17435c
-- title:
--   Ternary Cover Output Cap
-- statement:
--   Definitions and structural lemmas for Ternary Cover Output Cap, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverOutputCap.lean

import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic
import Theorems.Thm_ThreeSum_TernaryCoverLocal_edge_data

set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryCoverOutputCap
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}
abbrev outputFiber (α π : DigitType) (q : TritWord L) := {e : LocalEdge L α π // output e = q}
def choiceCode {α π : DigitType} {q : TritWord L} (e : outputFiber α π q) :
    (i : Fin L) → Fin ((q i).val+1) := fun i =>
  ⟨(left e.val i).val, by
    have hs := (edge_data e.val).2.2.2 i
    rw [e.property] at hs
    omega⟩
end ThreeSum.TernaryCoverOutputCap


