-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryCoverMoments
-- name    : Submission_ThreeSum_TernaryCoverMoments
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:45:48.532039+00:00
-- url     : https://prove2.me/theorems/42b2dbb5-1bba-4ddc-acf2-9822c2270ad9
-- title:
--   Ternary Cover Moments
-- statement:
--   Definitions and structural lemmas for Ternary Cover Moments, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverMoments.lean

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
set_option autoImplicit false
namespace ThreeSum.TernaryCoverMoments
open Finset
open scoped BigOperators
variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq Ω]
def jointEvent (events : E → Finset Ω) {k : ℕ} (es : Fin k → E) : Finset Ω :=
  univ.filter fun w => ∀ i, w ∈ events (es i)
section Caps
variable {T : Type*} [Fintype T] [DecidableEq T]
def badMaps (X : Ω → T → ℕ) (τ : ℕ) : Finset Ω :=
  univ.filter fun w => ∃ t, τ < X w t
end Caps
end ThreeSum.TernaryCoverMoments


