-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ClosedBallValuationSubringToSubring
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ClosedBallValuationSubringToSubring
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:20:21.257995+00:00
-- url     : https://prove2.me/theorems/47b29655-6c5f-4ebf-b171-c5d2d6577e57
-- title:
--   Closed Ball Valuation Subring To Subring
-- statement:
--   Definitions and structural lemmas for Closed Ball Valuation Subring To Subring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ClosedBallValuationSubringToSubring.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.ClosedBallValuationSubring
variable (K : Type*) [NormedField K] [IsUltrametricDist K]
def closedBallSubring : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg b) hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simpa using ha
def closedBallValuationSubring : ValuationSubring K where
  toSubring := closedBallSubring K
  mem_or_inv_mem' := by
    intro x
    change ‖x‖ ≤ 1 ∨ ‖x⁻¹‖ ≤ 1
    rcases le_total ‖x‖ 1 with h | h
    · exact Or.inl h
    · right
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ h
def openBallIdeal : Ideal (closedBallSubring K) where
  carrier := {x | ‖(x : K)‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    exact (IsUltrametricDist.norm_add_le_max (a : K) (b : K)).trans_lt (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    have hc : ‖(c : K)‖ ≤ 1 := c.2
    change ‖(c : K) * (x : K)‖ < 1
    rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right hc (norm_nonneg _) hx
variable {K}
variable (K)
instance isLocalRing_closedBallSubring : IsLocalRing (closedBallSubring K) :=
  inferInstanceAs (IsLocalRing (closedBallValuationSubring K))
end GlobalTheory.ClosedBallValuationSubring


