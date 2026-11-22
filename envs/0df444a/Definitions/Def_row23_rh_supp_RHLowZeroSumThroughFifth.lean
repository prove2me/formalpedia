-- Prove2me | Definitions.Def_row23_rh_supp_RHLowZeroSumThroughFifth
-- name    : row23_rh_supp_RHLowZeroSumThroughFifth
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T22:28:37.609174+00:00
-- url     : https://prove2.me/theorems/4658ae7a-9308-4b8e-b841-4535f9af863c
-- title:
--   Row 23 RH support: RHLowZeroSumThroughFifth
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLowZeroSumBelowWideSlab
import Definitions.Def_row23_rh_supp_RHLowSlabSecondFinal
import Definitions.Def_row23_rh_supp_RHLowSlabThirdFinal
import Definitions.Def_row23_rh_supp_RHLowSlabFourthFinal
import Definitions.Def_row23_rh_supp_RHLowSlabFifthFinal
set_option autoImplicit false
set_option maxHeartbeats 20000000
noncomputable section
open Complex Finset DusartSmoothing
namespace RHLowZeroSum

theorem no_zero_in_slab (a b : ℝ) (h : EdgeClearGlue.SlabClear a b)
    (ρ : ℂ) (hz : RvM.IsNontrivialZero ρ) (ha : a ≤ ρ.im) (hb : ρ.im ≤ b) : False := by
  have hn := h ρ.re ρ.im hz.2.1 hz.2.2 ha hb
  exact hn (by simpa only [Complex.re_add_im] using hz.1)

theorem no_positive_zero_to_103_16 (ρ : ℂ) (hz : RvM.IsNontrivialZero ρ)
    (hp : 0 < ρ.im) (hu : ρ.im ≤ (103/16:ℝ)) : False := by
  by_cases h1 : ρ.im ≤ (101/16:ℝ)
  · exact no_positive_zero_to_101_16 ρ hz hp h1
  by_cases h2 : ρ.im ≤ (203/32:ℝ)
  · exact no_zero_in_slab _ _ RHLowSlabSecondPilot.slab_clear ρ hz (le_of_not_ge h1) h2
  by_cases h3 : ρ.im ≤ (51/8:ℝ)
  · exact no_zero_in_slab _ _ RHLowSlabThirdPilot.slab_clear ρ hz (le_of_not_ge h2) h3
  by_cases h4 : ρ.im ≤ (205/32:ℝ)
  · exact no_zero_in_slab _ _ RHLowSlabFourthPilot.slab_clear ρ hz (le_of_not_ge h3) h4
  · exact no_zero_in_slab _ _ RHLowSlabFifthPilot.slab_clear ρ hz (le_of_not_ge h4) hu

theorem reciprocal_sum_below_103_16 (W : Finset ℂ)
    (hW : ∀ ρ ∈ W, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ (103/16:ℝ)) :
    (∑ ρ ∈ W, (RvM.zeroMult ρ:ℝ)*(1/ρ.im)) = 0 := by
  have he : W = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hn
    obtain ⟨ρ, hm⟩ := hn
    exact no_positive_zero_to_103_16 ρ (hW ρ hm).1 (hW ρ hm).2.1 (hW ρ hm).2.2
  simp [he]

end RHLowZeroSum
#print axioms RHLowZeroSum.no_zero_in_slab
#print axioms RHLowZeroSum.no_positive_zero_to_103_16
#print axioms RHLowZeroSum.reciprocal_sum_below_103_16


