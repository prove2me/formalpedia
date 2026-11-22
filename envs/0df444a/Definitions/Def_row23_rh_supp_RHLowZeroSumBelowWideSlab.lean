-- Prove2me | Definitions.Def_row23_rh_supp_RHLowZeroSumBelowWideSlab
-- name    : row23_rh_supp_RHLowZeroSumBelowWideSlab
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T22:27:19.756526+00:00
-- url     : https://prove2.me/theorems/0f6f1a2d-46e3-49a1-aa29-9ff7a8cdc314
-- title:
--   Row 23 RH support: RHLowZeroSumBelowWideSlab
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLowSlabWideFinal
import Definitions.Def_dusart_psi_433_20261014_LowCutoff
import Definitions.Def_row23_rh_supp_RHRow23NarrowLowGaps66388
set_option autoImplicit false
set_option maxHeartbeats 20000000
noncomputable section
open Complex Finset DusartSmoothing
namespace RHLowZeroSum

theorem no_positive_zero_to_101_16 (ρ : ℂ) (hz : RvM.IsNontrivialZero ρ)
    (hp : 0 < ρ.im) (hu : ρ.im ≤ (101/16:ℝ)) : False := by
  have hπ := DusartSmoothing.LowHeight.nontrivial_zero_height_gt_two_pi
    ρ hz.1 hz.2.1 hz.2.2
  rw [abs_of_pos hp] at hπ
  have hlo : (201/32:ℝ) ≤ ρ.im := by
    have hπ0 := Real.pi_gt_d4
    linarith
  have hn := RHLowSlabWideAboveTwoPiPilot.slab_clear ρ.re ρ.im hz.2.1 hz.2.2 hlo hu
  exact hn (by simpa only [Complex.re_add_im] using hz.1)

theorem reciprocal_sum_below_101_16 (W : Finset ℂ)
    (hW : ∀ ρ ∈ W, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ (101/16:ℝ)) :
    (∑ ρ ∈ W, (RvM.zeroMult ρ:ℝ)*(1/ρ.im)) = 0 := by
  have he : W = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hn
    obtain ⟨ρ, hm⟩ := hn
    exact no_positive_zero_to_101_16 ρ (hW ρ hm).1 (hW ρ hm).2.1 (hW ρ hm).2.2
  simp [he]

end RHLowZeroSum
#print axioms RHLowZeroSum.no_positive_zero_to_101_16
#print axioms RHLowZeroSum.reciprocal_sum_below_101_16


