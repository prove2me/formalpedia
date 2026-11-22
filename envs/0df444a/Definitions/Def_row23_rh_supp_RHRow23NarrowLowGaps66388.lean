-- Prove2me | Definitions.Def_row23_rh_supp_RHRow23NarrowLowGaps66388
-- name    : row23_rh_supp_RHRow23NarrowLowGaps66388
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T20:19:49.136588+00:00
-- url     : https://prove2.me/theorems/1dcd1806-9563-4c5a-8696-c997bad08fee
-- title:
--   Row 23 RH support: RHRow23NarrowLowGaps66388
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Theorems.Thm_TaoFivePrimes_row23_low_gap_cut_20261116
import Definitions.Def_dusart_psi_433_20261014_LowCutoff
set_option autoImplicit false
set_option maxHeartbeats 20000000
noncomputable section
namespace DusartLegendreSmoothing.Moment380k
open Complex DusartSmoothing

theorem row23_of_low_sum_narrow_low_gaps_and_positive_tail_66388
    (hFine : ∀ W : Finset ℂ,
      (∀ ρ ∈ W, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ 1000) →
      (∑ ρ ∈ W, (RvM.zeroMult ρ:ℝ)*(1/ρ.im)) ≤ (2028657/1000000:ℝ))
    (hGap : ∀ ρ : NontrivialZetaZero,
      ((2 * Real.pi < |ρ.val.im| ∧ |ρ.val.im| < (14:ℝ)) ∨
       ((100:ℝ) < |ρ.val.im| ∧ |ρ.val.im| ≤ (121 - 5773/100000:ℝ))) →
      ρ.val.re = 1/2)
    (hTail : ∀ s : ℂ, RvM.IsNontrivialZero s → (66388 + 25/8192:ℝ) < s.im →
      s.im ≤ (380000:ℝ) → s.re = 1/2)
    (x : ℝ) (hx : Real.exp (23:ℝ) ≤ x) :
    |Chebyshev.psi x - x| ≤ (2431/10000000:ℝ)*x := by
  apply TaoFivePrimes.row23_low_gap_cut_20261116 hFine ?_ hTail x hx
  intro ρ h
  rcases h with hlo | hhi
  · exact hGap ρ (Or.inl ⟨DusartSmoothing.LowHeight.nontrivial_zero_height_gt_two_pi
      ρ.val ρ.property.1 ρ.property.2.1 ρ.property.2.2, hlo⟩)
  · exact hGap ρ (Or.inr hhi)

end DusartLegendreSmoothing.Moment380k
#print axioms DusartLegendreSmoothing.Moment380k.row23_of_low_sum_narrow_low_gaps_and_positive_tail_66388


