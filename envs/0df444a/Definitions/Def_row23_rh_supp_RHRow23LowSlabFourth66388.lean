-- Prove2me | Definitions.Def_row23_rh_supp_RHRow23LowSlabFourth66388
-- name    : row23_rh_supp_RHRow23LowSlabFourth66388
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-21T20:29:02.847687+00:00
-- url     : https://prove2.me/theorems/adf6f75a-0cf1-46d3-9103-0973f92b32bb
-- title:
--   Row 23 RH support: RHRow23LowSlabFourth66388
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHRow23LowSlabThird66388
import Definitions.Def_row23_rh_supp_RHLowSlabFourthFinal
set_option autoImplicit false
set_option maxHeartbeats 20000000
noncomputable section
namespace DusartLegendreSmoothing.Moment380k
open Complex DusartSmoothing

theorem row23_of_low_sum_after_fourth_slab_and_positive_tail_66388
    (hFine : ∀ W : Finset ℂ,
      (∀ ρ ∈ W, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ 1000) →
      (∑ ρ ∈ W, (RvM.zeroMult ρ:ℝ)*(1/ρ.im)) ≤ (2028657/1000000:ℝ))
    (hGap : ∀ ρ : NontrivialZetaZero,
      (((205/32:ℝ) < |ρ.val.im| ∧ |ρ.val.im| < (14:ℝ)) ∨
       ((100:ℝ) < |ρ.val.im| ∧ |ρ.val.im| ≤ (121 - 5773/100000:ℝ))) →
      ρ.val.re = 1/2)
    (hTail : ∀ s : ℂ, RvM.IsNontrivialZero s → (66388 + 25/8192:ℝ) < s.im →
      s.im ≤ (380000:ℝ) → s.re = 1/2)
    (x : ℝ) (hx : Real.exp (23:ℝ) ≤ x) :
    |Chebyshev.psi x - x| ≤ (2431/10000000:ℝ)*x := by
  apply row23_of_low_sum_after_third_slab_and_positive_tail_66388 hFine ?_ hTail x hx
  intro ρ h
  rcases h with ⟨ha,hb⟩ | hhi
  · by_cases hsmall : |ρ.val.im| ≤ (205/32:ℝ)
    · have hlo : (51/8:ℝ) ≤ |ρ.val.im| := by
        have hp := Real.pi_gt_d4
        linarith
      by_cases hp : 0 ≤ ρ.val.im
      · rw [abs_of_nonneg hp] at hlo hsmall
        have hn := RHLowSlabFourthPilot.slab_clear ρ.val.re ρ.val.im
          ρ.property.2.1 ρ.property.2.2 hlo hsmall
        exact False.elim (hn (by simpa only [Complex.re_add_im] using ρ.property.1))
      · have hn : ρ.val.im < 0 := lt_of_not_ge hp
        rw [abs_of_neg hn] at hlo hsmall
        let z : ℂ := (starRingEnd ℂ) ρ.val
        have hz : RvM.IsNontrivialZero z := by
          refine ⟨?_, ?_, ?_⟩
          · dsimp [z]; rw [riemannZeta_conj, ρ.property.1, map_zero]
          · simpa [z] using ρ.property.2.1
          · simpa [z] using ρ.property.2.2
        have hzl : (51/8:ℝ) ≤ z.im := by simpa [z] using hlo
        have hzu : z.im ≤ (205/32:ℝ) := by simpa [z] using hsmall
        have hnz := RHLowSlabFourthPilot.slab_clear z.re z.im hz.2.1 hz.2.2 hzl hzu
        exact False.elim (hnz (by simpa only [Complex.re_add_im] using hz.1))
    · exact hGap ρ (Or.inl ⟨lt_of_not_ge hsmall,hb⟩)
  · exact hGap ρ (Or.inr hhi)

end DusartLegendreSmoothing.Moment380k
#print axioms DusartLegendreSmoothing.Moment380k.row23_of_low_sum_after_fourth_slab_and_positive_tail_66388


