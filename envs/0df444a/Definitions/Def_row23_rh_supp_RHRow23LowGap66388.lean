-- Prove2me | Definitions.Def_row23_rh_supp_RHRow23LowGap66388
-- name    : row23_rh_supp_RHRow23LowGap66388
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T20:56:02.002596+00:00
-- url     : https://prove2.me/theorems/b3426440-0028-4ece-847e-fbe5c8b5fa36
-- title:
--   Row 23 RH support: RHRow23LowGap66388
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHRow23LowSlab66388
import Theorems.Thm_TaoFivePrimes_rh_verified_block_14_1e2
set_option autoImplicit false
set_option maxHeartbeats 20000000
noncomputable section
namespace DusartLegendreSmoothing.Moment380k
open Complex DusartSmoothing

theorem low_RH_from_14_100_and_remaining_gaps
    (hGap : ∀ ρ : NontrivialZetaZero,
      (|ρ.val.im| < (14:ℝ) ∨
       ((100:ℝ) < |ρ.val.im| ∧ |ρ.val.im| ≤ (121 - 5773/100000:ℝ))) →
      ρ.val.re = 1/2)
    (ρ : NontrivialZetaZero)
    (hb : |ρ.val.im| ≤ (121 - 5773/100000:ℝ)) : ρ.val.re = 1/2 := by
  by_cases ha : |ρ.val.im| < (14:ℝ)
  · exact hGap ρ (Or.inl ha)
  by_cases hc : (100:ℝ) < |ρ.val.im|
  · exact hGap ρ (Or.inr ⟨hc, hb⟩)
  have hlo : (14:ℝ) ≤ |ρ.val.im| := le_of_not_gt ha
  have hhi : |ρ.val.im| ≤ (100:ℝ) := le_of_not_gt hc
  by_cases hp : 0 ≤ ρ.val.im
  · rw [abs_of_nonneg hp] at hlo hhi
    exact TaoFivePrimes.rh_verified_block_14_1e2 ρ.val ρ.property.1 ρ.property.2.1 ρ.property.2.2 hlo (by norm_num at ⊢; exact hhi)
  · have hn : ρ.val.im < 0 := lt_of_not_ge hp
    rw [abs_of_neg hn] at hlo hhi
    let z : ℂ := (starRingEnd ℂ) ρ.val
    have hz : RvM.IsNontrivialZero z := by
      refine ⟨?_, ?_, ?_⟩
      · dsimp [z]; rw [riemannZeta_conj, ρ.property.1, map_zero]
      · simpa [z] using ρ.property.2.1
      · simpa [z] using ρ.property.2.2
    have hzl : (14:ℝ) ≤ z.im := by simpa [z] using hlo
    have hzu : z.im ≤ (100:ℝ) := by simpa [z] using hhi
    have h := TaoFivePrimes.rh_verified_block_14_1e2 z hz.1 hz.2.1 hz.2.2 hzl (by norm_num at ⊢; exact hzu)
    simpa [z] using h

theorem row23_of_low_sum_low_gaps_and_positive_tail_66388
    (hFine : ∀ W : Finset ℂ,
      (∀ ρ ∈ W, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ 1000) →
      (∑ ρ ∈ W, (RvM.zeroMult ρ:ℝ)*(1/ρ.im)) ≤ (2028657/1000000:ℝ))
    (hGap : ∀ ρ : NontrivialZetaZero,
      (|ρ.val.im| < (14:ℝ) ∨
       ((100:ℝ) < |ρ.val.im| ∧ |ρ.val.im| ≤ (121 - 5773/100000:ℝ))) →
      ρ.val.re = 1/2)
    (hTail : ∀ s : ℂ, RvM.IsNontrivialZero s → (66388 + 25/8192:ℝ) < s.im →
      s.im ≤ (380000:ℝ) → s.re = 1/2)
    (x : ℝ) (hx : Real.exp (23:ℝ) ≤ x) :
    |Chebyshev.psi x - x| ≤ (2431/10000000:ℝ)*x := by
  exact row23_of_low_sum_shorter_low_RH_and_positive_tail_66388 hFine
    (low_RH_from_14_100_and_remaining_gaps hGap) hTail x hx

end DusartLegendreSmoothing.Moment380k
#print axioms DusartLegendreSmoothing.Moment380k.low_RH_from_14_100_and_remaining_gaps
#print axioms DusartLegendreSmoothing.Moment380k.row23_of_low_sum_low_gaps_and_positive_tail_66388


