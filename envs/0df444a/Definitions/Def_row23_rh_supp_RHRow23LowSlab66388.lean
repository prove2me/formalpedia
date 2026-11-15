-- Prove2me | Definitions.Def_row23_rh_supp_RHRow23LowSlab66388
-- name    : row23_rh_supp_RHRow23LowSlab66388
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T20:49:37.294358+00:00
-- url     : https://prove2.me/theorems/c5be5a65-1157-4fe1-8231-c3a9f654439e
-- title:
--   Row 23 RH support: RHRow23LowSlab66388
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLocalRow23StandardStripTail380kAfter66388
import Theorems.Thm_Arb4_H1000_S_L121_clear

set_option autoImplicit false
set_option maxHeartbeats 10000000
noncomputable section

namespace DusartLegendreSmoothing.Moment380k
open Complex DusartSmoothing

theorem low_RH_extended_over_clear_slab_66388
    (hLow : ∀ ρ : NontrivialZetaZero,
      |ρ.val.im| ≤ (121 - 5773/100000:ℝ) → ρ.val.re = 1/2)
    (ρ : NontrivialZetaZero) (hb : |ρ.val.im| ≤ (121:ℝ)) : ρ.val.re = 1/2 := by
  by_cases hs : |ρ.val.im| ≤ (121 - 5773/100000:ℝ)
  · exact hLow ρ hs
  · have hlo : (121 - 5773/100000:ℝ) ≤ |ρ.val.im| := le_of_lt (lt_of_not_ge hs)
    by_cases hp : 0 ≤ ρ.val.im
    · rw [abs_of_nonneg hp] at hlo hb
      have hn := Arb4.H1000.S_L121_clear ρ.val.re ρ.val.im
        ρ.property.2.1 ρ.property.2.2 hlo hb
      have he : (ρ.val.re : ℂ) + (ρ.val.im : ℂ) * I = ρ.val := by
        exact Complex.re_add_im ρ.val
      apply False.elim
      apply hn
      rw [he]
      exact ρ.property.1
    · have hn : ρ.val.im < 0 := lt_of_not_ge hp
      rw [abs_of_neg hn] at hlo hb
      let z : ℂ := (starRingEnd ℂ) ρ.val
      have hz : RvM.IsNontrivialZero z := by
        refine ⟨?_, ?_, ?_⟩
        · dsimp [z]; rw [riemannZeta_conj, ρ.property.1, map_zero]
        · simpa [z] using ρ.property.2.1
        · simpa [z] using ρ.property.2.2
      have hzl : (121 - 5773/100000:ℝ) ≤ z.im := by simpa [z] using hlo
      have hzu : z.im ≤ (121:ℝ) := by simpa [z] using hb
      have hzeta := Arb4.H1000.S_L121_clear z.re z.im hz.2.1 hz.2.2 hzl hzu
      have he : (z.re : ℂ) + (z.im : ℂ) * I = z := Complex.re_add_im z
      apply False.elim
      apply hzeta
      rw [he]
      exact hz.1

theorem row23_of_low_sum_shorter_low_RH_and_positive_tail_66388
    (hFine : ∀ W : Finset ℂ,
      (∀ ρ ∈ W, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ 1000) →
      (∑ ρ ∈ W, (RvM.zeroMult ρ:ℝ)*(1/ρ.im)) ≤ (2028657/1000000:ℝ))
    (hLow : ∀ ρ : NontrivialZetaZero,
      |ρ.val.im| ≤ (121 - 5773/100000:ℝ) → ρ.val.re = 1/2)
    (hTail : ∀ s : ℂ, RvM.IsNontrivialZero s → (66388 + 25/8192:ℝ) < s.im →
      s.im ≤ (380000:ℝ) → s.re = 1/2)
    (x : ℝ) (hx : Real.exp (23:ℝ) ≤ x) :
    |Chebyshev.psi x - x| ≤ (2431/10000000:ℝ)*x := by
  exact row23_of_low_sum_low_RH_and_positive_tail_after66388 hFine
    (low_RH_extended_over_clear_slab_66388 hLow) hTail x hx

end DusartLegendreSmoothing.Moment380k

#print axioms DusartLegendreSmoothing.Moment380k.low_RH_extended_over_clear_slab_66388
#print axioms DusartLegendreSmoothing.Moment380k.row23_of_low_sum_shorter_low_RH_and_positive_tail_66388


