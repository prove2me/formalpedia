-- Prove2me | Definitions.Def_row23_rh_supp_RHLocalRow23StandardStripTail380kAfter66388
-- name    : row23_rh_supp_RHLocalRow23StandardStripTail380kAfter66388
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T20:43:30.446201+00:00
-- url     : https://prove2.me/theorems/634eefd5-49e0-4805-a31d-53a1d8e04c3f
-- title:
--   Row 23 RH support: RHLocalRow23StandardStripTail380kAfter66388
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLocalRow23OfRH380kConditionalSum
import Definitions.Def_row23_rh_supp_RH66388SegmentExtended
set_option autoImplicit false
set_option maxHeartbeats 10000000
noncomputable section
namespace DusartLegendreSmoothing.Moment380k
open Complex DusartSmoothing

theorem row23_of_low_sum_low_RH_and_positive_tail_after66388
    (hFine : ∀ W : Finset ℂ,
      (∀ ρ ∈ W, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ 1000) →
      (∑ ρ ∈ W, (RvM.zeroMult ρ:ℝ)*(1/ρ.im)) ≤ (2028657/1000000:ℝ))
    (hLow : ∀ ρ : NontrivialZetaZero, |ρ.val.im| ≤ (121:ℝ) → ρ.val.re = 1/2)
    (hTail : ∀ s : ℂ, RvM.IsNontrivialZero s → (66388 + 25/8192:ℝ) < s.im →
      s.im ≤ (380000:ℝ) → s.re = 1/2)
    (x : ℝ) (hx : Real.exp (23:ℝ) ≤ x) :
    |Chebyshev.psi x - x| ≤ (2431/10000000:ℝ)*x := by
  apply row23_of_RH380k_and_low_sum hFine ?_ x hx
  intro ρ hb
  by_cases hlow : |ρ.val.im| ≤ (121:ℝ)
  · exact hLow ρ hlow
  have hne : ρ.val.im ≠ 0 := by
    intro he
    rw [he, abs_zero] at hlow
    norm_num at hlow
  by_cases hp : 0 < ρ.val.im
  · by_cases hm : ρ.val.im ≤ (66388:ℝ) + 25/8192
    · apply RH66388Count.segment_extended ρ.val ρ.property.1 ρ.property.2.1 ρ.property.2.2 hp ?_ hm
      rw [abs_of_pos hp] at hlow
      linarith
    · apply hTail ρ.val ρ.property (lt_of_not_ge hm)
      simpa [abs_of_pos hp] using hb
  · have hn : ρ.val.im < 0 := lt_of_le_of_ne (le_of_not_gt hp) hne
    have hc : RvM.IsNontrivialZero ((starRingEnd ℂ) ρ.val) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [riemannZeta_conj, ρ.property.1, map_zero]
      · simpa using ρ.property.2.1
      · simpa using ρ.property.2.2
    have hpos : 0 < ((starRingEnd ℂ) ρ.val).im := by simpa using (neg_pos.mpr hn)
    by_cases hm : ((starRingEnd ℂ) ρ.val).im ≤ (66388:ℝ) + 25/8192
    · have h := RH66388Count.segment_extended ((starRingEnd ℂ) ρ.val) hc.1 hc.2.1 hc.2.2 hpos (by
        rw [abs_of_neg hn] at hlow
        simpa using (le_of_lt (lt_of_not_ge hlow))) hm
      simpa using h
    · have h := hTail ((starRingEnd ℂ) ρ.val) hc (lt_of_not_ge hm) (by simpa [abs_of_neg hn] using hb)
      simpa using h
end DusartLegendreSmoothing.Moment380k
#print axioms DusartLegendreSmoothing.Moment380k.row23_of_low_sum_low_RH_and_positive_tail_after66388


