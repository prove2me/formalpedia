-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreCountEnvelope
-- name    : row23_rh_supp_RHLegendreCountEnvelope
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T21:59:26.2562+00:00
-- url     : https://prove2.me/theorems/df065020-77ea-469a-81e6-5057b2697250
-- title:
--   Row 23 RH support: RHLegendreCountEnvelope
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreZeroCountIncrement
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing
open DusartSmoothing Set MeasureTheory
 theorem finite_zero_sum_le_count_envelope {ι : Type*} (Z : Finset ι)
    (w : ι → ℕ) (γ : ι → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hγ : ∀ ρ ∈ Z, a ≤ γ ρ ∧ γ ρ ≤ b)
    (g g' F F' : ℝ → ℝ)
    (hg' : ContinuousOn g' (Icc a b)) (hF' : ContinuousOn F' (Icc a b))
    (hgD : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t)
    (hFD : ∀ t ∈ Icc a b, HasDerivAt F (F' t) t)
    (hg0 : 0 ≤ g b) (hgneg : ∀ t ∈ Icc a b, g' t ≤ 0)
    (hN : ∀ t ∈ Icc a b, finiteZeroCount Z w γ t ≤ F t) :
    (∑ ρ ∈ Z, (w ρ:ℝ)*g (γ ρ)) ≤
      g a*F a+∫ t : ℝ in a..b, g t*F' t := by
  have hsub : uIcc a b ⊆ Icc a b := by rw [uIcc_of_le hab]
  have hG : ContinuousOn g (uIcc a b) := fun t ht =>
    (hgD t (hsub ht)).continuousAt.continuousWithinAt
  have hF : ContinuousOn F (uIcc a b) := fun t ht =>
    (hFD t (hsub ht)).continuousAt.continuousWithinAt
  have hgp : IntervalIntegrable g' volume a b := (hg'.mono hsub).intervalIntegrable
  have hFp : IntervalIntegrable F' volume a b := (hF'.mono hsub).intervalIntegrable
  have hNM : Monotone (finiteZeroCount Z w γ) := by
    intro u v huv
    exact Finset.sum_le_sum (fun ρ _ =>
      mul_le_mul_of_nonneg_left (primeStep_mono (γ ρ) huv) (Nat.cast_nonneg _))
  have hNi : IntervalIntegrable (finiteZeroCount Z w γ) volume a b := hNM.intervalIntegrable
  have hNP : IntervalIntegrable (fun t => finiteZeroCount Z w γ t*g' t) volume a b :=
    hNi.mul_continuousOn (hg'.mono hsub)
  have hFP : IntervalIntegrable (fun t => F t*g' t) volume a b :=
    hF.intervalIntegrable.mul_continuousOn (hg'.mono hsub)
  have hI : (∫ t : ℝ in a..b, F t*g' t) ≤
      ∫ t : ℝ in a..b, finiteZeroCount Z w γ t*g' t := by
    apply intervalIntegral.integral_mono_on hab hFP hNP
    intro t ht
    exact mul_le_mul_of_nonpos_right (hN t ht) (hgneg t ht)
  have hNb : finiteZeroCount Z w γ b = ∑ ρ ∈ Z, (w ρ:ℝ) := by
    unfold finiteZeroCount
    apply Finset.sum_congr rfl
    intro ρ hρ
    simp only [primeStep,if_pos (hγ ρ hρ).2,mul_one]
  have hEnd := mul_le_mul_of_nonneg_left (hN b ⟨hab,le_rfl⟩) hg0
  rw [hNb] at hEnd
  have hS := finite_zero_summation_by_parts Z w γ a b hab hγ g g' hg' hgD
  have hOpen : Ioo (min a b) (max a b) ⊆ Icc a b := by
    rw [min_eq_left hab,max_eq_right hab]
    exact Ioo_subset_Icc_self
  have hP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hF hG
    (fun t ht => hFD t (hOpen ht)) (fun t ht => hgD t (hOpen ht)) hFp hgp
  have he : (∫ t : ℝ in a..b, F' t*g t) = ∫ t : ℝ in a..b, g t*F' t := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact mul_comm _ _
  rw [he] at hP
  nlinarith only [hI,hEnd,hS,hP]
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.finite_zero_sum_le_count_envelope


