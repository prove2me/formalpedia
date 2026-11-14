-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreZeroSeries
-- name    : row23_rh_supp_RHLegendreZeroSeries
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:04:57.409007+00:00
-- url     : https://prove2.me/theorems/34855566-18f1-478f-8626-d920d065f9f1
-- title:
--   Row 23 RH support: RHLegendreZeroSeries
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreHighKernel
import Mathlib.Analysis.Normed.Group.InfiniteSum
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing

/-- An absolutely convergent majorant controls both convergence and the norm. -/
lemma kernel_series_majorant {ι : Type*} (f : ι → ℂ) (g : ι → ℝ) (C : ℝ)
    (hg : Summable g) (h : ∀ i, ‖f i‖ ≤ C*g i) :
    Summable f ∧ ‖∑' i, f i‖ ≤ C*(∑' i, g i) := by
  have hs : Summable (fun i => C*g i) := hg.mul_left C
  constructor
  · exact hs.of_norm_bounded h
  · simpa only [tsum_mul_left] using tsum_of_norm_bounded hs.hasSum h

lemma weighted_zeroKernel_low (m : ℕ) (ρ : ℂ) (w : ℕ) (x δ a : ℝ)
    (hx : 1 ≤ x) (hd : 0 ≤ δ) (ha : a ≤ 1)
    (hβ : ρ.re ≤ a) (hi : 0 < |ρ.im|) :
    ‖(w:ℂ)*((x:ℂ)^ρ*zeroKernel m ρ δ)‖ ≤
      (x^a*(1+δ/2))*((w:ℝ)/|ρ.im|) := by
  have hxp : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hp := Real.rpow_le_rpow_of_exponent_le hx hβ
  rw [norm_mul, Complex.norm_natCast]
  calc
    _ ≤ (w:ℝ)*(x^ρ.re*(1+δ/2)/|ρ.im|) :=
      mul_le_mul_of_nonneg_left
        (zeroKernel_scaled_low m ρ x δ hxp hd (hβ.trans ha) hi) (Nat.cast_nonneg w)
    _ ≤ (w:ℝ)*(x^a*(1+δ/2)/|ρ.im|) := by gcongr
    _ = _ := by ring

lemma weighted_zeroKernel_high (m : ℕ) (ρ : ℂ) (w : ℕ) (x δ a M : ℝ)
    (hx : 1 ≤ x) (hd : 0 < δ) (ha : a ≤ 1) (hM0 : 0 ≤ M)
    (hM : derivativeMass m δ ≤ M) (hβ : ρ.re ≤ a) (hi : 0 < |ρ.im|) :
    ‖(w:ℂ)*((x:ℂ)^ρ*zeroKernel m ρ δ)‖ ≤
      (x^a*M/δ^m)*((w:ℝ)/|ρ.im|^(m+1)) := by
  have hxp : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hp := Real.rpow_le_rpow_of_exponent_le hx hβ
  rw [norm_mul, Complex.norm_natCast]
  calc
    _ ≤ (w:ℝ)*(x^ρ.re*derivativeMass m δ/(δ^m*|ρ.im|^(m+1))) :=
      mul_le_mul_of_nonneg_left
        (zeroKernel_scaled_high m ρ x δ hxp hd (hβ.trans ha) hi) (Nat.cast_nonneg w)
    _ ≤ (w:ℝ)*(x^ρ.re*M/(δ^m*|ρ.im|^(m+1))) := by gcongr
    _ ≤ (w:ℝ)*(x^a*M/(δ^m*|ρ.im|^(m+1))) := by gcongr
    _ = _ := by ring

/-- Low zeros: the reciprocal-height sum supplies the complete majorant. -/
theorem zero_series_low_bound {ι : Type*} (m : ℕ) (ρ : ι → ℂ) (w : ι → ℕ)
    (x δ a B : ℝ) (hx : 1 ≤ x) (hd : 0 ≤ δ) (ha : a ≤ 1)
    (hβ : ∀ i, (ρ i).re ≤ a) (hi : ∀ i, 0 < |(ρ i).im|)
    (hs : Summable (fun i => (w i:ℝ)/|(ρ i).im|))
    (hB : (∑' i, (w i:ℝ)/|(ρ i).im|) ≤ B) :
    Summable (fun i => (w i:ℂ)*((x:ℂ)^(ρ i)*zeroKernel m (ρ i) δ)) ∧
    ‖∑' i, (w i:ℂ)*((x:ℂ)^(ρ i)*zeroKernel m (ρ i) δ)‖ ≤ x^a*(1+δ/2)*B := by
  have h := kernel_series_majorant _ _ (x^a*(1+δ/2)) hs
    (fun i => weighted_zeroKernel_low m (ρ i) (w i) x δ a hx hd ha (hβ i) (hi i))
  refine ⟨h.1, h.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left hB (by positivity)

/-- Higher zeros: the certified derivative mass and reciprocal moment suffice. -/
theorem zero_series_high_bound {ι : Type*} (m : ℕ) (ρ : ι → ℂ) (w : ι → ℕ)
    (x δ a M B : ℝ) (hx : 1 ≤ x) (hd : 0 < δ) (ha : a ≤ 1) (hM0 : 0 ≤ M)
    (hM : derivativeMass m δ ≤ M) (hβ : ∀ i, (ρ i).re ≤ a)
    (hi : ∀ i, 0 < |(ρ i).im|)
    (hs : Summable (fun i => (w i:ℝ)/|(ρ i).im|^(m+1)))
    (hB : (∑' i, (w i:ℝ)/|(ρ i).im|^(m+1)) ≤ B) :
    Summable (fun i => (w i:ℂ)*((x:ℂ)^(ρ i)*zeroKernel m (ρ i) δ)) ∧
    ‖∑' i, (w i:ℂ)*((x:ℂ)^(ρ i)*zeroKernel m (ρ i) δ)‖ ≤ (x^a*M/δ^m)*B := by
  have h := kernel_series_majorant _ _ (x^a*M/δ^m) hs
    (fun i => weighted_zeroKernel_high m (ρ i) (w i) x δ a M hx hd ha hM0 hM (hβ i) (hi i))
  refine ⟨h.1, h.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left hB (by positivity)

end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.kernel_series_majorant
#print axioms DusartLegendreSmoothing.weighted_zeroKernel_low
#print axioms DusartLegendreSmoothing.weighted_zeroKernel_high
#print axioms DusartLegendreSmoothing.zero_series_low_bound
#print axioms DusartLegendreSmoothing.zero_series_high_bound


