-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreThreeBands
-- name    : row23_rh_supp_RHLegendreThreeBands
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:06:15.10747+00:00
-- url     : https://prove2.me/theorems/2b3d815a-5389-437c-b8b6-416c6613b149
-- title:
--   Row 23 RH support: RHLegendreThreeBands
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreZeroSeries
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing

/-- Multiplicity-weighted reciprocal moment restricted to a height band. -/
noncomputable def heightMoment {ι : Type*} (ρ : ι → ℂ) (w : ι → ℕ)
    (k : ℕ) (p : ℝ → Prop) : ι → ℝ := by
  classical
  exact fun i => if p |(ρ i).im| then (w i:ℝ)/|(ρ i).im|^k else 0

/-- A complete three-band series bound. RH is needed only up to H. -/
theorem zero_series_three_band_bound {ι : Type*} (m : ℕ)
    (ρ : ι → ℂ) (w : ι → ℕ) (x δ T H σ M B₁ B₂ B₃ : ℝ)
    (hx : 1 ≤ x) (hd : 0 < δ) (hTH : T ≤ H) (hσ : σ ≤ 1)
    (hM0 : 0 ≤ M) (hM : derivativeMass m δ ≤ M)
    (hi : ∀ i, 0 < |(ρ i).im|)
    (hRH : ∀ i, |(ρ i).im| ≤ H → (ρ i).re = 1/2)
    (hβ : ∀ i, (ρ i).re ≤ σ)
    (hs₁ : Summable (heightMoment ρ w 1 (fun t => t ≤ T)))
    (hs₂ : Summable (heightMoment ρ w (m+1) (fun t => T < t ∧ t ≤ H)))
    (hs₃ : Summable (heightMoment ρ w (m+1) (fun t => H < t)))
    (hB₁ : (∑' i, heightMoment ρ w 1 (fun t => t ≤ T) i) ≤ B₁)
    (hB₂ : (∑' i, heightMoment ρ w (m+1) (fun t => T < t ∧ t ≤ H) i) ≤ B₂)
    (hB₃ : (∑' i, heightMoment ρ w (m+1) (fun t => H < t) i) ≤ B₃) :
    Summable (fun i => (w i:ℂ)*((x:ℂ)^(ρ i)*zeroKernel m (ρ i) δ)) ∧
    ‖∑' i, (w i:ℂ)*((x:ℂ)^(ρ i)*zeroKernel m (ρ i) δ)‖ ≤
      x^(1/2:ℝ)*(1+δ/2)*B₁ +
      (x^(1/2:ℝ)*M/δ^m)*B₂ + (x^σ*M/δ^m)*B₃ := by
  classical
  let g₁ := heightMoment ρ w 1 (fun t => t ≤ T)
  let g₂ := heightMoment ρ w (m+1) (fun t => T < t ∧ t ≤ H)
  let g₃ := heightMoment ρ w (m+1) (fun t => H < t)
  let C₁ := x^(1/2:ℝ)*(1+δ/2)
  let C₂ := x^(1/2:ℝ)*M/δ^m
  let C₃ := x^σ*M/δ^m
  have hpoint (i : ι) :
      ‖(w i:ℂ)*((x:ℂ)^(ρ i)*zeroKernel m (ρ i) δ)‖ ≤
        C₁*g₁ i+C₂*g₂ i+C₃*g₃ i := by
    by_cases ht : |(ρ i).im| ≤ T
    · have hh : |(ρ i).im| ≤ H := ht.trans hTH
      have hb : (ρ i).re ≤ (1/2:ℝ) := (hRH i hh).le
      simpa [C₁,C₂,C₃,g₁,g₂,g₃,heightMoment,ht,
        not_lt_of_ge ht,not_lt_of_ge hh] using
        weighted_zeroKernel_low m (ρ i) (w i) x δ (1/2) hx hd.le (by norm_num) hb (hi i)
    · by_cases hh : |(ρ i).im| ≤ H
      · have hb : (ρ i).re ≤ (1/2:ℝ) := (hRH i hh).le
        simpa [C₁,C₂,C₃,g₁,g₂,g₃,heightMoment,ht,lt_of_not_ge ht,hh,
          not_lt_of_ge hh] using
          weighted_zeroKernel_high m (ρ i) (w i) x δ (1/2) M hx hd
            (by norm_num) hM0 hM hb (hi i)
      · have hh' := lt_of_not_ge hh
        simpa [C₁,C₂,C₃,g₁,g₂,g₃,heightMoment,ht,hh,hh'] using
          weighted_zeroKernel_high m (ρ i) (w i) x δ σ M hx hd hσ hM0 hM (hβ i) (hi i)
  have hg₁ : Summable (fun i => C₁*g₁ i) := hs₁.mul_left C₁
  have hg₂ : Summable (fun i => C₂*g₂ i) := hs₂.mul_left C₂
  have hg₃ : Summable (fun i => C₃*g₃ i) := hs₃.mul_left C₃
  have hg := (hg₁.add hg₂).add hg₃
  refine ⟨hg.of_norm_bounded hpoint, ?_⟩
  have hn := tsum_of_norm_bounded hg.hasSum hpoint
  rw [(hg₁.add hg₂).tsum_add hg₃,hg₁.tsum_add hg₂] at hn
  simp only [tsum_mul_left] at hn
  apply hn.trans
  exact add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left hB₁ (by dsimp [C₁]; positivity))
      (mul_le_mul_of_nonneg_left hB₂ (by dsimp [C₂]; positivity)))
    (mul_le_mul_of_nonneg_left hB₃ (by dsimp [C₃]; positivity))

end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.zero_series_three_band_bound


