-- Prove2me | solution 2 for AhlforsComplexAnalysis.riemann_mapping_theorem
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T12:35:35.509989+00:00
-- url     : https://prove2.me/submissions/8d15ccac-87b5-4f0c-b4e9-f4750f03ce7d

import Mathlib
import Definitions.Def_AhlforsComplexAnalysis_Defs
import Theorems.Thm_AhlforsComplexAnalysis_exists_log_and_root
import Theorems.Thm_AhlforsComplexAnalysis_rmt_exists_extremal
import Theorems.Thm_AhlforsComplexAnalysis_rmt_extremal_onto
import Theorems.Thm_AhlforsComplexAnalysis_rmt_uniqueness

set_option autoImplicit false

open AhlforsComplexAnalysis

/-!
Riemann mapping theorem as a reduction (Ahlfors Ch. 6 §1.1).  Existence: `hroot` comes from
`exists_log_and_root` (n = 2), `rmt_exists_extremal` gives an extremal injective `f : Ω → D`,
`rmt_extremal_onto` shows it is onto, and the rotation `c = conj f'(z₀) / ‖f'(z₀)‖` normalises the
derivative to be positive.  Uniqueness is `rmt_uniqueness`.
-/

theorem solution {Ω : Set ℂ}
    (hΩ : IsSimplyConnectedRegion Ω) (hne : Ω ≠ Set.univ) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    (∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f Ω ∧ f z₀ = 0 ∧
        0 < (deriv f z₀).re ∧ (deriv f z₀).im = 0 ∧
        Set.InjOn f Ω ∧ f '' Ω = Metric.ball 0 1) ∧
    ∀ f g : ℂ → ℂ,
      (AnalyticOnNhd ℂ f Ω ∧ f z₀ = 0 ∧ 0 < (deriv f z₀).re ∧ (deriv f z₀).im = 0 ∧
        Set.InjOn f Ω ∧ f '' Ω = Metric.ball 0 1) →
      (AnalyticOnNhd ℂ g Ω ∧ g z₀ = 0 ∧ 0 < (deriv g z₀).re ∧ (deriv g z₀).im = 0 ∧
        Set.InjOn g Ω ∧ g '' Ω = Metric.ball 0 1) →
      Set.EqOn f g Ω := by
  have hroot : ∀ u : ℂ → ℂ, AnalyticOnNhd ℂ u Ω → (∀ z ∈ Ω, u z ≠ 0) →
      ∃ r : ℂ → ℂ, AnalyticOnNhd ℂ r Ω ∧ ∀ z ∈ Ω, r z ^ 2 = u z :=
    fun u hu hu0 => (AhlforsComplexAnalysis.exists_log_and_root hΩ hu hu0).2 2 (by norm_num)
  refine ⟨?_, fun f g hf hg => AhlforsComplexAnalysis.rmt_uniqueness hΩ.1 hz₀ hf hg⟩
  obtain ⟨f, hf, hfmap, hf0, hfinj, hfd, hmax⟩ :=
    AhlforsComplexAnalysis.rmt_exists_extremal hΩ.1 hne hroot hz₀
  have honto := AhlforsComplexAnalysis.rmt_extremal_onto hΩ.1 hroot hz₀ hf hfmap hf0 hfinj hfd hmax
  have hmem : ∀ w : ℂ, w ∈ Metric.ball (0 : ℂ) 1 ↔ ‖w‖ < 1 := fun w => by simp
  -- rotate so that the derivative at `z₀` is positive
  have hnorm : 0 < ‖deriv f z₀‖ := norm_pos_iff.mpr hfd
  set c : ℂ := (starRingEnd ℂ) (deriv f z₀) / (‖deriv f z₀‖ : ℂ) with hc
  have hcn : ‖c‖ = 1 := by
    rw [hc, norm_div, Complex.norm_conj, Complex.norm_real, norm_norm]
    exact div_self hnorm.ne'
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hcn
    exact zero_ne_one hcn
  have hd : deriv (fun z => c * f z) z₀ = (‖deriv f z₀‖ : ℂ) := by
    rw [deriv_const_mul_field, hc, div_mul_eq_mul_div, Complex.conj_mul', sq, mul_div_assoc,
      div_self (by exact_mod_cast hnorm.ne'), mul_one]
  refine ⟨fun z => c * f z, analyticOnNhd_const.mul hf, by simp [hf0], ?_, ?_, ?_, ?_⟩
  · rw [hd, Complex.ofReal_re]
    exact hnorm
  · rw [hd, Complex.ofReal_im]
  · intro x hx y hy hxy
    exact hfinj hx hy (mul_left_cancel₀ hc0 hxy)
  · apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      rw [hmem, norm_mul, hcn, one_mul]
      exact hfmap z hz
    · intro w hw
      have hw' : c⁻¹ * w ∈ f '' Ω := by
        rw [honto, hmem, norm_mul, norm_inv, hcn, inv_one, one_mul]
        exact (hmem w).mp hw
      obtain ⟨z, hz, hzw⟩ := hw'
      exact ⟨z, hz, by simp only [hzw]; field_simp⟩

#print axioms solution
