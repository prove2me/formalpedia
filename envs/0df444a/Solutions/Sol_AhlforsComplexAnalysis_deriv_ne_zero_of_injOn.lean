-- Prove2me | solution 1 for AhlforsComplexAnalysis.deriv_ne_zero_of_injOn
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T11:58:59.471255+00:00
-- url     : https://prove2.me/submissions/3af23eb1-cac2-453b-974b-4bc777789e48

import Mathlib

set_option autoImplicit false

open Set Filter Topology

namespace AhlforsDerivInj

/-- An analytic function not vanishing at `c` has an analytic `m`-th root near `c`. -/
theorem rmtU_exists_root {u : ℂ → ℂ} {c : ℂ} (hu : AnalyticAt ℂ u c) (hc : u c ≠ 0) {m : ℕ}
    (hm : m ≠ 0) :
    ∃ v : ℂ → ℂ, AnalyticAt ℂ v c ∧ ∀ᶠ z in 𝓝 c, v z ^ m = u z := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  set r : ℂ := Complex.exp (Complex.log (u c) / m) with hr
  have hrm : r ^ m = u c := by
    rw [hr, ← Complex.exp_nat_mul, mul_div_cancel₀ _ hm', Complex.exp_log hc]
  refine ⟨fun z => r * Complex.exp (Complex.log (u z / u c) / m), ?_, ?_⟩
  · have h1 : AnalyticAt ℂ (fun z => u z / u c) c := hu.div analyticAt_const hc
    have h2 : u c / u c ∈ Complex.slitPlane := by
      rw [div_self hc]
      exact Complex.one_mem_slitPlane
    exact analyticAt_const.mul (((h1.clog h2).div analyticAt_const hm').cexp)
  · have hne : ∀ᶠ z in 𝓝 c, u z ≠ 0 := hu.continuousAt.eventually_ne hc
    filter_upwards [hne] with z hz
    rw [mul_pow, hrm, ← Complex.exp_nat_mul, mul_div_cancel₀ _ hm',
      Complex.exp_log (div_ne_zero hz hc)]
    field_simp

/-- An analytic function that is injective near `c` has nonzero derivative at `c`. -/
theorem rmtU_deriv_ne_zero {f : ℂ → ℂ} {c : ℂ} {U : Set ℂ} (hU : U ∈ 𝓝 c)
    (hf : AnalyticAt ℂ f c) (hinj : InjOn f U) : deriv f c ≠ 0 := by
  intro hd
  have hF : AnalyticAt ℂ (fun z => f z - f c) c := hf.sub analyticAt_const
  by_cases hconst : ∀ᶠ z in 𝓝 c, f z - f c = 0
  · -- `f` is locally constant, so it is not injective
    have h1 : ∀ᶠ z in 𝓝 c, z ∈ U ∧ f z = f c := by
      filter_upwards [hU, hconst] with z hzU hz
      exact ⟨hzU, sub_eq_zero.mp hz⟩
    obtain ⟨z, ⟨hzU, hz⟩, hzc⟩ :=
      ((h1.filter_mono nhdsWithin_le_nhds : ∀ᶠ z in 𝓝[≠] c, z ∈ U ∧ f z = f c).and
        self_mem_nhdsWithin).exists
    exact hzc (hinj hzU (mem_of_mem_nhds hU) hz)
  · obtain ⟨m, u, hu, hu0, hmu⟩ := hF.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hconst
    have hm2 : 2 ≤ m := by
      by_contra hlt
      have hm01 : m = 0 ∨ m = 1 := by omega
      rcases hm01 with rfl | rfl
      · apply hu0
        have h0 : 0 = u c := by simpa using hmu.self_of_nhds
        exact h0.symm
      · have h1 : HasDerivAt (fun z => f c + (z - c) * u z) (u c) c := by
          have := (((hasDerivAt_id c).sub_const c).mul hu.differentiableAt.hasDerivAt).const_add
            (f c)
          simpa using this
        have hd' : HasDerivAt f (u c) c := by
          refine h1.congr_of_eventuallyEq ?_
          filter_upwards [hmu] with z hz
          simp only [pow_one, smul_eq_mul] at hz
          linear_combination hz
        exact hu0 (hd'.deriv ▸ hd)
    have hm0 : m ≠ 0 := by omega
    obtain ⟨v, hv, hvu⟩ := rmtU_exists_root hu hu0 hm0
    -- `f z - f c = h z ^ m` with `h = (z - c) * v`
    set h : ℂ → ℂ := fun z => (z - c) * v z with hh_def
    have hh : AnalyticAt ℂ h c := (analyticAt_id.sub analyticAt_const).mul hv
    have hhc : h c = 0 := by simp [hh_def]
    have hrel : ∀ᶠ z in 𝓝 c, f z - f c = h z ^ m := by
      filter_upwards [hmu, hvu] with z hz hzv
      rw [hz, smul_eq_mul, hh_def, mul_pow, hzv]
    have hnc : ¬ ∀ᶠ z in 𝓝 c, h z = h c := by
      intro hev
      apply hconst
      filter_upwards [hrel, hev] with z hz1 hz2
      rw [hz1, hz2, hhc, zero_pow hm0]
    have hopen : 𝓝 (h c) ≤ map h (𝓝 c) :=
      hh.eventually_constant_or_nhds_le_map_nhds.resolve_left hnc
    have hV : {z | f z - f c = h z ^ m} ∩ U ∈ 𝓝 c := inter_mem hrel hU
    have himg : h '' ({z | f z - f c = h z ^ m} ∩ U) ∈ 𝓝 (0 : ℂ) := by
      rw [← hhc]
      exact hopen (image_mem_map hV)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp himg
    -- a primitive `m`-th root of unity
    have hζ := Complex.isPrimitiveRoot_exp m hm0
    set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / m) with hζ_def
    have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
    have hζm : ζ ^ m = 1 := hζ.pow_eq_one
    have hζn : ‖ζ‖ = 1 := hζ.norm'_eq_one hm0
    set w : ℂ := ((ε / 2 : ℝ) : ℂ) with hw_def
    have hwn : ‖w‖ = ε / 2 := by
      rw [hw_def, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hw0 : w ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hwn
      linarith
    have hw1 : w ∈ Metric.ball (0 : ℂ) ε := by
      rw [mem_ball_zero_iff, hwn]
      linarith
    have hw2 : ζ * w ∈ Metric.ball (0 : ℂ) ε := by
      rw [mem_ball_zero_iff, norm_mul, hζn, one_mul, hwn]
      linarith
    obtain ⟨z1, ⟨hz1r, hz1U⟩, hz1h⟩ := hball hw1
    obtain ⟨z2, ⟨hz2r, hz2U⟩, hz2h⟩ := hball hw2
    have hf12 : f z1 = f z2 := by
      have e1 : f z1 - f c = w ^ m := by rw [hz1r, hz1h]
      have e2 : f z2 - f c = w ^ m := by rw [hz2r, hz2h, mul_pow, hζm, one_mul]
      linear_combination e1 - e2
    have hz12 : z1 = z2 := hinj hz1U hz2U hf12
    rw [hz12, hz2h] at hz1h
    exact hw0 (by
      have : (ζ - 1) * w = 0 := by linear_combination hz1h
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd (sub_eq_zero.mp h0) hζ1
      · exact h0)

end AhlforsDerivInj

theorem solution {f : ℂ → ℂ} {c : ℂ} {U : Set ℂ} (hU : U ∈ nhds c)
    (hf : AnalyticAt ℂ f c) (hinj : Set.InjOn f U) : deriv f c ≠ 0 :=
  AhlforsDerivInj.rmtU_deriv_ne_zero hU hf hinj

#print axioms solution
