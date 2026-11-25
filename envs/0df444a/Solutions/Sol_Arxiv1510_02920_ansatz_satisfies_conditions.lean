-- Prove2me | solution 1 for Arxiv1510_02920.ansatz_satisfies_conditions
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T15:41:26.116597+00:00
-- url     : https://prove2.me/submissions/79ea7898-e1c1-49a6-be44-c79ebd373997

import Mathlib
import Definitions.Def_Arxiv1510_02920_Basic

open Filter Topology Asymptotics
namespace Arxiv1510_02920

lemma asc_formula (c γ : ℝ) (f : ℝ → ℝ) (hf : Differentiable ℝ f) (x : ℝ) :
    perm c (ansatzP f γ) x = fun ω : ℂ => (1 + (f x : ℂ) / ((γ : ℂ) - Complex.I * ω) ^ 2) ^ 2 -
      Complex.I * (c : ℂ) / ω * (((deriv f x : ℝ) : ℂ) / ((γ : ℂ) - Complex.I * ω) ^ 2) := by
  funext ω
  have hd : HasDerivAt (fun y : ℝ => ansatzP f γ y ω)
      (((deriv f x : ℝ) : ℂ) / ((γ : ℂ) - Complex.I * ω) ^ 2) x :=
    (((hf x).hasDerivAt.ofReal_comp).div_const _).const_add 1
  unfold perm
  rw [hd.deriv]
  rfl

lemma asc_ne (γ : ℝ) (hγ : 0 < γ) (w : ℂ) (hw : 0 ≤ w.im) : (γ : ℂ) - Complex.I * w ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

theorem ansatz_satisfies_conditions (c : ℝ) (hc : 0 < c) (γ : ℝ) (hγ : 0 < γ)
    (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    CondAnalytic (perm c (ansatzP f γ)) ∧ CondReality (perm c (ansatzP f γ)) ∧
      CondLowFreq (-1) (perm c (ansatzP f γ)) ∧ CondHighFreq (perm c (ansatzP f γ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    rw [asc_formula c γ f hf x]
    constructor
    · apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_im)
      intro w hw
      have hw' : 0 < w.im := hw
      have h1 := asc_ne γ hγ w hw'.le
      have h2 : w ≠ 0 := by intro h; rw [h] at hw'; simp at hw'
      apply DifferentiableAt.differentiableWithinAt
      fun_prop (disch := first | assumption | exact pow_ne_zero _ ‹_›)
    · intro w hw
      have h1 := asc_ne γ hγ w hw.1
      have h2 : w ≠ 0 := hw.2
      apply ContinuousAt.continuousWithinAt
      fun_prop (disch := first | assumption | exact pow_ne_zero _ ‹_›)
  · intro x ω hω
    rw [asc_formula c γ f hf x]
    simp only [star_sub, star_mul', star_pow, star_add, star_one, star_div₀]
    simp only [Complex.star_def, Complex.conj_ofReal, Complex.conj_I, map_sub, map_mul, map_pow]
    try simp only [map_div₀, map_add, map_one, map_sub, map_mul, map_pow, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
    ring
  · refine ⟨-1, le_refl _, fun x => ?_⟩
    set F : ℂ := (f x : ℂ)
    set D : ℂ := ((deriv f x : ℝ) : ℂ)
    refine ⟨(1 + F / (γ : ℂ) ^ 2) ^ 2, -Complex.I * c * D / (γ : ℂ) ^ 2, ?_⟩
    rw [asc_formula c γ f hf x]
    have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
    rw [Asymptotics.isLittleO_iff_tendsto']
    swap
    · filter_upwards [self_mem_nhdsWithin] with ω (hω : ω ≠ 0)
      intro h; exfalso; simp at h; exact hω h
    set h : ℝ → ℂ := fun ω => (ω : ℂ) * ((1 + F / ((γ : ℂ) - Complex.I * ω) ^ 2) ^ 2 -
        (1 + F / (γ : ℂ) ^ 2) ^ 2) - Complex.I * c * D * (1 / ((γ : ℂ) - Complex.I * ω) ^ 2 -
        1 / (γ : ℂ) ^ 2) with hh
    have hc0 : ContinuousAt h 0 := by
      have : ((γ : ℂ) - Complex.I * ((0:ℝ):ℂ)) ≠ 0 := by simpa using hγc
      rw [hh]
      fun_prop (disch := first | assumption | exact pow_ne_zero _ ‹_›)
    have h0 : h 0 = 0 := by simp [hh]
    rw [← h0]
    refine (hc0.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ω (hω : ω ≠ 0)
    have hωc : (ω : ℂ) ≠ 0 := by exact_mod_cast hω
    have hZ := asc_ne γ hγ (ω : ℂ) (by simp)
    simp only [hh, zpow_neg, zpow_one]
    field_simp
    ring
  · intro x
    set F : ℂ := (f x : ℂ)
    set D : ℂ := ((deriv f x : ℝ) : ℂ)
    refine ⟨-2 * F, ?_⟩
    rw [asc_formula c γ f hf x]
    rw [Asymptotics.isLittleO_iff_tendsto']
    swap
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with ω hω
      intro h; exfalso; have : (ω : ℂ) ≠ 0 := by exact_mod_cast hω.ne'
      simp [this] at h
    set H : ℝ → ℂ := fun t => 2 * F * (1 / ((γ : ℂ) * t - Complex.I) ^ 2 + 1) +
      F ^ 2 * (t : ℂ) ^ 2 / ((γ : ℂ) * t - Complex.I) ^ 4 -
      Complex.I * c * D * (t : ℂ) / ((γ : ℂ) * t - Complex.I) ^ 2 with hH
    have hI : ((γ : ℂ) * ((0:ℝ):ℂ) - Complex.I) ≠ 0 := by simp
    have hHc : ContinuousAt H 0 := by
      fun_prop (disch := first | assumption | exact pow_ne_zero _ hI)
    have hH0 : H 0 = 0 := by simp [hH]
    rw [← hH0]
    refine (hHc.tendsto.comp tendsto_inv_atTop_zero).congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with ω hω
    have hωc : (ω : ℂ) ≠ 0 := by exact_mod_cast hω.ne'
    have hZ := asc_ne γ hγ (ω : ℂ) (by simp)
    have hT : (γ : ℂ) * (ω : ℂ)⁻¹ - Complex.I ≠ 0 := by
      intro h0; apply hZ
      have : (γ : ℂ) - Complex.I * ω = ω * ((γ : ℂ) * (ω : ℂ)⁻¹ - Complex.I) := by
        field_simp
      rw [this, h0, mul_zero]
    have hrel : (γ : ℂ) - Complex.I * ω = ω * ((γ : ℂ) * (ω : ℂ)⁻¹ - Complex.I) := by
      field_simp
    simp only [Function.comp_apply, hH, Complex.ofReal_inv]
    rw [hrel]
    generalize (γ : ℂ) * (ω : ℂ)⁻¹ - Complex.I = T at *
    field_simp
    ring

end Arxiv1510_02920

open Arxiv1510_02920 in
theorem solution (c : ℝ) (hc : 0 < c) (γ : ℝ) (hγ : 0 < γ)
    (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    CondAnalytic (perm c (ansatzP f γ)) ∧ CondReality (perm c (ansatzP f γ)) ∧
      CondLowFreq (-1) (perm c (ansatzP f γ)) ∧ CondHighFreq (perm c (ansatzP f γ)) :=
  ansatz_satisfies_conditions c hc γ hγ f hf
