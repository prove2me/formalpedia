-- Prove2me | solution 1 for Arxiv1510_02920.entering_type_with_plasma_condition
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T15:46:04.786924+00:00
-- url     : https://prove2.me/submissions/b4a7c7a4-1bff-48cf-97fe-15ce8b18aa9c

import Mathlib
import Definitions.Def_Arxiv1510_02920_Basic

open Filter Topology Asymptotics
namespace Arxiv1510_02920

noncomputable def etpF (x : ℝ) : ℝ := 1 / 4 + Real.arctan x / (2 * Real.pi)
noncomputable def etpD (x : ℝ) : ℝ := (1 + x ^ 2)⁻¹ / (2 * Real.pi)
noncomputable def etpH (ω : ℂ) : ℂ := -1 / (ω * (ω + Complex.I))
noncomputable def etpP (x : ℝ) (ω : ℂ) : ℂ := 1 + (etpF x : ℂ) * etpH ω

lemma etpF_deriv (x : ℝ) : HasDerivAt etpF (etpD x) x :=
  ((Real.hasDerivAt_arctan' x).div_const (2 * Real.pi)).const_add (1 / 4)

lemma etpP_deriv (x : ℝ) (ω : ℂ) :
    HasDerivAt (fun y : ℝ => etpP y ω) ((etpD x : ℂ) * etpH ω) x :=
  (((etpF_deriv x).ofReal_comp).mul_const (etpH ω)).const_add 1

lemma etp_formula (c : ℝ) (x : ℝ) :
    perm c etpP x = fun ω : ℂ => (1 + (etpF x : ℂ) * etpH ω) ^ 2 -
      Complex.I * (c : ℂ) / ω * ((etpD x : ℂ) * etpH ω) := by
  funext ω
  unfold perm
  rw [(etpP_deriv x ω).deriv]
  rfl

lemma etpF_pos (x : ℝ) : 0 < etpF x := by
  unfold etpF
  have := Real.neg_pi_div_two_lt_arctan x
  have hp := Real.pi_pos
  have : -(Real.pi / 2) / (2 * Real.pi) < Real.arctan x / (2 * Real.pi) :=
    div_lt_div_of_pos_right this (by positivity)
  have e : -(Real.pi / 2) / (2 * Real.pi) = -1/4 := by field_simp; ring
  linarith

lemma etpF_lt (x : ℝ) : etpF x < 1 / 2 := by
  unfold etpF
  have := Real.arctan_lt_pi_div_two x
  have hp := Real.pi_pos
  have : Real.arctan x / (2 * Real.pi) < (Real.pi / 2) / (2 * Real.pi) :=
    div_lt_div_of_pos_right this (by positivity)
  have e : (Real.pi / 2) / (2 * Real.pi) = 1/4 := by field_simp; ring
  linarith

lemma etpD_pos (x : ℝ) : 0 < etpD x := by unfold etpD; have := Real.pi_pos; positivity

lemma ne_I (w : ℂ) (hw : 0 ≤ w.im) : w + Complex.I ≠ 0 := by
  intro h; have := congrArg Complex.im h; simp at this; linarith

lemma etpD_tendsto (l : Filter ℝ) (hl : Tendsto (fun x : ℝ => x ^ 2) l atTop) :
    Tendsto etpD l (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => 1 + x ^ 2) l atTop := tendsto_atTop_add_const_left _ _ hl
  have h2 := (tendsto_inv_atTop_zero.comp h1).div_const (2 * Real.pi)
  show Tendsto (fun x : ℝ => (1 + x ^ 2)⁻¹ / (2 * Real.pi)) l (𝓝 0)
  simpa [Function.comp_def] using h2

lemma sq_atBot : Tendsto (fun x : ℝ => x ^ 2) atBot atTop := by
  have := (tendsto_pow_atTop (α := ℝ) (two_ne_zero)).comp tendsto_abs_atBot_atTop
  simpa [Function.comp_def, sq_abs] using this

theorem entering_type_with_plasma_condition (c : ℝ) (hc : 0 < c) :
    ∃ (P : ℝ → ℂ → ℂ) (gp : ℝ → ℂ),
      (∀ ω : ℝ, ω ≠ 0 →
        Differentiable ℝ (fun x : ℝ => P x (ω : ℂ)) ∧
        Tendsto (fun x : ℝ => P x (ω : ℂ)) atBot (𝓝 1) ∧
        Tendsto (fun x : ℝ => P x (ω : ℂ)) atTop (𝓝 (gp ω)) ∧
        Tendsto (fun x : ℝ => deriv (fun y : ℝ => P y (ω : ℂ)) x) atBot (𝓝 0) ∧
        Tendsto (fun x : ℝ => deriv (fun y : ℝ => P y (ω : ℂ)) x) atTop (𝓝 0)) ∧
      (∃ ω : ℝ, ω ≠ 0 ∧ gp ω ^ 2 ≠ 1) ∧
      CondAnalytic (perm c P) ∧ CondReality (perm c P) ∧ CondNoGain (perm c P) ∧
      CondLowFreq (-2) (perm c P) ∧ CondHighFreq (perm c P) := by
  refine ⟨etpP, fun ω => 1 + ((1/2 : ℝ) : ℂ) * etpH ω, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω hω
    refine ⟨fun x => (etpP_deriv x ω).differentiableAt, ?_, ?_, ?_, ?_⟩
    · have hF : Tendsto etpF atBot (𝓝 0) := by
        have := ((Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).div_const
          (2 * Real.pi)).const_add (1 / 4)
        have e : etpF = fun x => 1 / 4 + Real.arctan x / (2 * Real.pi) := rfl
        rw [e]
        convert this using 2
        have := Real.pi_pos; field_simp; ring
      have := (((Complex.continuous_ofReal.tendsto 0).comp hF).mul_const (etpH ω)).const_add 1
      simpa [etpP, Function.comp_def] using this
    · have hF : Tendsto etpF atTop (𝓝 (1/2)) := by
        have := ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).div_const
          (2 * Real.pi)).const_add (1 / 4)
        have e : etpF = fun x => 1 / 4 + Real.arctan x / (2 * Real.pi) := rfl
        rw [e]
        convert this using 2
        have := Real.pi_pos; field_simp; ring
      have := (((Complex.continuous_ofReal.tendsto _).comp hF).mul_const (etpH ω)).const_add 1
      simpa [etpP, Function.comp_def] using this
    · have h := (((Complex.continuous_ofReal.tendsto 0).comp (etpD_tendsto atBot sq_atBot)).mul_const
        (etpH ω))
      simp only [Function.comp_def, Complex.ofReal_zero, zero_mul] at h
      refine h.congr fun x => ?_
      rw [(etpP_deriv x ω).deriv]
    · have h := (((Complex.continuous_ofReal.tendsto 0).comp
        (etpD_tendsto atTop (tendsto_pow_atTop two_ne_zero))).mul_const (etpH ω))
      simp only [Function.comp_def, Complex.ofReal_zero, zero_mul] at h
      refine h.congr fun x => ?_
      rw [(etpP_deriv x ω).deriv]
  · refine ⟨1, one_ne_zero, ?_⟩
    have hH : etpH ((1:ℝ):ℂ) = -1/2 + 1/2 * Complex.I := by
      unfold etpH
      have : ((1:ℝ):ℂ) * (((1:ℝ):ℂ) + Complex.I) ≠ 0 := by
        simp only [Complex.ofReal_one, one_mul]; exact ne_I 1 (by simp)
      rw [div_eq_iff this]
      push_cast
      ring_nf; rw [Complex.I_sq]; ring
    show (1 + ((1/2:ℝ):ℂ) * etpH ((1:ℝ):ℂ)) ^ 2 ≠ 1
    rw [hH]
    intro h
    have := congrArg Complex.im h
    push_cast at this
    simp [sq, Complex.mul_im] at this
    norm_num at this
  · intro x
    rw [etp_formula c x]
    unfold etpH
    constructor
    · apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_im)
      intro w hw
      have hw' : 0 < w.im := hw
      have h1 := ne_I w hw'.le
      have h2 : w ≠ 0 := by intro h; rw [h] at hw'; simp at hw'
      have h3 : w * (w + Complex.I) ≠ 0 := mul_ne_zero h2 h1
      apply DifferentiableAt.differentiableWithinAt
      fun_prop (disch := assumption)
    · intro w hw
      have h1 := ne_I w hw.1
      have h2 : w ≠ 0 := hw.2
      have h3 : w * (w + Complex.I) ≠ 0 := mul_ne_zero h2 h1
      apply ContinuousAt.continuousWithinAt
      fun_prop (disch := assumption)
  · intro x ω hω
    rw [etp_formula c x]
    unfold etpH
    simp only [star_sub, star_mul', star_pow, star_add, star_one, star_div₀]
    simp only [Complex.star_def, Complex.conj_ofReal, Complex.conj_I, map_sub, map_mul, map_pow,
      map_div₀, map_add, map_one, map_neg, Complex.ofReal_neg]
    have e : -(ω : ℂ) * (-(ω : ℂ) + Complex.I) = (ω : ℂ) * ((ω : ℂ) + -Complex.I) := by ring
    rw [e]
    ring
  · intro x ω hω
    rw [etp_formula c x]
    set F := etpF x
    set D := etpD x
    have hF := etpF_pos x
    have hF2 := etpF_lt x
    have hD := etpD_pos x
    set A : ℝ := -1 / (ω ^ 2 + 1)
    set B : ℝ := 1 / (ω * (ω ^ 2 + 1))
    have hHe : etpH (ω : ℂ) = (A : ℂ) + (B : ℂ) * Complex.I := by
      unfold etpH
      have hne : (ω : ℂ) * ((ω : ℂ) + Complex.I) ≠ 0 :=
        mul_ne_zero (by exact_mod_cast hω.ne') (ne_I _ (by simp))
      rw [div_eq_iff hne]
      have hr : A * ω ^ 2 - B * ω = -1 := by simp only [A, B]; field_simp; ring
      have hi : A * ω + B * ω ^ 2 = 0 := by simp only [A, B]; field_simp; ring
      rw [show ((A : ℂ) + (B : ℂ) * Complex.I) * ((ω : ℂ) * ((ω : ℂ) + Complex.I)) =
          ((A * ω ^ 2 - B * ω : ℝ) : ℂ) + ((A * ω + B * ω ^ 2 : ℝ) : ℂ) * Complex.I by
        push_cast; linear_combination ((B : ℂ) * (ω : ℂ)) * Complex.I_sq]
      rw [hr, hi]; simp
    have hc' : Complex.I * (c : ℂ) / (ω : ℂ) = Complex.I * ((c / ω : ℝ) : ℂ) := by
      push_cast; ring
    show 0 < ((1 + (F : ℂ) * etpH ω) ^ 2 - Complex.I * (c : ℂ) / ω * ((D : ℂ) * etpH ω)).im
    rw [hHe, hc']
    have him : ((1 + (F : ℂ) * ((A : ℂ) + (B : ℂ) * Complex.I)) ^ 2 -
        Complex.I * ((c / ω : ℝ) : ℂ) * ((D : ℂ) * ((A : ℂ) + (B : ℂ) * Complex.I))).im =
        2 * F * B + 2 * F ^ 2 * A * B - c / ω * D * A := by
      simp [sq, Complex.mul_im, Complex.mul_re]; ring
    rw [him]
    have e : 2 * F * B + 2 * F ^ 2 * A * B - c / ω * D * A =
        (2 * F * (ω ^ 2 + 1 - F) + c * D * (ω ^ 2 + 1)) / (ω * (ω ^ 2 + 1) ^ 2) := by
      simp only [A, B]; field_simp; ring
    rw [e]
    apply div_pos _ (by positivity)
    have : 0 < ω ^ 2 + 1 - F := by nlinarith
    positivity
  · refine ⟨-2, le_refl _, fun x => ?_⟩
    set F : ℂ := (etpF x : ℂ)
    set D : ℂ := (etpD x : ℂ)
    set g : ℝ → ℂ := fun ω => -1 / ((ω : ℂ) + Complex.I) with hg
    set b : ℂ := (F * g 0) ^ 2 - Complex.I * c * D * g 0 with hb
    refine ⟨0, b, ?_⟩
    rw [etp_formula c x]
    rw [Asymptotics.isLittleO_iff_tendsto']
    swap
    · filter_upwards [self_mem_nhdsWithin] with ω (hω : ω ≠ 0)
      intro h; exfalso; simp at h; exact hω h
    set H : ℝ → ℂ := fun ω => ((ω : ℂ) + F * g ω) ^ 2 - Complex.I * c * D * g ω - b with hH
    have hc0 : ContinuousAt H 0 := by
      have : ((0:ℝ):ℂ) + Complex.I ≠ 0 := ne_I _ (by simp)
      rw [hH, hg]
      fun_prop (disch := assumption)
    have h0 : H 0 = 0 := by simp only [hH, hb]; push_cast; ring
    have hct := hc0.tendsto
    rw [h0] at hct
    clear_value b
    refine (hct.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ω (hω : ω ≠ 0)
    have hωc : (ω : ℂ) ≠ 0 := by exact_mod_cast hω
    have hZ := ne_I (ω : ℂ) (by simp)
    simp only [hH, hg, etpH, zpow_neg]
    rw [show ((ω : ℂ) ^ (2:ℤ)) = (ω : ℂ) ^ 2 from by norm_cast]
    field_simp
    ring
  · intro x
    set F : ℂ := (etpF x : ℂ)
    set D : ℂ := (etpD x : ℂ)
    refine ⟨-2 * F, ?_⟩
    rw [etp_formula c x]
    rw [Asymptotics.isLittleO_iff_tendsto']
    swap
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with ω hω
      intro h; exfalso; have : (ω : ℂ) ≠ 0 := by exact_mod_cast hω.ne'
      simp [this] at h
    set H : ℝ → ℂ := fun t => 2 * F * (1 - 1 / (1 + Complex.I * t)) +
      F ^ 2 * (t : ℂ) ^ 2 / (1 + Complex.I * t) ^ 2 +
      Complex.I * c * D * (t : ℂ) / (1 + Complex.I * t) with hH
    have hI : (1 + Complex.I * ((0:ℝ):ℂ)) ≠ 0 := by simp
    have hHc : ContinuousAt H 0 := by
      rw [hH]
      fun_prop (disch := first | assumption | exact pow_ne_zero _ hI)
    have hH0 : H 0 = 0 := by simp [hH]
    have hct := hHc.tendsto
    rw [hH0] at hct
    refine (hct.comp tendsto_inv_atTop_zero).congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with ω hω
    have hωc : (ω : ℂ) ≠ 0 := by exact_mod_cast hω.ne'
    have hZ := ne_I (ω : ℂ) (by simp)
    have hrel : (ω : ℂ) + Complex.I = ω * (1 + Complex.I * (ω : ℂ)⁻¹) := by
      field_simp
    have hT : 1 + Complex.I * (ω : ℂ)⁻¹ ≠ 0 := by
      intro h0; apply hZ; rw [hrel, h0, mul_zero]
    simp only [Function.comp_apply, hH, Complex.ofReal_inv, etpH]
    rw [hrel]
    generalize 1 + Complex.I * (ω : ℂ)⁻¹ = T at *
    field_simp
    ring

end Arxiv1510_02920
open Arxiv1510_02920 in
theorem solution (c : ℝ) (hc : 0 < c) :
    ∃ (P : ℝ → ℂ → ℂ) (gp : ℝ → ℂ),
      (∀ ω : ℝ, ω ≠ 0 →
        Differentiable ℝ (fun x : ℝ => P x (ω : ℂ)) ∧
        Tendsto (fun x : ℝ => P x (ω : ℂ)) atBot (𝓝 1) ∧
        Tendsto (fun x : ℝ => P x (ω : ℂ)) atTop (𝓝 (gp ω)) ∧
        Tendsto (fun x : ℝ => deriv (fun y : ℝ => P y (ω : ℂ)) x) atBot (𝓝 0) ∧
        Tendsto (fun x : ℝ => deriv (fun y : ℝ => P y (ω : ℂ)) x) atTop (𝓝 0)) ∧
      (∃ ω : ℝ, ω ≠ 0 ∧ gp ω ^ 2 ≠ 1) ∧
      CondAnalytic (perm c P) ∧ CondReality (perm c P) ∧ CondNoGain (perm c P) ∧
      CondLowFreq (-2) (perm c P) ∧ CondHighFreq (perm c P) :=
  entering_type_with_plasma_condition c hc
