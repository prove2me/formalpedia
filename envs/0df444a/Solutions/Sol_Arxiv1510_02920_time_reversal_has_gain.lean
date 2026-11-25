-- Prove2me | solution 1 for Arxiv1510_02920.time_reversal_has_gain
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T15:53:21.198007+00:00
-- url     : https://prove2.me/submissions/60d397b7-c07a-4821-ba4e-fd5b723f1381

import Mathlib
import Definitions.Def_Arxiv1510_02920_Basic

open Filter Topology Asymptotics

namespace Arxiv1510_02920
theorem im_perm_formula (c : ℝ) (hc : 0 < c) (γ : ℝ) (hγ : 0 < γ)
    (f : ℝ → ℝ) (hf : Differentiable ℝ f) (x ω : ℝ) (hω : ω ≠ 0) :
    (perm c (ansatzP f γ) x (ω : ℂ)).im =
      (4 * γ * ω ^ 2 * f x * ((γ ^ 2 + ω ^ 2) ^ 2 + (γ ^ 2 - ω ^ 2) * f x) -
          c * (γ ^ 2 - ω ^ 2) * (γ ^ 2 + ω ^ 2) ^ 2 * deriv f x) /
        (ω * (γ ^ 2 + ω ^ 2) ^ 4) := by
  set Z : ℂ := ((γ : ℂ) - Complex.I * ω) ^ 2 with hZ
  have hd : HasDerivAt (fun y : ℝ => ansatzP f γ y (ω : ℂ)) (((deriv f x : ℝ) : ℂ) / Z) x := by
    have := (((hf x).hasDerivAt.ofReal_comp).div_const Z).const_add 1
    exact this
  unfold perm
  rw [hd.deriv]
  unfold ansatzP
  rw [← hZ]
  have hZe : Z = ((γ ^ 2 - ω ^ 2 : ℝ) : ℂ) + ((-2 * γ * ω : ℝ) : ℂ) * Complex.I := by
    rw [hZ]; apply Complex.ext <;> simp [sq] <;> ring
  have hD : 0 < γ ^ 2 + ω ^ 2 := by positivity
  have hZinv : Z⁻¹ = (((γ ^ 2 - ω ^ 2) / (γ ^ 2 + ω ^ 2) ^ 2 : ℝ) : ℂ) +
      ((2 * γ * ω / (γ ^ 2 + ω ^ 2) ^ 2 : ℝ) : ℂ) * Complex.I := by
    rw [hZe]
    apply inv_eq_of_mul_eq_one_right
    have key1 : (γ ^ 2 - ω ^ 2) * ((γ ^ 2 - ω ^ 2) / (γ ^ 2 + ω ^ 2) ^ 2) -
        (-2 * γ * ω) * (2 * γ * ω / (γ ^ 2 + ω ^ 2) ^ 2) = 1 := by field_simp; ring
    have key2 : (γ ^ 2 - ω ^ 2) * (2 * γ * ω / (γ ^ 2 + ω ^ 2) ^ 2) +
        (-2 * γ * ω) * ((γ ^ 2 - ω ^ 2) / (γ ^ 2 + ω ^ 2) ^ 2) = 0 := by ring
    generalize (γ ^ 2 - ω ^ 2) = p at key1 key2 ⊢
    generalize (-2 * γ * ω) = r at key1 key2 ⊢
    generalize (p / (γ ^ 2 + ω ^ 2) ^ 2) = A at key1 key2 ⊢
    generalize (2 * γ * ω / (γ ^ 2 + ω ^ 2) ^ 2) = B at key1 key2 ⊢
    apply Complex.ext <;> simp <;> linarith
  simp only [div_eq_mul_inv _ Z, hZinv]
  simp only [sq, Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
    Complex.div_re, Complex.div_im, Complex.normSq_ofReal, Complex.inv_re, Complex.inv_im]
  field_simp
  ring

theorem im_perm_limits (c : ℝ) (hc : 0 < c) (γ : ℝ) (hγ : 0 < γ)
    (f : ℝ → ℝ) (hf : Differentiable ℝ f) (x : ℝ) :
    Tendsto (fun ω : ℝ => ω * (perm c (ansatzP f γ) x (ω : ℂ)).im) (𝓝[≠] 0)
        (𝓝 (-c * deriv f x / γ ^ 2)) ∧
      Tendsto (fun ω : ℝ => ω ^ 3 * (perm c (ansatzP f γ) x (ω : ℂ)).im) atTop
        (𝓝 (4 * γ * f x + c * deriv f x)) := by
  set F := f x with hFx
  set D := deriv f x with hDx
  have hγ2 : 0 < γ ^ 2 := by positivity
  constructor
  · set g : ℝ → ℝ := fun ω => (4 * γ * ω ^ 2 * F * ((γ ^ 2 + ω ^ 2) ^ 2 + (γ ^ 2 - ω ^ 2) * F) -
          c * (γ ^ 2 - ω ^ 2) * (γ ^ 2 + ω ^ 2) ^ 2 * D) / ((γ ^ 2 + ω ^ 2) ^ 4) with hg
    have hgc : ContinuousAt g 0 := by
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      positivity
    have hg0 : g 0 = -c * D / γ ^ 2 := by
      simp only [hg]; field_simp; ring
    rw [← hg0]
    refine (hgc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ω (hω : ω ≠ 0)
    rw [im_perm_formula c hc γ hγ f hf x ω hω, hg]
    try rw [← hFx]
    try rw [← hDx]
    have : 0 < γ ^ 2 + ω ^ 2 := by positivity
    field_simp
    try ring
  · set G : ℝ → ℝ := fun t => (4 * γ * F * (γ ^ 2 * t ^ 2 + 1) ^ 2 + 4 * γ * F ^ 2 * (γ ^ 2 * t ^ 4 - t ^ 2) -
        c * D * (γ ^ 2 * t ^ 2 - 1) * (γ ^ 2 * t ^ 2 + 1) ^ 2) / (γ ^ 2 * t ^ 2 + 1) ^ 4 with hG
    have hGc : ContinuousAt G 0 := by
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      positivity
    have hG0 : G 0 = 4 * γ * F + c * D := by simp only [hG]; ring
    rw [← hG0]
    refine (hGc.tendsto.comp tendsto_inv_atTop_zero).congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with ω hω
    rw [Function.comp_apply, im_perm_formula c hc γ hγ f hf x ω hω.ne', hG]
    have : 0 < γ ^ 2 + ω ^ 2 := by positivity
    field_simp
    ring

lemma ng_tanh_deriv (a : ℝ) (ha : 0 < a) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.tanh (-y / a)) (-1 / a / Real.cosh (-x / a) ^ 2) x := by
  have hin : HasDerivAt (fun y : ℝ => -y / a) (-1 / a) x := by
    simpa using ((hasDerivAt_id x).neg).div_const a
  have hs := (Real.hasDerivAt_sinh (-x / a)).comp x hin
  have hc := (Real.hasDerivAt_cosh (-x / a)).comp x hin
  have hq := hs.div hc (Real.cosh_pos _).ne'
  have e : (fun y : ℝ => Real.tanh (-y / a)) = fun y => Real.sinh (-y / a) / Real.cosh (-y / a) := by
    funext y; rw [Real.tanh_eq_sinh_div_cosh]
  rw [e]
  refine hq.congr_deriv ?_
  have h1 := Real.cosh_sq_sub_sinh_sq (-x / a)
  have h2 := (Real.cosh_pos (-x / a)).ne'
  have h1' : Real.cosh (-(x / a)) ^ 2 - Real.sinh (-(x / a)) ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq _
  simp only [Function.comp]
  field_simp
  linear_combination (-1) * h1'

theorem no_gain_requirements (c : ℝ) (hc : 0 < c) :
    (∀ (γ : ℝ) (f : ℝ → ℝ), 0 < γ → Differentiable ℝ f →
      (∀ x ω : ℝ, 0 < ω → 0 < (perm c (ansatzP f γ) x (ω : ℂ)).im) →
      (∀ x, deriv f x ≤ 0 ∧ c * |deriv f x| ≤ 4 * γ * f x ∧ 0 < f x) ∧ Antitone f) ∧
    (∀ Om a : ℝ, Om ≠ 0 → 0 < a →
      (∀ x, deriv (tanhProfile Om a) x < 0) ∧
      ∀ᶠ γ in atTop, ∀ x, c * |deriv (tanhProfile Om a) x| < 4 * γ * tanhProfile Om a x) := by
  constructor
  · intro γ f hγ hf hpos
    have key : ∀ x, deriv f x ≤ 0 ∧ c * |deriv f x| ≤ 4 * γ * f x ∧ 0 < f x := by
      intro x
      obtain ⟨l1, l2⟩ := im_perm_limits c hc γ hγ f hf x
      have hγ2 : 0 < γ ^ 2 := by positivity
      have g1 : 0 ≤ -c * deriv f x / γ ^ 2 := by
        refine ge_of_tendsto (l1.mono_left (nhdsWithin_mono _ (fun y (hy : y ∈ Set.Ioi (0:ℝ)) => ne_of_gt hy))) ?_
        filter_upwards [self_mem_nhdsWithin] with ω (hω : 0 < ω)
        exact (mul_pos hω (hpos x ω hω)).le
      have g2 : 0 ≤ 4 * γ * f x + c * deriv f x := by
        refine ge_of_tendsto l2 ?_
        filter_upwards [eventually_gt_atTop (0:ℝ)] with ω hω
        exact (mul_pos (pow_pos hω 3) (hpos x ω hω)).le
      have hD : deriv f x ≤ 0 := by
        have : 0 ≤ -c * deriv f x := by
          have := mul_nonneg g1 hγ2.le; rwa [div_mul_cancel₀ _ hγ2.ne'] at this
        nlinarith
      have hab : |deriv f x| = -deriv f x := abs_of_nonpos hD
      refine ⟨hD, by rw [hab]; linarith, ?_⟩
      by_contra hF
      have hF0 : f x = 0 := by nlinarith
      have hD0 : deriv f x = 0 := by
        have : 0 ≤ c * deriv f x := by rw [hF0] at g2; linarith
        nlinarith
      have := hpos x 1 one_pos
      rw [im_perm_formula c hc γ hγ f hf x 1 one_ne_zero, hF0, hD0] at this
      simp at this
    exact ⟨key, antitone_of_deriv_nonpos hf (fun x => (key x).1)⟩
  · intro Om a hOm ha
    have hO2 : 0 < Om ^ 2 := by positivity
    have hder : ∀ x, deriv (tanhProfile Om a) x = Om ^ 2 / 2 * (-1 / a / Real.cosh (-x / a) ^ 2) := by
      intro x
      have := ((ng_tanh_deriv a ha x).const_add 1).const_mul (Om ^ 2 / 2)
      exact this.deriv
    refine ⟨fun x => ?_, ?_⟩
    · rw [hder]
      have : 0 < Real.cosh (-x / a) ^ 2 := by positivity
      have : -1 / a / Real.cosh (-x / a) ^ 2 < 0 := by
        apply div_neg_of_neg_of_pos _ this; exact div_neg_of_neg_of_pos (by norm_num) ha
      nlinarith
    · filter_upwards [eventually_gt_atTop (c / (2 * a))] with γ hγ x
      rw [hder]
      set y := -x / a
      have hch : 0 < Real.cosh y := Real.cosh_pos y
      have hey : 0 < Real.exp y := Real.exp_pos y
      have hγpos : 0 < γ := lt_trans (by positivity) hγ
      have hcγ : c < 2 * γ * a := by
        rw [div_lt_iff₀ (by positivity)] at hγ; linarith
      have htanh : 1 + Real.tanh y = Real.exp y / Real.cosh y := by
        rw [Real.tanh_eq_sinh_div_cosh, ← Real.cosh_add_sinh]; field_simp
      have hexpc : 1 / 2 < Real.exp y * Real.cosh y := by
        rw [Real.cosh_eq]
        have : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
        nlinarith [sq_nonneg (Real.exp y)]
      have habs : |Om ^ 2 / 2 * (-1 / a / Real.cosh y ^ 2)| = Om ^ 2 / 2 * (1 / a / Real.cosh y ^ 2) := by
        rw [abs_mul, abs_of_pos (by positivity), abs_div, abs_div, abs_neg, abs_one, abs_of_pos ha,
          abs_of_pos (by positivity)]
      rw [habs]
      unfold tanhProfile
      rw [htanh]
      rw [show c * (Om ^ 2 / 2 * (1 / a / Real.cosh y ^ 2)) = (Om ^ 2 / 2) * (c / (a * Real.cosh y ^ 2)) by
        field_simp]
      rw [show 4 * γ * (Om ^ 2 / 2 * (Real.exp y / Real.cosh y)) =
        (Om ^ 2 / 2) * (4 * γ * Real.exp y / Real.cosh y) by ring]
      apply mul_lt_mul_of_pos_left _ (by positivity)
      rw [div_lt_div_iff₀ (by positivity) hch]
      have h5 : c < 4 * γ * a * (Real.exp y * Real.cosh y) := by nlinarith [mul_pos hγpos ha]
      have h6 := mul_lt_mul_of_pos_right h5 hch
      nlinarith [h6]

lemma tp_core (γ ω f g c a Om2 : ℝ) (hγ : 0 < γ) (hω : 0 < ω) (hf : 0 < f) (hfO : f < Om2)
    (hg : 0 < g) (hgf : g ≤ 2 / a * f) (ha : 0 < a) (hc : 0 < c)
    (hγ1 : c / a ≤ γ) (hγ2 : 2 * Om2 < γ ^ 2) :
    0 < 4 * γ * ω ^ 2 * f * ((γ ^ 2 + ω ^ 2) ^ 2 + (γ ^ 2 - ω ^ 2) * f) -
        c * (γ ^ 2 - ω ^ 2) * (γ ^ 2 + ω ^ 2) ^ 2 * (-g) := by
  set S := γ ^ 2 + ω ^ 2 with hS
  set d := γ ^ 2 - ω ^ 2 with hd
  have hS0 : 0 < S := by positivity
  have hω2 : 0 < ω ^ 2 := by positivity
  have hca : c / a * a = c := div_mul_cancel₀ c ha.ne'
  rcases le_or_gt 0 d with hd0 | hd0
  · have h1 : 0 < 4 * γ * ω ^ 2 * f * (S ^ 2 + d * f) := by positivity
    have h2 : 0 ≤ c * d * S ^ 2 * g := by positivity
    nlinarith
  · -- d < 0
    have hdS : -d ≤ S := by rw [hd, hS]; nlinarith
    have hdw : -d ≤ ω ^ 2 := by rw [hd]; nlinarith
    have hg' : c * g ≤ 2 * (c / a) * f := by
      have := mul_le_mul_of_nonneg_left hgf hc.le
      calc c * g ≤ c * (2 / a * f) := this
        _ = 2 * (c / a) * f := by ring
    -- term3: c*(-d)*S^2*g ≤ 2*(c/a)*f*(-d)*S^2 ≤ 2γ f ω² S²
    have t3 : c * (-d) * S ^ 2 * g ≤ 2 * γ * f * ω ^ 2 * S ^ 2 := by
      have e1 : c * (-d) * S ^ 2 * g = (c * g) * ((-d) * S ^ 2) := by ring
      have hnd : 0 < -d := by linarith
      have hpos : 0 < (-d) * S ^ 2 := by positivity
      rw [e1]
      calc (c * g) * ((-d) * S ^ 2) ≤ (2 * (c / a) * f) * ((-d) * S ^ 2) :=
            mul_le_mul_of_nonneg_right hg' hpos.le
        _ ≤ (2 * γ * f) * (ω ^ 2 * S ^ 2) := by
            apply mul_le_mul (by nlinarith) (by nlinarith [sq_nonneg S]) hpos.le (by positivity)
        _ = 2 * γ * f * ω ^ 2 * S ^ 2 := by ring
    -- term2: 4γω² (-d) f² ≤ 4γω² S Om2 f
    have t2 : 4 * γ * ω ^ 2 * (-d) * f ^ 2 ≤ 4 * γ * ω ^ 2 * f * (S * Om2) := by
      have : (-d) * f ≤ S * Om2 := mul_le_mul hdS hfO.le hf.le hS0.le
      have h4 : 0 ≤ 4 * γ * ω ^ 2 * f := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this h4]
    have hSγ : γ ^ 2 ≤ S := by rw [hS]; nlinarith
    have t4 : 2 * Om2 * S < γ ^ 2 * S := mul_lt_mul_of_pos_right hγ2 hS0
    have t5 : γ ^ 2 * S ≤ S * S := mul_le_mul_of_nonneg_right hSγ hS0.le
    have key : 4 * γ * ω ^ 2 * f * (S * Om2) + 2 * γ * f * ω ^ 2 * S ^ 2 < 4 * γ * ω ^ 2 * f * S ^ 2 := by
      have hk : 0 < γ * ω ^ 2 * f := by positivity
      have : 2 * (S * Om2) < S ^ 2 := by nlinarith
      nlinarith [mul_lt_mul_of_pos_left this hk]
    nlinarith

theorem tanh_profile_no_gain (c a Om : ℝ) (hc : 0 < c) (ha : 0 < a) (hOm : Om ≠ 0) :
    ∀ᶠ γ in atTop, CondNoGain (tanhPerm c Om a γ) := by
  have hdiff : Differentiable ℝ (tanhProfile Om a) := fun x =>
    (((ng_tanh_deriv a ha x).const_add 1).const_mul (Om ^ 2 / 2)).differentiableAt
  have hder : ∀ x, deriv (tanhProfile Om a) x = Om ^ 2 / 2 * (-1 / a / Real.cosh (-x / a) ^ 2) := by
    intro x
    exact (((ng_tanh_deriv a ha x).const_add 1).const_mul (Om ^ 2 / 2)).deriv
  have hO2 : 0 < Om ^ 2 := by positivity
  filter_upwards [eventually_ge_atTop (c / a), eventually_gt_atTop (2 * Om ^ 2 + 1)] with γ hγ1 hγ2
  have hγ : 0 < γ := by linarith
  have hγsq : 2 * Om ^ 2 < γ ^ 2 := by nlinarith
  intro x ω hω
  unfold tanhPerm tanhP
  rw [im_perm_formula c hc γ hγ _ hdiff x ω hω.ne']
  apply div_pos _ (by positivity)
  set y := -x / a with hy
  have hch : 0 < Real.cosh y := Real.cosh_pos y
  have hey : 0 < Real.exp y := Real.exp_pos y
  have htanh : 1 + Real.tanh y = Real.exp y / Real.cosh y := by
    rw [Real.tanh_eq_sinh_div_cosh, ← Real.cosh_add_sinh]; field_simp
  have hexpc : 1 / 2 < Real.exp y * Real.cosh y := by
    rw [Real.cosh_eq]
    have : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [sq_nonneg (Real.exp y)]
  have hfv : tanhProfile Om a x = Om ^ 2 / 2 * (Real.exp y / Real.cosh y) := by
    unfold tanhProfile; rw [← hy, htanh]
  have hf0 : 0 < tanhProfile Om a x := by rw [hfv]; positivity
  have hfO : tanhProfile Om a x < Om ^ 2 := by
    unfold tanhProfile
    have := Real.tanh_lt_one (-x / a)
    nlinarith
  have hgpos : 0 < -deriv (tanhProfile Om a) x := by
    rw [hder, ← hy]
    rw [show -(Om ^ 2 / 2 * (-1 / a / Real.cosh y ^ 2)) = Om ^ 2 / 2 * (1 / a / Real.cosh y ^ 2) by ring]
    positivity
  have hgf : -deriv (tanhProfile Om a) x ≤ 2 / a * tanhProfile Om a x := by
    rw [hder, ← hy, hfv]
    have e : 2 / a * (Om ^ 2 / 2 * (Real.exp y / Real.cosh y)) =
        (2 * Real.exp y * Real.cosh y) * (Om ^ 2 / 2 * (1 / a / Real.cosh y ^ 2)) := by
      field_simp
    rw [e, show -(Om ^ 2 / 2 * (-1 / a / Real.cosh y ^ 2)) = Om ^ 2 / 2 * (1 / a / Real.cosh y ^ 2) by ring]
    exact le_mul_of_one_le_left (by positivity) (by linarith)
  have := tp_core γ ω (tanhProfile Om a x) (-deriv (tanhProfile Om a) x) c a (Om ^ 2) hγ hω hf0 hfO
    hgpos hgf ha hc hγ1 hγsq
  rwa [neg_neg] at this


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


theorem ansatz_solves_helmholtz_iff (c : ℝ) (hc : 0 < c) (ω : ℝ) (hω : ω ≠ 0)
    (P : ℝ → ℂ → ℂ) (hP : Differentiable ℝ (fun x : ℝ => P x (ω : ℂ)))
    (gp gm : ℂ) (hPp : Tendsto (fun x : ℝ => P x (ω : ℂ)) atTop (𝓝 gp))
    (hPm : Tendsto (fun x : ℝ => P x (ω : ℂ)) atBot (𝓝 gm))
    (E0 : ℂ) (hE0 : E0 ≠ 0) (eps : ℝ → ℂ) :
    (∀ x, HelmholtzAt c ω eps (waveField c E0 P ω) x) ↔ ∀ x, eps x = perm c P x (ω : ℂ) := by
  set p : ℝ → ℂ := fun x => P x (ω : ℂ) with hpdef
  set k : ℂ := ((ω / c : ℝ) : ℂ) with hk
  set E := waveField c E0 P ω with hEdef
  have hint : ∀ x, HasDerivAt (fun u => ∫ t in (0:ℝ)..u, p t) (p x) x := fun x =>
    (hP.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hE : ∀ x, HasDerivAt E (Complex.I * k * p x * E x) x := by
    intro x
    have h1 := (((hint x).const_mul (Complex.I * k)).cexp).const_mul E0
    have hfE : E = fun y => E0 * Complex.exp (Complex.I * k * ∫ t in (0:ℝ)..y, p t) := rfl
    rw [hfE]
    exact h1.congr_deriv (by beta_reduce; ring)
  have hdE : deriv E = fun x => Complex.I * k * p x * E x := funext fun x => (hE x).deriv
  have hE2 : ∀ x, HasDerivAt (deriv E)
      (Complex.I * k * (deriv p x * E x + p x * (Complex.I * k * p x * E x))) x := by
    intro x
    rw [hdE]
    have := (((hP x).hasDerivAt.mul (hE x)).const_mul (Complex.I * k))
    have hf : (fun x => Complex.I * k * p x * E x) = fun y => Complex.I * k * (p * E) y := by
      funext y; simp only [Pi.mul_apply]; ring
    rw [hf]; exact this
  have hEne : ∀ x, E x ≠ 0 := by
    intro x; simp only [hEdef, waveField]
    exact mul_ne_zero hE0 (Complex.exp_ne_zero _)
  have hkne : k ≠ 0 := by
    simp only [hk]; exact_mod_cast div_ne_zero hω hc.ne'
  have key : ∀ x, deriv (deriv E) x + ((ω / c : ℝ) : ℂ) ^ 2 * eps x * E x =
      k ^ 2 * E x * (eps x - perm c P x (ω : ℂ)) := by
    intro x
    rw [(hE2 x).deriv]
    unfold perm
    rw [← hk]
    have hωc : (ω : ℂ) ≠ 0 := by exact_mod_cast hω
    have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hkk : k = (ω : ℂ) / (c : ℂ) := by simp [hk]
    rw [hkk]
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  constructor
  · intro h x
    have := (h x).2.2
    rw [key x] at this
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 (mul_ne_zero (pow_ne_zero _ hkne) (hEne x))
    · exact sub_eq_zero.1 h0
  · intro h x
    refine ⟨Filter.Eventually.of_forall fun y => (hE y).differentiableAt, (hE2 x).differentiableAt, ?_⟩
    rw [key x, h x, sub_self, mul_zero]


noncomputable def ewF (Om a x : ℝ) : ℝ := Om ^ 2 / (1 + Real.exp (2 * x / a))
noncomputable def ewG (Om a x : ℝ) : ℝ := Om ^ 2 * (x - a / 2 * Real.log (1 + Real.exp (2 * x / a)))

lemma ew_profile (Om a : ℝ) (ha : 0 < a) : tanhProfile Om a = ewF Om a := by
  funext x
  unfold tanhProfile ewF
  rw [Real.tanh_eq]
  have e1 : Real.exp (2 * x / a) = Real.exp (x / a) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e2 : Real.exp (-(-x / a)) = Real.exp (x / a) := by congr 1; ring
  have e3 : Real.exp (-x / a) = (Real.exp (x / a))⁻¹ := by rw [← Real.exp_neg]; congr 1; ring
  rw [e1, e2, e3]
  have hu := Real.exp_pos (x / a)
  field_simp
  ring

lemma ewF_deriv (Om a : ℝ) (x : ℝ) :
    HasDerivAt (ewF Om a) (-(Om ^ 2 * (Real.exp (2 * x / a) * (2 / a))) /
      (1 + Real.exp (2 * x / a)) ^ 2) x := by
  have hin : HasDerivAt (fun y : ℝ => 2 * y / a) (2 / a) x := by
    simpa using ((hasDerivAt_id x).const_mul 2).div_const a
  have h1 := ((Real.hasDerivAt_exp (2 * x / a)).comp x hin).const_add 1
  have hpos : (1 + Real.exp (2 * x / a)) ≠ 0 := by positivity
  have := h1.inv hpos
  have := this.const_mul (Om ^ 2)
  refine HasDerivAt.congr_of_eventuallyEq (this.congr_deriv ?_) (Eventually.of_forall fun y => ?_)
  · simp only [Function.comp]; field_simp
  · simp [ewF, div_eq_mul_inv]

lemma ewG_deriv (Om a : ℝ) (ha : 0 < a) (x : ℝ) : HasDerivAt (ewG Om a) (ewF Om a x) x := by
  have hin : HasDerivAt (fun y : ℝ => 2 * y / a) (2 / a) x := by
    simpa using ((hasDerivAt_id x).const_mul 2).div_const a
  have h1 := ((Real.hasDerivAt_exp (2 * x / a)).comp x hin).const_add 1
  have hpos : (1 + Real.exp (2 * x / a)) ≠ 0 := by positivity
  have hl := h1.log hpos
  have := (((hasDerivAt_id x).sub (hl.const_mul (a / 2)))).const_mul (Om ^ 2)
  refine HasDerivAt.congr_of_eventuallyEq (this.congr_deriv ?_) (Eventually.of_forall fun y => ?_)
  · simp only [Function.comp, id, ewF]
    field_simp
    ring
  · simp [ewG]

lemma ewF_cont (Om a : ℝ) : Continuous (ewF Om a) :=
  continuous_iff_continuousAt.2 fun x => (ewF_deriv Om a x).continuousAt

lemma ewF_int (Om a : ℝ) (ha : 0 < a) (x : ℝ) :
    ∫ t in (0:ℝ)..x, ewF Om a t = ewG Om a x - ewG Om a 0 :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => ewG_deriv Om a ha t)
    ((ewF_cont Om a).intervalIntegrable _ _)

lemma ewG_top (Om a : ℝ) (ha : 0 < a) : Tendsto (ewG Om a) atTop (𝓝 0) := by
  have hexp : Tendsto (fun x : ℝ => Real.exp ((-2 / a) * x)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by
      have : 0 < 2 / a := by positivity
      linarith [show -2 / a = -(2 / a) by ring]))
  have hc : Tendsto (fun x : ℝ => -(Om ^ 2 * (a / 2)) * Real.log (1 + Real.exp ((-2 / a) * x)))
      atTop (𝓝 (-(Om ^ 2 * (a / 2)) * Real.log (1 + 0))) := by
    apply Tendsto.const_mul
    apply Tendsto.log (tendsto_const_nhds.add hexp) (by norm_num)
  simp only [add_zero, Real.log_one, mul_zero] at hc
  refine hc.congr fun x => ?_
  unfold ewG
  have e : 1 + Real.exp (2 * x / a) = Real.exp (2 * x / a) * (1 + Real.exp ((-2 / a) * x)) := by
    rw [mul_add, mul_one, ← Real.exp_add]
    have : 2 * x / a + -2 / a * x = 0 := by ring
    rw [this, Real.exp_zero]; ring
  rw [e, Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp]
  field_simp
  ring

lemma ewG_bot (Om a : ℝ) (ha : 0 < a) :
    Tendsto (fun x => ewG Om a x - Om ^ 2 * x) atBot (𝓝 0) := by
  have hexp : Tendsto (fun x : ℝ => Real.exp ((2 / a) * x)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot (by positivity))
  have hc : Tendsto (fun x : ℝ => -(Om ^ 2 * (a / 2)) * Real.log (1 + Real.exp ((2 / a) * x)))
      atBot (𝓝 (-(Om ^ 2 * (a / 2)) * Real.log (1 + 0))) := by
    apply Tendsto.const_mul
    apply Tendsto.log (tendsto_const_nhds.add hexp) (by norm_num)
  simp only [add_zero, Real.log_one, mul_zero] at hc
  refine hc.congr fun x => ?_
  unfold ewG
  have : 2 / a * x = 2 * x / a := by ring
  rw [this]; ring



lemma ew_wave_deriv (c : ℝ) (ω : ℝ) (P : ℝ → ℂ → ℂ) (hP : Differentiable ℝ (fun x : ℝ => P x (ω : ℂ)))
    (E0 : ℂ) (x : ℝ) :
    HasDerivAt (waveField c E0 P ω)
      (Complex.I * ((ω / c : ℝ) : ℂ) * P x (ω : ℂ) * waveField c E0 P ω x) x := by
  have hint : HasDerivAt (fun u => ∫ t in (0:ℝ)..u, P t (ω : ℂ)) (P x (ω : ℂ)) x :=
    (hP.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt
  have h1 := (((hint).const_mul (Complex.I * ((ω / c : ℝ) : ℂ))).cexp).const_mul E0
  have hfE : waveField c E0 P ω = fun y => E0 * Complex.exp (Complex.I * ((ω / c : ℝ) : ℂ) *
      ∫ t in (0:ℝ)..y, P t (ω : ℂ)) := rfl
  rw [hfE]
  exact h1.congr_deriv (by beta_reduce; ring)

lemma ewD_tendsto (Om a : ℝ) (l : Filter ℝ) (u : ℝ → ℝ) (hu : Tendsto u l (𝓝 0)) :
    Tendsto (fun x => -(Om ^ 2 * (u x * (2 / a))) / (1 + u x) ^ 2) l (𝓝 0) := by
  have := ((((hu.mul_const (2 / a)).const_mul (Om ^ 2)).neg).div
    (((tendsto_const_nhds (x := (1:ℝ))).add hu).pow 2) (by norm_num))
  convert this using 2
  all_goals simp

lemma exp_lin_top (a : ℝ) (ha : 0 < a) : Tendsto (fun x : ℝ => Real.exp (2 * x / a)) atTop atTop := by
  have := Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (show 0 < 2 / a by positivity))
  refine this.congr fun x => ?_
  simp only [Function.comp, id]; congr 1; ring

lemma exp_lin_bot (a : ℝ) (ha : 0 < a) : Tendsto (fun x : ℝ => Real.exp (2 * x / a)) atBot (𝓝 0) := by
  have := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot (show 0 < 2 / a by positivity))
  refine this.congr fun x => ?_
  simp only [Function.comp, id]; congr 1; ring

lemma exp_nlin_top (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℝ => Real.exp (-(2 * x / a))) atTop (𝓝 0) := by
  have := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
    (show -(2 / a) < 0 by have h : 0 < 2 / a := (by positivity); linarith))
  refine this.congr fun x => ?_
  simp only [Function.comp, id]; congr 1; ring

theorem exiting_wave_reflectionless (c a Om : ℝ) (hc : 0 < c) (ha : 0 < a) (hOm : Om ≠ 0) :
    (∀ γ : ℝ, 0 < γ →
      (∀ ω : ℝ, ω ≠ 0 →
        Tendsto (fun x : ℝ => tanhPerm c Om a γ x (ω : ℂ)) atTop (𝓝 1) ∧
        Tendsto (fun x : ℝ => tanhPerm c Om a γ x (ω : ℂ)) atBot
          (𝓝 (mediumIndex Om γ ω ^ 2)) ∧
        Tendsto (fun x : ℝ => tanhP Om a γ x (ω : ℂ)) atTop (𝓝 1) ∧
        Tendsto (fun x : ℝ => tanhP Om a γ x (ω : ℂ)) atBot (𝓝 (mediumIndex Om γ ω))) ∧
      CondAnalytic (tanhPerm c Om a γ) ∧ CondReality (tanhPerm c Om a γ) ∧
      CondLowFreq (-1) (tanhPerm c Om a γ) ∧ CondHighFreq (tanhPerm c Om a γ) ∧
      (∀ ω : ℝ, ω ≠ 0 → ∀ E0 : ℂ, E0 ≠ 0 →
        (∀ x, HelmholtzAt c ω (fun y => tanhPerm c Om a γ y (ω : ℂ))
          (waveField c E0 (tanhP Om a γ) ω) x) ∧
        (∀ x, deriv (waveField c E0 (tanhP Om a γ) ω) x =
          Complex.I * ((ω / c : ℝ) : ℂ) * tanhP Om a γ x (ω : ℂ) *
            waveField c E0 (tanhP Om a γ) ω x) ∧
        (∃ T : ℂ, T ≠ 0 ∧ Tendsto (fun x : ℝ => waveField c E0 (tanhP Om a γ) ω x *
          Complex.exp (-(Complex.I * ((ω / c : ℝ) : ℂ) * x))) atTop (𝓝 T)) ∧
        (∃ A : ℂ, A ≠ 0 ∧ Tendsto (fun x : ℝ => waveField c E0 (tanhP Om a γ) ω x *
          Complex.exp (-(Complex.I * ((ω / c : ℝ) : ℂ) * mediumIndex Om γ ω * x))) atBot
          (𝓝 A)))) ∧
    ∀ᶠ γ in atTop, CondNoGain (tanhPerm c Om a γ) := by
  have hdiff : Differentiable ℝ (tanhProfile Om a) := by
    rw [ew_profile Om a ha]; exact fun x => (ewF_deriv Om a x).differentiableAt
  refine ⟨fun γ hγ => ?_, tanh_profile_no_gain c a Om hc ha hOm⟩
  have hcond := ansatz_satisfies_conditions c hc γ hγ _ hdiff
  -- per-frequency facts
  have hPeq : ∀ ω : ℝ, ∀ x, tanhP Om a γ x (ω : ℂ) =
      1 + (ewF Om a x : ℂ) / ((γ : ℂ) - Complex.I * ω) ^ 2 := by
    intro ω x; unfold tanhP ansatzP; rw [ew_profile Om a ha]
  have hPd : ∀ ω : ℝ, ∀ x, HasDerivAt (fun y => tanhP Om a γ y (ω : ℂ))
      (((-(Om ^ 2 * (Real.exp (2 * x / a) * (2 / a))) / (1 + Real.exp (2 * x / a)) ^ 2 : ℝ) : ℂ) /
        ((γ : ℂ) - Complex.I * ω) ^ 2) x := by
    intro ω x
    have := (((ewF_deriv Om a x).ofReal_comp).div_const (((γ : ℂ) - Complex.I * ω) ^ 2)).const_add 1
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    exact hPeq ω y
  have hPdiff : ∀ ω : ℝ, Differentiable ℝ (fun x : ℝ => tanhP Om a γ x (ω : ℂ)) :=
    fun ω x => (hPd ω x).differentiableAt
  have hFtop : Tendsto (ewF Om a) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ 1 (exp_lin_top a ha))
  have hFbot : Tendsto (ewF Om a) atBot (𝓝 (Om ^ 2)) := by
    have := tendsto_const_nhds (x := Om ^ 2) |>.div ((tendsto_const_nhds (x := (1:ℝ))).add (exp_lin_bot a ha))
      (by norm_num)
    have e : ewF Om a = fun x => Om ^ 2 / (1 + Real.exp (2 * x / a)) := rfl
    rw [e]
    convert this using 2
    all_goals simp
  have hDtop : Tendsto (fun x => -(Om ^ 2 * (Real.exp (2 * x / a) * (2 / a))) /
      (1 + Real.exp (2 * x / a)) ^ 2) atTop (𝓝 0) := by
    refine (ewD_tendsto Om a atTop _ (exp_nlin_top a ha)).congr fun x => ?_
    have e : Real.exp (2 * x / a) = (Real.exp (-(2 * x / a)))⁻¹ := by rw [Real.exp_neg, inv_inv]
    rw [e]
    have := Real.exp_pos (-(2 * x / a))
    field_simp
    ring
  have hDbot : Tendsto (fun x => -(Om ^ 2 * (Real.exp (2 * x / a) * (2 / a))) /
      (1 + Real.exp (2 * x / a)) ^ 2) atBot (𝓝 0) :=
    ewD_tendsto Om a atBot _ (exp_lin_bot a ha)
  have hlimP : ∀ ω : ℝ, ∀ (l : Filter ℝ) (L : ℝ), Tendsto (ewF Om a) l (𝓝 L) →
      Tendsto (fun x : ℝ => tanhP Om a γ x (ω : ℂ)) l
        (𝓝 (1 + (L : ℂ) / ((γ : ℂ) - Complex.I * ω) ^ 2)) := by
    intro ω l L h
    have := (((Complex.continuous_ofReal.tendsto L).comp h).div_const
      (((γ : ℂ) - Complex.I * ω) ^ 2)).const_add 1
    refine this.congr fun x => ?_
    rw [hPeq ω x]; rfl
  have hlimE : ∀ ω : ℝ, ∀ (l : Filter ℝ) (L : ℝ), Tendsto (ewF Om a) l (𝓝 L) →
      Tendsto (fun x => -(Om ^ 2 * (Real.exp (2 * x / a) * (2 / a))) /
        (1 + Real.exp (2 * x / a)) ^ 2) l (𝓝 0) →
      Tendsto (fun x : ℝ => tanhPerm c Om a γ x (ω : ℂ)) l
        (𝓝 ((1 + (L : ℂ) / ((γ : ℂ) - Complex.I * ω) ^ 2) ^ 2)) := by
    intro ω l L h hD
    have h2 := ((Complex.continuous_ofReal.tendsto 0).comp hD).div_const
      (((γ : ℂ) - Complex.I * ω) ^ 2)
    have := ((hlimP ω l L h).pow 2).sub (h2.const_mul (Complex.I * (c : ℂ) / (ω : ℂ)))
    simp only [Complex.ofReal_zero, zero_div, mul_zero, sub_zero] at this
    refine this.congr fun x => ?_
    unfold tanhPerm perm
    rw [(hPd ω x).deriv]
    rfl
  have hM : ∀ ω : ℝ, mediumIndex Om γ ω = 1 + ((Om ^ 2 : ℝ) : ℂ) / ((γ : ℂ) - Complex.I * ω) ^ 2 :=
    fun ω => rfl
  refine ⟨fun ω hω => ⟨?_, ?_, ?_, ?_⟩, hcond.1, hcond.2.1, hcond.2.2.1, hcond.2.2.2,
    fun ω hω E0 hE0 => ⟨?_, ?_, ?_, ?_⟩⟩
  · simpa using hlimE ω atTop 0 hFtop hDtop
  · rw [hM]; exact hlimE ω atBot _ hFbot hDbot
  · simpa using hlimP ω atTop 0 hFtop
  · rw [hM]; exact hlimP ω atBot _ hFbot
  · have h1 := hlimP ω atTop 0 hFtop
    have h2 := hlimP ω atBot _ hFbot
    exact (ansatz_solves_helmholtz_iff c hc ω hω (tanhP Om a γ) (hPdiff ω) _ _ h1 h2 E0 hE0
      (fun y => tanhPerm c Om a γ y (ω : ℂ))).2 (fun x => rfl)
  · intro x; exact (ew_wave_deriv c ω (tanhP Om a γ) (hPdiff ω) E0 x).deriv
  · -- integral formula
    set Z : ℂ := ((γ : ℂ) - Complex.I * ω) ^ 2 with hZ
    have hZne : Z ≠ 0 := pow_ne_zero _ (asc_ne γ hγ (ω : ℂ) (by simp))
    have hInt : ∀ x : ℝ, ∫ t in (0:ℝ)..x, tanhP Om a γ t (ω : ℂ) =
        (x : ℂ) + ((ewG Om a x - ewG Om a 0 : ℝ) : ℂ) / Z := by
      intro x
      simp_rw [hPeq ω, ← hZ]
      rw [intervalIntegral.integral_add (f := fun _ => (1:ℂ)) (g := fun t => (ewF Om a t : ℂ) / Z)
        intervalIntegrable_const
        (by exact ((Complex.continuous_ofReal.comp (ewF_cont Om a)).div_const Z).intervalIntegrable 0 x),
        intervalIntegral.integral_const, intervalIntegral.integral_div,
        intervalIntegral.integral_ofReal, ewF_int Om a ha x]
      simp
      try rw [hZ]
    have hW : ∀ x : ℝ, waveField c E0 (tanhP Om a γ) ω x =
        E0 * Complex.exp (Complex.I * ((ω / c : ℝ) : ℂ) *
          ((x : ℂ) + ((ewG Om a x - ewG Om a 0 : ℝ) : ℂ) / Z)) := by
      intro x; unfold waveField; rw [hInt x]
    refine ⟨E0 * Complex.exp (Complex.I * ((ω / c : ℝ) : ℂ) * (((0 - ewG Om a 0 : ℝ) : ℂ) / Z)),
      mul_ne_zero hE0 (Complex.exp_ne_zero _), ?_⟩
    have hG := ((Complex.continuous_ofReal.tendsto _).comp
      ((ewG_top Om a ha).sub_const (ewG Om a 0)))
    have := ((((hG.div_const Z).const_mul (Complex.I * ((ω / c : ℝ) : ℂ))).cexp).const_mul E0)
    refine this.congr fun x => ?_
    rw [hW x, mul_assoc E0, ← Complex.exp_add]
    simp only [Function.comp]
    congr 2
    push_cast
    ring
  · set Z : ℂ := ((γ : ℂ) - Complex.I * ω) ^ 2 with hZ
    have hZne : Z ≠ 0 := pow_ne_zero _ (asc_ne γ hγ (ω : ℂ) (by simp))
    have hInt : ∀ x : ℝ, ∫ t in (0:ℝ)..x, tanhP Om a γ t (ω : ℂ) =
        (x : ℂ) + ((ewG Om a x - ewG Om a 0 : ℝ) : ℂ) / Z := by
      intro x
      simp_rw [hPeq ω, ← hZ]
      rw [intervalIntegral.integral_add (f := fun _ => (1:ℂ)) (g := fun t => (ewF Om a t : ℂ) / Z)
        intervalIntegrable_const
        (by exact ((Complex.continuous_ofReal.comp (ewF_cont Om a)).div_const Z).intervalIntegrable 0 x),
        intervalIntegral.integral_const, intervalIntegral.integral_div,
        intervalIntegral.integral_ofReal, ewF_int Om a ha x]
      simp
      try rw [hZ]
    have hW : ∀ x : ℝ, waveField c E0 (tanhP Om a γ) ω x =
        E0 * Complex.exp (Complex.I * ((ω / c : ℝ) : ℂ) *
          ((x : ℂ) + ((ewG Om a x - ewG Om a 0 : ℝ) : ℂ) / Z)) := by
      intro x; unfold waveField; rw [hInt x]
    refine ⟨E0 * Complex.exp (Complex.I * ((ω / c : ℝ) : ℂ) * (((0 - ewG Om a 0 : ℝ) : ℂ) / Z)),
      mul_ne_zero hE0 (Complex.exp_ne_zero _), ?_⟩
    have hG := ((Complex.continuous_ofReal.tendsto _).comp
      ((ewG_bot Om a ha).sub_const (ewG Om a 0)))
    have := ((((hG.div_const Z).const_mul (Complex.I * ((ω / c : ℝ) : ℂ))).cexp).const_mul E0)
    refine this.congr fun x => ?_
    rw [hW x, mul_assoc E0, ← Complex.exp_add, hM ω, ← hZ]
    simp only [Function.comp]
    congr 2
    push_cast
    ring


theorem time_reversal_has_gain (c a Om : ℝ) (hc : 0 < c) (ha : 0 < a) (hOm : Om ≠ 0) :
    (∀ γ : ℝ, 0 < γ → ∀ ω : ℝ, ω ≠ 0 → ∀ E0 : ℂ, E0 ≠ 0 →
      (∀ x, HelmholtzAt c ω (fun y => star (tanhPerm c Om a γ y (ω : ℂ)))
        (fun y => star (waveField c E0 (tanhP Om a γ) ω y)) x) ∧
      (∀ x, deriv (fun y => star (waveField c E0 (tanhP Om a γ) ω y)) x =
        -(Complex.I * ((ω / c : ℝ) : ℂ) * star (tanhP Om a γ x (ω : ℂ)) *
          star (waveField c E0 (tanhP Om a γ) ω x))) ∧
      (∃ T : ℂ, T ≠ 0 ∧ Tendsto (fun x : ℝ => star (waveField c E0 (tanhP Om a γ) ω x) *
        Complex.exp (Complex.I * ((ω / c : ℝ) : ℂ) * x)) atTop (𝓝 T)) ∧
      (∃ A : ℂ, A ≠ 0 ∧ Tendsto (fun x : ℝ => star (waveField c E0 (tanhP Om a γ) ω x) *
        Complex.exp (Complex.I * ((ω / c : ℝ) : ℂ) * star (mediumIndex Om γ ω) * x))
        atBot (𝓝 A))) ∧
    ∀ᶠ γ in atTop, ∀ x ω : ℝ, 0 < ω → (star (tanhPerm c Om a γ x (ω : ℂ))).im < 0 := by
  have EW := exiting_wave_reflectionless c a Om hc ha hOm
  refine ⟨fun γ hγ ω hω E0 hE0 => ?_, ?_⟩
  · obtain ⟨-, -, -, -, -, hw⟩ := EW.1 γ hγ
    obtain ⟨hh, hd, ⟨T, hT, hTt⟩, ⟨A, hA, hAt⟩⟩ := hw ω hω E0 hE0
    refine ⟨fun x => ?_, fun x => ?_, ⟨star T, star_ne_zero.2 hT, ?_⟩, ⟨star A, star_ne_zero.2 hA, ?_⟩⟩
    · obtain ⟨h1, h2, h3⟩ := hh x
      refine ⟨h1.mono fun y hy => hy.star, ?_, ?_⟩
      · rw [deriv.star']; exact h2.star
      · rw [deriv.star', deriv.star]
        have hk : star (((ω / c : ℝ) : ℂ) ^ 2) = ((ω / c : ℝ) : ℂ) ^ 2 := by
          simp [Complex.conj_ofReal]
        beta_reduce
        rw [← hk, ← star_mul', ← star_mul', ← star_add, h3, star_zero]
    · rw [deriv.star, hd x]
      simp only [star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
      ring
    · have := (continuous_star.tendsto T).comp hTt
      refine this.congr fun x => ?_
      simp only [Function.comp, star_mul', Complex.star_def, ← Complex.exp_conj, map_neg, map_mul,
        Complex.conj_I, Complex.conj_ofReal]
      ring_nf
    · have := (continuous_star.tendsto A).comp hAt
      refine this.congr fun x => ?_
      simp only [Function.comp, star_mul', Complex.star_def, ← Complex.exp_conj, map_neg, map_mul,
        Complex.conj_I, Complex.conj_ofReal]
      ring_nf
  · filter_upwards [EW.2] with γ hγ
    intro x ω hω
    have := hγ x ω hω
    simp only [Complex.star_def, Complex.conj_im]
    linarith

end Arxiv1510_02920
open Arxiv1510_02920 in
theorem solution (c a Om : ℝ) (hc : 0 < c) (ha : 0 < a) (hOm : Om ≠ 0) :
    (∀ γ : ℝ, 0 < γ → ∀ ω : ℝ, ω ≠ 0 → ∀ E0 : ℂ, E0 ≠ 0 →
      (∀ x, HelmholtzAt c ω (fun y => star (tanhPerm c Om a γ y (ω : ℂ)))
        (fun y => star (waveField c E0 (tanhP Om a γ) ω y)) x) ∧
      (∀ x, deriv (fun y => star (waveField c E0 (tanhP Om a γ) ω y)) x =
        -(Complex.I * ((ω / c : ℝ) : ℂ) * star (tanhP Om a γ x (ω : ℂ)) *
          star (waveField c E0 (tanhP Om a γ) ω x))) ∧
      (∃ T : ℂ, T ≠ 0 ∧ Tendsto (fun x : ℝ => star (waveField c E0 (tanhP Om a γ) ω x) *
        Complex.exp (Complex.I * ((ω / c : ℝ) : ℂ) * x)) atTop (𝓝 T)) ∧
      (∃ A : ℂ, A ≠ 0 ∧ Tendsto (fun x : ℝ => star (waveField c E0 (tanhP Om a γ) ω x) *
        Complex.exp (Complex.I * ((ω / c : ℝ) : ℂ) * star (mediumIndex Om γ ω) * x))
        atBot (𝓝 A))) ∧
    ∀ᶠ γ in atTop, ∀ x ω : ℝ, 0 < ω → (star (tanhPerm c Om a γ x (ω : ℂ))).im < 0 :=
  time_reversal_has_gain c a Om hc ha hOm
