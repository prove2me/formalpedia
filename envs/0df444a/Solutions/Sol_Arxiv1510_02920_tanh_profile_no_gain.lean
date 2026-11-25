-- Prove2me | solution 1 for Arxiv1510_02920.tanh_profile_no_gain
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T15:06:52.551781+00:00
-- url     : https://prove2.me/submissions/321e2c8c-87eb-4f13-9f65-a406da7a1f30

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

end Arxiv1510_02920
open Arxiv1510_02920 in
theorem solution (c a Om : ℝ) (hc : 0 < c) (ha : 0 < a) (hOm : Om ≠ 0) :
    ∀ᶠ γ in atTop, CondNoGain (tanhPerm c Om a γ) :=
  tanh_profile_no_gain c a Om hc ha hOm
