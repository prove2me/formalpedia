-- Prove2me | solution 1 for Arxiv1510_02920.no_vacuum_both_sides
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T15:02:33.137533+00:00
-- url     : https://prove2.me/submissions/6b9d9e79-f89f-433a-b197-f5c06bbfa22d

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

theorem no_vacuum_both_sides (c : ℝ) (hc : 0 < c) (γ : ℝ) (hγ : 0 < γ)
    (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hgain : CondNoGain (perm c (ansatzP f γ))) (ω : ℝ) (hω : ω ≠ 0) :
    ¬ (Tendsto (fun x : ℝ => ansatzP f γ x (ω : ℂ)) atTop (𝓝 1) ∧
        Tendsto (fun x : ℝ => ansatzP f γ x (ω : ℂ)) atBot (𝓝 1)) := by
  rintro ⟨-, hbot⟩
  obtain ⟨hkey, hanti⟩ := (no_gain_requirements c hc).1 γ f hγ hf (fun x ω hω => hgain x ω hω)
  set Z : ℂ := ((γ : ℂ) - Complex.I * ω) ^ 2 with hZ
  have hZ0 : Z ≠ 0 := by
    apply pow_ne_zero; intro h; have := congrArg Complex.re h; simp at this; linarith
  have hf0 : Tendsto (fun x => (f x : ℂ)) atBot (𝓝 0) := by
    have := (hbot.sub_const 1).mul_const Z
    simp only [sub_self, zero_mul] at this
    refine this.congr' (Eventually.of_forall fun x => ?_)
    simp only [ansatzP, ← hZ]
    field_simp
    ring
  have hfr : Tendsto f atBot (𝓝 0) := by
    have := (Complex.continuous_re.tendsto _).comp hf0
    simpa [Function.comp_def] using this
  have hpos := (hkey 0).2.2
  have : f 0 ≤ 0 := ge_of_tendsto hfr (Filter.eventually_atBot.mpr ⟨0, fun x hx => hanti hx⟩)
  linarith

end Arxiv1510_02920
open Arxiv1510_02920 in
theorem solution (c : ℝ) (hc : 0 < c) (γ : ℝ) (hγ : 0 < γ)
    (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hgain : CondNoGain (perm c (ansatzP f γ))) (ω : ℝ) (hω : ω ≠ 0) :
    ¬ (Tendsto (fun x : ℝ => ansatzP f γ x (ω : ℂ)) atTop (𝓝 1) ∧
        Tendsto (fun x : ℝ => ansatzP f γ x (ω : ℂ)) atBot (𝓝 1)) :=
  no_vacuum_both_sides c hc γ hγ f hf hgain ω hω
