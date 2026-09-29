-- Prove2me | solution 1 for AutomorphicForm.RealIwasawa.exists_forall_norm_weightFourierIntegral_continuation_le_mul_pow_abs_im_mul_pow_of_re_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/977013b7-3ac3-5db1-895e-94498ec0e0ae

import Mathlib
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Complex.CauchyIntegral
import Theorems.Thm_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_RealIwasawa_exists_forall_norm_weightFourierIntegral_continuation_le_mul_pow_abs_im_mul_pow_of_re_mem_Icc

open Set MeasureTheory
open scoped Topology

set_option autoImplicit false

noncomputable section

namespace Ws31
namespace ArchR

def S (x : ℝ) : ℂ := ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)

def B (x : ℝ) : ℂ := ((1 + x ^ 2 : ℝ) : ℂ)

def u (x : ℝ) : ℂ := (((x : ℝ) : ℂ) - Complex.I) / S x

def E (t x : ℝ) : ℂ := Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I))

def cI (t : ℝ) : ℂ := ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I

def F (k : ℤ) (w : ℂ) (t x : ℝ) : ℂ := u x ^ k * B x ^ (-w) * E t x

def jj (k : ℤ) (w : ℂ) (t : ℝ) : ℂ := ∫ x : ℝ, F k w t x

theorem base (k : ℤ) :
    ContinuousOn (fun p : ℂ × ℝ => jj k p.1 p.2) ({w : ℂ | 1 / 2 < w.re} ×ˢ Set.univ) ∧
    (∀ t : ℝ, DifferentiableOn ℂ (fun w : ℂ => jj k w t) {w : ℂ | 1 / 2 < w.re}) ∧
    (∀ K : Set ℂ, IsCompact K → K ⊆ {w : ℂ | 1 / 2 < w.re} → ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ w ∈ K, ∀ t : ℝ, ‖jj k w t‖ ≤ C * (1 + |t|) ^ (-(N : ℝ))) :=
  AutomorphicForm.RealIwasawa.continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral k

theorem cI_ne_zero {t : ℝ} (ht : t ≠ 0) : cI t ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) ht))
    Complex.I_ne_zero

theorem norm_cI (t : ℝ) : ‖cI t‖ = 2 * Real.pi * |t| := by
  rw [cI, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]

theorem one_add_sq_pos (x : ℝ) : 0 < 1 + x ^ 2 := by positivity

theorem sqrt_pos' (x : ℝ) : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr (one_add_sq_pos x)

theorem S_ne_zero (x : ℝ) : S x ≠ 0 := Complex.ofReal_ne_zero.mpr (sqrt_pos' x).ne'

theorem B_ne_zero (x : ℝ) : B x ≠ 0 := Complex.ofReal_ne_zero.mpr (one_add_sq_pos x).ne'

theorem B_mem_slitPlane (x : ℝ) : B x ∈ Complex.slitPlane :=
  Complex.ofReal_mem_slitPlane.mpr (one_add_sq_pos x)

theorem sub_I_ne_zero (x : ℝ) : ((x : ℝ) : ℂ) - Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this

theorem u_ne_zero (x : ℝ) : u x ≠ 0 := div_ne_zero (sub_I_ne_zero x) (S_ne_zero x)

theorem S_sq (x : ℝ) : S x ^ 2 = B x := by
  rw [S, B, ← Complex.ofReal_pow, Real.sq_sqrt (one_add_sq_pos x).le]

theorem B_eq_mul (x : ℝ) : B x = (((x : ℝ) : ℂ) - Complex.I) * (((x : ℝ) : ℂ) + Complex.I) := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [B]
  push_cast
  linear_combination hI

theorem S_eq_cpow (x : ℝ) : S x = B x ^ ((1 / 2 : ℂ)) := by
  rw [S, B, Real.sqrt_eq_rpow, Complex.ofReal_cpow (one_add_sq_pos x).le]
  norm_num

theorem u_inv (x : ℝ) : (u x)⁻¹ = (((x : ℝ) : ℂ) + Complex.I) / S x := by
  rw [u, inv_div, div_eq_div_iff (sub_I_ne_zero x) (S_ne_zero x), ← sq, S_sq, B_eq_mul]
  ring

theorem u_add_inv (x : ℝ) : u x + (u x)⁻¹ = 2 * ((x : ℝ) : ℂ) / S x := by
  rw [u_inv, u, ← add_div]
  congr 1
  ring

theorem norm_sub_I (x : ℝ) : ‖((x : ℝ) : ℂ) - Complex.I‖ = Real.sqrt (1 + x ^ 2) := by
  have h : ((x : ℝ) : ℂ) - Complex.I = (x : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, ← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm, Complex.normSq_add_mul_I]
  congr 1; ring

theorem norm_u (x : ℝ) : ‖u x‖ = 1 := by
  rw [u, norm_div, norm_sub_I, S, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    div_self (sqrt_pos' x).ne']

theorem norm_B_cpow (w : ℂ) (x : ℝ) : ‖B x ^ (-w)‖ = (1 + x ^ 2) ^ (-w.re) := by
  rw [B, Complex.norm_cpow_eq_rpow_re_of_pos (one_add_sq_pos x), Complex.neg_re]

theorem norm_E (t x : ℝ) : ‖E t x‖ = 1 := by
  rw [E, ← neg_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]

theorem norm_F (k : ℤ) (w : ℂ) (t x : ℝ) : ‖F k w t x‖ = (1 + x ^ 2) ^ (-w.re) := by
  rw [F, norm_mul, norm_mul, norm_zpow, norm_u, one_zpow, norm_B_cpow, norm_E, one_mul, mul_one]

theorem norm_F_le (k : ℤ) {σ : ℝ} {w : ℂ} (hw : σ ≤ w.re) (t x : ℝ) : ‖F k w t x‖ ≤ (1 + x ^ 2) ^ (-σ) := by
  rw [norm_F]
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg x]) (neg_le_neg hw)

theorem integrable_dom {σ : ℝ} (hσ : 1 / 2 < σ) : Integrable (fun x : ℝ => (1 + x ^ 2) ^ (-σ)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * σ)
    (by rw [Module.finrank_self]; push_cast; linarith)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs, sq_abs]
  congr 1
  ring

theorem continuous_S : Continuous S :=
  Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (continuous_const.add (continuous_pow 2)))

theorem continuous_u : Continuous u := by
  unfold u
  exact (Complex.continuous_ofReal.sub continuous_const).div continuous_S (fun x => S_ne_zero x)

theorem continuous_B : Continuous B := by
  unfold B
  exact Complex.continuous_ofReal.comp (continuous_const.add (continuous_pow 2))

theorem continuous_E (t : ℝ) : Continuous (E t) := by
  unfold E
  fun_prop

theorem continuous_F_x (k : ℤ) (w : ℂ) (t : ℝ) : Continuous (fun x => F k w t x) := by
  unfold F
  refine ((continuous_u.zpow₀ k (fun x => Or.inl (u_ne_zero x))).mul ?_).mul (continuous_E t)
  exact continuous_B.cpow continuous_const (fun x => B_mem_slitPlane x)

theorem integrable_F (k : ℤ) {w : ℂ} (hw : 1 / 2 < w.re) (t : ℝ) : Integrable (fun x => F k w t x) :=
  (integrable_dom hw).mono' (continuous_F_x k w t).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => norm_F_le k le_rfl t x)

theorem tendsto_norm_F (k : ℤ) {w : ℂ} (hw : 0 < w.re) (t : ℝ) :
    Filter.Tendsto (fun x => F k w t x) Filter.atBot (𝓝 0) ∧
    Filter.Tendsto (fun x => F k w t x) Filter.atTop (𝓝 0) := by
  have hr := tendsto_rpow_neg_atTop hw
  have htop : Filter.Tendsto (fun x : ℝ => 1 + x ^ 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_left _ _ (Filter.tendsto_pow_atTop two_ne_zero)
  have hbot : Filter.Tendsto (fun x : ℝ => 1 + x ^ 2) Filter.atBot Filter.atTop := by
    have h := Filter.tendsto_atTop_add_const_left Filter.atBot (1 : ℝ)
      ((Filter.tendsto_pow_atTop two_ne_zero).comp Filter.tendsto_abs_atBot_atTop)
    refine h.congr' (Filter.Eventually.of_forall fun x => ?_)
    simp [sq_abs]
  constructor
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [norm_F]
    exact hr.comp hbot
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [norm_F]
    exact hr.comp htop

theorem hasDerivAt_one_add_sq (x : ℝ) : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
  have h := (hasDerivAt_pow 2 x).const_add 1
  simpa using h

theorem hasDerivAt_S (x : ℝ) : HasDerivAt S (((x : ℝ) : ℂ) / S x) x := by
  have h2 := ((hasDerivAt_one_add_sq x).sqrt (one_add_sq_pos x).ne').ofReal_comp
  show HasDerivAt (fun y : ℝ => ((Real.sqrt (1 + y ^ 2) : ℝ) : ℂ)) _ x
  convert h2 using 1
  rw [S]
  push_cast
  field_simp

theorem hasDerivAt_u (x : ℝ) : HasDerivAt u (Complex.I * u x / B x) x := by
  have h0 : HasDerivAt (fun y : ℝ => ((y : ℝ) : ℂ)) 1 x := by
    simpa using (hasDerivAt_id x).ofReal_comp
  have h := (h0.sub_const Complex.I).div (hasDerivAt_S x) (S_ne_zero x)
  show HasDerivAt (fun y : ℝ => (((y : ℝ) : ℂ) - Complex.I) / S y) _ x
  convert h using 1 <;> try with_reducible_and_instances rfl
  have hS := S_ne_zero x
  have hB := B_ne_zero x
  have hS2 : S x ^ 2 = (((x : ℝ) : ℂ) - Complex.I) * (((x : ℝ) : ℂ) + Complex.I) := (S_sq x).trans (B_eq_mul x)
  rw [u, ← S_sq]
  congr 1
  rw [eq_comm, sub_eq_iff_eq_add, one_mul, ← mul_div_assoc, ← mul_div_assoc, ← add_div, eq_div_iff hS]
  linear_combination hS2

theorem hasDerivAt_u_zpow (k : ℤ) (x : ℝ) :
    HasDerivAt (fun y => u y ^ k) ((k : ℂ) * Complex.I * u x ^ k / B x) x := by
  have h := (hasDerivAt_zpow k (u x) (Or.inl (u_ne_zero x))).comp x (hasDerivAt_u x)
  have e : (fun y => u y ^ k) = (fun z : ℂ => z ^ k) ∘ u := rfl
  rw [e]
  convert h using 1 <;> try with_reducible_and_instances rfl
  have huinv : (u x)⁻¹ * u x = 1 := inv_mul_cancel₀ (u_ne_zero x)
  rw [zpow_sub_one₀ (u_ne_zero x)]
  linear_combination (-((k : ℂ) * Complex.I * u x ^ k / B x)) * huinv

theorem hasDerivAt_B (x : ℝ) : HasDerivAt B (((2 * x : ℝ)) : ℂ) x :=
  (hasDerivAt_one_add_sq x).ofReal_comp

theorem hasDerivAt_B_cpow (w : ℂ) (x : ℝ) :
    HasDerivAt (fun y => B y ^ (-w)) (-w * B x ^ (-w - 1) * (((2 * x : ℝ)) : ℂ)) x := by
  have h := (Complex.hasStrictDerivAt_cpow_const (c := -w) (B_mem_slitPlane x)).hasDerivAt.comp x
    (hasDerivAt_B x)
  have e : (fun y => B y ^ (-w)) = (fun z : ℂ => z ^ (-w)) ∘ B := rfl
  rw [e]
  exact h

theorem hasDerivAt_E (t x : ℝ) : HasDerivAt (E t) (E t x * (-cI t)) x := by
  have h0 : HasDerivAt (fun y : ℝ => 2 * Real.pi * t * y) (2 * Real.pi * t) x := by
    simpa using (hasDerivAt_id x).const_mul (2 * Real.pi * t)
  have h1 : HasDerivAt (fun y : ℝ => -(((2 * Real.pi * t * y : ℝ) : ℂ) * Complex.I)) (-cI t) x :=
    (h0.ofReal_comp.mul_const Complex.I).neg
  exact h1.cexp

def G' (k : ℤ) (w : ℂ) (x : ℝ) : ℂ :=
  (k : ℂ) * Complex.I * u x ^ k / B x * B x ^ (-w) + u x ^ k * (-w * B x ^ (-w - 1) * (((2 * x : ℝ)) : ℂ))

theorem hasDerivAt_G (k : ℤ) (w : ℂ) (x : ℝ) :
    HasDerivAt (fun y => u y ^ k * B y ^ (-w)) (G' k w x) x :=
  (hasDerivAt_u_zpow k x).mul (hasDerivAt_B_cpow w x)

theorem G'_mul_E (k : ℤ) (w : ℂ) (t x : ℝ) :
    G' k w x * E t x
      = (k : ℂ) * Complex.I * F k (w + 1) t x - w * (F (k + 1) (w + 1 / 2) t x + F (k - 1) (w + 1 / 2) t x) := by
  have hB := B_ne_zero x
  have hS := S_ne_zero x
  have hu := u_ne_zero x
  have e1 : B x ^ (-w - 1) * B x = B x ^ (-w) := by
    have h := Complex.cpow_add (-w - 1) 1 hB
    rw [Complex.cpow_one, sub_add_cancel] at h
    exact h.symm
  have e2 : B x ^ (-(w + 1)) = B x ^ (-w - 1) := by congr 1; ring
  have e3 : B x ^ (-(w + 1 / 2)) = B x ^ (-w - 1) * S x := by
    rw [S_eq_cpow, ← Complex.cpow_add _ _ hB]; congr 1; ring
  have e4 : u x ^ (k + 1) = u x ^ k * u x := zpow_add_one₀ hu k
  have e5 : u x ^ (k - 1) = u x ^ k * (u x)⁻¹ := zpow_sub_one₀ hu k
  have e7 : (((2 * x : ℝ)) : ℂ) = 2 * ((x : ℝ) : ℂ) := by push_cast; ring
  have e8 : u x * S x + (u x)⁻¹ * S x = 2 * ((x : ℝ) : ℂ) := by
    rw [← add_mul, u_add_inv, div_mul_cancel₀ _ hS]
  have hBinv : B x * (B x)⁻¹ = 1 := mul_inv_cancel₀ hB
  simp only [F, G']
  rw [e2, e3, e4, e5, ← e1, e7]
  linear_combination ((k : ℂ) * Complex.I * u x ^ k * B x ^ (-w - 1) * E t x) * hBinv
    + (w * u x ^ k * B x ^ (-w - 1) * E t x) * e8

theorem recur (k : ℤ) {w : ℂ} (hw : 1 / 2 < w.re) (t : ℝ) :
    cI t * jj k w t = (k : ℂ) * Complex.I * jj k (w + 1) t
      - w * (jj (k + 1) (w + 1 / 2) t + jj (k - 1) (w + 1 / 2) t) := by
  have hw1 : 1 / 2 < (w + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hw2 : 1 / 2 < (w + 1 / 2).re := by
    have h : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
    simp only [Complex.add_re, h]; linarith
  have hGE' : Integrable ((fun y => u y ^ k * B y ^ (-w)) * fun y => E t y * (-cI t)) := by
    have e : ((fun y => u y ^ k * B y ^ (-w)) * fun y => E t y * (-cI t)) = fun y => F k w t y * (-cI t) := by
      funext y; simp only [Pi.mul_apply, F]; ring
    rw [e]
    exact (integrable_F k hw t).mul_const _
  have hG'E : Integrable ((fun y => G' k w y) * E t) := by
    have e : ((fun y => G' k w y) * E t) = fun y => (k : ℂ) * Complex.I * F k (w + 1) t y
        - w * (F (k + 1) (w + 1 / 2) t y + F (k - 1) (w + 1 / 2) t y) := by
      funext y; simp only [Pi.mul_apply]; exact G'_mul_E k w t y
    rw [e]
    exact ((integrable_F k hw1 t).const_mul _).sub
      (((integrable_F (k + 1) hw2 t).add (integrable_F (k - 1) hw2 t)).const_mul _)
  have hlim := tendsto_norm_F k (by linarith : 0 < w.re) t
  have elim : ((fun y => u y ^ k * B y ^ (-w)) * E t) = fun y => F k w t y := by
    funext y; simp only [Pi.mul_apply, F]
  have ibp := integral_mul_deriv_eq_deriv_mul (u := fun y => u y ^ k * B y ^ (-w)) (v := E t)
    (u' := fun y => G' k w y) (v' := fun y => E t y * (-cI t))
    (fun y _ => hasDerivAt_G k w y) (fun y _ => hasDerivAt_E t y) hGE' hG'E
    (by rw [elim]; exact hlim.1) (by rw [elim]; exact hlim.2)
  have lhs : (∫ y : ℝ, u y ^ k * B y ^ (-w) * (E t y * (-cI t))) = -cI t * jj k w t := by
    rw [jj, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [F]; ring
  have rhs : (∫ y : ℝ, G' k w y * E t y) = (k : ℂ) * Complex.I * jj k (w + 1) t
      - w * (jj (k + 1) (w + 1 / 2) t + jj (k - 1) (w + 1 / 2) t) := by
    simp_rw [G'_mul_E]
    have i1 : Integrable (fun y => (k : ℂ) * Complex.I * F k (w + 1) t y) := (integrable_F k hw1 t).const_mul _
    have i23 : Integrable (fun y => F (k + 1) (w + 1 / 2) t y + F (k - 1) (w + 1 / 2) t y) :=
      (integrable_F (k + 1) hw2 t).add (integrable_F (k - 1) hw2 t)
    have i2 : Integrable (fun y => w * (F (k + 1) (w + 1 / 2) t y + F (k - 1) (w + 1 / 2) t y)) :=
      i23.const_mul _
    rw [integral_sub i1 i2, integral_const_mul, integral_const_mul,
      integral_add (integrable_F (k + 1) hw2 t) (integrable_F (k - 1) hw2 t)]
    rfl
  beta_reduce at ibp
  rw [lhs, rhs, sub_zero] at ibp
  linear_combination (-1 : ℂ) * ibp

def H (n : ℕ) : Set ℂ := {w : ℂ | 1 / 2 - (n : ℝ) / 2 < w.re}

theorem isOpen_H (n : ℕ) : IsOpen (H n) := isOpen_lt continuous_const Complex.continuous_re

theorem H_zero : H 0 = {w : ℂ | 1 / 2 < w.re} := by
  ext w; simp [H]

theorem add_one_mem_H {n : ℕ} {w : ℂ} (hw : w ∈ H (n + 1)) : w + 1 ∈ H n := by
  simp only [H, mem_setOf_eq, Complex.add_re, Complex.one_re] at hw ⊢
  push_cast at hw
  linarith

theorem add_half_mem_H {n : ℕ} {w : ℂ} (hw : w ∈ H (n + 1)) : w + 1 / 2 ∈ H n := by
  simp only [H, mem_setOf_eq, Complex.add_re] at hw ⊢
  have h : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
  rw [h]
  push_cast at hw
  linarith

theorem H_mono {m n : ℕ} (h : m ≤ n) : H m ⊆ H n := by
  intro w hw
  simp only [H, mem_setOf_eq] at hw ⊢
  have : (m : ℝ) ≤ n := by exact_mod_cast h
  linarith

def J : ℕ → ℤ → ℂ → ℝ → ℂ
  | 0, k, w, t => jj k w t
  | n + 1, k, w, t => (cI t)⁻¹ * ((k : ℂ) * Complex.I * J n k (w + 1) t
      - w * (J n (k + 1) (w + 1 / 2) t + J n (k - 1) (w + 1 / 2) t))

theorem J_zero (k : ℤ) (w : ℂ) (t : ℝ) : J 0 k w t = jj k w t := rfl

theorem J_succ (n : ℕ) (k : ℤ) (w : ℂ) (t : ℝ) :
    J (n + 1) k w t = (cI t)⁻¹ * ((k : ℂ) * Complex.I * J n k (w + 1) t
      - w * (J n (k + 1) (w + 1 / 2) t + J n (k - 1) (w + 1 / 2) t)) := rfl

theorem J_succ_eq (n : ℕ) : ∀ (k : ℤ) (w : ℂ) (t : ℝ), w ∈ H n → t ≠ 0 →
    J (n + 1) k w t = J n k w t := by
  induction n with
  | zero =>
    intro k w t hw ht
    have hw' : 1 / 2 < w.re := by rw [H_zero] at hw; exact hw
    rw [J_succ, J_zero, J_zero, J_zero, J_zero, ← recur k hw' t, ← mul_assoc,
      inv_mul_cancel₀ (cI_ne_zero ht), one_mul]
  | succ n ih =>
    intro k w t hw ht
    rw [J_succ (n + 1) k w t, ih k (w + 1) t (add_one_mem_H hw) ht,
      ih (k + 1) (w + 1 / 2) t (add_half_mem_H hw) ht, ih (k - 1) (w + 1 / 2) t (add_half_mem_H hw) ht]
    exact (J_succ n k w t).symm

theorem J_eq_of_le {m n : ℕ} (h : m ≤ n) (k : ℤ) (w : ℂ) (t : ℝ) (hw : w ∈ H m) (ht : t ≠ 0) :
    J n k w t = J m k w t := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [show m + (d + 1) = (m + d) + 1 from by ring, J_succ_eq (m + d) k w t (H_mono (Nat.le_add_right m d) hw) ht]
    exact ih (Nat.le_add_right m d)

theorem J_differentiableOn (n : ℕ) : ∀ (k : ℤ) (t : ℝ), t ≠ 0 →
    DifferentiableOn ℂ (fun w => J n k w t) (H n) := by
  induction n with
  | zero => intro k t _; rw [H_zero]; exact (base k).2.1 t
  | succ n ih =>
    intro k t ht
    have h1 : DifferentiableOn ℂ (fun w => J n k (w + 1) t) (H (n + 1)) :=
      (ih k t ht).comp ((differentiable_id.add_const (1 : ℂ)).differentiableOn) (fun w hw => add_one_mem_H hw)
    have h2 : DifferentiableOn ℂ (fun w => J n (k + 1) (w + 1 / 2) t) (H (n + 1)) :=
      (ih (k + 1) t ht).comp ((differentiable_id.add_const (1 / 2 : ℂ)).differentiableOn)
        (fun w hw => add_half_mem_H hw)
    have h3 : DifferentiableOn ℂ (fun w => J n (k - 1) (w + 1 / 2) t) (H (n + 1)) :=
      (ih (k - 1) t ht).comp ((differentiable_id.add_const (1 / 2 : ℂ)).differentiableOn)
        (fun w hw => add_half_mem_H hw)
    show DifferentiableOn ℂ (fun w => (cI t)⁻¹ * ((k : ℂ) * Complex.I * J n k (w + 1) t
      - w * (J n (k + 1) (w + 1 / 2) t + J n (k - 1) (w + 1 / 2) t))) (H (n + 1))
    exact ((h1.const_mul _).sub (differentiableOn_id.mul (h2.add h3))).const_mul _

theorem J_continuousOn (n : ℕ) : ∀ k : ℤ,
    ContinuousOn (fun p : ℂ × ℝ => J n k p.1 p.2) (H n ×ˢ {t : ℝ | t ≠ 0}) := by
  induction n with
  | zero =>
    intro k; rw [H_zero]
    exact (base k).1.mono (Set.prod_mono le_rfl (Set.subset_univ _))
  | succ n ih =>
    intro k
    have m1 : MapsTo (fun p : ℂ × ℝ => (p.1 + 1, p.2)) (H (n + 1) ×ˢ {t : ℝ | t ≠ 0}) (H n ×ˢ {t : ℝ | t ≠ 0}) :=
      fun p hp => ⟨add_one_mem_H hp.1, hp.2⟩
    have m2 : MapsTo (fun p : ℂ × ℝ => (p.1 + 1 / 2, p.2)) (H (n + 1) ×ˢ {t : ℝ | t ≠ 0}) (H n ×ˢ {t : ℝ | t ≠ 0}) :=
      fun p hp => ⟨add_half_mem_H hp.1, hp.2⟩
    have c1 : Continuous (fun p : ℂ × ℝ => (p.1 + 1, p.2)) := by fun_prop
    have c2 : Continuous (fun p : ℂ × ℝ => (p.1 + 1 / 2, p.2)) := by fun_prop
    have h1 : ContinuousOn (fun p : ℂ × ℝ => J n k (p.1 + 1) p.2) (H (n + 1) ×ˢ {t : ℝ | t ≠ 0}) :=
      (ih k).comp c1.continuousOn m1
    have h2 : ContinuousOn (fun p : ℂ × ℝ => J n (k + 1) (p.1 + 1 / 2) p.2) (H (n + 1) ×ˢ {t : ℝ | t ≠ 0}) :=
      (ih (k + 1)).comp c2.continuousOn m2
    have h3 : ContinuousOn (fun p : ℂ × ℝ => J n (k - 1) (p.1 + 1 / 2) p.2) (H (n + 1) ×ˢ {t : ℝ | t ≠ 0}) :=
      (ih (k - 1)).comp c2.continuousOn m2
    have hcI : Continuous (fun p : ℂ × ℝ => cI p.2) := by unfold cI; fun_prop
    have hc : ContinuousOn (fun p : ℂ × ℝ => (cI p.2)⁻¹) (H (n + 1) ×ˢ {t : ℝ | t ≠ 0}) :=
      hcI.continuousOn.inv₀ (fun p hp => cI_ne_zero hp.2)
    show ContinuousOn (fun p : ℂ × ℝ => (cI p.2)⁻¹ * ((k : ℂ) * Complex.I * J n k (p.1 + 1) p.2
      - p.1 * (J n (k + 1) (p.1 + 1 / 2) p.2 + J n (k - 1) (p.1 + 1 / 2) p.2))) (H (n + 1) ×ˢ {t : ℝ | t ≠ 0})
    exact hc.mul ((continuousOn_const.mul h1).sub (continuous_fst.continuousOn.mul (h2.add h3)))

theorem norm_inv_cI_le {t : ℝ} (ht : t ≠ 0) : ‖(cI t)⁻¹‖ ≤ max 1 |t|⁻¹ := by
  rw [norm_inv, norm_cI]
  refine le_trans ?_ (le_max_right _ _)
  have ht' : 0 < |t| := abs_pos.mpr ht
  rw [inv_le_inv₀ (by positivity) ht']
  have : (1 : ℝ) ≤ 2 * Real.pi := by have := Real.two_le_pi; linarith
  nlinarith

theorem J_bound (n : ℕ) : ∀ (k : ℤ) (K : Set ℂ), IsCompact K → K ⊆ H n → ∃ A : ℕ, ∀ N : ℕ,
    ∃ C : ℝ, 0 < C ∧ ∀ w ∈ K, ∀ t : ℝ, t ≠ 0 →
      ‖J n k w t‖ ≤ C * (max 1 |t|⁻¹) ^ A * (1 + |t|) ^ (-(N : ℝ)) := by
  induction n with
  | zero =>
    intro k K hK hKH
    refine ⟨0, fun N => ?_⟩
    obtain ⟨C, hC, hb⟩ := (base k).2.2 K hK (by rw [H_zero] at hKH; exact hKH) N
    exact ⟨C, hC, fun w hw t _ => by rw [pow_zero, mul_one, J_zero]; exact hb w hw t⟩
  | succ n ih =>
    intro k K hK hKH
    have hK1 : IsCompact ((fun w : ℂ => w + 1) '' K) := hK.image (by fun_prop)
    have hK1H : (fun w : ℂ => w + 1) '' K ⊆ H n := by
      rintro _ ⟨w, hw, rfl⟩; exact add_one_mem_H (hKH hw)
    have hK2 : IsCompact ((fun w : ℂ => w + 1 / 2) '' K) := hK.image (by fun_prop)
    have hK2H : (fun w : ℂ => w + 1 / 2) '' K ⊆ H n := by
      rintro _ ⟨w, hw, rfl⟩; exact add_half_mem_H (hKH hw)
    obtain ⟨A₁, hA₁⟩ := ih k _ hK1 hK1H
    obtain ⟨A₂, hA₂⟩ := ih (k + 1) _ hK2 hK2H
    obtain ⟨A₃, hA₃⟩ := ih (k - 1) _ hK2 hK2H
    obtain ⟨R₀, hR₀⟩ := hK.isBounded.exists_norm_le
    set R : ℝ := max R₀ 0 with hRdef
    have hR0 : 0 ≤ R := le_max_right _ _
    have hR : ∀ w ∈ K, ‖w‖ ≤ R := fun w hw => (hR₀ w hw).trans (le_max_left _ _)
    set A : ℕ := A₁ + A₂ + A₃ with hAdef
    refine ⟨A + 1, fun N => ?_⟩
    obtain ⟨C₁, hC₁, hb₁⟩ := hA₁ N
    obtain ⟨C₂, hC₂, hb₂⟩ := hA₂ N
    obtain ⟨C₃, hC₃, hb₃⟩ := hA₃ N
    refine ⟨|(k : ℝ)| * C₁ + R * C₂ + R * C₃ + 1, by positivity, fun w hw t ht => ?_⟩
    set M : ℝ := max 1 |t|⁻¹ with hMdef
    set D : ℝ := (1 + |t|) ^ (-(N : ℝ)) with hDdef
    have hM : 1 ≤ M := le_max_left _ _
    have hD : 0 ≤ D := Real.rpow_nonneg (by positivity) _
    have hMA : 0 ≤ M ^ A * D := mul_nonneg (pow_nonneg (zero_le_one.trans hM) _) hD
    have e1 : ‖J n k (w + 1) t‖ ≤ C₁ * (M ^ A * D) := by
      refine (hb₁ (w + 1) ⟨w, hw, rfl⟩ t ht).trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hM (by rw [hAdef]; omega)) hD) hC₁.le
    have e2 : ‖J n (k + 1) (w + 1 / 2) t‖ ≤ C₂ * (M ^ A * D) := by
      refine (hb₂ (w + 1 / 2) ⟨w, hw, rfl⟩ t ht).trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hM (by rw [hAdef]; omega)) hD) hC₂.le
    have e3 : ‖J n (k - 1) (w + 1 / 2) t‖ ≤ C₃ * (M ^ A * D) := by
      refine (hb₃ (w + 1 / 2) ⟨w, hw, rfl⟩ t ht).trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hM (by rw [hAdef]; omega)) hD) hC₃.le
    have hk : ‖(k : ℂ) * Complex.I‖ = |(k : ℝ)| := by
      rw [norm_mul, Complex.norm_I, mul_one, ← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
    rw [J_succ, norm_mul]
    have step : ‖(k : ℂ) * Complex.I * J n k (w + 1) t
        - w * (J n (k + 1) (w + 1 / 2) t + J n (k - 1) (w + 1 / 2) t)‖
        ≤ (|(k : ℝ)| * C₁ + R * C₂ + R * C₃ + 1) * (M ^ A * D) := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, hk, norm_mul]
      have hw' := hR w hw
      have h23 : ‖J n (k + 1) (w + 1 / 2) t + J n (k - 1) (w + 1 / 2) t‖ ≤ (C₂ + C₃) * (M ^ A * D) :=
        (norm_add_le _ _).trans (by rw [add_mul]; exact add_le_add e2 e3)
      have hkC : |(k : ℝ)| * ‖J n k (w + 1) t‖ ≤ |(k : ℝ)| * (C₁ * (M ^ A * D)) :=
        mul_le_mul_of_nonneg_left e1 (abs_nonneg _)
      have hwC : ‖w‖ * ‖J n (k + 1) (w + 1 / 2) t + J n (k - 1) (w + 1 / 2) t‖ ≤ R * ((C₂ + C₃) * (M ^ A * D)) :=
        mul_le_mul hw' h23 (norm_nonneg _) hR0
      nlinarith
    calc ‖(cI t)⁻¹‖ * ‖(k : ℂ) * Complex.I * J n k (w + 1) t
          - w * (J n (k + 1) (w + 1 / 2) t + J n (k - 1) (w + 1 / 2) t)‖
        ≤ M * ((|(k : ℝ)| * C₁ + R * C₂ + R * C₃ + 1) * (M ^ A * D)) :=
          mul_le_mul (norm_inv_cI_le ht) step (norm_nonneg _) (zero_le_one.trans hM)
      _ = (|(k : ℝ)| * C₁ + R * C₂ + R * C₃ + 1) * M ^ (A + 1) * D := by rw [pow_succ]; ring

def nw (w : ℂ) : ℕ := ⌈1 - 2 * w.re⌉₊ + 1

theorem mem_H_nw (w : ℂ) : w ∈ H (nw w) := by
  simp only [H, nw, mem_setOf_eq]
  have := Nat.le_ceil (1 - 2 * w.re)
  push_cast
  linarith

def Jg (k : ℤ) (w : ℂ) (t : ℝ) : ℂ := J (nw w) k w t

theorem Jg_eq (k : ℤ) {n : ℕ} {w : ℂ} (hw : w ∈ H n) {t : ℝ} (ht : t ≠ 0) : Jg k w t = J n k w t := by
  have h1 := J_eq_of_le (le_max_left (nw w) n) k w t (mem_H_nw w) ht
  have h2 := J_eq_of_le (le_max_right (nw w) n) k w t hw ht
  unfold Jg
  exact h1.symm.trans h2

theorem clause_a (k : ℤ) (t : ℝ) (ht : t ≠ 0) : AnalyticOnNhd ℂ (fun w : ℂ => Jg k w t) Set.univ := by
  refine DifferentiableOn.analyticOnNhd (fun w₀ _ => ?_) isOpen_univ
  apply DifferentiableAt.differentiableWithinAt
  have hmem : H (nw w₀) ∈ 𝓝 w₀ := (isOpen_H _).mem_nhds (mem_H_nw w₀)
  have hd : DifferentiableAt ℂ (fun w => J (nw w₀) k w t) w₀ :=
    (J_differentiableOn _ k t ht).differentiableAt hmem
  refine hd.congr_of_eventuallyEq ?_
  exact Filter.eventually_of_mem hmem (fun w hw => Jg_eq k hw ht)

theorem clause_b (k : ℤ) (w : ℂ) (t : ℝ) (hw : 1 / 2 < w.re) (ht : t ≠ 0) : Jg k w t = jj k w t := by
  have hw0 : w ∈ H 0 := by rw [H_zero]; exact hw
  rw [Jg_eq k hw0 ht, J_zero]

theorem clause_c (k : ℤ) :
    ContinuousOn (fun p : ℂ × ℝ => Jg k p.1 p.2) (Set.univ ×ˢ {t : ℝ | t ≠ 0}) := by
  intro p hp
  have ht : p.2 ≠ 0 := hp.2
  have hO : IsOpen (H (nw p.1) ×ˢ {t : ℝ | t ≠ 0}) := (isOpen_H _).prod isOpen_ne
  have hmem : H (nw p.1) ×ˢ {t : ℝ | t ≠ 0} ∈ 𝓝 p := hO.mem_nhds ⟨mem_H_nw _, ht⟩
  have hc : ContinuousAt (fun q : ℂ × ℝ => J (nw p.1) k q.1 q.2) p :=
    ((J_continuousOn _ k) p ⟨mem_H_nw _, ht⟩).continuousAt hmem
  refine (hc.congr_of_eventuallyEq ?_).continuousWithinAt
  exact Filter.eventually_of_mem hmem (fun q hq => Jg_eq k hq.1 hq.2)

theorem clause_d (k : ℤ) (K : Set ℂ) (hK : IsCompact K) :
    ∃ A : ℕ, ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ w ∈ K, ∀ t : ℝ, t ≠ 0 →
      ‖Jg k w t‖ ≤ C * (max 1 |t|⁻¹) ^ A * (1 + |t|) ^ (-(N : ℝ)) := by
  obtain ⟨m, hm⟩ := (hK.image Complex.continuous_re).bddBelow
  set n : ℕ := ⌈1 - 2 * m⌉₊ + 1 with hndef
  have hKH : K ⊆ H n := by
    intro w hw
    have h1 : m ≤ w.re := hm ⟨w, hw, rfl⟩
    simp only [H, hndef, mem_setOf_eq]
    have := Nat.le_ceil (1 - 2 * m)
    push_cast
    linarith
  obtain ⟨A, hA⟩ := J_bound n k K hK hKH
  refine ⟨A, fun N => ?_⟩
  obtain ⟨C, hC, hb⟩ := hA N
  exact ⟨C, hC, fun w hw t ht => by rw [Jg_eq k (hKH hw) ht]; exact hb w hw t ht⟩

theorem norm_inv_cI_le'' {t : ℝ} (ht : 1 ≤ |t|) : ‖(cI t)⁻¹‖ ≤ 2 * (1 + |t|)⁻¹ := by
  rw [norm_inv, norm_cI]
  have ht' : 0 < |t| := by linarith
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by have := Real.two_le_pi; linarith
  have h1 : (2 * Real.pi * |t|)⁻¹ ≤ |t|⁻¹ := by
    rw [inv_le_inv₀ (by positivity) ht']; nlinarith
  refine h1.trans ?_
  rw [inv_le_iff_one_le_mul₀ ht']
  have hpos : (0 : ℝ) < 1 + |t| := by positivity
  rw [show 2 * (1 + |t|)⁻¹ * |t| = (2 * |t|) / (1 + |t|) by ring, le_div_iff₀ hpos]
  linarith

theorem jj_norm_le (k : ℤ) {σ : ℝ} (hσ : 1 / 2 < σ) {w : ℂ} (hw : σ ≤ w.re) (t : ℝ) :
    ‖jj k w t‖ ≤ ∫ x : ℝ, (1 + x ^ 2) ^ (-σ) := by
  unfold jj
  refine (norm_integral_le_integral_norm _).trans ?_
  exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) (integrable_dom hσ)
    (Filter.Eventually.of_forall fun x => norm_F_le k hw t x)

theorem norm_le_of_strip {σ₁ σ₂ : ℝ} {w : ℂ} (hw1 : σ₁ ≤ w.re) (hw2 : w.re ≤ σ₂) :
    ‖w‖ ≤ (max |σ₁| |σ₂| + 1) * (1 + |w.im|) := by
  have h1 : ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
  have h2 : |w.re| ≤ max |σ₁| |σ₂| := by
    rw [abs_le]; constructor
    · have := neg_abs_le σ₁; have := le_max_left |σ₁| |σ₂|; linarith
    · have := le_abs_self σ₂; have := le_max_right |σ₁| |σ₂|; linarith
  have h3 : 0 ≤ max |σ₁| |σ₂| := le_trans (abs_nonneg _) (le_max_left _ _)
  nlinarith [abs_nonneg w.im]

theorem rpow_neg_succ (t : ℝ) (N : ℕ) :
    (1 + |t|) ^ (-((N + 1 : ℕ) : ℝ)) = (1 + |t|) ^ (-(N : ℝ)) * (1 + |t|)⁻¹ := by
  have h : (0 : ℝ) < 1 + |t| := by positivity
  rw [show (-((N + 1 : ℕ) : ℝ)) = -(N : ℝ) + (-1) by push_cast; ring, Real.rpow_add h, Real.rpow_neg_one]

theorem rpow_neg_nat_ge {t : ℝ} (ht : |t| < 1) (N : ℕ) : (2 : ℝ)⁻¹ ^ N ≤ (1 + |t|) ^ (-(N : ℝ)) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← inv_pow]
  exact pow_le_pow_left₀ (by norm_num) (by rw [inv_le_inv₀ (by norm_num) (by positivity)]; linarith [abs_nonneg t]) N

theorem strip_base (N : ℕ) : ∀ (k : ℤ) (σ₁ σ₂ : ℝ), 1 / 2 < σ₁ → ∃ C : ℝ, 0 < C ∧
    ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ → ∀ t : ℝ, t ≠ 0 →
      ‖jj k w t‖ ≤ C * (1 + |w.im|) ^ N * (1 + |t|) ^ (-(N : ℝ)) := by
  induction N with
  | zero =>
    intro k σ₁ σ₂ hσ₁
    have hI : 0 ≤ ∫ x : ℝ, (1 + x ^ 2) ^ (-σ₁) := integral_nonneg fun x => by positivity
    refine ⟨(∫ x : ℝ, (1 + x ^ 2) ^ (-σ₁)) + 1, by linarith, fun w hw1 _ t _ => ?_⟩
    rw [pow_zero, mul_one, Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one]
    exact (jj_norm_le k hσ₁ hw1 t).trans (by linarith)
  | succ N ih =>
    intro k σ₁ σ₂ hσ₁
    obtain ⟨C₁, hC₁, hb₁⟩ := ih k (σ₁ + 1) (σ₂ + 1) (by linarith)
    obtain ⟨C₂, hC₂, hb₂⟩ := ih (k + 1) (σ₁ + 1 / 2) (σ₂ + 1 / 2) (by linarith)
    obtain ⟨C₃, hC₃, hb₃⟩ := ih (k - 1) (σ₁ + 1 / 2) (σ₂ + 1 / 2) (by linarith)
    set R : ℝ := max |σ₁| |σ₂| + 1 with hR
    have hR0 : 0 ≤ R := by have : 0 ≤ max |σ₁| |σ₂| := le_trans (abs_nonneg _) (le_max_left _ _); linarith
    set I₀ : ℝ := ∫ x : ℝ, (1 + x ^ 2) ^ (-σ₁) with hI₀
    have hI₀0 : 0 ≤ I₀ := integral_nonneg fun x => by positivity
    refine ⟨2 * (|(k : ℝ)| * C₁ + R * (C₂ + C₃) + 1) + (I₀ + 1) * 2 ^ (N + 1), by positivity, fun w hw1 hw2 t ht => ?_⟩
    set P : ℝ := 1 + |w.im| with hP
    set D : ℝ := (1 + |t|) ^ (-(N : ℝ)) with hD
    have hP1 : 1 ≤ P := by rw [hP]; linarith [abs_nonneg w.im]
    have hD0 : 0 ≤ D := Real.rpow_nonneg (by positivity) _
    have hPD : 0 ≤ P ^ N * D := by positivity
    have hDs : (1 + |t|) ^ (-((N + 1 : ℕ) : ℝ)) = D * (1 + |t|)⁻¹ := rpow_neg_succ t N
    by_cases ht1 : 1 ≤ |t|
    ·
      have him1 : (w + 1).im = w.im := by simp
      have him2 : (w + 1 / 2).im = w.im := by simp
      have e1 : ‖jj k (w + 1) t‖ ≤ C₁ * (P ^ N * D) := by
        have := hb₁ (w + 1) (by simp; linarith) (by simp; linarith) t ht
        rw [him1] at this; rw [mul_assoc] at this; exact this
      have e2 : ‖jj (k + 1) (w + 1 / 2) t‖ ≤ C₂ * (P ^ N * D) := by
        have := hb₂ (w + 1 / 2) (by simp; linarith) (by simp; linarith) t ht
        rw [him2] at this; rw [mul_assoc] at this; exact this
      have e3 : ‖jj (k - 1) (w + 1 / 2) t‖ ≤ C₃ * (P ^ N * D) := by
        have := hb₃ (w + 1 / 2) (by simp; linarith) (by simp; linarith) t ht
        rw [him2] at this; rw [mul_assoc] at this; exact this
      have hw' : ‖w‖ ≤ R * P := norm_le_of_strip hw1 hw2
      have hrec := recur k (lt_of_lt_of_le hσ₁ hw1) t
      have hjj : jj k w t = (cI t)⁻¹ * ((k : ℂ) * Complex.I * jj k (w + 1) t
          - w * (jj (k + 1) (w + 1 / 2) t + jj (k - 1) (w + 1 / 2) t)) := by
        rw [← hrec, ← mul_assoc, inv_mul_cancel₀ (cI_ne_zero ht), one_mul]
      have hk : ‖(k : ℂ) * Complex.I‖ = |(k : ℝ)| := by
        rw [norm_mul, Complex.norm_I, mul_one, ← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
      have step : ‖(k : ℂ) * Complex.I * jj k (w + 1) t
          - w * (jj (k + 1) (w + 1 / 2) t + jj (k - 1) (w + 1 / 2) t)‖
          ≤ (|(k : ℝ)| * C₁ + R * (C₂ + C₃) + 1) * (P * (P ^ N * D)) := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, hk, norm_mul]
        have h23 : ‖jj (k + 1) (w + 1 / 2) t + jj (k - 1) (w + 1 / 2) t‖ ≤ (C₂ + C₃) * (P ^ N * D) :=
          (norm_add_le _ _).trans (by rw [add_mul]; exact add_le_add e2 e3)
        have hkC : |(k : ℝ)| * ‖jj k (w + 1) t‖ ≤ |(k : ℝ)| * (C₁ * (P ^ N * D)) :=
          mul_le_mul_of_nonneg_left e1 (abs_nonneg _)
        have hwC : ‖w‖ * ‖jj (k + 1) (w + 1 / 2) t + jj (k - 1) (w + 1 / 2) t‖ ≤ (R * P) * ((C₂ + C₃) * (P ^ N * D)) :=
          mul_le_mul hw' h23 (norm_nonneg _) (by positivity)
        nlinarith [mul_nonneg (abs_nonneg (k : ℝ)) (mul_nonneg hC₁.le hPD), hP1, hPD]
      rw [hjj, norm_mul, hDs]
      calc ‖(cI t)⁻¹‖ * ‖(k : ℂ) * Complex.I * jj k (w + 1) t
            - w * (jj (k + 1) (w + 1 / 2) t + jj (k - 1) (w + 1 / 2) t)‖
          ≤ (2 * (1 + |t|)⁻¹) * ((|(k : ℝ)| * C₁ + R * (C₂ + C₃) + 1) * (P * (P ^ N * D))) :=
            mul_le_mul (norm_inv_cI_le'' ht1) step (norm_nonneg _) (by positivity)
        _ = 2 * (|(k : ℝ)| * C₁ + R * (C₂ + C₃) + 1) * P ^ (N + 1) * (D * (1 + |t|)⁻¹) := by rw [pow_succ]; ring
        _ ≤ (2 * (|(k : ℝ)| * C₁ + R * (C₂ + C₃) + 1) + (I₀ + 1) * 2 ^ (N + 1)) * P ^ (N + 1) * (D * (1 + |t|)⁻¹) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            linarith [show (0:ℝ) ≤ (I₀ + 1) * 2 ^ (N + 1) by positivity]
    ·
      rw [not_le] at ht1
      have htriv : ‖jj k w t‖ ≤ I₀ := jj_norm_le k hσ₁ hw1 t
      have hlow : (2 : ℝ)⁻¹ ^ (N + 1) ≤ (1 + |t|) ^ (-((N + 1 : ℕ) : ℝ)) := rpow_neg_nat_ge ht1 (N + 1)
      have hPN : 1 ≤ P ^ (N + 1) := one_le_pow₀ hP1
      have h2 : (2 : ℝ) ^ (N + 1) * (2 : ℝ)⁻¹ ^ (N + 1) = 1 := by rw [← mul_pow]; norm_num
      calc ‖jj k w t‖ ≤ I₀ + 1 := by linarith
        _ = ((I₀ + 1) * 2 ^ (N + 1)) * 1 * (2 : ℝ)⁻¹ ^ (N + 1) := by rw [mul_one, mul_assoc, h2, mul_one]
        _ ≤ ((I₀ + 1) * 2 ^ (N + 1)) * P ^ (N + 1) * (1 + |t|) ^ (-((N + 1 : ℕ) : ℝ)) := by gcongr
        _ ≤ (2 * (|(k : ℝ)| * C₁ + R * (C₂ + C₃) + 1) + (I₀ + 1) * 2 ^ (N + 1)) * P ^ (N + 1) * (1 + |t|) ^ (-((N + 1 : ℕ) : ℝ)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            linarith [show (0:ℝ) ≤ 2 * (|(k : ℝ)| * C₁ + R * (C₂ + C₃) + 1) by positivity]

theorem strip_tower (n : ℕ) : ∀ (k : ℤ) (σ₁ σ₂ : ℝ), 1 / 2 - (n : ℝ) / 2 < σ₁ → ∀ N : ℕ, ∃ (A : ℕ) (C : ℝ), 0 < C ∧
    ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ → ∀ t : ℝ, t ≠ 0 →
      ‖J n k w t‖ ≤ C * (1 + |w.im|) ^ A * (max 1 |t|⁻¹) ^ n * (1 + |t|) ^ (-(N : ℝ)) := by
  induction n with
  | zero =>
    intro k σ₁ σ₂ hσ N
    obtain ⟨C, hC, hb⟩ := strip_base N k σ₁ σ₂ (by simpa using hσ)
    exact ⟨N, C, hC, fun w hw1 hw2 t ht => by rw [J_zero, pow_zero, mul_one]; exact hb w hw1 hw2 t ht⟩
  | succ n ih =>
    intro k σ₁ σ₂ hσ N
    have hσ' : 1 / 2 - (n : ℝ) / 2 < σ₁ + 1 / 2 := by push_cast at hσ; linarith
    have hσ'' : 1 / 2 - (n : ℝ) / 2 < σ₁ + 1 := by push_cast at hσ; linarith
    obtain ⟨A₁, C₁, hC₁, hb₁⟩ := ih k (σ₁ + 1) (σ₂ + 1) hσ'' N
    obtain ⟨A₂, C₂, hC₂, hb₂⟩ := ih (k + 1) (σ₁ + 1 / 2) (σ₂ + 1 / 2) hσ' N
    obtain ⟨A₃, C₃, hC₃, hb₃⟩ := ih (k - 1) (σ₁ + 1 / 2) (σ₂ + 1 / 2) hσ' N
    set R : ℝ := max |σ₁| |σ₂| + 1 with hR
    have hR0 : 0 ≤ R := by have : 0 ≤ max |σ₁| |σ₂| := le_trans (abs_nonneg _) (le_max_left _ _); linarith
    set A : ℕ := A₁ + A₂ + A₃ with hA
    refine ⟨A + 1, |(k : ℝ)| * C₁ + R * (C₂ + C₃) + 1, by positivity, fun w hw1 hw2 t ht => ?_⟩
    set P : ℝ := 1 + |w.im| with hP
    set M : ℝ := max 1 |t|⁻¹ with hM
    set D : ℝ := (1 + |t|) ^ (-(N : ℝ)) with hD
    have hP1 : 1 ≤ P := by rw [hP]; linarith [abs_nonneg w.im]
    have hM1 : 1 ≤ M := le_max_left _ _
    have hD0 : 0 ≤ D := Real.rpow_nonneg (by positivity) _
    have hX : 0 ≤ P ^ A * M ^ n * D := by positivity
    have him1 : (w + 1).im = w.im := by simp
    have him2 : (w + 1 / 2).im = w.im := by simp
    have e1 : ‖J n k (w + 1) t‖ ≤ C₁ * (P ^ A * M ^ n * D) := by
      have h := hb₁ (w + 1) (by simp; linarith) (by simp; linarith) t ht
      rw [him1] at h
      refine h.trans ?_
      rw [mul_assoc, mul_assoc, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hC₁.le
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hP1 (by rw [hA]; omega)) (by positivity)
    have e2 : ‖J n (k + 1) (w + 1 / 2) t‖ ≤ C₂ * (P ^ A * M ^ n * D) := by
      have h := hb₂ (w + 1 / 2) (by simp; linarith) (by simp; linarith) t ht
      rw [him2] at h
      refine h.trans ?_
      rw [mul_assoc, mul_assoc, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hC₂.le
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hP1 (by rw [hA]; omega)) (by positivity)
    have e3 : ‖J n (k - 1) (w + 1 / 2) t‖ ≤ C₃ * (P ^ A * M ^ n * D) := by
      have h := hb₃ (w + 1 / 2) (by simp; linarith) (by simp; linarith) t ht
      rw [him2] at h
      refine h.trans ?_
      rw [mul_assoc, mul_assoc, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hC₃.le
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hP1 (by rw [hA]; omega)) (by positivity)
    have hw' : ‖w‖ ≤ R * P := norm_le_of_strip hw1 hw2
    have hk : ‖(k : ℂ) * Complex.I‖ = |(k : ℝ)| := by
      rw [norm_mul, Complex.norm_I, mul_one, ← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
    rw [J_succ, norm_mul]
    have step : ‖(k : ℂ) * Complex.I * J n k (w + 1) t
        - w * (J n (k + 1) (w + 1 / 2) t + J n (k - 1) (w + 1 / 2) t)‖
        ≤ (|(k : ℝ)| * C₁ + R * (C₂ + C₃) + 1) * (P * (P ^ A * M ^ n * D)) := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, hk, norm_mul]
      have h23 : ‖J n (k + 1) (w + 1 / 2) t + J n (k - 1) (w + 1 / 2) t‖ ≤ (C₂ + C₃) * (P ^ A * M ^ n * D) :=
        (norm_add_le _ _).trans (by rw [add_mul]; exact add_le_add e2 e3)
      have hkC : |(k : ℝ)| * ‖J n k (w + 1) t‖ ≤ |(k : ℝ)| * (C₁ * (P ^ A * M ^ n * D)) :=
        mul_le_mul_of_nonneg_left e1 (abs_nonneg _)
      have hwC : ‖w‖ * ‖J n (k + 1) (w + 1 / 2) t + J n (k - 1) (w + 1 / 2) t‖ ≤ (R * P) * ((C₂ + C₃) * (P ^ A * M ^ n * D)) :=
        mul_le_mul hw' h23 (norm_nonneg _) (by positivity)
      nlinarith [mul_nonneg (abs_nonneg (k : ℝ)) (mul_nonneg hC₁.le hX), hP1, hX]
    calc ‖(cI t)⁻¹‖ * ‖(k : ℂ) * Complex.I * J n k (w + 1) t
          - w * (J n (k + 1) (w + 1 / 2) t + J n (k - 1) (w + 1 / 2) t)‖
        ≤ M * ((|(k : ℝ)| * C₁ + R * (C₂ + C₃) + 1) * (P * (P ^ A * M ^ n * D))) :=
          mul_le_mul (norm_inv_cI_le ht) step (norm_nonneg _) (le_trans zero_le_one hM1)
      _ = (|(k : ℝ)| * C₁ + R * (C₂ + C₃) + 1) * P ^ (A + 1) * M ^ (n + 1) * D := by rw [pow_succ, pow_succ]; ring

end Ws31.ArchR

theorem solution
    (k : ℤ) (σ₁ σ₂ : ℝ) :
    let j : ℂ → ℝ → ℂ := fun w t => ∫ x : ℝ, ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
          * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I))
    ∃ A₀ : ℕ, ∀ N : ℕ, ∃ (C : ℝ) (A : ℕ), 0 < C ∧
      ∀ (t : ℝ), t ≠ 0 → ∀ (J : ℂ → ℂ), Differentiable ℂ J → (∀ w : ℂ, 1 / 2 < w.re → J w = j w t) →
        ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ →
          ‖J w‖ ≤ C * (1 + |w.im|) ^ A * (max 1 |t|⁻¹) ^ A₀ * (1 + |t|) ^ (-(N : ℝ)) := by
  intro j
  have hj : j = fun w t => Ws31.ArchR.jj k w t := rfl
  set n : ℕ := ⌈1 - 2 * σ₁⌉₊ + 1 with hn
  have hσn : 1 / 2 - (n : ℝ) / 2 < σ₁ := by
    rw [hn]; have := Nat.le_ceil (1 - 2 * σ₁); push_cast; linarith
  refine ⟨n, fun N => ?_⟩
  obtain ⟨A, C, hC, hb⟩ := Ws31.ArchR.strip_tower n k σ₁ σ₂ hσn N
  refine ⟨C, A, hC, fun t ht Jf hJd hJeq w hw1 hw2 => ?_⟩
  have hwH : w ∈ Ws31.ArchR.H n := by
    show 1 / 2 - (n : ℝ) / 2 < w.re; exact lt_of_lt_of_le hσn hw1
  have hU : IsPreconnected (Ws31.ArchR.H n) := (convex_halfSpace_re_gt _).isPreconnected
  have h1H : (1 : ℂ) ∈ Ws31.ArchR.H n := by
    show 1 / 2 - (n : ℝ) / 2 < (1 : ℂ).re; simp; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hfan : AnalyticOnNhd ℂ Jf (Ws31.ArchR.H n) := (hJd.differentiableOn).analyticOnNhd (Ws31.ArchR.isOpen_H n)
  have hgan : AnalyticOnNhd ℂ (fun w => Ws31.ArchR.J n k w t) (Ws31.ArchR.H n) :=
    (Ws31.ArchR.J_differentiableOn n k t ht).analyticOnNhd (Ws31.ArchR.isOpen_H n)
  have heq : Jf =ᶠ[nhds (1 : ℂ)] (fun w => Ws31.ArchR.J n k w t) := by
    have hmem : {w : ℂ | 1 / 2 < w.re} ∈ nhds (1 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp; norm_num)
    refine Filter.eventually_of_mem hmem fun w hw => ?_
    have hw0 : w ∈ Ws31.ArchR.H 0 := by rw [Ws31.ArchR.H_zero]; exact hw
    rw [hJeq w hw, hj]
    show Ws31.ArchR.jj k w t = Ws31.ArchR.J n k w t
    rw [Ws31.ArchR.J_eq_of_le (Nat.zero_le n) k w t hw0 ht, Ws31.ArchR.J_zero]
  have key : Jf w = Ws31.ArchR.J n k w t := hfan.eqOn_of_preconnected_of_eventuallyEq hgan hU h1H heq hwH
  rw [key]
  exact hb w hw1 hw2 t ht

end
end S_AutomorphicForm_RealIwasawa_exists_forall_norm_weightFourierIntegral_continuation_le_mul_pow_abs_im_mul_pow_of_re_mem_Icc
end P2MW
export P2MW.S_AutomorphicForm_RealIwasawa_exists_forall_norm_weightFourierIntegral_continuation_le_mul_pow_abs_im_mul_pow_of_re_mem_Icc (solution)
