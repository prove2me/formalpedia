-- Prove2me | Definitions.Def_RHT1000_Support_20261118_S002
-- name    : RHT1000_Support_20261118_S002
-- status  : Definition
-- author  : @bueno_ricardo
-- created : 2026-11-18T16:55:55.915549+00:00
-- url     : https://prove2.me/theorems/d2dfacf0-fdae-4483-abc0-6a3a0f40799c
-- title:
--   Suporte completo para T1000 — bloco 7 de 10
-- statement:
--   Definições e lemas auxiliares completos para a prova finita T1000. Este bloco não afirma sozinho a conclusão T1000 nem RH. A divisão reduz o tempo de compilação sem substituir demonstrações por hipóteses.
-- source:
--   Código adaptado de Salvatore Mercuri e Bhavik Mehta, smmercuri/zeta, tag v1-1e8 (3dab648), com dependências e avisos de autoria preservados. Fonte histórica integral T1000: https://axle.axiommath.ai/check#r=d2dcb520-c50a-44dc-a527-de0f7a51b892 . Reorganização em módulos ordinários para compatibilidade com Prove2Me; atribuição da adaptação: projeto Desenvolvimento RH, Ricardo Marangoni Brandão Bueno.

import Definitions.Def_RHT1000_Support_20261118_B006
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
section CertificatePort95
section
open Complex
open scoped Real
namespace Zeta.RiemannSiegel
noncomputable def slantArg (x : ℂ) : ℝ := (exp ((π / 4 : ℝ) * I) * x).arg - π / 4
noncomputable def slantLog (x : ℂ) : ℂ := (Real.log ‖x‖ : ℂ) + (slantArg x : ℂ) * I
noncomputable def slantCpow (x s : ℂ) : ℂ :=
  exp (-((π / 4 : ℝ) * I * s)) * (exp ((π / 4 : ℝ) * I) * x) ^ s
theorem slantCpow_eq_exp_mul_slantLog {x : ℂ} (hx : x ≠ 0) (s : ℂ) :
    slantCpow x s = exp (s * slantLog x) := by
  rw [slantCpow, Complex.cpow_def_of_ne_zero (mul_ne_zero (exp_ne_zero _) hx), ← exp_add,
    Complex.log, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, slantLog, slantArg]
  congr 1
  push_cast
  ring
theorem slantLog_eq_log {x : ℂ} (hx : 0 < x.re) : slantLog x = Complex.log x := by
  have hpi := Real.pi_pos
  obtain ⟨h₁, h₂⟩ := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hx))
  rw [slantLog, slantArg, Complex.arg_exp_ofReal_mul_I_mul (fun h ↦ by simp [h] at hx)
    ⟨by linarith, by linarith⟩, add_sub_cancel_right, Complex.log]
theorem slantCpow_of_exp_pi_div_four_mul_I_mul_eq {x : ℂ} {ρ φ : ℝ} (hρ : 0 < ρ) (hφ₁ : -π < φ)
    (hφ₂ : φ ≤ π) (hx : exp ((π / 4 : ℝ) * I) * x = (ρ : ℂ) * exp ((φ : ℝ) * I)) (u : ℂ) :
    slantCpow x u = (ρ : ℂ) ^ u * exp ((φ - π / 4 : ℝ) * I * u) := by
  rw [slantCpow, hx, Complex.ofReal_mul_exp_mul_I_cpow hρ hφ₁ hφ₂ u, ← mul_assoc,
    mul_comm (exp (-(((π / 4 : ℝ) : ℂ) * I * u))) ((ρ : ℂ) ^ u), mul_assoc, ← exp_add]
  congr 2
  push_cast
  ring
theorem slantCpow_ofReal {r : ℝ} (hr : 0 < r) (s : ℂ) : slantCpow (r : ℂ) s = (r : ℂ) ^ s := by
  have hpi := Real.pi_pos
  rw [slantCpow_of_exp_pi_div_four_mul_I_mul_eq hr (φ := π / 4) (by linarith) (by linarith)
    (mul_comm _ _) s, sub_self, Complex.ofReal_zero, zero_mul, zero_mul, exp_zero, mul_one]
theorem slantCpow_ofReal_mul_exp_pi_div_four_mul_I {ρ : ℝ} (hρ : 0 < ρ) (u : ℂ) :
    slantCpow ((ρ : ℂ) * exp ((π / 4 : ℝ) * I)) u = (ρ : ℂ) ^ u * exp ((π / 4 : ℝ) * I * u) := by
  have hpi := Real.pi_pos
  have hrot : exp ((π / 4 : ℝ) * I) * ((ρ : ℂ) * exp ((π / 4 : ℝ) * I))
      = (ρ : ℂ) * exp ((π / 2 : ℝ) * I) := by
    rw [show ((π / 2 : ℝ) : ℂ) * I = (π : ℂ) / 2 * I by push_cast; ring, exp_pi_div_two_mul_I]
    linear_combination (ρ : ℂ) * Complex.exp_pi_div_four_mul_I_mul_self
  rw [slantCpow_of_exp_pi_div_four_mul_I_mul_eq hρ (by linarith) (by linarith) hrot u,
    show π / 2 - π / 4 = π / 4 by ring]
theorem slantCpow_neg_ofReal_mul_exp_pi_div_four_mul_I {ρ : ℝ} (hρ : 0 < ρ) (u : ℂ) :
    slantCpow (-((ρ : ℂ) * exp ((π / 4 : ℝ) * I))) u
      = (ρ : ℂ) ^ u * exp ((-(3 * π / 4) : ℝ) * I * u) := by
  have hpi := Real.pi_pos
  have hrot : exp ((π / 4 : ℝ) * I) * -((ρ : ℂ) * exp ((π / 4 : ℝ) * I))
      = (ρ : ℂ) * exp ((-(π / 2) : ℝ) * I) := by
    rw [show ((-(π / 2) : ℝ) : ℂ) * I = -((π : ℂ) / 2 * I) by push_cast; ring, exp_neg,
      exp_pi_div_two_mul_I, inv_I]
    linear_combination (-(ρ : ℂ)) * Complex.exp_pi_div_four_mul_I_mul_self
  rw [slantCpow_of_exp_pi_div_four_mul_I_mul_eq hρ (by linarith) (by linarith) hrot u,
    show -(π / 2) - π / 4 = -(3 * π / 4) by ring]
theorem differentiableAt_slantCpow (s : ℂ) {x : ℂ} (hx : exp ((π / 4 : ℝ) * I) * x ∈ slitPlane) :
    DifferentiableAt ℂ (fun y ↦ slantCpow y s) x :=
  (((by fun_prop : DifferentiableAt ℂ (fun y : ℂ ↦ exp ((π / 4 : ℝ) * I) * y) x).cpow
    (by fun_prop) hx).const_mul _)
theorem norm_slantCpow {x : ℂ} (hx : x ≠ 0) (s : ℂ) :
    ‖slantCpow x s‖ = ‖x‖ ^ s.re / Real.exp (slantArg x * s.im) := by
  have hre : (-(((π / 4 : ℝ) : ℂ) * I * s)).re = π / 4 * s.im := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [slantCpow, norm_mul, Complex.norm_cpow_of_ne_zero (mul_ne_zero (exp_ne_zero _) hx),
    norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_exp, hre, slantArg, sub_mul,
    Real.exp_sub]
  field_simp
theorem slantArg_line {a : ℝ} (ha : 0 < a) (w : ℝ) :
    slantArg (line a w) = Real.arctan ((a + 2 * w) / a) - π / 4 := by
  have hre : (exp ((π / 4 : ℝ) * I) * line a w).re = Real.sqrt 2 / 2 * a := by
    rw [exp_pi_div_four_mul_I_mul_line]; simp
  have him : (exp ((π / 4 : ℝ) * I) * line a w).im = Real.sqrt 2 / 2 * (a + 2 * w) := by
    rw [exp_pi_div_four_mul_I_mul_line]; simp
  rw [slantArg, Complex.arg_eq_arctan (by rw [hre]; positivity), hre, him,
    mul_div_mul_left _ _ (by positivity : Real.sqrt 2 / 2 ≠ 0)]
theorem abs_slantArg_line_lt {a : ℝ} (ha : 0 < a) (w : ℝ) : |slantArg (line a w)| < 3 * π / 4 := by
  rw [slantArg_line ha, abs_lt]
  exact ⟨by linarith [Real.neg_pi_div_two_lt_arctan ((a + 2 * w) / a)],
    by linarith [Real.arctan_lt_pi_div_two ((a + 2 * w) / a), Real.pi_pos]⟩
theorem slantArg_line_mul_im_le (s : ℂ) {a : ℝ} (ha : 0 < a) (w : ℝ) :
    slantArg (line a w) * s.im ≤ 3 * π * |s.im| / 4 := by
  refine (le_abs_self _).trans ?_
  rw [abs_mul]
  nlinarith [(abs_slantArg_line_lt ha w).le, abs_nonneg s.im, abs_nonneg (slantArg (line a w))]
theorem continuous_slantLog_line {a : ℝ} (ha0 : 0 < a) :
    Continuous fun w : ℝ ↦ slantLog (line a w) := by
  have hlog : Continuous fun w : ℝ ↦ Real.log ‖line a w‖ :=
    continuous_iff_continuousAt.2 fun w ↦
      (continuous_line a).norm.continuousAt.log (norm_ne_zero_iff.2 (line_ne_zero ha0.ne' w))
  simp only [slantLog, slantArg_line ha0]
  fun_prop
theorem norm_slantLog_line_le {a : ℝ} (ha0 : 0 < a) (w : ℝ) :
    ‖slantLog (line a w)‖ ≤ |Real.log (a / Real.sqrt 2)| + a + 3 * π / 4 + 2 * |w| := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]
  linarith [abs_log_norm_line_le ha0 w, (abs_slantArg_line_lt ha0 w).le]
end Zeta.RiemannSiegel
end
end CertificatePort95


section CertificatePort96
section
open Complex MeasureTheory
open scoped Real
namespace Complex
theorem norm_two_mul_I_mul (z : ℂ) : ‖2 * I * z‖ = 2 * ‖z‖ := by simp
theorem norm_one_add_I_mul_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : α → ℂ) : ‖(1 + I) * ∫ w, F w ∂μ‖ ≤ Real.sqrt 2 * ∫ w, ‖F w‖ ∂μ := by
  rw [norm_mul, norm_one_add_I]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (Real.sqrt_nonneg 2)
end Complex
namespace Zeta.RiemannSiegel
noncomputable def integrand (s x : ℂ) : ℂ :=
  slantCpow x (-s) * kernel x
noncomputable def contourIntegrand (s : ℂ) (a w : ℝ) : ℂ :=
  integrand s (line a w)
theorem norm_contourIntegrand (s : ℂ) (a w : ℝ) :
    ‖contourIntegrand s a w‖
      = ‖slantCpow (line a w) (-s) * exp (π * I * line a w ^ 2)‖ /
        (2 * ‖sin (π * line a w)‖) := by
  rw [contourIntegrand, integrand, kernel_eq_div_two_mul_I_mul_sin, ← mul_div_assoc, norm_div,
    norm_two_mul_I_mul]
theorem norm_contourIntegrand_eq_exp (s : ℂ) {a : ℝ} (ha0 : 0 < a) (w : ℝ) :
    ‖contourIntegrand s a w‖
      = Real.exp (Real.log ‖line a w‖ * (-s).re + slantArg (line a w) * s.im) *
        (Real.exp (-(2 * π * (a + w) * w)) / (2 * ‖sin (π * line a w)‖)) := by
  have hx0 : line a w ≠ 0 := line_ne_zero ha0.ne' w
  rw [norm_contourIntegrand, norm_mul, norm_slantCpow hx0, Complex.norm_exp_pi_mul_I_mul_sq,
    line_re, line_im, Real.rpow_def_of_pos (norm_pos_iff.2 hx0), Complex.neg_im, mul_neg,
    Real.exp_neg (slantArg (line a w) * s.im), div_inv_eq_mul,
    ← Real.exp_add (Real.log ‖line a w‖ * (-s).re) (slantArg (line a w) * s.im)]
  ring
theorem continuous_contourIntegrand (s : ℂ) {a : ℝ} (ha0 : 0 < a)
    (hsin : ∀ w : ℝ, sin (π * line a w) ≠ 0) : Continuous (contourIntegrand s a) := by
  have hline := continuous_line a
  have hrot : Continuous fun w : ℝ ↦ exp ((π / 4 : ℝ) * I) * line a w := continuous_const.mul hline
  have hpow : Continuous fun w : ℝ ↦ (exp ((π / 4 : ℝ) * I) * line a w) ^ (-s) :=
    hrot.cpow continuous_const fun w ↦ mem_slitPlane_iff.2 <| Or.inl <| by
      rw [re_exp_pi_div_four_mul_I_mul_line]
      exact div_pos ha0 (Real.sqrt_pos.2 two_pos)
  have hker : Continuous fun w : ℝ ↦ kernel (line a w) := by
    simp only [kernel_eq_div_two_mul_I_mul_sin]
    exact Continuous.div (by fun_prop) (by fun_prop) fun w ↦ by simpa [I_ne_zero] using hsin w
  unfold contourIntegrand integrand slantCpow
  exact (continuous_const.mul hpow).mul hker
theorem norm_contourIntegrand_le_exp {s : ℂ} {a c σ τ : ℝ} (ha0 : 0 < a) (hc : 0 < c)
    (hsin : ∀ w : ℝ, c ≤ ‖sin (π * line a w)‖) (hσ : |s.re| ≤ σ) (hτ : |s.im| ≤ τ) (w : ℝ) :
    ‖contourIntegrand s a w‖
      ≤ Real.exp (3 * π * τ / 4 + (|Real.log (a / Real.sqrt 2)| + a) * σ + 2 * σ ^ 2 / π +
          π * a ^ 2) / (2 * c) * Real.exp (-(π / 2) * w ^ 2) := by
  have hpi := Real.pi_pos
  set L : ℝ := |Real.log (a / Real.sqrt 2)|
  have hL0 : 0 ≤ L := abs_nonneg _
  have hσ0 : 0 ≤ σ := (abs_nonneg _).trans hσ
  have habs : |Real.log ‖line a w‖| ≤ L + a + 2 * |w| := abs_log_norm_line_le ha0 w
  have harg : slantArg (line a w) * s.im ≤ 3 * π * τ / 4 :=
    (slantArg_line_mul_im_le s ha0 w).trans (by gcongr)
  have hlog : Real.log ‖line a w‖ * (-s).re ≤ (L + a) * σ + 2 * σ ^ 2 / π + π / 2 * w ^ 2 := by
    have h1 : Real.log ‖line a w‖ * (-s).re ≤ |Real.log ‖line a w‖| * |s.re| := by
      simpa [abs_mul] using le_abs_self (Real.log ‖line a w‖ * (-s).re)
    have h2 : |Real.log ‖line a w‖| * |s.re| ≤ (L + a + 2 * |w|) * σ :=
      (mul_le_mul_of_nonneg_right habs (abs_nonneg _)).trans (by gcongr)
    have h3 : 2 * σ * |w| ≤ π / 2 * w ^ 2 + 2 * σ ^ 2 / π := by
      rw [← sq_abs w, ← sub_nonneg, show π / 2 * |w| ^ 2 + 2 * σ ^ 2 / π - 2 * σ * |w|
        = (π * |w| - 2 * σ) ^ 2 / (2 * π) by field_simp; ring]
      positivity
    nlinarith [h1, h2, h3]
  have hgauss : -(2 * π * (a + w) * w) ≤ π * a ^ 2 - π * w ^ 2 := by
    nlinarith [sq_nonneg (a + w)]
  rw [norm_contourIntegrand_eq_exp s ha0, ← mul_div_assoc, div_mul_eq_mul_div, ← Real.exp_add,
    ← Real.exp_add]
  gcongr Real.exp ?_ / ?_ <;> linarith [hsin w]
theorem integrable_contourIntegrand (s : ℂ) {a c : ℝ} (ha0 : 0 < a) (hc : 0 < c)
    (hsin : ∀ w : ℝ, c ≤ ‖sin (π * line a w)‖) : Integrable (contourIntegrand s a) := by
  have hsin0 : ∀ w : ℝ, sin (π * line a w) ≠ 0 := fun w ↦
    norm_pos_iff.1 (lt_of_lt_of_le hc (hsin w))
  exact Integrable.mono' ((integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < π / 2)).const_mul _)
    (continuous_contourIntegrand s ha0 hsin0).aestronglyMeasurable
    (.of_forall (norm_contourIntegrand_le_exp ha0 hc hsin le_rfl le_rfl))
theorem integrable_contourIntegrand_of_le_half (s : ℂ) {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2) :
    Integrable (contourIntegrand s a) :=
  integrable_contourIntegrand s ha0 (c := min (1 / 2) (a / Real.sqrt 2))
    (lt_min (by norm_num) (by positivity))
    fun w ↦ (min_le_min le_rfl (norm_line_ge a w)).trans (norm_sin_pi_mul_line_ge_min ha0.le ha w)
theorem norm_kernel_line_le {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2) (w : ℝ) :
    ‖kernel (line a w)‖
      ≤ Real.exp (π * a ^ 2) / (Real.sqrt 2 * a) * Real.exp (-(π * w ^ 2)) := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have h1 : (1 : ℝ) ≤ Real.sqrt 2 := (Real.le_sqrt' one_pos).2 (by norm_num)
  have hlow : a / Real.sqrt 2 ≤ ‖sin (π * line a w)‖ :=
    le_trans (le_min (by rw [div_le_iff₀ h2]; nlinarith) (norm_line_ge a w))
      (norm_sin_pi_mul_line_ge_min ha0.le ha w)
  rw [kernel_eq_div_two_mul_I_mul_sin, norm_div, Complex.norm_exp_pi_mul_I_mul_sq, line_re,
    line_im, Complex.norm_two_mul_I_mul,
    show Real.exp (π * a ^ 2) / (Real.sqrt 2 * a) * Real.exp (-(π * w ^ 2))
      = Real.exp (π * a ^ 2 + -(π * w ^ 2)) / (2 * (a / Real.sqrt 2)) by
      rw [Real.exp_add, show 2 * (a / Real.sqrt 2) = 2 / Real.sqrt 2 * a by ring, Real.div_sqrt]
      ring]
  gcongr
  nlinarith [sq_nonneg (a + w), Real.pi_pos]
noncomputable def slantIntegral (f : ℂ → ℂ) (a : ℝ) : ℂ :=
  (1 + I) * ∫ w : ℝ, f (line a w)
noncomputable def contourIntegral (s : ℂ) (a : ℝ) : ℂ :=
  (1 + I) * ∫ w : ℝ, contourIntegrand s a w
theorem contourIntegral_eq_slantIntegral (s : ℂ) (a : ℝ) :
    contourIntegral s a = slantIntegral (integrand s) a :=
  rfl
end Zeta.RiemannSiegel
end
end CertificatePort96


section CertificatePort97
section
open Complex MeasureTheory
open scoped Real
namespace Zeta.RiemannSiegel
noncomputable def modelFun (p x : ℂ) : ℂ :=
  exp (2 * π * I * (x - p) ^ 2) / (exp (π * I * x) - exp (-(π * I * x)))
noncomputable def modelIntegrand (p : ℂ) (a w : ℝ) : ℂ :=
  modelFun p (line a w)
noncomputable def modelIntegral (p : ℂ) (a : ℝ) : ℂ :=
  (1 + I) * ∫ w : ℝ, modelIntegrand p a w
theorem modelIntegral_eq_slantIntegral (p : ℂ) (a : ℝ) :
    modelIntegral p a = slantIntegral (modelFun p) a :=
  rfl
theorem modelFun_eq_div_two_mul_I_mul_sin (p x : ℂ) :
    modelFun p x = exp (2 * π * I * (x - p) ^ 2) / (2 * I * sin (π * x)) := by
  rw [modelFun, show ((π : ℂ) * I * x) = ((π : ℂ) * x) * I by ring, exp_mul_I_sub_exp_neg_mul_I]
theorem modelFun_eq_mul_kernel (p x : ℂ) :
    modelFun p x = exp (2 * π * I * (x - p) ^ 2 - π * I * x ^ 2) * kernel x := by
  rw [modelFun, kernel, ← mul_div_assoc, ← exp_add,
    show 2 * (π : ℂ) * I * (x - p) ^ 2 - π * I * x ^ 2 + π * I * x ^ 2
      = 2 * π * I * (x - p) ^ 2 by ring]
theorem modelFun_add_one (p x : ℂ) : modelFun p (x + 1) = -modelFun (p - 1) x := by
  have hden : exp ((π : ℂ) * I * (x + 1)) - exp (-((π : ℂ) * I * (x + 1)))
      = -(exp ((π : ℂ) * I * x) - exp (-((π : ℂ) * I * x))) := by
    rw [show ((π : ℂ) * I * (x + 1)) = π * I * x + π * I by ring, exp_add,
      show (-((π : ℂ) * I * x + π * I)) = -(π * I * x) + -(π * I) by ring, exp_add,
      exp_pi_mul_I, show exp (-((π : ℂ) * I)) = -1 by rw [exp_neg, exp_pi_mul_I]; norm_num]
    ring
  rw [modelFun, modelFun, hden, show (x + 1 - p) ^ 2 = (x - (p - 1)) ^ 2 by ring, div_neg]
theorem norm_modelFun_le (p : ℂ) {x : ℂ} {c : ℝ} (hc : 0 < c) (hx : c ≤ ‖sin (π * x)‖) :
    ‖modelFun p x‖ ≤ ‖exp (2 * π * I * (x - p) ^ 2)‖ / (2 * c) := by
  rw [modelFun_eq_div_two_mul_I_mul_sin, norm_div, Complex.norm_two_mul_I_mul]
  gcongr
theorem norm_modelIntegrand_le (p : ℂ) {a : ℝ} {n : ℤ} (ha : a = n + 1 / 2) (w : ℝ) :
    ‖modelIntegrand p a w‖ ≤ ‖exp (2 * π * I * (line a w - p) ^ 2)‖ / Real.sqrt 2 := by
  rw [modelIntegrand, show Real.sqrt 2 = 2 * (Real.sqrt 2 / 2) by ring]
  exact norm_modelFun_le p (by positivity) (norm_sin_pi_mul_line_ge ha w)
theorem continuous_modelIntegrand (p : ℂ) {a : ℝ} {n : ℤ} (ha : a = n + 1 / 2) :
    Continuous (modelIntegrand p a) := by
  have hline := continuous_line a
  have h : modelIntegrand p a
      = fun w : ℝ ↦ exp (2 * π * I * (line a w - p) ^ 2) / (2 * I * sin (π * line a w)) :=
    funext fun w ↦ modelFun_eq_div_two_mul_I_mul_sin p (line a w)
  rw [h]
  exact Continuous.div (by fun_prop) (by fun_prop) fun w ↦ by
    simpa [I_ne_zero] using sin_pi_mul_line_ne_zero ha w
theorem integrable_modelIntegrand (p : ℂ) {a : ℝ} {n : ℤ} (ha : a = n + 1 / 2) :
    Integrable (modelIntegrand p a) :=
  Integrable.mono' ((integrable_exp_two_pi_mul_I_mul_line_sub_sq a p).norm.div_const _)
    (continuous_modelIntegrand p ha).aestronglyMeasurable
    (.of_forall (norm_modelIntegrand_le p ha))
theorem norm_exp_two_pi_mul_I_mul_line_sub_sq (p w : ℝ) :
    ‖exp (2 * π * I * (line (1 / 2) w - (p : ℂ)) ^ 2)‖
      = Real.exp (π * (1 / 2 - p) ^ 2) * Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) := by
  rw [Complex.norm_exp_two_pi_mul_I_mul_sq, Complex.sub_re, Complex.sub_im, line_re, line_im,
    ofReal_re, ofReal_im,
    show -(4 * π * (1 / 2 + w - p) * (w - 0))
      = π * (1 / 2 - p) ^ 2 + -(4 * π) * (w + (1 / 2 - p) / 2) ^ 2 by ring, Real.exp_add]
theorem norm_exp_two_pi_mul_I_mul_line_sub_sq' (p w : ℝ) :
    ‖exp (2 * π * I * (line (1 / 2) w - (p : ℂ)) ^ 2)‖
      = Real.exp (2 * π * (1 / 2 - p) ^ 2) *
          Real.exp (-(2 * π) * ‖line (1 / 2) w - (p : ℂ)‖ ^ 2) := by
  rw [norm_exp_two_pi_mul_I_mul_line_sub_sq, norm_line_sub_ofReal_sq, ← Real.exp_add,
    ← Real.exp_add]
  congr 1
  ring
theorem norm_modelIntegral_le (p : ℝ) :
    ‖modelIntegral p (1 / 2)‖ ≤ Real.exp (π * (1 / 2 - p) ^ 2) / 2 := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hhalf : (1 / 2 : ℝ) = (0 : ℤ) + 1 / 2 := by norm_num
  have hgauss : ∫ w : ℝ, Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) = 1 / 2 := by
    rw [integral_add_right_eq_self (fun u : ℝ ↦ Real.exp (-(4 * π) * u ^ 2)) ((1 / 2 - p) / 2),
      integral_gaussian, show π / (4 * π) = (1 / 2 : ℝ) ^ 2 by
        rw [div_eq_iff (by positivity)]; ring, Real.sqrt_sq (by norm_num)]
  calc ‖modelIntegral (p : ℂ) (1 / 2)‖
      ≤ Real.sqrt 2 * ∫ w : ℝ, ‖modelIntegrand (p : ℂ) (1 / 2) w‖ :=
        norm_one_add_I_mul_integral_le _
    _ ≤ Real.sqrt 2 * ∫ w : ℝ,
          ‖exp (2 * π * I * (line (1 / 2) w - (p : ℂ)) ^ 2)‖ / Real.sqrt 2 :=
        mul_le_mul_of_nonneg_left (integral_mono (integrable_modelIntegrand _ hhalf).norm
          ((integrable_exp_two_pi_mul_I_mul_line_sub_sq (1 / 2) (p : ℂ)).norm.div_const _)
          (norm_modelIntegrand_le _ hhalf)) hs2.le
    _ = Real.exp (π * (1 / 2 - p) ^ 2) / 2 := by
        simp only [norm_exp_two_pi_mul_I_mul_line_sub_sq p, mul_div_right_comm]
        rw [integral_const_mul, hgauss]
        field_simp
theorem modelIntegral_add_half (p : ℂ) :
    modelIntegral (p + 1 / 2) (1 / 2)
      = I * exp (2 * π * I * p) * modelIntegral p (1 / 2)
        - I * exp ((π / 8 : ℝ) * I) * exp (π * I * p) / (Real.sqrt 2 : ℂ) := by
  have hhalf : (1 / 2 : ℝ) = (0 : ℤ) + 1 / 2 := by norm_num
  set C : ℂ := exp (-((π / 8 : ℝ) * I)) * exp (-((π : ℂ) * I * p)) with hC
  have hgpt (w : ℝ) : C * exp (2 * π * I * (line (1 / 2) w - (p + 1 / 4)) ^ 2)
      = exp (2 * π * I * (line (1 / 2) w - p) ^ 2) * exp (-((π : ℂ) * I * line (1 / 2) w)) := by
    rw [hC, ← exp_add, ← exp_add, ← exp_add]
    congr 1
    push_cast
    ring
  have hCval : ((1 + I) * ∫ w : ℝ, C * exp (2 * π * I * (line (1 / 2) w - (p + 1 / 4)) ^ 2))
      = C * ((1 + I) / 2) := by
    rw [integral_const_mul, mul_left_comm, integral_exp_two_pi_mul_I_mul_line_sub_sq]
  have hsplit (w : ℝ) : modelIntegrand (p + 1 / 2) (1 / 2) w
      = I * exp (2 * π * I * p) * (modelIntegrand p (1 / 2) w -
        C * exp (2 * π * I * (line (1 / 2) w - (p + 1 / 4)) ^ 2)) := by
    have hne : exp ((π : ℂ) * I * line (1 / 2) w) ≠ exp (-((π : ℂ) * I * line (1 / 2) w)) := by
      rw [← sub_ne_zero,
        show ((π : ℂ) * I * line (1 / 2) w) = ((π : ℂ) * line (1 / 2) w) * I by ring,
        exp_mul_I_sub_exp_neg_mul_I]
      simpa [I_ne_zero] using sin_pi_mul_line_ne_zero hhalf w
    have hquasi : exp (2 * (π : ℂ) * I * (line (1 / 2) w - (p + 1 / 2)) ^ 2)
        = exp ((π : ℂ) / 2 * I) * exp (2 * π * I * p) *
            exp (2 * π * I * (line (1 / 2) w - p) ^ 2) *
            exp (-(2 * π * I * line (1 / 2) w)) := by
      rw [← exp_add, ← exp_add, ← exp_add]
      congr 1
      ring
    rw [modelIntegrand, modelIntegrand, modelFun, modelFun, hquasi, exp_pi_div_two_mul_I,
      mul_div_assoc, exp_neg_two_pi_mul_I_div_sub_eq hne, hgpt w]
    ring
  have hMain : modelIntegral (p + 1 / 2) (1 / 2)
      = I * exp (2 * π * I * p) * (modelIntegral p (1 / 2) - C * ((1 + I) / 2)) := by
    rw [← hCval]
    simp only [modelIntegral, hsplit]
    rw [integral_const_mul, integral_sub (integrable_modelIntegrand p hhalf)
      ((integrable_exp_two_pi_mul_I_mul_line_sub_sq (1 / 2) (p + 1 / 4)).const_mul _)]
    ring
  have hexp : exp (2 * (π : ℂ) * I * p) * exp (-((π / 8 : ℝ) * I)) * exp (-((π : ℂ) * I * p)) *
      exp ((π / 4 : ℝ) * I) = exp ((π / 8 : ℝ) * I) * exp ((π : ℂ) * I * p) := by
    simp only [← exp_add]
    congr 1
    push_cast
    ring
  rw [hMain, mul_sub, hC, ← exp_pi_div_four_mul_I_div_sqrt_two]
  linear_combination (-I / (Real.sqrt 2 : ℂ)) * hexp
end Zeta.RiemannSiegel
end
end CertificatePort97


section CertificatePort98
section
open Complex MeasureTheory
open scoped Real
namespace Zeta.RiemannSiegel
noncomputable def modelMomentIntegrand (n : ℕ) (p : ℂ) (a w : ℝ) : ℂ :=
  (line a w - p) ^ n * modelIntegrand p a w
noncomputable def modelMoment (n : ℕ) (p : ℂ) (a : ℝ) : ℂ :=
  (1 + I) * ∫ w : ℝ, modelMomentIntegrand n p a w
theorem modelMoment_zero (p : ℂ) (a : ℝ) : modelMoment 0 p a = modelIntegral p a := by
  simp only [modelMoment, modelMomentIntegrand, modelIntegral, pow_zero, one_mul]
theorem continuous_modelMomentIntegrand (n : ℕ) (p : ℂ) {a : ℝ} {m : ℤ} (ha : a = m + 1 / 2) :
    Continuous (modelMomentIntegrand n p a) :=
  (((continuous_line a).sub continuous_const).pow n).mul (continuous_modelIntegrand p ha)
theorem norm_modelMomentIntegrand_le (n : ℕ) {p : ℂ} {a : ℝ} {m : ℤ} (ha : a = m + 1 / 2)
    {P : ℝ} (hP : ‖p‖ ≤ P) (w : ℝ) :
    ‖modelMomentIntegrand n p a w‖
      ≤ Real.exp (4 * π * P * (|a| + P)) / Real.sqrt 2 *
        ((|a| + P + Real.sqrt 2 * |w|) ^ n *
          Real.exp (-(4 * π) * w ^ 2 + 4 * π * (|a| + 2 * P) * |w|)) := by
  have hP0 : 0 ≤ P := (norm_nonneg p).trans hP
  have hre := abs_le.mp ((Complex.abs_re_le_norm p).trans hP)
  have him := abs_le.mp ((Complex.abs_im_le_norm p).trans hP)
  have h1 : ‖line a w - p‖ ≤ |a| + P + Real.sqrt 2 * |w| := by
    calc ‖line a w - p‖ ≤ ‖line a w‖ + ‖p‖ := norm_sub_le _ _
      _ ≤ |a| + Real.sqrt 2 * |w| + P := by gcongr; simpa using norm_line_sub_ofReal_le a w 0
      _ = |a| + P + Real.sqrt 2 * |w| := by ring
  have h2 : ‖exp (2 * π * I * (line a w - p) ^ 2)‖
      ≤ Real.exp (4 * π * P * (|a| + P)) *
        Real.exp (-(4 * π) * w ^ 2 + 4 * π * (|a| + 2 * P) * |w|) := by
    rw [Complex.norm_exp_two_pi_mul_I_mul_sq, ← Real.exp_add, Complex.sub_re, Complex.sub_im,
      line_re, line_im]
    refine Real.exp_le_exp.2 ?_
    have hw1 : -(w * (a - p.re - p.im)) ≤ (|a| + 2 * P) * |w| :=
      (neg_le_abs _).trans <| by
        rw [abs_mul, mul_comm (|a| + 2 * P) |w|]
        gcongr
        exact abs_le.2 ⟨by linarith [neg_abs_le a], by linarith [le_abs_self a]⟩
    have hw2 : p.im * (a - p.re) ≤ P * (|a| + P) :=
      (le_abs_self _).trans <| by
        rw [abs_mul]
        exact mul_le_mul ((Complex.abs_im_le_norm p).trans hP)
          (abs_le.2 ⟨by linarith [neg_abs_le a], by linarith [le_abs_self a]⟩) (abs_nonneg _) hP0
    have key : -((a + w - p.re) * (w - p.im))
        ≤ -w ^ 2 + (|a| + 2 * P) * |w| + P * (|a| + P) := by linarith
    linarith [mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 4 * π)]
  calc ‖modelMomentIntegrand n p a w‖ = ‖line a w - p‖ ^ n * ‖modelIntegrand p a w‖ := by
        rw [modelMomentIntegrand, norm_mul, norm_pow]
    _ ≤ (|a| + P + Real.sqrt 2 * |w|) ^ n *
          (Real.exp (4 * π * P * (|a| + P)) *
            Real.exp (-(4 * π) * w ^ 2 + 4 * π * (|a| + 2 * P) * |w|) / Real.sqrt 2) := by
        gcongr
        exact (norm_modelIntegrand_le p ha w).trans (by gcongr)
    _ = Real.exp (4 * π * P * (|a| + P)) / Real.sqrt 2 *
          ((|a| + P + Real.sqrt 2 * |w|) ^ n *
            Real.exp (-(4 * π) * w ^ 2 + 4 * π * (|a| + 2 * P) * |w|)) := by ring
theorem integrable_modelMomentIntegrand (n : ℕ) (p : ℂ) {a : ℝ} {m : ℤ} (ha : a = m + 1 / 2) :
    Integrable (modelMomentIntegrand n p a) := by
  have hmaj : Integrable fun w : ℝ ↦ Real.exp (4 * π * ‖p‖ * (|a| + ‖p‖)) / Real.sqrt 2 *
      ((|a| + ‖p‖ + Real.sqrt 2 * |w|) ^ n *
        Real.exp (-(4 * π) * w ^ 2 + 4 * π * (|a| + 2 * ‖p‖) * |w|)) :=
    (integrable_pow_add_mul_abs_mul_exp_neg_mul_sq_add_mul_abs (b := 4 * π) (by positivity)
      (by positivity) (Real.sqrt_nonneg 2) _ n).const_mul _
  exact hmaj.mono' (continuous_modelMomentIntegrand n p ha).aestronglyMeasurable
    (.of_forall fun w ↦ norm_modelMomentIntegrand_le n ha le_rfl w)
theorem hasDerivAt_modelMomentIntegrand (n : ℕ) (p : ℂ) {a : ℝ} {m : ℤ} (ha : a = m + 1 / 2)
    (w : ℝ) :
    HasDerivAt (fun q : ℂ ↦ modelMomentIntegrand n q a w)
      (-(n : ℂ) * modelMomentIntegrand (n - 1) p a w
        - 4 * π * I * modelMomentIntegrand (n + 1) p a w) p := by
  have hD : (2 : ℂ) * I * sin (π * line a w) ≠ 0 := by
    simpa [I_ne_zero] using sin_pi_mul_line_ne_zero ha w
  have hfun : ∀ (k : ℕ) (q : ℂ), modelMomentIntegrand k q a w
      = (line a w - q) ^ k * exp (2 * π * I * (line a w - q) ^ 2) /
          (2 * I * sin (π * line a w)) := fun k q ↦ by
    rw [modelMomentIntegrand, modelIntegrand, modelFun_eq_div_two_mul_I_mul_sin]
    ring
  have hg : HasDerivAt (fun q : ℂ ↦ line a w - q) (-1) p := by
    simpa using (hasDerivAt_id p).const_sub (line a w)
  have hpow : HasDerivAt (fun q : ℂ ↦ (line a w - q) ^ n)
      (-(n : ℂ) * (line a w - p) ^ (n - 1)) p := (hg.pow n).congr_deriv (by ring)
  have hquad : HasDerivAt (fun q : ℂ ↦ 2 * (π : ℂ) * I * (line a w - q) ^ 2)
      (-(4 * (π : ℂ) * I) * (line a w - p)) p :=
    ((hg.pow 2).const_mul (2 * (π : ℂ) * I)).congr_deriv (by push_cast; ring)
  simp only [hfun]
  refine ((hpow.mul hquad.cexp).div_const (2 * I * sin (π * line a w))).congr_deriv ?_
  field_simp
  ring
theorem hasDerivAt_modelMoment (n : ℕ) (p : ℂ) {a : ℝ} {m : ℤ} (ha : a = m + 1 / 2) :
    HasDerivAt (fun q : ℂ ↦ modelMoment n q a)
      (-(n : ℂ) * modelMoment (n - 1) p a - 4 * π * I * modelMoment (n + 1) p a) p := by
  obtain ⟨maj, hmajint, hmajle⟩ : ∃ maj : ℕ → ℝ → ℝ, (∀ k, Integrable (maj k)) ∧
      ∀ (k : ℕ) (q : ℂ), ‖q‖ ≤ ‖p‖ + 1 → ∀ w : ℝ, ‖modelMomentIntegrand k q a w‖ ≤ maj k w :=
    ⟨fun k w ↦ Real.exp (4 * π * (‖p‖ + 1) * (|a| + (‖p‖ + 1))) / Real.sqrt 2 *
        ((|a| + (‖p‖ + 1) + Real.sqrt 2 * |w|) ^ k *
          Real.exp (-(4 * π) * w ^ 2 + 4 * π * (|a| + 2 * (‖p‖ + 1)) * |w|)),
      fun k ↦ (integrable_pow_add_mul_abs_mul_exp_neg_mul_sq_add_mul_abs (b := 4 * π)
        (A := |a| + (‖p‖ + 1)) (β := Real.sqrt 2) (by positivity) (by positivity)
        (Real.sqrt_nonneg 2) _ k).const_mul _,
      fun k q hq w ↦ norm_modelMomentIntegrand_le k ha hq w⟩
  have hcoeff : ‖4 * (π : ℂ) * I‖ = 4 * π := by
    simp [abs_of_pos Real.pi_pos]
  have hbound : ∀ w : ℝ, ∀ q ∈ Metric.ball p 1,
      ‖-(n : ℂ) * modelMomentIntegrand (n - 1) q a w
        - 4 * π * I * modelMomentIntegrand (n + 1) q a w‖
        ≤ (n : ℝ) * maj (n - 1) w + 4 * π * maj (n + 1) w := by
    intro w q hq
    rw [Metric.mem_ball, dist_eq_norm] at hq
    have hqP : ‖q‖ ≤ ‖p‖ + 1 := by linarith [norm_le_insert' q p]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_neg, Complex.norm_natCast, norm_mul, hcoeff]
    gcongr <;> exact hmajle _ q hqP w
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := p)
    (F := fun (q : ℂ) (w : ℝ) ↦ modelMomentIntegrand n q a w)
    (F' := fun (q : ℂ) (w : ℝ) ↦ -(n : ℂ) * modelMomentIntegrand (n - 1) q a w
      - 4 * π * I * modelMomentIntegrand (n + 1) q a w)
    (bound := fun w ↦ (n : ℝ) * maj (n - 1) w + 4 * π * maj (n + 1) w)
    (s := Metric.ball p 1) (Metric.ball_mem_nhds p one_pos)
    (Filter.Eventually.of_forall fun q ↦
      (continuous_modelMomentIntegrand n q ha).aestronglyMeasurable)
    (integrable_modelMomentIntegrand n p ha)
    (((continuous_const.mul (continuous_modelMomentIntegrand (n - 1) p ha)).sub
      (continuous_const.mul (continuous_modelMomentIntegrand (n + 1) p ha))).aestronglyMeasurable)
    (Filter.Eventually.of_forall hbound)
    (((hmajint _).const_mul _).add ((hmajint _).const_mul _))
    (Filter.Eventually.of_forall fun w q _ ↦ hasDerivAt_modelMomentIntegrand n q ha w)
  have hsplit : ∫ w : ℝ, (-(n : ℂ) * modelMomentIntegrand (n - 1) p a w
      - 4 * π * I * modelMomentIntegrand (n + 1) p a w)
      = -(n : ℂ) * (∫ w : ℝ, modelMomentIntegrand (n - 1) p a w)
        - 4 * π * I * ∫ w : ℝ, modelMomentIntegrand (n + 1) p a w := by
    rw [integral_sub ((integrable_modelMomentIntegrand _ p ha).const_mul _)
      ((integrable_modelMomentIntegrand _ p ha).const_mul _), integral_const_mul,
      integral_const_mul]
  simp only [modelMoment]
  exact ((hkey.2.congr_deriv hsplit).const_mul (1 + I)).congr_deriv (by ring)
theorem differentiable_modelMoment (n : ℕ) {a : ℝ} {m : ℤ} (ha : a = m + 1 / 2) :
    Differentiable ℂ fun q : ℂ ↦ modelMoment n q a :=
  fun p ↦ (hasDerivAt_modelMoment n p ha).differentiableAt
theorem hasDerivAt_modelIntegral (p : ℂ) {a : ℝ} {m : ℤ} (ha : a = m + 1 / 2) :
    HasDerivAt (fun q : ℂ ↦ modelIntegral q a) (-(4 * π * I) * modelMoment 1 p a) p := by
  have h := hasDerivAt_modelMoment 0 p ha
  simp only [modelMoment_zero] at h
  exact h.congr_deriv (by push_cast; ring)
theorem iteratedDeriv_three_modelIntegral (p : ℂ) {a : ℝ} {m : ℤ} (ha : a = m + 1 / 2) :
    iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q a) p
      = 48 * π ^ 2 * modelMoment 1 p a + 64 * π ^ 3 * I * modelMoment 3 p a := by
  have e₁ : iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q a)
      = iteratedDeriv 2 fun q : ℂ ↦ -(4 * π * I) * modelMoment 1 q a :=
    iteratedDeriv_succ_of_hasDerivAt (fun q ↦ hasDerivAt_modelIntegral q ha) 2
  have e₂ : (iteratedDeriv 2 fun q : ℂ ↦ -(4 * π * I) * modelMoment 1 q a)
      = iteratedDeriv 1 fun q : ℂ ↦
          4 * π * I * modelIntegral q a - 16 * π ^ 2 * modelMoment 2 q a := by
    refine iteratedDeriv_succ_of_hasDerivAt (fun q ↦ ?_) 1
    refine ((hasDerivAt_modelMoment 1 q ha).const_mul (-(4 * (π : ℂ) * I))).congr_deriv ?_
    simp only [Nat.sub_self, modelMoment_zero]
    push_cast
    linear_combination (16 * (π : ℂ) ^ 2 * modelMoment 2 q a) * Complex.I_sq
  have e₃ : (iteratedDeriv 1 fun q : ℂ ↦
        4 * π * I * modelIntegral q a - 16 * π ^ 2 * modelMoment 2 q a)
      = iteratedDeriv 0 fun q : ℂ ↦
          48 * π ^ 2 * modelMoment 1 q a + 64 * π ^ 3 * I * modelMoment 3 q a := by
    refine iteratedDeriv_succ_of_hasDerivAt (fun q ↦ ?_) 0
    refine (((hasDerivAt_modelIntegral q ha).const_mul (4 * (π : ℂ) * I)).sub
      ((hasDerivAt_modelMoment 2 q ha).const_mul (16 * (π : ℂ) ^ 2))).congr_deriv ?_
    push_cast
    linear_combination (-(16 * (π : ℂ) ^ 2 * modelMoment 1 q a)) * Complex.I_sq
  rw [e₁, e₂, e₃, iteratedDeriv_zero]
theorem neg_half_modelMoment_one_sub_eq (p : ℂ) {a : ℝ} {m : ℤ} (ha : a = m + 1 / 2) :
    -(1 / 2) * modelMoment 1 p a - 2 * π * I / 3 * modelMoment 3 p a
      = -iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q a) p / (96 * π ^ 2) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [iteratedDeriv_three_modelIntegral p ha]
  field_simp
  ring
end Zeta.RiemannSiegel
end
end CertificatePort98


section CertificatePort99
section
open Complex
open scoped Real
namespace Zeta.RiemannSiegel
noncomputable def mainSumOfPhase (θ t : ℝ) (ν : ℕ) : ℝ :=
  2 * ∑ n ∈ Finset.Icc 1 ν, Real.cos (θ - t * Real.log n) / Real.sqrt n
noncomputable def correction (p : ℝ) : ℝ :=
  2 * (exp (-((π / 8 : ℝ) * I)) * modelIntegral (p : ℂ) (1 / 2)).re
noncomputable def correctionLinear (p : ℝ) : ℝ :=
  2 * (exp (-((π / 8 : ℝ) * I)) *
    (-(1 / 2) * modelMoment 1 (p : ℂ) (1 / 2) - 2 * π * I / 3 * modelMoment 3 (p : ℂ) (1 / 2))).re
end Zeta.RiemannSiegel
open Zeta.RiemannSiegel
noncomputable abbrev hardyZApproximantRS (t : ℝ) : ℝ :=
  mainSumOfPhase (riemannSiegelThetaApproximant 2 0 t) t ⌊Real.sqrt (t / (2 * π))⌋₊
    - (-1) ^ (⌊Real.sqrt (t / (2 * π))⌋₊ : ℕ) * (t / (2 * π)) ^ (-(1 / 4) : ℝ)
        * (correction (Real.sqrt (t / (2 * π)) - ⌊Real.sqrt (t / (2 * π))⌋₊)
          + correctionLinear (Real.sqrt (t / (2 * π)) - ⌊Real.sqrt (t / (2 * π))⌋₊)
              / Real.sqrt (t / (2 * π)))
noncomputable abbrev hardyZRemainderRS (t : ℝ) : ℝ := hardyZ t - hardyZApproximantRS t
noncomputable abbrev hardyZErrorBoundRS (t : ℝ) : ℝ :=
  25 / 4 * (t / (2 * π)) ^ (-(5 / 4) : ℝ) + 1 / 32 * (t / (2 * π)) ^ (-(15 / 4) : ℝ)
noncomputable abbrev hardyZApproximantRS₀ (t : ℝ) : ℝ :=
  mainSumOfPhase (riemannSiegelThetaApproximant 2 0 t) t ⌊Real.sqrt (t / (2 * π))⌋₊
    - (-1) ^ (⌊Real.sqrt (t / (2 * π))⌋₊ : ℕ) * (t / (2 * π)) ^ (-(1 / 4) : ℝ)
        * correction (Real.sqrt (t / (2 * π)) - ⌊Real.sqrt (t / (2 * π))⌋₊)
noncomputable abbrev hardyZRemainderRS₀ (t : ℝ) : ℝ := hardyZ t - hardyZApproximantRS₀ t
noncomputable abbrev hardyZErrorBoundRS₀ (t : ℝ) : ℝ :=
  hardyZErrorBoundRS t + 13 / 10 * (t / (2 * π)) ^ (-(3 / 4) : ℝ)
end
end CertificatePort99


section CertificatePort100
section
namespace Zeta.Certificates
structure ZIntervalEM extends NonemptyInterval ℝ where
  fstCutoff : ℕ
  sndCutoff : ℕ
  fstBernoulli : ℕ
  sndBernoulli : ℕ
abbrev ZIntervalRS := NonemptyInterval ℝ
noncomputable abbrev ZIntervalEM.fstVal (I : ZIntervalEM) : ℝ :=
  hardyZApproximantEM I.fstBernoulli I.fstCutoff I.fst
noncomputable abbrev ZIntervalEM.sndVal (I : ZIntervalEM) : ℝ :=
  hardyZApproximantEM I.sndBernoulli I.sndCutoff I.snd
noncomputable abbrev ZIntervalRS.fstVal (I : ZIntervalRS) : ℝ :=
  hardyZApproximantRS I.fst
noncomputable abbrev ZIntervalRS.sndVal (I : ZIntervalRS) : ℝ :=
  hardyZApproximantRS I.snd
noncomputable abbrev ZIntervalRS.fstVal₀ (I : ZIntervalRS) : ℝ :=
  hardyZApproximantRS₀ I.fst
noncomputable abbrev ZIntervalRS.sndVal₀ (I : ZIntervalRS) : ℝ :=
  hardyZApproximantRS₀ I.snd
structure ZIntervalEM.Certificate (I : ZIntervalEM) where
  fst_nonneg : 0 ≤ I.fst
  fstBernoulli_pos : 0 < I.fstBernoulli
  fstCutoff_pos : 0 < I.fstCutoff
  sndBernoulli_pos : 0 < I.sndBernoulli
  sndCutoff_pos : 0 < I.sndCutoff
  is_sign_change : I.fstVal * I.sndVal < 0
  fst_error : ‖I.fstVal‖ > hardyZErrorBoundEM I.fstBernoulli I.fstCutoff I.fst
  snd_error : ‖I.sndVal‖ > hardyZErrorBoundEM I.sndBernoulli I.sndCutoff I.snd
structure ZIntervalRS.Certificate (I : ZIntervalRS) where
  le_fst : 32 * Real.pi ≤ I.fst
  is_sign_change : I.fstVal * I.sndVal < 0
  fst_error : ‖I.fstVal‖ > hardyZErrorBoundRS I.fst
  snd_error : ‖I.sndVal‖ > hardyZErrorBoundRS I.snd
namespace ZIntervalRS.Certificate
variable {I : ZIntervalRS}
theorem le_snd (h : I.Certificate) : 32 * Real.pi ≤ I.snd := h.le_fst.trans I.fst_le_snd
theorem fst_nonneg (h : I.Certificate) : 0 ≤ I.fst :=
  le_trans (by positivity) h.le_fst
theorem sixteen_le_fst_div (h : I.Certificate) : 16 ≤ I.fst / (2 * Real.pi) := by
  rw [le_div_iff₀ (by positivity)]
  linarith [h.le_fst]
theorem sixteen_le_snd_div (h : I.Certificate) : 16 ≤ I.snd / (2 * Real.pi) := by
  rw [le_div_iff₀ (by positivity)]
  linarith [h.le_snd]
end ZIntervalRS.Certificate
structure ZIntervalRS.Certificate₀ (I : ZIntervalRS) where
  le_fst : 32 * Real.pi ≤ I.fst
  is_sign_change : I.fstVal₀ * I.sndVal₀ < 0
  fst_error : ‖I.fstVal₀‖ > hardyZErrorBoundRS₀ I.fst
  snd_error : ‖I.sndVal₀‖ > hardyZErrorBoundRS₀ I.snd
namespace ZIntervalRS.Certificate₀
variable {I : ZIntervalRS}
theorem le_snd (h : I.Certificate₀) : 32 * Real.pi ≤ I.snd := h.le_fst.trans I.fst_le_snd
theorem fst_nonneg (h : I.Certificate₀) : 0 ≤ I.fst :=
  le_trans (by positivity) h.le_fst
end ZIntervalRS.Certificate₀
abbrev ZIntervalRS.Certified (I : ZIntervalRS) : Prop := I.Certificate ∨ I.Certificate₀
structure CertifiedZeroIntervals where
  intervals : List (NonemptyInterval ℝ)
  fst_nonneg : ∀ I ∈ intervals, 0 ≤ I.fst
  has_zero : ∀ I ∈ intervals, ∃ t ∈ Set.Ioo I.fst I.snd, riemannZeta (1/2 + Complex.I * t) = 0
  disj : intervals.IsChain fun I J ↦ I.snd ≤ J.fst
@[simp]
noncomputable def CertifiedZeroIntervals.height (C : CertifiedZeroIntervals) : ℝ :=
  if h : C.intervals = [] then 0 else (C.intervals.maxOn (fun I ↦ I.snd) h).snd
theorem CertifiedZeroIntervals.le_height (C : CertifiedZeroIntervals)
    {I : NonemptyInterval ℝ} (hI : I ∈ C.intervals) : I.snd ≤ C.height := by
  rw [CertifiedZeroIntervals.height, dif_neg (List.ne_nil_of_mem hI)]
  exact List.le_apply_maxOn_of_mem (f := fun I : NonemptyInterval ℝ ↦ I.snd) hI
theorem CertifiedZeroIntervals.pairwise (C : CertifiedZeroIntervals) :
    C.intervals.Pairwise (fun I J ↦ I.snd ≤ J.fst) :=
  have : Trans (fun I J : NonemptyInterval ℝ ↦ I.snd ≤ J.fst)
      (fun I J : NonemptyInterval ℝ ↦ I.snd ≤ J.fst)
      (fun I J : NonemptyInterval ℝ ↦ I.snd ≤ J.fst) :=
    ⟨fun {_ b _} hab hbc ↦ (hab.trans b.fst_le_snd).trans hbc⟩
  List.isChain_iff_pairwise.mp C.disj
end Zeta.Certificates
open Zeta.Certificates
theorem Zeta.Certificates.mul_pos_of_abs_sub_lt {a b : ℝ} (h : |a - b| < |b|) :
    0 < a * b := by
  nlinarith [mul_self_lt_mul_self (abs_nonneg (a - b)) h, abs_mul_abs_self (a - b),
    abs_mul_abs_self b, sq_nonneg a]
theorem riemannZeta.exists_zero_of_zIntervalEM_certificate (I : ZIntervalEM) (h : I.Certificate) :
    ∃ t ∈ Set.Ioo I.fst I.snd, riemannZeta (1 / 2 + Complex.I * t) = 0 := by
  have hlr : I.fst ≤ I.snd := I.fst_le_snd
  have hr0 : 0 ≤ I.snd := h.fst_nonneg.trans hlr
  have hL : |hardyZ I.fst - I.fstVal| < |I.fstVal| :=
    (abs_hardyZRemainderEM_le h.fstBernoulli_pos h.fstCutoff_pos h.fst_nonneg).trans_lt
      (by simpa [Real.norm_eq_abs] using h.fst_error)
  have hR : |hardyZ I.snd - I.sndVal| < |I.sndVal| :=
    (abs_hardyZRemainderEM_le h.sndBernoulli_pos h.sndCutoff_pos hr0).trans_lt
      (by simpa [Real.norm_eq_abs] using h.snd_error)
  have hsL : 0 < hardyZ I.fst * I.fstVal := mul_pos_of_abs_sub_lt hL
  have hsR : 0 < hardyZ I.snd * I.sndVal := mul_pos_of_abs_sub_lt hR
  have hprod : hardyZ I.fst * hardyZ I.snd < 0 := by
    nlinarith [mul_pos hsL hsR, h.is_sign_change]
  have hcont : ContinuousOn hardyZ (Set.Icc I.fst I.snd) :=
    continuousOn_hardyZ.mono fun x hx ↦ h.fst_nonneg.trans hx.1
  obtain ⟨t₀, ht₀mem, ht₀⟩ : ∃ t₀ ∈ Set.Icc I.fst I.snd, hardyZ t₀ = 0 := by
    rcases mul_neg_iff.mp hprod with ⟨hlp, hrn⟩ | ⟨hln, hrp⟩
    · exact intermediate_value_Icc' hlr hcont ⟨hrn.le, hlp.le⟩
    · exact intermediate_value_Icc hlr hcont ⟨hln.le, hrp.le⟩
  have hlne : hardyZ I.fst ≠ 0 := left_ne_zero_of_mul hsL.ne'
  have hrne : hardyZ I.snd ≠ 0 := left_ne_zero_of_mul hsR.ne'
  have ht₀Ioo : t₀ ∈ Set.Ioo I.fst I.snd :=
    ⟨lt_of_le_of_ne ht₀mem.1 fun heq ↦ hlne (by rw [heq]; exact ht₀),
     lt_of_le_of_ne ht₀mem.2 fun heq ↦ hrne (by rw [← heq]; exact ht₀)⟩
  exact ⟨t₀, ht₀Ioo, (hardyZ_eq_zero_iff_riemannZeta (h.fst_nonneg.trans ht₀Ioo.1.le)).mp ht₀⟩
namespace Zeta.Certificates
open Complex Set
noncomputable def CertifiedZeroIntervals.zeros (C : CertifiedZeroIntervals) : List ℂ :=
  (C.intervals.pmap (fun I hI ↦ (C.has_zero I hI).choose) (by simp)).map
      fun t : ℝ ↦ 1/2 + I * t
theorem CertifiedZeroIntervals.zeros_spec (C : CertifiedZeroIntervals) :
    ∀ z ∈ C.zeros, z.im ∈ Ioo 0 C.height ∧ riemannZeta z = 0 := by
  intro z hz
  simp only [CertifiedZeroIntervals.zeros, List.mem_map] at hz
  rcases hz with ⟨I, hI, rfl⟩
  simp only [one_div, List.mem_pmap] at hI
  obtain ⟨a, ha, rfl⟩ := hI
  have := (C.has_zero a ha).choose_spec
  refine ⟨?_, by grind⟩
  convert Ioo_subset_Ioo (C.fst_nonneg _ ha) (le_height C ha) this.1
  simp
theorem CertifiedZeroIntervals.zeros_length (C : CertifiedZeroIntervals) :
    C.zeros.length = C.intervals.length := by
  simp [CertifiedZeroIntervals.zeros, List.length_map, List.length_pmap]
theorem CertifiedZeroIntervals.zeros_nodup (C : CertifiedZeroIntervals) :
    C.zeros.Nodup := by
  have hpair := C.pairwise
  have hInod : C.intervals.Nodup := by
    rw [show C.intervals.Nodup = List.Pairwise (· ≠ ·) C.intervals from rfl,
      List.pairwise_iff_getElem]
    intro i j hi hj hlt heq
    have hsep := List.pairwise_iff_getElem.mp hpair i j hi hj hlt
    obtain ⟨t, ht, -⟩ := C.has_zero _ (List.getElem_mem hi)
    rw [← heq] at hsep
    exact absurd (ht.1.trans ht.2) (not_lt.mpr hsep)
  have hcomp : ∀ I ∈ C.intervals, ∀ J ∈ C.intervals, I ≠ J →
      I.snd ≤ J.fst ∨ J.snd ≤ I.fst := by
    intro I hI J hJ hne
    have hpg := List.pairwise_iff_getElem.mp hpair
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hI
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hJ
    rcases lt_trichotomy i j with h | h | h
    · exact Or.inl (hpg i j hi hj h)
    · subst h; exact absurd rfl hne
    · exact Or.inr (hpg j i hj hi h)
  have key : (C.intervals.pmap
      (fun I hI ↦ (C.has_zero I hI).choose) (by simp)).Nodup := by
    refine List.Nodup.pmap (fun I hI J hJ heq ↦ ?_) hInod
    by_contra hne
    have hsI := (C.has_zero I hI).choose_spec.1
    have hsJ := (C.has_zero J hJ).choose_spec.1
    rw [Set.mem_Ioo] at hsI hsJ
    rw [heq] at hsI
    rcases hcomp I hI J hJ hne with h | h
    · linarith [hsI.2, hsJ.1, h]
    · linarith [hsI.1, hsJ.2, h]
  rw [zeros]
  exact List.Nodup.map (f := fun t : ℝ ↦ 1 / 2 + Complex.I * t)
    (fun a b h ↦ by simpa using h) key
theorem CertifiedZeroIntervals.zeros_re (C : CertifiedZeroIntervals) {z : ℂ} (hz : z ∈ C.zeros) :
    z.re = 1 / 2 := by
  simp only [CertifiedZeroIntervals.zeros, List.mem_map] at hz
  rcases hz with ⟨I, hI, rfl⟩
  simp only [one_div, List.mem_pmap] at hI
  obtain ⟨a, ha, rfl⟩ := hI
  simp
theorem CertifiedZeroIntervals.zeros_im (C : CertifiedZeroIntervals) {z : ℂ} (hz : z ∈ C.zeros) :
    z.im ∈ Ioo 0 C.height :=
  (C.zeros_spec z hz).1
theorem CertifiedZeroIntervals.height_le (C : CertifiedZeroIntervals) {r : ℝ} (h0 : 0 ≤ r)
    (hr : ∀ I ∈ C.intervals, I.snd ≤ r) : C.height ≤ r := by
  rw [CertifiedZeroIntervals.height]
  split
  · exact h0
  · exact hr _ List.maxOn_mem
private theorem snd_le_getLast_isChain : ∀ {l : List (NonemptyInterval ℝ)} (hne : l ≠ [])
    (_ : l.IsChain (fun I J ↦ I.snd ≤ J.fst)) {I}, I ∈ l →
    I.snd ≤ (l.getLast hne).snd
  | [], hne, _, _, _ => absurd rfl hne
  | [_], _, _, _, hI => by rw [List.mem_singleton] at hI; subst hI; simp
  | _ :: b :: t, _, hc, _, hI => by
    rw [List.isChain_cons_cons] at hc
    rw [List.getLast_cons (List.cons_ne_nil b t)]
    rcases List.mem_cons.1 hI with rfl | hI'
    · exact hc.1.trans (b.fst_le_snd.trans
        (snd_le_getLast_isChain (List.cons_ne_nil b t) hc.2 List.mem_cons_self))
    · exact snd_le_getLast_isChain (List.cons_ne_nil b t) hc.2 hI'
theorem CertifiedZeroIntervals.height_le_getLast (C : CertifiedZeroIntervals)
    (hne : C.intervals ≠ []) : C.height ≤ (C.intervals.getLast hne).snd := by
  refine C.height_le (le_trans (C.fst_nonneg _ (List.getLast_mem hne))
    (C.intervals.getLast hne).fst_le_snd) (fun I hI ↦ snd_le_getLast_isChain hne C.disj hI)
theorem CertifiedZeroIntervals.height_le_of_getLast? (C : CertifiedZeroIntervals)
    {I : NonemptyInterval ℝ} {q : ℝ} (h : C.intervals.getLast? = some I) (hq : I.snd ≤ q) :
    C.height ≤ q := by
  have hne : C.intervals ≠ [] := by
    intro he
    rw [he] at h
    simp at h
  refine (C.height_le_getLast hne).trans ?_
  rwa [show C.intervals.getLast hne = I from
    Option.some.inj ((List.getLast?_eq_some_getLast hne).symm.trans h)]
end Zeta.Certificates
end
end CertificatePort100


section CertificatePort101
section
namespace Zeta.Certificates
open Real Set
structure GramPoint extends NonemptyInterval ℝ where
  idx : ℕ
  fstCutoff : ℕ
  fstBernoulli : ℕ
  sndCutoff : ℕ
  sndBernoulli : ℕ
noncomputable abbrev GramPoint.fstVal (G : GramPoint) : ℝ :=
  riemannSiegelThetaApproximant G.fstBernoulli G.fstCutoff G.fst
noncomputable abbrev GramPoint.sndVal (G : GramPoint) : ℝ :=
  riemannSiegelThetaApproximant G.sndBernoulli G.sndCutoff G.snd
structure GramPoint.Certificate (G : GramPoint) where
  fst_nonneg : 0 ≤ G.fst
  snd_nonneg : 0 ≤ G.snd
  fstBernoulli_pos : 0 < G.fstBernoulli
  sndBernoulli_pos : 0 < G.sndBernoulli
  fst_bound : G.idx * π - G.fstVal >
    riemannSiegelThetaStirlingErrorBound' G.fstBernoulli G.fstCutoff G.fst
  snd_bound : G.sndVal - G.idx * π >
    riemannSiegelThetaStirlingErrorBound' G.sndBernoulli G.sndCutoff G.snd
structure GramBlock where
  left : GramPoint
  right : GramPoint
  zeros : List (NonemptyInterval ℝ)
  seq : left.idx + 1 = right.idx
  separated : left.snd ≤ right.fst
structure GramBlock.Certificate (G : GramBlock) where
  left_certificate : G.left.Certificate
  right_certificate : G.right.Certificate
  has_zero : ∀ z ∈ G.zeros, ∃ t ∈ Set.Ioo z.fst z.snd, riemannZeta (1 / 2 + Complex.I * t) = 0
  contains_zero : ∃ z ∈ G.zeros, z.fst ∈ Icc G.left.snd G.right.fst ∧
    z.snd ∈ Icc G.left.snd G.right.fst
structure CertifiedGramBlockSeq where
  blocks : List GramBlock
  seq : blocks.IsChain fun a b ↦ a.right.idx = b.left.idx
  cert : ∀ b ∈ blocks, b.Certificate
  non_empty : blocks ≠ []
  wide : (5 + (0.128 : ℝ) * ((blocks.getLast non_empty).right.snd / (2 * π)).log) <
    ((blocks.getLast non_empty).right.fst - (blocks.head non_empty).left.snd) / 2
  high : 168 * π < (blocks.head non_empty).left.fst
abbrev CertifiedGramBlockSeq.minIdx (C : CertifiedGramBlockSeq) : ℕ :=
  (C.blocks.head C.non_empty).left.idx
theorem GramPoint.certificate_theta_left_lt {G : GramPoint} (h : G.Certificate) :
    riemannSiegelTheta G.fst < (G.idx : ℝ) * π := by
  have hb := abs_le.1 <| abs_riemannSiegelTheta_sub_stirling_shift_le' (N := G.fstCutoff)
    h.fstBernoulli_pos h.fst_nonneg
  linarith [hb.2, h.fst_bound]
theorem GramPoint.certificate_theta_right_gt {G : GramPoint} (h : G.Certificate) :
    (G.idx : ℝ) * π < riemannSiegelTheta G.snd := by
  have hb := abs_le.1 <| abs_riemannSiegelTheta_sub_stirling_shift_le' (N := G.sndCutoff)
    h.sndBernoulli_pos h.snd_nonneg
  linarith [hb.1, h.snd_bound]
theorem CertifiedGramBlockSeq.getElem_left_idx (S : CertifiedGramBlockSeq) (j : ℕ) :
    ∀ (hj : j < S.blocks.length),
      (S.blocks[j]).left.idx = (S.blocks.head S.non_empty).left.idx + j := by
  induction j with
  | zero => intro hj; rw [List.head_eq_getElem_zero S.non_empty, Nat.add_zero]
  | succ i ih =>
    intro hj
    have hi : i < S.blocks.length := Nat.lt_of_succ_lt hj
    linarith [List.isChain_iff_getElem.1 S.seq i (by lia), (S.blocks[i]'hi).seq, ih hi]
end Zeta.Certificates
end
end CertificatePort101


section CertificatePort102
section
open Real Set Filter Zeta.Certificates Complex MeasureTheory
theorem existsUnique_gramPoint (n : ℕ) :
    ∃! x ∈ Ici (7 : ℝ), riemannSiegelTheta x = n * π := by
  have hi := isPreconnected_Ici.intermediate_value_Ici (a := 7) (by simp)
    (by simpa using ⟨7, by simp⟩) continuousOn_riemannSiegelTheta_gramDomain
    tendsto_riemannSiegelTheta_atTop
  have : n * π ∈ Ici (riemannSiegelTheta 7) := by grind [riemannSiegelTheta_seven_le n]
  obtain ⟨x, hx, hθx⟩ := hi this
  refine ⟨x, ⟨hx, hθx⟩, fun y ⟨hy, hθy⟩ ↦ ?_⟩
  have := strictMonoOn_riemannSiegelTheta_gramDomain hx hy
  have := strictMonoOn_riemannSiegelTheta_gramDomain hy hx
  grind
noncomputable def gramPoint (n : ℕ) : ℝ := (existsUnique_gramPoint n).choose
theorem gramPoint_theta_eq (n : ℕ) : riemannSiegelTheta (gramPoint n) = n * π :=
  (existsUnique_gramPoint n).choose_spec.1.2
theorem gramPoint_seven_le (n : ℕ) : 7 ≤ gramPoint n :=
  (existsUnique_gramPoint n).choose_spec.1.1
theorem gramPoint_pos (n : ℕ) : 0 < gramPoint n := by
  linarith [gramPoint_seven_le n]
theorem strictMono_gramPoint : StrictMono gramPoint := fun m n hmn ↦ by
  rw [← strictMonoOn_riemannSiegelTheta_gramDomain.lt_iff_lt
      (Set.mem_Ici.mpr (gramPoint_seven_le m))
      (Set.mem_Ici.mpr (gramPoint_seven_le n)), gramPoint_theta_eq, gramPoint_theta_eq]
  exact mul_lt_mul_of_pos_right (by exact_mod_cast hmn) pi_pos
theorem gramPoint_le_iff {n : ℕ} {t : ℝ} (ht : 7 ≤ t) :
    gramPoint n ≤ t ↔ (n : ℝ) * π ≤ riemannSiegelTheta t := by
  rw [← gramPoint_theta_eq n]
  exact (strictMonoOn_riemannSiegelTheta_gramDomain.le_iff_le
    (mem_Ici.mpr (gramPoint_seven_le n)) (mem_Ici.mpr ht)).symm
theorem lt_gramPoint_iff {n : ℕ} {t : ℝ} (ht : 7 ≤ t) :
    t < gramPoint n ↔ riemannSiegelTheta t < (n : ℝ) * π :=
  lt_iff_lt_of_le_iff_le (gramPoint_le_iff ht)
theorem gramPoint_lt_iff {n : ℕ} {t : ℝ} (ht : 7 ≤ t) :
    gramPoint n < t ↔ (n : ℝ) * π < riemannSiegelTheta t := by
  rw [← gramPoint_theta_eq n]
  exact (strictMonoOn_riemannSiegelTheta_gramDomain.lt_iff_lt
    (mem_Ici.mpr (gramPoint_seven_le n)) (mem_Ici.mpr ht)).symm
theorem lt_gramPoint_of_theta_lt {n : ℕ} {t : ℝ} (h : riemannSiegelTheta t < (n : ℝ) * π) :
    t < gramPoint n :=
  not_le.1 fun hcon ↦
    absurd ((gramPoint_le_iff ((gramPoint_seven_le n).trans hcon)).mp hcon) (not_le.mpr h)
noncomputable instance {T : ℝ} : Fintype (riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :=
  (Kadiri.zeroes_rect_univ_positive_height_finite T).fintype
lemma riemannZeta.N_eq_sum (T : ℝ) :
    riemannZeta.N T = ∑ ρ ∈ (riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)).toFinset,
      (riemannZeta.order ρ : ℝ) := by
  rw [riemannZeta.N, riemannZeta.zeroes_sum, tsum_fintype, ← Finset.sum_set_coe]
  exact Finset.sum_congr rfl fun _ _ ↦ one_mul _
lemma riemannZeta.exists_intCast_N (T : ℝ) : ∃ m : ℤ, riemannZeta.N T = m :=
  ⟨∑ ρ ∈ (riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)).toFinset, riemannZeta.order ρ, by
    rw [riemannZeta.N_eq_sum]; push_cast; rfl⟩
private lemma riemannZeta.order_nonneg_of_mem_toFinset {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ (riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)).toFinset) :
    (0 : ℝ) ≤ (riemannZeta.order ρ : ℝ) := by
  exact_mod_cast (Kadiri.riemannZeta_order_pos_positiveHeightZero
    ⟨ρ, Set.mem_toFinset.1 hρ⟩).le
theorem intervalIntegrable_gramCoord {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun t ↦ Int.fract (gramCoord a t)) volume a b := by
  have hsub : Set.uIoc a b ⊆ Set.Ici (0 : ℝ) := fun x hx ↦ ((le_min ha hb).trans_lt hx.1).le
  have hcont : ContinuousOn (fun t ↦ gramCoord a t) (Set.uIoc a b) :=
    ((continuousOn_riemannSiegelTheta.mono hsub).sub continuousOn_const).div_const _
  rw [intervalIntegrable_iff]
  refine .of_bound measure_Ioc_lt_top (measurable_fract.comp_aemeasurable
    (hcont.aestronglyMeasurable measurableSet_uIoc).aemeasurable).aestronglyMeasurable 1
    (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
  exact (Int.fract_lt_one _).le
private theorem riemannZeta.zeroes_rect_Ioo_subset {τ t : ℝ} (h : τ ≤ t) :
    riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 τ) ⊆
      riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 t) :=
  fun _ hz ↦ ⟨hz.1, Set.Ioo_subset_Ioo_right h hz.2.1, hz.2.2⟩
theorem riemannZeta.N_mono : Monotone riemannZeta.N := fun τ t hτt ↦ by
  rw [riemannZeta.N_eq_sum, riemannZeta.N_eq_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun _ hz ↦ Set.mem_toFinset.2 (zeroes_rect_Ioo_subset hτt (Set.mem_toFinset.1 hz)))
    fun _ hρ _ ↦ riemannZeta.order_nonneg_of_mem_toFinset hρ
theorem riemannZeta.N_add_one_le_of_zero {τ t : ℝ} (hτ : 0 < τ)
    (h_zero : riemannZeta (1 / 2 + I * τ) = 0) (ht : τ < t) :
    riemannZeta.N τ + 1 ≤ riemannZeta.N t := by
  have him : (1 / 2 + I * (τ : ℂ)).im = τ := by simp
  have hmem : (1 / 2 + I * (τ : ℂ)) ∈ riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 t) :=
    ⟨Set.mem_univ _, by rw [him]; exact ⟨hτ, ht⟩, h_zero⟩
  have hnot : (1 / 2 + I * (τ : ℂ)) ∉
      (riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 τ)).toFinset := fun hc ↦
    absurd (him ▸ (Set.mem_toFinset.1 hc).2.1).2 (lt_irrefl τ)
  have key := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun ρ ↦ (riemannZeta.order ρ : ℝ))
    (Finset.insert_subset (Set.mem_toFinset.2 hmem) fun _ hz ↦
      Set.mem_toFinset.2 (zeroes_rect_Ioo_subset ht.le (Set.mem_toFinset.1 hz)))
    fun _ hρ _ ↦ riemannZeta.order_nonneg_of_mem_toFinset hρ
  rw [Finset.sum_insert hnot] at key
  have h1 : (1 : ℝ) ≤ (riemannZeta.order (1 / 2 + I * (τ : ℂ)) : ℝ) := by
    exact_mod_cast Kadiri.riemannZeta_one_le_order_positiveHeightZero ⟨_, hmem⟩
  rw [riemannZeta.N_eq_sum, riemannZeta.N_eq_sum]
  linarith
theorem riemannZeta.N_le_of_gramPoints (n k : ℕ) (hg : 168 * π < gramPoint n)
    (h : (5 + (0.128 : ℝ) * (gramPoint (n + k + 1) / (2 * π)).log) <
      (gramPoint (n + k + 1) - gramPoint n) / 2)
    (hc : ∀ j < k + 1, ∃ t ∈ Ico (gramPoint (n + j)) (gramPoint (n + j + 1)),
      riemannZeta (1 / 2 + I * t) = 0) :
    riemannZeta.N (gramPoint n) ≤ n + 1 := by
  have hlt : gramPoint n < gramPoint (n + k + 1) := strictMono_gramPoint (by lia)
  have hg_le := hlt.le
  have hX {j : ℕ} {t : ℝ} (ht : t ∈ Ico (gramPoint (n + j)) (gramPoint (n + j + 1))) :
      ⌊gramCoord (gramPoint n) t⌋ = j := by
    have h7 : (7 : ℝ) ≤ t := (gramPoint_seven_le _).trans ht.1
    have h1 := (gramPoint_le_iff h7).mp ht.1
    have h2 := (lt_gramPoint_iff h7).mp ht.2
    push_cast at h1 h2
    rw [Int.floor_eq_iff]
    simp only [gramCoord, gramPoint_theta_eq, Int.cast_natCast]
    rw [le_div_iff₀ pi_pos, div_lt_iff₀ pi_pos]
    constructor <;> linarith
  have hN {j : ℕ} {t : ℝ} (hj : j < k + 1)
      (ht : t ∈ Ico (gramPoint (n + j)) (gramPoint (n + j + 1))) :
      j ≤ riemannZeta.N t - riemannZeta.N (gramPoint n) := by
    induction j generalizing t with
    | zero => simpa using sub_nonneg.2 (riemannZeta.N_mono ht.1)
    | succ j ih =>
      obtain ⟨τ, hτ, h_zero⟩ := hc j (by grind)
      specialize ih (t := τ) (by grind) (by simpa [add_assoc] using hτ)
      push_cast
      linarith [riemannZeta.N_add_one_le_of_zero (τ := τ) (t := t)
        (by grind [gramPoint_pos (n + j)]) h_zero (by grind)]
  have hΔ {t : ℝ} (ht : t ∈ Set.Ico (gramPoint n) (gramPoint (n + k + 1))) :
      ⌊gramCoord (gramPoint n) t⌋ ≤ riemannZeta.N t - riemannZeta.N (gramPoint n) := by
    have hcov := Ico_subset_biUnion_Ico (k + 1) (fun j ↦ gramPoint (n + j))
      (by simpa [add_assoc] using ht)
    simp only [Set.mem_iUnion, Finset.mem_range, exists_prop, ← add_assoc] at hcov
    obtain ⟨j, hj, htj⟩ := hcov
    rw [hX htj]
    exact_mod_cast hN hj htj
  suffices hq1 : riemannZeta.N (gramPoint n) - n - 1 < 1 by
    obtain ⟨M, hM⟩ := riemannZeta.exists_intCast_N (gramPoint n)
    rw [hM] at hq1 ⊢
    exact_mod_cast Int.lt_add_one_iff.mp
      (by exact_mod_cast (by push_cast; linarith : (M : ℝ) < (((n : ℤ) + 1 : ℤ) : ℝ) + 1))
  set q : ℝ := riemannZeta.N (gramPoint n) - n - 1 with hq
  have hS : (fun t ↦ q - Int.fract (gramCoord (gramPoint n) t))
      ≤ᵐ[volume.restrict (Icc (gramPoint n) (gramPoint (n + k + 1)))] argZeta := by
    filter_upwards [(finite_setOf_riemannZeta_zero_ray_Icc (gramPoint_pos n)
        hg_le).countable.ae_notMem <| volume.restrict (Icc (gramPoint n) (gramPoint (n + k + 1))),
      ae_restrict_mem measurableSet_Icc, Measure.ae_ne _ (gramPoint (n + k + 1))] with t ht ht' h_ne
    push Not at ht
    have ht_good := mt ht (by simpa using ht')
    push Not at ht_good
    have hΔt := hΔ (Set.mem_Ico.mpr ⟨ht'.1, ht'.2.lt_of_ne h_ne⟩)
    rw [riemannZeta.N_eq_of_forall_re_mem_Ico (by grind [gramPoint_pos n])
      fun σ hσ ↦ ht_good σ (by simpa using hσ.1)] at hΔt
    have hgx : gramCoord (gramPoint n) t = riemannSiegelTheta t / π - n := by
      rw [gramCoord, gramPoint_theta_eq]; field_simp
    rw [hq, Int.fract]
    linarith
  have hfract := integral_fract_gramCoord_le (k := k + 1) (p := fun i ↦ gramPoint (n + i))
    (by simpa using (gramPoint_pos n).le) (fun _ _ ↦ strictMono_gramPoint (by lia))
    (strictMonoOn_riemannSiegelTheta_gramDomain.mono fun _ _ ↦ by grind [gramPoint_seven_le])
    (fun _ _ ↦ by simp [gramPoint_theta_eq]; ring)
  have hleh := (abs_le.mp (norm_integral_argZeta_le_five_unconditional hg hlt)).2
  have hIx := intervalIntegrable_gramCoord (gramPoint_pos n).le (gramPoint_pos (n + k + 1)).le
  have hint := intervalIntegral.integral_mono_ae_restrict hg_le
    (.sub intervalIntegrable_const hIx) (intervalIntegrable_argZeta (gramPoint_pos n) hg_le) hS
  rw [intervalIntegral.integral_sub intervalIntegrable_const hIx] at hint
  simp only [intervalIntegral.integral_const, smul_eq_mul, add_zero, ← add_assoc] at hint hfract
  rw [← mul_lt_mul_iff_right₀ (sub_pos.mpr hlt)]
  linarith
theorem riemannSiegelTheta_zero : riemannSiegelTheta 0 = 0 := by
  unfold riemannSiegelTheta argVariation
  simp only [zero_div, zero_mul, sub_zero]
  split <;> simp
theorem riemannSiegelTheta_nonpos_of_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 7) :
    riemannSiegelTheta x ≤ 0 := by
  obtain ⟨hx0, hx7⟩ := hx
  have hb : (0 : ℝ) ≤ x / 7 := by positivity
  have hconv := convexOn_riemannSiegelTheta.2 Set.self_mem_Ici
    (Set.mem_Ici.2 (by norm_num : (0 : ℝ) ≤ 7)) (by linarith : (0 : ℝ) ≤ 1 - x / 7) hb (by ring)
  rw [show (1 - x / 7) • (0 : ℝ) + (x / 7) • (7 : ℝ) = x by simp only [smul_eq_mul]; ring] at hconv
  simp only [riemannSiegelTheta_zero, smul_eq_mul, mul_zero, zero_add] at hconv
  nlinarith [(by simpa using riemannSiegelTheta_seven_le 0 : riemannSiegelTheta 7 ≤ 0)]
namespace Zeta.Certificates
theorem GramPoint.certificate_left_lt_gramPoint {G : GramPoint} (h : G.Certificate) :
    G.fst < gramPoint G.idx :=
  lt_gramPoint_of_theta_lt (G.certificate_theta_left_lt h)
theorem GramPoint.certificate_gramPoint_lt_right {G : GramPoint} (h : G.Certificate) :
    gramPoint G.idx < G.snd := by
  have hgt := G.certificate_theta_right_gt h
  have hpos : (0 : ℝ) < riemannSiegelTheta G.snd := lt_of_le_of_lt (by positivity) hgt
  refine (gramPoint_lt_iff (not_lt.mp fun hcon ↦ ?_)).mpr hgt
  linarith [riemannSiegelTheta_nonpos_of_mem_Icc ⟨h.snd_nonneg, hcon.le⟩]
theorem GramBlock.certificate_exists_zero {B : GramBlock} (h : B.Certificate) :
    ∃ t ∈ Set.Ico (gramPoint B.left.idx) (gramPoint B.right.idx),
      riemannZeta (1 / 2 + I * t) = 0 := by
  obtain ⟨z, hz_mem, hz_left, hz_right⟩ := h.contains_zero
  obtain ⟨t, ht_mem, ht_zero⟩ := h.has_zero z hz_mem
  refine ⟨t, ⟨?_, ?_⟩, ht_zero⟩
  · linarith [ht_mem.1, hz_left.1, B.left.certificate_gramPoint_lt_right h.left_certificate]
  · linarith [ht_mem.2, hz_right.2, B.right.certificate_left_lt_gramPoint h.right_certificate]
theorem CertifiedGramBlockSeq.head_left_le_gramPoint (C : CertifiedGramBlockSeq) :
    (C.blocks.head C.non_empty).left.fst ≤ gramPoint C.minIdx :=
  (GramPoint.certificate_left_lt_gramPoint
    (C.cert _ (List.head_mem C.non_empty)).left_certificate).le
end Zeta.Certificates
theorem riemannZeta.N_le_of_certifiedGramBlockSeq (S : CertifiedGramBlockSeq) :
    riemannZeta.N (gramPoint S.minIdx) ≤ S.minIdx + 1 := by
  have hLpos : 0 < S.blocks.length := List.length_pos_of_ne_nil S.non_empty
  have hlen1 : S.blocks.length - 1 < S.blocks.length := by lia
  set n := (S.blocks.head S.non_empty).left.idx with hn_def
  set k := S.blocks.length - 1 with hk_def
  have hcertHead : (S.blocks.head S.non_empty).Certificate := S.cert _ (List.head_mem S.non_empty)
  have hcertLast : (S.blocks.getLast S.non_empty).Certificate :=
    S.cert _ (List.getLast_mem S.non_empty)
  have hlast_lidx : (S.blocks.getLast S.non_empty).left.idx = n + k := by
    rw [List.getLast_eq_getElem S.non_empty,
      S.getElem_left_idx (S.blocks.length - 1) hlen1, ← hn_def]
  have hlast_ridx : (S.blocks.getLast S.non_empty).right.idx = n + k + 1 := by
    have := (S.blocks.getLast S.non_empty).seq
    lia
  have hg : 168 * π < gramPoint n := lt_of_lt_of_le S.high S.head_left_le_gramPoint
  have hc : ∀ j < k + 1, ∃ t ∈ Set.Ico (gramPoint (n + j)) (gramPoint (n + j + 1)),
      riemannZeta (1 / 2 + I * t) = 0 := fun j hj ↦ by
    have hjl : j < S.blocks.length := by lia
    have hlidx : (S.blocks[j]'hjl).left.idx = n + j := by
      rw [S.getElem_left_idx j hjl, ← hn_def]
    have hridx : (S.blocks[j]'hjl).right.idx = n + j + 1 := by
      have := (S.blocks[j]'hjl).seq; lia
    obtain ⟨t, ht_mem, ht_zero⟩ :=
      (S.blocks[j]'hjl).certificate_exists_zero (S.cert _ (List.getElem_mem hjl))
    exact ⟨t, by rwa [hlidx, hridx] at ht_mem, ht_zero⟩
  have h : (5 + (0.128 : ℝ) * (gramPoint (n + k + 1) / (2 * π)).log)
      < (gramPoint (n + k + 1) - gramPoint n) / 2 := by
    have hB_last := hlast_ridx ▸ (S.blocks.getLast S.non_empty).right.certificate_left_lt_gramPoint
      hcertLast.right_certificate
    have hA_head := hn_def.symm ▸ (S.blocks.head S.non_empty).left.certificate_gramPoint_lt_right
      hcertHead.left_certificate
    have hlog : Real.log (gramPoint (n + k + 1) / (2 * π))
        ≤ Real.log ((S.blocks.getLast S.non_empty).right.snd / (2 * π)) := by
      refine Real.log_le_log (div_pos (gramPoint_pos _) (by positivity)) ?_
      gcongr
      exact (hlast_ridx ▸ (S.blocks.getLast S.non_empty).right.certificate_gramPoint_lt_right
        hcertLast.right_certificate).le
    linarith [S.wide]
  exact riemannZeta.N_le_of_gramPoints n k hg h hc
end
end CertificatePort102


section CertificatePort103
section
open Zeta.Certificates
theorem riemannZeta.zeroes_rect_Ioo_finite (T : ℝ) :
    (riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 T)).Finite := by
  have hSc : IsCompact ((Set.Icc 0 1 ×ℂ Set.Icc 0 T) : Set ℂ) :=
    isCompact_Icc.reProdIm isCompact_Icc
  apply Set.Finite.subset (riemannZeta.zeroes_on_Compact_finite' hSc)
  rintro z ⟨-, hzim, hz0⟩
  have hre := riemannZeta_re_mem_Ioo_of_eq_zero_of_im_ne_zero hz0 hzim.1.ne'
  exact ⟨Complex.mem_reProdIm.mpr ⟨⟨hre.1.le, hre.2.le⟩, ⟨hzim.1.le, hzim.2.le⟩⟩, hz0⟩
theorem riemannZeta.le_N_of_certifiedZeroIntervals (C : CertifiedZeroIntervals) :
    C.intervals.length ≤ riemannZeta.N C.height := by
  have : Fintype ↥(riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 C.height)) :=
    (zeroes_rect_Ioo_finite C.height).fintype
  have hzero : ∀ k : Fin C.intervals.length,
      ∃ t ∈ Set.Ioo (C.intervals.get k).fst (C.intervals.get k).snd,
        riemannZeta (1 / 2 + Complex.I * t) = 0 :=
    fun k ↦ C.has_zero _ (List.get_mem _ k)
  set t : Fin C.intervals.length → ℝ := fun k ↦ (hzero k).choose with ht
  have htspec : ∀ k, t k ∈ Set.Ioo (C.intervals.get k).fst (C.intervals.get k).snd ∧
      riemannZeta (1 / 2 + Complex.I * (t k : ℂ)) = 0 :=
    fun k ↦ (hzero k).choose_spec
  have hmono : StrictMono t := fun k₁ k₂ hlt ↦
    calc t k₁ < (C.intervals.get k₁).snd := (htspec k₁).1.2
      _ ≤ (C.intervals.get k₂).fst := List.pairwise_iff_get.mp C.pairwise k₁ k₂ hlt
      _ < t k₂ := (htspec k₂).1.1
  have hmem : ∀ k : Fin C.intervals.length,
      (1 / 2 + Complex.I * (t k : ℂ)) ∈ riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 C.height) := by
    refine fun k ↦ ⟨Set.mem_univ _, ?_, (htspec k).2⟩
    rw [show (1 / 2 + Complex.I * (t k : ℂ)).im = t k from by simp]
    exact ⟨(C.fst_nonneg _ (List.get_mem _ k)).trans_lt (htspec k).1.1,
      (htspec k).1.2.trans_le (C.le_height (List.get_mem _ k))⟩
  let g : Fin C.intervals.length → ↥(riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 C.height)) :=
    fun k ↦ ⟨1 / 2 + Complex.I * (t k : ℂ), hmem k⟩
  have hg_inj : Function.Injective g := fun k₁ k₂ hgeq ↦
    hmono.injective (by simpa [g] using congrArg (Complex.im ∘ Subtype.val) hgeq)
  have hcard : C.intervals.length ≤
      Fintype.card ↥(riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 C.height)) := by
    simpa using Fintype.card_le_of_injective g hg_inj
  have hNeq : riemannZeta.N C.height =
      ∑ ρ : ↥(riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 C.height)),
        ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ) := by
    rw [riemannZeta.N, riemannZeta.zeroes_sum, tsum_fintype]
    exact Finset.sum_congr rfl fun ρ _ ↦ one_mul _
  rw [hNeq]
  calc ((C.intervals.length : ℕ) : ℝ)
      ≤ ((Fintype.card ↥(riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 C.height)) : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ ≤ ∑ ρ : ↥(riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 C.height)),
          ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ) := by
        have h := Finset.card_nsmul_le_sum
          (Finset.univ (α := ↥(riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 C.height))))
          (fun ρ ↦ ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ)) 1
          (fun ρ _ ↦ by
            exact_mod_cast Kadiri.riemannZeta_one_le_order_positiveHeightZero ρ)
        rwa [Finset.card_univ, nsmul_eq_mul, mul_one] at h
structure CertifiedZeroCount extends CertifiedGramBlockSeq, CertifiedZeroIntervals where
  count : toCertifiedGramBlockSeq.minIdx + 1 = intervals.length
  below : toCertifiedZeroIntervals.height ≤ gramPoint toCertifiedGramBlockSeq.minIdx
end
end CertificatePort103


section CertificatePort104
section
open Set
theorem riemannZeta_ne_zero_of_mem_Ioo_zero_one {x : ℝ} (hx : x ∈ Ioo 0 1) :
    riemannZeta x ≠ 0 :=
  fun hz ↦ by simpa [hz] using riemannZeta_ofReal_re_neg_of_mem_Ioo hx
theorem riemannZeta_ofReal_ne_zero {x : ℝ} (h : ¬∃ n : ℕ, x = -2 * (n + 1)) :
    riemannZeta x ≠ 0 := by
  by_cases hx1 : 1 ≤ x
  ·
    exact riemannZeta_ne_zero_of_one_le_re (by simpa using hx1)
  push Not at hx1
  rcases lt_trichotomy x 0 with hx0 | hx0 | hx0
  ·
    rw [show (x : ℂ) = 1 - ((1 - x : ℝ) : ℂ) by push_cast; ring]
    refine Kadiri.riemannZeta_one_sub_ne_zero_of_one_le_re
      (by simp only [Complex.ofReal_re]; linarith) ?_
    rw [show ((Real.pi : ℂ) * ((1 - x : ℝ) : ℂ) / 2) = ((Real.pi * (1 - x) / 2 : ℝ) : ℂ) by
      push_cast; ring, ← Complex.ofReal_cos, ne_eq, Complex.ofReal_eq_zero]
    intro hcos
    rw [Real.cos_eq_zero_iff] at hcos
    obtain ⟨n, hn⟩ := hcos
    apply h
    have hpi := Real.pi_pos
    have hxn : x = -2 * n := by field_simp at hn; nlinarith [hn]
    have hn1 : (0 : ℤ) < n := by exact_mod_cast show (0 : ℝ) < (n : ℝ) by linarith
    refine ⟨(n - 1).toNat, ?_⟩
    have hc : (((n - 1).toNat : ℤ) : ℝ) = (n : ℝ) - 1 := by
      rw [Int.toNat_of_nonneg (by lia : (0 : ℤ) ≤ n - 1)]; push_cast; ring
    rw [hxn]; push_cast at hc ⊢; linarith
  ·
    subst hx0
    rw [Complex.ofReal_zero, riemannZeta_zero]
    norm_num
  ·
    exact riemannZeta_ne_zero_of_mem_Ioo_zero_one ⟨hx0, hx1⟩
end
end CertificatePort104


section CertificatePort105
section
open Complex
theorem Differentiable.iteratedDeriv_re_of_complex {e : ℂ → ℂ} (he : Differentiable ℂ e) (n : ℕ)
    (x : ℝ) : iteratedDeriv n (fun y : ℝ ↦ (e y).re) x = (iteratedDeriv n e x).re := by
  induction n generalizing e with
  | zero => simp
  | succ n ih =>
      have hderiv : Differentiable ℂ (_root_.deriv e) := he.deriv
      have hstep : _root_.deriv (fun y : ℝ ↦ (e y).re) = fun y : ℝ ↦ (_root_.deriv e y).re :=
        funext fun y ↦ ((he _).hasDerivAt.real_of_complex).deriv
      rw [iteratedDeriv_succ', hstep, ih hderiv, ← iteratedDeriv_succ']
end
end CertificatePort105


section CertificatePort106
section
open Asymptotics Complex Filter MeasureTheory Topology
open scoped Real
namespace Zeta.RiemannSiegel
theorem norm_exp_neg_pi_div_four_mul_I : ‖exp (-((π / 4 : ℝ) * I))‖ = 1 := by
  rw [show -(((π / 4 : ℝ) : ℂ) * I) = ((-(π / 4) : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _
noncomputable def rotatedFun (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  exp (-((π / 4 : ℝ) * I)) * f (exp (-((π / 4 : ℝ) * I)) * z)
theorem rotatedFun_exp_mul (f : ℂ → ℂ) (x : ℂ) :
    rotatedFun f (exp ((π / 4 : ℝ) * I) * x) = exp (-((π / 4 : ℝ) * I)) * f x := by
  rw [rotatedFun, ← mul_assoc, exp_neg_pi_div_four_mul_I_mul_exp, one_mul]
theorem norm_rotatedFun (f : ℂ → ℂ) (z : ℂ) :
    ‖rotatedFun f z‖ = ‖f (exp (-((π / 4 : ℝ) * I)) * z)‖ := by
  rw [rotatedFun, norm_mul, norm_exp_neg_pi_div_four_mul_I, one_mul]
theorem differentiableAt_rotatedFun {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f (exp (-((π / 4 : ℝ) * I)) * z)) :
    DifferentiableAt ℂ (rotatedFun f) z :=
  (hf.comp z (by fun_prop)).const_mul _
theorem tendsto_nhdsWithin_exp_neg_pi_div_four_mul_I (w : ℂ) :
    Tendsto (fun z : ℂ ↦ exp (-((π / 4 : ℝ) * I)) * z)
      (𝓝[≠] (exp ((π / 4 : ℝ) * I) * w)) (𝓝[≠] w) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h := ((by fun_prop : Continuous fun z : ℂ ↦ exp (-((π / 4 : ℝ) * I)) * z)).tendsto
      (exp ((π / 4 : ℝ) * I) * w)
    rw [← mul_assoc, exp_neg_pi_div_four_mul_I_mul_exp, one_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
    exact fun hcon ↦
      hz (by rw [← hcon, ← mul_assoc, exp_pi_div_four_mul_I_mul_exp_neg, one_mul])
theorem tendsto_sub_mul_rotatedFun {f : ℂ → ℂ} {n : ℤ} {R : ℂ}
    (h : Tendsto (fun x ↦ (x - n) * f x) (𝓝[≠] (n : ℂ)) (𝓝 R)) :
    Tendsto (fun z ↦ (z - exp ((π / 4 : ℝ) * I) * n) * rotatedFun f z)
      (𝓝[≠] (exp ((π / 4 : ℝ) * I) * (n : ℂ))) (𝓝 R) := by
  refine Tendsto.congr (fun z ↦ ?_)
    (h.comp (tendsto_nhdsWithin_exp_neg_pi_div_four_mul_I (n : ℂ)))
  simp only [Function.comp_apply, rotatedFun]
  linear_combination (f (exp (-((π / 4 : ℝ) * I)) * z) * (n : ℂ)) *
    exp_neg_pi_div_four_mul_I_mul_exp
noncomputable def rotatedIntegrand (s : ℂ) : ℂ → ℂ := rotatedFun (integrand s)
theorem rotatedIntegrand_exp_mul (s x : ℂ) :
    rotatedIntegrand s (exp ((π / 4 : ℝ) * I) * x) = exp (-((π / 4 : ℝ) * I)) * integrand s x :=
  rotatedFun_exp_mul _ _
theorem differentiableAt_integrand (s : ℂ) {x : ℂ} (hx : exp ((π / 4 : ℝ) * I) * x ∈ slitPlane)
    (hn : ∀ n : ℤ, x ≠ n) : DifferentiableAt ℂ (integrand s) x :=
  (differentiableAt_slantCpow (-s) hx).mul (differentiableAt_kernel hn)
theorem differentiableAt_rotatedIntegrand (s : ℂ) {z : ℂ} (hz : 0 < z.re)
    (hn : ∀ n : ℤ, z ≠ exp ((π / 4 : ℝ) * I) * n) :
    DifferentiableAt ℂ (rotatedIntegrand s) z := by
  have hzz : exp ((π / 4 : ℝ) * I) * (exp (-((π / 4 : ℝ) * I)) * z) = z := by
    rw [← mul_assoc, exp_pi_div_four_mul_I_mul_exp_neg, one_mul]
  exact differentiableAt_rotatedFun (differentiableAt_integrand s
    (mem_slitPlane_iff.2 (Or.inl (by rwa [hzz]))) fun n hcon ↦ hn n (by rw [← hzz, hcon]))
theorem tendsto_sub_mul_integrand (s : ℂ) {n : ℤ} (hn : 0 < n) :
    Tendsto (fun x ↦ (x - n) * integrand s x) (𝓝[≠] (n : ℂ))
      (𝓝 ((n : ℂ) ^ (-s) / (2 * π * I))) := by
  have hcast : ((n : ℤ) : ℂ) = (((n : ℝ)) : ℂ) := (Complex.ofReal_intCast n).symm
  have hrpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hre : exp ((π / 4 : ℝ) * I) * ((n : ℤ) : ℂ) ∈ slitPlane := by
    refine mem_slitPlane_iff.2 (Or.inl ?_)
    rw [hcast, re_exp_pi_div_four_mul_I_mul_ofReal]
    positivity
  rw [show ((n : ℂ) ^ (-s) : ℂ) = slantCpow ((n : ℤ) : ℂ) (-s) from by
    rw [hcast]; exact (slantCpow_ofReal hrpos (-s)).symm, div_eq_mul_one_div]
  refine Tendsto.congr (fun x ↦ ?_)
    ((((differentiableAt_slantCpow (-s) hre).continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds).mul (tendsto_sub_mul_kernel n))
  rw [integrand]; ring
theorem tendsto_sub_mul_rotatedIntegrand (s : ℂ) {n : ℤ} (hn : 0 < n) :
    Tendsto (fun z ↦ (z - exp ((π / 4 : ℝ) * I) * n) * rotatedIntegrand s z)
      (𝓝[≠] (exp ((π / 4 : ℝ) * I) * n)) (𝓝 ((n : ℂ) ^ (-s) / (2 * π * I))) :=
  tendsto_sub_mul_rotatedFun (tendsto_sub_mul_integrand s hn)
theorem norm_integrand_le (s : ℂ) {x : ℂ} (hx : 0 < (exp ((π / 4 : ℝ) * I) * x).re)
    (h1 : 1 ≤ ‖x‖) (h2 : Real.sqrt 2 / 2 ≤ |x.im|) :
    ‖integrand s x‖ ≤ Real.exp (‖x‖ * |s.re| + 3 * π * |s.im| / 4 - 2 * π * x.re * x.im) := by
  have hxpos : (0 : ℝ) < ‖x‖ := by linarith
  have hx0 : x ≠ 0 := norm_pos_iff.1 hxpos
  have hsin : (1 : ℝ) ≤ ‖sin ((π : ℂ) * x)‖ := Complex.one_le_norm_sin_pi_mul h2
  have hnorm : ‖integrand s x‖
      = Real.exp (Real.log ‖x‖ * (-s).re + slantArg x * s.im) *
        (Real.exp (-(2 * π * x.re * x.im)) / (2 * ‖sin (π * x)‖)) := by
    rw [integrand, norm_mul, norm_slantCpow hx0, kernel_eq_div_two_mul_I_mul_sin, norm_div,
      Complex.norm_exp_pi_mul_I_mul_sq,
      show ‖(2 : ℂ) * I * sin ((π : ℂ) * x)‖ = 2 * ‖sin ((π : ℂ) * x)‖ by simp,
      Real.rpow_def_of_pos hxpos, Complex.neg_im, mul_neg,
      Real.exp_neg (slantArg x * s.im), div_inv_eq_mul,
      ← Real.exp_add (Real.log ‖x‖ * (-s).re) (slantArg x * s.im)]
  have hlog : Real.log ‖x‖ * (-s).re ≤ ‖x‖ * |s.re| := by
    have hre : (-s).re ≤ |s.re| := by simpa using neg_le_abs s.re
    nlinarith [Real.log_nonneg h1, Real.log_le_self hxpos.le, abs_nonneg s.re]
  have harg : slantArg x * s.im ≤ 3 * π * |s.im| / 4 := by
    have h := abs_lt.1 (abs_arg_lt_pi_div_two_iff.2 (Or.inl hx))
    have hb : |slantArg x| ≤ 3 * π / 4 := by
      rw [slantArg, abs_le]; constructor <;> linarith
    nlinarith [le_abs_self (slantArg x * s.im), abs_mul (slantArg x) s.im, abs_nonneg s.im,
      abs_nonneg (slantArg x), mul_le_mul_of_nonneg_right hb (abs_nonneg s.im)]
  rw [hnorm]
  refine le_trans (mul_le_mul_of_nonneg_left (div_le_self (Real.exp_pos _).le (by linarith))
    (Real.exp_pos _).le) ?_
  rw [← Real.exp_add]
  exact Real.exp_le_exp.2 (by linarith)
theorem le_abs_im_of_im_eq_mul {z : ℂ} {c d : ℝ} (hc : 0 ≤ c) (hz : z.im = c * d)
    (hd : 1 ≤ |d|) : c ≤ |z.im| := by
  rw [hz, abs_mul, abs_of_nonneg hc]
  exact le_mul_of_one_le_right hc hd
private theorem norm_rotatedIntegrand_le (s : ℂ) {ξ y : ℝ} (hξ : 0 < ξ) (h1 : 1 ≤ |y|)
    (h2 : 1 ≤ |y - ξ|) :
    ‖rotatedIntegrand s ((ξ : ℂ) + (y : ℂ) * I)‖
      ≤ Real.exp ((ξ + |y|) * |s.re| + 3 * π * |s.im| / 4 + π * ξ ^ 2 - π * |y| ^ 2) := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2n : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  set x : ℂ := exp (-((π / 4 : ℝ) * I)) * ((ξ : ℂ) + (y : ℂ) * I) with hxdef
  have hxre : x.re = Real.sqrt 2 / 2 * (ξ + y) := by
    rw [hxdef, exp_neg_pi_div_four_mul_I_mul_re]; simp
  have hxim : x.im = Real.sqrt 2 / 2 * (y - ξ) := by
    rw [hxdef, exp_neg_pi_div_four_mul_I_mul_im]; simp
  have hrot : exp ((π / 4 : ℝ) * I) * x = (ξ : ℂ) + (y : ℂ) * I := by
    rw [hxdef, ← mul_assoc, exp_pi_div_four_mul_I_mul_exp_neg, one_mul]
  have hnx : ‖x‖ = ‖(ξ : ℂ) + (y : ℂ) * I‖ := by
    rw [hxdef, norm_mul, norm_exp_neg_pi_div_four_mul_I, one_mul]
  have hnx1 : 1 ≤ ‖x‖ := by
    refine h1.trans (hnx ▸ ?_)
    simpa using Complex.abs_im_le_norm ((ξ : ℂ) + (y : ℂ) * I)
  have hnx2 : ‖x‖ ≤ ξ + |y| := by
    rw [hnx]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp [abs_of_pos hξ]
  have hxim2 := le_abs_im_of_im_eq_mul (by positivity) hxim h2
  have hbound := norm_integrand_le s (by rw [hrot]; simpa using hξ) hnx1 hxim2
  refine le_trans ?_ (hbound.trans (Real.exp_le_exp.2 ?_))
  · rw [rotatedIntegrand, norm_rotatedFun, ← hxdef]
  · have hprod : 2 * π * x.re * x.im = π * |y| ^ 2 - π * ξ ^ 2 := by
      rw [hxre, hxim, sq_abs]
      linear_combination (π * (y ^ 2 - ξ ^ 2) / 2) * hs2
    rw [hprod]
    nlinarith [abs_nonneg s.re]
theorem tendsto_HIntegral_of_norm_le {F : ℂ → ℂ} {β α c C₀ C₁ T : ℝ} (hβα : β ≤ α) (hc : 0 < c)
    (hb : ∀ ξ y : ℝ, β ≤ ξ → ξ ≤ α → T ≤ |y| →
      ‖F ((ξ : ℂ) + (y : ℂ) * I)‖ ≤ Real.exp (C₀ + C₁ * |y| - c * y ^ 2))
    {y : ℝ → ℝ} (hy : Tendsto (fun H ↦ |y H|) atTop atTop) :
    Tendsto (fun H ↦ HIntegral F β α (y H)) atTop (𝓝 0) := by
  have hbound : ∀ H : ℝ, T ≤ |y H| →
      ‖HIntegral F β α (y H)‖ ≤ Real.exp (C₀ + C₁ * |y H| - c * |y H| ^ 2) * |α - β| := by
    intro H hH
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun ξ hξ ↦ ?_
    rw [Set.uIoc_of_le hβα, Set.mem_Ioc] at hξ
    rw [sq_abs]
    exact hb ξ (y H) hξ.1.le hξ.2 hH
  have hφ0 : Tendsto (fun u : ℝ ↦ Real.exp (C₀ + C₁ * u - c * u ^ 2) * |α - β|) atTop (𝓝 0) := by
    have hlin : Tendsto (fun u : ℝ ↦ C₁ - c * u) atTop atBot := by
      have h1 : Tendsto (fun u : ℝ ↦ c * u) atTop atTop :=
        Filter.Tendsto.const_mul_atTop hc tendsto_id
      simpa [sub_eq_add_neg] using
        tendsto_atBot_add_const_left atTop C₁ (tendsto_neg_atTop_atBot.comp h1)
    have hquad : Tendsto (fun u : ℝ ↦ C₀ + C₁ * u - c * u ^ 2) atTop atBot := by
      refine Tendsto.congr (fun u ↦ ?_)
        (tendsto_atBot_add_const_left atTop C₀ (tendsto_id.atTop_mul_atBot₀ hlin))
      simp only [id_eq]; ring
    simpa using (Real.tendsto_exp_comp_nhds_zero.2 hquad).mul_const |α - β|
  refine squeeze_zero_norm' ?_ (hφ0.comp hy)
  filter_upwards [hy.eventually_ge_atTop T] with H hH using hbound H hH
theorem tendsto_HIntegral_rotatedIntegrand (s : ℂ) {β α : ℝ} (hβ : 0 < β) (hβα : β ≤ α)
    {y : ℝ → ℝ} (hy : Tendsto (fun H ↦ |y H|) atTop atTop) :
    Tendsto (fun H ↦ HIntegral (rotatedIntegrand s) β α (y H)) atTop (𝓝 0) := by
  refine tendsto_HIntegral_of_norm_le (C₀ := α * |s.re| + 3 * π * |s.im| / 4 + π * α ^ 2)
    (C₁ := |s.re|) (T := α + 1) hβα Real.pi_pos (fun ξ u hξ1 hξ2 hu ↦ ?_) hy
  have hξ0 : 0 < ξ := hβ.trans_le hξ1
  have h1 : 1 ≤ |u| := by linarith
  have h2 : 1 ≤ |u - ξ| := by
    linarith [abs_sub_abs_le_abs_sub u ξ, abs_of_nonneg hξ0.le]
  refine (norm_rotatedIntegrand_le s hξ0 h1 h2).trans (Real.exp_le_exp.2 ?_)
  have hsq : ξ ^ 2 ≤ α ^ 2 := by nlinarith
  rw [sq_abs]
  nlinarith [mul_le_mul_of_nonneg_right hξ2 (abs_nonneg s.re),
    mul_le_mul_of_nonneg_left hsq Real.pi_pos.le]
private theorem div_sqrt_two (x : ℝ) : x / Real.sqrt 2 = Real.sqrt 2 / 2 * x := by
  rw [div_eq_iff (Real.sqrt_pos.2 two_pos).ne']
  linear_combination (-(x / 2)) * Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
theorem VIntegral_eq_intervalIntegral_line {F f : ℂ → ℂ}
    (hF : ∀ x : ℂ, F (exp ((π / 4 : ℝ) * I) * x) = exp (-((π / 4 : ℝ) * I)) * f x) (a H : ℝ) :
    VIntegral F (a / Real.sqrt 2) (-H) H
      = (1 + I) * ∫ w in (-(H / Real.sqrt 2) - a / 2)..(H / Real.sqrt 2 - a / 2), f (line a w) := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsqC : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by exact_mod_cast hsq
  have hend1 : Real.sqrt 2 * (-(H / Real.sqrt 2) - a / 2) + a / Real.sqrt 2 = -H := by
    rw [div_sqrt_two H, div_sqrt_two a]; linear_combination (-(H / 2)) * hsq
  have hend2 : Real.sqrt 2 * (H / Real.sqrt 2 - a / 2) + a / Real.sqrt 2 = H := by
    rw [div_sqrt_two H, div_sqrt_two a]; linear_combination (H / 2) * hsq
  have hpt : ∀ w : ℝ,
      F (((a / Real.sqrt 2 : ℝ) : ℂ) + ((Real.sqrt 2 * w + a / Real.sqrt 2 : ℝ) : ℂ) * I)
        = exp (-((π / 4 : ℝ) * I)) * f (line a w) := by
    intro w
    rw [show ((a / Real.sqrt 2 : ℝ) : ℂ) + ((Real.sqrt 2 * w + a / Real.sqrt 2 : ℝ) : ℂ) * I
        = exp ((π / 4 : ℝ) * I) * line a w from by
      rw [exp_pi_div_four_mul_I_mul_line, div_sqrt_two a]; push_cast; ring, hF]
  have hsub := intervalIntegral.smul_integral_comp_mul_add
    (a := -(H / Real.sqrt 2) - a / 2) (b := H / Real.sqrt 2 - a / 2)
    (fun y : ℝ ↦ F ((a / Real.sqrt 2 : ℝ) + (y : ℝ) * I))
    (Real.sqrt 2) (a / Real.sqrt 2)
  rw [hend1, hend2] at hsub
  rw [VIntegral, ← hsub]
  simp only [hpt, intervalIntegral.integral_const_mul, Complex.real_smul, smul_eq_mul]
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  rw [exp_neg_pi_div_four_mul_I]
  push_cast
  linear_combination ((I + 1) / 2) * hsqC - (((Real.sqrt 2 : ℝ) : ℂ) ^ 2 / 2) * Complex.I_sq
theorem tendsto_VIntegral_nhds_slantIntegral {F f : ℂ → ℂ}
    (hF : ∀ x : ℂ, F (exp ((π / 4 : ℝ) * I) * x) = exp (-((π / 4 : ℝ) * I)) * f x) {a : ℝ}
    (hint : Integrable fun w : ℝ ↦ f (line a w)) :
    Tendsto (fun H : ℝ ↦ VIntegral F (a / Real.sqrt 2) (-H) H) atTop (𝓝 (slantIntegral f a)) := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hdiv : Tendsto (fun H : ℝ ↦ H / Real.sqrt 2) atTop atTop :=
    tendsto_id.atTop_div_const hs2
  simp only [VIntegral_eq_intervalIntegral_line hF, slantIntegral]
  refine Filter.Tendsto.const_mul _
    (MeasureTheory.intervalIntegral_tendsto_integral hint ?_ ?_)
  · simpa [sub_eq_add_neg] using
      tendsto_atBot_add_const_right atTop (-(a / 2)) (tendsto_neg_atTop_atBot.comp hdiv)
  · simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-(a / 2)) hdiv
theorem tendsto_VIntegral_rotatedIntegrand (s : ℂ) {a : ℝ}
    (hint : Integrable (contourIntegrand s a)) :
    Tendsto (fun H : ℝ ↦ VIntegral (rotatedIntegrand s) (a / Real.sqrt 2) (-H) H) atTop
      (𝓝 (contourIntegral s a)) :=
  tendsto_VIntegral_nhds_slantIntegral (rotatedIntegrand_exp_mul s) hint
theorem tendsto_RectangleIntegral_of_tendsto {F : ℂ → ℂ} {β α : ℝ} {A B : ℂ}
    (h1 : Tendsto (fun H : ℝ ↦ HIntegral F β α (-H)) atTop (𝓝 0))
    (h2 : Tendsto (fun H : ℝ ↦ HIntegral F β α H) atTop (𝓝 0))
    (h3 : Tendsto (fun H : ℝ ↦ VIntegral F α (-H) H) atTop (𝓝 A))
    (h4 : Tendsto (fun H : ℝ ↦ VIntegral F β (-H) H) atTop (𝓝 B)) :
    Tendsto (fun H : ℝ ↦ RectangleIntegral F ((β : ℂ) - (H : ℂ) * I) ((α : ℂ) + (H : ℂ) * I))
      atTop (𝓝 (A - B)) := by
  have h5 := ((h1.sub h2).add h3).sub h4
  simp only [sub_zero, zero_add] at h5
  refine Tendsto.congr (fun H ↦ ?_) h5
  simp [RectangleIntegral]
theorem tendsto_RectangleIntegral_rotatedIntegrand (s : ℂ) {a b : ℝ} (hb0 : 0 < b / Real.sqrt 2)
    (hba : b / Real.sqrt 2 ≤ a / Real.sqrt 2) (hia : Integrable (contourIntegrand s a))
    (hib : Integrable (contourIntegrand s b)) :
    Tendsto (fun H : ℝ ↦ RectangleIntegral (rotatedIntegrand s)
      (((b / Real.sqrt 2 : ℝ) : ℂ) - (H : ℂ) * I) (((a / Real.sqrt 2 : ℝ) : ℂ) + (H : ℂ) * I))
      atTop (𝓝 (contourIntegral s a - contourIntegral s b)) :=
  tendsto_RectangleIntegral_of_tendsto
    (tendsto_HIntegral_rotatedIntegrand s hb0 hba (y := fun H : ℝ ↦ -H)
      (by simpa using tendsto_abs_atTop_atTop))
    (tendsto_HIntegral_rotatedIntegrand s hb0 hba (y := fun H : ℝ ↦ H) tendsto_abs_atTop_atTop)
    (tendsto_VIntegral_rotatedIntegrand s hia) (tendsto_VIntegral_rotatedIntegrand s hib)
theorem slantIntegral_sub_slantIntegral_of_pole {f F : ℂ → ℂ} {n : ℤ} {R : ℂ} (hn : 0 < n)
    (hF : ∀ x : ℂ, F (exp ((π / 4 : ℝ) * I) * x) = exp (-((π / 4 : ℝ) * I)) * f x)
    (hdiff : ∀ z : ℂ, 0 < z.re → (∀ k : ℤ, z ≠ exp ((π / 4 : ℝ) * I) * k) →
      DifferentiableAt ℂ F z)
    (hpole : Tendsto (fun z ↦ (z - exp ((π / 4 : ℝ) * I) * n) * F z)
      (𝓝[≠] (exp ((π / 4 : ℝ) * I) * (n : ℂ))) (𝓝 R))
    (hH1 : Tendsto (fun H : ℝ ↦ HIntegral F (((n : ℝ) - 1 / 2) / Real.sqrt 2)
      (((n : ℝ) + 1 / 2) / Real.sqrt 2) (-H)) atTop (𝓝 0))
    (hH2 : Tendsto (fun H : ℝ ↦ HIntegral F (((n : ℝ) - 1 / 2) / Real.sqrt 2)
      (((n : ℝ) + 1 / 2) / Real.sqrt 2) H) atTop (𝓝 0))
    (hia : Integrable fun w : ℝ ↦ f (line ((n : ℝ) + 1 / 2) w))
    (hib : Integrable fun w : ℝ ↦ f (line ((n : ℝ) - 1 / 2) w)) :
    slantIntegral f ((n : ℝ) + 1 / 2) - slantIntegral f ((n : ℝ) - 1 / 2) = 2 * π * I * R := by
  have hpiC : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hlt2 : Real.sqrt 2 < 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hcast : ((n : ℤ) : ℂ) = (((n : ℝ)) : ℂ) := (Complex.ofReal_intCast n).symm
  set b : ℝ := (n : ℝ) - 1 / 2 with hbdef
  set a : ℝ := (n : ℝ) + 1 / 2 with hadef
  have hb0 : 0 < b := by rw [hbdef]; linarith
  have hβ0 : 0 < b / Real.sqrt 2 := div_pos hb0 hs2
  have hβα : b / Real.sqrt 2 < a / Real.sqrt 2 := by
    rw [div_lt_div_iff_of_pos_right hs2, hbdef, hadef]; linarith
  set p : ℂ := exp ((π / 4 : ℝ) * I) * (n : ℂ) with hpdef
  have hpre : p.re = (n : ℝ) / Real.sqrt 2 := by
    rw [hpdef, hcast, re_exp_pi_div_four_mul_I_mul_ofReal]
  have hpim : p.im = (n : ℝ) / Real.sqrt 2 := by
    rw [hpdef, hcast, exp_pi_div_four_mul_I, div_sqrt_two]
    simp [Complex.mul_im]
  have hstrip : ∀ k : ℤ, b / Real.sqrt 2 ≤ (exp ((π / 4 : ℝ) * I) * (k : ℂ)).re →
      (exp ((π / 4 : ℝ) * I) * (k : ℂ)).re ≤ a / Real.sqrt 2 → k = n := by
    intro k h1 h2
    rw [← Complex.ofReal_intCast k,
      re_exp_pi_div_four_mul_I_mul_ofReal, div_le_div_iff_of_pos_right hs2] at h1 h2
    rw [hbdef] at h1
    rw [hadef] at h2
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hk : ((k : ℝ)) + 1 ≤ (n : ℝ) := by exact_mod_cast Int.add_one_le_iff.2 h
      linarith
    · have hk : ((n : ℝ)) + 1 ≤ (k : ℝ) := by exact_mod_cast Int.add_one_le_iff.2 h
      linarith
  have key : ∀ᶠ H : ℝ in atTop,
      RectangleIntegral F (((b / Real.sqrt 2 : ℝ) : ℂ) - (H : ℂ) * I)
          (((a / Real.sqrt 2 : ℝ) : ℂ) + (H : ℂ) * I) = 2 * π * I * R := by
    filter_upwards [eventually_gt_atTop ((n : ℝ) / Real.sqrt 2)] with H hH
    set z : ℂ := ((b / Real.sqrt 2 : ℝ) : ℂ) - (H : ℂ) * I with hzdef
    set w : ℂ := ((a / Real.sqrt 2 : ℝ) : ℂ) + (H : ℂ) * I with hwdef
    have hzre : z.re = b / Real.sqrt 2 := by rw [hzdef]; simp
    have hzim : z.im = -H := by rw [hzdef]; simp
    have hwre : w.re = a / Real.sqrt 2 := by rw [hwdef]; simp
    have hwim : w.im = H := by rw [hwdef]; simp
    have hH0 : 0 < H := lt_trans (by positivity) hH
    have hzw1 : z.re ≤ w.re := by rw [hzre, hwre]; exact hβα.le
    have hzw2 : z.im ≤ w.im := by rw [hzim, hwim]; linarith
    have hnhds : Rectangle z w ∈ 𝓝 p := by
      have hHn : (0 : ℝ) < (n : ℝ) / Real.sqrt 2 := by positivity
      rw [rectangle_mem_nhds_iff, Complex.mem_reProdIm, hzre, hzim, hwre, hwim,
        Set.uIoo_of_le hβα.le, Set.uIoo_of_le (by linarith : (-H : ℝ) ≤ H),
        Set.mem_Ioo, Set.mem_Ioo, hpre, hpim]
      refine ⟨⟨?_, ?_⟩, by linarith, hH⟩
      · rw [div_lt_div_iff_of_pos_right hs2, hbdef]; linarith
      · rw [div_lt_div_iff_of_pos_right hs2, hadef]; linarith
    have hrect : HolomorphicOn F (Rectangle z w \ {p}) := by
      intro ζ hζ
      obtain ⟨hr1, hr2, -, -⟩ := (mem_Rect hzw1 hzw2 ζ).1 hζ.1
      rw [hzre] at hr1
      rw [hwre] at hr2
      refine (hdiff ζ (lt_of_lt_of_le hβ0 hr1) ?_).differentiableWithinAt
      intro k hk
      refine hζ.2 (Set.mem_singleton_iff.2 ?_)
      rw [hk, hstrip k (by rw [← hk]; exact hr1) (by rw [← hk]; exact hr2), ← hpdef]
    have hballholo : HolomorphicOn F (Metric.ball p (1 / 2) \ {p}) := by
      intro ζ hζ
      have hd : ‖ζ - p‖ < 1 / 2 := by simpa [Complex.dist_eq] using Metric.mem_ball.1 hζ.1
      refine (hdiff ζ ?_ ?_).differentiableWithinAt
      · have h2 : p.re - ζ.re ≤ ‖ζ - p‖ := by
          linarith [neg_le_of_abs_le (Complex.abs_re_le_norm (ζ - p)), Complex.sub_re ζ p]
        have h4 : (1 : ℝ) / Real.sqrt 2 ≤ (n : ℝ) / Real.sqrt 2 := by gcongr
        have h5 : (1 : ℝ) / 2 < 1 / Real.sqrt 2 := by rw [lt_div_iff₀ hs2]; linarith
        rw [hpre] at h2
        linarith
      · intro k hk
        have hne : k ≠ n := fun h ↦ hζ.2 (Set.mem_singleton_iff.2 (by rw [hk, h, hpdef]))
        have h1 : (1 : ℝ) ≤ ‖(k : ℂ) - (n : ℂ)‖ := by
          rw [← Int.cast_sub k n, Complex.norm_intCast]
          exact_mod_cast Int.one_le_abs (sub_ne_zero.2 hne)
        have h2 : ‖ζ - p‖ = ‖(k : ℂ) - (n : ℂ)‖ := by
          rw [hk, hpdef, ← mul_sub, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
        linarith
    obtain ⟨V, hV, hbdd⟩ :=
      ResidueOfTendsTo (Metric.ball_mem_nhds p (by norm_num)) hballholo hpole
    obtain ⟨C, hC⟩ := hbdd
    have hnear : (F - fun t ↦ R / (t - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
      refine Asymptotics.isBigO_iff.2 ⟨C, ?_⟩
      filter_upwards [mem_nhdsWithin_of_mem_nhds hV, self_mem_nhdsWithin] with ζ h1 h2
      simpa [div_eq_mul_inv] using hC ⟨ζ, ⟨h1, h2⟩, rfl⟩
    have hres := ResidueTheoremOnRectangleWithSimplePole' hzw1 hzw2 hnhds hrect hnear
    rw [RectangleIntegral', smul_eq_mul] at hres
    field_simp at hres
    linear_combination hres
  have hlim := tendsto_RectangleIntegral_of_tendsto hH1 hH2
    (tendsto_VIntegral_nhds_slantIntegral hF hia) (tendsto_VIntegral_nhds_slantIntegral hF hib)
  have hconst : Tendsto (fun H : ℝ ↦ RectangleIntegral F
      (((b / Real.sqrt 2 : ℝ) : ℂ) - (H : ℂ) * I) (((a / Real.sqrt 2 : ℝ) : ℂ) + (H : ℂ) * I))
      atTop (𝓝 (2 * π * I * R)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [key] with H hH using hH.symm
  exact (tendsto_nhds_unique hconst hlim).symm
theorem contourIntegral_sub_contourIntegral_eq_cpow_neg (s : ℂ) {n : ℤ} (hn : 0 < n) :
    contourIntegral s ((n : ℝ) + 1 / 2) - contourIntegral s ((n : ℝ) - 1 / 2)
      = (n : ℂ) ^ (-s) := by
  have hpiC : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hb0 : 0 < (n : ℝ) - 1 / 2 := by linarith
  have ha0 : 0 < (n : ℝ) + 1 / 2 := by linarith
  have hβ0 : 0 < ((n : ℝ) - 1 / 2) / Real.sqrt 2 := div_pos hb0 hs2
  have hβα : ((n : ℝ) - 1 / 2) / Real.sqrt 2 ≤ ((n : ℝ) + 1 / 2) / Real.sqrt 2 := by
    rw [div_le_div_iff_of_pos_right hs2]; linarith
  have hbhalf : (n : ℝ) - 1 / 2 = ((n - 1 : ℤ) : ℝ) + 1 / 2 := by push_cast; ring
  have hahalf : (n : ℝ) + 1 / 2 = ((n : ℤ) : ℝ) + 1 / 2 := rfl
  have hkey := slantIntegral_sub_slantIntegral_of_pole (f := integrand s) hn
    (rotatedIntegrand_exp_mul s) (fun z hz hk ↦ differentiableAt_rotatedIntegrand s hz hk)
    (tendsto_sub_mul_rotatedIntegrand s hn)
    (tendsto_HIntegral_rotatedIntegrand s hβ0 hβα (y := fun H : ℝ ↦ -H)
      (by simpa using tendsto_abs_atTop_atTop))
    (tendsto_HIntegral_rotatedIntegrand s hβ0 hβα (y := fun H : ℝ ↦ H) tendsto_abs_atTop_atTop)
    (integrable_contourIntegrand s ha0 (by positivity) (norm_sin_pi_mul_line_ge hahalf))
    (integrable_contourIntegrand s hb0 (by positivity) (norm_sin_pi_mul_line_ge hbhalf))
  rw [contourIntegral_eq_slantIntegral, contourIntegral_eq_slantIntegral, hkey]
  field_simp
theorem contourIntegral_sub_contourIntegral_eq_sum_cpow_neg (s : ℂ) {j k : ℕ} (hjk : j ≤ k) :
    contourIntegral s ((k : ℝ) + 1 / 2) - contourIntegral s ((j : ℝ) + 1 / 2)
      = ∑ i ∈ Finset.Ioc j k, (i : ℂ) ^ (-s) := by
  induction k, hjk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hstep :=
      contourIntegral_sub_contourIntegral_eq_cpow_neg s (n := (k : ℤ) + 1) (by positivity)
    push_cast at hstep
    rw [show ((k : ℝ) + 1 - 1 / 2) = (k : ℝ) + 1 / 2 from by ring] at hstep
    rw [Finset.sum_Ioc_succ_top hk, ← ih]
    push_cast
    linear_combination hstep
theorem sum_cpow_neg_eq_contourIntegral_sub_contourIntegral (s : ℂ) (k : ℕ) :
    ∑ i ∈ Finset.Icc 1 k, (i : ℂ) ^ (-s)
      = contourIntegral s ((k : ℝ) + 1 / 2) - contourIntegral s (1 / 2) := by
  have h := contourIntegral_sub_contourIntegral_eq_sum_cpow_neg s (Nat.zero_le k)
  rw [Nat.cast_zero, zero_add] at h
  rw [show Finset.Icc 1 k = Finset.Ioc 0 k from Finset.Icc_succ_left_eq_Ioc _ _]
  exact h.symm
end Zeta.RiemannSiegel
end
end CertificatePort106


section CertificatePort107
section
open Complex Filter MeasureTheory Topology
open scoped Real
namespace Zeta.RiemannSiegel
noncomputable def rotatedModelFun (p : ℂ) : ℂ → ℂ := rotatedFun (modelFun p)
theorem rotatedModelFun_exp_mul (p x : ℂ) :
    rotatedModelFun p (exp ((π / 4 : ℝ) * I) * x) = exp (-((π / 4 : ℝ) * I)) * modelFun p x :=
  rotatedFun_exp_mul _ _
theorem differentiableAt_modelFun (p : ℂ) {x : ℂ} (hx : ∀ n : ℤ, x ≠ n) :
    DifferentiableAt ℂ (modelFun p) x := by
  rw [funext (modelFun_eq_mul_kernel p)]
  exact (by fun_prop : DifferentiableAt ℂ
    (fun x : ℂ ↦ exp (2 * π * I * (x - p) ^ 2 - π * I * x ^ 2)) x).mul (differentiableAt_kernel hx)
theorem differentiableAt_rotatedModelFun (p : ℂ) {z : ℂ}
    (hz : ∀ k : ℤ, z ≠ exp ((π / 4 : ℝ) * I) * k) : DifferentiableAt ℂ (rotatedModelFun p) z :=
  differentiableAt_rotatedFun (differentiableAt_modelFun p fun k hcon ↦ hz k (by
    rw [← hcon, ← mul_assoc, exp_pi_div_four_mul_I_mul_exp_neg, one_mul]))
theorem tendsto_sub_mul_modelFun (p : ℂ) (n : ℤ) :
    Tendsto (fun x ↦ (x - n) * modelFun p x) (𝓝[≠] (n : ℂ))
      (𝓝 (exp (2 * π * I * ((n : ℂ) - p) ^ 2 - π * I * (n : ℂ) ^ 2) / (2 * π * I))) := by
  have hcont : Tendsto (fun x : ℂ ↦ exp (2 * π * I * (x - p) ^ 2 - π * I * x ^ 2))
      (𝓝[≠] (n : ℂ)) (𝓝 (exp (2 * π * I * ((n : ℂ) - p) ^ 2 - π * I * (n : ℂ) ^ 2))) :=
    ((by fun_prop : Continuous fun x : ℂ ↦
      exp (2 * π * I * (x - p) ^ 2 - π * I * x ^ 2)).tendsto _).mono_left nhdsWithin_le_nhds
  rw [div_eq_mul_one_div]
  refine Tendsto.congr (fun x ↦ ?_) (hcont.mul (tendsto_sub_mul_kernel n))
  rw [modelFun_eq_mul_kernel]
  ring
theorem tendsto_sub_mul_rotatedModelFun (p : ℂ) (n : ℤ) :
    Tendsto (fun z ↦ (z - exp ((π / 4 : ℝ) * I) * n) * rotatedModelFun p z)
      (𝓝[≠] (exp ((π / 4 : ℝ) * I) * (n : ℂ)))
      (𝓝 (exp (2 * π * I * ((n : ℂ) - p) ^ 2 - π * I * (n : ℂ) ^ 2) / (2 * π * I))) :=
  tendsto_sub_mul_rotatedFun (tendsto_sub_mul_modelFun p n)
private theorem norm_rotatedModelFun_le (p : ℂ) {ξ y : ℝ} (h : 1 ≤ |y - ξ|) :
    ‖rotatedModelFun p ((ξ : ℂ) + (y : ℂ) * I)‖
      ≤ Real.exp (2 * π * ξ ^ 2 - 2 * π * y ^ 2
        + 2 * Real.sqrt 2 * π * (|ξ| + |y|) * (|p.re| + |p.im|) + 4 * π * |p.re| * |p.im|) := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  set x : ℂ := exp (-((π / 4 : ℝ) * I)) * ((ξ : ℂ) + (y : ℂ) * I) with hxdef
  have hxre : x.re = Real.sqrt 2 / 2 * (ξ + y) := by
    rw [hxdef, exp_neg_pi_div_four_mul_I_mul_re]; simp
  have hxim : x.im = Real.sqrt 2 / 2 * (y - ξ) := by
    rw [hxdef, exp_neg_pi_div_four_mul_I_mul_im]; simp
  have hxim2 := le_abs_im_of_im_eq_mul (by positivity) hxim h
  have hnorm : ‖rotatedModelFun p ((ξ : ℂ) + (y : ℂ) * I)‖ = ‖modelFun p x‖ := by
    rw [rotatedModelFun, norm_rotatedFun, ← hxdef]
  have hbound : ‖modelFun p x‖ ≤ Real.exp (-(4 * π * (x.re - p.re) * (x.im - p.im))) := by
    refine (norm_modelFun_le p one_pos (Complex.one_le_norm_sin_pi_mul hxim2)).trans ?_
    rw [Complex.norm_exp_two_pi_mul_I_mul_sq, Complex.sub_re, Complex.sub_im]
    exact div_le_self (Real.exp_pos _).le (by norm_num)
  have hid : -(4 * π * (Real.sqrt 2 / 2 * (ξ + y) - p.re) * (Real.sqrt 2 / 2 * (y - ξ) - p.im))
      = 2 * π * ξ ^ 2 - 2 * π * y ^ 2
        + 2 * Real.sqrt 2 * π * ((ξ + y) * p.im + (y - ξ) * p.re) - 4 * π * (p.re * p.im) := by
    linear_combination (-(π * (y ^ 2 - ξ ^ 2))) * hs2
  have hA : (ξ + y) * p.im + (y - ξ) * p.re ≤ (|ξ| + |y|) * (|p.re| + |p.im|) := by
    have h1 : (ξ + y) * p.im ≤ (|ξ| + |y|) * |p.im| :=
      (le_abs_self _).trans (by rw [abs_mul]; gcongr; exact abs_add_le ξ y)
    have h2 : (y - ξ) * p.re ≤ (|ξ| + |y|) * |p.re| :=
      (le_abs_self _).trans (by
        rw [abs_mul]; gcongr; simpa [sub_eq_add_neg, add_comm] using abs_add_le y (-ξ))
    nlinarith [abs_nonneg p.re, abs_nonneg p.im, abs_nonneg ξ, abs_nonneg y]
  have hB : -(p.re * p.im) ≤ |p.re| * |p.im| := by
    rw [← abs_mul]
    exact neg_le_abs _
  rw [hnorm]
  refine hbound.trans (Real.exp_le_exp.2 ?_)
  rw [hxre, hxim, hid]
  nlinarith [mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt 2 * π),
    mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ 4 * π)]
theorem tendsto_HIntegral_rotatedModelFun (p : ℂ) {β α : ℝ} (hβ : 0 ≤ β) (hβα : β ≤ α)
    {y : ℝ → ℝ} (hy : Tendsto (fun H ↦ |y H|) atTop atTop) :
    Tendsto (fun H ↦ HIntegral (rotatedModelFun p) β α (y H)) atTop (𝓝 0) := by
  have hK : (0 : ℝ) ≤ |p.re| + |p.im| := by positivity
  refine tendsto_HIntegral_of_norm_le
    (C₀ := 2 * π * α ^ 2 + 2 * Real.sqrt 2 * π * (α * (|p.re| + |p.im|)) + 4 * π * |p.re| * |p.im|)
    (C₁ := 2 * Real.sqrt 2 * π * (|p.re| + |p.im|)) (c := 2 * π) (T := α + 1) hβα (by positivity)
    (fun ξ u hξ1 hξ2 hu ↦ ?_) hy
  have hξ0 : 0 ≤ ξ := hβ.trans hξ1
  have h1 : 1 ≤ |u - ξ| := by
    linarith [abs_sub_abs_le_abs_sub u ξ, abs_of_nonneg hξ0]
  refine (norm_rotatedModelFun_le p h1).trans (Real.exp_le_exp.2 ?_)
  have hsq : ξ ^ 2 ≤ α ^ 2 := by nlinarith
  have hstep : 2 * Real.sqrt 2 * π * (ξ * (|p.re| + |p.im|))
      ≤ 2 * Real.sqrt 2 * π * (α * (|p.re| + |p.im|)) := by
    have h := mul_le_mul_of_nonneg_right hξ2 hK
    exact mul_le_mul_of_nonneg_left h (by positivity)
  rw [abs_of_nonneg hξ0]
  nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 2 * π)]
theorem modelIntegral_add_modelIntegral_add_one (p : ℂ) :
    modelIntegral p (1 / 2) + modelIntegral (p + 1) (1 / 2) = exp (2 * π * I * p ^ 2) := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hpi' : exp (-((π : ℂ) * I)) = -1 := by rw [exp_neg, exp_pi_mul_I]; norm_num
  have hcross : ∀ q : ℂ, modelIntegral q (3 / 2) - modelIntegral q (1 / 2)
      = -exp (2 * π * I * (1 - q) ^ 2) := by
    intro q
    have hβ : (0 : ℝ) ≤ (((1 : ℤ) : ℝ) - 1 / 2) / Real.sqrt 2 := by push_cast; positivity
    have hβα : (((1 : ℤ) : ℝ) - 1 / 2) / Real.sqrt 2 ≤ (((1 : ℤ) : ℝ) + 1 / 2) / Real.sqrt 2 := by
      rw [div_le_div_iff_of_pos_right hs2]; push_cast; linarith
    have hkey := slantIntegral_sub_slantIntegral_of_pole (f := modelFun q)
      (F := rotatedModelFun q) (n := 1) one_pos (rotatedModelFun_exp_mul q)
      (fun z _ hz ↦ differentiableAt_rotatedModelFun q hz)
      (tendsto_sub_mul_rotatedModelFun q 1)
      (tendsto_HIntegral_rotatedModelFun q hβ hβα (by simpa using tendsto_abs_atTop_atTop))
      (tendsto_HIntegral_rotatedModelFun q hβ hβα tendsto_abs_atTop_atTop)
      (integrable_modelIntegrand q (a := ((1 : ℤ) : ℝ) + 1 / 2) (n := 1) rfl)
      (integrable_modelIntegrand q (a := ((1 : ℤ) : ℝ) - 1 / 2) (n := 0) (by push_cast; ring))
    push_cast at hkey
    rw [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num,
      show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hkey
    rw [modelIntegral_eq_slantIntegral, modelIntegral_eq_slantIntegral, hkey,
      show 2 * (π : ℂ) * I * (1 - q) ^ 2 - π * I * 1 ^ 2
        = 2 * π * I * (1 - q) ^ 2 + -(π * I) by ring, exp_add, hpi']
    field_simp
  have htrans : ∀ q : ℂ, modelIntegral q (3 / 2) = -modelIntegral (q - 1) (1 / 2) := by
    intro q
    have hpt : ∀ w : ℝ, modelIntegrand q (3 / 2) w = -modelIntegrand (q - 1) (1 / 2) w := by
      intro w
      rw [modelIntegrand, modelIntegrand, show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, line_add_one,
        modelFun_add_one]
    rw [modelIntegral, modelIntegral]
    simp only [hpt]
    rw [integral_neg]
    ring
  have h := hcross (p + 1)
  rw [htrans (p + 1), show p + 1 - 1 = p by ring] at h
  rw [show (2 : ℂ) * π * I * p ^ 2 = 2 * π * I * (1 - (p + 1)) ^ 2 by ring]
  linear_combination -h
end Zeta.RiemannSiegel
end
end CertificatePort107


section CertificatePort108
section
open Complex
open scoped Real
namespace Zeta.RiemannSiegel
theorem two_mul_cos_mul_modelIntegral (p : ℂ) :
    2 * cos (2 * π * p) * modelIntegral p (1 / 2)
      = exp (2 * π * I * (p ^ 2 - p))
        + (Real.sqrt 2 : ℂ) * exp ((5 * π / 8 : ℝ) * I) * sin (π * p) := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsinv : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = ((Real.sqrt 2 : ℝ) : ℂ) / 2 := by
    rw [inv_eq_one_div, div_eq_div_iff (ofReal_ne_zero.2 (by positivity)) two_ne_zero]
    linear_combination -hs
  have h1 := modelIntegral_add_half p
  have h2 := modelIntegral_add_half (p + 1 / 2)
  have h3 := modelIntegral_add_modelIntegral_add_one p
  rw [show p + 1 / 2 + 1 / 2 = p + 1 by ring] at h2
  have h2p : exp (2 * (π : ℂ) * I * p) = exp ((π : ℂ) * I * p) ^ 2 := by
    rw [sq, ← exp_add]; congr 1; ring
  have e1 : exp (2 * (π : ℂ) * I * (p + 1 / 2)) = -exp ((π : ℂ) * I * p) ^ 2 := by
    rw [show 2 * (π : ℂ) * I * (p + 1 / 2) = 2 * π * I * p + π * I by ring, exp_add, exp_pi_mul_I,
      h2p]; ring
  have e2 : exp ((π : ℂ) * I * (p + 1 / 2)) = I * exp ((π : ℂ) * I * p) := by
    rw [show (π : ℂ) * I * (p + 1 / 2) = π * I * p + (π : ℂ) / 2 * I by ring, exp_add,
      exp_pi_div_two_mul_I]; ring
  rw [e1, e2] at h2
  rw [h2p] at h1
  set E : ℂ := exp ((π : ℂ) * I * p) with hEdef
  have hE0 : E ≠ 0 := exp_ne_zero _
  have hkey : (1 + E ^ 4) * modelIntegral p (1 / 2)
      = exp (2 * (π : ℂ) * I * p ^ 2)
        + E ^ 3 * exp ((π / 8 : ℝ) * I) * (((Real.sqrt 2 : ℝ) : ℂ) / 2)
        - exp ((π / 8 : ℝ) * I) * E * (((Real.sqrt 2 : ℝ) : ℂ) / 2) := by
    linear_combination h3 - h2 + (I * E ^ 2) * h1
      + (E ^ 3 * exp ((π / 8 : ℝ) * I) - exp ((π / 8 : ℝ) * I) * E) * hsinv
      + (E ^ 4 * modelIntegral p (1 / 2) + (exp ((π / 8 : ℝ) * I) * E
        - E ^ 3 * exp ((π / 8 : ℝ) * I)) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * Complex.I_sq
  have hDE : exp (-(2 * (π : ℂ) * I * p)) * E ^ 2 = 1 := by
    rw [← h2p, ← exp_add, neg_add_cancel, exp_zero]
  have hFE : exp (-((π : ℂ) * I * p)) * E = 1 := by
    rw [hEdef, ← exp_add, neg_add_cancel, exp_zero]
  have hcosE : 2 * cos (2 * (π : ℂ) * p) * E ^ 2 = E ^ 4 + 1 := by
    rw [Complex.two_cos, show 2 * (π : ℂ) * p * I = 2 * π * I * p by ring,
      show -(2 * (π : ℂ) * p) * I = -(2 * π * I * p) by ring, h2p]
    linear_combination hDE
  have hsinE : 2 * sin ((π : ℂ) * p) * E ^ 2 = (E - E ^ 3) * I := by
    have h := Complex.two_sin ((π : ℂ) * p)
    rw [show (π : ℂ) * p * I = π * I * p by ring,
      show -((π : ℂ) * p) * I = -((π : ℂ) * I * p) by ring, ← hEdef] at h
    rw [show 2 * sin ((π : ℂ) * p) * E ^ 2 = (2 * sin ((π : ℂ) * p)) * E ^ 2 by ring, h]
    linear_combination (E * I) * hFE
  have hQE : exp (2 * (π : ℂ) * I * (p ^ 2 - p)) * E ^ 2 = exp (2 * (π : ℂ) * I * p ^ 2) := by
    rw [← h2p, ← exp_add]; congr 1; ring
  have h5 : exp ((5 * π / 8 : ℝ) * I) = I * exp ((π / 8 : ℝ) * I) := by
    rw [show ((5 * π / 8 : ℝ) : ℂ) * I = (π : ℂ) / 2 * I + ((π / 8 : ℝ) : ℂ) * I by
      push_cast; ring, exp_add, exp_pi_div_two_mul_I]
  refine mul_right_cancel₀ (pow_ne_zero 2 hE0) ?_
  linear_combination (modelIntegral p (1 / 2)) * hcosE + hkey - hQE
    - (((Real.sqrt 2 : ℝ) : ℂ) * I * exp ((π / 8 : ℝ) * I) / 2) * hsinE
    - (((Real.sqrt 2 : ℝ) : ℂ) * sin ((π : ℂ) * p) * E ^ 2) * h5
    - (((Real.sqrt 2 : ℝ) : ℂ) * exp ((π / 8 : ℝ) * I) * (E - E ^ 3) / 2) * Complex.I_sq
theorem cos_mul_correction (p : ℝ) :
    Real.cos (2 * π * p) * correction p = Real.cos (2 * π * (p ^ 2 - p - 1 / 16)) := by
  have hG : exp (-((π / 8 : ℝ) * I)) * ((Real.sqrt 2 : ℂ) * exp ((5 * π / 8 : ℝ) * I))
      = (Real.sqrt 2 : ℂ) * I := by
    rw [show exp (-(((π / 8 : ℝ) : ℂ) * I)) * ((Real.sqrt 2 : ℂ) * exp (((5 * π / 8 : ℝ) : ℂ) * I))
        = (Real.sqrt 2 : ℂ) *
          (exp (-(((π / 8 : ℝ) : ℂ) * I)) * exp (((5 * π / 8 : ℝ) : ℂ) * I)) by ring,
      ← exp_add, show -(((π / 8 : ℝ) : ℂ) * I) + ((5 * π / 8 : ℝ) : ℂ) * I = (π : ℂ) / 2 * I by
        push_cast; ring, exp_pi_div_two_mul_I]
  have hQ : exp (-((π / 8 : ℝ) * I)) * exp (2 * (π : ℂ) * I * ((p : ℂ) ^ 2 - (p : ℂ)))
      = exp (((2 * π * (p ^ 2 - p - 1 / 16) : ℝ) : ℂ) * I) := by
    rw [← exp_add]; congr 1; push_cast; ring
  have key : 2 * ((Real.cos (2 * π * p) : ℝ) : ℂ) *
      (exp (-((π / 8 : ℝ) * I)) * modelIntegral (p : ℂ) (1 / 2))
      = exp (((2 * π * (p ^ 2 - p - 1 / 16) : ℝ) : ℂ) * I)
        + (Real.sqrt 2 : ℂ) * I * ((Real.sin (π * p) : ℝ) : ℂ) := by
    have h := two_mul_cos_mul_modelIntegral (p : ℂ)
    rw [show (2 : ℂ) * π * (p : ℂ) = ((2 * π * p : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
      show ((π : ℂ)) * (p : ℂ) = ((π * p : ℝ) : ℂ) by push_cast; ring, ← ofReal_sin] at h
    linear_combination exp (-((π / 8 : ℝ) * I)) * h + hQ +
      ((Real.sin (π * p) : ℝ) : ℂ) * hG
  have hL : (2 * ((Real.cos (2 * π * p) : ℝ) : ℂ) *
      (exp (-((π / 8 : ℝ) * I)) * modelIntegral (p : ℂ) (1 / 2))).re
      = Real.cos (2 * π * p) * correction p := by
    rw [show (2 : ℂ) * ((Real.cos (2 * π * p) : ℝ) : ℂ)
        = ((2 * Real.cos (2 * π * p) : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul,
      correction]
    ring
  have hR : (exp (((2 * π * (p ^ 2 - p - 1 / 16) : ℝ) : ℂ) * I)
      + (Real.sqrt 2 : ℂ) * I * ((Real.sin (π * p) : ℝ) : ℂ)).re
      = Real.cos (2 * π * (p ^ 2 - p - 1 / 16)) := by
    rw [Complex.add_re, Complex.exp_ofReal_mul_I_re,
      show (Real.sqrt 2 : ℂ) * I * ((Real.sin (π * p) : ℝ) : ℂ)
        = ((Real.sqrt 2 * Real.sin (π * p) : ℝ) : ℂ) * I by push_cast; ring]
    simp only [Complex.mul_I_re, Complex.ofReal_im, neg_zero, add_zero]
  rw [← hL, ← hR, key]
theorem cos_two_pi_fract_sqrt_ne_zero (q : ℚ) (hq : 0 < q) :
    Real.cos (2 * Real.pi *
        (Real.sqrt ((q : ℝ) / (2 * Real.pi)) - ⌊Real.sqrt ((q : ℝ) / (2 * Real.pi))⌋₊)) ≠ 0 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi0 : Real.pi ≠ 0 := ne_of_gt hpi
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  set s : ℝ := Real.sqrt ((q : ℝ) / (2 * Real.pi)) with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hsq : s ^ 2 = (q : ℝ) / (2 * Real.pi) := Real.sq_sqrt (by positivity)
  intro hcos
  obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hcos
  have hfrac : 4 * (s - (⌊s⌋₊ : ℝ)) = 2 * (k : ℝ) + 1 := by
    refine mul_left_cancel₀ hpi0 ?_
    ring_nf
    ring_nf at hk
    linarith
  set M : ℤ := 4 * (⌊s⌋₊ : ℤ) + 2 * k + 1 with hMdef
  have hsM : s = (M : ℝ) / 4 := by
    have : (M : ℝ) = 4 * (⌊s⌋₊ : ℝ) + 2 * (k : ℝ) + 1 := by push_cast [hMdef]; ring
    rw [this]; linarith
  have hM0 : (M : ℝ) ≠ 0 := by
    intro h; rw [h] at hsM; simp at hsM; linarith
  have hpiRat : ((8 * q / (M : ℚ) ^ 2 : ℚ) : ℝ) = Real.pi := by
    have hMQ : ((M : ℚ) : ℝ) ^ 2 ≠ 0 := by push_cast; exact pow_ne_zero 2 hM0
    have h1 : (M : ℝ) ^ 2 / 16 = (q : ℝ) / (2 * Real.pi) := by rw [← hsq, hsM]; ring
    have h2 : 2 * Real.pi * ((M : ℝ) ^ 2 / 16) = (q : ℝ) := by rw [h1]; field_simp
    push_cast
    field_simp
    linarith [h2]
  exact irrational_pi ⟨8 * q / (M : ℚ) ^ 2, hpiRat⟩
theorem iteratedDeriv_three_correction (p : ℝ) :
    iteratedDeriv 3 correction p
      = 2 * (exp (-((π / 8 : ℝ) * I)) *
          iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ)).re := by
  have h2 : ∀ z : ℂ, (2 * z).re = 2 * z.re := fun z ↦ by simp
  have hM : Differentiable ℂ fun q : ℂ ↦ modelIntegral q (1 / 2) := by
    simpa only [modelMoment_zero] using
      differentiable_modelMoment 0 (by norm_num : (1 : ℝ) / 2 = (0 : ℤ) + 1 / 2)
  have hcorr : correction = fun x : ℝ ↦
      (2 * exp (-((π / 8 : ℝ) * I)) * modelIntegral (x : ℂ) (1 / 2)).re := by
    funext x
    rw [correction, mul_assoc, h2]
  rw [hcorr, (hM.const_mul (2 * exp (-((π / 8 : ℝ) * I)))).iteratedDeriv_re_of_complex 3 p,
    iteratedDeriv_const_mul_field, mul_assoc, h2]
theorem neg_iteratedDeriv_three_correction_div_eq (p : ℝ) :
    -iteratedDeriv 3 correction p / (96 * π ^ 2)
      = 2 * (exp (-((π / 8 : ℝ) * I)) *
          (-(1 / 2) * modelMoment 1 (p : ℂ) (1 / 2)
            - 2 * π * I / 3 * modelMoment 3 (p : ℂ) (1 / 2))).re := by
  have hc : (96 : ℂ) * (π : ℂ) ^ 2 = ((96 * π ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [neg_half_modelMoment_one_sub_eq (p : ℂ) (by norm_num : (1 : ℝ) / 2 = (0 : ℤ) + 1 / 2),
    iteratedDeriv_three_correction p, hc,
    show exp (-((π / 8 : ℝ) * I)) *
        (-iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ) /
          ((96 * π ^ 2 : ℝ) : ℂ))
      = -(exp (-((π / 8 : ℝ) * I)) *
          iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ)) /
            ((96 * π ^ 2 : ℝ) : ℂ) by ring, Complex.div_ofReal_re, Complex.neg_re]
  ring
private noncomputable def modelCorrection (q : ℂ) : ℂ :=
  2 * exp (-((π / 8 : ℝ) * I)) * modelIntegral q (1 / 2)
private theorem differentiable_modelCorrection : Differentiable ℂ modelCorrection := by
  have hM : Differentiable ℂ fun q : ℂ ↦ modelIntegral q (1 / 2) := by
    simpa only [modelMoment_zero] using
      differentiable_modelMoment 0 (by norm_num : (1 : ℝ) / 2 = (0 : ℤ) + 1 / 2)
  exact hM.const_mul _
private theorem correction_eq_re : correction = fun x : ℝ ↦ (modelCorrection (x : ℂ)).re := by
  funext x
  have h2 : ∀ z : ℂ, (2 * z).re = 2 * z.re := fun z ↦ by simp
  rw [correction, modelCorrection, mul_assoc, h2]
private theorem differentiable_iteratedDeriv_modelCorrection (k : ℕ) :
    Differentiable ℂ (iteratedDeriv k modelCorrection) := by
  induction k with
  | zero => simpa using differentiable_modelCorrection
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv
theorem differentiable_iteratedDeriv_correction (k : ℕ) :
    Differentiable ℝ (iteratedDeriv k correction) := by
  have hre : iteratedDeriv k (fun x : ℝ ↦ (modelCorrection (x : ℂ)).re)
      = fun x : ℝ ↦ (iteratedDeriv k modelCorrection (x : ℂ)).re :=
    funext fun x ↦ differentiable_modelCorrection.iteratedDeriv_re_of_complex k x
  rw [correction_eq_re, hre]
  exact fun x ↦
    ((differentiable_iteratedDeriv_modelCorrection k _).hasDerivAt.real_of_complex).differentiableAt
private theorem hasDerivAt_iteratedDeriv_correction (k : ℕ) (p : ℝ) :
    HasDerivAt (iteratedDeriv k correction) (iteratedDeriv (k + 1) correction p) p := by
  rw [iteratedDeriv_succ]
  exact (differentiable_iteratedDeriv_correction k p).hasDerivAt
private theorem hasDerivAt_correction (p : ℝ) :
    HasDerivAt correction (iteratedDeriv 1 correction p) p := by
  simpa only [iteratedDeriv_zero] using hasDerivAt_iteratedDeriv_correction 0 p
private theorem hasDerivAt_deriv_correction (p : ℝ) :
    HasDerivAt (iteratedDeriv 1 correction) (iteratedDeriv 2 correction p) p :=
  hasDerivAt_iteratedDeriv_correction 1 p
private theorem hasDerivAt_phase (p : ℝ) :
    HasDerivAt (fun x : ℝ ↦ 2 * π * (x ^ 2 - x - 1 / 16)) (2 * π * (2 * p - 1)) p := by
  have : HasDerivAt (fun x : ℝ ↦ x ^ 2 - x - 1 / 16) (2 * p - 1) p := by
    simpa using ((hasDerivAt_pow 2 p).sub (hasDerivAt_id p)).sub_const (1 / 16)
  simpa using this.const_mul (2 * π)
private theorem hasDerivAt_cos_two_pi (p : ℝ) :
    HasDerivAt (fun x : ℝ ↦ Real.cos (2 * π * x)) (-Real.sin (2 * π * p) * (2 * π)) p := by
  simpa using (((hasDerivAt_id p).const_mul (2 * π)).cos)
private theorem hasDerivAt_sin_two_pi (p : ℝ) :
    HasDerivAt (fun x : ℝ ↦ Real.sin (2 * π * x)) (Real.cos (2 * π * p) * (2 * π)) p := by
  simpa using (((hasDerivAt_id p).const_mul (2 * π)).sin)
theorem cos_mul_iteratedDeriv_one (p : ℝ) :
    Real.cos (2 * π * p) * iteratedDeriv 1 correction p
      = -Real.sin (2 * π * (p ^ 2 - p - 1 / 16)) * (2 * π * (2 * p - 1))
        - -Real.sin (2 * π * p) * (2 * π) * correction p := by
  have hprod : HasDerivAt (fun x : ℝ ↦ Real.cos (2 * π * x) * correction x)
      (-Real.sin (2 * π * p) * (2 * π) * correction p
        + Real.cos (2 * π * p) * iteratedDeriv 1 correction p) p :=
    (hasDerivAt_cos_two_pi p).mul (hasDerivAt_correction p)
  have hfun : (fun x : ℝ ↦ Real.cos (2 * π * x) * correction x)
      = fun x : ℝ ↦ Real.cos (2 * π * (x ^ 2 - x - 1 / 16)) := funext cos_mul_correction
  rw [hfun] at hprod
  have hu := hprod.unique (hasDerivAt_phase p).cos
  linarith [hu]
theorem cos_mul_iteratedDeriv_two (p : ℝ) :
    Real.cos (2 * π * p) * iteratedDeriv 2 correction p
      = (-Real.cos (2 * π * (p ^ 2 - p - 1 / 16)) * ((2 * π * (2 * p - 1)) * (2 * π * (2 * p - 1)))
          - Real.sin (2 * π * (p ^ 2 - p - 1 / 16)) * (4 * π))
        - 2 * (-Real.sin (2 * π * p) * (2 * π)) * iteratedDeriv 1 correction p
        - -Real.cos (2 * π * p) * ((2 * π) * (2 * π)) * correction p := by
  have hL : HasDerivAt (fun x : ℝ ↦ Real.cos (2 * π * x) * iteratedDeriv 1 correction x)
      (-Real.sin (2 * π * p) * (2 * π) * iteratedDeriv 1 correction p
        + Real.cos (2 * π * p) * iteratedDeriv 2 correction p) p :=
    (hasDerivAt_cos_two_pi p).mul (hasDerivAt_deriv_correction p)
  have hlin : HasDerivAt (fun x : ℝ ↦ 2 * π * (2 * x - 1)) (2 * π * 2) p := by
    simpa using (((hasDerivAt_id p).const_mul 2).sub_const 1).const_mul (2 * π)
  have hA := (((hasDerivAt_phase p).sin).neg).mul hlin
  have hB := ((hasDerivAt_sin_two_pi p).neg.mul_const (2 * π)).mul (hasDerivAt_correction p)
  have hfun : (fun x : ℝ ↦ Real.cos (2 * π * x) * iteratedDeriv 1 correction x)
      = fun x : ℝ ↦ -Real.sin (2 * π * (x ^ 2 - x - 1 / 16)) * (2 * π * (2 * x - 1))
          - -Real.sin (2 * π * x) * (2 * π) * correction x :=
    funext cos_mul_iteratedDeriv_one
  rw [hfun] at hL
  have hu := hL.unique (hA.sub hB)
  simp only [Pi.neg_apply] at hu
  linear_combination hu
theorem cos_mul_iteratedDeriv_three (p : ℝ) :
    Real.cos (2 * π * p) * iteratedDeriv 3 correction p
      = (-(-Real.sin (2 * π * (p ^ 2 - p - 1 / 16)) * (2 * π * (2 * p - 1)))
            * ((2 * π * (2 * p - 1)) * (2 * π * (2 * p - 1)))
          + -Real.cos (2 * π * (p ^ 2 - p - 1 / 16)) * (2 * (2 * π * (2 * p - 1)) * (2 * π * 2))
          - Real.cos (2 * π * (p ^ 2 - p - 1 / 16)) * (2 * π * (2 * p - 1)) * (4 * π))
        - 2 * (-(Real.cos (2 * π * p) * (2 * π)) * (2 * π)) * iteratedDeriv 1 correction p
        - 3 * (-Real.sin (2 * π * p) * (2 * π)) * iteratedDeriv 2 correction p
        - (-(-Real.sin (2 * π * p) * (2 * π)) * ((2 * π) * (2 * π)) * correction p
            + -Real.cos (2 * π * p) * ((2 * π) * (2 * π)) * iteratedDeriv 1 correction p) := by
  have hphi := hasDerivAt_phase p
  have hlin : HasDerivAt (fun x : ℝ ↦ 2 * π * (2 * x - 1)) (2 * π * 2) p := by
    simpa using (((hasDerivAt_id p).const_mul 2).sub_const 1).const_mul (2 * π)
  have hsq : HasDerivAt (fun x : ℝ ↦ (2 * π * (2 * x - 1)) * (2 * π * (2 * x - 1)))
      (2 * π * 2 * (2 * π * (2 * p - 1)) + 2 * π * (2 * p - 1) * (2 * π * 2)) p :=
    hlin.mul hlin
  have hA := ((hphi.cos).neg).mul hsq
  have hB := (hphi.sin).mul_const (4 * π)
  have hD := (((hasDerivAt_sin_two_pi p).neg.mul_const (2 * π)).const_mul 2).mul
    (hasDerivAt_deriv_correction p)
  have hE := (((hasDerivAt_cos_two_pi p).neg).mul_const (((2 * π) * (2 * π)))).mul
    (hasDerivAt_correction p)
  have hL : HasDerivAt (fun x : ℝ ↦ Real.cos (2 * π * x) * iteratedDeriv 2 correction x)
      (-Real.sin (2 * π * p) * (2 * π) * iteratedDeriv 2 correction p
        + Real.cos (2 * π * p) * iteratedDeriv 3 correction p) p :=
    (hasDerivAt_cos_two_pi p).mul (hasDerivAt_iteratedDeriv_correction 2 p)
  have hfun : (fun x : ℝ ↦ Real.cos (2 * π * x) * iteratedDeriv 2 correction x)
      = fun x : ℝ ↦
          (-Real.cos (2 * π * (x ^ 2 - x - 1 / 16))
                * ((2 * π * (2 * x - 1)) * (2 * π * (2 * x - 1)))
              - Real.sin (2 * π * (x ^ 2 - x - 1 / 16)) * (4 * π))
            - 2 * (-Real.sin (2 * π * x) * (2 * π)) * iteratedDeriv 1 correction x
            - -Real.cos (2 * π * x) * ((2 * π) * (2 * π)) * correction x :=
    funext cos_mul_iteratedDeriv_two
  rw [hfun] at hL
  have hu := hL.unique (((hA.sub hB).sub hD).sub hE)
  simp only [Pi.neg_apply] at hu
  linear_combination hu
end Zeta.RiemannSiegel
end
end CertificatePort108


section CertificatePort109
section
open scoped Nat Real
namespace Real
private theorem hasDerivAt_sq_div_two_sub_one_add_exp_neg_mul (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ y ^ 2 / 2 - 1 + exp (-y) * (1 + y)) (x - x * exp (-x)) x := by
  have h1 : HasDerivAt (fun y : ℝ ↦ y ^ 2 / 2) x x := by
    simpa using (hasDerivAt_pow 2 x).div_const 2
  have h2 : HasDerivAt (fun y : ℝ ↦ exp (-y)) (-exp (-x)) x := by
    simpa using (hasDerivAt_neg x).exp
  have h3 : HasDerivAt (fun y : ℝ ↦ (1 : ℝ) + y) 1 x := by
    simpa using (hasDerivAt_id x).const_add 1
  rw [show x - x * exp (-x) = x + (-exp (-x) * (1 + x) + exp (-x) * 1) by ring]
  exact (h1.sub_const 1).add (h2.mul h3)
theorem exp_sub_one_sub_id_le {r : ℝ} (hr : 0 ≤ r) : exp r - 1 - r ≤ r ^ 2 / 2 * exp r := by
  have hd := hasDerivAt_sq_div_two_sub_one_add_exp_neg_mul
  have hmono : MonotoneOn (fun y : ℝ ↦ y ^ 2 / 2 - 1 + exp (-y) * (1 + y)) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ ↦ (hd x).continuousAt.continuousWithinAt)
      (fun x _ ↦ (hd x).differentiableAt.differentiableWithinAt) fun x hx ↦ ?_
    rw [interior_Ici] at hx
    rw [(hd x).deriv]
    have hx0 : (0 : ℝ) < x := hx
    nlinarith [exp_le_one_iff.2 (neg_nonpos.2 hx0.le)]
  have hkey : 0 ≤ r ^ 2 / 2 - 1 + exp (-r) * (1 + r) := by
    simpa using hmono Set.self_mem_Ici hr hr
  have he : exp (-r) * exp r = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
  have h2 : 0 ≤ (r ^ 2 / 2 - 1 + exp (-r) * (1 + r)) * exp r := mul_nonneg hkey (exp_pos r).le
  have h3 : (r ^ 2 / 2 - 1 + exp (-r) * (1 + r)) * exp r
      = r ^ 2 / 2 * exp r - exp r + (1 + r) := by linear_combination (1 + r) * he
  rw [h3] at h2
  linarith
theorem exp_pi_div_four_le : exp (π / 4) ≤ 11 / 5 := by
  have h : π / 4 ≤ 0.7854 := by linarith [pi_lt_d4]
  refine (exp_le_exp.2 h).trans ?_
  refine (exp_bound' (by norm_num) (by norm_num) (n := 4) (by norm_num)).trans ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]
theorem exp_half_add_pi_div_three_le : exp (1 / 2 + π / 3) ≤ 47 / 10 := by
  have h : 1 / 2 + π / 3 ≤ (4 : ℕ) * 0.3868 := by push_cast; linarith [pi_lt_d4]
  have hb : exp 0.3868 ≤ 1.4723 := by
    refine (exp_bound' (by norm_num) (by norm_num) (n := 6) (by norm_num)).trans ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc exp (1 / 2 + π / 3) ≤ exp ((4 : ℕ) * 0.3868) := exp_le_exp.2 h
    _ = exp 0.3868 ^ 4 := exp_nat_mul _ 4
    _ ≤ 1.4723 ^ 4 := pow_le_pow_left₀ (exp_pos _).le hb 4
    _ ≤ 47 / 10 := by norm_num
end Real
namespace Complex
theorem norm_exp_sub_one_sub_id_le' (z : ℂ) : ‖exp z - 1 - z‖ ≤ ‖z‖ ^ 2 / 2 * Real.exp ‖z‖ := by
  have h := norm_exp_sub_sum_le_exp_norm_sub_sum z 2
  have hz : ∑ m ∈ Finset.range 2, z ^ m / (m ! : ℂ) = 1 + z := by
    simp [Finset.sum_range_succ]
  have hr : ∑ m ∈ Finset.range 2, ‖z‖ ^ m / (m ! : ℝ) = 1 + ‖z‖ := by
    simp [Finset.sum_range_succ]
  rw [hz, hr] at h
  rw [sub_sub]
  refine h.trans ?_
  linarith [Real.exp_sub_one_sub_id_le (norm_nonneg z)]
end Complex
end
end CertificatePort109


section CertificatePort110
section
open Complex MeasureTheory
open scoped Real
namespace Zeta.RiemannSiegel
theorem norm_modelIntegral_le' {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    ‖modelIntegral (p : ℂ) (1 / 2)‖ ≤ 11 / 10 := by
  refine (norm_modelIntegral_le p).trans ?_
  have hexp : Real.exp (π * (1 / 2 - p) ^ 2) ≤ Real.exp (π / 4) :=
    Real.exp_le_exp.2 (by nlinarith [Real.pi_pos, mul_nonneg h0 (sub_nonneg.2 h1)])
  linarith [Real.exp_pi_div_four_le]
private theorem norm_modelMoment_le_of_norm_pow_le (n : ℕ) (p C₀ C₁ C₂ C₃ : ℝ)
    (hpt : ∀ w : ℝ, ‖line (1 / 2) w - (p : ℂ)‖ ^ n
      ≤ C₀ + C₁ * |w + (1 / 2 - p) / 2| + C₂ * (w + (1 / 2 - p) / 2) ^ 2
        + C₃ * |w + (1 / 2 - p) / 2| ^ 3) :
    ‖modelMoment n (p : ℂ) (1 / 2)‖
      ≤ Real.exp (π * (1 / 2 - p) ^ 2) *
        (C₀ / 2 + C₁ / (4 * π) + C₂ / (16 * π) + C₃ / (16 * π ^ 2)) := by
  have ha : (1 : ℝ) / 2 = (0 : ℤ) + 1 / 2 := by norm_num
  have hb : (0 : ℝ) < 4 * π := by positivity
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hsqrt : Real.sqrt (π / (4 * π)) = 1 / 2 := by
    rw [show π / (4 * π) = (1 / 2 : ℝ) ^ 2 by rw [div_eq_iff (by positivity)]; ring,
      Real.sqrt_sq (by norm_num)]
  have hmajint : Integrable fun w : ℝ ↦ Real.exp (π * (1 / 2 - p) ^ 2) *
      (Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) *
        (C₀ + C₁ * |w + (1 / 2 - p) / 2| + C₂ * (w + (1 / 2 - p) / 2) ^ 2
          + C₃ * |w + (1 / 2 - p) / 2| ^ 3)) :=
    ((integrable_exp_neg_mul_sq_mul_poly hb C₀ C₁ C₂ C₃).comp_add_right
      ((1 / 2 - p) / 2)).const_mul _
  have hlhs : Integrable fun w : ℝ ↦
      Real.sqrt 2 * ‖modelMomentIntegrand n (p : ℂ) (1 / 2) w‖ :=
    (integrable_modelMomentIntegrand n (p : ℂ) ha).norm.const_mul _
  have hstep : ∀ w : ℝ, Real.sqrt 2 * ‖modelMomentIntegrand n (p : ℂ) (1 / 2) w‖
      ≤ Real.exp (π * (1 / 2 - p) ^ 2) *
        (Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) *
          (C₀ + C₁ * |w + (1 / 2 - p) / 2| + C₂ * (w + (1 / 2 - p) / 2) ^ 2
            + C₃ * |w + (1 / 2 - p) / 2| ^ 3)) := by
    intro w
    calc Real.sqrt 2 * ‖modelMomentIntegrand n (p : ℂ) (1 / 2) w‖
        = ‖line (1 / 2) w - (p : ℂ)‖ ^ n *
            (Real.sqrt 2 * ‖modelIntegrand (p : ℂ) (1 / 2) w‖) := by
          rw [modelMomentIntegrand, norm_mul, norm_pow]; ring
      _ ≤ ‖line (1 / 2) w - (p : ℂ)‖ ^ n *
            ‖exp (2 * π * I * (line (1 / 2) w - (p : ℂ)) ^ 2)‖ := by
          gcongr
          exact (le_div_iff₀' (Real.sqrt_pos.2 two_pos)).mp (norm_modelIntegrand_le (p : ℂ) ha w)
      _ ≤ (C₀ + C₁ * |w + (1 / 2 - p) / 2| + C₂ * (w + (1 / 2 - p) / 2) ^ 2
            + C₃ * |w + (1 / 2 - p) / 2| ^ 3) *
            (Real.exp (π * (1 / 2 - p) ^ 2) *
              Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2)) := by
          rw [norm_exp_two_pi_mul_I_mul_line_sub_sq]
          gcongr
          exact hpt w
      _ = _ := by ring
  calc ‖modelMoment n (p : ℂ) (1 / 2)‖
      ≤ Real.sqrt 2 * ∫ w : ℝ, ‖modelMomentIntegrand n (p : ℂ) (1 / 2) w‖ := by
        rw [modelMoment]; exact norm_one_add_I_mul_integral_le _
    _ = ∫ w : ℝ, Real.sqrt 2 * ‖modelMomentIntegrand n (p : ℂ) (1 / 2) w‖ :=
        (integral_const_mul _ _).symm
    _ ≤ ∫ w : ℝ, Real.exp (π * (1 / 2 - p) ^ 2) *
          (Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) *
            (C₀ + C₁ * |w + (1 / 2 - p) / 2| + C₂ * (w + (1 / 2 - p) / 2) ^ 2
              + C₃ * |w + (1 / 2 - p) / 2| ^ 3)) := integral_mono hlhs hmajint hstep
    _ = Real.exp (π * (1 / 2 - p) ^ 2) * ∫ u : ℝ, Real.exp (-(4 * π) * u ^ 2) *
          (C₀ + C₁ * |u| + C₂ * u ^ 2 + C₃ * |u| ^ 3) := by
        rw [integral_const_mul]
        exact congrArg _ (integral_add_right_eq_self (fun u : ℝ ↦ Real.exp (-(4 * π) * u ^ 2) *
          (C₀ + C₁ * |u| + C₂ * u ^ 2 + C₃ * |u| ^ 3)) ((1 / 2 - p) / 2))
    _ = _ := by
        rw [integral_exp_neg_mul_sq_mul_poly hb, hsqrt]
        field_simp
        ring
private theorem norm_modelMoment_one_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    ‖modelMoment 1 (p : ℂ) (1 / 2)‖
      ≤ Real.exp (π * (1 / 2 - p) ^ 2) * (Real.sqrt 2 * (1 / 8 + 1 / (4 * π))) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  refine (norm_modelMoment_le_of_norm_pow_le 1 p (Real.sqrt 2 / 4) (Real.sqrt 2) 0 0
    fun w ↦ ?_).trans_eq ?_
  · have hc : |1 / 2 - p| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    have hle := norm_line_sub_ofReal_le' (1 / 2) w p
    rw [pow_one]
    nlinarith [Real.sqrt_nonneg 2, abs_nonneg (w + (1 / 2 - p) / 2)]
  · field_simp
    ring
private theorem norm_modelMoment_three_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    ‖modelMoment 3 (p : ℂ) (1 / 2)‖
      ≤ Real.exp (π * (1 / 2 - p) ^ 2) *
        (Real.sqrt 2 * (1 / 64 + 1 / (16 * π) + 1 / (8 * π ^ 2))) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  refine (norm_modelMoment_le_of_norm_pow_le 3 p (Real.sqrt 2 / 32) (Real.sqrt 2 / 8)
    (Real.sqrt 2 / 2) (2 * Real.sqrt 2) fun w ↦ ?_).trans_eq ?_
  · set X := |w + (1 / 2 - p) / 2| with hX
    have hXsq : X ^ 2 = (w + (1 / 2 - p) / 2) ^ 2 := by rw [hX]; exact sq_abs _
    have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hc : |1 / 2 - p| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    have hc2 : (1 / 2 - p) ^ 2 ≤ 1 / 4 := by nlinarith [abs_nonneg (1 / 2 - p), sq_abs (1 / 2 - p)]
    have hY0 : (0 : ℝ) ≤ ‖line (1 / 2) w - (p : ℂ)‖ := norm_nonneg _
    have hYsq : ‖line (1 / 2) w - (p : ℂ)‖ ^ 2 = 2 * X ^ 2 + (1 / 2 - p) ^ 2 / 2 := by
      rw [norm_line_sub_ofReal_sq, hXsq]
    have hYle : ‖line (1 / 2) w - (p : ℂ)‖ ≤ Real.sqrt 2 * (X + 1 / 4) := by
      have hle := norm_line_sub_ofReal_le' (1 / 2) w p
      nlinarith
    calc ‖line (1 / 2) w - (p : ℂ)‖ ^ 3
        = ‖line (1 / 2) w - (p : ℂ)‖ ^ 2 * ‖line (1 / 2) w - (p : ℂ)‖ := by ring
      _ ≤ (2 * X ^ 2 + 1 / 8) * (Real.sqrt 2 * (X + 1 / 4)) := by
          rw [hYsq]
          exact mul_le_mul (by linarith) hYle hY0 (by positivity)
      _ = Real.sqrt 2 / 32 + Real.sqrt 2 / 8 * X + Real.sqrt 2 / 2 * X ^ 2
            + 2 * Real.sqrt 2 * X ^ 3 := by ring
      _ = _ := by rw [← hXsq]
  · field_simp
    ring
theorem norm_iteratedDeriv_three_modelIntegral_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    ‖iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ)‖
      ≤ Real.sqrt 2 * Real.exp (π / 4) * (20 * π + 10 * π ^ 2 + π ^ 3) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hπ' : π ≠ 0 := hπ.ne'
  have hexp : Real.exp (π * (1 / 2 - p) ^ 2) ≤ Real.exp (π / 4) :=
    Real.exp_le_exp.2 (by nlinarith [mul_nonneg h0 (sub_nonneg.2 h1)])
  rw [iteratedDeriv_three_modelIntegral (p : ℂ) (by norm_num : (1 : ℝ) / 2 = (0 : ℤ) + 1 / 2)]
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hπ, Complex.norm_I, mul_one]
  calc 48 * π ^ 2 * ‖modelMoment 1 (p : ℂ) (1 / 2)‖
        + 64 * π ^ 3 * ‖modelMoment 3 (p : ℂ) (1 / 2)‖
      ≤ 48 * π ^ 2 * (Real.exp (π * (1 / 2 - p) ^ 2) * (Real.sqrt 2 * (1 / 8 + 1 / (4 * π))))
          + 64 * π ^ 3 * (Real.exp (π * (1 / 2 - p) ^ 2) *
            (Real.sqrt 2 * (1 / 64 + 1 / (16 * π) + 1 / (8 * π ^ 2)))) :=
        add_le_add (mul_le_mul_of_nonneg_left (norm_modelMoment_one_le h0 h1) (by positivity))
          (mul_le_mul_of_nonneg_left (norm_modelMoment_three_le h0 h1) (by positivity))
    _ = Real.exp (π * (1 / 2 - p) ^ 2) * (Real.sqrt 2 * (20 * π + 10 * π ^ 2 + π ^ 3)) := by
        field_simp
        ring
    _ ≤ Real.exp (π / 4) * (Real.sqrt 2 * (20 * π + 10 * π ^ 2 + π ^ 3)) := by
        gcongr
    _ = Real.sqrt 2 * Real.exp (π / 4) * (20 * π + 10 * π ^ 2 + π ^ 3) := by ring
theorem norm_iteratedDeriv_three_modelIntegral_le' {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    ‖iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ)‖ ≤ 610 := by
  refine (norm_iteratedDeriv_three_modelIntegral_le h0 h1).trans ?_
  have hs2 : Real.sqrt 2 ≤ 1.415 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hK : 20 * π + 10 * π ^ 2 + π ^ 3 ≤ 193 := by
    nlinarith [Real.pi_lt_d4, Real.pi_pos]
  calc Real.sqrt 2 * Real.exp (π / 4) * (20 * π + 10 * π ^ 2 + π ^ 3)
      ≤ 1.415 * (11 / 5) * 193 :=
        mul_le_mul (mul_le_mul hs2 Real.exp_pi_div_four_le (Real.exp_pos _).le (by norm_num)) hK
          (by positivity) (by norm_num)
    _ ≤ 610 := by norm_num
theorem abs_iteratedDeriv_three_correction_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    |iteratedDeriv 3 correction p| ≤ 1220 := by
  have hunit : ‖exp (-((π / 8 : ℝ) * I))‖ = 1 := by simp [Complex.norm_exp]
  rw [iteratedDeriv_three_correction p, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc 2 * |(exp (-((π / 8 : ℝ) * I)) *
          iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ)).re|
      ≤ 2 * ‖exp (-((π / 8 : ℝ) * I)) *
          iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ)‖ := by
        gcongr
        exact Complex.abs_re_le_norm _
    _ = 2 * ‖iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ)‖ := by
        rw [norm_mul, hunit, one_mul]
    _ ≤ 2 * 610 := by
        gcongr
        exact norm_iteratedDeriv_three_modelIntegral_le' h0 h1
    _ = 1220 := by norm_num
theorem correctionLinear_eq (p : ℝ) :
    correctionLinear p = -iteratedDeriv 3 correction p / (96 * π ^ 2) :=
  (neg_iteratedDeriv_three_correction_div_eq p).symm
theorem abs_correctionLinear_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    |correctionLinear p| ≤ 13 / 10 := by
  have hpos : (0 : ℝ) < 96 * π ^ 2 := by positivity
  rw [correctionLinear_eq, abs_div, abs_neg, abs_of_pos hpos, div_le_iff₀ hpos]
  nlinarith [abs_iteratedDeriv_three_correction_le h0 h1, Real.pi_gt_d2, Real.pi_pos]
end Zeta.RiemannSiegel
end
end CertificatePort110


section CertificatePort111
section
open Complex MeasureTheory
open scoped Real
namespace Zeta.RiemannSiegel
theorem norm_modelIntegrand_le_exp_neg_mul_sq {p : ℝ} (hκ : |1 / 2 - p| ≤ 1 / 2) (w : ℝ) :
    ‖modelIntegrand (p : ℂ) (1 / 2) w‖
      ≤ Real.exp (π / 4) * Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) / Real.sqrt 2 := by
  refine (norm_modelIntegrand_le (p : ℂ) (by norm_num : (1 / 2 : ℝ) = (0 : ℤ) + 1 / 2) w).trans ?_
  rw [norm_exp_two_pi_mul_I_mul_line_sub_sq p w,
    div_le_div_iff_of_pos_right (Real.sqrt_pos.2 two_pos)]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2
    (by nlinarith [Real.pi_pos, sq_le_sq' (abs_le.1 hκ).1 (abs_le.1 hκ).2])) (Real.exp_nonneg _)
noncomputable def leadingTheta (t : ℝ) : ℝ :=
  t / 2 * Real.log (t / (2 * π)) - t / 2 - π / 8
theorem leadingTheta_add_pi_div_eight (t : ℝ) :
    leadingTheta t + π / 8 = π * (t / (2 * π)) * (Real.log (t / (2 * π)) - 1) := by
  have hpi : π ≠ 0 := Real.pi_ne_zero
  rw [leadingTheta]
  field_simp
  ring
noncomputable def saddleDiscrepancy (t : ℝ) (x : ℂ) : ℂ :=
  π * I * x ^ 2 - (1 / 2 + t * I) * slantLog x + (Real.log (t / (2 * π)) : ℂ) / 4
    + I * ((leadingTheta t : ℂ) + π / 8)
    - 2 * π * I * (x - (Real.sqrt (t / (2 * π)) : ℂ)) ^ 2
noncomputable def saddleFactor (t : ℝ) (ν : ℕ) : ℂ :=
  (-1) ^ ν * ((t / (2 * π)) ^ (-(1 / 4) : ℝ) : ℝ)
    * exp (-(I * ((leadingTheta t : ℂ) + π / 8)))
theorem saddleFactor_ne_zero {t : ℝ} (ht : 0 < t) (ν : ℕ) : saddleFactor t ν ≠ 0 := by
  have hT0 : 0 < t / (2 * π) := by positivity
  rw [saddleFactor]
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_) (exp_ne_zero _)
  exact_mod_cast (Real.rpow_pos_of_pos hT0 _).ne'
theorem norm_saddleFactor {t : ℝ} (ht : 0 < t) (ν : ℕ) :
    ‖saddleFactor t ν‖ = (t / (2 * π)) ^ (-(1 / 4) : ℝ) := by
  have hT0 : 0 < t / (2 * π) := by positivity
  rw [saddleFactor, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hT0 _)]
  simp
theorem integrand_eq_modelFun_mul {t : ℝ} (ht : 0 < t) (ν : ℕ) {x : ℂ} (hx : x ≠ 0) :
    integrand (1 / 2 + t * I) x
      = saddleFactor t ν * modelFun ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (x - ν)
        * exp (saddleDiscrepancy t x) := by
  have hT0 : 0 < t / (2 * π) := by positivity
  have hinv : ((-1 : ℂ) ^ ν)⁻¹ = (-1) ^ ν := by rw [← inv_pow, inv_neg_one]
  have hdiv : ∀ E : ℂ, E / (2 * I * ((-1 : ℂ) ^ ν * Complex.sin (π * (x - ν))))
      = (-1) ^ ν * (E / (2 * I * Complex.sin (π * (x - ν)))) := fun E ↦ by
    rw [show (2 : ℂ) * I * ((-1 : ℂ) ^ ν * Complex.sin (π * (x - ν)))
        = (-1 : ℂ) ^ ν * (2 * I * Complex.sin (π * (x - ν))) by ring,
      div_mul_eq_div_div_swap, div_eq_mul_inv, hinv, mul_comm]
  have hsin : Complex.sin (π * x) = (-1) ^ ν * Complex.sin (π * (x - ν)) := by
    rw [show ((π : ℂ) * x) = π * (x - ν) + ν * π by ring]
    exact Complex.sin_antiperiodic.add_nat_mul_eq ν
  have hrpow : (((t / (2 * π)) ^ (-(1 / 4) : ℝ) : ℝ) : ℂ)
      = exp (-((Real.log (t / (2 * π)) : ℂ) / 4)) := by
    rw [Real.rpow_def_of_pos hT0, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hnum : exp (-(1 / 2 + (t : ℂ) * I) * slantLog x) * exp ((π : ℂ) * I * x ^ 2)
      = exp (-((Real.log (t / (2 * π)) : ℂ) / 4)) * exp (-(I * ((leadingTheta t : ℂ) + π / 8)))
        * exp (2 * π * I * (x - (Real.sqrt (t / (2 * π)) : ℂ)) ^ 2)
        * exp (saddleDiscrepancy t x) := by
    rw [← exp_add, ← exp_add, ← exp_add, ← exp_add, saddleDiscrepancy]
    congr 1
    ring
  rw [integrand, kernel_eq_div_two_mul_I_mul_sin, slantCpow_eq_exp_mul_slantLog hx,
    modelFun_eq_div_two_mul_I_mul_sin, hsin, saddleFactor, hrpow,
    show ((x - (ν : ℂ)) - ((Real.sqrt (t / (2 * π)) - ν : ℝ) : ℂ))
      = x - (Real.sqrt (t / (2 * π)) : ℂ) by push_cast; ring, hdiv]
  linear_combination ((-1 : ℂ) ^ ν / (2 * I * Complex.sin (π * (x - ν)))) * hnum
theorem line_sub_ofReal_sub {ν : ℕ} {S p : ℝ} (hp : p = S - ν) (w : ℝ) :
    line ((ν : ℝ) + 1 / 2) w - (S : ℂ) = line (1 / 2) w - (p : ℂ) := by
  rw [hp, line, line]
  push_cast
  ring
theorem contourIntegrand_eq_modelIntegrand_mul {t : ℝ} (ht : 0 < t) (ν : ℕ) (w : ℝ) :
    contourIntegrand (1 / 2 + t * I) ((ν : ℝ) + 1 / 2) w
      = saddleFactor t ν
        * (modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
          * exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w))) := by
  have hline : line ((ν : ℝ) + 1 / 2) w - (ν : ℂ) = line (1 / 2) w := by
    simpa using line_sub_ofReal_sub (S := (ν : ℝ)) (p := 0) (by ring) w
  have hx0 : line ((ν : ℝ) + 1 / 2) w ≠ 0 := line_ne_zero (by positivity) w
  rw [contourIntegrand, integrand_eq_modelFun_mul ht ν hx0, modelIntegrand, hline]
  ring
theorem norm_modelIntegrand_mul_exp_saddleDiscrepancy {t : ℝ} (ht : 0 < t) (ν : ℕ) (w : ℝ) :
    ‖modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
        * exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w))‖
      = ‖contourIntegrand (1 / 2 + t * I) ((ν : ℝ) + 1 / 2) w‖
          / (t / (2 * π)) ^ (-(1 / 4) : ℝ) := by
  have hR0 : (t / (2 * π)) ^ (-(1 / 4) : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos (by positivity) _).ne'
  rw [contourIntegrand_eq_modelIntegrand_mul ht ν w, norm_mul (saddleFactor t ν),
    norm_saddleFactor ht]
  field_simp
theorem integrable_modelIntegrand_mul_exp_saddleDiscrepancy {t : ℝ} (ht : 0 < t) (ν : ℕ) :
    Integrable fun w : ℝ ↦ modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
      * exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) := by
  have hint : Integrable (contourIntegrand (1 / 2 + t * I) ((ν : ℝ) + 1 / 2)) :=
    integrable_contourIntegrand _ (by positivity) (c := Real.sqrt 2 / 2) (by positivity)
      fun w ↦ norm_sin_pi_mul_line_ge (n := (ν : ℤ)) (by push_cast; ring) w
  refine (hint.const_mul (saddleFactor t ν)⁻¹).congr (.of_forall fun w ↦ ?_)
  change (saddleFactor t ν)⁻¹ * contourIntegrand (1 / 2 + t * I) ((ν : ℝ) + 1 / 2) w = _
  rw [contourIntegrand_eq_modelIntegrand_mul ht ν w, ← mul_assoc,
    inv_mul_cancel₀ (saddleFactor_ne_zero ht ν), one_mul]
theorem integrable_modelIntegrand_mul_exp_saddleDiscrepancy_sub_one {t : ℝ} (ht : 0 < t) (ν : ℕ) :
    Integrable fun w : ℝ ↦ modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
      * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1) := by
  have hhalf : (1 / 2 : ℝ) = (0 : ℤ) + 1 / 2 := by norm_num
  exact (((integrable_modelIntegrand_mul_exp_saddleDiscrepancy ht ν).sub
    (integrable_modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ) : ℂ) hhalf)).congr
    (.of_forall fun w ↦ by simp only [Pi.sub_apply]; ring))
theorem contourIntegral_eq_modelIntegrand_mul {t : ℝ} (ht : 0 < t) (ν : ℕ) :
    contourIntegral (1 / 2 + t * I) ((ν : ℝ) + 1 / 2)
      = saddleFactor t ν
        * ((1 + I) * ∫ w : ℝ, modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
            * exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w))) := by
  rw [contourIntegral]
  simp only [contourIntegrand_eq_modelIntegrand_mul ht ν]
  rw [integral_const_mul]
  ring
theorem contourIntegral_sub_mul_modelIntegral {t : ℝ} (ht : 0 < t) (ν : ℕ) :
    contourIntegral (1 / 2 + t * I) ((ν : ℝ) + 1 / 2)
        - saddleFactor t ν * modelIntegral ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2)
      = saddleFactor t ν
        * ((1 + I) * ∫ w : ℝ, modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
            * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1)) := by
  have hhalf : (1 / 2 : ℝ) = (0 : ℤ) + 1 / 2 := by norm_num
  have hsplit : (∫ w : ℝ, modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
        * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1))
      = (∫ w : ℝ, modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
          * exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)))
        - ∫ w : ℝ, modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w := by
    simp only [mul_sub, mul_one]
    exact integral_sub (integrable_modelIntegrand_mul_exp_saddleDiscrepancy ht ν)
      (integrable_modelIntegrand _ hhalf)
  rw [contourIntegral_eq_modelIntegrand_mul ht ν, modelIntegral, hsplit]
  ring
private theorem logTaylor_two (z : ℂ) : Complex.logTaylor 2 z = z := by
  simp [Complex.logTaylor_succ, Complex.logTaylor_zero]
private theorem logTaylor_three (z : ℂ) : Complex.logTaylor 3 z = z - z ^ 2 / 2 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, Complex.logTaylor_succ, Pi.add_apply, logTaylor_two]
  push_cast
  ring
private theorem logTaylor_four (z : ℂ) : Complex.logTaylor 4 z = z - z ^ 2 / 2 + z ^ 3 / 3 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, Complex.logTaylor_succ, Pi.add_apply, logTaylor_three]
  push_cast
  ring
private theorem norm_log_sub_logTaylor_le_of_norm_le_half {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) (n : ℕ) :
    ‖Complex.log (1 + u) - Complex.logTaylor (n + 1) u‖ ≤ 2 * ‖u‖ ^ (n + 1) / (n + 1) := by
  have hu1 : ‖u‖ < 1 := hu.trans_lt (by norm_num)
  have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) two_pos]
    linarith
  refine (Complex.norm_log_sub_logTaylor_le n hu1).trans ?_
  calc ‖u‖ ^ (n + 1) * (1 - ‖u‖)⁻¹ / ((n : ℝ) + 1)
      ≤ ‖u‖ ^ (n + 1) * 2 / ((n : ℝ) + 1) := by gcongr
    _ = 2 * ‖u‖ ^ (n + 1) / ((n : ℝ) + 1) := by ring
private theorem norm_neg_half_sub_two_pi_mul_I_mul_le {T α β : ℝ} (hT : 0 ≤ T) {A B : ℂ}
    (hA : ‖A‖ ≤ α) (hB : ‖B‖ ≤ β) :
    ‖-(1 / 2) * A - 2 * π * I * (T : ℂ) * B‖ ≤ 1 / 2 * α + 2 * π * T * β := by
  have hfac : ‖2 * (π : ℂ) * I * (T : ℂ)‖ = 2 * π * T := by
    simp only [norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_ofNat, mul_one,
      Real.norm_of_nonneg Real.pi_pos.le, Real.norm_of_nonneg hT]
  calc ‖-(1 / 2) * A - 2 * π * I * (T : ℂ) * B‖
      ≤ ‖-(1 / 2) * A‖ + ‖2 * (π : ℂ) * I * (T : ℂ) * B‖ := norm_sub_le _ _
    _ = 1 / 2 * ‖A‖ + 2 * π * T * ‖B‖ := by rw [norm_mul, norm_mul, hfac]; norm_num
    _ ≤ 1 / 2 * α + 2 * π * T * β :=
        add_le_add (by linarith)
          (mul_le_mul_of_nonneg_left hB (mul_nonneg (by positivity) hT))
theorem saddleDiscrepancy_eq_log_sub_logTaylor {t : ℝ} (ht : 0 < t) {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    saddleDiscrepancy t ((Real.sqrt (t / (2 * π)) : ℂ) * (1 + u))
      = -(1 / 2) * Complex.log (1 + u)
        - 2 * π * I * ((t / (2 * π) : ℝ) : ℂ)
          * (Complex.log (1 + u) - Complex.logTaylor 3 u) := by
  have hT0 : 0 < t / (2 * π) := by positivity
  have hS : 0 < Real.sqrt (t / (2 * π)) := Real.sqrt_pos.2 hT0
  have hur : -(1 / 2 : ℝ) ≤ u.re := by
    linarith [neg_abs_le u.re, (Complex.abs_re_le_norm u).trans hu]
  have h1u : (1 : ℂ) + u ≠ 0 := fun h ↦ by
    rw [show u = -1 by linear_combination h] at hur
    norm_num at hur
  have hre : 0 < ((Real.sqrt (t / (2 * π)) : ℂ) * (1 + u)).re := by
    have h1 : (0 : ℝ) < (1 + u).re := by rw [Complex.add_re, Complex.one_re]; linarith
    rw [Complex.re_ofReal_mul]
    positivity
  have hlog : Complex.log ((Real.sqrt (t / (2 * π)) : ℂ) * (1 + u))
      = (Real.log (t / (2 * π)) : ℂ) / 2 + Complex.log (1 + u) := by
    rw [Complex.log_ofReal_mul hS h1u, Real.log_sqrt hT0.le]
    push_cast
    ring
  have hS2 : ((Real.sqrt (t / (2 * π)) : ℂ)) ^ 2 = ((t / (2 * π) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hT0.le]
  have ht2 : (t : ℂ) = 2 * π * ((t / (2 * π) : ℝ) : ℂ) := by push_cast; field_simp
  have hϑ : ((leadingTheta t : ℝ) : ℂ) + (π : ℂ) / 8
      = π * ((t / (2 * π) : ℝ) : ℂ) * ((Real.log (t / (2 * π)) : ℂ) - 1) := by
    rw [show ((leadingTheta t : ℝ) : ℂ) + (π : ℂ) / 8 = ((leadingTheta t + π / 8 : ℝ) : ℂ) by
      push_cast; ring, leadingTheta_add_pi_div_eight]
    push_cast
    ring
  rw [saddleDiscrepancy, slantLog_eq_log hre, hlog, hϑ, logTaylor_three, ht2, ← hS2]
  ring
theorem norm_saddleDiscrepancy_le {t : ℝ} (ht : 0 < t) {x : ℂ}
    (hx : ‖x - (Real.sqrt (t / (2 * π)) : ℂ)‖ ≤ Real.sqrt (t / (2 * π)) / 2) :
    ‖saddleDiscrepancy t x‖
      ≤ (‖x - (Real.sqrt (t / (2 * π)) : ℂ)‖
          + 4 * π / 3 * ‖x - (Real.sqrt (t / (2 * π)) : ℂ)‖ ^ 3) / Real.sqrt (t / (2 * π)) := by
  have hT0 : 0 < t / (2 * π) := by positivity
  have hS : 0 < Real.sqrt (t / (2 * π)) := Real.sqrt_pos.2 hT0
  set S : ℝ := Real.sqrt (t / (2 * π)) with hSdef
  set n : ℝ := ‖x - (S : ℂ)‖ with hn
  have hn0 : 0 ≤ n := norm_nonneg _
  have hSne : ((S : ℝ) : ℂ) ≠ 0 := by simpa using hS.ne'
  have hxu : x = (S : ℂ) * (1 + (x - (S : ℂ)) / (S : ℂ)) := by field_simp; ring
  have hunorm : ‖(x - (S : ℂ)) / (S : ℂ)‖ = n / S := by
    rw [norm_div, hn, Complex.norm_real, Real.norm_of_nonneg hS.le]
  have hu : ‖(x - (S : ℂ)) / (S : ℂ)‖ ≤ 1 / 2 := by
    rw [hunorm, div_le_iff₀ hS]
    linarith [hx]
  have hTS : t / (2 * π) = S ^ 2 := (Real.sq_sqrt hT0.le).symm
  have hlog : ‖Complex.log (1 + (x - (S : ℂ)) / (S : ℂ))‖ ≤ 3 / 2 * (n / S) := by
    rw [← hunorm]
    exact Complex.norm_log_one_add_half_le_self hu
  have htail : ‖Complex.log (1 + (x - (S : ℂ)) / (S : ℂ))
      - Complex.logTaylor 3 ((x - (S : ℂ)) / (S : ℂ))‖ ≤ 2 / 3 * (n / S) ^ 3 := by
    have h := norm_log_sub_logTaylor_le_of_norm_le_half hu 2
    rw [hunorm] at h
    norm_num at h
    linarith
  have hΔ : saddleDiscrepancy t x
      = -(1 / 2) * Complex.log (1 + (x - (S : ℂ)) / (S : ℂ))
        - 2 * π * I * ((t / (2 * π) : ℝ) : ℂ)
          * (Complex.log (1 + (x - (S : ℂ)) / (S : ℂ))
            - Complex.logTaylor 3 ((x - (S : ℂ)) / (S : ℂ))) := by
    conv_lhs => rw [hxu]
    exact saddleDiscrepancy_eq_log_sub_logTaylor ht hu
  rw [hΔ]
  refine (norm_neg_half_sub_two_pi_mul_I_mul_le hT0.le hlog htail).trans ?_
  rw [show 1 / 2 * (3 / 2 * (n / S)) + 2 * π * (t / (2 * π)) * (2 / 3 * (n / S) ^ 3)
      = (3 / 4 * n + 4 * π / 3 * n ^ 3) / S by rw [hTS]; field_simp; ring]
  gcongr
  linarith
noncomputable def saddleLinear (y : ℂ) : ℂ := -(y / 2) - 2 * π * I / 3 * y ^ 3
theorem norm_saddleLinear_le (y : ℂ) : ‖saddleLinear y‖ ≤ ‖y‖ / 2 + 2 * π / 3 * ‖y‖ ^ 3 := by
  rw [saddleLinear]
  refine (norm_sub_le _ _).trans (le_of_eq ?_)
  rw [norm_neg, norm_div, norm_mul, norm_pow, norm_div, norm_mul, norm_mul, Complex.norm_I,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  norm_num
theorem norm_saddleDiscrepancy_sub_linear_le {t : ℝ} (ht : 0 < t) {x : ℂ}
    (hx : ‖x - (Real.sqrt (t / (2 * π)) : ℂ)‖ ≤ Real.sqrt (t / (2 * π)) / 2) :
    ‖saddleDiscrepancy t x
        - saddleLinear (x - (Real.sqrt (t / (2 * π)) : ℂ)) / (Real.sqrt (t / (2 * π)) : ℂ)‖
      ≤ (1 / 2 * ‖x - (Real.sqrt (t / (2 * π)) : ℂ)‖ ^ 2
          + π * ‖x - (Real.sqrt (t / (2 * π)) : ℂ)‖ ^ 4) / (t / (2 * π)) := by
  have hT0 : 0 < t / (2 * π) := by positivity
  have hS : 0 < Real.sqrt (t / (2 * π)) := Real.sqrt_pos.2 hT0
  set S : ℝ := Real.sqrt (t / (2 * π))
  set n : ℝ := ‖x - (S : ℂ)‖ with hn
  have hSne : ((S : ℝ) : ℂ) ≠ 0 := by simpa using hS.ne'
  have hS0 : S ≠ 0 := hS.ne'
  have hTS : t / (2 * π) = S ^ 2 := (Real.sq_sqrt hT0.le).symm
  have hTS' : ((t / (2 * π) : ℝ) : ℂ) = (S : ℂ) ^ 2 := by rw [hTS]; push_cast; ring
  set u : ℂ := (x - (S : ℂ)) / (S : ℂ) with hu_def
  have hunorm : ‖u‖ = n / S := by
    rw [hu_def, norm_div, hn, Complex.norm_real, Real.norm_of_nonneg hS.le]
  have hu : ‖u‖ ≤ 1 / 2 := by
    rw [hunorm, div_le_iff₀ hS]
    linarith [hx]
  have hxS : x - (S : ℂ) = (S : ℂ) * u := by
    rw [hu_def]
    field_simp
  have hxu : x = (S : ℂ) * (1 + u) := by linear_combination hxS
  have hkey : saddleDiscrepancy t x - saddleLinear (x - (S : ℂ)) / (S : ℂ)
      = -(1 / 2) * (Complex.log (1 + u) - Complex.logTaylor 2 u)
        - 2 * π * I * ((t / (2 * π) : ℝ) : ℂ)
          * (Complex.log (1 + u) - Complex.logTaylor 4 u) := by
    have hΔ : saddleDiscrepancy t x
        = -(1 / 2) * Complex.log (1 + u) - 2 * π * I * ((t / (2 * π) : ℝ) : ℂ)
            * (Complex.log (1 + u) - Complex.logTaylor 3 u) := by
      conv_lhs => rw [hxu]
      exact saddleDiscrepancy_eq_log_sub_logTaylor ht hu
    rw [hΔ, logTaylor_two, logTaylor_three, logTaylor_four, saddleLinear, hxS, hTS']
    field_simp
    ring
  have hlog2 : ‖Complex.log (1 + u) - Complex.logTaylor 2 u‖ ≤ ‖u‖ ^ 2 := by
    have h := norm_log_sub_logTaylor_le_of_norm_le_half hu 1
    norm_num at h
    linarith
  have hlog4 : ‖Complex.log (1 + u) - Complex.logTaylor 4 u‖ ≤ ‖u‖ ^ 4 / 2 := by
    have h := norm_log_sub_logTaylor_le_of_norm_le_half hu 3
    norm_num at h
    linarith
  rw [hkey]
  refine (norm_neg_half_sub_two_pi_mul_I_mul_le hT0.le hlog2 hlog4).trans_eq ?_
  rw [hunorm, hTS]
  field_simp
theorem norm_saddleDiscrepancy_le' {t : ℝ} (ht : 0 < t) {x : ℂ}
    (hx : ‖x - (Real.sqrt (t / (2 * π)) : ℂ)‖ ≤ Real.sqrt (t / (2 * π)) / 2) :
    ‖saddleDiscrepancy t x‖ ≤ 1 / 2 + 2 * π / 3 * ‖x - (Real.sqrt (t / (2 * π)) : ℂ)‖ ^ 2 := by
  have hT0 : 0 < t / (2 * π) := by positivity
  have hS : 0 < Real.sqrt (t / (2 * π)) := Real.sqrt_pos.2 hT0
  set S : ℝ := Real.sqrt (t / (2 * π))
  set n : ℝ := ‖x - (S : ℂ)‖
  have hcube : 0 ≤ π * (n ^ 2 * (S - 2 * n)) :=
    mul_nonneg Real.pi_pos.le (mul_nonneg (sq_nonneg n) (by linarith))
  refine (norm_saddleDiscrepancy_le ht hx).trans ?_
  rw [div_le_iff₀ hS]
  nlinarith [hcube]
theorem exp_norm_saddleDiscrepancy_mul_exp_le {t : ℝ} (ht : 0 < t) {x : ℂ}
    (hx : ‖x - (Real.sqrt (t / (2 * π)) : ℂ)‖ ≤ Real.sqrt (t / (2 * π)) / 2) :
    Real.exp ‖saddleDiscrepancy t x‖
        * Real.exp (-(2 * π) * ‖x - (Real.sqrt (t / (2 * π)) : ℂ)‖ ^ 2)
      ≤ Real.exp (1 / 2)
          * Real.exp (-(4 * π / 3) * ‖x - (Real.sqrt (t / (2 * π)) : ℂ)‖ ^ 2) := by
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  linarith [norm_saddleDiscrepancy_le' ht hx]
end Zeta.RiemannSiegel
end
end CertificatePort111


section CertificatePort112
section
open Complex MeasureTheory
open scoped Real
namespace Zeta.RiemannSiegel
noncomputable def sharpSplitRadius (t : ℝ) : ℝ :=
  (Real.sqrt (t / (2 * π)) - 1) / (2 * Real.sqrt 2)
theorem sqrt_two_le : Real.sqrt 2 ≤ 1.41422 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
theorem pow_mul_exp_neg_mul_sq_le {b A₀ A : ℝ} {k : ℕ} (hb : 0 < b) (hA₀ : 0 < A₀)
    (hbA : (k : ℝ) ≤ b * A₀ ^ 2) (hA : A₀ ≤ A) :
    A ^ k * Real.exp (-b * A ^ 2) ≤ A₀ ^ k * Real.exp (-b * A₀ ^ 2) := by
  have hx : 0 ≤ b * (A ^ 2 - A₀ ^ 2) := mul_nonneg hb.le (by nlinarith)
  have hA₀' : A₀ ≠ 0 := hA₀.ne'
  have hexp : A ^ k ≤ A₀ ^ k * Real.exp (b * (A ^ 2 - A₀ ^ 2)) := by
    rw [← div_le_iff₀' (pow_pos hA₀ k), ← div_pow]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using Real.one_le_exp hx
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hlin : A / A₀ ≤ 1 + b * (A ^ 2 - A₀ ^ 2) / k := by
      rw [div_le_iff₀ hA₀, ← sub_nonneg,
        show (1 + b * (A ^ 2 - A₀ ^ 2) / (k : ℝ)) * A₀ - A
          = (b * A₀ * (A + A₀) - k) * (A - A₀) / (k : ℝ) by field_simp; ring]
      have hkA : (k : ℝ) ≤ b * A₀ * (A + A₀) := by
        nlinarith [mul_nonneg (mul_nonneg hb.le hA₀.le) (sub_nonneg.2 hA),
          mul_pos hb (pow_pos hA₀ 2)]
      exact div_nonneg (mul_nonneg (by linarith) (by linarith)) hk0.le
    have hd : 0 ≤ b * (A ^ 2 - A₀ ^ 2) / k := div_nonneg hx hk0.le
    calc (A / A₀) ^ k ≤ (1 + b * (A ^ 2 - A₀ ^ 2) / k) ^ k :=
          pow_le_pow_left₀ (div_nonneg (by linarith) hA₀.le) hlin k
      _ ≤ Real.exp (b * (A ^ 2 - A₀ ^ 2) / k) ^ k :=
          pow_le_pow_left₀ (by linarith)
            (by linarith [Real.add_one_le_exp (b * (A ^ 2 - A₀ ^ 2) / k)]) k
      _ = Real.exp (b * (A ^ 2 - A₀ ^ 2)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp
  calc A ^ k * Real.exp (-b * A ^ 2)
      ≤ A₀ ^ k * Real.exp (b * (A ^ 2 - A₀ ^ 2)) * Real.exp (-b * A ^ 2) :=
        mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
    _ = A₀ ^ k * Real.exp (-b * A₀ ^ 2) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
theorem integrable_modelIntegrand_mul_saddleLinear_div (p S : ℂ) :
    Integrable fun w : ℝ ↦ modelIntegrand p (1 / 2) w
      * (saddleLinear (line (1 / 2) w - p) / S) := by
  have hhalf : (1 / 2 : ℝ) = (0 : ℤ) + 1 / 2 := by norm_num
  refine (((integrable_modelMomentIntegrand 1 p hhalf).const_mul (-(1 / 2) / S)).add
    ((integrable_modelMomentIntegrand 3 p hhalf).const_mul
      (-(2 * (π : ℂ) * I / 3) / S))).congr (.of_forall fun w ↦ ?_)
  simp only [Pi.add_apply, modelMomentIntegrand, saddleLinear]
  ring
theorem four_le_sqrt {t : ℝ} (ht : 16 ≤ t / (2 * π)) : 4 ≤ Real.sqrt (t / (2 * π)) :=
  Real.le_sqrt_of_sq_le (by nlinarith)
private theorem sq_sub_le {p : ℝ} (hκ : |1 / 2 - p| ≤ 1 / 2) : (1 / 2 - p) ^ 2 ≤ 1 / 4 := by
  nlinarith [sq_le_sq' (abs_le.1 hκ).1 (abs_le.1 hκ).2]
private theorem norm_line_sub_ofReal_sq_le_of_abs_le {p : ℝ} (hκ : |1 / 2 - p| ≤ 1 / 2) (w : ℝ) :
    ‖line (1 / 2) w - (p : ℂ)‖ ^ 2 ≤ 2 * (w + (1 / 2 - p) / 2) ^ 2 + 1 / 8 := by
  rw [norm_line_sub_ofReal_sq]
  linarith [sq_sub_le hκ]
private theorem pow_four_le {Y u : ℝ} (hQ : Y ^ 2 ≤ 2 * u ^ 2 + 1 / 8) :
    Y ^ 4 ≤ (2 * u ^ 2 + 1 / 8) ^ 2 :=
  (pow_le_pow_left₀ (sq_nonneg Y) hQ 2).trans_eq' (by ring)
private theorem discrepancy_weight_le {Y u : ℝ} (hQ : Y ^ 2 ≤ 2 * u ^ 2 + 1 / 8) :
    1 / 2 * Y ^ 2 + π * Y ^ 4 ≤ 1 / 16 + π / 64 + (1 + π / 2) * u ^ 2 + 4 * π * u ^ 4 := by
  have h4 : π * Y ^ 4 ≤ 4 * π * u ^ 4 + π / 2 * u ^ 2 + π / 64 := by
    have h := mul_le_mul_of_nonneg_left (pow_four_le hQ) Real.pi_pos.le
    nlinarith [h]
  linarith
private theorem exp_remainder_weight_le {Y u : ℝ} (hQ : Y ^ 2 ≤ 2 * u ^ 2 + 1 / 8) :
    Y ^ 2 + 8 * π / 3 * Y ^ 4 + 16 * π ^ 2 / 9 * Y ^ 6
      ≤ 1 / 8 + π / 24 + π ^ 2 / 288 + (2 + 4 * π / 3 + π ^ 2 / 6) * u ^ 2
        + (32 * π / 3 + 8 * π ^ 2 / 3) * u ^ 4 + 128 * π ^ 2 / 9 * u ^ 6 := by
  have h6 : Y ^ 6 ≤ (2 * u ^ 2 + 1 / 8) ^ 3 :=
    (pow_le_pow_left₀ (sq_nonneg Y) hQ 3).trans_eq' (by ring)
  have e4 : 8 * π / 3 * Y ^ 4 ≤ 8 * π / 3 * (2 * u ^ 2 + 1 / 8) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_four_le hQ) (by positivity)
  have e6 : 16 * π ^ 2 / 9 * Y ^ 6 ≤ 16 * π ^ 2 / 9 * (2 * u ^ 2 + 1 / 8) ^ 3 :=
    mul_le_mul_of_nonneg_left h6 (by positivity)
  nlinarith [e4, e6, hQ]
private theorem norm_modelIntegrand_mul_saddleDiscrepancy_sub_linear_le {t : ℝ} (ht : 0 < t)
    {ν : ℕ} {p S w : ℝ} (hS : S = Real.sqrt (t / (2 * π))) (hp : p = S - ν)
    (hκ : |1 / 2 - p| ≤ 1 / 2) (hu : ‖line (1 / 2) w - (p : ℂ)‖ ≤ S / 2) :
    ‖modelIntegrand (p : ℂ) (1 / 2) w
        * (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)
            - saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ))‖
      ≤ 11 / 5 / (Real.sqrt 2 * (t / (2 * π)))
          * (Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2)
              * (1 / 16 + π / 64 + (1 + π / 2) * (w + (1 / 2 - p) / 2) ^ 2
                  + 4 * π * (w + (1 / 2 - p) / 2) ^ 4)) := by
  subst hS
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hT0 : (0 : ℝ) < t / (2 * π) := by positivity
  have hxy := line_sub_ofReal_sub hp w
  have hx : ‖line ((ν : ℝ) + 1 / 2) w - ((Real.sqrt (t / (2 * π)) : ℝ) : ℂ)‖
      ≤ Real.sqrt (t / (2 * π)) / 2 := by rw [hxy]; exact hu
  have hd := norm_saddleDiscrepancy_sub_linear_le ht hx
  rw [hxy] at hd
  have h8 := norm_modelIntegrand_le_exp_neg_mul_sq hκ w
  set Y : ℝ := ‖line (1 / 2) w - (p : ℂ)‖ with hYdef
  set R : ℂ := saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)
    - saddleLinear (line (1 / 2) w - (p : ℂ)) / ((Real.sqrt (t / (2 * π)) : ℝ) : ℂ) with hRdef
  calc ‖modelIntegrand (p : ℂ) (1 / 2) w * R‖
      = ‖modelIntegrand (p : ℂ) (1 / 2) w‖ * ‖R‖ := norm_mul _ _
    _ ≤ Real.exp (π / 4) * Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) / Real.sqrt 2
          * ((1 / 2 * Y ^ 2 + π * Y ^ 4) / (t / (2 * π))) :=
        mul_le_mul h8 hd (norm_nonneg _) (by positivity)
    _ ≤ 11 / 5 * Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) / Real.sqrt 2
          * ((1 / 16 + π / 64 + (1 + π / 2) * (w + (1 / 2 - p) / 2) ^ 2
              + 4 * π * (w + (1 / 2 - p) / 2) ^ 4) / (t / (2 * π))) :=
        mul_le_mul
          ((div_le_div_iff_of_pos_right hs2).2
            (mul_le_mul_of_nonneg_right Real.exp_pi_div_four_le (Real.exp_nonneg _)))
          ((div_le_div_iff_of_pos_right hT0).2
            (discrepancy_weight_le (norm_line_sub_ofReal_sq_le_of_abs_le hκ w)))
          (div_nonneg (by positivity) hT0.le) (by positivity)
    _ = _ := by field_simp
private theorem norm_modelIntegrand_mul_exp_sub_one_sub_self_le {t : ℝ} (ht : 0 < t)
    {ν : ℕ} {p S w : ℝ} (hS : S = Real.sqrt (t / (2 * π))) (hp : p = S - ν)
    (hκ : |1 / 2 - p| ≤ 1 / 2) (hu : ‖line (1 / 2) w - (p : ℂ)‖ ≤ S / 2) :
    ‖modelIntegrand (p : ℂ) (1 / 2) w
        * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1
            - saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w))‖
      ≤ 47 / 10 / (2 * Real.sqrt 2 * (t / (2 * π)))
          * (Real.exp (-(8 * π / 3) * (w + (1 / 2 - p) / 2) ^ 2)
              * (1 / 8 + π / 24 + π ^ 2 / 288
                  + (2 + 4 * π / 3 + π ^ 2 / 6) * (w + (1 / 2 - p) / 2) ^ 2
                  + (32 * π / 3 + 8 * π ^ 2 / 3) * (w + (1 / 2 - p) / 2) ^ 4
                  + 128 * π ^ 2 / 9 * (w + (1 / 2 - p) / 2) ^ 6)) := by
  subst hS
  have hpi := Real.pi_pos
  have hhalf : (1 / 2 : ℝ) = (0 : ℤ) + 1 / 2 := by norm_num
  have hT0 : (0 : ℝ) < t / (2 * π) := by positivity
  have hTS : Real.sqrt (t / (2 * π)) ^ 2 = t / (2 * π) := Real.sq_sqrt hT0.le
  have hxy := line_sub_ofReal_sub hp w
  have hx : ‖line ((ν : ℝ) + 1 / 2) w - ((Real.sqrt (t / (2 * π)) : ℝ) : ℂ)‖
      ≤ Real.sqrt (t / (2 * π)) / 2 := by rw [hxy]; exact hu
  have hd1 := norm_saddleDiscrepancy_le ht hx
  have hd3 := exp_norm_saddleDiscrepancy_mul_exp_le ht hx
  rw [hxy] at hd1 hd3
  have hsq := sq_sub_le hκ
  have h8 : ‖modelIntegrand (p : ℂ) (1 / 2) w‖
      ≤ Real.exp (2 * π * (1 / 2 - p) ^ 2)
        * Real.exp (-(2 * π) * ‖line (1 / 2) w - (p : ℂ)‖ ^ 2) / Real.sqrt 2 := by
    refine (norm_modelIntegrand_le (p : ℂ) hhalf w).trans ?_
    rw [norm_exp_two_pi_mul_I_mul_line_sub_sq' p w]
  have hΔsq : ‖saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)‖ ^ 2
      ≤ (‖line (1 / 2) w - (p : ℂ)‖ ^ 2 + 8 * π / 3 * ‖line (1 / 2) w - (p : ℂ)‖ ^ 4
          + 16 * π ^ 2 / 9 * ‖line (1 / 2) w - (p : ℂ)‖ ^ 6) / (t / (2 * π)) := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hd1 2
    rw [div_pow, hTS] at h
    refine h.trans_eq ?_
    congr 1
    ring
  have hEc : Real.exp (2 * π * (1 / 2 - p) ^ 2)
      * (Real.exp (1 / 2) * Real.exp (-(2 * π / 3) * (1 / 2 - p) ^ 2)) ≤ 47 / 10 := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact (Real.exp_le_exp.2 (by nlinarith)).trans Real.exp_half_add_pi_div_three_le
  have hsplit : Real.exp (-(4 * π / 3) * ‖line (1 / 2) w - (p : ℂ)‖ ^ 2)
      = Real.exp (-(2 * π / 3) * (1 / 2 - p) ^ 2)
        * Real.exp (-(8 * π / 3) * (w + (1 / 2 - p) / 2) ^ 2) := by
    rw [← Real.exp_add, norm_line_sub_ofReal_sq]
    congr 1
    ring
  set Y : ℝ := ‖line (1 / 2) w - (p : ℂ)‖ with hYdef
  set D : ℂ := saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w) with hDdef
  calc ‖modelIntegrand (p : ℂ) (1 / 2) w * (exp D - 1 - D)‖
      = ‖modelIntegrand (p : ℂ) (1 / 2) w‖ * ‖exp D - 1 - D‖ := norm_mul _ _
    _ ≤ Real.exp (2 * π * (1 / 2 - p) ^ 2) * Real.exp (-(2 * π) * Y ^ 2) / Real.sqrt 2
          * (‖D‖ ^ 2 / 2 * Real.exp ‖D‖) :=
        mul_le_mul h8 (Complex.norm_exp_sub_one_sub_id_le' _) (norm_nonneg _) (by positivity)
    _ = Real.exp (2 * π * (1 / 2 - p) ^ 2) / (2 * Real.sqrt 2) * ‖D‖ ^ 2
          * (Real.exp ‖D‖ * Real.exp (-(2 * π) * Y ^ 2)) := by ring
    _ ≤ Real.exp (2 * π * (1 / 2 - p) ^ 2) / (2 * Real.sqrt 2)
          * ((Y ^ 2 + 8 * π / 3 * Y ^ 4 + 16 * π ^ 2 / 9 * Y ^ 6) / (t / (2 * π)))
          * (Real.exp (1 / 2) * Real.exp (-(4 * π / 3) * Y ^ 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hΔsq (by positivity)) hd3 (by positivity)
          (mul_nonneg (by positivity) (div_nonneg (by positivity) hT0.le))
    _ = Real.exp (2 * π * (1 / 2 - p) ^ 2)
          * (Real.exp (1 / 2) * Real.exp (-(2 * π / 3) * (1 / 2 - p) ^ 2)) / (2 * Real.sqrt 2)
          * ((Y ^ 2 + 8 * π / 3 * Y ^ 4 + 16 * π ^ 2 / 9 * Y ^ 6) / (t / (2 * π)))
          * Real.exp (-(8 * π / 3) * (w + (1 / 2 - p) / 2) ^ 2) := by
        rw [hsplit]
        ring
    _ ≤ 47 / 10 / (2 * Real.sqrt 2)
          * ((1 / 8 + π / 24 + π ^ 2 / 288
              + (2 + 4 * π / 3 + π ^ 2 / 6) * (w + (1 / 2 - p) / 2) ^ 2
              + (32 * π / 3 + 8 * π ^ 2 / 3) * (w + (1 / 2 - p) / 2) ^ 4
              + 128 * π ^ 2 / 9 * (w + (1 / 2 - p) / 2) ^ 6) / (t / (2 * π)))
          * Real.exp (-(8 * π / 3) * (w + (1 / 2 - p) / 2) ^ 2) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul ?_ ?_ ?_ ?_) (Real.exp_nonneg _)
        · exact (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * Real.sqrt 2)).2 hEc
        · exact (div_le_div_iff_of_pos_right hT0).2
            (exp_remainder_weight_le (norm_line_sub_ofReal_sq_le_of_abs_le hκ w))
        · exact div_nonneg (by positivity) hT0.le
        · positivity
    _ = _ := by field_simp
private theorem sharp_inner_constant_le :
    11 / 5 * (1 / 2 * (1 / 8 + π / 64 + 5 / (16 * π)))
      + 47 / 20 * ((π ^ 3 + 21 * π ^ 2 + 189 * π + 837) / (288 * π)) * Real.sqrt (3 / 8)
      ≤ 299 / 100 := by
  have hπ1 : (3.1415 : ℝ) < π := Real.pi_gt_d4
  have hπ2 : π < 3.1416 := Real.pi_lt_d4
  have hs : Real.sqrt (3 / 8) ≤ 0.6124 := by
    rw [show (0.6124 : ℝ) = Real.sqrt (0.6124 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hA : 11 / 5 * (1 / 2 * (1 / 8 + π / 64 + 5 / (16 * π))) ≤ 0.3010 := by
    have h1 : (5 : ℝ) / (16 * π) ≤ 5 / (16 * 3.1415) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    linarith
  have hBR : (π ^ 3 + 21 * π ^ 2 + 189 * π + 837) / (288 * π) ≤ 1.845 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hprod : (π ^ 3 + 21 * π ^ 2 + 189 * π + 837) / (288 * π) * Real.sqrt (3 / 8)
      ≤ 1.845 * 0.6124 :=
    mul_le_mul hBR hs (Real.sqrt_nonneg _) (by norm_num)
  linarith
theorem norm_integral_inner_sub_linear_le {t : ℝ} (ht : 16 ≤ t / (2 * π)) {ν : ℕ}
    (hν : (ν : ℝ) ≤ Real.sqrt (t / (2 * π)))
    (hν' : Real.sqrt (t / (2 * π)) ≤ ν + 1) :
    ‖(1 + I) * ∫ w in Set.Icc (-sharpSplitRadius t) (sharpSplitRadius t),
        modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
          * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1
              - saddleLinear (line (1 / 2) w - ((Real.sqrt (t / (2 * π)) - ν : ℝ) : ℂ))
                  / ((Real.sqrt (t / (2 * π)) : ℝ) : ℂ))‖
      ≤ 299 / 100 / (t / (2 * π)) := by
  have hT0 : (0 : ℝ) < t / (2 * π) := lt_of_lt_of_le (by norm_num) ht
  have ht0 : 0 < t := (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * π)).mp hT0
  have hhalf : (1 / 2 : ℝ) = (0 : ℤ) + 1 / 2 := by norm_num
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  set W : ℝ := sharpSplitRadius t with hWdef
  set S : ℝ := Real.sqrt (t / (2 * π)) with hSdef
  set p : ℝ := S - (ν : ℝ) with hpdef
  clear_value p S W
  have hS4 : 4 ≤ S := by rw [hSdef]; exact four_le_sqrt ht
  have hW : W = (S - 1) / (2 * Real.sqrt 2) := by rw [hWdef, hSdef, sharpSplitRadius]
  have hκ : |1 / 2 - p| ≤ 1 / 2 := by
    rw [abs_le, hpdef]
    constructor <;> linarith
  have hy : ∀ w ∈ Set.Icc (-W) W, ‖line (1 / 2) w - (p : ℂ)‖ ≤ S / 2 := fun w hw ↦ by
    have habs : |w| ≤ W := abs_le.2 ⟨hw.1, hw.2⟩
    rw [hW, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt 2)] at habs
    exact (norm_line_sub_ofReal_le (1 / 2) w p).trans
      (by linarith [(abs_le.1 hκ).1, (abs_le.1 hκ).2])
  set maj : ℝ → ℝ := fun w ↦
    11 / 5 / (Real.sqrt 2 * (t / (2 * π))) *
      (Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) *
        (1 / 16 + π / 64 + (1 + π / 2) * (w + (1 / 2 - p) / 2) ^ 2
          + 4 * π * (w + (1 / 2 - p) / 2) ^ 4))
    + 47 / 10 / (2 * Real.sqrt 2 * (t / (2 * π))) *
      (Real.exp (-(8 * π / 3) * (w + (1 / 2 - p) / 2) ^ 2) *
        (1 / 8 + π / 24 + π ^ 2 / 288
          + (2 + 4 * π / 3 + π ^ 2 / 6) * (w + (1 / 2 - p) / 2) ^ 2
          + (32 * π / 3 + 8 * π ^ 2 / 3) * (w + (1 / 2 - p) / 2) ^ 4
          + 128 * π ^ 2 / 9 * (w + (1 / 2 - p) / 2) ^ 6)) with hmajdef
  clear_value maj
  have hc1 : (0 : ℝ) < 11 / 5 / (Real.sqrt 2 * (t / (2 * π))) :=
    div_pos (by norm_num) (mul_pos hs2 hT0)
  have hc2 : (0 : ℝ) < 47 / 10 / (2 * Real.sqrt 2 * (t / (2 * π))) :=
    div_pos (by norm_num) (by positivity)
  have hmaj0 : ∀ w : ℝ, 0 ≤ maj w := fun w ↦ by
    rw [hmajdef]
    exact add_nonneg (mul_nonneg hc1.le (by positivity)) (mul_nonneg hc2.le (by positivity))
  have hint1 : Integrable fun w : ℝ ↦ 11 / 5 / (Real.sqrt 2 * (t / (2 * π))) *
      (Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) *
        (1 / 16 + π / 64 + (1 + π / 2) * (w + (1 / 2 - p) / 2) ^ 2
          + 4 * π * (w + (1 / 2 - p) / 2) ^ 4)) :=
    ((integrable_exp_neg_mul_sq_mul_even_quartic (b := 4 * π) (by positivity) _ _
      _).comp_add_right _).const_mul _
  have hint2 : Integrable fun w : ℝ ↦ 47 / 10 / (2 * Real.sqrt 2 * (t / (2 * π))) *
      (Real.exp (-(8 * π / 3) * (w + (1 / 2 - p) / 2) ^ 2) *
        (1 / 8 + π / 24 + π ^ 2 / 288
          + (2 + 4 * π / 3 + π ^ 2 / 6) * (w + (1 / 2 - p) / 2) ^ 2
          + (32 * π / 3 + 8 * π ^ 2 / 3) * (w + (1 / 2 - p) / 2) ^ 4
          + 128 * π ^ 2 / 9 * (w + (1 / 2 - p) / 2) ^ 6)) :=
    ((integrable_exp_neg_mul_sq_mul_even_poly (b := 8 * π / 3) (by positivity) _ _ _
      _).comp_add_right _).const_mul _
  have hmajint : Integrable maj := by rw [hmajdef]; exact hint1.add hint2
  have hsqrt1 : Real.sqrt (π / (4 * π)) = 1 / 2 := by
    rw [show π / (4 * π) = (1 / 2 : ℝ) ^ 2 by rw [div_eq_iff (by positivity)]; ring,
      Real.sqrt_sq (by norm_num)]
  have hsqrt2 : Real.sqrt (π / (8 * π / 3)) = Real.sqrt (3 / 8) := by
    rw [show π / (8 * π / 3) = (3 : ℝ) / 8 by rw [div_eq_iff (by positivity)]; ring]
  have hmajval : ∫ w : ℝ, maj w
      = 11 / 5 / (Real.sqrt 2 * (t / (2 * π))) * (1 / 2 * (1 / 8 + π / 64 + 5 / (16 * π)))
        + 47 / 10 / (2 * Real.sqrt 2 * (t / (2 * π)))
          * ((π ^ 3 + 21 * π ^ 2 + 189 * π + 837) / (288 * π) * Real.sqrt (3 / 8)) := by
    rw [hmajdef, integral_add hint1 hint2, integral_const_mul, integral_const_mul,
      integral_exp_neg_mul_sq_mul_even_quartic_comp_add_right
        (by positivity : (0 : ℝ) < 4 * π),
      integral_exp_neg_mul_sq_mul_even_poly_comp_add_right
        (by positivity : (0 : ℝ) < 8 * π / 3), hsqrt1, hsqrt2]
    have hπ0 : π ≠ 0 := Real.pi_ne_zero
    have hs2' : Real.sqrt 2 ≠ 0 := hs2.ne'
    have hT0' : t / (2 * π) ≠ 0 := hT0.ne'
    field_simp
    ring
  have hExp : Integrable fun w : ℝ ↦ modelIntegrand (p : ℂ) (1 / 2) w
      * exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) := by
    have h := integrable_modelIntegrand_mul_exp_saddleDiscrepancy ht0 ν
    rwa [← hSdef, ← hpdef] at h
  have hLin := integrable_modelIntegrand_mul_saddleLinear_div (p : ℂ) (S : ℂ)
  have hFint : Integrable fun w : ℝ ↦ modelIntegrand (p : ℂ) (1 / 2) w
      * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1
          - saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ)) :=
    (((hExp.sub (integrable_modelIntegrand (p : ℂ) hhalf)).sub hLin)).congr
      (.of_forall fun w ↦ by simp only [Pi.sub_apply]; ring)
  have key : ∀ w ∈ Set.Icc (-W) W, ‖modelIntegrand (p : ℂ) (1 / 2) w
      * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1
          - saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ))‖ ≤ maj w := by
    intro w hw
    have hu := hy w hw
    rw [show modelIntegrand (p : ℂ) (1 / 2) w
          * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1
              - saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ))
        = modelIntegrand (p : ℂ) (1 / 2) w
            * (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)
                - saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ))
          + modelIntegrand (p : ℂ) (1 / 2) w
            * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1
                - saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) by ring, hmajdef]
    exact (norm_add_le _ _).trans (add_le_add
      (norm_modelIntegrand_mul_saddleDiscrepancy_sub_linear_le ht0 hSdef hpdef hκ hu)
      (norm_modelIntegrand_mul_exp_sub_one_sub_self_le ht0 hSdef hpdef hκ hu))
  calc ‖(1 + I) * ∫ w in Set.Icc (-W) W, modelIntegrand (p : ℂ) (1 / 2) w
        * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1
            - saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ))‖
      ≤ Real.sqrt 2 * ∫ w in Set.Icc (-W) W, ‖modelIntegrand (p : ℂ) (1 / 2) w
          * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1
              - saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ))‖ :=
        norm_one_add_I_mul_integral_le _
    _ ≤ Real.sqrt 2 * ∫ w in Set.Icc (-W) W, maj w :=
        mul_le_mul_of_nonneg_left (setIntegral_mono_on hFint.norm.integrableOn
          hmajint.integrableOn measurableSet_Icc key) hs2.le
    _ ≤ Real.sqrt 2 * ∫ w : ℝ, maj w :=
        mul_le_mul_of_nonneg_left (setIntegral_le_integral hmajint (.of_forall hmaj0)) hs2.le
    _ = (11 / 5 * (1 / 2 * (1 / 8 + π / 64 + 5 / (16 * π)))
          + 47 / 20 * ((π ^ 3 + 21 * π ^ 2 + 189 * π + 837) / (288 * π)) * Real.sqrt (3 / 8))
            / (t / (2 * π)) := by
        rw [hmajval]
        field_simp
        ring
    _ ≤ 299 / 100 / (t / (2 * π)) := by
        gcongr
        exact sharp_inner_constant_le
end Zeta.RiemannSiegel
end
end CertificatePort112


section CertificatePort113
section
open Complex MeasureTheory
open scoped Real
namespace Zeta.RiemannSiegel
private theorem norm_modelIntegrand_mul_saddleLinear_le {p : ℝ} (hκ : |1 / 2 - p| ≤ 1 / 2)
    (w : ℝ) :
    ‖modelIntegrand (p : ℂ) (1 / 2) w * saddleLinear (line (1 / 2) w - (p : ℂ))‖
      ≤ 11 / 5 / Real.sqrt 2 * (Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2)
          * (27 / 100 + 182 / 100 * |w + (1 / 2 - p) / 2|
              + 445 / 100 * (w + (1 / 2 - p) / 2) ^ 2
              + 593 / 100 * |w + (1 / 2 - p) / 2| ^ 3)) := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hs2u : Real.sqrt 2 ≤ 1.41422 := sqrt_two_le
  have hπu : π ≤ 3.1416 := Real.pi_lt_d4.le
  have hsp : Real.sqrt 2 * π ≤ 1.41422 * 3.1416 :=
    mul_le_mul hs2u hπu Real.pi_pos.le (by norm_num)
  set u : ℝ := w + (1 / 2 - p) / 2 with hu
  have hu0 : (0 : ℝ) ≤ |u| := abs_nonneg u
  have husq : |u| ^ 2 = u ^ 2 := sq_abs u
  have h8 : ‖modelIntegrand (p : ℂ) (1 / 2) w‖
      ≤ 11 / 5 / Real.sqrt 2 * Real.exp (-(4 * π) * u ^ 2) :=
    (norm_modelIntegrand_le_exp_neg_mul_sq hκ w).trans (by
      rw [← hu, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hs2]
      exact mul_le_mul_of_nonneg_right Real.exp_pi_div_four_le (Real.exp_nonneg _))
  have hY : ‖line (1 / 2) w - (p : ℂ)‖ ≤ Real.sqrt 2 * |u| + Real.sqrt 2 / 4 := by
    refine (norm_line_sub_ofReal_le' (1 / 2) w p).trans ?_
    rw [show Real.sqrt 2 * |u| + Real.sqrt 2 / 4 = Real.sqrt 2 * (|u| + 1 / 4) by ring]
    exact mul_le_mul_of_nonneg_left (by rw [hu]; linarith) hs2.le
  have hcubic : ‖line (1 / 2) w - (p : ℂ)‖ / 2 + 2 * π / 3 * ‖line (1 / 2) w - (p : ℂ)‖ ^ 3
      ≤ 27 / 100 + 182 / 100 * |u| + 445 / 100 * |u| ^ 2 + 593 / 100 * |u| ^ 3 := by
    have hY0 : (0 : ℝ) ≤ ‖line (1 / 2) w - (p : ℂ)‖ := norm_nonneg _
    have hs2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hcube : ‖line (1 / 2) w - (p : ℂ)‖ ^ 3
        ≤ 2 * Real.sqrt 2 * (|u| ^ 3 + 3 / 4 * |u| ^ 2 + 3 / 16 * |u| + 1 / 64) := by
      refine (pow_le_pow_left₀ hY0 hY 3).trans (le_of_eq ?_)
      rw [show (Real.sqrt 2 * |u| + Real.sqrt 2 / 4) ^ 3
          = Real.sqrt 2 * Real.sqrt 2 ^ 2
            * (|u| ^ 3 + 3 / 4 * |u| ^ 2 + 3 / 16 * |u| + 1 / 64) by ring, hs2sq]
      ring
    have hcube' : 2 * π / 3 * ‖line (1 / 2) w - (p : ℂ)‖ ^ 3
        ≤ 4 * Real.sqrt 2 * π / 3 * |u| ^ 3 + Real.sqrt 2 * π * |u| ^ 2
          + Real.sqrt 2 * π / 4 * |u| + Real.sqrt 2 * π / 48 := by
      have h := mul_le_mul_of_nonneg_left hcube (by positivity : (0 : ℝ) ≤ 2 * π / 3)
      calc 2 * π / 3 * ‖line (1 / 2) w - (p : ℂ)‖ ^ 3
          ≤ 2 * π / 3 * (2 * Real.sqrt 2
              * (|u| ^ 3 + 3 / 4 * |u| ^ 2 + 3 / 16 * |u| + 1 / 64)) := h
        _ = _ := by ring
    have hc0 : Real.sqrt 2 / 8 + Real.sqrt 2 * π / 48 ≤ 27 / 100 := by linarith
    have hc1 : Real.sqrt 2 / 2 + Real.sqrt 2 * π / 4 ≤ 182 / 100 := by linarith
    have hc2 : Real.sqrt 2 * π ≤ 445 / 100 := by linarith
    have hc3 : 4 * Real.sqrt 2 * π / 3 ≤ 593 / 100 := by linarith
    have p1 := mul_le_mul_of_nonneg_right hc1 hu0
    have p2 := mul_le_mul_of_nonneg_right hc2 (sq_nonneg |u|)
    have p3 := mul_le_mul_of_nonneg_right hc3 (pow_nonneg hu0 3)
    linarith
  calc ‖modelIntegrand (p : ℂ) (1 / 2) w * saddleLinear (line (1 / 2) w - (p : ℂ))‖
      = ‖modelIntegrand (p : ℂ) (1 / 2) w‖ * ‖saddleLinear (line (1 / 2) w - (p : ℂ))‖ :=
        norm_mul _ _
    _ ≤ 11 / 5 / Real.sqrt 2 * Real.exp (-(4 * π) * u ^ 2)
          * (27 / 100 + 182 / 100 * |u| + 445 / 100 * |u| ^ 2 + 593 / 100 * |u| ^ 3) :=
        mul_le_mul h8 ((norm_saddleLinear_le _).trans hcubic) (norm_nonneg _) (by positivity)
    _ = _ := by rw [husq]; ring
private theorem le_sharpSplitRadius_sub_quarter {t : ℝ} (ht : 16 ≤ t / (2 * π)) :
    81 / 100 ≤ sharpSplitRadius t - 1 / 4 := by
  have hs2u : Real.sqrt 2 ≤ 1.41422 := sqrt_two_le
  have hS4 : 4 ≤ Real.sqrt (t / (2 * π)) := four_le_sqrt ht
  rw [sharpSplitRadius, le_sub_iff_add_le, le_div_iff₀ (by positivity)]
  linarith
private theorem linear_tail_constant_le {S A : ℝ} (hS : 0 ≤ S) (hA : 81 / 100 ≤ A)
    (hSA : S ≤ 5 * A) :
    S * (Real.exp (-(4 * π) * A ^ 2)
        * (27 / 100 / A + 182 / 100 + 2 * (445 / 100) * A + 2 * (593 / 100) * A ^ 2))
      ≤ π / 110 := by
  have hπ : (3.14 : ℝ) ≤ π := by linarith [Real.pi_gt_d4]
  have hA0 : (0 : ℝ) < A := by linarith
  have hP : 27 / 100 / A + 182 / 100 + 2 * (445 / 100) * A + 2 * (593 / 100) * A ^ 2
      ≤ 27 * A ^ 2 := by
    have h1 : 27 / 100 / A ≤ 1 / 3 := by
      rw [div_le_div_iff₀ hA0 (by norm_num)]
      linarith
    nlinarith [mul_nonneg (sub_nonneg.2 hA) hA0.le]
  have hmono : A ^ 3 * Real.exp (-(4 * π) * A ^ 2)
      ≤ (81 / 100 : ℝ) ^ 3 * Real.exp (-(4 * π) * (81 / 100 : ℝ) ^ 2) :=
    pow_mul_exp_neg_mul_sq_le (by positivity) (by norm_num) (by push_cast; nlinarith) hA
  have hnum : 135 * ((81 / 100 : ℝ) ^ 3 * Real.exp (-(4 * π) * (81 / 100 : ℝ) ^ 2))
      ≤ π / 110 := by
    have hthr : Real.exp (-(4 * π) * (81 / 100 : ℝ) ^ 2) * 2900 ≤ 1 := by
      rw [show -(4 * π) * (81 / 100 : ℝ) ^ 2 = -(4 * π * (81 / 100 : ℝ) ^ 2) by ring]
      exact exp_neg_mul_le_one (n := 8) (by norm_num) (by push_cast; nlinarith)
    nlinarith [Real.exp_pos (-(4 * π) * (81 / 100 : ℝ) ^ 2)]
  calc S * (Real.exp (-(4 * π) * A ^ 2)
        * (27 / 100 / A + 182 / 100 + 2 * (445 / 100) * A + 2 * (593 / 100) * A ^ 2))
      ≤ S * (Real.exp (-(4 * π) * A ^ 2) * (27 * A ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP (Real.exp_pos _).le) hS
    _ ≤ 5 * A * (Real.exp (-(4 * π) * A ^ 2) * (27 * A ^ 2)) :=
        mul_le_mul_of_nonneg_right hSA (by positivity)
    _ = 135 * (A ^ 3 * Real.exp (-(4 * π) * A ^ 2)) := by ring
    _ ≤ 135 * ((81 / 100 : ℝ) ^ 3 * Real.exp (-(4 * π) * (81 / 100 : ℝ) ^ 2)) := by gcongr
    _ ≤ π / 110 := hnum
theorem norm_integral_linear_tail_le {t : ℝ} (ht : 16 ≤ t / (2 * π)) {ν : ℕ}
    (hν : (ν : ℝ) ≤ Real.sqrt (t / (2 * π)))
    (hν' : Real.sqrt (t / (2 * π)) ≤ ν + 1) :
    ‖(1 + I) * ∫ w in (Set.Icc (-sharpSplitRadius t) (sharpSplitRadius t))ᶜ,
        modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
          * (saddleLinear (line (1 / 2) w - ((Real.sqrt (t / (2 * π)) - ν : ℝ) : ℂ))
              / ((Real.sqrt (t / (2 * π)) : ℝ) : ℂ))‖
      ≤ 1 / 200 / (t / (2 * π)) := by
  have hT0 : (0 : ℝ) < t / (2 * π) := lt_of_lt_of_le (by norm_num) ht
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hs2u : Real.sqrt 2 ≤ 1.41422 := sqrt_two_le
  have hπ : (3.14 : ℝ) ≤ π := by linarith [Real.pi_gt_d4]
  have hA81 : 81 / 100 ≤ sharpSplitRadius t - 1 / 4 := le_sharpSplitRadius_sub_quarter ht
  have hS4 : 4 ≤ Real.sqrt (t / (2 * π)) := four_le_sqrt ht
  set W : ℝ := sharpSplitRadius t with hWdef
  set S : ℝ := Real.sqrt (t / (2 * π)) with hSdef
  set p : ℝ := S - (ν : ℝ) with hpdef
  have hW : W = (S - 1) / (2 * Real.sqrt 2) := by rw [hWdef, hSdef, sharpSplitRadius]
  have hTS : S ^ 2 = t / (2 * π) := by rw [hSdef]; exact Real.sq_sqrt hT0.le
  clear_value p S W
  have hS0 : (0 : ℝ) < S := by linarith
  have hκ : |1 / 2 - p| ≤ 1 / 2 := by
    rw [abs_le, hpdef]
    constructor <;> linarith
  set A : ℝ := W - 1 / 4 with hAdef
  have hA0 : (0 : ℝ) < A := by linarith
  have hAW : A + |(1 / 2 - p) / 2| ≤ W := by
    rw [hAdef, abs_div, abs_two]
    linarith
  have hbA : (1 : ℝ) ≤ 4 * π * A ^ 2 := by nlinarith
  have hSA : S ≤ 5 * A := by
    have hkey : (S + 5 / 4) * (2 * Real.sqrt 2) ≤ 5 * (S - 1) := by
      nlinarith [mul_le_mul_of_nonneg_right hs2u hS0.le]
    have h5 : S + 5 / 4 ≤ 5 * ((S - 1) / (2 * Real.sqrt 2)) := by
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      linarith
    rw [hAdef, hW]
    linarith
  set maj : ℝ → ℝ := fun w ↦ 11 / 5 / Real.sqrt 2 *
    (Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) *
      (27 / 100 + 182 / 100 * |w + (1 / 2 - p) / 2|
        + 445 / 100 * (w + (1 / 2 - p) / 2) ^ 2
        + 593 / 100 * |w + (1 / 2 - p) / 2| ^ 3)) with hmajdef
  have hmajint : Integrable maj := by
    rw [hmajdef]
    exact ((integrable_exp_neg_mul_sq_mul_poly (b := 4 * π) (by positivity) _ _ _
      _).comp_add_right _).const_mul _
  clear_value maj
  have hFint := integrable_modelIntegrand_mul_saddleLinear_div (p : ℂ) (S : ℂ)
  have key : ∀ w ∈ (Set.Icc (-W) W)ᶜ, ‖modelIntegrand (p : ℂ) (1 / 2) w
      * (saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ))‖ ≤ maj w / S := by
    intro w _
    rw [show modelIntegrand (p : ℂ) (1 / 2) w
          * (saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ))
        = modelIntegrand (p : ℂ) (1 / 2) w * saddleLinear (line (1 / 2) w - (p : ℂ))
            / (S : ℂ) by ring, norm_div, Complex.norm_real, Real.norm_of_nonneg hS0.le,
      div_le_div_iff_of_pos_right hS0]
    simp only [hmajdef]
    exact norm_modelIntegrand_mul_saddleLinear_le hκ w
  have htail : ∫ w in (Set.Icc (-W) W)ᶜ, maj w
      ≤ 11 / 5 / Real.sqrt 2 * (Real.exp (-(4 * π) * A ^ 2) / (4 * π)
          * (27 / 100 / A + 182 / 100 + 2 * (445 / 100) * A + 2 * (593 / 100) * A ^ 2)) := by
    simp only [hmajdef]
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact integral_compl_Icc_exp_neg_mul_sq_mul_poly_comp_add_right_le (b := 4 * π)
      (by positivity) hA0 hAW hbA (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  calc ‖(1 + I) * ∫ w in (Set.Icc (-W) W)ᶜ, modelIntegrand (p : ℂ) (1 / 2) w
        * (saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ))‖
      ≤ Real.sqrt 2 * ∫ w in (Set.Icc (-W) W)ᶜ, ‖modelIntegrand (p : ℂ) (1 / 2) w
          * (saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ))‖ :=
        norm_one_add_I_mul_integral_le _
    _ ≤ Real.sqrt 2 * ∫ w in (Set.Icc (-W) W)ᶜ, maj w / S :=
        mul_le_mul_of_nonneg_left (setIntegral_mono_on hFint.norm.integrableOn
          (hmajint.div_const S).integrableOn measurableSet_Icc.compl key) hs2.le
    _ = Real.sqrt 2 * (∫ w in (Set.Icc (-W) W)ᶜ, maj w) / S := by
        rw [integral_div]
        ring
    _ ≤ Real.sqrt 2 * (11 / 5 / Real.sqrt 2 * (Real.exp (-(4 * π) * A ^ 2) / (4 * π)
          * (27 / 100 / A + 182 / 100 + 2 * (445 / 100) * A + 2 * (593 / 100) * A ^ 2))) / S := by
        gcongr
    _ = 11 / (20 * π) * (S * (Real.exp (-(4 * π) * A ^ 2)
          * (27 / 100 / A + 182 / 100 + 2 * (445 / 100) * A + 2 * (593 / 100) * A ^ 2)))
            / S ^ 2 := by
        field_simp
        ring
    _ ≤ 1 / 200 / S ^ 2 := by
        gcongr
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < 20 * π)]
        linarith [linear_tail_constant_le hS0.le (by linarith) hSA]
    _ = 1 / 200 / (t / (2 * π)) := by rw [hTS]
theorem norm_integral_linear_add_iteratedDeriv_three_modelIntegral_le {t : ℝ}
    (ht : 16 ≤ t / (2 * π)) {ν : ℕ} (hν : (ν : ℝ) ≤ Real.sqrt (t / (2 * π)))
    (hν' : Real.sqrt (t / (2 * π)) ≤ ν + 1) :
    ‖(1 + I) * (∫ w in Set.Icc (-sharpSplitRadius t) (sharpSplitRadius t),
          modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
            * (saddleLinear (line (1 / 2) w - ((Real.sqrt (t / (2 * π)) - ν : ℝ) : ℂ))
                / ((Real.sqrt (t / (2 * π)) : ℝ) : ℂ)))
        + iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2))
            ((Real.sqrt (t / (2 * π)) - ν : ℝ)) / (96 * (π : ℂ) ^ 2)
          / ((Real.sqrt (t / (2 * π)) : ℝ) : ℂ)‖
      ≤ 1 / 200 / (t / (2 * π)) := by
  have hhalf : (1 / 2 : ℝ) = (0 : ℤ) + 1 / 2 := by norm_num
  set S : ℝ := Real.sqrt (t / (2 * π)) with hSdef
  set p : ℝ := S - (ν : ℝ) with hpdef
  set W : ℝ := sharpSplitRadius t with hWdef
  set F : ℝ → ℂ := fun w ↦ modelIntegrand (p : ℂ) (1 / 2) w
    * (saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ)) with hFdef
  have hFeq : ∀ w : ℝ, F w = -(1 / 2) / (S : ℂ) * modelMomentIntegrand 1 (p : ℂ) (1 / 2) w
      + -(2 * (π : ℂ) * I / 3) / (S : ℂ) * modelMomentIntegrand 3 (p : ℂ) (1 / 2) w := fun w ↦ by
    rw [hFdef]
    simp only [modelMomentIntegrand, saddleLinear]
    ring
  have h1 := integrable_modelMomentIntegrand 1 (p : ℂ) hhalf
  have h3 := integrable_modelMomentIntegrand 3 (p : ℂ) hhalf
  have hFint : Integrable F := integrable_modelIntegrand_mul_saddleLinear_div (p : ℂ) (S : ℂ)
  have hfull : (1 + I) * ∫ w : ℝ, F w
      = -(iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ) / (96 * (π : ℂ) ^ 2))
          / (S : ℂ) := by
    rw [funext hFeq, integral_add (h1.const_mul _) (h3.const_mul _), integral_const_mul,
      integral_const_mul,
      show (1 + I) * ((-(1 / 2) / (S : ℂ) * ∫ w : ℝ, modelMomentIntegrand 1 (p : ℂ) (1 / 2) w)
            + -(2 * (π : ℂ) * I / 3) / (S : ℂ) * ∫ w : ℝ, modelMomentIntegrand 3 (p : ℂ) (1 / 2) w)
          = (-(1 / 2) * modelMoment 1 (p : ℂ) (1 / 2)
              - 2 * (π : ℂ) * I / 3 * modelMoment 3 (p : ℂ) (1 / 2)) / (S : ℂ) by
        simp only [modelMoment]; ring,
      neg_half_modelMoment_one_sub_eq (p : ℂ) hhalf]
    ring
  have hsplit : (∫ w in Set.Icc (-W) W, F w) + ∫ w in (Set.Icc (-W) W)ᶜ, F w = ∫ w : ℝ, F w :=
    integral_add_compl measurableSet_Icc hFint
  have hrewrite : (1 + I) * (∫ w in Set.Icc (-W) W, F w)
      + iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ) / (96 * (π : ℂ) ^ 2)
        / (S : ℂ) = -((1 + I) * ∫ w in (Set.Icc (-W) W)ᶜ, F w) := by
    rw [← hsplit] at hfull
    linear_combination hfull
  rw [hrewrite, norm_neg]
  exact norm_integral_linear_tail_le ht hν hν'
end Zeta.RiemannSiegel
end
end CertificatePort113


section CertificatePort114
section
open Complex
open scoped Real
namespace Zeta.RiemannSiegel
noncomputable def lineArg (r : ℝ) : ℝ := Real.arctan (1 + 2 * r) - π / 4
@[simp]
theorem lineArg_zero : lineArg 0 = 0 := by simp [lineArg, Real.arctan_one]
private theorem lineArg_neg_half : lineArg (-(1 / 2)) = -(π / 4) := by norm_num [lineArg]
theorem strictMono_lineArg : StrictMono lineArg := fun _ _ h ↦ by
  simpa [lineArg] using Real.arctan_lt_arctan_iff.2 (by linarith)
theorem lineArg_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ lineArg r :=
  lineArg_zero ▸ strictMono_lineArg.monotone hr
theorem lineArg_nonpos {r : ℝ} (hr : r ≤ 0) : lineArg r ≤ 0 :=
  lineArg_zero ▸ strictMono_lineArg.monotone hr
theorem hasDerivAt_lineArg (r : ℝ) : HasDerivAt lineArg (2 / (1 + (1 + 2 * r) ^ 2)) r := by
  have h : HasDerivAt (fun y : ℝ ↦ 1 + 2 * y) 2 r := by
    simpa using ((hasDerivAt_id r).const_mul (2 : ℝ)).const_add (1 : ℝ)
  have h' := h.arctan.sub_const (π / 4)
  rw [show 1 / (1 + (1 + 2 * r) ^ 2) * 2 = 2 / (1 + (1 + 2 * r) ^ 2) by ring] at h'
  exact h'
theorem lineArg_eq_arctan {r : ℝ} (hr : -1 < r) : lineArg r = Real.arctan (r / (1 + r)) := by
  have h := Real.arctan_add (x := 1 + 2 * r) (y := -1) (by linarith)
  rw [Real.arctan_neg, Real.arctan_one, show (1 + 2 * r + -1) / (1 - (1 + 2 * r) * -1)
      = r / (1 + r) by
    rw [show (1 : ℝ) - (1 + 2 * r) * -1 = 2 * (1 + r) by ring,
      show (1 : ℝ) + 2 * r + -1 = 2 * r by ring, mul_div_mul_left _ _ two_ne_zero]] at h
  rw [lineArg]
  linarith
private theorem lineArg_le_div {r : ℝ} (hr : 0 ≤ r) : lineArg r ≤ r / (1 + r) := by
  rw [lineArg_eq_arctan (by linarith)]
  exact Real.arctan_le_self (by positivity)
theorem lineArg_le_self {r : ℝ} (hr : 0 ≤ r) : lineArg r ≤ r :=
  (lineArg_le_div hr).trans <| by rw [div_le_iff₀ (by linarith)]; nlinarith
private theorem lineArg_le_div_one_sub {r : ℝ} (hr : -(1 / 2) ≤ r) (hr0 : r ≤ 0) :
    lineArg r ≤ (r - 2 * r ^ 2) / (1 - r) := by
  have hne : (1 : ℝ) - r ≠ 0 := ne_of_gt (by linarith)
  have hd : ∀ x : ℝ, x < 1 → HasDerivAt (fun y : ℝ ↦ 2 * y + 1 - 1 / (1 - y) - lineArg y)
      (2 - (0 * (1 - x) - 1 * (0 - 1)) / (1 - x) ^ 2 - 2 / (1 + (1 + 2 * x) ^ 2)) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ ↦ 2 * y + 1) 2 x := by
      simpa using ((hasDerivAt_id x).const_mul (2 : ℝ)).add_const (1 : ℝ)
    exact (h1.sub ((hasDerivAt_const x (1 : ℝ)).div
      ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x))
      (sub_ne_zero_of_ne hx.ne'))).sub (hasDerivAt_lineArg x)
  have hanti : AntitoneOn (fun y : ℝ ↦ 2 * y + 1 - 1 / (1 - y) - lineArg y)
      (Set.Icc (-(1 / 2) : ℝ) 0) := by
    have hmem : ∀ x ∈ interior (Set.Icc (-(1 / 2) : ℝ) 0), -(1 / 2) < x ∧ x < 0 := fun x hx ↦ by
      rwa [interior_Icc, Set.mem_Ioo] at hx
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (f' := fun x ↦ 2 - (0 * (1 - x) - 1 * (0 - 1)) / (1 - x) ^ 2 - 2 / (1 + (1 + 2 * x) ^ 2))
      (fun x hx ↦ (hd x (by linarith [(Set.mem_Icc.1 hx).2])).continuousAt.continuousWithinAt)
      (fun x hx ↦ (hd x (by linarith [(hmem x hx).2])).hasDerivWithinAt) fun x hx ↦ ?_
    obtain ⟨hx1, hx2⟩ := hmem x hx
    have hden : (0 : ℝ) < 1 + (1 + 2 * x) ^ 2 := by positivity
    have hden' : (0 : ℝ) < (1 - x) ^ 2 := pow_pos (by linarith) 2
    rw [show (0 * (1 - x) - 1 * (0 - 1)) / (1 - x) ^ 2 = 1 / (1 - x) ^ 2 by ring]
    have hkey : (2 : ℝ) ≤ 1 / (1 - x) ^ 2 + 2 / (1 + (1 + 2 * x) ^ 2) := by
      rw [div_add_div _ _ hden'.ne' hden.ne', le_div_iff₀ (by positivity)]
      nlinarith [mul_nonneg (sq_nonneg x) (by nlinarith : (0 : ℝ) ≤ 5 + 4 * x - 4 * x ^ 2)]
    linarith
  have h := hanti (Set.mem_Icc.2 ⟨hr, hr0⟩) (Set.mem_Icc.2 ⟨by norm_num, le_rfl⟩) hr0
  norm_num [lineArg_zero] at h
  rw [show (r - 2 * r ^ 2) / (1 - r) = 2 * r + 1 - (1 - r)⁻¹ by field_simp; ring]
  linarith
theorem lineArg_le_sub_div {r : ℝ} (hr : -(1 / 2) ≤ r) : lineArg r ≤ r - r ^ 2 / (1 + |r|) := by
  rcases le_total 0 r with h | h
  · have hne : (1 : ℝ) + r ≠ 0 := by positivity
    have heq : r - r ^ 2 / (1 + r) = r / (1 + r) := by field_simp; ring
    rw [abs_of_nonneg h, heq]
    exact lineArg_le_div h
  · have hne : (1 : ℝ) - r ≠ 0 := (show (0 : ℝ) < 1 - r by linarith).ne'
    have heq : r - r ^ 2 / (1 + -r) = (r - 2 * r ^ 2) / (1 - r) := by
      rw [show (1 : ℝ) + -r = 1 - r by ring]
      field_simp
      ring
    rw [abs_of_nonpos h, heq]
    exact lineArg_le_div_one_sub hr h
theorem mul_lineArg_le (c r : ℝ) : c * lineArg r ≤ |c| * (|r| + (r - lineArg r)) := by
  rcases le_total 0 r with h | h
  · rw [abs_of_nonneg h]
    nlinarith [lineArg_nonneg h, lineArg_le_self h, le_abs_self c, abs_nonneg c]
  · rw [abs_of_nonpos h]
    nlinarith [lineArg_nonpos h, neg_abs_le c, abs_nonneg c]
theorem mul_lineArg_sub_le' {lam r : ℝ} (hone : |lam - 1| ≤ 1) (hr : -(1 / 2) ≤ r) :
    lam * lineArg r - r - r ^ 2
      ≤ -r ^ 2 - (1 - |lam - 1|) * (r ^ 2 / (1 + |r|)) + |lam - 1| * |r| := by
  linarith [mul_lineArg_le (lam - 1) r,
    mul_le_mul_of_nonneg_left
      (by linarith [lineArg_le_sub_div hr] : r ^ 2 / (1 + |r|) ≤ r - lineArg r)
      (by linarith : (0 : ℝ) ≤ 1 - |lam - 1|)]
theorem mul_lineArg_sub_le_of_le_neg_half {lam r : ℝ} (hlam : 2 / π ≤ lam) (hr : r ≤ -(1 / 2)) :
    lam * lineArg r - r - r ^ 2 ≤ -(r ^ 2 / 2) := by
  have hg : lineArg r ≤ -(π / 4) := lineArg_neg_half ▸ strictMono_lineArg.monotone hr
  have hg0 : lineArg r ≤ 0 := by linarith [Real.pi_pos]
  have h2 : 2 / π * lineArg r ≤ -(1 / 2) := by
    have h := mul_le_mul_of_nonneg_left hg (by positivity : (0 : ℝ) ≤ 2 / π)
    rwa [show 2 / π * -(π / 4) = -(1 / 2) by field_simp; norm_num] at h
  linarith [mul_le_mul_of_nonpos_right hlam hg0, sq_nonneg (r + 1)]
theorem slantArg_line_eq_lineArg {a : ℝ} (ha : 0 < a) (w : ℝ) :
    slantArg (line a w) = lineArg (w / a) := by
  rw [slantArg_line ha, lineArg, show (a + 2 * w) / a = 1 + 2 * (w / a) by field_simp]
noncomputable def phase (t a w : ℝ) : ℝ := t * slantArg (line a w) - 2 * π * w * (a + w)
theorem norm_slantCpow_mul_exp_eq_phase {a : ℝ} (ha : a ≠ 0) (t w : ℝ) :
    ‖slantCpow (line a w) (-(1 / 2 + (t : ℂ) * I)) * exp (π * I * line a w ^ 2)‖
      = ‖line a w‖ ^ (-(1 / 2) : ℝ) * Real.exp (phase t a w) := by
  rw [norm_mul, norm_slantCpow (line_ne_zero ha w), Complex.norm_exp_pi_mul_I_mul_sq,
    line_re, line_im, phase,
    show (-(1 / 2 + (t : ℂ) * I)).re = -(1 / 2) by simp,
    show (-(1 / 2 + (t : ℂ) * I)).im = -t by simp,
    show Real.exp (slantArg (line a w) * -t) = (Real.exp (t * slantArg (line a w)))⁻¹ by
      rw [← Real.exp_neg]; congr 1; ring,
    div_eq_mul_inv, inv_inv, mul_assoc, ← Real.exp_add]
  congr 2
  ring
private theorem phase_le_of_le {t a : ℝ} (ha : 0 < a) {w R : ℝ}
    (h : t / (2 * π) / a ^ 2 * lineArg (w / a) - w / a - (w / a) ^ 2 ≤ R) :
    phase t a w ≤ 2 * π * a ^ 2 * R := by
  have ha' : a ≠ 0 := ha.ne'
  have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2 * π * a ^ 2)
  rw [show 2 * π * a ^ 2 * (t / (2 * π) / a ^ 2 * lineArg (w / a) - w / a - (w / a) ^ 2)
      = t * lineArg (w / a) - 2 * π * w * (a + w) by field_simp; ring] at h2
  rwa [phase, slantArg_line_eq_lineArg ha]
private theorem abs_div_sq_sub_one_le {t a : ℝ} (ht : 0 ≤ t) (ha : 0 < a)
    (hT : t / (2 * π) ≤ 2 * a ^ 2) : |t / (2 * π) / a ^ 2 - 1| ≤ 1 := by
  have ha₂ : (0 : ℝ) < a ^ 2 := by positivity
  have h0 : 0 ≤ t / (2 * π) / a ^ 2 := by positivity
  rw [abs_le]
  refine ⟨by linarith, ?_⟩
  rw [sub_le_iff_le_add, div_le_iff₀ ha₂]
  linarith
private theorem abs_div_sq_sub_one_eq {t a : ℝ} (ha : 0 < a) :
    |t / (2 * π) / a ^ 2 - 1| = |t / (2 * π) - a ^ 2| / a ^ 2 := by
  have ha' : a ≠ 0 := ha.ne'
  have ha₂ : (0 : ℝ) < a ^ 2 := by positivity
  rw [show t / (2 * π) / a ^ 2 - 1 = (t / (2 * π) - a ^ 2) / a ^ 2 by field_simp,
    abs_div, abs_of_pos ha₂]
theorem phase_le' {t a : ℝ} (ht : 0 ≤ t) (ha : 0 < a) (hT : t / (2 * π) ≤ 2 * a ^ 2)
    {w : ℝ} (hw : -(a / 2) ≤ w) :
    phase t a w
      ≤ -(2 * π * w ^ 2)
        - (1 - |t / (2 * π) - a ^ 2| / a ^ 2) * (2 * π * a * w ^ 2 / (a + |w|))
        + 2 * π * |t / (2 * π) - a ^ 2| / a * |w| := by
  have ha' : a ≠ 0 := ha.ne'
  have hr : -(1 / 2 : ℝ) ≤ w / a := by rw [le_div_iff₀ ha]; linarith
  refine (phase_le_of_le ha
    (mul_lineArg_sub_le' (r := w / a) (abs_div_sq_sub_one_le ht ha hT) hr)).trans_eq ?_
  rw [abs_div_sq_sub_one_eq ha, abs_div, abs_of_pos ha,
    show (1 : ℝ) + |w| / a = (a + |w|) / a by field_simp]
  field_simp
theorem phase_le_of_le_neg_half {t a : ℝ} (ha : 0 < a) (hT : 2 / π * a ^ 2 ≤ t / (2 * π))
    {w : ℝ} (hw : w ≤ -(a / 2)) :
    phase t a w ≤ -(π * w ^ 2) := by
  have ha' : a ≠ 0 := ha.ne'
  have hlam : 2 / π ≤ t / (2 * π) / a ^ 2 := by rw [le_div_iff₀ (by positivity)]; exact hT
  have hr : w / a ≤ -(1 / 2 : ℝ) := by rw [div_le_iff₀ ha]; linarith
  refine (phase_le_of_le ha
    (mul_lineArg_sub_le_of_le_neg_half (r := w / a) hlam hr)).trans_eq ?_
  field_simp
end Zeta.RiemannSiegel
end
end CertificatePort114


section CertificatePort115
section
open Complex MeasureTheory
open scoped Real
namespace Zeta.RiemannSiegel
theorem abs_sub_sq_le {T S a : ℝ} (hTS : S ^ 2 = T) (h0 : 0 ≤ S + a) (h1 : S - 1 / 2 ≤ a)
    (h2 : a ≤ S + 1 / 2) : |T - a ^ 2| ≤ a + 1 / 4 := by
  rw [← hTS, show S ^ 2 - a ^ 2 = (S - a) * (S + a) by ring, abs_mul, abs_of_nonneg h0]
  calc |S - a| * (S + a) ≤ 1 / 2 * (S + a) := by
        gcongr
        exact abs_le.2 ⟨by linarith, by linarith⟩
    _ ≤ a + 1 / 4 := by linarith
theorem rpow_neg_half_le_mul_rpow_neg_quarter {T a c : ℝ} (ha : 0 < a) (hT : 0 < T) (hc : 0 < c)
    (h : T ≤ c ^ 4 * a ^ 2) : a ^ (-(1 / 2) : ℝ) ≤ c * T ^ (-(1 / 4) : ℝ) := by
  have key : T ^ (1 / 4 : ℝ) ≤ c * a ^ (1 / 2 : ℝ) :=
    (Real.rpow_le_rpow hT.le h (by norm_num)).trans_eq <| by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast c 4,
        ← Real.rpow_natCast a 2, ← Real.rpow_mul hc.le, ← Real.rpow_mul ha.le]
      norm_num
  rw [Real.rpow_neg ha.le, Real.rpow_neg hT.le, inv_eq_one_div, inv_eq_one_div, mul_one_div,
    div_le_div_iff₀ (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hT _)]
  linarith
theorem norm_mul_sub_one_le (A E : ℂ) : ‖A * (E - 1)‖ ≤ ‖A * E‖ + ‖A‖ := by
  rw [mul_sub, mul_one]
  exact norm_sub_le _ _
private theorem norm_line_rpow_neg_half_le {a : ℝ} (ha0 : 0 < a) (w : ℝ) :
    ‖line a w‖ ^ (-(1 / 2) : ℝ) ≤ 2 ^ (1 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ) := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hlb : (0 : ℝ) < a / Real.sqrt 2 := by positivity
  have hxlb : a / Real.sqrt 2 ≤ ‖line a w‖ := norm_line_ge a w
  rw [show 2 ^ (1 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ) = (a / Real.sqrt 2) ^ (-(1 / 2) : ℝ) by
    rw [Real.div_rpow ha0.le hs2.le, Real.rpow_neg hs2.le,
      show Real.sqrt 2 ^ (1 / 2 : ℝ) = 2 ^ (1 / 4 : ℝ) by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num,
      div_inv_eq_mul]
    ring]
  exact Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num) (Set.mem_Ioi.2 hlb)
    (Set.mem_Ioi.2 (hlb.trans_le hxlb)) hxlb
theorem norm_contourIntegrand_le' {t a : ℝ} (ha0 : 0 < a) {w : ℝ} (hw : 1 ≤ |w|) :
    ‖contourIntegrand (1 / 2 + t * I) a w‖
      ≤ 100 / 99 * (2 ^ (1 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ))
        * Real.exp (phase t a w - π * |w|) := by
  have hE : (0 : ℝ) < Real.exp (π * |w|) := Real.exp_pos _
  have hsin : 99 / 200 * Real.exp (π * |w|) ≤ ‖sin ((π : ℂ) * line a w)‖ :=
    mul_exp_le_norm_sin_pi_mul_line a hw
  have hpow := norm_line_rpow_neg_half_le ha0 w
  have hEp : (0 : ℝ) < Real.exp (phase t a w) := Real.exp_pos _
  have hsin2 : (0 : ℝ) < 2 * ‖sin ((π : ℂ) * line a w)‖ := by nlinarith
  have hK0 : (0 : ℝ) ≤ 2 ^ (1 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg ha0.le _)
  rw [norm_contourIntegrand, norm_slantCpow_mul_exp_eq_phase ha0.ne' t w, div_le_iff₀ hsin2,
    Real.exp_sub]
  calc ‖line a w‖ ^ (-(1 / 2) : ℝ) * Real.exp (phase t a w)
      ≤ 2 ^ (1 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ) * Real.exp (phase t a w) :=
        mul_le_mul_of_nonneg_right hpow hEp.le
    _ = 100 / 99 * (2 ^ (1 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ))
          * (Real.exp (phase t a w) / Real.exp (π * |w|)) * (99 / 100 * Real.exp (π * |w|)) := by
        field_simp
    _ ≤ 100 / 99 * (2 ^ (1 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ))
          * (Real.exp (phase t a w) / Real.exp (π * |w|))
          * (2 * ‖sin ((π : ℂ) * line a w)‖) :=
        mul_le_mul_of_nonneg_left (by linarith)
          (mul_nonneg (mul_nonneg (by norm_num) hK0) (by positivity))
end Zeta.RiemannSiegel
end
end CertificatePort115


section CertificatePort116
section
open Complex MeasureTheory
open scoped Real
namespace Zeta.RiemannSiegel
noncomputable def splitRadius (t : ℝ) : ℝ := (t / (2 * π)) ^ ((12 : ℝ)⁻¹)
end Zeta.RiemannSiegel
end
end CertificatePort116


section CertificatePort117
section
open Complex MeasureTheory
open scoped Real
namespace Zeta.RiemannSiegel
end Zeta.RiemannSiegel
end
end CertificatePort117


section CertificatePort118
section
open Complex MeasureTheory
open scoped Real
namespace Zeta.RiemannSiegel
private theorem le_sqrt_two : (1.41421 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
private theorem phase_sub_pi_mul_abs_le {t a W w : ℝ} (ht : 0 ≤ t) (ha : 7 / 2 ≤ a)
    (hD : |t / (2 * π) - a ^ 2| ≤ a + 1 / 4) (hT : t / (2 * π) ≤ 2 * a ^ 2)
    (hW : 106 / 100 ≤ W) (hWa : 2 * Real.sqrt 2 * W ≤ a) (hw : W ≤ |w|)
    (hw' : -(a / 2) ≤ w) :
    phase t a w - π * |w| ≤ -(23 / 4 * w ^ 2) := by
  have hπ : (3.1415 : ℝ) ≤ π := Real.pi_gt_d4.le
  have hs2 : (1.41421 : ℝ) ≤ Real.sqrt 2 := le_sqrt_two
  have ha0 : (0 : ℝ) < a := by linarith
  have hph := phase_le' ht ha0 hT hw'
  set r : ℝ := |w|
  have hr0 : (0 : ℝ) < r := by linarith
  have hrsq : r ^ 2 = w ^ 2 := sq_abs w
  set D : ℝ := |t / (2 * π) - a ^ 2|
  have hε : D / a ^ 2 ≤ 15 / 49 := by
    rw [div_le_iff₀ (pow_pos ha0 2)]
    nlinarith [mul_nonneg (sub_nonneg.2 ha) (by linarith : (0 : ℝ) ≤ 15 * a + 7 / 2)]
  have hB : 2 * π * D / a ≤ 15 * π / 7 := by
    rw [div_le_iff₀ ha0]
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.2 ha),
      mul_le_mul_of_nonneg_left hD (by positivity : (0 : ℝ) ≤ 2 * π)]
  have hWa' : 2.82842 * W ≤ a := by
    nlinarith [mul_nonneg (sub_nonneg.2 hs2) (by linarith : (0 : ℝ) ≤ W)]
  have hQ : 73 / 100 * W ≤ a * r / (a + r) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [mul_nonneg (sub_nonneg.2 hWa') (by linarith : (0 : ℝ) ≤ r - 73 / 100 * W),
      mul_nonneg (by linarith : (0 : ℝ) ≤ W) (sub_nonneg.2 hw), sq_nonneg W]
  set Q : ℝ := a * r / (a + r) with hQdef
  set B : ℝ := 2 * π * D / a
  set ε : ℝ := D / a ^ 2
  have hbracket : 0 ≤ (2 * π - 23 / 4) * r + (1 - ε) * (2 * π * Q) - (B - π) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * π - 23 / 4)
      (by linarith : (0 : ℝ) ≤ r - 106 / 100), Real.pi_pos,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ε)
        (by nlinarith [Real.pi_pos] : (0 : ℝ) ≤ 2 * π * Q - 2 * π * (73 / 100 * (106 / 100)))]
  have hden : a + r ≠ 0 := ne_of_gt (by linarith)
  have hkey : (1 - ε) * (2 * π * a * w ^ 2 / (a + r)) = r * ((1 - ε) * (2 * π * Q)) := by
    rw [hQdef, ← hrsq]
    field_simp
  rw [hkey] at hph
  nlinarith [mul_nonneg hr0.le hbracket]
private theorem sqrt_two_mul_norm_modelIntegrand_mul_exp_saddleDiscrepancy_le {t : ℝ} (ht : 0 < t)
    {ν : ℕ} (hν' : Real.sqrt (t / (2 * π)) ≤ ν + 1) (hS : 4 ≤ Real.sqrt (t / (2 * π)))
    {w : ℝ} (hw : 1 ≤ |w|) :
    Real.sqrt 2 * ‖modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
        * exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w))‖
      ≤ 19 / 10 * Real.exp (phase t ((ν : ℝ) + 1 / 2) w - π * |w|) := by
  have hT0 : (0 : ℝ) < t / (2 * π) := div_pos ht (by positivity)
  have hs2u : Real.sqrt 2 ≤ 1.41422 := sqrt_two_le
  set S : ℝ := Real.sqrt (t / (2 * π)) with hSdef
  set a : ℝ := (ν : ℝ) + 1 / 2 with hadef
  have ha0 : (0 : ℝ) < a := by rw [hadef]; positivity
  have haS : S ≤ a + 1 / 2 := by rw [hadef]; linarith
  have ha : (7 : ℝ) / 2 ≤ a := by rw [hadef]; linarith
  have hS0 : (0 : ℝ) ≤ S := Real.sqrt_nonneg _
  have hSsq : S ^ 2 = t / (2 * π) := Real.sq_sqrt hT0.le
  have h2rpow : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 1.19 := by
    rw [show (2 : ℝ) ^ (1 / 4 : ℝ) = Real.sqrt (Real.sqrt 2) by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num]
    exact (Real.sqrt_le_left (by norm_num)).2 ((Real.sqrt_le_left (by norm_num)).2 (by norm_num))
  have hconst : Real.sqrt 2 * (100 / 99 * (2 ^ (1 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ)))
      ≤ 19 / 10 * (t / (2 * π)) ^ (-(1 / 4) : ℝ) := by
    have hcore : a ^ (-(1 / 2) : ℝ) ≤ 1.07 * (t / (2 * π)) ^ (-(1 / 4) : ℝ) :=
      rpow_neg_half_le_mul_rpow_neg_quarter ha0 hT0 (by norm_num)
        (by nlinarith [mul_le_mul haS haS hS0 (by linarith : (0 : ℝ) ≤ a + 1 / 2)])
    calc Real.sqrt 2 * (100 / 99 * (2 ^ (1 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ)))
        = Real.sqrt 2 * (100 / 99) * 2 ^ (1 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ) := by ring
      _ ≤ 1.41422 * (100 / 99) * 1.19 * (1.07 * (t / (2 * π)) ^ (-(1 / 4) : ℝ)) :=
          mul_le_mul (mul_le_mul (by linarith) h2rpow (by positivity) (by norm_num)) hcore
            (Real.rpow_nonneg ha0.le _) (by norm_num)
      _ ≤ 19 / 10 * (t / (2 * π)) ^ (-(1 / 4) : ℝ) := by
          nlinarith [Real.rpow_nonneg hT0.le (-(1 / 4) : ℝ)]
  rw [norm_modelIntegrand_mul_exp_saddleDiscrepancy ht ν w, ← mul_div_assoc,
    div_le_iff₀ (Real.rpow_pos_of_pos hT0 _)]
  calc Real.sqrt 2 * ‖contourIntegrand (1 / 2 + t * I) a w‖
      ≤ Real.sqrt 2 * (100 / 99 * (2 ^ (1 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ))
          * Real.exp (phase t a w - π * |w|)) := by
        gcongr
        exact norm_contourIntegrand_le' ha0 hw
    _ = Real.sqrt 2 * (100 / 99 * (2 ^ (1 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ)))
          * Real.exp (phase t a w - π * |w|) := by ring
    _ ≤ 19 / 10 * (t / (2 * π)) ^ (-(1 / 4) : ℝ) * Real.exp (phase t a w - π * |w|) :=
        mul_le_mul_of_nonneg_right hconst (Real.exp_nonneg _)
    _ = 19 / 10 * Real.exp (phase t a w - π * |w|) * (t / (2 * π)) ^ (-(1 / 4) : ℝ) := by ring
private theorem sqrt_two_mul_norm_modelIntegrand_le {p : ℝ} (hκ : |1 / 2 - p| ≤ 1 / 2) (w : ℝ) :
    Real.sqrt 2 * ‖modelIntegrand (p : ℂ) (1 / 2) w‖
      ≤ 11 / 5 * Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  calc Real.sqrt 2 * ‖modelIntegrand (p : ℂ) (1 / 2) w‖
      ≤ Real.sqrt 2 * (Real.exp (π / 4)
          * Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) / Real.sqrt 2) :=
        mul_le_mul_of_nonneg_left (norm_modelIntegrand_le_exp_neg_mul_sq hκ w) hs2.le
    _ = Real.exp (π / 4) * Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) := by field_simp
    _ ≤ 11 / 5 * Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) :=
        mul_le_mul_of_nonneg_right Real.exp_pi_div_four_le (Real.exp_nonneg _)
private theorem mul_exp_div_le_div_sq {b A S k m c₁ c₂ : ℝ} (hA0 : 0 < A) (hS0 : 0 < S)
    (hc₁ : 0 ≤ c₁) (hk : 0 ≤ k) (hb : 0 < b) (hSsq : S ^ 2 ≤ k * A ^ 2)
    (hkey : A * Real.exp (-b * A ^ 2) ≤ m) (hnum : c₁ * (k * m) ≤ c₂ * b) :
    c₁ * (Real.exp (-b * A ^ 2) / (b * A)) ≤ c₂ / S ^ 2 := by
  have hE0 : (0 : ℝ) < Real.exp (-b * A ^ 2) := Real.exp_pos _
  rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (pow_pos hS0 2)]
  linarith [mul_le_mul_of_nonneg_left hSsq (mul_nonneg hc₁ hE0.le),
    mul_le_mul_of_nonneg_left hkey (mul_nonneg (mul_nonneg hc₁ hk) hA0.le),
    mul_le_mul_of_nonneg_right hnum hA0.le]
private theorem outer_true_constant_le {S W : ℝ} (hW : 106 / 100 ≤ W)
    (hSW : S = 2 * Real.sqrt 2 * W + 1) :
    19 / 10 * (Real.exp (-(23 / 4) * W ^ 2) / (23 / 4 * W)) ≤ 1 / 25 / S ^ 2 := by
  have hs2u : Real.sqrt 2 ≤ 1.41422 := sqrt_two_le
  have hW0 : (0 : ℝ) < W := by linarith
  have hS0 : (0 : ℝ) < S := by rw [hSW]; nlinarith [le_sqrt_two]
  have hSsq : S ^ 2 ≤ 14.229 * W ^ 2 := by
    have hSle : S ≤ 3.772 * W := by rw [hSW]; nlinarith
    nlinarith
  have hthr : Real.exp (-(23 / 4) * (106 / 100 : ℝ) ^ 2) * 403 ≤ 1 := by
    rw [show -(23 / 4) * (106 / 100 : ℝ) ^ 2 = -(23 / 4 * (106 / 100 : ℝ) ^ 2) by ring]
    exact exp_neg_mul_le_one (n := 6) (by norm_num) (by norm_num)
  have hkey : W * Real.exp (-(23 / 4) * W ^ 2) ≤ 1 / 130 := by
    have hmono := pow_mul_exp_neg_mul_sq_le (b := 23 / 4) (A₀ := 106 / 100) (A := W) (k := 1)
      (by norm_num) (by norm_num) (by norm_num) hW
    nlinarith [Real.exp_pos (-(23 / 4) * (106 / 100 : ℝ) ^ 2)]
  exact mul_exp_div_le_div_sq hW0 hS0 (by norm_num) (by norm_num) (by norm_num) hSsq hkey
    (by norm_num)
private theorem outer_far_constant_le {S a : ℝ} (ha : 7 / 2 ≤ a) (hS0 : 0 < S)
    (hSa : S ≤ a + 1 / 2) :
    19 / 10 * (Real.exp (-π * (a / 2) ^ 2) / (π * (a / 2))) ≤ 1 / 200 / S ^ 2 := by
  have hπ : (3.1415 : ℝ) ≤ π := Real.pi_gt_d4.le
  have hSsq : S ^ 2 ≤ 256 / 49 * (a / 2) ^ 2 := by nlinarith
  have hthr : Real.exp (-π * (7 / 4 : ℝ) ^ 2) * 2900 ≤ 1 := by
    rw [show -π * (7 / 4 : ℝ) ^ 2 = -(π * (7 / 4 : ℝ) ^ 2) by ring]
    exact exp_neg_mul_le_one (n := 8) (by norm_num) (by push_cast; nlinarith)
  have hkey : a / 2 * Real.exp (-π * (a / 2) ^ 2) ≤ 7 / 11600 := by
    have hmono := pow_mul_exp_neg_mul_sq_le (b := π) (A₀ := 7 / 4) (A := a / 2) (k := 1)
      Real.pi_pos (by norm_num) (by push_cast; nlinarith) (by linarith)
    nlinarith [Real.exp_pos (-π * (7 / 4 : ℝ) ^ 2)]
  exact mul_exp_div_le_div_sq (by linarith) hS0 (by norm_num) (by norm_num) Real.pi_pos hSsq hkey
    (by linarith)
private theorem outer_model_constant_le {S A : ℝ} (hA : 81 / 100 ≤ A) (hS0 : 0 < S)
    (hSA : S ≤ 5 * A) :
    11 / 5 * (Real.exp (-(4 * π) * A ^ 2) / (4 * π * A)) ≤ 1 / 200 / S ^ 2 := by
  have hπ : (3.1415 : ℝ) ≤ π := Real.pi_gt_d4.le
  have hA0 : (0 : ℝ) < A := by linarith
  have hSsq : S ^ 2 ≤ 25 * A ^ 2 := by nlinarith
  have hthr : Real.exp (-(4 * π) * (81 / 100 : ℝ) ^ 2) * 2900 ≤ 1 := by
    rw [show -(4 * π) * (81 / 100 : ℝ) ^ 2 = -(4 * π * (81 / 100 : ℝ) ^ 2) by ring]
    exact exp_neg_mul_le_one (n := 8) (by norm_num) (by push_cast; nlinarith)
  have hkey : A * Real.exp (-(4 * π) * A ^ 2) ≤ 81 / 290000 := by
    have hmono := pow_mul_exp_neg_mul_sq_le (b := 4 * π) (A₀ := 81 / 100) (A := A) (k := 1)
      (by positivity) (by norm_num) (by push_cast; nlinarith) hA
    nlinarith [Real.exp_pos (-(4 * π) * (81 / 100 : ℝ) ^ 2)]
  exact mul_exp_div_le_div_sq hA0 hS0 (by norm_num) (by norm_num) (by positivity) hSsq hkey
    (by linarith)
private theorem integral_true_near_le {t p a W S : ℝ} (ht : 0 ≤ t)
    (hGint : Integrable fun w : ℝ ↦ modelIntegrand (p : ℂ) (1 / 2) w
      * exp (saddleDiscrepancy t (line a w)))
    (hGpt : ∀ w : ℝ, 1 ≤ |w| → Real.sqrt 2 * ‖modelIntegrand (p : ℂ) (1 / 2) w
      * exp (saddleDiscrepancy t (line a w))‖ ≤ 19 / 10 * Real.exp (phase t a w - π * |w|))
    (ha : 7 / 2 ≤ a) (hD : |t / (2 * π) - a ^ 2| ≤ a + 1 / 4) (hTa : t / (2 * π) ≤ 2 * a ^ 2)
    (hW : 106 / 100 ≤ W) (hWa : 2 * Real.sqrt 2 * W ≤ a) (hSW : S = 2 * Real.sqrt 2 * W + 1) :
    ∫ w in (Set.Icc (-W) W)ᶜ ∩ Set.Ici (-(a / 2)),
        Real.sqrt 2 * ‖modelIntegrand (p : ℂ) (1 / 2) w
          * exp (saddleDiscrepancy t (line a w))‖ ≤ 1 / 25 / S ^ 2 := by
  have hTint : Integrable fun w : ℝ ↦ 19 / 10 * Real.exp (-(23 / 4) * w ^ 2) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 23 / 4)).const_mul _
  refine (setIntegral_mono_on (hGint.norm.const_mul _).integrableOn hTint.integrableOn
    (measurableSet_Icc.compl.inter measurableSet_Ici) fun w hw ↦ ?_).trans ?_
  · simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_Icc, ← abs_le, not_le,
      Set.mem_Ici] at hw
    refine (hGpt w (by linarith)).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
      (by norm_num))
    exact (phase_sub_pi_mul_abs_le ht ha hD hTa hW hWa hw.1.le hw.2).trans_eq (by ring)
  · refine (setIntegral_mono_set hTint.integrableOn (.of_forall fun w ↦ by positivity)
      Set.inter_subset_left.eventuallyLE).trans ?_
    rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left (integral_compl_Icc_exp_neg_mul_sq_le
      (by norm_num : (0 : ℝ) < 23 / 4) (by linarith : (0 : ℝ) < W))
      (by norm_num)).trans (outer_true_constant_le hW hSW)
private theorem integral_true_far_le {t p a W S : ℝ}
    (hGint : Integrable fun w : ℝ ↦ modelIntegrand (p : ℂ) (1 / 2) w
      * exp (saddleDiscrepancy t (line a w)))
    (hGpt : ∀ w : ℝ, 1 ≤ |w| → Real.sqrt 2 * ‖modelIntegrand (p : ℂ) (1 / 2) w
      * exp (saddleDiscrepancy t (line a w))‖ ≤ 19 / 10 * Real.exp (phase t a w - π * |w|))
    (ha : 7 / 2 ≤ a) (hTa' : 2 / π * a ^ 2 ≤ t / (2 * π)) (hS0 : 0 < S) (haS : S ≤ a + 1 / 2) :
    ∫ w in (Set.Icc (-W) W)ᶜ \ Set.Ici (-(a / 2)),
        Real.sqrt 2 * ‖modelIntegrand (p : ℂ) (1 / 2) w
          * exp (saddleDiscrepancy t (line a w))‖ ≤ 1 / 200 / S ^ 2 := by
  have hFarint : Integrable fun w : ℝ ↦ 19 / 10 * Real.exp (-π * w ^ 2) :=
    (integrable_exp_neg_mul_sq Real.pi_pos).const_mul _
  have hlt : ∀ w ∈ (Set.Icc (-W) W)ᶜ \ Set.Ici (-(a / 2)), w < -(a / 2) := fun w hw ↦ by
    simpa only [Set.mem_Ici, not_le] using hw.2
  refine (setIntegral_mono_on (hGint.norm.const_mul _).integrableOn hFarint.integrableOn
    (measurableSet_Icc.compl.diff measurableSet_Ici) fun w hw ↦ ?_).trans ?_
  · have hwa : w ≤ -(a / 2) := (hlt w hw).le
    refine (hGpt w (by rw [abs_of_neg (by linarith)]; linarith)).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num))
    have hph := phase_le_of_le_neg_half (by linarith : (0 : ℝ) < a) hTa' hwa
    have habs : (0 : ℝ) ≤ π * |w| := by positivity
    linarith
  · have hsub : (Set.Icc (-W) W)ᶜ \ Set.Ici (-(a / 2)) ⊆ (Set.Icc (-(a / 2)) (a / 2))ᶜ :=
      fun w hw ↦ by
        simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le]
        exact Or.inl (hlt w hw)
    refine (setIntegral_mono_set hFarint.integrableOn (.of_forall fun w ↦ by positivity)
      hsub.eventuallyLE).trans ?_
    rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left (integral_compl_Icc_exp_neg_mul_sq_le Real.pi_pos
      (by linarith : (0 : ℝ) < a / 2)) (by norm_num)).trans (outer_far_constant_le ha hS0 haS)
private theorem integral_model_le {p W S : ℝ} (hHint : Integrable (modelIntegrand (p : ℂ) (1 / 2)))
    (hHpt : ∀ w : ℝ, Real.sqrt 2 * ‖modelIntegrand (p : ℂ) (1 / 2) w‖
      ≤ 11 / 5 * Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2))
    (hd : |(1 / 2 - p) / 2| ≤ 1 / 4) (hA : 81 / 100 ≤ W - 1 / 4) (hS0 : 0 < S)
    (hSA : S ≤ 5 * (W - 1 / 4)) :
    ∫ w in (Set.Icc (-W) W)ᶜ, Real.sqrt 2 * ‖modelIntegrand (p : ℂ) (1 / 2) w‖
      ≤ 1 / 200 / S ^ 2 := by
  have hπ : (3.1415 : ℝ) ≤ π := Real.pi_gt_d4.le
  have hbA : (1 : ℝ) ≤ 4 * π * (W - 1 / 4) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 81 / 100)
      hA 2) (by positivity : (0 : ℝ) ≤ 4 * π)
    linarith
  have hMint : Integrable fun w : ℝ ↦ 11 / 5 * Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) :=
    ((integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 4 * π)).comp_add_right
      ((1 / 2 - p) / 2)).const_mul _
  refine (setIntegral_mono_on (hHint.norm.const_mul _).integrableOn hMint.integrableOn
    measurableSet_Icc.compl fun w _ ↦ hHpt w).trans ?_
  rw [integral_const_mul]
  exact (mul_le_mul_of_nonneg_left (integral_compl_Icc_exp_neg_mul_sq_comp_add_right_le
    (by positivity : (0 : ℝ) < 4 * π) (by linarith : (0 : ℝ) < W - 1 / 4) (by linarith) hbA)
    (by norm_num)).trans (outer_model_constant_le hA hS0 hSA)
theorem norm_integral_outer_le' {t : ℝ} (ht : 16 ≤ t / (2 * π)) {ν : ℕ}
    (hν : (ν : ℝ) ≤ Real.sqrt (t / (2 * π)))
    (hν' : Real.sqrt (t / (2 * π)) ≤ ν + 1) :
    ‖(1 + I) * ∫ w in (Set.Icc (-sharpSplitRadius t) (sharpSplitRadius t))ᶜ,
        modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
          * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1)‖
      ≤ 1 / 20 / (t / (2 * π)) := by
  have hT0 : (0 : ℝ) < t / (2 * π) := lt_of_lt_of_le (by norm_num) ht
  have ht0 : 0 < t := (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * π)).mp hT0
  have hπ : (3.1415 : ℝ) ≤ π := Real.pi_gt_d4.le
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hs2u : Real.sqrt 2 ≤ 1.41422 := sqrt_two_le
  have hS4 : 4 ≤ Real.sqrt (t / (2 * π)) := four_le_sqrt ht
  have hκ : |1 / 2 - (Real.sqrt (t / (2 * π)) - ν)| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hGpt := fun (w : ℝ) (hw : (1 : ℝ) ≤ |w|) ↦
    sqrt_two_mul_norm_modelIntegrand_mul_exp_saddleDiscrepancy_le ht0 hν' hS4 hw
  have hHpt := sqrt_two_mul_norm_modelIntegrand_le hκ
  have hGint := integrable_modelIntegrand_mul_exp_saddleDiscrepancy ht0 ν
  have hHint := integrable_modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ) : ℂ)
    (show (1 / 2 : ℝ) = (0 : ℤ) + 1 / 2 by norm_num)
  have hFint := integrable_modelIntegrand_mul_exp_saddleDiscrepancy_sub_one ht0 ν
  set S : ℝ := Real.sqrt (t / (2 * π)) with hSdef
  set p : ℝ := S - (ν : ℝ)
  set a : ℝ := (ν : ℝ) + 1 / 2 with hadef
  set W : ℝ := sharpSplitRadius t with hWdef
  have hTS : S ^ 2 = t / (2 * π) := Real.sq_sqrt hT0.le
  have hSW : S = 2 * Real.sqrt 2 * W + 1 := by
    rw [hWdef, hSdef, sharpSplitRadius]
    field_simp
    ring
  have hW106 : 106 / 100 ≤ W := by
    rw [hWdef, sharpSplitRadius, ← hSdef, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt 2)]
    nlinarith
  have ha : (7 : ℝ) / 2 ≤ a := by rw [hadef]; linarith
  have haS : S ≤ a + 1 / 2 := by rw [hadef]; linarith
  have haS' : a ≤ S + 1 / 2 := by rw [hadef]; linarith
  clear_value S p a W
  have hS0 : (0 : ℝ) < S := by linarith
  have hW0 : (0 : ℝ) < W := by linarith
  have hD : |t / (2 * π) - a ^ 2| ≤ a + 1 / 4 :=
    abs_sub_sq_le hTS (by linarith) (by linarith) haS'
  have hTa : t / (2 * π) ≤ 2 * a ^ 2 := by rw [← hTS]; nlinarith
  have hTa' : 2 / π * a ^ 2 ≤ t / (2 * π) := by
    rw [← hTS, div_mul_eq_mul_div, div_le_iff₀ Real.pi_pos]
    nlinarith [mul_nonneg (sub_nonneg.2 hπ) (sq_nonneg S)]
  have hWa : 2 * Real.sqrt 2 * W ≤ a := by linarith
  have hA81 : 81 / 100 ≤ W - 1 / 4 := by linarith
  have hSA : S ≤ 5 * (W - 1 / 4) := by
    nlinarith [mul_le_mul_of_nonneg_right hs2u hW0.le]
  have hd : |(1 / 2 - p) / 2| ≤ 1 / 4 := by
    rw [abs_div, abs_two]
    linarith [(abs_le.1 hκ).1, (abs_le.1 hκ).2]
  have hnear := integral_true_near_le ht0.le hGint hGpt ha hD hTa hW106 hWa hSW
  have hfar := integral_true_far_le (W := W) hGint hGpt ha hTa' hS0 haS
  have hmodel := integral_model_le hHint hHpt hd hA81 hS0 hSA
  have hGsplit := integral_inter_add_sdiff (s := (Set.Icc (-W) W)ᶜ)
    (t := Set.Ici (-(a / 2))) measurableSet_Ici
    ((hGint.norm.const_mul (Real.sqrt 2)).integrableOn (s := (Set.Icc (-W) W)ᶜ))
  calc ‖(1 + I) * ∫ w in (Set.Icc (-W) W)ᶜ, modelIntegrand (p : ℂ) (1 / 2) w
        * (exp (saddleDiscrepancy t (line a w)) - 1)‖
      ≤ Real.sqrt 2 * ∫ w in (Set.Icc (-W) W)ᶜ, ‖modelIntegrand (p : ℂ) (1 / 2) w
          * (exp (saddleDiscrepancy t (line a w)) - 1)‖ :=
        norm_one_add_I_mul_integral_le _
    _ = ∫ w in (Set.Icc (-W) W)ᶜ, Real.sqrt 2 * ‖modelIntegrand (p : ℂ) (1 / 2) w
          * (exp (saddleDiscrepancy t (line a w)) - 1)‖ := (integral_const_mul _ _).symm
    _ ≤ ∫ w in (Set.Icc (-W) W)ᶜ, (Real.sqrt 2 * ‖modelIntegrand (p : ℂ) (1 / 2) w
            * exp (saddleDiscrepancy t (line a w))‖
          + Real.sqrt 2 * ‖modelIntegrand (p : ℂ) (1 / 2) w‖) := by
        refine setIntegral_mono_on (hFint.norm.const_mul _).integrableOn
          ((hGint.norm.const_mul _).add (hHint.norm.const_mul _)).integrableOn
          measurableSet_Icc.compl fun w _ ↦ ?_
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (norm_mul_sub_one_le _ _) hs2.le
    _ = (∫ w in (Set.Icc (-W) W)ᶜ, Real.sqrt 2 * ‖modelIntegrand (p : ℂ) (1 / 2) w
            * exp (saddleDiscrepancy t (line a w))‖)
          + ∫ w in (Set.Icc (-W) W)ᶜ, Real.sqrt 2 * ‖modelIntegrand (p : ℂ) (1 / 2) w‖ :=
        integral_add (hGint.norm.const_mul _).integrableOn (hHint.norm.const_mul _).integrableOn
    _ ≤ (1 / 25 / S ^ 2 + 1 / 200 / S ^ 2) + 1 / 200 / S ^ 2 := by
        rw [← hGsplit]
        exact add_le_add (add_le_add hnear hfar) hmodel
    _ = 1 / 20 / S ^ 2 := by ring
    _ = 1 / 20 / (t / (2 * π)) := by rw [hTS]
end Zeta.RiemannSiegel
end
end CertificatePort118


section CertificatePort119
section
open Complex Complex.Stirling
open scoped Nat Real
namespace Zeta.RiemannSiegel
private noncomputable def thetaArg (t : ℝ) : ℂ := 1 / 4 + Complex.I * (t / 2)
private theorem thetaArg_re (t : ℝ) : (thetaArg t).re = 1 / 4 := by simp [thetaArg]
private theorem thetaArg_im (t : ℝ) : (thetaArg t).im = t / 2 := by simp [thetaArg]
private theorem normSq_thetaArg (t : ℝ) :
    Complex.normSq (thetaArg t) = 1 / 16 + t ^ 2 / 4 := by
  rw [Complex.normSq_apply, thetaArg_re, thetaArg_im]; ring
private theorem norm_thetaArg (t : ℝ) : ‖thetaArg t‖ = Real.sqrt (1 / 16 + t ^ 2 / 4) := by
  rw [← Real.sqrt_sq (norm_nonneg (thetaArg t)), Complex.sq_norm, normSq_thetaArg]
private theorem half_le_norm_thetaArg {t : ℝ} (ht : 0 ≤ t) : t / 2 ≤ ‖thetaArg t‖ := by
  have h := Complex.abs_im_le_norm (thetaArg t)
  rwa [thetaArg_im, abs_of_nonneg (by linarith)] at h
private theorem abs_mul_log_norm_thetaArg_sub_le {t : ℝ} (ht : 0 < t) :
    |t / 2 * (Real.log ‖thetaArg t‖ - Real.log (t / 2)) - 1 / (16 * t)| ≤ 1 / (64 * t ^ 3) := by
  have htne : t ≠ 0 := ht.ne'
  set x : ℝ := 1 / (4 * t ^ 2) with hx
  have hx0 : 0 < x := by rw [hx]; positivity
  have hkey : Real.log ‖thetaArg t‖ - Real.log (t / 2) = Real.log (1 + x) / 2 := by
    have hq : (1 / 16 + t ^ 2 / 4) / ((t / 2) ^ 2) = 1 + x := by rw [hx]; field_simp; ring
    rw [norm_thetaArg, show t / 2 = Real.sqrt ((t / 2) ^ 2) from (Real.sqrt_sq (by linarith)).symm,
      Real.log_sqrt (by positivity), Real.log_sqrt (by positivity), ← sub_div,
      ← Real.log_div (by positivity) (pow_pos (by linarith : (0 : ℝ) < t / 2) 2).ne', hq]
  have h1x : (0 : ℝ) < 1 + x := by linarith
  have hup : Real.log (1 + x) ≤ x := by linarith [Real.log_le_sub_one_of_pos h1x]
  have hlow : x - x ^ 2 ≤ Real.log (1 + x) := by
    have hb : (1 + x)⁻¹ ≤ 1 - x + x ^ 2 := by
      rw [inv_eq_one_div, div_le_iff₀ h1x]
      nlinarith [pow_nonneg hx0.le 3]
    linarith [Real.one_sub_inv_le_log_of_pos h1x]
  have hval1 : t / 4 * (x - x ^ 2) = 1 / (16 * t) - 1 / (64 * t ^ 3) := by
    rw [hx]; field_simp; ring
  have hval2 : t / 4 * x = 1 / (16 * t) := by rw [hx]; field_simp; ring
  rw [hkey, show t / 2 * (Real.log (1 + x) / 2) = t / 4 * Real.log (1 + x) by ring, abs_le]
  constructor <;>
    linarith [mul_le_mul_of_nonneg_left hlow (by linarith : (0 : ℝ) ≤ t / 4),
      mul_le_mul_of_nonneg_left hup (by linarith : (0 : ℝ) ≤ t / 4),
      (by positivity : (0 : ℝ) ≤ 1 / (64 * t ^ 3))]
private theorem abs_arg_thetaArg_sub_le {t : ℝ} (ht : 0 < t) :
    |π / 8 - Complex.arg (thetaArg t) / 4 - 1 / (8 * t)| ≤ 1 / (32 * t ^ 3) := by
  have htne : t ≠ 0 := ht.ne'
  have hy0 : (0 : ℝ) < (2 * t)⁻¹ := by positivity
  have harg : Complex.arg (thetaArg t) = Real.arctan (2 * t) := by
    rw [Complex.arg_eq_arctan (by rw [thetaArg_re]; norm_num), thetaArg_re, thetaArg_im]
    congr 1; ring
  have hG : π / 8 - Complex.arg (thetaArg t) / 4 = Real.arctan (2 * t)⁻¹ / 4 := by
    rw [harg, Real.arctan_inv_of_pos (by linarith : (0 : ℝ) < 2 * t)]; ring
  have hup : Real.arctan (2 * t)⁻¹ ≤ (2 * t)⁻¹ := Real.arctan_le_self hy0.le
  have hlow : (2 * t)⁻¹ - ((2 * t)⁻¹) ^ 3 ≤ Real.arctan (2 * t)⁻¹ := by
    refine le_trans ?_ (Real.div_one_add_sq_le_arctan hy0.le)
    rw [le_div_iff₀ (by positivity)]
    nlinarith [pow_nonneg hy0.le 5]
  have hval1 : (2 * t)⁻¹ / 4 = 1 / (8 * t) := by field_simp; ring
  have hval2 : ((2 * t)⁻¹) ^ 3 / 4 = 1 / (32 * t ^ 3) := by field_simp; ring
  rw [hG, abs_le]
  constructor <;> linarith [(by positivity : (0 : ℝ) ≤ 1 / (32 * t ^ 3))]
private theorem abs_im_inv_thetaArg_sub_le {t : ℝ} (ht : 0 < t) :
    |(1 / 12 * (thetaArg t)⁻¹).im + 1 / (6 * t)| ≤ 1 / (24 * t ^ 3) := by
  have htne : t ≠ 0 := ht.ne'
  have him : (1 / 12 * (thetaArg t)⁻¹).im = -(t / 2) / (12 * (1 / 16 + t ^ 2 / 4)) := by
    rw [show (1 : ℂ) / 12 = ((1 / 12 : ℝ) : ℂ) by norm_num, Complex.im_ofReal_mul,
      Complex.inv_im, normSq_thetaArg, thetaArg_im]
    field_simp
  rw [him, show -(t / 2) / (12 * (1 / 16 + t ^ 2 / 4)) + 1 / (6 * t)
      = 1 / (96 * t * (1 / 16 + t ^ 2 / 4)) from by field_simp; ring,
    abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [ht]
private theorem abs_im_inv_thetaArg_cube_le {t : ℝ} (ht : 0 < t) :
    |(1 / 360 * ((thetaArg t) ^ 3)⁻¹).im| ≤ 1 / (45 * t ^ 3) := by
  have htne : t ≠ 0 := ht.ne'
  have hn : t / 2 ≤ ‖thetaArg t‖ := half_le_norm_thetaArg ht.le
  calc |(1 / 360 * ((thetaArg t) ^ 3)⁻¹).im|
      ≤ ‖(1 / 360 * ((thetaArg t) ^ 3)⁻¹ : ℂ)‖ := Complex.abs_im_le_norm _
    _ = 1 / 360 / ‖thetaArg t‖ ^ 3 := by
        rw [norm_mul, norm_inv, norm_pow, show ‖(1 / 360 : ℂ)‖ = 1 / 360 by norm_num]
        ring
    _ ≤ 1 / 360 / (t / 2) ^ 3 :=
        div_le_div_of_nonneg_left (by norm_num) (pow_pos (by linarith) 3)
          (pow_le_pow_left₀ (by linarith) hn 3)
    _ = 1 / (45 * t ^ 3) := by field_simp; ring
private theorem abs_im_logGammaStirling_two_sub_leading_sub_inv_le {t : ℝ} (ht : 0 < t) :
    |(logGammaStirling 2 (thetaArg t)).im - t / 2 * Real.log π - leadingTheta t - 1 / (48 * t)|
      ≤ 319 / (2880 * t ^ 3) := by
  have htne : t ≠ 0 := ht.ne'
  have h1 : ((thetaArg t - 1 / 2) * Complex.log (thetaArg t)).im
      = t / 2 * Real.log ‖thetaArg t‖ - Complex.arg (thetaArg t) / 4 := by
    rw [show (1 : ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.mul_im, Complex.log_re,
      Complex.log_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      thetaArg_re, thetaArg_im]
    ring
  have h2 : ((1 / 2 : ℂ) * ((Real.log (2 * π) : ℝ) : ℂ)).im = 0 := by simp
  have hexp : (logGammaStirling 2 (thetaArg t)).im
      = t / 2 * Real.log ‖thetaArg t‖ - Complex.arg (thetaArg t) / 4 - t / 2
        + (1 / 12 * (thetaArg t)⁻¹).im - (1 / 360 * ((thetaArg t) ^ 3)⁻¹).im := by
    rw [logGammaStirling_two]
    simp only [Complex.sub_im, Complex.add_im]
    rw [h1, h2, thetaArg_im]
    ring
  have hleading : leadingTheta t
      = t / 2 * Real.log (t / 2) - t / 2 * Real.log π - t / 2 - π / 8 := by
    rw [leadingTheta, show t / (2 * π) = t / 2 / π by ring,
      Real.log_div (by positivity) Real.pi_ne_zero]
    ring
  have hid : (logGammaStirling 2 (thetaArg t)).im - t / 2 * Real.log π - leadingTheta t
        - 1 / (48 * t)
      = (t / 2 * (Real.log ‖thetaArg t‖ - Real.log (t / 2)) - 1 / (16 * t))
        + (π / 8 - Complex.arg (thetaArg t) / 4 - 1 / (8 * t))
        + ((1 / 12 * (thetaArg t)⁻¹).im + 1 / (6 * t))
        - (1 / 360 * ((thetaArg t) ^ 3)⁻¹).im := by
    rw [hexp, hleading]
    ring
  have hA := abs_le.1 (abs_mul_log_norm_thetaArg_sub_le ht)
  have hG := abs_le.1 (abs_arg_thetaArg_sub_le ht)
  have hC := abs_le.1 (abs_im_inv_thetaArg_sub_le ht)
  have hE := abs_le.1 (abs_im_inv_thetaArg_cube_le ht)
  have hsum : 1 / (64 * t ^ 3) + 1 / (32 * t ^ 3) + 1 / (24 * t ^ 3) + 1 / (45 * t ^ 3)
      = 319 / (2880 * t ^ 3) := by ring
  rw [hid, abs_le]
  constructor <;> linarith [hA.1, hA.2, hG.1, hG.2, hC.1, hC.2, hE.1, hE.2]
theorem abs_riemannSiegelTheta_sub_leading_sub_inv_le {t : ℝ} (ht : 0 < t) :
    |riemannSiegelTheta t - leadingTheta t - 1 / (48 * t)|
      ≤ 319 / (2880 * t ^ 3) + 12 / t ^ 4 := by
  rw [show riemannSiegelTheta t - leadingTheta t - 1 / (48 * t)
      = (riemannSiegelTheta t - ((logGammaStirling 2 (thetaArg t)).im - t / 2 * Real.log π))
        + ((logGammaStirling 2 (thetaArg t)).im - t / 2 * Real.log π - leadingTheta t
            - 1 / (48 * t)) from by ring]
  refine (abs_add_le _ _).trans ?_
  have hrem : |riemannSiegelTheta t
      - ((logGammaStirling 2 (thetaArg t)).im - t / 2 * Real.log π)| ≤ 12 / t ^ 4 := by
    simpa [riemannSiegelThetaApproximant, thetaArg] using
      abs_riemannSiegelTheta_sub_approximant_two_le ht
  linarith [hrem, abs_im_logGammaStirling_two_sub_leading_sub_inv_le ht]
theorem abs_riemannSiegelTheta_sub_leading_le' {t : ℝ} (ht : 32 * π ≤ t) :
    |riemannSiegelTheta t - leadingTheta t| ≤ 101 / (4800 * t) := by
  have h100 : (100 : ℝ) ≤ t := le_trans (by linarith [Real.pi_gt_d2]) ht
  have ht0 : (0 : ℝ) < t := by linarith
  have ht2 : (10000 : ℝ) ≤ t ^ 2 := by nlinarith
  have ht3 : (1000000 : ℝ) ≤ t ^ 3 := by nlinarith
  have h3 : (319 : ℝ) / (2880 * t ^ 3) ≤ 1 / (9600 * t) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left ht2 (by positivity : (0 : ℝ) ≤ 2880 * t)]
  have h4 : (12 : ℝ) / t ^ 4 ≤ 1 / (9600 * t) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left ht3 ht0.le]
  have hval : (1 : ℝ) / (48 * t) + (1 / (9600 * t) + 1 / (9600 * t)) = 101 / (4800 * t) := by
    ring
  have hsharp := abs_riemannSiegelTheta_sub_leading_sub_inv_le ht0
  rw [abs_le] at hsharp ⊢
  constructor <;> linarith [hsharp.1, hsharp.2, (by positivity : (0 : ℝ) < 1 / (48 * t))]
end Zeta.RiemannSiegel
end
end CertificatePort119


section CertificatePort120
section
namespace Real
theorem sum_one_div_sqrt_le (ν : ℕ) :
    ∑ n ∈ Finset.Icc 1 ν, 1 / Real.sqrt n ≤ 2 * Real.sqrt ν := by
  induction ν with
  | zero => simp
  | succ k ih =>
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hb0 : 0 < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    have ha : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt hk0
    have hb : Real.sqrt ((k : ℝ) + 1) ^ 2 = (k : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have key : 1 / Real.sqrt ((k : ℝ) + 1)
        ≤ 2 * (Real.sqrt ((k : ℝ) + 1) - Real.sqrt (k : ℝ)) := by
      rw [div_le_iff₀ hb0]
      nlinarith [sq_nonneg (Real.sqrt ((k : ℝ) + 1) - Real.sqrt (k : ℝ))]
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    linarith
end Real
end
end CertificatePort120


