-- Prove2me | Definitions.Def_RPLib_S3_EllW2KS2
-- name    : RPLib_S3_EllW2KS2
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:47:05.70147+00:00
-- url     : https://prove2.me/theorems/66e553b5-b2f0-483e-bcfa-7d9d9ce1e9fe
-- title:
--   The Eichler-Selberg trace formula in weight two: `KS 0 0 = π² / 2`
-- statement:
--   `KS 0 0 = π² / 2`.
--
--   `Qe 0 μ τ = (1 + (μ − τ)²)(1 + (μ + τ)²)`, so with `fC x = (1 + x²)⁻¹`:
--   `∫_τ fC (μ − τ) fC (μ + τ) = ∫_v fC (2μ − v) fC v` (translate), swap the order, and
--   `∫_μ fC (2μ − v) = π / 2`, `∫ fC = π`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2KS1

/-!
# S3-ES-Wt2 (KS2): `KS 0 0 = π² / 2`

`Qe 0 μ τ = (1 + (μ − τ)²)(1 + (μ + τ)²)`, so with `fC x = (1 + x²)⁻¹`:
`∫_τ fC (μ − τ) fC (μ + τ) = ∫_v fC (2μ − v) fC v` (translate), swap the order, and
`∫_μ fC (2μ − v) = π / 2`, `∫ fC = π`.
-/

set_option autoImplicit false

open MeasureTheory Real

noncomputable section

namespace RamanujanPetersson.EllW2

/-- The Cauchy profile. -/
def fC (x : ℝ) : ℝ := (1 + x ^ 2)⁻¹

lemma fC_pos (x : ℝ) : 0 < fC x := by unfold fC; positivity

lemma continuous_fC : Continuous fC :=
  Continuous.inv₀ (by fun_prop) (fun x => by positivity)

lemma integrable_fC : Integrable fC := integrable_inv_one_add_sq

lemma integral_fC : ∫ x, fC x = π := integral_univ_inv_one_add_sq

lemma Qe0_rpow (μ τ : ℝ) : Qe 0 μ τ ^ (-(0 : ℝ) - 1) = fC (μ - τ) * fC (μ + τ) := by
  rw [Qe_zero, show (-(0 : ℝ) - 1) = -1 by norm_num, Real.rpow_neg_one, mul_inv]
  rfl

lemma integrable_fC_two_mul_sub (v : ℝ) : Integrable fun μ : ℝ => fC (2 * μ - v) :=
  (integrable_fC.comp_sub_right v).comp_mul_left' two_ne_zero

lemma integral_fC_two_mul_sub (v : ℝ) : ∫ μ, fC (2 * μ - v) = π / 2 := by
  calc ∫ μ, fC (2 * μ - v) = ∫ μ, (fun w => fC (w - v)) (2 * μ) := rfl
    _ = |(2 : ℝ)⁻¹| • ∫ w, (fun w => fC (w - v)) w :=
        Measure.integral_comp_mul_left (fun w => fC (w - v)) 2
    _ = |(2 : ℝ)⁻¹| * ∫ w, fC (w - v) := by simp only [smul_eq_mul]
    _ = |(2 : ℝ)⁻¹| * π := by rw [integral_sub_right_eq_self fC v, integral_fC]
    _ = π / 2 := by rw [abs_of_pos (by norm_num)]; ring

lemma integral_inner_Q0 (μ : ℝ) :
    ∫ τ, fC (μ - τ) * fC (μ + τ) = ∫ v, fC (2 * μ - v) * fC v := by
  have h := integral_add_right_eq_self (μ := volume) (fun v => fC (2 * μ - v) * fC v) μ
  refine Eq.trans ?_ h
  congr 1
  funext τ
  show fC (μ - τ) * fC (μ + τ) = fC (2 * μ - (τ + μ)) * fC (τ + μ)
  rw [show 2 * μ - (τ + μ) = μ - τ by ring, add_comm τ μ]

lemma integrable_Q0_prod :
    Integrable (Function.uncurry fun μ v : ℝ => fC (2 * μ - v) * fC v) (volume.prod volume) := by
  have hc : Continuous (Function.uncurry fun μ v : ℝ => fC (2 * μ - v) * fC v) :=
    (continuous_fC.comp ((continuous_const.mul continuous_fst).sub continuous_snd)).mul
      (continuous_fC.comp continuous_snd)
  refine (integrable_prod_iff' hc.aestronglyMeasurable).2 ⟨ae_of_all _ fun v => ?_, ?_⟩
  · simpa only [Function.uncurry_apply_pair] using (integrable_fC_two_mul_sub v).mul_const (fC v)
  · have e : (fun v : ℝ => ∫ μ, ‖Function.uncurry (fun μ v : ℝ => fC (2 * μ - v) * fC v) (μ, v)‖)
        = fun v => π / 2 * fC v := by
      funext v
      simp only [Function.uncurry_apply_pair]
      simp_rw [Real.norm_of_nonneg (mul_pos (fC_pos _) (fC_pos v)).le]
      rw [integral_mul_const, integral_fC_two_mul_sub]
    rw [e]
    exact integrable_fC.const_mul _

theorem KS_zero : KS 0 0 = π ^ 2 / 2 := by
  unfold KS
  simp_rw [Qe0_rpow, integral_inner_Q0]
  rw [integral_integral_swap integrable_Q0_prod]
  simp_rw [integral_mul_const, integral_fC_two_mul_sub]
  rw [integral_const_mul, integral_fC]
  ring

end RamanujanPetersson.EllW2


