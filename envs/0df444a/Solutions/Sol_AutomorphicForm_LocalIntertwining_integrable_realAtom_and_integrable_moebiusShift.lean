-- Prove2me | solution 1 for AutomorphicForm.LocalIntertwining.integrable_realAtom_and_integrable_moebiusShift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/4135c6cc-eb5e-587a-b5b2-bdb68308394f

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_LocalIntertwining_integrable_realAtom_and_integrable_moebiusShift

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace IntArchR

theorem norm_sub_I (x : ℝ) : ‖(x : ℂ) - Complex.I‖ = Real.sqrt (1 + x ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg ((x : ℂ) - Complex.I)), Complex.sq_norm, Complex.normSq_apply]
  congr 1
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.I_re, sub_zero, Complex.sub_im, Complex.ofReal_im,
    Complex.I_im, zero_sub]
  ring

theorem norm_unit (x : ℝ) :
    ‖((x : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)‖ = 1 := by
  have hpos : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 (by positivity)
  rw [norm_div, norm_sub_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, div_self hpos.ne']

theorem unit_ne_zero (x : ℝ) : ((x : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) ≠ 0 := by
  intro h
  have h1 := norm_unit x
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

theorem integrable_realFactor (k : ℤ) (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun x : ℝ => (((x : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
      * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2))) := by
  have hmaj : Integrable (fun x : ℝ => ((1 : ℝ) + ‖x‖ ^ 2) ^ (-(2 * s.re + 1) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (by rw [Module.finrank_self]; push_cast; linarith)
  refine hmaj.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · refine (Continuous.mul ?_ ?_).aestronglyMeasurable
    · exact Continuous.zpow₀ (Continuous.div (by fun_prop) (by fun_prop)
        (fun x => Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (by positivity)).ne')) k
        (fun x => Or.inl (unit_ne_zero x))
    · exact Continuous.cpow (by fun_prop) continuous_const
        (fun x => Complex.ofReal_mem_slitPlane.2 (by positivity))
  · have hre : (-(s + 1 / 2)).re = -(2 * s.re + 1) / 2 := by
      simp; ring
    have heq : ‖(((x : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
        * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2))‖
          = ((1 : ℝ) + ‖x‖ ^ 2) ^ (-(2 * s.re + 1) / 2) := by
      rw [norm_mul, norm_zpow, norm_unit x, one_zpow, one_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), hre, Real.norm_eq_abs, sq_abs]
    exact heq.le

theorem norm_realFactor_eq (k : ℤ) (σ y : ℝ) :
    ‖(((y : ℂ) - Complex.I) / ((Real.sqrt (1 + y ^ 2) : ℝ) : ℂ)) ^ k
        * (((1 + y ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2))‖ = (1 + y ^ 2) ^ (-(σ + 1 / 2)) := by
  have hre : (-((σ : ℂ) + 1 / 2)).re = -(σ + 1 / 2) := by simp
  rw [norm_mul, norm_zpow, norm_unit y, one_zpow, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), hre]

theorem floor (a b c d x : ℝ) :
    (a * d - b * c) ^ 2 * (1 + x ^ 2)
      ≤ (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * ((a + x * c) ^ 2 + (b + x * d) ^ 2) := by
  set P := a + x * c with hP
  set Q := b + x * d with hQ
  have h1 : a * d - b * c = d * P - c * Q := by rw [hP, hQ]; ring
  have h2 : x * (a * d - b * c) = a * Q - b * P := by rw [hP, hQ]; ring
  have s1 : (a * d - b * c) ^ 2 ≤ (d ^ 2 + c ^ 2) * (P ^ 2 + Q ^ 2) := by
    rw [h1]; nlinarith [sq_nonneg (d * Q + c * P)]
  have s2 : x ^ 2 * (a * d - b * c) ^ 2 ≤ (a ^ 2 + b ^ 2) * (P ^ 2 + Q ^ 2) := by
    have : x ^ 2 * (a * d - b * c) ^ 2 = (a * Q - b * P) ^ 2 := by rw [← h2]; ring
    rw [this]; nlinarith [sq_nonneg (a * P + b * Q)]
  nlinarith [s1, s2]

theorem entries_pos {a b c d : ℝ} (hdet : a * d - b * c ≠ 0) :
    0 < a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  have h := floor a b c d 0
  simp only [add_zero, zero_pow two_ne_zero, mul_one] at h
  have hD : 0 < (a * d - b * c) ^ 2 := by positivity
  have hS : 0 ≤ a ^ 2 + b ^ 2 := by positivity
  nlinarith [h, hD, hS, sq_nonneg c, sq_nonneg d]

theorem main (a b c d : ℝ) (hdet : a * d - b * c ≠ 0) (k : ℤ) (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun x : ℝ =>
      (((|a * d - b * c| : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((|a + x * c| : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)))
        * ((fun σ x => ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
            * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2))) σ ((b + x * d) / (a + x * c)))) := by
  set D : ℝ := |a * d - b * c| with hDdef
  set S : ℝ := a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 with hSdef
  have hD : 0 < D := abs_pos.2 hdet
  have hS : 0 < S := entries_pos hdet
  set K : ℝ := D ^ (σ + 1 / 2) * (D ^ 2 / S) ^ (-(σ + 1 / 2)) with hKdef
  have hK : 0 ≤ K := mul_nonneg (Real.rpow_nonneg hD.le _) (Real.rpow_nonneg (by positivity) _)

  have hmaj0 : Integrable (fun x : ℝ => ((1 : ℝ) + ‖x‖ ^ 2) ^ (-(2 * σ + 1) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
      (by rw [Module.finrank_self]; push_cast; linarith)
  have hmaj : Integrable (fun x : ℝ => K * (1 + x ^ 2) ^ (-(σ + 1 / 2))) := by
    refine (hmaj0.const_mul K).congr (Filter.Eventually.of_forall fun x => ?_)
    show K * ((1 : ℝ) + ‖x‖ ^ 2) ^ (-(2 * σ + 1) / 2) = K * (1 + x ^ 2) ^ (-(σ + 1 / 2))
    rw [Real.norm_eq_abs, sq_abs]
    congr 1; congr 1; ring
  refine hmaj.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  ·
    apply Measurable.aestronglyMeasurable
    fun_prop
  ·
    simp only
    set P : ℝ := a + x * c with hPdef
    set Q : ℝ := b + x * d with hQdef
    have hBpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
    have hrhs0 : 0 ≤ K * (1 + x ^ 2) ^ (-(σ + 1 / 2)) :=
      mul_nonneg hK (Real.rpow_nonneg hBpos.le _)
    rcases eq_or_ne P 0 with hP0 | hP0
    ·
      have hne : (-(2 * (σ : ℂ) + 1)) ≠ 0 := by
        intro h
        have := congrArg Complex.re h
        simp at this; linarith
      have hzero : ((abs P : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)) = 0 := by
        rw [hP0, abs_zero, Complex.ofReal_zero]
        exact Complex.zero_cpow hne
      rw [hzero, mul_zero, zero_mul, norm_zero]
      exact hrhs0
    · have hPpos : 0 < |P| := abs_pos.2 hP0
      have hP2pos : 0 < P ^ 2 := by positivity
      set y : ℝ := Q / P with hydef
      have hypos : (0 : ℝ) < 1 + y ^ 2 := by positivity

      have nJ1 : ‖((D : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2)‖ = D ^ (σ + 1 / 2) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hD]; congr 1; simp
      have nJ2 : ‖((abs P : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1))‖ = (P ^ 2) ^ (-(σ + 1 / 2)) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hPpos]
        have hre : (-(2 * (σ : ℂ) + 1)).re = 2 * (-(σ + 1 / 2)) := by simp; ring
        rw [hre, Real.rpow_mul (abs_nonneg P), ← sq_abs P]
        congr 1
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hatom := norm_realFactor_eq k σ y

      have hPy : P ^ 2 * (1 + y ^ 2) = P ^ 2 + Q ^ 2 := by
        rw [hydef]
        field_simp
      have hfl : D ^ 2 * (1 + x ^ 2) / S ≤ P ^ 2 + Q ^ 2 := by
        rw [div_le_iff₀ hS, hDdef, sq_abs]
        have := floor a b c d x
        rw [← hPdef, ← hQdef] at this
        linarith
      have hflpos : 0 < D ^ 2 * (1 + x ^ 2) / S := by positivity
      calc ‖((D : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((abs P : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1))
              * (((((y : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + y ^ 2) : ℝ) : ℂ)) ^ k
                * (((1 + y ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2)))‖
          = D ^ (σ + 1 / 2) * (P ^ 2) ^ (-(σ + 1 / 2)) * (1 + y ^ 2) ^ (-(σ + 1 / 2)) := by
            rw [norm_mul, norm_mul, nJ1, nJ2, hatom]
        _ = D ^ (σ + 1 / 2) * (P ^ 2 + Q ^ 2) ^ (-(σ + 1 / 2)) := by
            rw [mul_assoc, ← Real.mul_rpow hP2pos.le hypos.le, hPy]
        _ ≤ D ^ (σ + 1 / 2) * (D ^ 2 * (1 + x ^ 2) / S) ^ (-(σ + 1 / 2)) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hflpos hfl (by linarith))
              (Real.rpow_nonneg hD.le _)
        _ = K * (1 + x ^ 2) ^ (-(σ + 1 / 2)) := by
            rw [hKdef, show D ^ 2 * (1 + x ^ 2) / S = (D ^ 2 / S) * (1 + x ^ 2) from by ring,
              Real.mul_rpow (by positivity) hBpos.le]
            ring

end IntArchR

end

theorem solution
    (a b c d : ℝ) (_hdet : a * d - b * c ≠ 0) (k : ℤ) (σ : ℝ) (_hσ : 0 < σ) :
    let atom : ℝ → ℝ → ℂ := fun σ x =>
      ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2))
    Integrable (atom σ) ∧
    Integrable (fun x : ℝ =>
      (((|a * d - b * c| : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((|a + x * c| : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)))
        * atom σ ((b + x * d) / (a + x * c))) := by
  intro atom
  exact ⟨IntArchR.integrable_realFactor k (σ : ℂ) (by simpa using _hσ),
    IntArchR.main a b c d _hdet k σ _hσ⟩

end S_AutomorphicForm_LocalIntertwining_integrable_realAtom_and_integrable_moebiusShift
end P2MW
export P2MW.S_AutomorphicForm_LocalIntertwining_integrable_realAtom_and_integrable_moebiusShift (solution)
