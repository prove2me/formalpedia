-- Prove2me | solution 1 for AutomorphicForm.LocalIntertwining.integrable_complexAtom_and_integrable_moebiusShift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/60ea1bc5-da62-5b88-a504-d21065475761

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_LocalIntertwining_integrable_complexAtom_and_integrable_moebiusShift

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace IntArchC

theorem integrable_complexFactor (a b m : ℕ) (habm : a + b ≤ m) (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun z : ℂ => z ^ a * (starRingEnd ℂ) z ^ b
      * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * s + 1) - (m : ℂ) / 2)) := by
  have hmaj : Integrable (fun z : ℂ => ((1 : ℝ) + ‖z‖ ^ 2) ^ (-(2 * (2 * s.re + 1)) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume)
      (by rw [Complex.finrank_real_complex]; push_cast; linarith)
  refine hmaj.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · refine ((Continuous.mul (by fun_prop) (by fun_prop)).mul ?_).aestronglyMeasurable
    exact Continuous.cpow (by fun_prop) continuous_const (fun z => Complex.ofReal_mem_slitPlane.2 (by positivity))
  · have hB1 : (1 : ℝ) ≤ 1 + ‖z‖ ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
    have hBpos : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by linarith
    have hre : (-(2 * s + 1) - (m : ℂ) / 2).re = -(2 * s.re + 1 + (m : ℝ) / 2) := by
      simp; ring
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj,
      Complex.norm_cpow_eq_rpow_re_of_pos hBpos, hre]
    have hz : ‖z‖ ≤ (1 + ‖z‖ ^ 2) ^ ((1 : ℝ) / 2) := by
      calc ‖z‖ = Real.sqrt (‖z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg z)).symm
        _ ≤ Real.sqrt (1 + ‖z‖ ^ 2) := Real.sqrt_le_sqrt (by linarith)
        _ = (1 + ‖z‖ ^ 2) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
    have hzab : ‖z‖ ^ a * ‖z‖ ^ b ≤ (1 + ‖z‖ ^ 2) ^ ((m : ℝ) / 2) := by
      calc ‖z‖ ^ a * ‖z‖ ^ b = ‖z‖ ^ (a + b) := (pow_add _ _ _).symm
        _ ≤ ((1 + ‖z‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ (a + b) := pow_le_pow_left₀ (norm_nonneg z) hz _
        _ = (1 + ‖z‖ ^ 2) ^ ((1 : ℝ) / 2 * ((a + b : ℕ) : ℝ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hBpos.le]
        _ ≤ (1 + ‖z‖ ^ 2) ^ ((m : ℝ) / 2) := by
            refine Real.rpow_le_rpow_of_exponent_le hB1 ?_
            have hm : ((a + b : ℕ) : ℝ) ≤ m := by exact_mod_cast habm
            linarith
    calc ‖z‖ ^ a * ‖z‖ ^ b * (1 + ‖z‖ ^ 2) ^ (-(2 * s.re + 1 + (m : ℝ) / 2))
        ≤ (1 + ‖z‖ ^ 2) ^ ((m : ℝ) / 2) * (1 + ‖z‖ ^ 2) ^ (-(2 * s.re + 1 + (m : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right hzab (Real.rpow_nonneg hBpos.le _)
      _ = ((1 : ℝ) + ‖z‖ ^ 2) ^ (-(2 * (2 * s.re + 1)) / 2) := by
          rw [← Real.rpow_add hBpos]; congr 1; ring

theorem norm_complexFactor_le (a b m : ℕ) (habm : a + b ≤ m) (σ : ℝ) (y : ℂ) :
    ‖y ^ a * (starRingEnd ℂ) y ^ b * (((1 + ‖y‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1) - (m : ℂ) / 2)‖
      ≤ (1 + ‖y‖ ^ 2) ^ (-(2 * σ + 1)) := by
  have hB1 : (1 : ℝ) ≤ 1 + ‖y‖ ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
  have hBpos : (0 : ℝ) < 1 + ‖y‖ ^ 2 := by linarith
  have hre : (-(2 * (σ : ℂ) + 1) - (m : ℂ) / 2).re = -(2 * σ + 1 + (m : ℝ) / 2) := by
    simp; ring
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj,
    Complex.norm_cpow_eq_rpow_re_of_pos hBpos, hre]
  have hz : ‖y‖ ≤ (1 + ‖y‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    calc ‖y‖ = Real.sqrt (‖y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg y)).symm
      _ ≤ Real.sqrt (1 + ‖y‖ ^ 2) := Real.sqrt_le_sqrt (by linarith)
      _ = (1 + ‖y‖ ^ 2) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
  have hzab : ‖y‖ ^ a * ‖y‖ ^ b ≤ (1 + ‖y‖ ^ 2) ^ ((m : ℝ) / 2) := by
    calc ‖y‖ ^ a * ‖y‖ ^ b = ‖y‖ ^ (a + b) := (pow_add _ _ _).symm
      _ ≤ ((1 + ‖y‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ (a + b) := pow_le_pow_left₀ (norm_nonneg y) hz _
      _ = (1 + ‖y‖ ^ 2) ^ ((1 : ℝ) / 2 * ((a + b : ℕ) : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hBpos.le]
      _ ≤ (1 + ‖y‖ ^ 2) ^ ((m : ℝ) / 2) := by
          refine Real.rpow_le_rpow_of_exponent_le hB1 ?_
          have hm : ((a + b : ℕ) : ℝ) ≤ m := by exact_mod_cast habm
          linarith
  calc ‖y‖ ^ a * ‖y‖ ^ b * (1 + ‖y‖ ^ 2) ^ (-(2 * σ + 1 + (m : ℝ) / 2))
      ≤ (1 + ‖y‖ ^ 2) ^ ((m : ℝ) / 2) * (1 + ‖y‖ ^ 2) ^ (-(2 * σ + 1 + (m : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_right hzab (Real.rpow_nonneg hBpos.le _)
    _ = (1 + ‖y‖ ^ 2) ^ (-(2 * σ + 1)) := by
        rw [← Real.rpow_add hBpos]; congr 1; ring

theorem floor (a b c d z : ℂ) :
    ‖a * d - b * c‖ ^ 2 * (1 + ‖z‖ ^ 2)
      ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) * (‖a + z * c‖ ^ 2 + ‖b + z * d‖ ^ 2) := by
  set P := a + z * c with hP
  set Q := b + z * d with hQ
  have h1 : a * d - b * c = d * P - c * Q := by rw [hP, hQ]; ring
  have h2 : z * (a * d - b * c) = a * Q - b * P := by rw [hP, hQ]; ring
  have n1 : ‖a * d - b * c‖ ≤ ‖d‖ * ‖P‖ + ‖c‖ * ‖Q‖ := by
    rw [h1]
    exact (norm_sub_le _ _).trans (by rw [norm_mul, norm_mul])
  have n2 : ‖z‖ * ‖a * d - b * c‖ ≤ ‖a‖ * ‖Q‖ + ‖b‖ * ‖P‖ := by
    rw [← norm_mul, h2]
    exact (norm_sub_le _ _).trans (by rw [norm_mul, norm_mul])
  have hD := norm_nonneg (a * d - b * c)
  have hz := norm_nonneg z
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have hc := norm_nonneg c
  have hd := norm_nonneg d
  have hPn := norm_nonneg P
  have hQn := norm_nonneg Q
  have s1 : ‖a * d - b * c‖ ^ 2 ≤ (‖d‖ ^ 2 + ‖c‖ ^ 2) * (‖P‖ ^ 2 + ‖Q‖ ^ 2) := by
    calc ‖a * d - b * c‖ ^ 2 ≤ (‖d‖ * ‖P‖ + ‖c‖ * ‖Q‖) ^ 2 :=
          pow_le_pow_left₀ hD n1 2
      _ ≤ (‖d‖ ^ 2 + ‖c‖ ^ 2) * (‖P‖ ^ 2 + ‖Q‖ ^ 2) := by
          nlinarith [sq_nonneg (‖d‖ * ‖Q‖ - ‖c‖ * ‖P‖)]
  have s2 : ‖z‖ ^ 2 * ‖a * d - b * c‖ ^ 2 ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2) * (‖P‖ ^ 2 + ‖Q‖ ^ 2) := by
    calc ‖z‖ ^ 2 * ‖a * d - b * c‖ ^ 2 = (‖z‖ * ‖a * d - b * c‖) ^ 2 := by ring
      _ ≤ (‖a‖ * ‖Q‖ + ‖b‖ * ‖P‖) ^ 2 := pow_le_pow_left₀ (mul_nonneg hz hD) n2 2
      _ ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2) * (‖P‖ ^ 2 + ‖Q‖ ^ 2) := by
          nlinarith [sq_nonneg (‖a‖ * ‖P‖ - ‖b‖ * ‖Q‖)]
  nlinarith [s1, s2]

theorem entries_pos {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) :
    0 < ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2 := by
  have h := floor a b c d 0
  simp only [norm_zero, add_zero, zero_mul] at h
  have hD : 0 < ‖a * d - b * c‖ ^ 2 := by positivity
  have hS : 0 ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by positivity
  nlinarith [h, hD, hS, sq_nonneg ‖c‖, sq_nonneg ‖d‖]

theorem main (a b c d : ℂ) (hdet : a * d - b * c ≠ 0) (a₀ b₀ m : ℕ) (habm : a₀ + b₀ ≤ m)
    (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun z : ℂ =>
      (((‖a * d - b * c‖ ^ 2 : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((‖a + z * c‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)))
        * ((fun σ z => z ^ a₀ * (starRingEnd ℂ) z ^ b₀
            * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1) - ((m : ℂ)) / 2)) σ
              ((b + z * d) / (a + z * c)))) := by
  set D : ℝ := ‖a * d - b * c‖ ^ 2 with hDdef
  set S : ℝ := ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2 with hSdef
  have hD : 0 < D := by positivity
  have hS : 0 < S := entries_pos hdet
  set K : ℝ := D ^ (σ + 1 / 2) * (D / S) ^ (-(2 * σ + 1)) with hKdef
  have hK : 0 ≤ K := mul_nonneg (Real.rpow_nonneg hD.le _) (Real.rpow_nonneg (div_pos hD hS).le _)

  have hmaj0 : Integrable (fun z : ℂ => ((1 : ℝ) + ‖z‖ ^ 2) ^ (-(2 * (2 * σ + 1)) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume)
      (by rw [Complex.finrank_real_complex]; push_cast; linarith)
  have hmaj : Integrable (fun z : ℂ => K * ((1 : ℝ) + ‖z‖ ^ 2) ^ (-(2 * σ + 1))) := by
    refine (hmaj0.const_mul K).congr (Filter.Eventually.of_forall fun z => ?_)
    show K * ((1 : ℝ) + ‖z‖ ^ 2) ^ (-(2 * (2 * σ + 1)) / 2) = K * ((1 : ℝ) + ‖z‖ ^ 2) ^ (-(2 * σ + 1))
    congr 1; congr 1; ring
  refine hmaj.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  ·
    apply Measurable.aestronglyMeasurable
    fun_prop
  ·
    simp only
    set P : ℂ := a + z * c with hPdef
    set Q : ℂ := b + z * d with hQdef
    have hB1 : (1 : ℝ) ≤ 1 + ‖z‖ ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
    have hBpos : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by linarith
    have hrhs0 : 0 ≤ K * ((1 : ℝ) + ‖z‖ ^ 2) ^ (-(2 * σ + 1)) :=
      mul_nonneg hK (Real.rpow_nonneg hBpos.le _)
    have hexp1 : ((σ : ℂ) + 1 / 2) = (((σ + 1 / 2 : ℝ)) : ℂ) := by push_cast; ring
    have hexp2 : (-(2 * (σ : ℂ) + 1)) = (((-(2 * σ + 1) : ℝ)) : ℂ) := by push_cast; ring
    rcases eq_or_ne P 0 with hP0 | hP0
    ·
      have hne : (-(2 * (σ : ℂ) + 1)) ≠ 0 := by
        intro h
        have := congrArg Complex.re h
        simp at this; linarith
      have hzero : ((‖P‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)) = 0 := by
        rw [hP0, norm_zero, zero_pow two_ne_zero, Complex.ofReal_zero]
        exact Complex.zero_cpow hne
      rw [hzero, mul_zero, zero_mul, norm_zero]
      exact hrhs0
    · have hPpos : 0 < ‖P‖ ^ 2 := by positivity
      set y : ℂ := Q / P with hydef
      have hy1 : (1 : ℝ) ≤ 1 + ‖y‖ ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
      have hypos : (0 : ℝ) < 1 + ‖y‖ ^ 2 := by linarith

      have nJ1 : ‖((D : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2)‖ = D ^ (σ + 1 / 2) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hD]; congr 1; simp
      have nJ2 : ‖((‖P‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1))‖ = (‖P‖ ^ 2) ^ (-(2 * σ + 1)) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hPpos]; congr 1; simp
      have hatom := norm_complexFactor_le a₀ b₀ m habm σ y

      have hPy : ‖P‖ ^ 2 * (1 + ‖y‖ ^ 2) = ‖P‖ ^ 2 + ‖Q‖ ^ 2 := by
        rw [hydef, norm_div]
        field_simp
      have hfl : D * (1 + ‖z‖ ^ 2) / S ≤ ‖P‖ ^ 2 + ‖Q‖ ^ 2 := by
        rw [div_le_iff₀ hS]
        have := floor a b c d z
        rw [← hPdef, ← hQdef] at this
        linarith
      have hflpos : 0 < D * (1 + ‖z‖ ^ 2) / S := by positivity
      calc ‖((D : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((‖P‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1))
              * (y ^ a₀ * (starRingEnd ℂ) y ^ b₀
                * (((1 + ‖y‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1) - ((m : ℂ)) / 2))‖
          = D ^ (σ + 1 / 2) * (‖P‖ ^ 2) ^ (-(2 * σ + 1))
              * ‖y ^ a₀ * (starRingEnd ℂ) y ^ b₀
                * (((1 + ‖y‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1) - ((m : ℂ)) / 2)‖ := by
            rw [norm_mul, norm_mul, nJ1, nJ2]
        _ ≤ D ^ (σ + 1 / 2) * (‖P‖ ^ 2) ^ (-(2 * σ + 1)) * (1 + ‖y‖ ^ 2) ^ (-(2 * σ + 1)) :=
            mul_le_mul_of_nonneg_left hatom
              (mul_nonneg (Real.rpow_nonneg hD.le _) (Real.rpow_nonneg hPpos.le _))
        _ = D ^ (σ + 1 / 2) * (‖P‖ ^ 2 + ‖Q‖ ^ 2) ^ (-(2 * σ + 1)) := by
            rw [mul_assoc, ← Real.mul_rpow hPpos.le hypos.le, hPy]
        _ ≤ D ^ (σ + 1 / 2) * (D * (1 + ‖z‖ ^ 2) / S) ^ (-(2 * σ + 1)) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hflpos hfl (by linarith))
              (Real.rpow_nonneg hD.le _)
        _ = K * ((1 : ℝ) + ‖z‖ ^ 2) ^ (-(2 * σ + 1)) := by
            rw [hKdef, show D * (1 + ‖z‖ ^ 2) / S = (D / S) * (1 + ‖z‖ ^ 2) from by ring,
              Real.mul_rpow (div_pos hD hS).le hBpos.le]
            ring

end IntArchC

end

theorem solution
    (a b c d : ℂ) (_hdet : a * d - b * c ≠ 0) (a₀ b₀ m : ℕ) (_habm : a₀ + b₀ ≤ m) (σ : ℝ) (_hσ : 0 < σ) :
    let atom : ℝ → ℂ → ℂ := fun σ z =>
      z ^ a₀ * (starRingEnd ℂ) z ^ b₀ * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1) - ((m : ℂ)) / 2)
    Integrable (atom σ) ∧
    Integrable (fun z : ℂ =>
      (((‖a * d - b * c‖ ^ 2 : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((‖a + z * c‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)))
        * atom σ ((b + z * d) / (a + z * c))) := by
  intro atom
  exact ⟨IntArchC.integrable_complexFactor a₀ b₀ m _habm (σ : ℂ) (by simpa using _hσ),
    IntArchC.main a b c d _hdet a₀ b₀ m _habm σ _hσ⟩

end S_AutomorphicForm_LocalIntertwining_integrable_complexAtom_and_integrable_moebiusShift
end P2MW
export P2MW.S_AutomorphicForm_LocalIntertwining_integrable_complexAtom_and_integrable_moebiusShift (solution)
