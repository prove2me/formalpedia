-- Prove2me | Definitions.Def_Esgk_CirclePolynomialRestriction
-- name    : Esgk_CirclePolynomialRestriction
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:55:09.789724+00:00
-- url     : https://prove2.me/theorems/744ea1cb-4fca-4444-82d5-cce2f37829a9
-- title:
--   Restricting a polynomial along a rational circle parametrization
-- statement:
--   This constructs numerator and denominator polynomials for rational parametrization of a circle, clears denominators in a restricted plane polynomial, and records its evaluations, degree bounds, and finite-root consequences.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_CircleRationalParametrization
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open EuclideanGeometry PachDeZeeuw.Algebraic Polynomial

 
def circleDenominatorPolynomial : Polynomial ℝ :=
  1 + X ^ 2

 
def circleFirstNumeratorPolynomial (c : Point2) (r : ℝ) : Polynomial ℝ :=
  C (c 0) * circleDenominatorPolynomial + C r * (1 - X ^ 2)

 
def circleSecondNumeratorPolynomial (c : Point2) (r : ℝ) : Polynomial ℝ :=
  C (c 1) * circleDenominatorPolynomial + C r * (C 2 * X)

@[simp]
theorem eval_circleDenominatorPolynomial (t : ℝ) :
    eval t circleDenominatorPolynomial = circleParamDenominator t := by
  simp [circleDenominatorPolynomial, circleParamDenominator]

@[simp]
theorem eval_circleFirstNumeratorPolynomial (c : Point2) (r t : ℝ) :
    eval t (circleFirstNumeratorPolynomial c r) =
      c 0 * circleParamDenominator t + r * (1 - t ^ 2) := by
  simp [circleFirstNumeratorPolynomial]

@[simp]
theorem eval_circleSecondNumeratorPolynomial (c : Point2) (r t : ℝ) :
    eval t (circleSecondNumeratorPolynomial c r) =
      c 1 * circleParamDenominator t + r * (2 * t) := by
  simp [circleSecondNumeratorPolynomial]


theorem circleRationalParam_apply_zero_eq_eval_div
    (c : Point2) (r t : ℝ) :
    circleRationalParam c r t 0 =
      eval t (circleFirstNumeratorPolynomial c r) /
        eval t circleDenominatorPolynomial := by
  rw [eval_circleFirstNumeratorPolynomial, eval_circleDenominatorPolynomial]
  rw [circleRationalParam_apply_zero]
  field_simp [circleParamDenominator_ne_zero]


theorem circleRationalParam_apply_one_eq_eval_div
    (c : Point2) (r t : ℝ) :
    circleRationalParam c r t 1 =
      eval t (circleSecondNumeratorPolynomial c r) /
        eval t circleDenominatorPolynomial := by
  rw [eval_circleSecondNumeratorPolynomial, eval_circleDenominatorPolynomial]
  rw [circleRationalParam_apply_one]
  field_simp [circleParamDenominator_ne_zero]

 
@[simp]
theorem coeff_two_circleDenominatorPolynomial :
    circleDenominatorPolynomial.coeff 2 = 1 := by
  simp [circleDenominatorPolynomial, Polynomial.coeff_one]


@[simp]
theorem coeff_two_circleFirstNumeratorPolynomial (c : Point2) (r : ℝ) :
    (circleFirstNumeratorPolynomial c r).coeff 2 =
      circleRationalBasePoint c r 0 := by
  simp [circleFirstNumeratorPolynomial, circleDenominatorPolynomial,
    circleRationalBasePoint, Polynomial.coeff_one, sub_eq_add_neg]


@[simp]
theorem coeff_two_circleSecondNumeratorPolynomial (c : Point2) (r : ℝ) :
    (circleSecondNumeratorPolynomial c r).coeff 2 =
      circleRationalBasePoint c r 1 := by
  simp [circleSecondNumeratorPolynomial, circleDenominatorPolynomial,
    circleRationalBasePoint, Polynomial.coeff_one]

 
theorem natDegree_circleDenominatorPolynomial_le :
    circleDenominatorPolynomial.natDegree ≤ 2 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hn2 : n ≠ 2 := by omega
  simp [circleDenominatorPolynomial, Polynomial.coeff_one, hn0, hn2]

 
theorem natDegree_circleFirstNumeratorPolynomial_le
    (c : Point2) (r : ℝ) :
    (circleFirstNumeratorPolynomial c r).natDegree ≤ 2 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hn2 : n ≠ 2 := by omega
  simp [circleFirstNumeratorPolynomial, circleDenominatorPolynomial,
    Polynomial.coeff_one, hn0, hn2]

 
theorem natDegree_circleSecondNumeratorPolynomial_le
    (c : Point2) (r : ℝ) :
    (circleSecondNumeratorPolynomial c r).natDegree ≤ 2 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have hn2 : n ≠ 2 := by omega
  have hcoeffX : (X : Polynomial ℝ).coeff n = 0 :=
    Polynomial.coeff_X_of_ne_one hn1
  simp [circleSecondNumeratorPolynomial, circleDenominatorPolynomial,
    Polynomial.coeff_one, hn0, hn2, hcoeffX]

 
def circleClearedMonomial (c : Point2) (r : ℝ) (d i j : ℕ) (a : ℝ) :
    Polynomial ℝ :=
  C a * circleFirstNumeratorPolynomial c r ^ i *
      circleSecondNumeratorPolynomial c r ^ j *
    circleDenominatorPolynomial ^ (d - i - j)


theorem natDegree_circleClearedMonomial_le
    (c : Point2) (r : ℝ) (d i j : ℕ) (a : ℝ) (hij : i + j ≤ d) :
    (circleClearedMonomial c r d i j a).natDegree ≤ 2 * d := by
  have hcoeff : (C a : Polynomial ℝ).natDegree ≤ 0 := by
    simp
  have hfirst :
      (circleFirstNumeratorPolynomial c r ^ i).natDegree ≤ i * 2 :=
    Polynomial.natDegree_pow_le_of_le i
      (natDegree_circleFirstNumeratorPolynomial_le c r)
  have hsecond :
      (circleSecondNumeratorPolynomial c r ^ j).natDegree ≤ j * 2 :=
    Polynomial.natDegree_pow_le_of_le j
      (natDegree_circleSecondNumeratorPolynomial_le c r)
  have hdenominator :
      (circleDenominatorPolynomial ^ (d - i - j)).natDegree ≤
        (d - i - j) * 2 :=
    Polynomial.natDegree_pow_le_of_le (d - i - j)
      natDegree_circleDenominatorPolynomial_le
  have hfirstProduct :
      (C a * circleFirstNumeratorPolynomial c r ^ i).natDegree ≤
        0 + i * 2 :=
    Polynomial.natDegree_mul_le_of_le hcoeff hfirst
  have hsecondProduct :
      (C a * circleFirstNumeratorPolynomial c r ^ i *
        circleSecondNumeratorPolynomial c r ^ j).natDegree ≤
          (0 + i * 2) + j * 2 :=
    Polynomial.natDegree_mul_le_of_le hfirstProduct hsecond
  calc
    (circleClearedMonomial c r d i j a).natDegree ≤
        ((0 + i * 2) + j * 2) + (d - i - j) * 2 := by
      exact Polynomial.natDegree_mul_le_of_le hsecondProduct hdenominator
    _ = 2 * d := by omega


theorem eval_circleClearedMonomial
    (c : Point2) (r t : ℝ) (d i j : ℕ) (a : ℝ) (hij : i + j ≤ d) :
    eval t (circleClearedMonomial c r d i j a) =
      circleParamDenominator t ^ d * a *
        (circleRationalParam c r t 0) ^ i *
          (circleRationalParam c r t 1) ^ j := by
  rw [circleRationalParam_apply_zero_eq_eval_div,
    circleRationalParam_apply_one_eq_eval_div]
  simp only [circleClearedMonomial, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C]
  rw [eval_circleDenominatorPolynomial]
  have hden := circleParamDenominator_ne_zero t
  have hpow :
      circleParamDenominator t ^ d =
        circleParamDenominator t ^ i * circleParamDenominator t ^ j *
          circleParamDenominator t ^ (d - i - j) := by
    calc
      circleParamDenominator t ^ d =
          circleParamDenominator t ^ (i + j + (d - i - j)) := by
        congr 1
        omega
      _ = circleParamDenominator t ^ i * circleParamDenominator t ^ j *
          circleParamDenominator t ^ (d - i - j) := by
        rw [pow_add, pow_add]
  rw [hpow, div_pow, div_pow]
  field_simp [hden]


theorem coeff_two_mul_circleClearedMonomial
    (c : Point2) (r : ℝ) (d i j : ℕ) (a : ℝ) (hij : i + j ≤ d) :
    (circleClearedMonomial c r d i j a).coeff (2 * d) =
      a * (circleRationalBasePoint c r 0) ^ i *
        (circleRationalBasePoint c r 1) ^ j := by
  have hcoeff : (C a : Polynomial ℝ).natDegree ≤ 0 := by
    simp
  have hfirst :
      (circleFirstNumeratorPolynomial c r ^ i).natDegree ≤ i * 2 :=
    Polynomial.natDegree_pow_le_of_le i
      (natDegree_circleFirstNumeratorPolynomial_le c r)
  have hsecond :
      (circleSecondNumeratorPolynomial c r ^ j).natDegree ≤ j * 2 :=
    Polynomial.natDegree_pow_le_of_le j
      (natDegree_circleSecondNumeratorPolynomial_le c r)
  have hdenominator :
      (circleDenominatorPolynomial ^ (d - i - j)).natDegree ≤
        (d - i - j) * 2 :=
    Polynomial.natDegree_pow_le_of_le (d - i - j)
      natDegree_circleDenominatorPolynomial_le
  have hfirstProduct :
      (C a * circleFirstNumeratorPolynomial c r ^ i).natDegree ≤
        0 + i * 2 :=
    Polynomial.natDegree_mul_le_of_le hcoeff hfirst
  have hsecondProduct :
      (C a * circleFirstNumeratorPolynomial c r ^ i *
        circleSecondNumeratorPolynomial c r ^ j).natDegree ≤
          (0 + i * 2) + j * 2 :=
    Polynomial.natDegree_mul_le_of_le hfirstProduct hsecond
  rw [circleClearedMonomial]
  have hindex :
      2 * d = ((0 + i * 2) + j * 2) + (d - i - j) * 2 := by
    omega
  rw [hindex]
  rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hsecondProduct hdenominator]
  rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hfirstProduct hsecond]
  rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hcoeff hfirst]
  rw [Polynomial.coeff_pow_of_natDegree_le
      (natDegree_circleFirstNumeratorPolynomial_le c r)]
  rw [Polynomial.coeff_pow_of_natDegree_le
      (natDegree_circleSecondNumeratorPolynomial_le c r)]
  rw [Polynomial.coeff_pow_of_natDegree_le
      natDegree_circleDenominatorPolynomial_le]
  simp


def circlePolynomialRestrictionCleared
    (p : PlanePoly) (c : Point2) (r : ℝ) (d : ℕ) : Polynomial ℝ :=
  (AddMonoidAlgebra.coeff p).sum fun exponent coefficient ↦
    circleClearedMonomial c r d (exponent 0) (exponent 1) coefficient


theorem natDegree_circlePolynomialRestrictionCleared_le
    (p : PlanePoly) (c : Point2) (r : ℝ) (d : ℕ)
    (hdegree : p.totalDegree ≤ d) :
    (circlePolynomialRestrictionCleared p c r d).natDegree ≤ 2 * d := by
  rw [circlePolynomialRestrictionCleared, MvPolynomial.sum_def]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro exponent hexponent
  apply natDegree_circleClearedMonomial_le
  have htotal := (MvPolynomial.le_totalDegree hexponent).trans hdegree
  simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using htotal


theorem eval_circlePolynomialRestrictionCleared
    (p : PlanePoly) (c : Point2) (r t : ℝ) (d : ℕ)
    (hdegree : p.totalDegree ≤ d) :
    eval t (circlePolynomialRestrictionCleared p c r d) =
      circleParamDenominator t ^ d *
        MvPolynomial.eval (fun i ↦ circleRationalParam c r t i) p := by
  rw [circlePolynomialRestrictionCleared, MvPolynomial.sum_def,
    Polynomial.eval_finsetSum, MvPolynomial.eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro exponent hexponent
  have htotal := (MvPolynomial.le_totalDegree hexponent).trans hdegree
  have hij : exponent 0 + exponent 1 ≤ d := by
    simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using htotal
  rw [eval_circleClearedMonomial c r t d (exponent 0) (exponent 1)
    (p.coeff exponent) hij]
  simp [Fin.prod_univ_two]
  ring


theorem coeff_two_mul_circlePolynomialRestrictionCleared
    (p : PlanePoly) (c : Point2) (r : ℝ) (d : ℕ)
    (hdegree : p.totalDegree ≤ d) :
    (circlePolynomialRestrictionCleared p c r d).coeff (2 * d) =
      MvPolynomial.eval (fun i ↦ circleRationalBasePoint c r i) p := by
  rw [circlePolynomialRestrictionCleared, MvPolynomial.sum_def,
    MvPolynomial.eval_eq']
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro exponent hexponent
  have htotal := (MvPolynomial.le_totalDegree hexponent).trans hdegree
  have hij : exponent 0 + exponent 1 ≤ d := by
    simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using htotal
  rw [coeff_two_mul_circleClearedMonomial c r d (exponent 0)
    (exponent 1) (p.coeff exponent) hij]
  simp [Fin.prod_univ_two]
  ring


theorem circlePolynomialRestrictionCleared_ne_zero_of_not_sphere_subset
    (p : PlanePoly) (c : Point2) (r : ℝ) (d : ℕ)
    (hr : 0 < r) (hdegree : p.totalDegree ≤ d)
    (hnot : ¬ Metric.sphere c r ⊆ PlaneCurveZeroSet p) :
    circlePolynomialRestrictionCleared p c r d ≠ 0 := by
  intro hrestriction
  apply hnot
  intro z hz
  rw [mem_PlaneCurveZeroSet]
  by_cases hzbase : z = circleRationalBasePoint c r
  · subst z
    have htop :=
      coeff_two_mul_circlePolynomialRestrictionCleared p c r d hdegree
    rw [hrestriction] at htop
    simpa using htop.symm
  · obtain ⟨t, ht⟩ :=
      exists_circleRationalParam_eq_of_mem_sphere_ne_base c hr hz hzbase
    have heval :=
      eval_circlePolynomialRestrictionCleared p c r t d hdegree
    rw [hrestriction] at heval
    simp only [Polynomial.eval_zero] at heval
    have hparamZero :
        MvPolynomial.eval
            (fun i ↦ circleRationalParam c r t i) p = 0 := by
      have hdenPow : circleParamDenominator t ^ d ≠ 0 :=
        pow_ne_zero d (circleParamDenominator_ne_zero t)
      exact (mul_eq_zero.mp heval.symm).resolve_left hdenPow
    simpa [ht] using hparamZero


theorem finite_circle_zeroSet_card_le_two_mul
    (p : PlanePoly) (c : Point2) (r : ℝ) (d : ℕ) (S : Finset Point2)
    (hr : 0 < r) (hdegree : p.totalDegree ≤ d)
    (hzero : ∀ z ∈ S, MvPolynomial.eval (fun i ↦ z i) p = 0)
    (hcircle : ∀ z ∈ S, z ∈ Metric.sphere c r)
    (hrestriction : circlePolynomialRestrictionCleared p c r d ≠ 0) :
    S.card ≤ 2 * d := by
  let H := circlePolynomialRestrictionCleared p c r d
  let param := circleRationalParam c r
  let base := circleRationalBasePoint c r
  have hroot_of_param {z : Point2} (hz : z ∈ S) {t : ℝ}
      (ht : circleRationalParam c r t = z) :
      t ∈ H.roots.toFinset := by
    have heval : eval t H = 0 := by
      rw [show H = circlePolynomialRestrictionCleared p c r d by rfl]
      rw [eval_circlePolynomialRestrictionCleared p c r t d hdegree]
      have hzpoly := hzero z hz
      have hparamEval :
          MvPolynomial.eval
              (fun i ↦ circleRationalParam c r t i) p = 0 := by
        simpa [ht] using hzpoly
      rw [hparamEval, mul_zero]
    rw [Multiset.mem_toFinset]
    exact (Polynomial.mem_roots hrestriction).2
      ((Polynomial.IsRoot.def).2 heval)
  have hdegreeH : H.natDegree ≤ 2 * d := by
    exact natDegree_circlePolynomialRestrictionCleared_le p c r d hdegree
  by_cases hbaseZero :
      MvPolynomial.eval (fun i ↦ circleRationalBasePoint c r i) p = 0
  · have htop : H.coeff (2 * d) = 0 := by
      rw [show H = circlePolynomialRestrictionCleared p c r d by rfl]
      rw [coeff_two_mul_circlePolynomialRestrictionCleared p c r d hdegree]
      exact hbaseZero
    have hdegreeDrop : H.natDegree ≤ 2 * d - 1 :=
      Polynomial.natDegree_le_pred hdegreeH htop
    have hpositive : 0 < 2 * d := by
      by_contra hnot
      have hzeroDegree : 2 * d = 0 := Nat.eq_zero_of_not_pos hnot
      have hdegreeZero : H.natDegree ≤ 0 := by
        simpa [hzeroDegree] using hdegreeH
      have hcoeffZero : H.coeff 0 = 0 := by
        simpa [hzeroDegree] using htop
      have hHzero : H = 0 := by
        rw [Polynomial.eq_C_of_natDegree_le_zero hdegreeZero, hcoeffZero]
        simp
      exact hrestriction (by simpa [H] using hHzero)
    have hcard : S.card ≤ H.natDegree + 1 := by
      apply card_le_natDegree_add_one_of_parametrized_roots S H param base
      intro z hz
      by_cases hzbase : z = circleRationalBasePoint c r
      · exact Or.inl hzbase
      · right
        obtain ⟨t, ht⟩ :=
          exists_circleRationalParam_eq_of_mem_sphere_ne_base
            c hr (hcircle z hz) hzbase
        exact ⟨t, hroot_of_param hz ht, ht⟩
    exact hcard.trans (by omega)
  · apply le_trans
      (card_le_natDegree_of_parametrized_roots S H param ?_)
      hdegreeH
    intro z hz
    have hzbase : z ≠ circleRationalBasePoint c r := by
      intro hzbase
      apply hbaseZero
      have hzpoly := hzero z hz
      simpa [hzbase] using hzpoly
    obtain ⟨t, ht⟩ :=
      exists_circleRationalParam_eq_of_mem_sphere_ne_base
        c hr (hcircle z hz) hzbase
    exact ⟨t, hroot_of_param hz ht, ht⟩


theorem finite_circle_zeroSet_card_le_two_mul_of_not_sphere_subset
    (p : PlanePoly) (c : Point2) (r : ℝ) (d : ℕ) (S : Finset Point2)
    (hr : 0 < r) (hdegree : p.totalDegree ≤ d)
    (hzero : ∀ z ∈ S, MvPolynomial.eval (fun i ↦ z i) p = 0)
    (hcircle : ∀ z ∈ S, z ∈ Metric.sphere c r)
    (hnot : ¬ Metric.sphere c r ⊆ PlaneCurveZeroSet p) :
    S.card ≤ 2 * d :=
  finite_circle_zeroSet_card_le_two_mul p c r d S hr hdegree hzero
    hcircle
    (circlePolynomialRestrictionCleared_ne_zero_of_not_sphere_subset
      p c r d hr hdegree hnot)

end Esgk


