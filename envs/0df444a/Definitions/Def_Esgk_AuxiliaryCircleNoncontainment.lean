-- Prove2me | Definitions.Def_Esgk_AuxiliaryCircleNoncontainment
-- name    : Esgk_AuxiliaryCircleNoncontainment
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:57:44.524229+00:00
-- url     : https://prove2.me/theorems/a35c0765-1a4d-47a5-b9e3-cf927d28bed8
-- title:
--   Circle equations and finite self-incidence exclusions
-- statement:
--   This defines the polynomial equation of a Euclidean circle, identifies its zero set with the corresponding sphere, and records a finite deleted-label set for prepared incidence data.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_AuxiliaryIncidenceDeletion
import Definitions.Def_Esgk_CircleRationalParametrization
import Definitions.Def_Esgk_PlaneAffineIsometryDistancePolynomial
import Definitions.Def_Esgk_SelfCurveDistancePairs
import Definitions.Def_Esgk_SelfCurveReflectionInvariance
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Definitions.Def_LeanFormalizations_PachDeZeeuw_Basic
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveInterface
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open EuclideanGeometry PachDeZeeuw PachDeZeeuw.Algebraic

 
def circleEquationPolynomial (c : _root_.Point2) (r : ℝ) : PlanePoly :=
  planeSquaredDistancePolynomial c - MvPolynomial.C (r ^ 2)

 
theorem circleEquationPolynomial_ne_zero (c : _root_.Point2)
    {r : ℝ} (hr : r ≠ 0) :
    circleEquationPolynomial c r ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval (fun i : Fin 2 ↦ c i)) hzero
  have hrSq : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  apply hrSq
  simpa [circleEquationPolynomial] using heval


theorem circleEquationPolynomial_zeroSet (c : _root_.Point2)
    {r : ℝ} (hr : 0 ≤ r) :
    PlaneCurveZeroSet (circleEquationPolynomial c r) = Metric.sphere c r := by
  ext z
  simp only [mem_PlaneCurveZeroSet, Metric.mem_sphere]
  rw [circleEquationPolynomial, map_sub, eval_planeSquaredDistancePolynomial]
  simp only [MvPolynomial.eval_C, sub_eq_zero]
  constructor
  · intro hsq
    nlinarith [dist_nonneg (x := z) (y := c)]
  · intro hdist
    rw [hdist]


theorem sphere_isBoundedDegreeCurve (c : _root_.Point2)
    {r : ℝ} (hr : 0 < r) :
    PlaneCurve.IsBoundedDegreeCurve
      (circleEquationPolynomial c r).totalDegree (Metric.sphere c r) := by
  refine ⟨circleEquationPolynomial c r,
    circleEquationPolynomial_ne_zero c (ne_of_gt hr), le_rfl, ?_⟩
  simpa [PlaneCurveZeroSet] using
    (circleEquationPolynomial_zeroSet c hr.le).symm


theorem sphere_infinite (c : _root_.Point2) {r : ℝ} (hr : 0 < r) :
    (Metric.sphere c r).Infinite := by
  have hrange : (Set.range (circleRationalParam c r)).Infinite :=
    Set.infinite_range_of_injective
      (circleRationalParam_injective c (ne_of_gt hr))
  refine hrange.mono ?_
  rintro z ⟨t, rfl⟩
  exact circleRationalParam_mem_sphere c hr.le t


noncomputable def selfCurveDeletedLabels {d : ℕ}
    (X : PreparedBipartiteInput d) (E : Finset X.P₁)
    (Γ : Finset (X.P₁ × X.P₁)) : Finset (X.P₁ × X.P₁) := by
  classical
  exact deletedIndexedPairs Finset.univ E Γ


end Esgk


