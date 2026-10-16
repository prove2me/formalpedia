-- Prove2me | Definitions.Def_Esgk_PachDeZeeuwCurveSymmetryTranslation
-- name    : Esgk_PachDeZeeuwCurveSymmetryTranslation
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T05:03:34.530707+00:00
-- url     : https://prove2.me/theorems/26213fb1-8a3e-4eff-b0d6-6ea6fa68cde6
-- title:
--   Translation symmetries of irreducible plane curves
-- statement:
--   An infinite nonzero translation orbit on an irreducible plane curve forces its defining polynomial to divide a linear polynomial. This excludes nontrivial translations for curves that are neither lines nor circles and yields the corresponding finite symmetry bound.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_DirectIsometryClassification
import Definitions.Def_Esgk_IrreduciblePlaneInfiniteVanishing
import Definitions.Def_Esgk_PachDeZeeuwCurveSymmetryCommonCenter
import Definitions.Def_Esgk_PachDeZeeuwCurveSymmetryReduction
import Definitions.Def_Esgk_PlaneAffineLinePolynomial
import Definitions.Def_Esgk_SelfCurveReflectionInvariance
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveSymmetries
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry

theorem bundle_Esgk_PachDeZeeuwCurveSymmetryTranslation_translationOrbit_mem_affineLineZeroSet
    {x v z : CurveSymmetries.Point2} {n : ℕ}
    (hz : z = x + (n : ℝ) • v) :
    z ∈ PachDeZeeuw.Algebraic.PlaneCurveZeroSet
      (affineLinePolynomial x v) := by
  rw [hz]
  change MvPolynomial.eval (fun i ↦ (x + (n : ℝ) • v) i)
      (affineLinePolynomial x v) = 0
  rw [affineLinePolynomial_eval]
  change v 1 * (x 0 + (n : ℝ) * v 0 - x 0) -
    v 0 * (x 1 + (n : ℝ) * v 1 - x 1) = 0
  ring

theorem bundle_Esgk_PachDeZeeuwCurveSymmetryTranslation_translationOrbit_infinite
    {x v : CurveSymmetries.Point2} (hv : v ≠ 0) :
    Set.Infinite (Set.range (fun n : ℕ ↦ x + (n : ℝ) • v)) := by
  apply Set.infinite_range_of_injective
  intro m n hmn
  by_cases hv0 : v 0 = 0
  · have hv1 : v 1 ≠ 0 := by
      intro hv1
      apply hv
      ext i
      fin_cases i <;> simp [hv0, hv1]
    have hcoord := congrArg (fun z : CurveSymmetries.Point2 ↦ z 1) hmn
    have hscalar : (m : ℝ) * v 1 = (n : ℝ) * v 1 := by
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hcoord
    have hmnR : (m : ℝ) = (n : ℝ) := mul_right_cancel₀ hv1 hscalar
    exact_mod_cast hmnR
  · have hcoord := congrArg (fun z : CurveSymmetries.Point2 ↦ z 0) hmn
    have hscalar : (m : ℝ) * v 0 = (n : ℝ) * v 0 := by
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hcoord
    have hmnR : (m : ℝ) = (n : ℝ) := mul_right_cancel₀ hv0 hscalar
    exact_mod_cast hmnR


theorem CurveSymmetries.dvd_affineLinePolynomial_of_translationOrbit
    {d : ℕ} {C : Set CurveSymmetries.Point2}
    (hcurve : CurveSymmetries.IsIrreducibleCurve d C)
    {x v : CurveSymmetries.Point2} (hv : v ≠ 0)
    (horbit : ∀ n : ℕ, x + (n : ℝ) • v ∈ C) :
    ∃ p : MvPolynomial (Fin 2) ℝ,
      p ≠ 0 ∧ Irreducible p ∧
      C = CurveSymmetries.PlaneCurveZeroSet p ∧
      p ∣ affineLinePolynomial x v := by
  rcases hcurve with ⟨p, hp0, _hpdeg, hpirreducible, hC⟩
  refine ⟨p, hp0, hpirreducible, hC, ?_⟩
  apply dvd_of_infinite_irreducible_zeroSet_intersection hpirreducible
  have hCzero : C = PachDeZeeuw.Algebraic.PlaneCurveZeroSet p := by
    simpa [CurveSymmetries.PlaneCurveZeroSet,
      PachDeZeeuw.Algebraic.PlaneCurveZeroSet] using hC
  have hsubset : Set.range (fun n : ℕ ↦ x + (n : ℝ) • v) ⊆
      PachDeZeeuw.Algebraic.PlaneCurveZeroSet p ∩
        PachDeZeeuw.Algebraic.PlaneCurveZeroSet
          (affineLinePolynomial x v) := by
    intro z hz
    obtain ⟨n, rfl⟩ := hz
    refine ⟨?_, bundle_Esgk_PachDeZeeuwCurveSymmetryTranslation_translationOrbit_mem_affineLineZeroSet rfl⟩
    rw [← hCzero]
    exact horbit n
  exact Set.Infinite.mono hsubset (bundle_Esgk_PachDeZeeuwCurveSymmetryTranslation_translationOrbit_infinite (x := x) hv)


theorem CurveSymmetries.translationOrbit_of_identityLinearPart_preserving
    {C : Set CurveSymmetries.Point2}
    {g : IsometryEquiv CurveSymmetries.Point2 CurveSymmetries.Point2}
    (hlinear : planeIsometryLinearPart g = 1)
    (hpreserves : g '' C = C)
    {x : CurveSymmetries.Point2} (hx : x ∈ C) :
    ∀ n : ℕ, x + (n : ℝ) • g 0 ∈ C := by
  have htranslation : ∀ y : CurveSymmetries.Point2, g y = y + g 0 :=
    planeIsometry_apply_eq_add_zero_of_linearPart_eq_one hlinear
  intro n
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      have himage : g (x + (n : ℝ) • g 0) ∈ g '' C :=
        ⟨x + (n : ℝ) • g 0, ih, rfl⟩
      have hnext : g (x + (n : ℝ) • g 0) ∈ C := by
        rw [← hpreserves]
        exact himage
      rw [htranslation] at hnext
      convert hnext using 1
      module


theorem CurveSymmetries.dvd_affineLinePolynomial_of_translationSymmetry
    {d : ℕ} {C : Set CurveSymmetries.Point2}
    {g : IsometryEquiv CurveSymmetries.Point2 CurveSymmetries.Point2}
    (hcurve : CurveSymmetries.IsIrreducibleCurve d C)
    (hne : g ≠ 1) (hlinear : planeIsometryLinearPart g = 1)
    (hpreserves : g '' C = C)
    {x : CurveSymmetries.Point2} (hx : x ∈ C) :
    ∃ p : MvPolynomial (Fin 2) ℝ,
      p ≠ 0 ∧ Irreducible p ∧
      C = CurveSymmetries.PlaneCurveZeroSet p ∧
      p ∣ affineLinePolynomial x (g 0) := by
  have hzero : g 0 ≠ 0 :=
    planeIsometry_zero_ne_zero_of_ne_one_of_linearPart_eq_one hne hlinear
  apply CurveSymmetries.dvd_affineLinePolynomial_of_translationOrbit
    hcurve hzero
  exact CurveSymmetries.translationOrbit_of_identityLinearPart_preserving
    hlinear hpreserves hx


theorem CurveSymmetries.noNontrivialTranslationSymmetry :
    CurveSymmetries.NoNontrivialTranslationSymmetryStatement := by
  intro d C hcurve hnot g hpreserves hlinear
  by_contra hne
  obtain ⟨x, hx, _hxne⟩ :=
    CurveSymmetries.exists_mem_ne_of_not_lineOrCircle hnot 0
  obtain ⟨p, _hp0, hpirreducible, hC, hpdivides⟩ :=
    CurveSymmetries.dvd_affineLinePolynomial_of_translationSymmetry
      hcurve hne hlinear hpreserves hx
  have hzero : g 0 ≠ 0 :=
    planeIsometry_zero_ne_zero_of_ne_one_of_linearPart_eq_one hne hlinear
  have hlineIrreducible : Irreducible (affineLinePolynomial x (g 0)) :=
    affineLinePolynomial_irreducible hzero
  have hassociated : Associated p (affineLinePolynomial x (g 0)) :=
    hpirreducible.associated_of_dvd hlineIrreducible hpdivides
  have hzeroSets :
      PachDeZeeuw.Algebraic.PlaneCurveZeroSet p =
        PachDeZeeuw.Algebraic.PlaneCurveZeroSet
          (affineLinePolynomial x (g 0)) :=
    zeroSet_eq_of_associated hassociated
  have hcarrierLine : C =
      {z : CurveSymmetries.Point2 |
        (g 0) 1 * z 0 + (-(g 0) 0) * z 1 =
          (g 0) 1 * x 0 - (g 0) 0 * x 1} := by
    calc
      C = CurveSymmetries.PlaneCurveZeroSet p := hC
      _ = PachDeZeeuw.Algebraic.PlaneCurveZeroSet p := by
        rfl
      _ = PachDeZeeuw.Algebraic.PlaneCurveZeroSet
          (affineLinePolynomial x (g 0)) := hzeroSets
      _ = {z : CurveSymmetries.Point2 |
          (g 0) 1 * z 0 + (-(g 0) 0) * z 1 =
            (g 0) 1 * x 0 - (g 0) 0 * x 1} :=
        affineLinePolynomial_zeroSet_eq_line x (g 0)
  apply hnot
  exact Or.inl ⟨(g 0) 1, -(g 0) 0,
    (g 0) 1 * x 0 - (g 0) 0 * x 1,
    affineLinePolynomial_direction_ne_zero hzero, hcarrierLine⟩


theorem CurveSymmetries.lemma25 : CurveSymmetries.Lemma25Statement :=
  CurveSymmetries.lemma25_of_noNontrivialTranslationSymmetry
    CurveSymmetries.noNontrivialTranslationSymmetry

end Esgk


