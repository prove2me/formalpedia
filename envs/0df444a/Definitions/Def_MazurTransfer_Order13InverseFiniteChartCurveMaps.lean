-- Prove2me | Definitions.Def_MazurTransfer_Order13InverseFiniteChartCurveMaps
-- name    : MazurTransfer_Order13InverseFiniteChartCurveMaps
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T06:11:05.106788+00:00
-- url     : https://prove2.me/theorems/12008a29-c276-4ed2-b789-00ab9efa37fc
-- title:
--   The original inverse-atlas maps into the actual order-thirteen curve
-- statement:
--   For a commutative ring $R$, the actual ordinary parameter localization and positive reciprocal patch have their specified maps to the actual order-thirteen curve. Both maps preserve the structure map to $\operatorname{Spec}R$. If $2$ is invertible, the positive infinity section lifts to the reciprocal patch. These literal morphisms and structural identities supply the target maps for the inverse finite-chart gluing.
-- source:
--   Nine original declarations from MazurTheorem Order13InverseParameterCurveChartMaps.lean, Apache-2.0, Vas and contributors. Only imports change to the public inverse finite atlas and integral infinity sections interfaces. Every original declaration body is unchanged. All nine original closed types and four original data values are compared in the kernel. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumer: the global inverse finite-chart comparison, over its actual structural base.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: both inverse finite-chart sources map into the actual
original curve over its actual structural base, and the positive infinity
section lifts into the positive reciprocal patch. No gluing is assumed.
Named downstream consumer: the global inverse finite-chart comparison.
-/
import Definitions.Def_MazurTransfer_Order13InverseFiniteSchemeAtlas
import Definitions.Def_MazurTransfer_Order13IntegralInfinitySections

noncomputable section
universe u
namespace MazurTransfer.Order13InverseParameterFiniteAlgebra
open Polynomial CategoryTheory AlgebraicGeometry
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13SingleSectionFiniteAlgebra (ordinaryParameterLocalization)
variable (R : Type u) [CommRing R]

def ordinaryParameterCurveMap : Spec (.of (ordinaryParameterLocalization R)) ⟶ curveScheme R :=
  Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing R) (ordinaryParameterLocalization R))) ≫
    ordinaryChartMap R

def positiveReciprocalCurveMap :
    Spec (.of (Order13InverseParameterPositiveReciprocalPatch.PatchRing R)) ⟶ curveScheme R :=
  Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing R)
    (Order13InverseParameterPositiveReciprocalPatch.PatchRing R))) ≫ reciprocalChartMap R

theorem ordinaryParameterCurveMap_base : ordinaryParameterCurveMap R ≫ curveToBase R =
    Spec.map (CommRingCat.ofHom (algebraMap R (ordinaryParameterLocalization R))) := by
  rw [ordinaryParameterCurveMap,Category.assoc,ordinaryChartMap_curveToBase]
  unfold ordinaryChartToBase
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact (IsScalarTower.algebraMap_eq R (CoordinateRing R) (ordinaryParameterLocalization R)).symm

theorem positiveReciprocalCurveMap_base : positiveReciprocalCurveMap R ≫ curveToBase R =
    Spec.map (CommRingCat.ofHom (algebraMap R (Order13InverseParameterPositiveReciprocalPatch.PatchRing R))) := by
  rw [positiveReciprocalCurveMap,Category.assoc,reciprocalChartMap_curveToBase]
  unfold reciprocalChartToBase
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact (IsScalarTower.algebraMap_eq R (ReciprocalRing R)
    (Order13InverseParameterPositiveReciprocalPatch.PatchRing R)).symm

def positiveInfinityPatchEvaluation (h2 : IsUnit (2 : R)) :
    Order13InverseParameterPositiveReciprocalPatch.PatchRing R →+* R :=
  IsLocalization.Away.lift (g := Order13IntegralSections.reciprocalInfinityEvaluation R 1 (by simp))
    (x := Order13InverseParameterPositiveReciprocalPatch.f R *
      Order13InverseParameterPositiveReciprocalPatch.g R) (by
    rw [Order13InverseParameterPositiveReciprocalPatch.positive_infinity_denominator]
    convert h2.mul h2 using 1 <;> norm_num)

theorem positiveInfinityPatchEvaluation_algebraMap (h2 : IsUnit (2 : R)) (c : ReciprocalRing R) :
    positiveInfinityPatchEvaluation R h2 (algebraMap (ReciprocalRing R)
      (Order13InverseParameterPositiveReciprocalPatch.PatchRing R) c) =
      Order13IntegralSections.reciprocalInfinityEvaluation R 1 (by simp) c := by
  simp [positiveInfinityPatchEvaluation,IsLocalization.Away.lift_eq]

def positiveInfinityPatchMorphism (h2 : IsUnit (2 : R)) :
    Spec (.of R) ⟶ Spec (.of (Order13InverseParameterPositiveReciprocalPatch.PatchRing R)) :=
  Spec.map (CommRingCat.ofHom (positiveInfinityPatchEvaluation R h2))

theorem positiveInfinityPatchMorphism_curve (h2 : IsUnit (2 : R)) :
    positiveInfinityPatchMorphism R h2 ≫ positiveReciprocalCurveMap R =
      Order13IntegralSections.infinityMorphism R 1 (by simp) := by
  rw [positiveInfinityPatchMorphism,positiveReciprocalCurveMap,← Category.assoc,← Spec.map_comp]
  unfold Order13IntegralSections.infinityMorphism
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact positiveInfinityPatchEvaluation_algebraMap R h2

theorem positiveInfinityPatchMorphism_base (h2 : IsUnit (2 : R)) :
    positiveInfinityPatchMorphism R h2 ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R (Order13InverseParameterPositiveReciprocalPatch.PatchRing R))) = 𝟙 _ := by
  rw [← positiveReciprocalCurveMap_base,← Category.assoc,positiveInfinityPatchMorphism_curve,
    Order13IntegralSections.infinityMorphism_curveToBase]

end MazurTransfer.Order13InverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13InverseParameterFiniteAlgebra.ordinaryParameterCurveMap_base
#print axioms MazurTransfer.Order13InverseParameterFiniteAlgebra.positiveReciprocalCurveMap_base
#print axioms MazurTransfer.Order13InverseParameterFiniteAlgebra.positiveInfinityPatchMorphism_curve

#print axioms MazurTransfer.Order13InverseParameterFiniteAlgebra.positiveInfinityPatchMorphism_base


