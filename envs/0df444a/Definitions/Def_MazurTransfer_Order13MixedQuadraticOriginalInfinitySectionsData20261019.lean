-- Prove2me | Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalInfinitySectionsData20261019
-- name    : MazurTransfer_Order13MixedQuadraticOriginalInfinitySectionsData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T04:38:46.580449+00:00
-- url     : https://prove2.me/theorems/dc0f9c16-3b9b-4257-bdac-95ace619406e
-- title:
--   Both original infinity sections of the actual mixed quadratic curve
-- statement:
--   The two original reciprocal chart points with coordinates (0,0) and (0,-1), their whole glued-curve section morphisms, and both section identities over every commutative base ring. Nine public declaration types, four whole nonproof values and the private Spec section helper type are checked. Named downstream consumer: rigidification of the actual dyadic integral Picard family.
-- source:
--   MazurTheorem Order13MixedQuadraticInfinitySections; Vas and contributors; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: two actual coefficient-ring sections of the mixed
quadratic glued curve, with reciprocal coordinates (0,0) and (0,-1).
Named downstream consumer: rigidification of its integral Picard family.
Their comparison with the existing rational infinity sections is separate.
-/
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalGluedCurveData20261019

noncomputable section
namespace MazurTransfer.Order13MixedQuadraticInfinitySections
open Polynomial CategoryTheory AlgebraicGeometry
open MixedQuadraticCoordinateJacobian Order13MixedQuadraticJacobianCertificates
open Order13MixedQuadraticPolynomialEvaluations Order13DyadicMixedQuadraticCharts
open Order13MixedQuadraticGluedCurve
universe u
variable (R : Type u) [CommRing R]

def infinityPointZero : reciprocalCoordinateRing R →ₐ[R] R :=
  AdjoinRoot.liftAlgHom (equation R (reciprocalH R) (reciprocalF R)) (aeval (0 : R)) 0 (by
    change eval₂ (aeval (0 : R)).toRingHom 0
      (X ^ 2 + C (reciprocalH R) * X - C (reciprocalF R)) = 0
    simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
    rw [map_reciprocalH R _, map_reciprocalF R _]
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X]
    ring)

def infinityPointNegOne : reciprocalCoordinateRing R →ₐ[R] R :=
  AdjoinRoot.liftAlgHom (equation R (reciprocalH R) (reciprocalF R)) (aeval (0 : R)) (-1) (by
    change eval₂ (aeval (0 : R)).toRingHom (-1)
      (X ^ 2 + C (reciprocalH R) * X - C (reciprocalF R)) = 0
    simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
    rw [map_reciprocalH R _, map_reciprocalF R _]
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X]
    ring)

private theorem spec_algHom_section (A : Type u) [CommRing A] [Algebra R A] (φ : A →ₐ[R] R) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A)) = 𝟙 (Spec (.of R)) := by
  have hh : CommRingCat.ofHom (algebraMap R A) ≫ CommRingCat.ofHom φ.toRingHom =
      𝟙 (CommRingCat.of R) := by
    apply CommRingCat.hom_ext
    ext r
    exact φ.commutes r
  rw [← Spec.map_comp, hh, Spec.map_id]

def infinitySectionZero : Spec (.of R) ⟶ curveScheme R :=
  Spec.map (CommRingCat.ofHom (infinityPointZero R).toRingHom) ≫ reciprocalChartMap R

def infinitySectionNegOne : Spec (.of R) ⟶ curveScheme R :=
  Spec.map (CommRingCat.ofHom (infinityPointNegOne R).toRingHom) ≫ reciprocalChartMap R

theorem infinitySectionZero_comp : infinitySectionZero R ≫ curveToBase R = 𝟙 (Spec (.of R)) := by
  let t : Spec (.of R) ⟶ reciprocalScheme R := Spec.map (CommRingCat.ofHom (infinityPointZero R).toRingHom)
  have ht : t ≫ reciprocalToBase R = 𝟙 (Spec (.of R)) :=
    spec_algHom_section R (reciprocalCoordinateRing R) (infinityPointZero R)
  have he : t ≫ (reciprocalChartMap R ≫ curveToBase R) = t ≫ reciprocalToBase R :=
    congrArg (fun g : reciprocalScheme R ⟶ Spec (.of R) => t ≫ g) (reciprocalChartMap_curveToBase R)
  change (t ≫ reciprocalChartMap R) ≫ curveToBase R = 𝟙 (Spec (.of R))
  exact (Category.assoc t (reciprocalChartMap R) (curveToBase R)).trans (he.trans ht)


theorem infinitySectionNegOne_comp : infinitySectionNegOne R ≫ curveToBase R = 𝟙 (Spec (.of R)) := by
  let t : Spec (.of R) ⟶ reciprocalScheme R := Spec.map (CommRingCat.ofHom (infinityPointNegOne R).toRingHom)
  have ht : t ≫ reciprocalToBase R = 𝟙 (Spec (.of R)) :=
    spec_algHom_section R (reciprocalCoordinateRing R) (infinityPointNegOne R)
  have he : t ≫ (reciprocalChartMap R ≫ curveToBase R) = t ≫ reciprocalToBase R :=
    congrArg (fun g : reciprocalScheme R ⟶ Spec (.of R) => t ≫ g) (reciprocalChartMap_curveToBase R)
  change (t ≫ reciprocalChartMap R) ≫ curveToBase R = 𝟙 (Spec (.of R))
  exact (Category.assoc t (reciprocalChartMap R) (curveToBase R)).trans (he.trans ht)


end MazurTransfer.Order13MixedQuadraticInfinitySections
#print axioms MazurTransfer.Order13MixedQuadraticInfinitySections.infinitySectionZero_comp
#print axioms MazurTransfer.Order13MixedQuadraticInfinitySections.infinitySectionNegOne_comp


