-- Prove2me | Definitions.Def_MazurTransfer_Order13DegreeTwoClosedPoints
-- name    : MazurTransfer_Order13DegreeTwoClosedPoints
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-09T13:02:46.159994+00:00
-- url     : https://prove2.me/theorems/18075e48-14e0-43f6-9564-0e57d492ddc0
-- title:
--   Actual order-13 curve: closed points of geometric residue degree two
-- statement:
--   A degree-two point is a closed point of the literal two-chart curve whose scheme residue field has dimension two over the base field. The scalar structure is induced by the actual curve-to-base morphism through global sections and evaluation. The module also supplies compatible chart and affine-Spec residue-field algebra equivalences. Named downstream consumer: exhaustive degree-two closed-point counts and actual effective degree-two divisors. It assumes no finite-field Picard cardinality or supplied curve model.
-- source:
--   Vas and contributors, MazurTheorem at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion . Literal two-chart curve and unchanged finite-field arithmetic certificates reused with Apache-2.0 headers. Compatible scheme, residue-field, and curve infrastructure uses official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2: https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 . The coordinate-kernel, scalar compatibility, residue-lift and exhaustivity bridges are new checked work.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve

section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: residue-field scalar structures induced by the actual
scheme-to-base morphism, with compatible chart and affine-Spec equivalences.
Named downstream consumer: degree-two closed points of the F3/F5 curve.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace MazurTransfer.StructureResidueFields
universe u
local instance (A : Type u) [CommRing A] (x : Spec (.of A)) : x.asIdeal.IsPrime := x.isPrime

def baseRingMap {R : Type u} [CommRing R] {X : Scheme.{u}}
    (c : X ⟶ Spec (.of R)) (x : X) : CommRingCat.of R ⟶ X.residueField x :=
  (Scheme.ΓSpecIso (.of R)).inv ≫ c.appTop ≫ X.Γevaluation x

abbrev baseAlgebra {R : Type u} [CommRing R] {X : Scheme.{u}}
    (c : X ⟶ Spec (.of R)) (x : X) : Algebra R (X.residueField x) :=
  (baseRingMap c x).hom.toAlgebra

theorem baseRingMap_naturality {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (cX : X ⟶ Spec (.of R)) (cY : Y ⟶ Spec (.of R)) (f : X ⟶ Y)
    (hf : f ≫ cY = cX) (x : X) :
    baseRingMap cY (f x) ≫ f.residueFieldMap x = baseRingMap cX x := by
  simp only [baseRingMap, Category.assoc]
  rw [Scheme.Γevaluation_naturality, ← Scheme.Hom.comp_appTop_assoc, hf]

def residueFieldAlgHom {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (cX : X ⟶ Spec (.of R)) (cY : Y ⟶ Spec (.of R)) (f : X ⟶ Y)
    (hf : f ≫ cY = cX) (x : X) :
    letI := baseAlgebra cY (f x)
    letI := baseAlgebra cX x
    Y.residueField (f x) →ₐ[R] X.residueField x := by
  letI := baseAlgebra cY (f x)
  letI := baseAlgebra cX x
  exact {
    __ := (f.residueFieldMap x).hom
    commutes' r := congrArg (fun g : CommRingCat.of R ⟶ X.residueField x => g.hom r)
      (baseRingMap_naturality cX cY f hf x) }

def openImmersionResidueFieldAlgEquiv {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (cX : X ⟶ Spec (.of R)) (cY : Y ⟶ Spec (.of R)) (f : X ⟶ Y)
    [IsOpenImmersion f] (hf : f ≫ cY = cX) (x : X) :
    letI := baseAlgebra cY (f x)
    letI := baseAlgebra cX x
    Y.residueField (f x) ≃ₐ[R] X.residueField x := by
  letI := baseAlgebra cY (f x)
  letI := baseAlgebra cX x
  exact AlgEquiv.ofRingEquiv (f := (asIso (f.residueFieldMap x)).commRingCatIsoToRingEquiv)
    (residueFieldAlgHom cX cY f hf x).commutes

theorem baseRingMap_spec {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (x : Spec (.of A)) :
    baseRingMap (Spec.map (CommRingCat.ofHom (algebraMap R A))) x =
      CommRingCat.ofHom (algebraMap R x.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso (.of A) x).inv := by
  unfold baseRingMap
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
  change CommRingCat.ofHom (algebraMap R A) ≫ (Scheme.ΓSpecIso (.of A)).inv ≫
    (Spec (.of A)).presheaf.germ ⊤ x trivial ≫ (Spec (.of A)).residue x = _
  rw [← Scheme.Spec.algebraMap_residueFieldIso_inv]
  rw [← Category.assoc]
  congr 1

def idealToSpecResidueFieldAlgEquiv {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (x : Spec (.of A)) :
    letI := baseAlgebra (Spec.map (CommRingCat.ofHom (algebraMap R A))) x
    x.asIdeal.ResidueField ≃ₐ[R] (Spec (.of A)).residueField x := by
  letI := baseAlgebra (Spec.map (CommRingCat.ofHom (algebraMap R A))) x
  refine AlgEquiv.ofRingEquiv (f := (Scheme.Spec.residueFieldIso (.of A) x).symm.commRingCatIsoToRingEquiv) ?_
  intro r
  exact congrArg (fun g : CommRingCat.of R ⟶ (Spec (.of A)).residueField x => g.hom r)
    (baseRingMap_spec (R := R) x).symm

end MazurTransfer.StructureResidueFields
#print axioms MazurTransfer.StructureResidueFields.openImmersionResidueFieldAlgEquiv
#print axioms MazurTransfer.StructureResidueFields.idealToSpecResidueFieldAlgEquiv

end
end

section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: closed points of the literal curve with geometric residue
degree two over its actual base. Named downstream consumer: effective
degree-two divisors and the genuine finite-field Picard cardinality.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MazurTorsion
open MazurTorsion.XOneThirteenProjectiveCurve
namespace MazurTransfer.Order13FiniteCurvePlaces
universe u

def DegreeTwoPoint (R : Type u) [Field R] (x : curveScheme R) : Prop :=
  IsClosed ({x} : Set (curveScheme R)) ∧
    letI := StructureResidueFields.baseAlgebra (curveToBase R) x
    Module.finrank R ((curveScheme R).residueField x) = 2

end MazurTransfer.Order13FiniteCurvePlaces
#print axioms MazurTransfer.Order13FiniteCurvePlaces.DegreeTwoPoint

end
end


