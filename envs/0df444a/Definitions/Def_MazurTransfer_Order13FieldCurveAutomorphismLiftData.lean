-- Prove2me | Definitions.Def_MazurTransfer_Order13FieldCurveAutomorphismLiftData
-- name    : MazurTransfer_Order13FieldCurveAutomorphismLiftData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T18:09:19.911741+00:00
-- url     : https://prove2.me/theorems/bd5cc68a-38fb-4420-bb7e-fd976bb491f9
-- title:
--   Base-field automorphisms of the actual function field lift to the literal curve
-- statement:
--   Over any field with 104 nonzero, each base-field algebra automorphism of the actual curve function field has the original chosen curve lift, with its over-base identity, generic-stalk action and closed-point-place action; generic equality detects equality of over-base curve morphisms. The original generic closed-point-image constructor and place-action helper are included. Nine original types, three constructors and the original local scalar algebra provider are compared. Named downstream consumer: the lift group and geometric diamond base-change compatibility.
-- source:
--   Complete original MazurTheorem Order13FieldCurveAutomorphismLift, CurveClosedPointImage and FieldAutomorphismPlaceCongruence helper. Uses the accepted fixed-model isomorphism theorem and actual CurveModel definition. Official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses the complete checked fixed-model isomorphism construction of Anthropic
FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: every base-field algebra automorphism of the actual function field
lifts to the literal curve over every field with 104 nonzero, with specified generic-stalk and place actions.
Named downstream consumer: arithmetic naturality of inverse-curve pullback
on divisor presentations, and exact diamond order on the curve scheme.
-/
import Theorems.Thm_MazurTransfer_CurveModelIsoWithGenericCompatibility_exists_iso_with_generic_comp_and_place_congr
import Definitions.Def_MazurTransfer_Order13ActualCurveModel
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_eq_of_fromSpecStalk_genericPoint_comp_eq

noncomputable section
universe u
namespace MazurTransfer.CurveClosedPointImage
open CategoryTheory AlgebraicGeometry

def closedPointImage {C : Scheme.{u}} (e : C ≅ C) (x : closedPoints C) : closedPoints C :=
  ⟨e.hom.base x.1, by
    show IsClosed ({e.hom.base x.1} : Set C)
    rw [← Set.image_singleton]
    exact (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).isClosedMap _ x.2⟩

end MazurTransfer.CurveClosedPointImage
end
noncomputable section
universe u v
namespace MazurTransfer.FieldCurveLiftPublicPlaceHelpers20261017
open AlgebraicCurve
open scoped Pointwise
variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

theorem congrRingEquiv_eq_smul (σ : F ≃ₐ[K] F) (p : Place K F) :
    Place.congrRingEquiv σ.toRingEquiv σ.commutes p = σ • p := by
  apply Place.ext
  ext x
  change σ.symm x ∈ p.toValuationSubring ↔ x ∈ σ • p.toValuationSubring
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

end MazurTransfer.FieldCurveLiftPublicPlaceHelpers20261017
end
noncomputable section
universe u
namespace MazurTransfer.Order13FieldCurveAutomorphismLift
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualArithmeticCurveModel
open CurveClosedPointImage
variable (K : Type u) [Field K] [Fact ((104 : K) ≠ 0)]
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K

local notation "C" => curveScheme K
local notation "F" => actualCurveFunctionField K

def genericEmbedding : Spec (CommRingCat.of F) ⟶ C := (curveScheme K).fromSpecStalk (genericPoint C)

theorem exists_fieldLift (σ : F ≃ₐ[K] F) :
    ∃ e : C ≅ C, e.hom ≫ curveToBase K = curveToBase K ∧
      ((genericEmbedding K) ≫ e.hom =
        Spec.map (CommRingCat.ofHom σ.symm.toRingHom) ≫ (genericEmbedding K)) ∧
      ∀ x : closedPoints C,
        actualPlaceOfPoint K (CurveClosedPointImage.closedPointImage e x) =
          σ • actualPlaceOfPoint K x := by
  obtain ⟨e, he, hgen, hp⟩ :=
    MazurTransfer.CurveModelIsoWithGenericCompatibility.exists_iso_with_generic_comp_and_place_congr
      σ (actualCurveModel K) (actualCurveModel K)
  refine ⟨e, he, hgen, fun x => ?_⟩
  exact (hp x).trans (FieldCurveLiftPublicPlaceHelpers20261017.congrRingEquiv_eq_smul σ _)

def fieldLift (σ : F ≃ₐ[K] F) : Aut C := ((exists_fieldLift K) σ).choose

theorem fieldLift_over (σ : F ≃ₐ[K] F) :
    ((fieldLift K) σ).hom ≫ curveToBase K = curveToBase K := ((exists_fieldLift K) σ).choose_spec.1

theorem fieldLift_generic (σ : F ≃ₐ[K] F) :
    (genericEmbedding K) ≫ ((fieldLift K) σ).hom =
      Spec.map (CommRingCat.ofHom σ.symm.toRingHom) ≫ (genericEmbedding K) :=
  ((exists_fieldLift K) σ).choose_spec.2.1

theorem fieldLift_place (σ : F ≃ₐ[K] F) (x : closedPoints C) :
    actualPlaceOfPoint K (CurveClosedPointImage.closedPointImage ((fieldLift K) σ) x) =
      σ • actualPlaceOfPoint K x := ((exists_fieldLift K) σ).choose_spec.2.2 x

theorem hom_ext {f g : C ⟶ C} (hf : f ≫ curveToBase K = curveToBase K)
    (hg : g ≫ curveToBase K = curveToBase K)
    (hgen : (genericEmbedding K) ≫ f = (genericEmbedding K) ≫ g) : f = g :=
  Scheme.Hom.eq_of_fromSpecStalk_genericPoint_comp_eq
    (curveToBase K) (curveToBase K) f g hf hg hgen

end MazurTransfer.Order13FieldCurveAutomorphismLift
#print axioms MazurTransfer.Order13FieldCurveAutomorphismLift.exists_fieldLift
#print axioms MazurTransfer.Order13FieldCurveAutomorphismLift.fieldLift_generic
#print axioms MazurTransfer.Order13FieldCurveAutomorphismLift.hom_ext


