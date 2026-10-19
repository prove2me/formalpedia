-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualCurveFieldAutomorphismLift
-- name    : MazurTransfer_Order13ActualCurveFieldAutomorphismLift
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T11:50:50.79825+00:00
-- url     : https://prove2.me/theorems/903b928e-65f0-4fed-9dcf-5c19edf3b2db
-- title:
--   Generic-compatible lifts of every actual rational field automorphism
-- statement:
--   Every $\mathbb Q$-algebra automorphism of the actual order-thirteen function field lifts to an automorphism of the literal curve over $\mathbb Q$, with the specified action on its generic stalk and every closed-point place. These are the original choices and compatibility certificates, including equality of curve morphisms detected on the generic stalk. They supply arithmetic naturality of Picard pullback.
-- source:
--   Original complete declarations and bodies from MazurTheorem Order13ActualCurveFieldAutomorphismLift.lean, Apache-2.0, Vas and contributors. 9 complete original closed types and 4 data values are kernel-compared. Public imports alone replace dependencies. The original generic criterion is reused byte-for-byte without native rebuilding. Named downstream consumer: actual generic-compatible Picard action and arithmetic pullback naturality.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses the complete checked fixed-model isomorphism construction of Anthropic
FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: every Q-algebra automorphism of the actual function field
lifts to the literal curve with specified generic-stalk and place actions.
Named downstream consumer: arithmetic naturality of inverse-curve pullback
on divisor presentations, and exact diamond order on the curve scheme.
-/
import Theorems.Thm_MazurTransfer_CurveModelIsoWithGenericCompatibility_exists_iso_with_generic_comp_and_place_congr
import Definitions.Def_MazurTransfer_Order13ActualCurveModel
import Definitions.Def_MazurTransfer_Order13ActualDiamondCurveAutomorphism
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_eq_of_fromSpecStalk_genericPoint_comp_eq

noncomputable section
namespace MazurTransfer.Order13ActualCurveFieldAutomorphismLift
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualArithmeticCurveModel
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ

abbrev C := curveScheme ℚ
abbrev F := actualCurveFunctionField ℚ

def genericEmbedding : Spec (CommRingCat.of F) ⟶ C := C.fromSpecStalk (genericPoint C)

theorem exists_fieldLift (σ : F ≃ₐ[ℚ] F) :
    ∃ e : C ≅ C, e.hom ≫ curveToBase ℚ = curveToBase ℚ ∧
      (genericEmbedding ≫ e.hom =
        Spec.map (CommRingCat.ofHom σ.symm.toRingHom) ≫ genericEmbedding) ∧
      ∀ x : closedPoints C,
        actualPlaceOfPoint ℚ (Order13ActualDiamondCurveAutomorphism.closedPointImage e x) =
          σ • actualPlaceOfPoint ℚ x := by
  obtain ⟨e, he, hgen, hp⟩ :=
    CurveModelIsoWithGenericCompatibility.exists_iso_with_generic_comp_and_place_congr
      σ (actualCurveModel ℚ) (actualCurveModel ℚ)
  refine ⟨e, he, hgen, fun x => ?_⟩
  exact (hp x).trans (FieldAutomorphismPlaceCongruence.congrRingEquiv_eq_smul σ _)

def fieldLift (σ : F ≃ₐ[ℚ] F) : Aut C := (exists_fieldLift σ).choose

theorem fieldLift_over (σ : F ≃ₐ[ℚ] F) :
    (fieldLift σ).hom ≫ curveToBase ℚ = curveToBase ℚ := (exists_fieldLift σ).choose_spec.1

theorem fieldLift_generic (σ : F ≃ₐ[ℚ] F) :
    genericEmbedding ≫ (fieldLift σ).hom =
      Spec.map (CommRingCat.ofHom σ.symm.toRingHom) ≫ genericEmbedding :=
  (exists_fieldLift σ).choose_spec.2.1

theorem fieldLift_place (σ : F ≃ₐ[ℚ] F) (x : closedPoints C) :
    actualPlaceOfPoint ℚ (Order13ActualDiamondCurveAutomorphism.closedPointImage (fieldLift σ) x) =
      σ • actualPlaceOfPoint ℚ x := (exists_fieldLift σ).choose_spec.2.2 x

theorem hom_ext {f g : C ⟶ C} (hf : f ≫ curveToBase ℚ = curveToBase ℚ)
    (hg : g ≫ curveToBase ℚ = curveToBase ℚ)
    (hgen : genericEmbedding ≫ f = genericEmbedding ≫ g) : f = g :=
  Scheme.Hom.eq_of_fromSpecStalk_genericPoint_comp_eq
    (curveToBase ℚ) (curveToBase ℚ) f g hf hg hgen

end MazurTransfer.Order13ActualCurveFieldAutomorphismLift
#print axioms MazurTransfer.Order13ActualCurveFieldAutomorphismLift.exists_fieldLift
#print axioms MazurTransfer.Order13ActualCurveFieldAutomorphismLift.fieldLift_generic
#print axioms MazurTransfer.Order13ActualCurveFieldAutomorphismLift.hom_ext


