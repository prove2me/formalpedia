-- Prove2me | Definitions.Def_MazurTransfer_Order13FieldCurveLiftGroupData
-- name    : MazurTransfer_Order13FieldCurveLiftGroupData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T18:15:47.513458+00:00
-- url     : https://prove2.me/theorems/f598a470-cf6d-4643-9d6b-888f47aea4d8
-- title:
--   The actual field automorphism lift is an injective monoid homomorphism of curve automorphisms
-- statement:
--   Over every field with 104 nonzero, the original generic-compatible lift preserves identity and multiplication, forms the original monoid homomorphism into automorphisms of the actual curve, and is injective. Four full original types, the liftHom constructor value and both original local/dependency scalar algebra providers are compared. Named downstream consumer: exact generic diamond curve order and geometric inverse pullback.
-- source:
--   Complete original MazurTheorem Order13FieldCurveLiftGroup using the published generic-compatible field lift and original CurveFieldLiftGroupCriterion. Official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual function-field automorphism lift is an injective
monoid homomorphism into automorphisms of the literal curve over Q.
Named downstream consumer: exact diamond scheme order, generic section-map
compatibility, and arithmetic naturality of the Picard action.
-/
import Definitions.Def_MazurTransfer_Order13FieldCurveAutomorphismLiftData
import Definitions.Def_MazurTransfer_CurveFieldLiftGroupCriterion

noncomputable section
universe u
namespace MazurTransfer.Order13FieldCurveLiftGroup
open CategoryTheory AlgebraicGeometry
open Order13FieldCurveAutomorphismLift
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
variable (K : Type u) [Field K] [Fact ((104 : K) ≠ 0)]
local notation "C" => curveScheme K
local notation "F" => actualCurveFunctionField K
local instance : Algebra K F := actualCurveFunctionFieldAlgebra K

theorem fieldLift_one : (fieldLift K) (1 : F ≃ₐ[K] F) = 1 :=
  CurveFieldLiftGroupCriterion.lift_one (curveToBase K) (genericEmbedding K) (fieldLift K)
    (fieldLift_over K) (fieldLift_generic K) (fun _ _ hf hg h => (hom_ext K) hf hg h)

theorem fieldLift_mul (σ τ : F ≃ₐ[K] F) : (fieldLift K) (σ * τ) = (fieldLift K) σ * (fieldLift K) τ :=
  CurveFieldLiftGroupCriterion.lift_mul (curveToBase K) (genericEmbedding K) (fieldLift K)
    (fieldLift_over K) (fieldLift_generic K) (fun _ _ hf hg h => (hom_ext K) hf hg h) σ τ

def fieldLiftHom : (F ≃ₐ[K] F) →* Aut C :=
  CurveFieldLiftGroupCriterion.liftHom (curveToBase K) (genericEmbedding K) (fieldLift K)
    (fieldLift_over K) (fieldLift_generic K) (fun _ _ hf hg h => (hom_ext K) hf hg h)

theorem fieldLift_injective : Function.Injective (fieldLift K) := by
  haveI : Mono (genericEmbedding K) := by
    change Mono ((curveScheme K).fromSpecStalk (genericPoint C))
    infer_instance
  exact CurveFieldLiftGroupCriterion.lift_injective (genericEmbedding K) (fieldLift K) (fieldLift_generic K)

end MazurTransfer.Order13FieldCurveLiftGroup
#print axioms MazurTransfer.Order13FieldCurveLiftGroup.fieldLiftHom
#print axioms MazurTransfer.Order13FieldCurveLiftGroup.fieldLift_injective


