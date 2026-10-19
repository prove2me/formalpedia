-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualCurveFieldLiftGroup
-- name    : MazurTransfer_Order13ActualCurveFieldLiftGroup
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T11:55:26.281227+00:00
-- url     : https://prove2.me/theorems/569a4c7b-05c9-4e0a-8329-9404e9bc506b
-- title:
--   The actual generic-compatible field lift is an injective monoid homomorphism
-- statement:
--   The specified generic-compatible lifts from automorphisms of the actual rational function field to automorphisms of the literal curve form an injective monoid homomorphism: $$L(1)=1,\qquad L(\sigma\tau)=L(\sigma)L(\tau).$$ This original group structure supplies inverse generic-compatibility and the genuine Picard action.
-- source:
--   Original complete declarations and bodies from MazurTheorem Order13ActualCurveFieldLiftGroup.lean, Apache-2.0, Vas and contributors. 4 complete original closed types and 1 data values are kernel-compared. Public imports alone replace dependencies. The original generic criterion is reused byte-for-byte without native rebuilding. Named downstream consumer: actual generic-compatible Picard action and arithmetic pullback naturality.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual function-field automorphism lift is an injective
monoid homomorphism into automorphisms of the literal curve over Q.
Named downstream consumer: exact diamond scheme order, generic section-map
compatibility, and arithmetic naturality of the Picard action.
-/
import Definitions.Def_MazurTransfer_Order13ActualCurveFieldAutomorphismLift
import Definitions.Def_MazurTransfer_CurveFieldLiftGroupCriterion

noncomputable section
namespace MazurTransfer.Order13ActualCurveFieldLiftGroup
open CategoryTheory AlgebraicGeometry
open Order13ActualCurveFieldAutomorphismLift
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra ℚ F := actualCurveFunctionFieldAlgebra ℚ

theorem fieldLift_one : fieldLift (1 : F ≃ₐ[ℚ] F) = 1 :=
  CurveFieldLiftGroupCriterion.lift_one (curveToBase ℚ) genericEmbedding fieldLift
    fieldLift_over fieldLift_generic (fun _ _ hf hg h => hom_ext hf hg h)

theorem fieldLift_mul (σ τ : F ≃ₐ[ℚ] F) : fieldLift (σ * τ) = fieldLift σ * fieldLift τ :=
  CurveFieldLiftGroupCriterion.lift_mul (curveToBase ℚ) genericEmbedding fieldLift
    fieldLift_over fieldLift_generic (fun _ _ hf hg h => hom_ext hf hg h) σ τ

def fieldLiftHom : (F ≃ₐ[ℚ] F) →* Aut C :=
  CurveFieldLiftGroupCriterion.liftHom (curveToBase ℚ) genericEmbedding fieldLift
    fieldLift_over fieldLift_generic (fun _ _ hf hg h => hom_ext hf hg h)

theorem fieldLift_injective : Function.Injective fieldLift := by
  haveI : Mono genericEmbedding := by
    change Mono (C.fromSpecStalk (genericPoint C))
    infer_instance
  exact CurveFieldLiftGroupCriterion.lift_injective genericEmbedding fieldLift fieldLift_generic

end MazurTransfer.Order13ActualCurveFieldLiftGroup
#print axioms MazurTransfer.Order13ActualCurveFieldLiftGroup.fieldLiftHom
#print axioms MazurTransfer.Order13ActualCurveFieldLiftGroup.fieldLift_injective


