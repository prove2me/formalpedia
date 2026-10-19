-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualDiamondGenericCurveOrder
-- name    : MazurTransfer_Order13ActualDiamondGenericCurveOrder
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T12:05:33.185988+00:00
-- url     : https://prove2.me/theorems/a0301bde-8bb4-4ee5-9a5d-a16e7763c53a
-- title:
--   Exact order and inverse compatibility of the actual generic diamond curve lift
-- statement:
--   The generic-compatible lift of the actual rational diamond field automorphism is a curve automorphism of exact order six. The original field lift respects inverses and its inverse has the specified generic-stalk composition: $$\operatorname{ord}(L(\sigma))=6,\qquad L(\tau^{-1})=L(\tau)^{-1}.$$ These actual curve identities supply inverse-pullback naturality on divisor presentations and the represented Picard action.
-- source:
--   Original complete five declarations from MazurTheorem Order13ActualDiamondGenericCurveOrder.lean with the short original sixth-power identity inlined unchanged, Apache-2.0, Vas and contributors. Six complete original closed types and one data value are kernel-compared. Missing generated original local-instance names are normalized only from retained checked values. Imports alone are replaced and every original body is retained. Named downstream consumer: actual arithmetic Picard inverse-pullback naturality.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: exact order of the generic-compatible diamond lift on the
literal curve over Q. Named downstream consumer: compatible Picard pullback
and transport of divisor presentations along its inverse.
-/
import Definitions.Def_MazurTransfer_Order13ActualCurveFieldLiftGroup
import Theorems.Thm_MazurTransfer_Order13ActualDiamondExactOrder_diamondAlgEquiv_order

noncomputable section
namespace MazurTransfer.Order13ActualDiamondExactOrder
open MazurTransfer.Order13ActualDiamondFunctionFieldAutomorphism
theorem diamondAlgEquiv_pow_six : diamondAlgEquiv ^ 6 = 1 := by
  apply AlgEquiv.ext
  intro b
  exact RingHom.congr_fun diamondThird_square b

end MazurTransfer.Order13ActualDiamondExactOrder

noncomputable section
namespace MazurTransfer.Order13ActualDiamondGenericCurveOrder
open CategoryTheory AlgebraicGeometry
open Order13ActualCurveFieldAutomorphismLift Order13ActualCurveFieldLiftGroup
open Order13ActualDiamondFunctionFieldAutomorphism Order13ActualDiamondExactOrder
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra ℚ F := actualCurveFunctionFieldAlgebra ℚ

def genericDiamondCurveIso : Aut C := fieldLift diamondAlgEquiv

theorem genericDiamondCurveIso_order : orderOf genericDiamondCurveIso = 6 := by
  calc
    orderOf genericDiamondCurveIso = orderOf diamondAlgEquiv :=
      orderOf_injective fieldLiftHom fieldLift_injective diamondAlgEquiv
    _ = 6 := diamondAlgEquiv_order

theorem genericDiamondCurveIso_pow_six : genericDiamondCurveIso ^ 6 = 1 := by
  have h := congrArg fieldLiftHom diamondAlgEquiv_pow_six
  rw [map_pow, map_one] at h
  exact h

theorem fieldLift_inv (σ : F ≃ₐ[ℚ] F) : fieldLift σ⁻¹ = (fieldLift σ)⁻¹ :=
  map_inv fieldLiftHom σ

theorem fieldLift_inv_generic (σ : F ≃ₐ[ℚ] F) :
    genericEmbedding ≫ (fieldLift σ).inv =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ genericEmbedding := by
  have h := fieldLift_generic σ⁻¹
  rw [fieldLift_inv] at h
  exact h

end MazurTransfer.Order13ActualDiamondGenericCurveOrder
#print axioms MazurTransfer.Order13ActualDiamondGenericCurveOrder.genericDiamondCurveIso_order
#print axioms MazurTransfer.Order13ActualDiamondGenericCurveOrder.fieldLift_inv_generic


