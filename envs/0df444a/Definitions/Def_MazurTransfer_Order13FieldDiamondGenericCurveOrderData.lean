-- Prove2me | Definitions.Def_MazurTransfer_Order13FieldDiamondGenericCurveOrderData
-- name    : MazurTransfer_Order13FieldDiamondGenericCurveOrderData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T18:19:53.651228+00:00
-- url     : https://prove2.me/theorems/b390b078-aa68-40af-bcce-82e7bd18455c
-- title:
--   The generic-compatible diamond curve lift has exact order six over characteristic-zero fields
-- statement:
--   The original chosen diamond curve isomorphism over every characteristic-zero field has exact order six and sixth power one; the chosen lift respects inversion and has the original inverse generic-stalk identity. Five full original types, the chosen-isomorphism constructor value and four original scalar algebra providers are compared. Named downstream consumer: geometric inverse-diamond base-change naturality and Picard pullback.
-- source:
--   Complete original MazurTheorem Order13FieldDiamondGenericCurveOrder using the published original lift monoid homomorphism and actual diamond function-field exact order. Official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: exact order of the generic-compatible diamond lift on the
literal curve over every characteristic-zero field. Named downstream consumer: compatible Picard pullback
and transport of divisor presentations along its inverse.
-/
import Definitions.Def_MazurTransfer_Order13FieldCurveLiftGroupData
import Definitions.Def_MazurTransfer_Order13FieldDiamondExactOrderData

noncomputable section
universe u
namespace MazurTransfer.Order13FieldDiamondGenericCurveOrder
open CategoryTheory AlgebraicGeometry
open Order13FieldCurveAutomorphismLift Order13FieldCurveLiftGroup
open Order13FieldDiamondFunctionFieldAutomorphism Order13FieldDiamondExactOrder
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
variable (K : Type u) [Field K] [CharZero K]
local notation "C" => MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K
local notation "F" => actualCurveFunctionField K
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K F := actualCurveFunctionFieldAlgebra K

def genericDiamondCurveIso : Aut C := (fieldLift K) (diamondAlgEquiv K)

theorem genericDiamondCurveIso_order : orderOf (genericDiamondCurveIso K) = 6 := by
  calc
    orderOf (genericDiamondCurveIso K) = orderOf (diamondAlgEquiv K) :=
      orderOf_injective (fieldLiftHom K) (fieldLift_injective K) (diamondAlgEquiv K)
    _ = 6 := (diamondAlgEquiv_order K)

theorem genericDiamondCurveIso_pow_six : (genericDiamondCurveIso K) ^ 6 = 1 := by
  have h := congrArg (fieldLiftHom K) (diamondAlgEquiv_pow_six K)
  rw [map_pow, map_one] at h
  exact h

theorem fieldLift_inv (σ : F ≃ₐ[K] F) : (fieldLift K) σ⁻¹ = ((fieldLift K) σ)⁻¹ :=
  map_inv (fieldLiftHom K) σ

theorem fieldLift_inv_generic (σ : F ≃ₐ[K] F) :
    (genericEmbedding K) ≫ ((fieldLift K) σ).inv =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (genericEmbedding K) := by
  have h := (fieldLift_generic K) σ⁻¹
  rw [(fieldLift_inv K)] at h
  exact h

end MazurTransfer.Order13FieldDiamondGenericCurveOrder
#print axioms MazurTransfer.Order13FieldDiamondGenericCurveOrder.genericDiamondCurveIso_order
#print axioms MazurTransfer.Order13FieldDiamondGenericCurveOrder.fieldLift_inv_generic


