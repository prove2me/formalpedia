-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualArithmeticNineteenTorsionGaloisHomOriginalData20261018
-- name    : MazurTransfer_Order13ActualArithmeticNineteenTorsionGaloisHomOriginalData20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T14:37:57.398346+00:00
-- url     : https://prove2.me/theorems/56c8b84d-38ba-4eed-ac3b-7b4f86707c7e
-- title:
--   Original arithmetic Galois additive homomorphism on actual nineteen torsion
-- statement:
--   The exact original additive restriction of the Picard precomposition Galois action to its nineteen-torsion subgroup, with its complete telescope and constructor value checked. It supplies the named downstream theorem geometricNineteenTorsionDivisorAddEquiv_galois and actual arithmetic pairing covariance. It asserts no additional divisor-class naturality or arithmetic bound.
-- source:
--   MazurTheorem Order13ActualNineteenTorsionGaloisPairingBridge.arithmeticNineteenTorsionHom, exact original constructor; official Anthropic FLT interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original additive restriction of the existing Picard
precomposition Galois action to nineteen torsion. Named downstream consumer:
Galois naturality of the natural nineteen-torsion divisor comparison.
Original MazurTheorem constructor, using the official Anthropic FLT
interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardNormKernelGaloisActionData
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionNormRestrictionOriginalData20261018
noncomputable section
namespace MazurTransfer.Order13ActualNineteenTorsionGaloisPairingBridge
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open GoodReductionJacobian NeronModelInfra
open Order13ActualPicardGeometricNormPreimages Order13ActualNormKernelProductCardinality
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
attribute [local instance] actualNineteenTorsionProductOriginalGroupProvider20261018 actualNineteenTorsionProductOriginalCommProvider20261018
variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]

def arithmeticNineteenTorsionHom (σ : K ≃ₐ[ℚ] K) : NineteenTorsion K →+ NineteenTorsion K where
  toFun x := ⟨(actionHom K σ).toAdditive x.val, by
    change (19 : ℕ) • (actionHom K σ).toAdditive x.val = 0
    have hx : (19 : ℕ) • x.val = 0 := x.property
    rw [← map_nsmul, hx, map_zero]⟩
  map_zero' := Subtype.ext (map_zero (actionHom K σ).toAdditive)
  map_add' x y := Subtype.ext (map_add (actionHom K σ).toAdditive x.val y.val)

end MazurTransfer.Order13ActualNineteenTorsionGaloisPairingBridge
#print axioms MazurTransfer.Order13ActualNineteenTorsionGaloisPairingBridge.arithmeticNineteenTorsionHom


