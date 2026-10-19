-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicCharacterIntertwiningOriginalData20261018
-- name    : MazurTransfer_Order13ActualNormKernelCyclotomicCharacterIntertwiningOriginalData20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T15:50:42.621441+00:00
-- url     : https://prove2.me/theorems/d4caed09-6d1d-48d4-8dd2-e9857f3471c5
-- title:
--   Original actual norm-kernel cyclotomic character intertwining map
-- statement:
--   The original concrete intertwining map from the other actual norm kernel to literal nineteen-th roots, supplied with an original Galois-fixed vector in the first kernel. Its complete original type and nonproof constructor value are checked, together with forty-one complete original group/action/module/scalar provider types and nineteen values. The named downstream consumer is the actual cyclotomic quotient construction using linear character surjectivity. This interface does not assert a nonzero fixed vector or surjectivity without those original inputs.
-- source:
--   MazurTheorem Order13ActualNormKernelCyclotomicCharacter.kernelCharacterIntertwining, exact original constructor; official Anthropic FLT interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original concrete intertwining map from the other
actual norm kernel to literal nineteen roots, supplied with an original
fixed vector in the first kernel. Its complete original type and constructor
value are checked. Named downstream consumer: actual cyclotomic quotient
maps using kernelCharacterLinear_surjective_of_cross.
Original MazurTheorem constructor; official Anthropic FLT interfaces at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicCharacterOriginalData20261018
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelCyclotomicCharacter_kernelCharacter_galois
noncomputable section
namespace MazurTransfer.Order13ActualNormKernelCyclotomicCharacter
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelF19Representation NineteenRootsGaloisRepresentation
open scoped CategoryTheory.MonObj
attribute [local instance] kernelCharacterOriginalGroupProvider20261018 kernelCharacterOriginalCommProvider20261018 kernelCharacterOriginalPiHomProvider20261018 kernelCharacterOriginalConjugateHomProvider20261018 kernelCharacterOriginalPrimeProvider20261018 kernelCharacterOriginalLeftModuleProvider20261018 kernelCharacterOriginalRightModuleProvider20261018 kernelCharacterOriginalRootsModuleProvider20261018
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
variable (φ ψ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
  [IsMonHom φ] [IsMonHom ψ] [IsFinite φ.left] [IsFinite ψ.left]
  [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] [Fact (∀ z : Kernel K ψ, z ^ 19 = 1)]

def kernelCharacterIntertwining (a : Additive (Kernel K φ))
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K φ σ a = a) :
    Representation.IntertwiningMap (kernelRepresentation K ψ) (rootsRepresentation K) :=
  (kernelCharacterLinear K φ ψ a).intertwiningMap_of_isIntertwiningMap _ _
    (kernelCharacter_galois K φ ψ a ha)

end MazurTransfer.Order13ActualNormKernelCyclotomicCharacter
#print axioms MazurTransfer.Order13ActualNormKernelCyclotomicCharacter.kernelCharacterIntertwining


