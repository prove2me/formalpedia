-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualNormKernelBilinearPairingOriginalDataAndActionCertificateExplicitKernelNamespaceV220261018
-- name    : MazurTransfer_Order13ActualNormKernelBilinearPairingOriginalDataAndActionCertificateExplicitKernelNamespaceV220261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T00:15:56.95559+00:00
-- url     : https://prove2.me/theorems/c70a4520-d0b2-47a8-a73d-c1dee5876a09
-- title:
--   Original bilinear pairing on complete actual norm kernels
-- statement:
--   The original additive and F19-bilinear pairing constructors and their literal action certificate on the same complete norm kernels. Three declaration types, two whole values, and two necessary pairing-law helper types referenced from the published original character data are checked with their complete original contexts. Named downstream consumer: Galois covariance of this same pairing and the quotient paired against a character eigenvector. No character-action hypothesis is added.
-- source:
--   MazurTheorem original declarations and immediately necessary constructor certificates; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the SAME actual geometric nineteen-pairing on COMPLETE
norm kernels is F19-bilinear and covariant for their EXISTING arithmetic
Galois representations. Named downstream consumer: the complementary
character quotient and its actual intertwiner.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicCharacterOriginalData20261018
noncomputable section
namespace MazurTransfer.Order13ActualNormKernelPairingBilinear
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
open Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelCyclotomicCharacter Order13ActualNormKernelFiniteModule
open Order13ActualNormKernelNineteenEmbedding Order13ActualNormKernelF19Representation
open NineteenRootsGaloisRepresentation Order13ActualNineteenTorsionNormPairingAdjoint
open Order13ActualGeometricNineteenDivisorialPairing
attribute [local instance] kernelCharacterOriginalGroupProvider20261018 kernelCharacterOriginalCommProvider20261018 kernelCharacterOriginalPiHomProvider20261018 kernelCharacterOriginalConjugateHomProvider20261018 kernelCharacterOriginalPrimeProvider20261018 kernelCharacterOriginalLeftModuleProvider20261018 kernelCharacterOriginalRightModuleProvider20261018 kernelCharacterOriginalRootsModuleProvider20261018
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
variable (φ ψ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
  [IsMonHom φ] [IsMonHom ψ] [IsFinite φ.left] [IsFinite ψ.left]
  [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] [Fact (∀ z : Kernel K ψ, z ^ 19 = 1)]
def kernelPairingAddHom : Additive (Kernel K φ) →+
    (Additive (Kernel K ψ) →ₗ[ZMod 19] Additive (Roots K)) where
  toFun := kernelCharacterLinear K φ ψ
  map_zero' := by
    apply LinearMap.ext
    intro z
    apply Additive.toMul.injective
    apply Subtype.ext
    change actualGeometricNineteenPairing K (kernelNineteenAddHom K φ 0)
      (kernelNineteenAddHom K ψ z) = 1
    rw [map_zero]
    exact MazurTransfer.KernelCyclotomicCharacterOriginalProofHelpers20261018.pairingUnits_zero_left K (actualDivisorialNineteenPairingData K) _
  map_add' a b := by
    apply LinearMap.ext
    intro z
    apply Additive.toMul.injective
    apply Subtype.ext
    change actualGeometricNineteenPairing K (kernelNineteenAddHom K φ (a + b))
      (kernelNineteenAddHom K ψ z) =
        actualGeometricNineteenPairing K (kernelNineteenAddHom K φ a) (kernelNineteenAddHom K ψ z) *
          actualGeometricNineteenPairing K (kernelNineteenAddHom K φ b) (kernelNineteenAddHom K ψ z)
    rw [map_add]
    exact MazurTransfer.KernelCyclotomicCharacterOriginalProofHelpers20261018.pairingUnits_add_left K (actualDivisorialNineteenPairingData K) _ _ _

def kernelPairingLinear : Additive (Kernel K φ) →ₗ[ZMod 19]
    (Additive (Kernel K ψ) →ₗ[ZMod 19] Additive (Roots K)) :=
  (kernelPairingAddHom K φ ψ).toZModLinearMap 19

theorem kernelPairingLinear_apply (a : Additive (Kernel K φ)) (z : Additive (Kernel K ψ)) :
    kernelPairingLinear K φ ψ a z = kernelCharacterLinear K φ ψ a z := rfl

end MazurTransfer.Order13ActualNormKernelPairingBilinear
#print axioms MazurTransfer.Order13ActualNormKernelPairingBilinear.kernelPairingAddHom
#print axioms MazurTransfer.Order13ActualNormKernelPairingBilinear.kernelPairingLinear


