-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualNormKernelEigenCharacterIntertwiningOriginalDataAndEquivarianceCertificate20261018
-- name    : MazurTransfer_Order13ActualNormKernelEigenCharacterIntertwiningOriginalDataAndEquivarianceCertificate20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T00:24:33.82658+00:00
-- url     : https://prove2.me/theorems/d6a9133e-228c-4099-af28-227184e198c6
-- title:
--   Original eigencharacter intertwining quotient of actual norm kernels
-- statement:
--   The original quotient map obtained by pairing against an actual character eigenvector, with target the literal nineteen-root representation twisted by the inverse character. Its complete original constructor type and whole value are checked, together with all required original module and group contexts. The generic bilinear eigenvector equivariance and the same actual bilinear pairing covariance are reused directly as accepted public theorems. Named downstream consumers: quotient surjectivity and the complementary arithmetic-character exact sequence. No arithmetic existence or eigenvector hypothesis is added.
-- source:
--   MazurTheorem Order13ActualNormKernelEigenCharacterQuotient, original kernelEigenCharacterIntertwining constructor; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: pairing against an actual character eigenvector gives an
actual equivariant quotient into literal mu19 twisted by that character's
inverse. Named downstream consumer: the complementary norm exact sequence.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNormKernelBilinearPairingOriginalDataAndActionCertificateExplicitKernelNamespaceV220261018
import Definitions.Def_MazurTransfer_RepresentationCharacterTwistOriginalDataAndActionCertificate20261018
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelPairingBilinear_kernelPairing_galois
import Theorems.Thm_MazurTransfer_bilinear_eigenvector_twisted_equivariance
noncomputable section
namespace MazurTransfer.Order13ActualNormKernelEigenCharacterQuotient
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
open Order13ActualNormKernelPairingBilinear RepresentationCharacterTwist
def kernelEigenCharacterIntertwining
    (χ : (K ≃ₐ[ℚ] K) →* (ZMod 19)ˣ) (b : Additive (Kernel K φ))
    (hb : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K φ σ b = (χ σ : ZMod 19) • b) :
    Representation.IntertwiningMap (kernelRepresentation K ψ) (twist χ⁻¹ (rootsRepresentation K)) :=
  (kernelCharacterLinear K φ ψ b).intertwiningMap_of_isIntertwiningMap _ _ (by
    intro σ z
    change kernelPairingLinear K φ ψ b (kernelRepresentation K ψ σ z) =
      (((χ σ)⁻¹ : (ZMod 19)ˣ) : ZMod 19) • rootsRepresentation K σ (kernelPairingLinear K φ ψ b z)
    exact MazurTransfer.bilinear_eigenvector_twisted_equivariance (ZMod 19) (K ≃ₐ[ℚ] K)
      (Additive (Kernel K φ)) (Additive (Kernel K ψ)) (Additive (Roots K))
      (kernelRepresentation K φ) (kernelRepresentation K ψ) (rootsRepresentation K)
      (kernelPairingLinear K φ ψ) (kernelPairing_galois K φ ψ) χ b hb σ z)
end MazurTransfer.Order13ActualNormKernelEigenCharacterQuotient
#print axioms MazurTransfer.Order13ActualNormKernelEigenCharacterQuotient.kernelEigenCharacterIntertwining


