-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualNormKernelReflectionOriginalRestrictedCompleteEquivalencesAndEmbeddingCertificatesExplicitFiniteExponentContextV220261018
-- name    : MazurTransfer_Order13ActualNormKernelReflectionOriginalRestrictedCompleteEquivalencesAndEmbeddingCertificatesExplicitFiniteExponentContextV220261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T22:27:59.012364+00:00
-- url     : https://prove2.me/theorems/871719b9-c965-4d58-a016-44a92166b477
-- title:
--   Original reflection equivalences on the restricted and complete actual norm kernels
-- statement:
--   The original restricted-kernel reflection and the two complete-kernel additive equivalences retain both embedding identities. Five complete original declaration types and three whole values are checked, with seventy-nine context-provider types and twenty-seven values, and three original constructor-helper propositions supplied by the accepted actual nineteen-torsion reflection certificates. Named downstream consumer: MazurTransfer.order13_actual_norm_kernel_reflection_galois_certificates. No additional kernel hypothesis is introduced.
-- source:
--   MazurTheorem Order13ActualReflectionPairingOrthogonality.restrictedKernelReflection and Order13ActualNormKernelReflection.piKernelReflection, piConjugateKernelReflection and their embedding identities; original complete kernels and Anthropic FLT Picard comparison preserved; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original reflection equivalences on restricted and
complete kernels of the same two actual Picard norm maps.
Named downstream consumer: MazurTransfer.Order13ActualNormKernelReflection.piKernelReflection_galois.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNormKernelRanksTwoOriginalModuleContextData20261018
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionReflectionOriginalAdditiveEquivalencesAndClassCertificate20261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelNineteenEmbeddingOriginalData20261018
import Theorems.Thm_MazurTransfer_order13_actual_nineteen_torsion_reflection_certificates
noncomputable section
open MazurTransfer CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open GoodReductionJacobian NeronModelInfra
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualNormKernelProductCardinality
open Order13ActualPicardGeometricNormPreimages Order13ActualPicardSchemeNineteenNorm
open Order13ActualPicardNormKernelGaloisAction Order13ActualNormKernelNineteenEmbedding
open Order13ReflectionParameter Order13ActualNineteenTorsionReflection
open Order13ActualNineteenTorsionNormPairingAdjoint
open scoped CategoryTheory.MonObj
attribute [local instance] Order13ActualNineteenTorsionReflection.actualReflectionOriginalGroupProvider20261018
  Order13ActualNineteenTorsionReflection.actualReflectionOriginalCommProvider20261018
  Order13ActualNineteenTorsionReflection.actualReflectionOriginalPiHomProvider20261018
  Order13ActualNineteenTorsionReflection.actualReflectionOriginalConjugateHomProvider20261018
  Order13ActualNineteenTorsionReflection.actualReflectionOriginalFactProvider20261018
  Order13ActualNineteenTorsionReflection.actualReflectionOriginalAlgebraProvider20261018
attribute [local instance] MazurTransfer.Order13ActualNormKernelRanksTwo.originalNormKernelRanksTwoPiFiniteProvider20261018
  MazurTransfer.Order13ActualNormKernelRanksTwo.originalNormKernelRanksTwoConjugateFiniteProvider20261018
  MazurTransfer.Order13ActualNormKernelRanksTwo.originalNormKernelRanksTwoPiExponentProvider20261018
  MazurTransfer.Order13ActualNormKernelRanksTwo.originalNormKernelRanksTwoConjugateExponentProvider20261018
namespace MazurTransfer.NormKernelReflectionConstructorProofHelpers20261018
variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
theorem actualReflection_involution (a : ReflectionParameter K) (x : NineteenTorsion K) :
    actualReflection K a (actualReflection K a x) = x :=
  (MazurTransfer.order13_actual_nineteen_torsion_reflection_certificates).1 K a x
theorem actualReflection_normPi (a : ReflectionParameter K) (x : NineteenTorsion K) :
    actualReflection K a (actualNineteenTorsionNormHom K schemePi x) =
      actualNineteenTorsionNormHom K schemePiConjugate (actualReflection K a x) :=
  (MazurTransfer.order13_actual_nineteen_torsion_reflection_certificates).2.1 K a x
theorem actualReflection_normPiConjugate (a : ReflectionParameter K) (x : NineteenTorsion K) :
    actualReflection K a (actualNineteenTorsionNormHom K schemePiConjugate x) =
      actualNineteenTorsionNormHom K schemePi (actualReflection K a x) :=
  (MazurTransfer.order13_actual_nineteen_torsion_reflection_certificates).2.2 K a x
end MazurTransfer.NormKernelReflectionConstructorProofHelpers20261018
open MazurTransfer.NormKernelReflectionConstructorProofHelpers20261018
namespace MazurTransfer.Order13ActualReflectionPairingOrthogonality
variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
def restrictedKernelReflection (a : ReflectionParameter K) :
    (actualNineteenTorsionNormHom K schemePi).ker ≃+
      (actualNineteenTorsionNormHom K schemePiConjugate).ker where
  toFun x := ⟨actualReflection K a x.val, by
    change actualNineteenTorsionNormHom K schemePiConjugate (actualReflection K a x.val) = 0
    rw [← actualReflection_normPi]
    have hx : actualNineteenTorsionNormHom K schemePi x.val = 0 := x.property
    rw [hx, map_zero]⟩
  invFun x := ⟨actualReflection K a x.val, by
    change actualNineteenTorsionNormHom K schemePi (actualReflection K a x.val) = 0
    rw [← actualReflection_normPiConjugate]
    have hx : actualNineteenTorsionNormHom K schemePiConjugate x.val = 0 := x.property
    rw [hx, map_zero]⟩
  left_inv x := Subtype.ext (actualReflection_involution K a x.val)
  right_inv x := Subtype.ext (actualReflection_involution K a x.val)
  map_add' x y := Subtype.ext (map_add (actualReflection K a) x.val y.val)

end MazurTransfer.Order13ActualReflectionPairingOrthogonality
namespace MazurTransfer.Order13ActualNormKernelReflection
open Order13ActualReflectionPairingOrthogonality
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
def piKernelReflection (a : ReflectionParameter K) :
    Additive (Kernel K schemePi) ≃+ Additive (Kernel K schemePiConjugate) :=
  ((kernelRestrictedAddEquiv K schemePi).trans (restrictedKernelReflection K a)).trans
    (kernelRestrictedAddEquiv K schemePiConjugate).symm

def piConjugateKernelReflection (a : ReflectionParameter K) :
    Additive (Kernel K schemePiConjugate) ≃+ Additive (Kernel K schemePi) :=
  (piKernelReflection K a).symm

theorem piKernelReflection_embed (a : ReflectionParameter K) (z : Additive (Kernel K schemePi)) :
    kernelNineteenAddHom K schemePiConjugate (piKernelReflection K a z) =
      actualReflection K a (kernelNineteenAddHom K schemePi z) := by
  have h := (kernelRestrictedAddEquiv K schemePiConjugate).apply_symm_apply
    (restrictedKernelReflection K a (kernelRestrictedAddEquiv K schemePi z))
  exact congrArg Subtype.val h

theorem piConjugateKernelReflection_embed (a : ReflectionParameter K)
    (z : Additive (Kernel K schemePiConjugate)) :
    kernelNineteenAddHom K schemePi (piConjugateKernelReflection K a z) =
      actualReflection K a (kernelNineteenAddHom K schemePiConjugate z) := by
  apply (actualReflection K a).injective
  rw [actualReflection_involution]
  have h := piKernelReflection_embed K a (piConjugateKernelReflection K a z)
  change kernelNineteenAddHom K schemePiConjugate
    (piKernelReflection K a ((piKernelReflection K a).symm z)) = _ at h
  rw [AddEquiv.apply_symm_apply] at h
  exact h.symm

end MazurTransfer.Order13ActualNormKernelReflection
#print axioms MazurTransfer.Order13ActualNormKernelReflection.piKernelReflection


