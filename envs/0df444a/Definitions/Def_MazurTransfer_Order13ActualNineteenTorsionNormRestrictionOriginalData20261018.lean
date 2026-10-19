-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionNormRestrictionOriginalData20261018
-- name    : MazurTransfer_Order13ActualNineteenTorsionNormRestrictionOriginalData20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T12:15:58.570403+00:00
-- url     : https://prove2.me/theorems/a6013c57-6189-43c2-96dc-caf1ee391c27
-- title:
--   Original nineteen-torsion norm restrictions and complete norm-kernel equivalences
-- statement:
--   Preserve the original restriction of an actual Picard group endomorphism to nineteen-torsion, the equivalence from its restricted kernel to its complete kernel when killed by nineteen, and the two specializations for the actual norm factors. Four original constructor types and values and twelve original group and morphism provider types are checked. The downstream consumer is the equality of the complete norm-kernel cardinalities from the perfect actual divisorial pairing.
-- source:
--   MazurTheorem Order13ActualNineteenTorsionNormPairingAdjoint.actualNineteenTorsionNormHom and Order13ActualNormKernelRanksFromPerfectDivisorialPairing.restrictedNormKernelEquiv/restrictedPiKernelEquiv/restrictedPiConjugateKernelEquiv; exact original constructors.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: original norm maps restricted to the SAME actual
nineteen-torsion, and original equivalences between their restricted
kernels and the complete actual scheme norm kernels.
Named downstream consumer: equality of actual norm-kernel cardinalities
from perfect-pairing adjointness and individual actual kernel ranks.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelProductCardinalityData20261018
import Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNormGroupHom_schemePi_kernel_killed_nineteen
import Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNormGroupHom_schemePiConjugate_kernel_killed_nineteen
noncomputable section
namespace MazurTransfer.Order13ActualNineteenTorsionNormPairingAdjoint
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open Order13ActualNormKernelProductCardinality Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardNormKummerCocycles Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKernelGaloisAction Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open scoped CategoryTheory.MonObj
attribute [local instance] actualNineteenTorsionProductOriginalGroupProvider20261018 actualNineteenTorsionProductOriginalCommProvider20261018 actualNineteenTorsionProductOriginalPiHomProvider20261018 actualNineteenTorsionProductOriginalConjugateHomProvider20261018
variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]

def actualNineteenTorsionNormHom
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] :
    NineteenTorsion K →+ NineteenTorsion K where
  toFun x := ⟨(normHom K φ).toAdditive x.val, by
    change (19 : ℕ) • (normHom K φ).toAdditive x.val = 0
    have hx : (19 : ℕ) • x.val = 0 := x.property
    rw [← map_nsmul (normHom K φ).toAdditive, hx, map_zero]⟩
  map_zero' := Subtype.ext (map_zero (normHom K φ).toAdditive)
  map_add' x y := Subtype.ext (map_add (normHom K φ).toAdditive x.val y.val)

end MazurTransfer.Order13ActualNineteenTorsionNormPairingAdjoint
namespace MazurTransfer.Order13ActualNormKernelRanksFromPerfectDivisorialPairing
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open Order13ActualNineteenTorsionNormPairingAdjoint
open Order13ActualNormKernelProductCardinality Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardNormKummerCocycles Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKernelGaloisAction Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open scoped CategoryTheory.MonObj
attribute [local instance] actualNineteenTorsionProductOriginalGroupProvider20261018 actualNineteenTorsionProductOriginalCommProvider20261018 actualNineteenTorsionProductOriginalPiHomProvider20261018 actualNineteenTorsionProductOriginalConjugateHomProvider20261018
variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]

def restrictedNormKernelEquiv
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    (h19 : ∀ z : Kernel K φ, z.val ^ 19 = 1) :
    (actualNineteenTorsionNormHom K φ).ker ≃ Kernel K φ where
  toFun x := ⟨x.val.val.toMul, by
    have h := congrArg Subtype.val x.property
    change (x.val.val.toMul ≫ φ) = 1 at h
    exact h⟩
  invFun z := ⟨⟨Additive.ofMul z.val, by
    change z.val ^ 19 = 1
    exact h19 z⟩, by
    apply Subtype.ext
    exact z.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl

def restrictedPiKernelEquiv :
    (actualNineteenTorsionNormHom K schemePi).ker ≃ Kernel K schemePi :=
  restrictedNormKernelEquiv K schemePi (fun z => schemePi_kernel_killed_nineteen
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ K)))) z.val z.property)

def restrictedPiConjugateKernelEquiv :
    (actualNineteenTorsionNormHom K schemePiConjugate).ker ≃ Kernel K schemePiConjugate :=
  restrictedNormKernelEquiv K schemePiConjugate (fun z => schemePiConjugate_kernel_killed_nineteen
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ K)))) z.val z.property)

end MazurTransfer.Order13ActualNormKernelRanksFromPerfectDivisorialPairing
#print axioms MazurTransfer.Order13ActualNineteenTorsionNormPairingAdjoint.actualNineteenTorsionNormHom
#print axioms MazurTransfer.Order13ActualNormKernelRanksFromPerfectDivisorialPairing.restrictedNormKernelEquiv
#print axioms MazurTransfer.Order13ActualNormKernelRanksFromPerfectDivisorialPairing.restrictedPiKernelEquiv
#print axioms MazurTransfer.Order13ActualNormKernelRanksFromPerfectDivisorialPairing.restrictedPiConjugateKernelEquiv


