-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualNormKernelProductCardinalityData20261018
-- name    : MazurTransfer_Order13ActualNormKernelProductCardinalityData20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T08:35:10.636991+00:00
-- url     : https://prove2.me/theorems/4125f54d-1982-4e32-9067-cd6a62883120
-- title:
--   The original actual Picard nineteen-torsion and two norm-kernel product equivalence
-- statement:
--   For the original actual rational Picard scheme and any characteristic-zero field K, retain the subgroup of its geometric points killed by nineteen, the additive-to-multiplicative kernel equivalence, and the original equivalence from nineteen-torsion to the product of the two specific norm kernels. The original group object, commutativity and both norm-homomorphism providers are retained and checked. The product construction uses the publicly proved two scalar-nineteen composites and the literal sum-eight identity. Individual cardinalities and geometric ranks are separate obligations. Named downstream consumer: the intrinsic geometric nineteen-torsion divisor comparison and the actual divisorial pairing.
-- source:
--   MazurTheorem, Order13ActualNormKernelProductCardinality.lean; Apache-2.0. Four complete original declaration types, three nonproof values, and all four original instance-provider types with their one nonproof group-object value checked against the original module.

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: nineteen-torsion of the SAME actual Picard scheme splits
as the product of its two actual norm kernels over any characteristic-zero field.
Named downstream consumer: deriving geometric norm kernel dimensions from
actual Picard torsion cardinality. No numerical dimension or degree is asserted. -/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelFiniteF19ModuleWithOriginalExponentFactsData20261017
import Definitions.Def_MazurTransfer_ArithmeticNineteenKernelDecompositionData20261018
import Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNineteenNorm_schemePi_comp_schemePiConjugate
import Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNineteenNorm_schemePiConjugate_comp_schemePi
noncomputable section
namespace MazurTransfer.Order13ActualNormKernelProductCardinality
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualNineteenTorsionProductOriginalGroupProvider20261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNineteenTorsionProductOriginalCommProvider20261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNineteenTorsionProductOriginalPiHomProvider20261018 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNineteenTorsionProductOriginalConjugateHomProvider20261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K]

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelFiniteModule

theorem schemePi_mul_schemePiConjugate :
    schemePi * schemePiConjugate = (𝟙 (Over.mk actualPicard.toBase)) ^ 8 := by
  dsimp only [schemePi, schemePiConjugate]
  rw [mul_mul_mul_comm, mul_inv_cancel, mul_one, ← pow_add]

def additiveKernelEquiv (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    [IsMonHom φ] : (normHom K φ).toAdditive.ker ≃ Kernel K φ where
  toFun x := ⟨x.val.toMul, x.property⟩
  invFun x := ⟨Additive.ofMul x.val, x.property⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

abbrev NineteenTorsion :=
  ArithmeticNineteenKernelDecomposition.nineteenTorsion (G := Additive (Points K))

def kernelProductEquiv : NineteenTorsion K ≃ Kernel K schemePi × Kernel K schemePiConjugate :=
  (ArithmeticNineteenKernelDecomposition.kernelProductEquiv
    (normHom K schemePi).toAdditive (normHom K schemePiConjugate).toAdditive
    (fun x => by
      change (x.toMul ≫ schemePiConjugate) ≫ schemePi = x.toMul ^ 19
      rw [Category.assoc, schemePiConjugate_comp_schemePi, MonObj.comp_pow, Category.comp_id])
    (fun x => by
      change (x.toMul ≫ schemePi) ≫ schemePiConjugate = x.toMul ^ 19
      rw [Category.assoc, schemePi_comp_schemePiConjugate, MonObj.comp_pow, Category.comp_id])
    (fun x => by
      change (x.toMul ≫ schemePi) * (x.toMul ≫ schemePiConjugate) = x.toMul ^ 8
      rw [← MonObj.comp_mul, schemePi_mul_schemePiConjugate, MonObj.comp_pow, Category.comp_id])).trans
    (Equiv.prodCongr (additiveKernelEquiv K schemePi) (additiveKernelEquiv K schemePiConjugate))


end MazurTransfer.Order13ActualNormKernelProductCardinality
#print axioms MazurTransfer.Order13ActualNormKernelProductCardinality.actualNineteenTorsionProductOriginalGroupProvider20261018
#print axioms MazurTransfer.Order13ActualNormKernelProductCardinality.actualNineteenTorsionProductOriginalCommProvider20261018
#print axioms MazurTransfer.Order13ActualNormKernelProductCardinality.actualNineteenTorsionProductOriginalPiHomProvider20261018
#print axioms MazurTransfer.Order13ActualNormKernelProductCardinality.actualNineteenTorsionProductOriginalConjugateHomProvider20261018
#print axioms MazurTransfer.Order13ActualNormKernelProductCardinality.schemePi_mul_schemePiConjugate
#print axioms MazurTransfer.Order13ActualNormKernelProductCardinality.additiveKernelEquiv
#print axioms MazurTransfer.Order13ActualNormKernelProductCardinality.NineteenTorsion
#print axioms MazurTransfer.Order13ActualNormKernelProductCardinality.kernelProductEquiv


