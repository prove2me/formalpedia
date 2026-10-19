-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionReflectionOriginalAdditiveEquivalencesAndClassCertificate20261018
-- name    : MazurTransfer_Order13ActualNineteenTorsionReflectionOriginalAdditiveEquivalencesAndClassCertificate20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T21:35:08.66514+00:00
-- url     : https://prove2.me/theorems/f29f521a-9080-49c6-a0cd-da97a4607c0c
-- title:
--   Original reflection equivalences on actual geometric nineteen-torsion
-- statement:
--   The original Picard reflection restricts to divisorial nineteen-torsion and transports through the original geometric-divisor additive equivalence to the same actual represented Picard nineteen-torsion. Three complete original declaration types and both whole additive-equivalence values are checked, with seven own provider types and two values and thirty-one dependency provider types and twelve values. Eight candidate provider names belong to modules outside the original dependency environment and contribute no checks or credit. Named downstream consumer: MazurTransfer.Order13ActualNineteenTorsionReflection.actualReflection_normPi. The norm-exchange and pairing-preservation identities remain separate theorems.
-- source:
--   MazurTheorem Order13ActualNineteenTorsionReflection.divisorTorsionReflection, actualReflection and actualReflection_class, preserving the original actual geometric Picard group and Anthropic FLT divisor-class action; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal curve reflection acts on the SAME actual Picard
nineteen-torsion through its intrinsic divisor-class equivalence. It exchanges
the actual norm factors and preserves their actual divisorial pairing.
Named downstream consumer: the one-dimensional kernel of the actual
cyclotomic quotient and its arithmetic character.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13FieldPicardReflectionOriginalAdditiveEquivalenceDataAndCertificate20261018
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionNormRestrictionOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionPairingTransportOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionDiamondOriginalData20261018
noncomputable section
namespace MazurTransfer.Order13ActualNineteenTorsionReflection
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardGeometricNormPreimages
open Order13ActualNormKernelProductCardinality
open Order13ActualPicardAlgPointsComparison
open Order13ActualPicardGeometricArithmeticGroup
open Order13ActualPicardGeometricDiamondGroupAction
open scoped CategoryTheory.MonObj
local instance actualReflectionOriginalGroupProvider20261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualReflectionOriginalCommProvider20261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
open Order13ActualGeometricNineteenTorsionDivisorComparison
open Order13ActualPicardSchemeNormGroupHom Order13ActualPicardNormKummerCocycles
local instance actualReflectionOriginalDiamondHomProvider20261018 : IsMonHom schemeDiamond := schemeDiamond_isMonHom
variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
local instance actualReflectionOriginalFactProvider20261018 : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance actualReflectionOriginalAlgebraProvider20261018 : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K

open Order13ActualGeometricNineteenTorsionDiamondComparison

open Order13ActualNineteenTorsionPairingTransport
open Order13ActualPicardSchemeNineteenNorm
local instance actualReflectionOriginalPiHomProvider20261018 : IsMonHom schemePi := schemePi_isMonHom
local instance actualReflectionOriginalConjugateHomProvider20261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ReflectionParameter Order13FieldPicardReflection
open Order13ActualNineteenTorsionNormPairingAdjoint

def divisorTorsionReflection (a : ReflectionParameter K) :
    Pic0.torsion K (actualCurveFunctionField K) 19 ≃+
      Pic0.torsion K (actualCurveFunctionField K) 19 where
  toFun x := ⟨reflection K a x.val, by
    change (19 : ℤ) • reflection K a x.val = 0
    have hx : (19 : ℤ) • x.val = 0 := x.property
    rw [← map_zsmul (reflection K a), hx, map_zero]⟩
  invFun x := ⟨reflection K a x.val, by
    change (19 : ℤ) • reflection K a x.val = 0
    have hx : (19 : ℤ) • x.val = 0 := x.property
    rw [← map_zsmul (reflection K a), hx, map_zero]⟩
  left_inv x := by
    apply Subtype.ext
    exact (reflection K a).left_inv x.val
  right_inv x := by
    apply Subtype.ext
    exact (reflection K a).right_inv x.val
  map_add' x y := Subtype.ext (map_add (reflection K a) x.val y.val)

def actualReflection (a : ReflectionParameter K) : NineteenTorsion K ≃+ NineteenTorsion K :=
  ((geometricNineteenTorsionDivisorAddEquiv K).trans (divisorTorsionReflection K a)).trans
    (geometricNineteenTorsionDivisorAddEquiv K).symm

theorem actualReflection_class (a : ReflectionParameter K) (x : NineteenTorsion K) :
    geometricNineteenTorsionDivisorAddEquiv K (actualReflection K a x) =
      divisorTorsionReflection K a (geometricNineteenTorsionDivisorAddEquiv K x) :=
  (geometricNineteenTorsionDivisorAddEquiv K).apply_symm_apply _

end MazurTransfer.Order13ActualNineteenTorsionReflection
#print axioms MazurTransfer.Order13ActualNineteenTorsionReflection.actualReflection


