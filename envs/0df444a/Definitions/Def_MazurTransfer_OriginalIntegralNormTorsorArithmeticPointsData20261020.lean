-- Prove2me | Definitions.Def_MazurTransfer_OriginalIntegralNormTorsorArithmeticPointsData20261020
-- name    : MazurTransfer_OriginalIntegralNormTorsorArithmeticPointsData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-11-02T17:47:46.005193+00:00
-- url     : https://prove2.me/theorems/761fa4d4-9509-4f5f-98ce-519f2a1287c0
-- title:
--   Original rational norm preimages, arithmetic torsor point equivalence and differences
-- statement:
--   Use the same fixed arithmetic field-point equivalence and the same chosen integral Picard point to identify rational norm preimages with points of the original integral norm-preimage torsor. Its original group compatibility preserves inverse and differences. Its original field automorphism compatibility identifies the original arithmetic action. Consequently the previously fixed kernel cocycle is exactly the torsor difference for every original automorphism and preimage, without changing the selected cocycle or point label. All five complete original propositions and helper types, seven original constructor types and five whole values, three original scoped provider types and the group-provider whole value, all three private original-type construction certificates, generated helper types and every original coefficient and cocycle context are independently checked. Named downstream consumer: the exact selected literal mu19 torsor-cocycle pushforward and nineteen Kummer unit condition.
-- source:
--   MazurTheorem Order13IntegralNormTorsorArithmeticPoints by Vas and contributors; same selected pi quotient and normalized literal mu19 model, Apache-2.0.

import Definitions.Def_MazurTransfer_OriginalNineteenIntegralPointCompatibilityData20261020
import Theorems.Thm_MazurTransfer_original_nineteen_integral_point_compatibility
import Theorems.Thm_MazurTransfer_original_integral_arithmetic_field_point_comparison_laws
import Theorems.Thm_MazurTransfer_original_integral_norm_unit_and_all_point_identities
import Theorems.Thm_MazurTransfer_original_integral_norm_multiplication
noncomputable section

namespace MazurTransfer.Order13NineteenIntegralPointCompatibility
open CategoryTheory AlgebraicGeometry NeronModelInfra
open MazurTransfer.Order13LocalIntegralCoefficientMaps MazurTransfer.Order13ActualPicardNormKummerCocycles
open MazurTransfer.RelativeNormPreimageRepresentation MazurTransfer.FieldAutomorphismOverPointAction
attribute [local instance] MazurTransfer.Order13NineteenIntegralPointCompatibility.instFactPrimeOfNatNat_order13NineteenIntegralPointCompatibility
attribute [local instance] MazurTransfer.Order13NineteenIntegralPointCompatibility.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13NineteenIntegralPointCompatibility
private theorem integralPoint_field_compatibility (K : Type) [Field K] [CharZero K]
 [aRK : Algebra (LocalRing 19) K] [tRQ : IsScalarTower (LocalRing 19) ℚ K] (b : RationalPoints) :
 fixedActualFieldPointEquiv K (rationalPoint K b) =
 pulledPoint (integralPoint (overHomToSchemeHomOver b)) (fieldBase (LocalRing 19) K) :=
 MazurTransfer.original_nineteen_integral_point_compatibility.2.2.2 K b
end MazurTransfer.Order13NineteenIntegralPointCompatibility
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the ACTUAL integral norm torsor's field points
with the PREVIOUSLY FIXED rational norm preimages, retaining differences
and the original arithmetic Galois kernel cocycle for EVERY automorphism.
Named downstream consumer: exact selected mu19 torsor-cocycle pushforward
and the nineteen Kummer unit condition.
-/

noncomputable section
namespace MazurTransfer.Order13IntegralNormTorsorArithmeticPoints
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13LocalIntegralCoefficientMaps Order13ExceptionalNineteenFlatNormFibres
open Order13GoodPrimeLocalPicardModels Order13GoodPrimeIntegralNormExtensions
open Order13GoodPrimeIntegralNormGroupLaws Order13GoodPrimeIntegralNormPointwiseUnit
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardNormKummerCocycles Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKernelGaloisAction Order13NineteenIntegralPointCompatibility
open RelativeNormPreimagePointTorsor RelativeNormPreimageRepresentation
open scoped CategoryTheory.MonObj
local instance instFactPrimeOfNatNat_order13IntegralNormTorsorArithmeticPoints : Fact (Nat.Prime 19) := ⟨by norm_num⟩
local notation "R" => LocalRing 19
local instance instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralNormTorsorArithmeticPoints : GrpObj (Over.mk actualPicard.toBase) := actualGroup
local instance instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralNormTorsorArithmeticPoints : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
variable (K : Type) [Field K] [CharZero K]
variable [aRK : Algebra R K] [tRQ : IsScalarTower R ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
variable (a : RationalPoints)

abbrev rationalPreimages := {b : Points K // b ≫ φ = rationalPoint K a}

abbrev normOne {T : Scheme} (t : T ⟶ Spec (CommRingCat.of R)) :=
  MazurTransfer.original_integral_norm_unit_and_all_point_identities.2.2 19 nineteen_good φ t
abbrev normMul {T : Scheme} (t : T ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t integralModel.toBase) :=
  MazurTransfer.original_integral_norm_multiplication 19 nineteen_good φ t x y

private theorem fieldPoint_norm (b : Points K) :
    fixedActualFieldPointEquiv K (b ≫ φ) =
      NeronModelInfra.schemeHomOverComp (fixedActualFieldPointEquiv K b)
        (integralNorm 19 nineteen_good φ) :=
  MazurTransfer.original_integral_arithmetic_field_point_comparison_laws.2.2.2.1 19 nineteen_good K φ b

def preimageEquiv : rationalPreimages K φ a ≃
    preimagePoints (integralNorm 19 nineteen_good φ)
      (pulledPoint (integralPoint (overHomToSchemeHomOver a))
        (FieldAutomorphismOverPointAction.fieldBase R K)) where
  toFun b := ⟨fixedActualFieldPointEquiv K b.val,
    (fieldPoint_norm K φ b.val).symm.trans
      ((congrArg (fixedActualFieldPointEquiv K) b.property).trans (integralPoint_field_compatibility K a))⟩
  invFun y := ⟨(fixedActualFieldPointEquiv K).symm y.val, by
    apply (fixedActualFieldPointEquiv K).injective
    calc
      fixedActualFieldPointEquiv K ((fixedActualFieldPointEquiv K).symm y.val ≫ φ) =
          NeronModelInfra.schemeHomOverComp y.val (integralNorm 19 nineteen_good φ) :=
        (fieldPoint_norm K φ _).trans (congrArg
          (fun b => NeronModelInfra.schemeHomOverComp b (integralNorm 19 nineteen_good φ))
          ((fixedActualFieldPointEquiv K).apply_symm_apply y.val))
      _ = _ := y.property
      _ = fixedActualFieldPointEquiv K (rationalPoint K a) := (integralPoint_field_compatibility K a).symm⟩
  left_inv b := Subtype.ext ((fixedActualFieldPointEquiv K).symm_apply_apply b.val)
  right_inv y := Subtype.ext ((fixedActualFieldPointEquiv K).apply_symm_apply y.val)



def rationalDifference (x y : rationalPreimages K φ a) : Kernel K φ :=
  ⟨x.val * y.val⁻¹, by
    change normHom K φ (x.val * y.val⁻¹) = 1
    rw [map_mul, map_inv]
    change (x.val ≫ φ) * (y.val ≫ φ)⁻¹ = 1
    rw [x.property, y.property, mul_inv_cancel]⟩

def fixedKernelPointEquiv :=
  @Order13IntegralArithmeticNormKernelComparison.kernelPointEquiv 19 inferInstance nineteen_good
    K _ _ aRK tRQ φ inferInstance



def arithmeticPreimageAct (σ : K ≃ₐ[ℚ] K) (b : rationalPreimages K φ a) : rationalPreimages K φ a :=
  ⟨actionHom K σ b.val, by
    calc
      actionHom K σ b.val ≫ φ = actionHom K σ (b.val ≫ φ) :=
        (FieldAutomorphismOverPointAction.act_comp actualPicard.toBase σ b.val φ).symm
      _ = actionHom K σ (rationalPoint K a) := congrArg (actionHom K σ) b.property
      _ = rationalPoint K a := FieldAutomorphismOverPointAction.rationalPoint_fixed actualPicard.toBase σ a⟩





end MazurTransfer.Order13IntegralNormTorsorArithmeticPoints

#print axioms MazurTransfer.Order13IntegralNormTorsorArithmeticPoints.rationalPreimages
#print axioms MazurTransfer.Order13IntegralNormTorsorArithmeticPoints.normOne
#print axioms MazurTransfer.Order13IntegralNormTorsorArithmeticPoints.normMul
#print axioms MazurTransfer.Order13IntegralNormTorsorArithmeticPoints.preimageEquiv
#print axioms MazurTransfer.Order13IntegralNormTorsorArithmeticPoints.rationalDifference
#print axioms MazurTransfer.Order13IntegralNormTorsorArithmeticPoints.fixedKernelPointEquiv
#print axioms MazurTransfer.Order13IntegralNormTorsorArithmeticPoints.arithmeticPreimageAct
#print axioms MazurTransfer.Order13IntegralNormTorsorArithmeticPoints.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralNormTorsorArithmeticPoints
#print axioms MazurTransfer.Order13IntegralNormTorsorArithmeticPoints.instFactPrimeOfNatNat_order13IntegralNormTorsorArithmeticPoints
#print axioms MazurTransfer.Order13IntegralNormTorsorArithmeticPoints.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralNormTorsorArithmeticPoints


