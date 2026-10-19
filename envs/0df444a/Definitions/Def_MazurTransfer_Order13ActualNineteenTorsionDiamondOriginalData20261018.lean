-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionDiamondOriginalData20261018
-- name    : MazurTransfer_Order13ActualNineteenTorsionDiamondOriginalData20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T11:43:52.995519+00:00
-- url     : https://prove2.me/theorems/f46f32d3-f8e0-4117-8519-fff2fe2a3543
-- title:
--   Original actual and arithmetic diamond maps on nineteen-torsion
-- statement:
--   This interface preserves the original additive diamond map on actual Picard nineteen-torsion and the original arithmetic diamond map on divisor-class nineteen-torsion, with their original field hypotheses, complete types and nonproof values. Compatibility under the natural divisor-class equivalence is a subsequent theorem used for pairing invariance and norm adjointness.
-- source:
--   MazurTheorem Order13ActualGeometricNineteenTorsionDiamondComparison.actualNineteenTorsionDiamondHom and arithmeticNineteenTorsionDiamondHom, exact original constructors and values.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original actual and arithmetic diamond additive
maps on nineteen-torsion, preserving their complete types and values.
Named downstream consumer: natural torsion comparison under diamond,
actual pairing diamond invariance, and norm-factor adjointness.
-/
import Definitions.Def_MazurTransfer_Order13ActualNaturalNineteenTorsionDivisorAddEquivData20261018
import Definitions.Def_MazurTransfer_Order13FieldDiamondPicardEndomorphismsData
import Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNormGroupHom_schemeDiamond_isMonHom
noncomputable section
namespace MazurTransfer.Order13ActualGeometricNineteenTorsionDiamondComparison
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open GoodReductionJacobian NeronModelInfra
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualNormKernelProductCardinality Order13ActualGeometricNineteenTorsionDivisorComparison
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardGeometricDiamondGroupAction Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
attribute [local instance] actualNineteenTorsionProductOriginalGroupProvider20261018 actualNineteenTorsionProductOriginalCommProvider20261018 schemeDiamond_isMonHom
variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
local instance nineteenTorsionDiamondOriginalFactProvider20261018 : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance nineteenTorsionDiamondOriginalAlgebraProvider20261018 : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K

def actualNineteenTorsionDiamondHom : NineteenTorsion K →+ NineteenTorsion K where
  toFun x := ⟨(normHom K schemeDiamond).toAdditive x.val, by
    change (19 : ℕ) • (normHom K schemeDiamond).toAdditive x.val = 0
    have hx : (19 : ℕ) • x.val = 0 := x.property
    rw [← map_nsmul (normHom K schemeDiamond).toAdditive, hx, map_zero]⟩
  map_zero' := Subtype.ext (map_zero (normHom K schemeDiamond).toAdditive)
  map_add' x y := Subtype.ext (map_add (normHom K schemeDiamond).toAdditive x.val y.val)

def arithmeticNineteenTorsionDiamondHom :
    Pic0.torsion K (actualCurveFunctionField K) 19 →+
      Pic0.torsion K (actualCurveFunctionField K) 19 where
  toFun x := ⟨Order13FieldDiamondPicardEndomorphisms.rho K x.val, by
    change (19 : ℤ) • Order13FieldDiamondPicardEndomorphisms.rho K x.val = 0
    have hx : (19 : ℤ) • x.val = 0 := x.property
    rw [← map_zsmul (Order13FieldDiamondPicardEndomorphisms.rho K), hx, map_zero]⟩
  map_zero' := Subtype.ext (map_zero (Order13FieldDiamondPicardEndomorphisms.rho K))
  map_add' x y := Subtype.ext (map_add (Order13FieldDiamondPicardEndomorphisms.rho K) x.val y.val)

end MazurTransfer.Order13ActualGeometricNineteenTorsionDiamondComparison
#print axioms MazurTransfer.Order13ActualGeometricNineteenTorsionDiamondComparison.actualNineteenTorsionDiamondHom
#print axioms MazurTransfer.Order13ActualGeometricNineteenTorsionDiamondComparison.arithmeticNineteenTorsionDiamondHom


