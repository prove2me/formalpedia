-- Prove2me | Definitions.Def_MazurTransfer_OriginalIntegralArithmeticNormKernelComparisonData20261020
-- name    : MazurTransfer_OriginalIntegralArithmeticNormKernelComparisonData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T03:14:22.209955+00:00
-- url     : https://prove2.me/theorems/3df06f33-a74e-4025-9ab1-3e1eae7279f4
-- title:
--   Original integral norm-kernel arithmetic point equivalence
-- statement:
--   Retain the original equivalence between points of the same integral local norm kernel and the previously fixed arithmetic kernel of the same rational norm map. Its complete original type and whole equivalence value, both chosen original group and Galois action provider types and values, and the original coefficient and kernel contexts are independently checked. Named downstream consumer: actual finite-flat ordered arithmetic character quotients.
-- source:
--   MazurTheorem Order13IntegralArithmeticNormKernelComparison by Vas and contributors; complete original kernel equivalence and fixed arithmetic action, preserving Apache-2.0 attribution.

import Definitions.Def_MazurTransfer_OriginalIntegralArithmeticFieldPointComparisonData20261020
import Definitions.Def_MazurTransfer_OriginalRelativeNormKernelSchemePointsAndGroupLawData20261020
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormExtensionsData
import Definitions.Def_MazurTransfer_Order13ActualPicardNormKernelGaloisActionData
import Theorems.Thm_MazurTransfer_original_integral_arithmetic_field_point_comparison_laws
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the SAME integral norm-kernel point functor
with the PREVIOUSLY FIXED arithmetic Kernel of the rational norm map.
Preserve its multiplication and the existing Galois action by spectrum
precomposition; no transported substitute action or splitting is used.
Named downstream consumer: finite-flat ordered arithmetic character quotients.
-/

noncomputable section
namespace MazurTransfer.Order13IntegralArithmeticNormKernelComparison
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open Order13IntegralArithmeticFieldPointComparison
open Order13LocalIntegralCoefficientMaps Order13GoodPrimeLocalPicardModels
open Order13GoodPrimeIntegralNormExtensions RelativeGroupLawFiniteFlatKernelHopf
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardGeometricNormPreimages Order13ActualPicardNormKummerCocycles
open Order13ActualPicardNormKernelGaloisAction
open scoped CategoryTheory.MonObj
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)
variable (K : Type) [Field K] [CharZero K]
variable [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K]
local instance instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralArithmeticNormKernelComparison : GrpObj (Over.mk actualPicard.toBase) := actualGroup
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
local instance instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13IntegralArithmeticNormKernelComparison : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ

def kernelPointEquiv : Kernel K φ ≃
    kernelPoints (localLaw q hq) (integralNorm q hq φ)
      (FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K) where
  toFun z := ⟨actualFieldPointEquiv q hq K z.val, by
    exact ((MazurTransfer.original_integral_arithmetic_field_point_comparison_laws).2.2.2.1 q hq K φ z.val).symm.trans
      ((congrArg (actualFieldPointEquiv q hq K) z.property).trans
        ((MazurTransfer.original_integral_arithmetic_field_point_comparison_laws).2.1 q hq K))⟩
  invFun x := ⟨(actualFieldPointEquiv q hq K).symm x.val, by
    apply (actualFieldPointEquiv q hq K).injective
    change actualFieldPointEquiv q hq K
      ((actualFieldPointEquiv q hq K).symm x.val ≫ φ) = actualFieldPointEquiv q hq K 1
    calc
      actualFieldPointEquiv q hq K ((actualFieldPointEquiv q hq K).symm x.val ≫ φ) =
          NeronModelInfra.schemeHomOverComp x.val (integralNorm q hq φ) :=
        ((MazurTransfer.original_integral_arithmetic_field_point_comparison_laws).2.2.2.1 q hq K φ _).trans
          (congrArg (fun a => NeronModelInfra.schemeHomOverComp a (integralNorm q hq φ))
            ((actualFieldPointEquiv q hq K).apply_symm_apply x.val))
      _ = (localLaw q hq).one _ := x.property
      _ = actualFieldPointEquiv q hq K 1 := ((MazurTransfer.original_integral_arithmetic_field_point_comparison_laws).2.1 q hq K).symm⟩
  left_inv z := Subtype.ext ((actualFieldPointEquiv q hq K).symm_apply_apply z.val)
  right_inv x := Subtype.ext ((actualFieldPointEquiv q hq K).apply_symm_apply x.val)





end MazurTransfer.Order13IntegralArithmeticNormKernelComparison
#print axioms MazurTransfer.Order13IntegralArithmeticNormKernelComparison.kernelPointEquiv
#print axioms MazurTransfer.Order13IntegralArithmeticNormKernelComparison.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralArithmeticNormKernelComparison
#print axioms MazurTransfer.Order13IntegralArithmeticNormKernelComparison.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13IntegralArithmeticNormKernelComparison


