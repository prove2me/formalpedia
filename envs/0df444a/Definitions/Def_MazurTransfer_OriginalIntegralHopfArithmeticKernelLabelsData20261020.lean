-- Prove2me | Definitions.Def_MazurTransfer_OriginalIntegralHopfArithmeticKernelLabelsData20261020
-- name    : MazurTransfer_OriginalIntegralHopfArithmeticKernelLabelsData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T03:49:08.911802+00:00
-- url     : https://prove2.me/theorems/668d72da-b00d-446a-be8a-f90fd202be25
-- title:
--   Original integral Hopf labels into the fixed arithmetic norm kernel
-- statement:
--   Retain both original integral Hopf point labels, first into the previously fixed arithmetic norm kernel and then its additive type tag, with all three same chosen group and arithmetic action providers. Complete original constructor types, whole label values, provider types and values, and original arithmetic coefficient contexts are independently checked. The four multiplication, addition and spectrum-precomposition action laws remain separate theorem interfaces. Named downstream consumer: actual finite-flat ordered arithmetic character quotients.
-- source:
--   MazurTheorem Order13IntegralHopfArithmeticKernelLabels by Vas and contributors; retain the same integral Hopf points, fixed kernel and arithmetic action, Apache-2.0.

import Definitions.Def_MazurTransfer_OriginalIntegralArithmeticNormKernelComparisonData20261020
import Definitions.Def_MazurTransfer_OriginalActualArithmeticKernelAdditiveActionData20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: label the SAME integral Hopf points by the PREVIOUSLY
FIXED arithmetic norm kernel and its existing additive Galois action.
The point equivalence must preserve multiplication and spectrum
precomposition, not merely cardinality or abstract module isomorphism.
Named downstream consumer: actual finite-flat ordered character quotients.
-/

noncomputable section
namespace MazurTransfer.Order13IntegralHopfArithmeticKernelLabels
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open Order13IntegralArithmeticNormKernelComparison Order13IntegralArithmeticFieldPointComparison
open Order13LocalIntegralCoefficientMaps Order13GoodPrimeLocalPicardModels
open Order13GoodPrimeIntegralNormExtensions RelativeGroupLawFiniteFlatKernelHopf
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardGeometricNormPreimages Order13ActualPicardNormKummerCocycles
open Order13ActualPicardNormKernelGaloisAction Order13ActualArithmeticKernelAdditiveAction
open scoped CategoryTheory.MonObj
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)
variable (K : Type) [Field K] [CharZero K]
variable [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K]
local instance instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralHopfArithmeticKernelLabels : GrpObj (Over.mk actualPicard.toBase) := actualGroup
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
local instance instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13IntegralHopfArithmeticKernelLabels : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ
local instance instDistribMulActionAlgEquivRatAdditiveSubtypePointsMemSubgroupKernel_order13IntegralHopfArithmeticKernelLabels : DistribMulAction (K ≃ₐ[ℚ] K) (Additive (Kernel K φ)) := kernelAdditiveAction K φ
variable {H : Type} [CommRing H] [HopfAlgebra (LocalRing q) H]
variable (e : WithConv (H →ₐ[LocalRing q] K) ≃
  kernelPoints (localLaw q hq) (integralNorm q hq φ)
    (FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K))

def fixedKernelLabel : WithConv (H →ₐ[LocalRing q] K) ≃ Kernel K φ :=
  e.trans (kernelPointEquiv q hq K φ).symm





def arithmeticKernelLabel : WithConv (H →ₐ[LocalRing q] K) ≃ Additive (Kernel K φ) :=
  (fixedKernelLabel q hq K φ e).trans Additive.ofMul





end MazurTransfer.Order13IntegralHopfArithmeticKernelLabels
#print axioms MazurTransfer.Order13IntegralHopfArithmeticKernelLabels.fixedKernelLabel
#print axioms MazurTransfer.Order13IntegralHopfArithmeticKernelLabels.arithmeticKernelLabel
#print axioms MazurTransfer.Order13IntegralHopfArithmeticKernelLabels.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralHopfArithmeticKernelLabels
#print axioms MazurTransfer.Order13IntegralHopfArithmeticKernelLabels.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13IntegralHopfArithmeticKernelLabels
#print axioms MazurTransfer.Order13IntegralHopfArithmeticKernelLabels.instDistribMulActionAlgEquivRatAdditiveSubtypePointsMemSubgroupKernel_order13IntegralHopfArithmeticKernelLabels


