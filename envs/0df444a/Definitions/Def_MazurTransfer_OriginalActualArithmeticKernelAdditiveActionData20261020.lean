-- Prove2me | Definitions.Def_MazurTransfer_OriginalActualArithmeticKernelAdditiveActionData20261020
-- name    : MazurTransfer_OriginalActualArithmeticKernelAdditiveActionData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T03:36:44.315984+00:00
-- url     : https://prove2.me/theorems/6acc660b-bbcf-428c-ad25-6d317dcccbb3
-- title:
--   Original arithmetic kernel additive action
-- statement:
--   Retain the original additive tag of the existing arithmetic kernel action, with its same chosen group, commutative-group certificate, multiplicative kernel action and additive action providers. All complete original types and every whole nonproof value, including the fixed original arithmetic action contexts, are independently checked. Pointwise comparison to the previously fixed F19 representation remains a separate theorem. Named downstream consumer: actual integral Hopf character quotient APIs.
-- source:
--   MazurTheorem Order13ActualArithmeticKernelAdditiveAction by Vas and contributors; preserve the previously fixed arithmetic action and F19 representation, Apache-2.0.

import Definitions.Def_MazurTransfer_OriginalPicardComparisonGroupProvidersData20261020
import Definitions.Def_MazurTransfer_Order13ActualNormKernelF19RepresentationOriginalContextDataV220261018
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: express the EXISTING arithmetic kernel action on its
additive type tag, and check pointwise equality with the PREVIOUSLY FIXED
F19 representation. No new geometric or transported Galois action.
Named downstream consumer: actual integral Hopf character quotient APIs.
-/

noncomputable section
namespace MazurTransfer.Order13ActualArithmeticKernelAdditiveAction
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardNormKernelGaloisAction Order13ActualNormKernelF19Representation
open Order13ActualNormKernelFiniteModule
open scoped CategoryTheory.MonObj
variable (K : Type) [Field K] [CharZero K]
local instance instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualArithmeticKernelAdditiveAction : GrpObj (Over.mk actualPicard.toBase) := actualGroup
local instance instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualArithmeticKernelAdditiveAction : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
local instance instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualArithmeticKernelAdditiveAction : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ

abbrev kernelAdditiveAction : DistribMulAction (K ≃ₐ[ℚ] K) (Additive (Kernel K φ)) where
  smul σ z := Additive.ofMul (σ • z.toMul)
  one_smul z := congrArg Additive.ofMul (one_smul (K ≃ₐ[ℚ] K) z.toMul)
  mul_smul σ τ z := congrArg Additive.ofMul (mul_smul σ τ z.toMul)
  smul_zero σ := congrArg Additive.ofMul (smul_one σ : σ • (1 : Kernel K φ) = 1)
  smul_add σ z w := congrArg Additive.ofMul (smul_mul' σ z.toMul w.toMul)

local instance instDistribMulActionAlgEquivRatAdditiveSubtypePointsMemSubgroupKernel_order13ActualArithmeticKernelAdditiveAction : DistribMulAction (K ≃ₐ[ℚ] K) (Additive (Kernel K φ)) := kernelAdditiveAction K φ





end MazurTransfer.Order13ActualArithmeticKernelAdditiveAction
#print axioms MazurTransfer.Order13ActualArithmeticKernelAdditiveAction.kernelAdditiveAction
#print axioms MazurTransfer.Order13ActualArithmeticKernelAdditiveAction.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualArithmeticKernelAdditiveAction
#print axioms MazurTransfer.Order13ActualArithmeticKernelAdditiveAction.instDistribMulActionAlgEquivRatAdditiveSubtypePointsMemSubgroupKernel_order13ActualArithmeticKernelAdditiveAction
#print axioms MazurTransfer.Order13ActualArithmeticKernelAdditiveAction.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualArithmeticKernelAdditiveAction
#print axioms MazurTransfer.Order13ActualArithmeticKernelAdditiveAction.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualArithmeticKernelAdditiveAction


