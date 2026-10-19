-- Prove2me | Definitions.Def_MazurTransfer_Order13DyadicOriginalContinuousKummerTopologyAndScopedActionsData20261019
-- name    : MazurTransfer_Order13DyadicOriginalContinuousKummerTopologyAndScopedActionsData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T11:17:57.259619+00:00
-- url     : https://prove2.me/theorems/f4f2dac7-07fa-46a1-aa49-401d4c7d3e11
-- title:
--   Original dyadic Kummer topology and Galois action constructors
-- statement:
--   Let $P$ be the fixed original arithmetic Picard scheme. For a characteristic-zero field $K$, retain the original discrete topology on $P(K)$ and its original field-automorphism action.
--
--   $$\tau_{P(K)}=\tau_{\mathrm{disc}}.$$
--
--   The original actions on each geometric norm kernel and the scoped continuity and group structures are retained with their complete types and whole nonproof values. Named downstream consumer: continuous norm Kummer classes restricted to genuine valuation inertia above two.
-- source:
--   MazurTheorem original mixed single-section parameter algebras and reciprocal recovery, by Vas and contributors; exact official Anthropic FLT quotient/base-change bridge at pin 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0. Original per-file attribution retained.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: ONLY original topology, action and scoped group/provider constructors; all substantial dyadic Kummer proofs are separate theorem submissions.
Named downstream consumer: vanishing of the two fixed actual continuous norm quotient Kummer classes on every genuine valuation inertia subgroup above two.
Original file header and all constructor bodies are preserved below.
-/
import Definitions.Def_MazurTransfer_Order13DyadicOriginalNormInertiaScopedGroupProvidersV220261019
import Definitions.Def_MazurTransfer_Order13ActualConcreteContinuousNormKummerGroupHomData
import Definitions.Def_MazurTransfer_Order13ActualNormSubgroupRestrictionWithCoboundaryLawDataV220261018
import Definitions.Def_MazurTransfer_Order13ActualNormSubgroupRestrictionF19ConcreteData
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormContinuousCocycles_kernel_continuousSMul

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: continuous Kummer classes for the SAME actual rational
norm maps restrict to zero on the genuine valuation inertia groups at
the prime TWO, via the actual mixed dyadic Picard model.
The original good-prime proof specializes to the now proved actual
dyadic norm inertia theorem. No assumptions on 104-invertibility enter.
Named downstream consumer: global norm Selmer bounds.
-/

noncomputable section
namespace MazurTransfer.Order13DyadicMixedUnramifiedKummer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages Order13ActualPicardNormKummerCocycles
open Order13LocalIntegralCoefficientMaps
open scoped CategoryTheory.MonObj
local instance instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedUnramifiedKummer : GrpObj (Over.mk actualPicard.toBase) :=
  Order13DyadicMixedRationalPicardComparison.actualGroup
local instance instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedUnramifiedKummer : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj

local instance instFactPrimeOfNatNat_order13DyadicMixedUnramifiedKummer : Fact (Nat.Prime 2) := ⟨by decide⟩
variable (K : Type) [Field K] [CharZero K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]



open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable [IsGalois ℚ K]
abbrev pointsTopology : TopologicalSpace (Points K) := ⊥
local instance instTopologicalSpacePoints_order13DyadicMixedUnramifiedKummer : TopologicalSpace (Points K) := pointsTopology K
local instance instDiscreteTopologyPoints_order13DyadicMixedUnramifiedKummer : DiscreteTopology (Points K) := ⟨rfl⟩
local instance instMulActionAlgEquivRatPoints_order13DyadicMixedUnramifiedKummer : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  Order13ActualPicardNormSubgroupRestriction.actualNormSubgroupRestrictionDataProvider720261018 K
local instance instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13DyadicMixedUnramifiedKummer : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ
open Order13ActualPicardNormAlgebraicCohomology Order13ActualPicardNormContinuousCocycles
variable [IsFinite φ.left]
local instance instContinuousSMulAlgEquivRatSubtypePointsMemSubgroupKernel_order13DyadicMixedUnramifiedKummer : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) := kernel_continuousSMul K φ
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormSubgroupRestriction



end MazurTransfer.Order13DyadicMixedUnramifiedKummer

end
#print axioms MazurTransfer.Order13DyadicMixedUnramifiedKummer.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedUnramifiedKummer
#print axioms MazurTransfer.Order13DyadicMixedUnramifiedKummer.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedUnramifiedKummer
#print axioms MazurTransfer.Order13DyadicMixedUnramifiedKummer.instFactPrimeOfNatNat_order13DyadicMixedUnramifiedKummer
#print axioms MazurTransfer.Order13DyadicMixedUnramifiedKummer.instTopologicalSpacePoints_order13DyadicMixedUnramifiedKummer
#print axioms MazurTransfer.Order13DyadicMixedUnramifiedKummer.instDiscreteTopologyPoints_order13DyadicMixedUnramifiedKummer
#print axioms MazurTransfer.Order13DyadicMixedUnramifiedKummer.instMulActionAlgEquivRatPoints_order13DyadicMixedUnramifiedKummer
#print axioms MazurTransfer.Order13DyadicMixedUnramifiedKummer.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13DyadicMixedUnramifiedKummer
#print axioms MazurTransfer.Order13DyadicMixedUnramifiedKummer.instContinuousSMulAlgEquivRatSubtypePointsMemSubgroupKernel_order13DyadicMixedUnramifiedKummer
#print axioms MazurTransfer.Order13DyadicMixedUnramifiedKummer.pointsTopology


