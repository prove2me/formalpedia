-- Prove2me | Definitions.Def_MazurTransfer_Order13OriginalCharacterLocalConditionScopedTopologyAndModuleData20261019
-- name    : MazurTransfer_Order13OriginalCharacterLocalConditionScopedTopologyAndModuleData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T12:04:26.968406+00:00
-- url     : https://prove2.me/theorems/176ec657-9030-4591-916d-30b1344868a9
-- title:
--   Original norm-character local-condition topology and modules
-- statement:
--   Retain the original discrete topology, field automorphism actions, norm kernel and continuous cohomology modules for the same actual norm maps and character intertwiners. Every original full type and whole nonproof constructor value is checked. Named downstream consumer: norm-character inertia restrictions and the previously selected ordered character Selmer maps.
-- source:
--   MazurTheorem original mixed single-section parameter algebras and reciprocal recovery, by Vas and contributors; exact official Anthropic FLT quotient/base-change bridge at pin 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0. Original per-file attribution retained.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: preserve original scoped topology, group actions and modules for the same chosen actual norm and character maps. All substantial ramification proofs belong to separate theorem submissions.
Named downstream consumer: actual all-prime character local conditions and selected-character Selmer bounds.
-/
import Definitions.Def_MazurTransfer_Order13OriginalAllPrimeNormKummerTopologyAndInertiaNormalClosureData20261019
import Definitions.Def_MazurTransfer_Order13ActualNormCharacterKummerKernelControlData
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: preserve the EXISTING fixed norm-character Kummer map
and prove zero valuation-inertia restriction at TWO and every prime away
from thirteen and nineteen. No injectivity of coefficient pushforward
and no splitting of the actual character extensions is assumed.
Named downstream consumer: ordered actual character Selmer images and
exceptional local conditions at thirteen and nineteen.
-/

noncomputable section
namespace MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualNormCharacterDyadicKummerConditions : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualNormCharacterDyadicKummerConditions : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualNormCharacterDyadicKummerConditions : IsMonHom schemePi := schemePi_isMonHom
local instance instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualNormCharacterDyadicKummerConditions : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
abbrev pointsTopology : TopologicalSpace (Points K) := ⊥
local instance instTopologicalSpacePoints_order13ActualNormCharacterDyadicKummerConditions : TopologicalSpace (Points K) := pointsTopology K
local instance instDiscreteTopologyPoints_order13ActualNormCharacterDyadicKummerConditions : DiscreteTopology (Points K) := ⟨rfl⟩
local instance instMulActionAlgEquivRatPoints_order13ActualNormCharacterDyadicKummerConditions : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  Order13DyadicMixedUnramifiedKummer.instMulActionAlgEquivRatPoints_order13DyadicMixedUnramifiedKummer K
local instance instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualNormCharacterDyadicKummerConditions : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ



open Order13ActualNormKernelF19Representation Order13ActualNormKernelFiniteModule
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormContinuousCocycles
open Order13ActualPicardNormSubgroupRestriction Order13ActualPicardNormSubgroupRestrictionF19
open RepresentationDiscreteCoefficients ContinuousCoefficientExponentAndContinuity
variable [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
local instance instModuleZModOfNatNatAdditiveSubtypePointsMemSubgroupKernel_order13ActualNormCharacterDyadicKummerConditions : Module (ZMod 19) (Additive (Kernel K φ)) := kernelZModModule K φ
local instance instModuleZModOfNatNatContinuousH1_order13ActualNormCharacterDyadicKummerConditions : Module (ZMod 19) (ContinuousH1 K φ) := globalH1ZModModule K φ
local instance instContinuousSMulAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualNormCharacterDyadicKummerConditions : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) := kernel_continuousSMul K φ
variable {V : Type} [AddCommGroup V] [Module (ZMod 19) V]
variable (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V)
variable (f : Representation.IntertwiningMap (kernelRepresentation K φ) τ)
local instance instModuleZModOfNatNatH1AlgEquivRatCoefficient_order13ActualNormCharacterDyadicKummerConditions : Module (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient τ)) :=
  coefficientH1ZModModule τ

open Order13ActualPicardNormContinuousKummerInjection
open Order13ActualPicardNormAlgebraicKummerInjection
open Order13ActualNormCharacterContinuousH1
variable (hsurj : Function.Surjective (normHom K φ))

open Order13ActualNormCharacterKummerUnramified

variable (hφ : φ = schemePi ∨ φ = schemePiConjugate)
include hφ





variable (q : ℕ) [Fact q.Prime] (h13 : q ≠ 13) (h19 : q ≠ 19)
include h13 h19





end MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions

end
#print axioms MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualNormCharacterDyadicKummerConditions
#print axioms MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualNormCharacterDyadicKummerConditions
#print axioms MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualNormCharacterDyadicKummerConditions
#print axioms MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualNormCharacterDyadicKummerConditions
#print axioms MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instTopologicalSpacePoints_order13ActualNormCharacterDyadicKummerConditions
#print axioms MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instDiscreteTopologyPoints_order13ActualNormCharacterDyadicKummerConditions
#print axioms MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instMulActionAlgEquivRatPoints_order13ActualNormCharacterDyadicKummerConditions
#print axioms MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualNormCharacterDyadicKummerConditions
#print axioms MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instModuleZModOfNatNatAdditiveSubtypePointsMemSubgroupKernel_order13ActualNormCharacterDyadicKummerConditions
#print axioms MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instModuleZModOfNatNatContinuousH1_order13ActualNormCharacterDyadicKummerConditions
#print axioms MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instContinuousSMulAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualNormCharacterDyadicKummerConditions
#print axioms MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instModuleZModOfNatNatH1AlgEquivRatCoefficient_order13ActualNormCharacterDyadicKummerConditions
#print axioms MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.pointsTopology


