-- Prove2me | Definitions.Def_Q146C005
-- name    : Q146C005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T05:08:16.118722+00:00
-- url     : https://prove2.me/theorems/43ea5a28-2d50-46a3-b60e-cb221b0f6382
-- title:
--   Definitions bundle Q146C005 of the split of OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 312 declarations of OpenAI's Lean: 131 definitions, 4 inductive types or structures, 2 instances and 175 theorems. The definitions and types are `OAI.CircleDomainRigidity.FiniteTransfer.arcStartingAngleLaw`, `OAI.CircleDomainRigidity.FiniteTransfer.closedTerminalImages`, `OAI.CircleDomainRigidity.FiniteTransfer.completionCore`, `OAI.CircleDomainRigidity.FiniteTransfer.markedNeighborhoods`, `OAI.CircleDomainRigidity.FiniteTransfer.terminalRemainder`, `OAI.CircleDomainRigidity.InnerRationalInterval`, `OAI.CircleDomainRigidity.IsAnalyticJordanCap`, `OAI.CircleDomainRigidity.KoebeCircleDomainConjecture`, `OAI.CircleDomainRigidity.MatchedConformalEnds.realPlaneDomain`, `OAI.CircleDomainRigidity.NormalSidePattern`, `OAI.CircleDomainRigidity.OpenPlanePartition`, `OAI.CircleDomainRigidity.OpenPlanePartition.adjustedCircleMix`, `OAI.CircleDomainRigidity.OpenPlanePartition.circleMix`, `OAI.CircleDomainRigidity.OpenPlanePartition.mix`, `OAI.CircleDomainRigidity.PhysicalFieldCoareaIdentity`, `OAI.CircleDomainRigidity.PhysicalWeightedCoareaIdentity`, `OAI.CircleDomainRigidity.PlanarSobolevCoarea`, `OAI.CircleDomainRigidity.PlaneLocalWeakComplex.imagWitness`, `OAI.CircleDomainRigidity.PlaneLocalWeakComplex.realWitness`, `OAI.CircleDomainRigidity.PositivePathTime`, `OAI.CircleDomainRigidity.PrincipalRealBeltrami`, `OAI.CircleDomainRigidity.RegularJordanParametrization`, `OAI.CircleDomainRigidity.ScalarSmoothWeakLimit`, `OAI.CircleDomainRigidity.SeparatedTimes`, `OAI.CircleDomainRigidity.SignedTestFamily`, `OAI.CircleDomainRigidity.SmoothPhysicalDiskCover`, `OAI.CircleDomainRigidity.UnitDiskCrosscutSeparation`, `OAI.CircleDomainRigidity.UnorientedFiniteCircleGreenFormula`, `OAI.CircleDomainRigidity.activeTagSlot`, `OAI.CircleDomainRigidity.affineSobolevWitness`, `OAI.CircleDomainRigidity.assembleTags`, `OAI.CircleDomainRigidity.axialBandIncrement`, `OAI.CircleDomainRigidity.axialCircleFlux`, `OAI.CircleDomainRigidity.axialCircleIncrement`, `OAI.CircleDomainRigidity.borelSobolevWitness`, `OAI.CircleDomainRigidity.boundaryCurveTrace`, `OAI.CircleDomainRigidity.boundaryPaste`, `OAI.CircleDomainRigidity.boundaryTimeMeasure`, `OAI.CircleDomainRigidity.boundedCompactCutoffWitness`, `OAI.CircleDomainRigidity.centeredArcLaw` and 95 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `CircleDomains_Modulus_CountableConcatenationLength`, `CircleDomains_Modulus_FixedCapacityCutoffs`, `CircleDomains_Modulus_PathLengthKernel`, `CircleDomains_Modulus_RegularJordanNormalSides`, `CircleDomains_Modulus_ResidualIncidence`, `CircleDomains_Modulus_ReversedArclength`, `CircleDomains_Modulus_ReversedPhysicalLength`, `CircleDomains_Modulus_SphericalChartCost`, `CircleDomains_Probability_CenteredArcLaw`, `CircleDomains_Probability_CollarTimeMeasures`, `CircleDomains_Probability_ExactBandMeasure`, `CircleDomains_Probability_HorizontalNullPair`, `CircleDomains_Probability_LastEntryCircleLaw`, `CircleDomains_Probability_LastEntryLaw`, `CircleDomains_Probability_PathHitLaws`, `CircleDomains_Probability_PathIntersectionMeasure`, `CircleDomains_Probability_PhysicalImageOccupation`, `CircleDomains_Probability_RecursiveLawLevelEstimates`, `CircleDomains_Probability_SelectableMeanLaw`, `CircleDomains_Probability_SimpleArcMeasurability`, `CircleDomains_Probability_SphericalSliceDensity`, `CircleDomains_Probability_TagPaymentMeasure`, `CircleDomains_Probability_TagTupleMeasure`, `CircleDomains_Reflection_AnalyticJordanCap`, `CircleDomains_Reflection_AnalyticReflectionData`, `CircleDomains_Reflection_AnalyticStraighteningHolomorphic`, `CircleDomains_Reflection_PrincipalReflectionDefect`, `CircleDomains_Reflection_ReflectionPrincipalSolution`, `CircleDomains_Reflection_RoundReflectionCoefficient`, `CircleDomains_Rigidity_ActualAxialCircleFlux`, `CircleDomains_Rigidity_ActualEnclosedCircleSlice`, `CircleDomains_Rigidity_AxialBandFlux`, `CircleDomains_Rigidity_AxialCircleFlux`, `CircleDomains_Rigidity_AxialCommonPointTrace`, `CircleDomains_Rigidity_ConditionalNormalizedRigidity`, `CircleDomains_Rigidity_ConditionalRigidity`, `CircleDomains_Rigidity_ConductivityCoefficient`, `CircleDomains_Rigidity_FiniteMatchedField`, `CircleDomains_Rigidity_MaskedLevelData`, `CircleDomains_Rigidity_MatchedRealMaskSobolev`, `CircleDomains_Rigidity_PrincipalPhysicalWitness`, `CircleDomains_Rigidity_PrincipalRealBeltrami`, `CircleDomains_Rigidity_RankedCodeTraces`, `CircleDomains_Rigidity_SamplingTraceContinuity`, `CircleDomains_Rigidity_SignedTraceTruncationWeak`, `CircleDomains_Rigidity_ZeroTraceEnergy`, `CircleDomains_Rigidity_ZeroTraceExtension`, `CircleDomains_Selection_AtomicHitTests`, `CircleDomains_Selection_CodeConstraints`, `CircleDomains_Selection_CodePeriodGenericLevels`, `CircleDomains_Selection_CodeResidualAvoidance`, `CircleDomains_Selection_CountableTagAssembly`, `CircleDomains_Selection_FirstExitCuts`, `CircleDomains_Selection_LastEntryCuts`, `CircleDomains_Selection_LocalHeightDifference`, `CircleDomains_Selection_MeanMarkedBranchBands`, `CircleDomains_Selection_OrderedHoleIntegration`, `CircleDomains_Selection_OrderedProtrusionAvailability`, `CircleDomains_Selection_PhysicalSubpaths`, `CircleDomains_Selection_PreterminalTolls`, `CircleDomains_Selection_ProtrusionAlternatives`, `CircleDomains_Selection_ProtrusionTestAvailability`, `CircleDomains_Selection_RebasedLevelPresentations`, `CircleDomains_Selection_RecursiveMeanCompatibility`, `CircleDomains_Selection_RescaledBandWitness`, `CircleDomains_Selection_ResidualVisits`, `CircleDomains_Selection_ReversedTags`, `CircleDomains_Selection_SelectableRecursiveMean`, `CircleDomains_Selection_SelectedCoordinateTest`, `CircleDomains_Selection_SelectedLevelPresentation`, `CircleDomains_Selection_SelectedMarkedEndEquality`, `CircleDomains_Selection_SignedScalarTests`, `CircleDomains_Selection_SignedTestFamily`, `CircleDomains_Selection_SparseBaseCodes`, `CircleDomains_Selection_SparseTags`, `CircleDomains_Selection_TagDelay`, `CircleDomains_Selection_TerminalRemainder`, `CircleDomains_Selection_VisitCounts`, `CircleDomains_Sobolev_AffineLpTransport`, `CircleDomains_Sobolev_AffineSobolevWitness`, `CircleDomains_Sobolev_BorelSobolevGradient`, `CircleDomains_Sobolev_BoundedSobolevChain`, `CircleDomains_Sobolev_CirclePartitionSmoothing`, `CircleDomains_Sobolev_CompactWeakExtension`, `CircleDomains_Sobolev_ComplementWeakGradient`, `CircleDomains_Sobolev_ComplexLocalScalarWitness`, `CircleDomains_Sobolev_ComplexLocalSobolevTransport`, `CircleDomains_Sobolev_ComplexSobolevTransport`, `CircleDomains_Sobolev_ComplexWeakDirectionalTransport`, `CircleDomains_Sobolev_LipschitzArclengthBounds`, `CircleDomains_Sobolev_LipschitzMappedArclength`, `CircleDomains_Sobolev_LocalBoundedSobolevChain`, `CircleDomains_Sobolev_LocalComplexWitness`, `CircleDomains_Sobolev_LocalDensityIntegrability`, `CircleDomains_Sobolev_LocalSmoothPartition`, `CircleDomains_Sobolev_LocalizedSobolevRange`, `CircleDomains_Sobolev_LocallySobolevPartials`, `CircleDomains_Sobolev_MollificationEnergy`, `CircleDomains_Sobolev_PartitionErrorSum`, `CircleDomains_Sobolev_PartitionLiftErrorSum`, `CircleDomains_Sobolev_PartitionMixing`, `CircleDomains_Sobolev_PhysicalCauchyRiemann`, `CircleDomains_Sobolev_PhysicalCoareaCoordinates`, `CircleDomains_Sobolev_PhysicalCoordinateLines`, `CircleDomains_Sobolev_PhysicalFieldCoarea`, `CircleDomains_Sobolev_PhysicalLipschitzCoarea`, `CircleDomains_Sobolev_PhysicalRoundIntegrals`, `CircleDomains_Sobolev_PhysicalSamplingPartition`, `CircleDomains_Sobolev_PositiveSobolevApproximation`, `CircleDomains_Sobolev_PotentialRectangleACL`, `CircleDomains_Sobolev_PrincipalScalarWeakLimit`, `CircleDomains_Sobolev_RealGradientNorm`, `CircleDomains_Sobolev_RealGradientTransport`, `CircleDomains_Sobolev_ScalarEnergyMeasure`, `CircleDomains_Sobolev_ScalarFlatteningEnergy`, `CircleDomains_Sobolev_ScalarFlatteningWeak`, `CircleDomains_Sobolev_SmoothEnergyLimit`, `CircleDomains_Sobolev_SmoothMeanCodeLevels`, `CircleDomains_Sobolev_SmoothMeanPeriodConsequences`, `CircleDomains_Sobolev_SmoothMeanPhysicalBranches`, `CircleDomains_Sobolev_SmoothPhysicalPullback`, `CircleDomains_Sobolev_SmoothPlaneSobolev`, `CircleDomains_Sobolev_SmoothScalarCutoffWitness`, `CircleDomains_Sobolev_SmoothScalarWeakLimit`, `CircleDomains_Sobolev_SmoothWeakGradient`, `CircleDomains_Sobolev_SobolevEnergyMeasure`, `CircleDomains_Sobolev_SobolevGraphEnergy`, `CircleDomains_Sobolev_SobolevRangeBound`, `CircleDomains_Sobolev_SobolevScalarCoarea`, `CircleDomains_Sobolev_SphericalAreaLocalization`, `CircleDomains_Sobolev_WeakGradientAffineRescale`, `CircleDomains_Sobolev_ZeroWeakGradient`, `CircleDomains_Topology_ActualFiniteDiskSlice`, `CircleDomains_Topology_BoundaryPairNeighborhood`, `CircleDomains_Topology_BoundedCompactCutoff`, `CircleDomains_Topology_BoundedSphereHomotopy`, `CircleDomains_Topology_CenteredBoundary`, `CircleDomains_Topology_CircleMobiusImage`, `CircleDomains_Topology_CirclePartitionBands`, `CircleDomains_Topology_ClosedTimeCounts`, `CircleDomains_Topology_CompactCoordinateTest`, `CircleDomains_Topology_CompactLineJump`, `CircleDomains_Topology_CompactRelationCoordinateTest`, `CircleDomains_Topology_CountableClosedLevelCount`, `CircleDomains_Topology_CountableJordanCollars`, `CircleDomains_Topology_CountablePathConcatenation`, `CircleDomains_Topology_CountablePathTimes`, `CircleDomains_Topology_CrosscutSeparationInput`, `CircleDomains_Topology_DiskLineIntegration`, `CircleDomains_Topology_DomainPhysicalPaths`, `CircleDomains_Topology_EuclideanPlaneCoordinates`, `CircleDomains_Topology_FiniteTerminalDisks`, `CircleDomains_Topology_FullIntervalTag`, `CircleDomains_Topology_GatedQuotientMap`, `CircleDomains_Topology_JoinedPaths`, `CircleDomains_Topology_LastEntryContinua`, `CircleDomains_Topology_MeanArcIndex`, `CircleDomains_Topology_OpenDomainRepresentative`, `CircleDomains_Topology_OpenGapIntegration`, `CircleDomains_Topology_PathEndpoints`, `CircleDomains_Topology_PathGates`, `CircleDomains_Topology_PathImageCount`, `CircleDomains_Topology_PhysicalFrontierCrossings`, `CircleDomains_Topology_PlanarAffineRescale`, `CircleDomains_Topology_PlanarFilledJump`, `CircleDomains_Topology_ProjectedPlaneFunction`, `CircleDomains_Topology_RationalTimeIntervals`, `CircleDomains_Topology_RectifiableSubarcs`, `CircleDomains_Topology_RegularJordanParametrization`, `CircleDomains_Topology_RelativePlateauNeighborhoods`, `CircleDomains_Topology_RetainedCircleModel`, `CircleDomains_Topology_RetainedImageBoundary`, `CircleDomains_Topology_RoundCollarLifts`, `CircleDomains_Topology_SelectedCircleDomain`, `CircleDomains_Topology_SimpleSubarcRelation`, `CircleDomains_Topology_SmallQuotientDisks`, `CircleDomains_Topology_SphereClusterBridge`, `CircleDomains_Topology_SphereCoefficient`, `CircleDomains_Topology_SphereJordanCoordinates`, `CircleDomains_Topology_SphereLocalMapInjective`, `CircleDomains_Topology_TerminalArcSet`, `CircleDomains_Topology_TerminalBoundaryLimits`, `CircleDomains_Topology_UnorientedCircleGreen`, `CircleDomains_Transfer_CompletedChart`, `CircleDomains_Transfer_ComplexHausdorffTransport`, `CircleDomains_Transfer_FilledGapIntegration`, `CircleDomains_Transfer_ResidualImage`, `CircleDomains_Transfer_RetainedScalarEstimates`, `CircleDomains_Transfer_RetainedScalarTails`, `CircleDomains_Transfer_ShrinkingRealModels`, `CircleDomains_Transfer_TransportedTerminalBranches`, `CircleDomains_Transfer_VerticalFilledJump`, `CircleDomains_Uniformization_Conformal`, `CircleDomains_Uniformization_FiniteCompletion`.
--
--   **Imports.** It imports the published bundle `Def_KoebeCircleDomains`; the bundles `Q146C000`, `Q146C001` and `Q146C002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q146C007` and `Q146C008`; the statements `OAI.CircleDomainRigidity.CompactScalarModel.FlattenedSourceSelection.compact_tests`, `OAI.CircleDomainRigidity.PlaneLocalWeakComplex.jacobian_area_limit`, `OAI.CircleDomainRigidity.exteriorCoefficientAreaTheorem`, `OAI.CircleDomainRigidity.exteriorOmittedAreaTheorem`, `OAI.CircleDomainRigidity.planarSobolevCoarea`, `OAI.CircleDomainRigidity.principalRealBeltrami` and `OAI.CircleDomainRigidity.unorientedFiniteCircleGreenFormula`; the proofs of `OAI.CircleDomainRigidity.PlaneLocalWeakComplex.jacobian_area_limit`, `OAI.CircleDomainRigidity.planarSobolevCoarea` and `OAI.CircleDomainRigidity.unorientedFiniteCircleGreenFormula`.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C000
import Definitions.Def_Q146C001
import Definitions.Def_Q146C002

section
-- module Solutions.Q146_CD.Compat
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PathHitLaws
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed path-hit relations and the joint upper semicontinuity of their probabilities.
The time interval is compact, so projection of the closed incidence relation is closed.
Weak convergence and the existing Portmanteau theorem then apply to the product with
the moving point mass. This supplies the actual hit function used in law fusion. -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

section Paths

variable {X : Type*} [MetricSpace X]

theorem isClosed_pathHitSet : IsClosed (pathHitSet (X := X)) := by
  let K : Set ((C(PathTime, X) × X) × PathTime) :=
    {p | p.1.1 p.2 = p.1.2}
  have hK : IsClosed K := isClosed_eq
    (continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
    (continuous_snd.comp continuous_fst)
  have he : Prod.fst '' K = pathHitSet (X := X) := by
    ext p
    constructor
    · rintro ⟨⟨q, t⟩, ht, rfl⟩
      exact ⟨t, ht⟩
    · rintro ⟨t, ht⟩
      exact ⟨(p, t), ht, rfl⟩
  rw [← he]
  exact isClosedMap_fst_of_compactSpace K hK

theorem isClosed_paths_hitting (x : X) :
    IsClosed {γ : C(PathTime, X) | ∃ t : PathTime, γ t = x} :=
  isClosed_pathHitSet.preimage (continuous_id.prodMk continuous_const)

end Paths

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_VisitCounts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite visit witnesses have Borel incidence. The resulting extended count
records visits at distinct parameter times, including both endpoints. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

def separatedTimeSet (n : ℕ) (r : ℝ) : Set (Fin n → PathTime) :=
  {t | ∀ i j, i ≠ j → r ≤ dist (t i) (t j)}

abbrev SeparatedTimes (n : ℕ) (r : ℝ) := separatedTimeSet n r

def separatedVisitSet {X : Type*} [MetricSpace X] (n : ℕ) (r : ℝ) :
    Set (C(PathTime, X) × X) :=
  {q | ∃ t : SeparatedTimes n r, ∀ i, q.1 (t.val i) = q.2}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ClosedTimeCounts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable multiplicity in a closed time relation. This allows visits to
be restricted to a tagged path's residual times and to a closed test interval. -/

open Set Function MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section

namespace CircleDomainRigidity

variable {Z : Type*}

def timeCount (R : Set (Z × PathTime)) (z : Z) : ℝ≥0∞ :=
  ∑' t : PathTime, if (z, t) ∈ R then (1 : ℝ≥0∞) else 0

def timeWitnessSet (R : Set (Z × PathTime)) (n : ℕ) : Set Z :=
  {z | ∃ t : Fin n → PathTime, Injective t ∧ ∀ i, (z, t i) ∈ R}

def separatedTimeWitnessSet (R : Set (Z × PathTime)) (n : ℕ) (r : ℝ) : Set Z :=
  {z | ∃ t : SeparatedTimes n r, ∀ i, (z, t.val i) ∈ R}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ResidualVisits
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual residual visit multiplicities and tolls on closed test intervals. -/

open Set Function MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def residualVisitRelation (B : Set X) (I : Set PathTime) :
    Set ((TaggedPath X × X) × PathTime) :=
  {q | q.2 ∈ residualTimes B q.1.1 ∧ q.2 ∈ I ∧ q.1.1.1 q.2 = q.1.2}

def residualVisitCount (B : Set X) (I : Set PathTime) (Γ : TaggedPath X) (x : X) : ℝ≥0∞ :=
  timeCount (residualVisitRelation B I) (Γ, x)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ResidualIncidence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel residual incidences after finite point deletions. Compact time
projection proves these directly, including the prior-path and level tests. -/

open Set Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [TopologicalSpace Y]

def separatedResidualIncidence (B : Set X) (I : Set PathTime)
    (R : Set (Y × X)) (P : Set X) (r : ℝ) : Set (TaggedPath X × Y) :=
  {q | ∃ t ∈ residualTimes B q.1, t ∈ I ∧ (q.2, q.1.1 t) ∈ R ∧
    ∀ p ∈ P, r ≤ dist (q.1.1 t) p}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ResidualImage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact residual images and their Borel incidence masses. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def residualImageGraph (B : Set X) : Set (TaggedPath X × X) :=
  {q | q.2 ∈ residualImage B q.1}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RationalTimeIntervals
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every open time interval is the directed union of the rational closed
intervals contained in it. This passes the coded constraints to open pieces. -/

open Set

noncomputable section

namespace CircleDomainRigidity

def InnerRationalInterval (a b : PathTime) :=
  {p : RationalPathTime × RationalPathTime | a < p.1.toTime ∧ p.2.toTime < b}

def innerRationalInterval (a b : PathTime) (p : InnerRationalInterval a b) : Set PathTime :=
  Icc p.val.1.toTime p.val.2.toTime

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CountablePathTimes
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
attribute [-simp] _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Decreasing dyadic intervals for the countable collar concatenation. -/

open Set Function Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

def collarTime (n : ℕ) : PathTime :=
  ⟨(1 / 2 : ℝ) ^ n, pow_nonneg (by norm_num) n, pow_le_one₀ (by norm_num) (by norm_num)⟩

theorem collarTime_pos (n : ℕ) : (⊥ : PathTime) < collarTime n := by
  change (0 : ℝ) < (1 / 2 : ℝ) ^ n
  positivity

theorem collarTime_zero : collarTime 0 = ⊤ := by
  apply Subtype.ext
  simp [collarTime]

theorem collarTime_strictAnti : StrictAnti collarTime := by
  apply strictAnti_nat_of_succ_lt
  intro n
  change (1 / 2 : ℝ) ^ (n + 1) < (1 / 2 : ℝ) ^ n
  rw [pow_succ]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]

theorem collarTime_tendsto : Tendsto collarTime atTop (𝓝 (⊥ : PathTime)) := by
  apply tendsto_subtype_rng.mpr
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem exists_collarTime_cell {t : PathTime} (ht : ⊥ < t) :
    ∃ n, collarTime (n + 1) < t ∧ t ≤ collarTime n := by
  obtain ⟨n, hn⟩ := exists_nat_pow_near_of_lt_one
    (show (0 : ℝ) < t from ht) t.property.2
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  exact ⟨n, hn⟩

def collarCell (n : ℕ) : Set PathTime := Icc (collarTime (n + 1)) (collarTime n)

abbrev PositivePathTime := {t : PathTime // ⊥ < t}

theorem collarCells_locallyFinite :
    LocallyFinite (fun n => (Subtype.val : PositivePathTime → PathTime) ⁻¹' collarCell n) := by
  intro t
  have hevent : ∀ᶠ n in atTop, collarTime n < t.val :=
    collarTime_tendsto.eventually (gt_mem_nhds t.property)
  obtain ⟨N, hN⟩ := hevent.exists
  refine ⟨{s | collarTime N < (s : PathTime)}, ?_, ?_⟩
  · exact (isOpen_lt continuous_const continuous_subtype_val).mem_nhds hN
  · apply (Set.finite_lt_nat N).subset
    rintro n ⟨s, hs, hsn⟩
    change collarTime N < s.val at hsn
    by_contra hn
    have hle := collarTime_strictAnti.antitone (Nat.le_of_not_gt hn)
    exact (hsn.trans_le hs.2).not_ge hle

theorem collarCells_cover_positive :
    (⋃ n, (Subtype.val : PositivePathTime → PathTime) ⁻¹' collarCell n) = univ := by
  apply eq_univ_of_forall
  intro t
  obtain ⟨n, hlow, hhigh⟩ := exists_collarTime_cell t.property
  exact mem_iUnion.mpr ⟨n, hlow.le, hhigh⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CountablePathConcatenation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual countable path concatenation, including the new limiting endpoint.
The shrinking-tail hypothesis is the one supplied by nested dust collars. -/

open Set Function Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X]

def collarPieceIndex (t : PathTime) : ℕ :=
  if h : ⊥ < t then Classical.choose (exists_collarTime_cell h) else 0

theorem collarPieceIndex_spec {t : PathTime} (ht : ⊥ < t) :
    collarTime (collarPieceIndex t + 1) < t ∧ t ≤ collarTime (collarPieceIndex t) := by
  simp only [collarPieceIndex, dite_eq_left ht]
  exact Classical.choose_spec (exists_collarTime_cell ht)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CountableConcatenationLength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
attribute [-simp] _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact arclength addition over the decreasing collar intervals. This is
 an extended-real identity and therefore does not assume rectifiability. -/

open Set Function Filter
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem collar_variation_partial (γ : PathTime → X) (N : ℕ) :
    (∑ n ∈ Finset.range N, eVariationOn γ (collarCell n)) =
      eVariationOn γ (Icc (collarTime N) ⊤) := by
  induction N with
  | zero => simp [collarTime_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, add_comm]
    have he := eVariationOn.Icc_add_Icc γ (s := univ)
      (collarTime_strictAnti (Nat.lt_succ_self N)).le (le_top : collarTime N ≤ ⊤)
      (mem_univ (collarTime N))
    simpa only [univ_inter, collarCell] using he

theorem collar_variation_sum (γ : C(PathTime, X)) :
    eVariationOn γ univ = ∑' n, eVariationOn γ (collarCell n) := by
  apply le_antisymm
  · have he := eVariationOn.eVariationOn_Ioc_eq_Icc_of_continuousWithinAt
      (γ.continuous.continuousAt (x := (⊥ : PathTime))).continuousWithinAt
      (b := (⊤ : PathTime))
    rw [Icc_bot_top] at he
    rw [← he, eVariationOn]
    apply iSup_le
    rintro ⟨k, u, hu, hmem⟩
    obtain ⟨N, hN⟩ := (collarTime_tendsto.eventually (gt_mem_nhds (hmem 0).1)).exists
    have hall : ∀ i, u i ∈ Icc (collarTime N) ⊤ := by
      intro i
      exact ⟨hN.le.trans (hu (Nat.zero_le i)), le_top⟩
    exact (eVariationOn.sum_le hu hall).trans
      ((collar_variation_partial γ N).symm.le.trans (ENNReal.sum_le_tsum _))
  · rw [ENNReal.tsum_eq_iSup_nat]
    apply iSup_le
    intro N
    rw [collar_variation_partial]
    exact eVariationOn.mono γ (subset_univ _)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_EuclideanPlaneCoordinates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The area-preserving linear coordinates connecting the physical plane
with the Euclidean-space Sobolev library. -/

open Set MeasureTheory

noncomputable section

namespace CircleDomainRigidity

theorem euclideanPlaneCoordinates_measurePreserving :
    MeasurePreserving euclideanPlaneCoordinates volume volume := by
  change MeasurePreserving ((MeasurableEquiv.finTwoArrow :
    (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ)) ∘ WithLp.ofLp) volume volume
  exact (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))

theorem euclideanPlaneCoordinates_symm_measurePreserving :
    MeasurePreserving euclideanPlaneCoordinates.symm volume volume := by
  exact euclideanPlaneCoordinates_measurePreserving.symm
    euclideanPlaneCoordinates.toHomeomorph.toMeasurableEquiv

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_FixedCapacityCutoffs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed smooth cutoffs for the scalar graph-capacity argument. Their
bounds are independent of the function, graph point, and chosen scale. -/
open Set Function MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def spatialCapacityBump : ContDiffBump (0 : EuclideanPlane) := ⟨2,4,by norm_num,by norm_num⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PathLengthKernel
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The arclength measures form a Borel kernel on rectifiable paths. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

instance instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel (γ : RectifiablePath X) : IsFiniteMeasure (pathLengthKernel γ) := by
  change IsFiniteMeasure (pathLengthMeasure γ)
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RegularJordanParametrization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regular Jordan circuits with either orientation. The absolute Stokes
estimate does not need a choice of orientation. -/

open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

structure RegularJordanParametrization (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) γ
  periodic : Function.Periodic γ 1
  injective : InjOn γ (Ico 0 1)
  regular : ∀ t, deriv γ t ≠ 0
  boundary : γ '' Icc 0 1 = frontier (jordanInterior H)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RegularJordanNormalSides
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform local rectangles of the actual normal strip have one inward
and one outward half; no orientation is assumed. -/
open Set Function Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

def NormalSidePattern (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (t r : ℝ) (positive : Bool) : Prop :=
  ∀ s ∈ Ioo (t-r) (t+r), ∀ ρ ∈ Ioo (0 : ℝ) r,
    if positive then
      curveNormalStrip γ (s,ρ) ∈ jordanInterior H ∧
        curveNormalStrip γ (s,-ρ) ∈ (closure (jordanInterior H))ᶜ
    else
      curveNormalStrip γ (s,-ρ) ∈ jordanInterior H ∧
        curveNormalStrip γ (s,ρ) ∈ (closure (jordanInterior H))ᶜ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PathEndpoints
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel endpoint and first-arrival restrictions for the base path codes. -/

open Set Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def earlyHitSet (b : X) (n : ℕ) : Set C(PathTime, X) :=
  {γ | ∃ t : PathTime, (t : ℝ) ≤ 1 - 1 / ((n : ℝ) + 1) ∧ γ t = b}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PhysicalSubpaths
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual physical lifts of quotient paths on a compact time interval.
The quotient is inverted only where it is a homeomorphism. Constant extension
at the interval ends gives an ordinary continuous physical path. -/

open Set MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem physicalSubpath_mem {G : Set Y} {U : Set X} (e : G ≃ₜ U)
    {a b : PathTime} (hab : a ≤ b) (γ : pathsInsideOn U a b) (t : PathTime) :
    physicalSubpath e hab γ t ∈ G :=
  (e.symm _).property

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_TagTupleMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted tag-tuple measures. Tuple components retain the label list;
slot weights depend only on the slot number and have finite total mass. -/

open Set MeasureTheory TopologicalSpace Topology
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

def activeTagSlot (q : TagData) : TagSlot := Sum.inr q

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PathGates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countably many closed collar gates give Borel restrictions on path codes. -/

open Set Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def separatedGateViolation (C K : Set X) (r : ℝ) : Set C(PathTime, X) :=
  {γ | ∃ t : PathTime, γ t ∈ C ∧ ∀ p ∈ K, r ≤ dist (γ t) p}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TagDelay
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moving the same tags to later slots preserves the actual residual times
and all admissibility rules. The tuple measure decreases geometrically. -/

open Set Function MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem inactiveTag_rules (H : ℕ → Set (UnitAddCircle × X))
    (T : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (γ : C(PathTime, X)) :
    (γ, inactiveTag) ∈ validTagShape ∧ (γ, inactiveTag) ∈ tagContainment H ∧
      inactiveTag ∉ tagTupleExcluded T := by
  refine ⟨Or.inl ⟨(), rfl⟩, ?_, ?_⟩
  · intro t hleft _
    exact False.elim (not_lt_of_ge le_top hleft)
  · intro h
    obtain ⟨n, hn⟩ := mem_iUnion.mp h
    obtain ⟨l, hl⟩ := mem_iUnion.mp hn
    obtain ⟨p, _, heq⟩ := hl
    cases heq

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ReversedTags
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reversal of a tagged path retains every level tuple and reverses its
open time interval. Residual times and images are transported exactly. -/

open Set Function
open scoped Classical

noncomputable section

namespace CircleDomainRigidity

def reversedTag : TagSlot → TagSlot
  | Sum.inl u => Sum.inl u
  | Sum.inr q => Sum.inr ⟨q.1, q.2.1, q.2.2.1,
      unitInterval.symm q.2.2.2.2, unitInterval.symm q.2.2.2.1⟩

variable {X : Type*} [MetricSpace X]

def reversedPath (γ : C(PathTime, X)) : C(PathTime, X) :=
  γ.comp ⟨unitInterval.symm, unitInterval.continuous_symm⟩

def reversedTaggedPath (Γ : TaggedPath X) : TaggedPath X :=
  (reversedPath Γ.1, fun k => reversedTag (Γ.2 k))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ReversedPhysicalLength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reversing time preserves the actual physical-domain length. Dyadic
cells are matched with their reversed indices before summing. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

theorem symm_timeClip {a b : PathTime} (hab : a ≤ b) (t : PathTime) :
    unitInterval.symm (timeClip a b t) =
      timeClip (unitInterval.symm b) (unitInterval.symm a) (unitInterval.symm t) := by
  change unitInterval.symm (max a (min b t)) =
    max (unitInterval.symm b) (min (unitInterval.symm a) (unitInterval.symm t))
  rw [unitInterval.strictAnti_symm.antitone.map_max,
    unitInterval.strictAnti_symm.antitone.map_min, min_max_distrib_left,
    min_eq_right (unitInterval.symm_le_symm.mpr hab)]

theorem symm_dyadicLeft (n : ℕ) (i : Fin (2 ^ n)) :
    unitInterval.symm (dyadicLeft n i) = dyadicRight n i.rev := by
  have hs : i.val + (i.rev.val + 1) = 2 ^ n := by
    rw [Fin.val_rev]
    omega
  have hr : (i.val : ℝ) + ((i.rev.val + 1 : ℕ) : ℝ) = (2 : ℝ) ^ n := by
    exact_mod_cast hs
  apply Subtype.ext
  change 1 - (i.val : ℝ) / (2 : ℝ) ^ n = ((i.rev.val + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n
  field_simp
  linarith

theorem symm_dyadicRight (n : ℕ) (i : Fin (2 ^ n)) :
    unitInterval.symm (dyadicRight n i) = dyadicLeft n i.rev := by
  have h := congrArg unitInterval.symm (symm_dyadicLeft n i.rev)
  simpa only [Fin.rev_rev, unitInterval.symm_symm] using h.symm

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}

theorem pathsInsideOn_reversed_iff (γ : C(PathTime, X)) (a b : PathTime) :
    reversedPath γ ∈ pathsInsideOn U a b ↔
      γ ∈ pathsInsideOn U (unitInterval.symm b) (unitInterval.symm a) := by
  constructor
  · intro h t ht
    have hs : unitInterval.symm t ∈ Icc a b :=
      ⟨unitInterval.le_symm_comm.mpr ht.2, unitInterval.symm_le_comm.mpr ht.1⟩
    simpa only [reversedPath, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      unitInterval.symm_symm] using h hs
  · intro h t ht
    exact h ⟨unitInterval.symm_le_symm.mpr ht.2, unitInterval.symm_le_symm.mpr ht.1⟩

theorem variation_reversedPath {Z : Type*} [MetricSpace Z] (γ : C(PathTime, Z)) :
    eVariationOn (reversedPath γ) univ = eVariationOn γ univ := by
  change eVariationOn (γ ∘ unitInterval.symm) univ = _
  rw [eVariationOn.comp_eq_of_antitoneOn γ unitInterval.symm
    (unitInterval.strictAnti_symm.antitone.antitoneOn _), image_univ,
    unitInterval.symm_bijective.surjective.range_eq]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ReversedArclength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reversing an ordinary rectifiable arc preserves its full occupation
measure, hence every measurable weighted arclength. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def reversedRectifiablePath (γ : RectifiablePath X) : RectifiablePath X :=
  ⟨reversedPath γ.val, by
    change eVariationOn (reversedPath γ.val) univ ≠ ∞
    rw [variation_reversedPath]
    exact γ.property⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FirstExitCuts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual first-exit cuts for the collar-splicing construction. Every
retained initial fragment lies in the corresponding closed collar disk. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X]

def firstExitTime (γ : C(PathTime, X)) (V : Set X) : PathTime :=
  sInf {t | γ t ∉ V}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LastEntryCuts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Last-entry collar cuts and the strict separation of the retained
middle fragment from the two endpoint tails. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def lastEntryTime (γ : C(PathTime, X)) (V : Set X) : PathTime :=
  unitInterval.symm (firstExitTime (reversedPath γ) V)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RectifiableSubarcs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual short rectifiable arcs between nearby parameters of a
finite-cost curve, with either orientation. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def constantRectifiablePath (x : X) : RectifiablePath X :=
  ⟨ContinuousMap.const PathTime x, by
    change eVariationOn _ _ ≠ ∞
    have hz : eVariationOn (ContinuousMap.const PathTime x) univ = 0 :=
      (eVariationOn.eq_zero_iff _).mpr fun _ _ _ _ => edist_self _
    rw [hz]
    exact ENNReal.zero_ne_top⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PhysicalImageOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! General physical paths pay for the Hausdorff measure of their images.
Together with the opposite simple-arc bound this makes erasing loops decrease
physical occupation, including for arbitrary measurable densities. -/

open Set Function MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

def physicalStageImage (e : G ≃ₜ U) (y₀ : Y) (γ : C(PathTime, X)) (n : ℕ) : Set Y :=
  ⋃ i : Fin (2 ^ n), if γ ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)
    then (physicalValue e y₀ ∘ γ) '' Icc (dyadicLeft n i) (dyadicRight n i) else ∅

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PathImageCount
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct image intersections with a closed set. Finite separated
image witnesses make this count Borel without counting repeated visits. -/

open Set Function MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def pathImageCount (H : Set X) (γ : C(PathTime, X)) : ℝ≥0∞ :=
  ∑' x : X, if x ∈ range γ ∩ H then (1 : ℝ≥0∞) else 0

def imageHitAtLeast (H : Set X) (n : ℕ) : Set C(PathTime, X) :=
  {γ | ∃ t : Fin n → PathTime, Injective (γ ∘ t) ∧ ∀ i, γ (t i) ∈ H}

def separatedImageHits (H : Set X) (n : ℕ) (r : ℝ) : Set C(PathTime, X) :=
  {γ | ∃ t : Fin n → PathTime,
    (∀ i j, i ≠ j → r ≤ dist (γ (t i)) (γ (t j))) ∧ ∀ i, γ (t i) ∈ H}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_LastEntryLaw
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual last-entry location law is atomless when the paths avoid
each fixed point of the collar boundary. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

open scoped Classical in
noncomputable def lastEntryLaw (μ : ProbabilityMeasure C(PathTime, X)) (V : Set X) : ProbabilityMeasure X :=
  if h : AEMeasurable (fun γ : C(PathTime, X) => γ (lastEntryTime γ V)) (μ : Measure C(PathTime, X)) then
    μ.map h
  else
    μ.map (f := fun γ : C(PathTime, X) => γ ⊥) (continuous_eval_const ⊥).measurable.aemeasurable

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_Conformal
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Sphere conformality and circle-domain statements

The concrete Riemann-sphere charts define conformal equivalences,
round disks, and conformal removability. The two circle-domain statements
express unrestricted uniformization and rigidity under removability.
-/

noncomputable section

open Set
open scoped OnePoint

namespace CircleDomainRigidity

/-- Paper 047-02, Introduction, `thm:main`: unrestricted Koebe uniformization. -/
def KoebeCircleDomainConjecture : Prop :=
  ∀ U : Set Sphere, IsOpen U → IsConnected U →
    ∃ (V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain V ∧ IsConformalEquivalence f U V

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_SimpleArcMeasurability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel simple-path and image-containment relations for the measurable
terminal-arc selection used in the stream construction. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def pathsWithSeparatedCollision (r : ℝ) : Set C(PathTime, X) :=
  {γ | ∃ s t : PathTime, r ≤ dist s t ∧ γ s = γ t}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SimpleSubarcRelation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Borel relation used to select simple subarcs, including
the endpoint equalities and containment in the original path image. -/

open Set Function MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def simpleSubarcRelation : Set (C(PathTime, X) × C(PathTime, X)) :=
  {p | Injective p.2 ∧ p.2 ⊥ = p.1 ⊥ ∧ p.2 ⊤ = p.1 ⊤ ∧ range p.2 ⊆ range p.1}

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_LastEntryContinua
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The last-entry tails are actual compact connected sets. Their only point
outside the open collar is their initial boundary point. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def lastEntryTail (γ : C(PathTime, X)) (V : Set X) : Set X :=
  γ '' Ici (lastEntryTime γ V)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_TerminalArcSet
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The endpoint and interior conditions of the compact arc reduction form
a Borel set. Consequently a full law of these arcs has a compact core. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_4 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphericalAreaLocalization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local planar square integrability from spherical area. Spherical area
is written in its finite stereographic chart, with density 4/(1+|z|²)². -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_1 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleMobiusImage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Circle domains under the normalizing Möbius maps

Round complementary disks transform by multiplication of their defining
matrices. A homeomorphic Möbius map therefore preserves circle domains.
The explicit normalizer sends any prescribed sphere point to infinity.
-/

open Set Function
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity

def pointToInfinityMobius (p : Sphere) : Mobius :=
  p.elim 1 (fun z => inversionMobius * affineMobius 1 (-z) one_ne_zero)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_SphericalSliceDensity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical occupation density gives a square-integrable planar
slice density in every finite inverse-chart neighborhood. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal Classical

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_6 : BorelSpace Sphere := ⟨rfl⟩

 def sliceChartDensity (B : ℝ≥0) (g : Sphere → ℝ≥0∞) (z : ℂ) : ℝ≥0∞ :=
  (B : ℝ≥0∞) * ENNReal.ofReal (sphericalAreaDensity z) * g (z : Sphere)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_SphericalChartCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square-integrable planar derivatives give the finite spherical
weights used by each local tag payment measure. The inverse chart is
Borel, including its arbitrary value at infinity. -/

open Set Function MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_7 : BorelSpace Sphere := ⟨rfl⟩

def localizedSphericalChartWeight (L : ℝ≥0) (A : Set ℂ) (k : ℂ → ℝ≥0∞) : Sphere → ℝ≥0∞ :=
  fun y => (L : ℝ≥0∞) * (((↑) : ℂ → Sphere) '' A).indicator (fun y => k (finiteCoord y)) y

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SmallQuotientDisks
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth physical disks from the component quotient

These statements combine compact clopen isolation, actual contour selection,
the component quotient, and the infinity-chart argument. Connectedness and
unboundedness of the physical exterior are conclusions of the preceding
lemmas, not additional disk-selection hypotheses.
-/

open Set Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

/-- Concrete finite smooth Jordan disks covering the physical fiber of `x`.
The indexing set is a finite subset of the regular level's components. -/
def SmoothPhysicalDiskCover {X : Type*} (π : Sphere → X) (x : X)
    (V F : Set X) (G : Set Sphere) : Prop :=
  ∃ (f : ℂ → ℝ) (t : ℝ)
    (γ : ConnectedComponents {z // f z = t} → Circle → ℂ)
    (H : ConnectedComponents {z // f z = t} → ℂ ≃ₜ ℂ)
    (s : Set (ConnectedComponents {z // f z = t})),
    s.Finite ∧
    (∀ z : ℂ, π (z : Sphere) = x → z ∈ ⋃ i ∈ s, jordanInterior (H i)) ∧
    s.Pairwise (fun i j => Disjoint (closure (jordanInterior (H i)))
      (closure (jordanInterior (H j)))) ∧
    (∀ i ∈ s, closure (jordanInterior (H i)) ⊆
      (fun z : ℂ => π (z : Sphere)) ⁻¹' V) ∧
    ∀ i ∈ s, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧
      Topology.IsEmbedding (γ i) ∧ frontier (jordanInterior (H i)) = range (γ i) ∧
      (∀ z ∈ frontier (jordanInterior (H i)), (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ F)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_FiniteCompletion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The retained core and completed domain of a finite disk construction

The core is the spherical complement of all terminal and filling disks.
If the disks cover the preimage of the quotient dust, the core is a compact
subset of the original domain. Filling the second family leaves precisely
the complement of the terminal interiors. This completed compact set has
the open neighborhood consisting of the original domain and the filling
interiors. In a finite chart its bounded closed pieces are compact, even
though the entire planar exterior is unbounded.

The final statements apply the actual finite patching construction to this
open neighborhood and recover local agreement on the retained core.
-/

open Set Filter Function Metric
open scoped Topology ContDiff

namespace CircleDomainRigidity.FiniteTransfer

def completionCore {I J : Type*} (T : I → ℂ ≃ₜ ℂ) (F : J → ℂ ≃ₜ ℂ) : Set Sphere :=
  (sphericalDiskUnion T ∪ sphericalDiskUnion F)ᶜ

theorem isOpen_sphericalDiskUnion {I : Type*} (H : I → ℂ ≃ₜ ℂ) :
    IsOpen (sphericalDiskUnion H) :=
  isOpen_iUnion fun i => OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen (H i))

end CircleDomainRigidity.FiniteTransfer

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereJordanCoordinates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual complex disk and measurable circle coordinates for a spherical
Jordan collar. -/

open Set Function Metric MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

def sphereJordanBoundary (K : ℂ ≃ₜ ℂ) (θ : UnitAddCircle) : Sphere :=
  ((K (standardCirclePoint θ) : ℂ) : Sphere)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_MeanArcIndex
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Borel arc index is averaged against the actual arc law. On the
boundary its average is the positive Stieltjes coordinate already proved. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

def arcStartingAngleLaw (η : ProbabilityMeasure C(PathTime, ℂ)) : ProbabilityMeasure UnitAddCircle :=
  η.map (f := (fun γ => normalizedArgument (γ 0)))
    (measurable_normalizedArgument.comp (continuous_eval_const 0).measurable).aemeasurable

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CenteredArcLaw
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport of the constructed terminal arc law to centered disk coordinates.
The coordinate extension is only evaluated on the closed collar. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

def centeredArcLaw (η : ProbabilityMeasure C(PathTime, Sphere)) (F : C(Sphere, ℂ)) :
    ProbabilityMeasure C(PathTime, ℂ) := η.map (f := F.comp) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CollarTimeMeasures
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Atomless time measures add over all closed collar cells; the accumulating
endpoint has zero measure. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem collarCells_union : (⋃ n, collarCell n) = Ioi (⊥ : PathTime) := by
  ext t
  constructor
  · intro ht
    obtain ⟨n, hn⟩ := mem_iUnion.mp ht
    exact (collarTime_pos (n + 1)).trans_le hn.1
  · intro ht
    obtain ⟨n, hl, hr⟩ := exists_collarTime_cell ht
    exact mem_iUnion.mpr ⟨n, hl.le, hr⟩

theorem collarCells_aeDisjoint (μ : Measure PathTime) [NullSingletonClass μ] :
    Pairwise (AEDisjoint μ on collarCell) := by
  intro i j hij
  wlog hlt : i < j generalizing i j
  · exact (this hij.symm (lt_of_le_of_ne (Nat.le_of_not_gt hlt) hij.symm)).symm
  change μ (collarCell i ∩ collarCell j) = 0
  apply measure_mono_null (t := {collarTime (i + 1)}) _ (measure_singleton _)
  intro t ht
  apply mem_singleton_iff.mpr
  exact le_antisymm (ht.2.2.trans
    (collarTime_strictAnti.antitone (Nat.succ_le_of_lt hlt))) ht.1.1

theorem sum_collar_restrict (μ : Measure PathTime) [NullSingletonClass μ] :
    Measure.sum (fun n => μ.restrict (collarCell n)) = μ := by
  rw [← Measure.restrict_iUnion_ae (collarCells_aeDisjoint μ)
    (fun _ => measurableSet_Icc.nullMeasurableSet), collarCells_union]
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  have he : (Ioi (⊥ : PathTime))ᶜ = {⊥} := by
    ext t
    simp only [mem_compl_iff, mem_Ioi, not_lt, le_bot_iff, mem_singleton_iff]
  change μ (Ioi (⊥ : PathTime))ᶜ = 0
  rw [he, measure_singleton]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalDensityIntegrability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite spherical quadratic energy supplies finite planar line density
on almost every horizontal and vertical line in each compact chart patch. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_2 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LipschitzArclengthBounds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Lipschitz parameterization has arclength measure dominated by
its Lipschitz constant times one-dimensional Hausdorff measure on time. -/

open Set Function MeasureTheory Metric
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

theorem variation_time_identity {a b : PathTime} (hab : a ≤ b) :
    eVariationOn (id : PathTime → PathTime) (Icc a b) = edist b a := by
  have hm : Monotone (Subtype.val : PathTime → ℝ) := fun _ _ h => h
  have he : eVariationOn (id : PathTime → PathTime) (Icc a b) =
      eVariationOn (Subtype.val : PathTime → ℝ) (Icc a b) := rfl
  rw [he]
  have hv := (hm.monotoneOn univ).eVariationOn_eq (mem_univ a) (mem_univ b)
  rw [univ_inter] at hv
  rw [hv]
  rw [edist_dist, Subtype.dist_eq, Real.dist_eq]
  rw [abs_of_nonneg (show (0 : ℝ) ≤ (b : ℝ) - a from sub_nonneg.mpr hab)]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LipschitzMappedArclength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Lipschitz map multiplies actual path arclength by at most its
Lipschitz constant. The proof constructs the nonnegative Stieltjes difference. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

def lipschitzMappedPath (α : RectifiablePath X) (f : X → Y) {S : Set X} {L : ℝ≥0}
    (hL : LipschitzOnWith L f S) (hα : ∀t, α.val t ∈ S) : RectifiablePath Y := by
  have hc : Continuous (f ∘ α.val) := by
    apply ContinuousOn.comp_continuous hL.continuousOn α.val.continuous hα
  refine ⟨⟨f ∘ α.val, hc⟩, ?_⟩
  exact hL.comp_boundedVariationOn (fun t _ => hα t) α.property

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DomainPhysicalPaths
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rectifiable physical path entirely in the original domain projects
to an allowed quotient path, with exactly its original physical length. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}

def projectDomainPath (e : G ≃ₜ U) (β : C(PathTime, Y)) (hβ : ∀ t, β t ∈ G) :
    C(PathTime, X) where
  toFun t := (e ⟨β t, hβ t⟩).val
  continuous_toFun := continuous_subtype_val.comp (e.continuous.comp (β.continuous.subtype_mk _))

theorem projectDomainPath_mem (e : G ≃ₜ U) (β : C(PathTime, Y)) (hβ : ∀ t, β t ∈ G)
    (t : PathTime) : projectDomainPath e β hβ t ∈ U := (e _).property

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CountableTagAssembly
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Put countably many tag lists into one list without losing any tag.
Unused code slots are inactive, so tuple exclusions are preserved exactly. -/

open Set Function
open scoped Classical

noncomputable section

namespace CircleDomainRigidity

def assembleTags {ι : Type*} [Encodable ι] (θ : ι → ℕ → TagSlot) (k : ℕ) : TagSlot :=
  match Encodable.decode (α := ι × ℕ) k with
  | none => inactiveTag
  | some p => θ p.1 p.2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PreterminalTolls
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! True boundary tolls with exactly the final parameter omitted, retaining
all multiplicities at earlier times. Positive added weights control code mass. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def preterminalToll (γ : C(PathTime, X)) (m : X → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' t : PathTime, if t = ⊤ then 0 else m (γ t)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PotentialRectangleACL
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual barrier pullback is absolutely continuous on almost every
horizontal and vertical segment in each compact physical chart rectangle. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_3 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CrosscutSeparationInput
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The unit-disk specialization of the classical crosscut separation theorem.
Published statement: M. D. Contreras and S. Díaz-Madrigal, *Fractional iteration
in the disk algebra: prime ends and composition operators*, Rev. Mat.
Iberoamericana 21 (2005), 911–928, §3, p. 918, first paragraph defining
crosscuts: the complement has two connected components and each component's
boundary inside the domain is the crosscut.
https://ems.press/content/serial-article-files/38137
-/

open Set Function

namespace CircleDomainRigidity

/-- Exactly two open connected components, with the stated relative frontier.
The endpoints belong to the circle and the open arc belongs to the disk. -/
def UnitDiskCrosscutSeparation : Prop :=
  ∀ p : C(PathTime, ℂ), Injective p → ‖p 0‖ = 1 → ‖p 1‖ = 1 →
    (∀ t ∈ Ioo (0 : PathTime) 1, ‖p t‖ < 1) →
    ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = Metric.ball 0 1 \ range p ∧
      frontier U ∩ Metric.ball 0 1 = range p ∩ Metric.ball 0 1 ∧
      frontier V ∩ Metric.ball 0 1 = range p ∩ Metric.ball 0 1

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CenteredBoundary
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive angular parametrization and inverse of a centered Jordan boundary. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric

def centeredJordanBoundary (K : ℂ ≃ₜ ℂ) (b : Sphere) (θ : UnitAddCircle) : Sphere :=
  ((K (diskCentering (-sphereJordanCoordinate K b) (standardCirclePoint θ)) : ℂ) : Sphere)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalSmoothPartition
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact smooth partition functions on an open planar domain. The
family is locally finite in the domain, allowing accumulation at its boundary. -/

open Set Function Filter TopologicalSpace
open scoped Topology Manifold

noncomputable section

namespace CircleDomainRigidity

structure OpenPlanePartition (Ω : Opens EuclideanPlane) (ι : Type*) where
  weight : ι → EuclideanPlane → ℝ
  smooth : ∀i, ContDiff ℝ (⊤ : ℕ∞) (weight i)
  compact : ∀i, HasCompactSupport (weight i)
  inside : ∀i, tsupport (weight i) ⊆ Ω
  locallyFinite : LocallyFinite (fun i => Subtype.val ⁻¹' Function.support (weight i) :
    ι → Set Ω)
  nonneg : ∀i x, 0 ≤ weight i x
  sum_one : ∀x : Ω, ∑ᶠ i, weight i x = 1

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PartitionMixing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth mixing on an open planar domain. The locally finite sum is
represented by an actual finite sum in a neighborhood of each point. -/

open Set Function Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity
namespace OpenPlanePartition

variable {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
  (ρ : OpenPlanePartition Ω ι)

def mix (v : ι → EuclideanPlane → ℝ) (x : EuclideanPlane) : ℝ :=
  ∑ᶠ i, ρ.weight i x * v i x

end OpenPlanePartition

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CirclePartitionSmoothing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gluing smooth approximants to continuous real circle branches. The
integer transition functions cancel in the partition sum. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

namespace OpenPlanePartition
variable {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} (ρ : OpenPlanePartition Ω ι)

 def circleMix (f : EuclideanPlane → UnitAddCircle) (u v : ι → EuclideanPlane → ℝ)
    (x : EuclideanPlane) : UnitAddCircle :=
  f x + (ρ.mix (fun i y => v i y - u i y) x : UnitAddCircle)

end OpenPlanePartition
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CirclePartitionBands
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive smoothing of local circle branches preserves the limiting
bands in every comparison branch. Connected sampling patches fix the
integer transition before averaging. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
namespace OpenPlanePartition

variable {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} (ρ : OpenPlanePartition Ω ι)

 def adjustedCircleMix (u v : ι → EuclideanPlane → ℝ) (w : EuclideanPlane → ℝ)
    (x : EuclideanPlane) : ℝ := ρ.mix (fun i y => v i y + (w y - u i y)) x

end OpenPlanePartition
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PositiveSobolevApproximation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit positive mollification of a compactly supported planar
Sobolev function. The values and weak derivatives converge in L². -/

open Set Filter MeasureTheory
open scoped ENNReal Topology Convolution

noncomputable section

namespace CircleDomainRigidity

theorem planarMollification_mem_Icc {u : EuclideanPlane → ℝ}
    (hu : AEStronglyMeasurable u volume) {a b : ℝ} (hb : ∀x, u x ∈ Icc a b)
    (n : ℕ) (x : EuclideanPlane) : planarMollification u n x ∈ Icc a b :=
  normed_convolution_mem_Icc volume (DeGiorgi.shrinkingBump n) hu (fun y _ => hb y)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PartitionErrorSum
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected local smoothing errors have a globally controlled L²
sum. Finiteness at each point follows from local finiteness of the weights. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

def partitionDerivativeError
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
    (ρ : OpenPlanePartition Ω ι) (u : EuclideanPlane → ℝ)
    (G : ι → EuclideanPlane → EuclideanPlane) (v : ι → EuclideanPlane → ℝ)
    (i : Fin 2) (j : ι) (x : EuclideanPlane) : ℝ :=
  ρ.weight j x * ((fderiv ℝ (v j) x) (EuclideanSpace.single i 1) - G j x i) +
    (fderiv ℝ (ρ.weight j) x) (EuclideanSpace.single i 1) * (v j x - u x)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PartitionLiftErrorSum
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected local smoothing errors have a globally controlled L²
sum. Finiteness at each point follows from local finiteness of the weights. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

def partitionLiftDerivativeError
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
    (ρ : OpenPlanePartition Ω ι) (u : ι → EuclideanPlane → ℝ)
    (G : ι → EuclideanPlane → EuclideanPlane) (v : ι → EuclideanPlane → ℝ)
    (i : Fin 2) (j : ι) (x : EuclideanPlane) : ℝ :=
  ρ.weight j x * ((fderiv ℝ (v j) x) (EuclideanSpace.single i 1) - G j x i) +
    (fderiv ℝ (ρ.weight j) x) (EuclideanSpace.single i 1) * (v j x - u j x)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PhysicalSamplingPartition
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The small shrinking sampling cover for the actual physical quotient. -/

open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)]

def physicalPlaneOpens (G : Set Sphere) (hG : IsOpen G) : TopologicalSpace.Opens EuclideanPlane :=
  ⟨physicalPlaneDomain G, isOpen_physicalPlaneDomain hG⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RealGradientTransport
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport the smooth global energy conclusion to the real coordinates
used by the finite transfer construction. -/

open Set Function MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity

theorem euclideanPlaneCoordinates_symm_axis (i : Fin 2) :
    euclideanPlaneCoordinates.symm (if i = 0 then (1, 0) else (0, 1)) =
      EuclideanSpace.single i 1 := by
  apply euclideanPlaneCoordinates.injective
  fin_cases i <;> simp

theorem real_chart_partial_derivative {D : Set (ℝ × ℝ)} (hD : IsOpen D)
    {w : EuclideanPlane → ℝ}
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w (euclideanPlaneCoordinates ⁻¹' D))
    {p : ℝ × ℝ} (hp : p ∈ D) (i : Fin 2) :
    (fderiv ℝ (w ∘ euclideanPlaneCoordinates.symm) p) (if i = 0 then (1, 0) else (0, 1)) =
      (fderiv ℝ w (euclideanPlaneCoordinates.symm p)) (EuclideanSpace.single i 1) := by
  have hΩ : IsOpen (euclideanPlaneCoordinates ⁻¹' D) :=
    hD.preimage euclideanPlaneCoordinates.continuous
  have hx : euclideanPlaneCoordinates.symm p ∈ euclideanPlaneCoordinates ⁻¹' D := by
    simpa only [mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using hp
  have hd : DifferentiableAt ℝ w (euclideanPlaneCoordinates.symm p) :=
    (hw.differentiableOn (by simp) _ hx).differentiableAt (hΩ.mem_nhds hx)
  rw [fderiv_comp p hd euclideanPlaneCoordinates.symm.differentiableAt,
    euclideanPlaneCoordinates.symm.fderiv]
  change (fderiv ℝ w (euclideanPlaneCoordinates.symm p))
    (euclideanPlaneCoordinates.symm (if i = 0 then (1, 0) else (0, 1))) = _
  rw [euclideanPlaneCoordinates_symm_axis]

theorem real_chart_gradient_memLp {D : Set (ℝ × ℝ)} (hD : IsOpen D)
    {w : EuclideanPlane → ℝ}
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w (euclideanPlaneCoordinates ⁻¹' D))
    (henergy : ∀i : Fin 2, MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1))
      2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' D))) :
    MemLp (FiniteTransfer.planarGradient (w ∘ euclideanPlaneCoordinates.symm))
      2 (volume.restrict D) := by
  have hmp : MeasurePreserving euclideanPlaneCoordinates.symm (volume.restrict D)
      (volume.restrict (euclideanPlaneCoordinates ⁻¹' D)) := by
    convert euclideanPlaneCoordinates_symm_measurePreserving.restrict_preimage
      (hD.preimage euclideanPlaneCoordinates.continuous).measurableSet using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
  have hi (i : Fin 2) : MemLp
      (fun p => (fderiv ℝ w (euclideanPlaneCoordinates.symm p)) (EuclideanSpace.single i 1))
      2 (volume.restrict D) := (henergy i).comp_measurePreserving hmp
  have hj (i : Fin 2) : MemLp
      (fun p => (fderiv ℝ (w ∘ euclideanPlaneCoordinates.symm) p)
        (if i = 0 then (1, 0) else (0, 1))) 2 (volume.restrict D) := by
    apply (hi i).ae_eq
    filter_upwards [ae_restrict_mem hD.measurableSet] with p hp
    exact (real_chart_partial_derivative hD hw hp i).symm
  apply memLp_prod_iff.mpr
  exact ⟨hj 0, hj 1⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_OpenDomainRepresentative
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A globally measurable representative of a smooth function on an open
physical plane domain, preserving its actual derivatives there. -/

open Set Function MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity

def openZeroExtension (D : Set EuclideanPlane) (w : EuclideanPlane → ℝ) : EuclideanPlane → ℝ := by
  classical
  exact D.piecewise w (fun _ => 0)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RealGradientNorm
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact L² preservation for each derivative component under the planar
coordinate change used by finite transfer. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity

theorem real_chart_partial_eLpNorm {D : Set (ℝ × ℝ)} (hD : IsOpen D)
    {w : EuclideanPlane → ℝ}
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w (euclideanPlaneCoordinates ⁻¹' D))
    (i : Fin 2)
    (hi : MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1))
      2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' D))) :
    eLpNorm (fun p => (fderiv ℝ (w ∘ euclideanPlaneCoordinates.symm) p)
        (if i = 0 then (1, 0) else (0, 1))) 2 (volume.restrict D) =
      eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1))
        2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' D)) := by
  have hmp : MeasurePreserving euclideanPlaneCoordinates.symm (volume.restrict D)
      (volume.restrict (euclideanPlaneCoordinates ⁻¹' D)) := by
    convert euclideanPlaneCoordinates_symm_measurePreserving.restrict_preimage
      (hD.preimage euclideanPlaneCoordinates.continuous).measurableSet using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
  have heq : (fun p => (fderiv ℝ (w ∘ euclideanPlaneCoordinates.symm) p)
        (if i = 0 then (1, 0) else (0, 1))) =ᵐ[volume.restrict D]
      (fun p => (fderiv ℝ w (euclideanPlaneCoordinates.symm p)) (EuclideanSpace.single i 1)) := by
    filter_upwards [ae_restrict_mem hD.measurableSet] with p hp
    exact real_chart_partial_derivative hD hw hp i
  rw [eLpNorm_congr_ae heq]
  exact eLpNorm_comp_measurePreserving
    (g := fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) hi.aestronglyMeasurable hmp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SparseTags
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrary injective reassignment of tag slots. All geometric data and
residual conditions are preserved, including unused slots. -/

open Set Function MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

def sparseTags (e : ℕ ↪ ℕ) (θ : ℕ → TagSlot) (k : ℕ) : TagSlot :=
  if h : ∃ i, e i = k then θ h.choose else inactiveTag

theorem sparseTags_at (e : ℕ ↪ ℕ) (θ : ℕ → TagSlot) (i : ℕ) :
    sparseTags e θ (e i) = θ i := by
  have h : ∃ j, e j = e i := ⟨i, rfl⟩
  have hi : h.choose = i := e.injective h.choose_spec
  simp only [sparseTags, dite_eq_left h, hi]

theorem sparseTags_outside (e : ℕ ↪ ℕ) (θ : ℕ → TagSlot) {k : ℕ}
    (hk : k ∉ Set.range e) : sparseTags e θ k = inactiveTag := by
  exact dite_eq_right hk

def sparseTaggedPath {X : Type*} [TopologicalSpace X] (e : ℕ ↪ ℕ)
    (Γ : TaggedPath X) : TaggedPath X := (Γ.1, sparseTags e Γ.2)

theorem residualTimes_sparse {X : Type*} [TopologicalSpace X]
    (B : Set X) (e : ℕ ↪ ℕ) (Γ : TaggedPath X) :
    residualTimes B (sparseTaggedPath e Γ) = residualTimes B Γ := by
  ext t
  constructor
  · rintro ⟨ht, htags⟩
    refine ⟨ht, fun i => ?_⟩
    simpa only [sparseTaggedPath, sparseTags_at] using htags (e i)
  · rintro ⟨ht, htags⟩
    refine ⟨ht, fun k => ?_⟩
    by_cases hk : k ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hk
      simpa only [sparseTaggedPath, sparseTags_at] using htags i
    · left
      simp only [sparseTaggedPath, sparseTags_outside e Γ.2 hk, inactiveTag,
        tagLeft, Sum.elim_inl]
      exact le_top

theorem residualImage_sparse {X : Type*} [MetricSpace X]
    (B : Set X) (e : ℕ ↪ ℕ) (Γ : TaggedPath X) :
    residualImage B (sparseTaggedPath e Γ) = residualImage B Γ := by
  rw [residualImage, residualTimes_sparse]
  rfl

variable {X : Type*} [MetricSpace X]

theorem tagRules_sparse (H : ℕ → Set (UnitAddCircle × X))
    (T : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (e : ℕ ↪ ℕ) {Γ : TaggedPath X} (hΓ : TagRules H T Γ) :
    TagRules H T (sparseTaggedPath e Γ) := by
  intro k
  by_cases hk : k ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hk
    simpa only [sparseTaggedPath, sparseTags_at] using hΓ i
  · simpa only [sparseTaggedPath, sparseTags_outside e Γ.2 hk] using
      inactiveTag_rules H T Γ.1

theorem residualIncidence_sparse {Z : Type*} (B : Set X) (I : Set PathTime)
    (R : Set (Z × X)) (P : Set X) (e : ℕ ↪ ℕ) (Γ : TaggedPath X) (z : Z) :
    (sparseTaggedPath e Γ, z) ∈ residualIncidence B I R P ↔
      (Γ, z) ∈ residualIncidence B I R P := by
  change (∃ t ∈ residualTimes B (sparseTaggedPath e Γ),
    t ∈ I ∧ (z, Γ.1 t) ∈ R ∧ Γ.1 t ∉ P) ↔ _
  rw [residualTimes_sparse]
  rfl

theorem residualToll_sparse (B : Set X) (I : Set PathTime) (m : X → ℝ≥0∞)
    (e : ℕ ↪ ℕ) (Γ : TaggedPath X) :
    residualToll B I m (sparseTaggedPath e Γ) = residualToll B I m Γ := by
  unfold residualToll
  rw [residualTimes_sparse]
  rfl

theorem residualConstraintFamily_sparse {Z : Type*} [TopologicalSpace Z]
    [MeasurableSpace Z] (B : Set X) (R : ℕ → Set (Z × X))
    (P : ℕ → ℕ → Finset X) (ν : ℕ → Measure Z) (m : ℕ → X → ℝ≥0∞)
    (e : ℕ ↪ ℕ) (Γ : TaggedPath X) :
    ResidualConstraintFamily B R P ν m (sparseTaggedPath e Γ) ↔
      ResidualConstraintFamily B R P ν m Γ := by
  unfold ResidualConstraintFamily ResidualIncidenceBound
  simp only [residualIncidence_sparse, residualToll_sparse]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CodeConstraints
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Forgetting auxiliary dust and tuple exclusions maps an allowed endpoint
code into the base-code family without changing its path or tags. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem tagTupleExcluded_mono
    {S T : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle)}
    (h : ∀ n l, S n l ⊆ T n l) : tagTupleExcluded S ⊆ tagTupleExcluded T := by
  apply iUnion_mono
  intro n
  apply iUnion_mono
  intro l
  exact image_mono (Set.prod_mono (h n l) Subset.rfl)

theorem tagRules_relax {X : Type*} [MetricSpace X]
    {H : ℕ → Set (UnitAddCircle × X)}
    {S T : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle)}
    (h : ∀ n l, S n l ⊆ T n l) {Γ : TaggedPath X} (hΓ : TagRules H T Γ) :
    TagRules H S Γ := by
  intro k
  exact ⟨(hΓ k).1, (hΓ k).2.1, fun hk => (hΓ k).2.2 (tagTupleExcluded_mono h hk)⟩

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

theorem allowedTaggedPath_forget (d : PathCodeData X Y) (ν : Measure X)
    (T : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    {Γ : TaggedPath X} (hΓ : AllowedTaggedPath d ν T Γ) :
    AllowedTaggedPath d 0 (fun _ _ => ∅) Γ := by
  refine ⟨hΓ.1, tagRules_relax (fun _ _ => empty_subset _) hΓ.2.1,
    hΓ.2.2.1, hΓ.2.2.2.1, ?_⟩
  simp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SparseBaseCodes
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Injective retagging preserves the complete base-code conditions and cost finiteness.
It is a Borel operation on the actual code space. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

theorem allowedTaggedPath_sparse (d : PathCodeData X Y) (ν : Measure X)
    (T : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (e : ℕ ↪ ℕ) {Γ : TaggedPath X} (hΓ : AllowedTaggedPath d ν T Γ) :
    AllowedTaggedPath d ν T (sparseTaggedPath e Γ) := by
  refine ⟨hΓ.1, tagRules_sparse d.levels T e hΓ.2.1, ?_, ?_, ?_⟩
  · exact (residualConstraintFamily_sparse _ _ _ _ _ e Γ).mpr hΓ.2.2.1
  · exact (residualConstraintFamily_sparse _ _ _ _ _ e Γ).mpr hΓ.2.2.2.1
  · rw [residualImage_sparse]
    exact hΓ.2.2.2.2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FullIntervalTag
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A simple arc in a permitted finite level union can use one tag on its
whole open parameter interval. If its endpoints are in the domain, no dust
time remains and every residual constraint is vacuous. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

def fullIntervalTag (n : ℕ) (labels : Fin (n + 1) → ℕ)
    (levels : Fin (n + 1) → UnitAddCircle) : TagSlot :=
  Sum.inr ⟨n, labels, levels, ⊥, ⊤⟩

def fullIntervalTaggedPath {X : Type*} [TopologicalSpace X]
    (γ : C(PathTime, X)) (n : ℕ) (labels : Fin (n + 1) → ℕ)
    (levels : Fin (n + 1) → UnitAddCircle) : TaggedPath X :=
  (γ, fun k => if k = 0 then fullIntervalTag n labels levels else inactiveTag)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TerminalRemainder
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The safe region for filling after the terminals are selected

The remaining quotient dust is compact and relatively clopen. Its open
neighborhood is chosen to avoid both the retained physical core and all
closed terminal caps, so every later filling closure inherits both
separations.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def terminalRemainder {I : Type*} (π : Sphere → Sphere) (B : Set Sphere)
    (T : I → ℂ ≃ₜ ℂ) : Set Sphere := B \ (π '' sphericalDiskUnion T)

def closedTerminalImages {I : Type*} (π : Sphere → Sphere) (T : I → ℂ ≃ₜ ℂ) : Set Sphere :=
  ⋃ i, π '' (((↑) : ℂ → Sphere) '' closure (jordanInterior (T i)))

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_CompletedChart
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual completed region in the finite real chart

These identifications pass the spherical disk completion to the real
coordinates used by the energy estimates, preserving the original core
and the exact open extension domain.
-/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem isClosed_realChartDomain {Q : Set Sphere} (hQ : IsClosed Q) :
    IsClosed (realChartDomain Q) :=
  hQ.preimage (OnePoint.continuous_coe.comp Complex.equivRealProdCLM.symm.continuous)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PathIntersectionMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite intersection measure of a random path with a closed set.
Closed incidence tests suffice for measurability of the whole measure.
Paths with infinitely many intersections are discarded; they form a null
set whenever the expected total intersection count is finite. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

def pathIntersectionMeasure (H : Set X) (γ : C(PathTime, X)) : Measure X :=
  if pathImageCount H γ < ∞ then Measure.count.restrict (range γ ∩ H) else 0

def meanPathIntersectionMeasure (H : Set X) (μ : Measure C(PathTime, X)) : Measure X :=
  μ.bind (pathIntersectionMeasure H)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CountableClosedLevelCount
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint Borel measurability of distinct path intersections with a
countable union of closed level relations. Paths may retrace themselves.
-/

open Set Function MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

variable {X T : Type*} [MetricSpace X]
  [TopologicalSpace T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

def indexedSeparatedHits (H : ℕ → Set (X × T)) (n : ℕ)
    (a : Fin n → ℕ) (r : ℝ) : Set (C(PathTime, X) × T) :=
  {p | ∃ s : Fin n → PathTime,
    (∀ i j, i ≠ j → r ≤ dist (p.1 (s i)) (p.1 (s j))) ∧
    ∀ i, (p.1 (s i), p.2) ∈ H (a i)}

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothMeanPeriodConsequences
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed smooth mean coordinate has the actual point-hit
budget and satisfies compatibility with every finite prior level union. -/

open Set Function Filter MeasureTheory Classical
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_17 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothMeanPhysicalBranches
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained mean branches project to the actual physical circle
coordinate. Its smoothness upgrades those continuous branches to smooth
real functions on the physical patch, as required by terminal filling. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_19 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MeanMarkedBranchBands
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The chosen chart is retained together with each marked interval.
This lets the same branch supply both the graph incidence interval and
the physical terminal staircase estimate. -/

open Set Function Filter MeasureTheory Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_20 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_TerminalBoundaryLimits
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Inverse images approach the assigned terminal boundary

A target sequence approaching an assigned complementary component has
preimages eventually in every neighborhood of the corresponding physical
terminal boundary. Compactness and the proved component assignment replace
any assumption of a boundary extension of the uniformizing map.
-/

open Set Function Filter
open scoped Topology

namespace CircleDomainRigidity

open FiniteTransfer

instance sphereFirstCountableTopology : FirstCountableTopology Sphere :=
  (onePointEquivSphereOfFinrankEq (V := ℂ) (ι := Fin 3) (by simp)).isEmbedding.firstCountableTopology

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_TransportedTerminalBranches
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cluster oscillation of transported terminal branches

The finite model's actual inverse transports a real branch near a physical
terminal. All its cluster values at the assigned complementary component
come from the physical boundary. Thus the physical square-sum oscillation
estimate survives uniformization without a boundary-extension hypothesis.
-/

open Set Function Filter
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

/-- Finite real cluster values approached from the domain at a component. -/
def componentClusterValues (V : Set Sphere) (p : Sphere) (v : Sphere → ℝ) : Set ℝ :=
  {t | ∃ y ∈ connectedComponentIn Vᶜ p, ∃ yn : ℕ → Sphere,
    Tendsto yn atTop (𝓝 y) ∧ (∀ᶠ n in atTop, yn n ∈ V) ∧
      Tendsto (v ∘ yn) atTop (𝓝 t)}

/-- A real-coordinate function, with an arbitrary unused value at infinity. -/
def sphereRealFunction {Y : Type*} (w : (ℝ × ℝ) → Y) (p : Sphere) : Y :=
  w (Complex.equivRealProdCLM (finiteCoord p))

theorem continuousAt_sphereRealFunction {Y : Type*} [TopologicalSpace Y]
    {w : (ℝ × ℝ) → Y} {z : ℂ}
    (hw : ContinuousAt w (Complex.equivRealProdCLM z)) :
    ContinuousAt (sphereRealFunction w) (z : Sphere) := by
  apply OnePoint.continuousAt_coe.mpr
  have heq : sphereRealFunction w ∘ ((↑) : ℂ → Sphere) =
      w ∘ Complex.equivRealProdCLM := by
    funext x
    simp only [sphereRealFunction, comp_apply, finiteCoord_coe]
  rw [heq]
  exact hw.comp Complex.equivRealProdCLM.continuous.continuousAt

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereClusterBridge
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-chart cluster bounds from the assigned sphere ends

The line-payment lemma uses planar cluster points. They are the same
finite cluster values controlled by the inverse terminal-boundary
argument, so no boundary extension of the finite uniformization is needed.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem planar_mapClusterPt_mem_componentClusterValues
    {V : Set Sphere} {p : Sphere} {q : ℂ} {w : Sphere → ℝ} {t : ℝ}
    (hq : (q : Sphere) ∈ connectedComponentIn Vᶜ p)
    (ht : MapClusterPt t (𝓝[((↑) : ℂ → Sphere) ⁻¹' V] q)
      (w ∘ ((↑) : ℂ → Sphere))) :
    t ∈ componentClusterValues V p w := by
  obtain ⟨x, hwx, hx⟩ := ht.exists_seq_tendsto
  have hx' := tendsto_nhdsWithin_iff.mp hx
  refine ⟨(q : Sphere), hq, (fun n => (x n : Sphere)), ?_, ?_, hwx⟩
  · exact OnePoint.continuous_coe.continuousAt.tendsto.comp hx'.1
  · exact hx'.2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FiniteTerminalDisks
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Round disk coordinates for the actual terminal assignment

The finite model's complementary disks are constructed from its circle
domain property. Their labels are exactly the physical terminal labels,
and their union is the full complement in the finite chart.
-/

open Set Function Metric

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem terminal_disk_subset_bound
    {V : Set Sphere} {p : Sphere} {c : ℂ} {r L : ℝ}
    (he : connectedComponentIn Vᶜ p = ((↑) : ℂ → Sphere) '' closedBall c r)
    (hbound : Vᶜ ⊆ ((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) L) :
    closedBall c r ⊆ closedBall (0 : ℂ) L := by
  intro z hz
  have hzc : (z : Sphere) ∈ connectedComponentIn Vᶜ p := by
    rw [he]
    exact mem_image_of_mem _ hz
  exact OnePoint.coe_injective.mem_set_image.mp (hbound (connectedComponentIn_subset _ _ hzc))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RetainedImageBoundary
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual image boundary of a retained source collar, and its bounded
side. Schoenflies supplies only a chart for the embedded image circle. -/

open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem target_closed_collar_subset_image
    {G S V : Set Sphere} {f : Sphere → Sphere} (H J : ℂ ≃ₜ ℂ)
    (hbd : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G)
    (hboundary : f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior J))
    (hside : f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) =
      V ∩ (((↑) : ℂ → Sphere) '' jordanInterior J))
    (hsource : G ∩ closedTerminalCap H ⊆ S) :
    V ∩ closedTerminalCap J ⊆ f '' S := by
  rintro _ ⟨hyV, z, hz, rfl⟩
  by_cases hzi : z ∈ jordanInterior J
  · have hyt : (z : Sphere) ∈ f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) :=
      hside.symm ▸ ⟨hyV, z, hzi, rfl⟩
    obtain ⟨x, hx, he⟩ := hyt
    refine ⟨x, hsource ⟨hx.1, ?_⟩, he⟩
    obtain ⟨w, hw, rfl⟩ := hx.2
    exact ⟨w, subset_closure hw, rfl⟩
  · have hzfront : z ∈ frontier (jordanInterior J) :=
      ⟨hz, (jordanInterior_isOpen J).interior_eq.symm ▸ hzi⟩
    obtain ⟨x, hx, he⟩ := hboundary.symm ▸
      (show (z : Sphere) ∈ ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) from
        ⟨z, hzfront, rfl⟩)
    refine ⟨x, hsource ⟨hbd hx, ?_⟩, he⟩
    obtain ⟨w, hw, rfl⟩ := hx
    exact ⟨w, frontier_subset_closure hw, rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RoundCollarLifts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual zero-period real lift on a target collar is the source
branch composed with the inverse finite model. Its oscillation follows
from the terminal assignment, not from a boundary extension. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 def roundCollarRealLift (fi : Sphere → Sphere) (v : Sphere → ℝ)
    (c : ℂ) (r : ℝ) (t : ℝ) : ℝ := v (fi (unitCircleParam c r t : Sphere))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_UnorientedCircleGreen
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The orientation-independent form of the same published Green input.

M. Spivak, Calculus on Manifolds (1965), Theorem 5-5, p.124. A regular
once-traversed Jordan boundary has one of the two orientations; the sign
below changes its integral to the positive boundary orientation. Inner
circles retain their positive disk orientation. This is the signed
parametrized specialization of the same manifold Stokes theorem cited in
`FiniteCircleGreen.lean`, not an energy or uniformization assumption.
The sign is chosen before the holes and the differential form.
-/

open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 def UnorientedFiniteCircleGreenFormula : Prop :=
  ∀ (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ), RegularJordanParametrization H γ →
    ∃ e : ℝ, |e| = 1 ∧
    ∀ (n : ℕ) (c : Fin n → ℂ) (r : Fin n → ℝ),
      (∀ i, 0 < r i) →
      Pairwise (Disjoint on fun i => Metric.closedBall (c i) (r i)) →
      (∀ i, Metric.closedBall (c i) (r i) ⊆ jordanInterior H) →
    ∀ O : Set ℂ, IsOpen O →
      (closure (jordanInterior H) \ ⋃ i, Metric.ball (c i) (r i)) ⊆ O →
    ∀ P Q : ℂ → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) P O → ContDiffOn ℝ (⊤ : ℕ∞) Q O →
      e * planarFormIntegral P Q γ -
        ∑ i, planarFormIntegral P Q (unitCircleParam (c i) (r i)) =
        ∫ z in jordanInterior H \ ⋃ i, Metric.closedBall (c i) (r i),
          (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_BoundaryPairNeighborhood
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Open exclusion neighborhoods use the actual fixed-source boundary
functional. Its continuity is proved from the disk-distance estimate;
no stability or exclusion assertion is assumed. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal

noncomputable section
namespace CircleDomainRigidity

def boundaryCurveTrace (γ : ℝ → ℂ) (hγ : Continuous γ) : C(PathTime, ℂ) :=
  ⟨fun t => γ t, hγ.comp continuous_subtype_val⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ShrinkingRealModels
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vanishing transfer errors and shrinking physical marked neighborhoods. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

attribute [local instance] sphereMetric

def markedNeighborhoods {S : Type*} (σ : S → Sphere) (n : ℕ) (s : S) : Set Sphere :=
  ball (σ s) (modelError n)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedLevelData
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual marked band widths supply the level weights for the next
endpoint-law construction. This uses the full dust as a temporary label
set; the common countable mark restriction is performed after selection. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_21 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ExactBandMeasure
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Haar length of a projected interval. A band of width at most
one is measured without loss, so its actual coordinate weight controls
every bounded local real lift of that band. -/

open Set Function MeasureTheory Metric Filter
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem band_width_le_of_fiber_subset
    {U : Set Sphere} {f : Sphere → ℝ} {M : ℝ}
    (hf : ∀ y ∈ U, |f y| ≤ M) {x : Sphere} (hx : x ∈ closure U)
    (hwidth : limsup f (𝓝[U] x) - liminf f (𝓝[U] x) ≤ 1)
    {lo hi : ℝ}
    (hsub : {θ : UnitAddCircle | (x, θ) ∈ circleBandGraph U f} ⊆
      ((↑) : ℝ → UnitAddCircle) '' Icc lo hi) :
    ENNReal.ofReal (limsup f (𝓝[U] x) - liminf f (𝓝[U] x)) ≤
      ENNReal.ofReal (hi - lo) := by
  have hvol := measure_mono (μ := (volume : Measure UnitAddCircle)) hsub
  rw [circleBandGraph_fiber_eq_image_realFiber,
    intervalFiberHull_clusterGraph_eq_boundary_band hf hx,
    volume_addCircle_image_Icc, min_eq_right hwidth] at hvol
  exact hvol.trans ((volume_addCircle_image_Icc_le lo hi).trans
    (ENNReal.ofReal_le_ofReal (min_le_right _ _)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConductivityCoefficient
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual two-valued conductivity coefficient. Its strict contraction
constant is (n-1)/(n+1), and the constructed density vanishes off F. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

def conductivityCoefficient (F : Set EuclideanPlane) (n : ℕ) (x : EuclideanPlane) : ℝ :=
  F.indicator (fun _ => ((n : ℝ) - 1) / ((n : ℝ) + 1)) x

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothPlaneSobolev
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness on an open plane set and integrable partial derivatives give
an actual Sobolev witness. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem integrable_plane_mul_of_continuousOn
    {U : Set EuclideanPlane} (hU : IsOpen U) {f φ : EuclideanPlane → ℝ}
    (hf : ContinuousOn f U) (hφ : Continuous φ) (hs : HasCompactSupport φ)
    (hsub : tsupport φ ⊆ U) : Integrable (fun x => f x * φ x) :=
  ((hf.mul hφ.continuousOn).continuous_of_tsupport_subset hU
    (tsupport_mul_subset_right.trans hsub)).integrable_of_hasCompactSupport hs.mul_left

 theorem weakPartial_of_smooth_on
    {U : Set EuclideanPlane} (hU : IsOpen U) {f : EuclideanPlane → ℝ}
    (hf : ContDiffOn ℝ 1 f U) (i : Fin 2) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) f U := by
  intro φ hφ hs hsub
  let v : EuclideanPlane := EuclideanSpace.single i 1
  have hdf : ContinuousOn (fun x => fderiv ℝ f x v) U :=
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hdφ : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have he := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_plane_mul_of_continuousOn hU hdf hφ.continuous hs hsub)
    (integrable_plane_mul_of_continuousOn hU hf.continuousOn hdφ
      (hs.fderiv_apply (𝕜 := ℝ) v) ((tsupport_fderiv_apply_subset ℝ v).trans hsub))
    (integrable_plane_mul_of_continuousOn hU hf.continuousOn hφ.continuous hs hsub)
    (fun x hx => (hf.contDiffAt (hU.mem_nhds (hsub hx))).differentiableAt (by norm_num))
    (fun x _ => hφ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    have hn : x ∉ tsupport (fun y => fderiv ℝ φ y v) :=
      fun h => hx (hsub ((tsupport_fderiv_apply_subset ℝ v) h))
    rw [image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ φ y v) hn, mul_zero]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsub h)), mul_zero])]
  exact he

 def smoothPlaneSobolevWitness
    {U : Set EuclideanPlane} (hU : IsOpen U) {f : EuclideanPlane → ℝ}
    (hf : ContDiffOn ℝ 1 f U) (hL : MemLp f 2 (volume.restrict U))
    (hD : ∀ i : Fin 2, MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1))
      2 (volume.restrict U)) : DeGiorgi.MemW1pWitness 2 f U where
  memLp := hL
  weakGrad := fun x => WithLp.toLp 2 (fun i => fderiv ℝ f x (EuclideanSpace.single i 1))
  weakGrad_component_memLp := hD
  isWeakGrad := weakPartial_of_smooth_on hU hf

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_PrincipalRealBeltrami
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The precise classical real-coefficient principal Beltrami input.

Published source: Clop and Cruz, *Weighted estimates for Beltrami
equations*, Ann. Acad. Sci. Fenn. Math. 38 (2013), 91–113,
DOI 10.5186/aasfm.2013.3818, section 4, opening paragraph, p. 107.
Their theorem states existence of a principal W^{1,2}_loc plane homeomorphism
for compactly supported measurable coefficients mu, nu with
|mu|+|nu| bounded by k<1. We use only mu=0 and real nu=q.

No height, energy inequality, extremality, circle model, or limiting
assertion is included in this input. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

 def PrincipalRealBeltrami : Prop :=
  ∀ (q : EuclideanPlane → ℝ), AEStronglyMeasurable q volume →
    (∃ K : Set EuclideanPlane, IsCompact K ∧ ∀ x ∉ K, q x = 0) →
    ∀ k : ℝ≥0, k < 1 → (∀ᵐ x ∂volume, ‖q x‖ ≤ k) →
    ∃ (φ : ℂ ≃ₜ ℂ) (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x))),
      Tendsto (fun z => φ z - z) (Bornology.cobounded ℂ) (𝓝 0) ∧
      ∀ᵐ x ∂volume,
        planarDbar (D.realGradient x 0) (D.realGradient x 1)
          (D.imagGradient x 0) (D.imagGradient x 1) =
        q x • star (planarDz (D.realGradient x 0) (D.realGradient x 1)
          (D.imagGradient x 0) (D.imagGradient x 1))

 def conductivityValue (F : Set EuclideanPlane) (n : ℕ) (x : EuclideanPlane) : ℝ := by
  classical
  exact if x ∈ F then (n : ℝ) else 1

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalComplexWitness
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weak complex differential supplies genuine local Sobolev witnesses
for both scalar coordinates. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem weakPartial_restrict_from_univ
    {f g : EuclideanPlane → ℝ} {i : Fin 2}
    (h : DeGiorgi.HasWeakPartialDeriv i g f univ) (U : Set EuclideanPlane) :
    DeGiorgi.HasWeakPartialDeriv i g f U := by
  intro φ hφ hs hsub
  have hh := h φ hφ hs (subset_univ _)
  simp only [Measure.restrict_univ] at hh
  have hf : ∫ x in U, f x * fderiv ℝ φ x (EuclideanSpace.single i 1) =
      ∫ x, f x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ φ y (EuclideanSpace.single i 1))
      (fun hd => hx (hsub (tsupport_fderiv_apply_subset ℝ _ hd))), mul_zero]
  have hg : ∫ x in U, g x * φ x = ∫ x, g x * φ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hsub ht)), mul_zero]
  rw [hf, hg]
  exact hh

 theorem continuous_memLp_ball {f : EuclideanPlane → ℝ} (hf : Continuous f) (R : ℝ) :
    MemLp f 2 (volume.restrict (Metric.ball 0 R)) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball (0 : EuclideanPlane) R)) :=
    isFiniteMeasure_restrict.mpr (measure_ball_lt_top.ne)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : EuclideanPlane) R).bddAbove_image hf.norm.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable.restrict B
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact hB ⟨x, Metric.ball_subset_closedBall hx, rfl⟩

namespace PlaneLocalWeakComplex

 def realWitness {f : EuclideanPlane → ℂ} (D : PlaneLocalWeakComplex f)
    (hf : Continuous f) (R : ℝ) :
    DeGiorgi.MemW1pWitness 2 (fun x => (f x).re) (Metric.ball 0 R) where
  memLp := continuous_memLp_ball (Complex.continuous_re.comp hf) R
  weakGrad := D.realGradient
  weakGrad_component_memLp := D.real_memLp R
  isWeakGrad := fun i => weakPartial_restrict_from_univ (D.real_weak i) _

 def imagWitness {f : EuclideanPlane → ℂ} (D : PlaneLocalWeakComplex f)
    (hf : Continuous f) (R : ℝ) :
    DeGiorgi.MemW1pWitness 2 (fun x => (f x).im) (Metric.ball 0 R) where
  memLp := continuous_memLp_ball (Complex.continuous_im.comp hf) R
  weakGrad := D.imagGradient
  weakGrad_component_memLp := D.imag_memLp R
  isWeakGrad := fun i => weakPartial_restrict_from_univ (D.imag_weak i) _

end PlaneLocalWeakComplex
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_BorelSobolevGradient
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel L² representatives of the two actual global weak derivatives.
Changing these representatives preserves the Sobolev witness. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def scalarGradientRepresentative {u : EuclideanPlane → ℝ}
    (W : DeGiorgi.MemW1pWitness 2 u univ) (i : Fin 2) :
    Lp ℝ 2 (volume : Measure EuclideanPlane) :=
  (show MemLp (fun p => W.weakGrad p i) 2 volume by
    simpa only [Measure.restrict_univ] using W.weakGrad_component_memLp i).toLp _

 theorem scalarGradientRepresentative_ae {u : EuclideanPlane → ℝ}
    (W : DeGiorgi.MemW1pWitness 2 u univ) (i : Fin 2) :
    scalarGradientRepresentative W i =ᵐ[volume] (fun p => W.weakGrad p i) :=
  MemLp.coeFn_toLp _

 def borelSobolevWitness {u : EuclideanPlane → ℝ}
    (W : DeGiorgi.MemW1pWitness 2 u univ) : DeGiorgi.MemW1pWitness 2 u univ where
  memLp := W.memLp
  weakGrad := fun p => WithLp.toLp 2 (fun i => scalarGradientRepresentative W i p)
  weakGrad_component_memLp := fun i => (Lp.memLp (scalarGradientRepresentative W i)).restrict univ
  isWeakGrad := by
    intro i
    apply (W.isWeakGrad i).congr_ae (EventuallyEq.rfl)
    simpa only [Measure.restrict_univ] using (scalarGradientRepresentative_ae W i).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevScalarCoarea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The scalar planar specialization of Malý–Swanson–Ziemer,
*The co-area formula for Sobolev mappings*, Trans. AMS 355 (2003),
477–492, Theorem 1.1, DOI 10.1090/S0002-9947-02-03091-X.
Primary author text: https://arxiv.org/pdf/math/0112008, Theorem 1.1
and (1.2), p.1; nonnegative weights follow by the simple-function
approximation described before (1.2). The precise representative is
automatic for a continuous function, by the definition (2.5), p.5.

Only continuous real W1,2_loc functions on the plane and bounded Borel
sets are used. The derivative is the actual distributional gradient.
The proposition below contains no level topology or null image assertion.
-/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def sobolevLevelIntegral (E : Set EuclideanPlane) (v : EuclideanPlane → ℝ)
    (q : EuclideanPlane → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ p in E ∩ {p | v p = t}, q p ∂(μH[1] : Measure EuclideanPlane)

 def PlanarSobolevCoarea : Prop :=
  ∀ (v : EuclideanPlane → ℝ), Continuous v →
  ∀ (V : EuclideanPlane → EuclideanPlane), DeGiorgi.HasWeakGrad V v univ →
  (∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R))) →
  ∀ (E : Set EuclideanPlane), MeasurableSet E → IsBounded E →
  ∀ (q : EuclideanPlane → ℝ≥0∞), Measurable q →
    AEMeasurable (sobolevLevelIntegral E v q) volume ∧
    (∫⁻ t, sobolevLevelIntegral E v q t) =
      ∫⁻ p in E, q p * ENNReal.ofReal ‖V p‖

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ComplexSobolevTransport
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two physical complex-coordinate derivative identities give the
Euclidean-plane weak derivatives, with the same area measure. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

theorem complexPlaneCoordinates_measurePreserving :
    MeasurePreserving complexPlaneCoordinates volume volume :=
  (Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd).comp
    euclideanPlaneCoordinates_measurePreserving

theorem weakPartial_of_complex_identity
    {f G : ℂ → ℝ} (i : Fin 2) (v : ℂ)
    (hv : complexPlaneCoordinates (EuclideanSpace.single i 1) = v)
    (hweak : ∀ ψ : ℂ → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ z, f z * fderiv ℝ ψ z v) = -(∫ z, G z * ψ z))
    (U : Set ℂ) :
    DeGiorgi.HasWeakPartialDeriv i (G ∘ complexPlaneCoordinates)
      (f ∘ complexPlaneCoordinates) (complexPlaneCoordinates ⁻¹' U) := by
  intro φ hφ hs hsub
  let e := complexPlaneCoordinates
  let ψ : ℂ → ℝ := φ ∘ e.symm
  have hψ : ContDiff ℝ 1 ψ := (hφ.comp e.symm.contDiff).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hsψ : HasCompactSupport ψ := hs.comp_homeomorph e.symm.toHomeomorph
  have hd (z : ℂ) : fderiv ℝ ψ z v =
      fderiv ℝ φ (e.symm z) (EuclideanSpace.single i 1) := by
    rw [fderiv_comp z (hφ.differentiable (by simp)).differentiableAt e.symm.differentiableAt,
      e.symm.fderiv]
    change fderiv ℝ φ (e.symm z) (e.symm v) = _
    rw [← hv, ContinuousLinearEquiv.symm_apply_apply]
  have hleft : ∀ x, x ∉ e ⁻¹' U →
      (f ∘ e) x * fderiv ℝ φ x (EuclideanSpace.single i 1) = 0 := by
    intro x hx
    have hnx : x ∉ tsupport (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
      fun h => hx (hsub ((tsupport_fderiv_apply_subset ℝ _ ) h))
    rw [image_eq_zero_of_notMem_tsupport hnx, mul_zero]
  have hright : ∀ x, x ∉ e ⁻¹' U → (G ∘ e) x * φ x = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsub h)), mul_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hleft,
    setIntegral_eq_integral_of_forall_compl_eq_zero hright]
  have he : MeasurePreserving e volume volume := complexPlaneCoordinates_measurePreserving
  calc
    _ = ∫ x, f (e x) * fderiv ℝ ψ (e x) v := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [hd, ContinuousLinearEquiv.symm_apply_apply, comp_apply]
    _ = ∫ z, f z * fderiv ℝ ψ z v :=
      he.integral_comp e.toHomeomorph.measurableEmbedding (fun z => f z * fderiv ℝ ψ z v)
    _ = -(∫ z, G z * ψ z) := hweak ψ hψ hsψ
    _ = _ := by
      rw [← he.integral_comp e.toHomeomorph.measurableEmbedding (fun z => G z * ψ z)]
      simp only [ψ, comp_apply, ContinuousLinearEquiv.symm_apply_apply]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PhysicalRoundIntegrals
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact transport of round-disk integrals and smooth partial derivatives
between the physical Euclidean plane and the complex plane. -/
open Set Filter Function MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem complexPlaneCoordinates_preimage_ball (R : ℝ) :
    complexPlaneCoordinates ⁻¹' ball (0 : ℂ) R = ball (0 : EuclideanPlane) R := by
  ext x
  simp only [mem_preimage, mem_ball, dist_zero_right, complexPlaneCoordinates_norm]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ComplexHausdorffTransport
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical coordinate chart is an isometry, including for the
Hausdorff-length measures on the full pointwise coarea levels. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def complexPlaneIsometry : EuclideanPlane ≃ᵢ ℂ where
  toEquiv := complexPlaneCoordinates.toEquiv
  isometry_toFun := by
    apply isometry_iff_dist_eq.mpr
    intro p q
    change dist (complexPlaneCoordinates p) (complexPlaneCoordinates q) = dist p q
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, complexPlaneCoordinates_norm]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_MollificationEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong mollification converges in Dirichlet energy on every measurable
source region. The limiting energy is that of the original weak field. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem planarMollification_energy_tendsto
    {u : EuclideanPlane → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u univ)
    (hs : HasCompactSupport u) (U : Set EuclideanPlane) :
    Tendsto (fun n => ∫ x in U,
      (fderiv ℝ (planarMollification u n) x (EuclideanSpace.single 0 1)) ^ 2 +
      (fderiv ℝ (planarMollification u n) x (EuclideanSpace.single 1 1)) ^ 2)
      atTop (𝓝 (∫ x in U, hu.weakGrad x 0 ^ 2 + hu.weakGrad x 1 ^ 2)) := by
  have hg (i : Fin 2) : MemLp (fun x => hu.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using hu.weakGrad_component_memLp i
  have hl (i : Fin 2) : Tendsto (fun n => eLpNorm (fun x =>
      fderiv ℝ (planarMollification u n) x (EuclideanSpace.single i 1) - hu.weakGrad x i)
      2 (volume.restrict U)) atTop (𝓝 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (planarMollification_tendsto_gradient_L2 hu i)
      (fun _ => bot_le) (fun _ => eLpNorm_mono_measure _ Measure.restrict_le_self)
  have ht (i : Fin 2) := integral_sq_tendsto_of_L2
    (fun n => (planarMollification_partial_memLp hu hs n i).restrict U)
    ((hg i).restrict U) (hl i)
  have hh := (ht 0).add (ht 1)
  simpa only [← integral_add ((hg 0).restrict U).integrable_sq ((hg 1).restrict U).integrable_sq,
    ← integral_add ((planarMollification_partial_memLp hu hs _ 0).restrict U).integrable_sq
      ((planarMollification_partial_memLp hu hs _ 1).restrict U).integrable_sq] using hh

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_HorizontalNullPair
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The companion trace pair with the ordinary horizontal coordinate.
The same proved level argument applies to the constant rotated homeomorphism. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def horizontalGradient (_ : EuclideanPlane) : EuclideanPlane :=
  WithLp.toLp 2 (fun i => if i = 0 then 1 else 0)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_LastEntryCircleLaw
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact probabilities of the collar arc events used in alternation. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

open scoped Classical in
noncomputable def lastEntryCircleLaw (μ : ProbabilityMeasure C(PathTime, X))
    (V : Set X) (χ : X → UnitAddCircle) : ProbabilityMeasure UnitAddCircle :=
  if h : AEMeasurable χ (lastEntryLaw μ V : Measure X) then (lastEntryLaw μ V).map h
  else (lastEntryLaw μ V).map (f := fun _ => (0 : UnitAddCircle)) aemeasurable_const

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CodeResidualAvoidance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The stored rational-interval constraints give null residual-incidence
envelopes under the actual square bounds on visits. -/

open Set Filter Function MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

def rationalStart : RationalPathTime := ⟨0, by norm_num⟩
def rationalEnd : RationalPathTime := ⟨1, by norm_num⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_TagPaymentMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local tag cost is an actual measure on parameter time: a
weighted physical-length part plus one atom for each flagged visit. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

def boundaryTimeMeasure {X : Type*} (γ : PathTime → X) (m : X → ℝ≥0∞) :
    Measure PathTime :=
  Measure.sum (fun t => m (γ t) • Measure.dirac t)

def tagPaymentMeasure {X : Type*} (μ : Measure PathTime) (g : PathTime → ℝ≥0∞)
    (γ : PathTime → X) (m : X → ℝ≥0∞) : Measure PathTime :=
  μ.withDensity g + boundaryTimeMeasure γ m

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CodePeriodGenericLevels
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The period-coordinate case of the generic prior-level theorem.
Local branches supply null free traces; intrinsic two-cut coarea controls
physical counts, and the actual dust budget controls flagged counts. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_15 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_RankedCodeTraces
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Generic prior-level intersections for a code whose natural labels carry
an independent inherited order. Physical coarea and local trace estimates
are unchanged; only the finite-tuple comparison uses the rank. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_16 : BorelSpace Sphere := ⟨rfl⟩


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothMeanCodeLevels
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Generic prior levels for the actual smoothed mean and its masked
coordinate. The atlas and its weight estimates are derived from that
coordinate, not supplied as a generic-intersection hypothesis. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_23 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SelectedLevelPresentation
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Presentations of selected real and mean coordinates, retaining
their functions, compact laws, and the data for subsequent code-law bounds. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_24 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RebasedLevelPresentations
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Adding a target or prior law changes the code space, but preserves the
actual selected coordinates and their real/mean presentations. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_25 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_RecursiveLawLevelEstimates
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A recursively selected positive law supplies the visit and deletion
estimates required by all earlier real and mean levels. No generic-level
assumption remains in this application. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_26 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RecursiveMeanCompatibility
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A recursive positive law gives compatibility for the next smoothed
mean. Generic prior intersections follow from its retained real and mean
data and candidate budgets. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_27 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_SelectableMeanLaw
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The recursive positive-law alternative constructs a selectable mean
coordinate with its concrete presentation. Finite compatibility is derived
from the preceding law estimates, while preserving the coordinate’s
Stokes budget and exclusion. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_28 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_AnalyticJordanCap
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analytic circle parametrizations of the actual compact Jordan holes.
The neighborhood and injectivity are retained so that a later
circularization has the proved local continuation. -/
open Set Function Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

def IsAnalyticJordanCap (H : ℂ ≃ₜ ℂ) : Prop :=
  ∃ (S : Set ℂ) (α : ℂ → ℂ) (c : ℂ) (r : ℝ), IsOpen S ∧ 0 < r ∧
    closedBall c r⊆S ∧ DifferentiableOn ℂ α S ∧ InjOn α S ∧
    α '' closedBall c r=closure (jordanInterior H)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereCoefficient
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel complex coefficient fields on the concrete sphere, with an explicit
value at infinity. -/
open Set Function MeasureTheory
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_8 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_RoundReflectionCoefficient
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual norm-preserving coefficient transport for circular reflection. -/
open Set Function MeasureTheory
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_9 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ComplexWeakDirectionalTransport
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport a complex distributional directional derivative to each real
component of the physical weak gradient. Only smooth compact tests and
local integrability enter this bridge. -/
open MeasureTheory Set Filter Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma weakPartial_of_complex_directional_identity
    {f V : ℂ → ℂ} (hf : LocallyIntegrable f volume)
    (hV : LocallyIntegrable V volume) (i : Fin 2) (v : ℂ)
    (hv : complexPlaneCoordinates (EuclideanSpace.single i 1) = v)
    (hweak : ∀ ψ : SchwartzMap ℂ ℂ, HasCompactSupport (ψ : ℂ → ℂ) →
      (∫ z, ψ z * V z) = -(∫ z, fderiv ℝ (ψ : ℂ → ℂ) z v * f z))
    (L : ℂ →L[ℝ] ℝ) :
    DeGiorgi.HasWeakPartialDeriv i (fun x => L (V (complexPlaneCoordinates x)))
      (fun x => L (f (complexPlaneCoordinates x))) univ := by
  intro φ hφ hs _
  let e := complexPlaneCoordinates
  let ψ : ℂ → ℂ := fun z => ((φ (e.symm z) : ℝ) : ℂ)
  have hψ : ContDiff ℝ (↑(⊤ : ENat)) ψ :=
    Complex.ofRealCLM.contDiff.comp (hφ.comp e.symm.contDiff)
  have hsψ : HasCompactSupport ψ :=
    (hs.comp_homeomorph e.symm.toHomeomorph).comp_left Complex.ofReal_zero
  let Φ : SchwartzMap ℂ ℂ := hsψ.toSchwartzMap hψ
  have hd (z : ℂ) : fderiv ℝ ψ z v =
      ((fderiv ℝ φ (e.symm z) (EuclideanSpace.single i 1) : ℝ) : ℂ) := by
    rw [show ψ = Complex.ofRealCLM ∘ (φ ∘ e.symm) from rfl,
      fderiv_comp z Complex.ofRealCLM.differentiableAt
        ((hφ.differentiable (by simp)).comp e.symm.differentiable).differentiableAt,
      Complex.ofRealCLM.fderiv,
      fderiv_comp z (hφ.differentiable (by simp)).differentiableAt
        e.symm.differentiableAt, e.symm.fderiv]
    change ((fderiv ℝ φ (e.symm z) (e.symm v) : ℝ) : ℂ) = _
    rw [← hv, ContinuousLinearEquiv.symm_apply_apply]
  have hderiv : Continuous (fun z => fderiv ℝ ψ z v) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsderiv : HasCompactSupport (fun z => fderiv ℝ ψ z v) :=
    hsψ.fderiv_apply ℝ v
  have hintV : Integrable (fun z => ψ z * V z) volume := by
    simpa only [smul_eq_mul] using
      hV.integrable_smul_left_of_hasCompactSupport hψ.continuous hsψ
  have hintf : Integrable (fun z => fderiv ℝ ψ z v * f z) volume := by
    simpa only [smul_eq_mul] using
      hf.integrable_smul_left_of_hasCompactSupport hderiv hsderiv
  have hw := congrArg L (hweak Φ hsψ)
  change L (∫ z, ψ z * V z) = L (-(∫ z, fderiv ℝ ψ z v * f z)) at hw
  rw [map_neg, ← L.integral_comp_comm hintV, ← L.integral_comp_comm hintf] at hw
  have ht (g : ℂ → ℝ) : (∫ x, g (e x)) = ∫ z, g z :=
    complexPlaneCoordinates_measurePreserving.integral_comp
      e.toHomeomorph.measurableEmbedding g
  have hVtransport : (∫ z, L (ψ z * V z)) =
      ∫ x, L (V (e x)) * φ x := by
    rw [← ht]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [ψ, ContinuousLinearEquiv.symm_apply_apply]
    rw [← Complex.real_smul, map_smul, smul_eq_mul, mul_comm]
  have hftransport : (∫ z, L (fderiv ℝ ψ z v * f z)) =
      ∫ x, L (f (e x)) * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    rw [← ht]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hd, ContinuousLinearEquiv.symm_apply_apply, ← Complex.real_smul,
      map_smul, smul_eq_mul, mul_comm]
  rw [hVtransport, hftransport] at hw
  simp only [Measure.restrict_univ]
  linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ComplexLocalSobolevTransport
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Package actual complex weak directional fields as the physical local
Sobolev witness required by the principal-map construction. -/
open MeasureTheory Set Filter Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma complex_memLp_physical_ball {g : ℂ → ℂ} {R : ℝ}
    (hg : MemLp g 2 (volume.restrict (Metric.ball 0 R))) :
    MemLp (g ∘ complexPlaneCoordinates) 2
      (volume.restrict (Metric.ball 0 R)) := by
  have hmp := complexPlaneCoordinates_measurePreserving.restrict_preimage_emb
    complexPlaneCoordinates.toHomeomorph.measurableEmbedding (Metric.ball 0 R)
  simpa only [complexPlaneCoordinates_preimage_ball] using hg.comp_measurePreserving hmp

def localWeakComplexOfDirectionalFields (f : ℂ → ℂ) (V : Fin 2 → ℂ → ℂ)
    (hf : LocallyIntegrable f volume) (hV : ∀ i, LocallyIntegrable (V i) volume)
    (hweak : ∀ i (ψ : SchwartzMap ℂ ℂ), HasCompactSupport (ψ : ℂ → ℂ) →
      (∫ z, ψ z * V i z) = -(∫ z, fderiv ℝ (ψ : ℂ → ℂ) z
        (complexPlaneCoordinates (EuclideanSpace.single i 1)) * f z))
    (hL : ∀ R i, MemLp (V i) 2 (volume.restrict (Metric.ball 0 R))) :
    PlaneLocalWeakComplex (fun x => f (complexPlaneCoordinates x)) where
  realGradient := fun x => WithLp.toLp 2 (fun i => (V i (complexPlaneCoordinates x)).re)
  imagGradient := fun x => WithLp.toLp 2 (fun i => (V i (complexPlaneCoordinates x)).im)
  real_weak := fun i => weakPartial_of_complex_directional_identity hf (hV i) i _ rfl
    (hweak i) Complex.reCLM
  imag_weak := fun i => weakPartial_of_complex_directional_identity hf (hV i) i _ rfl
    (hweak i) Complex.imCLM
  real_memLp := fun R i => Complex.reCLM.comp_memLp' (complex_memLp_physical_ball (hL R i))
  imag_memLp := fun R i => Complex.imCLM.comp_memLp' (complex_memLp_physical_ball (hL R i))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_PrincipalPhysicalWitness
attribute [-instance] _root_.ContinuousMap.measurableSpace
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the actual principal weak directional fields to the exact
physical Sobolev witness, retaining the real conjugate Beltrami equation. -/
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

 def principalWeakDirections (g : PlaneL2) (i : Fin 2) (z : ℂ) : ℂ :=
  complexPlaneCoordinates (EuclideanSpace.single i 1) +
    principalDirectionalCorrection g (complexPlaneCoordinates (EuclideanSpace.single i 1)) z

lemma principalWeakDirections_locallyIntegrable (g : PlaneL2) (i : Fin 2) :
    LocallyIntegrable (principalWeakDirections g i) volume :=
  (locallyIntegrable_const _).add ((Lp.memLp (principalDirectionalCorrection g
    (complexPlaneCoordinates (EuclideanSpace.single i 1)))).locallyIntegrable (by norm_num))

lemma principalWeakDirections_memLp (g : PlaneL2) (R : ℝ) (i : Fin 2) :
    MemLp (principalWeakDirections g i) 2 (volume.restrict (Metric.ball 0 R)) := by
  have : IsFiniteMeasure (volume.restrict (Metric.ball (0 : ℂ) R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  exact (memLp_const (complexPlaneCoordinates (EuclideanSpace.single i 1))).add
    ((Lp.memLp (principalDirectionalCorrection g
      (complexPlaneCoordinates (EuclideanSpace.single i 1)))).restrict _)

 def principalPhysicalWitness (H : ℂ ≃ₜ ℂ) (g : PlaneL2)
    (hw : ∀ (v : ℂ) (φ : SchwartzMap ℂ ℂ), HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, H z*fderiv ℝ (φ : ℂ → ℂ) z v) =
        -(∫ z, (v+principalDirectionalCorrection g v z)*φ z)) :
    PlaneLocalWeakComplex (fun x => H (complexPlaneCoordinates x)) :=
  localWeakComplexOfDirectionalFields H (principalWeakDirections g)
    H.continuous.locallyIntegrable (principalWeakDirections_locallyIntegrable g)
    (fun i φ hφ => by
      have h := hw (complexPlaneCoordinates (EuclideanSpace.single i 1)) φ hφ
      simp only [principalWeakDirections, mul_comm] at h ⊢
      linear_combination h)
    (principalWeakDirections_memLp g)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_ReflectionPrincipalSolution
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Solve the actual bounded, compact, reflection-invariant coefficient field.
The original coefficient is retained exactly on the circular exterior. -/
open Set Function Filter MeasureTheory
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_11 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_AnalyticReflectionData
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual data for finite analytic uniformization by invariant Beltrami
coefficients. Conformality of the straightened comparison and roundness of
its boundary images are not fields and remain to be proved. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer CannonBeltrami
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_12 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_AnalyticStraighteningHolomorphic
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Holomorphicity of the actual finite straightening. The smooth
approximants have an L2-small antiholomorphic derivative on every closed
source rectangle; their locally uniform limit therefore satisfies Morera. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_14 : BorelSpace Sphere := ⟨rfl⟩
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_PrincipalReflectionDefect
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual mollified coefficients' reflection defects are uniformly
bounded and tend almost everywhere to zero. The smooth conjugate's exact
antiholomorphic derivative is expressed using this defect. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_13 : BorelSpace Sphere := ⟨rfl⟩
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CountableJordanCollars
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single countable family of genuine Jordan collars is a neighborhood
basis at every finite dust point. Boundaries lie in the quotient domain. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

def quotientJordanDisk (K : ℂ ≃ₜ ℂ) : Set Sphere :=
  ((↑) : ℂ → Sphere) '' jordanInterior K

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JoinedPaths
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A binary continuous join with exact affine parametrizations of both
halves, for attaching collar tails to retained fragments. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X]

def joinedPath (γ δ : C(PathTime, X)) (h : γ ⊤ = δ ⊥) : C(PathTime, X) :=
  ((⟨γ, rfl, rfl⟩ : Path (γ ⊥) (γ ⊤)).trans (⟨δ, h.symm, rfl⟩ : Path (γ ⊤) (δ ⊤))).toContinuousMap

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RelativePlateauNeighborhoods
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Plateau refinement for relatively closed sets in the physical domain,
including terminal collars that reach deleted boundary components. -/

open Set
noncomputable section
namespace CircleDomainRigidity

def relativePlateauNeighborhood (D A V : Set EuclideanPlane)
    (x : EuclideanPlane) : Set EuclideanPlane := by
  classical
  exact if x ∈ A then V else D \ A

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_AtomicHitTests
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure
attribute [-simp] _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable and atomless tests control integration against any finite measure
whose point masses have square norm at most one. This supplies the test-measure
step in finite law splitting; the atomless remainder is the restriction away
from the actual positive point masses. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [SecondCountableTopology X] [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
theorem countable_positiveAtoms (ν : Measure X) [SFinite ν] : (positiveAtoms ν).Countable := by
  simpa [positiveAtoms] using
    (Measure.countable_meas_level_set_pos (μ := ν) (g := id) measurable_id)

omit [SecondCountableTopology X] [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
theorem nullSingleton_restrict_compl_positiveAtoms (ν : Measure X) :
    NullSingletonClass (ν.restrict (positiveAtoms ν)ᶜ) := by
  constructor
  intro x
  by_cases hx : x ∈ positiveAtoms ν
  · rw [Measure.restrict_apply (measurableSet_singleton x)]
    simp [hx]
  · have hzero : ν {x} = 0 := le_antisymm (not_lt.mp hx) bot_le
    exact le_antisymm ((Measure.restrict_le_self {x}).trans hzero.le) bot_le

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_GatedQuotientMap
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normalized map on the quotient domain. Its finite physical
formula is required only over the bounded target gate, which misses infinity. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

 def quotientNormalizedMap {G U : Set Sphere} (e : G ≃ₜ U) (F : ℂ → ℂ) : U → Sphere :=
  fun x => extendAtInfinity F (e.symm x).val

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SelectableRecursiveMean
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed recursive mean is compatible with the actual preceding
selected presentations. Its physical coordinate and open exclusion are retained. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_29 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ProtrusionAlternatives
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At a marked-component protrusion, either a small compatible real
barrier exists, or positive-law duality constructs a compatible mean
coordinate with an open sized exclusion. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_31 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ProtrusionTestAvailability
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local real/mean alternative gives an actual compatible open test
at every protruding marked component. All exclusion data are constructed. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_32 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_OrderedProtrusionAvailability
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local construction is available against the whole preceding
ordered family. Its auxiliary anchor and level code are removed from the
returned test, preserving the original physical data and open exclusion. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_33 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SelectedMarkedEndEquality
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coverage and the constructed local test rule out every protrusion at
a mandatory marked end of the actual selected mixed limit. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_34 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SelectedCircleDomain
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected mixed limit is a circle domain: its mandatory ends are the
exact selected disks, and the original graded real tests collapse all other ends. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_35 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RetainedCircleModel
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble the actual graded real seed, countable open exclusion selection,
common mixed models and their normal limit into a circle uniformization. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_36 : BorelSpace Sphere := ⟨rfl⟩

open FiniteTransfer

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RetainedScalarEstimates
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Energy and terminal oscillation estimates for the unchanged scalar tests
on the actual finite stages of the selected circle model. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_37 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RetainedScalarTails
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual retained planar exhaustion has vanishing original energy
outside it. The same finite models transfer this tail estimate to the target. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_38 : BorelSpace Sphere := ⟨rfl⟩
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_OpenGapIntegration
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint traces supplied by finite energy give the distributional error
for clipped scalar functions and constant fillings of finitely many gaps. -/
open Set Function Filter MeasureTheory
open scoped Topology
namespace CircleDomainRigidity

 theorem clipped_integration_by_parts_from_open_gaps
    (n : ℕ) (a b : Fin (n + 1) → ℝ) (f d : ℝ → ℝ)
    (value A : Fin n → ℝ) (φ : ℝ → ℝ) (C : ℝ)
    (hab : ∀ i, a i < b i)
    (hd : ∀ i x, x ∈ Ioo (a i) (b i) → HasDerivAt f (d x) x)
    (hi : ∀ i, IntervalIntegrable d volume (a i) (b i))
    (hφ : ContDiff ℝ 1 φ) (hzero : φ (a 0) = 0) (hone : φ (b (Fin.last n)) = 0)
    (hC : 0 ≤ C) (hA : ∀ i, 0 ≤ A i)
    (hleft : ∀ (i : Fin n) u,
      Tendsto f (𝓝[Ioo (a i.castSucc) (b i.castSucc)] (b i.castSucc)) (𝓝 u) →
      |u - value i| ≤ A i)
    (hright : ∀ (i : Fin n) u,
      Tendsto f (𝓝[Ioo (a i.succ) (b i.succ)] (a i.succ)) (𝓝 u) →
      |value i - u| ≤ A i)
    (hφleft : ∀ i : Fin n, |φ (b i.castSucc)| ≤ C)
    (hφright : ∀ i : Fin n, |φ (a i.succ)| ≤ C) :
    |(∑ i, ((∫ x in a i..b i, clipScalar (f x) * deriv φ x) +
      (∫ x in a i..b i, deriv (clipScalar ∘ f) x * φ x))) +
      (∑ i : Fin n, clipScalar (value i) * (φ (a i.succ) - φ (b i.castSucc)))| ≤
        2 * C * ∑ i, A i := by
  choose g hg heq hl hr using fun i =>
    exists_absolutelyContinuous_extension_of_integrable_derivative (hab i) (hd i) (hi i)
  have hclip (i : Fin (n + 1)) :
      AbsolutelyContinuousOnInterval (clipScalar ∘ g i) (a i) (b i) :=
    clipScalar_lipschitz.comp_absolutelyContinuousOnInterval (hg i)
  have hevent (i : Fin (n + 1)) (x : ℝ) (hx : x ∈ Ioo (a i) (b i)) :
      (clipScalar ∘ g i) =ᶠ[𝓝 x] (clipScalar ∘ f) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with z hz
    exact congrArg clipScalar (heq i hz)
  have hfun (i : Fin (n + 1)) :
      (∫ x in a i..b i, (clipScalar ∘ g i) x * deriv φ x) =
        ∫ x in a i..b i, clipScalar (f x) * deriv φ x := by
    rw [intervalIntegral.integral_of_le (hab i).le, intervalIntegral.integral_of_le (hab i).le,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo fun x hx => congrArg (fun v => v * deriv φ x) (hevent i x hx).eq_of_nhds
  have hderiv (i : Fin (n + 1)) :
      (∫ x in a i..b i, deriv (clipScalar ∘ g i) x * φ x) =
        ∫ x in a i..b i, deriv (clipScalar ∘ f) x * φ x := by
    rw [intervalIntegral.integral_of_le (hab i).le, intervalIntegral.integral_of_le (hab i).le,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo fun x hx => congrArg (fun v => v * φ x) (hevent i x hx).deriv_eq
  have hbound := integration_by_parts_with_filled_gaps n a b (fun i => clipScalar ∘ g i)
    (clipScalar ∘ value) A φ C hclip hφ hzero hone hC hA
    (fun i => (by
      have h := clipScalar_lipschitz.dist_le_mul (g i.castSucc (b i.castSucc)) (value i)
      simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
      exact h.trans (hleft i _ (hr i.castSucc))))
    (fun i => (by
      have h := clipScalar_lipschitz.dist_le_mul (value i) (g i.succ (a i.succ))
      simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
      exact h.trans (hright i _ (hl i.succ))))
    hφleft hφright
  simp_rw [hfun, hderiv] at hbound
  simpa only [comp_apply] using hbound

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_FilledGapIntegration
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-gap estimate as an integral of the actual filled function,
with its ordinary derivative off the finitely many jumps. -/
open Set Function Filter MeasureTheory
open scoped Topology
namespace CircleDomainRigidity

 theorem filled_gap_integration_bound
    (n : ℕ) (a b : Fin (n + 1) → ℝ) (f d F : ℝ → ℝ)
    (value A : Fin n → ℝ) (φ : ℝ → ℝ) (C : ℝ)
    (hab : ∀ i, a i < b i) (hholes : ∀ i : Fin n, b i.castSucc ≤ a i.succ)
    (hd : ∀ i x, x ∈ Ioo (a i) (b i) → HasDerivAt f (d x) x)
    (hi : ∀ i, IntervalIntegrable d volume (a i) (b i))
    (hF : ∀ i, EqOn F (clipScalar ∘ f) (Ioo (a i) (b i)))
    (hfill : ∀ i : Fin n, EqOn F (fun _ => clipScalar (value i))
      (Ioo (b i.castSucc) (a i.succ)))
    (hφ : ContDiff ℝ 1 φ) (hzero : φ (a 0) = 0) (hone : φ (b (Fin.last n)) = 0)
    (hint : Integrable (fun x => F x * deriv φ x))
    (hdint : Integrable (fun x => deriv F x * φ x))
    (hC : 0 ≤ C) (hA : ∀ i, 0 ≤ A i)
    (hleft : ∀ (i : Fin n) u,
      Tendsto f (𝓝[Ioo (a i.castSucc) (b i.castSucc)] (b i.castSucc)) (𝓝 u) →
      |u - value i| ≤ A i)
    (hright : ∀ (i : Fin n) u,
      Tendsto f (𝓝[Ioo (a i.succ) (b i.succ)] (a i.succ)) (𝓝 u) →
      |value i - u| ≤ A i)
    (hφleft : ∀ i : Fin n, |φ (b i.castSucc)| ≤ C)
    (hφright : ∀ i : Fin n, |φ (a i.succ)| ≤ C) :
    |(∫ x in a 0..b (Fin.last n), F x * deriv φ x) +
      (∫ x in a 0..b (Fin.last n), deriv F x * φ x)| ≤ 2 * C * ∑ i, A i := by
  have hgap₁ (i : Fin (n + 1)) :
      (∫ x in a i..b i, F x * deriv φ x) =
        ∫ x in a i..b i, clipScalar (f x) * deriv φ x :=
    intervalIntegral_congr_Ioo (hab i).le fun x hx =>
      congrArg (fun t => t * deriv φ x) (hF i hx)
  have hgap₂ (i : Fin (n + 1)) :
      (∫ x in a i..b i, deriv F x * φ x) =
        ∫ x in a i..b i, deriv (clipScalar ∘ f) x * φ x := by
    apply intervalIntegral_congr_Ioo (hab i).le
    intro x hx
    have he : F =ᶠ[𝓝 x] clipScalar ∘ f := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with z hz
      exact hF i hz
    exact congrArg (fun t => t * φ x) he.deriv_eq
  have hhole₁ (i : Fin n) :
      (∫ x in b i.castSucc..a i.succ, F x * deriv φ x) =
        clipScalar (value i) * (φ (a i.succ) - φ (b i.castSucc)) := by
    rw [intervalIntegral_congr_Ioo (hholes i)
      (fun x hx => congrArg (fun t => t * deriv φ x) (hfill i hx)),
      intervalIntegral.integral_const_mul]
    congr 1
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => (hφ.differentiable (by norm_num)).differentiableAt.hasDerivAt)
      ((hφ.continuous_deriv le_rfl).intervalIntegrable _ _)
  have hhole₂ (i : Fin n) :
      (∫ x in b i.castSucc..a i.succ, deriv F x * φ x) = 0 := by
    trans ∫ x in b i.castSucc..a i.succ, (0 : ℝ)
    · apply intervalIntegral_congr_Ioo (hholes i)
      intro x hx
      have he : F =ᶠ[𝓝 x] fun _ => clipScalar (value i) := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with z hz
        exact hfill i hz
      change deriv F x * φ x = 0
      rw [he.deriv_eq, deriv_const, zero_mul]
    · simp
  rw [← sum_integral_gaps_and_holes n a b (fun x => F x * deriv φ x)
      (fun _ => hint.intervalIntegrable) (fun _ => hint.intervalIntegrable),
    ← sum_integral_gaps_and_holes n a b (fun x => deriv F x * φ x)
      (fun _ => hdint.intervalIntegrable) (fun _ => hdint.intervalIntegrable)]
  simp_rw [hgap₁, hgap₂, hhole₁, hhole₂]
  rw [Finset.sum_const_zero, add_zero, add_right_comm,
    ← Finset.sum_add_distrib]
  exact clipped_integration_by_parts_from_open_gaps n a b f d value A φ C
    hab hd hi hφ hzero hone hC hA hleft hright hφleft hφright

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_OrderedHoleIntegration
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integration by parts for a bounded filling of actual ordered closed
intervals. Finite variation constructs every endpoint trace used below. -/
open Set Function Filter MeasureTheory
open scoped Topology
namespace CircleDomainRigidity

 theorem filled_integration_of_ordered_holes
    {n : ℕ} {a b : ℝ} (hab : a < b) (H : Fin n → ℝ × ℝ)
    (hinside : ∀ i, a < (H i).1 ∧ (H i).1 ≤ (H i).2 ∧ (H i).2 < b)
    (hsep : ∀ i j, i < j → (H i).2 < (H j).1)
    {f d F ρ : ℝ → ℝ} (value A : Fin n → ℝ)
    (hd : ∀ x ∈ Icc a b ∩ (⋃ i, Icc (H i).1 (H i).2)ᶜ, HasDerivAt f (d x) x)
    (hcd : ContinuousOn d (Icc a b ∩ (⋃ i, Icc (H i).1 (H i).2)ᶜ))
    (hρ : Integrable ρ)
    (hdom : ∀ x ∈ Icc a b ∩ (⋃ i, Icc (H i).1 (H i).2)ᶜ, |d x| ≤ ρ x)
    (hF : EqOn F (clipScalar ∘ f) (Icc a b ∩ (⋃ i, Icc (H i).1 (H i).2)ᶜ))
    (hfill : ∀ i, EqOn F (fun _ => clipScalar (value i)) (Icc (H i).1 (H i).2))
    (hcluster : ∀ i p u, p ∈ Icc (H i).1 (H i).2 →
      MapClusterPt u (𝓝[Icc a b ∩ (⋃ j, Icc (H j).1 (H j).2)ᶜ] p) f →
        |u - value i| ≤ A i)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hzero : φ a = 0) (hone : φ b = 0)
    (hint : Integrable (fun x => F x * deriv φ x))
    (hdint : Integrable (fun x => deriv F x * φ x))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, |φ x| ≤ C) (hA : ∀ i, 0 ≤ A i) :
    |(∫ x in a..b, F x * deriv φ x) + (∫ x in a..b, deriv F x * φ x)| ≤
      2 * C * ∑ i, A i := by
  let gap := gapsAfterHoles a b H
  let D := Icc a b ∩ (⋃ i, Icc (H i).1 (H i).2)ᶜ
  have hgap (i : Fin (n + 1)) : (gap i).1 < (gap i).2 :=
    gapsAfterHoles_strict hab H hinside hsep i
  have hgapD (i : Fin (n + 1)) : Ioo (gap i).1 (gap i).2 ⊆ D :=
    gapsAfterHoles_subset_residual H hinside hsep i
  have hgi (i : Fin (n + 1)) : IntervalIntegrable d volume (gap i).1 (gap i).2 := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (hgap i).le).mpr
    apply hρ.integrableOn.mono' ((hcd.mono (hgapD i)).aestronglyMeasurable measurableSet_Ioo)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simpa only [Real.norm_eq_abs] using hdom x (hgapD i hx)
  have hleft (i : Fin n) (u : ℝ)
      (hu : Tendsto f (𝓝[Ioo (gap i.castSucc).1 (gap i.castSucc).2]
        (gap i.castSucc).2) (𝓝 u)) : |u - value i| ≤ A i := by
    have : NeBot (𝓝[Ioo (gap i.castSucc).1 (gap i.castSucc).2] (gap i.castSucc).2) :=
      mem_closure_iff_nhdsWithin_neBot.mp (by
        rw [closure_Ioo (hgap i.castSucc).ne]
        exact right_mem_Icc.mpr (hgap i.castSucc).le)
    apply hcluster i (H i).1 u (left_mem_Icc.mpr (hinside i).2.1)
    simpa only [gap, gapsAfterHoles_castSucc_snd] using
      hu.mapClusterPt.mono (nhdsWithin_mono _ (hgapD i.castSucc))
  have hright (i : Fin n) (u : ℝ)
      (hu : Tendsto f (𝓝[Ioo (gap i.succ).1 (gap i.succ).2]
        (gap i.succ).1) (𝓝 u)) : |value i - u| ≤ A i := by
    have : NeBot (𝓝[Ioo (gap i.succ).1 (gap i.succ).2] (gap i.succ).1) :=
      mem_closure_iff_nhdsWithin_neBot.mp (by
        rw [closure_Ioo (hgap i.succ).ne]
        exact left_mem_Icc.mpr (hgap i.succ).le)
    rw [abs_sub_comm]
    apply hcluster i (H i).2 u (right_mem_Icc.mpr (hinside i).2.1)
    simpa only [gap, gapsAfterHoles_succ_fst] using
      hu.mapClusterPt.mono (nhdsWithin_mono _ (hgapD i.succ))
  have hb := filled_gap_integration_bound n (fun i => (gap i).1) (fun i => (gap i).2)
    f d F value A φ C hgap
    (by intro i; simpa only [gap, gapsAfterHoles_castSucc_snd, gapsAfterHoles_succ_fst] using (hinside i).2.1)
    (fun i x hx => hd x (hgapD i hx)) hgi (fun i => hF.mono (hgapD i))
    (by
      intro i x hx
      apply hfill i
      simpa only [gap, gapsAfterHoles_castSucc_snd, gapsAfterHoles_succ_fst] using Ioo_subset_Icc_self hx)
    hφ (by simpa only [gap, gapsAfterHoles_zero_fst] using hzero)
    (by simpa only [gap, gapsAfterHoles_last_snd] using hone)
    hint hdint hC hA hleft hright (fun _ => hbound _) (fun _ => hbound _)
  simpa only [gap, gapsAfterHoles_zero_fst, gapsAfterHoles_last_snd] using hb

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskLineIntegration
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distributional line error for constant-filled disjoint round disks.
The estimate charges only disks met by the line. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology
namespace CircleDomainRigidity

 theorem filled_line_integration_through_disks
    {I : Type*} [Fintype I] (c : I → ℂ) (r value A : I → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hA : ∀ i, 0 ≤ A i)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    {y a b : ℝ} (hab : a < b)
    (ha : a ∈ diskLineDomain c r y) (hb : b ∈ diskLineDomain c r y)
    {f F ρ : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (diskLineDomain c r y))
    (hρ : Integrable ρ)
    (hmajor : ∀ x ∈ Icc a b ∩ diskLineDomain c r y, |deriv f x| ≤ ρ x)
    (hF : EqOn F (clipScalar ∘ f) (diskLineDomain c r y))
    (hfill : ∀ i x, (⟨x, y⟩ : ℂ) ∈ closedBall (c i) (r i) → F x = clipScalar (value i))
    (hcluster : ∀ i p u, (⟨p, y⟩ : ℂ) ∈ closedBall (c i) (r i) →
      MapClusterPt u (𝓝[diskLineDomain c r y] p) f → |u - value i| ≤ A i)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hzero : φ a = 0) (hone : φ b = 0)
    (hint : Integrable (fun x => F x * deriv φ x))
    (hdint : Integrable (fun x => deriv F x * φ x))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, |φ x| ≤ C) :
    |(∫ x in a..b, F x * deriv φ x) + (∫ x in a..b, deriv F x * φ x)| ≤
      2 * C * ∑ i, (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y := by
  classical
  let K := crossingChords c r y a b
  let H := K.orderEmbOfFin (α := ℝ ×ₗ ℝ) rfl
  have hmem (j : Fin K.card) : H j ∈ K := K.orderEmbOfFin_mem (α := ℝ ×ₗ ℝ) rfl j
  have honto (z : ℝ × ℝ) (hz : z ∈ K) : ∃ j : Fin K.card, H j = z := by
    let z' : (K : Finset (ℝ ×ₗ ℝ)) := ⟨z, hz⟩
    refine ⟨(K.orderIsoOfFin (α := ℝ ×ₗ ℝ) rfl).symm z', ?_⟩
    exact congrArg Subtype.val ((K.orderIsoOfFin (α := ℝ ×ₗ ℝ) rfl).apply_symm_apply z')
  have hcover : (⋃ j, Icc (H j).1 (H j).2) = ⋃ z ∈ K, Icc z.1 z.2 := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact mem_iUnion₂.mpr ⟨H j, hmem j, hj⟩
    · intro hx
      obtain ⟨z, hz, hx⟩ := mem_iUnion₂.mp hx
      obtain ⟨j, rfl⟩ := honto z hz
      exact mem_iUnion.mpr ⟨j, hx⟩
  have howner (j : Fin K.card) : ∃ i, i ∈ crossingDisks c r y a b ∧
      horizontalChord (c i) (r i) y = H j := Finset.mem_image.mp (hmem j)
  choose owner howner heq using howner
  have hinside := crossingChords_inside c r hr
    (fun i hi => ha (mem_iUnion.mpr ⟨i, hi⟩))
    (fun i hi => hb (mem_iUnion.mpr ⟨i, hi⟩))
  have hsep := sorted_holes_separated K (fun z hz => (hinside z hz).2.1)
    (crossingChords_disjoint c r hr hdisj)
  let D := Icc a b ∩ (⋃ j, Icc (H j).1 (H j).2)ᶜ
  have hDU : D ⊆ diskLineDomain c r y := by
    intro x hx
    apply (crossingChords_domain c r hr hx.1).mp
    change x ∈ (⋃ z ∈ K, Icc z.1 z.2)ᶜ
    rw [← hcover]
    exact hx.2
  have hD := isOpen_diskLineDomain c r y
  have hchord (j : Fin K.card) {x : ℝ} (hx : x ∈ Icc (H j).1 (H j).2) :
      (⟨x, y⟩ : ℂ) ∈ closedBall (c (owner j)) (r (owner j)) := by
    apply (mem_closedBall_iff_mem_horizontalChord _ (hr _) (crossingDisk_line_hit (howner j))).mpr
    simpa only [heq j] using hx
  have hpay := filled_integration_of_ordered_holes hab H
    (fun j => hinside _ (hmem j)) hsep (fun j => value (owner j))
    (fun j => chordToll c r A y a b (H j))
    (fun x hx => (hf.contDiffAt (hD.mem_nhds (hDU hx))).differentiableAt (by norm_num) |>.hasDerivAt)
    ((hf.continuousOn_deriv_of_isOpen hD le_rfl).mono hDU) hρ
    (fun x hx => hmajor x ⟨hx.1, hDU hx⟩)
    (hF.mono hDU) (fun j x hx => hfill _ x (hchord j hx))
    (by
      intro j p u hp hu
      exact (hcluster (owner j) p u (hchord j hp)
        (hu.mono (nhdsWithin_mono _ hDU))).trans (by
          simpa only [heq j] using le_chordToll c r A y a b hA (howner j)))
    hφ hzero hone hint hdint hC hbound (fun j => (hA _).trans (by
      simpa only [heq j] using le_chordToll c r A y a b hA (howner j)))
  have hsum : (∑ j : Fin K.card, chordToll c r A y a b (H j)) =
      ∑ z ∈ K, chordToll c r A y a b z := by
    apply Finset.sum_bij (fun j _ => H j)
    · exact fun j _ => hmem j
    · exact fun i _ j _ hij => H.injective hij
    · intro z hz
      obtain ⟨j, hj⟩ := honto z hz
      exact ⟨j, Finset.mem_univ _, hj⟩
    · exact fun _ _ => rfl
  have hpaid := hpay.trans_eq (congrArg (fun t : ℝ => 2 * C * t) hsum)
  exact hpaid.trans (mul_le_mul_of_nonneg_left
    (sum_chordToll_le_line_hits c r A y a b hA) (mul_nonneg (by norm_num) hC))

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactLineJump
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactly supported tests turn the finite-interval jump estimate into
an estimate over the entire line. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology
namespace CircleDomainRigidity

 theorem filled_line_integration_through_disks_univ
    {I : Type*} [Fintype I] (c : I → ℂ) (r value A : I → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hA : ∀ i, 0 ≤ A i)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    {y a b : ℝ} (hab : a < b)
    (ha : a ∈ diskLineDomain c r y) (hb : b ∈ diskLineDomain c r y)
    {f F ρ : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (diskLineDomain c r y))
    (hρ : Integrable ρ)
    (hmajor : ∀ x ∈ Icc a b ∩ diskLineDomain c r y, |deriv f x| ≤ ρ x)
    (hF : EqOn F (clipScalar ∘ f) (diskLineDomain c r y))
    (hfill : ∀ i x, (⟨x, y⟩ : ℂ) ∈ closedBall (c i) (r i) → F x = clipScalar (value i))
    (hcluster : ∀ i p u, (⟨p, y⟩ : ℂ) ∈ closedBall (c i) (r i) →
      MapClusterPt u (𝓝[diskLineDomain c r y] p) f → |u - value i| ≤ A i)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hsupp : tsupport φ ⊆ Ioo a b)
    (hint : Integrable (fun x => F x * deriv φ x))
    (hdint : Integrable (fun x => deriv F x * φ x))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, |φ x| ≤ C) :
    |(∫ x, F x * deriv φ x) + (∫ x, deriv F x * φ x)| ≤
      2 * C * ∑ i, (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y := by
  have hzero : φ a = 0 := image_eq_zero_of_notMem_tsupport (by
    intro h; exact (lt_irrefl a) (hsupp h).1)
  have hone : φ b = 0 := image_eq_zero_of_notMem_tsupport (by
    intro h; exact (lt_irrefl b) (hsupp h).2)
  have hs₁ : support (fun x => F x * deriv φ x) ⊆ Ioc a b := by
    intro x hx
    have hder : x ∈ support (deriv φ) := by
      intro h
      exact hx (by simp [h])
    exact Ioo_subset_Ioc_self (hsupp (support_deriv_subset hder))
  have hs₂ : support (fun x => deriv F x * φ x) ⊆ Ioc a b := by
    intro x hx
    have hφx : x ∈ support φ := by
      intro h
      exact hx (by simp [h])
    exact Ioo_subset_Ioc_self (hsupp (subset_tsupport φ hφx))
  have h := filled_line_integration_through_disks c r value A hr hA hdisj hab ha hb
    hf hρ hmajor hF hfill hcluster hφ hzero hone hint hdint hC hbound
  simpa only [intervalIntegral.integral_eq_integral_of_support_subset hs₁,
    intervalIntegral.integral_eq_integral_of_support_subset hs₂] using h

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PlanarFilledJump
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Planar integration of the actual disk-filling errors. A locally
integrable gradient majorant is used only on the square containing the test. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology
namespace CircleDomainRigidity

 theorem planar_filled_horizontal_jump_of_density
    {I : Type*} [Fintype I] (c : I → ℂ) (r value A : I → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hA : ∀ i, 0 ≤ A i)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    {L : ℝ} (hL : 0 < L) (hsub : ∀ i, closedBall (c i) (r i) ⊆ ball 0 L)
    {v F ρ G : ℂ → ℝ}
    (hv : ContDiffOn ℝ 1 v (⋃ i, closedBall (c i) (r i))ᶜ)
    (hρ : Integrable ρ)
    (hmajor : ∀ z ∈ (⋃ i, closedBall (c i) (r i))ᶜ,
      |z.re| ≤ L → |z.im| ≤ L → euclideanGradientNorm v z ≤ ρ z)
    (hF : EqOn F (clipScalar ∘ v) (⋃ i, closedBall (c i) (r i))ᶜ)
    (hfill : ∀ i, EqOn F (fun _ => clipScalar (value i)) (closedBall (c i) (r i)))
    (hcluster : ∀ i p t, p ∈ closedBall (c i) (r i) →
      MapClusterPt t (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] p) v → |t - value i| ≤ A i)
    (hrep : ∀ᵐ z ∂(volume : Measure ℂ),
      deriv (F ∘ horizontalLine z.im) z.re = G z)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hsupp : tsupport φ ⊆ ball 0 L)
    (hint : Integrable (fun z => F z * fderiv ℝ φ z 1))
    (hdint : Integrable (fun z => G z * φ z))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ z, |φ z| ≤ C) :
    |(∫ z, F z * fderiv ℝ φ z 1) + (∫ z, G z * φ z)| ≤
      4 * C * ∑ i, r i * A i := by
  let e := Complex.equivRealProdCLM.symm
  have hmp := Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  let f : ℝ × ℝ → ℝ := fun p => F (e p) * fderiv ℝ φ (e p) 1
  let g : ℝ × ℝ → ℝ := fun p => G (e p) * φ (e p)
  have hf : Integrable f := (hmp.integrable_comp hint.aestronglyMeasurable).mpr hint
  have hg : Integrable g := (hmp.integrable_comp hdint.aestronglyMeasurable).mpr hdint
  have hρp : Integrable (fun p : ℝ × ℝ => ρ (e p)) :=
    (hmp.integrable_comp hρ.aestronglyMeasurable).mpr hρ
  have hp : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)),
      deriv (F ∘ horizontalLine p.2) p.1 = G (e p) :=
    hmp.quasiMeasurePreserving.ae hrep
  rw [Measure.volume_eq_prod] at hp
  have hpy := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hp)
  have hU : IsOpen (⋃ i, closedBall (c i) (r i))ᶜ :=
    (isClosed_iUnion_of_finite (fun _ => isClosed_closedBall)).isOpen_compl
  have hφd (x y : ℝ) : deriv (φ ∘ horizontalLine y) x = fderiv ℝ φ (horizontalLine y x) 1 :=
    ((hφ.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp_hasDerivAt x
      (hasDerivAt_horizontalLine x y)).deriv
  have hsline (y : ℝ) : tsupport (φ ∘ horizontalLine y) ⊆ Ioo (-L) L := by
    intro x hx
    have hz := hsupp (tsupport_comp_subset_preimage φ (continuous_horizontalLine y) hx)
    have ha : |x| < L := (Complex.abs_re_le_norm (horizontalLine y x)).trans_lt
      (by simpa only [mem_ball, dist_zero_right, horizontalLine] using hz)
    exact abs_lt.mp ha
  have hend (y : ℝ) (x : ℝ) (hx : |x| = L) : x ∈ diskLineDomain c r y := by
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    have hz := hsub j hj
    have ha := Complex.abs_re_le_norm (horizontalLine y x)
    have hb : ‖horizontalLine y x‖ < L := by simpa only [mem_ball, dist_zero_right, horizontalLine] using hz
    change |x| ≤ _ at ha
    rw [hx] at ha
    exact (not_lt_of_ge ha) hb
  have hline : ∀ᵐ y : ℝ,
      |(∫ x : ℝ, f (x, y)) + (∫ x : ℝ, g (x, y))| ≤
        2 * C * ∑ j, (Icc ((c j).im - r j) ((c j).im + r j)).indicator (fun _ => A j) y := by
    filter_upwards [hf.prod_left_ae, hg.prod_left_ae, hρp.prod_left_ae, hpy] with y hfy hgy hρy hry
    by_cases hy : y ∈ Icc (-L) L
    · have h₁ : (∫ x, (F ∘ horizontalLine y) x * deriv (φ ∘ horizontalLine y) x) =
          ∫ x, f (x, y) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x =>
          congrArg (fun t => F (horizontalLine y x) * t) (hφd x y)
      have h₂ : (∫ x, deriv (F ∘ horizontalLine y) x * (φ ∘ horizontalLine y) x) =
          ∫ x, g (x, y) := by
        apply integral_congr_ae
        filter_upwards [hry] with x hx
        exact congrArg (fun t => t * φ (horizontalLine y x)) hx
      have hi₁ : Integrable (fun x => (F ∘ horizontalLine y) x * deriv (φ ∘ horizontalLine y) x) := by
        apply hfy.congr
        exact Eventually.of_forall fun x =>
          congrArg (fun t => F (horizontalLine y x) * t) (hφd x y).symm
      have hi₂ : Integrable (fun x => deriv (F ∘ horizontalLine y) x * (φ ∘ horizontalLine y) x) := by
        apply hgy.congr
        filter_upwards [hry] with x hx
        exact congrArg (fun t => t * φ (horizontalLine y x)) hx.symm
      have ht := filled_line_integration_through_disks_univ c r value A hr hA hdisj
        (by linarith : -L < L) (hend y (-L) (by rw [abs_neg, abs_of_pos hL]))
        (hend y L (abs_of_pos hL))
        (hv.comp (contDiff_horizontalLine y).contDiffOn (fun _ hx => hx)) hρy
        (by
          intro x hx
          exact (horizontal_derivative_le_gradient
            ((hv.contDiffAt (hU.mem_nhds hx.2)).differentiableAt (by norm_num))).trans
            (hmajor _ hx.2 (abs_le.mpr hx.1) (abs_le.mpr hy)))
        (fun x hx => hF hx) (fun j x hx => hfill j hx)
        (fun j p t hp ht => hcluster j _ t hp (horizontal_cluster_is_planar ht))
        (hφ.comp (contDiff_horizontalLine y)) (hsline y) hi₁ hi₂ hC (fun x => hbound _)
      change |(∫ x, (F ∘ horizontalLine y) x * deriv (φ ∘ horizontalLine y) x) +
        (∫ x, deriv (F ∘ horizontalLine y) x * (φ ∘ horizontalLine y) x)| ≤ _ at ht
      rw [h₁, h₂] at ht
      exact ht
    · have hz (x : ℝ) : horizontalLine y x ∉ tsupport φ := by
        intro hx
        have hn : |y| < L := (Complex.abs_im_le_norm (horizontalLine y x)).trans_lt
          (by simpa only [mem_ball, dist_zero_right] using hsupp hx)
        exact hy ⟨(abs_lt.mp hn).1.le, (abs_lt.mp hn).2.le⟩
      have hfzero (x : ℝ) : f (x, y) = 0 := by
        change F _ * fderiv ℝ φ (horizontalLine y x) 1 = 0
        rw [fderiv_of_notMem_tsupport ℝ (hz x), zero_apply, mul_zero]
      have hgzero (x : ℝ) : g (x, y) = 0 := by
        change _ * φ (horizontalLine y x) = 0
        rw [image_eq_zero_of_notMem_tsupport (hz x), mul_zero]
      simp only [hfzero, hgzero, integral_zero, zero_add, abs_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) hC)
        (Finset.sum_nonneg fun j _ => indicator_nonneg (fun _ _ => hA j) y)
  have hb := integral_bound_of_parallel_disk_errors c r A hr C hf hg hline
  have hfint : (∫ p, f p) = ∫ z, F z * fderiv ℝ φ z 1 := hmp.integral_comp' (fun z : ℂ => F z * fderiv ℝ φ z 1)
  have hgint : (∫ p, g p) = ∫ z, G z * φ z := hmp.integral_comp' (fun z : ℂ => G z * φ z)
  rw [hfint, hgint] at hb
  exact hb

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_VerticalFilledJump
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-disk distributional estimate in the second coordinate,
obtained by the measure-preserving interchange of the two axes. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology
namespace CircleDomainRigidity

 theorem planar_filled_vertical_jump
    {I : Type*} [Fintype I] (c : I → ℂ) (r value A : I → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hA : ∀ i, 0 ≤ A i)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    {L : ℝ} (hL : 0 < L) (hsub : ∀ i, closedBall (c i) (r i) ⊆ ball 0 L)
    {v F G : ℂ → ℝ}
    (hv : ContDiffOn ℝ 1 v (⋃ i, closedBall (c i) (r i))ᶜ)
    (he : IntegrableOn (euclideanGradientEnergy v) (⋃ i, closedBall (c i) (r i))ᶜ)
    (hF : EqOn F (clipScalar ∘ v) (⋃ i, closedBall (c i) (r i))ᶜ)
    (hfill : ∀ i, EqOn F (fun _ => clipScalar (value i)) (closedBall (c i) (r i)))
    (hcluster : ∀ i p t, p ∈ closedBall (c i) (r i) →
      MapClusterPt t (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] p) v → |t - value i| ≤ A i)
    (hrep : ∀ᵐ z ∂(volume : Measure ℂ), deriv (F ∘ verticalLine z.re) z.im = G z)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hsupp : tsupport φ ⊆ ball 0 L)
    (hint : Integrable (fun z => F z * fderiv ℝ φ z Complex.I))
    (hdint : Integrable (fun z => G z * φ z))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ z, |φ z| ≤ C) :
    |(∫ z, F z * fderiv ℝ φ z Complex.I) + (∫ z, G z * φ z)| ≤
      4 * C * ∑ i, r i * A i := by
  let U := (⋃ i, closedBall (c i) (r i))ᶜ
  let V := (⋃ i, closedBall (axisSwap (c i)) (r i))ᶜ
  have hswap : MeasurePreserving axisSwap (volume : Measure ℂ) volume := axisSwap.measurePreserving
  have hU : IsOpen U := (isClosed_iUnion_of_finite fun _ => isClosed_closedBall).isOpen_compl
  have hVU : V = axisSwap ⁻¹' U := by
    simp only [V, U, preimage_compl, preimage_iUnion, axisSwap_preimage_closedBall]
  have hV : IsOpen V := hVU ▸ hU.preimage axisSwap.continuous
  have hvV : ContDiffOn ℝ 1 (v ∘ axisSwap) V := by
    rw [hVU]
    exact hv.comp axisSwap.toContinuousLinearEquiv.contDiff.contDiffOn (fun _ hx => hx)
  have heV : IntegrableOn (euclideanGradientEnergy (v ∘ axisSwap)) V := by
    rw [hVU]
    exact (integral_energy_axisSwap hU hv he).1
  obtain ⟨ρ, hρ, hmajor⟩ := exists_integrable_gradient_majorant_on_square hV heV hL.le
  have hdisjV : Pairwise (Disjoint on fun i => closedBall (axisSwap (c i)) (r i)) := by
    intro i j hij
    simpa only [axisSwap_preimage_closedBall] using (hdisj hij).preimage axisSwap
  have hball (i : I) {z : ℂ} (hz : z ∈ closedBall (axisSwap (c i)) (r i)) :
      axisSwap z ∈ closedBall (c i) (r i) := by
    change z ∈ axisSwap ⁻¹' closedBall (c i) (r i)
    rwa [axisSwap_preimage_closedBall]
  have hsubV (i : I) : closedBall (axisSwap (c i)) (r i) ⊆ ball 0 L := by
    intro z hz
    have hb := hsub i (hball i hz)
    simpa only [mem_ball, dist_zero_right, axisSwap.norm_map] using hb
  have hFV : EqOn (F ∘ axisSwap) (clipScalar ∘ (v ∘ axisSwap)) V := by
    intro z hz
    apply hF
    change z ∈ axisSwap ⁻¹' U
    rw [← hVU]
    exact hz
  have hfillV (i : I) : EqOn (F ∘ axisSwap) (fun _ => clipScalar (value i))
      (closedBall (axisSwap (c i)) (r i)) := fun z hz => hfill i (hball i hz)
  have hclusterV : ∀ i p t, p ∈ closedBall (axisSwap (c i)) (r i) →
      MapClusterPt t (𝓝[V] p) (v ∘ axisSwap) → |t - value i| ≤ A i := by
    intro i p t hp ht
    apply hcluster i (axisSwap p) t (hball i hp)
    apply MapClusterPt.of_comp _ ht
    rw [hVU]
    exact tendsto_nhdsWithin_iff.mpr
      ⟨axisSwap.continuous.continuousAt.mono_left nhdsWithin_le_nhds, self_mem_nhdsWithin⟩
  have hrepV : ∀ᵐ z ∂(volume : Measure ℂ),
      deriv ((F ∘ axisSwap) ∘ horizontalLine z.im) z.re = (G ∘ axisSwap) z := by
    filter_upwards [hswap.quasiMeasurePreserving.ae hrep] with z hz
    have hf : (F ∘ axisSwap) ∘ horizontalLine z.im = F ∘ verticalLine z.im := by
      funext x
      simp only [comp_apply, axisSwap_horizontalLine]
    simpa only [hf, axisSwap_re, axisSwap_im, comp_apply] using hz
  have hφd (z : ℂ) : fderiv ℝ (φ ∘ axisSwap) z 1 =
      fderiv ℝ φ (axisSwap z) Complex.I := by
    have hd := ((hφ.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp z
      axisSwap.hasFDerivAt).fderiv
    rw [hd]
    change fderiv ℝ φ (axisSwap z) (axisSwap 1) = _
    rw [axisSwap_one]
  have hsV : tsupport (φ ∘ axisSwap) ⊆ ball 0 L := by
    intro z hz
    have hb := hsupp (tsupport_comp_subset_preimage φ axisSwap.continuous hz)
    simpa only [mem_ball, dist_zero_right, axisSwap.norm_map] using hb
  have hiV : Integrable (fun z => (F ∘ axisSwap) z * fderiv ℝ (φ ∘ axisSwap) z 1) := by
    simp only [comp_apply, hφd]
    exact hswap.integrable_comp_of_integrable hint
  have hgV : Integrable (fun z => (G ∘ axisSwap) z * (φ ∘ axisSwap) z) :=
    hswap.integrable_comp_of_integrable hdint
  have h := planar_filled_horizontal_jump_of_density (fun i => axisSwap (c i)) r value A
    hr hA hdisjV hL hsubV hvV hρ hmajor hFV hfillV hclusterV hrepV
    (hφ.comp axisSwap.toContinuousLinearEquiv.contDiff) hsV hiV hgV hC
    (fun z => hbound (axisSwap z))
  change |(∫ z, (F ∘ axisSwap) z * fderiv ℝ (φ ∘ axisSwap) z 1) +
    (∫ z, (G ∘ axisSwap) z * (φ ∘ axisSwap) z)| ≤ _ at h
  simp_rw [hφd] at h
  simp only [comp_apply] at h
  have he₁ : (∫ z, F (axisSwap z) * fderiv ℝ φ (axisSwap z) Complex.I) =
      ∫ z, F z * fderiv ℝ φ z Complex.I := hswap.integral_comp axisSwap.toMeasurableEquiv.measurableEmbedding (fun z : ℂ => F z * fderiv ℝ φ z Complex.I)
  have he₂ : (∫ z, G (axisSwap z) * φ (axisSwap z)) =
      ∫ z, G z * φ z := hswap.integral_comp axisSwap.toMeasurableEquiv.measurableEmbedding (fun z : ℂ => G z * φ z)
  rw [he₁, he₂] at h
  exact h

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_BoundedSobolevChain
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth scalar composition for the bounded, compactly supported
Sobolev functions needed by the local range argument. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem bounded_sobolev_chain_rule_Icc
    {u : EuclideanPlane → ℝ} (hw : DeGiorgi.MemW1pWitness 2 u univ)
    (hsu : HasCompactSupport u) {a b : ℝ} (hu : ∀ x, u x ∈ Icc a b) {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (i : Fin 2) :
    DeGiorgi.HasWeakPartialDeriv i (fun x => deriv F (u x) * hw.weakGrad x i)
      (F ∘ u) univ := by
  have huL : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using hw.memLp
  have hgi : MemLp (fun x => hw.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using hw.weakGrad_component_memLp i
  let un := planarMollification u
  have hb (n : ℕ) (x : EuclideanPlane) : un n x ∈ Icc a b :=
    planarMollification_mem_Icc huL.aestronglyMeasurable hu n x
  have hsm (n : ℕ) : ContDiff ℝ 1 (un n) :=
    (planarMollification_smooth (huL.locallyIntegrable (by norm_num)) n).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn hF.continuous.continuousOn
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn
    (hF.continuous_deriv le_rfl).continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg (F (u 0))).trans (hB (u 0) (hu 0))
  have hC0 : 0 ≤ C := (norm_nonneg (deriv F (u 0))).trans (hC (u 0) (hu 0))
  have hmeasure : TendstoInMeasure volume un atTop u :=
    tendstoInMeasure_of_tendsto_eLpNorm (hf := fun n => (hsm n).continuous.aestronglyMeasurable)
      (hg := huL.aestronglyMeasurable) (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (planarMollification_tendsto_L2 huL)
  obtain ⟨σ, hσ, hae⟩ := hmeasure.exists_seq_tendsto_ae
  intro φ hφ hs hsub
  let v : EuclideanPlane := EuclideanSpace.single i 1
  have hdφ : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsdφ : HasCompactSupport (fun x => fderiv ℝ φ x v) := hs.fderiv_apply (𝕜 := ℝ) v
  have hleft := tendsto_integral_of_dominated_convergence
    (F := fun n x => F (un (σ n) x) * fderiv ℝ φ x v)
    (f := fun x => F (u x) * fderiv ℝ φ x v)
    (fun x => B * ‖fderiv ℝ φ x v‖)
    (fun n => ((hF.comp (hsm (σ n))).continuous.aestronglyMeasurable).mul
      hdφ.aestronglyMeasurable)
    ((hdφ.integrable_of_hasCompactSupport hsdφ).norm.const_mul B)
    (fun n => Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hB _ (hb _ x)) (norm_nonneg _))
    (by filter_upwards [hae] with x hx
        exact ((hF.continuous.tendsto _).comp hx).mul_const _)
  have hright := tendsto_integral_bounded_mul_L2
    (g := fun n x => fderiv ℝ (un (σ n)) x v)
    (G := fun x => hw.weakGrad x i)
    (h := fun n x => deriv F (un (σ n) x))
    (H := fun x => deriv F (u x))
    (φ := φ)
    (fun n => by
      have hd : Continuous (fun x => fderiv ℝ (un (σ n)) x v) :=
        ((hsm (σ n)).continuous_fderiv one_ne_zero).clm_apply continuous_const
      exact hd.memLp_of_hasCompactSupport
        ((planarMollification_hasCompactSupport hsu (σ n)).fderiv_apply (𝕜 := ℝ) v))
    hgi (hφ.continuous.memLp_of_hasCompactSupport hs)
    ((planarMollification_tendsto_gradient_L2 hw i).comp hσ.tendsto_atTop)
    (fun n => ((hF.continuous_deriv le_rfl).comp (hsm (σ n)).continuous).aestronglyMeasurable)
    hC0 (fun n => Eventually.of_forall fun x => hC _ (hb _ x))
    (by filter_upwards [hae] with x hx
        exact ((hF.continuous_deriv le_rfl).tendsto _).comp hx)
  have heq (n : ℕ) :
      (∫ x, F (un (σ n) x) * fderiv ℝ φ x v) =
        -(∫ x, deriv F (un (σ n) x) * fderiv ℝ (un (σ n)) x v * φ x) := by
    have hi := DeGiorgi.HasWeakPartialDeriv.of_contDiff (i := i) isOpen_univ
      (hF.comp (hsm (σ n))) φ hφ hs hsub
    simp only [Measure.restrict_univ] at hi
    have he (x : EuclideanPlane) : fderiv ℝ (F ∘ un (σ n)) x v =
        deriv F (un (σ n) x) * fderiv ℝ (un (σ n)) x v := by
      have hd := (hF.differentiable one_ne_zero (un (σ n) x)).hasDerivAt.comp_hasFDerivAt x
        ((hsm (σ n)).differentiable one_ne_zero x).hasFDerivAt
      simpa only [smul_apply, smul_eq_mul] using
        congrArg (fun L : EuclideanPlane →L[ℝ] ℝ => L v) hd.fderiv
    change (∫ x, F (un (σ n) x) * fderiv ℝ φ x v) =
      -(∫ x, fderiv ℝ (F ∘ un (σ n)) x v * φ x) at hi
    simpa only [he] using hi
  simp only [Measure.restrict_univ]
  exact tendsto_nhds_unique hleft (by simpa only [heq] using hright.neg)

 theorem bounded_sobolev_chain_rule
    {u : EuclideanPlane → ℝ} (hw : DeGiorgi.MemW1pWitness 2 u univ)
    (hsu : HasCompactSupport u) (hu : ∀ x, u x ∈ Icc 0 1) {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (i : Fin 2) :
    DeGiorgi.HasWeakPartialDeriv i (fun x => deriv F (u x) * hw.weakGrad x i)
      (F ∘ u) univ := bounded_sobolev_chain_rule_Icc hw hsu hu hF i

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ZeroWeakGradient
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compactly supported planar Sobolev function whose weak gradient
vanishes is zero, by positive mollification. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal Convolution
noncomputable section
namespace CircleDomainRigidity

theorem zero_of_compact_support_zero_weak_gradient
    {u : EuclideanPlane → ℝ} (hw : DeGiorgi.MemW1pWitness 2 u univ)
    (hs : HasCompactSupport u)
    (hg : ∀ i : Fin 2, (fun x => hw.weakGrad x i) =ᵐ[volume] 0) :
    u =ᵐ[volume] 0 := by
  have hu : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using hw.memLp
  have hzero (n : ℕ) : planarMollification u n = 0 := by
    have hd (x : EuclideanPlane) : fderiv ℝ (planarMollification u n) x = 0 := by
      have heq : (fderiv ℝ (planarMollification u n) x).toLinearMap = 0 := by
        apply (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.ext
        intro i
        change (fderiv ℝ (planarMollification u n) x)
          ((EuclideanSpace.basisFun (Fin 2) ℝ) i) = 0
        rw [EuclideanSpace.basisFun_apply, planarMollification_derivative hw]
        have he := convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ)
          (EventuallyEq.refl (ae volume) ((DeGiorgi.shrinkingBump (d := 2) n).normed volume)) (hg i)
        rw [he, convolution_zero]
        rfl
      ext y
      exact LinearMap.congr_fun heq y
    have hc := planarMollification_hasCompactSupport hs n
    obtain ⟨y, hy⟩ : ∃ y, y ∉ tsupport (planarMollification u n) :=
      (Set.ne_univ_iff_exists_notMem _).mp hc.isCompact.ne_univ
    funext x
    exact (is_const_of_fderiv_eq_zero
      ((planarMollification_smooth (hu.locallyIntegrable (by norm_num)) n).differentiable
        (by simp)) hd x y).trans (image_eq_zero_of_notMem_tsupport hy)
  have ht := planarMollification_tendsto_L2 hu
  simp only [hzero, Pi.zero_apply, zero_sub] at ht
  change Tendsto (fun _ : ℕ => eLpNorm (-u) 2 volume) atTop (𝓝 0) at ht
  rw [eLpNorm_neg] at ht
  exact (eLpNorm_eq_zero_iff hu.aestronglyMeasurable (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp
    (tendsto_nhds_unique tendsto_const_nhds ht)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevRangeBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weak gradient cannot support an excess range hidden on a set
where that gradient vanishes. This will identify values on point dust. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

theorem ae_le_of_compact_sobolev_gradient_zero_above
    {u : EuclideanPlane → ℝ} (hw : DeGiorgi.MemW1pWitness 2 u univ)
    (hs : HasCompactSupport u) (hu : ∀ x, u x ∈ Icc 0 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hg : ∀ i : Fin 2, ∀ᵐ x ∂volume, b < u x → hw.weakGrad x i = 0) :
    ∀ᵐ x ∂volume, u x ≤ b := by
  let F : ℝ → ℝ := fun t => Real.smoothTransition (t - b)
  have hF : ContDiff ℝ 1 F := Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)
  have hF0 : F 0 = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
  have hFs : HasCompactSupport (F ∘ u) := hs.comp_left hF0
  have huL : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using hw.memLp
  have hm : AEStronglyMeasurable (F ∘ u) volume :=
    hF.continuous.comp_aestronglyMeasurable huL.aestronglyMeasurable
  have hL : MemLp (F ∘ u) 2 volume := by
    let K := tsupport (F ∘ u)
    let : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.mpr hFs.isCompact.measure_lt_top.ne
    have ht : MemLp (F ∘ u) 2 (volume.restrict K) :=
      MemLp.of_bound hm.restrict 1 (Eventually.of_forall fun x => by
        change ‖Real.smoothTransition (u x - b)‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
        exact Real.smoothTransition.le_one _)
    have he : K.indicator (F ∘ u) = F ∘ u := by
      funext x
      by_cases hx : x ∈ K
      · exact indicator_of_mem hx _
      · rw [indicator_of_notMem hx]
        exact (image_eq_zero_of_notMem_tsupport hx).symm
    rw [← he]
    exact (memLp_indicator_iff_restrict hFs.isCompact.isClosed.measurableSet).mpr ht
  have hd (t : ℝ) (ht : t ≤ b) : deriv F t = 0 := by
    apply IsLocalMin.deriv_eq_zero
    apply Eventually.of_forall
    intro y
    change F t ≤ F y
    have hz : F t = 0 := Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr ht)
    rw [hz]
    exact Real.smoothTransition.nonneg _
  have hgrad (i : Fin 2) :
      (fun x => deriv F (u x) * hw.weakGrad x i) =ᵐ[volume] 0 := by
    filter_upwards [hg i] with x hx
    by_cases ht : b < u x
    · simp only [hx ht, mul_zero, Pi.zero_apply]
    · simp only [hd _ (le_of_not_gt ht), zero_mul, Pi.zero_apply]
  let hW : DeGiorgi.MemW1pWitness 2 (F ∘ u) univ := {
    memLp := by simpa only [Measure.restrict_univ] using hL
    weakGrad := 0
    weakGrad_component_memLp := by
      intro i
      simp
    isWeakGrad := by
      intro i φ hφ hφs hφsub
      have ht := bounded_sobolev_chain_rule hw hs hu hF i φ hφ hφs hφsub
      have hi : (∫ x in univ, deriv F (u x) * hw.weakGrad x i * φ x) = 0 := by
        simp only [Measure.restrict_univ]
        apply integral_eq_zero_of_ae
        filter_upwards [hgrad i] with x hx
        change deriv F (u x) * hw.weakGrad x i = 0 at hx
        simp only [hx, zero_mul, Pi.zero_apply]
      rw [hi, neg_zero] at ht
      simpa using ht }
  have hz := zero_of_compact_support_zero_weak_gradient hW hFs
    (fun _ => Eventually.of_forall fun _ => rfl)
  filter_upwards [hz] with x hx
  exact sub_nonpos.mp (Real.smoothTransition.zero_iff_nonpos.mp hx)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_BoundedCompactCutoff
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact smooth cutoff of a bounded weakly differentiable scalar,
with its actual product-rule gradient retained. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem locallyIntegrable_of_unit_bound {f : EuclideanPlane → ℝ}
    (hm : AEStronglyMeasurable f volume) (hf : ∀ x, f x ∈ Icc 0 1) :
    LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  apply (MemLp.of_bound (p := (2 : ℝ≥0∞)) hm.restrict 1 ?_).integrable (by norm_num)
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hf x).1]
    exact (hf x).2

 def boundedCompactCutoffWitness
    {f : EuclideanPlane → ℝ} {G : EuclideanPlane → EuclideanPlane}
    (hm : AEStronglyMeasurable f volume) (hf : ∀ x, f x ∈ Icc 0 1)
    (hG : ∀ i : Fin 2, MemLp (fun x => G x i) 2 volume)
    (hw : DeGiorgi.HasWeakGrad G f univ)
    {η : EuclideanPlane → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hs : HasCompactSupport η) :
    DeGiorgi.MemW1pWitness 2 (fun x => η x * f x) univ where
  memLp := by
    simp only [Measure.restrict_univ]
    apply (hη.continuous.memLp_of_hasCompactSupport hs : MemLp η 2 volume).of_le
      (hη.continuous.aestronglyMeasurable.mul hm)
    exact Eventually.of_forall fun x => by
      simp only [Pi.mul_apply]
      rw [norm_mul, Real.norm_eq_abs (f x), abs_of_nonneg (hf x).1]
      exact (mul_le_mul_of_nonneg_left (hf x).2 (norm_nonneg _)).trans_eq (mul_one _)
  weakGrad := fun x => WithLp.toLp 2 (fun i =>
    η x * G x i + fderiv ℝ η x (EuclideanSpace.single i 1) * f x)
  weakGrad_component_memLp := by
    intro i
    simp only [Measure.restrict_univ]
    obtain ⟨B, hB⟩ := hη.continuous.bounded_above_of_compact_support hs
    have hfirst : MemLp (fun x => η x * G x i) 2 volume := by
      apply (hG i).of_le_mul (c := B)
        (hη.continuous.aestronglyMeasurable.mul (hG i).aestronglyMeasurable)
      exact Eventually.of_forall fun x => by
        simp only [Pi.mul_apply]
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)
    have hc : Continuous (fun x => fderiv ℝ η x (EuclideanSpace.single i 1)) :=
      (hη.continuous_fderiv (by simp)).clm_apply continuous_const
    have hsecond : MemLp (fun x => fderiv ℝ η x (EuclideanSpace.single i 1) * f x) 2 volume := by
      apply (hc.memLp_of_hasCompactSupport (hs.fderiv_apply (𝕜 := ℝ) _)
        : MemLp (fun x => fderiv ℝ η x (EuclideanSpace.single i 1)) 2 volume).of_le
          (hc.aestronglyMeasurable.mul hm)
      exact Eventually.of_forall fun x => by
        simp only [Pi.mul_apply]
        rw [norm_mul, Real.norm_eq_abs (f x), abs_of_nonneg (hf x).1]
        exact (mul_le_mul_of_nonneg_left (hf x).2 (norm_nonneg _)).trans_eq (mul_one _)
    exact hfirst.add hsecond
  isWeakGrad := by
    intro i
    simpa only [PiLp.toLp_apply] using
      DeGiorgi.HasWeakPartialDeriv.mul_smooth isOpen_univ (hw i) hη
        (by simpa only [Measure.restrict_univ] using locallyIntegrable_of_unit_bound hm hf)
        (by simpa only [Measure.restrict_univ] using (hG i).locallyIntegrable (by norm_num))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalizedSobolevRange
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A range bound on the smooth region propagates across the set where
the weak gradient is zero. Cutoff transitions lie in the smooth region. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem localized_sobolev_range
    {f : EuclideanPlane → ℝ} {G : EuclideanPlane → EuclideanPlane}
    (hm : AEStronglyMeasurable f volume) (hf : ∀ x, f x ∈ Icc 0 1)
    (hG : ∀ i : Fin 2, MemLp (fun x => G x i) 2 volume)
    (hw : DeGiorgi.HasWeakGrad G f univ)
    {D : Set EuclideanPlane}
    (hz : ∀ i : Fin 2, ∀ᵐ x ∂volume, x ∉ D → G x i = 0)
    {η : EuclideanPlane → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hs : HasCompactSupport η) (hηunit : ∀ x, η x ∈ Icc 0 1)
    (hηd : ∀ x, x ∉ D → fderiv ℝ η x = 0)
    {b : ℝ} (hb : 0 ≤ b)
    (hrange : ∀ᵐ x ∂volume, x ∈ D → η x ≠ 0 → f x ≤ b) :
    ∀ᵐ x ∂volume, η x = 1 → f x ≤ b := by
  let W := boundedCompactCutoffWitness hm hf hG hw hη hs
  have hunit (x : EuclideanPlane) : η x * f x ∈ Icc 0 1 :=
    ⟨mul_nonneg (hηunit x).1 (hf x).1,
      (mul_le_mul (hηunit x).2 (hf x).2 (hf x).1 zero_le_one).trans_eq (one_mul 1)⟩
  have hzero (i : Fin 2) : ∀ᵐ x ∂volume,
      b < η x * f x → W.weakGrad x i = 0 := by
    filter_upwards [hz i, hrange] with x hx hr hex
    have hηne : η x ≠ 0 := by
      intro h
      rw [h, zero_mul] at hex
      exact (not_lt_of_ge hb) hex
    have hfb : b < f x := hex.trans_le (by
      calc η x * f x ≤ 1 * f x := mul_le_mul_of_nonneg_right (hηunit x).2 (hf x).1
           _ = f x := one_mul _)
    have hout : x ∉ D := fun hin => (not_lt_of_ge (hr hin hηne)) hfb
    change η x * G x i + fderiv ℝ η x (EuclideanSpace.single i 1) * f x = 0
    simp only [hx hout, hηd x hout, zero_apply, mul_zero, zero_mul, add_zero]
  have hbound := ae_le_of_compact_sobolev_gradient_zero_above W hs.mul_right hunit hb hzero
  filter_upwards [hbound] with x hx hηx
  simpa only [hηx, one_mul] using hx

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ComplementWeakGradient
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complement of a unit-bounded scalar has the negative weak gradient. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem complement_weak_gradient
    {f : EuclideanPlane → ℝ} {G : EuclideanPlane → EuclideanPlane}
    (hm : AEStronglyMeasurable f volume) (hf : ∀ x, f x ∈ Icc 0 1)
    (hw : DeGiorgi.HasWeakGrad G f univ) :
    DeGiorgi.HasWeakGrad (fun x => -G x) (fun x => 1 - f x) univ := by
  intro i φ hφ hs hsub
  let v : EuclideanPlane := EuclideanSpace.single i 1
  have hd : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hds : HasCompactSupport (fun x => fderiv ℝ φ x v) := hs.fderiv_apply (𝕜 := ℝ) v
  have hi : Integrable (fun x => f x * fderiv ℝ φ x v) := by
    simpa only [smul_eq_mul] using
      (locallyIntegrable_of_unit_bound hm hf).integrable_smul_right_of_hasCompactSupport hd hds
  have hz := (DeGiorgi.HasWeakPartialDeriv.of_contDiff (i := i) isOpen_univ
    (f := fun _ : EuclideanPlane => (1 : ℝ)) contDiff_const) φ hφ hs hsub
  simp only [fderiv_const_apply, zero_apply, zero_mul, integral_zero, neg_zero,
    one_mul, Measure.restrict_univ] at hz
  have h := hw i φ hφ hs hsub
  simp only [Measure.restrict_univ] at h ⊢
  change (∫ x, (1 - f x) * fderiv ℝ φ x v) = -(∫ x, -(G x i) * φ x)
  simp only [sub_mul, one_mul, neg_mul, integral_neg]
  rw [integral_sub (hd.integrable_of_hasCompactSupport hds) hi]
  change (∫ x, fderiv ℝ φ x v) = 0 at hz
  change (∫ x, f x * fderiv ℝ φ x v) = -(∫ x, G x i * φ x) at h
  linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PhysicalCauchyRiemann
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real Cauchy–Riemann equations in the actual physical plane
coordinates imply complex differentiability. -/
open Set Function
noncomputable section
namespace CircleDomainRigidity

 def complexifyPair (a b : EuclideanPlane → ℝ) (z : ℂ) : ℂ :=
  (a (complexPlaneCoordinates.symm z) : ℂ) + Complex.I * (b (complexPlaneCoordinates.symm z) : ℂ)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ScalarEnergyMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pushforward of scalar Dirichlet energy has no atoms. This is
applied on the whole support of an old test, or on the fixed bounded
region used for the height. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def scalarEnergyMeasure (E : Set EuclideanPlane) (v : EuclideanPlane → ℝ)
    (V : EuclideanPlane → EuclideanPlane) : Measure ℝ :=
  Measure.map v ((volume.restrict E).withDensity (fun p => ENNReal.ofReal (‖V p‖^2)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalBoundedSobolevChain
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded scalar chain rule on an open planar set. Compact tests
are enclosed in a cutoff plateau, so no boundary regularity is needed. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem bounded_sobolev_chain_rule_on_symmetric
    {U : Set EuclideanPlane} (hU : IsOpen U) {u : EuclideanPlane → ℝ}
    (hw : DeGiorgi.MemW1pWitness 2 u U)
    {B : ℝ} (hB : 0 ≤ B) (hu : ∀ x ∈ U, u x ∈ Icc (-B) B) {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (i : Fin 2) :
    DeGiorgi.HasWeakPartialDeriv i (fun x => deriv F (u x) * hw.weakGrad x i)
      (F ∘ u) U := by
  intro φ hφ hs hsub
  obtain ⟨η, V, hη, hsη, hηunit, hηsub, hV, hKV, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hs hU hsub
  have hVU : V ⊆ U := by
    intro x hx
    apply hηsub
    apply subset_tsupport η
    change η x ≠ 0
    rw [hone x hx]
    exact one_ne_zero
  let v : EuclideanPlane → ℝ := fun x => η x * u x
  obtain ⟨hv⟩ := exists_global_compact_cutoff_witness hU hw.memW1p hη hsη hηsub
  have hvunit : ∀ x, v x ∈ Icc (-B) B := by
    intro x
    apply abs_le.mp
    by_cases hx : x ∈ U
    · have hux : |u x| ≤ B := abs_le.mpr (hu x hx)
      change |η x * u x| ≤ B
      rw [abs_mul, abs_of_nonneg (hηunit x).1]
      exact (mul_le_mul (hηunit x).2 hux (abs_nonneg _) zero_le_one).trans_eq (one_mul B)
    · have hz : η x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hηsub h))
      change |η x * u x| ≤ B
      simpa only [hz, zero_mul, abs_zero] using hB
  have heq : EqOn v u V := fun x hx => by dsimp [v]; rw [hone x hx, one_mul]
  have hg := weakGrad_eq_on_cutoff_plateau hV hVU hw hv hone i
  have hg' : ∀ᵐ x ∂volume, x ∈ V → hv.weakGrad x i = hw.weakGrad x i := by
    change ∀ᵐ x ∂volume.restrict V, hv.weakGrad x i = hw.weakGrad x i at hg
    exact (ae_restrict_iff' hV.measurableSet).mp hg
  have hc := bounded_sobolev_chain_rule_Icc hv hsη.mul_right hvunit hF i φ hφ hs (subset_univ _)
  simp only [Measure.restrict_univ] at hc
  have hderiv (x : EuclideanPlane) (hx : x ∉ V) :
      fderiv ℝ φ x (EuclideanSpace.single i 1) = 0 := by
    have hn : x ∉ tsupport (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) :=
      fun h => hx (hKV ((tsupport_fderiv_apply_subset ℝ _) h))
    exact image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) hn
  have hφzero (x : EuclideanPlane) (hx : x ∉ V) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (hKV h))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [hderiv x (fun h => hx (hVU h)), mul_zero])]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsub h)), mul_zero])]
  calc
    _ = ∫ x, (F ∘ v) x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only [comp_apply]
        by_cases hx : x ∈ V
        · rw [heq hx]
        · rw [hderiv x hx, mul_zero, mul_zero]
    _ = -(∫ x, (deriv F (v x) * hv.weakGrad x i) * φ x) := hc
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hg'] with x hx
      by_cases hxV : x ∈ V
      · rw [heq hxV, hx hxV]
      · rw [hφzero x hxV, mul_zero, mul_zero]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ScalarFlatteningWeak
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distributional chain rule for the constructed flattening map. Smooth
primitives converge with their bounded derivative multipliers, so the
identity follows from the smooth chain rule. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem flattenValues_weak_partial
    {U : Set EuclideanPlane} (hU : IsOpen U) {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (W : DeGiorgi.MemW1pWitness 2 u U)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ p ∈ U, u p ∈ Icc (-B) B)
    {O : Set ℝ} (hO : IsOpen O) (i : Fin 2) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun p => Oᶜ.indicator (fun _ => (1 : ℝ)) (u p) * W.weakGrad p i)
      (flattenValues O ∘ u) U := by
  obtain ⟨F, hF, hlim, hd, hdlim⟩ := exists_flattenValues_smooth_approximation hO
  intro φ hφ hs hsub
  let dφ : EuclideanPlane → ℝ := fun p => fderiv ℝ φ p (EuclideanSpace.single i 1)
  have hdc : Continuous dφ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hds : HasCompactSupport dφ := hs.fderiv_apply (𝕜 := ℝ) _
  have hFbound (n : ℕ) (p : EuclideanPlane) : ‖F n (u p)‖ ≤ ‖u p‖ := by
    have h := (hF n).2.2.dist_le_mul (u p) 0
    simpa only [(hF n).2.1, dist_zero_right, NNReal.coe_one, one_mul] using h
  have hleft : Tendsto (fun n => ∫ p in U, F n (u p)*dφ p) atTop
      (𝓝 (∫ p in U, flattenValues O (u p)*dφ p)) := by
    apply tendsto_integral_of_dominated_convergence (bound := fun p => B*‖dφ p‖)
    · intro n
      exact (((hF n).1.continuous.comp hu).aestronglyMeasurable).mul hdc.aestronglyMeasurable
    · exact ((hdc.integrable_of_hasCompactSupport hds).norm.const_mul B).restrict
    · intro n
      filter_upwards [ae_restrict_mem hU.measurableSet] with p hp
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right ((hFbound n p).trans
        (by simpa only [Real.norm_eq_abs] using abs_le.mpr (hb p hp))) (norm_nonneg _)
    · exact Eventually.of_forall fun p => (hlim (u p)).mul_const (dφ p)
  have hφL : MemLp φ 2 (volume.restrict U) :=
    (hφ.continuous.memLp_of_hasCompactSupport hs).restrict U
  have hgφ : Integrable (fun p => W.weakGrad p i*φ p) (volume.restrict U) :=
    (W.weakGrad_component_memLp i).integrable_mul
      hφL
  have hright : Tendsto (fun n => ∫ p in U, deriv (F n) (u p)*W.weakGrad p i*φ p) atTop
      (𝓝 (∫ p in U, Oᶜ.indicator (fun _ => (1 : ℝ)) (u p)*W.weakGrad p i*φ p)) := by
    apply tendsto_integral_of_dominated_convergence (bound := fun p => ‖W.weakGrad p i*φ p‖)
    · intro n
      exact ((((hF n).1.continuous_deriv le_rfl).comp hu).aestronglyMeasurable.mul
        (W.weakGrad_component_memLp i).aestronglyMeasurable).mul hφ.continuous.aestronglyMeasurable
    · exact hgφ.norm
    · intro n
      exact Eventually.of_forall fun p => by
        rw [mul_assoc, norm_mul]
        exact (mul_le_mul_of_nonneg_right (by
          rw [Real.norm_eq_abs, abs_of_nonneg (hd n (u p)).1]
          exact (hd n (u p)).2) (norm_nonneg _)).trans_eq (one_mul _)
    · exact Eventually.of_forall fun p => ((hdlim (u p)).mul_const (W.weakGrad p i)).mul_const (φ p)
  have heq (n : ℕ) : (∫ p in U, F n (u p)*dφ p) =
      -(∫ p in U, deriv (F n) (u p)*W.weakGrad p i*φ p) := by
    simpa only [comp_apply, dφ] using
      bounded_sobolev_chain_rule_on_symmetric hU W hB hb (hF n).1 i φ hφ hs hsub
  exact tendsto_nhds_unique hleft (by simpa only [heq] using hright.neg)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ScalarFlatteningEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The flattening construction retains a genuine Sobolev witness. Its
squared gradient error is exactly the energy above the removed values. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def flattenedGradient (O : Set ℝ) (u : EuclideanPlane → ℝ)
    (V : EuclideanPlane → EuclideanPlane) : EuclideanPlane → EuclideanPlane :=
  (u ⁻¹' Oᶜ).indicator V

 def flattenedSobolevWitness
    {U : Set EuclideanPlane} (hU : IsOpen U) {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (W : DeGiorgi.MemW1pWitness 2 u U)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ p ∈ U, u p ∈ Icc (-B) B)
    {O : Set ℝ} (hO : IsOpen O) : DeGiorgi.MemW1pWitness 2 (flattenValues O ∘ u) U where
  memLp := W.memLp.norm.mono' ((flattenValues_lipschitz hO.measurableSet).continuous.comp hu).aestronglyMeasurable
    (Eventually.of_forall (fun p => by simpa only [Function.comp_apply, norm_norm] using flattenValues_norm_le hO.measurableSet (u p)))
  weakGrad := flattenedGradient O u W.weakGrad
  weakGrad_component_memLp := by
    intro i
    have he : (fun p => flattenedGradient O u W.weakGrad p i) =
        (u ⁻¹' Oᶜ).indicator (fun p => W.weakGrad p i) := by
      funext p
      by_cases hp : u p ∈ O <;> simp [flattenedGradient, hp]
    rw [he]
    exact (W.weakGrad_component_memLp i).indicator (hu.measurable hO.measurableSet.compl)
  isWeakGrad := by
    intro i
    have he : (fun p => flattenedGradient O u W.weakGrad p i) =
        (fun p => Oᶜ.indicator (fun _ => (1 : ℝ)) (u p)*W.weakGrad p i) := by
      funext p
      by_cases hp : u p ∈ O <;> simp [flattenedGradient, hp]
    rw [he]
    exact flattenValues_weak_partial hU hu W hB hb hO i

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothEnergyLimit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A locally bounded pointwise limit of smooth functions with convergent
Dirichlet energies has a Sobolev witness with no greater energy. This is
used for the actual mollifications transported by the conformal inverse. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem smooth_energy_limit
    {U : Set EuclideanPlane} (hU : IsOpen U)
    {u : EuclideanPlane → ℝ} (hu : MemLp u 2 (volume.restrict U))
    (v : ℕ → EuclideanPlane → ℝ)
    (hv : ∀ n, ContDiffOn ℝ 1 (v n) U)
    (hgrad : ∀ n i, MemLp (fun x => fderiv ℝ (v n) x (EuclideanSpace.single i 1))
      2 (volume.restrict U))
    {C : ℝ} (hb : ∀ n x, x ∈ U → ‖v n x‖ ≤ C)
    (hp : ∀ x ∈ U, Tendsto (fun n => v n x) atTop (𝓝 (u x)))
    {B : ℝ} (henergy : Tendsto (fun n => ∫ x in U,
      (fderiv ℝ (v n) x (EuclideanSpace.single 0 1)) ^ 2 +
      (fderiv ℝ (v n) x (EuclideanSpace.single 1 1)) ^ 2) atTop (𝓝 B)) :
    ∃ H : DeGiorgi.MemW1pWitness 2 u U,
      (∫ x in U, H.weakGrad x 0 ^ 2 + H.weakGrad x 1 ^ 2) ≤ B := by
  let μ := volume.restrict U
  let g (i : Fin 2) (n : ℕ) (x : EuclideanPlane) :=
    fderiv ℝ (v n) x (EuclideanSpace.single i 1)
  let e (n : ℕ) := ∫ x, g 0 n x ^ 2 + g 1 n x ^ 2 ∂μ
  change Tendsto e atTop (𝓝 B) at henergy
  obtain ⟨M, hM⟩ := henergy.bddAbove_range
  have hMe (n : ℕ) : e n ≤ M := hM (mem_range_self n)
  have hnorm (n : ℕ) (i : Fin 2) : ‖(hgrad n i).toLp (g i n)‖ ≤ M + 1 := by
    have he (j : Fin 2) : (∫ x, g j n x ^ 2 ∂μ) = ‖(hgrad n j).toLp (g j n)‖ ^ 2 := by
      rw [Lp.norm_toLp, integral_sq_eq_eLpNorm_toReal_sq (hgrad n j)]
    have hm := hMe n
    dsimp only [e] at hm
    rw [integral_add (hgrad n 0).integrable_sq (hgrad n 1).integrable_sq, he, he] at hm
    fin_cases i
    · change ‖(hgrad n 0).toLp (g 0 n)‖ ≤ M + 1
      nlinarith [sq_nonneg (‖(hgrad n 0).toLp (g 0 n)‖ - 1),
        sq_nonneg ‖(hgrad n 1).toLp (g 1 n)‖]
    · change ‖(hgrad n 1).toLp (g 1 n)‖ ≤ M + 1
      nlinarith [sq_nonneg (‖(hgrad n 1).toLp (g 1 n)‖ - 1),
        sq_nonneg ‖(hgrad n 0).toLp (g 0 n)‖]
  obtain ⟨G₀, _, s₀, hs₀, hl₀⟩ := exists_L2_weak_subsequence μ (g 0)
    (fun n => hgrad n 0) (M + 1) (fun n => hnorm n 0)
  obtain ⟨G₁, _, s₁, hs₁, hl₁⟩ := exists_L2_weak_subsequence μ (g 1 ∘ s₀)
    (fun n => hgrad (s₀ n) 1) (M + 1) (fun n => hnorm (s₀ n) 1)
  let σ := s₀ ∘ s₁
  have hσ : Tendsto σ atTop atTop := hs₀.tendsto_atTop.comp hs₁.tendsto_atTop
  have hpair₀ (w : Lp ℝ 2 μ) :
      Tendsto (fun n => ∫ x, g 0 (σ n) x * w x ∂μ) atTop (𝓝 (∫ x, G₀ x * w x ∂μ)) :=
    (hl₀ w).comp hs₁.tendsto_atTop
  have hweak (i : Fin 2) (G : Lp ℝ 2 μ)
      (hl : ∀ w : Lp ℝ 2 μ, Tendsto (fun n => ∫ x, g i (σ n) x * w x ∂μ)
        atTop (𝓝 (∫ x, G x * w x ∂μ))) :
      DeGiorgi.HasWeakPartialDeriv i G u U := by
    intro φ hφ hs hsub
    let ψ (x : EuclideanPlane) := fderiv ℝ φ x (EuclideanSpace.single i 1)
    have hψ : Continuous ψ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hsψ : HasCompactSupport ψ := hs.fderiv_apply (𝕜 := ℝ) _
    have hleft : Tendsto (fun n => ∫ x, v (σ n) x * ψ x ∂μ) atTop
        (𝓝 (∫ x, u x * ψ x ∂μ)) := by
      apply tendsto_integral_of_dominated_convergence (bound := fun x => C * ‖ψ x‖)
      · intro n
        exact ((hv (σ n)).continuousOn.aestronglyMeasurable hU.measurableSet).mul
          hψ.aestronglyMeasurable
      · exact ((hψ.integrable_of_hasCompactSupport hsψ).restrict (s := U)).norm.const_mul C
      · intro n
        filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hb (σ n) x hx) (norm_nonneg _)
      · filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
        exact ((hp x hx).comp hσ).mul_const (ψ x)
    have hφL : MemLp φ 2 μ := (hφ.continuous.memLp_of_hasCompactSupport hs).restrict U
    have he (f : EuclideanPlane → ℝ) :
        (∫ x, f x * hφL.toLp φ x ∂μ) = ∫ x, f x * φ x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hφL.coeFn_toLp] with x hx
      rw [hx]
    have hright := hl (hφL.toLp φ)
    simp only [he] at hright
    have hboth : ∀ n, (∫ x, v (σ n) x * ψ x ∂μ) = -(∫ x, g i (σ n) x * φ x ∂μ) :=
      fun n => weakPartial_of_smooth_on hU (hv (σ n)) i φ hφ hs hsub
    rw [show (fun n => ∫ x, v (σ n) x * ψ x ∂μ) =
      (fun n => -(∫ x, g i (σ n) x * φ x ∂μ)) from funext hboth] at hleft
    exact tendsto_nhds_unique hleft hright.neg
  let H : DeGiorgi.MemW1pWitness 2 u U := {
    memLp := hu
    weakGrad := fun x => WithLp.toLp 2 (fun i => if i = 0 then G₀ x else G₁ x)
    weakGrad_component_memLp := by
      intro i
      fin_cases i
      · exact Lp.memLp G₀
      · exact Lp.memLp G₁
    isWeakGrad := by
      intro i
      fin_cases i
      · exact hweak 0 G₀ hpair₀
      · exact hweak 1 G₁ hl₁ }
  refine ⟨H, ?_⟩
  change (∫ x, G₀ x ^ 2 + G₁ x ^ 2 ∂μ) ≤ B
  apply paired_L2_energy_le (fun n => hgrad (σ n) 0) (fun n => hgrad (σ n) 1)
    G₀ G₁ (ε := fun n => e (σ n) - B)
  · simpa only [Function.comp_def, sub_self] using (henergy.comp hσ).sub_const B
  · exact Eventually.of_forall fun n => le_of_eq (by dsimp [e] <;> ring)
  · exact hpair₀ G₀
  · exact hl₁ G₁

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LocalHeightDifference
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.horizontalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The flattened height minus the genuine vertical coordinate has an
explicit local weak gradient and a controlled compact cutoff. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def verticalLocalWitness (A : ℝ) :
    DeGiorgi.MemW1pWitness 2 (fun x : EuclideanPlane => x 1) (ball 0 A) where
  memLp := continuous_memLp_ball verticalLinear.continuous A
  weakGrad := fun _ => EuclideanSpace.single (1 : Fin 2) 1
  weakGrad_component_memLp := by
    intro i
    let : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanPlane) A)) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    exact memLp_const _
  isWeakGrad := by
    intro i
    have h := weakPartial_of_smooth_on (U := ball (0 : EuclideanPlane) A) isOpen_ball verticalLinear.contDiff.contDiffOn i
    convert h using 1
    · funext x
      fin_cases i <;> simp [ContinuousLinearMap.fderiv, verticalLinear_apply]
    · rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ComplexLocalScalarWitness
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A local complex scalar with square-integrable value and differential
has the explicit physical Sobolev witness on its open source region. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 def complexLocalScalarWitness
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f D) (hL : MemLp f 2 (volume.restrict D))
    (hE : MemLp (fderiv ℝ f) 2 (volume.restrict D)) :
    DeGiorgi.MemW1pWitness 2 (f ∘ complexPlaneCoordinates)
      (complexPlaneCoordinates ⁻¹' D) := by
  let Ω := complexPlaneCoordinates ⁻¹' D
  let F := f ∘ complexPlaneCoordinates
  have hΩ : IsOpen Ω := hD.preimage complexPlaneCoordinates.continuous
  have hF : ContDiffOn ℝ ∞ F Ω :=
    hf.comp complexPlaneCoordinates.contDiff.contDiffOn (fun _ hp => hp)
  have hmajor : MemLp (fun p => ‖fderiv ℝ f (complexPlaneCoordinates p)‖) 2 (volume.restrict Ω) :=
    hE.norm.comp_measurePreserving (complexPlaneCoordinates_measurePreserving.restrict_preimage hD.measurableSet)
  have hpartial (i : Fin 2) : MemLp
      (fun p => fderiv ℝ F p (EuclideanSpace.single i 1)) 2 (volume.restrict Ω) := by
    have hm : AEStronglyMeasurable (fun p => fderiv ℝ F p (EuclideanSpace.single i 1))
        (volume.restrict Ω) :=
      ((hF.continuousOn_fderiv_of_isOpen hΩ (by simp)).clm_apply continuousOn_const).aestronglyMeasurable hΩ.measurableSet
    apply hmajor.of_le hm
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with p hp
    have hd : DifferentiableAt ℝ f (complexPlaneCoordinates p) :=
      (hf.contDiffAt (hD.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    change ‖fderiv ℝ (f ∘ complexPlaneCoordinates) p (EuclideanSpace.single i 1)‖ ≤ _
    rw [fderiv_comp p hd complexPlaneCoordinates.differentiableAt, complexPlaneCoordinates.fderiv]
    have haxis : ‖complexPlaneCoordinates (EuclideanSpace.single i 1)‖ = 1 := by
      fin_cases i
      · change ‖complexPlaneCoordinates (EuclideanSpace.single (0 : Fin 2) 1)‖ = 1
        rw [complexPlaneCoordinates_zero, norm_one]
      · change ‖complexPlaneCoordinates (EuclideanSpace.single (1 : Fin 2) 1)‖ = 1
        rw [complexPlaneCoordinates_one, Complex.norm_I]
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, haxis, mul_one,
      Real.norm_eq_abs, abs_norm] using
      (fderiv ℝ f (complexPlaneCoordinates p)).le_opNorm (complexPlaneCoordinates (EuclideanSpace.single i 1))
  exact {
    memLp := hL.comp_measurePreserving (complexPlaneCoordinates_measurePreserving.restrict_preimage hD.measurableSet)
    weakGrad := fun p => WithLp.toLp 2 (fun i => fderiv ℝ F p (EuclideanSpace.single i 1))
    weakGrad_component_memLp := hpartial
    isWeakGrad := fun i => weakPartial_of_smooth_on hΩ (hF.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) i }

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PhysicalCoordinateLines
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate lines in the actual Euclidean Sobolev plane. Their
one-dimensional derivatives and total energies are the physical partials. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def physicalCoordinateLine (i : Fin 2) (y x : ℝ) : EuclideanPlane :=
  if i = 0 then euclideanPlaneCoordinates.symm (x,y)
  else euclideanPlaneCoordinates.symm (y,x)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_SamplingTraceContinuity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Shrinking sampling sets preserve the exact continuous boundary trace
of a partition smoothing. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def boundaryPaste (U : Set EuclideanPlane) (u v : EuclideanPlane → ℝ)
    (x : EuclideanPlane) : ℝ := by
  classical
  exact if x ∈ U then v x else u x

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CompactWeakExtension
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A weak derivative whose function and field are supported on one compact
subset of an open set is a global weak derivative. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem weakPartial_global_of_compact_support
    {U K : Set EuclideanPlane} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {f g : EuclideanPlane → ℝ} {i : Fin 2}
    (hw : DeGiorgi.HasWeakPartialDeriv i g f U)
    (hf : ∀ x ∉ K, f x = 0) (hg : ∀ x ∉ K, g x = 0) :
    DeGiorgi.HasWeakPartialDeriv i g f univ := by
  obtain ⟨η, V, hη, hsη, _, hsU, hV, hKV, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hK hU hKU
  intro φ hφ hsφ _
  let ψ : EuclideanPlane → ℝ := fun x => η x * φ x
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hη.mul hφ
  have hsψ : HasCompactSupport ψ := hsη.mul_right
  have hψU : tsupport ψ ⊆ U := tsupport_mul_subset_left.trans hsU
  have he := hw ψ hψ hsψ hψU
  have hdη (x : EuclideanPlane) (hx : x ∈ K) : fderiv ℝ η x = 0 := by
    have heq : η =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [hV.mem_nhds (hKV hx)] with y hy
      exact hone y hy
    rw [heq.fderiv_eq]
    exact fderiv_const_apply 1
  have hleft (x : EuclideanPlane) :
      f x * fderiv ℝ ψ x (EuclideanSpace.single i 1) =
        f x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    by_cases hx : x ∈ K
    · rw [show fderiv ℝ ψ x = η x • fderiv ℝ φ x + φ x • fderiv ℝ η x from
        fderiv_fun_mul (hη.differentiable (by simp)).differentiableAt
          (hφ.differentiable (by simp)).differentiableAt]
      rw [hdη x hx, hone x (hKV hx)]
      simp
    · rw [hf x hx, zero_mul, zero_mul]
  have hright (x : EuclideanPlane) : g x * ψ x = g x * φ x := by
    by_cases hx : x ∈ K
    · simp only [ψ, hone x (hKV hx), one_mul]
    · rw [hg x hx, zero_mul, zero_mul]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [hf x (fun h => hx (hKU h)), zero_mul]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [hg x (fun h => hx (hKU h)), zero_mul])] at he
  simp only [hleft, hright] at he
  simpa only [Measure.restrict_univ] using he

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_SignedTraceTruncationWeak
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Signed zero-trace truncations have global weak derivatives, with no
regularity assumption on the excluded set. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem signed_trace_truncation_weak
    {U : Set EuclideanPlane} (hU : IsOpen U) {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (hz : ∀ x ∉ U, u x = 0) (hw : DeGiorgi.MemW1pWitness 2 u U)
    {δ : ℝ} (hδ : 0 < δ) (i : Fin 2) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => deriv (signedTraceTruncation δ) (u x) * U.indicator (fun x => hw.weakGrad x i) x)
      (signedTraceTruncation δ ∘ u) univ := by
  obtain ⟨B, hbound⟩ := hu.bounded_above_of_compact_support hs
  have hB : 0 ≤ B := (norm_nonneg (u 0)).trans (hbound 0)
  have hb : ∀ x ∈ U, u x ∈ Icc (-B) B := by
    intro x _
    exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hbound x)
  let K : Set EuclideanPlane := {x | δ ≤ |u x|}
  have hK : IsCompact K := hs.isCompact.of_isClosed_subset
    (isClosed_le continuous_const hu.abs) (by
      intro x hx
      apply subset_tsupport u
      change u x ≠ 0
      intro he
      have ht : δ ≤ |u x| := hx
      rw [he, abs_zero] at ht
      exact (not_le_of_gt hδ) ht)
  have hKU : K ⊆ U := by
    intro x hx
    by_contra hxU
    have ht : δ ≤ |u x| := hx
    rw [hz x hxU, abs_zero] at ht
    exact (not_le_of_gt hδ) ht
  apply weakPartial_global_of_compact_support hU hK hKU
  · apply (bounded_sobolev_chain_rule_on_symmetric hU hw hB hb
      ((signedTraceTruncation_contDiff δ).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) i).congr_ae Filter.EventuallyEq.rfl
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    rw [indicator_of_mem hx]
  · intro x hx
    exact signedTraceTruncation_zero hδ (le_of_not_ge hx)
  · intro x hx
    rw [signedTraceTruncation_deriv_zero hδ (le_of_not_ge hx), zero_mul]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ZeroTraceExtension
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous, compactly supported Sobolev function with
zero trace extends through the excluded set with zero weak gradient there.
Smooth value truncations give the extension without a geometric assumption
on that closed set. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem signed_zero_trace_global_weak
    {U : Set EuclideanPlane} (hU : IsOpen U) {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (hz : ∀ x ∉ U, u x = 0) (hw : DeGiorgi.MemW1pWitness 2 u U) (i : Fin 2) :
    DeGiorgi.HasWeakPartialDeriv i
      ({x | u x ≠ 0}.indicator (U.indicator (fun x => hw.weakGrad x i))) u univ := by
  classical
  let δ : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hδ : ∀ n, 0 < δ n := fun n => inv_pos.mpr (by positivity)
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    simpa only [δ, one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let G : EuclideanPlane → ℝ := U.indicator (fun x => hw.weakGrad x i)
  have hG : MemLp G 2 volume :=
    (memLp_indicator_iff_restrict hU.measurableSet).mpr (hw.weakGrad_component_memLp i)
  obtain ⟨C, hC, hbound⟩ := signedTraceTruncation_uniform_deriv_bound
  obtain ⟨B, hB⟩ := hu.bounded_above_of_compact_support hs
  intro φ hφ hsφ hsub
  let v : EuclideanPlane := EuclideanSpace.single i 1
  have hD : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsD : HasCompactSupport (fun x => fderiv ℝ φ x v) := hsφ.fderiv_apply (𝕜 := ℝ) v
  have hleft := tendsto_integral_of_dominated_convergence (μ := volume)
    (F := fun n x => signedTraceTruncation (δ n) (u x) * fderiv ℝ φ x v)
    (f := fun x => u x * fderiv ℝ φ x v)
    (fun x => B * ‖fderiv ℝ φ x v‖)
    (fun n => (((signedTraceTruncation_contDiff (δ n)).continuous.comp hu).aestronglyMeasurable).mul
      hD.aestronglyMeasurable)
    ((hD.integrable_of_hasCompactSupport hsD).norm.const_mul B)
    (fun n => Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        ((signedTraceTruncation_norm_le (hδ n)).trans (hB x)) (norm_nonneg _))
    (Eventually.of_forall fun x =>
      (signedTraceTruncation_tendsto hδ hδlim (u x)).mul_const _)
  have hright := tendsto_integral_bounded_mul_L2
    (g := fun _ : ℕ => G) (G := G)
    (h := fun n x => deriv (signedTraceTruncation (δ n)) (u x))
    (H := fun x => if u x = 0 then 0 else 1) (φ := φ)
    (fun _ => hG) hG (hφ.continuous.memLp_of_hasCompactSupport hsφ)
    (by
      simp only [sub_self]
      change Tendsto (fun _ : ℕ => eLpNorm (0 : EuclideanPlane → ℝ) 2 volume) atTop (𝓝 0)
      simp only [eLpNorm_zero]
      exact tendsto_const_nhds)
    (fun n => (((signedTraceTruncation_contDiff (δ n)).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) :
      ContDiff ℝ 1 (signedTraceTruncation (δ n))).continuous_deriv le_rfl).comp hu
      |>.aestronglyMeasurable)
    hC (fun n => Eventually.of_forall fun x => hbound (δ n) (hδ n) (u x))
    (Eventually.of_forall fun x => signedTraceTruncation_deriv_tendsto hδ hδlim (u x))
  have heq (n : ℕ) :
      (∫ x, signedTraceTruncation (δ n) (u x) * fderiv ℝ φ x v) =
        -(∫ x, deriv (signedTraceTruncation (δ n)) (u x) * G x * φ x) := by
    simpa only [Measure.restrict_univ, comp_apply] using
      signed_trace_truncation_weak hU hu hs hz hw (hδ n) i φ hφ hsφ hsub
  have he := tendsto_nhds_unique hleft (by simpa only [heq] using hright.neg)
  simp only [Measure.restrict_univ]
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    by_cases hx : u x = 0 <;> simp [hx, G]

 def zeroTraceWitness
    {U : Set EuclideanPlane} (hU : IsOpen U) {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (hz : ∀ x ∉ U, u x = 0) (hw : DeGiorgi.MemW1pWitness 2 u U) :
    DeGiorgi.MemW1pWitness 2 u univ where
  memLp := by simpa only [Measure.restrict_univ] using hu.memLp_of_hasCompactSupport hs
  weakGrad := fun x => WithLp.toLp 2 (fun i =>
    {x | u x ≠ 0}.indicator (U.indicator (fun x => hw.weakGrad x i)) x)
  weakGrad_component_memLp i := by
    simp only [Measure.restrict_univ]
    exact ((memLp_indicator_iff_restrict hU.measurableSet).mpr
      (hw.weakGrad_component_memLp i)).indicator (isOpen_ne_fun hu continuous_const).measurableSet
  isWeakGrad := signed_zero_trace_global_weak hU hu hs hz hw

 theorem zeroTraceWitness_zero
    {U : Set EuclideanPlane} (hU : IsOpen U) {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (hz : ∀ x ∉ U, u x = 0) (hw : DeGiorgi.MemW1pWitness 2 u U)
    (i : Fin 2) {x : EuclideanPlane} (hx : x ∉ U) :
    (zeroTraceWitness hU hu hs hz hw).weakGrad x i = 0 := by
  change {y | u y ≠ 0}.indicator (U.indicator (fun y => hw.weakGrad y i)) x = 0
  apply indicator_of_notMem
  change ¬ u x ≠ 0
  simp only [hz x hx, ne_eq, not_true_eq_false, not_false_eq_true]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ZeroTraceEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero-trace extension preserves the original weak gradient and
Dirichlet energy, and introduces no energy on the excluded set. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem zeroTraceWitness_gradient_on
    {U : Set EuclideanPlane} (hU : IsOpen U) {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (hz : ∀ x ∉ U, u x = 0) (hw : DeGiorgi.MemW1pWitness 2 u U) (i : Fin 2) :
    (fun x => (zeroTraceWitness hU hu hs hz hw).weakGrad x i) =ᵐ[volume.restrict U]
      (fun x => hw.weakGrad x i) := by
  let H := zeroTraceWitness hU hu hs hz hw
  let H' := H.restrict hU (subset_univ U)
  exact (H'.isWeakGrad i).ae_eq hU (hw.isWeakGrad i)
    ((H'.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
    ((hw.weakGrad_component_memLp i).locallyIntegrable (by norm_num))

 theorem zeroTraceWitness_component_energy
    {U : Set EuclideanPlane} (hU : IsOpen U) {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (hz : ∀ x ∉ U, u x = 0) (hw : DeGiorgi.MemW1pWitness 2 u U) (i : Fin 2) :
    (∫ x, (zeroTraceWitness hU hu hs hz hw).weakGrad x i ^ 2) =
      ∫ x in U, hw.weakGrad x i ^ 2 := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U) (fun x hx => by
    rw [zeroTraceWitness_zero hU hu hs hz hw i hx, zero_pow (by norm_num : 2 ≠ 0)])]
  apply integral_congr_ae
  filter_upwards [zeroTraceWitness_gradient_on hU hu hs hz hw i] with x hx
  rw [hx]

 theorem zeroTraceWitness_energy
    {U : Set EuclideanPlane} (hU : IsOpen U) {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (hz : ∀ x ∉ U, u x = 0) (hw : DeGiorgi.MemW1pWitness 2 u U) :
    (∫ x, (zeroTraceWitness hU hu hs hz hw).weakGrad x 0 ^ 2 +
      (zeroTraceWitness hU hu hs hz hw).weakGrad x 1 ^ 2) =
      ∫ x in U, hw.weakGrad x 0 ^ 2 + hw.weakGrad x 1 ^ 2 := by
  let H := zeroTraceWitness hU hu hs hz hw
  have hH (i : Fin 2) : Integrable (fun x => H.weakGrad x i ^ 2) := by
    have ht := (H.weakGrad_component_memLp i).integrable_sq
    simpa only [Measure.restrict_univ] using ht
  rw [integral_add (hH 0) (hH 1),
    integral_add (hw.weakGrad_component_memLp 0).integrable_sq
      (hw.weakGrad_component_memLp 1).integrable_sq]
  rw [zeroTraceWitness_component_energy hU hu hs hz hw 0,
    zeroTraceWitness_component_energy hU hu hs hz hw 1]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ProjectedPlaneFunction
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continue any compact planar test through the actual matched-end
projection. This construction does not require the test to be smooth. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel

 local instance instBorelSpaceSphere_64_r55b9a7_1 : BorelSpace Sphere := ⟨rfl⟩
theorem sphereFromPlaneFunction_zero_near_infty
    {u : EuclideanPlane → ℝ} (hs : HasCompactSupport u) :
    ∀ᶠ p in 𝓝 (OnePoint.infty : Sphere), sphereFromPlaneFunction u p = 0 := by
  let K := complexPlaneCoordinates '' tsupport u
  have hK : IsCompact K := hs.isCompact.image complexPlaneCoordinates.continuous
  have hN : (((↑) : ℂ → Sphere) '' K)ᶜ ∈ 𝓝 (OnePoint.infty : Sphere) :=
    (OnePoint.isOpen_compl_image_coe.mpr ⟨hK.isClosed, hK⟩).mem_nhds
      OnePoint.infty_notMem_image_coe
  filter_upwards [hN] with p hp
  cases p using OnePoint.rec with
  | infty => simp [sphereFromPlaneFunction]
  | coe z =>
    rw [sphereFromPlaneFunction_coe]
    apply image_eq_zero_of_notMem_tsupport
    intro hz
    exact hp ⟨z, ⟨complexPlaneCoordinates.symm z, hz,
      complexPlaneCoordinates.apply_symm_apply z⟩, rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SignedScalarTests
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact real tests can be encoded by unit-interval tests and a common
cutoff. On the dust this is an affine coordinate change, so pair-nullity
is preserved exactly. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def signedScalarEncoding (η u : EuclideanPlane → ℝ) (C : ℝ) (x : EuclideanPlane) : ℝ :=
  (η x + u x / C) / 2

 def smoothCompactPlaneWitness {η : EuclideanPlane → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hs : HasCompactSupport η) :
    DeGiorgi.MemW1pWitness 2 η univ :=
  smoothPlaneSobolevWitness isOpen_univ (hη.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffOn
    ((hη.continuous.memLp_of_hasCompactSupport hs).restrict univ)
    (fun i => (((hη.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1))).restrict univ)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SignedTestFamily
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One common cutoff encodes a finite signed list by unit-interval tests.
The cutoff is constant on the source dust, so all new trace pairs are null. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_70 : BorelSpace Sphere := ⟨rfl⟩

structure SignedTestFamily (G : Set Sphere) {m : ℕ} (u : Fin m → EuclideanPlane → ℝ) where
  test : Fin (m + 1) → EuclideanPlane → ℝ
  continuous : ∀ i, Continuous (test i)
  compact : ∀ i, HasCompactSupport (test i)
  unit : ∀ i x, test i x ∈ Icc 0 1
  witness : ∀ i, DeGiorgi.MemW1pWitness 2 (test i) (physicalPlaneDomain G)
  pair_null : ∀ i j, i ≠ j → volume
    ((fun p => (sphereFromPlaneFunction (test i) p, sphereFromPlaneFunction (test j) p)) '' Gᶜ) = 0
  scale : Fin m → ℝ
  recovery : ∀ i x, (2 * scale i) * test i.succ x - scale i * test 0 x = u i x

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactCoordinateTest
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An axial coordinate on a bounded sphere complement can be represented
by a smooth compact planar test. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_71 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SelectedCoordinateTest
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact scalar test recovers each actual finite target coordinate
on all source complementary components. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_72 : BorelSpace Sphere := ⟨rfl⟩
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_FiniteMatchedField
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual selected matched field is finite, measurable, and bounded
on every compact part of the source plane. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_73 : BorelSpace Sphere := ⟨rfl⟩
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_AxialCircleFlux
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common notation for the two axial circle fluxes. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def axialCircleIncrement (i : Fin 2) (F : ℂ → ℂ) (c : ℂ) (r y : ℝ) : ℝ :=
    (complexPlaneCoordinates.symm (F (complexCoordinateLine i y (axialChord i c r y).2))) i-
      (complexPlaneCoordinates.symm (F (complexCoordinateLine i y (axialChord i c r y).1))) i
 def axialCircleFlux (i : Fin 2) (F : ℂ → ℂ) (c : ℂ) (r : ℝ) : ℝ :=
    ∫ y in (transverseCoordinate i c-r)..(transverseCoordinate i c+r), axialCircleIncrement i F c r y

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_AxialBandFlux
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Zero extension of each axial circle increment to all transverse
lines. Its integral is exactly the corresponding circle flux. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def axialBandIncrement (i : Fin 2) (F : ℂ → ℂ) (c : ℂ) (r : ℝ) : ℝ → ℝ :=
    (Icc (transverseCoordinate i c-r) (transverseCoordinate i c+r)).indicator
      (axialCircleIncrement i F c r)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedRealMaskSobolev
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the proved open-set Sobolev gluing to the constructed masks.
The only scalar hypotheses concern the actual smooth pullback on the original domain. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere}
  {f : Sphere → Sphere}

 def realPlaneDomain (G : Set Sphere) : Set (ℝ × ℝ) :=
  {p | (Complex.equivRealProdCLM.symm p : Sphere) ∈ G}

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactRelationCoordinateTest
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One compact smooth coordinate test agrees with the actual coordinate
on all fibers over a prescribed compact source set and on all target
complementary components. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_74 : BorelSpace Sphere := ⟨rfl⟩
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ActualFiniteDiskSlice
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual matched field satisfies the finite enlarged-hole slice
inequality. No independent slice or flux assumption is retained. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_75 : BorelSpace Sphere := ⟨rfl⟩
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ActualEnclosedCircleSlice
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact finite-circle slice inequality for the selected matched
field and the actual zero-extended source differential. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_76 : BorelSpace Sphere := ⟨rfl⟩
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ActualAxialCircleFlux
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-hole axial flux bound from the proved common-point
trace and the source differential. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_77 : BorelSpace Sphere := ⟨rfl⟩
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_BoundedSphereHomotopy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded-displacement plane map extends to a sphere map homotopic
to the identity by the straight-line homotopy. Uniform properness proves
joint continuity at infinity. -/
open Set Function Filter Metric
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity

 def straightSphereHomotopy (F : ℂ → ℂ) (t : unitInterval × Sphere) : Sphere :=
  extendAtInfinity (fun z => z+(t.1:ℝ) • (F z-z)) t.2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothWeakGradient
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identify the weak gradient of an actual local Sobolev witness with
its classical differential when the represented scalar is smooth. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def localSobolevChangeDomain {U V : Set EuclideanPlane} {f : EuclideanPlane → ℝ}
    (W : DeGiorgi.MemW1pWitness 2 f U) (h : U = V) :
    DeGiorgi.MemW1pWitness 2 f V where
  memLp := by simpa only [← h] using W.memLp
  weakGrad := W.weakGrad
  weakGrad_component_memLp := fun i => by simpa only [← h] using W.weakGrad_component_memLp i
  isWeakGrad := by simpa only [← h] using W.isWeakGrad

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PhysicalFrontierCrossings
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact bounded region has a first boundary point on each
coordinate line meeting its closure. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def planeTransverse (i : Fin 2) (z : EuclideanPlane) : ℝ :=
  if i = 0 then z 1 else z 0

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_AxialCommonPointTrace
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact four axial trace conclusions for the singleton-to-singleton
part of the matched correspondence, from the recorded published inputs. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_78 : BorelSpace Sphere := ⟨rfl⟩
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConditionalNormalizedRigidity
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Principal normalized rigidity from exactly the recorded published inputs. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_79 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConditionalRigidity
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Paper 047-01, Introduction, thm:main. The exact unrestricted
removability-to-rigidity theorem from the recorded published inputs. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance instBorelSpaceSphere_80 : BorelSpace Sphere := ⟨rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PlanarAffineRescale
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive affine rescalings of the plane and their exact area factor. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def planarAffineHomeomorph (a : EuclideanPlane) (s : ℝ) (hs : s ≠ 0) :
    EuclideanPlane ≃ₜ EuclideanPlane where
  toFun x := a+s • x
  invFun y := s⁻¹ • (y-a)
  left_inv x := by simp [smul_smul, hs]
  right_inv y := by simp [smul_smul, hs]
  continuous_toFun := continuous_const.add (continuous_id.const_smul s)
  continuous_invFun := (continuous_id.sub continuous_const).const_smul s⁻¹

lemma planarAffineHomeomorph_apply (a : EuclideanPlane) (s : ℝ) (hs : s ≠ 0) (x : EuclideanPlane) :
    planarAffineHomeomorph a s hs x = a+s • x := rfl

lemma integral_planarAffine (a : EuclideanPlane) {s : ℝ} (hs : 0 < s)
    (h : EuclideanPlane → ℝ) :
    (∫ x, h (a+s • x)) = (s^2)⁻¹ * ∫ y, h y := by
  have he := Measure.integral_comp_smul_of_nonneg (E := EuclideanPlane) volume
    (fun y => h (a+y)) s (hR := hs.le)
  calc
    _ = (s ^ Module.finrank ℝ EuclideanPlane)⁻¹ • (∫ y, h (a+y)) := he
    _ = _ := by rw [finrank_euclideanSpace_fin, integral_add_left_eq_self, smul_eq_mul]

lemma planarAffine_inverse_hasFDerivAt (a : EuclideanPlane) {s : ℝ} (hs : s ≠ 0)
    (y : EuclideanPlane) :
    HasFDerivAt (planarAffineHomeomorph a s hs).symm
      (s⁻¹ • ContinuousLinearMap.id ℝ EuclideanPlane) y :=
  ((hasFDerivAt_id y).sub_const a).const_smul s⁻¹

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_AffineLpTransport
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability under the same physical affine rescaling as the weak
partial identities. The area factor is explicit and finite. -/
open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma map_volume_planarAffine (a : EuclideanPlane) {s : ℝ} (hs : 0 < s) :
    Measure.map (fun x : EuclideanPlane => a+s • x) volume =
      ENNReal.ofReal ((s^2)⁻¹) • volume := by
  have hm : Measurable (fun x : EuclideanPlane => s • x) := by fun_prop
  have ha : Measurable (fun x : EuclideanPlane => a+x) := by fun_prop
  rw [show (fun x : EuclideanPlane => a+s • x) =
    (fun x => a+x) ∘ (fun x => s • x) from rfl, ← Measure.map_map ha hm,
    Measure.map_addHaar_smul volume hs.ne', Measure.map_smul]
  simp only [finrank_euclideanSpace_fin, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg s)),
    map_add_left_eq_self]

lemma memLp_planarAffine {F : Type*} [NormedAddCommGroup F] {f : EuclideanPlane → F}
    {p : ℝ≥0∞} (hf : MemLp f p volume) (a : EuclideanPlane) {s : ℝ} (hs : 0 < s) :
    MemLp (fun x => f (a+s • x)) p volume := by
  have h : MemLp f p (Measure.map (fun x : EuclideanPlane => a+s • x) volume) := by
    rw [map_volume_planarAffine a hs]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact h.comp_of_map (by fun_prop)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WeakGradientAffineRescale
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual distributional gradient under a positive affine rescaling.
The proof changes variables in the compactly supported test identity. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma weakGradient_planarAffine {u : EuclideanPlane → ℝ} {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ) (a : EuclideanPlane) {s : ℝ} (hs : 0 < s) :
    DeGiorgi.HasWeakGrad (fun x => s • V (a+s • x)) (fun x => u (a+s • x)) univ := by
  intro i φ hφ hsφ _
  let e := planarAffineHomeomorph a s hs.ne'
  let ψ := φ ∘ e.symm
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    hφ.comp ((contDiff_id.sub contDiff_const).const_smul s⁻¹)
  have hsψ : HasCompactSupport ψ := hsφ.comp_homeomorph e.symm
  have heq (x : EuclideanPlane) : ψ (a+s • x) = φ x := e.symm_apply_apply x |> congrArg φ
  have hd (x : EuclideanPlane) :
      fderiv ℝ ψ (a+s • x) (EuclideanSpace.single i 1) =
        s⁻¹ * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    have hh := (hφ.differentiable (by simp) (e.symm (a+s • x))).hasFDerivAt.comp (a+s • x)
      (planarAffine_inverse_hasFDerivAt a hs.ne' (a+s • x))
    have h := congrArg (fun L : EuclideanPlane →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hh.fderiv
    simpa only [ψ, ← planarAffineHomeomorph_apply a s hs.ne', e, Homeomorph.symm_apply_apply,
      ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
      map_smul, smul_eq_mul] using h
  have hbase := hw i ψ hψ hsψ (subset_univ _)
  simp only [Measure.restrict_univ] at hbase ⊢
  let A : EuclideanPlane → ℝ := fun y => u y * fderiv ℝ ψ y (EuclideanSpace.single i 1)
  let B : EuclideanPlane → ℝ := fun y => V y i * ψ y
  have ht : (∫ x, A (a+s • x)) = -(∫ x, B (a+s • x)) := by
    rw [integral_planarAffine a hs, integral_planarAffine a hs]
    change (s^2)⁻¹*(∫ y, u y*fderiv ℝ ψ y (EuclideanSpace.single i 1)) = _
    rw [hbase, mul_neg]
  have hA : (fun x => A (a+s • x)) = fun x => s⁻¹*(u (a+s • x)*fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
    funext x
    dsimp only [A]
    rw [hd]
    ring
  have hB : (fun x => B (a+s • x)) = fun x => V (a+s • x) i * φ x := by
    funext x
    dsimp only [B]
    rw [heq]
  rw [hA, hB, integral_const_mul] at ht
  have hh := congrArg (fun t : ℝ => s*t) ht
  rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul, mul_neg] at hh
  have hR : (fun x => (s • V (a+s • x)) i * φ x) = fun x => s*(V (a+s • x) i * φ x) := by
    funext x
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  rw [hR, integral_const_mul]
  exact hh

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_AffineSobolevWitness
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global Sobolev witnesses retain their actual gradient under affine
rescaling. This is the witness used in the local capacity application. -/
open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

def affineSobolevWitness {u : EuclideanPlane → ℝ}
    (W : DeGiorgi.MemW1pWitness 2 u univ) (a : EuclideanPlane)
    {s : ℝ} (hs : 0 < s) :
    DeGiorgi.MemW1pWitness 2 (fun x => u (a+s • x)) univ where
  memLp := by
    simp only [Measure.restrict_univ] at *
    exact memLp_planarAffine (by simpa using W.memLp) a hs
  weakGrad := fun x => s • W.weakGrad (a+s • x)
  weakGrad_component_memLp := by
    intro i
    simp only [Measure.restrict_univ, PiLp.smul_apply, smul_eq_mul]
    exact (memLp_planarAffine (by simpa using W.weakGrad_component_memLp i) a hs).const_mul s
  isWeakGrad := weakGradient_planarAffine W.isWeakGrad a hs

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothScalarCutoffWitness
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth value cutoffs and spatial cutoffs of an actual compact
Sobolev function, retaining the exact product/chain-rule gradient. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

def smoothScalarCutoffWitness {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (hsu : HasCompactSupport u)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hFu : ∀ t, F t ∈ Icc 0 1)
    {C : ℝ} (hC : ∀ t, ‖deriv F t‖ ≤ C)
    {η : EuclideanPlane → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hsη : HasCompactSupport η) :
    DeGiorgi.MemW1pWitness 2 (fun x => η x * F (u x)) univ := by
  let B := Classical.choose (hu.bounded_above_of_compact_support hsu)
  have hB := Classical.choose_spec (hu.bounded_above_of_compact_support hsu)
  have hub (x : EuclideanPlane) : u x ∈ Icc (-B) B := by
    exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hB x)
  let G : EuclideanPlane → EuclideanPlane := fun x =>
    WithLp.toLp 2 (fun i => deriv F (u x) * W.weakGrad x i)
  have hG (i : Fin 2) : MemLp (fun x => G x i) 2 volume := by
    change MemLp (fun x => deriv F (u x) * W.weakGrad x i) 2 volume
    apply (show MemLp (fun x => W.weakGrad x i) 2 volume by
      simpa only [Measure.restrict_univ] using W.weakGrad_component_memLp i).of_le_mul
      (c := C)
      (((hF.continuous_deriv le_rfl).comp hu).aestronglyMeasurable.mul
        (by simpa only [Measure.restrict_univ] using
          (W.weakGrad_component_memLp i).aestronglyMeasurable))
    exact Eventually.of_forall fun x => by
      simp only [Pi.mul_apply, Function.comp_apply]
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC (u x)) (norm_nonneg _)
  have hwG : DeGiorgi.HasWeakGrad G (F ∘ u) univ := by
    intro i
    exact bounded_sobolev_chain_rule_Icc W hsu hub hF i
  exact boundedCompactCutoffWitness (hF.continuous.comp hu).aestronglyMeasurable
    (fun x => hFu (u x)) hG hwG hη hsη

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RescaledBandWitness
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At graph scale s the domain and value rescalings cancel in the
chain-rule term. The remaining gradient is the original physical one. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def rescaledBandWitness {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (hsu : HasCompactSupport u)
    (a : EuclideanPlane) (t : ℝ) {s : ℝ} (hs : 0 < s)
    {C : ℝ} (hC : ∀ y, ‖deriv scalarCapacityBump y‖ ≤ C) :
    DeGiorgi.MemW1pWitness 2
      (fun x => spatialCapacityBump x * scalarCapacityBump ((u (a+s • x)-t)/s)) univ :=
  smoothScalarCutoffWitness
    (hu.comp (planarAffineHomeomorph a s hs.ne').continuous)
    (affineSobolevWitness W a hs)
    (hsu.comp_homeomorph (planarAffineHomeomorph a s hs.ne'))
    (rescaledScalarBump_contDiff t s) (rescaledScalarBump_unit t s)
    (rescaledScalarBump_deriv_bound hC t hs)
    spatialCapacityBump.contDiff spatialCapacityBump.hasCompactSupport

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocallySobolevPartials
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Classical coordinate partials for the precise continuous representative
of a genuinely local W1,2 function. No global integrability is assumed. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def scalarBallWeakWitness {u : EuclideanPlane → ℝ} (hu : Continuous u)
    {V : EuclideanPlane → EuclideanPlane} (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R))) (R : ℝ) :
    DeGiorgi.MemW1pWitness 2 u (ball 0 R) where
  memLp := continuous_memLp_ball hu R
  weakGrad := V
  weakGrad_component_memLp := hLp R
  isWeakGrad := fun i => weakPartial_restrict_from_univ (hw i) _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PhysicalCoareaCoordinates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical Euclidean plane and complex plane carry the same area
and length measures, and precomposition preserves differential norms. -/
open Set Function MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

def complexPlaneLinearIsometry : EuclideanPlane ≃ₗᵢ[ℝ] ℂ :=
  { complexPlaneCoordinates.toLinearEquiv with
    norm_map' := complexPlaneCoordinates_norm }

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PhysicalLipschitzCoarea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact weighted coarea for a Lipschitz function on the physical
Euclidean plane, with the norm of its actual differential. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

def PhysicalWeightedCoareaIdentity (E : Set EuclideanPlane) (u : EuclideanPlane → ℝ)
    (q : EuclideanPlane → ℝ≥0∞) : Prop :=
  AEMeasurable (sobolevLevelIntegral E u q) volume ∧
    (∫⁻ t, sobolevLevelIntegral E u q t) =
      ∫⁻ x in E, q x * ENNReal.ofReal ‖fderiv ℝ u x‖

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PhysicalFieldCoarea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted coarea identities retaining a specified actual weak-gradient
field, and their disjoint countable assembly. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

def PhysicalFieldCoareaIdentity (E : Set EuclideanPlane) (u : EuclideanPlane → ℝ)
    (V : EuclideanPlane → EuclideanPlane) (q : EuclideanPlane → ℝ≥0∞) : Prop :=
  AEMeasurable (sobolevLevelIntegral E u q) volume ∧
    (∫⁻ t, sobolevLevelIntegral E u q t) = ∫⁻ x in E, q x*ENNReal.ofReal ‖V x‖

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothPhysicalPullback
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth quasiconformal pullback energy in the actual physical plane.
Only the finite compact-set estimate needed for the limiting scalar
transport is asserted. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def physicalSmoothEnergy (u : EuclideanPlane → ℝ) (x : EuclideanPlane) : ℝ :=
  (fderiv ℝ u x (EuclideanSpace.single 0 1))^2 +
    (fderiv ℝ u x (EuclideanSpace.single 1 1))^2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothScalarWeakLimit
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded smooth scalar energies give an actual Sobolev limit, retaining
the common subsequence and every L2 derivative pairing. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

structure ScalarSmoothWeakLimit (v : ℕ → EuclideanPlane → ℝ)
    (u : EuclideanPlane → ℝ) where
  witness : DeGiorgi.MemW1pWitness 2 u univ
  index : ℕ → ℕ
  index_strict : StrictMono index
  pairing : ∀ (i : Fin 2) (w : Lp ℝ 2 (volume : Measure EuclideanPlane)),
    Tendsto (fun n => ∫ x, fderiv ℝ (v (index n)) x (EuclideanSpace.single i 1)*w x)
      atTop (𝓝 (∫ x, witness.weakGrad x i*w x))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PrincipalScalarWeakLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained actual smooth principal maps transport the positive
mollifications of a continuous compact Sobolev scalar to an actual weak
Sobolev limit on the image plane. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami CannonPlane

variable {g : PlaneL2} {k R : ℝ} {S : PrincipalSmoothApproximation g k R}

def principalScalarApproximation (L : PrincipalMapLimit S)
    (u : EuclideanPlane → ℝ) (n : ℕ) : EuclideanPlane → ℝ :=
  planarMollification u n ∘ physicalHomeomorph (S.map (L.index n)).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevEnergyMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual local two-coordinate Sobolev energy as a measure. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

def coordinateSobolevEnergy (V : EuclideanPlane → EuclideanPlane) : Measure (ℝ × ℝ) :=
  volume.withDensity (fun p => ENNReal.ofReal
    ((|V (euclideanPlaneCoordinates.symm p) 0|+|V (euclideanPlaneCoordinates.symm p) 1|)^2))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevGraphEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original Sobolev energy pushed to the scalar graph. The local
capacity cost is bounded by its mass on an actual ambient graph ball. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

def sobolevGraph (u : EuclideanPlane → ℝ) (x : EuclideanPlane) : (ℝ × ℝ) × ℝ :=
  (euclideanPlaneCoordinates x,u x)

def sobolevGraphEnergy (u : EuclideanPlane → ℝ) (V : EuclideanPlane → EuclideanPlane) :
    Measure ((ℝ × ℝ) × ℝ) :=
  Measure.map (sobolevGraph u)
    (volume.withDensity (fun x => ENNReal.ofReal (1+(|V x 0|+|V x 1|)^2)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereLocalMapInjective
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An analytic local chart of a sphere homeomorphism has nonzero
complex derivative, obtained from genuine local injectivity. -/
open Set Filter Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def sphereLocalMapRegion (e : Sphere ≃ₜ Sphere) (p : Sphere) : Set ℂ :=
  {z | chartTransform (e p) (e (chartSymm p z)) ≠ OnePoint.infty}

end CircleDomainRigidity

end

end OAI
end


