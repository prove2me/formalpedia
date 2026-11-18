-- Prove2me | Definitions.Def_OAIQ361V3Ea002
-- name    : OAIQ361V3Ea002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T16:29:07.245175+00:00
-- url     : https://prove2.me/theorems/464511ea-c564-43e8-aa34-e9042cda2f1b
-- title:
--   Definitions bundle OAIQ361V3Ea002 of the split of OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 676 declarations of OpenAI's Lean: 442 definitions, 1 inductive type or structure, 17 instances and 216 theorems. The definitions and types are `OAI.EditApproximation.CP`, `OAI.EditApproximation.ComputedPhysicalCoarseBudget`, `OAI.EditApproximation.ComputedQueryRegisters`, `OAI.EditApproximation.ComputedQueryTableKey`, `OAI.EditApproximation.ComputedQueryTableParent`, `OAI.EditApproximation.DependencyExpansion.Valid`, `OAI.EditApproximation.DependencyExpansion.build`, `OAI.EditApproximation.DependencyExpansion.layerNodeCount`, `OAI.EditApproximation.DependencyExpansion.nodeCount`, `OAI.EditApproximation.DependencyExpansion.nodeCountAtDepth`, `OAI.EditApproximation.DependencyExpansion.nodeCountAtOrAbove`, `OAI.EditApproximation.DependencyExpansion.nodeCountThroughDescent`, `OAI.EditApproximation.FinalProgramDraw`, `OAI.EditApproximation.GP`, `OAI.EditApproximation.GP`, `OAI.EditApproximation.GP`, `OAI.EditApproximation.GP`, `OAI.EditApproximation.GP`, `OAI.EditApproximation.IP`, `OAI.EditApproximation.LP`, `OAI.EditApproximation.LocalCommonDraw`, `OAI.EditApproximation.LocalCommonFinalOutcome`, `OAI.EditApproximation.LocalCommonTerminalDraw`, `OAI.EditApproximation.LocalCommonTrace`, `OAI.EditApproximation.LocalFinalProgramDraw`, `OAI.EditApproximation.LocalFinalProgramOutcome`, `OAI.EditApproximation.LocalScheduledSeedDraw`, `OAI.EditApproximation.LocalScheduledTrace`, `OAI.EditApproximation.LocalTraceFinalOutcome`, `OAI.EditApproximation.PhysicalCommonCoordinate`, `OAI.EditApproximation.PhysicalCommonDraw`, `OAI.EditApproximation.PhysicalGroupArray`, `OAI.EditApproximation.PhysicalGroupKey`, `OAI.EditApproximation.PhysicalGroupStreams`, `OAI.EditApproximation.PhysicalLocalGroupArray`, `OAI.EditApproximation.PhysicalLocalOnlineDraw`, `OAI.EditApproximation.PhysicalLocalProgramCoordinate`, `OAI.EditApproximation.PhysicalLocalProgramDraw`, `OAI.EditApproximation.PhysicalOnlineArray`, `OAI.EditApproximation.PhysicalOnlineKey` and 403 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `EditApproximation_Binary_BinaryPowerStorage`, `EditApproximation_Binary_BinarySampledGroupPolynomial`, `EditApproximation_Binary_BitMemoHeap`, `EditApproximation_Binary_BitMemoSound`, `EditApproximation_Binary_IntegerBinaryOutput`, `EditApproximation_Binary_UnreducedNumerics`, `EditApproximation_Binary_UnreducedOptimizer`, `EditApproximation_Coarse_CoarseReadTree`, `EditApproximation_Geometry_ActualRepresentatives`, `EditApproximation_Geometry_ActualRoundedGroupInputs`, `EditApproximation_Geometry_BandEarlierDependence`, `EditApproximation_Geometry_BandGroupSampling`, `EditApproximation_Geometry_Bellman`, `EditApproximation_Geometry_CellGroupSelection`, `EditApproximation_Geometry_ChargedGlobalQuery`, `EditApproximation_Geometry_ChargedQueryProgress`, `EditApproximation_Geometry_ChargedRandomCoarseOracle`, `EditApproximation_Geometry_ChargedRandomExpansion`, `EditApproximation_Geometry_ChargedRandomGlobalQuery`, `EditApproximation_Geometry_ChargedRandomProgress`, `EditApproximation_Geometry_ChargedSeedQuery`, `EditApproximation_Geometry_CommonArrayFinal`, `EditApproximation_Geometry_CommonArrayTrace`, `EditApproximation_Geometry_CommonSeedTrace`, `EditApproximation_Geometry_ComparisonBounds`, `EditApproximation_Geometry_ComparisonLift`, `EditApproximation_Geometry_ComparisonLiftBounds`, `EditApproximation_Geometry_ComparisonTree`, `EditApproximation_Geometry_DependencyExpansion`, `EditApproximation_Geometry_GatheredLocalStep`, `EditApproximation_Geometry_GlobalQueryCost`, `EditApproximation_Geometry_GlobalQueryProgress`, `EditApproximation_Geometry_Grid`, `EditApproximation_Geometry_GroupCells`, `EditApproximation_Geometry_GroupInputDependence`, `EditApproximation_Geometry_InitialConeGrid`, `EditApproximation_Geometry_LocalCommonOutput`, `EditApproximation_Geometry_LocalCommonSeed`, `EditApproximation_Geometry_LocalFinalAccuracy`, `EditApproximation_Geometry_LocalGroupCones`, `EditApproximation_Geometry_LocalGroupSourceQuery`, `EditApproximation_Geometry_LocalOnlineMassBound`, `EditApproximation_Geometry_LocalOnlineSourceQuery`, `EditApproximation_Geometry_LocalRandomDataQuery`, `EditApproximation_Geometry_LocalRandomQueryKeys`, `EditApproximation_Geometry_LocalRandomSourceQuery`, `EditApproximation_Geometry_LocalRefinementQuery`, `EditApproximation_Geometry_LocalSeedSchedule`, `EditApproximation_Geometry_LocalSeedSequence`, `EditApproximation_Geometry_LocalTraceMemoOutput`, `EditApproximation_Geometry_LocalTraceProgram`, `EditApproximation_Geometry_MemoCodeWork`, `EditApproximation_Geometry_MemoizedOracle`, `EditApproximation_Geometry_OccurrenceIndex`, `EditApproximation_Geometry_OccurrenceLeaf`, `EditApproximation_Geometry_OccurrencePrefix`, `EditApproximation_Geometry_OccurrenceStorage`, `EditApproximation_Geometry_OnlineEarlierDependence`, `EditApproximation_Geometry_ParameterNumericalConstruction`, `EditApproximation_Geometry_PreparedBandPolynomial`, `EditApproximation_Geometry_PreparedCachedKernelWork`, `EditApproximation_Geometry_PreparedGroupPolynomial`, `EditApproximation_Geometry_PreparedInitialPolynomial`, `EditApproximation_Geometry_PreparedLocalGroupPolynomial`, `EditApproximation_Geometry_PreparedShellPolynomial`, `EditApproximation_Geometry_PreparedWarmupPolynomial`, `EditApproximation_Geometry_RefinementBandSupport`, `EditApproximation_Geometry_RefinementDataQuery`, `EditApproximation_Geometry_RefinementDataQueryWork`, `EditApproximation_Geometry_RefinementInitialSupport`, `EditApproximation_Geometry_RoundedComparison`, `EditApproximation_Geometry_RoundedGroupStates`, `EditApproximation_Geometry_SharedActions`, `EditApproximation_Geometry_SharedGroupInputBudget`, `EditApproximation_Geometry_SourceRankedRestriction`, `EditApproximation_Geometry_StateGeometry`, `EditApproximation_Geometry_UnifiedPhysicalTable`, `EditApproximation_Geometry_WarmupQueryKeys`, `EditApproximation_Geometry_WideActions`, `EditApproximation_Geometry_WideBellman`, `EditApproximation_Geometry_WideEarlierInputs`, `EditApproximation_Numerics_RationalRefinement`, `EditApproximation_Probability_AdaptiveSeedTrace`, `EditApproximation_Probability_ExactSampling`, `EditApproximation_Probability_FiniteQueryRestriction`, `EditApproximation_Queries_QueryCallbackPolynomial`, `EditApproximation_Queries_QueryChargedFamily`, `EditApproximation_Queries_QueryChargedFamilySpace`, `EditApproximation_Queries_QueryChargedSeedCost`, `EditApproximation_Queries_QueryChargedSeedSpace`, `EditApproximation_Queries_QueryChargedTableCost`, `EditApproximation_Queries_QueryChargedWarmupCost`, `EditApproximation_Queries_QueryChargedWarmupSpace`, `EditApproximation_Queries_QueryDependencyExpansion`, `EditApproximation_Queries_QueryFamilyMemo`, `EditApproximation_Queries_QueryFamilyMemoSpace`, `EditApproximation_Queries_QueryFamilySpace`, `EditApproximation_Queries_QueryGatherPolynomial`, `EditApproximation_Queries_QueryGatherSpace`, `EditApproximation_Queries_QueryIndexedSpace`, `EditApproximation_Queries_QueryInitialConeSpace`, `EditApproximation_Queries_QueryInitialWarmupPolynomial`, `EditApproximation_Queries_QueryInputSpace`, `EditApproximation_Queries_QueryLocalProgramSpace`, `EditApproximation_Queries_QueryPhysicalInitialCost`, `EditApproximation_Queries_QueryPhysicalReaderSpace`, `EditApproximation_Queries_QueryPhysicalScalarGuards`, `EditApproximation_Queries_QueryProgramPolynomial`, `EditApproximation_Queries_QueryRawWidthPolynomial`, `EditApproximation_Queries_QueryRefinementSpace`, `EditApproximation_Queries_QueryRestrictionSpace`, `EditApproximation_Queries_QueryScalarDispatch`, `EditApproximation_Queries_QueryScalarGuardSpace`, `EditApproximation_Queries_QueryScalarReadSpace`, `EditApproximation_Queries_QueryWarmupSpace`, `EditApproximation_Queries_QueryWarmupUniformCost`, `EditApproximation_Refinement_ComputedBands`, `EditApproximation_Refinement_ComputedCoarseBudget`, `EditApproximation_Refinement_ComputedCoarseExecution`, `EditApproximation_Refinement_ComputedCoarseInputWork`, `EditApproximation_Refinement_ComputedExecutionLaw`, `EditApproximation_Refinement_ComputedPhysicalCoarseWork`, `EditApproximation_Refinement_ComputedPhysicalUniform`, `EditApproximation_Refinement_ComputedPhysicalWork`, `EditApproximation_Refinement_ComputedQueryAnswer`, `EditApproximation_Refinement_ComputedQueryCorrect`, `EditApproximation_Refinement_ComputedQueryExecution`, `EditApproximation_Refinement_ComputedQueryHeap`, `EditApproximation_Refinement_ComputedQueryMemo`, `EditApproximation_Refinement_ComputedQueryNormalizationBudget`, `EditApproximation_Refinement_ComputedQueryProgramWork`, `EditApproximation_Refinement_ComputedQueryRawWork`, `EditApproximation_Refinement_ComputedQueryReadBudget`, `EditApproximation_Refinement_ComputedQueryRegisters`, `EditApproximation_Refinement_ComputedQueryTableBudget`, `EditApproximation_Refinement_ComputedQueryTableWork`, `EditApproximation_Refinement_ComputedQueryTemporarySpace`, `EditApproximation_Refinement_ComputedQueryWarmupBudget`, `EditApproximation_Refinement_ComputedQueryWork`, `EditApproximation_Refinement_ComputedRetainedValues`, `EditApproximation_Refinement_PhysicalBoundedQuery`, `EditApproximation_Refinement_PhysicalCoarseInputWork`, `EditApproximation_Refinement_PhysicalCoarseSeedLaw`, `EditApproximation_Refinement_PhysicalCommonSource`, `EditApproximation_Refinement_PhysicalConditionalNode`, `EditApproximation_Refinement_PhysicalDependencyRank`, `EditApproximation_Refinement_PhysicalFamilyMemo`, `EditApproximation_Refinement_PhysicalFamilyProgram`, `EditApproximation_Refinement_PhysicalFamilyRuntime`, `EditApproximation_Refinement_PhysicalFamilyWork`, `EditApproximation_Refinement_PhysicalFinalAccuracy`, `EditApproximation_Refinement_PhysicalGlobalQuery`, `EditApproximation_Refinement_PhysicalGlobalValue`, `EditApproximation_Refinement_PhysicalLocalGroupKeys`, `EditApproximation_Refinement_PhysicalLocalJointProgram`, `EditApproximation_Refinement_PhysicalLocalOnlineKeys`, `EditApproximation_Refinement_PhysicalLocalProgramLaw`, `EditApproximation_Refinement_PhysicalMedianQuery`, `EditApproximation_Refinement_PhysicalOnlineBand`, `EditApproximation_Refinement_PhysicalParentDraw`, `EditApproximation_Refinement_PhysicalProgramLaw`, `EditApproximation_Refinement_PhysicalQueryProgress`, `EditApproximation_Refinement_PhysicalRandomBoundedCost`, `EditApproximation_Refinement_PhysicalRandomBoundedQuery`, `EditApproximation_Refinement_PhysicalRandomDataRequest`, `EditApproximation_Refinement_PhysicalRandomGlobalProgress`, `EditApproximation_Refinement_PhysicalRandomGlobalQuery`, `EditApproximation_Refinement_PhysicalRandomRequestBounds`, `EditApproximation_Refinement_PhysicalRandomRequestProgress`, `EditApproximation_Refinement_PhysicalRandomValue`, `EditApproximation_Refinement_PhysicalRationalWarmup`, `EditApproximation_Refinement_PhysicalRawGroupProgram`, `EditApproximation_Refinement_PhysicalRawOnlineProgram`, `EditApproximation_Refinement_PhysicalRefinement`, `EditApproximation_Refinement_PhysicalRefinementDataRequest`, `EditApproximation_Refinement_PhysicalRefinementReadWork`, `EditApproximation_Refinement_PhysicalRefinementRequest`, `EditApproximation_Refinement_PhysicalRequestEncoding`, `EditApproximation_Refinement_PhysicalScalarFamily`, `EditApproximation_Refinement_PhysicalScalarReads`, `EditApproximation_Refinement_PhysicalScalarSource`, `EditApproximation_Refinement_PhysicalSeedMedian`, `EditApproximation_Refinement_PhysicalSeedPass`, `EditApproximation_Refinement_PhysicalSeedSchedule`, `EditApproximation_Refinement_PhysicalSeedTables`, `EditApproximation_Refinement_PhysicalSelectionProgram`, `EditApproximation_Refinement_PhysicalSubtree`, `EditApproximation_Refinement_PhysicalUniformAccuracy`, `EditApproximation_Refinement_PhysicalWarmupQuery`, `EditApproximation_Refinement_PhysicalWarmupStepQuery`, `EditApproximation_Refinement_StageComparisonBad`, `EditApproximation_Refinement_StageWarmup`, `EditApproximation_Specification_ConcreteFootprintBridges`, `EditApproximation_Specification_ConcreteFootprints`, `EditApproximation_Specification_RawBand`, `EditApproximation_Specification_RawBandPipelineFootprintBridges`.
--
--   **Imports.** It imports the published bundles `Def_EditApproxScheme_01`, `Def_EditApproxScheme_02`, `Def_EditApproxScheme_03`, `Def_EditApproxScheme_04`, `Def_EditApproxScheme_05`, `Def_EditApproxScheme_06`, `Def_EditApproxScheme_07`, `Def_EditApproxScheme_08`, `Def_EditApproxScheme_09`, `Def_EditApproxScheme_10`, `Def_EditApproxScheme_11`, `Def_EditApproxScheme_13`, `Def_EditApproxScheme_14`, `Def_EditApproxScheme_15`, `Def_EditApproxScheme_16` and `Def_EditApproxScheme_17`; the bundles `OAIQ361V3Ea000` and `OAIQ361V3Ea001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ361V3Ea004`; the statements `OAI.EditApproximation.computedActiveQueryBudget_cap`, `OAI.EditApproximation.computedFamilyCoarseInputWork_le`, `OAI.EditApproximation.computedFamilyTree_valid`, `OAI.EditApproximation.computedPhysicalCoarseWork_expected_le`, `OAI.EditApproximation.computedQueryAnswerWithWork_value`, `OAI.EditApproximation.computedQueryMemoNormalized_correct`, `OAI.EditApproximation.computedQueryMemoNormalized_width`, `OAI.EditApproximation.computedQueryMemoResult_decode`, `OAI.EditApproximation.computedQueryTable_work_width`, `OAI.EditApproximation.computedQueryTemporaryCells_polynomial`, `OAI.EditApproximation.computed_chargedRandomGlobalQuery_earlier_reads`, `OAI.EditApproximation.physicalFamilyCoarseInputWork_le`, `OAI.EditApproximation.physicalFamilyMemoCoarseWork_expected_le`, `OAI.EditApproximation.queryChargedFamilyTable_semantic_width`, `OAI.EditApproximation.queryChargedFamilyTable_semantic_work_bound` and `OAI.EditApproximation.queryChargedFamilyTable_width`; the proofs of `OAI.EditApproximation.BinaryFraction.coarseRootReadExtra_bound`, `OAI.EditApproximation.BinaryFraction.computedCoarseIndexedInitialWithWork_bound`, `OAI.EditApproximation.BinaryFraction.preparedBandActionWithWork_cost`, `OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsWithWork_cost`, `OAI.EditApproximation.BinaryFraction.queryEarlierRepresentativesWithWork_bounds`, `OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_bounds`, `OAI.EditApproximation.BinaryFraction.queryGroupSourceKeysWithWork_bounds`, `OAI.EditApproximation.BinaryFraction.queryRawCentersWithWork_bounds`, `OAI.EditApproximation.BinaryFraction.querySharedInputsWithWork_bounds_on`, `OAI.EditApproximation.computedFamilyCoarseInputWork_le`, `OAI.EditApproximation.computedFamilyResult_requests_le`, `OAI.EditApproximation.computedFamilyTree_valid`, `OAI.EditApproximation.computedPhysicalCoarseWork_expected_le`, `OAI.EditApproximation.computedQueryAnswerWithWork_value`, `OAI.EditApproximation.computedQueryMemoResult_decode`, `OAI.EditApproximation.computedQueryTable_work_width`, `OAI.EditApproximation.computedQueryTemporaryCells_polynomial`, `OAI.EditApproximation.computed_chargedRandomGlobalQuery_earlier_reads`, `OAI.EditApproximation.computed_localRandomDataQuery_table_cost`, `OAI.EditApproximation.queryChargedFamilyTable_semantic_width`, `OAI.EditApproximation.queryChargedFamilyTable_semantic_work_bound`, `OAI.EditApproximation.queryChargedFamilyTable_width`, `OAI.EditApproximation.queryChargedWarmup_refines`, `OAI.EditApproximation.queryFamilyBoundedActive_refines`, `OAI.EditApproximation.queryFamilyBoundedActive_work_bound`, `OAI.EditApproximation.queryInitialConeProgramAt_work_bound`, `OAI.EditApproximation.queryLocalRandomSources_refines`, `OAI.EditApproximation.queryLocalRandomSources_work_bound`, `OAI.EditApproximation.queryLocalRefinement_work_bound`, `OAI.EditApproximation.queryOnlineSourceGather_work_bound` and `OAI.EditApproximation.queryPhysicalInitial_width`.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Nat
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_07
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_EditApproxScheme_16
import Definitions.Def_EditApproxScheme_17
import Definitions.Def_OAIQ361V3Ea000
import Definitions.Def_OAIQ361V3Ea001

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_UnreducedNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The numerical primitives executed on unreduced fractions. Their exact
values agree with the rational routines; their stored denominators
have polynomial bit length without cancellation or Euclidean normalization. -/

namespace EditApproximation

open Finset
namespace UnreducedRational

def logarithmPartial (b : UnreducedRational) : ℕ → UnreducedRational
  | 0 => zero
  | K + 1 => (logarithmPartial b K).add ((b.pow (2 * K + 1)).div (nat (2 * K + 1)))

def logarithm (r : UnreducedRational) (K : ℕ) : UnreducedRational :=
  (nat 2).mul (logarithmPartial ((r.sub one).div (r.add one)) K)

def optimizerIterate {ι : Type*} (initial : ι → UnreducedRational)
    (selected : ℕ → ι → UnreducedRational) : ℕ → ι → UnreducedRational
  | 0 => initial
  | j + 1 => fun i => ((one.sub (optimizerStep j)).mul (optimizerIterate initial selected j i)).add
      ((optimizerStep j).mul (selected j i))

end UnreducedRational
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_ExactSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Exact fair-bit sampling of the optimizer mixture

The finite-word rejection calculation follows Section 9.
The random trial is encoded from actual Boolean bits. First-success trace
probabilities determine the output law and expected number of trials.
-/

namespace EditApproximation

open Finset

theorem optimizerTriangularMass_monotone : Monotone optimizerTriangularMass := by
  intro a b hab
  have hproduct := Nat.mul_le_mul hab (Nat.add_le_add_right hab 1)
  rw [← optimizerTriangularMass_twice a, ← optimizerTriangularMass_twice b] at hproduct
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_UnreducedOptimizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fraction-only implementation of the actual finite optimizer. None of
its arithmetic or score comparisons requires reduced rational numbers. -/

namespace EditApproximation

open Finset
namespace UnreducedRational

def scoredArgmax {α : Type*} (score : α → UnreducedRational) : List α → Option (α × UnreducedRational)
  | [] => none
  | a :: rest =>
    let current := score a
    match scoredArgmax score rest with
    | none => some (a, current)
    | some best => if current.lt best.2 then some best else some (a, current)

def gradientCell {d : ℕ} (G : ℕ) (linear point : Vector UnreducedRational d) (i : Fin d) : UnreducedRational :=
  ((logarithm ((point.get i).add ((nat G).pow 50).inv) (G ^ 60)).neg.sub one).add (linear.get i)

def gradient {d : ℕ} (G : ℕ) (linear point : Vector UnreducedRational d) : Vector UnreducedRational d :=
  Vector.ofFn (gradientCell G linear point)

def maximizer {d : ℕ} (gradient : Vector UnreducedRational d)
    (vertices : List (Vector UnreducedRational d)) : Vector UnreducedRational d :=
  ((scoredArgmax (dot gradient) vertices).map Prod.fst).getD (Vector.replicate d zero)

def finiteOptimizer {d : ℕ} (vertices : List (Vector UnreducedRational d))
    (linear : Vector UnreducedRational d) (G : ℕ) : ℕ → Vector UnreducedRational d
  | 0 => vertices.headD (Vector.replicate d zero)
  | j + 1 =>
    let previous := finiteOptimizer vertices linear G j
    let selected := maximizer (gradient G linear previous) vertices
    Vector.ofFn fun i => ((one.sub (optimizerStep j)).mul (previous.get i)).add
      ((optimizerStep j).mul (selected.get i))

end UnreducedRational
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPowerStorage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Construction of a prescribed power denominator uses literal Boolean
multiplication and trimming. The subsequent cache compression therefore has
no uncharged conversion from a natural number to its binary representation. -/

namespace EditApproximation



theorem refinementBaseWithWork_value (ell : List Bool) :
    bitWordValue (refinementBaseWithWork ell).1 = bitWordValue ell ^ 10 + 1 := by
  simp only [refinementBaseWithWork, trimBitWordWithWork_value, bitAddWithWork_value,
    bitPowerWithWork_value, bitWordValue, Bool.toNat_true, Bool.toNat_false]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_StateGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# The finite domain of valid target states

The endpoint domain is enumerated by actual bounded natural loops. A
state's true cost and signed length gap use the stored target substring.
-/

namespace EditApproximation

open EditDistortion





theorem targetStates_complete (n : ℕ) (q : TargetInterval n) : q ∈ targetStates n := by
  apply List.mem_flatMap.mpr
  refine ⟨q.lo, List.mem_range.mpr (Nat.lt_succ_of_le (q.ordered.trans q.valid)), ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨q.hi, List.mem_range.mpr (Nat.lt_succ_of_le q.valid), ?_⟩
  rw [makeTargetState, dite_eq_left (show q.lo ≤ q.hi ∧ q.hi ≤ n from ⟨q.ordered, q.valid⟩)]



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Bellman
attribute [-instance] _root_.OAI.EditApproximation.physicalNodeFintype _root_.OAI.EditApproximation.physicalScalarIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite Bellman propagation and warmup

The action minimum is computed by a finite list with the initial cone as
fallback. Empty action families need no extended-real convention. The
warmup lemmas concern the actual repeated finite Bellman operator.
-/

namespace EditApproximation

open Finset

def bellmanActionValue {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → ℝ) (L : ℝ) (child : Child → ℝ)
    (query : Parent) (action : BellmanAction Parent Child M) : ℝ :=
  L * distance query action.center + action.connection + ∑ i, child (action.childState i)

def finiteBellman {Parent Child : Type*} {M : ℕ}
    (fallback : Parent → ℝ) (distance : Parent → Parent → ℝ) (L : ℝ)
    (actions : List (BellmanAction Parent Child M)) (child : Child → ℝ) (query : Parent) : ℝ :=
  finiteMinimum (fallback query) (actions.map (bellmanActionValue distance L child query))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_RationalRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Rational execution of the Bellman and refinement operations

Every finite minimum, cone cost, warmup iteration, and refinement update
is computed in rational arithmetic. The real analysis used elsewhere is
the exact cast of these operations. An absent online candidate returns
the cone minimum, avoiding an extended-real value in the implementation.
-/

namespace EditApproximation



def RationalBellmanAction.toReal {Parent Child : Type*} {M : ℕ}
    (action : RationalBellmanAction Parent Child M) : BellmanAction Parent Child M :=
  ⟨action.center, action.connection, action.childState⟩





end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Grid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Integer endpoint grids

Rounding is an executable integer division. It preserves valid interval
states and shared endpoints, and the edit-distance perturbation is bounded
by the actual two remainders. No real-valued grid is substituted for it.
-/

namespace EditApproximation



theorem roundInterval_shared {n spacing : ℕ} (first second : TargetInterval n)
    (hshared : first.hi = second.lo) :
    (roundInterval spacing first).hi = (roundInterval spacing second).lo := by
  exact congrArg (gridRound spacing) hshared

theorem roundInterval_error {n : ℕ} (spacing : ℕ) (hspacing : 0 < spacing)
    (state : TargetInterval n) :
    Nat.dist state.lo (roundInterval spacing state).lo +
      Nat.dist state.hi (roundInterval spacing state).hi < 2 * spacing := by
  have hlo := gridRound_error_lt spacing state.lo hspacing
  have hhi := gridRound_error_lt spacing state.hi hspacing
  change Nat.dist state.lo (gridRound spacing state.lo) +
    Nat.dist state.hi (gridRound spacing state.hi) < 2 * spacing
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SharedActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact connection cancellation for shared-endpoint finite actions. -/

namespace EditApproximation

theorem round_shared_action {n M g : ℕ} (hM : 0 < M) (q : TargetInterval n)
    (states : Fin M → TargetInterval n)
    (hstart : (states ⟨0, hM⟩).lo = q.lo)
    (hend : (states ⟨M - 1, by omega⟩).hi = q.hi)
    (hnext : ∀ i j : Fin M, j.val = i.val + 1 → (states i).hi = (states j).lo)
    (hqGrid : g ∣ q.lo ∧ g ∣ q.hi) :
    endpointActionConnection q (fun i => roundInterval g (states i)) = 0 := by
  apply endpointActionConnection_zero hM q
  · change gridRound g (states ⟨0, hM⟩).lo = q.lo
    rw [hstart, gridRound_of_dvd hqGrid.1]
  · change gridRound g (states ⟨M - 1, by omega⟩).hi = q.hi
    rw [hend, gridRound_of_dvd hqGrid.2]
  · intro i j hij
    exact roundInterval_shared (states i) (states j) (hnext i j hij)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_InitialConeGrid
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# A rounded eligible center for each positive-cost query

This uses the actual natural division grid and the dyadic scale selected
from the integer edit cost. It supplies a finite-family witness for the
initial cone minimum.
-/

namespace EditApproximation





theorem rounded_seedGrid_error {n : ℕ} (b P : ℕ) (hP : 0 < P)
    (q : TargetInterval n) :
    (targetEndpointDistance q (roundInterval (seedGridSpacing b P) q) : ℚ) * P ≤ 2 * b := by
  by_cases hg : b / P ≤ 1
  · have he : targetEndpointDistance q (roundInterval (seedGridSpacing b P) q) = 0 := by
      simp [targetEndpointDistance, roundInterval, seedGridSpacing, max_eq_left hg]
    rw [he]
    simp only [Nat.cast_zero, zero_mul]
    positivity
  · have hquot : 1 ≤ b / P := by omega
    have he := roundInterval_error (b / P) (by omega) q
    have hdiv := Nat.div_mul_le_self b P
    have hprod : targetEndpointDistance q (roundInterval (seedGridSpacing b P) q) * P ≤ 2 * b := by
      unfold seedGridSpacing
      rw [max_eq_right hquot]
      change (Nat.dist q.lo (roundInterval (b / P) q).lo +
        Nat.dist q.hi (roundInterval (b / P) q).hi) * P ≤ 2 * b
      nlinarith
    exact_mod_cast hprod

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_WideActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Executable wide action lists

Endpoint indices are generated in the radius-`10b` grid boxes anchored
at the physical source cuts. Lists contain exactly the valid grid states
in those boxes and their Cartesian product over labeled children.
-/

namespace EditApproximation



theorem gridStateBox_complete {n g radius lo hi : ℕ} (hg : 0 < g)
    (r : TargetInterval n) (hlo : Nat.dist lo r.lo ≤ radius)
    (hhi : Nat.dist hi r.hi ≤ radius) (hgrid : g ∣ r.lo ∧ g ∣ r.hi) :
    r ∈ gridStateBox n g radius lo hi := by
  have hlo' : lo - radius ≤ r.lo ∧ r.lo ≤ lo + radius := by unfold Nat.dist at hlo; omega
  have hhi' : hi - radius ≤ r.hi ∧ r.hi ≤ hi + radius := by unfold Nat.dist at hhi; omega
  apply List.mem_flatMap.mpr
  refine ⟨r.lo, gridPointsBetween_complete hg hlo'.1 hlo'.2 hgrid.1, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨r.hi, gridPointsBetween_complete hg hhi'.1 hhi'.2 hgrid.2, ?_⟩
  rw [makeTargetState, dite_eq_left (show r.lo ≤ r.hi ∧ r.hi ≤ n from ⟨r.ordered, r.valid⟩)]





theorem wideActionList_complete {nx ny M b P : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (action : Fin M → TargetInterval ny)
    (hgrid : ∀ i, seedGridSpacing b P ∣ (action i).lo ∧ seedGridSpacing b P ∣ (action i).hi)
    (hlo : ∀ i, Nat.dist (r.lo + ((sourceChild parent i).lo - parent.lo)) (action i).lo ≤ 10 * b)
    (hhi : ∀ i, Nat.dist (r.lo + ((sourceChild parent i).hi - parent.lo)) (action i).hi ≤ 10 * b) :
    action ∈ wideActionList M parent r b P := by
  apply finiteAssignments_complete
  intro i
  exact gridStateBox_complete (by unfold seedGridSpacing; omega) (action i)
    (hlo i) (hhi i) (hgrid i)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# The literal finite predicted band

The band is a rationally decidable filter of the enumerated wide actions.
Its internal-cut diameter follows from the actual finite prefix predictor,
without assuming a predictor Lipschitz contract.
-/

namespace EditApproximation









theorem computedBandActions_mem {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (tau theta velocity : ℚ)
    (child : Fin M → TargetInterval ny → ℚ) (states : Fin M → TargetInterval ny)
    (hstates : states ∈ computedBandActions parent r b P tau theta velocity child) :
    ∃ hnonempty : wideActionList M parent r b P ≠ [],
      states ∈ wideActionList M parent r b P ∧ |velocity| ≤ 1 - tau ∧
        bandActionPredicate parent r b tau theta velocity (wideActionList M parent r b P) hnonempty child states := by
  by_cases hempty : wideActionList M parent r b P = []
  · simp only [computedBandActions, dite_eq_left hempty, List.not_mem_nil] at hstates
  · by_cases hvelocity : |velocity| ≤ 1 - tau
    · simp only [computedBandActions, dite_eq_right hempty, ite_eq_left hvelocity] at hstates
      obtain ⟨hmem, hpredicate⟩ := List.mem_filter.mp hstates
      exact ⟨hempty, hmem, hvelocity, of_decide_eq_true hpredicate⟩
    · simp only [computedBandActions, dite_eq_right hempty, ite_eq_right hvelocity,
        List.not_mem_nil] at hstates

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandGroupSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Executable shared group estimates

All dyadic powers in the prescribed closed range are enumerated, including
negative exponents. A scale is evaluated exactly when its sample count
reaches the child count; otherwise one shared array of uniform labels is
used for every member of the group. The selected member is the first
minimizer in the fixed list order.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory



section ActualUnskippedGroup

variable {α : Type*} {source target : List α} {M b P thetaExponent : ℕ}
  {parent : TargetInterval source.length} {tau F : ℚ}
  {child initial : Fin M → TargetInterval target.length → ℚ}

theorem testUnskippedBand_accept
    (member : UnskippedBand source target parent b P thetaExponent tau F child initial) :
    testUnskippedBand source target parent b P thetaExponent tau F child initial member.center = some member := by
  cases member with
  | mk center nonempty hsum hwide hgap =>
    simp only [testUnskippedBand, dite_eq_right nonempty, dite_eq_left hsum,
      dite_eq_left hwide, dite_eq_left hgap]

theorem unskippedBandList_mem_iff
    (centers : List (TargetInterval target.length))
    (member : UnskippedBand source target parent b P thetaExponent tau F child initial) :
    member ∈ unskippedBandList source target parent b P thetaExponent tau F child initial centers ↔
      member.center ∈ centers := by
  constructor
  · intro hmember
    obtain ⟨center, hcenter, haccepted⟩ := List.mem_filterMap.mp hmember
    rwa [testUnskippedBand_center center member haccepted]
  · intro hcenter
    exact List.mem_filterMap.mpr ⟨member.center, hcenter, testUnskippedBand_accept member⟩


end ActualUnskippedGroup

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_WideBellman
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bellman cones of the actual labeled finite wide actions preserve both lower invariants. -/

namespace EditApproximation

open Finset

noncomputable def actualWideActions {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P : ℕ) :
    List (BellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M) :=
  representatives.flatMap fun br => (wideActionList M parent br.2 br.1 P).map fun states =>
    ⟨br.2, endpointActionConnection br.2 states, fun i => (i, states i)⟩

noncomputable def actualWideBellman {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P : ℕ)
    (initial : TargetInterval ny → ℝ) (L : ℝ)
    (child : Fin M → TargetInterval ny → ℝ) (q : TargetInterval ny) : ℝ :=
  finiteBellman initial (fun q r => targetEndpointDistance q r) L
    (actualWideActions parent representatives P) (fun is => child is.1 is.2) q

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRationalWarmup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Rational execution of the physical wide-action warmup, with exact real casts. -/

namespace EditApproximation

open Finset



def rationalPhysicalWarmup {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℚ) (initial : PhysicalEntry M J target.length → ℚ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length)) :
    ℕ → PhysicalEntry M J target.length → ℚ :=
  rationalWarmup (rationalPhysicalBellman source target P L initial representatives) initial

def rationalPhysicalWarmupAverage {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℚ) (initial : PhysicalEntry M J target.length → ℚ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (T : ℕ) (state : PhysicalEntry M J target.length) : ℚ :=
  (∑ t ∈ range T, rationalPhysicalWarmup source target P L initial representatives t state) / T

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ActualRepresentatives
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.dyadicScalesWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite representative list and the actual rounded comparison representative. -/

namespace EditApproximation

theorem representativeList_mem {n N P F b : ℕ} (a : ℚ)
    (initial : TargetInterval n → ℚ) (r : TargetInterval n)
    (hb : b ∈ dyadicScales N)
    (hgrid : seedGridSpacing b P ∣ r.lo ∧ seedGridSpacing b P ∣ r.hi)
    (hlower : (b : ℚ) / (4 * a) ≤ initial r) (hupper : initial r ≤ 8 * F * b) :
    (b, r) ∈ representativeList N P F a initial := by
  apply List.mem_flatMap.mpr
  refine ⟨b, hb, List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨targetStates_complete n r, ?_⟩, rfl⟩⟩
  simpa using ⟨hgrid.1, hgrid.2, hlower, hupper⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_GroupCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Whole rational cells are enumerated by bounded ranges of grid indices. -/

namespace EditApproximation



theorem cellTargetStates_mem {n g : ℕ} {side : ℚ} (cell : ℕ × ℕ) (hg : 0 < g)
    (q : TargetInterval n) :
    q ∈ cellTargetStates n g side cell ↔
      g ∣ q.lo ∧ g ∣ q.hi ∧
      (cell.1 : ℚ) * side ≤ q.lo ∧ (q.lo : ℚ) < ((cell.1 : ℚ) + 1) * side ∧
      (cell.2 : ℚ) * side ≤ q.hi ∧ (q.hi : ℚ) < ((cell.2 : ℚ) + 1) * side := by
  constructor
  · intro hq
    obtain ⟨lo, hlo, hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨hi, hhi, hq⟩ := List.mem_filterMap.mp hq
    have hstate : q.lo = lo ∧ q.hi = hi := by
      unfold makeTargetState at hq
      split_ifs at hq with hvalid
      have heq := Option.some.inj hq
      exact ⟨congrArg TargetInterval.lo heq.symm, congrArg TargetInterval.hi heq.symm⟩
    rw [← hstate.1] at hlo
    rw [← hstate.2] at hhi
    have hl := cellGridPoints_mem hg |>.mp hlo
    have hh := cellGridPoints_mem hg |>.mp hhi
    exact ⟨hl.1, hh.1, hl.2.1, hl.2.2, hh.2.1, hh.2.2⟩
  · rintro ⟨hlo, hhi, hloL, hloU, hhiL, hhiU⟩
    apply List.mem_flatMap.mpr
    refine ⟨q.lo, (cellGridPoints_mem hg).mpr ⟨hlo, hloL, hloU⟩, List.mem_filterMap.mpr ?_⟩
    refine ⟨q.hi, (cellGridPoints_mem hg).mpr ⟨hhi, hhiL, hhiU⟩, ?_⟩
    rw [makeTargetState, dite_eq_left (show q.lo ≤ q.hi ∧ q.hi ≤ n from ⟨q.ordered, q.valid⟩)]



theorem cellRepresentativeStates_mem_representatives {n N P F b : ℕ}
    (a : ℚ) (initial : TargetInterval n → ℚ) (theta : ℚ) (cell : ℕ × ℕ)
    (r : TargetInterval n) (hb : b ∈ dyadicScales N)
    (hr : r ∈ cellRepresentativeStates n P F b a initial theta cell) :
    (b, r) ∈ representativeList N P F a initial := by
  obtain ⟨hcell, heligible⟩ := List.mem_filter.mp hr
  have hg : 0 < seedGridSpacing b P := by unfold seedGridSpacing; omega
  have hgrid := (cellTargetStates_mem cell hg r).mp hcell
  exact representativeList_mem a initial r hb ⟨hgrid.1, hgrid.2.1⟩
    (of_decide_eq_true heligible).1 (of_decide_eq_true heligible).2

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_CellGroupSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Literal unskipped groups of whole cells and their selected wide actions. -/

namespace EditApproximation

open Finset



theorem chooseCellGroupAction_wide_mem {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N b P F thetaExponent Q : ℕ) (tau a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial value : Fin M → TargetInterval target.length → ℚ) (cell : ℕ × ℕ)
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (hb : b ∈ dyadicScales N) (action : RationalBellmanAction
      (TargetInterval target.length) (Fin M × TargetInterval target.length) M)
    (hselected : chooseCellGroupAction source target parent b P F thetaExponent Q tau a
      parentInitial child initial value cell draw = some action) :
    action ∈ rationalActualWideActions parent (representativeList N P F a parentInitial) P := by
  unfold chooseCellGroupAction at hselected
  dsimp only at hselected
  split_ifs at hselected with hempty
  have heq := Option.some.inj hselected
  rw [← heq]
  apply UnskippedBand.rationalAction_wide_mem
  apply cellRepresentativeStates_mem_representatives a parentInitial _ cell _ hb
  apply (unskippedBandList_mem_iff _ _).mp
  exact (chooseUnskippedGroup_spec Q value _ hempty draw).1

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_StageWarmup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The literal initial table, representative enumeration and rational warmup of one refinement pass. -/

namespace EditApproximation



def stageWarmup {α : Type*} [DecidableEq α] {M J : ℕ} (source target : List α)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ) :
    ℕ → PhysicalEntry M J target.length → ℚ :=
  rationalPhysicalWarmup source target P (128 * F) (stageInitial source target U N P F A)
    (stageRepresentatives source target U N P F A)

def stageWarmupMass {α : Type*} [DecidableEq α] {M J : ℕ} (source target : List α)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ) (T : ℕ) :
    PhysicalEntry M J target.length → ℚ :=
  rationalPhysicalWarmupAverage source target P (128 * F) (stageInitial source target U N P F A)
    (stageRepresentatives source target U N P F A) T

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
The complete physical refinement recurrence. Current-index recursive requests
go only to physical children. The selection interface records literal wide
list membership, and carries no approximation or probability assumption.
-/

namespace EditApproximation





def physicalRefinement {α : Type*} [DecidableEq α] {M J : ℕ} (source target : List α)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J) : ℕ → TargetInterval target.length → ℚ :=
  if hbelow : node.1.val < J then
    if (physicalSourceInterval source.length node).hi - (physicalSourceInterval source.length node).lo ≤ 1 then
      fun _ q => stageInitial source target U N P F A (node, q)
    else
      let children : PhysicalChildTables M target.length := fun i =>
        physicalRefinement source target U N P F A T delta choices (physicalChild node hbelow i)
      fun t q => match t with
        | 0 => stageWarmup source target U N P F A T (node, q)
        | s + 1 => rationalWideStep (physicalSourceInterval source.length node)
            (stageRepresentatives source target U N P F A node) P
            (fun r => stageInitial source target U N P F A (node, r)) (128 * F) delta
            (fun is => children is.1 s is.2) (fun is => children is.1 (s + 1) is.2)
            (choices.groups node children (s + 1)) (choices.online node children (s + 1) q) q
  else fun _ q => stageInitial source target U N P F A (node, q)
termination_by J - node.1.val
decreasing_by
  unfold physicalChild
  dsimp only
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalGroupCones
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Cell-keyed shared draws permit direct local group enumeration. The
complete and local finite programs use the same draw at every cell label. -/

namespace EditApproximation

def representativeCells {n : ℕ} (N P F b : ℕ) (a theta : ℚ)
    (initial : TargetInterval n → ℚ) : List (ℕ × ℕ) :=
  (((representativeList N P F a initial).filter fun br => decide (br.1 = b)).map
    fun br => targetCell (theta * b) br.2).eraseDups



section CellPrograms

variable {α : Type*} {M : ℕ} (source target : List α)
  (parent : TargetInterval source.length) (N P F exponent Q : ℕ) (tau a : ℚ)
  (parentInitial : TargetInterval target.length → ℚ)
  (child initial current : Fin M → TargetInterval target.length → ℚ)
  (draw : CellGroupDraws M F Q)

local notation "theta" => (2 : ℚ) ^ (-(exponent : ℤ))

def completeCellGroupActions : List (PhysicalRationalAction M target.length) :=
  (dyadicScales N).flatMap fun b =>
    (representativeCells N P F b a theta parentInitial).filterMap fun cell =>
      chooseCellGroupAction source target parent b P F exponent Q tau a parentInitial
        child initial current cell (draw b cell)



end CellPrograms

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalOnlineBand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Online actions from the actual physical child histories

The fixed representative band uses the rational warmup-average child
table. Its envelopes scan the literal initial child table. Online gains
and decrements are computed from the full physical refinement histories.
-/

namespace EditApproximation

open Finset

theorem representativeBandActions_wide {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (b P : ℕ) (tau theta : ℚ) (child : Fin M → TargetInterval target.length → ℚ)
    (action : Fin M → TargetInterval target.length)
    (haction : action ∈ representativeBandActions source target parent r b P tau theta child) :
    action ∈ wideActionList M parent r b P := by
  by_cases hwide : wideActionList M parent r b P = []
  · simp only [representativeBandActions, dite_eq_left hwide, List.not_mem_nil] at haction
  · by_cases hZ : 0 < rationalWideActionMinimum parent r b P hwide child
    · simp only [representativeBandActions, dite_eq_right hwide, ite_eq_left hZ] at haction
      exact (computedBandActions_mem parent r b P tau theta _ child action haction).choose_spec.1
    · simp only [representativeBandActions, dite_eq_right hwide, ite_eq_right hZ, List.not_mem_nil] at haction


section PhysicalBand

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A))
  (node : PhysicalNode M J) (hbelow : node.1.val < J)

def physicalBandChildMassTable (i : Fin M) (s : TargetInterval target.length) : ℚ :=
  stageWarmupMass source target U N P F A T (physicalChild node hbelow i, s)

def physicalBandActions (b thetaExponent : ℕ) (tau : ℚ) (r : TargetInterval target.length) :
    List (Fin M → TargetInterval target.length) :=
  representativeBandActions source target (physicalSourceInterval source.length node) r b P tau
    ((2 : ℚ) ^ (-(thetaExponent : ℤ))) (physicalBandChildMassTable source target U N P F A T node hbelow)

def physicalBandEnvelope (b thetaExponent : ℕ) (tau : ℚ) (r : TargetInterval target.length) (i : Fin M) : ℚ :=
  bandChildEnvelope b (physicalBandActions source target U N P F A T node hbelow b thetaExponent tau r)
    (physicalBandChildInitial source target U N P F A node hbelow) i


end PhysicalBand

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSelectionProgram
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalEntryCodeWithWork_value _root_.OAI.EditApproximation.physicalNodeCodeWithWork_value _root_.OAI.EditApproximation.physicalSubtreeNode_zero _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.treeLayerCodeWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Finite online and whole-cell candidate programs

Physical selections use the representative and guarded band lists. Each
band has its own finite optimizer stream; every whole cell has shared
per-scale child streams. These streams define coherent finite tables.
-/

namespace EditApproximation

open Finset



section Program

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T thetaExponent H Q : ℕ) (tau η κ : ℚ)

local notation "representatives" => stageRepresentatives source target U N P F A
local notation "theta" => (2 : ℚ) ^ (-(thetaExponent : ℤ))

def physicalProgramBandG (node : PhysicalInternalNode M J)
    (representative : Fin (representatives node.1).length) : ℕ :=
  let br := (representatives node.1).get representative
  H + (bandCoordinates (physicalBandActions source target U N P F A T node.1 node.2
    br.1 thetaExponent tau br.2).toFinset).card + 2

def physicalProgramBandK (node : PhysicalInternalNode M J)
    (representative : Fin (representatives node.1).length) : ℕ :=
  (physicalProgramBandG source target U N P F A T thetaExponent H tau node representative) ^ 80


theorem physicalProgramBandG_ge_two (node : PhysicalInternalNode M J)
    (representative : Fin (representatives node.1).length) :
    2 ≤ physicalProgramBandG source target U N P F A T thetaExponent H tau node representative := by
  dsimp only [physicalProgramBandG]
  omega

theorem physicalProgramBandK_positive (node : PhysicalInternalNode M J)
    (representative : Fin (representatives node.1).length) :
    0 < physicalProgramBandK source target U N P F A T thetaExponent H tau node representative := by
  exact pow_pos (lt_of_lt_of_le (by norm_num : 0 < 2)
    (physicalProgramBandG_ge_two source target U N P F A T thetaExponent H tau node representative)) 80


def physicalProgramCells (node : PhysicalNode M J) (b : ℕ) : List (ℕ × ℕ) :=
  (((representatives node).filter fun br => decide (br.1 = b)).map
    fun br => targetCell (theta * b) br.2).eraseDups

def physicalBandOnlineCandidate (node : PhysicalInternalNode M J)
    (br : ℕ × TargetInterval target.length) (children : PhysicalChildTables M target.length)
    (t G K : ℕ) (integer : Fin (optimizerTriangularMass K)) :
    Option (PhysicalRationalAction M target.length) :=
  let band := physicalBandActions source target U N P F A T node.1 node.2 br.1 thetaExponent tau br.2
  if hband : band = [] then none else
    match testUnskippedBand source target (physicalSourceInterval source.length node.1)
      br.1 P thetaExponent tau F
      (physicalBandChildMassTable source target U N P F A T node.1 node.2)
      (physicalBandChildInitial source target U N P F A node.1 node.2) br.2 with
    | none => none
    | some _ => some (sharedBandRationalAction br.2
      (finiteOptimizerActionDraw band hband
        (physicalBandEnvelope source target U N P F A T node.1 node.2 br.1 thetaExponent tau br.2)
        (rationalOnlineLinear η κ
          (childGain (physicalBandEnvelope source target U N P F A T node.1 node.2 br.1 thetaExponent tau br.2)
            (fun t coordinate => children coordinate.1 t coordinate.2))
          (childDecrement (physicalBandEnvelope source target U N P F A T node.1 node.2 br.1 thetaExponent tau br.2)
            (fun t coordinate => children coordinate.1 t coordinate.2)) t)
        G
        K integer))

def physicalProgramOnlineCandidate (node : PhysicalInternalNode M J)
    (representative : Fin (representatives node.1).length) (children : PhysicalChildTables M target.length)
    (t : ℕ)
    (integer : Fin (optimizerTriangularMass
      (physicalProgramBandK source target U N P F A T thetaExponent H tau node representative))) :
    Option (PhysicalRationalAction M target.length) :=
  physicalBandOnlineCandidate source target U N P F A T thetaExponent tau η κ node
    ((representatives node.1).get representative) children t
    (physicalProgramBandG source target U N P F A T thetaExponent H tau node representative)
    (physicalProgramBandK source target U N P F A T thetaExponent H tau node representative) integer

abbrev PhysicalOnlineStreams (R : ℕ) := ∀ node : PhysicalInternalNode M J,
  ∀ representative : Fin (representatives node.1).length,
    Fin R → Fin (optimizerTriangularMass
      (physicalProgramBandK source target U N P F A T thetaExponent H tau node representative))

abbrev PhysicalGroupStreams (R : ℕ) := ∀ node : PhysicalInternalNode M J,
  ∀ scale : Fin (dyadicScales N).length,
    ∀ _cell : Fin (physicalProgramCells source target U N P F A thetaExponent node.1
      ((dyadicScales N).get scale)).length,
      Fin R → ∀ h : Fin (groupDyadicScales M ((dyadicScales N).get scale) F).length,
        Fin (groupSampleCount M Q ((dyadicScales N).get scale)
          (groupDyadicScaleAt M ((dyadicScales N).get scale) F h)) → Fin M

def physicalProgramGroups {R : ℕ} [NeZero R]
    (stream : PhysicalGroupStreams source target U N P F A thetaExponent Q R)
    (node : PhysicalNode M J) (children : PhysicalChildTables M target.length) (t : ℕ) :
    List (PhysicalRationalAction M target.length) :=
  if hbelow : node.1.val < J then
    (List.finRange (dyadicScales N).length).flatMap fun scale =>
      (List.finRange (physicalProgramCells source target U N P F A thetaExponent node
        ((dyadicScales N).get scale)).length).filterMap fun cell =>
        chooseCellGroupAction source target (physicalSourceInterval source.length node)
          ((dyadicScales N).get scale) P F thetaExponent Q tau (refinementFactor A F)
          (fun q => stageInitial source target U N P F A (node, q))
          (physicalBandChildMassTable source target U N P F A T node hbelow)
          (physicalBandChildInitial source target U N P F A node hbelow)
          (fun i q => children i t q)
          ((physicalProgramCells source target U N P F A thetaExponent node
            ((dyadicScales N).get scale)).get cell)
          (stream ⟨node, hbelow⟩ scale cell (Fin.ofNat R (t - 1)))
  else []

theorem physicalProgramGroups_wide {R : ℕ} [NeZero R]
    (stream : PhysicalGroupStreams source target U N P F A thetaExponent Q R)
    (node : PhysicalNode M J) (children : PhysicalChildTables M target.length) (t : ℕ)
    (action : PhysicalRationalAction M target.length)
    (hselected : action ∈ physicalProgramGroups source target U N P F A T thetaExponent Q tau
      stream node children t) :
    action ∈ rationalActualWideActions (physicalSourceInterval source.length node)
      (representatives node) P := by
  unfold physicalProgramGroups at hselected
  split_ifs at hselected with hbelow
  · obtain ⟨scale, _, hscale⟩ := List.mem_flatMap.mp hselected
    obtain ⟨cell, _, hselected⟩ := List.mem_filterMap.mp hscale
    exact chooseCellGroupAction_wide_mem source target (physicalSourceInterval source.length node)
      N ((dyadicScales N).get scale) P F thetaExponent Q tau (refinementFactor A F)
      (fun q => stageInitial source target U N P F A (node, q))
      (physicalBandChildMassTable source target U N P F A T node hbelow)
      (physicalBandChildInitial source target U N P F A node hbelow)
      (fun i q => children i t q) _ _ (List.get_mem _ _) action hselected
  · exact False.elim (List.not_mem_nil hselected)


end Program

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RoundedGroupStates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Enumerating rounded endpoints with a length-gap guard costs only
one wide coordinate and one envelope coordinate. -/

namespace EditApproximation



theorem gridGapStates_complete {n g anchor radius sourceLength gapRadius : ℕ}
    (hg : 0 < g) (r : TargetInterval n)
    (hfirst : Nat.dist anchor r.lo ≤ radius)
    (hgap : Nat.dist (r.lo + sourceLength) r.hi ≤ gapRadius)
    (hgrid : g ∣ r.lo ∧ g ∣ r.hi) :
    r ∈ gridGapStates n g anchor radius sourceLength gapRadius := by
  have hlo : anchor - radius ≤ r.lo ∧ r.lo ≤ anchor + radius := by unfold Nat.dist at hfirst; omega
  have hhi : r.lo + sourceLength - gapRadius ≤ r.hi ∧ r.hi ≤ r.lo + sourceLength + gapRadius := by
    unfold Nat.dist at hgap
    omega
  apply List.mem_flatMap.mpr
  refine ⟨r.lo, gridPointsBetween_complete hg hlo.1 hlo.2 hgrid.1, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨r.hi, gridPointsBetween_complete hg hhi.1 hhi.2 hgrid.2, ?_⟩
  rw [makeTargetState, dite_eq_left (show r.lo ≤ r.hi ∧ r.hi ≤ n from ⟨r.ordered, r.valid⟩)]

theorem wide_firstEndpoint_near_cell {n g b : ℕ} {theta : ℚ}
    (cell : ℕ × ℕ) (hg : 0 < g) (htheta : 0 ≤ theta ∧ theta ≤ 1) (hb : 1 ≤ b)
    (center r : TargetInterval n) (offset : ℕ)
    (hcenter : center ∈ cellTargetStates n g (theta * b) cell)
    (hwide : Nat.dist (center.lo + offset) r.lo ≤ 10 * b) :
    Nat.dist (⌊(cell.1 : ℚ) * (theta * b)⌋₊ + offset) r.lo ≤ 12 * b := by
  have hc := (cellTargetStates_mem cell hg center).mp hcenter
  have hbase : 0 ≤ (cell.1 : ℚ) * (theta * b) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg htheta.1 (Nat.cast_nonneg _))
  have hfloor := Nat.floor_le hbase
  have hfloorUpper := Nat.lt_floor_add_one ((cell.1 : ℚ) * (theta * b))
  have hthetaB := mul_le_mul_of_nonneg_right htheta.2 (Nat.cast_nonneg (α := ℚ) b)
  have hbR : (1 : ℚ) ≤ b := by exact_mod_cast hb
  have hlo : ⌊(cell.1 : ℚ) * (theta * b)⌋₊ ≤ center.lo := by
    exact_mod_cast hfloor.trans hc.2.2.1
  have hhi : center.lo ≤ ⌊(cell.1 : ℚ) * (theta * b)⌋₊ + 2 * b := by
    have hhiR : (center.lo : ℚ) ≤ (⌊(cell.1 : ℚ) * (theta * b)⌋₊ : ℚ) + 2 * b := by
      nlinarith only [hc.2.2.2.1, hfloorUpper, hthetaB, hbR]
    exact_mod_cast hhiR
  unfold Nat.dist at hwide ⊢
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ActualRoundedGroupInputs
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Every actual unskipped rounded group input belongs to a common
small endpoint list determined by the cell, child and envelope label. -/

namespace EditApproximation



theorem bandRoundSpacing_group_spacing {ny M : ℕ} (exponent b : ℕ)
    (band : List (Fin M → TargetInterval ny)) (initial : Fin M → TargetInterval ny → ℚ)
    (i : Fin M) (h : ℚ) (henvelope : bandChildEnvelope b band initial i = h) :
    bandRoundSpacing exponent b band initial i = groupRoundSpacing exponent h := by
  have heq := bandRoundSpacing_exact exponent b band initial i
  rw [henvelope] at heq
  have hceil := congrArg (fun r : ℚ => ⌈r⌉₊) heq
  simpa only [Nat.ceil_natCast, groupRoundSpacing] using hceil



theorem actual_rounded_group_input_mem {α : Type*} (source target : List α) {M b P exponent : ℕ}
    (parent : TargetInterval source.length) (tau a : ℚ) (F : ℕ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ) (cell : ℕ × ℕ)
    (member : UnskippedBand source target parent b P exponent tau F child initial)
    (hb : 1 ≤ b)
    (hcenter : member.center ∈ cellRepresentativeStates target.length P F b a parentInitial
      ((2 : ℚ) ^ (-(exponent : ℤ))) cell)
    (i : Fin M) (h : ℚ) (henvelope : member.envelope i = h) :
    member.rounded i ∈ groupRoundedStateList source target parent b exponent cell i h := by
  have hspacing := bandRoundSpacing_group_spacing exponent b member.actions initial i h henvelope
  have hgrid : groupRoundSpacing exponent h ∣ (member.rounded i).lo ∧
      groupRoundSpacing exponent h ∣ (member.rounded i).hi := by
    simpa only [UnskippedBand.rounded, canonicalRoundedBandAction, roundedBandAction, hspacing] using
      roundInterval_on_grid (bandRoundSpacing exponent b member.actions initial i)
        (member.actions.head member.nonempty i)
  have hwide : member.rounded i ∈ wideChildStateList parent member.center b P i :=
    finiteAssignments_sound M (wideChildStateList parent member.center b P) member.rounded member.wide_guard i
  have hwideFirst := (gridStateBox_sound (by unfold seedGridSpacing; omega) (member.rounded i) hwide).1
  have htheta : 0 ≤ (2 : ℚ) ^ (-(exponent : ℤ)) ∧ (2 : ℚ) ^ (-(exponent : ℤ)) ≤ 1 := by
    refine ⟨(zpow_pos (by norm_num : (0 : ℚ) < 2) _).le, ?_⟩
    rw [zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 2))
  have hfirst := wide_firstEndpoint_near_cell cell (by unfold seedGridSpacing; omega) htheta hb
    member.center (member.rounded i) ((sourceChild parent i).lo - parent.lo)
    (List.mem_filter.mp hcenter).1 hwideFirst
  have hgap := member.imbalance_guard i
  change |rationalStateGap _ _ (member.rounded i)| ≤ 2 * member.envelope i at hgap
  rw [henvelope] at hgap
  unfold rationalStateGap at hgap
  have hgapDistance := lengthGap_guard_distance (member.rounded i)
    (substring source (sourceChild parent i).lo (sourceChild parent i).hi).length h hgap
  unfold groupRoundedStateList
  apply gridGapStates_complete (groupRoundSpacing_pos exponent h) _ _ hgapDistance hgrid
  simpa only [mul_assoc] using hfirst

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SharedGroupInputBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A pathwise finite cover for every shared group estimator's current
child inputs. Repeated samples and member uses are counted once. -/

namespace EditApproximation

open Finset



theorem actual_group_input_in_cover {α : Type*} (source target : List α) {M b P exponent : ℕ}
    (parent : TargetInterval source.length) (tau a : ℚ) (F Q : ℕ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ) (cell : ℕ × ℕ)
    (member : UnskippedBand source target parent b P exponent tau F child initial)
    (hb : 1 ≤ b)
    (hcenter : member.center ∈ cellRepresentativeStates target.length P F b a parentInitial
      ((2 : ℚ) ^ (-(exponent : ℤ))) cell)
    (h : ℚ) (draw : Fin (groupSampleCount M Q b h) → Fin M)
    (i : Fin M) (hi : i ∈ groupQueriedChildLabels M Q b h draw) (henvelope : member.envelope i = h) :
    (i, member.rounded i) ∈ groupCurrentInputCover source target parent b exponent Q cell h draw := by
  apply Finset.mem_biUnion.mpr
  refine ⟨i, hi, Finset.mem_image.mpr ?_⟩
  exact ⟨member.rounded i, List.mem_toFinset.mpr
    (actual_rounded_group_input_mem source target parent tau a F parentInitial child initial cell
      member hb hcenter i h henvelope), rfl⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_GroupInputDependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Shared group estimates depend only on the explicitly bounded sampled
input cover. Thus scanning or repeatedly scoring all cell members can
reuse gathered values rather than issue new recursive requests. -/

namespace EditApproximation

open Finset

theorem dyadicUnskippedGroupEstimate_congr_cover {α : Type*}
    (source target : List α) {M b P exponent : ℕ}
    (parent : TargetInterval source.length) (tau a : ℚ) (F Q : ℕ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial value value' : Fin M → TargetInterval target.length → ℚ)
    (cell : ℕ × ℕ)
    (member : UnskippedBand source target parent b P exponent tau F child initial)
    (hb : 1 ≤ b)
    (hcenter : member.center ∈ cellRepresentativeStates target.length P F b a parentInitial
      ((2 : ℚ) ^ (-(exponent : ℤ))) cell)
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (hvalue : ∀ scale : Fin (groupDyadicScales M b F).length,
      ∀ input ∈ groupCurrentInputCover source target parent b exponent Q cell
        (groupDyadicScaleAt M b F scale) (draw scale), value input.1 input.2 = value' input.1 input.2) :
    dyadicUnskippedGroupEstimate Q value member draw =
      dyadicUnskippedGroupEstimate Q value' member draw := by
  unfold dyadicUnskippedGroupEstimate unskippedGroupEstimate groupMemberEstimate
  congr 1
  apply Finset.sum_congr rfl
  intro scale _
  apply groupScaleEstimate_congr_queried
  intro i hi henvelope
  exact hvalue scale (i, member.rounded i)
    (actual_group_input_in_cover source target parent tau a F Q parentInitial child initial cell
      member hb hcenter _ (draw scale) i hi henvelope)

theorem chooseCellGroupAction_congr_cover {α : Type*}
    (source target : List α) {M b P exponent : ℕ}
    (parent : TargetInterval source.length) (tau a : ℚ) (F Q : ℕ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial value value' : Fin M → TargetInterval target.length → ℚ)
    (cell : ℕ × ℕ) (hb : 1 ≤ b)
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (hvalue : ∀ scale : Fin (groupDyadicScales M b F).length,
      ∀ input ∈ groupCurrentInputCover source target parent b exponent Q cell
        (groupDyadicScaleAt M b F scale) (draw scale), value input.1 input.2 = value' input.1 input.2) :
    chooseCellGroupAction source target parent b P F exponent Q tau a parentInitial child initial value cell draw =
      chooseCellGroupAction source target parent b P F exponent Q tau a parentInitial child initial value' cell draw := by
  let members := cellUnskippedBands source target parent b P F exponent tau a parentInitial child initial cell
  change (if hm : members = [] then none else some (chooseUnskippedGroup Q value members hm draw).rationalAction) =
    (if hm : members = [] then none else some (chooseUnskippedGroup Q value' members hm draw).rationalAction)
  split_ifs with hempty
  · rfl
  · have hselected : chooseUnskippedGroup Q value members hempty draw =
        chooseUnskippedGroup Q value' members hempty draw := by
      unfold chooseUnskippedGroup
      apply selectGroupMember_congr_on
      intro member hm
      apply dyadicUnskippedGroupEstimate_congr_cover source target parent tau a F Q parentInitial
        child initial value value' cell member hb _ draw hvalue
      exact (unskippedBandList_mem_iff _ _).mp hm
    exact congrArg (fun member => some member.rationalAction) hselected

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinarySampledGroupPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed polynomial bounds the actual sampled-member bit counter. The
scale is supplied through its bit length, so a large distance scale does
not introduce a spurious linear dependence on that scale. -/

namespace EditApproximation

abbrev GP_p0 := FiniteBitPolynomial (Fin 6)
def gbits (x : GP_p0) : GP_p0 := .bitLength x
def gSumWord (n B : GP_p0) : GP_p0 :=
  (B + 1) + gbits n + 2 * (B + 2) + 2 * (1 + n * ((B + 1) + (B + 1))) + 1
def gSumWork (n B : GP_p0) : GP_p0 := 1 + n * (100000 * (gSumWord n B + 1) ^ 2)
def gSumStorage (n B : GP_p0) : GP_p0 := gbits n + B + 2 * (1 + n * (B + 1)) + 2
def gConnectionWord (M B : GP_p0) : GP_p0 := gSumStorage (M + 1) (8 * B + 6)
def gConnectionWork (M B : GP_p0) : GP_p0 :=
  (M + 1) * (6000 * (B + 1) ^ 2 + 4) + M * (2 * B + 6) +
    gSumWork (M + 1) (8 * B + 6) + 6 * (M + 1) + 1
def gEnvelopeWord (M bb B : GP_p0) : GP_p0 := B + bb + gbits M + 8
def gEnvelopeWork (M bb v B : GP_p0) : GP_p0 :=
  let W := gEnvelopeWord M bb B
  2100 * (bb + gbits M + 6) ^ 2 + (1 + v * (1000 * (W + 1) ^ 2 + 2)) +
    (1000 * (W + 1) ^ 2 + 1) +
    (1 + 2 * W * (1000 * (3 * W + 2) ^ 2 + 2) + 3 * W + 5) + v + 4
def gRoundWork (M e bb v B : GP_p0) : GP_p0 :=
  let W := e + 2 + 3 * gEnvelopeWord M bb B + B
  M * (gEnvelopeWork M bb v B + (2000 * (W + 1) ^ 2 + 1500 * (4 * W + 3) ^ 2 + 3) +
    500 * (4 * W + 4 + B + 1) ^ 2 + e + 11)
def gSampleCountWork (B : GP_p0) : GP_p0 :=
  2000 * (B + 1) ^ 2 + 2000 * (4 * B + 3) ^ 2 + 2100 * (16 * B + 12) ^ 2 +
    500 * (64 * B + 45) ^ 2 + 4 * (65 * B + 46) + 3 * B + 8
def gIndexWork (M B : GP_p0) : GP_p0 :=
  M * (2 * (1000 * (B + 1) ^ 2 + 1) + 6) + gSumWork M B + 6 * M + 1
def gScaleWord (M B : GP_p0) : GP_p0 := 4 * (4 * B + 4 + gSumStorage M B) + 2
def gScaleWork (M B : GP_p0) : GP_p0 :=
  gIndexWork M B + (2100 * (B + 2) ^ 2 + 1) +
    2000 * (4 * B + 4 + gSumStorage M B + 1) ^ 2 + 2 * B + 3
def gMemberWord (T B W : GP_p0) : GP_p0 := 8 * (B + gSumStorage T W) + 6
def gMemberWork (T B C W : GP_p0) : GP_p0 :=
  T * (C + 3) + gSumWork T W + 6 * T + 6000 * (B + gSumStorage T W + 1) ^ 2 + 1
def gCountedWork (M T B : GP_p0) : GP_p0 :=
  T * (gSampleCountWork B + 6) + gMemberWork T B (gScaleWork M B) (gScaleWord M B) + 1
def gInput (M bb B : GP_p0) : GP_p0 :=
  B + (3 * gEnvelopeWord M bb B + 1) + gConnectionWord M B + 1

def sampledGroupPolynomial : GP_p0 :=
  let M := .input 0
  let T := .input 1
  let e := .input 2
  let bb := .input 3
  let v := .input 4
  let B := .input 5
  gMemberWord T (gInput M bb B) (gScaleWord M (gInput M bb B)) +
    (M * (gEnvelopeWork M bb v B + 6) + gRoundWork M e bb v B + 7 * M +
      (gConnectionWork M B + 2 * B + M + 2) + gCountedWork M T (gInput M bb B) + 5)

def sampledGroupBitDegree : ℕ := sampledGroupPolynomial.degree

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_MemoizedOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Persistent dictionary requests. A fresh oracle is called only on a
cache miss; subsequent requests preserve and return the stored answer. -/

namespace EditApproximation

section Requests

variable {ι : Type*} (bits : ℕ) (encode : ι → ℕ) (oracle : ι → ℚ)

def memoSound (memory : BinaryMemo ℚ) : Prop :=
  ∀ key value, memory.lookup (binaryMemoKey bits (encode key)) = some value → value = oracle key

end Requests

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_DependencyExpansion
attribute [-instance] _root_.OAI.EditApproximation.physicalNodeFintype _root_.OAI.EditApproximation.physicalScalarIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite dependency expansions with two edge sorts. The certificate
checks progress and local branching at every actual node; the global
count follows from these local conditions. -/

namespace EditApproximation

open Finset

namespace DependencyExpansion

def nodeCount : DependencyExpansion → ℕ
  | .node _ _ _ _ same earlier => 1 + (∑ i, nodeCount (same i)) + ∑ i, nodeCount (earlier i)

/-- Every same edge strictly decreases physical depth and never increases
rank. Every earlier edge strictly decreases rank and never increases depth.
No global count is part of this certificate. -/
def Valid (a b : ℕ) : DependencyExpansion → Prop
  | .node d k m n same earlier =>
      m ≤ a ∧ n ≤ b ∧
      (∀ i, (same i).depth < d ∧ (same i).rank ≤ k ∧ Valid a b (same i)) ∧
      (∀ i, (earlier i).depth ≤ d ∧ (earlier i).rank < k ∧ Valid a b (earlier i))

/-- Literal count of nodes whose remaining physical depth is at least
`floor`. Descendants are inspected even when the current node fails the
test; pruning below the threshold is a consequence of `Valid`. -/
def nodeCountAtOrAbove (floor : ℕ) : DependencyExpansion → ℕ
  | .node d _ _ _ same earlier =>
      (if floor ≤ d then 1 else 0) +
        (∑ i, nodeCountAtOrAbove floor (same i)) +
        ∑ i, nodeCountAtOrAbove floor (earlier i)

/-- Literal count of nodes at one remaining physical depth. -/
def nodeCountAtDepth (target : ℕ) : DependencyExpansion → ℕ
  | .node d _ _ _ same earlier =>
      (if d = target then 1 else 0) +
        (∑ i, nodeCountAtDepth target (same i)) +
        ∑ i, nodeCountAtDepth target (earlier i)

/-- All nodes reached with physical descent at most `j`, including those
reached through earlier-index edges that themselves decrease depth. -/
def nodeCountThroughDescent (j : ℕ) (tree : DependencyExpansion) : ℕ :=
  nodeCountAtOrAbove (tree.depth - j) tree

/-- Nodes at physical descent exactly `j`. -/
def layerNodeCount (j : ℕ) (tree : DependencyExpansion) : ℕ :=
  if j ≤ tree.depth then nodeCountAtDepth (tree.depth - j) tree else 0

/-- Unfold actual finite successor arrays. Local progress makes the
construction terminate even when earlier edges also descend physically. -/
def build {ι : Type*} (d r m n : ι → ℕ)
    (s : (x : ι) → Fin (m x) → ι) (e : (x : ι) → Fin (n x) → ι)
    (hs : ∀ x i, d (s x i) < d x ∧ r (s x i) ≤ r x)
    (he : ∀ x i, d (e x i) ≤ d x ∧ r (e x i) < r x) (root : ι) : DependencyExpansion :=
  .node (d root) (r root) (m root) (n root)
    (fun i => build d r m n s e hs he (s root i))
    (fun i => build d r m n s e hs he (e root i))
termination_by d root + r root
decreasing_by
  · exact Nat.add_lt_add_of_lt_of_le (hs root i).1 (hs root i).2
  · exact Nat.add_lt_add_of_le_of_lt (he root i).1 (he root i).2

end DependencyExpansion
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalDependencyRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Concrete table requests and their dependency order. A single table
index identifies the end of warmup with refinement time zero. Copy labels
remain part of a request but do not reset its dependency rank. -/

namespace EditApproximation





namespace PhysicalTableRequest

variable {M J ny : ℕ}











theorem remainingDepth_le_of_no_ancestor (first second : PhysicalTableRequest M J ny)
    (hnode : first.node.1.val ≤ second.node.1.val) :
    second.remainingDepth ≤ first.remainingDepth :=
  Nat.sub_le_sub_left hnode J

theorem remainingDepth_lt_of_descendant (first second : PhysicalTableRequest M J ny)
    (hnode : first.node.1.val < second.node.1.val) :
    second.remainingDepth < first.remainingDepth := by
  have hsecond : second.node.1.val ≤ J := Nat.le_of_lt_succ second.node.1.isLt
  unfold remainingDepth
  omega



theorem rank_lt_same_pass (T S : ℕ) (first second : PhysicalTableRequest M J ny)
    (hpass : second.pass = first.pass) (hindex : second.index < first.index) :
    rank T S second < rank T S first := by
  unfold rank
  rw [hpass]
  exact Nat.add_lt_add_left hindex _

/-- A warmup predecessor lies at the physical child and at the preceding
unified table index. -/
theorem warmup_previous_child_progress (pass copy T S j : ℕ)
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (i : Fin M)
    (state previousState : TargetInterval ny) (hj : 0 < j) :
    (warmup pass copy (physicalChild node hbelow i) (j - 1) previousState).remainingDepth <
        (warmup pass copy node j state).remainingDepth ∧
      rank T S (warmup pass copy (physicalChild node hbelow i) (j - 1) previousState) <
        rank T S (warmup pass copy node j state) := by
  constructor
  · unfold remainingDepth warmup physicalChild
    dsimp only
    omega
  · dsimp only [rank, warmup]
    omega

theorem refinement_history_child_progress (pass copy T S t s : ℕ)
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (i : Fin M)
    (state previousState : TargetInterval ny) (hs : s < t) :
    (refinement pass copy (physicalChild node hbelow i) T s previousState).remainingDepth <
        (refinement pass copy node T t state).remainingDepth ∧
      rank T S (refinement pass copy (physicalChild node hbelow i) T s previousState) <
        rank T S (refinement pass copy node T t state) := by
  constructor
  · unfold remainingDepth refinement physicalChild
    dsimp only
    omega
  · dsimp only [rank, refinement]
    omega

/-- A previous pass can request any of its warmup/refinement indices.
The added one in the pass stride makes its last index strictly earlier
than the next pass's first index. -/
theorem rank_lt_previous_pass (T S : ℕ) (first second : PhysicalTableRequest M J ny)
    (hpass : second.pass < first.pass) (hindex : second.index ≤ T + S) :
    rank T S second < rank T S first := by
  have hblock : second.pass * (T + S + 1) + second.index <
      (second.pass + 1) * (T + S + 1) := by
    nlinarith only [hindex]
  have hnext := Nat.mul_le_mul_right (T + S + 1) (Nat.succ_le_of_lt hpass)
  exact hblock.trans_le (hnext.trans (Nat.le_add_right _ _))

theorem warmup_index_bound (pass copy : ℕ) (node : PhysicalNode M J)
    (T S j : ℕ) (state : TargetInterval ny) (hj : j ≤ T) :
    (warmup pass copy node j state).index ≤ T + S := by
  change j ≤ T + S
  omega

theorem refinement_index_bound (pass copy : ℕ) (node : PhysicalNode M J)
    (T S t : ℕ) (state : TargetInterval ny) (ht : t ≤ S) :
    (refinement pass copy node T t state).index ≤ T + S := by
  change T + t ≤ T + S
  omega

theorem warmup_bounded (passes copies pass copy : ℕ) (node : PhysicalNode M J)
    (T S j : ℕ) (state : TargetInterval ny)
    (hpass : pass < passes) (hcopy : copy < copies) (hj : j ≤ T) :
    Bounded passes copies T S (warmup pass copy node j state) :=
  ⟨hpass, hcopy, warmup_index_bound pass copy node T S j state hj⟩

theorem refinement_bounded (passes copies pass copy : ℕ) (node : PhysicalNode M J)
    (T S t : ℕ) (state : TargetInterval ny)
    (hpass : pass < passes) (hcopy : copy < copies) (ht : t ≤ S) :
    Bounded passes copies T S (refinement pass copy node T t state) :=
  ⟨hpass, hcopy, refinement_index_bound pass copy node T S t state ht⟩

end PhysicalTableRequest
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalWarmupQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Adaptive finite queries for the literal local initial cones and
warmup. Candidate lists are bounded local grid lists; no full target
domain is tabulated. -/

namespace EditApproximation



theorem finiteAnswerTable_map {κ : Type*} [DecidableEq κ] (keys : List κ) (value : κ → ℚ)
    (query : κ) (hquery : query ∈ keys) :
    finiteAnswerTable keys (keys.map value) query = value query := by
  induction keys with
  | nil => simp only [List.not_mem_nil] at hquery
  | cons key keys ih =>
    simp only [List.map_cons, finiteAnswerTable]
    by_cases heq : query = key
    · subst query
      rw [ite_eq_left rfl]
    · rw [ite_eq_right heq]
      exact ih (List.mem_of_ne_of_mem heq hquery)



theorem localInitialConeCenters_raw {n : ℕ} (N P : ℕ) (A : ℚ)
    (U : TargetInterval n → ℕ) (q r : TargetInterval n)
    (hr : r ∈ localInitialConeCenters N P A U q) :
    r ∈ rawInitialConeCenters N P A (U q) q := by
  obtain ⟨b, hb, hr⟩ := List.mem_flatMap.mp hr
  exact List.mem_flatMap.mpr ⟨b, hb, (List.mem_filter.mp hr).1⟩

theorem localInitialConeCenters_congr_raw {n : ℕ} (N P : ℕ) (A : ℚ)
    (U V : TargetInterval n → ℕ) (q : TargetInterval n) (hq : U q = V q)
    (heq : ∀ r ∈ rawInitialConeCenters N P A (U q) q, U r = V r) :
    localInitialConeCenters N P A U q = localInitialConeCenters N P A V q := by
  unfold localInitialConeCenters
  rw [← hq]
  apply List.flatMap_congr
  intro b hb
  apply List.filter_congr
  intro r hr
  rw [heq r (List.mem_flatMap.mpr ⟨b, hb, hr⟩)]

theorem localInitialConeTable_congr_raw {α : Type*} (source target : List α)
    (N P F : ℕ) (A a : ℚ) (U V : TargetInterval target.length → ℕ)
    (q : TargetInterval target.length) (hq : U q = V q)
    (heq : ∀ r ∈ rawInitialConeCenters N P A (U q) q, U r = V r) :
    localInitialConeTable source target U N P F A a q =
      localInitialConeTable source target V N P F A a q := by
  have hcenters := localInitialConeCenters_congr_raw N P A U V q hq heq
  unfold localInitialConeTable
  rw [← hq, ← hcenters]
  split_ifs
  · rfl
  · congr 1
    apply List.map_congr_left
    intro r hr
    unfold initialConeValue
    rw [heq r (localInitialConeCenters_raw N P A U q r hr)]



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitMemoHeap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A cumulative allocation counter for the actual memo execution. It keeps
all local allocations until the entire run finishes, so it also bounds peak
space. A read retains three continuation/result cells. Each memo call reserves
its address workspace, key bits, traversal frames and the possible new trie
path; existing values and input words are shared by reference. -/

namespace EditApproximation

/-- Sixteen scalar/frame slots suffice in addition to eight slots per key
bit and the supplied address-construction workspace; the larger fixed reserve
also covers the result record and the empty-trie case. -/


def rankedBitMemoCells {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → BitQuery {child : κ // rank child < rank key} BinaryFraction)
    (heap : ∀ key, BitQuery.Heap (program key))
    (bits : ℕ) (encode addressCells : κ → ℕ) (key : κ) (memory : BinaryMemo BinaryFraction) : ℕ :=
  let found := memory.lookupCosted (binaryMemoKey bits (encode key))
  match found.1 with
  | some _ => memoRequestCells bits (addressCells key)
  | none => memoRequestCells bits (addressCells key) + (heap key).runCells
      (fun child previous => rankedBitMemoEvaluate rank program bits encode child.val previous)
      (fun child previous => rankedBitMemoCells rank program heap bits encode addressCells child.val previous)
      memory
termination_by rank key
decreasing_by exact child.property

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitMemoSound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Memo hits return the same concrete binary word as the deterministic
rank-decreasing program. This stronger invariant also fixes the local
arithmetic work on repeated reads, independently of cache history. -/

namespace EditApproximation

def bitMemoSound {κ : Type*} (bits : ℕ) (encode : κ → ℕ)
    (expected : κ → BinaryFraction) (memory : BinaryMemo BinaryFraction) : Prop :=
  ∀ key value, memory.lookup (binaryMemoKey bits (encode key)) = some value → value = expected key


end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_GatheredLocalStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The current-index part of a local step can be evaluated in two
stages: gather the shared sampled inputs, select the whole-cell actions,
then gather their actual costs and the online action costs. -/

namespace EditApproximation

open Finset

theorem localCellGroupActions_congr_cover {α : Type*}
    (source target : List α) {M : ℕ} (parent : TargetInterval source.length)
    (N P F exponent Q : ℕ) (tau a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial current current' : Fin M → TargetInterval target.length → ℚ)
    (draw : CellGroupDraws M F Q) (q : TargetInterval target.length)
    (hvalue : ∀ input ∈ querySharedInputCover source target parent N F exponent Q a parentInitial q draw,
      current input.1 input.2 = current' input.1 input.2) :
    localCellGroupActions source target parent N P F exponent Q tau a parentInitial
        child initial current draw q =
      localCellGroupActions source target parent N P F exponent Q tau a parentInitial
        child initial current' draw q := by
  unfold localCellGroupActions
  apply List.flatMap_congr
  intro b hb
  apply List.filterMap_congr
  intro cell hc
  have hscale : b ∈ dyadicScales N := (List.mem_filter.mp hb).1
  have hbpos : 1 ≤ b := by
    obtain ⟨e, _, he⟩ := List.mem_map.mp hscale
    rw [← he]
    exact Nat.one_le_two_pow
  apply chooseCellGroupAction_congr_cover source target parent tau a F Q parentInitial
    child initial current current' cell hbpos (draw b cell)
  intro scale input hi
  apply hvalue input
  apply Finset.mem_biUnion.mpr
  refine ⟨(b, cell), ?_, Finset.mem_biUnion.mpr ⟨scale, Finset.mem_univ _, hi⟩⟩
  apply List.mem_toFinset.mpr
  exact List.mem_flatMap.mpr ⟨b, hb, List.mem_map.mpr ⟨cell, hc, rfl⟩⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRequestEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Fixed-width keys for the bounded physical cache. Their construction
uses only the request's coordinates, without enumerating table entries. -/

namespace EditApproximation
namespace PhysicalTableRequest





def bits (M J n passes copies T S : ℕ) : ℕ :=
  Nat.clog 2 (capacity M J n passes copies T S + 1)

end PhysicalTableRequest
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RoundedComparison
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual rounded comparison actions

An optimal balanced alignment at the rounded representative is rounded
on the same integer grid. This produces a shared-endpoint wide action
and the manuscript's multiplicative cost growth, with all empty children
retained as labeled coordinates.
-/

namespace EditApproximation

open Finset EditDistortion

theorem rounded_comparison_action {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (parent : TargetInterval source.length)
    (q : TargetInterval target.length) (b P : ℕ) (hP : 66 ≤ P)
    (hb : b ≤ stateEditCost (substring source parent.lo parent.hi) target q)
    (hcost : stateEditCost (substring source parent.lo parent.hi) target q < 2 * b) :
    let r := roundInterval (seedGridSpacing b P) q
    ∃ states : Fin M → TargetInterval target.length,
      states ∈ wideActionList M parent r b P ∧ endpointActionConnection r states = 0 ∧
      (∀ i j : Fin M, j.val = i.val + 1 → (states i).hi = (states j).lo) ∧
      (∀ i : Fin M,
        Nat.dist (r.lo + ((sourceChild parent i).lo - parent.lo)) (states i).lo ≤ 6 * b ∧
        Nat.dist (r.lo + ((sourceChild parent i).hi - parent.lo)) (states i).hi ≤ 6 * b) ∧
      (∑ i, (stateEditCost
        (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (states i) : ℝ)) ≤
          (1 + 4 * (M : ℝ) / P) * stateEditCost (substring source parent.lo parent.hi) target q := by
  dsimp only
  let g := seedGridSpacing b P
  let r := roundInterval g q
  let piece := fun i : Fin M =>
    substring source (sourceChild parent i).lo (sourceChild parent i).hi
  let c : ℝ := stateEditCost (substring source parent.lo parent.hi) target q
  let cr : ℝ := stateEditCost (substring source parent.lo parent.hi) target r
  have hPr : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have hProne : (1 : ℝ) ≤ P := by exact_mod_cast (by omega : 1 ≤ P)
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hbc : (b : ℝ) ≤ c := by dsimp only [c]; exact_mod_cast hb
  have hcb : c < 2 * b := by dsimp only [c]; exact_mod_cast hcost
  have hqgrid : (targetEndpointDistance q r : ℝ) * P ≤ 2 * b := by
    exact_mod_cast rounded_seedGrid_error b P (by omega) q
  have hcr : cr ≤ c + targetEndpointDistance q r := by
    have h := stateEditCost_distance_abs (substring source parent.lo parent.hi) target q r
    have hR : |c - cr| ≤ (targetEndpointDistance q r : ℝ) := by
      dsimp only [c, cr]
      exact_mod_cast h
    linarith [(abs_le.mp hR).1]
  have hcrP : cr * P ≤ c * P + 2 * b := by
    have hmul := mul_le_mul_of_nonneg_right hcr hPr.le
    nlinarith
  have hqerror : (targetEndpointDistance q r : ℝ) ≤ 2 * b := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (targetEndpointDistance q r))
      (sub_nonneg.mpr hProne)]
  obtain ⟨aligned, hsplit, hstart, hend, hshared, hanchors⟩ :=
    optimal_balanced_child_states source target hM parent r
  let states := fun i => roundInterval g (aligned i)
  have herror (i : Fin M) : (targetEndpointDistance (aligned i) (states i) : ℝ) * P ≤ 2 * b := by
    exact_mod_cast rounded_seedGrid_error b P (by omega) (aligned i)
  have hanchorBound (i : Fin M) (anchor endpoint rounded : ℕ)
      (hanchor : Nat.dist anchor endpoint ≤ stateEditCost (substring source parent.lo parent.hi) target r)
      (hround : Nat.dist endpoint rounded ≤ targetEndpointDistance (aligned i) (states i)) :
      Nat.dist anchor rounded ≤ 6 * b := by
    have htriangle := Nat.dist.triangle_inequality anchor endpoint rounded
    have hbound : (Nat.dist anchor rounded : ℝ) ≤ cr +
        targetEndpointDistance (aligned i) (states i) := by
      dsimp only [cr]
      exact_mod_cast (by omega : Nat.dist anchor rounded ≤
        stateEditCost (substring source parent.lo parent.hi) target r +
          targetEndpointDistance (aligned i) (states i))
    have he := herror i
    have herr : (targetEndpointDistance (aligned i) (states i) : ℝ) ≤ 2 * b := by
      nlinarith [mul_nonneg (Nat.cast_nonneg (targetEndpointDistance (aligned i) (states i)))
        (sub_nonneg.mpr hProne)]
    have hfinal : (Nat.dist anchor rounded : ℝ) ≤ 6 * b := by linarith
    exact_mod_cast hfinal
  have hanchorsRounded (i : Fin M) :
      Nat.dist (r.lo + ((sourceChild parent i).lo - parent.lo)) (states i).lo ≤ 6 * b ∧
      Nat.dist (r.lo + ((sourceChild parent i).hi - parent.lo)) (states i).hi ≤ 6 * b := by
    constructor
    · exact hanchorBound i _ _ _ (hanchors i).1 (Nat.le_add_right _ _)
    · exact hanchorBound i _ _ _ (hanchors i).2 (Nat.le_add_left _ _)
  have hcostPoint (i : Fin M) :
      (stateEditCost (piece i) target (states i) : ℝ) * P ≤
        (stateEditCost (piece i) target (aligned i) : ℝ) * P + 2 * b := by
    have h := stateEditCost_distance_abs (piece i) target (aligned i) (states i)
    have hR : |(stateEditCost (piece i) target (aligned i) : ℝ) -
        stateEditCost (piece i) target (states i)| ≤ targetEndpointDistance (aligned i) (states i) := by
      exact_mod_cast h
    have hstep : (stateEditCost (piece i) target (states i) : ℝ) ≤
        stateEditCost (piece i) target (aligned i) + targetEndpointDistance (aligned i) (states i) := by
      linarith [(abs_le.mp hR).1]
    have hmul := mul_le_mul_of_nonneg_right hstep hPr.le
    nlinarith [herror i]
  have hsum := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin M))) => hcostPoint i)
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← sum_mul] at hsum
  have hsplitR : (∑ i, (stateEditCost (piece i) target (aligned i) : ℝ)) = cr := by
    dsimp only [piece, cr]
    exact_mod_cast hsplit
  rw [hsplitR] at hsum
  have hsumFinal : (∑ i, (stateEditCost (piece i) target (states i) : ℝ)) ≤
      (1 + 4 * (M : ℝ) / P) * c := by
    have hMb := mul_le_mul_of_nonneg_left hbc (Nat.cast_nonneg M)
    have hbM : (b : ℝ) ≤ M * (b : ℝ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hMr) (Nat.cast_nonneg b)]
    have hscaled : (∑ i, (stateEditCost (piece i) target (states i) : ℝ)) * P ≤
        (P + 4 * (M : ℝ)) * c := by nlinarith
    have hformula : ((P : ℝ) + 4 * M) * c / P = (1 + 4 * (M : ℝ) / P) * c := by
      field_simp
    rw [← hformula]
    exact (le_div_iff₀ hPr).2 hscaled
  refine ⟨states, ?_, ?_, ?_, hanchorsRounded, hsumFinal⟩
  · apply wideActionList_complete parent r states (fun i => roundInterval_on_grid g (aligned i))
    · intro i; exact (hanchorsRounded i).1.trans (by omega)
    · intro i; exact (hanchorsRounded i).2.trans (by omega)
  · exact round_shared_action hM r aligned hstart hend hshared (roundInterval_on_grid g q)
  · intro i j hij
    exact roundInterval_shared (aligned i) (aligned j) (hshared i j hij)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ComparisonTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The input-determined rounded comparison tree

The choices here are only for the proof. They use the exact input edit
costs and a fixed classical choice of optimal alignment, and have no
sampling argument. Stopped states are carried in child zero, with the
remaining physical slots empty.
-/

namespace EditApproximation

open Finset

noncomputable def comparisonStateCost {α : Type*} (source target : List α) :
    ComparisonState source.length target.length → ℝ
  | none => 0
  | some (parent, q) => stateEditCost (substring source parent.lo parent.hi) target q

noncomputable def comparisonChildren {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (hc : 0 < stateEditCost (substring source parent.lo parent.hi) target q) :
    Fin M → TargetInterval target.length :=
  Classical.choose (rounded_comparison_action source target hM parent q
    (2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)) P hP
    (cost_dyadicScale _ _ hc le_rfl).2.1 (cost_dyadicScale _ _ hc le_rfl).2.2)

theorem comparisonChildren_spec {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (parent : TargetInterval source.length) (q : TargetInterval target.length)
    (hc : 0 < stateEditCost (substring source parent.lo parent.hi) target q) :
    let b := 2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)
    let r := roundInterval (seedGridSpacing b P) q
    let states := comparisonChildren source target hM P hP parent q hc
    states ∈ wideActionList M parent r b P ∧ endpointActionConnection r states = 0 ∧
      (∀ i j : Fin M, j.val = i.val + 1 → (states i).hi = (states j).lo) ∧
      (∀ i : Fin M,
        Nat.dist (r.lo + ((sourceChild parent i).lo - parent.lo)) (states i).lo ≤ 6 * b ∧
        Nat.dist (r.lo + ((sourceChild parent i).hi - parent.lo)) (states i).hi ≤ 6 * b) ∧
      (∑ i, (stateEditCost
        (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (states i) : ℝ)) ≤
          (1 + 4 * (M : ℝ) / P) * stateEditCost (substring source parent.lo parent.hi) target q :=
  Classical.choose_spec (rounded_comparison_action source target hM parent q
    (2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)) P hP
    (cost_dyadicScale _ _ hc le_rfl).2.1 (cost_dyadicScale _ _ hc le_rfl).2.2)

noncomputable def comparisonStep {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P) :
    ComparisonState source.length target.length → Fin M → ComparisonState source.length target.length
    := by
  classical
  exact fun node i => match node with
    | none => none
    | some (parent, q) =>
      if hstop : comparisonStopped source target parent q then
        if i = ⟨0, hM⟩ then some (parent, q) else none
      else
        some (sourceChild parent i,
          comparisonChildren source target hM P hP parent q
            (by unfold comparisonStopped at hstop; omega) i)

noncomputable def comparisonFrontier {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (root : ComparisonState source.length target.length) :
    (d : ℕ) → TreeLayer M d → ComparisonState source.length target.length
  | 0, _ => root
  | d + 1, node => comparisonStep source target hM P hP
      (comparisonFrontier source target hM P hP root d node.1) node.2

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalParentDraw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Parent random streams in a fixed child environment

Finite parent arrays contain independent uniform optimizer integers and
actual shared-group draws. The projection laws are exact. Their use in the
node bound needs only the individual marginals, so no independence between
an online payoff and a group-failure indicator is asserted there.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

noncomputable def parentDrawLaw (R O M K : ℕ) [NeZero M] [NeZero O]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] (count : Fin K → ℕ) :
    Measure (ParentRandomSpace R O M K count) :=
  (Measure.pi fun _ : Fin R => (PMF.uniformOfFintype (Fin O)).toMeasure).prod
    (Measure.pi fun _ : Fin R => groupSharedDrawLaw (M := M) count)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalConditionalNode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Conditional expected regret in a fixed child environment

Finite Bernstein bounds control the parent product draws. Agreement of
deeper selection functions fixes all child histories by locality, and
list membership connects the sampled actions to the refinement recurrence.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

noncomputable def bandParentLaw (R M b F Q K : ℕ) [NeZero M] [NeZero (optimizerTriangularMass K)]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] : Measure (BandParentSpace R M b F Q K) :=
  parentDrawLaw R (optimizerTriangularMass K) M (groupDyadicScales M b F).length
    (fun scale => groupSampleCount M Q b (groupDyadicScaleAt M b F scale))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalProgramLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The global finite product of actual selection streams

Online slots and whole-cell slots form a finite disjoint union. Each slot
contains its complete finite time array with the prescribed product law.
Mapping the flattened product produces
the actual online/group stream pair without independence hypotheses.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

section GlobalLaw

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T thetaExponent H Q : ℕ) (tau : ℚ)
  [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]

abbrev PhysicalOnlineKey := Σ node : PhysicalInternalNode M J,
  Fin (stageRepresentatives source target U N P F A node.1).length

abbrev PhysicalGroupKey := Σ node : PhysicalInternalNode M J,
  Σ scale : Fin (dyadicScales N).length,
    Fin (physicalProgramCells source target U N P F A thetaExponent node.1
      ((dyadicScales N).get scale)).length

abbrev PhysicalProgramKey := Sum (PhysicalOnlineKey source target U N P F A)
  (PhysicalGroupKey source target U N P F A thetaExponent)

abbrev PhysicalOnlineArray (key : PhysicalOnlineKey source target U N P F A) :=
  Fin R → Fin (optimizerTriangularMass
    (physicalProgramBandK source target U N P F A T thetaExponent H tau key.1 key.2))

abbrev PhysicalGroupArray (key : PhysicalGroupKey source target U N P F A thetaExponent) :=
  Fin R → ParentGroupDraw M (groupDyadicScales M ((dyadicScales N).get key.2.1) F).length
    (fun h => groupSampleCount M Q ((dyadicScales N).get key.2.1)
      (groupDyadicScaleAt M ((dyadicScales N).get key.2.1) F h))

abbrev PhysicalProgramCoordinate (key : PhysicalProgramKey source target U N P F A thetaExponent) : Type :=
  match key with
  | .inl online => PhysicalOnlineArray (R := R) source target U N P F A T thetaExponent H tau online
  | .inr group => PhysicalGroupArray (R := R) source target U N P F A thetaExponent Q group

instance physicalProgramCoordinateMeasurableSpace
    (key : PhysicalProgramKey source target U N P F A thetaExponent) :
    MeasurableSpace (PhysicalProgramCoordinate (R := R) source target U N P F A T thetaExponent H Q tau key) := by
  cases key <;> dsimp only [PhysicalProgramCoordinate] <;> infer_instance

abbrev PhysicalProgramDraw := ∀ key : PhysicalProgramKey source target U N P F A thetaExponent,
  PhysicalProgramCoordinate (R := R) source target U N P F A T thetaExponent H Q tau key


noncomputable def physicalProgramCoordinateLaw
    (key : PhysicalProgramKey source target U N P F A thetaExponent) :
    Measure (PhysicalProgramCoordinate (R := R) source target U N P F A T thetaExponent H Q tau key) :=
  match key with
  | .inl online =>
    let : NeZero (optimizerTriangularMass
      (physicalProgramBandK source target U N P F A T thetaExponent H tau online.1 online.2)) :=
      ⟨Nat.ne_of_gt (optimizerTriangularMass_positive _
        (physicalProgramBandK_positive source target U N P F A T thetaExponent H tau online.1 online.2))⟩
    Measure.pi fun _ : Fin R => (PMF.uniformOfFintype (Fin (optimizerTriangularMass
      (physicalProgramBandK source target U N P F A T thetaExponent H tau online.1 online.2)))).toMeasure
  | .inr group => Measure.pi fun _ : Fin R => groupSharedDrawLaw (M := M)
      (fun h => groupSampleCount M Q ((dyadicScales N).get group.2.1)
        (groupDyadicScaleAt M ((dyadicScales N).get group.2.1) F h))

instance physicalProgramCoordinateLaw_probability
    (key : PhysicalProgramKey source target U N P F A thetaExponent) :
    IsProbabilityMeasure
      (physicalProgramCoordinateLaw (R := R) source target U N P F A T thetaExponent H Q tau key) := by
  cases key <;> dsimp only [physicalProgramCoordinateLaw, physicalProgramCoordinateMeasurableSpace,
    PhysicalProgramCoordinate] <;> infer_instance

noncomputable def physicalProgramDrawLaw :
    Measure (PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau) :=
  Measure.pi (physicalProgramCoordinateLaw (R := R) source target U N P F A T thetaExponent H Q tau)

instance physicalProgramDrawLaw_probability :
    IsProbabilityMeasure (physicalProgramDrawLaw (R := R) source target U N P F A T thetaExponent H Q tau) := by
  unfold physicalProgramDrawLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def physicalProgramDrawStreams
    (draw : PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau) :
    PhysicalOnlineStreams source target U N P F A T thetaExponent H tau R ×
      PhysicalGroupStreams source target U N P F A thetaExponent Q R :=
  (fun node representative => draw (.inl ⟨node, representative⟩),
    fun node scale cell => draw (.inr ⟨node, scale, cell⟩))


end GlobalLaw

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ComparisonBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual terminal, nonterminal-cost and endpoint-movement bounds. -/

namespace EditApproximation

open Finset

noncomputable def comparisonActiveCost {α : Type*} (source target : List α) :
    ComparisonState source.length target.length → ℝ := by
  classical
  exact fun node => match node with
    | none => 0
    | some (parent, q) => if comparisonStopped source target parent q then 0
      else stateEditCost (substring source parent.lo parent.hi) target q

noncomputable def comparisonMovement {α : Type*} (source target : List α) (P : ℕ) :
    ComparisonState source.length target.length → ℝ := by
  classical
  exact fun node => match node with
    | none => 0
    | some (parent, q) => if comparisonStopped source target parent q then 0 else
      targetEndpointDistance q (roundInterval (seedGridSpacing
        (2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q)) P) q)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ComparisonLift
attribute [-instance] _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual physical tables on the stopped comparison tree. Stopped states retain
their exact cost while the complete-tree representation carries them forward.
-/

namespace EditApproximation

open Finset

noncomputable def stoppedComparisonValue {α : Type*} (source target : List α)
    (row : TargetInterval target.length → ℝ) : ComparisonState source.length target.length → ℝ := by
  classical
  exact fun state => match state with
    | none => 0
    | some (parent, q) => if comparisonStopped source target parent q then
        stateEditCost (substring source parent.lo parent.hi) target q else row q

noncomputable def comparisonPhysicalLift {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P)
    (table : PhysicalEntry M J target.length → ℝ) (rootQ : TargetInterval target.length)
    (d : ℕ) (path : TreeLayer M d) : ℝ := by
  classical
  exact stoppedComparisonValue source target
    (if hd : d ≤ J then fun q => table (⟨⟨d, by omega⟩, path⟩, q) else fun _ => 0)
    (comparisonFrontier source target hM P hP
      (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ)) d path)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ComparisonLiftBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual stopped-tree warmup masses and their energy telescope bounds. -/

namespace EditApproximation

open Finset

noncomputable def comparisonStateGap {α : Type*} (source target : List α) :
    ComparisonState source.length target.length → ℝ
  | none => 0
  | some (parent, q) => stateLengthGap (substring source parent.lo parent.hi) target q

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_StageComparisonBad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exceptional comparison-node costs are bounded by the actual global curvature charge. -/

namespace EditApproximation

open Finset

noncomputable def comparisonActiveScale {α : Type*} (source target : List α) :
    ComparisonState source.length target.length → ℝ := by
  classical
  exact fun state => match state with
    | none => 0
    | some (parent, q) => if comparisonStopped source target parent q then 0 else
        (2 ^ Nat.log 2 (stateEditCost (substring source parent.lo parent.hi) target q) : ℕ)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSubtree
attribute [-instance] _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparison paths below an arbitrary physical node retain their original
global table labels. No refinement program or random law is changed. -/

namespace EditApproximation

noncomputable def comparisonSubtreeLift {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (hP : 66 ≤ P) (table : PhysicalEntry M J target.length → ℝ)
    (root : PhysicalNode M J) (rootQ : TargetInterval target.length)
    (d : ℕ) (path : TreeLayer M d) : ℝ := by
  classical
  exact stoppedComparisonValue source target
    (if hd : root.1.val + d ≤ J then fun q => table (physicalSubtreeNode root d path hd, q) else fun _ => 0)
    (comparisonFrontier source target hM P hP (some (physicalSourceInterval source.length root, rootQ)) d path)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSeedMedian
attribute [-instance] _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The seed update uses the actual integer ceilings, upper median and clamp.
Copies share an entire table within each run and are independent between runs. -/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

noncomputable def physicalScaledCopy {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ) (a S : ℕ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (state : PhysicalEntry M J target.length) : ℕ :=
  ⌈(a : ℚ) * physicalRefinement source target U N P F A T delta choices state.1 S state.2⌉₊

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSeedPass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A full-table median seed pass from independent refinement copies under finite Bernstein bounds. -/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

noncomputable def physicalMedianUpdate {α Ω : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ) (a S copies : ℕ)
    (choices : Ω → PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (draws : Fin copies → Ω)
    (state : PhysicalEntry M J target.length) : ℕ :=
  finiteMedianSeed N copies
    (fun draw => physicalScaledCopy source target U N P F A T delta a S (choices draw) state) draws

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalMedianQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A seed entry is computed by querying the previous pass at the same
physical node in each copy, then applying the literal clamped median.
The copy coordinate never changes the dependency rank. -/

namespace EditApproximation



theorem previousPassRequest_progress {M J ny : ℕ} (T S copy : ℕ)
    (parent : PhysicalTableRequest M J ny) (hpass : 0 < parent.pass) (state : TargetInterval ny) :
    (previousPassRequest T S copy parent state).remainingDepth = parent.remainingDepth ∧
      (previousPassRequest T S copy parent state).rank T S < parent.rank T S := by
  refine ⟨rfl, ?_⟩
  exact PhysicalTableRequest.rank_lt_previous_pass T S parent _ (by
    change parent.pass - 1 < parent.pass
    omega) le_rfl





theorem physicalMedianSeedQuery_value {M J ny : ℕ} (N T S copies multiplier : ℕ)
    (parent : PhysicalTableRequest M J ny) (hpass : 0 < parent.pass) (state : TargetInterval ny)
    (values : PhysicalTableRequest M J ny → ℚ) :
    (physicalMedianSeedQuery N T S copies multiplier parent hpass state).value
      (fun child => values child.val) =
    (min N (upperMedian (List.ofFn fun copy : Fin copies =>
      ⌈(multiplier : ℚ) * values (previousPassRequest T S copy.val parent state)⌉₊)) : ℕ) := by
  unfold physicalMedianSeedQuery
  rw [FiniteQuery.collect_value]
  simp only [previousPassRead, FiniteQuery.value, List.map_map, List.ofFn_eq_map, Function.comp_def]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedSeedQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A pass-zero seed read requests a cached coarse entry. Later seed reads
request the previous pass's final table value in each distinct copy.
Thus neither kind of seed value enters the charged program as a free oracle. -/

namespace EditApproximation







theorem chargedSeedQuery_value {M J ny passes copies T S : ℕ} (N : ℕ) (multiplier : ℕ → ℕ)
    (parent : {r : PhysicalTableRequest M J ny // r.Bounded passes copies T S})
    (q : TargetInterval ny) (answer : ChargedPhysicalRequest M J ny passes copies T S → ℚ) :
    (chargedSeedQuery N multiplier parent (parent.val.node, q)).value (fun child => answer child.val) =
    if parent.val.pass = 0 then answer (Sum.inl (parent.val.node, q)) else
      (min N (upperMedian (List.ofFn fun copy : Fin copies =>
        ⌈(multiplier (parent.val.pass - 1) : ℚ) *
          answer (Sum.inr (chargedPreviousPass parent q copy))⌉₊)) : ℕ) := by
  unfold chargedSeedQuery
  rw [dite_eq_left rfl]
  split_ifs with hp
  · rfl
  · rw [FiniteQuery.collect_value]
    simp only [chargedPreviousRead, FiniteQuery.value, List.map_map,
      List.ofFn_eq_map, Function.comp_def]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteQueryRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Restriction of adaptive read programs to a proved finite request domain.
The restriction visits the same reads whenever the original execution stays
in that domain. It does not enumerate the domain. -/

namespace EditApproximation.FiniteQuery



 theorem restrict_value {ι : Type*} (P : ι → Prop) [DecidablePred P]
    (oracle : ι → ℚ) (program : FiniteQuery ι)
    (hvalid : ∀ key ∈ program.keys oracle, P key) :
    (restrict P program).value (fun key => oracle key.val) = program.value oracle := by
  induction program with
  | done result => rfl
  | read key next ih =>
    have hk : P key := hvalid key (by simp only [keys, List.mem_cons, true_or])
    have hnext : ∀ other ∈ (next (oracle key)).keys oracle, P other := by
      intro other hother
      exact hvalid other (List.mem_cons_of_mem key hother)
    simpa only [restrict, dite_eq_left hk, value] using ih (oracle key) hnext

 theorem restrict_keys {ι : Type*} (P : ι → Prop) [DecidablePred P]
    (oracle : ι → ℚ) (program : FiniteQuery ι)
    (hvalid : ∀ key ∈ program.keys oracle, P key) :
    ((restrict P program).keys (fun key => oracle key.val)).map Subtype.val = program.keys oracle := by
  induction program with
  | done result => rfl
  | read key next ih =>
    have hk : P key := hvalid key (by simp only [keys, List.mem_cons, true_or])
    have hnext : ∀ other ∈ (next (oracle key)).keys oracle, P other := by
      intro other hother
      exact hvalid other (List.mem_cons_of_mem key hother)
    simpa only [restrict, dite_eq_left hk, keys, List.map_cons] using
      congrArg (List.cons key) (ih (oracle key) hnext)

end EditApproximation.FiniteQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalWarmupStepQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A local warmup step gathers its candidate initial values and each
distinct wide child coordinate before evaluating the finite Bellman
minimum. Wide action enumeration makes no recursive oracle calls. -/

namespace EditApproximation



theorem localRefinementRepresentatives_congr_raw {n : ℕ} (N P F : ℕ) (a : ℚ)
    (left right : TargetInterval n → ℚ) (q : TargetInterval n) (hq : left q = right q)
    (heq : ∀ r ∈ rawRefinementCenters N P F a (left q) q, left r = right r) :
    localRefinementRepresentatives N P F a left q =
      localRefinementRepresentatives N P F a right q := by
  unfold localRefinementRepresentatives
  rw [← hq]
  apply List.flatMap_congr
  intro b hb
  congr 1
  apply List.filter_congr
  intro r hr
  rw [heq r (List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨b, hb, hr⟩))]



theorem wideWarmupInputs_action {nx ny M : ℕ} (parent : TargetInterval nx) (P : ℕ)
    (representatives : List (ℕ × TargetInterval ny))
    (action : RationalBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M)
    (ha : action ∈ rationalActualWideActions parent representatives P) (i : Fin M) :
    action.childState i ∈ wideWarmupInputs parent P representatives := by
  obtain ⟨br, hbr, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨states, hs, rfl⟩ := List.mem_map.mp ha
  apply List.mem_eraseDups.mpr
  apply List.mem_flatMap.mpr
  refine ⟨br, hbr, List.mem_flatMap.mpr ?_⟩
  exact ⟨i, List.mem_finRange i, List.mem_map.mpr
    ⟨states i, finiteAssignments_sound M _ states hs i, rfl⟩⟩



theorem localWarmupStepQuery_value {ι : Type*} {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F : ℕ) (a : ℚ) (initialRead : TargetInterval ny → FiniteQuery ι)
    (childRead : Fin M × TargetInterval ny → FiniteQuery ι) (oracle : ι → ℚ)
    (initial : TargetInterval ny → ℚ) (child : Fin M × TargetInterval ny → ℚ)
    (hinitial : ∀ r, (initialRead r).value oracle = initial r)
    (hchild : ∀ input, (childRead input).value oracle = child input) (q : TargetInterval ny) :
    (localWarmupStepQuery parent N P F a initialRead childRead q).value oracle =
      rationalBellman initial (fun q r => targetEndpointDistance q r) (128 * F)
        (rationalActualWideActions parent (localRefinementRepresentatives N P F a initial q) P) child q := by
  let centers := rawRefinementCenters N P F a (initial q) q
  let table := fun r => if r = q then initial q else finiteAnswerTable centers (centers.map initial) r
  have htable (r : TargetInterval ny) (hr : r ∈ centers) : table r = initial r := by
    dsimp only [table]
    split_ifs with heq
    · exact congrArg initial heq.symm
    · exact finiteAnswerTable_map centers initial r hr
  have htableq : table q = initial q := by simp only [table, ite_true, if_true]
  have hreps : localRefinementRepresentatives N P F a table q =
      localRefinementRepresentatives N P F a initial q :=
    localRefinementRepresentatives_congr_raw N P F a table initial q htableq
      (fun r hr => htable r (by simpa only [htableq] using hr))
  let representatives := localRefinementRepresentatives N P F a initial q
  let inputs := wideWarmupInputs (M := M) parent P representatives
  have hinputs : ∀ action ∈ rationalActualWideActions parent representatives P, ∀ i,
      finiteAnswerTable inputs (inputs.map child) (action.childState i) = child (action.childState i) := by
    intro action ha i
    exact finiteAnswerTable_map inputs child _ (wideWarmupInputs_action parent P representatives action ha i)
  simp only [localWarmupStepQuery, FiniteQuery.bind_value, hinitial, FiniteQuery.collect_value,
    hchild, FiniteQuery.value]
  change rationalBellman table _ _
    (rationalActualWideActions parent (localRefinementRepresentatives N P F a table q) P)
    (finiteAnswerTable
      (wideWarmupInputs parent P (localRefinementRepresentatives N P F a table q))
      ((wideWarmupInputs parent P (localRefinementRepresentatives N P F a table q)).map child)) q = _
  rw [hreps]
  unfold rationalBellman
  rw [htableq]
  congr 1
  apply List.map_congr_left
  intro action ha
  unfold rationalActionValue
  congr 1
  exact Finset.sum_congr rfl (fun i hi => hinputs action ha i)



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_WarmupQueryKeys
attribute [-instance] _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Initial and warmup queries preserve reader predicates. In particular,
only same-node seed reads are needed to prove boundedness of every emitted
request; unrelated seed-table entries play no role. -/

namespace EditApproximation

theorem physicalInitialQuery_keys_all {ι α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (N P F : ℕ) (A : ℚ)
    (seedRead : PhysicalEntry M J target.length → FiniteQuery ι)
    (node : PhysicalNode M J) (q : TargetInterval target.length)
    (oracle : ι → ℚ) (predicate : ι → Prop)
    (hseed : ∀ r key, key ∈ (seedRead (node, r)).keys oracle → predicate key) :
    ∀ key ∈ (physicalInitialQuery source target N P F A seedRead (node, q)).keys oracle, predicate key := by
  unfold physicalInitialQuery
  dsimp only
  split_ifs with hleaf
  · intro key hk
    exact False.elim (List.not_mem_nil hk)
  · rw [FiniteQuery.keys_bind]
    intro key hk
    rcases List.mem_append.mp hk with hfirst | hrest
    · exact hseed q key hfirst
    · apply FiniteQuery.keys_all_collect oracle predicate _ _ _ ?_ ?_ key hrest
      · intro r _ other ho
        exact hseed r other ho
      · intro answers other ho
        exact False.elim (List.not_mem_nil ho)

theorem localWarmupStepQuery_keys_all {ι : Type*} {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F : ℕ) (a : ℚ) (initialRead : TargetInterval ny → FiniteQuery ι)
    (childRead : Fin M × TargetInterval ny → FiniteQuery ι) (q : TargetInterval ny)
    (oracle : ι → ℚ) (predicate : ι → Prop)
    (hinitial : ∀ r key, key ∈ (initialRead r).keys oracle → predicate key)
    (hchild : ∀ input key, key ∈ (childRead input).keys oracle → predicate key) :
    ∀ key ∈ (localWarmupStepQuery parent N P F a initialRead childRead q).keys oracle, predicate key := by
  unfold localWarmupStepQuery
  rw [FiniteQuery.keys_bind]
  intro key hk
  rcases List.mem_append.mp hk with hfirst | hrest
  · exact hinitial q key hfirst
  · apply FiniteQuery.keys_all_collect oracle predicate _ _ _ ?_ ?_ key hrest
    · intro r _ other ho
      exact hinitial r other ho
    · intro initialValues
      apply FiniteQuery.keys_all_collect
      · intro input _ other ho
        exact hchild input other ho
      · intro childValues other ho
        exact False.elim (List.not_mem_nil ho)

theorem physicalWarmupRequestQuery_keys_all {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (N P F : ℕ) (A : ℚ)
    (pass copy T S j : ℕ) (node : PhysicalNode M J) (q : TargetInterval target.length)
    (seedRead : PhysicalEntry M J target.length →
      FiniteQuery {child : PhysicalTableRequest M J target.length //
        child.combinedRank T S < (PhysicalTableRequest.warmup pass copy node j q).combinedRank T S})
    (oracle) (predicate : PhysicalTableRequest M J target.length → Prop)
    (hseed : ∀ r key, key ∈ (seedRead (node, r)).keys oracle → predicate key.val)
    (hchild : ∀ (hbelow : node.1.val < J) (input : Fin M × TargetInterval target.length),
      predicate (PhysicalTableRequest.warmup pass copy (physicalChild node hbelow input.1) (j - 1) input.2)) :
    ∀ key ∈ (physicalWarmupRequestQuery source target N P F A pass copy T S j node q seedRead).keys oracle,
      predicate key.val := by
  cases j with
  | zero => exact physicalInitialQuery_keys_all source target N P F A seedRead node q oracle _ hseed
  | succ j =>
    dsimp only [physicalWarmupRequestQuery]
    split_ifs with hbelow hleaf
    · exact physicalInitialQuery_keys_all source target N P F A seedRead node q oracle _ hseed
    · unfold physicalWarmupStepQuery
      apply localWarmupStepQuery_keys_all
      · intro r
        exact physicalInitialQuery_keys_all source target N P F A seedRead node r oracle _ hseed
      · intro input key hk
        simp only [physicalWarmupChildQuery, FiniteQuery.keys, List.mem_singleton] at hk
        subst key
        exact hchild hbelow input
    · exact physicalInitialQuery_keys_all source target N P F A seedRead node q oracle _ hseed

theorem physicalWarmupRequestQuery_keys_bounded {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (N P F : ℕ) (A : ℚ)
    (passes copies pass copy T S j : ℕ) (hpass : pass < passes) (hcopy : copy < copies) (hj : j ≤ T)
    (node : PhysicalNode M J) (q : TargetInterval target.length)
    (seedRead : PhysicalEntry M J target.length →
      FiniteQuery {child : PhysicalTableRequest M J target.length //
        child.combinedRank T S < (PhysicalTableRequest.warmup pass copy node j q).combinedRank T S})
    (oracle)
    (hseed : ∀ r key, key ∈ (seedRead (node, r)).keys oracle → key.val.Bounded passes copies T S) :
    ∀ key ∈ (physicalWarmupRequestQuery source target N P F A pass copy T S j node q seedRead).keys oracle,
      key.val.Bounded passes copies T S := by
  apply physicalWarmupRequestQuery_keys_all source target N P F A pass copy T S j node q seedRead oracle _ hseed
  intro hbelow input
  exact PhysicalTableRequest.warmup_bounded passes copies pass copy (physicalChild node hbelow input.1)
    T S (j - 1) input.2 hpass hcopy (by omega)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_UnifiedPhysicalTable
attribute [-instance] _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cache's unified index uses warmup indices through T and then
refinement indices T+t. Refinement zero is exactly warmup T, including
terminal physical nodes and short source intervals. -/

namespace EditApproximation

theorem physicalLocalWarmup_terminal {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (node : PhysicalNode M J) (t : ℕ)
    (q : TargetInterval target.length)
    (hterminal : ¬ node.1.val < J ∨
      (physicalSourceInterval source.length node).hi - (physicalSourceInterval source.length node).lo ≤ 1) :
    physicalLocalWarmup source target U N P F A t (node, q) =
      stageInitial source target U N P F A (node, q) := by
  cases t with
  | zero => rfl
  | succ t =>
    rw [physicalLocalWarmup]
    rcases hterminal with hdepth | hwidth
    · rw [dite_eq_right hdepth]
    · split_ifs <;> rfl

theorem physicalLocalRefinement_zero {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F exponent Q : ℕ) (A tau delta : ℚ) (T : ℕ)
    (draw : PhysicalInternalNode M J → ℕ → CellGroupDraws M F Q)
    (online : PhysicalNode M J → PhysicalChildTables M target.length → ℕ →
      TargetInterval target.length → List (PhysicalRationalAction M target.length))
    (node : PhysicalNode M J) (q : TargetInterval target.length) :
    physicalLocalRefinement source target U N P F exponent Q A tau delta T draw online node 0 q =
      physicalLocalWarmup source target U N P F A T (node, q) := by
  rw [physicalLocalRefinement]
  split_ifs with hbelow hleaf
  · exact (physicalLocalWarmup_terminal source target U N P F A node T q (Or.inr hleaf)).symm
  · rfl
  · exact (physicalLocalWarmup_terminal source target U N P F A node T q (Or.inl hbelow)).symm

section Unified

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F exponent Q : ℕ) (A tau delta : ℚ) (T : ℕ)
  (draw : PhysicalInternalNode M J → ℕ → CellGroupDraws M F Q)
  (online : PhysicalNode M J → PhysicalChildTables M target.length → ℕ →
    TargetInterval target.length → List (PhysicalRationalAction M target.length))

theorem unifiedPhysicalValue_warmup (node : PhysicalNode M J) (index : ℕ)
    (hi : index ≤ T) (q : TargetInterval target.length) :
    unifiedPhysicalValue source target U N P F exponent Q A tau delta T draw online node index q =
      physicalLocalWarmup source target U N P F A index (node, q) := ite_eq_left hi

theorem unifiedPhysicalValue_refinement (node : PhysicalNode M J) (t : ℕ)
    (q : TargetInterval target.length) :
    unifiedPhysicalValue source target U N P F exponent Q A tau delta T draw online node (T + t) q =
      physicalLocalRefinement source target U N P F exponent Q A tau delta T draw online node t q := by
  cases t with
  | zero =>
    rw [Nat.add_zero, unifiedPhysicalValue_warmup source target U N P F exponent Q A tau delta T draw online node T le_rfl]
    exact (physicalLocalRefinement_zero source target U N P F exponent Q A tau delta T draw online node q).symm
  | succ t =>
    unfold unifiedPhysicalValue
    rw [ite_eq_right (by omega : ¬ T + (t + 1) ≤ T), Nat.add_sub_cancel_left]

end Unified

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalSeedSequence
attribute [-instance] _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mathematical values for the actual local seed passes. This complete
function is a specification for the lazy program, not a table allocated
by the implementation. Copy streams are kept distinct at every pass. -/

namespace EditApproximation

section Sequence

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (N P F exponent H Q T S copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)

theorem localRequestValue_warmup (initial : PhysicalEntry M J target.length → ℕ)
    (pass copy : ℕ) (node : PhysicalNode M J) (j : ℕ) (hj : j ≤ T) (q : TargetInterval target.length) :
    localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial (PhysicalTableRequest.warmup pass copy node j q) =
    physicalLocalWarmup source target
      (localSeedSequence source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial pass) N P F (factor pass) j (node, q) :=
  unifiedPhysicalValue_warmup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hj _

theorem localRequestValue_refinement (initial : PhysicalEntry M J target.length → ℕ)
    (pass copy : ℕ) (node : PhysicalNode M J) (t : ℕ) (q : TargetInterval target.length) :
    localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial (PhysicalTableRequest.refinement pass copy node T t q) =
    localPassValue source target N P F exponent H Q T factor tau eta kappa delta group integer
      (localSeedSequence source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial pass) pass copy node t q :=
  unifiedPhysicalValue_refinement _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

end Sequence

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_WideEarlierInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Wide enumeration gathers child states before scoring its Cartesian
action list. Its recursive input count depends on the coordinate lists,
rather than the exponentially larger number of complete actions. -/

namespace EditApproximation

open Finset

theorem bandCoordinates_earlier_cover {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P history b : ℕ) (tau theta : ℚ)
    (representatives : List (ℕ × TargetInterval target.length)) (r : TargetInterval target.length)
    (hrep : (b, r) ∈ representatives) (child : Fin M → TargetInterval target.length → ℚ)
    (t : ℕ) (ht : t < history) (coordinate : Fin M × TargetInterval target.length)
    (hcoordinate : coordinate ∈ bandCoordinates
      (representativeBandActions source target parent r b P tau theta child).toFinset) :
    (coordinate.1, t, coordinate.2) ∈ wideEarlierInputCover parent P history representatives := by
  obtain ⟨action, ha, hcoordinate⟩ := Finset.mem_biUnion.mp hcoordinate
  obtain ⟨i, _, heq⟩ := Finset.mem_image.mp hcoordinate
  obtain rfl : coordinate = (i, action i) := heq.symm
  exact wideEarlierInputCover_mem parent P history representatives b r hrep t ht action
    (representativeBandActions_wide source target parent r b P tau theta child action
      (List.mem_toFinset.mp ha)) i

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandEarlierDependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The band construction and its literal guards use only the child
coordinates of the finite wide action list. The result types retain the
full tables as indices, so acceptance and returned centers are compared
after projecting away proof fields. -/

namespace EditApproximation

open Finset

theorem representativeBandActions_congr_child {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (b P : ℕ) (tau theta : ℚ) (left right : Fin M → TargetInterval target.length → ℚ)
    (heq : ∀ action ∈ wideActionList M parent r b P,
      ∀ i, left i (action i) = right i (action i)) :
    representativeBandActions source target parent r b P tau theta left =
      representativeBandActions source target parent r b P tau theta right := by
  by_cases hnonempty : wideActionList M parent r b P = []
  · simp only [representativeBandActions, dite_eq_left hnonempty]
  · simp only [representativeBandActions, dite_eq_right hnonempty]
    rw [rationalWideActionMinimum_congr_child parent r b P hnonempty left right heq]
    split_ifs
    · exact computedBandActions_congr_child parent r b P tau theta _ left right heq
    · rfl

theorem representativeBandEnvelope_congr {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (b P exponent : ℕ) (tau : ℚ)
    (child child' initial initial' : Fin M → TargetInterval target.length → ℚ)
    (hchild : ∀ action ∈ wideActionList M parent r b P,
      ∀ i, child i (action i) = child' i (action i))
    (hinitial : ∀ action ∈ wideActionList M parent r b P,
      ∀ i, initial i (action i) = initial' i (action i)) :
    bandChildEnvelope b (representativeBandActions source target parent r b P tau
      ((2 : ℚ) ^ (-(exponent : ℤ))) child) initial =
    bandChildEnvelope b (representativeBandActions source target parent r b P tau
      ((2 : ℚ) ^ (-(exponent : ℤ))) child') initial' := by
  rw [← representativeBandActions_congr_child source target parent r b P tau _ child child' hchild]
  apply bandChildEnvelope_congr_initial
  intro action ha i
  exact hinitial action
    (representativeBandActions_wide source target parent r b P tau _ child action ha) i

theorem testUnskippedBand_isSome_congr {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (b P exponent : ℕ) (tau F : ℚ)
    (child child' initial initial' : Fin M → TargetInterval target.length → ℚ)
    (hchild : ∀ action ∈ wideActionList M parent r b P,
      ∀ i, child i (action i) = child' i (action i))
    (hinitial : ∀ action ∈ wideActionList M parent r b P,
      ∀ i, initial i (action i) = initial' i (action i)) :
    (testUnskippedBand source target parent b P exponent tau F child initial r).isSome =
      (testUnskippedBand source target parent b P exponent tau F child' initial' r).isSome := by
  apply Bool.eq_iff_iff.mpr
  rw [testUnskippedBand_isSome_iff, testUnskippedBand_isSome_iff]
  have hband := representativeBandActions_congr_child source target parent r b P tau
    ((2 : ℚ) ^ (-(exponent : ℤ))) child child' hchild
  rw [← hband]
  have hinitialBand : ∀ action ∈ representativeBandActions source target parent r b P tau
      ((2 : ℚ) ^ (-(exponent : ℤ))) child, ∀ i, initial i (action i) = initial' i (action i) := by
    intro action ha i
    exact hinitial action
      (representativeBandActions_wide source target parent r b P tau _ child action ha) i
  have henv := bandChildEnvelope_congr_initial b _ initial initial' hinitialBand
  have hrounded (hne) := canonicalRoundedBandAction_congr_initial exponent b _ hne
    initial initial' hinitialBand
  simp only [henv, hrounded]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_OnlineEarlierDependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual online optimizer reads only the recorded band coordinates
and earlier child histories. Equality on the finite query cover suffices
for equality of its returned action, including deterministic tie breaking. -/

namespace EditApproximation

open Finset

theorem keyedOnlineCandidate_congr_earlier_cover {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H b history : ℕ) (tau eta kappa : ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (left right : PhysicalChildTables M target.length) (t : ℕ)
    (r : TargetInterval target.length) (integer : ℕ)
    (representatives : List (ℕ × TargetInterval target.length)) (hrep : (b, r) ∈ representatives)
    (ht : t < history)
    (heq : ∀ i s q, (i, s, q) ∈ wideEarlierInputCover parent P history representatives →
      left i s q = right i s q) :
    keyedOnlineCandidate source target parent P F exponent H b tau eta kappa child initial left t r integer =
      keyedOnlineCandidate source target parent P F exponent H b tau eta kappa child initial right t r integer := by
  apply keyedOnlineCandidate_congr_history
  intro i hi s hs
  apply heq
  exact bandCoordinates_earlier_cover source target parent P history b tau _ representatives r hrep
    child s (by omega) i hi

/-- All online candidates for a local query, with their original order
and ties, are fixed by the finite earlier-input cover. -/
theorem localOnlineCandidates_congr_earlier_cover {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H history : ℕ) (tau a eta kappa : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (left right : PhysicalChildTables M target.length) (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ) (q : TargetInterval target.length)
    (ht : t < history)
    (heq : ∀ i s r, (i, s, r) ∈ queryEarlierInputCover parent N P F exponent history a parentInitial q →
      left i s r = right i s r) :
    localOnlineCandidates source target parent N P F exponent H tau a eta kappa
      parentInitial child initial left t integer q =
      localOnlineCandidates source target parent N P F exponent H tau a eta kappa
      parentInitial child initial right t integer q := by
  unfold localOnlineCandidates
  apply List.filterMap_congr
  intro b hb
  dsimp only
  split_ifs with heligible
  · apply keyedOnlineCandidate_congr_earlier_cover source target parent P F exponent H b history
      tau eta kappa child initial left right t _ _
      (queryEarlierRepresentatives N P F exponent a parentInitial q)
      (queryEarlierRepresentatives_online N P F exponent a parentInitial q b hb) ht
    exact heq
  · rfl

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalRefinementQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A local refinement query first reads its finite earlier-history
cover, then the shared current samples, and finally the selected actions.
The continuation is allowed to choose the last list from earlier answers. -/

namespace EditApproximation



theorem historyInputCode_injective (M n : ℕ) :
    Function.Injective (historyInputCode (M := M) (n := n)) := by
  rintro ⟨i, s, q⟩ ⟨i', s', q'⟩ heq
  have h := Nat.pair_eq_pair.mp heq
  have hc := childInputCode_injective M n h.2
  cases hc
  cases h.1
  rfl

section Step

variable {ι α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (parentInitial : TargetInterval target.length → ℚ)
  (child initial : Fin M → TargetInterval target.length → ℚ)
  (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)



theorem localRefinementStepQuery_value (oracle : ι → ℚ)
    (earlier : PhysicalChildTables M target.length)
    (current : Fin M → TargetInterval target.length → ℚ) (ht : 0 < t)
    (hreadEarlier : ∀ input, (readEarlier input).value oracle = earlier input.1 input.2.1 input.2.2)
    (hreadCurrent : ∀ input, (readCurrent input).value oracle = current input.1 input.2) :
    (localRefinementStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial draw integer q readEarlier readCurrent).value oracle =
    rationalLocalWideStep source target parent N P F exponent Q tau a delta parentInitial child initial
      (fun i r => earlier i (t - 1) r) current draw
      (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
        parentInitial child initial earlier (t - 1) integer q) q := by
  let earlierCover := queryEarlierInputCover (M := M) parent N P F exponent t a parentInitial q
  let earlierKeys := orderedInputs historyInputCode (historyInputCode_injective M target.length) earlierCover
  let cachedEarlier := fun i s r => finiteAnswerTable earlierKeys
    (earlierKeys.map fun input => earlier input.1 input.2.1 input.2.2) (i, s, r)
  have hearlier : ∀ i s r, (i, s, r) ∈ earlierCover → cachedEarlier i s r = earlier i s r := by
    intro i s r hr
    exact finiteAnswerTable_map earlierKeys _ _
      ((mem_orderedInputs historyInputCode (historyInputCode_injective M target.length) earlierCover _).2 hr)
  have honline := localOnlineCandidates_congr_earlier_cover source target parent N P F exponent H t
    tau a eta kappa parentInitial child initial cachedEarlier earlier (t - 1) integer q (by omega) hearlier
  let online := localOnlineCandidates source target parent N P F exponent H tau a eta kappa
    parentInitial child initial earlier (t - 1) integer q
  let shared := querySharedInputCover source target parent N F exponent Q a parentInitial q draw
  let sharedKeys := orderedInputs childInputCode (childInputCode_injective M target.length) shared
  let sharedCurrent := fun i r => finiteAnswerTable sharedKeys
    (sharedKeys.map fun input => current input.1 input.2) (i, r)
  have hshared : ∀ input ∈ shared, sharedCurrent input.1 input.2 = current input.1 input.2 := by
    intro input hi
    exact finiteAnswerTable_map sharedKeys _ input
      ((mem_orderedInputs childInputCode (childInputCode_injective M target.length) shared input).2 hi)
  have hselected := localCellGroupActions_congr_cover source target parent N P F exponent Q tau a
    parentInitial child initial sharedCurrent current draw q hshared
  let selected := localCellGroupActions source target parent N P F exponent Q tau a
    parentInitial child initial current draw q
  let needed := actionCurrentInputCover selected ∪ actionCurrentInputCover online
  let currentKeys := orderedInputs childInputCode (childInputCode_injective M target.length) needed
  let cachedCurrent := finiteAnswerTable currentKeys (currentKeys.map fun input => current input.1 input.2)
  have hcurrent : ∀ input ∈ needed, cachedCurrent input = current input.1 input.2 := by
    intro input hi
    exact finiteAnswerTable_map currentKeys _ input
      ((mem_orderedInputs childInputCode (childInputCode_injective M target.length) needed input).2 hi)
  have hgroupValues := rationalActionValues_congr_cover
    (fun q r : TargetInterval target.length => (targetEndpointDistance q r : ℚ)) (128 * F) selected q
    cachedCurrent (fun input => current input.1 input.2)
    (fun input hi => hcurrent input (Finset.mem_union_left _ hi))
  have honlineValues := rationalActionValues_congr_cover
    (fun q r : TargetInterval target.length => (targetEndpointDistance q r : ℚ)) (128 * F) online q
    cachedCurrent (fun input => current input.1 input.2)
    (fun input hi => hcurrent input (Finset.mem_union_right _ hi))
  have hfallback := localBellman_congr_earlier parent N P F exponent t (t - 1) a parentInitial q
    cachedEarlier earlier (by omega) (fun input hi => hearlier input.1 input.2.1 input.2.2 hi) (128 * F)
  unfold localRefinementStepQuery
  rw [FiniteQuery.collect_value]
  simp only [hreadEarlier]
  change (FiniteQuery.collect readCurrent sharedKeys _).value oracle = _
  rw [FiniteQuery.collect_value]
  simp only [hreadCurrent]
  change (FiniteQuery.collect readCurrent
    (orderedInputs childInputCode (childInputCode_injective M target.length)
      (actionCurrentInputCover (localCellGroupActions source target parent N P F exponent Q tau a
        parentInitial child initial sharedCurrent draw q) ∪
        actionCurrentInputCover (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
          parentInitial child initial cachedEarlier (t - 1) integer q))) _).value oracle = _
  rw [hselected, honline, FiniteQuery.collect_value]
  simp only [hreadCurrent, FiniteQuery.value]
  change rationalRefinementUpdate delta
      (rationalMinimum _ (selected.map (rationalActionValue _ _ cachedCurrent q)))
      (rationalOnlineMinimum (online.map (rationalActionValue _ _ cachedCurrent q))) = _
  rw [hgroupValues, honlineValues, hfallback]
  rfl

end Step

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RefinementInitialSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Finite initial-table support for the literal refinement loops. The
query value determines the raw local lists; tests of other initial values
only remove elements from these lists. -/

namespace EditApproximation



theorem refinementInitialSupport_query {n : ℕ} (N P F exponent : ℕ) (a value : ℚ)
    (q : TargetInterval n) : q ∈ refinementInitialSupport N P F exponent a value q :=
  List.mem_cons_self

theorem refinementInitialSupport_local {n : ℕ} (N P F exponent : ℕ) (a value : ℚ)
    (q r : TargetInterval n) (hr : r ∈ rawRefinementCenters N P F a value q) :
    r ∈ refinementInitialSupport N P F exponent a value q := by
  exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ hr))

theorem refinementInitialSupport_cell {n : ℕ} (N P F exponent : ℕ) (a : ℚ)
    (initial : TargetInterval n → ℚ) (q : TargetInterval n) (key : ℕ × (ℕ × ℕ))
    (hk : key ∈ localGroupQueryKeys N F exponent a initial q) (r : TargetInterval n)
    (hr : r ∈ cellTargetStates n (seedGridSpacing key.1 P)
      ((2 : ℚ) ^ (-(exponent : ℤ)) * key.1) key.2) :
    r ∈ refinementInitialSupport N P F exponent a (initial q) q := by
  apply List.mem_cons_of_mem
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨key, ?_, hr⟩
  simpa only [localGroupQueryKeys] using hk

theorem refinementInitialSupport_online {n : ℕ} (N P F exponent : ℕ) (a value : ℚ)
    (q : TargetInterval n) (b : ℕ) (hb : b ∈ dyadicQueryWindow N value a F) :
    roundInterval (seedGridSpacing b P) q ∈ refinementInitialSupport N P F exponent a value q := by
  apply List.mem_cons_of_mem
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨b, hb, rfl⟩

theorem cellRepresentativeStates_congr_initial {n : ℕ} (P F b : ℕ) (a theta : ℚ)
    (left right : TargetInterval n → ℚ) (cell : ℕ × ℕ)
    (heq : ∀ r ∈ cellTargetStates n (seedGridSpacing b P) (theta * b) cell,
      left r = right r) :
    cellRepresentativeStates n P F b a left theta cell =
      cellRepresentativeStates n P F b a right theta cell := by
  unfold cellRepresentativeStates
  apply List.filter_congr
  intro r hr
  rw [heq r hr]

section ParentTable

variable {n : ℕ} (N P F exponent : ℕ) (a : ℚ)
  (left right : TargetInterval n → ℚ) (q : TargetInterval n)
  (heq : ∀ r ∈ refinementInitialSupport N P F exponent a (left q) q, left r = right r)

include heq

theorem refinement_local_representatives_congr :
    localRefinementRepresentatives N P F a left q = localRefinementRepresentatives N P F a right q := by
  apply localRefinementRepresentatives_congr_raw
  · exact heq q (refinementInitialSupport_query N P F exponent a (left q) q)
  · intro r hr
    exact heq r (refinementInitialSupport_local N P F exponent a (left q) q r hr)

theorem refinement_cell_representatives_congr (key : ℕ × (ℕ × ℕ))
    (hk : key ∈ localGroupQueryKeys N F exponent a left q) :
    cellRepresentativeStates n P F key.1 a left ((2 : ℚ) ^ (-(exponent : ℤ))) key.2 =
      cellRepresentativeStates n P F key.1 a right ((2 : ℚ) ^ (-(exponent : ℤ))) key.2 := by
  apply cellRepresentativeStates_congr_initial
  intro r hr
  exact heq r (refinementInitialSupport_cell N P F exponent a left q key hk r hr)

end ParentTable

section Programs

variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa : ℚ) (t : ℕ)
  (left right : TargetInterval target.length → ℚ)
  (child initial current : Fin M → TargetInterval target.length → ℚ)
  (children : PhysicalChildTables M target.length)
  (integer : ℕ → TargetInterval target.length → ℕ) (draw : CellGroupDraws M F Q)
  (q : TargetInterval target.length)
  (heq : ∀ r ∈ refinementInitialSupport N P F exponent a (left q) q, left r = right r)

include heq

theorem localOnlineCandidates_congr_initial :
    localOnlineCandidates source target parent N P F exponent H tau a eta kappa
      left child initial children t integer q =
    localOnlineCandidates source target parent N P F exponent H tau a eta kappa
      right child initial children t integer q := by
  have hq := heq q (refinementInitialSupport_query N P F exponent a (left q) q)
  unfold localOnlineCandidates
  rw [← hq]
  apply List.filterMap_congr
  intro b hb
  dsimp only
  rw [heq _ (refinementInitialSupport_online N P F exponent a (left q) q b hb)]

theorem localCellGroupActions_congr_initial :
    localCellGroupActions source target parent N P F exponent Q tau a left child initial current draw q =
      localCellGroupActions source target parent N P F exponent Q tau a right child initial current draw q := by
  have hq := heq q (refinementInitialSupport_query N P F exponent a (left q) q)
  unfold localCellGroupActions
  rw [← hq]
  apply List.flatMap_congr
  intro b hb
  apply List.filterMap_congr
  intro cell hc
  unfold chooseCellGroupAction cellUnskippedBands
  rw [refinement_cell_representatives_congr N P F exponent a left right q heq (b, cell)
    (List.mem_flatMap.mpr ⟨b, hb, List.mem_map.mpr ⟨cell, hc, rfl⟩⟩)]

theorem rationalLocalWideStep_congr_initial (delta : ℚ)
    (old : Fin M → TargetInterval target.length → ℚ)
    (online : List (PhysicalRationalAction M target.length)) :
    rationalLocalWideStep source target parent N P F exponent Q tau a delta left
      child initial old current draw online q =
    rationalLocalWideStep source target parent N P F exponent Q tau a delta right
      child initial old current draw online q := by
  have hgroups := localCellGroupActions_congr_initial source target parent N P F exponent Q tau a
    left right child initial current draw q heq
  have hreps := refinement_local_representatives_congr N P F exponent a left right q heq
  have hq := heq q (refinementInitialSupport_query N P F exponent a (left q) q)
  unfold rationalLocalWideStep
  rw [hgroups, hreps]
  unfold rationalBellman
  rw [hq]

end Programs

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RefinementBandSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Band-table congruence uses proof-free data. Equality of these data
preserves the ordered minimization and its tie decisions, even though the
guard records have different table-indexed types. -/

namespace EditApproximation

abbrev UnskippedBandData (M ny : ℕ) :=
  TargetInterval ny × (Fin M → ℚ) × (Fin M → TargetInterval ny)

def UnskippedBand.data {α : Type*} {source target : List α} {M b P exponent : ℕ}
    {parent : TargetInterval source.length} {tau F : ℚ}
    {child initial : Fin M → TargetInterval target.length → ℚ}
    (member : UnskippedBand source target parent b P exponent tau F child initial) :
    UnskippedBandData M target.length :=
  (member.center, member.envelope, member.rounded)

def UnskippedBandData.action {M ny : ℕ} (data : UnskippedBandData M ny) :
    PhysicalRationalAction M ny :=
  ⟨data.1, endpointActionConnection data.1 data.2.2, fun i => (i, data.2.2 i)⟩

def UnskippedBandData.estimate {M ny : ℕ} (b Q : ℕ) (F : ℚ)
    (value : Fin M → TargetInterval ny → ℚ)
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (data : UnskippedBandData M ny) : ℚ :=
  groupMemberEstimate (groupDyadicScaleAt M b F)
    (fun scale => groupSampleCount M Q b (groupDyadicScaleAt M b F scale))
    (endpointActionConnection data.1 data.2.2) data.2.1 (fun i => value i (data.2.2 i)) draw

theorem testUnskippedBand_center_of_some {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P exponent : ℕ) (tau F : ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ) (r : TargetInterval target.length)
    (member : UnskippedBand source target parent b P exponent tau F child initial)
    (hmember : testUnskippedBand source target parent b P exponent tau F child initial r = some member) :
    member.center = r := by
  have h := testUnskippedBand_center_projection source target parent r b P exponent tau F child initial
  rw [hmember] at h
  simpa only [Option.map_some, Option.isSome_some, Bool.true_eq, ite_true, if_true, Option.some.injEq] using h

theorem unskippedBand_data_congr {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (b P exponent : ℕ) (tau F : ℚ)
    (child child' initial initial' : Fin M → TargetInterval target.length → ℚ)
    (hchild : ∀ action ∈ wideActionList M parent r b P,
      ∀ i, child i (action i) = child' i (action i))
    (hinitial : ∀ action ∈ wideActionList M parent r b P,
      ∀ i, initial i (action i) = initial' i (action i))
    (left : UnskippedBand source target parent b P exponent tau F child initial)
    (right : UnskippedBand source target parent b P exponent tau F child' initial')
    (hleft : left.center = r) (hright : right.center = r) : left.data = right.data := by
  have hband := representativeBandActions_congr_child source target parent r b P tau
    ((2 : ℚ) ^ (-(exponent : ℤ))) child child' hchild
  have hinitialBand : ∀ action ∈ representativeBandActions source target parent r b P tau
      ((2 : ℚ) ^ (-(exponent : ℤ))) child, ∀ i, initial i (action i) = initial' i (action i) := by
    intro action ha i
    exact hinitial action (representativeBandActions_wide source target parent r b P tau _ child action ha) i
  apply Prod.ext (hleft.trans hright.symm)
  apply Prod.ext
  · change left.envelope = right.envelope
    unfold UnskippedBand.envelope UnskippedBand.actions
    rw [hleft, hright]
    exact representativeBandEnvelope_congr source target parent r b P exponent tau
      child child' initial initial' hchild hinitial
  · change left.rounded = right.rounded
    have hactions : left.actions = right.actions := by
      simp only [UnskippedBand.actions, hleft, hright]
      exact hband
    have hrightInitial : ∀ action ∈ right.actions,
        ∀ i, initial i (action i) = initial' i (action i) := by
      intro action ha i
      simp only [UnskippedBand.actions, hright, ← hband] at ha
      exact hinitialBand action ha i
    exact (UnskippedBand.canonicalRounded_congr exponent b left.actions right.actions
      hactions left.nonempty right.nonempty initial).trans
      (canonicalRoundedBandAction_congr_initial exponent b right.actions right.nonempty
        initial initial' hrightInitial)

theorem testUnskippedBand_data_congr {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (b P exponent : ℕ) (tau F : ℚ)
    (child child' initial initial' : Fin M → TargetInterval target.length → ℚ)
    (hchild : ∀ action ∈ wideActionList M parent r b P,
      ∀ i, child i (action i) = child' i (action i))
    (hinitial : ∀ action ∈ wideActionList M parent r b P,
      ∀ i, initial i (action i) = initial' i (action i)) :
    (testUnskippedBand source target parent b P exponent tau F child initial r).map UnskippedBand.data =
      (testUnskippedBand source target parent b P exponent tau F child' initial' r).map UnskippedBand.data := by
  have haccept := testUnskippedBand_isSome_congr source target parent r b P exponent tau F
    child child' initial initial' hchild hinitial
  cases hleft : testUnskippedBand source target parent b P exponent tau F child initial r with
  | none =>
    cases hright : testUnskippedBand source target parent b P exponent tau F child' initial' r with
    | none => rfl
    | some right => simp only [hleft, hright, Option.isSome_none, Option.isSome_some, Bool.false_eq_true] at haccept
  | some left =>
    cases hright : testUnskippedBand source target parent b P exponent tau F child' initial' r with
    | none => simp only [hleft, hright, Option.isSome_none, Option.isSome_some, Bool.true_eq_false] at haccept
    | some right =>
      apply congrArg some
      exact unskippedBand_data_congr source target parent r b P exponent tau F child child' initial initial'
        hchild hinitial left right
        (testUnskippedBand_center_of_some source target parent b P exponent tau F child initial r left hleft)
        (testUnskippedBand_center_of_some source target parent b P exponent tau F child' initial' r right hright)

theorem unskippedBandList_data_congr {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P exponent : ℕ) (tau F : ℚ)
    (child child' initial initial' : Fin M → TargetInterval target.length → ℚ)
    (centers : List (TargetInterval target.length))
    (hchild : ∀ r ∈ centers, ∀ action ∈ wideActionList M parent r b P,
      ∀ i, child i (action i) = child' i (action i))
    (hinitial : ∀ r ∈ centers, ∀ action ∈ wideActionList M parent r b P,
      ∀ i, initial i (action i) = initial' i (action i)) :
    (unskippedBandList source target parent b P exponent tau F child initial centers).map UnskippedBand.data =
      (unskippedBandList source target parent b P exponent tau F child' initial' centers).map UnskippedBand.data := by
  simp only [unskippedBandList, List.map_filterMap]
  apply List.filterMap_congr
  intro r hr
  exact testUnskippedBand_data_congr source target parent r b P exponent tau F
    child child' initial initial' (hchild r hr) (hinitial r hr)

theorem chooseCellGroupAction_data {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (tau a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial current : Fin M → TargetInterval target.length → ℚ) (cell : ℕ × ℕ)
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M) :
    chooseCellGroupAction source target parent b P F exponent Q tau a parentInitial
      child initial current cell draw =
      (((cellUnskippedBands source target parent b P F exponent tau a parentInitial child initial cell).map
        UnskippedBand.data).argmax (fun data => -data.estimate b Q F current draw)).map UnskippedBandData.action := by
  let members := cellUnskippedBands source target parent b P F exponent tau a parentInitial child initial cell
  change (if h : members = [] then none else some (chooseUnskippedGroup Q current members h draw).rationalAction) = _
  rw [← rational_argmax_map members UnskippedBand.data (fun data => -data.estimate b Q F current draw)]
  by_cases hnil : members = []
  · simp only [hnil, dite_true, List.argmax_nil, Option.map_none]
  · rw [dite_eq_right hnil]
    unfold chooseUnskippedGroup selectGroupMember
    change some (UnskippedBand.rationalAction
        ((members.argmax (fun member => -member.data.estimate b Q F current draw)).getD (members.head hnil))) = _
    cases hmax : members.argmax (fun member => -member.data.estimate b Q F current draw) with
    | none => exact False.elim (hnil (List.argmax_eq_none.mp hmax))
    | some selected => rfl

theorem chooseCellGroupAction_congr_bandTables {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (tau a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child child' initial initial' current : Fin M → TargetInterval target.length → ℚ) (cell : ℕ × ℕ)
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (hchild : ∀ r ∈ cellRepresentativeStates target.length P F b a parentInitial
        ((2 : ℚ) ^ (-(exponent : ℤ))) cell, ∀ action ∈ wideActionList M parent r b P,
      ∀ i, child i (action i) = child' i (action i))
    (hinitial : ∀ r ∈ cellRepresentativeStates target.length P F b a parentInitial
        ((2 : ℚ) ^ (-(exponent : ℤ))) cell, ∀ action ∈ wideActionList M parent r b P,
      ∀ i, initial i (action i) = initial' i (action i)) :
    chooseCellGroupAction source target parent b P F exponent Q tau a parentInitial
      child initial current cell draw =
    chooseCellGroupAction source target parent b P F exponent Q tau a parentInitial
      child' initial' current cell draw := by
  rw [chooseCellGroupAction_data, chooseCellGroupAction_data]
  rw [show (cellUnskippedBands source target parent b P F exponent tau a parentInitial child initial cell).map
      UnskippedBand.data =
      (cellUnskippedBands source target parent b P F exponent tau a parentInitial child' initial' cell).map
        UnskippedBand.data from
    unskippedBandList_data_congr source target parent b P exponent tau F child child' initial initial' _
      hchild hinitial]

/-- Keep the optimizer opaque while transporting the finite band data. -/
def bandDataOnlineCandidate {M ny : ℕ} (band : List (Fin M → TargetInterval ny))
    (envelope : Fin M → ℚ) (H : ℕ) (eta kappa : ℚ)
    (children : PhysicalChildTables M ny) (t : ℕ) (r : TargetInterval ny)
    (integer : ℕ) (accepted : Bool) : Option (PhysicalRationalAction M ny) :=
  let G := H + (bandCoordinates band.toFinset).card + 2
  let K := G ^ 80
  let sample := boundedOnlineInteger (optimizerTriangularMass K)
    (optimizerTriangularMass_positive _ (pow_pos (by omega : 0 < G) 80)) integer
  if hband : band = [] then none else
    if accepted then some (sharedBandRationalAction r (finiteOptimizerActionDraw band hband envelope
      (rationalOnlineLinear eta kappa
        (childGain envelope (fun s coordinate => children coordinate.1 s coordinate.2))
        (childDecrement envelope (fun s coordinate => children coordinate.1 s coordinate.2)) t)
      G K sample))
    else none

theorem keyedOnlineCandidate_test_form {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H b : ℕ) (tau eta kappa : ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (children : PhysicalChildTables M target.length) (t : ℕ)
    (r : TargetInterval target.length) (integer : ℕ) :
    keyedOnlineCandidate source target parent P F exponent H b tau eta kappa
      child initial children t r integer =
    bandDataOnlineCandidate
      (representativeBandActions source target parent r b P tau ((2 : ℚ) ^ (-(exponent : ℤ))) child)
      (bandChildEnvelope b
        (representativeBandActions source target parent r b P tau ((2 : ℚ) ^ (-(exponent : ℤ))) child) initial)
      H eta kappa children t r integer
      (testUnskippedBand source target parent b P exponent tau F child initial r).isSome := by
  unfold keyedOnlineCandidate bandDataOnlineCandidate
  dsimp only
  by_cases hband : representativeBandActions source target parent r b P tau
      ((2 : ℚ) ^ (-(exponent : ℤ))) child = []
  · simp only [dite_eq_left hband]
  · simp only [dite_eq_right hband]
    cases testUnskippedBand source target parent b P exponent tau F child initial r <;> rfl

theorem keyedOnlineCandidate_congr_bandTables {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H b : ℕ) (tau eta kappa : ℚ)
    (child child' initial initial' : Fin M → TargetInterval target.length → ℚ)
    (children : PhysicalChildTables M target.length) (t : ℕ)
    (r : TargetInterval target.length) (integer : ℕ)
    (hchild : ∀ action ∈ wideActionList M parent r b P,
      ∀ i, child i (action i) = child' i (action i))
    (hinitial : ∀ action ∈ wideActionList M parent r b P,
      ∀ i, initial i (action i) = initial' i (action i)) :
    keyedOnlineCandidate source target parent P F exponent H b tau eta kappa
      child initial children t r integer =
    keyedOnlineCandidate source target parent P F exponent H b tau eta kappa
      child' initial' children t r integer := by
  have hband := representativeBandActions_congr_child source target parent r b P tau
    ((2 : ℚ) ^ (-(exponent : ℤ))) child child' hchild
  have henv := representativeBandEnvelope_congr source target parent r b P exponent tau
    child child' initial initial' hchild hinitial
  have htest := testUnskippedBand_isSome_congr source target parent r b P exponent tau F
    child child' initial initial' hchild hinitial
  rw [keyedOnlineCandidate_test_form, keyedOnlineCandidate_test_form]
  rw [htest, henv, hband]

theorem wideWarmupInputs_pair {nx ny M : ℕ} (parent : TargetInterval nx) (P b : ℕ)
    (representatives : List (ℕ × TargetInterval ny)) (r : TargetInterval ny)
    (hrep : (b, r) ∈ representatives) (action : Fin M → TargetInterval ny)
    (haction : action ∈ wideActionList M parent r b P) (i : Fin M) :
    (i, action i) ∈ wideWarmupInputs parent P representatives := by
  apply List.mem_eraseDups.mpr
  apply List.mem_flatMap.mpr
  refine ⟨(b, r), hrep, List.mem_flatMap.mpr ?_⟩
  exact ⟨i, List.mem_finRange i, List.mem_map.mpr
    ⟨action i, finiteAssignments_sound M _ action haction i, rfl⟩⟩



section QueryBands

variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa : ℚ) (t : ℕ)
  (parentInitial : TargetInterval target.length → ℚ)
  (child child' initial initial' current : Fin M → TargetInterval target.length → ℚ)
  (children : PhysicalChildTables M target.length)
  (integer : ℕ → TargetInterval target.length → ℕ) (draw : CellGroupDraws M F Q)
  (q : TargetInterval target.length)
  (hchild : ∀ input ∈ refinementBandInputList parent N P F exponent a parentInitial q,
    child input.1 input.2 = child' input.1 input.2)
  (hinitial : ∀ input ∈ refinementBandInputList parent N P F exponent a parentInitial q,
    initial input.1 input.2 = initial' input.1 input.2)

include hchild hinitial

theorem localOnlineCandidates_congr_bandTables :
    localOnlineCandidates source target parent N P F exponent H tau a eta kappa
      parentInitial child initial children t integer q =
    localOnlineCandidates source target parent N P F exponent H tau a eta kappa
      parentInitial child' initial' children t integer q := by
  unfold localOnlineCandidates
  apply List.filterMap_congr
  intro b hb
  dsimp only
  split_ifs with heligible
  · apply keyedOnlineCandidate_congr_bandTables source target parent P F exponent H b tau eta kappa
      child child' initial initial' children t _ _
    · intro action ha i
      exact hchild _ (wideWarmupInputs_pair parent P b _ _
        (queryEarlierRepresentatives_online N P F exponent a parentInitial q b hb) action ha i)
    · intro action ha i
      exact hinitial _ (wideWarmupInputs_pair parent P b _ _
        (queryEarlierRepresentatives_online N P F exponent a parentInitial q b hb) action ha i)
  · rfl

theorem localCellGroupActions_congr_bandTables :
    localCellGroupActions source target parent N P F exponent Q tau a parentInitial
      child initial current draw q =
    localCellGroupActions source target parent N P F exponent Q tau a parentInitial
      child' initial' current draw q := by
  unfold localCellGroupActions
  apply List.flatMap_congr
  intro b hb
  apply List.filterMap_congr
  intro cell hc
  have hkey : (b, cell) ∈ localGroupQueryKeys N F exponent a parentInitial q :=
    List.mem_flatMap.mpr ⟨b, hb, List.mem_map.mpr ⟨cell, hc, rfl⟩⟩
  apply chooseCellGroupAction_congr_bandTables source target parent b P F exponent Q tau a
    parentInitial child child' initial initial' current cell (draw b cell)
  · intro r hr action ha i
    exact hchild _ (wideWarmupInputs_pair parent P b _ r
      (queryEarlierRepresentatives_cell N P F exponent a parentInitial q (b, cell) hkey r hr) action ha i)
  · intro r hr action ha i
    exact hinitial _ (wideWarmupInputs_pair parent P b _ r
      (queryEarlierRepresentatives_cell N P F exponent a parentInitial q (b, cell) hkey r hr) action ha i)

end QueryBands

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RefinementDataQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Adaptive gathering of all fixed data used by one local refinement
entry: parent initial values, child warmup masses and child initial values.
Only the raw local support and the resulting wide coordinate lists are
requested. The later earlier/current gathers remain those of the literal
local refinement query. -/

namespace EditApproximation

section BandData

variable {ι α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (parentInitial : TargetInterval target.length → ℚ)
  (readMass readInitial : Fin M × TargetInterval target.length → FiniteQuery ι)
  (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)

def localRefinementBandDataQuery : FiniteQuery ι :=
  let keys := refinementBandInputList (M := M) parent N P F exponent a parentInitial q
  FiniteQuery.collect readMass keys fun massValues =>
    FiniteQuery.collect readInitial keys fun initialValues =>
      localRefinementStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
        parentInitial (fun i r => finiteAnswerTable keys massValues (i, r))
        (fun i r => finiteAnswerTable keys initialValues (i, r)) draw integer q readEarlier readCurrent

theorem localRefinementBandDataQuery_value (oracle : ι → ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (earlier : PhysicalChildTables M target.length)
    (current : Fin M → TargetInterval target.length → ℚ) (ht : 0 < t)
    (hreadMass : ∀ input, (readMass input).value oracle = child input.1 input.2)
    (hreadInitial : ∀ input, (readInitial input).value oracle = initial input.1 input.2)
    (hreadEarlier : ∀ input, (readEarlier input).value oracle = earlier input.1 input.2.1 input.2.2)
    (hreadCurrent : ∀ input, (readCurrent input).value oracle = current input.1 input.2) :
    (localRefinementBandDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial readMass readInitial draw integer q readEarlier readCurrent).value oracle =
    rationalLocalWideStep source target parent N P F exponent Q tau a delta parentInitial child initial
      (fun i r => earlier i (t - 1) r) current draw
      (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
        parentInitial child initial earlier (t - 1) integer q) q := by
  let keys := refinementBandInputList (M := M) parent N P F exponent a parentInitial q
  let mass := fun i r => finiteAnswerTable keys (keys.map fun input => child input.1 input.2) (i, r)
  let initial' := fun i r => finiteAnswerTable keys (keys.map fun input => initial input.1 input.2) (i, r)
  have hmass : ∀ input ∈ keys, mass input.1 input.2 = child input.1 input.2 := by
    intro input hi
    exact finiteAnswerTable_map keys _ input hi
  have hinitial : ∀ input ∈ keys, initial' input.1 input.2 = initial input.1 input.2 := by
    intro input hi
    exact finiteAnswerTable_map keys _ input hi
  have honline := localOnlineCandidates_congr_bandTables source target parent N P F exponent H
    tau a eta kappa (t - 1) parentInitial mass child initial' initial earlier integer q hmass hinitial
  have hgroups := localCellGroupActions_congr_bandTables source target parent N P F exponent Q
    tau a parentInitial mass child initial' initial current draw q hmass hinitial
  unfold localRefinementBandDataQuery
  rw [FiniteQuery.collect_value]
  simp only [hreadMass]
  rw [FiniteQuery.collect_value]
  simp only [hreadInitial]
  rw [localRefinementStepQuery_value source target parent N P F exponent H Q tau a eta kappa delta t
    parentInitial mass initial' draw integer q readEarlier readCurrent oracle earlier current ht
    hreadEarlier hreadCurrent]
  rw [honline]
  unfold rationalLocalWideStep
  rw [hgroups]

end BandData

section AllData

variable {ι α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (readParentInitial : TargetInterval target.length → FiniteQuery ι)
  (readMass readInitial : Fin M × TargetInterval target.length → FiniteQuery ι)
  (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)

def localRefinementDataQuery : FiniteQuery ι :=
  FiniteQuery.bind (readParentInitial q) fun value =>
    let keys := refinementInitialSupport N P F exponent a value q
    FiniteQuery.collect readParentInitial keys fun initialValues =>
      localRefinementBandDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
        (finiteAnswerTable keys initialValues) readMass readInitial draw integer q readEarlier readCurrent

theorem localRefinementDataQuery_value (oracle : ι → ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (earlier : PhysicalChildTables M target.length)
    (current : Fin M → TargetInterval target.length → ℚ) (ht : 0 < t)
    (hreadParentInitial : ∀ r, (readParentInitial r).value oracle = parentInitial r)
    (hreadMass : ∀ input, (readMass input).value oracle = child input.1 input.2)
    (hreadInitial : ∀ input, (readInitial input).value oracle = initial input.1 input.2)
    (hreadEarlier : ∀ input, (readEarlier input).value oracle = earlier input.1 input.2.1 input.2.2)
    (hreadCurrent : ∀ input, (readCurrent input).value oracle = current input.1 input.2) :
    (localRefinementDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
      readParentInitial readMass readInitial draw integer q readEarlier readCurrent).value oracle =
    rationalLocalWideStep source target parent N P F exponent Q tau a delta parentInitial child initial
      (fun i r => earlier i (t - 1) r) current draw
      (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
        parentInitial child initial earlier (t - 1) integer q) q := by
  let keys := refinementInitialSupport N P F exponent a (parentInitial q) q
  let cached := finiteAnswerTable keys (keys.map parentInitial)
  have heq : ∀ r ∈ refinementInitialSupport N P F exponent a (parentInitial q) q,
      parentInitial r = cached r := by
    intro r hr
    exact (finiteAnswerTable_map keys parentInitial r hr).symm
  have honline := localOnlineCandidates_congr_initial source target parent N P F exponent H
    tau a eta kappa (t - 1) parentInitial cached child initial earlier integer q heq
  have hstep := rationalLocalWideStep_congr_initial source target parent N P F exponent Q tau a
    parentInitial cached child initial current draw q heq delta (fun i r => earlier i (t - 1) r)
    (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
      parentInitial child initial earlier (t - 1) integer q)
  unfold localRefinementDataQuery
  rw [FiniteQuery.bind_value, hreadParentInitial q, FiniteQuery.collect_value]
  simp only [hreadParentInitial]
  rw [localRefinementBandDataQuery_value source target parent N P F exponent H Q tau a eta kappa delta t
    cached readMass readInitial draw integer q readEarlier readCurrent oracle child initial earlier current ht
    hreadMass hreadInitial hreadEarlier hreadCurrent]
  rw [← honline]
  exact hstep.symm

end AllData

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRefinementRequest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Concrete current and earlier child requests for refinement. The
history reader is total, with unused future times returning zero; the
local program only asks times below the current one. -/

namespace EditApproximation

theorem wideEarlierInputCover_time {nx ny M : ℕ} (parent : TargetInterval nx)
    (P history : ℕ) (representatives : List (ℕ × TargetInterval ny))
    (input : Fin M × ℕ × TargetInterval ny)
    (hinput : input ∈ wideEarlierInputCover parent P history representatives) : input.2.1 < history := by
  obtain ⟨br, _, hinput⟩ := Finset.mem_biUnion.mp hinput
  obtain ⟨i, _, hinput⟩ := Finset.mem_biUnion.mp hinput
  obtain ⟨t, ht, hinput⟩ := Finset.mem_biUnion.mp hinput
  obtain ⟨r, _, heq⟩ := Finset.mem_image.mp hinput
  have hs := congrArg (fun input : Fin M × ℕ × TargetInterval ny => input.2.1) heq
  exact hs ▸ Finset.mem_range.mp ht





end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRefinementDataRequest
attribute [-instance] _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! All initial and warmup-mass data are ordinary earlier table
requests. A positive refinement step therefore has no fixed-table oracle
arguments. Parent initial data use the same node's warmup-zero entry;
child data and histories use the concrete physical children. -/

namespace EditApproximation

theorem physicalInitialQuery_value_local {ι α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (N P F : ℕ) (A : ℚ)
    (seedRead : PhysicalEntry M J target.length → FiniteQuery ι)
    (oracle : ι → ℚ) (U : PhysicalEntry M J target.length → ℕ)
    (node : PhysicalNode M J) (q : TargetInterval target.length)
    (hseed : ∀ r, (seedRead (node, r)).value oracle = (U (node, r) : ℚ)) :
    (physicalInitialQuery source target N P F A seedRead (node, q)).value oracle =
      stageInitial source target U N P F A (node, q) := by
  unfold physicalInitialQuery stageInitial physicalInitialTable
  dsimp only
  split_ifs with hleaf
  · rfl
  · rw [FiniteQuery.bind_value, hseed q]
    simp only [Nat.ceil_natCast]
    rw [FiniteQuery.collect_value]
    simp only [hseed, FiniteQuery.value]
    symm
    apply localInitialConeTable_congr_raw
    · simp only [ite_true, if_true]
    · intro r hr
      by_cases heq : r = q
      · subst r
        simp only [ite_true, if_true]
      · rw [ite_eq_right heq, finiteAnswerTable_map _ _ r hr, Nat.ceil_natCast]

theorem physicalWarmupStepQuery_value_local {ι α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (N P F : ℕ) (A : ℚ)
    (seedRead : PhysicalEntry M J target.length → FiniteQuery ι)
    (childRead : Fin M × TargetInterval target.length → FiniteQuery ι) (oracle : ι → ℚ)
    (U : PhysicalEntry M J target.length → ℕ)
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (hleaf : ¬ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1)
    (t : ℕ) (q : TargetInterval target.length)
    (hseed : ∀ r, (seedRead (node, r)).value oracle = (U (node, r) : ℚ))
    (hchild : ∀ input, (childRead input).value oracle =
      physicalLocalWarmup source target U N P F A t (physicalChild node hbelow input.1, input.2)) :
    (physicalWarmupStepQuery source target N P F A seedRead childRead node q).value oracle =
      physicalLocalWarmup source target U N P F A (t + 1) (node, q) := by
  rw [physicalLocalWarmup]
  simp only [dite_eq_left hbelow, ite_eq_right hleaf]
  exact localWarmupStepQuery_value _ N P F (refinementFactor A F) _ _ oracle _ _
    (fun r => physicalInitialQuery_value_local source target N P F A seedRead oracle U node r hseed)
    hchild q

theorem physicalWarmupRequestQuery_value_local {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (N P F : ℕ) (A : ℚ)
    (pass copy T S j : ℕ) (node : PhysicalNode M J) (q : TargetInterval target.length)
    (seedRead : PhysicalEntry M J target.length →
      FiniteQuery {child : PhysicalTableRequest M J target.length //
        child.combinedRank T S < (PhysicalTableRequest.warmup pass copy node j q).combinedRank T S})
    (values : PhysicalTableRequest M J target.length → ℚ)
    (U : PhysicalEntry M J target.length → ℕ)
    (hseed : ∀ r, (seedRead (node, r)).value (fun child => values child.val) = (U (node, r) : ℚ))
    (hchild : ∀ (hbelow : node.1.val < J) (input : Fin M × TargetInterval target.length),
      values (PhysicalTableRequest.warmup pass copy (physicalChild node hbelow input.1) (j - 1) input.2) =
        physicalLocalWarmup source target U N P F A (j - 1)
          (physicalChild node hbelow input.1, input.2)) :
    (physicalWarmupRequestQuery source target N P F A pass copy T S j node q seedRead).value
      (fun child => values child.val) = physicalLocalWarmup source target U N P F A j (node, q) := by
  cases j with
  | zero => exact physicalInitialQuery_value_local source target N P F A seedRead _ U node q hseed
  | succ t =>
    dsimp only [physicalWarmupRequestQuery]
    split_ifs with hbelow hleaf
    · rw [physicalLocalWarmup]
      simp only [dite_eq_left hbelow, ite_eq_left hleaf]
      exact physicalInitialQuery_value_local source target N P F A seedRead _ U node q hseed
    · apply physicalWarmupStepQuery_value_local source target N P F A seedRead _ _ U
        node hbelow hleaf t q hseed
      intro input
      exact hchild hbelow input
    · rw [physicalLocalWarmup]
      simp only [dite_eq_right hbelow]
      exact physicalInitialQuery_value_local source target N P F A seedRead _ U node q hseed





theorem physicalRefinementMassQuery_value {M J ny : ℕ} (pass copy T S t : ℕ) (ht : 0 < t)
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (q : TargetInterval ny)
    (input : Fin M × TargetInterval ny) (answer : PhysicalTableRequest M J ny → ℚ) :
    (physicalRefinementMassQuery pass copy T S t ht node hbelow q input).value
      (fun request => answer request.val) =
      (∑ j : Fin T, answer (PhysicalTableRequest.warmup pass copy
        (physicalChild node hbelow input.1) j.val input.2)) / T := by
  simp only [physicalRefinementMassQuery, FiniteQuery.collect_value, physicalRefinementWarmupRead,
    FiniteQuery.value, List.map_ofFn, List.sum_ofFn, Function.comp_def]

section CompleteStep

variable {α : Type*} (source target : List α) {M J : ℕ}
  (N P F exponent H Q : ℕ) (tau a eta kappa delta : ℚ)
  (pass copy T S t : ℕ) (ht : 0 < t) (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
  (q : TargetInterval target.length)

def physicalRefinementDataRequestQuery :
    FiniteQuery {child : PhysicalTableRequest M J target.length //
      child.combinedRank T S < (PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} :=
  localRefinementDataQuery source target (physicalSourceInterval source.length node)
    N P F exponent H Q tau a eta kappa delta t
    (physicalRefinementWarmupRead pass copy T S t ht node q node le_rfl 0 (Nat.zero_le T))
    (physicalRefinementMassQuery pass copy T S t ht node hbelow q)
    (fun input => physicalRefinementWarmupRead pass copy T S t ht node q
      (physicalChild node hbelow input.1) (by change node.1.val ≤ node.1.val + 1; omega)
      0 (Nat.zero_le T) input.2)
    draw integer q (physicalRefinementEarlierQuery pass copy T S t node hbelow q)
    (physicalRefinementCurrentQuery pass copy T S t node hbelow q)

theorem physicalRefinementDataRequestQuery_value (answer : PhysicalTableRequest M J target.length → ℚ) :
    let parentInitial := fun r => answer (PhysicalTableRequest.warmup pass copy node 0 r)
    let child := fun i r => (∑ j : Fin T, answer (PhysicalTableRequest.warmup pass copy
      (physicalChild node hbelow i) j.val r)) / T
    let initial := fun i r => answer (PhysicalTableRequest.warmup pass copy (physicalChild node hbelow i) 0 r)
    let children := fun i s r => answer (PhysicalTableRequest.refinement pass copy
      (physicalChild node hbelow i) T s r)
    (physicalRefinementDataRequestQuery source target N P F exponent H Q tau a eta kappa delta
      pass copy T S t ht node hbelow draw integer q).value (fun request => answer request.val) =
      rationalLocalWideStep source target (physicalSourceInterval source.length node)
        N P F exponent Q tau a delta parentInitial child initial
        (fun i r => children i (t - 1) r) (fun i r => children i t r) draw
        (localOnlineCandidates source target (physicalSourceInterval source.length node)
          N P F exponent H tau a eta kappa parentInitial child initial children (t - 1) integer q) q := by
  dsimp only
  let earlier := fun i s r => answer (PhysicalTableRequest.refinement pass copy (physicalChild node hbelow i) T s r)
  let masked := fun i s r => if s < t then earlier i s r else 0
  let parentInitial := fun r => answer (PhysicalTableRequest.warmup pass copy node 0 r)
  let child := fun i r => (∑ j : Fin T, answer (PhysicalTableRequest.warmup pass copy
    (physicalChild node hbelow i) j.val r)) / T
  let initial := fun i r => answer (PhysicalTableRequest.warmup pass copy (physicalChild node hbelow i) 0 r)
  have he (input : Fin M × ℕ × TargetInterval target.length) :
      (physicalRefinementEarlierQuery pass copy T S t node hbelow q input).value
        (fun request => answer request.val) = masked input.1 input.2.1 input.2.2 := by
    unfold physicalRefinementEarlierQuery
    split_ifs with hs
    · simp only [FiniteQuery.value, masked, ite_eq_left hs, earlier]
    · simp only [FiniteQuery.value, masked, ite_eq_right hs]
  rw [physicalRefinementDataRequestQuery,
    localRefinementDataQuery_value source target (physicalSourceInterval source.length node)
      N P F exponent H Q tau a eta kappa delta t _ _ _ draw integer q _ _ _
      parentInitial child initial masked (fun i r => earlier i t r) ht]
  · have hprev : (fun i r => masked i (t - 1) r) = fun i r => earlier i (t - 1) r := by
      funext i r
      exact ite_eq_left (by omega : t - 1 < t)
    have honline := localOnlineCandidates_congr_earlier_cover source target
      (physicalSourceInterval source.length node) N P F exponent H t tau a eta kappa
      parentInitial child initial masked earlier (t - 1) integer q (by omega)
      (fun i s r hr => ite_eq_left (wideEarlierInputCover_time _ P t _ (i, s, r) hr))
    rw [hprev, honline]
  · intro r
    rfl
  · intro input
    exact physicalRefinementMassQuery_value pass copy T S t ht node hbelow q input answer
  · intro input
    rfl
  · exact he
  · intro input
    rfl

end CompleteStep

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalGlobalQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The global query body. A seed read at pass zero evaluates the coarse
seed entry; every later pass reads the preceding pass's copy medians.
All warmup and refinement dependencies carry strict physical ranks. -/

namespace EditApproximation



section Program

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (N P F exponent H Q T S copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

def physicalGlobalQuery (request : PhysicalTableRequest M J target.length) :
    FiniteQuery {child : PhysicalTableRequest M J target.length //
      child.combinedRank T S < request.combinedRank T S} := by
  let seedRead := globalSeedRead N T S copies multiplier initial request
  by_cases hwarmup : request.index ≤ T
  · exact physicalWarmupRequestQuery source target N P F (factor request.pass)
      request.pass request.copy T S request.index request.node request.state seedRead
  · by_cases hbelow : request.node.1.val < J
    · by_cases hshort : (physicalSourceInterval source.length request.node).hi -
          (physicalSourceInterval source.length request.node).lo ≤ 1
      · exact physicalInitialQuery source target N P F (factor request.pass) seedRead
          (request.node, request.state)
      · have ht : 0 < request.index - T := by omega
        have hrequest : PhysicalTableRequest.refinement request.pass request.copy request.node
            T (request.index - T) request.state = request := by
          have hi : T + (request.index - T) = request.index := by omega
          unfold PhysicalTableRequest.refinement
          rw [hi]
        have program := physicalRefinementDataRequestQuery source target N P F exponent H Q
          tau (refinementFactor (factor request.pass) F) eta kappa delta
          request.pass request.copy T S (request.index - T) ht request.node hbelow
          (group request.pass request.copy ⟨request.node, hbelow⟩ (Fin.ofNat R (request.index - T - 1)))
          (integer request.pass request.copy ⟨request.node, hbelow⟩ (Fin.ofNat R (request.index - T - 1)))
          request.state
        exact FiniteQuery.mapKeys
          (fun child => ⟨child.val, by simpa only [hrequest] using child.property⟩) program
    · exact physicalInitialQuery source target N P F (factor request.pass) seedRead
        (request.node, request.state)

end Program

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalGlobalValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global query body computes the local pass recurrence on every seed and draw. -/

namespace EditApproximation

section Value

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (N P F exponent H Q T S copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

theorem physicalGlobalQuery_warmup (pass copy : ℕ) (node : PhysicalNode M J)
    (j : ℕ) (hj : j ≤ T) (q : TargetInterval target.length) :
    physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial (PhysicalTableRequest.warmup pass copy node j q) =
    physicalWarmupRequestQuery source target N P F (factor pass) pass copy T S j node q
      (globalSeedRead N T S copies multiplier initial (PhysicalTableRequest.warmup pass copy node j q)) := by
  unfold physicalGlobalQuery
  dsimp only
  erw [dite_eq_left (show (PhysicalTableRequest.warmup pass copy node j q).index ≤ T from hj)]
  rfl

theorem physicalGlobalQuery_refinement_value (request : PhysicalTableRequest M J target.length)
    (hindex : T < request.index) (hbelow : request.node.1.val < J)
    (hshort : ¬ (physicalSourceInterval source.length request.node).hi -
      (physicalSourceInterval source.length request.node).lo ≤ 1)
    (values : PhysicalTableRequest M J target.length → ℚ) :
    (physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request).value (fun child => values child.val) =
    (physicalRefinementDataRequestQuery source target N P F exponent H Q tau
      (refinementFactor (factor request.pass) F) eta kappa delta request.pass request.copy T S
      (request.index - T) (Nat.sub_pos_of_lt hindex) request.node hbelow
      (group request.pass request.copy ⟨request.node, hbelow⟩ (Fin.ofNat R (request.index - T - 1)))
      (integer request.pass request.copy ⟨request.node, hbelow⟩ (Fin.ofNat R (request.index - T - 1)))
      request.state).value (fun child => values child.val) := by
  unfold physicalGlobalQuery
  dsimp only
  erw [dite_eq_right (Nat.not_le.mpr hindex), dite_eq_left hbelow, dite_eq_right hshort]
  rw [FiniteQuery.mapKeys_value]
  rfl


theorem globalSeedRead_value (parent : PhysicalTableRequest M J target.length)
    (q : TargetInterval target.length) :
    (globalSeedRead N T S copies multiplier initial parent (parent.node, q)).value
      (fun child => localRequestValue source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial child.val) =
    (localSeedSequence source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial parent.pass (parent.node, q) : ℚ) := by
  by_cases hp : parent.pass = 0
  · rw [globalSeedRead, ite_eq_left rfl, dite_eq_left hp]
    change (initial (parent.node, q) : ℚ) = _
    rw [hp]
    rfl
  · simp only [globalSeedRead, ite_true, if_true, dite_eq_right hp]
    rw [physicalMedianSeedQuery_value]
    have hprev (copy : Fin copies) :
        previousPassRequest T S copy.val parent q =
          PhysicalTableRequest.refinement (parent.pass - 1) copy.val parent.node T S q := rfl
    simp only [hprev, localRequestValue_refinement]
    obtain ⟨pass, hpass⟩ := Nat.exists_eq_succ_of_ne_zero hp
    simp only [hpass, Nat.succ_eq_add_one, Nat.add_sub_cancel, localSeedSequence]

theorem localRequestValue_initial (pass copy : ℕ) (node : PhysicalNode M J)
    (q : TargetInterval target.length) :
    localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial (PhysicalTableRequest.warmup pass copy node 0 q) =
    stageInitial source target
      (localSeedSequence source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial pass) N P F (factor pass) (node, q) := by
  rw [localRequestValue_warmup source target N P F exponent H Q T S copies factor multiplier
    tau eta kappa delta group integer initial pass copy node 0 (Nat.zero_le T)]
  rfl

theorem localRequestValue_mass (pass copy : ℕ) (node : PhysicalNode M J)
    (q : TargetInterval target.length) :
    (∑ j : Fin T, localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial (PhysicalTableRequest.warmup pass copy node j.val q)) / T =
    physicalLocalWarmupMass source target
      (localSeedSequence source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial pass) N P F (factor pass) T (node, q) := by
  unfold physicalLocalWarmupMass
  rw [← Fin.sum_univ_eq_sum_range]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => localRequestValue_warmup source target N P F exponent H Q
    T S copies factor multiplier tau eta kappa delta group integer initial pass copy node j.val
      (Nat.le_of_lt j.isLt) q)


theorem localPassValue_step (seed : PhysicalEntry M J target.length → ℕ)
    (pass copy : ℕ) (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (hshort : ¬ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1)
    (t : ℕ) (ht : 0 < t) (q : TargetInterval target.length) :
    let children := fun i s r => localPassValue source target N P F exponent H Q T factor
      tau eta kappa delta group integer seed pass copy (physicalChild node hbelow i) s r
    localPassValue source target N P F exponent H Q T factor tau eta kappa delta group integer
      seed pass copy node t q =
    rationalLocalWideStep source target (physicalSourceInterval source.length node)
      N P F exponent Q tau (refinementFactor (factor pass) F) delta
      (fun r => stageInitial source target seed N P F (factor pass) (node, r))
      (physicalLocalChildMass source target seed N P F (factor pass) T node hbelow)
      (fun i r => stageInitial source target seed N P F (factor pass) (physicalChild node hbelow i, r))
      (fun i r => children i (t - 1) r) (fun i r => children i t r)
      (group pass copy ⟨node, hbelow⟩ (Fin.ofNat R (t - 1)))
      (localOnlineCandidates source target (physicalSourceInterval source.length node)
        N P F exponent H tau (refinementFactor (factor pass) F) eta kappa
        (fun r => stageInitial source target seed N P F (factor pass) (node, r))
        (physicalLocalChildMass source target seed N P F (factor pass) T node hbelow)
        (fun i r => stageInitial source target seed N P F (factor pass) (physicalChild node hbelow i, r))
        children (t - 1) (integer pass copy ⟨node, hbelow⟩ (Fin.ofNat R (t - 1))) q) q := by
  dsimp only
  cases t with
  | zero => omega
  | succ t =>
    unfold localPassValue
    rw [physicalLocalRefinement]
    simp only [dite_eq_left hbelow, ite_eq_right hshort, Nat.add_sub_cancel,
      physicalLocalOnline]
    rfl

theorem physicalRefinementDataRequestQuery_localValue (pass copy : ℕ) (node : PhysicalNode M J)
    (hbelow : node.1.val < J)
    (hshort : ¬ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1)
    (t : ℕ) (ht : 0 < t) (q : TargetInterval target.length) :
    (physicalRefinementDataRequestQuery source target N P F exponent H Q tau
      (refinementFactor (factor pass) F) eta kappa delta pass copy T S t ht node hbelow
      (group pass copy ⟨node, hbelow⟩ (Fin.ofNat R (t - 1)))
      (integer pass copy ⟨node, hbelow⟩ (Fin.ofNat R (t - 1))) q).value
        (fun child => localRequestValue source target N P F exponent H Q T S copies factor multiplier
          tau eta kappa delta group integer initial child.val) =
    localPassValue source target N P F exponent H Q T factor tau eta kappa delta group integer
      (localSeedSequence source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial pass) pass copy node t q := by
  rw [physicalRefinementDataRequestQuery_value]
  dsimp only
  simp_rw [localRequestValue_initial source target N P F exponent H Q T S copies factor multiplier
    tau eta kappa delta group integer initial,
    localRequestValue_mass source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial,
    localRequestValue_refinement source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial]
  exact (localPassValue_step source target N P F exponent H Q T factor tau eta kappa delta
    group integer _ pass copy node hbelow hshort t ht q).symm


theorem physicalGlobalQuery_value (request : PhysicalTableRequest M J target.length) :
    (physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request).value
        (fun child => localRequestValue source target N P F exponent H Q T S copies factor multiplier
          tau eta kappa delta group integer initial child.val) =
    localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request := by
  rcases request with ⟨pass, copy, node, index, q⟩
  by_cases hj : index ≤ T
  · change (physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial (PhysicalTableRequest.warmup pass copy node index q)).value _ = _
    rw [physicalGlobalQuery_warmup source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial pass copy node index hj q]
    change _ = localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial (PhysicalTableRequest.warmup pass copy node index q)
    rw [localRequestValue_warmup source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial pass copy node index hj q]
    apply physicalWarmupRequestQuery_value_local
    · intro r
      exact globalSeedRead_value source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial _ r
    · intro hbelow input
      exact localRequestValue_warmup source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial pass copy (physicalChild node hbelow input.1)
        (index - 1) (by omega) input.2
  · obtain ⟨t, hi⟩ : ∃ t, index = T + t := ⟨index - T, by omega⟩
    subst index
    have ht : 0 < t := by omega
    change (physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial (PhysicalTableRequest.refinement pass copy node T t q)).value _ =
      localRequestValue source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial (PhysicalTableRequest.refinement pass copy node T t q)
    rw [localRequestValue_refinement source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial pass copy node t q]
    by_cases hbelow : node.1.val < J
    · by_cases hshort : (physicalSourceInterval source.length node).hi -
          (physicalSourceInterval source.length node).lo ≤ 1
      · have hterminal : localPassValue source target N P F exponent H Q T factor tau eta kappa delta
            group integer (localSeedSequence source target N P F exponent H Q T S copies factor multiplier
              tau eta kappa delta group integer initial pass) pass copy node t q =
            stageInitial source target
              (localSeedSequence source target N P F exponent H Q T S copies factor multiplier
                tau eta kappa delta group integer initial pass) N P F (factor pass) (node, q) := by
          unfold localPassValue
          rw [physicalLocalRefinement, dite_eq_left hbelow, ite_eq_left hshort]
        rw [hterminal]
        unfold physicalGlobalQuery
        dsimp only
        erw [dite_eq_right (show ¬ (PhysicalTableRequest.refinement pass copy node T t q).index ≤ T
          from hj), dite_eq_left hbelow, dite_eq_left hshort]
        apply physicalInitialQuery_value_local
        intro r
        exact globalSeedRead_value source target N P F exponent H Q T S copies factor multiplier
          tau eta kappa delta group integer initial _ r
      · erw [physicalGlobalQuery_refinement_value source target N P F exponent H Q T S copies
          factor multiplier tau eta kappa delta group integer initial
          (PhysicalTableRequest.refinement pass copy node T t q) (by change T < T + t; omega)
          hbelow hshort]
        refine (physicalRefinementDataRequestQuery_localValue source target N P F exponent H Q T S copies
          factor multiplier tau eta kappa delta group integer initial pass copy node hbelow hshort
          (T + t - T) (by omega) q).trans ?_
        rw [Nat.add_sub_cancel_left]
    · have hterminal : localPassValue source target N P F exponent H Q T factor tau eta kappa delta
          group integer (localSeedSequence source target N P F exponent H Q T S copies factor multiplier
            tau eta kappa delta group integer initial pass) pass copy node t q =
          stageInitial source target
            (localSeedSequence source target N P F exponent H Q T S copies factor multiplier
              tau eta kappa delta group integer initial pass) N P F (factor pass) (node, q) := by
        unfold localPassValue
        rw [physicalLocalRefinement, dite_eq_right hbelow]
      rw [hterminal]
      unfold physicalGlobalQuery
      dsimp only
      erw [dite_eq_right (show ¬ (PhysicalTableRequest.refinement pass copy node T t q).index ≤ T
        from hj), dite_eq_right hbelow]
      apply physicalInitialQuery_value_local
      intro r
      exact globalSeedRead_value source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial _ r


end Value

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RefinementDataQueryWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Read counts for the full adaptive data query. Weighting reads permits
the same theorem to count current-index and earlier-index dependencies
separately. The bounds count executed readers, including repeated reads
across successive gathering stages. -/

namespace EditApproximation

section Keys

variable {ι α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (parentInitial : TargetInterval target.length → ℚ)
  (child initial : Fin M → TargetInterval target.length → ℚ)
  (readParent : TargetInterval target.length → FiniteQuery ι)
  (readMass readInitial : Fin M × TargetInterval target.length → FiniteQuery ι)
  (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
  (oracle : ι → ℚ) (predicate : ι → Prop)

theorem localRefinementStepQuery_keys_all
    (hearlier : ∀ input key, key ∈ (readEarlier input).keys oracle → predicate key)
    (hcurrent : ∀ input key, key ∈ (readCurrent input).keys oracle → predicate key) :
    ∀ key ∈ (localRefinementStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial draw integer q readEarlier readCurrent).keys oracle, predicate key := by
  unfold localRefinementStepQuery
  apply FiniteQuery.keys_all_collect
  · intro input _ key hk
    exact hearlier input key hk
  · intro earlierValues
    apply FiniteQuery.keys_all_collect
    · intro input _ key hk
      exact hcurrent input key hk
    · intro sharedValues
      apply FiniteQuery.keys_all_collect
      · intro input _ key hk
        exact hcurrent input key hk
      · intro currentValues key hk
        exact False.elim (List.not_mem_nil hk)

theorem localRefinementBandDataQuery_keys_all
    (hmass : ∀ input key, key ∈ (readMass input).keys oracle → predicate key)
    (hinitial : ∀ input key, key ∈ (readInitial input).keys oracle → predicate key)
    (hearlier : ∀ input key, key ∈ (readEarlier input).keys oracle → predicate key)
    (hcurrent : ∀ input key, key ∈ (readCurrent input).keys oracle → predicate key) :
    ∀ key ∈ (localRefinementBandDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial readMass readInitial draw integer q readEarlier readCurrent).keys oracle, predicate key := by
  unfold localRefinementBandDataQuery
  apply FiniteQuery.keys_all_collect
  · intro input _ key hk
    exact hmass input key hk
  · intro massValues
    apply FiniteQuery.keys_all_collect
    · intro input _ key hk
      exact hinitial input key hk
    · intro initialValues
      exact localRefinementStepQuery_keys_all source target parent N P F exponent H Q
        tau a eta kappa delta t parentInitial _ _ draw integer q readEarlier readCurrent
        oracle predicate hearlier hcurrent

theorem localRefinementDataQuery_keys_all
    (hparent : ∀ r key, key ∈ (readParent r).keys oracle → predicate key)
    (hmass : ∀ input key, key ∈ (readMass input).keys oracle → predicate key)
    (hinitial : ∀ input key, key ∈ (readInitial input).keys oracle → predicate key)
    (hearlier : ∀ input key, key ∈ (readEarlier input).keys oracle → predicate key)
    (hcurrent : ∀ input key, key ∈ (readCurrent input).keys oracle → predicate key) :
    ∀ key ∈ (localRefinementDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
      readParent readMass readInitial draw integer q readEarlier readCurrent).keys oracle, predicate key := by
  unfold localRefinementDataQuery
  rw [FiniteQuery.keys_bind]
  intro key hk
  rcases List.mem_append.mp hk with hfirst | hrest
  · exact hparent q key hfirst
  · apply FiniteQuery.keys_all_collect oracle predicate readParent
      (refinementInitialSupport N P F exponent a ((readParent q).value oracle) q) _ ?_ ?_ key hrest
    · intro r _ other ho
      exact hparent r other ho
    · intro initialValues
      exact localRefinementBandDataQuery_keys_all source target parent N P F exponent H Q
        tau a eta kappa delta t _ readMass readInitial draw integer q readEarlier readCurrent
        oracle predicate hmass hinitial hearlier hcurrent

end Keys

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRefinementReadWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Split the literal recursive reads by the unified table index. The
current-index reads are physical-child requests; initial data, warmup
mass and old history have strictly smaller indices. -/

namespace EditApproximation

theorem physicalRefinementWarmupRead_keys_bounded {M J ny : ℕ}
    (passes copies pass copy T S t : ℕ) (ht : 0 < t)
    (hpass : pass < passes) (hcopy : copy < copies)
    (node : PhysicalNode M J) (q : TargetInterval ny)
    (otherNode : PhysicalNode M J) (hnode : node.1.val ≤ otherNode.1.val)
    (j : ℕ) (hj : j ≤ T) (r : TargetInterval ny) (oracle) :
    ∀ key ∈ (physicalRefinementWarmupRead pass copy T S t ht node q otherNode hnode j hj r).keys oracle,
      key.val.Bounded passes copies T S := by
  intro key hk
  simp only [physicalRefinementWarmupRead, FiniteQuery.keys, List.mem_singleton] at hk
  subst key
  exact PhysicalTableRequest.warmup_bounded passes copies pass copy otherNode T S j r hpass hcopy hj

theorem physicalRefinementDataRequest_keys_bounded {α : Type*} (source target : List α) {M J : ℕ}
    (N P F exponent H Q : ℕ) (tau a eta kappa delta : ℚ)
    (passes copies pass copy T S t : ℕ) (ht : 0 < t) (htS : t ≤ S)
    (hpass : pass < passes) (hcopy : copy < copies)
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
    (q : TargetInterval target.length) (oracle) :
    ∀ key ∈ (physicalRefinementDataRequestQuery source target N P F exponent H Q tau a eta kappa delta
      pass copy T S t ht node hbelow draw integer q).keys oracle,
      key.val.Bounded passes copies T S := by
  unfold physicalRefinementDataRequestQuery
  apply localRefinementDataQuery_keys_all
  · intro r key hk
    exact physicalRefinementWarmupRead_keys_bounded passes copies pass copy T S t ht hpass hcopy
      node q node le_rfl 0 (Nat.zero_le T) r oracle key hk
  · intro input
    unfold physicalRefinementMassQuery
    apply FiniteQuery.keys_all_collect
    · intro j _ key hk
      exact physicalRefinementWarmupRead_keys_bounded passes copies pass copy T S t ht hpass hcopy
        node q (physicalChild node hbelow input.1) _ j.val (Nat.le_of_lt j.isLt) input.2 oracle key hk
    · intro values key hk
      exact False.elim (List.not_mem_nil hk)
  · intro input key hk
    exact physicalRefinementWarmupRead_keys_bounded passes copies pass copy T S t ht hpass hcopy
      node q (physicalChild node hbelow input.1) _ 0 (Nat.zero_le T) input.2 oracle key hk
  · intro input key hk
    unfold physicalRefinementEarlierQuery at hk
    split_ifs at hk with hs
    · simp only [FiniteQuery.keys, List.mem_singleton] at hk
      subst key
      exact PhysicalTableRequest.refinement_bounded passes copies pass copy
        (physicalChild node hbelow input.1) T S input.2.1 input.2.2 hpass hcopy (by omega)
    · exact False.elim (List.not_mem_nil hk)
  · intro input key hk
    simp only [physicalRefinementCurrentQuery, FiniteQuery.keys, List.mem_singleton] at hk
    subst key
    exact PhysicalTableRequest.refinement_bounded passes copies pass copy
      (physicalChild node hbelow input.1) T S t input.2 hpass hcopy htS

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalBoundedQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual global read program stays within the bounded cache-key
domain. Restricting its type therefore preserves the complete local-pass
value and gives an injectively encoded memo evaluator. -/

namespace EditApproximation

instance PhysicalTableRequest.decidableBounded {M J ny : ℕ} (passes copies T S : ℕ) :
    DecidablePred (PhysicalTableRequest.Bounded (M := M) (J := J) (ny := ny) passes copies T S) :=
  fun request => inferInstanceAs (Decidable
    (request.pass < passes ∧ request.copy < copies ∧ request.index ≤ T + S))

theorem globalSeedRead_keys_bounded {M J ny : ℕ} (N T S passes copies : ℕ)
    (multiplier : ℕ → ℕ) (initial : PhysicalEntry M J ny → ℕ)
    (parent : PhysicalTableRequest M J ny) (hparent : parent.Bounded passes copies T S)
    (state : PhysicalEntry M J ny) (oracle) :
    ∀ key ∈ (globalSeedRead N T S copies multiplier initial parent state).keys oracle,
      key.val.Bounded passes copies T S := by
  unfold globalSeedRead
  split_ifs with hnode hpass
  · intro key hk
    exact False.elim (List.not_mem_nil hk)
  · unfold physicalMedianSeedQuery
    apply FiniteQuery.keys_all_collect
    · intro copy _ key hk
      simp only [previousPassRead, FiniteQuery.keys, List.mem_singleton] at hk
      subst key
      exact ⟨Nat.lt_of_le_of_lt (Nat.sub_le _ _) hparent.1, copy.isLt, le_rfl⟩
    · intro values key hk
      exact False.elim (List.not_mem_nil hk)
  · intro key hk
    exact False.elim (List.not_mem_nil hk)

section Bounded

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

theorem physicalGlobalQuery_keys_bounded (request : PhysicalTableRequest M J target.length)
    (hrequest : request.Bounded passes copies T S) (oracle) :
    ∀ key ∈ (physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request).keys oracle,
      key.val.Bounded passes copies T S := by
  rcases request with ⟨pass, copy, node, index, q⟩
  obtain ⟨hpass, hcopy, hindex⟩ := hrequest
  dsimp only at hpass hcopy hindex
  by_cases hj : index ≤ T
  · change ∀ key ∈ (physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial (PhysicalTableRequest.warmup pass copy node index q)).keys oracle,
        key.val.Bounded passes copies T S
    rw [physicalGlobalQuery_warmup source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial pass copy node index hj q]
    apply physicalWarmupRequestQuery_keys_bounded source target N P F (factor pass)
      passes copies pass copy T S index hpass hcopy hj node q _ oracle
    intro r key hk
    exact globalSeedRead_keys_bounded N T S passes copies multiplier initial _
      ⟨hpass, hcopy, hindex⟩ _ oracle key hk
  · obtain ⟨t, hi⟩ : ∃ t, index = T + t := ⟨index - T, by omega⟩
    subst index
    have ht : 0 < t := by omega
    have htS : t ≤ S := by omega
    change ∀ key ∈ (physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial (PhysicalTableRequest.refinement pass copy node T t q)).keys oracle,
        key.val.Bounded passes copies T S
    by_cases hbelow : node.1.val < J
    · by_cases hshort : (physicalSourceInterval source.length node).hi -
          (physicalSourceInterval source.length node).lo ≤ 1
      · unfold physicalGlobalQuery
        dsimp only
        erw [dite_eq_right (show ¬ (PhysicalTableRequest.refinement pass copy node T t q).index ≤ T
          from hj), dite_eq_left hbelow, dite_eq_left hshort]
        apply physicalInitialQuery_keys_all
        intro r key hk
        exact globalSeedRead_keys_bounded N T S passes copies multiplier initial _
          ⟨hpass, hcopy, hindex⟩ _ oracle key hk
      · unfold physicalGlobalQuery
        dsimp only
        erw [dite_eq_right (show ¬ (PhysicalTableRequest.refinement pass copy node T t q).index ≤ T
          from hj), dite_eq_left hbelow, dite_eq_right hshort]
        erw [FiniteQuery.mapKeys_keys]
        intro key hk
        obtain ⟨child, hc, rfl⟩ := List.mem_map.mp hk
        exact physicalRefinementDataRequest_keys_bounded source target N P F exponent H Q tau
          (refinementFactor (factor pass) F) eta kappa delta passes copies pass copy T S
          (T + t - T) (by omega) (by omega) hpass hcopy node hbelow _ _ q _ child hc
    · unfold physicalGlobalQuery
      dsimp only
      erw [dite_eq_right (show ¬ (PhysicalTableRequest.refinement pass copy node T t q).index ≤ T
        from hj), dite_eq_right hbelow]
      apply physicalInitialQuery_keys_all
      intro r key hk
      exact globalSeedRead_keys_bounded N T S passes copies multiplier initial _
        ⟨hpass, hcopy, hindex⟩ _ oracle key hk

def physicalBoundedQuery
    (request : {request : PhysicalTableRequest M J target.length // request.Bounded passes copies T S}) :
    FiniteQuery {child : {child : PhysicalTableRequest M J target.length // child.Bounded passes copies T S} //
      child.val.combinedRank T S < request.val.combinedRank T S} :=
  restrictRankedProgram (PhysicalTableRequest.combinedRank T S)
    (physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial) (PhysicalTableRequest.Bounded passes copies T S) request

end Bounded

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedGlobalQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The global lazy program exposes coarse entries as ordinary memo requests.
Warmup uses these explicit seed reads; positive internal refinement uses the
proved finite table query, whose data reads are all earlier table entries. -/

namespace EditApproximation





section Global

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

def chargedRequestValue : ChargedPhysicalRequest M J target.length passes copies T S → ℚ
  | .inl entry => initial entry
  | .inr request => localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request.val

theorem chargedSeedQuery_localValue
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
    (q : TargetInterval target.length) :
    (chargedSeedQuery N multiplier parent (parent.val.node, q)).value
      (fun child => chargedRequestValue source target N P F exponent H Q T S passes copies
        factor multiplier tau eta kappa delta group integer initial child.val) =
    (localSeedSequence source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial parent.val.pass (parent.val.node, q) : ℚ) := by
  rw [chargedSeedQuery_value]
  by_cases hp : parent.val.pass = 0
  · rw [ite_eq_left hp, hp]
    rfl
  · rw [ite_eq_right hp]
    simp only [chargedRequestValue, chargedPreviousPass]
    have hprev (copy : Fin copies) : previousPassRequest T S copy.val parent.val q =
        PhysicalTableRequest.refinement (parent.val.pass - 1) copy.val parent.val.node T S q := rfl
    simp only [hprev, localRequestValue_refinement]
    obtain ⟨pass, heq⟩ := Nat.exists_eq_succ_of_ne_zero hp
    simp only [heq, Nat.succ_eq_add_one, Nat.add_sub_cancel, localSeedSequence]

theorem chargedWarmupQuery_value
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
    (hindex : parent.val.index ≤ T) :
    (chargedWarmupQuery source target N P F factor multiplier parent).value
      (fun child => chargedRequestValue source target N P F exponent H Q T S passes copies
        factor multiplier tau eta kappa delta group integer initial child.val) =
    localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial parent.val := by
  have hreq : PhysicalTableRequest.warmup parent.val.pass parent.val.copy parent.val.node
      parent.val.index parent.val.state = parent.val := rfl
  rw [← hreq, localRequestValue_warmup source target N P F exponent H Q T S copies factor multiplier
    tau eta kappa delta group integer initial _ _ _ _ hindex]
  change (chargedWarmupQuery source target N P F factor multiplier parent).value _ = _
  have hseed := chargedSeedQuery_localValue source target N P F exponent H Q T S passes copies
    factor multiplier tau eta kappa delta group integer initial parent
  unfold chargedWarmupQuery
  split_ifs with hz hbelow hshort
  · rw [hz]
    exact physicalInitialQuery_value_local source target N P F _ _ _ _ _ _ hseed
  · rw [physicalLocalWarmup_terminal _ _ _ _ _ _ _ _ _ _ (Or.inr hshort)]
    exact physicalInitialQuery_value_local source target N P F _ _ _ _ _ _ hseed
  · have hi : parent.val.index = (parent.val.index - 1) + 1 := by omega
    conv_rhs => rw [hi]
    apply physicalWarmupStepQuery_value_local source target N P F _ _ _ _ _
      parent.val.node hbelow hshort (parent.val.index - 1) parent.val.state hseed
    intro input
    change localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial
      (PhysicalTableRequest.warmup parent.val.pass parent.val.copy
        (physicalChild parent.val.node hbelow input.1) (parent.val.index - 1) input.2) = _
    exact localRequestValue_warmup source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial _ _ _ _ (by omega) _
  · rw [physicalLocalWarmup_terminal _ _ _ _ _ _ _ _ _ _ (Or.inl hbelow)]
    exact physicalInitialQuery_value_local source target N P F _ _ _ _ _ _ hseed

def chargedGlobalQuery (request : ChargedPhysicalRequest M J target.length passes copies T S) :
    FiniteQuery {child : ChargedPhysicalRequest M J target.length passes copies T S //
      child.rank < request.rank} :=
  match request with
  | .inl entry => .done (initial entry)
  | .inr parent =>
    if parent.val.index ≤ T then chargedWarmupQuery source target N P F factor multiplier parent
    else if parent.val.node.1.val < J then
      if (physicalSourceInterval source.length parent.val.node).hi -
          (physicalSourceInterval source.length parent.val.node).lo ≤ 1 then
        physicalInitialQuery source target N P F (factor parent.val.pass)
          (chargedSeedQuery N multiplier parent) (parent.val.node, parent.val.state)
      else FiniteQuery.mapKeys (fun child =>
        ⟨Sum.inr child.val, ChargedPhysicalRequest.table_rank_lt parent child.val child.property⟩)
        (physicalBoundedQuery source target N P F exponent H Q T S passes copies factor multiplier
          tau eta kappa delta group integer initial parent)
    else physicalInitialQuery source target N P F (factor parent.val.pass)
      (chargedSeedQuery N multiplier parent) (parent.val.node, parent.val.state)


theorem localRequestValue_terminal (request : PhysicalTableRequest M J target.length)
    (hterminal : ¬ request.node.1.val < J ∨
      (physicalSourceInterval source.length request.node).hi -
        (physicalSourceInterval source.length request.node).lo ≤ 1) :
    localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request =
    stageInitial source target
      (localSeedSequence source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial request.pass)
      N P F (factor request.pass) (request.node, request.state) := by
  unfold localRequestValue unifiedPhysicalValue
  dsimp only
  split_ifs
  · exact physicalLocalWarmup_terminal _ _ _ _ _ _ _ _ _ _ hterminal
  · rw [physicalLocalRefinement]
    rcases hterminal with hd | hw
    · rw [dite_eq_right hd]
    · split_ifs <;> rfl

def chargedMemoEvaluate (request : ChargedPhysicalRequest M J target.length passes copies T S) :=
  rankedMemoEvaluate ChargedPhysicalRequest.rank
    (chargedGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial)
    (ChargedPhysicalRequest.bits M J target.length passes copies T S)
    ChargedPhysicalRequest.code request .empty

end Global

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalOnlineKeys
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Online random streams have bounded physical keys. The embedding of
the complete representative table is used only in the proof of the law;
the local program requests the scale and rounded center directly. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory





section Keys

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ)

def physicalLocalOnlineBandG (T exponent H : ℕ) (tau : ℚ)
    (key : PhysicalLocalOnlineKey M J N target.length) : ℕ :=
  keyedOnlineBandG source target (physicalSourceInterval source.length key.1.1)
    P exponent H ((dyadicScales N).get key.2.1) tau
    (physicalLocalChildMass source target U N P F A T key.1.1 key.1.2) key.2.2

theorem physicalLocalOnlineBandG_positive (T exponent H : ℕ) (tau : ℚ)
    (key : PhysicalLocalOnlineKey M J N target.length) :
    0 < physicalLocalOnlineBandG source target U N P F A T exponent H tau key :=
  keyedOnlineBandG_positive _ _ _ _ _ _ _ _ _ _

def physicalLocalOnlineMass (T exponent H : ℕ) (tau : ℚ)
    (key : PhysicalLocalOnlineKey M J N target.length) : ℕ :=
  optimizerTriangularMass
    (physicalLocalOnlineBandG source target U N P F A T exponent H tau key ^ 80)

instance physicalLocalOnlineMass_nezero (T exponent H : ℕ) (tau : ℚ)
    (key : PhysicalLocalOnlineKey M J N target.length) :
    NeZero (physicalLocalOnlineMass source target U N P F A T exponent H tau key) :=
  ⟨Nat.ne_of_gt (optimizerTriangularMass_positive _
    (pow_pos (physicalLocalOnlineBandG_positive source target U N P F A T exponent H tau key) 80))⟩

abbrev PhysicalLocalOnlineDraw (R T exponent H : ℕ) (tau : ℚ) :=
  ∀ key : PhysicalLocalOnlineKey M J N target.length,
    Fin R → Fin (physicalLocalOnlineMass source target U N P F A T exponent H tau key)

end Keys

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalOnlineMassBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A single finite source range bounds every actual local online sampler,
independently of the incoming seed and queried state. -/

namespace EditApproximation

theorem keyedOnlineBandG_le {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P exponent H b : ℕ) (hP : 0 < P) (tau : ℚ)
    (child : Fin M → TargetInterval target.length → ℚ) (r : TargetInterval target.length) :
    keyedOnlineBandG source target parent P exponent H b tau child r ≤
      H + M * (40 * P + 2) ^ 2 + 2 := by
  have hdimension := bandCoordinates_card_le parent r hP
    (representativeBandActions source target parent r b P tau ((2 : ℚ) ^ (-(exponent : ℤ))) child)
    (fun action ha => representativeBandActions_wide source target parent r b P tau _ child action ha)
  exact Nat.add_le_add_right (Nat.add_le_add_left hdimension H) 2



theorem physicalLocalOnlineMass_le {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T exponent H : ℕ) (tau : ℚ) (hP : 0 < P)
    (key : PhysicalLocalOnlineKey M J N target.length) :
    physicalLocalOnlineMass source target U N P F A T exponent H tau key ≤ localOnlineMassBound M P H := by
  apply optimizerTriangularMass_monotone
  exact Nat.pow_le_pow_left (keyedOnlineBandG_le source target _ P exponent H _ hP tau _ _) 80

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalQueryProgress
attribute [-instance] _root_.OAI.EditApproximation.PhysicalTableRequest.decidableBounded _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dependency split for keys actually emitted by the adaptive local
queries. Current-index edges descend in the physical tree; older reads
decrease the table rank and never move to an ancestor. -/

namespace EditApproximation

namespace PhysicalTableRequest

theorem warmup_before_refinement_progress {M J ny : ℕ}
    (pass copy T S t : ℕ) (ht : 0 < t)
    (node otherNode : PhysicalNode M J) (hnode : node.1.val ≤ otherNode.1.val)
    (j : ℕ) (hj : j ≤ T) (q r : TargetInterval ny) :
    DependencyProgress T S (refinement pass copy node T t q)
      (warmup pass copy otherNode j r) := by
  apply Or.inr
  refine ⟨remainingDepth_le_of_no_ancestor _ _ hnode, ?_⟩
  exact rank_lt_same_pass T S _ _ rfl (by change j < T + t; omega)

theorem refinement_child_same_progress {M J ny : ℕ}
    (pass copy T S t : ℕ) (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (i : Fin M) (q r : TargetInterval ny) :
    DependencyProgress T S (refinement pass copy node T t q)
      (refinement pass copy (physicalChild node hbelow i) T t r) := by
  apply Or.inl
  refine ⟨?_, le_rfl⟩
  apply remainingDepth_lt_of_descendant
  change node.1.val < node.1.val + 1
  omega

theorem refinement_child_earlier_progress {M J ny : ℕ}
    (pass copy T S t s : ℕ) (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (i : Fin M) (q r : TargetInterval ny) (hs : s < t) :
    DependencyProgress T S (refinement pass copy node T t q)
      (refinement pass copy (physicalChild node hbelow i) T s r) := by
  obtain ⟨hd, hr⟩ := refinement_history_child_progress pass copy T S t s node hbelow i q r hs
  exact Or.inr ⟨hd.le, hr⟩

end PhysicalTableRequest

theorem physicalRefinementWarmupRead_keys_progress {M J ny : ℕ}
    (pass copy T S t : ℕ) (ht : 0 < t) (node : PhysicalNode M J) (q : TargetInterval ny)
    (otherNode : PhysicalNode M J) (hnode : node.1.val ≤ otherNode.1.val)
    (j : ℕ) (hj : j ≤ T) (r : TargetInterval ny) (oracle) :
    ∀ key ∈ (physicalRefinementWarmupRead pass copy T S t ht node q otherNode hnode j hj r).keys oracle,
      PhysicalTableRequest.DependencyProgress T S
        (PhysicalTableRequest.refinement pass copy node T t q) key.val := by
  intro key hk
  simp only [physicalRefinementWarmupRead, FiniteQuery.keys, List.mem_singleton] at hk
  subst key
  exact PhysicalTableRequest.warmup_before_refinement_progress pass copy T S t ht
    node otherNode hnode j hj q r

theorem physicalRefinementDataRequest_keys_progress {α : Type*} (source target : List α) {M J : ℕ}
    (N P F exponent H Q : ℕ) (tau a eta kappa delta : ℚ)
    (pass copy T S t : ℕ) (ht : 0 < t)
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
    (q : TargetInterval target.length) (oracle) :
    ∀ key ∈ (physicalRefinementDataRequestQuery source target N P F exponent H Q tau a eta kappa delta
      pass copy T S t ht node hbelow draw integer q).keys oracle,
      PhysicalTableRequest.DependencyProgress T S
        (PhysicalTableRequest.refinement pass copy node T t q) key.val := by
  unfold physicalRefinementDataRequestQuery
  apply localRefinementDataQuery_keys_all
  · intro r key hk
    exact physicalRefinementWarmupRead_keys_progress pass copy T S t ht node q node le_rfl
      0 (Nat.zero_le T) r oracle key hk
  · intro input
    unfold physicalRefinementMassQuery
    apply FiniteQuery.keys_all_collect
    · intro j _ key hk
      exact physicalRefinementWarmupRead_keys_progress pass copy T S t ht node q
        (physicalChild node hbelow input.1) _ j.val (Nat.le_of_lt j.isLt) input.2 oracle key hk
    · intro values key hk
      exact False.elim (List.not_mem_nil hk)
  · intro input key hk
    exact physicalRefinementWarmupRead_keys_progress pass copy T S t ht node q
      (physicalChild node hbelow input.1) _ 0 (Nat.zero_le T) input.2 oracle key hk
  · intro input key hk
    unfold physicalRefinementEarlierQuery at hk
    split_ifs at hk with hs
    · simp only [FiniteQuery.keys, List.mem_singleton] at hk
      subst key
      exact PhysicalTableRequest.refinement_child_earlier_progress pass copy T S t input.2.1
        node hbelow input.1 q input.2.2 hs
    · exact False.elim (List.not_mem_nil hk)
  · intro input key hk
    simp only [physicalRefinementCurrentQuery, FiniteQuery.keys, List.mem_singleton] at hk
    subst key
    exact PhysicalTableRequest.refinement_child_same_progress pass copy T S t node hbelow input.1 q input.2

theorem physicalWarmupRequestQuery_keys_progress {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (N P F : ℕ) (A : ℚ)
    (pass copy T S j : ℕ) (node : PhysicalNode M J) (q : TargetInterval target.length)
    (seedRead : PhysicalEntry M J target.length →
      FiniteQuery {child : PhysicalTableRequest M J target.length //
        child.combinedRank T S < (PhysicalTableRequest.warmup pass copy node j q).combinedRank T S})
    (oracle)
    (hseed : ∀ r key, key ∈ (seedRead (node, r)).keys oracle →
      PhysicalTableRequest.DependencyProgress T S
        (PhysicalTableRequest.warmup pass copy node j q) key.val) :
    ∀ key ∈ (physicalWarmupRequestQuery source target N P F A pass copy T S j node q seedRead).keys oracle,
      PhysicalTableRequest.DependencyProgress T S
        (PhysicalTableRequest.warmup pass copy node j q) key.val := by
  cases j with
  | zero => exact physicalInitialQuery_keys_all source target N P F A seedRead node q oracle _ hseed
  | succ j =>
    apply physicalWarmupRequestQuery_keys_all source target N P F A pass copy T S (j + 1) node q
      seedRead oracle _ hseed
    intro hbelow input
    obtain ⟨hd, hr⟩ := PhysicalTableRequest.warmup_previous_child_progress pass copy T S (j + 1)
      node hbelow input.1 q input.2 (Nat.succ_pos j)
    exact Or.inr ⟨hd.le, hr⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalGroupKeys
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Every whole-cell stream used by the complete program has a bounded
physical key. Its two cell coordinates are at most n*2^exponent. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

abbrev PhysicalLocalGroupArray (M J N n exponent F Q R : ℕ)
    (key : PhysicalLocalGroupKey M J N n exponent) :=
  Fin R → ParentGroupDraw M (groupDyadicScales M ((dyadicScales N).get key.2.1) F).length
    (fun h => groupSampleCount M Q ((dyadicScales N).get key.2.1)
      (groupDyadicScaleAt M ((dyadicScales N).get key.2.1) F h))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalProgramLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single bounded-key product supplies both online and whole-cell
streams. Restriction to the complete program preserves their joint law,
including independence between the two kinds of stream. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Law

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T exponent H Q : ℕ) (tau : ℚ)

abbrev PhysicalLocalProgramCoordinate
    (key : PhysicalLocalProgramKey M J N target.length exponent) : Type :=
  match key with
  | .inl online => Fin R → Fin (physicalLocalOnlineMass source target U N P F A T exponent H tau online)
  | .inr group => PhysicalLocalGroupArray M J N target.length exponent F Q R group

abbrev PhysicalLocalProgramDraw := ∀ key : PhysicalLocalProgramKey M J N target.length exponent,
  PhysicalLocalProgramCoordinate (R := R) source target U N P F A T exponent H Q tau key

end Law

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalCommonSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The actual bounded physical program can share one source universe
across incoming seed tables. Online coordinates include their requested
range; group coordinates share whole-cell arrays. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory



abbrev PhysicalCommonCoordinate (M J N n exponent F Q R B : ℕ)
    (key : PhysicalCommonKey M J N n exponent B) : Type :=
  match key with
  | .inl online => Fin R → Fin online.2.val.val
  | .inr group => PhysicalLocalGroupArray M J N n exponent F Q R group

section Source

variable (M J N n exponent F Q R B : ℕ)
  [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]

abbrev PhysicalCommonDraw := ∀ key : PhysicalCommonKey M J N n exponent B,
  PhysicalCommonCoordinate M J N n exponent F Q R B key

end Source

section Selection

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T exponent H Q R B : ℕ) (tau : ℚ)
  (hbound : ∀ key, physicalLocalOnlineMass source target U N P F A T exponent H tau key ≤ B)

omit [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem physicalCommonMass_positive (key : PhysicalLocalOnlineKey M J N target.length) :
    0 < physicalLocalOnlineMass source target U N P F A T exponent H tau key :=
  optimizerTriangularMass_positive _
    (pow_pos (physicalLocalOnlineBandG_positive source target U N P F A T exponent H tau key) 80)

def physicalCommonSelectedOnlineKey (online : PhysicalLocalOnlineKey M J N target.length) :
    CommonRangeKey (PhysicalLocalOnlineKey M J N target.length) B :=
  (online, positiveDrawRangeOfLE B
    (physicalLocalOnlineMass source target U N P F A T exponent H tau online)
    (physicalCommonMass_positive source target U N P F A T exponent H tau online) (hbound online))

def physicalCommonSelectedKey (key : PhysicalLocalProgramKey M J N target.length exponent) :
    PhysicalCommonKey M J N target.length exponent B :=
  match key with
  | .inl online => .inl (physicalCommonSelectedOnlineKey source target U N P F A T exponent H B tau hbound online)
  | .inr group => .inr group

omit [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem physicalCommonSelectedOnlineKey_range (online : PhysicalLocalOnlineKey M J N target.length) :
    (physicalCommonSelectedOnlineKey source target U N P F A T exponent H B tau hbound online).2.val.val =
      physicalLocalOnlineMass source target U N P F A T exponent H tau online := by
  exact positiveDrawRangeOfLE_val B _
    (physicalCommonMass_positive source target U N P F A T exponent H tau online) (hbound online)

def physicalCommonCoordinateImage (key : PhysicalLocalProgramKey M J N target.length exponent) :
    PhysicalCommonCoordinate M J N target.length exponent F Q R B
        (physicalCommonSelectedKey source target U N P F A T exponent H B tau hbound key) →
      PhysicalLocalProgramCoordinate (R := R) source target U N P F A T exponent H Q tau key :=
  match key with
  | .inl online => fun array time => Fin.cast
      (physicalCommonSelectedOnlineKey_range source target U N P F A T exponent H B tau hbound online)
      (array time)
  | .inr _ => id

def physicalCommonSample
    (draw : PhysicalCommonDraw M J N target.length exponent F Q R B) :
    PhysicalLocalProgramDraw (R := R) source target U N P F A T exponent H Q tau :=
  fun key => physicalCommonCoordinateImage source target U N P F A T exponent H Q R B tau hbound key
    (draw (physicalCommonSelectedKey source target U N P F A T exponent H B tau hbound key))

end Selection

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalScalarSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Each common array source is realized by scalar exact uniform draws.
Regrouping finite coordinates recovers the common source law; unused
coordinates belong only to the probability space. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

def physicalScalarCoordinatePack (M J N n exponent F Q R B : ℕ)
    (key : PhysicalCommonKey M J N n exponent B)
    (draw : ∀ index : PhysicalScalarIndex M J N n exponent F Q R B key,
      Fin (physicalScalarRange M J N n exponent F Q R B ⟨key, index⟩)) :
    PhysicalCommonCoordinate M J N n exponent F Q R B key :=
  match key with
  | .inl _ => draw
  | .inr _ => fun time scale sample => draw ⟨time, scale, sample⟩

def physicalScalarPack (M J N n exponent F Q R B : ℕ)
    (draw : PhysicalScalarDraw M J N n exponent F Q R B) :
    PhysicalCommonDraw M J N n exponent F Q R B :=
  fun key => physicalScalarCoordinatePack M J N n exponent F Q R B key (fun index => draw ⟨key, index⟩)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRawGroupProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Whole-cell draws are read by their bounded scale and endpoint keys.
No list of all representatives or cells is searched by the provider. -/

namespace EditApproximation

section Raw

variable (M J N n exponent F Q R : ℕ) [NeZero M]
  (draw : ∀ key : PhysicalLocalGroupKey M J N n exponent,
    PhysicalLocalGroupArray M J N n exponent F Q R key)

def physicalRawGroupDraws (node : PhysicalInternalNode M J) (time : Fin R) :
    CellGroupDraws M F Q :=
  fun b cell =>
    if hb : b ∈ dyadicScales N then
      if hc : cell.1 ≤ n * 2 ^ exponent ∧ cell.2 ≤ n * 2 ^ exponent then
        let key : PhysicalLocalGroupKey M J N n exponent :=
          (node, physicalScaleIndex N b hb,
            ⟨cell.1, Nat.lt_succ_of_le hc.1⟩, ⟨cell.2, Nat.lt_succ_of_le hc.2⟩)
        Eq.mp (congrArg (fun b => ParentGroupDraw M (groupDyadicScales M b F).length
          (fun h => groupSampleCount M Q b (groupDyadicScaleAt M b F h)))
          (physicalScaleIndex_get N b hb)) (draw key time)
      else fun _ _ => 0
    else fun _ _ => 0

end Raw

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRawOnlineProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local online provider reads a scale/center key directly; the
complete representative index identifies the corresponding action. -/

namespace EditApproximation

theorem localOnlineCandidates_integer_congr {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H : ℕ) (tau a eta kappa : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (children : PhysicalChildTables M target.length) (t : ℕ)
    (left right : ℕ → TargetInterval target.length → ℕ) (q : TargetInterval target.length)
    (hequal : ∀ b ∈ dyadicQueryWindow N (parentInitial q) a F,
      (b, roundInterval (seedGridSpacing b P) q) ∈ representativeList N P F a parentInitial →
      left b (roundInterval (seedGridSpacing b P) q) = right b (roundInterval (seedGridSpacing b P) q)) :
    localOnlineCandidates source target parent N P F exponent H tau a eta kappa
      parentInitial child initial children t left q =
    localOnlineCandidates source target parent N P F exponent H tau a eta kappa
      parentInitial child initial children t right q := by
  unfold localOnlineCandidates
  apply List.filterMap_congr
  intro b hb
  dsimp only
  split_ifs with heligible
  · have hrep := representativeList_mem a parentInitial _ (List.mem_filter.mp hb).1
      (roundInterval_on_grid _ q) heligible.1 heligible.2
    rw [hequal b hb hrep]
  · rfl

section Program

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T exponent H : ℕ) (tau eta kappa : ℚ)
  (draw : PhysicalLocalOnlineDraw source target U N P F A R T exponent H tau)

def physicalRawOnlineIntegers (node : PhysicalInternalNode M J) (time : Fin R)
    (b : ℕ) (r : TargetInterval target.length) : ℕ :=
  if hb : b ∈ dyadicScales N then
    (draw (node, physicalScaleIndex N b hb, r) time).val
  else 0

end Program

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalJointProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Direct evaluation from the bounded joint random source agrees with
complete refinement. All complete-table indexing occurs in the proof. -/

namespace EditApproximation

section Joint

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T exponent H Q : ℕ) (tau eta kappa delta : ℚ)
  (draw : PhysicalLocalProgramDraw (R := R) source target U N P F A T exponent H Q tau)

def physicalLocalJointValue (node : PhysicalNode M J) (t : ℕ)
    (q : TargetInterval target.length) : ℚ :=
  physicalLocalRefinement source target U N P F exponent Q A tau delta T
    (fun label s => physicalRawGroupDraws M J N target.length exponent F Q R
      (fun key => draw (.inr key)) label (Fin.ofNat R (s - 1)))
    (physicalLocalOnline source target U N P F exponent H T A tau eta kappa
      (physicalRawOnlineIntegers source target U N P F A T exponent H tau
        (fun key => draw (.inl key)))) node t q

end Joint

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalOnlineSourceQuery
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Online ranges are computed from already gathered band data. The
following query reads only the scale/center pairs for the current entry,
then evaluates the existing local step with the returned integers. -/

namespace EditApproximation



theorem localOnlineSourceKeys_mem {n : ℕ} (N P F : ℕ) (a : ℚ)
    (initial : TargetInterval n → ℚ) (q : TargetInterval n) (b : ℕ)
    (hb : b ∈ dyadicQueryWindow N (initial q) a F) :
    (b, roundInterval (seedGridSpacing b P) q) ∈ localOnlineSourceKeys N P F a initial q :=
  List.mem_map.mpr ⟨b, hb, rfl⟩



theorem keyedOnlineSourceRange_congr {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P exponent H : ℕ) (tau : ℚ)
    (child child' : Fin M → TargetInterval target.length → ℚ) (key : ℕ × TargetInterval target.length)
    (h : ∀ action ∈ wideActionList M parent key.2 key.1 P,
      ∀ i, child i (action i) = child' i (action i)) :
    keyedOnlineSourceRange source target parent P exponent H tau child key =
      keyedOnlineSourceRange source target parent P exponent H tau child' key := by
  unfold keyedOnlineSourceRange keyedOnlineBandG
  rw [representativeBandActions_congr_child source target parent key.2 key.1 P tau
    ((2 : ℚ) ^ (-(exponent : ℤ))) child child' h]

theorem keyedOnlineSourceRange_gathered {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H : ℕ) (tau a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child : Fin M → TargetInterval target.length → ℚ) (q : TargetInterval target.length)
    (b : ℕ) (hb : b ∈ dyadicQueryWindow N (parentInitial q) a F) :
    let keys := refinementBandInputList (M := M) parent N P F exponent a parentInitial q
    keyedOnlineSourceRange source target parent P exponent H tau
      (fun i r => finiteAnswerTable keys (keys.map fun input => child input.1 input.2) (i, r))
      (b, roundInterval (seedGridSpacing b P) q) =
    keyedOnlineSourceRange source target parent P exponent H tau child
      (b, roundInterval (seedGridSpacing b P) q) := by
  dsimp only
  apply keyedOnlineSourceRange_congr
  intro action ha i
  apply finiteAnswerTable_map
  exact wideWarmupInputs_pair parent P b _ _
    (queryEarlierRepresentatives_online N P F exponent a parentInitial q b hb) action ha i

section Query

variable {ι α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (parentInitial : TargetInterval target.length → ℚ)
  (child initial : Fin M → TargetInterval target.length → ℚ)
  (draw : CellGroupDraws M F Q) (q : TargetInterval target.length)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)



theorem localOnlineSourceStepQuery_value (oracle : ι → ℚ)
    (integer : ℕ → TargetInterval target.length → ℕ)
    (earlier : PhysicalChildTables M target.length)
    (current : Fin M → TargetInterval target.length → ℚ) (ht : 0 < t)
    (hreadInteger : ∀ key ∈ localOnlineSourceKeys N P F a parentInitial q,
      (readInteger key (keyedOnlineSourceRange source target parent P exponent H tau child key)).value oracle =
        (integer key.1 key.2 : ℚ))
    (hreadEarlier : ∀ input, (readEarlier input).value oracle = earlier input.1 input.2.1 input.2.2)
    (hreadCurrent : ∀ input, (readCurrent input).value oracle = current input.1 input.2) :
    (localOnlineSourceStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial draw q readInteger readEarlier readCurrent).value oracle =
    rationalLocalWideStep source target parent N P F exponent Q tau a delta parentInitial child initial
      (fun i r => earlier i (t - 1) r) current draw
      (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
        parentInitial child initial earlier (t - 1) integer q) q := by
  let keys := localOnlineSourceKeys N P F a parentInitial q
  let values := keys.map fun key =>
    (readInteger key (keyedOnlineSourceRange source target parent P exponent H tau child key)).value oracle
  let cached := fun b r => ⌊finiteAnswerTable keys values (b, r)⌋₊
  have hcached (b : ℕ) (hb : b ∈ dyadicQueryWindow N (parentInitial q) a F) :
      cached b (roundInterval (seedGridSpacing b P) q) =
        integer b (roundInterval (seedGridSpacing b P) q) := by
    have hmem := localOnlineSourceKeys_mem N P F a parentInitial q b hb
    dsimp only [cached, values]
    rw [finiteAnswerTable_map keys _ _ hmem, hreadInteger _ hmem]
    simp
  have honline := localOnlineCandidates_integer_congr source target parent N P F exponent H tau a eta kappa
    parentInitial child initial earlier (t - 1) cached integer q (fun b hb _ => hcached b hb)
  unfold localOnlineSourceStepQuery
  rw [FiniteQuery.collect_value]
  rw [localRefinementStepQuery_value source target parent N P F exponent H Q tau a eta kappa delta t
    parentInitial child initial draw cached q readEarlier readCurrent oracle earlier current ht
    hreadEarlier hreadCurrent]
  rw [honline]

end Query

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SourceRankedRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Restrict only the recursive table keys of a mixed source/table query.
The source reads remain explicit. This preserves the finite cache domain
without materializing any counterfactual table. -/

namespace EditApproximation.SourceRanked

variable {σ κ : Type*} (tableRank : κ → ℕ) (supported : κ → Prop)







 theorem restrictBody_value
    (tableBody : (parent : κ) → FiniteQuery (Sum σ {key : κ // tableRank key < tableRank parent}))
    (sourceValue : σ → ℚ) (tableValue : κ → ℚ) (parent : {key : κ // supported key})
    (hkeys : ∀ key ∈ (tableBody parent.val).keys (Sum.elim sourceValue (fun key => tableValue key.val)),
      supportedChild tableRank supported parent.val key) :
    (restrictBody tableRank supported tableBody parent).value
        (Sum.elim sourceValue (fun key => tableValue key.val.val)) =
      (tableBody parent.val).value (Sum.elim sourceValue (fun key => tableValue key.val)) := by
  classical
  unfold restrictBody
  rw [FiniteQuery.mapKeys_value]
  have horacle :
      (Sum.elim sourceValue (fun key => tableValue key.val.val)) ∘
        supportedChildMap tableRank supported parent =
      (fun key => (Sum.elim sourceValue (fun key => tableValue key.val)) key.val) := by
    funext key
    rcases key with ⟨key, hs⟩
    cases key <;> rfl
  rw [horacle]
  exact FiniteQuery.restrict_value _ _ _ hkeys

 theorem restrictBody_keys_all
    (tableBody : (parent : κ) → FiniteQuery (Sum σ {key : κ // tableRank key < tableRank parent}))
    (sourceValue : σ → ℚ) (tableValue : κ → ℚ)
    (sourcePredicate : σ → Prop) (tablePredicate : κ → Prop)
    (parent : {key : κ // supported key})
    (hkeys : ∀ key ∈ (tableBody parent.val).keys (Sum.elim sourceValue (fun key => tableValue key.val)),
      supportedChild tableRank supported parent.val key)
    (hall : ∀ key ∈ (tableBody parent.val).keys (Sum.elim sourceValue (fun key => tableValue key.val)),
      match key with | .inl source => sourcePredicate source | .inr table => tablePredicate table.val) :
    ∀ key ∈ (restrictBody tableRank supported tableBody parent).keys
        (Sum.elim sourceValue (fun key => tableValue key.val.val)),
      match key with | .inl source => sourcePredicate source | .inr table => tablePredicate table.val.val := by
  classical
  unfold restrictBody
  rw [FiniteQuery.mapKeys_keys]
  intro key hk
  obtain ⟨small, hs, rfl⟩ := List.mem_map.mp hk
  have horacle :
      (Sum.elim sourceValue (fun key => tableValue key.val.val)) ∘
        supportedChildMap tableRank supported parent =
      (fun key => (Sum.elim sourceValue (fun key => tableValue key.val)) key.val) := by
    funext key
    rcases key with ⟨key, hp⟩
    cases key <;> rfl
  rw [horacle] at hs
  have hmem : small.val ∈ ((FiniteQuery.restrict
      (supportedChild tableRank supported parent.val) (tableBody parent.val)).keys
      (fun key => (Sum.elim sourceValue (fun key => tableValue key.val)) key.val)).map Subtype.val :=
    List.mem_map.mpr ⟨small, hs, rfl⟩
  rw [FiniteQuery.restrict_keys _ _ _ hkeys] at hmem
  have h := hall small.val hmem
  rcases small with ⟨small, hp⟩
  cases small <;> exact h

end EditApproximation.SourceRanked

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalGroupSourceQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Whole-cell group samples are exposed through scalar source reads.
Every needed scale/sample coordinate is enumerated once per group; unused
groups are absent from this query. -/

namespace EditApproximation





theorem groupDrawFromValues_eq {M F Q : ℕ} [NeZero M]
    (groups : List (ℕ × (ℕ × ℕ))) (draw : CellGroupDraws M F Q)
    (key : ℕ × (ℕ × ℕ)) (hk : key ∈ groups) :
    groupDrawFromValues (groupScalarKeys M F Q groups)
        ((groupScalarKeys M F Q groups).map (groupScalarValue draw)) key.1 key.2 = draw key.1 key.2 := by
  classical
  funext scale sample
  apply Fin.ext
  simp only [groupDrawFromValues, Fin.val_ofNat]
  rw [finiteAnswerTable_map _ _ _ (groupScalarKeys_mem M F Q groups key hk scale sample)]
  simp only [groupScalarValue, Nat.floor_natCast]
  exact Nat.mod_eq_of_lt (draw key.1 key.2 scale sample).isLt

theorem localCellGroupActions_congr_draw {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent Q : ℕ) (tau a : ℚ)
    (initial : TargetInterval target.length → ℚ)
    (child warmup current : Fin M → TargetInterval target.length → ℚ)
    (left right : CellGroupDraws M F Q) (q : TargetInterval target.length)
    (h : ∀ key ∈ localGroupQueryKeys N F exponent a initial q, left key.1 key.2 = right key.1 key.2) :
    localCellGroupActions source target parent N P F exponent Q tau a initial child warmup current left q =
      localCellGroupActions source target parent N P F exponent Q tau a initial child warmup current right q := by
  unfold localCellGroupActions
  apply List.flatMap_congr
  intro b hb
  apply List.filterMap_congr
  intro cell hc
  rw [h (b, cell) (List.mem_flatMap.mpr ⟨b, hb, List.mem_map.mpr ⟨cell, hc, rfl⟩⟩)]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalRandomSourceQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A local refinement step with both kinds of random input made explicit.
All scalar group reads and range-indexed online reads precede the existing
finite earlier/current queries, whose semantic values are preserved. -/

namespace EditApproximation

section Step

variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (parentInitial : TargetInterval target.length → ℚ)
  (child initial : Fin M → TargetInterval target.length → ℚ)
  (q : TargetInterval target.length)
  (readGroup : GroupScalarKey M F Q → FiniteQuery ι)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)



theorem localRandomSourceStepQuery_value (oracle : ι → ℚ) (draw : CellGroupDraws M F Q)
    (integer : ℕ → TargetInterval target.length → ℕ)
    (earlier : PhysicalChildTables M target.length)
    (current : Fin M → TargetInterval target.length → ℚ) (ht : 0 < t)
    (hreadGroup : ∀ key ∈ groupScalarKeys M F Q (localGroupQueryKeys N F exponent a parentInitial q),
      (readGroup key).value oracle = groupScalarValue draw key)
    (hreadInteger : ∀ key ∈ localOnlineSourceKeys N P F a parentInitial q,
      (readInteger key (keyedOnlineSourceRange source target parent P exponent H tau child key)).value oracle =
        (integer key.1 key.2 : ℚ))
    (hreadEarlier : ∀ input, (readEarlier input).value oracle = earlier input.1 input.2.1 input.2.2)
    (hreadCurrent : ∀ input, (readCurrent input).value oracle = current input.1 input.2) :
    (localRandomSourceStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial q readGroup readInteger readEarlier readCurrent).value oracle =
    rationalLocalWideStep source target parent N P F exponent Q tau a delta parentInitial child initial
      (fun i r => earlier i (t - 1) r) current draw
      (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
        parentInitial child initial earlier (t - 1) integer q) q := by
  classical
  let groups := localGroupQueryKeys N F exponent a parentInitial q
  let keys := groupScalarKeys M F Q groups
  have hvalues : keys.map (fun key => (readGroup key).value oracle) = keys.map (groupScalarValue draw) := by
    apply List.map_congr_left
    intro key hk
    exact hreadGroup key hk
  let cached := groupDrawFromValues keys (keys.map (groupScalarValue draw))
  have hdraw : ∀ key ∈ groups, cached key.1 key.2 = draw key.1 key.2 :=
    fun key hk => groupDrawFromValues_eq groups draw key hk
  unfold localRandomSourceStepQuery
  rw [FiniteQuery.collect_value, hvalues]
  rw [localOnlineSourceStepQuery_value source target parent N P F exponent H Q tau a eta kappa delta t
    parentInitial child initial cached q readInteger readEarlier readCurrent oracle integer earlier current ht
    hreadInteger hreadEarlier hreadCurrent]
  unfold rationalLocalWideStep
  rw [localCellGroupActions_congr_draw source target parent N P F exponent Q tau a parentInitial
    child initial current cached draw q hdraw]

end Step

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalRandomDataQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Gather data before selecting a random source coordinate. Online ranges
are calculated solely from previously requested band values; group draws and
online draws are ordinary scalar reads in the same adaptive query. -/

namespace EditApproximation

section BandData

variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (parentInitial : TargetInterval target.length → ℚ)
  (readMass readInitial : Fin M × TargetInterval target.length → FiniteQuery ι)
  (readGroup : GroupScalarKey M F Q → FiniteQuery ι)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)



theorem localRandomBandDataQuery_value (oracle : ι → ℚ)
    (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (earlier : PhysicalChildTables M target.length)
    (current : Fin M → TargetInterval target.length → ℚ) (ht : 0 < t)
    (hreadMass : ∀ input, (readMass input).value oracle = child input.1 input.2)
    (hreadInitial : ∀ input, (readInitial input).value oracle = initial input.1 input.2)
    (hreadEarlier : ∀ input, (readEarlier input).value oracle = earlier input.1 input.2.1 input.2.2)
    (hreadGroup : ∀ key, (readGroup key).value oracle = groupScalarValue draw key)
    (hreadInteger : ∀ key,
      (readInteger key (keyedOnlineSourceRange source target parent P exponent H tau child key)).value oracle =
        (integer key.1 key.2 : ℚ))
    (hreadCurrent : ∀ input, (readCurrent input).value oracle = current input.1 input.2) :
    (localRandomBandDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial readMass readInitial readGroup readInteger q readEarlier readCurrent).value oracle =
    rationalLocalWideStep source target parent N P F exponent Q tau a delta parentInitial child initial
      (fun i r => earlier i (t - 1) r) current draw
      (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
        parentInitial child initial earlier (t - 1) integer q) q := by
  classical
  let keys := refinementBandInputList (M := M) parent N P F exponent a parentInitial q
  let mass := fun i r => finiteAnswerTable keys (keys.map fun input => child input.1 input.2) (i, r)
  let initial' := fun i r => finiteAnswerTable keys (keys.map fun input => initial input.1 input.2) (i, r)
  have hmass : ∀ input ∈ keys, mass input.1 input.2 = child input.1 input.2 := by
    intro input hi
    exact finiteAnswerTable_map keys _ input hi
  have hinitial : ∀ input ∈ keys, initial' input.1 input.2 = initial input.1 input.2 := by
    intro input hi
    exact finiteAnswerTable_map keys _ input hi
  have honline := localOnlineCandidates_congr_bandTables source target parent N P F exponent H
    tau a eta kappa (t - 1) parentInitial mass child initial' initial earlier integer q hmass hinitial
  have hgroups := localCellGroupActions_congr_bandTables source target parent N P F exponent Q
    tau a parentInitial mass child initial' initial current draw q hmass hinitial
  unfold localRandomBandDataQuery
  rw [FiniteQuery.collect_value]
  simp only [hreadMass]
  rw [FiniteQuery.collect_value]
  simp only [hreadInitial]
  rw [localRandomSourceStepQuery_value source target parent N P F exponent H Q tau a eta kappa delta t
    parentInitial mass initial' q readGroup readInteger readEarlier readCurrent oracle draw integer earlier current ht
    (fun key _ => hreadGroup key) ?_ hreadEarlier hreadCurrent]
  rotate_left
  · intro key hk
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hk
    rw [keyedOnlineSourceRange_gathered source target parent N P F exponent H tau a
      parentInitial child q b hb]
    exact hreadInteger _
  rw [honline]
  unfold rationalLocalWideStep
  rw [hgroups]

end BandData

section AllData

variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (readParentInitial : TargetInterval target.length → FiniteQuery ι)
  (readMass readInitial : Fin M × TargetInterval target.length → FiniteQuery ι)
  (readGroup : GroupScalarKey M F Q → FiniteQuery ι)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)



theorem localRandomDataQuery_value (oracle : ι → ℚ)
    (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (earlier : PhysicalChildTables M target.length)
    (current : Fin M → TargetInterval target.length → ℚ) (ht : 0 < t)
    (hreadParentInitial : ∀ r, (readParentInitial r).value oracle = parentInitial r)
    (hreadMass : ∀ input, (readMass input).value oracle = child input.1 input.2)
    (hreadInitial : ∀ input, (readInitial input).value oracle = initial input.1 input.2)
    (hreadEarlier : ∀ input, (readEarlier input).value oracle = earlier input.1 input.2.1 input.2.2)
    (hreadGroup : ∀ key, (readGroup key).value oracle = groupScalarValue draw key)
    (hreadInteger : ∀ key,
      (readInteger key (keyedOnlineSourceRange source target parent P exponent H tau child key)).value oracle =
        (integer key.1 key.2 : ℚ))
    (hreadCurrent : ∀ input, (readCurrent input).value oracle = current input.1 input.2) :
    (localRandomDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
      readParentInitial readMass readInitial readGroup readInteger q readEarlier readCurrent).value oracle =
    rationalLocalWideStep source target parent N P F exponent Q tau a delta parentInitial child initial
      (fun i r => earlier i (t - 1) r) current draw
      (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
        parentInitial child initial earlier (t - 1) integer q) q := by
  classical
  let keys := refinementInitialSupport N P F exponent a (parentInitial q) q
  let cached := finiteAnswerTable keys (keys.map parentInitial)
  have heq : ∀ r ∈ refinementInitialSupport N P F exponent a (parentInitial q) q,
      parentInitial r = cached r := by
    intro r hr
    exact (finiteAnswerTable_map keys parentInitial r hr).symm
  have honline := localOnlineCandidates_congr_initial source target parent N P F exponent H
    tau a eta kappa (t - 1) parentInitial cached child initial earlier integer q heq
  have hstep := rationalLocalWideStep_congr_initial source target parent N P F exponent Q tau a
    parentInitial cached child initial current draw q heq delta (fun i r => earlier i (t - 1) r)
    (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
      parentInitial child initial earlier (t - 1) integer q)
  unfold localRandomDataQuery
  rw [FiniteQuery.bind_value, hreadParentInitial q, FiniteQuery.collect_value]
  simp only [hreadParentInitial]
  rw [localRandomBandDataQuery_value source target parent N P F exponent H Q tau a eta kappa delta t
    cached readMass readInitial readGroup readInteger q readEarlier readCurrent oracle draw integer child initial earlier current ht
    hreadMass hreadInitial hreadEarlier hreadGroup hreadInteger hreadCurrent]
  rw [← honline]
  exact hstep.symm

end AllData

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRandomDataRequest
attribute [-instance] _root_.OAI.EditApproximation.PhysicalTableRequest.decidableBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A physical refinement request with source reads interleaved with ranked
table requests. The requested online range is calculated after the child
mass values are returned. -/

namespace EditApproximation

section CompleteStep

variable {σ α : Type*} (source target : List α) {M J : ℕ} [NeZero M]
  (N P F exponent H Q : ℕ) (tau a eta kappa delta : ℚ)
  (pass copy T S t : ℕ) (ht : 0 < t) (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (readGroup : GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (q : TargetInterval target.length)



theorem physicalRandomDataRequestQuery_value (answer : PhysicalTableRequest M J target.length → ℚ)
    (sourceAnswer : σ → ℚ) (draw : CellGroupDraws M F Q)
    (integer : ℕ → TargetInterval target.length → ℕ)
    (hgroup : ∀ key, (readGroup key).value sourceAnswer = groupScalarValue draw key)
    (honline : ∀ key,
      (readInteger key (keyedOnlineSourceRange source target (physicalSourceInterval source.length node)
        P exponent H tau (fun i r => (∑ j : Fin T, answer (PhysicalTableRequest.warmup pass copy
          (physicalChild node hbelow i) j.val r)) / T) key)).value sourceAnswer =
        (integer key.1 key.2 : ℚ)) :
    let parentInitial := fun r => answer (PhysicalTableRequest.warmup pass copy node 0 r)
    let child := fun i r => (∑ j : Fin T, answer (PhysicalTableRequest.warmup pass copy
      (physicalChild node hbelow i) j.val r)) / T
    let initial := fun i r => answer (PhysicalTableRequest.warmup pass copy (physicalChild node hbelow i) 0 r)
    let children := fun i s r => answer (PhysicalTableRequest.refinement pass copy
      (physicalChild node hbelow i) T s r)
    (physicalRandomDataRequestQuery source target N P F exponent H Q tau a eta kappa delta
      pass copy T S t ht node hbelow readGroup readInteger q).value (Sum.elim sourceAnswer (fun request => answer request.val)) =
      rationalLocalWideStep source target (physicalSourceInterval source.length node)
        N P F exponent Q tau a delta parentInitial child initial
        (fun i r => children i (t - 1) r) (fun i r => children i t r) draw
        (localOnlineCandidates source target (physicalSourceInterval source.length node)
          N P F exponent H tau a eta kappa parentInitial child initial children (t - 1) integer q) q := by
  dsimp only
  let earlier := fun i s r => answer (PhysicalTableRequest.refinement pass copy (physicalChild node hbelow i) T s r)
  let masked := fun i s r => if s < t then earlier i s r else 0
  let parentInitial := fun r => answer (PhysicalTableRequest.warmup pass copy node 0 r)
  let child := fun i r => (∑ j : Fin T, answer (PhysicalTableRequest.warmup pass copy
    (physicalChild node hbelow i) j.val r)) / T
  let initial := fun i r => answer (PhysicalTableRequest.warmup pass copy (physicalChild node hbelow i) 0 r)
  have he (input : Fin M × ℕ × TargetInterval target.length) :
      (physicalRefinementEarlierQuery pass copy T S t node hbelow q input).value
        (fun request => answer request.val) = masked input.1 input.2.1 input.2.2 := by
    unfold physicalRefinementEarlierQuery
    split_ifs with hs
    · simp only [FiniteQuery.value, masked, ite_eq_left hs, earlier]
    · simp only [FiniteQuery.value, masked, ite_eq_right hs]
  rw [physicalRandomDataRequestQuery,
    localRandomDataQuery_value source target (physicalSourceInterval source.length node)
      N P F exponent H Q tau a eta kappa delta t _ _ _ _ _ q _ _ _ draw integer
      parentInitial child initial masked (fun i r => earlier i t r) ht]
  · have hprev : (fun i r => masked i (t - 1) r) = fun i r => earlier i (t - 1) r := by
      funext i r
      exact ite_eq_left (by omega : t - 1 < t)
    have honline := localOnlineCandidates_congr_earlier_cover source target
      (physicalSourceInterval source.length node) N P F exponent H t tau a eta kappa
      parentInitial child initial masked earlier (t - 1) integer q (by omega)
      (fun i s r hr => ite_eq_left (wideEarlierInputCover_time _ P t _ (i, s, r) hr))
    rw [hprev, honline]
  · intro r
    rw [FiniteQuery.mapKeys_value]
    rfl
  · intro input
    rw [FiniteQuery.mapKeys_value]
    exact physicalRefinementMassQuery_value pass copy T S t ht node hbelow q input answer
  · intro input
    rw [FiniteQuery.mapKeys_value]
    rfl
  · intro input
    rw [FiniteQuery.mapKeys_value]
    exact he input
  · intro key
    rw [FiniteQuery.mapKeys_value]
    exact hgroup key
  · intro key
    rw [FiniteQuery.mapKeys_value]
    exact honline key
  · intro input
    rw [FiniteQuery.mapKeys_value]
    rfl

end CompleteStep

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRandomGlobalQuery
attribute [-instance] _root_.OAI.EditApproximation.PhysicalTableRequest.decidableBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Global physical table bodies with explicit random reads. Only positive
internal refinement steps request random coordinates. All other cases
use finite warmup and initial queries. -/

namespace EditApproximation

theorem inactiveIfEq {β : Type*} (a b c : Prop) [Decidable a] [Decidable b] [Decidable c]
    (x y : β) (z : ¬ a → b → ¬ c → β) (h : ¬ (¬ a ∧ b ∧ ¬ c)) :
    (if a then x else y) =
      (if ha : a then x else if hb : b then if hc : c then y else z ha hb hc else y) := by
  by_cases ha : a
  · simp only [ite_eq_left ha, dite_eq_left ha]
  · by_cases hb : b
    · have hc : c := by
        by_contra hc
        exact h ⟨ha, hb, hc⟩
      simp only [ite_eq_right ha, dite_eq_right ha, dite_eq_left hb, dite_eq_left hc]
    · simp only [ite_eq_right ha, dite_eq_right ha, dite_eq_right hb]

section Global

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (initial : PhysicalEntry M J target.length → ℕ)





omit [NeZero M] in
 theorem physicalGlobalQuery_inactive
    (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
    (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
    (request : PhysicalTableRequest M J target.length)
    (hinactive : ¬ (T < request.index ∧ request.node.1.val < J ∧
      ¬ (physicalSourceInterval source.length request.node).hi -
        (physicalSourceInterval source.length request.node).lo ≤ 1)) :
    physicalInactiveGlobalQuery source target N P F T S copies factor multiplier initial request =
    physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request := by
  unfold physicalInactiveGlobalQuery physicalGlobalQuery
  dsimp only
  apply inactiveIfEq
  rintro ⟨hi, hb, hs⟩
  exact hinactive ⟨Nat.lt_of_not_ge hi, hb, hs⟩

 theorem physicalRandomGlobalQuery_inactive
    (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
    (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
    (request : PhysicalTableRequest M J target.length)
    (hinactive : ¬ (T < request.index ∧ request.node.1.val < J ∧
      ¬ (physicalSourceInterval source.length request.node).hi -
        (physicalSourceInterval source.length request.node).lo ≤ 1)) :
    physicalRandomGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request =
      FiniteQuery.mapKeys Sum.inr (physicalGlobalQuery source target N P F exponent H Q T S copies
        factor multiplier tau eta kappa delta group integer initial request) := by
  unfold physicalRandomGlobalQuery
  rw [dite_eq_right hinactive,
    physicalGlobalQuery_inactive source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta initial group integer request hinactive]

 theorem physicalRandomGlobalQuery_active_value (request : PhysicalTableRequest M J target.length)
    (hactive : T < request.index ∧ request.node.1.val < J ∧
      ¬ (physicalSourceInterval source.length request.node).hi -
        (physicalSourceInterval source.length request.node).lo ≤ 1)
    (sourceAnswer : σ → ℚ) (values : PhysicalTableRequest M J target.length → ℚ) :
    (physicalRandomGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request).value
      (Sum.elim sourceAnswer (fun child => values child.val)) =
    (physicalRandomDataRequestQuery source target N P F exponent H Q tau
      (refinementFactor (factor request.pass) F) eta kappa delta request.pass request.copy T S
      (request.index - T) (Nat.sub_pos_of_lt hactive.1) request.node hactive.2.1
      (readGroup request.pass request.copy ⟨request.node, hactive.2.1⟩
        (Fin.ofNat R (request.index - T - 1)))
      (readInteger request.pass request.copy ⟨request.node, hactive.2.1⟩
        (Fin.ofNat R (request.index - T - 1))) request.state).value
      (Sum.elim sourceAnswer (fun child => values child.val)) := by
  unfold physicalRandomGlobalQuery
  rw [dite_eq_left hactive, FiniteQuery.mapKeys_value]
  congr 1
  funext next
  cases next <;> rfl

 theorem physicalRandomGlobalQuery_compare
    (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
    (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
    (sourceAnswer : σ → ℚ) (values : PhysicalTableRequest M J target.length → ℚ)
    (hgroup : ∀ pass copy node time key, (readGroup pass copy node time key).value sourceAnswer =
      groupScalarValue (group pass copy node time) key)
    (honline : ∀ pass copy (node : PhysicalInternalNode M J) time key,
      (readInteger pass copy node time key
        (keyedOnlineSourceRange source target (physicalSourceInterval source.length node.val)
          P exponent H tau (fun i r => (∑ j : Fin T, values (PhysicalTableRequest.warmup pass copy
            (physicalChild node.val node.property i) j.val r)) / T) key)).value sourceAnswer =
        (integer pass copy node time key.1 key.2 : ℚ))
    (request : PhysicalTableRequest M J target.length) :
    (physicalRandomGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request).value
      (Sum.elim sourceAnswer (fun child => values child.val)) =
    (physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request).value (fun child => values child.val) := by
  by_cases ha : T < request.index ∧ request.node.1.val < J ∧
      ¬ (physicalSourceInterval source.length request.node).hi -
        (physicalSourceInterval source.length request.node).lo ≤ 1
  · rw [physicalRandomGlobalQuery_active_value source target N P F exponent H Q T S copies
      factor multiplier tau eta kappa delta readGroup readInteger initial request ha sourceAnswer values]
    rw [physicalGlobalQuery_refinement_value source target N P F exponent H Q T S copies
      factor multiplier tau eta kappa delta group integer initial request ha.1 ha.2.1 ha.2.2 values]
    let node : PhysicalInternalNode M J := ⟨request.node, ha.2.1⟩
    let time : Fin R := Fin.ofNat R (request.index - T - 1)
    have hg := hgroup request.pass request.copy node time
    have hi := honline request.pass request.copy node time
    have hnew := physicalRandomDataRequestQuery_value source target N P F exponent H Q tau
      (refinementFactor (factor request.pass) F) eta kappa delta request.pass request.copy T S
      (request.index - T) (Nat.sub_pos_of_lt ha.1) request.node ha.2.1
      (readGroup request.pass request.copy node time) (readInteger request.pass request.copy node time)
      request.state values sourceAnswer (group request.pass request.copy node time)
      (integer request.pass request.copy node time) hg hi
    have hold := physicalRefinementDataRequestQuery_value source target N P F exponent H Q tau
      (refinementFactor (factor request.pass) F) eta kappa delta request.pass request.copy T S
      (request.index - T) (Nat.sub_pos_of_lt ha.1) request.node ha.2.1
      (group request.pass request.copy node time) (integer request.pass request.copy node time)
      request.state values
    exact hnew.trans hold.symm
  · rw [physicalRandomGlobalQuery_inactive source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta readGroup readInteger initial group integer request ha, FiniteQuery.mapKeys_value]
    rfl

end Global

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalRandomQueryKeys
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Keys

variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (parentInitial : TargetInterval target.length → ℚ)
  (child initial : Fin M → TargetInterval target.length → ℚ)
  (readParent : TargetInterval target.length → FiniteQuery ι)
  (readMass readInitial : Fin M × TargetInterval target.length → FiniteQuery ι)
  (readGroup : GroupScalarKey M F Q → FiniteQuery ι)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
  (oracle : ι → ℚ) (predicate : ι → Prop)

variable
  (hgroup : ∀ input key, key ∈ (readGroup input).keys oracle → predicate key)
  (hinteger : ∀ input range key, key ∈ (readInteger input range).keys oracle → predicate key)
  (hearlier : ∀ input key, key ∈ (readEarlier input).keys oracle → predicate key)
  (hcurrent : ∀ input key, key ∈ (readCurrent input).keys oracle → predicate key)

omit [NeZero M] in
include hinteger hearlier hcurrent in
 theorem localOnlineSourceStepQuery_keys_all (draw : CellGroupDraws M F Q) :
    ∀ key ∈ (localOnlineSourceStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial draw q readInteger readEarlier readCurrent).keys oracle, predicate key := by
  unfold localOnlineSourceStepQuery
  apply FiniteQuery.keys_all_collect
  · intro input _ key hk
    exact hinteger input _ key hk
  · intro values
    exact localRefinementStepQuery_keys_all source target parent N P F exponent H Q
      tau a eta kappa delta t parentInitial child initial draw _ q readEarlier readCurrent
      oracle predicate hearlier hcurrent

include hgroup hinteger hearlier hcurrent in
 theorem localRandomSourceStepQuery_keys_all :
    ∀ key ∈ (localRandomSourceStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial q readGroup readInteger readEarlier readCurrent).keys oracle, predicate key := by
  unfold localRandomSourceStepQuery
  apply FiniteQuery.keys_all_collect
  · intro input _ key hk
    exact hgroup input key hk
  · intro values
    exact localOnlineSourceStepQuery_keys_all source target parent N P F exponent H Q
      tau a eta kappa delta t parentInitial child initial readInteger q readEarlier readCurrent
      oracle predicate hinteger hearlier hcurrent _

include hgroup hinteger hearlier hcurrent in
 theorem localRandomBandDataQuery_keys_all
    (hmass : ∀ input key, key ∈ (readMass input).keys oracle → predicate key)
    (hinitial : ∀ input key, key ∈ (readInitial input).keys oracle → predicate key) :
    ∀ key ∈ (localRandomBandDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial readMass readInitial readGroup readInteger q readEarlier readCurrent).keys oracle,
      predicate key := by
  unfold localRandomBandDataQuery
  apply FiniteQuery.keys_all_collect
  · intro input _ key hk
    exact hmass input key hk
  · intro massValues
    apply FiniteQuery.keys_all_collect
    · intro input _ key hk
      exact hinitial input key hk
    · intro initialValues
      exact localRandomSourceStepQuery_keys_all source target parent N P F exponent H Q
        tau a eta kappa delta t parentInitial _ _ readGroup readInteger q readEarlier readCurrent
        oracle predicate hgroup hinteger hearlier hcurrent

include hgroup hinteger hearlier hcurrent in
 theorem localRandomDataQuery_keys_all
    (hparent : ∀ r key, key ∈ (readParent r).keys oracle → predicate key)
    (hmass : ∀ input key, key ∈ (readMass input).keys oracle → predicate key)
    (hinitial : ∀ input key, key ∈ (readInitial input).keys oracle → predicate key) :
    ∀ key ∈ (localRandomDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
      readParent readMass readInitial readGroup readInteger q readEarlier readCurrent).keys oracle,
      predicate key := by
  unfold localRandomDataQuery
  rw [FiniteQuery.keys_bind]
  intro key hk
  rcases List.mem_append.mp hk with hfirst | hrest
  · exact hparent q key hfirst
  · apply FiniteQuery.keys_all_collect oracle predicate readParent
      (refinementInitialSupport N P F exponent a ((readParent q).value oracle) q) _ ?_ ?_ key hrest
    · intro r _ other ho
      exact hparent r other ho
    · intro initialValues
      exact localRandomBandDataQuery_keys_all source target parent N P F exponent H Q
        tau a eta kappa delta t _ readMass readInitial readGroup readInteger q readEarlier readCurrent
        oracle predicate hgroup hinteger hearlier hcurrent hmass hinitial

end Keys

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRandomRequestBounds
attribute [-instance] _root_.OAI.EditApproximation.PhysicalTableRequest.decidableBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

theorem physicalRandomDataRequest_keys_bounded {σ α : Type*} (source target : List α) {M J : ℕ} [NeZero M]
    (N P F exponent H Q : ℕ) (tau a eta kappa delta : ℚ)
    (passes copies pass copy T S t : ℕ) (ht : 0 < t) (htS : t ≤ S)
    (hpass : pass < passes) (hcopy : copy < copies)
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (readGroup : GroupScalarKey M F Q → FiniteQuery σ)
    (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
    (q : TargetInterval target.length) (oracle) :
    ∀ key ∈ (physicalRandomDataRequestQuery source target N P F exponent H Q tau a eta kappa delta
      pass copy T S t ht node hbelow readGroup readInteger q).keys oracle,
      (match key with | .inl _ => True | .inr table => table.val.Bounded passes copies T S) := by
  unfold physicalRandomDataRequestQuery
  apply localRandomDataQuery_keys_all
  · intro input
    apply FiniteQuery.keys_all_mapKeys
    intro key _
    trivial
  · intro input range
    apply FiniteQuery.keys_all_mapKeys
    intro key _
    trivial
  · intro input
    apply FiniteQuery.keys_all_mapKeys
    intro key hk
    unfold physicalRefinementEarlierQuery at hk
    split_ifs at hk with hs
    · simp only [FiniteQuery.keys, List.mem_singleton] at hk
      subst key
      exact PhysicalTableRequest.refinement_bounded passes copies pass copy
        (physicalChild node hbelow input.1) T S input.2.1 input.2.2 hpass hcopy (by omega)
    · exact False.elim (List.not_mem_nil hk)
  · intro input
    apply FiniteQuery.keys_all_mapKeys
    intro key hk
    simp only [physicalRefinementCurrentQuery, FiniteQuery.keys, List.mem_singleton] at hk
    subst key
    exact PhysicalTableRequest.refinement_bounded passes copies pass copy
      (physicalChild node hbelow input.1) T S t input.2 hpass hcopy htS
  · intro r
    apply FiniteQuery.keys_all_mapKeys
    intro key hk
    exact physicalRefinementWarmupRead_keys_bounded passes copies pass copy T S t ht hpass hcopy
      node q node le_rfl 0 (Nat.zero_le T) r _ key hk
  · intro input
    apply FiniteQuery.keys_all_mapKeys
    unfold physicalRefinementMassQuery
    apply FiniteQuery.keys_all_collect
    · intro j _ key hk
      exact physicalRefinementWarmupRead_keys_bounded passes copies pass copy T S t ht hpass hcopy
        node q (physicalChild node hbelow input.1) _ j.val (Nat.le_of_lt j.isLt) input.2 _ key hk
    · intro values key hk
      exact False.elim (List.not_mem_nil hk)
  · intro input
    apply FiniteQuery.keys_all_mapKeys
    intro key hk
    exact physicalRefinementWarmupRead_keys_bounded passes copies pass copy T S t ht hpass hcopy
      node q (physicalChild node hbelow input.1) _ 0 (Nat.zero_le T) input.2 _ key hk

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRandomBoundedQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

section Bounded

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (initial : PhysicalEntry M J target.length → ℕ)

 theorem physicalRandomGlobalQuery_keys_bounded (request : PhysicalTableRequest M J target.length)
    (hrequest : request.Bounded passes copies T S) (oracle) :
    ∀ key ∈ (physicalRandomGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request).keys oracle,
      SourceRanked.supportedChild (PhysicalTableRequest.combinedRank T S)
        (PhysicalTableRequest.Bounded passes copies T S) request key := by
  unfold physicalRandomGlobalQuery
  by_cases ha : T < request.index ∧ request.node.1.val < J ∧
      ¬ (physicalSourceInterval source.length request.node).hi -
        (physicalSourceInterval source.length request.node).lo ≤ 1
  · rw [dite_eq_left ha, FiniteQuery.mapKeys_keys]
    intro key hk
    obtain ⟨other, ho, rfl⟩ := List.mem_map.mp hk
    have hi := physicalRandomDataRequest_keys_bounded source target N P F exponent H Q tau
      (refinementFactor (factor request.pass) F) eta kappa delta passes copies request.pass request.copy T S
      (request.index - T) (Nat.sub_pos_of_lt ha.1) (by have := hrequest.2.2; omega)
      hrequest.1 hrequest.2.1 request.node ha.2.1
      (readGroup request.pass request.copy ⟨request.node, ha.2.1⟩ (Fin.ofNat R (request.index - T - 1)))
      (readInteger request.pass request.copy ⟨request.node, ha.2.1⟩ (Fin.ofNat R (request.index - T - 1)))
      request.state _ other ho
    cases other <;> exact hi
  · rw [dite_eq_right ha, FiniteQuery.mapKeys_keys]
    intro key hk
    obtain ⟨other, ho, rfl⟩ := List.mem_map.mp hk
    rw [physicalGlobalQuery_inactive (R := R) source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta initial (fun _ _ _ _ _ _ _ _ => 0) (fun _ _ _ _ _ _ => 0) request ha] at ho
    exact physicalGlobalQuery_keys_bounded (R := R) source target N P F exponent H Q T S passes copies
      factor multiplier tau eta kappa delta (fun _ _ _ _ _ _ _ _ => 0) (fun _ _ _ _ _ _ => 0)
      initial request hrequest _ other ho



 theorem physicalRandomBoundedQuery_value
    (sourceValue : σ → ℚ) (tableValue : PhysicalTableRequest M J target.length → ℚ)
    (request : {request : PhysicalTableRequest M J target.length // request.Bounded passes copies T S}) :
    (physicalRandomBoundedQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request).value
        (Sum.elim sourceValue (fun key => tableValue key.val.val)) =
    (physicalRandomGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request.val).value
        (Sum.elim sourceValue (fun key => tableValue key.val)) := by
  unfold physicalRandomBoundedQuery
  exact SourceRanked.restrictBody_value _ _ _ _ _ request
    (physicalRandomGlobalQuery_keys_bounded source target N P F exponent H Q T S passes copies
      factor multiplier tau eta kappa delta readGroup readInteger initial request.val request.property _)

end Bounded

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRandomValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Values

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

omit [NeZero M] in
 theorem localRequestValue_onlineRange (pass copy : ℕ) (node : PhysicalInternalNode M J)
    (key : ℕ × TargetInterval target.length) (hb : key.1 ∈ dyadicScales N) :
    keyedOnlineSourceRange source target (physicalSourceInterval source.length node.val) P exponent H tau
      (fun i r => (∑ j : Fin T, localRequestValue source target N P F exponent H Q T S copies
        factor multiplier tau eta kappa delta group integer initial
        (PhysicalTableRequest.warmup pass copy (physicalChild node.val node.property i) j.val r)) / T) key =
    physicalLocalOnlineMass source target
      (localSeedSequence source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial pass) N P F (factor pass) T exponent H tau
      (node, physicalScaleIndex N key.1 hb, key.2) := by
  have hmass :
      (fun i r => (∑ j : Fin T, localRequestValue source target N P F exponent H Q T S copies
        factor multiplier tau eta kappa delta group integer initial
        (PhysicalTableRequest.warmup pass copy (physicalChild node.val node.property i) j.val r)) / T) =
      physicalLocalChildMass source target
        (localSeedSequence source target N P F exponent H Q T S copies factor multiplier
          tau eta kappa delta group integer initial pass) N P F (factor pass) T node.val node.property := by
    funext i r
    exact localRequestValue_mass source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial pass copy (physicalChild node.val node.property i) r
  unfold keyedOnlineSourceRange physicalLocalOnlineMass physicalLocalOnlineBandG
  rw [physicalScaleIndex_get, hmass]

variable
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (sourceAnswer : σ → ℚ)
  (hgroup : ∀ pass copy node time key, (readGroup pass copy node time key).value sourceAnswer =
    groupScalarValue (group pass copy node time) key)
  (honline : ∀ pass copy (node : PhysicalInternalNode M J) time key,
    (readInteger pass copy node time key
      (keyedOnlineSourceRange source target (physicalSourceInterval source.length node.val)
        P exponent H tau (fun i r => (∑ j : Fin T, localRequestValue source target N P F exponent H Q T S
          copies factor multiplier tau eta kappa delta group integer initial (PhysicalTableRequest.warmup
            pass copy (physicalChild node.val node.property i) j.val r)) / T) key)).value sourceAnswer =
      (integer pass copy node time key.1 key.2 : ℚ))

include hgroup honline in
 theorem physicalRandomBoundedQuery_localValue
    (request : {request : PhysicalTableRequest M J target.length // request.Bounded passes copies T S}) :
    (physicalRandomBoundedQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request).value
      (Sum.elim sourceAnswer (fun key => localRequestValue source target N P F exponent H Q T S copies
        factor multiplier tau eta kappa delta group integer initial key.val.val)) =
    localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request.val := by
  rw [physicalRandomBoundedQuery_value]
  exact (physicalRandomGlobalQuery_compare source target N P F exponent H Q T S copies factor multiplier
    tau eta kappa delta readGroup readInteger initial group integer sourceAnswer
    (localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial) hgroup honline request.val).trans
    (physicalGlobalQuery_value source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request.val)

end Values

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalScalarReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Direct scalar source requests. The physical scale/cell guards agree
with the original raw providers, and an online request carries its range. -/

namespace EditApproximation

section GroupCorrectness

variable (M J N n exponent F Q R B : ℕ) [NeZero M]
  (draw : PhysicalScalarDraw M J N n exponent F Q R B)

omit [NeZero M] in
theorem groupQuery_transport (b c : ℕ) (h : b = c)
    (queries : PhysicalGroupQueries M J N n exponent F Q R B b)
    (values : ParentGroupDraw M (groupDyadicScales M b F).length
      (fun scale => groupSampleCount M Q b (groupDyadicScaleAt M b F scale)))
    (hq : ∀ scale sample, (queries scale sample).value
      (physicalScalarAnswer M J N n exponent F Q R B draw) = (values scale sample).val) :
    ∀ scale sample,
      ((Eq.mp (congrArg (PhysicalGroupQueries M J N n exponent F Q R B) h) queries) scale sample).value
        (physicalScalarAnswer M J N n exponent F Q R B draw) =
      ((Eq.mp (congrArg (fun b => ParentGroupDraw M (groupDyadicScales M b F).length
        (fun scale => groupSampleCount M Q b (groupDyadicScaleAt M b F scale))) h) values) scale sample).val := by
  subst c
  exact hq

 theorem physicalScalarGroupRead_value (node : PhysicalInternalNode M J) (time : Fin R)
    (key : GroupScalarKey M F Q) :
    (physicalScalarGroupRead M J N n exponent F Q R B node time key).value
      (physicalScalarAnswer M J N n exponent F Q R B draw) =
    groupScalarValue (physicalRawGroupDraws M J N n exponent F Q R
      (fun group => physicalScalarPack M J N n exponent F Q R B draw (.inr group)) node time) key := by
  rcases key with ⟨⟨b, cell⟩, scale, sample⟩
  unfold physicalScalarGroupRead physicalScalarGroupQueries groupScalarValue physicalRawGroupDraws
  dsimp only
  split_ifs with hb hc
  · let group : PhysicalLocalGroupKey M J N n exponent :=
      (node, physicalScaleIndex N b hb,
        ⟨cell.1, Nat.lt_succ_of_le hc.1⟩, ⟨cell.2, Nat.lt_succ_of_le hc.2⟩)
    exact groupQuery_transport M J N n exponent F Q R B draw
      ((dyadicScales N).get group.2.1) b (physicalScaleIndex_get N b hb)
      (physicalScalarGroupQueriesAt M J N n exponent F Q R B group time)
      (physicalScalarPack M J N n exponent F Q R B draw (.inr group) time)
      (fun _ _ => rfl) scale sample
  · rfl
  · rfl

end GroupCorrectness

section OnlineCorrectness

variable {α : Type*} [DecidableEq α] {M J : ℕ} [NeZero M]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T exponent H Q R B : ℕ) (tau : ℚ)
  (hbound : ∀ key, physicalLocalOnlineMass source target U N P F A T exponent H tau key ≤ B)
  (draw : PhysicalScalarDraw M J N target.length exponent F Q R B)

omit [NeZero M] in
 theorem physicalScalarOnlineRead_value [NeZero R]
    (node : PhysicalInternalNode M J) (time : Fin R) (key : ℕ × TargetInterval target.length)
    (range : ℕ)
    (hrange : ∀ hb : key.1 ∈ dyadicScales N, range =
      physicalLocalOnlineMass source target U N P F A T exponent H tau
        (node, physicalScaleIndex N key.1 hb, key.2)) :
    (physicalScalarOnlineRead M J N target.length exponent F Q R B node time key range).value
      (physicalScalarAnswer M J N target.length exponent F Q R B draw) =
    (physicalRawOnlineIntegers source target U N P F A T exponent H tau
      (fun online => physicalCommonSample source target U N P F A T exponent H Q R B tau hbound
        (physicalScalarPack M J N target.length exponent F Q R B draw) (.inl online))
      node time key.1 key.2 : ℚ) := by
  unfold physicalScalarOnlineRead physicalRawOnlineIntegers
  by_cases hb : key.1 ∈ dyadicScales N
  · rw [dite_eq_left hb, dite_eq_left hb, hrange hb]
    have hpos := physicalCommonMass_positive source target U N P F A T exponent H tau
      (node, physicalScaleIndex N key.1 hb, key.2)
    rw [dite_eq_left ⟨hpos, hbound _⟩]
    simp only [FiniteQuery.value, physicalCommonSample, physicalCommonCoordinateImage,
      physicalScalarPack, physicalScalarCoordinatePack, physicalScalarAnswer,
      physicalCommonSelectedKey, physicalCommonSelectedOnlineKey]
    exact (congrArg (fun z : ℕ => (z : ℚ)) (Fin.val_cast _ _)).symm
  · rw [dite_eq_right hb, dite_eq_right hb]
    rfl

end OnlineCorrectness

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalScalarFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Finite independent scalar sources for all passes and copies. The
incoming seed selects the range only after the earlier passes are evaluated. -/

namespace EditApproximation

section Family

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ) (hP : 0 < P)





variable (draw : PhysicalFamilyScalarDraw
  (M := M) (J := J) (R := R) target N P F exponent H Q passes copies)







noncomputable def physicalFamilySample (seed : PhysicalEntry M J target.length → ℕ) (pass copy : ℕ) :=
  physicalCommonSample source target seed N P F (factor pass) T exponent H Q R
    (localOnlineMassBound M P H) tau
    (physicalLocalOnlineMass_le source target seed N P F (factor pass) T exponent H tau hP)
    (physicalScalarPack M J N target.length exponent F Q R (localOnlineMassBound M P H)
      (physicalFamilyDraw target N P F exponent H Q passes copies draw pass copy))

noncomputable def physicalFamilySeed (initial : PhysicalEntry M J target.length → ℕ) :
    ℕ → PhysicalEntry M J target.length → ℕ
  | 0 => initial
  | pass + 1 => fun state => min N (upperMedian (List.ofFn fun copy : Fin copies =>
      ⌈(multiplier pass : ℚ) * physicalLocalJointValue source target
        (physicalFamilySeed initial pass) N P F (factor pass) T exponent H Q tau eta kappa delta
        (physicalFamilySample source target N P F exponent H Q T passes copies factor tau hP draw
          (physicalFamilySeed initial pass) pass copy.val) state.1 S state.2⌉₊))

noncomputable def physicalFamilyGroup (pass copy : ℕ) :=
  physicalRawGroupDraws M J N target.length exponent F Q R
    (fun group => physicalScalarPack M J N target.length exponent F Q R (localOnlineMassBound M P H)
      (physicalFamilyDraw target N P F exponent H Q passes copies draw pass copy) (.inr group))

noncomputable def physicalFamilyInteger (initial : PhysicalEntry M J target.length → ℕ)
    (pass copy : ℕ) :=
  physicalRawOnlineIntegers source target
    (physicalFamilySeed source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta hP draw initial pass)
    N P F (factor pass) T exponent H tau
    (fun online => physicalFamilySample source target N P F exponent H Q T passes copies factor tau hP draw
      (physicalFamilySeed source target N P F exponent H Q T S passes copies factor multiplier
        tau eta kappa delta hP draw initial pass) pass copy (.inl online))

 theorem physicalFamilySeed_eq (initial : PhysicalEntry M J target.length → ℕ) (pass : ℕ) :
    localSeedSequence source target N P F exponent H Q T S copies factor multiplier tau eta kappa delta
      (physicalFamilyGroup target N P F exponent H Q passes copies draw)
      (physicalFamilyInteger source target N P F exponent H Q T S passes copies factor multiplier
        tau eta kappa delta hP draw initial) initial pass =
    physicalFamilySeed source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta hP draw initial pass := by
  induction pass with
  | zero => rfl
  | succ pass ih =>
    rw [localSeedSequence, physicalFamilySeed, ih]
    rfl

omit [DecidableEq α] [NeZero R] in
 theorem physicalFamilyGroupRead_value (pass copy : ℕ) (node : PhysicalInternalNode M J)
    (time : Fin R) (key : GroupScalarKey M F Q) :
    (physicalFamilyGroupRead target N P F exponent H Q passes copies pass copy node time key).value
      (physicalFamilyAnswer target N P F exponent H Q passes copies draw) =
    groupScalarValue (physicalFamilyGroup target N P F exponent H Q passes copies draw pass copy node time) key := by
  rw [physicalFamilyGroupRead, FiniteQuery.mapKeys_value]
  exact physicalScalarGroupRead_value M J N target.length exponent F Q R (localOnlineMassBound M P H)
    (physicalFamilyDraw target N P F exponent H Q passes copies draw pass copy) node time key

 theorem physicalFamilyOnlineRead_value (initial : PhysicalEntry M J target.length → ℕ)
    (pass copy : ℕ) (node : PhysicalInternalNode M J) (time : Fin R)
    (key : ℕ × TargetInterval target.length) :
    (physicalFamilyOnlineRead target N P F exponent H Q passes copies pass copy node time key
      (keyedOnlineSourceRange source target (physicalSourceInterval source.length node.val) P exponent H tau
        (fun i r => (∑ j : Fin T, localRequestValue source target N P F exponent H Q T S copies
          factor multiplier tau eta kappa delta
          (physicalFamilyGroup target N P F exponent H Q passes copies draw)
          (physicalFamilyInteger source target N P F exponent H Q T S passes copies factor multiplier
            tau eta kappa delta hP draw initial) initial
          (PhysicalTableRequest.warmup pass copy (physicalChild node.val node.property i) j.val r)) / T) key)).value
      (physicalFamilyAnswer target N P F exponent H Q passes copies draw) =
    (physicalFamilyInteger source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta hP draw initial pass copy node time key.1 key.2 : ℚ) := by
  rw [physicalFamilyOnlineRead, FiniteQuery.mapKeys_value]
  apply physicalScalarOnlineRead_value source target
    (physicalFamilySeed source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta hP draw initial pass) N P F (factor pass) T exponent H Q R
    (localOnlineMassBound M P H) tau
    (physicalLocalOnlineMass_le source target _ N P F (factor pass) T exponent H tau hP)
    (physicalFamilyDraw target N P F exponent H Q passes copies draw pass copy) node time key
  intro hb
  rw [localRequestValue_onlineRange source target N P F exponent H Q T S copies factor multiplier
    tau eta kappa delta, physicalFamilySeed_eq]

end Family

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSeedTables
attribute [-instance] _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.physicalEntryCodeWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Finite clamped seed tables and the exact table returned by a median pass. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory





noncomputable def physicalMedianUpdateTable {α Ω : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ) (a S copies : ℕ)
    (choices : Ω → PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (draws : Fin copies → Ω) :
    ClampedPhysicalSeed M J target.length N := fun state =>
  ⟨physicalMedianUpdate source target U N P F A T delta a S copies choices draws state,
    Nat.lt_succ_of_le (min_le_left _ _)⟩

@[simp] theorem physicalMedianUpdateTable_value {α Ω : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ) (a S copies : ℕ)
    (choices : Ω → PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (draws : Fin copies → Ω)
    (state : PhysicalEntry M J target.length) :
    clampedSeedNat (physicalMedianUpdateTable source target U N P F A T delta a S copies choices draws) state =
      physicalMedianUpdate source target U N P F A T delta a S copies choices draws state := rfl

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalSeedSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The actual finite adaptive sequence of median seed passes. Every chosen
incoming table uses its own fresh product of full-table copy streams. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory





section Program

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "tau" => RationalParameters.tau (rationalParameters ell)

abbrev ScheduledSeedDraw (pass : ℕ) (seed : Seed) := Fin (H ^ 2) →
  PhysicalProgramDraw (R := R) source target (clampedSeedNat seed) N P ell (scheduledSeedFactor N pass)
    T thetaExponent H (ell ^ 80) tau

end Program

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalSeedSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The seed schedule run with bounded local random keys. A whole incoming
seed chooses one fresh product of full-copy local streams. The failure
bound follows from the actual local median law, rather than a seed oracle. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Program

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "tau" => RationalParameters.tau (rationalParameters ell)

abbrev LocalScheduledSeedDraw (pass : ℕ) (seed : Seed) := Fin (H ^ 2) →
  PhysicalLocalProgramDraw (R := R) source target (clampedSeedNat seed) N P ell
    (scheduledSeedFactor N pass) T thetaExponent H (ell ^ 80) tau

end Program

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalCoarseSeedLaw
attribute [-instance] _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The clamped incoming seed table is the image of the actual complete
coarse sampler. Its simultaneous initial accuracy is a derived fact. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section CoarseLaw

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (N B : ℕ)
  (depth : PhysicalEntry M J target.length → ℕ)





variable [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]

noncomputable def physicalCoarseSeedLaw : Measure (ClampedPhysicalSeed M J target.length N) := by
  classical
  exact (coarseFullSeedMeasure B depth
    (fun state : PhysicalEntry M J target.length => physicalSource source state.1)
    (fun state : PhysicalEntry M J target.length => substring target state.2.lo state.2.hi)).map
      (physicalCoarseSeedTable source target N B depth)

end CoarseLaw

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFinalAccuracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Accuracy of the final fresh refinement after adaptive median seed passes,
under finite Bernstein bounds and an explicit incoming seed failure bound. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Final

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "terminalFactor" => scheduledSeedFactor N (computedSeedPassCount N)
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "tau" => RationalParameters.tau (rationalParameters ell)

abbrev FinalProgramDraw (seed : Seed) :=
  PhysicalProgramDraw (R := R) source target (clampedSeedNat seed) N P ell terminalFactor
    T thetaExponent H (ell ^ 80) tau

noncomputable def finalProgramDrawLaw (seed : Seed) :
    Measure (FinalProgramDraw (R := R) source target N P T H seed) :=
  physicalProgramDrawLaw (R := R) source target (clampedSeedNat seed) N P ell terminalFactor
    T thetaExponent H (ell ^ 80) tau

instance finalProgramDrawLaw_probability (seed : Seed) :
    IsProbabilityMeasure (finalProgramDrawLaw (R := R) source target N P T H seed) := by
  unfold finalProgramDrawLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Final

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalFinalAccuracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The final fresh bounded-key local query, following the actual local
median schedule, has the required approximation probability. The incoming
law is supplied by the concrete coarse sampler in the final theorem. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Final

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "terminalFactor" => scheduledSeedFactor N (computedSeedPassCount N)
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "tau" => RationalParameters.tau (rationalParameters ell)

abbrev LocalFinalProgramDraw (seed : Seed) :=
  PhysicalLocalProgramDraw (R := R) source target (clampedSeedNat seed) N P ell terminalFactor
    T thetaExponent H (ell ^ 80) tau

abbrev LocalFinalProgramOutcome :=
  Seed × (∀ seed : Seed, LocalFinalProgramDraw (R := R) source target N P T H seed)

end Final

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedRandomGlobalQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The coarse seed, recursive table values, and random scalar sources are
all requested through the memo program. Inactive refinement branches use
the existing explicit coarse/median seed queries. -/

namespace EditApproximation

section Global

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (initial : PhysicalEntry M J target.length → ℕ)



variable
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (sourceAnswer : σ → ℚ)

/-- Composition with the local source-provider correctness theorem. -/
 theorem chargedRandomGlobalQuery_value
    (hbody : ∀ parent,
      (physicalRandomBoundedQuery source target N P F exponent H Q T S passes copies factor multiplier
        tau eta kappa delta readGroup readInteger initial parent).value
        (Sum.elim sourceAnswer (fun child => localRequestValue source target N P F exponent H Q T S copies
          factor multiplier tau eta kappa delta group integer initial child.val.val)) =
      localRequestValue source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial parent.val)
    (request : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedRandomGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request).value
      (Sum.elim sourceAnswer (fun child => chargedRequestValue source target N P F exponent H Q T S
        passes copies factor multiplier tau eta kappa delta group integer initial child.val)) =
    chargedRequestValue source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial request := by
  cases request with
  | inl entry => rfl
  | inr parent =>
    change _ = localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial parent.val
    unfold chargedRandomGlobalQuery
    dsimp only
    split_ifs with hi hd hw
    · rw [FiniteQuery.mapKeys_value]
      exact chargedWarmupQuery_value source target N P F exponent H Q T S passes copies
        factor multiplier tau eta kappa delta group integer initial parent hi
    · rw [FiniteQuery.mapKeys_value,
        localRequestValue_terminal source target N P F exponent H Q T S copies factor multiplier
          tau eta kappa delta group integer initial parent.val (Or.inr hw)]
      exact physicalInitialQuery_value_local source target N P F _ _ _ _ _ _
        (chargedSeedQuery_localValue source target N P F exponent H Q T S passes copies
          factor multiplier tau eta kappa delta group integer initial parent)
    · rw [FiniteQuery.mapKeys_value]
      refine Eq.trans ?_ (hbody parent)
      congr 1
      funext next
      cases next <;> rfl
    · rw [FiniteQuery.mapKeys_value,
        localRequestValue_terminal source target N P F exponent H Q T S copies factor multiplier
          tau eta kappa delta group integer initial parent.val (Or.inl hd)]
      exact physicalInitialQuery_value_local source target N P F _ _ _ _ _ _
        (chargedSeedQuery_localValue source target N P F exponent H Q T S passes copies
          factor multiplier tau eta kappa delta group integer initial parent)

end Global

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_CommonSeedTrace
attribute [-instance] _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Adaptive seed passes driven by common per-pass random sources. The
trace stores one source for the actual pass, with no seed-indexed family.
Its returned seed has the original adaptive law. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

instance commonSeedTraceFintype (Seed : Type) (Ω : ℕ → Type)
    [Fintype Seed] [∀ pass, Fintype (Ω pass)] : (pass : ℕ) → Fintype (CommonSeedTrace Seed Ω pass)
  | 0 => inferInstanceAs (Fintype Seed)
  | pass + 1 =>
    letI := commonSeedTraceFintype Seed Ω pass
    inferInstanceAs (Fintype (CommonSeedTrace Seed Ω pass × Ω pass))

instance commonSeedTraceMeasurable (Seed : Type) (Ω : ℕ → Type)
    [MeasurableSpace Seed] [∀ pass, MeasurableSpace (Ω pass)] :
    (pass : ℕ) → MeasurableSpace (CommonSeedTrace Seed Ω pass)
  | 0 => inferInstanceAs (MeasurableSpace Seed)
  | pass + 1 =>
    letI := commonSeedTraceMeasurable Seed Ω pass
    inferInstanceAs (MeasurableSpace (CommonSeedTrace Seed Ω pass × Ω pass))

instance commonSeedTraceSingleton (Seed : Type) (Ω : ℕ → Type)
    [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
    [∀ pass, MeasurableSpace (Ω pass)] [∀ pass, MeasurableSingletonClass (Ω pass)] :
    (pass : ℕ) → MeasurableSingletonClass (CommonSeedTrace Seed Ω pass)
  | 0 => inferInstanceAs (MeasurableSingletonClass Seed)
  | pass + 1 =>
    letI := commonSeedTraceSingleton Seed Ω pass
    inferInstanceAs (MeasurableSingletonClass (CommonSeedTrace Seed Ω pass × Ω pass))

section Common

variable {Seed : Type} [Fintype Seed] [DecidableEq Seed]
  [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
  {Draw : ℕ → Seed → Type} [∀ pass seed, Fintype (Draw pass seed)]
  [∀ pass seed, MeasurableSpace (Draw pass seed)]
  [∀ pass seed, MeasurableSingletonClass (Draw pass seed)]
  {Ω : ℕ → Type} [∀ pass, Fintype (Ω pass)]
  [∀ pass, MeasurableSpace (Ω pass)] [∀ pass, MeasurableSingletonClass (Ω pass)]
  (drawLaw : ∀ pass seed, Measure (Draw pass seed))
  [∀ pass seed, IsProbabilityMeasure (drawLaw pass seed)]
  (randomLaw : ∀ pass, Measure (Ω pass)) [∀ pass, IsProbabilityMeasure (randomLaw pass)]
  (sample : ∀ pass seed, Ω pass → Draw pass seed)
  (next : ∀ pass seed, Draw pass seed → Seed)

noncomputable def commonTraceValue : (pass : ℕ) → CommonSeedTrace Seed Ω pass → Seed
  | 0, seed => seed
  | pass + 1, trace =>
    let seed := commonTraceValue pass trace.1
    next pass seed (sample pass seed trace.2)

noncomputable def commonTraceLaw (incoming : Measure Seed) :
    (pass : ℕ) → Measure (CommonSeedTrace Seed Ω pass)
  | 0 => incoming
  | pass + 1 => (commonTraceLaw incoming pass).prod (randomLaw pass)

instance commonTraceLaw_probability (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (pass : ℕ) : IsProbabilityMeasure (commonTraceLaw randomLaw incoming pass) := by
  induction pass with
  | zero => exact inferInstanceAs (IsProbabilityMeasure incoming)
  | succ pass ih =>
    let := ih
    exact inferInstanceAs (IsProbabilityMeasure
      ((commonTraceLaw randomLaw incoming pass).prod (randomLaw pass)))

end Common

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalCommonSeed
attribute [-instance] _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete common-source seed passes. The sampler range cap is proved
for every seed; no good-seed event is used to define or bound the draws. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section CommonSeed

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "cap" => localOnlineMassBound M P H

abbrev LocalCommonDraw := Fin (H ^ 2) →
  PhysicalCommonDraw M J N target.length thetaExponent ell (ell ^ 80) R cap

abbrev LocalCommonTrace (passes : ℕ) := CommonSeedTrace Seed
  (fun _ => LocalCommonDraw (M := M) (J := J) (R := R) target N P H) passes

end CommonSeed

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_AdaptiveSeedTrace
attribute [-instance] _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Preserve the finite draw history of adaptive seed passes. The final
seed has exactly the existing sequential law, while the history remains
available to the lazy evaluator when it asks for an earlier pass. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

instance adaptiveSeedTraceFintype (Seed : Type) (Draw : ℕ → Seed → Type)
    [Fintype Seed] [DecidableEq Seed] [∀ pass seed, Fintype (Draw pass seed)] :
    (pass : ℕ) → Fintype (AdaptiveSeedTrace Seed Draw pass)
  | 0 => inferInstanceAs (Fintype Seed)
  | pass + 1 =>
    letI := adaptiveSeedTraceFintype Seed Draw pass
    inferInstanceAs (Fintype (AdaptiveSeedTrace Seed Draw pass × (∀ seed, Draw pass seed)))

instance adaptiveSeedTraceMeasurable (Seed : Type) (Draw : ℕ → Seed → Type)
    [MeasurableSpace Seed] [∀ pass seed, MeasurableSpace (Draw pass seed)] :
    (pass : ℕ) → MeasurableSpace (AdaptiveSeedTrace Seed Draw pass)
  | 0 => inferInstanceAs (MeasurableSpace Seed)
  | pass + 1 =>
    letI := adaptiveSeedTraceMeasurable Seed Draw pass
    inferInstanceAs (MeasurableSpace (AdaptiveSeedTrace Seed Draw pass × (∀ seed, Draw pass seed)))

instance adaptiveSeedTraceSingleton (Seed : Type) (Draw : ℕ → Seed → Type)
    [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
    [∀ pass seed, MeasurableSpace (Draw pass seed)] [∀ pass seed, MeasurableSingletonClass (Draw pass seed)]
    [Fintype Seed] : (pass : ℕ) → MeasurableSingletonClass (AdaptiveSeedTrace Seed Draw pass)
  | 0 => inferInstanceAs (MeasurableSingletonClass Seed)
  | pass + 1 =>
    letI := adaptiveSeedTraceSingleton Seed Draw pass
    inferInstanceAs (MeasurableSingletonClass (AdaptiveSeedTrace Seed Draw pass × (∀ seed, Draw pass seed)))

section Trace

variable {Seed : Type} [Fintype Seed] [DecidableEq Seed]
  [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
  {Draw : ℕ → Seed → Type} [∀ pass seed, Fintype (Draw pass seed)]
  [∀ pass seed, MeasurableSpace (Draw pass seed)]
  [∀ pass seed, MeasurableSingletonClass (Draw pass seed)]
  (drawLaw : ∀ pass seed, Measure (Draw pass seed))
  [∀ pass seed, IsProbabilityMeasure (drawLaw pass seed)]
  (incoming : Measure Seed) [IsProbabilityMeasure incoming]
  (next : ∀ pass seed, Draw pass seed → Seed)

def adaptiveTraceValue : (pass : ℕ) → AdaptiveSeedTrace Seed Draw pass → Seed
  | 0, seed => seed
  | pass + 1, trace =>
    let seed := adaptiveTraceValue pass trace.1
    next pass seed (trace.2 seed)

end Trace

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalTraceProgram
attribute [-instance] _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extract the actual per-pass streams from a finite adaptive draw trace.
Earlier-pass streams are preserved when a new draw is appended, and the
lazy program's seed recurrence is exactly the trace's returned table. -/

namespace EditApproximation

section Trace

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N

abbrev LocalScheduledTrace (passes : ℕ) := AdaptiveSeedTrace Seed
  (LocalScheduledSeedDraw (R := R) source target N P T H) passes

end Trace

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalTraceMemoOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The bounded-key adaptive trace drives the actual charged memo program.
Its final root query has the same distribution as the local answer. The program
uses all previous-pass copies from the trace and one fresh terminal copy. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Output

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "passes" => computedSeedPassCount N

abbrev LocalTraceFinalOutcome :=
  LocalScheduledTrace (M := M) (J := J) (R := R) source target N P T H passes ×
    (∀ seed : Seed, LocalFinalProgramDraw (R := R) source target N P T H seed)

end Output

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalCommonOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The charged memo answer under one common random source per pass and
one fresh terminal source. Correct marginal laws suffice; hypothetical
seed-indexed draw families are not part of the execution. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Output

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

local notation "passes" => computedSeedPassCount N
local notation "ell" => inputSmallLog N
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "cap" => localOnlineMassBound M P H

abbrev LocalCommonTerminalDraw :=
  PhysicalCommonDraw M J N target.length thetaExponent ell (ell ^ 80) R cap

abbrev LocalCommonFinalOutcome :=
  LocalCommonTrace (M := M) (J := J) (R := R) target N P H passes ×
    LocalCommonTerminalDraw (M := M) (J := J) (R := R) target N P H

end Output

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_CommonArrayTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite array of fresh pass draws is equivalent to the sequential
common-source trace. The conversion has exactly the nested product law. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

variable {Seed Ω : Type}

def commonArrayToTrace : (n : ℕ) → Seed × (Fin n → Ω) → CommonSeedTrace Seed (fun _ => Ω) n
  | 0, input => input.1
  | n + 1, input => (commonArrayToTrace n (input.1, fun i => input.2 i.castSucc), input.2 (Fin.last n))

def commonTraceToArray : (n : ℕ) → CommonSeedTrace Seed (fun _ => Ω) n → Seed × (Fin n → Ω)
  | 0, seed => (seed, Fin.elim0)
  | n + 1, trace =>
    let previous := commonTraceToArray n trace.1
    (previous.1, Fin.snoc previous.2 trace.2)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_CommonArrayFinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A final independent draw may be stored as the last array row. These
maps expose the literal product law used by the scheduled seed passes. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

variable {Seed Ω Δ : Type}

def commonArrayFinal (n : ℕ) (input : Seed × (Fin (n + 1) → Ω)) :
    CommonSeedTrace Seed (fun _ => Ω) n × Ω :=
  (commonArrayToTrace n (input.1, fun i => input.2 i.castSucc), input.2 (Fin.last n))

def commonFinalArray (n : ℕ) (input : CommonSeedTrace Seed (fun _ => Ω) n × Ω) :
    Seed × (Fin (n + 1) → Ω) :=
  let previous := commonTraceToArray n input.1
  (previous.1, Fin.snoc previous.2 input.2)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilyMemo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The finite family is consumed through actual source reads in the shared
memo evaluator. Its final value and law agree with the proved local answer. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Memo

variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "passes" => computedSeedPassCount N
local notation "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)
local notation "Family" => PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)
local notation "Table" => ChargedPhysicalRequest M J target.length (passes + 1) (H ^ 2) T S



noncomputable def physicalFamilyMemoAnswer (hH : 0 < H) (bits : ℕ)
    (encode : Sum Key Table → ℕ) (rootQ : TargetInterval target.length) (input : Seed × Family) : ℕ :=
  if source = substring target rootQ.lo rootQ.hi then 0 else
    integerAnswer N ((physicalFamilyMemoResult source target N P T S H hH bits encode rootQ input).value : ℝ)

end Memo

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilyRuntime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The source family is the projection of terminating rejection-sampling executions. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Runtime

variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P T S H : ℕ)

local notation "SeedState" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "passes" => computedSeedPassCount N
local notation "FamilyRange" => physicalFamilyRange (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)
local notation "Table" => ChargedPhysicalRequest M J target.length (passes + 1) (H ^ 2) T S



noncomputable def physicalFamilyRuntimeLaw (incoming : Measure SeedState) :
    Measure (PhysicalFamilyRuntimeOutcome (M := M) (J := J) (R := R) target N P H) :=
  incoming.prod (rejectionRuntimeArrayLaw FamilyRange)

noncomputable def physicalFamilyRuntimeAnswer (hH : 0 < H) (bits : ℕ)
    (encode : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
      target N P ell exponent H (ell ^ 80) passes (H ^ 2)) Table → ℕ)
    (rootQ : TargetInterval target.length)
    (execution : PhysicalFamilyRuntimeOutcome (M := M) (J := J) (R := R) target N P H) : ℕ :=
  physicalFamilyMemoAnswer source target N P T S H hH bits encode rootQ
    (physicalFamilyRuntimeAccepted target N P H execution)

end Runtime

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalUniformAccuracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

open MeasureTheory ProbabilityTheory Filter

section Uniform

variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P T S H B : ℕ)
  [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
  (depth : PhysicalEntry M J target.length → ℕ)

local notation "passes" => computedSeedPassCount N
local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)
local notation "Table" => ChargedPhysicalRequest M J target.length (passes + 1) (H ^ 2) T S

noncomputable def physicalUniformLaw (epsilon : BinaryFraction) :
    Measure (PhysicalUniformOutcome (M := M) (J := J) (R := R) target N P H) :=
  if physicalLargeInput N epsilon then
    (physicalFamilyRuntimeLaw (R := R) target N P H
      (physicalCoarseSeedLaw source target N B depth)).map Sum.inr
  else Measure.dirac (Sum.inl ())

noncomputable def physicalUniformAnswer (hH : 0 < H) (bits : ℕ)
    (encode : Sum Key Table → ℕ)
    (outcome : PhysicalUniformOutcome (M := M) (J := J) (R := R) target N P H) : ℕ :=
  match outcome with
  | .inl _ => exactSuffixAnswer source target
  | .inr execution => physicalFamilyRuntimeAnswer source target N P T S H hH bits encode
      (finalTargetState target.length) execution

end Uniform

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedPhysicalUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

open MeasureTheory ProbabilityTheory

noncomputable def computedPhysicalLaw (source target : List ℕ) (N : ℕ) (epsilon : BinaryFraction) :
    Measure (ComputedPhysicalOutcome source target N) :=
  physicalUniformLaw (R := inputHeight N ^ 2) source target N (integerParameters N).P
    (inputHeight N) (integerParameters N).B (computedPhysicalCoarseDepth source target N) epsilon

noncomputable def computedPhysicalAnswer (source target : List ℕ) (N : ℕ)
    (outcome : ComputedPhysicalOutcome source target N) : ℕ :=
  physicalUniformAnswer source target N (integerParameters N).P (integerParameters N).T
    (integerParameters N).S (inputHeight N) (Nat.two_pow_pos _)
    (16384 * inputHeight N + 5) (computedFamilyMemoCode source target N (inputHeight N ^ 2)) outcome

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryDependencyExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dependency tree here is obtained from the requests made by the
finite adaptive program at its actual answers. Local depth/index progress
therefore bounds execution, rather than an independently supplied tree. -/

namespace EditApproximation

open Finset

section Queries

variable {κ : Type*} (depth index : κ → ℕ)
  (program : (key : κ) → FiniteQuery
    {child : κ // depth child + index child < depth key + index key})

variable (progress : ∀ key child, child ∈ queryRequestList depth index program key →
  (depth child < depth key ∧ index child ≤ index key) ∨
  (depth child ≤ depth key ∧ index child < index key))

include progress

def queryDependencyExpansion (root : κ) : DependencyExpansion :=
  DependencyExpansion.build depth index
    (fun key => (querySameRequests depth index program key).length)
    (fun key => (queryEarlierRequests depth index program key).length)
    (fun key i => (querySameRequests depth index program key).get i)
    (fun key i => (queryEarlierRequests depth index program key).get i)
    (querySameRequests_progress depth index program progress)
    (queryEarlierRequests_progress depth index program progress) root

end Queries

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_GlobalQueryCost
attribute [-instance] _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact weighted-cost transport for the full internal refinement body.
In this branch every request is an ordinary table request: parent initial,
child mass, child initial, old history or a current physical child. -/

namespace EditApproximation

def chargedTableWeight {M J ny passes copies T S : ℕ}
    (coarse : ℕ) (weight : PhysicalTableRequest M J ny → ℕ) :
    ChargedPhysicalRequest M J ny passes copies T S → ℕ
  | .inl _ => coarse
  | .inr request => weight request.val

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_GlobalQueryProgress
attribute [-instance] _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete depth/pass-index progress is preserved by the finite-domain
transport. The statement concerns the reads executed at the actual values. -/

namespace EditApproximation

theorem globalSeedRead_keys_progress {M J ny : ℕ} (N T S copies : ℕ)
    (multiplier : ℕ → ℕ) (initial : PhysicalEntry M J ny → ℕ)
    (parent : PhysicalTableRequest M J ny) (state : PhysicalEntry M J ny) (oracle) :
    ∀ key ∈ (globalSeedRead N T S copies multiplier initial parent state).keys oracle,
      PhysicalTableRequest.DependencyProgress T S parent key.val := by
  unfold globalSeedRead
  split_ifs with hnode hpass
  · intro key hk
    exact False.elim (List.not_mem_nil hk)
  · unfold physicalMedianSeedQuery
    apply FiniteQuery.keys_all_collect
    · intro copy _ key hk
      simp only [previousPassRead, FiniteQuery.keys, List.mem_singleton] at hk
      subst key
      exact Or.inr ⟨(previousPassRequest_progress T S copy.val parent (Nat.pos_of_ne_zero hpass) state.2).1.le,
        (previousPassRequest_progress T S copy.val parent (Nat.pos_of_ne_zero hpass) state.2).2⟩
    · intro values key hk
      exact False.elim (List.not_mem_nil hk)
  · intro key hk
    exact False.elim (List.not_mem_nil hk)

section Progress

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

theorem physicalGlobalQuery_keys_progress (request : PhysicalTableRequest M J target.length)
    (oracle) :
    ∀ key ∈ (physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request).keys oracle,
      PhysicalTableRequest.DependencyProgress T S request key.val := by
  rcases request with ⟨pass, copy, node, index, q⟩
  by_cases hj : index ≤ T
  · change ∀ key ∈ (physicalGlobalQuery source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial (PhysicalTableRequest.warmup pass copy node index q)).keys oracle,
        PhysicalTableRequest.DependencyProgress T S _ key.val
    rw [physicalGlobalQuery_warmup source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial pass copy node index hj q]
    apply physicalWarmupRequestQuery_keys_progress
    intro r key hk
    exact globalSeedRead_keys_progress N T S copies multiplier initial _ _ oracle key hk
  · unfold physicalGlobalQuery
    dsimp only
    erw [dite_eq_right (show ¬ ({pass := pass, copy := copy, node := node, index := index, state := q} :
      PhysicalTableRequest M J target.length).index ≤ T from hj)]
    by_cases hbelow : node.1.val < J
    · erw [dite_eq_left hbelow]
      by_cases hshort : (physicalSourceInterval source.length node).hi -
          (physicalSourceInterval source.length node).lo ≤ 1
      · erw [dite_eq_left hshort]
        apply physicalInitialQuery_keys_all
        intro r key hk
        exact globalSeedRead_keys_progress N T S copies multiplier initial _ _ oracle key hk
      · erw [dite_eq_right hshort, FiniteQuery.mapKeys_keys]
        intro key hk
        obtain ⟨child, hc, rfl⟩ := List.mem_map.mp hk
        have h := physicalRefinementDataRequest_keys_progress source target N P F exponent H Q tau
          (refinementFactor (factor pass) F) eta kappa delta pass copy T S (index - T)
          (by omega) node hbelow _ _ q _ child hc
        have heq : PhysicalTableRequest.refinement pass copy node T (index - T) q =
            ({pass := pass, copy := copy, node := node, index := index, state := q} :
              PhysicalTableRequest M J target.length) := by
          unfold PhysicalTableRequest.refinement
          congr 1
          omega
        simpa only [heq] using h
    · erw [dite_eq_right hbelow]
      apply physicalInitialQuery_keys_all
      intro r key hk
      exact globalSeedRead_keys_progress N T S copies multiplier initial _ _ oracle key hk

end Progress

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedQueryProgress
attribute [-instance] _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every actual charged edge either descends at the current index or
uses a strictly earlier index without moving to an ancestor. Coarse
leaves retain their physical depth for source-width accounting. -/

namespace EditApproximation

theorem chargedSeedQuery_keys_earlier {M J ny passes copies T S : ℕ}
    (N : ℕ) (multiplier : ℕ → ℕ)
    (parent : {r : PhysicalTableRequest M J ny // r.Bounded passes copies T S})
    (state : PhysicalEntry M J ny) (oracle) :
    ∀ key ∈ (chargedSeedQuery N multiplier parent state).keys oracle,
      key.val.depth ≤ ChargedPhysicalRequest.depth (Sum.inr parent) ∧
        key.val.index < ChargedPhysicalRequest.index (Sum.inr parent) := by
  unfold chargedSeedQuery
  split_ifs with hn hp
  · intro key hk
    simp only [FiniteQuery.keys, List.mem_singleton] at hk
    subst key
    constructor
    · change J - state.1.1.val ≤ J - parent.val.node.1.val
      rw [hn]
    · change 0 < parent.val.rank T S + 1
      omega
  · apply FiniteQuery.keys_all_collect
    · intro copy _ key hk
      simp only [chargedPreviousRead, FiniteQuery.keys, List.mem_singleton] at hk
      subst key
      have h := previousPassRequest_progress T S copy.val parent.val (Nat.pos_of_ne_zero hp) state.2
      exact ⟨h.1.le, Nat.add_lt_add_right h.2 1⟩
    · intro values key hk
      exact False.elim (List.not_mem_nil hk)
  · intro key hk
    exact False.elim (List.not_mem_nil hk)

theorem chargedWarmupQuery_keys_earlier {α : Type*} [DecidableEq α] {M J passes copies T S : ℕ}
    (source target : List α) (N P F : ℕ) (factor : ℕ → ℚ) (multiplier : ℕ → ℕ)
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S}) (oracle) :
    ∀ key ∈ (chargedWarmupQuery source target N P F factor multiplier parent).keys oracle,
      key.val.depth ≤ ChargedPhysicalRequest.depth (Sum.inr parent) ∧
        key.val.index < ChargedPhysicalRequest.index (Sum.inr parent) := by
  have hseed (q : TargetInterval target.length) :=
    chargedSeedQuery_keys_earlier N multiplier parent (parent.val.node, q) oracle
  unfold chargedWarmupQuery
  split_ifs with hz hb hs
  · exact physicalInitialQuery_keys_all source target N P F _ _ _ _ oracle _ hseed
  · exact physicalInitialQuery_keys_all source target N P F _ _ _ _ oracle _ hseed
  · unfold physicalWarmupStepQuery
    apply localWarmupStepQuery_keys_all
    · intro q
      exact physicalInitialQuery_keys_all source target N P F _ _ _ _ oracle _ hseed
    · intro input key hk
      simp only [chargedWarmupChild, FiniteQuery.keys, List.mem_singleton] at hk
      subst key
      have h := PhysicalTableRequest.warmup_previous_child_progress parent.val.pass parent.val.copy T S
        parent.val.index parent.val.node hb input.1 parent.val.state input.2 (Nat.pos_of_ne_zero hz)
      exact ⟨h.1.le, Nat.add_lt_add_right h.2 1⟩
  · exact physicalInitialQuery_keys_all source target N P F _ _ _ _ oracle _ hseed

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRandomRequestProgress
attribute [-instance] _root_.OAI.EditApproximation.PhysicalTableRequest.decidableBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Adding source reads preserves the actual tree/index progress of all
physical table dependencies. Source coordinates have no table dependency. -/

namespace EditApproximation

 theorem physicalRandomDataRequest_keys_progress {σ α : Type*} (source target : List α)
    {M J : ℕ} [NeZero M] (N P F exponent H Q : ℕ) (tau a eta kappa delta : ℚ)
    (pass copy T S t : ℕ) (ht : 0 < t)
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (readGroup : GroupScalarKey M F Q → FiniteQuery σ)
    (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
    (q : TargetInterval target.length) (oracle) :
    ∀ key ∈ (physicalRandomDataRequestQuery source target N P F exponent H Q tau a eta kappa delta
      pass copy T S t ht node hbelow readGroup readInteger q).keys oracle,
      match key with
      | .inl _ => True
      | .inr table => PhysicalTableRequest.DependencyProgress T S
          (PhysicalTableRequest.refinement pass copy node T t q) table.val := by
  unfold physicalRandomDataRequestQuery
  apply localRandomDataQuery_keys_all
  · intro input
    apply FiniteQuery.keys_all_mapKeys
    intro key _
    trivial
  · intro input range
    apply FiniteQuery.keys_all_mapKeys
    intro key _
    trivial
  · intro input
    apply FiniteQuery.keys_all_mapKeys
    intro key hk
    unfold physicalRefinementEarlierQuery at hk
    split_ifs at hk with hs
    · simp only [FiniteQuery.keys, List.mem_singleton] at hk
      subst key
      exact PhysicalTableRequest.refinement_child_earlier_progress pass copy T S t input.2.1
        node hbelow input.1 q input.2.2 hs
    · exact False.elim (List.not_mem_nil hk)
  · intro input
    apply FiniteQuery.keys_all_mapKeys
    intro key hk
    simp only [physicalRefinementCurrentQuery, FiniteQuery.keys, List.mem_singleton] at hk
    subst key
    exact PhysicalTableRequest.refinement_child_same_progress pass copy T S t node hbelow input.1 q input.2
  · intro r
    apply FiniteQuery.keys_all_mapKeys
    intro key hk
    exact physicalRefinementWarmupRead_keys_progress pass copy T S t ht node q node le_rfl
      0 (Nat.zero_le T) r _ key hk
  · intro input
    apply FiniteQuery.keys_all_mapKeys
    unfold physicalRefinementMassQuery
    apply FiniteQuery.keys_all_collect
    · intro j _ key hk
      exact physicalRefinementWarmupRead_keys_progress pass copy T S t ht node q
        (physicalChild node hbelow input.1) _ j.val (Nat.le_of_lt j.isLt) input.2 _ key hk
    · intro values key hk
      exact False.elim (List.not_mem_nil hk)
  · intro input
    apply FiniteQuery.keys_all_mapKeys
    intro key hk
    exact physicalRefinementWarmupRead_keys_progress pass copy T S t ht node q
      (physicalChild node hbelow input.1) _ 0 (Nat.zero_le T) input.2 _ key hk

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRandomGlobalProgress
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Progress

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (initial : PhysicalEntry M J target.length → ℕ)

 theorem physicalRandomGlobalQuery_keys_progress (request : PhysicalTableRequest M J target.length)
    (oracle) :
    ∀ key ∈ (physicalRandomGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request).keys oracle,
      match key with
      | .inl _ => True
      | .inr table => PhysicalTableRequest.DependencyProgress T S request table.val := by
  unfold physicalRandomGlobalQuery
  by_cases ha : T < request.index ∧ request.node.1.val < J ∧
      ¬ (physicalSourceInterval source.length request.node).hi -
        (physicalSourceInterval source.length request.node).lo ≤ 1
  · rw [dite_eq_left ha, FiniteQuery.mapKeys_keys]
    intro key hk
    obtain ⟨other, ho, rfl⟩ := List.mem_map.mp hk
    have hi := physicalRandomDataRequest_keys_progress source target N P F exponent H Q tau
      (refinementFactor (factor request.pass) F) eta kappa delta request.pass request.copy T S
      (request.index - T) (Nat.sub_pos_of_lt ha.1) request.node ha.2.1
      (readGroup request.pass request.copy ⟨request.node, ha.2.1⟩ (Fin.ofNat R (request.index - T - 1)))
      (readInteger request.pass request.copy ⟨request.node, ha.2.1⟩ (Fin.ofNat R (request.index - T - 1)))
      request.state _ other ho
    have heq : PhysicalTableRequest.refinement request.pass request.copy request.node
        T (request.index - T) request.state = request := by
      unfold PhysicalTableRequest.refinement
      have ht : T + (request.index - T) = request.index :=
        Nat.add_sub_of_le (Nat.le_of_lt ha.1)
      rw [ht]
    cases other with
    | inl key => trivial
    | inr table => simpa only [Sum.map_inr, heq] using hi
  · rw [dite_eq_right ha, FiniteQuery.mapKeys_keys]
    intro key hk
    obtain ⟨other, ho, rfl⟩ := List.mem_map.mp hk
    rw [physicalGlobalQuery_inactive (R := R) source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta initial (fun _ _ _ _ _ _ _ _ => 0) (fun _ _ _ _ _ _ => 0) request ha] at ho
    exact physicalGlobalQuery_keys_progress (R := R) source target N P F exponent H Q T S copies
      factor multiplier tau eta kappa delta (fun _ _ _ _ _ _ _ _ => 0) (fun _ _ _ _ _ _ => 0)
      initial request _ other ho

end Progress

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRandomBoundedCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Bounded

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (initial : PhysicalEntry M J target.length → ℕ)
  (sourceValue : σ → ℚ) (tableValue : PhysicalTableRequest M J target.length → ℚ)

 theorem physicalRandomBoundedQuery_progress
    (request : {request : PhysicalTableRequest M J target.length // request.Bounded passes copies T S}) :
    ∀ key ∈ (physicalRandomBoundedQuery source target N P F exponent H Q T S passes copies
      factor multiplier tau eta kappa delta readGroup readInteger initial request).keys
        (Sum.elim sourceValue (fun child => tableValue child.val.val)),
      match key with
      | .inl _ => True
      | .inr child => PhysicalTableRequest.DependencyProgress T S request.val child.val.val := by
  unfold physicalRandomBoundedQuery
  have hall := SourceRanked.restrictBody_keys_all _ _ _ sourceValue tableValue (fun _ => True)
    (PhysicalTableRequest.DependencyProgress T S request.val) request
    (physicalRandomGlobalQuery_keys_bounded source target N P F exponent H Q T S passes copies
      factor multiplier tau eta kappa delta readGroup readInteger initial request.val request.property _)
    (by
      intro key hk
      have h := physicalRandomGlobalQuery_keys_progress source target N P F exponent H Q T S copies
        factor multiplier tau eta kappa delta readGroup readInteger initial request.val
        (Sum.elim sourceValue (fun child => tableValue child.val)) key hk
      cases key <;> exact h)
  intro key hk
  have h := hall key hk
  cases key <;> exact h

end Bounded

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedRandomProgress
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual mixed requests retain the charged physical depth/index progress.
This statement holds for every returned source and table value. -/

namespace EditApproximation

section Global

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (initial : PhysicalEntry M J target.length → ℕ)
  (sourceAnswer : σ → ℚ)
  (answer : ChargedPhysicalRequest M J target.length passes copies T S → ℚ)

 theorem chargedRandomGlobalQuery_keys_progress
    (request : ChargedPhysicalRequest M J target.length passes copies T S) :
    ∀ key ∈ (chargedRandomGlobalQuery source target N P F exponent H Q T S passes copies
      factor multiplier tau eta kappa delta readGroup readInteger initial request).keys
        (Sum.elim sourceAnswer (fun child => answer child.val)),
      match key with
      | .inl _ => True
      | .inr child => ChargedPhysicalRequest.DependencyProgress request child.val := by
  cases request with
  | inl entry =>
    intro key hk
    exact False.elim (List.not_mem_nil hk)
  | inr parent =>
    unfold chargedRandomGlobalQuery
    dsimp only
    split_ifs with hi hb hs
    · apply FiniteQuery.keys_all_mapKeys
      intro key hk
      exact Or.inr (chargedWarmupQuery_keys_earlier source target N P F factor multiplier parent _ key hk)
    · apply FiniteQuery.keys_all_mapKeys
      intro key hk
      apply Or.inr
      apply physicalInitialQuery_keys_all source target N P F _ _ _ _ _ _ _ key hk
      intro q
      exact chargedSeedQuery_keys_earlier N multiplier parent (parent.val.node, q) _
    · rw [FiniteQuery.mapKeys_keys]
      intro key hk
      obtain ⟨child, hc, rfl⟩ := List.mem_map.mp hk
      let tableMap :
          {child : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S} //
            child.val.combinedRank T S < parent.val.combinedRank T S} →
          {child : ChargedPhysicalRequest M J target.length passes copies T S //
            child.rank < ChargedPhysicalRequest.rank (.inr parent)} :=
        fun child => ⟨.inr child.val,
          ChargedPhysicalRequest.table_rank_lt parent child.val child.property⟩
      have horacle : (Sum.elim sourceAnswer (fun child => answer child.val)) ∘
          Sum.map (id : σ → σ) tableMap =
          Sum.elim sourceAnswer (fun child => answer (Sum.inr child.val)) := by
        funext key
        cases key <;> rfl
      rw [horacle] at hc
      have hp := physicalRandomBoundedQuery_progress source target N P F exponent H Q T S passes copies
        factor multiplier tau eta kappa delta readGroup readInteger initial sourceAnswer
        (fun r => if hr : r.Bounded passes copies T S then answer (.inr ⟨r, hr⟩) else 0)
        parent
      cases child with
      | inl key => trivial
      | inr child =>
        apply ChargedPhysicalRequest.table_progress
        apply hp (.inr child)
        convert hc using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        funext key
        cases key with
        | inl key => rfl
        | inr key => simp only [Sum.elim_inr, dite_eq_left key.val.property]
    · apply FiniteQuery.keys_all_mapKeys
      intro key hk
      apply Or.inr
      apply physicalInitialQuery_keys_all source target N P F _ _ _ _ _ _ _ key hk
      intro q
      exact chargedSeedQuery_keys_earlier N multiplier parent (parent.val.node, q) _

end Global

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedRandomExpansion
attribute [-instance] _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Expansion

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    CellGroupDraws M (inputSmallLog N) (inputSmallLog N ^ 80))
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

variable
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    GroupScalarKey M (inputSmallLog N) (inputSmallLog N ^ 80) → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (sourceAnswer : σ → ℚ)

local notation "mixedProgram" => chargedRandomGlobalQuery source target N P (inputSmallLog N)
  (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
  tau eta kappa delta readGroup readInteger initial
local notation "program" => SourceRanked.projectedBody ChargedPhysicalRequest.rank mixedProgram sourceAnswer
local notation "values" => chargedRequestValue source target N P (inputSmallLog N)
  (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
  tau eta kappa delta group integer initial
local notation "depth" => @ChargedPhysicalRequest.depth M J target.length passes copies T S
local notation "index" => @ChargedPhysicalRequest.index M J target.length passes copies T S

variable (hbody : ∀ (request : ChargedPhysicalRequest M J target.length passes copies T S),
  (chargedRandomGlobalQuery source target N P (inputSmallLog N)
    (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
    tau eta kappa delta readGroup readInteger initial request).value
    (Sum.elim sourceAnswer (fun child : {child : ChargedPhysicalRequest M J target.length passes copies T S //
      child.rank < request.rank} => chargedRequestValue source target N P (inputSmallLog N)
        (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
        tau eta kappa delta group integer initial child.val)) =
    chargedRequestValue source target N P (inputSmallLog N)
      (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
      tau eta kappa delta group integer initial request)

include hbody

 theorem chargedRandomRequestList_progress (root child : ChargedPhysicalRequest M J target.length passes copies T S)
    (hchild : child ∈ queryRequestList depth index program root) :
    (depth child < depth root ∧ index child ≤ index root) ∨
      (depth child ≤ depth root ∧ index child < index root) := by
  have hvalue := rankedProgramValue_eq ChargedPhysicalRequest.rank program values
    (SourceRanked.projectedBody_value ChargedPhysicalRequest.rank mixedProgram sourceAnswer values hbody)
  change child ∈ ((program root).keys
    (fun key => rankedProgramValue ChargedPhysicalRequest.rank program key.val)).map Subtype.val at hchild
  simp only [hvalue] at hchild
  obtain ⟨key, hk, rfl⟩ := List.mem_map.mp hchild
  apply FiniteQuery.eraseSources_keys_all sourceAnswer
    (fun child => values child.val) (mixedProgram root)
    (fun child => ChargedPhysicalRequest.DependencyProgress root child.val) ?_ key hk
  intro next hn
  have hp := chargedRandomGlobalQuery_keys_progress source target N P (inputSmallLog N)
    (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
    tau eta kappa delta readGroup readInteger initial sourceAnswer values root next hn
  cases next <;> exact hp

 noncomputable def chargedRandomDependencyTree (root : ChargedPhysicalRequest M J target.length passes copies T S) :
    DependencyExpansion :=
  queryDependencyExpansion depth index program
    (chargedRandomRequestList_progress source target N P H T S passes copies factor multiplier
      tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody) root

end Expansion

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilyProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The actual scalar family supplies the body-value and source-read
bounds required by the mixed source/table dependency analysis. -/

namespace EditApproximation

section Program

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (initial : PhysicalEntry M J target.length → ℕ)



variable (hP : 0 < P)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies)

noncomputable def physicalFamilyRequestValue :=
  chargedRequestValue source target N P F exponent H Q T S (passes + 1) copies
    factor multiplier tau eta kappa delta
    (physicalFamilyGroup target N P F exponent H Q passes copies draw)
    (physicalFamilyInteger source target N P F exponent H Q T S passes copies
      factor multiplier tau eta kappa delta hP draw initial) initial

 theorem physicalFamilyProgram_value
    (request : ChargedPhysicalRequest M J target.length (passes + 1) copies T S) :
    (physicalFamilyProgram source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta initial request).value
      (Sum.elim (physicalFamilyAnswer target N P F exponent H Q passes copies draw)
        (fun child => physicalFamilyRequestValue source target N P F exponent H Q T S passes copies
          factor multiplier tau eta kappa delta initial hP draw child.val)) =
    physicalFamilyRequestValue source target N P F exponent H Q T S passes copies
      factor multiplier tau eta kappa delta initial hP draw request := by
  exact chargedRandomGlobalQuery_value source target N P F exponent H Q T S (passes + 1)
    copies factor multiplier tau eta kappa delta _ _ initial _ _ _
    (physicalRandomBoundedQuery_localValue source target N P F exponent H Q T S (passes + 1)
      copies factor multiplier tau eta kappa delta _ _ initial _ _ _
      (physicalFamilyGroupRead_value target N P F exponent H Q passes copies draw)
      (physicalFamilyOnlineRead_value source target N P F exponent H Q T S passes copies
        factor multiplier tau eta kappa delta hP draw initial)) request

end Program

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilyWork
attribute [-instance] _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Work

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (initial : PhysicalEntry M J target.length → ℕ) (hPpos : 0 < P)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P (inputSmallLog N) (40 * smallLogExponent N) H (inputSmallLog N ^ 80) passes copies)

local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "group" => physicalFamilyGroup target N P ell exponent H (ell ^ 80) passes copies draw
local notation "integer" => physicalFamilyInteger source target N P ell exponent H (ell ^ 80)
  T S passes copies factor multiplier tau eta kappa delta hPpos draw initial
local notation "readGroup" => physicalFamilyGroupRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "readInteger" => physicalFamilyOnlineRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "answer" => physicalFamilyAnswer target N P ell exponent H (ell ^ 80) passes copies draw
local notation "bodyValue" => physicalFamilyProgram_value source target N P ell exponent H (ell ^ 80)
  T S passes copies factor multiplier tau eta kappa delta initial hPpos draw

noncomputable def physicalFamilyDependencyTree
    (root : ChargedPhysicalRequest M J target.length (passes + 1) copies T S) : DependencyExpansion :=
  chargedRandomDependencyTree source target N P H T S (passes + 1) copies factor multiplier
    tau eta kappa delta group integer initial readGroup readInteger answer bodyValue root

end Work

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedPhysicalWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

open Filter MeasureTheory









noncomputable def computedFamilyTree (source target : List ℕ) (N : ℕ)
    (input : ComputedFamilyInput source target N) : DependencyExpansion :=
  physicalFamilyDependencyTree source target N (integerParameters N).P (inputHeight N)
    (integerParameters N).T (integerParameters N).S (computedSeedPassCount N) (inputHeight N ^ 2)
    (scheduledSeedFactor N) (scheduledSeedMultiplier N)
    (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).eta
    (rationalParameters (inputSmallLog N)).kappa (rationalParameters (inputSmallLog N)).delta
    (clampedSeedNat input.1) (computedParameterP_pos N) input.2
    (localFinalRootRequest target N (integerParameters N).T (integerParameters N).S
      (inputHeight N) (Nat.two_pow_pos _) (finalTargetState target.length))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCoarseExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

open MeasureTheory





instance computedPhysicalCoarseLaw_probability (source target : List ℕ) (N : ℕ) :
    IsProbabilityMeasure (computedPhysicalCoarseLaw source target N) := by
  unfold computedPhysicalCoarseLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedExecutionLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The coarse sampler execution and its returned seed share one probability space. -/

namespace EditApproximation

open MeasureTheory








instance computedExecutionLaw_probability (source target : List ℕ) (N : ℕ) :
    IsProbabilityMeasure (computedExecutionLaw source target N) := by
  unfold computedExecutionLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)



instance computedFullOutcome_measurableSingleton (source target : List ℕ) (N : ℕ) :
    MeasurableSingletonClass (ComputedFullOutcome source target N) := by
  refine ⟨fun outcome => ?_⟩
  exact measurableSet_sum_iff.mpr
    ⟨(Set.to_countable _).measurableSet, (Set.to_countable _).measurableSet⟩



instance computedFullLaw_probability (source target : List ℕ) (N : ℕ) (epsilon : BinaryFraction) :
    IsProbabilityMeasure (computedFullLaw source target N epsilon) := by
  classical
  unfold computedFullLaw
  split
  · exact Measure.isProbabilityMeasure_map measurable_inr.aemeasurable
  · infer_instance

noncomputable def computedFullProjection (source target : List ℕ) (N : ℕ) :
    ComputedFullOutcome source target N → ComputedPhysicalOutcome source target N
  | .inl _ => .inl ()
  | .inr execution => .inr (computedExecutionProjection source target N execution)

noncomputable def computedFullAnswer (source target : List ℕ) (N : ℕ)
    (outcome : ComputedFullOutcome source target N) : ℕ :=
  computedPhysicalAnswer source target N (computedFullProjection source target N outcome)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_OccurrencePrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Cached binary position counts. Inserting a position and counting positions
strictly below a boundary both follow one root-to-leaf path. Counts are stored
at internal nodes, so a prefixCount query does not traverse a whole interval. -/

namespace EditApproximation



namespace PositionCounts









theorem prefixWithWork_spec (tree : PositionCounts) (d t : ℕ) :
    tree.prefixWithWork d t = (tree.prefixCount d t, 2 * d + 1) := by
  induction d generalizing tree t with
  | zero => rfl
  | succ d ih =>
    simp only [prefixWithWork, prefixCount]
    split_ifs <;> rw [ih] <;> simp only <;> congr 1

def nodes : PositionCounts → ℕ
  | .empty => 0
  | .node _ l r => 1 + l.nodes + r.nodes

end PositionCounts

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_OccurrenceIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A symbol dictionary of cached position tries. The target is enumerated
once; interval occurrence queries use two logarithmic prefix counts. -/

namespace EditApproximation



def occurrencePrefix (table : BinaryMemo PositionCounts) (symbolBits positionBits a t : ℕ) : ℕ :=
  ((table.lookup (binaryMemoKey symbolBits a)).getD .empty).prefixCount positionBits t

def occurrenceQuery (table : BinaryMemo PositionCounts) (symbolBits positionBits a lo hi : ℕ) : Bool :=
  decide (occurrencePrefix table symbolBits positionBits a lo <
    occurrencePrefix table symbolBits positionBits a hi)



theorem occurrenceQueryWithWork_spec (table : BinaryMemo PositionCounts)
    (symbolBits positionBits a lo hi : ℕ) :
    occurrenceQueryWithWork table symbolBits positionBits a lo hi =
      (occurrenceQuery table symbolBits positionBits a lo hi, 2 * symbolBits + 4 * positionBits + 5) := by
  simp only [occurrenceQueryWithWork, BinaryMemo.lookupCosted_spec,
    PositionCounts.prefixWithWork_spec, binaryMemoKey_length, occurrenceQuery, occurrencePrefix]
  congr 1
  ring

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_OccurrenceLeaf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Constant-size leaf descriptors use the preprocessed occurrence index.
The target interval is represented by endpoints; it is never copied or
scanned while evaluating a singleton leaf. -/

namespace EditApproximation

def indexedSingletonCost (table : BinaryMemo PositionCounts)
    (symbolBits positionBits a lo hi : ℕ) : ℕ :=
  if lo = hi then 1 else hi - lo -
    if occurrenceQuery table symbolBits positionBits a lo hi = true then 1 else 0

def indexedLeafCost (table : BinaryMemo PositionCounts)
    (symbolBits positionBits : ℕ) (symbol : Option ℕ) (lo hi : ℕ) : ℕ :=
  match symbol with
  | none => hi - lo
  | some a => indexedSingletonCost table symbolBits positionBits a lo hi

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ParameterNumericalConstruction
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.reduceOnlineIntegerWithWork_value _root_.OAI.EditApproximation.triangularChoiceWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation



 @[simp] theorem onlineMassWithWork_value (M P H : ℕ) :
    (onlineMassWithWork M P H).1 = localOnlineMassBound M P H := by
  simp only [onlineMassWithWork, parameterPowerWithWork_spec, localOnlineMassBound]
  rw [← optimizerTriangularMass_twice, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_MemoCodeWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Address generation is charged separately from binary trie traversal.
The loops visit only coordinates in a key, never the ambient key space. -/
namespace EditApproximation



 theorem treeLayerCodeWithWork_cost (M d : ℕ) (path : TreeLayer M d) :
    (treeLayerCodeWithWork M d path).2 = 3 * d + 1 := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [treeLayerCodeWithWork, ih]; omega



 @[simp] theorem computedFamilyMemoCodeWithWork_value (source target : List ℕ) (N R : ℕ)
    (key : Sum (ComputedFamilyScalarKey source target N R) (ComputedFamilyTableKey source target N)) :
    (computedFamilyMemoCodeWithWork source target N R key).1 = computedFamilyMemoCode source target N R key := by
  cases key <;> simp only [computedFamilyMemoCodeWithWork, computedFamilyMemoCode,
    SourceRanked.keyCode, physicalFamilyCodeWithWork_value, chargedPhysicalCodeWithWork_value]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedRetainedValues
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

noncomputable def computedFamilyTableValue (source target : List ℕ) (N : ℕ)
    (input : ComputedFamilyInput source target N) (key : ComputedFamilyTableKey source target N) : ℚ :=
  physicalFamilyRequestValue source target N (integerParameters N).P (inputSmallLog N)
    (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80) (integerParameters N).T
    (integerParameters N).S (computedSeedPassCount N) (inputHeight N ^ 2)
    (scheduledSeedFactor N) (scheduledSeedMultiplier N)
    (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).eta
    (rationalParameters (inputSmallLog N)).kappa (rationalParameters (inputSmallLog N)).delta
    (clampedSeedNat input.1) (computedParameterP_pos N) input.2 key

noncomputable def computedFamilyExpectedValue (source target : List ℕ) (N : ℕ)
    (input : ComputedFamilyInput source target N) :
    Sum (ComputedFamilyScalarKey source target N (inputHeight N ^ 2))
      (ComputedFamilyTableKey source target N) → ℚ :=
  Sum.elim (fun key => (input.2 key).val) (computedFamilyTableValue source target N input)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedRandomCoarseOracle
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed accepted source family leaves a nonanticipating coarse query:
coarse values enter only when the corresponding leaf is requested. -/

namespace EditApproximation

section Coarse

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R → (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (sourceAnswer : σ → ℚ)

/-- The flattened program receives each coarse answer from an explicit
external read. The constant zero here is never used as a seed answer. -/
noncomputable def chargedRandomCoarseQuery (root : ChargedPhysicalRequest M J target.length passes copies T S) :
    FiniteQuery (PhysicalEntry M J target.length) :=
  match root with
  | .inl entry => .read entry FiniteQuery.done
  | .inr parent =>
    (SourceRanked.projectedBody ChargedPhysicalRequest.rank
      (chargedRandomGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
        tau eta kappa delta readGroup readInteger (fun _ => 0)) sourceAnswer (.inr parent)).substitute
        (fun child => chargedRandomCoarseQuery child.val)
termination_by root.rank
decreasing_by exact child.property

end Coarse

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCoarseBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Polynomial coarse-sampling budgets for the computed dimensions. -/

namespace EditApproximation
open MeasureTheory Filter

section Coarse
variable {M J R B : ℕ} [NeZero M] [NeZero R] [NeZero B]
  (source target : List ℕ) (N : ℕ)
  (depth : PhysicalEntry M J target.length → ℕ)
  (encode : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
    (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2))
    (ChargedPhysicalRequest M J target.length (computedSeedPassCount N + 1)
      (inputHeight N ^ 2) (integerParameters N).T (integerParameters N).S) → ℕ)



 def SymbolicComputedCoarseBudget (budget : ℝ) : Prop :=
  ∀ draw, integral (coarseFullSeedMeasure B depth
    (fun entry => physicalSource source entry.1)
    (fun entry => substring target entry.2.lo entry.2.hi))
      (symbolicComputedCoarseWork (B := B) source target N depth encode draw) ≤ budget

end Coarse
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedPhysicalCoarseWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

open MeasureTheory Filter




def ComputedPhysicalCoarseBudget (source target : List ℕ) (N : ℕ) (budget : ℝ) : Prop :=
  SymbolicComputedCoarseBudget (M := (integerParameters N).M)
    (J := intervalTreeDepth (integerParameters N).M source.length) (R := inputHeight N ^ 2)
    (B := (integerParameters N).B) source target N (computedPhysicalCoarseDepth source target N)
    (computedFamilyMemoCode source target N (inputHeight N ^ 2)) budget

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalCoarseInputWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Coarse
variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (initial : PhysicalEntry M J target.length → ℕ) (hP : 0 < P)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P (inputSmallLog N) (40 * smallLogExponent N) H (inputSmallLog N ^ 80) passes copies)

local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "Table" => ChargedPhysicalRequest M J target.length (passes + 1) copies T S
local notation "readGroup" => physicalFamilyGroupRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "readInteger" => physicalFamilyOnlineRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "answer" => physicalFamilyAnswer target N P ell exponent H (ell ^ 80) passes copies draw

/-- Source scans and a constant setup charge for each first coarse request. -/
noncomputable def physicalFamilyCoarseInputWork (bits : ℕ) (encode : Sum Key Table → ℕ)
    (root : Table) : ℝ :=
  let result := chargedRandomMemoEvaluate source target N P ell exponent H (ell ^ 80)
    T S (passes + 1) copies factor multiplier tau eta kappa delta readGroup readInteger initial
    answer bits encode root
  ∑ entry, selectionIndicator (Sum.inr (Sum.inl entry) ∈ result.freshKeys) *
    ((physicalSource source entry.1).length + 1 : ℕ)

end Coarse
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCoarseInputWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter MeasureTheory

noncomputable def computedFamilyCoarseInputWork (source target : List ℕ) (N : ℕ)
    (input : ComputedFamilyInput source target N) : ℝ :=
  physicalFamilyCoarseInputWork source target N (integerParameters N).P (inputHeight N)
    (integerParameters N).T (integerParameters N).S (computedSeedPassCount N) (inputHeight N ^ 2)
    (scheduledSeedFactor N) (scheduledSeedMultiplier N)
    (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).eta
    (rationalParameters (inputSmallLog N)).kappa (rationalParameters (inputSmallLog N)).delta
    (clampedSeedNat input.1) input.2 (16384 * inputHeight N + 5)
    (computedFamilyMemoCode source target N (inputHeight N ^ 2))
    (computedFinalRoot source target N)

noncomputable def computedExecutionCoarseInputWork (source target : List ℕ) (N : ℕ)
    (execution : ComputedExecutionOutcome source target N) : ℝ :=
  computedFamilyCoarseInputWork source target N (computedExecutionAccepted source target N execution)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseReadTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

/-- A source descriptor is expanded by index arithmetic. No sliced or padded
list is allocated. The function is the original stored input's read operation. -/
def coarseReadTree (B : ℕ) {α : Type*} :
    (d : ℕ) → (ℕ → Option α) → CoarseSourceTree B α d
  | 0, read => .leaf (read 0)
  | d + 1, read => .branch (fun i =>
      coarseReadTree B d (fun j => read (i.val * B ^ d + j)))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryScalarDispatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The physical scalar sources locate a dyadic scale by a counted scan.
The scan computes the original first index and works also for absent scales. -/

namespace EditApproximation



@[simp] theorem queryNaturalIndexWithWork_value (a : ℕ) (xs : List ℕ) :
    (queryNaturalIndexWithWork a xs).1 = xs.idxOf a := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    unfold queryNaturalIndexWithWork
    by_cases hab : a = b
    · subst b
      rw [ite_eq_left ((naturalEqualWithWork_value a a).mpr rfl)]
      simp
    · rw [ite_eq_right (fun h => hab ((naturalEqualWithWork_value a b).mp h))]
      simp only [ih, List.idxOf_cons, beq_iff_eq]
      rw [beq_eq_false_iff_ne.mpr (Ne.symm hab)]; rfl



@[simp] theorem queryScaleDispatchWithWork_value (N b : ℕ) :
    (queryScaleDispatchWithWork N b).1 = (dyadicScales N).idxOf b := by
  simp only [queryScaleDispatchWithWork, queryNaturalIndexWithWork_value, dyadicScalesWithWork_value]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryPhysicalScalarGuards
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.queryNaturalLEWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Executed natural-word guards for finite physical source requests. -/

namespace EditApproximation



@[simp] theorem queryScalePresentWithWork_value (N b : ℕ) :
    (queryScalePresentWithWork N b).1 = true ↔ b ∈ dyadicScales N := by
  simp only [queryScalePresentWithWork, decide_eq_true_eq, binaryNaturalCompareWithWork_lt,
    queryScaleDispatchWithWork_value]
  have hl : (dyadicScales N).length = max 1 N.bits.length := by
    rw [← dyadicScalesWithWork_value N]
    simp only [dyadicScalesWithWork, arithmeticMapWithWork_value, List.length_map, List.length_range]
  rw [← hl]
  exact List.idxOf_lt_length_iff



@[simp] theorem queryCellValidWithWork_value (n exponent : ℕ) (cell : ℕ × ℕ) :
    (queryCellValidWithWork n exponent cell).1 = true ↔
      cell.1 ≤ n * 2 ^ exponent ∧ cell.2 ≤ n * 2 ^ exponent := by
  simp only [queryCellValidWithWork, Bool.and_eq_true, wordLEWithWork_value, bitWordValue_bits,
    binaryNaturalMulWithWork_value, powerTwoWord_value]



@[simp] theorem queryRangeValidWithWork_value (B range : ℕ) :
    (queryRangeValidWithWork B range).1 = true ↔ 0 < range ∧ range ≤ B := by
  simp only [queryRangeValidWithWork, Bool.and_eq_true, decide_eq_true_eq,
    binaryNaturalCompareWithWork_lt, wordLEWithWork_value, bitWordValue_bits]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryChargedFamily
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! All physical table branches run Boolean arithmetic and issue
address-charged adaptive requests.  Coarse entries are supplied by the
separately executed coarse initializer. -/

namespace EditApproximation

section Family
variable {M J R passes copies T S : ℕ} [NeZero M] [NeZero R]
  (source target : List ℕ) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction) (multiplier : ℕ → ℕ)
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)



def queryChargedFamilyTable
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S}) :
    BitQuery (ChargedFamilyQueryKey (R := R) target N P F exponent H Q (.inr parent)) BinaryFraction :=
  let index := wordLEWithWork parent.val.index.bits T.bits
  .charge (index.2 + 1)
    (if hi : index.1 = true then
      BitQuery.mapKeysWithWork (fun key => (Sum.inr key, 1))
        (queryChargedWarmup source target N P F (A parent.val.pass) (a parent.val.pass) multiplier
          parent occurrence symbolBits positionBits)
    else let depth := binaryNaturalCompareWithWork parent.val.node.1.val J
      .charge (depth.2 + 1)
        (if hb : depth.1 = .lt then
          let interval := physicalSourceInterval source.length parent.val.node
          let length := saturatingSubtractWithWork interval.hi interval.lo
          let short := wordLEWithWork length.1 [true]
          .charge (length.2 + short.2 + 1)
            (if short.1 then
              BitQuery.mapKeysWithWork (fun key => (Sum.inr key, 1))
                (queryPhysicalInitial source target N P F (A parent.val.pass) (a parent.val.pass)
                  multiplier parent occurrence symbolBits positionBits parent.val.state)
            else BitQuery.mapKeysWithWork
              (fun key => (Sum.map id (fun child =>
                ⟨Sum.inr child.val, ChargedPhysicalRequest.table_rank_lt parent child.val child.property⟩)
                key, 1))
              (queryFamilyBoundedActive (R := R) source target N P F exponent H Q eM eF hP hM hF
                tau (a parent.val.pass) eta kappa delta T S passes copies parent
                (Nat.lt_of_not_ge (fun h => hi ((queryNaturalLEWithWork_value parent.val.index T).mpr h)))
                ((binaryNaturalCompareWithWork_lt _ _).mp hb)))
        else BitQuery.mapKeysWithWork (fun key => (Sum.inr key, 1))
          (queryPhysicalInitial source target N P F (A parent.val.pass) (a parent.val.pass)
            multiplier parent occurrence symbolBits positionBits parent.val.state)))

def queryChargedFamilyGlobal
    (coarse : PhysicalEntry M J target.length → BinaryFraction × ℕ)
    (request : ChargedPhysicalRequest M J target.length (passes + 1) copies T S) :
    BitQuery (ChargedFamilyQueryKey (R := R) target N P F exponent H Q request) BinaryFraction :=
  match request with
  | .inl entry => BitQuery.compute (coarse entry)
  | .inr parent => queryChargedFamilyTable (R := R) source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits parent

end Family
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryFamilyMemo
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! One binary memo stores independent scalar draws, coarse values, and
all recursive tables.  The raw implementation preserves the exact
reference trace; normalization is justified on its reachable values. -/

namespace EditApproximation

section Family
variable {M J R passes copies T S : ℕ} [NeZero M] [NeZero R]
  (source target : List ℕ) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction) (multiplier : ℕ → ℕ)
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
  (coarse : PhysicalEntry M J target.length → BinaryFraction × ℕ)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies)





def queryFamilyMemoRaw (key : QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q) :=
  SourceRanked.bitBody ChargedPhysicalRequest.rank
    (queryChargedFamilyGlobal (R := R) source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse)
    (queryFamilySourceWordWithWork target N P F exponent H Q draw) key

end Family
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryMemo
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

/-- The same materialized binary constants are shared by all requests of a pass. -/




theorem computedQueryBase_value (N : ℕ) :
    bitWordValue (computedQueryBase N) = inputSmallLog N ^ 10 + 1 := by
  simp only [computedQueryBase, refinementBaseWithWork_value, bitWordValue_bits]

theorem computedQueryBase_pos (N : ℕ) : 0 < bitWordValue (computedQueryBase N) := by
  rw [computedQueryBase_value]
  omega

attribute [local instance] OAI.EditApproximation.queryArityNeZero

attribute [local instance] OAI.EditApproximation.queryRoundsNeZero

/-- Coarse words here are the stored outputs of the separately charged coarse
initializer. The adaptive mixed memo consumes them on demand. -/
def computedQueryMemoRaw (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) (key : ComputedFamilyMemoKey source target N) :=
  queryFamilyMemoRaw source target N (integerParameters N).P (inputSmallLog N)
    (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
    (heightExponent N / 20) (smallLogExponent N) (computedParameterP_pos N) rfl rfl
    (fun pass => (scheduledSeedWordWithWork N pass).1)
    (fun pass => (computedQueryParameters N pass).factor)
    (computedQueryParameters N 0).tau (computedQueryParameters N 0).eta
    (computedQueryParameters N 0).kappa (computedQueryParameters N 0).delta
    (scheduledSeedMultiplier N) occurrence symbolBits positionBits
    (fun entry => (BinaryFraction.nat (clampedSeedNat input.1 entry), 0)) input.2 key

def computedQueryMemoNormalized (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) :
    (key : ComputedFamilyMemoKey source target N) → BitQuery
      {child : ComputedFamilyMemoKey source target N //
        SourceRanked.rank ChargedPhysicalRequest.rank child < SourceRanked.rank ChargedPhysicalRequest.rank key}
      BinaryFraction :=
  rankedNormalizeBody (SourceRanked.rank ChargedPhysicalRequest.rank)
    (computedQueryMemoRaw source target N occurrence symbolBits positionBits input)
    (computedQueryBase N) (computedQueryBase_pos N)
    (queryFamilyMemoRemaining target N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryCorrect
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

attribute [local instance] queryArityNeZero queryRoundsNeZero

noncomputable def computedQueryReference (source target : List ℕ) (N : ℕ)
    (input : ComputedFamilyInput source target N) (key : ComputedFamilyMemoKey source target N) :=
  SourceRanked.body ChargedPhysicalRequest.rank
    (physicalFamilyProgram source target N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
      (integerParameters N).T (integerParameters N).S (computedSeedPassCount N) (inputHeight N ^ 2)
      (scheduledSeedFactor N) (scheduledSeedMultiplier N)
      (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).eta
      (rationalParameters (inputSmallLog N)).kappa (rationalParameters (inputSmallLog N)).delta
      (clampedSeedNat input.1))
    (physicalFamilyAnswer target N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
      (computedSeedPassCount N) (inputHeight N ^ 2) input.2) key

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryExecution
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
attribute [local instance] queryArityNeZero queryRoundsNeZero

/-- The executed mixed binary memo at the final refinement root. -/
def computedQueryMemoResult (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) :=
  rankedBitMemoEvaluate (SourceRanked.rank ChargedPhysicalRequest.rank)
    (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input)
    (16384 * inputHeight N + 5) (computedFamilyMemoCode source target N (inputHeight N ^ 2))
    (.inr (localFinalRootRequest target N (integerParameters N).T (integerParameters N).S
      (inputHeight N) (Nat.two_pow_pos _) (finalTargetState target.length))) .empty

def computedQueryLocalWork (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) : ComputedFamilyMemoKey source target N → ℕ :=
  rankedBitLocalWork (SourceRanked.rank ChargedPhysicalRequest.rank)
    (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PreparedBandPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed-degree bound for the complete band constructor. The sole
non-polynomial quantity is the actual Cartesian-product list bound, an
explicit input subsequently bounded by the computed grid parameters. -/

namespace EditApproximation

/-- The representative tail used to construct the actual online draw range. -/
def representativeCompleteBitDegree : ℕ :=
  (bpRepresentative (.input 0) (.input 1) (.input 2)).degree

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PreparedGroupPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed-degree cap for the complete cell selector, including all band
construction and exact finite-count sampled scores. -/

namespace EditApproximation

abbrev CP := FiniteBitPolynomial (Fin 4)
def cpEligibility (B : CP) : CP :=
  4000 * (B + 1) ^ 2 + 2100 * (4 * B + 4) ^ 2 + 2000 * (4 * B + 3) ^ 2 +
    2 * (1000 * (16 * B + 13) ^ 2 + 1) + 2 * B + 8
def cpGridPoints (n B : CP) : CP :=
  2000000 * (B + 100) ^ 2 + n * (1000 * (B + 100) ^ 2 + 5)
def cpCellStates (l r B : CP) : CP :=
  cpGridPoints l B + cpGridPoints r B + l * (r * (16 * (17 * B + 78) + 11) + r + 3) + 2
def cpCellCenters (P B : CP) : CP :=
  100 * (B + 2) ^ 2 + 2000 * (B + 1) ^ 2 + cpCellStates P P (4 * B + 40) +
    P * P * (cpEligibility B + 3) + 3
def cellGroupPolynomial : CP :=
  let M := .input 0
  let P := .input 1
  let B := .input 2
  let X := .input 3
  cpCellCenters P B + (P + 1) ^ 2 * (X ^ preparedBandBitDegree + 3) +
    (P + 1) ^ 2 * (X ^ sampledGroupBitDegree + 1000 * (X ^ sampledGroupBitDegree + 1) ^ 2 + 3) +
    1 + 2 * X ^ sampledGroupBitDegree + 2 * B + 2 * M + 6 + 2

def preparedCellGroupBitDegree : ℕ := cellGroupPolynomial.degree

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PreparedLocalGroupPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed-degree cap on all whole-cell loops at a query. Distance scales
enter through their bit length; their numeric size is never charged. -/

namespace EditApproximation

abbrev LP := FiniteBitPolynomial (Fin 8)
def lpGuard (B : LP) : LP :=
  4000 * (B + 1) ^ 2 + 2100 * (4 * B + 4) ^ 2 + 2000 * (4 * B + 3) ^ 2 +
    2 * (1000 * (16 * B + 13) ^ 2 + 1) + 2 * B + 8
def lpCellSetup (B : LP) : LP :=
  100 * (B + 1) + 4200 * (B + 6) ^ 2 + 400 * (4 * B + 21) ^ 2 + 100 * (4 * B + 25)
def lpTargetCells (K B : LP) : LP := 2 * lpCellSetup B + K + K + K * (5 * K + 3) + 2
def lpScales (eM eF B : LP) : LP :=
  (7 + eM + eF) * (eM + B + eF + 13) + .bitLength eM + .bitLength B + .bitLength eF + 8
def localGroupPolynomial : LP :=
  let F := .input 0
  let thetaPow := .input 1
  let B := .input 2
  let eM := .input 3
  let eF := .input 4
  let X := .input 5
  let K := (32 * F + 2) * thetaPow + 2
  let scale := 2000 * (B + 4) ^ 2 + 500 * (B + 1) ^ 2 + lpTargetCells K (4 * B + 40) +
    K ^ 2 * (lpScales eM eF B + X ^ preparedCellGroupBitDegree + 4) + B + 4
  (B + 1) * (lpGuard (B + 3) + scale + B + 4 + K ^ 2 + 3) + (B + 1) + B + 2

def preparedLocalGroupBitDegree : ℕ := localGroupPolynomial.degree

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PreparedShellPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-degree envelopes for the literal representative, online outer,
and continuation loops. Large action counts are explicit numeric inputs. -/

namespace EditApproximation

attribute [local irreducible] preparedBandBitDegree sampledOnlineBitDegree

abbrev SP_p1 := FiniteBitPolynomial (Fin 8)
def spGuard (B : SP_p1) : SP_p1 :=
  4000 * (B + 1) ^ 2 + 2100 * (4 * B + 4) ^ 2 + 2000 * (4 * B + 3) ^ 2 +
    2 * (1000 * (16 * B + 13) ^ 2 + 1) + 2 * B + 8
def spGrid (n B : SP_p1) : SP_p1 := 1000 * (B + 2) ^ 2 + n * (100 * (B + 3) ^ 2 + 5)
def spBox (n B : SP_p1) : SP_p1 :=
  96 * (B + 1) + 2 * spGrid n (B + 2) + n * (n * (16 * (B + 2) + 11) + n + 3) + 6
def spQuery (B : SP_p1) : SP_p1 := (B + 1) * (spGuard (B + 4) + B + 5) + 2 * B + 3
def representativeShell : SP_p1 :=
  let P := .input 0
  let F := .input 1
  let B := .input 2
  let C := B + 4
  let L := 64 * F * P + 2
  spQuery B + 500 * (B + 1) ^ 2 +
    (B + 1) * (100 * (C + 2) ^ 2 + spBox L C + L ^ 2 * (spGuard C + 3) +
      L ^ 2 * 4 + B + 6 + L ^ 2 + 3) + 3

def spCoordinates (M V B : SP_p1) : SP_p1 :=
  V * (5 * M + 3) + (V * M + 1) ^ 2 * (24 * B + 12) + 1
def spPower (n B : SP_p1) : SP_p1 := 1 + n * (200 * ((n + 1) * (B + 1) + 1) ^ 2)
def spOnline (M V B X : SP_p1) : SP_p1 :=
  2 * X ^ preparedBandBitDegree + (spCoordinates M V B + 40 * (B + 4) + spPower 80 (B + 4) + 3) +
    (10000 * (B + 3) ^ 2 + 200 * (4 * B + 6) ^ 2 + B + 2) + X ^ sampledOnlineBitDegree + 3
def onlineShell : SP_p1 :=
  let M := .input 0
  let V := .input 1
  let B := .input 2
  let X := .input 3
  let W := B + 4
  spQuery B + (B + 1) * (100 * (W + 2) ^ 2 + (500 * (W + 1) ^ 2 + 1) +
    spGuard W + spOnline M V W X + B + 4 + 3) + 1

def spSumStorage (n B : SP_p1) : SP_p1 := .bitLength n + B + 2 * (1 + n * (B + 1)) + 2
def spSumWord (n B : SP_p1) : SP_p1 :=
  (B + 1) + .bitLength n + 2 * (B + 2) + 2 * (1 + n * ((B + 1) + (B + 1))) + 1
def spSumWork (n B : SP_p1) : SP_p1 := 1 + n * (100000 * (spSumWord n B + 1) ^ 2)
def spConnectionWord (M B : SP_p1) : SP_p1 := spSumStorage (M + 1) (8 * B + 6)
def spConnectionWork (M B : SP_p1) : SP_p1 :=
  (M + 1) * (6000 * (B + 1) ^ 2 + 4) + M * (2 * B + 6) +
    spSumWork (M + 1) (8 * B + 6) + 6 * (M + 1) + 1
def spActionWord (M B : SP_p1) : SP_p1 := 8 * (40 * B + 22 + spSumStorage M B) + 6
def spActionWork (M B C : SP_p1) : SP_p1 :=
  C + 2000 * (B + 1) ^ 2 + 6000 * (5 * B + 3) ^ 2 + spSumWork M B + 6 * M +
    6000 * (40 * B + 22 + spSumStorage M B + 1) ^ 2 + 3
def spBellman (M n B F C : SP_p1) : SP_p1 :=
  n * (spActionWork M B C + 3) + (1 + n * (1000 * (F + spActionWord M B + 1) ^ 2 + 2)) + 1
def spUpdate (B : SP_p1) : SP_p1 :=
  6000 * (B + 1) ^ 2 + 2100 * (8 * B + 8) ^ 2 + 2 * (1000 * (32 * B + 29) ^ 2 + 1) + 2
def spContinuation (M nw ng no B C : SP_p1) : SP_p1 :=
  spBellman M nw B B C + spBellman M ng B (B + spActionWord M B) C +
    no * (spActionWork M B C + 3) + (2 + no * (1000 * (spActionWord M B + 1) ^ 2 + 2)) +
    spUpdate (B + 2 * spActionWord M B + 1) + 3
def physicalShell : SP_p1 :=
  let M := .input 0
  let P := .input 1
  let nr := .input 2
  let ng := .input 3
  let no := .input 4
  let B := .input 5
  let V := .input 6
  let Cart := .input 7
  let wide := M * (10000 * (B + 12) ^ 2 + spBox (40 * P + 2) (B + 12) + 6) +
    (M + 1) * (6 * M + 10) * Cart + 1
  let W := B + spConnectionWord M B + (64 * B + 54) + 4 * B + 2
  let distance := 2 * (6000 * (B + 1) ^ 2 + 2) + 6000 * (8 * B + 7) ^ 2 + 4 * B + 3
  nr * (wide + V * (spConnectionWork M B + 2 * B + 2 * M + 6) + 1 + V + 3) +
    2000 * (B + 1) ^ 2 + spContinuation M (nr * V) ng no W distance + 1

def representativeShellDegree : ℕ := representativeShell.degree
def onlineShellDegree : ℕ := onlineShell.degree
def physicalShellDegree : ℕ := physicalShell.degree

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PreparedCachedKernelWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete refinement return includes literal power-denominator
construction, multiplication, division and trimming before cache insertion. -/

namespace EditApproximation

def cacheSum (M B : CachePoly) : CachePoly :=
  .bitLength M + B + 2 * (1 + M * (B + 1)) + 2
def cacheConnection (M B : CachePoly) : CachePoly := cacheSum (M + 1) (8 * B + 6)
def cacheAction (M B : CachePoly) : CachePoly := 8 * (40 * B + 22 + cacheSum M B) + 6
def cacheRawWidth (M B : CachePoly) : CachePoly :=
  let W := B + 4 + cacheConnection M (B + 4) + (64 * (B + 4) + 54) + 4 * (B + 4) + 2
  32 * (W + 2 * cacheAction M W + 1) + 28
def cacheReturnPolynomial : CachePoly :=
  let M := .input 0
  let B := .input 1
  let n := .input 2
  let D := .input 3
  (1 + n * (200 * ((n + 1) * (D + 1) + 1) ^ 2)) +
    5000 * (cacheRawWidth M B + (n * D + 1) + 2) ^ 2 + 1

def preparedCacheReturnBitDegree : ℕ := cacheReturnPolynomial.degree

attribute [local irreducible] preparedCacheReturnBitDegree

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryCallbackPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

abbrev GP_p1 := FiniteBitPolynomial (Fin 6)

def gp_storedSumWordBudget (n B : GP_p1) : GP_p1 :=
  (B + 1) + FiniteBitPolynomial.bitLength n + 2 * (B + 2) + 2 * (1 + n * ((B + 1) + (B + 1))) + 1

def gp_storedSumBitBudget (n B : GP_p1) : GP_p1 :=
  1 + n * (100000 * (gp_storedSumWordBudget n B + 1) ^ 2)

def gp_bandMassTotalStorageBudget_p0 (M B : GP_p1) : GP_p1 :=
  FiniteBitPolynomial.bitLength M + B + 2 * (1 + M * (B + 1)) + 2

def gp_warmupAverageBitBudget (n B : GP_p1) : GP_p1 :=
  gp_storedSumBitBudget n B + 6 * n +
    2100 * (gp_bandMassTotalStorageBudget_p0 n B + FiniteBitPolynomial.bitLength n + 4) ^ 2 + FiniteBitPolynomial.bitLength n + 2

def gp_queryPhysicalDataBudget (T J B V C W : GP_p1) : GP_p1 :=
  W + (T + 1 + T * (7 * J + 30 + (C + 1) + 3) + gp_warmupAverageBitBudget T V) +
    (8 * B + 7 * J + 32 + (C + 1)) + 1

def gp_queryFamilySourceReadBudget (J B W : GP_p1) : GP_p1 :=
  200 * (1000 * (B + 1) + 1000 + 2) ^ 2 + 120 * (B + 1) ^ 2 + 10 * J + 100 + W

def gp_bitPowerBitBudget_p0 (n B : GP_p1) : GP_p1 :=
  1 + n * (200 * ((n + 1) * (B + 1) + 1) ^ 2)

def gp_powerDenominatorBitBudget (n A B : GP_p1) : GP_p1 :=
  gp_bitPowerBitBudget_p0 n B + 5000 * (A + (n * B + 1) + 2) ^ 2 + 1

def callbackPolynomial : GP_p1 :=
  gp_queryPhysicalDataBudget (.input 0) (.input 1) (.input 2) (.input 3) (.input 4)
    (gp_queryFamilySourceReadBudget (.input 1) (.input 2) (.input 5))

def queryCallbackShellDegree : ℕ := callbackPolynomial.degree

def normalizationPolynomial : GP_p1 :=
  gp_powerDenominatorBitBudget (.input 0) (.input 1) (.input 2)

def queryNormalizationBitDegree : ℕ := normalizationPolynomial.degree

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryRawWidthPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

abbrev GP_p4 := FiniteBitPolynomial (Fin 2)

def gp_bandMassTotalStorageBudget_p1 (M B : GP_p4) : GP_p4 :=
  FiniteBitPolynomial.bitLength M + B + 2 * (1 + M * (B + 1)) + 2

def gp_connectionWordBudget (k B : GP_p4) : GP_p4 :=
  gp_bandMassTotalStorageBudget_p1 (k + 1) (8 * B + 6)

def gp_endpointDistanceWordBudget (B : GP_p4) : GP_p4 :=
  64 * B + 54

def gp_physicalContinuationInputBudget (M B : GP_p4) : GP_p4 :=
  B + gp_connectionWordBudget M B + gp_endpointDistanceWordBudget B + 4 * B + 2

def gp_bellmanActionWordBudget (M B : GP_p4) : GP_p4 :=
  8 * (40 * B + 22 + gp_bandMassTotalStorageBudget_p1 M B) + 6

def gp_localWarmupWordBudget (M B : GP_p4) : GP_p4 :=
  let W := gp_physicalContinuationInputBudget M (B + 4)
  W + gp_bellmanActionWordBudget M W

def gp_refinementUpdateWordBudget (B : GP_p4) : GP_p4 :=
  32 * B + 28

def gp_localContinuationInputBudget (M B : GP_p4) : GP_p4 :=
  B + 2 * gp_bellmanActionWordBudget M B + 1

def gp_localContinuationWordBudget (M B : GP_p4) : GP_p4 :=
  gp_refinementUpdateWordBudget (gp_localContinuationInputBudget M B)

def gp_preparedKernelWordBudget (M B : GP_p4) : GP_p4 :=
  gp_localContinuationWordBudget M (gp_physicalContinuationInputBudget M (B + 4))

def rawWordPolynomial : GP_p4 :=
  gp_localWarmupWordBudget (.input 0) (.input 1) + gp_preparedKernelWordBudget (.input 0) (.input 1)

def queryRawWordDegree : ℕ := rawWordPolynomial.degree

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryNormalizationBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter
attribute [local irreducible] queryRawWordDegree queryNormalizationBitDegree

def computedQueryNormalizationDegree (K : ℕ) : ℕ := (K + 1) * queryNormalizationBitDegree

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryChargedSeedCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Seed
variable {M J n passes copies T S : ℕ}
  (parent : {r : PhysicalTableRequest M J n // r.Bounded passes copies T S})
  (oracle : {child : ChargedPhysicalRequest M J n passes copies T S //
    child.rank < ChargedPhysicalRequest.rank (.inr parent)} → BinaryFraction)
  (readWork : {child : ChargedPhysicalRequest M J n passes copies T S //
    child.rank < ChargedPhysicalRequest.rank (.inr parent)} → ℕ)

def queryChargedSeedBitBudget (copies J B C : ℕ) : ℕ :=
  8 * B + 3 + (7 * J + 33 + C) + copies + 1 +
    copies * (7 * J + 33 + C + 3) + BinaryFraction.seedMedianBitBudget copies B + B + 1

end Seed
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryPhysicalInitialCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

def queryPhysicalInitialBitBudget (P _F Amax copies J symbolBits positionBits B C : ℕ) : ℕ :=
  30 * B + 20 + (10 * B + 2 * symbolBits + 4 * positionBits + B + 17) +
    BinaryFraction.queryInitialProgramBitBudget P Amax B (queryChargedSeedBitBudget copies J B C)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryChargedWarmupCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

def queryChargedWarmupBitBudget (M P F Amax copies J symbolBits positionBits B C : ℕ) : ℕ :=
  let I := queryPhysicalInitialBitBudget P F Amax copies J symbolBits positionBits B C
  80 * (B + 1) + I +
    BinaryFraction.queryWarmupProgramBitBudget M P F B (I + 7 * J + 33 + C)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryChargedTableCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open BinaryFraction

def queryChargedTableBitBudget (M P F Amax copies J symbolBits positionBits B C active : ℕ) : ℕ :=
  80 * (B + 1) + queryChargedWarmupBitBudget M P F Amax copies J symbolBits positionBits B (C + 1) + active

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryRegisters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open BinaryFraction

/-- The remaining scalar premises of the concrete table dispatcher. -/
structure ComputedQueryRegisters (N ny J : ℕ)
    (request : PhysicalTableRequest (integerParameters N).M J ny) : Prop where
  targetSuccessor : Nat.size (ny + 1) + 2 ≤ inputHeight N ^ 8
  initial : Nat.size ((32 * inputSmallLog N + 1) * N) + 3 ≤ inputHeight N ^ 8
  depth : Nat.size J ≤ inputHeight N ^ 8
  index : Nat.size request.index ≤ inputHeight N ^ 8
  warmup : Nat.size (integerParameters N).T ≤ inputHeight N ^ 8
  refinement : Nat.size (integerParameters N).S ≤ inputHeight N ^ 8
  rank : Nat.size (request.combinedRank (integerParameters N).T (integerParameters N).S) ≤ inputHeight N ^ 8
  pass : Nat.size request.pass ≤ inputHeight N ^ 8
  copy : Nat.size request.copy ≤ inputHeight N ^ 8
  passes : Nat.size (computedSeedPassCount N + 1) ≤ inputHeight N ^ 8
  copies : Nat.size (inputHeight N ^ 2 + 1) ≤ inputHeight N ^ 8
  multiplier : Nat.size (scheduledSeedMultiplier N (request.pass - 1)) + 2 ≤ inputHeight N ^ 8
  mean : warmupAverageWordBudget (integerParameters N).T (inputHeight N ^ 3) ≤ inputHeight N ^ 8

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryReadBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter

/-- Degree contributed by guards, physical means, and scalar-source reads. -/
def computedQueryReadDegree (K : ℕ) : ℕ := (K + 1) * queryCallbackShellDegree

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PreparedInitialPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed degrees for the literal initial grid/minimum, trimmed seed
median, and child warmup average. Grid side length is an explicit input. -/

namespace EditApproximation

abbrev IP := FiniteBitPolynomial (Fin 2)
def ipCenter (B : IP) : IP :=
  2100 * (B + 2) ^ 2 + 2000 * (B + 1) ^ 2 + 2000 * (4 * B + 3) ^ 2 +
    2 * (1000 * (16 * B + 11) ^ 2 + 1) + 2 * B + 5
def ipScale (B : IP) : IP :=
  4000 * (B + 1) ^ 2 + 4000 * (4 * B + 3) ^ 2 + 2100 * (16 * B + 12) ^ 2 +
    2 * (1000 * (64 * B + 45) ^ 2 + 1) + 2 * B + 7
def ipGrid (L B : IP) : IP := 1000 * (B + 2) ^ 2 + L * (100 * (B + 3) ^ 2 + 5)
def ipBox (L B : IP) : IP :=
  96 * (B + 1) + 2 * ipGrid L (B + 2) + L * (L * (16 * (B + 2) + 11) + L + 3) + 6
def ipGridScale (L B : IP) : IP :=
  100 * (B + 6) ^ 2 + ipBox L (B + 5) + L ^ 2 * (ipCenter (B + 4) + 3) + 2
def ipDistance (B : IP) : IP :=
  2 * (6000 * (B + 1) ^ 2 + 2) + 6000 * (8 * B + 7) ^ 2 + 4 * B + 3
def ipGap (B : IP) : IP :=
  (6000 * (B + 1) ^ 2 + 1) + (6000 * (8 * B + 7) ^ 2 + 1) + 3 * B + 2
def ipConeInput (B : IP) : IP := B + (64 * B + 54) + (64 * B + 54)
def ipSeed (B : IP) : IP :=
  2100 * (B + 2) ^ 2 + 500 * (4 * B + 5) ^ 2 + (1000 * (4 * B + 7) ^ 2 + 1) + B + 3
def ipCone (B : IP) : IP :=
  ipGap B + ipSeed (ipConeInput B) + ipDistance B + 2000 * (ipConeInput B + 1) ^ 2 +
    6000 * (4 * ipConeInput B + 7) ^ 2 + 4
def ipMinimumWord (B : IP) : IP := 128 * B + 90 + (32 * ipConeInput (40 * B + 22) + 54)
def ipMinimum (n B : IP) : IP :=
  (8 * B + 2) + 2000 * (B + 1) ^ 2 + 6000 * (4 * B + 3) ^ 2 +
    2000 * (32 * B + 23) ^ 2 + n * (ipCone (40 * B + 22) + 3) +
    (1 + n * (1000 * (ipMinimumWord B + 1) ^ 2 + 2)) + 2 * B + 6
def initialShellPolynomial : IP :=
  let B := .input 0
  let L := .input 1
  ((B + 1) * (B + 9) + 2 + (B + 1) * (ipScale (B + 4) + 3) +
    (B + 1) * (ipGridScale L B + L ^ 2 + 3) + 3) +
    ipMinimum ((B + 1) * L ^ 2) (B + 4) + 1

def cachedInitialShellPolynomial : IP :=
  initialShellPolynomial + (1 + 0 * (200 * ((0 + 1) * (1 + 1) + 1) ^ 2) +
    5000 * (ipMinimumWord (.input 0 + 4) + (0 * 1 + 1) + 2) ^ 2 + 1) + 1

def preparedCachedInitialBitDegree : ℕ := cachedInitialShellPolynomial.degree

def medianShellPolynomial : IP :=
  let n := .input 0
  let B := .input 1
  let ceiling := 2000 * (B + 1) ^ 2 + 500 * (4 * B + 3) ^ 2 + B + 3
  (n * (ceiling + 3) + (n + 1) ^ 2 * (8 * (4 * B + 4) + 6) +
    n + 4 * (B + (4 * B + 4)) + 3 + B + 3) + 12 * B + 14

def preparedMedianBitDegree : ℕ := medianShellPolynomial.degree

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PreparedWarmupPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The initial warmup Bellman scan and its cache return are covered by
the same fixed polynomial envelope as the full continuation. -/

namespace EditApproximation

attribute [local irreducible] representativeShellDegree physicalShellDegree
  preparedCacheReturnBitDegree

def preparedWarmupBitDegree : ℕ :=
  max representativeShellDegree (max physicalShellDegree preparedCacheReturnBitDegree) + 3

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInitialWarmupPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial certificate for the complete initial and warmup dispatch,
including actual gathers, buffer scans, and the previous-pass median. -/

namespace EditApproximation

abbrev GP_p3 := FiniteBitPolynomial (Fin 13)

def gp_initialScaleGuardBitBudget (B : GP_p3) : GP_p3 :=
  4000 * (B + 1) ^ 2 + 4000 * (4 * B + 3) ^ 2 + 2100 * (16 * B + 12) ^ 2 +
    2 * (1000 * (64 * B + 45) ^ 2 + 1) + 2 * B + 7

def gp_gridPointsBitBudget_p1 (n B : GP_p3) : GP_p3 :=
  1000 * (B + 2) ^ 2 + n * (100 * (B + 3) ^ 2 + 5)

def gp_gridStateBoxBitBudget_p1 (count B : GP_p3) : GP_p3 :=
  96 * (B + 1) + 2 * gp_gridPointsBitBudget_p1 count (B + 2) +
    count * (count * (16 * (B + 2) + 11) + count + 3) + 6

def gp_queryGridPointsBitBudget_p1 (P K B : GP_p3) : GP_p3 :=
  100 * (B + 2) ^ 2 + gp_gridStateBoxBitBudget_p1 (4 * K * P + 2) (B + 1) + 1

def gp_queryInitialCentersBitBudget (P Amax B : GP_p3) : GP_p3 :=
  let L := (64 * Amax ^ 2 * P + 2) ^ 2
  500 * (B + 1) ^ 2 + (B + 1) * (B + 9) + 2 +
    (B + 1) * (gp_initialScaleGuardBitBudget (B + 4) + 3) +
    (B + 1) * (gp_queryGridPointsBitBudget_p1 P (16 * Amax ^ 2) (B + 2) + L + 3) + 2

def gp_queryInitialSeedReadBudget (count B : GP_p3) : GP_p3 :=
  16 * B + 7 + count * (16 * B + 6) + 500 * (B + 1) ^ 2

def gp_queryInitialProgramBitBudget (aux : Fin 3 → GP_p3) (P Amax B C : GP_p3) : GP_p3 :=
  let count := (B + 1) * (64 * Amax ^ 2 * P + 2) ^ 2
  C + gp_queryInitialCentersBitBudget P Amax B + count * (C + 3) +
    (aux 0) * (gp_queryInitialSeedReadBudget count B + 2)

def gp_queryChargedSeedBitBudget (aux : Fin 3 → GP_p3) (copies J B C : GP_p3) : GP_p3 :=
  8 * B + 3 + (7 * J + 33 + C) + copies + 1 +
    copies * (7 * J + 33 + C + 3) + (aux 1) + B + 1

def gp_queryPhysicalInitialBitBudget (aux : Fin 3 → GP_p3) (P __F Amax copies J symbolBits positionBits B C : GP_p3) : GP_p3 :=
  30 * B + 20 + (10 * B + 2 * symbolBits + 4 * positionBits + B + 17) +
    (gp_queryInitialProgramBitBudget aux) P Amax B ((gp_queryChargedSeedBitBudget aux) copies J B C)

def gp_localEligibilityBitBudget_p1 (B : GP_p3) : GP_p3 :=
  4000 * (B + 1) ^ 2 + 2100 * (4 * B + 4) ^ 2 + 2000 * (4 * B + 3) ^ 2 +
    2 * (1000 * (16 * B + 13) ^ 2 + 1) + 2 * B + 8

def gp_queryExponentsBitBudget_p1 (B : GP_p3) : GP_p3 :=
  (B + 1) * (gp_localEligibilityBitBudget_p1 (B + 4) + B + 5) + 2 * B + 3

def gp_queryScalesBitBudget_p1 (B : GP_p3) : GP_p3 :=
  gp_queryExponentsBitBudget_p1 B + (B + 1) * (B + 6) + 1

def gp_queryRawCentersBitBudget_p1 (P F B : GP_p3) : GP_p3 :=
  let L := (64 * F * P + 2) ^ 2
  let count := (B + 1) * L
  gp_queryScalesBitBudget_p1 B + 500 * (B + 1) ^ 2 +
    (B + 1) * (gp_queryGridPointsBitBudget_p1 P (16 * F) (B + 2) + L + 3) +
    (count + 1) ^ 2 * (16 * B + 9) + 3

def gp_queryWarmupRepresentatives (P F B : GP_p3) : GP_p3 :=
  (B + 1) * (64 * F * P + 2) ^ 2

def gp_localRepresentativeScaleBitBudget_p1 (P F B : GP_p3) : GP_p3 :=
  let C := B + 4
  let L := 64 * F * P + 2
  100 * (C + 2) ^ 2 + gp_gridStateBoxBitBudget_p1 L C +
    L ^ 2 * (gp_localEligibilityBitBudget_p1 C + 3) + L ^ 2 * 4 + B + 6

def gp_localRepresentativesBitBudget_p1 (P F B : GP_p3) : GP_p3 :=
  gp_queryExponentsBitBudget_p1 B + 500 * (B + 1) ^ 2 +
    (B + 1) * (gp_localRepresentativeScaleBitBudget_p1 P F B + (64 * F * P + 2) ^ 2 + 3) + 3

def gp_wideChildGridBitBudget_p1 (P B : GP_p3) : GP_p3 :=
  10000 * (B + 12) ^ 2 + gp_gridStateBoxBitBudget_p1 (40 * P + 2) (B + 12)

def gp_queryWideInputsBitBudget_p1 (M P count B : GP_p3) : GP_p3 :=
  let G := (40 * P + 2) ^ 2
  let C := gp_wideChildGridBitBudget_p1 P (B + 1)
  count * (M * (C + 4 * G + 1 + G + 3) + M * G + 3) +
    (count * (M * G) + 1) ^ 2 * (24 * B + 12) + M + 2

def gp_queryWarmupInputsBitBudget (M P F B I : GP_p3) : GP_p3 :=
  gp_localRepresentativesBitBudget_p1 P F B * (I + 2) +
    gp_queryWideInputsBitBudget_p1 M P (gp_queryWarmupRepresentatives P F B) B + 1

def gp_queryWarmupParentReadBudget (P F B : GP_p3) : GP_p3 :=
  16 * B + 7 + gp_queryWarmupRepresentatives P F B * (16 * B + 6)

def gp_queryWarmupChildReadBudget (M P F B : GP_p3) : GP_p3 :=
  1 + (gp_queryWarmupRepresentatives P F B * (M * (40 * P + 2) ^ 2)) * (24 * B + 9)

def gp_queryWarmupProgramBitBudget (aux : Fin 3 → GP_p3) (M P F B C : GP_p3) : GP_p3 :=
  C + gp_queryRawCentersBitBudget_p1 P F B + gp_queryWarmupRepresentatives P F B * (C + 3) +
    gp_queryWarmupInputsBitBudget M P F B (gp_queryWarmupParentReadBudget P F B) +
    (gp_queryWarmupRepresentatives P F B * (M * (40 * P + 2) ^ 2)) * (C + 3) +
    (aux 2) *
      (gp_queryWarmupParentReadBudget P F B + M * (gp_queryWarmupChildReadBudget M P F B + 3) + 4)

def gp_queryChargedWarmupBitBudget (aux : Fin 3 → GP_p3) (M P F Amax copies J symbolBits positionBits B C : GP_p3) : GP_p3 :=
  let I := (gp_queryPhysicalInitialBitBudget aux) P F Amax copies J symbolBits positionBits B C
  80 * (B + 1) + I +
    (gp_queryWarmupProgramBitBudget aux) M P F B (I + 7 * J + 33 + C)

def initialWarmupPolynomial : GP_p3 :=
  gp_queryChargedWarmupBitBudget ![.input 10, .input 11, .input 12]
    (.input 0) (.input 1) (.input 2) (.input 3) (.input 4) (.input 5)
    (.input 6) (.input 7) (.input 8) (.input 9)

def queryInitialWarmupBitDegree : ℕ := initialWarmupPolynomial.degree

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryWarmupUniformCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

attribute [local irreducible] preparedCachedInitialBitDegree preparedMedianBitDegree
  preparedWarmupBitDegree queryInitialWarmupBitDegree

def queryInitialWarmupPrimitiveDegree : ℕ :=
  max 1 (max preparedCachedInitialBitDegree (max preparedMedianBitDegree preparedWarmupBitDegree))

def queryInitialWarmupDegree : ℕ :=
  16 * queryInitialWarmupPrimitiveDegree * queryInitialWarmupBitDegree

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryGatherPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite polynomial certificate for the complete adaptive gather cost.
The four kernel bounds and the two Cartesian counts
are explicit inputs. Every remaining operation is addition, multiplication,
fixed natural power, or bit length. -/

namespace EditApproximation

abbrev GP_p2 := FiniteBitPolynomial (Fin 16)

def gp_localEligibilityBitBudget_p0 (B : GP_p2) : GP_p2 :=
  4000 * (B + 1) ^ 2 + 2100 * (4 * B + 4) ^ 2 + 2000 * (4 * B + 3) ^ 2 +
    2 * (1000 * (16 * B + 13) ^ 2 + 1) + 2 * B + 8

def gp_queryExponentsBitBudget_p0 (B : GP_p2) : GP_p2 :=
  (B + 1) * (gp_localEligibilityBitBudget_p0 (B + 4) + B + 5) + 2 * B + 3

def gp_queryScalesBitBudget_p0 (B : GP_p2) : GP_p2 :=
  gp_queryExponentsBitBudget_p0 B + (B + 1) * (B + 6) + 1

def gp_gridPointsBitBudget_p0 (n B : GP_p2) : GP_p2 :=
  1000 * (B + 2) ^ 2 + n * (100 * (B + 3) ^ 2 + 5)

def gp_gridStateBoxBitBudget_p0 (count B : GP_p2) : GP_p2 :=
  96 * (B + 1) + 2 * gp_gridPointsBitBudget_p0 count (B + 2) +
    count * (count * (16 * (B + 2) + 11) + count + 3) + 6

def gp_queryGridPointsBitBudget_p0 (P K B : GP_p2) : GP_p2 :=
  100 * (B + 2) ^ 2 + gp_gridStateBoxBitBudget_p0 (4 * K * P + 2) (B + 1) + 1

def gp_queryRawCentersBitBudget_p0 (P F B : GP_p2) : GP_p2 :=
  let L := (64 * F * P + 2) ^ 2
  let count := (B + 1) * L
  gp_queryScalesBitBudget_p0 B + 500 * (B + 1) ^ 2 +
    (B + 1) * (gp_queryGridPointsBitBudget_p0 P (16 * F) (B + 2) + L + 3) +
    (count + 1) ^ 2 * (16 * B + 9) + 3

def gp_cellCoordinateSetupBitBudget (B : GP_p2) : GP_p2 :=
  100 * (B + 1) + 4200 * (B + 6) ^ 2 + 400 * (4 * B + 21) ^ 2 + 100 * (4 * B + 25)

def gp_targetCellsBitBudget (left right B : GP_p2) : GP_p2 :=
  2 * gp_cellCoordinateSetupBitBudget B + left + right + left * (5 * right + 3) + 2

def gp_queryCellScanBitBudget (aux : Fin 7 → GP_p2) (F _exponent B : GP_p2) : GP_p2 :=
  let K := (32 * F + 2) * (aux 0) + 2
  2000 * (B + 4) ^ 2 + gp_targetCellsBitBudget K K (4 * B + 40)

def gp_queryGroupKeysBitBudget (aux : Fin 7 → GP_p2) (F exponent B : GP_p2) : GP_p2 :=
  let L := ((32 * F + 2) * (aux 0) + 2) ^ 2
  gp_queryScalesBitBudget_p0 B + 500 * (B + 1) ^ 2 +
    (B + 1) * ((gp_queryCellScanBitBudget aux) F exponent B + 5 * L + 5) + exponent + 4

def gp_cellGridSetupBitBudget (B : GP_p2) : GP_p2 :=
  2000000 * (B + 100) ^ 2

def gp_cellGridPointBitBudget (B : GP_p2) : GP_p2 :=
  1000 * (B + 100) ^ 2

def gp_cellGridPointsBitBudget (count B : GP_p2) : GP_p2 :=
  gp_cellGridSetupBitBudget B + count * (gp_cellGridPointBitBudget B + 5)

def gp_cellStatesBitBudget (left right B : GP_p2) : GP_p2 :=
  gp_cellGridPointsBitBudget left B + gp_cellGridPointsBitBudget right B +
    left * (right * (16 * (17 * B + 78) + 11) + right + 3) + 2

def gp_queryCellStatesBitBudget (P exponent B : GP_p2) : GP_p2 :=
  100 * (B + 5) ^ 2 + 2000 * (B + 4) ^ 2 +
    gp_cellStatesBitBudget P P (16 * B + 200) + exponent + 3

def gp_queryOnlineKeysBitBudget (B : GP_p2) : GP_p2 :=
  gp_queryScalesBitBudget_p0 B + (B + 1) * (600 * (B + 3) ^ 2 + 6) + 1

def gp_queryInitialSupportBitBudget (aux : Fin 7 → GP_p2) (P F exponent B : GP_p2) : GP_p2 :=
  let raw := (B + 1) * (64 * F * P + 2) ^ 2
  let groups := (B + 1) * ((32 * F + 2) * (aux 0) + 2) ^ 2
  gp_queryRawCentersBitBudget_p0 P F B + (gp_queryGroupKeysBitBudget aux) F exponent B +
    groups * (gp_queryCellStatesBitBudget P exponent B + P ^ 2 + 3) +
    gp_queryOnlineKeysBitBudget B + 4 * (B + 1) + 2 * raw + groups * P ^ 2 + 5

def gp_queryInitialSupportLength (aux : Fin 7 → GP_p2) (P F _exponent B : GP_p2) : GP_p2 :=
  let raw := (B + 1) * (64 * F * P + 2) ^ 2
  let groups := (B + 1) * ((32 * F + 2) * (aux 0) + 2) ^ 2
  1 + raw + groups * P ^ 2 + (B + 1)

def gp_queryInitialGatherBitBudget (aux : Fin 7 → GP_p2) (P F exponent B R K : GP_p2) : GP_p2 :=
  R + (gp_queryInitialSupportBitBudget aux) P F exponent B + (gp_queryInitialSupportLength aux) P F exponent B * (R + 3) + K

def gp_localRepresentativeScaleBitBudget_p0 (P F B : GP_p2) : GP_p2 :=
  let C := B + 4
  let L := 64 * F * P + 2
  100 * (C + 2) ^ 2 + gp_gridStateBoxBitBudget_p0 L C +
    L ^ 2 * (gp_localEligibilityBitBudget_p0 C + 3) + L ^ 2 * 4 + B + 6

def gp_localRepresentativesBitBudget_p0 (P F B : GP_p2) : GP_p2 :=
  gp_queryExponentsBitBudget_p0 B + 500 * (B + 1) ^ 2 +
    (B + 1) * (gp_localRepresentativeScaleBitBudget_p0 P F B + (64 * F * P + 2) ^ 2 + 3) + 3

def gp_cellCentersBitBudget (left right B : GP_p2) : GP_p2 :=
  100 * (B + 2) ^ 2 + 2000 * (B + 1) ^ 2 +
    gp_cellStatesBitBudget left right (4 * B + 40) +
    left * right * (gp_localEligibilityBitBudget_p0 B + 3) + 3

def gp_queryEarlierRepresentativesBitBudget (aux : Fin 7 → GP_p2) (P F exponent B R : GP_p2) : GP_p2 :=
  let groups := (B + 1) * ((32 * F + 2) * (aux 0) + 2) ^ 2
  let L := (P + 1) ^ 2
  R + gp_localRepresentativesBitBudget_p0 P F B * (R + 2) + (gp_queryGroupKeysBitBudget aux) F exponent B +
    groups * (gp_cellCentersBitBudget P P (16 * B + 200) * (R + 1) + 5 * L + 4) +
    gp_queryOnlineKeysBitBudget B + 2 * ((B + 1) * (64 * F * P + 2) ^ 2) + groups * L + 4

def gp_wideChildGridBitBudget_p0 (P B : GP_p2) : GP_p2 :=
  10000 * (B + 12) ^ 2 + gp_gridStateBoxBitBudget_p0 (40 * P + 2) (B + 12)

def gp_queryWideInputsBitBudget_p0 (M P count B : GP_p2) : GP_p2 :=
  let G := (40 * P + 2) ^ 2
  let C := gp_wideChildGridBitBudget_p0 P (B + 1)
  count * (M * (C + 4 * G + 1 + G + 3) + M * G + 3) +
    (count * (M * G) + 1) ^ 2 * (24 * B + 12) + M + 2

def gp_queryEarlierRepresentativesLength (aux : Fin 7 → GP_p2) (P F _exponent B : GP_p2) : GP_p2 :=
  (B + 1) * ((64 * F * P + 2) ^ 2 +
    ((32 * F + 2) * (aux 0) + 2) ^ 2 * (P + 1) ^ 2 + 1)

def gp_queryBandInputsBitBudget (aux : Fin 7 → GP_p2) (M P F exponent B R : GP_p2) : GP_p2 :=
  (gp_queryEarlierRepresentativesBitBudget aux) P F exponent B R +
    gp_queryWideInputsBitBudget_p0 M P ((gp_queryEarlierRepresentativesLength aux) P F exponent B) B + 1

def gp_queryBandGatherBitBudget (aux : Fin 7 → GP_p2) (M P F exponent B Rp W K : GP_p2) : GP_p2 :=
  (gp_queryBandInputsBitBudget aux) M P F exponent B Rp +
    2 * ((gp_queryEarlierRepresentativesLength aux) P F exponent B * (M * (40 * P + 2) ^ 2) * (W + 3)) + K

def gp_groupScalesBitBudget (eM eb eF : GP_p2) : GP_p2 :=
  (7 + eM + eF) * (eM + eb + eF + 13) +
    FiniteBitPolynomial.bitLength eM + FiniteBitPolynomial.bitLength eb + FiniteBitPolynomial.bitLength eF + 8

def gp_groupSampleCountBitBudget (B : GP_p2) : GP_p2 :=
  2000 * (B + 1) ^ 2 + 2000 * (4 * B + 3) ^ 2 +
    2100 * (16 * B + 12) ^ 2 + 500 * (64 * B + 45) ^ 2 +
    4 * (65 * B + 46) + 3 * B + 8

def gp_queryGroupSamplesBitBudget (M eM eb eF B : GP_p2) : GP_p2 :=
  let L := 7 + eM + eF
  gp_groupScalesBitBudget eM eb eF + 4 * L +
    L * (L + gp_groupSampleCountBitBudget B + 7 * M + 6) + eb + 4

def gp_queryGroupSourceKeysBitBudget (aux : Fin 7 → GP_p2) (M F exponent eM eF B : GP_p2) : GP_p2 :=
  let cells := ((32 * F + 2) * (aux 0) + 2) ^ 2
  let samples := (7 + eM + eF) * M
  let sampleWork := gp_queryGroupSamplesBitBudget M eM B eF (2 * B + 10)
  let scaleWork := (gp_queryCellScanBitBudget aux) F exponent B +
    cells * (sampleWork + samples + 3) + B + exponent + 4
  gp_queryExponentsBitBudget_p0 B + 500 * (B + 1) ^ 2 +
    (B + 1) * (scaleWork + cells * samples + 3) + 2

def gp_queryGroupSourceKeysLength (aux : Fin 7 → GP_p2) (M F _exponent eM eF B : GP_p2) : GP_p2 :=
  (B + 1) * ((((32 * F + 2) * (aux 0) + 2) ^ 2) * ((7 + eM + eF) * M))

def gp_queryGroupGatherBitBudget (aux : Fin 7 → GP_p2) (M F exponent eM eF B Rp W K : GP_p2) : GP_p2 :=
  Rp + (gp_queryGroupSourceKeysBitBudget aux) M F exponent eM eF B +
    (gp_queryGroupSourceKeysLength aux) M F exponent eM eF B * (W + 3) + K

def gp_wideMaterializationBitBudget (aux : Fin 7 → GP_p2) (M P B : GP_p2) : GP_p2 :=
  M * (gp_wideChildGridBitBudget_p0 P B + 6) +
    (M + 1) * (6 * M + 10) * (aux 2) + 1

def gp_tableReadFactor (R : GP_p2) : GP_p2 :=
  4 * (R + 4)

def gp_bandCoordinatesBitBudget (M vertices B : GP_p2) : GP_p2 :=
  vertices * (5 * M + 3) + (vertices * M + 1) ^ 2 * (24 * B + 12) + 1

def gp_bitPowerBitBudget_p1 (n B : GP_p2) : GP_p2 :=
  1 + n * (200 * ((n + 1) * (B + 1) + 1) ^ 2)

def gp_onlineIndexBitBudget (M vertices B : GP_p2) : GP_p2 :=
  gp_bandCoordinatesBitBudget M vertices B + 40 * (B + 4) +
    gp_bitPowerBitBudget_p1 80 (B + 4) + 3

def gp_queryOnlineRangeBitBudget (aux : Fin 7 → GP_p2) (M P B R : GP_p2) : GP_p2 :=
  let V := (aux 1)
  26 * B + 4 +
    ((gp_wideMaterializationBitBudget aux) M P B + (aux 6) + V + 1) *
      gp_tableReadFactor R + gp_onlineIndexBitBudget M V B + gp_bitPowerBitBudget_p1 80 (B + 4) +
      10000 * (80 * (B + 4) + 4) ^ 2 + 4

def gp_queryOnlineGatherBitBudget (aux : Fin 7 → GP_p2) (M P B Rp R W K : GP_p2) : GP_p2 :=
  Rp + gp_queryOnlineKeysBitBudget B +
    (B + 1) * ((gp_queryOnlineRangeBitBudget aux) M P (B + 1) R + W + 3) + K

def gp_queryHistoryInputsLength (M P history count : GP_p2) : GP_p2 :=
  count * (M * (history * (40 * P + 2) ^ 2))

def gp_queryGroupInputsLength (aux : Fin 7 → GP_p2) (M _exponent : GP_p2) : GP_p2 :=
  M * ((24 * (aux 0) * M + 2) * (4 * (aux 0) + 4))

def gp_querySharedCellInputsLength (aux : Fin 7 → GP_p2) (M exponent eM eF : GP_p2) : GP_p2 :=
  (7 + eM + eF) * (gp_queryGroupInputsLength aux) M exponent

def gp_querySharedInputsLength (aux : Fin 7 → GP_p2) (M F exponent eM eF B : GP_p2) : GP_p2 :=
  (B + 1) * ((((32 * F + 2) * (aux 0) + 2) ^ 2) * (gp_querySharedCellInputsLength aux) M exponent eM eF)

def gp_queryRefinementReadBudget (B Rp R earlier shared : GP_p2) : GP_p2 :=
  R + Rp + (1 + earlier * (32 * B + 12)) + (1 + shared * (24 * B + 9))

def gp_queryNeededInputsBitBudget (actions M B : GP_p2) : GP_p2 :=
  actions * (5 * M + 3) + 2 * M + actions * M +
    (actions * M + 1) ^ 2 * (202000 * (B + 1) ^ 2) + 4

def gp_queryRefinementStagesBudget (M B readCost earlierLength earlierCost onlineLength onlineCost sharedLength sharedCost groupLength groupCost parentCost finishCost : GP_p2) : GP_p2 :=
  earlierCost + earlierLength * (readCost + 3) + onlineCost + parentCost + sharedCost +
    sharedLength * (readCost + 3) + groupCost +
    gp_queryNeededInputsBitBudget (groupLength + onlineLength) M B +
    (groupLength + onlineLength) * M * (readCost + 3) + finishCost

def gp_queryRawHistoryInputsBitBudget (M P history count B : GP_p2) : GP_p2 :=
  let G := (40 * P + 2) ^ 2
  let C := gp_wideChildGridBitBudget_p0 P (B + 1)
  count * (M * (C + history * (5 * G + 3) + history + 2 + history * G + 3) +
    M * (history * G) + 3) + M + 1

def gp_queryEarlierInputsBitBudget (aux : Fin 7 → GP_p2) (M P F exponent history B R : GP_p2) : GP_p2 :=
  let count := (gp_queryEarlierRepresentativesLength aux) P F exponent B
  (gp_queryEarlierRepresentativesBitBudget aux) P F exponent B R +
    gp_queryRawHistoryInputsBitBudget M P history count B +
    (gp_queryHistoryInputsLength M P history count + 1) ^ 2 * (2002000 * (B + 1) ^ 2) + 2

def gp_groupSampleCountWordBudget (B : GP_p2) : GP_p2 :=
  64 * B + 46

def gp_queryGroupLabelsBitBudget (M B R : GP_p2) : GP_p2 :=
  gp_groupSampleCountBitBudget B + 8 * (gp_groupSampleCountWordBudget B) +
    M * (R + 4) + 4

def gp_queryGapStatesBitBudget (left right B : GP_p2) : GP_p2 :=
  let C := 1000 * (B + 10) ^ 2
  C + gp_gridPointsBitBudget_p0 left (B + 2) +
    left * (C + gp_gridPointsBitBudget_p0 right (B + 6) + right * (16 * (B + 6) + 11) + right + 7) + 3

def gp_queryRoundedStatesBitBudget (left right exponent B : GP_p2) : GP_p2 :=
  100000 * (32 * B + 210) ^ 2 + gp_queryGapStatesBitBudget left right (32 * B + 200) + exponent + 12

def gp_queryGroupInputsBitBudget (aux : Fin 7 → GP_p2) (M exponent B R : GP_p2) : GP_p2 :=
  let L := (24 * (aux 0) * M + 2) * (4 * (aux 0) + 4)
  gp_queryGroupLabelsBitBudget M B R +
    M * (gp_queryRoundedStatesBitBudget (24 * (aux 0) * M + 2) (4 * (aux 0) + 4) exponent B +
      5 * L + 4) + 1

def gp_querySharedCellInputsBitBudget (aux : Fin 7 → GP_p2) (M exponent eM eb eF B R : GP_p2) : GP_p2 :=
  let L := 7 + eM + eF
  gp_groupScalesBitBudget eM eb eF + 4 * L +
    L * ((gp_queryGroupInputsBitBudget aux) M exponent B R + L + (gp_queryGroupInputsLength aux) M exponent + 4) + eb + 4

def gp_querySharedInputsBitBudget (aux : Fin 7 → GP_p2) (M F exponent eM eF B R : GP_p2) : GP_p2 :=
  let cells := ((32 * F + 2) * (aux 0) + 2) ^ 2
  let samples := (gp_querySharedCellInputsLength aux) M exponent eM eF
  let sampleWork := (gp_querySharedCellInputsBitBudget aux) M exponent eM B eF (16 * B + 200) R
  let scaleWork := (gp_queryCellScanBitBudget aux) F exponent B +
    cells * (sampleWork + samples + 3) + B + exponent + 4
  gp_queryExponentsBitBudget_p0 B + 500 * (B + 1) ^ 2 + (B + 1) * (scaleWork + cells * samples + 3) +
    ((gp_querySharedInputsLength aux) M F exponent eM eF B + 1) ^ 2 * (202000 * (B + 1) ^ 2) + 3

def gp_queryRefinementFinishBitBudget (aux : Fin 7 → GP_p2) (_M P F B R _G _O : GP_p2) : GP_p2 :=
  R + gp_localRepresentativesBitBudget_p0 P F B * (R + 2) +
    (aux 5) * gp_tableReadFactor R + 2

def gp_queryFinishReadBudget (M B Rp earlierCount groups online : GP_p2) : GP_p2 :=
  Rp + 2 + earlierCount * (32 * B + 12) + (groups + online) * M * (24 * B + 9)

def gp_queryLocalRefinementBitBudget (aux : Fin 7 → GP_p2) (M _N P F exponent eM eF B _S t Rp R W Dg Do : GP_p2) : GP_p2 :=
  let earlier := gp_queryHistoryInputsLength M P t ((gp_queryEarlierRepresentativesLength aux) P F exponent B)
  let shared := (gp_querySharedInputsLength aux) M F exponent eM eF B
  let groups := (B + 1) * ((32 * F + 2) * (aux 0) + 2) ^ 2
  let U := gp_queryRefinementReadBudget B Rp R earlier shared
  gp_queryRefinementStagesBudget M B W earlier ((gp_queryEarlierInputsBitBudget aux) M P F exponent t B Rp)
    (B + 1) ((aux 4) * gp_tableReadFactor U * (Do + 4))
    shared ((gp_querySharedInputsBitBudget aux) M F exponent eM eF B Dg)
    groups ((aux 3) * gp_tableReadFactor U * (Dg + 4)) Rp
    ((gp_queryRefinementFinishBitBudget aux) M P F B (gp_queryFinishReadBudget M B Rp earlier groups (B + 1)) groups (B + 1))

def gp_queryGroupBufferReadBudget (count B V : GP_p2) : GP_p2 :=
  count * (40 * (40 * B + 500) + 15) + 200 * (V + 1) ^ 2 +
    30 * (V + 1) * (V + (40 * B + 500) + 1) + 4

def gp_queryBufferedGroupReadBudget (aux : Fin 7 → GP_p2) (M F exponent eM eF B V : GP_p2) : GP_p2 :=
  gp_queryGroupBufferReadBudget ((gp_queryGroupSourceKeysLength aux) M F exponent eM eF B) B V

def gp_queryOnlineBufferReadBudget (count B V : GP_p2) : GP_p2 :=
  count * (24 * (B + 1) + 9) + 200 * (V + 1) ^ 2 + 2

def gp_queryLocalSourcesBitBudget (aux : Fin 7 → GP_p2) (M N P F exponent eM eF B S t Rp R W : GP_p2) : GP_p2 :=
  (gp_queryGroupGatherBitBudget aux) M F exponent eM eF B Rp W
    ((gp_queryOnlineGatherBitBudget aux) M P B Rp R W
      ((gp_queryLocalRefinementBitBudget aux) M N P F exponent eM eF B S t Rp R W
        ((gp_queryBufferedGroupReadBudget aux) M F exponent eM eF B B)
        (gp_queryOnlineBufferReadBudget (B + 1) B B)))

def gp_queryBandReadBudget (aux : Fin 7 → GP_p2) (M P F exponent B : GP_p2) : GP_p2 :=
  1 + (gp_queryEarlierRepresentativesLength aux) P F exponent B * (M * (40 * P + 2) ^ 2) * (24 * B + 9)

def gp_queryLocalBandBitBudget (aux : Fin 7 → GP_p2) (M N P F exponent eM eF B S t Rp W : GP_p2) : GP_p2 :=
  (gp_queryBandGatherBitBudget aux) M P F exponent B Rp W
    ((gp_queryLocalSourcesBitBudget aux) M N P F exponent eM eF B S t Rp
      ((gp_queryBandReadBudget aux) M P F exponent B) W)

def gp_queryParentBufferReadBudget (aux : Fin 7 → GP_p2) (P F exponent B : GP_p2) : GP_p2 :=
  1 + (gp_queryInitialSupportLength aux) P F exponent B * (16 * B + 6)

def gp_queryLocalProgramBitBudget (aux : Fin 7 → GP_p2) (M N P F exponent eM eF B S t W : GP_p2) : GP_p2 :=
  (gp_queryInitialGatherBitBudget aux) P F exponent B W
    ((gp_queryLocalBandBitBudget aux) M N P F exponent eM eF B S t
      ((gp_queryParentBufferReadBudget aux) P F exponent B) W)

def queryGatherPolynomial : GP_p2 :=
  let aux : Fin 7 → GP_p2 := ![.input 9, .input 10, .input 11, .input 12, .input 13, .input 14, .input 15]
  gp_queryLocalProgramBitBudget aux (.input 0) 0 (.input 1) (.input 2) (.input 3)
    (.input 4) (.input 5) (.input 6) 0 (.input 7) (.input 8)

def queryGatherBitDegree : ℕ := queryGatherPolynomial.degree

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryProgramPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

attribute [local irreducible] preparedLocalGroupBitDegree onlineShellDegree physicalShellDegree
  representativeCompleteBitDegree queryGatherBitDegree

def queryPrimitiveBitDegree : ℕ :=
  max 1 (max preparedLocalGroupBitDegree
    (max onlineShellDegree (max physicalShellDegree representativeCompleteBitDegree)))

def queryLocalProgramBitDegree : ℕ := queryPrimitiveBitDegree * queryGatherBitDegree

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryProgramWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter

/-- Degree of the complete adaptive program when physical reads have degree `K`. -/
def computedQueryProgramDegree (K : ℕ) : ℕ := (K + 1) * (16 * queryLocalProgramBitDegree)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryWarmupBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter
attribute [local irreducible] queryInitialWarmupDegree queryInitialWarmupPrimitiveDegree queryInitialWarmupBitDegree queryChargedWarmupBitBudget

def computedQueryWarmupDegree (K : ℕ) : ℕ := (K + 1) * queryInitialWarmupDegree

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryTableBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter
attribute [local irreducible] queryLocalProgramBitDegree queryCallbackShellDegree queryInitialWarmupDegree

def computedActiveQueryDegree : ℕ := computedQueryProgramDegree (computedQueryReadDegree 1)

def computedActiveQueryBudget (N J t : ℕ) : ℕ :=
  BinaryFraction.queryLocalProgramBitBudget (integerParameters N).M N (integerParameters N).P
    (inputSmallLog N) (40 * smallLogExponent N) (heightExponent N / 20) (smallLogExponent N)
    (inputHeight N ^ 8)
    (inputHeight N ^ ((100 * (integerParameters N).M + 100000) *
      (coarseExponent (inputSmallLog N) + 1))) t
    (BinaryFraction.queryPhysicalDataBudget (integerParameters N).T J (inputHeight N ^ 8) (inputHeight N ^ 3)
      (50 * inputHeight N ^ 8 + 24)
      (BinaryFraction.queryFamilySourceReadBudget J (inputHeight N ^ 8) (50 * inputHeight N ^ 8 + 25)))

def computedTableQueryDegree : ℕ := max 2 (max (computedQueryWarmupDegree 1) computedActiveQueryDegree) + 1

def computedTableQueryBudget (N Amax J symbolBits positionBits t : ℕ) : ℕ :=
  queryChargedTableBitBudget (integerParameters N).M (integerParameters N).P (inputSmallLog N)
    Amax (inputHeight N ^ 2) J symbolBits positionBits (inputHeight N ^ 8) 1
    (computedActiveQueryBudget N J t)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryTableWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter BinaryFraction
attribute [local instance] queryArityNeZero queryRoundsNeZero
attribute [local irreducible] queryChargedFamilyTable localRequestValue

abbrev ComputedQueryTableParent (source target : List ℕ) (N : ℕ) :=
  {r : PhysicalTableRequest (integerParameters N).M
    (intervalTreeDepth (integerParameters N).M source.length) target.length //
    r.Bounded (computedSeedPassCount N + 1) (inputHeight N ^ 2) (integerParameters N).T (integerParameters N).S}

abbrev ComputedQueryTableKey (source target : List ℕ) (N : ℕ)
    (parent : ComputedQueryTableParent source target N) :=
  ChargedFamilyQueryKey (R := inputHeight N ^ 2) target N (integerParameters N).P
    (inputSmallLog N) (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80) (.inr parent)

def computedQueryTableProgram (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (parent : ComputedQueryTableParent source target N) :=
  queryChargedFamilyTable (R := inputHeight N ^ 2) source target N (integerParameters N).P
    (inputSmallLog N) (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
    (heightExponent N / 20) (smallLogExponent N) (computedParameterP_pos N) rfl rfl
    (fun pass => (scheduledSeedWordWithWork N pass).1) (fun pass => (computedQueryParameters N pass).factor)
    (computedQueryParameters N 0).tau (computedQueryParameters N 0).eta
    (computedQueryParameters N 0).kappa (computedQueryParameters N 0).delta
    (scheduledSeedMultiplier N) occurrence symbolBits positionBits parent

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryRawWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter BinaryFraction
attribute [local instance] queryArityNeZero queryRoundsNeZero
attribute [local irreducible] queryChargedFamilyTable localRequestValue

def computedQueryRawWorkDegree : ℕ := max 1 computedTableQueryDegree
def computedQueryRawWidthDegree : ℕ := max 1 queryRawWordDegree

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter BinaryFraction
attribute [local instance] queryArityNeZero queryRoundsNeZero
attribute [local irreducible] computedQueryRawWorkDegree computedQueryRawWidthDegree

def computedQueryWorkDegree : ℕ :=
  max computedQueryRawWorkDegree (computedQueryNormalizationDegree computedQueryRawWidthDegree) + 1

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryAnswer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
attribute [local instance] queryArityNeZero queryRoundsNeZero

/-- Binary output conversion, with the explicit equal-string guard. -/
def computedQueryAnswerWithWork (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) : List Bool × ℕ :=
  if source = target then ([], source.length + target.length + 1)
  else let result := computedQueryMemoResult source target N occurrence symbolBits positionBits input
    let answer := BinaryFraction.finalAnswerWithWork N result.value
    (answer.1, answer.2 + source.length + target.length + 1)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_IntegerBinaryOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

/-- Actual binary output on a fixed accepted finite draw. -/
def integerBinaryOutput (source target : List ℤ) (N : ℕ)
    (input : ComputedFamilyInput (source.map integerSymbolCode) (target.map integerSymbolCode) N) :=
  computedQueryAnswerWithWork (source.map integerSymbolCode) (target.map integerSymbolCode) N
    (integerOccurrenceIndex source target) (integerInputSymbolBits source target) (integerInputPositionBits target) input

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_OccurrenceStorage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
namespace PositionCounts

/-- All counters allocated in the position trie are bounded. -/
def CountsLE (C : ℕ) : PositionCounts → Prop
  | .empty => True
  | .node n l r => n ≤ C ∧ CountsLE C l ∧ CountsLE C r

end PositionCounts

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInputSpace
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation



theorem queryActionInputsAllocation_le_work {Parent Child : Type*} {M : ℕ}
    (actions : List (BinaryBellmanAction Parent Child M)) :
    queryActionInputsAllocation actions ≤ (queryActionInputsWithWork actions).2 := by
  have h := arithmeticFlatMapAllocation_le_work
    (fun action => arithmeticMapWithWork (fun i : Fin M => (action.childState i, 1)) (List.finRange M))
    (fun _ => arithmeticMapAllocation (fun _ : Fin M => 1) (List.finRange M) + M) actions (by
      intro action _
      simpa only [List.length_finRange] using arithmeticMapAllocation_with_spine
        (fun i : Fin M => (action.childState i, 1)) (fun _ => 1) (List.finRange M) (fun _ _ => le_rfl))
  unfold queryActionInputsAllocation queryActionInputsWithWork
  dsimp only
  omega



theorem queryNeededInputsAllocation_le_work {n M : ℕ}
    (selected online : List (BinaryBellmanAction (TargetInterval n) (Fin M × TargetInterval n) M)) :
    queryNeededInputsAllocation selected online ≤ (queryNeededInputsWithWork selected online).2 := by
  have hf := queryActionInputsAllocation_le_work selected
  have hs := queryActionInputsAllocation_le_work online
  have ho := queryOrderedChildInputsAllocation_le_work
    ((queryActionInputsWithWork selected).1 ++ (queryActionInputsWithWork online).1)
  unfold queryNeededInputsAllocation queryNeededInputsWithWork
  dsimp only
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryGatherSpace
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

open BitQuery

def queryInitialGatherHeap {ι β : Type*} {n : ℕ} (N P F exponent : ℕ) (hP : 0 < P)
    (a : BinaryFraction) (q : TargetInterval n)
    (reader : TargetInterval n → BitQuery ι BinaryFraction) (hr : ∀ key, Heap (reader key))
    (next : List (TargetInterval n) → List BinaryFraction → BitQuery ι β)
    (hn : ∀ keys words, Heap (next keys words)) :
    Heap (queryInitialGather N P F exponent hP a q reader next) :=
  (hr q).bind _ fun value =>
    (Heap.computeOf (BinaryFraction.queryInitialSupportWithWork N P F exponent hP a value q)
      (BinaryFraction.queryInitialSupportAllocation N P F exponent hP a value q)
      (BinaryFraction.queryInitialSupportAllocation_le_work N P F exponent hP a value q)).bind _ fun keys =>
        Heap.collect reader hr keys (next keys) (hn keys)

def queryBandGatherHeap {ι β : Type*} {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (N P F exponent : ℕ) (hP : 0 < P) (a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ) (allocation : TargetInterval ny → ℕ)
    (ha : ∀ r, allocation r ≤ (initial r).2) (q : TargetInterval ny)
    (massReader initialReader : (Fin M × TargetInterval ny) → BitQuery ι BinaryFraction)
    (hm : ∀ key, Heap (massReader key)) (hi : ∀ key, Heap (initialReader key))
    (next : List (Fin M × TargetInterval ny) → List BinaryFraction → List BinaryFraction → BitQuery ι β)
    (hn : ∀ keys mass words, Heap (next keys mass words)) :
    Heap (queryBandGather M parent N P F exponent hP a initial q massReader initialReader next) :=
  (Heap.computeOf (BinaryFraction.queryBandInputsWithWork M parent N P F exponent hP a initial q)
    (BinaryFraction.queryBandInputsAllocation M parent N P F exponent hP a initial allocation q)
    (BinaryFraction.queryBandInputsAllocation_le_work M parent N P F exponent hP a initial allocation q ha)).bind _ fun keys =>
      Heap.collect massReader hm keys _ fun mass => Heap.collect initialReader hi keys _ (hn keys mass)

def queryGroupSourceGatherHeap {ι β : Type*} {n : ℕ} (M N F Q exponent eM eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (a : BinaryFraction)
    (initial : TargetInterval n → BinaryFraction × ℕ) (allocation : TargetInterval n → ℕ)
    (ha : ∀ r, allocation r ≤ (initial r).2) (q : TargetInterval n)
    (reader : GroupScalarKey M F Q → BitQuery ι BinaryFraction) (hr : ∀ key, Heap (reader key))
    (next : List (GroupScalarKey M F Q) → List BinaryFraction → BitQuery ι β)
    (hn : ∀ keys words, Heap (next keys words)) :
    Heap (queryGroupSourceGather M N F Q exponent eM eF hM hF a initial q reader next) :=
  Heap.chargeOf (allocation q) (ha q)
    ((Heap.computeOf (BinaryFraction.queryGroupSourceKeysWithWork M N F Q exponent eM eF hM hF a (initial q).1 q)
      (BinaryFraction.queryGroupSourceKeysAllocation M N F Q exponent eM eF hM hF a (initial q).1 q)
      (BinaryFraction.queryGroupSourceKeysAllocation_le_work M N F Q exponent eM eF hM hF a (initial q).1 q)).bind _ fun keys =>
        Heap.collect reader hr keys (next keys) (hn keys))

def queryOnlineSourceGatherHeap {ι β : Type*} {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F exponent H : ℕ) (hP : 0 < P) (tau a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ) (initialAllocation : TargetInterval ny → ℕ)
    (child : Fin M → TargetInterval ny → BinaryFraction × ℕ)
    (childAllocation : Fin M → TargetInterval ny → ℕ)
    (hi : ∀ r, initialAllocation r ≤ (initial r).2)
    (hc : ∀ i r, childAllocation i r ≤ (child i r).2) (q : TargetInterval ny)
    (reader : (ℕ × TargetInterval ny) → ℕ → BitQuery ι BinaryFraction)
    (hr : ∀ key range, Heap (reader key range))
    (next : List (ℕ × TargetInterval ny) → List BinaryFraction → BitQuery ι β)
    (hn : ∀ keys words, Heap (next keys words)) :
    Heap (queryOnlineSourceGather parent N P F exponent H hP tau a initial child q reader next) :=
  Heap.chargeOf (initialAllocation q) (hi q)
    ((Heap.computeOf (BinaryFraction.queryOnlineKeysWithWork N P F hP a (initial q).1 q)
      (BinaryFraction.queryOnlineKeysAllocation N P F hP a (initial q).1 q)
      (BinaryFraction.queryOnlineKeysAllocation_le_work N P F hP a (initial q).1 q)).bind _ fun keys =>
        Heap.collect _ (fun key =>
          (Heap.computeOf (BinaryFraction.queryOnlineRangeWithWork parent P exponent H tau child key)
            (BinaryFraction.queryOnlineRangeAllocation parent P exponent H tau child childAllocation key)
            (BinaryFraction.queryOnlineRangeAllocation_le_work parent P exponent H tau child childAllocation key hc)).bind _ (hr key))
          keys (next keys) (hn keys))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryRefinementSpace
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open BitQuery

section Local
variable {ι α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (draw : CountedCellGroupDraws M F Q)
  (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
  (parentAllocation : TargetInterval target.length → ℕ)
  (childAllocation initialAllocation : Fin M → TargetInterval target.length → ℕ)
  (drawAllocation : CountedCellGroupAllocations M F Q)
  (integerAllocation : ℕ → TargetInterval target.length → ℕ)
  (hp : ∀ r, parentAllocation r ≤ (parentInitial r).2)
  (hca : ∀ i r, childAllocation i r ≤ (child i r).2)
  (hia : ∀ i r, initialAllocation i r ≤ (initial i r).2)
  (hd : ∀ b cell s j, drawAllocation b cell s j ≤ (draw b cell s j).2)
  (hz : ∀ b r, integerAllocation b r ≤ (integer b r).2)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (he : ∀ key, Heap (readEarlier key)) (hr : ∀ key, Heap (readCurrent key))

open BinaryFraction in
def queryLocalRefinementHeap : Heap (queryLocalRefinement source target parent N P F exponent H Q eM eF
    hP hM hF tau a eta kappa delta t parentInitial child initial R hc hi draw integer q readEarlier readCurrent) :=
  (Heap.computeOf (queryEarlierInputsWithWork M parent N P F exponent t hP a parentInitial q)
    (queryEarlierInputsAllocation M parent N P F exponent t hP a parentInitial parentAllocation q)
    (queryEarlierInputsAllocation_le_work M parent N P F exponent t hP a parentInitial parentAllocation q hp)).bind _
    fun earlierKeys => Heap.collect readEarlier he earlierKeys _ fun earlierWords =>
      (Heap.compute (queryOnlineSelectWithWork source target parent N P F exponent H hP
        tau a eta kappa parentInitial child initial R hc hi t integer earlierKeys earlierWords q)
        (queryOnlineSelectAllocation source target parent N P F exponent H hP tau a eta kappa
          parentInitial child initial R hc hi parentAllocation childAllocation initialAllocation
          t integer integerAllocation earlierKeys earlierWords q)
        (queryOnlineSelectAllocation_le_work source target parent N P F exponent H hP tau a eta kappa
          parentInitial child initial R hc hi parentAllocation childAllocation initialAllocation
          t integer integerAllocation earlierKeys earlierWords q hp hca hia hz)).bind _ fun online =>
        Heap.chargeOf (parentAllocation q) (hp q)
          ((Heap.computeOf (querySharedInputsWithWork M N F Q exponent eM eF hM hF parent a (parentInitial q).1 q draw)
            (querySharedInputsAllocation M N F Q exponent eM eF hM hF parent a (parentInitial q).1 q draw drawAllocation)
            (querySharedInputsAllocation_le_work M N F Q exponent eM eF hM hF parent a (parentInitial q).1 q draw drawAllocation hd)).bind _
            fun sharedKeys => Heap.collect readCurrent hr sharedKeys _ fun sharedWords =>
              (Heap.computeOf (queryGroupSelectWithWork source target parent N P F exponent Q eM eF hP hM hF
                tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q)
                (queryGroupSelectAllocation source target parent N P F exponent Q eM eF hP hM hF tau a
                  parentInitial child initial R hc hi parentAllocation childAllocation initialAllocation
                  draw drawAllocation sharedKeys sharedWords q)
                (queryGroupSelectAllocation_le_work source target parent N P F exponent Q eM eF hP hM hF tau a
                  parentInitial child initial R hc hi parentAllocation childAllocation initialAllocation
                  draw drawAllocation sharedKeys sharedWords q hp hca hia hd)).bind _ fun groups =>
                (Heap.computeOf (queryNeededInputsWithWork groups online)
                  (queryNeededInputsAllocation groups online) (queryNeededInputsAllocation_le_work groups online)).bind _
                    fun currentKeys => Heap.collect readCurrent hr currentKeys _ fun currentWords =>
                      Heap.computeOf (queryRefinementFinishWithWork parent N P F a delta parentInitial t
                        earlierKeys earlierWords groups online currentKeys currentWords q)
                        (queryRefinementFinishAllocation parent N P F a delta parentInitial parentAllocation t
                          earlierKeys earlierWords groups online currentKeys currentWords q)
                        (queryRefinementFinishAllocation_le_work parent N P F a delta parentInitial parentAllocation t
                          earlierKeys earlierWords groups online currentKeys currentWords q hp))

end Local
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryLocalProgramSpace
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open BitQuery

section Sources
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (parentAllocation : TargetInterval target.length → ℕ)
  (childAllocation initialAllocation : Fin M → TargetInterval target.length → ℕ)
  (hp : ∀ r, parentAllocation r ≤ (parentInitial r).2)
  (hca : ∀ i r, childAllocation i r ≤ (child i r).2)
  (hia : ∀ i r, initialAllocation i r ≤ (initial i r).2)
  (q : TargetInterval target.length)
  (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (hg : ∀ key, Heap (readGroup key)) (hz : ∀ key range, Heap (readInteger key range))
  (he : ∀ key, Heap (readEarlier key)) (hr : ∀ key, Heap (readCurrent key))

open BinaryFraction in
def queryLocalRandomSourcesHeap : Heap (queryLocalRandomSources source target parent N P F exponent H Q eM eF
    hP hM hF tau a eta kappa delta t parentInitial child initial R hc hi q
    readGroup readInteger readEarlier readCurrent) :=
  queryGroupSourceGatherHeap M N F Q exponent eM eF hM hF a parentInitial parentAllocation hp q
    readGroup hg _ fun groupKeys groupWords =>
      queryOnlineSourceGatherHeap parent N P F exponent H hP tau a parentInitial parentAllocation
        child childAllocation hp hca q readInteger hz _ fun onlineKeys onlineWords =>
          queryLocalRefinementHeap source target parent N P F exponent H Q eM eF hP hM hF
            tau a eta kappa delta t parentInitial child initial R hc hi
            (queryGroupDrawReadWithWork groupKeys groupWords)
            (queryOnlineIntegerReadWithWork onlineKeys onlineWords)
            parentAllocation childAllocation initialAllocation
            (queryGroupDrawReadAllocation groupKeys groupWords)
            (queryOnlineIntegerReadAllocation onlineKeys onlineWords)
            hp hca hia (queryGroupDrawReadAllocation_le_work groupKeys groupWords)
            (queryOnlineIntegerReadAllocation_le_work onlineKeys onlineWords) q readEarlier readCurrent he hr

end Sources

section Band
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (parentAllocation : TargetInterval target.length → ℕ)
  (hp : ∀ r, parentAllocation r ≤ (parentInitial r).2)
  (readMass readInitial : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (hm : ∀ key, Heap (readMass key)) (hi : ∀ key, Heap (readInitial key))
  (hg : ∀ key, Heap (readGroup key)) (hz : ∀ key range, Heap (readInteger key range))
  (he : ∀ key, Heap (readEarlier key)) (hr : ∀ key, Heap (readCurrent key))

open BinaryFraction in
def queryLocalBandHeap : Heap (queryLocalBand source target parent N P F exponent H Q eM eF hP hM hF
    tau a eta kappa delta t parentInitial readMass readInitial readGroup readInteger q readEarlier readCurrent) :=
  queryBandGatherHeap M parent N P F exponent hP a parentInitial parentAllocation hp q readMass readInitial hm hi _
    fun keys massWords initialWords =>
      queryLocalRandomSourcesHeap source target parent N P F exponent H Q eM eF hP hM hF
        tau a eta kappa delta t parentInitial
        (queryChildReadWithWork keys massWords) (queryChildReadWithWork keys initialWords)
        (queryDataReadBudget M target.length keys)
        (queryChildReadWithWork_budget keys massWords) (queryChildReadWithWork_budget keys initialWords)
        parentAllocation (queryChildReadAllocation keys massWords) (queryChildReadAllocation keys initialWords)
        hp (queryChildReadAllocation_le_work keys massWords) (queryChildReadAllocation_le_work keys initialWords)
        q readGroup readInteger readEarlier readCurrent hg hz he hr

end Band

section Program
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (readParent : TargetInterval target.length → BitQuery ι BinaryFraction)
  (readMass readInitial : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (hp : ∀ key, Heap (readParent key))
  (hm : ∀ key, Heap (readMass key)) (hi : ∀ key, Heap (readInitial key))
  (hg : ∀ key, Heap (readGroup key)) (hz : ∀ key range, Heap (readInteger key range))
  (he : ∀ key, Heap (readEarlier key)) (hr : ∀ key, Heap (readCurrent key))

open BinaryFraction in
def queryLocalProgramHeap : Heap (queryLocalProgram source target parent N P F exponent H Q eM eF hP hM hF
    tau a eta kappa delta t readParent readMass readInitial readGroup readInteger q readEarlier readCurrent) :=
  queryInitialGatherHeap N P F exponent hP a q readParent hp _ fun keys words =>
    queryLocalBandHeap source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa delta t
      (queryParentReadWithWork keys words) (queryParentReadAllocation keys words) (queryParentReadAllocation_le_work keys words)
      readMass readInitial readGroup readInteger q readEarlier readCurrent hm hi hg hz he hr

end Program
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryPhysicalReaderSpace
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

/-- Scalar RAM cells created by the node-code recurrence, two powers and
entry/table arithmetic. The path and input request are borrowed. -/


theorem physicalTableCodeAllocation_le_work {M J n : ℕ} (copies T S : ℕ)
    (request : PhysicalTableRequest M J n) :
    physicalTableCodeAllocation request ≤ (physicalTableCodeWithWork copies T S request).2 := by
  have tableBound (d J : ℕ) :
      2 * d + 2 * J + 20 ≤
        3 * d + 1 + (2 * J + 1) + 3 + 8 + (2 * J + 1) + 15 := by
    omega
  simp only [physicalTableCodeAllocation, physicalTableCodeWithWork, physicalEntryCodeWithWork,
    physicalNodeCodeWithWork, treeLayerCodeWithWork_cost, parameterPowerWithWork_spec]
  exact tableBound _ _

open BitQuery

def queryPhysicalTableReadHeap {M J n : ℕ} (copies T S : ℕ)
    (parent : PhysicalTableRequest M J n)
    (child : {r : PhysicalTableRequest M J n // r.combinedRank T S < parent.combinedRank T S}) :
    Heap (queryPhysicalTableRead copies T S parent child) :=
  Heap.chargeOf (physicalTableCodeAllocation child.val + 1)
    (Nat.add_le_add_right (physicalTableCodeAllocation_le_work copies T S child.val) 1)
    (.read child _ fun word => .done word)

def queryMeanReadHeap {ι : Type*} (count : ℕ) (reader : Fin count → BitQuery ι BinaryFraction)
    (hr : ∀ i, Heap (reader i)) : Heap (queryMeanRead count reader) := by
  refine Heap.chargeOf count (by omega) (Heap.collect reader hr _ _ fun words => ?_)
  refine Heap.computeOf (BinaryFraction.queryMeanWithWork count words)
    (BinaryFraction.sumListAllocation words + BinaryFraction.divAllocation
      (BinaryFraction.sumListWithWork words).1 (BinaryFraction.nat count) + Nat.size count) ?_
  have hs := BinaryFraction.sumListAllocation_le_work words
  have hd := BinaryFraction.divAllocation_le_work (BinaryFraction.sumListWithWork words).1 (BinaryFraction.nat count)
  unfold BinaryFraction.queryMeanWithWork
  dsimp only
  omega

def queryPhysicalEarlierReadHeap {M J n : ℕ} (copies pass copy T S t : ℕ)
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (q : TargetInterval n)
    (input : Fin M × ℕ × TargetInterval n) :
    Heap (queryPhysicalEarlierRead copies pass copy T S t node hbelow q input) := by
  refine Heap.chargeOf (input.2.1.bits.length + t.bits.length) ?_ ?_
  · exact (bitCompareWithWork_input_cells _ _).trans (Nat.le_succ _)
  · split
    · exact queryPhysicalTableReadHeap copies T S _ _
    · exact .done _

def queryPhysicalRandomDataRequestHeap {σ α : Type*} (source target : List α) {M J : ℕ} [NeZero M]
    (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
    (tau a eta kappa delta : BinaryFraction) (copies pass copy T S t : ℕ) (ht : 0 < t)
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (readGroup : GroupScalarKey M F Q → BitQuery σ BinaryFraction)
    (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery σ BinaryFraction)
    (q : TargetInterval target.length)
    (hg : ∀ key, Heap (readGroup key)) (hz : ∀ key range, Heap (readInteger key range)) :
    Heap (queryPhysicalRandomDataRequest source target N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta copies pass copy T S t ht node hbelow readGroup readInteger q) := by
  unfold queryPhysicalRandomDataRequest
  apply queryLocalProgramHeap
  · intro r
    exact (queryPhysicalTableReadHeap copies T S _ _).mapKeysWithWork _ (fun _ => 1) (fun _ => le_rfl)
  · intro input
    apply Heap.mapKeysWithWork _ (fun _ => 1) (fun _ => le_rfl)
    apply queryMeanReadHeap
    intro j
    exact queryPhysicalTableReadHeap copies T S _ _
  · intro input
    exact (queryPhysicalTableReadHeap copies T S _ _).mapKeysWithWork _ (fun _ => 1) (fun _ => le_rfl)
  · intro key
    exact (hg key).mapKeysWithWork _ (fun _ => 1) (fun _ => le_rfl)
  · intro key range
    exact (hz key range).mapKeysWithWork _ (fun _ => 1) (fun _ => le_rfl)
  · intro input
    exact (queryPhysicalEarlierReadHeap copies pass copy T S t node hbelow q input).mapKeysWithWork _
      (fun _ => 1) (fun _ => le_rfl)
  · intro input
    exact (queryPhysicalTableReadHeap copies T S _ _).mapKeysWithWork _ (fun _ => 1) (fun _ => le_rfl)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryChargedSeedSpace
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

/-- Scalar cells of the actual coarse/table address construction. -/


theorem chargedPhysicalCodeAllocation_le_work {M J n passes copies T S : ℕ}
    (request : ChargedPhysicalRequest M J n passes copies T S) :
    chargedPhysicalCodeAllocation request ≤ (chargedPhysicalCodeWithWork request).2 := by
  have entryBound (d J : ℕ) :
      2 * d + J + 12 ≤ 3 * d + 1 + (2 * J + 1) + 3 + 8 + 2 := by
    omega
  cases request with
  | inl entry =>
    simp only [chargedPhysicalCodeAllocation, chargedPhysicalCodeWithWork, physicalEntryCodeWithWork,
      physicalNodeCodeWithWork, treeLayerCodeWithWork_cost, parameterPowerWithWork_spec]
    exact entryBound _ _
  | inr request =>
    have h := physicalTableCodeAllocation_le_work copies T S request.val
    change physicalTableCodeAllocation request.val + 2 ≤ (physicalTableCodeWithWork copies T S request.val).2 + 3
    exact Nat.add_le_add h (by decide : 2 ≤ 3)

open BitQuery

section Seed
variable {M J n passes copies T S : ℕ}
  (parent : {r : PhysicalTableRequest M J n // r.Bounded passes copies T S})

def queryChargedReadHeap
    (key : {child : ChargedPhysicalRequest M J n passes copies T S //
      child.rank < ChargedPhysicalRequest.rank (.inr parent)}) : Heap (queryChargedRead parent key) :=
  Heap.chargeOf (chargedPhysicalCodeAllocation key.val + 1)
    (Nat.add_le_add_right (chargedPhysicalCodeAllocation_le_work key.val) 1) (.read key _ fun word => .done word)

def queryChargedSeedAtHeap (N : ℕ) (multiplier : ℕ → ℕ) (q : TargetInterval n) :
    Heap (queryChargedSeedAt parent N multiplier q) := by
  refine Heap.chargeOf (naturalEqualAllocation parent.val.pass 0)
    ((naturalEqualAllocation_le_work _ _).trans (Nat.le_succ _)) ?_
  split
  · exact queryChargedReadHeap parent _
  · refine Heap.chargeOf copies (Nat.le_succ _) ?_
    refine Heap.collect _ (fun _ => queryChargedReadHeap parent _) _ _ fun words => ?_
    let factor := multiplier (parent.val.pass - 1)
    refine Heap.computeOf (BinaryFraction.querySeedMedianWithWork N factor words)
      (BinaryFraction.seedMedianAllocation N factor words + (BinaryFraction.seedMedianWithWork N factor words).1.length + 1) ?_
    have hm := BinaryFraction.seedMedianAllocation_le_work N factor words
    unfold BinaryFraction.querySeedMedianWithWork
    dsimp only
    omega

end Seed
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryIndexedSpace
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

/-- The occurrence key, two prefix traversals and scalar result cells.
The occurrence trie itself is borrowed from preprocessing. -/


theorem indexedLeafAllocation_le_work (table : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (symbol : Option ℕ) (lo hi : ℕ) :
    indexedLeafAllocation symbolBits positionBits symbol lo hi ≤
      (indexedLeafWithWork table symbolBits positionBits symbol lo hi).2 := by
  cases symbol with
  | none => change 1 ≤ 2; omega
  | some a =>
    unfold indexedLeafAllocation indexedLeafWithWork indexedSingletonCostWithWork
    split_ifs <;> simp only [occurrenceQueryWithWork_spec] <;> omega



theorem binaryIndexedLeafAllocation_le_work (table : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (symbol : Option ℕ) (lo hi : ℕ) :
    binaryIndexedLeafAllocation table symbolBits positionBits symbol lo hi ≤
      (binaryIndexedLeafWithWork table symbolBits positionBits symbol lo hi).2 :=
  Nat.add_le_add_right (Nat.add_le_add_right (indexedLeafAllocation_le_work table symbolBits positionBits symbol lo hi) _) _



theorem queryIndexedSliceAllocation_le_work (source : List ℕ) (interval : TargetInterval source.length)
    (targetLength : ℕ) (q : TargetInterval targetLength)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ) :
    queryIndexedSliceAllocation source interval targetLength q occurrence symbolBits positionBits ≤
      (queryIndexedSliceWithWork source interval targetLength q occurrence symbolBits positionBits).2 := by
  have hc := bitCompareWithWork_input_cells interval.lo.bits interval.hi.bits
  have hl := binaryIndexedLeafAllocation_le_work occurrence symbolBits positionBits
    (querySliceHeadWithWork source interval).1 q.lo q.hi
  have hs : interval.lo.bits.length + interval.hi.bits.length + 1 ≤
      (querySliceHeadWithWork source interval).2 := by
    unfold querySliceHeadWithWork
    dsimp only
    change _ ≤ (bitCompareWithWork interval.lo.bits interval.hi.bits).2 + _ + _ + 3
    omega
  unfold queryIndexedSliceAllocation queryIndexedSliceWithWork
  dsimp only
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInitialConeSpace
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open BitQuery BinaryFraction

def queryInitialConeProgramAtHeap {ι : Type*} {n : ℕ} (sourceLength N P F : ℕ) (A a : BinaryFraction)
    (reader : TargetInterval n → BitQuery ι BinaryFraction) (q : TargetInterval n)
    (hr : ∀ r, Heap (reader r)) : Heap (queryInitialConeProgramAt sourceLength N P F A a reader q) :=
  (hr q).bind _ fun value =>
    (Heap.computeOf (queryInitialConeCentersWithWork N P A value q)
      (queryInitialConeCentersAllocation N P A value q)
      (queryInitialConeCentersAllocation_le_work N P A value q)).bind _ fun keys =>
        Heap.collect reader hr keys _ fun words =>
          Heap.computeOf (cachedInitialProgramReadWithWork sourceLength N P F A a
            (queryInitialSeedReadWithWork value q keys words) q)
            (cachedInitialProgramReadAllocation (queryInitialSeedReadWithWork value q keys words)
              (queryInitialSeedReadAllocation value q keys words) sourceLength N P F A a q)
            (cachedInitialProgramReadAllocation_le_work (queryInitialSeedReadWithWork value q keys words)
              (queryInitialSeedReadAllocation value q keys words) sourceLength N P F A a q
              (queryInitialSeedReadAllocation_le_work value q keys words))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryWarmupSpace
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open BitQuery BinaryFraction

def queryWarmupProgramHeap {ι : Type*} {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F : ℕ) (a : BinaryFraction)
    (initialRead : TargetInterval ny → BitQuery ι BinaryFraction)
    (childRead : (Fin M × TargetInterval ny) → BitQuery ι BinaryFraction) (q : TargetInterval ny)
    (hi : ∀ r, Heap (initialRead r)) (hc : ∀ key, Heap (childRead key)) :
    Heap (queryWarmupProgram parent N P F a initialRead childRead q) :=
  (hi q).bind _ fun value =>
    (Heap.computeOf (queryRawCentersWithWork N P F a value q)
      (queryRawCentersAllocation N P F a value q) (queryRawCentersAllocation_le_work N P F a value q)).bind _ fun centers =>
      Heap.collect initialRead hi centers _ fun words =>
        let initial := queryOverrideParentReadWithWork value q centers words
        let allocation := queryOverrideParentReadAllocation q centers words
        let halloc := queryOverrideParentReadAllocation_le_work value q centers words
        (Heap.computeOf (queryWarmupInputsWithWork M parent N P F a initial q)
          (queryWarmupInputsAllocation M parent N P F a initial allocation q)
          (queryWarmupInputsAllocation_le_work M parent N P F a initial allocation q halloc)).bind _ fun inputs =>
            Heap.collect childRead hc inputs _ fun childWords =>
              Heap.computeOf (localWarmupReadKernelWithWork parent N P F a initial
                (fun input => queryChildReadWithWork inputs childWords input.1 input.2) q)
                (localWarmupReadAllocation parent N P F a initial allocation
                  (fun input => queryChildReadWithWork inputs childWords input.1 input.2)
                  (fun input => queryChildReadAllocation inputs childWords input.1 input.2) q)
                (localWarmupReadAllocation_le_work parent N P F a initial allocation
                  (fun input => queryChildReadWithWork inputs childWords input.1 input.2)
                  (fun input => queryChildReadAllocation inputs childWords input.1 input.2) q halloc
                  (fun input => queryChildReadAllocation_le_work inputs childWords input.1 input.2))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryChargedWarmupSpace
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open BitQuery

section Initial
variable (source target : List ℕ) {M J passes copies T S : ℕ}
  (N P F : ℕ) (A a : BinaryFraction) (multiplier : ℕ → ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)

def queryPhysicalInitialHeap (q : TargetInterval target.length) :
    Heap (queryPhysicalInitial source target N P F A a multiplier parent occurrence symbolBits positionBits q) := by
  let interval := physicalSourceInterval source.length parent.val.node
  have hl := saturatingSubtractAllocation_le_work interval.hi interval.lo
  have ht := naturalWordLEAllocation_le_work (saturatingSubtractWithWork interval.hi interval.lo).1 [true]
  refine Heap.chargeOf (saturatingSubtractAllocation interval.hi interval.lo +
    naturalWordLEAllocation (saturatingSubtractWithWork interval.hi interval.lo).1 [true]) (by
      dsimp only [interval] at hl ht ⊢
      omega) ?_
  split
  · exact Heap.computeOf _ (queryIndexedSliceAllocation source interval target.length q occurrence symbolBits positionBits)
      (queryIndexedSliceAllocation_le_work source interval target.length q occurrence symbolBits positionBits)
  · exact queryInitialConeProgramAtHeap _ N P F A a (queryChargedSeedAt parent N multiplier) q
      (queryChargedSeedAtHeap parent N multiplier)

def queryChargedWarmupHeap :
    Heap (queryChargedWarmup source target N P F A a multiplier parent occurrence symbolBits positionBits) := by
  have hinit := queryPhysicalInitialHeap source target N P F A a multiplier parent occurrence symbolBits positionBits
  unfold queryChargedWarmup
  refine Heap.chargeOf (naturalEqualAllocation parent.val.index 0)
    ((naturalEqualAllocation_le_work _ _).trans (Nat.le_succ _)) ?_
  split
  · exact hinit _
  · refine Heap.chargeOf (parent.val.node.1.val.bits.length + J.bits.length)
      ((bitCompareWithWork_input_cells _ _).trans (Nat.le_succ _)) ?_
    split
    · let interval := physicalSourceInterval source.length parent.val.node
      have hl := saturatingSubtractAllocation_le_work interval.hi interval.lo
      have ht := naturalWordLEAllocation_le_work (saturatingSubtractWithWork interval.hi interval.lo).1 [true]
      refine Heap.chargeOf (saturatingSubtractAllocation interval.hi interval.lo +
        naturalWordLEAllocation (saturatingSubtractWithWork interval.hi interval.lo).1 [true]) (by
          dsimp only [interval] at hl ht ⊢
          omega) ?_
      split
      · exact hinit _
      · apply queryWarmupProgramHeap
        · exact hinit
        · intro input
          exact queryChargedReadHeap parent _
    · exact hinit _

end Initial
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryRestrictionSpace
attribute [-instance] _root_.OAI.EditApproximation.PhysicalTableRequest.decidableBounded _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation



theorem queryPhysicalBoundedAllocation_le_work {M J n : ℕ} (passes copies T S : ℕ)
    (request : PhysicalTableRequest M J n) :
    queryPhysicalBoundedAllocation passes copies T S request ≤ (queryPhysicalBoundedWithWork passes copies T S request).2 := by
  have hp := bitCompareWithWork_input_cells request.pass.bits passes.bits
  have hc := bitCompareWithWork_input_cells request.copy.bits copies.bits
  have ha := binaryNaturalAddAllocation_le_work T S
  have hi := naturalWordLEAllocation_le_work request.index.bits (binaryNaturalAddWithWork T S).1
  unfold queryPhysicalBoundedAllocation queryPhysicalBoundedWithWork
  dsimp only
  unfold binaryNaturalCompareWithWork
  omega



theorem querySupportedChildAllocation_le_work {σ : Type*} {M J n : ℕ} (passes copies T S : ℕ)
    (parent : {r : PhysicalTableRequest M J n // r.Bounded passes copies T S})
    (key : QueryPhysicalChild (σ := σ) passes copies T S parent) :
    querySupportedChildAllocation passes copies T S parent key ≤ (querySupportedChildWithWork passes copies T S parent key).2 := by
  cases key with
  | inl source => exact Nat.zero_le _
  | inr child => exact queryPhysicalBoundedAllocation_le_work passes copies T S child.val

open BitQuery

def queryRestrictPhysicalBodyHeap {σ : Type*} {M J n : ℕ} (passes copies T S : ℕ)
    (parent : {r : PhysicalTableRequest M J n // r.Bounded passes copies T S})
    (program : BitQuery (QueryPhysicalChild (σ := σ) passes copies T S parent) BinaryFraction)
    (heap : Heap program) : Heap (queryRestrictPhysicalBody passes copies T S parent program) :=
  (heap.restrictWithWork _ _ (querySupportedChildWithWork_value passes copies T S parent)
    (querySupportedChildAllocation passes copies T S parent)
    (querySupportedChildAllocation_le_work passes copies T S parent)).mapKeysWithWork _ (fun _ => 1) (fun _ => le_rfl)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryScalarGuardSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation



theorem queryNaturalIndexAllocation_le_work (a : ℕ) (xs : List ℕ) :
    queryNaturalIndexAllocation a xs ≤ (queryNaturalIndexWithWork a xs).2 := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons b rest ih =>
    have he := naturalEqualAllocation_le_work a b
    simp only [queryNaturalIndexAllocation, queryNaturalIndexWithWork]
    split_ifs <;> dsimp only <;> omega



theorem queryScaleDispatchAllocation_le_work (N b : ℕ) :
    queryScaleDispatchAllocation N b ≤ (queryScaleDispatchWithWork N b).2 := by
  have hd := dyadicScalesAllocation_le_work N
  have hi := queryNaturalIndexAllocation_le_work b (dyadicScalesWithWork N).1
  unfold queryScaleDispatchAllocation queryScaleDispatchWithWork
  dsimp only
  omega



theorem queryScalePresentAllocation_le_work (N b : ℕ) :
    queryScalePresentAllocation N b ≤ (queryScalePresentWithWork N b).2 := by
  have hd := queryScaleDispatchAllocation_le_work N b
  have hc := bitCompareWithWork_input_cells (queryScaleDispatchWithWork N b).1.bits (max 1 N.bits.length).bits
  unfold queryScalePresentAllocation queryScalePresentWithWork
  dsimp only
  change _ ≤ _ + (bitCompareWithWork (queryScaleDispatchWithWork N b).1.bits (max 1 N.bits.length).bits).2 + 2
  omega



theorem queryCellValidAllocation_le_work (n exponent : ℕ) (cell : ℕ × ℕ) :
    queryCellValidAllocation n exponent cell ≤ (queryCellValidWithWork n exponent cell).2 := by
  have hm := binaryNaturalMulAllocation_le_work n (bitWordValue (powerTwoWord exponent))
  have hl := naturalWordLEAllocation_le_work cell.1.bits (binaryNaturalMulWithWork n (bitWordValue (powerTwoWord exponent))).1
  have hr := naturalWordLEAllocation_le_work cell.2.bits (binaryNaturalMulWithWork n (bitWordValue (powerTwoWord exponent))).1
  unfold queryCellValidAllocation queryCellValidWithWork
  dsimp only
  omega



theorem queryRangeValidAllocation_le_work (B range : ℕ) :
    queryRangeValidAllocation B range ≤ (queryRangeValidWithWork B range).2 := by
  have hp := bitCompareWithWork_input_cells (0 : ℕ).bits range.bits
  have hb := naturalWordLEAllocation_le_work range.bits B.bits
  unfold queryRangeValidAllocation queryRangeValidWithWork
  dsimp only
  change _ ≤ (bitCompareWithWork (0 : ℕ).bits range.bits).2 + _ + 2
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryScalarReadSpace
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

theorem naturalPairWithWork_lower (a b : ℕ) : 4 ≤ (naturalPairWithWork a b).2 := by
  unfold naturalPairWithWork
  split_ifs <;> omega

/-- Address-recurrence and pairing cells; source data and node paths are borrowed. -/


theorem physicalScalarCodeAllocation_le_work {M J N n exponent F Q R B : ℕ}
    (key : PhysicalScalarKey M J N n exponent F Q R B) :
    physicalScalarCodeAllocation key ≤ (physicalScalarCodeWithWork key).2 := by
  have onlineBound (d J a b c : ℕ) (ha : 4 ≤ a) (hb : 4 ≤ b) (hc : 4 ≤ c) :
      2 * d + J + 20 ≤ 3 * d + 1 + (2 * J + 1) + 3 + 8 + a + b + c + 2 := by
    omega
  have groupBound (d J a b c e f g : ℕ)
      (ha : 4 ≤ a) (hb : 4 ≤ b) (hc : 4 ≤ c) (he : 4 ≤ e) (hf : 4 ≤ f) (hg : 4 ≤ g) :
      2 * d + J + 25 ≤ 3 * d + 1 + (2 * J + 1) + 3 + a + b + c + e + f + g + 3 := by
    omega
  rcases key with ⟨online | group, index⟩
  · have h1 := naturalPairWithWork_lower online.2.val.val index.val
    have h2 := naturalPairWithWork_lower online.1.2.1.val (naturalPairWithWork online.2.val.val index.val).1
    have h3 := naturalPairWithWork_lower (physicalEntryCodeWithWork (online.1.1.val, online.1.2.2)).1
      (naturalPairWithWork online.1.2.1.val (naturalPairWithWork online.2.val.val index.val).1).1
    simp only [physicalScalarCodeAllocation, physicalScalarCodeWithWork, physicalEntryCodeWithWork,
      physicalNodeCodeWithWork, treeLayerCodeWithWork_cost, parameterPowerWithWork_spec] at h3 ⊢
    exact onlineBound _ _ _ _ _ h1 h2 h3
  · have h1 := naturalPairWithWork_lower index.2.1.val index.2.2.val
    have h2 := naturalPairWithWork_lower index.1.val (naturalPairWithWork index.2.1.val index.2.2.val).1
    have h3 := naturalPairWithWork_lower group.2.2.2.val
      (naturalPairWithWork index.1.val (naturalPairWithWork index.2.1.val index.2.2.val).1).1
    have h4 := naturalPairWithWork_lower group.2.2.1.val
      (naturalPairWithWork group.2.2.2.val (naturalPairWithWork index.1.val (naturalPairWithWork index.2.1.val index.2.2.val).1).1).1
    have h5 := naturalPairWithWork_lower group.2.1.val
      (naturalPairWithWork group.2.2.1.val (naturalPairWithWork group.2.2.2.val
        (naturalPairWithWork index.1.val (naturalPairWithWork index.2.1.val index.2.2.val).1).1).1).1
    have h6 := naturalPairWithWork_lower (physicalNodeCodeWithWork group.1.val).1
      (naturalPairWithWork group.2.1.val (naturalPairWithWork group.2.2.1.val
        (naturalPairWithWork group.2.2.2.val (naturalPairWithWork index.1.val
          (naturalPairWithWork index.2.1.val index.2.2.val).1).1).1).1).1
    simp only [physicalScalarCodeAllocation, physicalScalarCodeWithWork,
      physicalNodeCodeWithWork, treeLayerCodeWithWork_cost, parameterPowerWithWork_spec] at h6 ⊢
    exact groupBound _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6

open BitQuery

section Scalar
variable (M J N n exponent F Q R B : ℕ)

def queryPhysicalScalarReadHeap (key : PhysicalScalarKey M J N n exponent F Q R B) :
    Heap (queryPhysicalScalarRead M J N n exponent F Q R B key) :=
  Heap.chargeOf (physicalScalarCodeAllocation key + 1)
    (Nat.add_le_add_right (physicalScalarCodeAllocation_le_work key) 1) (.read key _ fun word => .done word)

def groupHeapTransport (b c : ℕ) (h : b = c)
    (actual : BitPhysicalGroupQueries M J N n exponent F Q R B b)
    (heap : ∀ s j, Heap (actual s j)) :
    ∀ s j, Heap ((Eq.mp (congrArg (BitPhysicalGroupQueries M J N n exponent F Q R B) h) actual) s j) := by
  cases h
  exact heap

def queryPhysicalScalarGroupQueriesHeap (node : PhysicalInternalNode M J) (time : Fin R)
    (b : ℕ) (cell : ℕ × ℕ) :
    ∀ s j, Heap (queryPhysicalScalarGroupQueries M J N n exponent F Q R B node time b cell s j) := by
  intro s j
  refine (congrArg BitQuery.Heap (congrArg
    (fun f : BitPhysicalGroupQueries M J N n exponent F Q R B b => f s j)
    (queryPhysicalScalarGroupQueries.eq_1 M J N n exponent F Q R B node time b cell))).mpr ?_
  split
  · rename_i hb
    split
    · rename_i hc
      let key : PhysicalLocalGroupKey M J N n exponent :=
        (node, physicalScaleIndex N b ((queryScalePresentWithWork_value N b).mp hb),
          ⟨cell.1, Nat.lt_succ_of_le ((queryCellValidWithWork_value n exponent cell).mp hc).1⟩,
          ⟨cell.2, Nat.lt_succ_of_le ((queryCellValidWithWork_value n exponent cell).mp hc).2⟩)
      exact groupHeapTransport M J N n exponent F Q R B _ _
        (physicalScaleIndex_get N b ((queryScalePresentWithWork_value N b).mp hb))
        (queryPhysicalScalarGroupQueriesAt M J N n exponent F Q R B key time)
        (fun s j => (congrArg BitQuery.Heap
          (queryPhysicalScalarGroupQueriesAt.eq_1 M J N n exponent F Q R B key time s j)).mpr
            (queryPhysicalScalarReadHeap M J N n exponent F Q R B
              ⟨Sum.inr key, ⟨time, ⟨s, j⟩⟩⟩)) s j
    · exact .done _
  · exact .done _

def queryPhysicalScalarGroupReadHeap (node : PhysicalInternalNode M J) (time : Fin R)
    (key : GroupScalarKey M F Q) : Heap (queryPhysicalScalarGroupRead M J N n exponent F Q R B node time key) :=
  Heap.chargeOf (queryScalePresentAllocation N key.1.1 + queryCellValidAllocation n exponent key.1.2)
    (by have h1 := queryScalePresentAllocation_le_work N key.1.1
        have h2 := queryCellValidAllocation_le_work n exponent key.1.2
        omega)
    (queryPhysicalScalarGroupQueriesHeap M J N n exponent F Q R B node time key.1.1 key.1.2 key.2.1 key.2.2)

def queryPhysicalScalarOnlineReadHeap (node : PhysicalInternalNode M J) (time : Fin R)
    (key : ℕ × TargetInterval n) (range : ℕ) :
    Heap (queryPhysicalScalarOnlineRead M J N n exponent F Q R B node time key range) := by
  refine (congrArg BitQuery.Heap
    (queryPhysicalScalarOnlineRead.eq_1 M J N n exponent F Q R B node time key range)).mpr ?_
  refine BitQuery.Heap.chargeOf (queryScalePresentAllocation N key.1 + queryRangeValidAllocation B range) ?_ ?_
  · have h1 := queryScalePresentAllocation_le_work N key.1
    have h2 := queryRangeValidAllocation_le_work B range
    omega
  · split
    · rename_i hb
      split
      · rename_i hr
        exact queryPhysicalScalarReadHeap M J N n exponent F Q R B
          ⟨.inl ((node, physicalScaleIndex N key.1 ((queryScalePresentWithWork_value N key.1).mp hb), key.2),
            positiveDrawRangeOfLE B range ((queryRangeValidWithWork_value B range).mp hr).1
              ((queryRangeValidWithWork_value B range).mp hr).2), time⟩
      · exact .done _
    · exact .done _

end Scalar

section Family
variable {α : Type*} {M J R : ℕ} (target : List α)
  (N P F exponent H Q passes copies pass copy : ℕ)



theorem queryFamilyTagAllocation_le_work
    (scalar : PhysicalScalarKey M J N target.length exponent F Q R (localOnlineMassBound M P H)) :
    queryFamilyTagAllocation target N P F exponent H Q passes copies pass copy scalar ≤
      (queryFamilyTagWithWork target N P F exponent H Q passes copies pass copy scalar).2 := by
  let p := (queryFinOfNatWithWork (passes + 1) pass (Nat.succ_pos _)).1
  let c := (queryFinOfNatWithWork (copies + 1) copy (Nat.succ_pos _)).1
  have hp := binaryNaturalDivAllocation_le_work pass (passes + 1)
  have hc := binaryNaturalDivAllocation_le_work copy (copies + 1)
  have hs := physicalScalarCodeAllocation_le_work scalar
  have hcp := naturalPairWithWork_lower c.val (physicalScalarCodeWithWork scalar).1
  have hpp := naturalPairWithWork_lower p.val (naturalPairWithWork c.val (physicalScalarCodeWithWork scalar).1).1
  unfold queryFamilyTagAllocation queryFamilyTagWithWork physicalFamilyCodeWithWork
  dsimp only
  dsimp only [p, c, queryFinOfNatWithWork] at hcp hpp ⊢
  omega

def queryFamilyGroupReadHeap (node : PhysicalInternalNode M J) (time : Fin R) (key : GroupScalarKey M F Q) :
    Heap (queryFamilyGroupRead target N P F exponent H Q passes copies pass copy node time key) :=
  (queryPhysicalScalarGroupReadHeap M J N target.length exponent F Q R (localOnlineMassBound M P H) node time key).mapKeysWithWork
    _ (queryFamilyTagAllocation target N P F exponent H Q passes copies pass copy)
    (queryFamilyTagAllocation_le_work target N P F exponent H Q passes copies pass copy)

def queryFamilyOnlineReadHeap (node : PhysicalInternalNode M J) (time : Fin R)
    (key : ℕ × TargetInterval target.length) (range : ℕ) :
    Heap (queryFamilyOnlineRead target N P F exponent H Q passes copies pass copy node time key range) :=
  (queryPhysicalScalarOnlineReadHeap M J N target.length exponent F Q R (localOnlineMassBound M P H) node time key range).mapKeysWithWork
    _ (queryFamilyTagAllocation target N P F exponent H Q passes copies pass copy)
    (queryFamilyTagAllocation_le_work target N P F exponent H Q passes copies pass copy)

end Family
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryFamilySpace
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open BitQuery

section Family
variable {α : Type*} {M J R : ℕ} [NeZero M] (source target : List α)
  (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (passes copies pass copy T S t : ℕ) (ht : 0 < t)
  (node : PhysicalNode M J) (hbelow : node.1.val < J) (time : Fin R)
  (q : TargetInterval target.length)

def queryFamilyRefinementHeap : Heap (queryFamilyRefinement source target N P F exponent H Q eM eF hP hM hF
    tau a eta kappa delta passes copies pass copy T S t ht node hbelow time q) :=
  queryPhysicalRandomDataRequestHeap source target N P F exponent H Q eM eF hP hM hF
    tau a eta kappa delta copies pass copy T S t ht node hbelow _ _ q
    (queryFamilyGroupReadHeap target N P F exponent H Q passes copies pass copy ⟨node, hbelow⟩ time)
    (queryFamilyOnlineReadHeap target N P F exponent H Q passes copies pass copy ⟨node, hbelow⟩ time)

end Family

section Active
variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (T S passes copies : ℕ)
  (request : PhysicalTableRequest M J target.length)
  (hindex : T < request.index) (hbelow : request.node.1.val < J)

def queryFamilyActiveHeap : Heap (queryFamilyActive (R := R) source target N P F exponent H Q eM eF hP hM hF
    tau a eta kappa delta T S passes copies request hindex hbelow) :=
  (queryFamilyRefinementHeap source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta
    passes copies request.pass request.copy T S (request.index - T) (Nat.sub_pos_of_lt hindex)
    request.node hbelow (Fin.ofNat R (request.index - T - 1)) request.state).mapKeysWithWork _ (fun _ => 1) (fun _ => le_rfl)

end Active

section Bounded
variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (T S passes copies : ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S})
  (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J)

def queryFamilyBoundedActiveHeap : Heap (queryFamilyBoundedActive (R := R) source target N P F exponent H Q eM eF
    hP hM hF tau a eta kappa delta T S passes copies parent hindex hbelow) :=
  queryRestrictPhysicalBodyHeap (passes + 1) copies T S parent _
    (queryFamilyActiveHeap (R := R) source target N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta T S passes copies parent.val hindex hbelow)

end Bounded
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryChargedFamilySpace
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open BitQuery

section Family
variable {M J R passes copies T S : ℕ} [NeZero M] [NeZero R]
  (source target : List ℕ) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction) (multiplier : ℕ → ℕ)
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)

def queryChargedFamilyTableHeap
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S}) :
    Heap (queryChargedFamilyTable (R := R) source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits parent) := by
  have hinit := queryPhysicalInitialHeap source target N P F (A parent.val.pass) (a parent.val.pass)
    multiplier parent occurrence symbolBits positionBits parent.val.state
  unfold queryChargedFamilyTable
  refine Heap.chargeOf (naturalWordLEAllocation parent.val.index.bits T.bits)
    ((naturalWordLEAllocation_le_work _ _).trans (Nat.le_succ _)) ?_
  split
  · exact (queryChargedWarmupHeap source target N P F (A parent.val.pass) (a parent.val.pass)
      multiplier parent occurrence symbolBits positionBits).mapKeysWithWork _ (fun _ => 1) (fun _ => le_rfl)
  · refine Heap.chargeOf (parent.val.node.1.val.bits.length + J.bits.length)
      ((bitCompareWithWork_input_cells _ _).trans (Nat.le_succ _)) ?_
    split
    · let interval := physicalSourceInterval source.length parent.val.node
      have hl := saturatingSubtractAllocation_le_work interval.hi interval.lo
      have ht := naturalWordLEAllocation_le_work (saturatingSubtractWithWork interval.hi interval.lo).1 [true]
      refine Heap.chargeOf (saturatingSubtractAllocation interval.hi interval.lo +
        naturalWordLEAllocation (saturatingSubtractWithWork interval.hi interval.lo).1 [true]) (by
          dsimp only [interval] at hl ht ⊢
          omega) ?_
      split
      · exact hinit.mapKeysWithWork _ (fun _ => 1) (fun _ => le_rfl)
      · exact (queryFamilyBoundedActiveHeap (R := R) source target N P F exponent H Q eM eF hP hM hF
          tau (a parent.val.pass) eta kappa delta T S passes copies parent _ _).mapKeysWithWork _
          (fun _ => 1) (fun _ => le_rfl)
    · exact hinit.mapKeysWithWork _ (fun _ => 1) (fun _ => le_rfl)

def queryChargedFamilyGlobalHeap
    (coarse : PhysicalEntry M J target.length → BinaryFraction × ℕ)
    (allocation : PhysicalEntry M J target.length → ℕ)
    (hc : ∀ entry, allocation entry ≤ 3 * (coarse entry).2)
    (request : ChargedPhysicalRequest M J target.length (passes + 1) copies T S) :
    Heap (queryChargedFamilyGlobal (R := R) source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse request) := by
  cases request with
  | inl entry => exact Heap.compute (coarse entry) (allocation entry) (hc entry)
  | inr parent =>
    exact queryChargedFamilyTableHeap (R := R) source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits parent

end Family
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryFamilyMemoSpace
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open BitQuery

section Family
variable {M J R passes copies T S : ℕ} [NeZero M] [NeZero R]
  (source target : List ℕ) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction) (multiplier : ℕ → ℕ)
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
  (coarse : PhysicalEntry M J target.length → BinaryFraction × ℕ)
  (allocation : PhysicalEntry M J target.length → ℕ)
  (hc : ∀ entry, allocation entry ≤ 3 * (coarse entry).2)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies)

def queryFamilyMemoRawHeap
    (key : QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes)
      (copies := copies) (T := T) (S := S) target N P F exponent H Q) :
    Heap (queryFamilyMemoRaw source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse draw key) := by
  cases key with
  | inl scalar =>
    exact Heap.computeOf (queryFamilySourceWordWithWork target N P F exponent H Q draw scalar)
      (Nat.size (draw scalar).val + 2) (by simp only [queryFamilySourceWordWithWork]; omega)
  | inr request =>
    exact (queryChargedFamilyGlobalHeap source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse allocation hc request).mapKeysWithWork
        _ (fun _ => 1) (fun _ => le_rfl)

end Family
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryHeap
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
attribute [local instance] queryArityNeZero queryRoundsNeZero

/-- Coarse words are borrowed from the separately allocated initializer.
Every local buffer, guarded source read and final normalization is annotated. -/
def computedQueryMemoRawHeap (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) (key : ComputedFamilyMemoKey source target N) :
    BitQuery.Heap (computedQueryMemoRaw source target N occurrence symbolBits positionBits input key) :=
  queryFamilyMemoRawHeap source target N (integerParameters N).P (inputSmallLog N)
    (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
    (heightExponent N / 20) (smallLogExponent N) (computedParameterP_pos N) rfl rfl
    (fun pass => (scheduledSeedWordWithWork N pass).1)
    (fun pass => (computedQueryParameters N pass).factor)
    (computedQueryParameters N 0).tau (computedQueryParameters N 0).eta
    (computedQueryParameters N 0).kappa (computedQueryParameters N 0).delta
    (scheduledSeedMultiplier N) occurrence symbolBits positionBits
    (fun entry => (BinaryFraction.nat (clampedSeedNat input.1 entry), 0))
    (fun _ => 0) (fun _ => le_rfl) input.2 key

def computedQueryMemoHeap (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) (key : ComputedFamilyMemoKey source target N) :
    BitQuery.Heap (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input key) :=
  (computedQueryMemoRawHeap source target N occurrence symbolBits positionBits input key).normalize
    (computedQueryBase N) (computedQueryBase_pos N)
    (queryFamilyMemoRemaining target N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80) key)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryTemporarySpace
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter
attribute [local instance] queryArityNeZero queryRoundsNeZero

/-- Cumulative concrete local allocations, address workspace, suspended
reads, dictionary paths and evaluator frames, over the actual cache trace. -/
def computedQueryTemporaryCells (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) : ℕ :=
  rankedBitMemoCells (SourceRanked.rank ChargedPhysicalRequest.rank)
    (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input)
    (computedQueryMemoHeap source target N occurrence symbolBits positionBits input)
    (16384 * inputHeight N + 5) (computedFamilyMemoCode source target N (inputHeight N ^ 2))
    (fun key => (computedFamilyMemoCodeWithWork source target N (inputHeight N ^ 2) key).2)
    (.inr (localFinalRootRequest target N (integerParameters N).T (integerParameters N).S
      (inputHeight N) (Nat.two_pow_pos _) (finalTargetState target.length))) .empty

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Specification_ConcreteFootprints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete allocation traces preserve the cells in the certified Heap
construction while keeping its allocation-bound certificates separate. -/

namespace OAI.EditApproximation
open BitQuery
attribute [local instance] queryArityNeZero queryRoundsNeZero









def queryLocalRefinementFootprint.{u_1, u_2}
    {ι : Type u_1}
    {α : Type u_2}
    (source target : List α)
    {M : ℕ}
    (parent : TargetInterval source.length)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (tau a eta kappa delta : BinaryFraction)
    (t : ℕ)
    (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (R : ℕ)
    (hc : ∀ (i : Fin M) (r : TargetInterval target.length), (child i r).2 ≤ R)
    (hi : ∀ (i : Fin M) (r : TargetInterval target.length), (initial i r).2 ≤ R)
    (draw : CountedCellGroupDraws M F Q)
    (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
    (parentAllocation : TargetInterval target.length → ℕ)
    (childAllocation initialAllocation : Fin M → TargetInterval target.length → ℕ)
    (drawAllocation : CountedCellGroupAllocations M F Q)
    (integerAllocation : ℕ → TargetInterval target.length → ℕ)
    (q : TargetInterval target.length)
    (readEarlier : Fin M × ℕ × TargetInterval target.length →
  BitQuery ι BinaryFraction)
    (readCurrent : Fin M × TargetInterval target.length →
  BitQuery ι BinaryFraction)
    (he : (key : Fin M × ℕ × TargetInterval target.length) → (readEarlier key).Footprint)
    (hr : (key : Fin M × TargetInterval target.length) → (readCurrent key).Footprint) : (queryLocalRefinement source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa delta
    t parentInitial child initial R hc hi draw integer q readEarlier readCurrent).Footprint :=
(BitQuery.Footprint.computeOf
      (BinaryFraction.queryEarlierInputsWithWork M parent N P F exponent t hP a parentInitial q)
      (BinaryFraction.queryEarlierInputsAllocation M parent N P F exponent t hP a parentInitial
        parentAllocation q)).bind
  (fun (earlierKeys : List (Fin M × ℕ × TargetInterval target.length)) =>
    BitQuery.collect readEarlier earlierKeys
      fun (earlierWords : List BinaryFraction) =>
      (BitQuery.compute
            (BinaryFraction.queryOnlineSelectWithWork source target parent N P F exponent H hP tau
              a eta kappa parentInitial child initial R hc hi t integer earlierKeys earlierWords q)).bind
        fun
          (onlineActions :
            List
              (BinaryBellmanAction (TargetInterval target.length)
                (Fin M × TargetInterval target.length) M)) =>
        have word : BinaryFraction × ℕ := parentInitial q;
        BitQuery.charge word.2
          ((BitQuery.compute
                (BinaryFraction.querySharedInputsWithWork M N F Q exponent eM eF hM hF parent a
                  word.1 q draw)).bind
            fun (sharedKeys : List (Fin M × TargetInterval target.length)) =>
            BitQuery.collect readCurrent sharedKeys
              fun (sharedWords : List BinaryFraction) =>
              (BitQuery.compute
                    (BinaryFraction.queryGroupSelectWithWork source target parent N P F exponent Q
                      eM eF hP hM hF tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q)).bind
                fun
                  (selectedActions :
                    List
                      (BinaryBellmanAction (TargetInterval target.length)
                        (Fin M × TargetInterval target.length) M)) =>
                (BitQuery.compute
                      (queryNeededInputsWithWork selectedActions onlineActions)).bind
                  fun (currentKeys : List (Fin M × TargetInterval target.length)) =>
                  BitQuery.collect readCurrent currentKeys
                    fun (currentWords : List BinaryFraction) =>
                    BitQuery.compute
                      (BinaryFraction.queryRefinementFinishWithWork parent N P F a delta
                        parentInitial t earlierKeys earlierWords selectedActions onlineActions currentKeys currentWords
                        q)))
  fun (earlierKeys : List (Fin M × ℕ × TargetInterval target.length)) =>
  BitQuery.Footprint.collect readEarlier he earlierKeys
    (fun (earlierWords : List BinaryFraction) =>
      (BitQuery.compute
            (BinaryFraction.queryOnlineSelectWithWork source target parent N P F exponent H hP tau
              a eta kappa parentInitial child initial R hc hi t integer earlierKeys earlierWords q)).bind
        fun
          (onlineActions :
            List
              (BinaryBellmanAction (TargetInterval target.length)
                (Fin M × TargetInterval target.length) M)) =>
        have word : BinaryFraction × ℕ := parentInitial q;
        BitQuery.charge word.2
          ((BitQuery.compute
                (BinaryFraction.querySharedInputsWithWork M N F Q exponent eM eF hM hF parent a
                  word.1 q draw)).bind
            fun (sharedKeys : List (Fin M × TargetInterval target.length)) =>
            BitQuery.collect readCurrent sharedKeys
              fun (sharedWords : List BinaryFraction) =>
              (BitQuery.compute
                    (BinaryFraction.queryGroupSelectWithWork source target parent N P F exponent Q
                      eM eF hP hM hF tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q)).bind
                fun
                  (selectedActions :
                    List
                      (BinaryBellmanAction (TargetInterval target.length)
                        (Fin M × TargetInterval target.length) M)) =>
                (BitQuery.compute
                      (queryNeededInputsWithWork selectedActions onlineActions)).bind
                  fun (currentKeys : List (Fin M × TargetInterval target.length)) =>
                  BitQuery.collect readCurrent currentKeys
                    fun (currentWords : List BinaryFraction) =>
                    BitQuery.compute
                      (BinaryFraction.queryRefinementFinishWithWork parent N P F a delta
                        parentInitial t earlierKeys earlierWords selectedActions onlineActions currentKeys currentWords
                        q)))
    fun (earlierWords : List BinaryFraction) =>
    (BitQuery.Footprint.compute
          (BinaryFraction.queryOnlineSelectWithWork source target parent N P F exponent H hP tau a
            eta kappa parentInitial child initial R hc hi t integer earlierKeys earlierWords q)
          (BinaryFraction.queryOnlineSelectAllocation source target parent N P F exponent H hP tau
            a eta kappa parentInitial child initial R hc hi parentAllocation childAllocation initialAllocation t integer
            integerAllocation earlierKeys earlierWords q)).bind
      (fun
          (onlineActions :
            List
              (BinaryBellmanAction (TargetInterval target.length)
                (Fin M × TargetInterval target.length) M)) =>
        have word : BinaryFraction × ℕ := parentInitial q;
        BitQuery.charge word.2
          ((BitQuery.compute
                (BinaryFraction.querySharedInputsWithWork M N F Q exponent eM eF hM hF parent a
                  word.1 q draw)).bind
            fun (sharedKeys : List (Fin M × TargetInterval target.length)) =>
            BitQuery.collect readCurrent sharedKeys
              fun (sharedWords : List BinaryFraction) =>
              (BitQuery.compute
                    (BinaryFraction.queryGroupSelectWithWork source target parent N P F exponent Q
                      eM eF hP hM hF tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q)).bind
                fun
                  (selectedActions :
                    List
                      (BinaryBellmanAction (TargetInterval target.length)
                        (Fin M × TargetInterval target.length) M)) =>
                (BitQuery.compute
                      (queryNeededInputsWithWork selectedActions onlineActions)).bind
                  fun (currentKeys : List (Fin M × TargetInterval target.length)) =>
                  BitQuery.collect readCurrent currentKeys
                    fun (currentWords : List BinaryFraction) =>
                    BitQuery.compute
                      (BinaryFraction.queryRefinementFinishWithWork parent N P F a delta
                        parentInitial t earlierKeys earlierWords selectedActions onlineActions currentKeys currentWords
                        q)))
      fun
        (online :
          List
            (BinaryBellmanAction (TargetInterval target.length)
              (Fin M × TargetInterval target.length) M)) =>
      BitQuery.Footprint.chargeOf (parentAllocation q)
        ((BitQuery.Footprint.computeOf
              (BinaryFraction.querySharedInputsWithWork M N F Q exponent eM eF hM hF parent a
                (parentInitial q).1 q draw)
              (BinaryFraction.querySharedInputsAllocation M N F Q exponent eM eF hM hF parent a
                (parentInitial q).1 q draw drawAllocation)).bind
          (fun (sharedKeys : List (Fin M × TargetInterval target.length)) =>
            BitQuery.collect readCurrent sharedKeys
              fun (sharedWords : List BinaryFraction) =>
              (BitQuery.compute
                    (BinaryFraction.queryGroupSelectWithWork source target parent N P F exponent Q
                      eM eF hP hM hF tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q)).bind
                fun
                  (selectedActions :
                    List
                      (BinaryBellmanAction (TargetInterval target.length)
                        (Fin M × TargetInterval target.length) M)) =>
                (BitQuery.compute
                      (queryNeededInputsWithWork selectedActions online)).bind
                  fun (currentKeys : List (Fin M × TargetInterval target.length)) =>
                  BitQuery.collect readCurrent currentKeys
                    fun (currentWords : List BinaryFraction) =>
                    BitQuery.compute
                      (BinaryFraction.queryRefinementFinishWithWork parent N P F a delta
                        parentInitial t earlierKeys earlierWords selectedActions online currentKeys currentWords q))
          fun (sharedKeys : List (Fin M × TargetInterval target.length)) =>
          BitQuery.Footprint.collect readCurrent hr sharedKeys
            (fun (sharedWords : List BinaryFraction) =>
              (BitQuery.compute
                    (BinaryFraction.queryGroupSelectWithWork source target parent N P F exponent Q
                      eM eF hP hM hF tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q)).bind
                fun
                  (selectedActions :
                    List
                      (BinaryBellmanAction (TargetInterval target.length)
                        (Fin M × TargetInterval target.length) M)) =>
                (BitQuery.compute
                      (queryNeededInputsWithWork selectedActions online)).bind
                  fun (currentKeys : List (Fin M × TargetInterval target.length)) =>
                  BitQuery.collect readCurrent currentKeys
                    fun (currentWords : List BinaryFraction) =>
                    BitQuery.compute
                      (BinaryFraction.queryRefinementFinishWithWork parent N P F a delta
                        parentInitial t earlierKeys earlierWords selectedActions online currentKeys currentWords q))
            fun (sharedWords : List BinaryFraction) =>
            (BitQuery.Footprint.computeOf
                  (BinaryFraction.queryGroupSelectWithWork source target parent N P F exponent Q
                    eM eF hP hM hF tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q)
                  (BinaryFraction.queryGroupSelectAllocation source target parent N P F exponent Q
                    eM eF hP hM hF tau a parentInitial child initial R hc hi parentAllocation childAllocation
                    initialAllocation draw drawAllocation sharedKeys sharedWords q)).bind
              (fun
                  (selectedActions :
                    List
                      (BinaryBellmanAction (TargetInterval target.length)
                        (Fin M × TargetInterval target.length) M)) =>
                (BitQuery.compute
                      (queryNeededInputsWithWork selectedActions online)).bind
                  fun (currentKeys : List (Fin M × TargetInterval target.length)) =>
                  BitQuery.collect readCurrent currentKeys
                    fun (currentWords : List BinaryFraction) =>
                    BitQuery.compute
                      (BinaryFraction.queryRefinementFinishWithWork parent N P F a delta
                        parentInitial t earlierKeys earlierWords selectedActions online currentKeys currentWords q))
              fun
                (groups :
                  List
                    (BinaryBellmanAction (TargetInterval target.length)
                      (Fin M × TargetInterval target.length) M)) =>
              (BitQuery.Footprint.computeOf
                    (queryNeededInputsWithWork groups online)
                    (queryNeededInputsAllocation groups online)).bind
                (fun (currentKeys : List (Fin M × TargetInterval target.length)) =>
                  BitQuery.collect readCurrent currentKeys
                    fun (currentWords : List BinaryFraction) =>
                    BitQuery.compute
                      (BinaryFraction.queryRefinementFinishWithWork parent N P F a delta
                        parentInitial t earlierKeys earlierWords groups online currentKeys currentWords q))
                fun (currentKeys : List (Fin M × TargetInterval target.length)) =>
                BitQuery.Footprint.collect readCurrent hr currentKeys
                  (fun (currentWords : List BinaryFraction) =>
                    BitQuery.compute
                      (BinaryFraction.queryRefinementFinishWithWork parent N P F a delta
                        parentInitial t earlierKeys earlierWords groups online currentKeys currentWords q))
                  fun (currentWords : List BinaryFraction) =>
                  BitQuery.Footprint.computeOf
                    (BinaryFraction.queryRefinementFinishWithWork parent N P F a delta
                      parentInitial t earlierKeys earlierWords groups online currentKeys currentWords q)
                    (BinaryFraction.queryRefinementFinishAllocation parent N P F a delta
                      parentInitial parentAllocation t earlierKeys earlierWords groups online currentKeys currentWords
                      q))

def queryLocalRandomSourcesFootprint.{u_1, u_2}
    {ι : Type u_1}
    {α : Type u_2}
    (source target : List α)
    {M : ℕ}
    [NeZero M]
    (parent : TargetInterval source.length)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (tau a eta kappa delta : BinaryFraction)
    (t : ℕ)
    (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (R : ℕ)
    (hc : ∀ (i : Fin M) (r : TargetInterval target.length), (child i r).2 ≤ R)
    (hi : ∀ (i : Fin M) (r : TargetInterval target.length), (initial i r).2 ≤ R)
    (parentAllocation : TargetInterval target.length → ℕ)
    (childAllocation initialAllocation : Fin M → TargetInterval target.length → ℕ)
    (q : TargetInterval target.length)
    (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
    (readInteger : ℕ × TargetInterval target.length →
  ℕ → BitQuery ι BinaryFraction)
    (readEarlier : Fin M × ℕ × TargetInterval target.length →
  BitQuery ι BinaryFraction)
    (readCurrent : Fin M × TargetInterval target.length →
  BitQuery ι BinaryFraction)
    (hg : (key : GroupScalarKey M F Q) → (readGroup key).Footprint)
    (hz : (key : ℕ × TargetInterval target.length) → (range : ℕ) → (readInteger key range).Footprint)
    (he : (key : Fin M × ℕ × TargetInterval target.length) → (readEarlier key).Footprint)
    (hr : (key : Fin M × TargetInterval target.length) → (readCurrent key).Footprint) : (queryLocalRandomSources source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa
    delta t parentInitial child initial R hc hi q readGroup readInteger readEarlier readCurrent).Footprint :=
queryGroupSourceGatherFootprint M N F Q exponent eM eF hM hF a parentInitial parentAllocation q
  readGroup hg
  (fun (groupKeys : List (GroupScalarKey M F Q))
      (groupWords : List BinaryFraction) =>
    queryOnlineSourceGather parent N P F exponent H hP tau a parentInitial child q readInteger
      fun (onlineKeys : List (ℕ × TargetInterval target.length))
        (onlineWords : List BinaryFraction) =>
      queryLocalRefinement source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa
        delta t parentInitial child initial R hc hi
        (BinaryFraction.queryGroupDrawReadWithWork groupKeys groupWords)
        (BinaryFraction.queryOnlineIntegerReadWithWork onlineKeys onlineWords) q readEarlier
        readCurrent)
  fun (groupKeys : List (GroupScalarKey M F Q))
    (groupWords : List BinaryFraction) =>
  queryOnlineSourceGatherFootprint parent N P F exponent H hP tau a parentInitial parentAllocation
    child childAllocation q readInteger hz
    (fun (onlineKeys : List (ℕ × TargetInterval target.length))
        (onlineWords : List BinaryFraction) =>
      queryLocalRefinement source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa
        delta t parentInitial child initial R hc hi
        (BinaryFraction.queryGroupDrawReadWithWork groupKeys groupWords)
        (BinaryFraction.queryOnlineIntegerReadWithWork onlineKeys onlineWords) q readEarlier
        readCurrent)
    fun (onlineKeys : List (ℕ × TargetInterval target.length))
      (onlineWords : List BinaryFraction) =>
    queryLocalRefinementFootprint source target parent N P F exponent H Q eM eF hP hM hF tau a eta
      kappa delta t parentInitial child initial R hc hi
      (BinaryFraction.queryGroupDrawReadWithWork groupKeys groupWords)
      (BinaryFraction.queryOnlineIntegerReadWithWork onlineKeys onlineWords) parentAllocation
      childAllocation initialAllocation
      (BinaryFraction.queryGroupDrawReadAllocation groupKeys groupWords)
      (BinaryFraction.queryOnlineIntegerReadAllocation onlineKeys onlineWords) q readEarlier
      readCurrent he hr

def queryLocalBandFootprint.{u_1, u_2}
    {ι : Type u_1}
    {α : Type u_2}
    (source target : List α)
    {M : ℕ}
    [NeZero M]
    (parent : TargetInterval source.length)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (tau a eta kappa delta : BinaryFraction)
    (t : ℕ)
    (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
    (parentAllocation : TargetInterval target.length → ℕ)
    (readMass readInitial : Fin M × TargetInterval target.length →
  BitQuery ι BinaryFraction)
    (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
    (readInteger : ℕ × TargetInterval target.length →
  ℕ → BitQuery ι BinaryFraction)
    (q : TargetInterval target.length)
    (readEarlier : Fin M × ℕ × TargetInterval target.length →
  BitQuery ι BinaryFraction)
    (readCurrent : Fin M × TargetInterval target.length →
  BitQuery ι BinaryFraction)
    (hm : (key : Fin M × TargetInterval target.length) → (readMass key).Footprint)
    (hi : (key : Fin M × TargetInterval target.length) → (readInitial key).Footprint)
    (hg : (key : GroupScalarKey M F Q) → (readGroup key).Footprint)
    (hz : (key : ℕ × TargetInterval target.length) → (range : ℕ) → (readInteger key range).Footprint)
    (he : (key : Fin M × ℕ × TargetInterval target.length) → (readEarlier key).Footprint)
    (hr : (key : Fin M × TargetInterval target.length) → (readCurrent key).Footprint) : (queryLocalBand source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa delta t
    parentInitial readMass readInitial readGroup readInteger q readEarlier readCurrent).Footprint :=
queryBandGatherFootprint M parent N P F exponent hP a parentInitial parentAllocation q readMass
  readInitial hm hi
  (fun (keys : List (Fin M × TargetInterval target.length))
      (massWords initialWords : List BinaryFraction) =>
    queryLocalRandomSources source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa
      delta t parentInitial (BinaryFraction.queryChildReadWithWork keys massWords)
      (BinaryFraction.queryChildReadWithWork keys initialWords)
      (BinaryFraction.queryDataReadBudget M target.length keys) (BinaryFraction.queryChildReadWithWork_budget keys massWords) (BinaryFraction.queryChildReadWithWork_budget keys initialWords) q readGroup
      readInteger readEarlier readCurrent)
  fun (keys : List (Fin M × TargetInterval target.length))
    (massWords initialWords : List BinaryFraction) =>
  queryLocalRandomSourcesFootprint source target parent N P F exponent H Q eM eF hP hM hF tau a
    eta kappa delta t parentInitial (BinaryFraction.queryChildReadWithWork keys massWords)
    (BinaryFraction.queryChildReadWithWork keys initialWords)
    (BinaryFraction.queryDataReadBudget M target.length keys) (BinaryFraction.queryChildReadWithWork_budget keys massWords) (BinaryFraction.queryChildReadWithWork_budget keys initialWords)
    parentAllocation (BinaryFraction.queryChildReadAllocation keys massWords)
    (BinaryFraction.queryChildReadAllocation keys initialWords) q readGroup readInteger
    readEarlier readCurrent hg hz he hr

def queryLocalProgramFootprint.{u_1, u_2}
    {ι : Type u_1}
    {α : Type u_2}
    (source target : List α)
    {M : ℕ}
    [NeZero M]
    (parent : TargetInterval source.length)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (tau a eta kappa delta : BinaryFraction)
    (t : ℕ)
    (readParent : TargetInterval target.length →
  BitQuery ι BinaryFraction)
    (readMass readInitial : Fin M × TargetInterval target.length →
  BitQuery ι BinaryFraction)
    (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
    (readInteger : ℕ × TargetInterval target.length →
  ℕ → BitQuery ι BinaryFraction)
    (q : TargetInterval target.length)
    (readEarlier : Fin M × ℕ × TargetInterval target.length →
  BitQuery ι BinaryFraction)
    (readCurrent : Fin M × TargetInterval target.length →
  BitQuery ι BinaryFraction)
    (hp : (key : TargetInterval target.length) → (readParent key).Footprint)
    (hm : (key : Fin M × TargetInterval target.length) → (readMass key).Footprint)
    (hi : (key : Fin M × TargetInterval target.length) → (readInitial key).Footprint)
    (hg : (key : GroupScalarKey M F Q) → (readGroup key).Footprint)
    (hz : (key : ℕ × TargetInterval target.length) → (range : ℕ) → (readInteger key range).Footprint)
    (he : (key : Fin M × ℕ × TargetInterval target.length) → (readEarlier key).Footprint)
    (hr : (key : Fin M × TargetInterval target.length) → (readCurrent key).Footprint) : (queryLocalProgram source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa delta t
    readParent readMass readInitial readGroup readInteger q readEarlier readCurrent).Footprint :=
queryInitialGatherFootprint N P F exponent hP a q readParent hp
  (fun (keys : List (TargetInterval target.length))
      (words : List BinaryFraction) =>
    queryLocalBand source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa delta t
      (BinaryFraction.queryParentReadWithWork keys words) readMass readInitial readGroup
      readInteger q readEarlier readCurrent)
  fun (keys : List (TargetInterval target.length))
    (words : List BinaryFraction) =>
  queryLocalBandFootprint source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa
    delta t (BinaryFraction.queryParentReadWithWork keys words)
    (BinaryFraction.queryParentReadAllocation keys words) readMass readInitial readGroup
    readInteger q readEarlier readCurrent hm hi hg hz he hr








def queryPhysicalRandomDataRequestFootprint.{u_1, u_2}
    {σ : Type u_1}
    {α : Type u_2}
    (source target : List α)
    {M J : ℕ}
    [NeZero M]
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (tau a eta kappa delta : BinaryFraction)
    (copies pass copy T S t : ℕ)
    (ht : 0 < t)
    (node : PhysicalNode M J)
    (hbelow : ↑node.fst < J)
    (readGroup : GroupScalarKey M F Q → BitQuery σ BinaryFraction)
    (readInteger : ℕ × TargetInterval target.length →
  ℕ → BitQuery σ BinaryFraction)
    (q : TargetInterval target.length)
    (hg : (key : GroupScalarKey M F Q) → (readGroup key).Footprint)
    (hz : (key : ℕ × TargetInterval target.length) → (range : ℕ) → (readInteger key range).Footprint) : (queryPhysicalRandomDataRequest source target N P F exponent H Q eM eF hP hM hF tau a eta kappa
    delta copies pass copy T S t ht node hbelow readGroup readInteger q).Footprint := by
  unfold queryPhysicalRandomDataRequest
  apply queryLocalProgramFootprint
  · intro r
    exact (queryPhysicalTableReadFootprint copies T S _ _).mapKeysWithWork _ (fun _ => 1)
  · intro input
    apply Footprint.mapKeysWithWork _ (fun _ => 1)
    apply queryMeanReadFootprint
    intro j
    exact queryPhysicalTableReadFootprint copies T S _ _
  · intro input
    exact (queryPhysicalTableReadFootprint copies T S _ _).mapKeysWithWork _ (fun _ => 1)
  · intro key
    exact (hg key).mapKeysWithWork _ (fun _ => 1)
  · intro key range
    exact (hz key range).mapKeysWithWork _ (fun _ => 1)
  · intro input
    exact (queryPhysicalEarlierReadFootprint copies pass copy T S t node hbelow q input).mapKeysWithWork _
      (fun _ => 1)
  · intro input
    exact (queryPhysicalTableReadFootprint copies T S _ _).mapKeysWithWork _ (fun _ => 1)
















def queryFamilyRefinementFootprint.{u_1}
    {α : Type u_1}
    {M J R : ℕ}
    [NeZero M]
    (source target : List α)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (tau a eta kappa delta : BinaryFraction)
    (passes copies pass copy T S t : ℕ)
    (ht : 0 < t)
    (node : PhysicalNode M J)
    (hbelow : ↑node.fst < J)
    (time : Fin R)
    (q : TargetInterval target.length) : (queryFamilyRefinement source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta
    passes copies pass copy T S t ht node hbelow time q).Footprint :=
queryPhysicalRandomDataRequestFootprint source target N P F exponent H Q eM eF hP hM hF tau a eta
  kappa delta copies pass copy T S t ht node hbelow
  (queryFamilyGroupRead target N P F exponent H Q passes copies pass copy ⟨node, hbelow⟩ time)
  (queryFamilyOnlineRead target N P F exponent H Q passes copies pass copy ⟨node, hbelow⟩ time) q
  (queryFamilyGroupReadFootprint target N P F exponent H Q passes copies pass copy ⟨node, hbelow⟩
    time)
  (queryFamilyOnlineReadFootprint target N P F exponent H Q passes copies pass copy ⟨node, hbelow⟩
    time)

def queryFamilyActiveFootprint.{u_1}
    {α : Type u_1}
    {M J R : ℕ}
    [NeZero M]
    [NeZero R]
    (source target : List α)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (tau a eta kappa delta : BinaryFraction)
    (T S passes copies : ℕ)
    (request : PhysicalTableRequest M J target.length)
    (hindex : T < request.index)
    (hbelow : ↑request.node.fst < J) : (queryFamilyActive (R := R) source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta T S
    passes copies request hindex hbelow).Footprint :=
  (queryFamilyRefinementFootprint source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta
    passes copies request.pass request.copy T S (request.index - T) (Nat.sub_pos_of_lt hindex)
    request.node hbelow (Fin.ofNat R (request.index - T - 1)) request.state).mapKeysWithWork _ (fun _ => 1)

def queryFamilyBoundedActiveFootprint.{u_1}
    {α : Type u_1}
    {M J R : ℕ}
    [NeZero M]
    [NeZero R]
    (source target : List α)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (tau a eta kappa delta : BinaryFraction)
    (T S passes copies : ℕ)
    (parent : { r : PhysicalTableRequest M J target.length //
  PhysicalTableRequest.Bounded (passes + 1) copies T S r })
    (hindex : T < parent.val.index)
    (hbelow : ↑parent.val.node.fst < J) : (queryFamilyBoundedActive (R := R) source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta T
    S passes copies parent hindex hbelow).Footprint :=
  queryRestrictPhysicalBodyFootprint (passes + 1) copies T S parent _
    (queryFamilyActiveFootprint (R := R) source target N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta T S passes copies parent.val hindex hbelow)
















def queryChargedFamilyTableFootprint
    {M J R passes copies T S : ℕ}
    [NeZero M]
    [NeZero R]
    (source target : List ℕ)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (A a : ℕ → BinaryFraction)
    (tau eta kappa delta : BinaryFraction)
    (multiplier : ℕ → ℕ)
    (occurrence : BinaryMemo PositionCounts)
    (symbolBits positionBits : ℕ)
    (parent : { r : PhysicalTableRequest M J target.length //
  PhysicalTableRequest.Bounded (passes + 1) copies T S r }) : (queryChargedFamilyTable (R := R) source target N P F exponent H Q eM eF hP hM hF A a tau eta kappa delta
    multiplier occurrence symbolBits positionBits parent).Footprint := by
  have hinit := queryPhysicalInitialFootprint source target N P F (A parent.val.pass) (a parent.val.pass)
    multiplier parent occurrence symbolBits positionBits parent.val.state
  unfold queryChargedFamilyTable
  refine BitQuery.Footprint.chargeOf (naturalWordLEAllocation parent.val.index.bits T.bits) ?_
  split
  · exact (queryChargedWarmupFootprint source target N P F (A parent.val.pass) (a parent.val.pass)
      multiplier parent occurrence symbolBits positionBits).mapKeysWithWork _ (fun _ => 1)
  · refine BitQuery.Footprint.chargeOf (parent.val.node.1.val.bits.length + J.bits.length) ?_
    split
    · let interval := physicalSourceInterval source.length parent.val.node
      refine BitQuery.Footprint.chargeOf (saturatingSubtractAllocation interval.hi interval.lo +
        naturalWordLEAllocation (saturatingSubtractWithWork interval.hi interval.lo).1 [true]) ?_
      split
      · exact hinit.mapKeysWithWork _ (fun _ => 1)
      · exact (queryFamilyBoundedActiveFootprint (R := R) source target N P F exponent H Q eM eF hP hM hF
          tau (a parent.val.pass) eta kappa delta T S passes copies parent _ _).mapKeysWithWork _
          (fun _ => 1)
    · exact hinit.mapKeysWithWork _ (fun _ => 1)


def queryChargedFamilyGlobalFootprint
    {M J R passes copies T S : ℕ}
    [NeZero M]
    [NeZero R]
    (source target : List ℕ)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (A a : ℕ → BinaryFraction)
    (tau eta kappa delta : BinaryFraction)
    (multiplier : ℕ → ℕ)
    (occurrence : BinaryMemo PositionCounts)
    (symbolBits positionBits : ℕ)
    (coarse : PhysicalEntry M J target.length → BinaryFraction × ℕ)
    (allocation : PhysicalEntry M J target.length → ℕ)
    (request : ChargedPhysicalRequest M J target.length (passes + 1) copies T S) : (queryChargedFamilyGlobal (R := R) source target N P F exponent H Q eM eF hP hM hF A a tau eta kappa delta
    multiplier occurrence symbolBits positionBits coarse request).Footprint := by
  cases request with
  | inl entry => exact Footprint.compute (coarse entry) (allocation entry)
  | inr parent =>
    exact queryChargedFamilyTableFootprint (R := R) source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits parent

def queryFamilyMemoRawFootprint
    {M J R passes copies T S : ℕ}
    [NeZero M]
    [NeZero R]
    (source target : List ℕ)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (A a : ℕ → BinaryFraction)
    (tau eta kappa delta : BinaryFraction)
    (multiplier : ℕ → ℕ)
    (occurrence : BinaryMemo PositionCounts)
    (symbolBits positionBits : ℕ)
    (coarse : PhysicalEntry M J target.length → BinaryFraction × ℕ)
    (allocation : PhysicalEntry M J target.length → ℕ)
    (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R) target N P F exponent H Q passes copies)
    (key : QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q) : (queryFamilyMemoRaw (R := R) source target N P F exponent H Q eM eF hP hM hF A a tau eta kappa delta
    multiplier occurrence symbolBits positionBits coarse draw key).Footprint := by
  cases key with
  | inl scalar =>
    exact Footprint.computeOf (queryFamilySourceWordWithWork target N P F exponent H Q draw scalar)
      (Nat.size (draw scalar).val + 2)
  | inr request =>
    exact (queryChargedFamilyGlobalFootprint source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse allocation request).mapKeysWithWork
        _ (fun _ => 1)

def computedQueryMemoRawFootprint
    (source target : List ℕ)
    (N : ℕ)
    (occurrence : BinaryMemo PositionCounts)
    (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N)
    (key : ComputedFamilyMemoKey source target N) : (computedQueryMemoRaw source target N occurrence symbolBits positionBits input key).Footprint :=
  queryFamilyMemoRawFootprint source target N (integerParameters N).P (inputSmallLog N)
    (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
    (heightExponent N / 20) (smallLogExponent N) (computedParameterP_pos N) rfl rfl
    (fun pass => (scheduledSeedWordWithWork N pass).1)
    (fun pass => (computedQueryParameters N pass).factor)
    (computedQueryParameters N 0).tau (computedQueryParameters N 0).eta
    (computedQueryParameters N 0).kappa (computedQueryParameters N 0).delta
    (scheduledSeedMultiplier N) occurrence symbolBits positionBits
    (fun entry => (BinaryFraction.nat (clampedSeedNat input.1 entry), 0))
    (fun _ => 0) input.2 key

def computedQueryMemoFootprint
    (source target : List ℕ)
    (N : ℕ)
    (occurrence : BinaryMemo PositionCounts)
    (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N)
    (key : ComputedFamilyMemoKey source target N) : (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input
    key).Footprint :=
(computedQueryMemoRawFootprint source target N occurrence symbolBits positionBits input
      key).normalize
  (computedQueryBase N) (computedQueryBase_pos N)
  (queryFamilyMemoRemaining target N (integerParameters N).P
    (inputSmallLog N) (40 * smallLogExponent N)
    (inputHeight N) (inputSmallLog N ^ 80) key)

end OAI.EditApproximation
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Specification_ConcreteFootprintBridges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.EditApproximation

universe u_1 u_2

-- Supply case arguments directly so inference does not normalize indexed branch values.
universe u

set_option maxHeartbeats 2000000

@[simp] theorem queryInitialGatherHeap_footprint :
    ∀ {ι : Type u_1} {β : Type u_2} {n : Nat} (N P F exponent : Nat)
  (hP : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P)
  (a : OAI.EditApproximation.BinaryFraction) (q : OAI.EditApproximation.TargetInterval n)
  (reader :
    OAI.EditApproximation.TargetInterval n →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (hr :
    (key : OAI.EditApproximation.TargetInterval n) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (reader key))
  (next :
    List.{0} (OAI.EditApproximation.TargetInterval n) →
      List.{0} OAI.EditApproximation.BinaryFraction → OAI.EditApproximation.BitQuery.{u_1, u_2} ι β)
  (hn :
    (keys : List.{0} (OAI.EditApproximation.TargetInterval n)) →
      (words : List.{0} OAI.EditApproximation.BinaryFraction) →
        @OAI.EditApproximation.BitQuery.Heap.{u_1, u_2} ι β (next keys words)),
  @Eq.{(max u_1 u_2) + 1}
    (@OAI.EditApproximation.BitQuery.Footprint.{u_1, u_2} ι β
      (@OAI.EditApproximation.queryInitialGather.{u_1, u_2} ι β n N P F exponent hP a q reader next))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, u_2} ι β
      (@OAI.EditApproximation.queryInitialGather.{u_1, u_2} ι β n N P F exponent hP a q reader next)
      (@OAI.EditApproximation.queryInitialGatherHeap.{u_1, u_2} ι β n N P F exponent hP a q reader hr next hn))
    (@OAI.EditApproximation.queryInitialGatherFootprint.{u_1, u_2} ι β n N P F exponent hP a q reader
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (reader key)
          (hr key))
      next fun keys words =>
      @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, u_2} ι β (next keys words) (hn keys words)) := by
  intros
  simp [queryInitialGatherHeap, queryInitialGatherFootprint, queryInitialGather]

@[simp] theorem queryBandGatherHeap_footprint :
    ∀ {ι : Type u_1} {β : Type u_2} {nx ny : Nat} (M : Nat) (parent : OAI.EditApproximation.TargetInterval nx)
  (N P F exponent : Nat) (hP : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P)
  (a : OAI.EditApproximation.BinaryFraction)
  (initial : OAI.EditApproximation.TargetInterval ny → Prod.{0, 0} OAI.EditApproximation.BinaryFraction Nat)
  (allocation : OAI.EditApproximation.TargetInterval ny → Nat)
  (ha :
    ∀ (r : OAI.EditApproximation.TargetInterval ny),
      @LE.le.{0} Nat instLENat (allocation r) (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (initial r)))
  (q : OAI.EditApproximation.TargetInterval ny)
  (massReader initialReader :
    Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval ny) →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (hm :
    (key : Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval ny)) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (massReader key))
  (hi :
    (key : Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval ny)) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (initialReader key))
  (next :
    List.{0} (Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval ny)) →
      List.{0} OAI.EditApproximation.BinaryFraction →
        List.{0} OAI.EditApproximation.BinaryFraction → OAI.EditApproximation.BitQuery.{u_1, u_2} ι β)
  (hn :
    (keys : List.{0} (Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval ny))) →
      (mass words : List.{0} OAI.EditApproximation.BinaryFraction) →
        @OAI.EditApproximation.BitQuery.Heap.{u_1, u_2} ι β (next keys mass words)),
  @Eq.{(max u_1 u_2) + 1}
    (@OAI.EditApproximation.BitQuery.Footprint.{u_1, u_2} ι β
      (@OAI.EditApproximation.queryBandGather.{u_1, u_2} ι β nx ny M parent N P F exponent hP a initial q massReader
        initialReader next))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, u_2} ι β
      (@OAI.EditApproximation.queryBandGather.{u_1, u_2} ι β nx ny M parent N P F exponent hP a initial q massReader
        initialReader next)
      (@OAI.EditApproximation.queryBandGatherHeap.{u_1, u_2} ι β nx ny M parent N P F exponent hP a initial allocation
        ha q massReader initialReader hm hi next hn))
    (@OAI.EditApproximation.queryBandGatherFootprint.{u_1, u_2} ι β nx ny M parent N P F exponent hP a initial
      allocation q massReader initialReader
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (massReader key)
          (hm key))
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
          (initialReader key) (hi key))
      next fun keys mass words =>
      @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, u_2} ι β (next keys mass words) (hn keys mass words)) := by
  intros
  simp [queryBandGatherHeap, queryBandGatherFootprint, queryBandGather]

@[simp] theorem queryGroupSourceGatherHeap_footprint :
    ∀ {ι : Type u_1} {β : Type u_2} {n : Nat} (M N F Q exponent eM eF : Nat)
  (hM :
    @Eq.{1} Nat M
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eM))
  (hF :
    @Eq.{1} Nat F
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eF))
  (a : OAI.EditApproximation.BinaryFraction)
  (initial : OAI.EditApproximation.TargetInterval n → Prod.{0, 0} OAI.EditApproximation.BinaryFraction Nat)
  (allocation : OAI.EditApproximation.TargetInterval n → Nat)
  (ha :
    ∀ (r : OAI.EditApproximation.TargetInterval n),
      @LE.le.{0} Nat instLENat (allocation r) (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (initial r)))
  (q : OAI.EditApproximation.TargetInterval n)
  (reader :
    OAI.EditApproximation.GroupScalarKey M F Q →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (hr :
    (key : OAI.EditApproximation.GroupScalarKey M F Q) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (reader key))
  (next :
    List.{0} (OAI.EditApproximation.GroupScalarKey M F Q) →
      List.{0} OAI.EditApproximation.BinaryFraction → OAI.EditApproximation.BitQuery.{u_1, u_2} ι β)
  (hn :
    (keys : List.{0} (OAI.EditApproximation.GroupScalarKey M F Q)) →
      (words : List.{0} OAI.EditApproximation.BinaryFraction) →
        @OAI.EditApproximation.BitQuery.Heap.{u_1, u_2} ι β (next keys words)),
  @Eq.{(max u_1 u_2) + 1}
    (@OAI.EditApproximation.BitQuery.Footprint.{u_1, u_2} ι β
      (@OAI.EditApproximation.queryGroupSourceGather.{u_1, u_2} ι β n M N F Q exponent eM eF hM hF a initial q reader
        next))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, u_2} ι β
      (@OAI.EditApproximation.queryGroupSourceGather.{u_1, u_2} ι β n M N F Q exponent eM eF hM hF a initial q reader
        next)
      (@OAI.EditApproximation.queryGroupSourceGatherHeap.{u_1, u_2} ι β n M N F Q exponent eM eF hM hF a initial
        allocation ha q reader hr next hn))
    (@OAI.EditApproximation.queryGroupSourceGatherFootprint.{u_1, u_2} ι β n M N F Q exponent eM eF hM hF a initial
      allocation q reader
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (reader key)
          (hr key))
      next fun keys words =>
      @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, u_2} ι β (next keys words) (hn keys words)) := by
  intros
  simp [queryGroupSourceGatherHeap, queryGroupSourceGatherFootprint, queryGroupSourceGather]

@[simp] theorem queryOnlineSourceGatherHeap_footprint :
    ∀ {ι : Type u_1} {β : Type u_2} {nx ny M : Nat} (parent : OAI.EditApproximation.TargetInterval nx)
  (N P F exponent H : Nat)
  (hP : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P)
  (tau a : OAI.EditApproximation.BinaryFraction)
  (initial : OAI.EditApproximation.TargetInterval ny → Prod.{0, 0} OAI.EditApproximation.BinaryFraction Nat)
  (initialAllocation : OAI.EditApproximation.TargetInterval ny → Nat)
  (child : Fin M → OAI.EditApproximation.TargetInterval ny → Prod.{0, 0} OAI.EditApproximation.BinaryFraction Nat)
  (childAllocation : Fin M → OAI.EditApproximation.TargetInterval ny → Nat)
  (hi :
    ∀ (r : OAI.EditApproximation.TargetInterval ny),
      @LE.le.{0} Nat instLENat (initialAllocation r)
        (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (initial r)))
  (hc :
    ∀ (i : Fin M) (r : OAI.EditApproximation.TargetInterval ny),
      @LE.le.{0} Nat instLENat (childAllocation i r)
        (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (child i r)))
  (q : OAI.EditApproximation.TargetInterval ny)
  (reader :
    Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval ny) →
      Nat → OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (hr :
    (key : Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval ny)) →
      (range : Nat) →
        @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (reader key range))
  (next :
    List.{0} (Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval ny)) →
      List.{0} OAI.EditApproximation.BinaryFraction → OAI.EditApproximation.BitQuery.{u_1, u_2} ι β)
  (hn :
    (keys : List.{0} (Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval ny))) →
      (words : List.{0} OAI.EditApproximation.BinaryFraction) →
        @OAI.EditApproximation.BitQuery.Heap.{u_1, u_2} ι β (next keys words)),
  @Eq.{(max u_1 u_2) + 1}
    (@OAI.EditApproximation.BitQuery.Footprint.{u_1, u_2} ι β
      (@OAI.EditApproximation.queryOnlineSourceGather.{u_1, u_2} ι β nx ny M parent N P F exponent H hP tau a initial
        child q reader next))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, u_2} ι β
      (@OAI.EditApproximation.queryOnlineSourceGather.{u_1, u_2} ι β nx ny M parent N P F exponent H hP tau a initial
        child q reader next)
      (@OAI.EditApproximation.queryOnlineSourceGatherHeap.{u_1, u_2} ι β nx ny M parent N P F exponent H hP tau a
        initial initialAllocation child childAllocation hi hc q reader hr next hn))
    (@OAI.EditApproximation.queryOnlineSourceGatherFootprint.{u_1, u_2} ι β nx ny M parent N P F exponent H hP tau a
      initial initialAllocation child childAllocation q reader
      (fun key range =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
          (reader key range) (hr key range))
      next fun keys words =>
      @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, u_2} ι β (next keys words) (hn keys words)) := by
  intros
  simp [queryOnlineSourceGatherHeap, queryOnlineSourceGatherFootprint, queryOnlineSourceGather]

@[simp] theorem queryLocalRefinementHeap_footprint :
    ∀ {ι : Type u_1} {α : Type u_2} (source target : List.{u_2} α) {M : Nat}
  (parent : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α source)) (N P F exponent H Q eM eF : Nat)
  (hP : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P)
  (hM :
    @Eq.{1} Nat M
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eM))
  (hF :
    @Eq.{1} Nat F
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eF))
  (tau a eta kappa delta : OAI.EditApproximation.BinaryFraction) (t : Nat)
  (parentInitial :
    OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target) →
      Prod.{0, 0} OAI.EditApproximation.BinaryFraction Nat)
  (child initial :
    Fin M →
      OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target) →
        Prod.{0, 0} OAI.EditApproximation.BinaryFraction Nat)
  (R : Nat)
  (hc :
    ∀ (i : Fin M) (r : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)),
      @LE.le.{0} Nat instLENat (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (child i r)) R)
  (hi :
    ∀ (i : Fin M) (r : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)),
      @LE.le.{0} Nat instLENat (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (initial i r)) R)
  (draw : OAI.EditApproximation.CountedCellGroupDraws M F Q)
  (integer : Nat → OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target) → Prod.{0, 0} Nat Nat)
  (parentAllocation : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target) → Nat)
  (childAllocation initialAllocation : Fin M → OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target) → Nat)
  (drawAllocation : OAI.EditApproximation.CountedCellGroupAllocations M F Q)
  (integerAllocation : Nat → OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target) → Nat)
  (hp :
    ∀ (r : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)),
      @LE.le.{0} Nat instLENat (parentAllocation r)
        (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (parentInitial r)))
  (hca :
    ∀ (i : Fin M) (r : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)),
      @LE.le.{0} Nat instLENat (childAllocation i r)
        (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (child i r)))
  (hia :
    ∀ (i : Fin M) (r : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)),
      @LE.le.{0} Nat instLENat (initialAllocation i r)
        (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (initial i r)))
  (hd :
    ∀ (b : Nat) (cell : Prod.{0, 0} Nat Nat)
      (s :
        Fin (@List.length.{0} Rat (OAI.EditApproximation.groupDyadicScales M b (@Nat.cast.{0} Rat Rat.instNatCast F))))
      (j :
        Fin
          (OAI.EditApproximation.groupSampleCount M Q b
            (OAI.EditApproximation.groupDyadicScaleAt M b (@Nat.cast.{0} Rat Rat.instNatCast F) s))),
      @LE.le.{0} Nat instLENat (drawAllocation b cell s j) (@Prod.snd.{0, 0} (Fin M) Nat (draw b cell s j)))
  (hz :
    ∀ (b : Nat) (r : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)),
      @LE.le.{0} Nat instLENat (integerAllocation b r) (@Prod.snd.{0, 0} Nat Nat (integer b r)))
  (q : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))
  (readEarlier :
    Prod.{0, 0} (Fin M) (Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (readCurrent :
    Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)) →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (he :
    (key : Prod.{0, 0} (Fin M) (Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)))) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readEarlier key))
  (hr :
    (key : Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readCurrent key)),
  @Eq.{u_1 + 1}
    (@OAI.EditApproximation.BitQuery.Footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryLocalRefinement.{u_1, u_2} ι α source target M parent N P F exponent H Q eM eF hP hM
        hF tau a eta kappa delta t parentInitial child initial R hc hi draw integer q readEarlier readCurrent))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryLocalRefinement.{u_1, u_2} ι α source target M parent N P F exponent H Q eM eF hP hM
        hF tau a eta kappa delta t parentInitial child initial R hc hi draw integer q readEarlier readCurrent)
      (@OAI.EditApproximation.queryLocalRefinementHeap.{u_1, u_2} ι α source target M parent N P F exponent H Q eM eF hP
        hM hF tau a eta kappa delta t parentInitial child initial R hc hi draw integer parentAllocation childAllocation
        initialAllocation drawAllocation integerAllocation hp hca hia hd hz q readEarlier readCurrent he hr))
    (@OAI.EditApproximation.queryLocalRefinementFootprint.{u_1, u_2} ι α source target M parent N P F exponent H Q eM eF
      hP hM hF tau a eta kappa delta t parentInitial child initial R hc hi draw integer parentAllocation childAllocation
      initialAllocation drawAllocation integerAllocation q readEarlier readCurrent
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readEarlier key)
          (he key))
      fun key =>
      @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readCurrent key)
        (hr key)) := by
  intros
  simp [queryLocalRefinementHeap, queryLocalRefinementFootprint, queryLocalRefinement, queryRefinementGather]

@[simp] theorem queryLocalRandomSourcesHeap_footprint :
    ∀ {ι : Type u_1} {α : Type u_2} (source target : List.{u_2} α) {M : Nat}
  [_inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
  (parent : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α source)) (N P F exponent H Q eM eF : Nat)
  (hP : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P)
  (hM :
    @Eq.{1} Nat M
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eM))
  (hF :
    @Eq.{1} Nat F
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eF))
  (tau a eta kappa delta : OAI.EditApproximation.BinaryFraction) (t : Nat)
  (parentInitial :
    OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target) →
      Prod.{0, 0} OAI.EditApproximation.BinaryFraction Nat)
  (child initial :
    Fin M →
      OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target) →
        Prod.{0, 0} OAI.EditApproximation.BinaryFraction Nat)
  (R : Nat)
  (hc :
    ∀ (i : Fin M) (r : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)),
      @LE.le.{0} Nat instLENat (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (child i r)) R)
  (hi :
    ∀ (i : Fin M) (r : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)),
      @LE.le.{0} Nat instLENat (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (initial i r)) R)
  (parentAllocation : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target) → Nat)
  (childAllocation initialAllocation : Fin M → OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target) → Nat)
  (hp :
    ∀ (r : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)),
      @LE.le.{0} Nat instLENat (parentAllocation r)
        (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (parentInitial r)))
  (hca :
    ∀ (i : Fin M) (r : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)),
      @LE.le.{0} Nat instLENat (childAllocation i r)
        (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (child i r)))
  (hia :
    ∀ (i : Fin M) (r : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)),
      @LE.le.{0} Nat instLENat (initialAllocation i r)
        (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (initial i r)))
  (q : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))
  (readGroup :
    OAI.EditApproximation.GroupScalarKey M F Q →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (readInteger :
    Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)) →
      Nat → OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (readEarlier :
    Prod.{0, 0} (Fin M) (Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (readCurrent :
    Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)) →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (hg :
    (key : OAI.EditApproximation.GroupScalarKey M F Q) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readGroup key))
  (hz :
    (key : Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      (range : Nat) →
        @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readInteger key range))
  (he :
    (key : Prod.{0, 0} (Fin M) (Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)))) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readEarlier key))
  (hr :
    (key : Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readCurrent key)),
  @Eq.{u_1 + 1}
    (@OAI.EditApproximation.BitQuery.Footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryLocalRandomSources.{u_1, u_2} ι α source target M _inst parent N P F exponent H Q eM
        eF hP hM hF tau a eta kappa delta t parentInitial child initial R hc hi q readGroup readInteger readEarlier
        readCurrent))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryLocalRandomSources.{u_1, u_2} ι α source target M _inst parent N P F exponent H Q eM
        eF hP hM hF tau a eta kappa delta t parentInitial child initial R hc hi q readGroup readInteger readEarlier
        readCurrent)
      (@OAI.EditApproximation.queryLocalRandomSourcesHeap.{u_1, u_2} ι α source target M _inst parent N P F exponent H Q
        eM eF hP hM hF tau a eta kappa delta t parentInitial child initial R hc hi parentAllocation childAllocation
        initialAllocation hp hca hia q readGroup readInteger readEarlier readCurrent hg hz he hr))
    (@OAI.EditApproximation.queryLocalRandomSourcesFootprint.{u_1, u_2} ι α source target M _inst parent N P F exponent H
      Q eM eF hP hM hF tau a eta kappa delta t parentInitial child initial R hc hi parentAllocation childAllocation
      initialAllocation q readGroup readInteger readEarlier readCurrent
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readGroup key)
          (hg key))
      (fun key range =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
          (readInteger key range) (hz key range))
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readEarlier key)
          (he key))
      fun key =>
      @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readCurrent key)
        (hr key)) := by
  intros
  simp [queryLocalRandomSourcesHeap, queryLocalRandomSourcesFootprint, queryLocalRandomSources]

@[simp] theorem queryLocalBandHeap_footprint :
    ∀ {ι : Type u_1} {α : Type u_2} (source target : List.{u_2} α) {M : Nat}
  [_inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
  (parent : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α source)) (N P F exponent H Q eM eF : Nat)
  (hP : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P)
  (hM :
    @Eq.{1} Nat M
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eM))
  (hF :
    @Eq.{1} Nat F
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eF))
  (tau a eta kappa delta : OAI.EditApproximation.BinaryFraction) (t : Nat)
  (parentInitial :
    OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target) →
      Prod.{0, 0} OAI.EditApproximation.BinaryFraction Nat)
  (parentAllocation : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target) → Nat)
  (hp :
    ∀ (r : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)),
      @LE.le.{0} Nat instLENat (parentAllocation r)
        (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (parentInitial r)))
  (readMass readInitial :
    Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)) →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (readGroup :
    OAI.EditApproximation.GroupScalarKey M F Q →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (readInteger :
    Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)) →
      Nat → OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (q : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))
  (readEarlier :
    Prod.{0, 0} (Fin M) (Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (readCurrent :
    Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)) →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (hm :
    (key : Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readMass key))
  (hi :
    (key : Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readInitial key))
  (hg :
    (key : OAI.EditApproximation.GroupScalarKey M F Q) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readGroup key))
  (hz :
    (key : Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      (range : Nat) →
        @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readInteger key range))
  (he :
    (key : Prod.{0, 0} (Fin M) (Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)))) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readEarlier key))
  (hr :
    (key : Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readCurrent key)),
  @Eq.{u_1 + 1}
    (@OAI.EditApproximation.BitQuery.Footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryLocalBand.{u_1, u_2} ι α source target M _inst parent N P F exponent H Q eM eF hP hM
        hF tau a eta kappa delta t parentInitial readMass readInitial readGroup readInteger q readEarlier readCurrent))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryLocalBand.{u_1, u_2} ι α source target M _inst parent N P F exponent H Q eM eF hP hM
        hF tau a eta kappa delta t parentInitial readMass readInitial readGroup readInteger q readEarlier readCurrent)
      (@OAI.EditApproximation.queryLocalBandHeap.{u_1, u_2} ι α source target M _inst parent N P F exponent H Q eM eF hP
        hM hF tau a eta kappa delta t parentInitial parentAllocation hp readMass readInitial readGroup readInteger q
        readEarlier readCurrent hm hi hg hz he hr))
    (@OAI.EditApproximation.queryLocalBandFootprint.{u_1, u_2} ι α source target M _inst parent N P F exponent H Q eM eF
      hP hM hF tau a eta kappa delta t parentInitial parentAllocation readMass readInitial readGroup readInteger q
      readEarlier readCurrent
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readMass key)
          (hm key))
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readInitial key)
          (hi key))
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readGroup key)
          (hg key))
      (fun key range =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
          (readInteger key range) (hz key range))
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readEarlier key)
          (he key))
      fun key =>
      @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readCurrent key)
        (hr key)) := by
  intros
  simp [queryLocalBandHeap, queryLocalBandFootprint, queryLocalBand]

@[simp] theorem queryLocalProgramHeap_footprint :
    ∀ {ι : Type u_1} {α : Type u_2} (source target : List.{u_2} α) {M : Nat}
  [_inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
  (parent : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α source)) (N P F exponent H Q eM eF : Nat)
  (hP : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P)
  (hM :
    @Eq.{1} Nat M
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eM))
  (hF :
    @Eq.{1} Nat F
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eF))
  (tau a eta kappa delta : OAI.EditApproximation.BinaryFraction) (t : Nat)
  (readParent :
    OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target) →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (readMass readInitial :
    Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)) →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (readGroup :
    OAI.EditApproximation.GroupScalarKey M F Q →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (readInteger :
    Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)) →
      Nat → OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (q : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))
  (readEarlier :
    Prod.{0, 0} (Fin M) (Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (readCurrent :
    Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)) →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (hp :
    (key : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readParent key))
  (hm :
    (key : Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readMass key))
  (hi :
    (key : Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readInitial key))
  (hg :
    (key : OAI.EditApproximation.GroupScalarKey M F Q) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readGroup key))
  (hz :
    (key : Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      (range : Nat) →
        @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readInteger key range))
  (he :
    (key : Prod.{0, 0} (Fin M) (Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)))) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readEarlier key))
  (hr :
    (key : Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readCurrent key)),
  @Eq.{u_1 + 1}
    (@OAI.EditApproximation.BitQuery.Footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryLocalProgram.{u_1, u_2} ι α source target M _inst parent N P F exponent H Q eM eF hP
        hM hF tau a eta kappa delta t readParent readMass readInitial readGroup readInteger q readEarlier readCurrent))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryLocalProgram.{u_1, u_2} ι α source target M _inst parent N P F exponent H Q eM eF hP
        hM hF tau a eta kappa delta t readParent readMass readInitial readGroup readInteger q readEarlier readCurrent)
      (@OAI.EditApproximation.queryLocalProgramHeap.{u_1, u_2} ι α source target M _inst parent N P F exponent H Q eM eF
        hP hM hF tau a eta kappa delta t readParent readMass readInitial readGroup readInteger q readEarlier readCurrent
        hp hm hi hg hz he hr))
    (@OAI.EditApproximation.queryLocalProgramFootprint.{u_1, u_2} ι α source target M _inst parent N P F exponent H Q eM
      eF hP hM hF tau a eta kappa delta t readParent readMass readInitial readGroup readInteger q readEarlier
      readCurrent
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readParent key)
          (hp key))
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readMass key)
          (hm key))
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readInitial key)
          (hi key))
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readGroup key)
          (hg key))
      (fun key range =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
          (readInteger key range) (hz key range))
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readEarlier key)
          (he key))
      fun key =>
      @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (readCurrent key)
        (hr key)) := by
  intros
  simp [queryLocalProgramHeap, queryLocalProgramFootprint, queryLocalProgram]

@[simp] theorem queryPhysicalTableReadHeap_footprint :
    ∀ {M J n : Nat} (copies T S : Nat) (parent : OAI.EditApproximation.PhysicalTableRequest M J n)
  (child :
    @Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun r =>
      @LT.lt.{0} Nat instLTNat (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J n T S r)
        (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J n T S parent)),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun r =>
        @LT.lt.{0} Nat instLTNat (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J n T S r)
          (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J n T S parent))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryPhysicalTableRead M J n copies T S parent child))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun r =>
        @LT.lt.{0} Nat instLTNat (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J n T S r)
          (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J n T S parent))
      OAI.EditApproximation.BinaryFraction (@OAI.EditApproximation.queryPhysicalTableRead M J n copies T S parent child)
      (@OAI.EditApproximation.queryPhysicalTableReadHeap M J n copies T S parent child))
    (@OAI.EditApproximation.queryPhysicalTableReadFootprint M J n copies T S parent child) := by
  intros
  simp [queryPhysicalTableReadHeap, queryPhysicalTableReadFootprint, queryPhysicalTableRead]

@[simp] theorem queryMeanReadHeap_footprint :
    ∀ {ι : Type u_1} (count : Nat)
  (reader : Fin count → OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (hr :
    (i : Fin count) → @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (reader i)),
  @Eq.{u_1 + 1}
    (@OAI.EditApproximation.BitQuery.Footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryMeanRead.{u_1} ι count reader))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryMeanRead.{u_1} ι count reader)
      (@OAI.EditApproximation.queryMeanReadHeap.{u_1} ι count reader hr))
    (@OAI.EditApproximation.queryMeanReadFootprint.{u_1} ι count reader fun i =>
      @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (reader i) (hr i)) := by
  intros
  simp [queryMeanReadHeap, queryMeanReadFootprint, queryMeanRead]

@[simp] theorem queryPhysicalScalarReadHeap_footprint :
    ∀ (M J N n exponent F Q R B : Nat) (key : OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0} (OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B)
      OAI.EditApproximation.BinaryFraction (OAI.EditApproximation.queryPhysicalScalarRead M J N n exponent F Q R B key))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B) OAI.EditApproximation.BinaryFraction
      (OAI.EditApproximation.queryPhysicalScalarRead M J N n exponent F Q R B key)
      (OAI.EditApproximation.queryPhysicalScalarReadHeap M J N n exponent F Q R B key))
    (OAI.EditApproximation.queryPhysicalScalarReadFootprint M J N n exponent F Q R B key) := by
  intros
  simp [queryPhysicalScalarReadHeap, queryPhysicalScalarReadFootprint, queryPhysicalScalarRead]

@[simp] theorem queryInitialConeProgramAtHeap_footprint :
    ∀ {ι : Type u_1} {n : Nat} (sourceLength N P F : Nat) (A a : OAI.EditApproximation.BinaryFraction)
  (reader :
    OAI.EditApproximation.TargetInterval n →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (q : OAI.EditApproximation.TargetInterval n)
  (hr :
    (r : OAI.EditApproximation.TargetInterval n) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (reader r)),
  @Eq.{u_1 + 1}
    (@OAI.EditApproximation.BitQuery.Footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryInitialConeProgramAt.{u_1} ι n sourceLength N P F A a reader q))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryInitialConeProgramAt.{u_1} ι n sourceLength N P F A a reader q)
      (@OAI.EditApproximation.queryInitialConeProgramAtHeap.{u_1} ι n sourceLength N P F A a reader q hr))
    (@OAI.EditApproximation.queryInitialConeProgramAtFootprint.{u_1} ι n sourceLength N P F A a reader q fun r =>
      @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (reader r) (hr r)) := by
  intros
  simp [queryInitialConeProgramAtHeap, queryInitialConeProgramAtFootprint, queryInitialConeProgramAt]

@[simp] theorem queryChargedReadHeap_footprint :
    ∀ {M J n passes copies T S : Nat}
  (parent :
    @Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun r =>
      @OAI.EditApproximation.PhysicalTableRequest.Bounded M J n passes copies T S r)
  (key :
    @Subtype.{1} (OAI.EditApproximation.ChargedPhysicalRequest M J n passes copies T S) fun child =>
      @LT.lt.{0} Nat instLTNat (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J n passes copies T S child)
        (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J n passes copies T S
          (@Sum.inr.{0, 0} (OAI.EditApproximation.PhysicalEntry M J n)
            (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun request =>
              @OAI.EditApproximation.PhysicalTableRequest.Bounded M J n passes copies T S request)
            parent))),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (@Subtype.{1} (OAI.EditApproximation.ChargedPhysicalRequest M J n passes copies T S) fun child =>
        @LT.lt.{0} Nat instLTNat (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J n passes copies T S child)
          (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J n passes copies T S
            (@Sum.inr.{0, 0} (OAI.EditApproximation.PhysicalEntry M J n)
              (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun request =>
                @OAI.EditApproximation.PhysicalTableRequest.Bounded M J n passes copies T S request)
              parent)))
      OAI.EditApproximation.BinaryFraction (@OAI.EditApproximation.queryChargedRead M J n passes copies T S parent key))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (@Subtype.{1} (OAI.EditApproximation.ChargedPhysicalRequest M J n passes copies T S) fun child =>
        @LT.lt.{0} Nat instLTNat (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J n passes copies T S child)
          (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J n passes copies T S
            (@Sum.inr.{0, 0} (OAI.EditApproximation.PhysicalEntry M J n)
              (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun request =>
                @OAI.EditApproximation.PhysicalTableRequest.Bounded M J n passes copies T S request)
              parent)))
      OAI.EditApproximation.BinaryFraction (@OAI.EditApproximation.queryChargedRead M J n passes copies T S parent key)
      (@OAI.EditApproximation.queryChargedReadHeap M J n passes copies T S parent key))
    (@OAI.EditApproximation.queryChargedReadFootprint M J n passes copies T S parent key) := by
  intros
  simp [queryChargedReadHeap, queryChargedReadFootprint, queryChargedRead]

@[simp] theorem queryWarmupProgramHeap_footprint :
    ∀ {ι : Type u_1} {nx ny M : Nat} (parent : OAI.EditApproximation.TargetInterval nx) (N P F : Nat)
  (a : OAI.EditApproximation.BinaryFraction)
  (initialRead :
    OAI.EditApproximation.TargetInterval ny →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (childRead :
    Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval ny) →
      OAI.EditApproximation.BitQuery.{u_1, 0} ι OAI.EditApproximation.BinaryFraction)
  (q : OAI.EditApproximation.TargetInterval ny)
  (hi :
    (r : OAI.EditApproximation.TargetInterval ny) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (initialRead r))
  (hc :
    (key : Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval ny)) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (childRead key)),
  @Eq.{u_1 + 1}
    (@OAI.EditApproximation.BitQuery.Footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryWarmupProgram.{u_1} ι nx ny M parent N P F a initialRead childRead q))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryWarmupProgram.{u_1} ι nx ny M parent N P F a initialRead childRead q)
      (@OAI.EditApproximation.queryWarmupProgramHeap.{u_1} ι nx ny M parent N P F a initialRead childRead q hi hc))
    (@OAI.EditApproximation.queryWarmupProgramFootprint.{u_1} ι nx ny M parent N P F a initialRead childRead q
      (fun r =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (initialRead r)
          (hi r))
      fun key =>
      @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} ι OAI.EditApproximation.BinaryFraction (childRead key)
        (hc key)) := by
  intros
  simp [queryWarmupProgramHeap, queryWarmupProgramFootprint, queryWarmupProgram]

end OAI.EditApproximation
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Specification_RawBand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI.EditApproximation

/-- The finite data used after accepting an unskipped band. -/


def UnskippedBand.raw {α : Type*} {source target : List α} {M : ℕ}
    {parent : TargetInterval source.length} {b P exponent : ℕ}
    {tau F : ℚ} {child initial : Fin M → TargetInterval target.length → ℚ}
    (member : UnskippedBand source target parent b P exponent tau F child initial) :
    RawUnskippedBand M target.length :=
  ⟨member.center, member.actions, member.nonempty⟩

end OAI.EditApproximation
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Specification_RawBandPipelineFootprintBridges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false



namespace OAI.EditApproximation

universe u v

abbrev QueryFamilyBoundedActiveFootprintType (qfba : type_of% @queryFamilyBoundedActive.{0}) :=
  ∀ {α : Type} {M J R : ℕ} [NeZero M] [NeZero R] (source target : List α)
    (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
    (tau a eta kappa delta : BinaryFraction) (T S passes copies : ℕ)
    (parent : { r : PhysicalTableRequest M J target.length //
      PhysicalTableRequest.Bounded (passes + 1) copies T S r })
    (hindex : T < parent.val.index) (hbelow : ↑parent.val.node.fst < J),
    (qfba (R := R) source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta T
      S passes copies parent hindex hbelow).Footprint

end OAI.EditApproximation
end


