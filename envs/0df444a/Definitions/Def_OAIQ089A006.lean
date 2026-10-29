-- Prove2me | Definitions.Def_OAIQ089A006
-- name    : OAIQ089A006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T03:00:31.559641+00:00
-- url     : https://prove2.me/theorems/cc0de43e-66d3-427f-b9af-b9c31686d55d
-- title:
--   Definitions bundle OAIQ089A006 of the split of OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 815 declarations of OpenAI's Lean: 782 definitions and 33 theorems. The definitions and types are `OAI.ContingencyTables.CompanionBoundedWalkProgram.advanceRealizer`, `OAI.ContingencyTables.CompanionBoundedWalkProgram.candidateRealizer`, `OAI.ContingencyTables.CompanionBoundedWalkProgram.codeStep`, `OAI.ContingencyTables.CompanionBoundedWalkProgram.history`, `OAI.ContingencyTables.CompanionBoundedWalkProgram.historyRealizer`, `OAI.ContingencyTables.CompanionBoundedWalkProgram.initialRecord`, `OAI.ContingencyTables.CompanionBoundedWalkProgram.initialRecordRealizer`, `OAI.ContingencyTables.CompanionBoundedWalkProgram.nextRealizer`, `OAI.ContingencyTables.CompanionBoundedWalkProgram.recordAdvance`, `OAI.ContingencyTables.CompanionBoundedWalkProgram.recordAdvanceRealizer`, `OAI.ContingencyTables.CompanionBoundedWalkProgram.recordWalk`, `OAI.ContingencyTables.CompanionBoundedWalkProgram.recordWalkRealizer`, `OAI.ContingencyTables.CompanionCanonicalHistory.canonicalAdvance`, `OAI.ContingencyTables.CompanionCanonicalHistory.canonicalDecoded`, `OAI.ContingencyTables.CompanionCanonicalHistory.canonicalEstimate`, `OAI.ContingencyTables.CompanionCanonicalHistory.canonicalStep`, `OAI.ContingencyTables.CompanionCanonicalHistory.sourceAdvance`, `OAI.ContingencyTables.CompanionCanonicalPhaseLaw.canonicalResult`, `OAI.ContingencyTables.CompanionCanonicalPhaseLaw.rawSettings`, `OAI.ContingencyTables.CompanionCanonicalPhaseLaw.readbackResult`, `OAI.ContingencyTables.CompanionCanonicalPhaseLaw.sourceStored`, `OAI.ContingencyTables.CompanionCappedReturnProgram.optionDefaultRealizer`, `OAI.ContingencyTables.CompanionCappedReturnProgram.totalReturnCodeRealizer`, `OAI.ContingencyTables.CompanionChainValidator.pairedStateTestRealizer`, `OAI.ContingencyTables.CompanionComputedInitial.initialProgram`, `OAI.ContingencyTables.CompanionComputedInitial.initialProgramRealizer`, `OAI.ContingencyTables.CompanionComputedProposal.catalogInputRealizer`, `OAI.ContingencyTables.CompanionComputedProposal.proposalProgramRealizer`, `OAI.ContingencyTables.CompanionEvaluatedWeightProgram.LabelIndex`, `OAI.ContingencyTables.CompanionEvaluatedWeightProgram.outputRealizer`, `OAI.ContingencyTables.CompanionEvaluatedWeightProgram.sourceWeights`, `OAI.ContingencyTables.CompanionEvaluatedWeightProgram.weightRealizer`, `OAI.ContingencyTables.CompanionFlatReturnProgram.Input`, `OAI.ContingencyTables.CompanionFlatReturnProgram.data`, `OAI.ContingencyTables.CompanionFlatReturnProgram.output`, `OAI.ContingencyTables.CompanionFlatReturnProgram.outputRealizer`, `OAI.ContingencyTables.CompanionFlatReturnProgram.returnInput`, `OAI.ContingencyTables.CompanionFlatReturnProgram.returnInputRealizer`, `OAI.ContingencyTables.CompanionFlatReturnProgram.stateData`, `OAI.ContingencyTables.CompanionFlatReturnProgram.width` and 742 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `ContingencyTables_Counting_CompanionBoundedWalkProgram`, `ContingencyTables_Counting_CompanionBoundedWalkSemantics`, `ContingencyTables_Counting_CompanionCanonicalHistory`, `ContingencyTables_Counting_CompanionCanonicalHistoryLaw`, `ContingencyTables_Counting_CompanionCanonicalPhaseLaw`, `ContingencyTables_Counting_CompanionCappedReturnProgram`, `ContingencyTables_Counting_CompanionChainValidator`, `ContingencyTables_Counting_CompanionComputedInitial`, `ContingencyTables_Counting_CompanionComputedProposal`, `ContingencyTables_Counting_CompanionEvaluatedWeightProgram`, `ContingencyTables_Counting_CompanionFlatReturnProgram`, `ContingencyTables_Counting_CompanionHistoryReadback`, `ContingencyTables_Counting_CompanionInitialMatrixProgram`, `ContingencyTables_Counting_CompanionInitialStoredProgram`, `ContingencyTables_Counting_CompanionInitializedRestartJoint`, `ContingencyTables_Counting_CompanionInitializedRestartLaw`, `ContingencyTables_Counting_CompanionInitializedRestartProgram`, `ContingencyTables_Counting_CompanionInitializedRestartSemantics`, `ContingencyTables_Counting_CompanionLabelMetadataProgram`, `ContingencyTables_Counting_CompanionMetropolisLaw`, `ContingencyTables_Counting_CompanionMetropolisProgram`, `ContingencyTables_Counting_CompanionMetropolisWordProgram`, `ContingencyTables_Counting_CompanionMetropolisWordSemantics`, `ContingencyTables_Counting_CompanionMultiplierMatrixProgram`, `ContingencyTables_Counting_CompanionMultiplierProgram`, `ContingencyTables_Counting_CompanionNeighborProgram`, `ContingencyTables_Counting_CompanionObservationQueriesLaw`, `ContingencyTables_Counting_CompanionObservationQueriesProgram`, `ContingencyTables_Counting_CompanionObservedUpdateLaw`, `ContingencyTables_Counting_CompanionObservedUpdateProgram`, `ContingencyTables_Counting_CompanionOracleChain`, `ContingencyTables_Counting_CompanionOracleCorrection`, `ContingencyTables_Counting_CompanionOracleDensity`, `ContingencyTables_Counting_CompanionOrderedProposal`, `ContingencyTables_Counting_CompanionOrderedReturn`, `ContingencyTables_Counting_CompanionOuterHistoryProgram`, `ContingencyTables_Counting_CompanionOuterPhaseLaw`, `ContingencyTables_Counting_CompanionOuterPhaseProgram`, `ContingencyTables_Counting_CompanionOuterPhaseSemantics`, `ContingencyTables_Counting_CompanionOuterWidths`, `ContingencyTables_Counting_CompanionPhaseContextProgram`, `ContingencyTables_Counting_CompanionPhaseContinuation`, `ContingencyTables_Counting_CompanionPhaseCounts`, `ContingencyTables_Counting_CompanionPhaseFinishProgram`, `ContingencyTables_Counting_CompanionPhaseTrialLaw`, `ContingencyTables_Counting_CompanionPhaseTrialProgram`, `ContingencyTables_Counting_CompanionPhaseWords`, `ContingencyTables_Counting_CompanionProjectedHistory`, `ContingencyTables_Counting_CompanionRepeatedReturnLaw`, `ContingencyTables_Counting_CompanionRepeatedReturnProgram`, `ContingencyTables_Counting_CompanionRestartContinuation`, `ContingencyTables_Counting_CompanionRestartDataLaw`, `ContingencyTables_Counting_CompanionRestartInitializer`, `ContingencyTables_Counting_CompanionRestartNativeLaw`, `ContingencyTables_Counting_CompanionRestartProgram`, `ContingencyTables_Counting_CompanionRestartSchedule`, `ContingencyTables_Counting_CompanionRestartSemantics`, `ContingencyTables_Counting_CompanionRestartStageLaw`, `ContingencyTables_Counting_CompanionRestartStageProgram`, `ContingencyTables_Counting_CompanionReturnWords`, `ContingencyTables_Counting_CompanionStoredRepresentation`, `ContingencyTables_Counting_CompanionTraceProgram`, `ContingencyTables_Counting_CompanionTrajectoryProgram`, `ContingencyTables_Counting_CompanionTransitionWidth`, `ContingencyTables_Counting_CompanionUniformPhaseBounds`, `ContingencyTables_Counting_CompanionUniformPhaseWidth`, `ContingencyTables_Counting_CompanionWarmStart`, `ContingencyTables_Counting_ComputedCountingParameters`, `ContingencyTables_Counting_ComputedCountingWords`, `ContingencyTables_Counting_ComputedCountingZero`, `ContingencyTables_Counting_CountingActualPhase`, `ContingencyTables_Counting_CountingAdaptiveInputProgram`, `ContingencyTables_Counting_CountingBaseProgram`, `ContingencyTables_Counting_CountingCoefficientProgram`, `ContingencyTables_Counting_CountingComputedSettings`, `ContingencyTables_Counting_CountingDirectProgram`, `ContingencyTables_Counting_CountingLabelCountProgram`, `ContingencyTables_Counting_CountingOracleScheduleProgram`, `ContingencyTables_Counting_CountingPhaseParametersProgram`, `ContingencyTables_Counting_CountingPreparedState`, `ContingencyTables_Counting_CountingTerminalProgram`, `ContingencyTables_Machines_BinaryExchangeProgram`, `ContingencyTables_Machines_EndpointMatrixProgram`, `ContingencyTables_Machines_FractionAcceptanceProgram`, `ContingencyTables_Machines_FractionMetropolisProgram`, `ContingencyTables_Machines_ListWordProgram`, `ContingencyTables_Machines_MatrixSubtractProgram`, `ContingencyTables_Machines_NetworkTableProgram`, `ContingencyTables_Machines_OffsetCountProgram`, `ContingencyTables_Machines_PairedDemandProgram`, `ContingencyTables_Machines_PairedProfileProgram`, `ContingencyTables_Machines_ScalarScheduleProgram`, `ContingencyTables_Machines_SparseViewMatrixProgram`, `ContingencyTables_Machines_TightenedInputProgram`, `ContingencyTables_Machines_WeightedArgmaxProgram`, `ContingencyTables_Rooted_ComputedLargeForest`, `ContingencyTables_Rooted_ComputedRootedInput`, `ContingencyTables_Rooted_ForestEdgeChoiceProgram`, `ContingencyTables_Rooted_ForestGreedyProgram`, `ContingencyTables_Rooted_ForestGreedySemantics`, `ContingencyTables_Rooted_ForestJoinProgram`, `ContingencyTables_Rooted_ForestScaledBounds`, `ContingencyTables_Rooted_LargeEdgeCatalogProgram`, `ContingencyTables_Rooted_RootedArithmeticStep`, `ContingencyTables_Rooted_RootedCappedReturn`, `ContingencyTables_Rooted_RootedCatalogGrid`, `ContingencyTables_Rooted_RootedCorrectionArithmetic`, `ContingencyTables_Rooted_RootedCorrectionSamples`, `ContingencyTables_Rooted_RootedCountingAmplification`, `ContingencyTables_Rooted_RootedCountingWords`, `ContingencyTables_Rooted_RootedEstimatorAmplification`, `ContingencyTables_Rooted_RootedEstimatorLayoutProgram`, `ContingencyTables_Rooted_RootedEstimatorMedianProgram`, `ContingencyTables_Rooted_RootedEstimatorWordProgram`, `ContingencyTables_Rooted_RootedEstimatorWords`, `ContingencyTables_Rooted_RootedLabelWeightProgram`, `ContingencyTables_Rooted_RootedOracleAcceptance`, `ContingencyTables_Rooted_RootedOracleConfigProgram`, `ContingencyTables_Rooted_RootedOracleDraw`, `ContingencyTables_Rooted_RootedOracleEstimator`, `ContingencyTables_Rooted_RootedOracleFiniteStep`, `ContingencyTables_Rooted_RootedOracleRational`, `ContingencyTables_Rooted_RootedPhaseExperiment`, `ContingencyTables_Rooted_RootedPhaseHistory`, `ContingencyTables_Rooted_RootedPhaseTrial`, `ContingencyTables_Rooted_RootedPhaseWords`, `ContingencyTables_Rooted_RootedRatioSamples`, `ContingencyTables_Rooted_RootedRestartTrial`, `ContingencyTables_Rooted_RootedRestartWords`, `ContingencyTables_Rooted_RootedReturnWords`, `ContingencyTables_Rooted_RootedTraceWords`, `ContingencyTables_Rooted_RootedWeightOracle`, `ContingencyTables_Sampling_ProfileScheduleProgram`, `ContingencyTables_Sampling_SmallPatternProgram`, `ContingencyTables_Transport_BoundedProfileWalk`, `ContingencyTables_Transport_ComputedCompanionInstance`, `ContingencyTables_Transport_ComputedTableTightening`, `ContingencyTables_Transport_FiniteGraphRootSemantics`.
--
--   **Imports.** It imports the published bundle `Def_ContingencyTables`; the bundles `OAIQ089A003` and `OAIQ089A004` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ089A009`; the statements `OAI.ContingencyTables.CompanionObservationQueriesProgram.polynomial_output`, `OAI.ContingencyTables.CompanionObservedUpdateProgram.polynomial_output`, `OAI.ContingencyTables.CompanionPhaseContinuation.run_sameLaw`, `OAI.ContingencyTables.CompanionPhaseTrialProgram.polynomial_output`, `OAI.ContingencyTables.CompanionRepeatedReturnProgram.polynomial_output`, `OAI.ContingencyTables.CompanionRestartProgram.output_native_sameLaw`, `OAI.ContingencyTables.ComputedCountingZero.zero_success`, `OAI.ContingencyTables.RootedEstimatorMedianProgram.polynomial_output`, `OAI.ContingencyTables.RootedObservationStart.observed_failure_near`, `OAI.ContingencyTables.RootedPlainTrial.trial_failure` and `OAI.ContingencyTables.RootedTraceWords.arithmetic_recorded_event_bound`; the proofs of `OAI.ContingencyTables.CompanionObservationQueriesProgram.polynomial_output`, `OAI.ContingencyTables.CompanionObservedUpdateProgram.polynomial_output`, `OAI.ContingencyTables.CompanionPhaseTrialProgram.polynomial_output`, `OAI.ContingencyTables.CompanionRepeatedReturnProgram.polynomial_output` and `OAI.ContingencyTables.RootedEstimatorMedianProgram.polynomial_output`.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_ContingencyTables
import Definitions.Def_OAIQ089A003
import Definitions.Def_OAIQ089A004

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionWarmStart
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual companion transversal masses and adjacent warm starts -/

namespace ContingencyTables.CompanionWarmStart

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication CompanionAnnealing CompanionInitialization
open TwoLiftStates LabelledFactorial

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def total (A : Instance I J) (j : ℕ) : ℝ := slotTotal pairs (weight A j) ∅

noncomputable def law (A : Instance I J) (j : ℕ) (S : Set (Labels A×Bool)) : ℝ :=
  weight A j S/total A j

end ContingencyTables.CompanionWarmStart

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestScaledBounds
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual continuous forest penalty stays within the source allowance -/

namespace ContingencyTables.ForestScaledPenalty

open scoped BigOperators Classical
open CompanionFactorialApplication GraphCompletionCounts ForestAssignmentSplit
open ForestAffineCoefficients ForestPhysicalCompletion ForestRootPenalty
open ForestCountIdentification BalancedBox

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def rowCounts (A : Instance I J) (z : View A → ℕ) : I → J → ℤ :=
  fun i j => (smallX A.small z i j:ℤ)

noncomputable def columnCounts (A : Instance I J) (z : View A → ℕ) : I → J → ℤ :=
  fun i j => ((A.b i j-smallY A.small z i j:ℕ):ℤ)

end ContingencyTables.ForestScaledPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleDensity
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal weight-evaluator density on its finite-dimensional bin cube -/

namespace ContingencyTables.CompanionOracleDensity

open scoped BigOperators Classical
open CompanionFactorialApplication ForestAssignmentSplit ForestScaledPenalty

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def D (A : Instance I J) (C : ℝ) (z : View A → ℕ)
    (v : Fin (dimension A) → ℝ) : ℝ :=
  penalty A C (binWidth A C) (rowCounts A z) (columnCounts A z) (pull A v)

noncomputable def rho (A : Instance I J) (C a : ℝ) (z : View A → ℕ) :
    (Fin (dimension A) → ℝ) → ℝ := DenseWeights.density (a/height A C) (D A C z)

noncomputable def V (A : Instance I J) (C a : ℝ) (z : View A → ℕ) :
    (Fin (dimension A) → ℝ) → ℝ := DenseWeights.binWeight (a/height A C) (D A C z)

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleChain
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual finite bin chain for the companion evaluator -/

namespace ContingencyTables.CompanionOracleDensity

open CommonBasesFPRAS GridBoundary CompanionFactorialApplication
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def gridWeight (A : Instance I J) (C a : ℝ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) : ℝ := V A C a z (realCorner v)

end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOracleCorrection
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact population correction for the literal companion weight -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit ForestScaledPenalty GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def ratioObservable (A : Instance I J) (C : ℝ) (a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) : ℝ :=
  gridWeight A C (a+1) z v/gridWeight A C a z v


end

end ContingencyTables.CompanionOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseWords
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit fresh words and rational arithmetic for one outer phase -/

namespace ContingencyTables.CompanionPhaseWords

open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle CompanionRationalUpdates
open CommonBasesFPRAS GridBoundary FirstSuccess FairBits TwoLiftStates
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Separate current-parameter and next-parameter oracle words are
reserved at every observed state, including states at which they are unused. -/
def observationBits (A : Instance I J) (C K j : ℕ) (xi : ℚ) : ℕ :=
  medianEstimatorBits A C K j xi xi+medianEstimatorBits A C K (j+1) xi xi

def phaseBits (A : Instance I J) (C K j N : ℕ) (xi : ℚ) : ℕ :=
  N*observationBits A C K j xi

def phaseWordEquiv (A : Instance I J) (C K j N : ℕ) (xi : ℚ) :
    (Fin (phaseBits A C K j N xi) → Bool) ≃
      (Fin N → WeightWord A C K j xi × WeightWord A C K (j+1) xi) :=
  (oracleWalkWordEquiv N (observationBits A C K j xi)).trans
    (Equiv.piCongrRight (fun _ => splitWordEquiv _ _))

end

end ContingencyTables.CompanionPhaseWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BinaryExchangeProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial enumeration of exchanges of a binary profile

The program scans at most the square of the list length. It retains only
an absent receiving coordinate and a present donating coordinate, so every
retained natural-number update is again a binary profile.
-/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial
open scoped BigOperators Classical

def binaryExchangeTestRealizer : Realizer binaryExchangeTest := by
  let V : Realizer (fun z : List ℕ×(ℕ×ℕ) => z.1) := first
  let I : Realizer (fun z : List ℕ×(ℕ×ℕ) => z.2.1) := composition second first
  let J : Realizer (fun z : List ℕ×(ℕ×ℕ) => z.2.2) := composition second second
  let absent := composition (pair (composition (pair V I) (getDFast 0)) (constant 0)) natEqual
  let present := composition (pair (composition (pair V J) (getDFast 0)) (constant 1)) natEqual
  exact (choose absent present (constant false)).congr (by
    intro z
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,binaryExchangeTest,decide_eq_true_eq]
    split_ifs <;> simp_all)

def binaryExchangeIndicesRealizer : Realizer binaryExchangeIndices :=
  composition (pair identity (composition (pair identity identity) cellPairsRealizer))
    (filterWith binaryExchangeTestRealizer)

def binaryExchangesRealizer : Realizer binaryExchanges :=
  composition (pair identity binaryExchangeIndicesRealizer) (mapWith listExchangeRealizer)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ListWordProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary execution of the finite-list proposal

The list is scanned only up to its own length. A binary index beyond the
end produces `none`; its numerical magnitude never determines a loop bound.
-/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators

variable {A : Type} [Codec A] [Inhabited A]

def getOptionFast : Realizer (fun x : List A×ℕ => x.1[x.2]?) :=
  (choose (composition (pair second (composition first listLength)) less)
    (composition (getDFast default) TreeTyped.some) (constant none)).congr (by
      intro x
      simp only [Function.comp_apply,decide_eq_true_eq]
      by_cases h : x.2<x.1.length
      · rw [ite_eq_left h,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]
        rfl
      · rw [ite_eq_right h,List.getElem?_eq_none (by omega)])

def listWordChoiceRealizer : Realizer (listWordChoice (A := A)) :=
  composition (pair first (composition second bitValue)) getOptionFast

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallPatternProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial tests for the two allowed small-profile patterns -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

def balancedAtRealizer : Realizer balancedAt :=
  composition (pair pairSumRealizer (composition first second)) natEqual

def balancedTestRealizer : Realizer balancedTest :=
  (composition (composition (pair identity patternIndices) (mapWith balancedAtRealizer)) all).congr
    (by intro z; simp only [Function.comp_apply,List.all_map,Function.comp_def,id_eq,balancedTest])

def patternTestRealizer : Realizer patternTest :=
  (composition (pair balancedTestRealizer
    (composition (composition (pair identity
      (composition (pair (composition first first) (composition first first)) cellPairsRealizer))
      (mapWith defectTestRealizer)) any)) boolOr).congr (by
        intro z
        simp only [Function.comp_apply,List.any_map,Function.comp_def,id_eq,patternTest])

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionChainValidator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial validation of paired binary states

The bounded-profile arithmetic test specializes to width one.
Thus the companion's state filter is a concrete list program on the two
coordinates of every labelled pair.
-/

namespace ContingencyTables.CompanionChainValidator
open CommonBasesFPRAS TwoLiftStates ProfilePrograms
open MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

def pairedStateTestRealizer : Realizer pairedStateTest :=
  composition (pair (pair
    (composition (pair second first) (mapWith pairFirstLookup))
    (composition (pair second first) (mapWith pairSecondLookup))) (constant 1)) patternTestRealizer

end ContingencyTables.CompanionChainValidator

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionNeighborProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable valid-neighbor lists and their binary draw

This composes the actual integer-exchange program with the paired-state
validator and the bounded list-index program. The output code is exactly
the encoding of the semantic proposal, including its failure outcome.
-/

namespace ContingencyTables.CompanionNeighborProgram
open CompanionChainValidator CompanionArithmeticProposal CompanionFactorialApplication
open CompanionBooleanPhase ProfilePrograms MatchingFPRAS.TreeTyped
open CommonBasesFPRAS
open scoped BigOperators Classical

def validExchangesRealizer : Realizer validExchanges :=
  composition (pair first (composition second binaryExchangesRealizer))
    (filterWith pairedStateTestRealizer)

def codeProposalRealizer : Realizer codeProposal :=
  composition (pair (composition first validExchangesRealizer) second) listWordChoiceRealizer

end ContingencyTables.CompanionNeighborProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOrderedProposal
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The companion proposal with a specified coordinate order

The coordinate scan and its paired-state validator work with the same
explicit order used by the initializer. Its dyadic proposal law is
independent of this order, including unused proposal words.
-/

namespace ContingencyTables.CompanionOrderedProposal

open CommonBasesFPRAS TwoLiftStates CompanionFactorialApplication
open CompanionArithmeticProposal CompanionChainValidator CompanionNeighborProgram
open CompanionBooleanPhase FirstSuccess ResidualMixture ProfilePrograms
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]
variable (A : Instance I J) {m p : ℕ}

def orderedNeighbors (e : (Labels A×Bool) ≃ Fin m) (S : State A) : List (State A) :=
  neighborStates e pairs S

def orderedProposal (e : (Labels A×Bool) ≃ Fin m) (S : State A)
    (bits : Fin (proposalBits A) → Bool) : Option (State A) :=
  listWordChoice (orderedNeighbors A e S,List.ofFn bits)

end
end ContingencyTables.CompanionOrderedProposal

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionComputedInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Initialization from the computed small-cell catalog

The proof-level equivalence follows the actual catalog program. It is
used only to identify the output of the binary list initializer with a
paired transversal and to transfer its distributional error bound.
-/

namespace ContingencyTables.CompanionComputedInitial

open MatchingFPRAS.TreeTyped CompanionFactorialApplication
open InitialTransversals InitialFactorialBits CompanionInitialDraw
open FirstSuccess ResidualMixture TwoLiftStates CommonBasesFPRAS
open CompanionArithmeticProposal
open scoped BigOperators Classical

def initialProgram (z : ProgramInput) : List ℕ :=
  CanonicalInitialEncoding.initialCode ((CompanionCellCatalog.capacities z.1.1,z.1.2),z.2)

def initialProgramRealizer : Realizer initialProgram :=
  composition (pair (pair
    (composition (composition first first) CompanionCellCatalog.capacitiesRealizer)
    (composition first second)) second) CanonicalInitialEncoding.initialCodeRealizer

end ContingencyTables.CompanionComputedInitial

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionComputedProposal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The companion proposal with computed metadata

The executable proposal receives only a binary profile and fresh bits.
It computes the consecutive-pair catalog itself and scans coordinate
exchanges. Its semantic law is the same ordered proposal law.
-/

namespace ContingencyTables.CompanionComputedProposal

open MatchingFPRAS.TreeTyped CompanionFactorialApplication CompanionComputedInitial
open CompanionArithmeticProposal CompanionOrderedProposal CompanionNeighborProgram
open CompanionBooleanPhase
open scoped Classical

def catalogInputRealizer : Realizer (fun z : List ℕ×List Bool => PairedCatalogProgram.catalog z.1) :=
  composition (f := fun z : List ℕ×List Bool => z.1) (g := PairedCatalogProgram.catalog)
    first PairedCatalogProgram.catalogRealizer

def proposalProgramRealizer : Realizer proposalProgram :=
  composition (f := fun z : List ℕ×List Bool => ((PairedCatalogProgram.catalog z.1,z.1),z.2))
    (g := codeProposal) (pair (pair catalogInputRealizer first) second) codeProposalRealizer

end ContingencyTables.CompanionComputedProposal

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionTraceProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial code for recognizing and locating a trace return

The paired plain-state test sums the two bits of each label. The return
program scans the supplied path after its initial state; no enumeration
of the exponential paired-state space occurs.
-/

namespace ContingencyTables.CompanionTraceProgram

open CommonBasesFPRAS CompanionChainValidator CompanionArithmeticProposal
open CompanionFactorialApplication CompanionBooleanPhase CompanionTraceWords
open ProfilePrograms MatchingFPRAS.TreeTyped
open scoped Classical

def pairedPlainTestRealizer : Realizer pairedPlainTest :=
  composition (pair (pair
    (composition (pair second first) (mapWith pairFirstLookup))
    (composition (pair second first) (mapWith pairSecondLookup))) (constant 1))
    balancedTestRealizer

def firstPlainCodeRealizer : Realizer firstPlainCode :=
  composition (composition (filterWith pairedPlainTestRealizer)
    (pair identity (constant 0))) getOptionFast

def returnCodeRealizer : Realizer returnCode :=
  composition (pair first (composition second tail)) firstPlainCodeRealizer

end ContingencyTables.CompanionTraceProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable counts in an outer counting phase

The stored trajectory is scanned directly. Both the transversal count
and each labelled defect count use the actual polynomial occupancy
tests. No set-state enumeration is performed.
-/

namespace ContingencyTables.CompanionPhaseCounts

open MatchingFPRAS.TreeTyped ProfilePrograms CompanionChainValidator
open CompanionTraceProgram CompanionOrderedProposal CompanionArithmeticProposal
open CompanionFactorialApplication CompanionBooleanPhase
open CommonBasesFPRAS TwoLiftStates
open scoped Classical

def plainCountRealizer : Realizer plainCountCode :=
  composition (filterWith pairedPlainTestRealizer) listLength

def defectItemRealizer : Realizer defectItem :=
  composition (pair (pair (composition first first) second) (composition first second))
    pairedDefectTestRealizer

def defectCountRealizer : Realizer defectCountCode :=
  composition (composition (pair (pair (composition first first) second)
    (composition first second)) (filterWith defectItemRealizer)) listLength

end ContingencyTables.CompanionPhaseCounts

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionMultiplierProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A binary rational program for each learned multiplier

The two observed frequencies have the same trajectory length, which
cancels before division. Thus one multiplication by the ratio of the
actual integer counts implements the exact rational update, including
the zero-denominator behavior on unsuccessful histories.
-/

namespace ContingencyTables.CompanionMultiplierProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open CompanionPhaseCounts CompanionFactorialApplication CompanionRationalUpdates
open CompanionOrderedProposal CompanionArithmeticProposal CommonBasesFPRAS
open scoped Classical

def countPlainRealizer : Realizer (fun z : DefectCountInput => plainCountCode z.1) :=
  composition (f := fun z : DefectCountInput => z.1) (g := plainCountCode)
    first plainCountRealizer

def countRatioRealizer : Realizer countRatio :=
  pair countPlainRealizer defectCountRealizer

def diagonalRealizer : Realizer (fun z : UpdateInput => decide (z.1.2.1=z.1.2.2)) :=
  composition (pair (composition (composition first second) first)
    (composition (composition first second) second)) natEqual

def updateCodeRealizer : Realizer updateCode :=
  (choose diagonalRealizer second
    (composition (pair second (composition first countRatioRealizer)) TreeFraction.mulRealizer)).congr
      (by intro z; simp only [updateCode,Function.comp_apply,decide_eq_true_eq])

end ContingencyTables.CompanionMultiplierProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionMultiplierMatrixProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full multiplier update and abort test as list programs

Only the polynomial list of labelled pairs is traversed. Every matrix
entry is updated from the actual plain and defect counts of the stored
trajectory. The count check includes every off-diagonal labelled type.
-/

namespace ContingencyTables.CompanionMultiplierMatrixProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
open CompanionPhaseCounts CompanionMultiplierProgram CompanionOrderedProposal CompanionTraceProgram
open CompanionFactorialApplication CompanionArithmeticProposal CompanionRationalUpdates
open CommonBasesFPRAS
open scoped Classical

def indicesRealizer : Realizer indices := composition (composition first listLength) range

def updateEntryRealizer : Realizer updateEntry :=
  composition (pair (pair (composition first first) second)
    (composition (pair (composition first second) second) readEntryRealizer)) updateCodeRealizer

def rowEntryRealizer : Realizer rowEntry :=
  composition (pair (composition first first) (pair (composition first second) second))
    updateEntryRealizer

def updateRowRealizer : Realizer updateRow :=
  composition (pair identity (composition (composition first first) indicesRealizer))
    (mapWith rowEntryRealizer)

def updateMatrixRealizer : Realizer updateMatrix :=
  composition (pair identity (composition first indicesRealizer)) (mapWith updateRowRealizer)

def positiveEntryRealizer : Realizer positiveEntry :=
  (choose (composition second natEqual) (constant true)
    (composition (pair (constant 0) defectCountRealizer) less)).congr (by
      intro z
      by_cases h : z.2.1=z.2.2 <;> simp [positiveEntry,h])

def positiveRowRealizer : Realizer positiveRow :=
  (composition (composition (pair identity (composition first indicesRealizer))
    (mapWith (composition (pair (composition first first)
      (pair (composition first second) second)) positiveEntryRealizer))) all).congr (by
        intro z
        simp only [Function.comp_apply,List.all_map,Function.comp_def,id_eq,positiveRow])

def positiveCountsRealizer : Realizer positiveCounts :=
  (composition (pair (composition (pair (constant 0) plainCountRealizer) less)
    (composition (composition (pair identity indicesRealizer) (mapWith positiveRowRealizer)) all))
      boolAnd).congr (by
        intro z
        simp only [Function.comp_apply,List.all_map,Function.comp_def,id_eq,positiveCounts])

end ContingencyTables.CompanionMultiplierMatrixProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_MatrixSubtractProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Entrywise natural subtraction on a supplied matrix shape -/

namespace ContingencyTables.MatrixSubtractProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial DensePrograms

def entryRealizer : Realizer entry := by
  let left : Realizer (fun z : RowInput × ℕ => matrixEntry (z.1.1.1,(z.1.2,z.2))) :=
    composition (f := fun z : RowInput × ℕ => (z.1.1.1,(z.1.2,z.2))) (g := matrixEntry)
      (pair (composition (composition first first) first)
        (pair (composition first second) second)) matrixEntryRealizer
  let right : Realizer (fun z : RowInput × ℕ => matrixEntry (z.1.1.2,(z.1.2,z.2))) :=
    composition (f := fun z : RowInput × ℕ => (z.1.1.2,(z.1.2,z.2))) (g := matrixEntry)
      (pair (composition (composition first first) second)
        (pair (composition first second) second)) matrixEntryRealizer
  exact composition (f := fun z : RowInput × ℕ =>
    (matrixEntry (z.1.1.1,(z.1.2,z.2)),matrixEntry (z.1.1.2,(z.1.2,z.2))))
    (g := fun p : ℕ × ℕ => p.1-p.2) (pair left right) subtract
def sourceRowRealizer : Realizer sourceRow :=
  composition (pair (composition first first) second) (getDFast [])
def columnsRealizer : Realizer columns :=
  composition (f := sourceRow) (g := fun xs : List ℕ => List.range xs.length)
    sourceRowRealizer (composition listLength range)
def rowRealizer : Realizer row :=
  composition (pair identity columnsRealizer) (mapWith entryRealizer)
def indicesRealizer : Realizer indices := composition (composition first listLength) range
def matrixRealizer : Realizer matrix :=
  composition (pair identity indicesRealizer) (mapWith rowRealizer)

end ContingencyTables.MatrixSubtractProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_SparseViewMatrixProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Materializing a sparse retained-cell view in a rectangular matrix -/

namespace ContingencyTables.SparseViewMatrixProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial ProfilePrograms DensePrograms

def entryRealizer : Realizer entry :=
  composition (f := fun z : RowInput × ℕ => (z.1.1.2,(z.1.2,z.2))) (g := lookupView)
    (pair (composition (composition first first) second)
      (pair (composition first second) second)) lookupViewRealizer
def columnsRealizer : Realizer columns :=
  composition (composition (composition (composition first first) second) listLength) range
def rowRealizer : Realizer row :=
  composition (pair identity columnsRealizer) (mapWith entryRealizer)
def rowIndicesRealizer : Realizer rowIndices :=
  composition (composition (composition first first) listLength) range
def matrixRealizer : Realizer matrix :=
  composition (pair identity rowIndicesRealizer) (mapWith rowRealizer)

end ContingencyTables.SparseViewMatrixProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FractionAcceptanceProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary execution of the rational acceptance coin

The integer quotient computes the exact floor threshold used by the
finite-word acceptance law. The word length controls all powering and
word traversal, even for malformed fraction inputs.
-/

namespace ContingencyTables.FractionAcceptanceProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms

def scaledNumeratorRealizer : Realizer scaledNumerator :=
  composition (f := fun z : Input => (z.1.1,bitDenominator z.2))
    (g := fun x : ℕ×ℕ => x.1*x.2)
    (pair (composition first first) (composition second bitDenominatorRealizer)) multiply

def thresholdRealizer : Realizer threshold :=
  composition (f := fun z : Input => (scaledNumerator z,z.1.2))
    (g := fun x : ℕ×ℕ => x.1/x.2)
    (pair scaledNumeratorRealizer (composition first second)) quotient

def acceptCodeRealizer : Realizer acceptCode :=
  composition (f := fun z : Input => (StackAddition.value z.2,threshold z))
    (g := fun x : ℕ×ℕ => decide (x.1<x.2))
    (pair (composition second bitValue) thresholdRealizer) less

end ContingencyTables.FractionAcceptanceProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteGraphRootSemantics
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact correctness of the finite component-root program

The stored adjacency list is identified with the given finite graph.
Each list growth round is the proved finite reachability growth, and
the final binary minimum is the least vertex of the actual component.
-/

namespace ContingencyTables.FiniteGraphRootProgram

open MatchingFPRAS.ComputableReach SimpleGraph

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

lemma grow_mem (s : List ℕ) (b : Fin n) :
    b.val∈grow (graphCode G,s) ↔
      b.val∈s ∨ ∃ a : Fin n,a.val∈s ∧ G.Adj a b := by
  simp only [grow,indices,List.mem_filter,List.mem_range,graphCode_length,growTest,
    Bool.or_eq_true,decide_eq_true_eq,neighborHit,List.any_eq_true,graphCode_getD,
    b.isLt,true_and]
  constructor
  · rintro (h|⟨a,ha,hs⟩)
    · exact Or.inl h
    · obtain ⟨u,hu,hg⟩ := (adjacencyRow_mem G b a).mp ha
      exact Or.inr ⟨u,hu.symm ▸ hs,hg⟩
  · rintro (h|⟨a,ha,hg⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a.val,(adjacencyRow_mem G b a.val).mpr ⟨a,rfl,hg⟩,ha⟩

lemma iterate_mem (v b : Fin n) (k : ℕ) :
    b.val∈(fun s => grow (graphCode G,s))^[k] [v.val] ↔
      b∈MatchingFPRAS.ComputableReach.reached G {v} k := by
  induction k generalizing b with
  | zero =>
    simp only [Function.iterate_zero_apply,List.mem_singleton,
      MatchingFPRAS.ComputableReach.reached,Finset.mem_singleton]
    exact Fin.ext_iff.symm
  | succ k ih =>
    rw [Function.iterate_succ_apply',grow_mem,
      MatchingFPRAS.ComputableReach.reached_step,mem_grow]
    simp only [ih]

theorem reached_mem_iff (v b : Fin n) :
    b.val∈reached (graphCode G,v.val) ↔ G.Reachable v b := by
  rw [reached_eq_iterate,iterate_mem]
  simpa only [MatchingFPRAS.ComputableReach.closure,Fintype.card_fin] using mem_closure G v b

end ContingencyTables.FiniteGraphRootProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleRational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed-root grid weights are exactly dyadic rational values -/

namespace ContingencyTables.RootedOracleDensity

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit GraphCompletionCounts GridBoundary
open CompanionOracleDensity (dimension index height rationalHeight naturalBin)

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def rationalD (A : Instance I J) (S : Selection A.T) (C : ℕ)
    (z : View A → ℕ) (v : Fin (dimension A) → ℚ) : ℚ :=
  RootedPenaltyProgram.rationalPenalty A S C (ForestScaledPenalty.rowCounts A z)
    (ForestScaledPenalty.columnCounts A z) (fun f => v ((index A).symm f))

noncomputable def gridExponent (A : Instance I J) (S : Selection A.T) (C a : ℕ)
    (z : View A → ℕ) {K : ℕ} (v : Grid (I := Fin (dimension A)) K) : ℕ :=
  ⌊(a:ℚ)/rationalHeight A C*rationalD A S C z (fun i => (corner v i:ℚ))⌋₊

noncomputable def rationalGridWeight (A : Instance I J) (S : Selection A.T) (C a : ℕ)
    (z : View A → ℕ) {K : ℕ} (v : Grid (I := Fin (dimension A)) K) : ℚ :=
  1/(2:ℚ)^gridExponent A S C a z v

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCatalogGrid
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computed catalog coordinates for the oracle grid

The executable free-cell order need not agree with `Fintype.equivFin`.
Explicit reindexing identifies the grid exponent evaluated from the
catalog-ordered list.
-/

namespace ContingencyTables.RootedCatalogGrid

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open RootedCompletion
open scoped Classical

noncomputable section
variable {m n : ℕ}

def coordinateEquiv (A : Instance (Fin m) (Fin n)) :
    Fin (freeCount A) ≃ Fin (CompanionOracleDensity.dimension A) :=
  (RootedForestCatalog.freeEquiv A).trans (CompanionOracleDensity.index A).symm

def gridEquiv (A : Instance (Fin m) (Fin n)) (K : ℕ) :
    Grid (I := Fin (freeCount A)) K ≃
      Grid (I := Fin (CompanionOracleDensity.dimension A)) K where
  toFun v i := v ((coordinateEquiv A).symm i)
  invFun v i := v (coordinateEquiv A i)
  left_inv v := by funext i; simp only [Equiv.symm_apply_apply]
  right_inv v := by funext i; simp only [Equiv.apply_symm_apply]

end
end ContingencyTables.RootedCatalogGrid

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleFiniteStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed Boolean words realize the selected-root grid chain -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication GridBoundary CommonBasesFPRAS ResidualMixture FirstSuccess FairBits
open CompanionOracleDensity (dimension binWidth rationalHeight rationalHeight_cast oracleStepBits oracleTime)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

def oracleBitStep (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K)
    (bits : Fin (oracleStepBits A C) → Bool) : Grid (I := Fin (dimension A)) K :=
  let draw := pairWordEquiv (Nat.clog 2 (8*A.d)) (rationalHeight A C) bits
  match axisCodeStep v draw.1 with
  | none => v
  | some w => if draw.2.val < 2^(rationalHeight A C-(gridExponent A R C a z w-gridExponent A R C a z v))
      then w else v

end
end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PairedProfileProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reading the two cell counts from the actual paired code

The block widths come from the stored capacity list. Each count scans
only supplied code entries and clips them to one, including on malformed
input. No numeric capacity controls an unbounded allocation.
-/

namespace ContingencyTables.PairedProfileProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

def countsRealizer : Realizer counts :=
  pair (composition (f := fun xs : List ℕ => (xs,false)) (g := sideCount)
    (pair identity (constant false)) sideCountRealizer)
    (composition (f := fun xs : List ℕ => (xs,true)) (g := sideCount)
      (pair identity (constant true)) sideCountRealizer)
def profileRowsRealizer : Realizer profileRows := composition rowsRealizer (map countsRealizer)

end ContingencyTables.PairedProfileProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PairedDemandProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Replacing the oracle demand by the current encoded paired state

Only the retained-cell catalog and the supplied state are scanned. The
large cells receive zero in each sparse view and hence retain their full
capacity in the complemented column demand.
-/

namespace ContingencyTables.PairedDemandProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

def countsRealizer : Realizer counts :=
  composition (f := fun z : Input => (CompanionCellCatalog.capacities (cells z),z.2))
    (g := PairedProfileProgram.profileRows)
    (pair (composition (f := cells) (g := CompanionCellCatalog.capacities)
      cellsRealizer CompanionCellCatalog.capacitiesRealizer) second)
    PairedProfileProgram.profileRowsRealizer
def valuesRealizer : Realizer values :=
  composition (f := fun z : Input × Bool => (z.2,counts z.1))
    (g := fun p : Bool × List (ℕ × ℕ) => p.2.map (fun a => sideEntry (p.1,a)))
    (pair second (composition (f := Prod.fst) (g := counts) first countsRealizer))
    (mapWith sideEntryRealizer)
def viewInputRealizer : Realizer viewInput :=
  pair (composition (composition (composition (composition first first) first) first) second)
    (pair (composition (f := fun z : Input × Bool => cells z.1)
      (g := CompanionCellCatalog.catalog)
      (composition (f := Prod.fst) (g := cells) first cellsRealizer)
      CompanionCellCatalog.catalogRealizer) valuesRealizer)
def viewMatrixRealizer : Realizer viewMatrix :=
  composition (f := viewInput) (g := SparseViewMatrixProgram.matrix)
    viewInputRealizer SparseViewMatrixProgram.matrixRealizer
def complementRealizer : Realizer complement :=
  composition (f := fun z : Input => (z.1.1.2,viewMatrix (z,true)))
    (g := MatrixSubtractProgram.matrix)
    (pair (composition (composition first first) second)
      (composition (f := fun z : Input => (z,true)) (g := viewMatrix)
        (pair identity (constant true)) viewMatrixRealizer)) MatrixSubtractProgram.matrixRealizer
def outputRealizer : Realizer output :=
  pair (composition first first)
    (pair (composition (composition first second) first)
      (pair (composition (f := fun z : Input => (z,false)) (g := viewMatrix)
        (pair identity (constant false)) viewMatrixRealizer) complementRealizer))
end ContingencyTables.PairedDemandProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleDraw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual fixed-word corrected draws for the selected-root count -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess FairBits
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]


def flatOracleWalk (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) (n : ℕ)
    (bits : Fin (n*oracleStepBits A C) → Bool) : Grid (I := Fin (dimension A)) K :=
  wordWalk (oracleBitStep A R C a z) v n (oracleWalkWordEquiv n (oracleStepBits A C) bits)

def oracleIntegerDraw (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (dimension A)) K) (n h : ℕ)
    (bits : Fin (oracleIntegerBits A C n h) → Bool) : FreeIndex A.small A.T A.b :=
  let draws := splitWordEquiv (n*oracleStepBits A C) (binWordBits A h) bits
  flatBinDraw A K (by omega) hW (flatOracleWalk A R C a z v n draws.1) h draws.2

end
end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCorrectionArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational evaluation of the literal integer-population correction -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def correctionExponent (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 0 < K) (f : FreeIndex A.small A.T A.b) : ℚ :=
  (gridExponent A R C a z (integerBin A K hK f):ℚ)-
    (a:ℚ)/rationalHeight A C*rationalD A R C z (rationalIntegerPoint A C f)

def computedCorrection (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 0 < K) (sigma : ℚ) (f : FreeIndex A.small A.T A.b) : ℚ :=
  rationalPopulation A K hK f*
    PowerOfTwoApproximation.approximate (correctionExponent A R C a z K hK f) sigma

end

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCorrectionSamples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Confidence for the actual rational correction samples -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteIndependentAverages
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def correctionSample (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (sigma : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (n h : ℕ)
    (bits : Fin (oracleIntegerBits A C n h) → Bool) : ℚ :=
  computedCorrection A R C a z K (by omega) sigma (oracleIntegerDraw A R C a z K hK hW v n h bits)

end

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedRatioSamples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete rational observations of the companion annealing ratios -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication GridBoundary CommonBasesFPRAS ResidualMixture FirstSuccess
open FiniteIndependentAverages
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def rationalRatioObservable (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) : ℚ :=
  rationalGridWeight A R C (a+1) z v/rationalGridWeight A R C a z v

def ratioSample (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) (n : ℕ) (bits : RatioWords A C n) : ℚ :=
  rationalRatioObservable A R C a z (wordWalk (oracleBitStep A R C a z) v n bits)

end

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleEstimator
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal rational product estimator for a companion h-value -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteIndependentAverages
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def observedFactor (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (j : ℕ) (delta failure : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (draws : EstimatorInput A C K j delta failure) :
    Option (Fin j) → ℚ
  | none => rationalAverage
      (correctionSample A R C j z K hK hW (roundingTolerance delta) v
        (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta))
      (sampleCount j delta failure) draws.2
  | some a => rationalAverage
      (ratioSample A R C a.val z v (oracleTime A C K 1 delta))
      (sampleCount j delta failure) (draws.1 a)

def estimateValue (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (j : ℕ) (delta failure : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (draws : EstimatorInput A C K j delta failure) : ℚ :=
  (assignmentCount A:ℚ)*∏ i,observedFactor A R C z K hK hW j delta failure v draws i

end

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single Boolean word for the literal companion weight estimator -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteIndependentAverages FairBits
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def wordEstimate (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (j : ℕ) (epsilon failure : ℚ)
    (v : Grid (I := Fin (dimension A)) K)
    (bits : Fin (estimatorWordBits A C K j (innerTolerance epsilon j) failure) → Bool) : ℚ :=
  estimateValue A R C z K hK hW j (innerTolerance epsilon j) failure v
    (estimatorWordEquiv A C K j (innerTolerance epsilon j) failure bits)

end

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorAmplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic confidence amplification of the actual weight estimator -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def medianEstimate (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (j : ℕ) (epsilon delta : ℚ)
    (v : Grid (I := Fin (dimension A)) K)
    (bits : Fin (medianEstimatorBits A C K j epsilon delta) → Bool) : ℚ :=
  rationalMedian (List.ofFn (fun i : Fin (repetitionCount delta) =>
    wordEstimate A R C z K hK hW j (epsilon/2) 1 v
      (oracleWalkWordEquiv (repetitionCount delta)
        (estimatorWordBits A C K j (innerTolerance (epsilon/2) j) 1) bits i)))


end

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorLayoutProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computed sizes of the estimator's disjoint word banks

The schedule supplies the phase and sample counts and the two walk times.
The catalog itself supplies both the integer-draw widths and the initial
free-assignment count. No list is allocated from a binary count here.
-/

namespace ContingencyTables.RootedEstimatorLayoutProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

attribute [local irreducible] frames

attribute [local irreducible] rangeValue rangeValues

def wordWidthRealizer : Realizer wordWidth :=
  composition (f := fun z : Context => (ratioBankWidth z,z.2.1.2*correctionWidth z))
    (g := fun p : ℕ×ℕ => p.1+p.2) (pair ratioBankWidthRealizer
      (composition (f := fun z : Context => (z.2.1.2,correctionWidth z))
        (g := fun p : ℕ×ℕ => p.1*p.2)
        (pair (composition (composition second first) second) correctionWidthRealizer) multiply)) add

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open scoped BigOperators Classical

end ContingencyTables.RootedEstimatorLayoutProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorWordProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One flat word executes the complete weight estimator

The number of generated rows is bounded by the supplied word length.
The binary schedule therefore remains safe even on malformed inputs.
-/

namespace ContingencyTables.RootedEstimatorWordProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
open RootedEstimatorLayoutProgram

def phaseRealizer : Realizer phase := by
  let k : Realizer (fun z : State×ℕ => z.1.1.1) := composition (composition first first) first
  let dw : Realizer (fun z : State×ℕ => z.1.1.2.1.1) :=
    composition (composition (composition (composition first first) second) first) first
  let c : Realizer (fun z : State×ℕ => z.1.1.2.1.2.1) :=
    composition (composition (composition (composition (composition first first) second) first) second) first
  let demand : Realizer (fun z : State×ℕ => z.1.1.2.2) :=
    composition (composition (composition first first) second) second
  exact pair (pair k (pair (pair dw (pair c second)) demand)) (composition first second)
def ratioPrefixRealizer : Realizer ratioPrefix :=
  composition (f := fun z : Input => (z.2.2,ratioBankWidth z.1))
    (g := fun p : List Bool×ℕ => p.1.take p.2)
    (pair (composition second second)
      (composition (f := fun z : Input => z.1) (g := ratioBankWidth) first ratioBankWidthRealizer)) takeFast
def ratioRowsRealizer : Realizer ratioRows :=
  composition (f := fun z : Input => (ratioBlockWidth z.1,ratioPrefix z)) (g := completeWordRows)
    (pair (composition (f := fun z : Input => z.1) (g := ratioBlockWidth)
      first ratioBlockWidthRealizer) ratioPrefixRealizer) completeWordRowsRealizer
def ratioChunkRealizer : Realizer ratioChunk :=
  composition (f := fun z : Input×ℕ => ((ratioBlockWidth z.1.1,ratioPrefix z.1),z.2))
    (g := wordChunk)
    (pair (pair
      (composition (f := fun z : Input×ℕ => z.1.1) (g := ratioBlockWidth)
        (composition first first) ratioBlockWidthRealizer)
      (composition (f := fun z : Input×ℕ => z.1) (g := ratioPrefix) first ratioPrefixRealizer))
      second) wordChunkRealizer
def ratioStateRealizer : Realizer ratioState :=
  composition (f := fun z : Input×ℕ => (z.1.1.1,z.2)) (g := phase)
    (pair (composition (composition first first) first) second) phaseRealizer
def ratioWordsRealizer : Realizer ratioWords :=
  composition (f := fun z : Input×ℕ => (ratioWidth z.1.1,ratioChunk z)) (g := wordChunks)
    (pair (composition (f := fun z : Input×ℕ => z.1.1) (g := ratioWidth)
      (composition first first) ratioWidthRealizer) ratioChunkRealizer) wordChunksRealizer
def ratioBlockRealizer : Realizer ratioBlock :=
  composition (f := fun z : Input×ℕ => (ratioState z,ratioWords z))
    (g := fun z : State×List (List Bool) => z.2.map (fun bits => (z.1,bits)))
    (pair ratioStateRealizer ratioWordsRealizer) (mapWith identity)
def ratioBlocksRealizer : Realizer ratioBlocks :=
  composition (pair identity ratioRowsRealizer) (mapWith ratioBlockRealizer)
def correctionTailRealizer : Realizer correctionTail :=
  composition (f := fun z : Input => (z.2.2,ratioBankWidth z.1))
    (g := fun p : List Bool×ℕ => p.1.drop p.2)
    (pair (composition second second)
      (composition (f := fun z : Input => z.1) (g := ratioBankWidth) first ratioBankWidthRealizer)) dropFast
def correctionWordsRealizer : Realizer correctionWords := by
  let chunks : Realizer (fun z : Input => wordChunks (correctionWidth z.1,correctionTail z)) :=
    composition (f := fun z : Input => (correctionWidth z.1,correctionTail z)) (g := wordChunks)
      (pair (composition (f := fun z : Input => z.1) (g := correctionWidth)
        first correctionWidthRealizer) correctionTailRealizer) wordChunksRealizer
  exact composition (f := fun z : Input =>
    (wordChunks (correctionWidth z.1,correctionTail z),z.1.2.1.2))
    (g := fun p : List (List Bool)×ℕ => p.1.take p.2)
    (pair chunks (composition (composition (composition first second) first) second)) takeFast
def terminalStateRealizer : Realizer terminalState :=
  composition (f := fun z : Input => (z.1.1,z.1.2.1.1)) (g := phase)
    (pair (composition first first)
      (composition (composition (composition first second) first) first)) phaseRealizer
def correctionSampleRealizer : Realizer correctionSample := by
  let tw : Realizer (fun z : Input×List Bool => correctionWalkWidth z.1.1) :=
    composition (f := fun z : Input×List Bool => z.1.1) (g := correctionWalkWidth)
      (composition first first) correctionWalkWidthRealizer
  let args : Realizer (fun z : Input×List Bool => (z.2,correctionWalkWidth z.1.1)) := pair second tw
  let terminal : Realizer (fun z : Input×List Bool => terminalState z.1) :=
    composition (f := fun z : Input×List Bool => z.1) (g := terminalState) first terminalStateRealizer
  exact pair
    (pair terminal (composition (composition (composition (composition first first) second) second) second))
    (pair (composition (composition first second) first)
      (pair (composition args takeFast) (composition args dropFast)))
def correctionBlockRealizer : Realizer correctionBlock :=
  composition (pair identity correctionWordsRealizer) (mapWith correctionSampleRealizer)
def prepareRealizer : Realizer prepare :=
  pair (pair (composition (f := fun z : Input => z.1) (g := assignmentCount)
    first assignmentCountRealizer) ratioBlocksRealizer) correctionBlockRealizer

attribute [local irreducible] prepare

def outputRealizer : Realizer output :=
  composition (f := prepare) (g := RootedEstimatorBlockProgram.output)
    prepareRealizer RootedEstimatorBlockProgram.outputRealizer

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open scoped Classical
end ContingencyTables.RootedEstimatorWordProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorMedianProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing independent complete estimators and their rational median -/

namespace ContingencyTables.RootedEstimatorMedianProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
open RootedEstimatorLayoutProgram

def wordsRealizer : Realizer words := by
  let chunks : Realizer (fun z : Input => wordChunks (wordWidth z.1.1,z.2.2)) :=
    composition (f := fun z : Input => (wordWidth z.1.1,z.2.2)) (g := wordChunks)
      (pair (composition (f := fun z : Input => z.1.1) (g := wordWidth)
        (composition first first) wordWidthRealizer) (composition second second)) wordChunksRealizer
  exact composition (f := fun z : Input => (wordChunks (wordWidth z.1.1,z.2.2),z.1.2))
    (g := fun p : List (List Bool)×ℕ => p.1.take p.2)
    (pair chunks (composition first second)) takeFast
def sampleRealizer : Realizer sample :=
  composition (f := fun z : Input×List Bool => (z.1.1.1,(z.1.2.1,z.2)))
    (g := RootedEstimatorWordProgram.output)
    (pair (composition (composition first first) first)
      (pair (composition (composition first second) first) second))
    RootedEstimatorWordProgram.outputRealizer
def samplesRealizer : Realizer samples :=
  composition (pair identity wordsRealizer) (mapWith sampleRealizer)

attribute [local irreducible] samples

def outputRealizer : Realizer output :=
  composition (f := samples) (g := MedianFractionProgram.median)
    samplesRealizer MedianFractionProgram.medianRealizer

open GridBoundary CommonBasesFPRAS
open scoped Classical

end ContingencyTables.RootedEstimatorMedianProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedWeightOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual labelled-weight oracle used by the outer chain -/

namespace ContingencyTables.RootedWeightOracle

open CompanionFactorialApplication CompanionOracleDensity GridBoundary LabelledFactorial TwoLiftStates
open CommonBasesFPRAS
open CompanionWeightOracle
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def evaluate (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (K : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (j : ℕ) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (S : Set (Labels A×Bool))
    (bits : WeightWord A C K j xi) : ℚ :=
  RootedOracleDensity.medianEstimate A R C (profile A S) K hK hW j xi xi v bits*factorialRatio A S

end

end ContingencyTables.RootedWeightOracle

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedLabelWeightProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed weight oracle at a current paired state

The immutable schedule and graph are shared. Each call reconstructs the
two small-cell views from its actual state, runs the independent median
estimator, and multiplies by the exact factorial ratio.
-/

namespace ContingencyTables.RootedLabelWeightProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open RootedEstimatorLayoutProgram

def replaceStateRealizer : Realizer replaceState := by
  let k : Realizer (fun z : RootedOracleWalkProgram.State × List ℕ => z.1.1.1) :=
    composition (composition first first) first
  let parameters : Realizer (fun z : RootedOracleWalkProgram.State × List ℕ => z.1.1.2.1) :=
    composition (composition (composition first first) second) first
  let demands : Realizer (fun z : RootedOracleWalkProgram.State × List ℕ =>
      PairedDemandProgram.output (z.1.1.2.2,z.2)) :=
    composition (f := fun z : RootedOracleWalkProgram.State × List ℕ => (z.1.1.2.2,z.2))
      (g := PairedDemandProgram.output)
      (pair (composition (composition (composition first first) second) second) second)
      PairedDemandProgram.outputRealizer
  exact pair (pair k (pair parameters demands)) (composition first second)
def contextRealizer : Realizer context :=
  pair (composition (f := stateInput) (g := replaceState) stateInputRealizer replaceStateRealizer)
    (composition (composition (composition first first) first) second)
def medianInputRealizer : Realizer medianInput :=
  pair (pair contextRealizer (composition (composition first first) second))
    (pair (composition first second) (composition second second))

attribute [local irreducible] medianInput factorialInput

def medianResultRealizer : Realizer medianResult :=
  composition (f := medianInput) (g := RootedEstimatorMedianProgram.output)
    medianInputRealizer RootedEstimatorMedianProgram.outputRealizer

attribute [local irreducible] medianResult factorialResult

def outputRealizer : Realizer output :=
  composition (f := fun z : Input => (medianResult z,factorialResult z)) (g := TreeFraction.mul)
    (pair medianResultRealizer factorialResultRealizer) TreeFraction.mulRealizer
end ContingencyTables.RootedLabelWeightProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPhaseWords
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fresh selected-root oracle words and actual rational phase updates -/

namespace ContingencyTables.RootedPhaseWords

open CompanionFactorialApplication CompanionOracleDensity RootedWeightOracle CompanionRationalUpdates
open CommonBasesFPRAS GridBoundary FirstSuccess FairBits TwoLiftStates
open CompanionPhaseWords (phaseBits phaseWordEquiv Stored)
open CompanionWeightOracle (WeightWord)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

def observedTerm (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (S : Set (Labels A×Bool))
    (bits : WeightWord A C K j xi × WeightWord A C K (j+1) xi) : ℚ :=
  if PlainState pairs S then
    evaluate A R C K hK hW (j+1) xi v S bits.2/evaluate A R C K hK hW j xi v S bits.1
  else 0

def observedRatio (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (states : Fin N → Set (Labels A×Bool))
    (bits : Fin (phaseBits A C K j N xi) → Bool) : ℚ :=
  (∑ i,observedTerm A R C K j hK hW xi v (states i) (phaseWordEquiv A C K j N xi bits i))/
    plainCount A (List.ofFn states)

def update (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (old : Stored A)
    (states : Fin N → Set (Labels A×Bool))
    (bits : Fin (phaseBits A C K j N xi) → Bool) : Option (Stored A) :=
  if CountsPositive A (List.ofFn states) then
    some ⟨rationalLearn pairs old.multiplier (List.ofFn states),
      old.estimate*observedRatio A R C K j N hK hW xi v states bits⟩
  else none

end
end ContingencyTables.RootedPhaseWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleAcceptance
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual selected-root weight calls control the Metropolis decision -/

namespace ContingencyTables.RootedOracleAcceptance

open CompanionFactorialApplication CompanionOracleDensity RootedWeightOracle CompanionRationalUpdates
open RootedPhaseWords CommonBasesFPRAS GridBoundary FairBits TwoLiftStates
open CompanionWeightOracle (WeightWord)
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def evaluatedWeight (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S : Set (Labels A×Bool)) (bits : WeightWord A C K j xi) : ℚ :=
  rationalMultiplier pairs w S*evaluate A R C K hK hW j xi v S bits

def acceptance (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S T : Set (Labels A×Bool))
    (bits : WeightWord A C K j xi × WeightWord A C K j xi) : ℚ :=
  min 1 (evaluatedWeight A R C K j hK hW xi v w T bits.2/
    evaluatedWeight A R C K j hK hW xi v w S bits.1)

end
end ContingencyTables.RootedOracleAcceptance

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionEvaluatedWeightProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed multiplier times labelled weight

Both factors are computed from the supplied current state. The matrix
lookup and the oracle consume no hidden finite-state enumeration.
-/

namespace ContingencyTables.CompanionEvaluatedWeightProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open CompanionMultiplierMatrixProgram

attribute [local irreducible] weightInput RootedLabelWeightProgram.output

def weightRealizer : Realizer weight :=
  composition (f := weightInput) (g := RootedLabelWeightProgram.output)
    weightInputRealizer RootedLabelWeightProgram.outputRealizer

attribute [local irreducible] multiplier weight

def outputRealizer : Realizer output :=
  composition (f := fun z : Input => (multiplier z,weight z)) (g := TreeFraction.mul)
    (pair multiplierRealizer weightRealizer) TreeFraction.mulRealizer

attribute [local irreducible] output

noncomputable section
open CompanionRationalUpdates
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal GridBoundary CompanionOracleDensity CommonBasesFPRAS TwoLiftStates
open FiniteObservableTransport
open scoped Classical
variable {m n : ℕ}

abbrev LabelIndex (A : Instance (Fin m) (Fin n)) :=
  Fin (CanonicalInitialEncoding.copyOrder (capacities A)).length

def sourceWeights (A : Instance (Fin m) (Fin n))
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction) (a b : Pair A) : ℚ :=
  TreeFraction.val (w ((pairLabels A).symm a.1.1) ((pairLabels A).symm b.1.1))

end
end ContingencyTables.CompanionEvaluatedWeightProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FractionMetropolisProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Clipped rational Metropolis acceptance as a binary program -/

namespace ContingencyTables.FractionMetropolisProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

def ratioRealizer : Realizer ratio :=
  composition (f := fun z : Input => (z.1.2,z.1.1)) (g := TreeFraction.div)
    (pair (composition first second) (composition first first)) TreeFraction.divRealizer
def belowOneRealizer : Realizer belowOne :=
  composition (f := fun z : Input => (ratio z,(1,1))) (g := TreeFraction.less)
    (pair ratioRealizer (constant (1,1))) TreeFraction.lessRealizer
def probabilityRealizer : Realizer probability := choose belowOneRealizer ratioRealizer (constant (1,1))

attribute [local irreducible] probability

def acceptRealizer : Realizer accept :=
  composition (f := fun z : Input => (probability z,z.2)) (g := FractionAcceptanceProgram.acceptCode)
    (pair probabilityRealizer second) FractionAcceptanceProgram.acceptCodeRealizer

end ContingencyTables.FractionMetropolisProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionMetropolisProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One physical companion-chain step with independent word fields

The proposed state is computed by the quadratic arithmetic candidate
list. Two disjoint words evaluate the current and candidate states, and
a third field supplies the rational acceptance coin.
-/

namespace ContingencyTables.CompanionMetropolisProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

def proposedRealizer : Realizer proposed :=
  composition (f := fun z : Input => (z.1.2,z.2.2.1))
    (g := CompanionComputedProposal.proposalProgram)
    (pair (composition first second) (composition (composition second second) first))
    CompanionComputedProposal.proposalProgramRealizer
def defaultCodeRealizer : Realizer defaultCode :=
  (optionCases identity second).recode id defaultCode (fun _ => rfl)
    (by rintro ⟨d,o⟩; cases o <;> rfl)
def candidateRealizer : Realizer candidate :=
  composition (f := fun z : Input => (z.1.2,proposed z))
    (g := defaultCode) (pair (composition first second) proposedRealizer) defaultCodeRealizer

attribute [local irreducible] candidate

def currentInputRealizer : Realizer currentInput :=
  pair first (composition (composition (composition (composition second second) second) first) first)
def targetInputRealizer : Realizer targetInput :=
  pair (pair (composition first first) candidateRealizer)
    (composition (composition (composition (composition second second) second) first) second)

attribute [local irreducible] currentInput targetInput CompanionEvaluatedWeightProgram.output

def currentValueRealizer : Realizer currentValue :=
  composition (f := currentInput) (g := CompanionEvaluatedWeightProgram.output)
    currentInputRealizer CompanionEvaluatedWeightProgram.outputRealizer
def targetValueRealizer : Realizer targetValue :=
  composition (f := targetInput) (g := CompanionEvaluatedWeightProgram.output)
    targetInputRealizer CompanionEvaluatedWeightProgram.outputRealizer

attribute [local irreducible] currentValue targetValue

def acceptanceInputRealizer : Realizer acceptanceInput :=
  pair (pair currentValueRealizer targetValueRealizer)
    (composition (composition (composition second second) second) second)
def acceptedRealizer : Realizer accepted :=
  composition (f := acceptanceInput) (g := FractionMetropolisProgram.accept)
    acceptanceInputRealizer FractionMetropolisProgram.acceptRealizer

attribute [local irreducible] accepted

def outputRealizer : Realizer output :=
  choose (composition second first) (composition first second)
    (choose acceptedRealizer candidateRealizer (composition first second))

end ContingencyTables.CompanionMetropolisProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionMetropolisWordProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded slicing of one flat companion transition word -/

namespace ContingencyTables.CompanionMetropolisWordProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

def proposalWidthRealizer : Realizer proposalWidth := by
  let p : Realizer (fun z : Input => z.1.2.length/2) :=
    composition (f := fun z : Input => (z.1.2.length,2))
      (g := fun ab : ℕ × ℕ => ab.1/ab.2)
      (pair (composition (composition first second) listLength) (constant 2)) quotient
  exact composition (f := fun z : Input => (z.1.2.length/2)^2) (g := Nat.clog 2)
    ((composition (pair p p) multiply).congr (fun z => (pow_two _).symm)) ceilLogTwoRealizer
def contextRealizer : Realizer context :=
  composition (composition (composition (composition (composition first first) first) first) first) first
def queryWidthRealizer : Realizer queryWidth :=
  composition (f := fun z : Input =>
    (z.1.1.1.1.1.2,RootedEstimatorLayoutProgram.wordWidth (context z)))
    (g := fun ab : ℕ × ℕ => ab.1*ab.2)
    (pair (composition (composition (composition (composition (composition first first) first) first) first) second)
      (composition (f := context) (g := RootedEstimatorLayoutProgram.wordWidth)
        contextRealizer RootedEstimatorLayoutProgram.wordWidthRealizer)) multiply

attribute [local irreducible] context queryWidth proposalWidth

def firstOffsetRealizer : Realizer firstOffset :=
  composition (f := fun z : Input => (1,proposalWidth z)) (g := fun p : ℕ × ℕ => p.1+p.2)
    (pair (constant 1) proposalWidthRealizer) TreeTyped.add
attribute [local irreducible] firstOffset

def secondOffsetRealizer : Realizer secondOffset :=
  composition (f := fun z : Input => (firstOffset z,queryWidth z)) (g := fun p : ℕ × ℕ => p.1+p.2)
    (pair firstOffsetRealizer queryWidthRealizer) TreeTyped.add
attribute [local irreducible] secondOffset

def coinOffsetRealizer : Realizer coinOffset :=
  composition (f := fun z : Input => (secondOffset z,queryWidth z)) (g := fun p : ℕ × ℕ => p.1+p.2)
    (pair secondOffsetRealizer queryWidthRealizer) TreeTyped.add
def sliceRealizer {start count : Input → ℕ}
    (S : Realizer start) (C : Realizer count) : Realizer (slice start count) :=
  composition (pair (composition (pair second S) dropFast) C) takeFast
def fieldsRealizer : Realizer fields :=
  pair (composition (pair second (constant 0)) (getDFast false))
    (pair (sliceRealizer (constant 1) proposalWidthRealizer)
      (pair (pair (sliceRealizer firstOffsetRealizer queryWidthRealizer)
        (sliceRealizer secondOffsetRealizer queryWidthRealizer))
        (sliceRealizer coinOffsetRealizer (composition (composition first first) second))))
def stepInputRealizer : Realizer stepInput :=
  pair (pair (composition (composition first first) first) (composition first second)) fieldsRealizer

attribute [local irreducible] stepInput

def outputRealizer : Realizer output :=
  composition (f := stepInput) (g := CompanionMetropolisProgram.output)
    stepInputRealizer CompanionMetropolisProgram.outputRealizer

end ContingencyTables.CompanionMetropolisWordProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BoundedProfileWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial loop for the encoded small-profile walk -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

def capViewRealizer : Realizer capView :=
  composition (pair (composition first second)
    (composition (pair second (composition first first)) takeFast))
    (mapWith (composition (pair second first) minimum))

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionBoundedWalkProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial iteration of the physical companion transition

Clipping is redundant on the encoded binary chain states. It gives a
uniform bound on malformed inputs, so repeated calls remain polynomial.
-/

namespace ContingencyTables.CompanionBoundedWalkProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

def candidateRealizer : Realizer candidate :=
  composition (f := transitionInput) (g := CompanionMetropolisWordProgram.output)
    transitionInputRealizer CompanionMetropolisWordProgram.outputRealizer

attribute [local irreducible] candidate

def nextRealizer : Realizer next :=
  composition (f := fun z : List Bool × State => ((bound z,1),candidate z))
    (g := ProfilePrograms.capView) (pair (pair boundRealizer (constant 1)) candidateRealizer)
    ProfilePrograms.capViewRealizer
def advanceRealizer : Realizer advance := pair (composition second first) nextRealizer

def recordAdvance (z : List Bool × RecordState) : RecordState :=
  let nextState := advance (z.1,z.2.1)
  (nextState,nextState.2::z.2.2)
def recordAdvanceRealizer : Realizer recordAdvance := by
  let nxt : Realizer (fun z : List Bool × RecordState => advance (z.1,z.2.1)) :=
    composition (f := fun z : List Bool × RecordState => (z.1,z.2.1)) (g := advance)
      (pair first (composition second first)) advanceRealizer
  exact pair nxt (composition (pair (composition nxt second) (composition second second)) listCons)

def recordWalk (z : RecordState × List (List Bool)) : RecordState :=
  z.2.foldl (fun state bits => recordAdvance (bits,state)) z.1
def recordWalkRealizer : Realizer recordWalk :=
  composition (pair second first) (fold recordAdvanceRealizer)

def initialRecord (state : State) : RecordState := (state,[state.2])
def initialRecordRealizer : Realizer initialRecord :=
  pair identity (composition (pair second (constant ([] : List (List ℕ)))) listCons)

def history (z : State × List (List Bool)) : List (List ℕ) :=
  (recordWalk (initialRecord z.1,z.2)).2.reverse
def historyRealizer : Realizer history :=
  composition (f := fun z : State × List (List Bool) => (initialRecord z.1,z.2))
    (g := fun z : RecordState × List (List Bool) => (recordWalk z).2.reverse)
    (pair (composition first initialRecordRealizer) second)
    (composition (composition recordWalkRealizer second) reverse)

end ContingencyTables.CompanionBoundedWalkProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionMetropolisLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual computed proposal and two oracle calls have the phase law -/

namespace ContingencyTables.CompanionMetropolisProgram

open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionBooleanPhase (State)
open CompanionArithmeticProposal CompanionOrderedProposal CompanionOracleDensity CompanionWeightOracle
open CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram CommonBasesFPRAS
open FiniteObservableTransport TwoLiftStates GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

abbrev Fields (A : Instance (Fin m) (Fin n)) (C K j k : ℕ) (xi : ℚ) :=
  (Fin 1 → Bool) × ((Fin (CompanionBooleanPhase.proposalBits A) → Bool) ×
    ((WeightWord A C K j xi × WeightWord A C K j xi) × (Fin k → Bool)))

def programInput (A : Instance (Fin m) (Fin n)) (C K j k : ℕ) (xi : ℚ)
    (cfg : RootedLabelWeightProgram.Config)
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S : State A) (b : Fields A C K j k xi) : Input :=
  (((cfg,matrixCode w),encodeSet (coordinateOrder A) S.val),
    (b.1 0,(List.ofFn b.2.1,((List.ofFn b.2.2.1.1,List.ofFn b.2.2.1.2),List.ofFn b.2.2.2))))

def codeAccept (A : Instance (Fin m) (Fin n)) (C K j k : ℕ) (xi : ℚ)
    (cfg : RootedLabelWeightProgram.Config)
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S T : State A)
    (b : (WeightWord A C K j xi × WeightWord A C K j xi) × (Fin k → Bool)) : Bool :=
  FractionMetropolisProgram.accept
    ((CompanionEvaluatedWeightProgram.output (((cfg,matrixCode w),encodeSet (coordinateOrder A) S.val),List.ofFn b.1.1),
      CompanionEvaluatedWeightProgram.output (((cfg,matrixCode w),encodeSet (coordinateOrder A) T.val),List.ofFn b.1.2)),
      List.ofFn b.2)

end
end ContingencyTables.CompanionMetropolisProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionMetropolisWordSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The flat physical transition has the proved phase-step law -/

namespace ContingencyTables.CompanionMetropolisWordProgram

open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionOracleDensity CompanionWeightOracle
open CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram CommonBasesFPRAS
open CompanionBooleanPhase (State)
open FiniteObservableTransport TwoLiftStates GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

def packed (frame : CompanionMetropolisProgram.Frame) (k : ℕ) (code : List ℕ) (bits : List Bool) : Input :=
  (((frame,k),code),bits)

end
end ContingencyTables.CompanionMetropolisWordProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionBoundedWalkSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded physical recorder preserves the complete phase history -/

namespace ContingencyTables.CompanionBoundedWalkProgram

open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionOracleDensity CompanionWeightOracle
open CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram CommonBasesFPRAS
open CompanionBooleanPhase (State)
open FiniteObservableTransport TwoLiftStates GridBoundary
open scoped Classical

def codeStep (fixed : Fixed) (code : List ℕ) (bits : List Bool) : List ℕ :=
  next (bits,(fixed,code))

end ContingencyTables.CompanionBoundedWalkProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseFinishProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the observed ratio and learned phase update

The supplied pairs contain the current and next weight queries for every
observed state. Only plain states contribute to the ratio. The same actual
trajectory supplies the plain/defect counts and the abort test.
-/
namespace ContingencyTables.CompanionPhaseFinishProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
open CompanionTraceProgram CompanionMultiplierMatrixProgram CompanionPhaseCounts

def termRealizer : Realizer term :=
  choose (composition (f := fun z : TermInput => z.1) (g := CompanionTraceProgram.pairedPlainTest)
      first CompanionTraceProgram.pairedPlainTestRealizer)
    (composition (f := fun z : TermInput => (z.2.2,z.2.1)) (g := TreeFraction.div)
      (pair (composition second second) (composition second first)) TreeFraction.divRealizer)
    (constant (0,1))
def trajectoryRealizer : Realizer trajectory := composition (composition first first) first
def indicesRealizer : Realizer indices :=
  composition (composition (composition trajectoryRealizer second) listLength) range
def termInputRealizer : Realizer termInput :=
  pair (pair (composition (composition (f := fun z : Input×ℕ => z.1) (g := trajectory) first trajectoryRealizer) first)
    (composition (pair (composition (composition (f := fun z : Input×ℕ => z.1) (g := trajectory) first trajectoryRealizer) second) second) (getDFast [])))
    (composition (pair (composition first second) second) (getDFast ((0,1),(0,1))))
def indexedTermRealizer : Realizer indexedTerm :=
  composition (f := termInput) (g := term) termInputRealizer termRealizer
def termsRealizer : Realizer terms := composition (pair identity indicesRealizer) (mapWith indexedTermRealizer)

attribute [local irreducible] trajectory terms

def totalRealizer : Realizer total :=
  composition (f := terms) (g := TreeFraction.sum) termsRealizer TreeFraction.sumRealizer
def countRealizer : Realizer count :=
  pair (composition (f := trajectory) (g := plainCountCode) trajectoryRealizer plainCountRealizer) (constant 1)
def ratioRealizer : Realizer ratio :=
  composition (f := fun z : Input => (total z,count z)) (g := TreeFraction.div)
    (pair totalRealizer countRealizer) TreeFraction.divRealizer

attribute [local irreducible] ratio

def estimateRealizer : Realizer estimate :=
  composition (f := fun z : Input => (z.1.2,ratio z)) (g := TreeFraction.mul)
    (pair (composition first second) ratioRealizer) TreeFraction.mulRealizer
def nextRealizer : Realizer next :=
  pair (composition (f := fun z : Input => z.1.1) (g := updateMatrix)
    (composition first first) updateMatrixRealizer) estimateRealizer

attribute [local irreducible] next

def outputRealizer : Realizer output :=
  choose (composition (f := trajectory) (g := positiveCounts) trajectoryRealizer positiveCountsRealizer)
    (composition (f := next) (g := Option.some) nextRealizer TreeTyped.some) (constant none)

end ContingencyTables.CompanionPhaseFinishProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedArithmeticStep
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed coordinate proposals for the selected-root phase walk -/

namespace ContingencyTables.RootedArithmeticStep

open CommonBasesFPRAS FirstSuccess ResidualMixture FairBits GridBoundary
open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle
open RealKernelApproximation
open CompanionBooleanPhase (State stepBits proposalBits stepWordEquiv)
open CompanionArithmeticStep (RestWord)
open scoped BigOperators Classical

noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

def wordSplit (A : Instance I J) (C K j k : ℕ) (xi : ℚ) :
    (Fin (stepBits A C K j k xi) → Bool) ≃
      ((Fin (proposalBits A) → Bool)×RestWord A C K j k xi) :=
  (stepWordEquiv A C K j k xi).trans (regroup _ _ _)

def finish (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : CompanionRationalUpdates.Pair A → CompanionRationalUpdates.Pair A → ℚ)
    (S : State A) (U : Option (State A)) (rest : RestWord A C K j k xi) : State A :=
  if rest.1 0 then S else
    match U with
    | none => S
    | some T =>
        if rationalThresholdAccept k
          (RootedOracleAcceptance.acceptance A R C K j hK hW xi v w S.val T.val rest.2.1)
          rest.2.2 then T else S

def step (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : CompanionRationalUpdates.Pair A → CompanionRationalUpdates.Pair A → ℚ)
    (S : State A) (bits : Fin (stepBits A C K j k xi) → Bool) : State A :=
  let b := wordSplit A C K j k xi bits
  finish A R C K j k hK hW xi v w S (CompanionArithmeticProposal.proposal A S b.1) b.2

/-- The full recorded finite-word path therefore retains the proved
joint-history distribution, rather than merely its terminal marginal. -/
def recordedWalk (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k N n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : CompanionRationalUpdates.Pair A → CompanionRationalUpdates.Pair A → ℚ)
    (S : State A) (bits : Fin (n*stepBits A C K j k xi) → Bool) : PathState (State A) N :=
  wordWalk (fun a b => pathPut a (step A R C K j k hK hW xi v w (pathRead a) b))
    (pathInitial N S) n (oracleWalkWordEquiv n (stepBits A C K j k xi) bits)

end
end ContingencyTables.RootedArithmeticStep

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedTraceWords
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual bounded first-return words for the selected-root chain -/

namespace ContingencyTables.RootedTraceWords

open CommonBasesFPRAS CompanionFactorialApplication
open CompanionOracleDensity CompanionWeightOracle
open CompanionRationalUpdates TwoLiftStates GridBoundary FirstSuccess ResidualMixture
open CompanionBooleanPhase (State stepBits slowdown slowdown_bounds)
open CompanionPhaseTrajectory (historyPrefix)
open CompanionTraceWords (eventIndicator firstHit )
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

/-- The search consumes a fixed cap worth of disjoint words even when
the first return occurs before the last word. -/
def returnWord (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k N : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ) (S : State A)
    (bits : Fin (N*stepBits A C K j k xi) → Bool) :
    Option (PlainIndex (pairs : List (Pair A))) :=
  firstHit (plainPredicate pairs)
    (historyPrefix (RootedArithmeticStep.recordedWalk A R C K j k N N hK hW xi v w S bits)).tail

end
end ContingencyTables.RootedTraceWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPhaseExperiment
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Accuracy of the selected-root executed finite-word phase history -/

namespace ContingencyTables.RootedPhaseExperiment

open CommonBasesFPRAS FirstSuccess RealKernelApproximation
open CompanionFactorialApplication CompanionOracleDensity
open CompanionRationalUpdates
open RootedTraceWords TwoLiftStates GridBoundary
open CompanionPhaseTrajectory (historyPrefix)
open CompanionTraceWords (eventIndicator)
open CompanionBooleanPhase (State stepBits)
open scoped BigOperators Classical

noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

def observedStates (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k N : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S : State A) (bits : Fin (N*stepBits A C K j k xi) → Bool) :
    Fin (N+1) → Set (Labels A×Bool) := fun i =>
  ((RootedArithmeticStep.recordedWalk A R C K j k N N hK hW xi v w S bits).2 i).val

end
end ContingencyTables.RootedPhaseExperiment

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPhaseTrial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A complete finite-word selected-root phase trial

The trajectory and its weight queries use disjoint words. The output is
the actual guarded rational multiplier and count update.
-/

namespace ContingencyTables.RootedPhaseTrial

open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates
open CompanionOracleDensity
open RootedPhaseExperiment RootedPhaseWords
open CompanionBooleanPhase (State stepBits)
open CompanionPhaseWords (Stored phaseBits)
open CompanionTraceWords (eventIndicator)
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

abbrev TrialWords (A : Instance I J) (C K j k N : ℕ) (xi : ℚ) :=
  (Fin (N*stepBits A C K j k xi) → Bool) ×
    (Fin (phaseBits A C K j (N+1) xi) → Bool)

def trial (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (old : Stored A) (S : State A)
    (bits : TrialWords A C K j k N xi) : Option (Stored A) :=
  update A R C K j (N+1) hK hW xi v old
    (observedStates A R C K j k N hK hW xi v old.multiplier S bits.1) bits.2

end
end ContingencyTables.RootedPhaseTrial

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionReturnWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed Boolean word for repeated capped returns

The restart routine iterates the actual defaulted return experiment.
Every iteration receives a disjoint block, and an optional initial
finite-word draw receives its own disjoint block as well.
-/

namespace ContingencyTables.CompanionReturnWords

open CommonBasesFPRAS ResidualMixture FirstSuccess FairBits RealKernelApproximation
open CompanionFactorialApplication CompanionBooleanPhase CompanionOracleDensity
open CompanionCappedReturn
open CompanionRationalUpdates CompanionAnnealing TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

def returnBits (A : Instance I J) (C K j k n t : ℕ) (xi : ℚ) : ℕ :=
  t*((n+1)*stepBits A C K j k xi)

end
end ContingencyTables.CompanionReturnWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCappedReturn
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual selected-root capped returns with their literal fallback -/

namespace ContingencyTables.RootedCappedReturn

open CommonBasesFPRAS RootedTraceWords
open CompanionFactorialApplication CompanionOracleDensity CompanionRationalUpdates
open CompanionBooleanPhase (State stepBits)
open CompanionCappedReturn (returnDefault )
open CompanionTraceWords (eventIndicator firstHit)
open CompanionPhaseTrajectory (historyPrefix)
open FirstSuccess RealKernelApproximation TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

def returnWordDefault (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S : PlainIndex (pairs : List (Pair A)))
    (bits : Fin ((n+1)*stepBits A C K j k xi) → Bool) : PlainIndex (pairs : List (Pair A)) :=
  (returnWord A R C K j k (n+1) hK hW xi v w S.val bits).getD S

end
end ContingencyTables.RootedCappedReturn

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedReturnWords
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed Boolean word for selected-root repeated capped returns

The restart routine iterates the actual defaulted return experiment.
Every iteration receives a disjoint block, and an optional initial
finite-word draw receives its own disjoint block as well.
-/

namespace ContingencyTables.RootedReturnWords

open CommonBasesFPRAS ResidualMixture FirstSuccess FairBits RealKernelApproximation
open CompanionFactorialApplication CompanionOracleDensity
open CompanionBooleanPhase (stepBits)
open CompanionReturnWords (returnBits)
open RootedCappedReturn
open CompanionRationalUpdates TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

def booleanReturns (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k n t : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S : PlainIndex (pairs : List (Pair A)))
    (bits : Fin (returnBits A C K j k n t xi) → Bool) :
    PlainIndex (pairs : List (Pair A)) :=
  wordWalk (returnWordDefault A R C K j k n hK hW xi v w) S t
    (gridWordEquiv t ((n+1)*stepBits A C K j k xi) bits)

end
end ContingencyTables.RootedReturnWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedRestartWords
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual finite Boolean words for all successive restart stages -/

namespace ContingencyTables.RootedRestartWords

open CommonBasesFPRAS ResidualMixture FirstSuccess FairBits RealKernelApproximation
open CompanionFactorialApplication CompanionRationalUpdates CompanionOracleDensity
open CompanionTargetMixing (restartTime)
open CompanionReturnWords (returnBits)
open RootedReturnWords
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

def stageWidth (A : Instance I J) (C K H L k n : ℕ) (xi : ℚ) (i : ℕ) : ℕ :=
  returnBits A C K (i+1) k n (restartTime A H L) xi

def stageStep (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K H L k n : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : ℕ → Pair A → Pair A → ℚ) (i : ℕ)
    (S : PlainIndex (pairs : List (Pair A)))
    (bits : Fin (stageWidth A C K H L k n xi i) → Bool) :
    PlainIndex (pairs : List (Pair A)) :=
  booleanReturns A R C K (i+1) k n (restartTime A H L) hK hW xi v (w (i+1)) S bits

def stages (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K H L k n j : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : ℕ → Pair A → Pair A → ℚ)
    (S : PlainIndex (pairs : List (Pair A)))
    (bits : Fin (∑ i : Fin j,stageWidth A C K H L k n xi i.val) → Bool) :
    PlainIndex (pairs : List (Pair A)) :=
  varyingWalk (stageWidth A C K H L k n xi)
    (stageStep A R C K H L k n hK hW xi v w) S j
    (varyingWordEquiv (stageWidth A C K H L k n xi) j bits)

def initialStageBits (A : Instance I J) (C K H L k n h j : ℕ) (xi : ℚ) : ℕ :=
  CompanionInitialDraw.initialBits A (CompanionInitialDraw.precision A h)+
    ∑ i : Fin j,stageWidth A C K H L k n xi i.val

def initializedStages (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K H L k n h j : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : ℕ → Pair A → Pair A → ℚ)
    (bits : Fin (initialStageBits A C K H L k n h j xi) → Bool) :
    PlainIndex (pairs : List (Pair A)) :=
  let z := splitWordEquiv (CompanionInitialDraw.initialBits A (CompanionInitialDraw.precision A h))
    (∑ i : Fin j,stageWidth A C K H L k n xi i.val) bits
  stages A R C K H L k n j hK hW xi v w
    (CompanionInitialDraw.draw A (CompanionInitialDraw.precision A h) z.1) z.2

end
end ContingencyTables.RootedRestartWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedRestartTrial
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An actual initialized restart followed by the finite phase update -/

namespace ContingencyTables.RootedRestartTrial

open CommonBasesFPRAS FirstSuccess ResidualMixture RealKernelApproximation
open CompanionFactorialApplication CompanionRationalUpdates CompanionOracleDensity
open RootedPhaseTrial RootedRestartWords
open CompanionPhaseWords (Stored)
open CompanionTraceWords (eventIndicator)
open CompanionTargetMixing (restartTime)
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

abbrev Words (A : Instance I J) (C K H L j k n N h : ℕ) (xi : ℚ) :=
  (Fin (initialStageBits A C K H L k n h j xi) → Bool) × TrialWords A C K j k N xi

def run (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K H L j k n N h : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : ℕ → Pair A → Pair A → ℚ)
    (estimate : ℚ) (bits : Words A C K H L j k n N h xi) : Option (Stored A) :=
  trial A R C K j k N hK hW xi v ⟨w j,estimate⟩
    (initializedStages A R C K H L k n h j hK hW xi v w bits.1).val bits.2

end
end ContingencyTables.RootedRestartTrial

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPhaseHistory
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual adaptive phases on a common finite Boolean word space -/

namespace ContingencyTables.RootedPhaseHistory

open CommonBasesFPRAS FirstSuccess FairBits CompanionFactorialApplication
open CompanionRationalUpdates CompanionOracleDensity
open CompanionPhaseWords (Stored)
open CompanionTraceWords (eventIndicator)
open CompanionBooleanPhase (stepBits)
open RootedStoredHistory
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

def width (A : Instance I J) (s : Settings A) (j : ℕ) : ℕ :=
  RootedRestartWords.initialStageBits A s.C s.K s.H s.L s.k s.n s.h j s.xi+
    (s.N*stepBits A s.C s.K j s.k s.xi+
      CompanionPhaseWords.phaseBits A s.C s.K j (s.N+1) s.xi)

def totalWidth (A : Instance I J) (s : Settings A) : ℕ :=
  ∑ j : Fin s.H,width A s j.val

abbrev Word (A : Instance I J) (s : Settings A) := Fin (totalWidth A s) → Bool

def split (A : Instance I J) (s : Settings A) (j : ℕ) :
    (Fin (width A s j) → Bool) ≃
      RootedRestartTrial.Words A s.C s.K s.H s.L j s.k s.n s.N s.h s.xi :=
  (splitWordEquiv _ _).trans (Equiv.prodCongr (Equiv.refl _)
    (splitWordEquiv _ _))

lemma width_le (A : Instance I J) (s : Settings A) (j : ℕ) (hj : j < s.H) :
    width A s j ≤ totalWidth A s := by
  have h := value_le_sum (fun i : Fin s.H => width A s i.val) ⟨j,hj⟩
  exact h

def step (A : Instance I J) (R : RootedCompletion.Selection A.T) (s : Settings A)
    (history : List (Stored A)) (bits : Word A s) : Stored A :=
  let j := history.length
  let old := lookup A history j
  if hj : j < s.H then
    (RootedRestartTrial.run A R s.C s.K s.H s.L j s.k s.n s.N s.h s.hK s.hW s.xi s.v
      (fun i => (lookup A history i).multiplier) old.estimate
      (split A s j (prefixWord (width_le A s j hj) bits))).getD old
  else old

def decoded (A : Instance I J) (R : RootedCompletion.Selection A.T) (s : Settings A)
    (words : List (Word A s)) : List (Stored A) :=
  words.foldl (fun history bits => history++[step A R s history bits]) []

end
end ContingencyTables.RootedPhaseHistory

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionCanonicalHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical multiplier entries determine the projected phase history

The extension uses only the first label of a raw coordinate pair. Its values
away from canonical pairs need not match the original multiplier.
-/
namespace ContingencyTables.CompanionCanonicalHistory
open CompanionFactorialApplication CompanionRationalUpdates CompanionMultiplierAgreement
open CommonBasesFPRAS TwoLiftStates GridBoundary
open CompanionPhaseWords (Stored phaseBits)
open scoped Classical
noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]
variable (A : Instance I J) {p : ℕ} (g : Fin p ≃ Labels A)

def canonicalStep (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (history : List (Canonical (p := p))) (bits : RootedPhaseHistory.Word A s) : Canonical (p := p) :=
  project A g (RootedPhaseHistory.step A R s (history.map (extend A g)) bits)

end
end ContingencyTables.CompanionCanonicalHistory

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCountingWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual adaptive finite-word counting output and its accuracy -/

namespace ContingencyTables.RootedCountingWords

open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates
open CompanionOracleDensity RootedPhaseHistory RootedStoredHistory
open CompanionTerminalMass (Endpoints tableCount)
open CompanionTerminalApplication (finalPhase)
open GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

def estimate (A : Instance I J) (R : RootedCompletion.Selection A.T) (s : Settings A)
    (words : Fin s.H → Word A s) : ℚ :=
  (lookup A (decoded A R s (List.ofFn words)) s.H).estimate

def bitCount (A : Instance I J) (s : Settings A) : ℕ := s.H*totalWidth A s

def flatEstimate (A : Instance I J) (R : RootedCompletion.Selection A.T) (s : Settings A)
    (bits : Fin (bitCount A s) → Bool) : ℚ :=
  estimate A R s (gridWordEquiv s.H (totalWidth A s) bits)

end
end ContingencyTables.RootedCountingWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionCanonicalHistoryLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete source estimator factors through canonical stored entries -/
namespace ContingencyTables.CompanionCanonicalHistory
open CompanionFactorialApplication CommonBasesFPRAS GridBoundary FiniteObservableTransport
open CompanionPhaseWords (Stored)
open scoped Classical
noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]
variable (A : Instance I J) {p : ℕ} (g : Fin p ≃ Labels A)

def sourceAdvance (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (history : List (Stored A)) (bits : RootedPhaseHistory.Word A s) : List (Stored A) :=
  history++[RootedPhaseHistory.step A R s history bits]

def canonicalAdvance (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (history : List (Canonical (p := p))) (bits : RootedPhaseHistory.Word A s) : List (Canonical (p := p)) :=
  history++[canonicalStep A g R s history bits]

def canonicalDecoded (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (words : List (RootedPhaseHistory.Word A s)) : List (Canonical (p := p)) :=
  words.foldl (canonicalAdvance A g R s) []

def canonicalEstimate (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (words : Fin s.H→RootedPhaseHistory.Word A s) : ℚ :=
  (canonicalLookup A g (canonicalDecoded A g R s (List.ofFn words)) s.H).2

end
end ContingencyTables.CompanionCanonicalHistory

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_OffsetCountProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact binary tabulation of the bounded offset law -/

namespace ContingencyTables.OffsetCountPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

def ceilQuotientRealizer : Realizer ceilQuotient :=
  composition (pair
    (composition (pair (composition (pair first second) add) (constant 1)) subtract)
    second) quotient

end ContingencyTables.OffsetCountPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingOracleScheduleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary arithmetic for the counting oracle sample schedule -/

namespace ContingencyTables.CountingOracleScheduleProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

def ceilingRealizer : Realizer ceiling := OffsetCountPrograms.ceilQuotientRealizer
def sampleBaseRealizer : Realizer sampleBase :=
  composition (f := fun z : SampleInput => 65536*(z.1+1)) (g := natural)
    (composition (f := fun z : SampleInput => (65536,z.1+1))
      (g := fun p : ℕ×ℕ => p.1*p.2)
      (pair (constant 65536) (composition first successor)) multiply) naturalRealizer
def sampleDenominatorRealizer : Realizer sampleDenominator :=
  composition (f := fun z : SampleInput => (z.2.2,TreeFraction.mul (z.2.1,z.2.1)))
    (g := TreeFraction.mul)
    (pair (composition second second)
      (composition (f := fun z : SampleInput => (z.2.1,z.2.1)) (g := TreeFraction.mul)
        (pair (composition second first) (composition second first)) TreeFraction.mulRealizer))
    TreeFraction.mulRealizer
def sampleRatioRealizer : Realizer sampleRatio :=
  composition (f := fun z : SampleInput => (sampleBase z,sampleDenominator z))
    (g := TreeFraction.div) (pair sampleBaseRealizer sampleDenominatorRealizer) TreeFraction.divRealizer
def sampleCountRealizer : Realizer sampleCount :=
  composition (f := sampleRatio) (g := ceiling) sampleRatioRealizer ceilingRealizer
def offsetRatioRealizer : Realizer offsetRatio :=
  composition (f := fun z : OffsetInput => (offsetBase z,z.2)) (g := TreeFraction.div)
    (pair offsetBaseRealizer second) TreeFraction.divRealizer
def offsetAccuracyRealizer : Realizer offsetAccuracy :=
  composition (f := offsetRatio) (g := ceiling) offsetRatioRealizer ceilingRealizer
def timeExtraRealizer : Realizer timeExtra :=
  composition (f := fun z : TimeInput => (timeNumerator z,z.2)) (g := TreeFraction.div)
    (pair timeNumeratorRealizer second) TreeFraction.divRealizer
def timeTotalRealizer : Realizer timeTotal :=
  composition (f := fun z : TimeInput => (timeBase z,timeExtra z)) (g := TreeFraction.add)
    (pair timeBaseRealizer timeExtraRealizer) TreeFraction.addRealizer
def oracleTimeRealizer : Realizer oracleTime :=
  composition (f := timeTotal) (g := ceiling) timeTotalRealizer ceilingRealizer

end ContingencyTables.CountingOracleScheduleProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ScalarScheduleProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed arithmetic circuits for the scalar counting schedules

These circuits only read a fixed finite list and perform binary addition
and multiplication. Their syntax describes the fixed program, not a
numeric loop selected by the input.
-/

namespace ContingencyTables.ScalarScheduleProgram
open MatchingFPRAS.TreeTyped

def Expr.realizer : (e : Expr) → Realizer e.eval
  | .input i => composition (pair identity (constant i)) (getDFast 0)
  | .number n => constant n
  | .plus a b => composition (pair a.realizer b.realizer) add
  | .times a b => composition (pair a.realizer b.realizer) multiply

def vectorRealizer : (es : List Expr) → Realizer (vector es)
  | [] => constant []
  | e::es => composition (pair e.realizer (vectorRealizer es)) listCons


end ContingencyTables.ScalarScheduleProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPhaseParametersProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable rational controls for the adaptive counting phases -/

namespace ContingencyTables.CountingPhaseParametersProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
open CountingOracleScheduleProgram ScalarScheduleProgram

def scalarRealizer (e : Expr) : Realizer (scalar e) :=
  composition (f := fun z : Input => z.1) (g := e.eval) first e.realizer
def scalarFractionRealizer (e : Expr) : Realizer (scalarFraction e) :=
  composition (f := scalar e) (g := natural) (scalarRealizer e) naturalRealizer
def toleranceRealizer : Realizer tolerance :=
  composition (f := fun z : Input => (z.2,scalarFraction toleranceDenominator z))
    (g := TreeFraction.div) (pair second (scalarFractionRealizer toleranceDenominator))
    TreeFraction.divRealizer
def toleranceSquareRealizer : Realizer toleranceSquare :=
  composition (f := fun z : Input => (tolerance z,tolerance z)) (g := TreeFraction.mul)
    (pair toleranceRealizer toleranceRealizer) TreeFraction.mulRealizer
def observationRatioRealizer : Realizer observationRatio :=
  composition (f := fun z : Input =>
    (scalarFraction CountingPhaseScalarProgram.observationNumerator z,toleranceSquare z))
    (g := TreeFraction.div)
    (pair (scalarFractionRealizer CountingPhaseScalarProgram.observationNumerator)
      toleranceSquareRealizer) TreeFraction.divRealizer
def observationsRealizer : Realizer observations :=
  composition (f := fun z : Input => ceiling (observationRatio z)) (g := Nat.succ)
    (composition (f := observationRatio) (g := ceiling) observationRatioRealizer ceilingRealizer)
    successor
def reciprocalToleranceRealizer : Realizer reciprocalTolerance :=
  composition (f := fun z : Input => ((1,1),tolerance z)) (g := TreeFraction.div)
    (pair (constant (1,1)) toleranceRealizer) TreeFraction.divRealizer
def reciprocalCeilingRealizer : Realizer reciprocalCeiling :=
  composition (f := reciprocalTolerance) (g := ceiling) reciprocalToleranceRealizer ceilingRealizer
def precisionRealizer : Realizer precision :=
  composition (f := fun z : Input => (scalar CountingPhaseScalarProgram.precisionBase z,
    reciprocalCeiling z)) (g := fun p : ℕ×ℕ => p.1+p.2)
    (pair (scalarRealizer CountingPhaseScalarProgram.precisionBase) reciprocalCeilingRealizer) add
def noiseRealizer : Realizer noise := pair (constant 1) precisionRealizer

end ContingencyTables.CountingPhaseParametersProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleConfigProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing a phase's physical oracle configuration

Numeric schedules use binary arithmetic. The supplied reserve bounds
the two materialized precision markers; no binary natural controls an
unbounded list allocation.
-/

namespace ContingencyTables.RootedOracleConfigProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram
open CountingOracleScheduleProgram DensePrograms

def consR {f : Input → ℕ} {g : Input → List ℕ}
    (F : Realizer f) (G : Realizer g) : Realizer (fun z => f z::g z) :=
  composition (f := fun z : Input => (f z,g z)) (g := fun p : ℕ × List ℕ => p.1::p.2)
    (pair F G) listCons

def fieldsRealizer : Realizer fields := by
  let stateR : Realizer (fun z : Input => z.1.1.1) := composition (composition first first) first
  let frameR : Realizer (fun z : Input => z.1.1.1.1) := composition stateR first
  let parametersR : Realizer (fun z : Input => z.1.1.1.1.2.1) :=
    composition (composition frameR second) first
  let dR : Realizer (fun z : Input => z.1.1.1.1.2.1.1.1) :=
    composition (composition parametersR first) first
  let kR : Realizer (fun z : Input => z.1.1.1.1.1) := composition frameR first
  let hR : Realizer (fun z : Input => RootedPenaltyEvaluateProgram.height z.1.1.1.1.2.1) :=
    composition (f := fun z : Input => z.1.1.1.1.2.1)
      (g := RootedPenaltyEvaluateProgram.height) parametersR RootedPenaltyEvaluateProgram.heightRealizer
  exact consR dR (consR kR (consR hR (consR (composition first second) (constant []))))
def scalarRealizer (e : Expr) : Realizer (scalar e) :=
  composition (f := fields) (g := e.eval) fieldsRealizer e.realizer

def inner (z : Input) : Fraction :=
  TreeFraction.div (z.1.1.2,natural (scalar relativeDenominator z))
def innerRealizer : Realizer inner :=
  composition (f := fun z : Input => (z.1.1.2,natural (scalar relativeDenominator z)))
    (g := TreeFraction.div)
    (pair (composition (composition first first) second)
      (composition (f := scalar relativeDenominator) (g := natural)
        (scalarRealizer relativeDenominator) naturalRealizer)) TreeFraction.divRealizer

def correction (z : Input) : Fraction := TreeFraction.div (inner z,(256,1))
def correctionRealizer : Realizer correction :=
  composition (f := fun z : Input => (inner z,(256,1))) (g := TreeFraction.div)
    (pair innerRealizer (constant (256,1))) TreeFraction.divRealizer

def samples (z : Input) : ℕ := CountingOracleScheduleProgram.sampleCount (z.1.2,(inner z,(1,1)))
def samplesRealizer : Realizer samples :=
  composition (f := fun z : Input => (z.1.2,(inner z,(1,1))))
    (g := CountingOracleScheduleProgram.sampleCount)
    (pair (composition first second) (pair innerRealizer (constant (1,1)))) sampleCountRealizer
def timeInputRealizer : Realizer timeInput := pair (scalarRealizer mixing) (scalarRealizer allowance)

def ratioTime (z : Input) : ℕ := CountingOracleScheduleProgram.oracleTime (timeInput z,inner z)
def ratioTimeRealizer : Realizer ratioTime :=
  composition (f := fun z : Input => (timeInput z,inner z))
    (g := CountingOracleScheduleProgram.oracleTime) (pair timeInputRealizer innerRealizer) oracleTimeRealizer

def correctionTime (z : Input) : ℕ := CountingOracleScheduleProgram.oracleTime (timeInput z,correction z)
def correctionTimeRealizer : Realizer correctionTime :=
  composition (f := fun z : Input => (timeInput z,correction z))
    (g := CountingOracleScheduleProgram.oracleTime) (pair timeInputRealizer correctionRealizer) oracleTimeRealizer

def offsetAccuracy (z : Input) : ℕ := CountingOracleScheduleProgram.offsetAccuracy (scalar dim z,inner z)
def offsetAccuracyRealizer : Realizer offsetAccuracy :=
  composition (f := fun z : Input => (scalar dim z,inner z))
    (g := CountingOracleScheduleProgram.offsetAccuracy) (pair (scalarRealizer dim) innerRealizer)
    CountingOracleScheduleProgram.offsetAccuracyRealizer
def normalizedNoiseRealizer : Realizer normalizedNoise :=
  composition (composition (composition first first) second) TreeFraction.normalizeRealizer
def repeatsRealizer : Realizer repeats :=
  composition (f := fun z : Input => (64,(normalizedNoise z).2.bits.length+1))
    (g := fun p : ℕ × ℕ => p.1*p.2)
    (pair (constant 64) (composition
      (composition (composition (composition normalizedNoiseRealizer second) toBits) listLength)
      successor)) multiply

def rootDegree (z : Input) : ℕ := ceiling (TreeFraction.div ((512,1),inner z))
def rootDegreeRealizer : Realizer rootDegree :=
  composition (composition (f := fun z : Input => ((512,1),inner z)) (g := TreeFraction.div)
    (pair (constant (512,1)) innerRealizer) TreeFraction.divRealizer) ceilingRealizer

def depth (z : Input) : ℕ := Nat.clog 2 (rootDegree z)
def depthRealizer : Realizer depth := composition rootDegreeRealizer ceilLogTwoRealizer

def markers (z : Input) : List Bool × List Bool := (z.2.take (rootDegree z),z.2.take (depth z))
def markersRealizer : Realizer markers :=
  pair (composition (pair second rootDegreeRealizer) takeFast)
    (composition (pair second depthRealizer) takeFast)

def schedule (z : Input) : RootedEstimatorLayoutProgram.Schedule :=
  ((z.1.2,samples z),((ratioTime z,correctionTime z),offsetAccuracy z))
def scheduleRealizer : Realizer schedule :=
  pair (pair (composition first second) samplesRealizer)
    (pair (pair ratioTimeRealizer correctionTimeRealizer) offsetAccuracyRealizer)

def output (z : Input) : RootedLabelWeightProgram.Config :=
  (((z.1.1.1,schedule z),repeats z),markers z)
def outputRealizer : Realizer output :=
  pair (pair (pair (composition (composition first first) first) scheduleRealizer) repeatsRealizer) markersRealizer

attribute [local irreducible] output

def context (z : Input) : RootedEstimatorLayoutProgram.Context := (output z).1.1
def contextRealizer : Realizer context :=
  composition (composition (f := output) (g := fun c : RootedLabelWeightProgram.Config => c.1)
    outputRealizer first) first
attribute [local irreducible] context

def contextWidth (z : Input) : ℕ := RootedEstimatorLayoutProgram.wordWidth (context z)
def contextWidthRealizer : Realizer contextWidth :=
  composition (f := context) (g := RootedEstimatorLayoutProgram.wordWidth)
    contextRealizer RootedEstimatorLayoutProgram.wordWidthRealizer
attribute [local irreducible] contextWidth

def wordWidth (z : Input) : ℕ := repeats z*contextWidth z
def wordWidthRealizer : Realizer wordWidth :=
  composition (f := fun z : Input => (repeats z,contextWidth z))
    (g := fun p : ℕ × ℕ => p.1*p.2) (pair repeatsRealizer contextWidthRealizer) multiply

noncomputable section
open CompanionFactorialApplication GridBoundary CompanionOracleDensity
open scoped Classical
variable {m n : ℕ}

def data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) : Input :=
  (((RootedOracleWalkProgram.data A C 0 K z v,xi),j),reserve)

end
end ContingencyTables.RootedOracleConfigProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseContextProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing a phase configuration from immutable prepared data

The reserve is used only through its length. All precision-marker bits
are false, so the physical configuration is independent of the random
contents of the word that provides its bounded allocation.
-/

namespace ContingencyTables.CompanionPhaseContextProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

def noise (z : Input) : TreeFraction.Fraction := CountingPhaseParametersProgram.noise z.1.1.2
def noiseRealizer : Realizer noise :=
  composition (f := fun z : Input => z.1.1.2) (g := CountingPhaseParametersProgram.noise)
    (composition (composition first first) second) CountingPhaseParametersProgram.noiseRealizer
def precisionRealizer : Realizer precision :=
  composition (f := fun z : Input => z.1.1.2) (g := CountingPhaseParametersProgram.precision)
    (composition (composition first first) second) CountingPhaseParametersProgram.precisionRealizer
def scalarRealizer (e : ScalarScheduleProgram.Expr) : Realizer (scalar e) :=
  composition (f := fun z : Input => z.1.1.2) (g := CountingPhaseParametersProgram.scalar e)
    (composition (composition first first) second) (CountingPhaseParametersProgram.scalarRealizer e)
def falseReserveRealizer : Realizer falseReserve := composition second (map (constant false))

def configInput (z : Input) : RootedOracleConfigProgram.Input :=
  (((z.1.1.1,noise z),z.1.2),falseReserve z)
def configInputRealizer : Realizer configInput :=
  pair (pair (pair (composition (composition first first) first) noiseRealizer)
    (composition first second)) falseReserveRealizer

def config (z : Input) : RootedLabelWeightProgram.Config :=
  RootedOracleConfigProgram.output (configInput z)
def configRealizer : Realizer config :=
  composition (f := configInput) (g := RootedOracleConfigProgram.output)
    configInputRealizer RootedOracleConfigProgram.outputRealizer

noncomputable section
open CompanionFactorialApplication CompanionOracleDensity GridBoundary
open scoped Classical
variable {m n : ℕ}

def data (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (reserve : List Bool) : Input :=
  (((RootedOracleWalkProgram.data A C 0 K z v,parameters),j),reserve)

end
end ContingencyTables.CompanionPhaseContextProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRestartInitializer
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed finite initializer used before every restart experiment -/
namespace ContingencyTables.CompanionRestartInitializer
open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram DensePrograms

def forestRealizer : Realizer forest :=
  composition (composition (composition (composition first first) second) second) first
def cellInputRealizer : Realizer cellInput :=
  pair (pair (composition (f := forest) (g := fun d : RootedForestCatalog.Data => d.1.2)
      forestRealizer (composition first second))
    (composition (f := forest) (g := Prod.snd) forestRealizer second))
    (composition (f := forest) (g := fun d : RootedForestCatalog.Data => d.1.1.2)
      forestRealizer (composition (composition first first) second))
def fieldsRealizer : Realizer fields :=
  composition (f := fun z : Prepared => (z.1.1.2.1.1.1,z.2.1))
    (g := fun p : ℕ×List ℕ => p.1::p.2)
    (pair (composition (composition (composition (composition (composition first first) second) first) first) first)
      (composition second first)) listCons
def scalarRealizer (e : Expr) : Realizer (scalar e) :=
  composition (f := fields) (g := e.eval) fieldsRealizer e.realizer
def precisionRealizer : Realizer precision :=
  composition (f := fun z : Prepared =>
    (Nat.clog 2 (scalar initialBound z),scalar initialExponent z))
    (g := fun p : ℕ×ℕ => p.1+p.2)
    (pair (composition (f := scalar initialBound) (g := Nat.clog 2)
      (scalarRealizer initialBound) ceilLogTwoRealizer) (scalarRealizer initialExponent)) add
def capacitiesRealizer : Realizer capacities :=
  composition (f := cellInput) (g := CompanionCellCatalog.capacities)
    cellInputRealizer CompanionCellCatalog.capacitiesRealizer
def widthRealizer : Realizer width :=
  composition (f := fun z : Prepared => InitialChoiceProgram.widths (capacities z,precision z))
    (g := List.sum)
    (composition (f := fun z : Prepared => (capacities z,precision z)) (g := InitialChoiceProgram.widths)
      (pair capacitiesRealizer precisionRealizer) InitialChoiceProgram.widthsRealizer) listSum
def prepareRealizer : Realizer prepare :=
  pair (pair (composition (f := fun z : Input => z.1) (g := cellInput) first cellInputRealizer)
    (composition (f := fun z : Input => z.1) (g := precision) first precisionRealizer)) second

def output (z : Input) : List ℕ := CompanionComputedInitial.initialProgram (prepare z)
def outputRealizer : Realizer output :=
  composition (f := prepare) (g := CompanionComputedInitial.initialProgram)
    prepareRealizer CompanionComputedInitial.initialProgramRealizer

noncomputable section
open CompanionFactorialApplication CompanionOracleDensity GridBoundary
open CompanionComputedInitial CompanionArithmeticProposal FiniteObservableTransport
open scoped BigOperators Classical
variable {m n : ℕ}

def data (A : Instance (Fin m) (Fin n)) (C K H T N R L : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) : Prepared :=
  (RootedOracleWalkProgram.data A C 0 K z v,
    ([Fintype.card (Labels A),A.W,H,T,N,R,L],epsilon))

end
end ContingencyTables.CompanionRestartInitializer

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionCappedReturnProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary program for a total capped return

The strict return scan is followed by the supplied initial code on a
missing return. Both operations have polynomial binary realizers.
-/

namespace ContingencyTables.CompanionCappedReturnProgram

open CommonBasesFPRAS MatchingFPRAS.TreeTyped ProfilePrograms
open CompanionFactorialApplication CompanionBooleanPhase CompanionChainValidator
open CompanionCappedReturn CompanionTraceProgram CompanionTraceWords CompanionPhaseTrajectory
open CompanionArithmeticProposal CompanionRationalUpdates GridBoundary
open scoped Classical

def optionDefaultRealizer : Realizer optionDefault :=
  (optionCases identity second).recode id optionDefault (fun _ => rfl)
    (by rintro ⟨d,o⟩; cases o <;> rfl)

def totalReturnCodeRealizer : Realizer totalReturnCode :=
  composition (pair second (composition first returnCodeRealizer)) optionDefaultRealizer

end ContingencyTables.CompanionCappedReturnProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOrderedReturn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The return scan in the computed paired-coordinate order -/

namespace ContingencyTables.CompanionOrderedReturn

open MatchingFPRAS.TreeTyped CompanionBoundedWalkProgram CompanionTraceProgram
open CompanionCappedReturnProgram CompanionComputedProposal

abbrev Input := CompanionBoundedWalkProgram.State × List (List Bool)

def scanInput (z : Input) : TotalReturnInput :=
  ((PairedCatalogProgram.catalog z.1.2,history z),z.1.2)
def scanInputRealizer : Realizer scanInput :=
  pair (pair (composition (f := fun z : Input => z.1.2) (g := PairedCatalogProgram.catalog)
      (composition first second) PairedCatalogProgram.catalogRealizer)
    historyRealizer) (composition first second)

def output (z : Input) : List ℕ := totalReturnCode (scanInput z)
def outputRealizer : Realizer output :=
  composition (f := scanInput) (g := totalReturnCode) scanInputRealizer totalReturnCodeRealizer
end ContingencyTables.CompanionOrderedReturn

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionTransitionWidth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the exact companion transition word length -/

namespace ContingencyTables.CompanionTransitionWidth

open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram
open CompanionMetropolisWordProgram

def values (z : Input) : List ℕ := [proposalWidth z,queryWidth z,z.1.1.2]
attribute [local irreducible] proposalWidth queryWidth
def valuesRealizer : Realizer values := by
  let k : Realizer (fun z : Input => z.1.1.2) := composition (composition first first) second
  let ks : Realizer (fun z : Input => [z.1.1.2]) :=
    composition (f := fun z : Input => (z.1.1.2,([] : List ℕ))) (g := fun p => p.1::p.2)
      (pair k (constant [])) listCons
  let qs : Realizer (fun z : Input => [queryWidth z,z.1.1.2]) :=
    composition (f := fun z : Input => (queryWidth z,[z.1.1.2])) (g := fun p => p.1::p.2)
      (pair queryWidthRealizer ks) listCons
  exact composition (f := fun z : Input => (proposalWidth z,[queryWidth z,z.1.1.2]))
    (g := fun p => p.1::p.2) (pair proposalWidthRealizer qs) listCons
def width (z : Input) : ℕ := expression.eval (values z)
def widthRealizer : Realizer width :=
  composition (f := values) (g := expression.eval) valuesRealizer expression.realizer
end ContingencyTables.CompanionTransitionWidth

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionFlatReturnProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A bounded flat word for the actual capped-return program -/

namespace ContingencyTables.CompanionFlatReturnProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

abbrev Input := (CompanionBoundedWalkProgram.State × ℕ) × List Bool

def widthInput (z : Input) : CompanionMetropolisWordProgram.Input :=
  ((z.1.1.1.1,z.1.1.2),[])
def widthInputRealizer : Realizer widthInput :=
  pair (pair (composition (composition (composition first first) first) first)
    (composition (composition first first) second)) (constant [])

def width (z : Input) : ℕ := CompanionTransitionWidth.width (widthInput z)
def widthRealizer : Realizer width :=
  composition (f := widthInput) (g := CompanionTransitionWidth.width)
    widthInputRealizer CompanionTransitionWidth.widthRealizer

def words (z : Input) : List (List Bool) := (wordChunks (width z,z.2)).take z.1.2
def wordsRealizer : Realizer words :=
  composition (f := fun z : Input => (wordChunks (width z,z.2),z.1.2))
    (g := fun p : List (List Bool) × ℕ => p.1.take p.2)
    (pair (composition (f := fun z : Input => (width z,z.2)) (g := wordChunks)
      (pair widthRealizer second) wordChunksRealizer) (composition first second)) takeFast

def returnInput (z : Input) : CompanionOrderedReturn.Input := (z.1.1,words z)
def returnInputRealizer : Realizer returnInput :=
  pair (composition first first) wordsRealizer

def output (z : Input) : List ℕ := CompanionOrderedReturn.output (returnInput z)
def outputRealizer : Realizer output :=
  composition (f := returnInput) (g := CompanionOrderedReturn.output)
    returnInputRealizer CompanionOrderedReturn.outputRealizer

noncomputable section
open CommonBasesFPRAS CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionOracleDensity CompanionWeightOracle
open CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram FiniteObservableTransport
open CompanionTraceWords CompanionCappedReturn TwoLiftStates GridBoundary
open scoped Classical
variable {m n : ℕ}

def stateData (A : Instance (Fin m) (Fin n)) (C K j k : ℕ) (xi : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S : CompanionBooleanPhase.State A) : CompanionBoundedWalkProgram.State :=
  let code := encodeSet (coordinateOrder A) S.val
  let fixed : CompanionBoundedWalkProgram.Fixed :=
    (((RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w),k),code)
  (fixed,code)

def data (A : Instance (Fin m) (Fin n)) (C K j k N : ℕ) (xi : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S : CompanionBooleanPhase.State A) (bits : List Bool) : Input :=
  ((stateData A C K j k xi z v degree depth w S,N),bits)

end
end ContingencyTables.CompanionFlatReturnProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRepeatedReturnProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded iteration of the executed capped-return routine

The numeric repetition count only truncates chunks of the supplied
word. The stored profile is clipped to the fixed initial dimension,
which is redundant on every actual encoded state.
-/

namespace ContingencyTables.CompanionRepeatedReturnProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial DensePrograms

abbrev Fixed := CompanionBoundedWalkProgram.Fixed × ℕ
abbrev State := Fixed × List ℕ
abbrev Input := (State × ℕ) × List Bool

def returnInput (z : List Bool × State) : CompanionFlatReturnProgram.Input :=
  ((((z.2.1.1.1,z.2.2),z.2.2),z.2.1.2+1),z.1)
def returnInputRealizer : Realizer returnInput := by
  let frame : Realizer (fun z : List Bool × State => z.2.1.1.1) :=
    composition (composition (composition second first) first) first
  let current : Realizer (fun z : List Bool × State => z.2.2) := composition second second
  let cap : Realizer (fun z : List Bool × State => z.2.1.2+1) :=
    composition (f := fun z : List Bool × State => z.2.1.2) (g := Nat.succ)
      (composition (composition second first) second) successor
  exact pair (pair (pair (pair frame current) current) cap) first

def candidate (z : List Bool × State) : List ℕ := CompanionFlatReturnProgram.output (returnInput z)
def candidateRealizer : Realizer candidate :=
  composition (f := returnInput) (g := CompanionFlatReturnProgram.output)
    returnInputRealizer CompanionFlatReturnProgram.outputRealizer

def bound (z : List Bool × State) : ℕ := z.2.1.1.2.length
def boundRealizer : Realizer bound :=
  composition (composition (composition (composition second first) first) second) listLength

attribute [local irreducible] candidate

def next (z : List Bool × State) : List ℕ := ProfilePrograms.capView ((bound z,1),candidate z)
def nextRealizer : Realizer next :=
  composition (f := fun z : List Bool × State => ((bound z,1),candidate z))
    (g := ProfilePrograms.capView) (pair (pair boundRealizer (constant 1)) candidateRealizer)
    ProfilePrograms.capViewRealizer

def advance (z : List Bool × State) : State := (z.2.1,next z)
def advanceRealizer : Realizer advance := pair (composition second first) nextRealizer

def walk (z : State × List (List Bool)) : State :=
  z.2.foldl (fun state bits => advance (bits,state)) z.1
def walkRealizer : Realizer walk := composition (pair second first) (fold advanceRealizer)

def widthInput (fixed : Fixed) : CompanionMetropolisWordProgram.Input :=
  ((fixed.1.1,fixed.1.2),[])
def widthInputRealizer : Realizer widthInput :=
  pair (pair (composition first first) (composition first second)) (constant [])

def blockWidth (fixed : Fixed) : ℕ :=
  (fixed.2+1)*CompanionTransitionWidth.width (widthInput fixed)
def blockWidthRealizer : Realizer blockWidth :=
  composition (f := fun fixed : Fixed => (fixed.2+1,CompanionTransitionWidth.width (widthInput fixed)))
    (g := fun z : ℕ × ℕ => z.1*z.2)
    (pair (composition second successor)
      (composition (f := widthInput) (g := CompanionTransitionWidth.width)
        widthInputRealizer CompanionTransitionWidth.widthRealizer)) multiply

def words (z : Input) : List (List Bool) :=
  (wordChunks (blockWidth z.1.1.1,z.2)).take z.1.2
def wordsRealizer : Realizer words :=
  composition (f := fun z : Input => (wordChunks (blockWidth z.1.1.1,z.2),z.1.2))
    (g := fun z : List (List Bool) × ℕ => z.1.take z.2)
    (pair (composition (f := fun z : Input => (blockWidth z.1.1.1,z.2)) (g := wordChunks)
      (pair (composition (f := fun z : Input => z.1.1.1) (g := blockWidth)
        (composition (composition first first) first) blockWidthRealizer) second) wordChunksRealizer)
      (composition first second)) takeFast

def output (z : Input) : List ℕ := (walk (z.1.1,words z)).2
def outputRealizer : Realizer output :=
  composition (f := fun z : Input => (z.1.1,words z)) (g := fun z => (walk z).2)
    (pair (composition first first) wordsRealizer)
    (composition (f := walk) (g := Prod.snd) walkRealizer second)

end ContingencyTables.CompanionRepeatedReturnProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRestartStageProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One executed warm-restart stage

The context supplies the phase, immutable oracle metadata and deterministic
precision markers. The matrix is the stored multiplier for that phase.
-/
namespace ContingencyTables.CompanionRestartStageProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open CompanionMultiplierMatrixProgram

def contextRealizer : Realizer context := composition first first

def frame (z : Request) : CompanionMetropolisProgram.Frame × ℕ :=
  ((CompanionPhaseContextProgram.config (context z),z.1.2),
    CompanionPhaseContextProgram.precision (context z))
def frameRealizer : Realizer frame :=
  pair (pair
    (composition (f := context) (g := CompanionPhaseContextProgram.config)
      contextRealizer CompanionPhaseContextProgram.configRealizer)
    (composition first second))
    (composition (f := context) (g := CompanionPhaseContextProgram.precision)
      contextRealizer CompanionPhaseContextProgram.precisionRealizer)

def cap (z : Request) : ℕ := CompanionPhaseContextProgram.scalar (.input 5) (context z)
def capRealizer : Realizer cap :=
  composition (f := context) (g := CompanionPhaseContextProgram.scalar (.input 5))
    contextRealizer (CompanionPhaseContextProgram.scalarRealizer (.input 5))

def repetitions (z : Request) : ℕ := CompanionPhaseContextProgram.scalar (.input 3) (context z)
def repetitionsRealizer : Realizer repetitions :=
  composition (f := context) (g := CompanionPhaseContextProgram.scalar (.input 3))
    contextRealizer (CompanionPhaseContextProgram.scalarRealizer (.input 3))

attribute [local irreducible] frame cap repetitions

def fixed (z : Request) : CompanionRepeatedReturnProgram.Fixed := ((frame z,z.2),cap z)
def fixedRealizer : Realizer fixed := pair (pair frameRealizer second) capRealizer

def prepare (z : Input) : CompanionRepeatedReturnProgram.Input :=
  (((fixed z.1,z.1.2),repetitions z.1),z.2)
def prepareRealizer : Realizer prepare :=
  pair (pair (pair (composition (f := fun z : Input => z.1) (g := fixed)
    first fixedRealizer) (composition first second))
    (composition (f := fun z : Input => z.1) (g := repetitions) first repetitionsRealizer)) second

def output (z : Input) : List ℕ := CompanionRepeatedReturnProgram.output (prepare z)
def outputRealizer : Realizer output :=
  composition (f := prepare) (g := CompanionRepeatedReturnProgram.output)
    prepareRealizer CompanionRepeatedReturnProgram.outputRealizer

def width (z : Request) : ℕ :=
  repetitions z*CompanionRepeatedReturnProgram.blockWidth (fixed z)
def widthRealizer : Realizer width :=
  composition (f := fun z : Request =>
    (repetitions z,CompanionRepeatedReturnProgram.blockWidth (fixed z)))
    (g := fun z : ℕ×ℕ => z.1*z.2)
    (pair repetitionsRealizer (composition (f := fixed)
      (g := CompanionRepeatedReturnProgram.blockWidth) fixedRealizer
      CompanionRepeatedReturnProgram.blockWidthRealizer)) multiply

end ContingencyTables.CompanionRestartStageProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRestartProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed restart stages with disjoint variable-width words

The supplied stage list determines the number of iterations. The current
encoded profile is bounded by the original profile length after every stage.
-/
namespace ContingencyTables.CompanionRestartProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial DensePrograms
open CompanionMultiplierMatrixProgram

def request (z : Input × ℕ) : CompanionRestartStageProgram.Request :=
  (z.1.1.1.getD z.2 default,z.1.1.2)
def requestRealizer : Realizer request :=
  pair (composition (f := fun z : Input×ℕ => (z.1.1.1,z.2))
    (g := fun p : List Stage×ℕ => p.1.getD p.2 default)
    (pair (composition (composition first first) first) second) (getDFast default))
    (composition (composition first first) second)
def indicesRealizer : Realizer indices :=
  composition (composition (composition first first) listLength) range

def indexedWidth (z : Input×ℕ) : ℕ := CompanionRestartStageProgram.width (request z)
def indexedWidthRealizer : Realizer indexedWidth :=
  composition (f := request) (g := CompanionRestartStageProgram.width)
    requestRealizer CompanionRestartStageProgram.widthRealizer

def widths (z : Input) : List ℕ := (indices z).map (fun i => indexedWidth (z,i))
def widthsRealizer : Realizer widths :=
  composition (pair identity indicesRealizer) (mapWith indexedWidthRealizer)

def stageWord (z : Input×ℕ) : List Bool := dependentChunk ((widths z.1,z.1.2),z.2)
def stageWordRealizer : Realizer stageWord :=
  composition (f := fun z : Input×ℕ => ((widths z.1,z.1.2),z.2))
    (g := dependentChunk)
    (pair (pair (composition (f := fun z : Input×ℕ => z.1) (g := widths) first widthsRealizer)
      (composition first second)) second) dependentChunkRealizer

def stageInput (z : ℕ×State) : CompanionRestartStageProgram.Input :=
  ((z.2.1.1.1.getD z.1 default,z.2.2),stageWord (z.2.1,z.1))
def stageInputRealizer : Realizer stageInput := by
  let selected : Realizer (fun z : ℕ×State => z.2.1.1.1.getD z.1 (default : Stage)) :=
    composition (f := fun z : ℕ×State => (z.2.1.1.1,z.1))
      (g := fun p : List Stage×ℕ => p.1.getD p.2 default)
      (pair (composition (composition (composition second first) first) first) first) (getDFast default)
  exact pair (pair selected (composition second second))
    (composition (f := fun z : ℕ×State => (z.2.1,z.1)) (g := stageWord)
      (pair (composition second first) first) stageWordRealizer)

def candidate (z : ℕ×State) : List ℕ := CompanionRestartStageProgram.output (stageInput z)
def candidateRealizer : Realizer candidate :=
  composition (f := stageInput) (g := CompanionRestartStageProgram.output)
    stageInputRealizer CompanionRestartStageProgram.outputRealizer

def bound (z : ℕ×State) : ℕ := z.2.1.1.2.length
def boundRealizer : Realizer bound :=
  composition (composition (composition (composition second first) first) second) listLength

attribute [local irreducible] candidate

def next (z : ℕ×State) : List ℕ := ProfilePrograms.capView ((bound z,1),candidate z)
def nextRealizer : Realizer next :=
  composition (f := fun z : ℕ×State => ((bound z,1),candidate z)) (g := ProfilePrograms.capView)
    (pair (pair boundRealizer (constant 1)) candidateRealizer) ProfilePrograms.capViewRealizer

def advance (z : ℕ×State) : State := (z.2.1,next z)
def advanceRealizer : Realizer advance := pair (composition second first) nextRealizer

def walk (z : State×List ℕ) : State := z.2.foldl (fun state i => advance (i,state)) z.1
def walkRealizer : Realizer walk := composition (pair second first) (fold advanceRealizer)

def output (z : Input) : List ℕ := (walk ((z,z.1.2),indices z)).2
def outputRealizer : Realizer output :=
  composition (f := fun z : Input => ((z,z.1.2),indices z))
    (g := fun z : State×List ℕ => (walk z).2)
    (pair (pair identity (composition first second)) indicesRealizer)
    (composition (f := walk) (g := Prod.snd) walkRealizer second)

end ContingencyTables.CompanionRestartProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionInitializedRestartProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Initialization and all stored-multiplier restart stages

Past entries are stored in chronological order. Entry i contains the
multiplier for restart phase i+1. Initialization and restart stages take
disjoint slices of the supplied word.
-/
namespace ContingencyTables.CompanionInitializedRestartProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

def reserveRealizer : Realizer reserve := composition second (map (constant false))
def indicesRealizer : Realizer indices :=
  composition (composition (composition first second) listLength) range

def stageAt (z : Input×ℕ) : CompanionRestartProgram.Stage :=
  (((z.1.1.1,z.2+1),reserve z.1),(z.1.1.2.getD z.2 default).1)
def stageAtRealizer : Realizer stageAt := by
  let prepared : Realizer (fun z : Input×ℕ => z.1.1.1) := composition (composition first first) first
  let phase : Realizer (fun z : Input×ℕ => z.2+1) := composition second successor
  let marker : Realizer (fun z : Input×ℕ => reserve z.1) :=
    composition (f := fun z : Input×ℕ => z.1) (g := reserve) first reserveRealizer
  let stored : Realizer (fun z : Input×ℕ => z.1.1.2.getD z.2 (default : Stored)) :=
    composition (f := fun z : Input×ℕ => (z.1.1.2,z.2))
      (g := fun p : List Stored×ℕ => p.1.getD p.2 default)
      (pair (composition (composition first first) second) second) (getDFast default)
  exact pair (pair (pair prepared phase) marker) (composition (f := fun z : Input×ℕ =>
    z.1.1.2.getD z.2 (default : Stored)) (g := Prod.fst) stored first)

def stages (z : Input) : List CompanionRestartProgram.Stage :=
  (indices z).map (fun i => stageAt (z,i))
def stagesRealizer : Realizer stages := composition (pair identity indicesRealizer) (mapWith stageAtRealizer)

def initialWidth (z : Input) : ℕ := CompanionRestartInitializer.width z.1.1
def initialWidthRealizer : Realizer initialWidth :=
  composition (f := fun z : Input => z.1.1) (g := CompanionRestartInitializer.width)
    (composition first first) CompanionRestartInitializer.widthRealizer

def initialInput (z : Input) : CompanionRestartInitializer.Input :=
  (z.1.1,z.2.take (initialWidth z))
def initialInputRealizer : Realizer initialInput :=
  pair (composition first first)
    (composition (f := fun z : Input => (z.2,initialWidth z))
      (g := fun p : List Bool×ℕ => p.1.take p.2) (pair second initialWidthRealizer) takeFast)

def initialCode (z : Input) : List ℕ := CompanionRestartInitializer.output (initialInput z)
def initialCodeRealizer : Realizer initialCode :=
  composition (f := initialInput) (g := CompanionRestartInitializer.output)
    initialInputRealizer CompanionRestartInitializer.outputRealizer

attribute [local irreducible] stages initialCode initialWidth

def prepare (z : Input) : CompanionRestartProgram.Input :=
  ((stages z,initialCode z),z.2.drop (initialWidth z))
def prepareRealizer : Realizer prepare :=
  pair (pair stagesRealizer initialCodeRealizer)
    (composition (f := fun z : Input => (z.2,initialWidth z))
      (g := fun p : List Bool×ℕ => p.1.drop p.2) (pair second initialWidthRealizer) dropFast)

def output (z : Input) : List ℕ := CompanionRestartProgram.output (prepare z)
def outputRealizer : Realizer output :=
  composition (f := prepare) (g := CompanionRestartProgram.output)
    prepareRealizer CompanionRestartProgram.outputRealizer

end ContingencyTables.CompanionInitializedRestartProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRestartSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact disjoint-word semantics of the physical restart loop -/
namespace ContingencyTables.CompanionRestartProgram
open FirstSuccess FiniteObservableTransport MatchingFPRAS DensePrograms CommonBasesFPRAS
open scoped BigOperators Classical

def widthAt (base : List Stage×List ℕ) (i : ℕ) : ℕ := indexedWidth ((base,[]),i)

def detachedStep (base : List Stage×List ℕ) (i : ℕ) (code : List ℕ)
    (bits : List Bool) : List ℕ :=
  ProfilePrograms.capView ((base.2.length,1),
    CompanionRestartStageProgram.output ((base.1.getD i default,code),bits))

end ContingencyTables.CompanionRestartProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRepeatedReturnLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The physical return loop has the actual repeated-return law -/

namespace ContingencyTables.CompanionRepeatedReturnProgram

open MatchingFPRAS CommonBasesFPRAS FirstSuccess ResidualMixture
open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle
open CompanionComputedInitial CompanionComputedProposal CompanionArithmeticProposal
open CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram
open FiniteObservableTransport TwoLiftStates GridBoundary
open scoped Classical

noncomputable section
variable {m n : ℕ}

def fixedData (A : Instance (Fin m) (Fin n)) (C K j k cap : ℕ) (xi : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S₀ : Set (Labels A × Bool)) : Fixed :=
  ((((RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w),k),
    encodeSet (coordinateOrder A) S₀),cap)

def data (A : Instance (Fin m) (Fin n)) (C K j k cap t : ℕ) (xi : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S : Set (Labels A × Bool)) (bits : List Bool) : Input :=
  (((fixedData A C K j k cap xi z v degree depth w S,
    encodeSet (coordinateOrder A) S),t),bits)

def codeStep (fixed : Fixed) (code : List ℕ) (bits : List Bool) : List ℕ :=
  next (bits,(fixed,code))

end
end ContingencyTables.CompanionRepeatedReturnProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRestartStageLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed restart stage is the literal finite-word return law -/
namespace ContingencyTables.CompanionRestartStageProgram
open MatchingFPRAS CommonBasesFPRAS CompanionFactorialApplication
open CompanionOracleDensity CompanionWeightOracle CompanionComputedInitial
open CompanionComputedProposal CompanionArithmeticProposal CompanionMultiplierMatrixProgram
open CompanionEvaluatedWeightProgram
open FiniteObservableTransport TwoLiftStates GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

def oracleData (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    RootedOracleConfigProgram.Input :=
  RootedOracleConfigProgram.data A C K j (CountingPhaseParametersProgram.noise parameters)
    z v (List.replicate reserve.length false)

def degree (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) : List Bool :=
  (List.replicate reserve.length false).take
    (RootedOracleConfigProgram.rootDegree (oracleData A C K j parameters z v reserve))

def depth (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) : List Bool :=
  (List.replicate reserve.length false).take
    (RootedOracleConfigProgram.depth (oracleData A C K j parameters z v reserve))

def data (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool)
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S : Set (Labels A×Bool)) : Request :=
  ((CompanionPhaseContextProgram.data A C K j parameters z v reserve,matrixCode w),
    encodeSet (coordinateOrder A) S)

end
end ContingencyTables.CompanionRestartStageProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRestartDataLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete stored-matrix restart experiment -/
namespace ContingencyTables.CompanionRestartProgram
open MatchingFPRAS CommonBasesFPRAS FirstSuccess FiniteObservableTransport
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram
open CompanionOracleDensity CompanionWeightOracle TwoLiftStates GridBoundary
open scoped BigOperators Classical
noncomputable section
variable {m n : ℕ}

def stagesData (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction) : List Stage :=
  List.ofFn (fun i : Fin j =>
    (CompanionPhaseContextProgram.data A C K (i.val+1) parameters z v reserve,matrixCode (w (i.val+1))))

def baseData (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S : Set (Labels A×Bool)) :
    List Stage×List ℕ :=
  (stagesData A C K j parameters z v reserve w,encodeSet (coordinateOrder A) S)

def sourceWidth (A : Instance (Fin m) (Fin n)) (C K : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) (i : ℕ) : ℕ :=
  CountingPhaseParametersProgram.scalar (.input 3) parameters*
    ((CountingPhaseParametersProgram.scalar (.input 5) parameters+1)*
      CompanionBooleanPhase.stepBits A C K (i+1) (CountingPhaseParametersProgram.precision parameters)
        (TreeFraction.val (CountingPhaseParametersProgram.noise parameters)))

def sourceStep (A : Instance (Fin m) (Fin n)) (C K : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction) (i : ℕ)
    (S : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A)))
    (bits : Fin (sourceWidth A C K parameters i) → Bool) :
    PlainIndex (pairs : List (CompanionRationalUpdates.Pair A)) :=
  RootedReturnWords.booleanReturns A (RootedCompletion.rowColumn A.T) C K (i+1)
    (CountingPhaseParametersProgram.precision parameters)
    (CountingPhaseParametersProgram.scalar (.input 5) parameters)
    (CountingPhaseParametersProgram.scalar (.input 3) parameters) hK hW
    (TreeFraction.val (CountingPhaseParametersProgram.noise parameters))
    (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A (w (i+1))) S bits

end
end ContingencyTables.CompanionRestartProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRestartSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A deterministic bit allocation for initialized restart experiments -/
namespace ContingencyTables.CompanionRestartSchedule
open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram DensePrograms Polynomial

def configInput (z : StageInput) : RootedOracleConfigProgram.Input :=
  CompanionPhaseContextProgram.configInput ((z.1,z.2+1),[])
def configInputRealizer : Realizer configInput :=
  composition (f := fun z : StageInput => ((z.1,z.2+1),([] : List Bool)))
    (g := CompanionPhaseContextProgram.configInput)
    (pair (pair first (composition second successor)) (constant []))
    CompanionPhaseContextProgram.configInputRealizer

def queryWidth (z : StageInput) : ℕ := RootedOracleConfigProgram.wordWidth (configInput z)
def queryWidthRealizer : Realizer queryWidth :=
  composition (f := configInput) (g := RootedOracleConfigProgram.wordWidth)
    configInputRealizer RootedOracleConfigProgram.wordWidthRealizer
def scalarRealizer (e : Expr) : Realizer (scalar e) :=
  composition (f := fun z : StageInput => z.1.2) (g := CountingPhaseParametersProgram.scalar e)
    (composition first second) (CountingPhaseParametersProgram.scalarRealizer e)
def proposalWidthRealizer : Realizer proposalWidth :=
  composition (f := fun z : StageInput => scalar (.input 0) z*scalar (.input 0) z)
    (g := Nat.clog 2)
    (composition (f := fun z : StageInput => (scalar (.input 0) z,scalar (.input 0) z))
      (g := fun p : ℕ×ℕ => p.1*p.2) (pair (scalarRealizer (.input 0)) (scalarRealizer (.input 0))) multiply)
    ceilLogTwoRealizer
def precisionRealizer : Realizer precision :=
  composition (f := fun z : StageInput => z.1.2) (g := CountingPhaseParametersProgram.precision)
    (composition first second) CountingPhaseParametersProgram.precisionRealizer

 def consR {f : StageInput→ℕ} {g : StageInput→List ℕ}
    (F : Realizer f) (G : Realizer g) : Realizer (fun z => f z::g z) :=
  composition (f := fun z : StageInput => (f z,g z))
    (g := fun p : ℕ×List ℕ => p.1::p.2) (pair F G) listCons

def fields (z : StageInput) : List ℕ :=
  [proposalWidth z,queryWidth z,precision z,scalar (.input 3) z,scalar (.input 5) z]
def fieldsRealizer : Realizer fields :=
  consR proposalWidthRealizer (consR queryWidthRealizer (consR precisionRealizer
    (consR (scalarRealizer (.input 3)) (consR (scalarRealizer (.input 5)) (constant [])))))
def stageWidth (z : StageInput) : ℕ := expression.eval (fields z)
def stageWidthRealizer : Realizer stageWidth :=
  composition (f := fields) (g := expression.eval) fieldsRealizer expression.realizer
def indicesRealizer : Realizer indices := composition (composition second listLength) range

def indexedWidth (z : Input×ℕ) : ℕ := stageWidth (z.1.1,z.2)
def indexedWidthRealizer : Realizer indexedWidth :=
  composition (f := fun z : Input×ℕ => (z.1.1,z.2)) (g := stageWidth)
    (pair (composition first first) second) stageWidthRealizer

def restartWidth (z : Input) : ℕ := ((indices z).map (fun i => indexedWidth (z,i))).sum
def restartWidthRealizer : Realizer restartWidth :=
  composition (f := fun z : Input => (indices z).map (fun i => indexedWidth (z,i)))
    (g := List.sum) (composition (pair identity indicesRealizer) (mapWith indexedWidthRealizer)) listSum

def width (z : Input) : ℕ := CompanionRestartInitializer.width z.1+restartWidth z
def widthRealizer : Realizer width :=
  composition (f := fun z : Input => (CompanionRestartInitializer.width z.1,restartWidth z))
    (g := fun p : ℕ×ℕ => p.1+p.2)
    (pair (composition (f := fun z : Input => z.1) (g := CompanionRestartInitializer.width)
      first CompanionRestartInitializer.widthRealizer) restartWidthRealizer) add

end ContingencyTables.CompanionRestartSchedule

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionInitializedRestartSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal inputs and disjoint slices of initialized restarts -/
namespace ContingencyTables.CompanionInitializedRestartProgram
open MatchingFPRAS CommonBasesFPRAS FairBits DensePrograms
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram
open CompanionOracleDensity GridBoundary
open scoped BigOperators Classical
noncomputable section
variable {m n : ℕ}

def data (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (estimates : Fin j → TreeFraction.Fraction) (bits : List Bool) : Input :=
  ((CompanionRestartInitializer.data A C K H T N R L epsilon z v,
    List.ofFn (fun i : Fin j => (matrixCode (w (i.val+1)),estimates i))),bits)

end
end ContingencyTables.CompanionInitializedRestartProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRestartNativeLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common native bit width for all initial plain states -/
namespace ContingencyTables.CompanionRestartProgram
open MatchingFPRAS CommonBasesFPRAS FirstSuccess FiniteObservableTransport
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionEvaluatedWeightProgram
open CompanionOracleDensity TwoLiftStates GridBoundary
open scoped BigOperators Classical
noncomputable section
variable {m n : ℕ}

def sumBits (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) : ℕ :=
  ∑ i : Fin j,sourceWidth A C K parameters i.val

end
end ContingencyTables.CompanionRestartProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionInitializedRestartLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact law of the complete executed initializer and restart prefix -/
namespace ContingencyTables.CompanionInitializedRestartProgram
open MatchingFPRAS CommonBasesFPRAS FirstSuccess FairBits FiniteObservableTransport
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionEvaluatedWeightProgram
open CompanionOracleDensity TwoLiftStates GridBoundary
open scoped BigOperators Classical
noncomputable section
variable {m n : ℕ}

def parameters (A : Instance (Fin m) (Fin n)) (H T N R L : ℕ)
    (epsilon : TreeFraction.Fraction) : CountingPhaseParametersProgram.Input :=
  ([Fintype.card (Labels A),A.W,H,T,N,R,L],epsilon)

def model (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (bits : Fin (CompanionInitialDraw.initialBits A
        (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
      CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)) → Bool) :
    PlainIndex (pairs : List (CompanionRationalUpdates.Pair A)) :=
  let B := CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H)
  let widths := CompanionRestartProgram.sourceWidth A C K (parameters A H T N R L epsilon)
  let split := splitWordEquiv (CompanionInitialDraw.initialBits A B)
    (CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)) bits
  varyingWalk widths
    (CompanionRestartProgram.sourceStep A C K (parameters A H T N R L epsilon) hK hW v w)
    (CompanionInitialDraw.draw A B split.1) j (varyingWordEquiv widths j split.2)

end
end ContingencyTables.CompanionInitializedRestartProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionInitializedRestartJoint
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint restart law with the unused trajectory and query suffix -/
namespace ContingencyTables.CompanionInitializedRestartProgram
open MatchingFPRAS CommonBasesFPRAS FirstSuccess FairBits FiniteObservableTransport
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionEvaluatedWeightProgram
open CompanionOracleDensity TwoLiftStates GridBoundary
open scoped BigOperators Classical
noncomputable section
variable {m n : ℕ}

def jointModel (A : Instance (Fin m) (Fin n)) (C K H T N R L j padding : ℕ)
    (epsilon : TreeFraction.Fraction) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (bits : Fin (CompanionInitialDraw.initialBits A
      (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
      (CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)+padding)) → Bool) :
    PlainIndex (pairs : List (CompanionRationalUpdates.Pair A))×(Fin padding → Bool) :=
  let B := CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H)
  let widths := CompanionRestartProgram.sourceWidth A C K (parameters A H T N R L epsilon)
  let blocks := splitWordEquiv (CompanionInitialDraw.initialBits A B)
    (CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)+padding) bits
  let tail := splitWordEquiv (CompanionRestartProgram.sumBits A C K j
    (parameters A H T N R L epsilon)) padding blocks.2
  (varyingWalk widths
    (CompanionRestartProgram.sourceStep A C K (parameters A H T N R L epsilon) hK hW v w)
    (CompanionInitialDraw.draw A B blocks.1) j (varyingWordEquiv widths j tail.1),tail.2)


end
end ContingencyTables.CompanionInitializedRestartProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionObservationQueriesProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed current and next weight queries along a supplied trajectory -/
namespace ContingencyTables.CompanionObservationQueriesProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial DensePrograms

abbrev Config := RootedLabelWeightProgram.Config
abbrev Fraction := TreeFraction.Fraction
abbrev Input := (Config×Config)×(List (List ℕ)×List Bool)
abbrev PairInput := (Config×Config)×(List ℕ×List Bool)

def queryWidth (c : Config) : ℕ := c.1.2*RootedEstimatorLayoutProgram.wordWidth c.1.1
def queryWidthRealizer : Realizer queryWidth :=
  composition (pair (composition first second)
    (composition (f := fun c : Config => c.1.1) (g := RootedEstimatorLayoutProgram.wordWidth)
      (composition first first) RootedEstimatorLayoutProgram.wordWidthRealizer)) multiply

attribute [local irreducible] queryWidth

abbrev blockWidth (cs : Config×Config) : ℕ := queryWidth cs.1+queryWidth cs.2
def blockWidthRealizer : Realizer blockWidth :=
  composition (pair (composition (f := fun cs : Config×Config => cs.1) (g := queryWidth) first queryWidthRealizer)
    (composition (f := fun cs : Config×Config => cs.2) (g := queryWidth) second queryWidthRealizer)) add


def currentInput (z : PairInput) : RootedLabelWeightProgram.Input :=
  (z.1.1,(z.2.1,z.2.2.take (queryWidth z.1.1)))
def currentInputRealizer : Realizer currentInput :=
  pair (composition first first)
    (pair (composition second first)
      (composition (pair (composition second second)
        (composition (f := fun z : PairInput => z.1.1) (g := queryWidth)
          (composition first first) queryWidthRealizer)) takeFast))

def nextInput (z : PairInput) : RootedLabelWeightProgram.Input :=
  (z.1.2,(z.2.1,(z.2.2.drop (queryWidth z.1.1)).take (queryWidth z.1.2)))
def nextInputRealizer : Realizer nextInput :=
  pair (composition first second)
    (pair (composition second first)
      (composition (pair
        (composition (pair (composition second second)
          (composition (f := fun z : PairInput => z.1.1) (g := queryWidth)
            (composition first first) queryWidthRealizer)) dropFast)
        (composition (f := fun z : PairInput => z.1.2) (g := queryWidth)
          (composition first second) queryWidthRealizer)) takeFast))

attribute [local irreducible] currentInput nextInput RootedLabelWeightProgram.output

def queryPair (z : PairInput) : Fraction×Fraction :=
  (RootedLabelWeightProgram.output (currentInput z),RootedLabelWeightProgram.output (nextInput z))
def queryPairRealizer : Realizer queryPair :=
  pair (composition (f := currentInput) (g := RootedLabelWeightProgram.output)
    currentInputRealizer RootedLabelWeightProgram.outputRealizer)
    (composition (f := nextInput) (g := RootedLabelWeightProgram.output)
      nextInputRealizer RootedLabelWeightProgram.outputRealizer)

def indices (z : Input) : List ℕ := List.range z.2.1.length
def indicesRealizer : Realizer indices :=
  composition (composition (composition second first) listLength) range

def indexedInput (z : Input×ℕ) : PairInput :=
  (z.1.1,(z.1.2.1.getD z.2 [],wordChunk ((blockWidth z.1.1,z.1.2.2),z.2)))
def indexedInputRealizer : Realizer indexedInput :=
  pair (composition first first)
    (pair (composition (pair (composition (composition first second) first) second) (getDFast []))
      (composition (f := fun z : Input×ℕ => ((blockWidth z.1.1,z.1.2.2),z.2)) (g := wordChunk)
        (pair (pair (composition (f := fun z : Input×ℕ => z.1.1) (g := blockWidth)
          (composition first first) blockWidthRealizer) (composition (composition first second) second)) second)
        wordChunkRealizer))

def indexedPair (z : Input×ℕ) : Fraction×Fraction := queryPair (indexedInput z)
def indexedPairRealizer : Realizer indexedPair :=
  composition (f := indexedInput) (g := queryPair) indexedInputRealizer queryPairRealizer

def output (z : Input) : List (Fraction×Fraction) := (indices z).map (fun i => indexedPair (z,i))
def outputRealizer : Realizer output :=
  composition (pair identity indicesRealizer) (mapWith indexedPairRealizer)

end ContingencyTables.CompanionObservationQueriesProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionObservedUpdateProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing a phase update from its trajectory and fresh query word -/
namespace ContingencyTables.CompanionObservedUpdateProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
abbrev Base := (CompanionTraceProgram.ReturnInput×CompanionMultiplierMatrixProgram.FractionMatrix)×TreeFraction.Fraction
abbrev Configs := CompanionObservationQueriesProgram.Config×CompanionObservationQueriesProgram.Config
abbrev Input := (Configs×Base)×List Bool

local instance instCodecConfigs : Codec Configs := inferInstance
local instance instCodecBase : Codec Base := inferInstance
local instance instCodecProdConfigsBase : Codec (Configs×Base) := inferInstance
local instance instCodecInput : Codec Input := inferInstance

def queryInput (z : Input) : CompanionObservationQueriesProgram.Input :=
  (z.1.1,(z.1.2.1.1.2,z.2))
def queryInputRealizer : Realizer queryInput :=
  pair (composition first first)
    (pair (composition (composition (composition (composition first second) first) first) second) second)

attribute [local irreducible] queryInput

def finishInput (z : Input) : CompanionPhaseFinishProgram.Input :=
  (z.1.2,CompanionObservationQueriesProgram.output (queryInput z))
def finishInputRealizer : Realizer finishInput :=
  pair (composition first second)
    (composition (f := queryInput) (g := CompanionObservationQueriesProgram.output)
      queryInputRealizer CompanionObservationQueriesProgram.outputRealizer)

attribute [local irreducible] finishInput

def output (z : Input) : Option CompanionPhaseFinishProgram.Stored :=
  CompanionPhaseFinishProgram.output (finishInput z)
def outputRealizer : Realizer output :=
  composition (f := finishInput) (g := CompanionPhaseFinishProgram.output)
    finishInputRealizer CompanionPhaseFinishProgram.outputRealizer

end ContingencyTables.CompanionObservedUpdateProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionTrajectoryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The flat executed observation trajectory, including its initial state -/
namespace ContingencyTables.CompanionTrajectoryProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
abbrev Input := CompanionFlatReturnProgram.Input

def output (z : Input) : List (List ℕ) :=
  CompanionBoundedWalkProgram.history (CompanionFlatReturnProgram.returnInput z)
def outputRealizer : Realizer output :=
  composition (f := CompanionFlatReturnProgram.returnInput) (g := CompanionBoundedWalkProgram.history)
    CompanionFlatReturnProgram.returnInputRealizer CompanionBoundedWalkProgram.historyRealizer

open CommonBasesFPRAS CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionOracleDensity CompanionWeightOracle
open CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram FiniteObservableTransport
open TwoLiftStates GridBoundary
open scoped Classical
end ContingencyTables.CompanionTrajectoryProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseTrialProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A complete executed trajectory and fresh-observation phase trial -/
namespace ContingencyTables.CompanionPhaseTrialProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
abbrev Stored := CompanionPhaseFinishProgram.Stored
abbrev Frame := CompanionObservedUpdateProgram.Configs×Stored
abbrev Input := (Frame×CompanionTrajectoryProgram.Input)×List Bool
local instance instCodecConfigs : Codec CompanionObservedUpdateProgram.Configs := inferInstance
local instance instCodecBase : Codec CompanionObservedUpdateProgram.Base := inferInstance
local instance instCodecProdConfigsBase : Codec (CompanionObservedUpdateProgram.Configs×CompanionObservedUpdateProgram.Base) := inferInstance
local instance instCodecInput : Codec CompanionObservedUpdateProgram.Input := inferInstance
local instance instCodecFrame : Codec Frame := inferInstance
local instance instCodecProdFrameInput : Codec (Frame×CompanionTrajectoryProgram.Input) := inferInstance
local instance instCodecInput_1 : Codec Input := inferInstance

def trajectory (z : Input) : List (List ℕ) := CompanionTrajectoryProgram.output z.1.2
def trajectoryRealizer : Realizer trajectory :=
  composition (f := fun z : Input => z.1.2) (g := CompanionTrajectoryProgram.output)
    (composition first second) CompanionTrajectoryProgram.outputRealizer

def catalogue (z : Input) : List (ℕ×ℕ) := PairedCatalogProgram.catalog z.1.2.1.1.2
def catalogueRealizer : Realizer catalogue :=
  composition (f := fun z : Input => z.1.2.1.1.2) (g := PairedCatalogProgram.catalog)
    (composition (composition (composition (composition first second) first) first) second)
    PairedCatalogProgram.catalogRealizer

attribute [local irreducible] trajectory catalogue

def returnInput (z : Input) : CompanionTraceProgram.ReturnInput := (catalogue z,trajectory z)
def returnInputRealizer : Realizer returnInput := pair catalogueRealizer trajectoryRealizer

def storedInput (z : Input) : CompanionObservedUpdateProgram.Base :=
  ((returnInput z,z.1.1.2.1),z.1.1.2.2)
def storedInputRealizer : Realizer storedInput :=
  pair (pair returnInputRealizer
    (composition (composition (composition first first) second) first))
    (composition (composition (composition first first) second) second)

def updateInput (z : Input) : CompanionObservedUpdateProgram.Input :=
  ((z.1.1.1,storedInput z),z.2)
def updateInputRealizer : Realizer updateInput :=
  pair (pair (composition (composition first first) first) storedInputRealizer) second

attribute [local irreducible] updateInput

def output (z : Input) : Option Stored := CompanionObservedUpdateProgram.output (updateInput z)
def outputRealizer : Realizer output :=
  composition (f := updateInput) (g := CompanionObservedUpdateProgram.output)
    updateInputRealizer CompanionObservedUpdateProgram.outputRealizer

end ContingencyTables.CompanionPhaseTrialProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOuterPhaseProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One complete adaptive phase from the stored chronological history -/
namespace ContingencyTables.CompanionOuterPhaseProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
abbrev Stored := CompanionPhaseFinishProgram.Stored
abbrev Request := (Prepared×Stored)×List Stored
abbrev Input := Request×List Bool
local instance instCodecConfigs : Codec CompanionObservedUpdateProgram.Configs := inferInstance
local instance instCodecBase_r7d0123_1 : Codec CompanionObservedUpdateProgram.Base := inferInstance
local instance instCodecProdConfigsBase_r7d0123_1 : Codec (CompanionObservedUpdateProgram.Configs×CompanionObservedUpdateProgram.Base) := inferInstance
local instance instCodecProdPreparedStored : Codec (Prepared×Stored) := inferInstance
local instance instCodecRequest : Codec Request := inferInstance
local instance instCodecInput_1 : Codec Input := inferInstance

def history (z : Input) : List Stored := z.1.2
def historyRealizer : Realizer history := composition first second

def phase (z : Input) : ℕ := (history z).length
def phaseRealizer : Realizer phase :=
  composition (f := history) (g := List.length) historyRealizer listLength

def old (z : Input) : Stored :=
  if phase z=0 then z.1.1.2 else (history z).getD (phase z-1) default
def oldRealizer : Realizer old :=
  (choose (composition (pair phaseRealizer (constant 0)) natEqual)
    (composition (composition first first) second)
    (composition (pair historyRealizer (composition (pair phaseRealizer (constant 1)) subtract))
      (getDFast default))).congr (by intro z; simp only [old,Function.comp_apply,decide_eq_true_eq])

def reserve (z : Input) : List Bool := z.2.map (fun _ => false)
def reserveRealizer : Realizer reserve := composition second (map (constant false))

def contextInput (z : Input×ℕ) : CompanionPhaseContextProgram.Input :=
  (((z.1.1.1.1,phase z.1+z.2),reserve z.1))
def contextInputRealizer : Realizer contextInput :=
  pair (pair (composition (composition (composition first first) first) first)
    (composition (pair (composition (f := Prod.fst) (g := phase) first phaseRealizer) second) add))
    (composition (f := Prod.fst) (g := reserve) first reserveRealizer)

def configAt (i : ℕ) (z : Input) : RootedLabelWeightProgram.Config :=
  CompanionPhaseContextProgram.config (contextInput (z,i))
def configAtRealizer (i : ℕ) : Realizer (configAt i) :=
  composition (f := fun z : Input => contextInput (z,i)) (g := CompanionPhaseContextProgram.config)
    (composition (f := fun z : Input => (z,i)) (g := contextInput)
      (pair identity (constant i)) contextInputRealizer) CompanionPhaseContextProgram.configRealizer

def restartRequest (z : Input) : Prepared×List Stored := (z.1.1.1,history z)
def restartRequestRealizer : Realizer restartRequest :=
  pair (composition (composition first first) first) historyRealizer

def restartWidth (z : Input) : ℕ := CompanionRestartSchedule.width (restartRequest z)
def restartWidthRealizer : Realizer restartWidth :=
  composition (f := restartRequest) (g := CompanionRestartSchedule.width)
    restartRequestRealizer CompanionRestartSchedule.widthRealizer

def restartInput (z : Input) : CompanionInitializedRestartProgram.Input :=
  (restartRequest z,z.2)
def restartInputRealizer : Realizer restartInput :=
  pair restartRequestRealizer second

def startCode (z : Input) : List ℕ := CompanionInitializedRestartProgram.output (restartInput z)
def startCodeRealizer : Realizer startCode :=
  composition (f := restartInput) (g := CompanionInitializedRestartProgram.output)
    restartInputRealizer CompanionInitializedRestartProgram.outputRealizer

def parameters (z : Input) : CountingPhaseParametersProgram.Input := z.1.1.1.2
def parametersRealizer : Realizer parameters := composition (composition (composition first first) first) second

def precision (z : Input) : ℕ := CountingPhaseParametersProgram.precision (parameters z)
def precisionRealizer : Realizer precision :=
  composition (f := parameters) (g := CountingPhaseParametersProgram.precision)
    parametersRealizer CountingPhaseParametersProgram.precisionRealizer

def observations (z : Input) : ℕ := CountingPhaseParametersProgram.observations (parameters z)
def observationsRealizer : Realizer observations :=
  composition (f := parameters) (g := CountingPhaseParametersProgram.observations)
    parametersRealizer CountingPhaseParametersProgram.observationsRealizer

attribute [local irreducible] old startCode configAt

def walkState (z : Input) : CompanionBoundedWalkProgram.State :=
  ((((configAt 0 z,(old z).1),precision z),startCode z),startCode z)
def walkStateRealizer : Realizer walkState :=
  pair (pair (pair (pair (configAtRealizer 0) (composition (f := old) (g := Prod.fst) oldRealizer first))
    precisionRealizer) startCodeRealizer) startCodeRealizer

def widthInput (z : Input) : CompanionMetropolisWordProgram.Input :=
  (((walkState z).1.1,(walkState z).2),[])
def widthInputRealizer : Realizer widthInput :=
  pair (pair (composition (composition (f := walkState) (g := Prod.fst) walkStateRealizer first) first)
    (composition (f := walkState) (g := Prod.snd) walkStateRealizer second)) (constant [])

def trajectoryWidth (z : Input) : ℕ := observations z*CompanionTransitionWidth.width (widthInput z)
def trajectoryWidthRealizer : Realizer trajectoryWidth :=
  composition (pair observationsRealizer (composition (f := widthInput) (g := CompanionTransitionWidth.width)
    widthInputRealizer CompanionTransitionWidth.widthRealizer)) multiply

def afterRestart (z : Input) : List Bool := z.2.drop (restartWidth z)
def afterRestartRealizer : Realizer afterRestart := composition (pair second restartWidthRealizer) dropFast

def trajectoryInput (z : Input) : CompanionTrajectoryProgram.Input :=
  ((walkState z,observations z),(afterRestart z).take (trajectoryWidth z))
def trajectoryInputRealizer : Realizer trajectoryInput :=
  pair (pair walkStateRealizer observationsRealizer)
    (composition (pair afterRestartRealizer trajectoryWidthRealizer) takeFast)

def trialInput (z : Input) : CompanionPhaseTrialProgram.Input :=
  ((((configAt 0 z,configAt 1 z),old z),trajectoryInput z),(afterRestart z).drop (trajectoryWidth z))
def trialInputRealizer : Realizer trialInput :=
  pair (pair (pair (pair (configAtRealizer 0) (configAtRealizer 1)) oldRealizer) trajectoryInputRealizer)
    (composition (pair afterRestartRealizer trajectoryWidthRealizer) dropFast)

attribute [local irreducible] trialInput

def fallback (p : Stored×Option Stored) : Stored := p.2.getD p.1
def fallbackRealizer : Realizer fallback :=
  (optionCases identity second).congr (by intro p; unfold fallback; cases p.2 <;> rfl)

def output (z : Input) : Stored := (CompanionPhaseTrialProgram.output (trialInput z)).getD (old z)
def outputRealizer : Realizer output :=
  composition (f := fun z : Input => (old z,CompanionPhaseTrialProgram.output (trialInput z)))
    (g := fallback)
    (pair oldRealizer (composition (f := trialInput) (g := CompanionPhaseTrialProgram.output)
      trialInputRealizer CompanionPhaseTrialProgram.outputRealizer)) fallbackRealizer

end ContingencyTables.CompanionOuterPhaseProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionObservationQueriesLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact independent laws for the executed observation queries -/
namespace ContingencyTables.CompanionObservationQueriesProgram
open MatchingFPRAS DensePrograms GridBoundary FairBits CommonBasesFPRAS FiniteObservableTransport
open CompanionFactorialApplication CompanionComputedInitial CompanionArithmeticProposal
open CompanionOracleDensity CompanionWeightOracle
open scoped Classical
noncomputable section
attribute [local irreducible] queryWidth queryPair RootedLabelWeightProgram.output
  RootedLabelWeightProgram.config RootedEstimatorMedianProgram.context RootedEstimatorLayoutProgram.wordWidth

def values (xs : List (Fraction×Fraction)) : List (ℚ×ℚ) :=
  xs.map (fun z => (TreeFraction.val z.1,TreeFraction.val z.2))

variable {m n : ℕ}

/-- The two physical configurations used for observing one phase. -/
def phaseConfigs (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : ℚ)
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth nextDegree nextDepth : List Bool) : Config×Config :=
  (RootedLabelWeightProgram.config A C K j xi xi z v degree depth,
    RootedLabelWeightProgram.config A C K (j+1) xi xi z v nextDegree nextDepth)

end
end ContingencyTables.CompanionObservationQueriesProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionObservedUpdateLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Observable law of the physically executed phase update -/
namespace ContingencyTables.CompanionObservedUpdateProgram
open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial
open CompanionArithmeticProposal CompanionOrderedProposal CompanionMultiplierMatrixProgram
open FiniteObservableTransport CompanionComputedProposal TwoLiftStates
open scoped Classical
noncomputable section
variable {m n N : ℕ} (A : Instance (Fin m) (Fin n))

abbrev LabelIndex := CompanionEvaluatedWeightProgram.LabelIndex A

def data (cs : Configs) (states : Fin N→Set (Labels A×Bool))
    (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction) (E : TreeFraction.Fraction)
    (bits : List Bool) : Input :=
  ((cs,(((orderedCatalog A (pairLabels A) (coordinateOrder A),
    (List.ofFn states).map (encodeSet (coordinateOrder A))),matrixCode w),E)),bits)

attribute [local irreducible] CompanionObservationQueriesProgram.output
  CompanionPhaseFinishProgram.output CompanionPhaseFinishProgram.rationalResult

open GridBoundary CommonBasesFPRAS CompanionWeightOracle CompanionOracleDensity

end
end ContingencyTables.CompanionObservedUpdateProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseTrialLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed trajectory and fresh queries form the source phase trial -/
namespace ContingencyTables.CompanionPhaseTrialProgram
open MatchingFPRAS CommonBasesFPRAS CompanionFactorialApplication CompanionComputedInitial
open CompanionComputedProposal CompanionOrderedProposal CompanionArithmeticProposal
open CompanionOracleDensity CompanionWeightOracle CompanionMultiplierMatrixProgram
open CompanionEvaluatedWeightProgram FiniteObservableTransport GridBoundary TwoLiftStates
open scoped Classical
noncomputable section
variable {m n : ℕ}

def data (A : Instance (Fin m) (Fin n)) (C K j k N : ℕ) (xi : ℚ)
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth nextDegree nextDepth : List Bool)
    (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction) (E : TreeFraction.Fraction)
    (S : CompanionBooleanPhase.State A) (walkBits queryBits : List Bool) : Input :=
  (((CompanionObservationQueriesProgram.phaseConfigs A C K j xi z v degree depth nextDegree nextDepth,
      (matrixCode w,E)),
    CompanionFlatReturnProgram.data A C K j k N xi z v degree depth w S walkBits),queryBits)

end
end ContingencyTables.CompanionPhaseTrialProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOuterPhaseSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal data and slices of a complete adaptive phase -/
namespace ContingencyTables.CompanionOuterPhaseProgram
open MatchingFPRAS CommonBasesFPRAS CompanionFactorialApplication CompanionComputedInitial
open CompanionComputedProposal CompanionArithmeticProposal CompanionEvaluatedWeightProgram
open CompanionMultiplierMatrixProgram CompanionOracleDensity GridBoundary
open scoped BigOperators Classical
noncomputable section
variable {m n : ℕ}

def data (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ→LabelIndex A→LabelIndex A→TreeFraction.Fraction)
    (E : ℕ→TreeFraction.Fraction) (bits : List Bool) : Input :=
  (((CompanionRestartInitializer.data A C K H T N R L epsilon z v,(matrixCode (w 0),E 0)),
    List.ofFn (fun i : Fin j => (matrixCode (w (i.val+1)),E (i.val+1)))),bits)

end
end ContingencyTables.CompanionOuterPhaseProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionLabelMetadataProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering each paired label's cell and capacity

The multiplicities come from the actual bounded profile blocks. A
large numeric capacity never causes an allocation beyond the supplied
profile code. On a canonical code, the resulting order is exactly the
copy order used by the initializer and arithmetic proposals.
-/

namespace ContingencyTables.CompanionLabelMetadataProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
open PairedProfileProgram PairedFactorialProgram

def indicesRealizer : Realizer indices :=
  composition (composition second pairCountRealizer) range
def labelRowRealizer : Realizer labelRow :=
  composition (pair identity indicesRealizer)
    (mapWith (pair (composition first first) (composition (composition first second) pairCountRealizer)))
def rowInputRealizer : Realizer rowInput :=
  pair second (composition (pair
    (composition (f := fun z : Input × ℕ => z.1) (g := rows) first rowsRealizer)
    second) (getDFast []))
def indexedRowRealizer : Realizer indexedRow :=
  composition (f := rowInput) (g := labelRow) rowInputRealizer labelRowRealizer
def outputRealizer : Realizer output :=
  composition (composition (pair identity NaturalBlockProgram.indicesRealizer)
    (mapWith indexedRowRealizer)) flatten
end ContingencyTables.CompanionLabelMetadataProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionInitialMatrixProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the initial canonical multiplier matrix -/

namespace ContingencyTables.CompanionInitialMatrixProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped CompanionMultiplierMatrixProgram

def numeratorRealizer : Realizer numerator :=
  composition (f := fun z : Metadata × Metadata => (6,z.1.2+1))
    (g := fun p : ℕ × ℕ => p.1*p.2)
    (pair (constant 6) (composition (composition first second) successor)) multiply
def sameCellRealizer : Realizer sameCell :=
  composition (pair (composition first first) (composition second first)) natEqual
def entryRealizer : Realizer entry :=
  choose sameCellRealizer (constant (6,1))
    (composition (pair numeratorRealizer denominatorRealizer) TreeFraction.normalizeRealizer)
def rowRealizer : Realizer row := composition (pair second first) (mapWith entryRealizer)
def matrixRealizer : Realizer matrix := composition (pair identity identity) (mapWith rowRealizer)
def outputRealizer : Realizer output :=
  composition (f := CompanionLabelMetadataProgram.output) (g := matrix)
    CompanionLabelMetadataProgram.outputRealizer matrixRealizer
end ContingencyTables.CompanionInitialMatrixProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionInitialStoredProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal initial count and stored multiplier matrix

The integer count is the product of the free-cell ranges and the small-cell
ranges. Both lists come from the executed forest and cell catalogs.
-/
namespace ContingencyTables.CompanionInitialStoredProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms

def rangeAtRealizer : Realizer rangeAt :=
  composition (f := fun z : RootedForestCatalog.Data×(ℕ×ℕ) => matrixEntry (z.1.2,z.2))
    (g := Nat.succ)
    (composition (f := fun z : RootedForestCatalog.Data×(ℕ×ℕ) => (z.1.2,z.2))
      (g := matrixEntry) (pair (composition first second) second) matrixEntryRealizer) successor
def freeRangesRealizer : Realizer freeRanges :=
  composition (f := fun d : RootedForestCatalog.Data => (d,RootedForestCatalog.catalog (d,false)))
    (g := fun p : RootedForestCatalog.Data×List (ℕ×ℕ) => p.2.map (fun ij => rangeAt (p.1,ij)))
    (pair identity (composition (f := fun d : RootedForestCatalog.Data => (d,false))
      (g := RootedForestCatalog.catalog) (pair identity (constant false)) RootedForestCatalog.catalogRealizer))
    (mapWith rangeAtRealizer)
def freeProductRealizer : Realizer freeProduct :=
  composition (f := freeRanges) (g := List.prod) freeRangesRealizer listProd
def smallProductRealizer : Realizer smallProduct := composition (map successor) listProd
def totalRealizer : Realizer total :=
  pair (composition (f := fun z : Input => (freeProduct z.1,smallProduct z.2.1))
    (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (composition (f := fun z : Input => z.1) (g := freeProduct) first freeProductRealizer)
      (composition (f := fun z : Input => z.2.1) (g := smallProduct)
        (composition second first) smallProductRealizer)) multiply) (constant 1)
def outputRealizer : Realizer output :=
  pair (composition (f := fun z : Input => z.2) (g := CompanionInitialMatrixProgram.output)
    second CompanionInitialMatrixProgram.outputRealizer) totalRealizer
end ContingencyTables.CompanionInitialStoredProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOuterHistoryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Chronological execution of all counting phases -/
namespace ContingencyTables.CompanionOuterHistoryProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
abbrev Stored := CompanionPhaseFinishProgram.Stored
abbrev Fixed := Prepared×Stored
abbrev State := Fixed×List Stored
abbrev Input := Fixed×List (List Bool)
local instance instCodecFixed : Codec Fixed := inferInstance
local instance instCodecState : Codec State := inferInstance
local instance instCodecInput : Codec Input := inferInstance

def phaseInput (z : List Bool×State) : CompanionOuterPhaseProgram.Input := (z.2,z.1)
def phaseInputRealizer : Realizer phaseInput := pair second first

def next (z : List Bool×State) : Stored := CompanionOuterPhaseProgram.output (phaseInput z)
def nextRealizer : Realizer next :=
  composition (f := phaseInput) (g := CompanionOuterPhaseProgram.output)
    phaseInputRealizer CompanionOuterPhaseProgram.outputRealizer

def advance (z : List Bool×State) : State := (z.2.1,z.2.2++[next z])
def advanceRealizer : Realizer advance :=
  pair (composition second first)
    (composition (pair (composition second second)
      (composition (pair nextRealizer (constant [])) listCons)) append)

def run (z : Input) : State := z.2.foldl (fun state bits => advance (bits,state)) (z.1,[])
def runRealizer : Realizer run :=
  composition (pair second (pair first (constant []))) (fold advanceRealizer)

def storedHistory (z : Input) : List Stored := (run z).2
def storedHistoryRealizer : Realizer storedHistory :=
  composition (f := run) (g := Prod.snd) runRealizer second

def output (z : Input) : Stored :=
  CompanionOuterPhaseProgram.old ((z.1,storedHistory z),[])
def outputRealizer : Realizer output :=
  composition (f := fun z : Input => ((z.1,storedHistory z),[]))
    (g := CompanionOuterPhaseProgram.old)
    (pair (pair first storedHistoryRealizer) (constant [])) CompanionOuterPhaseProgram.oldRealizer

end ContingencyTables.CompanionOuterHistoryProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionStoredRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact square-matrix representations along the physical phase loop

Successful updates construct every entry in catalog order. Aborted updates
retain the previous stored value, so the same representation supports the
readback used in the projected history law.
-/
namespace ContingencyTables.CompanionStoredRepresentation
open MatchingFPRAS CompanionMultiplierMatrixProgram

def MatrixRep (p : ℕ) (M : FractionMatrix) : Prop :=
  ∃ w : Fin p→Fin p→TreeFraction.Fraction, M=matrixCode w

def StoredRep (p : ℕ) (s : CompanionPhaseFinishProgram.Stored) : Prop :=
  MatrixRep p s.1

def entries (p : ℕ) (M : FractionMatrix) (i j : Fin p) : TreeFraction.Fraction :=
  readEntry (M,(i.val,j.val))

end ContingencyTables.CompanionStoredRepresentation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionHistoryReadback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reading a represented physical history as source matrix data -/
namespace ContingencyTables.CompanionHistoryReadback
open MatchingFPRAS CompanionMultiplierMatrixProgram CompanionStoredRepresentation
open CompanionFactorialApplication CompanionComputedInitial CompanionEvaluatedWeightProgram
open GridBoundary
open scoped Classical
noncomputable section

abbrev Stored := CompanionPhaseFinishProgram.Stored

def lookup (initial : Stored) (history : List Stored) : ℕ→Stored
  | 0 => initial
  | i+1 => history.getD i initial

def matrixAt (p : ℕ) (initial : Stored) (history : List Stored) (i : ℕ) :
    Fin p→Fin p→TreeFraction.Fraction := entries p (lookup initial history i).1

def estimateAt (initial : Stored) (history : List Stored) (i : ℕ) : TreeFraction.Fraction :=
  (lookup initial history i).2

def viewLookup {Z : Type} (initial : Z) (history : List Z) : ℕ→Z
  | 0 => initial
  | i+1 => history.getD i initial

end
end ContingencyTables.CompanionHistoryReadback

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuing an adaptive phase from its initialized profile -/
namespace ContingencyTables.CompanionPhaseContinuation
open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram
open CompanionOracleDensity CompanionWeightOracle GridBoundary FiniteObservableTransport CommonBasesFPRAS TwoLiftStates
open scoped Classical
noncomputable section

abbrev Configs := CompanionObservedUpdateProgram.Configs
abbrev Stored := CompanionPhaseFinishProgram.Stored

def state (cs : Configs) (old : Stored) (k : ℕ) (code : List ℕ) : CompanionBoundedWalkProgram.State :=
  ((((cs.1,old.1),k),code),code)

def width (cs : Configs) (old : Stored) (k : ℕ) (code : List ℕ) : ℕ :=
  CompanionTransitionWidth.width ((((cs.1,old.1),k),code),[])

def input (cs : Configs) (old : Stored) (k N : ℕ) (code : List ℕ) (tail : List Bool) :
    CompanionPhaseTrialProgram.Input :=
  (((cs,old),((state cs old k code,N),tail.take (N*width cs old k code))),
    tail.drop (N*width cs old k code))

def run (cs : Configs) (old : Stored) (k N : ℕ) (code : List ℕ) (tail : List Bool) : Stored :=
  (CompanionPhaseTrialProgram.output (input cs old k N code tail)).getD old

end
end ContingencyTables.CompanionPhaseContinuation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRestartContinuation
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binding a restart law to its independent phase continuation -/

namespace ContingencyTables.CompanionOuterPhaseProgram
open MatchingFPRAS CommonBasesFPRAS CompanionFactorialApplication CompanionComputedInitial
open CompanionComputedProposal CompanionArithmeticProposal CompanionEvaluatedWeightProgram
open CompanionMultiplierMatrixProgram CompanionOracleDensity GridBoundary FiniteObservableTransport
open scoped Classical
noncomputable section
variable {m n : ℕ}

def configs (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    CompanionPhaseContinuation.Configs :=
  let p := CompanionInitializedRestartProgram.parameters A H T N R L epsilon
  CompanionObservationQueriesProgram.phaseConfigs A C K j
    (TreeFraction.val (CountingPhaseParametersProgram.noise p)) z v
    (CompanionRestartStageProgram.degree A C K j p z v reserve)
    (CompanionRestartStageProgram.depth A C K j p z v reserve)
    (CompanionRestartStageProgram.degree A C K (j+1) p z v reserve)
    (CompanionRestartStageProgram.depth A C K (j+1) p z v reserve)

end
end ContingencyTables.CompanionOuterPhaseProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOuterPhaseLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Law of an executed outer phase, including its initialized restart -/
namespace ContingencyTables.CompanionOuterPhaseProgram
open MatchingFPRAS CommonBasesFPRAS FirstSuccess FairBits CompanionFactorialApplication
open CompanionComputedInitial CompanionComputedProposal CompanionArithmeticProposal
open CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram CompanionOracleDensity
open GridBoundary FiniteObservableTransport TwoLiftStates
open scoped Classical
noncomputable section
variable {m n : ℕ}

def tailWidth (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) (padding : ℕ) : ℕ :=
  let p := CompanionInitializedRestartProgram.parameters A H T N R L epsilon
  let xi := TreeFraction.val (CountingPhaseParametersProgram.noise p)
  let k := CountingPhaseParametersProgram.precision p
  let obs := CountingPhaseParametersProgram.observations p
  obs*CompanionBooleanPhase.stepBits A C K j k xi+
    ((obs+1)*CompanionObservationQueriesProgram.blockWidth
      (configs A C K H T N R L j epsilon z v reserve)+padding)

def phaseWordWidth (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) (padding : ℕ) : ℕ :=
  wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
    (CompanionRestartProgram.sumBits A C K j
      (CompanionInitializedRestartProgram.parameters A H T N R L epsilon)+
      tailWidth A C K H T N R L j epsilon z v reserve padding)

attribute [local irreducible] CompanionInitializedRestartProgram.output
  CompanionInitializedRestartProgram.model CompanionInitializedRestartProgram.jointModel
  CompanionPhaseContinuation.run CompanionOuterPhaseProgram.output

end
end ContingencyTables.CompanionOuterPhaseProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOuterWidths
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed phase widths and the source history word

The supplied precision markers do not contribute to the number of oracle
bits. After identifying the computed scalar controls, the complete phase
width is the source width plus its unused padding.
-/
namespace ContingencyTables.CompanionOuterWidths
open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial
open CompanionOracleDensity GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

def tailWidth (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) (padding : ℕ) : ℕ :=
  let p := CompanionInitializedRestartProgram.parameters A H T N R L epsilon
  let xi := TreeFraction.val (CountingPhaseParametersProgram.noise p)
  let k := CountingPhaseParametersProgram.precision p
  let obs := CountingPhaseParametersProgram.observations p
  obs*CompanionBooleanPhase.stepBits A C K j k xi+
    ((obs+1)*CompanionObservationQueriesProgram.blockWidth
      (CompanionOuterPhaseProgram.configs A C K H T N R L j epsilon z v reserve)+padding)

def phaseWidth (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) (padding : ℕ) : ℕ :=
  wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
    (CompanionRestartProgram.sumBits A C K j
      (CompanionInitializedRestartProgram.parameters A H T N R L epsilon)+
      tailWidth A C K H T N R L j epsilon z v reserve padding)

end
end ContingencyTables.CompanionOuterWidths

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionCanonicalPhaseLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The projected law of one complete physical counting phase -/
namespace ContingencyTables.CompanionCanonicalPhaseLaw
open MatchingFPRAS CommonBasesFPRAS FirstSuccess FairBits FiniteObservableTransport
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram CompanionCanonicalHistory
open CompanionHistoryReadback CompanionStoredRepresentation CompanionOracleDensity
open CompanionRationalUpdates TwoLiftStates GridBoundary
open scoped Classical
noncomputable section

def canonicalResult {I J : Type} [Fintype I] [Fintype J]
    (A : Instance I J) {p : ℕ} (g : Fin p ≃ Labels A)
    (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (history : List (Canonical (p := p))) (j : ℕ)
    (bits : RootedRestartTrial.Words A s.C s.K s.H s.L j s.k s.n s.N s.h s.xi) :
    Canonical (p := p) :=
  let hs := history.map (extend A g)
  let old := RootedStoredHistory.lookup A hs j
  project A g ((RootedRestartTrial.run A R s.C s.K s.H s.L j s.k s.n s.N s.h
    s.hK s.hW s.xi s.v (fun i => (RootedStoredHistory.lookup A hs i).multiplier)
      old.estimate bits).getD old)

variable {m n : ℕ}

def rawSettings (A : Instance (Fin m) (Fin n)) (C K H N R L : ℕ)
    (epsilon : TreeFraction.Fraction) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) : RootedPhaseHistory.Settings A where
  C := C
  K := K
  H := H
  L := L
  k := CountingPhaseParametersProgram.precision (CompanionInitializedRestartProgram.parameters A H
    (CompanionTargetMixing.restartTime A H L) N R L epsilon)
  n := R
  N := CountingPhaseParametersProgram.observations (CompanionInitializedRestartProgram.parameters A H
    (CompanionTargetMixing.restartTime A H L) N R L epsilon)
  h := CountingPhaseSchedule.initialPrecision H
  hK := hK
  hW := hW
  xi := TreeFraction.val (CountingPhaseParametersProgram.noise
    (CompanionInitializedRestartProgram.parameters A H (CompanionTargetMixing.restartTime A H L) N R L epsilon))
  v := RootedCatalogGrid.gridEquiv A K v

def sourceStored (A : Instance (Fin m) (Fin n))
    (initial : CompanionPhaseFinishProgram.Stored) (history : List CompanionPhaseFinishProgram.Stored)
    (i : ℕ) : CompanionPhaseWords.Stored A :=
  ⟨sourceWeights A (matrixAt (CanonicalInitialEncoding.copyOrder (capacities A)).length initial history i),
    TreeFraction.val (estimateAt initial history i)⟩

def readbackResult (A : Instance (Fin m) (Fin n)) (s : RootedPhaseHistory.Settings A)
    (initial : CompanionPhaseFinishProgram.Stored) (history : List CompanionPhaseFinishProgram.Stored)
    (bits : RootedRestartTrial.Words A s.C s.K s.H s.L history.length s.k s.n s.N s.h s.xi) :
    Canonical (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length) :=
  let old := sourceStored A initial history history.length
  project A (pairLabels A) ((RootedRestartTrial.run A (RootedCompletion.rowColumn A.T)
    s.C s.K s.H s.L history.length s.k s.n s.N s.h s.hK s.hW s.xi s.v
      (fun i => (sourceStored A initial history i).multiplier) old.estimate bits).getD old)

end
end ContingencyTables.CompanionCanonicalPhaseLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionProjectedHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lifting executed phase laws through the complete adaptive history -/
namespace ContingencyTables.CompanionProjectedHistory
open MatchingFPRAS CommonBasesFPRAS FiniteObservableTransport
open CompanionFactorialApplication CompanionStoredRepresentation
open CompanionCanonicalHistory
open scoped Classical
noncomputable section

abbrev Stored := CompanionPhaseFinishProgram.Stored

def advance (fixed : CompanionOuterHistoryProgram.Fixed) {W : ℕ}
    (history : List Stored) (bits : Fin W→Bool) : List Stored :=
  history++[CompanionOuterPhaseProgram.output ((fixed,history),List.ofFn bits)]

end
end ContingencyTables.CompanionProjectedHistory

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionUniformPhaseWidth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A computed common padded width for every adaptive phase

All bounds are fixed arithmetic circuits. No numeric phase count controls
an unbounded preprocessing loop.
-/
namespace ContingencyTables.CompanionUniformPhaseWidth
open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram

def oracleInput (z : Input) : RootedOracleConfigProgram.Input :=
  (((z.1,CountingPhaseParametersProgram.noise z.2),0),[])
def oracleInputRealizer : Realizer oracleInput :=
  pair (pair (pair first (composition (f := Prod.snd) (g := CountingPhaseParametersProgram.noise)
    second CountingPhaseParametersProgram.noiseRealizer)) (constant 0)) (constant [])

def rawFields (z : Input) : List ℕ := RootedOracleConfigProgram.fields (oracleInput z)++z.2.1
def rawFieldsRealizer : Realizer rawFields :=
  composition (f := fun z : Input => (RootedOracleConfigProgram.fields (oracleInput z),z.2.1))
    (g := fun p : List ℕ×List ℕ => p.1++p.2)
    (pair (composition (f := oracleInput) (g := RootedOracleConfigProgram.fields)
      oracleInputRealizer RootedOracleConfigProgram.fieldsRealizer) (composition second first)) append
def precisionRealizer : Realizer precision :=
  composition (f := Prod.snd) (g := CountingPhaseParametersProgram.precision)
    second CountingPhaseParametersProgram.precisionRealizer
def initialPrecisionRealizer : Realizer initialPrecision :=
  composition (f := Prod.snd)
    (g := CountingPhaseParametersProgram.scalar CountingPhaseScalarProgram.initialPrecision)
    second (CountingPhaseParametersProgram.scalarRealizer CountingPhaseScalarProgram.initialPrecision)

def fields (z : Input) : List ℕ := rawFields z++[precision z,initialPrecision z]
def fieldsRealizer : Realizer fields :=
  composition (f := fun z : Input => (rawFields z,[precision z,initialPrecision z]))
    (g := fun p : List ℕ×List ℕ => p.1++p.2)
    (pair rawFieldsRealizer (composition
      (pair precisionRealizer (composition (pair initialPrecisionRealizer (constant [])) listCons)) listCons)) append

def measure (z : Input) : ℕ := (fields z).sum+1
def measureRealizer : Realizer measure := composition (composition fieldsRealizer listSum) successor

def width (z : Input) : ℕ := widthExpression.eval [measure z]
def widthRealizer : Realizer width :=
  composition (f := fun z : Input => [measure z]) (g := widthExpression.eval)
    (composition (pair measureRealizer (constant [])) listCons) widthExpression.realizer

end ContingencyTables.CompanionUniformPhaseWidth

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingLabelCountProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the actual number of factorial labels

Only retained capacities are summed; the program does not expand any
capacity into a list of labels to obtain the phase controls.
-/

namespace ContingencyTables.CountingLabelCountProgram
open MatchingFPRAS.TreeTyped

def catalogInputRealizer : Realizer catalogInput :=
  pair (pair (composition first second) second) (composition (composition first first) second)
def capacitiesRealizer : Realizer capacities :=
  composition (f := catalogInput) (g := CompanionCellCatalog.capacities)
    catalogInputRealizer CompanionCellCatalog.capacitiesRealizer
def countRealizer : Realizer count :=
  composition (f := capacities) (g := List.sum) capacitiesRealizer listSum

open CompanionFactorialApplication
open scoped BigOperators Classical

end ContingencyTables.CountingLabelCountProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCountingAmplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic confidence for the actual adaptive counting estimator -/

namespace ContingencyTables.RootedCountingAmplification

open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates
open CompanionOracleDensity RootedPhaseHistory RootedCountingSchedule
open CompanionTerminalMass (Endpoints tableCount )
open CompanionTerminalApplication (finalPhase)
open CountingPhaseSchedule GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

def bitCount (A : Instance I J) (s : Settings A) (delta : ℚ) : ℕ :=
  repetitionCount delta * RootedCountingWords.bitCount A s

def estimate (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (s : Settings A) (delta : ℚ) (bits : Fin (bitCount A s delta) → Bool) : ℚ :=
  rationalMedian (List.ofFn (fun i : Fin (repetitionCount delta) =>
    RootedCountingWords.flatEstimate A R s
      (gridWordEquiv (repetitionCount delta) (RootedCountingWords.bitCount A s) bits i)))

end
end ContingencyTables.RootedCountingAmplification

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_EndpointMatrixProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing every attained cell endpoint

Both scans use the dimensions of the stored margin lists. Each entry is
computed by the binary feasibility search; neither scan enumerates tables.
-/

namespace ContingencyTables.EndpointMatrixProgram

open MatchingFPRAS.TreeTyped Polynomial ResidualGraphProgram

def contextRealizer : Realizer context := pair (composition first first)
  (pair (composition first second) second)

def lowerEntry (z : CellInput) : ℕ := CellMinimumProgram.minimum (context z)
def lowerEntryRealizer : Realizer lowerEntry :=
  composition (f := context) (g := CellMinimumProgram.minimum)
    contextRealizer CellMinimumProgram.minimumRealizer

def upperEntry (z : CellInput) : ℕ := CellMaximumProgram.maximum (context z)
def upperEntryRealizer : Realizer upperEntry :=
  composition (f := context) (g := CellMaximumProgram.maximum)
    contextRealizer CellMaximumProgram.maximumRealizer
def columnsRealizer : Realizer columns :=
  composition (composition (composition (composition first first) second) listLength) range

def lowerRow (z : RowInput) : List ℕ := (columns z).map (fun j => lowerEntry (z,j))
def lowerRowRealizer : Realizer lowerRow :=
  composition (pair identity columnsRealizer) (mapWith lowerEntryRealizer)

def upperRow (z : RowInput) : List ℕ := (columns z).map (fun j => upperEntry (z,j))
def upperRowRealizer : Realizer upperRow :=
  composition (pair identity columnsRealizer) (mapWith upperEntryRealizer)
def rowsRealizer : Realizer rows :=
  composition (composition (composition first first) listLength) range

def lowerMatrix (z : Input) : NatMatrix := (rows z).map (fun i => lowerRow (z,i))
def lowerMatrixRealizer : Realizer lowerMatrix :=
  composition (pair identity rowsRealizer) (mapWith lowerRowRealizer)

def upperMatrix (z : Input) : NatMatrix := (rows z).map (fun i => upperRow (z,i))
def upperMatrixRealizer : Realizer upperMatrix :=
  composition (pair identity rowsRealizer) (mapWith upperRowRealizer)

lemma lowerMatrix_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    lowerMatrix (NetworkVertexCode.data r c b) = natCode (fun (i : Fin m) (j : Fin n) =>
      CellMinimumProgram.minimum (NetworkVertexCode.data r c b,(i.val,j.val))) := by
  simp only [lowerMatrix,rows,NetworkVertexCode.data,List.length_ofFn,
    DirectedBFSCode.range_eq_map,←List.ofFn_eq_map,List.map_ofFn,natCode]
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  simp only [lowerRow,columns,List.length_ofFn,DirectedBFSCode.range_eq_map,
    ←List.ofFn_eq_map,List.map_ofFn]
  rfl

lemma upperMatrix_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    upperMatrix (NetworkVertexCode.data r c b) = natCode (fun (i : Fin m) (j : Fin n) =>
      CellMaximumProgram.maximum (NetworkVertexCode.data r c b,(i.val,j.val))) := by
  simp only [upperMatrix,rows,NetworkVertexCode.data,List.length_ofFn,
    DirectedBFSCode.range_eq_map,←List.ofFn_eq_map,List.map_ofFn,natCode]
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  simp only [upperRow,columns,List.length_ofFn,DirectedBFSCode.range_eq_map,
    ←List.ofFn_eq_map,List.map_ofFn]
  rfl

end ContingencyTables.EndpointMatrixProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_NetworkTableProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extracting the bounded table from the executed flow

The output reads the row-to-column arcs of the computed flow. Both the
matrix dimensions and the encoded entries are obtained from the input;
there is no choice of a mathematical witness in the program.
-/

namespace ContingencyTables.NetworkTableProgram

open MatchingFPRAS.TreeTyped Polynomial NetworkVertexCode ResidualGraphProgram
open scoped BigOperators

abbrev Prepared := (List ℕ×List ℕ)×FlowMatrix
abbrev CellInput := Prepared×(ℕ×ℕ)

def cell (z : CellInput) : ℕ :=
  let a := flowEntry (z.1.2,(2+z.2.1,2+z.1.1.1.length+z.2.2))
  a.1-a.2

def cellRealizer : Realizer cell := by
  let F : Realizer (fun z : CellInput=>z.1.2) := composition first second
  let I : Realizer (fun z : CellInput=>2+z.2.1) :=
    composition (f := fun z : CellInput=>(2,z.2.1))
      (g := fun a : ℕ×ℕ=>a.1+a.2) (pair (constant 2) (composition second first)) add
  let J : Realizer (fun z : CellInput=>2+z.1.1.1.length+z.2.2) :=
    composition (f := fun z : CellInput=>(2+z.1.1.1.length,z.2.2))
      (g := fun a : ℕ×ℕ=>a.1+a.2)
      (pair (composition (f := fun z : CellInput=>(2,z.1.1.1.length))
        (g := fun a : ℕ×ℕ=>a.1+a.2)
        (pair (constant 2) (composition (composition (composition first first) first) listLength)) add)
        (composition second second)) add
  exact composition (f := fun z : CellInput=>
    flowEntry (z.1.2,(2+z.2.1,2+z.1.1.1.length+z.2.2)))
    (g := fun a : SignedPairProgram.Signed=>a.1-a.2)
    (composition (f := fun z : CellInput=>
      (z.1.2,(2+z.2.1,2+z.1.1.1.length+z.2.2))) (g := flowEntry)
      (pair F (pair I J)) flowEntryRealizer) subtract

def rowIndices (z : Prepared) : List ℕ := List.range z.1.1.length
def columnIndices (z : Prepared) : List ℕ := List.range z.1.2.length

def rowIndicesRealizer : Realizer rowIndices :=
  composition (composition (composition first first) listLength) range

def columnIndicesRealizer : Realizer columnIndices :=
  composition (composition (composition first second) listLength) range

def row (z : Prepared×ℕ) : List ℕ :=
  (columnIndices z.1).map (fun j=>cell (z.1,(z.2,j)))

def rowRealizer : Realizer row :=
  composition (pair identity (composition first columnIndicesRealizer))
    (mapWith (composition (f := fun z : (Prepared×ℕ)×ℕ=>(z.1.1,(z.1.2,z.2)))
      (g := cell) (pair (composition first first)
        (pair (composition first second) second)) cellRealizer))

def table (z : Prepared) : NatMatrix :=
  (rowIndices z).map (fun i=>row (z,i))

def tableRealizer : Realizer table :=
  composition (pair identity rowIndicesRealizer) (mapWith rowRealizer)

def prepare (z : Input) : Prepared :=
  (z.1,NetworkCapacityProgram.solve z)

def prepareRealizer : Realizer prepare :=
  pair first NetworkCapacityProgram.solveRealizer

def output (z : Input) : NatMatrix := table (prepare z)
def outputRealizer : Realizer output := composition prepareRealizer tableRealizer

lemma cell_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (i : Fin m) (j : Fin n) :
    cell (prepare (data r c b),(i.val,j.val))=
      LayeredTableNetwork.decode (BoundedTableFeasibility.computedFlow r c b) i j := by
  let f := EdmondsKarpAlgorithm.maxFlow (BoundedTableFeasibility.networkCapacity r c b)
    (BoundedTableFeasibility.vertices m n LayeredTableNetwork.source)
    (BoundedTableFeasibility.vertices m n LayeredTableNetwork.sink)
  have he := flowEntry_code f
    (BoundedTableFeasibility.vertices m n (LayeredTableNetwork.row i))
    (BoundedTableFeasibility.vertices m n (LayeredTableNetwork.column j))
  simp only [index_vertices,LayeredTableNetwork.row,LayeredTableNetwork.column,index] at he
  have hlen : (data r c b).1.1.length=m := by simp only [data,List.length_ofFn]
  dsimp only [cell,prepare]
  rw [hlen,NetworkCapacityProgram.solve_code,he]
  change (ForestAffineProgram.signedParts (f _ _)).1-
    (ForestAffineProgram.signedParts (f _ _)).2=(f _ _).toNat
  exact signedParts_toNat _

lemma output_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    output (data r c b)=natCode
      (LayeredTableNetwork.decode (BoundedTableFeasibility.computedFlow r c b)) := by
  simp only [output,table,row,rowIndices,columnIndices,prepare,data,List.length_ofFn,
    DirectedBFSCode.range_eq_map,←List.ofFn_eq_map,List.map_ofFn,natCode]
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  exact cell_code r c b i j

/-- The computed list output encodes a table with the supplied margins and
bounds whenever the concrete feasibility test accepts. -/
theorem output_correct {m n : ℕ} (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (ht : NetworkFeasibilityProgram.test (data r c b)=true) :
    ∃ X, output (data r c b)=natCode X ∧ HasMargins X r c ∧ ∀ i j,X i j≤b i j := by
  have hp : (∑ i,r i)=∑ j,c j ∧
      LayeredTableNetwork.value (BoundedTableFeasibility.computedFlow r c b)=∑ i,(r i:ℤ) := by
    simpa only [NetworkFeasibilityProgram.test_eq_feasible,
      BoundedTableFeasibility.feasibleTest,decide_eq_true_eq] using ht
  exact ⟨_,output_code r c b,LayeredTableNetwork.decode_boundedTable r c b _
    (BoundedTableFeasibility.computedFlow_feasible hEK r c b) hp.2 hp.1⟩

end ContingencyTables.NetworkTableProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ComputedTableTightening
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact table bijection for the computed attained endpoints

The endpoint hypotheses of the translation lemma are discharged by the
executed minimum and maximum searches, conditional only on EK1972.
-/

namespace ContingencyTables.ComputedTableTightening

open TableTightening
open scoped Classical

variable {m n : ℕ}

def lower (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (i : Fin m) (j : Fin n) : ℕ :=
  CellMinimumProgram.minimum (NetworkVertexCode.data r c b,(i.val,j.val))
def upper (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (i : Fin m) (j : Fin n) : ℕ :=
  CellMaximumProgram.maximum (NetworkVertexCode.data r c b,(i.val,j.val))

variable (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
  (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
  (hne : ∃ X,Feasible r c b X)

include hEK hne

lemma lower_le {X : Fin m→Fin n→ℕ} (hX : Feasible r c b X)
    (i : Fin m) (j : Fin n) : lower r c b i j≤X i j := by
  obtain ⟨Y,_,_,he,hy⟩ := CellMinimumProgram.minimum_correct hEK r c b i j hne
  have h := hy X hX.1 hX.2
  simpa only [he,lower] using h

lemma le_upper {X : Fin m→Fin n→ℕ} (hX : Feasible r c b X)
    (i : Fin m) (j : Fin n) : X i j≤upper r c b i j := by
  obtain ⟨Y,_,_,he,hy⟩ := CellMaximumProgram.maximum_correct hEK r c b i j hne
  have h := hy X hX.1 hX.2
  simpa only [he,upper] using h

lemma lower_attained (i : Fin m) (j : Fin n) :
    ∃ X,Feasible r c b X ∧ X i j=lower r c b i j := by
  obtain ⟨X,hm,hb,he,_⟩ := CellMinimumProgram.minimum_correct hEK r c b i j hne
  exact ⟨X,⟨hm,hb⟩,he⟩

lemma upper_attained (i : Fin m) (j : Fin n) :
    ∃ X,Feasible r c b X ∧ X i j=upper r c b i j := by
  obtain ⟨X,hm,hb,he,_⟩ := CellMaximumProgram.maximum_correct hEK r c b i j hne
  exact ⟨X,⟨hm,hb⟩,he⟩

lemma upper_le_bound (i : Fin m) (j : Fin n) : upper r c b i j≤b i j := by
  obtain ⟨X,hX,he⟩ := upper_attained hEK r c b hne i j
  simpa only [←he] using hX.2 i j

omit hEK hne in
def newRows : Fin m→ℕ := rows r (lower r c b)
omit hEK hne in
def newColumns : Fin n→ℕ := columns c (lower r c b)
omit hEK hne in
def newBounds : Fin m→Fin n→ℕ := bounds (lower r c b) (upper r c b)

noncomputable def tighten (X : BoundedTable r c b) :
    BoundedTable (newRows r c b) (newColumns r c b) (newBounds r c b) := by
  have h := subtract_feasible r c b (lower r c b) (upper r c b)
    (fun Y hY i j=>lower_le hEK r c b hne hY i j)
    (fun Y hY i j=>le_upper hEK r c b hne hY i j) ⟨X.val.property,X.property⟩
  exact ⟨⟨subtract X.val.val (lower r c b),h.1⟩,h.2⟩

noncomputable def restore
    (Y : BoundedTable (newRows r c b) (newColumns r c b) (newBounds r c b)) :
    BoundedTable r c b := by
  have h := add_feasible r c b (lower r c b) (upper r c b) hne
    (fun X hX i j=>lower_le hEK r c b hne hX i j)
    (upper_le_bound hEK r c b hne) ⟨Y.val.property,Y.property⟩
  exact ⟨⟨add Y.val.val (lower r c b),h.1⟩,h.2⟩

noncomputable def tighteningEquiv : BoundedTable r c b ≃
    BoundedTable (newRows r c b) (newColumns r c b) (newBounds r c b) where
  toFun := tighten hEK r c b hne
  invFun := restore hEK r c b hne
  left_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    exact add_subtract X.val.val (lower r c b)
      (fun i j=>lower_le hEK r c b hne ⟨X.val.property,X.property⟩ i j)
  right_inv Y := by
    apply Subtype.ext
    apply Subtype.ext
    exact subtract_add Y.val.val (lower r c b)

theorem attained_endpoints :
    (∀ i j,∃ Y,HasMargins Y (newRows r c b) (newColumns r c b) ∧
      (∀ a d,Y a d≤newBounds r c b a d) ∧ Y i j=0) ∧
    (∀ i j,∃ Y,HasMargins Y (newRows r c b) (newColumns r c b) ∧
      (∀ a d,Y a d≤newBounds r c b a d) ∧ Y i j=newBounds r c b i j) := by
  have h := endpoints r c b (lower r c b) (upper r c b)
    (fun X hX i j=>lower_le hEK r c b hne hX i j)
    (fun X hX i j=>le_upper hEK r c b hne hX i j)
    (lower_attained hEK r c b hne) (upper_attained hEK r c b hne)
  simpa only [TightFeasible,and_assoc,newRows,newColumns,newBounds] using h

end ContingencyTables.ComputedTableTightening

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_TightenedInputProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed endpoint translation and a feasible tightened baseline

The lower and upper matrices are computed by the endpoint scans. Binary
subtraction updates the capacities and both margins, then the same proved
flow program produces a baseline table in the translated instance.
-/

namespace ContingencyTables.TightenedInputProgram

open MatchingFPRAS.TreeTyped Polynomial ResidualGraphProgram NetworkVertexCode
open scoped BigOperators Classical

def rowValueRealizer : Realizer rowValue :=
  composition (pair
    (composition (pair (composition (composition (composition first first) first) first) second)
      (getDFast 0))
    (composition (composition (pair (composition (composition first first) second) second)
      (getDFast [])) listSum)) subtract
def columnValueRealizer : Realizer columnValue :=
  composition (pair
    (composition (pair (composition (composition (composition first first) first) second) second)
      (getDFast 0))
    (composition (composition
      (pair (composition first first) second) BoundedComplementProgram.columnValuesRealizer)
      listSum)) subtract
def positionRealizer : Realizer position := pair (composition first second) second
def cellValueRealizer : Realizer cellValue :=
  composition (pair
    (composition (pair (composition (composition first first) second) positionRealizer)
      capacityEntryRealizer)
    (composition (pair (composition (composition (composition first first) first) second)
      positionRealizer) capacityEntryRealizer)) subtract
def rowIndicesRealizer : Realizer rowIndices :=
  composition first BoundedComplementProgram.rowIndicesRealizer
def columnIndicesRealizer : Realizer columnIndices :=
  composition first BoundedComplementProgram.columnIndicesRealizer
def capacityRowRealizer : Realizer capacityRow :=
  composition (pair identity (composition first columnIndicesRealizer)) (mapWith cellValueRealizer)
def translateRealizer : Realizer translate :=
  pair (pair
    (composition (pair identity rowIndicesRealizer) (mapWith rowValueRealizer))
    (composition (pair identity columnIndicesRealizer) (mapWith columnValueRealizer)))
    (composition (pair identity rowIndicesRealizer) (mapWith capacityRowRealizer))

def prepare (z : Input) : TranslationInput :=
  ((z.1,EndpointMatrixProgram.lowerMatrix z),EndpointMatrixProgram.upperMatrix z)
def prepareRealizer : Realizer prepare :=
  pair (pair first EndpointMatrixProgram.lowerMatrixRealizer) EndpointMatrixProgram.upperMatrixRealizer

def compute (z : Input) : Input := translate (prepare z)
def computeRealizer : Realizer compute :=
  composition (f:=prepare) (g:=translate) prepareRealizer translateRealizer

lemma compute_code {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    compute (data r c b)=data (ComputedTableTightening.newRows r c b)
      (ComputedTableTightening.newColumns r c b) (ComputedTableTightening.newBounds r c b) := by
  unfold compute prepare
  rw [EndpointMatrixProgram.lowerMatrix_code,EndpointMatrixProgram.upperMatrix_code]
  exact translate_code r c (ComputedTableTightening.lower r c b) (ComputedTableTightening.upper r c b)

def baseline (z : Input) : NatMatrix := NetworkTableProgram.output (compute z)
def baselineRealizer : Realizer baseline :=
  composition (f:=compute) (g:=NetworkTableProgram.output) computeRealizer NetworkTableProgram.outputRealizer

/-- Endpoint translation preserves a concrete feasible witness. -/
theorem translated_nonempty {m n : ℕ} (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) :
    ∃ Y,HasMargins Y (ComputedTableTightening.newRows r c b)
      (ComputedTableTightening.newColumns r c b) ∧
      ∀ i j,Y i j≤ComputedTableTightening.newBounds r c b i j := by
  obtain ⟨X,hX⟩ := hne
  let x : BoundedTable r c b := ⟨⟨X,hX.1⟩,hX.2⟩
  let y := ComputedTableTightening.tighten hEK r c b ⟨X,hX⟩ x
  exact ⟨y.val.val,y.val.property,y.property⟩

/-- The stored baseline comes from the executed flow decoder, with all
its margin and capacity obligations discharged by endpoint translation. -/
theorem baseline_correct {m n : ℕ} (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) :
    ∃ Y,baseline (data r c b)=natCode Y ∧
      HasMargins Y (ComputedTableTightening.newRows r c b)
        (ComputedTableTightening.newColumns r c b) ∧
      ∀ i j,Y i j≤ComputedTableTightening.newBounds r c b i j := by
  have ht := (NetworkFeasibilityProgram.test_correct hEK
    (ComputedTableTightening.newRows r c b)
    (ComputedTableTightening.newColumns r c b)
    (ComputedTableTightening.newBounds r c b)).mpr (translated_nonempty hEK r c b hne)
  have h := NetworkTableProgram.output_correct hEK
    (ComputedTableTightening.newRows r c b)
    (ComputedTableTightening.newColumns r c b)
    (ComputedTableTightening.newBounds r c b) ht
  simpa only [baseline,compute_code] using h

end ContingencyTables.TightenedInputProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_WeightedArgmaxProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary scan selecting a greatest weighted edge

The accumulator is either empty or one stored edge. Its binary size is
bounded by the input list size even when capacities are numerically large.
-/

namespace ContingencyTables.WeightedArgmaxProgram

open MatchingFPRAS.TreeTyped Polynomial

def chooseRealizer : Realizer (fun z : Edge×Edge=>
    if z.2.2<z.1.2 then Option.some z.1 else Option.some z.2) :=
  (choose (composition compareRealizer less) (composition first some)
    (composition second some)).congr (by
      intro z
      by_cases h : z.2.2<z.1.2 <;> simp [Function.comp_apply,compareInput,h])

def advanceRealizer : Realizer advance :=
  (optionCases some chooseRealizer).congr (by
    rintro ⟨e,o⟩
    cases o <;> rfl)
def bestRealizer : Realizer best :=
  composition (f := fun xs : List Edge=>(xs,(none : Option Edge)))
    (g := fun z : List Edge×Option Edge=>z.1.foldl (fun o e=>advance (e,o)) z.2)
    (pair identity (constant none)) (fold advanceRealizer)

end ContingencyTables.WeightedArgmaxProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestEdgeChoiceProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choosing the heaviest edge between distinct forest components

The filter runs the actual finite component-search program. The maximum
scan receives only eligible stored edges and retains their binary weights.
-/

namespace ContingencyTables.ForestEdgeChoiceProgram

open MatchingFPRAS.TreeTyped WeightedArgmaxProgram FiniteGraphRootProgram
open FiniteGraphCutProgram
open scoped Classical

def queryRealizer : Realizer query :=
  pair (pair (composition first first) (composition (composition second first) first))
    (composition (composition second first) second)
def eligibleRealizer : Realizer eligible :=
  composition (composition (f := query) (g := reachableCode) queryRealizer
    reachableCodeRealizer) boolNot
def filteredRealizer : Realizer filtered :=
  composition (pair identity second) (filterWith eligibleRealizer)
def choiceRealizer : Realizer choice :=
  composition (f := filtered) (g := WeightedArgmaxProgram.best)
    filteredRealizer WeightedArgmaxProgram.bestRealizer

lemma eligible_code {n : ℕ} (T : SimpleGraph (Fin n)) [DecidableRel T.Adj]
    (es : List Edge) (u v : Fin n) (w : ℕ) :
    eligible ((graphCode T,es),((u.val,v.val),w))=true ↔ ¬T.Reachable u v := by
  simp only [eligible,query,reachableCode,Bool.not_eq_true',decide_eq_false_iff_not,
    reached_mem_iff]

end ContingencyTables.ForestEdgeChoiceProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestJoinProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical adjacency-list insertion of a forest edge

Every row is rebuilt from the stored vertex range. This keeps the graph
encoding canonical and bounds all intermediate lists by the vertex count.
-/

namespace ContingencyTables.ForestJoinProgram

open MatchingFPRAS.TreeTyped Polynomial FiniteGraphRootProgram SimpleGraph

def keepRealizer : Realizer keep := by
  let row : Realizer (fun z : TestInput=>z.1.2) := composition first second
  let u : Realizer (fun z : TestInput=>z.1.1.2.1) :=
    composition (composition (composition first first) second) first
  let v : Realizer (fun z : TestInput=>z.1.1.2.2) :=
    composition (composition (composition first first) second) second
  let old : Realizer (fun z : TestInput=>decide (z.2∈z.1.1.1.getD z.1.2 [])) :=
    composition (pair
      (composition (pair (composition (composition first first) first) row) (getDFast []))
      second) membership
  exact composition (pair old
    (composition (pair
      (composition (pair (composition (pair row u) natEqual)
        (composition (pair second v) natEqual)) boolAnd)
      (composition (pair (composition (pair row v) natEqual)
        (composition (pair second u) natEqual)) boolAnd)) boolOr)) boolOr

def verticesRealizer : Realizer vertices :=
  composition (composition first first) indicesRealizer
def rowRealizer : Realizer row :=
  composition (pair identity verticesRealizer) (filterWith keepRealizer)
def joinRealizer : Realizer join :=
  composition (pair identity (composition first indicesRealizer)) (mapWith rowRealizer)

lemma keep_code {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v r a : Fin n) (hne : u≠v) :
    keep (((graphCode G,(u.val,v.val)),r.val),a.val)=true ↔
      (G⊔edge u v).Adj a r := by
  simp only [keep,graphCode_getD,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
  rw [adjacencyRow_mem]
  have he : (∃ w : Fin n,w.val=a.val ∧ G.Adj w r) ↔ G.Adj a r := by
    constructor
    · rintro ⟨w,hw,hwr⟩
      exact (Fin.ext hw) ▸ hwr
    · intro har
      exact ⟨a,rfl,har⟩
  rw [he]
  simp only [Fin.val_inj,SimpleGraph.sup_adj,SimpleGraph.edge_adj]
  constructor
  · rintro (h|(⟨hr,ha⟩|⟨hr,ha⟩))
    · exact Or.inl h
    · subst r; subst a; exact Or.inr ⟨Or.inr ⟨rfl,rfl⟩,Ne.symm hne⟩
    · subst r; subst a; exact Or.inr ⟨Or.inl ⟨rfl,rfl⟩,hne⟩
  · rintro (h|⟨(⟨ha,hr⟩|⟨ha,hr⟩),_⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨hr,ha⟩)
    · exact Or.inr (Or.inl ⟨hr,ha⟩)

lemma join_code {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) (hne : u≠v) :
    join (graphCode G,(u.val,v.val))=graphCode (G⊔edge u v) := by
  simp only [join,indices,graphCode_length,DirectedBFSCode.range_eq_map,←List.ofFn_eq_map,
    List.map_ofFn]
  change List.ofFn (fun r : Fin n=>row ((graphCode G,(u.val,v.val)),r.val)) =
    List.ofFn (adjacencyRow (G⊔edge u v))
  apply congrArg List.ofFn
  funext r
  simp only [row,vertices,indices,graphCode_length,
    DirectedBFSCode.range_eq_map,List.filter_map,adjacencyRow]
  apply congrArg (List.map Fin.val)
  apply List.filter_congr
  intro a _
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq,Function.comp_apply] using keep_code G u v r a hne

end ContingencyTables.ForestJoinProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_LargeEdgeCatalogProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed weighted catalog of large cells

Rows and columns are indexed by their stored margin-list lengths. The
catalog contains each retained large cell once, with its actual binary
capacity and its row/column graph endpoints.
-/

namespace ContingencyTables.LargeEdgeCatalogProgram

open MatchingFPRAS.TreeTyped ProfilePrograms DensePrograms WeightedArgmaxProgram

def vertexCountRealizer : Realizer vertexCount :=
  composition (pair
    (composition (composition (composition first first) first) listLength)
    (composition (composition (composition first first) second) listLength)) add
def endpointsRealizer : Realizer endpoints :=
  pair (composition second first)
    (composition (pair
      (composition (composition (composition (composition first first) first) first) listLength)
      (composition second second)) add)
def entryRealizer : Realizer entry := pair endpointsRealizer CompanionCellCatalog.entryRealizer
def largeRealizer : Realizer large :=
  composition CompanionCellCatalog.retainedTestRealizer boolNot
def cellsRealizer : Realizer cells :=
  composition (pair identity (composition (composition first first) cellPairsRealizer))
    (filterWith largeRealizer)
def catalogRealizer : Realizer catalog :=
  composition (pair identity cellsRealizer) (mapWith entryRealizer)

end ContingencyTables.LargeEdgeCatalogProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestGreedyProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial execution of the component-greedy forest loop

The immutable weighted edge catalog is scanned after every insertion.
There are at most the square of the stored vertex count many iterations;
all adjacency rows stay inside that fixed vertex range.
-/

namespace ContingencyTables.ForestGreedyProgram

open MatchingFPRAS.TreeTyped Polynomial FiniteGraphRootProgram WeightedArgmaxProgram

def insertRealizer : Realizer insert :=
  composition (f := fun z : State×Edge=>(z.1.1,z.2.1)) (g := ForestJoinProgram.join)
    (pair (composition first first) (composition second first)) ForestJoinProgram.joinRealizer
def updateRealizer : Realizer update :=
  composition (f := fun s : State=>(s,ForestEdgeChoiceProgram.choice s))
    (g := fun z : State×Option Edge=>z.2.elim z.1.1 (fun e=>insert (z.1,e)))
    (pair identity ForestEdgeChoiceProgram.choiceRealizer) (optionCases first insertRealizer)
def advanceRealizer : Realizer advance :=
  pair (composition (f := fun z : ℕ×State=>z.2) (g := update) second updateRealizer)
    (composition second second)
def slotsRealizer : Realizer slots :=
  composition (f := fun s : State=>s.1.length*s.1.length) (g := List.range)
    (composition (f := fun s : State=>(s.1.length,s.1.length))
      (g := fun z : ℕ×ℕ=>z.1*z.2)
      (pair (composition first listLength) (composition first listLength)) multiply) range
def executeRealizer : Realizer execute :=
  composition (f := fun s : State=>(slots s,s))
    (g := fun z : List ℕ×State=>z.1.foldl (fun s a=>advance (a,s)) z.2)
    (pair slotsRealizer identity) (fold advanceRealizer)
def emptyGraphRealizer : Realizer emptyGraph :=
  composition (composition LargeEdgeCatalogProgram.vertexCountRealizer range) (map (constant []))
def prepareRealizer : Realizer prepare :=
  pair emptyGraphRealizer LargeEdgeCatalogProgram.catalogRealizer
def forestRealizer : Realizer forest :=
  composition (composition (f:=prepare) (g:=execute) prepareRealizer executeRealizer) first

end ContingencyTables.ForestGreedyProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestGreedySemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Correctness of the actual binary forest loop

The invariant refers to the adjacency list produced by the program.
The final graph is decoded directly from that list. Optimal forests
occur only as proof witnesses for the safe-edge invariant.
-/

namespace ContingencyTables.ForestGreedySemantics

open SimpleGraph MaximumForest MaximumForestExchange
open ForestGreedyProgram ForestEdgeChoiceProgram FiniteGraphRootProgram WeightedArgmaxProgram
open scoped Classical

variable {n : ℕ}

lemma chosen_spec {G T : SimpleGraph (Fin n)} {b : Sym2 (Fin n)→ℕ} {es : List Edge}
    (hC : Catalog G b es) {e : Edge} (he : choice (graphCode T,es)=some e) :
    ∃ u v : Fin n,e=((u.val,v.val),b s(u,v)) ∧ G.Adj u v ∧ ¬T.Reachable u v ∧
      ∀ a d,G.Adj a d → ¬T.Reachable a d → b s(a,d)≤b s(u,v) := by
  have hm := choice_mem he
  obtain ⟨u,v,hG,heq⟩ := hC.1 e hm.1
  subst e
  have hnu : ¬T.Reachable u v := (eligible_code T es u v _).mp hm.2
  refine ⟨u,v,rfl,hG,hnu,?_⟩
  intro a d had hn
  rcases hC.2 a d had with hmem|hmem
  · exact choice_max he hmem ((eligible_code T es a d _).mpr hn)
  · exact choice_max he hmem ((eligible_code T es d a _).mpr (fun hd=>hn hd.symm))

lemma none_spec {G T : SimpleGraph (Fin n)} {b : Sym2 (Fin n)→ℕ} {es : List Edge}
    (hC : Catalog G b es) (he : choice (graphCode T,es)=none) :
    ∀ u v,G.Adj u v → T.Reachable u v := by
  intro u v hG
  by_contra hn
  rcases hC.2 u v hG with hmem|hmem
  · have hfalse := choice_none he _ hmem
    have htrue := (eligible_code T es u v (b s(u,v))).mpr hn
    exact Bool.noConfusion (hfalse.symm.trans htrue)
  · have hfalse := choice_none he _ hmem
    have htrue := (eligible_code T es v u (b s(u,v))).mpr (fun hr=>hn hr.symm)
    exact Bool.noConfusion (hfalse.symm.trans htrue)

lemma advance_code (T : SimpleGraph (Fin n)) (es : List Edge) (u v : Fin n)
    (w : ℕ) (hne : u≠v)
    (he : choice (graphCode T,es)=some ((u.val,v.val),w)) :
    ForestGreedyProgram.advance (0,(graphCode T,es))=(graphCode (T⊔edge u v),es) := by
  simp only [ForestGreedyProgram.advance,update,he,Option.elim_some]
  change (ForestJoinProgram.join (graphCode T,(u.val,v.val)),es)=_
  rw [ForestJoinProgram.join_code T u v hne]

/-- A fuel count at least the number of missing unordered edges suffices
for the executed loop, without any tie-breaking assumption. -/
theorem iterate_optimal (G T : SimpleGraph (Fin n)) (b : Sym2 (Fin n)→ℕ)
    (es : List Edge) (hC : Catalog G b es) (hb : ∀ e∈G.edgeSet,0<b e)
    (hT : Extendible G T b) (k : ℕ)
    (hbudget : Fintype.card (Sym2 (Fin n))≤edgeCount T+k) :
    ∃ F : SimpleGraph (Fin n),iterate k (graphCode T,es)=(graphCode F,es) ∧
      F≤G ∧ F.IsAcyclic ∧
        ∀ H : SimpleGraph (Fin n),H≤G → H.IsAcyclic → weight H b≤weight F b := by
  induction k generalizing T with
  | zero=>
    have hnone : choice (graphCode T,es)=none := by
      cases he : choice (graphCode T,es) with
      | none=>rfl
      | some e=>
        obtain ⟨u,v,_,hg,hn,_⟩ := chosen_spec hC he
        have hc := card_add T hn hg.ne
        have hle := edgeCount_le (T⊔edge u v)
        omega
    exact ⟨T,rfl,finished G T b hT (none_spec hC hnone)⟩
  | succ k ih=>
    cases he : choice (graphCode T,es) with
    | none=>exact ⟨T,iterate_none he _,finished G T b hT (none_spec hC he)⟩
    | some e=>
      obtain ⟨u,v,rfl,hg,hn,hbest⟩ := chosen_spec hC he
      have hnext := safe_edge G T b hb hT hg hn hbest
      have hc := card_add T hn hg.ne
      obtain ⟨F,hF,hopt⟩ := ih (T⊔edge u v) hnext (by omega)
      refine ⟨F,?_,hopt⟩
      rw [iterate,advance_code T es u v _ hg.ne he]
      convert hF using 1
      all_goals try with_reducible_and_instances rfl
      congr 3

lemma decoded_graphCode (G : SimpleGraph (Fin n)) : decoded (graphCode G)=G := by
  ext u v
  simp only [decoded,graphCode_getD,adjacencyRow_mem]
  constructor
  · rintro ⟨_,⟨a,ha,haG⟩,_⟩
    exact (Fin.ext ha) ▸ haG
  · intro h
    exact ⟨h.ne,⟨u,rfl,h⟩,⟨v,rfl,h.symm⟩⟩

/-- The graph is decoded from the literal result list, not selected from
an existence proof. -/
theorem execute_optimal (G T : SimpleGraph (Fin n)) (b : Sym2 (Fin n)→ℕ)
    (es : List Edge) (hC : Catalog G b es) (hb : ∀ e∈G.edgeSet,0<b e)
    (hT : Extendible G T b) :
    let F := decoded (execute (graphCode T,es)).1
    F≤G ∧ F.IsAcyclic ∧
      ∀ H : SimpleGraph (Fin n),H≤G → H.IsAcyclic → weight H b≤weight F b := by
  obtain ⟨F,hF,hopt⟩ := iterate_optimal G T b es hC hb hT (n*n)
    (by have h := unordered_pair_budget (n:=n); omega)
  rw [execute_iterate,graphCode_length,hF]
  simpa only [decoded_graphCode] using hopt

end ContingencyTables.ForestGreedySemantics

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ComputedLargeForest
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed maximum-capacity forest on the original cell vertices

The program uses the concrete row-then-column natural indexing. The
returned adjacency list is decoded and transported back to the original
bipartite vertex type. Its catalog and optimality obligations follow
from the stored capacities, rather than supplied correctness predicates.
-/

namespace ContingencyTables.ComputedLargeForest

open SimpleGraph MaximumForest ForestCapacity ForestGreedySemantics
open FiniteGraphRootProgram LargeEdgeCatalogProgram
open scoped BigOperators Classical

variable {m n : ℕ}

/-- The executed list program gives a maximum-capacity forest on the
actual row and column vertices. -/
theorem computed_spec (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (W : ℕ) (hW : 1≤W) :
    computed r c b W ≤ cellGraph (small b W) ∧ (computed r c b W).IsAcyclic ∧
    ∀ F : SimpleGraph (Fin m⊕Fin n),F ≤ cellGraph (small b W) → F.IsAcyclic →
      weight F (capacity b)≤weight (computed r c b W) (capacity b) := by
  have ht := execute_optimal (graph b W) ⊥ (capacities b)
    (catalog (NetworkVertexCode.data r c b,W)) (catalog_correct r c b W)
    (capacity_positive b W hW) (MaximumForestExchange.bottom_extendible _ _)
  have hzero (d : DecidableRel (⊥ : SimpleGraph (Fin (m+n))).Adj) :
      @graphCode (m+n) ⊥ d=ForestGreedyProgram.emptyGraph (NetworkVertexCode.data r c b,W) := by
    symm
    simp only [ForestGreedyProgram.emptyGraph,vertexCount_code,DirectedBFSCode.range_eq_map,
      ←List.ofFn_eq_map,List.map_ofFn,graphCode]
    apply congrArg List.ofFn
    funext v
    simp [adjacencyRow]
  dsimp only at ht
  rw [hzero] at ht
  change let T:=decoded (ForestGreedyProgram.forest (NetworkVertexCode.data r c b,W));
    T≤graph b W ∧ T.IsAcyclic ∧
      ∀ H,H≤graph b W → H.IsAcyclic → weight H (capacities b)≤weight T (capacities b) at ht
  dsimp only at ht
  let T : SimpleGraph (Fin (m+n)) :=
    decoded (ForestGreedyProgram.forest (NetworkVertexCode.data r c b,W))
  have hback : (T.comap vertexEquiv).map vertexEquiv.toEmbedding=T := by
    rw [←SimpleGraph.comap_symm]
    ext u v
    change T.Adj (vertexEquiv (vertexEquiv.symm u))
      (vertexEquiv (vertexEquiv.symm v)) ↔ T.Adj u v
    simp only [Equiv.apply_symm_apply]
  have hT : T.comap vertexEquiv ≤ cellGraph (small b W) := by
    intro u v huv
    exact (SimpleGraph.map_adj_apply (G:=cellGraph (small b W))
      (f:=vertexEquiv.toEmbedding) (a:=u) (b:=v)).mp (ht.1 huv)
  refine ⟨hT,ht.2.1.of_comap vertexEquiv.toEmbedding,?_⟩
  intro F hF hac
  have hle : F.map vertexEquiv.toEmbedding≤graph b W := map_monotone _ hF
  have ha : (F.map vertexEquiv.toEmbedding).IsAcyclic :=
    (SimpleGraph.Iso.map vertexEquiv F).isAcyclic_iff.mp hac
  have hw := ht.2.2 (F.map vertexEquiv.toEmbedding) hle ha
  have h1 := weight_transport vertexEquiv F (capacity b)
  have h2 := weight_transport vertexEquiv (T.comap vertexEquiv) (capacity b)
  rw [hback] at h2
  exact h1.symm.trans_le (hw.trans_eq h2)

end ContingencyTables.ComputedLargeForest

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ComputedCompanionInstance
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A literal companion instance from binary bounded margins

All operational data are read from the executed endpoint, flow, and
maximum-forest programs. The existential endpoint witnesses are used
only in the terminal-mass proof, never to define an executed output.
-/

namespace ContingencyTables.ComputedCompanionInstance

open CompanionFactorialApplication ComputedTableTightening
open scoped BigOperators Classical

variable {m n : ℕ}

def baseline (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (i : Fin m) (j : Fin n) : ℕ :=
  ((TightenedInputProgram.baseline (NetworkVertexCode.data r c b)).getD i.val []).getD j.val 0

lemma baseline_properties (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) :
    HasMargins (baseline r c b) (newRows r c b) (newColumns r c b) ∧
      ∀ i j,baseline r c b i j≤newBounds r c b i j := by
  obtain ⟨Y,hcode,hm,hb⟩ := TightenedInputProgram.baseline_correct hEK r c b hne
  have he : baseline r c b=Y := by
    funext i j
    simp only [baseline,hcode,ResidualGraphProgram.natCode,
      List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,j.isLt,
      dite_true,Option.getD_some,Fin.eta]
  simpa only [he] using And.intro hm hb

/-- The package consumed by the proved factorial, terminal, and oracle
lemmas. Its forest and baseline are decoded executed values. -/
noncomputable def instanceData (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (W : ℕ) (hW : 2≤W) :
    Instance (Fin m) (Fin n) where
  small:=ComputedLargeForest.small (newBounds r c b) W
  b:=newBounds r c b
  T:=ComputedLargeForest.computed (newRows r c b) (newColumns r c b) (newBounds r c b) W
  hTG:=(ComputedLargeForest.computed_spec _ _ _ W (by omega)).1
  hT:=(ComputedLargeForest.computed_spec _ _ _ W (by omega)).2.1
  hmax:=(ComputedLargeForest.computed_spec _ _ _ W (by omega)).2.2
  r:=fun i=>(newRows r c b i:ℤ)
  c:=fun j=>(newColumns r c b j:ℤ)
  X:=fun i j=>(baseline r c b i j:ℤ)
  d:=1+m*n
  W:=W
  hd:=by omega
  hcard:=by simp only [Fintype.card_fin]; omega
  hW:=hW
  hlarge:=by
    intro i j hs
    have hb : W≤newBounds r c b i j := by
      simpa only [ComputedLargeForest.small,decide_eq_false_iff_not,not_lt] using hs
    exact ⟨hb,(show 1≤W by omega).trans hb⟩
  hsmall:=by
    intro i j hs
    simpa only [ComputedLargeForest.small,decide_eq_true_eq] using hs
  hX:=by
    intro i j
    exact ⟨Nat.cast_nonneg _,by exact_mod_cast (baseline_properties hEK r c b hne).2 i j⟩
  hXr:=by
    intro i
    exact_mod_cast (baseline_properties hEK r c b hne).1.1 i
  hXc:=by
    intro j
    exact_mod_cast (baseline_properties hEK r c b hne).1.2 j

/-- The endpoint assumption in the terminal proof follows from the
executed searches. The witnesses here are mathematical proof data. -/
noncomputable def endpoints (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (W : ℕ) (hW : 2≤W) :
    CompanionTerminalMass.Endpoints (instanceData hEK r c b hne W hW) := by
  have hends:=ComputedTableTightening.attained_endpoints hEK r c b hne
  let lo : ∀ i j,Fin m→Fin n→ℕ:=fun i j=>Classical.choose (hends.1 i j)
  let hi : ∀ i j,Fin m→Fin n→ℕ:=fun i j=>Classical.choose (hends.2 i j)
  have hlo (i : Fin m) (j : Fin n) := Classical.choose_spec (hends.1 i j)
  have hhi (i : Fin m) (j : Fin n) := Classical.choose_spec (hends.2 i j)
  refine { lowerTable:=fun t i j=>(lo t.val.1 t.val.2 i j:ℤ)
           upperTable:=fun t i j=>(hi t.val.1 t.val.2 i j:ℤ)
           lowerBounds:=?_,upperBounds:=?_,lowerRows:=?_,lowerColumns:=?_,
           upperRows:=?_,upperColumns:=?_,lowerAttains:=?_,upperAttains:=?_ }
  · intro t i j
    exact ⟨Nat.cast_nonneg _,by exact_mod_cast (hlo t.val.1 t.val.2).2.1 i j⟩
  · intro t i j
    exact ⟨Nat.cast_nonneg _,by exact_mod_cast (hhi t.val.1 t.val.2).2.1 i j⟩
  · intro t i
    change (∑ j,(lo t.val.1 t.val.2 i j:ℤ))=(newRows r c b i:ℤ)
    exact_mod_cast (hlo t.val.1 t.val.2).1.1 i
  · intro t j
    change (∑ i,(lo t.val.1 t.val.2 i j:ℤ))=(newColumns r c b j:ℤ)
    exact_mod_cast (hlo t.val.1 t.val.2).1.2 j
  · intro t i
    change (∑ j,(hi t.val.1 t.val.2 i j:ℤ))=(newRows r c b i:ℤ)
    exact_mod_cast (hhi t.val.1 t.val.2).1.1 i
  · intro t j
    change (∑ i,(hi t.val.1 t.val.2 i j:ℤ))=(newColumns r c b j:ℤ)
    exact_mod_cast (hhi t.val.1 t.val.2).1.2 j
  · intro t
    exact_mod_cast (hlo t.val.1 t.val.2).2.2
  · intro t
    exact_mod_cast (hhi t.val.1 t.val.2).2.2

end ContingencyTables.ComputedCompanionInstance

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_ComputedCountingParameters
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting schedules computed from the original bounded margins

The capacity-bit sum is formed after the executed endpoint translation.
All remaining dimensions, precisions, cutoffs and phase counts use the
proved rational/natural formulas. No numeric schedule hypothesis is
left to an external caller.
-/

namespace ContingencyTables.ComputedCountingParameters

open CompanionFactorialApplication CompanionOracleDensity RootedPhaseHistory GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

def capacityBits (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) : ℕ :=
  ∑ a : Fin m×Fin n,(ComputedTableTightening.newBounds r c b a.1 a.2+1).size

def coefficient (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) : ℕ :=
  CountingTerminalSchedule.coefficient (capacityBits r c b) (dimensionAllowance (m:=m) (n:=n))
    (epsilon/2)

def binCount (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) : ℕ :=
  16*coefficient r c b epsilon*(dimensionAllowance (m:=m) (n:=n))^2

def cutoff (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) : ℕ :=
  100*dimensionAllowance (m:=m) (n:=n)*binCount r c b epsilon

def phases (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) : ℕ :=
  10*coefficient r c b epsilon*(dimensionAllowance (m:=m) (n:=n))^2*(cutoff r c b epsilon+1)

lemma coefficient_pos (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) (he : 0<epsilon) : 0 < coefficient r c b epsilon :=
  CountingTerminalSchedule.coefficient_pos _ _ (by unfold dimensionAllowance; omega)
    (epsilon/2) (by positivity)

lemma binCount_pos (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) (he : 0<epsilon) : 0<binCount r c b epsilon := by
  have hC:=coefficient_pos r c b epsilon he
  have hd : 0<dimensionAllowance (m:=m) (n:=n) := by unfold dimensionAllowance; omega
  unfold binCount
  positivity

lemma cutoff_two (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) (he : 0<epsilon) : 2 ≤ cutoff r c b epsilon := by
  have hK:=binCount_pos r c b epsilon he
  have hd : 1≤dimensionAllowance (m:=m) (n:=n) := by unfold dimensionAllowance; omega
  unfold cutoff
  nlinarith

def data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon) :
    Instance (Fin m) (Fin n) :=
  ComputedCompanionInstance.instanceData hEK r c b hne (cutoff r c b epsilon)
    (cutoff_two r c b epsilon he)

lemma cutoff_eq (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon) :
    (data hEK r c b hne epsilon he).W=
      100*(data hEK r c b hne epsilon he).d*binCount r c b epsilon := rfl

/-- The canonical zero grid point is valid even when there are no free
coordinates; its construction does not search the geometric state space. -/
def start (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon) :
    Grid (I:=Fin (dimension (data hEK r c b hne epsilon he))) (binCount r c b epsilon) :=
  fun _=>⟨0,le_refl _,by have h:=binCount_pos r c b epsilon he; omega⟩

def settings (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon) :
    Settings (data hEK r c b hne epsilon he) :=
  RootedCountingSchedule.settings (data hEK r c b hne epsilon he)
    (coefficient r c b epsilon) (binCount r c b epsilon) (phases r c b epsilon)
    (capacityBits r c b) (binCount_pos r c b epsilon he) (cutoff_eq hEK r c b hne epsilon he).ge
    (epsilon/2) (start hEK r c b hne epsilon he)

end
end ContingencyTables.ComputedCountingParameters

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionUniformPhaseBounds
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed common width covers every actual phase and marker -/
namespace ContingencyTables.CompanionUniformPhaseWidth
open MatchingFPRAS CompanionFactorialApplication CompanionOracleDensity
open RootedPhaseHistory GridBoundary
open scoped BigOperators Classical
noncomputable section
variable {m n : ℕ}

def data (A : Instance (Fin m) (Fin n)) (s : Settings A) (epsilon : TreeFraction.Fraction)
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) s.K) : Input :=
  CompanionRestartInitializer.data A s.C s.K s.H (CompanionTargetMixing.restartTime A s.H s.L)
    s.N s.n s.L epsilon z v

end
end ContingencyTables.CompanionUniformPhaseWidth

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_ComputedCountingWords
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual counting experiment on original bounded-table inputs

This is the positive-label branch of the computed-input experiment.
Its output is the stored adaptive rational estimate, after independent
median amplification. Only the cited analytic/flow inputs are external.
-/

namespace ContingencyTables.ComputedCountingWords

open CompanionFactorialApplication CommonBasesFPRAS GridBoundary
open ComputedCountingParameters
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

def root (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon) :
    RootedCompletion.Selection (data hEK r c b hne epsilon he).T :=
  RootedCompletion.rowColumn _

def bitCount (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon)
    (delta : ℚ) : ℕ :=
  RootedCountingAmplification.bitCount (data hEK r c b hne epsilon he)
    (settings hEK r c b hne epsilon he) delta

def estimate (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon)
    (delta : ℚ) (bits : Fin (bitCount hEK r c b hne epsilon he delta)→Bool) : ℚ :=
  RootedCountingAmplification.estimate (data hEK r c b hne epsilon he)
    (root hEK r c b hne epsilon he) (settings hEK r c b hne epsilon he) delta bits

end
end ContingencyTables.ComputedCountingWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_ComputedCountingZero
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed zero-label counting branch

When all retained capacities vanish, the actual direct weight estimator
replaces the phase walk. Its target is still the original bounded-table
count, transported through the executed endpoint translation.
-/

namespace ContingencyTables.ComputedCountingZero

open CommonBasesFPRAS CompanionFactorialApplication GridBoundary
open CompanionOracleDensity CompanionTerminalApplication
open ComputedCountingParameters
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

def zeroBits (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon)
    (delta : ℚ) : ℕ :=
  medianEstimatorBits (data hEK r c b hne epsilon he) (coefficient r c b epsilon)
    (binCount r c b epsilon)
    (finalPhase (data hEK r c b hne epsilon he) (capacityBits r c b) ((epsilon/2:ℚ):ℝ))
    ((epsilon/2)/2) delta

def zeroEstimate (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon)
    (delta : ℚ) (bits : Fin (zeroBits hEK r c b hne epsilon he delta)→Bool) : ℚ :=
  RootedOracleDensity.medianEstimate (data hEK r c b hne epsilon he)
    (ComputedCountingWords.root hEK r c b hne epsilon he) (coefficient r c b epsilon)
    (fun _=>0) (binCount r c b epsilon) (binCount_pos r c b epsilon he)
    (cutoff_eq hEK r c b hne epsilon he).ge
    (finalPhase (data hEK r c b hne epsilon he) (capacityBits r c b) ((epsilon/2:ℚ):ℝ))
    ((epsilon/2)/2) delta (start hEK r c b hne epsilon he) bits

end
end ContingencyTables.ComputedCountingZero

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingCoefficientProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The terminal coefficient computed with binary natural arithmetic -/

namespace ContingencyTables.CountingCoefficientProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.TreeFraction Polynomial
open OffsetCountPrograms DensePrograms

def precisionRealizer : Realizer precision :=
  composition (f := fun e : Fraction => ceilQuotient (e.2,e.1)) (g := Nat.clog 2)
    (composition (pair second first) ceilQuotientRealizer) ceilLogTwoRealizer
def allowanceRealizer : Realizer allowance := by
  let ld : Realizer (fun z : Input => z.1.1+z.1.2) := composition first add
  let pr : Realizer (fun z : Input => precision z.2) :=
    composition (f := fun z : Input => z.2) (g := precision) second precisionRealizer
  let s : Realizer (fun z : Input => z.1.1+z.1.2+precision z.2+1) :=
    composition (composition (pair ld pr) add) successor
  exact composition (f := fun z : Input => (20,z.1.1+z.1.2+precision z.2+1))
    (g := fun p : ℕ×ℕ => p.1*p.2) (pair (constant 20) s) multiply
def numeratorRealizer : Realizer numerator := by
  let d : Realizer (fun z : Input => 2048*z.1.2) :=
    composition (f := fun z : Input => (2048,z.1.2))
      (g := fun p : ℕ×ℕ => p.1*p.2)
      (pair (constant 2048) (composition first second)) multiply
  let sq : Realizer (fun z : Input => (allowance z)^2) :=
    (composition (pair allowanceRealizer allowanceRealizer) multiply).congr
      (fun z => (pow_two _).symm)
  exact composition (pair (composition (pair d sq) multiply) (composition second second)) multiply
def coefficientRealizer : Realizer coefficient :=
  composition (f := fun z : Input => (numerator z,z.2.1)) (g := ceilQuotient)
    (pair numeratorRealizer (composition second first)) ceilQuotientRealizer

end ContingencyTables.CountingCoefficientProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingBaseProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the capacity-bit and dimension inputs to the counting schedule -/

namespace ContingencyTables.CountingBaseProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
open NetworkVertexCode

def cellBitsRealizer : Realizer cellBits :=
  (composition (composition successor toBits) listLength).congr
    (fun x => Nat.size_eq_bits_len (x+1))

def capacityBits (z : NetworkVertexCode.Input) : ℕ :=
  (((TightenedInputProgram.compute z).2.flatten).map cellBits).sum
def capacityBitsRealizer : Realizer capacityBits :=
  composition (f := fun z : NetworkVertexCode.Input => (TightenedInputProgram.compute z).2.flatten)
    (g := fun xs : List ℕ => (xs.map cellBits).sum)
    (composition (composition TightenedInputProgram.computeRealizer second) flatten)
    (composition (map cellBitsRealizer) listSum)
def dimensionRealizer : Realizer dimension :=
  composition (f := fun z : NetworkVertexCode.Input => (1,z.1.1.length*z.1.2.length))
    (g := fun p : ℕ×ℕ => p.1+p.2) (pair (constant 1)
    (composition (pair (composition (composition first first) listLength)
      (composition (composition first second) listLength)) multiply)) add

def frame (z : Input) : CountingCoefficientProgram.Input :=
  ((capacityBits z.1,dimension z.1),half z.2)
def frameRealizer : Realizer frame :=
  pair (pair
    (composition (f := fun z : Input => z.1) (g := capacityBits) first capacityBitsRealizer)
    (composition (f := fun z : Input => z.1) (g := dimension) first dimensionRealizer))
    (composition (f := fun z : Input => z.2) (g := half) second halfRealizer)

def coefficient (z : Input) : ℕ := CountingCoefficientProgram.coefficient (frame z)
def coefficientRealizer : Realizer coefficient :=
  composition (f := frame) (g := CountingCoefficientProgram.coefficient)
    frameRealizer CountingCoefficientProgram.coefficientRealizer

end ContingencyTables.CountingBaseProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingTerminalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed terminal grid width, cutoff and phase count -/

namespace ContingencyTables.CountingTerminalProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

def base (z : Input) : ℕ :=
  CountingBaseProgram.coefficient z * CountingBaseProgram.dimension z.1 * CountingBaseProgram.dimension z.1
def baseRealizer : Realizer base :=
  composition (f := fun z : Input =>
      (CountingBaseProgram.coefficient z*CountingBaseProgram.dimension z.1,CountingBaseProgram.dimension z.1))
    (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (composition (pair CountingBaseProgram.coefficientRealizer
      (composition (f := fun z : Input => z.1) (g := CountingBaseProgram.dimension)
        first CountingBaseProgram.dimensionRealizer)) multiply)
      (composition (f := fun z : Input => z.1) (g := CountingBaseProgram.dimension)
        first CountingBaseProgram.dimensionRealizer)) multiply

def binCount (z : Input) : ℕ := 16*base z
def binCountRealizer : Realizer binCount :=
  composition (f := fun z : Input => (16,base z)) (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (constant 16) baseRealizer) multiply

def cutoff (z : Input) : ℕ := 100*CountingBaseProgram.dimension z.1*binCount z
def cutoffRealizer : Realizer cutoff :=
  composition (f := fun z : Input => (100*CountingBaseProgram.dimension z.1,binCount z))
    (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (composition (f := fun z : Input => (100,CountingBaseProgram.dimension z.1))
      (g := fun p : ℕ×ℕ => p.1*p.2)
      (pair (constant 100) (composition (f := fun z : Input => z.1)
        (g := CountingBaseProgram.dimension) first CountingBaseProgram.dimensionRealizer)) multiply)
      binCountRealizer) multiply

def phases (z : Input) : ℕ := 10*base z*(cutoff z+1)
def phasesRealizer : Realizer phases :=
  composition (f := fun z : Input => (10*base z,cutoff z+1)) (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (composition (f := fun z : Input => (10,base z)) (g := fun p : ℕ×ℕ => p.1*p.2)
      (pair (constant 10) baseRealizer) multiply)
      (composition (f := cutoff) (g := fun n : ℕ => n+1) cutoffRealizer successor)) multiply

end ContingencyTables.CountingTerminalProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ComputedRootedInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rooted-oracle metadata from the executed original-input preprocessing -/

namespace ContingencyTables.ComputedRootedInput
open MatchingFPRAS MatchingFPRAS.TreeTyped
open DensePrograms NetworkVertexCode

def forestFrame (z : Input) : LargeEdgeCatalogProgram.Input :=
  (TightenedInputProgram.compute z.1,z.2)
def forestFrameRealizer : Realizer forestFrame :=
  pair (composition (f := fun z : Input => z.1) (g := TightenedInputProgram.compute)
    first TightenedInputProgram.computeRealizer) second

def catalogData (z : Input) : RootedForestCatalog.Data :=
  (((ForestGreedyProgram.forest (forestFrame z),z.2),(TightenedInputProgram.compute z.1).1),
    (TightenedInputProgram.compute z.1).2)
def catalogDataRealizer : Realizer catalogData :=
  pair (pair (pair
    (composition (f := forestFrame) (g := ForestGreedyProgram.forest)
      forestFrameRealizer ForestGreedyProgram.forestRealizer) second)
    (composition (composition (f := fun z : Input => z.1) (g := TightenedInputProgram.compute)
      first TightenedInputProgram.computeRealizer) first))
    (composition (composition (f := fun z : Input => z.1) (g := TightenedInputProgram.compute)
      first TightenedInputProgram.computeRealizer) second)

open scoped Classical

end ContingencyTables.ComputedRootedInput

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingComputedSettings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing every scalar control from the original bounded table -/

namespace ContingencyTables.CountingComputedSettings
open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram
open CountingPhaseScalarProgram

def catalog (z : Input) : RootedForestCatalog.Data :=
  ComputedRootedInput.catalogData (z.1,CountingTerminalProgram.cutoff z)
def catalogRealizer : Realizer catalog :=
  composition (f := fun z : Input => (z.1,CountingTerminalProgram.cutoff z))
    (g := ComputedRootedInput.catalogData) (pair first CountingTerminalProgram.cutoffRealizer)
    ComputedRootedInput.catalogDataRealizer

def labelCount (z : Input) : ℕ := CountingLabelCountProgram.count (catalog z)
def labelCountRealizer : Realizer labelCount :=
  composition (f := catalog) (g := CountingLabelCountProgram.count)
    catalogRealizer CountingLabelCountProgram.countRealizer

def preliminary (z : Input) : List ℕ :=
  [labelCount z,CountingTerminalProgram.cutoff z,CountingTerminalProgram.phases z,0,0,0,
    CountingBaseProgram.capacityBits z.1]
def consR {f : Input → ℕ} {g : Input → List ℕ}
    (F : Realizer f) (G : Realizer g) : Realizer (fun z => f z::g z) :=
  composition (f := fun z : Input => (f z,g z)) (g := fun p : ℕ×List ℕ => p.1::p.2)
    (pair F G) listCons

def preliminaryRealizer : Realizer preliminary :=
  consR labelCountRealizer (consR CountingTerminalProgram.cutoffRealizer
    (consR CountingTerminalProgram.phasesRealizer (consR (constant 0) (consR (constant 0)
      (consR (constant 0) (consR (composition (f := fun z : Input => z.1)
        (g := CountingBaseProgram.capacityBits) first CountingBaseProgram.capacityBitsRealizer)
        (constant [])))))))

def basic (z : Input) : Parameters :=
  (vector controlExpressions (preliminary z),CountingBaseProgram.half z.2)
def basicRealizer : Realizer basic :=
  pair (composition (f := preliminary) (g := vector controlExpressions)
    preliminaryRealizer (vectorRealizer controlExpressions))
    (composition second CountingBaseProgram.halfRealizer)
def fillObservationsRealizer : Realizer fillObservations := by
  let frontR : Realizer (fun z : Parameters => z.1.take 4) :=
    composition (f := fun z : Parameters => (z.1,4))
      (g := fun p : List ℕ×ℕ => p.1.take p.2) (pair first (constant 4)) takeFast
  let suffix : Realizer (fun z : Parameters => z.1.drop 5) :=
    composition (f := fun z : Parameters => (z.1,5))
      (g := fun p : List ℕ×ℕ => p.1.drop p.2) (pair first (constant 5)) dropFast
  let tailR : Realizer (fun z : Parameters => CountingPhaseParametersProgram.observations z::z.1.drop 5) :=
    composition (pair CountingPhaseParametersProgram.observationsRealizer suffix) listCons
  exact pair (composition (pair frontR tailR) append) second

def parameters (z : Input) : Parameters := fillObservations (basic z)
def parametersRealizer : Realizer parameters :=
  composition (f := basic) (g := fillObservations) basicRealizer fillObservationsRealizer

open CompanionFactorialApplication
open scoped Classical

end ContingencyTables.CountingComputedSettings

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPreparedState
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the immutable rooted state from the public bounded input -/

namespace ContingencyTables.CountingPreparedState
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

def catalog (z : Input) : RootedForestCatalog.Data := CountingComputedSettings.catalog z
def catalogRealizer : Realizer catalog := CountingComputedSettings.catalogRealizer

def baseline (z : Input) : MatrixCode := TightenedInputProgram.baseline z.1
def baselineRealizer : Realizer baseline :=
  composition (f := fun z : Input => z.1) (g := TightenedInputProgram.baseline)
    first TightenedInputProgram.baselineRealizer

def capacity (z : Input) : MatrixCode := (catalog z).2
def capacityRealizer : Realizer capacity := composition catalogRealizer second

def zeroMatrix (z : Input) : MatrixCode := (capacity z).map (fun row => row.map (fun _ => 0))
def zeroMatrixRealizer : Realizer zeroMatrix :=
  composition capacityRealizer (map (map (constant 0)))

def demand (z : Input) : RootedDemandProgram.Input :=
  (catalog z,(baseline z,(zeroMatrix z,capacity z)))
def demandRealizer : Realizer demand := pair catalogRealizer (pair baselineRealizer (pair zeroMatrixRealizer capacityRealizer))

def parameters (z : Input) : RootedPenaltyEvaluateProgram.Parameters :=
  ((CountingBaseProgram.dimension z.1,CountingTerminalProgram.cutoff z),(CountingBaseProgram.coefficient z,0))
def parametersRealizer : Realizer parameters :=
  pair (pair (composition (f := fun z : Input => z.1) (g := CountingBaseProgram.dimension)
    first CountingBaseProgram.dimensionRealizer) CountingTerminalProgram.cutoffRealizer)
    (pair CountingBaseProgram.coefficientRealizer (constant 0))

def zeroGrid (z : Input) : List ℕ := (RootedForestCatalog.catalog (catalog z,false)).map (fun _ => 0)
def zeroGridRealizer : Realizer zeroGrid :=
  composition (composition (f := fun z : Input => (catalog z,false)) (g := RootedForestCatalog.catalog)
    (pair catalogRealizer (constant false)) RootedForestCatalog.catalogRealizer) (map (constant 0))

def state (z : Input) : RootedOracleWalkProgram.State :=
  ((CountingTerminalProgram.binCount z,(parameters z,demand z)),zeroGrid z)
def stateRealizer : Realizer state :=
  pair (pair CountingTerminalProgram.binCountRealizer (pair parametersRealizer demandRealizer)) zeroGridRealizer

def output (z : Input) : RootedOracleWalkProgram.State×CountingPhaseParametersProgram.Input :=
  (state z,CountingComputedSettings.parameters z)
def outputRealizer : Realizer output := pair stateRealizer CountingComputedSettings.parametersRealizer

open CompanionFactorialApplication ForestAssignmentSplit
open scoped Classical
variable {m n : ℕ}

noncomputable def start (A : Instance (Fin m) (Fin n)) (K : ℕ) (hK : 0 < K) :
    GridBoundary.Grid (I := Fin (RootedCatalogGrid.freeCount A)) K :=
  fun _ => ⟨0,le_rfl,by omega⟩

end ContingencyTables.CountingPreparedState

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingDirectProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The direct estimator for the zero-label branch

The same finite-word median evaluator handles this branch. The confidence
parameter controls the outer repetition count independently of its relative
accuracy, which is one quarter of the public accuracy.
-/
namespace ContingencyTables.CountingDirectProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

abbrev Input := (CountingBaseProgram.Input×TreeFraction.Fraction)×List Bool

def accuracy (z : Input) : TreeFraction.Fraction := CountingBaseProgram.half (CountingBaseProgram.half z.1.1.2)

def reserve (z : Input) : List Bool := z.2.map (fun _ => false)

end ContingencyTables.CountingDirectProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingAdaptiveInputProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-input preparation for a positive-label counting run -/
namespace ContingencyTables.CountingAdaptiveInputProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

def prepared (z : Input) : Prepared := CountingPreparedState.output z.1
def preparedRealizer : Realizer prepared :=
  composition (f := Prod.fst) (g := CountingPreparedState.output) first CountingPreparedState.outputRealizer

def capacities (z : Input) : List ℕ := CompanionRestartInitializer.capacities (prepared z)
def capacitiesRealizer : Realizer capacities :=
  composition (f := prepared) (g := CompanionRestartInitializer.capacities)
    preparedRealizer CompanionRestartInitializer.capacitiesRealizer

def labelWidth (z : Input) : ℕ := 2*CountingComputedSettings.labelCount z.1
def labelWidthRealizer : Realizer labelWidth :=
  composition (f := fun z : Input => (2,CountingComputedSettings.labelCount z.1))
    (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (constant 2) (composition (f := Prod.fst) (g := CountingComputedSettings.labelCount)
      first CountingComputedSettings.labelCountRealizer)) multiply

def zeroCode (z : Input) : List ℕ := (z.2.take (labelWidth z)).map (fun _ => 0)
def zeroCodeRealizer : Realizer zeroCode :=
  composition (f := fun z : Input => z.2.take (labelWidth z))
    (g := fun bs : List Bool => bs.map (fun _ => (0:ℕ)))
    (composition (f := fun z : Input => (z.2,labelWidth z)) (g := fun p : List Bool×ℕ => p.1.take p.2)
      (pair second labelWidthRealizer) takeFast) (map (constant 0))

def initialInput (z : Input) : CompanionInitialStoredProgram.Input :=
  (CountingPreparedState.catalog z.1,(capacities z,zeroCode z))
def initialInputRealizer : Realizer initialInput :=
  pair (composition (f := Prod.fst) (g := CountingPreparedState.catalog)
    first CountingPreparedState.catalogRealizer) (pair capacitiesRealizer zeroCodeRealizer)

def initial (z : Input) : Stored := CompanionInitialStoredProgram.output (initialInput z)

end ContingencyTables.CountingAdaptiveInputProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingActualPhase
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed phases with the controls computed from the original input -/
namespace ContingencyTables.CountingActualPhase
open MatchingFPRAS CommonBasesFPRAS FiniteObservableTransport
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionStoredRepresentation CompanionCanonicalHistory CompanionOracleDensity GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

def fixed (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon)
    (initial : CompanionPhaseFinishProgram.Stored) : CompanionOuterHistoryProgram.Fixed :=
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
  (CompanionRestartInitializer.data A s.C s.K s.H
    (CompanionTargetMixing.restartTime A s.H s.L) s.N s.n s.L
    (CountingBaseProgram.half (TreeFraction.repr epsilon)) (fun _ => 0)
    (CountingPreparedState.start A s.K (ComputedCountingParameters.binCount_pos r c b epsilon he)),initial)

end
end ContingencyTables.CountingActualPhase

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileScheduleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the complete outer sampling schedule from binary margins -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

def squarePower : Realizer (fun n : ℕ => n^2) :=
  squareNat.congr (fun n => (pow_two n).symm)

end ContingencyTables.ProfilePrograms

end OAI
end


