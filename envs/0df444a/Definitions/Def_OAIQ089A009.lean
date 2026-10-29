-- Prove2me | Definitions.Def_OAIQ089A009
-- name    : OAIQ089A009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T03:06:57.597774+00:00
-- url     : https://prove2.me/theorems/28485ba0-95f1-4327-88ab-824df3452ac4
-- title:
--   Definitions bundle OAIQ089A009 of the split of OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 580 declarations of OpenAI's Lean: 537 definitions and 43 theorems. The definitions and types are `OAI.ContingencyTables.CountingAdaptiveInputProgram.initialRealizer`, `OAI.ContingencyTables.CountingAdaptiveInputProgram.output`, `OAI.ContingencyTables.CountingAdaptiveInputProgram.outputRealizer`, `OAI.ContingencyTables.CountingAdaptiveInputProgram.runInput`, `OAI.ContingencyTables.CountingAdaptiveInputProgram.runInputRealizer`, `OAI.ContingencyTables.CountingAmplifiedProgram.Input`, `OAI.ContingencyTables.CountingAmplifiedProgram.budget`, `OAI.ContingencyTables.CountingAmplifiedProgram.budgetRealizer`, `OAI.ContingencyTables.CountingAmplifiedProgram.output`, `OAI.ContingencyTables.CountingAmplifiedProgram.outputRealizer`, `OAI.ContingencyTables.CountingAmplifiedProgram.prepared`, `OAI.ContingencyTables.CountingAmplifiedProgram.preparedRealizer`, `OAI.ContingencyTables.CountingBranchProgram.Input`, `OAI.ContingencyTables.CountingBranchProgram.budget`, `OAI.ContingencyTables.CountingBranchProgram.budgetRealizer`, `OAI.ContingencyTables.CountingBranchProgram.direct`, `OAI.ContingencyTables.CountingBranchProgram.directRealizer`, `OAI.ContingencyTables.CountingBranchProgram.feasibleBudget`, `OAI.ContingencyTables.CountingBranchProgram.feasibleBudgetRealizer`, `OAI.ContingencyTables.CountingBranchProgram.feasibleOutput`, `OAI.ContingencyTables.CountingBranchProgram.feasibleOutputRealizer`, `OAI.ContingencyTables.CountingBranchProgram.machine`, `OAI.ContingencyTables.CountingBranchProgram.machineTime`, `OAI.ContingencyTables.CountingBranchProgram.output`, `OAI.ContingencyTables.CountingBranchProgram.outputRealizer`, `OAI.ContingencyTables.CountingBranchProgram.parsedInput`, `OAI.ContingencyTables.CountingBranchProgram.parsedInputRealizer`, `OAI.ContingencyTables.CountingBranchProgram.publicBudget`, `OAI.ContingencyTables.CountingBranchProgram.publicBudgetRealizer`, `OAI.ContingencyTables.CountingBranchProgram.publicOutput`, `OAI.ContingencyTables.CountingBranchProgram.publicOutputRealizer`, `OAI.ContingencyTables.CountingBranchProgram.sourceValue`, `OAI.ContingencyTables.CountingDirectProgram.accuracyRealizer`, `OAI.ContingencyTables.CountingDirectProgram.budget`, `OAI.ContingencyTables.CountingDirectProgram.budgetRealizer`, `OAI.ContingencyTables.CountingDirectProgram.config`, `OAI.ContingencyTables.CountingDirectProgram.configRealizer`, `OAI.ContingencyTables.CountingDirectProgram.context`, `OAI.ContingencyTables.CountingDirectProgram.contextRealizer`, `OAI.ContingencyTables.CountingDirectProgram.contextWidth` and 497 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `ContingencyTables_Counting_CountingAdaptiveInputProgram`, `ContingencyTables_Counting_CountingAmplifiedProgram`, `ContingencyTables_Counting_CountingBranchMachine`, `ContingencyTables_Counting_CountingBranchProgram`, `ContingencyTables_Counting_CountingDirectLaw`, `ContingencyTables_Counting_CountingDirectProgram`, `ContingencyTables_Counting_CountingDirectSemantics`, `ContingencyTables_Counting_CountingExecutedMachine`, `ContingencyTables_Counting_CountingPositiveProgram`, `ContingencyTables_Counting_CountingPositiveWordLaw`, `ContingencyTables_Dense_DenseCandidateCounts`, `ContingencyTables_Dense_DenseDrawTabulation`, `ContingencyTables_Dense_DenseSuppliedFallback`, `ContingencyTables_Dense_DenseTabulationScalarBounds`, `ContingencyTables_Dense_DenseTrialCountProgram`, `ContingencyTables_Machines_CachedCompletionWeights`, `ContingencyTables_Machines_CachedProfileDecision`, `ContingencyTables_Machines_CachedStepCount`, `ContingencyTables_Machines_CachedTerminalCount`, `ContingencyTables_Machines_OffsetCountProgram`, `ContingencyTables_Machines_OnlinePartialCall`, `ContingencyTables_Machines_PreparedOffsetCount`, `ContingencyTables_Machines_PreparedTransitionCache`, `ContingencyTables_Machines_ResidualDenseProgram`, `ContingencyTables_Machines_ScheduledCountInput`, `ContingencyTables_Machines_ScheduledResidualProgram`, `ContingencyTables_Machines_TransitionCacheRuntime`, `ContingencyTables_Rooted_RootedAnnealing`, `ContingencyTables_Rooted_RootedBinDrawLaw`, `ContingencyTables_Rooted_RootedBooleanKernel`, `ContingencyTables_Rooted_RootedBooleanPhase`, `ContingencyTables_Rooted_RootedCatalogStep`, `ContingencyTables_Rooted_RootedComputedEstimator`, `ContingencyTables_Rooted_RootedCorrectionSampleLaw`, `ContingencyTables_Rooted_RootedCorrectionSamples`, `ContingencyTables_Rooted_RootedCountIdentification`, `ContingencyTables_Rooted_RootedEstimatorConfidence`, `ContingencyTables_Rooted_RootedFactorialApplication`, `ContingencyTables_Rooted_RootedHistoryConfidence`, `ContingencyTables_Rooted_RootedLargeMarginal`, `ContingencyTables_Rooted_RootedOracleChain`, `ContingencyTables_Rooted_RootedOracleCorrection`, `ContingencyTables_Rooted_RootedOracleDensity`, `ContingencyTables_Rooted_RootedOracleDraw`, `ContingencyTables_Rooted_RootedOracleEstimator`, `ContingencyTables_Rooted_RootedOracleFiniteStep`, `ContingencyTables_Rooted_RootedOracleFlatProgram`, `ContingencyTables_Rooted_RootedOracleKernel`, `ContingencyTables_Rooted_RootedOracleRational`, `ContingencyTables_Rooted_RootedPhaseOracleError`, `ContingencyTables_Rooted_RootedRatioSampleLaw`, `ContingencyTables_Rooted_RootedRestartStages`, `ContingencyTables_Rooted_RootedReturnWords`, `ContingencyTables_Rooted_RootedTrace`, `ContingencyTables_Rooted_RootedWarmReturn`, `ContingencyTables_Rooted_RootedWarmStart`, `ContingencyTables_Rooted_RootedWeightOracle`, `ContingencyTables_Sampling_AllSamplingMachine`, `ContingencyTables_Sampling_AllSamplingProgram`, `ContingencyTables_Sampling_ExactBranchChoice`, `ContingencyTables_Sampling_ExactCoreCost`, `ContingencyTables_Sampling_ExactCoreProgram`, `ContingencyTables_Sampling_ExactCorrectionPrefix`, `ContingencyTables_Sampling_ExactGateCost`, `ContingencyTables_Sampling_ExactGatePhysical`, `ContingencyTables_Sampling_ExactGatePolynomial`, `ContingencyTables_Sampling_ExactGatePrefix`, `ContingencyTables_Sampling_ExactGatePublic`, `ContingencyTables_Sampling_ExactGateTyped`, `ContingencyTables_Sampling_ExactOrdinaryProgram`, `ContingencyTables_Sampling_ExactPhysicalCost`, `ContingencyTables_Sampling_ExactPhysicalProgram`, `ContingencyTables_Sampling_ExactPrintCost`, `ContingencyTables_Sampling_ExactPublicCost`, `ContingencyTables_Sampling_ExactPublicPrefix`, `ContingencyTables_Sampling_ExactRareCost`, `ContingencyTables_Sampling_ExactResidualInput`, `ContingencyTables_Sampling_ExactSamplingParameters`, `ContingencyTables_Sampling_ExactTablePrefix`, `ContingencyTables_Sampling_ExactTypedProgram`, `ContingencyTables_Sampling_FirstPaperCodeNeighbors`, `ContingencyTables_Sampling_FirstPaperCodeProposal`, `ContingencyTables_Sampling_FirstPaperContextBox`, `ContingencyTables_Sampling_FirstPaperContextChildren`, `ContingencyTables_Sampling_FirstPaperContextTransport`, `ContingencyTables_Sampling_FirstPaperPhysicalVariance`, `ContingencyTables_Sampling_OriginalOuterVector`, `ContingencyTables_Sampling_OriginalTrialVector`, `ContingencyTables_Sampling_OuterTableProgram`, `ContingencyTables_Sampling_OuterTrialProgram`, `ContingencyTables_Sampling_ProfileMatrixEntry`, `ContingencyTables_Sampling_ProfileMatrixEntryRuntime`, `ContingencyTables_Sampling_ProfileMatrixProgram`, `ContingencyTables_Sampling_ProfileMatrixSemantics`, `ContingencyTables_Sampling_ProfilePublicProgram`, `ContingencyTables_Sampling_ProfileRetryProgram`, `ContingencyTables_Sampling_ProfileSamplingProgram`, `ContingencyTables_Sampling_ProfileScheduleProgram`, `ContingencyTables_Sampling_ProfileTerminalProgram`, `ContingencyTables_Sampling_ProfileTerminalSemantics`, `ContingencyTables_Sampling_ProfileTransitionCount`, `ContingencyTables_Sampling_ProfileTransitionProgram`, `ContingencyTables_Sampling_ProfileTrialCountProgram`, `ContingencyTables_Sampling_ProfileTrialProgram`, `ContingencyTables_Sampling_ProfileWordProgram`, `ContingencyTables_Sampling_RepairPrefixes`, `ContingencyTables_Sampling_SmallContextCount`, `ContingencyTables_Sampling_SmallContextFibres`, `ContingencyTables_Sampling_SmallGraphProfiles`, `ContingencyTables_Sampling_SmallProfileValidator`, `ContingencyTables_Sampling_UnitMatrixEntry`, `ContingencyTables_Sampling_UnitMatrixProgram`, `ContingencyTables_Sampling_UnitOriginalVector`, `ContingencyTables_Sampling_UnitOuterVector`, `ContingencyTables_Sampling_UnitProfileProgram`, `ContingencyTables_Sampling_UnitTerminalProgram`, `ContingencyTables_Sampling_UnitTrialCountProgram`, `ContingencyTables_Sampling_UnitTrialProgram`, `ContingencyTables_Transport_AuxiliaryRepairMass`, `ContingencyTables_Transport_BoundedProfileWalk`, `ContingencyTables_Transport_CacheBoxBounds`, `ContingencyTables_Transport_CanonicalDrawTabulation`, `ContingencyTables_Transport_ChoiceContextEnumeration`, `ContingencyTables_Transport_ContextAdjacentTransport`, `ContingencyTables_Transport_ContextChildVariance`, `ContingencyTables_Transport_ContextGraphEnergy`, `ContingencyTables_Transport_ContextGraphMembership`, `ContingencyTables_Transport_ContextWeightedEnumeration`, `ContingencyTables_Transport_IntegerGraphTruncation`, `ContingencyTables_Transport_IntegerLeafEnergy`, `ContingencyTables_Transport_IntegerRootTransport`, `ContingencyTables_Transport_IntegerTransportLimit`, `ContingencyTables_Transport_IntegerTruncatedTransport`, `ContingencyTables_Transport_RowMajorPrefixFibres`, `ContingencyTables_Transport_WordContextVariance`.
--
--   **Imports.** It imports the published bundle `Def_ContingencyTables`; the bundles `OAIQ089A006`, `OAIQ089A007` and `OAIQ089A008` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ089A011`; the statements `OAI.ContingencyTables.CountingBranchProgram.polynomial_publicBudget`, `OAI.ContingencyTables.CountingBranchProgram.polynomial_publicOutput`, `OAI.ContingencyTables.CountingExecutedMachine.polynomial_positive`, `OAI.ContingencyTables.CountingExecutedMachine.positive_success`, `OAI.ContingencyTables.CountingExecutedMachine.public_time`, `OAI.ContingencyTables.CountingPositiveProgram.value_source_sameLaw`, `OAI.ContingencyTables.ExactGatePolynomial.public_bound`, `OAI.ContingencyTables.ExactGatePublic.failure`, `OAI.ContingencyTables.ExactGatePublic.table_prefix`, `OAI.ContingencyTables.ExactPublicCost.table_prefix`, `OAI.ContingencyTables.ExactPublicLaw.haltMass_limit`, `OAI.ContingencyTables.ExactPublicLaw.halted_feasible`, `OAI.ContingencyTables.ExactPublicLaw.tableMass_limit`, `OAI.ContingencyTables.ExactPublicPrefix.prefix_correct`, `OAI.ContingencyTables.ExactTablePrefix.failure_bound`, `OAI.ContingencyTables.ProfilePrograms.work_exactMatrixInput`, `OAI.ContingencyTables.ProfilePrograms.work_optionalTrialCount`, `OAI.ContingencyTables.RootedEstimatorWordProgram.output_scheduled`, `OAI.ContingencyTables.RootedHistoryConfidence.history_success`, `OAI.ContingencyTables.RootedOracleDensity.goodEstimate_failure`, `OAI.ContingencyTables.SmallGraphProfiles.allSamplingMachineTime_public_bound` and `OAI.ContingencyTables.SmallGraphProfiles.exact_public_correction_bound`; the proofs of `OAI.ContingencyTables.CompanionPhaseContinuation.run_sameLaw`, `OAI.ContingencyTables.CompanionRestartProgram.output_native_sameLaw`, `OAI.ContingencyTables.ComputedCountingZero.zero_success`, `OAI.ContingencyTables.CountingBranchProgram.polynomial_publicBudget`, `OAI.ContingencyTables.CountingBranchProgram.polynomial_publicOutput`, `OAI.ContingencyTables.CountingExecutedMachine.polynomial_positive`, `OAI.ContingencyTables.CountingExecutedMachine.positive_success`, `OAI.ContingencyTables.CountingExecutedMachine.public_time`, `OAI.ContingencyTables.CountingPositiveProgram.value_source_sameLaw`, `OAI.ContingencyTables.ExactGatePolynomial.public_bound`, `OAI.ContingencyTables.ExactPublicLaw.haltMass_limit`, `OAI.ContingencyTables.ExactPublicLaw.halted_feasible`, `OAI.ContingencyTables.ProfilePrograms.work_exactMatrixInput`, `OAI.ContingencyTables.ProfilePrograms.work_optionalTrialCount`, `OAI.ContingencyTables.RootedEstimatorWordProgram.output_scheduled`, `OAI.ContingencyTables.RootedHistoryConfidence.history_success`, `OAI.ContingencyTables.RootedObservationStart.observed_failure_near`, `OAI.ContingencyTables.RootedOracleDensity.goodEstimate_failure`, `OAI.ContingencyTables.RootedPlainTrial.trial_failure`, `OAI.ContingencyTables.RootedTargetMixing.targetTrace_poincare`, `OAI.ContingencyTables.RootedTraceWords.arithmetic_recorded_event_bound`, `OAI.ContingencyTables.SmallGraphProfiles.allSamplingMachineTime_public_bound`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_ContingencyTables
import Definitions.Def_OAIQ089A006
import Definitions.Def_OAIQ089A007
import Definitions.Def_OAIQ089A008

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerLeafEnergy
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual leaf energy as a finite sum of complete displays -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical
open FactorialSignatures BalancedFamily BalancedEnumeration IntegerMarginal

universe u

/-- The full exchange graph may contain further edges; their energies
are nonnegative. Every leaf edge occurs once in this graph. -/
theorem leafEnergySum_le_graphEnergy {I : Type u} [Fintype I] [DecidableEq I]
    (Ms : List ℕ) (F H : (Coordinates I Ms → ℕ) → ℝ) (z : I → ℕ)
    (hF : ∀ x, 0 ≤ F x) (V : Finset (Coordinates I Ms → ℕ))
    (hV : leafVertices Ms z ⊆ V) :
    leafEnergySum Ms F H z ≤ integerGraphEnergy V F H := by
  rw [leafEnergySum_eq_edges Ms F H z hF]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    obtain ⟨hx,hy,hadj⟩ := leafEdges_states_adjacent Ms z e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hV hx,hV hy⟩,hadj⟩
  · intro e _ _
    exact mul_nonneg (le_min (hF _) (hF _)) (sq_nonneg _)

theorem recursiveEnergy_le_graphEnergy {I : Type u} [Fintype I] [DecidableEq I]
    (Ms : List ℕ) (F H : (Coordinates I Ms → ℕ) → ℝ) (z : I → ℕ) (h : I → ℝ)
    (hF : ∀ x, 0 ≤ F x) (V : Finset (Coordinates I Ms → ℕ))
    (hV : leafVertices Ms z ⊆ V) :
    recursiveEnergy Ms F H z h ≤ integerGraphEnergy V F H := by
  rw [recursiveEnergy_eq_leafEnergySum]
  exact leafEnergySum_le_graphEnergy Ms F H z hF V hV

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerRootTransport
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Root transport with the actual auxiliary defect sum

The auxiliary kernel gives one ordinary slot occupancy M+1 and all
others their balances. Removing the two special coordinates leaves the
special slot negative, exactly the root defects in the manuscript.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Matrix
open FactorialSignatures BalancedFamily BalancedEnumeration IntegerMarginal

universe u

/-- The softened integer transport on the actual exchange graph. All
recursive coefficients and future forms have been eliminated. -/
theorem integer_root_graph_transport (Ms : List ℕ)
    (F H : (Coordinates Bool Ms → ℕ) → ℝ) (m z : Bool → ℕ) (R W : ℕ)
    (hlower : ∀ U ∈ Ms, 2 ≤ U) (hupper : ∀ U ∈ Ms, U ≤ W)
    (hF : ∀ x, 0 ≤ F x)
    (hpos : BalancedBox.PositiveSlice F (bounds m Ms) (R+Ms.sum))
    (hsig : BalancedBox.RemovalSlice F (bounds m Ms) (R+Ms.sum))
    (hz : BalancedBox.InBox m z) (htotal : (∑ i, z i)=R+1)
    (hs : 0 < oneHole (eliminate Ms F) z false)
    (ht : 0 < oneHole (eliminate Ms F) z true)
    (V : Finset (Coordinates Bool Ms → ℕ)) (hV : leafVertices Ms z ⊆ V) :
    let s := oneHole (eliminate Ms F) z false
    let t := oneHole (eliminate Ms F) z true
    let c := integerRemovalMatrix (auxiliaryKernel Ms F) z false true
    (holeLinear (eliminate Ms (fun p => F p*H p)) z (rootCoefficients s t))^2 ≤
      (1/s+1/t+2*((W:ℝ)+1)^2*c/(s*t)) * integerGraphEnergy V F H := by
  dsimp only
  have hp := recursive_root_potential Ms F m z R W hlower hupper hF hpos hsig hz htotal hs ht
  have hb := integer_recursive_transport_of_slice Ms F H m z R (rootCoefficients _ _)
    hF hpos hz htotal (root_balance _ _ hs ht)
  have he := recursiveEnergy_le_graphEnergy Ms F H z (rootCoefficients
    (oneHole (eliminate Ms F) z false) (oneHole (eliminate Ms F) z true)) hF V hV
  have hpn := recursivePotential_nonnegative Ms F z (rootCoefficients
    (oneHole (eliminate Ms F) z false) (oneHole (eliminate Ms F) z true)) hF
  have hen := recursiveEnergy_nonnegative Ms F H z (rootCoefficients
    (oneHole (eliminate Ms F) z false) (oneHole (eliminate Ms F) z true)) hF
  exact hb.trans ((mul_le_mul_of_nonneg_right hp hen).trans
    (mul_le_mul_of_nonneg_left he (hpn.trans hp)))

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerTransportLimit
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The hard-zero limit of the actual integer transport

The final bound contains only finite marginal and auxiliary defect sums,
minimum-endpoint graph energies, and the two positive endpoint masses.
Thus no limit of recursively defined coefficients is needed.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Topology
open FactorialSignatures BalancedFamily BalancedEnumeration IntegerMarginal Filter

universe u

variable {K : Type*} {l : Filter K}

lemma integerGraphEnergy_tendsto {C : Type*} [DecidableEq C]
    (V : Finset (C → ℕ)) (F : K → (C → ℕ) → ℝ) (f H : (C → ℕ) → ℝ)
    (hlim : ∀ x, Tendsto (fun t => F t x) l (nhds (f x))) :
    Tendsto (fun t => integerGraphEnergy V (F t) H) l (nhds (integerGraphEnergy V f H)) := by
  unfold integerGraphEnergy
  apply Tendsto.div_const
  apply tendsto_finsetSum
  intro e _
  exact ((hlim e.1).min (hlim e.2)).mul_const _

/-- The original raw integer transport survives arbitrary hard zeros.
Only its two endpoint marginal masses must remain positive. -/
theorem integer_root_graph_transport_limit [l.NeBot] (Ms : List ℕ)
    (F : K → (Coordinates Bool Ms → ℕ) → ℝ) (f H : (Coordinates Bool Ms → ℕ) → ℝ)
    (hlim : ∀ x, Tendsto (fun t => F t x) l (nhds (f x)))
    (m z : Bool → ℕ) (R W : ℕ)
    (hlower : ∀ U ∈ Ms, 2 ≤ U) (hupper : ∀ U ∈ Ms, U ≤ W)
    (hsoft : ∀ᶠ t in l, (∀ x, 0 ≤ F t x) ∧
      BalancedBox.PositiveSlice (F t) (bounds m Ms) (R+Ms.sum) ∧
      BalancedBox.RemovalSlice (F t) (bounds m Ms) (R+Ms.sum))
    (hz : BalancedBox.InBox m z) (htotal : (∑ i, z i)=R+1)
    (hs : 0 < oneHole (eliminate Ms f) z false)
    (ht : 0 < oneHole (eliminate Ms f) z true)
    (V : Finset (Coordinates Bool Ms → ℕ)) (hV : leafVertices Ms z ⊆ V) :
    let s := oneHole (eliminate Ms f) z false
    let t := oneHole (eliminate Ms f) z true
    let c := integerRemovalMatrix (auxiliaryKernel Ms f) z false true
    (oneHole (eliminate Ms (fun p => f p*H p)) z false/s -
      oneHole (eliminate Ms (fun p => f p*H p)) z true/t)^2 ≤
      (1/s+1/t+2*((W:ℝ)+1)^2*c/(s*t)) * integerGraphEnergy V f H := by
  dsimp only
  have hmarg := eliminate_tendsto Ms F f hlim
  have hnum := eliminate_tendsto Ms (fun t p => F t p*H p) (fun p => f p*H p)
    (fun p => (hlim p).mul_const (H p))
  have hsm := oneHole_tendsto _ _ hmarg z false
  have htm := oneHole_tendsto _ _ hmarg z true
  have hsn := oneHole_tendsto _ _ hnum z false
  have htn := oneHole_tendsto _ _ hnum z true
  have hc := removal_tendsto _ _ (auxiliaryKernel_tendsto Ms F f hlim) z false true
  have he := integerGraphEnergy_tendsto V F f H hlim
  have hleft := ((hsn.div hsm (ne_of_gt hs)).sub (htn.div htm (ne_of_gt ht))).pow 2
  have h1 : Tendsto (fun _ : K => (1:ℝ)) l (nhds 1) := tendsto_const_nhds
  have hright := (((h1.div hsm (ne_of_gt hs)).add
    (h1.div htm (ne_of_gt ht))).add
    ((hc.const_mul (2*((W:ℝ)+1)^2)).div (hsm.mul htm) (mul_ne_zero (ne_of_gt hs) (ne_of_gt ht)))).mul he
  apply le_of_tendsto_of_tendsto hleft hright
  have hspos : ∀ᶠ t in l, 0 < oneHole (eliminate Ms (F t)) z false :=
    hsm.eventually (lt_mem_nhds hs)
  have htpos : ∀ᶠ t in l, 0 < oneHole (eliminate Ms (F t)) z true :=
    htm.eventually (lt_mem_nhds ht)
  filter_upwards [hsoft,hspos,htpos] with t hf hsp htp
  have hb := integer_root_graph_transport Ms (F t) H m z R W hlower hupper
    hf.1 hf.2.1 hf.2.2 hz htotal hsp htp V hV
  simpa only [root_linear_eq, Pi.div_apply] using hb

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperContextTransport
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Raw transport for the literal first-paper completion counts

An actual small-coordinate bijection isolates a fixed balanced prefix,
the special pair, and the remaining ordinary pairs. Large completions
are still the original physical finite sum; the prefix coordinates are
excluded from every exchange in the transport graph.
-/

namespace ContingencyTables.FirstPaperContextTransport

open scoped BigOperators Classical Topology
open FirstPaperPhysicalMarginal LargePairEnumeration IntegerWeightedTransport
open BalancedFamily BalancedBox

universe u

variable {I J C : Type u} [Fintype I] [Fintype J] [Fintype C]
  [DecidableEq C]

omit [Fintype C] [DecidableEq C] in

theorem contextSoft_tendsto (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (Ms : List ℕ)
    (e : (C ⊕ Coordinates Bool Ms) ≃ SmallView (fun a : I×J => small a.1 a.2))
    (σ : C → ℕ) (x : Coordinates Bool Ms → ℕ) :
    Filter.Tendsto (fun a : ℝ => contextSoft small B r c L Ms e σ a x) Filter.atTop
      (nhds (contextHard small B r c L Ms e σ x)) :=
  softMarginal_tendsto small B r c L _

end ContingencyTables.FirstPaperContextTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperContextChildren
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Child-mass minimum for the actual first-paper context

Ordinary unexposed pairs are summed with their actual balances before
applying the proved two-coordinate removal inequality and its hard limit.
-/

namespace ContingencyTables.FirstPaperContextTransport

open scoped BigOperators Classical Topology
open LargePairEnumeration IntegerWeightedTransport BalancedFamily BalancedBox

universe u

variable {I J C : Type u} [Fintype I] [Fintype J] [Fintype C] [DecidableEq C]

theorem context_child_minimum (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (Ms : List ℕ)
    (e : (C ⊕ Coordinates Bool Ms) ≃ SmallView (fun a : I×J => small a.1 a.2))
    (σ mC : C → ℕ) (U : ℕ) (hprefix : InBox mC σ)
    (hlarge : ∀ i j, small i j=false → 2 ≤ B i j)
    (hlower : ∀ w ∈ Ms, 2 ≤ w)
    (a j b : ℕ) (haj : a ≤ j) (hjb : j ≤ b) (hbU : b ≤ U) :
    min (eliminate Ms (contextHard small B r c L Ms e σ) (childProfile U a))
      (eliminate Ms (contextHard small B r c L Ms e σ) (childProfile U b)) ≤
      eliminate Ms (contextHard small B r c L Ms e σ) (childProfile U j) := by
  apply child_minimum_limit
    (fun α => eliminate Ms (contextSoft small B r c L Ms e σ α)) _ U
    (eliminate_tendsto Ms _ _ (contextSoft_tendsto small B r c L Ms e σ)) _ a j b haj hjb hbU
  filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with α hα
  have hp := contextSoft_slices small B r c L Ms e σ mC (fun _ => U) U hprefix α hα hlarge
  exact eliminate_slices Ms (fun _ => U) U _ hlower hp.1 hp.2

end ContingencyTables.FirstPaperContextTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_RepairPrefixes
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal repair values and row-major prefix preservation -/

namespace ContingencyTables

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype I] [Fintype J] in
theorem repairMatrix_prefix [LinearOrder I] [LinearOrder J]
    {x q : I → J → ℕ} {s t w : I×J} (h : IsDefect x q s t)
    (hst : RowMajorBefore s t) (hws : RowMajorBefore w s) :
    repairMatrix x s t w.1 w.2=x w.1 w.2 := by
  apply repairMatrix_unchanged h (hws.trans hst).ne
  intro hw
  have hv : RowMajorBefore w (t.1,s.2) := by
    rcases hst with hr|⟨hr,_⟩
    · exact hws.trans (Or.inl hr)
    · simpa only [←hr] using hws
  exact hv.ne hw

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallContextFibres
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual small-prefix fibres and conditional repair

Only small cells in the row-major prefix are fixed. Large completions
remain free and retain their full counting multiplicity.
-/

namespace ContingencyTables.SmallContextFibres

open scoped BigOperators Classical
open PaddedCompletions CompletionCounts FirstPaperProfiles
open PhysicalCompletionFibres FirstPaperPhysicalMarginal LargePairEnumeration

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- The contextual injection fixes only earlier small entries. -/
theorem smallContext_card_le [LinearOrder I] [LinearOrder J]
    (small : I → J → Bool) (r rbar : I → ℕ) (c cbar : J → ℕ)
    (s t : I×J) (σ : I×J → ℕ) (l : ℕ)
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true) (hst : RowMajorBefore s t) :
    Fintype.card (SmallJointDefectContext small r rbar c cbar s t σ l) ≤
      Fintype.card (SmallResidualChild small r rbar c cbar s σ
        (l-1+if t.1=s.1 then 1 else 0)) := by
  let f : SmallJointDefectContext small r rbar c cbar s t σ l →
      SmallResidualChild small r rbar c cbar s σ (l-1+if t.1=s.1 then 1 else 0) :=
    fun Z => ⟨jointRepair hs ht Z.val,(fun i j hij hbefore => by
      change repairMatrix Z.val.val.val.1 s t i j=σ (i,j)
      rw [repairMatrix_prefix Z.val.property.1 hst hbefore]
      exact Z.property.1 i j hij hbefore),by
      change repairMatrix Z.val.val.val.1 s t s.1 s.2=_
      rw [repairMatrix_special Z.val.property.1,Z.property.2]⟩
  apply Fintype.card_le_of_injective f
  intro X Y he
  apply Subtype.ext
  apply jointRepair_injective hs ht
  exact congrArg Subtype.val he

end ContingencyTables.SmallContextFibres

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallContextCount
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal contextual mass domination by repair

Finite sums of the actual hard completion weights, including all large
completions, are compared by the concrete repair injection.
-/

namespace ContingencyTables.SmallContextFibres

open scoped BigOperators Classical
open PaddedCompletions CompletionCounts FirstPaperProfiles
open PhysicalCompletionFibres FirstPaperPhysicalMarginal

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [LinearOrder I] [LinearOrder J]

/-- Conditional repair domination for the actual weighted finite sums. -/
theorem conditional_defect_mass_le
    (small : I → J → Bool) (B : I → J → ℕ) (r : I → ℕ) (c : J → ℕ)
    (L : ℕ) (s t : I×J) (σ : I×J → ℕ) (l : ℕ)
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true) (hst : RowMajorBefore s t)
    (hcap : ∀ T : ResidualTables small r c
      (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L),
      ∀ i j, T.val.val i j ≤ B i j) :
    (∑ z : DefectProfiles small B s t σ l,
      hardMarginal small B r c L (naturalProfile z.val)) ≤
      ∑ z : BalancedProfiles small B s σ (l-1+if t.1=s.1 then 1 else 0),
        hardMarginal small B r c L (naturalProfile z.val) := by
  rw [sum_hard_eq_sigma_card small B r c L
    (fun z : DefectProfiles small B s t σ l => naturalProfile z.val)
    (fun z => naturalProfile_bounded z.val),
    balanced_mass_eq_child_card small B r c L s σ _ hs hcap]
  exact_mod_cast (Fintype.card_le_of_injective (defectPairContext hs ht)
    (defectPairContext_injective hs ht)).trans
    (smallContext_card_le small r _ c _ s t σ l hs ht hst)

end ContingencyTables.SmallContextFibres

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerTruncatedTransport
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Raw transport with the literal box and degree zero extension

Excess-pair auxiliary sums may visit profiles outside the original box.
Their zero extension is therefore retained in the auxiliary count and
energy. Balanced endpoint masses and numerators are unchanged.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Topology
open BalancedFamily BalancedBox IntegerBoxTruncation FactorialSignatures

/-- Transport for the literal zero-extended weight. Its endpoint masses
and weighted means are still the original physical balanced sums. -/
theorem integer_box_root_transport_limit {K : Type*} {l : Filter K} [l.NeBot]
    (Ms : List ℕ) (F : K → (Coordinates Bool Ms → ℕ) → ℝ)
    (f H : (Coordinates Bool Ms → ℕ) → ℝ)
    (hlim : ∀ x, Filter.Tendsto (fun t => F t x) l (nhds (f x)))
    (m z : Bool → ℕ) (R W : ℕ)
    (hlower : ∀ U ∈ Ms, 2 ≤ U) (hupper : ∀ U ∈ Ms, U ≤ W)
    (hsoft : ∀ᶠ t in l, (∀ x, 0 ≤ F t x) ∧
      PositiveSlice (F t) (bounds m Ms) (R+Ms.sum) ∧
      RemovalSlice (F t) (bounds m Ms) (R+Ms.sum))
    (hz : InBox m z) (htotal : (∑ i, z i)=R+1)
    (hs : 0 < oneHole (eliminate Ms f) z false)
    (ht : 0 < oneHole (eliminate Ms f) z true)
    (V : Finset (Coordinates Bool Ms → ℕ)) (hV : leafVertices Ms z ⊆ V) :
    let g := truncate f (bounds m Ms) (R+Ms.sum)
    let s := oneHole (eliminate Ms f) z false
    let t := oneHole (eliminate Ms f) z true
    let c := integerRemovalMatrix (auxiliaryKernel Ms g) z false true
    (oneHole (eliminate Ms (fun p => f p*H p)) z false/s-
      oneHole (eliminate Ms (fun p => f p*H p)) z true/t)^2 ≤
      (1/s+1/t+2*((W:ℝ)+1)^2*c/(s*t))*integerGraphEnergy V g H := by
  dsimp only
  let M := bounds m Ms
  let D := R+Ms.sum
  have hF : ∀ᶠ t in l, (∀ x, 0 ≤ truncate (F t) M D x) ∧
      PositiveSlice (truncate (F t) M D) M D ∧
      RemovalSlice (truncate (F t) M D) M D := by
    filter_upwards [hsoft] with t ht
    exact truncate_all_slices (F t) M D ht.1 ht.2.1 ht.2.2
  have hs' : 0 < oneHole (eliminate Ms (truncate f M D)) z false := by
    simpa only [M,D,oneHole_eliminate_truncate Ms f m z R hz htotal] using hs
  have ht' : 0 < oneHole (eliminate Ms (truncate f M D)) z true := by
    simpa only [M,D,oneHole_eliminate_truncate Ms f m z R hz htotal] using ht
  have h := integer_root_graph_transport_limit Ms (fun t => truncate (F t) M D)
    (truncate f M D) H (truncate_tendsto F f M D hlim) m z R W hlower hupper hF
    hz htotal hs' ht' V hV
  dsimp only at h
  rw [truncate_mul] at h
  simpa only [M,D,oneHole_eliminate_truncate Ms _ m z R hz htotal] using h

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallGraphProfiles
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.SmallContextEnumeration.choiceContextFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The physical small graph and contextual unit exchanges -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open IntegerWeightedTransport FirstPaperProfiles ExcessContextProfiles FactorialSignatures

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

lemma assemble_injective (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) {n : ℕ} (e : Fin n ≃ Later small s) :
    Function.Injective (assemble small s hs σ U e) := by
  intro v w he
  funext a
  have hh := congrFun he (contextEquiv small s hs e U (.inr a))
  simpa only [assemble,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inr] using hh

/-- Fixing a prefix and reindexing preserves every actual unit removal. -/
lemma assemble_removeOne (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) {n : ℕ} (e : Fin n ≃ Later small s)
    (v : Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ)
    (i : Coordinates Bool (widths (fun _ : Fin n => U))) :
    assemble small s hs σ U e (removeOne v i)=
      removeOne (assemble small s hs σ U e v) (contextEquiv small s hs e U (.inr i)) := by
  have he : Sum.elim (prefixRaw small s σ U) (removeOne v i)=
      removeOne (Sum.elim (prefixRaw small s σ U) v) (.inr i) := by
    funext a
    cases a with
    | inl a => simp only [removeOne,Sum.elim_inl,Sum.inl_ne_inr,↓reduceIte,Nat.sub_zero]
    | inr a => simp only [removeOne,Sum.elim_inr,Sum.inr.injEq]
  unfold assemble
  rw [he]
  exact removeOne_reindex (contextEquiv small s hs e U) _ (.inr i)

/-- Every contextual transport edge is an actual doubled-small-coordinate
unit exchange, with no move involving the retained prefix. -/
theorem assemble_exchange_adjacent (small : I → J → Bool) (s : I×J)
    (hs : small s.1 s.2=true) (σ : I×J → ℕ) (U : ℕ) {n : ℕ}
    (e : Fin n ≃ Later small s)
    (X Y : Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ)
    (hxy : IntegerExchangeAdjacent X Y) :
    IntegerExchangeAdjacent (assemble small s hs σ U e X) (assemble small s hs σ U e Y) := by
  obtain ⟨D,i,j,hij,hi,hj,rfl,rfl⟩ := hxy
  refine ⟨assemble small s hs σ U e D,contextEquiv small s hs e U (.inr i),
    contextEquiv small s hs e U (.inr j),?_,?_,?_,?_,?_⟩
  · intro he
    exact hij (Sum.inr.inj ((contextEquiv small s hs e U).injective he))
  · rw [assemble_apply]
    exact hi
  · rw [assemble_apply]
    exact hj
  · exact assemble_removeOne small s hs σ U e D i
  · exact assemble_removeOne small s hs σ U e D j

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerGraphTruncation
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The zero-extended energy is the actual box-restricted graph energy -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical
open IntegerBoxTruncation BalancedBox

variable {C : Type*} [Fintype C] [DecidableEq C]

theorem graphEnergy_truncate (V : Finset (C → ℕ)) (f H : (C → ℕ) → ℝ)
    (m : C → ℕ) (R : ℕ) (hf : ∀ x, 0 ≤ f x) :
    integerGraphEnergy V (truncate f m R) H=
      integerGraphEnergy (V.filter (fun x => InBox m x ∧ (∑ i, x i)=R)) f H := by
  unfold integerGraphEnergy
  rw [←Finset.filter_product,Finset.filter_filter]
  simp only [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  by_cases ha : IntegerExchangeAdjacent e.1 e.2
  · by_cases hx : InBox m e.1 ∧ (∑ i, e.1 i)=R
    · by_cases hy : InBox m e.2 ∧ (∑ i, e.2 i)=R
      · simp only [ha,hx,hy,↓reduceIte,and_self,edgeTerm,truncate]
      · simp [ha,hx,hy,edgeTerm,truncate,min_eq_right (hf e.1)]
    · by_cases hy : InBox m e.2 ∧ (∑ i, e.2 i)=R
      · simp [ha,hx,hy,edgeTerm,truncate,min_eq_left (hf e.2)]
      · simp [ha,hx,hy,edgeTerm,truncate]
  · simp only [ha,and_false,↓reduceIte]

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperContextBox
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal boxed physical context transport

Auxiliary defect counts use the actual box and total-degree zero extension.
The energy is exactly the bounded physical exchange graph energy. Endpoint
masses and weighted means remain the literal completion-count sums.
-/

namespace ContingencyTables.FirstPaperContextTransport

open scoped BigOperators Classical Topology
open LargePairEnumeration IntegerWeightedTransport BalancedFamily BalancedBox
open IntegerBoxTruncation

universe u

variable {I J C : Type u} [Fintype I] [Fintype J] [Fintype C] [DecidableEq C]

omit [Fintype C] [DecidableEq C] in
lemma contextHard_nonnegative (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (Ms : List ℕ)
    (e : (C ⊕ Coordinates Bool Ms) ≃ SmallView (fun a : I×J => small a.1 a.2))
    (σ : C → ℕ) (x : Coordinates Bool Ms → ℕ) :
    0 ≤ contextHard small B r c L Ms e σ x := by
  apply ge_of_tendsto (contextSoft_tendsto small B r c L Ms e σ x)
  exact Filter.Eventually.of_forall (fun a => contextSoft_nonnegative small B r c L Ms e σ a x)

/-- The physical contextual transport inequality, with every auxiliary
profile and energy endpoint restricted to the declared box and degree. -/
theorem context_box_transport (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (Ms : List ℕ)
    (e : (C ⊕ Coordinates Bool Ms) ≃ SmallView (fun a : I×J => small a.1 a.2))
    (σ mC : C → ℕ) (m z : Bool → ℕ) (R W : ℕ)
    (hprefix : InBox mC σ)
    (hlarge : ∀ i j, small i j=false → 2 ≤ B i j)
    (hlower : ∀ U ∈ Ms, 2 ≤ U) (hupper : ∀ U ∈ Ms, U ≤ W)
    (hz : InBox m z) (htotal : (∑ i, z i)=R+1)
    (H : (Coordinates Bool Ms → ℕ) → ℝ)
    (V : Finset (Coordinates Bool Ms → ℕ)) (hV : leafVertices Ms z ⊆ V)
    (hs : 0 < oneHole (eliminate Ms (contextHard small B r c L Ms e σ)) z false)
    (ht : 0 < oneHole (eliminate Ms (contextHard small B r c L Ms e σ)) z true) :
    let f := contextHard small B r c L Ms e σ
    let g := truncate f (bounds m Ms) (R+Ms.sum)
    let s := oneHole (eliminate Ms f) z false
    let t := oneHole (eliminate Ms f) z true
    let aux := FactorialSignatures.integerRemovalMatrix (auxiliaryKernel Ms g) z false true
    (oneHole (eliminate Ms (fun p => f p*H p)) z false/s-
      oneHole (eliminate Ms (fun p => f p*H p)) z true/t)^2 ≤
      (1/s+1/t+2*((W:ℝ)+1)^2*aux/(s*t))*
        integerGraphEnergy (V.filter (fun x => InBox (bounds m Ms) x ∧ (∑ i, x i)=R+Ms.sum)) f H := by
  have h := integer_box_root_transport_limit Ms
    (contextSoft small B r c L Ms e σ) _ H
    (contextSoft_tendsto small B r c L Ms e σ) m z R W hlower hupper
    (by
      filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with a ha
      exact ⟨contextSoft_nonnegative small B r c L Ms e σ a,
        contextSoft_slices small B r c L Ms e σ mC m R hprefix a ha hlarge⟩)
    hz htotal hs ht V hV
  dsimp only at h ⊢
  rw [graphEnergy_truncate V _ H _ _ (contextHard_nonnegative small B r c L Ms e σ)] at h
  exact h

end ContingencyTables.FirstPaperContextTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_AuxiliaryRepairMass
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallContextEnumeration.choiceContextFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional repair bounds the literal auxiliary kernel mass -/

namespace ContingencyTables.ExcessContextProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open BalancedEnumeration IntegerWeightedTransport FirstPaperProfiles
open FirstPaperContextTransport FirstPaperPhysicalMarginal IntegerBoxTruncation
open PaddedCompletions CompletionCounts

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

variable [Fintype I] [Fintype J]

/-- Apply the completion-retaining repair injection and sum over actual
later cells. Each repair enters one of the two adjacent children. -/
theorem auxiliary_mass_le_adjacent (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U l : ℕ) (hl0 : 1 ≤ l) (hlU : l ≤ U)
    (hB : ∀ i j, small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s)
    (hcap : ∀ T : ResidualTables small r c
      (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L),
      ∀ i j, T.val.val i j ≤ B i j) :
    let Ms := widths (fun _ : Fin n => U)
    let f := contextHard small B r c L Ms (contextEquiv small s hs e U) (prefixRaw small s σ U)
    auxiliaryKernel Ms (truncate f (bounds (fun _ : Bool => U) Ms) (U+Ms.sum)) (auxRoot U l) ≤
      n*max (eliminate Ms f (childProfile U (l-1))) (eliminate Ms f (childProfile U l)) := by
  dsimp only
  let f := contextHard small B r c L (widths (fun _ : Fin n => U))
    (contextEquiv small s hs e U) (prefixRaw small s σ U)
  have hfirst := auxiliary_mass_le_defect_sum small B r c L s hs σ U l hl0 hlU hB hσ e
  dsimp only at hfirst
  refine hfirst.trans ?_
  have htbound (t : Later small s) :
      (∑ z : DefectProfiles small B s t.val.val σ l, hardMarginal small B r c L (naturalProfile z.val)) ≤
      max (eliminate _ f (childProfile U (l-1))) (eliminate _ f (childProfile U l)) := by
    have hrepair := conditional_defect_mass_le small B r c L s t.val.val σ l hs
      t.val.property t.property hcap
    have hk : l-1+(if t.val.val.1=s.1 then 1 else 0) ≤ U := by
      split_ifs <;> omega
    have he := eliminate_context_eq_balanced_mass small B r c L s hs σ U hB hσ
      ⟨l-1+(if t.val.val.1=s.1 then 1 else 0),Nat.lt_succ_of_le hk⟩ e
    have hb := hrepair.trans_eq he.symm
    by_cases hrow : t.val.val.1=s.1
    · simp only [hrow,↓reduceIte] at hb
      have hl : l-1+1=l := by omega
      rw [hl] at hb
      exact hb.trans (le_max_right _ _)
    · simp only [hrow,↓reduceIte,add_zero] at hb
      exact hb.trans (le_max_left _ _)
  calc
    _ ≤ ∑ _t : Later small s,
      max (eliminate _ f (childProfile U (l-1))) (eliminate _ f (childProfile U l)) :=
      Finset.sum_le_sum (fun t _ => htbound t)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      rw [←Fintype.card_congr e,Fintype.card_fin]

end ContingencyTables.ExcessContextProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ContextAdjacentTransport
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallContextEnumeration.choiceContextFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Adjacent physical exposure means with the repaired coefficient -/

namespace ContingencyTables.ExcessContextProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open BalancedEnumeration IntegerWeightedTransport FirstPaperProfiles
open FirstPaperContextTransport FirstPaperPhysicalMarginal IntegerBoxTruncation
open PaddedCompletions CompletionCounts FactorialSignatures

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

lemma graphEnergy_nonnegative {C : Type*} [DecidableEq C]
    (V : Finset (C → ℕ)) (f H : (C → ℕ) → ℝ) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ integerGraphEnergy V f H := by
  unfold integerGraphEnergy
  apply div_nonneg _ (by norm_num)
  apply Finset.sum_nonneg
  intro e _
  exact mul_nonneg (le_min (hf _) (hf _)) (sq_nonneg _)

variable [Fintype I] [Fintype J]

/-- The actual adjacent conditional means satisfy the uniform repaired
transport estimate, with precisely the box-valid leaf exchange energy. -/
theorem adjacent_context_transport (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U l : ℕ) (hU : 2 ≤ U) (hl0 : 1 ≤ l) (hlU : l ≤ U)
    (hB : ∀ i j, small i j=true → B i j=U)
    (hlarge : ∀ i j, small i j=false → 2 ≤ B i j)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s)
    (hcap : ∀ T : ResidualTables small r c
      (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L),
      ∀ i j, T.val.val i j ≤ B i j)
    (H : (Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ) → ℝ)
    (hleft : 0 < eliminate (widths (fun _ : Fin n => U))
      (contextHard small B r c L _ (contextEquiv small s hs e U) (prefixRaw small s σ U))
      (childProfile U (l-1)))
    (hright : 0 < eliminate (widths (fun _ : Fin n => U))
      (contextHard small B r c L _ (contextEquiv small s hs e U) (prefixRaw small s σ U))
      (childProfile U l)) :
    let Ms := widths (fun _ : Fin n => U)
    let f := contextHard small B r c L Ms (contextEquiv small s hs e U) (prefixRaw small s σ U)
    let a := eliminate Ms f (childProfile U (l-1))
    let b := eliminate Ms f (childProfile U l)
    let E := integerGraphEnergy
      ((leafVertices Ms (rootDisplay U l)).filter
        (fun x => InBox (bounds (fun _ : Bool => U) Ms) x ∧ (∑ i, x i)=U+Ms.sum)) f H
    min a b*(eliminate Ms (fun p => f p*H p) (childProfile U (l-1))/a-
      eliminate Ms (fun p => f p*H p) (childProfile U l)/b)^2 ≤
      (2+2*n*((U:ℝ)+1)^2)*E := by
  dsimp only
  have htransport := context_box_transport small B r c L (widths (fun _ : Fin n => U))
    (contextEquiv small s hs e U) (prefixRaw small s σ U) (fun _ => U)
    (fun _ => U) (rootDisplay U l) U U (prefixRaw_inBox small s σ U hσ) hlarge
    (fun w hw => by rw [widths_constant_mem U w hw]; exact hU)
    (fun w hw => le_of_eq (widths_constant_mem U w hw))
    (rootDisplay_inBox U l hl0 hlU) (rootDisplay_total U l hlU) H
    (leafVertices _ (rootDisplay U l)) (Finset.Subset.refl _)
    (by rw [rootDisplay_oneHole_false _ U l hl0 hlU]; exact hleft)
    (by rw [rootDisplay_oneHole_true]; exact hright)
  dsimp only at htransport
  simp only [rootDisplay_oneHole_false _ U l hl0 hlU,rootDisplay_oneHole_true,
    rootDisplay_removal _ U l hl0] at htransport
  have haux := auxiliary_mass_le_adjacent small B r c L s hs σ U l hl0 hlU hB hσ e hcap
  dsimp only at haux
  exact repaired_root_transport _ _ _ n U _ _ hleft hright
    (graphEnergy_nonnegative _ _ _ (contextHard_nonnegative small B r c L _ _ _)) haux htransport

end ContingencyTables.ExcessContextProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ContextChildVariance
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallContextEnumeration.choiceContextFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Between-child variance for actual physical exposure contexts -/

namespace ContingencyTables.ExcessContextProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open IntegerWeightedTransport FirstPaperProfiles FirstPaperContextTransport
open FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts

universe u

lemma graphEnergy_mono {C : Type*} [DecidableEq C]
    (V W : Finset (C → ℕ)) (f H : (C → ℕ) → ℝ)
    (hVW : V ⊆ W) (hf : ∀ x, 0 ≤ f x) :
    integerGraphEnergy V f H ≤ integerGraphEnergy W f H := by
  unfold integerGraphEnergy
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    obtain ⟨he,hadj⟩ := Finset.mem_filter.mp he
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hVW hx,hVW hy⟩,hadj⟩
  · intro e _ _
    exact mul_nonneg (le_min (hf _) (hf _)) (sq_nonneg _)

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- The physical conditional masses and means satisfy the paper's
between-child estimate, allowing arbitrary zero-mass children. -/
theorem physical_child_variance (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) (hU : 2 ≤ U)
    (hB : ∀ i j, small i j=true → B i j=U)
    (hlarge : ∀ i j, small i j=false → 2 ≤ B i j)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s)
    (hcap : ∀ T : ResidualTables small r c
      (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L),
      ∀ i j, T.val.val i j ≤ B i j)
    (H : (Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ) → ℝ)
    (hZ : 0 < ∑ j : Fin (U+1), eliminate (widths (fun _ : Fin n => U))
      (contextHard small B r c L _ (contextEquiv small s hs e U) (prefixRaw small s σ U))
      (childProfile U j.val)) :
    let Ms := widths (fun _ : Fin n => U)
    let f := contextHard small B r c L Ms (contextEquiv small s hs e U) (prefixRaw small s σ U)
    let z := fun j => eliminate Ms f (childProfile U j)
    let μ := fun j => eliminate Ms (fun p => f p*H p) (childProfile U j)/z j
    let E := integerGraphEnergy ((contextVertices U n).filter
      (fun x => InBox (bounds (fun _ : Bool => U) Ms) x ∧ (∑ i, x i)=U+Ms.sum)) f H
    (∑ j : Fin (U+1), z j.val*(μ j.val-
      (∑ k : Fin (U+1),z k.val*μ k.val)/(∑ k : Fin (U+1),z k.val))^2) ≤
      ((U:ℝ)+1)^4*(2+2*n*((U:ℝ)+1)^2)*E := by
  dsimp only
  let Ms := widths (fun _ : Fin n => U)
  let f := contextHard small B r c L Ms (contextEquiv small s hs e U) (prefixRaw small s σ U)
  let z := fun j => eliminate Ms f (childProfile U j)
  let μ := fun j => eliminate Ms (fun p => f p*H p) (childProfile U j)/z j
  let V := (contextVertices U n).filter
    (fun x => InBox (bounds (fun _ : Bool => U) Ms) x ∧ (∑ i, x i)=U+Ms.sum)
  have hf : ∀ x, 0 ≤ f x := contextHard_nonnegative small B r c L Ms _ _
  have hz (j : ℕ) : 0 ≤ z j := eliminate_nonnegative Ms f hf _
  have hE : 0 ≤ integerGraphEnergy V f H := graphEnergy_nonnegative V f H hf
  apply child_variance_bound z μ U (2+2*n*((U:ℝ)+1)^2) (integerGraphEnergy V f H)
    (fun j _ => hz j) hZ (by positivity) hE
  · intro a j b haj hjb hbU
    exact context_child_minimum small B r c L Ms (contextEquiv small s hs e U)
      (prefixRaw small s σ U) (fun _ => U) U (prefixRaw_inBox small s σ U hσ) hlarge
      (fun w hw => by rw [widths_constant_mem U w hw]; exact hU) a j b haj hjb hbU
  · intro j hj
    by_cases hl : 0 < z j
    · by_cases hr : 0 < z (j+1)
      · have htransport := adjacent_context_transport small B r c L s hs σ U (j+1) hU
          (by omega) (by omega) hB hlarge hσ e hcap H (by simpa only [Nat.add_sub_cancel] using hl) hr
        dsimp only at htransport
        simp only [Nat.add_sub_cancel] at htransport
        have hsub : (leafVertices Ms (rootDisplay U (j+1))).filter
            (fun x => InBox (bounds (fun _ : Bool => U) Ms) x ∧ (∑ i, x i)=U+Ms.sum) ⊆ V := by
          intro x hx
          obtain ⟨hx,hbox⟩ := Finset.mem_filter.mp hx
          exact Finset.mem_filter.mpr ⟨leafVertices_subset_context U n (j+1) (by omega) hx,hbox⟩
        exact htransport.trans (mul_le_mul_of_nonneg_left (graphEnergy_mono _ V f H hsub hf) (by positivity))
      · have hr0 : z (j+1)=0 := le_antisymm (le_of_not_gt hr) (hz (j+1))
        rw [hr0,min_eq_right (hz j),zero_mul]
        positivity
    · have hl0 : z j=0 := le_antisymm (le_of_not_gt hl) (hz j)
      rw [hl0,min_eq_left (hz (j+1)),zero_mul]
      positivity

end ContingencyTables.ExcessContextProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ContextGraphMembership
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.SmallContextEnumeration.choiceContextFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Context leaf vertices are actual balanced or single-defect states -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open BalancedEnumeration IntegerWeightedTransport FirstPaperProfiles ExcessContextProfiles FactorialSignatures

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

lemma pattern_after_one_removal (small : I → J → Bool) (B : I → J → ℕ) (U : ℕ)
    (hU : 1 ≤ U) (hB : ∀ i j, small i j=true → B i j=U)
    (s : I×J) (hs : small s.1 s.2=true) (D : SmallProfile small)
    (hpair : ∀ a : Cells small, D (a,false)+D (a,true)=if a=⟨s,hs⟩ then U+1 else U)
    (i : SmallView (fun a : I×J => small a.1 a.2)) (hi : 0 < D i)
    (hz : ∀ a, removeOne D i a ≤ U) : Pattern small B (removeOne D i) := by
  rcases i with ⟨c,b⟩
  by_cases hc : c=⟨s,hs⟩
  · subst c
    left
    apply balanced_of_pair_totals small B U hB
    intro a
    have hh := pair_total_removeOne D ⟨s,hs⟩ a b hi
    rw [hpair a] at hh
    by_cases ha : a=⟨s,hs⟩
    · rw [ite_eq_left ha,ite_eq_left ha] at hh
      omega
    · rw [ite_eq_right ha,ite_eq_right ha] at hh
      omega
  · right
    have hc' : c.val≠s := fun he => hc (Subtype.ext he)
    refine ⟨c.val,s,c.property,hs,?_⟩
    apply defect_of_pair_totals small B U hU hB c.val s c.property hs hc' _ hz
    intro a
    have hh := pair_total_removeOne D c a b hi
    rw [hpair a] at hh
    have hp : removeOne D (c,b) (a,false)+removeOne D (c,b) (a,true)=
        if a=c then U-1 else if a=⟨s,hs⟩ then U+1 else U := by
      by_cases hac : a=c
      · have has : a≠⟨s,hs⟩ := fun he => hc (hac.symm.trans he)
        rw [ite_eq_right has,ite_eq_left hac] at hh
        rw [ite_eq_left hac]
        exact hh
      · rw [ite_eq_right hac] at hh ⊢
        by_cases has : a=⟨s,hs⟩
        · rw [ite_eq_left has] at hh ⊢
          omega
        · rw [ite_eq_right has] at hh ⊢
          omega
    simpa only [Subtype.ext_iff] using hp

lemma assemble_bounded (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U)
    {n : ℕ} (e : Fin n ≃ Later small s)
    (v : Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ)
    (hv : InBox (bounds (fun _ : Bool => U) (widths (fun _ : Fin n => U))) v) :
    ∀ a, assemble small s hs σ U e v a ≤ U := by
  rw [bounds_constant] at hv
  intro a
  obtain ⟨w,rfl⟩ := (contextEquiv small s hs e U).surjective a
  rw [assemble_apply]
  cases w with
  | inl p =>
    rcases p with ⟨p,b⟩
    cases b
    · exact hσ p
    · exact Nat.sub_le _ _
  | inr w => exact hv w

lemma base_pair_total (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U l : ℕ) (hlU : l ≤ U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s)
    (q : Assignments (widths (fun _ : Fin n => U))) (a : Cells small) :
    assemble small s hs σ U e (embedding _ (rootDisplay U l) q) (a,false)+
      assemble small s hs σ U e (embedding _ (rootDisplay U l) q) (a,true)=
      if a=⟨s,hs⟩ then U+1 else U := by
  obtain ⟨v,rfl⟩ := (cellSplitEquiv small s hs).surjective a
  rcases v with p|(_|t)
  · have hps : p.val≠⟨s,hs⟩ := by
      intro he
      have h := p.property
      rw [he] at h
      exact h.ne rfl
    change assemble small s hs σ U e (embedding _ (rootDisplay U l) q) (p.val,false)+
      assemble small s hs σ U e (embedding _ (rootDisplay U l) q) (p.val,true)=
      if p.val=⟨s,hs⟩ then U+1 else U
    simp only [assemble_prefix,Bool.false_eq_true,↓reduceIte,hps]
    have hb := hσ p
    omega
  · change assemble small s hs σ U e (embedding _ (rootDisplay U l) q) (⟨s,hs⟩,false)+
      assemble small s hs σ U e (embedding _ (rootDisplay U l) q) (⟨s,hs⟩,true)=
      if (⟨s,hs⟩ : Cells small)=⟨s,hs⟩ then U+1 else U
    rw [ite_eq_left rfl]
    simp only [assemble_special,embedding_root,rootDisplay,Bool.false_eq_true,↓reduceIte]
    omega
  · have hts : t.val≠⟨s,hs⟩ := by
      intro he
      have h := t.property
      rw [he] at h
      exact h.ne rfl
    change assemble small s hs σ U e (embedding _ (rootDisplay U l) q) (t.val,false)+
      assemble small s hs σ U e (embedding _ (rootDisplay U l) q) (t.val,true)=
      if t.val=⟨s,hs⟩ then U+1 else U
    have hf := assemble_later small s hs σ U e (embedding _ (rootDisplay U l) q) (e.symm t) false
    have ht := assemble_later small s hs σ U e (embedding _ (rootDisplay U l) q) (e.symm t) true
    simp only [Equiv.apply_symm_apply] at hf ht
    rw [hf,ht,ite_eq_right hts]
    exact embedding_pair_total (fun _ : Fin n => U) (rootDisplay U l) q (e.symm t)

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ContextGraphEnergy
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.SmallContextEnumeration.choiceContextFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Contextual transport energy embeds in the actual physical graph -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open IntegerWeightedTransport FirstPaperProfiles ExcessContextProfiles
open FirstPaperContextTransport FirstPaperPhysicalMarginal

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

omit [Fintype I] [Fintype J] in
lemma assemble_physicalPrefix (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) {n : ℕ} (e : Fin n ≃ Later small s)
    (x : Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ) :
    PhysicalPrefix small s σ (assemble small s hs σ U e x) := by
  intro a
  exact assemble_prefix small s hs σ U e x a false

noncomputable def physicalContextEdges (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (σ : I×J → ℕ) : Finset (SmallProfile small×SmallProfile small) :=
  ((vertices small B) ×ˢ (vertices small B)).filter
    (fun p => IntegerExchangeAdjacent p.1 p.2 ∧ PhysicalPrefix small s σ p.1 ∧ PhysicalPrefix small s σ p.2)

noncomputable def physicalContextEnergy (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (σ : I×J → ℕ) (f H : SmallProfile small → ℝ) : ℝ :=
  (∑ p ∈ physicalContextEdges small B s σ, edgeTerm f H p)/2

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ContextWeightedEnumeration
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallContextEnumeration.choiceContextFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical observables in the literal conditional enumeration -/

namespace ContingencyTables.SmallContextEnumeration

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres
open LargePairEnumeration BalancedEnumeration BalancedFamily
open FirstPaperContextTransport FirstPaperPhysicalMarginal ExcessContextProfiles
open IntegerWeightedTransport

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- Arbitrary physical observables keep exactly the same completion
multiplicity in recursive elimination and in the literal child fibre. -/
theorem eliminate_context_eq_weighted_sum (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (hs : small s.1 s.2=true) (σ : I×J → ℕ) (U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s,σ a.val.val ≤ U) (k : Fin (U+1))
    {n : ℕ} (e : Fin n ≃ Later small s) (F : SmallProfile small → ℝ) :
    eliminate (widths (fun _ : Fin n => U))
      (fun p => F (assemble small s hs σ U e p)) (childProfile U k.val)=
      ∑ z : BalancedProfiles small B s σ k.val,F (naturalProfile z.val) := by
  rw [eliminate_eq_sum]
  apply Fintype.sum_equiv (((assignmentEquiv (fun _ : Fin n => U)).trans
    (reindexChoices small s e)).trans (balancedContextEquiv small B s hs σ U hB hσ k))
  intro q
  unfold assemble
  rw [physical_embedding_eq small B s hs σ U hB hσ k e q]
  rfl

end ContingencyTables.SmallContextEnumeration

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ChoiceContextEnumeration
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal finite choice fibres equal the transport child sums -/

namespace ContingencyTables.SmallContextEnumeration

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres
open LargePairEnumeration BalancedEnumeration BalancedFamily
open FirstPaperContextTransport FirstPaperPhysicalMarginal ExcessContextProfiles SmallGraphProfiles
open FiniteExposureVariance
open IntegerWeightedTransport

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- The child mass and every child moment are the actual finite fibre
sums of balanced physical choices, retaining all large completions. -/
theorem eliminate_context_eq_choice_fibre (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (hs : small s.1 s.2=true) (U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U)
    (τ : Earlier small s → Fin (U+1)) (k : Fin (U+1))
    {n : ℕ} (e : Fin n ≃ Later small s) (F : SmallProfile small → ℝ) :
    eliminate (widths (fun _ : Fin n => U))
      (fun p => F (assemble small s hs (prefixExtension small s U τ) U e p)) (childProfile U k.val)=
      ∑ x,fibreWeight (fibreWeight (fun x => F (rawChoice small U x))
        (earlierChoices small s U) τ) (fun x => x ⟨s,hs⟩) k x := by
  rw [eliminate_context_eq_weighted_sum small B s hs _ U hB
    (prefixExtension_bounded small s U τ),choice_fibre_sum]
  have he := Fintype.sum_equiv
    (balancedContextEquiv small B s hs (prefixExtension small s U τ) U hB
      (prefixExtension_bounded small s U τ) k)
    (fun y => F (rawChoice small U (splitChoices small s hs U τ k y)))
    (fun z => F (naturalProfile z.val)) (fun y => by
      change F (rawChoice small U (splitChoices small s hs U τ k y))=
        F (rawChoice small U (splitChoices small s hs U
          (prefixChoices small s (prefixExtension small s U τ) U (prefixExtension_bounded small s U τ)) k y))
      rw [prefixChoices_extension])
  have hc := Fintype.sum_equiv (choiceContextEquiv small s hs U τ k)
    (fun y => F (rawChoice small U (splitChoices small s hs U τ k y)))
    (fun x => F (rawChoice small U x.val)) (fun _ => rfl)
  exact he.symm.trans hc

end ContingencyTables.SmallContextEnumeration

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RowMajorPrefixFibres
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Row-major word prefixes are the literal physical exposure contexts -/

namespace ContingencyTables.RowMajorEnumeration

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily
open ExcessContextProfiles SmallGraphProfiles FiniteExposureVariance IntegerWeightedTransport

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- Both zeroth and first moments in the finite prefix variance are
exactly the moments used by the proved physical transport inequality. -/
theorem eliminate_context_eq_word_fibre (small : I → J → Bool) (B : I → J → ℕ)
    (U : ℕ) (hB : ∀ i j,small i j=true → B i j=U)
    (k : Fin (Fintype.card (Cells small))) (τ : Fin k.val → Fin (U+1)) (j : Fin (U+1))
    (F : SmallProfile small → ℝ) :
    let s := (enumeration small k).val
    let hs := (enumeration small k).property
    let σ := prefixExtension small s U (earlierWordChoices small U k τ)
    let e := laterEnumeration small k
    eliminate (widths (fun _ : Fin (Fintype.card (Cells small)-k.val-1) => U))
      (fun p => F (assemble small s hs σ U e p)) (childProfile U j.val)=
      ∑ a,fibreWeight (fibreWeight (fun a => F (rawChoice small U (wordChoices small U a)))
        (restriction k.val (Nat.le_of_lt k.isLt)) τ) (fun a => a k) j a := by
  dsimp only
  rw [eliminate_context_eq_choice_fibre small B _ _ U hB]
  exact (word_fibre_sum small U k τ j (fun x => F (rawChoice small U x))).symm

end ContingencyTables.RowMajorEnumeration

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_WordContextVariance
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical transport bounds the literal word-prefix child variance -/

namespace ContingencyTables.RowMajorEnumeration

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open ExcessContextProfiles SmallGraphProfiles FiniteExposureVariance IntegerWeightedTransport
open FirstPaperContextTransport FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def wordWeight (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ)
    (a : Fin (Fintype.card (Cells small)) → Fin (U+1)) : ℝ :=
  hardMarginal small B r c L (rawChoice small U (wordChoices small U a))

noncomputable def wordObservable (small : I → J → Bool) (U : ℕ) (H : SmallProfile small → ℝ)
    (a : Fin (Fintype.card (Cells small)) → Fin (U+1)) : ℝ :=
  H (rawChoice small U (wordChoices small U a))

end ContingencyTables.RowMajorEnumeration

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperPhysicalVariance
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Poincare inequality on the actual feasible small states -/

namespace ContingencyTables.SmallGraphProfiles

open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal CompletionCounts SmallContextEnumeration FiniteExposureVariance

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma physicalExtension_at (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (H : PhysicalStates small B r c L → ℝ)
    (z : PhysicalStates small B r c L) :
    physicalExtension small B r c L H (physicalProfile small B r c L z)=H z :=
  (physicalProfile_injective small B r c L).extend_apply H (fun _ => 0) z

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallProfileValidator
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial binary validator for the positive profile space -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def profilePattern : Realizer (fun z : ProfileCheckData => patternTest (z.1.1.2,z.2)) :=
  composition (pair profileViews second) patternTestRealizer

def profileTestRealizer : Realizer profileTest :=
  composition (pair (profileShape true)
    (composition (pair (profileShape false)
    (composition (pair (profileBound true)
    (composition (pair (profileBound false)
    (composition (pair profilePattern
    (composition (pair (profileLineTest true) (profileLineTest false)) boolAnd)) boolAnd))
      boolAnd)) boolAnd)) boolAnd)) boolAnd

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperCodeNeighbors
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A binary program for the full physical neighbor list -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def codeNeighborsRealizer : Realizer codeNeighbors :=
  composition (composition (pair identity rawCodeNeighborsRealizer)
    (filterWith (composition candidateDataRealizer profileTestRealizer))) profileCodeDedup

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperCodeProposal
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The compiled neighbor draw has the small-chain proposal law -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def codeNeighborProposalRealizer : Realizer codeNeighborProposal :=
  composition (pair (composition
    (f := fun z : ProfileCheckData×List Bool => z.1) (g := codeNeighbors)
    first codeNeighborsRealizer) second) listWordChoiceRealizer

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedLargeMarginal
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual balanced large-cell marginal for the explicit root selector

The raw removal and reflected signatures are derived from the physical
line/unary factors. No signature of the marginal is postulated.
-/

namespace ContingencyTables.RootedLargeMarginal

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedPenalty
open LargePairEnumeration BalancedBox

variable {I J : Type*} [Fintype I] [Fintype J]

theorem largeMarginal_removal (A : Instance I J) (S : Selection A.T)
    (alpha : ℝ) (ha : 0≤ alpha) {n : ℕ}
    (e : Fin n ≃ LargeCell (fun a : I×J => A.small a.1 a.2)) (R : ℕ) :
    RemovalSlice (largeMarginal A S alpha e) (bounds A) R := by
  let N : Fin n → ℕ := fun k => RootedPenalty.widths A (e k).val.1 (e k).val.2
  have hu : ∀ a,0≤ ForestPenaltyApplication.unaryRate A.T A.b alpha a := by
    intro a
    unfold ForestPenaltyApplication.unaryRate
    split_ifs
    · exact div_nonneg ha (Nat.cast_nonneg _)
    · exact le_rfl
  have hs := EqualityReindex.physical_marginal_removal (LargePairEnumeration.widths N)
    (bounds A) R (physicalCoordinateEquiv (fun a : I×J => A.small a.1 a.2) e N)
    RowColumnPenalties.cellLine (rootFlag S) (fun _ => alpha)
    (ForestPenaltyApplication.lineOffset (ell A) (RootedPenalty.widths A) A.r A.c)
    RowColumnPenalties.viewSlope (ForestPenaltyApplication.unaryRate A.T A.b alpha)
    (ForestPenaltyApplication.unaryEll (ell A)) ForestPenaltyApplication.unarySlope
    (ForestPenaltyApplication.unaryCap A.b)
    (widths_lower N (large_width A e)) (fun _ => ha) hu
  rw [largeMarginal_eq_eliminate]
  exact hs

end ContingencyTables.RootedLargeMarginal

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCountIdentification
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected-root physical marginal is its literal completion count -/

namespace ContingencyTables.RootedCountIdentification

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedPenalty RootedLiteralCount
open ForestCountIdentification ForestAssignmentSplit ForestLiteralCount
open PhysicalLargeProfiles LargePairEnumeration BalancedBox GraphCompletionCounts

variable {I J : Type*} [Fintype I] [Fintype J]

theorem h_removal (A : Instance I J) (S : Selection A.T)
    (alpha : ℝ) (ha : 0≤ alpha) (R : ℕ) :
    RemovalSlice (h A S alpha) (bounds A) R := by
  let e := (Fintype.equivFin (LargeCell (fun a : I×J => A.small a.1 a.2))).symm
  have hs := RootedLargeMarginal.largeMarginal_removal A S alpha ha e R
  intro z hz ht
  rw [NestedReindex.removal_congr_box _ _ (bounds A) z hz (h_eq_largeMarginal A S alpha e)]
  convert hs z hz ht using 1
  all_goals try with_reducible_and_instances rfl

end ContingencyTables.RootedCountIdentification

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedFactorialApplication
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual factorial lifts of the selected-root completion count -/

namespace ContingencyTables.RootedFactorialApplication

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS CompanionFactorialApplication
open LargePairEnumeration BalancedBox LabelledFactorial

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The manuscript's actual factorial lift is positive on its degree and
has its omission signature, derived from the literal count. -/
theorem first_properties (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (ha : 0≤alpha) :
    BinaryContraction.DegreePositive (f A R alpha) (Fintype.card (Labels A)) ∧
      BinaryContraction.OmissionProperty (f A R alpha) (Fintype.card (Labels A)) := by
  change BinaryContraction.DegreePositive
      (firstLift (TwoLiftStates.group (labelCell A)) (RootedCountIdentification.h A R alpha) (denominator A)) _ ∧
    BinaryContraction.OmissionProperty
      (firstLift (TwoLiftStates.group (labelCell A)) (RootedCountIdentification.h A R alpha) (denominator A)) _
  constructor
  · exact SliceFactorial.firstLift_degreePositive (TwoLiftStates.group (labelCell A))
      (RootedCountIdentification.h A R alpha) (denominator A) (Fintype.card (Labels A)) (denominator_positive A)
      (fun z _ _ => RootedCountIdentification.h_positive A R alpha z)
  · have hs : @RemovalSlice (View A) _ (Classical.decEq _)
        (RootedCountIdentification.h A R alpha) (groupCount (TwoLiftStates.group (labelCell A)) Set.univ)
        (Fintype.card (Labels A)) := by
      rw [label_capacity]
      convert RootedCountIdentification.h_removal A R alpha ha _ using 1
      all_goals try with_reducible_and_instances rfl
    convert SliceFactorial.firstLift_omission_slice (TwoLiftStates.group (labelCell A))
      (RootedCountIdentification.h A R alpha) (denominator A) (Fintype.card (Labels A)) (denominator_positive A)
      (fun z => (RootedCountIdentification.h_positive A R alpha z).le) hs using 1
    all_goals try with_reducible_and_instances rfl

end ContingencyTables.RootedFactorialApplication

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedAnnealing
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Adjacent selected-root weights and ideal multipliers

The actual computed-root penalty satisfies the source height bound.
It gives the factor-two annealing estimates for the same literal
completion count used by the executed density evaluator.
-/

namespace ContingencyTables.RootedAnnealing

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication LabelledFactorial
open CompanionAnnealing (scale scale_positive )
open ForestAssignmentSplit
open ForestScaledPenalty (rowCounts columnCounts integerCube)
open TwoLiftStates BalancedBox

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The selected-root penalty of an actual integer free assignment. -/
noncomputable def penalty (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (z : View A → ℕ) (f : FreeIndex A.small A.T A.b) : ℝ :=
  RootedLiteralCount.actualPenalty A R
    (ForestCountIdentification.smallX A.small z) (ForestCountIdentification.smallY A.small z)
    (freeTable A.small A.T A.b f)
    (RootedPhysicalCompletion.solved A R (rowCounts A z) (columnCounts A z)
      (fun i j => (freeTable A.small A.T A.b f i j:ℤ)))

end ContingencyTables.RootedAnnealing

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleDensity
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected-root evaluator density on its actual finite bin cube -/

namespace ContingencyTables.RootedOracleDensity

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit
open CompanionOracleDensity (dimension index pull binWidth height)

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def D (A : Instance I J) (S : Selection A.T) (C : ℝ)
    (z : View A → ℕ) (v : Fin (dimension A) → ℝ) : ℝ :=
  RootedScaledPenalty.penalty A S C (binWidth A C)
    (ForestScaledPenalty.rowCounts A z) (ForestScaledPenalty.columnCounts A z) (pull A v)

lemma D_nonnegative (A : Instance I J) (S : Selection A.T) (C : ℝ) (hC : 0≤ C)
    (z : View A → ℕ) (v : Fin (dimension A) → ℝ) : 0≤ D A S C z v :=
  RootedScaledPenalty.penalty_nonnegative A S C (binWidth A C) hC _ _ _

noncomputable def rho (A : Instance I J) (S : Selection A.T) (C a : ℝ)
    (z : View A → ℕ) : (Fin (dimension A) → ℝ) → ℝ :=
  DenseWeights.density (a/height A C) (D A S C z)

noncomputable def V (A : Instance I J) (S : Selection A.T) (C a : ℝ)
    (z : View A → ℕ) : (Fin (dimension A) → ℝ) → ℝ :=
  DenseWeights.binWeight (a/height A C) (D A S C z)

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleCorrection
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact population correction for the computed-root completion count

Integer bins and their executable interval draws are the existing
physical bins.  Only their positive density weights change with the
explicit root selector.  All normalizer identities are finite sums.
-/

namespace ContingencyTables.RootedOracleDensity

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit GridBoundary
open CompanionOracleDensity (dimension index pull binWidth height integerPoint integerBin integerFiber
  assignmentCount )

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def gridWeight (A : Instance I J) (S : Selection A.T) (C a : ℝ)
    (z : View A → ℕ) {K : ℕ} (v : Grid (I := Fin (dimension A)) K) : ℝ :=
  V A S C a z (realCorner v)

noncomputable def binSum (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (z : View A → ℕ) (K : ℕ) : ℝ :=
  ∑ v : Grid (I := Fin (dimension A)) K,gridWeight A S C a z v

noncomputable def correctedMass (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (z : View A → ℕ) (K : ℕ) (hK : 0<K) (f : FreeIndex A.small A.T A.b) : ℝ :=
  gridWeight A S C a z (integerBin A K hK f)/binSum A S C a z K/
    (integerFiber A K hK (integerBin A K hK f)).card

noncomputable def correction (A : Instance I J) (S : Selection A.T)
    (C a : ℝ) (z : View A → ℕ) (K : ℕ) (hK : 0<K) (f : FreeIndex A.small A.T A.b) : ℝ :=
  ((K:ℝ)^dimension A*(integerFiber A K hK (integerBin A K hK f)).card/assignmentCount A)*
    rho A S C a z (integerPoint A C f)/gridWeight A S C a z (integerBin A K hK f)

noncomputable def ratioObservable (A : Instance I J) (S : Selection A.T) (C : ℝ)
    (a : ℕ) (z : View A → ℕ) {K : ℕ} (v : Grid (I := Fin (dimension A)) K) : ℝ :=
  gridWeight A S C (a+1) z v/gridWeight A S C a z v

noncomputable def ratioMean (A : Instance I J) (S : Selection A.T)
    (C : ℝ) (a : ℕ) (z : View A → ℕ) (K : ℕ) : ℝ :=
  ∑ v : Grid (I := Fin (dimension A)) K,
    (gridWeight A S C a z v/binSum A S C a z K)*ratioObservable A S C a z v

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleChain
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual bin chain for the computed-root forest penalty

All cut geometry is proved from the selected-root density. The only
conditional inputs are the same finite-box Prékopa–Leindler inequality
and finite reversible-chain Cheeger theorem used by the original chain.
-/

namespace ContingencyTables.RootedOracleDensity

open CommonBasesFPRAS GridBoundary CompanionFactorialApplication
open CompanionOracleDensity (dimension height proposal_bounds proposal_degree cutConstant)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

def oracleChain (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℝ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) : FiniteChain (Grid (I := Fin (dimension A)) K) := by
  letI : Nonempty (Grid (I := Fin (dimension A)) K) :=
    ⟨fun _ => ⟨0,by constructor <;> omega⟩⟩
  exact MetropolisChain.chain (gridWeight A R C a z) (fun _ => DenseWeights.binWeight_pos _ _ _)
    Neighbor neighbor_symm (binProposal A.d) (proposal_bounds A.d A.hd).1.le
    (2*dimension A) (fun v => by simpa using neighbor_degree v)
    ((proposal_degree A).trans (by norm_num))

end
end ContingencyTables.RootedOracleDensity

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

theorem rationalD_cast (A : Instance I J) (S : Selection A.T) (C : ℕ)
    (z : View A → ℕ) (v : Fin (dimension A) → ℚ) :
    (rationalD A S C z v:ℝ)=D A S C z (fun i => (v i:ℝ)) := by
  rw [rationalD,RootedPenaltyProgram.rationalPenalty_cast]
  rfl

lemma rationalD_nonnegative (A : Instance I J) (S : Selection A.T) (C : ℕ)
    (z : View A → ℕ) (v : Fin (dimension A) → ℚ) : 0≤ rationalD A S C z v := by
  have hh := D_nonnegative A S C (Nat.cast_nonneg C) z (fun i => (v i:ℝ))
  rw [←rationalD_cast] at hh
  exact_mod_cast hh

theorem gridExponent_eq_floor (A : Instance I J) (S : Selection A.T) (C a : ℕ)
    (z : View A → ℕ) {K : ℕ} (v : Grid (I := Fin (dimension A)) K) :
    (gridExponent A S C a z v:ℤ)=⌊(a:ℝ)/height A C*D A S C z (realCorner v)⌋ := by
  have hn := mul_nonneg (div_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg (rationalHeight A C)))
    (rationalD_nonnegative A S C z (fun i => (corner v i:ℚ)))
  rw [gridExponent,Int.natCast_floor_eq_floor hn]
  have he : (((a:ℚ)/rationalHeight A C*rationalD A S C z (fun i => (corner v i:ℚ)):ℚ):ℝ)=
      (a:ℝ)/height A C*D A S C z (realCorner v) := by
    simp only [Rat.cast_mul,Rat.cast_div,Rat.cast_natCast,
      CompanionOracleDensity.rationalHeight_cast,rationalD_cast,Rat.cast_intCast]
    rfl
  rw [←he,Rat.floor_cast]

theorem gridWeight_eq_dyadic (A : Instance I J) (S : Selection A.T) (C a : ℕ)
    (z : View A → ℕ) {K : ℕ} (v : Grid (I := Fin (dimension A)) K) :
    gridWeight A S C a z v=1/(2:ℝ)^gridExponent A S C a z v := by
  unfold gridWeight V DenseWeights.binWeight
  rw [←gridExponent_eq_floor]
  simp only [Int.cast_natCast,Real.rpow_neg (by norm_num : (0:ℝ)≤2),Real.rpow_natCast,one_div]

theorem rationalGridWeight_cast (A : Instance I J) (S : Selection A.T) (C a : ℕ)
    (z : View A → ℕ) {K : ℕ} (v : Grid (I := Fin (dimension A)) K) :
    (rationalGridWeight A S C a z v:ℝ)=gridWeight A S C a z v := by
  rw [gridWeight_eq_dyadic]
  simp only [rationalGridWeight,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat]

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleKernel
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact rational grid transitions for the selected-root evaluator -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication GridBoundary CommonBasesFPRAS ResidualMixture FirstSuccess
open CompanionOracleDensity (dimension height binWidth oracleProposalRat oracleTime)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

lemma rationalGridWeight_positive (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) : 0 < rationalGridWeight A R C a z v := by
  unfold rationalGridWeight
  positivity
def oracleMove (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v w : Grid (I := Fin (dimension A)) K) : ℚ :=
  if Neighbor v w then oracleProposalRat A.d*min 1
    (rationalGridWeight A R C a z w/rationalGridWeight A R C a z v) else 0

def oracleTransition (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v w : Grid (I := Fin (dimension A)) K) : ℚ :=
  oracleMove A R C a z v w+if v=w then 1-∑ b,oracleMove A R C a z v b else 0

lemma oracleMove_cast (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v w : Grid (I := Fin (dimension A)) K) :
    (oracleMove A R C a z v w:ℝ)=
      MetropolisChain.move (gridWeight A R C a z) Neighbor (binProposal A.d) v w := by
  unfold oracleMove MetropolisChain.move
  split_ifs
  · simp only [Rat.cast_mul,Rat.cast_min,Rat.cast_one,Rat.cast_div,
      rationalGridWeight_cast,oracleProposalRat,binProposal,Rat.cast_pow,Rat.cast_ofNat]
  · exact Rat.cast_zero

theorem oracleTransition_cast (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) (v w : Grid (I := Fin (dimension A)) K) :
    (oracleTransition A R C a z v w:ℝ)=(oracleChain A R C a z hK).P v w := by
  unfold oracleTransition
  dsimp only [oracleChain,MetropolisChain.chain,FiniteChain.ofMoves]
  by_cases hvw : v=w <;>
    simp only [hvw,ite_true, if_true,ite_false,Rat.cast_add,Rat.cast_sub,Rat.cast_sum,
      Rat.cast_one,Rat.cast_zero,oracleMove_cast]

def oracleTransitionLaw (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) (v : Grid (I := Fin (dimension A)) K) :
    RationalLaw (Grid (I := Fin (dimension A)) K) where
  mass := oracleTransition A R C a z v
  nonnegative := fun w => by
    have hh := (oracleChain A R C a z hK).nonnegative v w
    rw [←oracleTransition_cast A R C a z hK] at hh
    exact_mod_cast hh
  total := by
    apply Rat.cast_injective (α := ℝ)
    simp only [Rat.cast_sum,oracleTransition_cast A R C a z hK,Rat.cast_one]
    exact (oracleChain A R C a z hK).stochastic v

def oracleWalkLaw (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) (v : Grid (I := Fin (dimension A)) K) (n : ℕ) :
    RationalLaw (Grid (I := Fin (dimension A)) K) :=
  walkLaw (oracleTransitionLaw A R C a z hK) v n

def oracleStationaryLaw (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) : RationalLaw (Grid (I := Fin (dimension A)) K) := by
  let : Nonempty (Grid (I := Fin (dimension A)) K) :=
    ⟨fun _ => ⟨0,by constructor <;> omega⟩⟩
  let w := fun v : Grid (I := Fin (dimension A)) K => rationalGridWeight A R C a z v
  have hw : ∀ v,0 < w v := rationalGridWeight_positive A R C a z
  have hZ : 0 < ∑ v,w v := Finset.sum_pos (fun v _ => hw v) Finset.univ_nonempty
  exact ⟨fun v => w v/∑ b,w b,fun v => (div_pos (hw v) hZ).le,
    by rw [←Finset.sum_div]; exact div_self hZ.ne'⟩

end
end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleFiniteStep
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
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

def finiteOracleStepLaw (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) : RationalLaw (Grid (I := Fin (dimension A)) K) :=
  finiteAcceptLaw v
    (fun code : Fin (2^Nat.clog 2 (8*A.d)) => axisCodeStep v code)
    (fun w => acceptDyadic (gridExponent A R C a z w-gridExponent A R C a z v) (rationalHeight A C))

def oracleBitStepLaw (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) : RationalLaw (Grid (I := Fin (dimension A)) K) :=
  mapLaw (uniformLaw (α := Fin (oracleStepBits A C) → Bool)) (oracleBitStep A R C a z v)

def oracleBitWalkLaw (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) (n : ℕ) : RationalLaw (Grid (I := Fin (dimension A)) K) :=
  wordWalkLaw (oracleBitStep A R C a z) v n

end
end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleDraw
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
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

def stationaryIntegerLaw (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) : RationalLaw (FreeIndex A.small A.T A.b) :=
  bindLaw (oracleStationaryLaw A R C a z hK) (exactBinLaw A K (by omega) hW)

def sampledIntegerLaw (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (dimension A)) K) (n h : ℕ) : RationalLaw (FreeIndex A.small A.T A.b) :=
  bindLaw (oracleBitWalkLaw A R C a z v n) (fun w => approximateBinLaw A K (by omega) hW w h)

end
end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCorrectionSamples
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Confidence for the actual rational correction samples -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteLawMoments FiniteIndependentAverages
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def correctionMean (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) : ℝ :=
  expectation (stationaryIntegerLaw A R C a z K hK hW) (correction A R C a z K (by omega))

end

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleEstimator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal rational product estimator for a companion h-value -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteLawMoments FiniteIndependentAverages
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def targetFactor (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (j : ℕ) : Option (Fin j) → ℝ
  | none => correctionMean A R C j z K hK hW
  | some a => ratioMean A R C a.val z K

def GoodEstimate (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (j : ℕ) (delta failure : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (draws : EstimatorInput A C K j delta failure) : Prop :=
  ∀ i,|(observedFactor A R C z K hK hW j delta failure v draws i:ℝ)-targetFactor A R C z K hK hW j i| ≤
    (delta:ℝ)*targetFactor A R C z K hK hW j i

end

end ContingencyTables.RootedOracleDensity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorConfidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Confidence of the complete bounded-word weight estimator -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteIndependentAverages
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def badFactor (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (j : ℕ) (delta failure : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (i : Option (Fin j))
    (draws : EstimatorInput A C K j delta failure) : Prop :=
  (delta:ℝ)*targetFactor A R C z K hK hW j i <
    |(observedFactor A R C z K hK hW j delta failure v draws i:ℝ)-targetFactor A R C z K hK hW j i|

end

end ContingencyTables.RootedOracleDensity

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

/-- The relative-accuracy event for the rational labelled-weight estimate. -/
def accurateCall (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (S : Set (Labels A×Bool))
    (bits : WeightWord A C K j xi) : Prop :=
  (1-(xi:ℝ))*RootedAnnealing.weight A R j S ≤ (evaluate A R C K hK hW j xi v S bits:ℝ) ∧
    (evaluate A R C K hK hW j xi v S bits:ℝ) ≤ (1+(xi:ℝ))*RootedAnnealing.weight A R j S

end

end ContingencyTables.RootedWeightOracle

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPhaseOracleError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Error of actual selected-root calls in a rational phase update -/

namespace ContingencyTables.RootedPhaseWords

open CompanionFactorialApplication CompanionOracleDensity RootedWeightOracle CompanionRationalUpdates
open CommonBasesFPRAS FiniteIndependentAverages GridBoundary TwoLiftStates
open CompanionPhaseWords (phaseBits phaseWordEquiv )
open CompanionWeightOracle (WeightWord)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

def accurateCalls (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (states : Fin N → Set (Labels A×Bool))
    (bits : Fin (phaseBits A C K j N xi) → Bool) : Prop :=
  ∀ i,accurateCall A R C K j hK hW xi v (states i) (phaseWordEquiv A C K j N xi bits i).1 ∧
    accurateCall A R C K (j+1) hK hW xi v (states i) (phaseWordEquiv A C K j N xi bits i).2

end
end ContingencyTables.RootedPhaseWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedBooleanPhase
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual finite-word Metropolis steps using the selected-root oracle -/

namespace ContingencyTables.RootedBooleanPhase

open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle CompanionRationalUpdates
open CommonBasesFPRAS FirstSuccess FairBits TwoLiftStates GridBoundary ResidualMixture
open CompanionBooleanPhase (State proposal proposalBits proposal_codes stepBits stepWordEquiv)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

/-- The realized step evaluates the current and proposed weights from
separate words, then uses a third independent word for its rational coin. -/
def step (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S : State A) (bits : Fin (stepBits A C K j k xi) → Bool) : State A :=
  let b := stepWordEquiv A C K j k xi bits
  if b.1 0 then S else
    match proposal A S b.2.1 with
    | none => S
    | some T =>
        if rationalThresholdAccept k
          (RootedOracleAcceptance.acceptance A R C K j hK hW xi v w S.val T.val b.2.2.1) b.2.2.2
        then T else S

def transitionLaw (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ) (S : State A) :
    RationalLaw (State A) :=
  mapLaw (uniformLaw (α := Fin (stepBits A C K j k xi) → Bool))
    (step A R C K j k hK hW xi v w S)

end
end ContingencyTables.RootedBooleanPhase

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedWarmStart
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual companion transversal masses and adjacent warm starts -/

namespace ContingencyTables.RootedWarmStart

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication RootedAnnealing
open CompanionInitialization (freeTotal)
open TwoLiftStates LabelledFactorial

variable {I J : Type*} [Fintype I] [Fintype J]

lemma actual_degree (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) :
    BinaryContraction.DegreePositive (weight A R j)
      (pairs : List ((Labels A×Bool)×(Labels A×Bool))).length ∧
    BinaryContraction.OmissionProperty (weight A R j)
      (pairs : List ((Labels A×Bool)×(Labels A×Bool))).length := by
  have hs := RootedFactorialApplication.first_properties A R ((j:ℝ)/CompanionAnnealing.scale A)
    (div_nonneg (Nat.cast_nonneg j) (CompanionAnnealing.scale_positive A).le)
  simpa only [weight,PairedLabels.length] using hs

end ContingencyTables.RootedWarmStart

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedBooleanKernel
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selected-root Boolean row law and full-history perturbation -/

namespace ContingencyTables.RootedBooleanPhase

open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle
open CompanionRationalUpdates RootedOracleAcceptance
open CommonBasesFPRAS FirstSuccess FairBits TwoLiftStates GridBoundary ResidualMixture
open FiniteLawMoments RealKernelApproximation
open CompanionBooleanPhase (State proposal proposalBits proposal_codes stepBits stepWordEquiv
  slowdown slowdown_bounds)
open CompanionConcentration (pairs_ne_nil)
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def pathLaw (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k N n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ) (S : State A) :
    RationalLaw (PathState (State A) N) :=
  walkLaw (liftRational (transitionLaw A R C K j k hK hW xi v w)
    (fun a : PathState (State A) N => pathRead a)
    (fun (a : PathState (State A) N) (T : State A) => pathPut a T)) (pathInitial N S) n

/-- The same finite step word records the newly sampled state, so the
history law is physically realized by the concatenated step words. -/
def recordedWalk (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k N n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ) (S : State A)
    (bits : Fin (n*stepBits A C K j k xi) → Bool) : PathState (State A) N :=
  wordWalk (fun a b => pathPut a (step A R C K j k hK hW xi v w (pathRead a) b))
    (pathInitial N S) n (oracleWalkWordEquiv n (stepBits A C K j k xi) bits)

end
end ContingencyTables.RootedBooleanPhase

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedTrace
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Trace restart bounds for the selected-root companion weights

The actual factorial lifts supply the trace inverse gap, and exact
binomial cancellation supplies its minimum mass. The restart stage
therefore has a two-warm endpoint from every initial subprobability law.
-/

namespace ContingencyTables.RootedTrace

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication RootedAnnealing TwoLiftStates
open CompanionAnnealing (scale scale_positive)
open CompanionTrace (integerConstant time minimumMass )
open BinaryContraction DegreeCompletion ObservableBounds
open RootedWarmStart (actual_degree)
open CompanionConcentration (pairs_ne_nil )

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def trace (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0 < Fintype.card (Labels A))
    (w : ((Labels A×Bool)×(Labels A×Bool)) → ((Labels A×Bool)×(Labels A×Bool)) → ℝ)
    (hw : ∀ p r,0 < w p r) : FiniteChain (PlainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool)))) :=
  metropolisTrace pairs PairedLabels.fresh (pairs_ne_nil A hp) PairedLabels.cover w
    (completeDegree (weight A R j) (pairs : List ((Labels A×Bool)×(Labels A×Bool))).length)
    hw (completeDegree_positive _ _ (actual_degree A R j).1)

end ContingencyTables.RootedTrace

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedWarmReturn
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Warm input error of the actual selected-root bounded return law -/

namespace ContingencyTables.RootedWarmReturn

open CommonBasesFPRAS ResidualMixture FirstSuccess FiniteLawMoments RealKernelApproximation
open CompanionFactorialApplication RootedBooleanPhase CompanionOracleDensity
open CompanionWeightOracle CompanionRationalUpdates RootedTraceWords
open RootedCappedReturn RootedTargetTrace RootedAnnealing RootedWarmStart
open CompanionConcentration (pairs_ne_nil)
open CompanionBooleanPhase (State stepBits)
open CompanionTraceWords (eventIndicator)
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

def returnLaw (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S : PlainIndex (pairs : List (Pair A))) : RationalLaw (PlainIndex (pairs : List (Pair A))) :=
  mapLaw (uniformLaw (α := Fin ((n+1)*stepBits A C K j k xi) → Bool))
    (returnWordDefault A R C K j k n hK hW xi v w S)

def returnKernel (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ) :
    FiniteKernel (PlainIndex (pairs : List (Pair A))) (PlainIndex (pairs : List (Pair A))) :=
  rationalKernel (returnLaw A R C K j k n hK hW xi v w)

end
end ContingencyTables.RootedWarmReturn

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedReturnWords
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
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
open CompanionFactorialApplication RootedBooleanPhase CompanionOracleDensity
open CompanionBooleanPhase (stepBits)
open CompanionReturnWords (returnBits)
open RootedCappedReturn RootedWarmReturn
open CompanionRationalUpdates RootedAnnealing TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

def booleanReturnsLaw (A : Instance I J) (R : RootedCompletion.Selection A.T) (C K j k n t : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w : Pair A → Pair A → ℚ)
    (S : PlainIndex (pairs : List (Pair A))) :
    RationalLaw (PlainIndex (pairs : List (Pair A))) :=
  mapLaw (uniformLaw (α := Fin (returnBits A C K j k n t xi) → Bool))
    (booleanReturns A R C K j k n t hK hW xi v w S)

end
end ContingencyTables.RootedReturnWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedRestartStages
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Successive selected-root restart stages

The reference law is refreshed by the exact trace at each successive
parameter. Only that reference law is asserted to be warm. The actual
bounded-return law is compared to it by contraction and accumulated error.
-/

namespace ContingencyTables.RootedRestartStages

open CommonBasesFPRAS RealKernelApproximation CompanionFactorialApplication
open CompanionRationalUpdates RootedAnnealing RootedWarmStart RootedTargetTrace
open RootedTargetMixing RootedWarmReturn
open CompanionTargetMixing (restartTime)
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

def implemented (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K H L k n : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (CompanionOracleDensity.dimension A)) K)
    (w : ℕ → Pair A → Pair A → ℚ)
    (initial : PlainIndex (pairs : List (Pair A)) → ℝ) :
    ℕ → PlainIndex (pairs : List (Pair A)) → ℝ
  | 0 => initial
  | j+1 => ((returnKernel A R C K (j+1) k n hK hW xi v (w (j+1))).power
      (restartTime A H L)).push (implemented A R C K H L k n hK hW xi v w initial j)

end
end ContingencyTables.RootedRestartStages

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedHistoryConfidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Success probability of the actual adaptive selected-root history -/

namespace ContingencyTables.RootedHistoryConfidence

open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates
open CompanionOracleDensity RootedPhaseHistory RootedStoredHistory RootedHistoryStep
open CompanionTraceWords (eventIndicator)
open TwoLiftStates GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

def GoodWords (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (s : Settings A) (eta : ℝ) (words : List (Word A s)) : Prop :=
  Good A R s.xi eta (decoded A R s words)

end
end ContingencyTables.RootedHistoryConfidence

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_OffsetCountProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact binary tabulation of the bounded offset law -/

namespace ContingencyTables.OffsetCountPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

def endpointRealizer : Realizer endpoint :=
  composition (pair
    (composition (pair second (composition first second)) multiply)
    (composition first first)) ceilQuotientRealizer

def offsetCountRealizer : Realizer offsetCount :=
  composition (pair
    (composition (pair first (composition second successor)) endpointRealizer)
    endpointRealizer) subtract

end ContingencyTables.OffsetCountPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCatalogStep
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual oracle transition in computed catalog order

Axis proposals are uniform over a bounded dyadic code space. Changing
the coordinate order preserves their frequencies, even though it need
not preserve the value obtained from an individual proposal word.
-/

namespace ContingencyTables.RootedCatalogGrid

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open RootedCompletion ResidualMixture FirstSuccess FairBits
open CompanionOracleDensity (oracleStepBits rationalHeight)
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

def exponent (A : Instance (Fin m) (Fin n)) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (freeCount A)) K) : ℕ :=
  RootedOracleDensity.gridExponent A (rowColumn A.T) C a z (gridEquiv A K v)

def finiteStepLaw (A : Instance (Fin m) (Fin n)) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (freeCount A)) K) :
    RationalLaw (Grid (I := Fin (freeCount A)) K) :=
  finiteAcceptLaw v (fun code : Fin (2^Nat.clog 2 (8*A.d)) => axisCodeStep v code)
    (fun w => acceptDyadic (exponent A C a z w-exponent A C a z v) (rationalHeight A C))

def bitStep (A : Instance (Fin m) (Fin n)) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (freeCount A)) K)
    (bits : Fin (oracleStepBits A C) → Bool) : Grid (I := Fin (freeCount A)) K :=
  let draw := pairWordEquiv (Nat.clog 2 (8*A.d)) (rationalHeight A C) bits
  match axisCodeStep v draw.1 with
  | none => v
  | some w => if draw.2.val < 2^(rationalHeight A C-(exponent A C a z w-exponent A C a z v))
      then w else v

def bitStepLaw (A : Instance (Fin m) (Fin n)) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (freeCount A)) K) :
    RationalLaw (Grid (I := Fin (freeCount A)) K) :=
  mapLaw (uniformLaw (α := Fin (oracleStepBits A C) → Bool)) (bitStep A C a z v)

end
end ContingencyTables.RootedCatalogGrid

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedBinDrawLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed bin program has the analysed independent law

The execution order is the computed free-cell catalog.  The mathematical
law uses another enumeration.  Dependent word equivalences identify their
independent Boolean inputs, while preserving each physical cell's draw.
-/

namespace ContingencyTables.RootedBinDrawLaw

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity FirstSuccess ResidualMixture FairBits
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

attribute [local instance] OAI.ContingencyTables.RootedBinDrawLaw.freeCellDecidableEq
def draw (A : Instance (Fin m) (Fin n)) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (h : ℕ) (bits : Words A h) : FreeIndex A.small A.T A.b :=
  binWordDraw A K hK hW (RootedCatalogGrid.gridEquiv A K v) h (reindexWords A h bits)

def flatDraw (A : Instance (Fin m) (Fin n)) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (h : ℕ) (bits : Fin (wordBits A h) → Bool) : FreeIndex A.small A.T A.b :=
  draw A K hK hW v h (wordEquiv A h bits)

end
end ContingencyTables.RootedBinDrawLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleFlatProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial flat-word program for the actual oracle walk -/

namespace ContingencyTables.RootedOracleWalkProgram

open MatchingFPRAS.TreeTyped DensePrograms
open scoped Classical

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary FirstSuccess ResidualMixture

noncomputable section
variable {m n : ℕ}

def flatGridWalk (A : Instance (Fin m) (Fin n)) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (N : ℕ)
    (bits : Fin (N*CompanionOracleDensity.oracleStepBits A C) → Bool) :
    Grid (I := Fin (RootedCatalogGrid.freeCount A)) K :=
  wordWalk (RootedCatalogGrid.bitStep A C a z) v N
    (gridWordEquiv N (CompanionOracleDensity.oracleStepBits A C) bits)

end
end ContingencyTables.RootedOracleWalkProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCorrectionSampleLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact law of the executed correction sample

The two coordinate enumerations need not agree on a fixed bit string.
Their independent finite-word laws agree, which preserves every real
observable of the computed rational sample.
-/

namespace ContingencyTables.RootedCorrectionSampleLaw

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity ResidualMixture FirstSuccess FairBits
open CommonBasesFPRAS FiniteLawMoments
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

attribute [local instance] OAI.ContingencyTables.RootedCorrectionSampleLaw.freeCellDecidableEq
def integerDraw (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (N h : ℕ)
    (bits : Words A C N h) : FreeIndex A.small A.T A.b :=
  RootedBinDrawLaw.flatDraw A K (by omega) hW
    (RootedOracleWalkProgram.flatGridWalk A C a z v N bits.1) h bits.2

def sample (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (z : View A → ℕ)
    (sigma : ℚ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (N h : ℕ)
    (bits : Words A C N h) : ℚ :=
  RootedOracleDensity.computedCorrection A (RootedCompletion.rowColumn A.T) C a z K
    (by omega) sigma (integerDraw A C a K hK hW z v N h bits)

end
end ContingencyTables.RootedCorrectionSampleLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedRatioSampleLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed ratio sample has the exact analysed law -/

namespace ContingencyTables.RootedRatioSampleLaw

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity ResidualMixture FirstSuccess FiniteLawMoments
open CommonBasesFPRAS FiniteObservableTransport
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

def sample (A : Instance (Fin m) (Fin n)) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (N : ℕ)
    (bits : Fin (N*oracleStepBits A C) → Bool) : ℚ :=
  RootedOracleDensity.rationalRatioObservable A (RootedCompletion.rowColumn A.T) C a z
    (RootedCatalogGrid.gridEquiv A K (RootedOracleWalkProgram.flatGridWalk A C a z v N bits))

end
end ContingencyTables.RootedRatioSampleLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedComputedEstimator
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed blocks have the complete estimator law

Only the physical sample programs differ from the original enumeration.
Exact independent-observable transport identifies their whole product
estimator, including every event used by the confidence proof.
-/

namespace ContingencyTables.RootedComputedEstimator

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity FirstSuccess ResidualMixture FiniteObservableTransport
open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

def ratioAverage (A : Instance (Fin m) (Fin n)) (C K j a : ℕ)
    (delta failure : ℚ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (draws : RatioWords A C K j delta failure) : ℚ :=
  (∑ i,RootedRatioSampleLaw.sample A C a z v (oracleTime A C K 1 delta) (draws i))/
    sampleCount j delta failure

def correctionAverage (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (delta failure : ℚ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (draws : CorrectionWords A C K j delta failure) : ℚ :=
  (∑ i,RootedCorrectionSampleLaw.sample A C j K hK hW z (roundingTolerance delta) v
    (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta) (draws i))/
      sampleCount j delta failure

def estimate (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (delta failure : ℚ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (draws : Inputs A C K j delta failure) : ℚ :=
  (assignmentCount A:ℚ)*(∏ a : Fin j,ratioAverage A C K j a.val delta failure z v (draws.1 a))*
    correctionAverage A C K j hK hW delta failure z v draws.2

end
end ContingencyTables.RootedComputedEstimator

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingDirectProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
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

def accuracyRealizer : Realizer accuracy :=
  composition (composition (composition (composition first first) second)
    CountingBaseProgram.halfRealizer) CountingBaseProgram.halfRealizer
def reserveRealizer : Realizer reserve := composition second (map (constant false))

def oracleInput (z : Input) : RootedOracleConfigProgram.Input :=
  (((CountingPreparedState.state z.1.1,accuracy z),CountingTerminalProgram.phases z.1.1),reserve z)
def oracleInputRealizer : Realizer oracleInput :=
  pair (pair (pair (composition (f := fun z : Input => z.1.1) (g := CountingPreparedState.state)
    (composition first first) CountingPreparedState.stateRealizer) accuracyRealizer)
    (composition (f := fun z : Input => z.1.1) (g := CountingTerminalProgram.phases)
      (composition first first) CountingTerminalProgram.phasesRealizer)) reserveRealizer

def rawConfig (z : Input) : RootedLabelWeightProgram.Config := RootedOracleConfigProgram.output (oracleInput z)
def rawConfigRealizer : Realizer rawConfig :=
  composition (f := oracleInput) (g := RootedOracleConfigProgram.output)
    oracleInputRealizer RootedOracleConfigProgram.outputRealizer
attribute [local irreducible] rawConfig

def context (z : Input) : RootedEstimatorLayoutProgram.Context := (rawConfig z).1.1
def contextRealizer : Realizer context := composition (composition rawConfigRealizer first) first

def repeats (z : Input) : ℕ := FractionRepetitionProgram.count z.1.2
def repeatsRealizer : Realizer repeats :=
  composition (f := fun z : Input => z.1.2) (g := FractionRepetitionProgram.count)
    (composition first second) FractionRepetitionProgram.countRealizer

def markers (z : Input) : List Bool×List Bool := (rawConfig z).2
def markersRealizer : Realizer markers := composition rawConfigRealizer second
attribute [local irreducible] context repeats markers

def config (z : Input) : RootedLabelWeightProgram.Config := ((context z,repeats z),markers z)
def configRealizer : Realizer config := pair (pair contextRealizer repeatsRealizer) markersRealizer
attribute [local irreducible] config

def contextWidth (z : Input) : ℕ := RootedOracleConfigProgram.contextWidth (oracleInput z)
def contextWidthRealizer : Realizer contextWidth :=
  composition (f := oracleInput) (g := RootedOracleConfigProgram.contextWidth)
    oracleInputRealizer RootedOracleConfigProgram.contextWidthRealizer
attribute [local irreducible] contextWidth

def wordWidth (z : Input) : ℕ := repeats z*contextWidth z
def wordWidthRealizer : Realizer wordWidth :=
  composition (f := fun z : Input => (repeats z,contextWidth z))
    (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair repeatsRealizer contextWidthRealizer) multiply

def sampleBits (z : Input) : List Bool := z.2.take (wordWidth z)
def sampleBitsRealizer : Realizer sampleBits :=
  composition (f := fun z : Input => (z.2,wordWidth z))
    (g := fun p : List Bool×ℕ => p.1.take p.2) (pair second wordWidthRealizer) takeFast

def medianInput (z : Input) : RootedEstimatorMedianProgram.Input := ((config z).1,((config z).2,sampleBits z))
def medianInputRealizer : Realizer medianInput :=
  pair (composition configRealizer first) (pair (composition configRealizer second) sampleBitsRealizer)

def output (z : Input) : TreeFraction.Fraction := RootedEstimatorMedianProgram.output (medianInput z)
def outputRealizer : Realizer output :=
  composition (f := medianInput) (g := RootedEstimatorMedianProgram.output)
    medianInputRealizer RootedEstimatorMedianProgram.outputRealizer

def empty (z : Request) : Input := (z,[])
def emptyRealizer : Realizer empty := pair identity (constant [])

def padding (z : Request) : ℕ :=
  RootedOracleConfigProgram.rootDegree (oracleInput (empty z))+
    RootedOracleConfigProgram.depth (oracleInput (empty z))
def paddingRealizer : Realizer padding :=
  composition (pair (composition (composition emptyRealizer oracleInputRealizer)
    RootedOracleConfigProgram.rootDegreeRealizer)
    (composition (composition emptyRealizer oracleInputRealizer)
      RootedOracleConfigProgram.depthRealizer)) add

def budget (z : Request) : ℕ := wordWidth (empty z)+padding z
def budgetRealizer : Realizer budget :=
  composition (pair (composition emptyRealizer wordWidthRealizer) paddingRealizer) add

end ContingencyTables.CountingDirectProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingAdaptiveInputProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-input preparation for a positive-label counting run -/
namespace ContingencyTables.CountingAdaptiveInputProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

def initialRealizer : Realizer initial :=
  composition (f := initialInput) (g := CompanionInitialStoredProgram.output)
    initialInputRealizer CompanionInitialStoredProgram.outputRealizer

def output (z : Input) : Output := (prepared z,initial z)
def outputRealizer : Realizer output := pair preparedRealizer initialRealizer

/-- The outer confidence parameter is handled by independent repetition. -/
def runInput (z : CountingDirectProgram.Input) : Output×List Bool := (output (z.1.1,z.2),z.2)
def runInputRealizer : Realizer runInput :=
  pair (composition (f := fun z : CountingDirectProgram.Input => (z.1.1,z.2)) (g := output)
    (pair (composition first first) second) outputRealizer) second

end ContingencyTables.CountingAdaptiveInputProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingAmplifiedProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Outer confidence repetition of the executed counting program -/
namespace ContingencyTables.CountingAmplifiedProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped CommonBasesFPRAS GridBoundary
abbrev Input := CountingDirectProgram.Input

variable (single : Input→TreeFraction.Fraction) (F : Realizer single)
variable (width : Request→ℕ) (N : Realizer width)

def prepared (z : Input) : RepeatedFractionProgram.Input Request :=
  ((z.1,(repeats z.1,width z.1)),z.2)
def preparedRealizer : Realizer (prepared width) :=
  pair (pair first (pair (composition (f := fun z : Input => z.1) (g := repeats)
    first repeatsRealizer) (composition (f := fun z : Input => z.1) (g := width) first N))) second

attribute [local irreducible] prepared

def output (z : Input) : TreeFraction.Fraction := RepeatedFractionProgram.output single (prepared width z)
def outputRealizer : Realizer (output single width) :=
  composition (f := prepared width) (g := RepeatedFractionProgram.output single)
    (preparedRealizer width N) (RepeatedFractionProgram.outputRealizer F)

def budget (req : Request) : ℕ := repeats req*width req
def budgetRealizer : Realizer (budget width) :=
  composition (f := fun req : Request => (repeats req,width req))
    (g := fun p : ℕ×ℕ => p.1*p.2) (pair repeatsRealizer N) multiply

end ContingencyTables.CountingAmplifiedProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingBranchProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Public dispatch for the two counting branches

The positive-label evaluator is a program parameter, instantiated by the
adaptive estimator. Feasibility and the zero-label branch are computed from
the same parsed input used by the complete public machine.
-/
namespace ContingencyTables.CountingBranchProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
abbrev Input := CountingDirectProgram.Input

def direct (z : Request) : Bool := decide (CountingComputedSettings.labelCount z.1=0)
def directRealizer : Realizer direct :=
  composition (f := fun z : Request => (CountingComputedSettings.labelCount z.1,0))
    (g := fun p : ℕ×ℕ => decide (p.1=p.2))
    (pair (composition (f := fun z : Request => z.1) (g := CountingComputedSettings.labelCount)
      first CountingComputedSettings.labelCountRealizer) (constant 0)) natEqual

attribute [local irreducible] feasible direct

section Evaluator
variable (positive : Input → TreeFraction.Fraction) (F : Realizer positive)

def feasibleOutput (z : Input) : TreeFraction.Fraction :=
  if direct z.1 then CountingDirectProgram.output z else positive z
def feasibleOutputRealizer : Realizer (feasibleOutput positive) :=
  choose (composition (f := fun z : Input => z.1) (g := direct) first directRealizer) CountingDirectProgram.outputRealizer F

attribute [local irreducible] feasibleOutput

def output (z : Input) : TreeFraction.Fraction :=
  if feasible z.1 then feasibleOutput positive z else (0,1)
def outputRealizer : Realizer (output positive) :=
  choose (composition (f := fun z : Input => z.1) (g := feasible) first feasibleRealizer) (feasibleOutputRealizer positive F) (constant (0,1))

attribute [local irreducible] output

def parsedInput (z : List Symbol×List Bool) : Input :=
  (request (CountingInputParser.parseInput z.1),z.2)
def parsedInputRealizer : Realizer parsedInput :=
  pair (composition (composition first CountingInputParser.publicRealizer) requestRealizer) second

def publicOutput (z : List Symbol×List Bool) : List Symbol :=
  FractionOutputProgram.output (output positive (parsedInput z))
def publicOutputRealizer : Realizer (publicOutput positive) :=
  composition (f := fun z => output positive (parsedInput z)) (g := FractionOutputProgram.output)
    (composition (f := parsedInput) (g := output positive) parsedInputRealizer (outputRealizer positive F))
    FractionOutputProgram.outputRealizer

end Evaluator

section Budget
variable (positive : Request → ℕ) (N : Realizer positive)

def feasibleBudget (z : Request) : ℕ := if direct z then CountingDirectProgram.budget z else positive z
def feasibleBudgetRealizer : Realizer (feasibleBudget positive) :=
  choose directRealizer CountingDirectProgram.budgetRealizer N

attribute [local irreducible] feasibleBudget

def budget (z : Request) : ℕ := if feasible z then feasibleBudget positive z else 0
def budgetRealizer : Realizer (budget positive) :=
  choose feasibleRealizer (feasibleBudgetRealizer positive N) (constant 0)

attribute [local irreducible] budget

def publicBudget (as : List Symbol) : ℕ := budget positive (request (CountingInputParser.parseInput as))
def publicBudgetRealizer : Realizer (publicBudget positive) :=
  composition (f := fun as => request (CountingInputParser.parseInput as)) (g := budget positive)
    (composition CountingInputParser.publicRealizer requestRealizer) (budgetRealizer positive N)
end Budget

end ContingencyTables.CountingBranchProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingDirectSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The direct binary evaluator uses the original counting parameters -/
namespace ContingencyTables.CountingDirectProgram
open MatchingFPRAS CompanionFactorialApplication GridBoundary CompanionOracleDensity
open scoped Classical
noncomputable section
variable {m n : ℕ}

def degree (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (epsilon : ℚ) : ℕ :=
  PowerOfTwoApproximation.rootDegree (roundingTolerance
    (innerTolerance (((epsilon/2)/2)/2) (ComputedCountingParameters.phases r c b epsilon)))
def depth (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (epsilon : ℚ) : ℕ :=
  PowerOfTwoApproximation.depth (roundingTolerance
    (innerTolerance (((epsilon/2)/2)/2) (ComputedCountingParameters.phases r c b epsilon)))

end
end ContingencyTables.CountingDirectProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingBranchMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Public-machine output guarantees for the counting dispatcher -/
namespace ContingencyTables.CountingBranchProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream
open scoped Classical
noncomputable section

variable (positive : Input→TreeFraction.Fraction) (F : Realizer positive)
variable (width : Request→ℕ) (N : Realizer width)

noncomputable def machine : RandomMachine :=
  FiniteWordExecution.machine (publicBudgetRealizer width N) (publicOutputRealizer positive F)
noncomputable def machineTime (as : List Symbol) : ℕ :=
  FiniteWordExecution.machineTime (publicBudgetRealizer width N) (publicOutputRealizer positive F) as

def sourceValue (as : List Symbol) (bits : Bits (publicBudget width as)) : ℚ :=
  TreeFraction.val (output positive (parsedInput (as,List.ofFn bits)))

end
end ContingencyTables.CountingBranchProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingDirectLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact law of the executed direct counting estimator -/
namespace ContingencyTables.CountingDirectProgram
open MatchingFPRAS CompanionFactorialApplication CompanionOracleDensity GridBoundary
open CommonBasesFPRAS FiniteObservableTransport
open scoped Classical
noncomputable section
variable {m n : ℕ}

def modelContext (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    RootedEstimatorLayoutProgram.Context :=
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let C := ComputedCountingParameters.coefficient r c b epsilon
  let K := ComputedCountingParameters.binCount r c b epsilon
  RootedEstimatorMedianProgram.context A C K (ComputedCountingParameters.phases r c b epsilon)
    ((epsilon/2)/2) (fun _ => 0)
    (CountingPreparedState.start A K (ComputedCountingParameters.binCount_pos r c b epsilon he))

def modelWidth (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) (delta : ℚ) : ℕ :=
  repetitionCount delta*RootedEstimatorLayoutProgram.wordWidth (modelContext hEK r c b hne epsilon he)

def modelValue (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon)
    (delta : ℚ) (bits : List Bool) : ℚ :=
  TreeFraction.val (RootedEstimatorMedianProgram.output
    ((modelContext hEK r c b hne epsilon he,repetitionCount delta),
      ((List.replicate (degree r c b epsilon) false,List.replicate (depth r c b epsilon) false),bits)))

attribute [local irreducible] modelContext modelWidth modelValue
attribute [local irreducible] ComputedCountingParameters.data ComputedCountingParameters.coefficient
attribute [local irreducible] ComputedCountingParameters.phases ComputedCountingParameters.binCount
attribute [local irreducible] ComputedCountingZero.zeroEstimate ComputedCountingZero.zeroBits

def referenceBits (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) (delta : ℚ) : ℕ :=
  medianEstimatorBits (ComputedCountingParameters.data hEK r c b hne epsilon he)
    (ComputedCountingParameters.coefficient r c b epsilon) (ComputedCountingParameters.binCount r c b epsilon)
    (ComputedCountingParameters.phases r c b epsilon) ((epsilon/2)/2) delta

def reference (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) (delta : ℚ)
    (bits : Fin (referenceBits hEK r c b hne epsilon he delta)→Bool) : ℚ :=
  RootedOracleDensity.medianEstimate (ComputedCountingParameters.data hEK r c b hne epsilon he)
    (ComputedCountingWords.root hEK r c b hne epsilon he) (ComputedCountingParameters.coefficient r c b epsilon)
    (fun _ => 0) (ComputedCountingParameters.binCount r c b epsilon)
    (ComputedCountingParameters.binCount_pos r c b epsilon he)
    (ComputedCountingParameters.cutoff_eq hEK r c b hne epsilon he).ge
    (ComputedCountingParameters.phases r c b epsilon) ((epsilon/2)/2) delta
    (ComputedCountingParameters.start hEK r c b hne epsilon he) bits

attribute [local irreducible] referenceBits reference

end
end ContingencyTables.CountingDirectProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ResidualDenseProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A computed dense completion call from a retained small profile -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def residualDenseDraw (z : ResidualDrawData) : DensePrograms.MatrixCode :=
  DensePrograms.canonicalDenseDraw (residualParameters z.1,z.2)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileTransitionProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A binary small-profile transition with a fresh dense completion -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def stepProposalRealizer : Realizer stepProposal :=
  composition (pair stepCheck (composition second first)) codeNeighborProposalRealizer

def stepCandidateViewsRealizer : Realizer stepCandidateViews :=
  composition (pair stepViews stepProposalRealizer) FirstSuccessProgram.defaultRealizer

def stepCandidateRealizer : Realizer stepCandidate :=
  composition (pair stepCheck stepCandidateViewsRealizer) candidateDataRealizer

def stepCandidateParametersRealizer : Realizer stepCandidateParameters :=
  pair (pair stepCandidateRealizer (composition (composition first first) second))
    (composition first second)

def stepNewMarginsRealizer : Realizer stepNewMargins :=
  composition (f := fun z : ProfileStepInput => residualParameters (stepCandidateParameters z))
    (g := fun z : DensePrograms.CanonicalParameters => z.1)
    (composition (f := stepCandidateParameters) (g := residualParameters)
      stepCandidateParametersRealizer residualParametersRealizer) first

def stepTranslationRealizer : Realizer stepTranslation :=
  pair (pair stepOldMarginsRealizer stepNewMarginsRealizer) stepCompletionRealizer

def profileStepRealizer : Realizer profileStep :=
  (choose (composition stepTranslationRealizer DensePrograms.translationValidRealizer)
    stepCandidateViewsRealizer stepViews).congr
    (by intro z; simp only [profileStep,Function.comp_apply])

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OuterTableProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reconstructing and testing an original table from an outer trial -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms Polynomial

def outerSuccessRealizer : Realizer outerSuccess :=
  composition (pair
    (composition (pair (composition (composition first first) second)
      (composition (composition second first) first)) balancedTestRealizer)
    (composition (pair (composition (composition second first) second)
      (composition second second)) paddingTestRealizer)) boolAnd

def acceptedTableRealizer : Realizer acceptedTable :=
  choose (composition second outerSuccessRealizer)
    (composition outputMatrixRealizer MatchingFPRAS.TreeTyped.some) (constant none)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OuterTrialProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparing the original-table return from a residual draw -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

def outerTrialRealizer : Realizer outerTrial :=
  composition prepareOutputRealizer acceptedTableRealizer

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BoundedProfileWalk
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial loop for the encoded small-profile walk -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

def capViewsRealizer : Realizer capViews :=
  pair (composition (pair capBoundsRealizer (composition second first)) capViewRealizer)
    (composition (pair capBoundsRealizer (composition second second)) capViewRealizer)

def boundedNextRealizer : Realizer boundedNext := by
  let check : Realizer (fun z : ProfileConfiguration×ProfileWord => z.1.1.1.1) :=
    composition (composition (composition first first) first) first
  let input : Realizer (fun z : ProfileConfiguration×ProfileWord => (currentParameters z.1,z.2)) :=
    pair (composition first currentParametersRealizer) second
  exact composition (pair check (composition input profileStepRealizer)) capViewsRealizer

def advanceProfileRealizer : Realizer advanceProfile :=
  pair (composition second first) (composition
    (f := fun z : ProfileWord×ProfileConfiguration => (z.2,z.1)) (g := boundedNext)
    (pair second first) boundedNextRealizer)

def profileWalkRealizer : Realizer profileWalk :=
  composition (pair second first) (fold advanceProfileRealizer)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileTrialProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A complete polynomial outer trial on supplied independent words -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def trialStateRealizer : Realizer trialState := composition first profileWalkRealizer

def trialParametersRealizer : Realizer trialParameters :=
  composition trialStateRealizer currentParametersRealizer

def trialCompletionRealizer : Realizer trialCompletion :=
  composition (pair trialParametersRealizer second) reservedResidualDrawRealizer

def trialOutputInputRealizer : Realizer trialOutputInput :=
  pair (composition trialParametersRealizer first) trialCompletionRealizer

def profileTrialRealizer : Realizer profileTrial :=
  composition trialOutputInputRealizer outerTrialRealizer

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileWordProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Parsing the independent words of the physical outer trial -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

def packedProfileTrialRealizer : Realizer packedProfileTrial :=
  composition prepareProfileTrialRealizer profileTrialRealizer

open FairBits GridBoundary
open scoped Classical
end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileRetryProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial retry loop for the complete binary outer trial -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

def profileRetryRealizer : Realizer profileRetry :=
  composition (pair first profileRetryWordsRealizer)
    (FirstSuccessProgram.retryRealizer packedProfileTrialRealizer)

end ContingencyTables.ProfilePrograms

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

def parameterStepsRealizer : Realizer parameterSteps :=
  composition (f := fun z : SamplingParameters => ((parameterDimension z)^200,((z.2+parameterBinaryLength z))^2)) (g := fun t : ℕ×ℕ => t.1*t.2) (pair (composition (f := fun z : SamplingParameters => parameterDimension z) (g := fun n : ℕ => n^200) (parameterDimensionRealizer) twoHundredthPower) (composition (f := fun z : SamplingParameters => (z.2+parameterBinaryLength z)) (g := fun n : ℕ => n^2) (composition (f := fun z : SamplingParameters => (z.2,parameterBinaryLength z)) (g := fun t : ℕ×ℕ => t.1+t.2) (pair (second) (parameterBinaryLengthRealizer)) add) squarePower)) multiply

def parameterAccuracyRealizer : Realizer parameterAccuracy :=
  composition (f := fun z : SamplingParameters => ((parameterDimension z)^4,((z.2+parameterBinaryLength z))^2)) (g := fun t : ℕ×ℕ => t.1*t.2) (pair (composition (f := fun z : SamplingParameters => parameterDimension z) (g := fun n : ℕ => n^4) (parameterDimensionRealizer) fourthPower) (composition (f := fun z : SamplingParameters => (z.2+parameterBinaryLength z)) (g := fun n : ℕ => n^2) (composition (f := fun z : SamplingParameters => (z.2,parameterBinaryLength z)) (g := fun t : ℕ×ℕ => t.1+t.2) (pair (second) (parameterBinaryLengthRealizer)) add) squarePower)) multiply

def parameterProposalWidthRealizer : Realizer parameterProposalWidth :=
  composition (f := fun z : SamplingParameters => (32*(parameterDimension z)^2)) (g := Nat.clog 2) (composition (f := fun z : SamplingParameters => (32,(parameterDimension z)^2)) (g := fun t : ℕ×ℕ => t.1*t.2) (pair (constant 32) (composition (f := fun z : SamplingParameters => parameterDimension z) (g := fun n : ℕ => n^2) (parameterDimensionRealizer) squarePower)) multiply) ceilLogTwoRealizer

def parameterCompletionWidthRealizer : Realizer parameterCompletionWidth :=
  composition (f := fun z : SamplingParameters => (25,((((parameterDimension z+parameterBinaryLength z)+parameterAccuracy z)+1))^62)) (g := fun t : ℕ×ℕ => t.1*t.2) (pair (constant 25) (composition (f := fun z : SamplingParameters => (((parameterDimension z+parameterBinaryLength z)+parameterAccuracy z)+1)) (g := fun n : ℕ => n^62) (composition (f := fun z : SamplingParameters => (((parameterDimension z+parameterBinaryLength z)+parameterAccuracy z),1)) (g := fun t : ℕ×ℕ => t.1+t.2) (pair (composition (f := fun z : SamplingParameters => ((parameterDimension z+parameterBinaryLength z),parameterAccuracy z)) (g := fun t : ℕ×ℕ => t.1+t.2) (pair (composition (f := fun z : SamplingParameters => (parameterDimension z,parameterBinaryLength z)) (g := fun t : ℕ×ℕ => t.1+t.2) (pair (parameterDimensionRealizer) (parameterBinaryLengthRealizer)) add) (parameterAccuracyRealizer)) add) (constant 1)) add) sixtySecondPower)) multiply

def parameterWordCountRealizer : Realizer parameterWordCount :=
  composition (f := fun z : SamplingParameters => (parameterTrials z,((parameterSteps z*(parameterProposalWidth z+parameterCompletionWidth z))+parameterCompletionWidth z))) (g := fun t : ℕ×ℕ => t.1*t.2) (pair (parameterTrialsRealizer) (composition (f := fun z : SamplingParameters => ((parameterSteps z*(parameterProposalWidth z+parameterCompletionWidth z)),parameterCompletionWidth z)) (g := fun t : ℕ×ℕ => t.1+t.2) (pair (composition (f := fun z : SamplingParameters => (parameterSteps z,(parameterProposalWidth z+parameterCompletionWidth z))) (g := fun t : ℕ×ℕ => t.1*t.2) (pair (parameterStepsRealizer) (composition (f := fun z : SamplingParameters => (parameterProposalWidth z,parameterCompletionWidth z)) (g := fun t : ℕ×ℕ => t.1+t.2) (pair (parameterProposalWidthRealizer) (parameterCompletionWidthRealizer)) add)) multiply) (parameterCompletionWidthRealizer)) add)) multiply

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileSamplingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparing and executing the complete profile sampler -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

def initialConfigurationRealizer : Realizer initialConfiguration :=
  pair (pair (pair (composition (f := fun z : SamplingParameters => z.1) (g := initialCheck) first initialCheckRealizer)
    (composition (f := fun z : SamplingParameters => z.1) (g := marginPadding) first marginPaddingRealizer))
    (pair parameterDimensionRealizer parameterAccuracyRealizer))
    (composition (f := fun z : SamplingParameters => z.1) (g := initialViews) first initialViewsRealizer)

def samplingScheduleRealizer : Realizer samplingSchedule :=
  pair (pair parameterStepsRealizer parameterProposalWidthRealizer) parameterCompletionWidthRealizer

def samplingRetryParametersRealizer : Realizer samplingRetryParameters :=
  pair (pair initialConfigurationRealizer samplingScheduleRealizer)
    (composition (f := fun z : SamplingParameters => z.1) (g := fun z => GreedyFeasibleTable.listMatrix z.1 z.2) first GreedyFeasibleTable.tableRealizer)

def samplingMatrixRealizer : Realizer samplingMatrix :=
  composition (f := fun z : SamplingParameters×List Bool => (samplingRetryParameters z.1,z.2))
    (g := profileRetry)
    (pair (composition (f := fun z : SamplingParameters×List Bool => z.1)
      (g := samplingRetryParameters) first samplingRetryParametersRealizer) second) profileRetryRealizer

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfilePublicProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sampler's public binary parser and matrix printer -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped MatchingFPRAS.LiteralParse MatchingFPRAS.LiteralCodec
open DensePrograms

def publicWordCountRealizer : Realizer publicWordCount :=
  composition (f := parsedSampling) (g := parameterWordCount) parsedSamplingRealizer parameterWordCountRealizer

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPositiveProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One executed positive-label counting run

The supplied word is partitioned into equally padded phase words. The phase
count only truncates a supplied list, so malformed scalar inputs do
not create an unbounded loop.
-/
namespace ContingencyTables.CountingPositiveProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

abbrev Input := CountingDirectProgram.Input

def prepared (req : Request) : Prepared := CountingPreparedState.output req.1
def preparedRealizer : Realizer prepared :=
  composition (f := Prod.fst) (g := CountingPreparedState.output)
    first CountingPreparedState.outputRealizer

def phaseCount (req : Request) : ℕ :=
  CountingPhaseParametersProgram.scalar (.input 2) (prepared req).2
def phaseCountRealizer : Realizer phaseCount :=
  composition (f := fun req : Request => (prepared req).2)
    (g := CountingPhaseParametersProgram.scalar (.input 2))
    (composition (f := prepared) (g := Prod.snd) preparedRealizer second)
    (CountingPhaseParametersProgram.scalarRealizer (.input 2))

def phaseWidth (req : Request) : ℕ := CompanionUniformPhaseWidth.width (prepared req)
def phaseWidthRealizer : Realizer phaseWidth :=
  composition (f := prepared) (g := CompanionUniformPhaseWidth.width)
    preparedRealizer CompanionUniformPhaseWidth.widthRealizer

def bitCount (req : Request) : ℕ := phaseCount req*phaseWidth req
def bitCountRealizer : Realizer bitCount :=
  composition (f := fun req : Request => (phaseCount req,phaseWidth req))
    (g := fun p : ℕ×ℕ => p.1*p.2) (pair phaseCountRealizer phaseWidthRealizer) multiply

def words (z : Input) : List (List Bool) :=
  (wordChunks (phaseWidth z.1,z.2)).take (phaseCount z.1)
def wordsRealizer : Realizer words :=
  composition (f := fun z : Input => (wordChunks (phaseWidth z.1,z.2),phaseCount z.1))
    (g := fun p : List (List Bool)×ℕ => p.1.take p.2)
    (pair (composition (f := fun z : Input => (phaseWidth z.1,z.2)) (g := wordChunks)
      (pair (composition (f := Prod.fst) (g := phaseWidth) first phaseWidthRealizer) second)
      wordChunksRealizer)
      (composition (f := Prod.fst) (g := phaseCount) first phaseCountRealizer)) takeFast

def start (z : Input) : CompanionOuterHistoryProgram.Fixed :=
  (CountingAdaptiveInputProgram.runInput z).1
def startRealizer : Realizer start :=
  composition (f := CountingAdaptiveInputProgram.runInput) (g := Prod.fst)
    CountingAdaptiveInputProgram.runInputRealizer first

def historyInput (z : Input) : CompanionOuterHistoryProgram.Input := (start z,words z)
def historyInputRealizer : Realizer historyInput := pair startRealizer wordsRealizer

attribute [local irreducible] historyInput

def finalStored (z : Input) : CompanionOuterHistoryProgram.Stored :=
  CompanionOuterHistoryProgram.output (historyInput z)
def finalStoredRealizer : Realizer finalStored :=
  composition (f := historyInput) (g := CompanionOuterHistoryProgram.output)
    historyInputRealizer CompanionOuterHistoryProgram.outputRealizer

def output (z : Input) : TreeFraction.Fraction := (finalStored z).2
def outputRealizer : Realizer output :=
  composition (f := finalStored) (g := Prod.snd) finalStoredRealizer second

end ContingencyTables.CountingPositiveProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingExecutedMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One fixed counting machine with the computed adaptive program -/
namespace ContingencyTables.CountingExecutedMachine
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream
open scoped Classical
noncomputable section

abbrev positive := CountingAmplifiedProgram.output CountingPositiveProgram.output CountingPositiveProgram.bitCount
abbrev positiveWidth := CountingAmplifiedProgram.budget CountingPositiveProgram.bitCount

def positiveRealizer : Realizer positive := CountingAmplifiedProgram.outputRealizer
  CountingPositiveProgram.output CountingPositiveProgram.outputRealizer
  CountingPositiveProgram.bitCount CountingPositiveProgram.bitCountRealizer

def positiveWidthRealizer : Realizer positiveWidth := CountingAmplifiedProgram.budgetRealizer
  CountingPositiveProgram.bitCount CountingPositiveProgram.bitCountRealizer

def machine : RandomMachine :=
  CountingBranchProgram.machine positive positiveRealizer positiveWidth positiveWidthRealizer

def machineTime (as : List Symbol) : ℕ :=
  CountingBranchProgram.machineTime positive positiveRealizer positiveWidth positiveWidthRealizer as

abbrev wordCount := CountingBranchProgram.publicBudget positiveWidth
abbrev sourceValue := CountingBranchProgram.sourceValue positive positiveWidth

end
end ContingencyTables.CountingExecutedMachine

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPositiveWordLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Flattening the positive run while preserving its complete output law -/
namespace ContingencyTables.CountingPositiveProgram
open MatchingFPRAS CommonBasesFPRAS GridBoundary FiniteObservableTransport
open scoped Classical
noncomputable section

def independentOutput (req : Request)
    (words : Fin (phaseCount req)→Fin (phaseWidth req)→Bool) : TreeFraction.Fraction :=
  (CompanionOuterHistoryProgram.output
    (start (req,List.replicate (bitCount req) false),
      List.ofFn (fun i => List.ofFn (words i)))).2

end
end ContingencyTables.CountingPositiveProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PreparedOffsetCount
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary evaluation of the offset numerator product -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary FairBits
open scoped BigOperators

def preparedOffsetFactorRealizer : Realizer preparedOffsetFactor :=
  composition preparedOffsetInputRealizer OffsetCountPrograms.offsetCountRealizer

def preparedOffsetProductRealizer : Realizer preparedOffsetProduct :=
  composition (composition (pair identity preparedOffsetIndicesRealizer)
    (mapWith preparedOffsetFactorRealizer)) listProd

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseTrialCountProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing one accepted-table numerator from the cached bin vector -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators Classical

def trialTableCountRealizer : Realizer trialTableCount := by
  let idx := composition trialCountIndexInputRealizer gridIndexRealizer
  let bin := composition (pair (composition first first) idx) (getDFast 0)
  let offs := composition trialCountOffsetInputRealizer preparedOffsetProductRealizer
  let result := composition (pair bin offs) multiply
  exact result

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCandidateCounts
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact accepted counts throughout the enumerated completion box -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators Classical

def candidateCountRealizer : Realizer candidateCount :=
  optionCases (constant 0) (composition candidateCountInputRealizer trialTableCountRealizer)

def candidateCountsRealizer : Realizer candidateCounts :=
  composition (pair identity
    (composition (composition second first) completionCandidatesRealizer))
    (mapWith candidateCountRealizer)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseDrawTabulation
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the full integer law of an initialized dense draw -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators Classical

def rawVectorInputRealizer : Realizer rawVectorInput := by
  let markers := composition rawRepeatRealizer unaryMarkersRealizer
  let denominator := composition (pair (constant 2) rawTrialBitsRealizer)
    BinaryPowerPrograms.powerRealizer
  let counts := composition rawCountContextRealizer candidateCountsRealizer
  let result := pair (pair markers denominator) (pair counts rawFallbackIndexRealizer)
  exact result

def rawTabulationMeasure (z : CanonicalParameters) : ℕ :=
  tabulationMeasure z+gridStateCount (completionEnumerationData z.1)+rawTrialBits z+rawRepeat z

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseSuppliedFallback
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dense law tabulation retains the supplied feasible fallback -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators Classical

abbrev SuppliedTabulation := CanonicalParameters×MatrixCode

def replaceVectorFallback (z : VectorRetryPrograms.Input×ℕ) : VectorRetryPrograms.Input :=
  (z.1.1,(z.1.2.1,z.2))

def replaceVectorFallbackRealizer : Realizer replaceVectorFallback :=
  pair (composition first first) (pair (composition (composition first second) first) second)

def suppliedVectorInput (z : SuppliedTabulation) : VectorRetryPrograms.Input :=
  replaceVectorFallback (rawVectorInput z.1,tableIndex (z.1.1,z.2))

def suppliedVectorInputRealizer : Realizer suppliedVectorInput := by
  let base := composition (first (A := CanonicalParameters) (B := MatrixCode))
    rawVectorInputRealizer
  let margins : Realizer (fun z : SuppliedTabulation => z.1.1) := composition first first
  let query := pair margins (second (A := CanonicalParameters) (B := MatrixCode))
  let index := composition query tableIndexRealizer
  let result := composition (pair base index) replaceVectorFallbackRealizer
  exact result

def suppliedTabulationMeasure (z : SuppliedTabulation) : ℕ := rawTabulationMeasure z.1+weight z

def suppliedDrawCounts (z : SuppliedTabulation) : List ℕ :=
  VectorRetryPrograms.counts (suppliedVectorInput z)

def suppliedDrawCountsRealizer : Realizer suppliedDrawCounts :=
  composition suppliedVectorInputRealizer VectorRetryPrograms.countsRealizer

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_OnlinePartialCall
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Calling the actual retry loop without pretending it has halted -/

namespace ContingencyTables.OnlinePartialCall
open MatchingFPRAS MatchingFPRAS.TreeData
open MatchingFPRAS.TreeMachine (Env K encodeEnv)
open MatchingFPRAS.OnlineStack MatchingFPRAS.OnlineControl
open MatchingFPRAS.PhysicalStream Turing

variable {R Λ α : Type} [DecidableEq R]

def At (M : Λ → Instr R Λ) (out : α → Config M)
    (l : Option Λ) (E : Env R) (p : Experiment α) : Prop :=
  Executes (code M) (coins M) out (OnlineControl.cfg M l E) p

end ContingencyTables.OnlinePartialCall

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitProfileProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded profile program for the all-small branch -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms Polynomial

def unitNextRealizer : Realizer unitNext :=
  composition (f := fun z : UnitStepInput =>
      (z.1.1.1.1,stepCandidateViews (unitCandidateInput z))) (g := capViews)
    (pair (composition (composition (composition first first) first) first)
      (composition (f := unitCandidateInput) (g := stepCandidateViews)
        unitCandidateInputRealizer stepCandidateViewsRealizer)) capViewsRealizer

def unitAdvanceRealizer : Realizer unitAdvance :=
  pair (composition second first) (composition (f := fun z : List Bool×ProfileConfiguration => (z.2,z.1))
    (g := unitNext) (pair second first) unitNextRealizer)

def unitProfileWalkRealizer : Realizer unitProfileWalk :=
  composition (pair second first) (fold unitAdvanceRealizer)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitTrialProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All-small trials and retries use only the stored profile entries -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

def unitPackedStateRealizer : Realizer unitPackedState :=
  composition (f := fun z : PackedProfileTrial => (z.1.1,unitPackedWords z)) (g := unitProfileWalk)
    (pair (composition first first) unitPackedWordsRealizer) unitProfileWalkRealizer

def unitPackedTrialRealizer : Realizer unitPackedTrial :=
  composition (f := fun z : PackedProfileTrial => ((currentParameters (unitPackedState z)).1,[]))
    (g := outerTrial) (pair
      (composition (f := fun z : PackedProfileTrial => currentParameters (unitPackedState z))
        (g := Prod.fst) (composition (f := unitPackedState) (g := currentParameters)
          unitPackedStateRealizer currentParametersRealizer) first) (constant [])) outerTrialRealizer

def unitProfileRetryRealizer : Realizer unitProfileRetry :=
  composition (f := fun z : ProfileRetryData => (z.1,unitRetryWords z))
    (g := FirstSuccessProgram.retry unitPackedTrial) (pair first unitRetryWordsRealizer)
    (FirstSuccessProgram.retryRealizer unitPackedTrialRealizer)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_AllSamplingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single computed sampler for large and all-small rectangles -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

def parameterUnitWordsRealizer : Realizer parameterUnitWords :=
  composition (f := fun z : SamplingParameters =>
    (parameterTrials z,parameterSteps z*parameterProposalWidth z))
    (g := fun p : ℕ×ℕ => p.1*p.2) (pair parameterTrialsRealizer
      (composition (f := fun z : SamplingParameters => (parameterSteps z,parameterProposalWidth z))
        (g := fun p : ℕ×ℕ => p.1*p.2) (pair parameterStepsRealizer parameterProposalWidthRealizer) multiply)) multiply

attribute [local irreducible] parameterUnitWords

def unitSamplingBitsRealizer : Realizer unitSamplingBits :=
  composition (f := fun z : SamplingWordInput => (z.2,parameterUnitWords z.1))
    (g := fun z : List Bool×ℕ => z.1.take z.2)
    (pair (f := fun z : SamplingWordInput => z.2)
      (g := fun z : SamplingWordInput => parameterUnitWords z.1) second
      (composition (f := fun z : SamplingWordInput => z.1)
        (g := parameterUnitWords) first parameterUnitWordsRealizer)) takeFast

def unitSamplingInputRealizer : Realizer unitSamplingInput :=
  pair (composition (f := fun z : SamplingWordInput => z.1) (g := samplingRetryParameters)
    first samplingRetryParametersRealizer) unitSamplingBitsRealizer

def unitSamplingMatrixRealizer : Realizer unitSamplingMatrix :=
  composition (f := unitSamplingInput) (g := unitProfileRetry)
    unitSamplingInputRealizer unitProfileRetryRealizer

def samplingMatrixAllRealizer : Realizer samplingMatrixAll :=
  choose (composition (f := fun z : SamplingParameters×List Bool => z.1) (g := hasLargeRectangle)
    first hasLargeRectangleRealizer) samplingMatrixRealizer unitSamplingMatrixRealizer

def publicSamplingAll (z : List MatchingFPRAS.Symbol×List Bool) : List MatchingFPRAS.Symbol :=
  GreedyFeasibleTable.printMatrix (samplingMatrixAll (parsedSampling z.1,z.2))
def publicSamplingAllRealizer : Realizer publicSamplingAll :=
  composition (f := fun z : List MatchingFPRAS.Symbol×List Bool =>
      samplingMatrixAll (parsedSampling z.1,z.2)) (g := GreedyFeasibleTable.printMatrix)
    (composition (f := fun z : List MatchingFPRAS.Symbol×List Bool => (parsedSampling z.1,z.2))
      (g := samplingMatrixAll) (pair (composition (f := fun z : List MatchingFPRAS.Symbol×List Bool => z.1)
        (g := parsedSampling) first parsedSamplingRealizer) second) samplingMatrixAllRealizer)
      GreedyFeasibleTable.printMatrixRealizer

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_CanonicalDrawTabulation
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact dense counts after computed maximal-margin normalization -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators Classical

def canonicalCountInput (z : CanonicalParameters) : SuppliedTabulation :=
  ((swapMargins (marginIndices z.1,z.1),z.2),
    swapMatrix (marginIndices z.1,GreedyFeasibleTable.listMatrix z.1.1 z.1.2))

def canonicalCountInputRealizer : Realizer canonicalCountInput := by
  let source : Realizer (fun z : CanonicalParameters => z.1) := first
  let indices := composition source marginIndicesRealizer
  let margins := composition (pair indices source) swapMarginsRealizer
  let fallback := composition source GreedyFeasibleTable.tableRealizer
  let precision : Realizer (fun z : CanonicalParameters => z.2) := second
  let result := pair (pair margins precision)
    (composition (pair indices fallback) swapMatrixRealizer)
  exact result

attribute [local irreducible] canonicalCountInputRealizer suppliedDrawCountsRealizer

def canonicalDrawCounts : CanonicalParameters → List ℕ :=
  suppliedDrawCounts ∘ canonicalCountInput

def canonicalDrawCountsRealizer : Realizer canonicalDrawCounts := by
  let result := composition (f := canonicalCountInput) (g := suppliedDrawCounts)
    canonicalCountInputRealizer suppliedDrawCountsRealizer
  exact result

def canonicalTabulationMeasure (z : CanonicalParameters) : ℕ :=
  suppliedTabulationMeasure (canonicalCountInput z)+weight z

/-- The lookup index uses exactly the same two swaps as the sampler. -/
def canonicalTableIndex (z : CanonicalParameters×MatrixCode) : ℕ :=
  tableIndex ((canonicalCountInput z.1).1.1,swapMatrix (marginIndices z.1.1,z.2))

def canonicalTableIndexRealizer : Realizer canonicalTableIndex := by
  let source : Realizer (fun z : CanonicalParameters×MatrixCode => z.1) := first
  let normalized := composition source canonicalCountInputRealizer
  let margins := composition (composition normalized first) first
  let originals : Realizer (fun z : CanonicalParameters×MatrixCode => z.1.1) :=
    composition first first
  let indices := composition originals marginIndicesRealizer
  let query := composition (pair indices second) swapMatrixRealizer
  exact composition (pair margins query) tableIndexRealizer

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CachedCompletionWeights
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit table weights from the computed dense-law cache -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators Classical

abbrev CompletionCache := CanonicalParameters×List ℕ

def cachedCompletionWeight (z : CompletionCache×Option MatrixCode) : ℕ :=
  z.2.elim 0 (fun X => z.1.2.getD (canonicalTableIndex (z.1.1,X)) 0)

def cachedCompletionWeightRealizer : Realizer cachedCompletionWeight := by
  let context : Realizer (fun z : CompletionCache×MatrixCode => z.1.1) :=
    composition first first
  let cache : Realizer (fun z : CompletionCache×MatrixCode => z.1.2) :=
    composition first second
  let index := composition (pair context second) canonicalTableIndexRealizer
  let entry := composition (pair cache index) (getDFast 0)
  exact optionCases (constant 0) entry

def completionWeightEntry (z : CompletionCache×Option MatrixCode) : Option MatrixCode×ℕ :=
  (z.2,cachedCompletionWeight z)

def completionWeightEntryRealizer : Realizer completionWeightEntry :=
  pair second cachedCompletionWeightRealizer

def completionWeightInput (z : CanonicalParameters) : CompletionCache×List (Option MatrixCode) :=
  ((z,canonicalDrawCounts z),completionCandidates z.1)

def completionWeightInputRealizer : Realizer completionWeightInput :=
  pair (pair identity canonicalDrawCountsRealizer)
    (composition first completionCandidatesRealizer)

def completionWeightMeasure (z : CanonicalParameters) : ℕ :=
  canonicalTabulationMeasure z+completionEnumerationMeasure z.1

def completionWeights (z : CanonicalParameters) : List (Option MatrixCode×ℕ) :=
  (completionCandidates z.1).map
    (fun o => (o,cachedCompletionWeight ((z,canonicalDrawCounts z),o)))

def completionWeightsRealizer : Realizer completionWeights :=
  composition completionWeightInputRealizer (mapWith completionWeightEntryRealizer)

attribute [local irreducible] canonicalDrawCounts canonicalCounts

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CachedProfileDecision
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reusing the outer transition test on an enumerated completion -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

def cachedDecisionInputRealizer : Realizer cachedDecisionInput := by
  let input := composition (first (A := ShortStep) (B := DensePrograms.MatrixCode))
    shortStepInputRealizer
  let old := composition input stepOldMarginsRealizer
  let next := composition input stepNewMarginsRealizer
  exact pair (pair old next) second

def cachedDecisionRealizer : Realizer cachedDecision := by
  let input := composition (first (A := ShortStep) (B := DensePrograms.MatrixCode))
    shortStepInputRealizer
  let yes := composition input stepCandidateViewsRealizer
  let no := composition input stepViews
  exact (choose (composition cachedDecisionInputRealizer DensePrograms.translationValidRealizer)
    yes no).congr (by intro z; rfl)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CachedStepCount
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted transitions from the cached completion list -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
open scoped BigOperators Classical

attribute [local irreducible] cachedDecisionRealizer cachedDecision

abbrev DecisionQuery := ShortStep×(List ℕ×List ℕ)

/-- A rejected box entry contributes zero. A valid completion contributes
its cached integer multiplicity precisely when it reaches the target. -/
def decisionWeight (z : DecisionQuery×(Option MatrixCode×ℕ)) : ℕ :=
  z.2.1.elim 0 (fun X => if cachedDecision (z.1.1,X)=z.1.2 then z.2.2 else 0)

def decisionWeightRealizer : Realizer decisionWeight := by
  let input : Realizer (fun z : DecisionQuery×(Option MatrixCode×ℕ) =>
      ((z.1,z.2.2),z.2.1)) := pair (pair first (composition second second))
        (composition second first)
  let step : Realizer (fun z : (DecisionQuery×ℕ)×MatrixCode =>
      (z.1.1.1,z.2)) := pair (composition (composition first first) first) second
  let target : Realizer (fun z : (DecisionQuery×ℕ)×MatrixCode => z.1.1.2) :=
    composition (composition first first) second
  let test := composition (pair (composition step cachedDecisionRealizer) target) profileCodeEqual
  let entry := choose test (composition first second) (constant 0)
  exact (composition input (optionCases (constant 0) entry)).congr (by
    intro z
    simp only [Function.comp_apply,decide_eq_true_eq]
    rfl)

def decisionWeightSum (z : DecisionQuery×List (Option MatrixCode×ℕ)) : ℕ :=
  (z.2.map (fun a => decisionWeight (z.1,a))).sum

def decisionWeightSumRealizer : Realizer decisionWeightSum :=
  composition (mapWith decisionWeightRealizer) listSum

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileTransitionCount
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting the short proposal words with a shared dense cache -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
open scoped BigOperators Classical

/-- The scalar is the multiplicity of the ignored completion-bit suffix. -/
abbrev TransitionCache := ResidualParameters×(ℕ×List (Option MatrixCode×ℕ))
abbrev TransitionQuery := (TransitionCache×(List ℕ×List ℕ))×List Bool

def cachedWordInput (z : TransitionQuery) : DecisionQuery×List (Option MatrixCode×ℕ) :=
  (((z.1.1.1,z.2),z.1.2),z.1.1.2.2)

def cachedWordInputRealizer : Realizer cachedWordInput := by
  let context : Realizer (fun z : TransitionQuery => z.1.1) := composition first first
  let params := composition context first
  let entries := composition (composition context second) second
  exact pair (pair (pair params second) (composition first second)) entries

def cachedWordCount (z : TransitionQuery) : ℕ :=
  z.1.1.2.1*decisionWeightSum (cachedWordInput z)

def cachedWordCountRealizer : Realizer cachedWordCount := by
  let scalar : Realizer (fun z : TransitionQuery => z.1.1.2.1) :=
    composition (composition (composition first first) second) first
  let value := composition cachedWordInputRealizer decisionWeightSumRealizer
  exact composition (pair scalar value) multiply

def transitionCount (z : TransitionQuery) : ℕ :=
  ((booleanWords z.2).map (fun bits => cachedWordCount (z.1,bits))).sum

def transitionCountRealizer : Realizer transitionCount := by
  let input : Realizer (fun z : TransitionQuery => (z.1,booleanWords z.2)) :=
    pair first (composition (f := fun z : TransitionQuery => z.2) (g := booleanWords)
      second booleanWordsRealizer)
  let counts := composition (mapWith cachedWordCountRealizer) listSum
  exact composition (f := fun z : TransitionQuery => (z.1,booleanWords z.2))
    (g := fun z : (TransitionCache×(List ℕ×List ℕ))×List (List Bool) =>
      (z.2.map (fun bits => cachedWordCount (z.1,bits))).sum) input counts

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PreparedTransitionCache
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the dense cache and the unused-bit multiplicity -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

attribute [local irreducible] residualParameters residualParametersRealizer canonicalBitCount
  canonicalBitCountRealizer completionWeights completionWeightsRealizer

abbrev TransitionCacheParameters := ResidualParameters×ℕ

def completionMultiplicity (z : TransitionCacheParameters) : ℕ :=
  BinaryPowerPrograms.power (2,z.2-canonicalBitCount (residualParameters z.1))

def completionMultiplicityRealizer : Realizer completionMultiplicity := by
  let used : Realizer (fun z : TransitionCacheParameters =>
      canonicalBitCount (residualParameters z.1)) :=
    composition (f := fun z : TransitionCacheParameters => residualParameters z.1)
      (g := canonicalBitCount)
      (composition (f := fun z : TransitionCacheParameters => z.1) (g := residualParameters)
        first residualParametersRealizer) canonicalBitCountRealizer
  let remaining : Realizer (fun z : TransitionCacheParameters =>
      z.2-canonicalBitCount (residualParameters z.1)) :=
    composition (f := fun z : TransitionCacheParameters =>
      (z.2,canonicalBitCount (residualParameters z.1)))
      (g := fun z : ℕ×ℕ => z.1-z.2) (pair second used) subtract
  exact composition (f := fun z : TransitionCacheParameters =>
      (2,z.2-canonicalBitCount (residualParameters z.1))) (g := BinaryPowerPrograms.power)
    (pair (constant 2) remaining) BinaryPowerPrograms.powerRealizer

def prepareTransitionCache (z : TransitionCacheParameters) : TransitionCache :=
  (z.1,(completionMultiplicity z,completionWeights (residualParameters z.1)))

def prepareTransitionCacheRealizer : Realizer prepareTransitionCache :=
  pair first (pair completionMultiplicityRealizer
    (composition (f := fun z : TransitionCacheParameters => residualParameters z.1)
      (g := completionWeights)
      (composition (f := fun z : TransitionCacheParameters => z.1) (g := residualParameters)
        first residualParametersRealizer) completionWeightsRealizer))

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CachedTerminalCount
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact terminal counts from the retained dense-completion cache -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

abbrev TerminalOutputInput := (ProfileCheckData×ℕ)×(Option MatrixCode×ℕ)

def terminalOutputEntry (z : TerminalOutputInput) : Option MatrixCode×ℕ :=
  (z.2.1.bind (fun X => outerTrial (z.1,X)),z.2.2)

def terminalOutputEntryRealizer : Realizer terminalOutputEntry :=
  (pair (composition (pair first (composition second first))
    (optionCases (constant none) outerTrialRealizer)) (composition second second)).congr (by
      rintro ⟨p,⟨o,n⟩⟩
      cases o <;> rfl)

def terminalOutputs (z : TransitionCache) : List (Option MatrixCode×ℕ) :=
  z.2.2.map (fun entry => terminalOutputEntry (z.1.1,entry))

def terminalOutputsRealizer : Realizer terminalOutputs :=
  composition (pair (composition first first) (composition second second))
    (mapWith terminalOutputEntryRealizer)

def successfulWeight (z : MatrixCode×(Option MatrixCode×ℕ)) : ℕ :=
  z.2.1.elim 0 (fun X => if X=z.1 then z.2.2 else 0)

def successfulWeightRealizer : Realizer successfulWeight := by
  let input : Realizer (fun z : MatrixCode×(Option MatrixCode×ℕ) =>
      ((z.1,z.2.2),z.2.1)) := pair (pair first (composition second second))
    (composition second first)
  let test : Realizer (fun z : (MatrixCode×ℕ)×MatrixCode => decide (z.2=z.1.1)) :=
    composition (pair second (composition first first)) matrixEqual
  let result := choose test (composition first second) (constant 0)
  exact (composition input (optionCases (constant 0) result)).congr (by
    intro z
    simp only [Function.comp_apply,decide_eq_true_eq]
    rfl)

def successfulWeightSum (z : MatrixCode×List (Option MatrixCode×ℕ)) : ℕ :=
  (z.2.map (fun entry => successfulWeight (z.1,entry))).sum

def successfulWeightSumRealizer : Realizer successfulWeightSum :=
  composition (mapWith successfulWeightRealizer) listSum

def terminalCount (z : TransitionCache×MatrixCode) : ℕ :=
  z.1.2.1*successfulWeightSum (z.2,terminalOutputs z.1)

def terminalCountRealizer : Realizer terminalCount :=
  composition (pair (composition (composition first second) first)
    (composition (pair second (composition first terminalOutputsRealizer))
      successfulWeightSumRealizer)) multiply

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_TransitionCacheRuntime
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Work bounds for cached completion multiplicities -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

attribute [local irreducible] completionMultiplicityRealizer prepareTransitionCacheRealizer
  residualParametersRealizer canonicalBitCountRealizer completionWeightsRealizer
  residualParameters canonicalBitCount completionWeights

/-- The cache is charged by the finite completion box and the requested
reserved word length; no random-tape enumeration appears in this measure. -/
def transitionCacheMeasure (z : TransitionCacheParameters) : ℕ :=
  z.2+completionWeightMeasure (residualParameters z.1)+weight z

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileMatrixEntry
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable entries of the finite profile transition matrix -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

abbrev MatrixParameters := TransitionCacheParameters×List Bool
abbrev MatrixEntryInput := MatrixParameters×((List ℕ×List ℕ)×(List ℕ×List ℕ))

def matrixData (z : MatrixParameters) : ProfileCheckData := z.1.1.1.1

def matrixDataRealizer : Realizer matrixData :=
  composition (composition (composition first first) first) first

def sourceData (z : MatrixEntryInput) : ProfileCheckData :=
  candidateData (matrixData z.1,z.2.1)

def sourceDataRealizer : Realizer sourceData :=
  composition (pair (composition (f := fun z : MatrixEntryInput => z.1) (g := matrixData) first matrixDataRealizer) (composition second first))
    candidateDataRealizer

def targetData (z : MatrixEntryInput) : ProfileCheckData :=
  candidateData (matrixData z.1,z.2.2)

def targetDataRealizer : Realizer targetData :=
  composition (pair (composition (f := fun z : MatrixEntryInput => z.1) (g := matrixData) first matrixDataRealizer) (composition second second))
    candidateDataRealizer

def entryCacheParameters (z : MatrixEntryInput) : TransitionCacheParameters :=
  (((sourceData z,z.1.1.1.1.2),z.1.1.1.2),z.1.1.2)

def entryCacheParametersRealizer : Realizer entryCacheParameters := by
  let params : Realizer (fun z : MatrixEntryInput => z.1.1) := composition first first
  let resid : Realizer (fun z : MatrixEntryInput => z.1.1.1) := composition params first
  let padding := composition (composition resid first) second
  exact pair (pair (pair sourceDataRealizer padding) (composition resid second))
    (composition params second)

def entryQuery (z : MatrixEntryInput) : TransitionQuery :=
  ((prepareTransitionCache (entryCacheParameters z),z.2.2),z.1.2)

def entryQueryRealizer : Realizer entryQuery :=
  pair (pair
    (composition (f := entryCacheParameters) (g := prepareTransitionCache)
      entryCacheParametersRealizer prepareTransitionCacheRealizer)
    (composition second second)) (composition first second)

def validMatrixEntry (z : MatrixEntryInput) : ℕ := transitionCount (entryQuery z)

def validMatrixEntryRealizer : Realizer validMatrixEntry :=
  composition (f := entryQuery) (g := transitionCount) entryQueryRealizer transitionCountRealizer

/-- The denominator includes the proposal word and its padded completion word. -/
def matrixDenominator (z : MatrixParameters) : ℕ :=
  BinaryPowerPrograms.power (2,z.2.length+z.1.2)

def matrixDenominatorRealizer : Realizer matrixDenominator :=
  composition (pair (constant 2) (composition (pair
    (composition second listLength) (composition first second)) add)) BinaryPowerPrograms.powerRealizer

def diagonalMatrixEntry (z : MatrixEntryInput) : ℕ :=
  if z.2.1=z.2.2 then matrixDenominator z.1 else 0

def diagonalMatrixEntryRealizer : Realizer diagonalMatrixEntry :=
  (choose (composition second profileCodeEqual)
    (composition first matrixDenominatorRealizer) (constant 0)).congr (by
      intro z
      simp only [Function.comp_apply,decide_eq_true_eq]
      rfl)

/-- Invalid source vectors are stationary. Invalid target vectors have
zero weight from every valid source. -/
def matrixEntry (z : MatrixEntryInput) : ℕ :=
  if profileTest (sourceData z) then
    if profileTest (targetData z) then validMatrixEntry z else 0
  else diagonalMatrixEntry z

def matrixEntryRealizer : Realizer matrixEntry :=
  choose (composition sourceDataRealizer profileTestRealizer)
    (choose (composition targetDataRealizer profileTestRealizer)
      validMatrixEntryRealizer (constant 0)) diagonalMatrixEntryRealizer

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileMatrixEntryRuntime
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-box work bound for the executable transition entries -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

attribute [local irreducible] prepareTransitionCache prepareTransitionCacheRealizer
  entryCacheParameters entryCacheParametersRealizer transitionCount transitionCountRealizer
  entryQueryRealizer

def matrixEntryMeasure (z : MatrixEntryInput) : ℕ :=
  transitionCacheMeasure (entryCacheParameters z)+gridStateCount (z.1.2,2)+weight z

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileMatrixProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the finite transition matrix by deterministic enumeration -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

abbrev MatrixColumnInput := MatrixParameters×(List ℕ×List ℕ)
abbrev MatrixColumnEntryInput := MatrixColumnInput×(List ℕ×List ℕ)

def columnEntryInput (z : MatrixColumnEntryInput) : MatrixEntryInput :=
  (z.1.1,(z.2,z.1.2))

def columnEntryInputRealizer : Realizer columnEntryInput :=
  pair (composition first first) (pair second (composition first second))

def columnEntry (z : MatrixColumnEntryInput) : ℕ := matrixEntry (columnEntryInput z)

def columnEntryRealizer : Realizer columnEntry :=
  composition (f := columnEntryInput) (g := matrixEntry) columnEntryInputRealizer matrixEntryRealizer

def columnEntryMeasure (z : MatrixColumnEntryInput) : ℕ :=
  matrixEntryMeasure (columnEntryInput z)

def matrixColumn (z : MatrixColumnInput) : List ℕ :=
  (profileBoxViews (matrixData z.1)).map (fun source => columnEntry (z,source))

def matrixColumnRealizer : Realizer matrixColumn :=
  composition (f := fun z : MatrixColumnInput => (z,profileBoxViews (matrixData z.1)))
    (g := fun z : MatrixColumnInput×List (List ℕ×List ℕ) =>
      z.2.map (fun source => columnEntry (z.1,source)))
    (pair identity (composition
      (f := fun z : MatrixColumnInput => matrixData z.1) (g := profileBoxViews)
      (composition (f := fun z : MatrixColumnInput => z.1) (g := matrixData)
        first matrixDataRealizer) profileBoxViewsRealizer)) (mapWith columnEntryRealizer)

def matrixColumnMeasure (z : MatrixColumnInput) : ℕ :=
  gridStateCount (profileEnumerationData (matrixData z.1))+
    MeasuredMap.listMeasure columnEntryMeasure (z,profileBoxViews (matrixData z.1))

def profileMatrix (z : MatrixParameters) : List (List ℕ) :=
  (profileBoxViews (matrixData z)).map (fun target => matrixColumn (z,target))

def profileMatrixRealizer : Realizer profileMatrix :=
  composition (f := fun z : MatrixParameters => (z,profileBoxViews (matrixData z)))
    (g := fun z : MatrixParameters×List (List ℕ×List ℕ) =>
      z.2.map (fun target => matrixColumn (z.1,target)))
    (pair identity (composition (f := matrixData) (g := profileBoxViews)
      matrixDataRealizer profileBoxViewsRealizer)) (mapWith matrixColumnRealizer)

def profileMatrixMeasure (z : MatrixParameters) : ℕ :=
  gridStateCount (profileEnumerationData (matrixData z))+
    MeasuredMap.listMeasure matrixColumnMeasure (z,profileBoxViews (matrixData z))

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileMatrixSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed matrix is the actual profile transition law -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts CompletionTranslation
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2)≤b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "f" => 25*(d+b+h+1)^62

attribute [local irreducible] stateCode stateCodeData prepareTransitionCache transitionCount
  ProfilePrograms.matrixEntry validMatrixEntry listedStepCounts listedCompletionCounts

def matrixInput (x : PaperStates r c) (xs : List Bool) : MatrixParameters :=
  ((((stateCodeData r c e x,d^12),(d,h)),f),xs)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileTerminalProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing terminal success weights at every enumerated profile -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

abbrev TerminalEntryInput := MatrixParameters×((List ℕ×List ℕ)×MatrixCode)

def terminalSourceInput (z : TerminalEntryInput) : MatrixEntryInput :=
  (z.1,(z.2.1,z.2.1))

def terminalSourceInputRealizer : Realizer terminalSourceInput :=
  pair first (pair (composition second first) (composition second first))

def terminalEntryQuery (z : TerminalEntryInput) : TransitionCache×MatrixCode :=
  (prepareTransitionCache (entryCacheParameters (terminalSourceInput z)),z.2.2)

def terminalEntryQueryRealizer : Realizer terminalEntryQuery :=
  pair (composition (f := terminalSourceInput)
    (g := fun z => prepareTransitionCache (entryCacheParameters z)) terminalSourceInputRealizer
    (composition (f := entryCacheParameters) (g := prepareTransitionCache)
      entryCacheParametersRealizer prepareTransitionCacheRealizer)) (composition second second)

def terminalEntry (z : TerminalEntryInput) : ℕ := terminalCount (terminalEntryQuery z)

def terminalEntryRealizer : Realizer terminalEntry :=
  composition (f := terminalEntryQuery) (g := terminalCount) terminalEntryQueryRealizer terminalCountRealizer

def terminalEntryMeasure (z : TerminalEntryInput) : ℕ :=
  matrixEntryMeasure (terminalSourceInput z)+weight z

abbrev TerminalColumnInput := MatrixParameters×MatrixCode
abbrev TerminalColumnEntryInput := TerminalColumnInput×(List ℕ×List ℕ)

def terminalColumnEntryInput (z : TerminalColumnEntryInput) : TerminalEntryInput :=
  (z.1.1,(z.2,z.1.2))

def terminalColumnEntryInputRealizer : Realizer terminalColumnEntryInput :=
  pair (composition first first) (pair second (composition first second))

def terminalColumnEntry (z : TerminalColumnEntryInput) : ℕ := terminalEntry (terminalColumnEntryInput z)

def terminalColumnEntryRealizer : Realizer terminalColumnEntry :=
  composition (f := terminalColumnEntryInput) (g := terminalEntry)
    terminalColumnEntryInputRealizer terminalEntryRealizer

def terminalColumnEntryMeasure (z : TerminalColumnEntryInput) : ℕ :=
  terminalEntryMeasure (terminalColumnEntryInput z)+weight z

def terminalColumn (z : TerminalColumnInput) : List ℕ :=
  (profileBoxViews (matrixData z.1)).map (fun v => terminalColumnEntry (z,v))

def terminalColumnRealizer : Realizer terminalColumn :=
  composition (f := fun z : TerminalColumnInput => (z,profileBoxViews (matrixData z.1)))
    (g := fun z : TerminalColumnInput×List (List ℕ×List ℕ) =>
      z.2.map (fun v => terminalColumnEntry (z.1,v)))
    (pair identity (composition
      (f := fun z : TerminalColumnInput => matrixData z.1) (g := profileBoxViews)
      (composition (f := fun z : TerminalColumnInput => z.1) (g := matrixData)
        first matrixDataRealizer) profileBoxViewsRealizer)) (mapWith terminalColumnEntryRealizer)

def terminalColumnMeasure (z : TerminalColumnInput) : ℕ :=
  gridStateCount (profileEnumerationData (matrixData z.1))+
    MeasuredMap.listMeasure terminalColumnEntryMeasure (z,profileBoxViews (matrixData z.1))

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileTerminalSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact trial counts from matrix propagation and cached terminal weights -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
variable (hr : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn r)).length)
variable (hc : 0<(largeIndices ((dimensionAllowance (I := Fin m) (J := Fin n))^20,List.ofFn c)).length)
variable (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2)≤b)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "f" => 25*(d+b+h+1)^62

attribute [local irreducible] stateCode stateCodeData listedCompletionCounts listedWalkCounts
  listedTrialCounts prepareTransitionCache terminalCount matrixInput IntegerLaw.push

def terminalFibreCounts (x : PaperStates r c) : IntegerLaw (Option (Table r c)) (2^f) :=
  (listedCompletionCounts r c hr hc b h hb x).push (fun A => stateTrial r c ⟨x,A⟩)

attribute [local irreducible] terminalFibreCounts

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileTrialCountProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed walk-and-terminal integer trial counts -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

abbrev WalkCountInput := MatrixParameters×(ℕ×ℕ)

def walkCountData (z : WalkCountInput) : ℕ×(List (List ℕ)×ℕ) :=
  (z.2.1,(profileMatrix z.1,z.2.2))

def walkCountDataRealizer : Realizer walkCountData :=
  pair (composition second first)
    (pair (composition (f := fun z : WalkCountInput => z.1) (g := profileMatrix)
      first profileMatrixRealizer) (composition second second))

def walkCountMeasure (z : WalkCountInput) : ℕ :=
  z.2.1+profileMatrixMeasure z.1+weight z

def walkCounts (z : WalkCountInput) : List ℕ := IntegerMatrixPrograms.fromPoint (walkCountData z)

def walkCountsRealizer : Realizer walkCounts :=
  composition (f := walkCountData) (g := IntegerMatrixPrograms.fromPoint)
    walkCountDataRealizer IntegerMatrixPrograms.fromPointRealizer

abbrev TrialCountInput := WalkCountInput×MatrixCode

def trialCount (z : TrialCountInput) : ℕ :=
  IntegerMatrixPrograms.dot (walkCounts z.1,terminalColumn (z.1.1,z.2))

def trialCountRealizer : Realizer trialCount :=
  composition (pair (composition (f := fun z : TrialCountInput => z.1) (g := walkCounts)
      first walkCountsRealizer)
    (composition (f := fun z : TrialCountInput => (z.1.1,z.2)) (g := terminalColumn)
      (pair (composition first first) second) terminalColumnRealizer)) IntegerMatrixPrograms.dotRealizer

def trialCountMeasure (z : TrialCountInput) : ℕ :=
  walkCountMeasure z.1+terminalColumnMeasure (z.1.1,z.2)+weight z

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalTrialVector
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing trial counts on every original-table candidate -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

abbrev OptionalTrialInput := WalkCountInput×Option MatrixCode

def optionalTrialInput (z : OptionalTrialInput) : TrialCountInput := (z.1,z.2.getD [])

def optionalTrialInputRealizer : Realizer optionalTrialInput :=
  pair first (composition (pair (constant ([] : MatrixCode)) second) FirstSuccessProgram.defaultRealizer)

def optionalTrialCount (z : OptionalTrialInput) : ℕ :=
  if z.2.isSome then trialCount (optionalTrialInput z) else 0

def optionalTrialCountRealizer : Realizer optionalTrialCount :=
  choose (composition second FirstSuccessProgram.isSomeRealizer)
    (composition (f := optionalTrialInput) (g := trialCount)
      optionalTrialInputRealizer trialCountRealizer) (constant 0)

def optionalTrialMeasure (z : OptionalTrialInput) : ℕ :=
  trialCountMeasure (optionalTrialInput z)+weight z

abbrev TrialVectorInput := WalkCountInput×CompletionMargins

def trialVector (z : TrialVectorInput) : List ℕ :=
  (originalCandidates z.2).map (fun o => optionalTrialCount (z.1,o))

def trialVectorRealizer : Realizer trialVector :=
  composition (f := fun z : TrialVectorInput => (z.1,originalCandidates z.2))
    (g := fun z : WalkCountInput×List (Option MatrixCode) =>
      z.2.map (fun o => optionalTrialCount (z.1,o)))
    (pair first (composition second originalCandidatesRealizer))
    (mapWith optionalTrialCountRealizer)

def trialVectorMeasure (z : TrialVectorInput) : ℕ :=
  originalEnumerationMeasure z.2+
    MeasuredMap.listMeasure optionalTrialMeasure (z.1,originalCandidates z.2)+weight z

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalOuterVector
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computed first-success counts over the original-table box -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

/-- Walk data and margins; trial markers, denominator, and fallback matrix. -/
abbrev OuterVectorInput := TrialVectorInput×((List Bool×ℕ)×MatrixCode)

def outerVectorInput (z : OuterVectorInput) : VectorRetryPrograms.Input :=
  (z.2.1,(trialVector z.1,originalIndex (z.1.2,z.2.2)))

def outerVectorInputRealizer : Realizer outerVectorInput :=
  pair (composition second first)
    (pair (composition (f := fun z : OuterVectorInput => z.1) (g := trialVector)
      first trialVectorRealizer)
      (composition (f := fun z : OuterVectorInput => (z.1.2,z.2.2)) (g := originalIndex)
        (pair (composition first second) (composition second second)) originalIndexRealizer))

def outerVectorMeasure (z : OuterVectorInput) : ℕ := trialVectorMeasure z.1+weight z

attribute [local irreducible] outerVectorInput

def outerVector (z : OuterVectorInput) : List ℕ := VectorRetryPrograms.counts (outerVectorInput z)

def outerVectorRealizer : Realizer outerVector :=
  composition (f := outerVectorInput) (g := VectorRetryPrograms.counts)
    outerVectorInputRealizer VectorRetryPrograms.countsRealizer

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitMatrixEntry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer transition entries for the all-small walk -/

namespace ContingencyTables.UnitCountPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms Polynomial

abbrev WordInput := MatrixEntryInput×List Bool

def wordViews (z : WordInput) : List ℕ×List ℕ :=
  (codeNeighborProposal (sourceData z.1,z.2)).getD z.1.2.1

def wordViewsRealizer : Realizer wordViews :=
  composition (pair (composition (composition first second) first)
    (composition (pair (composition first sourceDataRealizer) second) codeNeighborProposalRealizer))
    FirstSuccessProgram.defaultRealizer

def wordCount (z : WordInput) : ℕ := if wordViews z=z.1.2.2 then 1 else 0

def wordCountRealizer : Realizer wordCount :=
  (choose (composition (pair wordViewsRealizer
    (composition (composition first second) second)) profileCodeEqual)
    (constant 1) (constant 0)).congr (by
      intro z
      simp only [Function.comp_apply,decide_eq_true_eq]
      rfl)

def validEntry (z : MatrixEntryInput) : ℕ :=
  ((booleanWords z.1.2).map (fun w => wordCount (z,w))).sum

def entryWords (z : MatrixEntryInput) : MatrixEntryInput×List (List Bool) :=
  (z,booleanWords z.1.2)

def entryWordsRealizer : Realizer entryWords :=
  pair identity (composition (f := fun z : MatrixEntryInput => z.1.2)
    (g := booleanWords) (composition first second) booleanWordsRealizer)

def wordSum (z : MatrixEntryInput×List (List Bool)) : ℕ :=
  (z.2.map (fun w => wordCount (z.1,w))).sum

def wordSumRealizer : Realizer wordSum := composition (mapWith wordCountRealizer) listSum

def validEntryRealizer : Realizer validEntry :=
  composition (f := entryWords) (g := wordSum) entryWordsRealizer wordSumRealizer

attribute [local irreducible] wordCount wordViews wordCountRealizer wordViewsRealizer

def entryMeasure (z : MatrixEntryInput) : ℕ := gridStateCount (z.1.2,2)+weight z

def denominator (z : MatrixParameters) : ℕ := BinaryPowerPrograms.power (2,z.2.length)

def denominatorRealizer : Realizer denominator :=
  composition (pair (constant 2) (composition second listLength)) BinaryPowerPrograms.powerRealizer

def diagonalEntry (z : MatrixEntryInput) : ℕ :=
  if z.2.1=z.2.2 then denominator z.1 else 0

def diagonalEntryRealizer : Realizer diagonalEntry :=
  (choose (composition second profileCodeEqual) (composition first denominatorRealizer)
    (constant 0)).congr (by intro z; simp only [Function.comp_apply,decide_eq_true_eq]; rfl)

def matrixEntry (z : MatrixEntryInput) : ℕ :=
  if profileTest (sourceData z) then validEntry z else diagonalEntry z

def matrixEntryRealizer : Realizer matrixEntry :=
  choose (composition sourceDataRealizer profileTestRealizer) validEntryRealizer diagonalEntryRealizer

end ContingencyTables.UnitCountPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitMatrixProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the finite transition matrix by deterministic enumeration -/

namespace ContingencyTables.UnitCountPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms Polynomial

abbrev MatrixColumnInput := MatrixParameters×(List ℕ×List ℕ)
abbrev MatrixColumnEntryInput := MatrixColumnInput×(List ℕ×List ℕ)

def columnEntryInput (z : MatrixColumnEntryInput) : MatrixEntryInput :=
  (z.1.1,(z.2,z.1.2))

def columnEntryInputRealizer : Realizer columnEntryInput :=
  pair (composition first first) (pair second (composition first second))

def columnEntry (z : MatrixColumnEntryInput) : ℕ := matrixEntry (columnEntryInput z)

def columnEntryRealizer : Realizer columnEntry :=
  composition (f := columnEntryInput) (g := matrixEntry) columnEntryInputRealizer matrixEntryRealizer

def columnEntryMeasure (z : MatrixColumnEntryInput) : ℕ :=
  entryMeasure (columnEntryInput z)

def matrixColumn (z : MatrixColumnInput) : List ℕ :=
  (profileBoxViews (matrixData z.1)).map (fun source => columnEntry (z,source))

def matrixColumnRealizer : Realizer matrixColumn :=
  composition (f := fun z : MatrixColumnInput => (z,profileBoxViews (matrixData z.1)))
    (g := fun z : MatrixColumnInput×List (List ℕ×List ℕ) =>
      z.2.map (fun source => columnEntry (z.1,source)))
    (pair identity (composition
      (f := fun z : MatrixColumnInput => matrixData z.1) (g := profileBoxViews)
      (composition (f := fun z : MatrixColumnInput => z.1) (g := matrixData)
        first matrixDataRealizer) profileBoxViewsRealizer)) (mapWith columnEntryRealizer)

def matrixColumnMeasure (z : MatrixColumnInput) : ℕ :=
  gridStateCount (profileEnumerationData (matrixData z.1))+
    MeasuredMap.listMeasure columnEntryMeasure (z,profileBoxViews (matrixData z.1))

def profileMatrix (z : MatrixParameters) : List (List ℕ) :=
  (profileBoxViews (matrixData z)).map (fun target => matrixColumn (z,target))

def profileMatrixRealizer : Realizer profileMatrix :=
  composition (f := fun z : MatrixParameters => (z,profileBoxViews (matrixData z)))
    (g := fun z : MatrixParameters×List (List ℕ×List ℕ) =>
      z.2.map (fun target => matrixColumn (z.1,target)))
    (pair identity (composition (f := matrixData) (g := profileBoxViews)
      matrixDataRealizer profileBoxViewsRealizer)) (mapWith matrixColumnRealizer)

def profileMatrixMeasure (z : MatrixParameters) : ℕ :=
  gridStateCount (profileEnumerationData (matrixData z))+
    MeasuredMap.listMeasure matrixColumnMeasure (z,profileBoxViews (matrixData z))

end ContingencyTables.UnitCountPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitTerminalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deterministic terminal weights for the all-small branch -/

namespace ContingencyTables.UnitCountPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms Polynomial

def terminalData (z : TerminalEntryInput) : (ProfileCheckData×ℕ)×MatrixCode :=
  ((sourceData (terminalSourceInput z),z.1.1.1.1.2),[])

def terminalDataRealizer : Realizer terminalData :=
  pair (pair (composition (f := terminalSourceInput) (g := sourceData)
    terminalSourceInputRealizer sourceDataRealizer)
    (composition (composition (composition (composition first first) first) first) second))
    (constant [])

def terminalEntry (z : TerminalEntryInput) : ℕ :=
  successfulWeight (z.2.2,(outerTrial (terminalData z),1))

def terminalEntryRealizer : Realizer terminalEntry :=
  composition (pair (composition second second)
    (pair (composition (f := terminalData) (g := outerTrial)
      terminalDataRealizer outerTrialRealizer) (constant 1))) successfulWeightRealizer

def terminalEntryMeasure (z : TerminalEntryInput) : ℕ := weight z

abbrev TerminalColumnInput := MatrixParameters×MatrixCode
abbrev TerminalColumnEntryInput := TerminalColumnInput×(List ℕ×List ℕ)

def terminalColumnEntryInput (z : TerminalColumnEntryInput) : TerminalEntryInput :=
  (z.1.1,(z.2,z.1.2))

def terminalColumnEntryInputRealizer : Realizer terminalColumnEntryInput :=
  pair (composition first first) (pair second (composition first second))

def terminalColumnEntry (z : TerminalColumnEntryInput) : ℕ := terminalEntry (terminalColumnEntryInput z)

def terminalColumnEntryRealizer : Realizer terminalColumnEntry :=
  composition (f := terminalColumnEntryInput) (g := terminalEntry)
    terminalColumnEntryInputRealizer terminalEntryRealizer

def terminalColumnEntryMeasure (z : TerminalColumnEntryInput) : ℕ :=
  terminalEntryMeasure (terminalColumnEntryInput z)+weight z

def terminalColumn (z : TerminalColumnInput) : List ℕ :=
  (profileBoxViews (matrixData z.1)).map (fun v => terminalColumnEntry (z,v))

def terminalColumnRealizer : Realizer terminalColumn :=
  composition (f := fun z : TerminalColumnInput => (z,profileBoxViews (matrixData z.1)))
    (g := fun z : TerminalColumnInput×List (List ℕ×List ℕ) =>
      z.2.map (fun v => terminalColumnEntry (z.1,v)))
    (pair identity (composition
      (f := fun z : TerminalColumnInput => matrixData z.1) (g := profileBoxViews)
      (composition (f := fun z : TerminalColumnInput => z.1) (g := matrixData)
        first matrixDataRealizer) profileBoxViewsRealizer)) (mapWith terminalColumnEntryRealizer)

def terminalColumnMeasure (z : TerminalColumnInput) : ℕ :=
  gridStateCount (profileEnumerationData (matrixData z.1))+
    MeasuredMap.listMeasure terminalColumnEntryMeasure (z,profileBoxViews (matrixData z.1))

end ContingencyTables.UnitCountPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitTrialCountProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed walk-and-terminal integer trial counts -/

namespace ContingencyTables.UnitCountPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms Polynomial

abbrev WalkCountInput := MatrixParameters×(ℕ×ℕ)

def walkCountData (z : WalkCountInput) : ℕ×(List (List ℕ)×ℕ) :=
  (z.2.1,(profileMatrix z.1,z.2.2))

def walkCountDataRealizer : Realizer walkCountData :=
  pair (composition second first)
    (pair (composition (f := fun z : WalkCountInput => z.1) (g := profileMatrix)
      first profileMatrixRealizer) (composition second second))

def walkCountMeasure (z : WalkCountInput) : ℕ :=
  z.2.1+profileMatrixMeasure z.1+weight z

def walkCounts (z : WalkCountInput) : List ℕ := IntegerMatrixPrograms.fromPoint (walkCountData z)

def walkCountsRealizer : Realizer walkCounts :=
  composition (f := walkCountData) (g := IntegerMatrixPrograms.fromPoint)
    walkCountDataRealizer IntegerMatrixPrograms.fromPointRealizer

abbrev TrialCountInput := WalkCountInput×MatrixCode

def trialCount (z : TrialCountInput) : ℕ :=
  IntegerMatrixPrograms.dot (walkCounts z.1,terminalColumn (z.1.1,z.2))

def trialCountRealizer : Realizer trialCount :=
  composition (pair (composition (f := fun z : TrialCountInput => z.1) (g := walkCounts)
      first walkCountsRealizer)
    (composition (f := fun z : TrialCountInput => (z.1.1,z.2)) (g := terminalColumn)
      (pair (composition first first) second) terminalColumnRealizer)) IntegerMatrixPrograms.dotRealizer

def trialCountMeasure (z : TrialCountInput) : ℕ :=
  walkCountMeasure z.1+terminalColumnMeasure (z.1.1,z.2)+weight z

end ContingencyTables.UnitCountPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitOriginalVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing trial counts on every original-table candidate -/

namespace ContingencyTables.UnitCountPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms Polynomial

abbrev OptionalTrialInput := WalkCountInput×Option MatrixCode

def optionalTrialInput (z : OptionalTrialInput) : TrialCountInput := (z.1,z.2.getD [])

def optionalTrialInputRealizer : Realizer optionalTrialInput :=
  pair first (composition (pair (constant ([] : MatrixCode)) second) FirstSuccessProgram.defaultRealizer)

def optionalTrialCount (z : OptionalTrialInput) : ℕ :=
  if z.2.isSome then trialCount (optionalTrialInput z) else 0

def optionalTrialCountRealizer : Realizer optionalTrialCount :=
  choose (composition second FirstSuccessProgram.isSomeRealizer)
    (composition (f := optionalTrialInput) (g := trialCount)
      optionalTrialInputRealizer trialCountRealizer) (constant 0)

def optionalTrialMeasure (z : OptionalTrialInput) : ℕ :=
  trialCountMeasure (optionalTrialInput z)+weight z

abbrev TrialVectorInput := WalkCountInput×CompletionMargins

def trialVector (z : TrialVectorInput) : List ℕ :=
  (originalCandidates z.2).map (fun o => optionalTrialCount (z.1,o))

def trialVectorRealizer : Realizer trialVector :=
  composition (f := fun z : TrialVectorInput => (z.1,originalCandidates z.2))
    (g := fun z : WalkCountInput×List (Option MatrixCode) =>
      z.2.map (fun o => optionalTrialCount (z.1,o)))
    (pair first (composition second originalCandidatesRealizer))
    (mapWith optionalTrialCountRealizer)

def trialVectorMeasure (z : TrialVectorInput) : ℕ :=
  originalEnumerationMeasure z.2+
    MeasuredMap.listMeasure optionalTrialMeasure (z.1,originalCandidates z.2)+weight z

end ContingencyTables.UnitCountPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitOuterVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computed first-success counts over the original-table box -/

namespace ContingencyTables.UnitCountPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms Polynomial

/-- Walk data and margins; trial markers, denominator, and fallback matrix. -/
abbrev OuterVectorInput := TrialVectorInput×((List Bool×ℕ)×MatrixCode)

def outerVectorInput (z : OuterVectorInput) : VectorRetryPrograms.Input :=
  (z.2.1,(trialVector z.1,originalIndex (z.1.2,z.2.2)))

def outerVectorInputRealizer : Realizer outerVectorInput :=
  pair (composition second first)
    (pair (composition (f := fun z : OuterVectorInput => z.1) (g := trialVector)
      first trialVectorRealizer)
      (composition (f := fun z : OuterVectorInput => (z.1.2,z.2.2)) (g := originalIndex)
        (pair (composition first second) (composition second second)) originalIndexRealizer))

def outerVectorMeasure (z : OuterVectorInput) : ℕ := trialVectorMeasure z.1+weight z

attribute [local irreducible] outerVectorInput

def outerVector (z : OuterVectorInput) : List ℕ := VectorRetryPrograms.counts (outerVectorInput z)

def outerVectorRealizer : Realizer outerVector :=
  composition (f := outerVectorInput) (g := VectorRetryPrograms.counts)
    outerVectorInputRealizer VectorRetryPrograms.countsRealizer

end ContingencyTables.UnitCountPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ScheduledCountInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Supplying the finite count evaluator from the public sampling parameters -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

attribute [local irreducible] initialCheck marginPadding parameterDimension parameterAccuracy
  parameterCompletionWidth parameterSteps parameterProposalWidth hasLargeRectangle parameterTrials
  profileBoxIndex outerVector UnitCountPrograms.outerVector

/-- The same cache parameters used by the executed approximate sampler. -/
def scheduledCacheParameters (z : SamplingParameters) : TransitionCacheParameters :=
  (((initialCheck z.1,marginPadding z.1),(parameterDimension z,parameterAccuracy z)),
    parameterCompletionWidth z)

def scheduledCacheParametersRealizer : Realizer scheduledCacheParameters :=
  pair (pair (pair (composition (f := fun z : SamplingParameters => z.1) (g := initialCheck) first initialCheckRealizer)
    (composition (f := fun z : SamplingParameters => z.1) (g := marginPadding) first marginPaddingRealizer))
    (pair parameterDimensionRealizer parameterAccuracyRealizer)) parameterCompletionWidthRealizer

def scheduledDenseWidth (z : SamplingParameters) : ℕ :=
  parameterSteps z*(parameterProposalWidth z+parameterCompletionWidth z)+parameterCompletionWidth z

def scheduledDenseWidthRealizer : Realizer scheduledDenseWidth :=
  composition (f := fun z : SamplingParameters =>
    (parameterSteps z*(parameterProposalWidth z+parameterCompletionWidth z),parameterCompletionWidth z))
    (g := fun p : ℕ×ℕ => p.1+p.2)
    (pair (composition (f := fun z : SamplingParameters =>
      (parameterSteps z,parameterProposalWidth z+parameterCompletionWidth z))
      (g := fun p : ℕ×ℕ => p.1*p.2)
      (pair parameterStepsRealizer (composition
        (f := fun z : SamplingParameters => (parameterProposalWidth z,parameterCompletionWidth z))
        (g := fun p : ℕ×ℕ => p.1+p.2)
        (pair parameterProposalWidthRealizer parameterCompletionWidthRealizer) add)) multiply)
      parameterCompletionWidthRealizer) add

def scheduledUnitWidth (z : SamplingParameters) : ℕ := parameterSteps z*parameterProposalWidth z

def scheduledUnitWidthRealizer : Realizer scheduledUnitWidth :=
  composition (f := fun z : SamplingParameters => (parameterSteps z,parameterProposalWidth z))
    (g := fun p : ℕ×ℕ => p.1*p.2) (pair parameterStepsRealizer parameterProposalWidthRealizer) multiply

attribute [local irreducible] scheduledDenseWidth scheduledUnitWidth

/-- The all-small branch uses only the proposal bits of each walk. -/
def scheduledTrialWidth (z : SamplingParameters) : ℕ :=
  if hasLargeRectangle z then scheduledDenseWidth z else scheduledUnitWidth z

def scheduledTrialWidthRealizer : Realizer scheduledTrialWidth :=
  choose hasLargeRectangleRealizer scheduledDenseWidthRealizer scheduledUnitWidthRealizer

attribute [local irreducible] scheduledTrialWidth

/-- Numeric loop lengths are charged explicitly, in addition to binary input size. -/
def scheduledCountInputMeasure (z : SamplingParameters) : ℕ :=
  parameterSteps z+parameterTrials z+parameterProposalWidth z+scheduledTrialWidth z+weight z

def scheduledMatrixParameters (z : SamplingParameters) : MatrixParameters :=
  (scheduledCacheParameters z,unaryMarkers (parameterProposalWidth z))

def scheduledMatrixParametersRealizer : Realizer scheduledMatrixParameters :=
  pair scheduledCacheParametersRealizer
    (composition (f := parameterProposalWidth) (g := unaryMarkers)
      parameterProposalWidthRealizer unaryMarkersRealizer)

attribute [local irreducible] scheduledMatrixParameters

def scheduledStartIndex (z : SamplingParameters) : ℕ := profileBoxIndex (initialCheck z.1)

def scheduledStartIndexRealizer : Realizer scheduledStartIndex :=
  composition (composition (f := fun z : SamplingParameters => z.1) (g := initialCheck) first initialCheckRealizer) profileBoxIndexRealizer

def scheduledWalkInput (z : SamplingParameters) : WalkCountInput :=
  (scheduledMatrixParameters z,(parameterSteps z,scheduledStartIndex z))

def scheduledWalkInputRealizer : Realizer scheduledWalkInput :=
  pair scheduledMatrixParametersRealizer (pair parameterStepsRealizer scheduledStartIndexRealizer)

attribute [local irreducible] scheduledWalkInput

def scheduledTrialInput (z : SamplingParameters) : TrialVectorInput := (scheduledWalkInput z,z.1)

def scheduledTrialInputRealizer : Realizer scheduledTrialInput := pair scheduledWalkInputRealizer first

attribute [local irreducible] scheduledTrialInput

def scheduledTrialDenominator (z : SamplingParameters) : ℕ :=
  BinaryPowerPrograms.power (2,scheduledTrialWidth z)

def scheduledTrialDenominatorRealizer : Realizer scheduledTrialDenominator :=
  composition (f := fun z : SamplingParameters => (2,scheduledTrialWidth z))
    (g := BinaryPowerPrograms.power)
    (pair (constant 2) scheduledTrialWidthRealizer) BinaryPowerPrograms.powerRealizer

attribute [local irreducible] scheduledTrialDenominator

def scheduledOuterInput (z : SamplingParameters) : OuterVectorInput :=
  (scheduledTrialInput z,((unaryMarkers (parameterTrials z),scheduledTrialDenominator z),
    GreedyFeasibleTable.listMatrix z.1.1 z.1.2))

def scheduledOuterInputRealizer : Realizer scheduledOuterInput :=
  pair scheduledTrialInputRealizer
    (pair (pair (composition (f := parameterTrials) (g := unaryMarkers)
      parameterTrialsRealizer unaryMarkersRealizer) scheduledTrialDenominatorRealizer)
      (composition (f := fun z : SamplingParameters => z.1)
        (g := fun p => GreedyFeasibleTable.listMatrix p.1 p.2) first GreedyFeasibleTable.tableRealizer))

attribute [local irreducible] scheduledOuterInput

/-- All first-success numerators, computed from the public binary margins. -/
def scheduledCounts (z : SamplingParameters) : List ℕ :=
  if hasLargeRectangle z then outerVector (scheduledOuterInput z)
  else UnitCountPrograms.outerVector (scheduledOuterInput z)

def scheduledCountsRealizer : Realizer scheduledCounts :=
  choose hasLargeRectangleRealizer
    (composition (f := scheduledOuterInput) (g := outerVector)
      scheduledOuterInputRealizer outerVectorRealizer)
    (composition (f := scheduledOuterInput) (g := UnitCountPrograms.outerVector)
      scheduledOuterInputRealizer UnitCountPrograms.outerVectorRealizer)

attribute [local irreducible] scheduledCounts

def scheduledCountsMeasure (z : SamplingParameters) : ℕ := scheduledCountInputMeasure z+
  outerVectorMeasure (scheduledOuterInput z)+UnitCountPrograms.outerVectorMeasure (scheduledOuterInput z)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ScheduledResidualProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing residual weights from margins, precision, and branch denominator -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

attribute [local irreducible] scheduledCounts residualVector originalCandidates originalCardinality

def scheduledResidualCache (z : SamplingParameters×ℕ) : ScheduledResidualCache :=
  (scheduledCounts z.1,(z.1.1,z.2))

def scheduledResidualCacheRealizer : Realizer scheduledResidualCache :=
  pair (composition (f := fun z : SamplingParameters×ℕ => z.1) (g := scheduledCounts)
    first scheduledCountsRealizer) (pair (composition first first) second)

def scheduledResidualMeasure (z : SamplingParameters×ℕ) : ℕ :=
  scheduledCountsMeasure z.1+originalEnumerationMeasure z.1.1+weight z

def cachedResidualInput (z : ScheduledResidualCache) : ResidualVectorCache :=
  ((originalCandidates z.2.1,z.1),((z.1.sum,z.2.2),originalCardinality z.2.1))

def cachedResidualInputRealizer : Realizer cachedResidualInput :=
  pair (pair (composition (f := fun z : ScheduledResidualCache => z.2.1) (g := originalCandidates)
    (composition second first) originalCandidatesRealizer) first)
    (pair (pair (composition first listSum) (composition second second))
      (composition (f := fun z : ScheduledResidualCache => z.2.1) (g := originalCardinality)
        (composition second first) originalCardinalityRealizer))

def cachedResidualMeasure (z : ScheduledResidualCache) : ℕ :=
  originalEnumerationMeasure z.2.1+weight z

def cachedResidualCounts (z : ScheduledResidualCache) : List ℕ :=
  residualVector (cachedResidualInput z)

def cachedResidualCountsRealizer : Realizer cachedResidualCounts :=
  composition (f := cachedResidualInput) (g := residualVector)
    cachedResidualInputRealizer residualVectorRealizer

attribute [local irreducible] scheduledResidualCache cachedResidualCounts

/-- This computes the complete correction vector; it asks for no probability oracle. -/
def scheduledResidualCounts (z : SamplingParameters×ℕ) : List ℕ :=
  cachedResidualCounts (scheduledResidualCache z)

def scheduledResidualCountsRealizer : Realizer scheduledResidualCounts :=
  composition (f := scheduledResidualCache) (g := cachedResidualCounts)
    scheduledResidualCacheRealizer cachedResidualCountsRealizer

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_AllSamplingMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded public sampler on every margin pair -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

noncomputable def allSamplingMachine : RandomMachine :=
  FiniteWordExecution.machine publicWordCountRealizer publicSamplingAllRealizer
noncomputable def allSamplingMachineTime (as : List MatchingFPRAS.Symbol) : ℕ :=
  FiniteWordExecution.machineTime publicWordCountRealizer publicSamplingAllRealizer as

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactSamplingParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the exact sampler's precision from its margin-only input -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

attribute [local irreducible] marginDimension marginBinaryLength parameterWordCount

def sixthPower : Realizer (fun n : ℕ => n^6) :=
  (composition (f := fun n : ℕ => n^3) (g := fun n : ℕ => n^2)
    cubicPower squarePower).congr (by intro n; simp only [Function.comp_apply,←pow_mul])

def exactPrecisionRealizer : Realizer exactPrecision :=
  composition (f := fun z : CompletionMargins => ((marginDimension z)^6,(marginBinaryLength z)^2))
    (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (composition (f := marginDimension) (g := fun n : ℕ => n^6) marginDimensionRealizer sixthPower)
      (composition (f := marginBinaryLength) (g := fun n : ℕ => n^2) marginBinaryLengthRealizer squarePower))
    multiply

attribute [local irreducible] exactPrecision

def exactSamplingParameters (z : CompletionMargins) : SamplingParameters := (z,2*exactPrecision z)

def exactSamplingParametersRealizer : Realizer exactSamplingParameters :=
  pair identity (composition (f := fun z : CompletionMargins => (2,exactPrecision z))
    (g := fun p : ℕ×ℕ => p.1*p.2) (pair (constant 2) exactPrecisionRealizer) multiply)

def exactBranchDenominator (z : CompletionMargins) : ℕ := BinaryPowerPrograms.power (2,exactPrecision z)

def exactBranchDenominatorRealizer : Realizer exactBranchDenominator :=
  composition (f := fun z : CompletionMargins => (2,exactPrecision z)) (g := BinaryPowerPrograms.power)
    (pair (constant 2) exactPrecisionRealizer) BinaryPowerPrograms.powerRealizer

def exactParameterMeasure (z : CompletionMargins) : ℕ := exactPrecision z+weight z

def exactResidualInput (z : CompletionMargins) : SamplingParameters×ℕ :=
  (exactSamplingParameters z,exactBranchDenominator z)

def exactResidualInputRealizer : Realizer exactResidualInput :=
  pair exactSamplingParametersRealizer exactBranchDenominatorRealizer

/-- The ordinary branch needs precisely the existing public sampler's word. -/
def exactOrdinaryBits (z : CompletionMargins) : ℕ := parameterWordCount (exactSamplingParameters z)

def exactOrdinaryBitsRealizer : Realizer exactOrdinaryBits :=
  composition (f := exactSamplingParameters) (g := parameterWordCount)
    exactSamplingParametersRealizer parameterWordCountRealizer

def exactParsedMargins (as : List Symbol) : CompletionMargins := (parsedSampling as).1

def exactParsedMarginsRealizer : Realizer exactParsedMargins :=
  composition (f := parsedSampling) (g := fun p : SamplingParameters => p.1) parsedSamplingRealizer first

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactResidualInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the complete input to the exact matrix rejection loop -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

attribute [local irreducible] exactResidualInput scheduledResidualCounts originalCandidates

def exactRareMeasure (z : CompletionMargins) : ℕ :=
  exactParameterMeasure z+scheduledResidualMeasure (exactResidualInput z)+
    originalEnumerationMeasure z+weight z

def exactRareWeights (z : CompletionMargins) : List ℕ :=
  scheduledResidualCounts (exactResidualInput z)

def exactRareWeightsRealizer : Realizer exactRareWeights :=
  composition (f := exactResidualInput) (g := scheduledResidualCounts)
    exactResidualInputRealizer scheduledResidualCountsRealizer

attribute [local irreducible] exactRareWeights

def exactMatrixInput (z : CompletionMargins) : ExactMatrixTrial.Input :=
  ((originalCandidates z,GreedyFeasibleTable.listMatrix z.1 z.2),exactRareWeights z)

def exactMatrixInputRealizer : Realizer exactMatrixInput :=
  pair (pair originalCandidatesRealizer GreedyFeasibleTable.tableRealizer) exactRareWeightsRealizer

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactCorrectionPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed correction prefixes converge to the exact residual law -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.PhysicalStream

def correctionPrefix (z : DensePrograms.CompletionMargins) (N : ℕ) :
    Experiment (Option DensePrograms.MatrixCode) :=
  OnlineIntegerRetry.prefixExperiment (f := ExactMatrixTrial.trial) (exactMatrixInput z) N

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactBranchChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact dyadic gate that selects the rare correction branch -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream DensePrograms Polynomial

/-- All zero bits select correction; every other word selects the ordinary draw. -/
def rareWord (z : CompletionMargins×List Bool) : Bool := decide (StackAddition.value z.2=0)

def rareWordRealizer : Realizer rareWord :=
  composition (f := fun z : CompletionMargins×List Bool => (StackAddition.value z.2,0))
    (g := fun p : ℕ×ℕ => decide (p.1=p.2))
    (pair (composition second bitValue) (constant 0)) natEqual

def rareBranch (z : CompletionMargins) : Experiment Bool :=
  FiniteWordExecution.experiment exactPrecision rareWord z

noncomputable def rareBranchRealizer : OnlineTree.Realizer rareBranch :=
  FiniteWordExecution.realizer exactPrecisionRealizer rareWordRealizer

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactOrdinaryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite ordinary branch of the exact sampler -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream DensePrograms Polynomial

def exactOrdinaryWord (z : CompletionMargins×List Bool) : MatrixCode :=
  samplingMatrixAll (exactSamplingParameters z.1,z.2)

def exactOrdinaryWordRealizer : Realizer exactOrdinaryWord :=
  composition (f := fun z : CompletionMargins×List Bool => (exactSamplingParameters z.1,z.2))
    (g := samplingMatrixAll)
    (pair (composition (f := Prod.fst) (g := exactSamplingParameters)
      first exactSamplingParametersRealizer) second) samplingMatrixAllRealizer

def exactOrdinary (z : CompletionMargins) : Experiment MatrixCode :=
  FiniteWordExecution.experiment exactOrdinaryBits exactOrdinaryWord z

noncomputable def exactOrdinaryRealizer : OnlineTree.Realizer exactOrdinary :=
  FiniteWordExecution.realizer exactOrdinaryBitsRealizer exactOrdinaryWordRealizer

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactCoreProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One finite control graph for the ordinary and unbounded correction branches -/

namespace ContingencyTables.ExactCoreProgram
open MatchingFPRAS MatchingFPRAS.TreeData MatchingFPRAS.TreeFunction
open MatchingFPRAS.TreeMachine (Env K encodeEnv)
open MatchingFPRAS.PhysicalStream MatchingFPRAS.OnlineStack
open ProfilePrograms DensePrograms

noncomputable def instructions : Phase → OnlineControl.Instr Reg Phase
  | .prepare => .call (OnlineProc.deterministic OnlineIntegerRetry.prepareProc) .gate
  | .gate => .call rareBranchRealizer.program .choose
  | .choose => .branch 0 .ordinaryInput .rareInput
  | .ordinaryInput => .call (OnlineProc.deterministic (split 0 2 (by decide))) .ordinary
  | .ordinary => .call exactOrdinaryRealizer.program .halt
  | .rareInput => .call (OnlineProc.deterministic (split 0 2 (by decide))) .prepareRare
  | .prepareRare => .call (OnlineProc.deterministic exactMatrixInputRealizer.program) .retry
  | .retry => .call (OnlineIntegerRetry.program ExactMatrixTrial.trialRealizer) .halt
  | .halt => .halt

noncomputable def program : OnlineProc.Proc (K Reg) := OnlineControl.compile instructions

noncomputable def output (z : CompletionMargins) (s : Data) :
    Option MatrixCode → OnlinePartialCall.Config instructions
  | none => OnlinePartialCall.callCfg instructions .retry
      (OnlineControl.cfg (OnlineIntegerRetry.instructions ExactMatrixTrial.trialRealizer)
        (some .prepare) (env (TreeTyped.encode (exactMatrixInput z)) .nil s))
  | some X => OnlineControl.cfg instructions none (env (TreeTyped.encode X) .nil s)

def prefixExperiment (z : CompletionMargins) (N : ℕ) : Experiment (Option MatrixCode) :=
  (rareBranch z).bind (fun rare => if rare then correctionPrefix z N else (exactOrdinary z).map some)

end ContingencyTables.ExactCoreProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactPrintCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform printing cost for every feasible exact-sampling output -/

namespace ContingencyTables.ExactPrintCost
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream
open DensePrograms SmallGraphProfiles Polynomial
open scoped BigOperators Classical
noncomputable section

def matrixSize {m n : ℕ} (r : Fin m → ℕ) : ℕ :=
  m*(n*(4*weight (∑ i,r i)+2)+2)+1

end
end ContingencyTables.ExactPrintCost

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseTabulationScalarBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numeric dense-tabulation schedules versus binary margin size -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary Polynomial

def offsetNumericMeasure (z : OffsetWidthData) : ℕ := z.1.2+z.2+weight z

def trialNumericMeasure (z : DenseDrawParameters) : ℕ := z.1.2+z.2+weight z

def canonicalNumericMeasure (z : CanonicalParameters) : ℕ := z.2.1+z.2.2+weight z

/-- Only the two finite boxes contribute an exponential factor; the
numeric walk, rejection and reserved-word schedules are polynomial. -/
def rawBoxMeasure (z : CanonicalParameters) : ℕ :=
  (4*z.2.1^8)^tabulationDimension z+
    gridStateCount (completionEnumerationData z.1)+canonicalNumericMeasure z

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactCoreCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-prefix cost of the actual exact sampler control graph -/

namespace ContingencyTables.ExactCoreCost
open MatchingFPRAS MatchingFPRAS.TreeData MatchingFPRAS.TreeFunction
open MatchingFPRAS.TreeMachine (Env K encodeEnv)
open MatchingFPRAS.PhysicalStream MatchingFPRAS.OnlineStack
open ProfilePrograms DensePrograms ExactCoreProgram

noncomputable def retryCost (z : CompletionMargins) : ℕ :=
  OnlineIntegerRetry.stepCost ExactMatrixTrial.trialRealizer (exactMatrixInput z)

noncomputable def branchBudget (z : CompletionMargins) (N : ℕ) : ℕ :=
  exactOrdinaryRealizer.cost z+exactMatrixInputRealizer.cost z+N*retryCost z+
    2*TreeFunction.size (TreeTyped.encode z)+20

noncomputable def budget (z : CompletionMargins) (N : ℕ) : ℕ :=
  rareBranchRealizer.cost z+exactOrdinaryRealizer.cost z+exactMatrixInputRealizer.cost z+
    N*retryCost z+10*TreeFunction.size (TreeTyped.encode z)+50

end ContingencyTables.ExactCoreCost

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactGatePrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A cheap prefix ending before rare-branch tabulation -/

namespace ContingencyTables.ExactGatePrefix
open MatchingFPRAS MatchingFPRAS.TreeData MatchingFPRAS.TreeFunction
open MatchingFPRAS.TreeMachine (Env K encodeEnv)
open MatchingFPRAS.PhysicalStream MatchingFPRAS.OnlineStack
open ProfilePrograms DensePrograms ExactCoreProgram

noncomputable def output (z : CompletionMargins) (s : Data) :
    Option MatrixCode → OnlinePartialCall.Config instructions
  | none => OnlineControl.cfg instructions (some .prepareRare) (env (TreeTyped.encode z) .nil s)
  | some X => OnlineControl.cfg instructions none (env (TreeTyped.encode X) .nil s)

def experiment (z : CompletionMargins) : Experiment (Option MatrixCode) :=
  (rareBranch z).bind (fun b => if b then .done none else (exactOrdinary z).map some)

noncomputable def budget (z : CompletionMargins) : ℕ :=
  rareBranchRealizer.cost z+exactOrdinaryRealizer.cost z+10*TreeFunction.size (TreeTyped.encode z)+50

end ContingencyTables.ExactGatePrefix

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactGateCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial cost before the rare branch starts -/

namespace ContingencyTables.ExactGateCost
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms Polynomial

def measure (z : CompletionMargins) : ℕ :=
  exactParameterMeasure z+FiniteWordExecution.wordMeasure exactOrdinaryBits z

end ContingencyTables.ExactGateCost

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactTypedProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Parsing and printing around the same unbounded exact core -/

namespace ContingencyTables.ExactTypedProgram
open MatchingFPRAS MatchingFPRAS.TreeData MatchingFPRAS.TreeFunction
open MatchingFPRAS.TreeMachine (K encodeEnv)
open MatchingFPRAS.PhysicalStream MatchingFPRAS.OnlineStack
open ProfilePrograms DensePrograms

noncomputable def printedProgram : OnlineProc.Proc (K Reg) :=
  OnlineProc.seq ExactCoreProgram.program
    (OnlineProc.deterministic GreedyFeasibleTable.printMatrixRealizer.program)

noncomputable def printedOutput (z : CompletionMargins) (s : Data) :
    Option MatrixCode → OnlineTree.StoreCfg printedProgram
  | none => StackComposition.mapCfg Sum.inl (some (Sum.inr default)) (ExactCoreProgram.output z s none)
  | some X => OnlineTree.final printedProgram (TreeTyped.encode (GreedyFeasibleTable.printMatrix X)) s

noncomputable def program : OnlineProc.Proc (K Reg) :=
  OnlineProc.seq (OnlineProc.deterministic exactParsedMarginsRealizer.program) printedProgram

noncomputable def output (as : List Symbol) (s : Data) (o : Option MatrixCode) :
    OnlineTree.StoreCfg program := StackComposition.mapCfg Sum.inr none
      (printedOutput (exactParsedMargins as) s o)

end ContingencyTables.ExactTypedProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactGateTyped
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Parsing and printing around the cheap pre-tabulation prefix -/

namespace ContingencyTables.ExactGateTyped
open MatchingFPRAS MatchingFPRAS.TreeData MatchingFPRAS.TreeFunction
open MatchingFPRAS.TreeMachine (K encodeEnv)
open MatchingFPRAS.PhysicalStream MatchingFPRAS.OnlineStack
open ProfilePrograms DensePrograms ExactTypedProgram

noncomputable def printedOutput (z : CompletionMargins) (s : Data) :
    Option MatrixCode → OnlineTree.StoreCfg printedProgram
  | none => StackComposition.mapCfg Sum.inl (some (Sum.inr default)) (ExactGatePrefix.output z s none)
  | some X => OnlineTree.final printedProgram (TreeTyped.encode (GreedyFeasibleTable.printMatrix X)) s

noncomputable def output (as : List Symbol) (s : Data) (o : Option MatrixCode) :
    OnlineTree.StoreCfg program := StackComposition.mapCfg Sum.inr none
      (printedOutput (exactParsedMargins as) s o)

end ContingencyTables.ExactGateTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactPhysicalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical execution of the parsed and printed exact sampler -/

namespace ContingencyTables.ExactPhysicalProgram
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost
open MatchingFPRAS.TreeTyped MatchingFPRAS.TreePost Turing
open DensePrograms

noncomputable def ofOnline (P : OnlineProc.Proc (TreeMachine.K TreeFunction.Reg)) : Program where
  State := OnlineStack.Q (TreeMachine.K TreeFunction.Reg) (fun _ => Bool)
    P.Label RegisterProc.Store
  table := liftBool (OnlineStack.table P.code P.coin)
  states := OnlineStack.states P.code
  supported := liftBool_supported _ _
    (OnlineStack.table_supported P.code P.coin)
  entry := OnlineStack.initialState
  entry_mem := OnlineStack.initialState_mem P.code

noncomputable def program : Program := ofOnline ExactTypedProgram.program

attribute [local irreducible] ExactTypedProgram.program

noncomputable def output (as : List Symbol) (o : Option MatrixCode) : Cfg Symbol program.State :=
  upCfg (OnlineStack.cfg (ExactTypedProgram.output as .nil o))

end ContingencyTables.ExactPhysicalProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactGatePhysical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cheap exact-sampling prefix on the same physical program -/

namespace ContingencyTables.ExactGatePhysical
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost
open MatchingFPRAS.TreeTyped MatchingFPRAS.TreePost Turing
open DensePrograms ProfilePrograms

attribute [local irreducible] ExactTypedProgram.program

noncomputable def output (as : List Symbol) (o : Option MatrixCode) :
    Cfg Symbol ExactPhysicalProgram.program.State :=
  upCfg (OnlineStack.cfg (ExactGateTyped.output as .nil o))

noncomputable def typedBudget (as : List Symbol) (B : ℕ) : ℕ :=
  exactParsedMarginsRealizer.cost as+ExactGatePrefix.budget (exactParsedMargins as)+B

noncomputable def budget (as : List Symbol) (B : ℕ) : ℕ :=
  typedBudget as B*OnlineStack.Executes.factor ExactTypedProgram.program.code
    (weight as) (typedBudget as B)

end ContingencyTables.ExactGatePhysical

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactPhysicalCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A physical cost bound for every finite prefix of the exact sampler -/

namespace ContingencyTables.ExactPhysicalCost
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost
open MatchingFPRAS.TreeTyped MatchingFPRAS.TreePost Turing
open DensePrograms ProfilePrograms ExactPhysicalProgram

attribute [local irreducible] ExactTypedProgram.program

noncomputable def typedBudget (as : List Symbol) (N B : ℕ) : ℕ :=
  exactParsedMarginsRealizer.cost as+ExactCoreCost.budget (exactParsedMargins as) N+B

noncomputable def budget (as : List Symbol) (N B : ℕ) : ℕ :=
  typedBudget as N B*OnlineStack.Executes.factor ExactTypedProgram.program.code
    (weight as) (typedBudget as N B)

end ContingencyTables.ExactPhysicalCost

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactTablePrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite physical prefixes indexed by feasible tables -/

namespace ContingencyTables.ExactTablePrefix
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost
open DensePrograms SmallGraphProfiles Turing
open scoped Classical BigOperators
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
attribute [local irreducible] ExactCoreProgram.prefixExperiment
  ExactPhysicalProgram.program ExactPhysicalProgram.output

def code (o : Option (Table r c)) : Option MatrixCode := o.map (fun X => matrixCode X.val)

def decode : Option MatrixCode → Option (Table r c) := Function.invFun (code r c)

def experiment (N : ℕ) : Experiment (Option (Table r c)) :=
  (ExactCoreProgram.prefixExperiment (List.ofFn r,List.ofFn c) N).map (decode r c)

def input : List Symbol := Algorithms.encodeMargins r c

def output (o : Option (Table r c)) : Cfg Symbol ExactPhysicalProgram.program.State :=
  ExactPhysicalProgram.output (input r c) (code r c o)

end
end ContingencyTables.ExactTablePrefix

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactPublicPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed exact-sampling machine on the literal public binary tape -/

namespace ContingencyTables.ExactPublicPrefix
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing
open DensePrograms
open scoped Classical
noncomputable section

/-- These two finite programs are independent of dimensions and margins. -/
def middle : Program := ExactPhysicalProgram.program.seq LiteralProgram.post
def program : Program := LiteralProgram.pack.seq middle

def machine : RandomMachine := program.machine

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

def word (X : Table r c) : List Symbol := GreedyFeasibleTable.printMatrix (matrixCode X.val)

def middleOutput : Option (Table r c) → Cfg Symbol middle.State
  | none => leftCfg LiteralProgram.post.entry (ExactTablePrefix.output r c none)
  | some X => rightCfg (LiteralProgram.post.final (Tape.mk₁ (word r c X)))

def output (o : Option (Table r c)) : Cfg Symbol program.State := rightCfg (middleOutput r c o)

end
end ContingencyTables.ExactPublicPrefix

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactPublicCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cost-preserving literal wrapping of exact-sampling prefixes -/

namespace ContingencyTables.ExactPublicCost
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing
open DensePrograms
open scoped Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

def middleOutput (out : Option (Table r c) → Cfg Symbol ExactPhysicalProgram.program.State) :
    Option (Table r c) → Cfg Symbol ExactPublicPrefix.middle.State
  | none => leftCfg LiteralProgram.post.entry (out none)
  | some X => rightCfg (LiteralProgram.post.final (Tape.mk₁ (ExactPublicPrefix.word r c X)))

def output (out : Option (Table r c) → Cfg Symbol ExactPhysicalProgram.program.State)
    (o : Option (Table r c)) : Cfg Symbol ExactPublicPrefix.program.State :=
  rightCfg (middleOutput r c out o)

noncomputable def budget (N B L : ℕ) : ℕ :=
  LiteralProgram.packTime (ExactTablePrefix.input r c).length+
    ExactPhysicalCost.budget (ExactTablePrefix.input r c) N B+LiteralProgram.postTime L

end
end ContingencyTables.ExactPublicCost

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactGatePublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cheap gate prefix on public binary input -/

namespace ContingencyTables.ExactGatePublic
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing
open DensePrograms ProfilePrograms SmallGraphProfiles
open ExactTablePrefix (code decode input)
open scoped BigOperators Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

attribute [local irreducible] exactOrdinary

def experiment : Experiment (Option (Table r c)) :=
  (ExactGatePrefix.experiment (List.ofFn r,List.ofFn c)).map (decode r c)

noncomputable def output (o : Option (Table r c)) :
    Cfg Symbol ExactPhysicalProgram.program.State := ExactGatePhysical.output (input r c) (code r c o)

noncomputable def budget (B L : ℕ) : ℕ :=
  LiteralProgram.packTime (input r c).length+ExactGatePhysical.budget (input r c) B+LiteralProgram.postTime L

noncomputable def publicOutput := ExactPublicCost.output r c (output r c)

end
end ContingencyTables.ExactGatePublic

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactGatePolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform polynomial bound for the cheap public prefix -/

namespace ContingencyTables.ExactGatePolynomial
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream
open ProfilePrograms DensePrograms Polynomial
open Algorithms (samplingSize encodeMargins)
open scoped BigOperators Classical
noncomputable section

attribute [local irreducible] ExactTypedProgram.program exactParsedMargins
  ExactGatePrefix.budget ExactGateCost.measure

def measure (as : List Symbol) (B : ℕ) : ℕ :=
  weight as+ExactGateCost.measure (exactParsedMargins as)+B

end
end ContingencyTables.ExactGatePolynomial

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactRareCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial dependence of the correction cost on its finite tabulation measure -/

namespace ContingencyTables.ExactRareCost
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream
open ProfilePrograms DensePrograms Polynomial
noncomputable section

attribute [local irreducible] ExactTypedProgram.program exactParsedMargins
  ExactGateCost.measure exactRareMeasure exactMatrixInput

def measure (z : CompletionMargins) : ℕ := ExactGateCost.measure z+exactRareMeasure z

def publicMeasure (as : List Symbol) (B : ℕ) : ℕ :=
  weight as+measure (exactParsedMargins as)+B

end
end ContingencyTables.ExactRareCost

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_CacheBoxBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite boxes controlling one cached transition entry -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms Polynomial

def completionBoxMeasure (z : CanonicalParameters) : ℕ :=
  rawBoxMeasure (canonicalCountInput z).1+
    gridStateCount (completionEnumerationData z.1)+weight z

end ContingencyTables.DensePrograms

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

def matrixEntryBox (z : MatrixEntryInput) : ℕ :=
  completionBoxMeasure (residualParameters (entryCacheParameters z).1)+
    (entryCacheParameters z).2+gridStateCount (z.1.2,2)+weight z

def entryResidualParameters (z : MatrixEntryInput) : CanonicalParameters :=
  residualParameters (entryCacheParameters z).1

def entryResidualRealizer : Realizer entryResidualParameters :=
  composition (f := fun z : MatrixEntryInput => (entryCacheParameters z).1)
    (g := residualParameters)
    (composition (f := entryCacheParameters) (g := Prod.fst) entryCacheParametersRealizer first)
    residualParametersRealizer

end ContingencyTables.ProfilePrograms

end OAI
end


