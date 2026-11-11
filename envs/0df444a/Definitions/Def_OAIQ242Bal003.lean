-- Prove2me | Definitions.Def_OAIQ242Bal003
-- name    : OAIQ242Bal003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:46:44.105682+00:00
-- url     : https://prove2.me/theorems/d1232721-0f2c-47bb-af67-f949f9e60cc4
-- title:
--   Definitions bundle OAIQ242Bal003 of the split of OpenAI, Directional transience implies ballisticity
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 457 declarations of OpenAI's Lean: 183 definitions, 32 instances and 242 theorems. The definitions and types are `OAI.DirectionalTransience.SmallCommonLayer`, `OAI.DirectionalTransience.Stay`, `OAI.DirectionalTransience.StoppedRowsEvent`, `OAI.DirectionalTransience.StripExcursion`, `OAI.DirectionalTransience.StripUntil`, `OAI.DirectionalTransience.SurvivingLane`, `OAI.DirectionalTransience.TupleRelativeBudget`, `OAI.DirectionalTransience.UpwardCross`, `OAI.DirectionalTransience.ValidObservation`, `OAI.DirectionalTransience.ValidTupleSplit`, `OAI.DirectionalTransience.VelocityPaths`, `OAI.DirectionalTransience.VisibleFailure`, `OAI.DirectionalTransience.VisibleHistory`, `OAI.DirectionalTransience.VisitPrefix`, `OAI.DirectionalTransience.VisitReached`, `OAI.DirectionalTransience.WordEnvelope`, `OAI.DirectionalTransience.ZeroHeightPair`, `OAI.DirectionalTransience.alignHeight`, `OAI.DirectionalTransience.alignedCurvePolicy`, `OAI.DirectionalTransience.anchorsPerm`, `OAI.DirectionalTransience.arrayDustFrequency`, `OAI.DirectionalTransience.arrayLink`, `OAI.DirectionalTransience.arrayNatHeight`, `OAI.DirectionalTransience.arrayOffsetTest`, `OAI.DirectionalTransience.arrayProfileMeasure`, `OAI.DirectionalTransience.arrayProfileTest`, `OAI.DirectionalTransience.arrayRealCost`, `OAI.DirectionalTransience.arraySamplingError`, `OAI.DirectionalTransience.arraySurvivalThreshold`, `OAI.DirectionalTransience.badBoxEvent`, `OAI.DirectionalTransience.badCrossingEvent`, `OAI.DirectionalTransience.blockRows`, `OAI.DirectionalTransience.boundaryAtom`, `OAI.DirectionalTransience.boundaryPrefixPair`, `OAI.DirectionalTransience.boundaryTerminal`, `OAI.DirectionalTransience.budgetEndpointMixture`, `OAI.DirectionalTransience.budgetFirstThreat`, `OAI.DirectionalTransience.budgetRetryEvent`, `OAI.DirectionalTransience.budgetThreatEvent`, `OAI.DirectionalTransience.budgetTraversalMass` and 143 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `Ballisticity_Coupling_FreshBufferAE`, `Ballisticity_Coupling_GaussianQuenchedTube`, `Ballisticity_Coupling_QuenchedMoments`, `Ballisticity_Coupling_SeedMedian`, `Ballisticity_Coupling_SeedProfile`, `Ballisticity_Coupling_SeedStateOrder`, `Ballisticity_Coupling_StoppedFreshField`, `Ballisticity_Coupling_WeightedAnnealed`, `Ballisticity_Crossings_BadCrossingLaw`, `Ballisticity_Crossings_CommonCutCounting`, `Ballisticity_Crossings_CommonCutObserver`, `Ballisticity_Crossings_CrossingGap`, `Ballisticity_Crossings_FiniteBoxExit`, `Ballisticity_Crossings_Hit`, `Ballisticity_Crossings_HitWord`, `Ballisticity_Crossings_LowerObservedCut`, `Ballisticity_Crossings_OffDiagonalCenteredCross`, `Ballisticity_Crossings_StripExitBound`, `Ballisticity_Entropy_BufferCostBounds`, `Ballisticity_Entropy_StoppedEntropySum`, `Ballisticity_Entropy_StoppedWindowEntropy`, `Ballisticity_Estimates_AlignedRecordPrefix`, `Ballisticity_Estimates_AllIndexMarks`, `Ballisticity_Estimates_BoundarySuffixIdentity`, `Ballisticity_Estimates_BudgetAdapted`, `Ballisticity_Estimates_BudgetAlgebra`, `Ballisticity_Estimates_BudgetClipping`, `Ballisticity_Estimates_BudgetEndpoint`, `Ballisticity_Estimates_BudgetMeasurable`, `Ballisticity_Estimates_BudgetNormalize`, `Ballisticity_Estimates_BudgetThreat`, `Ballisticity_Estimates_Buffer`, `Ballisticity_Estimates_BufferChanceData`, `Ballisticity_Estimates_BufferChildNode`, `Ballisticity_Estimates_BufferFirstFailure`, `Ballisticity_Estimates_BufferRestorationScript`, `Ballisticity_Estimates_BufferTree`, `Ballisticity_Estimates_CappedMomentTransfer`, `Ballisticity_Estimates_Cell`, `Ballisticity_Estimates_CellAttempt`, `Ballisticity_Estimates_CellFailure`, `Ballisticity_Estimates_CellSchedule`, `Ballisticity_Estimates_ClassFinset`, `Ballisticity_Estimates_CommonBoundaryRestart`, `Ballisticity_Estimates_CommonOffset`, `Ballisticity_Estimates_CommonTrueRecord`, `Ballisticity_Estimates_CommonWordWidth`, `Ballisticity_Estimates_CurvePolicy`, `Ballisticity_Estimates_CurvePolicyAverageMoment`, `Ballisticity_Estimates_CurvePolicyMaximal`, `Ballisticity_Estimates_CurvePolicyPMF`, `Ballisticity_Estimates_CurvePrefix`, `Ballisticity_Estimates_DirectBridge`, `Ballisticity_Estimates_Dust`, `Ballisticity_Estimates_FinitePastDecorrelation`, `Ballisticity_Estimates_FirstBelow`, `Ballisticity_Estimates_FixedPairSuffix`, `Ballisticity_Estimates_GaussianAbsTail`, `Ballisticity_Estimates_GlobalProfile`, `Ballisticity_Estimates_IndependentDyadic`, `Ballisticity_Estimates_IndependentPairLaw`, `Ballisticity_Estimates_IndependentRandomTestBound`, `Ballisticity_Estimates_IntegerMedian`, `Ballisticity_Estimates_JointPastRestart`, `Ballisticity_Estimates_LowerClip`, `Ballisticity_Estimates_MarkedObservables`, `Ballisticity_Estimates_MixtureSmallMassProbability`, `Ballisticity_Estimates_ObservedBudget`, `Ballisticity_Estimates_ObservedDrift`, `Ballisticity_Estimates_OperationalLengthMarks`, `Ballisticity_Estimates_PairUpwardRetention`, `Ballisticity_Estimates_ProfileMeasureUpdate`, `Ballisticity_Estimates_ProperProfile`, `Ballisticity_Estimates_ProtectionLoss`, `Ballisticity_Estimates_RawConditionedWeight`, `Ballisticity_Estimates_RawPair`, `Ballisticity_Estimates_RawPairLocality`, `Ballisticity_Estimates_RawPairRetention`, `Ballisticity_Estimates_RealJointPastRestart`, `Ballisticity_Estimates_RecordIndexTime`, `Ballisticity_Estimates_RecordMedianSlope`, `Ballisticity_Estimates_RecordPairFuture`, `Ballisticity_Estimates_RelativeBudget`, `Ballisticity_Estimates_Sampling`, `Ballisticity_Estimates_SamplingLaw`, `Ballisticity_Estimates_SelectedBoundaryRestart`, `Ballisticity_Estimates_SharedEndpointTests`, `Ballisticity_Estimates_SingleThreat`, `Ballisticity_Estimates_StayUntil`, `Ballisticity_Estimates_StoppedSplice`, `Ballisticity_Estimates_StrictRecord`, `Ballisticity_Estimates_SuccessfulAverage`, `Ballisticity_Estimates_SuccessfulWords`, `Ballisticity_Estimates_SurvivingLane`, `Ballisticity_Estimates_SymmetricTruncate`, `Ballisticity_Estimates_TailProfile`, `Ballisticity_Estimates_TupleEndpoint`, `Ballisticity_Estimates_TwoStopSplice`, `Ballisticity_Estimates_VisibleFailure`, `Ballisticity_Estimates_VisitTrials`, `Ballisticity_Estimates_WeightedConditioned`, `Ballisticity_Estimates_WordConcatenation`, `Ballisticity_Estimates_WordDepartures`, `Ballisticity_Estimates_WordPrefixes`, `Ballisticity_Geometry_AlignedSlabs`, `Ballisticity_Geometry_BufferStructuralHeight`, `Ballisticity_Geometry_CoordinateStrip`, `Ballisticity_Geometry_FinitePastCoordinates`, `Ballisticity_Geometry_FiniteWordGeometry`, `Ballisticity_Geometry_HeightSlab`, `Ballisticity_Geometry_PairHeight`, `Ballisticity_Geometry_SpatialConfinement`, `Ballisticity_Geometry_WindowWeak`, `Ballisticity_Geometry_WordHeightGain`, `Ballisticity_Renewal_DurationMoment`, `Ballisticity_Renewal_PositiveLengthMark`, `Ballisticity_Renewal_RegenerationWords`, `Ballisticity_Renewal_VelocityWords`, `Ballisticity_Stationary_Array`, `Ballisticity_Stationary_ArrayClosed`, `Ballisticity_Stationary_ArrayDust`, `Ballisticity_Stationary_ArrayFiniteClasses`, `Ballisticity_Stationary_ArrayMap`, `Ballisticity_Stationary_ArrayMarkTests`, `Ballisticity_Stationary_ArrayMarkedEntropy`, `Ballisticity_Stationary_ArrayMarkedIterate`, `Ballisticity_Stationary_ArrayMassSurvival`, `Ballisticity_Stationary_ArrayPermutation`, `Ballisticity_Stationary_ArrayProfileConsistency`, `Ballisticity_Stationary_ArraySurvival`, `Ballisticity_Stationary_ArrayTopology`, `Ballisticity_Stationary_ArrayWindowMarks`, `Ballisticity_Stationary_EpisodeCountLedger`, `Ballisticity_Stationary_EpisodeRetention`, `Ballisticity_Stationary_StationaryMonotone`, `Ballisticity_Walk_ArrayCostGrowth`, `Ballisticity_Walk_BufferGrowthArithmetic`, `Ballisticity_Walk_BufferNormalizedRows`, `Ballisticity_Walk_ClippedPairGrowth`, `Ballisticity_Walk_FixedQuenchedKernel`, `Ballisticity_Walk_OutwardCanonicalRows`, `Ballisticity_Walk_PathCompact`, `Ballisticity_Walk_RecordLinearPath`, `Ballisticity_Walk_RetentionRowsAllHeights`, `Ballisticity_Walk_SelectedFiniteKernel`, `Ballisticity_Walk_StateTrajectory`, `Ballisticity_Walk_UpperKernel`.
--
--   **Imports.** It imports the published bundle `Def_DirectionalBallisticity`; the bundles `OAIQ242Bal000` and `OAIQ242Bal001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ242Bal005` and `OAIQ242Bal006`; the statements `OAI.DirectionalTransience.OperationalConstants.bad_array_finite_marks`, `OAI.DirectionalTransience.OperationalConstants.bad_dropMarkCut_upper`, `OAI.DirectionalTransience.OperationalConstants.bad_limit_averaged_survival`, `OAI.DirectionalTransience.OperationalConstants.bad_limit_drop_moment`, `OAI.DirectionalTransience.OperationalConstants.bad_limit_length_moment`, `OAI.DirectionalTransience.OperationalConstants.bad_occupation_stationary_limit`, `OAI.DirectionalTransience.OperationalConstants.conditional_episode_drops`, `OAI.DirectionalTransience.OperationalConstants.raw_dropCut_upper`, `OAI.DirectionalTransience.actual_buffer_excess`, `OAI.DirectionalTransience.actual_consumed_cell_failure`, `OAI.DirectionalTransience.actual_late_protection_first_failure`, `OAI.DirectionalTransience.actual_outward_log_bound`, `OAI.DirectionalTransience.fresh_budget_threat_bound`, `OAI.DirectionalTransience.occupation_finite_bound`, `OAI.DirectionalTransience.shared_clipped_observation_transfer`, `OAI.DirectionalTransience.shared_uniform_good_clipped_drift`, `OAI.DirectionalTransience.spatial_confinement` and `OAI.DirectionalTransience.stripTime_rapidDecay`; the proof of `OAI.DirectionalTransience.gaussian_renewal_path_limit`.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal000
import Definitions.Def_OAIQ242Bal001

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_StateTrajectory
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
attribute [-simp] _root_.OAI.DirectionalTransience.latticeVector_zero _root_.OAI.DirectionalTransience.wordPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace DirectionalTransience

lemma stateTrajectory_eq {d : ℕ} (μ : Measure (State d)) :
    stateTrajectory ∘ₘ μ = Kernel.trajMeasure μ (historyTransition (d := d)) := by
  unfold Kernel.trajMeasure stateTrajectory
  rw [← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map]
  rfl

lemma annealed_eq_quenched_mixture {d : ℕ} (ν : Measure (Row d)) :
    annealedLaw ν = quenchedKernel ∘ₘ initialLaw ν := by
  unfold annealedLaw quenchedKernel
  rw [← stateTrajectory_eq, Measure.map_comp]
  exact Measurable.of_eval fun n => measurable_snd.comp (measurable_pi_apply n)

lemma annealed_apply {d : ℕ} (ν : Measure (Row d)) {A : Set (Path d)}
    (hA : MeasurableSet A) :
    annealedLaw ν A = ∫⁻ ω, quenchedKernel (ω, (0 : Lattice d)) A ∂environmentLaw ν := by
  rw [annealed_eq_quenched_mixture, Measure.bind_apply hA (Kernel.aemeasurable _),
    initialLaw, lintegral_map]
  · exact Kernel.measurable_coe _ hA
  · exact measurable_id.prodMk measurable_const

lemma environment_indep_rows {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    {S T : Set (Lattice d)} (hST : Disjoint S T) :
    Indep (rowSigma S) (rowSigma T) (environmentLaw ν) := by
  exact indep_iSup_of_disjoint (fun x => (measurable_pi_apply x).comap_le)
    (iIndepFun_infinitePi (P := fun _ : Lattice d => ν)
      (X := fun _ p => p) (fun _ => measurable_id)).iIndep hST

lemma environment_tail_zero_one {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    {E : Set (Environment d)}
    (hE : ∀ S ∈ (cofinite : Filter (Lattice d)), MeasurableSet[rowSigma S] E) :
    environmentLaw ν E = 0 ∨ environmentLaw ν E = 1 := by
  let s : Lattice d → MeasurableSpace (Environment d) := fun x =>
    MeasurableSpace.comap (fun ω : Environment d => ω x) inferInstance
  have hind : iIndep s (environmentLaw ν) :=
    (iIndepFun_infinitePi (P := fun _ : Lattice d => ν)
      (X := fun _ p => p) (fun _ => measurable_id)).iIndep
  have ht : MeasurableSet[limsup s cofinite] E := by
    rw [limsup_eq_iInf_iSup]
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro S
    apply MeasurableSpace.measurableSet_iInf.mpr
    exact hE S
  apply measure_zero_or_one_of_measurableSet_limsup
    (s := s) (p := Set.Finite) (ns := fun F : Finset (Lattice d) => (F : Set (Lattice d)))
    (fun x => (measurable_pi_apply x).comap_le) hind
    (fun S hS => by simpa only [mem_cofinite, compl_compl] using hS) _
    (fun F => F.finite_toSet) (fun x => ⟨{x}, by simp⟩) ht
  intro F G
  exact ⟨F ∪ G, Finset.coe_subset.mpr Finset.subset_union_left,
    Finset.coe_subset.mpr Finset.subset_union_right⟩

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_IndependentRandomTestBound
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma indepFun_of_disjoint_rows {d : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] {S T : Set (Lattice d)} (hST : Disjoint S T)
    (U : Environment d → A) (V : Environment d → B)
    (hU : @Measurable _ _ (rowSigma S) _ U) (hV : @Measurable _ _ (rowSigma T) _ V) :
    IndepFun U V (environmentLaw ν) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  exact (Indep_iff _ _ _).mp (environment_indep_rows ν hST) _ _ (hU hs) (hV ht)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_WordDepartures
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
attribute [-simp] _root_.OAI.DirectionalTransience.latticeVector_zero _root_.OAI.DirectionalTransience.recordCount_zero _root_.OAI.DirectionalTransience.regenerationTimes_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

def pathCylinder {d : ℕ} (f : Path d) (n : ℕ) : Set (Path d) :=
  {X | ∀ i ≤ n, X i = f i}

lemma measurableSet_pathCylinder {d : ℕ} (f : Path d) (n : ℕ) :
    MeasurableSet (pathCylinder f n) := by
  simp only [pathCylinder, Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    measurableSet_eq_fun (measurable_pi_apply i : Measurable (fun X : Path d => X i))
      measurable_const

lemma pathMeasure_ext {d : ℕ} (μ ν : Measure (Path d)) [IsFiniteMeasure μ]
    (h : ∀ f n, μ (pathCylinder f n) = ν (pathCylinder f n)) : μ = ν := by
  let P : (I : Finset ℕ) → Measure ((i : I) → Lattice d) :=
    fun I => μ.map I.restrict
  have hp : IsProjectiveMeasureFamily (α := fun _ : ℕ => Lattice d) P := by
    exact isProjectiveMeasureFamily_map_restrict (P := μ) (X := fun n (X : Path d) => X n)
      (fun n => (measurable_pi_apply n).aemeasurable)
  have hμ : IsProjectiveLimit (α := fun _ : ℕ => Lattice d) μ P := by
    intro I
    rfl
  apply hμ.unique
  apply (isProjectiveLimit_nat_iff hp ν).mpr
  intro n
  apply Measure.ext_of_singleton
  intro f
  have hf : MeasurableSet ({f} : Set ((i : Finset.Iic n) → Lattice d)) :=
    measurableSet_singleton _
  rw [Measure.map_apply (Preorder.measurable_frestrictLe n) hf]
  change _ = μ.map (Preorder.frestrictLe n) {f}
  rw [Measure.map_apply (Preorder.measurable_frestrictLe n) hf]
  let g : Path d := fun i => if hi : i ≤ n then f ⟨i, Finset.mem_Iic.mpr hi⟩ else 0
  have he : (fun X : Path d => Preorder.frestrictLe n X) ⁻¹' {f} = pathCylinder g n := by
    ext X
    simp only [Set.mem_preimage, Set.mem_singleton_iff, pathCylinder, Set.mem_ofPred_eq]
    constructor
    · intro hh i hi
      simpa [g, hi] using congrFun hh ⟨i, Finset.mem_Iic.mpr hi⟩
    · intro hh
      funext i
      simpa [g, Finset.mem_Iic.mp i.2] using hh i (Finset.mem_Iic.mp i.2)
  rw [he, h]

noncomputable def edgeWeight {d : ℕ} (ω : Environment d) (x y : Lattice d) : ℝ≥0∞ :=
  ∑ e : Direction d, if y = x + step e then ((ω x).1 e : ℝ≥0∞) else 0

lemma transition_singleton {d : ℕ} (ω : Environment d) (x y : Lattice d) :
    transition (ω, x) {(ω, y)} = edgeWeight ω x y := by
  classical
  change (∑ e : Direction d, ((ω x).1 e : ℝ≥0∞) •
    Measure.dirac (ω, x + step e)) {(ω, y)} = _
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, edgeWeight]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : y = x + step e
  · simp [he]
  · simp [he, Ne.symm he]

lemma quenched_pathCylinder {d : ℕ} (ω : Environment d) (x : Lattice d)
    (f : Path d) (hf : f 0 = x) (n : ℕ) :
    quenchedKernel (ω, x) (pathCylinder f n) =
      ∏ i ∈ Finset.range n, edgeWeight ω (f i) (f (i + 1)) := by
  have hm : Measurable (fun z : ℕ → State d => fun n => (z n).2) := by fun_prop
  rw [quenchedKernel, Kernel.map_apply _ hm, Measure.map_apply hm (measurableSet_pathCylinder f n)]
  have he : (fun z : ℕ → State d => fun n => (z n).2) ⁻¹' pathCylinder f n
      =ᵐ[stateTrajectory (ω, x)] stateCylinder (fun i => (ω, f i)) n := by
    filter_upwards [stateTrajectory_environment (ω, x)] with X hX
    apply propext
    change (∀ i ≤ n, (X i).2 = f i) ↔ (∀ i ≤ n, X i = (ω, f i))
    constructor
    · intro hh i hi
      exact Prod.ext (hX i) (hh i hi)
    · intro hh i hi
      exact congrArg Prod.snd (hh i hi)
  rw [measure_congr he, stateTrajectory_cylinder _ _ (by simp [hf])]
  simp only [transition_singleton]

lemma quenched_pathCylinder_zero {d : ℕ} (ω : Environment d) (x : Lattice d)
    (f : Path d) (hf : f 0 ≠ x) (n : ℕ) :
    quenchedKernel (ω, x) (pathCylinder f n) = 0 := by
  have hsub : pathCylinder f n ⊆ {X | X 0 ≠ x} := by
    intro X hX
    change X 0 ≠ x
    rw [hX 0 (Nat.zero_le n)]
    exact hf
  exact measure_mono_null hsub ((ae_iff).mp (quenched_initial_ae (ω, x)))

lemma edgeWeight_translation {d : ℕ} (ω : Environment d) (z x y : Lattice d) :
    edgeWeight (fun a => ω (z + a)) x y = edgeWeight ω (z + x) (z + y) := by
  classical
  simp only [edgeWeight]
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  simp only [add_assoc, add_right_inj]

lemma quenched_translation {d : ℕ} (ω : Environment d) (z x : Lattice d) :
    (quenchedKernel (ω, z + x)).map (fun X n => X n - z) =
      quenchedKernel ((fun a => ω (z + a)), x) := by
  have hm : Measurable (fun X : Path d => fun n => X n - z) := by fun_prop
  apply pathMeasure_ext
  intro f n
  rw [Measure.map_apply hm (measurableSet_pathCylinder f n)]
  have he : (fun X : Path d => fun i => X i - z) ⁻¹' pathCylinder f n =
      pathCylinder (fun i => z + f i) n := by
    ext X
    simp only [pathCylinder, Set.mem_preimage, Set.mem_ofPred_eq, sub_eq_iff_eq_add, add_comm]
  rw [he]
  by_cases hf : f 0 = x
  · rw [quenched_pathCylinder _ _ _ (by simp [hf]), quenched_pathCylinder _ _ _ hf]
    simp only [edgeWeight_translation]
  · rw [quenched_pathCylinder_zero _ _ _ (by simpa using hf),
      quenched_pathCylinder_zero _ _ _ hf]

def splicePath {d : ℕ} (f g : Path d) (n : ℕ) : Path d :=
  fun i => if i < n then f i else g (i - n)

lemma splicePath_left {d : ℕ} (f g : Path d) {n i : ℕ}
    (hg : g 0 = f n) (hi : i ≤ n) : splicePath f g n i = f i := by
  rcases lt_or_eq_of_le hi with hi | rfl
  · simp [splicePath, hi]
  · simp [splicePath, hg]

lemma splicePath_right {d : ℕ} (f g : Path d) (n i : ℕ) :
    splicePath f g n (n + i) = g i := by
  simp [splicePath]

lemma pathCylinder_splice {d : ℕ} (f g : Path d) (n k : ℕ) (hg : g 0 = f n) :
    (fun X : Path d => fun i => X (n + i)) ⁻¹' pathCylinder g k ∩ pathCylinder f n =
      pathCylinder (splicePath f g n) (n + k) := by
  ext X
  simp only [Set.mem_inter_iff, Set.mem_preimage, pathCylinder, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h₁, h₂⟩ i hi
    by_cases hin : i ≤ n
    · rw [splicePath_left f g hg hin]
      exact h₂ i hin
    · have hn : n ≤ i := by omega
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [splicePath_right]
      exact h₁ j (by omega)
  · intro hX
    constructor
    · intro i hi
      simpa only [splicePath_right] using hX (n + i) (by omega)
    · intro i hi
      simpa only [splicePath_left f g hg hi] using hX i (by omega)

lemma splicePath_weight {d : ℕ} (ω : Environment d) (f g : Path d) (n k : ℕ)
    (hg : g 0 = f n) :
    (∏ i ∈ Finset.range (n + k),
      edgeWeight ω (splicePath f g n i) (splicePath f g n (i + 1))) =
      (∏ i ∈ Finset.range n, edgeWeight ω (f i) (f (i + 1))) *
      ∏ i ∈ Finset.range k, edgeWeight ω (g i) (g (i + 1)) := by
  rw [Finset.prod_range_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    have hin := Finset.mem_range.mp hi
    rw [splicePath_left f g hg (by omega), splicePath_left f g hg (by omega)]
  · apply Finset.prod_congr rfl
    intro i _
    rw [splicePath_right, show n + i + 1 = n + (i + 1) by omega, splicePath_right]

lemma quenched_prefix_markov {d : ℕ} (ω : Environment d) (x : Lattice d)
    (f : Path d) (hf : f 0 = x) (n : ℕ) :
    ((quenchedKernel (ω, x)).restrict (pathCylinder f n)).map
        (fun X i => X (n + i)) =
      (quenchedKernel (ω, x) (pathCylinder f n)) • quenchedKernel (ω, f n) := by
  have hm : Measurable (fun X : Path d => fun i => X (n + i)) := by fun_prop
  apply pathMeasure_ext
  intro g k
  rw [Measure.map_apply hm (measurableSet_pathCylinder g k),
    Measure.restrict_apply (hm (measurableSet_pathCylinder g k)), Measure.smul_apply, smul_eq_mul]
  by_cases hg : g 0 = f n
  · rw [pathCylinder_splice f g n k hg,
      quenched_pathCylinder _ _ _ ((splicePath_left f g hg (Nat.zero_le n)).trans hf),
      quenched_pathCylinder _ _ _ hf, quenched_pathCylinder _ _ _ hg,
      splicePath_weight ω f g n k hg]
  · rw [quenched_pathCylinder_zero _ _ _ hg, mul_zero]
    have he : (fun X : Path d => fun i => X (n + i)) ⁻¹' pathCylinder g k ∩
        pathCylinder f n = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro X ⟨h₁, h₂⟩
      have h₁' := h₁ 0 (Nat.zero_le k)
      have h₂' := h₂ n le_rfl
      apply hg
      simpa using h₁'.symm.trans (by simpa using h₂')
    rw [he, measure_empty]

lemma quenched_prefix_future {d : ℕ} (ω : Environment d) (x : Lattice d)
    (f : Path d) (hf : f 0 = x) (n : ℕ) {A : Set (Path d)} (hA : MeasurableSet A) :
    quenchedKernel (ω, x)
      ((fun X : Path d => fun i => X (n + i)) ⁻¹' A ∩ pathCylinder f n) =
      quenchedKernel (ω, x) (pathCylinder f n) * quenchedKernel (ω, f n) A := by
  have h := congrArg (fun μ : Measure (Path d) => μ A) (quenched_prefix_markov ω x f hf n)
  rw [Measure.map_apply (by fun_prop) hA, Measure.restrict_apply ((by fun_prop : Measurable (fun X : Path d => fun i => X (n + i))) hA),
    Measure.smul_apply, smul_eq_mul] at h
  exact h

lemma measurableSet_noDrop {d : ℕ} (ℓ : Vector d) (x : Lattice d) :
    MeasurableSet (NoDrop ℓ x) := by
  simp only [NoDrop, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro n
  exact measurableSet_le measurable_const
    ((measurable_of_countable (f := fun y : Lattice d => dot (realPosition y) ℓ)).comp
      (measurable_pi_apply n))

lemma dot_realPosition_add {d : ℕ} (x y : Lattice d) (ℓ : Vector d) :
    dot (realPosition (x + y)) ℓ = dot (realPosition x) ℓ + dot (realPosition y) ℓ := by
  simp [dot, realPosition, add_mul, Finset.sum_add_distrib]

lemma dot_realPosition_sub {d : ℕ} (x y : Lattice d) (ℓ : Vector d) :
    dot (realPosition (x - y)) ℓ = dot (realPosition x) ℓ - dot (realPosition y) ℓ := by
  simp [dot, realPosition, sub_mul, Finset.sum_sub_distrib]

lemma noDrop_translation {d : ℕ} (ℓ : Vector d) (z x : Lattice d) :
    (fun X : Path d => fun n => X n - z) ⁻¹' NoDrop ℓ x = NoDrop ℓ (z + x) := by
  ext X
  simp only [NoDrop, Set.mem_preimage, Set.mem_ofPred_eq, dot_realPosition_add,
    dot_realPosition_sub]
  apply forall_congr'
  intro n
  constructor <;> intro h <;> linarith

lemma measurableSet_futureNoDrop {d : ℕ} (ℓ : Vector d) (n : ℕ) :
    MeasurableSet (FutureNoDrop ℓ n) := by
  simp only [FutureNoDrop, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le
    ((measurable_of_countable (fun y : Lattice d => dot (realPosition y) ℓ)).comp
      (measurable_pi_apply n))
    ((measurable_of_countable (fun y : Lattice d => dot (realPosition y) ℓ)).comp
      (measurable_pi_apply (n + i)))

lemma extendPrefix_apply {d : ℕ} (n : ℕ) (f : (i : Finset.Iic n) → Lattice d)
    (i : ℕ) (hi : i ≤ n) :
    extendPrefix n f i = f ⟨i, Finset.mem_Iic.mpr hi⟩ := by
  simp [extendPrefix, hi]

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_StayUntil
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
attribute [-simp] _root_.OAI.DirectionalTransience.latticeVector_zero _root_.OAI.DirectionalTransience.recordCount_zero _root_.OAI.DirectionalTransience.regenerationTimes_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

def Stay {d : ℕ} (S : Set (Lattice d)) : Set (Path d) :=
  {X | ∀ i, X i ∈ S}

lemma measurableSet_stay {d : ℕ} (S : Set (Lattice d)) :
    MeasurableSet (Stay S) := by
  simp only [Stay, Set.ofPred_forall]
  exact MeasurableSet.iInter fun i =>
    (measurable_pi_apply i) S.to_countable.measurableSet

lemma restrict_prefix_fiber {d : ℕ} (n : ℕ)
    (f : (i : Finset.Iic n) → Lattice d) :
    (fun X : Path d => Preorder.frestrictLe n X) ⁻¹' {f} =
      pathCylinder (extendPrefix n f) n := by
  ext X
  simp only [Set.mem_preimage, Set.mem_singleton_iff, pathCylinder, Set.mem_ofPred_eq]
  constructor
  · intro hh i hi
    simpa [extendPrefix, hi] using congrFun hh ⟨i, Finset.mem_Iic.mpr hi⟩
  · intro hh
    funext i
    simpa [extendPrefix, Finset.mem_Iic.mp i.2] using hh i (Finset.mem_Iic.mp i.2)

lemma dot_realPosition_nsmul {d : ℕ} (n : ℕ) (x : Lattice d) (ℓ : Vector d) :
    dot (realPosition (n • x)) ℓ = (n : ℝ) * dot (realPosition x) ℓ := by
  induction n with
  | zero => simp [dot, realPosition]
  | succ n ih =>
    rw [succ_nsmul, dot_realPosition_add, ih, Nat.cast_add, Nat.cast_one]
    ring

lemma measure_partition_prefix {d : ℕ} (μ : Measure (Path d)) (A : Set (Path d)) (n : ℕ) :
    μ A = ∑' f : (i : Finset.Iic n) → Lattice d, μ (A ∩ pathCylinder (extendPrefix n f) n) := by
  have h := tsum_measure_preimage_singleton (μ := μ.restrict A)
    (s := Set.univ) (Set.to_countable _) (f := fun X : Path d => Preorder.frestrictLe n X)
    (fun f _ => (Preorder.measurable_frestrictLe n) (measurableSet_singleton f))
  simp only [Set.preimage_univ, Measure.restrict_apply
    MeasurableSet.univ, Set.univ_inter] at h
  rw [tsum_subtype Set.univ (fun f => (μ.restrict A)
    ((fun X : Path d => Preorder.frestrictLe n X) ⁻¹' {f})), Set.indicator_univ] at h
  rw [← h]
  apply tsum_congr
  intro f
  rw [Measure.restrict_apply ((Preorder.measurable_frestrictLe n) (measurableSet_singleton f)),
    restrict_prefix_fiber, Set.inter_comm]

lemma lintegral_partition_prefix {d : ℕ} (μ : Measure (Path d)) (A : Set (Path d))
    (n : ℕ) (g : ((i : Finset.Iic n) → Lattice d) → ℝ≥0∞) :
    (∫⁻ X in A, g (Preorder.frestrictLe n X) ∂μ) =
      ∑' f : (i : Finset.Iic n) → Lattice d,
        g f * μ (A ∩ pathCylinder (extendPrefix n f) n) := by
  rw [← lintegral_map (measurable_of_countable g) (Preorder.measurable_frestrictLe n),
    lintegral_countable']
  apply tsum_congr
  intro f
  rw [Measure.map_apply (Preorder.measurable_frestrictLe n) (measurableSet_singleton f),
    Measure.restrict_apply ((Preorder.measurable_frestrictLe n) (measurableSet_singleton f)),
    restrict_prefix_fiber, Set.inter_comm]

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_Hit
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
attribute [-simp] _root_.OAI.DirectionalTransience.latticeVector_zero _root_.OAI.DirectionalTransience.recordCount_zero _root_.OAI.DirectionalTransience.regenerationTimes_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma measurableSet_hit {d : ℕ} (S T : Set (Lattice d)) : MeasurableSet (Hit S T) :=
  MeasurableSet.iUnion (measurableSet_hitAt S T)

lemma cross_eq_hit {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) :
    Cross ℓ x H = Hit (Strip ℓ x H) (Upper ℓ x H) := by
  classical
  ext X
  constructor
  · rintro ⟨n, hn, hp⟩
    have hex : ∃ k, dot (realPosition x) ℓ + H ≤ dot (realPosition (X k)) ℓ := ⟨n, hn⟩
    apply Set.mem_iUnion.mpr
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    intro i hi
    refine ⟨hp i (hi.trans_le (Nat.find_min' hex hn)), ?_⟩
    exact lt_of_not_ge (Nat.find_min hex hi)
  · intro h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
    exact ⟨n, hn.1, fun i hi => (hn.2 i hi).1⟩

lemma measurableSet_cross {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) :
    MeasurableSet (Cross ℓ x H) := by
  rw [cross_eq_hit]
  exact measurableSet_hit _ _

lemma cross_antitone {d : ℕ} (ℓ : Vector d) (x : Lattice d) : Antitone (Cross ℓ x) := by
  intro H K hHK X hX
  obtain ⟨n, hn, hp⟩ := hX
  exact ⟨n, (add_le_add_right hHK _).trans hn, hp⟩

lemma iInter_cross_subset_noDrop {d : ℕ} (ℓ : Vector d) (x : Lattice d) :
    (⋂ H : ℕ, Cross ℓ x H) ⊆ NoDrop ℓ x := by
  intro X hX n
  by_contra hn
  have hbound : ∃ b : ℝ, ∀ i ≤ n, dot (realPosition (X i)) ℓ < b := by
    obtain ⟨b, hb⟩ := ((Finset.range (n + 1)).finite_toSet.image
      (fun i => dot (realPosition (X i)) ℓ)).bddAbove
    refine ⟨b + 1, fun i hi => ?_⟩
    have hbi := hb (Set.mem_image_of_mem _ (show i ∈ (Finset.range (n + 1) : Set ℕ) by
      simp only [Finset.mem_coe, Finset.mem_range]; omega))
    linarith
  obtain ⟨b, hb⟩ := hbound
  obtain ⟨H, hH⟩ := exists_nat_gt (b - dot (realPosition x) ℓ)
  obtain ⟨m, hm, hp⟩ := Set.mem_iInter.mp hX H
  by_cases hmn : m ≤ n
  · have hh := hb m hmn
    linarith
  · exact hn (hp n (by omega))

lemma noDrop_subset_cross_of_tendsto {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (X : Path d) (hX : Tendsto (fun n => dot (realPosition (X n)) ℓ) atTop atTop)
    (hD : X ∈ NoDrop ℓ x) (H : ℝ) : X ∈ Cross ℓ x H := by
  obtain ⟨n, hn⟩ := (hX.eventually (eventually_ge_atTop (dot (realPosition x) ℓ + H))).exists
  exact ⟨n, hn, fun i _ => hD i⟩

lemma measurableSet_transientPaths {d : ℕ} (ℓ : Vector d) :
    MeasurableSet (TransientPaths ℓ) := by
  apply measurableSet_tendsto
  intro n
  exact (measurable_of_countable (fun y : Lattice d => dot (realPosition y) ℓ)).comp
    (measurable_pi_apply n)

lemma transientPaths_translation {d : ℕ} (ℓ : Vector d) (x : Lattice d) :
    (fun X : Path d => fun n => X n - x) ⁻¹' TransientPaths ℓ = TransientPaths ℓ := by
  ext X
  constructor
  · intro h
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [tendsto_atTop.mp h (b - dot (realPosition x) ℓ)] with n hn
    rw [dot_realPosition_sub] at hn
    linarith
  · intro h
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [tendsto_atTop.mp h (b + dot (realPosition x) ℓ)] with n hn
    rw [dot_realPosition_sub]
    linarith

lemma quenched_directionallyTransient_ae {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    ∀ᵐ ω ∂environmentLaw ν, ∀ x,
      ∀ᵐ X ∂quenchedKernel (ω, x), X ∈ TransientPaths ℓ := by
  apply ae_all_iff.mpr
  intro x
  have hm : MeasurableSet (TransientPaths ℓ)ᶜ := (measurableSet_transientPaths ℓ).compl
  have he (ω : Environment d) : quenchedKernel (ω, x) (TransientPaths ℓ)ᶜ =
      quenchedKernel ((fun a => ω (x + a)), 0) (TransientPaths ℓ)ᶜ := by
    have h := congrArg (fun μ : Measure (Path d) => μ (TransientPaths ℓ)ᶜ)
      (quenched_translation ω x 0)
    rw [Measure.map_apply (by fun_prop) hm, Set.preimage_compl,
      transientPaths_translation] at h
    simpa only [add_zero] using h
  have hz : (∫⁻ ω, quenchedKernel (ω, x) (TransientPaths ℓ)ᶜ ∂environmentLaw ν) = 0 := by
    simp_rw [he]
    have hm0 : Measurable (fun ω : Environment d => quenchedKernel (ω, 0) (TransientPaths ℓ)ᶜ) :=
      (Kernel.measurable_coe _ hm).comp (measurable_id.prodMk measurable_const)
    rw [← lintegral_map hm0 (show Measurable (fun ω : Environment d => fun a => ω (x + a)) by
      fun_prop), environment_translation]
    rw [← annealed_apply ν hm]
    exact ae_iff.mp htrans
  have hzero := (lintegral_eq_zero_iff ((Kernel.measurable_coe _ hm).comp
    (measurable_id.prodMk measurable_const))).mp hz
  filter_upwards [hzero] with ω hω
  exact ae_iff.mpr hω

lemma crossingQuenched_antitone {d : ℕ} (ℓ : Vector d) (x : Lattice d) (ω : Environment d) :
    Antitone (fun H => crossingQuenched ℓ x H ω) := by
  intro H K hHK
  exact measure_mono (cross_antitone ℓ x hHK)

lemma quenched_hitAt_congr {d : ℕ} (S T : Set (Lattice d))
    (ω η : Environment d) (hωη : Set.EqOn ω η S) (x : Lattice d) (n : ℕ) :
    quenchedKernel (ω, x) (HitAt S T n) = quenchedKernel (η, x) (HitAt S T n) := by
  let A : Set ((i : Finset.Iic n) → Lattice d) :=
    {f | f ⟨n, Finset.mem_Iic.mpr le_rfl⟩ ∈ T ∧ ∀ i : Finset.Iic n, (i : ℕ) < n → f i ∈ S}
  have hA : (fun X : Path d => Preorder.frestrictLe n X) ⁻¹' A = HitAt S T n := by
    ext X
    constructor
    · intro h
      exact ⟨h.1, fun i hi => h.2 ⟨i, Finset.mem_Iic.mpr hi.le⟩ hi⟩
    · intro h
      exact ⟨h.1, fun i hi => h.2 i hi⟩
  have hm (f : (i : Finset.Iic n) → Lattice d) (_ : f ∈ A) :
      MeasurableSet ((fun X : Path d => Preorder.frestrictLe n X) ⁻¹' {f}) :=
    (Preorder.measurable_frestrictLe n) (measurableSet_singleton f)
  rw [← hA, ← tsum_measure_preimage_singleton A.to_countable hm,
    ← tsum_measure_preimage_singleton A.to_countable hm]
  apply tsum_congr
  intro f
  rw [restrict_prefix_fiber]
  by_cases hf : extendPrefix n f.val 0 = x
  · rw [quenched_pathCylinder _ _ _ hf, quenched_pathCylinder _ _ _ hf]
    apply Finset.prod_congr rfl
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have hiS : extendPrefix n f.val i ∈ S := by
      rw [extendPrefix_apply _ _ _ hin.le]
      exact f.property.2 _ hin
    simp only [edgeWeight, hωη hiS]
  · rw [quenched_pathCylinder_zero _ _ _ hf, quenched_pathCylinder_zero _ _ _ hf]

lemma hitKernel_congr {d : ℕ} (S T : Set (Lattice d))
    (ω η : Environment d) (hωη : Set.EqOn ω η S) (x : Lattice d) :
    hitKernel S T (ω, x) = hitKernel S T (η, x) := by
  apply Measure.ext
  intro U _
  rw [hitKernel_apply, hitKernel_apply]
  exact tsum_congr fun n => quenched_hitAt_congr S (T ∩ U) ω η hωη x n

lemma measurable_hitKernel_rows {d : ℕ} (S T : Set (Lattice d)) (x : Lattice d) (hx : x ∈ S) :
    @Measurable _ _ (rowSigma S) _ (fun ω : Environment d => hitKernel S T (ω, x)) := by
  classical
  let patch : Environment d → Environment d := fun ω y => if y ∈ S then ω y else ω x
  have hp : @Measurable _ _ (rowSigma S) _ patch := by
    refine @Measurable.of_eval _ _ _ (rowSigma S) _ _ ?_
    intro y
    by_cases hy : y ∈ S
    · simpa only [patch, ite_eq_left hy] using measurable_row_on hy
    · simpa only [patch, ite_eq_right hy] using measurable_row_on hx
  have hm : Measurable (fun η : Environment d => hitKernel S T (η, x)) :=
    (hitKernel S T).measurable.comp (measurable_id.prodMk measurable_const)
  have he : (fun ω : Environment d => hitKernel S T (ω, x)) =
      (fun η : Environment d => hitKernel S T (η, x)) ∘ patch := by
    funext ω
    exact hitKernel_congr S T ω (patch ω) (fun y hy => by simp [patch, hy]) x
  rw [he]
  exact hm.comp hp

lemma crossingQuenched_eq_hitKernel {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (H : ℝ) (ω : Environment d) :
    crossingQuenched ℓ x H ω = hitKernel (Strip ℓ x H) (Upper ℓ x H) (ω, x) Set.univ := by
  rw [hitKernel_total (disjoint_strip_upper ℓ x H), crossingQuenched, cross_eq_hit]

lemma measurable_crossingQuenched_rows {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    {H : ℝ} (hH : 0 < H) :
    @Measurable _ _ (rowSigma (Strip ℓ x H)) _ (crossingQuenched ℓ x H) := by
  change @Measurable _ _ (rowSigma (Strip ℓ x H)) _ (fun ω => crossingQuenched ℓ x H ω)
  simp_rw [crossingQuenched_eq_hitKernel]
  exact (Measure.measurable_coe MeasurableSet.univ).comp
    (measurable_hitKernel_rows _ _ x ⟨le_rfl, by linarith⟩)

lemma crossingQuenched_zero {d : ℕ} (ℓ : Vector d) (x : Lattice d) (ω : Environment d) :
    crossingQuenched ℓ x 0 ω = 1 := by
  have he : Cross ℓ x 0 =ᵐ[quenchedKernel (ω, x)] Set.univ := by
    filter_upwards [quenched_initial_ae (ω, x)] with X hX
    apply propext
    change X ∈ Cross ℓ x 0 ↔ True
    refine ⟨fun _ => trivial, fun _ => ⟨0, ?_, by simp⟩⟩
    simp [hX]
  rw [crossingQuenched, measure_congr he, measure_univ]

noncomputable def endpointLaw {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ)
    (ω : Environment d) : Measure (Lattice d) :=
  (crossingQuenched ℓ x H ω)⁻¹ • hitKernel (Strip ℓ x H) (Upper ℓ x H) (ω, x)

lemma crossingQuenched_le_one {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) (ω : Environment d) :
    crossingQuenched ℓ x H ω ≤ 1 := prob_le_one

lemma crossingQuenched_ne_top {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) (ω : Environment d) :
    crossingQuenched ℓ x H ω ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) (crossingQuenched_le_one ℓ x H ω)

lemma endpointLaw_total {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) (ω : Environment d)
    (ha : crossingQuenched ℓ x H ω ≠ 0) : endpointLaw ℓ x H ω Set.univ = 1 := by
  rw [endpointLaw, Measure.smul_apply, smul_eq_mul, ← crossingQuenched_eq_hitKernel,
    ENNReal.inv_mul_cancel ha (crossingQuenched_ne_top ℓ x H ω)]

lemma endpointLaw_total_le_one {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) (ω : Environment d) :
    endpointLaw ℓ x H ω Set.univ ≤ 1 := by
  by_cases ha : crossingQuenched ℓ x H ω = 0
  · rw [endpointLaw, Measure.smul_apply, smul_eq_mul, ← crossingQuenched_eq_hitKernel, ha, mul_zero]
    exact zero_le
  · rw [endpointLaw_total ℓ x H ω ha]

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FirstBelow
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
attribute [-simp] _root_.OAI.DirectionalTransience.latticeVector_zero _root_.OAI.DirectionalTransience.recordCount_zero _root_.OAI.DirectionalTransience.regenerationTimes_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma measurable_endpointLaw_rows {d : ℕ} (ℓ : Vector d) (x : Lattice d) {H : ℝ} (hH : 0 < H)
    (U : Set (Lattice d)) :
    @Measurable _ _ (rowSigma (Strip ℓ x H)) _ (fun ω => endpointLaw ℓ x H ω U) := by
  simp only [endpointLaw, Measure.smul_apply, smul_eq_mul]
  exact (measurable_crossingQuenched_rows ℓ x hH).inv.mul
    ((Measure.measurable_coe U.to_countable.measurableSet).comp
      (measurable_hitKernel_rows _ _ x ⟨le_rfl, by linarith⟩))

lemma endpointLaw_supported {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ)
    (ω : Environment d) {y : Lattice d} (hy : y ∉ Upper ℓ x H) :
    endpointLaw ℓ x H ω {y} = 0 := by
  rw [endpointLaw, Measure.smul_apply, smul_eq_mul, hitKernel_apply]
  have he : Upper ℓ x H ∩ {y} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain rfl := hz.2
    exact hy hz.1
  rw [he]
  have he' (n : ℕ) : HitAt (Strip ℓ x H) ∅ n = ∅ := by
    ext X
    simp [HitAt]
  simp only [he', measure_empty, tsum_zero, mul_zero]

lemma measurableSet_firstBelow_crossing {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    {m : ℝ} (hm : 0 < m) (t : ℝ≥0∞) (n : ℕ) :
    MeasurableSet[rowSigma (Strip ℓ x (n * m))]
      {ω | FirstBelow (fun k => crossingQuenched ℓ x (k * m) ω) t n} := by
  have ha (k : ℕ) (hk : k ≤ n) :
      @Measurable _ _ (rowSigma (Strip ℓ x (n * m))) _ (crossingQuenched ℓ x (k * m)) := by
    by_cases hk0 : k = 0
    · subst k
      simp only [Nat.cast_zero, zero_mul]
      convert (measurable_const : @Measurable _ _ (rowSigma (Strip ℓ x (n * m))) _
        (fun _ : Environment d => (1 : ℝ≥0∞))) using 1
      all_goals try with_reducible_and_instances rfl
      funext ω
      exact crossingQuenched_zero ℓ x ω
    · apply (measurable_crossingQuenched_rows ℓ x (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0)) hm)).mono
        (rowSigma_mono ?_) le_rfl
      intro y hy
      refine ⟨hy.1, hy.2.trans_le ?_⟩
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) hm.le)
  change MeasurableSet[rowSigma (Strip ℓ x (n * m))]
    ({ω | crossingQuenched ℓ x (n * m) ω < t} ∩
      {ω | ∀ k < n, t ≤ crossingQuenched ℓ x (k * m) ω})
  apply MeasurableSet.inter (measurableSet_lt (ha n le_rfl) measurable_const)
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun hk =>
    measurableSet_le measurable_const (ha k hk.le)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_LowerClip
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
attribute [-simp] _root_.OAI.DirectionalTransience.recordCount_zero _root_.OAI.DirectionalTransience.regenerationTimes_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma exists_positive_step {d : ℕ} (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1) :
    ∃ e : Direction d, 0 < dot (realPosition (step e)) ℓ := by
  have hn : ∃ i, ℓ i ≠ 0 := by
    by_contra h
    push Not at h
    have hz : dot ℓ ℓ = 0 := by simp [dot, h]
    linarith
  obtain ⟨i, hi⟩ := hn
  rcases lt_or_gt_of_ne hi with hi | hi
  · refine ⟨(i, false), ?_⟩
    simpa [dot, realPosition, step] using neg_pos.mpr hi
  · refine ⟨(i, true), ?_⟩
    simpa [dot, realPosition, step] using hi

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_CoordinateStrip
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
attribute [-simp] _root_.OAI.DirectionalTransience.latticeVector_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma measurable_of_row_locality {d : ℕ} {α : Type*} [MeasurableSpace α]
    (f : Environment d → α) (hf : Measurable f) (S : Set (Lattice d))
    (x : Lattice d) (hx : x ∈ S)
    (hloc : ∀ ω η, Set.EqOn ω η S → f ω = f η) :
    @Measurable _ _ (rowSigma S) _ f := by
  classical
  let patch : Environment d → Environment d := fun ω y => if y ∈ S then ω y else ω x
  have hp : @Measurable _ _ (rowSigma S) _ patch := by
    refine @Measurable.of_eval _ _ _ (rowSigma S) _ _ ?_
    intro y
    by_cases hy : y ∈ S
    · simpa only [patch, ite_eq_left hy] using measurable_row_on hy
    · simpa only [patch, ite_eq_right hy] using measurable_row_on hx
  have he : f = f ∘ patch := by
    funext ω
    exact hloc ω (patch ω) (fun y hy => by simp [patch, hy])
  rw [he]
  exact hf.comp hp

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_HeightSlab
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma pathCylinder_weight_locality {d : ℕ} (S : Set (Lattice d))
    (ω η : Environment d) (hωη : Set.EqOn ω η S) (x : Lattice d)
    (f : Path d) (n : ℕ) (hf : ∀ j < n, f j ∈ S) :
    quenchedKernel (ω, x) (pathCylinder f n) =
      quenchedKernel (η, x) (pathCylinder f n) := by
  by_cases hfx : f 0 = x
  · rw [quenched_pathCylinder ω x f hfx, quenched_pathCylinder η x f hfx]
    exact Finset.prod_congr rfl fun j hj => by
      simp only [edgeWeight, hωη (hf j (Finset.mem_range.mp hj))]
  · rw [quenched_pathCylinder_zero ω x f hfx, quenched_pathCylinder_zero η x f hfx]

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_StrictRecord
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma measurableSet_strictRecord {d : ℕ} (ℓ : Vector d) (n : ℕ) :
    MeasurableSet {X : Path d | StrictRecord ℓ X n} := by
  simp only [StrictRecord, Set.ofPred_forall]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_lt
      ((measurable_of_countable (f := fun y : Lattice d => dot (realPosition y) ℓ)).comp
        (measurable_pi_apply j))
      ((measurable_of_countable (f := fun y : Lattice d => dot (realPosition y) ℓ)).comp
        (measurable_pi_apply n))

lemma strictRecord_congr_prefix {d : ℕ} (ℓ : Vector d) {X Y : Path d} {n m : ℕ}
    (hn : n ≤ m) (hXY : ∀ j ≤ m, X j = Y j) :
    StrictRecord ℓ X n ↔ StrictRecord ℓ Y n := by
  simp only [StrictRecord]
  constructor <;> intro h j hj
  · simpa only [hXY j (hj.le.trans hn), hXY n hn] using h j hj
  · simpa only [hXY j (hj.le.trans hn), hXY n hn] using h j hj

lemma conditionedLaw_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) :
    IsProbabilityMeasure (conditionedLaw ν ℓ) := by
  constructor
  simp only [conditionedLaw, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hp (measure_ne_top _ _)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Renewal_RegenerationWords
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
attribute [-simp] _root_.OAI.DirectionalTransience.latticeVector_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma recordCount_congr_prefix {d : ℕ} (ℓ : Vector d) {X Y : Path d} {n : ℕ}
    (hXY : ∀ j ≤ n, X j = Y j) : recordCount ℓ X n = recordCount ℓ Y n := by
  classical
  apply Finset.sum_congr rfl
  intro j hj
  rw [strictRecord_congr_prefix ℓ (by simpa using Finset.mem_range.mp hj) hXY]

open scoped Classical in
lemma recordCount_succ {d : ℕ} (ℓ : Vector d) (X : Path d) (n : ℕ) :
    recordCount ℓ X (n + 1) = recordCount ℓ X n +
      if StrictRecord ℓ X (n + 1) then 1 else 0 := by
  classical
  exact Finset.sum_range_succ (fun j => if StrictRecord ℓ X (j + 1) then 1 else 0) n

lemma recordCount_mono {d : ℕ} (ℓ : Vector d) (X : Path d) :
    Monotone (recordCount ℓ X) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [recordCount_succ]
  exact Nat.le_add_right _ _

lemma recordCount_lt_of_strictRecord {d : ℕ} (ℓ : Vector d) (X : Path d) {m n : ℕ}
    (hmn : m < n) (hn : StrictRecord ℓ X n) : recordCount ℓ X m < recordCount ℓ X n := by
  classical
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  rw [recordCount_succ, ite_eq_left hn]
  exact Nat.lt_succ_of_le (recordCount_mono ℓ X (by omega))

lemma measurable_recordCount {d : ℕ} (ℓ : Vector d) (n : ℕ) :
    Measurable (fun X : Path d => recordCount ℓ X n) := by
  classical
  apply Finset.measurable_fun_sum
  intro j _
  exact Measurable.ite (measurableSet_strictRecord ℓ (j+1)) measurable_const measurable_const

lemma measurableSet_recordIndexPrefix {d : ℕ} (ℓ : Vector d) (r n : ℕ) :
    MeasurableSet (RecordIndexPrefix ℓ r n) := by
  simp only [RecordIndexPrefix, Set.ofPred_and, Set.ofPred_forall]
  exact (MeasurableSet.const _).inter ((measurableSet_strictRecord ℓ n).inter
    ((measurableSet_eq_fun (measurable_recordCount ℓ n) measurable_const).inter
      (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
        measurableSet_le measurable_const
          ((measurable_of_countable (f := fun x : Lattice d => dot (realPosition x) ℓ)).comp
            (measurable_pi_apply j)))))

lemma recordIndexPrefix_disjoint {d : ℕ} (ℓ : Vector d) (r : ℕ) :
    Pairwise (fun m n => Disjoint (RecordIndexPrefix ℓ r m) (RecordIndexPrefix ℓ r n)) := by
  intro m n hmn
  apply Set.disjoint_left.mpr
  intro X hm hn
  rcases lt_or_gt_of_ne hmn with h | h
  · have := recordCount_lt_of_strictRecord ℓ X h hn.2.1
    rw [hm.2.2.1, hn.2.2.1] at this
    exact (lt_irrefl _) this
  · have := recordCount_lt_of_strictRecord ℓ X h hm.2.1
    rw [hm.2.2.1, hn.2.2.1] at this
    exact (lt_irrefl _) this

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_WordHeightGain
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma wordPath_step_or_stay {d : ℕ} (x : Lattice d) (w : List (Direction d)) (n : ℕ) :
    wordPath x w (n+1) = wordPath x w n ∨
      ∃ e : Direction d, wordPath x w (n+1) = wordPath x w n + step e := by
  induction w generalizing x n with
  | nil => exact Or.inl rfl
  | cons e w ih =>
    cases n with
    | zero => exact Or.inr ⟨e, by simp only [wordPath, wordPath_zero]⟩
    | succ n => exact ih (x + step e) n

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_FixedQuenchedKernel
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma signed_direction_unit {d : ℕ} (e : Direction d) :
    dot (realPosition (step e)) (realPosition (step e)) = 1 := by
  rw [dot_step]
  simp only [realPosition,step,ite_true, if_true,Int.cast_ite,Int.cast_one,Int.cast_neg]
  cases e.2 <;> norm_num

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonTrueRecord
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

def commonPairSuffix {d : ℕ} (n m : ℕ) (P : Path d × Path d) : Path d × Path d :=
  ((fun j => P.1 (n+j)), (fun j => P.2 (m+j)))

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_IndependentPairLaw
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

noncomputable def independentPairLaw {d : ℕ} (ν : Measure (Row d)) : Measure (Path d × Path d) :=
  (annealedLaw ν).prod (annealedLaw ν)

instance independentPairLaw_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (independentPairLaw ν) := inferInstanceAs
      (IsProbabilityMeasure ((annealedLaw ν).prod (annealedLaw ν)))

lemma independentConditionedPairLaw_probability {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) :
    IsProbabilityMeasure (independentConditionedPairLaw ν ℓ) := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ hp
  exact inferInstanceAs (IsProbabilityMeasure ((conditionedLaw ν ℓ).prod (conditionedLaw ν ℓ)))

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FixedPairSuffix
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

def fixedPairSuffix {d : ℕ} (wv : List (Direction d) × List (Direction d))
    (P : Path d × Path d) : Path d × Path d :=
  ((fun j => P.1 (wv.1.length+j) - wordPath 0 wv.1 wv.1.length),
   (fun j => P.2 (wv.2.length+j) - wordPath 0 wv.2 wv.2.length))

noncomputable def commonTimes {d : ℕ} (ℓ : Vector d) (P : Path d × Path d) (n : ℕ) : ℕ × ℕ :=
  (∑ i ∈ Finset.range n, (commonWords ℓ P i).1.length,
   ∑ i ∈ Finset.range n, (commonWords ℓ P i).2.length)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonWordWidth
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma singleCommonIndex_exists_bound {d : ℕ} (ℓ : Vector d) (P : Path d × Path d) :
    ∃ n, (firstPairWord ℓ P).1.length ≤ regenerationTimes ℓ P.1 n ∨
      (firstPairWord ℓ P).1.length < n :=
  ⟨(firstPairWord ℓ P).1.length+1,Or.inr (Nat.lt_succ_self _)⟩

open scoped Classical in
noncomputable def singleCommonIndex {d : ℕ} (ℓ : Vector d) (P : Path d × Path d) : ℕ :=
  Nat.find (singleCommonIndex_exists_bound ℓ P)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SymmetricTruncate
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma signedCoordinate_sub {d : ℕ} (e : Direction d) (x y : Lattice d) :
    signedCoordinate e (x-y) = signedCoordinate e x - signedCoordinate e y := by
  simp only [signedCoordinate, Pi.sub_apply, Int.cast_sub]
  split <;> ring

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RecordIndexTime
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma recordIndexTime_eq {d : ℕ} (ℓ : Vector d) (r n : ℕ) (X : Path d)
    (hX : X ∈ RecordIndexPrefix ℓ r n) : recordIndexTime ℓ r X = n := by
  classical
  have hex : ∃ n, X ∈ RecordIndexPrefix ℓ r n := ⟨n,hX⟩
  rw [recordIndexTime,dite_eq_left hex]
  by_contra h
  exact Set.disjoint_left.mp (recordIndexPrefix_disjoint ℓ r h) (Nat.find_spec hex) hX

lemma measurable_recordIndexTime {d : ℕ} (ℓ : Vector d) (r : ℕ) :
    Measurable (recordIndexTime ℓ r) := by
  classical
  apply measurable_to_countable'
  intro n
  have he : {X : Path d | recordIndexTime ℓ r X = n} =
      RecordIndexPrefix ℓ r n ∪
        (if n = 0 then (⋃ m, RecordIndexPrefix ℓ r m)ᶜ else ∅) := by
    ext X
    simp only [Set.mem_ofPred_eq]
    by_cases hx : ∃ m, X ∈ RecordIndexPrefix ℓ r m
    · obtain ⟨m,hm⟩ := hx
      rw [recordIndexTime_eq ℓ r m X hm]
      by_cases hn : n = m
      · subst n
        simp only [Set.mem_union,true_iff]
        exact Or.inl hm
      · have hnot : X ∉ RecordIndexPrefix ℓ r n :=
          fun hn' => Set.disjoint_left.mp (recordIndexPrefix_disjoint ℓ r hn) hn' hm
        have hnot' : X ∈ ⋃ j, RecordIndexPrefix ℓ r j := Set.mem_iUnion.mpr ⟨m,hm⟩
        simp only [Ne.symm hn,false_iff,Set.mem_union]
        rintro (h | h)
        · exact hnot h
        · split_ifs at h
          · exact h hnot'
          · exact h
    · have hm : X ∉ ⋃ m, RecordIndexPrefix ℓ r m := by simpa only [Set.mem_iUnion] using hx
      have hn : X ∉ RecordIndexPrefix ℓ r n := fun h => hx ⟨n,h⟩
      by_cases hn0 : n = 0
      · subst n
        simp only [recordIndexTime,dite_eq_right hx,Set.mem_union,true_iff]
        exact Or.inr hm
      · simp [recordIndexTime,hx,hn,hn0,Ne.symm hn0]
  change MeasurableSet {X : Path d | recordIndexTime ℓ r X = n}
  rw [he]
  exact (measurableSet_recordIndexPrefix ℓ r n).union (by
    split_ifs
    · exact (MeasurableSet.iUnion fun m => measurableSet_recordIndexPrefix ℓ r m).compl
    · exact MeasurableSet.empty)

lemma measurable_recordIndexPosition {d : ℕ} (ℓ : Vector d) (r : ℕ) :
    Measurable (recordIndexPosition ℓ r) :=
  (measurable_from_prod_countable_left
    (f := fun q : Path d × ℕ => q.1 q.2) (fun n => measurable_pi_apply n)).comp
      (measurable_id.prodMk (measurable_recordIndexTime ℓ r))

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_IntegerMedian
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

def signedIntegerCoordinate {d : ℕ} (e : Direction d) (x : Lattice d) : ℤ :=
  if e.2 then x e.1 else -x e.1

noncomputable def recordMedian {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) (e : Direction d) (r : ℕ) : ℤ := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ hp
  let f : Path d → ℤ := fun X => signedIntegerCoordinate e (recordIndexPosition ℓ r X)
  have hf : Measurable f := (measurable_of_countable (signedIntegerCoordinate e)).comp (measurable_recordIndexPosition ℓ r)
  let : IsProbabilityMeasure ((conditionedLaw ν ℓ).map f) :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).mpr inferInstance
  exact integerMedian ((conditionedLaw ν ℓ).map f)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_PathCompact
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

noncomputable def pathCompact (R : ℝ) (δ : ℕ → ℝ) : Set C(unitInterval,ℝ) :=
  {f | ‖f‖ ≤ R} ∩ ⋂ m : ℕ, (ContinuousOscillation (1/(m+1)) (δ m))ᶜ

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_AlignedRecordPrefix
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma measurableSet_recordOrZeroPrefix {d : ℕ} (ℓ : Vector d) (r n : ℕ) :
    MeasurableSet (RecordOrZeroPrefix ℓ r n) := by
  unfold RecordOrZeroPrefix
  split_ifs
  · exact MeasurableSet.const _
  · exact measurableSet_recordIndexPrefix ℓ r n

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_DirectBridge
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def directBridge {d : ℕ} (e : Direction d) (μ : Measure (Lattice d))
    (ω : Environment d) : Measure (Lattice d) :=
  Measure.sum fun y => (((ω y).1 e : ℝ≥0∞)*μ {y}) • Measure.dirac (y+step e)

noncomputable def probabilityNormalize {α : Type*} [MeasurableSpace α] (μ : Measure α) (x : α) : Measure α :=
  if μ Set.univ = 0 then Measure.dirac x else normalizedMeasure μ

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SurvivingLane
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def SurvivingLane {d : ℕ} (U T A : Set (Lattice d)) : Set (Path d) :=
  Stay U ∩ Hit (U \ T) (T ∩ A)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RecordMedianSlope
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def recordMedianSlope {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) (f : Direction d) (a : ℝ) : ℝ :=
  (recordMedian ν ℓ hp f ⌊fluctuationScale (independentConditionedPairLaw ν ℓ)
    (commonIncrementProcess ℓ f 0) a⌋₊ : ℝ) /
      ⌊fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) a⌋₊

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_WeightedAnnealed
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def weightedAnnealed {d : ℕ} (ν : Measure (Row d))
    (g : Environment d → ℝ≥0∞) : Measure (Path d) :=
  ((environmentLaw ν).withDensity g).bind (fun ω => quenchedKernel (ω,0))

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_WeightedConditioned
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def weightedConditioned {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (g : Environment d → ℝ≥0∞) : Measure (Path d) :=
  (annealedLaw ν (NoDrop ℓ 0))⁻¹ • (weightedAnnealed ν g).restrict (NoDrop ℓ 0)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_RecordLinearPath
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def recordLinearPath {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r n T : ℝ) (X : Path d) : C(unitInterval,ℝ) :=
  heightPolygon (fun h => signedCoordinate f (recordIndexPosition ℓ h X)-(h:ℝ)*θ) r n T

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_GaussianAbsTail
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def scaledRecordEndpoint {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r : ℝ) (k : ℕ) (x : Lattice d) (X : Path d) : ℝ :=
  (signedCoordinate f (recordIndexPosition ℓ k (fun j => X j-x))-(k:ℝ)*θ)/r

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RawConditionedWeight
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def rawConditionedWeight {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (g : Environment d → ℝ≥0∞) : Measure (Path d) :=
  (weightedAnnealed ν g).restrict (NoDrop ℓ 0)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SuccessfulAverage
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma measurable_crossingQuenched {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) :
    Measurable (crossingQuenched ℓ x H) :=
  (Kernel.measurable_coe quenchedKernel (measurableSet_cross ℓ x H)).comp
    (measurable_id.prodMk measurable_const)

noncomputable def successfulAverage {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d) (H : ℝ) :
    Measure (Path d) :=
  (weightedAnnealed ν (fun ω => (crossingQuenched ℓ 0 H ω)⁻¹)).restrict (Cross ℓ 0 H)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_MixtureSmallMassProbability
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def relativeGoodMass {d : ℕ} (ℓ : Vector d) (A : Set (Path d))
    (ω : Environment d) (x : Lattice d) : ℝ :=
  (quenchedKernel (ω,x)).real (((fun X : Path d => fun n => X n-x) ⁻¹' Aᶜ) ∩ NoDrop ℓ x)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_HitWord
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def hitWordsEvent {d : ℕ} (x y : Lattice d) (S T : Set (Lattice d))
    (E : Set (HitWord x S T × HitWord y S T)) : Set (Path d × Path d) :=
  ⋃ w ∈ E, wordCylinder x w.1.val ×ˢ wordCylinder y w.2.val

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_VisibleFailure
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def VisibleFailure {d : ℕ} (height : Lattice d → ℤ) (h B : ℤ) : Set (Path d) :=
  {X | ∃ a b c, X ∈ FirstLayerHit height h a ∧
    X ∈ FirstLayerHit height (h+B) c ∧ a ≤ b ∧ b < c ∧ height (X b) < h}

def VisibleHistory {d : ℕ} (height : Lattice d → ℤ) (H B : ℤ) (m : ℕ) : Set (Path d × Path d) :=
  {P | ∀ j < m, P.1 ∈ VisibleFailure height (H+j*B) B ∨ P.2 ∈ VisibleFailure height (H+j*B) B}

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonOffset
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma commonOffset_exists {d : ℕ} (ℓ : Vector d) (height : Lattice d → ℤ)
    (H : ℤ) (P : Path d × Path d) :
    ∃ n : ℕ, P ∈ CommonLayer ℓ height (H+n) ∨ ¬ ∃ k : ℕ, P ∈ CommonLayer ℓ height (H+k) := by
  by_cases hh : ∃ k : ℕ, P ∈ CommonLayer ℓ height (H+k)
  · obtain ⟨k,hk⟩ := hh
    exact ⟨k,Or.inl hk⟩
  · exact ⟨0,Or.inr hh⟩

noncomputable def commonOffset {d : ℕ} (ℓ : Vector d) (height : Lattice d → ℤ)
    (H : ℤ) (P : Path d × Path d) : ℕ := Nat.find (commonOffset_exists ℓ height H P)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CappedMomentTransfer
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

noncomputable def medianDeviation {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b : ℕ → ℝ) : ℕ → Path d → ℝ
  | 0, X => |signedCoordinate f (recordIndexPosition ℓ 0 X)-b 0|
  | H+1, X => max (medianDeviation ℓ f b H X)
      |signedCoordinate f (recordIndexPosition ℓ (H+1) X)-b (H+1)|

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CurvePrefix
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma measurableSet_curvePrefixAt {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (z : ℝ) (s n : ℕ) : MeasurableSet (CurvePrefixAt ℓ f x b z s n) := by
  apply (measurableSet_hitAt _ _ n).inter
  simp only [Set.ofPred_forall,Set.ofPred_exists,Set.ofPred_and]
  apply MeasurableSet.iInter; intro j
  apply MeasurableSet.iInter; intro _
  apply MeasurableSet.iUnion; intro a
  refine (MeasurableSet.const (a ≤ n)).inter ?_
  have hm : Measurable (fun X : Path d => fun k => X k-x) := by fun_prop
  have hc : Measurable (fun X : Path d => signedCoordinate f (X a-x)) :=
    (measurable_of_countable (signedCoordinate f)).comp
      ((measurable_pi_apply a : Measurable (fun X : Path d => X a)).sub_const x)
  exact ((measurableSet_recordOrZeroPrefix ℓ j a).preimage hm).inter
    (measurableSet_le ((hc.sub_const (b j)).abs) measurable_const)

lemma curvePrefixAt_disjoint {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (z : ℝ) (s : ℕ) : Pairwise (fun n m =>
      Disjoint (CurvePrefixAt ℓ f x b z s n) (CurvePrefixAt ℓ f x b z s m)) := by
  intro n m hnm
  exact (hitAt_pairwise_disjoint (disjoint_strip_upper ℓ x s) hnm).mono
    Set.inter_subset_left Set.inter_subset_left

noncomputable def curveEndpoint {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (z : ℝ) (s : ℕ) (ω : Environment d) : Measure (Lattice d) :=
  Measure.sum fun n => ((quenchedKernel (ω,x)).restrict (CurvePrefixAt ℓ f x b z s n)).map (fun X => X n)

lemma curveEndpoint_apply {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (z : ℝ) (s : ℕ) (ω : Environment d) (U : Set (Lattice d)) :
    curveEndpoint ℓ f x b z s ω U = ∑' n, quenchedKernel (ω,x)
      ((fun X => X n) ⁻¹' U ∩ CurvePrefixAt ℓ f x b z s n) := by
  rw [curveEndpoint,Measure.sum_apply _ U.to_countable.measurableSet]
  apply tsum_congr; intro n
  rw [Measure.map_apply (measurable_pi_apply n) U.to_countable.measurableSet,
    Measure.restrict_apply ((measurable_pi_apply n) U.to_countable.measurableSet)]

lemma curveEndpoint_total {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (z : ℝ) (s : ℕ) (ω : Environment d) :
    curveEndpoint ℓ f x b z s ω Set.univ = quenchedKernel (ω,x) (CurvePrefix ℓ f x b z s) := by
  rw [curveEndpoint_apply,CurvePrefix,measure_iUnion (curvePrefixAt_disjoint ℓ f x b z s)
    (measurableSet_curvePrefixAt ℓ f x b z s)]
  simp only [Set.preimage_univ,Set.univ_inter]

instance curveEndpoint_finite {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (z : ℝ) (s : ℕ) (ω : Environment d) : IsFiniteMeasure (curveEndpoint ℓ f x b z s ω) :=
  ⟨by rw [curveEndpoint_total]; exact measure_lt_top _ _⟩

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_SelectedFiniteKernel
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma selectedFiniteKernel_probability {α : Type*} [MeasurableSpace α]
    (D : Measure α) [IsFiniteMeasure D] (E : Set α) (dummy : α) (failure strict : Prop)
    [Decidable failure] [Decidable strict]
    (hD : ¬failure → D Set.univ ≠ 0) (hE : ¬failure → strict → D E ≠ 0) :
    IsProbabilityMeasure (selectedFiniteKernel D E dummy failure strict) := by
  by_cases hf : failure
  · simp only [selectedFiniteKernel,ite_eq_left hf]; infer_instance
  simp only [selectedFiniteKernel,ite_eq_right hf]
  by_cases hs : strict
  · simp only [ite_eq_left hs]
    apply normalizeFinite_probability
    · simpa using hE hf hs
    · exact measure_ne_top _ _
  · simp only [ite_eq_right hs]
    exact normalizeFinite_probability D (hD hf) (measure_ne_top _ _)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CurvePolicy
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

noncomputable def curveIncrement {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (ω : Environment d) : Measure (Lattice d) :=
  (curveEndpoint ℓ f x b B H ω).map (fun y => y-x)

instance curveIncrement_finite {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (ω : Environment d) :
    IsFiniteMeasure (curveIncrement ℓ f x b B H ω) := by
  unfold curveIncrement; infer_instance

lemma curveIncrement_total {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (ω : Environment d) :
    curveIncrement ℓ f x b B H ω Set.univ = quenchedKernel (ω,x) (CurvePrefix ℓ f x b B H) := by
  rw [curveIncrement,Measure.map_apply (measurable_of_countable _) MeasurableSet.univ,
    Set.preimage_univ,curveEndpoint_total]

lemma curveIncrement_le_crossing {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (ω : Environment d) :
    curveIncrement ℓ f x b B H ω Set.univ ≤ crossingQuenched ℓ x H ω := by
  rw [curveIncrement_total,crossingQuenched,cross_eq_hit]
  apply measure_mono
  intro X hX
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hX
  exact Set.mem_iUnion.mpr ⟨n,hn.1⟩

noncomputable def curvePolicy {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (E : Set (Lattice d))
    (δ α : ℝ≥0∞) (dummy : Lattice d) (ω : Environment d) : Measure (Lattice d) :=
  selectedFiniteKernel (curveIncrement ℓ f x b B H ω) E dummy
    (curveIncrement ℓ f x b B H ω Set.univ < δ)
    (α * crossingQuenched ℓ x H ω ≤ curveIncrement ℓ f x b B H ω E)

lemma curvePolicy_probability {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (E : Set (Lattice d))
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (dummy : Lattice d) (ω : Environment d) :
    IsProbabilityMeasure (curvePolicy ℓ f x b B H E δ α dummy ω) := by
  apply selectedFiniteKernel_probability
  · intro hf
    exact ne_of_gt (lt_of_lt_of_le hδ (not_lt.mp hf))
  · intro hf hs
    have ha : 0 < crossingQuenched ℓ x H ω :=
      lt_of_lt_of_le (lt_of_lt_of_le hδ (not_lt.mp hf))
        (curveIncrement_le_crossing ℓ f x b B H ω)
    exact ne_of_gt ((ENNReal.mul_pos hα.ne' ha.ne').trans_le hs)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_QuenchedMoments
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction

namespace DirectionalTransience

noncomputable def medianFirstHitPath {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν] (ℓ : Vector d)
    (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) (f : Direction d) (x : Lattice d)
    (r n T : ℝ) (X : Path d) : C(unitInterval,ℝ) :=
  heightPolygon (fun h => signedCoordinate f
    (recordIndexPosition ℓ h (fun j => X j-x))-(recordMedian ν ℓ hp f h:ℝ)) r n T

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_AlignedSlabs
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma signedHeight_add {d : ℕ} (e : Direction d) (x y : Lattice d) :
    signedHeight e (x+y) = signedHeight e x+signedHeight e y := by
  simp only [signedHeight,Pi.add_apply]
  split <;> omega

lemma signedHeight_zsmul_step {d : ℕ} (e : Direction d) (a : ℤ) :
    signedHeight e (a • step e) = a := by
  simp only [signedHeight,Pi.smul_apply,smul_eq_mul,step,ite_true, if_true]
  split <;> simp_all

noncomputable def alignHeight {d : ℕ} (e : Direction d) (a : ℤ) (x : Lattice d) : Lattice d :=
  x+(a-signedHeight e x) • step e

def blockRows {d : ℕ} (e : Direction d) (H i : ℕ) : Set (Lattice d) :=
  {x | (i:ℤ)*H ≤ signedHeight e x ∧ signedHeight e x < (i:ℤ)*H+H}

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CurvePolicyPMF
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

noncomputable def curvePolicyPMF {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x : Lattice d) (b : ℕ → ℝ) (B : ℝ) (H : ℕ) (E : Set (Lattice d))
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (dummy : Lattice d) (ω : Environment d) : PMF (Lattice d) :=
  let := curvePolicy_probability ℓ f x b B H E hδ hα dummy ω
  (curvePolicy ℓ f x b B H E δ α dummy ω).toPMF

noncomputable def alignedCurvePolicy {d : ℕ} (e f : Direction d) (b : ℕ → ℝ)
    (B : ℝ) (H : ℕ) (E : Set (Lattice d)) {δ α : ℝ≥0∞}
    (hδ : 0 < δ) (hα : 0 < α) (dummy : Lattice d) (i : ℕ) (ω : Environment d) (x : Lattice d) : PMF (Lattice d) :=
  curvePolicyPMF (realPosition (step e)) f (alignHeight e ((i:ℤ)*H) x) b B H E hδ hα dummy ω

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

local instance instMeasurableSpaceListLattice {d : ℕ} : MeasurableSpace (List (Lattice d)) := ⊤

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CurvePolicyAverageMoment
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience
noncomputable def medianDummy {d : ℕ} (e f : Direction d) (H : ℕ) (b : ℤ) : Lattice d :=
  (H:ℤ) • step e+b • step f
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CurvePolicyMaximal
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def priorRows {d : ℕ} (S : ℕ → Set (Lattice d)) (t : ℕ) : Set (Lattice d) :=
  ⋃ j ∈ Set.Iio t, S j

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RecordPairFuture
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def recordPairFuture {d : ℕ} (n m : ℕ) (B : Lattice d → Lattice d → Set (Path d × Path d)) :
    Set (Path d × Path d) := {P | commonPairSuffix n m P ∈ B (P.1 n) (P.2 m)}

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonBoundaryRestart
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

def truePairCylinder {d : ℕ} (ℓ : Vector d) (f g : Path d) (n m : ℕ) :
    Set (Path d × Path d) :=
  (pathCylinder f n ×ˢ pathCylinder g m) ∩ (FutureNoDrop ℓ n ×ˢ FutureNoDrop ℓ m)

def boundaryAtom {d : ℕ} (ℓ : Vector d) (H : ℝ) (x y : Lattice d)
    (f g : Path d) (n m : ℕ) : Set (Path d × Path d) :=
  (pathCylinder f n ×ˢ pathCylinder g m) ∩
    ((NoDrop ℓ x ×ˢ NoDrop ℓ y) ∩ {P | BoundaryAt ℓ H P n m})

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_JointPastRestart
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

instance instCountableBoundaryData {d : ℕ} : Countable (BoundaryData d) := by unfold BoundaryData; infer_instance
instance instMeasurableSpaceBoundaryData {d : ℕ} : MeasurableSpace (BoundaryData d) := ⊤
instance instDiscreteMeasurableSpaceBoundaryData {d : ℕ} : DiscreteMeasurableSpace (BoundaryData d) := ⟨fun _ => trivial⟩

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RealJointPastRestart
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

def boundaryTerminal {d : ℕ} (F : BoundaryData d) : Lattice d × Lattice d :=
  (extendPrefix F.1.1 F.2.1 F.1.1,extendPrefix F.1.2 F.2.2 F.1.2)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SharedEndpointTests
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def centeredFirstHit {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r : ℝ) (k : ℕ) (x : Lattice d) (X : Path d) : ℝ :=
  (signedCoordinate f (recordIndexPosition ℓ k (fun j => X j-x))-(k:ℝ)*θ)/r

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BoundarySuffixIdentity
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def centeredHitIncrement {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r : ℝ) (H k : ℕ) (x : Lattice d) (X : Path d) : ℝ :=
  (signedCoordinate f (recordIndexPosition ℓ (H+k) (fun j => X j-x))-
    signedCoordinate f (recordIndexPosition ℓ H (fun j => X j-x))-(k:ℝ)*θ)/r

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_FinitePastCoordinates
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def boundaryPrefixPair {d : ℕ} (D : BoundaryData d) : Path d × Path d :=
  (extendPrefix D.1.1 D.2.1, extendPrefix D.1.2 D.2.2)

noncomputable def centeredPastCoordinates {d q : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r : ℝ) (j : Fin q → ℕ) (x y : Lattice d) (P : Path d × Path d) : Fin q → ℝ × ℝ :=
  fun a => (centeredFirstHit ℓ f θ r (j a) x P.1, centeredFirstHit ℓ f θ r (j a) y P.2)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FinitePastDecorrelation
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def sharedLinearPairPath {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r n T : ℝ) (x y : Lattice d) (P : Path d × Path d) : RealPathPair :=
  (recordLinearPath ℓ f θ r n T (fun j => P.1 j-x),
    recordLinearPath ℓ f θ r n T (fun j => P.2 j-y))

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_OffDiagonalCenteredCross
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def centeredClipCross {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r : ℝ) (H : ℕ) (w : ℝ≥0) (x y : Lattice d) (P : Path d × Path d) : ℝ :=
  symmetricClip w (centeredFirstHit ℓ f θ r H x P.1)*
    symmetricClip w (centeredFirstHit ℓ f θ r H y P.2)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SelectedBoundaryRestart
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

def selectedBoundaryAt {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop) (P : Path d × Path d)
    (n m : ℕ) : Prop :=
  0 < n ∧ 0 < m ∧ CommonTrueRecord ℓ P n m ∧
    B (P.1 n,P.2 m) ∧
    ∀ j k, 0 < j → j < n → 0 < k → k < m →
      B (P.1 j,P.2 k) → ¬ CommonTrueRecord ℓ P j k

def selectedAdmissibleBoundaryPrefix {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop) (x y : Lattice d)
    (f g : Path d) (n m : ℕ) : Prop :=
  0 < n ∧ 0 < m ∧
    dot (realPosition (f n)) ℓ = dot (realPosition (g m)) ℓ ∧
    StrictRecord ℓ f n ∧ StrictRecord ℓ g m ∧
    (∀ j ≤ n, dot (realPosition x) ℓ ≤ dot (realPosition (f j)) ℓ) ∧
    (∀ k ≤ m, dot (realPosition y) ℓ ≤ dot (realPosition (g k)) ℓ) ∧
    B (f n,g m) ∧
    ∀ j k, 0 < j → j < n → 0 < k → k < m →
      B (f j,g k) → StrictRecord ℓ f j → StrictRecord ℓ g k →
      dot (realPosition (f j)) ℓ = dot (realPosition (g k)) ℓ →
      (∃ a, j < a ∧ a < n ∧ dot (realPosition (f a)) ℓ < dot (realPosition (f j)) ℓ) ∨
      (∃ b, k < b ∧ b < m ∧ dot (realPosition (g b)) ℓ < dot (realPosition (g k)) ℓ)

lemma selectedBoundaryCode_exists {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop) (P : Path d × Path d) :
    ∃ a : ℕ, selectedBoundaryAt ℓ B P (Nat.unpair a).1 (Nat.unpair a).2 ∨
      ¬ ∃ n m, selectedBoundaryAt ℓ B P n m := by
  by_cases h : ∃ n m, selectedBoundaryAt ℓ B P n m
  · obtain ⟨n,m,hnm⟩ := h
    exact ⟨Nat.pair n m,Or.inl (by simpa only [Nat.unpair_pair] using hnm)⟩
  · exact ⟨0,Or.inr h⟩

noncomputable def selectedBoundaryCode {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop) (P : Path d × Path d) : ℕ :=
  Nat.find (selectedBoundaryCode_exists ℓ B P)

noncomputable def selectedBoundaryTimes {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop) (P : Path d × Path d) : ℕ × ℕ :=
  Nat.unpair (selectedBoundaryCode ℓ B P)

def selectedBoundaryAtom {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop) (x y : Lattice d)
    (f g : Path d) (n m : ℕ) : Set (Path d × Path d) :=
  (pathCylinder f n ×ˢ pathCylinder g m) ∩
    ((NoDrop ℓ x ×ˢ NoDrop ℓ y) ∩ {P | selectedBoundaryAt ℓ B P n m})

noncomputable def selectedBoundarySuffix {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop) (P : Path d × Path d) :
    Path d × Path d := commonPairSuffix (selectedBoundaryTimes ℓ B P).1 (selectedBoundaryTimes ℓ B P).2 P

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_CommonCutObserver
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

def pairOrigin {d : ℕ} (P : Path d × Path d) : Lattice d × Lattice d := (P.1 0,P.2 0)

noncomputable def commonCutObserver {d : ℕ} (ℓ : Vector d)
    (active : Lattice d × Lattice d → Prop)
    (B : (Lattice d × Lattice d) → (Lattice d × Lattice d) → Prop)
    (P : Path d × Path d) : Path d × Path d :=
  if active (pairOrigin P) then selectedBoundarySuffix ℓ (B (pairOrigin P)) P else P

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_LowerObservedCut
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

def lowerCutCriterion {d : ℕ} (e f : Direction d) (h : ℤ) (b : ℝ) (K : ℕ)
    (uv : Lattice d × Lattice d) : Prop :=
  2*b ≤ |signedCoordinate f (uv.1-uv.2)| ∨ h+K ≤ signedHeight e uv.1

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ObservedDrift
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

def pairGap {d : ℕ} (f : Direction d) (i : Lattice d × Lattice d) : ℝ :=
  |signedCoordinate f (i.1-i.2)|

noncomputable def observedAdvanceRule {d : ℕ} (e f : Direction d) (b : ℝ)
    (K : ℕ) (k : ℝ → ℕ) (i uv : Lattice d × Lattice d) : Prop :=
  if pairGap f i ≤ b then lowerCutCriterion e f (signedHeight e i.1) b K uv else
    ((signedHeight e i.1+k (pairGap f i) : ℤ) : ℝ) ≤ dot (realPosition uv.1) (realPosition (step e))

noncomputable def observedAdvanceBound {d : ℕ} (f : Direction d) (b : ℝ)
    (K : ℕ) (k : ℝ → ℕ) (i : Lattice d × Lattice d) : ℕ :=
  if pairGap f i ≤ b then K else k (pairGap f i)

noncomputable def observedStatePotential {d : ℕ} (f : Direction d) (b R : ℝ)
    (i : Lattice d × Lattice d) : ℝ := observedPotential b R (signedCoordinate f (i.1-i.2))

noncomputable def observedStateGain {d : ℕ} (f : Direction d) (b R c q : ℝ)
    (i : Lattice d × Lattice d) : ℝ :=
  if pairGap f i<R then
    if pairGap f i≤b then q*((2*b)^((3:ℝ)/2)-b^((3:ℝ)/2)) else c*(pairGap f i)^((3:ℝ)/2)
  else 0

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ObservedBudget
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

def SmallCommonLayer {d : ℕ} (e f : Direction d) (s : ℝ) (H : ℤ) :
    Set (Path d × Path d) :=
  {P | ∃ n m, P.1 ∈ FirstLayerHit (signedHeight e) H n ∧
    P.2 ∈ FirstLayerHit (signedHeight e) H m ∧
    P.1 ∈ FutureNoDrop (realPosition (step e)) n ∧
    P.2 ∈ FutureNoDrop (realPosition (step e)) m ∧
    |signedCoordinate f (P.1 n-P.2 m)| ≤ s}

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_CommonCutCounting
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

noncomputable def smallCommonCount {d : ℕ} (e f : Direction d) (s : ℝ) (H : ℕ)
    (P : Path d × Path d) : ℕ :=
  ∑ j ∈ Finset.range H, if P ∈ SmallCommonLayer e f s (signedHeight e (P.1 0)+j) then 1 else 0

def ValidObservation {d : ℕ} (e f : Direction d) (b R : ℝ) (K : ℕ) (k : ℝ → ℕ)
    (P : Path d × Path d) : Prop :=
  signedHeight e (P.1 0)=signedHeight e (P.2 0) ∧
  P.1 ∈ NoDrop (realPosition (step e)) (P.1 0) ∧
  P.2 ∈ NoDrop (realPosition (step e)) (P.2 0) ∧
  (∀ n, ∃ g, P.1 (n+1)=P.1 n+step g) ∧
  (∀ n, ∃ g, P.2 (n+1)=P.2 n+step g) ∧
  (pairGap f (pairOrigin P) < R →
    selectedBoundaryAt (realPosition (step e)) (observedAdvanceRule e f b K k (pairOrigin P)) P
      (selectedBoundaryTimes (realPosition (step e)) (observedAdvanceRule e f b K k (pairOrigin P)) P).1
      (selectedBoundaryTimes (realPosition (step e)) (observedAdvanceRule e f b K k (pairOrigin P)) P).2)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_GaussianQuenchedTube
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

def medianTubeEndpoint {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) (f : Direction d)
    (x : Lattice d) (H : ℕ) (L R : ℝ) : Set (Path d) :=
  {X | heightTubeEndpointEvent (fun j => signedCoordinate f
    (recordIndexPosition ℓ j (fun k => X k-x))-(recordMedian ν ℓ hp f j:ℝ)) H L R}

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_ClippedPairGrowth
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
noncomputable def jumpPrefixMass {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b a s : ℝ) (H : ℕ) (ω : Environment d) (x : Lattice d) : ℝ :=
  (quenchedKernel (ω,x)).real (EndpointPrefix ℓ x H {z | a < s*(signedCoordinate f (z-x)-b)})
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RawPairLocality
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma rawPairEndpointLaw_rows {d : ℕ} (ℓ : Vector d) (x : Lattice d × Lattice d)
    {H : ℕ} (hH : 0 < H) {S : Set (Lattice d)}
    (h₁ : Strip ℓ x.1 H ⊆ S) (h₂ : Strip ℓ x.2 H ⊆ S) :
    @Measurable _ _ (rowSigma S) _ (fun ω => rawPairEndpointLaw ℓ H ω x) := by
  have hx (y : Lattice d) : y ∈ Strip ℓ y H := ⟨le_rfl,by exact lt_add_of_pos_right _ (by exact_mod_cast hH)⟩
  let : MeasurableSpace (Environment d) := rowSigma S
  let κ₁ : Kernel (Environment d) (Lattice d) :=
    ⟨fun ω => hitKernel (Strip ℓ x.1 H) (Upper ℓ x.1 H) (ω,x.1),
      (measurable_hitKernel_rows _ _ _ (hx x.1)).mono (rowSigma_mono h₁) le_rfl⟩
  let κ₂ : Kernel (Environment d) (Lattice d) :=
    ⟨fun ω => hitKernel (Strip ℓ x.2 H) (Upper ℓ x.2 H) (ω,x.2),
      (measurable_hitKernel_rows _ _ _ (hx x.2)).mono (rowSigma_mono h₂) le_rfl⟩
  have : @IsFiniteKernel (Environment d) (Lattice d) (rowSigma S) _ κ₁ :=
    ⟨⟨1,ENNReal.one_lt_top,fun ω => hitKernel_total_le_one (disjoint_strip_upper ℓ x.1 H) (ω,x.1)⟩⟩
  have : @IsFiniteKernel (Environment d) (Lattice d) (rowSigma S) _ κ₂ :=
    ⟨⟨1,ENNReal.one_lt_top,fun ω => hitKernel_total_le_one (disjoint_strip_upper ℓ x.2 H) (ω,x.2)⟩⟩
  have hm := (κ₁.prod κ₂).measurable
  change @Measurable _ _ (rowSigma S) _ (fun ω => (κ₁ ω).prod (κ₂ ω))
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext ω
  exact (Kernel.prod_apply κ₁ κ₂ ω).symm

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma supportedPairMeasures_singleton {d : ℕ} (C : Set (Lattice d × Lattice d))
    (π : SupportedPairMeasures C) {x : Lattice d × Lattice d} (hx : x ∉ C) : π.val {x} = 0 := by
  apply le_antisymm _ (by positivity)
  calc
    π.val {x} ≤ π.val Cᶜ := measure_mono (Set.singleton_subset_iff.mpr hx)
    _ = 0 := π.property

lemma pairKernelMass_joint_rows {d : ℕ} (ℓ : Vector d) (f : Direction d)
    {H : ℕ} (hH : 0 < H) (z : ℝ) (C : Set (Lattice d × Lattice d))
    (S : Set (Lattice d))
    (hC : ∀ x ∈ C, Strip ℓ x.1 H ⊆ S ∧ Strip ℓ x.2 H ⊆ S) :
    @Measurable (SupportedPairMeasures C × Environment d) ℝ≥0∞
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S)) _
      (fun p => pairKernelMass ℓ f H z p.1.val p.2) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  simp only [pairKernelMass,lintegral_countable']
  apply Measurable.tsum
  intro x
  by_cases hx : x ∈ C
  · have hm : @Measurable (SupportedPairMeasures C × Environment d) ℝ≥0∞ _ _
        (fun p => rawPairEndpointLaw ℓ H p.2 x {y | z ≤ signedCoordinate f (y.2-y.1)}) :=
      ((Measure.measurable_coe (Set.to_countable _).measurableSet).comp
        (rawPairEndpointLaw_rows ℓ x hH (hC x hx).1 (hC x hx).2)).comp measurable_snd
    exact hm.mul ((Measure.measurable_coe (measurableSet_singleton x)).comp
      (measurable_subtype_coe.comp measurable_fst))
  · have he : (fun p : SupportedPairMeasures C × Environment d =>
        rawPairEndpointLaw ℓ H p.2 x {y | z ≤ signedCoordinate f (y.2-y.1)}*p.1.val {x}) =
        fun _ => 0 := by
      funext p
      rw [supportedPairMeasures_singleton C p.1 hx,mul_zero]
    rw [he]
    exact measurable_const
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RawPairRetention
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def rawPairMixture {d : ℕ} (ℓ : Vector d) (H : ℕ)
    (π : Measure (Lattice d × Lattice d)) (ω : Environment d) : Measure (Lattice d × Lattice d) :=
  π.bind (rawPairEndpointLaw ℓ H ω)

lemma rawPairMixture_apply {d : ℕ} (ℓ : Vector d) (H : ℕ)
    (π : Measure (Lattice d × Lattice d)) (ω : Environment d) (U : Set (Lattice d × Lattice d)) :
    rawPairMixture ℓ H π ω U = ∫⁻ x, rawPairEndpointLaw ℓ H ω x U ∂π :=
  Measure.bind_apply (Set.to_countable U).measurableSet (measurable_of_countable _).aemeasurable

noncomputable def retainedPairLaw {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (H : ℕ) (z : ℝ) (π : Measure (Lattice d × Lattice d)) (ω : Environment d) :
    Measure (Lattice d × Lattice d) :=
  (rawPairMixture ℓ H π ω).restrict {y | z ≤ signedCoordinate f (y.2-y.1)}

lemma retainedPairLaw_le {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (H : ℕ) (z : ℝ) (π : Measure (Lattice d × Lattice d)) (ω : Environment d) :
    retainedPairLaw ℓ f H z π ω ≤ rawPairMixture ℓ H π ω := Measure.restrict_le_self

lemma rawPairMixture_joint_rows {d : ℕ} (ℓ : Vector d)
    {H : ℕ} (hH : 0 < H) (C : Set (Lattice d × Lattice d)) (S : Set (Lattice d))
    (hC : ∀ x ∈ C, Strip ℓ x.1 H ⊆ S ∧ Strip ℓ x.2 H ⊆ S) :
    @Measurable (SupportedPairMeasures C × Environment d) (Measure (Lattice d × Lattice d))
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S)) _
      (fun p => rawPairMixture ℓ H p.1.val p.2) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  apply Measure.measurable_of_measurable_coe
  intro U hU
  simp only [rawPairMixture_apply,lintegral_countable']
  apply Measurable.tsum
  intro x
  by_cases hx : x ∈ C
  · have hm : @Measurable (SupportedPairMeasures C × Environment d) ℝ≥0∞ _ _
        (fun p => rawPairEndpointLaw ℓ H p.2 x U) :=
      ((Measure.measurable_coe hU).comp
        (rawPairEndpointLaw_rows ℓ x hH (hC x hx).1 (hC x hx).2)).comp measurable_snd
    exact hm.mul ((Measure.measurable_coe (measurableSet_singleton x)).comp
      (measurable_subtype_coe.comp measurable_fst))
  · have he : (fun p : SupportedPairMeasures C × Environment d =>
        rawPairEndpointLaw ℓ H p.2 x U*p.1.val {x}) = fun _ => 0 := by
      funext p
      rw [supportedPairMeasures_singleton C p.1 hx,mul_zero]
    rw [he]
    exact measurable_const

lemma retainedPairLaw_joint_rows {d : ℕ} (ℓ : Vector d) (f : Direction d)
    {H : ℕ} (hH : 0 < H) (z : ℝ) (C : Set (Lattice d × Lattice d)) (S : Set (Lattice d))
    (hC : ∀ x ∈ C, Strip ℓ x.1 H ⊆ S ∧ Strip ℓ x.2 H ⊆ S) :
    @Measurable (SupportedPairMeasures C × Environment d) (Measure (Lattice d × Lattice d))
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S)) _
      (fun p => retainedPairLaw ℓ f H z p.1.val p.2) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  apply Measure.measurable_of_measurable_coe
  intro U hU
  simp only [retainedPairLaw,Measure.restrict_apply hU]
  exact (Measure.measurable_coe (hU.inter (Set.to_countable _).measurableSet)).comp
    (rawPairMixture_joint_rows ℓ hH C S hC)
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma measurable_normalizedMeasure {α : Type*} [MeasurableSpace α] :
    Measurable (normalizedMeasure (α := α)) := by
  apply Measure.measurable_of_measurable_coe
  intro U hU
  simp only [normalizedMeasure,Measure.smul_apply,smul_eq_mul]
  exact (Measure.measurable_coe MeasurableSet.univ).inv.mul (Measure.measurable_coe hU)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma strip_mono_nat_height {d : ℕ} (ℓ : Vector d) (x : Lattice d) {h H : ℕ} (hh : h ≤ H) :
    Strip ℓ x h ⊆ Strip ℓ x H := by
  intro y hy
  have hhR : (h:ℝ) ≤ H := by exact_mod_cast hh
  exact ⟨hy.1,by dsimp [Strip] at hy ⊢ <;> linarith [hy.2]⟩

lemma measurableSet_bufferStageEvent_rows {d : ℕ} (ℓ : Vector d) (f : Direction d)
    {H : ℕ} (hH : 0 < H) (z₀ r ε a g : ℝ) (C : Set (Lattice d × Lattice d))
    (S : Set (Lattice d))
    (hC : ∀ x ∈ C, Strip ℓ x.1 H ⊆ S ∧ Strip ℓ x.2 H ⊆ S) :
    @MeasurableSet (SupportedPairMeasures C × Environment d)
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S))
      {p | BufferStageEvent ℓ f H z₀ r ε a g p.1.val p.2} := by
  let : MeasurableSpace (Environment d) := rowSigma S
  unfold BufferStageEvent
  apply MeasurableSet.inter
  · change MeasurableSet {p : SupportedPairMeasures C × Environment d | ∀ h : ℕ, 0 < h → h ≤ H → ENNReal.ofReal g ≤ pairKernelMass ℓ f h (z₀+(1-ε)*r) p.1.val p.2}
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro h
    apply MeasurableSet.iInter
    intro hh
    apply MeasurableSet.iInter
    intro hhH
    exact measurableSet_le measurable_const (pairKernelMass_joint_rows ℓ f hh _ C S
      (fun x hx => ⟨(strip_mono_nat_height ℓ x.1 hhH).trans (hC x hx).1,
        (strip_mono_nat_height ℓ x.2 hhH).trans (hC x hx).2⟩))
  · exact measurableSet_le measurable_const (pairKernelMass_joint_rows ℓ f hH _ C S hC)
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_FreshBufferAE
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def pairLawValidSet {d : ℕ} (f : Direction d) (z : ℝ) {C : Set (Lattice d × Lattice d)}
    (π : Environment d → SupportedPairMeasures C) : Set (Environment d) :=
  {ω | (π ω).val Set.univ=1 ∧ (π ω).val {x | ¬ z ≤ signedCoordinate f (x.2-x.1)}=0}

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_TupleEndpoint
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

instance rawTupleEndpointLaw_finite {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Fin k → Lattice d) :
    IsFiniteMeasure (rawTupleEndpointLaw ℓ H ω x) := by
  unfold rawTupleEndpointLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SuccessfulWords
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma hitWordEvent_univ_ae {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S T : Set (Lattice d)) :
    hitWordEvent x S T Set.univ =ᵐ[quenchedKernel (ω,x)] Hit S T := by
  filter_upwards [quenched_initial_ae (ω,x), quenched_nearest_neighbor (ω,x)] with X h0 hnn
  apply propext
  change X ∈ hitWordEvent x S T Set.univ ↔ X ∈ Hit S T
  rw [hitWord_cover x S T X h0 hnn]
  simp only [hitWordEvent,Set.mem_iUnion,Subtype.exists,Set.mem_univ,exists_true_left]

lemma successfulWordLaw_univ {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S T : Set (Lattice d)) (hST : Disjoint S T) :
    successfulWordLaw ω x S T Set.univ = quenchedKernel (ω,x) (Hit S T) := by
  rw [successfulWordLaw_event ω x S T hST]
  exact measure_congr (hitWordEvent_univ_ae ω x S T)

lemma successfulWordLaw_le_one {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S T : Set (Lattice d)) (hST : Disjoint S T) :
    successfulWordLaw ω x S T Set.univ ≤ 1 := by
  rw [successfulWordLaw_univ ω x S T hST]
  exact prob_le_one

lemma successfulWordLaw_finite {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S T : Set (Lattice d)) (hST : Disjoint S T) :
    IsFiniteMeasure (successfulWordLaw ω x S T) :=
  ⟨lt_of_le_of_lt (successfulWordLaw_le_one ω x S T hST) ENNReal.one_lt_top⟩

instance rawWordLaw_finite {d : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Lattice d) : IsFiniteMeasure (rawWordLaw ℓ H ω x) := by
  let := successfulWordLaw_finite ω x (Strip ℓ x H) (Upper ℓ x H) (disjoint_strip_upper _ _ _)
  exact Measure.isFiniteMeasure_map _ _

noncomputable def rawTupleWordLaw {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Fin k → Lattice d) : Measure (Fin k → List (Direction d)) :=
  Measure.pi (fun j => rawWordLaw ℓ H ω (x j))

instance rawTupleWordLaw_finite {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Fin k → Lattice d) : IsFiniteMeasure (rawTupleWordLaw ℓ H ω x) := by
  unfold rawTupleWordLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma rawTupleWordLaw_singleton {d k : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Fin k → Lattice d) (w : Fin k → List (Direction d)) :
    rawTupleWordLaw ℓ H ω x {w} = ∏ j, rawWordLaw ℓ H ω (x j) {w j} := by
  exact Measure.pi_singleton _ _

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_FiniteWordGeometry
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma wordPath_append_prefix {d : ℕ} (x : Lattice d) (u v : List (Direction d))
    {n : ℕ} (hn : n ≤ u.length) : wordPath x (u ++ v) n = wordPath x u n := by
  induction u generalizing x n with
  | nil =>
    have : n = 0 := by simpa using hn
    simp [this]
  | cons e u ih =>
    cases n with
    | zero => simp
    | succ n =>
      simpa only [List.cons_append,wordPath] using ih (x+step e) (Nat.le_of_succ_le_succ hn)

lemma wordPath_append_suffix {d : ℕ} (x : Lattice d) (u v : List (Direction d))
    (n : ℕ) : wordPath x (u ++ v) (u.length+n) = wordPath (wordPath x u u.length) v n := by
  induction u generalizing x with
  | nil => simp [wordPath]
  | cons e u ih =>
    simpa only [List.cons_append,List.length_cons,Nat.succ_add,wordPath] using ih (x+step e)

lemma wordPath_height_step {d : ℕ} (e : Direction d) (x : Lattice d)
    (w : List (Direction d)) (n : ℕ) :
    signedHeight e (wordPath x w (n+1)) ≤ signedHeight e (wordPath x w n)+1 := by
  rcases wordPath_step_or_stay x w n with h | ⟨g,h⟩
  · rw [h]; omega
  · rw [h]; exact signedHeight_step_le e _ g

lemma wordPath_hit_exact {d : ℕ} (e : Direction d) (x : Lattice d) (H : ℕ)
    (w : HitWord x (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H)) :
    signedHeight e (wordPath x w.val w.val.length) = signedHeight e x + H := by
  have htop : signedHeight e x + H ≤ signedHeight e (wordPath x w.val w.val.length) := by
    have h := w.property.1
    change dot (realPosition x) (realPosition (step e))+(H:ℝ) ≤
      dot (realPosition (wordPath x w.val w.val.length)) (realPosition (step e)) at h
    rw [signedHeight_projection,signedHeight_projection] at h
    exact_mod_cast h
  apply le_antisymm _ htop
  cases hlen : w.val.length with
  | zero => simpa only [hlen,wordPath_zero] using (show signedHeight e x ≤ signedHeight e x+H by omega)
  | succ n =>
    have h := (w.property.2 n (by omega)).2
    change dot (realPosition (wordPath x w.val n)) (realPosition (step e)) <
      dot (realPosition x) (realPosition (step e))+(H:ℝ) at h
    rw [signedHeight_projection,signedHeight_projection] at h
    have hn : signedHeight e (wordPath x w.val n) < signedHeight e x+H := by exact_mod_cast h
    have hs := wordPath_height_step e x w.val n
    omega

lemma wordFirstHitTime_spec {d : ℕ} (e : Direction d) (x : Lattice d)
    (s : ℕ) (w : List (Direction d))
    (h : ∃ n, signedHeight e x+s ≤ signedHeight e (wordPath x w n)) :
    signedHeight e x+s ≤ signedHeight e (wordFirstHitPosition e x s w) := by
  simp only [wordFirstHitPosition,wordFirstHitTime,dite_eq_left h]
  exact Nat.find_spec h

lemma wordFirstHitTime_le {d : ℕ} (e : Direction d) (x : Lattice d)
    (s : ℕ) (w : List (Direction d)) {n : ℕ}
    (h : signedHeight e x+s ≤ signedHeight e (wordPath x w n)) :
    wordFirstHitTime e x s w ≤ n := by
  simp only [wordFirstHitTime,dite_eq_left (show ∃ n, signedHeight e x+s ≤ signedHeight e (wordPath x w n) from ⟨n,h⟩)]
  exact Nat.find_min' _ h

lemma wordFirstHitTime_min {d : ℕ} (e : Direction d) (x : Lattice d)
    (s : ℕ) (w : List (Direction d)) {n : ℕ} (hn : n < wordFirstHitTime e x s w) :
    signedHeight e (wordPath x w n) < signedHeight e x+s := by
  by_contra h
  exact (wordFirstHitTime_le e x s w (le_of_not_gt h)).not_gt hn

lemma wordFirstHitTime_endpoint {d : ℕ} (e : Direction d) (x : Lattice d) (H : ℕ)
    (w : HitWord x (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H)) :
    wordFirstHitTime e x H w.val = w.val.length := by
  have hh : signedHeight e x+(H:ℤ) ≤ signedHeight e (wordPath x w.val w.val.length) :=
    (wordPath_hit_exact e x H w).ge
  apply le_antisymm (wordFirstHitTime_le e x H w.val hh)
  by_contra h
  have hn : wordFirstHitTime e x H w.val < w.val.length := by omega
  have hp := (w.property.2 _ hn).2
  change dot (realPosition (wordFirstHitPosition e x H w.val)) (realPosition (step e)) <
    dot (realPosition x) (realPosition (step e))+(H:ℝ) at hp
  rw [signedHeight_projection,signedHeight_projection] at hp
  have hp' : signedHeight e (wordFirstHitPosition e x H w.val) < signedHeight e x+H := by exact_mod_cast hp
  exact hp'.not_ge (wordFirstHitTime_spec e x H w.val ⟨w.val.length,hh⟩)

lemma coordinate_mem_strip_iff {d : ℕ} (e : Direction d) (x y : Lattice d) (H : ℕ) :
    y ∈ Strip (realPosition (step e)) x H ↔
      signedHeight e x ≤ signedHeight e y ∧ signedHeight e y < signedHeight e x+H := by
  simp only [Strip,Set.mem_ofPred_eq,signedHeight_projection]
  constructor
  · rintro ⟨h1,h2⟩
    constructor
    · exact_mod_cast h1
    · exact_mod_cast h2
  · rintro ⟨h1,h2⟩
    constructor
    · exact_mod_cast h1
    · exact_mod_cast h2

lemma coordinate_mem_upper_iff {d : ℕ} (e : Direction d) (x y : Lattice d) (H : ℕ) :
    y ∈ Upper (realPosition (step e)) x H ↔ signedHeight e x+H ≤ signedHeight e y := by
  simp only [Upper,Set.mem_ofPred_eq,signedHeight_projection]
  constructor <;> intro h <;> exact_mod_cast h

lemma wordPath_hit_append {d : ℕ} (e : Direction d) (x : Lattice d) (h m : ℕ)
    (u : HitWord x (Strip (realPosition (step e)) x h) (Upper (realPosition (step e)) x h))
    (v : HitWord (wordPath x u.val u.val.length)
      (Strip (realPosition (step e)) (wordPath x u.val u.val.length) m)
      (Upper (realPosition (step e)) (wordPath x u.val u.val.length) m)) :
    wordPath x (u.val++v.val) ∈ HitAt (Strip (realPosition (step e)) x ((h+m : ℕ) : ℝ))
      (Upper (realPosition (step e)) x ((h+m : ℕ) : ℝ)) (u.val++v.val).length := by
  have hy := wordPath_hit_exact e x h u
  constructor
  · rw [List.length_append,wordPath_append_suffix,coordinate_mem_upper_iff,
      wordPath_hit_exact e _ m v,hy,Nat.cast_add]
    omega
  · intro n hn
    rw [coordinate_mem_strip_iff]
    by_cases hu : n < u.val.length
    · rw [wordPath_append_prefix x u.val v.val hu.le]
      have hp := (coordinate_mem_strip_iff e x (wordPath x u.val n) h).mp (u.property.2 n hu)
      constructor
      · exact hp.1
      · push_cast; omega
    · have he : n = u.val.length+(n-u.val.length) := by omega
      rw [he,wordPath_append_suffix]
      have hv : n-u.val.length < v.val.length := by simp only [List.length_append] at hn; omega
      have hp := (coordinate_mem_strip_iff e _ _ m).mp (v.property.2 _ hv)
      rw [hy] at hp
      constructor <;> push_cast <;> omega

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_WordConcatenation
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

def coordinateSplitFirst {d : ℕ} (e : Direction d) (x : Lattice d) (h m : ℕ)
    (p : CoordinateSplit e x h m) : CoordinateWord e x h := ⟨p.val.1,p.property.1⟩

def coordinateSplitSecond {d : ℕ} (e : Direction d) (x : Lattice d) (h m : ℕ)
    (p : CoordinateSplit e x h m) : CoordinateWord e (wordPath x p.val.1 p.val.1.length) m :=
  ⟨p.val.2,p.property.2⟩

def coordinateWordConcat {d : ℕ} (e : Direction d) (x : Lattice d) (h m : ℕ)
    (p : CoordinateSplit e x h m) : CoordinateWord e x (h+m) :=
  ⟨p.val.1++p.val.2,wordPath_hit_append e x h m (coordinateSplitFirst e x h m p)
    (coordinateSplitSecond e x h m p)⟩

noncomputable def rawWordPairLaw {d : ℕ} (e : Direction d) (h m : ℕ)
    (ω : Environment d) (x : Lattice d) : Measure (List (Direction d) × List (Direction d)) :=
  (rawWordLaw (realPosition (step e)) h ω x).bind (fun u =>
    (rawWordLaw (realPosition (step e)) m ω (wordPath x u u.length)).map (fun v => (u,v)))

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RelativeBudget
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

def TupleRelativeBudget {d k : ℕ} (e f : Direction d) (x : Fin k → Lattice d)
    (H : ℕ) (r : ℝ) (w : Fin k → List (Direction d)) : Prop :=
  ∀ s ≤ H, ∀ i j, |relativeWordDisplacement e f (x i) s (w i) -
    relativeWordDisplacement e f (x j) s (w j)| ≤ r

def tupleWordEndpoint {d k : ℕ} (x : Fin k → Lattice d)
    (w : Fin k → List (Direction d)) : Fin k → Lattice d :=
  fun j => wordPath (x j) (w j) (w j).length

lemma relativeWordDisplacement_endpoint {d : ℕ} (e f : Direction d) (x : Lattice d)
    (H : ℕ) (w : HitWord x (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H)) :
    relativeWordDisplacement e f x H w.val = signedCoordinate f (wordPath x w.val w.val.length - x) := by
  unfold relativeWordDisplacement wordFirstHitPosition
  rw [wordFirstHitTime_endpoint]

lemma tupleRelativeBudget_separation {d k : ℕ} (e f : Direction d) (x : Fin k → Lattice d)
    (H : ℕ) (G r : ℝ)
    (w : ∀ j, HitWord (x j) (Strip (realPosition (step e)) (x j) H) (Upper (realPosition (step e)) (x j) H))
    (hG : TupleSeparated f G x)
    (hw : TupleRelativeBudget e f x H r (fun j => (w j).val)) :
    TupleSeparated f (G-r) (tupleWordEndpoint x (fun j => (w j).val)) := by
  intro i j hij
  have hb := hw H le_rfl i j
  rw [relativeWordDisplacement_endpoint e f (x i) H (w i),
    relativeWordDisplacement_endpoint e f (x j) H (w j)] at hb
  apply sub_le_iff_le_add.mpr
  change G ≤ |signedCoordinate f (wordPath (x i) (w i).val (w i).val.length) -
    signedCoordinate f (wordPath (x j) (w j).val (w j).val.length)| + r
  calc
    G ≤ |signedCoordinate f (x i)-signedCoordinate f (x j)| := hG i j hij
    _ = |(signedCoordinate f (wordPath (x i) (w i).val (w i).val.length) -
        signedCoordinate f (wordPath (x j) (w j).val (w j).val.length)) -
      (signedCoordinate f (wordPath (x i) (w i).val (w i).val.length - x i) -
        signedCoordinate f (wordPath (x j) (w j).val (w j).val.length - x j))| := by
          simp only [signedCoordinate_sub]; congr 1; ring
    _ ≤ _ := (abs_sub _ _).trans (add_le_add le_rfl hb)

noncomputable def relativeBudgetWordLaw {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (ω : Environment d) (x : Fin k → Lattice d) :
    Measure (Fin k → List (Direction d)) :=
  (rawTupleWordLaw (realPosition (step e)) H ω x).restrict {w | TupleRelativeBudget e f x H r w}

noncomputable def relativeBudgetEndpointLaw {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (ω : Environment d) (x : Fin k → Lattice d) :
    Measure (Fin k → Lattice d) :=
  (relativeBudgetWordLaw e f H r ω x).map (tupleWordEndpoint x)

instance relativeBudgetWordLaw_finite {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (ω : Environment d) (x : Fin k → Lattice d) :
    IsFiniteMeasure (relativeBudgetWordLaw e f H r ω x) := by
  unfold relativeBudgetWordLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance relativeBudgetEndpointLaw_finite {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (ω : Environment d) (x : Fin k → Lattice d) :
    IsFiniteMeasure (relativeBudgetEndpointLaw e f H r ω x) := by
  unfold relativeBudgetEndpointLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience
namespace TupleKernel

lemma restrict_singleton {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : Measure A) (S : Set A) (a : A) :
    μ.restrict S {a} = if a ∈ S then μ {a} else 0 := by
  rw [Measure.restrict_apply (measurableSet_singleton a)]
  by_cases ha : a ∈ S
  · rw [ite_eq_left ha,Set.singleton_inter_of_mem ha]
  · rw [ite_eq_right ha,Set.singleton_inter_of_notMem ha,measure_empty]

end TupleKernel

noncomputable def rawTupleSplitLaw {d k : ℕ} (e : Direction d) (h m : ℕ)
    (ω : Environment d) (x : Fin k → Lattice d) :
    Measure ((Fin k → List (Direction d)) × (Fin k → List (Direction d))) :=
  TupleKernel.dependentPair (rawTupleWordLaw (realPosition (step e)) h ω x)
    (fun u => rawTupleWordLaw (realPosition (step e)) m ω (tupleWordEndpoint x u))

def ValidTupleSplit {d k : ℕ} (e : Direction d) (x : Fin k → Lattice d) (h m : ℕ)
    (p : (Fin k → List (Direction d)) × (Fin k → List (Direction d))) : Prop :=
  ∀ j, ValidWordSplit e (x j) h m (p.1 j,p.2 j)

def tupleWordConcat {d k : ℕ}
    (p : (Fin k → List (Direction d)) × (Fin k → List (Direction d))) : Fin k → List (Direction d) :=
  fun j => p.1 j++p.2 j

noncomputable def relativeBudgetSplitLaw {d k : ℕ} (e f : Direction d) (h m : ℕ)
    (r q : ℝ) (ω : Environment d) (x : Fin k → Lattice d) :
    Measure ((Fin k → List (Direction d)) × (Fin k → List (Direction d))) :=
  TupleKernel.dependentPair (relativeBudgetWordLaw e f h r ω x)
    (fun u => relativeBudgetWordLaw e f m q ω (tupleWordEndpoint x u))

lemma relativeBudgetWordLaw_singleton {d k : ℕ} (e f : Direction d) (H : ℕ)
    (r : ℝ) (ω : Environment d) (x : Fin k → Lattice d) (w : Fin k → List (Direction d)) :
    relativeBudgetWordLaw e f H r ω x {w} =
      if TupleRelativeBudget e f x H r w then rawTupleWordLaw (realPosition (step e)) H ω x {w} else 0 := by
  exact TupleKernel.restrict_singleton _ _ _

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BudgetClipping
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma rawWordLaw_le_one {d : ℕ} (ℓ : Vector d) (H : ℕ)
    (ω : Environment d) (x : Lattice d) : rawWordLaw ℓ H ω x Set.univ ≤ 1 := by
  rw [rawWordLaw, Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Set.preimage_univ]
  exact successfulWordLaw_le_one ω x _ _ (disjoint_strip_upper _ _ _)

lemma relativeBudgetWordLaw_le_one {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (ω : Environment d) (x : Fin k → Lattice d) :
    relativeBudgetWordLaw e f H r ω x Set.univ ≤ 1 := by
  calc
    _ ≤ rawTupleWordLaw (realPosition (step e)) H ω x Set.univ := Measure.restrict_le_self _
    _ = ∏ j, rawWordLaw (realPosition (step e)) H ω (x j) Set.univ := Measure.pi_univ _
    _ ≤ 1 := Finset.prod_le_one' (fun j _ => rawWordLaw_le_one _ _ _ _)

noncomputable def relativeBudgetMass {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (π : Measure (Fin k → Lattice d)) (ω : Environment d) : ℝ :=
  ∫ x, (relativeBudgetWordLaw e f H r ω x).real Set.univ ∂π

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BufferFirstFailure
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def bufferTraversalMass {d : ℕ} (ℓ : Vector d) (f : Direction d) (a z : ℝ)
    (π : Environment d → SupportedPairMeasures (PairAtHeight ℓ a)) (h : ℕ) (ω : Environment d) : ℝ≥0∞ :=
  if h=0 then 1 else pairKernelMass ℓ f h z (π ω).val ω

lemma bufferTraversalMass_adapted {d : ℕ} (ℓ : Vector d) (f : Direction d) (a z : ℝ)
    (π : Environment d → SupportedPairMeasures (PairAtHeight ℓ a))
    (hπ : @Measurable _ _ (rowSigma (BelowHeight ℓ a)) _ π) :
    Adapted (rowHeightFiltration ℓ a) (bufferTraversalMass ℓ f a z π) := by
  intro h
  by_cases hh : h=0
  · simp only [hh]
    exact measurable_const
  · have hhpos : 0 < h := Nat.pos_of_ne_zero hh
    have hle : rowSigma (BelowHeight ℓ a) ≤ rowSigma (BelowHeight ℓ (a+h)) := by
      apply rowSigma_mono
      intro y hy
      dsimp [BelowHeight] at hy ⊢
      have : (0:ℝ) ≤ h := Nat.cast_nonneg h
      linarith
    have hC (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight ℓ a) :
        Strip ℓ x.1 h ⊆ BelowHeight ℓ (a+h) ∧ Strip ℓ x.2 h ⊆ BelowHeight ℓ (a+h) := by
      constructor
      · intro y hy
        change dot (realPosition y) ℓ < a+h
        simpa only [hx.1] using hy.2
      · intro y hy
        change dot (realPosition y) ℓ < a+h
        simpa only [hx.2] using hy.2
    have hp : @Measurable _ _ (rowSigma (BelowHeight ℓ (a+h))) _ π := hπ.mono hle le_rfl
    have hm := (pairKernelMass_joint_rows ℓ f hhpos z (PairAtHeight ℓ a)
      (BelowHeight ℓ (a+h)) hC).comp (hp.prodMk measurable_id)
    change @Measurable _ _ (rowSigma (BelowHeight ℓ (a+h))) _ _
    unfold bufferTraversalMass
    simp only [ite_eq_right hh]
    exact hm

noncomputable def bufferFirstFailure {d : ℕ} (ℓ : Vector d) (f : Direction d) (a z g : ℝ)
    (π : Environment d → SupportedPairMeasures (PairAtHeight ℓ a)) (H : ℕ) : Environment d → ℕ :=
  hittingBtwn (bufferTraversalMass ℓ f a z π) (Set.Iio (ENNReal.ofReal g)) 1 H

lemma bufferFirstFailure_stopping {d : ℕ} (ℓ : Vector d) (f : Direction d) (a z g : ℝ)
    (π : Environment d → SupportedPairMeasures (PairAtHeight ℓ a))
    (hπ : @Measurable _ _ (rowSigma (BelowHeight ℓ a)) _ π) (H : ℕ) :
    IsStoppingTime (rowHeightFiltration ℓ a) (fun ω => (bufferFirstFailure ℓ f a z g π H ω : WithTop ℕ)) :=
  (bufferTraversalMass_adapted ℓ f a z π hπ).isStoppingTime_hittingBtwn measurableSet_Iio

lemma bufferFirstFailure_bounds {d : ℕ} (ℓ : Vector d) (f : Direction d) (a z g : ℝ)
    (π : Environment d → SupportedPairMeasures (PairAtHeight ℓ a)) {H : ℕ} (hH : 0 < H)
    (ω : Environment d) : 1 ≤ bufferFirstFailure ℓ f a z g π H ω ∧
      bufferFirstFailure ℓ f a z g π H ω ≤ H :=
  hittingBtwn_mem_Icc hH ω

lemma before_bufferFirstFailure_pass {d : ℕ} (ℓ : Vector d) (f : Direction d) (a z g : ℝ)
    (π : Environment d → SupportedPairMeasures (PairAtHeight ℓ a)) (H : ℕ)
    (ω : Environment d) {j : ℕ} (hj : 0 < j) (hjlt : j < bufferFirstFailure ℓ f a z g π H ω) :
    ENNReal.ofReal g ≤ pairKernelMass ℓ f j z (π ω).val ω := by
  have hn := notMem_of_lt_hittingBtwn hjlt hj
  simpa only [bufferTraversalMass,ite_eq_right (Nat.ne_of_gt hj),Set.mem_Iio,not_lt] using hn

lemma bufferFirstFailure_fails_of_lt {d : ℕ} (ℓ : Vector d) (f : Direction d) (a z g : ℝ)
    (π : Environment d → SupportedPairMeasures (PairAtHeight ℓ a)) {H : ℕ} (hH : 0 < H)
    (ω : Environment d) (hlt : bufferFirstFailure ℓ f a z g π H ω < H) :
    pairKernelMass ℓ f (bufferFirstFailure ℓ f a z g π H ω) z (π ω).val ω < ENNReal.ofReal g := by
  have hn := hittingBtwn_mem_set_of_hittingBtwn_lt hlt
  change bufferTraversalMass ℓ f a z π (bufferFirstFailure ℓ f a z g π H ω) ω < ENNReal.ofReal g at hn
  have hp := (bufferFirstFailure_bounds ℓ f a z g π hH ω).1
  simpa only [bufferTraversalMass,ite_eq_right (by omega : bufferFirstFailure ℓ f a z g π H ω ≠ 0),Set.mem_Iio] using hn
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BudgetAdapted
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def relativeBudgetMassENN {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (π : Measure (Fin k → Lattice d)) (ω : Environment d) : ℝ≥0∞ :=
  ∫⁻ x, relativeBudgetWordLaw e f H r ω x Set.univ ∂π

lemma relativeBudgetMassENN_le_one {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (π : Measure (Fin k → Lattice d)) [IsProbabilityMeasure π]
    (ω : Environment d) : relativeBudgetMassENN e f H r π ω ≤ 1 := by
  calc
    _ ≤ ∫⁻ _ : Fin k → Lattice d, (1:ℝ≥0∞) ∂π :=
      lintegral_mono fun x => relativeBudgetWordLaw_le_one e f H r ω x
    _ = 1 := by simp

noncomputable def budgetTraversalMass {d k : ℕ} (e f : Direction d) (a r : ℝ)
    (π : Environment d → SupportedTupleMeasures (TupleAtHeight (k := k) (realPosition (step e)) a))
    (h : ℕ) (ω : Environment d) : ℝ≥0∞ :=
  if h=0 then 1 else relativeBudgetMassENN e f h r (π ω).val ω

noncomputable def budgetFirstThreat {d k : ℕ} (e f : Direction d) (a r g : ℝ)
    (π : Environment d → SupportedTupleMeasures (TupleAtHeight (k := k) (realPosition (step e)) a))
    (H : ℕ) : Environment d → ℕ :=
  hittingBtwn (budgetTraversalMass e f a r π) (Set.Iio (ENNReal.ofReal g)) 1 H

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def tupleAppendUpward {d k : ℕ} (e : Direction d) (w : Fin k → List (Direction d)) :
    Fin k → List (Direction d) := fun j => w j ++ [e]

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BudgetEndpoint
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def budgetEndpointMixture {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (π : Measure (Fin k → Lattice d)) (ω : Environment d) :
    Measure (Fin k → Lattice d) := π.bind (relativeBudgetEndpointLaw e f H r ω)

lemma budgetEndpointMixture_apply {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (π : Measure (Fin k → Lattice d)) (ω : Environment d)
    (A : Set (Fin k → Lattice d)) :
    budgetEndpointMixture e f H r π ω A = ∫⁻ x, relativeBudgetEndpointLaw e f H r ω x A ∂π := by
  exact Measure.bind_apply (Set.to_countable _).measurableSet (measurable_of_countable _).aemeasurable

lemma budgetEndpointMixture_univ {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (π : Measure (Fin k → Lattice d)) (ω : Environment d) :
    budgetEndpointMixture e f H r π ω Set.univ = relativeBudgetMassENN e f H r π ω := by
  rw [budgetEndpointMixture_apply,relativeBudgetMassENN]
  congr 1; funext x
  exact Measure.map_apply_of_aemeasurable (measurable_of_countable _).aemeasurable MeasurableSet.univ

instance budgetEndpointMixture_finite {d k : ℕ} (e f : Direction d)
    (H : ℕ) (r : ℝ) (π : Measure (Fin k → Lattice d)) [IsProbabilityMeasure π] (ω : Environment d) :
    IsFiniteMeasure (budgetEndpointMixture e f H r π ω) := by
  constructor
  rw [budgetEndpointMixture_univ]
  exact lt_of_le_of_lt (relativeBudgetMassENN_le_one e f H r π ω) ENNReal.one_lt_top

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma relativeBudgetWordLaw_ae {d k : ℕ} (e f : Direction d) (H : ℕ) (r : ℝ)
    (ω : Environment d) (x : Fin k → Lattice d) :
    ∀ᵐ w ∂relativeBudgetWordLaw e f H r ω x,
      TupleRelativeBudget e f x H r w ∧ ∀ j,
      wordPath (x j) (w j) ∈ HitAt (Strip (realPosition (step e)) (x j) H)
        (Upper (realPosition (step e)) (x j) H) (w j).length := by
  apply ae_iff_of_countable.mpr
  intro w hw
  rw [relativeBudgetWordLaw_singleton] at hw
  by_cases hb : TupleRelativeBudget e f x H r w
  · rw [ite_eq_left hb,rawTupleWordLaw_singleton] at hw
    refine ⟨hb,?_⟩
    intro j
    by_contra hj
    apply hw
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [rawWordLaw_singleton,ite_eq_right hj]
  · exact False.elim (hw (by rw [ite_eq_right hb]))

lemma relativeBudgetEndpointLaw_support {d k : ℕ} (e f : Direction d) (H : ℕ)
    (a G r : ℝ) (ω : Environment d) (x : Fin k → Lattice d)
    (hx : x ∈ TupleAtHeight (realPosition (step e)) a) (hG : TupleSeparated f G x) :
    ∀ᵐ y ∂relativeBudgetEndpointLaw e f H r ω x,
      y ∈ TupleAtHeight (realPosition (step e)) (a+H) ∧ TupleSeparated f (G-r) y := by
  rw [relativeBudgetEndpointLaw,ae_map_iff (measurable_of_countable _).aemeasurable (Set.to_countable _).measurableSet]
  filter_upwards [relativeBudgetWordLaw_ae e f H r ω x] with w hw
  let u j : HitWord (x j) (Strip (realPosition (step e)) (x j) H) (Upper (realPosition (step e)) (x j) H) := ⟨w j,hw.2 j⟩
  refine ⟨?_,tupleRelativeBudget_separation e f x H G r u hG hw.1⟩
  intro j
  change dot (realPosition (wordPath (x j) (w j) (w j).length)) (realPosition (step e))=a+H
  have hh := wordPath_hit_exact e (x j) H (u j)
  have hr : dot (realPosition (wordPath (x j) (w j) (w j).length)) (realPosition (step e)) =
      dot (realPosition (x j)) (realPosition (step e))+(H:ℝ) := by
    rw [signedHeight_projection,signedHeight_projection]
    exact_mod_cast hh
  simpa only [hx j] using hr

lemma budgetEndpointMixture_support {d k : ℕ} (e f : Direction d) (H : ℕ) (a G r : ℝ)
    (π : Measure (Fin k → Lattice d)) (ω : Environment d)
    (hπ : ∀ᵐ x ∂π, x ∈ TupleAtHeight (realPosition (step e)) a ∧ TupleSeparated f G x) :
    ∀ᵐ y ∂budgetEndpointMixture e f H r π ω,
      y ∈ TupleAtHeight (realPosition (step e)) (a+H) ∧ TupleSeparated f (G-r) y := by
  apply TupleKernel.countable_bind_ae
  exact hπ.mono fun x hx => relativeBudgetEndpointLaw_support e f H a G r ω x hx.1 hx.2

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BudgetNormalize
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

instance budgetProfile_probability {d k : ℕ} (e f : Direction d) (a G : ℝ)
    (π : BudgetProfile (k:=k) e f a G) : IsProbabilityMeasure π.val := π.property.1

noncomputable def nextBudgetProfile {d k : ℕ} (e f : Direction d) (H : ℕ) (a G r : ℝ)
    (hr : 0 ≤ r) (π : BudgetProfile (k:=k) e f a G) (ω : Environment d) :
    BudgetProfile (k:=k) e f (a+H) (G-r) := by
  let μ := budgetEndpointMixture e f H r π.val ω
  let ρ := π.val.map (tupleShiftUp e H)
  letI : IsProbabilityMeasure ρ := by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  refine ⟨normalizeOr μ ρ,normalizeOr_probability μ ρ,?_⟩
  apply normalizeOr_ae
  · exact budgetEndpointMixture_support e f H a G r π.val ω π.property.2
  · rw [ae_map_iff (measurable_of_countable _).aemeasurable (Set.to_countable _).measurableSet]
    exact π.property.2.mono fun x hx => by
      have h := tupleShiftUp_support e f H a G x hx
      exact ⟨h.1,tupleSeparated_mono f (sub_le_self G hr) _ h.2⟩

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_SeedMedian
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def orientedIntegerLaw {d : ℕ} (f : Direction d) (s : ℤ)
    (μ : ProbabilityMeasure (Lattice d)) : ProbabilityMeasure ℤ :=
  ⟨μ.toMeasure.map (fun x => s*signedHeight f x),
    (Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable).mpr
      (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

noncomputable def seedMedian {d : ℕ} (f : Direction d) (s : ℤ)
    (μ : ProbabilityMeasure (Lattice d)) : ℤ := selectedIntegerMedian (orientedIntegerLaw f s μ)

noncomputable def seedHalfRaw {d : ℕ} (f : Direction d) (s : ℤ) (upper : Bool)
    (μ : ProbabilityMeasure (Lattice d)) : Measure (Lattice d) :=
  μ.toMeasure.restrict {x | if upper then seedMedian f s μ ≤ s*signedHeight f x
    else s*signedHeight f x ≤ seedMedian f s μ}

instance seedHalfRaw_finite {d : ℕ} (f : Direction d) (s : ℤ) (upper : Bool)
    (μ : ProbabilityMeasure (Lattice d)) : IsFiniteMeasure (seedHalfRaw f s upper μ) := by
  unfold seedHalfRaw; infer_instance

noncomputable def seedHalf {d : ℕ} (f : Direction d) (s : ℤ) (upper : Bool)
    (μ : ProbabilityMeasure (Lattice d)) : ProbabilityMeasure (Lattice d) :=
  ⟨normalizeOr (seedHalfRaw f s upper μ) μ.toMeasure,normalizeOr_probability _ _⟩

lemma seedHalf_inherits {d : ℕ} (f : Direction d) (s : ℤ) (upper : Bool)
    (μ : ProbabilityMeasure (Lattice d)) (P : Lattice d → Prop) (hP : ∀ᵐ x ∂μ.toMeasure, P x) :
    ∀ᵐ x ∂(seedHalf f s upper μ).toMeasure, P x := by
  change ∀ᵐ x ∂normalizeOr _ _, _
  exact normalizeOr_ae _ _ _ (ae_restrict_of_ae hP) hP

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_SeedProfile
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def seedShift {d : ℕ} (e : Direction d) (H : ℕ) (μ : ProbabilityMeasure (Lattice d)) :
    ProbabilityMeasure (Lattice d) :=
  ⟨μ.toMeasure.map (fun x => x+H • step e),(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_SeedStateOrder
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def seedBelow {d : ℕ} (e : Direction d) (a : ℤ) := {x : Lattice d | signedHeight e x<a}
def seedAbove {d : ℕ} (e : Direction d) (a : ℤ) := {x : Lattice d | a ≤ signedHeight e x}

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayTopology
attribute [-instance] _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace DirectionalTransience.StationaryCompact

variable {H R : Type*}
  [TopologicalSpace H] [DiscreteTopology H] [Countable H]
  [TopologicalSpace R] [CompactSpace R] [T2Space R] [SecondCountableTopology R]

instance array_compact : CompactSpace (EpisodeArray H R) := inferInstance
instance array_t2 : T2Space (EpisodeArray H R) := by
  have : T2Space (OnePoint H) := inferInstance
  have : T2Space MarkSpace := inferInstance
  unfold EpisodeArray
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end DirectionalTransience.StationaryCompact

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_Array
attribute [-instance] _root_.OAI.DirectionalTransience.annealedLaw_probability _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.environmentLaw_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.initialLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.quenchedKernel_markov _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.stateTrajectory_markov _root_.OAI.DirectionalTransience.state_measurableEq _root_.OAI.DirectionalTransience.state_measurableSingleton _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped NNReal ENNReal BigOperators Classical
namespace DirectionalTransience

instance actualArray_compact {d : ℕ} (e : Direction d) : CompactSpace (ActualEpisodeArray e) := inferInstance

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_GlobalProfile
attribute [-instance] _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

lemma signedHeight_horizontalLift {d : ℕ} (e : Direction d) (h : ℤ) (z : HorizontalSpace e) :
    signedHeight e (horizontalLift e h z)=h := by
  have hz : z.val e.1=0 := z.property
  rw [horizontalLift,signedHeight_add,signedHeight_zsmul_step]
  simp [signedHeight,hz]

lemma horizontalProjection_lift {d : ℕ} (e : Direction d) (h : ℤ) (z : HorizontalSpace e) :
    horizontalProjection e (horizontalLift e h z)=z := by
  apply Subtype.ext
  funext i
  by_cases hi : i=e.1
  · subst i
    have hz : z.val e.1=0 := z.property
    simp [horizontalProjection,hz]
  · simp [horizontalProjection,horizontalLift,step,hi]

lemma horizontalLift_projection {d : ℕ} (e : Direction d) (x : Lattice d) :
    horizontalLift e (signedHeight e x) (horizontalProjection e x)=x := by
  funext i
  by_cases hi : i=e.1
  · subst i
    simp only [horizontalLift,horizontalProjection,Pi.add_apply,Function.update_self,
      Pi.smul_apply,step,ite_true, if_true,zero_add,smul_eq_mul,signedHeight]
    split <;> simp_all
  · simp [horizontalLift,horizontalProjection,step,hi]

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_StoppedSplice
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
attribute [-simp] _root_.OAI.DirectionalTransience.latticeVector_zero _root_.OAI.DirectionalTransience.wordPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma fresh_rows_diagonal_lintegral {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    {S T : Set (Lattice d)} (hST : Disjoint S T)
    (F : Environment d × Environment d → ℝ≥0∞)
    (hF : @Measurable _ _ (MeasurableSpace.prod (rowSigma S) (rowSigma T)) _ F) :
    (∫⁻ ω, F (ω,ω) ∂environmentLaw ν)=
      ∫⁻ η, ∫⁻ ξ, F (η,ξ) ∂environmentLaw ν ∂environmentLaw ν := by
  have hU : @Measurable (Environment d) (Environment d) inferInstance (rowSigma S) id :=
    measurable_id.mono le_rfl (rowSigma_le S)
  have hV : @Measurable (Environment d) (Environment d) inferInstance (rowSigma T) id :=
    measurable_id.mono le_rfl (rowSigma_le T)
  exact @independent_diagonal_lintegral (Environment d) (Environment d) (Environment d)
    inferInstance (rowSigma S) (rowSigma T) (environmentLaw ν) inferInstance id id hU hV
    (@indepFun_of_disjoint_rows d (Environment d) (Environment d) (rowSigma S) (rowSigma T)
      ν _ S T hST id id measurable_id measurable_id) F hF

lemma rowGraft_measurable_rows {d : ℕ} (S : Set (Lattice d)) :
    @Measurable (Environment d×Environment d) (Environment d)
      (MeasurableSpace.prod (rowSigma S) (rowSigma Sᶜ)) inferInstance
      (fun p => rowGraft S p.1 p.2) := by
  apply @Measurable.of_eval (Environment d×Environment d) (Lattice d) (fun _ => Row d)
    (MeasurableSpace.prod (rowSigma S) (rowSigma Sᶜ)) (fun _ => inferInstance)
  intro x
  by_cases hx : x∈S
  · simp only [rowGraft,ite_eq_left hx]
    exact (measurable_row_on hx).comp measurable_fst
  · simp only [rowGraft,ite_eq_right hx]
    exact (measurable_row_on hx).comp measurable_snd

lemma rowGraft_measurable {d : ℕ} (S : Set (Lattice d)) :
    Measurable (fun p : Environment d×Environment d => rowGraft S p.1 p.2) := by
  apply Measurable.of_eval
  intro x
  by_cases hx : x∈S
  · simp only [rowGraft,ite_eq_left hx]
    exact (measurable_pi_apply x).comp measurable_fst
  · simp only [rowGraft,ite_eq_right hx]
    exact (measurable_pi_apply x).comp measurable_snd

lemma rowGraft_event_lintegral {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (S : Set (Lattice d)) (A : Set (Environment d))
    (hA : MeasurableSet[rowSigma S] A)
    (f : Environment d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ η, ∫⁻ ξ, A.indicator (fun ω => f (rowGraft S ω ξ)) η
      ∂environmentLaw ν ∂environmentLaw ν)=
      ∫⁻ ω, A.indicator f ω ∂environmentLaw ν := by
  have hF : @Measurable _ _ (MeasurableSpace.prod (rowSigma S) (rowSigma Sᶜ)) _
      (fun p : Environment d×Environment d => A.indicator
        (fun ω => f (rowGraft S ω p.2)) p.1) := by
    change @Measurable _ _ (MeasurableSpace.prod (rowSigma S) (rowSigma Sᶜ)) _
      ((Prod.fst ⁻¹' A).indicator (fun p => f (rowGraft S p.1 p.2)))
    exact (hf.comp (rowGraft_measurable_rows S)).indicator (hA.preimage measurable_fst)
  rw [←fresh_rows_diagonal_lintegral ν disjoint_compl_right _ hF]
  apply lintegral_congr
  intro ω
  by_cases hω : ω∈A
  · simp [hω,rowGraft_diagonal]
  · simp [hω]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

def StoppedRowsEvent {d : ℕ} (S : ℕ → Set (Lattice d)) (τ : Environment d → ℕ)
    (A : Set (Environment d)) : Prop :=
  ∀ n, MeasurableSet[rowSigma (S n)] (A∩{ω | τ ω=n})

lemma measurable_of_stop_events {d : ℕ} (S : ℕ → Set (Lattice d)) (τ : Environment d → ℕ)
    (hτ : ∀ n, MeasurableSet[rowSigma (S n)] {ω | τ ω=n}) : Measurable τ := by
  apply measurable_to_countable
  intro ω
  exact (rowSigma_le _) _ (hτ (τ ω))

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_StoppedFreshField
attribute [-instance] _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

noncomputable def upperField {d : ℕ} (e : Direction d) (n : ℕ) (ω : Environment d) :
    (ℕ×HorizontalSpace e) → Row d := fun p => ω (horizontalLift e (n+p.1) p.2)

lemma upperField_index_injective {d : ℕ} (e : Direction d) (n : ℕ) :
    Function.Injective (fun p : ℕ×HorizontalSpace e => horizontalLift e (n+p.1) p.2) := by
  intro p q h
  have hh := congrArg (signedHeight e) h
  have hz := congrArg (horizontalProjection e) h
  rw [signedHeight_horizontalLift,signedHeight_horizontalLift] at hh
  rw [horizontalProjection_lift,horizontalProjection_lift] at hz
  exact Prod.ext (by exact_mod_cast (add_left_cancel hh)) hz

lemma upperField_measurable_rows {d : ℕ} (e : Direction d) (n : ℕ) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) n)ᶜ) _ (upperField e n) := by
  apply @Measurable.of_eval (Environment d) (ℕ×HorizontalSpace e) (fun _ => Row d)
    (rowSigma (BelowHeight (realPosition (step e)) n)ᶜ) (fun _ => inferInstance)
  intro p
  apply measurable_row_on
  change ¬ dot (realPosition (horizontalLift e (n+p.1) p.2)) (realPosition (step e))<n
  rw [signedHeight_projection,signedHeight_horizontalLift]
  push_cast
  linarith [Nat.cast_nonneg (α:=ℝ) p.1]

lemma upperField_map {d : ℕ} (e : Direction d) (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (n : ℕ) : (environmentLaw ν).map (upperField e n)=
      Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν) :=
  Measure.map_infinitePi_infinitePi_of_inj (upperField_index_injective e n)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_BadCrossingLaw
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

def badCrossingEvent {d : ℕ} (e : Direction d) (N : ℕ) (β : ℝ) : Set (Environment d) :=
  {ω | (crossingQuenched (realPosition (step e)) 0 N ω).toReal < (N:ℝ)^(-β)}

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_SpatialConfinement
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def StripExcursion {d : ℕ} (ℓ : Vector d) (H R : ℝ) : Set (Path d) :=
  {X | ∃ n, X ∈ BoundedHeightPrefix ℓ H n ∧ ∃ u : Direction d, R < signedCoordinate u (X n)}

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_CrossingGap
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

noncomputable def latticeBox {d : ℕ} (M : ℕ) : Finset (Lattice d) :=
  Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(M:ℤ)) M)

def badBoxEvent {d : ℕ} (e : Direction d) (N : ℕ) (β : ℝ) (S : Finset (Lattice d)) :
    Set (Environment d) :=
  ⋃ x ∈ S, {ω | (crossingQuenched (realPosition (step e)) x N ω).toReal < (N:ℝ)^(-β)}

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_VisitTrials
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

noncomputable def visitCount {d : ℕ} (X : Path d) (y : Lattice d) (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, if X j=y then 1 else 0

def VisitPrefix {d : ℕ} (x : Lattice d) (S : Set (Lattice d)) (y : Lattice d) (k n : ℕ) :
    Set (Path d) := {X | X 0=x ∧ X n=y ∧ (∀ j ≤ n, X j∈S) ∧ visitCount X y n=k}

def VisitReached {d : ℕ} (x : Lattice d) (S : Set (Lattice d)) (y : Lattice d) (k : ℕ) :
    Set (Path d) := ⋃ n, VisitPrefix x S y k n

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_FiniteBoxExit
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def UpwardCross {d : ℕ} (e : Direction d) (y : Lattice d) (H : ℕ) : Set (Path d) :=
  (fun X : Path d => fun j => X (1+j)) ⁻¹' Cross (realPosition (step e)) (y+step e) H ∩
    wordCylinder y [e]

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_StripExitBound
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def StripUntil {d : ℕ} (e : Direction d) (H T : ℕ) : Set (Path d) :=
  ConfinedUntil 0 {y | 0 ≤ signedHeight e y ∧ signedHeight e y < (H:ℤ)} T

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BufferRestorationScript
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma wordPath_lateral_script_end {d : ℕ} (e f : Direction d) (x : Lattice d) (m : ℕ) :
    wordPath x (List.replicate m f ++ [e]) (m+1) = x+m • step f+step e := by
  induction m generalizing x with
  | zero => simp [wordPath]
  | succ m ih =>
    simp only [List.replicate_succ,List.cons_append,wordPath,ih,succ_nsmul]
    abel

lemma wordPath_lateral_script_prefix {d : ℕ} (e f : Direction d) (x : Lattice d)
    (m j : ℕ) (hj : j ≤ m) :
    wordPath x (List.replicate m f ++ [e]) j = x+j • step f := by
  induction m generalizing x j with
  | zero =>
    have : j=0 := by omega
    subst j
    simp
  | succ m ih =>
    cases j with
    | zero => simp
    | succ j =>
      simp only [List.replicate_succ,List.cons_append,wordPath,
        ih (x+step f) j (by omega),succ_nsmul]
      abel

noncomputable def bufferRestoreWord {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (x : Lattice d) (m : ℕ) : HitWord x
      (Strip (realPosition (step e)) x 1) (Upper (realPosition (step e)) x 1) := by
  refine ⟨List.replicate m f ++ [e],?_,?_⟩
  · simp only [List.length_append,List.length_replicate,List.length_cons,List.length_nil,
      zero_add,wordPath_lateral_script_end]
    change dot (realPosition x) (realPosition (step e))+1 ≤
      dot (realPosition (x+m • step f+step e)) (realPosition (step e))
    simp only [signedHeight_projection,signedHeight_add_step_self,
      signedHeight_add_nsmul_other e f hef,Int.cast_add,Int.cast_one]
    exact le_rfl
  · intro j hj
    have hjm : j ≤ m := by simpa only [List.length_append,List.length_replicate,
      List.length_cons,List.length_nil,zero_add,Nat.lt_succ_iff] using hj
    rw [wordPath_lateral_script_prefix e f x m j hjm]
    change dot (realPosition x) (realPosition (step e)) ≤
      dot (realPosition (x+j • step f)) (realPosition (step e)) ∧
      dot (realPosition (x+j • step f)) (realPosition (step e)) <
      dot (realPosition x) (realPosition (step e))+1
    simp only [signedHeight_projection,signedHeight_add_nsmul_other e f hef]
    exact ⟨le_rfl,by norm_num⟩

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def pairRestore {d : ℕ} (e f : Direction d) (m : ℕ) (x : Lattice d × Lattice d) :
    Lattice d × Lattice d := (x.1+step e,x.2+m • step f+step e)

lemma pairRestore_height {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (m : ℕ) (a : ℝ) (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight (realPosition (step e)) a) :
    pairRestore e f m x ∈ PairAtHeight (realPosition (step e)) (a+1) := by
  have h1 := hx.1
  have h2 := hx.2
  simp only [signedHeight_projection] at h1 h2
  constructor
  · change dot (realPosition (x.1+step e)) (realPosition (step e))=a+1
    simp only [signedHeight_projection,signedHeight_add_step_self,Int.cast_add,Int.cast_one,h1]
  · change dot (realPosition (x.2+m • step f+step e)) (realPosition (step e))=a+1
    simp only [signedHeight_projection,signedHeight_add_step_self,
      signedHeight_add_nsmul_other e f hef,Int.cast_add,Int.cast_one,h2]

noncomputable def bufferRestorationLaw {d : ℕ} (e f : Direction d) (m : ℕ)
    (π : Measure (Lattice d × Lattice d)) (κ : ℝ≥0) : Measure (Lattice d × Lattice d) :=
  (κ : ℝ≥0∞)^(m+2) • π.map (pairRestore e f m)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_PairUpwardRetention
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def pairUp {d : ℕ} (e : Direction d) (x : Lattice d × Lattice d) : Lattice d × Lattice d :=
  (x.1+step e,x.2+step e)

noncomputable def upwardRetainedLaw {d : ℕ} (e f : Direction d) (H : ℕ) (z : ℝ)
    (π : Measure (Lattice d × Lattice d)) (ω : Environment d) (κ : ℝ≥0) :
    Measure (Lattice d × Lattice d) :=
  (κ : ℝ≥0∞)^2 • (retainedPairLaw (realPosition (step e)) f H z π ω).map (pairUp e)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RawPair
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
lemma hitKernel_height_zero {d : ℕ} (ℓ : Vector d) (x : Lattice d) (ω : Environment d) :
    hitKernel (Strip ℓ x 0) (Upper ℓ x 0) (ω,x) = Measure.dirac x := by
  apply Measure.ext
  intro U hU
  rw [hitKernel_apply_eq_hit (disjoint_strip_upper _ _ _)]
  have heq : Hit (Strip ℓ x 0) (Upper ℓ x 0 ∩ U) =ᵐ[quenchedKernel (ω,x)]
      (fun _ : Path d => x∈U) := by
    filter_upwards [quenched_initial_ae (ω,x)] with X hX
    apply propext
    constructor
    · intro h
      obtain ⟨n,hn⟩ := Set.mem_iUnion.mp h
      have hn0 : n=0 := by
        by_contra hn0
        have hh := hn.2 0 (Nat.pos_of_ne_zero hn0)
        exact (not_lt_of_ge hh.1) (by simpa only [add_zero] using hh.2)
      subst n
      have hxU : x∈U := by simpa only [hX] using hn.1.2
      exact hxU
    · intro h
      have hxU : x∈U := h
      apply Set.mem_iUnion.mpr
      refine ⟨0,⟨?_,?_⟩,by intro j hj; omega⟩
      · change dot (realPosition x) ℓ+0 ≤ dot (realPosition (X 0)) ℓ
        simp only [hX,add_zero,le_refl]
      · simpa only [hX] using hxU
  rw [measure_congr heq,Measure.dirac_apply' _ hU]
  by_cases hu : x∈U <;> simp [hu]
  · change (quenchedKernel (ω,x)) Set.univ = 1
    simp
  · change (quenchedKernel (ω,x)) ∅ = 0
    simp

lemma rawPairEndpointLaw_zero {d : ℕ} (ℓ : Vector d) (ω : Environment d)
    (x : Lattice d × Lattice d) : rawPairEndpointLaw ℓ 0 ω x = Measure.dirac x := by
  simp only [rawPairEndpointLaw,Nat.cast_zero,hitKernel_height_zero,Measure.dirac_prod_dirac,Prod.mk.eta]

lemma rawPairMixture_zero {d : ℕ} (ℓ : Vector d) (ω : Environment d)
    (π : Measure (Lattice d × Lattice d)) : rawPairMixture ℓ 0 π ω = π := by
  unfold rawPairMixture
  change π.bind (fun x => rawPairEndpointLaw ℓ 0 ω x) = π
  simp_rw [rawPairEndpointLaw_zero]
  exact Measure.bind_dirac

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def bufferStageRetainedLaw {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    (H : ℕ) (ω : Environment d) (κ : ℝ≥0) : Measure (Lattice d × Lattice d) :=
  let ℓ := realPosition (step e)
  let z := z₀+(1-ε)*r
  let j := bufferFirstFailure ℓ f a z g π H ω
  if pairKernelMass ℓ f j z (π ω).val ω < ENNReal.ofReal g then
    upwardRetainedLaw e f (j-1) z (π ω).val ω κ
  else if ENNReal.ofReal g ≤ pairKernelMass ℓ f H (z₀+(1+α)*r) (π ω).val ω then
    retainedPairLaw ℓ f H (z₀+(1+α)*r) (π ω).val ω
  else retainedPairLaw ℓ f H z (π ω).val ω

lemma bufferFirstFailure_eq_top_of_pass {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (a z g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight ℓ a))
    {H : ℕ} (hH : 0 < H) (ω : Environment d)
    (hp : ENNReal.ofReal g ≤ pairKernelMass ℓ f (bufferFirstFailure ℓ f a z g π H ω) z (π ω).val ω) :
    bufferFirstFailure ℓ f a z g π H ω = H := by
  have hb := bufferFirstFailure_bounds ℓ f a z g π hH ω
  apply le_antisymm hb.2
  by_contra hn
  have hlt : bufferFirstFailure ℓ f a z g π H ω < H := lt_of_not_ge hn
  exact (not_lt_of_ge hp) (bufferFirstFailure_fails_of_lt ℓ f a z g π hH ω hlt)

lemma bufferStageEvent_iff_last_tests {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight ℓ a))
    {H : ℕ} (hH : 0 < H) (ω : Environment d) :
    BufferStageEvent ℓ f H z₀ r ε α g (π ω).val ω ↔
      ENNReal.ofReal g ≤ pairKernelMass ℓ f
        (bufferFirstFailure ℓ f a (z₀+(1-ε)*r) g π H ω) (z₀+(1-ε)*r) (π ω).val ω ∧
      ENNReal.ofReal g ≤ pairKernelMass ℓ f H (z₀+(1+α)*r) (π ω).val ω := by
  constructor
  · intro h
    have hb := bufferFirstFailure_bounds ℓ f a (z₀+(1-ε)*r) g π hH ω
    exact ⟨h.1 _ hb.1 hb.2,h.2⟩
  · rintro ⟨hp,hg⟩
    refine ⟨?_,hg⟩
    intro j hj hjH
    have heq := bufferFirstFailure_eq_top_of_pass ℓ f a (z₀+(1-ε)*r) g π hH ω hp
    rcases lt_or_eq_of_le hjH with hlt|rfl
    · apply before_bufferFirstFailure_pass ℓ f a (z₀+(1-ε)*r) g π H ω hj
      simpa only [heq] using hlt
    · simpa only [heq] using hp

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_PairHeight
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
lemma rawPairEndpointLaw_height {d : ℕ} (e : Direction d) (H : ℕ)
    (ω : Environment d) (x : Lattice d × Lattice d) (a : ℝ)
    (hx : x ∈ PairAtHeight (realPosition (step e)) a) :
    ∀ᵐ y ∂rawPairEndpointLaw (realPosition (step e)) H ω x,
      y ∈ PairAtHeight (realPosition (step e)) (a+H) := by
  have hfinite (z : Lattice d) : IsFiniteMeasure
      (hitKernel (Strip (realPosition (step e)) z H) (Upper (realPosition (step e)) z H) (ω,z)) :=
    ⟨lt_of_le_of_lt (hitKernel_total_le_one (disjoint_strip_upper _ _ _) _) ENNReal.one_lt_top⟩
  let := hfinite x.2
  rw [rawPairEndpointLaw,Measure.ae_prod_iff_ae_ae (Set.to_countable _ |>.measurableSet)]
  filter_upwards [coordinate_hitKernel_supported e x.1 H ω] with y hy
  filter_upwards [coordinate_hitKernel_supported e x.2 H ω] with z hz
  constructor
  · change dot (realPosition y) (realPosition (step e)) = a+H
    rw [signedHeight_projection]
    have h := hx.1
    rw [signedHeight_projection] at h
    rw [←h]
    exact_mod_cast hy
  · change dot (realPosition z) (realPosition (step e)) = a+H
    rw [signedHeight_projection]
    have h := hx.2
    rw [signedHeight_projection] at h
    rw [←h]
    exact_mod_cast hz

lemma rawPairMixture_height {d : ℕ} (e : Direction d) (H : ℕ)
    (ω : Environment d) (π : Measure (Lattice d × Lattice d)) (a : ℝ)
    (hπ : ∀ᵐ x ∂π, x ∈ PairAtHeight (realPosition (step e)) a) :
    ∀ᵐ y ∂rawPairMixture (realPosition (step e)) H π ω,
      y ∈ PairAtHeight (realPosition (step e)) (a+H) := by
  rw [ae_iff,rawPairMixture_apply]
  apply (lintegral_eq_zero_iff (measurable_of_countable _)).mpr
  filter_upwards [hπ] with x hx
  exact (ae_iff.mp (rawPairEndpointLaw_height e H ω x a hx))

lemma retainedPairLaw_height {d : ℕ} (e f : Direction d) (H : ℕ) (z : ℝ)
    (ω : Environment d) (π : Measure (Lattice d × Lattice d)) (a : ℝ)
    (hπ : ∀ᵐ x ∂π, x ∈ PairAtHeight (realPosition (step e)) a) :
    ∀ᵐ y ∂retainedPairLaw (realPosition (step e)) f H z π ω,
      y ∈ PairAtHeight (realPosition (step e)) (a+H) :=
  (Measure.absolutelyContinuous_of_le (retainedPairLaw_le _ _ _ _ _ _)).ae_le
    (rawPairMixture_height e H ω π a hπ)

lemma pairUp_height {d : ℕ} (e : Direction d) (x : Lattice d × Lattice d) (a : ℝ)
    (hx : x ∈ PairAtHeight (realPosition (step e)) a) :
    pairUp e x ∈ PairAtHeight (realPosition (step e)) (a+1) := by
  constructor <;> simp only [pairUp,dot_realPosition_add,signed_direction_unit]
  · rw [hx.1]
  · rw [hx.2]

lemma upwardRetainedLaw_height {d : ℕ} (e f : Direction d) (H : ℕ) (z : ℝ)
    (ω : Environment d) (π : Measure (Lattice d × Lattice d)) (κ : ℝ≥0) (a : ℝ)
    (hπ : ∀ᵐ x ∂π, x ∈ PairAtHeight (realPosition (step e)) a) :
    ∀ᵐ y ∂upwardRetainedLaw e f H z π ω κ,
      y ∈ PairAtHeight (realPosition (step e)) (a+(H+1:ℕ)) := by
  unfold upwardRetainedLaw
  apply Measure.ae_smul_measure
  rw [ae_map_iff (measurable_of_countable _).aemeasurable (Set.to_countable _ |>.measurableSet)]
  filter_upwards [retainedPairLaw_height e f H z ω π a hπ] with x hx
  have := pairUp_height e x (a+H) hx
  simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using this
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_RetentionRowsAllHeights
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
lemma retainedPairLaw_zero {d : ℕ} (ℓ : Vector d) (f : Direction d) (z : ℝ)
    (π : Measure (Lattice d × Lattice d)) (ω : Environment d) :
    retainedPairLaw ℓ f 0 z π ω = π.restrict {y | z ≤ signedCoordinate f (y.2-y.1)} := by
  simp only [retainedPairLaw,rawPairMixture_zero]

lemma retainedPairLaw_joint_rows_all {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (H : ℕ) (z : ℝ) (C : Set (Lattice d × Lattice d)) (S : Set (Lattice d))
    (hC : ∀ x ∈ C, Strip ℓ x.1 H ⊆ S ∧ Strip ℓ x.2 H ⊆ S) :
    @Measurable (SupportedPairMeasures C × Environment d) (Measure (Lattice d × Lattice d))
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S)) _
      (fun p => retainedPairLaw ℓ f H z p.1.val p.2) := by
  by_cases hH : H=0
  · subst H
    simp only [retainedPairLaw_zero]
    let : MeasurableSpace (Environment d) := rowSigma S
    apply Measure.measurable_of_measurable_coe
    intro U hU
    simp only [Measure.restrict_apply hU]
    exact (Measure.measurable_coe (hU.inter (Set.to_countable _).measurableSet)).comp
      (measurable_subtype_coe.comp measurable_fst)
  · exact retainedPairLaw_joint_rows ℓ f (Nat.pos_of_ne_zero hH) z C S hC

lemma upwardRetainedLaw_joint_rows {d : ℕ} (e f : Direction d)
    (H : ℕ) (z : ℝ) (κ : ℝ≥0) (C : Set (Lattice d × Lattice d)) (S : Set (Lattice d))
    (hC : ∀ x ∈ C, Strip (realPosition (step e)) x.1 H ⊆ S ∧
      Strip (realPosition (step e)) x.2 H ⊆ S) :
    @Measurable (SupportedPairMeasures C × Environment d) (Measure (Lattice d × Lattice d))
      (@Prod.instMeasurableSpace _ _ inferInstance (rowSigma S)) _
      (fun p => upwardRetainedLaw e f H z p.1.val p.2 κ) := by
  let : MeasurableSpace (Environment d) := rowSigma S
  have hm := (Measure.measurable_map (pairUp e) (measurable_of_countable _)).comp
    (retainedPairLaw_joint_rows_all (realPosition (step e)) f H z C S hC)
  apply Measure.measurable_of_measurable_coe
  intro U hU
  simp only [upwardRetainedLaw,Measure.smul_apply,smul_eq_mul]
  exact measurable_const.mul ((Measure.measurable_coe hU).comp hm)

lemma strip_subset_below_height {d : ℕ} (ℓ : Vector d) (a : ℝ)
    (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight ℓ a)
    {h k : ℕ} (hhk : h ≤ k) :
    Strip ℓ x.1 h ⊆ BelowHeight ℓ (a+k) ∧ Strip ℓ x.2 h ⊆ BelowHeight ℓ (a+k) := by
  have hhkR : (h:ℝ) ≤ k := by exact_mod_cast hhk
  constructor
  · intro y hy
    change dot (realPosition y) ℓ < a+k
    have ht := hy.2
    rw [hx.1] at ht
    linarith
  · intro y hy
    change dot (realPosition y) ℓ < a+k
    have ht := hy.2
    rw [hx.2] at ht
    linarith

lemma rowSigma_below_height_mono {d : ℕ} (ℓ : Vector d) (a : ℝ) (k : ℕ) :
    rowSigma (BelowHeight ℓ a) ≤ rowSigma (BelowHeight ℓ (a+k)) := by
  apply rowSigma_mono
  intro y hy
  dsimp [BelowHeight] at hy ⊢
  have : (0:ℝ) ≤ k := Nat.cast_nonneg k
  linarith

lemma retainedPairLaw_at_height_rows {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (a z : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight ℓ a))
    (hπ : @Measurable _ _ (rowSigma (BelowHeight ℓ a)) _ π)
    {h k : ℕ} (hhk : h ≤ k) :
    @Measurable _ _ (rowSigma (BelowHeight ℓ (a+k))) _
      (fun ω => retainedPairLaw ℓ f h z (π ω).val ω) := by
  let : MeasurableSpace (Environment d) := rowSigma (BelowHeight ℓ (a+k))
  have hp : @Measurable _ _ (rowSigma (BelowHeight ℓ (a+k))) _ π :=
    hπ.mono (rowSigma_below_height_mono ℓ a k) le_rfl
  have hm := (retainedPairLaw_joint_rows_all ℓ f h z (PairAtHeight ℓ a) (BelowHeight ℓ (a+k))
    (fun x hx => strip_subset_below_height ℓ a x hx hhk)).comp (hp.prodMk measurable_id)
  exact hm

lemma upwardRetainedLaw_at_height_rows {d : ℕ} (e f : Direction d)
    (a z : ℝ) (κ : ℝ≥0) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    {h k : ℕ} (hhk : h ≤ k) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a+k))) _
      (fun ω => upwardRetainedLaw e f h z (π ω).val ω κ) := by
  let : MeasurableSpace (Environment d) := rowSigma (BelowHeight (realPosition (step e)) (a+k))
  have hp : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a+k))) _ π :=
    hπ.mono (rowSigma_below_height_mono (realPosition (step e)) a k) le_rfl
  have hm := (upwardRetainedLaw_joint_rows e f h z κ (PairAtHeight (realPosition (step e)) a)
    (BelowHeight (realPosition (step e)) (a+k))
    (fun x hx => strip_subset_below_height (realPosition (step e)) a x hx hhk)).comp
      (hp.prodMk measurable_id)
  exact hm
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma bufferFirstFailure_eq_measurable {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (a z g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight ℓ a))
    (hπ : @Measurable _ _ (rowSigma (BelowHeight ℓ a)) _ π) (H k : ℕ) :
    MeasurableSet[rowSigma (BelowHeight ℓ (a+k))] {ω | bufferFirstFailure ℓ f a z g π H ω = k} := by
  have hm := (bufferFirstFailure_stopping ℓ f a z g π hπ H).measurableSet_eq_of_countable k
  have heq : {ω | bufferFirstFailure ℓ f a z g π H ω = k} =
      {ω | (bufferFirstFailure ℓ f a z g π H ω : WithTop ℕ) = (k : WithTop ℕ)} := by
    ext ω
    change _ = _ ↔ _ = _
    norm_cast
  rw [heq]
  exact hm

lemma bufferStageRetainedLaw_at_stop_lt {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    {H : ℕ} (hH : 0 < H) (ω : Environment d) (κ : ℝ≥0) {k : ℕ} (hkH : k < H)
    (hk : bufferFirstFailure (realPosition (step e)) f a (z₀+(1-ε)*r) g π H ω = k) :
    bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ =
      upwardRetainedLaw e f (k-1) (z₀+(1-ε)*r) (π ω).val ω κ := by
  have hf := bufferFirstFailure_fails_of_lt (realPosition (step e)) f a (z₀+(1-ε)*r) g π hH ω
    (by simpa only [hk] using hkH)
  rw [hk] at hf
  simp only [bufferStageRetainedLaw,hk,ite_eq_left hf]

lemma bufferStageRetainedLaw_stopped_rows {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    {H : ℕ} (hH : 0 < H) (κ : ℝ≥0) (k : ℕ) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a+k))) _
      (fun ω => if bufferFirstFailure (realPosition (step e)) f a (z₀+(1-ε)*r) g π H ω = k
        then bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ else 0) := by
  let ℓ := realPosition (step e)
  let z := z₀+(1-ε)*r
  have heq := bufferFirstFailure_eq_measurable ℓ f a z g π hπ H k
  by_cases hk : k ≤ H
  · rcases lt_or_eq_of_le hk with hklt|he
    · have hf : (fun ω => if bufferFirstFailure ℓ f a z g π H ω = k
          then bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ else 0) =
        (fun ω => if bufferFirstFailure ℓ f a z g π H ω = k
          then upwardRetainedLaw e f (k-1) z (π ω).val ω κ else 0) := by
        funext ω
        by_cases hj : bufferFirstFailure ℓ f a z g π H ω = k
        · simp only [ite_eq_left hj]
          exact bufferStageRetainedLaw_at_stop_lt e f a z₀ r ε α g π hH ω κ hklt hj
        · simp only [ite_eq_right hj]
      change @Measurable _ _ (rowSigma (BelowHeight ℓ (a+k))) _ _
      rw [hf]
      exact (upwardRetainedLaw_at_height_rows e f a z κ π hπ (Nat.sub_le k 1)).ite heq measurable_const
    · subst k
      have hp : @Measurable _ _ (rowSigma (BelowHeight ℓ (a+H))) _ π :=
        hπ.mono (rowSigma_below_height_mono ℓ a H) le_rfl
      have hmass (b : ℝ) : @Measurable _ _ (rowSigma (BelowHeight ℓ (a+H))) _
          (fun ω => pairKernelMass ℓ f H b (π ω).val ω) := by
        have hm := (pairKernelMass_joint_rows ℓ f hH b (PairAtHeight ℓ a) (BelowHeight ℓ (a+H))
          (fun x hx => strip_subset_below_height ℓ a x hx le_rfl)).comp (hp.prodMk measurable_id)
        exact hm
      have hu := upwardRetainedLaw_at_height_rows e f a z κ π hπ (Nat.sub_le H 1)
      have hc := retainedPairLaw_at_height_rows ℓ f a z π hπ (le_refl H)
      have hg := retainedPairLaw_at_height_rows ℓ f a (z₀+(1+α)*r) π hπ (le_refl H)
      have hf : (fun ω => if bufferFirstFailure ℓ f a z g π H ω = H
          then bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ else 0) =
        (fun ω => if bufferFirstFailure ℓ f a z g π H ω = H then
          (if pairKernelMass ℓ f H z (π ω).val ω < ENNReal.ofReal g then
            upwardRetainedLaw e f (H-1) z (π ω).val ω κ
          else if ENNReal.ofReal g ≤ pairKernelMass ℓ f H (z₀+(1+α)*r) (π ω).val ω then
            retainedPairLaw ℓ f H (z₀+(1+α)*r) (π ω).val ω
          else retainedPairLaw ℓ f H z (π ω).val ω) else 0) := by
        funext ω
        by_cases hj : bufferFirstFailure ℓ f a z g π H ω = H
        · simp only [ite_eq_left hj,bufferStageRetainedLaw]
          change (if pairKernelMass ℓ f (bufferFirstFailure ℓ f a z g π H ω) z (π ω).val ω < _
            then upwardRetainedLaw e f (bufferFirstFailure ℓ f a z g π H ω-1) z (π ω).val ω κ else _) = _
          rw [hj]
        · simp only [ite_eq_right hj]
      change @Measurable _ _ (rowSigma (BelowHeight ℓ (a+H))) _ _
      rw [hf]
      exact (hu.ite (measurableSet_lt (hmass z) measurable_const)
        (hg.ite (measurableSet_le measurable_const (hmass (z₀+(1+α)*r))) hc)).ite heq measurable_const
  · have hn (ω : Environment d) : bufferFirstFailure ℓ f a z g π H ω ≠ k := by
      have := (bufferFirstFailure_bounds ℓ f a z g π hH ω).2
      omega
    convert (measurable_const : @Measurable _ _ (rowSigma (BelowHeight ℓ (a+k))) _
      (fun _ : Environment d => (0 : Measure (Lattice d × Lattice d)))) using 1
    all_goals try with_reducible_and_instances rfl
    funext ω
    exact ite_eq_right (hn ω)
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_BufferNormalizedRows
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma normalizedMeasure_zero {α : Type*} [MeasurableSpace α] :
    normalizedMeasure (0 : Measure α) = 0 := by simp [normalizedMeasure]

lemma bufferStage_normalized_stopped_rows {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    {H : ℕ} (hH : 0 < H) (κ : ℝ≥0) (k : ℕ) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a+k))) _
      (fun ω => if bufferFirstFailure (realPosition (step e)) f a (z₀+(1-ε)*r) g π H ω = k
        then normalizedMeasure (bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ) else 0) := by
  have hm := measurable_normalizedMeasure.comp
    (bufferStageRetainedLaw_stopped_rows e f a z₀ r ε α g π hπ hH κ k)
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext ω
  dsimp only [Function.comp_def]
  split <;> simp_all only [normalizedMeasure_zero]

lemma bufferStage_success_stopped_rows {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    {H : ℕ} (hH : 0 < H) (k : ℕ) :
    MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) (a+k))]
      {ω | bufferFirstFailure (realPosition (step e)) f a (z₀+(1-ε)*r) g π H ω = k ∧
        BufferStageEvent (realPosition (step e)) f H z₀ r ε α g (π ω).val ω} := by
  let ℓ := realPosition (step e)
  by_cases h : k=H
  · subst k
    have heq := bufferFirstFailure_eq_measurable ℓ f a (z₀+(1-ε)*r) g π hπ H H
    have hp : @Measurable _ _ (rowSigma (BelowHeight ℓ (a+H))) _ π :=
      hπ.mono (rowSigma_below_height_mono ℓ a H) le_rfl
    have hm := (measurableSet_bufferStageEvent_rows ℓ f hH z₀ r ε α g (PairAtHeight ℓ a)
      (BelowHeight ℓ (a+H)) (fun x hx => strip_subset_below_height ℓ a x hx le_rfl)).preimage
        (hp.prodMk measurable_id)
    exact heq.inter hm
  · have he : {ω | bufferFirstFailure ℓ f a (z₀+(1-ε)*r) g π H ω = k ∧
        BufferStageEvent ℓ f H z₀ r ε α g (π ω).val ω} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨hk,hE⟩
      have hlast := bufferFirstFailure_eq_top_of_pass ℓ f a (z₀+(1-ε)*r) g π hH ω
        ((bufferStageEvent_iff_last_tests ℓ f a z₀ r ε α g π hH ω).mp hE).1
      exact h (hk.symm.trans hlast)
    change MeasurableSet[rowSigma (BelowHeight ℓ (a+k))] _
    rw [he]
    exact @MeasurableSet.empty _ (rowSigma (BelowHeight ℓ (a+k)))
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_BufferStructuralHeight
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
lemma bufferStageRetainedLaw_height_unconditional {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    {H : ℕ} (hH : 0 < H) (ω : Environment d) (κ : ℝ≥0) :
    ∀ᵐ y ∂bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ,
      y ∈ PairAtHeight (realPosition (step e))
        (a+bufferFirstFailure (realPosition (step e)) f a (z₀+(1-ε)*r) g π H ω) := by
  let ℓ := realPosition (step e)
  let z := z₀+(1-ε)*r
  let j := bufferFirstFailure ℓ f a z g π H ω
  have hπ : ∀ᵐ x ∂(π ω).val, x ∈ PairAtHeight ℓ a := ae_iff.mpr (π ω).property
  have hj : 1 ≤ j := (bufferFirstFailure_bounds ℓ f a z g π hH ω).1
  unfold bufferStageRetainedLaw
  dsimp only
  split
  · have he : j-1+1=j := by omega
    simpa only [he] using upwardRetainedLaw_height e f (j-1) z ω (π ω).val κ a hπ
  · rename_i hp
    have hjH : j=H := bufferFirstFailure_eq_top_of_pass ℓ f a z g π hH ω (le_of_not_gt hp)
    change ∀ᵐ y ∂(if _ then _ else _), y ∈ PairAtHeight ℓ (a+j)
    rw [hjH]
    split <;> exact retainedPairLaw_height e f H _ ω (π ω).val a hπ

noncomputable def bufferStageStoppedProbability {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    (H : ℕ) (hH : 0 < H) (κ : ℝ≥0) (k : ℕ) (ω : Environment d) :
    SupportedPairMeasures (PairAtHeight (realPosition (step e)) (a+k)) :=
  ⟨if bufferFirstFailure (realPosition (step e)) f a (z₀+(1-ε)*r) g π H ω = k
    then normalizedMeasure (bufferStageRetainedLaw e f a z₀ r ε α g π H ω κ) else 0, by
      split
      · rename_i hk
        apply ae_iff.mp
        apply Measure.ae_smul_measure
        simpa only [hk] using bufferStageRetainedLaw_height_unconditional e f a z₀ r ε α g π hH ω κ
      · simp⟩

lemma bufferStageStoppedProbability_rows {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    (H : ℕ) (hH : 0 < H) (κ : ℝ≥0) (k : ℕ) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a+k))) _
      (bufferStageStoppedProbability e f a z₀ r ε α g π H hH κ k) := by
  exact (bufferStage_normalized_stopped_rows e f a z₀ r ε α g π hπ hH κ k).subtype_mk

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BufferChildNode
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma bufferStage_branch_rows {d : ℕ} (e f : Direction d)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    {H : ℕ} (hH : 0 < H) (k : ℕ) (b : Bool) :
    MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) (a+k))]
      {ω | bufferFirstFailure (realPosition (step e)) f a (z₀+(1-ε)*r) g π H ω = k ∧
        (BufferStageEvent (realPosition (step e)) f H z₀ r ε α g (π ω).val ω ↔ b=true)} := by
  have hstop := bufferFirstFailure_eq_measurable (realPosition (step e)) f a (z₀+(1-ε)*r) g π hπ H k
  have hpass := bufferStage_success_stopped_rows e f a z₀ r ε α g π hπ hH k
  cases b
  · convert hstop.diff hpass using 1
    all_goals try with_reducible_and_instances rfl
    ext ω
    simp only [Bool.false_eq_true,iff_false,Set.mem_sdiff,Set.mem_ofPred_eq]
    tauto
  · convert hpass using 1
    all_goals try with_reducible_and_instances rfl
    ext ω
    simp

noncomputable def restoredStoppedLaw {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    (H : ℕ) (hH : 0 < H) (κ : ℝ≥0) (k m : ℕ) (ω : Environment d) :
    SupportedPairMeasures (PairAtHeight (realPosition (step e)) (a+k+1)) :=
  ⟨(bufferStageStoppedProbability e f a z₀ r ε α g π H hH κ k ω).val.map (pairRestore e f m), by
    apply ae_iff.mp
    rw [ae_map_iff (measurable_of_countable _).aemeasurable (Set.to_countable _).measurableSet]
    filter_upwards [ae_iff.mpr (bufferStageStoppedProbability e f a z₀ r ε α g π H hH κ k ω).property] with x hx
    exact pairRestore_height e f hef m (a+k) x hx⟩

lemma restoredStoppedLaw_rows {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a z₀ r ε α g : ℝ) (π : Environment d → SupportedPairMeasures (PairAtHeight (realPosition (step e)) a))
    (hπ : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π)
    (H : ℕ) (hH : 0 < H) (κ : ℝ≥0) (k m : ℕ) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) (a+k+1))) _
      (restoredStoppedLaw e f hef a z₀ r ε α g π H hH κ k m) := by
  apply Measurable.subtype_mk
  have hm := (bufferStageStoppedProbability_rows e f a z₀ r ε α g π hπ H hH κ k).subtype_val
  have hu : rowSigma (BelowHeight (realPosition (step e)) (a+k)) ≤
      rowSigma (BelowHeight (realPosition (step e)) (a+k+1)) :=
    by simpa only [Nat.cast_one] using rowSigma_below_height_mono (realPosition (step e)) (a+k) 1
  apply Measure.measurable_of_measurable_coe
  intro U hU
  simp only [Measure.map_apply (measurable_of_countable _) hU]
  exact ((Measure.measurable_coe ((measurable_of_countable _) hU)).comp hm).mono hu le_rfl

noncomputable def bufferChildNode {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (N : AdaptedBufferNode e)
    (H : ℕ) (hH : 0 < H) (k : ℕ) (b : Bool) : AdaptedBufferNode e where
  level := N.level+k+1
  radius := bufferNextRadius R₀ N.radius ε α b
  law := restoredStoppedLaw e f hef N.level z₀ N.radius ε α g N.law H hH κ k
    (bufferRestoreLength R₀ N.radius ε α b)
  law_rows := restoredStoppedLaw_rows e f hef N.level z₀ N.radius ε α g N.law N.law_rows H hH κ k _
  active := N.active ∩ {ω | bufferFirstFailure (realPosition (step e)) f N.level (z₀+(1-ε)*N.radius) g N.law H ω = k ∧
    (BufferStageEvent (realPosition (step e)) f H z₀ N.radius ε α g (N.law ω).val ω ↔ b=true)}
  active_rows := by
    have ha := N.active_rows
    have hb := bufferStage_branch_rows e f N.level z₀ N.radius ε α g N.law N.law_rows hH k b
    have h1 := rowSigma_below_height_mono (realPosition (step e)) N.level k
    have h2 : rowSigma (BelowHeight (realPosition (step e)) (N.level+k)) ≤
        rowSigma (BelowHeight (realPosition (step e)) (N.level+k+1)) := by
      simpa only [Nat.cast_one] using rowSigma_below_height_mono (realPosition (step e)) (N.level+k) 1
    exact (h2 _ (h1 _ ha)).inter (h2 _ hb)
end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_Buffer
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def bufferRootLaw {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ a : ℝ) (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight (realPosition (step e)) a) :
    SupportedPairMeasures (PairAtHeight (realPosition (step e)) (a+1)) :=
  ⟨Measure.dirac (pairRestore e f ⌈R₀⌉₊ x), by
    apply ae_iff.mp
    rw [ae_dirac_iff (Set.to_countable _).measurableSet]
    exact pairRestore_height e f hef ⌈R₀⌉₊ a x hx⟩

noncomputable def bufferRootNode {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ a : ℝ) (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight (realPosition (step e)) a) :
    AdaptedBufferNode e where
  level := a+1
  radius := R₀
  law := fun _ => bufferRootLaw e f hef R₀ a x hx
  law_rows := measurable_const
  active := Set.univ
  active_rows := MeasurableSet.univ

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BufferTree
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def bufferNodeAt {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) : List (ℕ × Bool) → AdaptedBufferNode e
  | [] => root
  | p::l => let N := bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l
    bufferChildNode e f hef R₀ z₀ ε α g κ N (H N.radius) (hH N.radius) p.1 p.2

noncomputable def bufferNodeDecision {d : ℕ} (e f : Direction d)
    (z₀ ε α g : ℝ) (H : ℝ → ℕ) (N : AdaptedBufferNode e) (ω : Environment d) : ℕ × Bool :=
  (bufferFirstFailure (realPosition (step e)) f N.level (z₀+(1-ε)*N.radius) g N.law (H N.radius) ω,
    decide (BufferStageEvent (realPosition (step e)) f (H N.radius) z₀ N.radius ε α g (N.law ω).val ω))

noncomputable def bufferHistory {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (ω : Environment d) : ℕ → List (ℕ × Bool)
  | 0 => []
  | n+1 => let l := bufferHistory e f hef R₀ z₀ ε α g κ H hH root ω n
    bufferNodeDecision e f z₀ ε α g H (bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l) ω :: l

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def bufferTreeSuccess {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (n : ℕ) : Set (Environment d) :=
  ⋃ l : BufferWords n, {ω | ω ∈ (bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l.val).active ∧
    (bufferNodeDecision e f z₀ ε α g H (bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l.val) ω).2=true}

noncomputable def bufferWordSuccesses : List (ℕ × Bool) → ℝ
  | [] => 0
  | p::l => (if p.2 then 1 else 0)+bufferWordSuccesses l

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BufferChanceData
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma positiveBufferPlan_pos {d : ℕ} (ν : Measure (Row d)) (e f : Direction d) (r : ℝ) :
    0 < positiveBufferPlan ν e f r := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_BufferGrowthArithmetic
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def bufferCurrentNode {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (ω : Environment d) (n : ℕ) : AdaptedBufferNode e :=
  bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root (bufferHistory e f hef R₀ z₀ ε α g κ H hH root ω n)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_BufferCostBounds
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def outwardKernelMass {d : ℕ} (e f : Direction d) (H : ℕ)
    (x : Lattice d × Lattice d) (ω : Environment d) : ℝ :=
  (rawPairEndpointLaw (realPosition (step e)) H ω x
    {y | signedCoordinate f (x.2-x.1) ≤ signedCoordinate f (y.2-y.1)}).toReal

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_TwoStopSplice
attribute [-instance] _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

instance row_standardBorel (d : ℕ) : StandardBorelSpace (Row d) :=
  (show MeasurableSet {p : Direction d → ℝ≥0 | ∑ e, p e = 1} from
    (isClosed_eq (by fun_prop) continuous_const).measurableSet).standardBorel

noncomputable def stoppedObservation {d : ℕ} (S : ℕ → Set (Lattice d))
    (τ : Environment d → ℕ) (filler : Environment d) : Environment d → Environment d :=
  fun ω => stoppedRowGraft S τ ω filler

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_StoppedWindowEntropy
attribute [-instance] _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience

noncomputable def stoppedWindowOutput {d : ℕ} (e : Direction d)
    (τ σ : Environment d → ℕ) (filler : Environment d)
    (p : Environment d × Environment d) :
    Environment d × ((ℕ × HorizontalSpace e) → Row d) :=
  (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler p.1,
   upperField e (τ p.1)
    (stoppedRowGraft (fun n => BelowHeight (realPosition (step e)) n) σ p.1 p.2))

noncomputable def stoppedWindowLaw {d : ℕ} (e : Direction d) (ν : Measure (Row d))
    (Q : Measure (Environment d)) (τ σ : Environment d → ℕ) (filler : Environment d) :=
  (Q.prod (environmentLaw ν)).map (stoppedWindowOutput e τ σ filler)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_StoppedEntropySum
attribute [-instance] _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical BigOperators
namespace DirectionalTransience

noncomputable def layerInformation {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) (Q : Measure (Environment d))
    (τ : Environment d → ℕ) (filler : Environment d) : ℝ≥0∞ :=
  klDiv (Q.map (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler))
    ((environmentLaw ν).map
      (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler))

noncomputable def ownedWindowEntropy {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) (Q : Measure (Environment d))
    (τ σ : Environment d → ℕ) (filler : Environment d) : ℝ≥0∞ :=
  klDiv (stoppedWindowLaw e ν Q τ σ filler)
    ((Q.map (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler)).prod
      (Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν)))

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_AllIndexMarks
attribute [-instance] _root_.OAI.DirectionalTransience.annealedLaw_probability _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.environmentLaw_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.initialLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.quenchedKernel_markov _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.stateTrajectory_markov _root_.OAI.DirectionalTransience.state_measurableEq _root_.OAI.DirectionalTransience.state_measurableSingleton _root_.OAI.DirectionalTransience.variableHitKernel_finite _root_.OAI.DirectionalTransience.wordDiscreteMeasurable _root_.OAI.DirectionalTransience.wordMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

local instance instMeasurableSpaceOnePointSubtypeLatticeMemAddSubgroupHorizontalSpace {d : ℕ} (e : Direction d) :
    MeasurableSpace (OnePoint (HorizontalSpace e)) := borel _

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BudgetThreat
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

def WordEnvelope {d : ℕ} (e f : Direction d) (x : Lattice d)
    (H : ℕ) (b : ℕ → ℝ) (z : ℝ) (w : List (Direction d)) : Prop :=
  ∀ s ≤ H, |relativeWordDisplacement e f x s w-b s| ≤ z

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def relativeBadMass {d : ℕ} (ℓ : Vector d) (A : Set (Path d))
    (ω : Environment d) (x : Lattice d) : ℝ := relativeGoodMass ℓ Aᶜ ω x

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SingleThreat
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

def budgetThreatEvent {d k : ℕ} (e f : Direction d) (H : ℕ) (r : ℝ)
    (π : Measure (Fin k → Lattice d)) (s : ℝ) : Set (Environment d) :=
  {ω | ∃ h ≤ H, relativeBudgetMass e f h r π ω < s}

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BudgetMeasurable
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def fullTupleProfile {d k : ℕ} (e : Direction d) (a : ℝ) (H : ℕ)
    (π : LayerTupleProfile (k:=k) e a) (ω : Environment d) : LayerTupleProfile (k:=k) e (a+H) := by
  let μ := rawTupleMixture (realPosition (step e)) H π.val ω
  let ρ := π.val.map (tupleShiftUp e H)
  let : IsProbabilityMeasure ρ := by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  refine ⟨normalizeOr μ ρ,normalizeOr_probability μ ρ,?_⟩
  apply normalizeOr_ae
  · exact rawTupleMixture_support e H a π.val ω π.property.2
  · rw [ae_map_iff (measurable_of_countable _).aemeasurable (Set.to_countable _).measurableSet]
    apply π.property.2.mono
    intro x hx
    have hg : TupleSeparated e 0 x := fun _ _ _ => abs_nonneg _
    exact (tupleShiftUp_support e e H a 0 x ⟨hx,hg⟩).1

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BudgetAlgebra
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def budgetRetryEvent {d k : ℕ} (e f : Direction d) (r s : ℝ) (hr : 0 ≤ r) :
    (n H : ℕ) → (a G : ℝ) → (Environment d → BudgetProfile (k:=k) e f a G) → Set (Environment d)
  | 0,_,_,_,_ => Set.univ
  | n+1,H,a,G,π => ⋃ h : {h : ℕ // 0<h ∧ h<H},
      {ω | budgetFirstThreat e f a r s (fun ω => (π ω).toSupported) H ω = h.val} ∩
        budgetRetryEvent e f r s hr n (H-h.val) (a+h.val) (G-r)
          (fun ω => nextBudgetProfile e f h.val a G r hr (π ω) ω)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ProtectionLoss
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

noncomputable def protectionProfile {d k : ℕ} (e f : Direction d) (base G : ℝ)
    (H : ℕ → ℕ) (r : ℕ → ℝ) (hr : ∀ i, 0 ≤ r i)
    (π : Environment d → BudgetProfile (k:=k) e f base G) :
    (n : ℕ) → Environment d → BudgetProfile (k:=k) e f
      (protectionHeight base H n) (protectionGap G r n)
  | 0 => π
  | n+1 => fun ω => nextBudgetProfile e f (H n) _ _ (r n) (hr n)
      (protectionProfile e f base G H r hr π n ω) ω

def protectionFiltration {d : ℕ} (e : Direction d) (base : ℝ) (H : ℕ → ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace (Environment d)) where
  seq n := rowSigma (BelowHeight (realPosition (step e)) (protectionHeight base H n))
  mono' _ _ hij := rowSigma_mono (fun _ hx => lt_of_lt_of_le hx (protectionHeight_mono base H hij))
  le' _ := rowSigma_le _

noncomputable def protectionMass {d k : ℕ} (e f : Direction d) (base G : ℝ)
    (H : ℕ → ℕ) (r : ℕ → ℝ) (hr : ∀ i, 0 ≤ r i)
    (π : Environment d → BudgetProfile (k:=k) e f base G) (n : ℕ) (ω : Environment d) : ℝ :=
  relativeBudgetMass e f (H n) (r n) (protectionProfile e f base G H r hr π n ω).val ω

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CellAttempt
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

noncomputable def cellSeedMass {d k : ℕ} (e f : Direction d) (a G : ℝ) (Hs : ℕ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (ω : Environment d) : ℝ≥0∞ :=
  seedSeparatedRaw e f Hs G (π ω).val ω Set.univ

noncomputable def cellEarlyMass {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a G : ℝ) (Hs He : ℕ) (π : Environment d → LayerTupleProfile (k:=k) e a)
    (ω : Environment d) : ℝ :=
  relativeBudgetMass e f He (G/4) (seedSeparatedProfile e f hef a G Hs (π ω) ω).val ω

noncomputable def cellEarlyProfile {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a G : ℝ) (hG : 0 ≤ G) (Hs He : ℕ) (π : Environment d → LayerTupleProfile (k:=k) e a)
    (ω : Environment d) : BudgetProfile (k:=k) e f (a+Hs+He) (3*G/4) := by
  let q := nextBudgetProfile e f He (a+Hs) G (G/4) (by positivity)
    (seedSeparatedProfile e f hef a G Hs (π ω) ω) ω
  refine ⟨q.val,q.property.1,?_⟩
  have hg : G-G/4=3*G/4 := by ring
  simpa only [hg] using q.property.2

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CellFailure
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

noncomputable def cellLateInitial {d k : ℕ} (e f : Direction d) (hef : e.1≠f.1)
    (a c ρ : ℝ) (hc : 0 ≤ c) (hρ : 0 ≤ ρ) (Hs He : ℕ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (ω : Environment d) :
    BudgetProfile (k:=k) e f (a+Hs+He) (3*c*ρ/4) := by
  let p := cellEarlyProfile e f hef a (c*ρ) (mul_nonneg hc hρ) Hs He π ω
  refine ⟨p.val,p.property.1,?_⟩
  have heq : 3*(c*ρ)/4=3*c*ρ/4 := by ring
  simpa only [heq] using p.property.2

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_Cell
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

noncomputable def cellLateMass {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) (Hs He s : ℕ) (H : ℕ → ℕ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) : ℕ → Environment d → ℝ :=
  protectionMass e f (a+Hs+He) (3*c*ρ/4) H (lateBudget c ρ s)
    (fun i => (lateBudget_pos hc hρ s i).le)
    (cellLateInitial e f hef a c ρ hc.le hρ.le Hs He π)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CellSchedule
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped BigOperators
namespace DirectionalTransience

lemma cellOpportunity_monotone (v w m : ℕ) : Monotone (cellOpportunity v w m) := by
  intro i j hij
  by_cases hj : j < m
  · have hi : i < m := lt_of_le_of_lt hij hj
    simp only [cellOpportunity,ite_eq_left hi,ite_eq_left hj]
    exact Nat.sub_le_sub_left (Nat.mul_le_mul_left 2 (cellWidth_antitone w m hij)) v
  · simp only [cellOpportunity,ite_eq_right hj]
    exact cellOpportunity_le_end v w m i

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

noncomputable def cellRestart {d k : ℕ} (e : Direction d) (a : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (v w m i : ℕ)
    (ω : Environment d) : LayerTupleProfile (k:=k) e (a+cellOpportunity v w m i) :=
  fullTupleProfile e a (cellOpportunity v w m i) (π ω) ω

def cellFiltration {d : ℕ} (e : Direction d) (a : ℝ) (v w m : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace (Environment d)) where
  seq i := rowSigma (BelowHeight (realPosition (step e)) (a+cellOpportunity v w m i))
  mono' i j hij := by
    have hh : (cellOpportunity v w m i : ℝ) ≤ cellOpportunity v w m j :=
      by exact_mod_cast cellOpportunity_monotone v w m hij
    apply rowSigma_mono
    intro x hx
    change dot (realPosition x) (realPosition (step e)) < a+cellOpportunity v w m i at hx
    change dot (realPosition x) (realPosition (step e)) < a+cellOpportunity v w m j
    linarith only [hx,hh]
  le' _ := rowSigma_le _

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_UpperKernel
attribute [-instance] _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

lemma upperEnvironment_continuous {d : ℕ} (e : Direction d) : Continuous (upperEnvironment e) := by
  unfold upperEnvironment
  fun_prop

lemma continuous_wordWeight {d : ℕ} (x : Lattice d) (w : List (Direction d)) :
    Continuous (fun ω : Environment d => wordWeight ω x w) := by
  induction w generalizing x with
  | nil => exact continuous_const
  | cons u w ih =>
    change Continuous (fun ω : Environment d => ((ω x).1 u:ℝ)*wordWeight ω (x+step u) w)
    exact (NNReal.continuous_coe.comp ((continuous_apply u).comp (continuous_subtype_val.comp (continuous_apply x)))).mul (ih _)

lemma hitKernel_eq_tsum_words {d : ℕ} (ω : Environment d) (x : Lattice d)
    (S T : Set (Lattice d)) (hST : Disjoint S T) (A : Set (Lattice d)) :
    hitKernel S T (ω,x) A =
      ∑' w : {w : HitWord x S T // wordPath x w.val w.val.length∈A},
        ENNReal.ofReal (wordWeight ω x w.val.val) := by
  rw [←successfulWordLaw_endpoint ω x S T hST,
    Measure.map_apply (measurable_of_countable _) (Set.to_countable A).measurableSet,
    successfulWordLaw_apply]
  rfl

lemma hitKernel_lowerSemicontinuous {d : ℕ} (x : Lattice d)
    (S T : Set (Lattice d)) (hST : Disjoint S T) (A : Set (Lattice d)) :
    LowerSemicontinuous (fun ω : Environment d => hitKernel S T (ω,x) A) := by
  simp_rw [hitKernel_eq_tsum_words _ x S T hST A]
  exact lowerSemicontinuous_tsum fun w =>
    (ENNReal.continuous_ofReal.comp (continuous_wordWeight x w.val.val)).lowerSemicontinuous

lemma upperHorizontalKernel_apply {d : ℕ} (e : Direction d) (H : ℕ) (ξ : UpperRows e)
    (z : HorizontalSpace e) (A : Set (HorizontalSpace e)) :
    upperHorizontalKernel e H ξ z A =
      hitKernel (Strip (realPosition (step e)) (horizontalLift e 0 z) H)
        (Upper (realPosition (step e)) (horizontalLift e 0 z) H)
        (upperEnvironment e ξ,horizontalLift e 0 z) (horizontalProjection e ⁻¹' A) := by
  rw [upperHorizontalKernel,Kernel.coe_mk,Measure.map_apply (measurable_of_countable _) (Set.to_countable A).measurableSet]
  rfl

lemma upperHorizontalKernel_lowerSemicontinuous {d : ℕ} (e : Direction d) (H : ℕ)
    (z : HorizontalSpace e) (A : Set (HorizontalSpace e)) :
    LowerSemicontinuous (fun ξ : UpperRows e => upperHorizontalKernel e H ξ z A) := by
  simp_rw [upperHorizontalKernel_apply]
  exact (hitKernel_lowerSemicontinuous _ _ _ (disjoint_strip_upper _ _ _) _).comp
    (upperEnvironment_continuous e)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical BigOperators
namespace DirectionalTransience

lemma wordPath_endpoint_sum {d : ℕ} (x : Lattice d) (w : List (Direction d)) :
    wordPath x w w.length=x+(w.map step).sum := by
  induction w generalizing x with
  | nil => simp [wordPath]
  | cons u w ih => simp [wordPath,ih,add_assoc]

lemma wordPath_replicate_min {d : ℕ} (x : Lattice d) (u : Direction d) (k n : ℕ) :
    wordPath x (List.replicate k u) n=x+(min n k:ℕ) • step u := by
  induction k generalizing x n with
  | zero => simp [wordPath]
  | succ k ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [List.replicate_succ,wordPath,ih,min_add_add_right,succ_nsmul]
      abel

lemma exists_horizontal_word {d : ℕ} (e : Direction d) (z : HorizontalSpace e) :
    ∃ w : List (Direction d), (w.map step).sum=z.val ∧ ∀ u∈w, u.1≠e.1 := by
  have hsingle (i : Fin d) : ∃ w : List (Direction d),
      (w.map step).sum=Pi.single i (z.val i) ∧ ∀ u∈w, u.1≠e.1 := by
    by_cases hi : i=e.1
    · subst i
      refine ⟨[],?_,by simp⟩
      have hz : z.val e.1=0 := z.property
      simp [hz]
    · cases hz : z.val i with
      | ofNat n =>
        refine ⟨List.replicate n (i,true),?_,?_⟩
        · simp only [List.map_replicate,List.sum_replicate]
          funext j
          by_cases hj : j=i
          · subst j; simp [step]
          · simp [step,hj]
        · intro u hu
          have he := List.eq_of_mem_replicate hu
          simpa only [he] using hi
      | negSucc n =>
        refine ⟨List.replicate (n+1) (i,false),?_,?_⟩
        · simp only [List.map_replicate,List.sum_replicate]
          funext j
          by_cases hj : j=i
          · subst j; simp [step]; omega
          · simp [step,hj]
        · intro u hu
          have he := List.eq_of_mem_replicate hu
          simpa only [he] using hi
  have hf (s : Finset (Fin d)) : ∃ w : List (Direction d),
      (w.map step).sum=∑ i∈s, Pi.single i (z.val i) ∧ ∀ u∈w, u.1≠e.1 := by
    induction s using Finset.induction_on with
    | empty => exact ⟨[],by simp,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨v,hv,hve⟩ := hsingle i
      obtain ⟨w,hw,hwe⟩ := ih
      refine ⟨v++w,by simp [hv,hw,hi],?_⟩
      intro u hu
      rcases List.mem_append.mp hu with hu|hu
      · exact hve u hu
      · exact hwe u hu
  obtain ⟨w,hw,hwe⟩ := hf Finset.univ
  refine ⟨w,hw.trans ?_,hwe⟩
  funext j
  simp

lemma wordPath_horizontal {d : ℕ} (e : Direction d) (x : Lattice d)
    (w : List (Direction d)) (hw : ∀ u∈w, u.1≠e.1) (n : ℕ) :
    signedHeight e (wordPath x w n)=signedHeight e x := by
  induction w generalizing x n with
  | nil => rfl
  | cons u w ih =>
    cases n with
    | zero => rfl
    | succ n =>
      rw [wordPath,ih (x+step u) (fun g hg => hw g (by simp [hg]))]
      have hu := hw u (by simp)
      rw [signedHeight_add]
      simp [signedHeight, step,Ne.symm hu]

lemma positive_wordWeight {d : ℕ} (ω : Environment d)
    (hω : ∀ x u, 0<(ω x).val u) (x : Lattice d) (w : List (Direction d)) :
    0<wordWeight ω x w := by
  induction w generalizing x with
  | nil => norm_num [wordWeight]
  | cons u w ih =>
    exact mul_pos (NNReal.coe_pos.mpr (hω x u)) (ih _)

lemma upperHorizontalKernel_pos {d : ℕ} (e : Direction d) (H : ℕ) (hH : 0<H)
    (ξ : UpperRows e) (hξ : ∀ p u, 0<(ξ p).val u) (x y : HorizontalSpace e) :
    0<upperHorizontalKernel e H ξ x {y} := by
  obtain ⟨v,hv,hve⟩ := exists_horizontal_word e (y-x)
  let w := v++List.replicate H e
  have hend : wordPath (horizontalLift e 0 x) v v.length=horizontalLift e 0 y := by
    rw [wordPath_endpoint_sum,hv]
    simp only [horizontalLift,zero_zsmul,add_zero,AddSubgroup.coe_sub]
    abel
  have hy : wordPath (horizontalLift e 0 x) w w.length=horizontalLift e H y := by
    simp only [w,List.length_append,List.length_replicate]
    rw [wordPath_append_suffix,hend,wordPath_replicate_min,Nat.min_self]
    simp [horizontalLift]
  have hh : wordPath (horizontalLift e 0 x) w∈HitAt
      (Strip (realPosition (step e)) (horizontalLift e 0 x) H)
      (Upper (realPosition (step e)) (horizontalLift e 0 x) H) w.length := by
    constructor
    · rw [coordinate_mem_upper_iff,hy,signedHeight_horizontalLift,signedHeight_horizontalLift]
      omega
    · intro n hn
      rw [coordinate_mem_strip_iff,signedHeight_horizontalLift]
      by_cases hnv : n≤v.length
      · have he := wordPath_append_prefix (horizontalLift e 0 x) v (List.replicate H e) hnv
        rw [he,wordPath_horizontal e _ v hve,signedHeight_horizontalLift]
        omega
      · have hn' : n=v.length+(n-v.length) := by omega
        rw [hn',wordPath_append_suffix,hend,wordPath_replicate_min,signedHeight_add,
          signedHeight_horizontalLift]
        have hmin : min (n-v.length) H=n-v.length := by
          have hh : n<v.length+H := by simpa only [w,List.length_append,List.length_replicate] using hn
          omega
        rw [hmin]
        have he : signedHeight e ((n-v.length) • step e)=(n-v.length:ℕ) := by
          exact_mod_cast signedHeight_zsmul_step e (n-v.length:ℕ)
        rw [he]
        have hh : n<v.length+H := by simpa only [w,List.length_append,List.length_replicate] using hn
        omega
  rw [upperHorizontalKernel_apply,hitKernel_eq_tsum_words _ _ _ _ (disjoint_strip_upper _ _ _) _]
  let a : {w : HitWord (horizontalLift e 0 x)
      (Strip (realPosition (step e)) (horizontalLift e 0 x) H)
      (Upper (realPosition (step e)) (horizontalLift e 0 x) H) //
      wordPath (horizontalLift e 0 x) w.val w.val.length∈horizontalProjection e ⁻¹' {y}} :=
    ⟨⟨w,hh⟩,by change horizontalProjection e (wordPath _ w w.length)=y; rw [hy,horizontalProjection_lift]⟩
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (positive_wordWeight (upperEnvironment e ξ)
    (fun z u => hξ _ u) (horizontalLift e 0 x) w))
    (ENNReal.le_tsum (f := fun term => ENNReal.ofReal
      (wordWeight (upperEnvironment e ξ) (horizontalLift e 0 x) term.val.val)) a)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_IndependentDyadic
attribute [-instance] _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma upperEnvironment_restrict_eq {d : ℕ} (e : Direction d) (ω : Environment d)
    (x : Lattice d) (hx : 0≤dot (realPosition x) (realPosition (step e))) :
    upperEnvironment e (upperField e 0 ω) x=ω x := by
  have hh : 0 ≤ signedHeight e x := by rw [signedHeight_projection] at hx; exact_mod_cast hx
  simp only [upperEnvironment,upperField,Nat.cast_zero,zero_add,Int.toNat_of_nonneg hh,horizontalLift_projection]

lemma upperKernel_restrict {d : ℕ} (e : Direction d) (ω : Environment d) (H : ℕ) :
    upperHorizontalKernel e H (upperField e 0 ω) 0 Set.univ=
      crossingQuenched (realPosition (step e)) 0 H ω := by
  rw [upperHorizontalKernel_apply,Set.preimage_univ,crossingQuenched_eq_hitKernel]
  have hz : horizontalLift e 0 0=0 := by simp [horizontalLift]
  rw [hz]
  apply congrArg (fun μ : Measure (Lattice d) => μ Set.univ)
  apply hitKernel_congr
  intro x hx
  apply upperEnvironment_restrict_eq e ω x
  have hh := hx.1
  simpa only [realPosition,Int.cast_zero,Pi.zero_apply,dot,zero_mul,Finset.sum_const_zero] using hh

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayMap
attribute [-instance] _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

instance horizontalOnePoint_borel {d : ℕ} (e : Direction d) :
    BorelSpace (OnePoint (HorizontalSpace e)) := ⟨rfl⟩

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_Dust
attribute [-instance] _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def currentDust {d : ℕ} (e : Direction d) (A : CurrentData e) (a : ℕ) : Prop := (A.2 (a,0):ℝ)=0

lemma currentDust_measurable {d : ℕ} (e : Direction d) (a : ℕ) :
    MeasurableSet {A : CurrentData e | currentDust e A a} := by
  exact (((measurable_pi_apply (a,0)).comp measurable_snd).subtype_val) (measurableSet_singleton 0)

noncomputable def currentDustFrequency {d : ℕ} (e : Direction d) (n : ℕ) (A : CurrentData e) : ℝ :=
  ReferenceClasses.dustFrequency (currentDust e A) n

lemma currentDustFrequency_measurable {d : ℕ} (e : Direction d) (n : ℕ) :
    Measurable (currentDustFrequency e n) := by
  unfold currentDustFrequency ReferenceClasses.dustFrequency
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro a _
  exact Measurable.ite (currentDust_measurable e a) measurable_const measurable_const

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ClassFinset
attribute [-instance] _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped Classical
namespace DirectionalTransience

noncomputable def currentClassFinset {d : ℕ} (e : Direction d) (A : CurrentData e) : Finset ℕ :=
  if h : CurrentFiniteClasses e A then h.toFinset else {0}

lemma currentClassFinset_nonempty {d : ℕ} (e : Direction d) (A : CurrentData e) :
    (currentClassFinset e A).Nonempty := by
  by_cases h : CurrentFiniteClasses e A
  · rw [currentClassFinset,dite_eq_left h]
    exact ⟨ReferenceClasses.representative A.1 0,(Set.Finite.mem_toFinset h).mpr (Set.mem_range_self 0)⟩
  · simp [currentClassFinset,h]

lemma currentClassFinset_rep_mem {d : ℕ} (e : Direction d) (A : CurrentData e)
    (h : CurrentFiniteClasses e A) (a : ℕ) :
    ReferenceClasses.representative A.1 a∈currentClassFinset e A := by
  rw [currentClassFinset,dite_eq_left h]
  exact (Set.Finite.mem_toFinset h).mpr (Set.mem_range_self a)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_Sampling
attribute [-instance] _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal NNReal BigOperators Classical Topology
namespace DirectionalTransience

noncomputable def arrayOffsetTest {d : ℕ} (e : Direction d)
    (p q : ℤ×ℕ) (z : HorizontalSpace e) : C(ActualEpisodeArray e,ℝ) :=
  ⟨fun X => finiteOffsetTest z (X.2.1 (p,q)),
    (finiteOffsetTest_continuous z).comp ((continuous_apply _).comp (continuous_fst.comp continuous_snd))⟩

noncomputable def arrayProfileTest {d : ℕ} (e : Direction d)
    (j : ℤ) (p : ℤ×ℕ) (z : HorizontalSpace e) : C(ActualEpisodeArray e,ℝ) :=
  ⟨fun X => (X.2.2.1 (j,p,z)).val,by fun_prop⟩

noncomputable def arraySamplingError {d : ℕ} (e : Direction d)
    (p : ℤ×ℕ) (j : ℤ) (z : HorizontalSpace e) (n : ℕ) : C(ActualEpisodeArray e,ℝ) :=
  ⟨fun X => (n:ℝ)⁻¹*(∑ b∈Finset.range n, arrayOffsetTest e p (j,b) z X)-arrayProfileTest e j p z X,
    by fun_prop⟩

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SamplingLaw
attribute [-instance] _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

instance actualArray_borel {d : ℕ} (e : Direction d) : BorelSpace (ActualEpisodeArray e) := by
  have : BorelSpace (ℤ → StationaryCompact.MarkSpace) := inferInstance
  have : BorelSpace ((StationaryCompact.Label×StationaryCompact.Label) → OnePoint (HorizontalSpace e)) := inferInstance
  have : BorelSpace ((ℤ×StationaryCompact.Label×HorizontalSpace e) → Set.Icc (0:ℝ) 1) := inferInstance
  have : BorelSpace ((ℤ×ℕ×ℕ×ℕ×HorizontalSpace e) → Row d) := inferInstance
  have : BorelSpace (((ℤ×StationaryCompact.Label×HorizontalSpace e) → Set.Icc (0:ℝ) 1) ×
      ((ℤ×ℕ×ℕ×ℕ×HorizontalSpace e) → Row d)) := inferInstance
  have : SecondCountableTopology (((StationaryCompact.Label×StationaryCompact.Label) → OnePoint (HorizontalSpace e))) := inferInstance
  have : BorelSpace ((((StationaryCompact.Label×StationaryCompact.Label) → OnePoint (HorizontalSpace e))) ×
      (((ℤ×StationaryCompact.Label×HorizontalSpace e) → Set.Icc (0:ℝ) 1) ×
      ((ℤ×ℕ×ℕ×ℕ×HorizontalSpace e) → Row d))) := inferInstance
  have : SecondCountableTopology (ℤ → StationaryCompact.MarkSpace) := inferInstance
  unfold ActualEpisodeArray StationaryCompact.EpisodeArray
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayClosed
attribute [-instance] _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

noncomputable def currentOffsets {d : ℕ} (e : Direction d) (j : ℤ)
    (Y : ActualEpisodeArray e) : ReferenceClasses.Offsets (HorizontalSpace e) :=
  fun p => Y.2.1 ((j,p.1),(j,p.2))

lemma currentOffsets_continuous {d : ℕ} (e : Direction d) (j : ℤ) :
    Continuous (currentOffsets e j) := by
  unfold currentOffsets
  fun_prop

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal Classical
namespace DirectionalTransience

instance currentOffsets_secondCountable {d : ℕ} (e : Direction d) :
    SecondCountableTopology (ReferenceClasses.Offsets (HorizontalSpace e)) := inferInstance
instance currentData_secondCountable {d : ℕ} (e : Direction d) :
    SecondCountableTopology (ReferenceClasses.Data (HorizontalSpace e)) :=
  Subtype.secondCountableTopology {O : ReferenceClasses.Offsets (HorizontalSpace e) | ReferenceClasses.Consistent O}
instance currentProfiles_secondCountable {d : ℕ} (e : Direction d) :
    SecondCountableTopology (CurrentProfiles e) := inferInstance
instance currentFields_secondCountable {d : ℕ} (e : Direction d) :
    SecondCountableTopology (ReferenceClasses.AllFields (HorizontalSpace e) (Row d)) := inferInstance
instance ambientCurrentWindow_borel {d : ℕ} (e : Direction d) :
    BorelSpace (AmbientCurrentWindow e) := inferInstance
instance currentWindow_borel {d : ℕ} (e : Direction d) :
    BorelSpace (CurrentWindow e) := inferInstance

def currentWindowInclude {d : ℕ} (e : Direction d) (W : CurrentWindow e) : AmbientCurrentWindow e :=
  ((W.1.1.1,W.1.2),W.2)

lemma currentWindowInclude_continuous {d : ℕ} (e : Direction d) :
    Continuous (currentWindowInclude e) := by unfold currentWindowInclude; fun_prop

noncomputable def currentArrayWindow {d : ℕ} (e : Direction d) (j : ℤ) (m : ℕ)
    (Y : ActualEpisodeArray e) : AmbientCurrentWindow e :=
  ((currentOffsets e j Y,fun p => Y.2.2.1 (j,(j,p.1),p.2)),
    fun p => Y.2.2.2 (j,m,p.1,p.2.1,p.2.2))

lemma currentArrayWindow_continuous {d : ℕ} (e : Direction d) (j : ℤ) (m : ℕ) :
    Continuous (currentArrayWindow e j m) := by
  unfold currentArrayWindow currentOffsets
  fun_prop

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_WordPrefixes
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma wordPath_take {d : ℕ} (x : Lattice d) (w : List (Direction d)) (n i : ℕ)
    (hi : i≤n) : wordPath x (w.take n) i=wordPath x w i := by
  by_cases hn : n≤w.length
  · have hp := wordPath_append_prefix x (w.take n) (w.drop n)
      (n:=i) (by simpa only [List.length_take,Nat.min_eq_left hn] using hi)
    simpa only [List.take_append_drop] using hp.symm
  · rw [List.take_of_length_le (by omega)]

noncomputable def wordPrefix {d : ℕ} (e : Direction d) (x : Lattice d) (h : ℕ)
    (w : List (Direction d)) := w.take (wordFirstHitTime e x h w)

lemma wordFirstHitTime_le_end {d : ℕ} (e : Direction d) (x : Lattice d) (h H : ℕ)
    (hh : h≤H) (w : CoordinateWord e x H) : wordFirstHitTime e x h w.val≤w.val.length := by
  apply wordFirstHitTime_le
  rw [wordPath_hit_exact]
  omega

lemma wordPrefix_length {d : ℕ} (e : Direction d) (x : Lattice d) (h H : ℕ)
    (hh : h≤H) (w : CoordinateWord e x H) : (wordPrefix e x h w.val).length=wordFirstHitTime e x h w.val := by
  simp only [wordPrefix,List.length_take,Nat.min_eq_left (wordFirstHitTime_le_end e x h H hh w)]

lemma wordPrefix_hit {d : ℕ} (e : Direction d) (x : Lattice d) (h H : ℕ)
    (hh : h≤H) (w : CoordinateWord e x H) :
    wordPath x (wordPrefix e x h w.val)∈HitAt (Strip (realPosition (step e)) x h)
      (Upper (realPosition (step e)) x h) (wordPrefix e x h w.val).length := by
  rw [wordPrefix_length e x h H hh w]
  constructor
  · rw [coordinate_mem_upper_iff]
    unfold wordPrefix
    rw [wordPath_take x w.val _ _ le_rfl]
    exact wordFirstHitTime_spec e x h w.val ⟨w.val.length,by
      rw [wordPath_hit_exact]; omega⟩
  · intro i hi
    rw [coordinate_mem_strip_iff]
    unfold wordPrefix
    rw [wordPath_take x w.val _ i hi.le]
    refine ⟨?_,wordFirstHitTime_min e x h w.val hi⟩
    have h := (coordinate_mem_strip_iff e x _ H).mp
      (w.property.2 i (hi.trans_le (wordFirstHitTime_le_end e x h H hh w)))
    exact h.1

noncomputable def coordinateWordPrefix {d : ℕ} (e : Direction d) (x : Lattice d)
    (h H : ℕ) (hh : h≤H) (w : CoordinateWord e x H) : CoordinateWord e x h :=
  ⟨wordPrefix e x h w.val,wordPrefix_hit e x h H hh w⟩

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeRetention
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

def episodeMeasure {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}
    (q : EpisodeState (k:=k) e f r) : Measure (Fin k → Lattice d) := q.profile.val

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeCountLedger
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

noncomputable def episodeStageIncomplete {d k : ℕ} (e f : Direction d) (r : ℝ → ℝ)
    (fexp g χ b : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r) (ω : Environment d) : Prop :=
  ¬episodeStageGrows e f r fexp g χ b N q ω ∧ ¬episodeStageFails e f r fexp g χ b N q ω

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayProfileConsistency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

lemma array_offset_symm {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (h : ArrayOffsetsConsistent e Y) (p q : StationaryCompact.Label)
    (z : HorizontalSpace e) (ho : Y.2.1 (p,q)=(z:OnePoint (HorizontalSpace e))) :
    Y.2.1 (q,p)=((-z:HorizontalSpace e):OnePoint (HorizontalSpace e)) := by
  let E := Denumerable.eqv StationaryCompact.Label
  have hs := (h E.symm).symm (E p) (E q) z
  simpa only [selectedOffsets,Equiv.symm_apply_apply] using hs (by simpa [selectedOffsets] using ho)

lemma dust_isolated {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (hO : ArrayOffsetsConsistent e Y) (hP : ArrayProfilesConsistent e Y)
    (hzero : ∀ p q z, p≠q → arrayProfileTest e q.1 p z Y=0 → arrayOffsetTest e p q z Y=0)
    (p q : StationaryCompact.Label) (hpq : p≠q)
    (hdust : arrayProfileTest e p.1 p 0 Y=0) (z : HorizontalSpace e) :
    Y.2.1 (p,q)≠(z:OnePoint (HorizontalSpace e)) := by
  intro ho
  have hrev := array_offset_symm e Y hO p q z ho
  have hp := congrArg Subtype.val (hP.1 p.1 p q z (-z) ho)
  have hprofile : arrayProfileTest e p.1 q (-z) Y=0 := by
    change (Y.2.2.1 (p.1,q,-z)).val=0
    simp only [add_neg_cancel] at hp
    exact hp.symm.trans hdust
  have htest := hzero q p (-z) hpq.symm hprofile
  simp [arrayOffsetTest,finiteOffsetTest,hrev] at htest

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayMarkTests
attribute [-instance] _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

lemma arrayMark_iterate {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (r : ℕ) (i : ℤ) : (StationaryCompact.shift^[r] Y).1 i = Y.1 (i+r) := by
  induction r generalizing i with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    change (StationaryCompact.shift^[r] Y).1 (i+1)=_
    rw [ih]
    simp only [Nat.cast_add,Nat.cast_one,add_assoc,add_comm (1:ℤ)]

noncomputable def stageMarkCut {d : ℕ} (e : Direction d) (B : ℝ≥0)
    (i : ℤ) : C(ActualEpisodeArray e,ℝ) :=
  (cutENNReal B).comp ⟨fun Y => ((Y.1 i).2.1).toENNReal,
    ENat.continuous_toENNReal.comp (by fun_prop)⟩

noncomputable def dropMarkCut {d : ℕ} (e : Direction d) (B : ℝ≥0)
    (i : ℤ) : C(ActualEpisodeArray e,ℝ) :=
  (cutENNReal B).comp ⟨fun Y => (Y.1 i).2.2,by fun_prop⟩

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayPermutation
attribute [-instance] _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter BoundedContinuousFunction
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def anchorsPerm {d : ℕ} (e : Direction d) (σ : Equiv.Perm ℕ)
    (E : EpisodeAnchors e) : EpisodeAnchors e := E ∘ labelPerm σ
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayWindowMarks
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal NNReal Classical BigOperators
namespace DirectionalTransience

lemma expNeg_le_one (C : ℝ≥0∞) : expNeg C≤1 := by
  rw [←EReal.exp_zero]
  change EReal.exp (-(C:EReal)) ≤ EReal.exp 0
  simpa only [EReal.expOrderIso_apply] using
    EReal.expOrderIso.monotone (show -(C:EReal) ≤ 0 from (EReal.neg_le_zero.mpr (EReal.coe_ennreal_nonneg C)))
lemma expNeg_ne_top (C : ℝ≥0∞) : expNeg C≠⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (expNeg_le_one C)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma arrayUpperRows_continuous {d : ℕ} (e : Direction d) (i : ℤ) (m a : ℕ) :
    Continuous (arrayUpperRows e i m a) := by unfold arrayUpperRows; fun_prop

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_ArrayCostGrowth
attribute [-instance] _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

noncomputable def arrayRealCost {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e) : ℝ := (Y.1 0).2.2.toReal
lemma arrayRealCost_measurable {d : ℕ} (e : Direction d) : Measurable (arrayRealCost e) := by
  exact (show Measurable (fun Y : ActualEpisodeArray e => (Y.1 0).2.2) from by fun_prop).ennreal_toReal
lemma arrayRealCost_nonneg {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e) : 0≤arrayRealCost e Y := ENNReal.toReal_nonneg

lemma arrayWindowCost_toReal {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (hc : ∀ j, (Y.1 j).2.2≠⊤) (m : ℕ) :
    (arrayWindowCost e 0 m Y).toReal=∑ j∈Finset.range m, arrayRealCost e (StationaryCompact.shift^[j] Y) := by
  rw [arrayWindowCost,ENNReal.toReal_sum (fun (j : ℕ) _ => hc (0+(j:ℤ)))]
  apply Finset.sum_congr rfl
  intro j _
  simp only [arrayRealCost,arrayMark_iterate]

lemma expNeg_toReal_of_ne_top (C : ℝ≥0∞) (hc : C≠⊤) : (expNeg C).toReal=Real.exp (-C.toReal) := by
  rw [←ENNReal.ofReal_toReal hc]
  unfold expNeg
  rw [EReal.coe_ennreal_ofReal,max_eq_left ENNReal.toReal_nonneg,←EReal.coe_neg,EReal.exp_coe,
    ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayMassSurvival
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma arrayProfileMass_total_le_one {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (hP : ArrayProfilesConsistent e Y) (i : ℤ) (p : StationaryCompact.Label) :
    (∑' z, arrayProfileMass e i p z Y)≤1 := by
  apply ENNReal.summable.tsum_le_of_sum_le
  intro s
  dsimp only [arrayProfileMass]
  rw [←ENNReal.ofReal_sum_of_nonneg (fun z _ => (Y.2.2.1 (i,p,z)).property.1)]
  exact ENNReal.ofReal_le_one.mpr (hP.2 i p s)

lemma upperHorizontalKernel_mass_sum {d : ℕ} (e : Direction d) (H : ℕ)
    (ξ : UpperRows e) (x : HorizontalSpace e) :
    (∑' z, upperHorizontalKernel e H ξ x {z})=upperHorizontalKernel e H ξ x Set.univ := by
  simpa only [Set.indicator_univ] using
    (upperHorizontalKernel e H ξ x).tsum_indicator_apply_singleton Set.univ MeasurableSet.univ

lemma arrayKernelImage_total_le_discount {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (hP : ArrayProfilesConsistent e Y) (hc : ArrayContinuation e Y)
    (i : ℤ) (m a H : ℕ) (hH : arrayWindowHeight e i m Y=H) :
    arrayKernelImage e i m a H Set.univ Y≤expNeg (arrayWindowCost e i m Y) := by
  calc
    _ = ∑' z, arrayKernelImage e i m a H {z} Y := by
      unfold arrayKernelImage
      calc
        _ = ∑' x, ∑' z, arrayProfileMass e i (i,a) x Y *
            upperHorizontalKernel e H (arrayUpperRows e i m a Y) x {z} := by
          congr 1
          funext x
          rw [ENNReal.tsum_mul_left,upperHorizontalKernel_mass_sum]
        _ = _ := ENNReal.tsum_comm
    _ ≤ ∑' z, arrayDiscountedProfile e i m a z Y := ENNReal.tsum_le_tsum (fun z => hc i m a H z hH)
    _ = expNeg (arrayWindowCost e i m Y)*(∑' z, arrayProfileMass e (i+m) (i,a) z Y) := by
      simp only [arrayDiscountedProfile,ENNReal.tsum_mul_left]
    _ ≤ expNeg (arrayWindowCost e i m Y)*1 := mul_le_mul_right (arrayProfileMass_total_le_one e Y hP _ _) _
    _ = _ := mul_one _

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma selfmass_nodrop_bound {mass q c : ℝ≥0∞} {r t : ℝ}
    (hr : 0 < r) (hm : ENNReal.ofReal r≤ mass) (hc : c≠⊤)
    (hcost : 2*t ≤ c.toReal) (hrt : Real.exp (-t) ≤ r)
    (hbound : mass*q≤expNeg c) : q≤ENNReal.ofReal (Real.exp (-t)) := by
  have hexp : expNeg c=ENNReal.ofReal (Real.exp (-c.toReal)) := by
    rw [←ENNReal.ofReal_toReal (expNeg_ne_top _),expNeg_toReal_of_ne_top c hc]
  have hb : ENNReal.ofReal r*q≤ENNReal.ofReal (Real.exp (-c.toReal)) :=
    (mul_le_mul_left hm q).trans (hbound.trans_eq hexp)
  have hr0 : ENNReal.ofReal r≠0 := (ENNReal.ofReal_pos.mpr hr).ne'
  apply (ENNReal.mul_le_mul_iff_right hr0 ENNReal.ofReal_ne_top).mp
  apply hb.trans
  rw [←ENNReal.ofReal_mul hr.le]
  apply ENNReal.ofReal_le_ofReal
  calc
    Real.exp (-c.toReal) ≤ Real.exp (-2*t) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-t)*Real.exp (-t) := by rw [←Real.exp_add]; congr 1; ring
    _ ≤ r*Real.exp (-t) := mul_le_mul_of_nonneg_right hrt (Real.exp_nonneg _)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArraySurvival
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

noncomputable def arraySurvivalThreshold {d : ℕ} (e : Direction d) (i : ℤ) (m n : ℕ)
    (ε : ℝ) (Y : ActualEpisodeArray e) : ℝ≥0∞ :=
  ENNReal.ofReal ((n:ℝ)*((expNeg (arrayWindowCost e i m Y)).toReal+ε))

noncomputable def localSurvival {d : ℕ} (e : Direction d) (ω : Environment d) (k H : ℕ)
    (z : HorizontalSpace e) : ℝ≥0∞ :=
  variableHitKernel (realPosition (step e)) H (ω,horizontalLift e k z) Set.univ

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_WindowWeak
attribute [-instance] _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory TopologicalSpace Filter
open scoped ENNReal Classical Topology
namespace DirectionalTransience

instance currentDataProfiles_secondCountable {d : ℕ} (e : Direction d) :
    SecondCountableTopology (ReferenceClasses.Data (HorizontalSpace e) × CurrentProfiles e) := inferInstance
instance currentFields_compact {d : ℕ} (e : Direction d) :
    CompactSpace (ReferenceClasses.AllFields (HorizontalSpace e) (Row d)) := inferInstance
instance currentWindow_secondCountable {d : ℕ} (e : Direction d) : SecondCountableTopology (CurrentWindow e) := inferInstance

instance currentWindow_opens {d : ℕ} (e : Direction d) : OpensMeasurableSpace (CurrentWindow e) := inferInstance
instance currentDataProfiles_borel {d : ℕ} (e : Direction d) :
    BorelSpace (ReferenceClasses.Data (HorizontalSpace e) × CurrentProfiles e) := inferInstance
instance currentDataProfiles_opens {d : ℕ} (e : Direction d) :
    OpensMeasurableSpace (ReferenceClasses.Data (HorizontalSpace e) × CurrentProfiles e) := inferInstance

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayDust
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

noncomputable def arrayDustFrequency {d : ℕ} (e : Direction d) (i : ℤ) (n : ℕ)
    (Y : ActualEpisodeArray e) : ℝ := ReferenceClasses.dustFrequency (fun a => arrayDust e i a Y) n

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_OperationalLengthMarks
attribute [-instance] _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

noncomputable def logLengthMark {d : ℕ} (e : Direction d) : C(ActualEpisodeArray e,ℝ≥0∞) :=
  ⟨fun Y => (ENNReal.log (1+(Y.1 0).1.toENNReal)).toENNReal,
    EReal.continuous_toENNReal.comp (ENNReal.continuous_log.comp
      (continuous_const.add (ENat.continuous_toENNReal.comp (by fun_prop))))⟩

noncomputable def logLengthCut {d : ℕ} (e : Direction d) (B : ℝ≥0) : C(ActualEpisodeArray e,ℝ) :=
  (cutENNReal B).comp (logLengthMark e)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Renewal_PositiveLengthMark
attribute [-instance] _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

noncomputable def lengthUnitTest {d : ℕ} (e : Direction d) : C(ActualEpisodeArray e,ℝ) :=
  (cutENNReal 1).comp ⟨fun Y => ((Y.1 0).1).toENNReal,
    ENat.continuous_toENNReal.comp (by fun_prop)⟩

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayFiniteClasses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical BigOperators Topology
namespace DirectionalTransience

lemma arrayRelated_measurable {d : ℕ} (e : Direction d) (p q : StationaryCompact.Label) :
    MeasurableSet {Y : ActualEpisodeArray e | ArrayRelated e Y p q} := by
  simp only [ArrayRelated,Set.ofPred_exists]
  exact MeasurableSet.iUnion fun z => measurableSet_eq_fun (by fun_prop) measurable_const

lemma array_offset_self {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (h : ArrayOffsetsConsistent e Y) (p : StationaryCompact.Label) :
    Y.2.1 (p,p)=(0:HorizontalSpace e) := by
  exact (h (fun _ => p)).self 0

lemma array_offset_add {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (h : ArrayOffsetsConsistent e Y) (p q r : StationaryCompact.Label)
    (z w : HorizontalSpace e) (hz : Y.2.1 (p,q)=(z:OnePoint (HorizontalSpace e)))
    (hw : Y.2.1 (q,r)=(w:OnePoint (HorizontalSpace e))) :
    Y.2.1 (p,r)=((z+w:HorizontalSpace e):OnePoint (HorizontalSpace e)) := by
  let E := Denumerable.eqv StationaryCompact.Label
  have hs := (h E.symm).add (E p) (E q) (E r) z w
  simpa only [selectedOffsets,Equiv.symm_apply_apply] using hs
    (by simpa [selectedOffsets] using hz) (by simpa [selectedOffsets] using hw)

lemma arrayRelated_refl {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (h : ArrayOffsetsConsistent e Y) (p : StationaryCompact.Label) : ArrayRelated e Y p p :=
  ⟨0,array_offset_self e Y h p⟩
lemma arrayRelated_symm {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (h : ArrayOffsetsConsistent e Y) {p q : StationaryCompact.Label}
    (hpq : ArrayRelated e Y p q) : ArrayRelated e Y q p := by
  obtain ⟨z,hz⟩ := hpq
  exact ⟨-z,array_offset_symm e Y h p q z hz⟩
lemma arrayRelated_trans {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (h : ArrayOffsetsConsistent e Y) {p q r : StationaryCompact.Label}
    (hpq : ArrayRelated e Y p q) (hqr : ArrayRelated e Y q r) : ArrayRelated e Y p r := by
  obtain ⟨z,hz⟩ := hpq
  obtain ⟨w,hw⟩ := hqr
  exact ⟨z+w,array_offset_add e Y h p q r z w hz hw⟩

lemma array_positive_coordinate_represented {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (hs : ∀ p j z, Tendsto (fun n => arraySamplingError e p j z (2^n) Y) atTop (𝓝 0))
    (p : StationaryCompact.Label) (j : ℤ) (z : HorizontalSpace e)
    (hp : 0<(Y.2.2.1 (j,p,z):ℝ)) :
    ∃ b, Y.2.1 (p,(j,b))=(z:OnePoint (HorizontalSpace e)) := by
  by_contra h
  have hn : ∀ b, Y.2.1 (p,(j,b))≠(z:OnePoint (HorizontalSpace e)) := by simpa using h
  have he (n : ℕ) : arraySamplingError e p j z (2^n) Y=-(Y.2.2.1 (j,p,z):ℝ) := by
    simp [arraySamplingError,arrayOffsetTest,arrayProfileTest,finiteOffsetTest,hn]
  have hlim := hs p j z
  simp_rw [he] at hlim
  have hz := tendsto_nhds_unique hlim tendsto_const_nhds
  linarith

lemma array_next_full {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (κ : ℝ≥0) (hκ : 0<κ) (he : ArrayElliptic e κ Y) (hc : ArrayContinuation e Y)
    (hm : ∀ i, 0<(Y.1 i).1 ∧ (Y.1 i).1<⊤)
    (i : ℤ) (a : ℕ) (ha : 0<(Y.2.2.1 (i,(i,a),0):ℝ)) (z : HorizontalSpace e) :
    0<(Y.2.2.1 (i+1,(i,a),z):ℝ) := by
  let H := (Y.1 i).1.toNat
  have hH : arrayWindowHeight e i 1 Y=(H:ℕ∞) := by
    simp only [arrayWindowHeight,Finset.sum_range_one,Nat.cast_zero,add_zero]
    exact (ENat.natCast_toNat (hm i).2.ne).symm
  have hpH : 0<H := by
    have : (0:ℕ∞)<(H:ℕ∞) := (hm i).1.trans_eq (ENat.natCast_toNat (hm i).2.ne).symm
    exact_mod_cast this
  have hpK := upperHorizontalKernel_pos e H hpH (arrayUpperRows e i 1 a Y)
    (fun p u => hκ.trans_le (he i 1 a p.1 p.2 u)) 0 z
  have hL : 0<arrayKernelImage e i 1 a H {z} Y :=
    lt_of_lt_of_le (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr ha).ne' hpK.ne')
      (ENNReal.le_tsum (f := fun offset => arrayProfileMass e i (i,a) offset Y *
        upperHorizontalKernel e H (arrayUpperRows e i 1 a Y) offset {z}) 0)
  have hR := hL.trans_le (hc i 1 a H z hH)
  have : arrayProfileMass e (i+1) (i,a) z Y≠0 := by
    intro hz
    simp only [arrayDiscountedProfile,Nat.cast_one,hz,mul_zero,lt_self_iff_false] at hR
  exact ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr this)

lemma array_forward_survives {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (hs : ∀ p j z, Tendsto (fun n => arraySamplingError e p j z (2^n) Y) atTop (𝓝 0))
    (κ : ℝ≥0) (hκ : 0<κ) (he : ArrayElliptic e κ Y) (hc : ArrayContinuation e Y)
    (hm : ∀ i, 0<(Y.1 i).1 ∧ (Y.1 i).1<⊤)
    (hd : ∀ i a, ¬arrayDust e i a Y) (i : ℤ) (a : ℕ) :
    ∃ b, ArrayRelated e Y (i,a) (i+1,b) := by
  have ha : 0<(Y.2.2.1 (i,(i,a),0):ℝ) :=
    lt_of_le_of_ne (Y.2.2.1 (i,(i,a),0)).property.1 (show (Y.2.2.1 (i,(i,a),0):ℝ)≠0 from hd i a).symm
  obtain ⟨b,hb⟩ := array_positive_coordinate_represented e Y hs (i,a) (i+1) 0
    (array_next_full e Y κ hκ he hc hm i a ha 0)
  exact ⟨b,0,hb⟩

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_StationaryMonotone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

noncomputable def arrayLink {d : ℕ} (e : Direction d) (i : ℤ) (Y : ActualEpisodeArray e) (a : ℕ) : ℕ :=
  if h : ∃ b, ArrayRelated e Y (i,a) (i+1,b) then Nat.find h else 0

lemma arrayLink_measurable {d : ℕ} (e : Direction d) (i : ℤ) (a : ℕ) :
    Measurable (fun Y => arrayLink e i Y a) := by
  have hm : MeasurableSet {Y | ∃ b, ArrayRelated e Y (i,a) (i+1,b)} := by
    simpa only [Set.ofPred_exists] using MeasurableSet.iUnion fun b => arrayRelated_measurable e (i,a) (i+1,b)
  unfold arrayLink
  apply Measurable.dite (s := {Y | ∃ b, ArrayRelated e Y (i,a) (i+1,b)})
    (f := fun Y => Nat.find Y.property) (g := fun _ => 0)
  · exact measurable_find (fun Y : {Y | ∃ b, ArrayRelated e Y (i,a) (i+1,b)} => Y.property)
      (fun b => (arrayRelated_measurable e (i,a) (i+1,b)).preimage measurable_subtype_coe)
  · exact measurable_const
  · exact hm

lemma arrayLink_related {d : ℕ} (e : Direction d) (i : ℤ) (Y : ActualEpisodeArray e) (a : ℕ)
    (h : ∃ b, ArrayRelated e Y (i,a) (i+1,b)) :
    ArrayRelated e Y (i,a) (i+1,arrayLink e i Y a) := by
  rw [arrayLink,dite_eq_left h]
  exact Nat.find_spec h

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayMarkedEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

noncomputable def selectUpperField {d : ℕ} (e : Direction d)
    (p : ℕ × ReferenceClasses.AllFields (HorizontalSpace e) (Row d)) : UpperRows e :=
  fun z => p.2 (p.1,z)
lemma selectUpperField_measurable {d : ℕ} (e : Direction d) : Measurable (selectUpperField e) := by
  apply Measurable.of_eval
  intro z
  have hm : Measurable (fun p : ReferenceClasses.AllFields (HorizontalSpace e) (Row d) × ℕ => p.1 (p.2,z)) :=
    measurable_from_prod_countable_left (fun a => measurable_pi_apply (a,z))
  exact hm.comp measurable_swap

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_OutwardCanonicalRows
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def outwardCanonicalExcess {d : ℕ} (e f : Direction d) (A : ℝ)
    (x : Lattice d × Lattice d) : Environment d → ℝ :=
  canonicalLogExcess A (fun n => outwardKernelMass e f (n+1) x)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ProperProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

noncomputable def fillUpper {d : ℕ} (e : Direction d) (p : UpperRows e × Environment d) : Environment d :=
  rowGraft {x | 0 ≤ signedHeight e x} (upperEnvironment e p.1) p.2

lemma fillUpper_measurable {d : ℕ} (e : Direction d) : Measurable (fillUpper e) :=
  (rowGraft_measurable _).comp (((upperEnvironment_continuous e).measurable.comp measurable_fst).prodMk measurable_snd)

lemma fillUpper_eq {d : ℕ} (e : Direction d) (ξ : UpperRows e) (ω : Environment d)
    (x : Lattice d) (hx : 0 ≤ signedHeight e x) :
    fillUpper e (ξ,ω) x=upperEnvironment e ξ x := by simp [fillUpper,rowGraft,hx]

lemma fillUpper_reference {d : ℕ} (e : Direction d) (ν : Measure (Row d)) [IsProbabilityMeasure ν] :
    ((Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν)).prod (environmentLaw ν)).map (fillUpper e)=
      environmentLaw ν := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (fillUpper_measurable e),lintegral_prod _ (show Measurable (fun p => f (fillUpper e p)) from hf.comp (fillUpper_measurable e)).aemeasurable,
    ←upperField_map e ν 0]
  rw [lintegral_map ((show Measurable (fun p => f (fillUpper e p)) from hf.comp (fillUpper_measurable e)).lintegral_prod_right') ((upperField_measurable_rows e 0).mono (rowSigma_le _) le_rfl)]
  have he (η ξ : Environment d) : fillUpper e (upperField e 0 η,ξ)=rowGraft {x | 0 ≤ signedHeight e x} η ξ := by
    funext x
    by_cases hx : 0 ≤ signedHeight e x
    · simp only [fillUpper,rowGraft,Set.mem_ofPred_eq,ite_eq_left hx,upperEnvironment_restrict_eq e η x (by rw [signedHeight_projection]; exact_mod_cast hx)]
    · simp only [fillUpper,rowGraft,Set.mem_ofPred_eq,ite_eq_right hx]
  simp_rw [he]
  simpa only [Set.indicator_univ] using rowGraft_event_lintegral ν {x | 0 ≤ signedHeight e x}
    Set.univ MeasurableSet.univ f hf

lemma fillUpper_joint_reference {d : ℕ} {D : Type*} [MeasurableSpace D]
    (e : Direction d) (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (δ : Measure D) [IsFiniteMeasure δ] :
    ((δ.prod (Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν))).prod (environmentLaw ν)).map
      (fun p => (p.1.1,fillUpper e (p.1.2,p.2)))=δ.prod (environmentLaw ν) := by
  have hp : Measurable (fun p : (D × UpperRows e) × Environment d => (p.1.1,fillUpper e (p.1.2,p.2))) :=
    measurable_fst.fst.prodMk ((fillUpper_measurable e).comp (measurable_fst.snd.prodMk measurable_snd))
  apply Measure.ext_of_lintegral
  intro f hf
  have hfp : Measurable (fun p : (D × UpperRows e) × Environment d => f (p.1.1,fillUpper e (p.1.2,p.2))) := hf.comp hp
  rw [lintegral_map hf hp,lintegral_prod _ hfp.aemeasurable,
    lintegral_prod _ hfp.lintegral_prod_right'.aemeasurable,
    lintegral_prod _ hf.aemeasurable]
  apply lintegral_congr
  intro a
  have hm : Measurable (fun p : UpperRows e × Environment d => f (a,fillUpper e p)) :=
    hf.comp (measurable_const.prodMk (fillUpper_measurable e))
  rw [←lintegral_prod _ hm.aemeasurable]
  simpa only [Function.comp_apply,id_eq,fillUpper_reference e ν] using
    (lintegral_map (μ := (Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν)).prod (environmentLaw ν))
      (hf.comp (measurable_const.prodMk measurable_id)) (fillUpper_measurable e)).symm

lemma fillUpper_finite_entropy {d : ℕ} {Ω D : Type*} [MeasurableSpace Ω] [MeasurableSpace D]
    (e : Direction d) (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u : Ω → D) (hu : Measurable u) (ξ : Ω → UpperRows e) (hξ : Measurable ξ)
    (hkl : klDiv (μ.map (fun ω => (u ω,ξ ω)))
      ((μ.map u).prod (Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν)))≠∞) :
    klDiv ((μ.prod (environmentLaw ν)).map (fun p => (u p.1,fillUpper e (ξ p.1,p.2))))
      ((μ.map u).prod (environmentLaw ν))≠∞ := by
  have : Nonempty (Row d) := nonempty_of_isProbabilityMeasure ν
  let W := μ.map (fun ω => (u ω,ξ ω))
  let R := (μ.map u).prod (Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν))
  have : IsProbabilityMeasure W :=
    (Measure.isProbabilityMeasure_map_iff (hu.prodMk hξ).aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure (μ.map u) :=
    (Measure.isProbabilityMeasure_map_iff hu.aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure R := by dsimp only [R]; (first | exact Measure.isProbabilityMeasure_map (by first | exact hu.aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  have hp : Measurable (fun p : (D × UpperRows e) × Environment d => (p.1.1,fillUpper e (p.1.2,p.2))) :=
    measurable_fst.fst.prodMk ((fillUpper_measurable e).comp (measurable_fst.snd.prodMk measurable_snd))
  have hh := klDiv_map_le (W.prod (environmentLaw ν)) (R.prod (environmentLaw ν)) hp
  rw [StoppedWindow.same_auxiliary_cost] at hh
  have he : (W.prod (environmentLaw ν)).map (fun p => (p.1.1,fillUpper e (p.1.2,p.2)))=
      (μ.prod (environmentLaw ν)).map (fun p => (u p.1,fillUpper e (ξ p.1,p.2))) := by
    have hmap := Measure.map_prod_map μ (environmentLaw ν) (hu.prodMk hξ) measurable_id
    simp only [Measure.map_id] at hmap
    rw [show W.prod (environmentLaw ν)=_ from hmap,Measure.map_map hp ((hu.prodMk hξ).prodMap measurable_id)]
    rfl
  rw [he,fillUpper_joint_reference] at hh
  exact ne_top_of_le_ne_top hkl hh

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ProfileMeasureUpdate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical BigOperators
namespace DirectionalTransience

noncomputable def arrayProfileMeasure {d : ℕ} (e : Direction d) (j : ℤ)
    (p : StationaryCompact.Label) (Y : ActualEpisodeArray e) : Measure (HorizontalSpace e) :=
  Measure.sum (fun z => arrayProfileMass e j p z Y • Measure.dirac z)

lemma arrayProfileMeasure_atom {d : ℕ} (e : Direction d) (j : ℤ)
    (p : StationaryCompact.Label) (Y : ActualEpisodeArray e) (z : HorizontalSpace e) :
    arrayProfileMeasure e j p Y {z}=arrayProfileMass e j p z Y :=
  Measure.sum_smul_dirac_singleton

lemma arrayProfileImage {d : ℕ} (e : Direction d) (i : ℤ) (m a H : ℕ)
    (Y : ActualEpisodeArray e) (A : Set (HorizontalSpace e)) :
    (upperHorizontalKernel e H (arrayUpperRows e i m a Y) ∘ₘ arrayProfileMeasure e i (i,a) Y) A=
      arrayKernelImage e i m a H A Y := by
  rw [Measure.comp_eq_sum_of_countable,Measure.sum_apply _ (Set.to_countable A).measurableSet]
  simp only [Measure.smul_apply,smul_eq_mul,arrayProfileMeasure_atom]
  rfl

lemma arrayProfile_measure_update {d : ℕ} (e : Direction d) (i : ℤ) (m a H : ℕ)
    (Y : ActualEpisodeArray e) (hc : ArrayContinuation e Y) (hh : arrayWindowHeight e i m Y=H) :
    upperHorizontalKernel e H (arrayUpperRows e i m a Y) ∘ₘ arrayProfileMeasure e i (i,a) Y ≤
      expNeg (arrayWindowCost e i m Y) • arrayProfileMeasure e (i+m) (i,a) Y := by
  apply measure_le_of_atoms
  intro z
  rw [arrayProfileImage,Measure.smul_apply,smul_eq_mul,arrayProfileMeasure_atom]
  exact hc i m a H z hh

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayMarkedIterate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

lemma arrayOffset_iterate {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (n : ℕ) (p q : StationaryCompact.Label) :
    (StationaryCompact.shift^[n] Y).2.1 (p,q)=Y.2.1 ((p.1+n,p.2),(q.1+n,q.2)) := by
  induction n generalizing p q with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change (StationaryCompact.shift^[n] Y).2.1 ((p.1+1,p.2),(q.1+1,q.2))=_
    rw [ih]
    simp only [Nat.cast_add,Nat.cast_one,add_left_comm,add_comm]

lemma arrayProfile_iterate {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (n : ℕ) (j : ℤ) (p : StationaryCompact.Label) (z : HorizontalSpace e) :
    (StationaryCompact.shift^[n] Y).2.2.1 (j,p,z)=Y.2.2.1 (j+n,(p.1+n,p.2),z) := by
  induction n generalizing j p with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change (StationaryCompact.shift^[n] Y).2.2.1 (j+1,(p.1+1,p.2),z)=_
    rw [ih]
    simp only [Nat.cast_add,Nat.cast_one,add_left_comm,add_comm]

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_TailProfile
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

abbrev ZeroHeightPair {d : ℕ} (e : Direction d) :=
  {p : Lattice d × Lattice d // p ∈ PairAtHeight (realPosition (step e)) 0}

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_MarkedObservables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

noncomputable def arrayNatHeight {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e) : ℕ :=
  (Y.1 0).1.toNat
lemma arrayNatHeight_measurable {d : ℕ} (e : Direction d) : Measurable (arrayNatHeight e) :=
  (measurable_of_countable ENat.toNat).comp (by fun_prop)
lemma arrayNatHeight_positive {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (h0 : 0<(Y.1 0).1) (ht : (Y.1 0).1<⊤) : 1≤arrayNatHeight e Y := by
  have he := ENat.natCast_toNat ht.ne
  rw [←he] at h0
  exact_mod_cast h0

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical BigOperators
namespace DirectionalTransience

lemma arrayProfileMeasure_translation {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (hp : ArrayProfilesConsistent e Y) (j : ℤ) (p q : StationaryCompact.Label)
    (v : HorizontalSpace e) (hv : Y.2.1 (p,q)=(v:OnePoint (HorizontalSpace e))) :
    (arrayProfileMeasure e j q Y).map (fun x => x+v)=arrayProfileMeasure e j p Y := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have he : (fun y : HorizontalSpace e => y+v) ⁻¹' {x}={x-v} := by
    ext y
    simp only [Set.mem_preimage,Set.mem_singleton_iff]
    exact eq_sub_iff_add_eq.symm
  rw [he,arrayProfileMeasure_atom,arrayProfileMeasure_atom]
  unfold arrayProfileMass
  rw [←hp.1 j p q v (x-v) hv]
  congr 2
  abel_nf

lemma arrayProfileMeasure_iterate {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (n a : ℕ) : arrayProfileMeasure e 0 (0,a) (StationaryCompact.shift^[n] Y)=
      arrayProfileMeasure e n (n,a) Y := by
  apply Measure.ext_of_singleton
  intro z
  simp only [arrayProfileMeasure_atom,arrayProfileMass,arrayProfile_iterate,zero_add]

lemma arrayHeight_sum {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (hf : ∀ j, (Y.1 j).1<⊤) (n : ℕ) :
    arrayWindowHeight e 0 n Y=(∑ i∈Finset.range n, arrayNatHeight e (StationaryCompact.shift^[i] Y):ℕ) := by
  simp only [arrayWindowHeight,Nat.cast_sum,arrayNatHeight,arrayMark_iterate,zero_add]
  apply Finset.sum_congr rfl
  intro j _
  exact (ENat.natCast_toNat (hf j).ne).symm

lemma exp_sum_discount {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (hf : ∀ j, (Y.1 j).2.2≠⊤) (n : ℕ) :
    ENNReal.ofReal (Real.exp (∑ i∈Finset.range n, arrayRealCost e (StationaryCompact.shift^[i] Y))) *
      expNeg (arrayWindowCost e 0 n Y)=1 := by
  have hc : arrayWindowCost e 0 n Y≠⊤ := ENNReal.sum_ne_top.mpr fun j _ => hf _
  rw [←ENNReal.ofReal_toReal (expNeg_ne_top _),expNeg_toReal_of_ne_top _ hc,
    arrayWindowCost_toReal e Y hf,←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add]
  simp

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Renewal_DurationMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def VelocityPaths {d : ℕ} (v : Vector d) : Set (Path d) :=
  {X | Tendsto (fun n : ℕ => fun i => (X n i:ℝ)/(n:ℝ)) atTop (𝓝 v)}

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Renewal_VelocityWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

noncomputable def renewalVelocity {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d) : Vector d :=
  fun i => (∫ X, wordCoordinate (i,true) (firstWord ℓ X) ∂conditionedLaw ν ℓ) /
    (∫ X, ((firstWord ℓ X).length:ℝ) ∂conditionedLaw ν ℓ)

end DirectionalTransience

end

end OAI
end


