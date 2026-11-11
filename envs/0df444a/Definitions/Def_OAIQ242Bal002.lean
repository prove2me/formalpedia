-- Prove2me | Definitions.Def_OAIQ242Bal002
-- name    : OAIQ242Bal002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:49:05.562231+00:00
-- url     : https://prove2.me/theorems/f358fbf9-5189-4a64-92d4-a8d7b96e8105
-- title:
--   Definitions bundle OAIQ242Bal002 of the split of OpenAI, Directional transience implies ballisticity
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 217 declarations of OpenAI's Lean: 146 definitions, 4 inductive types or structures, 11 instances and 56 theorems. The definitions and types are `OAI.DirectionalTransience.EpisodeAtlas.advance`, `OAI.DirectionalTransience.EpisodeAtlas.run`, `OAI.DirectionalTransience.EpisodeAuxiliary`, `OAI.DirectionalTransience.EpisodeChainLedger.arrayStages`, `OAI.DirectionalTransience.EpisodeChainLedger.arrayTime`, `OAI.DirectionalTransience.EpisodeChainLedger.count`, `OAI.DirectionalTransience.EpisodeChainLedger.dropMark`, `OAI.DirectionalTransience.EpisodeChainLedger.number`, `OAI.DirectionalTransience.EpisodeChainLedger.stepMark`, `OAI.DirectionalTransience.EpisodeChainLedger.steps`, `OAI.DirectionalTransience.EpisodeChart.countedBranch`, `OAI.DirectionalTransience.EpisodeChart.countedNext`, `OAI.DirectionalTransience.EpisodeChart.failsAt`, `OAI.DirectionalTransience.EpisodeCounter`, `OAI.DirectionalTransience.EpisodeInput`, `OAI.DirectionalTransience.EpisodeLedger.scale`, `OAI.DirectionalTransience.EpisodeReady`, `OAI.DirectionalTransience.EpisodeRecordedAtlas`, `OAI.DirectionalTransience.EpisodeRecordedAtlas.advance`, `OAI.DirectionalTransience.EpisodeRecordedAtlas.reinject`, `OAI.DirectionalTransience.EpisodeRecordedAtlas.runFrom`, `OAI.DirectionalTransience.EpisodeRecordedAtlas.zero`, `OAI.DirectionalTransience.FiniteHitOscillation`, `OAI.DirectionalTransience.FirstHighRecord`, `OAI.DirectionalTransience.FirstPairRecordDeviation`, `OAI.DirectionalTransience.FirstRatioExceed`, `OAI.DirectionalTransience.FirstTubeThreat`, `OAI.DirectionalTransience.ForwardTemplate`, `OAI.DirectionalTransience.FullMarkedArray`, `OAI.DirectionalTransience.FutureEvent`, `OAI.DirectionalTransience.GridPrefix`, `OAI.DirectionalTransience.GridReached`, `OAI.DirectionalTransience.HighWordEvent`, `OAI.DirectionalTransience.HitThrough`, `OAI.DirectionalTransience.HorizontalLayer`, `OAI.DirectionalTransience.IsGaussianSequence`, `OAI.DirectionalTransience.IsProperProfile`, `OAI.DirectionalTransience.JointTubeSuccess`, `OAI.DirectionalTransience.LateFailure`, `OAI.DirectionalTransience.LateGridFailure` and 110 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `Ballisticity_Coupling_CellSeedParameters`, `Ballisticity_Coupling_SeedMedian`, `Ballisticity_Coupling_SeedOptions`, `Ballisticity_Coupling_SeedOrder`, `Ballisticity_Coupling_SeedProfile`, `Ballisticity_Coupling_SeedRadius`, `Ballisticity_Crossings_FiniteHitOscillation`, `Ballisticity_Crossings_FirstHitPairGap`, `Ballisticity_Crossings_GaussianBadCutoff`, `Ballisticity_Crossings_UniformLowerCutoff`, `Ballisticity_Entropy_BadWindowEntropy`, `Ballisticity_Estimates_AlignedRecordPrefix`, `Ballisticity_Estimates_AnchorFrameReference`, `Ballisticity_Estimates_BadOccupationLimit`, `Ballisticity_Estimates_CappedExp`, `Ballisticity_Estimates_CellBadEvent`, `Ballisticity_Estimates_CommonBoundaryRestart`, `Ballisticity_Estimates_CommonLayer`, `Ballisticity_Estimates_CommonOccupationBound`, `Ballisticity_Estimates_CommonWidthProcess`, `Ballisticity_Estimates_CommonWordWidth`, `Ballisticity_Estimates_FirstHighRecord`, `Ballisticity_Estimates_GlobalProfile`, `Ballisticity_Estimates_GlobalTuple`, `Ballisticity_Estimates_GridTrials`, `Ballisticity_Estimates_IndependentDyadic`, `Ballisticity_Estimates_IntegerMedian`, `Ballisticity_Estimates_JointPastRestart`, `Ballisticity_Estimates_LocalRadiusOrder`, `Ballisticity_Estimates_LocalStoppedSplice`, `Ballisticity_Estimates_OccupationParameters`, `Ballisticity_Estimates_OccupationSampling`, `Ballisticity_Estimates_OperationalLengthMarks`, `Ballisticity_Estimates_PairPrefix`, `Ballisticity_Estimates_PrefixVariationNonneg`, `Ballisticity_Estimates_ProperProfile`, `Ballisticity_Estimates_RecordIndexTime`, `Ballisticity_Estimates_ReferenceContinuity`, `Ballisticity_Estimates_ReferenceFeller`, `Ballisticity_Estimates_SamplingLaw`, `Ballisticity_Estimates_SingleCoverWord`, `Ballisticity_Estimates_StageClassification`, `Ballisticity_Estimates_StageRetention`, `Ballisticity_Estimates_StayUntil`, `Ballisticity_Estimates_StrictRecord`, `Ballisticity_Estimates_SurvivingLane`, `Ballisticity_Estimates_VisitTrials`, `Ballisticity_Estimates_WidthGridTail`, `Ballisticity_Estimates_WordDepartures`, `Ballisticity_Estimates_WordTemplate`, `Ballisticity_Geometry_CoordinateStrip`, `Ballisticity_Geometry_JointTubeSuccess`, `Ballisticity_Geometry_LatticeVector`, `Ballisticity_Geometry_MedianTubeFailure`, `Ballisticity_Geometry_RawWindow`, `Ballisticity_Geometry_SignedCoordinate`, `Ballisticity_Geometry_StoppedTubeEndpoint`, `Ballisticity_Geometry_TubePrefix`, `Ballisticity_Geometry_TubePrefixMass`, `Ballisticity_Geometry_WordHeightGain`, `Ballisticity_Renewal_Regeneration`, `Ballisticity_Renewal_RegenerationWords`, `Ballisticity_Stationary_ArrayMap`, `Ballisticity_Stationary_ArrayMarkedEntropy`, `Ballisticity_Stationary_ArrayTopology`, `Ballisticity_Stationary_BadCrossingEpisodes`, `Ballisticity_Stationary_EpisodeAdapted`, `Ballisticity_Stationary_EpisodeCharts`, `Ballisticity_Stationary_EpisodeCountLedger`, `Ballisticity_Stationary_EpisodeCounterChain`, `Ballisticity_Stationary_EpisodeDropLedger`, `Ballisticity_Stationary_EpisodeInjection`, `Ballisticity_Stationary_EpisodeLength`, `Ballisticity_Stationary_EpisodeNumber`, `Ballisticity_Stationary_EpisodeRecordedAtlas`, `Ballisticity_Stationary_EpisodeRetention`, `Ballisticity_Stationary_LocalEpisodeLog`, `Ballisticity_Stationary_OperationalEpisode`, `Ballisticity_Stationary_StationaryMarking`, `Ballisticity_Stationary_StationaryProfile2`, `Ballisticity_Walk_FixedQuenchedKernel`, `Ballisticity_Walk_ProfileGrowth2`, `Ballisticity_Walk_RegularPath`.
--
--   **Imports.** It imports the published bundle `Def_DirectionalBallisticity`; the bundles `OAIQ242Bal000` and `OAIQ242Bal001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ242Bal005` and `OAIQ242Bal006`; the statements `OAI.DirectionalTransience.EpisodeChainLedger.mean_episode_drops_local`, `OAI.DirectionalTransience.OperationalConstants.bad_array_finite_marks`, `OAI.DirectionalTransience.OperationalConstants.bad_dropMarkCut_upper`, `OAI.DirectionalTransience.OperationalConstants.bad_limit_averaged_survival`, `OAI.DirectionalTransience.OperationalConstants.bad_limit_drop_moment`, `OAI.DirectionalTransience.OperationalConstants.bad_limit_length_moment`, `OAI.DirectionalTransience.OperationalConstants.bad_occupation_stationary_limit`, `OAI.DirectionalTransience.OperationalConstants.conditional_episode_drops`, `OAI.DirectionalTransience.OperationalConstants.raw_dropCut_upper`, `OAI.DirectionalTransience.actual_consumed_cell_failure`, `OAI.DirectionalTransience.actual_expected_stages`, `OAI.DirectionalTransience.bad_radius_lower_escape_uniform`, `OAI.DirectionalTransience.clipping_uniform`, `OAI.DirectionalTransience.conditioned_wordRadius_integrable`, `OAI.DirectionalTransience.exists_occupationData`, `OAI.DirectionalTransience.gaussian_renewal_path_limit`, `OAI.DirectionalTransience.independent_firstHit_clipped_drift`, `OAI.DirectionalTransience.occupation_finite_bound`, `OAI.DirectionalTransience.operational_constants_exist`, `OAI.DirectionalTransience.seed_block_tests`, `OAI.DirectionalTransience.separated_seeds`, `OAI.DirectionalTransience.shared_clipped_observation_transfer`, `OAI.DirectionalTransience.shared_physical_exit_gaussian`, `OAI.DirectionalTransience.shared_uniform_good_clipped_drift`, `OAI.DirectionalTransience.shared_uniform_good_shrinking`, `OAI.DirectionalTransience.transverse_bad_radius_spread` and `OAI.DirectionalTransience.transverse_firstHit_fixed_sum_error`; the proof of `OAI.DirectionalTransience.gaussian_renewal_path_limit`.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal000
import Definitions.Def_OAIQ242Bal001

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_WordDepartures
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

noncomputable def noDropQuenched {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (ω : Environment d) : ℝ≥0∞ := quenchedKernel (ω, x) (NoDrop ℓ x)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_StayUntil
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

def StayUntil {d : ℕ} (S : Set (Lattice d)) (n : ℕ) : Set (Path d) :=
  {X | ∀ i ≤ n, X i ∈ S}

def FutureEvent {d : ℕ} (B : Lattice d → Set (Path d)) (n : ℕ) : Set (Path d) :=
  {X | (fun j => X (n + j)) ∈ B (X n)}

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_CoordinateStrip
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

def HitThrough {d : ℕ} (S T : Set (Lattice d)) (n : ℕ) : Set (Path d) :=
  ⋃ k ≤ n, HitAt S T k

def LatticeBall {d : ℕ} (x : Lattice d) (n : ℕ) : Set (Lattice d) :=
  {y | ∀ i, |y i - x i| ≤ (n : ℤ)}

def NearestNeighborPrefix {d : ℕ} (f : Path d) (n : ℕ) : Prop :=
  ∀ k < n, ∃ e : Direction d, f (k + 1) = f k + step e

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_StrictRecord
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

def PrefixDetermined {d : ℕ} (n : ℕ) (A : Set (Path d)) : Prop :=
  ∀ X Y, (∀ j ≤ n, X j = Y j) → (X ∈ A ↔ Y ∈ A)

def NextRecordAfter {d : ℕ} (ℓ : Vector d) (N n : ℕ) : Set (Path d) :=
  {X | N < n ∧ StrictRecord ℓ X n ∧ ∀ j, N < j → j < n → ¬ StrictRecord ℓ X j}

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Renewal_RegenerationWords
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

noncomputable def wordRecordCount {d : ℕ} (ℓ : Vector d) (w : List (Direction d)) : ℕ :=
  recordCount ℓ (wordPath 0 w) w.length

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

noncomputable def wordHeightGain {d : ℕ} (ℓ : Vector d) (w : List (Direction d)) : ℝ :=
  dot (realPosition (wordPath 0 w w.length)) ℓ

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_LatticeVector
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

noncomputable def wordRadius {d : ℕ} (w : List (Direction d)) : ℝ := by
  classical
  exact (Finset.range (w.length+1)).sup' (Finset.nonempty_range_iff.mpr (by omega))
    (fun j => ‖latticeVector (wordPath 0 w j)‖)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_WordTemplate
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

def WordTemplate {d : ℕ} (ℓ : Vector d) (c C C0 a : ℝ) (K : ℕ) : Set (Path d) :=
  {X | ∀ k ≤ K,
    (c*k-C0 ≤ ∑ j ∈ Finset.range k, wordHeightGain ℓ (regenerationWords ℓ X j)) ∧
    ((∑ j ∈ Finset.range k, wordHeightGain ℓ (regenerationWords ℓ X j)) ≤ C*k+C0) ∧
    ((∑ j ∈ Finset.range k, wordRadius (regenerationWords ℓ X j)) ≤ a*k)}

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_SignedCoordinate
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

noncomputable def runningHeight {d : ℕ} (ℓ : Vector d) (X : Path d) (n : ℕ) : ℝ :=
  prefixMax (fun j => dot (realPosition (X j)) ℓ) (n+1)

noncomputable def tiltedCoordinate {d : ℕ} (ℓ : Vector d) (u : Direction d)
    (b a : ℝ) (x : Lattice d) : ℝ := signedCoordinate u x + b*a*dot (realPosition x) ℓ

noncomputable def heightRatio {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a : ℝ)
    (X : Path d) (n : ℕ) : ℝ := tiltedCoordinate ℓ u b a (X n) / (a*(1+runningHeight ℓ X n))

def RatioExceed {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a H t : ℝ) (n : ℕ) : Set (Path d) :=
  AdmissiblePrefix n ∩ BoundedHeightPrefix ℓ H n ∩ {X | t < heightRatio ℓ u b a X n}

def RatioHit {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a H t : ℝ) : Set (Path d) :=
  ⋃ n, RatioExceed ℓ u b a H t n

def FirstRatioExceed {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a H t : ℝ) (n : ℕ) : Set (Path d) :=
  RatioExceed ℓ u b a H t n ∩ {X | ∀ j < n, heightRatio ℓ u b a X j ≤ t}

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Renewal_Regeneration
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

def RegenerationSupport {d : ℕ} (ℓ : Vector d) : Set (Path d) :=
  {X | X 0 = 0 ∧ ∀ n, ((renewSuffix ℓ)^[n] X) ∈
    FirstWordEvent ℓ (regenerationWords ℓ X n)}

def ForwardTemplate {d : ℕ} (ℓ : Vector d) (e : Direction d) (c C C0 a : ℝ)
    (K M : ℕ) : Set (Path d) :=
  ((fun X : Path d => fun j => X (M+j) - M • step e) ⁻¹'
    (RegenerationSupport ℓ ∩ WordTemplate ℓ c C C0 a K)) ∩
      wordCylinder 0 (List.replicate M e)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_FixedQuenchedKernel
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

noncomputable def fixedQuenchedKernel {d : ℕ} (x : Lattice d) :
    Kernel (Environment d) (Path d) :=
  quenchedKernel.comap (fun ω => (ω,x)) (measurable_id.prodMk measurable_const)

noncomputable def sharedPairKernel {d : ℕ} (x y : Lattice d) :
    Kernel (Environment d) (Path d × Path d) :=
  (fixedQuenchedKernel x).prod (fixedQuenchedKernel y)

noncomputable def sharedPairLaw {d : ℕ} (ν : Measure (Row d)) (x y : Lattice d) :
    Measure (Path d × Path d) := sharedPairKernel x y ∘ₘ environmentLaw ν

noncomputable def sharedNoDropMass {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (x y : Lattice d) : ℝ≥0∞ :=
  ∫⁻ ω, noDropQuenched ℓ x ω * noDropQuenched ℓ y ω ∂environmentLaw ν

noncomputable def sharedConditionedPairLaw {d : ℕ} (ν : Measure (Row d))
    (ℓ : Vector d) (x y : Lattice d) : Measure (Path d × Path d) :=
  (sharedNoDropMass ν ℓ x y)⁻¹ •
    (sharedPairLaw ν x y).restrict (NoDrop ℓ x ×ˢ NoDrop ℓ y)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_PairPrefix
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

def pairPrefix {d : ℕ} (n m : ℕ) (P : Path d × Path d) :
    ((i : Finset.Iic n) → Lattice d) × ((i : Finset.Iic m) → Lattice d) :=
  (Preorder.frestrictLe n P.1, Preorder.frestrictLe m P.2)

def PairPrefixDetermined {d : ℕ} (n m : ℕ) (A : Set (Path d × Path d)) : Prop :=
  ∀ P Q, (∀ j ≤ n, P.1 j = Q.1 j) → (∀ k ≤ m, P.2 k = Q.2 k) → (P ∈ A ↔ Q ∈ A)

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

noncomputable def commonWordWidth {d : ℕ} (ℓ : Vector d)
    (wv : List (Direction d) × List (Direction d)) : ℕ := wordRecordCount ℓ wv.1

def NoCommonInPrefix {d : ℕ} (ℓ : Vector d) {j : ℕ}
    (w : Fin j → List (Direction d)) (Y : Path d) : Prop :=
  ∀ k : Fin j, ¬ ∃ m, TrueRecord ℓ Y m ∧
    dot (realPosition (Y m)) ℓ = ∑ i : Fin j, if (i : ℕ) < k+1 then wordHeightGain ℓ (w i) else 0

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RecordIndexTime
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

def PairRecordDeviation {d : ℕ} (ℓ : Vector d) (e : Direction d) (H : ℕ) (z : ℝ)
    (n m : ℕ) : Set (Path d × Path d) :=
  {P | (∃ r, 0 < r ∧ r ≤ H ∧ P.1 ∈ RecordIndexPrefix ℓ r n ∧
      P.2 ∈ RecordIndexPrefix ℓ r m) ∧
    dot (realPosition (P.1 n)) ℓ = dot (realPosition (P.2 m)) ℓ ∧
    z < |signedCoordinate e (P.1 n)-signedCoordinate e (P.2 m)|}

def FirstPairRecordDeviation {d : ℕ} (ℓ : Vector d) (e : Direction d) (H : ℕ) (z : ℝ)
    (q : ℕ × ℕ) : Set (Path d × Path d) :=
  PairRecordDeviation ℓ e H z q.1 q.2 ∩
    {P | ∀ j < q.1, ∀ k < q.2, P ∉ PairRecordDeviation ℓ e H z j k}

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_IntegerMedian
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

def IsGaussianSequence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (r : ℕ → ℝ) : Prop :=
  Tendsto r atTop atTop ∧ ∀ a : ℝ, 0 < a →
    Tendsto (fun i => fluctuationScale μ S (r i) * μ.real {x | a*r i < |S x|})
      atTop (𝓝 0)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonWidthProcess
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

noncomputable def commonWidthProcess {d : ℕ} (ℓ : Vector d)
    (n : ℕ) (P : Path d × Path d) : ℕ := commonWordWidth ℓ (commonWords ℓ P n)

noncomputable def commonMeanWidth {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d) : ℝ :=
  ∫ P, (commonWidthProcess ℓ 0 P : ℝ) ∂independentConditionedPairLaw ν ℓ

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_FirstHitPairGap
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
namespace DirectionalTransience

noncomputable def firstHitPairGap {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (h : ℕ) (P : Path d × Path d) : ℝ :=
  signedCoordinate e (recordIndexPosition ℓ h P.1)-
    signedCoordinate e (recordIndexPosition ℓ h P.2)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_AlignedRecordPrefix
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
namespace DirectionalTransience

def PairOscillationTest {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (J : Set (ℕ × ℕ)) (z : ℝ) (q : ℕ × ℕ) : Set (Path d × Path d) :=
  {P | ∃ s r a b : ℕ, (s,r) ∈ J ∧ 0 < r ∧ a ≤ q.1 ∧ b ≤ q.2 ∧
    P.1 ∈ RecordIndexPrefix ℓ r q.1 ∧ P.2 ∈ RecordIndexPrefix ℓ r q.2 ∧
    P.1 ∈ RecordOrZeroPrefix ℓ s a ∧ P.2 ∈ RecordOrZeroPrefix ℓ s b ∧
    dot (realPosition (P.1 q.1)) ℓ = dot (realPosition (P.2 q.2)) ℓ ∧
    z < |(signedCoordinate e (P.1 q.1)-signedCoordinate e (P.2 q.2))-
      (signedCoordinate e (P.1 a)-signedCoordinate e (P.2 b))|}

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_TubePrefix
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
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def TubePrefixAt {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (θ z : ℝ) (s n : ℕ) : Set (Path d) :=
  HitAt (Strip ℓ x s) (Upper ℓ x s) n ∩
    {X | ∀ j ≤ s, ∃ a ≤ n,
      (fun k => X k-x) ∈ RecordOrZeroPrefix ℓ j a ∧
      |signedCoordinate f (X a-x)-(j:ℝ)*θ| ≤ z}

def TubePrefix {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (θ z : ℝ) (s : ℕ) : Set (Path d) := ⋃ n, TubePrefixAt ℓ f x θ z s n

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_TubePrefixMass
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
open MeasureTheory ProbabilityTheory Filter
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

noncomputable def tubeLayerMass {d : ℕ} (ℓ : Vector d) (f : Direction d) (a θ z : ℝ)
    (s : ℕ) (π : Measure (Lattice d)) (ω : Environment d) : ℝ≥0∞ :=
  ∑' x, if dot (realPosition x) ℓ = a then
    quenchedKernel (ω,x) (TubePrefix ℓ f x θ z s)*π {x} else 0

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def FirstTubeThreat {d : ℕ} (ℓ : Vector d) (f : Direction d) (a θ z δ : ℝ)
    (s : ℕ) (π : Measure (Lattice d)) : Set (Environment d) :=
  {ω | 0 < s ∧ (tubeLayerMass ℓ f a θ z s π ω).toReal < δ ∧
    ∀ j, 0 < j → j < s → δ ≤ (tubeLayerMass ℓ f a θ z j π ω).toReal}

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SurvivingLane
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
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
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
namespace DirectionalTransience

def PrefixContact {d : ℕ} (S : Set (Lattice d)) : Set (Path d × Path d) :=
  {Z | ∃ n m, Z.1 n = Z.2 m ∧ (∀ j < n, Z.1 j ∈ S) ∧ (∀ j < m, Z.2 j ∈ S)}

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CappedExp
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
namespace DirectionalTransience

abbrev RecordWord {d : ℕ} (ℓ : Vector d) (k : ℕ) :=
  {w : List (Direction d) // wordPath 0 w ∈ RecordIndexPrefix ℓ k w.length}

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FirstHighRecord
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
namespace DirectionalTransience

def FirstHighRecord {d : ℕ} (ℓ : Vector d) (J : ℝ) (X : Path d) (n : ℕ) : Prop :=
  TrueRecord ℓ X n ∧ J < dot (realPosition (X n)) ℓ ∧
    ∀ j < n, J < dot (realPosition (X j)) ℓ → ¬ TrueRecord ℓ X j

def HighWordEvent {d : ℕ} (ℓ : Vector d) (J : ℝ) (w : List (Direction d)) : Set (Path d) :=
  {X | X ∈ NoDrop ℓ 0 ∧ X ∈ wordCylinder 0 w ∧ FirstHighRecord ℓ J X w.length}

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_RegularPath
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
namespace DirectionalTransience

def RegularPath {d : ℕ} (ℓ : Vector d) (x : Lattice d) : Set (Path d) :=
  {X | X 0 = x ∧ (∀ n, ∃ f, X (n+1) = X n+step f) ∧ X ∈ TransientPaths ℓ}

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SingleCoverWord
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
namespace DirectionalTransience

def LateFailure {d : ℕ} (height : Lattice d → ℤ) (h B : ℤ) : Set (Path d) :=
  {X | ∃ c b, X ∈ FirstLayerHit height (h+B) c ∧ c ≤ b ∧ height (X b) < h}

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_FiniteHitOscillation
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
namespace DirectionalTransience

def FiniteHitOscillation {d : ℕ} (ℓ : Vector d) (e : Direction d) (h R : ℕ) (r : ℝ) : Set (Path d) :=
  {X | ∃ j ≤ R, r ≤ |signedCoordinate e (recordIndexPosition ℓ (h+j) X)-
    signedCoordinate e (recordIndexPosition ℓ h X)|}

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_MedianTubeFailure
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
namespace DirectionalTransience

def MedianTubeFailure {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b : ℕ → ℝ) (H : ℕ) (z : ℝ) : Set (Path d) :=
  {X | ∃ j ≤ H, z < |signedCoordinate f (recordIndexPosition ℓ j X)-b j|}

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_StoppedTubeEndpoint
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
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
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

lemma signedHeight_add_nsmul_step {d : ℕ} (e : Direction d) (x : Lattice d) (s : ℕ) :
    signedHeight e (x+s • step e) = signedHeight e x+s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [succ_nsmul,← add_assoc,signedHeight_add_step_self,ih]
    simp only [Nat.cast_add,Nat.cast_one,add_assoc]

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
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_JointTubeSuccess
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
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
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

def JointTubeSuccess {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) (H : ℕ) (z : ℝ) : Set (Path d) :=
  Hit (Strip ℓ x H) (Upper ℓ x H) ∩
    {X | (fun n => X n-x) ∉ MedianTubeFailure ℓ f b H z ∧
      (fun n => X n-x) ∉ MedianTubeFailure ℓ f (fun j => (j:ℝ)*b H/H) H z}

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_PrefixVariationNonneg
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
namespace DirectionalTransience

def layerPairPrefix {d : ℕ} (ℓ : Vector d) (height : Lattice d → ℤ)
    (x y : Lattice d) (H : ℤ) (E : Set (Lattice d × Lattice d)) (nm : ℕ × ℕ) :
    Set (Path d × Path d) :=
  (FirstLayerHit height H (nm.1+1) ×ˢ FirstLayerHit height H (nm.2+1)) ∩
  {P | (P.1 (nm.1+1),P.2 (nm.2+1)) ∈ E} ∩
  (StayUntil {z | dot (realPosition x) ℓ ≤ dot (realPosition z) ℓ} (nm.1+1) ×ˢ
   StayUntil {z | dot (realPosition y) ℓ ≤ dot (realPosition z) ℓ} (nm.2+1))

def layerPairTruthEvent {d : ℕ} (ℓ : Vector d) (height : Lattice d → ℤ)
    (x y : Lattice d) (H : ℤ) (E : Set (Lattice d × Lattice d)) : Set (Path d × Path d) :=
  ⋃ nm, layerPairPrefix ℓ height x y H E nm ∩
    (FutureNoDrop ℓ (nm.1+1) ×ˢ FutureNoDrop ℓ (nm.2+1))

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonLayer
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
namespace DirectionalTransience

def NoCommonGrid {d : ℕ} (ℓ : Vector d) (height : Lattice d → ℤ) (H B : ℤ) (m : ℕ) :
    Set (Path d × Path d) := {P | ∀ j < m, P ∉ CommonLayer ℓ height (H+j*B)}

def NoCommonInterval {d : ℕ} (ℓ : Vector d) (height : Lattice d → ℤ) (H : ℤ) (R : ℕ) :
    Set (Path d × Path d) := {P | ∀ q : ℤ, H ≤ q → q ≤ H+R → P ∉ CommonLayer ℓ height q}

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_GaussianBadCutoff
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
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
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
namespace DirectionalTransience

noncomputable def physicalFirstHitGap {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x y : Lattice d) (H : ℕ) (P : Path d × Path d) : ℝ :=
  signedCoordinate f (x-y)+ firstHitPairGap ℓ f H
    ((fun n => P.1 n-x),(fun n => P.2 n-y))

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonBoundaryRestart
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma boundaryCode_exists {d : ℕ} (ℓ : Vector d) (H : ℝ) (P : Path d × Path d) :
    ∃ a : ℕ, BoundaryAt ℓ H P (Nat.unpair a).1 (Nat.unpair a).2 ∨
      ¬ ∃ n m, BoundaryAt ℓ H P n m := by
  by_cases h : ∃ n m, BoundaryAt ℓ H P n m
  · obtain ⟨n,m,hnm⟩ := h
    exact ⟨Nat.pair n m,Or.inl (by simpa only [Nat.unpair_pair] using hnm)⟩
  · exact ⟨0,Or.inr h⟩

noncomputable def boundaryCode {d : ℕ} (ℓ : Vector d) (H : ℝ) (P : Path d × Path d) : ℕ :=
  Nat.find (boundaryCode_exists ℓ H P)

noncomputable def boundaryTimes {d : ℕ} (ℓ : Vector d) (H : ℝ) (P : Path d × Path d) : ℕ × ℕ :=
  Nat.unpair (boundaryCode ℓ H P)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_JointPastRestart
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

noncomputable def boundaryData {d : ℕ} (ℓ : Vector d) (H : ℝ) (P : Path d × Path d) :
    BoundaryData d := ⟨boundaryTimes ℓ H P,
      pairPrefix (boundaryTimes ℓ H P).1 (boundaryTimes ℓ H P).2 P⟩

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_UniformLowerCutoff
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

def LowerEscape {d : ℕ} (ν : Measure (Row d)) (e f : Direction d) (b C q : ℝ) : Prop :=
  ∃ K : ℕ, 0 < K ∧ (K:ℝ) ≤ C*fluctuationScale
    (independentConditionedPairLaw ν (realPosition (step e)))
    (commonIncrementProcess (realPosition (step e)) f 0) b ∧
    ∀ x y : Lattice d, signedHeight e x=signedHeight e y →
      q ≤ (sharedConditionedPairLaw ν (realPosition (step e)) x y).real
        (layerPairTruthEvent (realPosition (step e)) (signedHeight e) x y
          (signedHeight e x+K) {uv | 2*b ≤ |signedCoordinate f uv.1-signedCoordinate f uv.2|})

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_OccupationParameters
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

structure OccupationData {d : ℕ} (ν : Measure (Row d)) (e f : Direction d) (t : ℝ) where
  l : ℝ
  ε : ℝ
  u₀ : ℝ
  C : ℝ
  q : ℝ
  l_pos : 0 < l
  l_le_one : l ≤ 1
  ε_pos : 0 < ε
  u₀_pos : 0 < u₀
  C_pos : 0 < C
  q_pos : 0 < q
  doubling : (2:ℝ)^((7:ℝ)/4) ≤ 4/(1+4*ε)
  upper : ∀ u : ℝ, u₀ ≤ u →
    fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) u*
      (independentConditionedPairLaw ν (realPosition (step e))).real
        {P | l*u < |commonIncrementProcess (realPosition (step e)) f 0 P|} ≤ ε →
    ∀ x y : Lattice d, signedHeight e x=signedHeight e y → |signedCoordinate f (x-y)|=u →
    ∀ b R : ℝ, b ≤ u → u ≤ R →
    let H := ⌊t*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) u⌋₊
    0 < H ∧ u^((3:ℝ)/2)+t/(128*commonMeanWidth ν (realPosition (step e)))*u^((3:ℝ)/2) ≤
      ∫ P, observedPotential b R
        (signedCoordinate f ((boundaryData (realPosition (step e)) ((signedHeight e x+H:ℤ):ℝ) P).endpoints.1-
          (boundaryData (realPosition (step e)) ((signedHeight e x+H:ℤ):ℝ) P).endpoints.2))
        ∂sharedConditionedPairLaw ν (realPosition (step e)) x y
  shrink : ∀ u : ℝ, u₀ ≤ u →
    fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) u*
      (independentConditionedPairLaw ν (realPosition (step e))).real
        {P | l*u < |commonIncrementProcess (realPosition (step e)) f 0 P|} ≤ ε →
    ∀ x y : Lattice d, signedHeight e x=signedHeight e y → |signedCoordinate f (x-y)|=u →
    (sharedConditionedPairLaw ν (realPosition (step e)) x y).real
      {P | ∃ h ≤ ⌊t*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) u⌋₊,
        |physicalFirstHitGap (realPosition (step e)) f x y h P| ≤ u/2} ≤
      8*Real.exp (-commonMeanWidth ν (realPosition (step e))/(16*t))
  escape : ∀ b : ℝ, (b=u₀ ∨ ∃ D : ℝ, u₀ ≤ D ∧
      ε ≤ fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) D*
        (independentConditionedPairLaw ν (realPosition (step e))).real
          {P | l*D < |commonIncrementProcess (realPosition (step e)) f 0 P|} ∧ b=4*D) →
      LowerEscape ν e f b C q

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonOccupationBound
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

def PhysicalGapExit {d : ℕ} (e f : Direction d) (R : ℝ) (H : ℕ)
    (i : Lattice d × Lattice d) : Set (Path d × Path d) :=
  {P | ∃ j < H, R ≤ |physicalFirstHitGap (realPosition (step e)) f i.1 i.2 j P|}

end DirectionalTransience

end

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

noncomputable def seedEndpointRaw {d : ℕ} (e : Direction d) (H : ℕ)
    (R : Lattice d → Lattice d → Prop) (μ : Measure (Lattice d)) (ω : Environment d) : Measure (Lattice d) :=
  μ.bind (fun x => (variableHitKernel (realPosition (step e)) H (ω,x)).restrict {y | R x y})

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

def SeedProfile {d : ℕ} (e : Direction d) (a : ℤ) :=
  {μ : ProbabilityMeasure (Lattice d) // ∀ᵐ x ∂μ.toMeasure, signedHeight e x=a}

noncomputable def SeedProfile.measure {d : ℕ} {e : Direction d} {a : ℤ} (μ : SeedProfile e a) : Measure (Lattice d) := μ.val.toMeasure
instance SeedProfile.probability {d : ℕ} {e : Direction d} {a : ℤ} (μ : SeedProfile e a) : IsProbabilityMeasure μ.measure := μ.val.property

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def SeedCentral {d : ℕ} (f : Direction d) (H : ℕ) (θ z : ℝ) (x y : Lattice d) : Prop :=
  |signedCoordinate f (y-x)-(H:ℝ)*θ| ≤ z

def SeedJump {d : ℕ} (f : Direction d) (H : ℕ) (s : ℤ) (θ z : ℝ) (x y : Lattice d) : Prop :=
  z < (s:ℝ)*(signedCoordinate f (y-x)-(H:ℝ)*θ)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_SeedOrder
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

def SeedOrdered {d : ℕ} (f : Direction d) (s : ℤ) (g : ℝ)
    (μ ρ : Measure (Lattice d)) : Prop :=
  ∀ x, μ {x} ≠ 0 → ∀ y, ρ {y} ≠ 0 →
    g ≤ (s:ℝ)*(signedCoordinate f y-signedCoordinate f x)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

abbrev SeedState {d : ℕ} (e : Direction d) (a : ℤ) := ℕ × (ℕ → SeedProfile e a)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_SeedOptions
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

def SeedOptions {d : ℕ} (f : Direction d) (k : ℕ) (s : ℤ) (g : ℝ)
    (δ : ℝ≥0∞) (ρ : Measure (Lattice d)) : Prop :=
  ∃ μ : Fin k → ProbabilityMeasure (Lattice d),
    (∀ i, δ • (μ i).toMeasure ≤ ρ) ∧
    ∀ i j, i<j → SeedOrdered f s g (μ i).toMeasure (μ j).toMeasure

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_SeedRadius
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def fluctuationRadius {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (s : ℝ) : ℝ :=
  if h : ∃ r : ℝ, 0 < r ∧ fluctuationScale μ S r=s then h.choose else 1

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_CellSeedParameters
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma fluctuationRadius_pos {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (s : ℝ) : 0<fluctuationRadius μ S s := by
  unfold fluctuationRadius
  split
  · rename_i h
    exact h.choose_spec.1
  · norm_num

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CellBadEvent
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

def stageBadEvent {d k : ℕ} (e f : Direction d) (H : ℕ) (Gminus Gplus : ℝ)
    (π : Measure (Fin k → Lattice d)) (p : ℝ≥0∞) : Set (Environment d) :=
  {ω | (∃ h : ℕ, 1 ≤ h ∧ h ≤ H ∧
      rawTupleMixture (realPosition (step e)) h π ω {y | TupleSeparated f Gminus y} < p) ∨
    rawTupleMixture (realPosition (step e)) H π ω {y | TupleSeparated f Gplus y} < p}

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_StageRetention
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

noncomputable def stageRetainedGap {d k : ℕ} (e f : Direction d) (a Gminus Gplus B : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (H R : ℕ) (ω : Environment d) : ℝ :=
  let h := stageStop e f a Gminus Gplus B π H R ω
  if h=H ∧ ENNReal.ofReal (Real.exp (-B))  ≤  stageTestMass e f a Gminus Gplus π H h ω
  then Gplus else Gminus

noncomputable def stageOutput {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (a Gminus Gplus B : ℝ) (π : Environment d → LayerTupleProfile (k:=k) e a)
    (H R : ℕ) (ω : Environment d) :
    BudgetProfile (k:=k) e f (a+stageStop e f a Gminus Gplus B π H R ω)
      (stageRetainedGap e f a Gminus Gplus B π H R ω) :=
  seedSeparatedProfile e f hef a (stageRetainedGap e f a Gminus Gplus B π H R ω)
    (stageStop e f a Gminus Gplus B π H R ω) (π ω) ω

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_OperationalEpisode
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

def EpisodeReady {d k : ℕ} (e f : Direction d) (r : ℝ  →  ℝ)
    (sfloor : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r) : Prop :=
  q.height<N ∧ sfloor ≤ q.scale

noncomputable def episodeStageScale {d k : ℕ} (e f : Direction d) (r : ℝ  →  ℝ)
    (fexp g χ b : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r) (ω : Environment d) : ℝ :=
  if episodeStageGrows e f r fexp g χ b N q ω
  then q.scale*Real.exp (g*b) else q.scale*Real.exp (-fexp*b)

lemma episodeStageGap {d k : ℕ} (e f : Direction d) (r : ℝ  →  ℝ)
    (fexp g χ b : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r) (ω : Environment d) :
    stageRetainedGap e f q.height (r (q.scale*Real.exp (-fexp*b)))
      (r (q.scale*Real.exp (g*b))) ((k:ℝ)*b) (fun _ => q.profile.toLayerProfile)
      (episodeStageH χ b q.scale) (N-q.height) ω=
      r (episodeStageScale e f r fexp g χ b N q ω) := by
  unfold stageRetainedGap episodeStageScale episodeStageGrows episodeStageLength
  dsimp only
  simp only [neg_mul]
  split <;> rfl

noncomputable def episodeStageNext {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ  →  ℝ) (fexp g χ b : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d) : EpisodeState (k:=k) e f r := by
  let out := stageOutput e f hef q.height (r (q.scale*Real.exp (-fexp*b)))
    (r (q.scale*Real.exp (g*b))) ((k:ℝ)*b) (fun _ => q.profile.toLayerProfile)
    (episodeStageH χ b q.scale) (N-q.height) ω
  refine ⟨q.height+episodeStageLength e f r fexp g χ b N q ω,
    episodeStageScale e f r fexp g χ b N q ω, out.val, out.property.1, ?_⟩
  filter_upwards [out.property.2] with x hx
  constructor
  · simpa only [Nat.cast_add,episodeStageLength] using hx.1
  · have hh := hx.2
    rwa [episodeStageGap] at hh

lemma episodeStageNext_height {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ  →  ℝ) (fexp g χ b : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d) :
    (episodeStageNext e f hef r fexp g χ b N q ω).height=
      q.height+episodeStageLength e f r fexp g χ b N q ω := rfl

noncomputable def episodeRun {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ  →  ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d) : ℕ  →  EpisodeState (k:=k) e f r
  | 0 => q
  | n+1 => let p := episodeRun e f hef r fexp g χ b sfloor N q ω n
    if EpisodeReady e f r sfloor N p then episodeStageNext e f hef r fexp g χ b N p ω else p

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeCharts
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma EpisodeState.ext_raw {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}
    {p q : EpisodeState (k:=k) e f r} (hh : p.height=q.height) (hs : p.scale=q.scale)
    (hm : p.profile.val=q.profile.val) : p=q := by
  cases p with | mk hp sp pp =>
    cases q with | mk hq sq pq =>
      dsimp only at hh hs hm
      subst hq
      subst sq
      have he : pp=pq := Subtype.ext hm
      subst pq
      rfl

namespace EpisodeChart
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}

lemma stop_eq (c : EpisodeChart (k:=k) e f r) (fexp g χ b : ℝ) (N : ℕ) (ω : Environment d) :
    c.stop fexp g χ b N ω=episodeStageLength e f r fexp g χ b N (c.state ω) ω := rfl

lemma growsAt_eq (c : EpisodeChart (k:=k) e f r) (fexp g χ b : ℝ) (N : ℕ) (ω : Environment d) :
    c.growsAt fexp g χ b (c.stop fexp g χ b N ω) ω ↔
      episodeStageGrows e f r fexp g χ b N (c.state ω) ω := by
  simp only [growsAt,episodeStageGrows,neg_mul]
  rfl

end EpisodeChart
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma episodeStageNext_profile {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r) (ω : Environment d) :
    (episodeStageNext e f hef r fexp g χ b N q ω).profile.val =
      (seedSeparatedProfile e f hef q.height (r (episodeStageScale e f r fexp g χ b N q ω))
        (episodeStageLength e f r fexp g χ b N q ω) q.profile.toLayerProfile ω).val := by
  change (seedSeparatedProfile e f hef q.height
    (stageRetainedGap e f q.height (r (q.scale*Real.exp (-fexp*b)))
      (r (q.scale*Real.exp (g*b))) ((k:ℝ)*b) (fun _ => q.profile.toLayerProfile)
      (episodeStageH χ b q.scale) (N-q.height) ω) _ _ ω).val = _
  rw [episodeStageGap]
  rfl

namespace EpisodeChart
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}

lemma next_state (c : EpisodeChart (k:=k) e f r) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N j : ℕ) (grow : Bool) (ω : Environment d)
    (hω : ω∈(c.next hef fexp g χ b sfloor N j grow).event) :
    (c.next hef fexp g χ b sfloor N j grow).state ω =
      episodeStageNext e f hef r fexp g χ b N (c.state ω) ω := by
  have hj : c.stop fexp g χ b N ω=j := hω.2.2.2.1
  have hg : episodeStageGrows e f r fexp g χ b N (c.state ω) ω ↔ grow=true := by
    rw [←c.growsAt_eq fexp g χ b N ω,hj]
    exact hω.2.2.2.2
  have hscale : c.nextScale fexp g b grow=episodeStageScale e f r fexp g χ b N (c.state ω) ω := by
    cases grow with
    | false =>
      have hn : ¬episodeStageGrows e f r fexp g χ b N (c.state ω) ω := by
        intro hh
        exact Bool.false_ne_true (hg.mp hh)
      simp only [nextScale,Bool.false_eq_true,ite_false, if_false,episodeStageScale,ite_eq_right hn]
      rfl
    | true =>
      have hp : episodeStageGrows e f r fexp g χ b N (c.state ω) ω := hg.mpr rfl
      simp only [nextScale,ite_true, if_true,episodeStageScale,ite_eq_left hp]
      rfl
  apply EpisodeState.ext_raw
  · change c.height+j=c.height+episodeStageLength e f r fexp g χ b N (c.state ω) ω
    rw [←c.stop_eq,hj]
  · exact hscale
  · rw [episodeStageNext_profile,←c.stop_eq,hj]
    change (seedSeparatedProfile e f hef c.height (r (c.nextScale fexp g b grow)) j (c.layerProfile ω) ω).val=_
    rw [hscale]
    rfl

lemma branch_state (c : EpisodeChart (k:=k) e f r) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N : ℕ) (ω : Environment d) (l : Option (ℕ×Bool))
    (hω : ω∈(c.branch hef fexp g χ b sfloor N l).event) :
    ω∈c.event ∧ (c.branch hef fexp g χ b sfloor N l).state ω =
      if EpisodeReady e f r sfloor N (c.state ω)
      then episodeStageNext e f hef r fexp g χ b N (c.state ω) ω else c.state ω := by
  cases l with
  | none =>
    refine ⟨hω.1,?_⟩
    rw [ite_eq_right (show ¬EpisodeReady e f r sfloor N (c.state ω) from hω.2)]
    rfl
  | some l =>
    have hr : EpisodeReady e f r sfloor N (c.state ω) := ⟨hω.2.1,hω.2.2.1⟩
    exact ⟨hω.1,by rw [ite_eq_left hr]; exact c.next_state hef fexp g χ b sfloor N l.1 l.2 ω hω⟩

end EpisodeChart

namespace EpisodeAtlas
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}
  {q : Environment d → EpisodeState (k:=k) e f r}

noncomputable def advance (A : EpisodeAtlas q) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N : ℕ) :
    EpisodeAtlas (fun ω => if EpisodeReady e f r sfloor N (q ω)
      then episodeStageNext e f hef r fexp g χ b N (q ω) ω else q ω) := by
  let := A.countable
  refine ⟨A.Label×Option (ℕ×Bool),inferInstance,
    fun l => (A.chart l.1).branch hef fexp g χ b sfloor N l.2,?_,?_⟩
  · intro ω
    obtain ⟨l,hl⟩ := A.cover ω
    obtain ⟨j,hj⟩ := (A.chart l).branch_covers hef fexp g χ b sfloor N ω hl
    exact ⟨(l,j),hj⟩
  · intro l ω hω
    obtain ⟨hl,hnext⟩ := (A.chart l.1).branch_state hef fexp g χ b sfloor N ω l.2 hω
    rw [A.correct l.1 ω hl]
    exact hnext.symm

noncomputable def run (A : EpisodeAtlas q) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N : ℕ) (n : ℕ) :
    EpisodeAtlas (fun ω => episodeRun e f hef r fexp g χ b sfloor N (q ω) ω n) := by
  induction n with
  | zero => exact A
  | succ n ih => exact ih.advance hef fexp g χ b sfloor N

lemma height_event (A : EpisodeAtlas q) (m : ℕ) :
    MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) m)] {ω | (q ω).height=m} := by
  let := A.countable
  have he : {ω | (q ω).height=m} = ⋃ l : {l : A.Label // (A.chart l).height=m}, (A.chart l.val).event := by
    ext ω
    change (q ω).height=m ↔ _
    constructor
    · intro hω
      obtain ⟨l,hl⟩ := A.cover ω
      have hh : (A.chart l).height=m := by rw [A.correct l ω hl] at hω; exact hω
      exact Set.mem_iUnion.mpr ⟨⟨l,hh⟩,hl⟩
    · intro hω
      obtain ⟨l,hl⟩ := Set.mem_iUnion.mp hω
      rw [A.correct l.val ω hl]
      exact l.property
  rw [he]
  apply MeasurableSet.iUnion
  intro l
  have hm := (A.chart l.val).measurable_event
  rwa [l.property] at hm

end EpisodeAtlas
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayTopology
attribute [-instance] _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
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

instance array_secondCountable : SecondCountableTopology (EpisodeArray H R) := inferInstance

end DirectionalTransience.StationaryCompact

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_GlobalProfile
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

noncomputable def globalEndpointProfile {d : ℕ} (e : Direction d) (H : ℕ)
    (ω : Environment d) : Measure (Lattice d) :=
  normalizeOr (variableHitKernel (realPosition (step e)) H (ω,0))
    (Measure.dirac (H • step e))

instance globalEndpointProfile_probability {d : ℕ} (e : Direction d) (H : ℕ) (ω : Environment d) :
    IsProbabilityMeasure (globalEndpointProfile e H ω) := normalizeOr_probability _ _

lemma globalEndpointProfile_measurable_below {d : ℕ} (e : Direction d) (H : ℕ) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) H)) _ (globalEndpointProfile e H) := by
  let : MeasurableSpace (Environment d) := rowSigma (BelowHeight (realPosition (step e)) H)
  apply measurable_normalizeOr _ _ _ measurable_const
  have hm := measurable_rawWordLaw_rows (realPosition (step e)) H (0:Lattice d)
  have hS : Strip (realPosition (step e)) (0:Lattice d) H⊆BelowHeight (realPosition (step e)) H := by
    intro x hx
    simpa [Strip,BelowHeight,dot,realPosition] using hx.2
  have hmap := (Measure.measurable_map (fun w : List (Direction d) => wordPath (0:Lattice d) w w.length)
      (measurable_of_countable _)).comp (hm.mono (rowSigma_mono hS) le_rfl)
  simpa only [Function.comp_def,rawWordLaw_endpoint] using hmap

noncomputable def globalHorizontalProfile {d : ℕ} (e : Direction d) (H : ℕ) (ω : Environment d) :
    Measure (HorizontalSpace e) := (globalEndpointProfile e H ω).map (horizontalProjection e)

instance globalHorizontalProfile_probability {d : ℕ} (e : Direction d) (H : ℕ) (ω : Environment d) :
    IsProbabilityMeasure (globalHorizontalProfile e H ω) :=
  (show IsProbabilityMeasure ((globalEndpointProfile e H ω).map (horizontalProjection e)) by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))

lemma globalHorizontalProfile_measurable_below {d : ℕ} (e : Direction d) (H : ℕ) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) H)) _ (globalHorizontalProfile e H) :=
  (Measure.measurable_map _ (measurable_of_countable _)).comp (globalEndpointProfile_measurable_below e H)

lemma globalHorizontalProfile_measurable {d : ℕ} (e : Direction d) (H : ℕ) :
    Measurable (globalHorizontalProfile e H) :=
  (globalHorizontalProfile_measurable_below e H).mono (rowSigma_le _) le_rfl

noncomputable def globalHorizontalCoordinate {d : ℕ} (e : Direction d) (H : ℕ)
    (ω : Environment d) (z : HorizontalSpace e) : Set.Icc (0:ℝ) 1 :=
  ⟨(globalHorizontalProfile e H ω {z}).toReal, ENNReal.toReal_nonneg,
    ENNReal.toReal_le_of_le_ofReal (by exact_mod_cast (zero_le_one: (0:ℝ)≤1)) (by simpa using prob_le_one (μ:=globalHorizontalProfile e H ω) (s:={z}))⟩

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_GlobalTuple
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

lemma globalEndpointProfile_support {d : ℕ} (e : Direction d) (H : ℕ)
    (ω : Environment d) : ∀ᵐ y ∂globalEndpointProfile e H ω,
      dot (realPosition y) (realPosition (step e))=(H:ℝ) := by
  apply normalizeOr_ae
  · apply (coordinate_hitKernel_supported e (0:Lattice d) H ω).mono
    intro y hy
    rw [signedHeight_projection,hy]
    simp [signedHeight]
  · rw [ae_dirac_iff (Set.to_countable _).measurableSet]
    rw [signedHeight_projection]
    have hh := signedHeight_add_nsmul_step e (0:Lattice d) H
    have hh : signedHeight e (H • step e) = H := by simpa [signedHeight] using hh
    exact_mod_cast hh

noncomputable def globalTupleProfile {d k : ℕ} (e : Direction d) (H : ℕ)
    (ω : Environment d) : LayerTupleProfile (k:=k) e H := by
  let μ := Measure.pi (fun _ : Fin k => globalEndpointProfile e H ω)
  refine ⟨μ,inferInstance,?_⟩
  apply ae_all_iff.mpr
  intro j
  exact (Measure.tendsto_eval_ae_ae (μ:=fun _ : Fin k => globalEndpointProfile e H ω)
    (i:=j)).eventually (globalEndpointProfile_support e H ω)

lemma globalTupleProfile_measurable_below {d k : ℕ} (e : Direction d) (H : ℕ) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) H)) _
      (globalTupleProfile (k:=k) e H) := by
  let : MeasurableSpace (Environment d) := rowSigma (BelowHeight (realPosition (step e)) H)
  apply Measurable.subtype_mk
  apply TupleKernel.measurable_countable_measure
  intro x
  change Measurable (fun ω => (Measure.pi (fun _ : Fin k => globalEndpointProfile e H ω)) {x})
  simp_rw [Measure.pi_singleton]
  exact Finset.measurable_prod _ fun j _ =>
    (Measure.measurable_coe (measurableSet_singleton _)).comp (globalEndpointProfile_measurable_below e H)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeRetention
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

noncomputable def episodeSteps {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d) : ℕ → ℕ
  | 0 => 0
  | n+1 => episodeSteps e f hef r fexp g χ b sfloor N q ω n +
      if EpisodeReady e f r sfloor N (episodeRun e f hef r fexp g χ b sfloor N q ω n) then 1 else 0

lemma episodeRun_height_mono {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d) (n : ℕ) :
    q.height ≤ (episodeRun e f hef r fexp g χ b sfloor N q ω n).height := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [episodeRun]
    split
    · rw [episodeStageNext_height]
      exact ih.trans (Nat.le_add_right _ _)
    · exact ih

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeInjection
attribute [-instance] _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

noncomputable def episodeInitial {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (sfloor : ℝ) (hR : 0 ≤ r sfloor) (t : ℕ) (ω : Environment d) :
    EpisodeState (k:=k) e f r := by
  let p := BoundedInjection.injectionProfile e f hef (r sfloor) hR t
    (globalTupleProfile (k:=k) e t ω)
  refine ⟨t+1,sfloor,p.val,p.property.1,?_⟩
  simpa only [Nat.cast_add,Nat.cast_one] using p.property.2

noncomputable def episodeFinal {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N t : ℕ)
    (ω : Environment d) : EpisodeState (k:=k) e f r :=
  episodeRun e f hef r fexp g χ b sfloor N
    (episodeInitial e f hef r sfloor hR t ω) ω N

lemma episodeFinal_gt {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N t : ℕ)
    (ω : Environment d) : t < (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω).height := by
  have hh := episodeRun_height_mono e f hef r fexp g χ b sfloor N
    (episodeInitial (k:=k) e f hef r sfloor hR t ω) ω N
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self t) hh

noncomputable def episodeBoundary {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
    (ω : Environment d) : ℕ → ℕ
  | 0 => 0
  | i+1 => let t := episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    if t<N then (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω).height else t

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeAdapted
attribute [-instance] _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

noncomputable def episodeInitialChart {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (sfloor : ℝ) (hR : 0 ≤ r sfloor) (t : ℕ) : EpisodeChart (k:=k) e f r where
  height := t+1
  scale := sfloor
  profile := fun ω => (episodeInitial (k:=k) e f hef r sfloor hR t ω).profile
  measurable_profile := by
    apply Measurable.subtype_mk
    have hm := measurable_subtype_coe.comp
      ((BoundedInjection.injectionProfile_measurable (k:=k) e f hef (r sfloor) hR t).comp
        (globalTupleProfile_measurable_below (k:=k) e t))
    exact hm.mono (rowSigma_mono (by
      intro x hx
      change dot (realPosition x) (realPosition (step e)) < ((t+1:ℕ):ℝ)
      exact hx.trans_le (by exact_mod_cast Nat.le_add_right t 1))) le_rfl
  event := Set.univ
  measurable_event := MeasurableSet.univ

noncomputable def episodeInitialAtlas {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (sfloor : ℝ) (hR : 0 ≤ r sfloor) (t : ℕ) :
    EpisodeAtlas (episodeInitial (k:=k) e f hef r sfloor hR t) where
  Label := Unit
  countable := inferInstance
  chart := fun _ => episodeInitialChart e f hef r sfloor hR t
  cover := fun _ => ⟨(),Set.mem_univ _⟩
  correct := fun _ _ _ => rfl

noncomputable def episodeFinalAtlas {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N t : ℕ) :
    EpisodeAtlas (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t) :=
  (episodeInitialAtlas (k:=k) e f hef r sfloor hR t).run hef fexp g χ b sfloor N N

lemma episodeFinal_height_event {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N t m : ℕ) :
    MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) m)]
      {ω | (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω).height=m} :=
  (episodeFinalAtlas (k:=k) e f hef r fexp g χ b sfloor hR N t).height_event m

lemma episodeBoundary_height_event {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N i m : ℕ) :
    MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) m)]
      {ω | episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i=m} := by
  induction i generalizing m with
  | zero =>
    change MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) m)] {_ω : Environment d | (0:ℕ)=m}
    exact MeasurableSet.const _
  | succ i ih =>
    let T := fun ω => episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    let U := fun t ω => (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω).height
    have he : {ω | episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω (i+1)=m} =
        ({ω | T ω=m} ∩ {ω | N ≤ m}) ∪
        ⋃ t : {t : ℕ // t < N ∧ t < m}, {ω | T ω=t} ∩ {ω | U t ω=m} := by
      ext ω
      simp only [Set.mem_ofPred_eq,Set.mem_union,Set.mem_inter_iff,Set.mem_iUnion]
      constructor
      · intro hh
        change (if T ω<N then U (T ω) ω else T ω)=m at hh
        split at hh
        · rename_i ht
          have htm : T ω< m := by rw [←hh]; exact episodeFinal_gt (k:=k) e f hef r fexp g χ b sfloor hR N (T ω) ω
          exact Or.inr ⟨⟨T ω,ht,htm⟩,rfl,hh⟩
        · rename_i ht
          exact Or.inl ⟨hh,by omega⟩
      · rintro (⟨hh,hN⟩ | ⟨t,ht,hU⟩)
        · change (if T ω<N then U (T ω) ω else T ω)=m
          rw [hh,ite_eq_right (by omega)]
        · change (if T ω<N then U (T ω) ω else T ω)=m
          rw [ht,ite_eq_left t.property.1]
          exact hU
    rw [he]
    apply MeasurableSet.union
    · exact (ih m).inter (MeasurableSet.const _)
    · apply MeasurableSet.iUnion
      intro t
      have hle : rowSigma (BelowHeight (realPosition (step e)) (t.val:ℝ)) ≤
          rowSigma (BelowHeight (realPosition (step e)) (m:ℝ)) :=
        rowSigma_mono (by
          intro x hx
          change dot (realPosition x) (realPosition (step e)) < (t.val:ℝ) at hx
          change dot (realPosition x) (realPosition (step e)) < (m:ℝ)
          exact hx.trans_le (by exact_mod_cast t.property.2.le))
      exact (hle _ (ih t.val)).inter (episodeFinal_height_event (k:=k) e f hef r fexp g χ b sfloor hR N t m)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_LocalRadiusOrder
attribute [-instance] _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

noncomputable def episodeScaleRadius {d : ℕ} (ν : Measure (Row d)) (e f : Direction d) : ℝ → ℝ :=
  fluctuationRadius (independentConditionedPairLaw ν (realPosition (step e)))
    (commonIncrementProcess (realPosition (step e)) f 0)

structure OperationalConstants {d : ℕ} (ν : Measure (Row d)) (e f : Direction d) (D : ℝ) where
  fexp : ℝ
  g : ℝ
  χ : ℝ
  K : ℝ
  b : ℝ
  sfloor : ℝ
  k : ℕ
  κ : ℝ≥0
  hk : 2 ≤ k
  hκ0 : 0 < κ
  hκ1 : κ ≤ 1
  rows : ∀ᵐ ω ∂environmentLaw ν, ∀ y u, κ ≤ (ω y).1 u
  hf : 0 < fexp
  hg : 0 < g
  hgap : g < χ
  hK : 0 < K
  hb : 0 < b
  hs : 1 ≤ sfloor
  hbκ : -Real.log κ ≤ b
  coeff : 1/g+(1+fexp/g)*D/K ≤ (1/2:ℝ)/32
  small : (1+fexp/g)*Real.exp (-(K*b))/(K*b) ≤ 1/2
  order : StageRadiusOrder (episodeScaleRadius ν e f) fexp b sfloor
  height : ∀ s, sfloor ≤ s → s*Real.exp (g*b) ≤ (episodeStageH χ b s:ℝ)
  stages : ∀ s, sfloor ≤ s → ∀ a : ℝ, ∀ π : BudgetProfile (k:=k) e f a (episodeScaleRadius ν e f s),
    environmentLaw ν (stageBadEvent e f (episodeStageH χ b s)
      (episodeScaleRadius ν e f (s*Real.exp (-fexp*b)))
      (episodeScaleRadius ν e f (s*Real.exp (g*b))) π.val
      (ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))) ≤ ENNReal.ofReal (Real.exp (-2*(K*b)))

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayMap
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

noncomputable def episodeProfile {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (ω : Environment d) (i : ℤ) :=
  globalHorizontalProfile e (t ω i) ω

instance episodeProfile_probability {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (ω : Environment d) (i : ℤ) :
    IsProbabilityMeasure (episodeProfile e t ω i) := by
  unfold episodeProfile
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma globalHorizontalProfile_joint_measurable {d : ℕ} (e : Direction d) :
    Measurable (fun p : Environment d×ℕ => globalHorizontalProfile e p.2 p.1) := by
  apply measurable_from_prod_countable_left
  intro n
  exact globalHorizontalProfile_measurable e n

abbrev EpisodeAuxiliary {d : ℕ} (e : Direction d) := (ℤ×ℕ) → (ℕ×HorizontalSpace e) → Row d
abbrev EpisodeInput {d : ℕ} (e : Direction d) := (Environment d×EpisodeAnchors e)×EpisodeAuxiliary e

lemma episodeProfile_measurable {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i) (i : ℤ) :
    Measurable (fun ω => episodeProfile e t ω i) := by
  have hn : Measurable (fun ω : Environment d => (ω,t ω i)) := measurable_id.prodMk (ht i)
  have hm := (globalHorizontalProfile_joint_measurable e).comp hn
  simpa only [Function.comp_def,episodeProfile] using hm

noncomputable def globalEpisodeAnchors {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i) :
    Kernel (Environment d) (EpisodeAnchors e) :=
  AnchorSampling.anchorKernel (episodeProfile e t)
    (episodeProfile_measurable e t ht)

instance globalEpisodeAnchors_markov {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i) :
    IsMarkovKernel (globalEpisodeAnchors e t ht) := by unfold globalEpisodeAnchors; infer_instance

noncomputable def episodeAuxiliaryLaw {d : ℕ} (e : Direction d) (ν : Measure (Row d)) :
    Measure (EpisodeAuxiliary e) :=
  Measure.infinitePi (fun _ : ℤ×ℕ => Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν))

instance episodeAuxiliaryLaw_probability {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (episodeAuxiliaryLaw e ν) := by unfold episodeAuxiliaryLaw; (first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))

noncomputable def episodeInputLaw {d : ℕ} (e : Direction d) (ν : Measure (Row d))
    (Q : Measure (Environment d)) (t : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) : Measure (EpisodeInput e) :=
  (Q.compProd (globalEpisodeAnchors e t ht)).prod (episodeAuxiliaryLaw e ν)

noncomputable def episodeCost {d : ℕ} (e : Direction d) (t : Environment d → ℤ → ℕ)
    (ω : Environment d) (i : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.log (crossingQuenched (realPosition (step e)) 0 (t ω i) ω).toReal-
    Real.log (crossingQuenched (realPosition (step e)) 0 (t ω (i+1)) ω).toReal)

noncomputable def episodeSplicedRow {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (X : EpisodeInput e)
    (i : ℤ) (m a l : ℕ) (z : HorizontalSpace e) : Row d :=
  if l<t X.1.1 (i+m)-t X.1.1 i then
    X.1.1 (horizontalLift e (t X.1.1 i+l) (X.1.2 (i,a)+z))
  else X.2 (i,m) (l,X.1.2 (i,a)+z)

noncomputable def actualArrayMap {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (X : EpisodeInput e) : ActualEpisodeArray e :=
  ⟨(fun i => ((t X.1.1 (i+1)-t X.1.1 i : ℕ),(J X.1.1 i : ℕ),episodeCost e t X.1.1 i)),
    (fun p => ((X.1.2 p.2-X.1.2 p.1 : HorizontalSpace e) : OnePoint (HorizontalSpace e))),
    (fun p => globalHorizontalCoordinate e (t X.1.1 p.1) X.1.1 (X.1.2 p.2.1+p.2.2)),
    (fun p => episodeSplicedRow e t X p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)⟩

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SamplingLaw
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

instance episodeInputLaw_finite {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i) :
    IsFiniteMeasure (episodeInputLaw e ν Q t ht) := by unfold episodeInputLaw; infer_instance

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_OccupationSampling
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

noncomputable def actualOccupationRaw {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d))
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (N : ℕ) (M : Environment d → ℕ) : Measure (ActualEpisodeArray e) :=
  StationaryCompact.episodeOccupationRaw N (episodeInputLaw e ν Q t ht)
    (actualArrayMap e t J) (fun X => M X.1.1) StationaryCompact.shift

instance actualOccupationRaw_finite {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (N : ℕ) (M : Environment d → ℕ) : IsFiniteMeasure (actualOccupationRaw e ν Q t J ht N M) := by
  unfold actualOccupationRaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal BigOperators Classical Topology
namespace DirectionalTransience

noncomputable def actualOccupation {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (N : ℕ) (M : Environment d → ℕ) : ProbabilityMeasure (ActualEpisodeArray e) := by
  haveI : Nonempty (Row d) := nonempty_of_isProbabilityMeasure ν
  exact FiniteMeasure.normalize (⟨actualOccupationRaw e ν Q t J ht N M,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ : FiniteMeasure (ActualEpisodeArray e))

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_StageClassification
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

noncomputable def episodeCount {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d)
    (test : EpisodeState (k:=k) e f r → Environment d → Prop) : ℕ → ℕ
  | 0 => 0
  | n+1 => episodeCount e f hef r fexp g χ b sfloor N q ω test n +
    if EpisodeReady e f r sfloor N (episodeRun e f hef r fexp g χ b sfloor N q ω n) ∧
      test (episodeRun e f hef r fexp g χ b sfloor N q ω n) ω then 1 else 0

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeLength
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience
namespace EpisodeLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
  (q : EpisodeState (k:=k) e f r) (ω : Environment d)

noncomputable def scale : ℕ → ℝ
  | 0 => q.scale
  | n+1 =>
    let p := episodeRun e f hef r fexp g χ b sfloor N q ω n
    if EpisodeReady e f r sfloor N p then
      if episodeStageGrows e f r fexp g χ b N p ω then
        scale n * Real.exp (g*b)
      else if episodeStageFails e f r fexp g χ b N p ω then
        scale n * Real.exp (-fexp*b)
      else scale n
    else scale n

end EpisodeLedger
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeCountLedger
attribute [-instance] _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience
namespace EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
  (ω : Environment d)

local notation "T" => episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω
local notation "Q" => episodeInitial (k:=k) e f hef r sfloor hR
local notation "LocalCount" => episodeCount e f hef r fexp g χ b sfloor N

noncomputable def count (test : EpisodeState (k:=k) e f r → Environment d → Prop) : ℕ → ℕ
  | 0 => 0
  | i+1 => count test i + if T i < N then LocalCount (Q (T i) ω) ω test N else 0

noncomputable def steps : ℕ → ℕ
  | 0 => 0
  | i+1 => steps i + if T i < N then episodeSteps e f hef r fexp g χ b sfloor N (Q (T i) ω) ω N else 0

end EpisodeChainLedger
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_LocalEpisodeLog
attribute [-instance] _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience
namespace EpisodeChart
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}

noncomputable def failsAt (c : EpisodeChart (k:=k) e f r) (fexp g χ b : ℝ) (j : ℕ) (ω : Environment d) : Prop :=
  stageTestMass e f c.height (r (c.scale*Real.exp (-fexp*b))) (r (c.scale*Real.exp (g*b)))
    c.layerProfile (episodeStageH χ b c.scale) j ω < ENNReal.ofReal (Real.exp (-((k:ℝ)*b)))

lemma measurableSet_failsAt (c : EpisodeChart (k:=k) e f r) (fexp g χ b : ℝ) (j : ℕ) :
    MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) ((c.height+j:ℕ):ℝ))]
      {ω | c.failsAt fexp g χ b j ω} := by
  have hm := measurableSet_lt
    (stageTestMass_adapted e f c.height (r (c.scale*Real.exp (-fexp*b)))
      (r (c.scale*Real.exp (g*b))) c.layerProfile c.measurable_layerProfile
      (episodeStageH χ b c.scale) j)
    (measurable_const (a:=ENNReal.ofReal (Real.exp (-((k:ℝ)*b)))))
  convert hm using 1 <;> first | rfl | (rw [Nat.cast_add]; rfl)

lemma failsAt_eq (c : EpisodeChart (k:=k) e f r) (fexp g χ b : ℝ) (N : ℕ) (ω : Environment d) :
    c.failsAt fexp g χ b (c.stop fexp g χ b N ω) ω ↔
      episodeStageFails e f r fexp g χ b N (c.state ω) ω := Iff.rfl

noncomputable def countedNext (c : EpisodeChart (k:=k) e f r) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N j : ℕ) (grow failed : Bool) : EpisodeChart (k:=k) e f r :=
  { c.next hef fexp g χ b sfloor N j grow with
    event := (c.next hef fexp g χ b sfloor N j grow).event ∩
      {ω | c.failsAt fexp g χ b j ω ↔ failed=true}
    measurable_event := (c.measurable_nextEvent fexp g χ b sfloor N j grow).inter (by
      cases failed
      · simpa only [Bool.false_eq_true,iff_false,Set.compl_ofPred] using (c.measurableSet_failsAt fexp g χ b j).compl
      · simpa only [iff_true] using c.measurableSet_failsAt fexp g χ b j) }

noncomputable def countedBranch (c : EpisodeChart (k:=k) e f r) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N : ℕ) : Option (ℕ×Bool×Bool) → EpisodeChart (k:=k) e f r
  | none => c.frozen sfloor N
  | some (j,grow,failed) => c.countedNext hef fexp g χ b sfloor N j grow failed

lemma countedBranch_covers (c : EpisodeChart (k:=k) e f r) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N : ℕ) (ω : Environment d) (hω : ω∈c.event) :
    ∃ l, ω∈(c.countedBranch hef fexp g χ b sfloor N l).event := by
  obtain ⟨l,hl⟩ := c.branch_covers hef fexp g χ b sfloor N ω hω
  cases l with
  | none => exact ⟨none,hl⟩
  | some l =>
    by_cases hf : c.failsAt fexp g χ b l.1 ω
    · exact ⟨some (l.1,l.2,true),hl,by simpa only [Set.mem_ofPred_eq,iff_true] using hf⟩
    · exact ⟨some (l.1,l.2,false),hl,by simpa only [Set.mem_ofPred_eq,Bool.false_eq_true,iff_false] using hf⟩

lemma countedBranch_state (c : EpisodeChart (k:=k) e f r) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N : ℕ) (ω : Environment d) (l : Option (ℕ×Bool×Bool))
    (hω : ω∈(c.countedBranch hef fexp g χ b sfloor N l).event) :
    ω∈c.event ∧ (c.countedBranch hef fexp g χ b sfloor N l).state ω =
      if EpisodeReady e f r sfloor N (c.state ω)
      then episodeStageNext e f hef r fexp g χ b N (c.state ω) ω else c.state ω := by
  cases l with
  | none => exact c.branch_state hef fexp g χ b sfloor N ω none hω
  | some l => exact c.branch_state hef fexp g χ b sfloor N ω (some (l.1,l.2.1)) hω.1

lemma countedBranch_record (c : EpisodeChart (k:=k) e f r) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N : ℕ) (ω : Environment d) (l : Option (ℕ×Bool×Bool))
    (hω : ω∈(c.countedBranch hef fexp g χ b sfloor N l).event) :
    (if EpisodeReady e f r sfloor N (c.state ω) then 1 else 0 : ℕ) = (if l.isSome then 1 else 0) ∧
    (if EpisodeReady e f r sfloor N (c.state ω) ∧ episodeStageFails e f r fexp g χ b N (c.state ω) ω
      then 1 else 0 : ℕ) = (if (l.map (fun z => z.2.2)).getD false then 1 else 0) := by
  cases l with
  | none =>
    have hn : ¬EpisodeReady e f r sfloor N (c.state ω) := hω.2
    simp only [hn,false_and,ite_false, if_false,Option.isSome_none,Option.map_none,Option.getD_none,Bool.false_eq_true,and_self]
  | some l =>
    have hr : EpisodeReady e f r sfloor N (c.state ω) := ⟨hω.1.2.1,hω.1.2.2.1⟩
    have hfail : episodeStageFails e f r fexp g χ b N (c.state ω) ω ↔ l.2.2=true := by
      rw [←c.failsAt_eq fexp g χ b N ω,hω.1.2.2.2.1]
      exact hω.2
    simp only [hr,true_and,ite_true, if_true,Option.isSome_some,Option.map_some,Option.getD_some,hfail]

end EpisodeChart
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeRecordedAtlas
attribute [-instance] _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

structure EpisodeRecordedAtlas {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}
    (q : Environment d → EpisodeState (k:=k) e f r) (J F : Environment d → ℕ)
    extends EpisodeAtlas q where
  stages : Label → ℕ
  failures : Label → ℕ
  stages_correct : ∀ l ω, ω∈(chart l).event → J ω=stages l
  failures_correct : ∀ l ω, ω∈(chart l).event → F ω=failures l

namespace EpisodeRecordedAtlas
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}
  {q : Environment d → EpisodeState (k:=k) e f r} {J F : Environment d → ℕ}

noncomputable def zero (A : EpisodeAtlas q) : EpisodeRecordedAtlas q (fun _ => 0) (fun _ => 0) where
  toEpisodeAtlas := A
  stages := fun _ => 0
  failures := fun _ => 0
  stages_correct := fun _ _ _ => rfl
  failures_correct := fun _ _ _ => rfl

noncomputable def advance (A : EpisodeRecordedAtlas q J F) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N : ℕ) :
    EpisodeRecordedAtlas
      (fun ω => if EpisodeReady e f r sfloor N (q ω) then episodeStageNext e f hef r fexp g χ b N (q ω) ω else q ω)
      (fun ω => J ω+if EpisodeReady e f r sfloor N (q ω) then 1 else 0)
      (fun ω => F ω+if EpisodeReady e f r sfloor N (q ω) ∧ episodeStageFails e f r fexp g χ b N (q ω) ω then 1 else 0) := by
  have := A.countable
  refine { Label := A.Label×Option (ℕ×Bool×Bool)
           countable := inferInstance
           chart := fun l => (A.chart l.1).countedBranch hef fexp g χ b sfloor N l.2
           cover := ?_
           correct := ?_
           stages := fun l => A.stages l.1+if l.2.isSome then 1 else 0
           failures := fun l => A.failures l.1+if (l.2.map (fun z => z.2.2)).getD false then 1 else 0
           stages_correct := ?_
           failures_correct := ?_ }
  · intro ω
    obtain ⟨l,hl⟩ := A.cover ω
    obtain ⟨j,hj⟩ := (A.chart l).countedBranch_covers hef fexp g χ b sfloor N ω hl
    exact ⟨(l,j),hj⟩
  · intro l ω hω
    obtain ⟨hl,hnext⟩ := (A.chart l.1).countedBranch_state hef fexp g χ b sfloor N ω l.2 hω
    rw [A.correct l.1 ω hl]
    exact hnext.symm
  · intro l ω hω
    have hl := ((A.chart l.1).countedBranch_state hef fexp g χ b sfloor N ω l.2 hω).1
    rw [A.stages_correct l.1 ω hl,A.correct l.1 ω hl]
    exact congrArg (A.stages l.1+ ·) (((A.chart l.1).countedBranch_record hef fexp g χ b sfloor N ω l.2 hω).1)
  · intro l ω hω
    have hl := ((A.chart l.1).countedBranch_state hef fexp g χ b sfloor N ω l.2 hω).1
    rw [A.failures_correct l.1 ω hl,A.correct l.1 ω hl]
    exact congrArg (A.failures l.1+ ·) (((A.chart l.1).countedBranch_record hef fexp g χ b sfloor N ω l.2 hω).2)

end EpisodeRecordedAtlas
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience
namespace EpisodeRecordedAtlas
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}
  {q : Environment d → EpisodeState (k:=k) e f r} {J F : Environment d → ℕ}

noncomputable def reinject (A : EpisodeRecordedAtlas q J F) (hef : e.1 ≠ f.1)
    (sfloor : ℝ) (hR : 0 ≤ r sfloor) :
    EpisodeRecordedAtlas (fun ω => episodeInitial (k:=k) e f hef r sfloor hR (q ω).height ω) J F where
  Label := A.Label
  countable := A.countable
  chart := fun l => { episodeInitialChart e f hef r sfloor hR (A.chart l).height with
    event := (A.chart l).event
    measurable_event := (rowSigma_mono (by
      intro x hx
      change dot (realPosition x) (realPosition (step e)) < (((A.chart l).height+1:ℕ):ℝ)
      change dot (realPosition x) (realPosition (step e)) < ((A.chart l).height:ℝ) at hx
      exact hx.trans_le (by exact_mod_cast Nat.le_add_right (A.chart l).height 1))) _ (A.chart l).measurable_event }
  cover := A.cover
  correct := by
    intro l ω hω
    change episodeInitial e f hef r sfloor hR (q ω).height ω =
      episodeInitial e f hef r sfloor hR (A.chart l).height ω
    rw [A.correct l ω hω]
    rfl
  stages := A.stages
  failures := A.failures
  stages_correct := A.stages_correct
  failures_correct := A.failures_correct

noncomputable def runFrom (A : EpisodeRecordedAtlas q J F) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N n : ℕ) :
    EpisodeRecordedAtlas
      (fun ω => episodeRun e f hef r fexp g χ b sfloor N (q ω) ω n)
      (fun ω => J ω+episodeSteps e f hef r fexp g χ b sfloor N (q ω) ω n)
      (fun ω => F ω+episodeCount e f hef r fexp g χ b sfloor N (q ω) ω
        (episodeStageFails e f r fexp g χ b N) n) := by
  induction n with
  | zero => exact A
  | succ n ih =>
    let B := ih.advance hef fexp g χ b sfloor N
    refine { toEpisodeAtlas := B.toEpisodeAtlas
             stages := B.stages
             failures := B.failures
             stages_correct := ?_
             failures_correct := ?_ }
    · intro l ω hω
      rw [episodeSteps,←Nat.add_assoc]
      exact B.stages_correct l ω hω
    · intro l ω hω
      rw [episodeCount,←Nat.add_assoc]
      exact B.failures_correct l ω hω

end EpisodeRecordedAtlas
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeCounterChain
attribute [-instance] _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

structure EpisodeCounter {d k : ℕ} (e f : Direction d) (r : ℝ → ℝ) where
  state : EpisodeState (k:=k) e f r
  stages : ℕ
  failures : ℕ

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeNumber
attribute [-instance] _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma episodeBoundary_measurable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N i : ℕ) :
    Measurable (fun ω => episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i) := by
  apply measurable_to_countable'
  intro m
  exact (rowSigma_le _) _ (episodeBoundary_height_event (k:=k) e f hef r fexp g χ b sfloor hR N i m)

namespace EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "T" => episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N

noncomputable def number (ω : Environment d) : ℕ → ℕ
  | 0 => 0
  | i+1 => number ω i+if T ω i<N then 1 else 0

end EpisodeChainLedger
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeDropLedger
attribute [-instance] _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience.EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "T" => episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N

noncomputable def stepMark (ω : Environment d) (i : ℕ) : ℕ :=
  if T ω i<N then episodeSteps e f hef r fexp g χ b sfloor N
    (episodeInitial (k:=k) e f hef r sfloor hR (T ω i) ω) ω N else 0

noncomputable def dropMark (ω : Environment d) (i : ℕ) : ℝ :=
  Real.log (crossingQuenched (realPosition (step e)) 0 (T ω i) ω).toReal-
    Real.log (crossingQuenched (realPosition (step e)) 0 (T ω (i+1)) ω).toReal

end DirectionalTransience.EpisodeChainLedger

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_BadCrossingEpisodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience
namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} {e f : Direction d} {D : ℝ}

lemma radius_nonneg (C : OperationalConstants ν e f D) :
    0 ≤ episodeScaleRadius ν e f C.sfloor :=
  (fluctuationRadius_pos _ _ _).le

noncomputable def activeCount (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (ω : Environment d) : ℕ :=
  EpisodeChainLedger.number (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω N

noncomputable def stagesAt (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (ω : Environment d) (i : ℕ) : ℕ :=
  EpisodeChainLedger.stepMark (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω i

noncomputable def dropAt (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (ω : Environment d) (i : ℕ) : ℝ :=
  EpisodeChainLedger.dropMark (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω i

noncomputable def injectionCost (C : OperationalConstants ν e f D) : ℝ :=
  ((BoundedInjection.injectionMultiplier (episodeScaleRadius ν e f C.sfloor)*C.k+1:ℕ)*(-Real.log C.κ))

end OperationalConstants
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

namespace EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "T" => episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "j" => stepMark (k:=k) e f hef r fexp g χ b sfloor hR N

noncomputable def arrayTime (ω : Environment d) (i : ℤ) := T ω i.toNat
noncomputable def arrayStages (ω : Environment d) (i : ℤ) :=
  if i<0 then 0 else j ω i.toNat
local notation "t" => arrayTime (k:=k) e f hef r fexp g χ b sfloor hR N

lemma arrayTime_measurable (i : ℤ) : Measurable (fun ω => t ω i) :=
  episodeBoundary_measurable (k:=k) e f hef r fexp g χ b sfloor hR N i.toNat

end EpisodeChainLedger
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BadOccupationLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience
namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

noncomputable def paddedTimes (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) : Environment d → ℤ → ℕ :=
  EpisodeChainLedger.arrayTime (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N

noncomputable def paddedStages (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) : Environment d → ℤ → ℕ :=
  EpisodeChainLedger.arrayStages (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N

omit [IsProbabilityMeasure ν] in
lemma paddedTimes_measurable (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (i : ℤ) : Measurable (fun ω => C.paddedTimes hef N ω i) :=
  EpisodeChainLedger.arrayTime_measurable (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N i

noncomputable def occupation (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (Q : Measure (Environment d)) [IsFiniteMeasure Q] : ProbabilityMeasure (ActualEpisodeArray e) :=
  actualOccupation e ν Q (C.paddedTimes hef N) (C.paddedStages hef N)
    (C.paddedTimes_measurable hef N) N (C.activeCount hef N)

end OperationalConstants
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_LocalStoppedSplice
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience

abbrev LocalUpperField {d : ℕ} (e : Direction d) := (ℕ × HorizontalSpace e) → Row d

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal Topology
namespace DirectionalTransience.ReferenceClasses

variable {H : Type*} [AddCommGroup H]

lemma related_symm {O : Data H} {a b : ℕ} (h : related O a b) : related O b a := by
  obtain ⟨z,hz⟩ := h
  exact ⟨-z,O.2.symm a b z hz⟩
lemma related_trans {O : Data H} {a b c : ℕ}
    (hab : related O a b) (hbc : related O b c) : related O a c := by
  obtain ⟨z,hz⟩ := hab
  obtain ⟨w,hw⟩ := hbc
  exact ⟨z+w,O.2.add a b c z w hz hw⟩

lemma representative_related (O : Data H) (a : ℕ) : related O (representative O a) a :=
  by
    classical
    exact Nat.find_spec (p := fun b => related O b a) ⟨a,related_self O a⟩

lemma representative_le {O : Data H} {a b : ℕ} (h : related O b a) :
    representative O a ≤ b := by
  classical
  exact Nat.find_min' (p := fun b => related O b a) ⟨a,related_self O a⟩ h

lemma representative_eq_iff (O : Data H) (a b : ℕ) :
    representative O a = representative O b ↔ related O a b := by
  constructor
  · intro h
    exact related_trans (related_symm (representative_related O a))
      (h ▸ representative_related O b)
  · intro hab
    exact le_antisymm (representative_le (related_trans (representative_related O b)
      (related_symm hab))) (representative_le (related_trans (representative_related O a) hab))

noncomputable def displacement (O : Data H) (a : ℕ) : H :=
  Classical.choose (representative_related O a)

lemma displacement_spec (O : Data H) (a : ℕ) :
    O.1 (representative O a,a) = (↑(displacement O a) : OnePoint H) :=
  Classical.choose_spec (representative_related O a)

lemma offset_eq (O : Data H) {a b : ℕ} {z : H}
    (h : O.1 (a,b) = (z : OnePoint H)) :
    displacement O b = displacement O a + z := by
  have hr := (representative_eq_iff O a b).mpr ⟨z,h⟩
  have hh := O.2.add (representative O a) a b (displacement O a) z (displacement_spec O a) h
  rw [hr, displacement_spec] at hh
  exact OnePoint.coe_injective hh

noncomputable def inputSite (O : Data H) (p : ℕ × ℕ × H) : ℕ × ℕ × H :=
  (representative O p.1,p.2.1,displacement O p.1+p.2.2)

lemma inputSite_eq_iff (O : Data H) (a b l l' : ℕ) (z z' : H) :
    inputSite O (a,l,z) = inputSite O (b,l',z') ↔
      l = l' ∧ O.1 (a,b) = ((z-z' : H) : OnePoint H) := by
  constructor
  · intro h
    have hr : representative O a = representative O b := congrArg Prod.fst h
    have hl : l = l' := congrArg (fun p : ℕ × ℕ × H => p.2.1) h
    have hx : displacement O a+z = displacement O b+z' :=
      congrArg (fun p : ℕ × ℕ × H => p.2.2) h
    obtain ⟨u,hu⟩ := (representative_eq_iff O a b).mp hr
    have hd := offset_eq O hu
    have hu' : u = z-z' := (eq_sub_iff_add_eq).mpr (by
      apply add_left_cancel (a := displacement O a)
      simpa only [hd,add_assoc] using hx.symm)
    exact ⟨hl,by simpa only [hu'] using hu⟩
  · rintro ⟨rfl,h⟩
    have hr := (representative_eq_iff O a b).mpr ⟨z-z',h⟩
    have hd := offset_eq O h
    dsimp only [inputSite]
    apply Prod.ext hr
    change (l,displacement O a+z) = (l,displacement O b+z')
    congr 1
    rw [hd]
    abel

section Measurable
variable [Countable H] [TopologicalSpace H] [DiscreteTopology H]
  [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (OnePoint H)] [BorelSpace (OnePoint H)]

omit [Countable H] [TopologicalSpace H] [DiscreteTopology H] [MeasurableSpace H]
  [BorelSpace H] [BorelSpace (OnePoint H)] in
lemma measurable_offset (a b : ℕ) : Measurable (fun O : Data H => O.1 (a,b)) :=
  (measurable_pi_apply (a,b)).comp measurable_subtype_coe

omit [MeasurableSpace H] [BorelSpace H] in
lemma measurable_related (a b : ℕ) : MeasurableSet {O : Data H | related O a b} := by
  simp only [related,Set.ofPred_exists]
  exact MeasurableSet.iUnion fun z => (measurable_offset a b) (measurableSet_singleton _)

omit [MeasurableSpace H] [BorelSpace H] in
lemma measurable_representative (a : ℕ) : Measurable (fun O : Data H => representative O a) := by
  classical
  exact measurable_find (p := fun O b => related O b a) (fun O => ⟨a,related_self O a⟩) (fun b => measurable_related b a)

omit [BorelSpace H] in
lemma measurable_displacement (a : ℕ) : Measurable (fun O : Data H => displacement O a) := by
  apply measurable_to_countable'
  intro z
  have hm : Measurable (fun O : Data H => O.1 (representative O a,a)) := by
    have h : Measurable (fun p : Data H × ℕ => p.1.1 (p.2,a)) :=
      measurable_from_prod_countable_left fun b => measurable_offset b a
    exact h.comp (measurable_id.prodMk (measurable_representative a))
  have heq : {O : Data H | displacement O a = z} =
      {O | O.1 (representative O a,a) = (z : OnePoint H)} := by
    ext O
    simp only [Set.mem_ofPred_eq,displacement_spec,OnePoint.coe_eq_coe]
  change MeasurableSet {O : Data H | displacement O a = z}
  rw [heq]
  exact hm (measurableSet_singleton _)

lemma measurable_inputSite (p : ℕ × ℕ × H) : Measurable (fun O : Data H => inputSite O p) := by
  exact (measurable_representative p.1).prodMk
    (measurable_const.prodMk ((measurable_displacement p.1).add measurable_const))

variable {R : Type*} [MeasurableSpace R]

noncomputable def fields (O : Data H) (ξ : AllFields H R) : AllFields H R :=
  fun p => ξ (inputSite O p)

lemma measurable_fields : Measurable (fun p : Data H × AllFields H R => fields p.1 p.2) := by
  apply Measurable.of_eval
  intro p
  have hm : Measurable (fun u : AllFields H R × Site H => u.1 u.2) :=
    measurable_from_prod_countable_left fun q => measurable_pi_apply q
  exact hm.comp (measurable_snd.prodMk ((measurable_inputSite p).comp measurable_fst))

noncomputable def reference (ν : Measure R) [IsProbabilityMeasure ν] :
    Kernel (Data H) (AllFields H R) :=
  ((Kernel.id : Kernel (Data H) (Data H)).prod
    (Kernel.const (Data H) (Measure.infinitePi (fun _ : Site H => ν)))).map
    (fun p => fields p.1 p.2)

instance reference_markov (ν : Measure R) [IsProbabilityMeasure ν] : IsMarkovKernel (reference (H := H) ν) := by
  unfold reference
  exact Kernel.IsMarkovKernel.map _ measurable_fields

lemma reference_apply (ν : Measure R) [IsProbabilityMeasure ν] (O : Data H) :
    reference ν O = (Measure.infinitePi (fun _ : Site H => ν)).map (fields O) := by
  rw [reference,Kernel.map_apply _ measurable_fields,Kernel.prod_apply,Kernel.id_apply,
    Kernel.const_apply,Measure.dirac_prod,Measure.map_map measurable_fields measurable_prodMk_left]
  rfl

omit [Countable H] [TopologicalSpace H] [DiscreteTopology H] [MeasurableSpace H]
  [BorelSpace H] [MeasurableSpace (OnePoint H)] [BorelSpace (OnePoint H)] in
lemma inputSite_injective_at_label (O : Data H) (a : ℕ) :
    Function.Injective (fun p : ℕ × H => inputSite O (a,p)) := by
  rintro ⟨l,z⟩ ⟨l',z'⟩ h
  have hh := (inputSite_eq_iff O a a l l' z z').mp h
  rw [O.2.self,OnePoint.coe_eq_coe] at hh
  exact Prod.ext hh.1 (sub_eq_zero.mp hh.2.symm)

lemma reference_single_field (ν : Measure R) [IsProbabilityMeasure ν] (O : Data H) (a : ℕ) :
    (reference ν O).map (fun φ => fun p : ℕ × H => φ (a,p)) =
      Measure.infinitePi (fun _ : ℕ × H => ν) := by
  have hm : Measurable (fields O : AllFields H R → _) :=
    Measurable.of_eval fun _ => measurable_pi_apply _
  rw [reference_apply,Measure.map_map (by fun_prop) hm]
  exact Measure.map_infinitePi_infinitePi_of_inj (inputSite_injective_at_label O a)

omit [Countable H] [TopologicalSpace H] [DiscreteTopology H] [MeasurableSpace H]
  [BorelSpace H] [MeasurableSpace (OnePoint H)] [BorelSpace (OnePoint H)] in
lemma inputSite_injective_distinct_classes {I : Type*} (O : Data H) (a : I → ℕ)
    (ha : ∀ i j, i ≠ j → ¬ related O (a i) (a j)) :
    Function.Injective (fun p : I × (ℕ × H) => inputSite O (a p.1,p.2)) := by
  rintro ⟨i,l,z⟩ ⟨j,l',z'⟩ h
  have hh := (inputSite_eq_iff O (a i) (a j) l l' z z').mp h
  have hij : i = j := by
    by_contra he
    exact ha i j he ⟨z-z',hh.2⟩
  subst j
  exact Prod.ext rfl (inputSite_injective_at_label O (a i) h)

lemma reference_distinct_classes {I : Type*} (ν : Measure R) [IsProbabilityMeasure ν]
    (O : Data H) (a : I → ℕ) (ha : ∀ i j, i ≠ j → ¬ related O (a i) (a j)) :
    (reference ν O).map (fun φ => fun p : I × (ℕ × H) => φ (a p.1,p.2)) =
      Measure.infinitePi (fun _ : I × (ℕ × H) => ν) := by
  have hm : Measurable (fields O : AllFields H R → _) :=
    Measurable.of_eval fun _ => measurable_pi_apply _
  rw [reference_apply,Measure.map_map (by fun_prop) hm]
  exact Measure.map_infinitePi_infinitePi_of_inj (inputSite_injective_distinct_classes O a ha)

end Measurable
end DirectionalTransience.ReferenceClasses

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ReferenceContinuity
attribute [-instance] _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace DirectionalTransience.ReferenceClasses

section Closed
variable {H : Type*} [AddCommGroup H] [TopologicalSpace H] [DiscreteTopology H]

omit [AddCommGroup H] in
lemma offset_clopen (a b : ℕ) (z : H) :
    IsClopen {O : Offsets H | O (a,b) = (z : OnePoint H)} :=
  (finite_value_clopen z).preimage (continuous_apply (a,b))

lemma consistent_closed : IsClosed {O : Offsets H | Consistent O} := by
  have hself : IsClosed {O : Offsets H | ∀ a, O (a,a) = ((0 : H) : OnePoint H)} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun a => (offset_clopen a a 0).1
  have hsymm : IsClosed {O : Offsets H | ∀ (a b : ℕ) (z : H),
      O (a,b) = (z : OnePoint H) → O (b,a) = ((-z : H) : OnePoint H)} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun z => ?_
    have heq : {O : Offsets H | O (a,b) = (z : OnePoint H) → O (b,a) = ((-z : H) : OnePoint H)} =
        {O | O (a,b) = (z : OnePoint H)}ᶜ ∪ {O | O (b,a) = ((-z : H) : OnePoint H)} := by
      ext; simp [imp_iff_not_or]
    rw [heq]
    exact (offset_clopen a b z).2.isClosed_compl.union (offset_clopen b a (-z)).1
  have hadd : IsClosed {O : Offsets H | ∀ (a b c : ℕ) (z w : H),
      O (a,b) = (z : OnePoint H) → O (b,c) = (w : OnePoint H) →
      O (a,c) = ((z+w : H) : OnePoint H)} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun c =>
      isClosed_iInter fun z => isClosed_iInter fun w => ?_
    have heq : {O : Offsets H | O (a,b) = (z : OnePoint H) → O (b,c) = (w : OnePoint H) →
        O (a,c) = ((z+w : H) : OnePoint H)} =
      {O | O (a,b) = (z : OnePoint H)}ᶜ ∪
      ({O | O (b,c) = (w : OnePoint H)}ᶜ ∪ {O | O (a,c) = ((z+w : H) : OnePoint H)}) := by
      ext; simp [imp_iff_not_or]
    rw [heq]
    exact (offset_clopen a b z).2.isClosed_compl.union
      ((offset_clopen b c w).2.isClosed_compl.union (offset_clopen a c (z+w)).1)
  have heq : {O : Offsets H | Consistent O} =
      {O : Offsets H | ∀ a, O (a,a) = ((0 : H) : OnePoint H)} ∩
      {O : Offsets H | ∀ (a b : ℕ) (z : H),
        O (a,b) = (z : OnePoint H) → O (b,a) = ((-z : H) : OnePoint H)} ∩
      {O : Offsets H | ∀ (a b c : ℕ) (z w : H),
        O (a,b) = (z : OnePoint H) → O (b,c) = (w : OnePoint H) →
        O (a,c) = ((z+w : H) : OnePoint H)} := by
    ext O
    exact ⟨fun h => ⟨⟨h.self,h.symm⟩,h.add⟩,fun h => ⟨h.1.1,h.1.2,h.2⟩⟩
  rw [heq]
  exact (hself.inter hsymm).inter hadd

instance data_compact : CompactSpace (Data H) :=
  isCompact_iff_compactSpace.mp consistent_closed.isCompact

end Closed

end DirectionalTransience.ReferenceClasses

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_AnchorFrameReference
attribute [-instance] _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience.ReferenceClasses
variable {H : Type*} [AddCommGroup H]

noncomputable def anchorOffsets (U : ℕ → H) : Data H :=
  ⟨fun p => ((U p.2-U p.1 : H) : OnePoint H), by
    constructor
    · intro a; simp
    · intro a b z h
      simp only [OnePoint.coe_eq_coe] at h ⊢
      rw [← h]; abel
    · intro a b c z w h h'
      simp only [OnePoint.coe_eq_coe] at h h' ⊢
      rw [← h,← h']; abel⟩

noncomputable def anchorFields {R : Type*} (U : ℕ → H) (ξ : UpperField H R) : AllFields H R :=
  fun p => ξ (p.2.1,U p.1+p.2.2)

end DirectionalTransience.ReferenceClasses

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_RawWindow
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience

abbrev RawCurrentData {d : ℕ} (e : Direction d) :=
  ℕ × (Environment d × (ℕ → HorizontalSpace e))

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ReferenceFeller
attribute [-instance] _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace Filter
open scoped ENNReal Topology BoundedContinuousFunction
namespace DirectionalTransience.ReferenceClasses

variable {H R : Type*} [AddCommGroup H] [Countable H]
  [TopologicalSpace H] [DiscreteTopology H] [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (OnePoint H)] [BorelSpace (OnePoint H)]
  [UniformSpace R] [CompactSpace R] [SecondCountableTopology R]
  [MeasurableSpace R] [BorelSpace R]

noncomputable def referenceProb (ν : Measure R) [IsProbabilityMeasure ν]
    (O : Data H) : ProbabilityMeasure (AllFields H R) := ⟨reference ν O,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

end DirectionalTransience.ReferenceClasses

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_BadWindowEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience
namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)}
  {e f : Direction d} {D : ℝ}

noncomputable def windowEntropyConstant (C : OperationalConstants ν e f D) : ℝ :=
  (8/3:ℝ)*D*C.injectionCost

end OperationalConstants
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_GridTrials
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def GridPrefix {d : ℕ} (e : Direction d) (B : ℕ) : ℕ → ℕ → Set (Path d)
  | 0,n => {X | X 0=0} ∩ FirstLayerHit (signedHeight e) B n
  | k+1,m => ({X | X 0=0} ∩ FirstLayerHit (signedHeight e) (((k+2)*B:ℕ):ℤ) m) ∩
      ⋃ n < m, GridPrefix e B k n ∩ DropBetween (realPosition (step e)) n m

def GridReached {d : ℕ} (e : Direction d) (B k : ℕ) : Set (Path d) :=
  ⋃ n, GridPrefix e B k n

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_IndependentDyadic
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience.ReferenceClasses
variable {H R : Type*} [AddCommGroup H]

lemma representative_singleton (O : Data H) (a : ℕ)
    (ha : ∀ b, related O a b → a=b) : representative O a=a :=
  (ha _ (related_symm (representative_related O a))).symm

lemma displacement_singleton (O : Data H) (a : ℕ)
    (ha : ∀ b, related O a b → a=b) : displacement O a=0 := by
  have h := displacement_spec O a
  rw [representative_singleton O a ha,O.2.self] at h
  exact (OnePoint.coe_injective h).symm

noncomputable def dustWeight (dust : ℕ → Prop) (q : UpperField H R → ℝ)
    (n : ℕ) (φ : AllFields H R) : ℝ :=
  sampleAverage (fun a φ => if dust a then q (fun p => φ (a,p)) else 0) n φ

variable [MeasurableSpace R]

omit [AddCommGroup H] in
lemma dustWeight_measurable (dust : ℕ → Prop) (q : UpperField H R → ℝ)
    (hq : Measurable q) (n : ℕ) : Measurable (dustWeight dust q n) := by
  unfold dustWeight sampleAverage
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro a _
  split_ifs
  · exact hq.comp (Measurable.of_eval fun p => measurable_pi_apply (a,p))
  · exact measurable_const

end DirectionalTransience.ReferenceClasses

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_OperationalLengthMarks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)}
  {e f : Direction d} {D : ℝ}

noncomputable def lengthCost (C : OperationalConstants ν e f D) : ℝ :=
  Real.log 2+Real.log (1+C.sfloor*Real.exp (C.χ*C.b))+1+C.g*C.b

end OperationalConstants
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_StationaryMarking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

abbrev MarkedArray {d : ℕ} (e : Direction d) := ActualEpisodeArray e × ℕ
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

abbrev MarkedCurrentData {d : ℕ} (e : Direction d) := CurrentData e × ℕ
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_ProfileGrowth2
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

def HorizontalLayer {d : ℕ} (e : Direction d) := {x : Lattice d // x e.1 = 0}

end DirectionalTransience

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

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def IsProperProfile {d : ℕ} (e : Direction d) (w : HorizontalSpace e → ℝ≥0∞) : Prop :=
  (∀ z, 0<w z) ∧ (∑' z, w z)≤1

abbrev ProperProfile {d : ℕ} (e : Direction d) := {w : HorizontalSpace e → ℝ≥0∞ // IsProperProfile e w}

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_VisitTrials
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def ReturnIn {d : ℕ} (S : Set (Lattice d)) (y : Lattice d) : Set (Path d) :=
  {X | ∃ n, 0 < n ∧ X n=y ∧ ∀ j ≤ n, X j∈S}

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_StationaryProfile2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

abbrev FullMarkedArray {d : ℕ} (e : Direction d) := MarkedArray e × Environment d
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_WidthGridTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def LateGridFailure {d : ℕ} (e : Direction d) (B j : ℕ) : Set (Path d) :=
  ⋃ n, (({X : Path d | X 0=0} ∩ FirstLayerHit (signedHeight e) (j*B:ℕ) n) ∩
    FutureEvent (fun x => Cross (realPosition (step e)) x B) n) \ FutureNoDrop (realPosition (step e)) n

def NoTruePastHeight {d : ℕ} (e : Direction d) (H : ℕ) : Set (Path d) :=
  {X | X 0=0 ∧ ∃ n, X ∈ FirstLayerHit (signedHeight e) H n ∧
    ∀ t, 0 < t → t ≤ n → ¬TrueRecord (realPosition (step e)) X t}

end DirectionalTransience

end

end OAI
end


