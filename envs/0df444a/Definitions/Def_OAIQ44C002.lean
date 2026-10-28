-- Prove2me | Definitions.Def_OAIQ44C002
-- name    : OAIQ44C002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T12:04:27.41664+00:00
-- url     : https://prove2.me/theorems/b27bd9dd-722f-4213-b906-2f995dd9b676
-- title:
--   Definitions bundle OAIQ44C002 of the split of OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.StandardMapEntropy.main_components`, carved from OpenAI's openai/math development (OpenAI, *Positive Metric Entropy for the Standard Map at Large Parameters*, OpenAI Math Release, September 23, 2026, result family 146, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 265 declarations of OpenAI's Lean: 163 definitions, 3 inductive types or structures, 9 instances and 90 theorems. The definitions and types are `OAI.StandardMapEntropy.NonlinearStable.LocalRecurrence.trueOrbit`, `OAI.StandardMapEntropy.NonlinearStable.Recurrence.graph`, `OAI.StandardMapEntropy.NonlinearStable.Recurrence.orbit`, `OAI.StandardMapEntropy.NonlinearStable.Recurrence.perronApprox`, `OAI.StandardMapEntropy.NonlinearStable.Recurrence.solution`, `OAI.StandardMapEntropy.NonlinearStable.Recurrence.tail`, `OAI.StandardMapEntropy.NonlinearStable.Recurrence.trappedBox`, `OAI.StandardMapEntropy.NonlinearStable.graphLinearization`, `OAI.StandardMapEntropy.RescaledPath.denominator`, `OAI.StandardMapEntropy.RescaledPath.phase`, `OAI.StandardMapEntropy.RescaledPath.quotient`, `OAI.StandardMapEntropy.RescaledPath.ratio`, `OAI.StandardMapEntropy.ReversibleGraphFamilies`, `OAI.StandardMapEntropy.ReversibleGraphRectangle`, `OAI.StandardMapEntropy.ReversibleGraphRectangle.torusPoint`, `OAI.StandardMapEntropy.ReversibleRectangleBlock`, `OAI.StandardMapEntropy.ReversibleRectangleBlock.carrierProbability`, `OAI.StandardMapEntropy.ReversibleRectangleBlock.chart`, `OAI.StandardMapEntropy.ReversibleRectangleBlock.coordinateCarrier`, `OAI.StandardMapEntropy.ReversibleRectangleBlock.coordinates`, `OAI.StandardMapEntropy.ReversibleRectangleBlock.holonomyConstant`, `OAI.StandardMapEntropy.ReversibleRectangleBlock.label`, `OAI.StandardMapEntropy.ReversibleRectangleBlock.reverseCoordinates`, `OAI.StandardMapEntropy.ReversibleRectangleBlock.stableInterval`, `OAI.StandardMapEntropy.ReversibleRectangleBlock.unstableInterval`, `OAI.StandardMapEntropy.SlowPair`, `OAI.StandardMapEntropy.SlowShape`, `OAI.StandardMapEntropy.TransferLimit`, `OAI.StandardMapEntropy.TreeArray`, `OAI.StandardMapEntropy.arrayBridgeEvent`, `OAI.StandardMapEntropy.arrayCancellation`, `OAI.StandardMapEntropy.arrayTest`, `OAI.StandardMapEntropy.arrayTranslation`, `OAI.StandardMapEntropy.arrayV`, `OAI.StandardMapEntropy.badIndices`, `OAI.StandardMapEntropy.bandCap`, `OAI.StandardMapEntropy.bandIntensity`, `OAI.StandardMapEntropy.bandLaw`, `OAI.StandardMapEntropy.bandMoment`, `OAI.StandardMapEntropy.blockAtom` and 126 more.
--
--   **Sources.** They come from these modules of lean/OAI/Dynamics/StandardMap, in whole or in part: `StandardMap_ArrayActions`, `StandardMap_ArrayAffinity`, `StandardMap_ArrayHalf`, `StandardMap_ArrayMoments`, `StandardMap_ArrayTests`, `StandardMap_ArrayTopology`, `StandardMap_BandCap`, `StandardMap_BandCoboundary`, `StandardMap_BandIntensity`, `StandardMap_Bernoulli_ErgodicAverages`, `StandardMap_BridgeAveraging`, `StandardMap_BridgeVague`, `StandardMap_CancellationTheorem`, `StandardMap_CancellationVector`, `StandardMap_CappedTests`, `StandardMap_ClosedEligibility`, `StandardMap_CocycleAlgebra`, `StandardMap_Components_BirkhoffAtoms`, `StandardMap_Components_BoundedBirkhoff`, `StandardMap_Components_CurvedHolonomy`, `StandardMap_Components_FineChartGraph`, `StandardMap_Components_SliceRectangleNonsingular`, `StandardMap_CosineNull`, `StandardMap_DoublingPointwise`, `StandardMap_DyadicArrays`, `StandardMap_EndpointClasses`, `StandardMap_EndpointCovariance`, `StandardMap_EndpointDefinition`, `StandardMap_EndpointObservations`, `StandardMap_Entropy_FineCharts`, `StandardMap_Entropy_PhysicalVolume`, `StandardMap_FineArrays`, `StandardMap_FixedDeficit`, `StandardMap_GridPartition`, `StandardMap_Holonomy_DerivativeQuantitative`, `StandardMap_Holonomy_FinePlaqueParameters`, `StandardMap_Holonomy_FineStableGeometry`, `StandardMap_Holonomy_FiniteOrbitDecay`, `StandardMap_LocalScarcity`, `StandardMap_LogDerivativeCore`, `StandardMap_Lyapunov_BoundedTempering`, `StandardMap_Lyapunov_DerivativeGrowth`, `StandardMap_Lyapunov_InverseLyapunov`, `StandardMap_Lyapunov_MeasurableFrame`, `StandardMap_Lyapunov_Subadditive`, `StandardMap_Lyapunov_TransverseLines`, `StandardMap_ManyGood`, `StandardMap_MeanCancellation`, `StandardMap_MeanDeficit`, `StandardMap_MeanGrowth`, `StandardMap_MiddleCount`, `StandardMap_MiddleObservationBridge`, `StandardMap_MiddlePrefixBridge`, `StandardMap_NonaffineLimits`, `StandardMap_ObservationTransport`, `StandardMap_ProductDistances`, `StandardMap_RealArrays`, `StandardMap_RealBridge`, `StandardMap_ScaleAction`, `StandardMap_ScaleCancellation`, `StandardMap_ScaleEndpoints`, `StandardMap_ScaleEvaluation`, `StandardMap_ShapeClassification`, `StandardMap_ShapeCore`, `StandardMap_ShapeTopology`, `StandardMap_Stable_LocalStable`, `StandardMap_Stable_PerronStability`, `StandardMap_Stable_SmoothRemainder`, `StandardMap_TerminalCap`, `StandardMap_TerminalStrict`, `StandardMap_TorusDynamics`, `StandardMap_TorusObservations`, `StandardMap_TransferCore`, `StandardMap_TruncationArrays`, `StandardMap_VectorGrowth`, `StandardMap_WeightBridge`, `StandardMap_WeightSlow`, `StandardMap_WeightUnit`.
--
--   **Imports.** It imports the published bundle `Def_StandardMapComponents`; the bundles `OAIQ44C000` and `OAIQ44C001` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.StandardMapEntropy.BridgeScalarControl.prefix_dirichlet_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.bridge_null_terminal_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.capG_integrable_remainder_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.capG_integrable_sum_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.capG_integral_decomposition_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.capG_limit_balance_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.endpoint_bridge_null_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.middle_weight_tendsto_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.noCancellation_aemulti_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.noCancellation_aeterminal_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_cap_nonpos_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_left_ray_zero_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_right_ray_zero_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_shape_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_translate_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.shape_aeterminal_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.slowPair_aemulti_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.slowPair_aeterminal_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.terminal_cap_strict_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.terminal_event_lower_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.weight_affine_null_q44`, `OAI.StandardMapEntropy.ReversibleGraphRectangle.exists_weakBernoulli_partitions_q44`, `OAI.StandardMapEntropy.actual_backward_carry_full_q44`, `OAI.StandardMapEntropy.actual_compact_graph_labels_full_q44`, `OAI.StandardMapEntropy.actual_cyclic_weakBernoulli_component_q44`, `OAI.StandardMapEntropy.actual_grid_square_product_q44`, `OAI.StandardMapEntropy.bandMoment_order_q44`, `OAI.StandardMapEntropy.band_coboundary_q44`, `OAI.StandardMapEntropy.exists_reversibleRectangleBlock_q44`, `OAI.StandardMapEntropy.jointly_continuous_dirichlet_family_q44` and `OAI.StandardMapEntropy.middle_observation_product_q44`; the proofs of `OAI.StandardMapEntropy.BridgeGrid.scale_bound_q44`, `OAI.StandardMapEntropy.BridgeScalarControl.prefix_dirichlet_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.bridge_null_terminal_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.capG_integrable_remainder_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.capG_integrable_sum_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.capG_integral_decomposition_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.capG_limit_balance_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.dilation_balance_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.endpoint_bridge_null_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.exists_limitLaws_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.middle_weight_tendsto_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.noCancellation_aemulti_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.noCancellation_aeterminal_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_cap_nonpos_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_left_ray_zero_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_right_ray_zero_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_shape_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_translate_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.shape_aeterminal_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.slowPair_aemulti_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.slowPair_aeterminal_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.terminal_cap_strict_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.terminal_event_lower_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.weight_affine_null_q44`, `OAI.StandardMapEntropy.ReversibleGraphRectangle.exists_weakBernoulli_partitions_q44`, `OAI.StandardMapEntropy.actual_backward_carry_full_q44`, `OAI.StandardMapEntropy.actual_compact_graph_labels_full_q44`, `OAI.StandardMapEntropy.actual_cyclic_weakBernoulli_component_q44`, `OAI.StandardMapEntropy.actual_grid_square_product_q44`, `OAI.StandardMapEntropy.actual_return_bernoulli_q44`, `OAI.StandardMapEntropy.actual_return_full_entropy_iid_factor_q44`, `OAI.StandardMapEntropy.bandMoment_order_q44`, `OAI.StandardMapEntropy.band_coboundary_q44`, `OAI.StandardMapEntropy.eventually_meanDeficit_doubling_q44`, `OAI.StandardMapEntropy.eventually_small_endpoints_slice_q44`, `OAI.StandardMapEntropy.exists_reversibleRectangleBlock_q44`, `OAI.StandardMapEntropy.jointly_continuous_dirichlet_family_q44`, `OAI.StandardMapEntropy.main_components`, `OAI.StandardMapEntropy.middle_observation_product_q44` and `OAI.StandardMapEntropy.no_critical_scale_sequence_q44`.
-- source:
--   OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 146; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Dynamics/StandardMap at commit adc7f12

import Mathlib
import Definitions.Def_StandardMapComponents
import Definitions.Def_OAIQ44C000
import Definitions.Def_OAIQ44C001

section
-- module Solutions.OAIQ44_CM.StandardMap_LocalScarcity
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StandardMapEntropy

def blockAtom {r : ℕ} (f : Torus → Torus) (p : FinitePartition r)
    (n : ℕ) (w : Fin n → Fin (r + 1)) : Set Torus :=
  { z | ∀ i : Fin n, p.val (f^[i.val] z) = w i }

noncomputable def blockEntropy {r : ℕ} (μ : Measure Torus) (f : Torus → Torus)
    (p : FinitePartition r) (n : ℕ) : ℝ :=
  - ∑ w : Fin n → Fin (r + 1),
    (μ (blockAtom f p n w)).toReal * Real.log (μ (blockAtom f p n w)).toReal

noncomputable def partitionEntropy {r : ℕ} (μ : Measure Torus) (f : Torus → Torus)
    (p : FinitePartition r) : ℝ≥0∞ :=
  ⨅ n : ℕ, ENNReal.ofReal (blockEntropy μ f p (n + 1) / (n + 1 : ℝ))

noncomputable def metricEntropy (μ : Measure Torus) (f : Torus → Torus) : ℝ≥0∞ :=
  ⨆ r : ℕ, ⨆ p : FinitePartition r, partitionEntropy μ f p

instance circleVolumeProbability : IsProbabilityMeasure (volume : Measure Circle) := by
  constructor
  rw [AddCircle.measure_univ]
  norm_num

instance areaProbability : IsProbabilityMeasure area := by
  unfold area
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def sSolution (v : ℕ → ℝ) : ℕ → ℝ := linearSolution v 1 0

noncomputable def boundaryValue (v : ℕ → ℝ) (j : ℕ) : ℝ :=
  -sSolution v j / tSolution v j

noncomputable def dirichletSolution (v : ℕ → ℝ) (j : ℕ) : ℕ → ℝ :=
  linearSolution v 1 (boundaryValue v j)

noncomputable def greenKernel (v : ℕ → ℝ) (j a b : ℕ) : ℝ :=
  tSolution v (min a b) * dirichletSolution v j (max a b)

noncomputable def forcingResponse (v F : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | n + 2 => v (n + 1) * forcingResponse v F (n + 1) - forcingResponse v F n + F (n + 1)

noncomputable def orbitDisplacement (k q₀ θ δ : ℝ) (n : ℕ) : ℝ :=
  liftedOrbit k q₀ (θ + δ) n - liftedOrbit k q₀ θ n

noncomputable def orbitForcing (k q₀ θ δ : ℝ) (n : ℕ) : ℝ :=
  phi k (liftedOrbit k q₀ (θ + δ) n) - phi k (liftedOrbit k q₀ θ n) -
    orbitCoefficient k q₀ θ n * orbitDisplacement k q₀ θ δ n

noncomputable def rescaledD₂ (k q₀ θ L ξ : ℝ) : ℕ → ℝ :=
  forcingResponse (orbitCoefficient k q₀ (θ + ξ / L))
    (fun i => phiSecond k (rescaledOrbit k q₀ θ L ξ i) * (rescaledD₁ k q₀ θ L ξ i) ^ 2)

noncomputable def rescaledF₃ (k q₀ θ L ξ : ℝ) (i : ℕ) : ℝ :=
  phiThird k (rescaledOrbit k q₀ θ L ξ i) * (rescaledD₁ k q₀ θ L ξ i) ^ 3 +
    3 * phiSecond k (rescaledOrbit k q₀ θ L ξ i) * rescaledD₁ k q₀ θ L ξ i * rescaledD₂ k q₀ θ L ξ i
noncomputable def rescaledD₃ (k q₀ θ L ξ : ℝ) : ℕ → ℝ :=
  forcingResponse (orbitCoefficient k q₀ (θ + ξ / L)) (rescaledF₃ k q₀ θ L ξ)

noncomputable def rescaledF₄ (k q₀ θ L ξ : ℝ) (i : ℕ) : ℝ :=
  phiFourth k (rescaledOrbit k q₀ θ L ξ i) * (rescaledD₁ k q₀ θ L ξ i) ^ 4 +
    6 * phiThird k (rescaledOrbit k q₀ θ L ξ i) * (rescaledD₁ k q₀ θ L ξ i) ^ 2 * rescaledD₂ k q₀ θ L ξ i +
    3 * phiSecond k (rescaledOrbit k q₀ θ L ξ i) * (rescaledD₂ k q₀ θ L ξ i) ^ 2 +
    4 * phiSecond k (rescaledOrbit k q₀ θ L ξ i) * rescaledD₁ k q₀ θ L ξ i * rescaledD₃ k q₀ θ L ξ i
noncomputable def rescaledD₄ (k q₀ θ L ξ : ℝ) : ℕ → ℝ :=
  forcingResponse (orbitCoefficient k q₀ (θ + ξ / L)) (rescaledF₄ k q₀ θ L ξ)

noncomputable def rescaledF₅ (k q₀ θ L ξ : ℝ) (i : ℕ) : ℝ :=
  phiFifth k (rescaledOrbit k q₀ θ L ξ i) * (rescaledD₁ k q₀ θ L ξ i) ^ 5 +
    10 * phiFourth k (rescaledOrbit k q₀ θ L ξ i) * (rescaledD₁ k q₀ θ L ξ i) ^ 3 * rescaledD₂ k q₀ θ L ξ i +
    15 * phiThird k (rescaledOrbit k q₀ θ L ξ i) * rescaledD₁ k q₀ θ L ξ i * (rescaledD₂ k q₀ θ L ξ i) ^ 2 +
    10 * phiThird k (rescaledOrbit k q₀ θ L ξ i) * (rescaledD₁ k q₀ θ L ξ i) ^ 2 * rescaledD₃ k q₀ θ L ξ i +
    10 * phiSecond k (rescaledOrbit k q₀ θ L ξ i) * rescaledD₂ k q₀ θ L ξ i * rescaledD₃ k q₀ θ L ξ i +
    5 * phiSecond k (rescaledOrbit k q₀ θ L ξ i) * rescaledD₁ k q₀ θ L ξ i * rescaledD₄ k q₀ θ L ξ i
noncomputable def rescaledD₅ (k q₀ θ L ξ : ℝ) : ℕ → ℝ :=
  forcingResponse (orbitCoefficient k q₀ (θ + ξ / L)) (rescaledF₅ k q₀ θ L ξ)

noncomputable def greenMatrix (v : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun a b => greenKernel v (n + 1) (a.val + 1) (b.val + 1)

noncomputable def rescaledV₁ (k q₀ θ L ξ : ℝ) (a : ℕ) : ℝ :=
  phiSecond k (rescaledOrbit k q₀ θ L ξ a) * rescaledD₁ k q₀ θ L ξ a
noncomputable def rescaledV₂ (k q₀ θ L ξ : ℝ) (a : ℕ) : ℝ :=
  phiThird k (rescaledOrbit k q₀ θ L ξ a) * (rescaledD₁ k q₀ θ L ξ a) ^ 2 +
    phiSecond k (rescaledOrbit k q₀ θ L ξ a) * rescaledD₂ k q₀ θ L ξ a
noncomputable def rescaledV₃ (k q₀ θ L ξ : ℝ) (a : ℕ) : ℝ :=
  phiFourth k (rescaledOrbit k q₀ θ L ξ a) * (rescaledD₁ k q₀ θ L ξ a) ^ 3 +
    3 * phiThird k (rescaledOrbit k q₀ θ L ξ a) * rescaledD₁ k q₀ θ L ξ a * rescaledD₂ k q₀ θ L ξ a +
    phiSecond k (rescaledOrbit k q₀ θ L ξ a) * rescaledD₃ k q₀ θ L ξ a
noncomputable def rescaledV₄ (k q₀ θ L ξ : ℝ) (a : ℕ) : ℝ :=
  phiFifth k (rescaledOrbit k q₀ θ L ξ a) * (rescaledD₁ k q₀ θ L ξ a) ^ 4 +
    6 * phiFourth k (rescaledOrbit k q₀ θ L ξ a) * (rescaledD₁ k q₀ θ L ξ a) ^ 2 * rescaledD₂ k q₀ θ L ξ a +
    3 * phiThird k (rescaledOrbit k q₀ θ L ξ a) * (rescaledD₂ k q₀ θ L ξ a) ^ 2 +
    4 * phiThird k (rescaledOrbit k q₀ θ L ξ a) * rescaledD₁ k q₀ θ L ξ a * rescaledD₃ k q₀ θ L ξ a +
    phiSecond k (rescaledOrbit k q₀ θ L ξ a) * rescaledD₄ k q₀ θ L ξ a

open scoped Matrix.Norms.Operator

noncomputable def rescaledMatrix (k q₀ θ L ξ : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  dirichletMatrix (fun a => potential k (rescaledOrbit k q₀ θ L ξ a)) n

noncomputable def rescaledInverse (k q₀ θ L ξ : ℝ) (n : ℕ) :=
  Ring.inverse (rescaledMatrix k q₀ θ L ξ n)
noncomputable def rescaledInverse₁ (k q₀ θ L ξ : ℝ) (n : ℕ) :=
  inverseJet₁ (rescaledInverse k q₀ θ L ξ n) (rescaledDiagonal rescaledV₁ k q₀ θ L ξ n)
noncomputable def rescaledInverse₂ (k q₀ θ L ξ : ℝ) (n : ℕ) :=
  inverseJet₂ (rescaledInverse k q₀ θ L ξ n) (rescaledDiagonal rescaledV₁ k q₀ θ L ξ n)
    (rescaledDiagonal rescaledV₂ k q₀ θ L ξ n)
noncomputable def rescaledInverse₃ (k q₀ θ L ξ : ℝ) (n : ℕ) :=
  inverseJet₃ (rescaledInverse k q₀ θ L ξ n) (rescaledDiagonal rescaledV₁ k q₀ θ L ξ n)
    (rescaledDiagonal rescaledV₂ k q₀ θ L ξ n) (rescaledDiagonal rescaledV₃ k q₀ θ L ξ n)
noncomputable def rescaledInverse₄ (k q₀ θ L ξ : ℝ) (n : ℕ) :=
  inverseJet₄ (rescaledInverse k q₀ θ L ξ n) (rescaledDiagonal rescaledV₁ k q₀ θ L ξ n)
    (rescaledDiagonal rescaledV₂ k q₀ θ L ξ n) (rescaledDiagonal rescaledV₃ k q₀ θ L ξ n)
    (rescaledDiagonal rescaledV₄ k q₀ θ L ξ n)

noncomputable def rescaledPotentialJets (k q₀ θ L ξ : ℝ) (n : ℕ) : Fin 4 → Fin n → ℝ :=
  ![fun a => rescaledV₁ k q₀ θ L ξ (a.val + 1),
    fun a => rescaledV₂ k q₀ θ L ξ (a.val + 1),
    fun a => rescaledV₃ k q₀ θ L ξ (a.val + 1),
    fun a => rescaledV₄ k q₀ θ L ξ (a.val + 1)]

noncomputable def rescaledTJet (p : ℕ) (k q₀ θ L ξ : ℝ) (l : ℕ) : ℝ := match p with
  | 0 => rescaledD₁ k q₀ θ L ξ l
  | 1 => rescaledD₂ k q₀ θ L ξ l
  | 2 => rescaledD₃ k q₀ θ L ξ l
  | 3 => rescaledD₄ k q₀ θ L ξ l
  | _ => rescaledD₅ k q₀ θ L ξ l

open Filter
open scoped Topology

open Metric

section

noncomputable def rescaledPotentialJet (p : ℕ) (k q₀ θ L h : ℝ) (j : ℕ) : ℝ := match p with
  | 0 => potential k (rescaledOrbit k q₀ θ L h j)
  | 1 => rescaledV₁ k q₀ θ L h j
  | 2 => rescaledV₂ k q₀ θ L h j
  | 3 => rescaledV₃ k q₀ θ L h j
  | _ => rescaledV₄ k q₀ θ L h j

noncomputable def slowDenominator (k q₀ θ L : ℝ) (j : ℕ) (h : ℝ) : ℝ :=
  (normalizedSlope k q₀ θ L j h) ^ 2 * shiftedCosine k q₀ θ L j h

end

end StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace StandardMapEntropy

namespace RescaledPath
noncomputable def ratio (P : RescaledPath) : ℝ := P.size / P.L
noncomputable def phase (P : RescaledPath) : ℝ → ℝ :=
  centerPhase (fun x => rescaledOrbit P.k P.q₀ P.θ P.L (P.sign * x) P.j)
noncomputable def quotient (P : RescaledPath) (x : ℝ) : ℝ :=
  terminalQuotient P.k P.q₀ P.θ P.L (P.sign * x) P.j
noncomputable def denominator (P : RescaledPath) (x : ℝ) : ℝ :=
  slowDenominator P.k P.q₀ P.θ P.L P.j (P.sign * x)

end RescaledPath
noncomputable def cubicError (k : ℝ) : ℝ :=
  inverseFourthMajorant (52 * derivativeMajorant) / 12 * growthBase k ^ (-(9 / 5 : ℝ)) +
    16 * growthBase k ^ (-(77 / 100 : ℝ))
noncomputable def cubicFineError (k r : ℝ) : ℝ :=
  inverseFourthMajorant (52 * derivativeMajorant) / 12 * growthBase k ^ (-(9 / 5 : ℝ)) +
    16 / r ^ 2 * growthBase k ^ (1 - 3 * goodExponent)
end StandardMapEntropy
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TransferCore
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy

noncomputable def transferProductInv (v : ℕ → ℝ) : ℕ → (ℂ →L[ℝ] ℂ)
  | 0 => ContinuousLinearMap.id ℝ ℂ
  | n+1 => (transferProductInv v n).comp (transferStepInv (v (n+1)))
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ObservationTransport
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
lemma transferStep_difference_bound (v w : ℝ) : ‖transferStep v-transferStep w‖ ≤ |v-w| := by
  apply (transferStep v-transferStep w).opNorm_le_bound (abs_nonneg _)
  intro z
  have he : (transferStep v-transferStep w) z=((v-w)*z.re : ℝ) := by
    apply Complex.ext <;> simp only [sub_apply,Complex.sub_re,Complex.sub_im,
      transferStep_re,transferStep_im,Complex.ofReal_re,Complex.ofReal_im] <;> ring
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_mul]
  exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) (abs_nonneg _)

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_LogDerivativeCore
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy

noncomputable def tVariation (v dv : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | n+2 => v (n+1)*tVariation v dv (n+1)-tVariation v dv n+dv (n+1)*tSolution v (n+1)

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TorusDynamics
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma continuous_torusStep (k : ℝ) : Continuous (torusStep k) :=
  (((continuous_fst.nsmul 2).add ((continuous_kick k).comp continuous_fst)).sub continuous_snd).prodMk continuous_fst
lemma continuous_torusStep_symm (k : ℝ) : Continuous (torusStep k).symm :=
  continuous_snd.prodMk (((continuous_snd.nsmul 2).add ((continuous_kick k).comp continuous_snd)).sub continuous_fst)
noncomputable def torusStep_measurableEquiv (k : ℝ) : MeasurableEquiv Torus Torus where
  toEquiv := torusStep k
  measurable_toFun := (continuous_torusStep k).measurable
  measurable_invFun := (continuous_torusStep_symm k).measurable
lemma torusIter_add (k : ℝ) (i j : ℤ) (z : Torus) :
    torusIter k (i+j) z=torusIter k i (torusIter k j z) := by
  simp only [torusIter,zpow_add,Equiv.Perm.coe_mul,Function.comp_apply]
lemma continuous_torusIter (k : ℝ) (i : ℤ) : Continuous (torusIter k i) := by
  cases i with
  | ofNat n =>
      change Continuous (torusIter k (n : ℤ))
      simpa only [torusIter,zpow_natCast,Equiv.Perm.coe_pow] using (continuous_torusStep k).iterate n
  | negSucc n => simpa only [torusIter,zpow_negSucc,← inv_pow,Equiv.Perm.inv_def,Equiv.Perm.coe_pow] using
      (continuous_torusStep_symm k).iterate (n+1)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_GridPartition
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal Classical BigOperators
namespace StandardMapEntropy
lemma circleRep_mem (x : Circle) : circleRep x∈Ico (0:ℝ) 1 := by
  have h:=(AddCircle.equivIco 1 0 x).property
  simpa only [zero_add,circleRep] using h
noncomputable def gridIndex (Q:ℕ) (hQ:0<Q) (x:Circle) : Fin Q :=
  ⟨⌊(Q:ℝ)*circleRep x⌋₊,(Nat.floor_lt (mul_nonneg (Nat.cast_nonneg _) (circleRep_mem x).1)).mpr
    (by nlinarith [(circleRep_mem x).2,(Nat.cast_pos.mpr hQ : (0:ℝ)<Q)])⟩
noncomputable def gridLabel (Q:ℕ) (hQ:0<Q) (z:Torus) : Fin (Q*Q+1) :=
  (finProdFinEquiv (gridIndex Q hQ z.1,gridIndex Q hQ z.2)).castSucc
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ClosedEligibility
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy

noncomputable def prefixEligible (k : ℝ) (B J : ℕ) (z : ℝ × ℝ) : Prop :=
  (∀ i, 1 ≤ i → i ≤ B → growthBase k^((49/50:ℝ)*(i:ℝ)) ≤
    ‖transferProduct (orbitCoefficient k z.1 z.2) i‖) ∧
  ‖transferProduct (orbitCoefficient k z.1 z.2) B‖/3 ≤
    |tSolution (orbitCoefficient k z.1 z.2) J|

lemma continuous_transferStep : Continuous transferStep := by
  apply Metric.continuous_iff.mpr
  intro v ε hε
  refine ⟨ε,hε,?_⟩
  intro w hw
  rw [dist_eq_norm]
  exact (transferStep_difference_bound w v).trans_lt (by simpa only [Real.dist_eq] using hw)

lemma continuous_transferProduct_params {α : Type*} [TopologicalSpace α]
    (v : α → ℕ → ℝ) (hv : ∀ n, Continuous (fun x => v x n)) (n : ℕ) :
    Continuous (fun x => transferProduct (v x) n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact (continuous_transferStep.comp (hv (n+1))).clm_comp ih

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TorusObservations
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma continuous_cosine : Continuous cosine := by
  apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))).continuous_iff.mpr
  change Continuous (fun x : ℝ => cosine (x : Circle))
  simpa only [cosine_coe,Function.comp_def,Pi.mul_apply,id_eq] using
    (Real.continuous_cos.comp (continuous_const.mul continuous_id))
lemma continuous_torusPotential (k : ℝ) : Continuous (torusPotential k) :=
  continuous_const.add (continuous_const.mul continuous_cosine)
lemma continuous_torusSegmentCoefficient (k : ℝ) (a : ℤ) (i : ℕ) :
    Continuous (fun z => torusSegmentCoefficient k z a i) :=
  (continuous_torusPotential k).comp (continuous_fst.comp (continuous_torusIter k _))
lemma continuous_torusSegmentTransfer (k : ℝ) (a : ℤ) (n : ℕ) :
    Continuous (fun z => torusSegmentTransfer k z a n) :=
  continuous_transferProduct_params (fun z i => torusSegmentCoefficient k z a i)
    (fun i => continuous_torusSegmentCoefficient k a i) n
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_CocycleAlgebra
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma torusSegmentTransfer_shift (k : ℝ) (z : Torus) (a b : ℤ) (n : ℕ) :
    torusSegmentTransfer k (torusIter k b z) a n=torusSegmentTransfer k z (a+b) n := by
  unfold torusSegmentTransfer
  congr 1
  funext i
  unfold torusSegmentCoefficient
  rw [← torusIter_add]
  congr 3
  ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ProductDistances
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma productDistance_forward (k : ℝ) (z : Torus) (i : ℤ) (n : ℕ) :
    productDistance k z i (i+(n:ℤ))=Real.log ‖torusSegmentTransfer k z i n‖/Real.log (growthBase k) := by
  simp only [productDistance,torusTransfer_forward]
lemma productDistance_shift (k : ℝ) (z : Torus) (i j a : ℤ) :
    productDistance k (torusIter k a z) i j=productDistance k z (i+a) (j+a) := by
  wlog hij : i≤j generalizing i j
  · rw [productDistance_symm k _ i j,productDistance_symm k _ (i+a) (j+a)]
    exact this j i (le_of_not_ge hij)
  have hn : i+((j-i).toNat:ℤ)=j := by rw [Int.toNat_of_nonneg (sub_nonneg.mpr hij)]; ring
  have hn' : i+a+((j-i).toNat:ℤ)=j+a := by omega
  rw [← hn,productDistance_forward]
  conv_rhs => rw [show i+((j-i).toNat:ℤ)+a=i+a+((j-i).toNat:ℤ) by ring]
  rw [productDistance_forward,torusSegmentTransfer_shift]
lemma continuous_productDistance (k : ℝ) (hk : 0≤k) (i j : ℤ) :
    Continuous (fun z => productDistance k z i j) := by
  wlog hij : i≤j generalizing i j
  · have hh := this j i (le_of_not_ge hij)
    simpa only [productDistance_symm k _ j i] using hh
  have hn : i+((j-i).toNat:ℤ)=j := by rw [Int.toNat_of_nonneg (sub_nonneg.mpr hij)]; ring
  rw [← hn]
  simp only [productDistance_forward]
  apply Continuous.div_const
  exact (continuous_torusSegmentTransfer k i _).norm.log (fun z => by
    have := (torusSegmentTransfer_norm_bounds k hk z i (j-i).toNat).1; linarith)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ManyGood
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
noncomputable def badIndices (M : ℝ) (v : ℕ → ℝ) (b : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc (2:ℕ) (N-2)).filter fun j => ¬GoodIndex M v b j
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_CancellationVector
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
noncomputable def torusSmallEndpoints (k : ℝ) (Np Nm : ℕ) (R : ℝ) (z : Torus) : Prop :=
  ∃ b ∈ Icc (-growthBase k) (growthBase k),
    ‖torusSegmentTransfer k z.swap 0 (Nm-1) ⟨b,1⟩‖ ≤ R ∧
    ‖torusSegmentTransfer k z 0 Np ⟨1,b⟩‖ ≤ R
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_CancellationTheorem
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
noncomputable def torusCancellation (k : ℝ) (n : ℕ) (z : Torus) : Prop :=
  growthBase k^((1-1/100000000:ℝ)*(n:ℝ)) ≤ ‖torusSegmentTransfer k z (-(n:ℤ)) n‖ ∧
  growthBase k^((1-1/100000000:ℝ)*(n:ℝ)) ≤ ‖torusSegmentTransfer k z 0 n‖ ∧
  ‖torusSegmentTransfer k z (-(n:ℤ)) (n+n)‖ ≤ growthBase k^((1/100000000:ℝ)*(n:ℝ))
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_DoublingPointwise
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
noncomputable def wingDefect (k : ℝ) (z : Torus) (n : ℕ) : ℝ :=
  (n:ℝ)-min (productDistance k z 0 (-(n:ℤ))) (productDistance k z 0 (n:ℤ))
noncomputable def cancellationLoss (k : ℝ) (z : Torus) (n : ℕ) : ℝ :=
  productDistance k z 0 (-(n:ℤ))+productDistance k z 0 (n:ℤ)-productDistance k z (-(n:ℤ)) (n:ℤ)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_MeanDeficit
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
noncomputable def torusIterMeasurableEquiv (k : ℝ) (a : ℤ) : Torus ≃ᵐ Torus where
  toEquiv := (torusStep k)^a
  measurable_toFun := (continuous_torusIter k a).measurable
  measurable_invFun := by
    have hh := (continuous_torusIter k (-a)).measurable
    simpa only [torusIter,zpow_neg,Equiv.Perm.inv_def] using hh
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_MeanCancellation
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
noncomputable def cancellationWeight (k : ℝ) (s : ℕ) (z : Torus) : ℝ :=
  if torusCancellation k s z then 2*(s:ℝ)+2 else 0
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_MeanGrowth
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
noncomputable def meanLoss (k : ℝ) (n : ℕ) : ℝ :=
  (n:ℝ)-∫ z,productDistance k z 0 (n:ℤ) ∂area
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_CosineNull
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StandardMapEntropy
instance circleVolumeNullSingleton : NullSingletonClass (volume : Measure Circle) := by
  constructor
  intro x
  rw [← Metric.closedBall_zero (x := x),AddCircle.volume_closedBall]
  norm_num
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_FixedDeficit
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
noncomputable def cosineBad (δ : ℝ) (x : Circle) : ℝ :=
  {x : Circle | |cosine x|≤δ}.indicator (fun _ => 1) x
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_DyadicArrays
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace StandardMapEntropy

lemma dyadicTime_dense : Dense (Set.range ((↑) : DyadicTime → ℝ)) := by
  rw [dense_iff_inter_open]
  intro U hU hUn
  obtain ⟨x,hx⟩ := hUn
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt hε
  let m := n
  have hp (n : ℕ) : (n:ℝ)+1≤2^n := by
    induction n with
    | zero => norm_num
    | succ n ih => rw [pow_succ]; push_cast; nlinarith
  let a : ℤ := ⌊x*2^m⌋
  let y : DyadicTime := ⟨(a:ℝ)/2^m,m,a,rfl⟩
  have hpow : (0:ℝ)<2^m := by positivity
  have hfl : (a:ℝ)≤x*2^m ∧ x*2^m<(a:ℝ)+1 := ⟨Int.floor_le _,Int.lt_floor_add_one _⟩
  have hd : dist (y:ℝ) x<ε := by
    rw [Real.dist_eq]
    change |(a:ℝ)/2^m-x|<ε
    rw [abs_lt]
    constructor
    · have hεp : (1:ℝ)<ε*2^m := by
        have he := (div_lt_iff₀ (show (0:ℝ)<(n:ℝ)+1 by positivity)).mp hn
        have hp' := hp m
        change (n:ℝ)+1≤2^m at hp'
        nlinarith
      have hlow : x-ε<(a:ℝ)/2^m := (lt_div_iff₀ hpow).mpr (by nlinarith [hfl.2])
      linarith
    · have hle : (a:ℝ)/2^m≤x := (div_le_iff₀ hpow).mpr hfl.1
      linarith
  exact ⟨y,hball hd,⟨y,rfl⟩⟩

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ArrayTests
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma continuous_arrayTranslate (r : DyadicTime) : Continuous (arrayTranslate r) := by
  apply Continuous.subtype_mk
  apply continuous_pi; intro s
  apply continuous_pi; intro t
  exact continuous_arrayEval (s+r) (t+r)
lemma arrayTranslate_add (r q : DyadicTime) (d : DistanceArray) :
    arrayTranslate r (arrayTranslate q d)=arrayTranslate (r+q) d := by
  apply Subtype.ext
  funext s t
  simp only [arrayTranslate,add_assoc]
noncomputable def arrayTranslation (r : DyadicTime) : DistanceArray ≃ₜ DistanceArray where
  toFun := arrayTranslate r
  invFun := arrayTranslate (-r)
  left_inv := by intro d; rw [arrayTranslate_add,neg_add_cancel,arrayTranslate_zero]
  right_inv := by intro d; rw [arrayTranslate_add,add_neg_cancel,arrayTranslate_zero]
  continuous_toFun := continuous_arrayTranslate r
  continuous_invFun := continuous_arrayTranslate (-r)
noncomputable def arrayV (s t : DyadicTime) (d : DistanceArray) : ℝ :=
  (arrayShortfall s (dyadicMid s t) d-arrayShortfall (dyadicMid s t) t d)^2
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ArrayAffinity
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology
namespace StandardMapEntropy
noncomputable def arrayTest (i : ArrayTestIndex) (d : DistanceArray) : ℝ := arrayJ i.val.1 i.val.2 d+arrayV i.val.1 i.val.2 d
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ArrayMoments
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
noncomputable def meanSquareDeficit (k : ℝ) (n : ℕ) : ℝ :=
  ∫ z,(torusShortfall k z 0 n)^2 ∂area
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_NonaffineLimits
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped Topology ENNReal CompactlySupported Classical
namespace StandardMapEntropy
instance instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray (μ : Measure DistanceArray) [IsFiniteMeasure μ] : IsFiniteMeasure (nonaffinePart μ) := inferInstanceAs (IsFiniteMeasure (μ.comap Subtype.val))
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ArrayActions
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped Topology CompactlySupported Classical
namespace StandardMapEntropy
lemma arrayTranslate_mem_affine_iff (r : DyadicTime) (d : DistanceArray) :
    arrayTranslate r d ∈ affineLocus ↔ d ∈ affineLocus := by
  constructor
  · rintro ⟨w,hw⟩
    have hh := congrArg (arrayTranslate (-r)) hw
    rw [arrayTranslate_affine,arrayTranslate_add,neg_add_cancel,arrayTranslate_zero] at hh
    exact ⟨w,hh⟩
  · rintro ⟨w,rfl⟩; exact ⟨w,(arrayTranslate_affine r w).symm⟩
noncomputable def nonaffineTranslation (r : DyadicTime) : NonAffineArray ≃ₜ NonAffineArray where
  toFun d := ⟨arrayTranslate r d.val,by simpa only [arrayTranslate_mem_affine_iff] using d.property⟩
  invFun d := ⟨arrayTranslate (-r) d.val,by simpa only [arrayTranslate_mem_affine_iff] using d.property⟩
  left_inv d := by apply Subtype.ext; exact (arrayTranslation r).left_inv d.val
  right_inv d := by apply Subtype.ext; exact (arrayTranslation r).right_inv d.val
  continuous_toFun := (continuous_arrayTranslate r).comp continuous_subtype_val |>.subtype_mk _
  continuous_invFun := (continuous_arrayTranslate (-r)).comp continuous_subtype_val |>.subtype_mk _
noncomputable def nonaffineDilation : CocompactMap NonAffineArray NonAffineArray where
  toFun := nonaffineDilate
  continuous_toFun := continuous_nonaffineDilate
  cocompact_tendsto' := (isProperMap_iff_tendsto_cocompact.mp proper_nonaffineDilate).2

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ArrayTopology
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open TopologicalSpace Topology
namespace StandardMapEntropy
instance instPseudoMetrizableSpaceDistanceArray : PseudoMetrizableSpace DistanceArray := by
  let : PseudoMetrizableSpace (DyadicTime → DyadicTime → ℝ) := inferInstance
  exact PseudoMetrizableSpace.subtype _
instance instSecondCountableTopologyDistanceArray : SecondCountableTopology DistanceArray := by
  let : SecondCountableTopology (DyadicTime → DyadicTime → ℝ) := inferInstance
  exact Subtype.secondCountableTopology _
instance instPseudoMetrizableSpaceNonAffineArray : PseudoMetrizableSpace NonAffineArray := PseudoMetrizableSpace.subtype _
instance instSecondCountableTopologyNonAffineArray : SecondCountableTopology NonAffineArray := Subtype.secondCountableTopology _
instance instSigmaCompactSpaceNonAffineArray : SigmaCompactSpace NonAffineArray := inferInstance
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_RealArrays
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace StandardMapEntropy
def TreeArray (d : DistanceArray) : Prop := ∀ v x y z : DyadicTime,
  min (d.val v x+d.val v y-d.val x y) (d.val v y+d.val v z-d.val y z) ≤
    d.val v x+d.val v z-d.val x z
lemma isClosed_unitArray : IsClosed {d : DistanceArray | UnitArray d} := by
  unfold UnitArray
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun s => isClosed_iInter fun t => isClosed_le (continuous_arrayEval s t) continuous_const
lemma denseRange_dyadicTime : DenseRange ((↑) : DyadicTime → ℝ) := dyadicTime_dense
lemma dyadicPairDense : IsDenseInducing (Prod.map ((↑) : DyadicTime → ℝ) ((↑) : DyadicTime → ℝ)) :=
  ((isUniformInducing_val (dyadicTimes:Set ℝ)).prod (isUniformInducing_val (dyadicTimes:Set ℝ))).isDenseInducing
    (denseRange_dyadicTime.prodMap denseRange_dyadicTime)
noncomputable def realArray (d : DistanceArray) (s t : ℝ) : ℝ :=
  dyadicPairDense.extend (fun p : DyadicTime × DyadicTime => d.val p.1 p.2) (s,t)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ArrayHalf
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped Topology Classical
namespace StandardMapEntropy
lemma arrayHalf_unit (d : DistanceArray) (hu : UnitArray d) : UnitArray (arrayHalf d hu) := by
  intro s t
  have hh := hu (dyadicHalf s) (dyadicHalf t)
  change d.val (dyadicHalf s) (dyadicHalf t)≤|(t:ℝ)/2-(s:ℝ)/2| at hh
  rw [←sub_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
  change 2*d.val (dyadicHalf s) (dyadicHalf t)≤|(t:ℝ)-(s:ℝ)|
  linarith
lemma arrayDilate_unit (d : DistanceArray) (hu : UnitArray d) : UnitArray (arrayDilate d) := by
  intro s t
  have hh := hu (s+s) (t+t)
  change d.val (s+s) (t+t)≤|((t:ℝ)+(t:ℝ))-((s:ℝ)+(s:ℝ))| at hh
  rw [show ((t:ℝ)+(t:ℝ))-((s:ℝ)+(s:ℝ))=2*((t:ℝ)-(s:ℝ)) by ring,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
  change d.val (s+s) (t+t)/2≤|(t:ℝ)-(s:ℝ)|
  linarith
lemma arrayHalf_dilate (d : DistanceArray) (hu : UnitArray d) : arrayHalf (arrayDilate d) (arrayDilate_unit d hu)=d := by
  apply Subtype.ext; funext s t
  change 2*(d.val (dyadicHalf s+dyadicHalf s) (dyadicHalf t+dyadicHalf t)/2)=d.val s t
  rw [dyadicHalf_add_self,dyadicHalf_add_self]; ring
lemma continuous_nonaffineHalfOn : Continuous nonaffineHalfOn := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi; intro s
  apply continuous_pi; intro t
  exact continuous_const.mul ((continuous_arrayEval (dyadicHalf s) (dyadicHalf t)).comp (continuous_subtype_val.comp continuous_subtype_val))
lemma measurable_nonaffineHalf : Measurable nonaffineHalf := by
  exact continuous_nonaffineHalfOn.measurable.dite measurable_subtype_coe
    (isClosed_unitArray.preimage continuous_subtype_val).measurableSet
lemma nonaffineHalf_unit (d : NonAffineArray) (hu : UnitArray d.val) : UnitArray (nonaffineHalf d).val := by
  rw [nonaffineHalf,dite_eq_left hu]
  exact arrayHalf_unit d.val hu
lemma nonaffineDilate_half (d : NonAffineArray) (hu : UnitArray d.val) : nonaffineDilate (nonaffineHalf d)=d := by
  apply Subtype.ext
  rw [nonaffineHalf,dite_eq_left hu]
  exact arrayDilate_half d.val hu
lemma nonaffineHalf_dilate (d : NonAffineArray) (hu : UnitArray d.val) : nonaffineHalf (nonaffineDilate d)=d := by
  have hh : UnitArray (nonaffineDilate d).val := arrayDilate_unit d.val hu
  rw [nonaffineHalf,dite_eq_left hh]
  apply Subtype.ext
  exact arrayHalf_dilate d.val hu
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ShapeTopology
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology Classical
namespace StandardMapEntropy
def locallyAffineSet (d : ℝ → ℝ → ℝ) : Set ℝ := {x | ∃w,LocallyAffineAt d x w}
def locallyUnitSet (d : ℝ → ℝ → ℝ) : Set ℝ := {x | LocallyAffineAt d x 1}
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_MiddleCount
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy

noncomputable def bridgeMiddleGood (z : ℕ → ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (bridgeMiddle N).filter (MiddleLogGood z N)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_MiddlePrefixBridge
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
noncomputable def torusPrefixGrowth (k : ℝ) (B : ℕ) (z : Torus) : Prop :=
  ∀ i, 1 ≤ i → i ≤ B → growthBase k^((49/50:ℝ)*(i:ℝ)) ≤ ‖torusSegmentTransfer k z 0 i‖
noncomputable def middlePrefixEvent (k : ℝ) (Bp Bm : ℕ) : Set Torus :=
  {z | torusPrefixGrowth k Bp z ∧ torusPrefixGrowth k Bm z.swap}
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_VectorGrowth
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
noncomputable def transferVectorLog (M : ℝ) (v : ℕ → ℝ) (u : ℂ) (j : ℕ) : ℝ :=
  Real.log ‖transferProduct v j u‖/Real.log M
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BridgeAveraging
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
noncomputable def torusFastBridge (k : ℝ) (z : Torus) (N : ℕ) : Prop :=
  growthBase k^((999/1000:ℝ)*(N:ℝ))≤‖torusSegmentTransfer k z 0 N‖
noncomputable def torusGoodMiddles (k : ℝ) (z : Torus) (N : ℕ) : Finset ℕ := by
  classical
  exact (bridgeMiddle N).filter (fun i => torusIter k (i:ℤ) z∈middlePrefixEvent k (N-i) i)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_MiddleObservationBridge
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
noncomputable def shortfallObservation (k : ℝ) {R : ℕ} (a : Fin R → ℤ) (n : Fin R → ℕ)
    (F : (Fin R → ℝ) → ℝ) (z : Torus) : ℝ := F (fun j => torusShortfall k z (a j) (n j))
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ScaleCancellation
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
noncomputable def arrayCancellation (s t : DyadicTime) (d : DistanceArray) : Prop :=
  (1-1/100000000:ℝ)*((t:ℝ)-(s:ℝ))/2<d.val s (dyadicMid s t) ∧
  (1-1/100000000:ℝ)*((t:ℝ)-(s:ℝ))/2<d.val (dyadicMid s t) t ∧
  d.val s t<(1/100000000:ℝ)*((t:ℝ)-(s:ℝ))/2
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BridgeVague
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
noncomputable def arrayBridgeEvent {Rw Rh : ℕ} (B : BridgeGrid Rw Rh)
    (Fw : (Fin Rw → ℝ) → ℝ) (Fh : (Fin Rh → ℝ) → ℝ) (ηw ηh : ℝ) : Set DistanceArray :=
  {d | (999/1000:ℝ)*((B.v:ℝ)-(B.u:ℝ))<d.val B.u B.v ∧
    ηw<arrayObservation B.sw B.tw Fw d ∧ ηh<arrayObservation B.sh B.th Fh d}
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_EndpointObservations
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
def intervalInWindow (j : ArrayTestIndex) (u : DyadicTime) (q : ℕ) : Prop :=
  -((1:ℝ)/(2:ℝ)^q)≤(j.val.1:ℝ)-(u:ℝ) ∧ (j.val.2:ℝ)-(u:ℝ)≤(1:ℝ)/(2:ℝ)^q
noncomputable def endpointBridgeEvent (u v : DyadicTime) (W H : EndpointObservation) (ηw ηh : ℝ) : Set DistanceArray :=
  {d | (999/1000:ℝ)*((v:ℝ)-(u:ℝ))< d.val u v ∧ ηw< W.value d ∧ ηh< H.value d}
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_RealBridge
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
def SlowPair (d : ℝ → ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ s t, (¬∃w,LocallyAffineAt d s w) → (¬LocallyAffineAt d t 1) → d s t≤ c*|t-s|
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ShapeCore
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology Classical
namespace StandardMapEntropy
def slowCore (d : ℝ → ℝ → ℝ) : Set ℝ := (locallyUnitSet d)ᶜ
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ShapeClassification
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology Classical
namespace StandardMapEntropy

def SlowShape (d : ℝ → ℝ → ℝ) (c : ℝ) : Prop :=
  (∀x y:ℝ,d x y≤ c*|y-x|) ∨
  (∃a:ℝ,(∀x≤ a,∀y≤ a,d x y=|y-x|) ∧ (∀x≥ a,∀y≥ a,d x y≤ c*|y-x|)) ∨
  (∃b:ℝ,(∀x≥ b,∀y≥ b,d x y=|y-x|) ∧ (∀x≤ b,∀y≤ b,d x y≤ c*|y-x|)) ∨
  (∃a b:ℝ,a< b ∧ ExteriorUnitRays d a b ∧ ∀x∈Icc a b,∀y∈Icc a b,d x y≤ c*|y-x|)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_CappedTests
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology Classical ENNReal
namespace StandardMapEntropy
noncomputable def capG (α : ℝ) (d : DistanceArray) : ℝ :=
  entropyCap α (arrayShortfall 0 (dyadicInt 2) d)-
    (entropyCap α (arrayShortfall 0 (dyadicInt 1) d)+entropyCap α (arrayShortfall (dyadicInt 1) (dyadicInt 2) d))/2
noncomputable def coreTestIndex : ArrayTestIndex := ⟨(0,dyadicInt 2),by norm_num⟩
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_FineArrays
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace StandardMapEntropy
noncomputable def dyadicFine (n : ℕ) (s : DyadicTime) : DyadicTime := (dyadicHalf^[n]) s
lemma dyadicFine_val (n : ℕ) (s : DyadicTime) : (dyadicFine n s:ℝ)=(s:ℝ)/(2:ℝ)^n := by
  induction n with
  | zero => simp [dyadicFine]
  | succ n ih =>
    rw [dyadicFine,Function.iterate_succ_apply']
    rw [dyadicHalf_val,show ((dyadicHalf^[n]) s:ℝ)=(s:ℝ)/(2:ℝ)^n from ih,pow_succ]
    ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TruncationArrays
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped ENNReal Classical
namespace StandardMapEntropy
noncomputable def unitDefect (d:DistanceArray) : ℝ :=
  max (arrayShortfall 0 (dyadicInt 1) d) (arrayShortfall (dyadicInt 1) (dyadicInt 2) d)+arrayJ 0 (dyadicInt 2) d
noncomputable def cutLeft (b:ℕ) : DyadicTime := dyadicInt 1-dyadicFine b (dyadicInt 1)
noncomputable def cutRight (b:ℕ) : DyadicTime := dyadicInt 1+dyadicFine b (dyadicInt 1)
lemma cutLeft_val (b:ℕ) : (cutLeft b:ℝ)=1-1/(2:ℝ)^b := by simp [cutLeft,dyadicFine_val]
lemma cutRight_val (b:ℕ) : (cutRight b:ℝ)=1+1/(2:ℝ)^b := by simp [cutRight,dyadicFine_val]
lemma cut_order (b:ℕ) : (cutLeft b:ℝ)<(cutRight b:ℝ) := by
  rw [cutLeft_val,cutRight_val]
  have : (0:ℝ)<1/2^b := by positivity
  linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_WeightSlow
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
noncomputable def slowCapOpen : Set DistanceArray :=
  {d | 3/10000 < min (arrayShortfall 0 (dyadicInt 1) d) (arrayShortfall (dyadicInt 1) (dyadicInt 2) d)}
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_WeightUnit
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
noncomputable def unitCapOpen (b:ℕ) : Set DistanceArray := {d | unitDefect d<1/(2:ℝ)^b}
noncomputable def unitAffine : DistanceArray := affineArray ⟨1,by norm_num⟩
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_WeightBridge
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
noncomputable def farTestIndex : ArrayTestIndex := ⟨(dyadicInt 4097,dyadicInt 4098),by norm_num⟩
noncomputable def middleCapOpen (η:ℝ) : Set DistanceArray :=
  {d | (999/1000:ℝ)*4096 < d.val (dyadicInt 1) (dyadicInt 4097) ∧
    η < clippedShortfall (dyadicInt 4097) (dyadicInt 4098) d ∧
    0 < arrayShortfall 0 (dyadicInt 1) d ∧ 0 < arrayShortfall (dyadicInt 1) (dyadicInt 2) d}
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TerminalCap
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
noncomputable def capF (α : ℝ) (d : DistanceArray) : ℝ := entropyCap α (arrayShortfall 0 (dyadicInt 1) d)
noncomputable def capFpos (α : ℝ) (d : DistanceArray) : ℝ := entropyCap α (max (arrayShortfall 0 (dyadicInt 1) d) 0)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_EndpointDefinition
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology Classical
namespace StandardMapEntropy

noncomputable def leftEndpoint (d : DistanceArray) : EReal :=
  ⨅s:DyadicTime,⨅t:DyadicTime,if d.val s t≠|(t:ℝ)-(s:ℝ)| then ((max (s:ℝ) (t:ℝ)):EReal) else ⊤
noncomputable def rightEndpoint (d : DistanceArray) : EReal :=
  ⨆s:DyadicTime,⨆t:DyadicTime,if d.val s t≠|(t:ℝ)-(s:ℝ)| then ((min (s:ℝ) (t:ℝ)):EReal) else ⊥
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_EndpointCovariance
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology Classical
namespace StandardMapEntropy
noncomputable def dyadicHalfEquiv : DyadicTime ≃ DyadicTime where
  toFun := dyadicHalf
  invFun := fun s => s+s
  left_inv := dyadicHalf_add_self
  right_inv := dyadicHalf_double
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_EndpointClasses
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology Classical
namespace StandardMapEntropy
noncomputable def endpointLeft (d:DistanceArray) : ℝ := (leftEndpoint d).toReal
noncomputable def endpointRight (d:DistanceArray) : ℝ := (rightEndpoint d).toReal
def leftRayClass : Set DistanceArray := {d | leftEndpoint d≠⊥ ∧ leftEndpoint d≠⊤ ∧ rightEndpoint d=⊤}
def rightRayClass : Set DistanceArray := {d | leftEndpoint d=⊥ ∧ rightEndpoint d≠⊥ ∧ rightEndpoint d≠⊤}
def twoRayClass : Set DistanceArray := {d | leftEndpoint d≠⊥ ∧ leftEndpoint d≠⊤ ∧ rightEndpoint d≠⊥ ∧ rightEndpoint d≠⊤}
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ScaleAction
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped Classical
namespace StandardMapEntropy
noncomputable def nonaffineDouble (d:NonAffineArray) : NonAffineArray :=
  if UnitArray d.val then nonaffineDilate d else d
lemma measurable_nonaffineDouble : Measurable nonaffineDouble :=
  continuous_nonaffineDilate.measurable.ite (isClosed_unitArray.preimage continuous_subtype_val).measurableSet measurable_id
noncomputable def scaleEquiv : NonAffineArray ≃ᵐ NonAffineArray where
  toFun := nonaffineDouble
  invFun := nonaffineHalf
  left_inv d := by
    by_cases h:UnitArray d.val
    · simpa only [nonaffineDouble,ite_eq_left h] using nonaffineHalf_dilate d h
    · simp only [nonaffineDouble,ite_eq_right h,nonaffineHalf,dite_eq_right h]
  right_inv d := by
    by_cases h:UnitArray d.val
    · rw [nonaffineDouble,ite_eq_left (nonaffineHalf_unit d h),nonaffineDilate_half d h]
    · simp only [nonaffineHalf,dite_eq_right h,nonaffineDouble,ite_eq_right h]
  measurable_toFun := measurable_nonaffineDouble
  measurable_invFun := measurable_nonaffineHalf
noncomputable def scaleZ (j:ℤ) : Equiv.Perm NonAffineArray := scaleEquiv.toEquiv ^ j
@[simp] lemma scaleZ_zero (d:NonAffineArray) : scaleZ 0 d=d := by simp only [scaleZ,zpow_zero]; rfl
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ScaleEndpoints
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped Classical
namespace StandardMapEntropy
noncomputable def coreLength (d:DistanceArray) : ℝ := endpointRight d-endpointLeft d
noncomputable def lengthBand (j:ℤ) : Set NonAffineArray := {d | UnitArray d.val ∧ d.val∈twoRayClass ∧ (2:ℝ)^j ≤ coreLength d.val ∧ coreLength d.val<(2:ℝ)^(j+1)}
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BandIntensity
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped ENNReal Classical
namespace StandardMapEntropy
noncomputable def bandLaw (μ:Measure NonAffineArray) : Measure NonAffineArray := μ.restrict (lengthBand 0)
noncomputable def bandIntensity (μ:Measure NonAffineArray) : Measure ℝ := (bandLaw μ).map (fun d => endpointLeft d.val)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ScaleEvaluation
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped Classical
namespace StandardMapEntropy
noncomputable def dyadicZoom (j:ℤ) (s:DyadicTime) : DyadicTime := match j with
  | .ofNat n => (2^n) • s
  | .negSucc n => dyadicFine (n+1) s
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BandCap
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped ENNReal Classical
namespace StandardMapEntropy
noncomputable def bandCap (α:ℝ) (t:DyadicTime) (d:NonAffineArray) : ℝ := entropyCap α (arrayShortfall 0 t d.val)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BandCoboundary
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped ENNReal Classical
namespace StandardMapEntropy
noncomputable def bandMoment (μ:Measure NonAffineArray) (α:ℝ) (j:ℤ) : ℝ :=
  ∫d,bandCap α (dyadicZoom j (dyadicInt 1)) d ∂bandLaw μ
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TerminalStrict
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace StandardMapEntropy
noncomputable def fineCap (α:ℝ) (n:ℕ) (z:DyadicTime) (d:NonAffineArray) : ℝ :=
  capF α ((nonaffineHalf^[n]) (nonaffineTranslation z d)).val
noncomputable def fineCapEvent (α:ℝ) (z:DyadicTime) (N:ℕ) : Set NonAffineArray :=
  {d | ∀n≥N,fineCap α n z d=1}
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_Subadditive
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace StandardMapEntropy
open BoundedSubadditive

lemma torusIter_nat_apply (k : ℝ) (n : ℕ) (z : Torus) :
    torusIter k (n : ℤ) z = (torusStep k)^[n] z := by
  simp only [torusIter, zpow_natCast, Equiv.Perm.coe_pow]

lemma productDistance_one_shift_bound (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (z : Torus) :
    |productDistance k (torusStep k z) 0 (n : ℤ) - productDistance k z 0 (n : ℤ)| ≤ 2 := by
  have ht : torusStep k z = torusIter k 1 z := by
    simp only [torusIter, zpow_one]
  rw [ht, productDistance_shift]
  simp only [zero_add]
  have h10 := productDistance_le k hk z 1 0
  have h01 := productDistance_le k hk z 0 1
  have hnn := productDistance_le k hk z (n : ℤ) ((n : ℤ) + 1)
  have hnn' := productDistance_le k hk z ((n : ℤ) + 1) (n : ℤ)
  norm_num only [Int.cast_one, Int.cast_zero, zero_sub, sub_zero, abs_neg, abs_one] at h10 h01
  have hncast : (((n : ℤ) + 1 : ℤ) : ℝ) = (n : ℝ) + 1 := by push_cast; rfl
  rw [hncast, Int.cast_natCast, add_sub_cancel_left, abs_one] at hnn
  rw [hncast, Int.cast_natCast, sub_add_cancel_left, abs_neg, abs_one] at hnn'
  apply abs_le.mpr
  constructor
  · have h1 := productDistance_triangle k hk z 0 1 (n : ℤ)
    have h2 := productDistance_triangle k hk z 1 ((n : ℤ) + 1) (n : ℤ)
    linarith
  · have h1 := productDistance_triangle k hk z 1 0 ((n : ℤ) + 1)
    have h2 := productDistance_triangle k hk z 0 (n : ℤ) ((n : ℤ) + 1)
    linarith

noncomputable def transferCocycle (k : ℝ) (hk : 0 ≤ k) : Cocycle Torus (torusStep k) where
  value n z := productDistance k z 0 (n : ℤ)
  measurable n := (continuous_productDistance k hk 0 (n : ℤ)).measurable
  nonneg n z := productDistance_nonneg k hk z 0 (n : ℤ)
  le_time n z := by simpa using productDistance_le k hk z 0 (n : ℤ)
  subadd m n z := by
    have hh := productDistance_triangle k hk z 0 (m : ℤ) ((m : ℤ) + (n : ℤ))
    rw [← torusIter_nat_apply, productDistance_shift]
    simpa only [Nat.cast_add, zero_add, add_zero, add_comm] using hh
  shift_bound n z := productDistance_one_shift_bound k hk n z

noncomputable def transferLyapunov (k : ℝ) (hk : 0 ≤ k) (z : Torus) : ℝ :=
  Real.log (growthBase k) * (transferCocycle k hk).lowerRate z

def TransferLimit (k : ℝ) (L : Torus → ℝ) : Prop :=
  Measurable L ∧ Integrable L area ∧ (∀ z, 0 ≤ L z) ∧
  (∀ z, L (torusStep k z) = L z) ∧
  ∀ᵐ z ∂area, Tendsto
    (fun n : ℕ => Real.log ‖torusSegmentTransfer k z 0 n‖ / (n : ℝ))
    atTop (𝓝 (L z))

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_DerivativeGrowth
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

lemma complexProjection_standardLift (k : ℝ) (z : ℂ) :
    complexProjection (standardLift k z) = standardMap k (complexProjection z) := by
  ext <;> simp [complexProjection, standardLift, standardMap]

end StandardMapEntropy

namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

lemma hasFDerivAt_standardLift (k : ℝ) (z : ℂ) :
    HasFDerivAt (standardLift k) (standardDerivative k (complexProjection z)) z := by
  have hr := Complex.reCLM.hasFDerivAt (x := z)
  have hi := Complex.imCLM.hasFDerivAt (x := z)
  have hs := ((hr.const_mul (2*Real.pi)).sin).const_mul k
  have hh := Complex.equivRealProdCLM.symm.toContinuousLinearMap.hasFDerivAt.comp z
    (((hr.add hi).add hs).prodMk (hi.add hs))
  convert! hh using 1; try rfl
  apply ContinuousLinearMap.ext
  intro w
  apply Complex.ext <;> simp [standardDerivative_re, standardDerivative_im, complexProjection,
    torusPotential, cosine_coe] <;> ring

noncomputable def standardLyapunov (k : ℝ) (hk : 0 ≤ k) (z : Torus) : ℝ :=
  transferLyapunov k hk (recurrenceCoordinates z)

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_InverseLyapunov
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

def coincidentLines (k : ℝ) (hk : 0 ≤ k) : Set Torus :=
  {z | 0 < standardLyapunov k hk z ∧ wedge (stableVector k z) (unstableVector k z)=0}

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_TransverseLines
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable def stableGrowthAverage (k : ℝ) (n : ℕ) (z : Torus) : ℝ :=
  Real.log ‖standardDerivativeProduct k z n (stableVector k z)‖/(n : ℝ)
noncomputable def stableBackwardAverage (k : ℝ) (n : ℕ) (z : Torus) : ℝ :=
  Real.log ‖standardInverseDerivativeProduct k z n (stableVector k z)‖/(n : ℝ)

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma stableScale_ge_one (k χ : ℝ) (z : Torus) : 1 ≤ stableScale k χ z := by
  simpa only [stableScale, Real.sqrt_one] using Real.sqrt_le_sqrt (le_max_left (1 : ℝ) (stableEnergy k χ z))
lemma unstableScale_ge_one (k χ : ℝ) (z : Torus) : 1 ≤ unstableScale k χ z := by
  simpa only [unstableScale, Real.sqrt_one] using Real.sqrt_le_sqrt (le_max_left (1 : ℝ) (unstableEnergy k χ z))

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_BoundedTempering
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

def spectralGapRegion (k : ℝ) (hk : 0≤k) (χ : ℝ) : Set Torus :=
  {z | χ < standardLyapunov k hk z}

noncomputable def energyRatioBound (k χ : ℝ) : ℝ :=
  1+Real.exp (2*χ)*(9*growthBase k)^2+(9*growthBase k)^2

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma planeFrame_apply (s u v : ℂ) (a b : ℝ) :
    planeFrame s u a b v = (v.re/(2*a)) • s + (v.im/(2*b)) • u := by
  simp only [planeFrame, add_apply, ContinuousLinearMap.smulRight_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, smul_smul, div_eq_mul_inv]

lemma planeCoframe_apply (s u v : ℂ) (a b : ℝ) :
    planeCoframe s u a b v = ⟨2*a*wedge v u / wedge s u, 2*b*wedge s v / wedge s u⟩ := rfl

lemma planeFrame_coframe (s u : ℂ) {a b : ℝ} (ha : a≠0) (hb : b≠0)
    (hw : wedge s u≠0) :
    (planeFrame s u a b).comp (planeCoframe s u a b)=ContinuousLinearMap.id ℝ ℂ := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, planeCoframe_apply,
    planeFrame_apply]
  apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im, Complex.smul_re,
    Complex.smul_im, smul_eq_mul]
  all_goals field_simp [ha,hb,hw]; dsimp only [wedge]; ring

lemma planeFrame_norm_le {s u : ℂ} (hs : ‖s‖=1) (hu : ‖u‖=1)
    {a b : ℝ} (ha : 1≤a) (hb : 1≤b) : ‖planeFrame s u a b‖≤1 := by
  have ha0 : 0<a := zero_lt_one.trans_le ha
  have hb0 : 0<b := zero_lt_one.trans_le hb
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [planeFrame_apply, one_mul]
  calc
    _ ≤ ‖(v.re/(2*a))•s‖+‖(v.im/(2*b))•u‖ := norm_add_le _ _
    _ = |v.re|/(2*a)+|v.im|/(2*b) := by
      rw [norm_smul, norm_smul, hs, hu, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_div, abs_div, abs_of_pos (by positivity : 0<2*a),
        abs_of_pos (by positivity : 0<2*b), mul_one, mul_one]
    _ ≤ ‖v‖/2+‖v‖/2 := add_le_add
      (le_trans (div_le_div_of_nonneg_right (Complex.abs_re_le_norm v) (by positivity))
        (div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) (by linarith)))
      (le_trans (div_le_div_of_nonneg_right (Complex.abs_im_le_norm v) (by positivity))
        (div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) (by linarith)))
    _ = ‖v‖ := by ring

lemma lyapunovFrame_norm_le (k χ : ℝ) (z : Torus) : ‖lyapunovFrame k χ z‖≤1 :=
  planeFrame_norm_le (norm_stableVector k z) (norm_unstableVector k z)
    (stableScale_ge_one k χ z) (unstableScale_ge_one k χ z)

lemma lyapunovFrame_coframe (k χ : ℝ) (z : Torus)
    (hw : wedge (stableVector k z) (unstableVector k z)≠0) :
    (lyapunovFrame k χ z).comp (lyapunovCoframe k χ z)=ContinuousLinearMap.id ℝ ℂ :=
  planeFrame_coframe _ _ (ne_of_gt (zero_lt_one.trans_le (stableScale_ge_one k χ z)))
    (ne_of_gt (zero_lt_one.trans_le (unstableScale_ge_one k χ z))) hw

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_MeasurableFrame
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace TemperedControl

variable {X : Type*} [MeasurableSpace X]

lemma control_nonneg (e : X ≃ᵐ X) {c : X → ℝ} (hc : ∀ x, 0 ≤ c x) (ε : ℝ) (x : X) :
    0 ≤ control e c ε x := tsum_nonneg fun _ => mul_nonneg (hc _) (Real.exp_pos _).le

lemma radius_pos (e : X ≃ᵐ X) {c : X → ℝ} (hc : ∀ x, 0 ≤ c x) (ε : ℝ) (x : X) :
    0 < radius e c ε x := by
  have := control_nonneg e hc ε x
  exact inv_pos.mpr (by linarith)

end TemperedControl
end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma chartControl_ge_one (k χ : ℝ) (z : Torus) : 1 ≤ chartControl k χ z := le_max_left _ _
lemma chartRadius_pos (k χ ε : ℝ) (z : Torus) : 0 < chartRadius k χ ε z :=
  TemperedControl.radius_pos _ (fun z => zero_le_one.trans (chartControl_ge_one k χ z)) ε z

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Stable_SmoothRemainder
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma potential_lift_sub_bound (k : ℝ) (z w : ℂ) :
    |torusPotential k (complexProjection z).1-torusPotential k (complexProjection w).1|≤
      4*Real.pi^2*|k| *‖z-w‖ := by
  have hc := Real.abs_cos_sub_cos_le (2*Real.pi*z.re) (2*Real.pi*w.re)
  have hz : |z.re-w.re|≤‖z-w‖ := Complex.abs_re_le_norm (z-w)
  have he : torusPotential k (complexProjection z).1-torusPotential k (complexProjection w).1 =
      2*Real.pi*k*(Real.cos (2*Real.pi*z.re)-Real.cos (2*Real.pi*w.re)) := by
    simp only [complexProjection,torusPotential,cosine_coe]
    ring
  rw [he,abs_mul]
  calc
    _ ≤ |2*Real.pi*k| * |2*Real.pi*z.re-2*Real.pi*w.re| :=
      mul_le_mul_of_nonneg_left hc (abs_nonneg _)
    _ = (4*Real.pi^2*|k|)*|z.re-w.re| := by
      rw [show 2*Real.pi*z.re-2*Real.pi*w.re=2*Real.pi*(z.re-w.re) by ring]
      simp only [abs_mul,abs_of_pos Real.pi_pos,abs_of_pos (by norm_num : (0 : ℝ)<2)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hz (by positivity)

lemma standardDerivative_lift_sub_bound (k : ℝ) (z w : ℂ) :
    ‖standardDerivative k (complexProjection z)-standardDerivative k (complexProjection w)‖≤
      derivativeVariationBound k*‖z-w‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (derivativeVariationBound_nonneg k) (norm_nonneg _))
  intro v
  have hre : ((standardDerivative k (complexProjection z)-standardDerivative k (complexProjection w)) v).re =
      (torusPotential k (complexProjection z).1-torusPotential k (complexProjection w).1)*v.re := by
    simp only [sub_apply,Complex.sub_re,standardDerivative_re]
    ring
  have him : ((standardDerivative k (complexProjection z)-standardDerivative k (complexProjection w)) v).im =
      (torusPotential k (complexProjection z).1-torusPotential k (complexProjection w).1)*v.re := by
    simp only [sub_apply,Complex.sub_im,standardDerivative_im]
    ring
  calc
    _ ≤ |((standardDerivative k (complexProjection z)-standardDerivative k (complexProjection w)) v).re|+
        |((standardDerivative k (complexProjection z)-standardDerivative k (complexProjection w)) v).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = 2*|torusPotential k (complexProjection z).1-torusPotential k (complexProjection w).1| * |v.re| := by
      rw [hre,him,abs_mul]
      ring
    _ ≤ 2*(4*Real.pi^2*|k| *‖z-w‖)*‖v‖ :=
      mul_le_mul (mul_le_mul_of_nonneg_left (potential_lift_sub_bound k z w) (by norm_num))
        (Complex.abs_re_le_norm v) (abs_nonneg _) (by positivity)
    _ = _ := by unfold derivativeVariationBound; ring

noncomputable def liftRemainder (k : ℝ) (z v : ℂ) : ℂ :=
  standardLift k (z+v)-standardLift k z-standardDerivative k (complexProjection z) v
@[simp] lemma liftRemainder_zero (k : ℝ) (z : ℂ) : liftRemainder k z 0=0 := by
  simp only [liftRemainder,add_zero,sub_self,map_zero]

lemma hasFDerivAt_liftRemainder (k : ℝ) (z v : ℂ) :
    HasFDerivAt (liftRemainder k z)
      (standardDerivative k (complexProjection (z+v))-standardDerivative k (complexProjection z)) v := by
  have hh := ((hasFDerivAt_standardLift k (z+v)).comp v ((hasFDerivAt_id v).const_add z)).sub_const (standardLift k z)
  have hh' := hh.sub (standardDerivative k (complexProjection z)).hasFDerivAt
  convert! hh' using 1
  all_goals try with_reducible_and_instances rfl

lemma liftRemainder_sub_bound (k : ℝ) (z : ℂ) {r : ℝ} {v w : ℂ}
    (hv : ‖v‖ ≤ r) (hw : ‖w‖ ≤ r) :
    ‖liftRemainder k z v-liftRemainder k z w‖≤derivativeVariationBound k*r*‖v-w‖ := by
  apply (convex_closedBall (0 : ℂ) r).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x _ => (hasFDerivAt_liftRemainder k z x).hasFDerivWithinAt) (fun x hx => ?_)
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hw)
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hv)
  have hh := standardDerivative_lift_sub_bound k (z+x) z
  rw [add_sub_cancel_left] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)
    (derivativeVariationBound_nonneg k))

end StandardMapEntropy

end
section
namespace StandardMapEntropy.NonlinearStable
open Filter
open scoped Topology NNReal

variable {ℓ δ : ℝ≥0}

lemma perron_contracting (r : Recurrence ℓ δ) (h : ℓ+δ<1) {s : ℝ} :
    ContractingWith (ℓ+δ) (r.perron (le_trans (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ δ from bot_le)) h.le) s) := by
  refine ⟨h,LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [dist_eq_norm,dist_eq_norm]
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro n
  have hh := perronValue_sub_bound r (le_trans (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ δ from bot_le)) h.le) s s x y n
  simpa only [BoundedContinuousFunction.sub_apply, perron_apply, sub_self, abs_zero,
    max_eq_right (mul_nonneg (ℓ+δ).coe_nonneg (norm_nonneg _))] using hh

noncomputable def Recurrence.solution (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) : Sequence :=
  ContractingWith.fixedPoint _ (perron_contracting r h (s := s))

lemma solution_fixed (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) :
    r.perron (le_trans (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ δ from bot_le)) h.le) s (r.solution h s)=r.solution h s :=
  (perron_contracting r h (s := s)).fixedPoint_isFixedPt

lemma fixed_norm_bound (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) (x : Sequence)
    (hx : r.perron (le_trans (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ δ from bot_le)) h.le) s x=x) : ‖x‖≤|s| := by
  apply bound_of_max_contraction (abs_nonneg _) (show ((ℓ+δ : ℝ≥0) : ℝ)<1 from h)
  conv_lhs => rw [← hx]
  apply (BoundedContinuousFunction.norm_le (le_trans (abs_nonneg _) (le_max_left _ _))).mpr
  intro n
  exact perronValue_norm_bound r (le_trans (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ δ from bot_le)) h.le) s x n

lemma solution_norm_bound (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) : ‖r.solution h s‖≤|s| :=
  fixed_norm_bound r h s _ (solution_fixed r h s)

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy.NonlinearStable
open Filter
open scoped Topology NNReal
variable {ℓ δ : ℝ≥0}

noncomputable def Recurrence.tail (r : Recurrence ℓ δ) (m : ℕ) : Recurrence ℓ δ where
  a n := r.a (m+n)
  b n := r.b (m+n)
  remainder n := r.remainder (m+n)
  stable_bound n := r.stable_bound (m+n)
  inverse_bound n := r.inverse_bound (m+n)
  b_ne n := r.b_ne (m+n)
  lipschitz n := r.lipschitz (m+n)
  zero n := r.zero (m+n)

noncomputable def Recurrence.graph (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) : ℝ :=
  (r.solution h s 0).2

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal

noncomputable def complexToPair : ℂ →L[ℝ] RealPlane := Complex.equivRealProdCLM.toContinuousLinearMap
noncomputable def pairToComplex : RealPlane →L[ℝ] ℂ := Complex.equivRealProdCLM.symm.toContinuousLinearMap
@[simp] lemma complexToPair_apply (v : ℂ) : complexToPair v=(v.re,v.im) := rfl
@[simp] lemma pairToComplex_apply (v : RealPlane) : pairToComplex v=⟨v.1,v.2⟩ := rfl
@[simp] lemma complexToPair_pairToComplex (v : RealPlane) : complexToPair (pairToComplex v)=v := by rfl
@[simp] lemma pairToComplex_complexToPair (v : ℂ) : pairToComplex (complexToPair v)=v := by rfl
lemma complexToPair_norm_le (v : ℂ) : ‖complexToPair v‖≤‖v‖ := by
  exact max_le (Complex.abs_re_le_norm v) (Complex.abs_im_le_norm v)
lemma pairToComplex_norm_le (v : RealPlane) : ‖pairToComplex v‖≤2*‖v‖ := by
  have hh := Complex.norm_le_abs_re_add_abs_im (pairToComplex v)
  have h1 : |v.1|≤‖v‖ := norm_fst_le v
  have h2 : |v.2|≤‖v‖ := norm_snd_le v
  exact hh.trans (by change |v.1|+|v.2|≤_; linarith)

noncomputable def flatFrame (q : ℝ) (F : ℂ →L[ℝ] ℂ) : RealPlane →L[ℝ] ℂ :=
  (q • F).comp pairToComplex
noncomputable def flatInverse (q : ℝ) (C : ℂ →L[ℝ] ℂ) : ℂ →L[ℝ] RealPlane :=
  complexToPair.comp (q⁻¹ • C)

lemma flatFrame_inverse {q : ℝ} (hq : q≠0) {F C : ℂ →L[ℝ] ℂ}
    (hFC : F.comp C=ContinuousLinearMap.id ℝ ℂ) (v : ℂ) :
    flatFrame q F (flatInverse q C v)=v := by
  have hh : F (C v)=v := congrArg (fun D : ℂ →L[ℝ] ℂ => D v) hFC
  simp only [flatInverse,flatFrame,ContinuousLinearMap.comp_apply,smul_apply,map_smul,
    pairToComplex_complexToPair,hh,smul_smul,inv_mul_cancel₀ hq,one_smul]

lemma flatFrame_norm_le {q : ℝ} (hq : 0≤q) {F : ℂ →L[ℝ] ℂ} (hF : ‖F‖≤1) :
    ‖flatFrame q F‖≤2*q := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  simp only [flatFrame,ContinuousLinearMap.comp_apply,smul_apply,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg hq]
  have hh := (F.le_opNorm (pairToComplex v)).trans (mul_le_mul_of_nonneg_right hF (norm_nonneg _))
  have hh' : ‖F (pairToComplex v)‖≤2*‖v‖ := by simpa only [one_mul] using hh.trans (by simpa using pairToComplex_norm_le v)
  exact (mul_le_mul_of_nonneg_left hh' hq).trans_eq (by ring)

lemma flatInverse_norm_le {q : ℝ} (hq : 0≤q) (C : ℂ →L[ℝ] ℂ) :
    ‖flatInverse q C‖≤q⁻¹*‖C‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hh := complexToPair_norm_le (q⁻¹ • C v)
  simp only [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg hq] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left (C.le_opNorm v) (inv_nonneg.mpr hq)).trans_eq (by ring))

noncomputable def flatRemainder (k : ℝ) (z : ℂ) (F : RealPlane →L[ℝ] ℂ)
    (C : ℂ →L[ℝ] RealPlane) (v : RealPlane) : RealPlane := C (liftRemainder k z (F v))
@[simp] lemma flatRemainder_zero (k : ℝ) (z : ℂ) (F : RealPlane →L[ℝ] ℂ)
    (C : ℂ →L[ℝ] RealPlane) : flatRemainder k z F C 0=0 := by
  simp only [flatRemainder,map_zero,liftRemainder_zero]

lemma flatRemainder_sub_bound (k : ℝ) (z : ℂ) (F : RealPlane →L[ℝ] ℂ)
    (C : ℂ →L[ℝ] RealPlane) {v w : RealPlane} (hv : ‖v‖≤1) (hw : ‖w‖≤1) :
    ‖flatRemainder k z F C v-flatRemainder k z F C w‖≤
      (‖C‖*derivativeVariationBound k*‖F‖^2)*‖v-w‖ := by
  have hfv : ‖F v‖≤‖F‖ := (F.le_opNorm v).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hv (norm_nonneg F))
  have hfw : ‖F w‖≤‖F‖ := (F.le_opNorm w).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hw (norm_nonneg F))
  calc
    _ = ‖C (liftRemainder k z (F v)-liftRemainder k z (F w))‖ := by rw [map_sub]; rfl
    _ ≤ ‖C‖*‖liftRemainder k z (F v)-liftRemainder k z (F w)‖ := C.le_opNorm _
    _ ≤ ‖C‖*(derivativeVariationBound k*‖F‖*‖F v-F w‖) :=
      mul_le_mul_of_nonneg_left (liftRemainder_sub_bound k z hfv hfw) (norm_nonneg C)
    _ ≤ ‖C‖*(derivativeVariationBound k*‖F‖*(‖F‖*‖v-w‖)) := by
      rw [←map_sub]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (F.le_opNorm (v-w))
        (mul_nonneg (derivativeVariationBound_nonneg k) (norm_nonneg F))) (norm_nonneg C)
    _ = _ := by ring

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Stable_LocalStable
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.NonlinearStable
open Filter
open scoped Topology NNReal

variable {ℓ δ : ℝ≥0}

lemma local_solution_bound (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1) {s : ℝ} (hs : |s|≤1) (n : ℕ) :
    ‖r.extend.solution h s n‖≤1 :=
  ((r.extend.solution h s).norm_coe_le_norm n).trans ((solution_norm_bound _ h s).trans hs)

end StandardMapEntropy.NonlinearStable

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Stable_PerronStability
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

noncomputable def flatRemainderDerivative (k : ℝ) (z : ℂ) (F : RealPlane →L[ℝ] ℂ)
    (C : ℂ →L[ℝ] RealPlane) (v : RealPlane) : RealPlane →L[ℝ] RealPlane :=
  C.comp ((standardDerivative k (complexProjection (z+F v))-standardDerivative k (complexProjection z)).comp F)
@[simp] lemma flatRemainderDerivative_zero (k : ℝ) (z : ℂ) (F : RealPlane →L[ℝ] ℂ)
    (C : ℂ →L[ℝ] RealPlane) : flatRemainderDerivative k z F C 0=0 := by
  simp only [flatRemainderDerivative,map_zero,add_zero,sub_self,ContinuousLinearMap.zero_comp,ContinuousLinearMap.comp_zero]

end StandardMapEntropy

end
section
namespace StandardMapEntropy.NonlinearStable
open Filter Set
open scoped Topology NNReal
variable {ℓ δ : ℝ≥0}

noncomputable def graphLinearization (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (D : ℕ → Plane → Plane →L[ℝ] Plane)
    (hD : ∀ n v, ‖v‖≤1 → ‖D n v‖≤δ) (s : ℝ) (hs : |s|≤1) : Sequence :=
  (r.linearized (fun n => D n (r.extend.solution h s n))
    (fun n => hD n _ (local_solution_bound r h hs n))).solution h 1

end StandardMapEntropy.NonlinearStable

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Entropy_FineCharts
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

noncomputable def fineSize (k χ ε δ : ℝ) (z : Torus) : ℝ := fineScale k ε δ*chartRadius k χ ε z
noncomputable def fineFrame (k χ ε δ : ℝ) (z : Torus) : RealPlane →L[ℝ] ℂ :=
  flatFrame (fineSize k χ ε δ z) (lyapunovFrame k χ z)
noncomputable def fineInverse (k χ ε δ : ℝ) (z : Torus) : ℂ →L[ℝ] RealPlane :=
  flatInverse (fineSize k χ ε δ z) (lyapunovCoframe k χ z)
noncomputable def fineStableMultiplier (k χ ε δ : ℝ) (z : Torus) : ℝ :=
  fineSize k χ ε δ z/fineSize k χ ε δ (standardMap k z)*stableMultiplier k χ z
noncomputable def fineUnstableMultiplier (k χ ε δ : ℝ) (z : Torus) : ℝ :=
  fineSize k χ ε δ z/fineSize k χ ε δ (standardMap k z)*unstableMultiplier k χ z
lemma fineSize_pos (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : Torus) : 0<fineSize k χ ε δ z :=
  mul_pos (fineScale_pos k ε hδ) (chartRadius_pos k χ ε z)
lemma fineFrame_norm_le (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : Torus) :
    ‖fineFrame k χ ε δ z‖≤2*fineSize k χ ε δ z :=
  flatFrame_norm_le (fineSize_pos k χ ε hδ z).le (lyapunovFrame_norm_le k χ z)
lemma fineFrame_inverse (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : Torus)
    (hw : wedge (stableVector k z) (unstableVector k z)≠0) (v : ℂ) :
    fineFrame k χ ε δ z (fineInverse k χ ε δ z v)=v :=
  flatFrame_inverse (ne_of_gt (fineSize_pos k χ ε hδ z)) (lyapunovFrame_coframe k χ z hw) v

lemma fineSize_ratio (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z w : Torus) :
    fineSize k χ ε δ z/fineSize k χ ε δ w=chartRadius k χ ε z/chartRadius k χ ε w := by
  unfold fineSize
  rw [mul_div_mul_left _ _ (ne_of_gt (fineScale_pos k ε hδ))]
lemma fineStableMultiplier_bound (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : Torus)
    (hz : FineRegular k χ ε z) : |fineStableMultiplier k χ ε δ z|≤Real.exp (-χ+ε) := by
  have hr := slow_radius_ratio (chartRadius_pos k χ ε z) (chartRadius_pos k χ ε (standardMap k z)) hz.2.2.2.2.2.1
  have he : Real.exp ε*Real.exp (-χ)=Real.exp (-χ+ε) := by rw [←Real.exp_add,add_comm]
  unfold fineStableMultiplier
  rw [abs_mul,abs_of_pos (div_pos (fineSize_pos k χ ε hδ z) (fineSize_pos k χ ε hδ _)),fineSize_ratio k χ ε hδ]
  exact (mul_le_mul hr hz.2.2.1 (abs_nonneg _) (Real.exp_pos _).le).trans_eq he
lemma fineUnstableMultiplier_ne (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : Torus)
    (hz : FineRegular k χ ε z) : fineUnstableMultiplier k χ ε δ z≠0 := by
  have hb : unstableMultiplier k χ z≠0 := abs_pos.mp ((Real.exp_pos χ).trans_le hz.2.2.2.1)
  exact mul_ne_zero (div_ne_zero (ne_of_gt (fineSize_pos k χ ε hδ z)) (ne_of_gt (fineSize_pos k χ ε hδ _))) hb
lemma fineUnstableMultiplier_inverse_bound (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : Torus)
    (hz : FineRegular k χ ε z) : |(fineUnstableMultiplier k χ ε δ z)⁻¹|≤Real.exp (-χ+ε) := by
  have hr := slow_radius_ratio (chartRadius_pos k χ ε (standardMap k z)) (chartRadius_pos k χ ε z) hz.2.2.2.2.2.2
  have hb : |unstableMultiplier k χ z|⁻¹≤Real.exp (-χ) := by
    rw [Real.exp_neg]
    exact inv_anti₀ (Real.exp_pos χ) hz.2.2.2.1
  have he : Real.exp ε*Real.exp (-χ)=Real.exp (-χ+ε) := by rw [←Real.exp_add,add_comm]
  unfold fineUnstableMultiplier
  rw [abs_inv,abs_mul,abs_of_pos (div_pos (fineSize_pos k χ ε hδ z) (fineSize_pos k χ ε hδ _)),
    mul_inv,inv_div,fineSize_ratio k χ ε hδ]
  exact (mul_le_mul hr hb (inv_nonneg.mpr (abs_nonneg _)) (Real.exp_pos _).le).trans_eq he

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal
noncomputable def codingScale (k ε δ : ℝ) : ℝ := min 1 (fineScale k ε δ)/(100*(1+|9*growthBase k|))
noncomputable def codingRadius (k χ ε δ : ℝ) (z : Torus) : ℝ :=
  codingScale k ε δ*(chartRadius k χ ε z)^2

end StandardMapEntropy

end
section
namespace StandardMapEntropy.NonlinearStable
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {ℓ δ : ℝ≥0}

noncomputable def Recurrence.orbit (r : Recurrence ℓ δ) (v : Plane) : ℕ → Plane
  | 0 => v
  | n+1 => r.step n (r.orbit v n)

def Recurrence.trappedBox (r : Recurrence ℓ δ) (n : ℕ) : Set Plane :=
  {v | ∀ j : ℕ, j≤n → ‖r.orbit v j‖≤1}

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

lemma fine_nonlinearity_coefficient (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : Torus)
    (hz : FineRegular k χ ε z) (hn : FineRegular k χ ε (standardMap k z)) :
    ‖fineInverse k χ ε δ (standardMap k z)‖*derivativeVariationBound k*‖fineFrame k χ ε δ z‖^2≤δ := by
  let a := chartRadius k χ ε z
  let b := chartRadius k χ ε (standardMap k z)
  let c := ‖lyapunovCoframe k χ (standardMap k z)‖
  let η := fineScale k ε δ
  have ha : 0<a := chartRadius_pos k χ ε z
  have hb : 0<b := chartRadius_pos k χ ε (standardMap k z)
  have hη : 0<η := fineScale_pos k ε hδ
  have hc : 0 ≤ c := norm_nonneg _
  have hbc : b*c≤1 := hn.2.2.2.2.1
  have hab : a/b≤Real.exp ε := slow_radius_ratio ha hb hz.2.2.2.2.2.1
  have hD := derivativeVariationBound_nonneg k
  have hF : ‖fineFrame k χ ε δ z‖≤2*(η*a) := fineFrame_norm_le k χ ε hδ z
  have hC : ‖fineInverse k χ ε δ (standardMap k z)‖≤(η*b)⁻¹*c :=
    flatInverse_norm_le (fineSize_pos k χ ε hδ _).le _
  have hEF : (Real.exp ε)^2=Real.exp (2*ε) := by rw [pow_two,←Real.exp_add]; congr 1; ring
  have hsqr : (a/b)^2≤Real.exp (2*ε) := by
    rw [←hEF]
    exact pow_le_pow_left₀ (div_nonneg ha.le hb.le) hab 2
  calc
    _ ≤ ((η*b)⁻¹*c)*derivativeVariationBound k*(2*(η*a))^2 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hC hD)
        (pow_le_pow_left₀ (norm_nonneg _) hF 2) (sq_nonneg _)
        (mul_nonneg (mul_nonneg (inv_nonneg.mpr (mul_nonneg hη.le hb.le)) hc) hD)
    _ = (4*derivativeVariationBound k*η)*((b*c)*(a/b)^2) := by
      field_simp [ne_of_gt hη,ne_of_gt hb]; ring
    _ ≤ (4*derivativeVariationBound k*η)*(1*Real.exp (2*ε)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hbc hsqr (sq_nonneg _) (by norm_num)) (by positivity)
    _ = δ*(derivativeVariationBound k/(2*(1+derivativeVariationBound k))) := by
      dsimp [η,fineScale]
      field_simp [ne_of_gt (Real.exp_pos (2*ε)),ne_of_gt (show 0<1+derivativeVariationBound k by linarith)]
      ring
    _ ≤ δ*1 := by
      apply mul_le_mul_of_nonneg_left _ hδ.le
      apply (div_le_iff₀ (show 0<2*(1+derivativeVariationBound k) by linarith)).mpr
      linarith
    _ = _ := mul_one _

noncomputable def fineRemainder (k χ ε δ : ℝ) (z : ℂ) : RealPlane → RealPlane :=
  flatRemainder k z (fineFrame k χ ε δ (complexProjection z))
    (fineInverse k χ ε δ (standardMap k (complexProjection z)))
@[simp] lemma fineRemainder_zero (k χ ε δ : ℝ) (z : ℂ) : fineRemainder k χ ε δ z 0=0 :=
  flatRemainder_zero _ _ _ _
lemma fineRemainder_lipschitz (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : ℂ)
    (hz : FineRegular k χ ε (complexProjection z)) (hn : FineRegular k χ ε (standardMap k (complexProjection z)))
    {v w : RealPlane} (hv : ‖v‖≤1) (hw : ‖w‖≤1) :
    ‖fineRemainder k χ ε δ z v-fineRemainder k χ ε δ z w‖≤δ*‖v-w‖ :=
  (flatRemainder_sub_bound k z _ _ hv hw).trans
    (mul_le_mul_of_nonneg_right (fine_nonlinearity_coefficient k χ ε hδ _ hz hn) (norm_nonneg _))

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

lemma fine_regular_lift_next (k χ ε : ℝ) (w : ℂ)
    (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w))) (n : ℕ) :
    FineRegular k χ ε (standardMap k (complexProjection ((standardLift k)^[n] w))) := by
  simpa only [Function.iterate_succ_apply',complexProjection_standardLift] using hw (n+1)
noncomputable def fineLocalRecurrence (k χ ε δ : ℝ) (hδ : 0<δ) (w : ℂ)
    (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w))) :
    LocalRecurrence (fineLinearRate χ ε) (fineErrorRate δ hδ) where
  a n := fineStableMultiplier k χ ε δ (complexProjection ((standardLift k)^[n] w))
  b n := fineUnstableMultiplier k χ ε δ (complexProjection ((standardLift k)^[n] w))
  remainder n := fineRemainder k χ ε δ ((standardLift k)^[n] w)
  stable_bound n := fineStableMultiplier_bound k χ ε hδ _ (hw n)
  inverse_bound n := fineUnstableMultiplier_inverse_bound k χ ε hδ _ (hw n)
  b_ne n := fineUnstableMultiplier_ne k χ ε hδ _ (hw n)
  local_lipschitz n _ _ hv hu := fineRemainder_lipschitz k χ ε hδ _ (hw n) (fine_regular_lift_next k χ ε w hw n) hv hu
  zero _ := fineRemainder_zero _ _ _ _ _

noncomputable def fineCoordinate (k χ ε δ : ℝ) (w p : ℂ) (n : ℕ) : RealPlane :=
  fineInverse k χ ε δ (complexProjection ((standardLift k)^[n] w))
    ((standardLift k)^[n] p-(standardLift k)^[n] w)

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Entropy_PhysicalVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable def fineVolumeFactor (k χ ε δ : ℝ) (z : Torus) : ℝ :=
  |(fineSize k χ ε δ z • lyapunovFrame k χ z).det|

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Holonomy_DerivativeQuantitative
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open Finset

namespace NonlinearStable
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {ℓ δ : ℝ≥0}

@[simp] lemma Recurrence.step_zero (r : Recurrence ℓ δ) (n : ℕ) : r.step n 0=0 := by
  simp [Recurrence.step,r.zero]
@[simp] lemma Recurrence.orbit_zero (r : Recurrence ℓ δ) (n : ℕ) : r.orbit 0 n=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Recurrence.orbit,ih,r.step_zero]

end NonlinearStable
end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

noncomputable def fineRemainderDerivative (k χ ε δ : ℝ) (z : ℂ) : RealPlane → RealPlane →L[ℝ] RealPlane :=
  flatRemainderDerivative k z (fineFrame k χ ε δ (complexProjection z))
    (fineInverse k χ ε δ (standardMap k (complexProjection z)))
@[simp] lemma fineRemainderDerivative_zero (k χ ε δ : ℝ) (z : ℂ) : fineRemainderDerivative k χ ε δ z 0=0 :=
  flatRemainderDerivative_zero _ _ _ _

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Holonomy_FineStableGeometry
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

noncomputable def fineStableGraph (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w))) : ℝ → ℝ :=
  (fineLocalRecurrence k χ ε δ hδ w hw).extend.graph hq
noncomputable def fineStableCurve (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w))) : ℝ → ℂ :=
  fun s => w+fineFrame k χ ε δ (complexProjection w) (s,fineStableGraph k χ ε δ hδ hq w hw s)

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal

noncomputable def lyapunovChartData (k χ ε : ℝ) (z : Torus) : LyapunovChartData :=
  (lyapunovFrame k χ z,lyapunovCoframe k χ z,chartRadius k χ ε z)
noncomputable def orbitChartData (k χ ε : ℝ) (z : Torus) : ℕ → LyapunovChartData × LyapunovChartData :=
  fun n => (lyapunovChartData k χ ε ((standardMap k)^[n] z),
    lyapunovChartData k χ ε ((inverseMap k)^[n] z))

end StandardMapEntropy

end
section
namespace StandardMapEntropy.NonlinearStable
open Set Filter
open scoped Topology NNReal
variable {ℓ δ : ℝ≥0}

noncomputable def Recurrence.perronApprox (r : Recurrence ℓ δ) (s : ℝ) : ℕ → ℕ → Plane
  | 0, _ => 0
  | N+1, n =>
    ((match n with | 0 => s | m+1 => r.a m*(r.perronApprox s N m).1+(r.remainder m (r.perronApprox s N m)).1),
      (r.b n)⁻¹*((r.perronApprox s N (n+1)).2-(r.remainder n (r.perronApprox s N n)).2))

end StandardMapEntropy.NonlinearStable

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Holonomy_FiniteOrbitDecay
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.NonlinearStable
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {ℓ δ : ℝ≥0}

noncomputable def LocalRecurrence.trueOrbit (r : LocalRecurrence ℓ δ) (v : Plane) : ℕ → Plane
  | 0 => v
  | n+1 => r.step n (r.trueOrbit v n)

end StandardMapEntropy.NonlinearStable

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Holonomy_FinePlaqueParameters
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

noncomputable def finePlaqueInChart (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w v : ℂ) (hv : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] v)))
    (s : ℝ) : Plane :=
  fineInverse k χ ε δ (complexProjection w) (fineStableCurve k χ ε δ hδ hq v hv s-w)

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Components_BoundedBirkhoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology NNReal ENNReal
open NonlinearStable

noncomputable def fineUnstableCurve (k χ ε δ : ℝ) (hδ : 0<δ) (hq : Real.exp (-χ+ε)+δ<1)
    (w : ℂ) (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] (tangentReversal w)))) : ℝ → ℂ :=
  fun s => tangentReversal (fineStableCurve k χ ε δ hδ hq (tangentReversal w) hw s)

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Components_FineChartGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal
open NonlinearStable

structure ReversibleRectangleBlock (k χ : ℝ) where
  ε : ℝ
  δ : ℝ
  ε_pos : 0<ε
  δ_pos : 0<δ
  δ_small : δ≤1/2
  contraction : Real.exp (-χ+ε)+δ<1
  slow : Real.exp (4*ε)*(Real.exp (-χ+ε)+δ)<1
  carrier : Set ℂ
  compact : IsCompact carrier
  positive : 0<volume carrier
  centre : ℂ
  centre_regular : wedge (stableVector k (complexProjection centre)) (unstableVector k (complexProjection centre))≠0
  reverse_regular : wedge (stableVector k (complexProjection (tangentReversal centre)))
    (unstableVector k (complexProjection (tangentReversal centre)))≠0
  α : ℝ
  β : ℝ
  α_ne : α≠0
  β_ne : β≠0
  swap : ∀ p : RealPlane,fineInverse k χ ε δ (complexProjection centre)
    (tangentReversal (fineFrame k χ ε δ (complexProjection (tangentReversal centre)) p))=(β*p.2,α*p.1)
  η : ℝ
  η_pos : 0<η
  η_small : η≤1/16
  slope : Real.exp (-χ+ε)*δ/(1-Real.exp (-χ+ε))≤η
  reverse_slope : (|β|/|α|)*((8/3)*η)≤1/2
  r : ℝ
  r' : ℝ
  R : ℝ
  R' : ℝ
  ρ : ℝ
  r_pos : 0 < r
  r'_pos : 0 < r'
  R_pos : 0<R
  R'_pos : 0<R'
  ρ_pos : 0<ρ
  r_small : r≤1/12
  r'_small : r'≤1/12
  ρ_small : ρ ≤ r/8
  ρ_reverse : ρ≤|α| *r'/8
  size : (4*fineScale k ε δ*r)/(100*R)+r≤1
  reverse_size : (4*fineScale k ε δ*r')/(100*R')+r'≤1
  data : ContinuousOn (fun v => (orbitChartData k χ ε (complexProjection v),
    orbitChartData k χ ε (complexProjection (tangentReversal v)))) carrier
  regular : ∀ v∈carrier,∀ n : ℕ,FineRegular k χ ε (complexProjection ((standardLift k)^[n] v))
  reversed : ∀ v∈carrier,∀ n : ℕ,FineRegular k χ ε (complexProjection ((standardLift k)^[n] (tangentReversal v)))
  radius : ∀ v∈carrier,R ≤ codingRadius k χ ε δ (complexProjection v)
  reverse_radius : ∀ v∈carrier,R' ≤ codingRadius k χ ε δ (complexProjection (tangentReversal v))
  frames : ∀ v∈carrier,
    ‖(fineInverse k χ ε δ (complexProjection centre)).comp (fineFrame k χ ε δ (complexProjection v))-
      ContinuousLinearMap.id ℝ Plane‖≤η
  reverse_frames : ∀ v∈carrier,
    ‖(fineInverse k χ ε δ (complexProjection (tangentReversal centre))).comp
      (fineFrame k χ ε δ (complexProjection (tangentReversal v)))-ContinuousLinearMap.id ℝ Plane‖≤η
  coframes : ∀ v∈carrier,
    ‖(fineInverse k χ ε δ (complexProjection v)).comp (fineFrame k χ ε δ (complexProjection centre))-
      ContinuousLinearMap.id ℝ Plane‖≤1/4
  reverse_coframes : ∀ v∈carrier,
    ‖(fineInverse k χ ε δ (complexProjection (tangentReversal v))).comp
      (fineFrame k χ ε δ (complexProjection (tangentReversal centre)))-ContinuousLinearMap.id ℝ Plane‖≤1/4
  central : ∀ v∈carrier,‖fineInverse k χ ε δ (complexProjection centre) (v-centre)‖≤ρ/100
  reverse_central : ∀ v∈carrier,
    ‖fineInverse k χ ε δ (complexProjection (tangentReversal centre)) (tangentReversal v-tangentReversal centre)‖ ≤ r'/4

end StandardMapEntropy
end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal
open NonlinearStable

namespace ReversibleRectangleBlock
variable {k χ : ℝ} (B : ReversibleRectangleBlock k χ)

noncomputable def chart (p : RealPlane) : ℂ := B.centre+fineFrame k χ B.ε B.δ (complexProjection B.centre) p
noncomputable def coordinates (v : ℂ) : RealPlane := fineInverse k χ B.ε B.δ (complexProjection B.centre) (v-B.centre)
noncomputable def reverseCoordinates (v : ℂ) : RealPlane :=
  fineInverse k χ B.ε B.δ (complexProjection (tangentReversal B.centre)) (tangentReversal v-tangentReversal B.centre)

@[simp] lemma chart_coordinates (v : ℂ) : B.chart (B.coordinates v)=v := by
  rw [chart,coordinates,fineFrame_inverse k χ B.ε B.δ_pos _ B.centre_regular]
  abel

end ReversibleRectangleBlock

structure ReversibleGraphFamilies {k χ : ℝ} (B : ReversibleRectangleBlock k χ) where
  G : B.carrier → ℝ → ℝ
  U : B.carrier → ℝ → ℝ
  stableParameter : B.carrier → ℝ → ℝ
  unstableParameter : B.carrier → ℝ → ℝ
  continuous_G : Continuous (fun p : B.carrier×ℝ => G p.1 p.2)
  continuous_U : Continuous (fun p : B.carrier×ℝ => U p.1 p.2)
  continuous_stableParameter : Continuous (fun p : B.carrier×ℝ => stableParameter p.1 p.2)
  continuous_unstableParameter : Continuous (fun p : B.carrier×ℝ => unstableParameter p.1 p.2)
  slope_G : ∀ a s t,|G a s-G a t|≤(1/2)*|s-t|
  slope_U : ∀ a s t,|U a s-U a t|≤(1/2)*|s-t|
  stable_bound : ∀ a s,|stableParameter a s|≤B.r
  unstable_bound : ∀ a s,|unstableParameter a s|≤B.r'
  stable_representation : ∀ a s,|s|≤B.r/2 → B.chart (s,G a s)=
    fineStableCurve k χ B.ε B.δ B.δ_pos B.contraction a (B.regular a a.property) (stableParameter a s)
  unstable_representation : ∀ a s,|s|≤|B.α| * B.r'/2 → B.chart (U a s,s)=
    fineUnstableCurve k χ B.ε B.δ B.δ_pos B.contraction a (B.reversed a a.property) (unstableParameter a s)
  G_centre : ∀ a,G a (B.coordinates a).1=(B.coordinates a).2
  U_centre : ∀ a,U a (B.coordinates a).2=(B.coordinates a).1

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Components_CurvedHolonomy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal
open NonlinearStable

namespace ReversibleRectangleBlock
variable {k χ : ℝ} (B : ReversibleRectangleBlock k χ)
noncomputable def holonomyConstant : ℝ := 2*Real.exp (8*B.δ/(1-(Real.exp (-χ+B.ε)+B.δ)))
noncomputable def stableInterval : Set ℝ := Icc (-B.r/2) (B.r/2)
noncomputable def unstableInterval : Set ℝ := Icc (-|B.α| * B.r'/2) (|B.α| * B.r'/2)
end ReversibleRectangleBlock

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal
attribute [local instance] Measure.Subtype.measureSpace

namespace ReversibleRectangleBlock
variable {k χ : ℝ} (B : ReversibleRectangleBlock k χ)

noncomputable def coordinateCarrier : Set RealPlane := B.coordinates '' B.carrier
noncomputable def label (p : B.coordinateCarrier) : B.carrier := ⟨B.chart p,by
  obtain ⟨v,hv,he⟩ := p.property
  change B.coordinates v=(p : RealPlane) at he
  rw [←he,B.chart_coordinates]
  exact hv⟩

end ReversibleRectangleBlock
end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Components_SliceRectangleNonsingular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal
open NonlinearStable
attribute [local instance] Measure.Subtype.measureSpace

structure ReversibleGraphRectangle {k χ : ℝ} {B : ReversibleRectangleBlock k χ} (F : ReversibleGraphFamilies B) where
  point : B.coordinateCarrier×B.coordinateCarrier → RealPlane
  continuous : Continuous point
  nonsingular : QuasiMeasurePreserving point ((volume : Measure B.coordinateCarrier).prod volume) volume
  stable : ∀ p,(point p).2=F.G (B.label p.1) (point p).1
  unstable : ∀ p,(point p).1=F.U (B.label p.2) (point p).2
  x_bound : ∀ p,|(point p).1|≤B.ρ
  y_bound : ∀ p,|(point p).2|≤B.ρ

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Components_BirkhoffAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal
open NonlinearStable BoundedSubadditive
attribute [local instance] Measure.Subtype.measureSpace

namespace ReversibleGraphRectangle
variable {k χ : ℝ} {B : ReversibleRectangleBlock k χ} {F : ReversibleGraphFamilies B} (R : ReversibleGraphRectangle F)
noncomputable def torusPoint (p : B.coordinateCarrier×B.coordinateCarrier) : Torus := complexProjection (B.chart (R.point p))
end ReversibleGraphRectangle

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Bernoulli_ErgodicAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal
open BoundedSubadditive HyperbolicCoding
attribute [local instance] Measure.Subtype.measureSpace

namespace ReversibleRectangleBlock
variable {k χ : ℝ} (B : ReversibleRectangleBlock k χ)

noncomputable def carrierProbability : Measure B.coordinateCarrier :=
  ((volume : Measure B.coordinateCarrier) univ)⁻¹ • volume

end ReversibleRectangleBlock

end StandardMapEntropy

end
end

end OAI
end


