-- Prove2me | Definitions.Def_OAIQ44C000
-- name    : OAIQ44C000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T12:03:00.72369+00:00
-- url     : https://prove2.me/theorems/8b395a5b-66a9-4eab-91ae-38701e3052a0
-- title:
--   Definitions bundle OAIQ44C000 of the split of OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.StandardMapEntropy.main_components`, carved from OpenAI's openai/math development (OpenAI, *Positive Metric Entropy for the Standard Map at Large Parameters*, OpenAI Math Release, September 23, 2026, result family 146, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 562 declarations of OpenAI's Lean: 302 definitions, 17 inductive types or structures, 11 instances and 232 theorems. The definitions and types are `OAI.AEPeriod.Class`, `OAI.AEPeriod.act`, `OAI.AEPeriod.ofSet`, `OAI.AEPeriod.setoid`, `OAI.BoundedSubadditive.Cocycle`, `OAI.BoundedSubadditive.Cocycle.average`, `OAI.BoundedSubadditive.Cocycle.badObservation`, `OAI.BoundedSubadditive.Cocycle.badSet`, `OAI.BoundedSubadditive.Cocycle.lowerRate`, `OAI.BoundedSubadditive.Cocycle.upperRate`, `OAI.BoundedSubadditive.ContinuousBirkhoffCode`, `OAI.BoundedSubadditive.CyclicAtom`, `OAI.BoundedSubadditive.PowerAtomFamily`, `OAI.BoundedSubadditive.PowerAtomFamily.cycle`, `OAI.BoundedSubadditive.excess`, `OAI.BoundedSubadditive.observationCocycle`, `OAI.HyperbolicCoding.ExponentiallyAsymptotic`, `OAI.HyperbolicCoding.FiniteRateSupremum`, `OAI.HyperbolicCoding.GeneratingIIDStage`, `OAI.HyperbolicCoding.GoodIIDStage`, `OAI.HyperbolicCoding.GoodNames`, `OAI.HyperbolicCoding.IIDCopyTest`, `OAI.HyperbolicCoding.IsTailAtom`, `OAI.HyperbolicCoding.LawClose`, `OAI.HyperbolicCoding.Marker.HeadMarker`, `OAI.HyperbolicCoding.Marker.MarkedBlock`, `OAI.HyperbolicCoding.Marker.candidates`, `OAI.HyperbolicCoding.Marker.centeredWindow`, `OAI.HyperbolicCoding.Marker.column`, `OAI.HyperbolicCoding.Marker.decodeWindow`, `OAI.HyperbolicCoding.Marker.markWord`, `OAI.HyperbolicCoding.Marker.phase`, `OAI.HyperbolicCoding.Marker.reserved`, `OAI.HyperbolicCoding.MatrixCoupling`, `OAI.HyperbolicCoding.MatrixCoupling.assignment`, `OAI.HyperbolicCoding.MatrixCoupling.comp`, `OAI.HyperbolicCoding.MatrixCoupling.conditionalAssignment`, `OAI.HyperbolicCoding.MatrixCoupling.cost`, `OAI.HyperbolicCoding.MatrixCoupling.decodingThreshold`, `OAI.HyperbolicCoding.MatrixCoupling.diagonal` and 279 more.
--
--   **Sources.** They come from these modules of lean/OAI/Dynamics/StandardMap, in whole or in part: `StandardMap_ArrayActions`, `StandardMap_ArrayAffinity`, `StandardMap_ArrayHalf`, `StandardMap_ArrayTests`, `StandardMap_Bernoulli_ErgodicAverages`, `StandardMap_Bernoulli_ErgodicL1`, `StandardMap_Bernoulli_IntegerDynamics`, `StandardMap_Bernoulli_ReverseFano`, `StandardMap_Bernoulli_ReverseTailProjection`, `StandardMap_Bernoulli_RohlinSinaiFinite`, `StandardMap_Bernoulli_TailNameSaturation`, `StandardMap_BiCocycle`, `StandardMap_BridgeExclusions`, `StandardMap_BridgeGrid`, `StandardMap_BridgeSamples`, `StandardMap_BridgeScalars`, `StandardMap_CancellationTheorem`, `StandardMap_ClippedTests`, `StandardMap_CocycleAlgebra`, `StandardMap_Coding_CenteredDecoder`, `StandardMap_Coding_DecodedTowerCopy`, `StandardMap_Coding_EntropyRateCodebook`, `StandardMap_Coding_FixedWindowCost`, `StandardMap_Coding_FullEntropyCopySequence`, `StandardMap_Coding_PositiveWeakBernoulliRate`, `StandardMap_Coding_ReconstructionEntropy`, `StandardMap_Coding_SanitizedTowerLaw`, `StandardMap_Coding_TypicalDecodableCoupling`, `StandardMap_Coding_TypicalWordCodebook`, `StandardMap_Components_BirkhoffAtoms`, `StandardMap_Components_CurvedHolonomy`, `StandardMap_Components_PowerAtomCycles`, `StandardMap_Components_SliceRectangleNonsingular`, `StandardMap_Coupling_ActualFiniteRecodingBounds`, `StandardMap_Coupling_AtomlessFinitePartition`, `StandardMap_Coupling_ChunkNameCost`, `StandardMap_Coupling_CoarseConditionalBudget`, `StandardMap_Coupling_ConditionalRefinementInformation`, `StandardMap_Coupling_FiniteConditionalLawTests`, `StandardMap_Coupling_FiniteMaximalCoupling`, `StandardMap_Coupling_FiniteProductVariance`, `StandardMap_Coupling_FiniteVectorEntropy`, `StandardMap_Coupling_IidFiniteWindowApprox`, `StandardMap_Coupling_SequentialChunkCoupling`, `StandardMap_CriticalLaws`, `StandardMap_CriticalLimits`, `StandardMap_CriticalSequence`, `StandardMap_DyadicArrays`, `StandardMap_EndpointObservations`, `StandardMap_Entropy_FineCharts`, `StandardMap_Entropy_FiniteBinCoding`, `StandardMap_Entropy_LiftGrid`, `StandardMap_Entropy_ObservableEntropy`, `StandardMap_Entropy_PhysicalVolume`, `StandardMap_Entropy_SupportEntropy`, `StandardMap_GridPartition`, `StandardMap_Holonomy_FineStableGeometry`, `StandardMap_LiftDynamics`, `StandardMap_LimitActions`, `StandardMap_LimitBalance`, `StandardMap_LocalMidpointGrid`, `StandardMap_LocalScarcity`, `StandardMap_Lyapunov_BoundedTempering`, `StandardMap_Lyapunov_Definitions`, `StandardMap_Lyapunov_DerivativeGrowth`, `StandardMap_Lyapunov_InverseLyapunov`, `StandardMap_Lyapunov_MeasurableFrame`, `StandardMap_Lyapunov_Subadditive`, `StandardMap_Lyapunov_TransverseLines`, `StandardMap_MeanCancellation`, `StandardMap_MeanDeficit`, `StandardMap_MiddleCount`, `StandardMap_NonaffineLimits`, `StandardMap_PlaneGeometry`, `StandardMap_PlaneTransfer`, `StandardMap_ProductDistances`, `StandardMap_RealArrays`, `StandardMap_RemainderLaws`, `StandardMap_RescaledArrays`, `StandardMap_SampleLaws`, `StandardMap_ScaleLaws`, `StandardMap_SegmentObservations`, `StandardMap_ShapeComponents`, `StandardMap_StablePrefix`, `StandardMap_Stable_LocalStable`, `StandardMap_Stable_PerronStability`, `StandardMap_Stable_SmoothRemainder`, `StandardMap_TestObservations`, `StandardMap_TorusDynamics`, `StandardMap_TorusIntegral`, `StandardMap_TorusObservations`, `StandardMap_Towers_FiniteCouplingRealization`, `StandardMap_Towers_PhaseAveraging`, `StandardMap_Towers_ScaledFiniteCoupling`, `StandardMap_TransferCore`, `StandardMap_TreeLine`, `StandardMap_TreeLocalAffine`, `StandardMap_WeightedCompact`.
--
--   **Imports.** It imports the published bundle `Def_StandardMapComponents`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ44C002`; the statements `OAI.HyperbolicCoding.actual_fixed_window_rate_copy_q44`, `OAI.HyperbolicCoding.block_recoding_small_cost_q44`, `OAI.HyperbolicCoding.fixed_decoder_arbitrary_tests_q44`, `OAI_HyperbolicCoding_fixed_window_fd_graph_q44`, `OAI_HyperbolicCoding_generating_iid_partition_q44`, `OAI.HyperbolicCoding.goodIIDStage_initial_q44`, `OAI.HyperbolicCoding.goodIIDStage_next_q44`, `OAI.StandardMapEntropy.BridgeGrid.scale_bound_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.dilation_balance_q44`, `OAI_StandardMapEntropy_CriticalScaleSequence_dyadicBridge_aeselected_q44`, `OAI.StandardMapEntropy.CriticalScaleSequence.exists_limitLaws_q44`, `OAI_StandardMapEntropy_CriticalScaleSequence_remainder_cap_band_q44`, `OAI_StandardMapEntropy_CriticalScaleSequence_remainder_dilate_q44`, `OAI_StandardMapEntropy_actual_backward_slice_q44`, `OAI_StandardMapEntropy_actual_fast_bridge_real_q44`, `OAI.StandardMapEntropy.actual_return_bernoulli_q44`, `OAI.StandardMapEntropy.actual_return_full_entropy_iid_factor_q44`, `OAI_StandardMapEntropy_eventually_actual_cyclic_weakBernoulli_component_q44`, `OAI.StandardMapEntropy.eventually_meanDeficit_doubling_q44`, `OAI_StandardMapEntropy_eventually_meanDeficit_small_q44`, `OAI.StandardMapEntropy.eventually_small_endpoints_slice_q44`, `OAI_StandardMapEntropy_exists_critical_scale_sequence_q44` and `OAI.StandardMapEntropy.no_critical_scale_sequence_q44`; the proofs of `OAI.HyperbolicCoding.actual_fixed_window_rate_copy_q44`, `OAI.HyperbolicCoding.block_recoding_small_cost_q44`, `OAI.HyperbolicCoding.fixed_decoder_arbitrary_tests_q44`, `OAI_HyperbolicCoding_fixed_window_fd_graph_q44`, `OAI_HyperbolicCoding_generating_iid_partition_q44`, `OAI.HyperbolicCoding.goodIIDStage_initial_q44`, `OAI.HyperbolicCoding.goodIIDStage_next_q44`, `OAI_StandardMapEntropy_CriticalScaleSequence_dyadicBridge_aeselected_q44`, `OAI_StandardMapEntropy_CriticalScaleSequence_remainder_cap_band_q44`, `OAI_StandardMapEntropy_CriticalScaleSequence_remainder_dilate_q44`, `OAI_StandardMapEntropy_actual_backward_slice_q44`, `OAI_StandardMapEntropy_actual_fast_bridge_real_q44`, `OAI_StandardMapEntropy_eventually_actual_cyclic_weakBernoulli_component_q44`, `OAI_StandardMapEntropy_eventually_meanDeficit_small_q44` and `OAI_StandardMapEntropy_exists_critical_scale_sequence_q44`.
-- source:
--   OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 146; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Dynamics/StandardMap at commit adc7f12

import Mathlib
import Definitions.Def_StandardMapComponents

section
-- module Solutions.OAIQ44_CM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_LocalScarcity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StandardMapEntropy

def FinitePartition (r : ℕ) := { p : Torus → Fin (r + 1) // Measurable p }

@[simp] lemma sine_coe (x : ℝ) : sine (x : Circle) = Real.sin (2 * Real.pi * x) :=
  sine_periodic.lift_coe x

lemma continuous_sine : Continuous sine := by
  apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))).continuous_iff.mpr
  change Continuous (fun x : ℝ => sine (x : Circle))
  simpa only [sine_coe, Function.comp_def, Pi.mul_apply, id_eq] using
    Real.continuous_sin.comp (continuous_const.mul continuous_id)

noncomputable def kick (k : ℝ) (x : Circle) : Circle := (k * sine x : ℝ)

lemma continuous_kick (k : ℝ) : Continuous (kick k) :=
  (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_const.mul continuous_sine)

lemma continuous_standardMap (k : ℝ) : Continuous (standardMap k) := by
  exact ((continuous_fst.add continuous_snd).add
    ((continuous_kick k).comp continuous_fst)).prodMk
      (continuous_snd.add ((continuous_kick k).comp continuous_fst))

noncomputable def inverseMap (k : ℝ) (z : Torus) : Torus :=
  (z.1 - z.2, z.2 - kick k (z.1 - z.2))

lemma standardMap_inverseMap (k : ℝ) (z : Torus) :
    standardMap k (inverseMap k z) = z := by
  apply Prod.ext <;> simp only [standardMap, inverseMap, kick]
  · abel
  · abel

lemma inverseMap_standardMap (k : ℝ) (z : Torus) :
    inverseMap k (standardMap k z) = z := by
  have hx : (standardMap k z).1 - (standardMap k z).2 = z.1 := by
    simp only [standardMap]
    abel
  apply Prod.ext
  · exact hx
  · change (standardMap k z).2 - kick k
      ((standardMap k z).1 - (standardMap k z).2) = z.2
    rw [hx]
    simp [standardMap, kick]

def recurrenceCoordinates (z : Torus) : Torus := (z.1, z.1 - z.2)

noncomputable def recurrenceMap (k : ℝ) (z : Torus) : Torus :=
  (2 • z.1 + kick k z.1 - z.2, z.1)

noncomputable def phi (k x : ℝ) : ℝ := 2 * x + k * Real.sin (2 * Real.pi * x)

noncomputable def potential (k x : ℝ) : ℝ := 2 + (2 * Real.pi * k) * Real.cos (2 * Real.pi * x)

noncomputable def linearSolution (v : ℕ → ℝ) (a b : ℝ) : ℕ → ℝ
  | 0 => a
  | 1 => b
  | n + 2 => v (n + 1) * linearSolution v a b (n + 1) - linearSolution v a b n

@[simp] lemma linearSolution_zero (v : ℕ → ℝ) (a b : ℝ) :
    linearSolution v a b 0 = a := rfl

@[simp] lemma linearSolution_one (v : ℕ → ℝ) (a b : ℝ) :
    linearSolution v a b 1 = b := rfl

noncomputable def tSolution (v : ℕ → ℝ) : ℕ → ℝ := linearSolution v 0 1

noncomputable def liftedOrbit (k q₀ q₁ : ℝ) : ℕ → ℝ
  | 0 => q₀
  | 1 => q₁
  | n + 2 => phi k (liftedOrbit k q₀ q₁ (n + 1)) - liftedOrbit k q₀ q₁ n

@[simp] lemma liftedOrbit_zero (k q₀ q₁ : ℝ) : liftedOrbit k q₀ q₁ 0 = q₀ := rfl
@[simp] lemma liftedOrbit_one (k q₀ q₁ : ℝ) : liftedOrbit k q₀ q₁ 1 = q₁ := rfl

noncomputable def orbitCoefficient (k q₀ q₁ : ℝ) (n : ℕ) : ℝ :=
  potential k (liftedOrbit k q₀ q₁ n)

noncomputable def goodExponent : ℝ := 99 / 100
noncomputable def growthBase (k : ℝ) : ℝ := 2 * Real.pi * k + 4
noncomputable def pairMagnitude (u : ℕ → ℝ) (j : ℕ) : ℝ :=
  max |u j| |u (j - 1)|
noncomputable def pairLog (M : ℝ) (u : ℕ → ℝ) (j : ℕ) : ℝ :=
  Real.logb M (pairMagnitude u j)

def GoodIndex (M : ℝ) (v : ℕ → ℝ) (b : ℝ) (j : ℕ) : Prop :=
  2 ≤ j ∧
  (∀ l : ℕ, 1 ≤ l → l < j →
    goodExponent * ((j : ℝ) - (l : ℝ)) ≤
      pairLog M (tSolution v) j - pairLog M (tSolution v) l) ∧
  goodExponent ≤ pairLog M (tSolution v) (j + 1) - pairLog M (tSolution v) j ∧
  goodExponent ≤ pairLog M (linearSolution v 1 b) j -
      pairLog M (linearSolution v 1 b) (j + 1) ∧
  goodExponent ≤ pairLog M (linearSolution v 1 b) (j + 1) -
      pairLog M (linearSolution v 1 b) (j + 2)

def CommonGood (k q₀ θ : ℝ) (jMinus jPlus : ℕ) : Prop :=
  ∃ b : ℝ,
    GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b jMinus ∧
    GoodIndex (growthBase k) (orbitCoefficient k q₀ (phi k q₀ - θ))
      (potential k q₀ - b) jPlus

noncomputable def matchedScale (k q₀ θ : ℝ) (jMinus jPlus : ℕ) : ℝ :=
  max |tSolution (orbitCoefficient k q₀ θ) jMinus|
    |tSolution (orbitCoefficient k q₀ (phi k q₀ - θ)) jPlus|

def MatchedLogs (k q₀ θ : ℝ) (jMinus jPlus : ℕ) : Prop :=
  |pairLog (growthBase k) (tSolution (orbitCoefficient k q₀ θ)) jMinus -
    pairLog (growthBase k) (tSolution (orbitCoefficient k q₀ (phi k q₀ - θ))) jPlus| ≤ 3 / 5

def localSuccessfulSet (k q₀ θ : ℝ) (jMinus jPlus : ℕ) : Set ℝ :=
  {h | h ∈ Icc (-1) 1 ∧
    CommonGood k q₀ (θ + h / matchedScale k q₀ θ jMinus jPlus) jMinus jPlus}

def LocalScarcityObligation : Prop :=
  ∀ η : ℝ, 0 < η → ∃ η' : ℝ, 0 < η' ∧ ∃ Mη : ℝ,
    ∀ k : ℝ, 0 < k → Mη ≤ growthBase k → ∀ q₀ θ : ℝ, ∀ jMinus jPlus : ℕ,
      CommonGood k q₀ θ jMinus jPlus → MatchedLogs k q₀ θ jMinus jPlus →
      volume {x : ℝ | ∃ y ∈ localSuccessfulSet k q₀ θ jMinus jPlus, dist x y < η'} ≤
        ENNReal.ofReal η

lemma growthBase_ge_four (k : ℝ) (hk : 0 ≤ k) : 4 ≤ growthBase k := by
  have h : 0 ≤ 2 * Real.pi * k := mul_nonneg (by positivity) hk
  unfold growthBase
  linarith

lemma potential_bound (k x : ℝ) (hk : 0 ≤ k) : |potential k x| + 1 ≤ growthBase k := by
  have hK : 0 ≤ 2 * Real.pi * k := by positivity
  have hc := Real.abs_cos_le_one (2 * Real.pi * x)
  calc
    |potential k x| + 1 ≤ (2 + (2 * Real.pi * k) * |Real.cos (2 * Real.pi * x)|) + 1 := by
      unfold potential
      have h := abs_add_le (2 : ℝ) (2 * Real.pi * k * Real.cos (2 * Real.pi * x))
      simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_pos Real.pi_pos, abs_of_nonneg hk] at h
      linarith only [h]
    _ ≤ growthBase k := by
      have h := mul_le_mul_of_nonneg_left hc hK
      unfold growthBase
      linarith

noncomputable def rescaledOrbit (k q₀ θ L ξ : ℝ) (n : ℕ) : ℝ :=
  liftedOrbit k q₀ (θ + ξ / L) n

noncomputable def rescaledD₁ (k q₀ θ L ξ : ℝ) (n : ℕ) : ℝ :=
  tSolution (orbitCoefficient k q₀ (θ + ξ / L)) n / L

noncomputable def derivativeMajorant : ℝ := (1 + 2 * Real.pi) ^ (4 : ℕ)

def HigherControl (k : ℝ) : Prop :=
  growthBase k * (1 + 8 * Real.pi) * (growthBase k ^ (-goodExponent)) ^ (2 : ℕ) ≤ 1 / 2 ∧
  512 * (derivativeMajorant * growthBase k) * (growthBase k ^ (-goodExponent)) ^ (2 : ℕ) ≤ 1

open scoped Matrix.Norms.Operator

noncomputable def terminalQuotient (k q₀ θ L ξ : ℝ) (j : ℕ) : ℝ :=
  tSolution (orbitCoefficient k q₀ (θ + ξ / L)) (j - 1) /
    tSolution (orbitCoefficient k q₀ (θ + ξ / L)) j

open Filter
open scoped Topology

open Metric

noncomputable def localReciprocalTerm (k q₀ θ L h : ℝ) (j : ℕ) : ℝ :=
  1 / ((rescaledD₁ k q₀ θ L h j) ^ 2 *
    (Real.cos (2 * Real.pi * liftedOrbit k q₀ (θ + h / L) j) +
      (2 - terminalQuotient k q₀ θ L h j) / (2 * Real.pi * k)))

section

noncomputable def normalizedSlope (k q₀ θ L : ℝ) (j : ℕ) (h : ℝ) : ℝ :=
  deriv (fun x => rescaledOrbit k q₀ θ L x j) h / (|tSolution (orbitCoefficient k q₀ θ) j| / L)

noncomputable def shiftedCosine (k q₀ θ L : ℝ) (j : ℕ) (h : ℝ) : ℝ :=
  (potential k (rescaledOrbit k q₀ θ L h j) - terminalQuotient k q₀ θ L h j) / (2 * Real.pi * k)

end

end StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace StandardMapEntropy

noncomputable def centerPhase (Q : ℝ → ℝ) (x : ℝ) : ℝ := Q x - ⌊Q 0⌋

structure RescaledPath where
  k : ℝ
  q₀ : ℝ
  θ : ℝ
  L : ℝ
  sign : ℝ
  j : ℕ

namespace RescaledPath
noncomputable def size (P : RescaledPath) : ℝ := |tSolution (orbitCoefficient P.k P.q₀ P.θ) P.j|

def Admissible (P : RescaledPath) : Prop :=
  1 ≤ P.k ∧ HigherControl P.k ∧ |P.sign| = 1 ∧ P.size ≤ P.L ∧
    ∃ b, GoodIndex (growthBase P.k) (orbitCoefficient P.k P.q₀ P.θ) b P.j

end RescaledPath
structure LocalConfiguration where
  k : ℝ
  q₀ : ℝ
  θ : ℝ
  jm : ℕ
  jp : ℕ
namespace LocalConfiguration
noncomputable def scale (C : LocalConfiguration) : ℝ := matchedScale C.k C.q₀ C.θ C.jm C.jp
noncomputable def left (C : LocalConfiguration) : RescaledPath := ⟨C.k, C.q₀, C.θ, C.scale, 1, C.jm⟩
noncomputable def right (C : LocalConfiguration) : RescaledPath := ⟨C.k, C.q₀, phi C.k C.q₀ - C.θ, C.scale, -1, C.jp⟩
noncomputable def fast (C : LocalConfiguration) : RescaledPath :=
  if C.right.size ≤ C.left.size then C.left else C.right
noncomputable def slow (C : LocalConfiguration) : RescaledPath :=
  if C.right.size ≤ C.left.size then C.right else C.left
def successful (C : LocalConfiguration) : Set ℝ := localSuccessfulSet C.k C.q₀ C.θ C.jm C.jp
noncomputable def reciprocalSum (C : LocalConfiguration) (x : ℝ) : ℝ :=
  localReciprocalTerm C.k C.q₀ C.θ C.scale x C.jm +
    localReciprocalTerm C.k C.q₀ (phi C.k C.q₀ - C.θ) C.scale (-x) C.jp
def Valid (C : LocalConfiguration) : Prop :=
  1 ≤ C.k ∧ HigherControl C.k ∧ growthBase C.k ^ (-(47/100 : ℝ)) ≤ 1/2 ∧
    CommonGood C.k C.q₀ C.θ C.jm C.jp ∧ MatchedLogs C.k C.q₀ C.θ C.jm C.jp
end LocalConfiguration
end StandardMapEntropy
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_PlaneGeometry
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
noncomputable def dot (z w : ℂ) : ℝ := z.re * w.re + z.im * w.im
noncomputable def quarterTurn (z : ℂ) : ℂ := Complex.I * z
lemma norm_quarterTurn (z : ℂ) : ‖quarterTurn z‖ = ‖z‖ := by simp [quarterTurn]
lemma wedge_quarterTurn (z : ℂ) : wedge z (quarterTurn z) = ‖z‖^2 := by
  simp [wedge, quarterTurn, Complex.sq_norm, Complex.normSq_apply]
lemma dot_quarterTurn (z : ℂ) : dot z (quarterTurn z) = 0 := by
  simp [dot, quarterTurn]
  ring
lemma dot_wedge_sq (z w : ℂ) : dot z w ^ 2 + wedge z w ^ 2 = ‖z‖^2 * ‖w‖^2 := by
  simp only [dot, wedge, Complex.sq_norm, Complex.normSq_apply]
  ring
lemma norm_add_smul_sq (z w : ℂ) (t : ℝ) :
    ‖z+t • w‖^2 = ‖z‖^2 + 2*t*dot z w+t^2*‖w‖^2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.smul_re, Complex.smul_im, smul_eq_mul, dot]
  ring
lemma unit_expansion (a z : ℂ) (ha : ‖a‖=1) :
    z = dot a z • a + wedge a z • quarterTurn a := by
  have hsq : a.re*a.re+a.im*a.im=1 := by
    calc
      _ = ‖a‖^2 := Complex.normSq_eq_norm_sq a
      _ = 1 := by rw [ha]; norm_num
  apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im, Complex.smul_re,
    Complex.smul_im, smul_eq_mul, dot, wedge, quarterTurn, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im] <;> nlinarith [congrArg (fun x : ℝ => x*z.re) hsq, congrArg (fun x : ℝ => x*z.im) hsq]
lemma exists_unit_opNorm (A : ℂ →L[ℝ] ℂ) : ∃ a : ℂ, ‖a‖=1 ∧ ‖A a‖=‖A‖ := by
  obtain ⟨a,ha,hmax⟩ := (isCompact_sphere (0 : ℂ) 1).exists_isMaxOn
    (show (sphere (0 : ℂ) 1).Nonempty by exact ⟨1,by simp⟩) A.continuous.norm.continuousOn
  have ha : ‖a‖=1 := by simpa [mem_sphere,dist_zero_right] using ha
  refine ⟨a,ha,le_antisymm (by simpa [ha] using A.le_opNorm a) ?_⟩
  apply A.opNorm_le_bound (norm_nonneg _)
  intro z
  by_cases hz : z=0
  · simp [hz]
  have hn : 0<‖z‖ := norm_pos_iff.mpr hz
  have hm := hmax (show (‖z‖⁻¹ : ℝ) • z ∈ sphere (0 : ℂ) 1 by
    simp [ne_of_gt hn])
  change ‖A ((‖z‖⁻¹ : ℝ) • z)‖ ≤ ‖A a‖ at hm
  rw [map_smul,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hn] at hm
  exact (div_le_iff₀ hn).mp (by simpa [div_eq_mul_inv,mul_comm] using hm)
lemma linear_term_of_quadratic_nonpos (d c : ℝ) (h : ∀ t : ℝ, 2*d*t-c*t^2≤0) : d=0 := by
  have hm : IsLocalMax (fun t : ℝ => 2*d*t-c*t^2) 0 := by
    exact Eventually.of_forall (fun t => by simpa using h t)
  have hd : HasDerivAt (fun t : ℝ => 2*d*t-c*t^2) (2*d) 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).const_mul (2*d)).sub
      (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul c) using 1 ; norm_num
  linarith [hm.hasDerivAt_eq_zero hd]
lemma orthogonal_image_of_max (A : ℂ →L[ℝ] ℂ) (a : ℂ) (ha : ‖a‖=1) (hA : ‖A a‖=‖A‖) :
    dot (A a) (A (quarterTurn a))=0 := by
  apply linear_term_of_quadratic_nonpos _ (‖A‖^2-‖A (quarterTurn a)‖^2)
  intro t
  have h0 := A.le_opNorm (a+t • quarterTurn a)
  have hs : ‖A (a+t • quarterTurn a)‖^2 ≤ ‖A‖^2*‖a+t • quarterTurn a‖^2 := by
    nlinarith [norm_nonneg (A (a+t • quarterTurn a)), norm_nonneg A,
      norm_nonneg (a+t • quarterTurn a)]
  rw [map_add,map_smul,norm_add_smul_sq,norm_add_smul_sq,hA,ha,norm_quarterTurn,ha,dot_quarterTurn] at hs
  nlinarith

def PlaneAreaPreserving (A : ℂ →L[ℝ] ℂ) : Prop := ∀ z w, wedge (A z) (A w)=wedge z w
lemma PlaneAreaPreserving.singular_pair {A : ℂ →L[ℝ] ℂ} (h : PlaneAreaPreserving A) :
    ∃ a : ℂ, ‖a‖=1 ∧ ‖A a‖=‖A‖ ∧ dot (A a) (A (quarterTurn a))=0 ∧
      ‖A (quarterTurn a)‖=‖A‖⁻¹ ∧ 1≤‖A‖ := by
  obtain ⟨a,ha,hA⟩ := exists_unit_opNorm A
  have hd := orthogonal_image_of_max A a ha hA
  have hw : wedge (A a) (A (quarterTurn a))=1 := by rw [h, wedge_quarterTurn, ha]; norm_num
  have hs := dot_wedge_sq (A a) (A (quarterTurn a))
  rw [hd,hw,hA] at hs
  have hp : ‖A‖*‖A (quarterTurn a)‖=1 := by
    have hpos := mul_nonneg (norm_nonneg (A : ℂ →L[ℝ] ℂ)) (norm_nonneg (A (quarterTurn a)))
    have he : (‖A‖*‖A (quarterTurn a)‖)^2=1^2 := by nlinarith
    exact (sq_eq_sq₀ hpos (by norm_num)).mp he
  have hn : 0<‖A‖ := by
    have hh:= norm_nonneg (A : ℂ →L[ℝ] ℂ)
    by_contra hh'; have hz : ‖A‖=0 := le_antisymm (not_lt.mp hh') hh
    simp [hz] at hp
  have hi : ‖A (quarterTurn a)‖=‖A‖⁻¹ := by
    rw [← one_div]
    apply (eq_div_iff (ne_of_gt hn)).mpr
    simpa [mul_comm] using hp
  refine ⟨a,ha,hA,hd,hi,?_⟩
  have hb : ‖A (quarterTurn a)‖≤‖A‖ := by simpa [norm_quarterTurn,ha] using A.le_opNorm (quarterTurn a)
  nlinarith [hp]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_PlaneTransfer
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
lemma norm_smul_add_smul_sq (z w : ℂ) (s t : ℝ) :
    ‖s • z+t • w‖^2 = s^2*‖z‖^2+2*s*t*dot z w+t^2*‖w‖^2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.smul_re, Complex.smul_im, smul_eq_mul, dot]
  ring
lemma PlaneAreaPreserving.norm_map_sq {A : ℂ →L[ℝ] ℂ} (h : PlaneAreaPreserving A)
    (a : ℂ) (ha : ‖a‖=1) (hA : ‖A a‖=‖A‖) (z : ℂ) :
    ‖A z‖^2 = dot a z ^ 2 * ‖A‖^2 + wedge a z ^ 2 * ‖A‖⁻¹^2 := by
  have hd := orthogonal_image_of_max A a ha hA
  have hw : wedge (A a) (A (quarterTurn a))=1 := by rw [h,wedge_quarterTurn,ha]; norm_num
  have hs := dot_wedge_sq (A a) (A (quarterTurn a))
  rw [hd,hw,hA] at hs
  have hprod : ‖A‖*‖A (quarterTurn a)‖=1 := by
    have hp := mul_nonneg (norm_nonneg (A : ℂ →L[ℝ] ℂ)) (norm_nonneg (A (quarterTurn a)))
    exact (sq_eq_sq₀ hp (by norm_num)).mp (by nlinarith [hs])
  have hn : ‖A‖≠0 := by intro hz; simp [hz] at hprod
  have hb : ‖A (quarterTurn a)‖=‖A‖⁻¹ := by
    rw [← one_div]; apply (eq_div_iff hn).mpr; simpa [mul_comm] using hprod
  conv_lhs => rw [unit_expansion a z ha]
  rw [map_add,map_smul,map_smul,norm_smul_add_smul_sq,hA,hd,hb]
  ring
lemma PlaneAreaPreserving.norm_lower {A : ℂ →L[ℝ] ℂ} (h : PlaneAreaPreserving A) (z : ℂ) :
    ‖z‖ ≤ ‖A‖*‖A z‖ := by
  obtain ⟨a,ha,hA,hd,hb,hD⟩ := h.singular_pair
  have hsq := h.norm_map_sq a ha hA z
  have hdw := dot_wedge_sq a z
  rw [ha] at hdw
  have hn : ‖A‖≠0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hD)
  have hid : ‖A‖^2*(‖A‖⁻¹)^2=1 := by field_simp
  have hm : ‖A‖^2*‖A z‖^2=(‖A‖^2)^2*dot a z^2+wedge a z^2 := by
    calc
      _ = ‖A‖^2 * (dot a z^2*‖A‖^2+wedge a z^2*‖A‖⁻¹^2) := by rw [hsq]
      _ = (‖A‖^2)^2*dot a z^2+(‖A‖^2*‖A‖⁻¹^2)*wedge a z^2 := by ring
      _ = _ := by rw [hid]; ring
  have h4 : 1≤(‖A‖^2)^2 := by nlinarith [sq_nonneg (‖A‖^2-1)]
  have hsqle : ‖z‖^2≤(‖A‖*‖A z‖)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h4) (sq_nonneg (dot a z))]
  exact (sq_le_sq₀ (norm_nonneg z) (mul_nonneg (norm_nonneg A) (norm_nonneg _))).mp hsqle
lemma PlaneAreaPreserving.norm_inverse {A B : ℂ →L[ℝ] ℂ}
    (hA : PlaneAreaPreserving A) (hB : PlaneAreaPreserving B)
    (hAB : ∀ z, A (B z)=z) (hBA : ∀ z, B (A z)=z) : ‖A‖=‖B‖ := by
  apply le_antisymm
  · apply A.opNorm_le_bound (norm_nonneg _)
    intro z
    simpa [hBA] using hB.norm_lower (A z)
  · apply B.opNorm_le_bound (norm_nonneg _)
    intro z
    simpa [hAB] using hA.norm_lower (B z)
lemma PlaneAreaPreserving.comp {A B : ℂ →L[ℝ] ℂ}
    (hA : PlaneAreaPreserving A) (hB : PlaneAreaPreserving B) : PlaneAreaPreserving (A.comp B) := by
  intro z w
  exact (hA (B z) (B w)).trans (hB z w)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TransferCore
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

@[simp] lemma transferStep_re (v : ℝ) (z : ℂ) : (transferStep v z).re = v*z.re-z.im := rfl
@[simp] lemma transferStep_im (v : ℝ) (z : ℂ) : (transferStep v z).im = z.re := rfl
noncomputable def transferStepInv (v : ℝ) : ℂ →L[ℝ] ℂ :=
  { toLinearMap :=
      { toFun := fun z => ⟨z.im,v*z.im-z.re⟩
        map_add' := by intro z w; apply Complex.ext <;> simp ; ring
        map_smul' := by intro t z; apply Complex.ext <;> simp ; ring }
    cont := by
      exact Complex.equivRealProdCLM.symm.continuous.comp
        (Complex.continuous_im.prodMk ((continuous_const.mul Complex.continuous_im).sub Complex.continuous_re)) }
@[simp] lemma transferStepInv_re (v : ℝ) (z : ℂ) : (transferStepInv v z).re = z.im := rfl
@[simp] lemma transferStepInv_im (v : ℝ) (z : ℂ) : (transferStepInv v z).im = v*z.im-z.re := rfl
lemma transferStep_area (v : ℝ) : PlaneAreaPreserving (transferStep v) := by
  intro z w; simp [wedge]; ring
lemma transferStepInv_area (v : ℝ) : PlaneAreaPreserving (transferStepInv v) := by
  intro z w; simp [wedge]; ring
@[simp] lemma transferStep_inv (v : ℝ) (z : ℂ) : transferStep v (transferStepInv v z)=z := by
  apply Complex.ext <;> simp
@[simp] lemma transferStepInv_inv (v : ℝ) (z : ℂ) : transferStepInv v (transferStep v z)=z := by
  apply Complex.ext <;> simp
lemma transferStep_norm (v : ℝ) : ‖transferStep v‖ ≤ |v|+1 := by
  apply (transferStep v).opNorm_le_bound (by positivity)
  intro z
  have hdecomp : transferStep v z = (v*z.re : ℝ) + quarterTurn z := by
    apply Complex.ext <;> simp [quarterTurn] ; ring
  rw [hdecomp]
  calc
    _ ≤ ‖((v*z.re : ℝ):ℂ)‖+‖quarterTurn z‖ := norm_add_le _ _
    _ ≤ |v| *‖z‖+‖z‖ := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,norm_quarterTurn]
      simpa only [add_comm] using add_le_add_right (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) (abs_nonneg v)) ‖z‖
    _ = _ := by ring

noncomputable def transferProduct (v : ℕ → ℝ) : ℕ → (ℂ →L[ℝ] ℂ)
  | 0 => ContinuousLinearMap.id ℝ ℂ
  | n+1 => (transferStep (v (n+1))).comp (transferProduct v n)
lemma transferProduct_area (v : ℕ → ℝ) (n : ℕ) : PlaneAreaPreserving (transferProduct v n) := by
  induction n with
  | zero => intro z w; rfl
  | succ n ih => exact (transferStep_area _).comp ih
lemma transferProduct_norm_bounds (v : ℕ → ℝ) (M : ℝ) (n : ℕ) (hM : 0≤M)
    (hv : ∀ i : ℕ, 1 ≤ i → i ≤ n → |v i| + 1 ≤ M) :
    1≤‖transferProduct v n‖ ∧ ‖transferProduct v n‖≤M^n := by
  refine ⟨(transferProduct_area v n).singular_pair.choose_spec.2.2.2.2,?_⟩
  induction n with
  | zero => simp [transferProduct]
  | succ n ih =>
    calc
      _ ≤ ‖transferStep (v (n+1))‖*‖transferProduct v n‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ M*M^n := mul_le_mul ((transferStep_norm _).trans (hv _ (by omega) (by omega)))
        (ih fun i hi hin => hv i hi (by omega)) (norm_nonneg _) hM
      _ = _ := by rw [pow_succ]; ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_LiftDynamics
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
noncomputable def liftStep (k : ℝ) : Equiv.Perm (ℝ × ℝ) where
  toFun z := (phi k z.1-z.2,z.1)
  invFun z := (z.2,phi k z.2-z.1)
  left_inv := by intro z; ext <;> simp
  right_inv := by intro z; ext <;> simp
@[simp] lemma liftStep_apply (k : ℝ) (z : ℝ × ℝ) :
    liftStep k z=(phi k z.1-z.2,z.1) := rfl
@[simp] lemma liftStep_symm_apply (k : ℝ) (z : ℝ × ℝ) :
    (liftStep k).symm z=(z.2,phi k z.2-z.1) := rfl
noncomputable def liftIter (k : ℝ) (i : ℤ) : ℝ × ℝ → ℝ × ℝ := ((liftStep k)^i : Equiv.Perm (ℝ × ℝ))
@[simp] lemma liftIter_zero (k : ℝ) (z : ℝ × ℝ) : liftIter k 0 z=z := by simp [liftIter]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_SegmentObservations
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
noncomputable def liftSegmentCoefficient (k : ℝ) (z : ℝ × ℝ) (a : ℤ) (i : ℕ) : ℝ :=
  potential k (liftIter k (a+(i:ℤ)-1) z).1
noncomputable def liftSegmentTransfer (k : ℝ) (z : ℝ × ℝ) (a : ℤ) (n : ℕ) : ℂ →L[ℝ] ℂ :=
  transferProduct (liftSegmentCoefficient k z a) n
noncomputable def liftShortfall (k : ℝ) (z : ℝ × ℝ) (a : ℤ) (n : ℕ) : ℝ :=
  1-Real.log ‖liftSegmentTransfer k z a n‖/((n:ℝ)*Real.log (growthBase k))
lemma liftSegmentCoefficient_bound (k : ℝ) (hk : 0 ≤ k) (z : ℝ × ℝ) (a : ℤ) (i : ℕ) :
    |liftSegmentCoefficient k z a i|+1 ≤ growthBase k := potential_bound k _ hk
lemma liftSegmentTransfer_norm_bounds (k : ℝ) (hk : 0 ≤ k) (z : ℝ × ℝ) (a : ℤ) (n : ℕ) :
    1 ≤ ‖liftSegmentTransfer k z a n‖ ∧ ‖liftSegmentTransfer k z a n‖ ≤ growthBase k^n :=
  transferProduct_norm_bounds _ _ _ (by have := growthBase_ge_four k hk; linarith)
    (fun i _ _ => liftSegmentCoefficient_bound k hk z a i)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_StablePrefix
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
lemma Complex.norm_le_abs_re_add_abs_im (z : ℂ) : ‖z‖ ≤ |z.re|+|z.im| := by
  have he : z = (z.re : ℂ)+z.im*Complex.I := by apply Complex.ext <;> simp
  calc
    ‖z‖ = ‖(z.re : ℂ)+z.im*Complex.I‖ := congrArg norm he
    _ ≤ ‖(z.re : ℂ)‖+‖(z.im : ℂ)*Complex.I‖ := norm_add_le _ _
    _ = _ := by simp
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TorusIntegral
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
noncomputable def liftProjection (z : ℝ × ℝ) : Torus := ((z.1 : Circle),(z.2 : Circle))

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TorusDynamics
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
noncomputable def torusStep (k : ℝ) : Equiv.Perm Torus where
  toFun := recurrenceMap k
  invFun z := (z.2,2 • z.2+kick k z.2-z.1)
  left_inv := by intro z; ext <;> simp [recurrenceMap]
  right_inv := by intro z; ext <;> simp [recurrenceMap]
@[simp] lemma torusStep_apply (k : ℝ) (z : Torus) : torusStep k z=recurrenceMap k z := rfl
@[simp] lemma torusStep_symm_apply (k : ℝ) (z : Torus) :
    (torusStep k).symm z=(z.2,2 • z.2+kick k z.2-z.1) := rfl
noncomputable def torusIter (k : ℝ) (i : ℤ) : Torus → Torus := ((torusStep k)^i : Equiv.Perm Torus)
@[simp] lemma torusIter_zero (k : ℝ) (z : Torus) : torusIter k 0 z=z := by simp [torusIter]
lemma coe_phi (k x : ℝ) : (phi k x : Circle)=2 • (x : Circle)+kick k (x : Circle) := by
  simp only [phi,kick,sine_coe,AddCircle.coe_add]
  rw [two_mul,two_smul,AddCircle.coe_add]
lemma liftProjection_step (k : ℝ) (z : ℝ × ℝ) :
    liftProjection (liftStep k z)=torusStep k (liftProjection z) := by
  apply Prod.ext
  · change ((phi k z.1-z.2 : ℝ) : Circle)=_
    rw [AddCircle.coe_sub,coe_phi]
    rfl
  · rfl
lemma liftProjection_step_symm (k : ℝ) (z : ℝ × ℝ) :
    liftProjection ((liftStep k).symm z)=(torusStep k).symm (liftProjection z) := by
  apply (torusStep k).injective
  rw [Equiv.apply_symm_apply,← liftProjection_step,Equiv.apply_symm_apply]
lemma liftProjection_iter (k : ℝ) (i : ℤ) (z : ℝ × ℝ) :
    liftProjection (liftIter k i z)=torusIter k i (liftProjection z) := by
  have hf : Function.Semiconj liftProjection (liftStep k) (torusStep k) := liftProjection_step k
  have hb : Function.Semiconj liftProjection (liftStep k).symm (torusStep k).symm := liftProjection_step_symm k
  cases i with
  | ofNat n =>
      change liftProjection (liftIter k (n : ℤ) z)=torusIter k (n : ℤ) (liftProjection z)
      simpa only [liftIter,torusIter,zpow_natCast,Equiv.Perm.coe_pow] using hf.iterate_right n z
  | negSucc n => simpa only [liftIter,torusIter,zpow_negSucc,← inv_pow,Equiv.Perm.inv_def,Equiv.Perm.coe_pow] using hb.iterate_right (n+1) z
lemma liftProjection_surjective : Function.Surjective liftProjection := by
  intro z
  obtain ⟨x,hx⟩ := Quotient.mk_surjective z.1
  obtain ⟨y,hy⟩ := Quotient.mk_surjective z.2
  exact ⟨(x,y),Prod.ext hx hy⟩
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_GridPartition
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
noncomputable def circleRep (x : Circle) : ℝ := (AddCircle.equivIco 1 0 x).val
@[simp] lemma coe_circleRep (x : Circle) : (circleRep x : Circle)=x := AddCircle.coe_equivIco
@[simp] lemma circleRep_coe (x : ℝ) : circleRep (x:Circle)=Int.fract x := by
  simpa only [div_one,mul_one,circleRep] using AddCircle.coe_equivIco_mk_apply (1:ℝ) x
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TorusObservations
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
@[simp] lemma cosine_coe (x : ℝ) : cosine (x : Circle)=Real.cos (2*Real.pi*x) :=
  cosine_periodic.lift_coe x
@[simp] lemma torusPotential_coe (k x : ℝ) : torusPotential k (x : Circle)=potential k x := rfl
noncomputable def torusSegmentCoefficient (k : ℝ) (z : Torus) (a : ℤ) (i : ℕ) : ℝ :=
  torusPotential k (torusIter k (a+(i:ℤ)-1) z).1
noncomputable def torusSegmentTransfer (k : ℝ) (z : Torus) (a : ℤ) (n : ℕ) : ℂ →L[ℝ] ℂ :=
  transferProduct (torusSegmentCoefficient k z a) n
noncomputable def torusShortfall (k : ℝ) (z : Torus) (a : ℤ) (n : ℕ) : ℝ :=
  1-Real.log ‖torusSegmentTransfer k z a n‖/((n:ℝ)*Real.log (growthBase k))
@[simp] lemma torusSegmentCoefficient_lift (k : ℝ) (z : ℝ × ℝ) (a : ℤ) (i : ℕ) :
    torusSegmentCoefficient k (liftProjection z) a i=liftSegmentCoefficient k z a i := by
  unfold torusSegmentCoefficient liftSegmentCoefficient
  rw [← liftProjection_iter]
  rfl
@[simp] lemma torusSegmentTransfer_lift (k : ℝ) (z : ℝ × ℝ) (a : ℤ) (n : ℕ) :
    torusSegmentTransfer k (liftProjection z) a n=liftSegmentTransfer k z a n := by
  unfold torusSegmentTransfer liftSegmentTransfer
  congr 1
  funext i
  exact torusSegmentCoefficient_lift k z a i
@[simp] lemma torusShortfall_lift (k : ℝ) (z : ℝ × ℝ) (a : ℤ) (n : ℕ) :
    torusShortfall k (liftProjection z) a n=liftShortfall k z a n := by
  simp only [torusShortfall,liftShortfall,torusSegmentTransfer_lift]
lemma torusSegmentTransfer_norm_bounds (k : ℝ) (hk : 0 ≤ k) (z : Torus) (a : ℤ) (n : ℕ) :
    1 ≤ ‖torusSegmentTransfer k z a n‖ ∧ ‖torusSegmentTransfer k z a n‖ ≤ growthBase k^n := by
  obtain ⟨w,rfl⟩ := liftProjection_surjective z
  rw [torusSegmentTransfer_lift]
  exact liftSegmentTransfer_norm_bounds k hk w a n
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_CocycleAlgebra
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
noncomputable def planeSwap : ℂ →L[ℝ] ℂ :=
  { toLinearMap :=
      { toFun := fun z => ⟨z.im,z.re⟩
        map_add' := by intro z w; apply Complex.ext <;> simp
        map_smul' := by intro t z; apply Complex.ext <;> simp }
    cont := Complex.equivRealProdCLM.symm.continuous.comp
      (Complex.continuous_im.prodMk Complex.continuous_re) }
@[simp] lemma planeSwap_re (z : ℂ) : (planeSwap z).re=z.im := rfl
@[simp] lemma planeSwap_im (z : ℂ) : (planeSwap z).im=z.re := rfl
@[simp] lemma planeSwap_invol (z : ℂ) : planeSwap (planeSwap z)=z := by apply Complex.ext <;> rfl
@[simp] lemma norm_planeSwap (z : ℂ) : ‖planeSwap z‖=‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [Complex.sq_norm,Complex.normSq_apply,planeSwap_re,planeSwap_im]
  ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BiCocycle
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
noncomputable def transferStepEquiv (v : ℝ) : ℂ ≃L[ℝ] ℂ :=
  { toLinearEquiv :=
      { toLinearMap := (transferStep v).toLinearMap
        invFun := transferStepInv v
        left_inv := transferStepInv_inv v
        right_inv := transferStep_inv v }
    continuous_toFun := (transferStep v).continuous
    continuous_invFun := (transferStepInv v).continuous }
@[simp] lemma transferStepEquiv_apply (v : ℝ) (u : ℂ) : transferStepEquiv v u=transferStep v u := rfl
@[simp] lemma transferStepEquiv_symm_apply (v : ℝ) (u : ℂ) : (transferStepEquiv v).symm u=transferStepInv v u := rfl
noncomputable def positivePrefix (G : ℤ → (ℂ ≃L[ℝ] ℂ)) : ℕ → (ℂ ≃L[ℝ] ℂ)
  | 0 => ContinuousLinearEquiv.refl ℝ ℂ
  | n+1 => (positivePrefix G n).trans (G (n:ℤ))
noncomputable def negativePrefix (G : ℤ → (ℂ ≃L[ℝ] ℂ)) : ℕ → (ℂ ≃L[ℝ] ℂ)
  | 0 => ContinuousLinearEquiv.refl ℝ ℂ
  | n+1 => (negativePrefix G n).trans (G (-((n:ℤ)+1))).symm
noncomputable def integerPrefix (G : ℤ → (ℂ ≃L[ℝ] ℂ)) : ℤ → (ℂ ≃L[ℝ] ℂ)
  | .ofNat n => positivePrefix G n
  | .negSucc n => negativePrefix G (n+1)
@[simp] lemma integerPrefix_nat (G : ℤ → (ℂ ≃L[ℝ] ℂ)) (n : ℕ) : integerPrefix G (n:ℤ)=positivePrefix G n := rfl
@[simp] lemma integerPrefix_neg_nat (G : ℤ → (ℂ ≃L[ℝ] ℂ)) (n : ℕ) : integerPrefix G (-(n:ℤ))=negativePrefix G n := by
  cases n <;> rfl
lemma integerPrefix_step (G : ℤ → (ℂ ≃L[ℝ] ℂ)) (i : ℤ) (u : ℂ) :
    integerPrefix G (i+1) u=G i (integerPrefix G i u) := by
  cases i with
  | ofNat n => rfl
  | negSucc n =>
    change integerPrefix G (-((n:ℤ)+1)+1) u=G (-((n:ℤ)+1)) (negativePrefix G (n+1) u)
    rw [show -((n:ℤ)+1)+1=-(n:ℤ) by ring,integerPrefix_neg_nat]
    simp only [negativePrefix,ContinuousLinearEquiv.trans_apply,ContinuousLinearEquiv.apply_symm_apply]
lemma equiv_area_symm (A : ℂ ≃L[ℝ] ℂ) (hA : PlaneAreaPreserving A.toContinuousLinearMap) :
    PlaneAreaPreserving A.symm.toContinuousLinearMap := by
  intro u v
  have h := hA (A.symm u) (A.symm v)
  simpa using h.symm
lemma equiv_area_trans (A B : ℂ ≃L[ℝ] ℂ)
    (hA : PlaneAreaPreserving A.toContinuousLinearMap) (hB : PlaneAreaPreserving B.toContinuousLinearMap) :
    PlaneAreaPreserving (A.trans B).toContinuousLinearMap := by
  intro u v
  exact (hB (A u) (A v)).trans (hA u v)
lemma integerPrefix_area (G : ℤ → (ℂ ≃L[ℝ] ℂ))
    (hG : ∀ i, PlaneAreaPreserving (G i).toContinuousLinearMap) (i : ℤ) :
    PlaneAreaPreserving (integerPrefix G i).toContinuousLinearMap := by
  have hp : ∀ n, PlaneAreaPreserving (positivePrefix G n).toContinuousLinearMap := by
    intro n
    induction n with
    | zero => exact fun _ _ => rfl
    | succ n ih => exact equiv_area_trans _ _ ih (hG _)
  have hm : ∀ n, PlaneAreaPreserving (negativePrefix G n).toContinuousLinearMap := by
    intro n
    induction n with
    | zero => exact fun _ _ => rfl
    | succ n ih => exact equiv_area_trans _ _ ih (equiv_area_symm _ (hG _))
  cases i with
  | ofNat n => exact hp n
  | negSucc n => exact hm (n+1)
noncomputable def torusPrefix (k : ℝ) (z : Torus) (i : ℤ) : ℂ ≃L[ℝ] ℂ :=
  integerPrefix (fun a => transferStepEquiv (torusPotential k (torusIter k a z).1)) i
noncomputable def torusTransfer (k : ℝ) (z : Torus) (i j : ℤ) : ℂ ≃L[ℝ] ℂ :=
  (torusPrefix k z i).symm.trans (torusPrefix k z j)
lemma torusTransfer_apply (k : ℝ) (z : Torus) (i j : ℤ) (u : ℂ) :
    torusTransfer k z i j u=torusPrefix k z j ((torusPrefix k z i).symm u) := rfl
lemma torusTransfer_comp (k : ℝ) (z : Torus) (i j l : ℤ) (u : ℂ) :
    torusTransfer k z j l (torusTransfer k z i j u)=torusTransfer k z i l u := by
  simp only [torusTransfer_apply,ContinuousLinearEquiv.symm_apply_apply]
lemma torusTransfer_self (k : ℝ) (z : Torus) (i : ℤ) :
    (torusTransfer k z i i).toContinuousLinearMap=ContinuousLinearMap.id ℝ ℂ := by
  ext u
  exact ContinuousLinearEquiv.apply_symm_apply _ _
lemma torusTransfer_area (k : ℝ) (z : Torus) (i j : ℤ) :
    PlaneAreaPreserving (torusTransfer k z i j).toContinuousLinearMap := by
  apply equiv_area_trans
  · apply equiv_area_symm
    exact integerPrefix_area (fun a => transferStepEquiv (torusPotential k (torusIter k a z).1))
      (fun a => transferStep_area _) i
  · exact integerPrefix_area (fun a => transferStepEquiv (torusPotential k (torusIter k a z).1))
      (fun a => transferStep_area _) j
lemma torusTransfer_forward (k : ℝ) (z : Torus) (a : ℤ) (n : ℕ) :
    (torusTransfer k z a (a+(n:ℤ))).toContinuousLinearMap=torusSegmentTransfer k z a n := by
  induction n with
  | zero => simpa only [Nat.cast_zero,add_zero,torusSegmentTransfer,transferProduct] using torusTransfer_self k z a
  | succ n ih =>
    ext u
    change torusPrefix k z (a+((n+1:ℕ):ℤ)) ((torusPrefix k z a).symm u)=_
    rw [show a+((n+1:ℕ):ℤ)=(a+(n:ℤ))+1 by omega]
    change integerPrefix _ ((a+(n:ℤ))+1) _=_
    rw [integerPrefix_step]
    change transferStep (torusPotential k (torusIter k (a+(n:ℤ)) z).1)
      ((torusTransfer k z a (a+(n:ℤ))).toContinuousLinearMap u)=_
    rw [ih]
    simp only [torusSegmentTransfer,transferProduct,ContinuousLinearMap.comp_apply,torusSegmentCoefficient]
    congr 1
    exact congrArg (fun t : ℤ => transferStep (torusPotential k (torusIter k t z).1)) (by omega)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ProductDistances
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
lemma torusTransfer_inverse (k : ℝ) (z : Torus) (i j : ℤ) (u : ℂ) :
    torusTransfer k z j i (torusTransfer k z i j u)=u := by
  rw [torusTransfer_comp]
  change (torusTransfer k z i i).toContinuousLinearMap u=u
  rw [torusTransfer_self]; rfl
lemma torusTransfer_norm_symm (k : ℝ) (z : Torus) (i j : ℤ) :
    ‖(torusTransfer k z i j).toContinuousLinearMap‖=‖(torusTransfer k z j i).toContinuousLinearMap‖ :=
  (torusTransfer_area k z i j).norm_inverse (torusTransfer_area k z j i) (torusTransfer_inverse k z j i) (torusTransfer_inverse k z i j)
lemma torusTransfer_one_le_norm (k : ℝ) (z : Torus) (i j : ℤ) :
    1≤‖(torusTransfer k z i j).toContinuousLinearMap‖ :=
  (torusTransfer_area k z i j).singular_pair.choose_spec.2.2.2.2
lemma torusTransfer_norm_pos (k : ℝ) (z : Torus) (i j : ℤ) :
    0<‖(torusTransfer k z i j).toContinuousLinearMap‖ := lt_of_lt_of_le zero_lt_one (torusTransfer_one_le_norm k z i j)
lemma torusTransfer_norm_le (k : ℝ) (hk : 0≤k) (z : Torus) (i j : ℤ) :
    ‖(torusTransfer k z i j).toContinuousLinearMap‖ ≤ growthBase k^(j-i).natAbs := by
  wlog hij : i≤j generalizing i j
  · rw [torusTransfer_norm_symm]
    convert this j i (le_of_not_ge hij) using 1
    all_goals try with_reducible_and_instances rfl
    rw [show i-j=-(j-i) by ring,Int.natAbs_neg]
  have hn : i+((j-i).natAbs:ℤ)=j := by rw [Int.natCast_natAbs,abs_of_nonneg (sub_nonneg.mpr hij)]; ring
  calc
    _ = ‖torusSegmentTransfer k z i (j-i).natAbs‖ := by rw [← torusTransfer_forward,hn]
    _ ≤ _ := (torusSegmentTransfer_norm_bounds k hk z i _).2
noncomputable def productDistance (k : ℝ) (z : Torus) (i j : ℤ) : ℝ :=
  Real.log ‖(torusTransfer k z i j).toContinuousLinearMap‖/Real.log (growthBase k)
lemma log_growthBase_pos (k : ℝ) (hk : 0≤k) : 0<Real.log (growthBase k) :=
  Real.log_pos (lt_of_lt_of_le (by norm_num : (1:ℝ)<4) (growthBase_ge_four k hk))
lemma productDistance_symm (k : ℝ) (z : Torus) (i j : ℤ) :
    productDistance k z i j=productDistance k z j i := by
  unfold productDistance; rw [torusTransfer_norm_symm]
@[simp] lemma productDistance_self (k : ℝ) (z : Torus) (i : ℤ) : productDistance k z i i=0 := by
  simp [productDistance,torusTransfer_self]
lemma productDistance_nonneg (k : ℝ) (hk : 0≤k) (z : Torus) (i j : ℤ) : 0≤productDistance k z i j :=
  div_nonneg (Real.log_nonneg (torusTransfer_one_le_norm k z i j)) (log_growthBase_pos k hk).le
lemma productDistance_le (k : ℝ) (hk : 0≤k) (z : Torus) (i j : ℤ) :
    productDistance k z i j≤|(j:ℝ)-(i:ℝ)| := by
  apply (div_le_iff₀ (log_growthBase_pos k hk)).mpr
  have hh := Real.log_le_log (torusTransfer_norm_pos k z i j) (torusTransfer_norm_le k hk z i j)
  rw [Real.log_pow] at hh
  have he : ((j-i).natAbs:ℝ)=|(j:ℝ)-(i:ℝ)| := by
    have hh := congrArg (fun a : ℤ => (a:ℝ)) (Int.natCast_natAbs (j-i))
    simpa only [Int.cast_natCast,Int.cast_abs,Int.cast_sub] using hh
  simpa only [he] using hh
lemma productDistance_triangle (k : ℝ) (hk : 0≤k) (z : Torus) (i j l : ℤ) :
    productDistance k z i l≤productDistance k z i j+productDistance k z j l := by
  have hc : (torusTransfer k z i l).toContinuousLinearMap=
      (torusTransfer k z j l).toContinuousLinearMap.comp (torusTransfer k z i j).toContinuousLinearMap := by
    ext u; exact (torusTransfer_comp k z i j l u).symm
  have hh := ContinuousLinearMap.opNorm_comp_le (torusTransfer k z j l).toContinuousLinearMap
    (torusTransfer k z i j).toContinuousLinearMap
  rw [← hc] at hh
  have hlog := Real.log_le_log (torusTransfer_norm_pos k z i l) hh
  rw [Real.log_mul (torusTransfer_norm_pos k z j l).ne' (torusTransfer_norm_pos k z i j).ne'] at hlog
  unfold productDistance
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by linarith) (log_growthBase_pos k hk).le
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_CancellationTheorem
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
noncomputable def cancellationConstant : ℝ := 2*(4:ℝ)^10000000
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_MeanDeficit
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
noncomputable def meanDeficit (k : ℝ) (n : ℕ) : ℝ :=
  1-(∫ z, productDistance k z 0 (n:ℤ) ∂area)/(n:ℝ)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_MeanCancellation
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
noncomputable def doublingConstant : ℝ := 10000000001+4*cancellationConstant
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_CriticalSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Filter Set
open scoped Topology Classical
namespace StandardMapEntropy

def BadGrowth (η k : ℝ) : Prop := ∃ n : ℕ, 0<n ∧ η ≤ meanDeficit k n

noncomputable def criticalTheta (r i : ℕ) : ℝ := (1/2:ℝ)^(i+r+1)
def criticalLowerExponent (r i : ℕ) : ℕ := 2*(i+r+1)
structure CriticalScaleSequence where
  offset : ℕ
  parameter : ℕ → ℝ
  exponent : ℕ → ℕ
  positive : ∀ i, 0 < parameter i
  large : ∀ i : ℕ, (i:ℝ) ≤ parameter i
  lower_lt : ∀ i, criticalLowerExponent offset i < exponent i
  threshold : ∀ i, criticalTheta offset i < meanDeficit (parameter i) (2^(exponent i))
  upper : ∀ i, meanDeficit (parameter i) (2^(exponent i)) ≤ 2*doublingConstant*criticalTheta offset i
  initial : ∀ i m, meanDeficit (parameter i) (2^(criticalLowerExponent offset i+m)) ≤
    2*(2*doublingConstant)^m*(criticalTheta offset i)^2
  terminal : ∀ i m, meanDeficit (parameter i) (2^(exponent i+m)) ≤
    2*(2*doublingConstant)^m*meanDeficit (parameter i) (2^(exponent i))
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence)
noncomputable def epsilon (i : ℕ) : ℝ := meanDeficit (S.parameter i) (2^(S.exponent i))
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_DyadicArrays
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

def dyadicTimes : AddSubgroup ℝ where
  carrier := {x | ∃ n : ℕ, ∃ a : ℤ, x=(a:ℝ)/(2:ℝ)^n}
  zero_mem' := ⟨0,0,by norm_num⟩
  add_mem' := by
    rintro x y ⟨n,a,rfl⟩ ⟨m,b,rfl⟩
    refine ⟨n+m,a*2^m+b*2^n,?_⟩
    rw [pow_add]
    push_cast
    field_simp
  neg_mem' := by
    rintro x ⟨n,a,rfl⟩
    exact ⟨n,-a,by push_cast; ring⟩
abbrev DyadicTime := dyadicTimes
lemma dyadicTime_mem (x : DyadicTime) : ∃ n : ℕ, ∃ a : ℤ, (x:ℝ)=(a:ℝ)/(2:ℝ)^n := x.property
noncomputable instance instCountableSubtypeRealMemAddSubgroupDyadicTime : Countable DyadicTime := by
  apply Set.Countable.to_subtype
  have hh : (dyadicTimes : Set ℝ)⊆Set.range (fun p : ℕ × ℤ => (p.2:ℝ)/(2:ℝ)^p.1) := by
    rintro x ⟨n,a,h⟩
    exact ⟨(n,a),h.symm⟩
  exact (Set.countable_range _).mono hh
noncomputable def dyadicInt (a : ℤ) : DyadicTime := ⟨a,0,a,by norm_num⟩
@[simp] lemma dyadicInt_val (a : ℤ) : (dyadicInt a:ℝ)=(a:ℝ) := rfl
noncomputable def dyadicHalf (x : DyadicTime) : DyadicTime :=
  ⟨(x:ℝ)/2,by
    obtain ⟨n,a,ha⟩ := dyadicTime_mem x
    refine ⟨n+1,a,?_⟩
    rw [ha,pow_succ]; ring⟩
@[simp] lemma dyadicHalf_val (x : DyadicTime) : (dyadicHalf x:ℝ)=(x:ℝ)/2 := rfl
@[simp] lemma dyadicHalf_add_self (x : DyadicTime) : dyadicHalf x+dyadicHalf x=x := by
  apply Subtype.ext
  change (x:ℝ)/2+(x:ℝ)/2=(x:ℝ); ring
@[simp] lemma dyadicHalf_double (x : DyadicTime) : dyadicHalf (x+x)=x := by
  apply Subtype.ext
  change ((x:ℝ)+(x:ℝ))/2=(x:ℝ); ring
noncomputable def dyadicMid (s t : DyadicTime) : DyadicTime := dyadicHalf (s+t)
@[simp] lemma dyadicMid_val (s t : DyadicTime) : (dyadicMid s t:ℝ)=((s:ℝ)+(t:ℝ))/2 := rfl

def AmbientArray (d : DyadicTime → DyadicTime → ℝ) : Prop :=
  (∀ s t, 0≤d s t) ∧ (∀ s, d s s=0) ∧ (∀ s t, d s t=d t s) ∧
  (∀ s t u, d s u≤d s t+d t u) ∧ (∀ s t, d s t≤|(t:ℝ)-(s:ℝ)|+2)
abbrev DistanceArray := {d : DyadicTime → DyadicTime → ℝ // AmbientArray d}
lemma isClosed_ambientArray : IsClosed {d | AmbientArray d} := by
  unfold AmbientArray
  simp only [Set.ofPred_and,Set.ofPred_forall]
  apply IsClosed.inter
  · exact isClosed_iInter fun s => isClosed_iInter fun t => isClosed_le continuous_const (continuous_apply t |>.comp (continuous_apply s))
  apply IsClosed.inter
  · exact isClosed_iInter fun s => isClosed_eq (continuous_apply s |>.comp (continuous_apply s)) continuous_const
  apply IsClosed.inter
  · exact isClosed_iInter fun s => isClosed_iInter fun t => isClosed_eq
      (continuous_apply t |>.comp (continuous_apply s)) (continuous_apply s |>.comp (continuous_apply t))
  apply IsClosed.inter
  · refine isClosed_iInter fun s => isClosed_iInter fun t => isClosed_iInter fun u => ?_
    have h1 : Continuous (fun d : DyadicTime → DyadicTime → ℝ => d s t) := (continuous_apply t).comp (continuous_apply s)
    have h2 : Continuous (fun d : DyadicTime → DyadicTime → ℝ => d t u) := (continuous_apply u).comp (continuous_apply t)
    exact isClosed_le ((continuous_apply u).comp (continuous_apply s)) (h1.add h2)
  · exact isClosed_iInter fun s => isClosed_iInter fun t => isClosed_le
      (continuous_apply t |>.comp (continuous_apply s)) continuous_const
lemma isCompact_ambientArray : IsCompact {d | AmbientArray d} := by
  have hc : IsCompact {d : DyadicTime → DyadicTime → ℝ | ∀ s t : DyadicTime, d s t∈Icc (0:ℝ) (|(t:ℝ)-(s:ℝ)|+2)} :=
    isCompact_pi_infinite fun s => isCompact_pi_infinite fun t => isCompact_Icc
  apply hc.of_isClosed_subset isClosed_ambientArray
  intro d hd s t
  exact ⟨hd.1 s t,hd.2.2.2.2 s t⟩
noncomputable instance instCompactSpaceDistanceArray : CompactSpace DistanceArray := isCompact_iff_compactSpace.mp isCompact_ambientArray
noncomputable def arrayEval (s t : DyadicTime) (d : DistanceArray) : ℝ := d.val s t
lemma continuous_arrayEval (s t : DyadicTime) : Continuous (arrayEval s t) :=
  (continuous_apply t).comp ((continuous_apply s).comp continuous_subtype_val)
noncomputable def affineArray (w : Set.Icc (0:ℝ) 1) : DistanceArray := ⟨fun s t => w.val*|(t:ℝ)-(s:ℝ)|,by
  refine ⟨fun s t => mul_nonneg w.property.1 (abs_nonneg _),?_,?_,?_,?_⟩
  · intro s; simp
  · intro s t; dsimp only; rw [abs_sub_comm]
  · intro s t u
    calc
      _ ≤ w.val*(|(t:ℝ)-(s:ℝ)|+|(u:ℝ)-(t:ℝ)|) := mul_le_mul_of_nonneg_left (by
        simpa only [add_comm] using abs_sub_le (u:ℝ) (t:ℝ) (s:ℝ)) w.property.1
      _ = _ := by ring
  · intro s t
    have hh := mul_le_mul_of_nonneg_right w.property.2 (abs_nonneg ((t:ℝ)-(s:ℝ)))
    linarith⟩
lemma continuous_affineArray : Continuous affineArray := by
  apply Continuous.subtype_mk
  apply continuous_pi; intro s
  apply continuous_pi; intro t
  exact continuous_subtype_val.mul continuous_const
noncomputable def affineLocus : Set DistanceArray := Set.range affineArray
lemma isCompact_affineLocus : IsCompact affineLocus := isCompact_range continuous_affineArray
lemma isClosed_affineLocus : IsClosed affineLocus := isCompact_affineLocus.isClosed
abbrev NonAffineArray := {d : DistanceArray // d∉affineLocus}
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ArrayTests
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
noncomputable def arrayTranslate (r : DyadicTime) (d : DistanceArray) : DistanceArray :=
  ⟨fun s t => d.val (s+r) (t+r),by
    obtain ⟨h0,hs,hsy,ht,hb⟩ := d.property
    refine ⟨fun s t => h0 _ _,fun s => hs _,fun s t => hsy _ _,fun s t u => ht _ _ _,?_⟩
    intro s t
    convert hb (s+r) (t+r) using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    change (t:ℝ)-(s:ℝ)=((t:ℝ)+(r:ℝ))-((s:ℝ)+(r:ℝ))
    ring⟩
@[simp] lemma arrayTranslate_zero (d : DistanceArray) : arrayTranslate 0 d=d := by
  apply Subtype.ext
  funext s t
  simp [arrayTranslate]
noncomputable def arrayDilate (d : DistanceArray) : DistanceArray :=
  ⟨fun s t => d.val (s+s) (t+t)/2,by
    obtain ⟨h0,hs,hsy,ht,hb⟩ := d.property
    refine ⟨fun s t => div_nonneg (h0 _ _) (by norm_num),?_,?_,?_,?_⟩
    · intro s; simp only [hs,zero_div]
    · intro s t; dsimp only; rw [hsy]
    · intro s t u; have := ht (s+s) (t+t) (u+u); dsimp only; linarith
    · intro s t
      have hh := hb (s+s) (t+t)
      change d.val (s+s) (t+t)≤|((t:ℝ)+(t:ℝ))-((s:ℝ)+(s:ℝ))|+2 at hh
      rw [show ((t:ℝ)+(t:ℝ))-((s:ℝ)+(s:ℝ))=2*((t:ℝ)-(s:ℝ)) by ring,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
      dsimp only; linarith⟩
lemma continuous_arrayDilate : Continuous arrayDilate := by
  apply Continuous.subtype_mk
  apply continuous_pi; intro s
  apply continuous_pi; intro t
  exact (continuous_arrayEval (s+s) (t+t)).div_const 2
@[simp] lemma arrayDilate_affine (w : Icc (0:ℝ) 1) : arrayDilate (affineArray w)=affineArray w := by
  apply Subtype.ext
  funext s t
  change (w.val*|((t:ℝ)+(t:ℝ))-((s:ℝ)+(s:ℝ))|)/2=w.val*|(t:ℝ)-(s:ℝ)|
  rw [show ((t:ℝ)+(t:ℝ))-((s:ℝ)+(s:ℝ))=2*((t:ℝ)-(s:ℝ)) by ring,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  ring
@[simp] lemma arrayTranslate_affine (r : DyadicTime) (w : Icc (0:ℝ) 1) : arrayTranslate r (affineArray w)=affineArray w := by
  apply Subtype.ext
  funext s t
  change w.val*|((t:ℝ)+(r:ℝ))-((s:ℝ)+(r:ℝ))|=w.val*|(t:ℝ)-(s:ℝ)|
  congr 2; ring
lemma arrayDilate_mem_affine_iff (d : DistanceArray) : arrayDilate d∈affineLocus ↔ d∈affineLocus := by
  constructor
  · rintro ⟨w,hw⟩
    refine ⟨w,?_⟩
    apply Subtype.ext
    funext s t
    have he := congrArg (fun d : DistanceArray => d.val (dyadicHalf s) (dyadicHalf t)) hw
    change w.val*|((t:ℝ)/2)-((s:ℝ)/2)|=d.val (dyadicHalf s+dyadicHalf s) (dyadicHalf t+dyadicHalf t)/2 at he
    rw [dyadicHalf_add_self,dyadicHalf_add_self,← sub_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)] at he
    change w.val*|(t:ℝ)-(s:ℝ)|=d.val s t
    linarith
  · rintro ⟨w,rfl⟩; exact ⟨w,(arrayDilate_affine w).symm⟩
noncomputable def arrayShortfall (s t : DyadicTime) (d : DistanceArray) : ℝ :=
  1-d.val s t/((t:ℝ)-(s:ℝ))
noncomputable def arrayJ (s t : DyadicTime) (d : DistanceArray) : ℝ :=
  arrayShortfall s t d-(arrayShortfall s (dyadicMid s t) d+arrayShortfall (dyadicMid s t) t d)/2
lemma arrayJ_eq (s t : DyadicTime) (hst : (s:ℝ)<(t:ℝ)) (d : DistanceArray) :
    arrayJ s t d=(d.val s (dyadicMid s t)+d.val (dyadicMid s t) t-d.val s t)/((t:ℝ)-(s:ℝ)) := by
  unfold arrayJ arrayShortfall
  rw [dyadicMid_val]
  have h1 : (t:ℝ)-(s:ℝ)≠0 := sub_ne_zero.mpr hst.ne'
  have h2 : ((s:ℝ)+(t:ℝ))/2-(s:ℝ)≠0 := by linarith
  have h3 : (t:ℝ)-((s:ℝ)+(t:ℝ))/2≠0 := by linarith
  rw [show ((s:ℝ)+(t:ℝ))/2-(s:ℝ)=((t:ℝ)-(s:ℝ))/2 by ring,
    show (t:ℝ)-((s:ℝ)+(t:ℝ))/2=((t:ℝ)-(s:ℝ))/2 by ring]
  field_simp [h1]; ring
lemma arrayJ_nonneg (s t : DyadicTime) (hst : (s:ℝ)<(t:ℝ)) (d : DistanceArray) : 0≤arrayJ s t d := by
  rw [arrayJ_eq s t hst d]
  exact div_nonneg (sub_nonneg.mpr (d.property.2.2.2.1 _ _ _)) (sub_pos.mpr hst).le
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ArrayAffinity
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
noncomputable def dyadicUnit (n : ℕ) : DyadicTime := ⟨(1:ℝ)/(2:ℝ)^n,n,1,by simp⟩
@[simp] lemma dyadicUnit_val (n : ℕ) : (dyadicUnit n:ℝ)=(1:ℝ)/(2:ℝ)^n := rfl
abbrev ArrayTestIndex := {p : DyadicTime × DyadicTime // (p.1:ℝ)<(p.2:ℝ)}
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_RescaledArrays
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
lemma floor_difference_bound (x y : ℝ) : |(⌊y⌋:ℝ)-(⌊x⌋:ℝ)|≤|y-x|+1 := by
  have hx0 := Int.floor_le x
  have hx1 := Int.lt_floor_add_one x
  have hy0 := Int.floor_le y
  have hy1 := Int.lt_floor_add_one y
  rw [abs_le]
  constructor <;> linarith [le_abs_self (y-x),neg_le_abs (y-x)]
noncomputable def rescaledDistance (k : ℝ) (z : Torus) (n : ℕ) (s t : DyadicTime) : ℝ :=
  productDistance k z ⌊(n:ℝ)*(s:ℝ)⌋ ⌊(n:ℝ)*(t:ℝ)⌋/(n:ℝ)
lemma rescaledDistance_bound (k : ℝ) (hk : 0≤k) (z : Torus) (n : ℕ) (hn : 0<n) (s t : DyadicTime) :
    rescaledDistance k z n s t≤|(t:ℝ)-(s:ℝ)|+1/(n:ℝ) := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have h := (productDistance_le k hk z ⌊(n:ℝ)*(s:ℝ)⌋ ⌊(n:ℝ)*(t:ℝ)⌋).trans (floor_difference_bound _ _)
  rw [← mul_sub,abs_mul,abs_of_pos hn'] at h
  unfold rescaledDistance
  apply (div_le_iff₀ hn').mpr
  rw [add_mul,div_mul_cancel₀ _ hn'.ne']
  nlinarith
noncomputable def sampleArray (k : ℝ) (hk : 0≤k) (z : Torus) (n : ℕ) (hn : 0<n) : DistanceArray :=
  ⟨rescaledDistance k z n,by
    have hn' : (0:ℝ)<n := by exact_mod_cast hn
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro s t; exact div_nonneg (productDistance_nonneg k hk z _ _) hn'.le
    · intro s; simp [rescaledDistance]
    · intro s t; unfold rescaledDistance; rw [productDistance_symm]
    · intro s t u
      dsimp only [rescaledDistance]
      rw [← add_div]
      exact div_le_div_of_nonneg_right (productDistance_triangle k hk z _ _ _) hn'.le
    · intro s t
      have h1 : 1/(n:ℝ)≤1 := (div_le_one hn').mpr (by exact_mod_cast hn)
      linarith [rescaledDistance_bound k hk z n hn s t]⟩
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_SampleLaws
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
noncomputable def sampleLaw (k : ℝ) (hk : 0≤k) (n : ℕ) (hn : 0<n) : Measure DistanceArray :=
  area.map (fun z => sampleArray k hk z n hn)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ScaleLaws
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
noncomputable def scaleLaw (k : ℝ) (hk : 0≤k) (p l : ℕ) (ε : ℝ) : Measure DistanceArray :=
  ENNReal.ofReal (1/ε) • ∑ i∈Finset.range l,sampleLaw k hk (2^(p+i)) (by positivity)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_CriticalLaws
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
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence)
noncomputable def initialLaw (i : ℕ) : Measure DistanceArray :=
  scaleLaw (S.parameter i) (S.positive i).le (criticalLowerExponent S.offset i) 1 (S.epsilon i)
noncomputable def terminalLaw (i : ℕ) : Measure DistanceArray :=
  scaleLaw (S.parameter i) (S.positive i).le (S.exponent i) 1 (S.epsilon i)
noncomputable def multiLaw (i : ℕ) : Measure DistanceArray :=
  scaleLaw (S.parameter i) (S.positive i).le (criticalLowerExponent S.offset i)
    (S.exponent i-criticalLowerExponent S.offset i) (S.epsilon i)
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_NonaffineLimits
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
noncomputable instance instLocallyCompactSpaceNonAffineArray : LocallyCompactSpace NonAffineArray := isClosed_affineLocus.isOpen_compl.locallyCompactSpace
noncomputable def nonaffinePart (μ : Measure DistanceArray) : Measure NonAffineArray := μ.comap Subtype.val
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_CriticalLimits
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
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence)

structure LimitLaws where
  filter : Ultrafilter ℕ
  refines : (filter : Filter ℕ) ≤ atTop
  multi : Measure NonAffineArray
  terminal : Measure NonAffineArray
  multi_regular : multi.Regular
  terminal_regular : terminal.Regular
  multi_local : IsFiniteMeasureOnCompacts multi
  terminal_local : IsFiniteMeasureOnCompacts terminal
  multi_converges : ∀ g : C_c(NonAffineArray,ℝ),
    Tendsto (fun i => ∫ d,g d ∂nonaffinePart (S.multiLaw i)) (filter:Filter ℕ) (𝓝 (∫ d,g d ∂multi))
  terminal_converges : ∀ g : C_c(NonAffineArray,ℝ),
    Tendsto (fun i => ∫ d,g d ∂nonaffinePart (S.terminalLaw i)) (filter:Filter ℕ) (𝓝 (∫ d,g d ∂terminal))
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ArrayActions
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
noncomputable def nonaffineDilate (d : NonAffineArray) : NonAffineArray :=
  ⟨arrayDilate d.val,by simpa only [arrayDilate_mem_affine_iff] using d.property⟩
lemma continuous_nonaffineDilate : Continuous nonaffineDilate :=
  (continuous_arrayDilate.comp continuous_subtype_val).subtype_mk _
lemma proper_nonaffineDilate : IsProperMap nonaffineDilate := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨continuous_nonaffineDilate,?_⟩
  intro K hK
  have hA : IsCompact (Subtype.val '' K : Set DistanceArray) := hK.image continuous_subtype_val
  have hB : IsCompact (arrayDilate ⁻¹' (Subtype.val '' K)) :=
    (hA.isClosed.preimage continuous_arrayDilate).isCompact
  have hsub : arrayDilate ⁻¹' (Subtype.val '' K) ⊆ affineLocusᶜ := by
    rintro d ⟨u,hu,he⟩
    exact fun hd => u.property (he ▸ (arrayDilate_mem_affine_iff d).mpr hd)
  have hsub' : arrayDilate ⁻¹' (Subtype.val '' K) ⊆ Set.range ((↑) : NonAffineArray → DistanceArray) :=
    fun d hd => ⟨⟨d,hsub hd⟩,rfl⟩
  have hh := IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hB hsub'
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  ext d
  change nonaffineDilate d ∈ K ↔ ∃ u ∈ K,u.val=arrayDilate d.val
  exact ⟨fun hd => ⟨nonaffineDilate d,hd,rfl⟩,fun ⟨u,hu,he⟩ => (Subtype.ext he : u=nonaffineDilate d) ▸ hu⟩

noncomputable def arrayTestExtend (g : C_c(NonAffineArray,ℝ)) : C_c(DistanceArray,ℝ) := {
  toFun := Subtype.val.extend g 0
  continuous_toFun := HasCompactSupport.continuous_extend_zero isClosed_affineLocus.isOpen_compl g.continuous g.hasCompactSupport
  hasCompactSupport' := g.hasCompactSupport.extend_zero continuous_subtype_val }
@[simp] lemma arrayTestExtend_apply (g : C_c(NonAffineArray,ℝ)) (d : NonAffineArray) :
    arrayTestExtend g d.val=g d := Subtype.val_injective.extend_apply _ _ _
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_LimitActions
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
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
instance instRegularNonAffineArrayMulti : L.multi.Regular := L.multi_regular
instance instRegularNonAffineArrayTerminal : L.terminal.Regular := L.terminal_regular
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_LimitBalance
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
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
instance multi_dilate_local : IsFiniteMeasureOnCompacts (L.multi.map nonaffineDilate) where
  lt_top_of_isCompact K hK := by
    rw [Measure.map_apply continuous_nonaffineDilate.measurable hK.isClosed.measurableSet]
    exact (proper_nonaffineDilate.isCompact_preimage hK).measure_lt_top
instance multi_terminal_local : IsFiniteMeasureOnCompacts (L.multi+L.terminal) where
  lt_top_of_isCompact K hK := by
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top,hK.measure_lt_top⟩
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_RealArrays
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
def UnitArray (d : DistanceArray) : Prop := ∀ s t : DyadicTime, d.val s t ≤ |(t:ℝ)-(s:ℝ)|
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ArrayHalf
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
noncomputable def arrayHalf (d : DistanceArray) (hu : UnitArray d) : DistanceArray :=
  ⟨fun s t => 2*d.val (dyadicHalf s) (dyadicHalf t),by
    obtain ⟨h0,hs,hsy,ht,hb⟩ := d.property
    refine ⟨fun s t => mul_nonneg (by norm_num) (h0 _ _),?_,?_,?_,?_⟩
    · intro s; simp only [hs,mul_zero]
    · intro s t; dsimp only; rw [hsy]
    · intro s t u; have := ht (dyadicHalf s) (dyadicHalf t) (dyadicHalf u); dsimp only; linarith
    · intro s t
      have hh := hu (dyadicHalf s) (dyadicHalf t)
      change d.val (dyadicHalf s) (dyadicHalf t)≤|(t:ℝ)/2-(s:ℝ)/2| at hh
      rw [←sub_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
      dsimp only; linarith⟩
lemma arrayDilate_half (d : DistanceArray) (hu : UnitArray d) : arrayDilate (arrayHalf d hu)=d := by
  apply Subtype.ext; funext s t
  change (2*d.val (dyadicHalf (s+s)) (dyadicHalf (t+t)))/2=d.val s t
  rw [dyadicHalf_double,dyadicHalf_double]; ring
noncomputable def nonaffineHalfOn (d : {d : NonAffineArray // UnitArray d.val}) : NonAffineArray :=
  ⟨arrayHalf d.val.val d.property,by
    intro ha
    have hh := (arrayDilate_mem_affine_iff _).mpr ha
    rw [arrayDilate_half] at hh
    exact d.val.property hh⟩
noncomputable def nonaffineHalf (d : NonAffineArray) : NonAffineArray :=
  if h : UnitArray d.val then nonaffineHalfOn ⟨d,h⟩ else d
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TreeLine
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

def NoFastCancellation (d : ℝ → ℝ → ℝ) (δ : ℝ) : Prop :=
  ∀ z t : ℝ, 0 < t → ¬ ((1-δ)*t < d (z-t) z ∧ (1-δ)*t < d z (z+t) ∧ d (z-t) (z+t) < δ*t)

def ExteriorUnitRays (d : ℝ → ℝ → ℝ) (a b : ℝ) : Prop :=
  (∀ x y : ℝ, x ≤ a → y ≤ a → d x y=|y-x|) ∧
  (∀ x y : ℝ, b ≤ x → b ≤ y → d x y=|y-x|)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TreeLocalAffine
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
def LocallyAffineAt (d : ℝ → ℝ → ℝ) (x w : ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∀ u∈ball x r,∀ v∈ball x r,d u v=w*|v-u|
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_MiddleCount
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

def MiddleLogGood (z : ℕ → ℝ) (N i : ℕ) : Prop :=
  (∀ j, j < i → (49/50:ℝ)*((i:ℝ)-(j:ℝ)) ≤ z i-z j) ∧
  (∀ j, i < j → j ≤ N → (49/50:ℝ)*((j:ℝ)-(i:ℝ)) ≤ z j-z i)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BridgeScalars
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
structure BridgeScalarControl (k : ℝ) : Prop where
  nonneg : 0 ≤ k
  prefix_geom : growthBase k^(-(49/25:ℝ)) ≤ 1/2
  prefix_small : 3*growthBase k^(-(47/50:ℝ)) ≤ 1/4
  graph_geom : growthBase k^(-(3/5:ℝ)) ≤ 1/2
  graph_small : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2
  slope_small : 24/growthBase k^((4/5:ℝ)) ≤ 1/2
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BridgeSamples
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
noncomputable def arrayObservation {R : ℕ} (a b : Fin R → DyadicTime)
    (F : (Fin R → ℝ) → ℝ) (d : DistanceArray) : ℝ := F (fun i => arrayShortfall (a i) (b i) d)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BridgeGrid
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

structure BridgeGrid (Rw Rh : ℕ) where
  p : ℕ
  u : DyadicTime
  v : DyadicTime
  b : ℤ
  N : ℕ
  r : ℕ
  large : 100≤ N
  narrow : (r:ℝ)≤ (N:ℝ)/1000
  hu : ((2^p:ℕ):ℝ)*(u:ℝ)=(b:ℝ)
  hv : ((2^p:ℕ):ℝ)*(v:ℝ)=(b:ℝ)+(N:ℝ)
  sw : Fin Rw → DyadicTime
  tw : Fin Rw → DyadicTime
  sh : Fin Rh → DyadicTime
  th : Fin Rh → DyadicTime
  aw : Fin Rw → ℤ
  nw : Fin Rw → ℕ
  ah : Fin Rh → ℤ
  nh : Fin Rh → ℕ
  pw : ∀j,0< nw j
  ph : ∀j,0< nh j
  hwleft : ∀j,-(r:ℤ)≤ aw j
  hwright : ∀j,aw j+(nw j:ℤ)≤ r
  hhleft : ∀j,-(r:ℤ)≤ ah j-(N:ℤ)
  hhright : ∀j,ah j+(nh j:ℤ)-(N:ℤ)≤ r
  hsw : ∀j,((2^p:ℕ):ℝ)*(sw j:ℝ)=((aw j+b):ℤ)
  htw : ∀j,((2^p:ℕ):ℝ)*(tw j:ℝ)=((aw j+b):ℤ)+(nw j:ℝ)
  hsh : ∀j,((2^p:ℕ):ℝ)*(sh j:ℝ)=((ah j+b):ℤ)
  hth : ∀j,((2^p:ℕ):ℝ)*(th j:ℝ)=((ah j+b):ℤ)+(nh j:ℝ)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TestObservations
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
noncomputable def unitClip (x : ℝ) : ℝ := max 0 (min 1 x)
lemma unitClip_mem (x : ℝ) : unitClip x∈Icc (0:ℝ) 1 := by
  exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
lemma unitClip_lipschitz : LipschitzWith 1 unitClip := by
  exact ((LipschitzWith.id : LipschitzWith 1 (fun x : ℝ => x)).const_min 1).const_max 0
lemma bounded_square_lipschitz {a b : ℝ} (ha : |a|≤1) (hb : |b|≤1) : |a^2-b^2|≤2*|a-b| := by
  have hab : |a+b|≤2 := (abs_add_le a b).trans (by linarith)
  rw [show a^2-b^2=(a-b)*(a+b) by ring,abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left hab (abs_nonneg (a-b))]
noncomputable def testObservation (x : Fin 3 → ℝ) : ℝ :=
  x 0-(x 1+x 2)/2+(unitClip (x 1)-unitClip (x 2))^2
lemma testObservation_lipschitz : LipschitzWith 6 testObservation := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hc (j : Fin 3) : |x j-y j|≤dist x y := by
    simpa only [Real.dist_eq,one_mul,NNReal.coe_one] using (LipschitzWith.eval j).dist_le_mul x y
  have hd (j : Fin 3) : |unitClip (x j)-unitClip (y j)|≤dist x y := by
    have hh := unitClip_lipschitz.dist_le_mul (x j) (y j)
    simp only [Real.dist_eq,one_mul,NNReal.coe_one] at hh
    exact hh.trans (hc j)
  have hxy (z : Fin 3 → ℝ) : |unitClip (z 1)-unitClip (z 2)|≤1 := by
    rw [abs_le]
    have h1 := unitClip_mem (z 1)
    have h2 := unitClip_mem (z 2)
    constructor <;> linarith [h1.1,h1.2,h2.1,h2.2]
  have hdiff : |(unitClip (x 1)-unitClip (x 2))-(unitClip (y 1)-unitClip (y 2))|≤2*dist x y := by
    calc
      _ = |(unitClip (x 1)-unitClip (y 1))-(unitClip (x 2)-unitClip (y 2))| := by congr 1; ring
      _ ≤ |unitClip (x 1)-unitClip (y 1)|+|unitClip (x 2)-unitClip (y 2)| := by simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (unitClip (x 1)-unitClip (y 1)) 0 (unitClip (x 2)-unitClip (y 2))
      _ ≤ _ := by linarith [hd 1,hd 2]
  have hsq := (bounded_square_lipschitz (hxy x) (hxy y)).trans (mul_le_mul_of_nonneg_left hdiff (by norm_num))
  have hlin : |(x 0-(x 1+x 2)/2)-(y 0-(y 1+y 2)/2)|≤2*dist x y := by
    calc
      _ = |(x 0-y 0)-((x 1-y 1)+(x 2-y 2))/2| := by congr 1; ring
      _ ≤ |x 0-y 0|+|((x 1-y 1)+(x 2-y 2))/2| := by simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (x 0-y 0) 0 (((x 1-y 1)+(x 2-y 2))/2)
      _ = |x 0-y 0|+|(x 1-y 1)+(x 2-y 2)|/2 := by rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
      _ ≤ _ := by linarith [abs_add_le (x 1-y 1) (x 2-y 2),hc 0,hc 1,hc 2]
  rw [Real.dist_eq]
  change |(x 0-(x 1+x 2)/2+(unitClip (x 1)-unitClip (x 2))^2)-
    (y 0-(y 1+y 2)/2+(unitClip (y 1)-unitClip (y 2))^2)|≤(6:ℝ)*dist x y
  have hab := abs_add_le ((x 0-(x 1+x 2)/2)-(y 0-(y 1+y 2)/2))
    ((unitClip (x 1)-unitClip (x 2))^2-(unitClip (y 1)-unitClip (y 2))^2)
  have he : (x 0-(x 1+x 2)/2+(unitClip (x 1)-unitClip (x 2))^2)-
      (y 0-(y 1+y 2)/2+(unitClip (y 1)-unitClip (y 2))^2)=
    ((x 0-(x 1+x 2)/2)-(y 0-(y 1+y 2)/2))+
    ((unitClip (x 1)-unitClip (x 2))^2-(unitClip (y 1)-unitClip (y 2))^2) := by ring
  rw [he]
  linarith
noncomputable def testLeft (s t : DyadicTime) : Fin 3 → DyadicTime := ![s,s,dyadicMid s t]
noncomputable def testRight (s t : DyadicTime) : Fin 3 → DyadicTime := ![t,dyadicMid s t,t]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ClippedTests
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
noncomputable def clippedTest (j : ArrayTestIndex) : DistanceArray → ℝ :=
  arrayObservation (testLeft j.val.1 j.val.2) (testRight j.val.1 j.val.2) testObservation
lemma clippedTest_eq (j : ArrayTestIndex) (d : DistanceArray) :
    clippedTest j d=arrayJ j.val.1 j.val.2 d+
      (unitClip (arrayShortfall j.val.1 (dyadicMid j.val.1 j.val.2) d)-
        unitClip (arrayShortfall (dyadicMid j.val.1 j.val.2) j.val.2 d))^2 := by rfl
lemma clippedTest_nonneg (j : ArrayTestIndex) (d : DistanceArray) : 0≤ clippedTest j d := by
  rw [clippedTest_eq]
  exact add_nonneg (arrayJ_nonneg _ _ j.property d) (sq_nonneg _)
noncomputable def clippedShortfall (s t : DyadicTime) (d : DistanceArray) : ℝ := unitClip (arrayShortfall s t d)
lemma clippedShortfall_nonneg (s t : DyadicTime) (d : DistanceArray) : 0≤ clippedShortfall s t d := (unitClip_mem _).1
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_EndpointObservations
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
noncomputable def shortfallObservationFunction (x : Fin 1 → ℝ) : ℝ := unitClip (x 0)
lemma shortfallObservationFunction_lipschitz : LipschitzWith 6 shortfallObservationFunction := by
  exact (unitClip_lipschitz.comp (LipschitzWith.eval (0 : Fin 1))).weaken (by norm_num)
lemma testObservation_zero : testObservation 0=0 := by norm_num [testObservation,unitClip]
lemma shortfallObservationFunction_zero : shortfallObservationFunction 0=0 := by norm_num [shortfallObservationFunction,unitClip]
structure EndpointObservation where
  size : ℕ
  left : Fin size → DyadicTime
  right : Fin size → DyadicTime
  ordered : ∀i,(left i:ℝ)<(right i:ℝ)
  function : (Fin size → ℝ) → ℝ
  lipschitz : LipschitzWith 6 function
  at_zero : function 0=0
  nonneg : ∀d,0≤ arrayObservation left right function d
noncomputable def EndpointObservation.value (O : EndpointObservation) : DistanceArray → ℝ :=
  arrayObservation O.left O.right O.function
noncomputable def testEndpoint (j : ArrayTestIndex) : EndpointObservation where
  size := 3
  left := testLeft j.val.1 j.val.2
  right := testRight j.val.1 j.val.2
  ordered := by
    intro i
    fin_cases i <;> dsimp [testLeft,testRight,dyadicMid,dyadicHalf] <;> linarith [j.property]
  function := testObservation
  lipschitz := testObservation_lipschitz
  at_zero := testObservation_zero
  nonneg := clippedTest_nonneg j
noncomputable def shortfallEndpoint (j : ArrayTestIndex) : EndpointObservation where
  size := 1
  left := fun _ => j.val.1
  right := fun _ => j.val.2
  ordered := fun _ => j.property
  function := shortfallObservationFunction
  lipschitz := shortfallObservationFunction_lipschitz
  at_zero := shortfallObservationFunction_zero
  nonneg := clippedShortfall_nonneg _ _
@[simp] lemma testEndpoint_value (j : ArrayTestIndex) (d : DistanceArray) : (testEndpoint j).value d=clippedTest j d := rfl
@[simp] lemma shortfallEndpoint_value (j : ArrayTestIndex) (d : DistanceArray) :
    (shortfallEndpoint j).value d=clippedShortfall j.val.1 j.val.2 d := rfl
def EndpointObservation.inWindow (O : EndpointObservation) (u : DyadicTime) (q : ℕ) : Prop :=
  (∀i,-((1:ℝ)/(2:ℝ)^q)≤(O.left i:ℝ)-(u:ℝ)) ∧
  (∀i,(O.right i:ℝ)-(u:ℝ)≤(1:ℝ)/(2:ℝ)^q)
namespace CriticalScaleSequence
noncomputable def LimitLaws.selected (S : CriticalScaleSequence) (K : S.LimitLaws) (b : Bool) : Measure NonAffineArray :=
  if b then K.multi else K.terminal
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BridgeExclusions
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
noncomputable def bridgeLeft (b : Bool) (j l : ArrayTestIndex) : EndpointObservation :=
  if b then testEndpoint j else shortfallEndpoint l
noncomputable def bridgeRight (b : Bool) (j l : ArrayTestIndex) : EndpointObservation :=
  if b then shortfallEndpoint l else testEndpoint j
def DyadicBridgeExclusions (d : DistanceArray) : Prop :=
  ∀ (u v : DyadicTime) (q : ℕ) (j l : ArrayTestIndex) (b : Bool),
    (u:ℝ)<(v:ℝ) → (1:ℝ)/(2:ℝ)^q≤((v:ℝ)-(u:ℝ))/1000 →
    (bridgeLeft b j l).inWindow u q → (bridgeRight b j l).inWindow v q →
    0<(bridgeLeft b j l).value d → 0<(bridgeRight b j l).value d →
    d.val u v≤(999/1000:ℝ)*((v:ℝ)-(u:ℝ))
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_LocalMidpointGrid
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
def MidpointAffineOn (d : ℝ → ℝ → ℝ) (U : Set ℝ) : Prop :=
  ∀s∈U,∀t∈U,s< t → d s ((s+t)/2)=d s t/2 ∧ d ((s+t)/2) t=d s t/2
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ShapeComponents
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
def NonaffineLine (d : ℝ → ℝ → ℝ) : Prop := ¬∃w:ℝ,∀x y:ℝ,d x y=w*|y-x|
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_RemainderLaws
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
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
noncomputable def backwardLaw (n : ℕ) : Measure NonAffineArray := L.terminal.map (nonaffineHalf^[n])
noncomputable def backwardSum : Measure NonAffineArray := Measure.sum (fun n : ℕ => S.backwardLaw L (n+1))
noncomputable def remainderLaw : Measure NonAffineArray := L.multi-S.backwardSum L
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_WeightedCompact
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
structure CompactWeightLimit {ι:Type*} (l:Filter ι) (μ:ι→Measure DistanceArray) (f:DistanceArray→ℝ) where
  law : Measure DistanceArray
  regular : law.Regular
  finite : IsFiniteMeasure law
  converges : ∀g:C(DistanceArray,ℝ), Tendsto (fun i => ∫d,g d*f d ∂μ i) l (𝓝 (∫d,g d ∂law))
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_Definitions
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

attribute [local instance] OAI.StandardMapEntropy.realTangentCompTriple
noncomputable def standardInverseDerivative (k : ℝ) (z : Torus) : ℂ →L[ℝ] ℂ :=
  tangentCoordinates.comp
    ((transferStepInv (torusPotential k (inverseMap k z).1)).comp tangentCoordinates)

noncomputable def complexProjection (z : ℂ) : Torus := ((z.re : Circle), (z.im : Circle))

end StandardMapEntropy
end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_Subadditive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace BoundedSubadditive

variable {X : Type*}

noncomputable def excess (T : X → X) (h : X → ℝ) (δ : ℝ) : ℕ → X → ℝ
  | 0, _ => 0
  | n + 1, x => max 0 (h x - δ + excess T h δ n (T x))

structure Cocycle (X : Type*) [MeasurableSpace X] (T : X → X) where
  value : ℕ → X → ℝ
  measurable : ∀ n, Measurable (value n)
  nonneg : ∀ n x, 0 ≤ value n x
  le_time : ∀ n x, value n x ≤ n
  subadd : ∀ m n x, value (m + n) x ≤ value m x + value n (T^[m] x)
  shift_bound : ∀ n x, |value n (T x) - value n x| ≤ 2

namespace Cocycle
variable [MeasurableSpace X] {T : X → X} (f : Cocycle X T)

noncomputable def average (n : ℕ) (x : X) : ℝ := f.value n x / (n : ℝ)
noncomputable def lowerRate (x : X) : ℝ := liminf (fun n => f.average n x) atTop
noncomputable def upperRate (x : X) : ℝ := limsup (fun n => f.average n x) atTop

noncomputable def badSet (ε : ℝ) (N : ℕ) : Set X :=
  (⋃ n ∈ Set.Ioc 0 N, {x | f.value n x ≤ (n : ℝ) * (f.lowerRate x + ε)})ᶜ

noncomputable def badObservation (ε : ℝ) (N : ℕ) : X → ℝ :=
  (f.badSet ε N).indicator (fun _ => 1)

end Cocycle
end BoundedSubadditive

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_DerivativeGrowth
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

@[simp] lemma tangentCoordinates_re (z : ℂ) : (tangentCoordinates z).re = z.re := rfl
@[simp] lemma tangentCoordinates_im (z : ℂ) : (tangentCoordinates z).im = z.re-z.im := rfl
@[simp] lemma tangentCoordinates_involutive (z : ℂ) :
    tangentCoordinates (tangentCoordinates z) = z := by
  apply Complex.ext <;> simp

lemma tangentCoordinates_wedge (z w : ℂ) :
    wedge (tangentCoordinates z) (tangentCoordinates w) = -wedge z w := by
  simp only [wedge, tangentCoordinates_re, tangentCoordinates_im]
  ring

@[simp] lemma standardDerivative_re (k : ℝ) (z : Torus) (v : ℂ) :
    (standardDerivative k z v).re = (torusPotential k z.1-1)*v.re+v.im := by
  simp only [standardDerivative, ContinuousLinearMap.comp_apply,
    tangentCoordinates_re, tangentCoordinates_im, transferStep_re]
  ring
@[simp] lemma standardDerivative_im (k : ℝ) (z : Torus) (v : ℂ) :
    (standardDerivative k z v).im = (torusPotential k z.1-2)*v.re+v.im := by
  simp only [standardDerivative, ContinuousLinearMap.comp_apply,
    tangentCoordinates_re, tangentCoordinates_im, transferStep_re, transferStep_im]
  ring

lemma standardDerivative_area (k : ℝ) (z : Torus) :
    PlaneAreaPreserving (standardDerivative k z) := by
  intro v w
  simp only [standardDerivative, ContinuousLinearMap.comp_apply, tangentCoordinates_wedge]
  rw [transferStep_area _ _ _, tangentCoordinates_wedge, neg_neg]

lemma standardInverseDerivative_area (k : ℝ) (z : Torus) :
    PlaneAreaPreserving (standardInverseDerivative k z) := by
  intro v w
  simp only [standardInverseDerivative, ContinuousLinearMap.comp_apply, tangentCoordinates_wedge]
  rw [transferStepInv_area _ _ _, tangentCoordinates_wedge, neg_neg]

lemma standardDerivativeProduct_area (k : ℝ) (z : Torus) (n : ℕ) :
    PlaneAreaPreserving (standardDerivativeProduct k z n) := by
  induction n with
  | zero => intro v w; rfl
  | succ n ih => exact (standardDerivative_area k _).comp ih

lemma continuous_inverseMap (k : ℝ) : Continuous (inverseMap k) :=
  (continuous_fst.sub continuous_snd).prodMk
    (continuous_snd.sub ((continuous_kick k).comp (continuous_fst.sub continuous_snd)))

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_InverseLyapunov
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

def standardReversal (z : Torus) : Torus :=
  recurrenceCoordinates (recurrenceCoordinates z).swap

noncomputable def tangentReversal : ℂ →L[ℝ] ℂ :=
  tangentCoordinates.comp (planeSwap.comp tangentCoordinates)

@[simp] lemma standardReversal_fst (z : Torus) : (standardReversal z).1 = z.1-z.2 := rfl
@[simp] lemma standardReversal_snd (z : Torus) : (standardReversal z).2 = -z.2 := by
  simp [standardReversal, recurrenceCoordinates]
@[simp] lemma tangentReversal_re (z : ℂ) : (tangentReversal z).re = z.re-z.im := rfl
@[simp] lemma tangentReversal_im (z : ℂ) : (tangentReversal z).im = -z.im := by
  simp [tangentReversal]
@[simp] lemma tangentReversal_involutive (z : ℂ) : tangentReversal (tangentReversal z)=z := by
  apply Complex.ext <;> simp

noncomputable def standardInverseDerivativeProduct (k : ℝ) (z : Torus) : ℕ → (ℂ →L[ℝ] ℂ)
  | 0 => ContinuousLinearMap.id ℝ ℂ
  | n+1 => (standardInverseDerivative k ((inverseMap k)^[n] z)).comp
      (standardInverseDerivativeProduct k z n)

lemma standardInverseDerivativeProduct_area (k : ℝ) (z : Torus) (n : ℕ) :
    PlaneAreaPreserving (standardInverseDerivativeProduct k z n) := by
  induction n with
  | zero => intro v w; rfl
  | succ n ih => exact (standardInverseDerivative_area k _).comp ih

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

namespace PlaneLyapunov

abbrev UnitPlane := {v : ℂ // ‖v‖ = 1}
instance instNonemptyUnitPlane : Nonempty UnitPlane := ⟨⟨1, by simp⟩⟩

noncomputable def denseUnit : ℕ → UnitPlane := TopologicalSpace.denseSeq UnitPlane

lemma exists_approx_slow (A : ℂ →L[ℝ] ℂ) (hA : PlaneAreaPreserving A) :
    ∃ j : ℕ, ‖A (denseUnit j)‖ < 2/‖A‖ := by
  obtain ⟨a,ha,_,_,hb,hD⟩ := hA.singular_pair
  apply (TopologicalSpace.denseRange_denseSeq UnitPlane).exists_mem_open
    (isOpen_lt ((A.continuous.comp continuous_subtype_val).norm) continuous_const)
  refine ⟨⟨quarterTurn a, by simpa only [norm_quarterTurn] using ha⟩, ?_⟩
  change ‖A (quarterTurn a)‖ < 2/‖A‖
  rw [hb, inv_eq_one_div]
  exact div_lt_div_of_pos_right (by norm_num) (lt_of_lt_of_le zero_lt_one hD)

noncomputable def approxSlow (A : ℂ →L[ℝ] ℂ) (hA : PlaneAreaPreserving A) : ℂ :=
  (denseUnit (Nat.find (exists_approx_slow A hA))).val

noncomputable def stableCandidate (A : ℕ → ℂ →L[ℝ] ℂ)
    (hA : ∀ n, PlaneAreaPreserving (A n)) : ℂ := by
  let p := liminf (fun n => (approxSlow (A n) (hA n)).re^2) atTop
  let q := liminf (fun n => (approxSlow (A n) (hA n)).re*(approxSlow (A n) (hA n)).im) atTop
  exact if p=0 then Complex.I else ⟨p,q⟩

lemma stableCandidate_ne_zero (A : ℕ → ℂ →L[ℝ] ℂ)
    (hA : ∀ n, PlaneAreaPreserving (A n)) : stableCandidate A hA ≠ 0 := by
  classical
  unfold stableCandidate
  dsimp only
  split_ifs with h
  · exact Complex.I_ne_zero
  · intro he
    exact h (congrArg Complex.re he)

noncomputable def stableUnit (A : ℕ → ℂ →L[ℝ] ℂ)
    (hA : ∀ n, PlaneAreaPreserving (A n)) : ℂ :=
  (‖stableCandidate A hA‖⁻¹ : ℝ) • stableCandidate A hA

lemma norm_stableUnit (A : ℕ → ℂ →L[ℝ] ℂ)
    (hA : ∀ n, PlaneAreaPreserving (A n)) : ‖stableUnit A hA‖=1 := by
  rw [stableUnit, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (stableCandidate_ne_zero A hA))

end PlaneLyapunov
end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable def stableVector (k : ℝ) (z : Torus) : ℂ :=
  PlaneLyapunov.stableUnit (standardDerivativeProduct k z) (standardDerivativeProduct_area k z)
noncomputable def unstableVector (k : ℝ) (z : Torus) : ℂ :=
  PlaneLyapunov.stableUnit (standardInverseDerivativeProduct k z) (standardInverseDerivativeProduct_area k z)

@[simp] lemma norm_stableVector (k : ℝ) (z : Torus) : ‖stableVector k z‖=1 :=
  PlaneLyapunov.norm_stableUnit _ _
@[simp] lemma norm_unstableVector (k : ℝ) (z : Torus) : ‖unstableVector k z‖=1 :=
  PlaneLyapunov.norm_stableUnit _ _

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_TransverseLines
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

noncomputable def standardMap_measurableEquiv (k : ℝ) : Torus ≃ᵐ Torus where
  toFun := standardMap k
  invFun := inverseMap k
  left_inv := inverseMap_standardMap k
  right_inv := standardMap_inverseMap k
  measurable_toFun := (continuous_standardMap k).measurable
  measurable_invFun := (continuous_inverseMap k).measurable

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace PlaneLyapunov

noncomputable def energy (A : ℕ → ℂ →L[ℝ] ℂ) (χ : ℝ) (v : ℂ) : ℝ :=
  ∑' n : ℕ, ‖A n v‖^2 * Real.exp (2*χ*(n : ℝ))

end PlaneLyapunov

noncomputable def stableEnergy (k χ : ℝ) (z : Torus) : ℝ :=
  PlaneLyapunov.energy (standardDerivativeProduct k z) χ (stableVector k z)
noncomputable def unstableEnergy (k χ : ℝ) (z : Torus) : ℝ :=
  PlaneLyapunov.energy (standardInverseDerivativeProduct k z) χ (unstableVector k z)

noncomputable def stableScale (k χ : ℝ) (z : Torus) : ℝ := Real.sqrt (max 1 (stableEnergy k χ z))
noncomputable def unstableScale (k χ : ℝ) (z : Torus) : ℝ := Real.sqrt (max 1 (unstableEnergy k χ z))

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_BoundedTempering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace BoundedSubadditive
variable {X : Type*} [MeasurableSpace X] {T : X → X}

noncomputable def observationCocycle (g : X → ℝ) (hT : Measurable T) (hg : Measurable g)
    (h0 : ∀ x, 0≤g x) (h1 : ∀ x, g x≤1) : Cocycle X T where
  value := birkhoffSum T g
  measurable n := Finset.measurable_sum _ (fun i _ => hg.comp (hT.iterate i))
  nonneg n x := Finset.sum_nonneg fun i _ => h0 _
  le_time n x := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun i _ => h1 _
      _ = n := by simp
  subadd m n x := (birkhoffSum_add T g m n x).le
  shift_bound n x := by
    rw [birkhoffSum_apply_sub_birkhoffSum]
    exact abs_le.mpr ⟨by linarith [h0 (T^[n] x), h1 x], by linarith [h1 (T^[n] x), h0 x]⟩

end BoundedSubadditive

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable def planeFrame (s u : ℂ) (a b : ℝ) : ℂ →L[ℝ] ℂ :=
  (Complex.reCLM.smulRight ((2*a)⁻¹ • s)) +
    (Complex.imCLM.smulRight ((2*b)⁻¹ • u))

noncomputable def planeCoframe (s u : ℂ) (a b : ℝ) : ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => ⟨2*a*wedge v u / wedge s u, 2*b*wedge s v / wedge s u⟩
      map_add' := by intro v w; apply Complex.ext <;> simp [wedge] <;> ring
      map_smul' := by intro t v; apply Complex.ext <;> simp [wedge] <;> ring }

noncomputable def lyapunovFrame (k χ : ℝ) (z : Torus) : ℂ →L[ℝ] ℂ :=
  planeFrame (stableVector k z) (unstableVector k z) (stableScale k χ z) (unstableScale k χ z)
noncomputable def lyapunovCoframe (k χ : ℝ) (z : Torus) : ℂ →L[ℝ] ℂ :=
  planeCoframe (stableVector k z) (unstableVector k z) (stableScale k χ z) (unstableScale k χ z)

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_MeasurableFrame
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

def orbit (e : X ≃ᵐ X) (n : ℤ) (x : X) : X := (e.toEquiv ^ n) x
@[simp] lemma orbit_zero (e : X ≃ᵐ X) (x : X) : orbit e 0 x=x := by simp [orbit]
@[simp] lemma orbit_one (e : X ≃ᵐ X) (x : X) : orbit e 1 x=e x := by simp [orbit]
@[simp] lemma orbit_neg_one (e : X ≃ᵐ X) (x : X) : orbit e (-1) x=e.symm x := by simp [orbit]

noncomputable def weight (ε : ℝ) (n : ℤ) : ℝ := Real.exp (-ε*|(n : ℝ)|)
noncomputable def control (e : X ≃ᵐ X) (c : X → ℝ) (ε : ℝ) (x : X) : ℝ :=
  ∑' n : ℤ, c (orbit e n x)*weight ε n
noncomputable def radius (e : X ≃ᵐ X) (c : X → ℝ) (ε : ℝ) (x : X) : ℝ :=
  (1+control e c ε x)⁻¹

end TemperedControl
end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable def diagonalPlane (α β : ℝ) : ℂ →L[ℝ] ℂ :=
  Complex.reCLM.smulRight (α : ℂ) + Complex.imCLM.smulRight (β*Complex.I)

noncomputable def stableMultiplier (k χ : ℝ) (z : Torus) : ℝ :=
  dot (stableVector k (standardMap k z)) (standardDerivative k z (stableVector k z)) *
    stableScale k χ (standardMap k z) / stableScale k χ z
noncomputable def unstableMultiplier (k χ : ℝ) (z : Torus) : ℝ :=
  dot (unstableVector k (standardMap k z)) (standardDerivative k z (unstableVector k z)) *
    unstableScale k χ (standardMap k z) / unstableScale k χ z

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

@[simp] lemma standardMap_measurableEquiv_apply (k : ℝ) (z : Torus) :
    standardMap_measurableEquiv k z=standardMap k z := rfl
@[simp] lemma standardMap_measurableEquiv_symm_apply (k : ℝ) (z : Torus) :
    (standardMap_measurableEquiv k).symm z=inverseMap k z := rfl

noncomputable def chartControl (k χ : ℝ) (z : Torus) : ℝ := max 1 ‖lyapunovCoframe k χ z‖
noncomputable def chartRadius (k χ ε : ℝ) : Torus → ℝ :=
  TemperedControl.radius (standardMap_measurableEquiv k) (chartControl k χ) ε

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Stable_SmoothRemainder
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

abbrev Plane := ℝ × ℝ
abbrev Sequence := BoundedContinuousFunction ℕ Plane

structure Recurrence (ℓ δ : ℝ≥0) where
  a : ℕ → ℝ
  b : ℕ → ℝ
  remainder : ℕ → Plane → Plane
  stable_bound : ∀ n, |a n|≤ℓ
  inverse_bound : ∀ n, |(b n)⁻¹|≤ℓ
  b_ne : ∀ n, b n≠0
  lipschitz : ∀ n, LipschitzWith δ (remainder n)
  zero : ∀ n, remainder n 0=0

variable {ℓ δ : ℝ≥0}

def Recurrence.step (r : Recurrence ℓ δ) (n : ℕ) (v : Plane) : Plane :=
  (r.a n*v.1+(r.remainder n v).1, r.b n*v.2+(r.remainder n v).2)

noncomputable def Recurrence.perronValue (r : Recurrence ℓ δ) (s : ℝ) (x : Sequence) (n : ℕ) : Plane :=
  ((match n with | 0 => s | m+1 => r.a m*(x m).1+(r.remainder m (x m)).1),
    (r.b n)⁻¹*((x (n+1)).2-(r.remainder n (x n)).2))

lemma point_sub_bound (x y : Sequence) (n : ℕ) : ‖x n-y n‖≤‖x-y‖ :=
  (x-y).norm_coe_le_norm n
lemma fst_sub_bound (x y : Sequence) (n : ℕ) : |(x n).1-(y n).1|≤‖x-y‖ :=
  (norm_fst_le (x n-y n)).trans (point_sub_bound x y n)
lemma snd_sub_bound (x y : Sequence) (n : ℕ) : |(x n).2-(y n).2|≤‖x-y‖ :=
  (norm_snd_le (x n-y n)).trans (point_sub_bound x y n)

lemma remainder_sub_bound (r : Recurrence ℓ δ) (x y : Sequence) (n : ℕ) :
    ‖r.remainder n (x n)-r.remainder n (y n)‖≤(δ : ℝ)*‖x-y‖ := by
  have hh := (r.lipschitz n).dist_le_mul (x n) (y n)
  rw [dist_eq_norm,dist_eq_norm] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (point_sub_bound x y n) δ.coe_nonneg)

lemma perronValue_sub_bound (r : Recurrence ℓ δ) (hℓ : ℓ≤1)
    (s t : ℝ) (x y : Sequence) (n : ℕ) :
    ‖r.perronValue s x n-r.perronValue t y n‖≤
      max |s-t| (((ℓ+δ : ℝ≥0) : ℝ)*‖x-y‖) := by
  have hδ : 0≤(δ : ℝ) := δ.coe_nonneg
  have hℓ0 : 0≤(ℓ : ℝ) := ℓ.coe_nonneg
  have hℓ1 : (ℓ : ℝ)≤1 := hℓ
  have hfst (m : ℕ) := (norm_fst_le (r.remainder m (x m)-r.remainder m (y m))).trans
    (remainder_sub_bound r x y m)
  have hsnd (m : ℕ) := (norm_snd_le (r.remainder m (x m)-r.remainder m (y m))).trans
    (remainder_sub_bound r x y m)
  rw [Prod.norm_def]
  apply max_le
  · cases n with
    | zero => exact le_max_left _ _
    | succ m =>
      change |r.a m*(x m).1+(r.remainder m (x m)).1-
        (r.a m*(y m).1+(r.remainder m (y m)).1)|≤_
      calc
        _ = |r.a m*((x m).1-(y m).1)+((r.remainder m (x m)).1-(r.remainder m (y m)).1)| := by congr 1; ring
        _ ≤ |r.a m| *|(x m).1-(y m).1| +|(r.remainder m (x m)).1-(r.remainder m (y m)).1| := by
          simpa only [abs_mul] using abs_add_le (r.a m*((x m).1-(y m).1))
            ((r.remainder m (x m)).1-(r.remainder m (y m)).1)
        _ ≤ (ℓ : ℝ)*‖x-y‖+(δ : ℝ)*‖x-y‖ := add_le_add
          (mul_le_mul (r.stable_bound m) (fst_sub_bound x y m) (abs_nonneg _) hℓ0) (hfst m)
        _ = ((ℓ+δ : ℝ≥0) : ℝ)*‖x-y‖ := by push_cast; ring
        _ ≤ _ := le_max_right _ _
  · change |(r.b n)⁻¹*((x (n+1)).2-(r.remainder n (x n)).2)-
      (r.b n)⁻¹*((y (n+1)).2-(r.remainder n (y n)).2)|≤_
    calc
      _ = |(r.b n)⁻¹| *|((x (n+1)).2-(y (n+1)).2)-
          ((r.remainder n (x n)).2-(r.remainder n (y n)).2)| := by rw [← abs_mul]; congr 1; ring
      _ ≤ |(r.b n)⁻¹| *(|(x (n+1)).2-(y (n+1)).2| +
          |(r.remainder n (x n)).2-(r.remainder n (y n)).2|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)
      _ ≤ (ℓ : ℝ)*(‖x-y‖+(δ : ℝ)*‖x-y‖) := mul_le_mul (r.inverse_bound n)
        (add_le_add (snd_sub_bound x y (n+1)) (hsnd n)) (by positivity) hℓ0
      _ ≤ ((ℓ+δ : ℝ≥0) : ℝ)*‖x-y‖ := by
        have hh := mul_le_mul_of_nonneg_right hℓ1 (mul_nonneg hδ (norm_nonneg (x-y)))
        push_cast
        nlinarith
      _ ≤ _ := le_max_right _ _

@[simp] lemma perronValue_zero (r : Recurrence ℓ δ) (n : ℕ) : r.perronValue 0 0 n=0 := by
  cases n <;> simp [Recurrence.perronValue,r.zero]

lemma perronValue_norm_bound (r : Recurrence ℓ δ) (hℓ : ℓ≤1) (s : ℝ) (x : Sequence) (n : ℕ) :
    ‖r.perronValue s x n‖≤ max |s| (((ℓ+δ : ℝ≥0) : ℝ)*‖x‖) := by
  simpa only [perronValue_zero,sub_zero] using perronValue_sub_bound r hℓ s 0 x 0 n

noncomputable def Recurrence.perron (r : Recurrence ℓ δ) (hℓ : ℓ≤1) (s : ℝ) (x : Sequence) : Sequence :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (r.perronValue s x)
    (max |s| (((ℓ+δ : ℝ≥0) : ℝ)*‖x‖)) (perronValue_norm_bound r hℓ s x)

@[simp] lemma perron_apply (r : Recurrence ℓ δ) (hℓ : ℓ≤1) (s : ℝ) (x : Sequence) (n : ℕ) :
    r.perron hℓ s x n=r.perronValue s x n := rfl

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy.NonlinearStable
open Filter
open scoped Topology NNReal
variable {ℓ δ : ℝ≥0}

noncomputable def Sequence.tail (x : Sequence) (m : ℕ) : Sequence :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun n => x (m+n)) ‖x‖
    (fun n => x.norm_coe_le_norm (m+n))
@[simp] lemma tail_apply (x : Sequence) (m n : ℕ) : x.tail m n=x (m+n) := rfl

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal

abbrev RealPlane := ℝ × ℝ

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Entropy_LiftGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.Entropy
open Set Finset
open scoped BigOperators

noncomputable def shannon {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  ∑ a, Real.negMulLog (p a)

lemma negMulLog_le_cross {p q : ℝ} (hp : 0≤p) (hq : 0≤q) (hs : p≠0 → q≠0) :
    Real.negMulLog p≤ -p*Real.log q+q-p := by
  by_cases he : p=0
  · simp only [he,Real.negMulLog_zero,neg_zero,zero_mul,sub_zero,zero_add]
    exact hq
  have hp' : 0<p := lt_of_le_of_ne hp (Ne.symm he)
  have hq' : 0<q := lt_of_le_of_ne hq (Ne.symm (hs he))
  have hh := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hq' hp')) hp
  rw [Real.log_div hq'.ne' hp'.ne'] at hh
  have hc : p*(q/p-1)=q-p := by field_simp
  rw [hc] at hh
  dsimp [Real.negMulLog]
  nlinarith

lemma shannon_le_cross {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ a, 0≤p a) (hq : ∀ a, 0≤q a) (hs : ∀ a, p a≠0 → q a≠0)
    (hm : ∑ a,q a≤∑ a,p a) :
    shannon p≤ -∑ a,p a*Real.log (q a) := by
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun a _ => negMulLog_le_cross (hp a) (hq a) (hs a))
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,neg_mul,Finset.sum_neg_distrib] at hh
  dsimp [shannon]
  linarith

lemma matrix_row_nonneg {α β : Type*} [Fintype α] [Fintype β]
    (p : α → β → ℝ) (hp : ∀ a b, 0≤p a b) (a : α) : 0≤∑ b,p a b :=
  Finset.sum_nonneg (fun b _ => hp a b)
lemma matrix_col_nonneg {α β : Type*} [Fintype α] [Fintype β]
    (p : α → β → ℝ) (hp : ∀ a b, 0≤p a b) (b : β) : 0≤∑ a,p a b :=
  Finset.sum_nonneg (fun a _ => hp a b)
lemma matrix_le_row {α β : Type*} [Fintype α] [Fintype β]
    (p : α → β → ℝ) (hp : ∀ a b, 0≤p a b) (a : α) (b : β) : p a b≤∑ j,p a j :=
  Finset.single_le_sum (fun j _ => hp a j) (Finset.mem_univ b)
lemma matrix_le_col {α β : Type*} [Fintype α] [Fintype β]
    (p : α → β → ℝ) (hp : ∀ a b, 0≤p a b) (a : α) (b : β) : p a b≤∑ i,p i b :=
  Finset.single_le_sum (fun i _ => hp i b) (Finset.mem_univ a)

lemma matrix_subadd {α β : Type*} [Fintype α] [Fintype β]
    (p : α → β → ℝ) (hp : ∀ a b, 0≤p a b) :
    shannon (fun ab : α×β => p ab.1 ab.2)≤
      shannon (fun a => ∑ b,p a b)+shannon (fun b => ∑ a,p a b)-
        Real.negMulLog (∑ a,∑ b,p a b) := by
  let A : α → ℝ := fun a => ∑ b,p a b
  let B : β → ℝ := fun b => ∑ a,p a b
  let T : ℝ := ∑ a,∑ b,p a b
  have hA := matrix_row_nonneg p hp
  have hB := matrix_col_nonneg p hp
  have hT : 0≤T := Finset.sum_nonneg (fun a _ => hA a)
  have hpT (a : α) (b : β) : p a b≤T := (matrix_le_row p hp a b).trans
    (Finset.single_le_sum (fun i _ => hA i) (Finset.mem_univ a))
  by_cases he : T=0
  · have hz (a : α) (b : β) : p a b=0 := le_antisymm (by simpa only [he] using hpT a b) (hp a b)
    simp only [shannon,hz,Finset.sum_const_zero,Real.negMulLog_zero,add_zero,sub_zero,le_refl]
  have hT' : 0<T := lt_of_le_of_ne hT (Ne.symm he)
  let q : α×β → ℝ := fun ab => A ab.1*B ab.2/T
  have hq (ab : α×β) : 0≤q ab := div_nonneg (mul_nonneg (hA ab.1) (hB ab.2)) hT
  have hs (ab : α×β) (hh : p ab.1 ab.2≠0) : q ab≠0 := by
    have hpos : 0<p ab.1 ab.2 := lt_of_le_of_ne (hp _ _) (Ne.symm hh)
    exact div_ne_zero (mul_ne_zero (ne_of_gt (hpos.trans_le (matrix_le_row p hp _ _)))
      (ne_of_gt (hpos.trans_le (matrix_le_col p hp _ _)))) he
  have hmass : ∑ ab : α×β,q ab=∑ ab : α×β,p ab.1 ab.2 := by
    simp only [q,Fintype.sum_prod_type,←Finset.sum_div,←Finset.mul_sum,←Finset.sum_mul]
    have hsumA : ∑ a,A a=T := rfl
    have hsumB : ∑ b,B b=T := by dsimp [B,T]; exact Finset.sum_comm
    rw [hsumA,hsumB,mul_div_cancel_right₀ _ he]
  have hh := shannon_le_cross (fun ab : α×β => p ab.1 ab.2) q (fun ab => hp ab.1 ab.2) hq hs hmass.le
  have hlog (a : α) (b : β) : p a b*Real.log (q (a,b))=
      p a b*Real.log (A a)+p a b*Real.log (B b)-p a b*Real.log T := by
    by_cases hz : p a b=0
    · simp only [hz,zero_mul,add_zero,sub_zero]
    have hpos : 0<p a b := lt_of_le_of_ne (hp a b) (Ne.symm hz)
    have ha : A a≠0 := ne_of_gt (hpos.trans_le (matrix_le_row p hp a b))
    have hb : B b≠0 := ne_of_gt (hpos.trans_le (matrix_le_col p hp a b))
    rw [show q (a,b)=A a*B b/T from rfl,Real.log_div (mul_ne_zero ha hb) he,Real.log_mul ha hb]
    ring
  have hsum1 : ∑ a,∑ b,p a b*Real.log (A a)=∑ a,A a*Real.log (A a) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [←Finset.sum_mul]
  have hsum2 : ∑ a,∑ b,p a b*Real.log (B b)=∑ b,B b*Real.log (B b) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [←Finset.sum_mul]
  have hsum3 : ∑ a,∑ b,p a b*Real.log T=T*Real.log T := by simp only [←Finset.sum_mul]; rfl
  simp only [Fintype.sum_prod_type,hlog,Finset.sum_sub_distrib,Finset.sum_add_distrib] at hh
  rw [hsum1,hsum2,hsum3] at hh
  dsimp only [shannon,Real.negMulLog] at hh ⊢
  simp only [neg_mul,Finset.sum_neg_distrib] at hh ⊢
  change _≤ -(∑ a,A a*Real.log (A a)) + -(∑ b,B b*Real.log (B b)) - (-(T*Real.log T))
  linarith

end StandardMapEntropy.Entropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Entropy_ObservableEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]

noncomputable def mass (p : Ω → α) (a : α) : ℝ := (μ (p ⁻¹' {a})).toReal
noncomputable def obs (p : Ω → α) : ℝ := shannon (mass μ p)
omit [IsFiniteMeasure μ] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma mass_nonneg (p : Ω → α) (a : α) : 0 ≤ mass μ p a := ENNReal.toReal_nonneg
omit [MeasurableSpace Ω] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma fiber_disjoint (p : Ω → α) : Pairwise (Function.onFun Disjoint (fun a => p ⁻¹' {a})) := by
  intro a b hab
  exact Set.disjoint_left.mpr (fun x hxa hxb => hab (hxa.symm.trans hxb))
lemma mass_sum (p : Ω → α) (hp : Measurable p) : ∑ a,mass μ p a=(μ univ).toReal := by
  have he : (⋃ a : α,p ⁻¹' {a})=univ := by ext x; simp only [mem_iUnion,mem_preimage,mem_singleton_iff,exists_eq',mem_univ]
  rw [←he,measure_iUnion (fiber_disjoint p) (fun a => hp (measurableSet_singleton a)),tsum_fintype,
    ENNReal.toReal_sum (fun a _ => measure_ne_top μ _)]
  rfl
omit [Fintype α] in
lemma mass_joint_row (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) (a : α) :
    mass μ p a=∑ b,mass μ (fun x => (p x,q x)) (a,b) := by
  have he : p ⁻¹' {a}=⋃ b : β,(fun x => (p x,q x)) ⁻¹' {(a,b)} := by
    ext x
    simp only [mem_preimage,mem_singleton_iff,Prod.mk.injEq,mem_iUnion,exists_and_left,exists_eq',and_true]
  have hd : Pairwise (Function.onFun Disjoint (fun b : β => (fun x => (p x,q x)) ⁻¹' {(a,b)})) := by
    intro b c hbc
    exact (fiber_disjoint (fun x => (p x,q x))) (by intro h; exact hbc (Prod.mk.inj h).2)
  unfold mass
  rw [he,measure_iUnion hd (fun b => (hp.prodMk hq) (measurableSet_singleton _)),tsum_fintype,
    ENNReal.toReal_sum (fun b _ => measure_ne_top μ _)]
omit [IsFiniteMeasure μ] [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma mass_joint_swap (p : Ω → α) (q : Ω → β) (a : α) (b : β) :
    mass μ (fun x => (p x,q x)) (a,b)=mass μ (fun x => (q x,p x)) (b,a) := by
  unfold mass
  congr 2
  ext x
  simp only [mem_preimage,mem_singleton_iff,Prod.mk.injEq,and_comm]
omit [Fintype β] in
lemma mass_joint_col (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) (b : β) :
    mass μ q b=∑ a,mass μ (fun x => (p x,q x)) (a,b) := by
  rw [mass_joint_row μ q p hq hp]
  exact Finset.sum_congr rfl (fun a _ => mass_joint_swap μ q p b a)
lemma obs_pair_subadd (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) :
    obs μ (fun x => (p x,q x)) ≤ obs μ p+obs μ q-Real.negMulLog (μ univ).toReal := by
  have h := matrix_subadd (fun a b => mass μ (fun x => (p x,q x)) (a,b))
    (fun a b => mass_nonneg μ _ _)
  simpa only [obs,Prod.mk.eta,←mass_joint_row μ p q hp hq,←mass_joint_col μ p q hp hq,mass_sum μ p hp] using h
lemma obs_pair_subadd_prob [IsProbabilityMeasure μ] (p : Ω → α) (q : Ω → β)
    (hp : Measurable p) (hq : Measurable q) : obs μ (fun x => (p x,q x)) ≤ obs μ p+obs μ q := by
  simpa only [measure_univ,ENNReal.toReal_one,Real.negMulLog_one,sub_zero] using obs_pair_subadd μ p q hp hq

omit [IsFiniteMeasure μ] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma obs_equiv (p : Ω → α) (e : α ≃ β) : obs μ (e ∘ p)=obs μ p := by
  have he (a : α) : mass μ (e ∘ p) (e a)=mass μ p a := by
    unfold mass
    congr 2
    ext x
    simp only [mem_preimage,mem_singleton_iff,Function.comp_apply,e.injective.eq_iff]
  unfold obs shannon
  rw [←e.sum_comp]
  simp only [he]

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
variable {α β γ ζ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype ζ]
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace ζ]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ] [MeasurableSingletonClass ζ]

noncomputable def cond (p : Ω → α) (q : Ω → β) : ℝ := obs μ (fun x => (p x,q x))-obs μ q

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β : Type*} [Fintype α] [Fintype β]
variable [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]

omit [IsProbabilityMeasure μ] [Fintype α] in
lemma mass_comp_preserving (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α)
    (hp : Measurable p) (a : α) : mass μ (p ∘ f) a=mass μ p a := by
  unfold mass
  rw [Set.preimage_comp,hf.measure_preimage (hp (measurableSet_singleton a)).nullMeasurableSet]
omit [IsProbabilityMeasure μ] in
lemma obs_comp_preserving (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α)
    (hp : Measurable p) : obs μ (p ∘ f)=obs μ p := by
  simp only [obs,shannon,mass_comp_preserving μ f hf p hp]

def word (f : Ω → Ω) (p : Ω → α) (n : ℕ) (x : Ω) : Fin n → α := fun i => p (f^[i.val] x)
omit [Fintype α] [MeasurableSingletonClass α] in
lemma word_measurable (f : Ω → Ω) (hf : Measurable f) (p : Ω → α) (hp : Measurable p) (n : ℕ) :
    Measurable (word f p n) := Measurable.of_eval (fun i => hp.comp (hf.iterate i.val))
noncomputable def wordSplit (n m : ℕ) : (Fin (n+m) → α) ≃ (Fin n → α)×(Fin m → α) :=
  ((Equiv.piCongrLeft (fun _ : Fin (n+m) => α) finSumFinEquiv).symm).trans
    (Equiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => α))
omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma wordSplit_apply (n m : ℕ) (v : Fin (n+m) → α) :
    wordSplit n m v=(fun i => v (Fin.castAdd m i),fun i => v (Fin.natAdd n i)) := by
  simp only [wordSplit,Equiv.trans_apply,Equiv.sumPiEquivProdPi_apply,
    Equiv.piCongrLeft_symm_apply,finSumFinEquiv_apply_left,finSumFinEquiv_apply_right]
omit [MeasurableSpace Ω] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma word_split (f : Ω → Ω) (p : Ω → α) (n m : ℕ) (x : Ω) :
    wordSplit n m (word f p (n+m) x)=(word f p n x,word f p m (f^[n] x)) := by
  rw [wordSplit_apply]
  apply Prod.ext
  · rfl
  · funext i
    simp only [word,Fin.val_natAdd,Nat.add_comm n i.val,Function.iterate_add_apply]
omit [IsProbabilityMeasure μ] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma obs_word_split (f : Ω → Ω) (p : Ω → α) (n m : ℕ) :
    obs μ (word f p (n+m))=obs μ (fun x => (word f p n x,word f p m (f^[n] x))) := by
  have h := obs_equiv μ (word f p (n+m)) (wordSplit n m)
  simpa only [Function.comp_def,word_split] using h.symm
lemma obs_word_subadd (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (hp : Measurable p) :
    Subadditive (fun n => obs μ (word f p n)) := by
  intro n m
  dsimp only
  rw [obs_word_split]
  have h := obs_pair_subadd_prob μ (word f p n) ((word f p m) ∘ f^[n])
    (word_measurable f hf.measurable p hp n) ((word_measurable f hf.measurable p hp m).comp (hf.measurable.iterate n))
  rw [obs_comp_preserving μ (f^[n]) (hf.iterate n) _ (word_measurable f hf.measurable p hp m)] at h
  exact h

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β : Type*} [Fintype α] [Fintype β]
variable [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]

noncomputable def rate (f : Ω → Ω) (p : Ω → α) : ℝ :=
  sInf ((fun n : ℕ => obs μ (word f p n)/(n : ℝ)) '' Ici 1)

end StandardMapEntropy.Entropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Stable_LocalStable
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

noncomputable def unitClip (x : ℝ) : ℝ := max (min x 1) (-1)
lemma abs_unitClip_le (x : ℝ) : |unitClip x|≤1 := by
  rw [abs_le]
  exact ⟨le_max_right _ _,max_le (min_le_right _ _) (by norm_num)⟩
lemma unitClip_eq {x : ℝ} (hx : |x|≤1) : unitClip x=x := by
  rw [abs_le] at hx
  simp only [unitClip,min_eq_left hx.2,max_eq_left hx.1]
lemma unitClip_lipschitz : LipschitzWith 1 unitClip :=
  (LipschitzWith.id.min_const 1).max_const (-1)

noncomputable def planeClip (v : Plane) : Plane := (unitClip v.1,unitClip v.2)
lemma norm_planeClip_le (v : Plane) : ‖planeClip v‖≤1 :=
  max_le (abs_unitClip_le _) (abs_unitClip_le _)
lemma planeClip_eq {v : Plane} (hv : ‖v‖≤1) : planeClip v=v := by
  exact Prod.ext (unitClip_eq ((norm_fst_le v).trans hv)) (unitClip_eq ((norm_snd_le v).trans hv))
@[simp] lemma planeClip_zero : planeClip 0=0 := planeClip_eq (by simp)
lemma planeClip_lipschitz : LipschitzWith 1 planeClip := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one,one_mul,Prod.dist_eq,planeClip]
  have h1 := unitClip_lipschitz.dist_le_mul v.1 w.1
  have h2 := unitClip_lipschitz.dist_le_mul v.2 w.2
  simp only [NNReal.coe_one,one_mul] at h1 h2
  exact max_le_max h1 h2

structure LocalRecurrence (ℓ δ : ℝ≥0) where
  a : ℕ → ℝ
  b : ℕ → ℝ
  remainder : ℕ → Plane → Plane
  stable_bound : ∀ n, |a n|≤ℓ
  inverse_bound : ∀ n, |(b n)⁻¹|≤ℓ
  b_ne : ∀ n, b n≠0
  local_lipschitz : ∀ n v w, ‖v‖≤1 → ‖w‖≤1 →
    ‖remainder n v-remainder n w‖≤(δ : ℝ)*‖v-w‖
  zero : ∀ n, remainder n 0=0

variable {ℓ δ : ℝ≥0}
def LocalRecurrence.step (r : LocalRecurrence ℓ δ) (n : ℕ) (v : Plane) : Plane :=
  (r.a n*v.1+(r.remainder n v).1,r.b n*v.2+(r.remainder n v).2)
noncomputable def LocalRecurrence.extend (r : LocalRecurrence ℓ δ) : Recurrence ℓ δ where
  a := r.a
  b := r.b
  remainder n v := r.remainder n (planeClip v)
  stable_bound := r.stable_bound
  inverse_bound := r.inverse_bound
  b_ne := r.b_ne
  lipschitz n := LipschitzWith.of_dist_le_mul fun v w => by
    have hh := r.local_lipschitz n (planeClip v) (planeClip w) (norm_planeClip_le v) (norm_planeClip_le w)
    have he := planeClip_lipschitz.dist_le_mul v w
    simp only [dist_eq_norm,NNReal.coe_one,one_mul] at he ⊢
    exact hh.trans (mul_le_mul_of_nonneg_left he δ.coe_nonneg)
  zero n := by rw [planeClip_zero,r.zero]

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy.NonlinearStable
open Filter
open scoped Topology NNReal
variable {ℓ δ : ℝ≥0}

noncomputable def sndSequence (x : Sequence) : BoundedContinuousFunction ℕ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun n => (x n).2) ‖x‖
    (fun n => (norm_snd_le (x n)).trans (x.norm_coe_le_norm n))
@[simp] lemma sndSequence_apply (x : Sequence) (n : ℕ) : sndSequence x n=(x n).2 := rfl

end StandardMapEntropy.NonlinearStable

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Stable_PerronStability
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

noncomputable def LocalRecurrence.linearized (r : LocalRecurrence ℓ δ)
    (D : ℕ → Plane →L[ℝ] Plane) (hD : ∀ n, ‖D n‖≤δ) : Recurrence ℓ δ where
  a := r.a
  b := r.b
  remainder n := D n
  stable_bound := r.stable_bound
  inverse_bound := r.inverse_bound
  b_ne := r.b_ne
  lipschitz n := LipschitzWith.of_dist_le_mul fun v w => by
    rw [dist_eq_norm,dist_eq_norm,←map_sub]
    exact ((D n).le_opNorm (v-w)).trans (mul_le_mul_of_nonneg_right (hD n) (norm_nonneg _))
  zero n := map_zero _

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy.NonlinearStable
open Filter Set
open scoped Topology NNReal
variable {ℓ δ : ℝ≥0}

noncomputable def sequenceEval (n : ℕ) : Sequence →L[ℝ] Plane :=
  ({ toFun := fun x => x n
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Sequence →ₗ[ℝ] Plane).mkContinuous 1
      (fun x => by change ‖x n‖≤1*‖x‖; simpa only [one_mul] using x.norm_coe_le_norm n)
@[simp] lemma sequenceEval_apply (n : ℕ) (x : Sequence) : sequenceEval n x=x n := rfl

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

@[simp] lemma standardReversal_involutive (z : Torus) : standardReversal (standardReversal z)=z := by
  apply Prod.ext <;> simp
@[simp] lemma complexProjection_tangentReversal (w : ℂ) :
    complexProjection (tangentReversal w)=standardReversal (complexProjection w) := by
  apply Prod.ext <;> simp [complexProjection]

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Entropy_SupportEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

noncomputable def errorObs (p q : Ω → α) (x : Ω) : Bool := by
  classical
  exact decide (p x≠q x)

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

noncomputable def complexRep (z : Torus) : ℂ := ⟨circleRep z.1,circleRep z.2⟩
@[simp] lemma complexProjection_complexRep (z : Torus) : complexProjection (complexRep z)=z := by
  ext <;> simp only [complexProjection,complexRep,coe_circleRep]

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Entropy_FineCharts
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

def FineRegular (k χ ε : ℝ) (z : Torus) : Prop :=
  wedge (stableVector k z) (unstableVector k z)≠0 ∧
  (lyapunovCoframe k χ (standardMap k z)).comp ((standardDerivative k z).comp (lyapunovFrame k χ z)) =
    diagonalPlane (stableMultiplier k χ z) (unstableMultiplier k χ z) ∧
  |stableMultiplier k χ z|≤Real.exp (-χ) ∧ Real.exp χ≤|unstableMultiplier k χ z| ∧
  chartRadius k χ ε z*‖lyapunovCoframe k χ z‖≤1 ∧
  Real.exp (-ε)*chartRadius k χ ε z ≤ chartRadius k χ ε (standardMap k z) ∧
  Real.exp (-ε)*chartRadius k χ ε (standardMap k z) ≤ chartRadius k χ ε z

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
namespace StandardMapEntropy.LocalCoding
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
variable {ι : Type*} [DecidableEq ι]

instance optionFinsetMeasurableSpace (A : Finset ι) : MeasurableSpace (Option A) := ⊤
instance optionFinsetMeasurableSingleton (A : Finset ι) : MeasurableSingletonClass (Option A) :=
  ⟨fun _ => trivial⟩

end StandardMapEntropy.LocalCoding

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
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal

abbrev LyapunovChartData := (ℂ →L[ℝ] ℂ) × (ℂ →L[ℝ] ℂ) × ℝ

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

def AffineGraphControl {X : Type*} (G : X → ℝ → ℝ) (I : Set ℝ) (K : ℝ) : Prop :=
  ∀ c∈I,∀ d∈I,∃ H : ℝ → ℝ,
    ContinuousOn H (range (fun a => G a c)) ∧ (∀ a,H (G a c)=G a d) ∧
    ∀ z∈range (fun a => G a c),∀ᶠ z' in 𝓝[range (fun a => G a c)] z,|H z'-H z|≤K*|z'-z|

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
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoundedSubadditive
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

structure ContinuousBirkhoffCode (T S : X → X) (μ : Measure X) where
  observation : ℕ → C(X,ℝ)
  dense : DenseRange observation
  value : X → ℕ → ℝ
  measurable : Measurable value
  invariant : ∀ x,value (T x)=value x
  generic : ∀ᵐ x ∂μ,∀ j : ℕ,
    Tendsto (fun n : ℕ => birkhoffSum T (observation j) n x/(n : ℝ)) atTop (𝓝 (value x j)) ∧
    Tendsto (fun n : ℕ => birkhoffSum S (observation j) n x/(n : ℝ)) atTop (𝓝 (value x j))
  integral : ∀ (A : Set X), MeasurableSet A → T ⁻¹' A=A → ∀ j : ℕ,
    ∫ x in A,value x j ∂μ=∫ x in A,observation j x ∂μ

end BoundedSubadditive

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
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

namespace AEPeriod
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def setoid : Setoid (Set X) where
  r A B := A =ᵐ[μ] B
  iseqv := ⟨fun _ => EventuallyEq.rfl,fun h => h.symm,fun h h' => h.trans h'⟩

abbrev Class := Quotient (setoid μ)
def ofSet (A : Set X) : Class μ := Quotient.mk _ A
lemma ofSet_eq_iff (A B : Set X) : ofSet μ A=ofSet μ B ↔ A =ᵐ[μ] B := Quotient.eq

variable {μ} {T : X → X}
def act (hT : QuasiMeasurePreserving T μ μ) : Class μ → Class μ :=
  Quotient.map (fun A => T ⁻¹' A) (fun _ _ h => hT.preimage_ae_eq h)

lemma act_ofSet (hT : QuasiMeasurePreserving T μ μ) (A : Set X) :
    act hT (ofSet μ A)=ofSet μ (T ⁻¹' A) := rfl
lemma iterate_act (hT : QuasiMeasurePreserving T μ μ) (A : Set X) (n : ℕ) :
    (act hT)^[n] (ofSet μ A)=ofSet μ ((T^[n]) ⁻¹' A) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,act_ofSet]
    congr 1

lemma periodic_iff (hT : QuasiMeasurePreserving T μ μ) (A : Set X) (n : ℕ) :
    Function.IsPeriodicPt (act hT) n (ofSet μ A) ↔ (T^[n]) ⁻¹' A =ᵐ[μ] A := by
  change (act hT)^[n] (ofSet μ A)=ofSet μ A ↔ _
  rw [iterate_act,ofSet_eq_iff]

lemma period_pos (hT : QuasiMeasurePreserving T μ μ) {A : Set X} {n : ℕ}
    (hn : 0 < n) (hinv : (T^[n]) ⁻¹' A =ᵐ[μ] A) :
    0<Function.minimalPeriod (act hT) (ofSet μ A) :=
  ((periodic_iff hT A n).mpr hinv).minimalPeriod_pos hn

lemma period_dvd (hT : QuasiMeasurePreserving T μ μ) {A : Set X} {n : ℕ}
    (hinv : (T^[n]) ⁻¹' A =ᵐ[μ] A) : Function.minimalPeriod (act hT) (ofSet μ A) ∣ n :=
  ((periodic_iff hT A n).mpr hinv).minimalPeriod_dvd

lemma period_preimage (hT : QuasiMeasurePreserving T μ μ) (A : Set X) :
    (T^[Function.minimalPeriod (act hT) (ofSet μ A)]) ⁻¹' A =ᵐ[μ] A :=
  (periodic_iff hT A _).mp (Function.isPeriodicPt_minimalPeriod _ _)

lemma preimage_mod (hT : QuasiMeasurePreserving T μ μ) (A : Set X) (j : ℕ) :
    (T^[j%Function.minimalPeriod (act hT) (ofSet μ A)]) ⁻¹' A =ᵐ[μ] (T^[j]) ⁻¹' A := by
  apply (ofSet_eq_iff μ _ _).mp
  rw [←iterate_act,←iterate_act]
  exact Function.iterate_mod_minimalPeriod_eq

lemma preimage_ne (hT : QuasiMeasurePreserving T μ μ) (A : Set X) {i j : ℕ}
    (hi : i<Function.minimalPeriod (act hT) (ofSet μ A))
    (hj : j<Function.minimalPeriod (act hT) (ofSet μ A)) (hij : i≠j) :
    ¬ ((T^[i]) ⁻¹' A =ᵐ[μ] (T^[j]) ⁻¹' A) := by
  intro he
  apply hij
  apply (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hi hj).mp
  rw [iterate_act,iterate_act]
  exact (ofSet_eq_iff μ _ _).mpr he

end AEPeriod

end
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

namespace BoundedSubadditive
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {T : X → X} {A B : Set X}

lemma ergodic_restrict_subset_of_inter [IsFiniteMeasure μ] (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : PreErgodic T (μ.restrict A)) (hBInv : T ⁻¹' B=B) (hpos : 0<μ (A∩B)) :
    A ≤ᵐ[μ] B := by
  rcases h.ae_mem_or_ae_notMem hB hBInv with hh|hh
  · exact (ae_restrict_iff' hA).mp hh
  · have hz : μ.restrict A B=0 := by
      simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hh
    rw [Measure.restrict_apply hB,inter_comm] at hz
    exact (hpos.ne' hz).elim

lemma ergodic_restrict_disjoint_or_eq [IsFiniteMeasure μ] (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : PreErgodic T (μ.restrict A)) (hBInv : T ⁻¹' B=B) (hmass : μ A=μ B) :
    μ (A∩B)=0 ∨ A =ᵐ[μ] B := by
  by_cases hz : μ (A∩B)=0
  · exact Or.inl hz
  · exact Or.inr (ae_eq_of_ae_subset_of_measure_ge
      (ergodic_restrict_subset_of_inter hA hB h hBInv (pos_iff_ne_zero.mpr hz))
      hmass.symm.le hA.nullMeasurableSet (measure_ne_top μ B))

lemma measurePreserving_restrict_of_ae [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ) (hA : MeasurableSet A)
    (hInv : T ⁻¹' A =ᵐ[μ] A) : MeasurePreserving T (μ.restrict A) (μ.restrict A) := by
  have h := hT.restrict_preimage hA
  rwa [Measure.restrict_congr_set hInv] at h

lemma preimage_iterate_symm_eq (e : X ≃ᵐ X) {n : ℕ} (hA : (e^[n]) ⁻¹' A=A) :
    (e.symm^[n]) ⁻¹' A=A := by
  ext x
  have hh := congrArg (fun U : Set X => (e.symm^[n] x)∈U) hA
  have hi : Function.LeftInverse (e : X → X) e.symm := e.apply_symm_apply
  simpa only [mem_preimage,hi.iterate n x] using Iff.of_eq hh.symm

lemma translate_invariant (e : X ≃ᵐ X) {n : ℕ} (hA : (e^[n]) ⁻¹' A=A) (j : ℕ) :
    (e^[n]) ⁻¹' ((e.symm^[j]) ⁻¹' A)=((e.symm^[j]) ⁻¹' A) := by
  have hc : Function.Commute (e : X → X) e.symm := fun x => by simp
  ext x
  change (e.symm^[j] (e^[n] x)∈A) ↔ (e.symm^[j] x∈A)
  rw [←(hc.iterate_iterate n j).eq]
  exact Iff.of_eq (congrArg (fun U : Set X => e.symm^[j] x∈U) hA)

lemma measurePreserving_translate [IsFiniteMeasure μ] (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (hA : MeasurableSet A) (j : ℕ) :
    MeasurePreserving (e^[j]) (μ.restrict A) (μ.restrict ((e.symm^[j]) ⁻¹' A)) := by
  have hB : MeasurableSet ((e.symm^[j]) ⁻¹' A) := hA.preimage (e.symm.measurable.iterate j)
  have h := (he.iterate j).restrict_preimage hB
  have hi : Function.LeftInverse (e.symm : X → X) e := e.symm_apply_apply
  have hh : (e^[j]) ⁻¹' ((e.symm^[j]) ⁻¹' A)=A := by
    ext x
    simp only [mem_preimage,hi.iterate j x]
  rwa [hh] at h

lemma ergodic_translate [IsFiniteMeasure μ] (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (hA : MeasurableSet A) {n : ℕ} (h : Ergodic (e^[n]) (μ.restrict A)) (j : ℕ) :
    Ergodic (e^[n]) (μ.restrict ((e.symm^[j]) ⁻¹' A)) := by
  exact (measurePreserving_translate e he hA j).ergodic_of_ergodic_semiconj h
    (e.measurable.iterate n) (Function.Commute.iterate_iterate_self e j n)

end BoundedSubadditive

end
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

namespace BoundedSubadditive
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

structure CyclicAtom (e : X ≃ᵐ X) (μ : Measure X) (E A : Set X) (n : ℕ) where
  period : ℕ
  positive : 0<period
  divides : period ∣ n
  periodic : (e.symm^[period]) ⁻¹' A =ᵐ[μ] A
  disjoint : ∀ i j : Fin period,i≠j → μ (((e.symm^[i.val]) ⁻¹' A)∩((e.symm^[j.val]) ⁻¹' A))=0
  cover : (⋃ j : Fin period,(e.symm^[j.val]) ⁻¹' A) =ᵐ[μ] E
  mass : (period : ℝ≥0∞)*μ A=μ E
  forward : ∀ j : Fin period,e '' ((e.symm^[j.val]) ⁻¹' A) =ᵐ[μ]
    (e.symm^[(j.val+1)%period]) ⁻¹' A
  ergodic : ∀ j : Fin period,Ergodic (e^[period]) (μ.restrict ((e.symm^[j.val]) ⁻¹' A))

lemma inverse_preimage_ae [IsFiniteMeasure μ] (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) {A : Set X} (p : ℕ)
    (hp : (e.symm^[p]) ⁻¹' A =ᵐ[μ] A) : (e^[p]) ⁻¹' A =ᵐ[μ] A := by
  have hh := (he.iterate p).quasiMeasurePreserving.preimage_ae_eq hp
  have hi : Function.LeftInverse (e.symm : X → X) e := e.symm_apply_apply
  have hx : (e^[p]) ⁻¹' ((e.symm^[p]) ⁻¹' A)=A := by
    ext x
    simp only [mem_preimage,hi.iterate p x]
  rw [hx] at hh
  exact hh.symm

theorem finite_cycle_of_ergodic_atom [IsFiniteMeasure μ] (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    {E A : Set X} (hE : MeasurableSet E) (hA : MeasurableSet A) (hApos : 0<μ A)
    (hAE : A ≤ᵐ[μ] E) (hEInv : e ⁻¹' E=E) (hErgE : Ergodic e (μ.restrict E))
    {n : ℕ} (hn : 0 < n) (hAInv : (e^[n]) ⁻¹' A=A) (hErgA : Ergodic (e^[n]) (μ.restrict A)) :
    Nonempty (CyclicAtom e μ E A n) := by
  let hs := (he.symm e).quasiMeasurePreserving
  let p := Function.minimalPeriod (AEPeriod.act hs) (AEPeriod.ofSet μ A)
  have haS : (e.symm^[n]) ⁻¹' A =ᵐ[μ] A := Eventually.of_forall fun x =>
    congrArg (fun U : Set X => x∈U) (preimage_iterate_symm_eq e hAInv)
  have hp : 0 < p := AEPeriod.period_pos hs hn haS
  have hpd : p ∣ n := AEPeriod.period_dvd hs haS
  have hpp : (e.symm^[p]) ⁻¹' A =ᵐ[μ] A := AEPeriod.period_preimage hs A
  let P (j : ℕ) : Set X := (e.symm^[j]) ⁻¹' A
  have hPm (j : ℕ) : MeasurableSet (P j) := hA.preimage (e.symm.measurable.iterate j)
  have hPmass (j : ℕ) : μ (P j)=μ A := ((he.symm e).iterate j).measure_preimage hA.nullMeasurableSet
  have hPInv (j : ℕ) : (e^[n]) ⁻¹' (P j)=P j := translate_invariant e hAInv j
  have hPdisj (i j : Fin p) (hij : i≠j) : μ (P i.val∩P j.val)=0 := by
    rcases ergodic_restrict_disjoint_or_eq (hPm _) (hPm _)
      (ergodic_translate e he hA hErgA i.val).toPreErgodic (hPInv j.val)
      ((hPmass _).trans (hPmass _).symm) with hh|hh
    · exact hh
    · exact (AEPeriod.preimage_ne hs A i.isLt j.isLt (fun hv => hij (Fin.ext hv)) hh).elim
  have hnext (j : Fin p) : e.symm ⁻¹' P j.val =ᵐ[μ] P ((j.val+1)%p) := by
    have heq : e.symm ⁻¹' P j.val=P (j.val+1) := by
      ext x
      simp only [P,mem_preimage,Function.iterate_succ_apply]
    rw [heq]
    exact (AEPeriod.preimage_mod hs A (j.val+1)).symm
  let U : Set X := ⋃ j : Fin p,P j.val
  have hUm : MeasurableSet U := MeasurableSet.iUnion fun j => hPm j.val
  have hUsub : U ≤ᵐ[μ] E := by
    have hh (j : Fin p) : P j.val ≤ᵐ[μ] E := by
      have hh := ((he.symm e).iterate j.val).quasiMeasurePreserving.preimage_mono_ae hAE
      rwa [preimage_iterate_symm_eq e (Function.IsFixedPt.preimage_iterate hEInv j.val)] at hh
    filter_upwards [ae_all_iff.mpr hh] with x hx
    intro hxU
    obtain ⟨j,hj⟩ := mem_iUnion.mp hxU
    exact hx j hj
  have hUInv : e.symm ⁻¹' U =ᵐ[μ] U := by
    have hnxt (j : Fin p) : e.symm ⁻¹' P j.val =ᵐ[μ] P (finRotate p j).val := by
      have hrot : (finRotate p j).val=(j.val+1)%p := by
        let : NeZero p := ⟨hp.ne'⟩
        rw [finRotate_apply]
        rw [Fin.val_add]
        change (j.val+1%p)%p=(j.val+1)%p
        exact Nat.add_mod_mod _ _ _
      simpa only [hrot] using hnext j
    filter_upwards [ae_all_iff.mpr hnxt] with x hx
    apply propext
    change (e.symm x ∈ U) ↔ x ∈ U
    simp only [U,mem_iUnion]
    constructor
    · rintro ⟨j,hj⟩
      exact ⟨finRotate p j,Eq.mp (hx j) hj⟩
    · rintro ⟨j,hj⟩
      refine ⟨(finRotate p).symm j,?_⟩
      apply (Iff.of_eq (hx ((finRotate p).symm j))).mpr
      simp only [Equiv.apply_symm_apply]
      exact hj
  have hUpos : 0<μ U := hApos.trans_le (measure_mono (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨0,hp⟩,hx⟩))
  have hEU : E ≤ᵐ[μ] U := by
    have hInvR : e.symm ⁻¹' U =ᵐ[μ.restrict E] U :=
      Measure.absolutelyContinuous_restrict.ae_eq hUInv
    rcases hErgE.symm.quasiErgodic.ae_mem_or_ae_notMem₀ hUm.nullMeasurableSet hInvR with h|h
    · exact (ae_restrict_iff' hE).mp h
    · have hz : μ.restrict E U=0 := by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using h
      rw [Measure.restrict_apply hUm] at hz
      have hei : (U∩E : Set X) =ᵐ[μ] U := by
        filter_upwards [hUsub] with x hx
        apply propext
        exact ⟨fun h => h.1,fun h => ⟨h,hx h⟩⟩
      rw [measure_congr hei] at hz
      exact (hUpos.ne' hz).elim
  have hcover : U =ᵐ[μ] E := eventuallyLE_antisymm_iff.mpr ⟨hUsub,hEU⟩
  have hmass : (p : ℝ≥0∞)*μ A=μ E := by
    rw [←measure_congr hcover]
    dsimp only [U]
    rw [measure_iUnion₀ (fun i j hij => hPdisj i j hij) (fun j => (hPm j.val).nullMeasurableSet),tsum_fintype]
    simp only [hPmass,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hbaseErg : Ergodic (e^[p]) (μ.restrict A) := by
    refine ⟨measurePreserving_restrict_of_ae (he.iterate p) hA (inverse_preimage_ae e he p hpp),?_⟩
    obtain ⟨q,hq⟩ := hpd
    apply PreErgodic.of_iterate q
    simpa only [hq,Function.iterate_mul] using hErgA.toPreErgodic
  refine ⟨{
    period := p
    positive := hp
    divides := hpd
    periodic := hpp
    disjoint := hPdisj
    cover := hcover
    mass := hmass
    forward := ?_
    ergodic := ?_ }⟩
  · intro j
    rw [e.image_eq_preimage_symm]
    exact hnext j
  · intro j
    exact ergodic_translate e he hA hbaseErg j.val

end BoundedSubadditive

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
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology ENNReal NNReal BigOperators

namespace HyperbolicCoding

def ExponentiallyAsymptotic {X : Type*} [PseudoMetricSpace X]
    (T : X → X) (x y : X) : Prop :=
  ∃ ρ : ℝ,0≤ρ ∧ ρ<1 ∧ ∃ C : ℝ,
    ∀ᶠ n : ℕ in atTop,dist (T^[n] x) (T^[n] y)≤C*ρ^n

end HyperbolicCoding

end
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology NNReal ENNReal

namespace HyperbolicCoding

def joinedBinary {X : Type*} (α : ℕ → ℕ → X → Bool) (N : ℕ) (x : X) :
    (Fin N × Fin N) → Bool := fun p => α p.1 p.2 x

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Bernoulli_TailNameSaturation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology

namespace HyperbolicCoding

def tailName {X A : Type*} (T : X → X) (α : X → A) (m : ℕ) (x : X) : ℕ → A :=
  fun n => α (T^[n+m] x)

lemma measurable_tailName {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    {T : X → X} (hT : Measurable T) {α : X → A} (hα : Measurable α) (m : ℕ) :
    Measurable (tailName T α m) :=
  Measurable.of_eval (fun n => hα.comp (hT.iterate (n+m)))

def TailEvent {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (μ : Measure X) (T : X → X) (α : X → A) (E : Set X) : Prop :=
  ∀ m : ℕ,∃ D : Set (ℕ → A),MeasurableSet D ∧ E=ᵐ[μ](tailName T α m) ⁻¹' D

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter

def TailObservable {X A B : Type*} [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure X) (T : X → X) (α : X → A) (q : X → B) : Prop :=
  ∀ m : ℕ,∃ G : (ℕ → A) → B,Measurable G ∧ q=ᵐ[μ]G ∘ tailName T α m

end HyperbolicCoding
end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Bernoulli_ReverseFano
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β : Type*} [Fintype α] [Fintype β]
variable [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]

def wordPairEquiv (n : ℕ) : (Fin n → α×β) ≃ (Fin n → α)×(Fin n → β) where
  toFun v := (fun i => (v i).1,fun i => (v i).2)
  invFun v := fun i => (v.1 i,v.2 i)
  left_inv v := by funext i; rfl
  right_inv v := by cases v; rfl

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

def wordReverseEquiv (n : ℕ) : (Fin n → α) ≃ (Fin n → α) where
  toFun v i := v i.rev
  invFun v i := v i.rev
  left_inv v := by funext i; simp
  right_inv v := by funext i; simp

end StandardMapEntropy.Entropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Bernoulli_RohlinSinaiFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory Set Filter
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
variable {μ : Measure X} [IsFiniteMeasure μ] {T : X → X} {α : X → A}

def IsTailAtom (μ : Measure X) (T : X → X) (α : X → A) (C : Set X) : Prop :=
  TailEvent μ T α C ∧ 0<μ C ∧ ∀ E,TailEvent μ T α E → C ≤ᵐ[μ] E ∨ C ≤ᵐ[μ] Eᶜ

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Components_PowerAtomCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

namespace BoundedSubadditive
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

structure PowerAtomFamily (e : X ≃ᵐ X) (μ : Measure X) where
  atom : ℕ → Set X
  measurable : ∀ n,MeasurableSet (atom n)
  positive : ∀ n,0<μ (atom n)
  invariant : ∀ n,(e^[n+1]) ⁻¹' (atom n)=atom n
  ergodic : ∀ n,Ergodic (e^[n+1]) (μ.restrict (atom n))
  common : ∃ D : Set X,0<μ D ∧ ∀ n,D⊆atom n

namespace PowerAtomFamily
variable {e : X ≃ᵐ X} (F : PowerAtomFamily e μ) (he : MeasurePreserving e μ μ)

lemma refinement {n m : ℕ} (hdiv : n+1 ∣ m+1) : F.atom m ≤ᵐ[μ] F.atom n := by
  obtain ⟨D,hD,hDA⟩ := F.common
  have hi : 0<μ (F.atom m∩F.atom n) := hD.trans_le (measure_mono (fun x hx => ⟨hDA m hx,hDA n hx⟩))
  apply ergodic_restrict_subset_of_inter (F.measurable m) (F.measurable n) (F.ergodic m).toPreErgodic _ hi
  obtain ⟨q,hq⟩ := hdiv
  simpa only [hq,Function.iterate_mul,Function.IsFixedPt] using Function.IsFixedPt.preimage_iterate (F.invariant n) q

noncomputable def cycle (n : ℕ) : CyclicAtom e μ (F.atom 0) (F.atom n) (n+1) :=
  Classical.choice (finite_cycle_of_ergodic_atom e he (F.measurable 0) (F.measurable n) (F.positive n)
    (F.refinement (by simp)) (by simpa only [zero_add,Function.iterate_one] using F.invariant 0)
    (by simpa only [zero_add,Function.iterate_one] using F.ergodic 0) (Nat.succ_pos n) (F.invariant n) (F.ergodic n))

end PowerAtomFamily
end BoundedSubadditive

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Bernoulli_IntegerDynamics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter

namespace HyperbolicCoding
variable {X : Type*} [MeasurableSpace X]

def integerIterate (e : X ≃ᵐ X) (n : ℤ) (x : X) : X := (e.toEquiv^n) x

@[simp] lemma integerIterate_zero (e : X ≃ᵐ X) (x : X) : integerIterate e 0 x=x := by
  simp only [integerIterate,zpow_zero,Equiv.Perm.one_apply]
@[simp] lemma integerIterate_one (e : X ≃ᵐ X) (x : X) : integerIterate e 1 x=e x := by
  simp only [integerIterate,zpow_one,MeasurableEquiv.coe_toEquiv]

def orbitName {A : Type*} (e : X ≃ᵐ X) (α : X → A) (x : X) : ℤ → A :=
  fun n => α (integerIterate e n x)

end HyperbolicCoding

end
section
open MeasureTheory Set Filter

namespace HyperbolicCoding
variable {X A : Type*} [MeasurableSpace X]

def iterateEquiv (e : X ≃ᵐ X) (n : ℕ) : X ≃ᵐ X where
  toEquiv := e.toEquiv^n
  measurable_toFun := by simpa only [Equiv.Perm.coe_pow,MeasurableEquiv.coe_toEquiv] using e.measurable.iterate n
  measurable_invFun := by
    change Measurable (⇑((e.toEquiv^n)⁻¹))
    rw [←inv_pow,Equiv.Perm.inv_def,Equiv.Perm.coe_pow]
    exact e.symm.measurable.iterate n

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Filter

def GoodNames {X A : Type*} [MetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (T : X → X) (α : X → A) : Prop :=
  ∀ᵐ x ∂μ,∀ y,ExponentiallyAsymptotic T x y →
    ∀ᶠ n : ℕ in atTop,α (T^[n] x)=α (T^[n] y)
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def LawClose (μ ν : Measure X) (ε : ℝ) : Prop :=
  ∀ D : Set X,MeasurableSet D → |μ.real D-ν.real D|≤ε

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Bernoulli_ReverseTailProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

@[instance_reducible] def tailSigma (T : X → X) (α : X → A) (n : ℕ) : MeasurableSpace X :=
  MeasurableSpace.comap (tailName T α n) inferInstance

lemma tailSigma_le {T : X → X} {α : X → A} (hT : Measurable T) (hα : Measurable α) (n : ℕ) :
    tailSigma T α n ≤ (inferInstance : MeasurableSpace X) :=
  (measurable_tailName hT hα n).comap_le

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

noncomputable def constL2 (μ : Measure X) [IsFiniteMeasure μ] (c : ℝ) : Lp ℝ 2 μ :=
  indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) c

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

def remotePair (T S : X → X) (α : X → A) (n : ℕ) (x : X) : (ℕ → A)×(ℕ → A) :=
  (tailName S α n x,tailName T α n x)

noncomputable def remoteProductLaw (μ : Measure X) (T S : X → X) (α : X → A) :
    Measure ((ℕ → A)×(ℕ → A)) :=
  (μ.map (tailName S α 0)).prod (μ.map (tailName T α 0))

def RemoteIndependent (μ η : Measure X) (T S : X → X) (α : X → A) : Prop :=
  ∀ ε : ℝ,0<ε → ∀ᶠ n : ℕ in atTop,
    LawClose (η.map (remotePair T S α n)) (remoteProductLaw μ T S α) ε

def WeakBernoulliProcess (μ : Measure X) (e : X ≃ᵐ X) (α : X → A) : Prop :=
  RemoteIndependent μ μ e e.symm α

def dropName (k : ℕ) (v : ℕ → A) (i : ℕ) : A := v (i+k)

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Bernoulli_ErgodicL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter BoundedSubadditive
open scoped ENNReal Topology BigOperators
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

noncomputable def orbitAverage (T : X → X) (f : X → ℝ) (n : ℕ) (x : X) : ℝ :=
  birkhoffSum T f n x/(n : ℝ)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology BigOperators
variable {X : Type*} [MeasurableSpace X]

noncomputable def cesaroLawMass (e : X ≃ᵐ X) (η : Measure X) (N : ℕ) (D : Set X) : ℝ :=
  (∑ i∈Finset.range N,(η.map (e^[i])).real D)/(N : ℝ)

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_FiniteMaximalCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

structure MatrixCoupling (p : A → ℝ) (q : B → ℝ) where
  weight : A → B → ℝ
  nonneg : ∀ a b,0≤weight a b
  row : ∀ a,∑ b,weight a b=p a
  col : ∀ b,∑ a,weight a b=q b

namespace MatrixCoupling
variable {p : A → ℝ} {q : B → ℝ} {s : C → ℝ}

lemma right_nonneg (r : MatrixCoupling p q) (b : B) : 0≤q b := by
  rw [←r.col b]
  exact Finset.sum_nonneg (fun a _ => r.nonneg a b)
lemma le_left (r : MatrixCoupling p q) (a : A) (b : B) : r.weight a b≤p a := by
  rw [←r.row a]
  exact Finset.single_le_sum (fun b _ => r.nonneg a b) (Finset.mem_univ b)
lemma le_right (r : MatrixCoupling p q) (a : A) (b : B) : r.weight a b≤q b := by
  rw [←r.col b]
  exact Finset.single_le_sum (fun a _ => r.nonneg a b) (Finset.mem_univ a)

noncomputable def glueWeight (r : MatrixCoupling p q) (t : MatrixCoupling q s)
    (a : A) (b : B) (c : C) : ℝ := r.weight a b*t.weight b c/q b

lemma glueWeight_nonneg (r : MatrixCoupling p q) (t : MatrixCoupling q s) (a b c) :
    0≤glueWeight r t a b c := div_nonneg (mul_nonneg (r.nonneg _ _) (t.nonneg _ _)) (r.right_nonneg b)

lemma glueWeight_row (r : MatrixCoupling p q) (t : MatrixCoupling q s) (a b) :
    (∑ c,glueWeight r t a b c)=r.weight a b := by
  simp only [glueWeight,←Finset.sum_div,←Finset.mul_sum,t.row]
  by_cases hq : q b=0
  · have hz : r.weight a b=0 := le_antisymm (by simpa only [hq] using r.le_right a b) (r.nonneg a b)
    simp [hq,hz]
  · exact mul_div_cancel_right₀ _ hq

lemma glueWeight_col (r : MatrixCoupling p q) (t : MatrixCoupling q s) (b c) :
    (∑ a,glueWeight r t a b c)=t.weight b c := by
  simp only [glueWeight,←Finset.sum_div,←Finset.sum_mul,r.col]
  by_cases hq : q b=0
  · have hz : t.weight b c=0 := le_antisymm (by simpa only [hq] using t.le_left b c) (t.nonneg b c)
    simp [hq,hz]
  · exact mul_div_cancel_left₀ _ hq

noncomputable def comp (r : MatrixCoupling p q) (t : MatrixCoupling q s) : MatrixCoupling p s where
  weight a c := ∑ b,glueWeight r t a b c
  nonneg a c := Finset.sum_nonneg (fun b _ => glueWeight_nonneg r t a b c)
  row a := by rw [Finset.sum_comm]; simp only [glueWeight_row,r.row]
  col c := by rw [Finset.sum_comm]; simp only [glueWeight_col,t.col]

noncomputable def cost (r : MatrixCoupling p q) (d : A → B → ℝ) := ∑ a,∑ b,r.weight a b*d a b

end MatrixCoupling
end HyperbolicCoding

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [Fintype A] [MeasurableSingletonClass A]

noncomputable def information (μ : Measure X) (p : X → A) (x : X) : ℝ :=
  -Real.log (mass μ p (p x))

end StandardMapEntropy.Entropy

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B C D : Type*} [MeasurableSpace X]
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]

namespace MatrixCoupling
variable {p : A → ℝ} {q : B → ℝ} {s : C → ℝ} {t : D → ℝ}

noncomputable def symm (r : MatrixCoupling p q) : MatrixCoupling q p where
  weight b a := r.weight a b
  nonneg b a := r.nonneg a b
  row b := r.col b
  col a := r.row a

noncomputable def diagonal (p : A → ℝ) (hp : ∀ a,0≤p a) : MatrixCoupling p p := by
  classical
  exact {
    weight := fun a b => if a=b then p a else 0
    nonneg := fun a b => by split_ifs; exact hp a; exact le_rfl
    row := fun a => by simp
    col := fun b => by simp }

noncomputable def product (r : MatrixCoupling p q) (u : MatrixCoupling s t) :
    MatrixCoupling (fun ac : A×C => p ac.1*s ac.2) (fun bd : B×D => q bd.1*t bd.2) where
  weight ac bd := r.weight ac.1 bd.1*u.weight ac.2 bd.2
  nonneg ac bd := mul_nonneg (r.nonneg _ _) (u.nonneg _ _)
  row ac := by simp only [Fintype.sum_prod_type,←Finset.mul_sum,←Finset.sum_mul,r.row,u.row]
  col bd := by simp only [Fintype.sum_prod_type,←Finset.mul_sum,←Finset.sum_mul,r.col,u.col]

section Observations
variable [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
variable (μ : Measure X) [IsFiniteMeasure μ]

noncomputable def observations (p : X → A) (q : X → B) (hp : Measurable p) (hq : Measurable q) :
    MatrixCoupling (mass μ p) (mass μ q) where
  weight a b := mass μ (fun x => (p x,q x)) (a,b)
  nonneg _ _ := mass_nonneg _ _ _
  row a := (mass_joint_row μ p q hp hq a).symm
  col b := (mass_joint_col μ p q hp hq b).symm

end Observations
end MatrixCoupling
end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_AtomlessFinitePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B C D : Type*} [MeasurableSpace X]
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]

noncomputable def symbolCost {E : Type*} (a b : E) : ℝ := by
  classical
  exact if a=b then 0 else 1

namespace MatrixCoupling
variable {p : A → ℝ} {q : B → ℝ}

noncomputable def reindex (r : MatrixCoupling p q) (e : C ≃ A) (f : D ≃ B) :
    MatrixCoupling (p ∘ e) (q ∘ f) where
  weight c d := r.weight (e c) (f d)
  nonneg c d := r.nonneg _ _
  row c := by rw [f.sum_comp]; exact r.row (e c)
  col d := (e.sum_comp (fun a => r.weight a (f d))).trans (r.col (f d))

end MatrixCoupling

noncomputable def nameCost {E : Type*} {n : ℕ} (a b : Fin n → E) : ℝ :=
  ∑ i,symbolCost (a i) (b i)

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_SequentialChunkCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
variable (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]

def finiteName (q : ℕ → X → A) (i n : ℕ) (x : X) : Fin n → A := fun j => q (i+j) x

noncomputable def independentNameWeights (q : ℕ → X → A) (i n : ℕ) (w : Fin n → A) : ℝ :=
  ∏ j : Fin n,mass μ (q (i+j.val)) (w j)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
variable (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]

def chunkObservation (f : X → X) (p : X → A) (k g i : ℕ) (x : X) : Fin k → A :=
  word f p k (f^[i*(k+g)] x)

def selectChunks (k g n : ℕ) (w : Fin (n*(k+g)) → A) : Fin n → Fin k → A :=
  fun j r => w ⟨j.val*(k+g)+r.val,by
    have h1 : (j.val+1)*(k+g)≤n*(k+g) := Nat.mul_le_mul_right _ j.isLt
    have h2 : r.val<k+g := lt_of_lt_of_le r.isLt (Nat.le_add_right _ _)
    nlinarith⟩

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

noncomputable def productWeights (w : B → A → ℝ) (D : B → A) : ℝ := ∏ b,w b (D b)
noncomputable def finiteExpectation {E : Type*} [Fintype E] (v : E → ℝ) (F : E → ℝ) : ℝ :=
  ∑ x,v x*F x

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_ChunkNameCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open scoped BigOperators

noncomputable def relativeInformation {A : Type*} [Fintype A] (p q : A → ℝ) : ℝ :=
  ∑ a,p a*(Real.log (p a)-Real.log (q a))

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_ConditionalRefinementInformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set HyperbolicCoding
open scoped BigOperators ENNReal
variable {X A B C : Type*} [MeasurableSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]
variable (μ : Measure X) [IsProbabilityMeasure μ]

noncomputable def refinementCopyWeights (p : X → A) (q : X → B) (c : A → C) (a : A) (b : B) : ℝ :=
  mass μ p a*mass μ (fun x => (c (p x),q x)) (c a,b)/mass μ (c ∘ p) (c a)

end StandardMapEntropy.Entropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_FiniteProductVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [Nonempty A]

noncomputable def assignedMass (q : B → ℝ) (D : B → A) (a : A) : ℝ :=
  ∑ b,q b*(if D b=a then 1 else 0)
noncomputable def fractionalMass (q : B → ℝ) (w : B → A → ℝ) (a : A) : ℝ :=
  ∑ b,q b*w b a
noncomputable def assignmentError (q : B → ℝ) (w : B → A → ℝ) (D : B → A) : ℝ :=
  ∑ a,|assignedMass q D a-fractionalMass q w a|

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [Nonempty A]
namespace MatrixCoupling
variable {p : A → ℝ} {q : B → ℝ}

noncomputable def conditionalAssignment (r : MatrixCoupling p q) (b : B) (a : A) : ℝ :=
  if q b=0 then (if a=Classical.choice (inferInstance : Nonempty A) then 1 else 0)
  else r.weight a b/q b

end MatrixCoupling
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [Nonempty A]

namespace MatrixCoupling
variable {p : A → ℝ} {q : B → ℝ}
noncomputable def assignment (q : B → ℝ) (hq : ∀ b,0≤q b) (D : B → A) :
    MatrixCoupling (assignedMass q D) q where
  weight a b := q b*(if D b=a then 1 else 0)
  nonneg a b := mul_nonneg (hq b) (by split_ifs <;> norm_num)
  row a := rfl
  col b := by simp

end MatrixCoupling
end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_TypicalWordCodebook
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {A : Type*} [Fintype A] [DecidableEq A]

noncomputable def productWordWeight (p : A → ℝ) (n : ℕ) (w : Fin n → A) : ℝ := ∏ i,p (w i)
noncomputable def wordInformation (p : A → ℝ) {n : ℕ} (w : Fin n → A) : ℝ := ∑ i,-Real.log (p (w i))

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {A : Type*} [Fintype A] [DecidableEq A]

noncomputable def weightEntropy (p : A → ℝ) : ℝ := ∑ a,p a*(-Real.log (p a))
noncomputable def informationVariance (p : A → ℝ) : ℝ :=
  ∑ a,p a*(-Real.log (p a)-weightEntropy p)^2

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

noncomputable def finiteWeightLaw (p : A → ℝ) : Measure A :=
  ∑ a,ENNReal.ofReal (p a) • Measure.dirac a

instance finiteWeightLaw_finite (p : A → ℝ) : IsFiniteMeasure (finiteWeightLaw p) := by
  constructor
  simp [finiteWeightLaw,Measure.finsetSum_apply]

def iidShift : (ℤ → A) ≃ᵐ (ℤ → A) where
  toFun w i := w (i+1)
  invFun w i := w (i-1)
  left_inv w := by funext i; simp
  right_inv w := by funext i; simp
  measurable_toFun := Measurable.of_eval (fun _ => measurable_pi_apply _)
  measurable_invFun := Measurable.of_eval (fun _ => measurable_pi_apply _)

end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Entropy_FiniteBinCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

noncomputable def wordPack (n m : ℕ) : (Fin (n*m) → α) ≃ (Fin n → Fin m→α) :=
  ((Equiv.piCongrLeft (fun _ : Fin (n*m) => α) finProdFinEquiv).symm).trans
    (Equiv.curry (Fin n) (Fin m) α)

end StandardMapEntropy.Entropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_EntropyRateCodebook
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding.Marker
open scoped BigOperators
variable {A C : Type*} {n r : ℕ}

def HeadMarker (hr : r < n) (zero one : A) (w : Fin n → A) : Prop :=
  (∀ j : Fin r, w ⟨j.val,lt_trans j.isLt hr⟩=zero) ∧ w ⟨r,hr⟩=one

def MarkedBlock (hr : r < n) (zero one : A) (w : Fin n → A) : Prop :=
  HeadMarker hr zero one w ∧
    ∀ j : Fin n,0 < j.val → ∃ (l : Fin r) (h : j.val+l.val < n), w ⟨j.val+l.val,h⟩=one

def centeredWindow (n : ℕ) (a : ℤ → A) (i : Fin n) : Fin (2*n) → A :=
  fun j => a ((i.val : ℤ)+(j.val : ℤ)-(n : ℤ))

def column (v : Fin (2*n) → A) (t : Fin n) : Fin n → A :=
  fun j => v ⟨n-t.val+j.val,by omega⟩

noncomputable def candidates (hr : r < n) (zero one : A) (v : Fin (2*n) → A) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun t => HeadMarker hr zero one (column v t))

noncomputable def phase (hn : 0 < n) (hr : r < n) (zero one : A) (v : Fin (2*n) → A) : Fin n :=
  if h : (candidates hr zero one v).Nonempty then (candidates hr zero one v).min' h
    else ⟨0,hn⟩

noncomputable def decodeWindow (hn : 0 < n) (hr : r < n) (zero one : A)
    (D : (Fin n → A) → (Fin n → C)) (v : Fin (2*n) → A) : C :=
  D (column v (phase hn hr zero one v)) (phase hn hr zero one v)

section Construction

def markWord (r : ℕ) (zero one : A) (w : Fin n → A) (i : Fin n) : A :=
  if i.val < r then zero else if i.val%r=0 ∨ i.val+1=n then one else w i

end Construction
end HyperbolicCoding.Marker

end
section
namespace HyperbolicCoding.Marker
open scoped BigOperators
variable {A : Type*} [Fintype A] [DecidableEq A] {n r : ℕ}

def reserved (n r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.val < r ∨ i.val%r=0 ∨ i.val+1=n)

end HyperbolicCoding.Marker

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Towers_FiniteCouplingRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory Set
variable {X I A : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [MeasurableSingletonClass I] [Countable I] [MeasurableSpace A]

local instance disjointIndexOptionMeasurableSpace : MeasurableSpace (Option I) := ⊤

noncomputable def disjointIndex (s : I → Set X) (x : X) : Option I :=
  by
    classical
    exact if h : ∃ i,x∈s i then some h.choose else none

noncomputable def disjointPaste (s : I → Set X) (f : I → X → A) (f₀ : X → A) (x : X) : A :=
  match disjointIndex s x with
  | none => f₀ x
  | some i => f i x

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X : Type*} [MeasurableSpace X]

def entryLevel (T : X → X) (B : Set X) (n : ℕ) : Set X :=
  {x | T^[n] x∈B ∧ ∀ j<n,T^[j] x∉B}

def entryTowerBase (e : X ≃ᵐ X) (B : Set X) (N : ℕ) : Set X :=
  ⋃ q : ℕ,entryLevel e B (q*N+(N-1))

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [Fintype A] [MeasurableSingletonClass A]

noncomputable def paintTower (e : X ≃ᵐ X) (U : Set X) (N : ℕ)
    (B : X → (Fin N → A)) (p : X → A) : X → A :=
  disjointPaste (fun i : Fin N => (e^[i.val]) '' U)
    (fun i x => B (e.symm^[i.val] x) i) p

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_ReconstructionEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A C : Type*} [MeasurableSpace X]

noncomputable def extendPrefixDecoder {k t : ℕ} (D : (Fin (k+t) → A) → (Fin k → C))
    (c₀ : C) (w : Fin (k+t) → A) : Fin (k+t) → C :=
  Fin.addCases (D w) (fun _ => c₀)

end HyperbolicCoding

end
section
namespace HyperbolicCoding.MatrixCoupling
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [Nonempty A]
    {p : A → ℝ} {q : B → ℝ}

noncomputable def decodingThreshold (ε : ℝ) : ℝ :=
  min (ε^2/16) ((ε^2/16)*ε/4)

end HyperbolicCoding.MatrixCoupling

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_TypicalDecodableCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding.MatrixCoupling
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {p : A → ℝ} {q : B → ℝ}

noncomputable def extendRows (S : Finset A) (g : S → B → ℝ) (a : A) (b : B) : ℝ :=
  if h : a∈S then g ⟨a,h⟩ b else 0

omit [Fintype B] [DecidableEq B] in
lemma sum_extendRows (S : Finset A) (g : S → B → ℝ) (b : B) :
    (∑ a,extendRows S g a b)=∑ a : S,g a b := by
  exact (Finset.sum_attach_eq_sum_dite S (fun a => g a b)).symm

omit [Fintype A] [Fintype B] [DecidableEq B] in
lemma extendRows_nonneg (S : Finset A) (g : S → B → ℝ) (hg : ∀ a b,0≤g a b) (a b) :
    0≤extendRows S g a b := by
  unfold extendRows
  split
  · exact hg _ _
  · rfl

omit [Fintype A] [DecidableEq B] in
lemma extendRows_sum (S : Finset A) (g : S → B → ℝ) (a : A) :
    (∑ b,extendRows S g a b)=if h : a∈S then ∑ b,g ⟨a,h⟩ b else 0 := by
  unfold extendRows
  split <;> simp_all

noncomputable def replaceSub (R : MatrixCoupling p q) (S : Finset A)
    {u : S → ℝ} {v : B → ℝ} (G H : MatrixCoupling u v)
    (hle : ∀ a b,G.weight a b≤R.weight a b) : MatrixCoupling p q where
  weight a b := R.weight a b-extendRows S G.weight a b+extendRows S H.weight a b
  nonneg a b := by
    have hg : extendRows S G.weight a b≤R.weight a b := by
      unfold extendRows
      split
      · exact hle _ _
      · exact R.nonneg _ _
    exact add_nonneg (sub_nonneg.mpr hg) (extendRows_nonneg S _ H.nonneg a b)
  row a := by
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,R.row,extendRows_sum,G.row,H.row]
    ring
  col b := by
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,R.col,sum_extendRows,G.col,H.col]
    ring

noncomputable def divide (R : MatrixCoupling p q) {t : ℝ} (ht : 0<t) :
    MatrixCoupling (fun a => p a/t) (fun b => q b/t) where
  weight a b := R.weight a b/t
  nonneg a b := div_nonneg (R.nonneg a b) ht.le
  row a := by rw [←Finset.sum_div,R.row]
  col b := by rw [←Finset.sum_div,R.col]

noncomputable def rectangle (R : MatrixCoupling p q) (S : Finset A) (T : Finset B) :
    MatrixCoupling (fun a : S => ∑ b,if b∈T then R.weight a b else 0)
      (fun b => ∑ a : S,if b∈T then R.weight a b else 0) where
  weight a b := if b∈T then R.weight a b else 0
  nonneg a b := by split <;> first | exact R.nonneg _ _ | exact le_rfl
  row _ := rfl
  col _ := rfl

end HyperbolicCoding.MatrixCoupling

end
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

noncomputable def pushWeight (q : A → ℝ) (f : A → B) (b : B) : ℝ :=
  ∑ a,if f a=b then q a else 0

lemma pushWeight_sum (q : A → ℝ) (f : A → B) :
    (∑ b,pushWeight q f b)=∑ a,q a := by
  unfold pushWeight
  rw [Finset.sum_comm]
  simp

omit [Fintype B] in
lemma pushWeight_nonneg (q : A → ℝ) (hq : ∀ a,0 ≤ q a) (f : A → B) (b : B) :
    0 ≤ pushWeight q f b := by
  apply Finset.sum_nonneg
  intro a _
  split <;> first | exact hq a | exact le_rfl

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

namespace MatrixCoupling
variable {p : A → ℝ} {q : B → ℝ}
noncomputable def pushRight [DecidableEq C] (R : MatrixCoupling p q) (f : B → C) :
    MatrixCoupling p (pushWeight q f) where
  weight a c := pushWeight (R.weight a) f c
  nonneg a c := pushWeight_nonneg _ (R.nonneg a) _ c
  row a := by rw [pushWeight_sum,R.row]
  col c := by
    simp only [pushWeight]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    split
    · exact R.col b
    · simp

end MatrixCoupling

end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Towers_PhaseAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped ENNReal BigOperators
variable {X : Type*} [MeasurableSpace X]

def phaseBlockStart (n : ℕ) {K : ℕ} (kr : Fin K × Fin n) : ℕ := n+kr.1.val*n+kr.2.val

noncomputable def phaseBlockBase (e : X ≃ᵐ X) (U : Set X) (n K : ℕ) (q : X → Fin n) : Set X :=
  ⋃ kr : Fin K × Fin n,(e^[phaseBlockStart n kr]) '' (U∩q ⁻¹' {kr.2})

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

def middleTower (e : X ≃ᵐ X) (U : Set X) (n K : ℕ) : Set X :=
  ⋃ kr : Fin K × Fin n,(e^[phaseBlockStart n kr]) '' U

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Towers_ScaledFiniteCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B : Type*} [MeasurableSpace X] [Fintype A] [Fintype B]

namespace MatrixCoupling
variable {p : A → ℝ} {q : B → ℝ}
noncomputable def scale (R : MatrixCoupling p q) (c : ℝ) (hc : 0 ≤ c) :
    MatrixCoupling (fun a => c*p a) (fun b => c*q b) where
  weight a b := c*R.weight a b
  nonneg a b := mul_nonneg hc (R.nonneg a b)
  row a := by rw [←Finset.mul_sum,R.row]
  col b := by rw [←Finset.mul_sum,R.col]
end MatrixCoupling

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X Y A : Type*} [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

def wordWindow {n m : ℕ} (i : ℕ) (hi : i+m≤n) (w : Fin n → A) : Fin m → A :=
  fun j => w ⟨j.val+i,by omega⟩

end HyperbolicCoding

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_DecodedTowerCopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X A C : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
  [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]

noncomputable def prefixNameCost {k t : ℕ} (F : C → A)
    (a : Fin k → C) (b : Fin (k+t) → A) : ℝ :=
  ∑ i : Fin k,symbolCost (F (a i)) (b (Fin.castAdd t i))

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A C : Type*} {k t r : ℕ}

noncomputable def normalizedPrefixCost {k t : ℕ} (F : C → A)
    (a : Fin k → C) (b : Fin (k+t) → A) : ℝ := prefixNameCost F a b/(k+t : ℕ)

end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_SanitizedTowerLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]

structure IIDCopyTest (μ : Measure X) (e : X ≃ᵐ X) (β : A → ℝ) (η : ℝ) where
  length : ℕ
  step : ℕ
  step_pos : 0 < step
  tolerance : ℝ
  tolerance_pos : 0 < tolerance
  transport : ∀ q : X → A,Measurable q →
    LawClose (μ.map (word e q length))
      (Measure.pi (fun _ : Fin length => finiteWeightLaw β)) tolerance →
    weightEntropy β-tolerance ≤ rate μ e q →
    ∀ n : ℕ,∃ R : MatrixCoupling (mass μ (word e q (n*step)))
      (productWordWeight β (n*step)), R.cost nameCost≤η*(n*step : ℕ)

variable [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
variable {C : Type*} [MeasurableSpace C] [Fintype C] [DecidableEq C]
  [MeasurableSingletonClass C] [Nonempty C]

noncomputable def MatrixCoupling.independent {B D : Type*} [Fintype B] [Fintype D]
    (u : B → ℝ) (v : D → ℝ) (hu : ∀ b,0≤u b) (hv : ∀ d,0≤v d)
    (hsu : ∑ b,u b=1) (hsv : ∑ d,v d=1) : MatrixCoupling u v where
  weight b d := u b*v d
  nonneg b d := mul_nonneg (hu b) (hv d)
  row b := by rw [←Finset.mul_sum,hsv,mul_one]
  col d := by rw [←Finset.sum_mul,hsu,one_mul]

end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_FullEntropyCopySequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]

def FiniteRateSupremum (μ : Measure X) (f : X → X) (h : ℝ) : Prop :=
  (∀ r : ℕ,∀ p : X → Fin (r+1),Measurable p → rate μ f p≤h) ∧
  (∀ ε : ℝ,0 < ε → ∃ r : ℕ,∃ p : X → Fin (r+1),Measurable p ∧ h-ε < rate μ f p)

def GoodIIDStage (μ : Measure X) (e : X ≃ᵐ X) (β : A → ℝ)
    {η : ℝ} (T : IIDCopyTest μ e β η) (n : ℕ) (q : X → A) : Prop :=
  Measurable q ∧
  LawClose (μ.map (word e q (max T.length n)))
    (Measure.pi (fun _ : Fin (max T.length n) => finiteWeightLaw β))
    (min T.tolerance (1/(n+1 : ℝ))) ∧
  weightEntropy β-T.tolerance ≤ rate μ e q

end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_IidFiniteWindowApprox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {A B : Type*} [MeasurableSpace A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]

def centeredWindow (N : ℕ) (w : ℤ → A) : Fin (2*N+1) → A := fun i => w ((i.val : ℤ)-N)

end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_CoarseConditionalBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding.MatrixCoupling
open scoped BigOperators
variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I] [DecidableEq I]
    (p : I → A → ℝ) (q : I → B → ℝ)

noncomputable def piCoupling (R : ∀ i,MatrixCoupling (p i) (q i)) :
    MatrixCoupling (fun a : I → A => ∏ i,p i (a i)) (fun b : I → B => ∏ i,q i (b i)) where
  weight a b := ∏ i,(R i).weight (a i) (b i)
  nonneg a b := Finset.prod_nonneg (fun i _ => (R i).nonneg _ _)
  row a := by
    rw [←Fintype.prod_sum]
    simp only [(R _).row]
  col b := by
    rw [←Fintype.prod_sum (fun i a => (R i).weight a (b i))]
    simp only [(R _).col]

end HyperbolicCoding.MatrixCoupling

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X Y A : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty A]

noncomputable def fullBlock (s n : ℕ) (q : Y → Fin (n*s) → A)
    (i : ℕ) (x : Y) : Fin s → A :=
  if hi : i<n then wordPack n s (q x) ⟨i,hi⟩ else fun _ => Classical.ofNonempty

end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_FiniteConditionalLawTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {Y A B : Type*} [Nonempty A]

def suffixPrefix (n L i : ℕ) (h : i+L<n) (w : Fin (n-i-1) → B) : Fin L → B :=
  fun a => w ⟨a.val,by omega⟩

def vectorFuture (n L i : ℕ) (h : i+L<n) (w : Fin n → B) : Fin L → B :=
  fun a => w ⟨i+1+a.val,by omega⟩

lemma block_inner_future_lt (M J L : ℕ) (I : Fin M) (j : Fin J) (hj : j.val+L<J) :
    (finProdFinEquiv (I,j)).val+L<M*J := by
  have hm := Nat.mul_le_mul_right J I.isLt
  change j.val+J*I.val+L<M*J
  nlinarith

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {Y A B : Type*} [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

noncomputable def insideCoarse [Nonempty B] (M J L : ℕ) (i : Fin (M*J))
    (w : Fin (M*J-i.val-1) → B) : Fin L → B :=
  if h : (finProdFinEquiv.symm i).2.val+L<J then
    suffixPrefix (M*J) L i.val (by
      have hh := block_inner_future_lt M J L (finProdFinEquiv.symm i).1
        (finProdFinEquiv.symm i).2 h
      simpa only [Prod.mk.eta,Equiv.apply_symm_apply] using hh) w
  else fun _ => Classical.ofNonempty

noncomputable def extendedCoarse [Nonempty B] (M J L i : ℕ)
    (w : Fin (M*J-i-1) → B) : Fin L → B :=
  if hi : i<M*J then insideCoarse M J L ⟨i,hi⟩ w else fun _ => Classical.ofNonempty

noncomputable def boundaryLoss (M J L : ℕ) (i : Fin (M*J)) : ℝ :=
  if (finProdFinEquiv.symm i).2.val+L<J then 0 else 1

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X Y A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

noncomputable def nestedOutput (M J s : ℕ) (V : Y → Fin M → Fin J → Fin s → A)
    (y : Y) : Fin ((M*J)*s) → A :=
  (wordPack (M*J) s).symm ((wordPack M J).symm (V y))

end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_FiniteVectorEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {A B : Type*} [MeasurableSpace A] [Fintype A]
    [MeasurableSpace B] [Fintype B]

noncomputable def finiteChannelLaw (N : ℕ) (P : (Fin N → A) → ℝ)
    (K : Fin N → A → B → ℝ) : Measure ((Fin N → A)×(Fin N → B)) :=
  finiteWeightLaw (fun vw => P vw.1*∏ i,K i (vw.1 i) (vw.2 i))

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X Y A B : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]

noncomputable def recodingKernel (μ : Measure X) [IsProbabilityMeasure μ] (p : X → A) (r : X → B)
    (hp : Measurable p) (hr : Measurable r) : A → B → ℝ := by
  classical
  exact (MatrixCoupling.observations μ r p hr hp).conditionalAssignment

noncomputable def recodingLaw (μ : Measure X) [IsProbabilityMeasure μ] (p : X → A) (r : X → B)
    (hp : Measurable p) (hr : Measurable r) (ν : Measure Y)
    (N : ℕ) (Q : Y → Fin N → A) : Measure ((Fin N → A)×(Fin N → B)) :=
  finiteChannelLaw N (mass ν Q) (fun _ => recodingKernel μ p r hp hr)

end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coupling_ActualFiniteRecodingBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X Y A : Type*}

noncomputable def nestedPack (M J s : ℕ) : (Fin ((M*J)*s) → A) ≃ (Fin M → Fin J → Fin s → A) :=
  (wordPack (M*J) s).trans (wordPack M J)

noncomputable def fineWordCost (J s : ℕ) (v w : Fin J → Fin s → A) : ℝ :=
  nameCost ((wordPack J s).symm v) ((wordPack J s).symm w)

end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_FixedWindowCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators
variable {A B C : Type*} {k t R : ℕ}

def blockWindow (b : Fin (k+t) → A) (i : Fin (k-2*R)) : Fin (2*R+1) → A :=
  fun j => b ⟨i.val+j.val,by have := i.isLt; have := j.isLt; omega⟩
def blockCenter (a : Fin k → C) (i : Fin (k-2*R)) : C :=
  a ⟨i.val+R,by have := i.isLt; omega⟩

noncomputable def decoderNameCost (H : C → B) (D : (Fin (2*R+1) → A) → B)
    (a : Fin k → C) (b : Fin (k+t) → A) : ℝ :=
  ∑ i : Fin (k-2*R),symbolCost (H (blockCenter a i)) (D (blockWindow b i))

noncomputable def fixedWindowCost (F : C → A) (H : C → B)
    (D : (Fin (2*R+1) → A) → B) (a : Fin k → C) (b : Fin (k+t) → A) : ℝ :=
  (prefixNameCost F a b+decoderNameCost H D a b)/(2*(k+t : ℕ))

end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_CenteredDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal NNReal Topology
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]
  [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]

structure GeneratingIIDStage (μ : Measure X) (e : X ≃ᵐ X) (β : A → ℝ)
    (α : ℕ → ℕ → X → Bool) (n : ℕ) where
  partition : X → A
  measurable_partition : Measurable partition
  iid : MeasurePreserving (orbitName e partition) μ (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β))
  radius : ℕ
  decoder : (Fin (2*radius+1) → A) → ((Fin (n+1) × Fin (n+1)) → Bool)
  error : μ.real {x | joinedBinary α (n+1) x≠decoder (centeredWindow radius (orbitName e partition x))} <
    (1/2 : ℝ)^(n+2)
  budget : ℝ
  budget_pos : 0 < budget
  budget_small : (2*radius+1 : ℕ)*budget≤(1/2 : ℝ)^(n+2)

end HyperbolicCoding

end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Coding_PositiveWeakBernoulliRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology

noncomputable def entropyPath (n : ℕ) (t : ℝ) (a : Fin (n+2)) : ℝ :=
  (1-t)*(if a=0 then 1 else 0)+t/(n+2 : ℝ)

end HyperbolicCoding

end

end OAI
end


