-- Prove2me | Definitions.Def_OAIQ2St000
-- name    : OAIQ2St000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T00:10:41.132348+00:00
-- url     : https://prove2.me/theorems/97d8e4e3-df80-4e67-8834-990381b4346b
-- title:
--   Definitions bundle OAIQ2St000 of the split of OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.StandardMapEntropy.main_entropy`, carved from OpenAI's openai/math development (OpenAI, *Positive Metric Entropy for the Standard Map at Large Parameters*, OpenAI Math Release, September 23, 2026, result family 146, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 507 declarations of OpenAI's Lean: 306 definitions, 11 inductive types or structures, 21 instances and 169 theorems. The definitions and types are `OAI.StandardMapEntropy.AmbientArray`, `OAI.StandardMapEntropy.ArrayTestIndex`, `OAI.StandardMapEntropy.BadGrowth`, `OAI.StandardMapEntropy.BridgeGrid`, `OAI.StandardMapEntropy.BridgeScalarControl`, `OAI.StandardMapEntropy.CommonGood`, `OAI.StandardMapEntropy.CompactWeightLimit`, `OAI.StandardMapEntropy.ControlledCurve`, `OAI.StandardMapEntropy.CriticalScaleSequence`, `OAI.StandardMapEntropy.CriticalScaleSequence.LimitLaws`, `OAI.StandardMapEntropy.CriticalScaleSequence.LimitLaws.selected`, `OAI.StandardMapEntropy.CriticalScaleSequence.backwardLaw`, `OAI.StandardMapEntropy.CriticalScaleSequence.backwardSum`, `OAI.StandardMapEntropy.CriticalScaleSequence.epsilon`, `OAI.StandardMapEntropy.CriticalScaleSequence.initialLaw`, `OAI.StandardMapEntropy.CriticalScaleSequence.multiLaw`, `OAI.StandardMapEntropy.CriticalScaleSequence.remainderLaw`, `OAI.StandardMapEntropy.CriticalScaleSequence.terminalLaw`, `OAI.StandardMapEntropy.CurveInterval`, `OAI.StandardMapEntropy.CurveInterval.comp`, `OAI.StandardMapEntropy.CurveInterval.length`, `OAI.StandardMapEntropy.CurveInterval.parameter`, `OAI.StandardMapEntropy.CurveInterval.velocity`, `OAI.StandardMapEntropy.CurvePlane`, `OAI.StandardMapEntropy.CurveStepBranch`, `OAI.StandardMapEntropy.CurveTree`, `OAI.StandardMapEntropy.DistanceArray`, `OAI.StandardMapEntropy.DyadicBridgeExclusions`, `OAI.StandardMapEntropy.DyadicTime`, `OAI.StandardMapEntropy.EndpointObservation`, `OAI.StandardMapEntropy.EndpointObservation.inWindow`, `OAI.StandardMapEntropy.EndpointObservation.value`, `OAI.StandardMapEntropy.ExteriorUnitRays`, `OAI.StandardMapEntropy.GoodIndex`, `OAI.StandardMapEntropy.HigherControl`, `OAI.StandardMapEntropy.LocalConfiguration`, `OAI.StandardMapEntropy.LocalConfiguration.Valid`, `OAI.StandardMapEntropy.LocalConfiguration.fast`, `OAI.StandardMapEntropy.LocalConfiguration.left`, `OAI.StandardMapEntropy.LocalConfiguration.reciprocalSum` and 277 more.
--
--   **Sources.** They come from these modules of lean/OAI/Dynamics/StandardMap, in whole or in part: `StandardMap_ArrayActions`, `StandardMap_ArrayAffinity`, `StandardMap_ArrayHalf`, `StandardMap_ArrayMoments`, `StandardMap_ArrayTests`, `StandardMap_ArrayTopology`, `StandardMap_BandCap`, `StandardMap_BandCoboundary`, `StandardMap_BandIntensity`, `StandardMap_BiCocycle`, `StandardMap_BridgeAveraging`, `StandardMap_BridgeExclusions`, `StandardMap_BridgeGrid`, `StandardMap_BridgeRealBound`, `StandardMap_BridgeSamples`, `StandardMap_BridgeScalars`, `StandardMap_BridgeVague`, `StandardMap_CancellationTheorem`, `StandardMap_CancellationVector`, `StandardMap_CappedTests`, `StandardMap_ClippedTests`, `StandardMap_ClosedEligibility`, `StandardMap_CocycleAlgebra`, `StandardMap_CosineNull`, `StandardMap_CriticalLaws`, `StandardMap_CriticalLimits`, `StandardMap_CriticalSequence`, `StandardMap_CurveCharts`, `StandardMap_CurveColumns`, `StandardMap_CurveCompose`, `StandardMap_CurveCore`, `StandardMap_CurveIterate`, `StandardMap_CurveLift`, `StandardMap_CurveOneStep`, `StandardMap_CurveSubdivision`, `StandardMap_DoublingPointwise`, `StandardMap_DyadicArrays`, `StandardMap_EndpointClasses`, `StandardMap_EndpointCovariance`, `StandardMap_EndpointDefinition`, `StandardMap_EndpointObservations`, `StandardMap_EntropyConjugacy`, `StandardMap_FastBridge`, `StandardMap_FineArrays`, `StandardMap_FixedDeficit`, `StandardMap_GraphJacobians`, `StandardMap_GridBridge`, `StandardMap_GridPartition`, `StandardMap_LiftDynamics`, `StandardMap_LimitActions`, `StandardMap_LimitBalance`, `StandardMap_LocalMidpointGrid`, `StandardMap_LocalScarcity`, `StandardMap_LogDerivativeCore`, `StandardMap_ManyGood`, `StandardMap_MeanCancellation`, `StandardMap_MeanDeficit`, `StandardMap_MeanGrowth`, `StandardMap_MiddleCount`, `StandardMap_MiddleObservationBridge`, `StandardMap_MiddlePrefixBridge`, `StandardMap_NonaffineLimits`, `StandardMap_PlaneGeometry`, `StandardMap_PlaneTransfer`, `StandardMap_ProductDistances`, `StandardMap_RealArrays`, `StandardMap_RealBridge`, `StandardMap_RemainderLaws`, `StandardMap_RescaledArrays`, `StandardMap_SampleLaws`, `StandardMap_ScaleAction`, `StandardMap_ScaleCancellation`, `StandardMap_ScaleEndpoints`, `StandardMap_ScaleEvaluation`, `StandardMap_ScaleLaws`, `StandardMap_SegmentObservations`, `StandardMap_ShapeClassification`, `StandardMap_ShapeComponents`, `StandardMap_ShapeCore`, `StandardMap_ShapeTopology`, `StandardMap_SmoothCap`, `StandardMap_TerminalCap`, `StandardMap_TerminalStrict`, `StandardMap_TestObservations`, `StandardMap_TorusDynamics`, `StandardMap_TorusIntegral`, `StandardMap_TorusObservations`, `StandardMap_TransferCore`, `StandardMap_TreeLine`, `StandardMap_TreeLocalAffine`, `StandardMap_TruncationArrays`, `StandardMap_VectorGrowth`, `StandardMap_WeightBridge`, `StandardMap_WeightSlow`, `StandardMap_WeightUnit`, `StandardMap_WeightedCompact`.
--
--   **Imports.** It imports the published bundle `Def_StandardMapEntropy`.
--
--   **Imported by** (directly, in this split): the statements `OAI.StandardMapEntropy.CriticalScaleSequence.capG_limit_balance`, `OAI.StandardMapEntropy.CriticalScaleSequence.dyadicBridge_aeselected`, `OAI.StandardMapEntropy.CriticalScaleSequence.noCancellation_aemulti`, `OAI.StandardMapEntropy.CriticalScaleSequence.noCancellation_aeterminal`, `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_cap_band`, `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_cap_nonpos`, `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_dilate`, `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_shape`, `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_translate`, `OAI.StandardMapEntropy.CriticalScaleSequence.terminal_cap_strict`, `OAI.StandardMapEntropy.CriticalScaleSequence.terminal_event_lower`, `OAI.StandardMapEntropy.CriticalScaleSequence.weight_middle_null`, `OAI.StandardMapEntropy.actual_backward_slice`, `OAI.StandardMapEntropy.actual_compact_graph_labels_full`, `OAI.StandardMapEntropy.actual_fast_bridge_product`, `OAI.StandardMapEntropy.bandMoment_order`, `OAI.StandardMapEntropy.eventually_meanDeficit_small` and `OAI.StandardMapEntropy.exists_critical_scale_sequence`; the proofs of `OAI.StandardMapEntropy.CriticalScaleSequence.capG_limit_balance`, `OAI.StandardMapEntropy.CriticalScaleSequence.dyadicBridge_aeselected`, `OAI.StandardMapEntropy.CriticalScaleSequence.noCancellation_aemulti`, `OAI.StandardMapEntropy.CriticalScaleSequence.noCancellation_aeterminal`, `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_cap_band`, `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_cap_nonpos`, `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_dilate`, `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_shape`, `OAI.StandardMapEntropy.CriticalScaleSequence.remainder_translate`, `OAI.StandardMapEntropy.CriticalScaleSequence.terminal_cap_strict`, `OAI.StandardMapEntropy.CriticalScaleSequence.terminal_event_lower`, `OAI.StandardMapEntropy.CriticalScaleSequence.weight_middle_null`, `OAI.StandardMapEntropy.actual_backward_slice`, `OAI.StandardMapEntropy.actual_compact_graph_labels_full`, `OAI.StandardMapEntropy.actual_fast_bridge_product`, `OAI.StandardMapEntropy.bandMoment_order`, `OAI.StandardMapEntropy.eventually_meanDeficit_small`, `OAI.StandardMapEntropy.exists_critical_scale_sequence` and `OAI.StandardMapEntropy.main_entropy`.
-- source:
--   OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 146; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Dynamics/StandardMap at commit adc7f12

import Mathlib
import Definitions.Def_StandardMapEntropy

section
-- module Solutions.OAIQ2_Std.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_LocalScarcity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StandardMapEntropy

@[simp] lemma sine_coe (x : ℝ) : sine (x : Circle) = Real.sin (2 * Real.pi * x) :=
  sine_periodic.lift_coe x

lemma continuous_sine : Continuous sine := by
  apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))).continuous_iff.mpr
  change Continuous (fun x : ℝ => sine (x : Circle))
  simpa only [sine_coe, Function.comp_def, Pi.mul_apply, id_eq] using
    Real.continuous_sin.comp (continuous_const.mul continuous_id)

instance circleVolumeProbability : IsProbabilityMeasure (volume : Measure Circle) := by
  constructor
  rw [AddCircle.measure_univ]
  norm_num

instance areaProbability : IsProbabilityMeasure area := by
  unfold area
  infer_instance

noncomputable def kick (k : ℝ) (x : Circle) : Circle := (k * sine x : ℝ)

lemma continuous_kick (k : ℝ) : Continuous (kick k) :=
  (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_const.mul continuous_sine)

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

noncomputable def sSolution (v : ℕ → ℝ) : ℕ → ℝ := linearSolution v 1 0

noncomputable def boundaryValue (v : ℕ → ℝ) (j : ℕ) : ℝ :=
  -sSolution v j / tSolution v j

noncomputable def liftedOrbit (k q₀ q₁ : ℝ) : ℕ → ℝ
  | 0 => q₀
  | 1 => q₁
  | n + 2 => phi k (liftedOrbit k q₀ q₁ (n + 1)) - liftedOrbit k q₀ q₁ n

@[simp] lemma liftedOrbit_zero (k q₀ q₁ : ℝ) : liftedOrbit k q₀ q₁ 0 = q₀ := rfl
@[simp] lemma liftedOrbit_one (k q₀ q₁ : ℝ) : liftedOrbit k q₀ q₁ 1 = q₁ := rfl

noncomputable def orbitCoefficient (k q₀ q₁ : ℝ) (n : ℕ) : ℝ :=
  potential k (liftedOrbit k q₀ q₁ n)

noncomputable def dirichletSolution (v : ℕ → ℝ) (j : ℕ) : ℕ → ℝ :=
  linearSolution v 1 (boundaryValue v j)

noncomputable def greenKernel (v : ℕ → ℝ) (j a b : ℕ) : ℝ :=
  tSolution v (min a b) * dirichletSolution v j (max a b)

noncomputable def drawdown (z : ℕ → ℝ) (c : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => max 0 (drawdown z c n + c + z n - z (n + 1))

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

noncomputable def forcingResponse (v F : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | n + 2 => v (n + 1) * forcingResponse v F (n + 1) - forcingResponse v F n + F (n + 1)

noncomputable def forcingBudget (M : ℝ) (F : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => M * forcingBudget M F n + |F (n + 1)|

noncomputable def orbitDisplacement (k q₀ θ δ : ℝ) (n : ℕ) : ℝ :=
  liftedOrbit k q₀ (θ + δ) n - liftedOrbit k q₀ θ n

noncomputable def orbitForcing (k q₀ θ δ : ℝ) (n : ℕ) : ℝ :=
  phi k (liftedOrbit k q₀ (θ + δ) n) - phi k (liftedOrbit k q₀ θ n) -
    orbitCoefficient k q₀ θ n * orbitDisplacement k q₀ θ δ n

noncomputable def phiSecond (k x : ℝ) : ℝ := -(2 * Real.pi) ^ 2 * k * Real.sin (2 * Real.pi * x)

noncomputable def rescaledOrbit (k q₀ θ L ξ : ℝ) (n : ℕ) : ℝ :=
  liftedOrbit k q₀ (θ + ξ / L) n

noncomputable def rescaledD₁ (k q₀ θ L ξ : ℝ) (n : ℕ) : ℝ :=
  tSolution (orbitCoefficient k q₀ (θ + ξ / L)) n / L

noncomputable def rescaledD₂ (k q₀ θ L ξ : ℝ) : ℕ → ℝ :=
  forcingResponse (orbitCoefficient k q₀ (θ + ξ / L))
    (fun i => phiSecond k (rescaledOrbit k q₀ θ L ξ i) * (rescaledD₁ k q₀ θ L ξ i) ^ 2)

noncomputable def phiThird (k x : ℝ) : ℝ := -(2 * Real.pi) ^ 3 * k * Real.cos (2 * Real.pi * x)
noncomputable def phiFourth (k x : ℝ) : ℝ := (2 * Real.pi) ^ 4 * k * Real.sin (2 * Real.pi * x)
noncomputable def phiFifth (k x : ℝ) : ℝ := (2 * Real.pi) ^ 5 * k * Real.cos (2 * Real.pi * x)

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

noncomputable def derivativeMajorant : ℝ := (1 + 2 * Real.pi) ^ (4 : ℕ)

def HigherControl (k : ℝ) : Prop :=
  growthBase k * (1 + 8 * Real.pi) * (growthBase k ^ (-goodExponent)) ^ (2 : ℕ) ≤ 1 / 2 ∧
  512 * (derivativeMajorant * growthBase k) * (growthBase k ^ (-goodExponent)) ^ (2 : ℕ) ≤ 1

section InverseChains
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [HasSummableGeomSeries R]

def inverseJet₁ (G B₁ : R) : R := -(G * B₁ * G)
def inverseJet₂ (G B₁ B₂ : R) : R :=
  2 * G * B₁ * G * B₁ * G - G * B₂ * G

def inverseJet₃ (G B₁ B₂ B₃ : R) : R :=
  -(6 * G * B₁ * G * B₁ * G * B₁ * G) +
  3 * G * B₂ * G * B₁ * G + 3 * G * B₁ * G * B₂ * G - G * B₃ * G

def inverseJet₄ (G B₁ B₂ B₃ B₄ : R) : R :=
  24 * G * B₁ * G * B₁ * G * B₁ * G * B₁ * G -
  12 * G * B₂ * G * B₁ * G * B₁ * G -
  12 * G * B₁ * G * B₂ * G * B₁ * G -
  12 * G * B₁ * G * B₁ * G * B₂ * G +
  6 * G * B₂ * G * B₂ * G + 4 * G * B₃ * G * B₁ * G +
  4 * G * B₁ * G * B₃ * G - G * B₄ * G

end InverseChains

noncomputable def dirichletMatrix (v : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun a b => (if a = b then v (a.val + 1) else 0) -
    (if a.val = b.val + 1 then 1 else 0) - (if b.val = a.val + 1 then 1 else 0)

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

noncomputable def matrixEntryCLM (n : ℕ) (a b : Fin n) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
  (show Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ from {
    toFun := fun A => A a b
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }).toContinuousLinearMap

noncomputable def rescaledMatrix (k q₀ θ L ξ : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  dirichletMatrix (fun a => potential k (rescaledOrbit k q₀ θ L ξ a)) n

noncomputable def rescaledDiagonal (v : ℝ → ℝ → ℝ → ℝ → ℝ → ℕ → ℝ)
    (k q₀ θ L ξ : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun a : Fin n => v k q₀ θ L ξ (a.val + 1))

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

def finTotal {n : ℕ} (f : Fin n → ℝ) (i : ℕ) : ℝ :=
  if h : i < n then f ⟨i, h⟩ else 0
@[simp] lemma finTotal_coe {n : ℕ} (f : Fin n → ℝ) (i : Fin n) : finTotal f i.val = f i := by
  simp [finTotal, i.isLt]

noncomputable def boundaryChain {n : ℕ} (U : Fin n → ℝ)
    (G : Matrix (Fin n) (Fin n) ℝ) (s : ℕ) (v : Fin (s + 1) → Fin n → ℝ)
    (a : Fin (s + 1) → Fin n) : ℝ :=
  U (a 0) * (∏ i, v i (a i)) *
    (∏ i : Fin s, G (a i.castSucc) (a i.succ)) * U (a (Fin.last s))

noncomputable def matrixChain {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) :
    (s : ℕ) → (Fin (s + 1) → Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ
  | 0, v => G * Matrix.diagonal (v 0) * G
  | s + 1, v => G * Matrix.diagonal (v 0) * matrixChain G s (fun i => v i.succ)

noncomputable def matrixPath {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (s : ℕ) (v : Fin (s + 1) → Fin n → ℝ) (a : Fin (s + 1) → Fin n)
    (row col : Fin n) : ℝ :=
  G row (a 0) * (∏ i, v i (a i)) *
    (∏ i : Fin s, G (a i.castSucc) (a i.succ)) * G (a (Fin.last s)) col

noncomputable def inverseFourthMajorant (A : ℝ) : ℝ :=
  24 * (8 * A) ^ 4 + 36 * (8 * A) ^ 3 + 14 * (8 * A) ^ 2 + 8 * A

noncomputable def rescaledPotentialJets (k q₀ θ L ξ : ℝ) (n : ℕ) : Fin 4 → Fin n → ℝ :=
  ![fun a => rescaledV₁ k q₀ θ L ξ (a.val + 1),
    fun a => rescaledV₂ k q₀ θ L ξ (a.val + 1),
    fun a => rescaledV₃ k q₀ θ L ξ (a.val + 1),
    fun a => rescaledV₄ k q₀ θ L ξ (a.val + 1)]

noncomputable def scalarReciprocalJet (i : ℕ) (d : ℕ → ℝ) : ℝ := match i with
  | 0 => (d 0)⁻¹
  | 1 => inverseJet₁ (d 0)⁻¹ (d 1)
  | 2 => inverseJet₂ (d 0)⁻¹ (d 1) (d 2)
  | 3 => inverseJet₃ (d 0)⁻¹ (d 1) (d 2) (d 3)
  | _ => inverseJet₄ (d 0)⁻¹ (d 1) (d 2) (d 3) (d 4)

noncomputable def scalarProductJet (i : ℕ) (n d : ℕ → ℝ) : ℝ := match i with
  | 0 => n 0 * d 0
  | 1 => n 1 * d 0 + n 0 * d 1
  | 2 => n 2 * d 0 + 2 * n 1 * d 1 + n 0 * d 2
  | 3 => n 3 * d 0 + 3 * n 2 * d 1 + 3 * n 1 * d 2 + n 0 * d 3
  | _ => n 4 * d 0 + 4 * n 3 * d 1 + 6 * n 2 * d 2 + 4 * n 1 * d 3 + n 0 * d 4

noncomputable def rescaledTJet (p : ℕ) (k q₀ θ L ξ : ℝ) (l : ℕ) : ℝ := match p with
  | 0 => rescaledD₁ k q₀ θ L ξ l
  | 1 => rescaledD₂ k q₀ θ L ξ l
  | 2 => rescaledD₃ k q₀ θ L ξ l
  | 3 => rescaledD₄ k q₀ θ L ξ l
  | _ => rescaledD₅ k q₀ θ L ξ l

noncomputable def terminalQuotient (k q₀ θ L ξ : ℝ) (j : ℕ) : ℝ :=
  tSolution (orbitCoefficient k q₀ (θ + ξ / L)) (j - 1) /
    tSolution (orbitCoefficient k q₀ (θ + ξ / L)) j

noncomputable def oppositeLimitDifference (p : Polynomial ℝ) (A B C β z b : ℝ) (h : ℝ) : ℝ :=
  p.eval h * b ^ 2 * (Real.cos (2 * Real.pi * (z + b * h))) ^ 2 -
    (2 / b * (2 * A * h + B) * Real.cos (2 * Real.pi * (z + b * h)) -
      2 * Real.pi * (A * h ^ 2 + B * h + C) * Real.sin (2 * Real.pi * (z + b * h)) - 4 * β)

noncomputable def taylorPolynomialAtZero (f : ℝ → ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (iteratedDeriv i f 0 / (i.factorial : ℝ))

open Filter
open scoped Topology

noncomputable def coefficientPolynomial {d : ℕ} (c : Fin d → ℝ) : Polynomial ℝ :=
  ∑ i : Fin d, Polynomial.monomial i.val (c i)

open Metric

noncomputable def scaledTaylorPolynomial (f : ℝ → ℝ) (a : ℝ) : Polynomial ℝ :=
  (taylorPolynomialAtZero f 3).comp (Polynomial.C a * Polynomial.X)

noncomputable def localReciprocalTerm (k q₀ θ L h : ℝ) (j : ℕ) : ℝ :=
  1 / ((rescaledD₁ k q₀ θ L h j) ^ 2 *
    (Real.cos (2 * Real.pi * liftedOrbit k q₀ (θ + h / L) j) +
      (2 - terminalQuotient k q₀ θ L h j) / (2 * Real.pi * k)))

section

noncomputable def rescaledPotentialJet (p : ℕ) (k q₀ θ L h : ℝ) (j : ℕ) : ℝ := match p with
  | 0 => potential k (rescaledOrbit k q₀ θ L h j)
  | 1 => rescaledV₁ k q₀ θ L h j
  | 2 => rescaledV₂ k q₀ θ L h j
  | 3 => rescaledV₃ k q₀ θ L h j
  | _ => rescaledV₄ k q₀ θ L h j

noncomputable def normalizedSlope (k q₀ θ L : ℝ) (j : ℕ) (h : ℝ) : ℝ :=
  deriv (fun x => rescaledOrbit k q₀ θ L x j) h / (|tSolution (orbitCoefficient k q₀ θ) j| / L)

noncomputable def shiftedCosine (k q₀ θ L : ℝ) (j : ℕ) (h : ℝ) : ℝ :=
  (potential k (rescaledOrbit k q₀ θ L h j) - terminalQuotient k q₀ θ L h j) / (2 * Real.pi * k)

noncomputable def slowDenominator (k q₀ θ L : ℝ) (j : ℕ) (h : ℝ) : ℝ :=
  (normalizedSlope k q₀ θ L j h) ^ 2 * shiftedCosine k q₀ θ L j h

end

section

noncomputable def slowDenominatorModel (Q E : ℝ → ℝ) (K r h : ℝ) : ℝ :=
  (deriv Q h / r) ^ 2 * (Real.cos (2 * Real.pi * Q h) + (2 - E h) / K)

end

end StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace StandardMapEntropy

noncomputable def coefficientScale {ι : Type*} (a b c d : ι → ℝ) (n : ι) : ℝ :=
  max (max |a n| |b n|) (max |c n| (d n))

noncomputable def centerPhase (Q : ℝ → ℝ) (x : ℝ) : ℝ := Q x - ⌊Q 0⌋

noncomputable def phaseReciprocal (Q E : ℝ → ℝ) (d x : ℝ) : ℝ :=
  1 / ((deriv Q x) ^ 2 * (Real.cos (2 * Real.pi * Q x) + (2 - E x) * d))

structure RescaledPath where
  k : ℝ
  q₀ : ℝ
  θ : ℝ
  L : ℝ
  sign : ℝ
  j : ℕ

namespace RescaledPath
noncomputable def size (P : RescaledPath) : ℝ := |tSolution (orbitCoefficient P.k P.q₀ P.θ) P.j|
noncomputable def ratio (P : RescaledPath) : ℝ := P.size / P.L
noncomputable def phase (P : RescaledPath) : ℝ → ℝ :=
  centerPhase (fun x => rescaledOrbit P.k P.q₀ P.θ P.L (P.sign * x) P.j)
noncomputable def quotient (P : RescaledPath) (x : ℝ) : ℝ :=
  terminalQuotient P.k P.q₀ P.θ P.L (P.sign * x) P.j
noncomputable def denominator (P : RescaledPath) (x : ℝ) : ℝ :=
  slowDenominator P.k P.q₀ P.θ P.L P.j (P.sign * x)

def Admissible (P : RescaledPath) : Prop :=
  1 ≤ P.k ∧ HigherControl P.k ∧ |P.sign| = 1 ∧ P.size ≤ P.L ∧
    ∃ b, GoodIndex (growthBase P.k) (orbitCoefficient P.k P.q₀ P.θ) b P.j

end RescaledPath
noncomputable def cubicError (k : ℝ) : ℝ :=
  inverseFourthMajorant (52 * derivativeMajorant) / 12 * growthBase k ^ (-(9 / 5 : ℝ)) +
    16 * growthBase k ^ (-(77 / 100 : ℝ))
noncomputable def cubicFineError (k r : ℝ) : ℝ :=
  inverseFourthMajorant (52 * derivativeMajorant) / 12 * growthBase k ^ (-(9 / 5 : ℝ)) +
    16 / r ^ 2 * growthBase k ^ (1 - 3 * goodExponent)
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
-- module Solutions.OAIQ2_Std.StandardMap_PlaneGeometry
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
noncomputable def wedge (z w : ℂ) : ℝ := z.re * w.im - z.im * w.re
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
-- module Solutions.OAIQ2_Std.StandardMap_PlaneTransfer
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
-- module Solutions.OAIQ2_Std.StandardMap_TransferCore
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

noncomputable def transferStep (v : ℝ) : ℂ →L[ℝ] ℂ :=
  { toLinearMap :=
      { toFun := fun z => ⟨v*z.re-z.im,z.re⟩
        map_add' := by intro z w; apply Complex.ext <;> simp ; ring
        map_smul' := by intro t z; apply Complex.ext <;> simp ; ring }
    cont := by
      exact Complex.equivRealProdCLM.symm.continuous.comp
        (((continuous_const.mul Complex.continuous_re).sub Complex.continuous_im).prodMk Complex.continuous_re) }
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
noncomputable def transferProductInv (v : ℕ → ℝ) : ℕ → (ℂ →L[ℝ] ℂ)
  | 0 => ContinuousLinearMap.id ℝ ℂ
  | n+1 => (transferProductInv v n).comp (transferStepInv (v (n+1)))
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
-- module Solutions.OAIQ2_Std.StandardMap_LiftDynamics
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
-- module Solutions.OAIQ2_Std.StandardMap_CurveCore
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
abbrev CurvePlane := ℝ × ℝ

structure ControlledCurve (ε : ℝ) where
  map : ℝ → CurvePlane
  velocity : ℝ → CurvePlane
  hasDeriv : ∀ t, HasDerivAt map (velocity t) t
  continuous_velocity : Continuous velocity
  speed : ∀ t ∈ Icc (0:ℝ) 1, ‖velocity t‖ ≤ ε
  variation : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1,
    ‖velocity s-velocity t‖ ≤ ε*|s-t|

def affineParameter (a b t : ℝ) : ℝ := a+(b-a)*t
lemma affineParameter_mem (a b : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) : affineParameter a b t∈Icc (0:ℝ) 1 := by
  dsimp [affineParameter]
  rcases ht with ⟨ht0,ht1⟩
  constructor <;> nlinarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_CurveCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology Classical
namespace StandardMapEntropy
structure CurveInterval where
  left : ℝ
  right : ℝ
  left_nonneg : 0≤left
  ordered : left≤right
  right_le : right≤1
namespace CurveInterval
def length (I : CurveInterval) : ℝ:=I.right-I.left
def parameter (I : CurveInterval) : ℝ → ℝ:=affineParameter I.left I.right
lemma length_nonneg (I : CurveInterval) : 0≤I.length := sub_nonneg.mpr I.ordered
lemma parameter_mem (I : CurveInterval) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    I.parameter t∈Icc (0:ℝ) 1 := affineParameter_mem _ _ I.left_nonneg I.ordered I.right_le ht
lemma parameter_sub (I : CurveInterval) (s t : ℝ) :
    I.parameter s-I.parameter t=I.length*(s-t) := by dsimp [parameter,affineParameter,length]; ring
def velocity (I : CurveInterval) (v : ℝ → CurvePlane) (t : ℝ) : CurvePlane:=I.length • v (I.parameter t)
end CurveInterval

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_CurveSubdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology Classical
namespace StandardMapEntropy
noncomputable def subdivisionInterval (N : ℕ) (hN : 0<N) (i : Fin N) : CurveInterval where
  left := (i:ℝ)/N
  right := ((i:ℝ)+1)/N
  left_nonneg := by positivity
  ordered := by apply div_le_div_of_nonneg_right; linarith; positivity
  right_le := by
    have hNr:0<(N:ℝ) := by exact_mod_cast hN
    apply (div_le_one hNr).mpr
    exact_mod_cast (Nat.succ_le_of_lt i.isLt)
noncomputable def pointCurveInterval : CurveInterval:=⟨0,0,le_rfl,le_rfl,by norm_num⟩
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_CurveCompose
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
namespace CurveInterval
noncomputable def comp (I J : CurveInterval) : CurveInterval where
  left := I.parameter J.left
  right := I.parameter J.right
  left_nonneg := (I.parameter_mem ⟨J.left_nonneg,J.ordered.trans J.right_le⟩).1
  ordered := by
    have h:0≤I.length*(J.right-J.left) := mul_nonneg I.length_nonneg J.length_nonneg
    rw [← I.parameter_sub] at h
    exact sub_nonneg.mp h
  right_le := (I.parameter_mem ⟨J.left_nonneg.trans J.ordered,J.right_le⟩).2
end CurveInterval
noncomputable def wrappedCurveCenter (c x : CurvePlane) (i : Fin 7×Fin 7) : CurvePlane :=
  (c.1+(⌊x.1-c.1⌋+(i.1:ℤ)-3:ℤ), c.2+(⌊x.2-c.2⌋+(i.2:ℤ)-3:ℤ))
def wrappedBox (δ : ℝ) (c x : CurvePlane) : Prop :=
  ∃m:ℤ×ℤ,‖x-(c.1+(m.1:ℝ),c.2+(m.2:ℝ))‖≤δ
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_CurveLift
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
def pairTransfer (a : ℝ) (v : CurvePlane) : CurvePlane := (a*v.1-v.2,v.1)
noncomputable def liftCurveVelocity (k : ℝ) (g v : ℝ → CurvePlane) (t : ℝ) : CurvePlane :=
  pairTransfer (potential k (g t).1) (v t)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_CurveOneStep
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
abbrev CurveStepBranch (N : ℕ) := Fin N × (Fin 7 × Fin 7) × Fin 4
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_CurveIterate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology Classical
namespace StandardMapEntropy
def CurveTree (N : ℕ) : ℕ  →  Type
  | 0 => Unit
  | n+1 => CurveTree N n × CurveStepBranch N
instance curveTreeFintype (N n : ℕ) : Fintype (CurveTree N n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => exact @instFintypeProd _ _ ih inferInstance
noncomputable def fullCurveInterval : CurveInterval := ⟨0,1,le_rfl,by norm_num,le_rfl⟩
noncomputable def curveIterVelocity (k : ℝ) (g v : ℝ → CurvePlane) : ℕ  →  ℝ  →  CurvePlane
  | 0 => v
  | n+1 => liftCurveVelocity k ((liftStep k)^[n] ∘ g) (curveIterVelocity k g v n)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_SegmentObservations
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
-- module Solutions.OAIQ2_Std.StandardMap_LogDerivativeCore
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
-- module Solutions.OAIQ2_Std.StandardMap_GraphJacobians
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
namespace StandardMapEntropy
noncomputable def planeDual (a b : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  a • ContinuousLinearMap.fst ℝ ℝ ℝ+b • ContinuousLinearMap.snd ℝ ℝ ℝ
noncomputable def planeMatrix (a b c d : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (planeDual a b).prod (planeDual c d)
@[simp] lemma planeDual_apply (a b : ℝ) (z : ℝ × ℝ) : planeDual a b z=a*z.1+b*z.2 := rfl
@[simp] lemma planeMatrix_apply (a b c d : ℝ) (z : ℝ × ℝ) :
    planeMatrix a b c d z=(a*z.1+b*z.2,c*z.1+d*z.2) := rfl
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_TorusIntegral
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
-- module Solutions.OAIQ2_Std.StandardMap_TorusDynamics
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
lemma continuous_torusStep (k : ℝ) : Continuous (torusStep k) :=
  (((continuous_fst.nsmul 2).add ((continuous_kick k).comp continuous_fst)).sub continuous_snd).prodMk continuous_fst
lemma continuous_torusStep_symm (k : ℝ) : Continuous (torusStep k).symm :=
  continuous_snd.prodMk (((continuous_snd.nsmul 2).add ((continuous_kick k).comp continuous_snd)).sub continuous_fst)
lemma measurePreserving_recurrenceCoordinates : MeasurePreserving recurrenceCoordinates area area := by
  unfold area
  apply (MeasurePreserving.id (volume : Measure Circle)).skew_product
  · exact measurable_fst.sub measurable_snd
  · exact Eventually.of_forall fun x => (Measure.measurePreserving_sub_left (volume : Measure Circle) x).map_eq
noncomputable def torusStep_measurableEquiv (k : ℝ) : MeasurableEquiv Torus Torus where
  toEquiv := torusStep k
  measurable_toFun := (continuous_torusStep k).measurable
  measurable_invFun := (continuous_torusStep_symm k).measurable
noncomputable def torusIter (k : ℝ) (i : ℤ) : Torus → Torus := ((torusStep k)^i : Equiv.Perm Torus)
@[simp] lemma torusIter_zero (k : ℝ) (z : Torus) : torusIter k 0 z=z := by simp [torusIter]
lemma continuous_torusIter (k : ℝ) (i : ℤ) : Continuous (torusIter k i) := by
  cases i with
  | ofNat n =>
      change Continuous (torusIter k (n : ℤ))
      simpa only [torusIter,zpow_natCast,Equiv.Perm.coe_pow] using (continuous_torusStep k).iterate n
  | negSucc n => simpa only [torusIter,zpow_negSucc,← inv_pow,Equiv.Perm.inv_def,Equiv.Perm.coe_pow] using
      (continuous_torusStep_symm k).iterate (n+1)
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
-- module Solutions.OAIQ2_Std.StandardMap_GridPartition
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
lemma circleRep_mem (x : Circle) : circleRep x∈Ico (0:ℝ) 1 := by
  have h:=(AddCircle.equivIco 1 0 x).property
  simpa only [zero_add,circleRep] using h
lemma measurable_circleRep : Measurable circleRep := by
  exact measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable
@[simp] lemma coe_circleRep (x : Circle) : (circleRep x : Circle)=x := AddCircle.coe_equivIco
@[simp] lemma circleRep_coe (x : ℝ) : circleRep (x:Circle)=Int.fract x := by
  simpa only [div_one,mul_one,circleRep] using AddCircle.coe_equivIco_mk_apply (1:ℝ) x
noncomputable def torusRep (z:Torus) : CurvePlane := (circleRep z.1,circleRep z.2)
@[simp] lemma liftProjection_torusRep (z:Torus) : liftProjection (torusRep z)=z := by
  ext <;> simp [liftProjection,torusRep]
noncomputable def gridIndex (Q:ℕ) (hQ:0<Q) (x:Circle) : Fin Q :=
  ⟨⌊(Q:ℝ)*circleRep x⌋₊,(Nat.floor_lt (mul_nonneg (Nat.cast_nonneg _) (circleRep_mem x).1)).mpr
    (by nlinarith [(circleRep_mem x).2,(Nat.cast_pos.mpr hQ : (0:ℝ)<Q)])⟩
lemma measurable_gridIndex (Q:ℕ) (hQ:0<Q) : Measurable (gridIndex Q hQ) := by
  apply measurable_to_countable
  intro y
  have h:Measurable (fun x:Circle=>⌊(Q:ℝ)*circleRep x⌋₊) :=
    Nat.measurable_floor.comp (measurable_const.mul measurable_circleRep)
  convert h (measurableSet_singleton (gridIndex Q hQ y).val) using 1
  ext x
  simp only [mem_preimage,mem_singleton_iff,Fin.ext_iff,gridIndex]
noncomputable def gridLabel (Q:ℕ) (hQ:0<Q) (z:Torus) : Fin (Q*Q+1) :=
  (finProdFinEquiv (gridIndex Q hQ z.1,gridIndex Q hQ z.2)).castSucc
lemma measurable_gridLabel (Q:ℕ) (hQ:0<Q) : Measurable (gridLabel Q hQ) := by
  exact (measurable_of_finite (fun i:Fin Q×Fin Q=>(finProdFinEquiv i).castSucc)).comp
    (((measurable_gridIndex Q hQ).comp measurable_fst).prodMk ((measurable_gridIndex Q hQ).comp measurable_snd))
noncomputable def gridPartition (Q:ℕ) (hQ:0<Q) : FinitePartition (Q*Q) :=
  ⟨gridLabel Q hQ,measurable_gridLabel Q hQ⟩
noncomputable def gridInterval (Q:ℕ) (hQ:0<Q) (i:Fin Q) : CurveInterval where
  left := (i:ℝ)/(Q:ℝ)
  right := ((i:ℝ)+1)/(Q:ℝ)
  left_nonneg := by positivity
  ordered := div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  right_le := (div_le_one (Nat.cast_pos.mpr hQ)).mpr (by exact_mod_cast i.isLt)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_ClosedEligibility
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

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_TorusObservations
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
lemma cosine_periodic : Function.Periodic (fun x : ℝ => Real.cos (2*Real.pi*x)) 1 := by
  intro x
  dsimp only
  rw [show 2*Real.pi*(x+1)=2*Real.pi*x+2*Real.pi by ring]
  exact Real.cos_add_two_pi _
noncomputable def cosine (x : Circle) : ℝ := cosine_periodic.lift x
@[simp] lemma cosine_coe (x : ℝ) : cosine (x : Circle)=Real.cos (2*Real.pi*x) :=
  cosine_periodic.lift_coe x
noncomputable def torusPotential (k : ℝ) (x : Circle) : ℝ := 2+(2*Real.pi*k)*cosine x
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
-- module Solutions.OAIQ2_Std.StandardMap_CurveColumns
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
def complexPair (z:CurvePlane) : ℂ := ⟨z.1,z.2⟩
noncomputable def horizontalVelocity (k:ℝ) (n:ℕ) (z:CurvePlane) : CurvePlane :=
  curveIterVelocity k (fun t=>(t,z.2)) (fun _=>(1,0)) n z.1
noncomputable def verticalVelocity (k:ℝ) (n:ℕ) (z:CurvePlane) : CurvePlane :=
  curveIterVelocity k (fun t=>(z.1,t)) (fun _=>(0,1)) n z.2
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_CocycleAlgebra
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
-- module Solutions.OAIQ2_Std.StandardMap_BiCocycle
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
-- module Solutions.OAIQ2_Std.StandardMap_ProductDistances
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
-- module Solutions.OAIQ2_Std.StandardMap_SmoothCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped Interval Topology
namespace StandardMapEntropy
noncomputable def capSlope (u : ℝ) : ℝ := 1-Real.smoothTransition (10000*u-1)
noncomputable def capPrimitive (u : ℝ) : ℝ := ∫ t in (0:ℝ)..u,capSlope t
noncomputable def capBase : ℝ := capPrimitive (1/5000)
noncomputable def entropyCap (α u : ℝ) : ℝ :=
  α*capPrimitive u+(1-α*capBase)*Real.smoothTransition (10000*u-2)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_ManyGood
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
-- module Solutions.OAIQ2_Std.StandardMap_CancellationVector
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
-- module Solutions.OAIQ2_Std.StandardMap_CancellationTheorem
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
noncomputable def cancellationConstant : ℝ := 2*(4:ℝ)^10000000
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_DoublingPointwise
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
-- module Solutions.OAIQ2_Std.StandardMap_MeanDeficit
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
noncomputable def meanDeficit (k : ℝ) (n : ℕ) : ℝ :=
  1-(∫ z, productDistance k z 0 (n:ℤ) ∂area)/(n:ℝ)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_MeanCancellation
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
noncomputable def doublingConstant : ℝ := 10000000001+4*cancellationConstant
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_MeanGrowth
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
-- module Solutions.OAIQ2_Std.StandardMap_CosineNull
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
-- module Solutions.OAIQ2_Std.StandardMap_FixedDeficit
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
-- module Solutions.OAIQ2_Std.StandardMap_CriticalSequence
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
-- module Solutions.OAIQ2_Std.StandardMap_DyadicArrays
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
-- module Solutions.OAIQ2_Std.StandardMap_ArrayTests
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
    congr 2
    change (t:ℝ)-(s:ℝ)=((t:ℝ)+(r:ℝ))-((s:ℝ)+(r:ℝ))
    ring⟩
lemma continuous_arrayTranslate (r : DyadicTime) : Continuous (arrayTranslate r) := by
  apply Continuous.subtype_mk
  apply continuous_pi; intro s
  apply continuous_pi; intro t
  exact continuous_arrayEval (s+r) (t+r)
@[simp] lemma arrayTranslate_zero (d : DistanceArray) : arrayTranslate 0 d=d := by
  apply Subtype.ext
  funext s t
  simp [arrayTranslate]
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
noncomputable def arrayV (s t : DyadicTime) (d : DistanceArray) : ℝ :=
  (arrayShortfall s (dyadicMid s t) d-arrayShortfall (dyadicMid s t) t d)^2
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
-- module Solutions.OAIQ2_Std.StandardMap_ArrayAffinity
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
noncomputable def arrayTest (i : ArrayTestIndex) (d : DistanceArray) : ℝ := arrayJ i.val.1 i.val.2 d+arrayV i.val.1 i.val.2 d
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_RescaledArrays
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
-- module Solutions.OAIQ2_Std.StandardMap_SampleLaws
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
-- module Solutions.OAIQ2_Std.StandardMap_ArrayMoments
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
-- module Solutions.OAIQ2_Std.StandardMap_ScaleLaws
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
-- module Solutions.OAIQ2_Std.StandardMap_CriticalLaws
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
-- module Solutions.OAIQ2_Std.StandardMap_NonaffineLimits
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
instance instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray (μ : Measure DistanceArray) [IsFiniteMeasure μ] : IsFiniteMeasure (nonaffinePart μ) := inferInstanceAs (IsFiniteMeasure (μ.comap Subtype.val))
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_CriticalLimits
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
-- module Solutions.OAIQ2_Std.StandardMap_ArrayActions
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
  ext d
  change nonaffineDilate d ∈ K ↔ ∃ u ∈ K,u.val=arrayDilate d.val
  exact ⟨fun hd => ⟨nonaffineDilate d,hd,rfl⟩,fun ⟨u,hu,he⟩ => (Subtype.ext he : u=nonaffineDilate d) ▸ hu⟩
noncomputable def nonaffineDilation : CocompactMap NonAffineArray NonAffineArray where
  toFun := nonaffineDilate
  continuous_toFun := continuous_nonaffineDilate
  cocompact_tendsto' := (isProperMap_iff_tendsto_cocompact.mp proper_nonaffineDilate).2

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
-- module Solutions.OAIQ2_Std.StandardMap_LimitActions
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
-- module Solutions.OAIQ2_Std.StandardMap_ArrayTopology
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
-- module Solutions.OAIQ2_Std.StandardMap_LimitBalance
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
-- module Solutions.OAIQ2_Std.StandardMap_RealArrays
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
-- module Solutions.OAIQ2_Std.StandardMap_ArrayHalf
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
lemma arrayDilate_half (d : DistanceArray) (hu : UnitArray d) : arrayDilate (arrayHalf d hu)=d := by
  apply Subtype.ext; funext s t
  change (2*d.val (dyadicHalf (s+s)) (dyadicHalf (t+t)))/2=d.val s t
  rw [dyadicHalf_double,dyadicHalf_double]; ring
lemma arrayHalf_dilate (d : DistanceArray) (hu : UnitArray d) : arrayHalf (arrayDilate d) (arrayDilate_unit d hu)=d := by
  apply Subtype.ext; funext s t
  change 2*(d.val (dyadicHalf s+dyadicHalf s) (dyadicHalf t+dyadicHalf t)/2)=d.val s t
  rw [dyadicHalf_add_self,dyadicHalf_add_self]; ring
noncomputable def nonaffineHalfOn (d : {d : NonAffineArray // UnitArray d.val}) : NonAffineArray :=
  ⟨arrayHalf d.val.val d.property,by
    intro ha
    have hh := (arrayDilate_mem_affine_iff _).mpr ha
    rw [arrayDilate_half] at hh
    exact d.val.property hh⟩
lemma continuous_nonaffineHalfOn : Continuous nonaffineHalfOn := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi; intro s
  apply continuous_pi; intro t
  exact continuous_const.mul ((continuous_arrayEval (dyadicHalf s) (dyadicHalf t)).comp (continuous_subtype_val.comp continuous_subtype_val))
noncomputable def nonaffineHalf (d : NonAffineArray) : NonAffineArray :=
  if h : UnitArray d.val then nonaffineHalfOn ⟨d,h⟩ else d
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
-- module Solutions.OAIQ2_Std.StandardMap_TreeLine
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
structure TreeLine (d : ℝ → ℝ → ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ d x y
  symm : ∀ x y, d x y=d y x
  triangle : ∀ x y z, d x z ≤ d x y+d y z
  unit : ∀ x y, d x y ≤ |y-x|
  tree : ∀ v x y z,
    min (d v x+d v y-d x y) (d v y+d v z-d y z) ≤ d v x+d v z-d x z
noncomputable def lineB (d : ℝ → ℝ → ℝ) (v x y : ℝ) : ℝ := d v x+d v y-d x y

def NoFastCancellation (d : ℝ → ℝ → ℝ) (δ : ℝ) : Prop :=
  ∀ z t : ℝ, 0 < t → ¬ ((1-δ)*t < d (z-t) z ∧ (1-δ)*t < d z (z+t) ∧ d (z-t) (z+t) < δ*t)

def ExteriorUnitRays (d : ℝ → ℝ → ℝ) (a b : ℝ) : Prop :=
  (∀ x y : ℝ, x ≤ a → y ≤ a → d x y=|y-x|) ∧
  (∀ x y : ℝ, b ≤ x → b ≤ y → d x y=|y-x|)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_TreeLocalAffine
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
-- module Solutions.OAIQ2_Std.StandardMap_ShapeTopology
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
-- module Solutions.OAIQ2_Std.StandardMap_MiddleCount
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

def bridgeMiddle (N : ℕ) : Finset ℕ := Finset.Icc (N/3+1) (2*N/3)
def MiddleLogGood (z : ℕ → ℝ) (N i : ℕ) : Prop :=
  (∀ j, j < i → (49/50:ℝ)*((i:ℝ)-(j:ℝ)) ≤ z i-z j) ∧
  (∀ j, i < j → j ≤ N → (49/50:ℝ)*((j:ℝ)-(i:ℝ)) ≤ z j-z i)
noncomputable def bridgeMiddleGood (z : ℕ → ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (bridgeMiddle N).filter (MiddleLogGood z N)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_BridgeScalars
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
-- module Solutions.OAIQ2_Std.StandardMap_GridBridge
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
noncomputable def bridgeGridLo (i : Fin 32) : ℝ := (i:ℝ)/32
noncomputable def bridgeGridHi (i : Fin 32) : ℝ := ((i:ℝ)+1)/32
noncomputable def bridgeGridCell (i : Fin 32) : Set ℝ := Icc (bridgeGridLo i) (bridgeGridHi i)
noncomputable def bridgeAreaScale : ℝ≥0∞ :=
  (ENNReal.ofReal (Real.exp (-1152*Real.pi))*(1/32)) *
    (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(3/4))*(1/32))
noncomputable def bridgeLocalConstant : ℝ≥0∞ := ENNReal.ofReal (Real.exp (1152*Real.pi))*256
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_MiddlePrefixBridge
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
def bridgeRowLength (B : ℕ) (b : Bool) : ℕ := if b then B else B-1
noncomputable def middlePrefixEvent (k : ℝ) (Bp Bm : ℕ) : Set Torus :=
  {z | torusPrefixGrowth k Bp z ∧ torusPrefixGrowth k Bm z.swap}
noncomputable def middleBridgeConstant : ℝ≥0∞ := 4096*bridgeLocalConstant/bridgeAreaScale
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_VectorGrowth
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
-- module Solutions.OAIQ2_Std.StandardMap_BridgeAveraging
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
-- module Solutions.OAIQ2_Std.StandardMap_MiddleObservationBridge
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
-- module Solutions.OAIQ2_Std.StandardMap_FastBridge
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
noncomputable def fastBridgeConstant : ℝ≥0∞ := 5*middleBridgeConstant
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_BridgeRealBound
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
noncomputable def bridgeRealConstant : ℝ := fastBridgeConstant.toReal
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_BridgeSamples
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
-- module Solutions.OAIQ2_Std.StandardMap_ScaleCancellation
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
-- module Solutions.OAIQ2_Std.StandardMap_BridgeGrid
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
-- module Solutions.OAIQ2_Std.StandardMap_TestObservations
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
-- module Solutions.OAIQ2_Std.StandardMap_ClippedTests
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
-- module Solutions.OAIQ2_Std.StandardMap_BridgeVague
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
-- module Solutions.OAIQ2_Std.StandardMap_EndpointObservations
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
def intervalInWindow (j : ArrayTestIndex) (u : DyadicTime) (q : ℕ) : Prop :=
  -((1:ℝ)/(2:ℝ)^q)≤(j.val.1:ℝ)-(u:ℝ) ∧ (j.val.2:ℝ)-(u:ℝ)≤(1:ℝ)/(2:ℝ)^q
noncomputable def endpointBridgeEvent (u v : DyadicTime) (W H : EndpointObservation) (ηw ηh : ℝ) : Set DistanceArray :=
  {d | (999/1000:ℝ)*((v:ℝ)-(u:ℝ))< d.val u v ∧ ηw< W.value d ∧ ηh< H.value d}
namespace CriticalScaleSequence
noncomputable def LimitLaws.selected (S : CriticalScaleSequence) (K : S.LimitLaws) (b : Bool) : Measure NonAffineArray :=
  if b then K.multi else K.terminal
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_BridgeExclusions
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
-- module Solutions.OAIQ2_Std.StandardMap_LocalMidpointGrid
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
-- module Solutions.OAIQ2_Std.StandardMap_RealBridge
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
-- module Solutions.OAIQ2_Std.StandardMap_ShapeComponents
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
-- module Solutions.OAIQ2_Std.StandardMap_ShapeCore
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
-- module Solutions.OAIQ2_Std.StandardMap_ShapeClassification
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
-- module Solutions.OAIQ2_Std.StandardMap_RemainderLaws
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
-- module Solutions.OAIQ2_Std.StandardMap_CappedTests
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
-- module Solutions.OAIQ2_Std.StandardMap_FineArrays
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
-- module Solutions.OAIQ2_Std.StandardMap_TruncationArrays
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
-- module Solutions.OAIQ2_Std.StandardMap_WeightedCompact
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
noncomputable def realWeight {X:Type*} [MeasurableSpace X] (μ:Measure X) (f:X→ℝ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal (f x))
structure CompactWeightLimit {ι:Type*} (l:Filter ι) (μ:ι→Measure DistanceArray) (f:DistanceArray→ℝ) where
  law : Measure DistanceArray
  regular : law.Regular
  finite : IsFiniteMeasure law
  converges : ∀g:C(DistanceArray,ℝ), Tendsto (fun i => ∫d,g d*f d ∂μ i) l (𝓝 (∫d,g d ∂law))
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_WeightSlow
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
-- module Solutions.OAIQ2_Std.StandardMap_WeightUnit
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
-- module Solutions.OAIQ2_Std.StandardMap_WeightBridge
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
-- module Solutions.OAIQ2_Std.StandardMap_TerminalCap
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
-- module Solutions.OAIQ2_Std.StandardMap_EndpointDefinition
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
-- module Solutions.OAIQ2_Std.StandardMap_EndpointCovariance
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
noncomputable def erealOrderIso (e : ℝ ≃o ℝ) : EReal ≃o EReal := e.withTopCongr.withBotCongr
@[simp] lemma erealOrderIso_coe (e : ℝ ≃o ℝ) (r : ℝ) : erealOrderIso e (r:EReal)=(e r:ℝ) := rfl
@[simp] lemma erealOrderIso_top (e : ℝ ≃o ℝ) : erealOrderIso e ⊤=⊤ := rfl
@[simp] lemma erealOrderIso_bot (e : ℝ ≃o ℝ) : erealOrderIso e ⊥=⊥ := rfl
noncomputable def dyadicHalfEquiv : DyadicTime ≃ DyadicTime where
  toFun := dyadicHalf
  invFun := fun s => s+s
  left_inv := dyadicHalf_add_self
  right_inv := dyadicHalf_double
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_EndpointClasses
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
-- module Solutions.OAIQ2_Std.StandardMap_ScaleAction
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
-- module Solutions.OAIQ2_Std.StandardMap_ScaleEndpoints
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
noncomputable def lengthBand (j:ℤ) : Set NonAffineArray := {d | UnitArray d.val ∧ d.val∈twoRayClass ∧ (2:ℝ)^j≤coreLength d.val ∧ coreLength d.val<(2:ℝ)^(j+1)}
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_BandIntensity
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
-- module Solutions.OAIQ2_Std.StandardMap_ScaleEvaluation
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
-- module Solutions.OAIQ2_Std.StandardMap_BandCap
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
-- module Solutions.OAIQ2_Std.StandardMap_BandCoboundary
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
-- module Solutions.OAIQ2_Std.StandardMap_TerminalStrict
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
-- module Solutions.OAIQ2_Std.StandardMap_EntropyConjugacy
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
noncomputable def coordinatePartition {r:ℕ} (p:FinitePartition r) : FinitePartition r :=
  ⟨p.val ∘ recurrenceCoordinates,p.property.comp measurePreserving_recurrenceCoordinates.measurable⟩
end StandardMapEntropy

end OAI
end


