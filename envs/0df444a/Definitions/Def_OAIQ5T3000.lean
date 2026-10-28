-- Prove2me | Definitions.Def_OAIQ5T3000
-- name    : OAIQ5T3000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T10:14:20.449379+00:00
-- url     : https://prove2.me/theorems/8129cd46-4a04-4bb5-a5bc-c798061881b2
-- title:
--   Definitions bundle OAIQ5T3000 of the split of OpenAI, Zero entropy does not guarantee a smooth positive-volume model
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SmoothObstruction.main`, carved from OpenAI's openai/math development (OpenAI, *Zero entropy does not guarantee a smooth positive-volume model*, OpenAI Math Release, September 25, 2026, result family 152, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 632 declarations of OpenAI's Lean: 301 definitions, 8 inductive types or structures, 24 instances and 299 theorems. The definitions and types are `OAI.SmoothObstruction.Alignment.align`, `OAI.SmoothObstruction.Alignment.boundaryMeasure`, `OAI.SmoothObstruction.ArrayRemainder.Data`, `OAI.SmoothObstruction.ArrayRemainder.Paths`, `OAI.SmoothObstruction.ArrayRemainder.residual`, `OAI.SmoothObstruction.BinaryCharacter.extendZero`, `OAI.SmoothObstruction.BinaryCharacter.sign`, `OAI.SmoothObstruction.BoundaryNeumann.perturb`, `OAI.SmoothObstruction.ChartDensity.coordinates`, `OAI.SmoothObstruction.ChartDensity.inverse`, `OAI.SmoothObstruction.ChartDomination.coordinateSet`, `OAI.SmoothObstruction.CloseComplement.difference`, `OAI.SmoothObstruction.CloseProjection.ambientInverse`, `OAI.SmoothObstruction.CloseProjection.equiv`, `OAI.SmoothObstruction.CloseProjection.restrictProjection`, `OAI.SmoothObstruction.CompactInvariant.cesaro`, `OAI.SmoothObstruction.CompactInvariant.iterateLaw`, `OAI.SmoothObstruction.CompactInvariant.testEmbedding`, `OAI.SmoothObstruction.CompactMatrix.Alphabet`, `OAI.SmoothObstruction.CompactMatrix.equiv`, `OAI.SmoothObstruction.ConullTransport.inverse`, `OAI.SmoothObstruction.CoordinateTubes.carrier`, `OAI.SmoothObstruction.CylinderApproximation.cylinders`, `OAI.SmoothObstruction.DirectedProjection.equiv`, `OAI.SmoothObstruction.DirectedProjection.restrictProjection`, `OAI.SmoothObstruction.DyadicChord.average`, `OAI.SmoothObstruction.DyadicChord.averageEnergy`, `OAI.SmoothObstruction.DyadicChord.chord`, `OAI.SmoothObstruction.DyadicChord.deviation`, `OAI.SmoothObstruction.DyadicChord.deviationEnergy`, `OAI.SmoothObstruction.DyadicChord.orbit`, `OAI.SmoothObstruction.DyadicChord.prefixSum`, `OAI.SmoothObstruction.EndpointBranch.derivative`, `OAI.SmoothObstruction.EndpointBranch.equiv_of_det`, `OAI.SmoothObstruction.EndpointBranch.exchange`, `OAI.SmoothObstruction.EndpointBranch.sumExchange`, `OAI.SmoothObstruction.EndpointBudget.admissible`, `OAI.SmoothObstruction.EndpointBudget.graph`, `OAI.SmoothObstruction.EndpointBudget.leading`, `OAI.SmoothObstruction.EndpointBudget.mixedCost` and 269 more.
--
--   **Sources.** They come from these modules of lean/OAI/Dynamics/SmoothObstruction, in whole or in part: `SmoothObstruction_BoundaryMatching`, `SmoothObstruction_Charts`, `SmoothObstruction_CoordinateTubes`, `SmoothObstruction_Coordinates`, `SmoothObstruction_DensityBounds`, `SmoothObstruction_DyadicChord`, `SmoothObstruction_EndpointFrames`, `SmoothObstruction_EndpointMass`, `SmoothObstruction_ExteriorPowers`, `SmoothObstruction_FiniteEntropy`, `SmoothObstruction_FiniteLaw`, `SmoothObstruction_GreenOperator`, `SmoothObstruction_GridCells`, `SmoothObstruction_InvariantMeasure`, `SmoothObstruction_Main`, `SmoothObstruction_ManifoldMatching`, `SmoothObstruction_MinorTransfer`, `SmoothObstruction_Models`, `SmoothObstruction_NonlinearMatching`, `SmoothObstruction_Obstruction`, `SmoothObstruction_OrthogonalCocycle`, `SmoothObstruction_PairBounds`, `SmoothObstruction_PairLaw`, `SmoothObstruction_PartitionEntropy`, `SmoothObstruction_PhaseDynamics`, `SmoothObstruction_PhaseEntropy`, `SmoothObstruction_ProductCoordinates`, `SmoothObstruction_Recognition`, `SmoothObstruction_Sampling`, `SmoothObstruction_Selection`, `SmoothObstruction_ShearGauge`, `SmoothObstruction_ShortDerivative`, `SmoothObstruction_SmoothScales`, `SmoothObstruction_SpectralBins`, `SmoothObstruction_Splitting`, `SmoothObstruction_SplittingStability`, `SmoothObstruction_StandardProbability`, `SmoothObstruction_StationaryGauge`, `SmoothObstruction_SwitchScales`, `SmoothObstruction_SymbolCores`, `SmoothObstruction_TubeProjection`, `SmoothObstruction_WordEntropy`, `SmoothObstruction_WordHierarchy`, `SmoothObstruction_WordLaw`, `SmoothObstruction_WordParameters`, `SmoothObstruction_WordStep`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the statements `OAI.SmoothObstruction.EuclideanSplitting.endpoint_bounds`, `OAI.SmoothObstruction.ManifoldCoordinates.family_original_germ_uniform`, `OAI.SmoothObstruction.ManifoldCoordinates.gauge_original_germ_sharp`, `OAI.SmoothObstruction.ManifoldCoordinates.genuine_pair_switch`, `OAI.SmoothObstruction.ManifoldCoordinates.grid_switches` and `OAI.SmoothObstruction.WordHierarchy.no_switching`; the proofs of `OAI.SmoothObstruction.EuclideanSplitting.endpoint_bounds`, `OAI.SmoothObstruction.ManifoldCoordinates.family_original_germ_uniform`, `OAI.SmoothObstruction.ManifoldCoordinates.gauge_original_germ_sharp`, `OAI.SmoothObstruction.ManifoldCoordinates.genuine_pair_switch`, `OAI.SmoothObstruction.ManifoldCoordinates.grid_switches`, `OAI.SmoothObstruction.WordHierarchy.no_switching` and `OAI.SmoothObstruction.main`.
-- source:
--   OpenAI, Zero entropy does not guarantee a smooth positive-volume model, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 152; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-finite-entropy-system-without-a-smooth-positive-volume-model-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Dynamics/SmoothObstruction at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ5_T3.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
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
-- module Solutions.OAIQ5_T3.SmoothObstruction_ShearGauge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix

namespace SmoothObstruction.FiniteShears

/-- The finite forward Green solution; no division by a spectral gap. -/
noncomputable def forward (q : ℝ) (f : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ j ∈ range t, q ^ (t - 1 - j) * f j

@[simp] lemma forward_zero (q : ℝ) (f : ℕ → ℝ) : forward q f 0 = 0 := by
  simp [forward]

/-- A terminal-value Green solution with coefficients at most one when q≥1. -/
noncomputable def backward (N : ℕ) (q : ℝ) (f : ℕ → ℝ) (t : ℕ) : ℝ :=
  -q⁻¹ * forward q⁻¹ (fun j => f (N - 1 - j)) (N - t)

@[simp] lemma backward_terminal (N : ℕ) (q : ℝ) (f : ℕ → ℝ) :
    backward N q f N = 0 := by simp [backward]

end SmoothObstruction.FiniteShears

namespace SmoothObstruction.TriangularGauge
open SmoothObstruction.FiniteShears

variable {d : ℕ}

/-- Replace one row, retaining the other rows. -/
def rowReplace (U : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) (v : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ := fun k j => if k = i then v j else U k j

end SmoothObstruction.TriangularGauge

namespace SmoothObstruction.NormalizedGauge
open SmoothObstruction.TriangularGauge
variable {d : ℕ}

noncomputable def error (A : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) (t : ℕ) (j : Fin d) : ℝ :=
  ∑ a ∈ range t, (Real.log (A a j j) - lam j)

noncomputable def normalized (A : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) (t : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => Real.exp (-error A lam (t + 1) i) * A t i j * Real.exp (error A lam t j)

end SmoothObstruction.NormalizedGauge

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_DyadicChord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators

namespace SmoothObstruction.DyadicChord

def prefixSum (f : ℕ → ℝ) (n : ℕ) : ℝ := ∑ j ∈ range n, f j
noncomputable def average (f : ℕ → ℝ) (n : ℕ) : ℝ := prefixSum f n / n
noncomputable def chord (f : ℕ → ℝ) (n u : ℕ) : ℝ := prefixSum f u - u * average f n
noncomputable def deviation (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  (range (n + 1)).sup' (by simp) (fun u => |chord f n u| / n)

end SmoothObstruction.DyadicChord

namespace SmoothObstruction.DyadicChord

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A measure-preserving transformation gives precisely the stationarity needed
below; no independence, ergodicity, or decay of correlations enters. -/
def orbit (T : Ω → Ω) (f : Ω → ℝ) (x : Ω) (j : ℕ) : ℝ := f (T^[j] x)

noncomputable def averageEnergy (T : Ω → Ω) (f : Ω → ℝ) (μ : Measure Ω) (n : ℕ) : ℝ :=
  ∫ x, (average (orbit T f x) n)^2 ∂μ

noncomputable def deviationEnergy (T : Ω → Ω) (f : Ω → ℝ) (μ : Measure Ω) (n : ℕ) : ℝ :=
  ∫ x, (deviation (orbit T f x) n)^2 ∂μ

@[simp] lemma averageEnergy_one (T : Ω → Ω) (f : Ω → ℝ) :
    averageEnergy T f μ 1 = ∫ x, (f x)^2 ∂μ := by
  simp [averageEnergy, average, prefixSum, orbit]

end SmoothObstruction.DyadicChord

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_Coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

abbrev E := EuclideanSpace ℝ (Fin d)

noncomputable def coord (S : Diffeomorph I I M M ∞) (a b : M) (x : M) : E (d:=d) →L[ℝ] E (d:=d) :=
  ContinuousLinearMap.inCoordinates (E (d:=d)) (TangentSpace I)
    (E (d:=d)) (TangentSpace I) a x b (S x) (mfderiv I I S x)

def domain (S : Diffeomorph I I M M ∞) (a b : M) : Set M :=
  (chartAt H a).source ∩ S ⁻¹' (chartAt H b).source


noncomputable def coordEquiv (S : Diffeomorph I I M M ∞) (a b x : M)
    (hx : x∈domain I S a b) : E (d:=d) ≃L[ℝ] E (d:=d) :=
  (((trivializationAt (E (d:=d)) (TangentSpace I) a).continuousLinearEquivAt ℝ x hx.1).symm.trans
    (S.mfderivToContinuousLinearEquiv (by simp) x)).trans
    ((trivializationAt (E (d:=d)) (TangentSpace I) b).continuousLinearEquivAt ℝ (S x) hx.2)

@[simp] theorem coordEquiv_coe (S : Diffeomorph I I M M ∞) (a b x : M)
    (hx : x∈domain I S a b) : (coordEquiv I S a b x hx).toContinuousLinearMap=coord I S a b x := by
  rw [coord,ContinuousLinearMap.inCoordinates_eq hx.1 hx.2]
  rfl

end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.CompactMatrix
open Set Metric

/-- Compact alphabet of uniformly bounded, uniformly invertible derivative
matrices. The coercion remembers the actual matrix, not an extra axiom. -/
abbrev Alphabet (d : ℕ) (K : ℝ) :=
  {A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) //
    ‖A‖≤K ∧ ∀ v,‖v‖≤K*‖A v‖}

instance instCompactSpaceAlphabet {d : ℕ} {K : ℝ} : CompactSpace (Alphabet d K) := by
  let T := EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)
  have hc : IsClosed (⋂ (v : EuclideanSpace ℝ (Fin d)), {A : T | ‖v‖≤K*‖A v‖}) := by
    apply isClosed_iInter
    intro v
    exact isClosed_le continuous_const (continuous_const.mul
      ((continuous_id : Continuous (fun A : T => A)).clm_apply
        (continuous_const : Continuous (fun _ : T => v))).norm)
  have he : {A : T | ∀ v, ‖v‖≤K*‖A v‖} =
      ⋂ (v : EuclideanSpace ℝ (Fin d)), {A : T | ‖v‖≤K*‖A v‖} := by
    ext A; simp
  have hf : IsClosed {A : T | ∀ v, ‖v‖≤K*‖A v‖} := he.symm ▸ hc
  have hg : IsClosed {A : T | ‖A‖≤K} := isClosed_le continuous_norm continuous_const
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : T) K).of_isClosed_subset
  · exact hg.inter hf
  · intro A hA
    simpa only [mem_closedBall,dist_zero_right] using hA.1

lemma injective {d : ℕ} {K : ℝ} (A : Alphabet d K) : Function.Injective A.val := by
  intro x y he
  have hh := A.property.2 (x-y)
  rw [map_sub,he,sub_self,norm_zero,mul_zero] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))

noncomputable def equiv {d : ℕ} {K : ℝ} (A : Alphabet d K) :
    EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
  (LinearEquiv.ofBijective A.val.toLinearMap
    ⟨injective A,(LinearMap.injective_iff_surjective).mp (injective A)⟩).toContinuousLinearEquiv

@[simp] lemma equiv_coe {d : ℕ} {K : ℝ} (A : Alphabet d K) :
    (equiv A).toContinuousLinearMap=A.val := rfl

end SmoothObstruction.CompactMatrix

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_InvariantMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction

namespace SmoothObstruction.CompactInvariant

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]

/-- The pushforward of the initial probability by the jth iterate. -/
noncomputable def iterateLaw (T : X → X) (hT : Continuous T)
    (μ : ProbabilityMeasure X) (j : ℕ) : ProbabilityMeasure X :=
  ⟨(μ : Measure X).map (T^[j]),
    (Measure.isProbabilityMeasure_map_iff (hT.iterate j).measurable.aemeasurable).2
      inferInstance⟩

/-- Cesaro averages indexed by n+1 to keep the total mass equal to one even
at the first index. No ergodic theorem is used in their construction. -/
noncomputable def cesaro (T : X → X) (hT : Continuous T)
    (μ : ProbabilityMeasure X) (n : ℕ) : ProbabilityMeasure X :=
  ⟨((n + 1 : ℕ) : ℝ≥0∞)⁻¹ • ∑ j ∈ range (n + 1),
      (iterateLaw T hT μ j : Measure X), by
    apply isProbabilityMeasure_iff.mpr
    simp only [Measure.finsetSum_apply, Measure.smul_apply, measure_univ,
      sum_const, card_range, nsmul_eq_mul, mul_one, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by positivity) (by finiteness)⟩

variable [MetrizableSpace X] [CompactSpace X]


/-- Real continuous test integrals embed probability laws into a locally
convex product space. This permits direct reuse of Mathlib's Krein--Milman
lemma, without an unproved ergodic-decomposition input. -/
noncomputable def testEmbedding (μ : ProbabilityMeasure X) : (X →ᵇ ℝ) → ℝ :=
  fun f => ∫ x, f x ∂(μ : Measure X)

end SmoothObstruction.CompactInvariant

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_OrthogonalCocycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction

namespace SmoothObstruction.QR
open InnerProductSpace Finset Set

/-- Finite orthonormal frames; the zero-dimensional case is included. -/
abbrev Frame (d : ℕ) := {f : Fin d → EuclideanSpace ℝ (Fin d) // Orthonormal ℝ f}

instance instNonemptyFrame (d : ℕ) : Nonempty (Frame d) :=
  ⟨⟨EuclideanSpace.basisFun (Fin d) ℝ, (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal⟩⟩

instance instCompactSpaceFrame (d : ℕ) : CompactSpace (Frame d) := by
  have hc : IsClosed {f : Fin d → EuclideanSpace ℝ (Fin d) | Orthonormal ℝ f} := by
    simp only [orthonormal_iff_ite,Set.ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_iInter (fun j =>
      isClosed_eq ((continuous_apply i).inner (continuous_apply j)) continuous_const))
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : Fin d → EuclideanSpace ℝ (Fin d)) 1).of_isClosed_subset hc
  intro f hf
  rw [Metric.mem_closedBall,dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  exact (hf.norm_eq_one i).le

variable {d : ℕ}

/-- The QR frame of the image of an orthonormal frame under an invertible map. -/
noncomputable def step (A : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (e : Frame d) : Frame d :=
  ⟨gramSchmidtNormed ℝ (fun i => A (e.val i)),
    gramSchmidtNormed_orthonormal (e.property.linearIndependent.map' A.toLinearMap (LinearMap.ker_eq_bot.mpr A.injective))⟩

end SmoothObstruction.QR

namespace SmoothObstruction.QR
open InnerProductSpace Finset
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}

variable {d : ℕ}
noncomputable def triangular (A : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (e : Frame d) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => inner ℝ ((step A e).val i) (A (e.val j))


end SmoothObstruction.QR

namespace SmoothObstruction.QR
open MeasureTheory Filter Topology InnerProductSpace
variable {d : ℕ}

noncomputable def basis (e : Frame d) : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
  gramSchmidtOrthonormalBasis (by simp) e.val

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

noncomputable def skew (T : X → X)
    (A : X → EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d)) :
    X × Frame d → X × Frame d := fun z => (T z.1,step (A z.1) z.2)

end SmoothObstruction.QR

namespace SmoothObstruction.OrbitCocycle
open MeasureTheory Filter Topology
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {d : ℕ} {K : ℝ}

abbrev Path := ℤ → X × CompactMatrix.Alphabet d K

noncomputable def code (S : X ≃ₜ X) (A : X → CompactMatrix.Alphabet d K) (x : X) :
    Path (X:=X) (d:=d) (K:=K) := fun j => ((S^j) x,A ((S^j) x))

def shift : Path (X:=X) (d:=d) (K:=K) → Path (X:=X) (d:=d) (K:=K) :=
  fun p j => p (j+1)

end SmoothObstruction.OrbitCocycle

namespace SmoothObstruction.OrbitCocycle
open MeasureTheory Filter Topology
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {d : ℕ} {K : ℝ}

/-- This Borel set remembers the entire genuine orbit, and the actual
cocycle value at every integer index, despite measurable trivializations. -/
def Actual (S : X ≃ₜ X) (A : X → CompactMatrix.Alphabet d K) :
    Set (Path (X:=X) (d:=d) (K:=K)) := {p | p=code S A (p 0).1}

noncomputable def matrix (p : Path (X:=X) (d:=d) (K:=K)) := CompactMatrix.equiv (p 0).2

end SmoothObstruction.OrbitCocycle

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_StationaryGauge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators

namespace SmoothObstruction.GoodStationary
open MeasureTheory Finset Filter Topology
open SmoothObstruction.DyadicChord
open scoped ENNReal NNReal

/-- The literal geometric floor used throughout the source. -/
noncomputable def floorAt (k : ℕ) : ℝ := (2 : ℝ) ^ (-(k : ℝ) / 10)

/-- Here `a h` is the sum over the diagonal coordinates of the dyadic
squared chord errors. Its square root replaces the optional convolution
upper bound in the manuscript's example of the choice of sequence. -/
noncomputable def bAt (η : ℝ) (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  (40 / Real.sqrt η) * Real.sqrt (a (k + 1)) + floorAt k

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

noncomputable def jointEnergy {d : ℕ} (T : Ω → Ω) (f : Fin d → Ω → ℝ)
    (μ : Measure Ω) (h : ℕ) : ℝ :=
  ∑ j, deviationEnergy T (f j) μ (2^h)

/-- A finite set of forward chord inequalities. Centered integer intervals
are precisely these sets pulled back by the negative iterate of a homeomorphism. -/
def Good {d : ℕ} (T : Ω → Ω) (f : Fin d → Ω → ℝ) (k : ℕ) (b : ℝ) : Set Ω :=
  {x | ∀ j, ∀ u ≤ 2^(k + 1), |chord (orbit T (f j) x) (2^(k + 1)) u| ≤ b * (2 : ℝ)^k}

end SmoothObstruction.GoodStationary

namespace SmoothObstruction.OrbitCocycle
open MeasureTheory Filter Topology Set
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {d : ℕ} {K : ℝ}

noncomputable def logDiagonal (j : Fin d) (z : Path (X:=X) (d:=d) (K:=K) × QR.Frame d) :=
  Real.log (QR.triangular (matrix z.1) z.2 j j)

end SmoothObstruction.OrbitCocycle

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_Splitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.EuclideanSplitting
variable {d : ℕ}

noncomputable def rate (lam : Fin d → ℝ) (l : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.diagonal (fun j => Real.exp (l*lam j))

noncomputable def mask (S : Finset (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.diagonal (fun j => if j ∈ S then 1 else 0)

@[simp] lemma rate_zero (lam : Fin d → ℝ) : rate lam 0=1 := by
  simp [rate]
lemma rate_add (lam : Fin d → ℝ) (a b : ℝ) :
    rate lam (a+b)=rate lam a*rate lam b := by
  rw [rate,rate,rate,Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [add_mul,Real.exp_add]
lemma rate_mask_comm (lam : Fin d → ℝ) (l : ℝ) (S : Finset (Fin d)) :
    rate lam l*mask S=mask S*rate lam l := by
  simp only [rate,mask,Matrix.diagonal_mul_diagonal]; congr 1; funext i; ring
@[simp] lemma mask_sq (S : Finset (Fin d)) : mask S*mask S=mask S := by
  simp only [mask,Matrix.diagonal_mul_diagonal]
  congr 1; funext i; split <;> simp
lemma mask_compl_add (S : Finset (Fin d)) : mask S+mask Sᶜ=1 := by
  rw [mask,mask,Matrix.diagonal_add]
  convert Matrix.diagonal_one (n:=Fin d) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1; funext i; simp; split <;> norm_num

/-- Gauge-coordinate fundamental matrix; both time directions are encoded. -/
noncomputable def transition (U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) (s t : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  U t * rate lam ((t:ℝ)-s) * V s
noncomputable def projection (U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (S : Finset (Fin d)) (t : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  U t*mask S*V t

lemma transition_self (U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) (hUV : ∀ t, U t*V t=1) (s : ℕ) : transition U V lam s s=1 := by
  simp [transition,hUV]
lemma transition_comp (U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) (hVU : ∀ t, V t*U t=1) (s t u : ℕ) :
    transition U V lam t u*transition U V lam s t=transition U V lam s u := by
  simp only [transition]
  calc
    _ = U u*(rate lam ((u:ℝ)-t)*(V t*U t)*rate lam ((t:ℝ)-s))*V s := by noncomm_ring
    _ = _ := by rw [hVU,mul_one,←rate_add]; congr 3; ring
lemma transition_projection (U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) (hVU : ∀ t, V t*U t=1) (S : Finset (Fin d)) (s t : ℕ) :
    transition U V lam s t*projection U V S s=projection U V S t*transition U V lam s t := by
  dsimp [transition,projection]
  calc
    _ = U t*(rate lam ((t:ℝ)-s)*(V s*U s)*mask S)*V s := by noncomm_ring
    _ = U t*(mask S*rate lam ((t:ℝ)-s))*V s := by rw [hVU,mul_one,rate_mask_comm]
    _ = _ := by
      symm
      calc
        _ = U t*(mask S*(V t*U t)*rate lam ((t:ℝ)-s))*V s := by noncomm_ring
        _ = _ := by rw [hVU,mul_one]
lemma projection_idem (U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hVU : ∀ t, V t*U t=1) (S : Finset (Fin d)) (t : ℕ) :
    projection U V S t*projection U V S t=projection U V S t := by
  dsimp [projection]
  calc
    _ = U t*(mask S*(V t*U t)*mask S)*V t := by noncomm_ring
    _ = _ := by rw [hVU,mul_one,mask_sq]
lemma projection_compl (U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hUV : ∀ t, U t*V t=1) (S : Finset (Fin d)) (t : ℕ) :
    projection U V S t+projection U V Sᶜ t=1 := by
  dsimp [projection]
  rw [←add_mul,←mul_add,mask_compl_add,mul_one,hUV]

/-- Actual later-on-the-left product used in the manuscript. -/
def propagator (A : ℕ → Matrix (Fin d) (Fin d) ℝ) (s : ℕ) : ℕ → Matrix (Fin d) (Fin d) ℝ
  | 0 => 1
  | n+1 => A (s+n)*propagator A s n

end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.QR
open Matrix
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

noncomputable def frameMatrix (e : Frame d) : Matrix (Fin d) (Fin d) ℝ :=
  (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm (basis e).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap

noncomputable def frameInverse (e : Frame d) : Matrix (Fin d) (Fin d) ℝ :=
  (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm (basis e).repr.toContinuousLinearEquiv.toContinuousLinearMap

end SmoothObstruction.QR

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_Charts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator
universe u
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type u} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A finite two-sided gauge of the ACTUAL derivative, based at time zero.
This carries no splitting, threshold, switch, Jacobian or measure conclusion. -/
structure BilateralGauge (S : Diffeomorph I I M M ∞) {ι : Type*}
    (a : ι → M) (c : M → ι) (n : ℕ) (B R : ℝ) (x : M) where
  lam : Fin d → ℝ
  rate_bound : ∀ i,|lam i|≤R
  UF : ℕ → Matrix (Fin d) (Fin d) ℝ
  VF : ℕ → Matrix (Fin d) (Fin d) ℝ
  UB : ℕ → Matrix (Fin d) (Fin d) ℝ
  VB : ℕ → Matrix (Fin d) (Fin d) ℝ
  invF : ∀ t,UF t*VF t=1 ∧ VF t*UF t=1
  invB : ∀ t,UB t*VB t=1 ∧ VB t*UB t=1
  centerU : UB 0=UF 0
  centerV : VB 0=VF 0
  normF : ∀ t≤n,‖UF t‖≤Real.exp B ∧ ‖VF t‖≤Real.exp B
  normB : ∀ t≤n,‖UB t‖≤Real.exp B ∧ ‖VB t‖≤Real.exp B
  stepF : ∀ t<n,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
    (coord I S (a (c (S^[t] x))) (a (c (S^[t+1] x))) (S^[t] x))*UF t=
      UF (t+1)*EuclideanSplitting.rate lam 1
  stepB : ∀ t<n,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
    (coord I S.symm (a (c (S.symm^[t] x))) (a (c (S.symm^[t+1] x))) (S.symm^[t] x))*UB t=
      UB (t+1)*EuclideanSplitting.rate (fun i => -lam i) 1

end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology Metric
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def chartChange (a b x : M) (ha : x∈(chartAt H a).source)
    (hb : x∈(chartAt H b).source) : E (d:=d) ≃L[ℝ] E (d:=d) :=
  ((trivializationAt (E (d:=d)) (TangentSpace I) a).continuousLinearEquivAt ℝ x ha).symm.trans
    ((trivializationAt (E (d:=d)) (TangentSpace I) b).continuousLinearEquivAt ℝ x hb)

end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ShortBin
open scoped Matrix.Norms.L2Operator
structure Gauge (d L : ℕ) (K : ℝ) where
  U : ℕ → Matrix (Fin d) (Fin d) ℝ
  V : ℕ → Matrix (Fin d) (Fin d) ℝ
  lam : Fin d → ℝ
  UV : ∀ t,U t*V t=1
  VU : ∀ t,V t*U t=1
  normU : ∀ t≤L,‖U t‖≤Real.exp K
  normV : ∀ t≤L,‖V t‖≤Real.exp K

end SmoothObstruction.ShortBin

namespace SmoothObstruction.ShortBin
open scoped Matrix.Norms.L2Operator

/-- Extend only beyond the finite window by its terminal value. This
extension is algebraically invertible at every index and never affects an
actual derivative equation within the window. -/
noncomputable def Gauge.ofFinite {d n : ℕ} {B : ℝ}
    (P Q : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hi : ∀ t≤n,P t*Q t=1 ∧ Q t*P t=1)
    (hb : ∀ t≤n,‖P t‖≤Real.exp B ∧ ‖Q t‖≤Real.exp B) : Gauge d n B where
  U t := P (min t n)
  V t := Q (min t n)
  lam := lam
  UV t := (hi _ (Nat.min_le_right _ _)).1
  VU t := (hi _ (Nat.min_le_right _ _)).2
  normU t ht := by simpa only [Nat.min_eq_left ht] using (hb t ht).1
  normV t ht := by simpa only [Nat.min_eq_left ht] using (hb t ht).2
end SmoothObstruction.ShortBin

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def localMap (S : Diffeomorph I I M M ∞) (a b : M) : E (d:=d) → E (d:=d) :=
  extChartAt I b ∘ S ∘ (extChartAt I a).symm

end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- An ambient open carrier of the exact local expression's relative
coordinate domain. It is NOT a smooth extension of the expression. -/
def domainU (S : Diffeomorph I I M M ∞) (a b : M) : Set (E (d:=d)) :=
  I.symm ⁻¹' ((chartAt H a).target∩(chartAt H a).symm ⁻¹' (S ⁻¹' (chartAt H b).source))

end SmoothObstruction.ManifoldCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_ShortDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.RelativeProduct

variable {R : Type*}

/-- Later times multiply on the left, as in the manuscript. -/
def segment [Monoid R] (A : ℕ → R) (s : ℕ) : ℕ → R
  | 0 => 1
  | n + 1 => A (s + n) * segment A s n

@[simp] theorem segment_zero [Monoid R] (A : ℕ → R) (s : ℕ) :
    segment A s 0 = 1 := rfl

@[simp] theorem segment_succ [Monoid R] (A : ℕ → R) (s n : ℕ) :
    segment A s (n + 1) = A (s + n) * segment A s n := rfl

end SmoothObstruction.RelativeProduct

namespace SmoothObstruction.ShortDerivative
open Set Finset
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual nonautonomous coordinate composition. -/
def iterate (f : ℕ → E → E) : ℕ → E → E
  | 0 => id
  | n+1 => f n ∘ iterate f n

end SmoothObstruction.ShortDerivative

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_SpectralBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.EuclideanSplitting
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

noncomputable def gaugeEquiv (U V : Matrix (Fin d) (Fin d) ℝ)
    (hUV : U*V=1) (hVU : V*U=1) :
    EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
  (LinearEquiv.ofLinearMap
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) U).toLinearMap
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) V).toLinearMap
    (by
      apply LinearMap.ext
      intro x
      change Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) U
        (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) V x)=x
      rw [←mul_apply_eq_comp,←map_mul,hUV,map_one]
      rfl)
    (by
      apply LinearMap.ext
      intro x
      change Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) V
        (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) U x)=x
      rw [←mul_apply_eq_comp,←map_mul,hVU,map_one]
      rfl)).toContinuousLinearEquiv

@[simp] lemma gaugeEquiv_apply (U V : Matrix (Fin d) (Fin d) ℝ)
    (hUV : U*V=1) (hVU : V*U=1) (x : EuclideanSpace ℝ (Fin d)) :
    gaugeEquiv U V hUV hVU x=Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) U x := rfl

@[simp] lemma gaugeEquiv_symm_apply (U V : Matrix (Fin d) (Fin d) ℝ)
    (hUV : U*V=1) (hVU : V*U=1) (x : EuclideanSpace ℝ (Fin d)) :
    (gaugeEquiv U V hUV hVU).symm x=Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) V x := rfl

noncomputable def coordinateSpace (S : Finset (Fin d)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  (Pi.spanSubset ℝ (S:Set (Fin d))).map (WithLp.linearEquiv 2 ℝ (Fin d→ℝ)).symm.toLinearMap

noncomputable def groupSpace (U V : Matrix (Fin d) (Fin d) ℝ)
    (hUV : U*V=1) (hVU : V*U=1) (S : Finset (Fin d)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  (coordinateSpace S).map (gaugeEquiv U V hUV hVU).toLinearEquiv.toLinearMap

end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.ShortBin
open EuclideanSplitting
open scoped Matrix.Norms.L2Operator

variable {d L : ℕ} {K : ℝ}

noncomputable def Gauge.product (A : Gauge d L K) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition A.U A.V A.lam 0 L)

noncomputable def Gauge.space (A : Gauge d L K) (S : Finset (Fin d)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  groupSpace (A.U 0) (A.V 0) (A.UV 0) (A.VU 0) S

end SmoothObstruction.ShortBin

namespace SmoothObstruction.DirectedProjection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def restrictProjection (U V : Submodule ℝ E) : U →L[ℝ] V :=
  V.orthogonalProjectionOnto.comp U.subtypeL

lemma lower (U V : Submodule ℝ E) {ε : ℝ} (hε : ε ≤ 1/2)
    (h : ∀ x : U, ‖(x:E)-V.starProjection x‖ ≤ ε*‖x‖) (x : U) :
    ‖x‖ ≤ 2*‖restrictProjection U V x‖ := by
  have hh : ‖x‖ ≤ ‖(x:E)-V.starProjection x‖+‖V.starProjection x‖ := by
    calc
      _ = ‖((x:E)-V.starProjection x)+V.starProjection x‖ := by rw [sub_add_cancel]; rfl
      _ ≤ _ := norm_add_le _ _
  have he := (h x).trans (mul_le_mul_of_nonneg_right hε (norm_nonneg _))
  change ‖x‖ ≤ 2*‖V.starProjection x‖
  linarith

noncomputable def equiv (U V : Submodule ℝ E)
    (hdim : Module.finrank ℝ U=Module.finrank ℝ V) {ε : ℝ} (hε : ε ≤ 1/2)
    (h : ∀ x : U, ‖(x:E)-V.starProjection x‖ ≤ ε*‖x‖) : U ≃L[ℝ] V :=
  (LinearMap.linearEquivOfInjective (restrictProjection U V).toLinearMap (by
    intro x y hxy
    change restrictProjection U V x=restrictProjection U V y at hxy
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    have hh := lower U V hε h (x-y)
    rw [map_sub,hxy,sub_self,norm_zero,mul_zero] at hh
    exact le_antisymm hh (norm_nonneg _)) hdim).toContinuousLinearEquiv

@[simp] lemma equiv_apply (U V : Submodule ℝ E)
    (hdim : Module.finrank ℝ U=Module.finrank ℝ V) {ε : ℝ} (hε : ε ≤ 1/2)
    (h : ∀ x : U, ‖(x:E)-V.starProjection x‖ ≤ ε*‖x‖) (x : U) :
    equiv U V hdim hε h x=restrictProjection U V x := rfl

end SmoothObstruction.DirectedProjection

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_CoordinateTubes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.CoordinateTubes
open Set Metric
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Ambient open carrier of an arbitrary open subset of a chart source.
It does not assert a smooth extension across a manifold boundary. -/
def carrier (a : M) (U : Set M) : Set (EuclideanSpace ℝ (Fin d)) :=
  I.symm ⁻¹' ((chartAt H a).target∩(chartAt H a).symm ⁻¹' U)

end SmoothObstruction.CoordinateTubes

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology Metric MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- Restriction of an actual bilateral gauge keeps exactly the same bases,
not a recomputed QR path or a newly chosen stationary witness. -/
def BilateralGauge.restrict (S : Diffeomorph I I M M ∞) (a : ι → M) (c : M → ι)
    {n N : ℕ} {B R : ℝ} {x : M} (A : BilateralGauge I S a c n B R x) (hN : N≤n) :
    BilateralGauge I S a c N B R x where
  lam := A.lam
  rate_bound := A.rate_bound
  UF := A.UF
  VF := A.VF
  UB := A.UB
  VB := A.VB
  invF := A.invF
  invB := A.invB
  centerU := A.centerU
  centerV := A.centerV
  normF t ht := A.normF t (ht.trans hN)
  normB t ht := A.normB t (ht.trans hN)
  stepF t ht := A.stepF t (ht.trans_le hN)
  stepB t ht := A.stepB t (ht.trans_le hN)

end SmoothObstruction.ManifoldCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_GreenOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.FiniteGreen
open Finset
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Finite fundamental matrices, with the output time first. -/
structure Evolution (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  map : ℕ → ℕ → E →L[ℝ] E
  self : ∀ t,map t t=ContinuousLinearMap.id ℝ E
  compose : ∀ t s u,(map t s).comp (map s u)=map t u

namespace Evolution
variable (A : Evolution E)

@[simp] lemma self_apply (t : ℕ) (v : E) : A.map t t v=v := by rw [A.self]; rfl
lemma comp_apply (t s u : ℕ) (v : E) : A.map t s (A.map s u v)=A.map t u v :=
  congrArg (fun F : E →L[ℝ] E => F v) (A.compose t s u)

noncomputable def forward (P : ℕ → E →L[ℝ] E) (f : ℕ → E) (a : E) (t : ℕ) : E :=
  A.map t 0 a + ∑ j ∈ range t,A.map t (j+1) (P (j+1) (f j))

noncomputable def backward (P : ℕ → E →L[ℝ] E) (f : ℕ → E) (c : E) (n t : ℕ) : E :=
  A.map t n c - ∑ j ∈ Ico t n,A.map t (j+1) (P (j+1) (f j))

@[simp] lemma forward_zero (P : ℕ → E →L[ℝ] E) (f : ℕ → E) (a : E) :
    A.forward P f a 0=a := by simp [forward]
@[simp] lemma backward_end (P : ℕ → E →L[ℝ] E) (f : ℕ → E) (c : E) (n : ℕ) :
    A.backward P f c n n=c := by simp [backward]

lemma forward_step (P : ℕ → E →L[ℝ] E) (f : ℕ → E) (a : E) (t : ℕ) :
    A.forward P f a (t+1)=A.map (t+1) t (A.forward P f a t)+P (t+1) (f t) := by
  simp only [forward,sum_range_succ,map_add,map_sum,A.comp_apply,A.self_apply]
  abel

lemma backward_step (P : ℕ → E →L[ℝ] E) (f : ℕ → E) (c : E) {n t : ℕ} (ht : t<n) :
    A.backward P f c n (t+1)=A.map (t+1) t (A.backward P f c n t)+P (t+1) (f t) := by
  have hs := sum_eq_sum_Ico_succ_bot ht (fun j => A.map (t+1) (j+1) (P (j+1) (f j)))
  simp only [backward,map_sub,map_sum,A.comp_apply]
  rw [hs,A.self_apply]
  abel

lemma recurrence_unique {v w : ℕ → E} {f : ℕ → E} {n : ℕ}
    (hv : ∀ t<n,v (t+1)=A.map (t+1) t (v t)+f t)
    (hw : ∀ t<n,w (t+1)=A.map (t+1) t (w t)+f t)
    (h0 : v 0=w 0) : ∀ t≤n,v t=w t := by
  intro t ht
  induction t with
  | zero => exact h0
  | succ t ih => rw [hv t (by omega),hw t (by omega),ih (by omega)]

lemma backward_recurrence_unique {v w : ℕ → E} {f : ℕ → E} {n : ℕ}
    (hv : ∀ t<n,v (t+1)=A.map (t+1) t (v t)+f t)
    (hw : ∀ t<n,w (t+1)=A.map (t+1) t (w t)+f t)
    (hn : v n=w n) : ∀ t≤n,v t=w t := by
  intro t ht
  induction ht using Nat.decreasingInduction with
  | self => exact hn
  | of_succ t ht ih =>
    have hh : A.map (t+1) t (v t)=A.map (t+1) t (w t) := by
      have hh := ih
      rw [hv t ht,hw t ht] at hh
      exact add_right_cancel hh
    have hh' := congrArg (A.map t (t+1)) hh
    simpa only [A.comp_apply,A.self_apply] using hh'

end Evolution
end SmoothObstruction.FiniteGreen

namespace SmoothObstruction.FiniteGreen
open Finset
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- An invariant complementary splitting. Empty groups are permitted. -/
structure Splitting (A : Evolution E) where
  slow : ℕ → E →L[ℝ] E
  fast : ℕ → E →L[ℝ] E
  slow_idem : ∀ t,(slow t).comp (slow t)=slow t
  fast_idem : ∀ t,(fast t).comp (fast t)=fast t
  add : ∀ t,slow t+fast t=ContinuousLinearMap.id ℝ E
  slow_inv : ∀ t s,(slow t).comp (A.map t s)=(A.map t s).comp (slow s)
  fast_inv : ∀ t s,(fast t).comp (A.map t s)=(A.map t s).comp (fast s)

namespace Splitting
variable {A : Evolution E} (B : Splitting A)

lemma add_apply (t : ℕ) (v : E) : B.slow t v+B.fast t v=v :=
  congrArg (fun F : E →L[ℝ] E => F v) (B.add t)
lemma slow_comm (t s : ℕ) (v : E) : B.slow t (A.map t s v)=A.map t s (B.slow s v) :=
  congrArg (fun F : E →L[ℝ] E => F v) (B.slow_inv t s)
lemma fast_comm (t s : ℕ) (v : E) : B.fast t (A.map t s v)=A.map t s (B.fast s v) :=
  congrArg (fun F : E →L[ℝ] E => F v) (B.fast_inv t s)
lemma slow_self (t : ℕ) (v : E) : B.slow t (B.slow t v)=B.slow t v :=
  congrArg (fun F : E →L[ℝ] E => F v) (B.slow_idem t)
lemma fast_self (t : ℕ) (v : E) : B.fast t (B.fast t v)=B.fast t v :=
  congrArg (fun F : E →L[ℝ] E => F v) (B.fast_idem t)
lemma slow_fast (t : ℕ) (v : E) : B.slow t (B.fast t v)=0 := by
  have hh := congrArg (B.slow t) (B.add_apply t v)
  rw [map_add,B.slow_self] at hh
  exact add_left_cancel (hh.trans (add_zero _).symm)
lemma fast_slow (t : ℕ) (v : E) : B.fast t (B.slow t v)=0 := by
  have hh := congrArg (B.fast t) (B.add_apply t v)
  rw [map_add,B.fast_self] at hh
  exact add_right_cancel (hh.trans (zero_add _).symm)

/-- The endpoint projection has a specified bounded inverse on the actual
fast space. It need not annihilate the slow space. -/
structure Terminal (n : ℕ) where
  P : E →L[ℝ] H
  J : H →L[ℝ] E
  right : P.comp J=ContinuousLinearMap.id ℝ H
  left : (J.comp P).comp (B.fast n)=B.fast n
  range : (B.fast n).comp J=J

namespace Terminal
variable {B} {n : ℕ} (C : B.Terminal (H:=H) n)
lemma P_J (h : H) : C.P (C.J h)=h := congrArg (fun F : H →L[ℝ] H => F h) C.right
lemma J_P_fast (v : E) : C.J (C.P (B.fast n v))=B.fast n v :=
  congrArg (fun F : E →L[ℝ] E => F v) C.left

noncomputable def terminalValue (f : ℕ → E) (a : E) (h : H) : E :=
  C.J (h-C.P (A.forward B.slow f a n))
noncomputable def trajectory (f : ℕ → E) (a : E) (h : H) (t : ℕ) : E :=
  A.forward B.slow f a t+A.backward B.fast f (C.terminalValue f a h) n t

lemma trajectory_step (f : ℕ → E) (a : E) (h : H) {t : ℕ} (ht : t<n) :
    C.trajectory f a h (t+1)=A.map (t+1) t (C.trajectory f a h t)+f t := by
  rw [trajectory,A.forward_step,A.backward_step _ _ _ ht,trajectory,map_add]
  have hh := B.add_apply (t+1) (f t)
  calc
    _ = A.map (t+1) t (A.forward B.slow f a t)+
        A.map (t+1) t (A.backward B.fast f (C.terminalValue f a h) n t)+
        (B.slow (t+1) (f t)+B.fast (t+1) (f t)) := by abel
    _ = _ := by rw [hh]


lemma trajectory_terminal (f : ℕ → E) (a : E) (h : H) :
    C.P (C.trajectory f a h n)=h := by
  simp only [trajectory,A.backward_end,map_add,terminalValue,C.P_J]
  abel

/-- Existence and uniqueness of the half-orbit boundary problem are proved
from the actual finite recurrence. No implicit-function hypothesis. -/
theorem trajectory_unique (f : ℕ → E) (a : E) (_ha : B.slow 0 a=a) (h : H)
    (v : ℕ → E) (hv : ∀ t<n,v (t+1)=A.map (t+1) t (v t)+f t)
    (h0 : B.slow 0 (v 0)=a) (hn : C.P (v n)=h) :
    ∀ t≤n,v t=C.trajectory f a h t := by
  have hs : ∀ t≤n,B.slow t (v t)=A.forward B.slow f a t := by
    apply A.recurrence_unique (f:=fun t => B.slow (t+1) (f t))
    · intro t ht
      rw [hv t ht,map_add,B.slow_comm]
    · intro t _
      exact A.forward_step B.slow f a t
    · simpa only [A.forward_zero] using h0
  have hend : B.fast n (v n)=C.terminalValue f a h := by
    unfold terminalValue
    rw [←hs n le_rfl,←hn,←map_sub]
    have he : v n-B.slow n (v n)=B.fast n (v n) := by
      apply sub_eq_iff_eq_add.mpr
      simpa only [add_comm] using (B.add_apply n (v n)).symm
    rw [he,C.J_P_fast]
  have hf : ∀ t≤n,B.fast t (v t)=A.backward B.fast f (C.terminalValue f a h) n t := by
    apply A.backward_recurrence_unique (f:=fun t => B.fast (t+1) (f t))
    · intro t ht
      rw [hv t ht,map_add,B.fast_comm]
    · intro t ht
      exact A.backward_step B.fast f _ ht
    · simpa only [A.backward_end] using hend
  intro t ht
  rw [←B.add_apply t (v t),hs t ht,hf t ht]
  rfl

/-- Endpoint correction on the slow initial data. Both decaying factors
are kept explicitly, as required in (future-kernel-graph). -/
noncomputable def kernel : E →L[ℝ] E :=
  -((A.map 0 n).comp (C.J.comp (C.P.comp ((A.map n 0).comp (B.slow 0)))))

end Terminal
end Splitting
end SmoothObstruction.FiniteGreen

namespace SmoothObstruction.EuclideanSplitting
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

noncomputable def evolution (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1) :
    FiniteGreen.Evolution (EuclideanSpace ℝ (Fin d)) where
  map t s := Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)
  self t := by
    rw [transition_self U V lam hUV]
    exact map_one _
  compose t s u := by
    change Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)*
      Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam u s)=_
    rw [←map_mul,transition_comp U V lam hVU]

noncomputable def splitting (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1) (S : Finset (Fin d)) :
    FiniteGreen.Splitting (evolution U V lam hUV hVU) where
  slow t := Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection U V S t)
  fast t := Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection U V Sᶜ t)
  slow_idem t := by
    change Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection U V S t)*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection U V S t)=_
    rw [←map_mul,projection_idem U V hVU]
  fast_idem t := by
    change Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection U V Sᶜ t)*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection U V Sᶜ t)=_
    rw [←map_mul,projection_idem U V hVU]
  add t := by
    rw [←map_add,projection_compl U V hUV]
    exact map_one _
  slow_inv t s := by
    change Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection U V S t)*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)=
      Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection U V S s)
    rw [←map_mul,←map_mul,transition_projection U V lam hVU]
  fast_inv t s := by
    change Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection U V Sᶜ t)*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)=
      Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)*Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection U V Sᶜ s)
    rw [←map_mul,←map_mul,transition_projection U V lam hVU]

end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.FiniteGreen.Splitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A : Evolution E} (B : Splitting A)

lemma slow_range_self (t : ℕ) (x : (B.slow t).range) : B.slow t (x:E)=x := by
  obtain ⟨y,hy⟩ := x.property
  rw [←hy]
  exact B.slow_self t y
lemma fast_range_self (t : ℕ) (x : (B.fast t).range) : B.fast t (x:E)=x := by
  obtain ⟨y,hy⟩ := x.property
  rw [←hy]
  exact B.fast_self t y
lemma slow_fast_range (t : ℕ) (x : (B.fast t).range) : B.slow t (x:E)=0 := by
  obtain ⟨y,hy⟩ := x.property
  rw [←hy]
  exact B.slow_fast t y
lemma fast_slow_range (t : ℕ) (x : (B.slow t).range) : B.fast t (x:E)=0 := by
  obtain ⟨y,hy⟩ := x.property
  rw [←hy]
  exact B.fast_slow t y

/-- Exact middle-time complementary matching. No determinant or angle
nondegeneracy is assumed: it follows from the splitting identities. -/
noncomputable def referenceLinear (t : ℕ) : ((B.slow t).range × (B.fast t).range) ≃ₗ[ℝ] E where
  toFun x := (x.1:E)-(x.2:E)
  invFun x := (⟨B.slow t x,⟨x,rfl⟩⟩,⟨-B.fast t x,⟨-x,by simp⟩⟩)
  left_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      change B.slow t ((x.1:E)-(x.2:E))=x.1
      rw [map_sub,B.slow_range_self,B.slow_fast_range,sub_zero]
    · apply Subtype.ext
      change -B.fast t ((x.1:E)-(x.2:E))=x.2
      rw [map_sub,B.fast_slow_range,B.fast_range_self,zero_sub,neg_neg]
  right_inv x := by
    change B.slow t x-(-B.fast t x)=x
    rw [sub_neg_eq_add,B.add_apply]
  map_add' x y := by change (x.1+y.1:E)-(x.2+y.2:E)=_; abel
  map_smul' c x := by change c • (x.1:E)-c • (x.2:E)=_; simp only [smul_sub,RingHom.id_apply]

variable [FiniteDimensional ℝ E]
noncomputable def referenceMatching (t : ℕ) : ((B.slow t).range × (B.fast t).range) ≃L[ℝ] E :=
  (B.referenceLinear t).toContinuousLinearEquiv

@[simp] lemma referenceMatching_apply (t : ℕ) (x : (B.slow t).range × (B.fast t).range) :
    B.referenceMatching t x=(x.1:E)-(x.2:E) := rfl

end SmoothObstruction.FiniteGreen.Splitting

namespace SmoothObstruction.CloseProjection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def restrictProjection (U V : Submodule ℝ E) : U →L[ℝ] V :=
  V.orthogonalProjectionOnto.comp U.subtypeL

/-- Equal-dimensional close spaces have a quantitatively invertible endpoint
projection. This includes zero and full spaces without a separate convention. -/
lemma lower (U V : Submodule ℝ E) (hclose : ‖U.starProjection-V.starProjection‖ ≤ 1/2) (x : U) :
    ‖x‖ ≤ 2*‖restrictProjection U V x‖ := by
  have he : (U.starProjection-V.starProjection) x=(x:E)-V.starProjection x := by
    simp only [_root_.sub_apply,U.starProjection_eq_self_iff.mpr x.property]
  have hn := (U.starProjection-V.starProjection).le_opNorm (x:E)
  rw [he] at hn
  have hne : ‖(x:E)-V.starProjection x‖ ≤ (1/2:ℝ)*‖x‖ :=
    hn.trans (mul_le_mul_of_nonneg_right hclose (norm_nonneg _))
  have hh : ‖x‖ ≤ ‖(x:E)-V.starProjection x‖+‖V.starProjection x‖ := by
    calc
      _ = ‖((x:E)-V.starProjection x)+V.starProjection x‖ := by rw [sub_add_cancel]; rfl
      _ ≤ _ := norm_add_le _ _
  change ‖x‖ ≤ 2*‖V.starProjection x‖
  linarith

lemma injective (U V : Submodule ℝ E) (hclose : ‖U.starProjection-V.starProjection‖ ≤ 1/2) :
    Function.Injective (restrictProjection U V) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hh := lower U V hclose (x-y)
  rw [map_sub,hxy,sub_self,norm_zero,mul_zero] at hh
  exact le_antisymm hh (norm_nonneg _)

noncomputable def equiv (U V : Submodule ℝ E)
    (hdim : Module.finrank ℝ U=Module.finrank ℝ V)
    (hclose : ‖U.starProjection-V.starProjection‖ ≤ 1/2) : U ≃L[ℝ] V :=
  (LinearMap.linearEquivOfInjective (restrictProjection U V).toLinearMap
    (injective U V hclose) hdim).toContinuousLinearEquiv

@[simp] lemma equiv_apply (U V : Submodule ℝ E)
    (hdim : Module.finrank ℝ U=Module.finrank ℝ V)
    (hclose : ‖U.starProjection-V.starProjection‖ ≤ 1/2) (x : U) :
    equiv U V hdim hclose x=restrictProjection U V x := rfl

end SmoothObstruction.CloseProjection

namespace SmoothObstruction.BoundaryNeumann
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A genuine inverse for an explicitly estimated perturbation of an
invertible matching map. This is the Neumann step in source (4.15),
with no bijectivity hypothesis on the perturbed map. -/
noncomputable def perturb (L : E ≃L[ℝ] F) (D : E →L[ℝ] F)
    (h : ‖L.symm.toContinuousLinearMap.comp D‖ < 1) : E ≃L[ℝ] F :=
  (ContinuousLinearEquiv.ofUnit (Units.oneSub (-(L.symm.toContinuousLinearMap.comp D))
    (by simpa only [norm_neg] using h))).trans L

lemma perturb_apply (L : E ≃L[ℝ] F) (D : E →L[ℝ] F)
    (h : ‖L.symm.toContinuousLinearMap.comp D‖ < 1) (x : E) :
    perturb L D h x=L x+D x := by
  change L (x - -(L.symm (D x)))=L x+D x
  rw [sub_neg_eq_add,map_add,L.apply_symm_apply]

end SmoothObstruction.BoundaryNeumann

namespace SmoothObstruction.CloseComplement
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def difference (U V : Submodule ℝ E) : U × V →L[ℝ] E :=
  (U.subtypeL.comp (ContinuousLinearMap.fst ℝ U V))-
  (V.subtypeL.comp (ContinuousLinearMap.snd ℝ U V))

omit [FiniteDimensional ℝ E] in
@[simp] lemma difference_apply (U V : Submodule ℝ E) (x : U × V) :
    difference U V x=(x.1:E)-(x.2:E) := rfl

end SmoothObstruction.CloseComplement

namespace SmoothObstruction.FiniteGreen.Splitting
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {A : Evolution E} (B : Splitting A)

/-- Fixed endpoint-bin orthogonal projection, together with its genuine
inverse on the moving fast space. Empty endpoint spaces are included. -/
noncomputable def terminalProjection (n : ℕ) (V : Submodule ℝ E)
    (hdim : Module.finrank ℝ (B.fast n).range=Module.finrank ℝ V)
    (hclose : ‖(B.fast n).range.starProjection-V.starProjection‖≤1/2) : B.Terminal (H:=V) n where
  P := V.orthogonalProjectionOnto
  J := (B.fast n).range.subtypeL.comp
    (CloseProjection.equiv (B.fast n).range V hdim hclose).symm.toContinuousLinearMap
  right := by
    ext x
    exact congrArg Subtype.val ((CloseProjection.equiv (B.fast n).range V hdim hclose).apply_symm_apply x)
  left := by
    ext x
    let v : (B.fast n).range := ⟨B.fast n x,⟨x,rfl⟩⟩
    change ((CloseProjection.equiv (B.fast n).range V hdim hclose).symm
      (CloseProjection.equiv (B.fast n).range V hdim hclose v):E)=(v:E)
    rw [ContinuousLinearEquiv.symm_apply_apply]
  range := by
    ext x
    change B.fast n (((CloseProjection.equiv (B.fast n).range V hdim hclose).symm x):E)=_
    have hv := ((CloseProjection.equiv (B.fast n).range V hdim hclose).symm x).property
    obtain ⟨v,hv⟩ := hv
    change B.fast n (((CloseProjection.equiv (B.fast n).range V hdim hclose).symm x):E)=
      (((CloseProjection.equiv (B.fast n).range V hdim hclose).symm x):E)
    change B.fast n v=(((CloseProjection.equiv (B.fast n).range V hdim hclose).symm x):E) at hv
    rw [←hv,B.fast_self]

end SmoothObstruction.FiniteGreen.Splitting

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_BoundaryMatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.ShortBin
open EuclideanSplitting
open scoped Matrix.Norms.L2Operator
variable {d n : ℕ} {K : ℝ}

noncomputable def Gauge.evolution (A : Gauge d n K) :=
  EuclideanSplitting.evolution A.U A.V A.lam A.UV A.VU
noncomputable def Gauge.splitting (A : Gauge d n K) (S : Finset (Fin d)) :=
  EuclideanSplitting.splitting A.U A.V A.lam A.UV A.VU S

end SmoothObstruction.ShortBin

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology Metric MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- The past short segment of the true forward gauge, centered at its long
endpoint. Rates are merely negated; the original starting threshold remains
available, and no new stationary witness is chosen. -/
noncomputable def BilateralGauge.endpointBackward (S : Diffeomorph I I M M ∞)
    (a : ι → M) (c : M → ι) {n N : ℕ} {B R : ℝ} {x : M}
    (A : BilateralGauge I S a c n B R x) : ShortBin.Gauge d N B where
  U t := A.UF (n-t)
  V t := A.VF (n-t)
  lam j := -A.lam j
  UV _t := (A.invF _).1
  VU _t := (A.invF _).2
  normU _t _ := (A.normF _ (Nat.sub_le _ _)).1
  normV _t _ := (A.normF _ (Nat.sub_le _ _)).2

end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.FiniteGreen
open Finset
variable {E H G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

namespace Splitting
variable {A : Evolution E} (B : Splitting A)

noncomputable def initialSpace : Submodule ℝ E := (B.slow 0).range
lemma slow_initial (x : B.initialSpace) : B.slow 0 x=x := by
  obtain ⟨v,hv⟩ := x.property
  change B.slow 0 v=x.val at hv
  rw [←hv,B.slow_self]

namespace Terminal
variable {B} {n : ℕ} (C : B.Terminal (H:=H) n)

lemma trajectory_initial (f : ℕ → E) (a : E) (ha : B.slow 0 a=a) (h : H) :
    C.trajectory f a h 0=a+C.kernel a+C.trajectory f 0 h 0 := by
  simp only [trajectory,A.forward_zero]
  simp only [terminalValue,Evolution.forward,Evolution.backward, map_add,map_sub,map_zero,
    map_sum,kernel,_root_.neg_apply,ContinuousLinearMap.coe_comp,Function.comp_apply,ha,
    zero_add]
  abel

end Terminal

end Splitting

namespace Matching
variable [FiniteDimensional ℝ E]
variable {A₁ A₂ : Evolution E} {B₁ : Splitting A₁} {B₂ : Splitting A₂}
  {n₁ n₂ : ℕ} (C₁ : B₁.Terminal (H:=H) n₁) (C₂ : B₂.Terminal (H:=G) n₂)

noncomputable def correction : (B₁.initialSpace × B₂.initialSpace) →L[ℝ] E :=
  (C₁.kernel.comp (B₁.initialSpace.subtypeL.comp (ContinuousLinearMap.fst ℝ _ _)))-
    (C₂.kernel.comp (B₂.initialSpace.subtypeL.comp (ContinuousLinearMap.snd ℝ _ _)))

omit [FiniteDimensional ℝ E] in
@[simp] lemma correction_apply (x : B₁.initialSpace × B₂.initialSpace) :
    correction C₁ C₂ x=C₁.kernel x.1-C₂.kernel x.2 := rfl

/-- The exact two half-orbit boundary problem. The only matching input is
complementarity of the unperturbed initial spaces. The small graph terms
are inverted by a proved Neumann construction, not by assuming invertibility. -/
theorem solve (L : (B₁.initialSpace × B₂.initialSpace) ≃L[ℝ] E)
    (hL : ∀ x,L x=(x.1:E)-(x.2:E))
    (hsmall : ‖L.symm.toContinuousLinearMap.comp (correction C₁ C₂)‖ < 1)
    (f₁ f₂ : ℕ → E) (h₁ : H) (h₂ : G) (m : E) :
    ∃ v₁ v₂ : ℕ → E,
      (∀ t<n₁,v₁ (t+1)=A₁.map (t+1) t (v₁ t)+f₁ t) ∧
      (∀ t<n₂,v₂ (t+1)=A₂.map (t+1) t (v₂ t)+f₂ t) ∧
      C₁.P (v₁ n₁)=h₁ ∧ C₂.P (v₂ n₂)=h₂ ∧ v₁ 0-v₂ 0=m ∧
      ∀ w₁ w₂ : ℕ → E,
        (∀ t<n₁,w₁ (t+1)=A₁.map (t+1) t (w₁ t)+f₁ t) →
        (∀ t<n₂,w₂ (t+1)=A₂.map (t+1) t (w₂ t)+f₂ t) →
        C₁.P (w₁ n₁)=h₁ → C₂.P (w₂ n₂)=h₂ → w₁ 0-w₂ 0=m →
        (∀ t≤n₁,w₁ t=v₁ t) ∧ (∀ t≤n₂,w₂ t=v₂ t) := by
  let M := BoundaryNeumann.perturb L (correction C₁ C₂) hsmall
  let q₁ := C₁.trajectory f₁ 0 h₁ 0
  let q₂ := C₂.trajectory f₂ 0 h₂ 0
  let a := M.symm (m-q₁+q₂)
  have hM (x : B₁.initialSpace × B₂.initialSpace) :
      M x=(x.1:E)-(x.2:E)+C₁.kernel x.1-C₂.kernel x.2 := by
    rw [BoundaryNeumann.perturb_apply,hL,correction_apply]
    abel
  refine ⟨C₁.trajectory f₁ a.1 h₁,C₂.trajectory f₂ a.2 h₂,
    fun _ ht => C₁.trajectory_step _ _ _ ht,fun _ ht => C₂.trajectory_step _ _ _ ht,
    C₁.trajectory_terminal _ _ _,C₂.trajectory_terminal _ _ _,?_,?_⟩
  · rw [C₁.trajectory_initial _ _ (B₁.slow_initial _) _,
      C₂.trajectory_initial _ _ (B₂.slow_initial _) _]
    have ha : M a=m-q₁+q₂ := M.apply_symm_apply _
    rw [hM] at ha
    change (a.1:E)+C₁.kernel a.1+q₁-((a.2:E)+C₂.kernel a.2+q₂)=m
    calc
      _ = ((a.1:E)-(a.2:E)+C₁.kernel a.1-C₂.kernel a.2)+q₁-q₂ := by abel
      _ = m := by rw [ha]; abel
  · intro w₁ w₂ hw₁ hw₂ he₁ he₂ hm
    let b₁ : B₁.initialSpace := ⟨B₁.slow 0 (w₁ 0),⟨w₁ 0,rfl⟩⟩
    let b₂ : B₂.initialSpace := ⟨B₂.slow 0 (w₂ 0),⟨w₂ 0,rfl⟩⟩
    have hv₁ := C₁.trajectory_unique f₁ b₁ (B₁.slow_initial b₁) h₁ w₁ hw₁ rfl he₁
    have hv₂ := C₂.trajectory_unique f₂ b₂ (B₂.slow_initial b₂) h₂ w₂ hw₂ rfl he₂
    have hb : M (b₁,b₂)=M a := by
      rw [M.apply_symm_apply,hM]
      rw [hv₁ 0 (by omega),hv₂ 0 (by omega),
        C₁.trajectory_initial _ _ (B₁.slow_initial _) _,
        C₂.trajectory_initial _ _ (B₂.slow_initial _) _] at hm
      change (b₁:E)-(b₂:E)+C₁.kernel b₁-C₂.kernel b₂=m-q₁+q₂
      change (b₁:E)+C₁.kernel b₁+q₁-((b₂:E)+C₂.kernel b₂+q₂)=m at hm
      calc
        _ = ((b₁:E)+C₁.kernel b₁+q₁-((b₂:E)+C₂.kernel b₂+q₂))-q₁+q₂ := by abel
        _ = _ := by rw [hm]
    have hb' := M.injective hb
    have hb₁ : b₁=a.1 := congrArg Prod.fst hb'
    have hb₂ : b₂=a.2 := congrArg Prod.snd hb'
    rw [hb₁] at hv₁
    rw [hb₂] at hv₂
    exact ⟨hv₁,hv₂⟩

end Matching
end SmoothObstruction.FiniteGreen

namespace SmoothObstruction.FiniteGreen.Matching
open Finset
variable {E H G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ E]
variable {A₁ A₂ : Evolution E} {B₁ : Splitting A₁} {B₂ : Splitting A₂}
  {n₁ n₂ : ℕ} (C₁ : B₁.Terminal (H:=H) n₁) (C₂ : B₂.Terminal (H:=G) n₂)

abbrev Paths (E : Type*) (n₁ n₂ : ℕ) := (Fin (n₁+1) → E) × (Fin (n₂+1) → E)
abbrev Data (E H G : Type*) (n₁ n₂ : ℕ) :=
  (Fin n₁ → E) × (Fin n₂ → E) × E × H × G

/-- The actual finite-array boundary operator consists of both recurrence
residuals, the middle matching equation, and the two terminal projections. -/
noncomputable def boundaryLinear : Paths E n₁ n₂ →ₗ[ℝ] Data E H G n₁ n₂ where
  toFun v := (fun t => v.1 t.succ-A₁.map (t+1) t (v.1 t.castSucc),
    fun t => v.2 t.succ-A₂.map (t+1) t (v.2 t.castSucc),
    v.1 0-v.2 0,C₁.P (v.1 (Fin.last n₁)),C₂.P (v.2 (Fin.last n₂)))
  map_add' v w := by
    apply Prod.ext
    · funext t; simp only [Prod.fst_add,Pi.add_apply,map_add]; abel
    · apply Prod.ext
      · funext t; simp only [Prod.snd_add,Prod.fst_add,Pi.add_apply,map_add]; abel
      · apply Prod.ext
        · simp only [Prod.snd_add,Prod.fst_add,Pi.add_apply]; abel
        · apply Prod.ext <;> simp only [Prod.snd_add,Prod.fst_add,Pi.add_apply,map_add]
  map_smul' c v := by
    apply Prod.ext
    · funext t; simp [smul_sub]
    · apply Prod.ext
      · funext t; simp [smul_sub]
      · apply Prod.ext
        · simp [smul_sub]
        · apply Prod.ext <;> simp

noncomputable def boundary : Paths E n₁ n₂ →L[ℝ] Data E H G n₁ n₂ :=
  (boundaryLinear C₁ C₂).toContinuousLinearMap

noncomputable def extend {n : ℕ} (v : Fin n → E) (t : ℕ) : E :=
  if h : t<n then v ⟨t,h⟩ else 0

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma extend_apply {n : ℕ} (v : Fin n → E) (t : Fin n) : extend v t=v t := by
  simp [extend,t.isLt]

/-- Finite-dimensional invertibility is a consequence of the Green formulas
and the genuinely small terminal graph correction. No linear inverse is
postulated. -/
theorem boundary_bijective (L : (B₁.initialSpace × B₂.initialSpace) ≃L[ℝ] E)
    (hL : ∀ x,L x=(x.1:E)-(x.2:E))
    (hsmall : ‖L.symm.toContinuousLinearMap.comp (correction C₁ C₂)‖ < 1) :
    Function.Bijective (boundary C₁ C₂) := by
  classical
  have huniq (d : Data E H G n₁ n₂) : ∃! v : Paths E n₁ n₂,boundary C₁ C₂ v=d := by
    obtain ⟨v₁,v₂,hv₁,hv₂,he₁,he₂,hm,hu⟩ := solve C₁ C₂ L hL hsmall
      (extend d.1) (extend d.2.1) d.2.2.2.1 d.2.2.2.2 d.2.2.1
    let v : Paths E n₁ n₂ := (fun t => v₁ t,fun t => v₂ t)
    have hv : boundary C₁ C₂ v=d := by
      apply Prod.ext
      · funext t
        change v₁ (t+1)-A₁.map (t+1) t (v₁ t)=d.1 t
        rw [hv₁ t t.isLt,extend_apply]; abel
      · apply Prod.ext
        · funext t
          change v₂ (t+1)-A₂.map (t+1) t (v₂ t)=d.2.1 t
          rw [hv₂ t t.isLt,extend_apply]; abel
        · exact Prod.ext hm (Prod.ext he₁ he₂)
    refine ⟨v,hv,?_⟩
    intro w hw
    have h₁ : ∀ t<n₁,extend w.1 (t+1)=A₁.map (t+1) t (extend w.1 t)+extend d.1 t := by
      intro t ht
      have h := congrArg (fun z : Data E H G n₁ n₂ => z.1 ⟨t,ht⟩) hw
      change w.1 ⟨t+1,by omega⟩-A₁.map (t+1) t (w.1 ⟨t,by omega⟩)=d.1 ⟨t,ht⟩ at h
      simp only [extend,dite_eq_left (show t+1<n₁+1 by omega),dite_eq_left (show t<n₁+1 by omega),dite_eq_left ht]
      rw [←h]; abel
    have h₂ : ∀ t<n₂,extend w.2 (t+1)=A₂.map (t+1) t (extend w.2 t)+extend d.2.1 t := by
      intro t ht
      have h := congrArg (fun z : Data E H G n₁ n₂ => z.2.1 ⟨t,ht⟩) hw
      change w.2 ⟨t+1,by omega⟩-A₂.map (t+1) t (w.2 ⟨t,by omega⟩)=d.2.1 ⟨t,ht⟩ at h
      simp only [extend,dite_eq_left (show t+1<n₂+1 by omega),dite_eq_left (show t<n₂+1 by omega),dite_eq_left ht]
      rw [←h]; abel
    have he₁' : C₁.P (extend w.1 n₁)=d.2.2.2.1 := by
      have h := congrArg (fun z : Data E H G n₁ n₂ => z.2.2.2.1) hw
      change C₁.P (w.1 (Fin.last n₁))=d.2.2.2.1 at h
      change C₁.P (extend w.1 (Fin.last n₁))=d.2.2.2.1
      rw [extend_apply]
      exact h
    have he₂' : C₂.P (extend w.2 n₂)=d.2.2.2.2 := by
      have h := congrArg (fun z : Data E H G n₁ n₂ => z.2.2.2.2) hw
      change C₂.P (w.2 (Fin.last n₂))=d.2.2.2.2 at h
      change C₂.P (extend w.2 (Fin.last n₂))=d.2.2.2.2
      rw [extend_apply]
      exact h
    have hm' : extend w.1 0-extend w.2 0=d.2.2.1 := by
      have h := congrArg (fun z : Data E H G n₁ n₂ => z.2.2.1) hw
      change w.1 0-w.2 0=d.2.2.1 at h
      change extend w.1 (0 : Fin (n₁+1))-extend w.2 (0 : Fin (n₂+1))=d.2.2.1
      rw [extend_apply,extend_apply]
      exact h
    obtain ⟨hu₁,hu₂⟩ := hu (extend w.1) (extend w.2) h₁ h₂ he₁' he₂' hm'
    apply Prod.ext
    · funext t
      simpa only [extend_apply] using hu₁ t (by omega)
    · funext t
      simpa only [extend_apply] using hu₂ t (by omega)
  constructor
  · intro v w h
    obtain ⟨z,hz,hzu⟩ := huniq (boundary C₁ C₂ v)
    exact (hzu v rfl).trans (hzu w h.symm).symm
  · intro d
    obtain ⟨v,hv,_⟩ := huniq d
    exact ⟨v,hv⟩

noncomputable def boundaryEquiv (L : (B₁.initialSpace × B₂.initialSpace) ≃L[ℝ] E)
    (hL : ∀ x,L x=(x.1:E)-(x.2:E))
    (hsmall : ‖L.symm.toContinuousLinearMap.comp (correction C₁ C₂)‖ < 1) :
    Paths E n₁ n₂ ≃L[ℝ] Data E H G n₁ n₂ :=
  (LinearEquiv.ofBijective (boundaryLinear C₁ C₂)
    (boundary_bijective C₁ C₂ L hL hsmall)).toContinuousLinearEquiv

end SmoothObstruction.FiniteGreen.Matching

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_Models
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Set Filter
open scoped ENNReal Topology Manifold ContDiff

namespace SmoothObstruction.ConullTransport
open MeasureTheory Set
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- A measurable total representative of the inverse conjugacy; it uses an
arbitrary value only off the given invariant conull subset. -/
noncomputable def inverse (A : Set X) (B : Set Y) (e : A ≃ᵐ B) (x₀ : X) : Y → X :=
  Function.extend (Subtype.val : B → Y) (fun y => (e.symm y : X)) (fun _ => x₀)

end SmoothObstruction.ConullTransport

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_DensityBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.ChartDomination
open MeasureTheory Set Filter Topology
open scoped ENNReal
variable {X E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The image of a measurable carrier under a measurable coordinate map with
measurable inverse. Unlike an arbitrary image, this is visibly measurable. -/
def coordinateSet (e : X → E) (r : E → X) (G : Set X) : Set E :=
  {u | r u ∈ G ∧ e (r u) = u}

end SmoothObstruction.ChartDomination

namespace SmoothObstruction.ChartDensity
open Set MeasureTheory Filter Topology
open scoped Manifold ContDiff ENNReal
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M] [BorelSpace M]

noncomputable def coordinates (a : M) : M → EuclideanSpace ℝ (Fin d) := by
  classical
  exact (extChartAt I a).source.piecewise (extChartAt I a) (fun _ => 0)

noncomputable def inverse (a : M) : EuclideanSpace ℝ (Fin d) → M := by
  classical
  exact (extChartAt I a).target.piecewise (extChartAt I a).symm (fun _ => a)

end SmoothObstruction.ChartDensity

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_ExteriorPowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped ContDiff BigOperators
open Module

namespace SmoothObstruction.ExteriorStability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The exterior power as a continuous operator on the canonical inner product space. -/
noncomputable def exterior (p : ℕ) (A : E →L[ℝ] E) :
    (⋀[ℝ]^p E) →L[ℝ] (⋀[ℝ]^p E) :=
  (exteriorPower.map p A.toLinearMap).toContinuousLinearMap

@[simp] theorem exterior_apply (p : ℕ) (A : E →L[ℝ] E) (v : ⋀[ℝ]^p E) :
    exterior p A v = exteriorPower.map p A.toLinearMap v := rfl

/-- A determinant polynomial is smooth in all its entries. -/
theorem contDiff_det {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : WithTop ℕ∞}
    (f : D → Matrix ι ι ℝ) (hf : ∀ i j, ContDiff ℝ n (fun x => f x i j)) :
    ContDiff ℝ n (fun x => (f x).det) := by
  simp only [Matrix.det_apply]
  fun_prop

/-- The canonical wedge of a fixed number of vectors is a smooth polynomial. -/
theorem contDiff_wedge (p : ℕ) :
    ContDiff ℝ ∞ (exteriorPower.ιMulti ℝ p (M := E)) := by
  let b := (stdOrthonormalBasis ℝ E).toBasis
  let e := (b.exteriorPower p).equivFunL
  apply e.comp_contDiff_iff.mp
  apply contDiff_pi.mpr
  intro s
  change ContDiff ℝ ∞ (fun v => (b.exteriorPower p).repr (exteriorPower.ιMulti ℝ p v) s)
  simp only [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  apply contDiff_det
  intro i j
  exact ((b.coord (Set.powersetCard.ofFinEmbEquiv.symm s j)).toContinuousLinearMap.contDiff).comp
    (contDiff_apply ℝ E i)

@[simp] theorem exterior_one (p : ℕ) :
    exterior (E := E) p 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  change exteriorPower.map p LinearMap.id v = v
  rw [exteriorPower.map_id]
  rfl

@[simp] theorem exterior_mul (p : ℕ) (A B : E →L[ℝ] E) :
    exterior p (A * B) = exterior p A * exterior p B := by
  apply ContinuousLinearMap.ext
  intro v
  change exteriorPower.map p (A.toLinearMap.comp B.toLinearMap) v =
    exteriorPower.map p A.toLinearMap (exteriorPower.map p B.toLinearMap v)
  rw [exteriorPower.map_comp]
  rfl

end SmoothObstruction.ExteriorStability

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_SmoothScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Filter Topology
open scoped Real

namespace SmoothObstruction.ExteriorStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
@[simp] theorem exterior_zero (A : E →L[ℝ] E) : exterior 0 A = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  apply (exteriorPower.zeroEquiv ℝ E).injective
  exact congrArg (fun f : (⋀[ℝ]^0 E) →ₗ[ℝ] ℝ => f v)
    (exteriorPower.zeroEquiv_naturality A.toLinearMap)
@[simp] theorem exterior_zero_difference (A B : E →L[ℝ] E) :
    exterior 0 B - exterior 0 A = 0 := by simp
end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.SmoothScales
/-- The spatial exponent in the manuscript, with its literal positive root. -/
noncomputable def B (b : ℝ) : ℝ := b ^ (1 / 8 : ℝ)

end SmoothObstruction.SmoothScales

namespace SmoothObstruction.RelativeAsymptotics
open Filter Topology

/-- A single, choice-independent numerical envelope for all the relative
exterior errors at a given dyadic scale. -/
noncomputable def envelope (C C₀ C₁ C₂ C₃ b n : ℝ) : ℝ :=
  2 * C * C₃ * Real.exp C₂ *
    (n * Real.exp (-(3 / 2 : ℝ) * SmoothScales.B b * n +
      (2 * C₁ + C₀) * b * n))

end SmoothObstruction.RelativeAsymptotics

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_SplittingStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SmoothObstruction.ExteriorStability
open Module Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Actual projected maximal minor in fixed orthonormal endpoint coordinates.
The rows use the selected projection coordinates and the columns are arbitrary
starting vectors; starting bases need not be orthogonal. -/
noncomputable def projectedMinor (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (s : powersetCard ι p) (A : E →L[ℝ] E) (v : Fin p → E) : ℝ :=
  (b.exteriorPower p).repr (exterior p A (exteriorPower.ιMulti ℝ p v)) s

/-- A uniform local modulus for the wedge of a fixed number of vectors.
This is used when replacing actual subspaces by fixed frame-bin references. -/
theorem exists_wedge_lipschitz (p : ℕ) (R : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ v w : Fin p → E,
      ‖v‖≤R → ‖w‖≤R →
      ‖exteriorPower.ιMulti ℝ p v-exteriorPower.ιMulti ℝ p w‖≤C*‖v-w‖ := by
  obtain ⟨C,hC⟩ := (contDiff_wedge (E:=E) p).contDiffOn.exists_lipschitzOnWith
    (by simp) (convex_closedBall (0 : Fin p → E) R) (isCompact_closedBall 0 R)
  refine ⟨C,C.coe_nonneg,fun v w hv hw => ?_⟩
  simpa only [dist_eq_norm] using hC.dist_le_mul v
    (by simpa only [Metric.mem_closedBall,dist_zero_right] using hv) w
    (by simpa only [Metric.mem_closedBall,dist_zero_right] using hw)

end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.CloseProjection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Extend the inverse endpoint restriction back to an ambient linear map.
It is a left inverse on the actual moving fast space, with uniform norm 2. -/
noncomputable def ambientInverse (U V : Submodule ℝ E)
    (hdim : Module.finrank ℝ U=Module.finrank ℝ V)
    (hclose : ‖U.starProjection-V.starProjection‖≤1/2) : E →L[ℝ] E :=
  U.subtypeL.comp ((equiv U V hdim hclose).symm.toContinuousLinearMap.comp
    V.orthogonalProjectionOnto)

end SmoothObstruction.CloseProjection

namespace SmoothObstruction.ExteriorStability
open Module Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Continuity is proved from the actual determinant polynomial. -/
noncomputable def continuousWedge (p : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin p => E) (⋀[ℝ]^p E) where
  toMultilinearMap := (exteriorPower.ιMulti ℝ p).toMultilinearMap
  cont := (contDiff_wedge p).continuous

end SmoothObstruction.ExteriorStability

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_MinorTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SmoothObstruction.ExteriorStability
open Set Module
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma projected_frame_distance (p : ℕ) (F G : Submodule ℝ E)
    (w : Fin p → E) (hw : ∀ i,w i∈G) (hnorm : ∀ i,‖w i‖≤1)
    {δ : ℝ} (hδ : 0≤δ) (hclose : ‖F.starProjection-G.starProjection‖≤δ) :
    ‖(fun i => F.starProjection (w i))-w‖≤δ := by
  apply (pi_norm_le_iff_of_nonneg hδ).mpr
  intro i
  have he : F.starProjection (w i)-w i=(F.starProjection-G.starProjection) (w i) := by
    rw [_root_.sub_apply,G.starProjection_eq_self_iff.mpr (hw i)]
  change ‖F.starProjection (w i)-w i‖≤δ
  rw [he]
  exact ((F.starProjection-G.starProjection).le_opNorm (w i)).trans
    ((mul_le_mul hclose (hnorm i) (norm_nonneg _) hδ).trans_eq (mul_one _))

/-- One dimension-dependent uniform constant controls projected common
frames. This bypasses choosing a continuously varying orthonormal basis:
project the reference columns and use their determinant volume directly. -/
theorem exists_common_frame_wedge_control (p : ℕ) :
    ∃ L : ℝ,1≤L ∧ ∀ (F G : Submodule ℝ E) (w : Fin p → E)
      (δ : ℝ), (∀ i,w i∈G) → (∀ i,‖w i‖≤1) → 0≤δ →
      ‖F.starProjection-G.starProjection‖≤δ →
      ‖exteriorPower.ιMulti ℝ p (fun i => F.starProjection (w i))-
        exteriorPower.ιMulti ℝ p w‖≤L*δ := by
  obtain ⟨L,hL,hbound⟩ := exists_wedge_lipschitz (E:=E) p 1
  refine ⟨max L 1,le_max_right _ _,?_⟩
  intro F G w δ hw hnorm hδ hclose
  have hp : ‖fun i => F.starProjection (w i)‖≤1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
    intro i
    exact (F.norm_starProjection_apply_le (w i)).trans (hnorm i)
  have hw' : ‖w‖≤1 := (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr hnorm
  exact (hbound _ w hp hw').trans
    (mul_le_mul (le_max_left _ _) (projected_frame_distance p F G w hw hnorm hδ hclose)
      (norm_nonneg _) (le_trans hL (le_max_left _ _)))

end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.ExteriorStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def frameWedgeConstant (p : ℕ) : ℝ :=
  (exists_common_frame_wedge_control (E:=E) p).choose

end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.ExteriorStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def unitWedgeConstant (p : ℕ) : ℝ :=
  max (exists_wedge_lipschitz (E:=E) p 1).choose 1

end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.ExteriorStability
open Set Matrix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Actual endpoint-coordinate matrix; columns are the represented starting
vectors. Unlike the exterior-coordinate scalar formula, this uses the usual
matrix convention (output row, input column). -/
noncomputable def endpointMatrix (b : OrthonormalBasis ι ℝ E) (p : ℕ)
    (r : powersetCard ι p) (A : E →L[ℝ] E) {n : ℕ} (v : Fin n → E) :
    Matrix (Fin p) (Fin n) ℝ :=
  fun i j => b.repr (A (v j)) (powersetCard.ofFinEmbEquiv.symm r i)

end SmoothObstruction.ExteriorStability

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_NonlinearMatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.SmoothRemainder
open Set Metric
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def remainder (f : E → F) (x u : E) : F :=
  f (x+u)-f x-(fderiv ℝ f x) u

@[simp] lemma remainder_zero (f : E → F) (x : E) : remainder f x 0=0 := by
  simp [remainder]

end SmoothObstruction.SmoothRemainder

namespace SmoothObstruction.ArrayRemainder
open Set Metric
variable {E H G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H]
  [NormedAddCommGroup G]
  {n₁ n₂ : ℕ}

abbrev Paths (E : Type*) (n₁ n₂ : ℕ) := (Fin (n₁+1) → E) × (Fin (n₂+1) → E)
abbrev Data (E H G : Type*) (n₁ n₂ : ℕ) :=
  (Fin n₁ → E) × (Fin n₂ → E) × E × H × G

/-- Actual one-step Taylor residuals. The affine matching and terminal
constraints really have zero residual. -/
noncomputable def residual (f₁ : Fin n₁ → E → E) (f₂ : Fin n₂ → E → E)
    (x₁ : Fin n₁ → E) (x₂ : Fin n₂ → E)
    (v : Paths E n₁ n₂) : Data E H G n₁ n₂ :=
  (fun t => SmoothRemainder.remainder (f₁ t) (x₁ t) (v.1 t.castSucc),
    fun t => SmoothRemainder.remainder (f₂ t) (x₂ t) (v.2 t.castSucc),0,0,0)

@[simp] lemma residual_zero (f₁ : Fin n₁ → E → E) (f₂ : Fin n₂ → E → E)
    (x₁ : Fin n₁ → E) (x₂ : Fin n₂ → E) :
    residual (H:=H) (G:=G) f₁ f₂ x₁ x₂ 0=0 := by
  simp [residual,funext_iff]

end SmoothObstruction.ArrayRemainder

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_ManifoldMatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.ShortBin
noncomputable def bvpGrowth (K a : ℝ) (n : ℕ) : ℝ := Real.exp (2*K+a*n)+2
noncomputable def bvpInverseBound (K a : ℝ) (n : ℕ) : ℝ :=
  let U := bvpGrowth K a n
  let D := (2*U+U^4)*(n+n : ℕ)+U^2
  (U+U^4)*(4*Real.exp (2*K))*(1+2*D)+D
end SmoothObstruction.ShortBin

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology Metric MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

noncomputable def BilateralGauge.forward (S : Diffeomorph I I M M ∞)
    (a : ι → M) (c : M → ι) {n : ℕ} {B R : ℝ} {x : M}
    (A : BilateralGauge I S a c n B R x) : ShortBin.Gauge d n B :=
  ShortBin.Gauge.ofFinite A.UF A.VF A.lam (fun t _ => A.invF t) A.normF

noncomputable def BilateralGauge.backward (S : Diffeomorph I I M M ∞)
    (a : ι → M) (c : M → ι) {n : ℕ} {B R : ℝ} {x : M}
    (A : BilateralGauge I S a c n B R x) : ShortBin.Gauge d n B :=
  ShortBin.Gauge.ofFinite A.UB A.VB (fun j => -A.lam j) (fun t _ => A.invB t) A.normB

end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology Metric MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- Spaces of the genuine long-window gauge in its original endpoint chart. -/
noncomputable def BilateralGauge.forwardSpace (S : Diffeomorph I I M M ∞)
    (a : ι → M) (c : M → ι) {n : ℕ} {B R : ℝ} {x : M}
    (A : BilateralGauge I S a c n B R x) (t : ℕ) (T : Finset (Fin d)) :=
  EuclideanSplitting.groupSpace (A.UF t) (A.VF t) (A.invF t).1 (A.invF t).2 T

noncomputable def BilateralGauge.backwardSpace (S : Diffeomorph I I M M ∞)
    (a : ι → M) (c : M → ι) {n : ℕ} {B R : ℝ} {x : M}
    (A : BilateralGauge I S a c n B R x) (t : ℕ) (T : Finset (Fin d)) :=
  EuclideanSplitting.groupSpace (A.UB t) (A.VB t) (A.invB t).1 (A.invB t).2 T

end SmoothObstruction.ManifoldCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_TubeProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.FiniteBins
open Set
variable {X C : Type*} (P : X → C) (G : Set X)
/-- Only bins meeting the original good set require a reference. -/
def Active := {c : C // ∃ x∈G,P x=c}
def Fiber (c : Active P G) := {x : G // P x=c.val}

noncomputable def reference (c : Active P G) : Fiber P G c := by
  classical
  apply Classical.choice
  obtain ⟨x,hx,hP⟩ := c.property
  exact ⟨⟨⟨x,hx⟩,hP⟩⟩

instance instFiniteActive [Finite C] : Finite (Active P G) :=
  inferInstanceAs (Finite {category : C // ∃ point∈G,P point=category})
end SmoothObstruction.FiniteBins

namespace SmoothObstruction.ManifoldCoordinates
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} (S : Diffeomorph I I M M ∞) (a : ι → M) (c : M → ι)
    {n : ℕ} {B R : ℝ} {x : M}

/-- Time reversal keeps the original gauge and negates its rates; it is not
an independently selected certificate. -/
noncomputable def BilateralGauge.reverse (A : BilateralGauge I S a c n B R x) :
    BilateralGauge I S.symm a c n B R x where
  lam := fun j => -A.lam j
  rate_bound j := by simpa only [abs_neg] using A.rate_bound j
  UF := A.UB
  VF := A.VB
  UB := A.UF
  VB := A.VF
  invF := A.invB
  invB := A.invF
  centerU := A.centerU.symm
  centerV := A.centerV.symm
  normF := A.normB
  normB := A.normF
  stepF := A.stepB
  stepB t ht := by
    have he : S.symm.symm = S := by ext x; rfl
    simpa only [he,neg_neg] using A.stepF t ht

@[simp] lemma BilateralGauge.reverse_forwardSpace (A : BilateralGauge I S a c n B R x)
    (t : ℕ) (T : Finset (Fin d)) :
    (A.reverse I S a c).forwardSpace I S.symm a c t T=A.backwardSpace I S a c t T := rfl

end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.FiniteBins
open Set
variable {X C Z : Type*} (P : X → C) (G : Set X)
def key (x : G) : Active P G := ⟨P x,⟨x,x.property,rfl⟩⟩
noncomputable def extend (f : Active P G → Z) (z₀ : Z) (c : C) : Z := by
  classical
  exact if h : ∃ x∈G,P x=c then f ⟨c,h⟩ else z₀
@[simp] lemma extend_active (f : Active P G → Z) (z₀ : Z) (c : Active P G) :
    extend P G f z₀ c.val=f c := by
  classical
  simp only [extend,dite_eq_left c.property]
  congr 1
@[simp] lemma extend_key (f : Active P G → Z) (z₀ : Z) (x : G) :
    extend P G f z₀ (P x)=f (key P G x) := extend_active P G f z₀ (key P G x)
end SmoothObstruction.FiniteBins

namespace SmoothObstruction.ManifoldCoordinates
open Set Filter Topology Metric MeasureTheory FiniteBins
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι C : Type*} [Fintype ι]

noncomputable def fastSet (v : Fin d → ℝ) (γ : ℝ) : Finset (Fin d) := by
  classical
  exact Finset.univ.filter (fun j => γ<v j)
noncomputable def slowSet (v : Fin d → ℝ) (γ : ℝ) : Finset (Fin d) := by
  classical
  exact Finset.univ.filter (fun j => v j≤γ)
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} (S : Diffeomorph I I M M ∞) (a : ι → M) (c : M → ι)
    {n : ℕ} {B R : ℝ} {x : M}
open FiniteGreen ShortBin

/-- An old tube tests the candidate in the original input's selected charts.
The candidate is not required to belong to the good set. -/
def originalTube (δ : ℝ) (x z : M) : Prop :=
  ∀ t : Fin (n+1),S^[t.val] z∈(chartAt H (a (c (S^[t.val] x)))).source ∧
    ‖(extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] z)-
      (extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)‖≤δ

/-- Fixed endpoint projection, still based on the old input's endpoint chart. -/
def originalEndpoint (V : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (x z : M) : Prop :=
  V.starProjection ((extChartAt I (a (c (S^[n] x)))) (S^[n] z))=
    V.starProjection ((extChartAt I (a (c (S^[n] x)))) (S^[n] x))
end SmoothObstruction.ManifoldCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_ProductCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.ProductBasis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable def blockMap (U V : Submodule ℝ E) (h : IsCompl U V)
    (bU : OrthonormalBasis ι ℝ U) (bV : OrthonormalBasis κ ℝ V) :
    EuclideanSpace ℝ (ι ⊕ κ) ≃L[ℝ] E :=
  EuclideanSpace.sumEquivProd.trans
    ((bU.repr.symm.toContinuousLinearEquiv.prodCongr bV.repr.symm.toContinuousLinearEquiv).trans
      (U.prodEquivOfIsCompl V h).toContinuousLinearEquiv)

end SmoothObstruction.ProductBasis

namespace SmoothObstruction.FiniteGreen.Splitting
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {T : Evolution E} (B : Splitting T)

lemma ranges_isCompl (t : ℕ) : IsCompl (B.slow t).range (B.fast t).range := by
  refine ⟨Submodule.disjoint_def.mpr ?_,codisjoint_iff.mpr ?_⟩
  · intro x hx hy
    obtain ⟨u,hu⟩ := hx
    obtain ⟨v,hv⟩ := hy
    have hs : B.slow t x=x := by
      rw [←hu]
      change B.slow t (B.slow t u)=B.slow t u
      exact B.slow_self t u
    have hf : B.slow t x=0 := by
      rw [←hv]
      change B.slow t (B.fast t v)=0
      exact B.slow_fast t v
    exact hs.symm.trans hf
  · apply top_unique
    intro x _
    exact Submodule.mem_sup.mpr ⟨B.slow t x,⟨x,rfl⟩,B.fast t x,⟨x,rfl⟩,B.add_apply t x⟩

end SmoothObstruction.FiniteGreen.Splitting

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_EndpointFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Filter Topology
open scoped Real

namespace SmoothObstruction.EndpointFrame
open Set Matrix
open scoped EuclideanGeometry
variable {d p : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual selected orthonormal coordinates, not a formal minor proxy. -/
noncomputable def coordinates (b : OrthonormalBasis (Fin d) ℝ E)
    (r : powersetCard (Fin d) p) : E →L[ℝ] EuclideanSpace ℝ (Fin p) :=
  LinearMap.toContinuousLinearMap {
    toFun x := WithLp.toLp 2 (fun i => b.repr x (powersetCard.ofFinEmbEquiv.symm r i))
    map_add' x y := by ext i; simp
    map_smul' c x := by ext i; simp }

@[simp] lemma coordinates_apply (b : OrthonormalBasis (Fin d) ℝ E)
    (r : powersetCard (Fin d) p) (x : E) (i : Fin p) :
    coordinates b r x i=b.repr x (powersetCard.ofFinEmbEquiv.symm r i) := rfl

end SmoothObstruction.EndpointFrame

namespace SmoothObstruction.EndpointFrame
open Set Matrix ProductBasis ExteriorStability
variable {d p q : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ (Fin p ⊕ Fin q)

noncomputable def joint (bF bP : OrthonormalBasis (Fin d) ℝ E)
    (rF : powersetCard (Fin d) p) (rP : powersetCard (Fin d) q)
    (f g : E → E) (x : E) : F :=
  EuclideanSpace.sumEquivProd.symm (coordinates bF rF (f x),coordinates bP rP (g x))

noncomputable def jointLinear (bF bP : OrthonormalBasis (Fin d) ℝ E)
    (rF : powersetCard (Fin d) p) (rP : powersetCard (Fin d) q)
    (A B : E →L[ℝ] E) : E →L[ℝ] F :=
  EuclideanSpace.sumEquivProd.symm.toContinuousLinearMap.comp
    (((coordinates bF rF).comp A).prod ((coordinates bP rP).comp B))

end SmoothObstruction.EndpointFrame

namespace SmoothObstruction.EndpointBranch
open Filter Topology
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable def derivative (A B C D : E ≃L[ℝ] E)
    (σ : (E×E) ≃L[ℝ] (E×E)) : (E×E) ≃L[ℝ] (E×E) :=
  ((A.prodCongr B).trans σ).trans (C.prodCongr D).symm

section Exchange
variable {F P : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Exchange the past coordinates and leave the future coordinates fixed. -/
def exchange : ((F×P)×(F×P)) ≃L[ℝ] ((F×P)×(F×P)) where
  toFun u := ((u.1.1,u.2.2),(u.2.1,u.1.2))
  invFun u := ((u.1.1,u.2.2),(u.2.1,u.1.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end Exchange
end SmoothObstruction.EndpointBranch

namespace SmoothObstruction.EndpointBranch
open Filter Topology
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def equiv_of_det (A : E →L[ℝ] E) (hA : A.det≠0) : E ≃L[ℝ] E :=
  (LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr hA)).toContinuousLinearEquiv

omit [CompleteSpace E] in
@[simp] lemma equiv_of_det_coe (A : E →L[ℝ] E) (hA : A.det≠0) :
    (equiv_of_det A hA : E →L[ℝ] E)=A := by
  ext x
  exact LinearMap.equivOfIsUnitDet_apply _ x

end SmoothObstruction.EndpointBranch

namespace SmoothObstruction.EndpointBranch
open Filter Topology
open scoped ContDiff
variable {p q : ℕ}
local notation "F" => EuclideanSpace ℝ (Fin p ⊕ Fin q)

/-- The exact future/past exchange in the orthonormal sum coordinates used
for the endpoint block matrices. -/
noncomputable def sumExchange : (F×F) ≃L[ℝ] (F×F) :=
  let e : F ≃L[ℝ] (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) :=
    EuclideanSpace.sumEquivProd
  (e.prodCongr e).trans (exchange.trans (e.prodCongr e).symm)

end SmoothObstruction.EndpointBranch

namespace SmoothObstruction.EndpointFrame
open Set Matrix ProductBasis ExteriorStability Filter Topology
open scoped ContDiff
variable {d p q : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The same leading minor is used at the old and perturbed point. -/
def GoodEndpoint {r s : ℕ} (δ : ℝ)
    (b : OrthonormalBasis (Fin d) ℝ E) (a : powersetCard (Fin d) r)
    (u : Fin r → E) (v : Fin s → E) (f : E → E) (x : E)
    (D₀ : Matrix (Fin r) (Fin r) ℝ) : Prop :=
  ContDiffAt ℝ ∞ f x ∧ D₀.det≠0 ∧
    |(endpointMatrix b r a (fderiv ℝ f x) u).det/D₀.det-1|≤(1/100:ℝ) ∧
    ∀ i j,|((endpointMatrix b r a (fderiv ℝ f x) u)⁻¹*
      endpointMatrix b r a (fderiv ℝ f x) v) i j|≤δ

end SmoothObstruction.EndpointFrame

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_GridCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.GridMargin
open Set MeasureTheory

/-- The deleted street for one of N translated grids of the same mesh Nδ. -/
def street (δ : ℝ) (N : ℕ) (k : Fin N) : Set ℝ :=
  {x | ∃ j : ℤ, |x-δ*((N:ℝ)*j+k.val)|≤δ/4}

end SmoothObstruction.GridMargin

namespace SmoothObstruction.GridMargin
open Set MeasureTheory
variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]

/-- The precise regular translated-grid label. -/
noncomputable def gridIndex (δ : ℝ) (N : ℕ) (k : Fin N) (x : ℝ) : ℤ :=
  ⌊(x-δ*k.val)/(δ*N)⌋

/-- Bounded integer labels are encoded without enlarging the physical cells. -/
def boundedLabel (m : ℕ) (j : ℤ) : Fin (2*m+1) :=
  ⟨(max 0 (min (2*m : ℤ) (j+m))).toNat,by omega⟩

/-- Arbitrary bounded coordinates give a genuine finite measurable partition,
with exactly this finite alphabet, rather than an assumed cardinal bound. -/
noncomputable def productLabel (m : ℕ) (δ : ℝ) (N : ℕ) (k : ι → Fin N)
    (c : X → ι → ℝ) (x : X) : ι → Fin (2*m+1) :=
  fun i =>  boundedLabel m (gridIndex δ N (k i) (c x i))

end SmoothObstruction.GridMargin

namespace SmoothObstruction.GridRefinement
open Set MeasureTheory
open SmoothObstruction.GridMargin
variable {X C ι : Type*} [MeasurableSpace X] [Fintype C]
  [MeasurableSpace C] [MeasurableSingletonClass C] [Fintype ι] [DecidableEq ι]

noncomputable def label (P : X → C) (c : C → X → ι → ℝ)
    (m : ℕ) (δ : ℝ) (N : ℕ) (k : C → ι → Fin N) (x : X) :
    C × (ι → Fin (2*m+1)) :=
  (P x,productLabel m δ N (k (P x)) (c (P x)) x)

end SmoothObstruction.GridRefinement

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_PairLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped Classical
open Finset

namespace SmoothObstruction.PairLaw
open MeasureTheory Set Finset
open scoped ENNReal
variable {X α : Type*} [MeasurableSpace X] [Fintype α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

noncomputable abbrev cell (μ : Measure X) (P : X → α) (a : α) : Measure X :=
  μ.restrict (P ⁻¹' {a})

/-- The manuscript's original, unnormalized-on-retained-pairs law. All
zero-mass cells contribute zero; no conditional renormalization is used. -/
noncomputable def law (μ : Measure X) (P : X → α) : Measure (X × X) :=
  ∑ a, (μ (P ⁻¹' {a}))⁻¹ • (cell μ P a).prod (cell μ P a)

lemma sum_cells (μ : Measure X) (P : X → α) (hP : Measurable P) :
    ∑ a,cell μ P a=μ := by
  have hd : Pairwise (fun a b => Disjoint (P ⁻¹' {a}) (P ⁻¹' {b})) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    intro x hxa hxb
    exact hab ((Set.mem_singleton_iff.mp hxa).symm.trans (Set.mem_singleton_iff.mp hxb))
  have hu : (⋃ a,P ⁻¹' {a})=univ := by ext x; simp
  have hh := Measure.restrict_iUnion (μ:=μ) hd (fun a => hP (measurableSet_singleton a))
  rw [hu,Measure.restrict_univ,Measure.sum_fintype] at hh
  exact hh.symm

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma normalized_cell (μ : Measure X) [IsFiniteMeasure μ] (P : X → α) (a : α) :
    ((μ (P ⁻¹' {a}))⁻¹ * (cell μ P a) univ) • cell μ P a=cell μ P a := by
  rw [cell,Measure.restrict_apply MeasurableSet.univ,univ_inter]
  by_cases hz : μ (P ⁻¹' {a})=0
  · rw [Measure.restrict_eq_zero.mpr hz,smul_zero]
  · rw [ENNReal.inv_mul_cancel hz (measure_ne_top _ _),one_smul]

lemma first_marginal (μ : Measure X) [IsFiniteMeasure μ] (P : X → α) (hP : Measurable P) :
    (law μ P).map Prod.fst=μ := by
  rw [law,←Measure.mapₗ_apply_of_measurable measurable_fst,map_sum]
  simp only [Measure.mapₗ_apply_of_measurable measurable_fst,
    Measure.map_smul,
    Measure.map_fst_prod,smul_smul,normalized_cell]
  exact sum_cells μ P hP

theorem law_probability (μ : Measure X) [IsProbabilityMeasure μ] (P : X → α)
    (hP : Measurable P) : IsProbabilityMeasure (law μ P) := by
  apply isProbabilityMeasure_iff.mpr
  have hh := congrArg (fun ν : Measure X => ν univ) (first_marginal μ P hP)
  simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,preimage_univ,measure_univ] using hh

end SmoothObstruction.PairLaw

end

section

namespace SmoothObstruction
open MeasureTheory Filter Topology Set
open scoped ENNReal
/-- A finite original cell-weighted pair law and its measurable switch.
The carrier is not normalized and no sigma-algebra on the retained subtype
is silently substituted for the ambient original pair law. -/
structure SwitchData {M : Type} [MeasurableSpace M] (μ : Measure M) where
  J : Type
  fin : Fintype J
  meas : MeasurableSpace J
  singletons : MeasurableSingletonClass J
  label : M → J
  carrier : Set (M×M)
  point : M×M → M
  label_measurable : Measurable label
  carrier_measurable : MeasurableSet carrier
  point_measurable : Measurable point
attribute [instance] SwitchData.fin SwitchData.meas SwitchData.singletons
namespace SwitchData
variable {M : Type} [MeasurableSpace M] {μ : Measure M}
noncomputable def law (D : SwitchData μ) : Measure (M×M) := PairLaw.law μ D.label
noncomputable def retained (D : SwitchData μ) : Measure (M×M) := D.law.restrict D.carrier
def Good (D : SwitchData μ) (η C B : ℝ) (n : ℕ) : Prop :=
  (Fintype.card D.J : ℝ)≤Real.exp (C*B*n) ∧ 1-η≤D.law.real D.carrier ∧
    D.retained.map D.point≤(2:ℝ≥0∞) • μ
end SwitchData
/-- The literal quantitative smooth switching property, with one fixed
sequence of original finite cell laws, summable sixteenth powers, and
uniform two-sided shadowing over the full dyadic windows. -/
def SmoothSwitching {M : Type} [MetricSpace M] [MeasurableSpace M]
    (μ : Measure M) (S Sinv : M → M) : Prop :=
  ∀ η : ℝ,0<η → ∃ (B : ℕ → ℝ) (C : ℝ) (D : ℕ → SwitchData μ),
    (∀ k,0<B k) ∧ Summable (fun k => (B k)^16) ∧
    (∀ᶠ k in atTop,(D k).Good η C (B k) (2^k)) ∧
    ∀ ε : ℝ,0<ε → ∀ᶠ k in atTop,∀ u∈(D k).carrier,∀ t v : Fin (2^k+1),
      dist (S^[t.val] ((D k).point u)) (S^[t.val] u.1)+
      dist (Sinv^[v.val] ((D k).point u)) (Sinv^[v.val] u.2)<ε
end SmoothObstruction

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_EndpointMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped BigOperators
open scoped ContDiff BigOperators
open Module
open Filter Topology
open scoped Real

namespace SmoothObstruction.EndpointBudget
open Filter Topology
noncomputable def leading (C K : ℝ) (p : ℕ) : ℝ := (C*(Real.exp K)^p)^2*(C*2^p)
noncomputable def normCost (C K N : ℝ) (p : ℕ) : ℝ := C*(C^2*(Real.exp K)^(2*p)*N)
noncomputable def mixedCost (C K N V : ℝ) (p : ℕ) : ℝ := C*(C*(Real.exp K)^p)^2*N*V
noncomputable def relative (C Crel C₁ C₂ C₃ D V b n : ℝ) (p : ℕ) : ℝ :=
  2*leading C (D*b*n) p*C*
    (RelativeAsymptotics.envelope Crel 0 C₁ C₂ C₃ b n*
      Real.exp (RelativeAsymptotics.envelope Crel 0 C₁ C₂ C₃ b n))*V
noncomputable def graph (C D N V W b n δ : ℝ) (p : ℕ) : ℝ :=
  2*leading C (D*b*n) p*
    (mixedCost C (D*b*n) N V p*Real.exp (-2*b^(1/2:ℝ)*n)+normCost C (D*b*n) N p*W*δ)

end SmoothObstruction.EndpointBudget

end

section

namespace SmoothObstruction.EndpointBudget
open Set EndpointFrame ExteriorStability
/-- Literal three errors entering the actual endpoint-minor theorem. -/
def admissible (d p : ℕ) (Dg R C K₀ Crel C₁ b n g δ β : ℝ) : Prop :=
  let K := Dg*(b*n)
  let L₀ := (C*(Real.exp K)^p)^2*(C*2^p)
  let N₀ := C*(C^2*(Real.exp K)^(2*p)*(Fintype.card (powersetCard (Fin d) p) : ℝ))
  let N₁ := C*(C*(Real.exp K)^p)^2*(Fintype.card (powersetCard (Fin d) p) : ℝ)*‖continuousWedge (E := EuclideanSpace ℝ (Fin d)) p‖
  let ζ := RelativeAsymptotics.envelope Crel 0 C₁ (d*R) K₀ b n *
    Real.exp (RelativeAsymptotics.envelope Crel 0 C₁ (d*R) K₀ b n)
  let ε := 2*L₀*C*ζ*‖continuousWedge (E := EuclideanSpace ℝ (Fin d)) p‖
  let θ := 2*L₀*(N₁*Real.exp (-2*g*n)+N₀*unitWedgeConstant (E := EuclideanSpace ℝ (Fin d)) p*δ)
  (frameWedgeConstant (E := EuclideanSpace ℝ (Fin d)) p*δ)*(1+L₀*N₀)≤1/2 ∧
    ε≤1/100 ∧ (θ+ε)/(1-ε)≤β
end SmoothObstruction.EndpointBudget

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology EndpointFrame
open scoped Manifold ContDiff
variable {d p q : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

def OriginalEndpointControl (S : Diffeomorph I I M M ∞) (a : ι → M) (c : M → ι)
    (n : ℕ) (ρ β : ℝ) (W : Submodule ℝ E₀) (u : Fin p → E₀) (v : Fin q → E₀) (x : M) : Prop :=
  ∃ (b : OrthonormalBasis (Fin d) ℝ E₀) (r : powersetCard (Fin d) p)
    (D : Matrix (Fin p) (Fin p) ℝ),
    (∀ j∈r,b j∈W) ∧ (∀ z∈W,∀ j∉r,b.repr z j=0) ∧
    ∀ y,originalTube I S a c (n:=n) ρ x y →
      GoodEndpoint β b r u v
        (extChartAt I (a (c (S^[n] x))) ∘ S^[n] ∘ (extChartAt I (a (c x))).symm)
        ((extChartAt I (a (c x))) y) D

end SmoothObstruction.ManifoldCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_FiniteEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

namespace SmoothObstruction

namespace FiniteEntropy

variable {α β γ : Type*}

noncomputable def natEntropy [Fintype α] (p : α → ℝ) : ℝ := ∑ a, Real.negMulLog (p a)

/-- The high-atom mass of a finite law at threshold exp(-a log L). -/
noncomputable def heavyMass [Fintype α] (a : ℝ) (p : α → ℝ) : ℝ :=
  ∑ i, if Real.exp (-a * Real.log (Fintype.card α)) < p i then p i else 0

end FiniteEntropy
end SmoothObstruction

namespace SmoothObstruction.FiniteEntropy

open Finset
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

noncomputable def leftMass (p : α × β → ℝ) (a : α) : ℝ := ∑ b, p (a,b)
noncomputable def rightMass (p : α × β → ℝ) (b : β) : ℝ := ∑ a, p (a,b)

/-- Pushing a finite entropy vector through a deterministic map cannot
increase entropy. There is no measurability or independence assumption. -/
noncomputable def pushMass (p : α → ℝ) (f : α → β) (b : β) : ℝ := by
  classical
  exact ∑ a, if f a = b then p a else 0

end SmoothObstruction.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_FiniteLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

namespace SmoothObstruction.FiniteLaw

variable (A : Type*) [Fintype A]

structure Law where
  mass : A → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

variable {A}

noncomputable def expect (P : Law A) (f : A → ℝ) : ℝ := ∑ a, P.mass a * f a

lemma expect_nonneg (P : Law A) {f : A → ℝ} (hf : ∀ a, 0 ≤ f a) :
    0 ≤ expect P f := sum_nonneg (fun a _ => mul_nonneg (P.nonneg a) (hf a))

lemma expect_mono (P : Law A) {f g : A → ℝ} (h : ∀ a, f a ≤ g a) :
    expect P f ≤ expect P g := sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (h a) (P.nonneg a))

@[simp] lemma expect_const (P : Law A) (c : ℝ) : expect P (fun _ => c) = c := by
  simp [expect, ← sum_mul, P.total]

lemma expect_add (P : Law A) (f g : A → ℝ) :
    expect P (fun a => f a + g a) = expect P f + expect P g := by
  simp only [expect, mul_add, sum_add_distrib]

lemma expect_sub (P : Law A) (f g : A → ℝ) :
    expect P (fun a => f a - g a) = expect P f - expect P g := by
  simp only [expect, mul_sub, sum_sub_distrib]

lemma expect_mul_const (P : Law A) (f : A → ℝ) (c : ℝ) :
    expect P (fun a => f a * c) = expect P f * c := by
  simp only [expect, ← mul_assoc, sum_mul]

lemma expect_const_mul (P : Law A) (c : ℝ) (f : A → ℝ) :
    expect P (fun a => c * f a) = c * expect P f := by
  simpa only [mul_comm] using expect_mul_const P f c

lemma expect_sum {I : Type*} [Fintype I] (P : Law A) (f : I → A → ℝ) :
    expect P (fun a => ∑ i, f i a) = ∑ i, expect P (f i) := by
  simp only [expect, mul_sum]
  exact sum_comm

lemma expect_sq_abs (P : Law A) (f : A → ℝ) :
    (expect P (fun a => |f a|)) ^ 2 ≤ expect P (fun a => f a ^ 2) := by
  have h := sum_sq_le_sum_mul_sum_of_sq_le_mul univ
    (f := P.mass) (g := fun a => P.mass a * f a ^ 2)
    (r := fun a => P.mass a * |f a|)
    (fun a _ => P.nonneg a) (fun a _ => mul_nonneg (P.nonneg a) (sq_nonneg _))
    (fun a _ => by rw [mul_pow, sq_abs]; ring_nf; exact le_rfl)
  simpa only [P.total, one_mul, expect] using h

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def product (P : I → Law A) : Law (I → A) where
  mass x := ∏ i, (P i).mass (x i)
  nonneg x := prod_nonneg (fun i _ => (P i).nonneg _)
  total := by
    classical
    have h := prod_univ_sum (fun _ : I => (univ : Finset A)) (fun i a => (P i).mass a)
    simp only [Fintype.piFinset_univ, (P _).total, prod_const_one] at h
    exact h.symm

lemma product_moment (P : I → Law A) (f : I → A → ℝ) :
    expect (product P) (fun x => ∏ i, f i (x i)) = ∏ i, expect (P i) (f i) := by
  classical
  simp only [expect, product, ← prod_mul_distrib]
  exact (show (∏ i, ∑ a, (P i).mass a * f i a) =
    ∑ x : I → A, ∏ i, (P i).mass (x i) * f i (x i) by
    simpa only [Fintype.piFinset_univ] using
      (prod_univ_sum (fun _ : I => (univ : Finset A)) (fun i a => (P i).mass a * f i a))).symm

lemma product_one_moment (P : I → Law A) (i : I) (f : A → ℝ) :
    expect (product P) (fun x => f (x i)) = expect (P i) f := by
  have h := product_moment P (fun j a => if j = i then f a else 1)
  simp only [Fintype.prod_ite_eq'] at h
  have he (j : I) : expect (P j) (fun a => if j = i then f a else 1) =
      if j = i then expect (P j) f else 1 := by
    split_ifs <;> simp [*]
  simp_rw [he] at h
  simpa only [Fintype.prod_ite_eq'] using h

lemma product_two_moment (P : I → Law A) {i j : I} (hij : i ≠ j)
    (f g : A → ℝ) :
    expect (product P) (fun x => f (x i) * g (x j)) =
      expect (P i) f * expect (P j) g := by
  have h := product_moment P (fun k a => (if k = i then f a else 1) *
    (if k = j then g a else 1))
  simp only [prod_mul_distrib, Fintype.prod_ite_eq'] at h
  have he (k : I) : expect (P k) (fun a => (if k = i then f a else 1) *
      (if k = j then g a else 1)) =
      (if k = i then expect (P k) f else 1) *
      (if k = j then expect (P k) g else 1) := by
    by_cases hi : k = i <;> by_cases hj : k = j <;> simp_all
  simp_rw [he] at h
  simpa only [prod_mul_distrib, Fintype.prod_ite_eq'] using h

variable [DecidableEq A]

noncomputable def condition (P : Law A) (E : Finset A) (hE : 0 < ∑ a ∈ E, P.mass a) : Law A where
  mass a := if a ∈ E then P.mass a / (∑ a ∈ E, P.mass a) else 0
  nonneg a := by split_ifs; exact div_nonneg (P.nonneg a) hE.le; exact le_rfl
  total := by
    classical
    simp only [sum_ite_mem, univ_inter, ← sum_div]
    exact div_self hE.ne'

lemma condition_bound (P : Law A) (E : Finset A) (hE : 1 / 2 ≤ ∑ a ∈ E, P.mass a)
    (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) :
    expect (condition P E (by linarith)) f ≤ 2 * expect P f := by
  change (∑ a, (if a ∈ E then P.mass a / (∑ a ∈ E, P.mass a) else 0) * f a) ≤
    2 * ∑ a, P.mass a * f a
  rw [mul_sum]
  simp only [← mul_assoc]
  apply sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_right _ (hf a)
  change (if a ∈ E then _ else 0) ≤ 2 * P.mass a
  split_ifs
  · apply (div_le_iff₀ (by linarith : 0 < ∑ a ∈ E, P.mass a)).mpr
    nlinarith [P.nonneg a]
  · exact mul_nonneg (by norm_num) (P.nonneg a)

end SmoothObstruction.FiniteLaw

namespace SmoothObstruction.FiniteLaw
open Finset

variable {A I J : Type*} [Fintype A] [Fintype I] [Fintype J] [DecidableEq I]

omit [DecidableEq I] in
lemma orthogonal_sum_square (P : Law A) (Z : I → A → ℝ)
    (h : ∀ i j, i ≠ j → expect P (fun x => Z i x * Z j x) = 0) :
    expect P (fun x => (∑ i, Z i x) ^ 2) = ∑ i, expect P (fun x => Z i x ^ 2) := by
  have hex (x : A) : (∑ i, Z i x) ^ 2 = ∑ i, ∑ j, Z i x * Z j x := by
    simp only [sq, sum_mul, mul_sum]
    exact sum_comm
  simp_rw [hex, expect_sum]
  apply sum_congr rfl
  intro i _
  rw [sum_eq_single i]
  · simp only [sq]
  · intro j _ hji
    exact h i j hji.symm
  · simp

lemma centered_square_le (P : Law A) (f : A → ℝ) (p : ℝ) (he : expect P f = p) :
    expect P (fun x => (f x - p) ^ 2) ≤ expect P (fun x => f x ^ 2) := by
  have hr (x : A) : (f x - p) ^ 2 = f x ^ 2 - 2 * p * f x + p ^ 2 := by ring
  simp_rw [hr, expect_add, expect_sub, expect_const_mul, expect_const, he]
  nlinarith [sq_nonneg p]

/-- The exact second-moment calculation for genuinely independent sampled
probability vectors. The vector's coordinates need not be independent. -/
lemma empirical_variance [Nonempty I] (P : I → Law A) (Y : I → A → J → ℝ)
    (p : J → ℝ) (hY : ∀ i x a, 0 ≤ Y i x a) (hs : ∀ i x, ∑ a, Y i x a = 1)
    (hm : ∀ i a, expect (P i) (fun x => Y i x a) = p a) :
    (∑ a, expect (product P) (fun x =>
      ((∑ i, Y i (x i) a) / Fintype.card I - p a) ^ 2)) ≤
        1 / Fintype.card I := by
  let q : ℝ := Fintype.card I
  have hq : 0 < q := Nat.cast_pos.mpr Fintype.card_pos
  have hcenter (i : I) (a : J) : expect (P i) (fun x => Y i x a - p a) = 0 := by
    rw [expect_sub, hm, expect_const, sub_self]
  have horth (a : J) (i j : I) (hij : i ≠ j) :
      expect (product P) (fun x => (Y i (x i) a - p a) * (Y j (x j) a - p a)) = 0 := by
    rw [product_two_moment P hij (fun x => Y i x a - p a) (fun x => Y j x a - p a),
      hcenter, hcenter, zero_mul]
  have hid (a : J) : expect (product P) (fun x =>
      ((∑ i, Y i (x i) a) / q - p a) ^ 2) =
      (∑ i, expect (P i) (fun x => (Y i x a - p a) ^ 2)) * (q ^ 2)⁻¹ := by
    have hx (x : I → A) : ((∑ i, Y i (x i) a) / q - p a) ^ 2 =
        (∑ i, (Y i (x i) a - p a)) ^ 2 * (q ^ 2)⁻¹ := by
      simp only [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
      change (_ / q - p a) ^ 2 = (_ - q * p a) ^ 2 * _
      field_simp [hq.ne']
    simp_rw [hx]
    rw [expect_mul_const, orthogonal_sum_square _ _ (horth a)]
    congr 1
    apply sum_congr rfl
    intro i _
    exact product_one_moment P i (fun x => (Y i x a - p a) ^ 2)
  have hb (i : I) : ∑ a, expect (P i) (fun x => (Y i x a - p a) ^ 2) ≤ 1 := by
    calc
      _ ≤ ∑ a, expect (P i) (fun x => Y i x a ^ 2) :=
        sum_le_sum (fun a _ => centered_square_le _ _ _ (hm i a))
      _ = expect (P i) (fun x => ∑ a, Y i x a ^ 2) := (expect_sum _ _).symm
      _ ≤ expect (P i) (fun _ => 1) := expect_mono _ (fun x => by
        simpa only [hs, one_pow] using sum_sq_le_sq_sum_of_nonneg (s := univ)
          (f := fun a => Y i x a) (fun a _ => hY i x a))
      _ = 1 := expect_const _ _
  change (∑ a, expect (product P) (fun x => ((∑ i, Y i (x i) a) / q - p a) ^ 2)) ≤ 1 / q
  simp_rw [hid]
  rw [← sum_mul, sum_comm]
  calc
    _ ≤ (∑ _i : I, (1 : ℝ)) * (q ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right (sum_le_sum (fun i _ => hb i)) (by positivity)
    _ = 1 / q := by
      simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]
      change q * (q ^ 2)⁻¹ = 1 / q
      field_simp [hq.ne']

/-- A finite form of the TV/second-moment inequality, including samples with
zero mass. -/
lemma expected_tv_of_second_moment (P : Law A) (Z : A → J → ℝ) {v : ℝ}
    (hv : 0 ≤ v) (hvar : ∑ a, expect P (fun x => Z x a ^ 2) ≤ v) :
    expect P (fun x => (1 / 2 : ℝ) * ∑ a, |Z x a|) ≤
      (1 / 2 : ℝ) * Real.sqrt (Fintype.card J * v) := by
  have hsq : (∑ a, expect P (fun x => |Z x a|)) ^ 2 ≤ Fintype.card J * v := by
    calc
      _ ≤ Fintype.card J * ∑ a, (expect P (fun x => |Z x a|)) ^ 2 := by
        simpa only [card_univ] using sq_sum_le_card_mul_sum_sq
          (s := (univ : Finset J)) (f := fun a => expect P (fun x => |Z x a|))
      _ ≤ Fintype.card J * ∑ a, expect P (fun x => Z x a ^ 2) := by
        apply mul_le_mul_of_nonneg_left (sum_le_sum (fun a _ => expect_sq_abs _ _))
        positivity
      _ ≤ Fintype.card J * v := mul_le_mul_of_nonneg_left hvar (by positivity)
  have hn : 0 ≤ (Fintype.card J : ℝ) * v := mul_nonneg (by positivity) hv
  have hroot := Real.sq_sqrt hn
  have hrnon := Real.sqrt_nonneg ((Fintype.card J : ℝ) * v)
  rw [expect_const_mul, expect_sum]
  have hsum : (∑ a, expect P (fun x => |Z x a|)) ≤ Real.sqrt (Fintype.card J * v) := by
    nlinarith
  linarith

/-- Source lem:word-tv, for independent complete vectors, with its literal
one-half constant. This is used twice, not an assumption about empirical laws. -/
theorem independent_vectors_tv [Nonempty I] (P : I → Law A) (Y : I → A → J → ℝ)
    (p : J → ℝ) (hY : ∀ i x a, 0 ≤ Y i x a) (hs : ∀ i x, ∑ a, Y i x a = 1)
    (hm : ∀ i a, expect (P i) (fun x => Y i x a) = p a) :
    expect (product P) (fun x => (1 / 2 : ℝ) *
      ∑ a, |(∑ i, Y i (x i) a) / Fintype.card I - p a|) ≤
        (1 / 2 : ℝ) * Real.sqrt (Fintype.card J / Fintype.card I) := by
  simpa only [mul_one_div] using expected_tv_of_second_moment (product P)
    (fun x a => (∑ i, Y i (x i) a) / Fintype.card I - p a)
    (by positivity : 0 ≤ (1 : ℝ) / Fintype.card I)
    (empirical_variance P Y p hY hs hm)

end SmoothObstruction.FiniteLaw

namespace SmoothObstruction.FiniteLaw
open Finset
variable {A : Type*} [Fintype A] [DecidableEq A]

noncomputable def prob (P : Law A) (E : Finset A) : ℝ := ∑ a ∈ E, P.mass a

lemma prob_eq_expect (P : Law A) (E : Finset A) :
    prob P E = expect P (fun a => if a ∈ E then 1 else 0) := by
  simp [prob, expect, mul_ite]

lemma prob_compl (P : Law A) (E : Finset A) : prob P Eᶜ = 1 - prob P E := by
  have h := sum_add_sum_compl E P.mass
  rw [P.total] at h
  simpa [prob] using (eq_sub_iff_add_eq.mpr (by linarith : (∑ a ∈ Eᶜ, P.mass a) + ∑ a ∈ E, P.mass a = 1))

lemma markov (P : Law A) (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) {δ : ℝ} (hδ : 0 < δ) :
    prob P (univ.filter (fun a => δ < f a)) ≤ expect P f / δ := by
  rw [prob_eq_expect, le_div_iff₀ hδ, ← expect_mul_const]
  apply expect_mono
  intro a
  simp only [mem_filter, mem_univ, true_and]
  split_ifs with h
  · simpa using h.le
  · simpa using hf a

lemma union_bound {I : Type*} [Fintype I] (P : Law A) (E : I → Finset A) :
    prob P (univ.biUnion E) ≤ ∑ i, prob P (E i) := by
  simp_rw [prob_eq_expect]
  rw [← expect_sum]
  apply expect_mono
  intro a
  split_ifs with ha
  · obtain ⟨i, _, hi⟩ := mem_biUnion.mp ha
    calc
      (1 : ℝ) = (if a ∈ E i then 1 else 0) := by simp [hi]
      _ ≤ ∑ j, if a ∈ E j then (1 : ℝ) else 0 :=
        single_le_sum (f := fun j => if a ∈ E j then (1 : ℝ) else 0)
          (fun j _ => by positivity) (mem_univ i)
  · exact sum_nonneg (fun j _ => by positivity)

lemma good_event_mass {I : Type*} [Fintype I] (P : Law A) (f : I → A → ℝ)
    (hf : ∀ i a, 0 ≤ f i a) {δ c : ℝ} (hδ : 0 < δ)
    (hb : ∀ i, expect P (f i) ≤ c)
    (hc : (Fintype.card I : ℝ) * c / δ ≤ 1 / 2) :
    1 / 2 ≤ prob P (univ.filter (fun a => ∀ i, f i a ≤ δ)) := by
  classical
  let E : I → Finset A := fun i => univ.filter (fun a => δ < f i a)
  have he : (univ.filter (fun a => ∀ i, f i a ≤ δ)) = (univ.biUnion E)ᶜ := by
    ext a
    simp [E]
  rw [he, prob_compl]
  have hbound : prob P (univ.biUnion E) ≤ 1 / 2 := calc
    _ ≤ ∑ i, prob P (E i) := union_bound P E
    _ ≤ ∑ _ : I, c / δ := sum_le_sum fun i _ =>
      (markov P (f i) (hf i) hδ).trans (div_le_div_of_nonneg_right (hb i) hδ.le)
    _ = Fintype.card I * c / δ := by simp [mul_div_assoc]
    _ ≤ _ := hc
  linarith

lemma exists_good {I : Type*} [Fintype I] (P : Law A) (E : I → Finset A)
    (h : (∑ i, prob P (E i)) < 1) : ∃ a, 0 < P.mass a ∧ ∀ i, a ∉ E i := by
  classical
  have hpos : 0 < prob P (univ.biUnion E)ᶜ := by
    rw [prob_compl]
    have := union_bound P E
    linarith
  obtain ⟨a, ha, hw⟩ := sum_pos_iff_of_nonneg (fun a _ => P.nonneg a) |>.mp
    (show 0 < ∑ a ∈ (univ.biUnion E)ᶜ, P.mass a from hpos)
  exact ⟨a, hw, fun i hi => (mem_compl.mp ha) (mem_biUnion.mpr ⟨i, mem_univ i, hi⟩)⟩

lemma condition_supported (P : Law A) (E : Finset A) (hE : 0 < prob P E) {a : A}
    (ha : 0 < (condition P E hE).mass a) : a ∈ E ∧ 0 < P.mass a := by
  by_cases he : a ∈ E
  · refine ⟨he, ?_⟩
    have hdiv : 0 < P.mass a / prob P E := by simpa [condition, he, prob] using ha
    exact (div_pos_iff_of_pos_right hE).mp hdiv
  · simp [condition, he] at ha

noncomputable def push {C : Type*} [Fintype C] [DecidableEq C]
    (P : Law A) (f : A → C) : Law C where
  mass c := ∑ a, if f a = c then P.mass a else 0
  nonneg c := sum_nonneg (fun a _ => by split_ifs; exact P.nonneg a; exact le_rfl)
  total := by rw [sum_comm]; simpa using P.total

end SmoothObstruction.FiniteLaw

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_Selection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.SelectedTube
open Set MeasureTheory
variable {X C E : Type*} [MeasurableSpace X] [Fintype C]
  [MeasurableSpace C] [MeasurableSingletonClass C]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The literal fixed-atlas coordinate tube, with chart sources checked.
Only the base point chooses the chart; the second point need not be good. -/
def tube (q : X → C) (U : C → Set X) (φ : C → X → E)
    (f : ℕ → X → X) (n : ℕ) (δ : ℝ) (x z : X) : Prop :=
  ∀ t : Fin (n+1),f t z∈U (q (f t x)) ∧
    ‖φ (q (f t x)) (f t z)-φ (q (f t x)) (f t x)‖≤δ

end SmoothObstruction.SelectedTube

namespace SmoothObstruction.MeasurableSwitch
open Set MeasureTheory
variable {X C E : Type*} [MeasurableSpace X] [Fintype C]
  [MeasurableSpace C] [MeasurableSingletonClass C]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Fixed-bin future/past observations and the two old coordinate tubes.
All auxiliary frames have disappeared from this boundary relation. -/
def relation (F P : X → X → E) (TF TB : X → X → Prop) (u : X×X) (z : X) : Prop :=
  F u.1 z=F u.1 u.1 ∧ P u.2 z=P u.2 u.2 ∧ TF u.1 z ∧ TB u.2 z

end SmoothObstruction.MeasurableSwitch

namespace SmoothObstruction.EndpointObservation
open Set MeasureTheory
variable {X C B E : Type*} [MeasurableSpace X]
  [Fintype C] [Fintype B] [MeasurableSpace C] [MeasurableSingletonClass C]
  [MeasurableSpace B] [MeasurableSingletonClass B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The source endpoint observation in the ambient coordinate space. Its
finite index consists ONLY of the starting coarse bin and endpoint coarse
bin; an internal frame witness is not part of this index. -/
def observation (c : X → C) (b : X → B) (f : X → X)
    (φ : B → X → E) (P : C → B → E →L[ℝ] E) (x z : X) : E :=
  P (c x) (b (f x)) (φ (b (f x)) (f z))

end SmoothObstruction.EndpointObservation

namespace SmoothObstruction.ManifoldCoordinates
open Set MeasureTheory
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]

/-- A chart has no prescribed behaviour outside its source. This Borel
extension, used only to state global relations, agrees with it on the source. -/
noncomputable def borelChart (a : M) : M → EuclideanSpace ℝ (Fin d) := by
  classical
  exact (chartAt H a).source.piecewise (extChartAt I a) (fun _ => 0)

variable [MeasurableSpace M] [BorelSpace M]

variable {ι C : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
    (S : Diffeomorph I I M M ∞) (a : ι → M) (c : M → ι) (n : ℕ)

noncomputable def originalObservation (P : M → C)
    (W : C×C → Submodule ℝ (EuclideanSpace ℝ (Fin d))) (x z : M) :=
  (W (P x,P (S^[n] x))).starProjection
    (borelChart I (a (c (S^[n] x))) (S^[n] z))

end SmoothObstruction.ManifoldCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_SwitchScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Filter Topology
open scoped Real

namespace SmoothObstruction.SwitchScales
open Filter Topology
open scoped Real
noncomputable def shortTime (b n : ℝ) : ℕ := ⌈b^(1/4:ℝ)*n⌉₊
noncomputable def root (b : ℝ) : ℝ := b^(1/8:ℝ)
noncomputable def gap (b : ℝ) : ℝ := b^(1/2:ℝ)
noncomputable def shortSignal (b n : ℝ) : ℝ := b^(3/4:ℝ)*n

end SmoothObstruction.SwitchScales

end

section

namespace SmoothObstruction.SwitchScales
open Filter Topology
/-- The finite-time noise is monotone in the literal chart constant. -/
def refNoise (C : ℝ) (N : ℕ) (h : ℝ) : ℝ := (N:ℝ)*C*C^(2*N)*h

noncomputable def refError (K A g : ℝ) (N : ℕ) (noise : ℝ) : ℝ :=
  Real.exp (-2*g*N+4*K)+noise*Real.exp (A*g*N+2*K)

end SmoothObstruction.SwitchScales

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_PartitionEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

namespace SmoothObstruction.PartitionEntropy
open MeasureTheory Set Filter Finset
open SmoothObstruction.FiniteEntropy
open scoped Topology
variable {X α β : Type*} [MeasurableSpace X] [Fintype α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
  (μ : Measure X) [IsProbabilityMeasure μ]

noncomputable def mass (f : X → α) (a : α) : ℝ := μ.real (f ⁻¹' {a})
noncomputable def entropy (f : X → α) : ℝ := natEntropy (mass μ f)

/-- The actual forward partition name, not an independent copy. -/
def name (T : X → X) (P : X → α) (n : ℕ) (x : X) : Fin n → α :=
  fun j => P ((T^[j.val]) x)

end SmoothObstruction.PartitionEntropy

namespace SmoothObstruction.PartitionEntropy
open MeasureTheory Set Filter Finset
open SmoothObstruction.FiniteEntropy
open scoped Topology
variable {X α : Type*} [MeasurableSpace X] [Fintype α] [MeasurableSpace α]
  [MeasurableSingletonClass α] (μ : Measure X) [IsProbabilityMeasure μ]

local instance instMeasurableSpaceOption_solutions : MeasurableSpace (Option α) := ⊤

noncomputable def errorCode (P Q : X → α) (x : X) : Option α := by
  classical
  exact if P x = Q x then none else some (P x)

def recover (q : α) : Option α → α
  | none => q
  | some a => a

end SmoothObstruction.PartitionEntropy

namespace SmoothObstruction.PartitionEntropy
open MeasureTheory Set Filter Finset
open SmoothObstruction.FiniteEntropy
open scoped Topology
variable {X α : Type*} [MeasurableSpace X] [Fintype α] [MeasurableSpace α]
  [MeasurableSingletonClass α] (μ : Measure X) [IsProbabilityMeasure μ]

local instance instMeasurableSpaceOption_solutions_1 : MeasurableSpace (Option α) := ⊤

end SmoothObstruction.PartitionEntropy

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_PhaseEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset
open MeasureTheory Set MeasurableSpace
open scoped ENNReal symmDiff

namespace SmoothObstruction.CylinderApproximation

variable {X ι : Type*} {A : ι → Type*} [MeasurableSpace X]
  [∀ i, MeasurableSpace (A i)] (π : X → ∀ i, A i)

/-- Cylinders pulled back along the actual coordinate map. -/
def cylinders : Set (Set X) := Set.preimage π '' measurableCylinders A

end SmoothObstruction.CylinderApproximation

namespace SmoothObstruction.PhaseEntropy
open MeasureTheory Set Filter Finset
open SmoothObstruction.PartitionEntropy
open scoped Topology

variable (A : Type) (m : ℕ → ℕ)
def Coordinate : ℤ ⊕ ℕ → Type
  | Sum.inl _ => A
  | Sum.inr i => ZMod (m i)
instance instFintypeCoordinateOfNeZeroNat [Fintype A] [∀ i, NeZero (m i)] (i : ℤ ⊕ ℕ) : Fintype (Coordinate A m i) := by
  cases i <;> dsimp [Coordinate] <;> infer_instance
instance instNonemptyCoordinate [Nonempty A] (i : ℤ ⊕ ℕ) : Nonempty (Coordinate A m i) := by
  cases i <;> dsimp [Coordinate] <;> infer_instance
instance instMeasurableSpaceCoordinate [MeasurableSpace A] (i : ℤ ⊕ ℕ) : MeasurableSpace (Coordinate A m i) := by
  cases i <;> dsimp [Coordinate] <;> infer_instance
instance instMeasurableSingletonClassCoordinate [MeasurableSpace A] [MeasurableSingletonClass A] (i : ℤ ⊕ ℕ) :
    MeasurableSingletonClass (Coordinate A m i) := by
  cases i <;> dsimp [Coordinate] <;> infer_instance

variable {A m} {X : Type*} [MeasurableSpace X]
  [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [∀ i, NeZero (m i)]
  (s : X → ℤ → A) (p : X → ∀ i, ZMod (m i))

def coordinates (x : X) : ∀ i, Coordinate A m i
  | Sum.inl t => s x t
  | Sum.inr i => p x i

end SmoothObstruction.PhaseEntropy

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_StandardProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set ENNReal unitInterval Filter Topology Function

namespace SmoothObstruction

/- The quantile construction gives a measurable map from the unit interval
with the prescribed probability law. Injectivity yields a measurable
isomorphism on conull subsets for nonatomic laws. -/

noncomputable def unitQuantile (μ : Measure I) (t : I) : I :=
  sSup {x | μ.real (Icc 0 x) < t}

def setEqEquiv {Z : Type*} [MeasurableSpace Z] {A B : Set Z} (h : A = B) :
    A ≃ᵐ B := by
  subst B
  exact MeasurableEquiv.refl A

end SmoothObstruction

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_PhaseDynamics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Set Filter Topology

namespace SmoothObstruction.PhaseDynamics

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

section Ambient
variable (A : Type*) [TopologicalSpace A] (m : ℕ → ℕ)

abbrev Space := (ℤ → A) × ∀ i, ZMod (m i)

/-- The source map: bilateral symbol shift and addition of one in every
phase. Its inverse subtracts one, with no modulo-null restriction. -/
def shift : Space A m ≃ₜ Space A m where
  toFun x := (fun t => x.1 (t + 1), fun i => x.2 i + 1)
  invFun x := (fun t => x.1 (t - 1), fun i => x.2 i - 1)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  continuous_toFun := by
    apply Continuous.prodMk
    · exact continuous_pi (fun t => (continuous_apply (t + 1)).comp continuous_fst)
    · exact continuous_pi (fun i => ((continuous_apply i).comp continuous_snd).add continuous_const)
  continuous_invFun := by
    apply Continuous.prodMk
    · exact continuous_pi (fun t => (continuous_apply (t - 1)).comp continuous_fst)
    · exact continuous_pi (fun i => ((continuous_apply i).comp continuous_snd).sub continuous_const)

@[simp] lemma shift_symbol (x : Space A m) (t : ℤ) : (shift A m x).1 t = x.1 (t + 1) := rfl
@[simp] lemma shift_phase (x : Space A m) (i : ℕ) : (shift A m x).2 i = x.2 i + 1 := rfl

end Ambient

section Words
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
  (m : ℕ → ℕ) (hm : ∀ i, m i ∣ m (i + 1))
  (W : ∀ i, Set (Fin (m i) → A))

/-- Level-i symbols beginning at an integer time. -/
def wordAt (x : Space A m) (i : ℕ) (t : ℤ) : Fin (m i) → A :=
  fun j => x.1 (t + j.val)

/-- Exact compatibility of phases through the canonical cyclic quotient. -/
def Compatible (x : Space A m) (i : ℕ) : Prop :=
  ZMod.castHom (hm i) (ZMod (m i)) (x.2 (i + 1)) = x.2 i

/-- Every level boundary carries a legal word; the sign convention records
the index of the origin inside its word, exactly as in source section 6. -/
def Legal (x : Space A m) (i : ℕ) : Prop :=
  ∀ t : ℤ, (t : ZMod (m i)) = -x.2 i → wordAt m x i t ∈ W i

def extension : Set (Space A m) :=
  {x | ∀ i, Compatible m hm x i ∧ Legal m W x i}

omit [DiscreteTopology A] in
lemma compatible_shift_iff (x : Space A m) (i : ℕ) :
    Compatible m hm (shift A m x) i ↔ Compatible m hm x i := by
  simp [Compatible, shift, map_add, map_one]

omit [DiscreteTopology A] in
lemma legal_shift_iff (x : Space A m) (i : ℕ) :
    Legal m W (shift A m x) i ↔ Legal m W x i := by
  constructor
  · intro h t ht
    have hb : ((t - 1 : ℤ) : ZMod (m i)) = -(shift A m x).2 i := by
      simp only [Int.cast_sub, Int.cast_one, shift_phase]
      rw [ht]
      ring
    have hw := h (t - 1) hb
    convert hw using 1
    all_goals try with_reducible_and_instances rfl
    ext j
    change x.1 (t + (j.val : ℤ)) = x.1 (t - 1 + (j.val : ℤ) + 1)
    exact congrArg x.1 (by ring)
  · intro h t ht
    have hb : ((t + 1 : ℤ) : ZMod (m i)) = -x.2 i := by
      simp only [Int.cast_add, Int.cast_one]
      rw [ht, shift_phase]
      ring
    have hw := h (t + 1) hb
    convert hw using 1
    all_goals try with_reducible_and_instances rfl
    ext j
    change x.1 (t + (j.val : ℤ) + 1) = x.1 (t + 1 + (j.val : ℤ))
    exact congrArg x.1 (by ring)

omit [DiscreteTopology A] in
lemma extension_shift_iff (x : Space A m) :
    shift A m x ∈ extension m hm W ↔ x ∈ extension m hm W := by
  simp only [extension, mem_ofPred_eq, compatible_shift_iff, legal_shift_iff]

omit [DiscreteTopology A] in
lemma extension_shift_symm (x : Space A m) (hx : x ∈ extension m hm W) :
    (shift A m).symm x ∈ extension m hm W := by
  apply (extension_shift_iff m hm W ((shift A m).symm x)).mp
  simpa using hx

/-- Restriction to the genuine closed phase extension, in both directions. -/
def extensionShift : extension m hm W ≃ₜ extension m hm W where
  toFun x := ⟨shift A m x.val, (extension_shift_iff m hm W x.val).mpr x.property⟩
  invFun x := ⟨(shift A m).symm x.val, extension_shift_symm m hm W x.val x.property⟩
  left_inv x := Subtype.ext ((shift A m).left_inv x.val)
  right_inv x := Subtype.ext ((shift A m).right_inv x.val)
  continuous_toFun := ((shift A m).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((shift A m).symm.continuous.comp continuous_subtype_val).subtype_mk _

end Words
end SmoothObstruction.PhaseDynamics

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_Sampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

namespace SmoothObstruction.SymplecticSampling

lemma bit_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  exact h a

lemma bit_one {a : ZMod 2} (h : a ≠ 0) : a = 1 := (bit_cases a).resolve_left h

lemma bit_neg (a : ZMod 2) : -a = a := by
  rcases bit_cases a with rfl | rfl <;> decide

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

lemma add_self (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 by decide, zero_smul]

lemma alt_symm {B : LinearMap.BilinForm (ZMod 2) V} (hB : B.IsAlt) (x y : V) :
    B x y = B y x := by
  rw [← hB.neg_eq x y, bit_neg]

lemma transvection_preserves {B : LinearMap.BilinForm (ZMod 2) V}
    (hB : B.IsAlt) (v x y : V) :
    B (LinearEquiv.transvection (hB v) x) (LinearEquiv.transvection (hB v) y) = B x y := by
  simp only [LinearEquiv.transvection.apply, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, hB v, mul_zero, add_zero]
  rw [← alt_symm hB x v]
  rcases bit_cases (B v x) with hx | hx <;>
    rcases bit_cases (B v y) with hy | hy <;>
    simp [hx, hy, alt_symm hB x v, add_assoc,
      show (1 : ZMod 2) + 1 = 0 by decide]

lemma transvection_moves {B : LinearMap.BilinForm (ZMod 2) V} (hB : B.IsAlt)
    {v w : V} (hvw : B v w = 1) :
    LinearEquiv.transvection (hB (v + w)) v = w := by
  rw [LinearEquiv.transvection.apply, map_add, LinearMap.add_apply, hB v,
    alt_symm hB w v, hvw, zero_add, one_smul, ← add_assoc, add_self, zero_add]

lemma exists_pairing_one {B : LinearMap.BilinForm (ZMod 2) V}
    (hB : B.Nondegenerate) {v : V} (hv : v ≠ 0) : ∃ w, B v w = 1 := by
  have h : ¬ ∀ w, B v w = 0 := fun h => hv (hB.1 v h)
  obtain ⟨w, hw⟩ := not_forall.mp h
  exact ⟨w, bit_one hw⟩

lemma common_pairing_one {B : LinearMap.BilinForm (ZMod 2) V}
    (hB : B.Nondegenerate) {v w : V} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ z, B v z = 1 ∧ B w z = 1 := by
  obtain ⟨a, ha⟩ := exists_pairing_one hB hv
  obtain ⟨b, hb⟩ := exists_pairing_one hB hw
  rcases bit_cases (B w a) with hwa | hwa
  · rcases bit_cases (B v b) with hvb | hvb
    · exact ⟨a + b, by simp [ha, hvb], by simp [hwa, hb]⟩
    · exact ⟨b, hvb, hb⟩
  · exact ⟨a, ha, hwa⟩

/-- Explicit symplectic transitivity in characteristic two, using at most two
transvections. This proves the uniform one-label marginal input to the actual
sequential word sampling, without assuming a symplectic-basis theorem. -/
theorem symplectic_transitive {B : LinearMap.BilinForm (ZMod 2) V}
    (hB : B.IsAlt) (hnd : B.Nondegenerate) {v w : V} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ e : V ≃ₗ[ZMod 2] V, e v = w ∧ ∀ x y, B (e x) (e y) = B x y := by
  obtain ⟨z, hvz, hwz⟩ := common_pairing_one hnd hv hw
  let e₁ := LinearEquiv.transvection (hB (v + z))
  let e₂ := LinearEquiv.transvection (hB (z + w))
  refine ⟨e₁.trans e₂, ?_, ?_⟩
  · change e₂ (e₁ v) = w
    rw [show e₁ v = z from transvection_moves hB hvz]
    exact transvection_moves hB ((alt_symm hB z w).trans hwz)
  · intro x y
    exact (transvection_preserves hB (z + w) (e₁ x) (e₁ y)).trans
      (transvection_preserves hB (v + z) x y)

section Cardinality
variable [Fintype V] [DecidableEq V]
noncomputable local instance instFintypeSubtypeMemSubmoduleZModOfNatNatKerForallFin_solutions {k : ℕ} (f : V →ₗ[ZMod 2] (Fin k → ZMod 2)) :
    Fintype f.ker := Fintype.ofFinite _

noncomputable def nonzeroKerEquiv {k : ℕ} (f : V →ₗ[ZMod 2] (Fin k → ZMod 2)) :
    {u : f.ker // u ≠ 0} ≃ {v : V // v ≠ 0 ∧ f v = 0} where
  toFun u := ⟨u.val.val, by
    constructor
    · intro h
      exact u.property (Subtype.ext h)
    · exact u.val.property⟩
  invFun v := ⟨⟨v.val, v.property.2⟩, by
    intro h
    exact v.property.1 (congrArg Subtype.val h)⟩
  left_inv u := rfl
  right_inv v := rfl

lemma card_nonzero_ker {k : ℕ} (f : V →ₗ[ZMod 2] (Fin k → ZMod 2)) :
    Fintype.card f.ker = Fintype.card {v : V // v ≠ 0 ∧ f v = 0} + 1 := by
  have h := Fintype.card_congr (Equiv.optionSubtypeNe (0 : f.ker))
  rw [Fintype.card_option, Fintype.card_congr (nonzeroKerEquiv f)] at h
  exact h.symm

/-- At most k linear equations remove at most k binary dimensions, even when
they are dependent. The zero vector is then removed exactly once. -/
theorem common_kernel_lower {k : ℕ} (f : V →ₗ[ZMod 2] (Fin k → ZMod 2)) :
    2 ^ (Module.finrank (ZMod 2) V - k) ≤
      Fintype.card {v : V // v ≠ 0 ∧ f v = 0} + 1 := by
  have hr := f.finrank_range_add_finrank_ker
  have hk : Module.finrank (ZMod 2) f.range ≤ k := by
    simpa using (Submodule.finrank_le f.range)
  have hdim : Module.finrank (ZMod 2) V - k ≤ Module.finrank (ZMod 2) f.ker := by omega
  calc
    _ ≤ 2 ^ Module.finrank (ZMod 2) f.ker := Nat.pow_le_pow_right (by decide) hdim
    _ = Fintype.card f.ker := by rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
    _ = _ := card_nonzero_ker f

/-- The quantitative bound actually used in source (word-choices), with the
original nonzero alphabet and dependent equations allowed. -/
theorem common_kernel_choices {k : ℕ} (f : V →ₗ[ZMod 2] (Fin k → ZMod 2))
    (hk : 1 ≤ k) (hd : k + 1 ≤ Module.finrank (ZMod 2) V) :
    Fintype.card {v : V // v ≠ 0} ≤
      2 ^ (2 * k) * Fintype.card {v : V // v ≠ 0 ∧ f v = 0} := by
  let d := Module.finrank (ZMod 2) V
  let c := Fintype.card {v : V // v ≠ 0 ∧ f v = 0}
  have hlo : 2 ^ (d - k) ≤ c + 1 := common_kernel_lower f
  have hexp : d - k = (d - k - 1) + 1 := by dsimp [d]; omega
  have hpow : 2 ^ (d - k - 1) ≤ c := by
    rw [hexp, pow_succ] at hlo
    have hn : 1 ≤ 2 ^ (d - k - 1) := Nat.one_le_pow _ _ (by decide)
    omega
  have hdim : d ≤ 2 * k + (d - k - 1) := by dsimp [d]; omega
  have hfull : Fintype.card V ≤ 2 ^ (2 * k) * c := calc
    _ = 2 ^ d := by rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
    _ ≤ 2 ^ (2 * k + (d - k - 1)) := Nat.pow_le_pow_right (by decide) hdim
    _ = 2 ^ (2 * k) * 2 ^ (d - k - 1) := pow_add _ _ _
    _ ≤ _ := Nat.mul_le_mul_left _ hpow
  exact (Fintype.card_subtype_le _).trans hfull

variable (B : LinearMap.BilinForm (ZMod 2) V)

/-- The exact nonzero choices, not an independent-equations approximation. -/
noncomputable def allowed {k : ℕ} (u : Fin k → V) : Finset {v : V // v ≠ 0} :=
  univ.filter (fun v => ∀ j, B (u j) v.val = 0)

noncomputable def equationMap {k : ℕ} (u : Fin k → V) : V →ₗ[ZMod 2] (Fin k → ZMod 2) :=
  LinearMap.pi (fun j => B (u j))

lemma mem_allowed {k : ℕ} (u : Fin k → V) (v : {v : V // v ≠ 0}) :
    v ∈ allowed B u ↔ ∀ j, B (u j) v.val = 0 := by
  classical
  simp [allowed]

lemma allowed_card {k : ℕ} (u : Fin k → V) :
    (allowed B u).card = Fintype.card {v : V // v ≠ 0 ∧ equationMap B u v = 0} := by
  classical
  let e : {v // v ∈ allowed B u} ≃ {v : V // v ≠ 0 ∧ equationMap B u v = 0} :=
    { toFun := fun v => ⟨v.val.val, v.val.property, by
        ext j
        exact (mem_allowed B u v.val).mp v.property j⟩
      invFun := fun v => ⟨⟨v.val, v.property.1⟩, (mem_allowed B u _).mpr (fun j =>
        congrFun v.property.2 j)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Fintype.card_coe _).symm.trans (Fintype.card_congr e)

lemma allowed_nonempty {k : ℕ} (u : Fin k → V)
    (hd : k + 1 ≤ Module.finrank (ZMod 2) V) : (allowed B u).Nonempty := by
  have h := common_kernel_lower (equationMap B u)
  rw [← allowed_card B u] at h
  have hpow : 2 ≤ 2 ^ (Module.finrank (ZMod 2) V - k) := by
    simpa using Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤
      Module.finrank (ZMod 2) V - k by omega)
  exact card_pos.mp (by omega)

/-- Uniform sampling among all allowed nonzero labels. -/
noncomputable def kernel {k : ℕ} (u : Fin k → V) (v : {v : V // v ≠ 0}) : ℝ :=
  if v ∈ allowed B u then ((allowed B u).card : ℝ)⁻¹ else 0

lemma kernel_nonneg {k : ℕ} (u : Fin k → V) (v : {v : V // v ≠ 0}) :
    0 ≤ kernel B u v := by
  unfold kernel
  split_ifs <;> positivity

lemma kernel_sum {k : ℕ} (u : Fin k → V)
    (hd : k + 1 ≤ Module.finrank (ZMod 2) V) : ∑ v, kernel B u v = 1 := by
  classical
  have hc : ((allowed B u).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Finset.card_ne_zero.mpr (allowed_nonempty B u hd))
  simp only [kernel, sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
  exact mul_inv_cancel₀ hc

lemma kernel_upper {k : ℕ} (u : Fin k → V) (v : {v : V // v ≠ 0})
    (hk : 1 ≤ k) (hd : k + 1 ≤ Module.finrank (ZMod 2) V) :
    kernel B u v ≤ (2 : ℝ) ^ (2 * k) / Fintype.card {v : V // v ≠ 0} := by
  have hN : 0 < (Fintype.card {v : V // v ≠ 0} : ℝ) := by
    have : Nonempty {v : V // v ≠ 0} := (allowed_nonempty B u hd).nonempty
    exact_mod_cast Fintype.card_pos
  have hc : 0 < ((allowed B u).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (allowed_nonempty B u hd)
  have hb : (Fintype.card {v : V // v ≠ 0} : ℝ) ≤
      (2 : ℝ) ^ (2 * k) * (allowed B u).card := by
    have h := common_kernel_choices (equationMap B u) hk hd
    rw [← allowed_card B u] at h
    exact_mod_cast h
  unfold kernel
  split_ifs
  · apply (le_div_iff₀ hN).mpr
    apply (inv_mul_le_iff₀ hc).mpr
    simpa only [mul_comm] using hb
  · positivity

noncomputable def nonzeroEquiv (e : V ≃ₗ[ZMod 2] V) :
    {v : V // v ≠ 0} ≃ {v : V // v ≠ 0} where
  toFun v := ⟨e v.val, fun h => v.property (e.injective (h.trans e.map_zero.symm))⟩
  invFun v := ⟨e.symm v.val, fun h => v.property (e.symm.injective (h.trans e.symm.map_zero.symm))⟩
  left_inv v := Subtype.ext (e.symm_apply_apply v.val)
  right_inv v := Subtype.ext (e.apply_symm_apply v.val)

lemma allowed_equivariant {k : ℕ} (u : Fin k → V) (e : V ≃ₗ[ZMod 2] V)
    (he : ∀ x y, B (e x) (e y) = B x y) (v : {v : V // v ≠ 0}) :
    nonzeroEquiv e v ∈ allowed B (e ∘ u) ↔ v ∈ allowed B u := by
  simp only [mem_allowed, nonzeroEquiv, Equiv.coe_fn_mk, Function.comp_apply, he]

lemma allowed_card_equivariant {k : ℕ} (u : Fin k → V) (e : V ≃ₗ[ZMod 2] V)
    (he : ∀ x y, B (e x) (e y) = B x y) :
    (allowed B (e ∘ u)).card = (allowed B u).card := by
  classical
  have h := Fintype.card_congr ((nonzeroEquiv e).subtypeEquiv
    (fun v => (allowed_equivariant B u e he v).symm))
  simpa only [Fintype.card_coe] using h.symm

lemma kernel_equivariant {k : ℕ} (u : Fin k → V) (e : V ≃ₗ[ZMod 2] V)
    (he : ∀ x y, B (e x) (e y) = B x y) (v : {v : V // v ≠ 0}) :
    kernel B (e ∘ u) (nonzeroEquiv e v) = kernel B u v := by
  simp only [kernel, allowed_equivariant B u e he, allowed_card_equivariant B u e he]

end Cardinality

end SmoothObstruction.SymplecticSampling

namespace SmoothObstruction.SequentialLaw

variable {A : Type*}

/-- A finite left-to-right sampling law. The kernel at time k may depend on
all k preceding labels; no independence inside a group is assumed. -/
def weight (K : (k : ℕ) → (Fin k → A) → A → ℝ) : (n : ℕ) → (Fin n → A) → ℝ
  | 0, _ => 1
  | n + 1, w => weight K n (Fin.init w) * K n (Fin.init w) (w (Fin.last n))

@[simp] lemma weight_zero (K : (k : ℕ) → (Fin k → A) → A → ℝ) (w : Fin 0 → A) :
    weight K 0 w = 1 := rfl

@[simp] lemma weight_snoc (K : (k : ℕ) → (Fin k → A) → A → ℝ)
    {n : ℕ} (w : Fin n → A) (a : A) :
    weight K (n + 1) (Fin.snoc w a) = weight K n w * K n w a := by
  simp [weight]

lemma weight_nonneg {K : (k : ℕ) → (Fin k → A) → A → ℝ}
    (hK : ∀ k w a, 0 ≤ K k w a) : ∀ n w, 0 ≤ weight K n w
  | 0, _ => by simp
  | n + 1, w => mul_nonneg (weight_nonneg hK n _) (hK n _ _)

variable [Fintype A]

omit [Fintype A] in
lemma snoc_equiv_apply {n : ℕ} (p : A × (Fin n → A)) :
    (Fin.snocEquiv (fun _ : Fin (n + 1) => A)) p = Fin.snoc p.2 p.1 := rfl

lemma sum_weight {K : (k : ℕ) → (Fin k → A) → A → ℝ}
    (hK : ∀ k w, ∑ a, K k w a = 1) : ∀ n, ∑ w, weight K n w = 1 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => A)).sum_comp]
    simp only [snoc_equiv_apply, weight_snoc, Fintype.sum_prod_type]
    rw [sum_comm]
    simp only [← mul_sum, hK, mul_one]
    exact ih

variable [DecidableEq A]

def mark (m : Option A) (a : A) : ℝ :=
  match m with
  | none => 1
  | some b => if a = b then 1 else 0

def test {n : ℕ} (m : Fin n → Option A) (w : Fin n → A) : ℝ :=
  ∏ i, mark (m i) (w i)

omit [Fintype A] in
lemma mark_nonneg (m : Option A) (a : A) : 0 ≤ mark m a := by
  cases m with
  | none => norm_num [mark]
  | some b => change 0 ≤ (if _ = b then (1 : ℝ) else 0); split_ifs <;> norm_num

omit [Fintype A] in
lemma test_nonneg {n : ℕ} (m : Fin n → Option A) (w : Fin n → A) : 0 ≤ test m w :=
  prod_nonneg (fun i _ => mark_nonneg (m i) (w i))

omit [Fintype A] in
@[simp] lemma test_snoc {n : ℕ} (m : Fin (n + 1) → Option A) (w : Fin n → A) (a : A) :
    test m (Fin.snoc w a) = test (Fin.init m) w * mark (m (Fin.last n)) a := by
  unfold test
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rfl

lemma sum_test_succ (K : (k : ℕ) → (Fin k → A) → A → ℝ)
    {n : ℕ} (m : Fin (n + 1) → Option A) :
    (∑ w, weight K (n + 1) w * test m w) =
      ∑ w, (weight K n w * test (Fin.init m) w) *
        (∑ a, K n w a * mark (m (Fin.last n)) a) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => A)).sum_comp]
  simp only [snoc_equiv_apply, weight_snoc, test_snoc, Fintype.sum_prod_type]
  rw [sum_comm]
  apply sum_congr rfl
  intro w _
  rw [mul_sum]
  apply sum_congr rfl
  intro a _
  ring

/-- Any list of specified coordinates has probability at most the product
of the pointwise conditional upper bounds. Unspecified labels are integrated
out, exactly as in (word-raw-sublist). -/
theorem cylinder_bound {K : (k : ℕ) → (Fin k → A) → A → ℝ} {ζ : ℝ}
    (h0 : ∀ k w a, 0 ≤ K k w a) (h1 : ∀ k w, ∑ a, K k w a = 1)
    (hζ : 0 ≤ ζ) (hK : ∀ k w a, K k w a ≤ ζ) :
    ∀ n (m : Fin n → Option A), (∑ w, weight K n w * test m w) ≤
      ∏ i, (if (m i).isSome then ζ else 1) := by
  intro n
  induction n with
  | zero => intro m; simp [test]
  | succ n ih =>
    intro m
    rw [sum_test_succ, Fin.prod_univ_castSucc]
    have hstep (w : Fin n → A) : (∑ a, K n w a * mark (m (Fin.last n)) a) ≤
        if (m (Fin.last n)).isSome then ζ else 1 := by
      cases hm : m (Fin.last n) with
      | none => simp [mark, h1]
      | some a => simpa [mark] using hK n w a
    calc
      _ ≤ ∑ w, (weight K n w * test (Fin.init m) w) *
          (if (m (Fin.last n)).isSome then ζ else 1) :=
        sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left (hstep w)
          (mul_nonneg (weight_nonneg h0 n w) (test_nonneg _ _)))
      _ = (∑ w, weight K n w * test (Fin.init m) w) *
          (if (m (Fin.last n)).isSome then ζ else 1) := by rw [sum_mul]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right (ih (Fin.init m))
        split_ifs <;> positivity

omit [Fintype A] [DecidableEq A] in
lemma weight_equivariant (K : (k : ℕ) → (Fin k → A) → A → ℝ) (e : A ≃ A)
    (hK : ∀ k w a, K k (e ∘ w) (e a) = K k w a) :
    ∀ n w, weight K n (e ∘ w) = weight K n w := by
  intro n
  induction n with
  | zero => intro w; rfl
  | succ n ih =>
    intro w
    simp only [weight]
    have hi : Fin.init (e ∘ w) = e ∘ Fin.init w := rfl
    rw [hi, ih, Function.comp_apply, hK]

lemma test_eq_indicator {n : ℕ} (m : Fin n → Option A) (w : Fin n → A) :
    test m w = if ∀ i a, m i = some a → w i = a then 1 else 0 := by
  classical
  have hm (i : Fin n) : mark (m i) (w i) =
      if ∀ a, m i = some a → w i = a then 1 else 0 := by
    cases h : m i <;> simp [mark]
  simp only [test, hm, Finset.prod_boole, Finset.mem_univ, forall_const]

lemma test_upper_pow {K : (k : ℕ) → (Fin k → A) → A → ℝ} {ζ : ℝ}
    (h0 : ∀ k w a, 0 ≤ K k w a) (h1 : ∀ k w, ∑ a, K k w a = 1)
    (hζ : 0 ≤ ζ) (hK : ∀ k w a, K k w a ≤ ζ)
    (n : ℕ) (m : Fin n → Option A) :
    (∑ w, weight K n w * test m w) ≤
      ζ ^ (univ.filter (fun i => (m i).isSome)).card := by
  simpa only [Finset.prod_ite, Finset.prod_const, one_pow, mul_one]
    using cylinder_bound h0 h1 hζ hK n m

/-- The unconditioned one-coordinate law; the complete path is summed out. -/
def marginal (K : (k : ℕ) → (Fin k → A) → A → ℝ) {n : ℕ} (i : Fin n) (a : A) : ℝ :=
  ∑ w, if w i = a then weight K n w else 0

lemma sum_marginal {K : (k : ℕ) → (Fin k → A) → A → ℝ}
    (hK : ∀ k w, ∑ a, K k w a = 1) {n : ℕ} (i : Fin n) :
    ∑ a, marginal K i a = 1 := by
  unfold marginal
  rw [sum_comm]
  simp only [sum_ite_eq, mem_univ, ite_true]
  exact sum_weight hK n

lemma marginal_equivariant (K : (k : ℕ) → (Fin k → A) → A → ℝ) (e : A ≃ A)
    (hK : ∀ k w a, K k (e ∘ w) (e a) = K k w a) {n : ℕ} (i : Fin n) (a : A) :
    marginal K i (e a) = marginal K i a := by
  unfold marginal
  let E : (Fin n → A) ≃ (Fin n → A) := Equiv.piCongrRight (fun _ => e)
  rw [← E.sum_comp]
  apply sum_congr rfl
  intro w _
  change (if e (w i) = e a then weight K n (e ∘ w) else 0) = _
  simp only [e.injective.eq_iff, weight_equivariant K e hK]

/-- Equivariance under a transitive collection of label permutations gives
exactly uniform marginals, despite arbitrary dependencies between positions. -/
theorem uniform_marginal [Nonempty A]
    {K : (k : ℕ) → (Fin k → A) → A → ℝ}
    (h1 : ∀ k w, ∑ a, K k w a = 1)
    (htrans : ∀ a b : A, ∃ e : A ≃ A, e a = b ∧
      ∀ k w x, K k (e ∘ w) (e x) = K k w x)
    {n : ℕ} (i : Fin n) (a : A) : marginal K i a = 1 / Fintype.card A := by
  have heq (b : A) : marginal K i b = marginal K i a := by
    obtain ⟨e, hab, he⟩ := htrans a b
    rw [← hab]
    exact marginal_equivariant K e he i a
  have hsum := sum_marginal h1 i
  simp_rw [heq] at hsum
  simp only [sum_const, card_univ, nsmul_eq_mul] at hsum
  have hc : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact (eq_div_iff hc).mpr (by simpa only [mul_comm] using hsum)

end SmoothObstruction.SequentialLaw

namespace SmoothObstruction.GroupSampler
open Finset SymplecticSampling SequentialLaw

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [Fintype V] [DecidableEq V]
variable (B : LinearMap.BilinForm (ZMod 2) V) {K : ℕ}

/-- At time t, at most K earlier positions are constrained. None represents
an absent constraint, whose equation is identically zero. -/
def previous (back : (t : ℕ) → Fin K → Option (Fin t))
    (t : ℕ) (w : Fin t → {v : V // v ≠ 0}) (j : Fin K) : V :=
  (back t j).elim 0 (fun r => (w r).val)

noncomputable def step (back : (t : ℕ) → Fin K → Option (Fin t))
    (t : ℕ) (w : Fin t → {v : V // v ≠ 0}) (a : {v : V // v ≠ 0}) : ℝ :=
  kernel B (previous back t w) a

lemma step_sum (back : (t : ℕ) → Fin K → Option (Fin t))
    (hd : K + 1 ≤ Module.finrank (ZMod 2) V) (t : ℕ) (w : Fin t → {v : V // v ≠ 0}) :
    ∑ a, step B back t w a = 1 := kernel_sum B _ hd

omit [Fintype V] [DecidableEq V] in
lemma previous_equivariant (back : (t : ℕ) → Fin K → Option (Fin t))
    (e : V ≃ₗ[ZMod 2] V) (t : ℕ) (w : Fin t → {v : V // v ≠ 0}) :
    previous back t (nonzeroEquiv e ∘ w) = e ∘ previous back t w := by
  funext j
  cases h : back t j <;> simp [previous, h, nonzeroEquiv]

lemma step_equivariant (back : (t : ℕ) → Fin K → Option (Fin t))
    (e : V ≃ₗ[ZMod 2] V) (he : ∀ x y, B (e x) (e y) = B x y)
    (t : ℕ) (w : Fin t → {v : V // v ≠ 0}) (a : {v : V // v ≠ 0}) :
    step B back t (nonzeroEquiv e ∘ w) (nonzeroEquiv e a) = step B back t w a := by
  unfold step
  rw [previous_equivariant, kernel_equivariant B _ e he]

/-- The actual sequential sampling has exactly uniform one-position laws.
This is not a product law inside a group. -/
theorem uniform_position (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (back : (t : ℕ) → Fin K → Option (Fin t))
    (hd : K + 1 ≤ Module.finrank (ZMod 2) V)
    {n : ℕ} (i : Fin n) (a : {v : V // v ≠ 0}) :
    marginal (step B back) i a = 1 / Fintype.card {v : V // v ≠ 0} := by
  let : Nonempty {v : V // v ≠ 0} := ⟨a⟩
  apply uniform_marginal (step_sum B back hd)
  intro v w
  obtain ⟨e, he, hpres⟩ := symplectic_transitive hB hnd v.property w.property
  exact ⟨nonzeroEquiv e, Subtype.ext he, step_equivariant B back e hpres⟩

/-- All sublist probabilities have the source bound, even though prior
constraints can be linearly dependent and unobserved labels are integrated out. -/
theorem raw_sublist (back : (t : ℕ) → Fin K → Option (Fin t))
    (hK : 1 ≤ K) (hd : K + 1 ≤ Module.finrank (ZMod 2) V)
    (n : ℕ) (m : Fin n → Option {v : V // v ≠ 0}) :
    (∑ w, weight (step B back) n w * test m w) ≤
      ((2 : ℝ) ^ (2 * K) / Fintype.card {v : V // v ≠ 0}) ^
        (univ.filter (fun i => (m i).isSome)).card := by
  apply test_upper_pow
  · intro t w a; exact kernel_nonneg B _ _
  · exact step_sum B back hd
  · positivity
  · intro t w a; exact kernel_upper B _ _ hK hd

lemma step_positive_constraint (back : (t : ℕ) → Fin K → Option (Fin t))
    (t : ℕ) (w : Fin t → {v : V // v ≠ 0}) (a : {v : V // v ≠ 0})
    (h : 0 < step B back t w a) {j : Fin K} {r : Fin t} (hr : back t j = some r) :
    B (w r).val a.val = 0 := by
  have hm : a ∈ allowed B (previous back t w) := by
    by_contra hc
    simp [step, kernel, hc] at h
  have he := (mem_allowed B _ _).mp hm j
  simpa [previous, hr] using he

/-- Positively weighted paths satisfy every prescribed relation. -/
theorem supported_constraints (back : (t : ℕ) → Fin K → Option (Fin t)) :
    ∀ n (w : Fin n → {v : V // v ≠ 0}), 0 < weight (step B back) n w →
      ∀ (t : Fin n) (j : Fin K) (r : Fin t.val), back t.val j = some r →
        B (w ⟨r.val, lt_trans r.isLt t.isLt⟩).val (w t).val = 0 := by
  intro n
  induction n with
  | zero => intro w h t; exact Fin.elim0 t
  | succ n ih =>
    intro w hw t j r hr
    have hp : 0 < weight (step B back) n (Fin.init w) ∧
        0 < step B back n (Fin.init w) (w (Fin.last n)) := by
      rcases mul_pos_iff.mp hw with h | h
      · exact h
      · exact False.elim ((not_lt_of_ge (kernel_nonneg B _ _)) h.2)
    by_cases ht : t.val < n
    · exact ih (Fin.init w) hp.1 ⟨t.val, ht⟩ j r hr
    · have teq : t = Fin.last n := Fin.ext (by simp; omega)
      subst t
      exact step_positive_constraint B back n (Fin.init w) (w (Fin.last n)) hp.2 hr

end SmoothObstruction.GroupSampler

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_WordLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

namespace SmoothObstruction.WordLaw
open Finset FiniteLaw GroupSampler SequentialLaw SymplecticSampling

/-- The literal dyadic predecessor schedule of W1, padded by absent equations
up to K slots. Groups restart this schedule at zero. -/
def lagBack (K t : ℕ) (j : Fin K) : Option (Fin t) :=
  if h : j.val ≤ K / 8 ∧ 2 ^ j.val ≤ t then
    some ⟨t - 2 ^ j.val, Nat.sub_lt (lt_of_lt_of_le (by positivity) h.2) (by positivity)⟩
  else none

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [Fintype V] [DecidableEq V]
variable (B : LinearMap.BilinForm (ZMod 2) V) {K H q : ℕ}

noncomputable def groupLaw (hd : K + 1 ≤ Module.finrank (ZMod 2) V) (H : ℕ) :
    Law (Fin H → {v : V // v ≠ 0}) where
  mass := weight (step B (lagBack K)) H
  nonneg := weight_nonneg (fun _ _ _ => kernel_nonneg B _ _) H
  total := sum_weight (step_sum B (lagBack K) hd) H

noncomputable def rawLaw (hd : K + 1 ≤ Module.finrank (ZMod 2) V) (H q : ℕ) :
    Law (Fin q → Fin H → {v : V // v ≠ 0}) :=
  product (fun _ : Fin q => groupLaw B hd H)

lemma group_relations (hd : K + 1 ≤ Module.finrank (ZMod 2) V)
    {w : Fin H → {v : V // v ≠ 0}} (hw : 0 < (groupLaw B hd H).mass w)
    {r k : ℕ} (hk : k < K) (hk8 : k ≤ K / 8) (hrt : r + 2 ^ k < H) :
    B (w ⟨r, lt_trans (Nat.lt_add_of_pos_right (by positivity)) hrt⟩).val
      (w ⟨r + 2 ^ k, hrt⟩).val = 0 := by
  have hlag : 2 ^ k ≤ r + 2 ^ k := Nat.le_add_left _ _
  have hre : lagBack K (r + 2 ^ k) ⟨k, hk⟩ =
      some ⟨r, Nat.lt_add_of_pos_right (by positivity)⟩ := by
    simp [lagBack, hk8, hlag]
  exact supported_constraints B (lagBack K) H w hw ⟨r + 2 ^ k, hrt⟩ ⟨k, hk⟩ _ hre

lemma raw_relations (hd : K + 1 ≤ Module.finrank (ZMod 2) V)
    {w : Fin q → Fin H → {v : V // v ≠ 0}} (hw : 0 < (rawLaw B hd H q).mass w)
    (b : Fin q) {r k : ℕ} (hk : k < K) (hk8 : k ≤ K / 8) (hrt : r + 2 ^ k < H) :
    B (w b ⟨r, lt_trans (Nat.lt_add_of_pos_right (by positivity)) hrt⟩).val
      (w b ⟨r + 2 ^ k, hrt⟩).val = 0 := by
  apply group_relations B hd (k := k) (r := r) _ hk hk8 hrt
  have hz : (groupLaw B hd H).mass (w b) ≠ 0 := by
    intro hz
    have hp : (∏ i, (groupLaw B hd H).mass (w i)) = 0 :=
      prod_eq_zero (mem_univ b) hz
    exact (ne_of_gt hw) hp
  exact lt_of_le_of_ne ((groupLaw B hd H).nonneg (w b)) hz.symm

lemma group_label (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hd : K + 1 ≤ Module.finrank (ZMod 2) V) (r : Fin H) (a : {v : V // v ≠ 0}) :
    expect (groupLaw B hd H) (fun w => if w r = a then 1 else 0) =
      1 / Fintype.card {v : V // v ≠ 0} := by
  simpa only [FiniteLaw.expect, groupLaw, mul_ite, mul_one, mul_zero, marginal]
    using uniform_position B hB hnd (lagBack K) hd r a

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Empirical probability vector formed from a single group. -/
noncomputable def empirical (f : {v : V // v ≠ 0} → C)
    (w : Fin H → {v : V // v ≠ 0}) (c : C) : ℝ :=
  (∑ r, if f (w r) = c then (1 : ℝ) else 0) / H

omit [Module (ZMod 2) V] [Fintype V] [DecidableEq V] [Fintype C] in
lemma empirical_nonneg (f : {v : V // v ≠ 0} → C)
    (w : Fin H → {v : V // v ≠ 0}) (c : C) : 0 ≤ empirical f w c := by
  unfold empirical
  positivity

omit [Module (ZMod 2) V] [Fintype V] [DecidableEq V] in
lemma empirical_total (hH : 0 < H) (f : {v : V // v ≠ 0} → C)
    (w : Fin H → {v : V // v ≠ 0}) : ∑ c, empirical f w c = 1 := by
  unfold empirical
  rw [← sum_div, sum_comm]
  simp [hH.ne']

omit [Fintype C] in
lemma group_observable (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hd : K + 1 ≤ Module.finrank (ZMod 2) V) (f : {v : V // v ≠ 0} → C)
    (r : Fin H) (c : C) :
    expect (groupLaw B hd H) (fun w => if f (w r) = c then 1 else 0) =
      (∑ a : {v : V // v ≠ 0}, if f a = c then (1 : ℝ) else 0) /
        Fintype.card {v : V // v ≠ 0} := by
  have he (w : Fin H → {v : V // v ≠ 0}) :
      (if f (w r) = c then (1 : ℝ) else 0) =
        ∑ a, (if w r = a then (1 : ℝ) else 0) * (if f a = c then 1 else 0) := by
    simp only [ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]
  simp_rw [he]
  rw [expect_sum]
  simp_rw [expect_mul_const, group_label B hB hnd hd]
  rw [← mul_sum]
  ring

omit [Fintype C] in
lemma group_mean (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hd : K + 1 ≤ Module.finrank (ZMod 2) V) (hH : 0 < H)
    (f : {v : V // v ≠ 0} → C) (c : C) :
    expect (groupLaw B hd H) (fun w => empirical f w c) =
      (∑ a : {v : V // v ≠ 0}, if f a = c then (1 : ℝ) else 0) /
        Fintype.card {v : V // v ≠ 0} := by
  simp only [empirical, div_eq_mul_inv]
  rw [expect_mul_const, expect_sum]
  simp_rw [← div_eq_mul_inv, group_observable B hB hnd hd]
  simp [hH.ne']

/-- The first source use of the probability-vector estimate: it averages
groups, not falsely independent positions within a group. -/
theorem raw_empirical_tv (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hd : K + 1 ≤ Module.finrank (ZMod 2) V) (hH : 0 < H) (hq : 0 < q)
    (f : {v : V // v ≠ 0} → C) :
    expect (rawLaw B hd H q) (fun w => (1 / 2 : ℝ) * ∑ c,
      |(∑ b, empirical f (w b) c) / q -
        (∑ a : {v : V // v ≠ 0}, if f a = c then (1 : ℝ) else 0) /
          Fintype.card {v : V // v ≠ 0}|) ≤
      (1 / 2 : ℝ) * Real.sqrt (Fintype.card C / q) := by
  have : NeZero q := ⟨hq.ne'⟩
  simpa only [Fintype.card_fin, rawLaw] using independent_vectors_tv
    (fun _ : Fin q => groupLaw B hd H) (fun _ => empirical f) _
    (fun _ => empirical_nonneg f) (fun _ => empirical_total hH f)
    (fun _ => group_mean B hB hnd hd hH f)


/-- A specified arbitrary sublist, across any number of groups. The exponent
is the exact number of specified coordinates, not the size of its span. -/
theorem raw_sublist_groups (hd : K + 1 ≤ Module.finrank (ZMod 2) V) (hK : 1 ≤ K)
    (m : Fin q → Fin H → Option {v : V // v ≠ 0}) :
    FiniteLaw.expect (rawLaw B hd H q) (fun w => ∏ b, test (m b) (w b)) ≤
      ((2 : ℝ) ^ (2 * K) / Fintype.card {v : V // v ≠ 0}) ^
        (∑ b, (univ.filter (fun r => (m b r).isSome)).card) := by
  change FiniteLaw.expect (product (fun _ : Fin q => groupLaw B hd H)) _ ≤ _
  rw [product_moment]
  calc
    _ ≤ ∏ b, ((2 : ℝ) ^ (2 * K) / Fintype.card {v : V // v ≠ 0}) ^
        (univ.filter (fun r => (m b r).isSome)).card := by
      apply prod_le_prod
      · intro b _; exact expect_nonneg _ (test_nonneg _)
      · intro b _; exact raw_sublist B (lagBack K) hK hd H (m b)
    _ = _ := prod_pow_eq_pow_sum _ _ _

/-- All actual conditioned laws pay the factor two once for the whole word. -/
theorem conditioned_sublist (hd : K + 1 ≤ Module.finrank (ZMod 2) V) (hK : 1 ≤ K)
    (E : Finset (Fin q → Fin H → {v : V // v ≠ 0}))
    (hE : 1 / 2 ≤ prob (rawLaw B hd H q) E)
    (m : Fin q → Fin H → Option {v : V // v ≠ 0}) :
    FiniteLaw.expect (condition (rawLaw B hd H q) E (by change 0 < prob _ E; linarith))
      (fun w => ∏ b, test (m b) (w b)) ≤
      2 * ((2 : ℝ) ^ (2 * K) / Fintype.card {v : V // v ≠ 0}) ^
        (∑ b, (univ.filter (fun r => (m b r).isSome)).card) := by
  exact (condition_bound (rawLaw B hd H q) E hE _
    (fun w => prod_nonneg (fun b _ => test_nonneg _ _))).trans
      (mul_le_mul_of_nonneg_left (raw_sublist_groups B hd hK m) (by norm_num))

noncomputable def tvFromUniformObservable (f : {v : V // v ≠ 0} → C)
    (w : Fin q → Fin H → {v : V // v ≠ 0}) : ℝ :=
  (1 / 2 : ℝ) * ∑ c, |(∑ b, empirical f (w b) c) / q -
    (∑ a : {v : V // v ≠ 0}, if f a = c then (1 : ℝ) else 0) /
      Fintype.card {v : V // v ≠ 0}|

/-- A concrete, nonempty conditioning event enforcing the per-word condition
simultaneously for all the earlier-level windows. -/
theorem approximation_event {I : Type*} [Fintype I]
    (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hd : K + 1 ≤ Module.finrank (ZMod 2) V) (hH : 0 < H) (hq : 0 < q)
    (f : I → {v : V // v ≠ 0} → C) {θ : ℝ} (hθ : 0 < θ)
    (hbudget : (Fintype.card I : ℝ) *
      ((1 / 2 : ℝ) * Real.sqrt (Fintype.card C / q)) / θ ≤ 1 / 2) :
    1 / 2 ≤ prob (rawLaw B hd H q)
      (univ.filter (fun w => ∀ i, tvFromUniformObservable (f i) w ≤ θ)) := by
  apply good_event_mass _ _ _ hθ _ hbudget
  · intro i w
    unfold tvFromUniformObservable
    positivity
  · intro i
    exact raw_empirical_tv B hB hnd hd hH hq (f i)

end SmoothObstruction.WordLaw

namespace SmoothObstruction.FiniteLaw
open Finset
variable {A I J : Type*} [Fintype A] [Fintype I] [Fintype J]
  [DecidableEq A] [DecidableEq I] [DecidableEq J]

omit [DecidableEq A] [DecidableEq J] in
lemma product_injective_moment (P : I → Law A) (e : J → I) (he : Function.Injective e)
    (f : J → A → ℝ) :
    expect (product P) (fun x => ∏ j, f j (x (e j))) =
      ∏ j, expect (P (e j)) (f j) := by
  classical
  let F : I → A → ℝ := fun i a => if h : i ∈ Set.range e then f (Classical.choose h) a else 1
  have hF (j : J) (a : A) : F (e j) a = f j a := by
    have h : e j ∈ Set.range e := ⟨j, rfl⟩
    have hj : Classical.choose h = j := he (Classical.choose_spec h)
    dsimp only [F]
    rw [dite_eq_left h, hj]
  have hnot (i : I) (hi : i ∉ Set.range e) : F i = fun _ => 1 := by
    funext a
    dsimp only [F]
    rw [dite_eq_right hi]
  have hprod (x : I → A) : (∏ j, f j (x (e j))) = ∏ i, F i (x i) := by
    exact Fintype.prod_of_injective e he _ _ (fun i hi => congrFun (hnot i hi) (x i))
      (fun j => (hF j (x (e j))).symm)
  simp_rw [hprod]
  rw [product_moment]
  symm
  exact Fintype.prod_of_injective e he _ _
    (fun i hi => by rw [hnot i hi]; exact expect_const _ 1)
    (fun j => by congr 1; funext a; exact (hF j a).symm)

lemma product_restriction (P : I → Law A) (e : J → I) (he : Function.Injective e)
    (y : J → A) :
    expect (product P) (fun x => if (fun j => x (e j)) = y then 1 else 0) =
      (product (fun j => P (e j))).mass y := by
  classical
  have hprod (x : I → A) :
      (if (fun j => x (e j)) = y then (1 : ℝ) else 0) =
        ∏ j, if x (e j) = y j then (1 : ℝ) else 0 := by
    simp only [prod_boole, mem_univ, forall_const, funext_iff]
  simp_rw [hprod]
  rw [product_injective_moment P e he (fun j a => if a = y j then 1 else 0)]
  apply prod_congr rfl
  intro j _
  simp [expect, mul_ite]

lemma product_restriction_expect (P : I → Law A) (e : J → I) (he : Function.Injective e)
    (f : (J → A) → ℝ) :
    expect (product P) (fun x => f (fun j => x (e j))) =
      expect (product (fun j => P (e j))) f := by
  classical
  have hsum (x : I → A) : f (fun j => x (e j)) =
      ∑ y : J → A, (if (fun j => x (e j)) = y then (1 : ℝ) else 0) * f y := by
    simp only [ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]
  simp_rw [hsum]
  rw [expect_sum]
  simp_rw [expect_mul_const, product_restriction P e he]
  rfl

omit [DecidableEq A] [DecidableEq I] in
lemma prob_card_bound (P : Law A) (E : Finset A) {c : ℝ} (hc : ∀ a ∈ E, P.mass a ≤ c) :
    prob P E ≤ E.card * c := by
  calc
    _ ≤ ∑ _a ∈ E, c := sum_le_sum hc
    _ = _ := by simp

omit [DecidableEq A] in
lemma product_mass_upper (P : I → Law A) {c : ℝ} (hc : ∀ i a, (P i).mass a ≤ c)
    (x : I → A) : (product P).mass x ≤ c ^ Fintype.card I := by
  calc
    _ ≤ ∏ _i : I, c := prod_le_prod (fun i _ => (P i).nonneg (x i)) (fun i _ => hc i (x i))
    _ = _ := by simp

end SmoothObstruction.FiniteLaw

namespace SmoothObstruction.MatchingCount

variable {A I : Type*} [Fintype A] [Fintype I]

/-- Equalities oriented to a distinct later variable determine the removed
coordinates uniquely from those left free. This is the acyclic comparison
count, without an assumption of independence between equality events. -/
lemma increasing_count {n : ℕ} (f g : I → Fin n)
    (hfg : ∀ i, f i < g i) (hg : Function.Injective g) :
    Nat.card {w : Fin n → A // ∀ i, w (f i) = w (g i)} ≤
      Fintype.card A ^ (n - Fintype.card I) := by
  classical
  let F := {j : Fin n // j ∉ Set.range g}
  let restrict : {w : Fin n → A // ∀ i, w (f i) = w (g i)} → (F → A) :=
    fun w j => w.val j.val
  have hinj : Function.Injective restrict := by
    intro u v huv
    apply Subtype.ext
    funext j
    have heq : ∀ m, ∀ k : Fin n, k.val = m → u.val k = v.val k := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
        intro k hk
        by_cases hmem : k ∈ Set.range g
        · obtain ⟨i, rfl⟩ := hmem
          rw [← u.property i, ← v.property i]
          exact ih (f i).val (by simpa [← hk] using hfg i) (f i) rfl
        · exact congrFun huv (⟨k, hmem⟩ : F)
    exact heq j.val j rfl
  have hcardF : Fintype.card F = n - Fintype.card I := by
    have hsum := Fintype.card_subtype_compl (fun j : Fin n => j ∈ Set.range g)
    have hrange : Fintype.card {j : Fin n // j ∈ Set.range g} = Fintype.card I :=
      (Fintype.card_congr (Equiv.ofInjective g hg)).symm
    simp only [Fintype.card_fin] at hsum
    dsimp [F]
    omega
  have hbound := Nat.card_le_card_of_injective restrict hinj
  simpa [Nat.card_eq_fintype_card, Fintype.card_fun, hcardF] using hbound


/-- For a comparison with two injective endpoint lists and no tautological
loops, at least half the equality constraints can be oriented to distinct
later variables. This includes parallel edges and all repeated-word cases. -/
theorem matching_count {n : ℕ} (f g : I → Fin n)
    (hf : Function.Injective f) (hg : Function.Injective g) (hne : ∀ i, f i ≠ g i) :
    Nat.card {w : Fin n → A // ∀ i, w (f i) = w (g i)} ≤
      Fintype.card A ^ (n - (Fintype.card I + 1) / 2) := by
  classical
  let J := {i : I // f i < g i}
  let J' := {i : I // ¬ f i < g i}
  have hj : Fintype.card J + Fintype.card J' = Fintype.card I := by
    have h := Fintype.card_subtype_compl (fun i : I => f i < g i)
    have hle := Fintype.card_subtype_le (fun i : I => f i < g i)
    change Fintype.card J' = Fintype.card I - Fintype.card J at h
    change Fintype.card J ≤ Fintype.card I at hle
    omega
  by_cases ha : IsEmpty A
  · let := ha
    by_cases hn : n = 0
    · subst n
      have : IsEmpty I := ⟨fun i => Fin.elim0 (f i)⟩
      simp [Fintype.card_eq_zero]
    · have : IsEmpty (Fin n → A) := ⟨fun w => isEmptyElim (w ⟨0, Nat.pos_of_ne_zero hn⟩)⟩
      simp
  have : Nonempty A := not_isEmpty_iff.mp ha
  have mono {c : ℕ} (h : (Fintype.card I + 1) / 2 ≤ c) :
      Fintype.card A ^ (n - c) ≤ Fintype.card A ^ (n - (Fintype.card I + 1) / 2) :=
    Nat.pow_le_pow_right Fintype.card_pos (Nat.sub_le_sub_left h _)
  by_cases hJ : (Fintype.card I + 1) / 2 ≤ Fintype.card J
  · let R : {w : Fin n → A // ∀ i, w (f i) = w (g i)} →
        {w : Fin n → A // ∀ i : J, w (f i.val) = w (g i.val)} :=
      fun w => ⟨w.val, fun i => w.property i.val⟩
    have hinj : Function.Injective R := fun u v h => Subtype.ext (show u.val = v.val from congrArg (fun w => w.val) h)
    exact (Nat.card_le_card_of_injective R hinj).trans
      ((increasing_count (fun i : J => f i.val) (fun i : J => g i.val)
        (fun i => i.property) (hg.comp Subtype.val_injective)).trans (mono hJ))
  · have hJ' : (Fintype.card I + 1) / 2 ≤ Fintype.card J' := by omega
    let R : {w : Fin n → A // ∀ i, w (f i) = w (g i)} →
        {w : Fin n → A // ∀ i : J', w (g i.val) = w (f i.val)} :=
      fun w => ⟨w.val, fun i => (w.property i.val).symm⟩
    have hinj : Function.Injective R := fun u v h => Subtype.ext (show u.val = v.val from congrArg (fun w => w.val) h)
    have hgf (i : J') : g i.val < f i.val :=
      lt_of_le_of_ne (le_of_not_gt i.property) (hne i.val).symm
    exact (Nat.card_le_card_of_injective R hinj).trans
      ((increasing_count (fun i : J' => g i.val) (fun i : J' => f i.val) hgf
        (hf.comp Subtype.val_injective)).trans (mono hJ'))

end SmoothObstruction.MatchingCount

namespace SmoothObstruction.MatchingCount
open Finset
variable {A I W : Type*} [Fintype A] [Fintype I] [Fintype W]

/-- The comparison count in an arbitrary finite ambient coordinate set,
including several complete sampled words and repeated sample-list indices. -/
theorem matching_count_finite (f g : I → W)
    (hf : Function.Injective f) (hg : Function.Injective g) (hne : ∀ i, f i ≠ g i) :
    Nat.card {w : W → A // ∀ i, w (f i) = w (g i)} ≤
      Fintype.card A ^ (Fintype.card W - (Fintype.card I + 1) / 2) := by
  classical
  let E := Fintype.equivFin W
  let e : {w : W → A // ∀ i, w (f i) = w (g i)} ≃
      {w : Fin (Fintype.card W) → A // ∀ i, w (E (f i)) = w (E (g i))} :=
    { toFun := fun w => ⟨w.val ∘ E.symm, by simpa using w.property⟩
      invFun := fun w => ⟨w.val ∘ E, w.property⟩
      left_inv := fun w => Subtype.ext (by funext i; simp)
      right_inv := fun w => Subtype.ext (by funext i; simp) }
  rw [Nat.card_congr e]
  exact matching_count _ _ (E.injective.comp hf) (E.injective.comp hg)
    (fun i he => hne i (E.injective he))

end SmoothObstruction.MatchingCount

namespace SmoothObstruction.FiniteLaw
open Finset
variable {A I J R : Type*} [Fintype A] [Fintype I] [Fintype J] [Fintype R]
  [DecidableEq A] [DecidableEq I] [DecidableEq J] [DecidableEq R]

omit [DecidableEq A] in
lemma prob_mono (P : Law A) {E F : Finset A} (h : E ⊆ F) : prob P E ≤ prob P F := by
  apply Finset.sum_le_sum_of_subset_of_nonneg h
  intro a _ _
  exact P.nonneg a

/-- Actual independent complete-list sampling, with arbitrary repeated uses of
list indices in the comparison endpoints. The index injection counts each
independently sampled word once and all unused sampled words are integrated. -/
lemma sampled_matching_probability (P : I → Law (R → A)) (e : J → I)
    (he : Function.Injective e) (f g : R → J × R)
    (hf : Function.Injective f) (hg : Function.Injective g) (hne : ∀ r, f r ≠ g r)
    (s : Finset R) {c : ℝ} (hc : 0 ≤ c) (hP : ∀ j w, (P (e j)).mass w ≤ c) :
    prob (product P) (univ.filter (fun x => ∀ r ∈ s,
      x (e (f r).1) (f r).2 = x (e (g r).1) (g r).2)) ≤
      (Fintype.card A : ℝ) ^ (Fintype.card J * Fintype.card R - (s.card + 1) / 2) *
        c ^ Fintype.card J := by
  classical
  rw [prob_eq_expect]
  simp only [mem_filter, mem_univ, true_and]
  rw [product_restriction_expect P e he
    (fun x => if ∀ r ∈ s, x (f r).1 (f r).2 = x (g r).1 (g r).2 then 1 else 0)]
  have hprob : expect (product (fun j => P (e j)))
      (fun x => if ∀ r ∈ s, x (f r).1 (f r).2 = x (g r).1 (g r).2 then 1 else 0) =
      prob (product (fun j => P (e j)))
      (univ.filter (fun x => ∀ r ∈ s, x (f r).1 (f r).2 = x (g r).1 (g r).2)) := by
    rw [prob_eq_expect]
    simp only [mem_filter, mem_univ, true_and]
  rw [hprob]
  let Q := product (fun j => P (e j))
  let E : Finset (J → R → A) := univ.filter
    (fun x => ∀ r ∈ s, x (f r).1 (f r).2 = x (g r).1 (g r).2)
  have hcount : E.card ≤ Fintype.card A ^
      (Fintype.card J * Fintype.card R - (s.card + 1) / 2) := by
    let se : {x : J → R → A // ∀ r ∈ s, x (f r).1 (f r).2 = x (g r).1 (g r).2} ≃
        {x : J × R → A // ∀ r : s, x (f r) = x (g r)} :=
      { toFun := fun x => ⟨Function.uncurry x.val, fun r => x.property r r.property⟩
        invFun := fun x => ⟨Function.curry x.val, fun r hr => x.property ⟨r, hr⟩⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
    have h := MatchingCount.matching_count_finite (A := A)
      (fun r : s => f r) (fun r : s => g r)
      (hf.comp Subtype.val_injective) (hg.comp Subtype.val_injective) (fun r => hne r)
    rw [← Nat.card_congr se] at h
    simpa [Nat.card_eq_fintype_card, Fintype.card_subtype, E] using h
  exact (prob_card_bound Q E (fun x _ => product_mass_upper _ hP x)).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (pow_nonneg hc _))

/-- Union over specified matching-position sets. No label independence inside
a sampled word is assumed. -/
lemma sampled_bad_comparison (P : I → Law (R → A)) (e : J → I)
    (he : Function.Injective e) (f g : R → J × R)
    (hf : Function.Injective f) (hg : Function.Injective g) (hne : ∀ r, f r ≠ g r)
    (a : ℕ) {c : ℝ} (hc : 0 ≤ c) (hP : ∀ j w, (P (e j)).mass w ≤ c) :
    prob (product P) (univ.filter (fun x => a ≤ (univ.filter (fun r =>
      x (e (f r).1) (f r).2 = x (e (g r).1) (g r).2)).card)) ≤
      (2 : ℝ) ^ Fintype.card R *
        (Fintype.card A : ℝ) ^ (Fintype.card J * Fintype.card R - (a + 1) / 2) *
        c ^ Fintype.card J := by
  classical
  let S := powersetCard a (univ : Finset R)
  let E : S → Finset (I → R → A) := fun s => univ.filter (fun x => ∀ r ∈ s.val,
    x (e (f r).1) (f r).2 = x (e (g r).1) (g r).2)
  have hsub : (univ.filter (fun x => a ≤ (univ.filter (fun r : R =>
      x (e (f r).1) (f r).2 = x (e (g r).1) (g r).2)).card)) ⊆ univ.biUnion E := by
    intro x hx
    obtain ⟨s, hs, hsa⟩ := Finset.exists_subset_card_eq (mem_filter.mp hx).2
    have hsS : s ∈ S := mem_powersetCard.mpr ⟨subset_univ _, hsa⟩
    apply mem_biUnion.mpr
    refine ⟨⟨s, hsS⟩, mem_univ _, ?_⟩
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    intro r hr
    exact (mem_filter.mp (hs hr)).2
  have hbound (s : S) : prob (product P) (E s) ≤
      (Fintype.card A : ℝ) ^ (Fintype.card J * Fintype.card R - (a + 1) / 2) *
        c ^ Fintype.card J := by
    have h := sampled_matching_probability P e he f g hf hg hne s.val hc hP
    have hs := (mem_powersetCard.mp s.property).2
    simpa only [hs] using h
  have hcard : Fintype.card S ≤ 2 ^ Fintype.card R := by
    rw [Fintype.card_coe, card_powersetCard, card_univ]
    exact Nat.choose_le_two_pow _ _
  calc
    _ ≤ prob (product P) (univ.biUnion E) := prob_mono _ hsub
    _ ≤ ∑ s : S, prob (product P) (E s) := union_bound _ E
    _ ≤ ∑ _s : S, (Fintype.card A : ℝ) ^
        (Fintype.card J * Fintype.card R - (a + 1) / 2) * c ^ Fintype.card J :=
      sum_le_sum (fun s _ => hbound s)
    _ = (Fintype.card S : ℝ) * ((Fintype.card A : ℝ) ^
        (Fintype.card J * Fintype.card R - (a + 1) / 2) * c ^ Fintype.card J) := by simp
    _ ≤ (2 : ℝ) ^ Fintype.card R * ((Fintype.card A : ℝ) ^
        (Fintype.card J * Fintype.card R - (a + 1) / 2) * c ^ Fintype.card J) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (mul_nonneg (by positivity) (pow_nonneg hc _))
    _ = _ := by ring

end SmoothObstruction.FiniteLaw

namespace SmoothObstruction.FiniteLaw

/-- Exact simplification of the sampled comparison cost. The one-time
conditioning doubles each of at most three word laws, costing eight, not a
factor per selected label. -/
lemma comparison_cost {L U : ℝ} (hL : 1 ≤ L) (hU : 1 ≤ U)
    {N j a : ℕ} (hj : 1 ≤ j) (hj' : j ≤ 3) (ha : a ≤ N) :
    (2 : ℝ) ^ N * L ^ (j * N - (a + 1) / 2) *
      (2 * (U / L) ^ N) ^ j ≤
      8 * 2 ^ N * U ^ (3 * N) * L ^ (-(a : ℝ) / 2) := by
  have hLp : 0 < L := by linarith
  have hUp : 0 < U := by linarith
  have hd : (a + 1) / 2 ≤ j * N := by
    have h1 : (a + 1) / 2 ≤ a := by omega
    have h2 : N ≤ j * N := by nlinarith
    omega
  have heq : L ^ (j * N - (a + 1) / 2) * (2 * (U / L) ^ N) ^ j =
      (2 : ℝ) ^ j * U ^ (j * N) / L ^ ((a + 1) / 2) := by
    simp only [mul_pow, div_pow, ← pow_mul]
    rw [Nat.mul_comm N j]
    apply (eq_div_iff (pow_ne_zero _ hLp.ne')).mpr
    have hp : L ^ (j * N - (a + 1) / 2) * L ^ ((a + 1) / 2) = L ^ (j * N) := by
      rw [← pow_add, Nat.sub_add_cancel hd]
    field_simp
    nlinarith [congrArg (fun z => (2 : ℝ) ^ j * U ^ (j * N) * z) hp]
  have ht : (2 : ℝ) ^ j ≤ 8 := by
    calc
      _ ≤ (2 : ℝ) ^ 3 := pow_le_pow_right₀ (by norm_num) hj'
      _ = _ := by norm_num
  have hu : U ^ (j * N) ≤ U ^ (3 * N) := pow_le_pow_right₀ hU (Nat.mul_le_mul_right _ hj')
  have hhalf : (a : ℝ) / 2 ≤ ((a + 1) / 2 : ℕ) := by
    have h : a ≤ 2 * ((a + 1) / 2) := by omega
    have hr : (a : ℝ) ≤ 2 * (((a + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast h
    linarith
  have hp : L ^ ((a : ℝ) / 2) ≤ L ^ ((a + 1) / 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hL hhalf
  have hinv : 1 / L ^ ((a + 1) / 2) ≤ L ^ (-(a : ℝ) / 2) := by
    rw [show -(a : ℝ) / 2 = -((a : ℝ) / 2) by ring,
      Real.rpow_neg hLp.le, ← one_div]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hLp _) hp
  calc
    _ = 2 ^ N * ((2 : ℝ) ^ j * U ^ (j * N) / L ^ ((a + 1) / 2)) := by
      rw [mul_assoc, heq]
    _ ≤ 2 ^ N * (8 * U ^ (3 * N) / L ^ ((a + 1) / 2)) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (mul_le_mul ht hu (by positivity) (by norm_num)) (by positivity))
        (by positivity)
    _ ≤ 2 ^ N * (8 * U ^ (3 * N) * L ^ (-(a : ℝ) / 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [div_eq_mul_inv, one_div, one_mul] using
        mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ 8 * U ^ (3 * N))
    _ = _ := by ring

end SmoothObstruction.FiniteLaw

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_WordParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Filter Topology

namespace SmoothObstruction.WordParameters

/-- The source logarithm is binary. Levels here are numbered i+1. -/
noncomputable def ell (s : ℕ) : ℝ := Real.logb 2 ((2 : ℝ) ^ (2 * s) - 1)
noncomputable def K (s : ℕ) : ℕ := ⌊Real.sqrt (ell s)⌋₊
noncomputable def epsilon (i : ℕ) : ℝ := 1 / (2 : ℝ) ^ (i + 3)
noncomputable def X (i s : ℕ) : ℝ := epsilon i / 100 * 2 ^ K s * ell s
noncomputable def nextS (i s : ℕ) : ℕ := ⌊X i s / 2⌋₊
noncomputable def sequence (s₀ : ℕ) : ℕ → ℕ
  | 0 => s₀
  | i + 1 => nextS i (sequence s₀ i)

lemma epsilon_pos (i : ℕ) : 0 < epsilon i := by unfold epsilon; positivity
lemma epsilon_succ (i : ℕ) : epsilon (i + 1) = epsilon i / 2 := by
  unfold epsilon
  rw [show i + 1 + 3 = i + 3 + 1 by omega, pow_succ]
  ring

lemma ell_zero : ell 0 = 0 := by simp [ell]
lemma ell_bounds {s : ℕ} (hs : 1 ≤ s) : (2 * s : ℝ) - 1 < ell s ∧ ell s < 2 * s := by
  have hd : 2 ≤ 2 * s := by omega
  have hpow : 2 ≤ (2 : ℝ) ^ (2 * s - 1) := by
    calc
      _ = (2 : ℝ) ^ 1 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have hrew : (2 : ℝ) ^ (2 * s) = 2 ^ (2 * s - 1) * 2 := by
    conv_lhs => rw [show 2 * s = (2 * s - 1) + 1 by omega]
    rw [pow_succ]
  have hpos : 0 < (2 : ℝ) ^ (2 * s) - 1 := by rw [hrew]; linarith
  have hl := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by positivity : 0 < (2 : ℝ) ^ (2 * s - 1))
    (show (2 : ℝ) ^ (2 * s - 1) < 2 ^ (2 * s) - 1 by rw [hrew]; linarith)
  have hu := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) hpos
    (show (2 : ℝ) ^ (2 * s) - 1 < 2 ^ (2 * s) by linarith)
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hl hu
  have hsreal : ((2 * s - 1 : ℕ) : ℝ) = 2 * s - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; rfl
  exact ⟨by simpa [ell, hsreal] using hl, by simpa [ell] using hu⟩

lemma ell_nonneg (s : ℕ) : 0 ≤ ell s := by
  rcases s with _ | s
  · rw [ell_zero]
  · have h := (ell_bounds (by omega : 1 ≤ s + 1)).1
    have hs : (0 : ℝ) ≤ s := by positivity
    push_cast at h
    linarith

lemma K_bounds (s : ℕ) : (K s : ℝ) ^ 2 ≤ ell s ∧ ell s < (K s + 1 : ℝ) ^ 2 := by
  have h0 := Real.sqrt_nonneg (ell s)
  have h1 := Nat.floor_le h0
  have h2 := Nat.lt_floor_add_one (Real.sqrt (ell s))
  have he := Real.sq_sqrt (ell_nonneg s)
  change (K s : ℝ) ≤ Real.sqrt (ell s) at h1
  change Real.sqrt (ell s) < (K s : ℝ) + 1 at h2
  constructor <;> nlinarith [sq_nonneg ((K s : ℝ) - Real.sqrt (ell s)),
    show 0 ≤ (K s : ℝ) from Nat.cast_nonneg _]

/-- A single integer estimate proves all the logarithmic polynomial budgets
at the fixed initial threshold. No floating-point certificate is used. -/
lemma polynomial_budget : ∀ k : ℕ, 256 ≤ k → ((k : ℝ) + 14) ^ 16 ≤ (2 : ℝ) ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hnreal : (256 : ℝ) ≤ n := by exact_mod_cast hn
    have hstep : (n : ℝ) + 1 + 14 ≤ (257 / 256 : ℝ) * (n + 14) := by linarith
    have hp := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ n + 1 + 14) hstep 16
    have hc : (257 / 256 : ℝ) ^ 16 ≤ 2 := by norm_num
    calc
      (((n + 1 : ℕ) : ℝ) + 14) ^ 16 ≤ (257 / 256 : ℝ) ^ 16 * ((n : ℝ) + 14) ^ 16 := by
        simpa only [Nat.cast_add, Nat.cast_one, mul_pow] using hp
      _ ≤ 2 * ((n : ℝ) + 14) ^ 16 := mul_le_mul_of_nonneg_right hc (by positivity)
      _ ≤ 2 * 2 ^ n := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

lemma polynomial_root_budget {k : ℕ} (hk : 256 ≤ k) :
    (14 + k : ℝ) ≤ (2 : ℝ) ^ ((k : ℝ) / 8) ∧
      ((k : ℝ) + 1) ^ 2 ≤ (2 : ℝ) ^ ((k : ℝ) / 8) ∧
      (k : ℝ) ^ 2 ≤ (2 : ℝ) ^ ((k : ℝ) / 3) := by
  have hbase := polynomial_budget k hk
  have hkn : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have h8 : (14 + k : ℝ) ^ 8 ≤ 2 ^ k := by
    calc
      _ ≤ ((k : ℝ) + 14) ^ 16 := by
        rw [add_comm 14]
        exact pow_le_pow_right₀ (by linarith) (by decide)
      _ ≤ _ := hbase
  have h16 : (((k : ℝ) + 1) ^ 2) ^ 8 ≤ 2 ^ k := by
    rw [← pow_mul]
    exact (pow_le_pow_left₀ (by positivity) (by linarith : (k : ℝ) + 1 ≤ k + 14) 16).trans hbase
  have h6 : ((k : ℝ) ^ 2) ^ 3 ≤ 2 ^ k := by
    rw [← pow_mul]
    exact ((pow_le_pow_left₀ (by positivity) (by linarith : (k : ℝ) ≤ k + 14) 6).trans
      (pow_le_pow_right₀ (by linarith) (by decide))).trans hbase
  have hr8 : ((2 : ℝ) ^ ((k : ℝ) / 8)) ^ 8 = (2 : ℝ) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    simp
  have hr3 : ((2 : ℝ) ^ ((k : ℝ) / 3)) ^ 3 = (2 : ℝ) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    simp
  refine ⟨?_, ?_, ?_⟩
  · exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 8 ≠ 0)).mp (hr8 ▸ h8)
  · exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 8 ≠ 0)).mp (hr8 ▸ h16)
  · exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 3 ≠ 0)).mp (hr3 ▸ h6)


lemma rounding {i s : ℕ} (hX : 6 ≤ X i s) :
    X i s - 3 < ell (nextS i s) ∧ ell (nextS i s) ≤ X i s ∧
      X i s / 2 ≤ ell (nextS i s) := by
  have hpos : 0 ≤ X i s / 2 := by linarith
  have hlo := Nat.lt_floor_add_one (X i s / 2)
  have hup := Nat.floor_le hpos
  change X i s / 2 < (nextS i s : ℝ) + 1 at hlo
  change (nextS i s : ℝ) ≤ X i s / 2 at hup
  have hs : 1 ≤ nextS i s := by
    by_contra h
    have hz : nextS i s = 0 := by omega
    simp only [hz, Nat.cast_zero, zero_add] at hlo
    linarith
  obtain ⟨he1, he2⟩ := ell_bounds hs
  refine ⟨by linarith, by linarith, by linarith⟩

lemma exp_half_sub_one {k : ℕ} (hk : 6 ≤ k) :
    (2 : ℝ) ^ ((k : ℝ) / 3) ≤ 2 ^ ((k : ℝ) / 2) - 1 := by
  have hkr : (6 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : 1 ≤ (2 : ℝ) ^ ((k : ℝ) / 3) := Real.one_le_rpow (by norm_num) (by positivity)
  have hh : (2 : ℝ) ^ ((k : ℝ) / 3 + 1) ≤ 2 ^ ((k : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one] at hh
  linarith

lemma X_lower {i s : ℕ} (hε : 32 ≤ epsilon i * K s) :
    (8 / 25 : ℝ) * K s * 2 ^ K s ≤ X i s := by
  have hk : 0 ≤ (K s : ℝ) := Nat.cast_nonneg _
  have hep : 0 ≤ epsilon i := (epsilon_pos i).le
  have he1 := mul_le_mul_of_nonneg_left (K_bounds s).1 hep
  have he2 := mul_le_mul_of_nonneg_right hε hk
  have ht : 32 * K s ≤ epsilon i * ell s := by nlinarith
  have ht' := mul_le_mul_of_nonneg_right ht
    (show 0 ≤ (2 : ℝ) ^ K s / 100 by positivity)
  unfold X
  nlinarith

/-- Growth from exactly the source recursion, including the floor to the
largest even dimension. No later enlargement of the initial alphabet occurs. -/
theorem one_step_growth {i s : ℕ} (hk : 256 ≤ K s) (hε : 32 ≤ epsilon i * K s) :
    6 ≤ X i s ∧ (2 : ℝ) ^ K s ≤ ell (nextS i s) ∧
      (2 : ℝ) ^ ((K s : ℝ) / 3) ≤ K (nextS i s) ∧
      K s ^ 2 ≤ K (nextS i s) ∧ 4 * K s ≤ K (nextS i s) := by
  have hkr : (256 : ℝ) ≤ K s := by exact_mod_cast hk
  have hn : 1 ≤ (2 : ℝ) ^ K s := one_le_pow₀ (by norm_num)
  have hxlo := X_lower hε
  have hx : 6 ≤ X i s := by nlinarith
  have hround := rounding hx
  have hnext : (2 : ℝ) ^ K s ≤ ell (nextS i s) := by nlinarith
  have hsq : ((2 : ℝ) ^ ((K s : ℝ) / 2)) ^ 2 = (2 : ℝ) ^ K s := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    simp
  have hhalf : (2 : ℝ) ^ ((K s : ℝ) / 2) ≤ (K (nextS i s) : ℝ) + 1 := by
    have hbound := (K_bounds (nextS i s)).2
    nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) ((K s : ℝ) / 2),
      show 0 ≤ (K (nextS i s) : ℝ) from Nat.cast_nonneg _]
  have hthird := exp_half_sub_one (by omega : 6 ≤ K s)
  have hg : (2 : ℝ) ^ ((K s : ℝ) / 3) ≤ K (nextS i s) := by linarith
  have hsqr : K s ^ 2 ≤ K (nextS i s) := by
    have h := (polynomial_root_budget hk).2.2.trans hg
    exact_mod_cast h
  have hfour : 4 * K s ≤ K (nextS i s) := by
    have hkn : 4 ≤ K s := by omega
    have := Nat.mul_le_mul_right (K s) hkn
    rw [← sq] at this
    exact this.trans hsqr
  exact ⟨hx, hnext, hg, hsqr, hfour⟩

/-- All levels obey the fixed initial threshold and the exact epsilon growth
bound in source (word-growth). Level zero means manuscript level one. -/
theorem sequence_growth {s₀ : ℕ} (h₀ : 256 ≤ K s₀) :
    ∀ i, 256 ≤ K (sequence s₀ i) ∧
      32 * (2 : ℝ) ^ i ≤ epsilon i * K (sequence s₀ i) := by
  intro i
  induction i with
  | zero =>
    simp only [sequence, pow_zero, mul_one]
    refine ⟨h₀, ?_⟩
    have h : (256 : ℝ) ≤ K s₀ := by exact_mod_cast h₀
    norm_num [epsilon]
    linarith
  | succ i ih =>
    have hε : 32 ≤ epsilon i * K (sequence s₀ i) := by
      have hh : 1 ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
      nlinarith [ih.2]
    have hstep := one_step_growth ih.1 hε
    have hfour := hstep.2.2.2.2
    change 256 ≤ K (nextS i (sequence s₀ i)) ∧ _
    refine ⟨by omega, ?_⟩
    change 32 * 2 ^ (i + 1) ≤ epsilon (i + 1) * K (nextS i (sequence s₀ i))
    rw [epsilon_succ, pow_succ]
    have hfourr : (4 : ℝ) * K (sequence s₀ i) ≤ K (nextS i (sequence s₀ i)) := by
      exact_mod_cast hfour
    have he := mul_le_mul_of_nonneg_left hfourr (epsilon_pos i).le
    nlinarith [ih.2]


noncomputable def commonBound (k : ℕ) : ℝ :=
  14 + k + 1 / 2 * (2 : ℝ) ^ ((k : ℝ) / 8) * ((k : ℝ) + 1) ^ 2

lemma common_bound {k : ℕ} (hk : 256 ≤ k) :
    commonBound k ≤ (2 : ℝ) ^ ((k : ℝ) / 4) ∧
      (2 : ℝ) ^ ((k : ℝ) / 4) ≤ (1 / 8 : ℝ) * 2 ^ ((k : ℝ) / 3) := by
  obtain ⟨ha, hb, _⟩ := polynomial_root_budget hk
  have hkr : (256 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : 0 < (2 : ℝ) ^ ((k : ℝ) / 8) := by positivity
  have htwo : 2 ≤ (2 : ℝ) ^ ((k : ℝ) / 8) := by
    calc
      _ = (2 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hs : ((2 : ℝ) ^ ((k : ℝ) / 8)) ^ 2 = (2 : ℝ) ^ ((k : ℝ) / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1; push_cast; ring
  constructor
  · unfold commonBound
    nlinarith [mul_le_mul_of_nonneg_left hb hp.le]
  · have h : (2 : ℝ) ^ ((k : ℝ) / 4 + 3) ≤ (2 : ℝ) ^ ((k : ℝ) / 3) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)] at h
    norm_num at h
    linarith

lemma log_tolerance : Real.logb 2 (10000 : ℝ) < 14 := by
  have h := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 10000)
    (by norm_num : (10000 : ℝ) < 2 ^ 14)
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at h
  simpa only [Nat.cast_ofNat, mul_one] using h

/-- The logarithmic filter budget at consecutive source levels. -/
lemma filter_exponent {i s : ℕ} (hk : 256 ≤ K s) (hε : 32 ≤ epsilon i * K s) :
    Real.logb 2 (10000 : ℝ) + K s +
      (2 : ℝ) ^ (K s / 8) * ell s / 2 -
      ((K (nextS i s) - K (nextS i s) / 2 : ℕ) : ℝ) / 2 ≤
      -(1 / 8 : ℝ) * (2 : ℝ) ^ ((K s : ℝ) / 3) := by
  have hg := (one_step_growth hk hε).2.2.1
  have hc := (common_bound hk).1.trans (common_bound hk).2
  have hd : (2 : ℝ) ^ (K s / 8) ≤ (2 : ℝ) ^ ((K s : ℝ) / 8) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have h := Nat.div_mul_le_self (K s) 8
    have hr : ((K s / 8 : ℕ) : ℝ) * 8 ≤ K s := by exact_mod_cast h
    linarith
  have hdiv : (K (nextS i s) : ℝ) / 2 ≤
      ((K (nextS i s) - K (nextS i s) / 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (Nat.div_le_self _ _)]
    have h := Nat.div_mul_le_self (K (nextS i s)) 2
    have hr : ((K (nextS i s) / 2 : ℕ) : ℝ) * 2 ≤ K (nextS i s) := by exact_mod_cast h
    linarith
  have hp := mul_le_mul hd (K_bounds s).2.le (ell_nonneg s)
    (show 0 ≤ (2 : ℝ) ^ ((K s : ℝ) / 8) by positivity)
  unfold commonBound at hc
  nlinarith [log_tolerance]

/-- The logarithmic window budget, with exactly the source cardinalities. -/
lemma window_exponent {i s : ℕ} (hk : 256 ≤ K s) (hε : 32 ≤ epsilon i * K s) :
    Real.logb 2 (10000 : ℝ) + K s +
      (2 : ℝ) ^ (K s / 8) * ell s / 2 - ell (nextS i s) / 2 ≤
      -(2 : ℝ) ^ K s / 4 := by
  have hg := (one_step_growth hk hε).2.1
  have hc := (common_bound hk).1
  have hd : (2 : ℝ) ^ (K s / 8) ≤ (2 : ℝ) ^ ((K s : ℝ) / 8) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have h := Nat.div_mul_le_self (K s) 8
    have hr : ((K s / 8 : ℕ) : ℝ) * 8 ≤ K s := by exact_mod_cast h
    linarith
  have hp := mul_le_mul hd (K_bounds s).2.le (ell_nonneg s)
    (show 0 ≤ (2 : ℝ) ^ ((K s : ℝ) / 8) by positivity)
  have hkr : (256 : ℝ) ≤ K s := by exact_mod_cast hk
  have hsmall : (2 : ℝ) ^ ((K s : ℝ) / 4) ≤ (2 : ℝ) ^ K s / 4 := by
    have h : (2 : ℝ) ^ ((K s : ℝ) / 4 + 2) ≤ (2 : ℝ) ^ (K s : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)] at h
    norm_num at h
    linarith
  unfold commonBound at hc
  nlinarith [log_tolerance]

lemma distance_exponent {i s : ℕ} (hk : 256 ≤ K s) (hε : 32 ≤ epsilon i * K s) :
    5 + K s + 3 * ell (nextS i s) +
      (6 * K s + 1) * (2 : ℝ) ^ K s - epsilon i * (2 : ℝ) ^ K s * ell s / 2 ≤
      -(K s : ℝ) * (2 : ℝ) ^ K s := by
  have hround := (rounding (one_step_growth hk hε).1).2.1
  have hel : 32 * K s ≤ epsilon i * ell s := by
    have h1 := mul_le_mul_of_nonneg_left (K_bounds s).1 (epsilon_pos i).le
    have h2 := mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg (K s) : (0 : ℝ) ≤ K s)
    nlinarith
  have hel' := mul_le_mul_of_nonneg_right hel
    (show 0 ≤ (2 : ℝ) ^ K s by positivity)
  have hkr : (256 : ℝ) ≤ K s := by exact_mod_cast hk
  have hp : 1 ≤ (2 : ℝ) ^ K s := one_le_pow₀ (by norm_num)
  unfold X at hround
  nlinarith


noncomputable def alphabetSize (s : ℕ) : ℝ := (2 : ℝ) ^ (2 * s) - 1
noncomputable def filterBudget (s t : ℕ) : ℝ :=
  10000 * (2 : ℝ) ^ K s * Real.sqrt
    (alphabetSize s ^ (2 ^ (K s / 8)) / (2 : ℝ) ^ (K t - K t / 2))
noncomputable def windowBudget (s t : ℕ) : ℝ :=
  10000 * (2 : ℝ) ^ K s * Real.sqrt
    (alphabetSize s ^ (2 ^ (K s / 8)) / alphabetSize t)
noncomputable def distanceBudget (i s t : ℕ) : ℝ :=
  32 * (2 : ℝ) ^ K s * alphabetSize t ^ 3 *
    (2 : ℝ) ^ ((6 * K s + 1) * 2 ^ K s) *
      alphabetSize s ^ (-epsilon i * (2 : ℝ) ^ K s / 2)

lemma s_pos_of_Kpos {s : ℕ} (hk : 0 < K s) : 1 ≤ s := by
  by_contra h
  have hz : s = 0 := by omega
  subst s
  simp [K, ell_zero] at hk

lemma alphabetSize_pos {s : ℕ} (hs : 1 ≤ s) : 0 < alphabetSize s := by
  have h : (1 : ℝ) < 2 ^ (2 * s) := one_lt_pow₀ (by norm_num) (by omega)
  unfold alphabetSize
  linarith

lemma log_sqrt {x : ℝ} (hx : 0 < x) : Real.logb 2 (Real.sqrt x) = Real.logb 2 x / 2 := by
  rw [Real.sqrt_eq_rpow, Real.logb_rpow_eq_mul_logb_of_pos hx]
  ring

lemma filterBudget_pos {s : ℕ} (hs : 1 ≤ s) (t : ℕ) : 0 < filterBudget s t := by
  unfold filterBudget
  have := alphabetSize_pos hs
  positivity

lemma windowBudget_pos {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) : 0 < windowBudget s t := by
  unfold windowBudget
  have := alphabetSize_pos hs
  have := alphabetSize_pos ht
  positivity

lemma distanceBudget_pos {i s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) : 0 < distanceBudget i s t := by
  unfold distanceBudget
  have := alphabetSize_pos hs
  have := alphabetSize_pos ht
  positivity

lemma log_filterBudget {s : ℕ} (hs : 1 ≤ s) (t : ℕ) :
    Real.logb 2 (filterBudget s t) = Real.logb 2 (10000 : ℝ) + K s +
      (2 : ℝ) ^ (K s / 8) * ell s / 2 -
      ((K t - K t / 2 : ℕ) : ℝ) / 2 := by
  have hL := alphabetSize_pos hs
  unfold filterBudget
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by norm_num) (by positivity),
    log_sqrt (by positivity), Real.logb_div (by positivity) (by positivity)]
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one,
    Nat.cast_pow, Nat.cast_ofNat]
  change Real.logb 2 (10000 : ℝ) + K s +
    ((2 : ℝ) ^ (K s / 8) * ell s - ((K t - K t / 2 : ℕ) : ℝ)) / 2 = _
  ring

lemma log_windowBudget {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) :
    Real.logb 2 (windowBudget s t) = Real.logb 2 (10000 : ℝ) + K s +
      (2 : ℝ) ^ (K s / 8) * ell s / 2 - ell t / 2 := by
  have hL := alphabetSize_pos hs
  have hM := alphabetSize_pos ht
  unfold windowBudget
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by norm_num) (by positivity),
    log_sqrt (by positivity), Real.logb_div (by positivity) (by positivity)]
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one,
    Nat.cast_pow, Nat.cast_ofNat]
  change Real.logb 2 (10000 : ℝ) + K s +
    ((2 : ℝ) ^ (K s / 8) * ell s - ell t) / 2 = _
  ring

lemma log_distanceBudget {i s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) :
    Real.logb 2 (distanceBudget i s t) =
      5 + K s + 3 * ell t + (6 * K s + 1) * (2 : ℝ) ^ K s -
        epsilon i * (2 : ℝ) ^ K s * ell s / 2 := by
  have hL := alphabetSize_pos hs
  have hM := alphabetSize_pos ht
  have h32 : Real.logb 2 (32 : ℝ) = 5 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num]
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num
  unfold distanceBudget
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by norm_num) (by positivity),
    Real.logb_rpow_eq_mul_logb_of_pos hL]
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one,
    Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_add, Nat.cast_one, h32]
  change 5 + K s + 3 * ell t + (6 * K s + 1) * (2 : ℝ) ^ K s +
    (-epsilon i * (2 : ℝ) ^ K s / 2) * ell s = _
  ring

/-- All actual probability budgets, not just formal logarithmic surrogates,
are controlled at the single fixed initial threshold. -/
theorem actual_budgets {i s : ℕ} (hk : 256 ≤ K s) (hε : 32 ≤ epsilon i * K s) :
    filterBudget s (nextS i s) < 1 / 2 ∧
      windowBudget s (nextS i s) < 1 / 4 ∧
      distanceBudget i s (nextS i s) < 1 / 4 := by
  have hs : 1 ≤ s := s_pos_of_Kpos (by omega)
  have hstep := one_step_growth hk hε
  have ht : 1 ≤ nextS i s := s_pos_of_Kpos (by omega)
  have hkr : (256 : ℝ) ≤ K s := by exact_mod_cast hk
  have hthird : 16 ≤ (2 : ℝ) ^ ((K s : ℝ) / 3) := by
    calc
      _ = (2 : ℝ) ^ (4 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hpow : 16 ≤ (2 : ℝ) ^ K s := by
    calc
      _ = (2 : ℝ) ^ 4 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have hlog2 : Real.logb 2 (1 / 2 : ℝ) = -1 := by
    rw [Real.logb_div (by norm_num) (by norm_num)]
    simp
  have hlog4 : Real.logb 2 (1 / 4 : ℝ) = -2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    rw [Real.logb_div (by norm_num) (by norm_num), Real.logb_pow]
    simp
  refine ⟨?_, ?_, ?_⟩
  · apply (Real.logb_lt_logb_iff (by norm_num : (1 : ℝ) < 2) (filterBudget_pos hs _) (by norm_num)).mp
    rw [log_filterBudget hs, hlog2]
    linarith [filter_exponent hk hε]
  · apply (Real.logb_lt_logb_iff (by norm_num : (1 : ℝ) < 2) (windowBudget_pos hs ht) (by norm_num)).mp
    rw [log_windowBudget hs ht, hlog4]
    linarith [window_exponent hk hε]
  · apply (Real.logb_lt_logb_iff (by norm_num : (1 : ℝ) < 2) (distanceBudget_pos (i := i) hs ht) (by norm_num)).mp
    rw [log_distanceBudget hs ht, hlog4]
    nlinarith [distance_exponent hk hε]

end SmoothObstruction.WordParameters

namespace SmoothObstruction.WordParameters

noncomputable def length (s₀ : ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => length s₀ i * 2 ^ K (sequence s₀ i)

noncomputable def rate (s₀ i : ℕ) : ℝ := ell (sequence s₀ i) / length s₀ i

lemma length_pos (s₀ i : ℕ) : 0 < length s₀ i := by
  induction i with
  | zero => simp [length]
  | succ i ih => exact Nat.mul_pos ih (by positivity)

lemma length_dvd (s₀ i : ℕ) : length s₀ i ∣ length s₀ (i + 1) :=
  ⟨2 ^ K (sequence s₀ i), rfl⟩

lemma step_conditions {s₀ : ℕ} (h₀ : 256 ≤ K s₀) (i : ℕ) :
    256 ≤ K (sequence s₀ i) ∧ 32 ≤ epsilon i * K (sequence s₀ i) := by
  have h := sequence_growth h₀ i
  refine ⟨h.1, ?_⟩
  have hp : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  nlinarith [h.2]

end SmoothObstruction.WordParameters

namespace SmoothObstruction.WordParameters

/-- A concrete admissible first vector dimension. It makes the main
construction's initial-size condition nonvacuous. -/
lemma initial_threshold : 256 ≤ K 40000 := by
  unfold K
  apply Nat.le_floor
  apply (Real.le_sqrt (by norm_num) (ell_nonneg 40000)).mpr
  have h := (ell_bounds (by norm_num : 1 ≤ (40000 : ℕ))).1
  norm_num at h ⊢
  linarith

/-- The actual nonzero symplectic sampler always has a nonzero choice. -/
lemma dimension_budget {s : ℕ} (hK : 256 ≤ K s) : K s + 1 ≤ 2 * s := by
  have hs : 1 ≤ s := by
    by_contra hn
    have hz : s = 0 := by omega
    simp [hz, K, ell_zero] at hK
  have hl := (ell_bounds hs).2
  have hk := (K_bounds s).1
  have hkreal : (256 : ℝ) ≤ K s := by exact_mod_cast hK
  have h : (K s : ℝ) + 1 < 2 * s := by nlinarith
  have hn : K s + 1 < 2 * s := by exact_mod_cast h
  exact hn.le

end SmoothObstruction.WordParameters

end

section

open Finset

namespace SmoothObstruction.WordAlphabet

/-- The two coordinate halves of the source's F₂^(2s); this product is the
canonical coordinate bijection, not a different graph or bilinear form. -/
abbrev Space (s : ℕ) := (Fin s → ZMod 2) × (Fin s → ZMod 2)
abbrev Alphabet (s : ℕ) := {v : Space s // v ≠ 0}

def form (s : ℕ) : LinearMap.BilinForm (ZMod 2) (Space s) :=
  LinearMap.mk₂ (ZMod 2) (fun u v => ∑ a, (u.1 a * v.2 a + u.2 a * v.1 a))
    (by intro u v w; simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply];
        simp only [add_mul, sum_add_distrib]; ring)
    (by intro c u v; simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul];
        simp only [mul_assoc, ← mul_add, ← mul_sum])
    (by intro u v w; simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply];
        simp only [mul_add, sum_add_distrib]; ring)
    (by intro c u v; simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul];
        simp only [mul_left_comm _ c, ← mul_add, ← mul_sum])

lemma form_apply (s : ℕ) (u v : Space s) :
    form s u v = ∑ a, (u.1 a * v.2 a + u.2 a * v.1 a) := rfl

lemma form_alt (s : ℕ) : (form s).IsAlt := by
  intro u
  rw [form_apply]
  apply sum_eq_zero
  intro a _
  rw [mul_comm (u.2 a) (u.1 a), ← two_mul]
  rw [show (2 : ZMod 2) = 0 by decide, zero_mul]

lemma form_symm (s : ℕ) (u v : Space s) : form s u v = form s v u := by
  rw [form_apply, form_apply]
  apply sum_congr rfl
  intro a _
  ring

lemma form_nondegenerate (s : ℕ) : (form s).Nondegenerate := by
  have hleft (u : Space s) (hu : ∀ v, form s u v = 0) : u = 0 := by
    apply Prod.ext <;> apply funext
    · intro a
      have h := hu (0, Pi.single a 1)
      simpa [form_apply, Pi.single_apply, mul_ite] using h
    · intro a
      have h := hu (Pi.single a 1, 0)
      simpa [form_apply, Pi.single_apply, mul_ite] using h
  exact ⟨hleft, fun v hv => hleft v (fun u => (form_symm s v u).trans (hv u))⟩

lemma finrank (s : ℕ) : Module.finrank (ZMod 2) (Space s) = 2 * s := by
  rw [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin]
  omega

lemma card_space (s : ℕ) : Fintype.card (Space s) = 2 ^ (2 * s) := by
  simp only [Space, Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [← pow_add]
  congr 1
  omega

lemma card_alphabet (s : ℕ) : Fintype.card (Alphabet s) = 2 ^ (2 * s) - 1 := by
  have h := Fintype.card_congr (Equiv.optionSubtypeNe (0 : Space s))
  rw [Fintype.card_option, card_space] at h
  change Fintype.card {v : Space s // v ≠ 0} = _
  omega

end SmoothObstruction.WordAlphabet

end

section

open Filter Topology

namespace SmoothObstruction.WordParameters
open Filter Finset

noncomputable def logLevel (s₀ i : ℕ) : ℕ := ∑ j∈Finset.range i, K (sequence s₀ j)
noncomputable def testScales (s₀ i : ℕ) : Finset ℕ :=
  Finset.Icc (logLevel s₀ i+(K (sequence s₀ i)+15)/16)
    (logLevel s₀ i+K (sequence s₀ i)/8)

end SmoothObstruction.WordParameters

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_WordStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

namespace SmoothObstruction.ShiftComparisons
open Finset

/-- The exact first endpoint of a comparison against a length-N window in
uv. It also includes aligned different-word comparisons when t=0. -/
def first {M N : ℕ} (a b : Fin M) (t r : Fin N) : Fin M × Fin N :=
  (if r.val + t.val < N then a else b, r + t)
def second {M N : ℕ} (c : Fin M) (r : Fin N) : Fin M × Fin N := (c,r)

lemma first_injective {M N : ℕ} (a b : Fin M) (t : Fin N) :
    Function.Injective (first a b t) := by
  intro r s h
  have hh := congrArg Prod.snd h
  have hm : r.val + t.val ≡ s.val + t.val [MOD N] := congrArg Fin.val hh
  exact Fin.ext ((Nat.ModEq.add_right_cancel' t.val hm).eq_of_lt_of_lt r.isLt s.isLt)
lemma no_loops {M N : ℕ} [NeZero N] (a b c : Fin M) (t : Fin N)
    (h : t ≠ 0 ∨ a ≠ c) (r : Fin N) : first a b t r ≠ second c r := by
  intro he
  have hs : r + t = r := congrArg Prod.snd he
  have hm : r.val + t.val ≡ r.val + (0 : Fin N).val [MOD N] :=
    congrArg Fin.val (hs.trans (Fin.add_zero r).symm)
  have ht : t = 0 := Fin.ext ((Nat.ModEq.add_left_cancel' r.val hm).eq_of_lt_of_lt t.isLt (0 : Fin N).isLt)
  rcases h with h | h
  · exact h ht
  · subst t
    have ha := congrArg Prod.fst he
    have hr : r.val < N := r.isLt
    simp only [first, second, Fin.val_zero, add_zero, ite_eq_left hr] at ha
    exact h ha

/-- Only the at-most-three sampled words actually present are charged by the
probability bound, even when some input indices coincide. -/
def used {M : ℕ} (a b c : Fin M) : Finset (Fin M) := {a,b,c}

lemma used_nonempty {M : ℕ} (a b c : Fin M) : (used a b c).Nonempty := by
  exact ⟨a, by simp [used]⟩
lemma used_card {M : ℕ} (a b c : Fin M) : (used a b c).card ≤ 3 := by
  calc
    _ ≤ ({b,c} : Finset (Fin M)).card + 1 := card_insert_le _ _
    _ ≤ ({c} : Finset (Fin M)).card + 1 + 1 := Nat.add_le_add_right (card_insert_le _ _) 1
    _ = _ := by simp

noncomputable def firstUsed {M N : ℕ} (a b c : Fin M) (t r : Fin N) :
    {j : Fin M // j ∈ used a b c} × Fin N :=
  (⟨(first a b t r).1, by
    unfold first used
    split_ifs <;> simp⟩, (first a b t r).2)
def secondUsed {M N : ℕ} (a b c : Fin M) (r : Fin N) :
    {j : Fin M // j ∈ used a b c} × Fin N :=
  (⟨c, by simp [used]⟩,r)

lemma firstUsed_injective {M N : ℕ} (a b c : Fin M) (t : Fin N) :
    Function.Injective (firstUsed a b c t) := by
  intro r s h
  exact first_injective a b t (congrArg (fun z => (z.1.val,z.2)) h)
lemma secondUsed_injective {M N : ℕ} (a b c : Fin M) :
    Function.Injective (secondUsed (N := N) a b c) := by
  intro r s h
  exact congrArg Prod.snd h
lemma no_loops_used {M N : ℕ} [NeZero N] (a b c : Fin M) (t : Fin N)
    (h : t ≠ 0 ∨ a ≠ c) (r : Fin N) : firstUsed a b c t r ≠ secondUsed a b c r := by
  intro he
  exact no_loops a b c t h r (congrArg (fun z => (z.1.val,z.2)) he)

end SmoothObstruction.ShiftComparisons

namespace SmoothObstruction.ShiftComparisons
open Finset FiniteLaw
variable {A : Type*} [Fintype A] [DecidableEq A]

noncomputable def matchCount {M N : ℕ} (w : Fin M → Fin N → A) (a b c : Fin M) (t : Fin N) : ℕ :=
  (univ.filter (fun r => w (first a b t r).1 (first a b t r).2 = w c r)).card

/-- Source shifted-comparison probability, including coincidences among all
three selected sample-list indices. -/
theorem bad_probability {M N : ℕ} [NeZero N] (P : Law (Fin N → A))
    (a b c : Fin M) (t : Fin N) (h : t ≠ 0 ∨ a ≠ c) (d : ℕ) (hd : d ≤ N)
    {U : ℝ} (hU : 1 ≤ U) (hA : 1 ≤ (Fintype.card A : ℝ))
    (hP : ∀ w, P.mass w ≤ 2 * (U / Fintype.card A) ^ N) :
    prob (product (fun _ : Fin M => P)) (univ.filter (fun w => d ≤ matchCount w a b c t)) ≤
      8 * 2 ^ N * U ^ (3 * N) * (Fintype.card A : ℝ) ^ (-(d : ℝ) / 2) := by
  let J := {j : Fin M // j ∈ used a b c}
  have hc : 0 ≤ 2 * (U / Fintype.card A) ^ N := by positivity
  have hp := sampled_bad_comparison (fun _ : Fin M => P) (Subtype.val : J → Fin M)
    Subtype.val_injective (firstUsed a b c t) (secondUsed a b c)
    (firstUsed_injective a b c t) (secondUsed_injective a b c)
    (no_loops_used a b c t h) d hc (fun _ => hP)
  change prob _ (univ.filter (fun w => d ≤ matchCount w a b c t)) ≤ _ at hp
  have hj : 1 ≤ Fintype.card J := by
    simpa only [J, Fintype.card_coe] using Nat.succ_le_iff.mpr (used_nonempty a b c).card_pos
  have hj' : Fintype.card J ≤ 3 := by simpa only [J, Fintype.card_coe] using used_card a b c
  simp only [Fintype.card_fin] at hp
  exact hp.trans (comparison_cost hA hU hj hj' hd)

abbrev Config (M N : ℕ) [NeZero N] :=
  {z : Fin M × Fin M × Fin M × Fin N // z.2.2.2 ≠ 0 ∨ z.1 ≠ z.2.2.1}

lemma card_config (M N : ℕ) [NeZero N] : Fintype.card (Config M N) ≤ N * M ^ 3 := by
  have h := Fintype.card_subtype_le (fun z : Fin M × Fin M × Fin M × Fin N =>
    z.2.2.2 ≠ 0 ∨ z.1 ≠ z.2.2.1)
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

/-- Simultaneous bound for every aligned or shifted comparison in the actual
M-word sample. The finite index set has at most N M³ members. -/
theorem all_bad_probability {M N : ℕ} [NeZero N] (P : Law (Fin N → A))
    (d : ℕ) (hd : d ≤ N) {U : ℝ} (hU : 1 ≤ U) (hA : 1 ≤ (Fintype.card A : ℝ))
    (hP : ∀ w, P.mass w ≤ 2 * (U / Fintype.card A) ^ N) :
    prob (product (fun _ : Fin M => P))
      (univ.biUnion (fun z : Config M N => univ.filter (fun w =>
        d ≤ matchCount w z.val.1 z.val.2.1 z.val.2.2.1 z.val.2.2.2))) ≤
      (N * M ^ 3 : ℝ) * (8 * 2 ^ N * U ^ (3 * N) *
        (Fintype.card A : ℝ) ^ (-(d : ℝ) / 2)) := by
  let C := 8 * (2 : ℝ) ^ N * U ^ (3 * N) * (Fintype.card A : ℝ) ^ (-(d : ℝ) / 2)
  calc
    _ ≤ ∑ z : Config M N, prob (product (fun _ : Fin M => P))
      (univ.filter (fun w => d ≤ matchCount w z.val.1 z.val.2.1 z.val.2.2.1 z.val.2.2.2)) :=
        union_bound _ _
    _ ≤ ∑ _ : Config M N, C := sum_le_sum (fun z _ =>
      bad_probability P _ _ _ _ z.property d hd hU hA hP)
    _ = Fintype.card (Config M N) * C := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card_config M N) (by dsimp [C]; positivity)

end SmoothObstruction.ShiftComparisons

namespace SmoothObstruction.WordFamily
open Finset FiniteLaw ShiftComparisons
variable {A C I : Type*} [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
  [Fintype I]

noncomputable def observableLaw {N : ℕ} (P : Law (Fin N → A)) (f : (Fin N → A) → C) (c : C) : ℝ :=
  expect P (fun w => if f w = c then 1 else 0)

noncomputable def empiricalTV {M N : ℕ} (P : Law (Fin N → A)) (f : (Fin N → A) → C)
    (w : Fin M → Fin N → A) : ℝ :=
  (1/2 : ℝ) * ∑ c, |(∑ i, if f (w i) = c then (1 : ℝ) else 0) / M - observableLaw P f c|

omit [DecidableEq A] in
lemma empiricalTV_nonneg {M N : ℕ} (P : Law (Fin N → A)) (f : (Fin N → A) → C)
    (w : Fin M → Fin N → A) : 0 ≤ empiricalTV P f w := by
  unfold empiricalTV; positivity

omit [DecidableEq A] in
lemma expectedTV {M N : ℕ} [NeZero M] (P : Law (Fin N → A)) (f : (Fin N → A) → C) :
    expect (product (fun _ : Fin M => P)) (empiricalTV P f) ≤
      (1/2 : ℝ) * Real.sqrt (Fintype.card C / M) := by
  unfold empiricalTV
  simpa only [Fintype.card_fin] using independent_vectors_tv
    (fun _ : Fin M => P) (fun _ w c => if f w = c then (1 : ℝ) else 0)
    (observableLaw P f) (by intros; positivity) (by intros; simp) (by intros; rfl)

lemma window_bad_probability {M N : ℕ} [NeZero M] (P : Law (Fin N → A))
    (f : I → (Fin N → A) → C) {θ : ℝ} (hθ : 0 < θ) :
    prob (product (fun _ : Fin M => P))
      (univ.biUnion (fun i => univ.filter (fun w => θ < empiricalTV P (f i) w))) ≤
        Fintype.card I * ((1/2 : ℝ) * Real.sqrt (Fintype.card C / M)) / θ := by
  classical
  calc
    _ ≤ ∑ i, prob (product (fun _ : Fin M => P))
      (univ.filter (fun w => θ < empiricalTV P (f i) w)) := union_bound _ _
    _ ≤ ∑ _ : I, ((1/2 : ℝ) * Real.sqrt (Fintype.card C / M)) / θ :=
      sum_le_sum (fun i _ => (markov _ _ (empiricalTV_nonneg P (f i)) hθ).trans
        (div_le_div_of_nonneg_right (expectedTV P (f i)) hθ.le))
    _ = _ := by simp [mul_div_assoc]

omit [Fintype C] [DecidableEq C] [Fintype I] [DecidableEq A] in
lemma product_support {M N : ℕ} (P : Law (Fin N → A))
    {w : Fin M → Fin N → A} (hw : 0 < (product (fun _ : Fin M => P)).mass w) (i : Fin M) :
    0 < P.mass (w i) := by
  have hn : P.mass (w i) ≠ 0 := by
    intro hz
    have hp : (∏ j, P.mass (w j)) = 0 := prod_eq_zero (mem_univ i) hz
    exact (ne_of_gt hw) hp
  exact lt_of_le_of_ne (P.nonneg (w i)) hn.symm

omit [Fintype C] [DecidableEq C] [Fintype I] [Fintype A] in
lemma injective_of_separation {M N d : ℕ} [NeZero N] {w : Fin M → Fin N → A} (hd : d ≤ N)
    (hsep : ∀ a b c : Fin M, ∀ t : Fin N, t ≠ 0 ∨ a ≠ c → matchCount w a b c t < d) :
    Function.Injective w := by
  intro a c he
  by_contra hac
  have hb := hsep a a c 0 (Or.inr hac)
  have hmc : matchCount w a a c 0 = N := by
    unfold matchCount
    have hall (r : Fin N) : w (first a a 0 r).1 (first a a 0 r).2 = w c r := by
      simp [first, he]
    simp [hall]
  omega

/-- Actual simultaneous family selection. The two bad events are evaluated
in one product law and support is preserved for each complete list. -/
theorem exists_family {M N d : ℕ} [NeZero M] [NeZero N]
    (P : Law (Fin N → A)) (f : I → (Fin N → A) → C)
    {U θ : ℝ} (hU : 1 ≤ U) (hA : 1 ≤ (Fintype.card A : ℝ)) (hθ : 0 < θ)
    (hd : d ≤ N) (hP : ∀ w, P.mass w ≤ 2 * (U / Fintype.card A) ^ N)
    (hwindow : Fintype.card I * ((1/2 : ℝ) * Real.sqrt (Fintype.card C / M)) / θ < 1/4)
    (hdistance : (N * M ^ 3 : ℝ) * (8 * 2 ^ N * U ^ (3 * N) *
      (Fintype.card A : ℝ) ^ (-(d : ℝ) / 2)) < 1/4) :
    ∃ w : Fin M → Fin N → A, Function.Injective w ∧
      (∀ i, 0 < P.mass (w i)) ∧
      (∀ i, empiricalTV P (f i) w ≤ θ) ∧
      ∀ a b c : Fin M, ∀ t : Fin N, t ≠ 0 ∨ a ≠ c → matchCount w a b c t < d := by
  classical
  let E₀ := univ.biUnion (fun i => univ.filter (fun w : Fin M → Fin N → A => θ < empiricalTV P (f i) w))
  let E₁ := univ.biUnion (fun z : Config M N => univ.filter (fun w : Fin M → Fin N → A =>
    d ≤ matchCount w z.val.1 z.val.2.1 z.val.2.2.1 z.val.2.2.2))
  let E : Bool → Finset (Fin M → Fin N → A) := fun b => if b then E₁ else E₀
  have he₀ : prob (product (fun _ : Fin M => P)) E₀ < 1/4 :=
    (window_bad_probability P f hθ).trans_lt hwindow
  have he₁ : prob (product (fun _ : Fin M => P)) E₁ < 1/4 :=
    (all_bad_probability P d hd hU hA hP).trans_lt hdistance
  have hsum : (∑ b, prob (product (fun _ : Fin M => P)) (E b)) < 1 := by
    simp only [E, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
    linarith
  obtain ⟨w,hw,havoid⟩ := exists_good (product (fun _ : Fin M => P)) E hsum
  have hw₀ : w ∉ E₀ := havoid false
  have hw₁ : w ∉ E₁ := havoid true
  have hsep : ∀ a b c : Fin M, ∀ t : Fin N, t ≠ 0 ∨ a ≠ c → matchCount w a b c t < d := by
    intro a b c t h
    by_contra hn
    exact hw₁ (mem_biUnion.mpr ⟨⟨(a,b,c,t),h⟩,mem_univ _,mem_filter.mpr ⟨mem_univ _,show d ≤ matchCount w a b c t from by omega⟩⟩)
  refine ⟨w,injective_of_separation hd hsep,product_support P hw,?_,hsep⟩
  intro i
  by_contra hn
  exact hw₀ (mem_biUnion.mpr ⟨i,mem_univ i,mem_filter.mpr ⟨mem_univ _,by linarith⟩⟩)

end SmoothObstruction.WordFamily

namespace SmoothObstruction.FiniteLaw
open Finset
variable {A B : Type*} [Fintype A] [Fintype B]
noncomputable def transport (e : A ≃ B) (P : Law A) : Law B where
  mass b := P.mass (e.symm b)
  nonneg b := P.nonneg (e.symm b)
  total := (e.symm.sum_comp P.mass).trans P.total

end SmoothObstruction.FiniteLaw

namespace SmoothObstruction.WordFlatten
open Finset FiniteLaw WordLaw SequentialLaw
variable {A : Type*} {q H : ℕ}

def flattenEquiv : (Fin q → Fin H → A) ≃ (Fin (q*H) → A) where
  toFun w i := w (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  invFun w b r := w (finProdFinEquiv (b,r))
  left_inv w := by funext b r; simp
  right_inv w := by
    funext i
    change w (finProdFinEquiv (finProdFinEquiv.symm i)) = w i
    rw [Equiv.apply_symm_apply]

lemma full_test [Fintype A] [DecidableEq A] (v w : Fin q → Fin H → A) :
    (∏ b, test (fun r => some (v b r)) (w b)) = if w = v then 1 else 0 := by
  classical
  have ht (b : Fin q) : test (fun r => some (v b r)) (w b) =
      if w b = v b then 1 else 0 := by
    rw [test_eq_indicator]
    congr 1
    simp only [Option.some.injEq, funext_iff]
    apply propext
    constructor
    · intro h i
      exact h i _ rfl
    · intro h i a ha
      exact (h i).trans ha
  simp only [ht, Finset.prod_boole, mem_univ, forall_const, ← funext_iff]

lemma expect_full_test [Fintype A] [DecidableEq A] (P : Law (Fin q → Fin H → A))
    (v : Fin q → Fin H → A) :
    expect P (fun w => ∏ b, test (fun r => some (v b r)) (w b)) = P.mass v := by
  classical
  simp [full_test, FiniteLaw.expect, mul_ite]

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [Fintype V] [DecidableEq V] (B : LinearMap.BilinForm (ZMod 2) V) {K : ℕ}

/-- Pointwise mass of the true constrained and once-conditioned complete
list. This is derived from the arbitrary sublist estimate, not independence
of constituent positions. -/
lemma conditioned_mass (hd : K+1 ≤ Module.finrank (ZMod 2) V) (hK : 1 ≤ K)
    (E : Finset (Fin q → Fin H → {v : V // v ≠ 0}))
    (hE : 1/2 ≤ prob (rawLaw B hd H q) E) (v : Fin q → Fin H → {v : V // v ≠ 0}) :
    (condition (rawLaw B hd H q) E (by change 0 < prob _ E; linarith)).mass v ≤
      2 * ((2 : ℝ) ^ (2*K) / Fintype.card {v : V // v ≠ 0}) ^ (q*H) := by
  have h := conditioned_sublist B hd hK E hE (fun b r => some (v b r))
  rw [expect_full_test] at h
  simpa using h

noncomputable def flatLaw (hd : K+1 ≤ Module.finrank (ZMod 2) V)
    (E : Finset (Fin q → Fin H → {v : V // v ≠ 0}))
    (hE : 1/2 ≤ prob (rawLaw B hd H q) E) : Law (Fin (q*H) → {v : V // v ≠ 0}) :=
  transport flattenEquiv (condition (rawLaw B hd H q) E (by change 0 < prob _ E; linarith))

lemma flat_mass (hd : K+1 ≤ Module.finrank (ZMod 2) V) (hK : 1 ≤ K)
    (E : Finset (Fin q → Fin H → {v : V // v ≠ 0}))
    (hE : 1/2 ≤ prob (rawLaw B hd H q) E) (v : Fin (q*H) → {v : V // v ≠ 0}) :
    (flatLaw B hd E hE).mass v ≤
      2 * ((2 : ℝ) ^ (2*K) / Fintype.card {v : V // v ≠ 0}) ^ (q*H) :=
  conditioned_mass B hd hK E hE _

lemma flat_support (hd : K+1 ≤ Module.finrank (ZMod 2) V)
    (E : Finset (Fin q → Fin H → {v : V // v ≠ 0}))
    (hE : 1/2 ≤ prob (rawLaw B hd H q) E) {v : Fin (q*H) → {v : V // v ≠ 0}}
    (hv : 0 < (flatLaw B hd E hE).mass v) :
    flattenEquiv.symm v ∈ E ∧ 0 < (rawLaw B hd H q).mass (flattenEquiv.symm v) := by
  exact condition_supported (rawLaw B hd H q) E (by linarith) hv

lemma flat_relations (hd : K+1 ≤ Module.finrank (ZMod 2) V)
    (E : Finset (Fin q → Fin H → {v : V // v ≠ 0}))
    (hE : 1/2 ≤ prob (rawLaw B hd H q) E) {v : Fin (q*H) → {v : V // v ≠ 0}}
    (hv : 0 < (flatLaw B hd E hE).mass v) (b : Fin q)
    {r k : ℕ} (hk : k < K) (hk8 : k ≤ K/8) (hrt : r+2^k < H) :
    B (v (finProdFinEquiv (b,⟨r,lt_trans (Nat.lt_add_of_pos_right (by positivity)) hrt⟩))).val
      (v (finProdFinEquiv (b,⟨r+2^k,hrt⟩))).val = 0 :=
  raw_relations B hd (flat_support B hd E hE hv).2 b hk hk8 hrt

/-- Complete supported family selection for the actual grouped symplectic
sampler. Caller-specified observables encode the short windows, while E is
the proved per-word approximation event. -/
theorem exists_family {M d : ℕ} [NeZero M] [NeZero (q*H)]
    {C I : Type*} [Fintype C] [DecidableEq C] [Fintype I]
    (hd : K+1 ≤ Module.finrank (ZMod 2) V) (hK : 1 ≤ K)
    (hA : 1 ≤ (Fintype.card {v : V // v ≠ 0} : ℝ))
    (E : Finset (Fin q → Fin H → {v : V // v ≠ 0}))
    (hE : 1/2 ≤ prob (rawLaw B hd H q) E)
    (f : I → (Fin (q*H) → {v : V // v ≠ 0}) → C)
    {θ : ℝ} (hθ : 0 < θ) (hmatch : d ≤ q*H)
    (hwindow : Fintype.card I * ((1/2 : ℝ) * Real.sqrt (Fintype.card C / M)) / θ < 1/4)
    (hdistance : ((q*H) * M^3 : ℝ) * (8 * 2^(q*H) * ((2 : ℝ)^(2*K))^(3*(q*H)) *
      (Fintype.card {v : V // v ≠ 0} : ℝ)^(-(d : ℝ)/2)) < 1/4) :
    ∃ w : Fin M → Fin (q*H) → {v : V // v ≠ 0}, Function.Injective w ∧
      (∀ i, flattenEquiv.symm (w i) ∈ E) ∧
      (∀ i b (r k : ℕ) (_hk : k<K) (_hk8 : k ≤ K/8) (hr : r+2^k<H),
        B (w i (finProdFinEquiv (b,⟨r,lt_trans (Nat.lt_add_of_pos_right (by positivity)) hr⟩))).val
          (w i (finProdFinEquiv (b,⟨r+2^k,hr⟩))).val = 0) ∧
      (∀ i, WordFamily.empiricalTV (flatLaw B hd E hE) (f i) w ≤ θ) ∧
      ∀ a b c : Fin M, ∀ t : Fin (q*H), t≠0 ∨ a≠c → ShiftComparisons.matchCount w a b c t < d := by
  obtain ⟨w,hinj,hsupp,htv,hsep⟩ := WordFamily.exists_family
    (flatLaw B hd E hE) f (by exact one_le_pow₀ (by norm_num)) hA hθ hmatch
    (flat_mass B hd hK E hE) hwindow (by simpa only [Nat.cast_mul] using hdistance)
  exact ⟨w,hinj,fun i => (flat_support B hd E hE (hsupp i)).1,
    fun i b _ _ hk hk8 hr => flat_relations B hd E hE (hsupp i) b hk hk8 hr,htv,hsep⟩
end SmoothObstruction.WordFlatten

end

section

namespace SmoothObstruction.WordStep
open WordParameters WordAlphabet FiniteLaw WordLaw
open scoped BigOperators

instance alphabetFintype (s : ℕ) : Fintype (Alphabet s) := inferInstance
instance alphabetDecidableEq (s : ℕ) : DecidableEq (Alphabet s) := inferInstance

noncomputable def N (s : ℕ) := 2 ^ K s
noncomputable def H (s : ℕ) := 2 ^ (K s / 2)
noncomputable def q (s : ℕ) := 2 ^ (K s - K s / 2)
noncomputable def D (s : ℕ) := 2 ^ (K s / 8)
lemma q_mul_H (s : ℕ) : q s * H s = N s := by
  simp only [q,H,N,←pow_add,Nat.sub_add_cancel (Nat.div_le_self (K s) 2)]
lemma N_pos (s : ℕ) : 0 < N s := by unfold N; positivity
lemma H_pos (s : ℕ) : 0 < H s := by unfold H; positivity
lemma q_pos (s : ℕ) : 0 < q s := by unfold q; positivity
instance qH_neZero (s : ℕ) : NeZero (q s*H s) := ⟨(mul_pos (q_pos s) (H_pos s)).ne'⟩
lemma cardAlphabetReal (s : ℕ) : (Fintype.card (Alphabet s) : ℝ) = alphabetSize s := by
  rw [card_alphabet,Nat.cast_sub (Nat.one_le_two_pow),Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  rfl
lemma epsilon_le_one (i : ℕ) : epsilon i ≤ 1 := by
  unfold epsilon
  exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))

noncomputable def matchThreshold (i s : ℕ) := ⌈epsilon i * N s⌉₊
lemma matchThreshold_le (i s : ℕ) : matchThreshold i s ≤ N s := by
  apply Nat.ceil_le.mpr
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (epsilon_le_one i) (Nat.cast_nonneg (N s))
lemma le_matchThreshold (i s : ℕ) : epsilon i * N s ≤ matchThreshold i s := Nat.le_ceil _

/-- Actual offset set for nonwrapping source D-windows. -/
abbrev Offsets (s : ℕ) := {t : Fin (q s * H s) // t.val+D s ≤ q s*H s}
def window (s : ℕ) (t : Offsets s) (w : Fin (q s*H s) → Alphabet s) : Fin (D s) → Alphabet s :=
  fun r => w ⟨t.val.val + r.val,lt_of_lt_of_le (Nat.add_lt_add_left r.isLt _) t.property⟩
lemma card_offsets (s : ℕ) : Fintype.card (Offsets s) ≤ N s := by
  exact (Fintype.card_subtype_le _).trans_eq (by simp [q_mul_H])

lemma window_budget {i s : ℕ} (hk : 256 ≤ K s) (hε : 32 ≤ epsilon i * K s) :
    (Fintype.card (Offsets s) : ℝ) * ((1/2:ℝ) * Real.sqrt
      (Fintype.card (Fin (D s) → Alphabet s) / Fintype.card (Alphabet (nextS i s)))) / (1/10000) < 1/4 := by
  have hc : (Fintype.card (Offsets s) : ℝ) ≤ (N s : ℝ) := by exact_mod_cast card_offsets s
  have hcard : (Fintype.card (Fin (D s) → Alphabet s) : ℝ) = alphabetSize s ^ D s := by
    simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,cardAlphabetReal]
  rw [hcard,cardAlphabetReal]
  have hsqrt : 0 ≤ Real.sqrt (alphabetSize s ^ D s / alphabetSize (nextS i s)) := Real.sqrt_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hc hsqrt
  have hn : (N s : ℝ) = (2 : ℝ)^K s := by simp only [N,Nat.cast_pow,Nat.cast_ofNat]
  have hbound := (actual_budgets hk hε).2.1
  unfold windowBudget at hbound
  rw [←hn] at hbound
  change _ < (1/4:ℝ)
  dsimp [D] at *
  nlinarith

lemma distance_budget {i s : ℕ} (hk : 256 ≤ K s) (hε : 32 ≤ epsilon i * K s) :
    ((q s*H s) * (Fintype.card (Alphabet (nextS i s)))^3 : ℝ) *
      (8 * 2^(q s*H s) * ((2:ℝ)^(2*K s))^(3*(q s*H s)) *
        (Fintype.card (Alphabet s) : ℝ)^(-(matchThreshold i s : ℝ)/2)) < 1/4 := by
  have hs : 1 ≤ s := s_pos_of_Kpos (by omega)
  have ht : 1 ≤ nextS i s := s_pos_of_Kpos (by have := one_step_growth hk hε; omega)
  have hA : 1 ≤ alphabetSize s := by
    have hp : (2 : ℝ)^(2:ℕ) ≤ (2:ℝ)^(2*s) := pow_le_pow_right₀ (by norm_num) (by omega)
    unfold alphabetSize
    norm_num at hp
    linarith
  have hexp : -(matchThreshold i s : ℝ)/2 ≤ -epsilon i * N s/2 := by
    have := le_matchThreshold i s
    linarith
  have hr := Real.rpow_le_rpow_of_exponent_le hA hexp
  have hpow : (2 : ℝ)^(N s) * ((2:ℝ)^(2*K s))^(3*N s) =
      (2:ℝ)^((6*K s+1)*N s) := by
    rw [←pow_mul,←pow_add]
    congr 1
    ring
  rw [q_mul_H,cardAlphabetReal,cardAlphabetReal,←Nat.cast_mul,q_mul_H]
  have hm : 0 ≤ (N s : ℝ) * alphabetSize (nextS i s)^3 :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (alphabetSize_pos ht).le _)
  have hm' : 0 ≤ 8*(2:ℝ)^((6*K s+1)*N s) := by positivity
  have hle := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr hm') hm
  have hn : (N s : ℝ) = (2:ℝ)^K s := by simp only [N,Nat.cast_pow,Nat.cast_ofNat]
  have hbound := (actual_budgets hk hε).2.2
  unfold distanceBudget at hbound
  rw [←hn] at hbound
  have heq : 8*(2:ℝ)^N s*((2:ℝ)^(2*K s))^(3*N s) = 8*(2:ℝ)^((6*K s+1)*N s) := by
    rw [mul_assoc,hpow]
  rw [heq]
  change _ < (1/4:ℝ)
  dsimp only [N] at *
  have hnn := mul_nonneg hm (mul_nonneg hm'
    (Real.rpow_nonneg (by positivity : 0 ≤ alphabetSize s) (-epsilon i * (N s : ℝ)/2)))
  nlinarith

lemma alphabetSize_ge_one {s : ℕ} (hs : 1 ≤ s) : 1 ≤ alphabetSize s := by
  have hp : (2:ℝ)^(2:ℕ) ≤ (2:ℝ)^(2*s) := pow_le_pow_right₀ (by norm_num) (by omega)
  unfold alphabetSize
  norm_num at hp
  linarith

/-- One actual finite-family selection at the exact source parameters.
No distance, injectivity, window law or symplectic relation is an assumption;
they are all supplied by the independent sample argument and checked budgets.
The single per-word conditioning event is passed with its proved mass bound. -/
theorem exists_step {i s : ℕ} (hk : 256 ≤ K s) (hε : 32 ≤ epsilon i * K s)
    (E : Finset (Fin (q s) → Fin (H s) → Alphabet s))
    (hE : 1/2 ≤ prob (rawLaw (form s) (by rw [finrank]; exact dimension_budget hk) (H s) (q s)) E) :
    ∃ w : Fin (Fintype.card (Alphabet (nextS i s))) → Fin (q s*H s) → Alphabet s,
      Function.Injective w ∧
      (∀ a, WordFlatten.flattenEquiv.symm (w a) ∈ E) ∧
      (∀ a b (r k : ℕ) (_hk : k<K s) (_hk8 : k ≤ K s/8) (hr : r+2^k<H s),
        form s (w a (finProdFinEquiv (b,⟨r,lt_trans (Nat.lt_add_of_pos_right (by positivity)) hr⟩))).val
          (w a (finProdFinEquiv (b,⟨r+2^k,hr⟩))).val = 0) ∧
      (∀ t, WordFamily.empiricalTV
        (WordFlatten.flatLaw (form s) (by rw [finrank]; exact dimension_budget hk) E hE)
        (window s t) w ≤ 1/10000) ∧
      ∀ a b c, ∀ t : Fin (q s*H s), t≠0 ∨ a≠c →
        ShiftComparisons.matchCount w a b c t < matchThreshold i s := by
  have hnext : 1 ≤ nextS i s := s_pos_of_Kpos (by have := one_step_growth hk hε; omega)
  have hcard : 0 < Fintype.card (Alphabet (nextS i s)) := by
    have hh : (0:ℝ) < Fintype.card (Alphabet (nextS i s)) := by
      rw [cardAlphabetReal]; exact alphabetSize_pos hnext
    exact_mod_cast hh
  let : NeZero (Fintype.card (Alphabet (nextS i s))) := ⟨hcard.ne'⟩
  let : NeZero (q s*H s) := ⟨(mul_pos (q_pos s) (H_pos s)).ne'⟩
  apply WordFlatten.exists_family (form s)
    (by rw [finrank]; exact dimension_budget hk) (by omega)
    (by rw [cardAlphabetReal]; exact alphabetSize_ge_one (s_pos_of_Kpos (by omega)))
    E hE (window s) (by norm_num)
    (by rw [q_mul_H]; exact matchThreshold_le i s)
    (window_budget hk hε) (distance_budget hk hε)

/-- At successive exact source levels the per-word approximation event
has probability at least a half, for every actual previous-window map. -/
theorem approximation_mass {i s : ℕ} (hk : 256 ≤ K s) (hε : 32 ≤ epsilon i * K s)
    (f : Offsets s → Alphabet (nextS i s) → (Fin (D s) → Alphabet s)) :
    1/2 ≤ prob (rawLaw (form (nextS i s))
      (by rw [finrank]; exact dimension_budget (by have := one_step_growth hk hε; omega))
      (H (nextS i s)) (q (nextS i s)))
      (Finset.univ.filter (fun w => ∀ t, tvFromUniformObservable (f t) w ≤ 1/10000)) := by
  apply approximation_event _ (form_alt _) (form_nondegenerate _) _
    (H_pos _) (q_pos _) f (by norm_num)
  have hc : (Fintype.card (Offsets s) : ℝ) ≤ (N s : ℝ) := by exact_mod_cast card_offsets s
  have hcard : (Fintype.card (Fin (D s) → Alphabet s) : ℝ) = alphabetSize s ^ D s := by
    simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,cardAlphabetReal]
  rw [hcard]
  have hmul := mul_le_mul_of_nonneg_right hc
    (Real.sqrt_nonneg (alphabetSize s ^ D s / q (nextS i s)))
  have hbound := (actual_budgets hk hε).1
  unfold filterBudget at hbound
  simp only [N,q,D,Nat.cast_pow,Nat.cast_ofNat] at *
  nlinarith
end SmoothObstruction.WordStep

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_WordHierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SmoothObstruction.WordHierarchy
open WordParameters WordAlphabet WordStep FiniteLaw WordLaw
open scoped BigOperators

noncomputable abbrev S (i : ℕ) := sequence 40000 i
abbrev A (i : ℕ) := Alphabet (S i)
noncomputable abbrev size (i : ℕ) := Fintype.card (A i)
noncomputable abbrev groupLength (i : ℕ) := q (S i)*H (S i)
noncomputable abbrev Config (i : ℕ) := Fin (q (S i)) → Fin (H (S i)) → A i
noncomputable abbrev Labels (i : ℕ) := Fin (groupLength i) → A i
noncomputable abbrev goodDim (i : ℕ) : K (S i)+1 ≤ Module.finrank (ZMod 2) (WordAlphabet.Space (S i)) := by
  rw [finrank]
  exact dimension_budget (step_conditions initial_threshold i).1
noncomputable abbrev raw (i : ℕ) := rawLaw (form (S i)) (goodDim i) (H (S i)) (q (S i))

/-- The chosen family stores the actual conditioning event and its mass,
not merely the existence of enough labels. -/
structure Family (i : ℕ) where
  E : Finset (Config i)
  massE : 1/2 ≤ prob (raw i) E
  w : Fin (size (i+1)) → Labels i
  injective : Function.Injective w
  supported : ∀ a, WordFlatten.flattenEquiv.symm (w a) ∈ E
  relations : ∀ a b (r k : ℕ) (_hk : k<K (S i)) (_hk8 : k ≤ K (S i)/8) (hr : r+2^k<H (S i)),
    form (S i) (w a (finProdFinEquiv (b,⟨r,lt_trans (Nat.lt_add_of_pos_right (by positivity)) hr⟩))).val
      (w a (finProdFinEquiv (b,⟨r+2^k,hr⟩))).val = 0
  windowTV : ∀ t, WordFamily.empiricalTV
    (WordFlatten.flatLaw (form (S i)) (goodDim i) E massE)
    (window (S i) t) w ≤ 1/10000
  separated : ∀ a b c, ∀ t : Fin (groupLength i), t≠0 ∨ a≠c →
    ShiftComparisons.matchCount w a b c t < matchThreshold i (S i)

noncomputable def chooseFamily (i : ℕ) (E : Finset (Config i))
    (hE : 1/2 ≤ prob (raw i) E) : Family i := by
  classical
  have hx := exists_step (step_conditions initial_threshold i).1
    (step_conditions initial_threshold i).2 E hE
  let w := Classical.choose hx
  have hw := Classical.choose_spec hx
  exact ⟨E,hE,w,hw.1,hw.2.1,hw.2.2.1,hw.2.2.2.1,hw.2.2.2.2⟩

noncomputable def Family.word {i : ℕ} (F : Family i) (a : A (i+1)) : Labels i :=
  F.w ((Fintype.equivFin (A (i+1))) a)

lemma Family.word_injective {i : ℕ} (F : Family i) : Function.Injective F.word :=
  F.injective.comp (Fintype.equivFin (A (i+1))).injective

noncomputable def stage : (i : ℕ) → Family i
  | 0 => chooseFamily 0 Finset.univ (by norm_num [prob,FiniteLaw.Law.total])
  | i+1 => by
    classical
    let f := fun t a => window (S i) t ((stage i).word a)
    let E := Finset.univ.filter (fun w : Config (i+1) => ∀ t, tvFromUniformObservable (f t) w ≤ 1/10000)
    have hE : 1/2 ≤ prob (raw (i+1)) E :=
      approximation_mass (step_conditions initial_threshold i).1
        (step_conditions initial_threshold i).2 f
    exact chooseFamily (i+1) E hE

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.WordConcatenation
variable {A B : Type*} {m N : ℕ}

def pack : Fin N × Fin m ≃ Fin (m*N) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm N m))

def concat (u : B → Fin m → A) (w : Fin N → B) : Fin (m*N) → A :=
  fun j => u (w (pack.symm j).1) (pack.symm j).2

@[simp] lemma concat_pack (u : B → Fin m → A) (w : Fin N → B) (b : Fin N) (r : Fin m) :
    concat u w (pack (b,r)) = u (w b) r := by simp [concat]

lemma concat_injective (u : B → Fin m → A) (hu : Function.Injective u) :
    Function.Injective (concat (N:=N) u) := by
  intro w v hw
  funext b
  apply hu
  funext r
  have hh := congrFun hw (pack (b,r))
  simpa only [concat_pack] using hh

end SmoothObstruction.WordConcatenation

namespace SmoothObstruction.WordHierarchy
open WordParameters WordStep WordConcatenation

noncomputable def children (i : ℕ) (a : A (i+1)) : Fin (N (S i)) → A i :=
  fun j => (stage i).word a ((finCongr (q_mul_H (S i))).symm j)

lemma children_injective (i : ℕ) : Function.Injective (children i) := by
  intro a b hab
  apply (stage i).word_injective
  funext j
  have hh := congrFun hab ((finCongr (q_mul_H (S i))) j)
  simpa only [children,Equiv.symm_apply_apply] using hh

/-- Source words have exactly the recursively prescribed lengths, over the
fixed initial alphabet. Reindexing is the fixed arbitrary labeling allowed
by the manuscript, not a new conditioning at any level. -/
noncomputable def word : (i : ℕ) → A i → Fin (length 40000 i) → A 0
  | 0,a,_ => a
  | i+1,a,j => concat (word i) (children i a) j

lemma word_injective (i : ℕ) : Function.Injective (word i) := by
  induction i with
  | zero =>
    intro a b hab
    exact congrFun hab ⟨0,by simp [length]⟩
  | succ i ih =>
    exact (concat_injective (word i) ih).comp (children_injective i)

noncomputable def words (i : ℕ) : Set (Fin (length 40000 i) → A 0) := Set.range (word i)

lemma alphabet_nonempty (i : ℕ) : Nonempty (A i) := by
  have hs := s_pos_of_Kpos (show 0<K (S i) by
    change 0<K (sequence 40000 i)
    have := (step_conditions initial_threshold i).1
    omega)
  have hp : (0 : ℝ) < Fintype.card (A i) := by
    rw [cardAlphabetReal]
    exact alphabetSize_pos hs
  exact Fintype.card_pos_iff.mp (by exact_mod_cast hp)

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.PhaseDynamics
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
  (m : ℕ → ℕ) [∀ i, NeZero (m i)] (hm : ∀ i, m i ∣ m (i+1))
  (W : ∀ i, Set (Fin (m i) → A))

/-- The exact concatenation property of legal source words, expressed at
all aligned lower-word positions. -/
def SubwordClosed : Prop :=
  ∀ i (w : Fin (m (i+1)) → A), w ∈ W (i+1) → ∀ r : ℕ,
    m i ∣ r → ∀ hr : r+m i ≤ m (i+1),
    (fun j : Fin (m i) => w ⟨r+j.val,lt_of_lt_of_le (Nat.add_lt_add_left j.isLt r) hr⟩) ∈ W i

/-- Periodic repetition is used solely as a finite-admissibility witness;
it is not the ergodic measure ultimately selected. -/
def repeatWord (n : ℕ) (w : Fin (m n) → A) : Space A m :=
  (fun t => w ⟨(t : ZMod (m n)).val,ZMod.val_lt _⟩,fun _ => 0)

end SmoothObstruction.PhaseDynamics

namespace SmoothObstruction.WordHierarchy
open WordParameters WordStep WordConcatenation MeasureTheory

noncomputable instance lengthNeZero (i : ℕ) : NeZero (length 40000 i) :=
  ⟨(length_pos 40000 i).ne'⟩

/-- The compact source extension is nonvacuous for the actual balanced,
shift-separated, symplectically constrained recursively selected hierarchy. -/
noncomputable abbrev Extension := PhaseDynamics.extension (length 40000) (length_dvd 40000) words

noncomputable instance initialNonempty : Nonempty (A 0) := alphabet_nonempty 0

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.PhaseDynamics
open MeasureTheory Set Finset
section Window
variable {A : Type*} [TopologicalSpace A] 
  [MeasurableSpace A] [MeasurableSingletonClass A] (m : ℕ → ℕ)
  [∀ i, NeZero (m i)]

/-- The actual symbol word containing the origin, not an independently
assigned label. Its starting time is minus the finite phase representative. -/
def containingWord (x : Space A m) (i : ℕ) : Fin (m i) → A :=
  wordAt m x i (-((x.2 i).val : ℤ))

omit [TopologicalSpace A] [MeasurableSingletonClass A] in
lemma measurable_containingWord (i : ℕ) : Measurable (fun x : Space A m => containingWord m x i) := by
  refine measurable_pi_iff.mpr (fun j => ?_)
  have he : Measurable (fun p : (ℤ → A) × ℤ => p.1 p.2) :=
    measurable_from_prod_countable_left (fun t => measurable_pi_apply t)
  have hi : Measurable (fun x : Space A m => -((x.2 i).val : ℤ)+(j.val : ℤ)) := by
    exact (measurable_of_countable (fun a : ZMod (m i) => -(a.val : ℤ)+(j.val : ℤ))).comp
      ((measurable_pi_apply i).comp measurable_snd)
  exact he.comp (measurable_fst.prodMk hi)

end Window
end SmoothObstruction.PhaseDynamics

namespace SmoothObstruction.WordHierarchy
open WordParameters WordStep WordConcatenation MeasureTheory Set

noncomputable abbrev T : Extension ≃ₜ Extension :=
  PhaseDynamics.extensionShift (length 40000) (length_dvd 40000) words

lemma containingWord_legal (i : ℕ) (x : Extension) :
    PhaseDynamics.containingWord (length 40000) x.val i ∈ words i := by
  apply (x.property i).2
  simp only [Int.cast_neg,Int.cast_natCast,ZMod.natCast_zmod_val]

/-- The actual legal word containing the origin, read as its unique selected
level label. This is a function of the symbolic configuration, not added data. -/
noncomputable def label (i : ℕ) (x : Extension) : A i :=
  Classical.choose (containingWord_legal i x)

lemma word_label (i : ℕ) (x : Extension) :
    word i (label i x)=PhaseDynamics.containingWord (length 40000) x.val i :=
  Classical.choose_spec (containingWord_legal i x)

lemma measurable_label (i : ℕ) : Measurable (label i) := by
  let : Nonempty (A i) := alphabet_nonempty i
  have he : label i = (Function.invFun (word i)) ∘
      (fun x : Extension => PhaseDynamics.containingWord (length 40000) x.val i) := by
    funext x
    simp only [Function.comp_apply,←word_label]
    exact ((Function.leftInverse_invFun (word_injective i)) (label i x)).symm
  rw [he]
  exact (measurable_of_countable _).comp
    ((PhaseDynamics.measurable_containingWord (length 40000) i).comp measurable_subtype_coe)


/-- The slot of the containing selected child inside the containing parent. -/
noncomputable def slot (i : ℕ) (x : Extension) : Fin (N (S i)) :=
  ⟨(x.val.2 (i+1)).val / length 40000 i,by
    apply (Nat.div_lt_iff_lt_mul (length_pos 40000 i)).mpr
    simpa only [length,N,S,Nat.mul_comm] using ZMod.val_lt (x.val.2 (i+1))⟩

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.Alignment
open MeasureTheory Set Finset
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [Fintype Y] [MeasurableSingletonClass Y]

/-- Partition an arbitrary event by a finite measurable observation. -/
lemma sum_fibers (μ : Measure X) [IsFiniteMeasure μ] (E : Set X)
    {f : X → Y} (hf : Measurable f) :
    (∑ a : Y,μ.real {x | x∈E ∧ f x=a})=μ.real E := by
  have hh := sum_measureReal_preimage_singleton (μ:=μ.restrict E) univ
    (fun a _ => hf (measurableSet_singleton a))
  have he (a : Y) : (μ.restrict E).real (f ⁻¹' {a})=μ.real {x | x∈E ∧ f x=a} := by
    rw [measureReal_restrict_apply (hf (measurableSet_singleton a))]
    congr 1
    ext x
    simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_singleton_iff,Set.mem_ofPred_eq,and_comm]
  simp only [he,coe_univ,Set.preimage_univ,measureReal_restrict_apply_univ] at hh
  exact hh

section Cyclic
variable {m : ℕ} [NeZero m]
variable (T : X → X) (a : X → ZMod m)

def align (x : X) : X := (T^[(-a x).val]) x

omit [MeasurableSpace X] [NeZero m] in
lemma iterate_phase (ha : ∀ x,a (T x)=a x+1) (x : X) (j : ℕ) :
    a ((T^[j]) x)=a x+j := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply',ha,ih,Nat.cast_add,Nat.cast_one,add_assoc]

lemma measurable_align (hT : Measurable T) (ha : Measurable a) : Measurable (align T a) := by
  have hf : Measurable (fun p : ℕ × X => (T^[p.1]) p.2) :=
    measurable_from_prod_countable_right (fun j => hT.iterate j)
  exact hf.comp (((measurable_of_countable (fun r : ZMod m => (-r).val)).comp ha).prodMk measurable_id)

/-- Each fixed phase piece maps to exactly the same boundary event; this
is an unnormalized identity using invariance, not a uniform-word assumption. -/
lemma phase_piece (μ : Measure X) (hT : MeasurePreserving T μ μ)
    (ha : Measurable a) (hevolve : ∀ x,a (T x)=a x+1)
    (E : Set X) (hE : MeasurableSet E) (j : ZMod m) :
    μ {x | x∈(align T a) ⁻¹' E ∧ a x=j}=μ (E∩{x | a x=0}) := by
  have hb : MeasurableSet (E∩{x | a x=0}) :=
    hE.inter (measurableSet_eq_fun ha measurable_const)
  rw [←(hT.iterate (-j).val).measure_preimage hb.nullMeasurableSet]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq,Set.mem_preimage,Set.mem_inter_iff,iterate_phase T a hevolve,
    ZMod.natCast_zmod_val]
  constructor
  · rintro ⟨hx,hj⟩
    exact ⟨by simpa only [align,hj] using hx,by rw [hj,add_neg_cancel]⟩
  · rintro ⟨hx,hj⟩
    have hj' : a x=j := by exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hj)
    exact ⟨by simpa only [align,hj'] using hx,hj'⟩

/-- Exact forward-alignment law for every measurable event. -/
theorem align_real (μ : Measure X) [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (ha : Measurable a)
    (hevolve : ∀ x,a (T x)=a x+1) (E : Set X) (hE : MeasurableSet E) :
    μ.real ((align T a) ⁻¹' E) = (m:ℝ)*μ.real (E∩{x | a x=0}) := by
  rw [←sum_fibers μ ((align T a) ⁻¹' E) ha]
  simp only [Measure.real,phase_piece T a μ hT ha hevolve E hE]
  simp only [sum_const,card_univ,ZMod.card,nsmul_eq_mul]

noncomputable def boundaryMeasure (μ : Measure X) : Measure X :=
  (m:ℝ≥0∞) • μ.restrict {x | a x=0}

omit [NeZero m] in
lemma boundary_real (μ : Measure X) (E : Set X) (hE : MeasurableSet E) :
    (boundaryMeasure a μ).real E=(m:ℝ)*μ.real (E∩{x | a x=0}) := by
  rw [boundaryMeasure,Measure.real,Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
    ENNReal.toReal_natCast,Measure.restrict_apply hE]
  rfl

/-- The image of the original stationary law under first-boundary advance
is the normalized boundary restriction itself. -/
theorem align_map (μ : Measure X) [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (ha : Measurable a)
    (hevolve : ∀ x,a (T x)=a x+1) :
    μ.map (align T a)=boundaryMeasure a μ := by
  have hm := measurable_align T a hT.measurable ha
  apply Measure.ext
  intro E hE
  apply ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by
    change ((m:ℝ≥0∞)*(μ.restrict {x | a x=0}) E)≠⊤
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) (measure_ne_top _ _)) |>.mp
  change (μ.map (align T a)).real E=(boundaryMeasure a μ).real E
  rw [boundary_real a μ E hE]
  simpa only [Measure.real,Measure.map_apply hm hE] using align_real T a μ hT ha hevolve E hE

/-- Its normalization is proved, including the literal source factor m. -/
theorem boundary_probability (μ : Measure X) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (ha : Measurable a)
    (hevolve : ∀ x,a (T x)=a x+1) : IsProbabilityMeasure (boundaryMeasure a μ) := by
  rw [←align_map T a μ hT ha hevolve]
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_align T a hT.measurable ha).aemeasurable).2 inferInstance
end Cyclic
end SmoothObstruction.Alignment

namespace SmoothObstruction.WordHierarchy
open WordParameters WordStep MeasureTheory Set
open scoped ENNReal

abbrev phase (i : ℕ) (x : Extension) : ZMod (length 40000 i) := x.val.2 i
lemma measurable_phase (i : ℕ) : Measurable (phase i) :=
  ((measurable_pi_apply i).comp measurable_snd).comp measurable_subtype_coe

noncomputable def boundary (μ : Measure Extension) (i : ℕ) : Measure Extension :=
  Alignment.boundaryMeasure (phase i) μ

lemma boundary_isProbability (μ : Measure Extension) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (i : ℕ) : IsProbabilityMeasure (boundary μ i) :=
  Alignment.boundary_probability T (phase i) μ hT (measurable_phase i) (fun _ => rfl)

noncomputable def advance (i : ℕ) : Extension → Extension := Alignment.align T (phase i)

lemma length_two (i : ℕ) :
    length 40000 (i+2)=length 40000 i*(N (S i)*N (S (i+1))) := by
  simp only [length,N,S]
  ring

noncomputable def parentSlot (i : ℕ) (x : Extension) : Fin (N (S i)*N (S (i+1))) :=
  ⟨(phase (i+2) x).val / length 40000 i,by
    apply (Nat.div_lt_iff_lt_mul (length_pos 40000 i)).mpr
    simpa only [length_two,Nat.mul_comm] using ZMod.val_lt (phase (i+2) x)⟩

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.WordHierarchy
open WordParameters WordStep WordConcatenation MeasureTheory Set

lemma length_step (i : ℕ) : length 40000 (i+1)=length 40000 i*N (S i) := rfl

/-- The exact observed finite word-label list on the normalized boundary. -/
noncomputable def labelList (i r : ℕ) (x : Extension) : Fin r → A i :=
  fun j => label i ((T^[j.val*length 40000 i]) x)

lemma measurable_T : Measurable (T : Extension → Extension) := by
  apply Measurable.subtype_mk
  apply Measurable.prodMk
  · exact measurable_pi_iff.mpr (fun t =>
      ((measurable_pi_apply (t+1)).comp measurable_fst).comp measurable_subtype_coe)
  · exact measurable_pi_iff.mpr (fun i =>
      (measurable_of_countable (fun a : ZMod (length 40000 i) => a+1)).comp (measurable_phase i))

lemma measurable_labelList (i r : ℕ) : Measurable (labelList i r) := by
  exact measurable_pi_iff.mpr (fun j => (measurable_label i).comp
    (measurable_T.iterate (j.val*length 40000 i)))

end SmoothObstruction.WordHierarchy

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_WordEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SmoothObstruction.FiniteLaw
open Finset FiniteEntropy
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

noncomputable def uniform [Nonempty α] : Law α where
  mass := fun _ => (Fintype.card α : ℝ)⁻¹
  nonneg := fun _ => by positivity
  total := by simp [Fintype.card_ne_zero]

noncomputable def mixture (P : Law α) (Q : α → Law β) : Law β where
  mass b := ∑ a,P.mass a*(Q a).mass b
  nonneg b := sum_nonneg (fun a _ => mul_nonneg (P.nonneg a) ((Q a).nonneg b))
  total := by
    rw [sum_comm]
    simp only [←mul_sum,(Q _).total,mul_one,P.total]

noncomputable def TV (P Q : Law α) : ℝ := (1/2:ℝ)*∑ a,|P.mass a-Q.mass a|
noncomputable def entropy (P : Law α) : ℝ := natEntropy P.mass

end SmoothObstruction.FiniteLaw

namespace SmoothObstruction.SequentialLaw
open Finset
variable {A : Type*} [Fintype A] [DecidableEq A] {q N : ℕ}

noncomputable def embeddedMarks (e : Fin q ↪ Fin N) (v : Fin q → A) : Fin N → Option A :=
  fun i => if h : ∃ j, e j=i then some (v h.choose) else none

end SmoothObstruction.SequentialLaw

namespace SmoothObstruction.WordHierarchy
open Finset WordParameters WordStep WordAlphabet FiniteLaw

noncomputable instance levelNonempty (i : ℕ) : Nonempty (A i) := alphabet_nonempty i
noncomputable instance groupNeZero (i : ℕ) : NeZero (groupLength i) :=
  ⟨by rw [groupLength,q_mul_H]; exact (N_pos _).ne'⟩
noncomputable instance familyNeZero (i : ℕ) : NeZero (size i) := ⟨Fintype.card_ne_zero⟩

noncomputable def conditionedLabels (i : ℕ) : Law (Labels i) :=
  WordFlatten.flatLaw (form (S i)) (goodDim i) (stage i).E (stage i).massE
noncomputable def conditionedWindow (i : ℕ) (t : Offsets (S i)) : Law (Fin (D (S i)) → A i) :=
  push (conditionedLabels i) (window (S i) t)
noncomputable def uniformWindow (i : ℕ) (t : Offsets (S i)) : Law (Fin (D (S i)) → A i) :=
  push uniform (fun a : A (i+1) => window (S i) t ((stage i).word a))
noncomputable def parentWindow (i : ℕ) (a : A (i+2)) (t : Offsets (S i)) : Law (Fin (D (S i)) → A i) :=
  push uniform (fun j : Fin (groupLength (i+1)) =>
    window (S i) t ((stage i).word ((stage (i+1)).word a j)))

def windowEmbedding (i : ℕ) (t : Offsets (S i)) {r : ℕ} (hr : r ≤ D (S i)) : Fin r ↪ Fin (groupLength i) where
  toFun k := ⟨t.val.val+k.val,by change t.val.val+k.val < q (S i)*H (S i); have h := t.property; have hk := k.isLt; omega⟩
  inj' := by intro j k h; apply Fin.ext; have he := congrArg Fin.val h; dsimp at he; omega

def takePrefix {level r d : ℕ} (hr : r ≤ d) (w : Fin d → A level) : Fin r → A level :=
  fun k => w ⟨k.val,lt_of_lt_of_le k.isLt hr⟩

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.FiniteLaw
open MeasureTheory Set Finset
variable {X α β : Type*} [MeasurableSpace X] [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  [MeasurableSpace β] [MeasurableSingletonClass β]

noncomputable def observed (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → α) (hf : Measurable f) : Law α where
  mass a := μ.real {x | f x=a}
  nonneg _ := measureReal_nonneg
  total := by
    have h := Alignment.sum_fibers μ univ hf
    simpa only [Set.mem_univ,true_and,probReal_univ] using h

noncomputable def conditionalObserved (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → α) (hf : Measurable f) (k : X → β) (_hk : Measurable k)
    [Nonempty α] (b : β) : Law α := by
  let p := μ.real {x | k x=b}
  by_cases hp : p=0
  · exact uniform
  · refine ⟨(fun a => μ.real {x | k x=b ∧ f x=a}/p),fun _ => div_nonneg measureReal_nonneg measureReal_nonneg,?_⟩
    rw [←sum_div]
    have hs := Alignment.sum_fibers μ {x | k x=b} hf
    simp only [Set.mem_ofPred_eq] at hs
    rw [hs]
    exact div_self hp

end SmoothObstruction.FiniteLaw

namespace SmoothObstruction.WordHierarchy
open WordParameters WordStep WordConcatenation MeasureTheory Set Finset FiniteLaw
open scoped ENNReal

noncomputable instance stageLengthNeZero (i : ℕ) : NeZero (N (S i)) := ⟨(N_pos _).ne'⟩

lemma measurable_slot (i : ℕ) : Measurable (slot i) := by
  have hh : slot i = (fun a : ZMod (length 40000 (i+1)) =>
      (⟨a.val / length 40000 i,by
        apply (Nat.div_lt_iff_lt_mul (length_pos 40000 i)).mpr
        simpa only [length_step,Nat.mul_comm] using ZMod.val_lt a⟩ : Fin (N (S i)))) ∘ phase (i+1) := rfl
  rw [hh]
  exact (measurable_of_countable _).comp (measurable_phase (i+1))

noncomputable def windowKey (i : ℕ) (x : Extension) : A (i+2) × Fin (N (S i)) :=
  (label (i+2) x,slot i x)

lemma measurable_windowKey (i : ℕ) : Measurable (windowKey i) :=
  (measurable_label _).prodMk (measurable_slot _)

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.WordHierarchy
open WordParameters WordStep WordConcatenation MeasureTheory Set Finset FiniteLaw

/-- The actual r-child window at an internal offset of a specified parent. -/
noncomputable def sampledWindow (i r : ℕ) (u : Fin (N (S i)))
    (hr : u.val+r ≤ N (S i)) (v : A (i+2)) (h : Fin (N (S (i+1)))) : Fin r → A i :=
  fun j => children i (children (i+1) v h) ⟨u.val+j.val,by have := j.isLt; omega⟩

noncomputable def sampledLaw (i r : ℕ) (u : Fin (N (S i)))
    (hr : u.val+r ≤ N (S i)) (v : A (i+2)) : Law (Fin r → A i) :=
  push uniform (sampledWindow i r u hr v)

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.WordHierarchy
open MeasureTheory Set Finset WordParameters WordStep FiniteLaw

noncomputable def windowLower (i r : ℕ) : ℝ :=
  (r:ℝ)*((1-2/10000)*Real.log (Fintype.card (A i))-(2*K (S i):ℕ)*Real.log 2)-2*Real.log 2

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.WordHierarchy
open WordParameters WordAlphabet WordStep WordConcatenation MeasureTheory Set Finset

lemma group_site_lt (i : ℕ) (u : Fin (N (S i))) {r : ℕ} (hr : r<H (S i)) :
    H (S i)*(u.val/H (S i))+r < N (S i) := by
  have hd : u.val/H (S i)<q (S i) := by
    apply (Nat.div_lt_iff_lt_mul (H_pos (S i))).mpr
    rw [q_mul_H]
    exact u.isLt
  have hh : (u.val/H (S i)+1)*H (S i) ≤ q (S i)*H (S i) :=
    Nat.mul_le_mul_right _ hd
  rw [q_mul_H] at hh
  nlinarith

/-- The genuine two-window graph event on a boundary-started orbit. -/
def graphWindows (i k : ℕ) (x : Extension) : Prop :=
  ∀ j : Fin (2^k-1), form (S i)
    (label i ((T^[j.val*length 40000 i]) x)).val
    (label i ((T^[(j.val+2^k)*length 40000 i]) x)).val=0

end SmoothObstruction.WordHierarchy

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_PairBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped Classical
open Finset

namespace SmoothObstruction.BinaryCharacter

/-- The real-valued character of the two-element field. -/
def sign (a : ZMod 2) : ℝ := if a = 0 then 1 else -1

@[simp] lemma sign_zero : sign 0 = 1 := by simp [sign]
@[simp] lemma sign_one : sign 1 = -1 := by norm_num [sign]
@[simp] lemma sign_sq (a : ZMod 2) : sign a ^ 2 = 1 := by
  unfold sign
  split_ifs <;> norm_num

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

section Nonzero
variable [DecidableEq V]

noncomputable def extendZero (p : {v : V // v ≠ 0} → ℝ) (v : V) : ℝ :=
  if h : v ≠ 0 then p ⟨v, h⟩ else 0

omit [Module (ZMod 2) V] [Fintype V] in
@[simp] lemma extendZero_zero (p : {v : V // v ≠ 0} → ℝ) : extendZero p 0 = 0 := by
  simp [extendZero]
omit [Module (ZMod 2) V] [Fintype V] in
@[simp] lemma extendZero_coe (p : {v : V // v ≠ 0} → ℝ) (v : {v : V // v ≠ 0}) :
    extendZero p v = p v := by simp [extendZero, v.property]

end Nonzero
end SmoothObstruction.BinaryCharacter

namespace SmoothObstruction.GraphBound
open BinaryCharacter

variable {α : Type*} [Fintype α]

noncomputable def light (τ : ℝ) (p : α → ℝ) (i : α) : ℝ :=
  if p i ≤ τ then p i else 0

noncomputable def passing {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) (e : α → V) (p q : α → ℝ) : ℝ :=
  ∑ u, ∑ v, p u * q v * if B (e u) (e v) = 0 then 1 else 0

end SmoothObstruction.GraphBound

namespace SmoothObstruction.PairUpper
open MeasureTheory Set Finset FiniteLaw
open scoped ENNReal
variable {X C J V : Type*} [MeasurableSpace X]
  [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
  [Fintype J] [DecidableEq J] [Nonempty J]
  [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] [DecidableEq V] [Nontrivial V]
  [MeasurableSpace V] [MeasurableSingletonClass V]

instance nonzeroNonempty : Nonempty {v : V // v≠0} := by
  obtain ⟨v,hv⟩ := exists_ne (0:V)
  exact ⟨⟨v,hv⟩⟩

noncomputable def statistic (B : LinearMap.BilinForm (ZMod 2) V)
    (u v : J → {v : V // v≠0}) : ℝ :=
  (∑ j,if B (u j) (v j)=0 then (1:ℝ) else 0)/Fintype.card J

end SmoothObstruction.PairUpper

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_Recognition
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SmoothObstruction.WordConcatenation
open Finset
variable {A B : Type*} {m N : ℕ}

noncomputable def mismatches {ι : Type*} [Fintype ι] (u v : ι → A) : ℕ := by
  classical
  exact (univ.filter (fun r => u r ≠ v r)).card

/-- Arbitrarily addressed letters of a two-word splice. Only addresses less
than twice the word length are used by recognition. -/
def joined [NeZero m] (u v : Fin m → A) (k : ℕ) : A :=
  if k < m then u ⟨k%m,Nat.mod_lt _ (NeZero.pos m)⟩
  else v ⟨k%m,Nat.mod_lt _ (NeZero.pos m)⟩

def splice [NeZero m] (u v : Fin m → A) (t : Fin m) : Fin m → A :=
  fun r => joined u v (t.val+r.val)

@[simp] lemma splice_zero [NeZero m] (u v : Fin m → A) : splice u v 0=u := by
  funext r
  simp [splice,joined,Nat.mod_eq_of_lt r.isLt,r.isLt]

/-- A single recognition predicate handles both distinct words and every
nontrivial splice, so the symbol-scale induction cannot drop an offset. -/
def Recognizes [NeZero m] (u : B → Fin m → A) (δ : ℝ) : Prop :=
  ∀ a b c (t : Fin m), t≠0 ∨ a≠c →
    δ*m ≤ (mismatches (splice (u a) (u b) t) (u c) : ℝ)

end SmoothObstruction.WordConcatenation

namespace SmoothObstruction.WordHierarchy
open WordConcatenation WordParameters WordStep Finset

instance recognitionNNeZero (i : ℕ) : NeZero (N (S i)) :=
  ⟨by rw [←q_mul_H]; exact NeZero.ne (q (S i)*H (S i))⟩

noncomputable def delta (i : ℕ) : ℝ := ∏ j ∈ range i, (1-epsilon j)

@[simp] lemma delta_zero : delta 0=1 := by simp [delta]

noncomputable instance recognitionLengthNeZero (i : ℕ) : NeZero (length 40000 i) :=
  ⟨(length_pos 40000 i).ne'⟩

end SmoothObstruction.WordHierarchy

namespace SmoothObstruction.RecognitionWindow
open Finset WordConcatenation
variable {A B : Type*} {m : ℕ} [NeZero m]

/-- A legal phase-marked bilateral sequence, with no restriction at window
endpoints; adjacent words are allowed to be identical. -/
def LegalAt (w : B → Fin m → A) (u : ℤ → A) (p : ZMod m) : Prop :=
  ∀ t : ℤ,(t : ZMod m)=-p → ∃ a,∀ r : Fin m,u (t+r.val)=w a r

/-- The D-1 full blocks after first alignment are disjoint and remain in
[0,D*m), including the case of a nonzero advance. -/
def blocksEmbedding (D a : ℕ) (ha : a < m) : Fin (D-1) × Fin m ↪ Fin (D*m) where
  toFun jr := ⟨a+jr.1.val*m+jr.2.val,by
    have hj := jr.1.isLt
    have hr := jr.2.isLt
    have hm := NeZero.pos m
    have hjD : jr.1.val+2≤D := by omega
    have hb := Nat.mul_le_mul_right m hjD
    nlinarith⟩
  inj' := by
    intro p q he
    have hv := congrArg Fin.val he
    change a+p.1.val*m+p.2.val=a+q.1.val*m+q.2.val at hv
    have hp := p.2.isLt
    have hq := q.2.isLt
    have hm := NeZero.pos m
    have hj : p.1.val=q.1.val := by
      by_contra hn
      rcases lt_or_gt_of_ne hn with h|h
      · have hh := Nat.mul_le_mul_right m (Nat.succ_le_of_lt h)
        nlinarith
      · have hh := Nat.mul_le_mul_right m (Nat.succ_le_of_lt h)
        nlinarith
    have hk : p.2.val=q.2.val := by nlinarith
    exact Prod.ext (Fin.ext hj) (Fin.ext hk)

end SmoothObstruction.RecognitionWindow

namespace SmoothObstruction.WordHierarchy
open WordParameters WordStep WordConcatenation MeasureTheory Set Finset FiniteLaw

lemma measurable_advance (i : ℕ) : Measurable (advance i) :=
  Alignment.measurable_align T (phase i) measurable_T (measurable_phase i)

/-- Original ordered labels after the first true boundary, without changing
its phase or introducing a new pairing. -/
noncomputable def firstList (i D : ℕ) (x : Extension) : Fin (D-1) → A i :=
  labelList i (D-1) (advance i x)

lemma measurable_firstList (i D : ℕ) : Measurable (firstList i D) :=
  (measurable_labelList i (D-1)).comp (measurable_advance i)

end SmoothObstruction.WordHierarchy

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_SymbolCores
attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SmoothObstruction.SymbolMass
open MeasureTheory Set
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Counted mismatches, before any normalization of the retained law. -/
noncomputable def errors (N : ℕ) (bad : Fin N → Set Ω) (ω : Ω) : ℝ≥0∞ :=
  ∑ t : Fin N, (bad t).indicator (fun _ => (1 : ℝ≥0∞)) ω

end SmoothObstruction.SymbolMass

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_Obstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SmoothObstruction.WordHierarchy
open Set MeasureTheory WordParameters WordAlphabet WordStep WordConcatenation FiniteLaw
open scoped ENNReal

noncomputable def initialSymbol (x : Extension) : A 0 := x.val.1 0
end SmoothObstruction.WordHierarchy

end

end OAI
end

section
-- module Solutions.OAIQ5_T3.SmoothObstruction_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SmoothObstruction
open MeasureTheory Set Filter Topology
open scoped ENNReal Manifold ContDiff
open WordHierarchy

/-- Both sides of the phase-extension shift have the original product
sigma-algebra measurability, independent of any choice of compatible metrics. -/
lemma measurable_word_inverse : Measurable (T.symm : Extension → Extension) := by
  apply Measurable.subtype_mk
  apply Measurable.prodMk
  · exact measurable_pi_iff.mpr (fun t =>
      ((measurable_pi_apply (t-1)).comp measurable_fst).comp measurable_subtype_coe)
  · exact measurable_pi_iff.mpr (fun i =>
      (measurable_of_countable (fun a : ZMod (WordParameters.length 40000 i) => a-1)).comp
        (measurable_phase i))

noncomputable def wordMeasurableEquiv : Extension ≃ᵐ Extension where
  toEquiv := T.toEquiv
  measurable_toFun := measurable_T
  measurable_invFun := measurable_word_inverse

end SmoothObstruction

end

end OAI
end


