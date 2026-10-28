-- Prove2me | Definitions.Def_OAIS336000
-- name    : OAIS336000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T10:38:14.55299+00:00
-- url     : https://prove2.me/theorems/6c59e322-cedd-442b-9e5b-d2a0dcb39233
-- title:
--   Definitions bundle OAIS336000 of the split of OpenAI, The free uniform spanning forest is a factor of IID
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Problem336.fusf_is_factor_iid`, carved from OpenAI's openai/math development (OpenAI, *The free uniform spanning forest is a factor of IID*, OpenAI Math Release, September 25, 2026, result family 231, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 545 declarations of OpenAI's Lean: 259 definitions, 19 instances and 267 theorems. The definitions and types are `Finset.orderEmbOfFinWithBot`, `OAI.Problem336.AllPairAllocation.ballRank`, `OAI.Problem336.AllPairAllocation.coordinate`, `OAI.Problem336.AllPairAllocation.coordinateNat`, `OAI.Problem336.AllPairAllocation.radius`, `OAI.Problem336.AllPairAllocation.radiusPredicate`, `OAI.Problem336.AllPairIID.raw`, `OAI.Problem336.AllPairIID.uniformRule`, `OAI.Problem336.AllPairObservation.observations`, `OAI.Problem336.AllPairObservation.vertexPairs`, `OAI.Problem336.AllPairWiener.Path`, `OAI.Problem336.AllPairWiener.instMeasurableSpacePath`, `OAI.Problem336.AllPairWiener.law`, `OAI.Problem336.AllPairWiener.noise`, `OAI.Problem336.AllPairWiener.pathEval`, `OAI.Problem336.AllPairWiener.paths`, `OAI.Problem336.BinaryLaw.signedCylinder`, `OAI.Problem336.BrownianBridge.residual`, `OAI.Problem336.BrownianFamilyIdentification.vectorGaussian`, `OAI.Problem336.BrownianReference.coupling`, `OAI.Problem336.CanonicalBrownianReference.Space`, `OAI.Problem336.CanonicalBrownianReference.hidden`, `OAI.Problem336.CanonicalBrownianReference.instMeasurableSpacePath`, `OAI.Problem336.CanonicalBrownianReference.law`, `OAI.Problem336.CanonicalBrownianReference.noise`, `OAI.Problem336.CanonicalBrownianReference.noiseLaw`, `OAI.Problem336.CanonicalBrownianReference.observation`, `OAI.Problem336.CanonicalBrownianSampler.driftField`, `OAI.Problem336.CanonicalBrownianSampler.filtration`, `OAI.Problem336.CanonicalBrownianSampler.instMeasurableSpacePath`, `OAI.Problem336.CanonicalBrownianSampler.signal`, `OAI.Problem336.CanonicalDrift.outerLimit`, `OAI.Problem336.CanonicalPosteriorMartingale.observation`, `OAI.Problem336.CauchyBinet.ColumnSets`, `OAI.Problem336.CauchyBinet.columnIndexEquiv`, `OAI.Problem336.CauchyBinet.columnMinor`, `OAI.Problem336.CodeTransferKernel.edgeEquiv`, `OAI.Problem336.CodeTransferKernel.incidence`, `OAI.Problem336.ContinuousPathLaw.denseEval`, `OAI.Problem336.ContinuousPathLaw.raw` and 219 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability/SpanningForest, in whole or in part: `SpanningForest_AlgebraicCycleSpace`, `SpanningForest_AllPairAllocation`, `SpanningForest_AllPairIID`, `SpanningForest_AllPairObservation`, `SpanningForest_AllPairWiener`, `SpanningForest_BinaryGaussianPosterior`, `SpanningForest_BinaryLawUnique`, `SpanningForest_BitRecovery`, `SpanningForest_BrownianBridge`, `SpanningForest_BrownianFamilyIdentification`, `SpanningForest_BrownianReference`, `SpanningForest_CanonicalBrownianReference`, `SpanningForest_CanonicalBrownianSampler`, `SpanningForest_CanonicalDrift`, `SpanningForest_CanonicalPosteriorIdentification`, `SpanningForest_CanonicalPosteriorMartingale`, `SpanningForest_CauchyBinet`, `SpanningForest_CodeLaplacian`, `SpanningForest_CodeTransferKernel`, `SpanningForest_CodedIncidenceMinors`, `SpanningForest_CodedInclusion`, `SpanningForest_CodedMatrixTree`, `SpanningForest_ContinuousPathLaw`, `SpanningForest_ContinuousPathLimit`, `SpanningForest_CoordinateTruncation`, `SpanningForest_CountableBrownian`, `SpanningForest_CountableProjective`, `SpanningForest_DenseBrownian`, `SpanningForest_DenseGaussianModification`, `SpanningForest_DisconnectedIncidence`, `SpanningForest_DyadicGaussianBound`, `SpanningForest_DyadicInterpolation`, `SpanningForest_DyadicPathLimit`, `SpanningForest_DyadicTimes`, `SpanningForest_EdgeAction`, `SpanningForest_EdgeAllocation`, `SpanningForest_EdgeAllocationMeasurable`, `SpanningForest_EdgeIID`, `SpanningForest_EdgeUniformRule`, `SpanningForest_ExhaustionExistence`, `SpanningForest_FUSFLawUnique`, `SpanningForest_FactorAssembly`, `SpanningForest_FinalFactor`, `SpanningForest_FiniteCycleIncidence`, `SpanningForest_FiniteGaussianPosterior`, `SpanningForest_FiniteGradientResponse`, `SpanningForest_FiniteIncidenceBridge`, `SpanningForest_FiniteKernelEmbedding`, `SpanningForest_FinitePosterior`, `SpanningForest_FiniteResponse`, `SpanningForest_FiniteUSTLimit`, `SpanningForest_FiniteUSTMeasure`, `SpanningForest_FiniteUSTProbability`, `SpanningForest_FiniteUSTRelabel`, `SpanningForest_GaussianObservationKernel`, `SpanningForest_GlobalWiener`, `SpanningForest_GraphBalls`, `SpanningForest_GraphCoordinateTruncation`, `SpanningForest_GraphEncoding`, `SpanningForest_GraphFreeKernel`, `SpanningForest_GraphTreePosterior`, `SpanningForest_IncidenceCirculation`, `SpanningForest_IncidenceUnimodular`, `SpanningForest_InducedCode`, `SpanningForest_InnovationErrorRate`, `SpanningForest_InnovationMartingale`, `SpanningForest_InnovationPhaseRecurrence`, `SpanningForest_IntrinsicBridge`, `SpanningForest_IntrinsicExhaustion`, `SpanningForest_IntrinsicTreeDrift`, `SpanningForest_JointProcessLaw`, `SpanningForest_ObservationPosterior`, `SpanningForest_ObservedBrownianMartingale`, `SpanningForest_PathConcatenation`, `SpanningForest_Picard`, `SpanningForest_PicardBounds`, `SpanningForest_PicardNonnegativeSampler`, `SpanningForest_PicardNonnegativeTime`, `SpanningForest_PicardSamplerLaw`, `SpanningForest_PicardUniqueness`, `SpanningForest_PosteriorDrift`, `SpanningForest_PosteriorIndependentExtension`, `SpanningForest_PosteriorTiltLimit`, `SpanningForest_RawInnovationSampler`, `SpanningForest_ReducedCycleKernel`, `SpanningForest_ReducedLaplacian`, `SpanningForest_SampledPathConcatenation`, `SpanningForest_SampledUnitPath`, `SpanningForest_SchauderTail`, `SpanningForest_SchauderTents`, `SpanningForest_SubtypeSubsetSums`, `SpanningForest_TransferCurrent`, `SpanningForest_TransferCurrentLipschitz`, `SpanningForest_TransferProjection`, `SpanningForest_USTFiniteTilt`, `SpanningForest_USTInclusionCount`, `SpanningForest_USTPosteriorResponse`, `SpanningForest_USTResponse`, `SpanningForest_UniformSampler`, `SpanningForest_WeightedTreeBorel`, `SpanningForest_WeightedTreeEquiv`, `SpanningForest_WienerSampler`.
--
--   **Imports.** It imports the published bundle `Def_FreeUniformSpanningForest`.
--
--   **Imported by** (directly, in this split): the statements `OAI.Problem336.CanonicalBrownianSampler.raw_innovation_hasLaw`, `OAI.Problem336.FinalFactor.worksOnGraph` and `OAI.Problem336.HasFUSFLaw.finiteResponseBound`; the proofs of `OAI.Problem336.CanonicalBrownianSampler.raw_innovation_hasLaw`, `OAI.Problem336.FinalFactor.worksOnGraph`, `OAI.Problem336.HasFUSFLaw.finiteResponseBound`, `OAI.Problem336.exists_hasFUSFLaw` and `OAI.Problem336.fusf_is_factor_iid`.
-- source:
--   OpenAI, The free uniform spanning forest is a factor of IID, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 231; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-free-uniform-spanning-forest-is-a-factor-of-IID-September-25-2026/The-free-uniform-spanning-forest-is-a-factor-of-IID-September-25-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/SpanningForest at commit adc7f12

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.List.Nodup
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Definitions.Def_FreeUniformSpanningForest

section
-- module Solutions.OAIS_P336.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
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
-- module Solutions.OAIS_P336.SpanningForest_AlgebraicCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem336

abbrev EdgeFlow := EdgeCode →₀ ℝ

def edgeBoundary : EdgeFlow →ₗ[ℝ] (ℕ →₀ ℝ) :=
  Finsupp.linearCombination ℝ (fun e : EdgeCode =>
    Finsupp.single e.1.1 1 - Finsupp.single e.1.2 1)

@[simp] theorem edgeBoundary_single (e : EdgeCode) (c : ℝ) :
    edgeBoundary (Finsupp.single e c) =
      c • (Finsupp.single e.1.1 1 - Finsupp.single e.1.2 1) := by
  simp [edgeBoundary]

def finiteCodeEdges (K : FiniteSubgraphCode) : Set EdgeCode :=
  {e | e.1 ∈ K.2}

def graphCodeEdges (G : GraphCode) : Set EdgeCode :=
  {e | Adj G e.1.1 e.1.2}

def finiteCycleSpace (K : FiniteSubgraphCode) : Submodule ℝ EdgeFlow :=
  Finsupp.supported ℝ ℝ (finiteCodeEdges K) ⊓ LinearMap.ker edgeBoundary

def graphCycleSpace (G : GraphCode) : Submodule ℝ EdgeFlow :=
  Finsupp.supported ℝ ℝ (graphCodeEdges G) ⊓ LinearMap.ker edgeBoundary

@[simp] theorem mem_finiteCycleSpace (K : FiniteSubgraphCode) (f : EdgeFlow) :
    f ∈ finiteCycleSpace K ↔
      (∀ e ∈ f.support, e.1 ∈ K.2) ∧ edgeBoundary f = 0 := by
  simp [finiteCycleSpace, Finsupp.mem_supported, finiteCodeEdges, Set.subset_def]

@[simp] theorem mem_graphCycleSpace (G : GraphCode) (f : EdgeFlow) :
    f ∈ graphCycleSpace G ↔
      (∀ e ∈ f.support, Adj G e.1.1 e.1.2) ∧ edgeBoundary f = 0 := by
  simp [graphCycleSpace, Finsupp.mem_supported, graphCodeEdges, Set.subset_def]

 theorem finiteCodeEdges_finite (K : FiniteSubgraphCode) :
    (finiteCodeEdges K).Finite :=
  Set.Finite.preimage Subtype.val_injective.injOn K.2.finite_toSet

instance finiteDimensional_finiteCycleSpace (K : FiniteSubgraphCode) :
    FiniteDimensional ℝ (finiteCycleSpace K) := by
  let : Fintype (finiteCodeEdges K) := (finiteCodeEdges_finite K).fintype
  let : FiniteDimensional ℝ (Finsupp.supported ℝ ℝ (finiteCodeEdges K)) :=
    (Finsupp.supportedEquivFinsupp (M := ℝ) (R := ℝ) (finiteCodeEdges K)).symm.finiteDimensional
  exact Submodule.finiteDimensional_of_le
    (show finiteCycleSpace K ≤ Finsupp.supported ℝ ℝ (finiteCodeEdges K) from inf_le_left)

abbrev EdgeHilbert := lp (fun _ : EdgeCode => ℝ) 2

def edgeFlowToHilbert : EdgeFlow →ₗ[ℝ] EdgeHilbert :=
  Finsupp.linearCombination ℝ (fun e : EdgeCode => lp.single 2 e (1 : ℝ))

@[simp] theorem edgeFlowToHilbert_single (e : EdgeCode) (c : ℝ) :
    edgeFlowToHilbert (Finsupp.single e c) = lp.single 2 e c := by
  simp [edgeFlowToHilbert, ← lp.single_smul]

@[simp] theorem edgeFlowToHilbert_apply (f : EdgeFlow) (e : EdgeCode) :
    edgeFlowToHilbert f e = f e := by
  classical
  induction f using Finsupp.induction with
  | zero => simp
  | single_add a b f ha hb ih =>
    simp only [map_add, edgeFlowToHilbert_single, lp.coeFn_add, Pi.add_apply,
      Finsupp.add_apply, ih]
    simp [lp.single_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]

def finiteHilbertCycleSpace (K : FiniteSubgraphCode) : Submodule ℝ EdgeHilbert :=
  (finiteCycleSpace K).map edgeFlowToHilbert

def closedGraphCycleSpace (G : GraphCode) : Submodule ℝ EdgeHilbert :=
  ((graphCycleSpace G).map edgeFlowToHilbert).topologicalClosure

instance finiteDimensional_finiteHilbertCycleSpace (K : FiniteSubgraphCode) :
    FiniteDimensional ℝ (finiteHilbertCycleSpace K) := by
  unfold finiteHilbertCycleSpace
  infer_instance

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_EdgeAllocation
attribute [-instance] _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem336
namespace EdgeAllocation

def source (key : ℕ → ℝ) (e : EdgeCode) : ℕ :=
  if key e.1.1 < key e.1.2 then e.1.1 else e.1.2

def target (key : ℕ → ℝ) (e : EdgeCode) : ℕ :=
  if key e.1.1 < key e.1.2 then e.1.2 else e.1.1

end EdgeAllocation
end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_EdgeAllocationMeasurable
attribute [-instance] _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem336.EdgeAllocation

@[fun_prop]
theorem measurable_source (e : EdgeCode) :
    Measurable (fun key : ℕ → ℝ => source key e) := by
  apply Measurable.ite _ measurable_const measurable_const
  exact measurableSet_lt (measurable_pi_apply _) (measurable_pi_apply _)

@[fun_prop]
theorem measurable_target (e : EdgeCode) :
    Measurable (fun key : ℕ → ℝ => target key e) := by
  apply Measurable.ite _ measurable_const measurable_const
  exact measurableSet_lt (measurable_pi_apply _) (measurable_pi_apply _)

@[fun_prop]
theorem measurable_source_joint :
    Measurable (fun q : (ℕ → ℝ) × EdgeCode => source q.1 q.2) :=
  measurable_from_prod_countable_left measurable_source

@[fun_prop]
theorem measurable_target_joint :
    Measurable (fun q : (ℕ → ℝ) × EdgeCode => target q.1 q.2) :=
  measurable_from_prod_countable_left measurable_target

end Problem336.EdgeAllocation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_EdgeAction
attribute [-instance] _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem336

theorem rawPair_comm (u v : ℕ) : rawPair u v = rawPair v u := by
  unfold rawPair
  split_ifs <;> simp_all <;> omega

@[simp] theorem rawPair_of_lt {u v : ℕ} (h : u < v) :
    rawPair u v = (u, v) := by
  simp [rawPair, h]

@[simp] theorem mkEdge_val (u v : ℕ) (h : u ≠ v) :
    (mkEdge u v h).val = rawPair u v := by
  unfold mkEdge rawPair
  split_ifs <;> rfl

@[simp] theorem mkEdge_of_lt {u v : ℕ} (h : u < v) :
    mkEdge u v (Nat.ne_of_lt h) = ⟨(u, v), h⟩ := by
  simp [mkEdge, h]

theorem mkEdge_swap (u v : ℕ) (h : u ≠ v) :
    mkEdge u v h = mkEdge v u h.symm := by
  apply Subtype.ext
  simpa only [mkEdge_val] using rawPair_comm u v

@[simp] theorem mkEdge_endpoints (e : EdgeCode) :
    mkEdge e.val.1 e.val.2 (Nat.ne_of_lt e.property) = e := by
  apply Subtype.ext
  simp [mkEdge, e.property]

theorem mapEdge_mkEdge (σ : Equiv ℕ ℕ) (u v : ℕ) (h : u ≠ v) :
    mapEdge σ (mkEdge u v h) =
      mkEdge (σ u) (σ v) (fun huv => h (σ.injective huv)) := by
  by_cases huv : u < v
  · simp [mapEdge, mkEdge, huv]
  · have hvu : v < u := lt_of_le_of_ne (Nat.le_of_not_gt huv) h.symm
    have he : mkEdge u v h = ⟨(v, u), hvu⟩ := by
      simp [mkEdge, huv]
    rw [he]
    change mkEdge (σ v) (σ u) _ = mkEdge (σ u) (σ v) _
    exact mkEdge_swap _ _ _

@[simp] theorem mapEdge_refl (e : EdgeCode) :
    mapEdge (Equiv.refl ℕ) e = e := by
  change mkEdge e.val.1 e.val.2 _ = e
  exact mkEdge_endpoints e

theorem mapEdge_trans (σ τ : Equiv ℕ ℕ) (e : EdgeCode) :
    mapEdge (σ.trans τ) e = mapEdge τ (mapEdge σ e) := by
  symm
  exact mapEdge_mkEdge τ (σ e.val.1) (σ e.val.2) _

@[simp] theorem mapEdge_symm_apply (σ : Equiv ℕ ℕ) (e : EdgeCode) :
    mapEdge σ.symm (mapEdge σ e) = e := by
  rw [← mapEdge_trans]
  simp

@[simp] theorem mapEdge_apply_symm (σ : Equiv ℕ ℕ) (e : EdgeCode) :
    mapEdge σ (mapEdge σ.symm e) = e := by
  simpa using mapEdge_symm_apply σ.symm e

def edgeEquiv (σ : Equiv ℕ ℕ) : Equiv EdgeCode EdgeCode where
  toFun := mapEdge σ
  invFun := mapEdge σ.symm
  left_inv := mapEdge_symm_apply σ
  right_inv := mapEdge_apply_symm σ

@[simp] theorem edgeEquiv_apply (σ : Equiv ℕ ℕ) (e : EdgeCode) :
    edgeEquiv σ e = mapEdge σ e := rfl

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_GraphBalls
attribute [-instance] _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem336

def withinRadius (G : GraphCode) : ℕ → ℕ → ℕ → Prop
  | 0, u, v => u = v
  | n + 1, u, v => withinRadius G n u v ∨
      ∃ w, withinRadius G n u w ∧ Adj G w v

@[simp] theorem withinRadius_zero (G : GraphCode) (u v : ℕ) :
    withinRadius G 0 u v ↔ u = v := Iff.rfl

def edgeBall (G : GraphCode) (n : ℕ) (e : EdgeCode) : Set ℕ :=
  {v | withinRadius G n e.val.1 v ∨ withinRadius G n e.val.2 v}

def finiteSetCode (s : Set ℕ) : Finset ℕ := by
  classical
  exact if hs : s.Finite then hs.toFinset else ∅

@[simp] theorem finiteSetCode_of_finite (s : Set ℕ) (hs : s.Finite) :
    finiteSetCode s = hs.toFinset := by
  simp [finiteSetCode, hs]

def edgeBallCode (G : GraphCode) (n : ℕ) (e : EdgeCode) : Finset ℕ :=
  finiteSetCode (edgeBall G n e)

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_AllPairAllocation
attribute [-instance] _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem336.AllPairAllocation

def radiusPredicate (G : GraphCode) (u v n : ℕ) : Prop :=
  withinRadius G n u v ∨ ¬ ∃ m, withinRadius G m u v

theorem exists_radiusPredicate (G : GraphCode) (u v : ℕ) :
    ∃ n, radiusPredicate G u v n := by
  classical
  by_cases h : ∃ n, withinRadius G n u v
  · obtain ⟨n, hn⟩ := h
    exact ⟨n, Or.inl hn⟩
  · exact ⟨0, Or.inr h⟩

def radius (G : GraphCode) (u v : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_radiusPredicate G u v)

def ballRank (G : GraphCode) (key : ℕ → ℝ) (n u v : ℕ) : ℕ :=
  Set.ncard {w | withinRadius G n u w ∧ key w < key v}

def coordinate (G : GraphCode) (key : ℕ → ℝ) (e : EdgeCode) : ℕ × (ℕ × ℕ) :=
  let u := EdgeAllocation.source key e
  let v := EdgeAllocation.target key e
  let n := radius G u v
  (u, n, ballRank G key n u v)

def coordinateNat (G : GraphCode) (key : ℕ → ℝ) (e : EdgeCode) : ℕ × ℕ :=
  let c := coordinate G key e
  (c.1, Nat.pair c.2.1 c.2.2)

end Problem336.AllPairAllocation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_UniformSampler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped unitInterval

namespace Problem336

def clampUniform : ℝ → I := Set.projIcc 0 1 zero_le_one

@[fun_prop]
theorem measurable_clampUniform : Measurable clampUniform :=
  continuous_projIcc.measurable

theorem uniform01_eq_map_unitInterval :
    uniform01 = (volume : Measure I).map (fun x : I => (x : ℝ)) :=
  unitInterval.measurePreserving_coe.map_eq.symm

theorem map_clampUniform : uniform01.map clampUniform = (volume : Measure I) := by
  rw [uniform01_eq_map_unitInterval,
    Measure.map_map measurable_clampUniform measurable_subtype_coe]
  convert (Measure.map_id : (volume : Measure I).map id = volume) using 1
  congr 1
  funext x
  exact Set.projIcc_val zero_le_one x

theorem exists_uniform01_sampler {Y : Type*} [MeasurableSpace Y]
    [Nonempty Y] [StandardBorelSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ] :
    ∃ f : ℝ → Y, Measurable f ∧ uniform01.map f = μ := by
  obtain ⟨f, hf, hmap⟩ := μ.exists_measurable_map_eq
  refine ⟨f ∘ clampUniform, hf.comp measurable_clampUniform, ?_⟩
  rw [← Measure.map_map hf measurable_clampUniform, map_clampUniform, hmap]

theorem sampler_uniform01_probability : IsProbabilityMeasure uniform01 := by
  rw [uniform01_eq_map_unitInterval]
  exact Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

def privatePoolLaw : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => uniform01)

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_EdgeIID
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem336.EdgeIID

local instance instIsProbabilityMeasureRealUniform01 : IsProbabilityMeasure uniform01 := sampler_uniform01_probability

abbrev Stream := Option ℕ → ℝ

def streamLaw : Measure Stream := Measure.infinitePi (fun _ : Option ℕ => uniform01)

local instance instIsProbabilityMeasureStreamStreamLaw : IsProbabilityMeasure streamLaw := by
  unfold streamLaw
  infer_instance

def stream : ℝ → Stream := Classical.choose (exists_uniform01_sampler streamLaw)

@[fun_prop] theorem measurable_stream : Measurable stream :=
  (Classical.choose_spec (exists_uniform01_sampler streamLaw)).1

def expanded (U : ℕ → ℝ) (p : ℕ × Option ℕ) : ℝ := stream (U p.1) p.2

@[fun_prop] theorem measurable_expanded : Measurable expanded := by
  apply Measurable.of_eval
  intro p
  exact (measurable_pi_apply p.2).comp (measurable_stream.comp (measurable_pi_apply p.1))

def keys (U : ℕ → ℝ) (v : ℕ) : ℝ := expanded U (v, none)

def pool (U : ℕ → ℝ) (p : ℕ × ℕ) : ℝ := expanded U (p.1, some p.2)

@[fun_prop] theorem measurable_keys : Measurable keys := by
  exact Measurable.of_eval (fun v => (measurable_pi_apply (v, none)).comp measurable_expanded)

@[fun_prop] theorem measurable_pool : Measurable pool := by
  exact Measurable.of_eval (fun p =>
    (measurable_pi_apply (p.1, some p.2)).comp measurable_expanded)

end Problem336.EdgeIID

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_EdgeUniformRule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem336

@[fun_prop]
theorem measurable_injective_keyField :
    Measurable (fun key : ℕ → ℝ => Function.Injective key) := by
  apply Measurable.forall
  intro i
  apply Measurable.forall
  intro j
  exact (measurableSet_setOfPred.mp
    (measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j))).imp
      measurable_const

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_AllPairIID
attribute [-instance] _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Problem336.AllPairIID

def raw (G : GraphCode) (U : ℕ → ℝ) (e : EdgeCode) : ℝ :=
  EdgeIID.pool U (AllPairAllocation.coordinateNat G (EdgeIID.keys U) e)

def uniformRule (G : GraphCode) (U : ℕ → ℝ) (e : EdgeCode) : ℝ := by
  classical
  exact if Function.Injective (EdgeIID.keys U) then raw G U e else 0

end Problem336.AllPairIID

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_IntrinsicExhaustion
attribute [-instance] _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem336
namespace IntrinsicExhaustion

def vertexBall (G : GraphCode) (c : ℕ) : ℕ → Set ℕ
  | 0 => {c}
  | n + 1 => vertexBall G c n ∪ {v | ∃ u ∈ vertexBall G c n, Adj G u v}

@[simp] theorem mem_vertexBall_zero (G : GraphCode) (c v : ℕ) :
    v ∈ vertexBall G c 0 ↔ v = c := Iff.rfl

@[simp] theorem mem_vertexBall_succ (G : GraphCode) (c v n : ℕ) :
    v ∈ vertexBall G c (n + 1) ↔
      v ∈ vertexBall G c n ∨ ∃ u ∈ vertexBall G c n, Adj G u v := Iff.rfl

theorem finite_vertexBall {G : GraphCode} (hG : GraphLocallyFinite G)
    (c n : ℕ) : (vertexBall G c n).Finite := by
  induction n with
  | zero => exact Set.finite_singleton c
  | succ n ih =>
    have h := ih.union (ih.biUnion (fun u _ => hG u))
    convert h using 1
    ext v
    simp [vertexBall]

def edgeBall (G : GraphCode) (e : EdgeCode) (n : ℕ) : Set ℕ :=
  vertexBall G e.1.1 n ∪ vertexBall G e.1.2 n

theorem finite_edgeBall {G : GraphCode} (hG : GraphLocallyFinite G)
    (e : EdgeCode) (n : ℕ) : (edgeBall G e n).Finite :=
  (finite_vertexBall hG e.1.1 n).union (finite_vertexBall hG e.1.2 n)

def ballInducedSubgraph (G : GraphCode) (s : Finset ℕ) : FiniteSubgraphCode := by
  classical
  exact (s, (s.product s).filter (fun p => p.1 < p.2 ∧ Adj G p.1 p.2))

@[simp] theorem ballInducedSubgraph_vertices (G : GraphCode) (s : Finset ℕ) :
    (ballInducedSubgraph G s).1 = s := rfl

@[simp] theorem mem_ballInducedSubgraph_edges (G : GraphCode) (s : Finset ℕ)
    (p : ℕ × ℕ) :
    p ∈ (ballInducedSubgraph G s).2 ↔
      p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2 ∧ Adj G p.1 p.2 := by
  classical
  simp [ballInducedSubgraph, and_assoc]

def edgeBallSubgraph (G : GraphCode) (hG : GraphLocallyFinite G)
    (e : EdgeCode) (n : ℕ) : FiniteSubgraphCode :=
  ballInducedSubgraph G (finite_edgeBall hG e n).toFinset

@[simp] theorem mem_edgeBallSubgraph_vertices (G : GraphCode)
    (hG : GraphLocallyFinite G) (e : EdgeCode) (n v : ℕ) :
    v ∈ (edgeBallSubgraph G hG e n).1 ↔ v ∈ edgeBall G e n := by
  simp [edgeBallSubgraph]

@[simp] theorem mem_edgeBallSubgraph_edges (G : GraphCode)
    (hG : GraphLocallyFinite G) (e : EdgeCode) (n : ℕ) (p : ℕ × ℕ) :
    p ∈ (edgeBallSubgraph G hG e n).2 ↔
      p.1 ∈ edgeBall G e n ∧ p.2 ∈ edgeBall G e n ∧ p.1 < p.2 ∧ Adj G p.1 p.2 := by
  simp [edgeBallSubgraph]

end IntrinsicExhaustion
end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_AllPairObservation
attribute [-instance] _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem336.AllPairObservation

def vertexPairs (V : Finset ℕ) : Finset EdgeCode :=
  (V.product V).subtype (fun p => p.1 < p.2)

@[simp] theorem mem_vertexPairs (V : Finset ℕ) (e : EdgeCode) :
    e ∈ vertexPairs V ↔ e.1.1 ∈ V ∧ e.1.2 ∈ V := by
  simp [vertexPairs]

def observations (G : GraphCode) (e : EdgeCode) (n : ℕ) : Finset EdgeCode := by
  classical
  exact if h : GraphLocallyFinite G then
    vertexPairs (IntrinsicExhaustion.edgeBallSubgraph G h e n).1 else ∅

@[simp] theorem mem_observations (G : GraphCode) (e a : EdgeCode) (n : ℕ) :
    a ∈ observations G e n ↔ GraphLocallyFinite G ∧
      a.1.1 ∈ IntrinsicExhaustion.edgeBall G e n ∧
      a.1.2 ∈ IntrinsicExhaustion.edgeBall G e n := by
  classical
  by_cases h : GraphLocallyFinite G <;> simp [observations, h]

end Problem336.AllPairObservation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_BinaryLawUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem336.BinaryLaw

def signedCylinder {I : Type*} (A B : Finset I) : Set (I → Bool) :=
  {x | (∀ e ∈ A, x e = true) ∧ (∀ e ∈ B, x e = false)}

end Problem336.BinaryLaw

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FUSFLawUnique
attribute [-instance] _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal Topology

namespace Problem336

def configurationCylinder (A B : Finset EdgeCode) : Set EdgeConfiguration :=
  {x | (∀ e ∈ A, x e = true) ∧ (∀ e ∈ B, x e = false)}

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_Picard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter MeasureTheory Set
open scoped Topology BigOperators

namespace Problem336.Picard

variable {ι : Type*}

def iterate (w : ι → ℝ → ℝ) (b : ℝ → (ι → ℝ) → ι → ℝ) :
    ℕ → ι → ℝ → ℝ
  | 0 => w
  | n + 1 => fun i t => w i t +
      ∫ s in (0 : ℝ)..t, b s (fun j => iterate w b n j s) i

def majorant (L T : ℝ) (n : ℕ) : ℝ :=
  L ^ n * T ^ (n + 1) / (n + 1).factorial

def decode (w : ι → ℝ → ℝ) (b : ℝ → (ι → ℝ) → ι → ℝ) (i : ι) (t : ℝ) : ℝ :=
  Filter.limUnder atTop (fun n => iterate w b n i t)

end Problem336.Picard

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FactorAssembly
attribute [-instance] _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace Problem336
namespace FactorAssembly

abbrev EdgeField := EdgeCode → ℝ
abbrev GraphDrift := GraphCode → ℝ → EdgeField → EdgeCode → ℝ
abbrev GraphNoise := GraphCode → (ℕ → ℝ) → EdgeCode → ℝ → ℝ

def DriftBorel (b : GraphDrift) : Prop :=
  ∀ e, Measurable (fun p : GraphCode × (ℝ × EdgeField) => b p.1 p.2.1 p.2.2 e)

def NoiseBorel (w : GraphNoise) : Prop :=
  ∀ e, Measurable (fun p : (GraphCode × (ℕ → ℝ)) × ℝ => w p.1.1 p.1.2 e p.2)

def DriftEquivariant (b : GraphDrift) : Prop :=
  ∀ (σ : Equiv ℕ ℕ) (G : GraphCode) (t : ℝ) (y : EdgeField) (e : EdgeCode),
    b (relabelGraph σ G) t (fun f => y (mapEdge σ.symm f)) (mapEdge σ e) = b G t y e

def NoiseEquivariant (w : GraphNoise) : Prop :=
  ∀ (σ : Equiv ℕ ℕ) (G : GraphCode) (U : ℕ → ℝ) (e : EdgeCode) (t : ℝ),
    w (relabelGraph σ G) (relabelLabels σ U) (mapEdge σ e) t = w G U e t

def decodedSlope (b : GraphDrift) (w : GraphNoise)
    (G : GraphCode) (U : ℕ → ℝ) (e : EdgeCode) (n : ℕ) : ℝ :=
  Picard.decode (w G U) (b G) e (n : ℝ) / (n : ℝ)

def rule (b : GraphDrift) (w : GraphNoise) : FactorRule := by
  classical
  exact fun G U e =>
    if (1 / 2 : ℝ) < limsup (decodedSlope b w G U e) atTop then true else false

end FactorAssembly
end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_BitRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators NNReal

namespace Problem336

def bitValue (b : Bool) : ℝ := if b then 1 else 0

def slopeReadout (z : ℕ → ℝ) : Bool :=
  if (1 / 2 : ℝ) < limsup (fun n : ℕ => z (n + 1) / (n + 1 : ℝ)) atTop
  then true else false

def configurationReadout {I : Type*} (z : I → ℕ → ℝ) : I → Bool :=
  fun i => slopeReadout (z i)

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_PicardBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter MeasureTheory
open scoped Topology NNReal

namespace Problem336.DeterministicDecoder

def picardBound (L T : ℝ) (n : ℕ) : ℝ :=
  L ^ n * T ^ (n + 1) / (n + 1).factorial

end Problem336.DeterministicDecoder

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_PicardUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace Problem336.DeterministicDecoder

@[simp] theorem picardBound_zero (L t : ℝ) : picardBound L t 0 = t := by
  simp [picardBound]

def BoundedDifferenceResponse {I : Type*}
    (b : ℝ → (I → ℝ) → I → ℝ) (L : ℝ) : Prop :=
  ∀ t, 0 ≤ t → ∀ y y' : I → ℝ, ∀ d : ℝ, 0 ≤ d →
    (∀ i, |y i - y' i| ≤ d) → ∀ i, |b t y i - b t y' i| ≤ L * d

end Problem336.DeterministicDecoder

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_PicardSamplerLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem336.PicardSampler

def decodedIntegers {I W : Type*} (w : W → I → ℝ → ℝ)
    (b : ℝ → (I → ℝ) → I → ℝ) (q : W) : I → ℕ → ℝ :=
  fun i n => Picard.decode (w q) b i n

def sample {I W : Type*} (w : W → I → ℝ → ℝ)
    (b : ℝ → (I → ℝ) → I → ℝ) (q : W) : I → Bool :=
  configurationReadout (decodedIntegers w b q)

end Problem336.PicardSampler

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_PicardNonnegativeTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter MeasureTheory
open scoped Topology NNReal

namespace Problem336.Picard.NonnegativeTime

variable {ι : Type*}

def extendInput (w : ι → ℝ≥0 → ℝ) (i : ι) (t : ℝ) : ℝ :=
  w i (Real.toNNReal t)

@[simp] theorem extendInput_coe (w : ι → ℝ≥0 → ℝ) (i : ι) (t : ℝ≥0) :
    extendInput w i (t : ℝ) = w i t := by
  simp only [extendInput, Real.toNNReal_coe]

end Problem336.Picard.NonnegativeTime

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_PicardNonnegativeSampler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem336.PicardSampler.NonnegativeTime

open Picard.NonnegativeTime

def sample {I W : Type*} (w : W → I → ℝ≥0 → ℝ)
    (b : ℝ → (I → ℝ) → I → ℝ) (q : W) : I → Bool :=
  PicardSampler.sample (fun q => extendInput (w q)) b q

end Problem336.PicardSampler.NonnegativeTime

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_DenseBrownian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal Topology Matrix

namespace Problem336.DenseBrownian

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {X : ℝ≥0 → Ω → ℝ}

def evaluationChar {ι : Type*} [Fintype ι] (X : ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (a : ι → ℝ) (t : ι → ℝ≥0) : ℂ :=
  ∫ ω, Complex.exp ((((∑ i, a i * X (t i) ω) : ℝ) : ℂ) * Complex.I) ∂P

def brownianChar {ι : Type*} [Fintype ι] (a : ι → ℝ) (t : ι → ℝ≥0) : ℂ :=
  Complex.exp (-(((∑ i, ∑ j, a i * a j * min (t i : ℝ) (t j : ℝ)) : ℝ) : ℂ) / 2)

lemma continuous_evaluationChar [IsFiniteMeasure P] {ι : Type*} [Fintype ι]
    (hX : ∀ t, Measurable (X t)) (hc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (a : ι → ℝ) : Continuous (evaluationChar X P a) := by
  classical
  unfold evaluationChar
  apply continuous_of_dominated (bound := fun _ => (1 : ℝ))
  · intro t
    apply Measurable.aestronglyMeasurable
    fun_prop
  · intro t
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Complex.norm_exp_ofReal_mul_I])
  · exact integrable_const 1
  · filter_upwards [hc] with ω hω
    have hi (i : ι) : Continuous (fun t : ι → ℝ≥0 => a i * X (t i) ω) :=
      continuous_const.mul (hω.comp (continuous_apply i))
    fun_prop

lemma continuous_brownianChar {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    Continuous (brownianChar a) := by
  unfold brownianChar
  fun_prop

theorem characteristic_of_dense [IsFiniteMeasure P] {D : Set ℝ≥0} (hD : Dense D)
    (hX : ∀ t, Measurable (X t)) (hc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (hd : ∀ t : ι → ℝ≥0, (∀ i, t i ∈ D) →
      evaluationChar X P a t = brownianChar a t) :
    ∀ t : ι → ℝ≥0, evaluationChar X P a t = brownianChar a t := by
  have hpi : Dense (Set.pi Set.univ (fun _ : ι => D)) :=
    dense_pi Set.univ (fun _ _ => hD)
  have heq := Continuous.ext_on hpi (continuous_evaluationChar hX hc a)
    (continuous_brownianChar a) (fun t ht => hd t (fun i => ht i (Set.mem_univ i)))
  exact fun t => congrFun heq t

lemma evaluationChar_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (a : κ → ℝ) (t : κ → ℝ≥0) :
    evaluationChar X P (a ∘ e) (t ∘ e) = evaluationChar X P a t := by
  unfold evaluationChar
  congr 1
  funext ω
  simp only [Function.comp_apply]
  rw [e.sum_comp (fun i => a i * X (t i) ω)]

lemma brownianChar_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (a : κ → ℝ) (t : κ → ℝ≥0) :
    brownianChar (a ∘ e) (t ∘ e) = brownianChar a t := by
  unfold brownianChar
  simp only [Function.comp_apply]
  have hs : (∑ i : ι, ∑ j : ι,
      a (e i) * a (e j) * min (t (e i) : ℝ) (t (e j) : ℝ)) =
      ∑ i : κ, ∑ j : κ, a i * a j * min (t i : ℝ) (t j : ℝ) := by
    calc
      _ = ∑ i : ι, ∑ j : κ, a (e i) * a j * min (t (e i) : ℝ) (t j : ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        exact e.sum_comp (fun j => a (e i) * a j * min (t (e i) : ℝ) (t j : ℝ))
      _ = _ := e.sum_comp (fun i => ∑ j : κ, a i * a j * min (t i : ℝ) (t j : ℝ))
  rw [hs]

theorem isPreBrownian_of_characteristic [IsProbabilityMeasure P]
    (hX : ∀ t, Measurable (X t))
    (hchar : ∀ (I : Finset ℝ≥0) (a : I → ℝ),
      evaluationChar X P a (fun i => i.val) = brownianChar a (fun i => i.val)) :
    IsPreBrownianReal X P := by
  classical
  refine ⟨fun I => ?_⟩
  have hm : Measurable (fun ω => I.restrict (X · ω)) := by
    exact Measurable.of_eval (fun i => hX i.val)
  refine ⟨hm.aemeasurable, ?_⟩
  apply (MeasurableEquiv.toLp 2 (I → ℝ)).map_measurableEquiv_injective
  rw [Measure.map_map (MeasurableEquiv.measurable _) hm]
  rw [MeasurableEquiv.coe_toLp]
  rw [(BrownianReal.measurePreserving_toLp_projectiveFamily I).map_eq]
  apply Measure.ext_of_charFun
  funext a
  rw [charFun_apply, integral_map]
  · rw [charFun_multivariateGaussian (BrownianReal.posSemidef_covMatrix I)]
    have hinner (ω : Ω) :
        inner (𝕜 := ℝ) (WithLp.toLp 2 (I.restrict (X · ω))) a =
          ∑ i : I, a i * X i.val ω := by
      simp [PiLp.inner_apply, Finset.restrict_def]
    simp_rw [Function.comp_apply, hinner]
    change evaluationChar X P (fun i => a i) (fun i => i.val) = _
    rw [hchar]
    unfold brownianChar
    congr 1
    simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
    simp only [dotProduct, Matrix.mulVec, BrownianReal.covMatrix_apply]
    simp_rw [Finset.mul_sum]
    have hsum : (∑ i : I, ∑ j : I, a i * a j * min (i.val : ℝ) (j.val : ℝ)) =
        ∑ i : I, ∑ j : I, a i * ((min i.val j.val : ℝ≥0) * a j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [NNReal.coe_min]
      ring
    rw [hsum]
    ring
  · simpa only [MeasurableEquiv.coe_toLp] using
      ((MeasurableEquiv.toLp 2 (I → ℝ)).measurable.comp hm).aemeasurable
  · fun_prop

theorem isBrownian_of_dense_characteristic [IsProbabilityMeasure P]
    {D : Set ℝ≥0} (hD : Dense D) (hX : ∀ t, Measurable (X t))
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hchar : ∀ (I : Finset ℝ≥0) (a : I → ℝ) (t : I → ℝ≥0),
      (∀ i, t i ∈ D) → evaluationChar X P a t = brownianChar a t) :
    IsBrownianReal X P := by
  refine ⟨isPreBrownian_of_characteristic hX ?_, hc⟩
  intro I a
  exact characteristic_of_dense hD hX hc a (hchar I a) (fun i => i.val)

theorem isBrownian_of_dense_characteristic_fin [IsProbabilityMeasure P]
    {D : Set ℝ≥0} (hD : Dense D) (hX : ∀ t, Measurable (X t))
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hchar : ∀ (n : ℕ) (a : Fin n → ℝ) (t : Fin n → ℝ≥0),
      (∀ i, t i ∈ D) → evaluationChar X P a t = brownianChar a t) :
    IsBrownianReal X P := by
  apply isBrownian_of_dense_characteristic hD hX hc
  intro I a t ht
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have h := hchar (Fintype.card I) (a ∘ e) (t ∘ e) (fun i => ht (e i))
  rwa [evaluationChar_reindex e a t, brownianChar_reindex e a t] at h

def dyadicTimes : Set ℝ≥0 :=
  {t | ∃ n k : ℕ, t = (k : ℝ≥0) / (2 : ℝ≥0) ^ n}

lemma dense_dyadicTimes : Dense dyadicTimes := by
  intro t
  let q : ℕ → ℝ≥0 := fun n =>
    (⌊(t : ℝ) * (2 : ℝ) ^ n⌋₊ : ℝ≥0) / (2 : ℝ≥0) ^ n
  have hq : Filter.Tendsto q Filter.atTop (nhds t) := by
    apply NNReal.tendsto_coe.mp
    have h := (tendsto_nat_floor_mul_div_atTop t.property).comp
      (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num))
    convert h using 1 <;> simp [q, Function.comp_def]
  apply mem_closure_of_tendsto hq
  exact Filter.Eventually.of_forall (fun n => ⟨n, ⌊(t : ℝ) * (2 : ℝ) ^ n⌋₊, rfl⟩)

end Problem336.DenseBrownian

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_DenseGaussianModification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal Topology

namespace Problem336.DenseBrownian

variable {Ω J : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {Y : J → Ω → ℝ} {τ : J → ℝ≥0}

lemma characteristic_of_gaussian_family [IsProbabilityMeasure P]
    (hY : IsGaussianProcess Y P) (hm : ∀ j, ∫ ω, Y j ω ∂P = 0)
    (hv : ∀ i j, cov[Y i, Y j; P] = min (τ i : ℝ) (τ j : ℝ))
    {ι : Type*} [Fintype ι] (b : ι → J) (a : ι → ℝ) :
    (∫ ω, Complex.exp ((((∑ i, a i * Y (b i) ω) : ℝ) : ℂ) * Complex.I) ∂P) =
      brownianChar a (τ ∘ b) := by
  classical
  let Z : Ω → ℝ := fun ω => ∑ i, a i * Y (b i) ω
  have hZ : HasGaussianLaw Z P := by
    simpa [Z, Function.comp_def, smul_eq_mul] using
      ((hY.comp_right b).smul a).hasGaussianLaw_fun_sum (I := Finset.univ)
  have hmean : ∫ ω, Z ω ∂P = 0 := by
    dsimp [Z]
    rw [integral_finsetSum]
    · simp [integral_const_mul, hm]
    · intro i _
      exact (hY.hasGaussianLaw_eval (b i)).integrable.const_mul (a i)
  have hmem (i : ι) : MemLp (fun ω => a i * Y (b i) ω) 2 P :=
    (hY.hasGaussianLaw_eval (b i)).memLp_two.const_mul (a i)
  have hvar : Var[Z; P] = ∑ i, ∑ j,
      a i * a j * min (τ (b i) : ℝ) (τ (b j) : ℝ) := by
    rw [← covariance_self hZ.aemeasurable]
    dsimp [Z]
    rw [covariance_fun_sum_fun_sum hmem hmem]
    simp_rw [covariance_const_mul_left, covariance_const_mul_right, hv]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hc := hZ.charFun_map_eq (1 : ℝ)
  simp only [Real.inner_apply, one_mul] at hc
  rw [hmean, hvar] at hc
  have hi : charFun (P.map Z) (1 : ℝ) =
      ∫ ω, Complex.exp (((Z ω : ℝ) : ℂ) * Complex.I) ∂P := by
    rw [charFun_apply, integral_map hZ.aemeasurable (by fun_prop)]
    simp
  rw [hi] at hc
  simpa [Z, brownianChar, Function.comp_def, neg_div] using hc

theorem isBrownian_of_dense_gaussian_modification [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → ℝ} {D : Set ℝ≥0} (hD : Dense D)
    (hX : ∀ t, Measurable (X t))
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hY : IsGaussianProcess Y P) (hm : ∀ j, ∫ ω, Y j ω ∂P = 0)
    (hv : ∀ i j, cov[Y i, Y j; P] = min (τ i : ℝ) (τ j : ℝ))
    (hmod : ∀ t ∈ D, ∃ j, τ j = t ∧ X t =ᵐ[P] Y j) :
    IsBrownianReal X P := by
  classical
  apply isBrownian_of_dense_characteristic_fin hD hX hc
  intro n a t ht
  choose b hb heq using fun i => hmod (t i) (ht i)
  have ha : ∀ᵐ ω ∂P, ∀ i, X (t i) ω = Y (b i) ω :=
    ae_all_iff.mpr heq
  have hi : evaluationChar X P a t =
      ∫ ω, Complex.exp ((((∑ i, a i * Y (b i) ω) : ℝ) : ℂ) * Complex.I) ∂P := by
    unfold evaluationChar
    apply integral_congr_ae
    filter_upwards [ha] with ω hω
    simp_rw [hω]
  rw [hi, characteristic_of_gaussian_family hY hm hv b a]
  congr 1
  funext i
  exact hb i

end Problem336.DenseBrownian

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_PathConcatenation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Problem336.PathConcatenation
abbrev UnitPath := C(Set.Icc (0 : ℝ) 1, ℝ)
local instance instMeasurableSpaceUnitPath : MeasurableSpace UnitPath := borel UnitPath
local instance instBorelSpaceUnitPath : BorelSpace UnitPath := ⟨rfl⟩
local instance instMeasurableSpaceContinuousMapReal_solutions : MeasurableSpace C(ℝ, ℝ) := borel C(ℝ, ℝ)
local instance instBorelSpaceContinuousMapReal_solutions : BorelSpace C(ℝ, ℝ) := ⟨rfl⟩
def leftEnd : Set.Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
def rightEnd : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩

def segment (w : ℕ → UnitPath) (k : ℕ) (t : ℝ) : ℝ :=
  w k (Set.projIcc 0 1 (by norm_num) (t - k)) - w k leftEnd
theorem continuous_segment (w : ℕ → UnitPath) (k : ℕ) : Continuous (segment w k) := by
  unfold segment
  exact ((w k).continuous.comp (continuous_projIcc.comp
    (continuous_id.sub continuous_const))).sub continuous_const
theorem segment_eq_zero_of_le (w : ℕ → UnitPath) (k : ℕ) {t : ℝ}
    (ht : t ≤ k) : segment w k t = 0 := by
  unfold segment
  rw [Set.projIcc_of_le_left _ (sub_nonpos.mpr ht)]
  exact sub_self _
theorem segment_eq_endpoint_of_ge (w : ℕ → UnitPath) (k : ℕ) {t : ℝ}
    (ht : (k : ℝ) + 1 ≤ t) : segment w k t = w k rightEnd - w k leftEnd := by
  unfold segment
  rw [Set.projIcc_of_right_le _ (by linarith : (1 : ℝ) ≤ t - k)]
  rfl

def concat (w : ℕ → UnitPath) (t : ℝ) : ℝ := ∑' k, segment w k t
theorem concat_eq_sum (w : ℕ → UnitPath) (N : ℕ) {t : ℝ} (ht : t ≤ N) :
    concat w t = ∑ k ∈ Finset.range N, segment w k t := by
  apply tsum_eq_sum
  intro k hk
  apply segment_eq_zero_of_le
  exact ht.trans (by exact_mod_cast (Nat.le_of_not_gt (fun h => hk (Finset.mem_range.mpr h))))
theorem continuous_concat (w : ℕ → UnitPath) : Continuous (concat w) := by
  rw [continuous_iff_continuousAt]
  intro t
  obtain ⟨N, hN⟩ := exists_nat_gt t
  have hc : Continuous (fun s => ∑ k ∈ Finset.range N, segment w k s) :=
    continuous_finsetSum _ (fun k _ => continuous_segment w k)
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hN] with s hs
  exact concat_eq_sum w N (le_of_lt hs)

def concatPath (w : ℕ → UnitPath) : C(ℝ, ℝ) := ⟨concat w, continuous_concat w⟩
@[simp] theorem concat_nonpos (w : ℕ → UnitPath) {t : ℝ} (ht : t ≤ 0) : concat w t = 0 := by
  simpa using concat_eq_sum w 0 (by simpa using ht)
theorem continuous_segment_joint (k : ℕ) :
    Continuous (fun q : (ℕ → UnitPath) × ℝ => segment q.1 k q.2) := by
  unfold segment
  have hw : Continuous (fun q : (ℕ → UnitPath) × ℝ => q.1 k) :=
    (continuous_apply k).comp continuous_fst
  have ht : Continuous (fun q : (ℕ → UnitPath) × ℝ =>
      Set.projIcc (0 : ℝ) 1 (by norm_num) (q.2 - k)) :=
    continuous_projIcc.comp (continuous_snd.sub continuous_const)
  exact (continuous_eval.comp (hw.prodMk ht)).sub
    (continuous_eval.comp (hw.prodMk continuous_const))

theorem continuous_concat_joint :
    Continuous (fun q : (ℕ → UnitPath) × ℝ => concat q.1 q.2) := by
  rw [continuous_iff_continuousAt]
  intro q
  obtain ⟨N, hN⟩ := exists_nat_gt q.2
  have hc : Continuous (fun p : (ℕ → UnitPath) × ℝ =>
      ∑ k ∈ Finset.range N, segment p.1 k p.2) :=
    continuous_finsetSum _ (fun k _ => continuous_segment_joint k)
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (Iio_mem_nhds hN)] with p hp
  exact concat_eq_sum p.1 N (le_of_lt hp)

theorem continuous_concatPath : Continuous concatPath :=
  ContinuousMap.continuous_of_continuous_uncurry _ continuous_concat_joint

theorem measurable_concatPath : Measurable concatPath := continuous_concatPath.measurable

theorem segment_at_nat_add (w : ℕ → UnitPath) (n : ℕ)
    (x : Set.Icc (0 : ℝ) 1) :
    segment w n ((n : ℝ) + x) = w n x - w n leftEnd := by
  unfold segment
  rw [add_sub_cancel_left, Set.projIcc_of_mem _ x.property]

theorem concat_nat_add (w : ℕ → UnitPath) (n : ℕ)
    (x : Set.Icc (0 : ℝ) 1) :
    concat w ((n : ℝ) + x) =
      (∑ k ∈ Finset.range n, (w k rightEnd - w k leftEnd)) +
        (w n x - w n leftEnd) := by
  rw [concat_eq_sum w (n + 1) (by push_cast; linarith [x.property.2]),
    Finset.sum_range_succ, segment_at_nat_add]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  apply segment_eq_endpoint_of_ge
  have hkn : (k : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.mp hk
  linarith [x.property.1]

end Problem336.PathConcatenation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CountableProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Finset Preorder
open scoped ENNReal

namespace Problem336.CountableProjective

variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]

abbrev Prefix (X : Type*) (n : ℕ) := Finset.Iic n → X

def stepEquiv (n : ℕ) : (Prefix X n × X) ≃ᵐ Prefix X (n + 1) :=
  ((MeasurableEquiv.refl (Prefix X n)).prodCongr
    (MeasurableEquiv.piSingleton (X := fun _ => X) n)).trans
    (MeasurableEquiv.IicProdIoc (X := fun _ => X) n.le_succ)

variable (P : (n : ℕ) → Measure (Prefix X n)) [probabilityPrefixes : ∀ n, IsProbabilityMeasure (P n)]

def stepLaw (n : ℕ) : Measure (Prefix X n × X) :=
  (P (n + 1)).map (stepEquiv n).symm

instance stepLaw_probability (n : ℕ) : IsProbabilityMeasure (stepLaw P n) := by
  unfold stepLaw
  infer_instance

def transition (n : ℕ) : Kernel (Prefix X n) X :=
  (stepLaw P n).condKernel

instance transition_markov (n : ℕ) : IsMarkovKernel (transition P n) := by
  unfold transition
  infer_instance

variable (hP : ∀ n, (P (n + 1)).map (frestrictLe₂ (π := fun _ => X) n.le_succ) = P n)

include hP

omit [StandardBorelSpace X] [Nonempty X] [∀ n, IsProbabilityMeasure (P n)] in
lemma stepLaw_fst (n : ℕ) : (stepLaw P n).fst = P n := by
  rw [Measure.fst, stepLaw, Measure.map_map measurable_fst (stepEquiv n).symm.measurable]
  exact hP n

include probabilityPrefixes in
lemma compProd_transition (n : ℕ) : P n ⊗ₘ transition P n = stepLaw P n := by
  rw [← stepLaw_fst P hP n]
  exact (stepLaw P n).disintegrate (stepLaw P n).condKernel

lemma partialTraj_step (n : ℕ) :
    Kernel.partialTraj (X := fun _ => X) (transition P) n (n + 1) ∘ₘ P n = P (n + 1) := by
  have hg : Measurable (IicProdIoc (X := fun _ => X) n (n + 1)) :=
    measurable_IicProdIoc
  rw [Kernel.partialTraj_succ_self,
    ← Measure.map_comp _ _ hg,
    ← Measure.compProd_eq_comp_prod,
    Measure.compProd_map (MeasurableEquiv.piSingleton (X := fun _ => X) n).measurable,
    compProd_transition P hP n,
    Measure.map_map hg
      (measurable_id.prodMap (MeasurableEquiv.piSingleton (X := fun _ => X) n).measurable)]
  change (stepLaw P n).map (stepEquiv n) = P (n + 1)
  exact (stepEquiv n).map_map_symm

lemma partialTraj_initial (n : ℕ) :
    Kernel.partialTraj (X := fun _ => X) (transition P) 0 n ∘ₘ P 0 = P n := by
  induction n with
  | zero => rw [Kernel.partialTraj_self, Measure.id_comp]
  | succ n ih =>
      rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n),
        ← Measure.comp_assoc, ih, partialTraj_step P hP n]

theorem exists_measure_prefix :
    ∃ μ : Measure (ℕ → X), IsProbabilityMeasure μ ∧
      ∀ n, μ.map (frestrictLe (π := fun _ => X) n) = P n := by
  let μ : Measure (ℕ → X) := Kernel.traj (X := fun _ => X) (transition P) 0 ∘ₘ P 0
  refine ⟨μ, inferInstance, ?_⟩
  intro n
  change (Kernel.traj (X := fun _ => X) (transition P) 0 ∘ₘ P 0).map (frestrictLe n) = P n
  rw [Measure.map_comp _ _ (measurable_frestrictLe n),
    Kernel.traj_map_frestrictLe]
  exact partialTraj_initial P hP n

omit hP

theorem exists_projectiveLimit
    (Q : (s : Finset ℕ) → Measure (s → X)) [∀ s, IsProbabilityMeasure (Q s)]
    (hQ : IsProjectiveMeasureFamily (α := fun _ : ℕ => X) Q) :
    ∃ μ : Measure (ℕ → X), IsProbabilityMeasure μ ∧ IsProjectiveLimit (α := fun _ : ℕ => X) μ Q := by
  obtain ⟨μ, hμ, hmarg⟩ := exists_measure_prefix (fun n => Q (Iic n))
    (fun n => (hQ (Iic (n + 1)) (Iic n) (Iic_subset_Iic.mpr n.le_succ)).symm)
  exact ⟨μ, hμ, (isProjectiveLimit_nat_iff hQ μ).mpr hmarg⟩

end Problem336.CountableProjective

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CountableBrownian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace Problem336.CountableBrownian

open BrownianReal

def pullbackTimes (τ : ℕ → ℝ≥0) (I : Finset ℕ) :
    ((I.image τ) → ℝ) → (I → ℝ) :=
  fun x i => x ⟨τ i, Finset.mem_image.mpr ⟨i, i.property, rfl⟩⟩

@[fun_prop]
lemma measurable_pullbackTimes (τ : ℕ → ℝ≥0) (I : Finset ℕ) :
    Measurable (pullbackTimes τ I) := by
  exact Measurable.of_eval (fun i => measurable_pi_apply _)

def family (τ : ℕ → ℝ≥0) (I : Finset ℕ) : Measure (I → ℝ) :=
  (projectiveFamily (I.image τ)).map (pullbackTimes τ I)

instance family_probability (τ : ℕ → ℝ≥0) (I : Finset ℕ) :
    IsProbabilityMeasure (family τ I) := by
  unfold family
  exact Measure.isProbabilityMeasure_map (measurable_pullbackTimes τ I).aemeasurable

instance family_isGaussian (τ : ℕ → ℝ≥0) (I : Finset ℕ) :
    IsGaussian (family τ I) := by
  let L : ((I.image τ) → ℝ) →L[ℝ] (I → ℝ) :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj
      ⟨τ i, Finset.mem_image.mpr ⟨i, i.property, rfl⟩⟩)
  have h : HasGaussianLaw (pullbackTimes τ I) (projectiveFamily (I.image τ)) :=
    (IsGaussian.hasGaussianLaw_id (μ := projectiveFamily (I.image τ))).map L
  exact h.isGaussian_map

lemma family_projective (τ : ℕ → ℝ≥0) :
    IsProjectiveMeasureFamily (α := fun _ : ℕ => ℝ) (family τ) := by
  classical
  intro I J hJI
  unfold family
  rw [isProjectiveMeasureFamily_projectiveFamily (I.image τ) (J.image τ)
    (Finset.image_subset_image hJI)]
  rw [Measure.map_map (measurable_pullbackTimes τ J)
      (Finset.measurable_restrict₂ (X := fun _ : ℝ≥0 => ℝ) (Finset.image_subset_image hJI)),
    Measure.map_map (Finset.measurable_restrict₂ (X := fun _ : ℕ => ℝ) hJI) (measurable_pullbackTimes τ I)]
  congr 1

theorem exists_countable_brownian_law (τ : ℕ → ℝ≥0) :
    ∃ μ : Measure (ℕ → ℝ), IsProbabilityMeasure μ ∧
      IsProjectiveLimit (α := fun _ : ℕ => ℝ) μ (family τ) :=
  CountableProjective.exists_projectiveLimit (family τ) (family_projective τ)

theorem hasLaw_increment {τ : ℕ → ℝ≥0} {μ : Measure (ℕ → ℝ)}
    (hμ : IsProjectiveLimit (α := fun _ : ℕ => ℝ) μ (family τ)) (i j : ℕ) :
    HasLaw (fun ω => ω i - ω j) (gaussianReal 0 (nndist (τ i) (τ j))) μ := by
  classical
  let I : Finset ℕ := {i, j}
  let a : I := ⟨i, by simp [I]⟩
  let b : I := ⟨j, by simp [I]⟩
  have hX : HasLaw (pullbackTimes τ I) (family τ I)
      (projectiveFamily (I.image τ)) :=
    ⟨(measurable_pullbackTimes τ I).aemeasurable, rfl⟩
  have hY : HasLaw I.restrict (family τ I) μ :=
    ⟨(Finset.measurable_restrict I).aemeasurable, hμ I⟩
  have hD : HasLaw (fun x => pullbackTimes τ I x a - pullbackTimes τ I x b)
      (gaussianReal 0 (nndist (τ i) (τ j))) (projectiveFamily (I.image τ)) :=
    (measurePreserving_eval_sub_eval_projectiveFamily (I.image τ)
      ⟨τ i, Finset.mem_image.mpr ⟨i, by simp [I], rfl⟩⟩
      ⟨τ j, Finset.mem_image.mpr ⟨j, by simp [I], rfl⟩⟩).hasLaw
  exact HasLaw.comp_of_hasLaw_comp (f := fun x : I → ℝ => x a - x b)
    (by fun_prop) hX hY hD

theorem hasLaw_eval {τ : ℕ → ℝ≥0} {μ : Measure (ℕ → ℝ)}
    (hμ : IsProjectiveLimit (α := fun _ : ℕ => ℝ) μ (family τ)) (i : ℕ) :
    HasLaw (fun ω => ω i) (gaussianReal 0 (τ i)) μ := by
  classical
  let I : Finset ℕ := {i}
  let a : I := ⟨i, by simp [I]⟩
  have hX : HasLaw (pullbackTimes τ I) (family τ I)
      (projectiveFamily (I.image τ)) :=
    ⟨(measurable_pullbackTimes τ I).aemeasurable, rfl⟩
  have hY : HasLaw I.restrict (family τ I) μ :=
    ⟨(Finset.measurable_restrict I).aemeasurable, hμ I⟩
  have hE : HasLaw (fun x => pullbackTimes τ I x a)
      (gaussianReal 0 (τ i)) (projectiveFamily (I.image τ)) :=
    (measurePreserving_eval_projectiveFamily
      ⟨τ i, Finset.mem_image.mpr ⟨i, by simp [I], rfl⟩⟩).hasLaw
  exact HasLaw.comp_of_hasLaw_comp (f := fun x : I → ℝ => x a)
    (measurable_pi_apply a).aemeasurable hX hY hE

theorem isGaussianProcess {τ : ℕ → ℝ≥0} {μ : Measure (ℕ → ℝ)}
    (hμ : IsProjectiveLimit (α := fun _ : ℕ => ℝ) μ (family τ)) :
    IsGaussianProcess (fun i ω => ω i) μ where
  hasGaussianLaw I :=
    (show HasLaw I.restrict (family τ I) μ from
      ⟨(Finset.measurable_restrict I).aemeasurable, hμ I⟩).hasGaussianLaw

lemma integral_eval {τ : ℕ → ℝ≥0} {μ : Measure (ℕ → ℝ)}
    (hμ : IsProjectiveLimit (α := fun _ : ℕ => ℝ) μ (family τ)) (i : ℕ) :
    ∫ ω, ω i ∂μ = 0 := by
  rw [(hasLaw_eval hμ i).integral_eq, integral_id_gaussianReal]

lemma covariance_eval {τ : ℕ → ℝ≥0} {μ : Measure (ℕ → ℝ)}
    (hμ : IsProjectiveLimit (α := fun _ : ℕ => ℝ) μ (family τ)) (i j : ℕ) :
    cov[fun ω => ω i, fun ω => ω j; μ] = min (τ i : ℝ) (τ j : ℝ) := by
  classical
  let I : Finset ℕ := {i, j}
  let a : I := ⟨i, by simp [I]⟩
  let b : I := ⟨j, by simp [I]⟩
  have hX : HasLaw (pullbackTimes τ I) (family τ I)
      (projectiveFamily (I.image τ)) :=
    ⟨(measurable_pullbackTimes τ I).aemeasurable, rfl⟩
  have hY : HasLaw I.restrict (family τ I) μ :=
    ⟨(Finset.measurable_restrict I).aemeasurable, hμ I⟩
  calc
    cov[fun ω => ω i, fun ω => ω j; μ] =
        cov[fun x : I → ℝ => x a, fun x : I → ℝ => x b; family τ I] :=
      hY.covariance_fun_comp (measurable_pi_apply a).aemeasurable
        (measurable_pi_apply b).aemeasurable
    _ = cov[fun x => pullbackTimes τ I x a, fun x => pullbackTimes τ I x b;
        projectiveFamily (I.image τ)] :=
      (hX.covariance_fun_comp (measurable_pi_apply a).aemeasurable
        (measurable_pi_apply b).aemeasurable).symm
    _ = min (τ i : ℝ) (τ j : ℝ) := covariance_eval_projectiveFamily _ _ _

end Problem336.CountableBrownian

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_SchauderTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace Problem336.SchauderTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma measure_abs_gt_le_fourth_moment (Z : Ω → ℝ) (hZ : AEMeasurable Z P)
    (C : ℝ≥0∞) (hC : ∫⁻ ω, ‖Z ω‖ₑ ^ (4 : ℕ) ∂P ≤ C)
    (b : ℝ) (hb : 0 < b) :
    P {ω | b < |Z ω|} ≤ C / (ENNReal.ofReal b) ^ (4 : ℕ) := by
  calc
    P {ω | b < |Z ω|} ≤ P {ω | (ENNReal.ofReal b) ^ (4 : ℕ) ≤ ‖Z ω‖ₑ ^ (4 : ℕ)} := by
      apply measure_mono
      intro ω hω
      change (ENNReal.ofReal b) ^ (4 : ℕ) ≤ ‖Z ω‖ₑ ^ (4 : ℕ)
      apply pow_le_pow_left₀ (by positivity)
      simpa [Real.enorm_eq_ofReal_abs] using ENNReal.ofReal_le_ofReal hω.le
    _ ≤ (∫⁻ ω, ‖Z ω‖ₑ ^ (4 : ℕ) ∂P) / (ENNReal.ofReal b) ^ (4 : ℕ) := by
      apply meas_ge_le_lintegral_div
      · fun_prop
      · exact pow_ne_zero _ (ENNReal.ofReal_ne_zero_iff.mpr hb)
      · finiteness
    _ ≤ C / (ENNReal.ofReal b) ^ (4 : ℕ) := by gcongr

lemma fourth_threshold_identity (C : ℝ≥0∞) (n : ℕ) :
    C / (ENNReal.ofReal ((4 / 3 : ℝ) ^ n)) ^ (4 : ℕ) =
      C * ENNReal.ofReal (81 / 256 : ℝ) ^ n := by
  rw [ENNReal.ofReal_pow (by norm_num), ← pow_mul, Nat.mul_comm n 4, pow_mul,
    div_eq_mul_inv, ENNReal.inv_pow]
  have hb : ((ENNReal.ofReal (4 / 3 : ℝ)) ^ (4 : ℕ))⁻¹ =
      ENNReal.ofReal (81 / 256 : ℝ) := by
    rw [← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_inv_of_pos (by positivity)]
    norm_num
  rw [hb]

lemma measure_bad_block_le (Z : (n : ℕ) → Fin (2 ^ n) → Ω → ℝ)
    (hZ : ∀ n k, AEMeasurable (Z n k) P) (C : ℝ≥0∞)
    (hC : ∀ n k, ∫⁻ ω, ‖Z n k ω‖ₑ ^ (4 : ℕ) ∂P ≤ C) (n : ℕ) :
    P {ω | ∃ k : Fin (2 ^ n), (4 / 3 : ℝ) ^ n < |Z n k ω|} ≤
      C * ENNReal.ofReal (81 / 128 : ℝ) ^ n := by
  classical
  calc
    P {ω | ∃ k : Fin (2 ^ n), (4 / 3 : ℝ) ^ n < |Z n k ω|} ≤
        ∑ k : Fin (2 ^ n), P {ω | (4 / 3 : ℝ) ^ n < |Z n k ω|} := by
      rw [show {ω | ∃ k : Fin (2 ^ n), (4 / 3 : ℝ) ^ n < |Z n k ω|} =
        ⋃ k : Fin (2 ^ n), {ω | (4 / 3 : ℝ) ^ n < |Z n k ω|} by ext ω; simp]
      exact measure_iUnion_fintype_le P _
    _ ≤ ∑ _k : Fin (2 ^ n), C * ENNReal.ofReal (81 / 256 : ℝ) ^ n := by
      apply Finset.sum_le_sum
      intro k _
      rw [← fourth_threshold_identity]
      exact measure_abs_gt_le_fourth_moment (Z n k) (hZ n k) C (hC n k) _
        (pow_pos (by norm_num) n)
    _ = C * ENNReal.ofReal (81 / 128 : ℝ) ^ n := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_ofNat]
      rw [mul_left_comm, ← mul_pow]
      have hr : (2 : ℝ≥0∞) * ENNReal.ofReal (81 / 256 : ℝ) =
          ENNReal.ofReal (81 / 128 : ℝ) := by
        calc
          (2 : ℝ≥0∞) * ENNReal.ofReal (81 / 256 : ℝ) =
              ENNReal.ofReal ((2 : ℝ) * (81 / 256)) := by
            simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
          _ = _ := by norm_num
      rw [hr]

theorem ae_eventually_dyadic_bound
    (Z : (n : ℕ) → Fin (2 ^ n) → Ω → ℝ)
    (hZ : ∀ n k, AEMeasurable (Z n k) P) (C : ℝ≥0∞) (hCfin : C < ∞)
    (hC : ∀ n k, ∫⁻ ω, ‖Z n k ω‖ₑ ^ (4 : ℕ) ∂P ≤ C) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ k : Fin (2 ^ n), |Z n k ω| ≤ (4 / 3 : ℝ) ^ n := by
  have hs : (∑' n, P {ω | ∃ k : Fin (2 ^ n), (4 / 3 : ℝ) ^ n < |Z n k ω|}) ≠ ∞ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (ENNReal.tsum_le_tsum (measure_bad_block_le Z hZ C hC))
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_lt_top hCfin (tsum_geometric_lt_top.mpr (ENNReal.ofReal_lt_one.mpr (by norm_num)))
  filter_upwards [ae_eventually_notMem hs] with ω hω
  filter_upwards [hω] with n hn
  simpa only [Set.mem_ofPred_eq, not_exists, not_lt] using hn

theorem ae_eventually_gaussian_dyadic_bound
    (Z : (n : ℕ) → Fin (2 ^ n) → Ω → ℝ)
    (hZ : ∀ n k, HasLaw (Z n k) (gaussianReal 0 1) P) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ k : Fin (2 ^ n), |Z n k ω| ≤ (4 / 3 : ℝ) ^ n := by
  let C : ℝ≥0∞ := ∫⁻ x : ℝ, ‖x‖ₑ ^ (4 : ℕ) ∂gaussianReal 0 1
  have hCfin : C < ∞ := by
    have hm := memLp_id_gaussianReal (μ := 0) (v := 1) (4 : ℝ≥0)
    have ht := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := (4 : ℝ≥0∞)) (by norm_num) (by norm_num) hm.2
    simpa [C] using ht
  apply ae_eventually_dyadic_bound Z (fun n k => (hZ n k).aemeasurable) C hCfin
  intro n k
  exact ((hZ n k).lintegral_comp (f := fun x : ℝ => ‖x‖ₑ ^ (4 : ℕ)) (by fun_prop)).le

def incrementRatio : ℝ := (4 / 3) / Real.sqrt 2

lemma incrementRatio_nonneg : 0 ≤ incrementRatio := by
  unfold incrementRatio
  positivity

lemma incrementRatio_lt_one : incrementRatio < 1 := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [incrementRatio, div_lt_one hs]
  nlinarith

lemma summable_incrementRatio : Summable (fun n : ℕ => incrementRatio ^ n) :=
  summable_geometric_of_lt_one incrementRatio_nonneg incrementRatio_lt_one

theorem ae_eventually_gaussian_increment_bound
    (D : (n : ℕ) → Fin (2 ^ n) → Ω → ℝ)
    (hD : ∀ n k, HasLaw (D n k) (gaussianReal 0 ((2 : ℝ≥0)⁻¹ ^ n)) P) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ k : Fin (2 ^ n), |D n k ω| ≤ incrementRatio ^ n := by
  let Z : (n : ℕ) → Fin (2 ^ n) → Ω → ℝ :=
    fun n k ω => (Real.sqrt 2) ^ n * D n k ω
  have hZ (n : ℕ) (k : Fin (2 ^ n)) : HasLaw (Z n k) (gaussianReal 0 1) P := by
    have hv : (NNReal.mk (((Real.sqrt 2) ^ n) ^ 2) (sq_nonneg _)) *
        ((2 : ℝ≥0)⁻¹ ^ n) = 1 := by
      apply NNReal.coe_injective
      simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_pow,
        NNReal.coe_inv, NNReal.coe_ofNat, NNReal.coe_one]
      rw [← pow_mul, Nat.mul_comm n 2, pow_mul, Real.sq_sqrt (by norm_num), ← mul_pow]
      norm_num
    have h := gaussianReal_const_mul (hD n k) ((Real.sqrt 2) ^ n)
    rw [mul_zero, hv] at h
    exact h
  filter_upwards [ae_eventually_gaussian_dyadic_bound Z hZ] with ω hω
  filter_upwards [hω] with n hn
  intro k
  have hk := hn k
  have hs : 0 < (Real.sqrt 2) ^ n := pow_pos (Real.sqrt_pos.2 (by norm_num)) _
  rw [incrementRatio, div_pow]
  apply (le_div_iff₀ hs).2
  simpa [Z, abs_mul, abs_of_pos hs, mul_comm] using hk

theorem ae_all_eventually_gaussian_increment_bound {I : Type*} [Countable I]
    (D : I → (n : ℕ) → Fin (2 ^ n) → Ω → ℝ)
    (hD : ∀ i n k, HasLaw (D i n k) (gaussianReal 0 ((2 : ℝ≥0)⁻¹ ^ n)) P) :
    ∀ᵐ ω ∂P, ∀ i, ∀ᶠ n in atTop, ∀ k : Fin (2 ^ n),
      |D i n k ω| ≤ incrementRatio ^ n := by
  apply ae_all_iff.mpr
  intro i
  exact ae_eventually_gaussian_increment_bound (D i) (hD i)

end Problem336.SchauderTail

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_DyadicGaussianBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace Problem336.DyadicGaussianBound

variable {τ : ℕ → ℝ≥0} {μ : Measure (ℕ → ℝ)}

theorem ae_time_consistent
    (hμ : IsProjectiveLimit (α := fun _ : ℕ => ℝ) μ (CountableBrownian.family τ)) :
    ∀ᵐ ω ∂μ, ∀ i j, τ i = τ j → ω i = ω j := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : τ i = τ j
  · have h := CountableBrownian.hasLaw_increment hμ i j
    rw [hij, nndist_self, gaussianReal_zero_var] at h
    filter_upwards [h.ae_eq_of_dirac] with ω hω
    exact fun _ => sub_eq_zero.mp hω
  · exact ae_of_all _ (fun _ h => (hij h).elim)

theorem ae_zero_coordinates
    (hμ : IsProjectiveLimit (α := fun _ : ℕ => ℝ) μ (CountableBrownian.family τ)) :
    ∀ᵐ ω ∂μ, ∀ i, τ i = 0 → ω i = 0 := by
  apply ae_all_iff.mpr
  intro i
  by_cases hi : τ i = 0
  · have h := CountableBrownian.hasLaw_eval hμ i
    rw [hi, gaussianReal_zero_var] at h
    filter_upwards [h.ae_eq_of_dirac] with ω hω
    exact fun _ => hω
  · exact ae_of_all _ (fun _ h => (hi h).elim)

def sample (τ : ℕ → ℝ≥0) (ω : ℕ → ℝ) (t : ℝ) : ℝ := by
  classical
  exact if h : ∃ i, (τ i : ℝ) = t then ω (Classical.choose h) else 0

@[fun_prop]
theorem measurable_sample (τ : ℕ → ℝ≥0) (t : ℝ) :
    Measurable (fun ω : ℕ → ℝ => sample τ ω t) := by
  classical
  unfold sample
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const

theorem sample_time_eq {ω : ℕ → ℝ}
    (hω : ∀ i j, τ i = τ j → ω i = ω j) (i : ℕ) :
    sample τ ω (τ i) = ω i := by
  classical
  unfold sample
  split_ifs with hi
  · apply hω
    exact NNReal.coe_injective (Classical.choose_spec hi)
  · exact (hi ⟨i, rfl⟩).elim

lemma nndist_adjacent_grid (n k : ℕ) :
    nndist (((k + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n)
      ((k : ℝ≥0) / (2 : ℝ≥0) ^ n) = (2 : ℝ≥0)⁻¹ ^ n := by
  apply NNReal.coe_injective
  simp only [coe_nndist, NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_ofNat]
  change |((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n - (k : ℝ) / (2 : ℝ) ^ n| =
    (2 : ℝ)⁻¹ ^ n
  rw [Nat.cast_add, Nat.cast_one, add_div, add_sub_cancel_left, one_div, inv_pow]
  exact abs_of_nonneg (by positivity)

theorem hasLaw_grid_increment
    (hμ : IsProjectiveLimit (α := fun _ : ℕ => ℝ) μ (CountableBrownian.family τ))
    (idx : ℕ → ℕ → ℕ)
    (hidx : ∀ n k, τ (idx n k) = (k : ℝ≥0) / (2 : ℝ≥0) ^ n) (n k : ℕ) :
    HasLaw (fun ω : ℕ → ℝ => ω (idx n (k + 1)) - ω (idx n k))
      (gaussianReal 0 ((2 : ℝ≥0)⁻¹ ^ n)) μ := by
  have h := CountableBrownian.hasLaw_increment hμ (idx n (k + 1)) (idx n k)
  rwa [hidx, hidx, nndist_adjacent_grid] at h

theorem ae_all_grid_increment_bound
    (hμ : IsProjectiveLimit (α := fun _ : ℕ => ℝ) μ (CountableBrownian.family τ))
    (idx : ℕ → ℕ → ℕ)
    (hidx : ∀ n k, τ (idx n k) = (k : ℝ≥0) / (2 : ℝ≥0) ^ n) :
    ∀ᵐ ω ∂μ, ∀ m : ℕ, ∀ᶠ n in atTop, ∀ k : Fin (2 ^ n),
      |ω (idx n (m * 2 ^ n + k.val + 1)) - ω (idx n (m * 2 ^ n + k.val))| ≤
        SchauderTail.incrementRatio ^ n := by
  apply SchauderTail.ae_all_eventually_gaussian_increment_bound (P := μ)
    (fun (m : ℕ) (n : ℕ) (k : Fin (2 ^ n)) (ω : ℕ → ℝ) => ω (idx n (m * 2 ^ n + k.val + 1)) -
      ω (idx n (m * 2 ^ n + k.val)))
  intro m n k
  exact hasLaw_grid_increment hμ idx hidx n (m * 2 ^ n + k.val)

theorem ae_all_sample_increment_bound
    (hμ : IsProjectiveLimit (α := fun _ : ℕ => ℝ) μ (CountableBrownian.family τ))
    (idx : ℕ → ℕ → ℕ)
    (hidx : ∀ n k, τ (idx n k) = (k : ℝ≥0) / (2 : ℝ≥0) ^ n) :
    ∀ᵐ ω ∂μ, ∀ m : ℕ, ∀ᶠ n in atTop, ∀ k : Fin (2 ^ n),
      |sample τ ω (((m * 2 ^ n + k.val + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) -
        sample τ ω (((m * 2 ^ n + k.val : ℕ) : ℝ) / (2 : ℝ) ^ n)| ≤
        SchauderTail.incrementRatio ^ n := by
  filter_upwards [ae_time_consistent hμ, ae_all_grid_increment_bound hμ idx hidx]
    with ω hω hbound
  have heval (n k : ℕ) : sample τ ω ((k : ℝ) / (2 : ℝ) ^ n) = ω (idx n k) := by
    have h := sample_time_eq hω (idx n k)
    simpa [hidx, NNReal.coe_div, NNReal.coe_pow] using h
  intro m
  filter_upwards [hbound m] with n hn
  intro k
  simpa only [heval] using hn k

end Problem336.DyadicGaussianBound

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_ContinuousPathLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem336.ContinuousPathLimit

open Filter MeasureTheory
open scoped Topology

variable {T Ω : Type*} [TopologicalSpace T] [CompactSpace T]

def pathLimit (F : ℕ → C(T, ℝ)) : C(T, ℝ) := by
  classical
  exact if ∃ f, Tendsto F atTop (𝓝 f) then limUnder atTop F else 0

omit [CompactSpace T] in

theorem pathLimit_eq_of_tendsto {F : ℕ → C(T, ℝ)} {f : C(T, ℝ)}
    (h : Tendsto F atTop (𝓝 f)) : pathLimit F = f := by
  rw [pathLimit, ite_eq_left ⟨f, h⟩]
  exact h.limUnder_eq

theorem tendsto_pathLimit_of_summable {F : ℕ → C(T, ℝ)} (d : ℕ → ℝ)
    (hF : ∀ n, dist (F n) (F (n + 1)) ≤ d n) (hd : Summable d) :
    Tendsto F atTop (𝓝 (pathLimit F)) := by
  obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_dist_le_of_summable d hF hd)
  rwa [pathLimit_eq_of_tendsto hf]

theorem tendsto_pathLimit_of_eventually_summable {F : ℕ → C(T, ℝ)} (d : ℕ → ℝ)
    (hF : ∀ᶠ n in atTop, dist (F n) (F (n + 1)) ≤ d n) (hd : Summable d) :
    Tendsto F atTop (𝓝 (pathLimit F)) := by
  let d' n := max (dist (F n) (F (n + 1))) (d n)
  have heq : d =ᶠ[cofinite] d' := by
    rw [Nat.cofinite_eq_atTop]
    exact hF.mono (fun n hn => (max_eq_right hn).symm)
  exact tendsto_pathLimit_of_summable d' (fun n => le_max_left _ _)
    (hd.congr_cofinite heq)

section Measurability

variable [MeasurableSpace Ω]

theorem stronglyMeasurable_pathLimit (F : ℕ → Ω → C(T, ℝ))
    (hF : ∀ n, StronglyMeasurable (F n)) :
    StronglyMeasurable (fun ω => pathLimit (fun n => F n ω)) := by
  classical
  have hc : MeasurableSet {ω | ∃ f, Tendsto (fun n => F n ω) atTop (𝓝 f)} :=
    StronglyMeasurable.measurableSet_exists_tendsto (l := atTop) hF
  unfold pathLimit
  exact StronglyMeasurable.ite hc
    (StronglyMeasurable.limUnder (l := atTop) hF) stronglyMeasurable_const

variable [MeasurableSpace C(T, ℝ)] [BorelSpace C(T, ℝ)]

theorem measurable_pathLimit [SecondCountableTopology C(T, ℝ)]
    (F : ℕ → Ω → C(T, ℝ)) (hF : ∀ n, Measurable (F n)) :
    Measurable (fun ω => pathLimit (fun n => F n ω)) :=
  (stronglyMeasurable_pathLimit F (fun n => (hF n).stronglyMeasurable)).measurable

end Measurability

open ProbabilityTheory

end Problem336.ContinuousPathLimit

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_SchauderTents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem336.SchauderTents

def unitTent (t : ℝ) : ℝ := max 0 (min t (1 - t))

theorem continuous_unitTent : Continuous unitTent := by
  unfold unitTent
  fun_prop

theorem unitTent_nonneg (t : ℝ) : 0 ≤ unitTent t := le_max_left _ _

theorem unitTent_le_half (t : ℝ) : unitTent t ≤ 1 / 2 := by
  unfold unitTent
  apply max_le (by norm_num)
  by_cases h : t ≤ 1 / 2
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (by linarith)

theorem unitTent_pos_iff (t : ℝ) : 0 < unitTent t ↔ 0 < t ∧ t < 1 := by
  simp only [unitTent, lt_max_iff, lt_self_iff_false, false_or, lt_min_iff]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem unitTent_ne_zero_iff (t : ℝ) : unitTent t ≠ 0 ↔ 0 < t ∧ t < 1 := by
  constructor
  · intro h
    exact (unitTent_pos_iff t).mp (lt_of_le_of_ne (unitTent_nonneg t) h.symm)
  · intro h
    exact ne_of_gt ((unitTent_pos_iff t).mpr h)

theorem unitTent_eq_zero_of_le_zero {t : ℝ} (ht : t ≤ 0) : unitTent t = 0 := by
  apply le_antisymm _ (unitTent_nonneg t)
  exact max_le le_rfl ((min_le_left _ _).trans ht)

theorem unitTent_eq_zero_of_one_le {t : ℝ} (ht : 1 ≤ t) : unitTent t = 0 := by
  apply le_antisymm _ (unitTent_nonneg t)
  exact max_le le_rfl ((min_le_right _ _).trans (by linarith))

@[simp] theorem unitTent_half : unitTent (1 / 2) = 1 / 2 := by
  norm_num [unitTent]

theorem unitTent_of_left {t : ℝ} (h₀ : 0 ≤ t) (h₁ : t ≤ 1 / 2) :
    unitTent t = t := by
  unfold unitTent
  rw [min_eq_left (by linarith), max_eq_right h₀]

theorem unitTent_of_right {t : ℝ} (h₀ : 1 / 2 ≤ t) (h₁ : t ≤ 1) :
    unitTent t = 1 - t := by
  unfold unitTent
  rw [min_eq_right (by linarith), max_eq_right (by linarith)]

theorem unitTent_midpoint_of_no_corner {a b : ℝ} (hab : a ≤ b)
    (h : b ≤ 0 ∨ (0 ≤ a ∧ b ≤ 1 / 2) ∨ (1 / 2 ≤ a ∧ b ≤ 1) ∨ 1 ≤ a) :
    unitTent ((a + b) / 2) = (unitTent a + unitTent b) / 2 := by
  rcases h with h | h | h | h
  · rw [unitTent_eq_zero_of_le_zero (by linarith),
      unitTent_eq_zero_of_le_zero (by linarith), unitTent_eq_zero_of_le_zero h]
    norm_num
  · rw [unitTent_of_left (by linarith [h.1]) (by linarith [h.2]),
      unitTent_of_left h.1 (by linarith [h.2]),
      unitTent_of_left (by linarith [h.1]) h.2]
  · rw [unitTent_of_right (by linarith [h.1]) (by linarith [h.2]),
      unitTent_of_right h.1 (by linarith [h.2]),
      unitTent_of_right (by linarith [h.1]) h.2]
    ring
  · rw [unitTent_eq_zero_of_one_le (by linarith), unitTent_eq_zero_of_one_le h,
      unitTent_eq_zero_of_one_le (by linarith)]
    norm_num

theorem unitTent_even_grid_midpoint (d j k : ℕ) (hd : 0 < d) :
    unitTent (((j : ℝ) + 1 / 2) / (2 * d) - k) =
      (unitTent ((j : ℝ) / (2 * d) - k) +
        unitTent (((j : ℝ) + 1) / (2 * d) - k)) / 2 := by
  have hden : 0 < (2 : ℝ) * d := by positivity
  have hden_ne : (2 : ℝ) * d ≠ 0 := ne_of_gt hden
  have hmid : ((j : ℝ) + 1 / 2) / (2 * d) - k =
      (((j : ℝ) / (2 * d) - k) + (((j : ℝ) + 1) / (2 * d) - k)) / 2 := by
    ring
  rw [hmid]
  apply unitTent_midpoint_of_no_corner
  · exact sub_le_sub_right (div_le_div_of_nonneg_right (by linarith) hden.le) _
  · by_cases h₀ : j < 2 * d * k
    · left
      have hj : (j : ℝ) + 1 ≤ 2 * d * k := by exact_mod_cast (Nat.succ_le_of_lt h₀)
      exact sub_nonpos.mpr ((div_le_iff₀ hden).mpr (by nlinarith))
    · have h₀' : 2 * d * k ≤ j := le_of_not_gt h₀
      have ha : 0 ≤ (j : ℝ) / (2 * d) - k := by
        apply sub_nonneg.mpr
        apply (le_div_iff₀ hden).mpr
        have : (2 : ℝ) * d * k ≤ j := by exact_mod_cast h₀'
        nlinarith
      by_cases h₁ : j < 2 * d * k + d
      · right; left
        refine ⟨ha, ?_⟩
        apply sub_le_iff_le_add.mpr
        apply (div_le_iff₀ hden).mpr
        have : (j : ℝ) + 1 ≤ 2 * d * k + d := by exact_mod_cast (Nat.succ_le_of_lt h₁)
        nlinarith
      · have h₁' : 2 * d * k + d ≤ j := le_of_not_gt h₁
        have ha' : 1 / 2 ≤ (j : ℝ) / (2 * d) - k := by
          apply le_sub_iff_add_le.mpr
          apply (le_div_iff₀ hden).mpr
          have : (2 : ℝ) * d * k + d ≤ j := by exact_mod_cast h₁'
          nlinarith
        by_cases h₂ : j < 2 * d * (k + 1)
        · right; right; left
          refine ⟨ha', ?_⟩
          apply sub_le_iff_le_add.mpr
          apply (div_le_iff₀ hden).mpr
          have : (j : ℝ) + 1 ≤ 2 * d * (k + 1) := by exact_mod_cast (Nat.succ_le_of_lt h₂)
          nlinarith
        · right; right; right
          apply le_sub_iff_add_le.mpr
          apply (le_div_iff₀ hden).mpr
          have : (2 : ℝ) * d * (k + 1) ≤ j := by exact_mod_cast (le_of_not_gt h₂)
          nlinarith

def amplitude (n : ℕ) : ℝ := (Real.sqrt 2)⁻¹ ^ n

theorem amplitude_pos (n : ℕ) : 0 < amplitude n := by
  unfold amplitude
  positivity

def tent (n k : ℕ) (t : ℝ) : ℝ :=
  amplitude n * unitTent ((2 : ℝ) ^ n * t - k)

theorem continuous_tent (n k : ℕ) : Continuous (tent n k) := by
  exact continuous_const.mul (continuous_unitTent.comp (by fun_prop))

theorem tent_nonneg (n k : ℕ) (t : ℝ) : 0 ≤ tent n k t :=
  mul_nonneg (amplitude_pos n).le (unitTent_nonneg _)

theorem tent_le_half_amplitude (n k : ℕ) (t : ℝ) :
    tent n k t ≤ amplitude n / 2 := by
  unfold tent
  simpa only [mul_one_div] using
    mul_le_mul_of_nonneg_left (unitTent_le_half ((2 : ℝ) ^ n * t - k))
      (amplitude_pos n).le

theorem tent_ne_zero_iff (n k : ℕ) (t : ℝ) :
    tent n k t ≠ 0 ↔ (k : ℝ) < 2 ^ n * t ∧ 2 ^ n * t < k + 1 := by
  rw [tent, mul_ne_zero_iff, and_iff_right (ne_of_gt (amplitude_pos n)),
    unitTent_ne_zero_iff]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem tent_disjoint (n : ℕ) {k l : ℕ} (hkl : k ≠ l) (t : ℝ)
    (hk : tent n k t ≠ 0) : tent n l t = 0 := by
  by_contra hl
  obtain ⟨hk₁, hk₂⟩ := (tent_ne_zero_iff n k t).mp hk
  obtain ⟨hl₁, hl₂⟩ := (tent_ne_zero_iff n l t).mp hl
  rcases lt_or_gt_of_ne hkl with h | h
  · have : (k : ℝ) + 1 ≤ l := by exact_mod_cast h
    linarith
  · have : (l : ℝ) + 1 ≤ k := by exact_mod_cast h
    linarith

def level (n : ℕ) (z : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ n), z k * tent n k t

theorem continuous_level (n : ℕ) (z : ℕ → ℝ) : Continuous (level n z) := by
  unfold level
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_tent n k)

theorem abs_level_le (n : ℕ) (z : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hz : ∀ k < 2 ^ n, |z k| ≤ C) (t : ℝ) :
    |level n z t| ≤ C * amplitude n / 2 := by
  classical
  by_cases h : ∃ k ∈ Finset.range (2 ^ n), tent n k t ≠ 0
  · obtain ⟨k, hk, hkt⟩ := h
    have hsum : level n z t = z k * tent n k t := by
      unfold level
      apply Finset.sum_eq_single k
      · intro l hl hlk
        rw [tent_disjoint n (Ne.symm hlk) t hkt, mul_zero]
      · exact fun hnot => (hnot hk).elim
    rw [hsum, abs_mul, abs_of_nonneg (tent_nonneg n k t)]
    calc
      |z k| * tent n k t ≤ C * tent n k t :=
        mul_le_mul_of_nonneg_right (hz k (Finset.mem_range.mp hk)) (tent_nonneg n k t)
      _ ≤ C * (amplitude n / 2) :=
        mul_le_mul_of_nonneg_left (tent_le_half_amplitude n k t) hC
      _ = C * amplitude n / 2 := by ring
  · have hzero : level n z t = 0 := by
      unfold level
      apply Finset.sum_eq_zero
      intro k hk
      have hkt : tent n k t = 0 := by
        by_contra hne
        exact h ⟨k, hk, hne⟩
      rw [hkt, mul_zero]
    rw [hzero, abs_zero]
    exact div_nonneg (mul_nonneg hC (amplitude_pos n).le) (by norm_num)

theorem unitTent_nat_sub (j k : ℕ) : unitTent ((j : ℝ) - k) = 0 := by
  by_cases h : j ≤ k
  · apply unitTent_eq_zero_of_le_zero
    have : (j : ℝ) ≤ k := by exact_mod_cast h
    linarith
  · apply unitTent_eq_zero_of_one_le
    have : (k : ℝ) + 1 ≤ j := by exact_mod_cast (Nat.succ_le_of_lt (lt_of_not_ge h))
    linarith

theorem tent_prior_grid_zero (n r k j : ℕ) :
    tent (n + r) k ((j : ℝ) / 2 ^ n) = 0 := by
  have hpow : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have harg : (2 : ℝ) ^ (n + r) * ((j : ℝ) / 2 ^ n) - k =
      (((2 ^ r * j : ℕ) : ℝ) - k) := by
    push_cast
    rw [pow_add]
    field_simp
  rw [tent, harg, unitTent_nat_sub, mul_zero]

theorem level_prior_grid_zero (n r j : ℕ) (z : ℕ → ℝ) :
    level (n + r) z ((j : ℝ) / 2 ^ n) = 0 := by
  simp [level, tent_prior_grid_zero]

def midpoint (n k : ℕ) : ℝ := ((k : ℝ) + 1 / 2) / 2 ^ n

theorem tent_at_midpoint (n k : ℕ) :
    tent n k (midpoint n k) = amplitude n / 2 := by
  have hpow : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have harg : (2 : ℝ) ^ n * midpoint n k - k = 1 / 2 := by
    unfold midpoint
    field_simp
    ring
  rw [tent, harg, unitTent_half]
  ring

theorem tent_at_other_midpoint (n : ℕ) {k l : ℕ} (hkl : k ≠ l) :
    tent n l (midpoint n k) = 0 := by
  apply tent_disjoint n hkl
  rw [tent_at_midpoint]
  exact ne_of_gt (div_pos (amplitude_pos n) (by norm_num))

theorem level_at_midpoint (n k : ℕ) (z : ℕ → ℝ) (hk : k < 2 ^ n) :
    level n z (midpoint n k) = z k * amplitude n / 2 := by
  classical
  unfold level
  rw [Finset.sum_eq_single k]
  · rw [tent_at_midpoint]
    ring
  · intro l hl hlk
    rw [tent_at_other_midpoint n (Ne.symm hlk), mul_zero]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr hk)).elim

theorem tent_old_midpoint (m r k j : ℕ) :
    tent m k (midpoint (m + r + 1) j) =
      (tent m k ((j : ℝ) / 2 ^ (m + r + 1)) +
        tent m k (((j : ℝ) + 1) / 2 ^ (m + r + 1))) / 2 := by
  have hscale (q : ℝ) :
      (2 : ℝ) ^ m * (q / 2 ^ (m + r + 1)) = q / (2 * (2 ^ r : ℕ)) := by
    push_cast
    rw [pow_add, pow_add, pow_one]
    field_simp
  simp only [tent, midpoint, hscale]
  rw [unitTent_even_grid_midpoint (2 ^ r) j k (by positivity)]
  ring

theorem tent_old_midpoint_of_lt {m n : ℕ} (hmn : m < n) (k j : ℕ) :
    tent m k (midpoint n j) =
      (tent m k ((j : ℝ) / 2 ^ n) + tent m k (((j : ℝ) + 1) / 2 ^ n)) / 2 := by
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hmn)
  have hn : n = m + r + 1 := by omega
  rw [hn]
  exact tent_old_midpoint m r k j

theorem level_old_midpoint {m n : ℕ} (hmn : m < n) (z : ℕ → ℝ) (j : ℕ) :
    level m z (midpoint n j) =
      (level m z ((j : ℝ) / 2 ^ n) + level m z (((j : ℝ) + 1) / 2 ^ n)) / 2 := by
  simp only [level, tent_old_midpoint_of_lt hmn, ← mul_div_assoc, mul_add,
    ← Finset.sum_div, Finset.sum_add_distrib]

end Problem336.SchauderTents

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_DyadicInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem336.DyadicInterpolation

open SchauderTents

def grid (n j : ℕ) : ℝ := (j : ℝ) / 2 ^ n

@[simp] theorem grid_zero (n : ℕ) : grid n 0 = 0 := by simp [grid]
@[simp] theorem grid_zero_level (j : ℕ) : grid 0 j = j := by simp [grid]

theorem grid_succ_even (n j : ℕ) : grid (n + 1) (2 * j) = grid n j := by
  unfold grid
  push_cast
  rw [pow_succ]
  field_simp

theorem grid_succ_odd (n j : ℕ) : grid (n + 1) (2 * j + 1) = midpoint n j := by
  unfold grid SchauderTents.midpoint
  push_cast
  rw [pow_succ]
  field_simp

theorem midpoint_eq_average (n j : ℕ) :
    midpoint n j = (grid n j + grid n (j + 1)) / 2 := by
  unfold SchauderTents.midpoint grid
  push_cast
  ring

def residual (x : ℝ → ℝ) (n k : ℕ) : ℝ :=
  x (midpoint n k) - (x (grid n k) + x (grid n (k + 1))) / 2

def coefficient (x : ℝ → ℝ) (n k : ℕ) : ℝ :=
  2 * residual x n k / amplitude n

def approx (x : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  x 0 + (x 1 - x 0) * t + ∑ m ∈ Finset.range n, level m (coefficient x m) t

theorem continuous_approx (x : ℝ → ℝ) (n : ℕ) : Continuous (approx x n) := by
  unfold approx
  apply Continuous.add
  · fun_prop
  · exact continuous_finsetSum _ fun m _ => continuous_level m (coefficient x m)

theorem approx_succ (x : ℝ → ℝ) (n : ℕ) (t : ℝ) :
    approx x (n + 1) t = approx x n t + level n (coefficient x n) t := by
  simp only [approx, Finset.sum_range_succ]
  ring

theorem approx_old_midpoint (x : ℝ → ℝ) (n j : ℕ) :
    approx x n (midpoint n j) =
      (approx x n (grid n j) + approx x n (grid n (j + 1))) / 2 := by
  have hs :
      (∑ m ∈ Finset.range n, level m (coefficient x m) (midpoint n j)) =
      ((∑ m ∈ Finset.range n, level m (coefficient x m) (grid n j)) +
        ∑ m ∈ Finset.range n, level m (coefficient x m) (grid n (j + 1))) / 2 := by
    calc
      _ = ∑ m ∈ Finset.range n,
          (level m (coefficient x m) (grid n j) +
            level m (coefficient x m) (grid n (j + 1))) / 2 := by
        apply Finset.sum_congr rfl
        intro m hm
        simpa only [grid, Nat.cast_add, Nat.cast_one] using
          level_old_midpoint (Finset.mem_range.mp hm) (coefficient x m) j
      _ = _ := by rw [← Finset.sum_div, Finset.sum_add_distrib]
  simp only [approx]
  rw [hs, midpoint_eq_average]
  ring

theorem level_coefficient_midpoint (x : ℝ → ℝ) (n k : ℕ) (hk : k < 2 ^ n) :
    level n (coefficient x n) (midpoint n k) = residual x n k := by
  rw [level_at_midpoint n k _ hk, coefficient]
  have ha : amplitude n ≠ 0 := ne_of_gt (amplitude_pos n)
  field_simp

theorem approx_grid (x : ℝ → ℝ) (n j : ℕ) (hj : j ≤ 2 ^ n) :
    approx x n (grid n j) = x (grid n j) := by
  induction n generalizing j with
  | zero =>
      have hj' : j = 0 ∨ j = 1 := by norm_num at hj; omega
      rcases hj' with rfl | rfl <;> simp [approx, grid]
  | succ n ih =>
      obtain ⟨k, h | h⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 :=
        ⟨j / 2, by omega⟩
      · subst j
        have hk : k ≤ 2 ^ n := by rw [pow_succ] at hj; omega
        rw [grid_succ_even, approx_succ]
        have hz : level n (coefficient x n) (grid n k) = 0 := by
          simpa only [Nat.add_zero, grid] using
            level_prior_grid_zero n 0 k (coefficient x n)
        rw [hz, add_zero, ih k hk]
      · subst j
        have hk : k < 2 ^ n := by rw [pow_succ] at hj; omega
        rw [grid_succ_odd, approx_succ, approx_old_midpoint,
          level_coefficient_midpoint x n k hk, ih k hk.le, ih (k + 1) (by omega)]
        unfold residual
        ring

theorem abs_residual_le (x : ℝ → ℝ) (n k : ℕ) {D : ℝ}
    (hleft : |x (midpoint n k) - x (grid n k)| ≤ D)
    (hright : |x (grid n (k + 1)) - x (midpoint n k)| ≤ D) :
    |residual x n k| ≤ D := by
  obtain ⟨hl₁, hl₂⟩ := abs_le.mp hleft
  obtain ⟨hr₁, hr₂⟩ := abs_le.mp hright
  rw [residual, abs_le]
  constructor <;> linarith

theorem abs_residual_le_of_increments (x : ℝ → ℝ) (n k : ℕ) {D : ℝ}
    (hk : k < 2 ^ n)
    (hinc : ∀ j < 2 ^ (n + 1),
      |x (grid (n + 1) (j + 1)) - x (grid (n + 1) j)| ≤ D) :
    |residual x n k| ≤ D := by
  apply abs_residual_le
  · have h := hinc (2 * k) (by rw [pow_succ]; omega)
    simpa only [grid_succ_even, grid_succ_odd] using h
  · have h := hinc (2 * k + 1) (by rw [pow_succ]; omega)
    have heq : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
    simpa only [heq, grid_succ_even, grid_succ_odd] using h

theorem abs_approx_succ_sub_le_of_residual (x : ℝ → ℝ) (n : ℕ) {D : ℝ}
    (hD : 0 ≤ D) (hres : ∀ k < 2 ^ n, |residual x n k| ≤ D) (t : ℝ) :
    |approx x (n + 1) t - approx x n t| ≤ D := by
  have ha : 0 < amplitude n := amplitude_pos n
  have hC : 0 ≤ 2 * D / amplitude n := div_nonneg (by positivity) ha.le
  have hc : ∀ k < 2 ^ n, |coefficient x n k| ≤ 2 * D / amplitude n := by
    intro k hk
    rw [coefficient, abs_div, abs_mul, abs_of_pos ha,
      abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hres k hk) (by norm_num)) ha.le
  have h := abs_level_le n (coefficient x n) hC hc t
  have hbound : (2 * D / amplitude n) * amplitude n / 2 = D := by
    field_simp
  rw [hbound] at h
  simpa only [approx_succ, add_sub_cancel_left] using h

theorem abs_approx_succ_sub_le (x : ℝ → ℝ) (n : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hinc : ∀ j < 2 ^ (n + 1),
      |x (grid (n + 1) (j + 1)) - x (grid (n + 1) j)| ≤ D) (t : ℝ) :
    |approx x (n + 1) t - approx x n t| ≤ D :=
  abs_approx_succ_sub_le_of_residual x n hD
    (fun k hk => abs_residual_le_of_increments x n k hk hinc) t

variable {Ω : Type*} [MeasurableSpace Ω] (x : Ω → ℝ → ℝ)
    (hx : ∀ t, Measurable (fun ω => x ω t))

include hx

theorem measurable_residual (n k : ℕ) :
    Measurable (fun ω => residual (x ω) n k) := by
  exact (hx _).sub (((hx _).add (hx _)).div_const 2)

theorem measurable_coefficient (n k : ℕ) :
    Measurable (fun ω => coefficient (x ω) n k) := by
  exact ((measurable_residual x hx n k).const_mul 2).div_const _

end Problem336.DyadicInterpolation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_DyadicPathLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem336.DyadicPathLimit

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators
open DyadicInterpolation

def unitApprox (x : ℝ → ℝ) (n : ℕ) : C(unitInterval, ℝ) :=
  ⟨fun t => approx x n t, (continuous_approx x n).comp continuous_subtype_val⟩

@[simp] theorem unitApprox_apply (x : ℝ → ℝ) (n : ℕ) (t : unitInterval) :
    unitApprox x n t = approx x n t := rfl

def unitPath (x : ℝ → ℝ) : C(unitInterval, ℝ) :=
  ContinuousPathLimit.pathLimit (unitApprox x)

theorem approx_grid_add (x : ℝ → ℝ) (n j : ℕ) (hj : j ≤ 2 ^ n) (r : ℕ) :
    approx x (n + r) (grid n j) = x (grid n j) := by
  induction r with
  | zero => simpa using approx_grid x n j hj
  | succ r ih =>
      rw [Nat.add_succ, approx_succ, ih]
      have hz := SchauderTents.level_prior_grid_zero n r j (coefficient x (n + r))
      change SchauderTents.level (n + r) (coefficient x (n + r)) (grid n j) = 0 at hz
      rw [hz, add_zero]

theorem eventually_unitApprox_grid (x : ℝ → ℝ) (n j : ℕ) (hj : j ≤ 2 ^ n)
    (t : unitInterval) (ht : (t : ℝ) = grid n j) :
    ∀ᶠ m in atTop, unitApprox x m t = x t := by
  filter_upwards [eventually_ge_atTop n] with m hm
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm
  simpa only [unitApprox_apply, ht] using approx_grid_add x n j hj r

theorem dist_unitApprox_succ_le (x : ℝ → ℝ) (n : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hinc : ∀ j < 2 ^ (n + 1),
      |x (grid (n + 1) (j + 1)) - x (grid (n + 1) j)| ≤ D) :
    dist (unitApprox x n) (unitApprox x (n + 1)) ≤ D := by
  apply (ContinuousMap.dist_le hD).mpr
  intro t
  rw [dist_comm, Real.dist_eq]
  exact abs_approx_succ_sub_le x n hD hinc t

theorem tendsto_unitPath (x : ℝ → ℝ) (d : ℕ → ℝ)
    (hd0 : ∀ n, 0 ≤ d n) (hd : Summable d)
    (hinc : ∀ᶠ n in atTop, ∀ j < 2 ^ (n + 1),
      |x (grid (n + 1) (j + 1)) - x (grid (n + 1) j)| ≤ d n) :
    Tendsto (unitApprox x) atTop (𝓝 (unitPath x)) := by
  exact ContinuousPathLimit.tendsto_pathLimit_of_eventually_summable d
    (hinc.mono fun n hn => dist_unitApprox_succ_le x n (hd0 n) hn) hd

theorem unitPath_grid (x : ℝ → ℝ) (d : ℕ → ℝ)
    (hd0 : ∀ n, 0 ≤ d n) (hd : Summable d)
    (hinc : ∀ᶠ n in atTop, ∀ j < 2 ^ (n + 1),
      |x (grid (n + 1) (j + 1)) - x (grid (n + 1) j)| ≤ d n)
    (n j : ℕ) (hj : j ≤ 2 ^ n) (t : unitInterval) (ht : (t : ℝ) = grid n j) :
    unitPath x t = x t := by
  exact tendsto_nhds_unique
    ((continuous_eval_const t).continuousAt.tendsto.comp (tendsto_unitPath x d hd0 hd hinc))
    (tendsto_const_nhds.congr' ((eventually_unitApprox_grid x n j hj t ht).mono (fun _ h => h.symm)))

variable {Ω : Type*} [MeasurableSpace Ω]
variable [MeasurableSpace C(unitInterval, ℝ)] [BorelSpace C(unitInterval, ℝ)]

theorem measurable_unitApprox (x : Ω → ℝ → ℝ)
    (hx : ∀ t, Measurable (fun ω => x ω t)) (n : ℕ) :
    Measurable (fun ω => unitApprox (x ω) n) := by
  let coordinate : C(unitInterval, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩
  let tentPath (m k : ℕ) : C(unitInterval, ℝ) :=
    ⟨fun t => SchauderTents.tent m k t,
      (SchauderTents.continuous_tent m k).comp continuous_subtype_val⟩
  have hc : Continuous (ContinuousMap.const unitInterval : ℝ → C(unitInterval, ℝ)) :=
    ContinuousMap.continuous_of_continuous_uncurry _ continuous_fst
  have heq : (fun ω => unitApprox (x ω) n) = fun ω =>
      ContinuousMap.const unitInterval (x ω 0) + (x ω 1 - x ω 0) • coordinate +
        ∑ m ∈ Finset.range n, ∑ k ∈ Finset.range (2 ^ m),
          coefficient (x ω) m k • tentPath m k := by
    funext ω
    ext t
    simp [unitApprox, approx, SchauderTents.level, coordinate, tentPath]
  rw [heq]
  apply Measurable.add
  · exact (hc.measurable.comp (hx 0)).add (((hx 1).sub (hx 0)).smul measurable_const)
  · apply Finset.measurable_sum
    intro m hm
    apply Finset.measurable_sum
    intro k hk
    exact (measurable_coefficient x hx m k).smul measurable_const

theorem measurable_unitPath (x : Ω → ℝ → ℝ)
    (hx : ∀ t, Measurable (fun ω => x ω t)) :
    Measurable (fun ω => unitPath (x ω)) :=
  ContinuousPathLimit.measurable_pathLimit (fun n ω => unitApprox (x ω) n)
    (measurable_unitApprox x hx)

end Problem336.DyadicPathLimit

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_DyadicTimes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology NNReal

namespace Problem336.DyadicTimes

def grid (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / (2 : ℝ≥0) ^ n

def enumeration (i : ℕ) : ℝ≥0 := grid (Nat.unpair i).1 (Nat.unpair i).2

@[simp] theorem enumeration_pair (n k : ℕ) : enumeration (Nat.pair n k) = grid n k := by
  simp [enumeration]

@[simp] theorem enumeration_zero : enumeration 0 = 0 := by
  norm_num [enumeration, grid, Nat.unpair]

@[simp] theorem coe_grid (n k : ℕ) :
    (grid n k : ℝ) = (k : ℝ) / (2 : ℝ) ^ n := by
  simp [grid]

@[simp] theorem grid_zero (n : ℕ) : grid n 0 = 0 := by simp [grid]

@[simp] theorem grid_level_zero (k : ℕ) : grid 0 k = k := by simp [grid]

end Problem336.DyadicTimes

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_SampledUnitPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem336.SampledUnitPath

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open DyadicGaussianBound

def pathBlock (τ : ℕ → ℝ≥0) (ω : ℕ → ℝ) (m : ℕ) : C(unitInterval, ℝ) :=
  DyadicPathLimit.unitPath (fun t => sample τ ω ((m : ℝ) + t))

section Measurability

variable [MeasurableSpace C(unitInterval, ℝ)] [BorelSpace C(unitInterval, ℝ)]

theorem measurable_pathBlock (τ : ℕ → ℝ≥0) (m : ℕ) :
    Measurable (fun ω : ℕ → ℝ => pathBlock τ ω m) :=
  DyadicPathLimit.measurable_unitPath _ (fun _ => measurable_sample τ _)

theorem measurable_pathBlocks (τ : ℕ → ℝ≥0) :
    Measurable (fun ω : ℕ → ℝ => pathBlock τ ω) :=
  Measurable.of_eval (measurable_pathBlock τ)

end Measurability

lemma shift_grid (m n j : ℕ) :
    ((m * 2 ^ n + j : ℕ) : ℝ) / (2 : ℝ) ^ n =
      (m : ℝ) + DyadicInterpolation.grid n j := by
  unfold DyadicInterpolation.grid
  push_cast
  field_simp

lemma shift_grid_succ (m n j : ℕ) :
    ((m * 2 ^ n + j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n =
      (m : ℝ) + DyadicInterpolation.grid n (j + 1) := by
  rw [Nat.add_assoc]
  exact shift_grid m n (j + 1)

def bound (n : ℕ) : ℝ := SchauderTail.incrementRatio ^ (n + 1)

lemma bound_nonneg (n : ℕ) : 0 ≤ bound n :=
  pow_nonneg SchauderTail.incrementRatio_nonneg _

lemma summable_bound : Summable bound := by
  change Summable (fun n : ℕ => SchauderTail.incrementRatio ^ (n + 1))
  simpa only [pow_succ] using
    SchauderTail.summable_incrementRatio.mul_right SchauderTail.incrementRatio

variable {τ : ℕ → ℝ≥0} {μ : Measure (ℕ → ℝ)}
variable (hμ : IsProjectiveLimit (α := fun _ : ℕ => ℝ) μ (CountableBrownian.family τ))
variable (idx : ℕ → ℕ → ℕ)
variable (hidx : ∀ n k, τ (idx n k) = (k : ℝ≥0) / (2 : ℝ≥0) ^ n)

include hμ idx hidx

theorem ae_block_increment_bound :
    ∀ᵐ ω ∂μ, ∀ m : ℕ, ∀ᶠ n in atTop, ∀ j < 2 ^ (n + 1),
      |sample τ ω ((m : ℝ) + DyadicInterpolation.grid (n + 1) (j + 1)) -
        sample τ ω ((m : ℝ) + DyadicInterpolation.grid (n + 1) j)| ≤ bound n := by
  filter_upwards [ae_all_sample_increment_bound hμ idx hidx] with ω hω
  intro m
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hω m)
  filter_upwards [eventually_ge_atTop N] with n hn
  intro j hj
  have h := hN (n + 1) (by omega) ⟨j, hj⟩
  simpa only [shift_grid_succ, shift_grid, bound] using h

theorem ae_pathBlock_grid :
    ∀ᵐ ω ∂μ, ∀ m n j : ℕ, ∀ (_ : j ≤ 2 ^ n) (t : unitInterval),
      (t : ℝ) = DyadicInterpolation.grid n j →
      pathBlock τ ω m t = sample τ ω ((m : ℝ) + t) := by
  filter_upwards [ae_block_increment_bound hμ idx hidx] with ω hω
  intro m n j hj t ht
  exact DyadicPathLimit.unitPath_grid _ bound bound_nonneg summable_bound
    (hω m) n j hj t ht

theorem ae_sample_zero : ∀ᵐ ω ∂μ, sample τ ω 0 = 0 := by
  filter_upwards [ae_time_consistent hμ, ae_zero_coordinates hμ] with ω hc hz
  have hi : τ (idx 0 0) = 0 := by simpa using hidx 0 0
  have hs := sample_time_eq hc (idx 0 0)
  simpa [hi, hz _ hi] using hs

theorem ae_pathBlock_endpoints :
    ∀ᵐ ω ∂μ, ∀ m : ℕ,
      pathBlock τ ω m 0 = sample τ ω m ∧
      pathBlock τ ω m 1 = sample τ ω ((m : ℝ) + 1) := by
  filter_upwards [ae_pathBlock_grid hμ idx hidx] with ω hω
  intro m
  constructor
  · simpa using hω m 0 0 (by norm_num) 0 (by simp [DyadicInterpolation.grid])
  · exact hω m 0 1 (by norm_num) 1 (by simp [DyadicInterpolation.grid])

end Problem336.SampledUnitPath

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_SampledPathConcatenation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem336.SampledPathConcatenation

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators NNReal
open SampledUnitPath DyadicGaussianBound

local instance instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions : MeasurableSpace C(unitInterval, ℝ) := borel _
local instance instBorelSpaceContinuousMapElemRealUnitInterval_solutions : BorelSpace C(unitInterval, ℝ) := ⟨rfl⟩
local instance instMeasurableSpaceContinuousMapReal_solutions : MeasurableSpace C(ℝ, ℝ) := borel _

def fullPath (τ : ℕ → ℝ≥0) (ω : ℕ → ℝ) : C(ℝ, ℝ) :=
  PathConcatenation.concatPath (pathBlock τ ω)

theorem measurable_fullPath (τ : ℕ → ℝ≥0) : Measurable (fullPath τ) :=
  PathConcatenation.measurable_concatPath.comp (measurable_pathBlocks τ)

variable {τ : ℕ → ℝ≥0} {μ : Measure (ℕ → ℝ)}
variable (hμ : IsProjectiveLimit (α := fun _ : ℕ => ℝ) μ (CountableBrownian.family τ))
variable (idx : ℕ → ℕ → ℕ)
variable (hidx : ∀ n k, τ (idx n k) = (k : ℝ≥0) / (2 : ℝ≥0) ^ n)
include hμ idx hidx

theorem ae_fullPath_block_grid :
    ∀ᵐ ω ∂μ, ∀ m n j : ℕ, ∀ (_ : j ≤ 2 ^ n) (t : unitInterval),
      (t : ℝ) = DyadicInterpolation.grid n j →
      fullPath τ ω ((m : ℝ) + t) = sample τ ω ((m : ℝ) + t) := by
  filter_upwards [ae_pathBlock_grid hμ idx hidx, ae_pathBlock_endpoints hμ idx hidx,
    ae_sample_zero hμ idx hidx] with ω hg he hz
  intro m n j hj t ht
  change PathConcatenation.concat (pathBlock τ ω) ((m : ℝ) + t) = _
  rw [PathConcatenation.concat_nat_add]
  have hsum : (∑ k ∈ Finset.range m,
      (pathBlock τ ω k PathConcatenation.rightEnd -
        pathBlock τ ω k PathConcatenation.leftEnd)) = sample τ ω m - sample τ ω 0 := by
    change (∑ k ∈ Finset.range m, (pathBlock τ ω k 1 - pathBlock τ ω k 0)) = _
    simp_rw [(he _).1, (he _).2]
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] using
      Finset.sum_range_sub (fun k : ℕ => sample τ ω (k : ℝ)) m
  rw [hsum, hz, sub_zero, hg m n j hj t ht]
  change sample τ ω m + (sample τ ω ((m : ℝ) + t) - pathBlock τ ω m 0) = _
  rw [(he m).1]
  ring

omit hμ idx hidx in

lemma grid_decompose (n k : ℕ) :
    ∃ (m j : ℕ) (t : unitInterval), j ≤ 2 ^ n ∧
      (t : ℝ) = DyadicInterpolation.grid n j ∧
      DyadicInterpolation.grid n k = (m : ℝ) + t := by
  let m := k / 2 ^ n
  let j := k % 2 ^ n
  have hp : 0 < 2 ^ n := by positivity
  have hj : j < 2 ^ n := Nat.mod_lt _ hp
  have hjR : (j : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hj.le
  let t : unitInterval := ⟨DyadicInterpolation.grid n j,
    ⟨by unfold DyadicInterpolation.grid; positivity,
      by unfold DyadicInterpolation.grid; exact (div_le_one (by positivity)).mpr hjR⟩⟩
  refine ⟨m, j, t, hj.le, rfl, ?_⟩
  change (k : ℝ) / (2 : ℝ) ^ n = (m : ℝ) + (j : ℝ) / (2 : ℝ) ^ n
  have hkj : j + 2 ^ n * m = k := Nat.mod_add_div k (2 ^ n)
  have hcast : (j : ℝ) + (2 : ℝ) ^ n * (m : ℝ) = k := by exact_mod_cast hkj
  apply (div_eq_iff (by positivity : (2 : ℝ) ^ n ≠ 0)).mpr
  field_simp
  nlinarith

theorem ae_fullPath_grid :
    ∀ᵐ ω ∂μ, ∀ n k : ℕ,
      fullPath τ ω (DyadicInterpolation.grid n k) =
        sample τ ω (DyadicInterpolation.grid n k) := by
  filter_upwards [ae_fullPath_block_grid hμ idx hidx] with ω hω
  intro n k
  obtain ⟨m, j, t, hj, ht, hdecomp⟩ := grid_decompose n k
  rw [hdecomp]
  exact hω m n j hj t ht

theorem ae_fullPath_coordinates :
    ∀ᵐ ω ∂μ, ∀ n k : ℕ,
      fullPath τ ω ((k : ℝ) / (2 : ℝ) ^ n) = ω (idx n k) := by
  filter_upwards [ae_fullPath_grid hμ idx hidx, ae_time_consistent hμ] with ω hg hc
  intro n k
  rw [show ((k : ℝ) / (2 : ℝ) ^ n) = DyadicInterpolation.grid n k from rfl, hg n k]
  have hs := sample_time_eq hc (idx n k)
  simpa [hidx, DyadicInterpolation.grid, NNReal.coe_div, NNReal.coe_pow] using hs

end Problem336.SampledPathConcatenation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_GlobalWiener
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace Problem336.GlobalWiener

abbrev Path := C(ℝ≥0, ℝ)

local instance instMeasurableSpaceContinuousMapReal_solutions : MeasurableSpace C(ℝ, ℝ) := borel _
local instance instBorelSpaceContinuousMapReal_solutions : BorelSpace C(ℝ, ℝ) := ⟨rfl⟩
local instance instMeasurableSpacePath : MeasurableSpace Path := borel _
local instance instBorelSpacePath : BorelSpace Path := ⟨rfl⟩

def nonnegativeEmbedding : C(ℝ≥0, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩

def samplePath (ω : ℕ → ℝ) : Path :=
  (SampledPathConcatenation.fullPath DyadicTimes.enumeration ω).comp nonnegativeEmbedding

lemma measurable_samplePath : Measurable samplePath :=
  (ContinuousMap.continuous_precomp nonnegativeEmbedding).measurable.comp
    (SampledPathConcatenation.measurable_fullPath DyadicTimes.enumeration)

theorem isBrownian_samplePath {μ : Measure (ℕ → ℝ)} [IsProbabilityMeasure μ]
    (hμ : IsProjectiveLimit (α := fun _ : ℕ => ℝ) μ
      (CountableBrownian.family DyadicTimes.enumeration)) :
    IsBrownianReal (fun t ω => samplePath ω t) μ := by
  apply DenseBrownian.isBrownian_of_dense_gaussian_modification
    (τ := DyadicTimes.enumeration) (Y := fun i ω => ω i)
    DenseBrownian.dense_dyadicTimes
  · intro t
    exact (continuous_eval_const t).measurable.comp measurable_samplePath
  · exact ae_of_all _ (fun ω => (samplePath ω).continuous)
  · exact CountableBrownian.isGaussianProcess hμ
  · exact CountableBrownian.integral_eval hμ
  · exact CountableBrownian.covariance_eval hμ
  · intro t ht
    obtain ⟨n, k, rfl⟩ := ht
    refine ⟨Nat.pair n k, ?_, ?_⟩
    · simp [DyadicTimes.grid]
    · filter_upwards [SampledPathConcatenation.ae_fullPath_coordinates hμ Nat.pair
        (by intro n k; simp [DyadicTimes.grid])] with ω hω
      change SampledPathConcatenation.fullPath DyadicTimes.enumeration ω
        (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ) = ω (Nat.pair n k)
      simpa using hω n k

theorem exists_wiener :
    ∃ ρ : Measure Path, IsProbabilityMeasure ρ ∧
      IsBrownianReal (fun t (w : Path) => w t) ρ := by
  obtain ⟨μ, hprob, hμ⟩ :=
    CountableBrownian.exists_countable_brownian_law DyadicTimes.enumeration
  let : IsProbabilityMeasure μ := hprob
  let ρ : Measure Path := μ.map samplePath
  have hρ : IsProbabilityMeasure ρ :=
    Measure.isProbabilityMeasure_map measurable_samplePath.aemeasurable
  have hB := isBrownian_samplePath hμ
  refine ⟨ρ, hρ, ?_⟩
  constructor
  · constructor
    intro I
    have hm : Measurable (fun w : Path => I.restrict (fun t => w t)) :=
      Measurable.of_eval (fun i => (continuous_eval_const i.val).measurable)
    refine ⟨hm.aemeasurable, ?_⟩
    change (μ.map samplePath).map (fun w : Path => I.restrict (fun t => w t)) = _
    rw [Measure.map_map hm measurable_samplePath]
    exact (hB.toIsPreBrownianReal.hasLaw I).map_eq
  · exact ae_of_all _ (fun w => w.continuous)

def wienerMeasure : Measure Path := Classical.choose exists_wiener

instance wienerMeasure_isProbabilityMeasure : IsProbabilityMeasure wienerMeasure :=
  (Classical.choose_spec exists_wiener).1

end Problem336.GlobalWiener

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_WienerSampler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336.WienerSampler

abbrev Path := GlobalWiener.Path
local instance instMeasurableSpacePath : MeasurableSpace Path := borel _
local instance instBorelSpacePath : BorelSpace Path := ⟨rfl⟩

def sample : ℝ → Path :=
  Classical.choose (exists_uniform01_sampler GlobalWiener.wienerMeasure)

end Problem336.WienerSampler

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_AllPairWiener
attribute [-instance] _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336.AllPairWiener
open FactorAssembly
abbrev Path := GlobalWiener.Path
local instance instMeasurableSpacePath : MeasurableSpace Path := borel _

def law : Measure (EdgeCode → Path) :=
  Measure.infinitePi (fun _ : EdgeCode => GlobalWiener.wienerMeasure)

instance law_isProbabilityMeasure : IsProbabilityMeasure law := by
  unfold law
  infer_instance

def pathEval (w : Path) (t : ℝ) : ℝ := w (Real.toNNReal t)

def paths (G : GraphCode) (U : ℕ → ℝ) (e : EdgeCode) : Path :=
  WienerSampler.sample (AllPairIID.uniformRule G U e)

def noise : GraphNoise := fun G U e => pathEval (paths G U e)

end Problem336.AllPairWiener

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FinitePosterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators ProbabilityTheory

namespace Problem336.FinitePosterior

variable {Θ Y : Type*} [Fintype Θ] [MeasurableSpace Θ]
    [MeasurableSingletonClass Θ] [MeasurableSpace Y]

def mixtureDensity (π : Measure Θ) (f : Θ → Y → ℝ≥0∞) (y : Y) : ℝ≥0∞ :=
  ∑ θ, π {θ} * f θ y

end Problem336.FinitePosterior

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_GaussianObservationKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Problem336.GaussianObservation

variable {ι α : Type*} [Fintype ι] [MeasurableSpace α]

def endpointKernel (v : ℝ≥0) (ξ : α → ι → ℝ) : Kernel α (ι → ℝ) :=
  (Kernel.const α (Measure.pi (fun _ : ι => gaussianReal 0 v))).withDensity
    (fun a y => ENNReal.ofReal (Real.exp (∑ i, (y i - (v : ℝ) / 2) * ξ a i)))

end Problem336.GaussianObservation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FiniteGaussianPosterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators ProbabilityTheory

namespace Problem336.FinitePosterior

variable {Θ ι : Type*} [Fintype Θ] [MeasurableSpace Θ]
    [MeasurableSingletonClass Θ] [Fintype ι]

def gaussianLikelihood (t : ℝ≥0) (signal : Θ → ι → ℝ) (θ : Θ) (y : ι → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (∑ i, (y i - (t : ℝ) / 2) * signal θ i))

end Problem336.FinitePosterior

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_BinaryGaussianPosterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators ProbabilityTheory

namespace Problem336.FinitePosterior

def binaryValue (b : Bool) : ℝ := if b then 1 else 0

def binarySummary {I ι : Type*} (observed : ι → I) (target : I) (x : I → Bool) :
    Bool × (ι → Bool) := (x target, fun j => x (observed j))

def gaussianFiniteTilt {I ι : Type*} [Fintype ι] (ν : Measure (I → Bool))
    (observed : ι → I) (target : I) (t : ℝ) (y : ι → ℝ) : ℝ :=
  (∫ x, Real.exp (∑ j, (y j - t / 2) * binaryValue (x (observed j))) *
    binaryValue (x target) ∂ν) /
  (∫ x, Real.exp (∑ j, (y j - t / 2) * binaryValue (x (observed j))) ∂ν)

end Problem336.FinitePosterior

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_BrownianBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336.BrownianBridge

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

def residual (B : ℝ≥0 → Ω → ℝ) (t s : ℝ≥0) (ω : Ω) : ℝ :=
  B s ω - (s : ℝ) / (t : ℝ) * B t ω

end Problem336.BrownianBridge

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_JointProcessLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

section PrivateCopy
open MeasureTheory Finset

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [LinearOrder T]

namespace Finset

variable (I : Finset T)

section Bot

variable [Bot T]

/-- (Mathlib private, copied: OpenAI imports it with `import all`.) Given a finite set `I : Finset T` of cardinality `n`,
`I.orderEmbOfFinWithBot : Fin (#I + 1) → T` is the map `(⊥, t₁, ..., tₙ)`,
where `t₁ < ... < tₙ` are the elements of `I` and `⊥` is the smallest element of `T`. -/
noncomputable def orderEmbOfFinWithBot (i : Fin (#I + 1)) : T :=
  if h : i = 0
    then ⊥
    else I.orderEmbOfFin rfl (i.pred h)

@[simp]
lemma orderEmbOfFinWithBot_zero : I.orderEmbOfFinWithBot 0 = ⊥ := rfl

end Bot

end Finset

namespace ProbabilityTheory

/-- `incrementsToRestrict I` is a continuous linear map `f` such that if `t₁ < ... < tₙ` are
then elements of `I`, then `f (xₜ₁, xₜ₂ - xₜ₁, ..., xₜₙ - xₜₙ₋₁) = (xₜ₁, ..., xₜₙ)`. -/
noncomputable def incrementsToRestrict (R : Type*) [Semiring R] [AddCommMonoid E]
    [Module R E] [TopologicalSpace E] [ContinuousAdd E] (I : Finset T) :
    (Fin #I → E) →L[R] (I → E) :=
  { toFun x i := ∑ j ≤ (I.orderIsoOfFin rfl).symm i, x j
    map_add' x y := by ext; simp [sum_add_distrib]
    map_smul' m x := by ext; simp [smul_sum]
    cont := by fun_prop }

end ProbabilityTheory
end PrivateCopy
end

section
-- module Solutions.OAIS_P336.SpanningForest_BrownianFamilyIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem336.BrownianFamilyIdentification

variable {I : Type*}

def vectorGaussian (S : Finset I) (h : ℝ≥0) : Measure (EuclideanSpace ℝ S) :=
  (Measure.infinitePi (fun _ : S => gaussianReal 0 h)).map
    (MeasurableEquiv.toLp 2 (S → ℝ))

instance instIsProbabilityMeasureEuclideanSpaceRealSubtypeMemFinsetVectorGaussian (S : Finset I) (h : ℝ≥0) : IsProbabilityMeasure (vectorGaussian S h) := by
  unfold vectorGaussian
  infer_instance

end Problem336.BrownianFamilyIdentification

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_BrownianReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336.BrownianReference

variable {A W I : Type*} [MeasurableSpace A] [MeasurableSpace W]
  (ν : Measure A) (ρ : Measure W) [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]

def coupling : Measure (A × (I → W)) := ν.prod (Measure.infinitePi (fun _ : I => ρ))

instance coupling_probability : IsProbabilityMeasure (coupling (I := I) ν ρ) := by
  unfold coupling
  infer_instance

end Problem336.BrownianReference

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_PosteriorIndependentExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory

namespace Problem336.Observation

def fieldRectangles {Ω : Type*} (m n : MeasurableSpace Ω) : Set (Set Ω) :=
  {s | ∃ a b, MeasurableSet[m] a ∧ MeasurableSet[n] b ∧ a ∩ b = s}

end Problem336.Observation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_ObservationPosterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

namespace Problem336.Observation

def finiteObservationFiltration {Ω I : Type*} {mΩ : MeasurableSpace Ω}
    (coordinate : I → MeasurableSpace Ω) (hcoordinate : ∀ i, coordinate i ≤ mΩ)
    (S : ℕ → Finset I) (hS : Monotone S) : Filtration ℕ mΩ where
  seq n := ⨆ i ∈ S n, coordinate i
  mono' := by
    intro n m hnm
    exact iSup_le fun i => iSup_le fun hi =>
      le_iSup_of_le i (le_iSup_of_le (hS hnm hi) le_rfl)
  le' n := iSup_le fun i => iSup_le fun _ => hcoordinate i

end Problem336.Observation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CanonicalDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace Problem336
namespace CanonicalDrift

def outerLimit {X : Type*} (b : ℕ → X → ℝ) (x : X) : ℝ :=
  Filter.limsup (fun n => b n x) Filter.atTop

end CanonicalDrift
end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_PosteriorTiltLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace Problem336.TiltLimit

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω]

def tiltedMean (μ : ProbabilityMeasure Ω) (h X : Ω → ℝ) : ℝ :=
  (∫ x, X x * Real.exp (h x) ∂(μ : Measure Ω)) /
    (∫ x, Real.exp (h x) ∂(μ : Measure Ω))

variable {I : Type*}

def bit (b : Bool) : ℝ := if b then 1 else 0

theorem continuous_bit : Continuous bit := continuous_of_discreteTopology

def finiteEnergy (S : Finset I) (h : I → ℝ) (x : I → Bool) : ℝ :=
  ∑ i ∈ S, h i * bit (x i)

def finiteTiltMean (μ : ProbabilityMeasure (I → Bool)) (S : Finset I) (h : I → ℝ) (e : I) : ℝ :=
  tiltedMean μ (finiteEnergy S h) (fun x => bit (x e))

end Problem336.TiltLimit

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_PosteriorDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Problem336.PosteriorDrift
open TiltLimit

variable {I : Type*} [Countable I]

def finiteStage (μ : ProbabilityMeasure (I → Bool)) (S : I → ℕ → Finset I)
    (e : I) (n : ℕ) (p : ℝ × (I → ℝ)) : ℝ :=
  finiteTiltMean μ (S e n) (fun i => p.2 i - p.1 / 2) e

def drift (μ : ProbabilityMeasure (I → Bool)) (S : I → ℕ → Finset I)
    (t : ℝ) (y : I → ℝ) (e : I) : ℝ :=
  CanonicalDrift.outerLimit (finiteStage μ S e) (t, y)

def FiniteResponseBound (μ : ProbabilityMeasure (I → Bool)) (S : I → ℕ → Finset I)
    (L : ℝ) : Prop :=
  ∀ (e : I) (n : ℕ) (h h' : I → ℝ) (D : ℝ), 0 ≤ D →
    (∀ i ∈ S e n, |h i - h' i| ≤ D) →
    |finiteTiltMean μ (S e n) h e - finiteTiltMean μ (S e n) h' e| ≤ L * D

end Problem336.PosteriorDrift

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CanonicalPosteriorIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem336.Observation

abbrev historySigma {Ω I T : Type*} (Y : I → T → Ω → ℝ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (p : I × T) => Y p.1 p.2 ω) inferInstance

end Problem336.Observation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CanonicalBrownianReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace Problem336.CanonicalBrownianReference

local instance instMeasurableSpacePath : MeasurableSpace GlobalWiener.Path := borel _
local instance instBorelSpacePath : BorelSpace GlobalWiener.Path := ⟨rfl⟩

abbrev Space (I : Type*) := (I → Bool) × (I → GlobalWiener.Path)

def noiseLaw (I : Type*) : Measure (I → GlobalWiener.Path) :=
  Measure.infinitePi (fun _ : I => GlobalWiener.wienerMeasure)

instance noiseLaw_probability (I : Type*) : IsProbabilityMeasure (noiseLaw I) := by
  unfold noiseLaw
  infer_instance

def law {I : Type*} (μ : ProbabilityMeasure (I → Bool)) : Measure (Space I) :=
  BrownianReference.coupling (μ : Measure (I → Bool)) GlobalWiener.wienerMeasure

instance law_probability {I : Type*} (μ : ProbabilityMeasure (I → Bool)) :
    IsProbabilityMeasure (law μ) := by
  unfold law
  infer_instance

def hidden {I : Type*} (q : Space I) : I → Bool := q.1

def noise {I : Type*} (i : I) (t : ℝ≥0) (q : Space I) : ℝ := q.2 i t

def observation {I : Type*} (t : ℝ≥0) (q : Space I) (i : I) : ℝ :=
  (t : ℝ) * TiltLimit.bit (hidden q i) + noise i t q

variable {I : Type*} (μ : ProbabilityMeasure (I → Bool))

theorem noise_jointlyMeasurable (i : I) :
    Measurable (fun p : ℝ≥0 × Space I => noise i p.1 p.2) := by
  exact continuous_eval.measurable.comp
    (((measurable_pi_apply i).comp measurable_snd.snd).prodMk measurable_fst)

theorem observation_jointlyMeasurable :
    Measurable (fun p : ℝ≥0 × Space I => observation p.1 p.2) := by
  apply Measurable.of_eval
  intro i
  exact ((measurable_subtype_coe.comp measurable_fst).mul
    (TiltLimit.continuous_bit.measurable.comp
      ((measurable_pi_apply i).comp measurable_snd.fst))).add (noise_jointlyMeasurable i)

end Problem336.CanonicalBrownianReference

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_InnovationMartingale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal

namespace Problem336.Innovation

def innovation {Ω : Type*} (X : Ω → ℝ) (B b : ℝ → Ω → ℝ)
    (t : ℝ) (ω : Ω) : ℝ :=
  t * X ω + B t ω - ∫ s in 0..t, b s ω

def nnInnovation {Ω : Type*} (X : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (b : ℝ → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  innovation X (fun s => B s.toNNReal) b t ω

@[simp]
theorem nnInnovation_apply {Ω : Type*} (X : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (b : ℝ → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    nnInnovation X B b t ω = (t : ℝ) * X ω + B t ω - ∫ s in 0..t, b s ω := by
  simp [nnInnovation, innovation]

end Problem336.Innovation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_ObservedBrownianMartingale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace Problem336.Innovation

def observationHistoryFiltration {I Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Y : ℝ≥0 → Ω → I → ℝ) (hY : ∀ t i, Measurable (fun ω => Y t ω i)) :
    Filtration ℝ≥0 mΩ where
  seq t := MeasurableSpace.comap (fun ω (p : I × Iic t) => Y p.2 ω p.1) inferInstance
  mono' := by
    intro u v huv
    let restrict : (I × Iic v → ℝ) → (I × Iic u → ℝ) :=
      fun f p => f (p.1, ⟨p.2, p.2.2.trans huv⟩)
    have hr : Measurable restrict := by fun_prop
    have heq : (fun ω (p : I × Iic u) => Y p.2 ω p.1) =
        restrict ∘ (fun ω (p : I × Iic v) => Y p.2 ω p.1) := rfl
    dsimp only
    rw [heq, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hr.comap_le
  le' t := (Measurable.of_eval (fun p : I × Iic t => hY p.2 p.1)).comap_le

end Problem336.Innovation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CanonicalPosteriorMartingale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336.CanonicalPosteriorMartingale

def observation {I Ω : Type*} (X : Ω → I → Bool)
    (B : I → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) (i : I) : ℝ :=
  (t : ℝ) * TiltLimit.bit (X ω i) + B i t ω

lemma measurable_observation {I Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → I → Bool) (hX : Measurable X) (B : I → ℝ≥0 → Ω → ℝ)
    (hBm : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (i : I) :
    Measurable (fun ω => observation X B t ω i) :=
  ((TiltLimit.continuous_bit.measurable.comp
    ((measurable_pi_apply i).comp hX)).const_mul _).add (hBm i t)

end Problem336.CanonicalPosteriorMartingale

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_ContinuousPathLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem336.ContinuousPathLaw

variable {I T : Type*} [TopologicalSpace T]
  [TopologicalSpace.SeparableSpace T] [Nonempty T]
  [MeasurableSpace C(T, ℝ)] [BorelSpace C(T, ℝ)]
  [StandardBorelSpace C(T, ℝ)]

def raw (x : I → C(T, ℝ)) : I → T → ℝ := fun i t => x i t

def denseEval (x : I → C(T, ℝ)) : I → ℕ → ℝ :=
  fun i n => x i (TopologicalSpace.denseSeq T n)

end Problem336.ContinuousPathLaw

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_InnovationErrorRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem336.Innovation

def gaussianErrorConstant (L c : ℝ) : ℝ :=
  16 * ((Real.sqrt c) ^ 3 * (∫ z : ℝ, |z| ^ 3 ∂gaussianReal 0 1) + L ^ 3) +
    L * Real.sqrt c + L ^ 2 / 2 + c ^ 2 / 4

end Problem336.Innovation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_InnovationPhaseRecurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal

namespace Problem336.InnovationPhaseRecurrence

def phaseOn {Ω : Type*} (A : Set Ω) (X Y : Ω → ℝ) : Ω → ℂ :=
  A.indicator (fun ω => Complex.exp (((Y ω - X ω : ℝ) : ℂ) * Complex.I))

def timeGrid (s d : ℝ≥0) (n k : ℕ) : ℝ≥0 :=
  s + (k : ℝ≥0) * (d / ((n + 1 : ℕ) : ℝ≥0))

@[simp] lemma timeGrid_zero (s d : ℝ≥0) (n : ℕ) : timeGrid s d n 0 = s := by
  simp [timeGrid]

@[simp] lemma timeGrid_finish (s d : ℝ≥0) (n : ℕ) :
    timeGrid s d n (n + 1) = s + d := by
  simp [timeGrid, mul_div_cancel₀]

end Problem336.InnovationPhaseRecurrence

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_RawInnovationSampler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem336.RawInnovationSampler

variable {I Ω : Type*}

def observation (X : Ω → I → Bool) (B : I → ℝ≥0 → Ω → ℝ)
    (ω : Ω) (i : I) (t : ℝ≥0) : ℝ :=
  (t : ℝ) * bitValue (X ω i) + B i t ω

def rawInnovation (X : Ω → I → Bool) (B : I → ℝ≥0 → Ω → ℝ)
    (b : ℝ → (I → ℝ) → I → ℝ) (ω : Ω) (i : I) (t : ℝ≥0) : ℝ :=
  Innovation.nnInnovation (fun ω => bitValue (X ω i)) (B i)
    (fun s ω => b s (fun j => observation X B ω j s.toNNReal) i) t ω

@[simp]
lemma rawInnovation_apply (X : Ω → I → Bool) (B : I → ℝ≥0 → Ω → ℝ)
    (b : ℝ → (I → ℝ) → I → ℝ) (ω : Ω) (i : I) (t : ℝ≥0) :
    rawInnovation X B b ω i t = observation X B ω i t -
      ∫ s in (0 : ℝ)..t, b s (fun j => observation X B ω j s.toNNReal) i := by
  simp only [rawInnovation, Innovation.nnInnovation_apply, observation]

end Problem336.RawInnovationSampler

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CanonicalBrownianSampler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace Problem336.CanonicalBrownianSampler

local instance instMeasurableSpacePath : MeasurableSpace GlobalWiener.Path := borel _

open CanonicalBrownianReference

variable {I : Type*} [countableIndices : Countable I]

def signal (q : Space I) (i : I) : ℝ := TiltLimit.bit (CanonicalBrownianReference.hidden q i)

def driftField (μ : ProbabilityMeasure (I → Bool)) (S : I → ℕ → Finset I)
    (i : I) (s : ℝ) (q : Space I) : ℝ :=
  PosteriorDrift.drift μ S s (CanonicalBrownianReference.observation s.toNNReal q) i

omit countableIndices in
theorem observation_measurable [Countable I] (t : ℝ≥0) (i : I) :
    Measurable (fun q : Space I => CanonicalBrownianReference.observation t q i) :=
  (measurable_pi_apply i).comp (observation_jointlyMeasurable.comp
    (measurable_const.prodMk measurable_id))

def filtration : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Space I)) :=
  Innovation.observationHistoryFiltration CanonicalBrownianReference.observation observation_measurable

end Problem336.CanonicalBrownianSampler

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CauchyBinet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix Polynomial
open scoped BigOperators

namespace Problem336.CauchyBinet

variable {R m n : Type*} [CommRing R]
variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

abbrev ColumnSets (n m : Type*) [Fintype n] [Fintype m] :=
  ((Finset.univ : Finset m).powersetCard (Fintype.card n))

def columnIndexEquiv (s : ColumnSets n m) : (s.val : Finset m) ≃ n :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_coe]
    exact (Finset.mem_powersetCard.mp s.property).2)

def columnMinor (A : Matrix n m R) (s : ColumnSets n m) :
    Matrix (s.val : Finset m) (s.val : Finset m) R :=
  A.submatrix (columnIndexEquiv s) Subtype.val

end Problem336.CauchyBinet

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_ReducedLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem336.ReducedLaplacian

open scoped BigOperators Matrix

variable {V E : Type*}

def EdgeAdj (src dst : E → V) (u v : V) : Prop :=
  ∃ e, (src e = u ∧ dst e = v) ∨ (src e = v ∧ dst e = u)

def Connected (src dst : E → V) : Prop :=
  ∀ u v, Relation.ReflTransGen (EdgeAdj src dst) u v

variable [DecidableEq V]

def extendZero (root : V) (x : {v : V // v ≠ root} → ℝ) (v : V) : ℝ :=
  if hv : v ≠ root then x ⟨v, hv⟩ else 0

@[simp] theorem extendZero_root (root : V) (x : {v : V // v ≠ root} → ℝ) :
    extendZero root x root = 0 := by simp [extendZero]

@[simp] theorem extendZero_subtype (root : V) (x : {v : V // v ≠ root} → ℝ)
    (v : {v : V // v ≠ root}) : extendZero root x v = x v := by
  simp [extendZero, v.property]

def reducedGradient (src dst : E → V) (root : V) :
    Matrix E {v : V // v ≠ root} ℝ :=
  fun e v => (if v.val = src e then 1 else 0) - (if v.val = dst e then 1 else 0)

variable [Fintype V]

variable [Fintype E] [DecidableEq E]

def weightedLaplacian (src dst : E → V) (root : V) (w : E → ℝ) :
    Matrix {v : V // v ≠ root} {v : V // v ≠ root} ℝ :=
  (reducedGradient src dst root)ᵀ * Matrix.diagonal w * reducedGradient src dst root

end Problem336.ReducedLaplacian

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CodeLaplacian
attribute [-instance] _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem336

open scoped Matrix

variable {G : GraphCode} {K : FiniteSubgraphCode}

def codeSource (hK : IsFiniteConnectedSubgraph G K) (e : K.2) : K.1 :=
  ⟨e.val.1, (hK.2.1 e.val e.property).1⟩

def codeTarget (hK : IsFiniteConnectedSubgraph G K) (e : K.2) : K.1 :=
  ⟨e.val.2, (hK.2.1 e.val e.property).2.1⟩

def codeWeightedLaplacian (hK : IsFiniteConnectedSubgraph G K)
    (root : K.1) (w : K.2 → ℝ) :
    Matrix {v : K.1 // v ≠ root} {v : K.1 // v ≠ root} ℝ :=
  ReducedLaplacian.weightedLaplacian (codeSource hK) (codeTarget hK) root w

end Problem336

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FiniteCycleIncidence
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem336

instance finiteCodeEdgesFintype (K : FiniteSubgraphCode) : Fintype (finiteCodeEdges K) :=
  (finiteCodeEdges_finite K).fintype

def finiteFlowEmbedding (K : FiniteSubgraphCode) :
    (finiteCodeEdges K → ℝ) →ₗ[ℝ] EdgeFlow :=
  Fintype.linearCombination ℝ (fun e : finiteCodeEdges K => Finsupp.single e.1 1)

@[simp] theorem finiteFlowEmbedding_apply (K : FiniteSubgraphCode)
    (x : finiteCodeEdges K → ℝ) (e : finiteCodeEdges K) :
    finiteFlowEmbedding K x e.1 = x e := by
  classical
  simp only [finiteFlowEmbedding, Fintype.linearCombination_apply, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
  rw [Finset.sum_eq_single e]
  · simp
  · intro b hb hbe
    have hval : b.1 ≠ e.1 := fun h => hbe (Subtype.ext h)
    simp [hval]
  · simp

def finiteIncidence (K : FiniteSubgraphCode) :
    Matrix ↥K.1 (finiteCodeEdges K) ℝ :=
  fun v e => (if v.1 = e.1.1.1 then 1 else 0) - (if v.1 = e.1.1.2 then 1 else 0)

def finiteHilbertEmbeddingLinear (K : FiniteSubgraphCode) :
    EuclideanSpace ℝ (finiteCodeEdges K) →ₗ[ℝ] EdgeHilbert :=
  (edgeFlowToHilbert.comp (finiteFlowEmbedding K)).comp
    (WithLp.linearEquiv 2 ℝ (finiteCodeEdges K → ℝ)).toLinearMap

@[simp] theorem finiteHilbertEmbeddingLinear_apply (K : FiniteSubgraphCode)
    (x : EuclideanSpace ℝ (finiteCodeEdges K)) (e : finiteCodeEdges K) :
    finiteHilbertEmbeddingLinear K x e.1 = x e := by
  simp [finiteHilbertEmbeddingLinear]

 theorem finiteHilbertEmbeddingLinear_sum (K : FiniteSubgraphCode)
    (x : EuclideanSpace ℝ (finiteCodeEdges K)) :
    finiteHilbertEmbeddingLinear K x =
      ∑ e : finiteCodeEdges K, x e • lp.single 2 e.1 (1 : ℝ) := by
  simp [finiteHilbertEmbeddingLinear, finiteFlowEmbedding, Fintype.linearCombination_apply,
    map_sum, ← lp.single_smul]

 theorem finiteHilbertEmbeddingLinear_inner (K : FiniteSubgraphCode)
    (x y : EuclideanSpace ℝ (finiteCodeEdges K)) :
    inner ℝ (finiteHilbertEmbeddingLinear K x) (finiteHilbertEmbeddingLinear K y) =
      inner ℝ x y := by
  classical
  rw [finiteHilbertEmbeddingLinear_sum K x]
  simp [sum_inner, inner_smul_left, lp.inner_single_left, PiLp.inner_apply,
    finiteHilbertEmbeddingLinear_apply, mul_comm]

def finiteHilbertEmbedding (K : FiniteSubgraphCode) :
    EuclideanSpace ℝ (finiteCodeEdges K) →ₗᵢ[ℝ] EdgeHilbert :=
  (finiteHilbertEmbeddingLinear K).isometryOfInner (finiteHilbertEmbeddingLinear_inner K)

@[simp] theorem finiteHilbertEmbedding_apply (K : FiniteSubgraphCode)
    (x : EuclideanSpace ℝ (finiteCodeEdges K)) (e : finiteCodeEdges K) :
    finiteHilbertEmbedding K x e.1 = x e :=
  finiteHilbertEmbeddingLinear_apply K x e

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_IncidenceCirculation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
open Matrix

namespace Problem336.IncidenceCirculation

variable {V E R : Type*} [DecidableEq V] [Fintype V] [Fintype E] [CommRing R]

def incidence (src dst : E → V) : Matrix V E R :=
  fun v e => (if v = src e then 1 else 0) - (if v = dst e then 1 else 0)

def reducedIncidence (src dst : E → V) (root : V) : Matrix {v : V // v ≠ root} E R :=
  fun v e => incidence src dst v.1 e

omit [Fintype E] in
@[simp] theorem sum_incidence_column (src dst : E → V) (e : E) :
    ∑ v, incidence (R := R) src dst v e = 0 := by
  simp [incidence, Finset.sum_sub_distrib]

end Problem336.IncidenceCirculation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_TransferProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem336
namespace TransferProjection

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def transferMatrix (A : Matrix m n ℝ) : Matrix n n ℝ :=
  A.transpose * (A * A.transpose)⁻¹ * A

end TransferProjection
end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_ReducedCycleKernel
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem336
namespace ReducedCycleKernel

def reducedFiniteIncidence (K : FiniteSubgraphCode) (root : ↥K.1) :
    Matrix {v : ↥K.1 // v ≠ root} (finiteCodeEdges K) ℝ :=
  fun v e => finiteIncidence K v.1 e

variable {G : GraphCode} {K : FiniteSubgraphCode}

def codeSource (hK : IsFiniteConnectedSubgraph G K) (e : finiteCodeEdges K) : ↥K.1 :=
  ⟨e.1.1.1, (hK.2.1 e.1.1 e.2).1⟩

def codeDestination (hK : IsFiniteConnectedSubgraph G K) (e : finiteCodeEdges K) : ↥K.1 :=
  ⟨e.1.1.2, (hK.2.1 e.1.1 e.2).2.1⟩

end ReducedCycleKernel
end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CodeTransferKernel
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem336
namespace CodeTransferKernel

open scoped Matrix

variable {G : GraphCode} {K : FiniteSubgraphCode}

def edgeEquiv (hK : IsFiniteConnectedSubgraph G K) : K.2 ≃ finiteCodeEdges K where
  toFun e := ⟨⟨e.1, (hK.2.1 e.1 e.2).2.2.1⟩, e.2⟩
  invFun e := ⟨e.1.1, e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def incidence (hK : IsFiniteConnectedSubgraph G K) (root : K.1) :
    Matrix {v : K.1 // v ≠ root} K.2 ℝ :=
  (ReducedLaplacian.reducedGradient (Problem336.codeSource hK)
    (Problem336.codeTarget hK) root).transpose

end CodeTransferKernel
end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FiniteIncidenceBridge
attribute [-instance] _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem336.FiniteIncidence

def ValidEdges (V : Finset ℕ) (T : Finset (ℕ × ℕ)) : Prop :=
  ∀ p ∈ T, p.1 ∈ V ∧ p.2 ∈ V ∧ p.1 < p.2

def src (V : Finset ℕ) (T : Finset (ℕ × ℕ)) (h : ValidEdges V T) : T → V :=
  fun e => ⟨e.val.1, (h e.val e.property).1⟩

def dst (V : Finset ℕ) (T : Finset (ℕ × ℕ)) (h : ValidEdges V T) : T → V :=
  fun e => ⟨e.val.2, (h e.val e.property).2.1⟩

theorem validEdges_of_subgraph {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) {T : Finset (ℕ × ℕ)} (hT : T ⊆ K.2) :
    ValidEdges K.1 T := by
  intro p hp
  have h := hK.2.1 p (hT hp)
  exact ⟨h.1, h.2.1, h.2.2.1⟩

end Problem336.FiniteIncidence

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_DisconnectedIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Matrix

namespace Problem336.IncidenceDisconnected

variable {V E : Type*}

def EndpointAdj (src dst : E → V) (u v : V) : Prop :=
  ∃ e, (src e = u ∧ dst e = v) ∨ (src e = v ∧ dst e = u)

variable [Fintype V] [DecidableEq V]

def reducedIncidence (r : V) (src dst : E → V) :
    Matrix {v : V // v ≠ r} E ℝ :=
  fun v e => (if v.1 = src e then 1 else 0) - (if v.1 = dst e then 1 else 0)

end Problem336.IncidenceDisconnected

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_IncidenceUnimodular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Matrix

namespace Problem336.Incidence

variable {V E : Type*} [DecidableEq V]

def signedIncidence (src dst : E → V) : Matrix V E ℝ :=
  fun v e => (if v = src e then 1 else 0) - (if v = dst e then 1 else 0)

end Problem336.Incidence

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CodedIncidenceMinors
attribute [-instance] _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Matrix
open Classical

namespace Problem336.FiniteIncidence

def selectedEdges {K : FiniteSubgraphCode} (s : Finset K.2) : Finset (ℕ × ℕ) :=
  s.map (Function.Embedding.subtype (fun p => p ∈ K.2))

@[simp] theorem selectedEdges_card {K : FiniteSubgraphCode} (s : Finset K.2) :
    (selectedEdges s).card = s.card := Finset.card_map _

def selectedEdgeEquiv {K : FiniteSubgraphCode} (s : Finset K.2) :
    s ≃ selectedEdges s :=
  Equiv.ofBijective
    (fun e => ⟨e.val.val, Finset.mem_map.mpr ⟨e.val, e.property, rfl⟩⟩)
    ⟨by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun p : selectedEdges s => p.val) hab,
     by
      intro p
      obtain ⟨e, he, hep⟩ := Finset.mem_map.mp p.property
      exact ⟨⟨e, he⟩, Subtype.ext hep⟩⟩

end Problem336.FiniteIncidence

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_SubtypeSubsetSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem336.SubtypeSubsetSums

variable {α : Type*}

def forget (s : Finset α) (T : Finset s) : Finset α :=
  T.map (Function.Embedding.subtype (· ∈ s))

@[simp] theorem card_forget (s : Finset α) (T : Finset s) :
    (forget s T).card = T.card := Finset.card_map _

@[simp] theorem mem_forget (s : Finset α) (T : Finset s) (a : s) :
    a.val ∈ forget s T ↔ a ∈ T := by
  simp [forget]

@[simp] theorem forget_univ (s : Finset α) :
    forget s Finset.univ = s := by
  rw [forget, Finset.univ_eq_attach, Finset.attach_map_val]

end Problem336.SubtypeSubsetSums

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CodedMatrixTree
attribute [-instance] _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Matrix
open Classical

namespace Problem336

variable {G : GraphCode} {K : FiniteSubgraphCode}

def codeIncidence (hK : IsFiniteConnectedSubgraph G K) (root : K.1) :
    Matrix {v : K.1 // v ≠ root} K.2 ℝ :=
  (ReducedLaplacian.reducedGradient (codeSource hK) (codeTarget hK) root).transpose

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CodedInclusion
attribute [-instance] _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Polynomial Matrix
open Classical Polynomial

namespace Problem336

variable {G : GraphCode} {K : FiniteSubgraphCode}

def codeTransferCurrent (hK : IsFiniteConnectedSubgraph G K) (root : K.1)
    (c : (ℕ × ℕ) → ℝ) (S : Finset K.2) : Matrix S S ℝ :=
  Matrix.diagonal (fun e : S => c e.val.val) *
    ((codeIncidence hK root).submatrix id (Subtype.val : S → K.2)).transpose *
      (codeWeightedLaplacian hK root (fun e => c e.val))⁻¹ *
      (codeIncidence hK root).submatrix id (Subtype.val : S → K.2)

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_CoordinateTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology ENNReal

namespace Problem336.CoordinateTruncation

variable {ι 𝕜 : Type*} [DecidableEq ι] [RCLike 𝕜]

abbrev Space (ι 𝕜 : Type*) [RCLike 𝕜] := lp (fun _ : ι => 𝕜) 2

def truncate (s : Finset ι) : Space ι 𝕜 →L[𝕜] Space ι 𝕜 :=
  ∑ i ∈ s, (lp.singleContinuousLinearMap 𝕜 (fun _ : ι => 𝕜) 2 i).comp
    (lp.evalCLM 𝕜 (fun _ : ι => 𝕜) 2 i)

def supported (s : Set ι) : Submodule 𝕜 (Space ι 𝕜) where
  carrier := {x | ∀ i, i ∉ s → x i = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i hi; simp [hx i hi, hy i hi]
  smul_mem' := by intro c x hx i hi; simp [hx i hi]

omit [DecidableEq ι] in
@[simp] theorem mem_supported (s : Set ι) (x : Space ι 𝕜) :
    x ∈ supported s ↔ ∀ i, i ∉ s → x i = 0 := Iff.rfl

instance supported_isClosed (s : Set ι) :
    IsClosed (supported (𝕜 := 𝕜) s : Set (Space ι 𝕜)) := by
  change IsClosed {x : Space ι 𝕜 | ∀ i, i ∉ s → x i = 0}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro hi
  exact isClosed_eq ((continuous_apply i).comp lp.uniformContinuous_coe.continuous)
    continuous_const

instance supported_completeSpace (s : Set ι) :
    CompleteSpace (supported (𝕜 := 𝕜) s) := IsClosed.completeSpace_coe

instance supported_hasOrthogonalProjection (s : Set ι) :
    (supported (𝕜 := 𝕜) s).HasOrthogonalProjection := inferInstance

end Problem336.CoordinateTruncation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_ExhaustionExistence
attribute [-instance] _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem336

def inducedFiniteCode (G : GraphCode) (S : Finset ℕ) : FiniteSubgraphCode := by
  classical
  exact (S, (S.product S).filter (fun p => p.1 < p.2 ∧ Adj G p.1 p.2))

@[simp] theorem mem_inducedFiniteCode_edges {G : GraphCode} {S : Finset ℕ}
    {u v : ℕ} :
    (u, v) ∈ (inducedFiniteCode G S).2 ↔
      u ∈ S ∧ v ∈ S ∧ u < v ∧ Adj G u v := by
  classical
  constructor
  · intro h
    have hfilter := Finset.mem_filter.mp h
    have hprod := Finset.mem_product.mp hfilter.1
    exact ⟨hprod.1, hprod.2, hfilter.2.1, hfilter.2.2⟩
  · rintro ⟨hu, hv, hlt, hadj⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu, hv⟩, hlt, hadj⟩

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_InducedCode
attribute [-instance] _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem336

def inducedCode (G : GraphCode) (S : Finset ℕ) : FiniteSubgraphCode := by
  classical
  exact (S, (S.product S).filter (fun p => p.1 < p.2 ∧ Adj G p.1 p.2))

@[simp] theorem inducedCode_vertices (G : GraphCode) (S : Finset ℕ) :
    (inducedCode G S).1 = S := rfl

@[simp] theorem mem_inducedCode_edges (G : GraphCode) (S : Finset ℕ) (p : ℕ × ℕ) :
    p ∈ (inducedCode G S).2 ↔ p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 < p.2 ∧ Adj G p.1 p.2 := by
  classical
  rcases p with ⟨u, v⟩
  simp only [inducedCode, Finset.mem_filter]
  have hprod : (u,v) ∈ S.product S ↔ u ∈ S ∧ v ∈ S := Finset.mem_product
  rw [hprod]
  tauto

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_IntrinsicBridge
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem336.Intrinsic

def exhaustion (G : GraphCode) (e : EdgeCode) (n : ℕ) : FiniteSubgraphCode :=
  inducedCode G (edgeBallCode G n e)

end Problem336.Intrinsic

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_GraphTreePosterior
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem336.GraphTreePosterior

def energy (T : Finset (ℕ × ℕ)) (S : Finset EdgeCode)
    (t : ℝ) (y : EdgeCode → ℝ) : ℝ := by
  classical
  exact ∑ f ∈ S, if f.1 ∈ T then y f - t / 2 else 0

def weight (T : Finset (ℕ × ℕ)) (S : Finset EdgeCode)
    (t : ℝ) (y : EdgeCode → ℝ) : ℝ := Real.exp (energy T S t y)

def partition (K : FiniteSubgraphCode) (S : Finset EdgeCode)
    (t : ℝ) (y : EdgeCode → ℝ) : ℝ :=
  ∑ T ∈ spanningTrees K, weight T S t y

def numerator (K : FiniteSubgraphCode) (e : EdgeCode) (S : Finset EdgeCode)
    (t : ℝ) (y : EdgeCode → ℝ) : ℝ := by
  classical
  exact ∑ T ∈ (spanningTrees K).filter (fun T => e.1 ∈ T), weight T S t y

def mean (K : FiniteSubgraphCode) (e : EdgeCode) (S : Finset EdgeCode)
    (t : ℝ) (y : EdgeCode → ℝ) : ℝ := numerator K e S t y / partition K S t y

def edgeCodes (K : FiniteSubgraphCode) : Finset EdgeCode :=
  K.2.subtype (fun p => p.1 < p.2)

@[simp] theorem mem_edgeCodes (K : FiniteSubgraphCode) (e : EdgeCode) :
    e ∈ edgeCodes K ↔ e.1 ∈ K.2 := Finset.mem_subtype

def finiteBallMean (G : GraphCode) (e : EdgeCode) (n m : ℕ)
    (t : ℝ) (y : EdgeCode → ℝ) : ℝ :=
  mean (Intrinsic.exhaustion G e m) e (edgeCodes (Intrinsic.exhaustion G e n)) t y

end Problem336.GraphTreePosterior

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FiniteUSTMeasure
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Problem336

attribute [local instance] Classical.propDecidable

def finiteTreeConfiguration (T : Finset (ℕ × ℕ)) : EdgeConfiguration :=
  fun e => decide (e.1 ∈ T)

def edgeCylinder (A B : Finset EdgeCode) : Set EdgeConfiguration :=
  {X | (∀ e ∈ A, X e = true) ∧ (∀ e ∈ B, X e = false)}

def finiteUSTMeasure (K : FiniteSubgraphCode) : Measure EdgeConfiguration :=
  (↑(spanningTrees K).card : ℝ≥0∞)⁻¹ •
    ∑ T ∈ spanningTrees K, Measure.dirac (finiteTreeConfiguration T)

lemma finiteUSTMeasure_apply (K : FiniteSubgraphCode)
    (s : Set EdgeConfiguration) (hs : MeasurableSet s) :
    finiteUSTMeasure K s =
      (↑((spanningTrees K).filter (fun T => finiteTreeConfiguration T ∈ s)).card : ℝ≥0∞) /
        (↑(spanningTrees K).card : ℝ≥0∞) := by
  classical
  simp only [finiteUSTMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.finsetSum_apply, Measure.dirac_apply' _ hs, Set.indicator_apply,
    Pi.one_apply]
  rw [ENNReal.div_eq_inv_mul]
  congr 1
  simp

lemma finiteUSTMeasure_isProbabilityMeasure (K : FiniteSubgraphCode)
    (hK : (spanningTrees K).Nonempty) : IsProbabilityMeasure (finiteUSTMeasure K) := by
  constructor
  rw [finiteUSTMeasure_apply K Set.univ MeasurableSet.univ]
  simp only [Set.mem_univ, Finset.filter_true]
  exact ENNReal.div_self (by exact_mod_cast Finset.card_ne_zero.mpr hK) (by simp)

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FiniteUSTLimit
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Problem336

def finiteUSTProbabilityMeasure (K : FiniteSubgraphCode)
    (hK : (spanningTrees K).Nonempty) : ProbabilityMeasure EdgeConfiguration :=
  ⟨finiteUSTMeasure K, finiteUSTMeasure_isProbabilityMeasure K hK⟩

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_GraphEncoding
attribute [-instance] _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem336
namespace FiniteEncoding

lemma rawPair_comm (u v : ℕ) : rawPair u v = rawPair v u := by
  unfold rawPair
  split_ifs <;> simp_all <;> omega

def graph (K : FiniteSubgraphCode) : SimpleGraph {v : ℕ // v ∈ K.1} where
  Adj u v := u ≠ v ∧ rawPair u.1 v.1 ∈ K.2
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, by simpa [rawPair_comm] using h.2⟩⟩
  loopless := ⟨by
    intro u h
    exact h.1 rfl⟩

lemma rawPair_self (u : ℕ) : rawPair u u = (u,u) := by simp [rawPair]

lemma rawPair_ne_of_mem {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) {u v : ℕ}
    (h : rawPair u v ∈ K.2) : u ≠ v := by
  intro huv
  subst v
  have hp := (hK.2.1 _ h).2.2.1
  simp [rawPair_self] at hp

lemma reachable_of_subgraphPath {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) {u v : ℕ}
    (p : Relation.ReflTransGen (SubgraphAdj K) u v)
    (hu : u ∈ K.1) (hv : v ∈ K.1) :
    (graph K).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  induction p with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail w z p hwz ih =>
    exact (ih hwz.1).trans (SimpleGraph.Adj.reachable (G := graph K)
      ⟨by intro he; exact rawPair_ne_of_mem hK hwz.2.2 (congrArg Subtype.val he), hwz.2.2⟩)

lemma connected {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) : (graph K).Connected := by
  obtain ⟨u, hu⟩ := hK.1
  let : Nonempty {v : ℕ // v ∈ K.1} := ⟨⟨u, hu⟩⟩
  exact ⟨fun v w => reachable_of_subgraphPath hK
    (hK.2.2 v.1 v.2 w.1 w.2) v.2 w.2⟩

def edgePair {s : Finset ℕ} : Sym2 {v : ℕ // v ∈ s} → ℕ × ℕ :=
  Sym2.lift ⟨fun u v => rawPair u.1 v.1, fun u v => rawPair_comm u.1 v.1⟩

@[simp] lemma edgePair_mk {s : Finset ℕ} (u v : {v : ℕ // v ∈ s}) :
    edgePair s(u,v) = rawPair u.1 v.1 := rfl

lemma edgePair_forget {s : Finset ℕ} (e : Sym2 {v : ℕ // v ∈ s}) :
    s((edgePair e).1, (edgePair e).2) = Sym2.map Subtype.val e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [edgePair_mk, Sym2.map_mk]
    unfold rawPair
    split_ifs
    · rfl
    · exact Sym2.eq_swap

lemma edgePair_injective {s : Finset ℕ} :
    Function.Injective (edgePair (s := s)) := by
  intro a b hab
  apply Sym2.map.injective Subtype.val_injective
  rw [← edgePair_forget a, ← edgePair_forget b, hab]

def edgePairs {s : Finset ℕ} (F : SimpleGraph {v : ℕ // v ∈ s}) :
    Finset (ℕ × ℕ) := by
  classical
  exact F.edgeFinset.image edgePair

lemma card_edgePairs {s : Finset ℕ} (F : SimpleGraph {v : ℕ // v ∈ s}) :
    (edgePairs F).card = Nat.card F.edgeSet := by
  classical
  rw [edgePairs, Finset.card_image_of_injective _ edgePair_injective,
    SimpleGraph.edgeFinset, Set.toFinset_card, Nat.card_eq_fintype_card]

lemma rawPair_mem_edgePairs {s : Finset ℕ} {F : SimpleGraph {v : ℕ // v ∈ s}}
    {u v : {v : ℕ // v ∈ s}} (h : F.Adj u v) :
    rawPair u.1 v.1 ∈ edgePairs F := by
  classical
  exact Finset.mem_image.mpr ⟨s(u,v), by simpa using h, rfl⟩

lemma edgePairs_subset {K : FiniteSubgraphCode}
    {F : SimpleGraph {v : ℕ // v ∈ K.1}} (hF : F ≤ graph K) :
    edgePairs F ⊆ K.2 := by
  classical
  intro p hp
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
  induction e using Sym2.inductionOn with
  | _ u v =>
    have h : F.Adj u v := by simpa using he
    exact (hF h).2

lemma treeOn_edgePairs {K : FiniteSubgraphCode}
    {F : SimpleGraph {v : ℕ // v ∈ K.1}}
    (hF : F ≤ graph K) (hT : F.IsTree) : TreeOn K (edgePairs F) := by
  classical
  refine ⟨edgePairs_subset hF, ?_, ?_⟩
  · rw [card_edgePairs]
    simpa [SimpleGraph.edgeFinset, Nat.card_eq_fintype_card] using hT.card_edgeFinset
  · intro u hu v hv
    have hp := (F.reachable_iff_reflTransGen _ _).mp
      (hT.connected ⟨u, hu⟩ ⟨v,hv⟩)
    exact hp.lift Subtype.val (fun a b hab => rawPair_mem_edgePairs hab)

lemma mem_spanningTrees_iff {K : FiniteSubgraphCode} {T : Finset (ℕ × ℕ)} :
    T ∈ spanningTrees K ↔ TreeOn K T := by
  classical
  simp only [spanningTrees, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨And.right, fun h => ⟨h.1,h⟩⟩

lemma spanningTrees_nonempty {G : GraphCode} {K : FiniteSubgraphCode}
    (hK : IsFiniteConnectedSubgraph G K) : (spanningTrees K).Nonempty := by
  obtain ⟨F, hF, hT⟩ := (connected hK).exists_isTree_le
  exact ⟨edgePairs F, mem_spanningTrees_iff.mpr (treeOn_edgePairs hF hT)⟩

end FiniteEncoding
end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_IntrinsicTreeDrift
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace Problem336.GraphTreePosterior

def innerMean (G : GraphCode)
    (e : EdgeCode) (n : ℕ) (t : ℝ) (y : EdgeCode → ℝ) : ℝ :=
  CanonicalDrift.outerLimit
    (fun m (q : ℝ × (EdgeCode → ℝ)) => finiteBallMean G e n m q.1 q.2) (t, y)

def drift (G : GraphCode)
    (t : ℝ) (y : EdgeCode → ℝ) (e : EdgeCode) : ℝ :=
  CanonicalDrift.outerLimit
    (fun n (q : ℝ × (EdgeCode → ℝ)) => innerMean G e n q.1 q.2) (t, y)

end Problem336.GraphTreePosterior

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FiniteGradientResponse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem336.FiniteGradientResponse

variable {ι : Type*}

def segmentField (h k : ι → ℝ) (t : ℝ) : ι → ℝ :=
  fun i => h i + t * (k i - h i)

@[simp] theorem segmentField_zero (h k : ι → ℝ) : segmentField h k 0 = h := by
  funext i
  simp [segmentField]

@[simp] theorem segmentField_one (h k : ι → ℝ) : segmentField h k 1 = k := by
  funext i
  simp [segmentField]

end Problem336.FiniteGradientResponse

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_TransferCurrent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Operator

namespace Problem336.TransferCurrent

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance instTopologicalSpaceMatrixReal_solutions : TopologicalSpace (Matrix n n ℝ) :=
  (Matrix.linftyOpNormedAddCommGroup : NormedAddCommGroup (Matrix n n ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

def bilinear (M : Matrix n n ℝ) (a b : n → ℝ) : ℝ :=
  a ⬝ᵥ (M *ᵥ b)

def bilinearCLM (a b : n → ℝ) : Matrix n n ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => bilinear M a b
      map_add' := by
        intro M N
        simp [bilinear, Matrix.add_mulVec, dotProduct_add]
      map_smul' := by
        intro c M
        simp [bilinear, Matrix.smul_mulVec, dotProduct_smul] }

@[simp] lemma bilinearCLM_apply (a b : n → ℝ) (M : Matrix n n ℝ) :
    bilinearCLM a b M = bilinear M a b := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def laplacian (a : ι → n → ℝ) (h : ι → ℝ) : Matrix n n ℝ :=
  ∑ i, Real.exp (h i) • Matrix.vecMulVec (a i) (a i)

def marginal (a : ι → n → ℝ) (h : ι → ℝ) (e : ι) : ℝ :=
  Real.exp (h e) * bilinear (laplacian a h)⁻¹ (a e) (a e)

def responseSquare (a : ι → n → ℝ) (h : ι → ℝ) (e f : ι) : ℝ :=
  Real.exp (h e) * Real.exp (h f) *
    (bilinear (laplacian a h)⁻¹ (a e) (a f))^2

def response (a : ι → n → ℝ) (h : ι → ℝ) (e f : ι) : ℝ :=
  (if e = f then marginal a h e else 0) - responseSquare a h e f

end Problem336.TransferCurrent

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_TransferCurrentLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Operator

namespace Problem336.TransferCurrent

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance instTopologicalSpaceMatrixReal_solutions_1 : TopologicalSpace (Matrix n n ℝ) :=
  (Matrix.linftyOpNormedAddCommGroup : NormedAddCommGroup (Matrix n n ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

open FiniteGradientResponse

end Problem336.TransferCurrent

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FiniteResponse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem336.FiniteResponse

variable {Ω E : Type*} [Fintype Ω] [Fintype E]

def mean (p : Ω → ℝ) (x : Ω → E → ℝ) (e : E) : ℝ :=
  ∑ ω, p ω * x ω e

end Problem336.FiniteResponse

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_USTResponse
attribute [-instance] _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem336.USTResponse

abbrev TreeSample (K : FiniteSubgraphCode) :=
  {T : Finset (ℕ × ℕ) // T ∈ spanningTrees K}

abbrev FiniteEdge (K : FiniteSubgraphCode) :=
  {e : ℕ × ℕ // e ∈ K.2}

def indicator (K : FiniteSubgraphCode) (T : TreeSample K) (e : FiniteEdge K) : ℝ :=
  if e.1 ∈ T.1 then 1 else 0

lemma tree_property (K : FiniteSubgraphCode) (T : TreeSample K) : TreeOn K T.1 := by
  classical
  exact (Finset.mem_filter.mp T.2).2

def weight (K : FiniteSubgraphCode) (h : FiniteEdge K → ℝ) (T : TreeSample K) : ℝ :=
  Real.exp (∑ e, h e * indicator K T e)

def partition (K : FiniteSubgraphCode) (h : FiniteEdge K → ℝ) : ℝ :=
  ∑ T : TreeSample K, weight K h T

def mass (K : FiniteSubgraphCode) (h : FiniteEdge K → ℝ) (T : TreeSample K) : ℝ :=
  weight K h T / partition K h

def inclusion (K : FiniteSubgraphCode) (h : FiniteEdge K → ℝ) (e : FiniteEdge K) : ℝ :=
  FiniteResponse.mean (mass K h) (indicator K) e

end Problem336.USTResponse

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_WeightedTreeBorel
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem336.WeightedTree

abbrev Field := (ℕ × ℕ) → ℝ

def weight (h : Field) (T : Finset (ℕ × ℕ)) : ℝ :=
  Real.exp (∑ p ∈ T, h p)

def partition (K : FiniteSubgraphCode) (h : Field) : ℝ :=
  ∑ T ∈ spanningTrees K, weight h T

def numerator (K : FiniteSubgraphCode) (e : ℕ × ℕ) (h : Field) : ℝ := by
  classical
  exact ∑ T ∈ (spanningTrees K).filter (fun T => e ∈ T), weight h T

def inclusion (K : FiniteSubgraphCode) (e : ℕ × ℕ) (h : Field) : ℝ :=
  numerator K e h / partition K h

def finiteField (S : Finset (ℕ × ℕ)) (t : ℝ) (y : Field) : Field :=
  fun p => if p ∈ S then y p - t / 2 else 0

def extendField (y : EdgeCode → ℝ) : Field :=
  fun p => if hp : p.1 < p.2 then y ⟨p, hp⟩ else 0

end Problem336.WeightedTree

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FiniteUSTProbability
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem336

def finiteUSTProbability (K : FiniteSubgraphCode)
    (hK : (spanningTrees K).Nonempty) : ProbabilityMeasure EdgeConfiguration :=
  ⟨finiteUSTMeasure K, finiteUSTMeasure_isProbabilityMeasure K hK⟩

@[simp] lemma finiteUSTProbability_toMeasure (K : FiniteSubgraphCode)
    (hK : (spanningTrees K).Nonempty) :
    (finiteUSTProbability K hK : Measure EdgeConfiguration) = finiteUSTMeasure K := rfl

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_USTFiniteTilt
attribute [-instance] _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem336.USTResponse

def observationField (K : FiniteSubgraphCode) (S : Finset (ℕ × ℕ))
    (t : ℝ) (y : (ℕ × ℕ) → ℝ) : FiniteEdge K → ℝ :=
  fun e => if e.1 ∈ S then y e.1 - t / 2 else 0

def finiteTilt (K : FiniteSubgraphCode) (S : Finset (ℕ × ℕ))
    (t : ℝ) (y : (ℕ × ℕ) → ℝ) (e : ℕ × ℕ) : ℝ :=
  if he : e ∈ K.2 then inclusion K (observationField K S t y) ⟨e, he⟩ else 0

end Problem336.USTResponse

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_USTPosteriorResponse
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Problem336.USTResponse

def extendMarks (h : EdgeCode → ℝ) (p : ℕ × ℕ) : ℝ :=
  if hp : p.1 < p.2 then h ⟨p, hp⟩ else 0

@[simp] lemma extendMarks_coe (h : EdgeCode → ℝ) (e : EdgeCode) :
    extendMarks h e.1 = h e := by simp [extendMarks, e.2]

end Problem336.USTResponse

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_GraphCoordinateTruncation
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace Problem336.CoordinateTruncation

def finiteEdges (K : FiniteSubgraphCode) : Finset EdgeCode :=
  K.2.subtype (fun p => p.1 < p.2)

@[simp] theorem mem_finiteEdges (K : FiniteSubgraphCode) (e : EdgeCode) :
    e ∈ finiteEdges K ↔ e.1 ∈ K.2 := by
  simp [finiteEdges]

def graphEdges (G : GraphCode) : Set EdgeCode :=
  {e | Adj G e.1.1 e.1.2}

end Problem336.CoordinateTruncation

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_GraphFreeKernel
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.finiteCodeEdgesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology ENNReal

namespace Problem336.FreeKernel

open CoordinateTruncation

instance complete_closedGraphCycleSpace (G : GraphCode) :
    CompleteSpace (closedGraphCycleSpace G) := by
  unfold closedGraphCycleSpace
  infer_instance

instance projection_closedGraphCycleSpace (G : GraphCode) :
    (closedGraphCycleSpace G).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

def finiteKernel (K : FiniteSubgraphCode) : EdgeHilbert →L[ℝ] EdgeHilbert :=
  truncate (finiteEdges K) - (finiteHilbertCycleSpace K).starProjection

def graphKernel (G : GraphCode) : EdgeHilbert →L[ℝ] EdgeHilbert :=
  (supported (graphEdges G)).starProjection - (closedGraphCycleSpace G).starProjection

def edgeVector (e : EdgeCode) : EdgeHilbert := lp.single 2 e (1 : ℝ)

def kernelEntry (G : GraphCode) (e f : EdgeCode) : ℝ :=
  inner ℝ (edgeVector e) (graphKernel G (edgeVector f))

def finiteInclusionMinor (K : FiniteSubgraphCode) (A : Finset EdgeCode) : ℝ≥0∞ :=
  ENNReal.ofReal (Matrix.det (fun e f : A =>
    inner ℝ (edgeVector e.1) (finiteKernel K (edgeVector f.1))))

def inclusionMinorLimit (G : GraphCode) (A : Finset EdgeCode) : ℝ≥0∞ :=
  ENNReal.ofReal (Matrix.det (fun e f : A => kernelEntry G e.1 f.1))

end Problem336.FreeKernel

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FiniteKernelEmbedding
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem336.FreeKernel

open CoordinateTruncation

@[simp] theorem finiteHilbertEmbedding_single (K : FiniteSubgraphCode)
    (e : finiteCodeEdges K) :
    finiteHilbertEmbedding K (EuclideanSpace.single e (1 : ℝ)) = edgeVector e.1 := by
  change finiteHilbertEmbeddingLinear K (EuclideanSpace.single e (1 : ℝ)) = edgeVector e.1
  rw [finiteHilbertEmbeddingLinear_sum]
  simp [EuclideanSpace.single, PiLp.single_apply, edgeVector]

end Problem336.FreeKernel

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_USTInclusionCount
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem336.USTInclusionCount

def edgePairs (A : Finset EdgeCode) : Finset (ℕ × ℕ) :=
  A.map (Function.Embedding.subtype (fun p : ℕ × ℕ => p.1 < p.2))

@[simp] theorem edgePairs_card (A : Finset EdgeCode) : (edgePairs A).card = A.card :=
  Finset.card_map _

@[simp] theorem edgePairs_subset_iff (A : Finset EdgeCode) (T : Finset (ℕ × ℕ)) :
    edgePairs A ⊆ T ↔ ∀ e ∈ A, e.val ∈ T := by
  simp [edgePairs, Finset.subset_iff]

def supportedPairs (K : FiniteSubgraphCode) (A : Finset EdgeCode) : Finset K.2 :=
  (edgePairs A).subtype (fun p => p ∈ K.2)

def requiredEdgeEquiv (K : FiniteSubgraphCode) (A : Finset EdgeCode)
    (hA : ∀ e ∈ A, e.val ∈ K.2) : A ≃ supportedPairs K A :=
  Equiv.ofBijective
    (fun e => ⟨⟨e.val.val, hA e.val e.property⟩,
      Finset.mem_subtype.mpr (Finset.mem_map.mpr ⟨e.val, e.property, rfl⟩)⟩)
    ⟨by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun p : supportedPairs K A => p.val.val) hab,
     by
      intro p
      obtain ⟨e, he, hep⟩ := Finset.mem_map.mp (Finset.mem_subtype.mp p.property)
      refine ⟨⟨e, he⟩, ?_⟩
      apply Subtype.ext
      exact Subtype.ext hep⟩

@[simp] theorem requiredEdgeEquiv_val (K : FiniteSubgraphCode) (A : Finset EdgeCode)
    (hA : ∀ e ∈ A, e.val ∈ K.2) (e : A) :
    (requiredEdgeEquiv K A hA e).val.val = e.val.val := rfl

end Problem336.USTInclusionCount

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FiniteUSTRelabel
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal

namespace Problem336

def relabelPair (σ : Equiv ℕ ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  rawPair (σ p.1) (σ p.2)

def relabelEdgeSet (σ : Equiv ℕ ℕ) (T : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  T.image (relabelPair σ)

def relabelFiniteSubgraph (σ : Equiv ℕ ℕ) (K : FiniteSubgraphCode) :
    FiniteSubgraphCode :=
  (K.1.image σ, relabelEdgeSet σ K.2)

@[simp] theorem relabelPair_rawPair (σ : Equiv ℕ ℕ) (u v : ℕ) :
    relabelPair σ (rawPair u v) = rawPair (σ u) (σ v) := by
  unfold relabelPair
  by_cases h : u < v
  · rw [rawPair_of_lt h]
  · have hraw : rawPair u v = (v, u) := by simp [rawPair, h]
    rw [hraw]
    exact rawPair_comm _ _

@[simp] theorem relabelPair_edge (σ : Equiv ℕ ℕ) (e : EdgeCode) :
    relabelPair σ e.val = (mapEdge σ e).val := by
  simp [relabelPair, mapEdge]

@[simp] theorem relabelPair_symm (σ : Equiv ℕ ℕ) {p : ℕ × ℕ}
    (hp : p.1 < p.2) :
    relabelPair σ.symm (relabelPair σ p) = p := by
  have h := congrArg Subtype.val (mapEdge_symm_apply σ ⟨p, hp⟩)
  simpa only [← relabelPair_edge] using h

theorem relabelPair_injOn (σ : Equiv ℕ ℕ) :
    Set.InjOn (relabelPair σ) {p : ℕ × ℕ | p.1 < p.2} := by
  intro p hp q hq h
  have h' := congrArg (relabelPair σ.symm) h
  simpa only [relabelPair_symm σ hp, relabelPair_symm σ hq] using h'

theorem relabelEdgeSet_card (σ : Equiv ℕ ℕ) (T : Finset (ℕ × ℕ))
    (hT : ∀ p ∈ T, p.1 < p.2) :
    (relabelEdgeSet σ T).card = T.card := by
  apply Finset.card_image_iff.mpr
  intro p hp q hq h
  exact relabelPair_injOn σ (hT p hp) (hT q hq) h

@[simp] theorem relabelEdgeSet_symm (σ : Equiv ℕ ℕ) (T : Finset (ℕ × ℕ))
    (hT : ∀ p ∈ T, p.1 < p.2) :
    relabelEdgeSet σ.symm (relabelEdgeSet σ T) = T := by
  unfold relabelEdgeSet
  rw [Finset.image_image]
  calc
    T.image (fun p => relabelPair σ.symm (relabelPair σ p)) = T.image id := by
      apply Finset.image_congr
      intro p hp
      exact relabelPair_symm σ (hT p hp)
    _ = T := Finset.image_id

theorem relabelEdgeSet_valid (σ : Equiv ℕ ℕ) (T : Finset (ℕ × ℕ))
    (hT : ∀ p ∈ T, p.1 < p.2) :
    ∀ p ∈ relabelEdgeSet σ T, p.1 < p.2 := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  have h := (mapEdge σ ⟨q, hT q hq⟩).property
  simpa only [← relabelPair_edge] using h

theorem treeAdj_relabelEdgeSet (σ : Equiv ℕ ℕ) (T : Finset (ℕ × ℕ))
    (hT : ∀ p ∈ T, p.1 < p.2) (u v : ℕ) :
    TreeAdj (relabelEdgeSet σ T) (σ u) (σ v) ↔ TreeAdj T u v := by
  constructor
  · intro h
    obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp h
    have hback := congrArg (relabelPair σ.symm) heq
    have hpraw : p = rawPair u v := by
      simpa only [relabelPair_symm σ (hT p hp), relabelPair_rawPair,
        Equiv.symm_apply_apply] using hback
    simpa only [TreeAdj, ← hpraw] using hp
  · intro h
    apply Finset.mem_image.mpr
    exact ⟨rawPair u v, h, relabelPair_rawPair σ u v⟩

theorem treeOn_relabel (σ : Equiv ℕ ℕ) {K : FiniteSubgraphCode}
    (hK : ∀ p ∈ K.2, p.1 < p.2) {T : Finset (ℕ × ℕ)}
    (hT : TreeOn K T) :
    TreeOn (relabelFiniteSubgraph σ K) (relabelEdgeSet σ T) := by
  have hTv : ∀ p ∈ T, p.1 < p.2 := fun p hp => hK p (hT.1 hp)
  refine ⟨Finset.image_subset_image hT.1, ?_, ?_⟩
  · change (relabelEdgeSet σ T).card + 1 = (K.1.image σ).card
    rw [relabelEdgeSet_card σ T hTv, Finset.card_image_of_injective _ σ.injective]
    exact hT.2.1
  · intro u hu v hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
    have hpath := hT.2.2 a ha b hb
    clear ha hb hu hv
    induction hpath with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c hab hbc ih =>
      exact ih.tail ((treeAdj_relabelEdgeSet σ T hTv b c).mpr hbc)

@[simp] theorem relabelFiniteSubgraph_symm (σ : Equiv ℕ ℕ)
    (K : FiniteSubgraphCode) (hK : ∀ p ∈ K.2, p.1 < p.2) :
    relabelFiniteSubgraph σ.symm (relabelFiniteSubgraph σ K) = K := by
  apply Prod.ext
  · simp [relabelFiniteSubgraph, Finset.image_image]
  · exact relabelEdgeSet_symm σ K.2 hK

theorem treeOn_of_mem_spanningTrees {K : FiniteSubgraphCode}
    {T : Finset (ℕ × ℕ)} (h : T ∈ spanningTrees K) : TreeOn K T := by
  classical
  exact (Finset.mem_filter.mp h).2

theorem mem_spanningTrees_of_treeOn {K : FiniteSubgraphCode}
    {T : Finset (ℕ × ℕ)} (h : TreeOn K T) : T ∈ spanningTrees K := by
  simp only [spanningTrees, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨h.1, h⟩

theorem spanningTrees_relabel (σ : Equiv ℕ ℕ) (K : FiniteSubgraphCode)
    (hK : ∀ p ∈ K.2, p.1 < p.2) :
    spanningTrees (relabelFiniteSubgraph σ K) =
      (spanningTrees K).image (relabelEdgeSet σ) := by
  ext T
  constructor
  · intro h
    have hT := treeOn_of_mem_spanningTrees h
    have hKv := relabelEdgeSet_valid σ K.2 hK
    have hTv : ∀ p ∈ T, p.1 < p.2 := fun p hp => hKv p (hT.1 hp)
    refine Finset.mem_image.mpr ⟨relabelEdgeSet σ.symm T, ?_, ?_⟩
    · apply mem_spanningTrees_of_treeOn
      have hback := treeOn_relabel σ.symm hKv hT
      simpa only [relabelFiniteSubgraph_symm σ K hK] using hback
    · simpa only [Equiv.symm_symm] using relabelEdgeSet_symm σ.symm T hTv
  · intro h
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp h
    exact mem_spanningTrees_of_treeOn (treeOn_relabel σ hK (treeOn_of_mem_spanningTrees hS))

end Problem336

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_WeightedTreeEquiv
attribute [-instance] _root_.OAI.Problem336.AllPairWiener.law_isProbabilityMeasure _root_.OAI.Problem336.FreeKernel.complete_closedGraphCycleSpace _root_.OAI.Problem336.FreeKernel.projection_closedGraphCycleSpace _root_.OAI.Problem336.finiteCodeEdgesFintype _root_.OAI.Problem336.finiteDimensional_finiteCycleSpace _root_.OAI.Problem336.finiteDimensional_finiteHilbertCycleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem336.WeightedTree

theorem tree_canonical {K : FiniteSubgraphCode}
    (hK : ∀ p ∈ K.2, p.1 < p.2) (T : USTResponse.TreeSample K) :
    ∀ p ∈ T.1, p.1 < p.2 :=
  fun p hp => hK p ((USTResponse.tree_property K T).1 hp)

def treeRelabelEquiv (σ : Equiv ℕ ℕ) (K : FiniteSubgraphCode)
    (hK : ∀ p ∈ K.2, p.1 < p.2) :
    USTResponse.TreeSample K ≃ USTResponse.TreeSample (relabelFiniteSubgraph σ K) where
  toFun T := ⟨relabelEdgeSet σ T.1, by
    rw [spanningTrees_relabel σ K hK]
    exact Finset.mem_image.mpr ⟨T.1, T.2, rfl⟩⟩
  invFun T := ⟨relabelEdgeSet σ.symm T.1, by
    have hm : T.1 ∈ (spanningTrees K).image (relabelEdgeSet σ) := by
      simpa only [spanningTrees_relabel σ K hK] using T.2
    obtain ⟨S, hS, heq⟩ := Finset.mem_image.mp hm
    rw [← heq, relabelEdgeSet_symm σ S (tree_canonical hK ⟨S, hS⟩)]
    exact hS⟩
  left_inv T := Subtype.ext (relabelEdgeSet_symm σ T.1 (tree_canonical hK T))
  right_inv T := by
    apply Subtype.ext
    exact relabelEdgeSet_symm σ.symm T.1
      (tree_canonical (relabelEdgeSet_valid σ K.2 hK) T)

@[simp] theorem treeRelabelEquiv_val (σ : Equiv ℕ ℕ) (K : FiniteSubgraphCode)
    (hK : ∀ p ∈ K.2, p.1 < p.2) (T : USTResponse.TreeSample K) :
    (treeRelabelEquiv σ K hK T).1 = relabelEdgeSet σ T.1 := rfl

def relabelField (σ : Equiv ℕ ℕ) (h : Field) : Field :=
  fun p => h (relabelPair σ.symm p)

@[simp] theorem relabelField_mapEdge (σ : Equiv ℕ ℕ) (h : Field) (e : EdgeCode) :
    relabelField σ h (mapEdge σ e).1 = h e.1 := by
  unfold relabelField
  rw [← relabelPair_edge, relabelPair_symm σ e.2]

end Problem336.WeightedTree

end

end OAI
end

section
-- module Solutions.OAIS_P336.SpanningForest_FinalFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem336.FinalFactor

def rule : FactorRule :=
  FactorAssembly.rule GraphTreePosterior.drift AllPairWiener.noise

end Problem336.FinalFactor

end

end OAI
end


