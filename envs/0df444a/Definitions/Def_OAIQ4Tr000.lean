-- Prove2me | Definitions.Def_OAIQ4Tr000
-- name    : OAIQ4Tr000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T06:52:06.86027+00:00
-- url     : https://prove2.me/theorems/43126bb9-2506-4ef1-b549-d7fbedc876f7
-- title:
--   Definitions bundle OAIQ4Tr000 of the split of OpenAI, The sharp terminal leave in random triangle removal
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SharpTerminalLeave.sharp_terminal_leave`, carved from OpenAI's openai/math development (OpenAI, *The sharp terminal leave in random triangle removal*, OpenAI Math Release, September 25, 2026, result family 188, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 620 declarations of OpenAI's Lean: 360 definitions, 9 inductive types or structures, 15 instances and 236 theorems. The definitions and types are `OAI.SharpTerminalLeave.BirthGraph`, `OAI.SharpTerminalLeave.BirthGraph.Covered`, `OAI.SharpTerminalLeave.BirthGraph.ExposedAt`, `OAI.SharpTerminalLeave.BirthGraph.ExtraEdge`, `OAI.SharpTerminalLeave.BirthGraph.IsTriangle`, `OAI.SharpTerminalLeave.BirthGraph.SpawnRules`, `OAI.SharpTerminalLeave.BirthGraph.Within`, `OAI.SharpTerminalLeave.BirthGraph.backEdges`, `OAI.SharpTerminalLeave.BirthGraph.bornEdges`, `OAI.SharpTerminalLeave.BirthGraph.graph`, `OAI.SharpTerminalLeave.BirthGraph.inducedEdges`, `OAI.SharpTerminalLeave.BirthGraph.initialAssignmentSet`, `OAI.SharpTerminalLeave.BirthGraph.parentType`, `OAI.SharpTerminalLeave.BirthGraph.parentVertices`, `OAI.SharpTerminalLeave.BirthGraph.restrict`, `OAI.SharpTerminalLeave.BirthGraph.rootClosers`, `OAI.SharpTerminalLeave.BirthGraph.suffixBoundary`, `OAI.SharpTerminalLeave.BirthGraph.suffixEdges`, `OAI.SharpTerminalLeave.BirthGraph.suffixTemplate`, `OAI.SharpTerminalLeave.BirthGraph.suffixVertices`, `OAI.SharpTerminalLeave.BoundedEmbeddedWitness`, `OAI.SharpTerminalLeave.CavitySpace`, `OAI.SharpTerminalLeave.ChargesCovered`, `OAI.SharpTerminalLeave.CompleteEdge`, `OAI.SharpTerminalLeave.DivergentArms`, `OAI.SharpTerminalLeave.EdgeMatching`, `OAI.SharpTerminalLeave.Enumerates`, `OAI.SharpTerminalLeave.ExposureTree`, `OAI.SharpTerminalLeave.ExposureTree.bind`, `OAI.SharpTerminalLeave.ExposureTree.checkMarked`, `OAI.SharpTerminalLeave.ExposureTree.checkMarkedTrace`, `OAI.SharpTerminalLeave.ExposureTree.checkNone`, `OAI.SharpTerminalLeave.ExposureTree.checkNoneTrace`, `OAI.SharpTerminalLeave.ExposureTree.coupled`, `OAI.SharpTerminalLeave.ExposureTree.evaluate`, `OAI.SharpTerminalLeave.ExposureTree.exposeLabeled`, `OAI.SharpTerminalLeave.ExposureTree.exposeValues`, `OAI.SharpTerminalLeave.ExposureTree.fresh`, `OAI.SharpTerminalLeave.ExposureTree.freshLog`, `OAI.SharpTerminalLeave.ExposureTree.freshRecorded` and 329 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/TriangleRemoval, in whole or in part: `TriangleRemoval_Asymptotics_ActiveL2Map`, `TriangleRemoval_Asymptotics_DensityEdgeSafe`, `TriangleRemoval_Asymptotics_EarlyDensity`, `TriangleRemoval_Asymptotics_FreshLog`, `TriangleRemoval_Asymptotics_FreshLogExposeLabeled`, `TriangleRemoval_Coupling_ClockOrder`, `TriangleRemoval_Coupling_GridUniformError`, `TriangleRemoval_Coupling_HyperScanAction`, `TriangleRemoval_Coupling_OrderEmbRank`, `TriangleRemoval_Coupling_OrderLaw`, `TriangleRemoval_Coupling_OrderedSuffix`, `TriangleRemoval_Coupling_ScanList`, `TriangleRemoval_Coupling_UnitTime`, `TriangleRemoval_Embeddings_BirthGraph`, `TriangleRemoval_Embeddings_DegreeTemplate`, `TriangleRemoval_Embeddings_EmbeddedWitnessRoots`, `TriangleRemoval_Embeddings_EmptyRootInjection`, `TriangleRemoval_Embeddings_GraphEmbeddings`, `TriangleRemoval_Embeddings_PathBirthIndex`, `TriangleRemoval_Embeddings_ReindexEmbedding`, `TriangleRemoval_Embeddings_RerootTemplate`, `TriangleRemoval_Embeddings_RestrictLabel`, `TriangleRemoval_Embeddings_RootedTemplates`, `TriangleRemoval_Embeddings_SuffixTemplate`, `TriangleRemoval_Embeddings_TriangleGrowth`, `TriangleRemoval_Embeddings_TriangleGrowth2`, `TriangleRemoval_Embeddings_WitnessEmbeddingBound`, `TriangleRemoval_Probability_FiniteMean`, `TriangleRemoval_Probability_HistoryLawPathSupport`, `TriangleRemoval_Probability_MarkovLaw`, `TriangleRemoval_Probability_PairVisitProbability`, `TriangleRemoval_Probability_PathVisitProbability`, `TriangleRemoval_Probability_ProductPMF`, `TriangleRemoval_Process_ActiveHypergraph`, `TriangleRemoval_Process_Attachment`, `TriangleRemoval_Process_BornEdges`, `TriangleRemoval_Process_ChargesCovered`, `TriangleRemoval_Process_CommonNeighbors`, `TriangleRemoval_Process_CompleteEdge`, `TriangleRemoval_Process_CompleteEdgePair`, `TriangleRemoval_Process_CopyEdgeLoad`, `TriangleRemoval_Process_CopyLoadSafe`, `TriangleRemoval_Process_DivergentArms`, `TriangleRemoval_Process_EdgeFamilyDegree`, `TriangleRemoval_Process_EdgeIncidence`, `TriangleRemoval_Process_EdgeMatching`, `TriangleRemoval_Process_EigenProjector`, `TriangleRemoval_Process_Finish`, `TriangleRemoval_Process_History`, `TriangleRemoval_Process_HistoryAdditive`, `TriangleRemoval_Process_HistoryAlive`, `TriangleRemoval_Process_HistoryCompensator`, `TriangleRemoval_Process_IncidenceDegree`, `TriangleRemoval_Process_IndexedPatternEdges`, `TriangleRemoval_Process_IndexedWitnessCode`, `TriangleRemoval_Process_InitialAssignmentSet`, `TriangleRemoval_Process_LevelDeletes`, `TriangleRemoval_Process_LinkSimpleGraph`, `TriangleRemoval_Process_LocalChoiceRank`, `TriangleRemoval_Process_LookupGraph`, `TriangleRemoval_Process_MapOutput`, `TriangleRemoval_Process_NonrootForest`, `TriangleRemoval_Process_OlderSeed`, `TriangleRemoval_Process_OverlapVertices`, `TriangleRemoval_Process_PairRequired`, `TriangleRemoval_Process_Parent`, `TriangleRemoval_Process_PathForest`, `TriangleRemoval_Process_PathPattern`, `TriangleRemoval_Process_PathRequired`, `TriangleRemoval_Process_PathSuffix`, `TriangleRemoval_Process_ProgramDemand`, `TriangleRemoval_Process_ProspectiveFailure`, `TriangleRemoval_Process_ReindexSet`, `TriangleRemoval_Process_ReindexSetImage`, `TriangleRemoval_Process_RelativeNoiseExit`, `TriangleRemoval_Process_RelativeSafeCopyIncrement`, `TriangleRemoval_Process_RelativeScaleBudget`, `TriangleRemoval_Process_Restrict`, `TriangleRemoval_Process_RestrictedParent`, `TriangleRemoval_Process_RootClosers`, `TriangleRemoval_Process_RootSet`, `TriangleRemoval_Process_SuffixBoundary`, `TriangleRemoval_Process_SuffixProjection`, `TriangleRemoval_Process_TerminalLaw`, `TriangleRemoval_Process_TriangleDegreeMean`, `TriangleRemoval_Process_TriangleHypergraph`, `TriangleRemoval_Process_TriangleIndex`, `TriangleRemoval_Process_TriangleThird`, `TriangleRemoval_Process_ValidIndexedAttachments`, `TriangleRemoval_Process_Within`, `TriangleRemoval_Process_WitnessDimensionEquiv`, `TriangleRemoval_Process_WitnessDimensions`, `TriangleRemoval_Process_WitnessMu`, `TriangleRemoval_Queries_Address`, `TriangleRemoval_Queries_AddressHead`, `TriangleRemoval_Queries_CallPath`, `TriangleRemoval_Queries_CanonicalCollisionSum`, `TriangleRemoval_Queries_Child`, `TriangleRemoval_Queries_FinsetCandidateOrder`, `TriangleRemoval_Queries_ForkAddressesNotSuffix`, `TriangleRemoval_Queries_GridCollision`, `TriangleRemoval_Queries_JointMarkedQuery`, `TriangleRemoval_Queries_LegalCollisionPairs`, `TriangleRemoval_Queries_MarkedChild`, `TriangleRemoval_Queries_MarkedSuccess`, `TriangleRemoval_Queries_OrderedMarkedRow`, `TriangleRemoval_Queries_RecordedCallForest`, `TriangleRemoval_Queries_Separated`, `TriangleRemoval_Queries_SplitQueryPaths`, `TriangleRemoval_Queries_TreeBind`, `TriangleRemoval_Queries_VertexCall`, `TriangleRemoval_Spectral_CheckMarkedTrace`, `TriangleRemoval_Spectral_ClosedWalkFamily`, `TriangleRemoval_Spectral_ClosedWalkPattern`, `TriangleRemoval_Spectral_ClosedWords`, `TriangleRemoval_Spectral_EdgeStar`, `TriangleRemoval_Spectral_FreshLogCheckNone`, `TriangleRemoval_Spectral_FreshLogCheckNone2`, `TriangleRemoval_Spectral_FreshLogCheckNone3`, `TriangleRemoval_Spectral_LinkStarMatrix`, `TriangleRemoval_Spectral_MatrixEuclideanAlgHom`, `TriangleRemoval_Spectral_MatrixInfinityAlgHom`, `TriangleRemoval_Spectral_MovingStarDegree`, `TriangleRemoval_Spectral_NormalizedOnes`, `TriangleRemoval_Spectral_StarInclusion`, `TriangleRemoval_Spectral_TracedGridQueryAddress`, `TriangleRemoval_Spectral_WheelSpoke`, `TriangleRemoval_Stability_CavityGenerator`, `TriangleRemoval_Stability_CavityReference`, `TriangleRemoval_Stability_CavityWeight`, `TriangleRemoval_Stability_EdgeStabilityRate`, `TriangleRemoval_Stability_GridCavityError`, `TriangleRemoval_Stability_MovingResidualForcing`, `TriangleRemoval_Stability_Volterra`, `TriangleRemoval_Tracking_BalancedJump`, `TriangleRemoval_Tracking_CenteredCodegreeNeighborSum`, `TriangleRemoval_Tracking_CodegreeNoiseRadius`, `TriangleRemoval_Tracking_CodegreeVarianceRate`, `TriangleRemoval_Tracking_PrefixBalancedNoise`, `TriangleRemoval_Tracking_PrefixCodeSet`, `TriangleRemoval_Tracking_PrefixCodegreeDriftTerm`, `TriangleRemoval_Tracking_PrefixCodegreeNoiseExit`, `TriangleRemoval_Tracking_PrefixCodegreeNoiseGood`, `TriangleRemoval_Tracking_PrefixEdgeForcingBound`, `TriangleRemoval_Tracking_PrefixEdgeRadius`, `TriangleRemoval_Tracking_PrefixEmbeddings`, `TriangleRemoval_Tracking_PrefixEpsilon`, `TriangleRemoval_Tracking_PrefixHorizon`, `TriangleRemoval_Tracking_PrefixTriangleRadius`, `TriangleRemoval_Tracking_PrefixWeight`, `TriangleRemoval_Tracking_RootedCompletionMax`, `TriangleRemoval_Tracking_RootedCountedTracedRepeat`, `TriangleRemoval_Tracking_RootedInjectionEquivFree`, `TriangleRemoval_Tracking_RootedTemplateEncoding`, `TriangleRemoval_Tracking_TriangleDrift`.
--
--   **Imports.** It imports the published bundle `Def_TriangleRemoval`.
--
--   **Imported by** (directly, in this split): the statements `OAI.SharpTerminalLeave.averaged_disjoint_grid_collision`, `OAI.SharpTerminalLeave.averaged_singleton_grid_collision`, `OAI.SharpTerminalLeave.goodPrefix_cavity_semigroup`, `OAI.SharpTerminalLeave.main_l2_prefix_failure_bound`, `OAI.SharpTerminalLeave.prefix_all_pair_closure`, `OAI.SharpTerminalLeave.prefix_edge_residual_bounds`, `OAI.SharpTerminalLeave.prefix_good_history` and `OAI.SharpTerminalLeave.prefix_present_edge_closure`; the proofs of `OAI.SharpTerminalLeave.averaged_disjoint_grid_collision`, `OAI.SharpTerminalLeave.averaged_singleton_grid_collision`, `OAI.SharpTerminalLeave.goodPrefix_cavity_semigroup`, `OAI.SharpTerminalLeave.main_l2_prefix_failure_bound`, `OAI.SharpTerminalLeave.prefix_all_pair_closure`, `OAI.SharpTerminalLeave.prefix_edge_residual_bounds`, `OAI.SharpTerminalLeave.prefix_good_history`, `OAI.SharpTerminalLeave.prefix_present_edge_closure` and `OAI.SharpTerminalLeave.sharp_terminal_leave`.
-- source:
--   OpenAI, The sharp terminal leave in random triangle removal, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 188; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Sharp-Terminal-Leave-in-Random-Triangle-Removal-September-25-2026/The-Sharp-Terminal-Leave-in-Random-Triangle-Removal-September-25-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/TriangleRemoval at commit adc7f12

import Mathlib
import Definitions.Def_TriangleRemoval

section
-- module Solutions.OAIQ4_Tr.Compat
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
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_MovingStarDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators

namespace SharpTerminalLeave

open Classical

noncomputable def movingStarDegree {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : Finset E) (u : V) : ℝ := by
  classical
  exact ((active.filter (fun e => u ∈ ends e)).card : ℝ)

noncomputable def movingStarMean {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : Finset E) (x : E → ℝ) (u : V) : ℝ := by
  classical
  exact (∑ e ∈ active.filter (fun e => u ∈ ends e), x e) / movingStarDegree ends active u

noncomputable def movingStarLift {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (b : V → ℝ) (e : E) : ℝ := ∑ u ∈ ends e, b u

noncomputable def movingStarOtherMean {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : Finset E) (b : V → ℝ) (u : V) : ℝ := by
  classical
  exact (∑ e ∈ active.filter (fun e => u ∈ ends e), ∑ v ∈ (ends e).erase u, b v) /
    movingStarDegree ends active u

noncomputable def movingStarVertices {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : ℕ → Finset E) (a : ℕ → ℝ)
    (M : ℕ → E → ℝ) : ℕ → V → ℝ
  | 0 => fun _ => 0
  | k+1 => fun u => movingStarVertices ends active a M k u + a k *
      movingStarMean ends (active k)
        (fun e => M k e-movingStarLift ends (movingStarVertices ends active a M k) e) u

end SharpTerminalLeave
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_ActiveL2Map
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators

namespace SharpTerminalLeave
open Classical

noncomputable def activeL2Map {E : Type*} [Fintype E] (s : Finset E) :
    (E → ℝ) →ₗ[ℝ] EuclideanSpace ℝ E where
  toFun x := WithLp.toLp 2 (fun e => if e ∈ s then x e else 0)
  map_add' x y := by ext e; by_cases he : e ∈ s <;> simp [he]
  map_smul' c x := by ext e; by_cases he : e ∈ s <;> simp [he]

noncomputable def activeL2 {E : Type*} [Fintype E] (s : Finset E) : Seminorm ℝ (E → ℝ) :=
  (normSeminorm ℝ (EuclideanSpace ℝ E)).comp (activeL2Map s)

lemma movingStarMean_add {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (s : Finset E) (x y : E → ℝ) (u : V) :
    movingStarMean ends s (x+y) u = movingStarMean ends s x u+movingStarMean ends s y u := by
  simp [movingStarMean,Pi.add_apply,Finset.sum_add_distrib,add_div]

lemma movingStarLift_add {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (b c : V → ℝ) :
    movingStarLift ends (b+c) = movingStarLift ends b+movingStarLift ends c := by
  funext e
  simp [movingStarLift,Pi.add_apply,Finset.sum_add_distrib]

noncomputable def activeLinf {E : Type*} [Fintype E] (s : Finset E) : Seminorm ℝ (E → ℝ) :=
  s.sup (fun e => (normSeminorm ℝ ℝ).comp (LinearMap.proj e))

noncomputable def trajectorySeminorm {E : Type*} [Fintype E]
    (P : ℕ → Seminorm ℝ (E → ℝ)) (T : ℕ) : Seminorm ℝ (ℕ → E → ℝ) :=
  (Finset.range (T+1)).sup (fun t => (P t).comp (LinearMap.proj t))

noncomputable def movingStarSolve {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : ℕ → Finset E) (a : ℕ → ℝ)
    (M : ℕ → E → ℝ) : ℕ → E → ℝ
  | 0 => M 0
  | t+1 => fun e => movingStarSolve ends active a M t e-
      a t*movingStarLift ends (movingStarMean ends (active t) (movingStarSolve ends active a M t)) e+
        (M (t+1) e-M t e)

lemma movingStarMean_smul {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (s : Finset E) (c : ℝ) (x : E → ℝ) :
    movingStarMean ends s (c • x) = c • movingStarMean ends s x := by
  funext u
  simp only [movingStarMean,Pi.smul_apply,smul_eq_mul,← Finset.mul_sum]
  ring

lemma movingStarLift_smul {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (c : ℝ) (b : V → ℝ) :
    movingStarLift ends (c • b) = c • movingStarLift ends b := by
  funext e
  simp [movingStarLift,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]

lemma movingStarSolve_add {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : ℕ → Finset E) (a : ℕ → ℝ)
    (M N : ℕ → E → ℝ) :
    movingStarSolve ends active a (M+N) = movingStarSolve ends active a M+movingStarSolve ends active a N := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih =>
    have hm : movingStarMean ends (active t)
        (movingStarSolve ends active a M t+movingStarSolve ends active a N t) =
        movingStarMean ends (active t) (movingStarSolve ends active a M t)+
        movingStarMean ends (active t) (movingStarSolve ends active a N t) := by
      funext u
      exact movingStarMean_add _ _ _ _ _
    simp only [movingStarSolve,ih,Pi.add_apply] at hm ⊢
    rw [hm,movingStarLift_add]
    funext e
    simp only [Pi.add_apply]
    ring

lemma movingStarSolve_smul {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : ℕ → Finset E) (a : ℕ → ℝ)
    (c : ℝ) (M : ℕ → E → ℝ) :
    movingStarSolve ends active a (c • M) = c • movingStarSolve ends active a M := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih =>
    change (fun e => movingStarSolve ends active a (c • M) t e-
      a t*movingStarLift ends (movingStarMean ends (active t) (movingStarSolve ends active a (c • M) t)) e+
        ((c • M) (t+1) e-(c • M) t e)) = c • movingStarSolve ends active a M (t+1)
    rw [show movingStarSolve ends active a (c • M) t = c • movingStarSolve ends active a M t from ih,
      movingStarMean_smul,movingStarLift_smul]
    simp only [movingStarSolve]
    funext e
    simp only [Pi.smul_apply,smul_eq_mul]
    ring

noncomputable def movingStarResponse {E V : Type*} [Fintype E] [Fintype V]
    (ends : E → Finset V) (active : ℕ → Finset E) (a : ℕ → ℝ) :
    Module.End ℝ (ℕ → E → ℝ) where
  toFun := movingStarSolve ends active a
  map_add' := movingStarSolve_add ends active a
  map_smul' := movingStarSolve_smul ends active a

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_FiniteMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

noncomputable def pmfMean {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) : ℝ :=
  ∑ a, (p a).toReal * f a

@[simp] theorem pmfMean_pure {α : Type*} [Fintype α] (a : α) (f : α → ℝ) :
    pmfMean (PMF.pure a) f = f a := by
  classical
  simp [pmfMean, PMF.pure_apply, apply_ite]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_MarkovLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

noncomputable def markovLaw {α : Type*} (initial : PMF α) (K : ℕ → α → PMF α) : ℕ → PMF α
  | 0 => initial
  | k + 1 => (markovLaw initial K k).bind (K k)

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_History
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

abbrev History (α : Type*) (T : ℕ) := Fin (T + 1) → α

def historyIndex (T k : ℕ) : Fin (T + 1) := ⟨min k T,by omega⟩

@[simp] theorem historyIndex_val (T k : ℕ) : (historyIndex T k).val = min k T := rfl

noncomputable def historyInitial {α : Type*} (initial : PMF α) (T : ℕ) : PMF (History α T) :=
  initial.map (fun a => fun _ => a)

noncomputable def historyKernel {α : Type*} (K : ℕ → α → PMF α) (T k : ℕ)
    (ω : History α T) : PMF (History α T) :=
  if k < T then (K k (ω (historyIndex T k))).map
    (fun b => Function.update ω (historyIndex T (k + 1)) b) else PMF.pure ω

noncomputable def historyLaw {α : Type*} (initial : PMF α) (K : ℕ → α → PMF α)
    (T k : ℕ) : PMF (History α T) :=
  markovLaw (historyInitial initial T) (historyKernel K T) k

theorem historyIndex_ne_succ {T j k : ℕ} (hjk : j ≤ k) (hk : k < T) :
    historyIndex T j ≠ historyIndex T (k + 1) := by
  intro h
  have he := congrArg Fin.val h
  simp only [historyIndex_val] at he
  omega

noncomputable def historyIncrement {α : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (f : ℕ → α → ℝ) (T j : ℕ) (ω : History α T) : ℝ :=
  f (j + 1) (ω (historyIndex T (j + 1))) -
    pmfMean (K j (ω (historyIndex T j))) (f (j + 1))

noncomputable def historyNoise {α : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (f : ℕ → α → ℝ) (T k : ℕ) (ω : History α T) : ℝ :=
  ∑ j ∈ Finset.range (min k T), historyIncrement K f T j ω

noncomputable def historyCounter {α : Type*} (v : ℕ → α → ℝ)
    (T k : ℕ) (ω : History α T) : ℝ :=
  ∑ j ∈ Finset.range (min k T), v j (ω (historyIndex T j))

noncomputable def historyCounterRate {α : Type*} (v : ℕ → α → ℝ)
    (T k : ℕ) (ω : History α T) : ℝ :=
  if k < T then v k (ω (historyIndex T k)) else 0

@[simp] theorem historyNoise_zero {α : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (f : ℕ → α → ℝ) (T : ℕ) (ω : History α T) :
    historyNoise K f T 0 ω = 0 := by simp [historyNoise]

@[simp] theorem historyCounter_zero {α : Type*} (v : ℕ → α → ℝ)
    (T : ℕ) (ω : History α T) : historyCounter v T 0 ω = 0 := by simp [historyCounter]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_TerminalLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

@[simp] theorem card_completeGraph (n : ℕ) : (completeGraph n).card = n.choose 2 := by
  simp [completeGraph, Finset.card_powersetCard]

@[simp] theorem mem_completeGraph {n : ℕ} {e : Finset (Fin n)} :
    e ∈ completeGraph n ↔ e.card = 2 := by
  simp [completeGraph, Finset.mem_powersetCard]

@[simp] theorem mem_triangles {n : ℕ} {G : Graph n} {t : Finset (Fin n)} :
    t ∈ triangles G ↔ t.card = 3 ∧ t.powersetCard 2 ⊆ G := by
  simp [triangles, Finset.mem_powersetCard]

theorem step_support_active {n : ℕ} {G H : Graph n}
    (h : (triangles G).Nonempty) :
    H ∈ (step G).support ↔ ∃ t ∈ triangles G, G \ t.powersetCard 2 = H := by
  simp only [step, dite_eq_left h, PMF.mem_support_map_iff,
    PMF.mem_support_uniformOfFinset_iff]

theorem step_support_subset {n : ℕ} {G H : Graph n} (h : H ∈ (step G).support) :
    H ⊆ G := by
  by_cases hG : (triangles G).Nonempty
  · obtain ⟨t, _, rfl⟩ := (step_support_active hG).mp h
    exact Finset.sdiff_subset
  · simp only [step, dite_eq_right hG, PMF.mem_support_pure_iff] at h
    exact h ▸ Finset.Subset.refl G

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_TriangleDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

def hittingTriangles {n : ℕ} (G F : Graph n) : Finset (Finset (Fin n)) :=
  (triangles G).filter (fun t => ¬ Disjoint F (t.powersetCard 2))

def incidentTriangles {n : ℕ} (G : Graph n) (e : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (triangles G).filter (fun t => e ∈ t.powersetCard 2)

def triangleDegree {n : ℕ} (G : Graph n) (e : Finset (Fin n)) : ℕ :=
  (incidentTriangles G e).card

noncomputable def intact {n : ℕ} (F H : Graph n) : ℝ :=
  if F ⊆ H then 1 else 0

noncomputable def copyCount {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) : ℝ :=
  ∑ a, intact (required a) G

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_HistoryAlive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

def historyAlive {α : Type*} (safe : ℕ → α → Prop) (T j : ℕ)
    (ω : History α T) : Prop := ∀ i < j, safe i (ω (historyIndex T i))

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_TriangleDegreeMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

noncomputable def triangleDegreeMean {n : ℕ} (G : Graph n) : ℝ :=
  3 * (triangles G).card / G.card

noncomputable def triangleDegreeVariance {n : ℕ} (G : Graph n) : ℝ :=
  ∑ e ∈ G, ((triangleDegree G e : ℝ) - triangleDegreeMean G)^2

end SharpTerminalLeave
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_DensityEdgeSafe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators

namespace SharpTerminalLeave
open Classical

def densityEdgeSafe (n : ℕ) (p η : ℝ) (G : Graph n) : Prop :=
  G ⊆ completeGraph n ∧ (G.card : ℝ) = (n : ℝ)^2*p/2 ∧
    ∀ e ∈ G, |(triangleDegree G e : ℝ)-n*p^2| ≤ η*(n*p^2)

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_RootedTemplates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

structure RootedTemplate (k : ℕ) where
  edges : Graph k
  roots : Finset (Fin k)
  simple : ∀ e ∈ edges, e.card = 2
  independent : ∀ e ∈ edges, ¬ e ⊆ roots

abbrev RootedInjection {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) :=
  {φ : Fin k ↪ Fin n // ∀ v : {v // v ∈ T.roots}, φ v = ψ v}

def imageEdges {k n : ℕ} (T : RootedTemplate k) (φ : Fin k ↪ Fin n) : Graph n :=
  T.edges.image (fun e => e.map φ)

@[simp] theorem imageEdges_card {k n : ℕ} (T : RootedTemplate k) (φ : Fin k ↪ Fin n) :
    (imageEdges T φ).card = T.edges.card := by
  apply Finset.card_image_of_injective
  intro e f h
  exact Finset.map_injective φ h

noncomputable def rootedCount {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) (G : Graph n) : ℝ :=
  copyCount (fun φ : RootedInjection T ψ => imageEdges T φ.val) G

noncomputable def rootedScaling {k : ℕ} (T : RootedTemplate k) (n : ℕ) (p : ℝ) : ℝ :=
  (n : ℝ) ^ (k - T.roots.card) * p ^ T.edges.card

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_CommonNeighbors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

def commonNeighbors {n : ℕ} (G : Graph n) (u v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun w => {u,w} ∈ G ∧ {v,w} ∈ G)

def currentCodegree {n : ℕ} (G : Graph n) (u v : Fin n) : ℕ :=
  (commonNeighbors G u v).card

def wedgeEdges {n : ℕ} (u v w : Fin n) : Graph n := {{u,w},{v,w}}

@[simp] theorem mem_commonNeighbors {n : ℕ} (G : Graph n) (u v w : Fin n) :
    w ∈ commonNeighbors G u v ↔ {u,w} ∈ G ∧ {v,w} ∈ G := by
  simp [commonNeighbors]

@[simp] theorem wedgeEdges_subset {n : ℕ} (G : Graph n) (u v w : Fin n) :
    wedgeEdges u v w ⊆ G ↔ w ∈ commonNeighbors G u v := by
  simp [wedgeEdges, Finset.insert_subset_iff, Finset.singleton_subset_iff]

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixEpsilon
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

noncomputable def prefixEpsilon : ℝ := 1 / 2000
def prefixCycleCap : ℕ := 8000
def prefixTemplateCap : ℕ := 8001

noncomputable def prefixTargetDensity (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-(1 / 2 : ℝ) + prefixEpsilon)

noncomputable def prefixTargetTime (n : ℕ) : ℝ :=
  (n : ℝ)^2 / 6 * (1 - 1 / (n : ℝ) - prefixTargetDensity n)

noncomputable def prefixTime (n : ℕ) : ℕ := ⌊prefixTargetTime n⌋₊

noncomputable def prefixDensity (n : ℕ) : ℝ :=
  1 - 1 / (n : ℝ) - 6 * prefixTime n / (n : ℝ)^2

noncomputable def prefixD (n : ℕ) : ℝ := n * prefixDensity n ^ 2
noncomputable def prefixM (n : ℕ) : ℝ := (n : ℝ)^2 * prefixDensity n / 2

noncomputable def prefixLaw (n : ℕ) : PMF (Graph n) :=
  evolve (completeGraph n) (prefixTime n)

def neighbors {n : ℕ} (G : Graph n) (u : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => {u,v} ∈ G)

def currentDegree {n : ℕ} (G : Graph n) (u : Fin n) : ℕ :=
  (neighbors G u).card

def cycleNext {j : ℕ} (i : Fin j) : Fin j :=
  ⟨(i.val + 1) % j, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

noncomputable def linkCycleCount {n : ℕ} (j : ℕ) (G : Graph n) (u : Fin n) : ℝ := by
  classical
  exact ∑ φ : Fin j ↪ Fin n,
    if ∀ i, {u, φ i} ∈ G ∧ {φ i, φ (cycleNext i)} ∈ G then 1 else 0

def largeTemplateEligible {k : ℕ} (T : RootedTemplate k) (n : ℕ) (p : ℝ) : Prop :=
  ∀ W : Finset (Fin k), T.roots ⊆ W →
    ∀ F : Graph k, F ⊆ T.edges → (∀ e ∈ F, e ⊆ W) →
      1 ≤ (n : ℝ) ^ (W.card - T.roots.card) * p ^ F.card

def smallTemplateEligible {k : ℕ} (T : RootedTemplate k) (n : ℕ) (p : ℝ) : Prop :=
  ∀ J : Finset (Fin k), T.roots ⊆ J →
    (n : ℝ) ^ (k - J.card) * p ^ (T.edges.card - (T.edges.filter (· ⊆ J)).card) ≤ 1

noncomputable def prefixTemplateFactor (n : ℕ) (C : ℝ) : ℝ :=
  (1 + Real.log n) ^ C

def GoodPrefixGraph (n : ℕ) (c C : ℝ) (G : Graph n) : Prop :=
  G ⊆ completeGraph n ∧
  (G.card : ℝ) = prefixM n ∧
  (∀ u, |(currentDegree G u : ℝ) - n * prefixDensity n| ≤
    (n : ℝ)^(-c) * (n * prefixDensity n)) ∧
  (∀ u v, u ≠ v → |(currentCodegree G u v : ℝ) - prefixD n| ≤
    (n : ℝ)^(-c) * prefixD n) ∧
  (∀ j, 3 ≤ j → j ≤ prefixCycleCap → ∀ u,
    |linkCycleCount j G u - prefixD n ^ j| ≤ (n : ℝ)^(-c) * prefixD n ^ j) ∧
  (∀ k, k ≤ prefixTemplateCap → ∀ T : RootedTemplate k,
    ∀ ψ : {v // v ∈ T.roots} ↪ Fin n,
      (largeTemplateEligible T n (prefixDensity n) →
        rootedCount T ψ G ≤ prefixTemplateFactor n C * rootedScaling T n (prefixDensity n)) ∧
      (smallTemplateEligible T n (prefixDensity n) →
        rootedCount T ψ G ≤ prefixTemplateFactor n C))

noncomputable def prefixFailure (n : ℕ) (c C : ℝ) : ℝ := by
  classical
  exact pmfMean (prefixLaw n) (fun G => if GoodPrefixGraph n c C G then 0 else 1)

def UniformPrefixObligation : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
    prefixFailure n c C ≤ Real.exp (- (Real.log n) ^ (4 / 3 : ℝ))

end SharpTerminalLeave

open InnerProductSpace
open scoped InnerProductSpace

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_HistoryLawPathSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem historyLaw_path_support {α : Type*} (initial : PMF α)
    (K : ℕ → α → PMF α) (T k : ℕ) (hk : k ≤ T)
    (ω : History α T) (hω : ω ∈ (historyLaw initial K T k).support) :
    ω (historyIndex T 0) ∈ initial.support ∧
      ∀ j < k, ω (historyIndex T (j+1)) ∈ (K j (ω (historyIndex T j))).support := by
  induction k generalizing ω with
  | zero =>
    obtain ⟨a,ha,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hω
    exact ⟨ha,fun _ h => (Nat.not_lt_zero _ h).elim⟩
  | succ k ih =>
    have hkt : k < T := by omega
    obtain ⟨π,hπ,hω⟩ := (PMF.mem_support_bind_iff _ _ _).mp hω
    rw [historyKernel,ite_eq_left hkt] at hω
    obtain ⟨b,hb,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hω
    obtain ⟨hinit,hpath⟩ := ih (by omega) π hπ
    constructor
    · rw [Function.update_of_ne (historyIndex_ne_succ (Nat.zero_le k) hkt)]
      exact hinit
    · intro j hj
      by_cases he : j = k
      · subst j
        rw [Function.update_self,
          Function.update_of_ne (historyIndex_ne_succ le_rfl hkt)]
        exact hb
      · have hjk : j < k := by omega
        rw [Function.update_of_ne (historyIndex_ne_succ (by omega : j+1 ≤ k) hkt),
          Function.update_of_ne (historyIndex_ne_succ hjk.le hkt)]
        exact hpath j hjk

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_HistoryAdditive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

noncomputable def historyAdditive {α : Type*} (g : ℕ → α → α → ℝ)
    (T k : ℕ) (ω : History α T) : ℝ :=
  ∑ j ∈ Finset.range (min k T), g j (ω (historyIndex T j)) (ω (historyIndex T (j+1)))

@[simp] lemma historyAdditive_zero {α : Type*} (g : ℕ → α → α → ℝ)
    (T : ℕ) (ω : History α T) : historyAdditive g T 0 ω = 0 := by
  simp [historyAdditive]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_CodegreeVarianceRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

@[simp] theorem markovLaw_triangle_step {n : ℕ} (G : Graph n) (k : ℕ) :
    markovLaw (PMF.pure G) (fun _ => step) k = evolve G k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [markovLaw,evolve,ih]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_CopyEdgeLoad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

noncomputable def copyEdgeLoad {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) (e : Finset (Fin n)) : ℝ :=
  ∑ a, if e ∈ required a then intact (required a) G else 0

noncomputable def copyVarianceRate {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (L : ℝ) (_k : ℕ) (G : Graph n) : ℝ :=
  3*L*(copyCount required G - pmfMean (step G) (copyCount required))

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_CopyLoadSafe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

def copyLoadSafe {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (L : ℝ) (G : Graph n) : Prop :=
  ∀ e ∈ G, copyEdgeLoad required G e ≤ L

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_RelativeSafeCopyIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

noncomputable def relativeSafeCopyIncrement {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (L s : ℕ → ℝ) (j : ℕ) (G H : Graph n) : ℝ := by
  classical
  exact if copyLoadSafe required (L j) G then
    (copyCount required H - pmfMean (step G) (copyCount required)) / s (j+1) else 0

noncomputable def relativeCopyVarianceRate {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (L s : ℕ → ℝ) (j : ℕ) (G : Graph n) : ℝ :=
  copyVarianceRate required (L j) j G / (s (j+1))^2

noncomputable def relativeSafeCopyVarianceRate {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (L s : ℕ → ℝ) (j : ℕ) (G : Graph n) : ℝ := by
  classical
  exact if copyLoadSafe required (L j) G then relativeCopyVarianceRate required L s j G
    else 0

def pastRelativeCopyLoadsSafe {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (L : ℕ → ℝ) (T j : ℕ) (ω : History (Graph n) T) : Prop :=
  ∀ k < min j T, copyLoadSafe required (L k) (ω (historyIndex T k))

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_RelativeScaleBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

noncomputable def relativeScaleBudget (s : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range j, (s k / s (k+1) - 1)

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_EarlyDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

noncomputable def earlyDensity (n i : ℕ) : ℝ :=
  1-1/(n : ℝ)-6*(i : ℝ)/(n : ℝ)^2

@[simp] lemma earlyDensity_prefix (n : ℕ) :
    earlyDensity n (prefixTime n) = prefixDensity n := rfl

noncomputable def earlyTemplateScale (a b n i : ℕ) : ℝ :=
  (n : ℝ)^a * earlyDensity n i ^ b

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Coupling_UnitTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

section
open Filter MeasureTheory
open scoped BigOperators Topology BoundedContinuousFunction

namespace SharpTerminalLeave

def unitTime (t : ℝ) : ℝ := max 0 (min 1 t)

theorem unitTime_nonneg (t : ℝ) : 0 ≤ unitTime t := le_max_left _ _
theorem unitTime_le_one (t : ℝ) : unitTime t ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)
theorem unitTime_of_mem {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : unitTime t = t := by
  simp [unitTime, min_eq_right ht.2, max_eq_right ht.1]
theorem continuous_unitTime : Continuous unitTime :=
  continuous_const.max (continuous_const.min continuous_id)

theorem abs_prod_sub_prod_le_sum {α : Type*} (s : Finset α) (f g : α → ℝ)
    (hf : ∀ a ∈ s, f a ∈ Set.Icc (0 : ℝ) 1)
    (hg : ∀ a ∈ s, g a ∈ Set.Icc (0 : ℝ) 1) :
    |(∏ a ∈ s, f a) - ∏ a ∈ s, g a| ≤ ∑ a ∈ s, |f a - g a| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfa := hf a (Finset.mem_insert_self _ _)
    have hga := hg a (Finset.mem_insert_self _ _)
    have hfs := fun a (ha : a ∈ s) => hf a (Finset.mem_insert_of_mem ha)
    have hgs := fun a (ha : a ∈ s) => hg a (Finset.mem_insert_of_mem ha)
    have hp : |∏ i ∈ s, f i| ≤ 1 := by
      rw [abs_of_nonneg (Finset.prod_nonneg fun i hi => (hfs i hi).1)]
      exact Finset.prod_le_one (fun index hindex => (hfs index hindex).1)
        (fun index hindex => (hfs index hindex).2)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    calc
      _ = |(f a - g a) * (∏ i ∈ s, f i) +
          g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)| := by congr 1; ring
      _ ≤ |f a - g a| * |∏ i ∈ s, f i| +
          |g a| * |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| := by
        simpa only [abs_mul] using abs_add_le
          ((f a - g a) * (∏ i ∈ s, f i))
          (g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i))
      _ ≤ |f a - g a| * 1 + 1 * (∑ i ∈ s, |f i - g i|) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)
        · exact mul_le_mul (by simpa only [abs_of_nonneg hga.1] using hga.2)
            (ih hfs hgs) (abs_nonneg _) zero_le_one
      _ = _ := by ring

section Cavity
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

def messageCandidates (H : τ → Finset ι) (e : ι) (parent : Option τ) : Finset τ :=
  Finset.univ.filter (fun T => e ∈ H T ∧ some T ≠ parent)

noncomputable def messageIntegral (H : τ → Finset ι)
    (q : ι → Option τ → ℝ → ℝ) (e : ι) (T : τ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..unitTime t, ∏ f ∈ (H T).erase e, q f (some T) s

noncomputable def cavityOperator (H : τ → Finset ι)
    (q : ι → Option τ → ℝ → ℝ) (e : ι) (parent : Option τ) (t : ℝ) : ℝ :=
  ∏ T ∈ messageCandidates H e parent, (1 - messageIntegral H q e T t)

noncomputable def cavityDepth (H : τ → Finset ι) : ℕ → ι → Option τ → ℝ → ℝ
  | 0 => fun _ _ _ => 1
  | k + 1 => cavityOperator H (cavityDepth H k)

omit [Fintype ι] [Fintype τ] [DecidableEq τ] in
theorem continuous_message_integrand (H : τ → Finset ι)
    (q : ι → Option τ → ℝ → ℝ) (hq : ∀ e p, Continuous (q e p)) (e : ι) (T : τ) :
    Continuous (fun s => ∏ f ∈ (H T).erase e, q f (some T) s) := by
  exact continuous_finsetProd _ (fun f _ => hq f (some T))

omit [Fintype ι] [Fintype τ] [DecidableEq τ] in
theorem continuous_messageIntegral (H : τ → Finset ι)
    (q : ι → Option τ → ℝ → ℝ) (hq : ∀ e p, Continuous (q e p)) (e : ι) (T : τ) :
    Continuous (messageIntegral H q e T) := by
  exact (intervalIntegral.continuous_primitive
    (fun a b => (continuous_message_integrand H q hq e T).intervalIntegrable a b) 0).comp
      continuous_unitTime

omit [Fintype ι] in
theorem continuous_cavityOperator (H : τ → Finset ι)
    (q : ι → Option τ → ℝ → ℝ) (hq : ∀ e p, Continuous (q e p)) (e : ι) (p : Option τ) :
    Continuous (cavityOperator H q e p) := by
  exact continuous_finsetProd _ (fun T _ =>
    continuous_const.sub (continuous_messageIntegral H q hq e T))

omit [Fintype ι] in
theorem continuous_cavityDepth (H : τ → Finset ι) (k : ℕ) (e : ι) (p : Option τ) :
    Continuous (cavityDepth H k e p) := by
  induction k generalizing e p with
  | zero => exact continuous_const
  | succ k ih => exact continuous_cavityOperator H _ ih e p

omit [Fintype ι] [Fintype τ] [DecidableEq τ] in
theorem messageIntegral_mem_unit (H : τ → Finset ι)
    (q : ι → Option τ → ℝ → ℝ) (hc : ∀ e p, Continuous (q e p))
    (hq : ∀ e p t, q e p t ∈ Set.Icc (0 : ℝ) 1) (e : ι) (T : τ) (t : ℝ) :
    messageIntegral H q e T t ∈ Set.Icc (0 : ℝ) 1 := by
  have ha : ∀ s, 0 ≤ ∏ f ∈ (H T).erase e, q f (some T) s := fun s =>
    Finset.prod_nonneg fun f _ => (hq f (some T) s).1
  have hb : ∀ s, (∏ f ∈ (H T).erase e, q f (some T) s) ≤ 1 := fun s =>
    Finset.prod_le_one (fun edge _ => (hq edge (some T) s).1)
      (fun edge _ => (hq edge (some T) s).2)
  refine ⟨intervalIntegral.integral_nonneg_of_forall (unitTime_nonneg t) ha, ?_⟩
  have hu := intervalIntegral.integral_mono_on (μ := volume) (unitTime_nonneg t)
    ((continuous_message_integrand H q hc e T).intervalIntegrable 0 (unitTime t))
    (continuous_const.intervalIntegrable 0 (unitTime t)) (fun s _ => hb s)
  have : messageIntegral H q e T t ≤ unitTime t := by simpa [messageIntegral] using hu
  exact this.trans (unitTime_le_one t)

omit [Fintype ι] in
theorem cavityOperator_mem_unit (H : τ → Finset ι)
    (q : ι → Option τ → ℝ → ℝ) (hc : ∀ e p, Continuous (q e p))
    (hq : ∀ e p t, q e p t ∈ Set.Icc (0 : ℝ) 1) (e : ι) (p : Option τ) (t : ℝ) :
    cavityOperator H q e p t ∈ Set.Icc (0 : ℝ) 1 := by
  have hh : ∀ T, 1 - messageIntegral H q e T t ∈ Set.Icc (0 : ℝ) 1 := by
    intro T
    have h := messageIntegral_mem_unit H q hc hq e T t
    constructor <;> linarith [h.1, h.2]
  exact ⟨Finset.prod_nonneg (fun T _ => (hh T).1),
    Finset.prod_le_one (fun triangle _ => (hh triangle).1)
      (fun triangle _ => (hh triangle).2)⟩

omit [Fintype ι] in
theorem cavityDepth_mem_unit (H : τ → Finset ι) (k : ℕ) (e : ι) (p : Option τ) (t : ℝ) :
    cavityDepth H k e p t ∈ Set.Icc (0 : ℝ) 1 := by
  induction k generalizing e p t with
  | zero => exact ⟨zero_le_one, le_rfl⟩
  | succ k ih => exact cavityOperator_mem_unit H _ (continuous_cavityDepth H k) ih e p t

def cavityBranching : ℝ := (Fintype.card τ : ℝ) * Fintype.card ι

omit [DecidableEq ι] [DecidableEq τ] in
theorem cavityBranching_nonneg : 0 ≤ cavityBranching (ι := ι) (τ := τ) := by
  unfold cavityBranching
  positivity

theorem cavityOperator_lipschitz (H : τ → Finset ι)
    (q r : ι → Option τ → ℝ → ℝ)
    (hqc : ∀ e p, Continuous (q e p)) (hrc : ∀ e p, Continuous (r e p))
    (hq : ∀ e p t, q e p t ∈ Set.Icc (0 : ℝ) 1)
    (hr : ∀ e p t, r e p t ∈ Set.Icc (0 : ℝ) 1)
    (b : ℝ → ℝ) (hbc : Continuous b) (hb : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ b s)
    (hqr : ∀ e p s, s ∈ Set.Icc (0 : ℝ) 1 → |q e p s - r e p s| ≤ b s)
    (e : ι) (p : Option τ) (t : ℝ) :
    |cavityOperator H q e p t - cavityOperator H r e p t| ≤
      cavityBranching (ι := ι) (τ := τ) * ∫ s in (0 : ℝ)..unitTime t, b s := by
  have ht : ∀ s ∈ Set.Icc (0 : ℝ) (unitTime t), s ∈ Set.Icc (0 : ℝ) 1 :=
    fun s hs => ⟨hs.1, hs.2.trans (unitTime_le_one t)⟩
  have hbi : 0 ≤ ∫ s in (0 : ℝ)..unitTime t, b s := by
    have h := intervalIntegral.integral_mono_on (μ := volume) (unitTime_nonneg t)
      (continuous_const.intervalIntegrable 0 (unitTime t))
      (hbc.intervalIntegrable 0 (unitTime t)) (fun s hs => hb s (ht s hs))
    simpa using h
  have hinner : ∀ T s, s ∈ Set.Icc (0 : ℝ) (unitTime t) →
      |(∏ f ∈ (H T).erase e, q f (some T) s) -
        ∏ f ∈ (H T).erase e, r f (some T) s| ≤ (Fintype.card ι : ℝ) * b s := by
    intro T s hs
    calc
      _ ≤ ∑ f ∈ (H T).erase e, |q f (some T) s - r f (some T) s| :=
        abs_prod_sub_prod_le_sum _ _ _ (fun f _ => hq f (some T) s) (fun f _ => hr f (some T) s)
      _ ≤ ∑ _f ∈ (H T).erase e, b s :=
        Finset.sum_le_sum fun f _ => hqr f (some T) s (ht s hs)
      _ = (((H T).erase e).card : ℝ) * b s := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ ((H T).erase e))
        (hb s (ht s hs))
  have hint : ∀ T, |messageIntegral H q e T t - messageIntegral H r e T t| ≤
      (Fintype.card ι : ℝ) * ∫ s in (0 : ℝ)..unitTime t, b s := by
    intro T
    have hqint := (continuous_message_integrand H q hqc e T).intervalIntegrable (μ := volume) 0 (unitTime t)
    have hrint := (continuous_message_integrand H r hrc e T).intervalIntegrable (μ := volume) 0 (unitTime t)
    rw [messageIntegral, messageIntegral, ← intervalIntegral.integral_sub hqint hrint]
    calc
      _ ≤ ∫ s in (0 : ℝ)..unitTime t,
          |(∏ f ∈ (H T).erase e, q f (some T) s) -
            ∏ f ∈ (H T).erase e, r f (some T) s| :=
        intervalIntegral.abs_integral_le_integral_abs (unitTime_nonneg t)
      _ ≤ ∫ s in (0 : ℝ)..unitTime t, (Fintype.card ι : ℝ) * b s := by
        apply intervalIntegral.integral_mono_on (unitTime_nonneg t)
          (((continuous_message_integrand H q hqc e T).sub
            (continuous_message_integrand H r hrc e T)).abs.intervalIntegrable 0 (unitTime t))
          ((continuous_const.mul hbc).intervalIntegrable 0 (unitTime t))
        exact hinner T
      _ = _ := intervalIntegral.integral_const_mul _ _
  have hqf : ∀ T ∈ messageCandidates H e p,
      1 - messageIntegral H q e T t ∈ Set.Icc (0 : ℝ) 1 := by
    intro T _
    have h := messageIntegral_mem_unit H q hqc hq e T t
    constructor <;> linarith [h.1, h.2]
  have hrf : ∀ T ∈ messageCandidates H e p,
      1 - messageIntegral H r e T t ∈ Set.Icc (0 : ℝ) 1 := by
    intro T _
    have h := messageIntegral_mem_unit H r hrc hr e T t
    constructor <;> linarith [h.1, h.2]
  calc
    _ ≤ ∑ T ∈ messageCandidates H e p,
        |(1 - messageIntegral H q e T t) - (1 - messageIntegral H r e T t)| :=
      abs_prod_sub_prod_le_sum _ _ _ hqf hrf
    _ ≤ ∑ _T ∈ messageCandidates H e p,
        (Fintype.card ι : ℝ) * ∫ s in (0 : ℝ)..unitTime t, b s := by
      apply Finset.sum_le_sum
      intro T _
      simpa only [sub_sub_sub_cancel_left, abs_sub_comm] using hint T
    _ = ((messageCandidates H e p).card : ℝ) *
        ((Fintype.card ι : ℝ) * ∫ s in (0 : ℝ)..unitTime t, b s) := by simp
    _ ≤ (Fintype.card τ : ℝ) *
        ((Fintype.card ι : ℝ) * ∫ s in (0 : ℝ)..unitTime t, b s) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Finset.card_le_univ (messageCandidates H e p)
      · positivity
    _ = _ := by rw [cavityBranching]; ring

theorem cavityDepth_succ_diff (H : τ → Finset ι) (k : ℕ) (e : ι) (p : Option τ) (t : ℝ) :
    |cavityDepth H (k + 1) e p t - cavityDepth H k e p t| ≤
      cavityBranching (ι := ι) (τ := τ) ^ k * (unitTime t) ^ k / k.factorial := by
  let M := cavityBranching (ι := ι) (τ := τ)
  have hM : 0 ≤ M := cavityBranching_nonneg
  induction k generalizing e p t with
  | zero =>
    have h := cavityDepth_mem_unit H 1 e p t
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, div_one]
    change |cavityDepth H 1 e p t - 1| ≤ 1
    exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
  | succ k ih =>
    let b : ℝ → ℝ := fun s => M ^ k / (k.factorial : ℝ) * s ^ k
    have hbc : Continuous b := continuous_const.mul (continuous_id.pow k)
    have hb : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ b s := by
      intro s hs
      exact mul_nonneg (div_nonneg (pow_nonneg hM _) (Nat.cast_nonneg _))
        (pow_nonneg hs.1 _)
    have hd : ∀ e p s, s ∈ Set.Icc (0 : ℝ) 1 →
        |cavityDepth H (k + 1) e p s - cavityDepth H k e p s| ≤ b s := by
      intro e p s hs
      have h := ih e p s
      rw [unitTime_of_mem hs] at h
      simpa only [b, M, div_mul_eq_mul_div] using h
    have h := cavityOperator_lipschitz H (cavityDepth H (k + 1)) (cavityDepth H k)
      (continuous_cavityDepth H (k + 1)) (continuous_cavityDepth H k)
      (cavityDepth_mem_unit H (k + 1)) (cavityDepth_mem_unit H k)
      b hbc hb hd e p t
    change |cavityOperator H (cavityDepth H (k + 1)) e p t -
      cavityOperator H (cavityDepth H k) e p t| ≤ _
    apply h.trans_eq
    simp only [b, intervalIntegral.integral_const_mul, integral_pow, zero_pow (Nat.succ_ne_zero k),
      sub_zero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    dsimp [M]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

abbrev CavitySpace (ι τ : Type*) := ι → Option τ → (ℝ →ᵇ ℝ)

noncomputable def cavityDepthBCF (H : τ → Finset ι) (k : ℕ) : CavitySpace ι τ :=
  fun e p => BoundedContinuousFunction.mkOfBound
    ⟨cavityDepth H k e p, continuous_cavityDepth H k e p⟩ 1 (by
      intro x y
      change |cavityDepth H k e p x - cavityDepth H k e p y| ≤ 1
      have hx := cavityDepth_mem_unit H k e p x
      have hy := cavityDepth_mem_unit H k e p y
      exact abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩)

omit [Fintype ι] in
@[simp] theorem cavityDepthBCF_apply (H : τ → Finset ι) (k : ℕ) (e : ι) (p : Option τ) (t : ℝ) :
    cavityDepthBCF H k e p t = cavityDepth H k e p t := rfl

theorem cavityDepthBCF_succ_dist (H : τ → Finset ι) (k : ℕ) :
    dist (cavityDepthBCF H k) (cavityDepthBCF H (k + 1)) ≤
      cavityBranching (ι := ι) (τ := τ) ^ k / k.factorial := by
  have hb : 0 ≤ cavityBranching (ι := ι) (τ := τ) ^ k / (k.factorial : ℝ) :=
    div_nonneg (pow_nonneg cavityBranching_nonneg _) (Nat.cast_nonneg _)
  rw [dist_comm, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg hb).mpr
  intro e
  apply (pi_norm_le_iff_of_nonneg hb).mpr
  intro p
  apply (BoundedContinuousFunction.norm_le hb).mpr
  intro t
  change |cavityDepth H (k + 1) e p t - cavityDepth H k e p t| ≤ _
  apply (cavityDepth_succ_diff H k e p t).trans
  calc
    _ = (cavityBranching (ι := ι) (τ := τ) ^ k / k.factorial) * (unitTime t) ^ k := by ring
    _ ≤ (cavityBranching (ι := ι) (τ := τ) ^ k / k.factorial) * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ (unitTime_nonneg t) (unitTime_le_one t)) hb
    _ = _ := mul_one _

theorem cavityDepthBCF_cauchy (H : τ → Finset ι) : CauchySeq (cavityDepthBCF H) :=
  cauchySeq_of_dist_le_of_summable _ (cavityDepthBCF_succ_dist H)
    (Real.summable_pow_div_factorial _)

noncomputable def cavityLimitBCF (H : τ → Finset ι) : CavitySpace ι τ :=
  (cauchySeq_tendsto_of_complete (cavityDepthBCF_cauchy H)).choose

noncomputable def cavityLimit (H : τ → Finset ι) (e : ι) (p : Option τ) (t : ℝ) : ℝ :=
  cavityLimitBCF H e p t

omit [Fintype ι] in
@[simp] theorem cavityDepth_zero_time (H : τ → Finset ι) (k : ℕ) (e : ι) (p : Option τ) :
    cavityDepth H k e p 0 = 1 := by
  cases k <;> simp [cavityDepth, cavityOperator, messageIntegral, unitTime]

noncomputable def cavityTime (D s : ℝ) : ℝ := (Real.exp (2 * s) - 1) / (2 * D)

noncomputable def cavityLog (H : τ → Finset ι) (D : ℝ) (e : ι) (s : ℝ) : ℝ :=
  Real.log (cavityLimit H e none (cavityTime D s)) + s

noncomputable def cavityMessage (H : τ → Finset ι) (D : ℝ) (e : ι) (T : τ) (s : ℝ) : ℝ :=
  messageIntegral H (cavityLimit H) e T (cavityTime D s)

omit [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ] in
@[simp] theorem cavityTime_zero (D : ℝ) : cavityTime D 0 = 0 := by
  simp [cavityTime]

@[simp] theorem cavityMessage_zero (H : τ → Finset ι) (D : ℝ) (e : ι) (T : τ) :
    cavityMessage H D e T 0 = 0 := by
  simp [cavityMessage, messageIntegral, unitTime]

end Cavity
end SharpTerminalLeave

open scoped BigOperators

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_ProductPMF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

noncomputable def productPMF {K V : Type*} [Fintype K] [DecidableEq K] [Fintype V]
    (ρ : K → PMF V) : PMF (K → V) :=
  PMF.ofFintype (fun ω => ∏ k, ρ k (ω k)) (by
    calc
      (∑ ω : K → V, ∏ k, ρ k (ω k)) = ∏ k, ∑ v, ρ k v :=
        (Fintype.prod_sum (fun (k : K) (v : V) => ρ k v)).symm
      _ = 1 := by
        apply Finset.prod_eq_one
        intro k _
        simpa only [tsum_fintype] using (ρ k).tsum_coe)

@[simp] theorem productPMF_apply {K V : Type*} [Fintype K] [DecidableEq K] [Fintype V]
    (ρ : K → PMF V) (ω : K → V) : productPMF ρ ω = ∏ k, ρ k (ω k) := rfl

@[simp] theorem productPMF_support {K V : Type*} [Fintype K] [DecidableEq K] [Fintype V]
    (ρ : K → PMF V) (ω : K → V) :
    ω ∈ (productPMF ρ).support ↔ ∀ k, ω k ∈ (ρ k).support := by
  simp [PMF.mem_support_iff, Finset.prod_ne_zero_iff]

inductive ExposureTree (K V O : Type*) where
  | done : O → ExposureTree K V O
  | ask : K → (V → ExposureTree K V O) → ExposureTree K V O

namespace ExposureTree
variable {K V O : Type*}

def evaluate (ω : K → V) : ExposureTree K V O → O
  | .done o => o
  | .ask k f => evaluate ω (f (ω k))

noncomputable def fresh (ν : K → PMF V) : ExposureTree K V O → PMF O
  | .done o => PMF.pure o
  | .ask k f => (ν k).bind (fun v => fresh ν (f v))

noncomputable def coupled [DecidableEq K] (ν : K → PMF V) (ω : K → V) :
    ExposureTree K V O → Finset K → PMF (O × Bool)
  | .done o, _ => PMF.pure (o, false)
  | .ask k f, seen =>
      if k ∈ seen then
        (ν k).bind (fun v => (coupled ν ω (f v) seen).map (fun z => (z.1, true)))
      else coupled ν ω (f (ω k)) (insert k seen)

noncomputable def freshRecorded [DecidableEq K] (ν : K → PMF V) :
    ExposureTree K V O → Finset K → PMF (O × Bool)
  | .done o, _ => PMF.pure (o, false)
  | .ask k f, seen =>
      (ν k).bind (fun v => if k ∈ seen then
        (freshRecorded ν (f v) seen).map (fun z => (z.1, true))
        else freshRecorded ν (f v) (insert k seen))

end ExposureTree

namespace ExposureTree
variable {K V O : Type*} [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]

noncomputable def jointLaw (ν : K → PMF V) (P : ExposureTree K V O) :
    PMF (O × (O × Bool)) :=
  (productPMF ν).bind (fun ω =>
    (coupled ν ω P ∅).map (fun z => (evaluate ω P, z)))

end ExposureTree
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_TreeBind
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave
namespace ExposureTree
variable {K V O P : Type*}

def bind : ExposureTree K V O → (O → ExposureTree K V P) → ExposureTree K V P
  | .done o, f => f o
  | .ask k g, f => .ask k (fun v => bind (g v) f)

@[simp] theorem evaluate_bind (ω : K → V) (A : ExposureTree K V O)
    (f : O → ExposureTree K V P) : evaluate ω (bind A f) = evaluate ω (f (evaluate ω A)) := by
  induction A with
  | done o => rfl
  | ask k g ih => exact ih (ω k)

@[simp] theorem fresh_bind (ν : K → PMF V) (A : ExposureTree K V O)
    (f : O → ExposureTree K V P) : fresh ν (bind A f) = (fresh ν A).bind (fun o => fresh ν (f o)) := by
  induction A with
  | done o => simp [bind, fresh]
  | ask k g ih => simp only [bind, fresh, ih, PMF.bind_bind]

def exposeValues : List K → ExposureTree K V (List (K × V))
  | [] => .done []
  | k :: ks => .ask k (fun v => bind (exposeValues ks) (fun xs => .done ((k, v) :: xs)))

def checkNone : List (ExposureTree K V Bool) → ExposureTree K V Bool
  | [] => .done true
  | A :: As => bind A (fun b => if b then .done false else checkNone As)

end ExposureTree

noncomputable def trueProbability (p : PMF Bool) : ℝ := (p true).toReal
noncomputable def falseProbability (p : PMF Bool) : ℝ := (p false).toReal

@[simp] theorem trueProbability_pure (b : Bool) : trueProbability (PMF.pure b) = if b then 1 else 0 := by
  cases b <;> simp [trueProbability]

@[simp] theorem falseProbability_pure (b : Bool) : falseProbability (PMF.pure b) = if b then 0 else 1 := by
  cases b <;> simp [falseProbability]

namespace ExposureTree
variable {K V : Type*}

def exposeLabeled {A : Type*} (key : A → K) : List A → ExposureTree K V (List (A × V))
  | [] => .done []
  | a :: as => .ask (key a) (fun v => bind (exposeLabeled key as)
      (fun xs => .done ((a, v) :: xs)))

end ExposureTree

section GridQuery
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

def gridCandidates (H : τ → Finset ι) (focus : Finset ι) (parent : Option τ) :
    Finset (ι × τ) :=
  (focus.product Finset.univ).filter (fun p => p.1 ∈ H p.2 ∧ some p.2 ≠ parent)

noncomputable def gridQueryDepth (H : τ → Finset ι) (N : ℕ) :
    ℕ → ℕ → Finset ι → Option τ → ExposureTree τ (Fin N) Bool
  | 0, _, focus, parent =>
      ExposureTree.bind
        (ExposureTree.exposeLabeled Prod.snd (gridCandidates H focus parent).toList)
        (fun _ => .done true)
  | d + 1, k, focus, parent =>
      ExposureTree.bind
        (ExposureTree.exposeLabeled Prod.snd (gridCandidates H focus parent).toList)
        (fun values => ExposureTree.checkNone
          (((values.mergeSort (fun a b => a.2.val ≤ b.2.val)).map
            (fun p => if p.2.val < k then
              gridQueryDepth H N d p.2.val ((H p.1.2).erase p.1.1) (some p.1.2)
              else .done false))))

noncomputable def gridPriorities (N : ℕ) [NeZero N] : τ → PMF (Fin N) :=
  fun _ => PMF.uniformOfFintype (Fin N)

noncomputable def gridAnswerProbability (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) : ℝ :=
  trueProbability (ExposureTree.fresh (gridPriorities N) (gridQueryDepth H N d k focus parent))

@[simp] theorem gridAnswerProbability_zero (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k : ℕ) (focus : Finset ι) (parent : Option τ) :
    gridAnswerProbability H N 0 k focus parent = 1 := by
  simp [gridAnswerProbability, gridQueryDepth, ExposureTree.fresh_bind,
    ExposureTree.fresh, PMF.bind_const]

noncomputable def gridMessage (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (e : ι) (parent : Option τ) : ℝ :=
  gridAnswerProbability H N d k {e} parent

namespace ExposureTree
@[simp] theorem checkNone_done_false {K V A : Type*} (xs : List A) :
    checkNone (xs.map (fun _ => (done false : ExposureTree K V Bool))) = done true := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, checkNone, bind, Bool.false_eq_true,
      ↓reduceIte, ih]
end ExposureTree

end GridQuery
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_FreshLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave.ExposureTree
open scoped BigOperators

variable {K V O P : Type*}

noncomputable def freshLog (ν : K → PMF V) : ExposureTree K V O → PMF (O × List K)
  | .done o => PMF.pure (o, [])
  | .ask k f => (ν k).bind (fun v =>
      (freshLog ν (f v)).map (fun z => (z.1, k :: z.2)))

def repeats [DecidableEq K] : Finset K → List K → Bool
  | _, [] => false
  | seen, k :: ks => decide (k ∈ seen) || repeats (insert k seen) ks

@[simp] theorem repeats_cons [DecidableEq K] (seen : Finset K) (k : K) (ks : List K) :
    repeats seen (k :: ks) = (decide (k ∈ seen) || repeats (insert k seen) ks) := rfl

@[simp] theorem freshLog_outcome (ν : K → PMF V) (A : ExposureTree K V O) :
    (freshLog ν A).map Prod.fst = fresh ν A := by
  induction A with
  | done o => simp [freshLog, fresh, PMF.pure_map]
  | ask k f ih =>
    simp only [freshLog, PMF.map_bind, PMF.map_comp, fresh]
    congr 1
    funext v
    exact ih v

theorem freshLog_bind (ν : K → PMF V) (A : ExposureTree K V O)
    (f : O → ExposureTree K V P) :
    freshLog ν (bind A f) =
      (freshLog ν A).bind (fun z =>
        (freshLog ν (f z.1)).map (fun y => (y.1, z.2 ++ y.2))) := by
  induction A with
  | done o =>
    simp only [bind, freshLog, PMF.pure_bind, List.nil_append]
    exact (PMF.map_id _).symm
  | ask k g ih =>
    simp only [bind, freshLog, ih, PMF.bind_bind, PMF.map_bind, PMF.bind_map,
      PMF.map_comp]
    congr 1

end SharpTerminalLeave.ExposureTree

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_MapOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave
namespace ExposureTree
variable {K V O P Q : Type*}

def mapOutput (f : O → P) : ExposureTree K V O → ExposureTree K V P
  | .done o => .done (f o)
  | .ask k g => .ask k (fun v => mapOutput f (g v))

@[simp] theorem mapOutput_done (f : O → P) (o : O) :
    mapOutput (K := K) (V := V) f (.done o) = .done (f o) := rfl

@[simp] theorem mapOutput_bind (f : P → Q) (A : ExposureTree K V O)
    (g : O → ExposureTree K V P) :
    mapOutput f (bind A g) = bind A (fun o => mapOutput f (g o)) := by
  induction A with
  | done o => rfl
  | ask k h ih => simp only [bind, mapOutput, ih]

@[simp] theorem bind_mapOutput (f : O → P) (A : ExposureTree K V O)
    (g : P → ExposureTree K V Q) :
    bind (mapOutput f A) g = bind A (fun o => g (f o)) := by
  induction A with
  | done o => rfl
  | ask k h ih => simp only [bind, mapOutput, ih]

@[simp] theorem mapOutput_comp (f : P → Q) (g : O → P) (A : ExposureTree K V O) :
    mapOutput f (mapOutput g A) = mapOutput (f ∘ g) A := by
  induction A with
  | done o => rfl
  | ask k h ih => simp only [mapOutput, ih]

@[simp] theorem mapOutput_id (A : ExposureTree K V O) : mapOutput id A = A := by
  induction A with
  | done o => rfl
  | ask k h ih => simp only [mapOutput, ih]

@[simp] theorem fresh_mapOutput (ν : K → PMF V) (f : O → P) (A : ExposureTree K V O) :
    fresh ν (mapOutput f A) = (fresh ν A).map f := by
  induction A with
  | done o => simp [mapOutput, fresh, PMF.pure_map]
  | ask k h ih => simp only [mapOutput, fresh, ih, PMF.map_bind]

@[simp] theorem freshLog_mapOutput (ν : K → PMF V) (f : O → P) (A : ExposureTree K V O) :
    freshLog ν (mapOutput f A) = (freshLog ν A).map (fun z => (f z.1, z.2)) := by
  induction A with
  | done o => simp [mapOutput, freshLog, PMF.pure_map]
  | ask k h ih =>
    simp only [mapOutput, freshLog, ih, PMF.map_bind, PMF.map_comp]
    rfl

def checkNoneTrace {R : Type*} :
    List (ExposureTree K V (Bool × List R)) → ExposureTree K V (Bool × List R)
  | [] => .done (true, [])
  | A :: As => bind A (fun z =>
      if z.1 then .done (false, z.2)
      else mapOutput (fun y => (y.1, z.2 ++ y.2)) (checkNoneTrace As))

@[simp] theorem checkNoneTrace_outcome {R : Type*}
    (as : List (ExposureTree K V (Bool × List R))) :
    mapOutput Prod.fst (checkNoneTrace as) =
      checkNone (as.map (mapOutput Prod.fst)) := by
  induction as with
  | nil => rfl
  | cons A as ih =>
    simp only [checkNoneTrace, mapOutput_bind, List.map_cons, checkNone,
      bind_mapOutput]
    congr 1
    funext z
    cases z.1 <;> simp only [Bool.false_eq_true, ↓reduceIte, mapOutput_done,
      mapOutput_comp]
    exact ih

end ExposureTree

section TraceQuery
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

structure QueryCall (ι τ : Type*) where
  address : List (ι × τ)
  focus : Finset ι
  parent : Option τ

noncomputable def QueryCall.keys (H : τ → Finset ι) (c : QueryCall ι τ) : List τ :=
  (gridCandidates H c.focus c.parent).toList.map Prod.snd

noncomputable def tracedGridQuery (H : τ → Finset ι) (N : ℕ) :
    ℕ → ℕ → QueryCall ι τ → ExposureTree τ (Fin N) (Bool × List (QueryCall ι τ))
  | 0, _, c => ExposureTree.bind
      (ExposureTree.exposeLabeled Prod.snd (gridCandidates H c.focus c.parent).toList)
      (fun _ => .done (true, [c]))
  | d+1, k, c => ExposureTree.bind
      (ExposureTree.exposeLabeled Prod.snd (gridCandidates H c.focus c.parent).toList)
      (fun values => ExposureTree.mapOutput (fun y => (y.1, c :: y.2))
        (ExposureTree.checkNoneTrace
          ((values.mergeSort (fun a b => a.2.val ≤ b.2.val)).map
            (fun p => if p.2.val < k then
              tracedGridQuery H N d p.2.val
                ⟨p.1 :: c.address, (H p.1.2).erase p.1.1, some p.1.2⟩
              else .done (false, [])))))

end TraceQuery
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_FreshLogExposeLabeled
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave.ExposureTree
variable {K V O R A : Type*}

theorem freshLog_exposeLabeled_support (ν : K → PMF V) (key : A → K) (as : List A)
    {z : List (A × V) × List K}
    (hz : z ∈ (freshLog ν (exposeLabeled key as)).support) :
    z.1.map Prod.fst = as ∧ z.2 = as.map key := by
  induction as generalizing z with
  | nil =>
    have heq : z = ([],[]) := by simpa [exposeLabeled, freshLog] using hz
    simp [heq]
  | cons a as ih =>
    simp only [exposeLabeled, freshLog, PMF.mem_support_bind_iff] at hz
    obtain ⟨v,_,hv⟩ := hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hv
    rw [freshLog_bind] at hy
    obtain ⟨w,hw,hy⟩ := (PMF.mem_support_bind_iff _ _ _).mp hy
    have heq : y = ((a,v)::w.1,w.2) := by
      simpa [freshLog, PMF.pure_map, List.append_nil] using hy
    obtain ⟨hvals,hkeys⟩ := ih hw
    simp [heq,hvals,hkeys]

end SharpTerminalLeave.ExposureTree

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Coupling_OrderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators
open scoped BigOperators ENNReal Classical

namespace SharpTerminalLeave
section RandomOrder
variable {K : Type*} [Fintype K] [DecidableEq K]

noncomputable def orderLaw : ℕ → Finset K → PMF (List K)
  | 0, _ => PMF.pure []
  | d + 1, C =>
      if h : C.Nonempty then
        (PMF.uniformOfFinset C h).bind
          (fun a => (orderLaw d (C.erase a)).map (List.cons a))
      else PMF.pure []

omit [Fintype K] in
@[simp] theorem pmf_map_cons_apply (p : PMF (List K)) (a b : K) (bs : List K) :
    (p.map (List.cons a)) (b :: bs) = if a = b then p bs else 0 := by
  by_cases hab : a = b
  · subst b
    simp [PMF.map_apply]
  · simp [PMF.map_apply, hab, Ne.symm hab]

omit [Fintype K] [DecidableEq K] in
@[simp] theorem pmf_map_cons_nil (p : PMF (List K)) (a : K) :
    (p.map (List.cons a)) [] = 0 := by simp [PMF.map_apply]

def Enumerates (C : Finset K) (as : List K) : Prop := as.Nodup ∧ as.toFinset = C

omit [Fintype K] in
@[simp] theorem enumerates_nil (C : Finset K) : Enumerates C [] ↔ C = ∅ := by
  simp [Enumerates, eq_comm]

omit [Fintype K] in
@[simp] theorem enumerates_cons (C : Finset K) (a : K) (as : List K) :
    Enumerates C (a :: as) ↔ a ∈ C ∧ Enumerates (C.erase a) as := by
  constructor
  · rintro ⟨hn, hc⟩
    have ha : a ∉ as.toFinset := by simpa using (List.nodup_cons.mp hn).1
    simp only [List.toFinset_cons] at hc
    refine ⟨hc ▸ Finset.mem_insert_self _ _, (List.nodup_cons.mp hn).2, ?_⟩
    rw [← hc, Finset.erase_insert ha]
  · rintro ⟨ha, hn, hc⟩
    have han : a ∉ as := by
      simpa only [← List.mem_toFinset] using (hc ▸ Finset.notMem_erase a C)
    refine ⟨List.nodup_cons.mpr ⟨han, hn⟩, ?_⟩
    simp only [List.toFinset_cons, hc, Finset.insert_erase ha]

end RandomOrder
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Coupling_ClockOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators
open scoped BigOperators ENNReal Classical

namespace SharpTerminalLeave
section ClockOrders
variable {K V : Type*} [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]

noncomputable def clockOrder (ω : K → ℕ) : List K :=
  Finset.univ.toList.mergeSort (fun a b => ω a ≤ ω b)

end ClockOrders
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Stability_GridCavityError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave
open Filter
open scoped BigOperators Topology

section GridApproximation
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

noncomputable def gridCavityError (H : τ → Finset ι) (N : ℕ) [NeZero N] (k : ℕ) : ℝ :=
  ‖(fun ep : ι × Option τ => gridMessage H N N k ep.1 ep.2 -
    cavityLimit H ep.1 ep.2 ((k : ℝ) / N))‖

end GridApproximation
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Coupling_GridUniformError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave
section GridRowBounds
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

noncomputable def gridUniformError (_H : τ → Finset ι) : ℝ :=
  ((Fintype.card τ : ℝ)^2 * Fintype.card ι) *
    Real.exp ((Fintype.card τ : ℝ) * Fintype.card ι)

noncomputable def gridCandidateFailure (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k : ℕ) (e : ι) (T : τ) : ℝ :=
  1 - (1/(N : ℝ)) * ∑ j ∈ Finset.range k,
    ∏ f ∈ (H T).erase e, gridMessage H N N j f (some T)

end GridRowBounds
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_LevelDeletes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators
open scoped BigOperators ENNReal Classical

namespace SharpTerminalLeave
namespace ExposureTree
variable {K V O A : Type*}

@[simp] theorem evaluate_exposeLabeled (ω : K → V) (key : A → K) (as : List A) :
    evaluate ω (exposeLabeled key as) = as.map (fun a => (a, ω (key a))) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [exposeLabeled, evaluate, evaluate_bind, ih, List.map_cons]

@[simp] theorem evaluate_checkNone (ω : K → V) (as : List (ExposureTree K V Bool)) :
    evaluate ω (checkNone as) = true ↔ ∀ A ∈ as, evaluate ω A = false := by
  induction as with
  | nil => simp [checkNone, evaluate]
  | cons A as ih =>
    simp only [checkNone, evaluate_bind, List.mem_cons, forall_eq_or_imp]
    cases h : evaluate ω A <;> simp [evaluate, ih]

end ExposureTree

section TimeScan
variable {ι τ : Type*} [DecidableEq ι] [Fintype τ] [DecidableEq τ]

def levelDeletes (H : τ → Finset ι) (ω : τ → ℕ) (G : Finset ι) (k : ℕ) : Finset ι :=
  (Finset.univ.filter (fun T => ω T = k ∧ H T ⊆ G)).biUnion H

def timeScan (H : τ → Finset ι) (ω : τ → ℕ) (E : Finset ι) : ℕ → Finset ι
  | 0 => E
  | k + 1 => timeScan H ω E k \ levelDeletes H ω (timeScan H ω E k) k

omit [DecidableEq τ] in
@[simp] theorem mem_levelDeletes (H : τ → Finset ι) (ω : τ → ℕ) (G : Finset ι) (k : ℕ)
    (e : ι) : e ∈ levelDeletes H ω G k ↔ ∃ T, ω T = k ∧ H T ⊆ G ∧ e ∈ H T := by
  simp only [levelDeletes, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
    true_and]
  aesop

end TimeScan
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Coupling_HyperScanAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators
open scoped BigOperators ENNReal Classical

namespace SharpTerminalLeave
section GenericClockScan
variable {ι τ : Type*} [DecidableEq ι] [Fintype τ] [DecidableEq τ]

def hyperScanAction (H : τ → Finset ι) (G : Finset ι) (T : τ) : Finset ι :=
  if H T ⊆ G then G \ H T else G

def hyperScan (H : τ → Finset ι) (G : Finset ι) (as : List τ) : Finset ι :=
  as.foldl (hyperScanAction H) G

omit [Fintype τ] [DecidableEq τ] in
@[simp] theorem hyperScan_singleton (H : τ → Finset ι) (G : Finset ι) (T : τ) :
    hyperScan H G [T] = hyperScanAction H G T := rfl

end GenericClockScan
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Coupling_OrderEmbRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

lemma orderEmb_rank {N : ℕ} (s : Finset (Fin N)) (i : Fin s.card) :
    (s.filter (fun x => x < s.orderEmbOfFin rfl i)).card = i.val := by
  have he : s.filter (fun x => x < s.orderEmbOfFin rfl i) =
      (Finset.Iio i).image (s.orderEmbOfFin rfl) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_image,Finset.mem_Iio]
    constructor
    · rintro ⟨hx,hxi⟩
      obtain ⟨j,hj⟩ := (s.orderIsoOfFin rfl).surjective ⟨x,hx⟩
      have he : s.orderEmbOfFin rfl j = x := congrArg Subtype.val hj
      exact ⟨j,(s.orderEmbOfFin rfl).lt_iff_lt.mp (he ▸ hxi),he⟩
    · rintro ⟨j,hji,rfl⟩
      exact ⟨s.orderEmbOfFin_mem rfl j,(s.orderEmbOfFin rfl).strictMono hji⟩
  rw [he,Finset.card_image_of_injective _ (s.orderEmbOfFin rfl).injective,Fin.card_Iio]

lemma initial_rank {N R : ℕ} (s : Finset (Fin N))
    (hroot : ∀ x : Fin N, x.val < R → x ∈ s) (x : Fin N) (hx : x.val < R) :
    ((s.orderIsoOfFin rfl).symm ⟨x,hroot x hx⟩).val = x.val := by
  let i := (s.orderIsoOfFin rfl).symm ⟨x,hroot x hx⟩
  have he : s.orderEmbOfFin rfl i = x :=
    congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨x,hroot x hx⟩)
  have hr := orderEmb_rank s i
  rw [he] at hr
  have hf : s.filter (fun z => z < x) = Finset.univ.filter (fun z : Fin N => z.val < x.val) := by
    ext z
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨fun h => h.2,fun h => ⟨hroot z (h.trans hx),h⟩⟩
  rw [hf,Fin.card_filter_val_lt,Nat.min_eq_right x.isLt.le] at hr
  exact hr.symm

lemma orderEmb_nonroot {N R : ℕ} (s : Finset (Fin N))
    (hroot : ∀ x : Fin N, x.val < R → x ∈ s)
    (i : Fin s.card) (hi : R ≤ i.val) : R ≤ (s.orderEmbOfFin rfl i).val := by
  by_contra hn
  have hx : (s.orderEmbOfFin rfl i).val < R := Nat.lt_of_not_ge hn
  have hr := initial_rank s hroot (s.orderEmbOfFin rfl i) hx
  have he : (s.orderIsoOfFin rfl).symm
      ⟨s.orderEmbOfFin rfl i,hroot (s.orderEmbOfFin rfl i) hx⟩ = i := by
    apply (s.orderIsoOfFin rfl).injective
    simpa only [OrderIso.apply_symm_apply] using (show
      (⟨s.orderEmbOfFin rfl i,hroot (s.orderEmbOfFin rfl i) hx⟩ : s) = s.orderIsoOfFin rfl i from rfl)
  rw [he] at hr
  omega

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Coupling_OrderedSuffix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

def orderedSuffix {N : ℕ} (S : Finset (Fin N)) (R : ℕ) : Finset (Fin N) :=
  S.filter (fun x => R ≤ x.val)

lemma prefix_suffix_card {N R : ℕ} (S : Finset (Fin N)) (hR : R ≤ N)
    (hroot : ∀ x : Fin N, x.val < R → x ∈ S) :
    S.card = R + (orderedSuffix S R).card := by
  have he : S.filter (fun x => x.val < R) = Finset.univ.filter (fun x => x.val < R) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨And.right,fun hx => ⟨hroot x hx,hx⟩⟩
  have hh := Finset.card_filter_add_card_filter_not (s := S) (fun x => x.val < R)
  rw [he,Fin.card_filter_val_lt,Nat.min_eq_right hR] at hh
  simpa only [orderedSuffix,Nat.not_lt] using hh.symm

lemma suffix_full_rank {N R : ℕ} (S : Finset (Fin N)) (hR : R ≤ N)
    (hroot : ∀ x : Fin N, x.val < R → x ∈ S)
    (i : Fin (orderedSuffix S R).card) :
    ((S.orderIsoOfFin rfl).symm
      ⟨(orderedSuffix S R).orderEmbOfFin rfl i,
        (Finset.mem_filter.mp ((orderedSuffix S R).orderEmbOfFin_mem rfl i)).1⟩).val = R+i.val := by
  let T := orderedSuffix S R
  let v := T.orderEmbOfFin rfl i
  have hvT : v ∈ T := T.orderEmbOfFin_mem rfl i
  have hvR : R ≤ v.val := (Finset.mem_filter.mp hvT).2
  have hvS : v ∈ S := (Finset.mem_filter.mp hvT).1
  let j := (S.orderIsoOfFin rfl).symm ⟨v,hvS⟩
  have hj : S.orderEmbOfFin rfl j = v :=
    congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply _)
  have hr := orderEmb_rank S j
  rw [hj] at hr
  have he : (S.filter (fun x => x < v)).filter (fun x => x.val < R) =
      Finset.univ.filter (fun x => x.val < R) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · exact And.right
    · intro hx
      exact ⟨⟨hroot x hx,(show x.val < v.val from lt_of_lt_of_le hx hvR)⟩,hx⟩
  have hn : (S.filter (fun x => x < v)).filter (fun x => ¬ x.val < R) =
      T.filter (fun x => x < v) := by
    ext x
    simp only [T,orderedSuffix,Finset.mem_filter,Nat.not_lt]
    exact ⟨fun h => ⟨⟨h.1.1,h.2⟩,h.1.2⟩,fun h => ⟨⟨h.1.1,h.2⟩,h.1.2⟩⟩
  have hh := Finset.card_filter_add_card_filter_not
    (s := S.filter (fun x => x < v)) (fun x => x.val < R)
  rw [he,hn,Fin.card_filter_val_lt,Nat.min_eq_right hR,hr] at hh
  have ht := orderEmb_rank T i
  change (T.filter (fun x => x < v)).card = i.val at ht
  rw [ht] at hh
  exact hh.symm

def suffixFullIndex {N R : ℕ} (S : Finset (Fin N)) (hR : R ≤ N)
    (hroot : ∀ x : Fin N, x.val < R → x ∈ S)
    (i : Fin (orderedSuffix S R).card) : Fin S.card :=
  ⟨R+i.val,by rw [prefix_suffix_card S hR hroot]; omega⟩

lemma suffix_full_embedding {N R : ℕ} (S : Finset (Fin N)) (hR : R ≤ N)
    (hroot : ∀ x : Fin N, x.val < R → x ∈ S)
    (i : Fin (orderedSuffix S R).card) :
    S.orderEmbOfFin rfl (suffixFullIndex S hR hroot i) =
      (orderedSuffix S R).orderEmbOfFin rfl i := by
  have hh := suffix_full_rank S hR hroot i
  have he : (S.orderIsoOfFin rfl).symm
      ⟨(orderedSuffix S R).orderEmbOfFin rfl i,
        (Finset.mem_filter.mp ((orderedSuffix S R).orderEmbOfFin_mem rfl i)).1⟩ =
      suffixFullIndex S hR hroot i := Fin.ext hh
  rw [← he]
  exact congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply _)

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_Finish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators
open scoped BigOperators ENNReal Classical

namespace SharpTerminalLeave

noncomputable def finish {n : ℕ} (G : Graph n) : PMF (Graph n) :=
  evolve G G.card

def scanAction {n : ℕ} (G : Graph n) (t : Finset (Fin n)) : Graph n :=
  if t ∈ triangles G then G \ t.powersetCard 2 else G

noncomputable def scanLaw {n : ℕ} : ℕ → Graph n → Finset (Finset (Fin n)) → PMF (Graph n)
  | 0, G, _ => PMF.pure G
  | k + 1, G, C =>
      if h : C.Nonempty then
        (PMF.uniformOfFinset C h).bind (fun t => scanLaw k (scanAction G t) (C.erase t))
      else PMF.pure G

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Coupling_ScanList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators
open scoped BigOperators ENNReal Classical

namespace SharpTerminalLeave

def scanList {n : ℕ} (G : Graph n) (as : List (Finset (Fin n))) : Graph n :=
  as.foldl scanAction G

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_BirthGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

structure BirthGraph (N : ℕ) where
  older : Fin N → Finset (Fin N)
  older_lt : ∀ v, ∀ u ∈ older v, u < v
  older_card : ∀ v, (older v).card ≤ 2

namespace BirthGraph
variable {N : ℕ} (B : BirthGraph N)

def graph : SimpleGraph (Fin N) where
  Adj u v := u ∈ B.older v ∨ v ∈ B.older u
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun v h => by
    rcases h with h | h <;> exact (lt_irrefl v) (B.older_lt v v h)⟩

@[simp] theorem graph_adj (u v : Fin N) :
    B.graph.Adj u v ↔ u ∈ B.older v ∨ v ∈ B.older u := Iff.rfl

def parentVertices (v : Fin N) : Finset (Fin N) := insert v (B.older v)

@[simp] theorem self_not_mem_older (v : Fin N) : v ∉ B.older v := by
  intro hv
  exact (lt_irrefl v) (B.older_lt v v hv)

theorem older_eq_pair {a b v : Fin N} (hab : a ≠ b)
    (ha : a ∈ B.older v) (hb : b ∈ B.older v) : B.older v = {a, b} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro ha hb
  · simpa only [Finset.card_pair hab] using B.older_card v

section Labels
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) (label : Fin N → V)

def parentType (v : Fin N) : Finset V := (B.parentVertices v).image label

def IsTriangle (T : Finset V) : Prop :=
  T.card = 3 ∧ ∀ x ∈ T, ∀ y ∈ T, x ≠ y → G.Adj x y

def ExposedAt (v : Fin N) (T : Finset V) : Prop :=
  IsTriangle G T ∧
  (∃ u ∈ B.older v, label u ∈ T ∧ label v ∈ T) ∧
  ((B.older v).card = 2 → T ≠ B.parentType label v)

def ExtraEdge (a b : Fin N) : Prop :=
  a ≠ b ∧ ¬ B.graph.Adj a b ∧ G.Adj (label a) (label b)

structure SpawnRules : Prop where
  edge_labels : ∀ a b, B.graph.Adj a b → G.Adj (label a) (label b)
  attachment : ∀ v, (B.older v).card = 2 →
    ∀ a ∈ B.older v, ∀ b ∈ B.older v, a ≠ b → B.graph.Adj a b
  omit_parent : ∀ v p, p ∈ B.older v → (∀ a ∈ B.older v, a ≤ p) →
    (B.older p).card = 2 → B.parentType label v ≠ B.parentType label p
  distinct_siblings : ∀ v w, (B.older v).card = 2 → B.older v = B.older w →
    label v = label w → v = w

end Labels
end BirthGraph
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_OverlapVertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Classical

namespace SharpTerminalLeave

def overlapVertices {k n : ℕ} (W : Finset (Fin n)) (φ : Fin k ↪ Fin n) : Finset (Fin k) :=
  Finset.univ.filter (fun v => φ v ∈ W)

@[simp] lemma mem_overlapVertices {k n : ℕ} (W : Finset (Fin n)) (φ : Fin k ↪ Fin n) (v : Fin k) :
    v ∈ overlapVertices W φ ↔ φ v ∈ W := by simp [overlapVertices]

def copyUnionSum {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) : ℕ → (Graph n → ℝ) → Graph n → ℝ
  | 0,f,F => f F
  | q+1,f,F => ∑ a, copyUnionSum required q f (F ∪ required a)

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixEdgeRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter
open Classical

namespace SharpTerminalLeave

noncomputable def prefixEdgeRadius (n : ℕ) : ℝ := (n : ℝ)^(-1/40000 : ℝ)

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_RootedTemplateEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

def rootedTemplateEncoding {k : ℕ} (T : RootedTemplate k) :
    Graph k × Finset (Fin k) := (T.edges,T.roots)

lemma rootedTemplateEncoding_injective (k : ℕ) :
    Function.Injective (rootedTemplateEncoding (k := k)) := by
  intro T U h
  cases T
  cases U
  cases h
  rfl

noncomputable instance rootedTemplateFintype (k : ℕ) : Fintype (RootedTemplate k) :=
  Fintype.ofInjective rootedTemplateEncoding (rootedTemplateEncoding_injective k)

abbrev RootedCountIndex (H n : ℕ) :=
  Σ k : Fin (H+1), Σ T : RootedTemplate k.val, ({v // v ∈ T.roots} ↪ Fin n)

noncomputable def rootedFamilySize (H : ℕ) : ℕ :=
  ∑ k : Fin (H+1), Fintype.card (RootedTemplate k.val)

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_RootedInjectionEquivFree
attribute [-instance] _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

noncomputable def rootedInjectionEquivFree {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) :
    RootedInjection T ψ ≃
      ({v : Fin k // v ∉ T.roots} ↪ {w : Fin n // w ∉ Set.range ψ}) := by
  classical
  refine {
    toFun := fun φ => {
      toFun := fun v => ⟨φ.val v,?_⟩
      inj' := ?_ }
    invFun := fun f => ⟨{
      toFun := fun v => if hv : v ∈ T.roots then ψ ⟨v,hv⟩ else f ⟨v,hv⟩
      inj' := ?_ },?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro h
    obtain ⟨a,ha⟩ := h
    rw [← φ.property a] at ha
    have hh : a.val = v.val := φ.val.injective ha
    exact v.property (hh ▸ a.property)
  · intro a b hab
    apply Subtype.ext
    exact φ.val.injective (congrArg Subtype.val hab)
  · intro a b hab
    dsimp at hab
    split_ifs at hab with ha hb hb
    · exact congrArg Subtype.val (ψ.injective hab)
    · exact ((f ⟨b,hb⟩).property ⟨⟨a,ha⟩,hab⟩).elim
    · exact ((f ⟨a,ha⟩).property ⟨⟨b,hb⟩,hab.symm⟩).elim
    · exact congrArg Subtype.val (f.injective (Subtype.ext hab))
  · intro v
    change (if hv : v.val ∈ T.roots then ψ ⟨v.val,hv⟩ else _) = ψ v
    simp only [dite_eq_left v.property]
  · intro φ
    apply Subtype.ext
    apply DFunLike.ext
    intro v
    change (if hv : v ∈ T.roots then ψ ⟨v,hv⟩ else φ.val v) = φ.val v
    split_ifs with hv
    · exact (φ.property ⟨v,hv⟩).symm
    · rfl
  · intro f
    apply DFunLike.ext
    intro v
    apply Subtype.ext
    change (if hv : v.val ∈ T.roots then ψ ⟨v.val,hv⟩ else (f ⟨v.val,hv⟩).val) = (f v).val
    simp only [dite_eq_right v.property]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_RootedCompletionMax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

def rootedCompletionMax {k : ℕ} (T : RootedTemplate k) (n : ℕ) (p : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun J : Finset (Fin k) =>
    if T.roots ⊆ J then (n : ℝ)^(k-J.card)*p^(T.edges.card-(T.edges.filter (· ⊆ J)).card) else 1)

noncomputable def rootedMomentOrder (n : ℕ) : ℕ := ⌊(1+Real.log (n : ℝ))^2⌋₊

def PrefixRootedUpper (H n : ℕ) (ω : History (Graph n) (prefixTime n)) : Prop :=
  ∀ j ≤ prefixTime n,
    historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n))
      (prefixTime n) j ω →
    ∀ k ≤ H, ∀ T : RootedTemplate k, ∀ ψ : {v // v ∈ T.roots} ↪ Fin n,
      rootedCount T ψ (ω (historyIndex (prefixTime n) j)) <
        (1+Real.log (n : ℝ))^(3*H+2)*rootedCompletionMax T n (earlyDensity n j)

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_RerootTemplate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Classical Filter

namespace SharpTerminalLeave

def rerootTemplate {k : ℕ} (T : RootedTemplate k) (J : Finset (Fin k)) : RootedTemplate k where
  edges := T.edges.filter (fun e => ¬ e ⊆ J)
  roots := J
  simple := fun e he => T.simple e (Finset.mem_filter.mp he).1
  independent := fun _e he => (Finset.mem_filter.mp he).2

def RootedTwoBalanced {k : ℕ} (T : RootedTemplate k) : Prop :=
  ∀ J : Finset (Fin k), T.roots ⊆ J →
    (T.edges.filter (· ⊆ J)).card ≤ 2*(J.card-T.roots.card)

abbrev RootedEdgePin {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) (f : Finset (Fin k)) (e : Finset (Fin n)) :=
  {ξ : {v // v ∈ T.roots ∪ f} ↪ Fin n //
    (∀ r : {v // v ∈ T.roots}, ξ ⟨r.val,Finset.mem_union_left _ r.property⟩ = ψ r) ∧
    ∀ v : {v // v ∈ f}, ξ ⟨v.val,Finset.mem_union_right _ v.property⟩ ∈ e}

def rootedEdgeFiberEncoding {k n : ℕ} (T : RootedTemplate k)
    (ψ : {v // v ∈ T.roots} ↪ Fin n) (f : Finset (Fin k)) (e : Finset (Fin n))
    (φ : {φ : RootedInjection T ψ // f.map φ.val = e}) :
    Σ ξ : RootedEdgePin T ψ f e, RootedInjection (rerootTemplate T (T.roots ∪ f)) ξ.val := by
  let ξ : {v // v ∈ T.roots ∪ f} ↪ Fin n :=
    ⟨fun v => φ.val.val v,fun _ _ h => Subtype.ext (φ.val.val.injective h)⟩
  have hξ : (∀ r : {v // v ∈ T.roots}, ξ ⟨r.val,Finset.mem_union_left _ r.property⟩ = ψ r) ∧
      ∀ v : {v // v ∈ f}, ξ ⟨v.val,Finset.mem_union_right _ v.property⟩ ∈ e := by
    refine ⟨fun r => φ.val.property r,?_⟩
    intro v
    rw [← φ.property]
    exact Finset.mem_map.mpr ⟨v.val,v.property,rfl⟩
  exact ⟨⟨ξ,hξ⟩,φ.val.val,fun _ => rfl⟩

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_DegreeTemplate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

def degreeTemplate : RootedTemplate 2 where
  edges := {{0,1}}
  roots := {0}
  simple := by decide
  independent := by decide

def degreeRoot {n : ℕ} (u : Fin n) : {v // v ∈ degreeTemplate.roots} ↪ Fin n where
  toFun := fun _ => u
  inj' := by
    intro a b _
    apply Subtype.ext
    exact (Finset.mem_singleton.mp a.property).trans (Finset.mem_singleton.mp b.property).symm

@[simp] theorem degree_rootedScaling (n : ℕ) (p : ℝ) :
    rootedScaling degreeTemplate n p = (n : ℝ)*p := by
  simp [rootedScaling,degreeTemplate]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_TriangleGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

structure TriangleGrowth {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (N R : ℕ) where
  label : Fin N → V
  seed : BirthGraph N
  seed_small : ∀ v, v.val < R → (seed.older v).card ≤ 1
  seed_root : ∀ v, ∀ u ∈ seed.older v, v.val < R → u.val < R
  seed_labels : ∀ v, v.val < R → ∀ u ∈ seed.older v, G.Adj (label u) (label v)
  roots_injective : Set.InjOn label {v | v.val < R}
  attach : Fin N → Finset V
  parent : Fin N → Option (Fin N)
  parent_lt : ∀ v p, R ≤ v.val → parent v = some p → p < v
  parent_nonroot : ∀ v p, R ≤ v.val → parent v = some p → R ≤ p.val
  attach_card : ∀ v, R ≤ v.val → (attach v).card = 2
  new_label : ∀ v, R ≤ v.val → label v ∉ attach v
  triangle : ∀ v, R ≤ v.val → BirthGraph.IsTriangle G (insert (label v) (attach v))
  root_attach : ∀ v, R ≤ v.val → parent v = none →
    ∃ x y : Fin N, x.val < R ∧ y.val < R ∧ seed.graph.Adj x y ∧
      attach v = {label x, label y}
  child_attach : ∀ v p, R ≤ v.val → parent v = some p →
    attach v ⊆ insert (label p) (attach p) ∧ attach v ≠ attach p
  omission : ∀ v p, R ≤ v.val → parent v = some p →
    insert (label v) (attach v) ≠ insert (label p) (attach p)
  distinct_children : ∀ v w, R ≤ v.val → R ≤ w.val → parent v = parent w →
    attach v = attach w → label v = label w → v = w

namespace TriangleGrowth
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {N R : ℕ}
variable (A : TriangleGrowth G N R)

noncomputable def roots (_A : TriangleGrowth G N R) : Finset (Fin N) := Finset.univ.filter (fun v => v.val < R)

@[simp] theorem mem_roots (v : Fin N) : v ∈ A.roots ↔ v.val < R := by
  simp [roots]

noncomputable def older (A : TriangleGrowth G N R) (v : Fin N) : Finset (Fin N) :=
  if _hv : R ≤ v.val then
    match _hp : A.parent v with
    | none => A.roots.filter (fun x => A.label x ∈ A.attach v)
    | some p => (insert p (A.older p)).filter (fun x => A.label x ∈ A.attach v)
  else A.seed.older v
termination_by v.val
decreasing_by exact A.parent_lt v p _hv _hp

lemma lifted_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (s : Finset α) (t : Finset β)
    (ht : t ⊆ s.image f) : (s.filter (fun x => f x ∈ t)).image f = t := by
  ext y
  constructor
  · rintro h
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp h
    exact (Finset.mem_filter.mp hx).2
  · intro hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp (ht hy)
    exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,hy⟩,rfl⟩

lemma lifted_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (s : Finset α) (t : Finset β)
    (hi : Set.InjOn f s) (ht : t ⊆ s.image f) :
    (s.filter (fun x => f x ∈ t)).card = t.card := by
  have hi' : Set.InjOn f (s.filter (fun x => f x ∈ t)) :=
    hi.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1)
  have hc : ((s.filter (fun x => f x ∈ t)).image f).card =
      (s.filter (fun x => f x ∈ t)).card := Finset.card_image_iff.mpr hi'
  rw [lifted_image f s t ht] at hc
  exact hc.symm

theorem older_invariants (v : Fin N) :
    (∀ x ∈ A.older v, x < v) ∧
    (R ≤ v.val → (A.older v).card = 2 ∧ (A.older v).image A.label = A.attach v ∧
      Set.InjOn A.label (insert v (A.older v) : Finset (Fin N))) := by
  induction v using (measure (fun v : Fin N => v.val)).wf.induction with
  | h v ih =>
    by_cases hv : R ≤ v.val
    · have main :
        (∀ x ∈ A.older v, x < v) ∧ (A.older v).card = 2 ∧
        (A.older v).image A.label = A.attach v ∧ Set.InjOn A.label (A.older v) := by
        cases hp : A.parent v with
        | none =>
          obtain ⟨x,y,hx,hy,_,hat⟩ := A.root_attach v hv hp
          have hs : A.attach v ⊆ A.roots.image A.label := by
            rw [hat]
            intro z hz
            simp only [Finset.mem_insert,Finset.mem_singleton] at hz
            rcases hz with rfl | rfl
            · exact Finset.mem_image.mpr ⟨x,A.mem_roots x |>.mpr hx,rfl⟩
            · exact Finset.mem_image.mpr ⟨y,A.mem_roots y |>.mpr hy,rfl⟩
          have hi : Set.InjOn A.label A.roots := by
            intro x hx y hy he
            exact A.roots_injective ((A.mem_roots x).mp hx) ((A.mem_roots y).mp hy) he
          rw [older,dite_eq_left hv,hp]
          refine ⟨?_,?_,lifted_image _ _ _ hs,?_⟩
          · intro z hz
            have hzR := (A.mem_roots z).mp (Finset.mem_filter.mp hz).1
            change z.val < v.val
            exact lt_of_lt_of_le hzR hv
          · rw [lifted_card _ _ _ hi hs,A.attach_card v hv]
          · exact hi.mono (by intro z hz; exact (Finset.mem_filter.mp hz).1)
        | some p =>
          have hpv := A.parent_lt v p hv hp
          have hpR := A.parent_nonroot v p hv hp
          have hind := ih p hpv
          have hpim : (insert p (A.older p)).image A.label =
              insert (A.label p) (A.attach p) := by
            rw [Finset.image_insert,(hind.2 hpR).2.1]
          have hs : A.attach v ⊆ (insert p (A.older p)).image A.label := by
            rw [hpim]
            exact (A.child_attach v p hv hp).1
          have hi := (hind.2 hpR).2.2
          rw [older,dite_eq_left hv,hp]
          refine ⟨?_,?_,lifted_image _ _ _ hs,?_⟩
          · intro z hz
            rcases Finset.mem_insert.mp (Finset.mem_filter.mp hz).1 with rfl | hz
            · exact hpv
            · exact (hind.1 z hz).trans hpv
          · rw [lifted_card _ _ _ hi hs,A.attach_card v hv]
          · exact hi.mono (by intro z hz; exact (Finset.mem_filter.mp hz).1)
      refine ⟨main.1,fun _ => ⟨main.2.1,main.2.2.1,?_⟩⟩
      intro x hx y hy he
      by_cases hxv : x = v <;> by_cases hyv : y = v
      · exact hxv.trans hyv.symm
      · subst x
        have hy' := (Finset.mem_insert.mp hy).resolve_left hyv
        have hm : A.label y ∈ A.attach v := by
          rw [← main.2.2.1]
          exact Finset.mem_image.mpr ⟨y,hy',rfl⟩
        exact False.elim (A.new_label v hv (he.symm ▸ hm))
      · subst y
        have hx' := (Finset.mem_insert.mp hx).resolve_left hxv
        have hm : A.label x ∈ A.attach v := by
          rw [← main.2.2.1]
          exact Finset.mem_image.mpr ⟨x,hx',rfl⟩
        exact False.elim (A.new_label v hv (he ▸ hm))
      · exact main.2.2.2 ((Finset.mem_insert.mp hx).resolve_left hxv)
          ((Finset.mem_insert.mp hy).resolve_left hyv) he
    · rw [older,dite_eq_right hv]
      exact ⟨A.seed.older_lt v,fun h => False.elim (hv h)⟩

noncomputable def birthGraph : BirthGraph N where
  older := A.older
  older_lt := fun v => (A.older_invariants v).1
  older_card := by
    intro v
    by_cases hv : R ≤ v.val
    · exact le_of_eq ((A.older_invariants v).2 hv).1
    · rw [older,dite_eq_right hv]
      exact (A.seed_small v (Nat.lt_of_not_ge hv)).trans (by omega)

@[simp] theorem parentType_eq (v : Fin N) (hv : R ≤ v.val) :
    A.birthGraph.parentType A.label v = insert (A.label v) (A.attach v) := by
  change (insert v (A.older v)).image A.label = _
  rw [Finset.image_insert,((A.older_invariants v).2 hv).2.1]

end TriangleGrowth
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_ReindexSet
attribute [-instance] _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

def reindexSet {N : ℕ} (s e : Finset (Fin N)) : Finset (Fin s.card) :=
  Finset.univ.filter (fun i => s.orderEmbOfFin rfl i ∈ e)

@[simp] lemma mem_reindexSet {N : ℕ} (s e : Finset (Fin N)) (i : Fin s.card) :
    i ∈ reindexSet s e ↔ s.orderEmbOfFin rfl i ∈ e := by
  simp only [reindexSet,Finset.mem_filter,Finset.mem_univ,true_and]

lemma image_reindexSet {N : ℕ} {s e : Finset (Fin N)} (he : e ⊆ s) :
    (reindexSet s e).image (s.orderEmbOfFin rfl) = e := by
  ext x
  constructor
  · rintro h
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
    exact (mem_reindexSet s e i).mp hi
  · intro hx
    let i := (s.orderIsoOfFin rfl).symm ⟨x,he hx⟩
    have hi : s.orderEmbOfFin rfl i = x :=
      congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨x,he hx⟩)
    exact Finset.mem_image.mpr ⟨i,(mem_reindexSet s e i).mpr (by rwa [hi]),hi⟩

lemma reindexSet_card {N : ℕ} {s e : Finset (Fin N)} (he : e ⊆ s) :
    (reindexSet s e).card = e.card := by
  have hc := Finset.card_image_of_injective (reindexSet s e) (s.orderEmbOfFin rfl).injective
  rw [image_reindexSet he] at hc
  exact hc.symm

lemma reindexSet_subset_iff {N : ℕ} {s e f : Finset (Fin N)} (he : e ⊆ s) :
    reindexSet s e ⊆ reindexSet s f ↔ e ⊆ f := by
  constructor
  · intro h x hx
    rw [← image_reindexSet he] at hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    exact (mem_reindexSet s f i).mp (h hi)
  · intro h i hi
    exact (mem_reindexSet s f i).mpr (h ((mem_reindexSet s e i).mp hi))

def reindexTemplate {N : ℕ} (s : Finset (Fin N)) (E : Graph N) (I : Finset (Fin N))
    (hE : ∀ e ∈ E, e ⊆ s) (hsimple : ∀ e ∈ E, e.card = 2)
    (hind : ∀ e ∈ E, ¬ e ⊆ I) : RootedTemplate s.card where
  edges := E.image (reindexSet s)
  roots := reindexSet s I
  simple := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    rw [reindexSet_card (hE f hf),hsimple f hf]
  independent := by
    intro e he hs
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    exact hind f hf ((reindexSet_subset_iff (hE f hf)).mp hs)

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_ReindexEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

def reindexEmbedding {N n : ℕ} (s : Finset (Fin N)) (φ : Fin N ↪ Fin n) :
    Fin s.card ↪ Fin n := (s.orderEmbOfFin rfl).toEmbedding.trans φ

@[simp] lemma reindexEmbedding_apply {N n : ℕ} (s : Finset (Fin N))
    (φ : Fin N ↪ Fin n) (i : Fin s.card) :
    reindexEmbedding s φ i = φ (s.orderEmbOfFin rfl i) := rfl

def boundaryInjection {N n : ℕ} (s I P : Finset (Fin N)) (hIP : I ⊆ P)
    (ξ : {x // x ∈ P} ↪ Fin n) : {i // i ∈ reindexSet s I} ↪ Fin n where
  toFun i := ξ ⟨s.orderEmbOfFin rfl i, hIP ((mem_reindexSet s I i).mp i.property)⟩
  inj' := by
    intro i j hij
    apply Subtype.ext
    exact (s.orderEmbOfFin rfl).injective
      (congrArg (fun x : {x // x ∈ P} => x.val) (ξ.injective hij))

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_RestrictLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

def restrictLabel {N n : ℕ} (P : Finset (Fin N)) (φ : Fin N ↪ Fin n) :
    {x // x ∈ P} ↪ Fin n := (Function.Embedding.subtype _).trans φ

@[simp] lemma restrictLabel_apply {N n : ℕ} (P : Finset (Fin N))
    (φ : Fin N ↪ Fin n) (x : {x // x ∈ P}) : restrictLabel P φ x = φ x := rfl

noncomputable def graphEmbeddingSet {N n : ℕ} (F : Graph N) (G : Graph n) :
    Finset (Fin N ↪ Fin n) := Finset.univ.filter (fun φ => F.image (fun e => e.map φ) ⊆ G)

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_LookupGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

def lookupGraph {n : ℕ} (G : Graph n) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ {x,y} ∈ G
  symm := ⟨fun x y h => ⟨h.1.symm,by simpa only [Finset.pair_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def initialVertices (N k : ℕ) : Finset (Fin N) := Finset.univ.filter (fun x => x.val < k)

@[simp] lemma mem_initialVertices (N k : ℕ) (x : Fin N) :
    x ∈ initialVertices N k ↔ x.val < k := by simp [initialVertices]

def initialLabel {N n k : ℕ} (hk : k ≤ N) (φ : Fin N ↪ Fin n) : Fin k ↪ Fin n :=
  ⟨fun i => φ (Fin.castLE hk i),φ.injective.comp (Fin.castLE_injective hk)⟩

def initialSubtypeLabel {N n k : ℕ} (ψ : Fin k ↪ Fin n) :
    {x // x ∈ initialVertices N k} ↪ Fin n where
  toFun x := ψ ⟨x.val.val,(mem_initialVertices N k x.val).mp x.property⟩
  inj' := by
    intro x y h
    have he := congrArg Fin.val (ψ.injective h)
    apply Subtype.ext
    exact Fin.ext he

@[simp] lemma initialSubtypeLabel_initialLabel {N n k : ℕ} (hk : k ≤ N)
    (φ : Fin N ↪ Fin n) : initialSubtypeLabel (initialLabel hk φ) =
      restrictLabel (initialVertices N k) φ := by
  ext x
  rfl

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_TriangleHypergraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators
open scoped BigOperators ENNReal Classical

namespace SharpTerminalLeave

def triangleHypergraph {n : ℕ} (G : Graph n) (T : Finset (Fin n)) : Graph n :=
  if T ∈ triangles G then T.powersetCard 2 else ∅

noncomputable def focusSurvival {n : ℕ} (G focus : Graph n) : ℝ :=
  trueProbability ((finish G).map (fun E => decide (focus ⊆ E)))

end SharpTerminalLeave

open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_FreshLogCheckNone3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave.ExposureTree
variable {K V R : Type*}

theorem freshLog_checkNoneTrace_append (ν : K → PMF V)
    (P : List R → Prop) (h0 : P [])
    (happend : ∀ a b, P a → P b → P (a ++ b))
    (as : List (ExposureTree K V (Bool × List R)))
    (ha : ∀ A ∈ as, ∀ z ∈ (freshLog ν A).support, P z.1.2)
    {z : (Bool × List R) × List K}
    (hz : z ∈ (freshLog ν (checkNoneTrace as)).support) : P z.1.2 := by
  induction as generalizing z with
  | nil =>
    have he : z = ((true,[]),[]) := by simpa [checkNoneTrace,freshLog] using hz
    simpa only [he] using h0
  | cons A as ih =>
    rw [checkNoneTrace, freshLog_bind] at hz
    obtain ⟨x,hx,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    have hxa := ha A (by simp) x hx
    have has (B) (hB : B ∈ as) := ha B (by simp [hB])
    cases hb : x.1.1
    · simp only [hb,Bool.false_eq_true,↓reduceIte,freshLog_mapOutput] at hy
      obtain ⟨w,hw,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
      exact happend _ _ hxa (ih has hw)
    · simp only [hb,↓reduceIte,freshLog,PMF.mem_support_pure_iff] at hy
      subst y
      exact hxa

end SharpTerminalLeave.ExposureTree

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_Child
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave
section TraceParents
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

def QueryCall.Child (H : τ → Finset ι) (c a : QueryCall ι τ) : Prop :=
  ∃ p ∈ gridCandidates H c.focus c.parent,
    a = ⟨p :: c.address, (H p.2).erase p.1, some p.2⟩

noncomputable def QueryCall.RootedTrace (H : τ → Finset ι)
    (c : QueryCall ι τ) (cs : List (QueryCall ι τ)) : Prop :=
  c ∈ cs ∧ ∀ a ∈ cs, a = c ∨ ∃ p ∈ cs, p.Child H a

theorem tracedGridQuery_parents (H : τ → Finset ι) (N d k : ℕ) (c : QueryCall ι τ)
    (ν : τ → PMF (Fin N))
    {z : (Bool × List (QueryCall ι τ)) × List τ}
    (hz : z ∈ (ExposureTree.freshLog ν (tracedGridQuery H N d k c)).support) :
    c.RootedTrace H z.1.2 := by
  induction d generalizing k c z with
  | zero =>
    rw [tracedGridQuery,ExposureTree.freshLog_bind] at hz
    obtain ⟨x,_,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    have he : y = ((true,[c]),[]) := by
      simpa [ExposureTree.freshLog] using hy
    subst y
    constructor
    · simp
    · intro a ha
      exact Or.inl (List.mem_singleton.mp ha)
  | succ d ih =>
    rw [tracedGridQuery,ExposureTree.freshLog_bind] at hz
    obtain ⟨x,hx,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    rw [ExposureTree.freshLog_mapOutput] at hy
    obtain ⟨w,hw,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
    have hxv := (ExposureTree.freshLog_exposeLabeled_support ν Prod.snd
      (gridCandidates H c.focus c.parent).toList hx).1
    let P : List (QueryCall ι τ) → Prop := fun cs =>
      ∀ a ∈ cs, ∃ p ∈ c :: cs, p.Child H a
    have h0 : P [] := by intro a ha; simp at ha
    have happend : ∀ a b, P a → P b → P (a ++ b) := by
      intro a b ha hb x hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨p,hp,hpx⟩ := ha x hx
        refine ⟨p,?_,hpx⟩
        rcases List.mem_cons.mp hp with rfl | hp
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ hp)
      · obtain ⟨p,hp,hpx⟩ := hb x hx
        refine ⟨p,?_,hpx⟩
        rcases List.mem_cons.mp hp with rfl | hp
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ hp)
    have hall : P w.1.2 := by
      apply ExposureTree.freshLog_checkNoneTrace_append ν P h0 happend _ ?_ hw
      intro A hA q hq
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hA
      have hp' : p ∈ x.1 := (List.mergeSort_perm _ _).mem_iff.mp hp
      have hcand : p.1 ∈ gridCandidates H c.focus c.parent := by
        have hmem : p.1 ∈ x.1.map Prod.fst := List.mem_map.mpr ⟨p,hp',rfl⟩
        rw [hxv] at hmem
        exact Finset.mem_toList.mp hmem
      split_ifs at hq with hpk
      · have ht := ih p.2.val
          ⟨p.1 :: c.address, (H p.1.2).erase p.1.1, some p.1.2⟩ hq
        intro a ha
        rcases ht.2 a ha with rfl | ⟨b,hb,hba⟩
        · exact ⟨c,by simp, p.1,hcand,rfl⟩
        · exact ⟨b,List.mem_cons_of_mem _ hb,hba⟩
      · have he : q = ((false,[]),[]) := by simpa [ExposureTree.freshLog] using hq
        simpa only [he] using h0
    constructor
    · simp
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact Or.inl rfl
      · exact Or.inr (hall a ha)

end TraceParents
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_FreshLogCheckNone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave.ExposureTree
variable {K V R : Type*}

theorem freshLog_checkNoneTrace_forall (ν : K → PMF V) (P : R → Prop)
    (as : List (ExposureTree K V (Bool × List R)))
    (ha : ∀ A ∈ as, ∀ z ∈ (freshLog ν A).support, ∀ c ∈ z.1.2, P c)
    {z : (Bool × List R) × List K}
    (hz : z ∈ (freshLog ν (checkNoneTrace as)).support) :
    ∀ c ∈ z.1.2, P c := by
  induction as generalizing z with
  | nil =>
    have heq : z = ((true,[]),[]) := by simpa [checkNoneTrace,freshLog] using hz
    simp [heq]
  | cons A as ih =>
    rw [checkNoneTrace, freshLog_bind] at hz
    obtain ⟨x,hx,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    have hxP := ha A (by simp) x hx
    have has (B) (hB : B ∈ as) := ha B (by simp [hB])
    cases hb : x.1.1
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, freshLog_mapOutput] at hy
      obtain ⟨w,hw,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hxP c hc
      · exact ih has hw c hc
    · simp only [hb, ↓reduceIte, freshLog, PMF.mem_support_pure_iff] at hy
      subst y
      exact hxP

end SharpTerminalLeave.ExposureTree

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_FreshLogCheckNone2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave.ExposureTree
variable {K V R : Type*}

theorem freshLog_checkNoneTrace_pairwise (ν : K → PMF V) (rel : R → R → Prop)
    (as : List (ExposureTree K V (Bool × List R)))
    (ha : ∀ A ∈ as, ∀ z ∈ (freshLog ν A).support, z.1.2.Pairwise rel)
    (hab : as.Pairwise (fun A B =>
      ∀ x ∈ (freshLog ν A).support, ∀ y ∈ (freshLog ν B).support,
        ∀ c ∈ x.1.2, ∀ d ∈ y.1.2, rel c d))
    {z : (Bool × List R) × List K}
    (hz : z ∈ (freshLog ν (checkNoneTrace as)).support) :
    z.1.2.Pairwise rel := by
  induction as generalizing z with
  | nil =>
    have heq : z = ((true,[]),[]) := by simpa [checkNoneTrace,freshLog] using hz
    simp [heq]
  | cons A as ih =>
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hab
    rw [checkNoneTrace, freshLog_bind] at hz
    obtain ⟨x,hx,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    have hxR := ha A (by simp) x hx
    have has (B) (hB : B ∈ as) := ha B (by simp [hB])
    cases hb : x.1.1
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, freshLog_mapOutput] at hy
      obtain ⟨w,hw,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
      apply List.pairwise_append.mpr
      refine ⟨hxR, ih has htail hw, ?_⟩
      intro c hc
      exact freshLog_checkNoneTrace_forall ν (rel c) as
        (fun B hB y hy' d hd => hhead B hB x hx y hy' c hc d hd) hw
    · simp only [hb, ↓reduceIte, freshLog, PMF.mem_support_pure_iff] at hy
      subst y
      exact hxR

end SharpTerminalLeave.ExposureTree

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_TracedGridQueryAddress
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave
section TraceAddress
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem tracedGridQuery_address (H : τ → Finset ι) (N d k : ℕ) (c : QueryCall ι τ)
    (ν : τ → PMF (Fin N)) {z : (Bool × List (QueryCall ι τ)) × List τ}
    (hz : z ∈ (ExposureTree.freshLog ν (tracedGridQuery H N d k c)).support) :
    ∀ a ∈ z.1.2, c.address <:+ a.address := by
  induction d generalizing k c z with
  | zero =>
    rw [tracedGridQuery, ExposureTree.freshLog_bind] at hz
    obtain ⟨x,_,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    have heq : y = ((true,[c]),[]) := by simpa [ExposureTree.freshLog] using hy
    simp [heq]
  | succ d ih =>
    rw [tracedGridQuery, ExposureTree.freshLog_bind] at hz
    obtain ⟨x,_,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    rw [ExposureTree.freshLog_mapOutput] at hy
    obtain ⟨w,hw,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
    have hwP := ExposureTree.freshLog_checkNoneTrace_forall ν
      (fun a : QueryCall ι τ => c.address <:+ a.address) _
      (by
        intro A hA a ha
        obtain ⟨p,_,rfl⟩ := List.mem_map.mp hA
        split_ifs at ha with hp
        · intro b hb
          exact (List.suffix_cons p.1 c.address).trans (ih _ _ ha b hb)
        · have heq : a = ((false,[]),[]) := by simpa [ExposureTree.freshLog] using ha
          simp [heq]) hw
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨[],rfl⟩
    · exact hwP a ha

lemma fork_addresses_ne {α : Type*} {p q : α} {base a b : List α} (hpq : p ≠ q)
    (ha : p :: base <:+ a) (hb : q :: base <:+ b) : a ≠ b := by
  intro hab
  subst b
  have hh := List.suffix_of_suffix_length_le ha hb (by simp)
  have heq := hh.eq_of_length (by simp)
  exact hpq (List.cons.inj heq).1

lemma child_address_ne {α : Type*} {p : α} {base a : List α}
    (ha : p :: base <:+ a) : base ≠ a := by
  intro h
  have hh := ha.length_le
  simp only [List.length_cons, ← h] at hh
  omega

theorem tracedGridQuery_address_nodup (H : τ → Finset ι) (N d k : ℕ) (c : QueryCall ι τ)
    (ν : τ → PMF (Fin N)) {z : (Bool × List (QueryCall ι τ)) × List τ}
    (hz : z ∈ (ExposureTree.freshLog ν (tracedGridQuery H N d k c)).support) :
    (z.1.2.map QueryCall.address).Nodup := by
  induction d generalizing k c z with
  | zero =>
    rw [tracedGridQuery, ExposureTree.freshLog_bind] at hz
    obtain ⟨x,_,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    have heq : y = ((true,[c]),[]) := by simpa [ExposureTree.freshLog] using hy
    simp [heq]
  | succ d ih =>
    rw [tracedGridQuery, ExposureTree.freshLog_bind] at hz
    obtain ⟨x,hx,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    rw [ExposureTree.freshLog_mapOutput] at hy
    obtain ⟨w,hw,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
    have hxvals := (ExposureTree.freshLog_exposeLabeled_support ν Prod.snd _ hx).1
    have hnd : (x.1.map Prod.fst).Nodup := by rw [hxvals]; exact Finset.nodup_toList _
    have hsnd := ((List.mergeSort_perm x.1 (fun a b => a.2.val ≤ b.2.val)).map Prod.fst).nodup_iff.mpr hnd
    have hpair : (x.1.mergeSort (fun a b => a.2.val ≤ b.2.val)).Pairwise
        (fun a b => a.1 ≠ b.1) := by
      simpa only [List.Nodup, List.pairwise_map] using hsnd
    have hwR := ExposureTree.freshLog_checkNoneTrace_pairwise ν
      (fun a b : QueryCall ι τ => a.address ≠ b.address) _
      (by
        intro A hA a ha
        obtain ⟨p,_,rfl⟩ := List.mem_map.mp hA
        split_ifs at ha with hp
        · have hh := ih _ _ ha
          simpa only [List.Nodup, List.pairwise_map] using hh
        · have heq : a = ((false,[]),[]) := by simpa [ExposureTree.freshLog] using ha
          simp [heq])
      (by
        apply List.pairwise_map.mpr
        apply hpair.imp
        intro p q hpq x hx y hy a ha b hb
        split_ifs at hx hy with hp hq
        · exact fork_addresses_ne hpq
            (tracedGridQuery_address H N d _ _ ν hx a ha)
            (tracedGridQuery_address H N d _ _ ν hy b hb)
        · have heq : y = ((false,[]),[]) := by simpa [ExposureTree.freshLog] using hy
          simp [heq] at hb
        · have heq : x = ((false,[]),[]) := by simpa [ExposureTree.freshLog] using hx
          simp [heq] at ha
        · have heq : x = ((false,[]),[]) := by simpa [ExposureTree.freshLog] using hx
          simp [heq] at ha) hw
    have hwP := ExposureTree.freshLog_checkNoneTrace_forall ν
      (fun a : QueryCall ι τ => c.address ≠ a.address) _
      (by
        intro A hA a ha
        obtain ⟨p,_,rfl⟩ := List.mem_map.mp hA
        split_ifs at ha with hp
        · intro b hb
          exact child_address_ne (tracedGridQuery_address H N d _ _ ν ha b hb)
        · have heq : a = ((false,[]),[]) := by simpa [ExposureTree.freshLog] using ha
          simp [heq]) hw
    simpa only [List.Nodup, List.map_cons, List.pairwise_cons, List.pairwise_map,
      List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      using (And.intro hwP hwR)

end TraceAddress
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_ForkAddressesNotSuffix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave
section ChronologicalTrace
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

lemma fork_addresses_not_suffix {α : Type*} {p q : α} {base a b : List α}
    (hpq : p ≠ q) (ha : p :: base <:+ a) (hb : q :: base <:+ b) : ¬ b <:+ a := by
  intro hba
  have hh := List.suffix_of_suffix_length_le ha (hb.trans hba) (by simp)
  have heq := hh.eq_of_length (by simp)
  exact hpq (List.cons.inj heq).1

lemma child_address_not_suffix {α : Type*} {p : α} {base a : List α}
    (ha : p :: base <:+ a) : ¬ a <:+ base := by
  intro hab
  have h₁ := ha.length_le
  have h₂ := hab.length_le
  simp only [List.length_cons] at h₁
  omega

theorem tracedGridQuery_no_later_ancestor (H : τ → Finset ι) (N d k : ℕ) (c : QueryCall ι τ)
    (ν : τ → PMF (Fin N)) {z : (Bool × List (QueryCall ι τ)) × List τ}
    (hz : z ∈ (ExposureTree.freshLog ν (tracedGridQuery H N d k c)).support) :
    (z.1.2.Pairwise (fun a b => ¬ b.address <:+ a.address)) := by
  induction d generalizing k c z with
  | zero =>
    rw [tracedGridQuery, ExposureTree.freshLog_bind] at hz
    obtain ⟨x,_,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    have heq : y = ((true,[c]),[]) := by simpa [ExposureTree.freshLog] using hy
    simp [heq]
  | succ d ih =>
    rw [tracedGridQuery, ExposureTree.freshLog_bind] at hz
    obtain ⟨x,hx,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    rw [ExposureTree.freshLog_mapOutput] at hy
    obtain ⟨w,hw,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
    have hxvals := (ExposureTree.freshLog_exposeLabeled_support ν Prod.snd _ hx).1
    have hnd : (x.1.map Prod.fst).Nodup := by rw [hxvals]; exact Finset.nodup_toList _
    have hsnd := ((List.mergeSort_perm x.1 (fun a b => a.2.val ≤ b.2.val)).map Prod.fst).nodup_iff.mpr hnd
    have hpair : (x.1.mergeSort (fun a b => a.2.val ≤ b.2.val)).Pairwise
        (fun a b => a.1 ≠ b.1) := by
      simpa only [List.Nodup, List.pairwise_map] using hsnd
    have hwR := ExposureTree.freshLog_checkNoneTrace_pairwise ν
      (fun a b : QueryCall ι τ => ¬ b.address <:+ a.address) _
      (by
        intro A hA a ha
        obtain ⟨p,_,rfl⟩ := List.mem_map.mp hA
        split_ifs at ha with hp
        · exact ih _ _ ha
        · have heq : a = ((false,[]),[]) := by simpa [ExposureTree.freshLog] using ha
          simp [heq])
      (by
        apply List.pairwise_map.mpr
        apply hpair.imp
        intro p q hpq x hx y hy a ha b hb
        split_ifs at hx hy with hp hq
        · exact fork_addresses_not_suffix hpq
            (tracedGridQuery_address H N d _ _ ν hx a ha)
            (tracedGridQuery_address H N d _ _ ν hy b hb)
        · have heq : y = ((false,[]),[]) := by simpa [ExposureTree.freshLog] using hy
          simp [heq] at hb
        · have heq : x = ((false,[]),[]) := by simpa [ExposureTree.freshLog] using hx
          simp [heq] at ha
        · have heq : x = ((false,[]),[]) := by simpa [ExposureTree.freshLog] using hx
          simp [heq] at ha) hw
    have hwP := ExposureTree.freshLog_checkNoneTrace_forall ν
      (fun a : QueryCall ι τ => ¬ a.address <:+ c.address) _
      (by
        intro A hA a ha
        obtain ⟨p,_,rfl⟩ := List.mem_map.mp hA
        split_ifs at ha with hp
        · intro b hb
          exact child_address_not_suffix (tracedGridQuery_address H N d _ _ ν ha b hb)
        · have heq : a = ((false,[]),[]) := by simpa [ExposureTree.freshLog] using ha
          simp [heq]) hw
    exact List.pairwise_cons.mpr ⟨hwP,hwR⟩

theorem tracedGridQuery_parent_before (H : τ → Finset ι) (N d k : ℕ)
    (c : QueryCall ι τ) (ν : τ → PMF (Fin N))
    {z : (Bool × List (QueryCall ι τ)) × List τ}
    (hz : z ∈ (ExposureTree.freshLog ν (tracedGridQuery H N d k c)).support)
    (i j : Fin z.1.2.length) (h : (z.1.2.get j).Child H (z.1.2.get i)) : j < i := by
  have ho := tracedGridQuery_no_later_ancestor H N d k c ν hz
  obtain ⟨p,_,he⟩ := h
  have hs : (z.1.2.get j).address <:+ (z.1.2.get i).address := by
    rw [he]
    exact List.suffix_cons _ _
  rcases lt_trichotomy j i with hlt | rfl | hgt
  · exact hlt
  · have hlen := congrArg (fun a => a.address.length) he
    simp only [List.length_cons] at hlen
    omega
  · exact False.elim ((List.pairwise_iff_get.mp ho i j hgt) hs)

end ChronologicalTrace
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_RecordedCallForest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

structure RecordedCallForest {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]
    (H : τ → Finset ι) (c : QueryCall ι τ) where
  size : ℕ
  call : Fin size → QueryCall ι τ
  root : Fin size
  root_eq : call root = c
  address_injective : Function.Injective (fun i => (call i).address)
  parent : (i : Fin size) → i ≠ root → Fin size
  is_child : ∀ i h, (call (parent i h)).Child H (call i)
  parent_lt : ∀ i h, parent i h < i

namespace RecordedCallForest
section General
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]
variable {H : τ → Finset ι} {c : QueryCall ι τ} (F : RecordedCallForest H c)

theorem root_le (i : Fin F.size) : F.root ≤ i := by
  induction i using (measure (fun i : Fin F.size => i.val)).wf.induction with
  | h i ih =>
    by_cases hi : i = F.root
    · exact le_of_eq hi.symm
    · exact (ih (F.parent i hi) (F.parent_lt i hi)).trans (le_of_lt (F.parent_lt i hi))

theorem root_val : F.root.val = 0 := by
  by_contra hn
  have hs : 0 < F.size := lt_of_le_of_lt (Nat.zero_le _) F.root.isLt
  have hl := F.root_le ⟨0,hs⟩
  exact hn (Nat.eq_zero_of_le_zero hl)

end General
end RecordedCallForest

section ExtractForest
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

noncomputable def extractCallForest (H : τ → Finset ι) (N d k : ℕ) (c : QueryCall ι τ)
    (ν : τ → PMF (Fin N))
    (z : (Bool × List (QueryCall ι τ)) × List τ)
    (hz : z ∈ (ExposureTree.freshLog ν (tracedGridQuery H N d k c)).support) :
    RecordedCallForest H c := by
  classical
  have ht := tracedGridQuery_parents H N d k c ν hz
  have hnd := tracedGridQuery_address_nodup H N d k c ν hz
  let r := (List.mem_iff_get.mp ht.1).choose
  have hr : z.1.2.get r = c := (List.mem_iff_get.mp ht.1).choose_spec
  have hinj : Function.Injective (fun i : Fin z.1.2.length => (z.1.2.get i).address) := by
    intro i j he
    have hp : z.1.2.Pairwise (fun a b => a.address ≠ b.address) := by
      simpa only [List.Nodup,List.pairwise_map] using hnd
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (List.pairwise_iff_get.mp hp i j hlt) he
    · exact (List.pairwise_iff_get.mp hp j i hgt) he.symm
  have hp (i : Fin z.1.2.length) (hi : i ≠ r) :
      ∃ p : Fin z.1.2.length, (z.1.2.get p).Child H (z.1.2.get i) := by
    rcases ht.2 _ (List.get_mem _ _) with he | ⟨p,hp,hpc⟩
    · have hh : i = r := hinj (congrArg QueryCall.address (he.trans hr.symm))
      exact False.elim (hi hh)
    · obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hp
      exact ⟨j,hpc⟩
  exact ⟨z.1.2.length,z.1.2.get,r,hr,hinj,
    fun i hi => (hp i hi).choose, fun i hi => (hp i hi).choose_spec,
    fun i hi => tracedGridQuery_parent_before H N d k c ν hz i _ (hp i hi).choose_spec⟩

end ExtractForest
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_TriangleThird
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma graphCandidate_iff {n : ℕ} (G : Graph n) (focus : Graph n)
    (parent : Option (Finset (Fin n))) (p : Finset (Fin n) × Finset (Fin n)) :
    p ∈ gridCandidates (triangleHypergraph G) focus parent ↔
      p.1 ∈ focus ∧ p.2 ∈ triangles G ∧ p.1 ∈ p.2.powersetCard 2 ∧ some p.2 ≠ parent := by
  rcases p with ⟨e,T⟩
  simp only [gridCandidates,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_univ,and_true]
  by_cases ht : T ∈ triangles G
  · simp only [triangleHypergraph,ht,↓reduceIte,true_and]
  · simp only [triangleHypergraph,ht,↓reduceIte,Finset.notMem_empty,false_and,and_false]

lemma triangle_third_exists {α : Type*} [DecidableEq α] {T e : Finset α}
    (hT : T.card = 3) (he : e ∈ T.powersetCard 2) :
    ∃ x, x ∉ e ∧ T = insert x e := by
  obtain ⟨heT,hce⟩ := Finset.mem_powersetCard.mp he
  have hdiff : (T \ e).card = 1 := by
    rw [Finset.card_sdiff,Finset.inter_eq_left.mpr heT,hT,hce]
  obtain ⟨x,hx⟩ := Finset.card_eq_one.mp hdiff
  have hxm : x ∈ T \ e := by rw [hx]; simp
  refine ⟨x,(Finset.mem_sdiff.mp hxm).2,?_⟩
  have hh := Finset.sdiff_union_of_subset heT
  rw [hx,Finset.singleton_union] at hh
  exact hh.symm

noncomputable def triangleThird {α : Type*} [DecidableEq α] (T e : Finset α)
    (hT : T.card = 3) (he : e ∈ T.powersetCard 2) : α :=
  (triangle_third_exists hT he).choose

lemma triangleThird_spec {α : Type*} [DecidableEq α] (T e : Finset α)
    (hT : T.card = 3) (he : e ∈ T.powersetCard 2) :
    triangleThird T e hT he ∉ e ∧ T = insert (triangleThird T e hT he) e :=
  (triangle_third_exists hT he).choose_spec

namespace RecordedCallForest
section Incoming
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]
variable {H : τ → Finset ι} {c : QueryCall ι τ} (F : RecordedCallForest H c)

noncomputable def incoming (i : Fin F.size) (hi : i ≠ F.root) : ι × τ :=
  (F.is_child i hi).choose

theorem incoming_spec (i : Fin F.size) (hi : i ≠ F.root) :
    F.incoming i hi ∈ gridCandidates H (F.call (F.parent i hi)).focus
      (F.call (F.parent i hi)).parent ∧
    F.call i = ⟨F.incoming i hi :: (F.call (F.parent i hi)).address,
      (H (F.incoming i hi).2).erase (F.incoming i hi).1,some (F.incoming i hi).2⟩ :=
  (F.is_child i hi).choose_spec

theorem incoming_unique (i j : Fin F.size) (hi : i ≠ F.root) (hj : j ≠ F.root)
    (hp : F.parent i hi = F.parent j hj) (he : F.incoming i hi = F.incoming j hj) : i = j := by
  apply F.address_injective
  change (F.call i).address = (F.call j).address
  rw [(F.incoming_spec i hi).2,(F.incoming_spec j hj).2]
  simp only [hp,he]

end Incoming

section GraphIncoming
variable {n : ℕ} {G : Graph n} {c : QueryCall (Finset (Fin n)) (Finset (Fin n))}
variable (F : RecordedCallForest (triangleHypergraph G) c)

lemma incoming_graph (i : Fin F.size) (hi : i ≠ F.root) :
    (F.incoming i hi).1 ∈ (F.call (F.parent i hi)).focus ∧
    (F.incoming i hi).2 ∈ triangles G ∧
    (F.incoming i hi).1 ∈ (F.incoming i hi).2.powersetCard 2 ∧
    some (F.incoming i hi).2 ≠ (F.call (F.parent i hi)).parent :=
  (graphCandidate_iff G _ _ _).mp (F.incoming_spec i hi).1

noncomputable def newVertex (i : Fin F.size) (hi : i ≠ F.root) : Fin n :=
  triangleThird (F.incoming i hi).2 (F.incoming i hi).1
    (mem_triangles.mp (F.incoming_graph i hi).2.1).1 (F.incoming_graph i hi).2.2.1

lemma newVertex_spec (i : Fin F.size) (hi : i ≠ F.root) :
    F.newVertex i hi ∉ (F.incoming i hi).1 ∧
    (F.incoming i hi).2 = insert (F.newVertex i hi) (F.incoming i hi).1 :=
  triangleThird_spec _ _ _ _

lemma incoming_card (i : Fin F.size) (hi : i ≠ F.root) :
    (F.incoming i hi).1.card = 2 :=
  (Finset.mem_powersetCard.mp (F.incoming_graph i hi).2.2.1).2

lemma incoming_parent (i : Fin F.size) (hi : i ≠ F.root) :
    (F.call i).parent = some (F.incoming i hi).2 := by
  rw [(F.incoming_spec i hi).2]

lemma incoming_focus (i : Fin F.size) (hi : i ≠ F.root) :
    (F.call i).focus = ((F.incoming i hi).2.powersetCard 2).erase (F.incoming i hi).1 := by
  rw [(F.incoming_spec i hi).2]
  simp only [triangleHypergraph,(F.incoming_graph i hi).2.1,↓reduceIte]

lemma incoming_of_nonroot_parent (i : Fin F.size) (hi : i ≠ F.root)
    (hp : F.parent i hi ≠ F.root) :
    (F.incoming i hi).1 ⊆ insert (F.newVertex (F.parent i hi) hp)
      (F.incoming (F.parent i hi) hp).1 ∧
    (F.incoming i hi).1 ≠ (F.incoming (F.parent i hi) hp).1 ∧
    (F.incoming i hi).2 ≠ (F.incoming (F.parent i hi) hp).2 := by
  have hc := F.incoming_graph i hi
  rw [F.incoming_focus _ hp] at hc
  obtain ⟨hediff,hepow⟩ := Finset.mem_erase.mp hc.1
  refine ⟨?_,hediff,?_⟩
  · rw [← (F.newVertex_spec _ hp).2]
    exact (Finset.mem_powersetCard.mp hepow).1
  · rw [F.incoming_parent _ hp] at hc
    exact fun he => hc.2.2.2 (congrArg some he)

end GraphIncoming
end RecordedCallForest
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_RootSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave.RecordedCallForest
variable {n : ℕ} {G : Graph n} {c : QueryCall (Finset (Fin n)) (Finset (Fin n))}
variable (F : RecordedCallForest (triangleHypergraph G) c)

def rootSet (_F : RecordedCallForest (triangleHypergraph G) c) : Finset (Fin n) := c.focus.biUnion id

def rootCount : ℕ := F.rootSet.card

def vertexCount : ℕ := F.rootCount + (F.size - 1)

lemma size_pos : 0 < F.size := lt_of_le_of_lt (Nat.zero_le _) F.root.isLt

lemma nonroot_pos (i : Fin F.size) (hi : i ≠ F.root) : 0 < i.val := by
  have hr := F.root_val
  have hn : i.val ≠ F.root.val := (Fin.ne_iff_vne _ _).mp hi
  omega

def birthIndex (i : Fin F.size) (hi : i ≠ F.root) : Fin F.vertexCount :=
  ⟨F.rootCount + (i.val - 1), by
    have his := i.isLt
    have hs := F.size_pos
    have hip := F.nonroot_pos i hi
    unfold vertexCount
    omega⟩

lemma birthIndex_nonroot (i : Fin F.size) (hi : i ≠ F.root) :
    F.rootCount ≤ (F.birthIndex i hi).val := Nat.le_add_right _ _

lemma birthIndex_injective (i j : Fin F.size) (hi : i ≠ F.root) (hj : j ≠ F.root)
    (he : F.birthIndex i hi = F.birthIndex j hj) : i = j := by
  have hi0 := F.nonroot_pos i hi
  have hj0 := F.nonroot_pos j hj
  have hh := congrArg Fin.val he
  change F.rootCount + (i.val - 1) = F.rootCount + (j.val - 1) at hh
  apply Fin.ext
  omega

lemma birthIndex_lt (i j : Fin F.size) (hi : i ≠ F.root) (hj : j ≠ F.root)
    (hij : i < j) : F.birthIndex i hi < F.birthIndex j hj := by
  have hi0 := F.nonroot_pos i hi
  change F.rootCount + (i.val - 1) < F.rootCount + (j.val - 1)
  change i.val < j.val at hij
  omega

def callIndex (v : Fin F.vertexCount) (hv : F.rootCount ≤ v.val) : Fin F.size :=
  ⟨v.val - F.rootCount + 1, by
    have hs := F.size_pos
    have hvs := v.isLt
    unfold vertexCount at hvs
    omega⟩

lemma callIndex_nonroot (v : Fin F.vertexCount) (hv : F.rootCount ≤ v.val) :
    F.callIndex v hv ≠ F.root := by
  intro he
  have hh := congrArg Fin.val he
  change v.val - F.rootCount + 1 = F.root.val at hh
  rw [F.root_val] at hh
  omega

@[simp] lemma callIndex_birthIndex (i : Fin F.size) (hi : i ≠ F.root) :
    F.callIndex (F.birthIndex i hi) (F.birthIndex_nonroot i hi) = i := by
  apply Fin.ext
  change F.rootCount + (i.val - 1) - F.rootCount + 1 = i.val
  have hi0 := F.nonroot_pos i hi
  omega

@[simp] lemma birthIndex_callIndex (v : Fin F.vertexCount) (hv : F.rootCount ≤ v.val) :
    F.birthIndex (F.callIndex v hv) (F.callIndex_nonroot v hv) = v := by
  apply Fin.ext
  change F.rootCount + (v.val - F.rootCount + 1 - 1) = v.val
  omega

noncomputable def rootLabel (i : Fin F.rootCount) : Fin n :=
  ((F.rootSet.equivFin).symm i).val

lemma rootLabel_injective : Function.Injective F.rootLabel := by
  intro i j he
  have hs : (F.rootSet.equivFin).symm i = (F.rootSet.equivFin).symm j := Subtype.ext he
  exact (F.rootSet.equivFin).symm.injective hs

lemma rootLabel_covers (x : Fin n) (hx : x ∈ F.rootSet) :
    ∃ i : Fin F.rootCount, F.rootLabel i = x := by
  refine ⟨F.rootSet.equivFin ⟨x,hx⟩,?_⟩
  exact congrArg Subtype.val (F.rootSet.equivFin.symm_apply_apply ⟨x,hx⟩)

noncomputable def vertexLabel (v : Fin F.vertexCount) : Fin n :=
  if hv : v.val < F.rootCount then F.rootLabel ⟨v.val,hv⟩
  else F.newVertex (F.callIndex v (Nat.le_of_not_gt hv)) (F.callIndex_nonroot v _)

lemma vertexLabel_root (v : Fin F.vertexCount) (hv : v.val < F.rootCount) :
    F.vertexLabel v = F.rootLabel ⟨v.val,hv⟩ := dite_eq_left hv

lemma vertexLabel_birth (i : Fin F.size) (hi : i ≠ F.root) :
    F.vertexLabel (F.birthIndex i hi) = F.newVertex i hi := by
  rw [vertexLabel,dite_eq_right (Nat.not_lt.mpr (F.birthIndex_nonroot i hi))]
  simp only [callIndex_birthIndex]

lemma vertexLabel_injective_roots : Set.InjOn F.vertexLabel {v | v.val < F.rootCount} := by
  intro v hv w hw he
  rw [F.vertexLabel_root v hv,F.vertexLabel_root w hw] at he
  exact Fin.ext (congrArg (fun i : Fin F.rootCount => i.val) (F.rootLabel_injective he))

lemma vertexLabel_covers (e : Finset (Fin n)) (he : e ∈ c.focus) (x : Fin n) (hx : x ∈ e) :
    ∃ v : Fin F.vertexCount, v.val < F.rootCount ∧ F.vertexLabel v = x := by
  have hxr : x ∈ F.rootSet := Finset.mem_biUnion.mpr ⟨e,he,hx⟩
  obtain ⟨i,hi⟩ := F.rootLabel_covers x hxr
  have hib : i.val < F.vertexCount := by
    have hh := i.isLt
    unfold vertexCount
    omega
  refine ⟨⟨i.val,hib⟩,i.isLt,?_⟩
  rw [F.vertexLabel_root _ i.isLt]
  exact hi

end SharpTerminalLeave.RecordedCallForest

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_Attachment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

lemma lookupGraph_triangle {n : ℕ} {G : Graph n} {T : Finset (Fin n)}
    (hT : T ∈ triangles G) : BirthGraph.IsTriangle (lookupGraph G) T := by
  have ht := mem_triangles.mp hT
  refine ⟨ht.1,?_⟩
  intro x hx y hy hne
  refine ⟨hne,ht.2 ?_⟩
  exact Finset.mem_powersetCard.mpr ⟨by
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro hx hy,
    Finset.card_pair hne⟩

namespace RecordedCallForest
variable {n : ℕ} {G : Graph n} {c : QueryCall (Finset (Fin n)) (Finset (Fin n))}
variable (F : RecordedCallForest (triangleHypergraph G) c)

noncomputable def attachment (v : Fin F.vertexCount) : Finset (Fin n) :=
  if hv : F.rootCount ≤ v.val then
    (F.incoming (F.callIndex v hv) (F.callIndex_nonroot v hv)).1 else ∅

noncomputable def birthParent (v : Fin F.vertexCount) : Option (Fin F.vertexCount) :=
  if hv : F.rootCount ≤ v.val then
    let i := F.callIndex v hv
    let hi := F.callIndex_nonroot v hv
    if hp : F.parent i hi ≠ F.root then some (F.birthIndex (F.parent i hi) hp) else none
  else none

lemma vertexLabel_nonroot (v : Fin F.vertexCount) (hv : F.rootCount ≤ v.val) :
    F.vertexLabel v = F.newVertex (F.callIndex v hv) (F.callIndex_nonroot v hv) := by
  rw [vertexLabel,dite_eq_right (Nat.not_lt.mpr hv)]

lemma attachment_nonroot (v : Fin F.vertexCount) (hv : F.rootCount ≤ v.val) :
    F.attachment v = (F.incoming (F.callIndex v hv) (F.callIndex_nonroot v hv)).1 := dite_eq_left hv

lemma attachment_birth (i : Fin F.size) (hi : i ≠ F.root) :
    F.attachment (F.birthIndex i hi) = (F.incoming i hi).1 := by
  rw [F.attachment_nonroot _ (F.birthIndex_nonroot i hi)]
  simp only [F.callIndex_birthIndex]

lemma birthParent_nonroot (v : Fin F.vertexCount) (hv : F.rootCount ≤ v.val) :
    F.birthParent v =
      if hp : F.parent (F.callIndex v hv) (F.callIndex_nonroot v hv) ≠ F.root then
        some (F.birthIndex _ hp) else none := dite_eq_left hv

lemma birthParent_some (v p : Fin F.vertexCount) (hv : F.rootCount ≤ v.val)
    (hp : F.birthParent v = some p) :
    ∃ h : F.parent (F.callIndex v hv) (F.callIndex_nonroot v hv) ≠ F.root,
      p = F.birthIndex _ h := by
  rw [F.birthParent_nonroot v hv] at hp
  split_ifs at hp with hh
  exact ⟨hh,(Option.some.inj hp).symm⟩

lemma birthParent_none (v : Fin F.vertexCount) (hv : F.rootCount ≤ v.val)
    (hp : F.birthParent v = none) :
    F.parent (F.callIndex v hv) (F.callIndex_nonroot v hv) = F.root := by
  rw [F.birthParent_nonroot v hv] at hp
  split_ifs at hp with hh
  exact not_ne_iff.mp hh

lemma birthParent_eq (v w : Fin F.vertexCount) (hv : F.rootCount ≤ v.val)
    (hw : F.rootCount ≤ w.val) (hp : F.birthParent v = F.birthParent w) :
    F.parent (F.callIndex v hv) (F.callIndex_nonroot v hv) =
      F.parent (F.callIndex w hw) (F.callIndex_nonroot w hw) := by
  cases hh : F.birthParent w with
  | none =>
    exact (F.birthParent_none v hv (hp.trans hh)).trans (F.birthParent_none w hw hh).symm
  | some p =>
    obtain ⟨hv',hpv⟩ := F.birthParent_some v p hv (hp.trans hh)
    obtain ⟨hw',hpw⟩ := F.birthParent_some w p hw hh
    exact F.birthIndex_injective _ _ hv' hw' (hpv.symm.trans hpw)

lemma newTriangle (v : Fin F.vertexCount) (hv : F.rootCount ≤ v.val) :
    insert (F.vertexLabel v) (F.attachment v) =
      (F.incoming (F.callIndex v hv) (F.callIndex_nonroot v hv)).2 := by
  rw [F.vertexLabel_nonroot v hv,F.attachment_nonroot v hv]
  exact (F.newVertex_spec _ _).2.symm

lemma attachments_distinct (v w : Fin F.vertexCount) (hv : F.rootCount ≤ v.val)
    (hw : F.rootCount ≤ w.val) (hp : F.birthParent v = F.birthParent w)
    (ha : F.attachment v = F.attachment w) (hl : F.vertexLabel v = F.vertexLabel w) : v = w := by
  have hpa := F.birthParent_eq v w hv hw hp
  have he : F.incoming (F.callIndex v hv) (F.callIndex_nonroot v hv) =
      F.incoming (F.callIndex w hw) (F.callIndex_nonroot w hw) := by
    apply Prod.ext
    · simpa only [F.attachment_nonroot v hv,F.attachment_nonroot w hw] using ha
    · rw [← F.newTriangle v hv,← F.newTriangle w hw,ha,hl]
  have hi := F.incoming_unique _ _ (F.callIndex_nonroot v hv) (F.callIndex_nonroot w hw) hpa he
  have hvw : F.birthIndex (F.callIndex v hv) (F.callIndex_nonroot v hv) =
      F.birthIndex (F.callIndex w hw) (F.callIndex_nonroot w hw) := by
    congr 1
  simpa only [F.birthIndex_callIndex] using hvw

end RecordedCallForest
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_EdgeMatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

def EdgeMatching {V : Type*} [DecidableEq V] (E : Finset (Finset V)) : Prop :=
  (∀ e ∈ E, e.card = 2) ∧ ∀ e ∈ E, ∀ f ∈ E, e ≠ f → Disjoint e f

namespace EdgeMatching
variable {V : Type*} [DecidableEq V] {E : Finset (Finset V)}

lemma unique_neighbor (hE : EdgeMatching E) {x y z : V}
    (hx : {x,z} ∈ E) (hy : {y,z} ∈ E) : x = y := by
  have hxz : x ≠ z := by
    intro he
    have hc := hE.1 _ hx
    simp [he] at hc
  have he : ({x,z} : Finset V) = {y,z} := by
    by_contra hn
    exact (Finset.disjoint_left.mp (hE.2 _ hx _ hy hn) (show z ∈ ({x,z} : Finset V) by simp)
      (show z ∈ ({y,z} : Finset V) by simp))
  have hm : x ∈ ({y,z} : Finset V) := he ▸ (by simp)
  exact (Finset.mem_insert.mp hm).resolve_right (by simpa using hxz)

end EdgeMatching

noncomputable def matchingSeed {V : Type*} [DecidableEq V] {N R : ℕ}
    (label : Fin N → V) (E : Finset (Finset V)) (hE : EdgeMatching E)
    (hi : Set.InjOn label {v | v.val < R}) : BirthGraph N where
  older v := Finset.univ.filter (fun u => v.val < R ∧ u < v ∧ {label u,label v} ∈ E)
  older_lt := by
    intro v u hu
    exact (Finset.mem_filter.mp hu).2.2.1
  older_card := by
    intro v
    apply (Finset.card_le_one.mpr ?_).trans (show 1 ≤ 2 by omega)
    intro x hx y hy
    obtain ⟨_,hv,hxv,hxe⟩ := Finset.mem_filter.mp hx
    obtain ⟨_,_,hyv,hye⟩ := Finset.mem_filter.mp hy
    apply hi (show x.val < R by exact lt_trans hxv hv)
      (show y.val < R by exact lt_trans hyv hv)
    exact hE.unique_neighbor hxe hye

section MatchingSeed
variable {V : Type*} [DecidableEq V] {N R : ℕ}
variable (label : Fin N → V) (E : Finset (Finset V)) (hE : EdgeMatching E)
variable (hi : Set.InjOn label {v | v.val < R})

@[simp] lemma matchingSeed_mem_older (v u : Fin N) :
    u ∈ (matchingSeed label E hE hi).older v ↔
      v.val < R ∧ u < v ∧ {label u,label v} ∈ E := by
  simp only [matchingSeed,Finset.mem_filter,Finset.mem_univ,true_and]

lemma matchingSeed_small (v : Fin N) : ((matchingSeed label E hE hi).older v).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨hv,hxv,hxe⟩ := (matchingSeed_mem_older _ _ _ _ _ _).mp hx
  obtain ⟨_,hyv,hye⟩ := (matchingSeed_mem_older _ _ _ _ _ _).mp hy
  exact hi (show x.val < R by exact lt_trans hxv hv)
      (show y.val < R by exact lt_trans hyv hv) (hE.unique_neighbor hxe hye)

lemma matchingSeed_root (v u : Fin N) (hu : u ∈ (matchingSeed label E hE hi).older v) :
    u.val < R := by
  obtain ⟨hv,huv,_⟩ := (matchingSeed_mem_older _ _ _ _ _ _).mp hu
  exact lt_trans huv hv

lemma matchingSeed_labels (G : SimpleGraph V)
    (hl : ∀ e ∈ E, ∀ x ∈ e, ∀ y ∈ e, x ≠ y → G.Adj x y)
    (v u : Fin N) (hu : u ∈ (matchingSeed label E hE hi).older v) :
    G.Adj (label u) (label v) := by
  obtain ⟨hv,huv,he⟩ := (matchingSeed_mem_older _ _ _ _ _ _).mp hu
  have hne : label u ≠ label v := fun h => (ne_of_lt huv) (hi (show u.val < R from lt_trans huv hv) hv h)
  exact hl _ he _ (by simp) _ (by simp) hne

lemma matchingSeed_covers
    (hc : ∀ e ∈ E, ∀ x ∈ e, ∃ v : Fin N, v.val < R ∧ label v = x)
    (e : Finset V) (he : e ∈ E) :
    ∃ x y : Fin N, x.val < R ∧ y.val < R ∧
      (matchingSeed label E hE hi).graph.Adj x y ∧ e = {label x,label y} := by
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp (hE.1 e he)
  obtain ⟨x,hx,hxa⟩ := hc _ he a (by simp)
  obtain ⟨y,hy,hyb⟩ := hc _ he b (by simp)
  have hxy : x ≠ y := fun heq => hab ((hxa.symm.trans (congrArg label heq)).trans hyb)
  refine ⟨x,y,hx,hy,?_,by rw [hxa,hyb]⟩
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · exact Or.inl ((matchingSeed_mem_older _ _ _ _ _ _).mpr ⟨hy,hlt,by simpa [hxa,hyb] using he⟩)
  · exact Or.inr ((matchingSeed_mem_older _ _ _ _ _ _).mpr ⟨hx,hgt,by
      simpa [hxa,hyb,Finset.pair_comm] using he⟩)

end MatchingSeed
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_OlderSeed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.TriangleGrowth
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {N R : ℕ}
variable (A : TriangleGrowth G N R)

lemma older_eq_seed {v : Fin N} (hv : v.val < R) : A.older v = A.seed.older v := by
  rw [older,dite_eq_right (Nat.not_le_of_gt hv)]

lemma parent_label_mem {v p : Fin N} (hv : R ≤ v.val) (hp : A.parent v = some p) :
    A.label p ∈ A.attach v := by
  by_contra hn
  have hs : A.attach v ⊆ A.attach p := by
    intro x hx
    exact (Finset.mem_insert.mp ((A.child_attach v p hv hp).1 hx)).resolve_left
      (fun h => hn (h ▸ hx))
  have he : A.attach v = A.attach p := Finset.eq_of_subset_of_card_le hs (by
    rw [A.attach_card v hv,A.attach_card p (A.parent_nonroot v p hv hp)])
  exact (A.child_attach v p hv hp).2 he

lemma parent_mem_older {v p : Fin N} (hv : R ≤ v.val) (hp : A.parent v = some p) :
    p ∈ A.older v := by
  rw [older,dite_eq_left hv,hp]
  exact Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _,A.parent_label_mem hv hp⟩

lemma older_root_of_none {v x : Fin N} (hv : R ≤ v.val) (hp : A.parent v = none)
    (hx : x ∈ A.older v) : x.val < R := by
  rw [older,dite_eq_left hv,hp] at hx
  exact (A.mem_roots x).mp (Finset.mem_filter.mp hx).1

lemma older_pair_of_root {v : Fin N} (hv : R ≤ v.val) (hp : A.parent v = none) :
    ∃ x y : Fin N, x.val < R ∧ y.val < R ∧ A.seed.graph.Adj x y ∧
      A.older v = {x,y} := by
  obtain ⟨x,y,hx,hy,hxy,hat⟩ := A.root_attach v hv hp
  refine ⟨x,y,hx,hy,hxy,?_⟩
  have hxm : x ∈ A.older v := by
    rw [older,dite_eq_left hv,hp]
    exact Finset.mem_filter.mpr ⟨(A.mem_roots x).mpr hx,by rw [hat]; simp⟩
  have hym : y ∈ A.older v := by
    rw [older,dite_eq_left hv,hp]
    exact Finset.mem_filter.mpr ⟨(A.mem_roots y).mpr hy,by rw [hat]; simp⟩
  exact A.birthGraph.older_eq_pair hxy.ne hxm hym

end SharpTerminalLeave.TriangleGrowth

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_TriangleGrowth2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.RecordedCallForest
variable {n : ℕ} {G : Graph n} {c : QueryCall (Finset (Fin n)) (Finset (Fin n))}
variable (F : RecordedCallForest (triangleHypergraph G) c)

lemma root_edges_adj (hM : EdgeMatching c.focus) (hG : c.focus ⊆ G) :
    ∀ e ∈ c.focus, ∀ x ∈ e, ∀ y ∈ e, x ≠ y → (lookupGraph G).Adj x y := by
  intro e he x hx y hy hne
  refine ⟨hne,?_⟩
  have hp : ({x,y} : Finset (Fin n)) = e := Finset.eq_of_subset_of_card_le
    (by simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro hx hy)
    (by rw [hM.1 e he,Finset.card_pair hne])
  rw [hp]
  exact hG he

noncomputable def toTriangleGrowth (hM : EdgeMatching c.focus) (hG : c.focus ⊆ G) :
    TriangleGrowth (lookupGraph G) F.vertexCount F.rootCount where
  label := F.vertexLabel
  seed := matchingSeed F.vertexLabel c.focus hM F.vertexLabel_injective_roots
  seed_small := fun v _ => matchingSeed_small _ _ _ _ v
  seed_root := fun v u hu _ => matchingSeed_root _ _ _ _ v u hu
  seed_labels := fun v _ u hu => matchingSeed_labels _ _ _ _ (lookupGraph G)
    (root_edges_adj hM hG) v u hu
  roots_injective := F.vertexLabel_injective_roots
  attach := F.attachment
  parent := F.birthParent
  parent_lt := by
    intro v p hv hp
    obtain ⟨hh,rfl⟩ := F.birthParent_some v p hv hp
    have ht := F.birthIndex_lt _ _ hh (F.callIndex_nonroot v hv)
      (F.parent_lt (F.callIndex v hv) (F.callIndex_nonroot v hv))
    simpa only [F.birthIndex_callIndex] using ht
  parent_nonroot := by
    intro v p hv hp
    obtain ⟨hh,rfl⟩ := F.birthParent_some v p hv hp
    exact F.birthIndex_nonroot _ hh
  attach_card := by
    intro v hv
    rw [F.attachment_nonroot v hv]
    exact F.incoming_card _ _
  new_label := by
    intro v hv
    rw [F.attachment_nonroot v hv,F.vertexLabel_nonroot v hv]
    exact (F.newVertex_spec _ _).1
  triangle := by
    intro v hv
    rw [F.newTriangle v hv]
    exact lookupGraph_triangle (F.incoming_graph _ _).2.1
  root_attach := by
    intro v hv hp
    have hm := (F.incoming_graph (F.callIndex v hv) (F.callIndex_nonroot v hv)).1
    rw [F.birthParent_none v hv hp,F.root_eq] at hm
    rw [F.attachment_nonroot v hv]
    exact matchingSeed_covers _ _ _ _ (F.vertexLabel_covers) _ hm
  child_attach := by
    intro v p hv hp
    obtain ⟨hh,rfl⟩ := F.birthParent_some v p hv hp
    rw [F.attachment_nonroot v hv,F.vertexLabel_birth,F.attachment_birth]
    exact ⟨(F.incoming_of_nonroot_parent _ _ hh).1,
      (F.incoming_of_nonroot_parent _ _ hh).2.1⟩
  omission := by
    intro v p hv hp
    obtain ⟨hh,rfl⟩ := F.birthParent_some v p hv hp
    rw [F.newTriangle v hv,F.vertexLabel_birth,F.attachment_birth,
      ← (F.newVertex_spec _ hh).2]
    exact (F.incoming_of_nonroot_parent _ _ hh).2.2
  distinct_children := F.attachments_distinct

end SharpTerminalLeave.RecordedCallForest

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_BornEdges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.BirthGraph
open scoped BigOperators

variable {N : ℕ} (B : BirthGraph N)

def bornEdges (v : Fin N) : Finset (Finset (Fin N)) :=
  (B.older v).image (fun u => {u, v})

def backEdges (Z : Finset (Fin N)) : Finset (Finset (Fin N)) :=
  Z.biUnion B.bornEdges

theorem backEdges_mem_pair {Z : Finset (Fin N)} {e : Finset (Fin N)}
    (he : e ∈ B.backEdges Z) :
    ∃ v ∈ Z, ∃ u ∈ B.older v, e = {u, v} := by
  obtain ⟨v, hv, he⟩ := Finset.mem_biUnion.mp he
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp he
  exact ⟨v, hv, u, hu, rfl⟩

def inducedEdges (U : Finset (Fin N)) : Finset (Finset (Fin N)) :=
  (B.backEdges U).filter (fun e => e ⊆ U)

end SharpTerminalLeave.BirthGraph

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_Parent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.TriangleGrowth
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {N R : ℕ}
variable (A : TriangleGrowth G N R)

def Parent (x y : Fin N) : Prop := R ≤ y.val ∧ A.parent y = some x

def Ancestor : Fin N → Fin N → Prop := Relation.ReflTransGen A.Parent

lemma parent_le {x y : Fin N} (h : A.Parent x y) : x ≤ y :=
  le_of_lt (A.parent_lt y x h.1 h.2)

lemma ancestor_le {x y : Fin N} (h : A.Ancestor x y) : x ≤ y := by
  induction h with
  | refl => exact le_rfl
  | @tail y z _ hyz ih => exact ih.trans (A.parent_le hyz)

lemma older_ancestor (v : Fin N) : ∀ x ∈ A.older v,
    x.val < R ∨ A.Ancestor x v := by
  induction v using (measure (fun v : Fin N => v.val)).wf.induction with
  | h v ih =>
    intro x hx
    by_cases hv : R ≤ v.val
    · cases hp : A.parent v with
      | none => exact Or.inl (A.older_root_of_none hv hp hx)
      | some p =>
        have hstep : A.Ancestor p v := Relation.ReflTransGen.single ⟨hv,hp⟩
        have hpv := A.parent_lt v p hv hp
        rw [older,dite_eq_left hv,hp] at hx
        rcases Finset.mem_insert.mp (Finset.mem_filter.mp hx).1 with rfl | hx
        · exact Or.inr hstep
        · exact (ih p hpv x hx).imp_right (fun h => h.trans hstep)
    · rw [A.older_eq_seed (Nat.lt_of_not_ge hv)] at hx
      exact Or.inl (A.seed_root v x hx (Nat.lt_of_not_ge hv))

noncomputable def pathUnion (a b : Fin N) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun x => x.val < R ∨ A.Ancestor x a ∨ A.Ancestor x b)

@[simp] lemma mem_pathUnion (a b x : Fin N) :
    x ∈ A.pathUnion a b ↔ x.val < R ∨ A.Ancestor x a ∨ A.Ancestor x b := by
  classical
  simp only [pathUnion,Finset.mem_filter,Finset.mem_univ,true_and]

lemma left_mem_pathUnion (a b : Fin N) : a ∈ A.pathUnion a b :=
  (A.mem_pathUnion a b a).mpr (Or.inr (Or.inl Relation.ReflTransGen.refl))

lemma right_mem_pathUnion (a b : Fin N) : b ∈ A.pathUnion a b :=
  (A.mem_pathUnion a b b).mpr (Or.inr (Or.inr Relation.ReflTransGen.refl))

lemma pathUnion_older_closed {a b v x : Fin N} (hv : v ∈ A.pathUnion a b)
    (hx : x ∈ A.older v) : x ∈ A.pathUnion a b := by
  apply (A.mem_pathUnion a b x).mpr
  rcases A.older_ancestor v x hx with hroot | hanc
  · exact Or.inl hroot
  · rcases (A.mem_pathUnion a b v).mp hv with hroot | ha | hb
    · exact Or.inl (lt_of_le_of_lt (A.ancestor_le hanc) hroot)
    · exact Or.inr (Or.inl (hanc.trans ha))
    · exact Or.inr (Or.inr (hanc.trans hb))

end SharpTerminalLeave.TriangleGrowth

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_Within
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.BirthGraph
variable {N : ℕ} (B : BirthGraph N)

def Within (Z : Finset (Fin N)) (x y : Fin N) : Prop :=
  Relation.ReflTransGen (fun x y => x ∈ Z ∧ y ∈ Z ∧ x ∈ B.older y) x y

def Covered (Z : Finset (Fin N)) (a b : Fin N) : Prop :=
  ∀ z ∈ Z, (a ∈ Z ∧ B.Within Z z a) ∨ (b ∈ Z ∧ B.Within Z z b)

end SharpTerminalLeave.BirthGraph

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_PathSuffix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.TriangleGrowth
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {N R : ℕ}
variable (A : TriangleGrowth G N R)

noncomputable def pathSuffix (a b : Fin N) (cut : ℕ) : Finset (Fin N) :=
  (A.pathUnion a b).filter (fun x => cut ≤ x.val)

@[simp] lemma mem_pathSuffix (a b x : Fin N) (cut : ℕ) :
    x ∈ A.pathSuffix a b cut ↔ x ∈ A.pathUnion a b ∧ cut ≤ x.val := by
  simp only [pathSuffix,Finset.mem_filter]

end SharpTerminalLeave.TriangleGrowth

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_PathForest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

def PathForest (s : ℕ) :=
  {p : Fin s → Option (Fin s) // ∀ i j, p i = some j → j < i}

namespace PathForest
variable {s : ℕ}

noncomputable instance instFintype : Fintype (PathForest s) := by
  classical
  unfold PathForest
  infer_instance
noncomputable instance instDecidableEq : DecidableEq (PathForest s) := Classical.decEq _

def parent (F : PathForest s) : Fin s → Option (Fin s) := F.val

def Step (F : PathForest s) (x y : Fin s) : Prop := F.parent y = some x

def Ancestor (F : PathForest s) : Fin s → Fin s → Prop := Relation.ReflTransGen F.Step

def OnPath (F : PathForest s) (a : Option (Fin s)) (v : Fin s) : Prop :=
  ∃ w, a = some w ∧ F.Ancestor v w

inductive PathColor
  | left | right | both
  deriving DecidableEq

instance instFintypePathColor : Fintype PathColor where
  elems := {.left,.right,.both}
  complete := by intro x; cases x <;> simp

noncomputable def color (F : PathForest s) (a b : Option (Fin s)) (v : Fin s) : PathColor := by
  classical
  exact if F.OnPath a v then if F.OnPath b v then .both else .left else .right

end PathForest
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_RestrictedParent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.PathForest
variable {s : ℕ}

noncomputable def restrictedParent (F : PathForest s) (S : Finset (Fin s))
    (hS : ∀ v ∈ S, ∀ p, F.parent v = some p → p ∈ S)
    (i : Fin S.card) : Option (Fin S.card) :=
  match hp : F.parent (S.orderEmbOfFin rfl i) with
  | none => none
  | some p => some ((S.orderIsoOfFin rfl).symm
      ⟨p,hS _ (S.orderEmbOfFin_mem rfl i) p hp⟩)

noncomputable def restrict (F : PathForest s) (S : Finset (Fin s))
    (hS : ∀ v ∈ S, ∀ p, F.parent v = some p → p ∈ S) : PathForest S.card := by
  refine ⟨F.restrictedParent S hS,?_⟩
  intro i j hij
  unfold restrictedParent at hij
  split at hij
  · contradiction
  · rename_i p hp
    have hj := Option.some.inj hij
    subst j
    apply (S.orderEmbOfFin rfl).lt_iff_lt.mp
    have he : S.orderEmbOfFin rfl ((S.orderIsoOfFin rfl).symm
        ⟨p,hS _ (S.orderEmbOfFin_mem rfl i) p hp⟩) = p :=
      congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply _)
    rw [he]
    exact F.property _ _ hp

noncomputable def index (S : Finset (Fin s)) (v : Fin s) (hv : v ∈ S) : Fin S.card :=
  (S.orderIsoOfFin rfl).symm ⟨v,hv⟩

@[simp] lemma embed_index (S : Finset (Fin s)) (v : Fin s) (hv : v ∈ S) :
    S.orderEmbOfFin rfl (index S v hv) = v :=
  congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply _)

@[simp] lemma index_embed (S : Finset (Fin s)) (i : Fin S.card) :
    index S (S.orderEmbOfFin rfl i) (S.orderEmbOfFin_mem rfl i) = i :=
  (S.orderIsoOfFin rfl).symm_apply_apply i

lemma restrict_parent_some (F : PathForest s) (S : Finset (Fin s))
    (hS : ∀ v ∈ S, ∀ p, F.parent v = some p → p ∈ S) (i j : Fin S.card) :
    (F.restrict S hS).parent i = some j ↔
      F.parent (S.orderEmbOfFin rfl i) = some (S.orderEmbOfFin rfl j) := by
  change F.restrictedParent S hS i = some j ↔ _
  unfold restrictedParent
  split
  · rename_i he
    rw [he]
    simp
  · rename_i p hp
    simp only [hp,Option.some.injEq]
    change index S p (hS _ (S.orderEmbOfFin_mem rfl i) p hp) = j ↔ _
    constructor
    · intro he
      rw [← he,embed_index]
    · intro he
      subst p
      exact index_embed S j

lemma restrict_step_iff (F : PathForest s) (S : Finset (Fin s))
    (hS : ∀ v ∈ S, ∀ p, F.parent v = some p → p ∈ S) (i j : Fin S.card) :
    (F.restrict S hS).Step i j ↔
      F.Step (S.orderEmbOfFin rfl i) (S.orderEmbOfFin rfl j) :=
  restrict_parent_some F S hS j i

lemma restrict_ancestor (F : PathForest s) (S : Finset (Fin s))
    (hS : ∀ v ∈ S, ∀ p, F.parent v = some p → p ∈ S)
    {x y : Fin s} (hx : x ∈ S) (hy : y ∈ S) (h : F.Ancestor x y) :
    (F.restrict S hS).Ancestor (index S x hx) (index S y hy) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail y z hxy hyz ih =>
    have hym : y ∈ S := hS z hy y hyz
    apply Relation.ReflTransGen.tail (ih hym)
    apply (F.restrict_step_iff S hS _ _).mpr
    simpa only [embed_index] using hyz

noncomputable def restrictMark (S : Finset (Fin s)) (a : Fin s) : Option (Fin S.card) := by
  classical
  exact if ha : a ∈ S then some (index S a ha) else none

lemma restrict_onPath (F : PathForest s) (S : Finset (Fin s))
    (hS : ∀ v ∈ S, ∀ p, F.parent v = some p → p ∈ S)
    {x a : Fin s} (hx : x ∈ S) (ha : a ∈ S) (h : F.Ancestor x a) :
    (F.restrict S hS).OnPath (restrictMark S a) (index S x hx) := by
  classical
  refine ⟨index S a ha,?_,F.restrict_ancestor S hS hx ha h⟩
  simp only [restrictMark,dite_eq_left ha]

theorem restrict_two_path_cover (F : PathForest s) (S : Finset (Fin s))
    (hS : ∀ v ∈ S, ∀ p, F.parent v = some p → p ∈ S) (a b : Fin s)
    (hc : ∀ v ∈ S, (a ∈ S ∧ F.Ancestor v a) ∨ (b ∈ S ∧ F.Ancestor v b)) :
    ∀ i, (F.restrict S hS).OnPath (restrictMark S a) i ∨
      (F.restrict S hS).OnPath (restrictMark S b) i := by
  intro i
  have hi := S.orderEmbOfFin_mem rfl i
  rcases hc _ hi with ⟨ha,hva⟩ | ⟨hb,hvb⟩
  · exact Or.inl (by simpa only [index_embed] using F.restrict_onPath S hS hi ha hva)
  · exact Or.inr (by simpa only [index_embed] using F.restrict_onPath S hS hi hb hvb)

end SharpTerminalLeave.PathForest

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_NonrootForest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.TriangleGrowth
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {N R : ℕ}
variable (A : TriangleGrowth G N R)

noncomputable def nonrootForest : PathForest N := by
  refine ⟨fun v => if R ≤ v.val then A.parent v else none,?_⟩
  intro v p hp
  change (if R ≤ v.val then A.parent v else none) = some p at hp
  split_ifs at hp with hv
  exact A.parent_lt v p hv hp

lemma nonrootForest_step {x y : Fin N} (h : A.Parent x y) :
    A.nonrootForest.Step x y := by
  change (if R ≤ y.val then A.parent y else none) = some x
  rw [ite_eq_left h.1]
  exact h.2

lemma nonrootForest_ancestor {x y : Fin N} (h : A.Ancestor x y) :
    A.nonrootForest.Ancestor x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail y z hxy hyz ih =>
    exact Relation.ReflTransGen.tail ih (A.nonrootForest_step hyz)

lemma pathNonroots_parent_closed (a b : Fin N) :
    ∀ v ∈ A.pathSuffix a b R, ∀ p, A.nonrootForest.parent v = some p →
      p ∈ A.pathSuffix a b R := by
  intro v hv p hp
  obtain ⟨hvP,hvR⟩ := (A.mem_pathSuffix a b v R).mp hv
  change (if R ≤ v.val then A.parent v else none) = some p at hp
  rw [ite_eq_left hvR] at hp
  exact (A.mem_pathSuffix a b p R).mpr
    ⟨A.pathUnion_older_closed hvP (A.parent_mem_older hvR hp),A.parent_nonroot v p hvR hp⟩

lemma pathNonroots_cover (a b : Fin N) :
    ∀ v ∈ A.pathSuffix a b R,
      (a ∈ A.pathSuffix a b R ∧ A.nonrootForest.Ancestor v a) ∨
      (b ∈ A.pathSuffix a b R ∧ A.nonrootForest.Ancestor v b) := by
  intro v hv
  obtain ⟨hvP,hvR⟩ := (A.mem_pathSuffix a b v R).mp hv
  rcases (A.mem_pathUnion a b v).mp hvP with hroot | ha | hb
  · omega
  · exact Or.inl ⟨(A.mem_pathSuffix a b a R).mpr
      ⟨A.left_mem_pathUnion a b,hvR.trans (A.ancestor_le ha)⟩,A.nonrootForest_ancestor ha⟩
  · exact Or.inr ⟨(A.mem_pathSuffix a b b R).mpr
      ⟨A.right_mem_pathUnion a b,hvR.trans (A.ancestor_le hb)⟩,A.nonrootForest_ancestor hb⟩

noncomputable def pathForest (a b : Fin N) : PathForest (A.pathSuffix a b R).card :=
  A.nonrootForest.restrict (A.pathSuffix a b R) (A.pathNonroots_parent_closed a b)

theorem pathForest_two_path_cover (a b : Fin N) :
    ∀ i, (A.pathForest a b).OnPath (PathForest.restrictMark (A.pathSuffix a b R) a) i ∨
      (A.pathForest a b).OnPath (PathForest.restrictMark (A.pathSuffix a b R) b) i :=
  A.nonrootForest.restrict_two_path_cover _ (A.pathNonroots_parent_closed a b) a b
    (A.pathNonroots_cover a b)

theorem older_focus {v p : Fin N} (hv : R ≤ v.val) (hp : A.parent v = some p) :
    ∃ u ∈ A.older p, A.older v = {p,u} := by
  classical
  obtain ⟨x,y,hxy,hpair⟩ := Finset.card_eq_two.mp ((A.older_invariants v).2 hv).1
  have hpm := A.parent_mem_older hv hp
  rw [hpair,Finset.mem_insert,Finset.mem_singleton] at hpm
  have hsub : A.older v ⊆ insert p (A.older p) := by
    rw [older,dite_eq_left hv,hp]
    exact Finset.filter_subset _ _
  rcases hpm with rfl | rfl
  · refine ⟨y,?_,hpair⟩
    exact (Finset.mem_insert.mp (hsub (by rw [hpair]; simp))).resolve_left (Ne.symm hxy)
  · refine ⟨x,?_,?_⟩
    · exact (Finset.mem_insert.mp (hsub (by rw [hpair]; simp))).resolve_left hxy
    · simpa only [Finset.pair_comm] using hpair

end SharpTerminalLeave.TriangleGrowth

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_Restrict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.BirthGraph
variable {N : ℕ} (B : BirthGraph N)

def restrict (s : Finset (Fin N))
    (hclosed : ∀ v ∈ s, B.older v ⊆ s) : BirthGraph s.card where
  older v := reindexSet s (B.older (s.orderEmbOfFin rfl v))
  older_lt v u hu := (s.orderEmbOfFin rfl).lt_iff_lt.mp
    (B.older_lt _ _ ((mem_reindexSet _ _ _).mp hu))
  older_card v := by
    rw [reindexSet_card (hclosed _ (s.orderEmbOfFin_mem rfl v))]
    exact B.older_card _

@[simp] lemma restrict_older_mem (s : Finset (Fin N))
    (hclosed : ∀ v ∈ s, B.older v ⊆ s) (u v : Fin s.card) :
    u ∈ (B.restrict s hclosed).older v ↔
      s.orderEmbOfFin rfl u ∈ B.older (s.orderEmbOfFin rfl v) :=
  mem_reindexSet _ _ _

@[simp] lemma restrict_graph_adj (s : Finset (Fin N))
    (hclosed : ∀ v ∈ s, B.older v ⊆ s) (u v : Fin s.card) :
    (B.restrict s hclosed).graph.Adj u v ↔
      B.graph.Adj (s.orderEmbOfFin rfl u) (s.orderEmbOfFin rfl v) := by
  simp only [graph_adj,restrict_older_mem]

lemma restrict_older_card (s : Finset (Fin N))
    (hclosed : ∀ v ∈ s, B.older v ⊆ s) (v : Fin s.card) :
    ((B.restrict s hclosed).older v).card = (B.older (s.orderEmbOfFin rfl v)).card :=
  reindexSet_card (hclosed _ (s.orderEmbOfFin_mem rfl v))

end SharpTerminalLeave.BirthGraph

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_PathPattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.TriangleGrowth
variable {n N R : ℕ} {G : Graph n} (A : TriangleGrowth (lookupGraph G) N R)

noncomputable def pathPattern (a b : Fin N) : BirthGraph (A.pathUnion a b).card :=
  A.birthGraph.restrict (A.pathUnion a b)
    (fun _ hv _ hx => A.pathUnion_older_closed hv hx)

noncomputable def pathIndex (a b x : Fin N) (hx : x ∈ A.pathUnion a b) :
    Fin (A.pathUnion a b).card := (A.pathUnion a b).orderIsoOfFin rfl |>.symm ⟨x,hx⟩

@[simp] lemma pathIndex_image (a b x : Fin N) (hx : x ∈ A.pathUnion a b) :
    (A.pathUnion a b).orderEmbOfFin rfl (A.pathIndex a b x hx) = x :=
  congrArg Subtype.val ((A.pathUnion a b).orderIsoOfFin rfl |>.apply_symm_apply ⟨x,hx⟩)

noncomputable def pathAssignment (a b : Fin N)
    (hi : Set.InjOn A.label (A.pathUnion a b)) : Fin (A.pathUnion a b).card ↪ Fin n where
  toFun i := A.label ((A.pathUnion a b).orderEmbOfFin rfl i)
  inj' := by
    intro i j he
    apply (A.pathUnion a b).orderEmbOfFin rfl |>.injective
    exact hi ((A.pathUnion a b).orderEmbOfFin_mem rfl i)
      ((A.pathUnion a b).orderEmbOfFin_mem rfl j) he

@[simp] lemma pathAssignment_index (a b x : Fin N) (hx : x ∈ A.pathUnion a b)
    (hi : Set.InjOn A.label (A.pathUnion a b)) :
    A.pathAssignment a b hi (A.pathIndex a b x hx) = A.label x := by
  change A.label ((A.pathUnion a b).orderEmbOfFin rfl (A.pathIndex a b x hx)) = A.label x
  rw [A.pathIndex_image]

theorem pathPattern_nonroot (a b : Fin N) (i : Fin (A.pathUnion a b).card)
    (hi : R ≤ i.val) : ((A.pathPattern a b).older i).card = 2 := by
  rw [pathPattern,BirthGraph.restrict_older_card]
  exact ((A.older_invariants _).2 (orderEmb_nonroot _
    (fun x hx => (A.mem_pathUnion a b x).mpr (Or.inl hx)) i hi)).1

end SharpTerminalLeave.TriangleGrowth

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_LocalChoiceRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

noncomputable def localChoiceRank {α : Type*} (C : Finset α) (a : α) : ℕ := by
  classical
  exact if h : a ∈ C then ((Fintype.equivFin {a // a ∈ C}) ⟨a,h⟩).val else 0

noncomputable def prefixChoiceValues {n : ℕ} {α : Type*}
    (S : Finset (Fin n → α)) (f : Fin n → α) (i : Fin n) : Finset α := by
  classical
  exact (S.filter (fun g => ∀ j, j < i → g j = f j)).image (fun g => g i)

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_ValidIndexedAttachments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

def ValidIndexedAttachments {K s : ℕ} (E : Finset (Finset (Fin K))) (birth : Fin s → Fin K)
    (F : PathForest s) (f : Fin s → Finset (Fin K)) : Prop :=
  (∀ i, (f i).card ≤ 2) ∧ ∀ i,
    match F.parent i with
    | none => f i ∈ E
    | some p => ∃ u ∈ f p, f i = {birth p,u}

noncomputable def indexedAttachmentFamily {K s : ℕ} (E : Finset (Finset (Fin K))) (birth : Fin s → Fin K)
    (F : PathForest s) : Finset (Fin s → Finset (Fin K)) := by
  classical
  exact Finset.univ.filter (ValidIndexedAttachments E birth F)

@[simp] lemma mem_indexedAttachmentFamily {K s : ℕ} (E : Finset (Finset (Fin K))) (birth : Fin s → Fin K)
    (F : PathForest s) (f : Fin s → Finset (Fin K)) :
    f ∈ indexedAttachmentFamily E birth F ↔ ValidIndexedAttachments E birth F f := by
  classical
  simp only [indexedAttachmentFamily,Finset.mem_filter,Finset.mem_univ,true_and]

end SharpTerminalLeave

open Filter
open scoped BigOperators Topology
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_PathBirthIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

lemma reindexSet_pair {N : ℕ} (S : Finset (Fin N)) (x y : Fin N)
    (hx : x ∈ S) (hy : y ∈ S) :
    reindexSet S {x,y} = {PathForest.index S x hx,PathForest.index S y hy} := by
  ext i
  simp only [mem_reindexSet,Finset.mem_insert,Finset.mem_singleton]
  have hxi : S.orderEmbOfFin rfl i = x ↔ i = PathForest.index S x hx := by
    simpa only [PathForest.embed_index] using
      ((S.orderEmbOfFin rfl).injective.eq_iff (a := i) (b := PathForest.index S x hx))
  have hyi : S.orderEmbOfFin rfl i = y ↔ i = PathForest.index S y hy := by
    simpa only [PathForest.embed_index] using
      ((S.orderEmbOfFin rfl).injective.eq_iff (a := i) (b := PathForest.index S y hy))
  rw [hxi,hyi]

lemma PathForest.restrict_parent_none {s : ℕ} (F : PathForest s) (S : Finset (Fin s))
    (hS : ∀ v ∈ S, ∀ p, F.parent v = some p → p ∈ S) (i : Fin S.card) :
    (F.restrict S hS).parent i = none ↔ F.parent (S.orderEmbOfFin rfl i) = none := by
  classical
  change F.restrictedParent S hS i = none ↔ _
  unfold PathForest.restrictedParent
  split <;> simp_all

namespace TriangleGrowth
variable {n N R : ℕ} {G : Graph n} (A : TriangleGrowth (lookupGraph G) N R)

noncomputable def pathBirthIndex (a b : Fin N) (hR : R ≤ N)
    (i : Fin (A.pathSuffix a b R).card) : Fin (A.pathUnion a b).card :=
  suffixFullIndex (A.pathUnion a b) hR
    (fun x hx => (A.mem_pathUnion a b x).mpr (Or.inl hx)) i

@[simp] lemma pathBirthIndex_val (a b : Fin N) (hR : R ≤ N)
    (i : Fin (A.pathSuffix a b R).card) : (A.pathBirthIndex a b hR i).val = R+i.val := rfl

@[simp] lemma pathBirthIndex_embedding (a b : Fin N) (hR : R ≤ N)
    (i : Fin (A.pathSuffix a b R).card) :
    (A.pathUnion a b).orderEmbOfFin rfl (A.pathBirthIndex a b hR i) =
      (A.pathSuffix a b R).orderEmbOfFin rfl i :=
  suffix_full_embedding _ hR _ i

noncomputable def pathAttachments (a b : Fin N) (hR : R ≤ N)
    (i : Fin (A.pathSuffix a b R).card) : Finset (Fin (A.pathUnion a b).card) :=
  (A.pathPattern a b).older (A.pathBirthIndex a b hR i)

lemma pathAttachments_eq (a b : Fin N) (hR : R ≤ N)
    (i : Fin (A.pathSuffix a b R).card) :
    A.pathAttachments a b hR i = reindexSet (A.pathUnion a b)
      (A.older ((A.pathSuffix a b R).orderEmbOfFin rfl i)) := by
  change reindexSet _ (A.older ((A.pathUnion a b).orderEmbOfFin rfl _)) = _
  rw [A.pathBirthIndex_embedding]

noncomputable def pathRootEdges (a b : Fin N) : Finset (Finset (Fin (A.pathUnion a b).card)) :=
  (A.seed.backEdges A.roots).image (reindexSet (A.pathUnion a b))

lemma pathForest_parent_some (a b : Fin N) (i j : Fin (A.pathSuffix a b R).card) :
    (A.pathForest a b).parent i = some j ↔
      A.parent ((A.pathSuffix a b R).orderEmbOfFin rfl i) =
        some ((A.pathSuffix a b R).orderEmbOfFin rfl j) := by
  rw [pathForest,PathForest.restrict_parent_some]
  change (if R ≤ _ then _ else none) = _ ↔ _
  rw [ite_eq_left ((A.mem_pathSuffix a b _ R).mp
    ((A.pathSuffix a b R).orderEmbOfFin_mem rfl i)).2]

lemma pathForest_parent_none (a b : Fin N) (i : Fin (A.pathSuffix a b R).card) :
    (A.pathForest a b).parent i = none ↔
      A.parent ((A.pathSuffix a b R).orderEmbOfFin rfl i) = none := by
  rw [pathForest,PathForest.restrict_parent_none]
  change (if R ≤ _ then _ else none) = _ ↔ _
  rw [ite_eq_left ((A.mem_pathSuffix a b _ R).mp
    ((A.pathSuffix a b R).orderEmbOfFin_mem rfl i)).2]

theorem pathAttachments_valid (a b : Fin N) (hR : R ≤ N) :
    ValidIndexedAttachments (A.pathRootEdges a b) (A.pathBirthIndex a b hR)
      (A.pathForest a b) (A.pathAttachments a b hR) := by
  classical
  constructor
  · intro i
    exact le_of_eq (A.pathPattern_nonroot a b _ (by simp only [pathBirthIndex_val]; omega))
  · intro i
    have hiv := (A.pathSuffix a b R).orderEmbOfFin_mem rfl i
    have hiR := ((A.mem_pathSuffix a b _ R).mp hiv).2
    cases hp : (A.pathForest a b).parent i with
    | none =>
      have hpar := (A.pathForest_parent_none a b i).mp hp
      obtain ⟨x,y,hx,hy,hxy,he⟩ := A.older_pair_of_root hiR hpar
      have hem : ({x,y} : Finset (Fin N)) ∈ A.seed.backEdges A.roots := by
        rcases hxy with hxy | hyx
        · exact Finset.mem_biUnion.mpr ⟨y,(A.mem_roots y).mpr hy,
            Finset.mem_image.mpr ⟨x,hxy,rfl⟩⟩
        · have hh : ({y,x} : Finset (Fin N)) ∈ A.seed.backEdges A.roots :=
            Finset.mem_biUnion.mpr ⟨x,(A.mem_roots x).mpr hx,
              Finset.mem_image.mpr ⟨y,hyx,rfl⟩⟩
          simpa only [Finset.pair_comm] using hh
      change A.pathAttachments a b hR i ∈ A.pathRootEdges a b
      rw [A.pathAttachments_eq,he]
      exact Finset.mem_image.mpr ⟨{x,y},hem,rfl⟩
    | some j =>
      have hpar := (A.pathForest_parent_some a b i j).mp hp
      obtain ⟨u,hu,he⟩ := A.older_focus hiR hpar
      have hjP := ((A.mem_pathSuffix a b _ R).mp
        ((A.pathSuffix a b R).orderEmbOfFin_mem rfl j)).1
      have huP := A.pathUnion_older_closed hjP hu
      let k := PathForest.index (A.pathUnion a b) u huP
      refine ⟨k,?_,?_⟩
      · rw [A.pathAttachments_eq]
        apply (mem_reindexSet _ _ _).mpr
        simpa only [k,PathForest.embed_index] using hu
      · rw [A.pathAttachments_eq,he,reindexSet_pair _ _ _ hjP huP]
        have hj : PathForest.index (A.pathUnion a b)
            ((A.pathSuffix a b R).orderEmbOfFin rfl j) hjP = A.pathBirthIndex a b hR j := by
          apply (A.pathUnion a b).orderEmbOfFin rfl |>.injective
          rw [PathForest.embed_index,A.pathBirthIndex_embedding]
        rw [hj]

end TriangleGrowth
end SharpTerminalLeave

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_IndexedPatternEdges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

def indexedPatternEdges {K s : ℕ} (E : Finset (Finset (Fin K)))
    (birth : Fin s → Fin K) (f : Fin s → Finset (Fin K)) : Finset (Finset (Fin K)) :=
  E ∪ Finset.univ.biUnion (fun i => (f i).image (fun u => {u,birth i}))

end SharpTerminalLeave

open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_SuffixProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

def suffixProjection {K R s : ℕ} (hK : K = R+s) (i : Fin K) : Option (Fin s) :=
  if h : R ≤ i.val then some ⟨i.val-R,by omega⟩ else none

lemma suffix_projection_embedding {N R : ℕ} (S : Finset (Fin N)) (hR : R ≤ N)
    (hroot : ∀ x : Fin N, x.val < R → x ∈ S) (x : Fin N) (hx : x ∈ S) :
    suffixProjection (prefix_suffix_card S hR hroot) (PathForest.index S x hx) =
      PathForest.restrictMark (orderedSuffix S R) x := by
  classical
  by_cases hn : R ≤ x.val
  · have hxT : x ∈ orderedSuffix S R := Finset.mem_filter.mpr ⟨hx,hn⟩
    let i := PathForest.index (orderedSuffix S R) x hxT
    have hs : PathForest.index S x hx = suffixFullIndex S hR hroot i := by
      apply (S.orderEmbOfFin rfl).injective
      rw [PathForest.embed_index,suffix_full_embedding]
      exact (PathForest.embed_index _ _ _).symm
    have hiv : (PathForest.index S x hx).val = R+i.val := by rw [hs]; rfl
    rw [PathForest.restrictMark,dite_eq_left hxT]
    unfold suffixProjection
    rw [dite_eq_left (show R ≤ (PathForest.index S x hx).val by omega)]
    apply congrArg some
    apply Fin.ext
    simp only [hiv]
    exact Nat.add_sub_cancel_left R i.val
  · have hxT : x ∉ orderedSuffix S R := by simpa only [orderedSuffix,Finset.mem_filter,hx,true_and] using hn
    have hiv : (PathForest.index S x hx).val = x.val := initial_rank S hroot x (by omega)
    rw [PathForest.restrictMark,dite_eq_right hxT]
    unfold suffixProjection
    rw [dite_eq_right (show ¬ R ≤ (PathForest.index S x hx).val by omega)]

namespace TriangleGrowth
variable {n N R : ℕ} {G : Graph n} (A : TriangleGrowth (lookupGraph G) N R)

lemma path_card_split (a b : Fin N) (hR : R ≤ N) :
    (A.pathUnion a b).card = R+(A.pathSuffix a b R).card :=
  prefix_suffix_card _ hR (fun x hx => (A.mem_pathUnion a b x).mpr (Or.inl hx))

lemma path_mark_projection (a b : Fin N) (hR : R ≤ N)
    (x : Fin N) (hx : x ∈ A.pathUnion a b) :
    suffixProjection (A.path_card_split a b hR) (A.pathIndex a b x hx) =
      PathForest.restrictMark (A.pathSuffix a b R) x :=
  suffix_projection_embedding _ hR
    (fun y hy => (A.mem_pathUnion a b y).mpr (Or.inl hy)) x hx

open Classical in

noncomputable def pathWitnessCode (a b : Fin N) (hR : R ≤ N) :
    Σ ab : Fin (A.pathUnion a b).card × Fin (A.pathUnion a b).card,
      Σ F : {F : PathForest (A.pathSuffix a b R).card // ∀ i,
        F.OnPath (suffixProjection (A.path_card_split a b hR) ab.1) i ∨
        F.OnPath (suffixProjection (A.path_card_split a b hR) ab.2) i},
        {f // f ∈ indexedAttachmentFamily (A.pathRootEdges a b) (A.pathBirthIndex a b hR) F.val} := by
  refine ⟨⟨A.pathIndex a b a (A.left_mem_pathUnion a b),
    A.pathIndex a b b (A.right_mem_pathUnion a b)⟩,⟨A.pathForest a b,?_⟩,
    A.pathAttachments a b hR,?_⟩
  · rw [A.path_mark_projection a b hR a (A.left_mem_pathUnion a b),
      A.path_mark_projection a b hR b (A.right_mem_pathUnion a b)]
    exact A.pathForest_two_path_cover a b
  · exact (mem_indexedAttachmentFamily _ _ _ _).mpr (A.pathAttachments_valid a b hR)

end TriangleGrowth
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_IndexedWitnessCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

abbrev IndexedWitnessCode {K s : ℕ} (E : Graph K) (birth : Fin s → Fin K)
    (mark : Fin K → Option (Fin s)) :=
  Σ ab : Fin K × Fin K,
    Σ F : {F : PathForest s // ∀ i, F.OnPath (mark ab.1) i ∨ F.OnPath (mark ab.2) i},
      {f // f ∈ indexedAttachmentFamily E birth F.val}

noncomputable instance instFintypeIndexedWitnessCode {K s : ℕ} (E : Graph K) (birth : Fin s → Fin K)
    (mark : Fin K → Option (Fin s)) : Fintype (IndexedWitnessCode E birth mark) := by
  classical
  unfold IndexedWitnessCode
  infer_instance

def decodeWitnessPattern {K s : ℕ} {E : Graph K} {birth : Fin s → Fin K}
    {mark : Fin K → Option (Fin s)} (w : IndexedWitnessCode E birth mark) :
    (Fin K × Fin K) × Graph K :=
  (w.1,insert {w.1.1,w.1.2} (indexedPatternEdges E birth w.2.2.val))

def rootEdgeUniverse (K R : ℕ) : Graph K := (initialVertices K R).powersetCard 2

def seedPatternChoices (K R : ℕ) : Finset (Graph K) :=
  (rootEdgeUniverse K R).powerset.filter (fun E => E.card ≤ 2)

end SharpTerminalLeave

open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_Address
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave
namespace PathForest
variable {s : ℕ} {α : Type*}

def address (F : PathForest s) (key : Fin s → α) (i : Fin s) : List α :=
  key i :: match _hp : F.parent i with
    | none => []
    | some j => F.address key j
termination_by i.val
decreasing_by exact F.property i j _hp

end PathForest

def indexedTriangleKey {K s n : ℕ} (birth : Fin s → Fin K)
    (f : Fin s → Finset (Fin K)) (ψ : Fin K → Fin n) (i : Fin s) :
    Finset (Fin n) × Finset (Fin n) :=
  ((f i).image ψ,insert (ψ (birth i)) ((f i).image ψ))

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_MarkedChild
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

structure MarkedChild where
  required : Bool
  law : PMF (Bool × Bool)
  priority : ℕ := 0

noncomputable def markedDemand : List MarkedChild → Bool
  | [] => false
  | a :: as => a.required || markedDemand as

noncomputable def markedCheck : List MarkedChild → PMF (Bool × Bool)
  | [] => PMF.pure (true, true)
  | a :: as => a.law.bind (fun z =>
      if z.1 then PMF.pure (false, ((!a.required) || z.2) && !markedDemand as)
      else (markedCheck as).map (fun y => (y.1, ((!a.required) || z.2) && y.2)))

noncomputable def markedGood (p : PMF (Bool × Bool)) : ℝ :=
  pmfMean p (fun z => if z.2 then 1 else 0)

noncomputable def markedFailure (p : PMF (Bool × Bool)) : ℝ :=
  pmfMean p (fun z => if z.1 then 0 else 1)

noncomputable def markedBound : List MarkedChild → ℝ
  | [] => 1
  | a :: as => (if a.required then markedGood a.law
      else if markedDemand as then markedFailure a.law else 1) * markedBound as

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_ChargesCovered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

def ChargesCovered (charge : MarkedChild → Bool) (as : List MarkedChild) : Prop :=
  ∀ pre a post, as = pre ++ a :: post →
    a.required = false → charge a = true → markedDemand post = true

noncomputable def chargedFactor (charge : MarkedChild → Bool) (a : MarkedChild) : ℝ :=
  if a.required then markedGood a.law else if charge a then markedFailure a.law else 1

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_MarkedSuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

noncomputable def markedSuccess (p : PMF (Bool × Bool)) : ℝ :=
  pmfMean p (fun z => if z.1 then 1 else 0)

noncomputable def selectedClockLaw {K : Type*} [DecidableEq K]
    (N : ℕ) [NeZero N] (S : Finset K) (σ : K → Fin N) (k : K) : PMF (Fin N) :=
  if k ∈ S then PMF.pure (σ k) else PMF.uniformOfFintype (Fin N)

noncomputable def rowChild {K : Type*} [DecidableEq K] {N : ℕ}
    (S : Finset K) (p : K → Fin N → PMF (Bool × Bool))
    (deadline : ℕ) (ω : K → Fin N) (k : K) : MarkedChild :=
  ⟨decide (k ∈ S), if (ω k).val < deadline then p k (ω k)
      else PMF.pure (false,false), (ω k).val⟩

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_ProspectiveFailure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

noncomputable def prospectiveFailure (N : ℕ) [NeZero N] (t : ℕ) (q : Fin N → ℝ) : ℝ :=
  1 - (∑ u : Fin N, if u.val < t then q u else 0) / (N : ℝ)

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_OrderedMarkedRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

noncomputable def orderedMarkedRow {K : Type*} [DecidableEq K] {N : ℕ}
    (order : List K) (S : Finset K) (p : K → Fin N → PMF (Bool × Bool))
    (deadline : ℕ) (ω : K → Fin N) : List MarkedChild :=
  (order.map (rowChild S p deadline ω)).mergeSort
    (fun a b => decide (a.priority ≤ b.priority))

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_ProgramDemand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave
namespace ExposureTree
variable {K V O A : Type*}

def programDemand : List (Bool × ExposureTree K V (Bool × Bool)) → Bool
  | [] => false
  | a :: as => a.1 || programDemand as

def checkMarked : List (Bool × ExposureTree K V (Bool × Bool)) →
    ExposureTree K V (Bool × Bool)
  | [] => .done (true,true)
  | a :: as => bind a.2 (fun z =>
      if z.1 then .done (false, ((!a.1) || z.2) && !programDemand as)
      else mapOutput (fun y => (y.1, ((!a.1) || z.2) && y.2)) (checkMarked as))

@[simp] theorem programDemand_law (ν : K → PMF V)
    (as : List (Bool × ExposureTree K V (Bool × Bool))) :
    markedDemand (as.map (fun a => (⟨a.1,fresh ν a.2,0⟩ : MarkedChild))) =
      programDemand as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons,markedDemand,programDemand,ih]

end ExposureTree

section MarkedGrid
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

noncomputable def markedGridQueryDepth (H : τ → Finset ι) (N : ℕ)
    (required : List (ι × τ) → Bool) :
    ℕ → ℕ → List (ι × τ) → Finset ι → Option τ → ExposureTree τ (Fin N) (Bool × Bool)
  | 0, _, _, focus, parent => ExposureTree.bind
      (ExposureTree.exposeLabeled Prod.snd (gridCandidates H focus parent).toList)
      (fun _ => .done (true,true))
  | d+1, k, address, focus, parent => ExposureTree.bind
      (ExposureTree.exposeLabeled Prod.snd (gridCandidates H focus parent).toList)
      (fun values => ExposureTree.checkMarked
        ((values.mergeSort (fun a b => a.2.val ≤ b.2.val)).map
          (fun p => (required (p.1 :: address), if p.2.val < k then
            markedGridQueryDepth H N required d p.2.val (p.1 :: address)
              ((H p.1.2).erase p.1.1) (some p.1.2)
            else .done (false,false)))))

end MarkedGrid
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_FinsetCandidateOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

noncomputable def finsetCandidateOrder {A : Type*} [DecidableEq A] (C : Finset A) : List C :=
  C.toList.attach.map (fun a => ⟨a.val,Finset.mem_toList.mp a.property⟩)

section CandidateKernel
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

noncomputable def requiredCandidates (H : τ → Finset ι)
    (required : List (ι × τ) → Bool) (address : List (ι × τ))
    (focus : Finset ι) (parent : Option τ) : Finset (gridCandidates H focus parent) :=
  Finset.univ.filter (fun a => required (a.val :: address))

noncomputable def markedChildKernel (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (required : List (ι × τ) → Bool) (d : ℕ) (address : List (ι × τ))
    (focus : Finset ι) (parent : Option τ)
    (a : gridCandidates H focus parent) (u : Fin N) : PMF (Bool × Bool) :=
  ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
    (markedGridQueryDepth H N required d u.val (a.val :: address)
      ((H a.val.2).erase a.val.1) (some a.val.2))

end CandidateKernel
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave

def prefixWeight (w : ℕ → ℝ) (t : ℕ) : ℝ := ∑ i ∈ Finset.range t, w i

def orderedWeight (w : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | j + 1, t => ∑ i ∈ Finset.range t, w i * orderedWeight w j i

@[simp] theorem prefixWeight_zero (w : ℕ → ℝ) : prefixWeight w 0 = 0 := by
  simp [prefixWeight]

@[simp] theorem prefixWeight_succ (w : ℕ → ℝ) (t : ℕ) :
    prefixWeight w (t + 1) = prefixWeight w t + w t := Finset.sum_range_succ _ _

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_PathRequired
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave

def pathRequired {A : Type*} [DecidableEq A] (path address : List A) : Bool :=
  decide (address.reverse <+: path)

section PathVisitation
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

def LegalQueryPath (H : τ → Finset ι) : Finset ι → Option τ → List (ι × τ) → Prop
  | _, _, [] => True
  | focus, parent, a :: as => a ∈ gridCandidates H focus parent ∧
      LegalQueryPath H ((H a.2).erase a.1) (some a.2) as

noncomputable def pathVisitProbability (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) (path : List (ι × τ)) : ℝ :=
  markedGood (ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
    (markedGridQueryDepth H N (pathRequired path) d k [] focus parent))

def GridRowQuality (H : τ → Finset ι) (N : ℕ) [NeZero N] (b : ℕ → ℝ) : Prop :=
  (∀ t ≤ N, ∀ (e : ι) (T : τ), e ∈ H T →
    (7/8 : ℝ) ≤ gridCandidateFailure H N t e T) ∧
  (∀ t ≤ N, ∀ (e : ι) (T : τ), e ∈ H T →
    gridAnswerProbability H N N t ((H T).erase e) (some T) ≤ (9/8 : ℝ)*b t)

end PathVisitation
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_CallPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave
section LegalPathCover
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

def callAtPath (H : τ → Finset ι) : QueryCall ι τ → List (ι × τ) → QueryCall ι τ
  | c, [] => c
  | c, a :: as => callAtPath H ⟨a :: c.address,(H a.2).erase a.1,some a.2⟩ as

noncomputable def legalPaths (H : τ → Finset ι) : ℕ → Finset ι → Option τ → Finset (List (ι × τ))
  | 0, _, _ => {[]}
  | d+1, focus, parent => insert [] ((gridCandidates H focus parent).biUnion
      (fun a => (legalPaths H d ((H a.2).erase a.1) (some a.2)).image (List.cons a)))

end LegalPathCover
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_Separated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave
section CandidateUniqueness
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

def QueryCall.Separated (H : τ → Finset ι) (c : QueryCall ι τ) : Prop :=
  ∀ T, some T ≠ c.parent → ((H T) ∩ c.focus).card ≤ 1

end CandidateUniqueness
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_VertexCall
attribute [-instance] _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.RecordedCallForest
variable {n : ℕ} {G : Graph n} {c : QueryCall (Finset (Fin n)) (Finset (Fin n))}
variable (F : RecordedCallForest (triangleHypergraph G) c)

def vertexCall (v : Fin F.vertexCount) : Fin F.size :=
  if hv : F.rootCount ≤ v.val then F.callIndex v hv else F.root

end SharpTerminalLeave.RecordedCallForest

open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_WitnessDimensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave

abbrev WitnessDimensions (R d : ℕ) :=
  {q : Fin (R+2*d+1) × Fin (2*d+1) // q.1.val = R+q.2.val}

def dimensionBirth {R d : ℕ} (q : WitnessDimensions R d) : Fin q.val.2 → Fin q.val.1 :=
  fun i => ⟨R+i.val,by have hi := i.isLt; have hq := q.property; omega⟩

abbrev BoundedEmbeddedWitness {n : ℕ} (G : Graph n) (R d : ℕ) :=
  Σ q : WitnessDimensions R d,
    Σ E : {E : Graph q.val.1 // E ∈ seedPatternChoices q.val.1 R},
      Σ w : IndexedWitnessCode E.val (dimensionBirth q) (suffixProjection q.property),
        {ψ : Fin q.val.1 ↪ Fin n // ψ ∈ graphEmbeddingSet (decodeWitnessPattern w).2 G}

noncomputable instance instFintypeBoundedEmbeddedWitness {n : ℕ} (G : Graph n) (R d : ℕ) :
    Fintype (BoundedEmbeddedWitness G R d) := by
  classical
  unfold BoundedEmbeddedWitness
  infer_instance

def embeddedWitnessPaths {n R d : ℕ} {G : Graph n} (W : BoundedEmbeddedWitness G R d) :
    List (Finset (Fin n) × Finset (Fin n)) × List (Finset (Fin n) × Finset (Fin n)) :=
  let q := W.1
  let w := W.2.2.1
  let ψ := W.2.2.2.val
  let key := indexedTriangleKey (dimensionBirth q) w.2.2.val ψ
  ((suffixProjection q.property w.1.1).elim [] (w.2.1.val.address key) |>.reverse,
   (suffixProjection q.property w.1.2).elim [] (w.2.1.val.address key) |>.reverse)

end SharpTerminalLeave

open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_EmbeddedWitnessRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave

noncomputable def embeddedWitnessRoots {n R d : ℕ} {G : Graph n}
    (W : BoundedEmbeddedWitness G R d) : Graph n :=
  W.2.1.val.image (fun e => e.image W.2.2.2.val)

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_EmptyRootInjection
attribute [-instance] _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

noncomputable def emptyRootInjection {k n : ℕ} (T : RootedTemplate k) (hT : T.roots = ∅) :
    {x // x ∈ T.roots} ↪ Fin n where
  toFun x := False.elim (by simpa [hT] using x.property)
  inj' := by intro x; exact False.elim (by simpa [hT] using x.property)

def unrootedTemplate {N : ℕ} (E : Graph N) (hE : ∀ e ∈ E, e.card = 2) : RootedTemplate N where
  edges := E
  roots := ∅
  simple := hE
  independent := by
    intro e he hemp
    have hz : e = ∅ := Finset.subset_empty.mp hemp
    have hh := hE e he
    rw [hz,Finset.card_empty] at hh
    omega

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_GraphEmbeddings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave

section RootExtension
variable {A V : Type*} [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]
variable (H : SimpleGraph A) (G : SimpleGraph V)

noncomputable def graphEmbeddings : Finset (A ↪ V) := by
  classical
  exact Finset.univ.filter (fun f => ∀ a b, H.Adj a b → G.Adj (f a) (f b))

noncomputable def rootedEmbeddingFiber (S : Finset A) (ψ : A → V) : Finset (A ↪ V) := by
  classical
  exact (graphEmbeddings H G).filter (fun f => ∀ a ∈ S, f a = ψ a)

end RootExtension
end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_ReindexSetImage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

@[simp] lemma reindexSet_image {N : ℕ} (s : Finset (Fin N)) (J : Finset (Fin s.card)) :
    reindexSet s (J.image (s.orderEmbOfFin rfl)) = J := by
  ext i
  simp only [mem_reindexSet,Finset.mem_image]
  constructor
  · rintro ⟨j,hj,he⟩
    exact (s.orderEmbOfFin rfl).injective he ▸ hj
  · intro hi
    exact ⟨i,hi,rfl⟩

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_SuffixBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.BirthGraph
variable {N : ℕ} (B : BirthGraph N)

def suffixBoundary (Z : Finset (Fin N)) (a b : Fin N) : Finset (Fin N) :=
  ((Z.biUnion B.older) ∪ {a,b}) \ Z

def suffixVertices (Z : Finset (Fin N)) (a b : Fin N) : Finset (Fin N) :=
  Z ∪ B.suffixBoundary Z a b

def suffixEdges (Z : Finset (Fin N)) (a b : Fin N) : Finset (Finset (Fin N)) :=
  insert {a,b} (B.backEdges Z)

lemma suffixBoundary_disjoint (Z : Finset (Fin N)) (a b : Fin N) :
    Disjoint (B.suffixBoundary Z a b) Z := Finset.sdiff_disjoint

lemma mem_suffixBoundary (Z : Finset (Fin N)) (a b x : Fin N) :
    x ∈ B.suffixBoundary Z a b ↔
      ((∃ v ∈ Z, x ∈ B.older v) ∨ x = a ∨ x = b) ∧ x ∉ Z := by
  simp only [suffixBoundary,Finset.mem_sdiff,Finset.mem_union,Finset.mem_biUnion,
    Finset.mem_insert,Finset.mem_singleton]

lemma suffixEdges_simple {Z : Finset (Fin N)} {a b : Fin N} (hab : a ≠ b) :
    ∀ e ∈ B.suffixEdges Z a b, e.card = 2 := by
  intro e he
  rcases Finset.mem_insert.mp he with rfl | he
  · exact Finset.card_pair hab
  · obtain ⟨v,_,u,hu,rfl⟩ := B.backEdges_mem_pair he
    exact Finset.card_pair (ne_of_lt (B.older_lt v u hu))

lemma suffixEdges_subset_vertices {Z : Finset (Fin N)} {a b : Fin N} :
    ∀ e ∈ B.suffixEdges Z a b, e ⊆ B.suffixVertices Z a b := by
  intro e he x hx
  apply Finset.mem_union.mpr
  by_cases hxZ : x ∈ Z
  · exact Or.inl hxZ
  · apply Or.inr
    apply (B.mem_suffixBoundary Z a b x).mpr
    refine ⟨?_,hxZ⟩
    rcases Finset.mem_insert.mp he with rfl | he
    · exact Or.inr (by simpa only [Finset.mem_insert,Finset.mem_singleton] using hx)
    · obtain ⟨v,hv,u,hu,rfl⟩ := B.backEdges_mem_pair he
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Or.inl ⟨v,hv,hu⟩
      · exact False.elim (hxZ (Finset.mem_singleton.mp hx ▸ hv))

lemma suffixEdges_touch {Z : Finset (Fin N)} {a b : Fin N} (hmark : a ∈ Z ∨ b ∈ Z) :
    ∀ e ∈ B.suffixEdges Z a b, ∃ v ∈ e, v ∈ Z := by
  intro e he
  rcases Finset.mem_insert.mp he with rfl | he
  · rcases hmark with ha | hb
    · exact ⟨a,by simp,ha⟩
    · exact ⟨b,by simp,hb⟩
  · obtain ⟨v,hv,u,_,rfl⟩ := B.backEdges_mem_pair he
    exact ⟨v,by simp,hv⟩

lemma suffixBoundary_independent {Z : Finset (Fin N)} {a b : Fin N}
    (hmark : a ∈ Z ∨ b ∈ Z) :
    ∀ e ∈ B.suffixEdges Z a b, ¬ e ⊆ B.suffixBoundary Z a b := by
  intro e he hs
  obtain ⟨v,hve,hvZ⟩ := B.suffixEdges_touch hmark e he
  exact Finset.disjoint_left.mp (B.suffixBoundary_disjoint Z a b) (hs hve) hvZ

end SharpTerminalLeave.BirthGraph

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_SuffixTemplate
attribute [-instance] _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.BirthGraph
variable {N : ℕ} (B : BirthGraph N)

def suffixTemplate (Z : Finset (Fin N)) (a b : Fin N) (hab : a ≠ b)
    (hmark : a ∈ Z ∨ b ∈ Z) : RootedTemplate (B.suffixVertices Z a b).card :=
  reindexTemplate (B.suffixVertices Z a b) (B.suffixEdges Z a b) (B.suffixBoundary Z a b)
    B.suffixEdges_subset_vertices (B.suffixEdges_simple hab) (B.suffixBoundary_independent hmark)

end SharpTerminalLeave.BirthGraph

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixEmbeddings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave
section OrderedEmbeddings
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {N : ℕ} (J : SimpleGraph (Fin N)) (G : SimpleGraph V)
variable [DecidableRel J.Adj] [DecidableRel G.Adj]

noncomputable def prefixEmbeddings (k : ℕ) (hk : k ≤ N) : Finset (Fin k ↪ V) :=
  Finset.univ.filter (fun φ => ∀ i j : Fin k,
    J.Adj (Fin.castLE hk i) (Fin.castLE hk j) → G.Adj (φ i) (φ j))

variable {G J}

def dropLastEmbedding {k : ℕ} (φ : Fin (k+1) ↪ V) : Fin k ↪ V :=
  ⟨fun i => φ i.castSucc,φ.injective.comp (Fin.castSucc_injective k)⟩

omit [Fintype V] [DecidableEq V] in
@[simp] lemma dropLastEmbedding_apply {k : ℕ} (φ : Fin (k+1) ↪ V) (i : Fin k) :
    dropLastEmbedding φ i = φ i.castSucc := rfl

def compatibleNext (J : SimpleGraph (Fin N)) (G : SimpleGraph V)
    [DecidableRel J.Adj] [DecidableRel G.Adj] {k : ℕ} (hk : k+1 ≤ N)
    (ψ : Fin k ↪ V) : Finset V := Finset.univ.filter (fun z =>
      ∀ i : Fin k, J.Adj (Fin.castLE (by omega) i) ⟨k,by omega⟩ → G.Adj (ψ i) z)

end OrderedEmbeddings
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_InitialAssignmentSet
attribute [-instance] _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.BirthGraph
variable {N n : ℕ} (B : BirthGraph N) (G : Graph n)

noncomputable def initialAssignmentSet (k : ℕ) (hk : k ≤ N) :
    Finset ({x // x ∈ initialVertices N k} ↪ Fin n) := by
  classical
  exact (prefixEmbeddings B.graph (lookupGraph G) k hk).image initialSubtypeLabel

end SharpTerminalLeave.BirthGraph

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_RootClosers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

namespace BirthGraph
variable {N : ℕ} (B : BirthGraph N)

noncomputable def rootClosers (R : ℕ) : Finset ℕ :=
  ((initialVertices N R).filter (fun v => (B.older v).Nonempty)).image Fin.val

end BirthGraph
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_WitnessEmbeddingBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

def WitnessEmbeddingBound {n R d : ℕ} {G : Graph n}
    (r : ℕ) (W : BoundedEmbeddedWitness G R d) : Prop :=
  ((graphEmbeddingSet (decodeWitnessPattern W.2.2.1).2 G).card : ℝ) ≤
    (4*prefixM n)^r * (2*prefixD n)^W.1.val.2.val / prefixD n^50

end SharpTerminalLeave

open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

noncomputable instance instFintypeIndexedWitnessCodeEmbeddingBound {K s : ℕ}
    (E : Graph K) (birth : Fin s → Fin K)
    (mark : Fin K → Option (Fin s)) : Fintype (IndexedWitnessCode E birth mark) := by
  classical
  unfold IndexedWitnessCode
  infer_instance

end SharpTerminalLeave

open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_CheckMarkedTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave.ExposureTree
variable {K V R : Type*}

def checkMarkedTrace : List (Bool × ExposureTree K V (Bool × Bool × List R)) →
    ExposureTree K V (Bool × Bool × List R)
  | [] => .done (true,true,[])
  | a :: as => bind a.2 (fun z =>
      if z.1 then .done (false,((!a.1)||z.2.1) && !(as.any Prod.fst),z.2.2)
      else mapOutput (fun y => (y.1,((!a.1)||z.2.1) && y.2.1,z.2.2 ++ y.2.2))
        (checkMarkedTrace as))

end SharpTerminalLeave.ExposureTree

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_JointMarkedQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave
section MarkedTrace
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

noncomputable def jointMarkedQuery (H : τ → Finset ι) (N : ℕ)
    (required : List (ι × τ) → Bool) :
    ℕ → ℕ → QueryCall ι τ → ExposureTree τ (Fin N) (Bool × Bool × List (QueryCall ι τ))
  | 0, _, c => ExposureTree.bind
      (ExposureTree.exposeLabeled Prod.snd (gridCandidates H c.focus c.parent).toList)
      (fun _ => .done (true,true,[c]))
  | d+1, k, c => ExposureTree.bind
      (ExposureTree.exposeLabeled Prod.snd (gridCandidates H c.focus c.parent).toList)
      (fun values => ExposureTree.mapOutput (fun z => (z.1,z.2.1,c :: z.2.2))
        (ExposureTree.checkMarkedTrace
          ((values.mergeSort (fun a b => a.2.val ≤ b.2.val)).map
            (fun p => (required (p.1 :: c.address), if p.2.val < k then
              jointMarkedQuery H N required d p.2.val
                ⟨p.1 :: c.address,(H p.1.2).erase p.1.1,some p.1.2⟩
              else .done (false,false,[]))))))

end MarkedTrace
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_PathVisitProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave

section TracePathProbability
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

noncomputable def actualPathVisitProbability (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) (path : List (ι × τ)) : ℝ :=
  (((ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
    (tracedGridQuery H N d k ⟨[],focus,parent⟩)).map
      (fun z => z.2.any (fun c => decide (c.address = path.reverse)))) true).toReal

end TracePathProbability
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_PairRequired
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave

def pairRequired {A : Type*} [DecidableEq A] (p q address : List A) : Bool :=
  pathRequired p address || pathRequired q address

section ForkVisitation
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

noncomputable def pairVisitProbability (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) (p q : List (ι × τ)) : ℝ :=
  markedGood (ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
    (markedGridQueryDepth H N (pairRequired p q) d k [] focus parent))

end ForkVisitation
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_PairVisitProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave
section TracePairProbability
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

noncomputable def actualPairVisitProbability (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ)
    (path₁ path₂ : List (ι × τ)) : ℝ :=
  (((ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
    (tracedGridQuery H N d k ⟨[],focus,parent⟩)).map
      (fun z => z.2.any (fun c => decide (c.address = path₁.reverse)) &&
        z.2.any (fun c => decide (c.address = path₂.reverse)))) true).toReal

end TracePairProbability
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_ActiveHypergraph
attribute [-instance] _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

def activeHypergraph {n : ℕ} (G : Graph n) (T : ↥(triangles G)) : Finset ↥G :=
  Finset.univ.filter (fun e => e.val ∈ T.val.powersetCard 2)

def edgeEmbedding {n : ℕ} (G : Graph n) : ↥G ↪ Finset (Fin n) :=
  ⟨Subtype.val, Subtype.val_injective⟩

def triangleEmbedding {n : ℕ} (G : Graph n) : ↥(triangles G) ↪ Finset (Fin n) :=
  ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem activeHypergraph_mem {n : ℕ} (G : Graph n)
    (T : ↥(triangles G)) (e : ↥G) : e ∈ activeHypergraph G T ↔ e.val ∈ T.val.powersetCard 2 := by
  simp only [activeHypergraph, Finset.mem_filter, Finset.mem_univ, true_and]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Stability_Volterra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory

namespace SharpTerminalLeave

section Volterra
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

noncomputable def volterra (P R : A) (f : ℝ → A) (s : ℝ) : A :=
  ∫ t in (0 : ℝ)..s, NormedSpace.exp ((t - s) • P) * R * f t

noncomputable def volterraIter (P R : A) (f : ℝ → A) : ℕ → ℝ → A
  | 0 => f
  | k + 1 => volterra P R (volterraIter P R f k)

end Volterra
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_MatrixInfinityAlgHom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave
noncomputable def matrixInfinityAlgHom {I : Type*} [Fintype I] [DecidableEq I] :
    Matrix I I ℝ →ₐ[ℝ] ((I → ℝ) →L[ℝ] (I → ℝ)) :=
  (Matrix.toLinAlgEquiv'.trans (Module.End.toContinuousLinearMap (I → ℝ))).toAlgHom

@[simp] theorem matrixInfinityAlgHom_apply {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (z : I → ℝ) (i : I) :
    matrixInfinityAlgHom A z i = ∑ j, A i j * z j := rfl

open scoped Matrix.Norms.Operator in

@[simp] theorem matrixInfinityAlgHom_norm {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) : ‖matrixInfinityAlgHom A‖ = ‖A‖ :=
  (Matrix.linfty_opNorm_eq_opNorm A).symm

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_CompleteEdge
attribute [-instance] _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Classical Matrix

namespace SharpTerminalLeave

abbrev CompleteEdge (n : ℕ) := ↥(completeGraph n)

def graphActive {n : ℕ} (G : Graph n) : Finset (CompleteEdge n) :=
  Finset.univ.filter (fun e => e.val ∈ G)

@[simp] lemma mem_graphActive {n : ℕ} (G : Graph n) (e : CompleteEdge n) :
    e ∈ graphActive G ↔ e.val ∈ G := by simp [graphActive]

def graphEdgeEmbed {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) : G ↪ CompleteEdge n :=
  ⟨fun e => ⟨e.val,hG e.property⟩,fun _ _ h => Subtype.ext (congrArg (fun e : CompleteEdge n => e.val) h)⟩

def graphRestrict {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) :
    (CompleteEdge n → ℝ) →ₗ[ℝ] (G → ℝ) where
  toFun x e := x (graphEdgeEmbed G hG e)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def graphExtend {n : ℕ} (G : Graph n) : (G → ℝ) →ₗ[ℝ] (CompleteEdge n → ℝ) where
  toFun z e := if he : e.val ∈ G then z ⟨e.val,he⟩ else 0
  map_add' _ _ := by funext e; by_cases he : e.val ∈ G <;> simp [he]
  map_smul' _ _ := by funext e; by_cases he : e.val ∈ G <;> simp [he]

@[simp] lemma graphRestrict_extend {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (z : G → ℝ) :
    graphRestrict G hG (graphExtend G z) = z := by
  funext e
  change (if he : e.val ∈ G then z ⟨e.val,he⟩ else 0) = z e
  simp only [dite_eq_left e.property]

noncomputable def graphMatrixLift {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (M : Matrix G G ℝ) : Module.End ℝ (CompleteEdge n → ℝ) :=
  (graphExtend G).comp ((Matrix.toLin' M).comp (graphRestrict G hG))

@[simp] lemma graphMatrixLift_restrict {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (M : Matrix G G ℝ) (x : CompleteEdge n → ℝ) :
    graphRestrict G hG (graphMatrixLift G hG M x) = M *ᵥ (graphRestrict G hG x) := by
  simp [graphMatrixLift]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_StarInclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace SharpTerminalLeave

variable {E U : Type*} [Fintype E] [DecidableEq E] [Fintype U]

def starInclusion (S : Finset E) : Matrix E S ℝ :=
  fun e f => if e = f.val then 1 else 0

noncomputable def extendStar (S : Finset E) (M : Matrix S S ℝ) : Matrix E E ℝ :=
  starInclusion S * M * (starInclusion S)ᴴ

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_EdgeStar
attribute [-instance] _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace SharpTerminalLeave

def edgeStar {n : ℕ} (G : Graph n) (u : Fin n) : Finset G :=
  Finset.univ.filter (fun e => u ∈ e.val)

@[simp] theorem mem_edgeStar {n : ℕ} (G : Graph n) (u : Fin n) (e : G) :
    e ∈ edgeStar G u ↔ u ∈ e.val := by simp [edgeStar]

def neighborEdge {n : ℕ} (G : Graph n) (u : Fin n) (v : neighbors G u) : edgeStar G u :=
  ⟨⟨{u,v.val},(Finset.mem_filter.mp v.property).2⟩,by simp⟩

theorem neighborEdge_injective {n : ℕ} (G : Graph n) (u : Fin n) :
    Function.Injective (neighborEdge G u) := by
  intro v w h
  have he : ({u,v.val} : Finset (Fin n)) = {u,w.val} := congrArg (fun e => e.val.val) h
  have hv : v.val ∈ ({u,w.val} : Finset (Fin n)) := he ▸ (by simp)
  have hw : w.val ∈ ({u,v.val} : Finset (Fin n)) := he.symm ▸ (by simp)
  simp only [Finset.mem_insert,Finset.mem_singleton] at hv hw
  apply Subtype.ext
  rcases hv with hv | hv
  · rcases hw with hw | hw
    · exact hv.trans hw.symm
    · exact hw.symm
  · exact hv

theorem neighborEdge_surjective {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (u : Fin n) :
    Function.Surjective (neighborEdge G u) := by
  intro e
  obtain ⟨a,b,hab,he⟩ := Finset.card_eq_two.mp (mem_completeGraph.mp (hG e.val.property))
  have hu : u ∈ e.val.val := (mem_edgeStar G u e.val).mp e.property
  rw [he] at hu
  simp only [Finset.mem_insert,Finset.mem_singleton] at hu
  have hm : ({a,b} : Finset (Fin n)) ∈ G := he ▸ e.val.property
  rcases hu with rfl | rfl
  · refine ⟨⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm⟩⟩,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact he.symm
  · refine ⟨⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩,?_⟩
    · simpa only [Finset.pair_comm] using hm
    · apply Subtype.ext
      apply Subtype.ext
      exact (Finset.pair_comm _ _).trans he.symm

noncomputable def neighborEdgeEquiv {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (u : Fin n) :
    neighbors G u ≃ edgeStar G u :=
  Equiv.ofBijective (neighborEdge G u) ⟨neighborEdge_injective G u,neighborEdge_surjective G hG u⟩

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_LinkSimpleGraph
attribute [-instance] _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave

def linkSimpleGraph {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (u : Fin n) :
    SimpleGraph (neighbors G u) where
  Adj x y := {x.val, y.val} ∈ G
  symm := ⟨by intro x y h; simpa only [Finset.pair_comm] using h⟩
  loopless := ⟨by
    intro x h
    have hh := mem_completeGraph.mp (hG h)
    simp at hh⟩

instance linkSimpleGraph_decidable {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (u : Fin n) :
    DecidableRel (linkSimpleGraph G hG u).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ G))

@[simp] theorem linkSimpleGraph_adj {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (u : Fin n) (v w : neighbors G u) :
    (linkSimpleGraph G hG u).Adj v w ↔ {v.val,w.val} ∈ G := Iff.rfl

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_EigenProjector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace SharpTerminalLeave

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def eigenProjector (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (i : ι) :
    Matrix ι ι ℝ :=
  Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
    (Matrix.diagonal (Pi.single i (1 : ℝ)))

end SharpTerminalLeave

open scoped BigOperators NNReal
open Matrix

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_NormalizedOnes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace

namespace SharpTerminalLeave

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

noncomputable def normalizedOnes : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun _ => (Real.sqrt (Fintype.card ι : ℝ))⁻¹)

noncomputable def averagingProjector : Matrix ι ι ℝ :=
  fun _ _ => (Fintype.card ι : ℝ)⁻¹

end SharpTerminalLeave

open scoped BigOperators

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_ClosedWalkPattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave

section WalkPatterns
variable {r k : ℕ}

def closedWalkPattern (σ : Fin r → Fin k) : SimpleGraph (Fin k) :=
  (SimpleGraph.cycleGraph r).map σ

def PatternProper (σ : Fin r → Fin k) : Prop :=
  ∀ i j, (SimpleGraph.cycleGraph r).Adj i j → σ i ≠ σ j

noncomputable def patternHom (σ : Fin r → Fin k) (hσ : PatternProper σ) :
    SimpleGraph.cycleGraph r →g closedWalkPattern σ :=
  SimpleGraph.Hom.map σ _ (fun hij => hσ _ _ hij)

@[simp] lemma patternHom_apply (σ : Fin r → Fin k) (hσ : PatternProper σ) (i : Fin r) :
    patternHom σ hσ i = σ i := rfl

end WalkPatterns

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_ClosedWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave
section ClosedWords
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def closedWords (r : ℕ) : Finset (Fin r → V) := by
  classical
  exact Finset.univ.filter (fun f => ∀ i j, (SimpleGraph.cycleGraph r).Adj i j →
    G.Adj (f i) (f j))

noncomputable def nonsimpleWords (r : ℕ) : Finset (Fin r → V) := by
  classical
  exact (closedWords G r).filter (fun f => ¬Function.Injective f)

end ClosedWords
end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_ClosedWalkFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace
open scoped BigOperators

namespace SharpTerminalLeave
section TraceBridge
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev closedWalkFamily (r : ℕ) := Σ v : V, {p : G.Walk v v // p.length = r}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in

lemma wordOfWalk_adj {r : ℕ} {a : V} (p : G.Walk a a) (hp : p.length = r)
    (i j : Fin r) (hij : (SimpleGraph.cycleGraph r).Adj i j) :
    G.Adj (p.getVert i.val) (p.getVert j.val) := by
  obtain ⟨x,hx⟩ := i
  obtain ⟨y,hy⟩ := j
  have hne : x ≠ y := by
    intro h
    subst y
    exact hij.ne rfl
  wlog hgt : x > y generalizing x y
  · exact (this y hy x hx hij.symm hne.symm (by omega)).symm
  rcases SimpleGraph.cycleGraph_adj'.mp hij with h | h
  · rw [Fin.sub_val_of_le (show (⟨y, hy⟩ : Fin r) ≤ ⟨x, hx⟩ from hgt.le)] at h
    dsimp only at h
    have heq : x = y+1 := by omega
    subst x
    exact (p.adj_getVert_succ (by omega : y < p.length)).symm
  · rw [Fin.coe_sub_iff_lt.mpr hgt] at h
    dsimp only at h
    have hx' : x = r-1 := by omega
    have hy' : y = 0 := by omega
    subst x; subst y
    have hlast := p.adj_getVert_succ (by omega : r-1 < p.length)
    simpa only [show r-1+1 = p.length by omega, SimpleGraph.Walk.getVert_length,
      SimpleGraph.Walk.getVert_zero] using hlast

noncomputable def wordOfWalk {r : ℕ} (p : closedWalkFamily G r) : closedWords G r :=
  ⟨fun i => p.2.1.getVert i.val, by
    classical
    simp only [closedWords, Finset.mem_filter, Finset.mem_univ, true_and]
    exact wordOfWalk_adj G p.2.1 p.2.2⟩

noncomputable def walkOfWord (n : ℕ) (f : closedWords G (n+3)) :
    closedWalkFamily G (n+3) := by
  let h : SimpleGraph.cycleGraph (n+3) →g G := ⟨f.val, by
    have hf := f.property
    simpa only [closedWords, Finset.mem_filter, Finset.mem_univ, true_and] using hf⟩
  exact ⟨f.val 0, (SimpleGraph.cycleGraph.cycle n).map h, by
    change ((SimpleGraph.cycleGraph.cycle n).map h).length = n+3
    rw [SimpleGraph.Walk.length_map, SimpleGraph.cycleGraph.length_cycle]⟩

end TraceBridge
end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_LinkStarMatrix
attribute [-instance] _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace SharpTerminalLeave
open scoped Matrix.Norms.L2Operator

noncomputable def linkStarMatrix {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (u : Fin n) :
    Matrix (edgeStar G u) (edgeStar G u) ℝ :=
  Matrix.reindex (neighborEdgeEquiv G hG u) (neighborEdgeEquiv G hG u)
    ((linkSimpleGraph G hG u).adjMatrix ℝ)

noncomputable def globalLinkAdjacency {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) :
    Matrix G G ℝ := ∑ u, extendStar (edgeStar G u) (linkStarMatrix G hG u)

noncomputable def globalStarAverage {n : ℕ} (G : Graph n) : Matrix G G ℝ :=
  ∑ u, extendStar (edgeStar G u) averagingProjector

noncomputable def prefixSpectralError (n : ℕ) (c : ℝ) : ℝ :=
  4 * ((8001 : ℝ) * (n : ℝ)^(-c) + (8000 : ℝ)^8001 * 2^8000 *
    ((n : ℝ) / prefixD n^4000 + 1/prefixD n)) ^ (1 / (8000 : ℝ)) + 7*(n : ℝ)^(-c)

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_GridCollision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

section Continuum
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

noncomputable def gridCollision (H : τ → Finset ι) (focus : Finset ι)
    (parent : Option τ) (n : ℕ) : ℝ :=
  trueProbability ((ExposureTree.freshRecorded (gridPriorities (n + 1))
    (gridQueryDepth H (n + 1) (n + 1) (n + 1) focus parent) ∅).map Prod.snd)

noncomputable def collisionCost (H : τ → Finset ι) (focus : Finset ι)
    (parent : Option τ) : ℝ :=
  Filter.liminf (gridCollision H focus parent) atTop

end Continuum

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_IncidenceDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
open scoped BigOperators Topology NNReal Matrix.Norms.Operator
open MeasureTheory

namespace SharpTerminalLeave

def incidenceDegree {ι κ : Type*} [Fintype ι] (U : Matrix ι κ ℝ) (v : κ) : ℝ :=
  ∑ e, U e v

noncomputable def starAverage {ι κ : Type*} [Fintype ι] (U : Matrix ι κ ℝ) :
    Matrix κ ι ℝ := fun v e => U e v / incidenceDegree U v

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_EdgeIncidence
attribute [-instance] _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
open scoped BigOperators Topology NNReal Matrix.Norms.Operator
open MeasureTheory

namespace SharpTerminalLeave
open scoped Matrix.Norms.Operator

noncomputable def edgeIncidence {n : ℕ} (G : Graph n) : Matrix G (Fin n) ℝ :=
  fun e u => if u ∈ e.val then 1 else 0

end SharpTerminalLeave

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_MatrixEuclideanAlgHom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory

namespace SharpTerminalLeave

noncomputable def matrixEuclideanAlgHom {I : Type*} [Fintype I] [DecidableEq I] :
    Matrix I I ℝ →ₐ[ℝ] (EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I) :=
  (Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ)).toAlgEquiv.toAlgHom

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Stability_CavityGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

section
open scoped BigOperators Topology BoundedContinuousFunction
open scoped BigOperators
open Filter MeasureTheory
open scoped Topology

namespace SharpTerminalLeave
section CavityStability
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

noncomputable def cavityGenerator (H : τ → Finset ι) (D : ℝ) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun e => (1 / D) •
    ∑ T ∈ messageCandidates H e none, ∑ f ∈ (H T).erase e, ContinuousLinearMap.proj f

omit [Fintype ι] in
@[simp] theorem cavityGenerator_apply (H : τ → Finset ι) (D : ℝ) (z : ι → ℝ) (e : ι) :
    cavityGenerator H D z e = (1 / D) *
      ∑ T ∈ messageCandidates H e none, ∑ f ∈ (H T).erase e, z f := by
  simp [cavityGenerator]

noncomputable def cavityVelocity (H : τ → Finset ι) (D : ℝ) (s : ℝ) (e : ι) : ℝ :=
  1 - Real.exp (2 * s) / D * ∑ T ∈ messageCandidates H e none,
     (∏ f ∈ (H T).erase e, cavityLimit H f (some T) (cavityTime D s)) /
       (1 - cavityMessage H D e T s)

noncomputable def cavityResidual (H : τ → Finset ι) (D : ℝ) (s : ℝ) : ι → ℝ :=
  cavityVelocity H D s + cavityGenerator H D (fun e => cavityLog H D e s)

noncomputable def cavityIncidentMessages (H : τ → Finset ι) (D s : ℝ) : ι × τ → ℝ :=
  fun p => if p.1 ∈ H p.2 then cavityMessage H D p.1 p.2 s else 0

@[simp] theorem cavityIncidentMessages_zero (H : τ → Finset ι) (D : ℝ) :
    cavityIncidentMessages H D 0 = 0 := by
  ext p
  simp [cavityIncidentMessages]

end CavityStability
end SharpTerminalLeave

end

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixHorizon
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

noncomputable def prefixHorizon (n : ℕ) : ℝ := Real.log (1+2*prefixD n)/2

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Stability_CavityReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

noncomputable def cavityReference (D t : ℝ) : ℝ := (1+2*D*t)^(-(1/2 : ℝ))
noncomputable def cavityClock (D t : ℝ) : ℝ := Real.log (1+2*D*t)/2

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_WitnessMu
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave

noncomputable def witnessMu (D : ℝ) : ℝ := Real.log (1 + 2 * D) / (2 * D)

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_WitnessDimensionEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

def witnessDimensionEquiv (R d : ℕ) : WitnessDimensions R d ≃ Fin (2*d+1) where
  toFun q := q.val.2
  invFun s := ⟨(⟨R+s.val,by have h := s.isLt; omega⟩,s),rfl⟩
  left_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      exact q.property.symm
    · rfl
  right_inv _ := rfl

end SharpTerminalLeave

open Filter
open scoped BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_DivergentArms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave

def DivergentArms {A : Type*} (p q : List A) : Prop :=
  match p,q with
  | a :: _, b :: _ => a ≠ b
  | _,_ => True

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_SplitQueryPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave

def splitQueryPaths {A : Type*} [DecidableEq A] : List A → List A → List A × List A × List A
  | [], q => ([],[],q)
  | p, [] => ([],p,[])
  | a :: p, b :: q => if a = b then
      let s := splitQueryPaths p q
      (a :: s.1,s.2.1,s.2.2)
    else ([],a :: p,b :: q)

noncomputable def pairFactorialWeight {A : Type*} [DecidableEq A] (x : ℝ) (p q : List A) : ℝ :=
  let s := splitQueryPaths p q
  x ^ (s.1.length+s.2.1.length+s.2.2.length) /
    ((s.1.length.factorial : ℝ)*(s.2.1.length.factorial : ℝ)*(s.2.2.length.factorial : ℝ))

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixCodeSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

def prefixCodeSet {A : Type*} [DecidableEq A] : List A → Finset (List A)
  | [] => ∅
  | a::p => insert [a] ((prefixCodeSet p).image (List.cons a))

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_AddressHead
attribute [-instance] _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

noncomputable instance indexedWitnessCodeAddressFintype {K s : ℕ} (E : Graph K) (birth : Fin s → Fin K)
    (mark : Fin K → Option (Fin s)) : Fintype (IndexedWitnessCode E birth mark) := by
  classical
  unfold IndexedWitnessCode
  infer_instance

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_LegalCollisionPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave
section CollisionPathSum
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

noncomputable def tracedCollisionProbability (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) : ℝ :=
  (((ExposureTree.freshLog (gridPriorities N)
    (tracedGridQuery H N d k ⟨[],focus,parent⟩)).map
      (fun z => ExposureTree.repeats ∅ z.2)) true).toReal

end CollisionPathSum

end SharpTerminalLeave

open Filter
open scoped BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_RootedCountedTracedRepeat
attribute [-instance] _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

noncomputable instance rootedCountedTracedRepeatIndexedWitnessCodeFintype
    {K s : ℕ} (E : Graph K) (birth : Fin s → Fin K)
    (mark : Fin K → Option (Fin s)) : Fintype (IndexedWitnessCode E birth mark) := by
  classical
  unfold IndexedWitnessCode
  infer_instance

end SharpTerminalLeave

open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_CanonicalCollisionSum
attribute [-instance] _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

noncomputable instance canonicalCollisionSumIndexedWitnessCodeFintype
    {K s : ℕ} (E : Graph K) (birth : Fin s → Fin K)
    (mark : Fin K → Option (Fin s)) : Fintype (IndexedWitnessCode E birth mark) := by
  classical
  unfold IndexedWitnessCode
  infer_instance

end SharpTerminalLeave

open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_EdgeFamilyDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave
section RootOverlap
variable {V : Type*} [Fintype V] [DecidableEq V]

def edgeFamilyDegree (G : Finset (Finset V)) (v : V) : ℕ :=
  (G.filter (fun e => v ∈ e)).card

noncomputable def rootOverlap (G : Finset (Finset V)) (hne : G.Nonempty) : ℝ := by
  classical
  exact pmfMean (PMF.uniformOfFinset G hne) (fun e =>
    pmfMean (PMF.uniformOfFinset G hne) (fun f => if ¬Disjoint e f then 1 else 0))

end RootOverlap
end SharpTerminalLeave

open Filter
open scoped BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Stability_CavityWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

noncomputable def cavityWeight (D t : ℝ) : ℝ := 1/(1+2*D*t)

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_CodegreeNoiseRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

noncomputable def codegreeNoiseRadius (n : ℕ) : ℝ := (n : ℝ)^(-1/10000 : ℝ)
noncomputable def codegreeNoiseDenominator (n : ℕ) : ℝ :=
  4*((6/prefixD n)*(4+8*Real.log n+codegreeNoiseRadius n+6/prefixD n)+
    (6/prefixD n)*codegreeNoiseRadius n)

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixCodegreeNoiseExit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

def PrefixCodegreeNoiseExit {n : ℕ} (u v : Fin n)
    (ω : History (Graph n) (prefixTime n)) : Prop :=
  ∃ j ≤ prefixTime n,
    (∀ k < j, (currentCodegree (ω (historyIndex (prefixTime n) k)) u v : ℝ) ≤
      2*earlyTemplateScale 1 2 n k) ∧
    codegreeNoiseRadius n ≤ |historyNoise (fun _ => step)
      (fun k H => (currentCodegree H u v : ℝ)/earlyTemplateScale 1 2 n k)
      (prefixTime n) j ω|

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_HistoryCompensator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

noncomputable def historyCompensator {α : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (f : ℕ → α → ℝ) (T j : ℕ)
    (ω : History α T) : ℝ :=
  historyCounter (fun k a => pmfMean (K k a) (f (k+1))-f k a) T j ω

noncomputable def prefixNormalizedCodegree {n : ℕ} (u v : Fin n)
    (k : ℕ) (G : Graph n) : ℝ :=
  (currentCodegree G u v : ℝ)/earlyTemplateScale 1 2 n k

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_CenteredCodegreeNeighborSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

noncomputable def centeredCodegreeNeighborSum {n : ℕ} (G : Graph n)
    (u v : Fin n) (s : ℝ) : ℝ :=
  ∑ w ∈ commonNeighbors G u v,
    ((currentCodegree G u w : ℝ)+currentCodegree G v w-2*s)

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_RelativeNoiseExit
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

def RelativeNoiseExit {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (L s : ℕ → ℝ) (B r : ℝ)
    (T : ℕ) (ω : History (Graph n) T) : Prop :=
  ∃ j ≤ T, pastRelativeCopyLoadsSafe required L T j ω ∧
    (∀ k < j, copyCount required (ω (historyIndex T k)) ≤ B*s k) ∧
    r ≤ |historyNoise (fun _ => step) (fun k H => copyCount required H/s k) T j ω|

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_TriangleIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

abbrev TriangleIndex (n : ℕ) := ↥((Finset.univ : Finset (Fin n)).powersetCard 3)
def triangleRequired {n : ℕ} (t : TriangleIndex n) : Graph n := t.val.powersetCard 2

@[simp] theorem triangle_copyCount {n : ℕ} (G : Graph n) :
    copyCount (triangleRequired (n := n)) G = ((triangles G).card : ℝ) := by
  unfold copyCount triangleRequired
  rw [Finset.sum_coe_sort (Finset.univ.powersetCard 3 : Finset (Finset (Fin n))) (fun (t : Finset (Fin n)) => intact (t.powersetCard 2) G)]
  simp [intact,triangles]

@[simp] theorem triangle_copyEdgeLoad {n : ℕ} (G : Graph n) (e : Finset (Fin n)) :
    copyEdgeLoad (triangleRequired (n := n)) G e = (triangleDegree G e : ℝ) := by
  unfold copyEdgeLoad triangleRequired
  rw [Finset.sum_coe_sort (Finset.univ.powersetCard 3 : Finset (Finset (Fin n))) (fun (t : Finset (Fin n)) => if e ∈ t.powersetCard 2 then intact (t.powersetCard 2) G else 0)]
  simp only [triangleDegree,incidentTriangles,triangles,Finset.filter_filter]
  rw [Finset.card_filter,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro t ht
  unfold intact
  split_ifs <;> simp_all

noncomputable def earlyTriangleScale (n i : ℕ) : ℝ := earlyTemplateScale 3 3 n i/6
noncomputable def triangleNoiseLoad (n i : ℕ) : ℝ := 2*earlyTemplateScale 1 2 n i

def PrefixTriangleNoise (n : ℕ) (ω : History (Graph n) (prefixTime n)) : Prop :=
  ¬ RelativeNoiseExit (triangleRequired (n := n)) (triangleNoiseLoad n)
    (earlyTriangleScale n) 2 (codegreeNoiseRadius n) (prefixTime n) ω

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Stability_EdgeStabilityRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

noncomputable def edgeStabilityRate (s t Q : ℝ) : ℝ := s^2/(Q*t)
noncomputable def edgeStabilityScalar (s t Q κ : ℝ) : ℝ := s/t-1-2*edgeStabilityRate s t Q+κ*s/(Q*t)

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixCodegreeDriftTerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem complete_history_valid {n T : ℕ}
    (ω : History (Graph n) T)
    (hω : ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) T T).support) :
    ∀ j ≤ T, ω (historyIndex T j) ⊆ completeGraph n := by
  obtain ⟨hi,hp⟩ := historyLaw_path_support (PMF.pure (completeGraph n))
    (fun _ => step) T T le_rfl ω hω
  have hi' : ω (historyIndex T 0) = completeGraph n := by
    simpa only [PMF.mem_support_pure_iff] using hi
  intro j
  induction j with
  | zero =>
    intro _
    rw [hi']
  | succ j ih =>
    intro hj
    exact (step_support_subset (hp j (Nat.lt_of_succ_le hj))).trans
      (ih (Nat.le_of_succ_le hj))

end SharpTerminalLeave
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_CompleteEdgePair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical Matrix

namespace SharpTerminalLeave

noncomputable def completeEdgePair {n : ℕ} (e : CompleteEdge n) :
    {uv : Fin n × Fin n // uv.1 ≠ uv.2 ∧ e.val = {uv.1,uv.2}} := by
  have h : ∃ uv : Fin n × Fin n, uv.1 ≠ uv.2 ∧ e.val = {uv.1,uv.2} := by
    obtain ⟨u,v,huv,he⟩ := Finset.card_eq_two.mp (mem_completeGraph.mp e.property)
    exact ⟨(u,v),huv,he⟩
  exact ⟨h.choose,h.choose_spec⟩

noncomputable def centeredEdgeVector {n : ℕ} (G : Graph n) (s : ℝ) (e : CompleteEdge n) : ℝ :=
  (currentCodegree G (completeEdgePair e).val.1 (completeEdgePair e).val.2 : ℝ)/s-1

lemma history_valid_all {n T : ℕ} (ω : History (Graph n) T)
    (hω : ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) T T).support) (i : ℕ) :
    ω (historyIndex T i) ⊆ completeGraph n := by
  have hi : historyIndex T i = historyIndex T (min i T) := by simp [historyIndex]
  rw [hi]
  exact complete_history_valid ω hω _ (Nat.min_le_right _ _)

noncomputable def prefixCenteredEdge {n : ℕ} (ω : History (Graph n) (prefixTime n))
    (i : ℕ) : CompleteEdge n → ℝ :=
  centeredEdgeVector (ω (historyIndex (prefixTime n) i)) (earlyTemplateScale 1 2 n i)

noncomputable def prefixEdgeRate {n : ℕ} (ω : History (Graph n) (prefixTime n)) (i : ℕ) : ℝ :=
  edgeStabilityRate (earlyTemplateScale 1 2 n i) (earlyTemplateScale 1 2 n (i+1))
    (triangles (ω (historyIndex (prefixTime n) i))).card

noncomputable def prefixEdgeScalar {n : ℕ} (ω : History (Graph n) (prefixTime n)) (i : ℕ) : ℝ :=
  edgeStabilityScalar (earlyTemplateScale 1 2 n i) (earlyTemplateScale 1 2 n (i+1))
    (triangles (ω (historyIndex (prefixTime n) i))).card 1

noncomputable def prefixEdgeResidual {n : ℕ} (ω : History (Graph n) (prefixTime n))
    (hω : ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support)
    (i : ℕ) : Module.End ℝ (CompleteEdge n → ℝ) :=
  graphMatrixLift _ (history_valid_all ω hω i)
    ((earlyTemplateScale 1 2 n i)⁻¹ • globalLinkAdjacency _ (history_valid_all ω hω i)-globalStarAverage _)

noncomputable def prefixEdgeForcing {n : ℕ} (ω : History (Graph n) (prefixTime n))
    (i : ℕ) (e : CompleteEdge n) : ℝ :=
  prefixCenteredEdge ω 0 e+
    historyNoise (fun _ => step)
      (fun k H => (currentCodegree H (completeEdgePair e).val.1 (completeEdgePair e).val.2 : ℝ)/earlyTemplateScale 1 2 n k)
      (prefixTime n) i ω+
    ∑ k ∈ Finset.range i, prefixEdgeScalar ω k*(prefixCenteredEdge ω k e+1)

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_WheelSpoke
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

lemma cycleNext_val {j : ℕ} (i : Fin j) :
    (cycleNext i).val = if i.val+1 < j then i.val+1 else 0 := by
  unfold cycleNext
  dsimp
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have he : i.val+1 = j := by omega
    simp [he]

lemma cycleNext_ne {j : ℕ} (hj : 2 ≤ j) (i : Fin j) : cycleNext i ≠ i := by
  intro h
  have hh := congrArg Fin.val h
  rw [cycleNext_val] at hh
  split_ifs at hh <;> omega

def wheelSpoke {j : ℕ} (i : Fin j) : Finset (Fin (j+1)) := {0,i.succ}
def wheelRim {j : ℕ} (i : Fin j) : Finset (Fin (j+1)) := {i.succ,(cycleNext i).succ}

def wheelTemplate (j : ℕ) (hj : 3 ≤ j) : RootedTemplate (j+1) where
  edges := Finset.univ.image wheelSpoke ∪ Finset.univ.image wheelRim
  roots := {0}
  simple := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      simp [wheelSpoke,(Ne.symm (Fin.succ_ne_zero _))]
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      have hne : i.succ ≠ (cycleNext i).succ := by
        intro h; exact cycleNext_ne (by omega) i (Fin.succ_injective _ h).symm
      simp [wheelRim,hne]
  independent := by
    intro e he hsub
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      have hh := hsub (show i.succ ∈ wheelSpoke i by simp [wheelSpoke])
      simp at hh
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      have hh := hsub (show i.succ ∈ wheelRim i by simp [wheelRim])
      simp at hh

@[simp] lemma wheelTemplate_roots_card (j : ℕ) (hj : 3 ≤ j) :
    (wheelTemplate j hj).roots.card = 1 := Finset.card_singleton _

def wheelRoot {j n : ℕ} (hj : 3 ≤ j) (u : Fin n) :
    {v // v ∈ (wheelTemplate j hj).roots} ↪ Fin n where
  toFun := fun _ => u
  inj' := by
    intro a b _
    apply Subtype.ext
    have ha : a.val = 0 := Finset.mem_singleton.mp a.property
    have hb : b.val = 0 := Finset.mem_singleton.mp b.property
    exact ha.trans hb.symm

def wheelRestrict {j n : ℕ} (hj : 3 ≤ j) (u : Fin n)
    (φ : RootedInjection (wheelTemplate j hj) (wheelRoot hj u)) : Fin j ↪ Fin n :=
  (Fin.succEmb j).trans φ.val

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Stability_MovingResidualForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators

namespace SharpTerminalLeave
open Classical

noncomputable def movingResidualForcing {E : Type*} [Fintype E]
    (a : ℕ → ℝ) (R : ℕ → Module.End ℝ (E → ℝ)) : Module.End ℝ (ℕ → E → ℝ) where
  toFun x t := ∑ i ∈ Finset.range t, (-a i) • (R i (x i))
  map_add' x y := by
    funext t
    simp only [Pi.add_apply,map_add,smul_add,Finset.sum_add_distrib]
  map_smul' c x := by
    funext t
    simp only [Pi.smul_apply,map_smul,smul_comm (-a _) c,Finset.smul_sum,RingHom.id_apply]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_BalancedJump
attribute [-instance] _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

noncomputable def balancedJump (n : ℕ) : ℝ := (n : ℝ)^(-1/2000 : ℝ)
noncomputable def balancedLoad (H : ℕ) {k : ℕ} (T : RootedTemplate k) (n i : ℕ) : ℝ :=
  4*(T.edges.card : ℝ)*(1+Real.log (n : ℝ))^(3*H+2)*
    rootedScaling T n (earlyDensity n i)/((n : ℝ)*earlyDensity n i^2)

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixBalancedNoise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

def PrefixBalancedNoise (H n : ℕ) (ω : History (Graph n) (prefixTime n)) : Prop :=
  ∀ k ≤ H, ∀ T : RootedTemplate k, ∀ ψ : {v // v ∈ T.roots} ↪ Fin n,
    ¬ RelativeNoiseExit (fun φ : RootedInjection T ψ => imageEdges T φ.val)
      (balancedLoad H T n) (earlyTemplateScale (k-T.roots.card) T.edges.card n) 2
      (codegreeNoiseRadius n) (prefixTime n) ω

noncomputable def prefixWheelRadius (n : ℕ) : ℝ := (n : ℝ)^(-1/80000 : ℝ)

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixCodegreeNoiseGood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

def PrefixCodegreeNoiseGood (n : ℕ) (ω : History (Graph n) (prefixTime n)) : Prop :=
  ∀ u v : Fin n, ¬ PrefixCodegreeNoiseExit u v ω

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixTriangleRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

noncomputable def prefixTriangleRadius (n : ℕ) : ℝ := (n : ℝ)^(-3/80000 : ℝ)

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixEdgeForcingBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

noncomputable def prefixEdgeForcingBound (n : ℕ) : ℝ :=
  4/(n : ℝ)+codegreeNoiseRadius n+16*prefixTriangleRadius n*Real.log n+
    4/prefixD n+24*Real.log n/(n : ℝ)

end SharpTerminalLeave
end
end

end OAI
end


