-- Prove2me | Definitions.Def_OAIQ236Ap001
-- name    : OAIQ236Ap001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T19:45:30.223827+00:00
-- url     : https://prove2.me/theorems/ee961e3f-69f8-4bf4-b35f-927c454d9867
-- title:
--   Definitions bundle OAIQ236Ap001 of the split of OpenAI, Parabolic intersections in Artin groups
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure` and `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections`, carved from OpenAI's openai/math development (OpenAI, *Parabolic intersections in Artin groups*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 469 declarations of OpenAI's Lean: 182 definitions, 7 inductive types or structures, 12 instances and 268 theorems. The definitions and types are `OAI.HarmonicArtin.Geometric.FiniteOrbit.form`, `OAI.HarmonicArtin.Geometric.FiniteOrbit.scale`, `OAI.HarmonicArtin.GraphConnection.LeftSector`, `OAI.HarmonicArtin.GraphConnection.RightSector`, `OAI.HarmonicArtin.GraphConnection.crossing`, `OAI.HarmonicArtin.GraphConnection.neighbors`, `OAI.HarmonicArtin.GraphConnection.sectorEquiv`, `OAI.HarmonicArtin.GraphConnection.sectorSwitch`, `OAI.HarmonicArtin.GraphConnection.sectorUnswitch`, `OAI.HarmonicArtin.LateDelay`, `OAI.HarmonicArtin.LayerExpression`, `OAI.HarmonicArtin.NullBoundary.coordFunctional`, `OAI.HarmonicArtin.NullBoundary.extend`, `OAI.HarmonicArtin.OrderWeights`, `OAI.HarmonicArtin.ParabolicIntersections.AmalgamTree.Amalgam`, `OAI.HarmonicArtin.ParabolicIntersections.AmalgamTree.Factor`, `OAI.HarmonicArtin.ParabolicIntersections.AmalgamTree.Vertex`, `OAI.HarmonicArtin.ParabolicIntersections.AmalgamTree.graph`, `OAI.HarmonicArtin.ParabolicIntersections.AmalgamTree.translate`, `OAI.HarmonicArtin.ParabolicIntersections.AmalgamTree.vertex`, `OAI.HarmonicArtin.ParabolicIntersections.GraphRealization.HasCurve`, `OAI.HarmonicArtin.ParabolicIntersections.GraphRealization.Point`, `OAI.HarmonicArtin.ParabolicIntersections.GraphRealization.actDart`, `OAI.HarmonicArtin.ParabolicIntersections.GraphRealization.anchor`, `OAI.HarmonicArtin.ParabolicIntersections.GraphRealization.distance`, `OAI.HarmonicArtin.ParabolicIntersections.GraphRealization.route`, `OAI.HarmonicArtin.ParabolicIntersections.GraphRealization.via`, `OAI.HarmonicArtin.ParabolicIntersections.GraphRealization.weight`, `OAI.HarmonicArtin.ParabolicIntersections.InsideIntersectionProperty`, `OAI.HarmonicArtin.ParabolicIntersections.IsVisualSplit`, `OAI.HarmonicArtin.ParabolicIntersections.LocalDescent`, `OAI.HarmonicArtin.ParabolicIntersections.MeshPaths`, `OAI.HarmonicArtin.ParabolicIntersections.MeshProjectionStage`, `OAI.HarmonicArtin.ParabolicIntersections.PathWithin`, `OAI.HarmonicArtin.ParabolicIntersections.ReductionAt`, `OAI.HarmonicArtin.ParabolicIntersections.RelativeBlock`, `OAI.HarmonicArtin.ParabolicIntersections.RelativeNullData`, `OAI.HarmonicArtin.ParabolicIntersections.SupportValue`, `OAI.HarmonicArtin.ParabolicIntersections.TreeAction.ContainsSegment`, `OAI.HarmonicArtin.ParabolicIntersections.TreeAction.PathClosed` and 149 more.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `ArtinGroups_Complexes_HighConeIndex`, `ArtinGroups_Complexes_HomSpace`, `ArtinGroups_Complexes_OptionSumEquiv`, `ArtinGroups_Diagrams_CongrEquiv`, `ArtinGroups_Diagrams_SupportedKernel`, `ArtinGroups_Diagrams_TransposeConjugateEquiv`, `ArtinGroups_Geometry_Form`, `ArtinGroups_Geometry_RootNonposDescent`, `ArtinGroups_Geometry_RootPair`, `ArtinGroups_Harmonic_CanonicalFusionLow`, `ArtinGroups_Harmonic_ConeAttachmentRel`, `ArtinGroups_Harmonic_CosetBelow`, `ArtinGroups_Harmonic_CosetSum`, `ArtinGroups_Harmonic_CosetVertex`, `ArtinGroups_Harmonic_Crossing`, `ArtinGroups_Harmonic_EigenvectorProportional`, `ArtinGroups_Harmonic_Extend`, `ArtinGroups_Harmonic_FiniteChainEnum`, `ArtinGroups_Harmonic_HarmonicExtension`, `ArtinGroups_Harmonic_HarmonicUpperAntitone`, `ArtinGroups_Harmonic_Initial`, `ArtinGroups_Harmonic_InjectiveFinrankOne`, `ArtinGroups_Harmonic_InsertOldIso`, `ArtinGroups_Harmonic_LateDelay`, `ArtinGroups_Harmonic_LayerExpression`, `ArtinGroups_Harmonic_LeftSector`, `ArtinGroups_Harmonic_NegativePrepend`, `ArtinGroups_Harmonic_PacketWord`, `ArtinGroups_Harmonic_PositiveComponent`, `ArtinGroups_Harmonic_PositiveSupportComponent`, `ArtinGroups_Harmonic_PredAboveSuccSucc`, `ArtinGroups_Harmonic_PrismFlag`, `ArtinGroups_Harmonic_PrismGrid`, `ArtinGroups_Harmonic_PrismPrefix`, `ArtinGroups_Harmonic_PrismSimplexZero`, `ArtinGroups_Harmonic_RootExtension`, `ArtinGroups_Harmonic_RowReflect`, `ArtinGroups_Harmonic_SignedLetter`, `ArtinGroups_Harmonic_SimplexSupport`, `ArtinGroups_Harmonic_SumNeighborsSubtype`, `ArtinGroups_Harmonic_UnfoldedHom`, `ArtinGroups_ParabolicIntersections_ActiveColors`, `ArtinGroups_ParabolicIntersections_AmalgamGraph`, `ArtinGroups_ParabolicIntersections_Basic`, `ArtinGroups_ParabolicIntersections_ConditionalMain`, `ArtinGroups_ParabolicIntersections_ConnectedMinima`, `ArtinGroups_ParabolicIntersections_Consequences`, `ArtinGroups_ParabolicIntersections_DynamicsDefinitions`, `ArtinGroups_ParabolicIntersections_GeneratorPowers`, `ArtinGroups_ParabolicIntersections_GraphMetric`, `ArtinGroups_ParabolicIntersections_GraphRealizationAction`, `ArtinGroups_ParabolicIntersections_GraphRealizationDistance`, `ArtinGroups_ParabolicIntersections_MainIntersection`, `ArtinGroups_ParabolicIntersections_MeshGraphNilpotence`, `ArtinGroups_ParabolicIntersections_MeshMain`, `ArtinGroups_ParabolicIntersections_MeshMatrixAction`, `ArtinGroups_ParabolicIntersections_MeshNormalization`, `ArtinGroups_ParabolicIntersections_MeshPathEvaluation`, `ArtinGroups_ParabolicIntersections_MeshPathSpaces`, `ArtinGroups_ParabolicIntersections_MeshProjection`, `ArtinGroups_ParabolicIntersections_MeshProjectionInduction`, `ArtinGroups_ParabolicIntersections_MeshQuantum`, `ArtinGroups_ParabolicIntersections_MeshQuiverAlgebra`, `ArtinGroups_ParabolicIntersections_MeshTrace`, `ArtinGroups_ParabolicIntersections_MetricUnitCurves`, `ArtinGroups_ParabolicIntersections_NoncommutingGraph`, `ArtinGroups_ParabolicIntersections_OrbitEdgeGraph`, `ArtinGroups_ParabolicIntersections_ParabolicRead`, `ArtinGroups_ParabolicIntersections_ParabolicReadReduced`, `ArtinGroups_ParabolicIntersections_PathImages`, `ArtinGroups_ParabolicIntersections_PositiveSupport`, `ArtinGroups_ParabolicIntersections_ReducedInputsMain`, `ArtinGroups_ParabolicIntersections_RelativeDiagram`, `ArtinGroups_ParabolicIntersections_RelativeFamily`, `ArtinGroups_ParabolicIntersections_RelativeHeight`, `ArtinGroups_ParabolicIntersections_RelativeInitialStabilizer`, `ArtinGroups_ParabolicIntersections_RelativeNullBlockData`, `ArtinGroups_ParabolicIntersections_RelativeUpperBasics`, `ArtinGroups_ParabolicIntersections_StabilizerDescent`, `ArtinGroups_ParabolicIntersections_TreeActionDefinitions`, `ArtinGroups_ParabolicIntersections_TreeAvoidingGraph`, `ArtinGroups_ParabolicIntersections_TreeBoundaryRays`, `ArtinGroups_ParabolicIntersections_TreePeriodicPaths`, `ArtinGroups_ParabolicIntersections_TreeSegmentBallCount`, `ArtinGroups_ParabolicIntersections_TreeSegmentOccurrences`, `ArtinGroups_ParabolicIntersections_TreeShortcutHyperbolic`, `ArtinGroups_ParabolicIntersections_TreeShortcutMetric`, `ArtinGroups_ParabolicIntersections_TreeTranslationSegment`, `ArtinGroups_ParabolicIntersections_UnconditionalMain`, `ArtinGroups_ParabolicIntersections_VisualAmalgam`, `ArtinGroups_Quivers_ProbeVertex`, `ArtinGroups_Quivers_StringArrow`, `ArtinGroups_Realizations_ConeWeights`, `ArtinGroups_Realizations_ContractionPoint`, `ArtinGroups_Realizations_FiniteWeightedNatSums`, `ArtinGroups_Realizations_FusionWeightSplit`, `ArtinGroups_Realizations_MulBlockDiagonal'Entry`, `ArtinGroups_Realizations_NerveChain`, `ArtinGroups_Realizations_NerveOrderMap`, `ArtinGroups_Realizations_NerveOrderRetractionEquiv`, `ArtinGroups_Realizations_NervePrismValue`, `ArtinGroups_Realizations_OrderWeights`, `ArtinGroups_Realizations_WeightColor`, `ArtinGroups_Realizations_WeightDim`, `ArtinGroups_Realizations_WeightDual`, `ArtinGroups_Realizations_WeightEarlierLower`, `ArtinGroups_Realizations_WeightHomeomorph`, `ArtinGroups_Realizations_WeightInclusion`, `ArtinGroups_Realizations_WeightJoinKey`, `ArtinGroups_Realizations_WeightLinearLinkInverse`, `ArtinGroups_Realizations_WeightMap`, `ArtinGroups_Realizations_WeightMapCover`, `ArtinGroups_Realizations_WeightOld`.
--
--   **Imports.** It imports the published bundle `Def_ArtinParabolicIntersections`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ236Ap002`, `OAIQ236Ap003` and `OAIQ236Ap004`.
-- source:
--   OpenAI, Parabolic intersections in Artin groups, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.PushoutI
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.Isometry
import Definitions.Def_ArtinParabolicIntersections

section
-- module Solutions.OAIQ236_AP.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h

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
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). A def, made a local instance by the port only in modules naming
`CommCStarAlgebra` or `IsMulCommutative` (`oaiport.comm_cstar_line`): as a global instance it made `whnf` time out in
FactorGeneration modules with their own `CStarAlgebra` instances on a subalgebra (oaiq-122). -/
@[reducible]
noncomputable def starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HomSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J : Type*}
  [Field K]
  [Fintype A]
  [DecidableEq V]

namespace BasedComplex

variable [Fintype I] [Fintype J]

def cochainSign (n : ℤ) : K := (n.negOnePow.val : K)

lemma cochainSign_zero : cochainSign (K := K) 0 = 1 := by
  simp [cochainSign]

lemma cochainSign_add_one (n : ℤ) : cochainSign (K := K) (n + 1) = -cochainSign n := by
  simp [cochainSign, Int.negOnePow_add]

lemma cochainSign_add (n m : ℤ) :
    cochainSign (K := K) (n + m) = cochainSign n * cochainSign m := by
  simp [cochainSign, Int.negOnePow_add]

lemma cochainSign_neg (n : ℤ) : cochainSign (K := K) (-n) = cochainSign n := by
  simp only [cochainSign, Int.negOnePow_neg]

lemma cochainSign_mul_self (n : ℤ) : cochainSign (K := K) n * cochainSign n = 1 := by
  conv_lhs => lhs; rw [← cochainSign_neg (K := K) n]
  rw [← cochainSign_add, neg_add_cancel, cochainSign_zero]

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_InjectiveFinrankOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

lemma injective_of_finrank_le_one (h : Module.finrank K W ≤ 1)
    (L : W →ₗ[K] K) (u : W) (hu : L u ≠ 0) : Function.Injective L := by
  obtain ⟨v, hv⟩ := (finrank_le_one_iff (K := K) (V := W)).mp h
  have hv' : L v ≠ 0 := by
    obtain ⟨c, rfl⟩ := hv u
    intro hh
    apply hu
    rw [map_smul, hh, smul_zero]
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro w hw
  change L w = 0 at hw
  change w = 0
  obtain ⟨c, rfl⟩ := hv w
  have hc : c = 0 := by
    rw [map_smul, smul_eq_mul] at hw
    exact (mul_eq_zero.mp hw).resolve_right hv'
  rw [hc, zero_smul]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Diagrams_SupportedKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
namespace ScalarCycles
variable {K I J : Type*} [Field K] [Fintype I]

def supportedKernel (D : Matrix I I K) (P : I → Prop) : Submodule K (I → K) where
  carrier := {x | (∀ i, ¬ P i → x i = 0) ∧ Matrix.vecMul x D = 0}
  zero_mem' := by constructor <;> simp
  add_mem' := by
    rintro x y ⟨hx,hxd⟩ ⟨hy,hyd⟩
    constructor
    · intro i hi; simp [hx i hi,hy i hi]
    · rw [Matrix.add_vecMul,hxd,hyd,add_zero]
  smul_mem' := by
    rintro r x ⟨hx,hxd⟩
    constructor
    · intro i hi; simp [hx i hi]
    · rw [Matrix.smul_vecMul,hxd,smul_zero]

lemma supported_vecMul (P : I → Prop) (R : J → Prop)
    (S : Matrix I J K) (hS : ∀ i j, S i j ≠ 0 → (P i ↔ R j))
    (x : I → K) (hx : ∀ i, ¬ P i → x i = 0) :
    ∀ j, ¬ R j → Matrix.vecMul x S j = 0 := by
  intro j hj
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hs : S i j=0
  · simp [hs]
  · rw [hx i (fun hp => hj ((hS i j hs).mp hp)),zero_mul]

variable [Fintype J]

noncomputable def conjugateMap (L : Matrix I I K) (R : Matrix J J K)
    (P : I → Prop) (T : J → Prop) (S : Matrix I J K)
    (hS : ∀ i j, S i j ≠ 0 → (P i ↔ T j)) (hc : L*S=S*R) :
    supportedKernel L P →ₗ[K] supportedKernel R T where
  toFun x := ⟨Matrix.vecMul x.val S, supported_vecMul P T S hS x.val x.property.1, by
    rw [Matrix.vecMul_vecMul,← hc,← Matrix.vecMul_vecMul,x.property.2,Matrix.zero_vecMul]⟩
  map_add' x y := by apply Subtype.ext; exact Matrix.add_vecMul _ _ _
  map_smul' r x := by apply Subtype.ext; exact Matrix.smul_vecMul _ _ _

noncomputable def conjugateEquiv [DecidableEq I] [DecidableEq J]
    (L : Matrix I I K) (R : Matrix J J K)
    (P : I → Prop) (T : J → Prop) (S : Matrix I J K) (D : Matrix J I K)
    (hS : ∀ i j, S i j ≠ 0 → (P i ↔ T j))
    (hD : ∀ j i, D j i ≠ 0 → (T j ↔ P i))
    (hSD : S*D=1) (hDS : D*S=1) (hc : L*S=S*R) :
    supportedKernel L P ≃ₗ[K] supportedKernel R T := by
  have hd : R*D=D*L := by
    calc
      R*D = (D*S)*(R*D) := by rw [hDS,Matrix.one_mul]
      _ = D*(S*R)*D := by simp only [Matrix.mul_assoc]
      _ = D*(L*S)*D := by rw [hc]
      _ = D*L*(S*D) := by simp only [Matrix.mul_assoc]
      _ = D*L := by rw [hSD,Matrix.mul_one]
  refine {
    toLinearMap := conjugateMap L R P T S hS hc
    invFun := conjugateMap R L T P D hD hd
    left_inv := ?_
    right_inv := ?_ }
  · intro x
    apply Subtype.ext
    change Matrix.vecMul (Matrix.vecMul x.val S) D=x.val
    rw [Matrix.vecMul_vecMul,hSD,Matrix.vecMul_one]
  · intro x
    apply Subtype.ext
    change Matrix.vecMul (Matrix.vecMul x.val D) S=x.val
    rw [Matrix.vecMul_vecMul,hDS,Matrix.vecMul_one]

noncomputable def reindexEquiv (L : Matrix I I K) (P : I → Prop) (e : J ≃ I) :
    supportedKernel L P ≃ₗ[K] supportedKernel (L.submatrix e e) (P ∘ e) where
  toFun x := ⟨x.val ∘ e, by
    constructor
    · intro j hj; exact x.property.1 (e j) hj
    · rw [Matrix.submatrix_vecMul_equiv]
      simp only [Function.comp_assoc,e.self_comp_symm,Function.comp_id,x.property.2,Pi.zero_comp]⟩
  invFun y := ⟨y.val ∘ e.symm, by
    constructor
    · intro i hi
      exact y.property.1 (e.symm i) (by simpa only [Function.comp_apply,e.apply_symm_apply] using hi)
    · have hh := y.property.2
      rw [Matrix.submatrix_vecMul_equiv] at hh
      funext i
      simpa only [Function.comp_apply,e.apply_symm_apply,Pi.zero_apply] using congrFun hh (e.symm i)⟩
  left_inv x := by apply Subtype.ext; funext i; simp
  right_inv y := by apply Subtype.ext; funext j; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

section Block
variable {A : Type*} [Fintype A] [DecidableEq A] {B : A → Type*} [∀ a, Fintype (B a)]

lemma vecMul_blockDiagonal' (D : (a:A) → Matrix (B a) (B a) K)
    (x : (Sigma B) → K) (a:A) (i:B a) :
    Matrix.vecMul x (Matrix.blockDiagonal' D) ⟨a,i⟩ =
      Matrix.vecMul (fun j => x ⟨a,j⟩) (D a) i := by
  change (∑ z, x z * Matrix.blockDiagonal' D z ⟨a,i⟩) = _
  rw [Fintype.sum_sigma,Finset.sum_eq_single a]
  · simp only [Matrix.blockDiagonal'_apply_eq]; rfl
  · intro b hb hba
    apply Finset.sum_eq_zero
    intro j hj
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hba,mul_zero]
  · simp

noncomputable def blockEquiv (D : (a:A) → Matrix (B a) (B a) K)
    (P : (a:A) → B a → Prop) :
    supportedKernel (Matrix.blockDiagonal' D) (fun x => P x.1 x.2) ≃ₗ[K]
      ((a:A) → supportedKernel (D a) (P a)) where
  toFun x a := ⟨fun i => x.val ⟨a,i⟩, by
    constructor
    · intro i hi; exact x.property.1 ⟨a,i⟩ hi
    · funext i
      rw [← vecMul_blockDiagonal']
      exact congrFun x.property.2 ⟨a,i⟩⟩
  invFun x := ⟨fun i => (x i.1).val i.2, by
    constructor
    · rintro ⟨a,i⟩ hi; exact (x a).property.1 i hi
    · funext i
      rw [vecMul_blockDiagonal']
      exact congrFun (x i.1).property.2 i.2⟩
  left_inv x := by rfl
  right_inv x := by rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end Block

end ScalarCycles
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Diagrams_TransposeConjugateEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ScalarCycles
variable {K I J : Type*} [Field K] [Fintype I] [Fintype J]

noncomputable def transposeConjugateEquiv [DecidableEq I] [DecidableEq J]
    (L : Matrix I I K) (R : Matrix J J K)
    (P : I → Prop) (T : J → Prop) (S : Matrix I J K) (D : Matrix J I K)
    (hS : ∀ i j, S i j ≠ 0 → (P i ↔ T j))
    (hD : ∀ j i, D j i ≠ 0 → (T j ↔ P i))
    (hSD : S*D=1) (hDS : D*S=1) (hc : R*D=D*L) :
    supportedKernel L.transpose P ≃ₗ[K] supportedKernel R.transpose T := by
  apply conjugateEquiv _ _ _ _ D.transpose S.transpose
  · intro i j h; exact (hD j i h).symm
  · intro j i h; exact (hS i j h).symm
  · rw [← Matrix.transpose_mul,hSD,Matrix.transpose_one]
  · rw [← Matrix.transpose_mul,hDS,Matrix.transpose_one]
  · have h := congrArg Matrix.transpose hc
    simpa only [Matrix.transpose_mul] using h.symm

end HarmonicArtin.ScalarCycles

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_HighConeIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u}
  {K:Type*}
  [Field K]
  [Fintype V]
  [Fintype A]
  [DecidableEq V]
  [DecidableEq A]
  {I:Type u}
  [Fintype I]
  [DecidableEq I]

noncomputable def highConeIndex (T:Set I) :
    ((Tᶜ:Set I) ⊕ ((Tᶜ:Set I) ⊕ T)) ≃ (I ⊕ (Tᶜ:Set I)) where
  toFun
    | .inl i=>.inl i.val
    | .inr (.inl j)=>.inr j
    | .inr (.inr k)=>.inl k.val
  invFun
    | .inl i=>if h:i∈T then .inr (.inr ⟨i,h⟩) else .inl ⟨i,h⟩
    | .inr j=>.inr (.inl j)
  left_inv k:=by
    rcases k with i|(j|k)
    · simp only [dite_eq_right i.property]
    · rfl
    · simp only [dite_eq_left k.property]
  right_inv k:=by
    rcases k with i|j
    · dsimp only
      split_ifs <;> rfl
    · rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Complexes_OptionSumEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
open Zigzag

universe u
attribute [local instance] Classical.decEq
variable {V A : Type u}
  {K : Type*}
  [Field K]
  [Fintype V]
  [Fintype A]
  [DecidableEq V]
  [DecidableEq A]

def optionSumEquiv (J L:Type u) : Option (J ⊕ L) ≃ Option J ⊕ L where
  toFun z := z.elim (.inl none) (fun x => x.elim (fun j=>.inl (some j)) Sum.inr)
  invFun z := z.elim (fun j => j.elim none (fun j=>some (.inl j))) (fun l=>some (.inr l))
  left_inv z := by cases z with | none => rfl | some z => cases z <;> rfl
  right_inv z := by cases z with | inl z => cases z <;> rfl | inr z => rfl

def optionProdEquiv (J L:Type u) : L ⊕ (J × L) ≃ Option J × L where
  toFun z := z.elim (fun l=>(none,l)) (fun p=>(some p.1,p.2))
  invFun z := z.1.elim (.inl z.2) (fun j=>.inr (j,z.2))
  left_inv z := by cases z <;> rfl
  right_inv z := by rcases z with ⟨j,l⟩; cases j <;> rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Diagrams_CongrEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ScalarCycles
noncomputable def congrEquiv {K I : Type*} [Field K] [Fintype I]
    (L R : Matrix I I K) (P T : I → Prop) (hL:L=R) (hP:P=T) :
    supportedKernel L P ≃ₗ[K] supportedKernel R T := by
  subst R; subst T
  exact LinearEquiv.refl K _
end HarmonicArtin.ScalarCycles

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_Form
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric.FiniteOrbit
open _root_.Matrix
open scoped _root_.Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S G:Type*} [Fintype S] [Group G] [Fintype G]
  (ρ:G →* (S → ℝ) ≃ₗ[ℝ] (S → ℝ))

noncomputable def form (x y:S → ℝ) : ℝ :=
  ∑ w:G,ρ w x ⬝ᵥ ρ w y

lemma form_symm (x y:S → ℝ) : form ρ x y=form ρ y x := by
  unfold form
  apply Finset.sum_congr rfl
  intro w _
  exact dotProduct_comm _ _

lemma form_sub_right (x y z:S → ℝ) :
    form ρ x (y-z)=form ρ x y-form ρ x z := by
  simp only [form,map_sub,dotProduct_sub,Finset.sum_sub_distrib]

lemma form_smul_right (x y:S → ℝ) (r:ℝ) :
    form ρ x (r • y)=r*form ρ x y := by
  simp only [form,map_smul,dotProduct_smul,smul_eq_mul,Finset.mul_sum]

lemma form_neg_left (x y:S → ℝ) :
    form ρ (-x) y= -form ρ x y := by
  rw [form_symm,form,form]
  simp only [map_neg,dotProduct_neg,Finset.sum_neg_distrib]
  rw [show (∑ w,ρ w y ⬝ᵥ ρ w x)=
    ∑ w,ρ w x ⬝ᵥ ρ w y from by
      apply Finset.sum_congr rfl; intro w _; exact dotProduct_comm _ _]

lemma form_invariant (g:G) (x y:S → ℝ) :
    form ρ (ρ g x) (ρ g y)=form ρ x y := by
  unfold form
  have he (w:G) : ρ w (ρ g x) ⬝ᵥ
      ρ w (ρ g y)=
      ρ (w*g) x ⬝ᵥ ρ (w*g) y := by
    simp only [map_mul,LinearEquiv.mul_apply]
  simp_rw [he]
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun w=>rfl)

lemma form_pos (x:S → ℝ) (hx:x≠0) : 0 < form ρ x x := by
  apply Finset.sum_pos'
  · intro w _
    exact Finset.sum_nonneg (fun i _=>mul_self_nonneg _)
  · refine ⟨1,Finset.mem_univ _,?_⟩
    simp only [map_one]
    change 0 < x ⬝ᵥ x
    exact lt_of_le_of_ne (Finset.sum_nonneg (fun i _=>mul_self_nonneg _))
      (Ne.symm (fun h=>hx (dotProduct_self_eq_zero.mp h)))

lemma form_sum_left {I:Type*} [Fintype I] (x:I → S → ℝ) (y:S → ℝ) :
    form ρ (∑ i,x i) y=∑ i,form ρ (x i) y := by
  simp only [form,map_sum,sum_dotProduct]
  rw [Finset.sum_comm]

lemma form_smul_left (x y:S → ℝ) (r:ℝ) : form ρ (r • x) y=r*form ρ x y := by
  rw [form_symm,form_smul_right,form_symm ρ y x]

variable [DecidableEq S]

noncomputable def scale (i:S) : ℝ := form ρ (Pi.single i 1) (Pi.single i 1)/2

lemma scale_pos (i:S) : 0 < scale ρ i := by
  apply div_pos _ (by norm_num)
  apply form_pos
  intro h
  have hi:=congrFun h i
  simp at hi

end HarmonicArtin.Geometric.FiniteOrbit

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_RootNonposDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W : Type*} [Fintype S] [DecidableEq S] [Group W]
  {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

lemma vector_eq_sum_simple (x : S → ℝ) : x=∑ i,x i • Pi.single i 1 := by
  ext k
  simp [Finset.sum_apply,Pi.single_apply]

omit [Fintype S] [DecidableEq S] in
lemma exists_longest [Finite W] : ∃ z : W,∀ w : W,cs.length w ≤ cs.length z := by
  let : Fintype W := Fintype.ofFinite W
  obtain ⟨z,_,hz⟩ := Finset.exists_max_image (Finset.univ : Finset W) cs.length Finset.univ_nonempty
  exact ⟨z,fun w => hz w (Finset.mem_univ _)⟩

omit [Fintype S] [DecidableEq S] in
lemma all_descents_of_longest (z : W) (hz : ∀ w,cs.length w ≤ cs.length z) (i : S) :
    cs.length (z*cs.simple i)+1=cs.length z := by
  have h := hz (z*cs.simple i)
  rcases cs.length_mul_simple z i with ha | hd <;> omega

omit [Fintype S] [DecidableEq S] in
lemma all_left_descents_of_longest (z : W) (hz : ∀ w,cs.length w ≤ cs.length z) (i : S) :
    cs.length (cs.simple i*z)+1=cs.length z := by
  have h := hz (cs.simple i*z)
  rcases cs.length_simple_mul z i with ha | hd <;> omega

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Geometry_RootPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open _root_.Matrix
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W : Type*} [Fintype S] [DecidableEq S] [Group W]
  {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

omit [Fintype S] [DecidableEq S] in
lemma inverse_right_length (w : W) (s : S) :
    cs.length (w⁻¹*cs.simple s)=cs.length (cs.simple s*w) := by
  rw [← cs.length_inv (cs.simple s*w),_root_.mul_inv_rev,cs.inv_simple]

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_Crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.GraphConnection

variable {J K : Type*} [Fintype J] [DecidableEq J] [Field K]

def crossing (μ : J → K) (A : K) (a b c d : J) : K :=
  (if a = d then A * (μ c / μ a) else 0) + (if b = c then A⁻¹ else 0)

variable (N : J → J → Prop) [DecidableRel N]

def neighbors (a : J) : Finset J := Finset.univ.filter (N a)

omit [DecidableEq J] in
@[simp] lemma mem_neighbors (a b : J) : b ∈ neighbors N a ↔ N a b := by
  simp [neighbors]

lemma exists_crossing_parameter (δ : ℂ) :
    ∃ A : ℂ, A ≠ 0 ∧ A^2 + A⁻¹^2 + δ = 0 := by
  obtain ⟨D, hD⟩ := IsAlgClosed.exists_pow_nat_eq (δ^2-4) (by decide : 0 < 2)
  let z := (-δ+D)/2
  have hz : z^2+δ*z+1=0 := by
    dsimp [z]
    linear_combination (1/4 : ℂ) * hD
  have hn : z ≠ 0 := by
    intro h
    rw [h] at hz
    norm_num at hz
  obtain ⟨A, hA⟩ := IsAlgClosed.exists_pow_nat_eq z (by decide : 0 < 2)
  have hAn : A ≠ 0 := by intro h; apply hn; rw [← hA,h]; norm_num
  refine ⟨A,hAn,?_⟩
  have hpoly : A^4+δ*A^2+1=0 := by
    rw [show A^4=(A^2)^2 by ring, hA]
    exact hz
  apply (mul_right_cancel₀ (pow_ne_zero 2 hAn))
  field_simp [hAn]
  linear_combination hpoly

end HarmonicArtin.GraphConnection

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_StringArrow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver

variable {V B J K : Type*}

abbrev StringArrow (step : B → Bool) (N : J → J → Prop) :=
  {p : B × J × J // if step p.1 then N p.2.1 p.2.2 else p.2.1 = p.2.2}

namespace StringArrow
variable {N : J → J → Prop} {step : B → Bool}

def base (p : StringArrow step N) : B := p.1.1
def left (p : StringArrow step N) : J := p.1.2.1
def right (p : StringArrow step N) : J := p.1.2.2

@[ext] lemma ext {p q : StringArrow step N}
    (hb : p.base=q.base) (hl : p.left=q.left) (hr : p.right=q.right) : p=q := by
  apply Subtype.ext
  exact Prod.ext hb (Prod.ext hl hr)

end StringArrow

variable (step : B → Bool)
  (N : J → J → Prop)
  (hN : ∀ ⦃first second⦄, N first second → N second first)

abbrev StringIndex := {p : (V × J) × J // N p.1.2 p.2}

namespace StringIndex
variable {N}
def old (i : StringIndex (V := V) N) : V × J := i.1.1
def label (i : StringIndex (V := V) N) : J := i.1.2
def new (i : StringIndex (V := V) N) : V × J := (i.old.1,i.label)
@[ext] lemma ext {i j : StringIndex (V := V) N}
    (ho : i.old=j.old) (hl : i.label=j.label) : i=j := Subtype.ext (Prod.ext ho hl)
end StringIndex

namespace StringFunctor

variable [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]

local notation "I" => StringIndex (V := V) N

def coefficient (orient : B → Bool) (μ : J → K) (A : K)
    (p : StringArrow step N) (c d : J) : K :=
  if step p.base then GraphConnection.crossing μ A p.left p.right c d
  else if c=d then (if orient p.base then μ c / μ p.left else 1) else 0

def liftIndex (a : V × J) (c : {c : J // N a.2 c}) : I := ⟨(a,c),c.property⟩

end StringFunctor
end HarmonicArtin.ReversibleQuiver

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_LeftSector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.GraphConnection
variable {J K : Type*} [Fintype J] [DecidableEq J] [Field K]
  (N : J → J → Prop) [DecidableRel N] (hN : ∀ ⦃left right⦄, N left right → N right left)

abbrev LeftSector (marked : Bool) (b c : J) :=
  {a : J // (if marked then N a b else a=b) ∧ N a c}

abbrev RightSector (marked : Bool) (b c : J) :=
  {d : J // N b d ∧ (if marked then N c d else c=d)}

noncomputable def sectorEquiv (marked : Bool) (b c : J) :
    LeftSector N marked b c ≃ RightSector N marked b c := by
  cases marked
  · exact {
      toFun a := ⟨c,⟨by
        have ha : a.val=b := by simpa using a.property.1
        simpa only [ha] using a.property.2,by simp⟩⟩
      invFun d := ⟨b,⟨by simp,by
        have hd : c=d.val := by simpa using d.property.2
        simpa only [hd] using d.property.1⟩⟩
      left_inv a := Subtype.ext (by simpa using a.property.1.symm)
      right_inv d := Subtype.ext (by simpa using d.property.2) }
  · exact {
      toFun a := ⟨a,⟨hN (by simpa using a.property.1),hN a.property.2⟩⟩
      invFun d := ⟨d,⟨hN d.property.1,hN (by simpa using d.property.2)⟩⟩
      left_inv _ := rfl
      right_inv _ := rfl }

lemma scalar_sector_inverse (b c : J) (r : K) (hr : r ≠ 0) :
    Matrix.of (fun (_ : LeftSector N false b c) (_ : RightSector N false b c) => r) *
      Matrix.of (fun (_ : RightSector N false b c) (_ : LeftSector N false b c) => r⁻¹) =
      (1 : Matrix (LeftSector N false b c) (LeftSector N false b c) K) := by
  classical
  ext a a'
  have hea : a=a' := Subtype.ext (a.property.1.trans a'.property.1.symm)
  subst a'
  have ha : a.val = b := by simpa using a.property.1
  let d : RightSector N false b c := ⟨c,⟨by simpa only [ha] using a.property.2,rfl⟩⟩
  rw [Matrix.mul_apply,Finset.sum_eq_single d]
  · simpa only [Matrix.of_apply, Matrix.one_apply_eq] using mul_inv_cancel₀ hr
  · intro e he hed
    exact (hed (Subtype.ext e.property.2.symm)).elim
  · simp

def sectorSwitch (μ : J → K) (A : K) (b c : J) (r : K) (marked : Bool) :
    Matrix (LeftSector N marked b c) (RightSector N marked b c) K :=
  match marked with
  | false => Matrix.of fun _ _ => r
  | true => Matrix.of fun a d => crossing μ A a b c d

omit [Fintype J] [DecidableRel N] in
lemma sectorSwitch_apply (μ : J → K) (A : K) (b c : J) (r : K) (marked : Bool)
    (a : LeftSector N marked b c) (d : RightSector N marked b c) :
    sectorSwitch N μ A b c r marked a d =
      if marked then crossing μ A a b c d else r := by
  cases marked <;> rfl

def sectorUnswitch (μ : J → K) (A : K) (b c : J) (r : K) (marked : Bool) :
    Matrix (RightSector N marked b c) (LeftSector N marked b c) K :=
  match marked with
  | false => Matrix.of fun _ _ => r⁻¹
  | true => Matrix.of fun d a => crossing μ A b a d c * (μ a / μ c)

end HarmonicArtin.GraphConnection

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_MulBlockDiagonal'Entry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Matrix
open scoped _root_.Matrix
variable {R T X : Type*} [Semiring R] [Fintype T] [DecidableEq T]
  {B C : T → Type*} [∀ i, Fintype (B i)]
lemma mul_blockDiagonal'_entry (M : Matrix X (Sigma B) R)
    (S : (i:T) → Matrix (B i) (C i) R) (x:X) (j:T) (y:C j) :
    (M * _root_.Matrix.blockDiagonal' S) x ⟨j,y⟩ = ∑ z, M x ⟨j,z⟩ * S j z y := by
  rw [_root_.Matrix.mul_apply,Fintype.sum_sigma,Finset.sum_eq_single j]
  · simp only [_root_.Matrix.blockDiagonal'_apply_eq]
  · intro i hi hij
    apply Finset.sum_eq_zero
    intro z hz
    rw [_root_.Matrix.blockDiagonal'_apply_ne _ _ _ hij,mul_zero]
  · simp
lemma blockDiagonal'_mul_entry (S : (i:T) → Matrix (C i) (B i) R)
    (M : Matrix (Sigma B) X R) (i:T) (x:C i) (y:X) :
    (_root_.Matrix.blockDiagonal' S * M) ⟨i,x⟩ y = ∑ z, S i x z * M ⟨i,z⟩ y := by
  rw [_root_.Matrix.mul_apply,Fintype.sum_sigma,Finset.sum_eq_single i]
  · simp only [_root_.Matrix.blockDiagonal'_apply_eq]
  · intro j hj hji
    apply Finset.sum_eq_zero
    intro z hz
    rw [_root_.Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hji),zero_mul]
  · simp
end Matrix

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_EigenvectorProportional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.GraphConnection
variable {J : Type*} [Fintype J] [DecidableEq J]
  (N : J → J → Prop) [DecidableRel N]

omit [DecidableEq J] in
theorem eigenvector_proportional [Nonempty J]
    (hconn : ∀ a b, Relation.ReflTransGen N a b)
    (μ : J → ℝ) (hμ : ∀ a, 0 < μ a) (δ : ℝ)
    (hPF : ∀ a, ∑ b ∈ neighbors N a, μ b = δ * μ a)
    (v : J → ℝ) (hv : ∀ a, ∑ b ∈ neighbors N a, v b = δ * v a) :
    ∃ r : ℝ, ∀ a, v a = r * μ a := by
  classical
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image Finset.univ (fun a => v a / μ a)
    Finset.univ_nonempty
  let r := v a / μ a
  let z (b : J) := r * μ b - v b
  have hz : ∀ b, 0 ≤ z b := by
    intro b
    have h := (div_le_iff₀ (hμ b)).mp (hmax b (Finset.mem_univ _))
    exact sub_nonneg.mpr h
  have hzPF (b : J) : ∑ c ∈ neighbors N b, z c = δ * z b := by
    simp only [z,Finset.sum_sub_distrib,← Finset.mul_sum,hPF,hv]
    ring
  have hza : z a = 0 := by
    dsimp only [z,r]
    rw [div_mul_cancel₀ _ (ne_of_gt (hμ a)),sub_self]
  have hstep {b c : J} (hb : z b=0) (hbc : N b c) : z c=0 := by
    have hs : ∑ d ∈ neighbors N b, z d=0 := by rw [hzPF,hb,mul_zero]
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun d _ => hz d)).mp hs c
      ((mem_neighbors N b c).mpr hbc)
  have hzero (b : J) : z b=0 := by
    have hp := hconn a b
    induction hp with
    | refl => exact hza
    | tail hp hbc ih => exact hstep ih hbc
  refine ⟨r,fun b => ?_⟩
  exact (sub_eq_zero.mp (hzero b)).symm

omit [DecidableEq J] in
theorem nonnegative_eigenvector_proportional [Nonempty J]
    (hconn : ∀ a b, Relation.ReflTransGen N a b)
    (μ : J → ℝ) (hμ : ∀ a, 0 < μ a) (δ : ℝ)
    (hPF : ∀ a, ∑ b ∈ neighbors N a, μ b = δ * μ a)
    (v : J → ℝ) (hv : ∀ a, ∑ b ∈ neighbors N a, v b = δ * v a)
    (hnonneg : ∀ a, 0 ≤ v a) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ a, v a = r * μ a := by
  obtain ⟨r,hr⟩ := eigenvector_proportional N hconn μ hμ δ hPF v hv
  refine ⟨r,?_,hr⟩
  let a : J := Classical.choice inferInstance
  exact nonneg_of_mul_nonneg_right (by rw [mul_comm,← hr]; exact hnonneg a) (hμ a)

end HarmonicArtin.GraphConnection

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_SumNeighborsSubtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.GraphConnection
variable {J : Type*} [Fintype J]
  (N : J → J → Prop) [DecidableRel N]

lemma sum_neighbors_subtype {R : Type*} [AddCommMonoid R] (a : J) (f : J → R) :
    ∑ b ∈ neighbors N a, f b = ∑ b : {b // N a b}, f b :=
  Finset.sum_subtype (neighbors N a) (mem_neighbors N a) f

lemma sum_neighbors_subtype_left (hN : ∀ ⦃left right⦄, N left right → N right left)
    {R : Type*} [AddCommMonoid R] (a : J) (f : J → R) :
    ∑ b ∈ neighbors N a, f b = ∑ b : {b // N b a}, f b :=
  Finset.sum_subtype (neighbors N a)
    (fun b => (mem_neighbors N a b).trans ⟨fun h => hN h, fun h => hN h⟩) f

lemma weighted_intertwiner (hN : ∀ ⦃left right⦄, N left right → N right left)
    (ρ : J → ℝ) (θ : ℝ)
    (hρ : ∀ a, ∑ b ∈ neighbors N a, ρ b = θ * ρ a)
    (D : J → J → ℕ)
    (hD : ∀ i j, (∑ b : {b // N b j}, D i b) = ∑ a : {a // N i a}, D a j)
    (j : J) :
    ∑ b ∈ neighbors N j, (∑ i, ρ i * (D i b : ℝ)) =
      θ * (∑ i, ρ i * (D i j : ℝ)) := by
  have hd (i j : J) : ∑ b ∈ neighbors N j, (D i b : ℝ) =
      ∑ a ∈ neighbors N i, (D a j : ℝ) := by
    rw [sum_neighbors_subtype_left N hN,sum_neighbors_subtype N]
    exact_mod_cast hD i j
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,hd]
  simp_rw [Finset.mul_sum,neighbors,Finset.sum_filter]
  rw [Finset.sum_comm]
  calc
    _ = ∑ a, (∑ i ∈ neighbors N a, ρ i) * (D a j : ℝ) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_mul]
      simp only [neighbors,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      have he : N i a ↔ N a i := ⟨fun h => hN h,fun h => hN h⟩
      simp only [he]
    _ = _ := by simp_rw [hρ]; apply Finset.sum_congr rfl; intros; ring

end HarmonicArtin.GraphConnection

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_LayerExpression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

inductive LayerExpression (V:Type*) where
  | input : LayerExpression V
  | word : List (V × Bool) → LayerExpression V → LayerExpression V
  | low : ℤ → LayerExpression V → LayerExpression V
  | layer : ℤ → LayerExpression V → LayerExpression V

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_CanonicalFusionLow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V:Type}
  {K:Type*}
  [Field K]
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  (m:E→ℕ)

def canonicalFusionExpression (w:List V) (z:List (V×Bool)) (q:ℤ) : LayerExpression V :=
  .word (w.map fun s=>(s,true))
    (.low (q-1) (.word ((w.map fun s=>(s,true)).reverse.map fun a=>(a.1,!a.2))
      (.layer q (.word z .input))))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_ConeAttachmentRel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

universe u v
variable {A:Type u} {L:Type v} [TopologicalSpace A] [TopologicalSpace L]

lemma continuous_prod_sum_elim {B X Y Z:Type*} [TopologicalSpace B]
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (g:B×(X⊕Y)→Z)
    (hx:Continuous (fun p:B×X=>g (p.1,.inl p.2)))
    (hy:Continuous (fun p:B×Y=>g (p.1,.inr p.2))) : Continuous g := by
  have h:= (hx.sumElim hy).comp (Homeomorph.prodSumDistrib (X:=B) (Y:=X) (Z:=Y)).continuous
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  rcases p with ⟨b,x|y⟩ <;> rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_Extend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
namespace NullBoundary

open scoped _root_.Matrix Classical
open Set Filter

variable {V : Type*}

noncomputable def extend (J : Set V) (s : J → ℝ) : V → ℝ := by
  classical
  exact fun i => if hi : i ∈ J then s ⟨i, hi⟩ else 0

@[simp] lemma extend_apply_mem (J : Set V) (s : J → ℝ) (i : J) :
    extend J s i = s i := by
  classical
  simp [extend, i.property]

@[simp] lemma extend_apply_not_mem (J : Set V) (s : J → ℝ) (i : V) (hi : i ∉ J) :
    extend J s i = 0 := by
  classical
  simp [extend, hi]

variable [Fintype V]

noncomputable def coordFunctional (J : Set V) (v : V → ℝ) : (J → ℝ) →L[ℝ] ℝ :=
  ∑ j : J, (ContinuousLinearMap.proj j).smulRight (v j)

end NullBoundary
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_CosetVertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe u
variable {S : Type u}

 theorem artinParabolic_mono (M : CoxeterMatrix S) {T U : Set S} (h : T ⊆ U) :
    artinParabolic M T ≤ artinParabolic M U :=
  Subgroup.closure_mono (Set.image_mono h)

open _root_.Matrix

theorem harmonic_minimum_principle {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hC : C.PosDef)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ (C *ᵥ x) i) : ∀ i, 0 ≤ x i := by
  classical
  let y : ι → ℝ := fun i => min (x i) 0
  let z : ι → ℝ := fun i => max (x i) 0
  have hy : ∀ i, y i ≤ 0 := fun i => min_le_right _ _
  have hz : ∀ i, 0 ≤ z i := fun i => le_max_right _ _
  have hsplit : x = y + z := by
    funext i
    simp only [Pi.add_apply, y, z, min_add_max, add_zero]
  have hyz : ∀ i, y i * z i = 0 := by
    intro i
    dsimp [y, z]
    by_cases hi : x i ≤ 0
    · simp [min_eq_left hi, max_eq_right hi]
    · simp [min_eq_right (le_of_not_ge hi), max_eq_left (le_of_not_ge hi)]
  have hcross : 0 ≤ y ⬝ᵥ (C *ᵥ z) := by
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_nonneg
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_nonneg
    intro j _
    by_cases hij : i = j
    · subst j
      apply le_of_eq
      calc
        0 = C i i * (y i * z i) := by rw [hyz i, mul_zero]
        _ = y i * (C i i * z i) := by ring
    · simpa only [mul_assoc] using
        mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (hy i) (hOff i j hij)) (hz j)
  have htotal : y ⬝ᵥ (C *ᵥ x) ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg (hy i) (hx i)
  have hym : y ⬝ᵥ (C *ᵥ y) ≤ 0 := by
    rw [hsplit, Matrix.mulVec_add, dotProduct_add] at htotal
    linarith
  have hy0 : y = 0 := by
    by_contra h
    have hp := hC.dotProduct_mulVec_pos h
    exact (not_lt_of_ge hym) (by simpa only [star_trivial] using hp)
  intro i
  have hi : min (x i) 0 = 0 := congrFun hy0 i
  exact (min_eq_right_iff).mp hi

theorem harmonic_solve {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : C.PosDef) (v : ι → ℝ) :
    C *ᵥ (C⁻¹ *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv C ((Matrix.isUnit_iff_isUnit_det C).mp hC.isUnit),
    Matrix.one_mulVec]

theorem harmonic_extension_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : C.PosDef)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) : ∀ i, 0 ≤ (C⁻¹ *ᵥ v) i := by
  apply harmonic_minimum_principle C hC hOff
  simpa only [harmonic_solve C hC v] using hv

theorem harmonic_positive_neighbor {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hCx : ∀ i, 0 ≤ (C *ᵥ x) i)
    {i j : ι} (hij : C i j < 0) (hj : 0 < x j) : 0 < x i := by
  classical
  by_contra hi
  have hi0 : x i = 0 := le_antisymm (le_of_not_gt hi) (hx i)
  have hterm : ∀ k ∈ (Finset.univ : Finset ι), C i k * x k ≤ 0 := by
    intro k _
    by_cases hik : i = k
    · subst k
      rw [hi0, mul_zero]
    · exact mul_nonpos_of_nonpos_of_nonneg (hOff i k hik) (hx k)
  have hsum : (C *ᵥ x) i < 0 :=
    Finset.sum_neg' hterm ⟨j, Finset.mem_univ j, mul_neg_of_neg_of_pos hij hj⟩
  exact (not_lt_of_ge (hCx i)) hsum

theorem harmonic_positive_path {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hCx : ∀ i, 0 ≤ (C *ᵥ x) i)
    {i j : ι} (hij : Relation.ReflTransGen (fun a b => C a b < 0) i j)
    (hj : 0 < x j) : 0 < x i := by
  induction hij using Relation.ReflTransGen.head_induction_on with
  | refl => exact hj
  | @head a b hab _ ih => exact harmonic_positive_neighbor C hOff x hx hCx hab ih

theorem harmonic_scaled_form {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hSym : ∀ i j, C i j = C j i)
    (v w : ι → ℝ) :
    (v * w) ⬝ᵥ (C *ᵥ (v * w)) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, (-C i j * v i * v j) * (w i - w j)^2 +
      ∑ i, v i * (C *ᵥ v) i * (w i)^2 := by
  classical
  have hswap : (∑ i, ∑ j, C i j * v i * v j * (w j)^2) =
      ∑ i, ∑ j, C i j * v i * v j * (w i)^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hSym j i]
    ring
  have hexpand : (∑ i, ∑ j, (-C i j * v i * v j) * (w i - w j)^2) =
      -(∑ i, ∑ j, C i j * v i * v j * (w i)^2) +
      2 * (∑ i, ∑ j, C i j * v i * v j * w i * w j) -
      (∑ i, ∑ j, C i j * v i * v j * (w j)^2) := by
    simp only [← Finset.sum_neg_distrib, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hdiag : (∑ i, v i * (C *ᵥ v) i * (w i)^2) =
      ∑ i, ∑ j, C i j * v i * v j * (w i)^2 := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hquad : (v * w) ⬝ᵥ (C *ᵥ (v * w)) =
      ∑ i, ∑ j, C i j * v i * v j * w i * w j := by
    simp only [Matrix.mulVec, dotProduct, Pi.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexpand, hswap, hdiag, hquad]
  ring

theorem harmonic_posDef_of_strict_row {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hSym : ∀ i j, C i j = C j i)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (hConn : ∀ i j, Relation.ReflTransGen (fun a b => C a b < 0) i j)
    (v : ι → ℝ) (hv : ∀ i, 0 < v i)
    (hCv : ∀ i, 0 ≤ (C *ᵥ v) i) (hStrict : ∃ k, 0 < (C *ᵥ v) k) : C.PosDef := by
  classical
  have hHerm : C.IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j
    exact hSym j i
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hHerm
  intro x hx
  simp only [star_trivial]
  let w : ι → ℝ := fun i => x i / v i
  have hxw : x = v * w := by
    funext i
    dsimp [w]
    exact (mul_div_cancel₀ (x i) (ne_of_gt (hv i))).symm
  let e : ι → ι → ℝ := fun i j => (-C i j * v i * v j) * (w i - w j)^2
  let f : ι → ℝ := fun i => v i * (C *ᵥ v) i * (w i)^2
  have he : ∀ i j, 0 ≤ e i j := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [e]
    · exact mul_nonneg (mul_nonneg (mul_nonneg (neg_nonneg.mpr (hOff i j hij))
        (le_of_lt (hv i))) (le_of_lt (hv j))) (sq_nonneg _)
  have hf : ∀ i, 0 ≤ f i := by
    intro i
    exact mul_nonneg (mul_nonneg (le_of_lt (hv i)) (hCv i)) (sq_nonneg _)
  have hE : 0 ≤ ∑ i, ∑ j, e i j := Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => he i j
  have hF : 0 ≤ ∑ i, f i := Finset.sum_nonneg fun i _ => hf i
  have hformula : x ⬝ᵥ (C *ᵥ x) = (1 / 2 : ℝ) * (∑ i, ∑ j, e i j) + ∑ i, f i := by
    rw [hxw]
    exact harmonic_scaled_form C hSym v w
  by_contra hn
  have hE0 : (∑ i, ∑ j, e i j) = 0 := by linarith
  have hF0 : (∑ i, f i) = 0 := by linarith
  have hedge : ∀ i j, C i j < 0 → w i = w j := by
    intro i j hij
    have hsum0 : (∑ j, e i j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Finset.sum_nonneg fun j _ => he i j)).mp hE0 i (Finset.mem_univ i)
    have he0 : e i j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => he i j)).mp hsum0 j (Finset.mem_univ j)
    have hc : 0 < -C i j * v i * v j :=
      mul_pos (mul_pos (neg_pos.mpr hij) (hv i)) (hv j)
    have hs : (w i - w j)^2 = 0 := (mul_eq_zero.mp he0).resolve_left (ne_of_gt hc)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
  obtain ⟨k, hk⟩ := hStrict
  have hfk : f k = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hf i)).mp hF0 k (Finset.mem_univ k)
  have hwk : w k = 0 := by
    have hc : 0 < v k * (C *ᵥ v) k := mul_pos (hv k) hk
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hfk).resolve_left (ne_of_gt hc))
  have hwzero : w = 0 := by
    funext i
    have hi : w i = w k := by
      induction hConn i k using Relation.ReflTransGen.head_induction_on with
      | refl => rfl
      | @head a b hab _ ih => exact (hedge a b hab).trans ih
    exact hi.trans hwk
  apply hx
  rw [hxw, hwzero, mul_zero]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_RowReflect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix
open scoped _root_.Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {V:Type*} [Fintype V] [DecidableEq V]

noncomputable def rowReflect (C:Matrix V V ℝ) (i:V) (x:V → ℝ) : V → ℝ :=
  x-(C *ᵥ x) i • Pi.single i 1

noncomputable def rowReflectWord (C:Matrix V V ℝ) (l:List V) (x:V → ℝ) : V → ℝ :=
  l.foldr (rowReflect C) x

lemma rowReflectWord_orthogonal (C:Matrix V V ℝ) (l:List V) (hn:l.Nodup)
    (ho:∀ i∈l,∀ j∈l,i≠j → C i j=0) (x:V → ℝ) :
    rowReflectWord C l x=x-∑ i∈l.toFinset,(C *ᵥ x) i • Pi.single i 1 := by
  induction l with
  | nil => simp [rowReflectWord]
  | cons a l ih =>
    obtain ⟨ha,hl⟩:=List.nodup_cons.mp hn
    have ho' : ∀ i∈l,∀ j∈l,i≠j → C i j=0 :=
      fun i hi j hj h=>ho i (by simp [hi]) j (by simp [hj]) h
    have hs : (C *ᵥ (∑ i∈l.toFinset,(C *ᵥ x) i • Pi.single i 1)) a=0 := by
      rw [Matrix.mulVec_sum,Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro i hi
      have hi':i∈l:=List.mem_toFinset.mp hi
      have hai:a≠i := fun h=>ha (h.symm ▸ hi')
      simp [Matrix.mulVec_smul,Matrix.mulVec_single,Matrix.col,
        ho a (by simp) i (by simp [hi']) hai]
    change rowReflect C a (rowReflectWord C l x)=_
    rw [ih hl ho']
    simp only [rowReflect,Matrix.mulVec_sub,Pi.sub_apply,hs,sub_zero]
    rw [List.toFinset_cons,Finset.sum_insert (by simpa using ha)]
    module

variable {E:Type*} [Fintype E] [DecidableEq E] (m:E → ℕ)

lemma rowReflectWord_append (C:Matrix V V ℝ) (a b:List V) (x:V → ℝ) :
    rowReflectWord C (a++b) x=rowReflectWord C a (rowReflectWord C b x) := by
  simp [rowReflectWord,List.foldr_append]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_FusionWeightSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.propDecidable
variable {E:Type} [Fintype E] [DecidableEq E] (m:E → ℕ)

lemma finitePi_update_constant {α:E → Type*} {B:Type*} (f:((i:E) → α i) → B)
    (hf:∀ x i a,f (Function.update x i a)=f x) (x y:(i:E) → α i) : f x=f y := by
  have hh (s:Finset E) : ∀ x y:(i:E) → α i, (∀ i,i ∉ s → x i=y i) → f x=f y := by
    induction s using Finset.induction_on with
    | empty =>
      intro x y h
      exact congrArg f (funext fun i=>h i (Finset.notMem_empty i))
    | @insert i s hi ih =>
      intro x y h
      calc
        f x = f (Function.update x i (y i)) := (hf x i (y i)).symm
        _ = f y := ih _ _ (by
          intro j hj
          by_cases he:j=i
          · subst j; exact Function.update_self _ _ _
          · rw [Function.update_of_ne he]
            exact h j (by simp [he,hj]))
  exact hh Finset.univ x y (by simp)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Quivers_ProbeVertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver
variable {V A:Type*}
attribute [local instance] Classical.decEq Classical.propDecidable

abbrev ProbeVertex (V:Type*) := V⊕(V×Bool)
abbrev ProbeArrow (V A:Type*) := A⊕(V×Bool×Bool)

end HarmonicArtin.ReversibleQuiver

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_HarmonicExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe u
variable {S : Type u}
open _root_.Matrix

theorem harmonic_positive_null_alternative {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hSym : ∀ i j, C i j = C j i)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (hConn : ∀ i j, Relation.ReflTransGen (fun a b => C a b < 0) i j)
    (v : ι → ℝ) (hv : ∀ i, 0 < v i) (hCv : ∀ i, 0 ≤ (C *ᵥ v) i) :
    C.PosDef ∨ C *ᵥ v = 0 := by
  by_cases hs : ∃ k, 0 < (C *ᵥ v) k
  · exact Or.inl (harmonic_posDef_of_strict_row C hSym hOff hConn v hv hCv hs)
  · right
    funext i
    exact le_antisymm (le_of_not_gt fun h => hs ⟨i, h⟩) (hCv i)

open scoped Classical

noncomputable def harmonicExtension {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (T : Set ι) (v : ι → ℝ) : ι → ℝ := by
  classical
  exact fun i => if hi : i ∈ T then
    ((C.submatrix Subtype.val Subtype.val : Matrix T T ℝ)⁻¹ *ᵥ
      fun a : T => ∑ b : ↥(Tᶜ), -(C a b) * v b) ⟨i, hi⟩ else v i

theorem harmonicExtension_outside {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (T : Set ι) (v : ι → ℝ) {i : ι} (hi : i ∉ T) :
    harmonicExtension C T v i = v i := by
  classical
  simp [harmonicExtension, hi]

theorem harmonicExtension_inside {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (T : Set ι) (v : ι → ℝ) :
    (fun i : T => harmonicExtension C T v i) =
      (C.submatrix Subtype.val Subtype.val : Matrix T T ℝ)⁻¹ *ᵥ
        (fun a : T => ∑ b : ↥(Tᶜ), -(C a b) * v b) := by
  classical
  funext i
  simp [harmonicExtension, i.property]

theorem harmonic_row_split {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (T : Set ι) (v : ι → ℝ) (i : ι) :
    (C *ᵥ v) i = (∑ j : T, C i j * v j) + ∑ j : ↥(Tᶜ), C i j * v j := by
  classical
  exact (Fintype.sum_subtype_add_sum_subtype (fun j => j ∈ T)
    (fun j => C i j * v j)).symm

theorem harmonicExtension_harmonic {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (T : Set ι)
    (hT : (C.submatrix Subtype.val Subtype.val : Matrix T T ℝ).PosDef)
    (v : ι → ℝ) (i : T) : (C *ᵥ harmonicExtension C T v) i = 0 := by
  classical
  rw [harmonic_row_split C T]
  have hsolve := congrFun (harmonic_solve
    (C.submatrix Subtype.val Subtype.val : Matrix T T ℝ) hT
    (fun a : T => ∑ b : ↥(Tᶜ), -(C a b) * v b)) i
  rw [← harmonicExtension_inside C T v] at hsolve
  change (∑ j : T, C i j * harmonicExtension C T v j) = _ at hsolve
  rw [hsolve]
  have he (j : ↥(Tᶜ)) : harmonicExtension C T v j = v j :=
    harmonicExtension_outside C T v j.property
  simp only [he, neg_mul, Finset.sum_neg_distrib, neg_add_cancel]

theorem harmonicExtension_nonneg {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (T : Set ι)
    (hT : (C.submatrix Subtype.val Subtype.val : Matrix T T ℝ).PosDef)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0) (v : ι → ℝ)
    (hv : ∀ i, 0 ≤ v i) : ∀ i, 0 ≤ harmonicExtension C T v i := by
  classical
  have hb (a : T) : 0 ≤ ∑ b : ↥(Tᶜ), -(C a b) * v b := by
    apply Finset.sum_nonneg
    intro b _
    have hab : (a : ι) ≠ b := fun h => b.property (h ▸ a.property)
    exact mul_nonneg (neg_nonneg.mpr (hOff a b hab)) (hv b)
  have hOffT (a b : T) (h : a ≠ b) : C a b ≤ 0 :=
    hOff a b (fun e => h (Subtype.ext e))
  intro i
  by_cases hi : i ∈ T
  · simpa only [harmonicExtension, dite_eq_left hi] using
      harmonic_extension_nonneg (C.submatrix Subtype.val Subtype.val : Matrix T T ℝ)
        hT hOffT _ hb ⟨i, hi⟩
  · simpa only [harmonicExtension_outside C T v hi] using hv i

theorem harmonic_solve_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : C.PosDef) (v : ι → ℝ) :
    C⁻¹ *ᵥ (C *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul C ((Matrix.isUnit_iff_isUnit_det C).mp hC.isUnit),
    Matrix.one_mulVec]

theorem harmonicExtension_unique {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (T : Set ι)
    (hT : (C.submatrix Subtype.val Subtype.val : Matrix T T ℝ).PosDef)
    (v p : ι → ℝ) (hExt : ∀ i ∉ T, p i = v i)
    (hHarm : ∀ i : T, (C *ᵥ p) i = 0) : p = harmonicExtension C T v := by
  classical
  have hrow : (C.submatrix Subtype.val Subtype.val : Matrix T T ℝ) *ᵥ
      (fun i : T => p i) = fun a : T => ∑ b : ↥(Tᶜ), -(C a b) * v b := by
    funext i
    have hi := hHarm i
    rw [harmonic_row_split C T] at hi
    have he (j : ↥(Tᶜ)) : p j = v j := hExt j j.property
    simp only [he] at hi
    simp only [neg_mul, Finset.sum_neg_distrib]
    exact eq_neg_of_add_eq_zero_left hi
  have hval := harmonic_solve_left
    (C.submatrix Subtype.val Subtype.val : Matrix T T ℝ) hT (fun i : T => p i)
  rw [hrow, ← harmonicExtension_inside C T v] at hval
  funext i
  by_cases hi : i ∈ T
  · exact (congrFun hval ⟨i, hi⟩).symm
  · simpa only [harmonicExtension_outside C T v hi] using hExt i hi

theorem harmonic_upper_change {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (U : Set ι)
    (hU : (C.submatrix Subtype.val Subtype.val : Matrix U U ℝ).PosDef)
    (p q : ι → ℝ) (hExt : ∀ i ∉ U, q i = p i)
    (hHarm : ∀ i : U, (C *ᵥ q) i = 0) :
    (fun i : U => q i - p i) =
      -((C.submatrix Subtype.val Subtype.val : Matrix U U ℝ)⁻¹ *ᵥ
        fun i : U => (C *ᵥ p) i) := by
  classical
  have hrow : (C.submatrix Subtype.val Subtype.val : Matrix U U ℝ) *ᵥ
      (fun i : U => q i - p i) = -(fun i : U => (C *ᵥ p) i) := by
    funext i
    have hi := congrFun (Matrix.mulVec_sub C q p) (i : ι)
    simp only [Pi.sub_apply, hHarm i, zero_sub] at hi
    rw [harmonic_row_split C U] at hi
    have he : ∑ j : ↥(Uᶜ), C i j * (q - p) j = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      simp only [Pi.sub_apply, hExt j j.property, sub_self, mul_zero]
    rw [he, add_zero] at hi
    exact hi
  have hval := harmonic_solve_left
    (C.submatrix Subtype.val Subtype.val : Matrix U U ℝ) hU
    (fun i : U => q i - p i)
  rw [hrow, Matrix.mulVec_neg] at hval
  exact hval.symm

noncomputable def framedCartan (M : CoxeterMatrix S) :
    Matrix (S ⊕ Unit) (S ⊕ Unit) ℝ
  | .inl i, .inl j => if i = j then 2 else
      if M i j = 0 then -2 else -2 * Real.cos (Real.pi / (M i j : ℝ))
  | .inl _, .inr _ => -1
  | .inr _, .inl _ => -1
  | .inr _, .inr _ => 2

theorem framedCartan_symm (M : CoxeterMatrix S) (i j : S ⊕ Unit) :
    framedCartan M i j = framedCartan M j i := by
  cases i <;> cases j <;> simp only [framedCartan]
  rename_i i j
  by_cases h : i = j
  · subst j; simp
  · simp only [h, Ne.symm h, ↓reduceIte, M.symmetric i j]

theorem framedCartan_diag (M : CoxeterMatrix S) (i : S ⊕ Unit) :
    framedCartan M i i = 2 := by
  cases i <;> simp [framedCartan]

theorem framedCartan_off (M : CoxeterMatrix S) (i j : S ⊕ Unit) (h : i ≠ j) :
    framedCartan M i j ≤ 0 := by
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hij : i ≠ j := fun e => h (congrArg Sum.inl e)
      simp only [framedCartan, hij, ↓reduceIte]
      split_ifs with hm
      · norm_num
      · have hm2 : 2 ≤ M i j := by
          have hm1 := M.off_diagonal i j hij
          omega
        have hc : (2 : ℝ) ≤ (M i j : ℝ) := by exact_mod_cast hm2
        have hp : 0 < (M i j : ℝ) := by linarith
        have hcos : 0 ≤ Real.cos (Real.pi / (M i j : ℝ)) := by
          apply Real.cos_nonneg_of_mem_Icc
          constructor
          · have hn := div_nonneg Real.pi_pos.le hp.le
            linarith [Real.pi_pos]
          · apply (div_le_iff₀ hp).mpr
            nlinarith [Real.pi_pos]
        exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) hcos
    | inr j => norm_num [framedCartan]
  | inr i =>
    cases j with
    | inl j => norm_num [framedCartan]
    | inr j => exact (h (congrArg Sum.inr (Subsingleton.elim i j))).elim

theorem harmonic_lower_change {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (R : Set ι)
    (hR : (C.submatrix Subtype.val Subtype.val : Matrix R R ℝ).PosDef)
    (p q : ι → ℝ) (hp : ∀ i : R, (C *ᵥ p) i = 0)
    (hq : ∀ i : R, (C *ᵥ q) i = 0) :
    (fun i : R => q i - p i) =
      (C.submatrix Subtype.val Subtype.val : Matrix R R ℝ)⁻¹ *ᵥ
        (fun i : R => ∑ j : ↥(Rᶜ), -(C i j) * (q j - p j)) := by
  have heq : q - p = harmonicExtension C R (q - p) := by
    apply harmonicExtension_unique C R hR
    · intro i _; rfl
    · intro i
      simp only [Matrix.mulVec_sub, Pi.sub_apply, hp i, hq i, sub_self]
  calc
    _ = (fun i : R => harmonicExtension C R (q - p) i) :=
      congrArg (fun v : ι → ℝ => fun i : R => v i) heq
    _ = _ := by
      simpa only [Pi.sub_apply] using harmonicExtension_inside C R (q - p)

theorem harmonic_boundary_comparison {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (R : Set ι)
    (hR : (C.submatrix Subtype.val Subtype.val : Matrix R R ℝ).PosDef)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (p q : ι → ℝ) (hp : ∀ i : R, (C *ᵥ p) i = 0)
    (hq : ∀ i : R, (C *ᵥ q) i = 0)
    (hext : ∀ i ∉ R, p i ≤ q i) : ∀ i, p i ≤ q i := by
  have hchange := harmonic_lower_change C R hR p q hp hq
  have hnonneg : ∀ i : R, 0 ≤ q i - p i := by
    intro a
    rw [congrFun hchange a]
    apply harmonic_extension_nonneg _ hR
    · intro i j hij
      exact hOff i j (fun e => hij (Subtype.ext e))
    · intro i
      apply Finset.sum_nonneg
      intro j _
      apply mul_nonneg
      · exact neg_nonneg.mpr (hOff i j (fun e => j.property (e ▸ i.property)))
      · exact sub_nonneg.mpr (hext j j.property)
  intro i
  by_cases hi : i ∈ R
  · exact sub_nonneg.mp (hnonneg ⟨i, hi⟩)
  · exact hext i hi

theorem harmonic_positive_neighbor_at {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) {i j : ι}
    (hCx : 0 ≤ (C *ᵥ x) i) (hij : C i j < 0) (hj : 0 < x j) : 0 < x i := by
  classical
  by_contra hi
  have hi0 : x i = 0 := le_antisymm (le_of_not_gt hi) (hx i)
  have hterm : ∀ k ∈ (Finset.univ : Finset ι), C i k * x k ≤ 0 := by
    intro k _
    by_cases hik : i = k
    · subst k; rw [hi0, mul_zero]
    · exact mul_nonpos_of_nonpos_of_nonneg (hOff i k hik) (hx k)
  have hsum : (C *ᵥ x) i < 0 :=
    Finset.sum_neg' hterm ⟨j, Finset.mem_univ j, mul_neg_of_neg_of_pos hij hj⟩
  exact (not_lt_of_ge hCx) hsum

theorem harmonic_support_alternative {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hSym : ∀ i j, C i j = C j i)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (G : Set ι)
    (hConn : ∀ i j : G, Relation.ReflTransGen (fun a b : G => C a b < 0) i j)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hrow : ∀ i : G, 0 ≤ (C *ᵥ p) i)
    (hInc : ∃ j, 0 < p j ∧ (j ∈ G ∨ ∃ i : G, C i j < 0)) :
    (C.submatrix Subtype.val Subtype.val : Matrix G G ℝ).PosDef ∨
      ((∀ i : G, 0 < p i) ∧ (∀ i : G, (C *ᵥ p) i = 0) ∧
        ∀ i : G, ∀ j ∉ G, C i j < 0 → p j = 0) := by
  classical
  let A : Matrix G G ℝ := C.submatrix Subtype.val Subtype.val
  have haOff (i j : G) (hij : i ≠ j) : A i j ≤ 0 :=
    hOff i j (fun h => hij (Subtype.ext h))
  have hext (i : G) : (∑ j : ↥(Gᶜ), C i j * p j) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    exact mul_nonpos_of_nonpos_of_nonneg
      (hOff i j (fun h => j.property (h ▸ i.property))) (hp j)
  have haRow (i : G) : 0 ≤ (A *ᵥ (fun j : G => p j)) i := by
    have hi := hrow i
    rw [harmonic_row_split C G] at hi
    have he := hext i
    change 0 ≤ ∑ j : G, C i j * p j
    linarith
  have hex : ∃ i : G, 0 < p i := by
    obtain ⟨j, hj, hjG | ⟨i, hij⟩⟩ := hInc
    · exact ⟨⟨j, hjG⟩, hj⟩
    · exact ⟨i, harmonic_positive_neighbor_at C hOff p hp (hrow i) hij hj⟩
  obtain ⟨j, hj⟩ := hex
  have hpG (i : G) : 0 < p i :=
    harmonic_positive_path A haOff (fun a : G => p a) (fun a => hp a)
      haRow (hConn i j) hj
  rcases harmonic_positive_null_alternative A (fun a b => hSym a b)
    haOff hConn (fun i : G => p i) hpG haRow with hdef | hnull
  · exact Or.inl hdef
  · right
    refine ⟨hpG, ?_, ?_⟩
    · intro i
      have hi := congrFun hnull i
      have ht := harmonic_row_split C G p i
      change (∑ j : G, C i j * p j) = 0 at hi
      rw [hi, zero_add] at ht
      exact le_antisymm (ht ▸ hext i) (hrow i)
    · intro i j hjG hij
      have hi := congrFun hnull i
      change (∑ j : G, C i j * p j) = 0 at hi
      have hr := hrow i
      rw [harmonic_row_split C G, hi, zero_add] at hr
      have hterm : ∀ b ∈ (Finset.univ : Finset ↥(Gᶜ)), C i b * p b ≤ 0 := by
        intro b _
        exact mul_nonpos_of_nonpos_of_nonneg
          (hOff i b (fun h => b.property (h ▸ i.property))) (hp b)
      have hz : C i j * p j = 0 :=
        (Finset.sum_eq_zero_iff_of_nonpos hterm).mp (le_antisymm (hext i) hr)
          ⟨j, hjG⟩ (Finset.mem_univ _)
      exact (mul_eq_zero.mp hz).resolve_left (ne_of_lt hij)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_UnfoldedHom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open Geometric
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable

lemma wordProd_flatten_replicate {V W : Type*} [Group W] {N : CoxeterMatrix V}
    (cs : CoxeterSystem N W) (u : List V) (n : ℕ) :
    cs.wordProd ((List.replicate n u).flatten)=(cs.wordProd u)^n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ,List.flatten_cons,cs.wordProd_append,ih,pow_succ']

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_RootExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix Geometric
open scoped _root_.Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I:Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

noncomputable def rootExtension (f:I→V) (x:I→ℝ) : V→ℝ := ∑ i,x i • Pi.single (f i) 1

variable {S:Type*} [Fintype S] [LinearOrder S]

noncomputable def sourceRootInclusion (J:Set S) (j:J) : S⊕Unit := .inl (j:S)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_NegativePrepend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V:Type}
  {K:Type*}
  [Field K]
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  (m:E→ℕ)

def negativePrepend (w:List V) (z:List (V×Bool)) : List (V×Bool) :=
  ((w.map fun s=>(s,true)).reverse.map fun a=>(a.1,!a.2))++z

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PacketWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix
open scoped _root_.Matrix _root_.OAI.Matrix BigOperators

attribute [local instance] Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

def sourcePacketWord (w:List (S × Bool)) : List ((S ⊕ Unit) × Bool) :=
  w.map fun b=>(Sum.inl b.1,b.2)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_SignedLetter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K]
  (M:CoxeterMatrix S)

noncomputable def sourceSignedLetter (a:S×Bool) : Artin M :=
  if a.2 then generator M a.1 else (generator M a.1)⁻¹
noncomputable def sourceSignedWord (w:List (S×Bool)) : Artin M :=
  (w.map (sourceSignedLetter M)).prod

omit [Fintype S] [LinearOrder S] in
lemma sourceSignedWord_cons (a:S×Bool) (w:List (S×Bool)) :
    sourceSignedWord M (a::w)=sourceSignedLetter M a*sourceSignedWord M w := rfl

omit [Fintype S] [LinearOrder S] in
lemma artinParabolic_signed_word (J:Set S) (g:Artin M) (hg:g∈artinParabolic M J) :
    ∃ w:List (S×Bool),(∀ a∈w,a.1∈J) ∧ sourceSignedWord M w=g := by
  apply Subgroup.closure_induction_left
    (p:=fun g _=>∃ w:List (S×Bool),(∀ a∈w,a.1∈J) ∧ sourceSignedWord M w=g) ?_ ?_ ?_ hg
  · exact ⟨[],by simp, rfl⟩
  · rintro g ⟨s,hs,rfl⟩ y hy ⟨w,hw,rfl⟩
    refine ⟨(s,true)::w,?_,?_⟩
    · intro a ha
      rcases List.mem_cons.mp ha with rfl|ha
      · exact hs
      · exact hw a ha
    · simp only [sourceSignedWord_cons,sourceSignedLetter,ite_true, if_true]
  · rintro g ⟨s,hs,rfl⟩ y hy ⟨w,hw,rfl⟩
    refine ⟨(s,false)::w,?_,?_⟩
    · intro a ha
      rcases List.mem_cons.mp ha with rfl|ha
      · exact hs
      · exact hw a ha
    · simp only [sourceSignedWord_cons,sourceSignedLetter,Bool.false_eq_true,ite_false, if_false]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_CosetBelow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

omit [Fintype S] [LinearOrder S] in
lemma sourceSplit_types {B C R V R' V':Set S} (hd:Disjoint B C)
    (hR:R⊆B) (hV:V⊆C) (hR':R'⊆B) (hV':V'⊆C) :
    R∪V⊆R'∪V' ↔ R⊆R' ∧ V⊆V' := by
  constructor
  · intro h
    constructor
    · intro s hs
      rcases h (Or.inl hs) with hp|hp
      · exact hp
      · exact False.elim (Set.disjoint_left.mp hd (hR hs) (hV' hp))
    · intro s hs
      rcases h (Or.inr hs) with hp|hp
      · exact False.elim (Set.disjoint_left.mp hd (hR' hp) (hV hs))
      · exact hp
  · rintro ⟨h,h'⟩ s (hs|hs)
    · exact Or.inl (h hs)
    · exact Or.inr (h' hs)

omit [Fintype S] [LinearOrder S] in
lemma sourceSplit_inter {B C R V:Set S} (hd:Disjoint B C) (hR:R⊆B) (hV:V⊆C) :
    (R∪V)∩B=R ∧ (R∪V)∩C=V := by
  constructor
  · ext s
    constructor
    · rintro ⟨hs,hb⟩
      rcases hs with hs|hs
      · exact hs
      · exact False.elim (Set.disjoint_left.mp hd hb (hV hs))
    · intro hs;exact ⟨Or.inl hs,hR hs⟩
  · ext s
    constructor
    · rintro ⟨hs,hc⟩
      rcases hs with hs|hs
      · exact False.elim (Set.disjoint_left.mp hd (hR hs) hc)
      · exact hs
    · intro hs;exact ⟨Or.inr hs,hV hs⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_FiniteWeightedNatSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped BigOperators

theorem finite_weighted_nat_sums {ι:Type*} [Fintype ι]
    (w:ι→ℝ) (hw:∀ i,0<w i) (B:ℝ) :
    {x:ℝ | x≤B ∧ ∃ n:ι→ℕ,x=∑ i,w i*(n i:ℝ)}.Finite := by
  classical
  choose N hN using fun i=>exists_nat_gt (B / w i)
  have hfinite : {n:ι→ℕ | ∀ i,n i≤N i}.Finite := by
    exact (Set.finite_Iic N)
  apply (hfinite.image (fun n:ι→ℕ=>∑ i,w i*(n i:ℝ))).subset
  rintro x ⟨hB,n,rfl⟩
  refine ⟨n,?_,rfl⟩
  intro i
  have hs:w i*(n i:ℝ)≤∑ j,w j*(n j:ℝ) :=
    Finset.single_le_sum (fun j _=>mul_nonneg (hw j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)
  have hn:(n i:ℝ)≤B/w i := (le_div_iff₀ (hw i)).mpr (by simpa [mul_comm] using hs.trans hB)
  exact_mod_cast (hn.trans (hN i).le)

theorem finite_normalized_weighted_nat_sums {ι:Type*} [Fintype ι]
    (w:ι→ℝ) (hw:∀ i,0<w i) (a:ℝ) (ha:0<a) (B:ℝ) :
    {x:ℝ | x≤B ∧ ∃ n:ι→ℕ,x=(∑ i,w i*(n i:ℝ))/a}.Finite := by
  have h:=finite_weighted_nat_sums (fun i=>w i/a) (fun i=>div_pos (hw i) ha) B
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [Set.mem_ofPred_eq]
  apply and_congr_right
  intro hx
  apply exists_congr
  intro n
  have he : (∑ i,w i*(n i:ℝ))/a=∑ i,w i/a*(n i:ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_CosetSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable

lemma harmonicExtension_zero {ι:Type*} [Fintype ι] (C:Matrix ι ι ℝ) (T:Set ι) :
    harmonicExtension C T 0=0 := by
  funext i
  simp [harmonicExtension,Matrix.mulVec,dotProduct]

lemma harmonicExtension_congr_exterior {ι:Type*} [Fintype ι]
    (C:Matrix ι ι ℝ) (T:Set ι) {v w:ι→ℝ} (h:∀i,i∉T→v i=w i) :
    harmonicExtension C T v=harmonicExtension C T w := by
  funext i
  by_cases hi:i∈T
  · simp only [harmonicExtension,dite_eq_left hi]
    congr 2
    funext j
    apply Finset.sum_congr rfl
    intro k _
    rw [h k k.property]
  · simp only [harmonicExtension,dite_eq_right hi,h i hi]

lemma finite_harmonic_images {ι:Type*} [Fintype ι]
    (C:Matrix ι ι ℝ) (A:Set ℝ) (hA:A.Finite) :
    {p:ι→ℝ | ∃ T:Set ι,∃ v:ι→ℝ,(∀i,v i∈A) ∧ p=harmonicExtension C T v}.Finite := by
  have hv:{v:ι→ℝ | ∀i,v i∈A}.Finite := by
    exact Set.Finite.pi' (fun _=>hA)
  have h:((Set.univ:Set (Set ι)) ×ˢ {v:ι→ℝ | ∀i,v i∈A}).Finite :=
    Set.finite_univ.prod hv
  apply (h.image fun Tv=>harmonicExtension C Tv.1 Tv.2).subset
  rintro p ⟨T,v,hv,rfl⟩
  exact ⟨(T,v),⟨Set.mem_univ _,hv⟩,rfl⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.StdSimplexCompat
attribute [-instance] _root_.OAI.closedSubmoduleNormedAddCommGroup _root_.OAI.isProbabilityMeasure_map_fst _root_.OAI.isProbabilityMeasure_map_measurableEquiv _root_.OAI.isProbabilityMeasure_map_snd _root_.OAI.isProbabilityMeasure_map_subtype_val _root_.OAI.vonNeumannToStarSubalgebraIsClosed
/-!
# Standard simplex compatibility layer for ports of openai/math

This file is not OpenAI's code. OpenAI's openai/math is built on Mathlib `d13f23b`; prove2.me's
environment is Mathlib `0df444a`. Both have the structure `Convexity.StdSimplex`, but `0df444a`
lacks part of its API (the files `Mathlib.Geometry.Convex.ConvexSpace.{Topology,
CompactSpaceStdSimplex, Barycenter, PathConnectedSpaceStdSimplex}` and some lemmas of `Defs`),
and its `SimplexCategory.toTop` takes the topological simplex to be the subtype
`stdSimplex ℝ (Fin (n+1))`, where `d13f23b` takes the structure.

Part 1 adds the missing `d13f23b` API to `Convexity.StdSimplex` under its `d13f23b` names. It is
copied from Mathlib `d13f23b` (Copyright (c) 2025 Lean FRO, LLC, authors Kim Morrison, Andrew
Yang, Yaël Dillies; Copyright (c) 2026 Joël Riou; released under the Apache 2.0 license), adapted
to `0df444a` (module keywords removed).

Part 2 (`OAI.SStd`) is ours: the subtype `stdSimplex R X` on a finite type with the `d13f23b`
names, for ported code that identifies the simplex with `SimplexCategory.toTop.obj`; there the
port rewrites `Convexity.StdSimplex` to `OAI.SStd`.
-/

noncomputable section StdSimplexCompat

universe u v w

open Topology

/-! ## Part 1: the `d13f23b` API missing from `0df444a`, on `Convexity.StdSimplex` -/

/-! ## Part 2: `OAI.SStd`, the subtype `stdSimplex R X` with the `d13f23b` names -/

namespace OAI

/-- The standard simplex on a finite type, as the subtype `stdSimplex R X`
(the topological simplex of this Mathlib's `SimplexCategory.toTop`). -/
abbrev SStd (R : Type*) [Semiring R] [PartialOrder R] (X : Type*) [Fintype X] : Type _ :=
  ↥(stdSimplex R X)

namespace SStd

section Semiring

variable {R : Type*} [Semiring R] [PartialOrder R]
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- The weights as a finitely supported function. -/
noncomputable def weights (s : SStd R X) : X →₀ R := Finsupp.equivFunOnFinite.symm s.1

lemma weights_apply (s : SStd R X) (x : X) : s.weights x = s.1 x := rfl

lemma weights_nonneg (s : SStd R X) (x : X) : 0 ≤ s.weights x := s.2.1 x

lemma total_of_fintype (s : SStd R X) : ∑ x, s.weights x = 1 := s.2.2

lemma ext {s t : SStd R X} (h : s.weights = t.weights) : s = t :=
  Subtype.ext (congrArg (fun f : X →₀ R => (f : X → R)) h)

end Semiring

end SStd

end OAI

end StdSimplexCompat
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_OrderWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open Simplicial CategoryTheory Opposite Convexity
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

structure OrderWeights (P:Type u) [PartialOrder P] where
  weights:P→₀ℝ
  nonneg:∀p,0≤weights p
  total:weights.sum (fun _ a=>a)=1
  chain:∀p∈weights.support,∀q∈weights.support,p≤q ∨ q≤p

@[ext] lemma OrderWeights.ext {x y:OrderWeights P} (h:x.weights=y.weights) : x=y := by
  cases x;cases y;cases h;rfl

lemma OrderWeights.support_nonempty (x:OrderWeights P) : x.weights.support.Nonempty := by
  by_contra hn
  have he:x.weights=0:=Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hn)
  have ht:=x.total
  rw [he,Finsupp.sum_zero_index] at ht
  norm_num at ht

noncomputable def chainWeights {n:ℕ} (x:Fin (n+1)→o P) (z:StdSimplex ℝ (Fin (n+1))) : P→₀ℝ :=
  ∑i,Finsupp.single (x i) (z.weights i)

lemma chainWeights_apply {n:ℕ} (x:Fin (n+1)→o P) (z:StdSimplex ℝ (Fin (n+1))) (p:P) :
    chainWeights x z p=∑i,if x i=p then z.weights i else 0 := by
  simp only [chainWeights,Finsupp.finsetSum_apply,Finsupp.single_apply]

lemma chainWeights_nonneg {n:ℕ} (x:Fin (n+1)→o P) (z:StdSimplex ℝ (Fin (n+1))) (p:P) :
    0 ≤ chainWeights x z p := by
  rw [chainWeights_apply]
  exact Finset.sum_nonneg (fun i _=>by split_ifs; exacts [z.nonneg i,le_rfl])

lemma chainWeights_support {n:ℕ} (x:Fin (n+1)→o P) (z:StdSimplex ℝ (Fin (n+1))) :
    (chainWeights x z).support⊆Finset.univ.image x := by
  apply Finset.Subset.trans Finsupp.support_finsetSum
  intro p hp
  obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hp
  have he:p=x i:=Finset.mem_singleton.mp (Finsupp.support_single_subset hi)
  exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he.symm⟩

noncomputable def nerveChain {n:SimplexCategory} (x:(nerve P).obj (op n)) : Fin (n.len+1)→o P where
  toFun:=x.obj
  monotone':=by intro i j h;exact leOfHom (x.map (homOfLE h))

lemma chainWeights_natural {n m:ℕ} (x:Fin (m+1)→o P) (a:Fin (n+1)→o Fin (m+1))
    (z:StdSimplex ℝ (Fin (n+1))) :
    chainWeights (x.comp a) z=chainWeights x (StdSimplex.map a z) := by
  have chainWeights_eq {dimension : ℕ} (chain : Fin (dimension+1) →o P)
      (simplex : StdSimplex ℝ (Fin (dimension+1))) :
      chainWeights chain simplex = simplex.weights.mapDomain chain := by
    simp [chainWeights, Finsupp.mapDomain, Finsupp.sum_fintype]
  rw [chainWeights_eq, chainWeights_eq]
  exact Finsupp.mapDomain_comp (v := z.weights) (f := a) (g := x)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_SimplexSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open Convexity
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

noncomputable def simplexSupport {n:ℕ} (z:StdSimplex ℝ (Fin (n+1))) : Finset (Fin (n+1)) :=
  Finset.univ.filter (fun index=>z.weights index≠0)

lemma mem_simplexSupport {n:ℕ} (z:StdSimplex ℝ (Fin (n+1))) (i:Fin (n+1)) :
    i∈simplexSupport z ↔ z.weights i≠0 := by simp [simplexSupport]

noncomputable def simplexSupportDim {n:ℕ} (z:StdSimplex ℝ (Fin (n+1))) : ℕ :=
  (simplexSupport z).card-1

lemma chainWeights_support_positive {n:ℕ} (x:Fin (n+1)→o P)
    (z:StdSimplex ℝ (Fin (n+1))) {i:Fin (n+1)} (hi:i∈simplexSupport z) :
    x i∈(chainWeights x z).support := by
  rw [Finsupp.mem_support_iff]
  have hz:0<z.weights i:=lt_of_le_of_ne (z.nonneg i) (Ne.symm ((mem_simplexSupport z i).mp hi))
  have hs:z.weights i ≤ chainWeights x z (x i):=by
    rw [chainWeights_apply]
    calc
      _=(if x i=x i then z.weights i else 0):=by simp
      _≤_:=Finset.single_le_sum (f:=fun index:Fin (n+1)=>if x index=x i then z.weights index else 0)
        (fun index _=>by split_ifs;exacts [z.nonneg index,le_rfl]) (Finset.mem_univ i)
  exact ne_of_gt (lt_of_lt_of_le hz hs)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_WeightDim
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped BigOperators
open Simplicial CategoryTheory Opposite Convexity

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

noncomputable instance orderWeightSupportLinearOrder (w:OrderWeights P) :
    LinearOrder {p // p∈w.weights.support} :=
  IsChain.linearOrder (show IsChain (·≤·) (↑w.weights.support:Set P) from
    fun left hleft right hright _ => w.chain left hleft right hright)

noncomputable def weightDim (w:OrderWeights P) : ℕ := w.weights.support.card-1

lemma weightDim_succ (w:OrderWeights P) : weightDim w+1=w.weights.support.card := by
  have :=w.support_nonempty.card_pos
  unfold weightDim
  omega

noncomputable def weightEnum (w:OrderWeights P) :
    Fin (weightDim w+1) ≃o {p // p∈w.weights.support} :=
  Fintype.orderIsoFinOfCardEq _ (by rw [Fintype.card_coe,weightDim_succ])

noncomputable def weightChain (w:OrderWeights P) : Fin (weightDim w+1) →o P where
  toFun:=fun i=>(weightEnum w i).val
  monotone':=fun _ _ h=>(weightEnum w).monotone h

lemma weightChain_injective (w:OrderWeights P) : Function.Injective (weightChain w) :=
  Subtype.val_injective.comp (weightEnum w).injective

noncomputable def weightSimplex (w:OrderWeights P) : StdSimplex ℝ (Fin (weightDim w+1)) :=
  ⟨Finsupp.equivFunOnFinite.symm (fun coordinate=>w.weights (weightChain w coordinate)),
    fun coordinate=>w.nonneg _,by
    have he:=Equiv.sum_comp (weightEnum w).toEquiv (fun p=>w.weights p.val)
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change (∑i,w.weights (weightChain w i))=1
    rw [show (∑i,w.weights (weightChain w i))=∑p:w.weights.support,w.weights p.val from he]
    rw [Finset.sum_coe_sort]
    exact w.total⟩

lemma chainWeights_injective_apply {n:ℕ} (x:Fin (n+1)→o P)
    (hx:Function.Injective x) (z:StdSimplex ℝ (Fin (n+1))) (i:Fin (n+1)) :
    chainWeights x z (x i)=z.weights i := by
  rw [chainWeights_apply,Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hx.ne hj]
  · simp

lemma chainWeights_coordinates_injective {n:ℕ} (x:Fin (n+1)→o P)
    (hx:Function.Injective x) {z z':StdSimplex ℝ (Fin (n+1))}
    (h:chainWeights x z=chainWeights x z') : z=z' := by
  apply StdSimplex.ext
  ext coordinate
  have he:=congrArg (fun weights:P→₀ℝ=>weights (x coordinate)) h
  simpa only [chainWeights_injective_apply x hx] using he

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_NerveChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped BigOperators
open Simplicial CategoryTheory Opposite Convexity

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

noncomputable def nerveOfChain {n:ℕ} (x:Fin (n+1) →o P) : (nerve P).obj (op ⦋n⦌) := x.toFunctor

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_WeightMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped BigOperators
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable
universe u v
variable {P:Type u} {Q:Type v} [PartialOrder P] [PartialOrder Q]

noncomputable def weightMap (f:P→oQ) (w:OrderWeights P) : OrderWeights Q where
  weights:=w.weights.mapDomain f
  nonneg q:=by
    unfold Finsupp.mapDomain
    rw [Finsupp.sum_apply]
    exact Finset.sum_nonneg (fun p _=>by
      simp only [Finsupp.single_apply]
      split_ifs; exacts [w.nonneg p,le_rfl])
  total:=by
    rw [Finsupp.sum_mapDomain_index (by intros;rfl) (by intros;rfl)]
    exact w.total
  chain:=by
    intro p hp q hq
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp (Finsupp.mapDomain_support hp)
    obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp (Finsupp.mapDomain_support hq)
    exact (w.chain a ha b hb).imp (fun h=>f.monotone h) (fun h=>f.monotone h)

lemma weightMap_id (w:OrderWeights P) : weightMap OrderHom.id w=w := by
  apply OrderWeights.ext
  exact Finsupp.mapDomain_id

lemma weightMap_comp {R:Type*} [PartialOrder R] (f:P→oQ) (g:Q→oR) (w:OrderWeights P) :
    weightMap g (weightMap f w)=weightMap (g.comp f) w := by
  apply OrderWeights.ext
  exact Finsupp.mapDomain_comp.symm

lemma weightMap_injective (f:P→oQ) (hf:Function.Injective f) : Function.Injective (weightMap f) := by
  intro x y h
  apply OrderWeights.ext
  have he:=congrArg OrderWeights.weights h
  change x.weights.mapDomain f=y.weights.mapDomain f at he
  exact Finsupp.mapDomain_injective hf he

lemma weightMap_apply_embedding (f:P→oQ) (hf:Function.Injective f) (w:OrderWeights P) (p:P) :
    (weightMap f w).weights (f p)=w.weights p := by
  change (w.weights.mapDomain f) (f p)=_
  exact Finsupp.mapDomain_apply hf _ _

lemma weightMap_support_embedding (f:P→oQ) (hf:Function.Injective f) (w:OrderWeights P) :
    (weightMap f w).weights.support=w.weights.support.image f :=
  Finsupp.mapDomain_support_of_injective hf w.weights

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_FiniteChainEnum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped BigOperators
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

noncomputable def finiteChainEnum (C:Finset P) (hC:IsChain (·≤·) (↑C:Set P)) (hne:C.Nonempty) :
    Fin (C.card-1+1) ≃o {p // p∈C} := by
  letI := IsChain.linearOrder hC
  exact Fintype.orderIsoFinOfCardEq _ (by rw [Fintype.card_coe];have:=hne.card_pos;omega)

noncomputable def finiteChainOrder (C:Finset P) (hC:IsChain (·≤·) (↑C:Set P)) (hne:C.Nonempty) :
    Fin (C.card-1+1) →o P where
  toFun:=fun i=>(finiteChainEnum C hC hne i).val
  monotone':=fun _ _ h=>(finiteChainEnum C hC hne).monotone h

lemma finiteChainOrder_injective (C:Finset P) (hC:IsChain (·≤·) (↑C:Set P)) (hne:C.Nonempty) :
    Function.Injective (finiteChainOrder C hC hne) :=
  Subtype.val_injective.comp (finiteChainEnum C hC hne).injective

noncomputable def carrierSimplex (C:Finset P) (hC:IsChain (·≤·) (↑C:Set P)) (hne:C.Nonempty)
    (w:OrderWeights P) (hw:w.weights.support⊆C) : Convexity.StdSimplex ℝ (Fin (C.card-1+1)) :=
  ⟨Finsupp.equivFunOnFinite.symm (fun index=>w.weights (finiteChainOrder C hC hne index)),
    fun index=>w.nonneg _,by
    have he:=Equiv.sum_comp (finiteChainEnum C hC hne).toEquiv (fun p=>w.weights p.val)
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change (∑i,w.weights (finiteChainOrder C hC hne i))=1
    rw [show (∑i,w.weights (finiteChainOrder C hC hne i))=∑p:C,w.weights p.val from he,
      Finset.sum_coe_sort]
    rw [← w.total]
    symm
    apply Finset.sum_subset hw
    intro p _ hp
    exact Finsupp.notMem_support_iff.mp hp⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_HarmonicUpperAntitone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix

theorem harmonic_upper_antitone {ι:Type*} [Fintype ι]
    (C:Matrix ι ι ℝ) (hOff:∀i j,i≠j→C i j≤0) (U:Set ι)
    (hU:(C.submatrix Subtype.val Subtype.val:Matrix U U ℝ).PosDef)
    (p q:ι→ℝ) (hExt:∀i∉U,q i=p i) (hHarm:∀i:U,(C *ᵥ q) i=0)
    (hrow:∀i:U,0≤(C *ᵥ p) i) : q≤p := by
  classical
  have hv:∀i:U,0≤((C.submatrix Subtype.val Subtype.val:Matrix U U ℝ)⁻¹ *ᵥ
      (fun i:U=>(C *ᵥ p) i)) i :=
    harmonic_extension_nonneg _ hU
      (fun i j hij=>hOff i j (fun he=>hij (Subtype.ext he))) _ hrow
  have hc:=harmonic_upper_change C U hU p q hExt hHarm
  intro i
  by_cases hi:i∈U
  · have hh:=congrFun hc ⟨i,hi⟩
    have hh0:=hv ⟨i,hi⟩
    simp only [Pi.neg_apply] at hh
    linarith
  · exact le_of_eq (hExt i hi)

theorem harmonic_upper_monotone {ι:Type*} [Fintype ι]
    (C:Matrix ι ι ℝ) (hOff:∀i j,i≠j→C i j≤0) (U:Set ι)
    (hU:(C.submatrix Subtype.val Subtype.val:Matrix U U ℝ).PosDef)
    (p q:ι→ℝ) (hExt:∀i∉U,q i=p i) (hHarm:∀i:U,(C *ᵥ q) i=0)
    (hrow:∀i:U,(C *ᵥ p) i≤0) : p≤q := by
  have h:=harmonic_upper_antitone C hOff U hU (-p) (-q)
    (fun i hi=>by simp only [Pi.neg_apply,hExt i hi])
    (fun i=>by rw [Matrix.mulVec_neg]; simp only [Pi.neg_apply,hHarm i,neg_zero])
    (fun i=>by rw [Matrix.mulVec_neg]; exact neg_nonneg.mpr (hrow i))
  intro i
  exact neg_le_neg_iff.mp (h i)

lemma harmonic_sum_lt_of_lt {ι:Type*} [Fintype ι] (p q:ι→ℝ)
    (h:p≤q) (hne:p≠q) : (∑i,p i)<∑i,q i := by
  classical
  apply Finset.sum_lt_sum (fun i _=>h i)
  by_contra hn
  apply hne
  funext i
  exact le_antisymm (h i) (le_of_not_gt (fun hi=>hn ⟨i,Finset.mem_univ _,hi⟩))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_ConeWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped BigOperators unitInterval
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable
universe u v
variable {P:Type u} {Q:Type v} [PartialOrder P] [PartialOrder Q]

noncomputable def coneWeights (f:Q→oP) (v:P) (hv:∀q,f q≤v ∨ v≤f q)
    (t:I) (w:OrderWeights Q) : OrderWeights P where
  weights:=(σ t).val • (weightMap f w).weights + Finsupp.single v t.val
  nonneg p:=by
    change 0≤ (σ t).val * (weightMap f w).weights p + (Finsupp.single v t.val) p
    apply add_nonneg (mul_nonneg (σ t).property.1 ((weightMap f w).nonneg p))
    simp only [Finsupp.single_apply]
    split_ifs; exacts [t.property.1,le_rfl]
  total:=by
    rw [Finsupp.sum_add_index (by intros;rfl) (by intros;rfl),
      Finsupp.sum_single_index (by rfl),Finsupp.sum_smul_index (by intros;rfl)]
    change (∑p∈(weightMap f w).weights.support,(σ t).val * (weightMap f w).weights p)+t.val=1
    rw [←Finset.mul_sum]
    change (σ t).val * ((weightMap f w).weights.sum (fun _ a=>a))+t.val=1
    rw [(weightMap f w).total]
    change (1-t.val)*1+t.val=1
    ring
  chain:=by
    intro a ha b hb
    have hl {p:P} (h:p∈((σ t).val • (weightMap f w).weights + Finsupp.single v t.val).support) :
        p∈(weightMap f w).weights.support ∨ p=v:=by
      rcases Finset.mem_union.mp (Finsupp.support_add h) with h|h
      · exact Or.inl (Finsupp.support_smul h)
      · exact Or.inr (Finset.mem_singleton.mp (Finsupp.support_single_subset h))
    rcases hl ha with hpa|hpa
    · rcases hl hb with hpb|hpb
      · exact (weightMap f w).chain _ hpa _ hpb
      · subst b
        obtain ⟨q,_,rfl⟩:=Finset.mem_image.mp (Finsupp.mapDomain_support hpa)
        exact hv q
    · subst a
      rcases hl hb with hpb|hpb
      · obtain ⟨q,_,rfl⟩:=Finset.mem_image.mp (Finsupp.mapDomain_support hpb)
        exact (hv q).symm
      · subst b
        exact Or.inl le_rfl

lemma coneWeights_apply (f:Q→oP) (v:P) (hv:∀q,f q≤v ∨ v≤f q)
    (t:I) (w:OrderWeights Q) (p:P) :
    (coneWeights f v hv t w).weights p=(1-t.val)*(weightMap f w).weights p+if v=p then t.val else 0 := by
  simp [coneWeights,Finsupp.single_apply,unitInterval.symm]

lemma coneWeights_zero (f:Q→oP) (v:P) (hv:∀q,f q≤v ∨ v≤f q) (w:OrderWeights Q) :
    coneWeights f v hv 0 w=weightMap f w := by
  apply OrderWeights.ext
  change (σ (0:I)).val • (weightMap f w).weights+Finsupp.single v (0:ℝ)=_
  simp

lemma coneWeights_support (f:Q→oP) (v:P) (hv:∀q,f q≤v ∨ v≤f q) (t:I) (w:OrderWeights Q) :
    (coneWeights f v hv t w).weights.support⊆insert v (w.weights.support.image f) := by
  intro p hp
  rcases Finset.mem_union.mp (Finsupp.support_add hp) with h|h
  · exact Finset.mem_insert_of_mem (Finsupp.mapDomain_support (Finsupp.support_smul h))
  · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp (Finsupp.support_single_subset h)))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_WeightInclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped BigOperators unitInterval
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

noncomputable def weightInclusion (A:Set P) : A→oP :=⟨Subtype.val,fun _ _ h=>h⟩

noncomputable def weightRestrict (A:Set P) (w:OrderWeights P) (hw:∀p∈w.weights.support,p∈A) : OrderWeights A where
  weights:=w.weights.subtypeDomain (·∈A)
  nonneg p:=w.nonneg p.val
  total:=by
    exact (Finsupp.sum_subtypeDomain_index (h := fun (_:P) (a:ℝ)=>a) hw).trans w.total
  chain:=by
    intro p hp q hq
    apply w.chain p.val _ q.val _
    · rw [Finsupp.mem_support_iff] at hp ⊢
      exact hp
    · rw [Finsupp.mem_support_iff] at hq ⊢
      exact hq

lemma weightRestrict_map (A:Set P) (w:OrderWeights P) (hw:∀p∈w.weights.support,p∈A) :
    weightMap (weightInclusion A) (weightRestrict A w hw)=w := by
  apply OrderWeights.ext
  ext p
  by_cases hp:p∈A
  · exact weightMap_apply_embedding (weightInclusion A) Subtype.val_injective _ ⟨p,hp⟩
  · have h₁:p∉(weightMap (weightInclusion A) (weightRestrict A w hw)).weights.support:=by
      rw [weightMap_support_embedding _ Subtype.val_injective]
      rintro hx
      obtain ⟨q,_,he⟩:=Finset.mem_image.mp hx
      exact hp (he ▸ q.property)
    have h₂:p∉w.weights.support:=fun h=>hp (hw _ h)
    exact (Finsupp.notMem_support_iff.mp h₁).trans (Finsupp.notMem_support_iff.mp h₂).symm

lemma weight_le_one (w:OrderWeights P) (p:P) : w.weights p≤1 := by
  by_cases hp:p∈w.weights.support
  · rw [←w.total]
    exact Finset.single_le_sum (fun q _=>w.nonneg q) hp
  · rw [Finsupp.notMem_support_iff.mp hp]
    norm_num

noncomputable def weightTime (v:P) (w:OrderWeights P) : I :=⟨w.weights v,w.nonneg v,weight_le_one w v⟩

noncomputable def weightVertex (v:P) : OrderWeights P where
  weights:=Finsupp.single v 1
  nonneg p:=by simp only [Finsupp.single_apply];split_ifs <;> norm_num
  total:=by simp
  chain:=by
    intro p hp q hq
    have hpv:p=v:=Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
    have hqv:q=v:=Finset.mem_singleton.mp (Finsupp.support_single_subset hq)
    subst p;subst q;exact Or.inl le_rfl

lemma coneWeights_one_vertex {Q:Type*} [PartialOrder Q] (f:Q→oP) (v:P) (hv:∀q,f q≤v ∨ v≤f q)
    (w:OrderWeights Q) : coneWeights f v hv 1 w=weightVertex v := by
  apply OrderWeights.ext
  simp [coneWeights,weightVertex]

lemma weight_eq_vertex_of_one (w:OrderWeights P) (v:P) (hv:w.weights v=1) : w=weightVertex v := by
  have hvS:v∈w.weights.support:=Finsupp.mem_support_iff.mpr (hv ▸ one_ne_zero)
  have hsum:∑p∈w.weights.support.erase v,w.weights p=0:=by
    have ht:=w.total
    change (∑p∈w.weights.support,w.weights p)=1 at ht
    rw [←Finset.add_sum_erase _ _ hvS,hv] at ht
    linarith
  apply OrderWeights.ext
  ext p
  by_cases hp:p=v
  · subst p;simp [weightVertex,hv]
  · have he:w.weights p=0:=by
      by_cases hps:p∈w.weights.support
      · have hm:p∈w.weights.support.erase v:=Finset.mem_erase.mpr ⟨hp,hps⟩
        have hl:=Finset.single_le_sum (fun q _=>w.nonneg q) hm
        rw [hsum] at hl
        exact le_antisymm hl (w.nonneg p)
      · exact Finsupp.notMem_support_iff.mp hps
    simp [weightVertex,he,Ne.symm hp]

noncomputable def weightDelete (v:P) (w:OrderWeights P) (hv:w.weights v<1) : OrderWeights P where
  weights:=(1-w.weights v)⁻¹ • w.weights.erase v
  nonneg p:=by
    change 0≤ (1-w.weights v)⁻¹ * (w.weights.erase v) p
    apply mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hv.le))
    by_cases hp:p=v
    · subst p;simp
    · rw [Finsupp.erase_ne hp]
      exact w.nonneg p
  total:=by
    rw [Finsupp.sum_smul_index (by intros;rfl)]
    change (∑p∈(w.weights.erase v).support,(1-w.weights v)⁻¹*(w.weights.erase v) p)=1
    rw [←Finset.mul_sum]
    have he:(w.weights.erase v).sum (fun _ a=>a)=1-w.weights v:=by
      have hh:=congrArg (fun z:P→₀ℝ=>z.sum (fun _ a=>a)) (Finsupp.single_add_erase v w.weights)
      rw [Finsupp.sum_add_index (by intros;rfl) (by intros;rfl),Finsupp.sum_single_index (by rfl),w.total] at hh
      linarith
    change (1-w.weights v)⁻¹*((w.weights.erase v).sum (fun _ a=>a))=1
    rw [he,inv_mul_cancel₀ (ne_of_gt (sub_pos.mpr hv))]
  chain:=by
    intro p hp q hq
    apply w.chain p _ q _
    · have ht:=Finsupp.support_smul hp
      rw [Finsupp.support_erase] at ht
      exact (Finset.mem_erase.mp ht).2
    · have ht:=Finsupp.support_smul hq
      rw [Finsupp.support_erase] at ht
      exact (Finset.mem_erase.mp ht).2

lemma weightDelete_apply (v:P) (w:OrderWeights P) (hv:w.weights v<1) (p:P) :
    (weightDelete v w hv).weights p=(1-w.weights v)⁻¹*(if p=v then 0 else w.weights p) := by
  simp only [weightDelete,Finsupp.smul_apply,smul_eq_mul,Finsupp.erase_apply]

lemma weightDelete_support (v:P) (w:OrderWeights P) (hv:w.weights v<1) :
    (weightDelete v w hv).weights.support⊆w.weights.support.erase v := by
  exact Finsupp.support_smul.trans (by rw [Finsupp.support_erase])

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_WeightHomeomorph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

universe u v
variable {P:Type u} {Q:Type v} [PartialOrder P] [PartialOrder Q]

lemma weightMap_vertex (f:P→oQ) (p:P) : weightMap f (weightVertex p)=weightVertex (f p) := by
  apply OrderWeights.ext
  exact Finsupp.mapDomain_single

noncomputable def weightSubset (A B:Set P) (h:A⊆B) : A→oB :=
  ⟨fun p=>⟨p.val,h p.property⟩,fun _ _ he=>he⟩

lemma weightSubset_self (A:Set P) (h:A⊆A) : weightSubset A A h=OrderHom.id :=by ext p;rfl

noncomputable def transportContraction {X Y:Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e:X≃ₜY) (c:X) (H:ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.const X c)) :
    ContinuousMap.Homotopy (ContinuousMap.id Y) (ContinuousMap.const Y (e c)) where
  toFun p:=e (H (p.1,e.symm p.2))
  continuous_toFun:=e.continuous.comp (H.continuous.comp
    (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)))
  map_zero_left x:=by rw [H.apply_zero];exact e.apply_symm_apply x
  map_one_left x:=by rw [H.apply_one];rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_LateDelay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval
open Topology

attribute [local instance] Classical.propDecidable
universe u v
variable {A:Type u} {X:Type v} [TopologicalSpace A] [TopologicalSpace X] [T2Space X]

abbrev LateDelay (δ:C(X,I)) := {p:I×X // δ p.2≤p.1}

noncomputable def lateDelayTime (δ:C(X,I)) (hd:∀x,δ x<1) : C(LateDelay δ,I) where
  toFun p:=⟨(p.val.1.val-(δ p.val.2).val)/(1-(δ p.val.2).val),by
    have hpos:0<1-(δ p.val.2).val:=sub_pos.mpr (hd _)
    exact ⟨div_nonneg (sub_nonneg.mpr p.property) hpos.le,
      (div_le_one hpos).mpr (sub_le_sub_right p.val.1.property.2 _)⟩⟩
  continuous_toFun:=by
    apply Continuous.subtype_mk
    exact ((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).sub
      (continuous_subtype_val.comp (δ.continuous.comp (continuous_snd.comp continuous_subtype_val)))).div
      (continuous_const.sub (continuous_subtype_val.comp (δ.continuous.comp (continuous_snd.comp continuous_subtype_val))))
      (fun p=>ne_of_gt (sub_pos.mpr (hd _)))

variable (i:C(A,X)) (r:C(X,A)) (hr:∀a,r (i a)=a)
  (D:ContinuousMap.HomotopyRel (ContinuousMap.id X) (i.comp r) (Set.range i))
  (δ:C(X,I)) (hd:∀x,δ x<1) (hz:∀x,δ x=0↔x∈Set.range i)
  (c:A) (H:ContinuousMap.Homotopy (ContinuousMap.id A) (ContinuousMap.const A c))

include hz in
omit [T2Space X] in
lemma extension_stationary (x:X) (hx:δ x=0) (t:I) : D (t,x)=D (0,x) := by
  rw [D.eq_fst t ((hz x).mp hx),D.apply_zero]

noncomputable def extensionLate : C(LateDelay δ,X) :=
  i.comp (H.toContinuousMap.comp ((lateDelayTime δ hd).prodMk (r.comp ⟨fun p=>p.val.2,continuous_snd.comp continuous_subtype_val⟩)))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_WeightOld
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped BigOperators unitInterval

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

abbrev WeightOld (v:P) := {p:P // p≠v}
abbrev WeightLink (v:P) := {p:P // p≠v ∧ (p≤v ∨ v≤p)}
noncomputable abbrev weightOldIncl (v:P) : WeightOld v→o P :=⟨Subtype.val,fun _ _ h=>h⟩
noncomputable abbrev weightLinkIncl (v:P) : WeightLink v→o P :=⟨Subtype.val,fun _ _ h=>h⟩
noncomputable abbrev weightLinkOld (v:P) : WeightLink v→o WeightOld v :=⟨fun p=>⟨p.val,p.property.1⟩,fun _ _ h=>h⟩

lemma weightMap_zero_of_not_range {Q:Type*} [PartialOrder Q] (f:Q→oP) (w:OrderWeights Q) (p:P)
    (hp:p∉Set.range f) : (weightMap f w).weights p=0 := by
  apply Finsupp.notMem_support_iff.mp
  intro h
  obtain ⟨q,_,he⟩:=Finset.mem_image.mp (Finsupp.mapDomain_support h)
  exact hp ⟨q,he⟩

lemma weightDelete_link {v:P} (w:OrderWeights P) (ht:w.weights v<1) (hp:0<w.weights v) :
    ∀p∈(weightDelete v w ht).weights.support,p≠v ∧ (p≤v ∨ v≤p) := by
  intro p hp'
  have h:=Finset.mem_erase.mp (weightDelete_support v w ht hp')
  exact ⟨h.1,w.chain p h.2 v (Finsupp.mem_support_iff.mpr (ne_of_gt hp))⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_WeightLinearLinkInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped BigOperators unitInterval
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable
universe u v

lemma weightMap_cone {P Q R:Type*} [PartialOrder P] [PartialOrder Q] [PartialOrder R]
    (f:Q→oP) (g:P→oR) (v:P) (hv:∀q,f q≤v ∨ v≤f q) (t:I) (w:OrderWeights Q) :
    weightMap g (coneWeights f v hv t w)=
      coneWeights (g.comp f) (g v) (fun q=>(hv q).imp (fun h=>g.monotone h) (fun h=>g.monotone h)) t w := by
  apply OrderWeights.ext
  change Finsupp.mapDomain g ((σ t).val • (weightMap f w).weights+Finsupp.single v t.val)=_
  rw [Finsupp.mapDomain_add,Finsupp.mapDomain_smul,Finsupp.mapDomain_single]
  congr 1
  exact congrArg (fun z:OrderWeights R=>(σ t).val • z.weights) (weightMap_comp f g w)

lemma weight_support_singleton {P:Type*} [PartialOrder P] (w:OrderWeights P) (v:P)
    (hs:w.weights.support⊆{v}) : w=weightVertex v := by
  have he:=Finsupp.support_subset_singleton.mp hs
  have ht:=w.total
  rw [he,Finsupp.sum_single_index (by rfl)] at ht
  apply weight_eq_vertex_of_one w v ht

noncomputable def weightLinearLinkInverse {P:Type*} [LinearOrder P] (v:P) : WeightOld v→o WeightLink v :=
  ⟨fun p=>⟨p.val,p.property,le_total p.val v⟩,fun _ _ h=>h⟩

noncomputable def weightLinkEmbedding {P Q:Type*} [PartialOrder P] [PartialOrder Q]
    (j:Q↪oP) (v:Q) : WeightLink v→o WeightLink (j v) where
  toFun p:=⟨j p.val,fun h=>p.property.1 (j.injective h),
    p.property.2.imp (fun h=>j.monotone h) (fun h=>j.monotone h)⟩
  monotone':=fun _ _ h=>j.monotone h

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_InsertOldIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

noncomputable def insertOldIso (A:Set P) (v:P) (hv:v∉A) :
    A≃oWeightOld (⟨v,Set.mem_insert v A⟩:↥(insert v A)) where
  toFun x:=⟨⟨x.val,Set.mem_insert_of_mem v x.property⟩,by
    intro he
    have he':x.val=v:=congrArg Subtype.val he
    exact hv (he' ▸ x.property)⟩
  invFun x:=⟨x.val.val,(Set.mem_insert_iff.mp x.val.property).resolve_left (by
    intro he
    exact x.property (Subtype.ext he))⟩
  left_inv x:=rfl
  right_inv x:=rfl
  map_rel_iff':=by intros;rfl

abbrev WeightEarlierLink (r:P→P→Prop) (v:P) := {x:P // r x v ∧ (x≤v ∨ v≤x)}

noncomputable def insertLinkIso (r:P→P→Prop) (hirr:∀x,¬r x x)
    (A:Set P) (v:P) (heA:∀x,x∈A↔r x v) :
    WeightLink (⟨v,Set.mem_insert v A⟩:↥(insert v A))≃oWeightEarlierLink r v where
  toFun x:=⟨x.val.val,(heA _).mp ((Set.mem_insert_iff.mp x.val.property).resolve_left
    (fun he=>x.property.1 (Subtype.ext he))),x.property.2⟩
  invFun x:=⟨⟨x.val,Set.mem_insert_of_mem v ((heA _).mpr x.property.1)⟩,
    (by
      intro he
      have he':x.val=v:=congrArg Subtype.val he
      have hr : r x.val v := x.property.1
      rw [he'] at hr
      exact hirr v hr),x.property.2⟩
  left_inv x:=rfl
  right_inv x:=rfl
  map_rel_iff':=by intros;rfl

lemma insertOldIso_incl (A:Set P) (v:P) (hv:v∉A) :
    (weightOldIncl (⟨v,Set.mem_insert v A⟩:↥(insert v A))).comp (OrderHomClass.toOrderHom (insertOldIso A v hv)) =
      weightSubset A (insert v A) (Set.subset_insert v A) :=rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_WeightMapCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval
open Simplicial

universe u v w z
variable {P:Type u} [PartialOrder P] {J:Type v} {Q:J→Type u} [∀j,PartialOrder (Q j)]
  (f:∀j,Q j→oP) {Z:Type w} [TopologicalSpace Z] [LocallyCompactSpace Z]
  {Y:Type z} [TopologicalSpace Y]

def WeightMapCover : Prop :=
  ∀(n:ℕ) (a:Fin (n+1)→oP),∃i:J,∃b:Fin (n+1)→o Q i,(f i).comp b=a

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_Initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

lemma weight_eq_vertex_subsingleton [Subsingleton P] (w:OrderWeights P) (v:P) : w=weightVertex v := by
  apply weight_eq_vertex_of_one
  have he:w.weights.support={v}:=by
    obtain ⟨x,hx⟩:=w.support_nonempty
    have hxv:x=v:=Subsingleton.elim _ _
    subst x
    apply Finset.eq_singleton_iff_unique_mem.mpr
    exact ⟨hx,fun y _=>Subsingleton.elim _ _⟩
  simpa only [Finsupp.sum,he,Finset.sum_singleton] using w.total

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PositiveComponent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

def sourcePositiveComponent (p:S⊕Unit→ℝ) (i:S⊕Unit) : Set (S⊕Unit) :=
  {j | Relation.ReflTransGen (fun a b=>0<p a ∧ framedCartan M a b<0 ∧ 0<p b) i j}

def sourceClosedRegion (I:Set (S⊕Unit)) : Set (S⊕Unit) :=
  {j | j∈I ∨ ∃i∈I,framedCartan M j i<0}

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PositiveSupportComponent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe u
variable {S : Type u}
open _root_.Matrix
open scoped Classical

def PositiveSupportComponent {ι : Type*} (C : Matrix ι ι ℝ)
    (v : ι → ℝ) (I : Set ι) : Prop :=
  I.Nonempty ∧ (∀ i ∈ I, 0 < v i) ∧
    (∀ i j : I, Relation.ReflTransGen (fun a b : I => C a b < 0) i j) ∧
    ∀ i ∈ I, ∀ j, C i j < 0 → 0 < v j → j ∈ I

def levelIncident {ι : Type*} (C : Matrix ι ι ℝ)
    (p : ℕ →₀ (ι → ℝ)) (k : ℕ) (i : ι) : Prop :=
  0 < p k i ∨ ∃ j, C i j < 0 ∧ 0 < p k j

noncomputable def incidenceIndices {ι : Type*} (C : Matrix ι ι ℝ)
    (p : ℕ →₀ (ι → ℝ)) (i : ι) : Finset ℕ :=
  p.support.filter (fun k => levelIncident C p k i)

noncomputable def incidenceLevel {ι : Type*} (C : Matrix ι ι ℝ)
    (p : ℕ →₀ (ι → ℝ)) (i : ι) : ℕ :=
  (incidenceIndices C p i).sup id

theorem levelIncident_support {ι : Type*} (C : Matrix ι ι ℝ)
    (p : ℕ →₀ (ι → ℝ)) {k : ℕ} {i : ι} (h : levelIncident C p k i) :
    k ∈ p.support := by
  rw [Finsupp.mem_support_iff]
  intro hk
  rcases h with h | ⟨j, _, h⟩ <;> simp only [hk, Pi.zero_apply, lt_self_iff_false] at h

theorem levelIncident_mem {ι : Type*} (C : Matrix ι ι ℝ)
    (p : ℕ →₀ (ι → ℝ)) {k : ℕ} {i : ι} (h : levelIncident C p k i) :
    k ∈ incidenceIndices C p i :=
  Finset.mem_filter.mpr ⟨levelIncident_support C p h, h⟩

theorem levelIncident_le {ι : Type*} (C : Matrix ι ι ℝ)
    (p : ℕ →₀ (ι → ℝ)) {k : ℕ} {i : ι} (h : levelIncident C p k i) :
    k ≤ incidenceLevel C p i :=
  Finset.le_sup (f := id) (levelIncident_mem C p h)

theorem incidenceLevel_incident {ι : Type*} (C : Matrix ι ι ℝ)
    (p : ℕ →₀ (ι → ℝ)) (i : ι) (h : ∃ k, levelIncident C p k i) :
    levelIncident C p (incidenceLevel C p i) i := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨d, hd, hlevel⟩ := Finset.exists_mem_eq_sup (incidenceIndices C p i)
    ⟨k, levelIncident_mem C p hk⟩ id
  change levelIncident C p ((incidenceIndices C p i).sup id) i
  rw [hlevel]
  exact (Finset.mem_filter.mp hd).2

theorem no_incidence_row_zero {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (p : ℕ →₀ (ι → ℝ)) (hp : ∀ k i, 0 ≤ p k i)
    {k : ℕ} {i : ι} (hn : ¬levelIncident C p k i) : (C *ᵥ p k) i = 0 := by
  have hi : p k i = 0 := le_antisymm
    (le_of_not_gt (fun h => hn (Or.inl h))) (hp k i)
  change ∑ j, C i j * p k j = 0
  apply Finset.sum_eq_zero
  intro j _
  by_cases hij : i = j
  · subst j; rw [hi, mul_zero]
  · by_cases hneg : C i j < 0
    · have hj : p k j = 0 := le_antisymm
        (le_of_not_gt (fun h => hn (Or.inr ⟨j, hneg, h⟩))) (hp k j)
      rw [hj, mul_zero]
    · rw [le_antisymm (hOff i j hij) (le_of_not_gt hneg), zero_mul]

theorem matrix_posDef_of_fibers {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : Matrix ι ι ℝ) (hSym : ∀ i j, C i j = C j i) (f : ι → κ)
    (hblock : ∀ i j, f i ≠ f j → C i j = 0)
    (hdef : ∀ b : κ,
      (C.submatrix Subtype.val Subtype.val :
        Matrix {i // f i = b} {i // f i = b} ℝ).PosDef) : C.PosDef := by
  classical
  have hHerm : C.IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j; exact hSym j i
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hHerm
  intro x hx
  simp only [star_trivial]
  have hrow (b : κ) (i : {i // f i = b}) :
      (C *ᵥ x) i = ((C.submatrix Subtype.val Subtype.val :
        Matrix {i // f i = b} {i // f i = b} ℝ) *ᵥ
        (fun j : {i // f i = b} => x j)) i := by
    rw [harmonic_row_split C {i | f i = b} x i]
    have hz : (∑ j : ↥({i | f i = b}ᶜ), C i j * x j) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [hblock i j (fun e => j.property (e.symm.trans i.property)), zero_mul]
    rw [hz, add_zero]
    rfl
  let Q (b : κ) : ℝ :=
    (fun i : {i // f i = b} => x i) ⬝ᵥ
      ((C.submatrix Subtype.val Subtype.val :
        Matrix {i // f i = b} {i // f i = b} ℝ) *ᵥ
        (fun j : {i // f i = b} => x j))
  have hsum : x ⬝ᵥ (C *ᵥ x) = ∑ b, Q b := by
    change (∑ i, x i * (C *ᵥ x) i) = _
    rw [← Fintype.sum_fiberwise f (fun i => x i * (C *ᵥ x) i)]
    apply Finset.sum_congr rfl
    intro b _
    simp only [Q, dotProduct, hrow b]
  have hnonneg (b : κ) : 0 ≤ Q b := by
    simpa only [star_trivial] using
      (hdef b).posSemidef.dotProduct_mulVec_nonneg (fun i : {i // f i = b} => x i)
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hn
    apply hx
    funext i
    exact not_ne_iff.mp (fun hi => hn ⟨i, hi⟩)
  have hstrict : 0 < Q (f i) := by
    apply (hdef (f i)).dotProduct_mulVec_pos
    intro hz
    exact hi (congrFun hz ⟨i, rfl⟩)
  rw [hsum]
  exact Finset.sum_pos' (fun b _ => hnonneg b)
    ⟨f i, Finset.mem_univ _, hstrict⟩

theorem matrix_posDef_of_connected {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hSym : ∀ i j, C i j = C j i)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0) (hDiag : ∀ i, 0 ≤ C i i)
    (hComp : ∀ G : Set ι,
      (∀ i j : G, Relation.ReflTransGen (fun a b : G => C a b < 0) i j) →
      (C.submatrix Subtype.val Subtype.val : Matrix G G ℝ).PosDef) : C.PosDef := by
  classical
  let graph : SimpleGraph ι := {
    Adj := fun i j => C i j < 0
    symm := ⟨fun {i j} h => (hSym i j) ▸ h⟩
    loopless := ⟨fun i => not_lt_of_ge (hDiag i)⟩ }
  let : Fintype graph.ConnectedComponent := Fintype.ofFinite _
  apply matrix_posDef_of_fibers C hSym graph.connectedComponentMk
  · intro i j hij
    have hne : i ≠ j := fun e => hij (congrArg graph.connectedComponentMk e)
    apply le_antisymm (hOff i j hne)
    apply le_of_not_gt
    intro hneg
    exact hij (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj (G := graph) hneg)
  · intro b
    apply hComp b.supp
    intro i j
    exact (SimpleGraph.reachable_iff_reflTransGen i j).mp
      (b.connected_toSimpleGraph.preconnected i j)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PrismPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped BigOperators unitInterval
open Simplicial

attribute [local instance] Classical.decEq Classical.propDecidable

def prismPrefix {n:ℕ} (z:Convexity.StdSimplex ℝ (Fin (n+1))) (k:Fin (n+1)) : ℝ :=
  ∑i∈Finset.Iio k,z.weights i

def PrismCell {n:ℕ} (k:Fin (n+1)) : Set (Convexity.StdSimplex ℝ (Fin (n+1)) × I) :=
  {p | prismPrefix p.1 k ≤ p.2.val ∧ p.2.val ≤ prismPrefix p.1 k + p.1.weights k}

lemma prismPrefix_add {n:ℕ} (z:Convexity.StdSimplex ℝ (Fin (n+1))) (k:Fin (n+1)) :
    prismPrefix z k+z.weights k=∑i∈Finset.Iic k,z.weights i := by
  rw [Finset.Iic_eq_cons_Iio]
  simp only [Finset.sum_cons,prismPrefix,add_comm]

lemma prismPrefix_zero {n:ℕ} (z:Convexity.StdSimplex ℝ (Fin (n+1))) : prismPrefix z 0=0 := by
  unfold prismPrefix
  apply Finset.sum_eq_zero
  intro i hi
  exact ((not_lt_of_ge (Fin.zero_le i)) (Finset.mem_Iio.mp hi)).elim

noncomputable def prismLeft {n:ℕ} (k:Fin (n+1)) (p:Convexity.StdSimplex ℝ (Fin (n+1)) × I) : ℝ :=
  min (p.1.weights k) (max 0 (p.2.val-prismPrefix p.1 k))

lemma prismLeft_nonneg {n:ℕ} (k:Fin (n+1)) (p:Convexity.StdSimplex ℝ (Fin (n+1)) × I) : 0≤ prismLeft k p :=
  le_min (p.1.weights_nonneg k) (le_max_left _ _)
lemma prismLeft_le {n:ℕ} (k:Fin (n+1)) (p:Convexity.StdSimplex ℝ (Fin (n+1)) × I) : prismLeft k p≤ p.1.weights k :=
  min_le_left _ _
lemma prismLeft_cell {n:ℕ} (k:Fin (n+1)) (p:Convexity.StdSimplex ℝ (Fin (n+1)) × I) (hp:p∈PrismCell k) :
    prismLeft k p=p.2.val-prismPrefix p.1 k := by
  rw [prismLeft,max_eq_right (sub_nonneg.mpr hp.1),min_eq_right (by linarith [hp.2])]

noncomputable def prismWeights {n:ℕ} (k:Fin (n+1)) (p:Convexity.StdSimplex ℝ (Fin (n+1)) × I) :
    Fin (n+2)→ℝ :=
  k.castSucc.insertNth (prismLeft k p) (Function.update p.1.weights k (p.1.weights k-prismLeft k p))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PrismFlag
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped BigOperators unitInterval
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable

lemma linearMap_insertNth {n:ℕ} {Y:Type*} [Fintype Y]
    (φ:Fin (n+1)→Y) (k:Fin (n+1)) (a:ℝ) (v:Fin n→ℝ) :
    FunOnFinite.linearMap ℝ ℝ φ (k.insertNth a v)=
      Pi.single (φ k) a+FunOnFinite.linearMap ℝ ℝ (φ∘k.succAbove) v := by
  ext y
  simp only [FunOnFinite.linearMap_apply_apply,Pi.add_apply,Pi.single_apply,
    Finset.sum_filter]
  rw [Fin.sum_univ_succAbove _ k]
  simp only [Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove,Function.comp_apply]
  simp only [eq_comm (a:=y) (b:=φ k)]

lemma collapse_insertNth {n:ℕ} (k:Fin (n+1)) (a:ℝ) (v:Fin (n+1)→ℝ) :
    FunOnFinite.linearMap ℝ ℝ k.predAbove (k.castSucc.insertNth a v)=Pi.single k a+v := by
  rw [linearMap_insertNth,Fin.predAbove_castSucc_self]
  have he:k.predAbove∘k.castSucc.succAbove=id:=funext (Fin.predAbove_succAbove k)
  rw [he,FunOnFinite.linearMap_id,LinearMap.id_apply]
  ext i
  simp only [Pi.add_apply,Pi.single_apply]
  by_cases hi:i=k <;> simp only [hi,ite_true, if_true,ite_false, if_false]

lemma succAbove_le_castSucc_iff {n:ℕ} (k i:Fin (n+1)) :
    k.castSucc.succAbove i≤k.castSucc ↔ i<k := by
  by_cases hi:i<k
  · rw [Fin.succAbove_castSucc_of_lt _ _ hi]
    simp only [Fin.castSucc_le_castSucc_iff,hi,iff_true]; exact hi.le
  · rw [Fin.succAbove_castSucc_of_le _ _ (not_lt.mp hi)]
    simp only [Fin.le_iff_val_le_val,Fin.val_succ,Fin.val_castSucc,
      Fin.lt_def] at hi ⊢
    omega

def prismFlag {n:ℕ} (k:Fin (n+1)) (i:Fin (n+2)) : Fin 2 :=
  if i≤k.castSucc then 0 else 1

lemma flag_insertNth {n:ℕ} (k:Fin (n+1)) (a:ℝ) (v:Fin (n+1)→ℝ) :
    FunOnFinite.linearMap ℝ ℝ (prismFlag k) (k.castSucc.insertNth a v) 0=
      a+∑i∈Finset.Iio k,v i := by
  rw [linearMap_insertNth]
  simp only [Pi.add_apply,prismFlag,le_refl,ite_true, if_true,Pi.single_eq_same,
    FunOnFinite.linearMap_apply_apply,Finset.sum_filter,Function.comp_apply,
    succAbove_le_castSucc_iff]
  congr 1
  rw [←Finset.sum_filter]
  apply Finset.sum_congr
  · ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iio]
    by_cases hi:i<k <;> simp [hi]
  · intro _ _; rfl

lemma simplex_map_weights {Source Target : Type*} [Finite Source] [Finite Target]
    (function : Source → Target) (simplex : Convexity.StdSimplex ℝ Source) :
    ⇑(Convexity.StdSimplex.map function simplex).weights =
      FunOnFinite.linearMap ℝ ℝ function simplex.weights := by
  change ⇑(Finsupp.mapDomain function simplex.weights) =
    Finsupp.equivFunOnFinite (Finsupp.mapDomain function
      (Finsupp.equivFunOnFinite.symm (Finsupp.equivFunOnFinite simplex.weights)))
  rw [Equiv.symm_apply_apply]
  rfl

lemma simplex_insertNth_decomp {n:ℕ} (k:Fin (n+1))
    (w:Convexity.StdSimplex ℝ (Fin (n+2))) :
    k.castSucc.insertNth (w.weights k.castSucc)
      (fun i=>w.weights (k.castSucc.succAbove i))=w.weights := by
  funext i
  obtain rfl|⟨j,rfl⟩:=Fin.eq_self_or_eq_succAbove k.castSucc i
  · exact Fin.insertNth_apply_same _ _ _
  · exact Fin.insertNth_apply_succAbove _ _ _ _

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PrismGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CategoryTheory Opposite Simplicial

attribute [local instance] Classical.decEq Classical.propDecidable

def prismGrid {n:ℕ} (k:Fin (n+1)) : Fin (n+2) →o Fin (n+1) × Fin 2 where
  toFun i:=(k.predAbove i,if i≤ k.castSucc then 0 else 1)
  monotone' :=by
    intro i j hij
    refine ⟨k.predAbove_right_monotone hij,?_⟩
    by_cases hi:i≤ k.castSucc <;> by_cases hj:j≤ k.castSucc
    · simp only [hi,hj,ite_true, if_true]; exact le_rfl
    · simpa only [hi,hj,ite_true, if_true,ite_false, if_false] using (show (0:Fin 2)≤1 by decide)
    · exact (hi (hij.trans hj)).elim
    · simp only [hi,hj,ite_false, if_false]; exact le_rfl

lemma prismGrid_apply {n:ℕ} (k:Fin (n+1)) (i:Fin (n+2)) :
    prismGrid k i = (k.predAbove i,if i≤k.castSucc then (0:Fin 2) else 1) := rfl

def orderCylinder {P Q:Type*} [Preorder P] [Preorder Q]
    (f g:P→o Q) (h:∀p,f p≤ g p) : P × Fin 2 →o Q where
  toFun p:=if p.2=0 then f p.1 else g p.1
  monotone' :=by
    intro p q hpq
    by_cases hp:p.2=0 <;> by_cases hq:q.2=0
    · simp only [hp,hq,ite_true, if_true]; exact f.monotone hpq.1
    · simp only [hp,hq,ite_true, if_true,ite_false, if_false]; exact (h p.1).trans (g.monotone hpq.1)
    · have hh:p.2≤0:=hq ▸ hpq.2
      exact (hp (le_antisymm hh (Fin.zero_le _))).elim
    · simp only [hp,hq,ite_false, if_false]; exact g.monotone hpq.1

noncomputable def nervePrism {P Q:Type*} [Preorder P] [Preorder Q]
    (f g:P→o Q) (h:∀p,f p≤ g p) {n:SimplexCategory}
    (x:(nerve P).obj (op n)) (k:Fin (n.len+1)) : (nerve Q).obj (op ⦋n.len+1⦌) :=
  ((orderCylinder f g h).comp ((x.toOrderHom.prodMap (OrderHom.id)).comp (prismGrid k))).toFunctor

def prismOrdinal {n m:SimplexCategory} (u:n⟶m) (k:Fin (n.len+1)) : ⦋n.len+1⦌⟶⦋m.len+1⦌ :=
  SimplexCategory.mkHom {
    toFun i:=if i≤ k.castSucc then (u.toOrderHom (k.predAbove i)).castSucc
      else (u.toOrderHom (k.predAbove i)).succ
    monotone':=by
      intro i j hij
      have hh:=u.toOrderHom.monotone (k.predAbove_right_monotone hij)
      by_cases hi:i≤ k.castSucc <;> by_cases hj:j≤ k.castSucc
      · simp only [hi,hj,ite_true, if_true]; exact Fin.castSucc_le_castSucc_iff.mpr hh
      · simp only [hi,hj,ite_true, if_true,ite_false, if_false]
        exact le_trans (Fin.castSucc_le_castSucc_iff.mpr hh) (by simp only [Fin.le_iff_val_le_val,Fin.val_castSucc,Fin.val_succ]; omega)
      · exact (hi (hij.trans hj)).elim
      · simp only [hi,hj,ite_false, if_false]; exact Fin.succ_le_succ_iff.mpr hh }

lemma prismGrid_natural {n m:SimplexCategory} (u:n⟶m) (k:Fin (n.len+1)) (i:Fin (n.len+2)) :
    prismGrid (u.toOrderHom k) ((prismOrdinal u k).toOrderHom i)=
      (u.toOrderHom ((prismGrid k i).1),(prismGrid k i).2) := by
  by_cases hi:i≤ k.castSucc
  · have hk:k.predAbove i≤ k:=by
      have hh:=k.predAbove_right_monotone hi
      simpa only [Fin.predAbove_castSucc_self] using hh
    have hu:=u.toOrderHom.monotone hk
    change ((u.toOrderHom k).predAbove (if i≤k.castSucc then
        (u.toOrderHom (k.predAbove i)).castSucc else (u.toOrderHom (k.predAbove i)).succ),
      if (if i≤k.castSucc then (u.toOrderHom (k.predAbove i)).castSucc
        else (u.toOrderHom (k.predAbove i)).succ)≤(u.toOrderHom k).castSucc then (0:Fin 2) else 1)=
      (u.toOrderHom (k.predAbove i),if i≤k.castSucc then (0:Fin 2) else 1)
    simp only [hi,ite_true, if_true,Fin.castSucc_le_castSucc_iff.mpr hu,Fin.predAbove_castSucc_of_le _ _ hu]
  · have hk:k≤ k.predAbove i:=by
      have hh:k.succ≤ i:=by
        simp only [Fin.le_iff_val_le_val,Fin.val_succ]
        have hh:=not_le.mp hi
        simpa only [Fin.lt_def,Fin.val_castSucc,Nat.succ_le_iff] using hh
      have hh:=k.predAbove_right_monotone hh
      simpa only [Fin.predAbove_succ_self] using hh
    have hu:=u.toOrderHom.monotone hk
    have hlu:¬(u.toOrderHom (k.predAbove i)).succ≤(u.toOrderHom k).castSucc:=by
      simp only [Fin.le_iff_val_le_val,Fin.val_succ,Fin.val_castSucc] at hu ⊢
      omega
    change ((u.toOrderHom k).predAbove (if i≤k.castSucc then
        (u.toOrderHom (k.predAbove i)).castSucc else (u.toOrderHom (k.predAbove i)).succ),
      if (if i≤k.castSucc then (u.toOrderHom (k.predAbove i)).castSucc
        else (u.toOrderHom (k.predAbove i)).succ)≤(u.toOrderHom k).castSucc then (0:Fin 2) else 1)=
      (u.toOrderHom (k.predAbove i),if i≤k.castSucc then (0:Fin 2) else 1)
    simp only [hi,ite_false, if_false,hlu,Fin.predAbove_succ_of_le _ _ hu]

lemma nervePrism_natural {P Q:Type*} [Preorder P] [Preorder Q]
    (f g:P→o Q) (h:∀p,f p≤ g p) {n m:SimplexCategory} (u:n⟶m)
    (x:(nerve P).obj (op m)) (k:Fin (n.len+1)) :
    nervePrism f g h ((nerve P).map u.op x) k =
      (nerve Q).map (prismOrdinal u k).op (nervePrism f g h x (u.toOrderHom k)) := by
  apply nerve.ext_of_isThin
  funext i
  have he:=prismGrid_natural u k i
  change orderCylinder f g h ((x.obj ((u.toOrderHom ((prismGrid k i).1)))),(prismGrid k i).2)=
    orderCylinder f g h (x.obj ((prismGrid (u.toOrderHom k) ((prismOrdinal u k).toOrderHom i)).1),
      (prismGrid (u.toOrderHom k) ((prismOrdinal u k).toOrderHom i)).2)
  rw [he]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PredAboveSuccSucc
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped BigOperators unitInterval
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable

lemma predAbove_succ_succAbove {n:ℕ} (k i:Fin (n+1)) :
    k.predAbove (k.succ.succAbove i)=i := by
  by_cases hi:i≤k
  · rw [Fin.succAbove_succ_of_le _ _ hi,Fin.predAbove_castSucc_of_le _ _ hi]
  · rw [Fin.succAbove_succ_of_lt _ _ (not_le.mp hi),Fin.predAbove_succ_of_le _ _ (not_le.mp hi).le]

lemma prismGrid_face_right {n:ℕ} (k i:Fin (n+1)) :
    prismGrid k (k.succ.succAbove i)=(i,if i≤k then (0:Fin 2) else 1) := by
  rw [prismGrid_apply,predAbove_succ_succAbove]
  by_cases hi:i≤k
  · rw [Fin.succAbove_succ_of_le _ _ hi]
    simp only [Fin.castSucc_le_castSucc_iff,hi,ite_true, if_true]
  · rw [Fin.succAbove_succ_of_lt _ _ (not_le.mp hi)]
    have hh:¬i.succ≤k.castSucc:=by
      simp only [Fin.le_iff_val_le_val,Fin.val_succ,Fin.val_castSucc] at hi ⊢
      omega
    simp only [hi,hh,ite_false, if_false]

lemma prismGrid_face_adjacent {n:ℕ} (k l:Fin (n+1)) (hkl:l.val=k.val+1) (i:Fin (n+1)) :
    prismGrid l (k.succ.succAbove i)=prismGrid k (k.succ.succAbove i) := by
  have hd:k.succ=l.castSucc:=Fin.ext hkl.symm
  rw [prismGrid_face_right,hd,prismGrid_apply,Fin.predAbove_succAbove]
  have he:i<l ↔ i≤k:=by
    simp only [Fin.lt_def,Fin.le_iff_val_le_val]
    omega
  simp only [succAbove_le_castSucc_iff,he]

lemma prismPrefix_step {n:ℕ} (z:Convexity.StdSimplex ℝ (Fin (n+1))) (k l:Fin (n+1)) (hkl:l.val=k.val+1) :
    prismPrefix z l=prismPrefix z k+z.weights k := by
  rw [prismPrefix_add]
  apply Finset.sum_congr
  · ext i
    simp only [Finset.mem_Iio,Finset.mem_Iic,Fin.lt_def,Fin.le_iff_val_le_val]
    omega
  · intro _ _; rfl

lemma nervePrism_face_adjacent {P Q:Type*} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) {n:SimplexCategory} (x:(nerve P).obj (op n))
    (k l:Fin (n.len+1)) (hkl:l.val=k.val+1) :
    (nerve Q).map (SimplexCategory.δ k.succ).op (nervePrism f g h x l)=
      (nerve Q).map (SimplexCategory.δ k.succ).op (nervePrism f g h x k) := by
  apply nerve.ext_of_isThin
  funext i
  change orderCylinder f g h (x.obj ((prismGrid l (k.succ.succAbove i)).1),
      (prismGrid l (k.succ.succAbove i)).2)=
    orderCylinder f g h (x.obj ((prismGrid k (k.succ.succAbove i)).1),
      (prismGrid k (k.succ.succAbove i)).2)
  rw [prismGrid_face_adjacent k l hkl]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_NervePrismValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped BigOperators unitInterval
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable

lemma prismPrefix_mono {n:ℕ} (z:Convexity.StdSimplex ℝ (Fin (n+1))) {k l:Fin (n+1)} (hkl:k≤l) :
    prismPrefix z k≤prismPrefix z l :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Iio_subset_Iio hkl) (fun index _ _=>z.weights_nonneg index)

lemma prismRight_mono {n:ℕ} (z:Convexity.StdSimplex ℝ (Fin (n+1))) {k l:Fin (n+1)} (hkl:k≤l) :
    prismPrefix z k+z.weights k≤prismPrefix z l+z.weights l := by
  rw [prismPrefix_add,prismPrefix_add]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Iic_subset_Iic.mpr hkl) (fun index _ _=>z.weights_nonneg index)

lemma prismCell_between {n:ℕ} (p:Convexity.StdSimplex ℝ (Fin (n+1))×I) {k j l:Fin (n+1)}
    (hk:p∈PrismCell k) (hl:p∈PrismCell l) (hkj:k≤j) (hjl:j≤l) : p∈PrismCell j :=
  ⟨(prismPrefix_mono p.1 hjl).trans hl.1,hk.2.trans (prismRight_mono p.1 hkj)⟩

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Harmonic_PrismSimplexZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe u
open scoped BigOperators unitInterval
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable

lemma nervePrism_zero_face {P Q:Type u} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) {n:SimplexCategory} (x:(nerve P).obj (op n)) :
    (nerve Q).map (SimplexCategory.δ (0:Fin (n.len+2))).op (nervePrism f g h x 0)=
      (nerveMap g.toFunctor).app (op n) x := by
  apply nerve.ext_of_isThin
  funext i
  change orderCylinder f g h (x.obj ((0:Fin (n.len+1)).predAbove i.succ),
    if i.succ≤(0:Fin (n.len+1)).castSucc then (0:Fin 2) else 1)=g (x.obj i)
  rw [Fin.predAbove_succ_of_le _ _ (Fin.zero_le _)]
  have hn:¬i.succ≤(0:Fin (n.len+1)).castSucc:=by
    simp only [Fin.le_iff_val_le_val,Fin.val_succ,Fin.val_castSucc,Fin.val_zero]; omega
  simp only [hn,ite_false, if_false]
  change (if (1:Fin 2)=0 then f (x.obj i) else g (x.obj i))=g (x.obj i)
  simp

lemma nervePrism_one_face {P Q:Type u} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) {n:SimplexCategory} (x:(nerve P).obj (op n)) :
    (nerve Q).map (SimplexCategory.δ (Fin.last (n.len+1))).op (nervePrism f g h x (Fin.last n.len))=
      (nerveMap f.toFunctor).app (op n) x := by
  apply nerve.ext_of_isThin
  funext i
  change orderCylinder f g h (x.obj ((Fin.last n.len).predAbove ((Fin.last (n.len+1)).succAbove i)),
    if (Fin.last (n.len+1)).succAbove i≤(Fin.last n.len).castSucc then (0:Fin 2) else 1)=f (x.obj i)
  rw [Fin.succAbove_last]
  rw [Fin.predAbove_castSucc_of_le _ _ (Fin.le_last _)]
  simp only [Fin.castSucc_le_castSucc_iff,Fin.le_last,ite_true, if_true]
  change (if (0:Fin 2)=0 then f (x.obj i) else g (x.obj i))=f (x.obj i)
  simp

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ActiveColors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Active colors for a relative frame

Section 6.3 of paper 082-03 requires an active-color argument without
universal adjacency of the frame. Null signs are allowed at every recorded
level, including the cutoff. All assertions here are proved from the
Cartan matrix and the finite profile.
-/

namespace HarmonicArtin.ParabolicIntersections

open _root_.Matrix

variable {ι : Type*} [Fintype ι]

/-- A closed positive null component, isolated from all higher levels. -/
def relativePositiveSign (C : Matrix ι ι ℝ) (U : Set ι)
    (p : ℕ →₀ (ι → ℝ)) (k : ℕ) (i : ι) : Prop :=
  ∃ I : Set ι, i ∈ I ∧ I ⊆ U ∧ PositiveSupportComponent C (p k) I ∧
    (∀ j ∈ I, (C *ᵥ p k) j = 0) ∧
    ∀ d, k < d → ∀ j, (j ∈ I ∨ ∃ a ∈ I, C a j < 0) → p d j = 0

/-- Active colors at their last recorded incidence. -/
def relativeActive (C : Matrix ι ι ℝ) (U : Set ι)
    (p : ℕ →₀ (ι → ℝ)) (i : ι) : Prop :=
  let k := incidenceLevel C p i
  0 < (C *ᵥ p k) i ∨
    (C *ᵥ p k) i = 0 ∧ 0 < p k i ∧ ¬relativePositiveSign C U p k i

/-- Every connected component formed from a positive definite closed
part and active colors remains positive definite. -/
theorem relative_active_component_posDef
    (C : Matrix ι ι ℝ) (hSym : ∀ i j, C i j = C j i)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0) (U : Set ι)
    (p : ℕ →₀ (ι → ℝ)) (hp : ∀ k i, 0 ≤ p k i)
    (T : Set ι) (hT : (C.submatrix Subtype.val Subtype.val : Matrix T T ℝ).PosDef)
    (hHarm : ∀ k, ∀ i ∈ T, (C *ᵥ p k) i = 0)
    (G : Set ι) (hU : G ⊆ U)
    (hG : ∀ i ∈ G, i ∈ T ∨ relativeActive C U p i)
    (hConn : ∀ i j : G, Relation.ReflTransGen (fun a b : G => C a b < 0) i j) :
    (C.submatrix Subtype.val Subtype.val : Matrix G G ℝ).PosDef := by
  classical
  by_cases hGT : G ⊆ T
  · exact hT.submatrix (e := fun i : G => (⟨i, hGT i.property⟩ : T))
      (fun a b h => Subtype.ext (congrArg (fun z : T => (z : ι)) h))
  have hGne : G.Nonempty := by
    by_contra hn
    exact hGT (fun i hi => (hn ⟨i, hi⟩).elim)
  let : Nonempty G := ⟨⟨hGne.choose, hGne.choose_spec⟩⟩
  let k := (Finset.univ : Finset G).sup (fun i => incidenceLevel C p i)
  have hmax (i : G) : incidenceLevel C p i ≤ k :=
    Finset.le_sup (f := fun j : G => incidenceLevel C p j) (Finset.mem_univ i)
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset G)
    Finset.univ_nonempty (fun i => incidenceLevel C p i)
  have hsome : ∃ i : G, ∃ q, levelIncident C p q i := by
    obtain ⟨i, hi, hiT⟩ := Set.not_subset.mp hGT
    have hact := (hG i hi).resolve_left hiT
    refine ⟨⟨i, hi⟩, incidenceLevel C p i, ?_⟩
    by_contra hn
    have hz := no_incidence_row_zero C hOff p hp hn
    rcases hact with hpos | ⟨_, hpos, _⟩
    · exact (ne_of_gt hpos) hz
    · exact hn (Or.inl hpos)
  have haInc : ∃ i : G, levelIncident C p k i := by
    obtain ⟨i, q, hq⟩ := hsome
    by_cases hk : k = 0
    · have hi : incidenceLevel C p i = 0 := Nat.eq_zero_of_le_zero (hk ▸ hmax i)
      refine ⟨i, ?_⟩
      rw [hk, ← hi]
      exact incidenceLevel_incident C p i ⟨q, hq⟩
    · refine ⟨a, ?_⟩
      rw [show k = incidenceLevel C p a from ha]
      apply incidenceLevel_incident C p a
      by_contra hn
      have hempty : incidenceIndices C p a = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro l hl
        exact hn ⟨l, (Finset.mem_filter.mp hl).2⟩
      have hz : incidenceLevel C p a = 0 := by
        simp only [incidenceLevel, hempty, Finset.sup_empty, bot_eq_zero]
      exact hk (ha.trans hz)
  have hrows (i : G) : 0 ≤ (C *ᵥ p k) i := by
    rcases hG i i.property with hiT | hiAct
    · rw [hHarm k i hiT]
    · by_cases hik : incidenceLevel C p i = k
      · change 0 < (C *ᵥ p (incidenceLevel C p i)) i ∨
          (C *ᵥ p (incidenceLevel C p i)) i = 0 ∧ _ at hiAct
        rw [hik] at hiAct
        rcases hiAct with hpos | ⟨hz, _⟩
        · exact le_of_lt hpos
        · exact le_of_eq hz.symm
      · have hn : ¬levelIncident C p k i := by
          intro h
          exact hik (le_antisymm (hmax i) (levelIncident_le C p h))
        rw [no_incidence_row_zero C hOff p hp hn]
  have hInc : ∃ j, 0 < p k j ∧ (j ∈ G ∨ ∃ i : G, C i j < 0) := by
    obtain ⟨a, hinc⟩ := haInc
    rcases hinc with h | ⟨j, haj, hj⟩
    · exact ⟨a, h, Or.inl a.property⟩
    · exact ⟨j, hj, Or.inr ⟨a, haj⟩⟩
  rcases harmonic_support_alternative C hSym hOff G hConn (p k) (hp k)
    hrows hInc with hdef | ⟨hpos, hzero, hboundary⟩
  · exact hdef
  have hcomponent : PositiveSupportComponent C (p k) G := by
    refine ⟨hGne, fun i hi => hpos ⟨i, hi⟩, hConn, ?_⟩
    intro i hi j hij hj
    by_contra hjG
    exact (ne_of_gt hj) (hboundary ⟨i, hi⟩ j hjG hij)
  have hhigher : ∀ d, k < d → ∀ j,
      (j ∈ G ∨ ∃ a ∈ G, C a j < 0) → p d j = 0 := by
    intro d hd j hj
    apply le_antisymm _ (hp d j)
    apply le_of_not_gt
    intro hjpos
    have hdk : d ≤ k := by
      rcases hj with hjG | ⟨i, hi, hij⟩
      · exact (levelIncident_le C p (Or.inl hjpos)).trans (hmax ⟨j, hjG⟩)
      · exact (levelIncident_le C p (Or.inr ⟨j, hij, hjpos⟩)).trans (hmax ⟨i, hi⟩)
    exact (not_le_of_gt hd) hdk
  have hsign (i : G) : relativePositiveSign C U p k i :=
    ⟨G, i.property, (fun _ hj => hU hj), hcomponent, fun j hj => hzero ⟨j, hj⟩, hhigher⟩
  exfalso
  apply hGT
  intro i hi
  rcases hG i hi with hiT | hiAct
  · exact hiT
  · have hik : incidenceLevel C p i = k := le_antisymm (hmax ⟨i, hi⟩)
      (levelIncident_le C p (Or.inl (hpos ⟨i, hi⟩)))
    change 0 < (C *ᵥ p (incidenceLevel C p i)) i ∨
      (C *ᵥ p (incidenceLevel C p i)) i = 0 ∧ _ at hiAct
    rw [hik, hzero ⟨i, hi⟩] at hiAct
    rcases hiAct with himposs | ⟨_, _, hnot⟩
    · exact (lt_irrefl 0 himposs).elim
    · exact (hnot (hsign ⟨i, hi⟩)).elim

theorem relative_active_posDef {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hSym : ∀ i j, C i j = C j i)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0) (hDiag : ∀ i, 0 ≤ C i i) (U : Set ι)
    (p : ℕ →₀ (ι → ℝ)) (hp : ∀ k i, 0 ≤ p k i)
    (T : Set ι) (hT : (C.submatrix Subtype.val Subtype.val : Matrix T T ℝ).PosDef)
    (hHarm : ∀ k, ∀ i ∈ T, (C *ᵥ p k) i = 0)
    (K : Set ι) (hKU : K ⊆ U)
    (hK : ∀ i ∈ K, i ∈ T ∨ relativeActive C U p i) :
    (C.submatrix Subtype.val Subtype.val : Matrix K K ℝ).PosDef := by
  classical
  apply matrix_posDef_of_connected
    (C.submatrix Subtype.val Subtype.val : Matrix K K ℝ)
    (fun i j => hSym i j)
    (fun i j hij => hOff i j (fun e => hij (Subtype.ext e))) (fun i => hDiag i)
  intro H hH
  let G : Set ι := {i | ∃ hi : i ∈ K, (⟨i, hi⟩ : K) ∈ H}
  let e : H ≃ G := Equiv.subtypeSubtypeEquivSubtypeExists (· ∈ K) (· ∈ H)
  have hG : ∀ i ∈ G, i ∈ T ∨ relativeActive C U p i := by
    intro i hi
    obtain ⟨hiK, _⟩ := hi
    exact hK i hiK
  have hGU : G ⊆ U := by
    rintro i ⟨hiK, _⟩
    exact hKU hiK
  have hConn : ∀ i j : G, Relation.ReflTransGen (fun a b : G => C a b < 0) i j := by
    intro i j
    have hh := Relation.ReflTransGen.lift
      (r := fun a b : H => C a.val.val b.val.val < 0)
      (p := fun a b : G => C a b < 0) e
      (fun a b hab => show C (e a) (e b) < 0 from hab)
      (e.symm i) (e.symm j) (hH (e.symm i) (e.symm j))
    change Relation.ReflTransGen (fun a b : G => C a b < 0) (e (e.symm i)) (e (e.symm j)) at hh
    simpa only [e.apply_symm_apply] using hh
  have hg := relative_active_component_posDef C hSym hOff U p hp T hT
    hHarm G hGU hG hConn
  exact hg.submatrix e.injective

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Parabolic subgroups for result 082-03

We use the Artin presentation and standard parabolics already used by
`Topology.ArtinGroups`. In Mathlib's Coxeter matrix convention, a zero
off-diagonal entry means an infinite label.
-/

namespace HarmonicArtin.ParabolicIntersections

variable {G : Type*} [Group G]

@[simp] theorem mem_conjugate (g : G) (P : Subgroup G) (a : G) :
    a ∈ conjugate g P ↔ g⁻¹ * a * g ∈ P := by
  simp [conjugate]

@[simp] theorem conjugate_one (P : Subgroup G) : conjugate 1 P = P := by
  ext a
  simp

@[simp] theorem conjugate_top (g : G) : conjugate g (⊤ : Subgroup G) = ⊤ := by
  ext a
  simp

@[simp] theorem conjugate_bot (g : G) : conjugate g (⊥ : Subgroup G) = ⊥ := by
  ext a
  simp only [mem_conjugate, Subgroup.mem_bot]
  constructor
  · intro h
    calc
      a = g * (g⁻¹ * a * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; simp
  · rintro rfl
    simp

theorem conjugate_mul (g h : G) (P : Subgroup G) :
    conjugate (g * h) P = conjugate g (conjugate h P) := by
  ext a
  simp only [mem_conjugate, mul_inv_rev]
  group

@[simp] theorem conjugate_inv_cancel (g : G) (P : Subgroup G) :
    conjugate g⁻¹ (conjugate g P) = P := by
  rw [← conjugate_mul, inv_mul_cancel, conjugate_one]

theorem conjugate_mono (g : G) {P Q : Subgroup G} (h : P ≤ Q) :
    conjugate g P ≤ conjugate g Q := fun _ ha => h ha

@[simp] theorem conjugate_le_conjugate_iff (g : G) (P Q : Subgroup G) :
    conjugate g P ≤ conjugate g Q ↔ P ≤ Q := by
  constructor
  · intro h
    simpa using conjugate_mono g⁻¹ h
  · exact conjugate_mono g

/-- Conjugation as an order isomorphism of the subgroup lattice. -/
def conjugateOrderIso (g : G) : Subgroup G ≃o Subgroup G where
  toFun := conjugate g
  invFun := conjugate g⁻¹
  left_inv := conjugate_inv_cancel g
  right_inv P := by simpa using conjugate_inv_cancel g⁻¹ P
  map_rel_iff' := fun {P Q} => conjugate_le_conjugate_iff g P Q

variable {S : Type*} (M : CoxeterMatrix S)

theorem standard_mono {X Y : Set S} (h : X ⊆ Y) :
    artinParabolic M X ≤ artinParabolic M Y :=
  Subgroup.closure_mono (Set.image_mono h)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_AmalgamGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coset graph of a two-factor amalgam, with its genuine group action. -/
namespace HarmonicArtin.ParabolicIntersections.AmalgamTree
open Monoid
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G : Bool → Type} [∀ b, Group (G b)] {H : Type} [Group H]
variable (φ : ∀ b, H →* G b)

abbrev Amalgam := Monoid.PushoutI φ
abbrev Factor (b : Bool) : Subgroup (Amalgam φ) := (PushoutI.of b).range
abbrev Vertex := Σ b : Bool, Amalgam φ ⧸ Factor φ b

def vertex (b : Bool) (g : Amalgam φ) : Vertex φ := ⟨b,QuotientGroup.mk g⟩

def graph : SimpleGraph (Vertex φ) where
  Adj u v := u.1≠v.1 ∧ ∃ g : Amalgam φ,
    u.2=(QuotientGroup.mk g : Amalgam φ ⧸ Factor φ u.1) ∧
    v.2=(QuotientGroup.mk g : Amalgam φ ⧸ Factor φ v.1)
  symm := ⟨by rintro u v ⟨hn,g,hu,hv⟩; exact ⟨hn.symm,g,hv,hu⟩⟩
  loopless := ⟨by rintro v ⟨h,_⟩; exact h rfl⟩

instance instMulActionAmalgamVertex : MulAction (Amalgam φ) (Vertex φ) where
  smul g v := ⟨v.1,g • v.2⟩
  one_smul := by
    rintro ⟨b,v⟩
    change (⟨b,(1 : Amalgam φ) • v⟩ : Vertex φ)=⟨b,v⟩
    rw [one_smul]
  mul_smul := by
    rintro a b ⟨i,v⟩
    change (⟨i,(a*b) • v⟩ : Vertex φ)=⟨i,a • (b • v)⟩
    rw [mul_smul]

@[simp] lemma smul_vertex (g h : Amalgam φ) (b : Bool) :
    g • vertex φ b h=vertex φ b (g*h) := rfl

def translate (g : Amalgam φ) : graph φ →g graph φ where
  toFun := (g • ·)
  map_rel' := by
    rintro ⟨i,u⟩ ⟨j,v⟩ ⟨hn,h,hu,hv⟩
    refine ⟨hn,g*h,?_,?_⟩
    · change g • u=(QuotientGroup.mk (g*h) : Amalgam φ ⧸ Factor φ i)
      exact congrArg (fun x : Amalgam φ ⧸ Factor φ i => g • x) hu
    · change g • v=(QuotientGroup.mk (g*h) : Amalgam φ ⧸ Factor φ j)
      exact congrArg (fun x : Amalgam φ ⧸ Factor φ j => g • x) hv

end HarmonicArtin.ParabolicIntersections.AmalgamTree

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_DynamicsDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Acylindrical actions and visual splittings

The definitions below spell out the metric content of acylindrical
hyperbolicity. Non-elementarity means that an orbit has three distinct
Gromov-boundary limit points, represented by Gromov sequences whose
pairwise mixed products are bounded. No dynamical assertion is built
into a definition of an Artin group.
-/
namespace HarmonicArtin.ParabolicIntersections

variable {S : Type} (M : CoxeterMatrix S)

/-- The presentation-graph condition in CMMW Definition 2.4. The vertex
subgraphs are proper, cover every vertex, and omit no finite-label edge. -/
def IsVisualSplit (Y Z : Set S) : Prop :=
  Y ∪ Z = Set.univ ∧ Y ⊂ Set.univ ∧ Z ⊂ Set.univ ∧
    ∀ s ∈ Y \ Z, ∀ t ∈ Z \ Y, M s t = 0

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_Consequences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Consequences of the inside-parabolic intersection theorem

These are the deductions in the introduction of paper 082-03. The premise
`InsideIntersectionProperty` is a **new result of that paper**, not a
published input and not an established instance. These deductions alone
do not constitute a formalization of its main intersection theorem.
-/

namespace HarmonicArtin.ParabolicIntersections

variable {S : Type*} (M : CoxeterMatrix S)

/-- The inside-parabolic conclusion of §8. Its proof, for arbitrary
Artin matrices, must come from the relative stabilizer argument. -/
def InsideIntersectionProperty : Prop :=
  ∀ (X Y : Set S) (g : Artin M), ∃ (Z : Set S) (c : Artin M),
    Z ⊆ Y ∧ c ∈ artinParabolic M Y ∧
      artinParabolic M Y ⊓ conjugate g (artinParabolic M X) =
        conjugate c (artinParabolic M Z)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_StabilizerDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The rank induction in §8 of paper 082-03

The finite-rank induction is proved here for an actual group action.
`ReductionAt` records the three alternatives that the paper obtains from
its new relative-height arguments. It is deliberately not called a
published input: constructing these alternatives for the categorical
action is still required before this module implies the main theorem.
-/

namespace HarmonicArtin.ParabolicIntersections

variable {S : Type*} (M : CoxeterMatrix S)
variable {V : Type*} [MulAction (Artin M) V] (v : V)

/-- Stabilizer of the transported family, restricted to a standard subgroup.
For a family of homotopy classes, take `V` to be the product of the classes. -/
def relativeStabilizer (Y : Set S) (x : Artin M) : Subgroup (Artin M) :=
  artinParabolic M Y ⊓ MulAction.stabilizer (Artin M) (x • v)

@[simp] theorem mem_relativeStabilizer (Y : Set S) (x a : Artin M) :
    a ∈ relativeStabilizer M v Y x ↔
      a ∈ artinParabolic M Y ∧ a • (x • v) = x • v := Iff.rfl

/-- The alternatives furnished by the spherical positive-height reduction
and the nonspherical harmonic-minimum reduction. The split case expresses
the invisible direct factor, including its normalization property. -/
inductive ReductionAt (Y : Set S) (x : Artin M) : Prop
  | fixed : relativeStabilizer M v Y x = artinParabolic M Y → ReductionAt Y x
  | smaller (D : Set S) (b : Artin M) :
      D ⊂ Y → b ∈ artinParabolic M Y →
      relativeStabilizer M v Y x ≤ conjugate b⁻¹ (artinParabolic M D) → ReductionAt Y x
  | split (T K : Set S) :
      T ⊂ Y → K ⊆ Y →
      (∀ c ∈ artinParabolic M T, conjugate c (artinParabolic M K) = artinParabolic M K) →
      relativeStabilizer M v Y x = artinParabolic M K ⊔ relativeStabilizer M v T x →
      ReductionAt Y x

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The relative harmonic height

The finite-support, highest-level-first height of §6.2 of paper 082-03.
The last coordinate is the full closed-type sign mask. The cutoff is an
arbitrary integer; null signs can occur at the cutoff itself.
-/

namespace HarmonicArtin.ParabolicIntersections

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
  (U : Set (S ⊕ Unit)) (cutoff : ℤ)

noncomputable def relativeSign (p : ℕ →₀ (S ⊕ Unit → ℝ)) (k : ℕ) (i : S ⊕ Unit) : ℤ :=
  if p k i = 0 then 0 else if relativePositiveSign (framedCartan M) U p k i then 1 else -1

abbrev RelativeBlock (S : Type) :=
  Lex (ℝ × Lex (Lex (Lex (S ⊕ Unit) → ℝ) × Lex (Lex (S ⊕ Unit) → ℤ)))

def relativeZeroBlock : RelativeBlock S := toLex (0, toLex (toLex 0, toLex 0))

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ConnectedMinima
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Lowering paths across tied heights

This is the finite-path argument of §6.5 of paper 082-03. The local
hypotheses are precisely the connected descending neighborhoods and the
compatibility across tied adjacent vertices. They are not installed as
published assumptions; their verification for the relative harmonic
height is a separate part of that paper's proof.
-/

namespace HarmonicArtin.ParabolicIntersections

section Paths

variable {V H : Type*} [LinearOrder H]
variable (adj : V → V → Prop) (height : V → H)

/-- Paths all of whose edges and vertices lie in a specified region.
For the reflexive path the endpoint condition is supplied separately. -/
def PathWithin (p : V → Prop) (a b : V) : Prop :=
  Relation.ReflTransGen (fun x y => p x ∧ p y ∧ adj x y) a b

/-- Descending neighbors at one vertex lie in one strict-sublevel
component; a tied edge carries that component to the other vertex. -/
structure LocalDescent : Prop where
  symmetric : ∀ {a b}, adj a b → adj b a
  descending : ∀ v a b, adj v a → height a < height v →
    adj v b → height b < height v →
    PathWithin adj (fun z => height z < height v) a b
  tied : ∀ v w, adj v w → height v = height w →
    ∀ a, adj v a → height a < height v →
    ∃ b, adj w b ∧ height b < height w ∧
      PathWithin adj (fun z => height z < height v) a b

end Paths

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_NerveOrderMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe u
open scoped unitInterval
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable

noncomputable def nerveOrderMap {P Q:Type u} [Preorder P] [Preorder Q] (f:P→oQ) :
    C(|nerve P|,|nerve Q|) := (SSet.toTop.map (nerveMap f.toFunctor)).hom

noncomputable def nervePathEvaluate (Q:Type u) [Preorder Q] (t:I) :
    TopCat.of C(I,|nerve Q|)⟶|nerve Q| :=
  TopCat.ofHom ⟨fun f=>f t,continuous_eval_const t⟩

lemma nerveOrderMap_id (P:Type u) [Preorder P] :
    nerveOrderMap (OrderHom.id (α:=P))=ContinuousMap.id |nerve P| := by
  have he:nerveMap (OrderHom.id (α:=P)).toFunctor=𝟙 (nerve P):=by
    ext n x
    rfl
  change (SSet.toTop.map _).hom=_
  rw [he,CategoryTheory.Functor.map_id]
  rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_NerveOrderRetractionEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe u
open Simplicial CategoryTheory Opposite

lemma nerveOrderMap_comp {P Q R:Type u} [Preorder P] [Preorder Q] [Preorder R]
    (f:P→oQ) (g:Q→oR) : nerveOrderMap (g.comp f)=(nerveOrderMap g).comp (nerveOrderMap f) := by
  have he:nerveMap (g.comp f).toFunctor=nerveMap f.toFunctor≫nerveMap g.toFunctor:=by
    ext n x
    rfl
  change (SSet.toTop.map _).hom=_
  rw [he,CategoryTheory.Functor.map_comp]
  rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_WeightDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

noncomputable def weightDual (w:OrderWeights P) : OrderWeights Pᵒᵈ where
  weights:=w.weights
  nonneg:=w.nonneg
  total:=w.total
  chain:=by
    intro a ha b hb
    exact (w.chain a ha b hb).symm

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_ContractionPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

noncomputable def contractionToPoint {X:Type*} [TopologicalSpace X]
    (a:X) (H:ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.const X a)) (b:X) :
    ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.const X b) :=
  H.trans {
    toFun p:=H (σ p.1,b)
    continuous_toFun:=H.continuous.comp ((unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_const)
    map_zero_left:=by intro x;rw [unitInterval.symm_zero,H.apply_one];rfl
    map_one_left:=by intro x;rw [unitInterval.symm_one,H.apply_zero];rfl }

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_WeightJoinKey
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

noncomputable def weightJoinKey (A:Set P) (d:P→ℕ) (x:P) : ℕ :=
  if x∈A then 0 else d x+1

def WeightJoinEarlier (A:Set P) (d:P→ℕ) (x y:P) : Prop :=
  Prod.Lex (·<·) WellOrderingRel (weightJoinKey A d x,x) (weightJoinKey A d y,y)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_WeightEarlierLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

abbrev WeightEarlierLower (r:P→P→Prop) (v:P) := {x:P // r x v ∧ x<v}
abbrev WeightEarlierUpper (r:P→P→Prop) (v:P) := {x:P // r x v ∧ v<x}

noncomputable def earlierLowerIso (r:P→P→Prop) (v:P) :
    WeightEarlierLower r v≃o {x:WeightEarlierLink r v // x.val<v} where
  toFun x:=⟨⟨x.val,x.property.1,Or.inl x.property.2.le⟩,x.property.2⟩
  invFun x:=⟨x.val.val,x.val.property.1,x.property⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=by intros;rfl

noncomputable def earlierUpperIso (r:P→P→Prop) (hirr:∀x,¬r x x) (v:P) :
    WeightEarlierUpper r v≃o {x:WeightEarlierLink r v // ¬x.val<v} where
  toFun x:=⟨⟨x.val,x.property.1,Or.inr x.property.2.le⟩,not_lt_of_ge x.property.2.le⟩
  invFun x:=⟨x.val.val,x.val.property.1,by
    have hne : x.val.val≠v := by
      intro he
      have hr:=x.val.property.1
      rw [he] at hr
      exact hirr v hr
    rcases x.val.property.2 with h|h
    · exact (x.property (lt_of_le_of_ne h hne)).elim
    · exact lt_of_le_of_ne h hne.symm⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=by intros;rfl

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeUpperBasics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Highest-incidence comparisons for upper edges of the relative filtration. -/
namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
  (U : Set (S ⊕ Unit)) (cutoff : ℤ)

omit [LinearOrder S] in
lemma relativeSign_congr_above (p r : ℕ →₀ (S ⊕ Unit → ℝ)) (k : ℕ)
    (he : ∀ d, k ≤ d → p d = r d) (i : S ⊕ Unit) :
    relativeSign M U p k i = relativeSign M U r k i := by
  have hk := he k le_rfl
  have hs : relativePositiveSign (framedCartan M) U p k i ↔
      relativePositiveSign (framedCartan M) U r k i := by
    unfold relativePositiveSign
    simp only [hk]
    constructor
    · rintro ⟨I, hi, hU, hc, hr, hh⟩
      exact ⟨I, hi, hU, hc, hr, fun d hd j hj => by rw [←he d hd.le]; exact hh d hd j hj⟩
    · rintro ⟨I, hi, hU, hc, hr, hh⟩
      exact ⟨I, hi, hU, hc, hr, fun d hd j hj => by rw [he d hd.le]; exact hh d hd j hj⟩
  simp only [relativeSign, hk, hs]

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeNullBlockData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

omit [LinearOrder S] in
def RelativeNullData (p:ℕ →₀ (S ⊕ Unit → ℝ)) (q:ℕ) (i:S ⊕ Unit) : Prop :=
  sourcePositiveComponent M (p q) i ⊆ U ∧
  (∀ j ∈ sourcePositiveComponent M (p q) i, (framedCartan M *ᵥ p q) j=0) ∧
  ∀ j ∈ sourceClosedRegion M (sourcePositiveComponent M (p q) i), ∀ d, q<d → p d j=0


end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_Realizations_WeightColor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CategoryTheory

attribute [local instance] Classical.decEq Classical.propDecidable
universe u v
variable {P:Type u} [PartialOrder P]

noncomputable def weightColor {A:Type v} (f:P→A) (w:OrderWeights P) : A :=
  f (Classical.choose w.support_nonempty)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeDiagram
attribute [-simp] _root_.OAI.HarmonicArtin.ParabolicIntersections.mem_relativeStabilizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The relative diagram in §2.1 of paper 082-03

Adjoin the color `f`, with label 2 to the chosen standard type `X` and
label 3 to its complement. The existing fusion construction subsequently
adjoins the universal auxiliary color `o`. The map on Artin presentations
is constructed directly; no parabolic embedding theorem is assumed here.
-/

namespace HarmonicArtin.ParabolicIntersections

attribute [local instance] Classical.propDecidable

variable {S : Type*} (M : CoxeterMatrix S) (X : Set S)

noncomputable def relativeMatrix : CoxeterMatrix (S ⊕ Unit) := by
  classical
  exact {
    M := fun a b => match a, b with
      | .inl s, .inl t => M s t
      | .inl s, .inr _ => if s ∈ X then 2 else 3
      | .inr _, .inl s => if s ∈ X then 2 else 3
      | .inr _, .inr _ => 1
    isSymm := by
      apply Matrix.ext
      intro a b
      cases a <;> cases b <;> dsimp [Matrix.transpose]
      exact M.symmetric _ _
    diagonal := by intro a; cases a <;> simp
    off_diagonal := by
      intro a b h
      cases a with
      | inl s =>
        cases b with
        | inl t => exact M.off_diagonal s t (fun e => h (congrArg Sum.inl e))
        | inr u => dsimp; split_ifs <;> norm_num
      | inr u =>
        cases b with
        | inl t => dsimp; split_ifs <;> norm_num
        | inr v => exact (h (by cases u; cases v; rfl)).elim }

@[simp] theorem relativeMatrix_original (s t : S) :
    relativeMatrix M X (.inl s) (.inl t) = M s t := rfl

@[simp] theorem relativeMatrix_frame (s : S) :
    relativeMatrix M X (.inl s) (.inr ()) = if s ∈ X then 2 else 3 := by
  classical
  rfl

theorem alternating_lift_inclusion (s t : S) (n : ℕ) :
    FreeGroup.lift (fun s => generator (relativeMatrix M X) (.inl s))
      (alternating s t n) =
    FreeGroup.lift (generator (relativeMatrix M X))
      (alternating (.inl s) (.inl t) n) := by
  induction n generalizing s t with
  | zero => simp [alternating]
  | succ n ih => simp only [alternating, map_mul, FreeGroup.lift_apply_of, ih]

theorem relative_relators : ∀ r ∈ braidRelators M,
    FreeGroup.lift (fun s => generator (relativeMatrix M X) (.inl s)) r = 1 := by
  rintro r ⟨⟨s, t⟩, rfl⟩
  rw [map_mul, map_inv, alternating_lift_inclusion, alternating_lift_inclusion]
  change FreeGroup.lift (PresentedGroup.of (rels := braidRelators (relativeMatrix M X)))
    (alternating (.inl s) (.inl t) (M s t)) *
    (FreeGroup.lift (PresentedGroup.of (rels := braidRelators (relativeMatrix M X)))
      (alternating (.inl t) (.inl s) (M s t)))⁻¹ = 1
  rw [← map_inv, ← map_mul]
  have hl : FreeGroup.lift (PresentedGroup.of (rels := braidRelators (relativeMatrix M X))) =
      PresentedGroup.mk (braidRelators (relativeMatrix M X)) := by
    apply FreeGroup.ext_hom
    intro s
    rfl
  rw [hl]
  exact PresentedGroup.one_of_mem ⟨(.inl s, .inl t), rfl⟩

/-- The canonical homomorphism into the Artin group of the relative diagram. -/
noncomputable def relativeArtinHom : Artin M →* Artin (relativeMatrix M X) :=
  PresentedGroup.toGroup (relative_relators M X)

@[simp] theorem relativeArtinHom_generator (s : S) :
    relativeArtinHom M X (generator M s) =
      generator (relativeMatrix M X) (.inl s) :=
  PresentedGroup.toGroup.of _

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The relative categorical family of paper 082-03

The family consists of actual bounded-projective homotopy classes in the
extended diagram. Its initial color is the new relative color `f`; the
auxiliary universal color is the one already adjoined by the fusion model.
-/

namespace HarmonicArtin.ParabolicIntersections

variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (X : Set S)
local instance instLinearOrderSumUnit_solutions : LinearOrder (S ⊕ Unit) := Sum.Lex.linearOrder

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_RelativeInitialStabilizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The initial stabilizer in the relative diagram

The sole input below is the unrestricted standard-parabolic embedding theorem:
van der Lek, *The Homotopy Type of Complex Hyperplane Complements* (1983),
Chapter II, §4, Theorem 4.13(i). See also Charney–Paris, *Convexity of parabolic
subgroups in Artin groups* (2014), §1, p. 2, https://arxiv.org/abs/1401.7634.
The exact case needed is injectivity of the canonical inclusion from the
original Artin presentation into the presentation with one additional color.
The categorical stabilizer identity is proved below, not assumed.
-/
namespace HarmonicArtin.ParabolicIntersections
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (X:Set S)
local instance instLinearOrderSumUnit_solutions_1 : LinearOrder (S⊕Unit) := Sum.Lex.linearOrder
attribute [local instance] Classical.decEq Classical.propDecidable

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PathImages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Iterated images of the arrow coefficient maps. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {A I : Type} [Fintype I] [DecidableEq I] (B : A → Matrix I I ℂ)

noncomputable def pathImages (n : ℕ) : Submodule ℂ (I → ℂ) :=
  Submodule.span ℂ {x | ∃ w : List A, w.length = n ∧
    ∃ y : I → ℂ, Matrix.vecMul y (w.map B).prod = x}

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_PositiveSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Support of an element of the actual positive Artin monoid. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable

@[ext] structure SupportValue (S : Type) where
  carrier : Set S

instance instCommMonoidSupportValue {S : Type} : CommMonoid (SupportValue S) where
  mul a b := ⟨a.carrier ∪ b.carrier⟩
  one := ⟨∅⟩
  mul_assoc a b c := by ext s; exact or_assoc
  one_mul a := by ext s; change (False ∨ s ∈ a.carrier) ↔ s ∈ a.carrier; tauto
  mul_one a := by ext s; change (s ∈ a.carrier ∨ False) ↔ s ∈ a.carrier; tauto
  mul_comm a b := by ext s; exact or_comm

lemma supportValue_word {S : Type} (w : List S) (s : S) :
    s ∈ ((w.map (fun t => (⟨{t}⟩ : SupportValue S))).prod).carrier ↔ s ∈ w := by
  induction w with
  | nil => change False ↔ s ∈ ([] : List S); simp
  | cons t w ih =>
    change (s=t ∨ s ∈ ((w.map (fun t => (⟨{t}⟩ : SupportValue S))).prod).carrier) ↔ _
    rw [ih, List.mem_cons]

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MainIntersection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The main intersection theorems of paper 082-03

The hypotheses are exactly the published inputs documented in
`MeshNilpotence`, `FoldingGcdInput`, `AcyclicTwistInput`, and
`RelativeInitialStabilizer`. All relative-height, positive-height,
stabilizer-containment and rank-induction arguments are proved in this
local development; none of those new assertions is a hypothesis here.
-/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

section Relative
local instance instLinearOrderSumUnit_solutions_2 : LinearOrder (S⊕Unit) := Sum.Lex.linearOrder
end Relative

local instance instLinearOrderSumUnit_solutions_3 : LinearOrder (S⊕Unit) := Sum.Lex.linearOrder

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ConditionalMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Main statements with the acyclic-evaluation input already discharged. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [fS : Fintype S] [oS : LinearOrder S] (M : CoxeterMatrix S)

local instance conditionalSumOrder : LinearOrder (S⊕Unit) := Sum.Lex.linearOrder

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ParabolicRead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reading the parabolic letters crossed by a Coxeter gallery. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W : Type} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)
    (J : Set S)

noncomputable def parabolicLetterValue : Option J → W
  | none => 1
  | some t => cs.simple t

noncomputable def parabolicLetter (r : W) : Option J :=
  Classical.epsilon (fun l => parabolicLetterValue cs J l=r)

lemma parabolicLetter_word (l : Option J) :
    cs.wordProd (l.toList.map Subtype.val)=parabolicLetterValue cs J l := by
  cases l <;> simp [parabolicLetterValue]

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ParabolicReadReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A parabolic read of a reduced gallery is reduced. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W : Type} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

lemma conjugate_sequence (a b : W) (l : List W) :
    (l.map (MulAut.conj b)).map (MulAut.conj a) = l.map (MulAut.conj (a*b)) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro x _
  simp only [Function.comp_apply,MulAut.conj_apply]
  group

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_GeneratorPowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Infinite cyclic generator subgroups and their intersections with standard
parabolics. The retraction argument supplies infinite branching in visual trees. -/
namespace HarmonicArtin.ParabolicIntersections
open Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} (M : CoxeterMatrix S)

lemma exponent_alternating (s t : S) (n : ℕ) :
    FreeGroup.lift (fun _ : S => Multiplicative.ofAdd (1 : ℤ)) (alternating s t n)=
      Multiplicative.ofAdd (n : ℤ) := by
  induction n generalizing s t with
  | zero => rfl
  | succ n ih =>
    rw [alternating,map_mul,FreeGroup.lift_apply_of,ih]
    change Multiplicative.ofAdd (1+(n : ℤ))=Multiplicative.ofAdd (n+1 : ℤ)
    congr 1
    omega

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_GraphMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real-valued graph metric and the induced isometric action. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {V : Type} (H : SimpleGraph V)

@[instance_reducible]
noncomputable def graphMetric (hH : H.Connected) : MetricSpace V where
  dist x y := H.dist x y
  dist_self x := by simp
  dist_comm x y := by rw [H.dist_comm]
  dist_triangle x y z := by exact_mod_cast hH.dist_triangle (u := x) (v := y) (w := z)
  eq_of_dist_eq_zero h := hH.dist_eq_zero_iff.mp (Nat.cast_eq_zero.mp h)

variable {G : Type} [Group G] [MulAction G V]

lemma graph_action_dist (hH : H.Connected)
    (hA : ∀ g : G,∀ ⦃x y : V⦄,H.Adj x y → H.Adj (g • x) (g • y))
    (g : G) (x y : V) : H.dist (g • x) (g • y)=H.dist x y := by
  have hle (a : G) (u v : V) : H.dist (a • u) (a • v)≤H.dist u v := by
    obtain ⟨p,hp⟩ := hH.exists_walk_length_eq_dist u v
    let f : H →g H := ⟨(a • ·),fun h => hA a h⟩
    have h := H.dist_le (p.map f)
    change H.dist (a • u) (a • v)≤(p.map f).length at h
    simpa only [SimpleGraph.Walk.length_map,hp] using h
  apply le_antisymm (hle g x y)
  simpa only [inv_smul_smul] using hle g⁻¹ (g • x) (g • y)

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_GraphRealizationDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The path distance on unit intervals attached to graph edges. -/
namespace HarmonicArtin.ParabolicIntersections.GraphRealization
open TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} (H : SimpleGraph V)

/-- Endpoints are retained at this stage and identified by the metric quotient. -/
inductive Point where
  | vertex : V → Point
  | edge : H.Dart → Set.Icc (0 : ℝ) 1 → Point

def anchor : Point H → Bool → V
  | .vertex v, _ => v
  | .edge e _, false => e.fst
  | .edge e _, true => e.snd

def weight : Point H → Bool → ℝ
  | .vertex _, _ => 0
  | .edge _ t, false => t
  | .edge _ t, true => 1-t

noncomputable def route (p q : Point H) (i j : Bool) : ℝ :=
  weight H p i+(H.dist (anchor H p i) (anchor H q j) : ℝ)+weight H q j

noncomputable def via (p q : Point H) : ℝ :=
  min (route H p q false false) (min (route H p q false true)
    (min (route H p q true false) (route H p q true true)))

noncomputable def distance : Point H → Point H → ℝ
  | .edge e t, .edge f s => if e=f then min |(t : ℝ)-s| (via H (.edge e t) (.edge f s))
      else via H (.edge e t) (.edge f s)
  | p,q => via H p q

lemma weight_nonneg (p : Point H) (i : Bool) : 0 ≤ weight H p i := by
  cases p with
  | vertex v => rfl
  | edge e t => cases i <;> simp only [weight] <;> linarith [t.property.1,t.property.2]

lemma route_nonneg (p q : Point H) (i j : Bool) : 0 ≤ route H p q i j := by
  exact add_nonneg (add_nonneg (weight_nonneg H p i) (Nat.cast_nonneg _)) (weight_nonneg H q j)

lemma via_le_route (p q : Point H) (i j : Bool) : via H p q ≤ route H p q i j := by
  cases i <;> cases j <;> simp only [via] <;> order

lemma via_eq_route (p q : Point H) : ∃ i j, via H p q=route H p q i j := by
  rcases min_choice (route H p q false false)
    (min (route H p q false true) (min (route H p q true false) (route H p q true true))) with h|h
  · exact ⟨false,false,h⟩
  · rcases min_choice (route H p q false true)
      (min (route H p q true false) (route H p q true true)) with h'|h'
    · exact ⟨false,true,h.trans h'⟩
    · rcases min_choice (route H p q true false) (route H p q true true) with h''|h''
      · exact ⟨true,false,h.trans (h'.trans h'')⟩
      · exact ⟨true,true,h.trans (h'.trans h'')⟩

lemma distance_le_via (p q : Point H) : distance H p q ≤ via H p q := by
  cases p <;> cases q <;> simp only [distance]
  all_goals first | exact le_rfl | (split_ifs <;> order)

lemma distance_le_route (p q : Point H) (i j : Bool) : distance H p q ≤ route H p q i j :=
  (distance_le_via H p q).trans (via_le_route H p q i j)

lemma distance_le_direct (e : H.Dart) (t s : Set.Icc (0 : ℝ) 1) :
    distance H (.edge e t) (.edge e s) ≤ |(t : ℝ)-s| := by
  simp [distance]

lemma route_comm (p q : Point H) (i j : Bool) : route H p q i j=route H q p j i := by
  unfold route
  rw [H.dist_comm]
  ring

lemma anchor_bridge (p : Point H) (i j : Bool) :
    (H.dist (anchor H p i) (anchor H p j) : ℝ) ≤ weight H p i+weight H p j := by
  cases p with
  | vertex v => simp [anchor,weight]
  | edge e t =>
    have hd : H.dist e.fst e.snd=1 := H.dist_eq_one_iff_adj.mpr e.adj
    have hd' : H.dist e.snd e.fst=1 := H.dist_eq_one_iff_adj.mpr e.adj.symm
    cases i <;> cases j <;> simp only [anchor,weight,hd,hd',SimpleGraph.dist_self,Nat.cast_zero,Nat.cast_one]
    all_goals linarith [t.property.1,t.property.2]

lemma edge_weight_le (e : H.Dart) (t s : Set.Icc (0 : ℝ) 1) (i : Bool) :
    weight H (.edge e t) i ≤ weight H (.edge e s) i+|(t : ℝ)-s| := by
  cases i <;> simp only [weight]
  · linarith [le_abs_self ((t : ℝ)-s)]
  · linarith [neg_le_abs ((t : ℝ)-s)]

lemma route_triangle (hH : H.Connected) (p q r : Point H) (i j k l : Bool) :
    route H p r i l ≤ route H p q i j+route H q r k l := by
  have h₁ := hH.dist_triangle (u := anchor H p i) (v := anchor H q j) (w := anchor H r l)
  have h₂ := hH.dist_triangle (u := anchor H q j) (v := anchor H q k) (w := anchor H r l)
  have h₁' : (H.dist (anchor H p i) (anchor H r l) : ℝ) ≤
      H.dist (anchor H p i) (anchor H q j)+H.dist (anchor H q j) (anchor H r l) := by exact_mod_cast h₁
  have h₂' : (H.dist (anchor H q j) (anchor H r l) : ℝ) ≤
      H.dist (anchor H q j) (anchor H q k)+H.dist (anchor H q k) (anchor H r l) := by exact_mod_cast h₂
  have hb := anchor_bridge H q j k
  unfold route
  linarith

end HarmonicArtin.ParabolicIntersections.GraphRealization

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeActionDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Basic data for actions on simplicial trees. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V)

def PreservesAdj : Prop := ∀ g : G, ∀ {u v : V}, T.Adj u v → T.Adj (g • u) (g • v)

def translate (hA : PreservesAdj (G := G) T) (g : G) : T →g T :=
  ⟨(g • ·),hA g⟩

def pairStabilizer (u v : V) : Subgroup G :=
  MulAction.stabilizer G u ⊓ MulAction.stabilizer G v

/-- A set contains the unique path between any two of its vertices. -/
def PathClosed (T : SimpleGraph V) (U : Set V) : Prop :=
  ∀ ⦃u v⦄, u∈U → v∈U → ∀ p : T.Walk u v, p.IsPath → ∀ w∈p.support,w∈U

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_GraphRealizationAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An action on a graph extends isometrically to its unit-interval realization. -/
namespace HarmonicArtin.ParabolicIntersections.GraphRealization
open TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (H : SimpleGraph V) (hA : PreservesAdj (G := G) H)

def actDart (g : G) (e : H.Dart) : H.Dart := ⟨(g • e.fst,g • e.snd),hA g e.adj⟩

lemma actDart_injective (g : G) : Function.Injective (actDart H hA g) := by
  intro e f he
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · exact (MulAction.toPerm g).injective (congrArg (fun d : H.Dart => d.fst) he)
  · exact (MulAction.toPerm g).injective (congrArg (fun d : H.Dart => d.snd) he)

end HarmonicArtin.ParabolicIntersections.GraphRealization

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshPathSpaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite path spaces and weighted last-backtrack contractions. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} (G : SimpleGraph V)

/-- Paths of length `n`, indexed by their final vertex. The recursive
presentation makes extension of prefix operators a block-diagonal map. -/
def MeshPaths : ℕ → V → Type
  | 0, _ => PUnit
  | n+1, v => Σ u : {u : V // G.Adj u v}, MeshPaths n u.val

noncomputable instance meshPathsFintype [Fintype V] (n : ℕ) (v : V) : Fintype (MeshPaths G n v) := by
  induction n generalizing v with
  | zero => change Fintype PUnit; infer_instance
  | succ n ih =>
    change Fintype (Σ u : {u : V // G.Adj u v}, MeshPaths G n u.val)
    let (u : V) : Fintype (MeshPaths G n u) := ih u
    infer_instance

/-- Attach the last two edges `v,u,v` to a path ending at `v`. -/
def meshInsertBacktrack {n : ℕ} {v : V} (u : {u : V // G.Adj u v})
    (p : MeshPaths G n v) : MeshPaths G (n+2) v :=
  ⟨u,⟨⟨v,u.property.symm⟩,p⟩⟩

variable [Fintype V]

/-- The contraction coefficient is the positive square root used in the
essential-path representation of the mesh algebra. -/
noncomputable def meshContractionMatrix (μ : V → ℝ) (n : ℕ) (v : V) :
    Matrix (MeshPaths G n v) (MeshPaths G (n+2) v) ℂ :=
  fun p q => ∑ u : {u : V // G.Adj u v},
    if q=meshInsertBacktrack G u p then (Real.sqrt (μ u/μ v) : ℂ) else 0

/-- Extending a prefix operator by one edge, without changing that edge. -/
noncomputable def meshExtendMatrix {m n : ℕ}
    (T : ∀ v, Matrix (MeshPaths G m v) (MeshPaths G n v) ℂ) (v : V) :
    Matrix (MeshPaths G (m+1) v) (MeshPaths G (n+1) v) ℂ :=
  Matrix.blockDiagonal' (fun u : {u : V // G.Adj u v} => T u.val)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshMatrixAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluating complex path matrices in an arbitrary complex module. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I J K R : Type} [Fintype I] [Fintype J] [Fintype K]
variable [AddCommGroup R] [Module ℂ R]

noncomputable def meshApply (A : Matrix I J ℂ) (f : I → R) (q : J) : R :=
  ∑ p, A p q • f p

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshQuantum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite positivity interval for the Jones--Wenzl scalar recurrence. -/
namespace HarmonicArtin.ParabolicIntersections

/-- Quantum integers as a real recurrence, with no trigonometric choices. -/
noncomputable def meshQuantum (δ : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | n+2 => δ*meshQuantum δ (n+1)-meshQuantum δ n

@[simp] lemma meshQuantum_zero (δ : ℝ) : meshQuantum δ 0=0 := rfl
@[simp] lemma meshQuantum_one (δ : ℝ) : meshQuantum δ 1=1 := rfl

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive weighted traces detect vanishing of all endpoint projections. -/
namespace HarmonicArtin.ParabolicIntersections
open scoped ComplexOrder
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} [Fintype V]

noncomputable def meshWeightedTrace {D : V → Type} [∀ v, Fintype (D v)]
    (μ : V → ℝ) (P : ∀ v, Matrix (D v) (D v) ℂ) : ℂ :=
  ∑ v, (μ v : ℂ)*Matrix.trace (P v)

variable (G : SimpleGraph V)

/-- Reversal of an oriented edge exchanges the two endpoint sums. -/
def meshEdgeFlip : (Σ v : V, {u : V // G.Adj u v}) ≃
    (Σ v : V, {u : V // G.Adj u v}) where
  toFun p := ⟨p.2.val,⟨p.1,p.2.property.symm⟩⟩
  invFun p := ⟨p.2.val,⟨p.1,p.2.property.symm⟩⟩
  left_inv := by rintro ⟨v,⟨u,h⟩⟩; rfl
  right_inv := by rintro ⟨v,⟨u,h⟩⟩; rfl

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Jones--Wenzl projections on the actual finite path spaces. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} [Fintype V] (G : SimpleGraph V)

/-- The correction formula removes precisely the final contraction from
the already projected prefix. Only positive-index quantum integers occur
as denominators before the cutoff. -/
noncomputable def meshProjection (μ : V → ℝ) (δ : ℝ) :
    (n : ℕ) → (v : V) → Matrix (MeshPaths G n v) (MeshPaths G n v) ℂ
  | 0, _ => 1
  | 1, _ => 1
  | n+2, v =>
    let Q := meshExtendMatrix G (meshProjection μ δ (n+1)) v
    let T := meshContractionMatrix G μ n v * Q
    Q - (((meshQuantum δ (n+2)/meshQuantum δ (n+1))⁻¹ : ℝ) : ℂ) •
      (T.conjTranspose*T)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshProjectionInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Jones--Wenzl induction before the first nonpositive quantum integer. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} [Fintype V] (G : SimpleGraph V)

structure MeshProjectionStage (μ : V → ℝ) (δ : ℝ) (n : ℕ) : Prop where
  lower_star : ∀ v, (meshProjection G μ δ n v).conjTranspose=meshProjection G μ δ n v
  lower_square : ∀ v, meshProjection G μ δ n v*meshProjection G μ δ n v=meshProjection G μ δ n v
  upper_star : ∀ v, (meshProjection G μ δ (n+1) v).conjTranspose=meshProjection G μ δ (n+1) v
  upper_square : ∀ v, meshProjection G μ δ (n+1) v*meshProjection G μ δ (n+1) v=
    meshProjection G μ δ (n+1) v
  nested : ∀ v, meshProjection G μ δ (n+1) v*meshExtendMatrix G (meshProjection G μ δ n) v=
    meshProjection G μ δ (n+1) v
  scalar : ∀ v, meshContractionMatrix G μ n v *
    meshExtendMatrix G (meshProjection G μ δ (n+1)) v *
    (meshContractionMatrix G μ n v).conjTranspose =
    ((meshQuantum δ (n+2)/meshQuantum δ (n+1) : ℝ) : ℂ) • meshProjection G μ δ n v
  trace_recurrence : n≠0 → ∀ v, Matrix.trace (meshProjection G μ δ (n+1) v)=
    Matrix.trace (meshExtendMatrix G (meshProjection G μ δ n) v)-
      Matrix.trace (meshProjection G μ δ (n-1) v)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshPathEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted mesh relations annihilate sufficiently long actual paths. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V R : Type} [Fintype V] (G : SimpleGraph V)
variable [Ring R] [Algebra ℂ R]

def meshPathEvaluate (B : ∀ u v, G.Adj u v → R) :
    (n : ℕ) → (v : V) → MeshPaths G n v → R
  | 0, _, _ => 1
  | n+1, v, p => meshPathEvaluate B n p.1.val p.2 * B p.1.val v p.1.property

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passage from the weighted essential-path relations to all-plus meshes. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V R : Type} [Fintype V] (G : SimpleGraph V) [Ring R] [Algebra ℂ R]

noncomputable def meshRescale (μ : V → ℝ) (B : ∀ u v, G.Adj u v → R)
    (u v : V) (h : G.Adj u v) : R :=
  ((Real.sqrt (μ v))⁻¹ : ℂ) • B u v h

noncomputable def meshPathScale (μ : V → ℝ) :
    (n : ℕ) → (v : V) → MeshPaths G n v → ℂ
  | 0, _, _ => 1
  | n+1, v, p => meshPathScale μ n p.1.val p.2 * ((Real.sqrt (μ v))⁻¹ : ℂ)

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshGraphNilpotence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite mesh path bounds, including disconnected positive Cartan graphs. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
open _root_.Matrix
variable {V R : Type} [Fintype V] (G : SimpleGraph V) [Ring R] [Algebra ℂ R]

omit [Fintype V] in
def meshPathInComponent (C : G.ConnectedComponent) :
    (n : ℕ) → (v : C) → MeshPaths G n v.val → MeshPaths C.toSimpleGraph n v
  | 0, _, _ => PUnit.unit
  | n+1, v, p =>
    let u : C := ⟨p.1.val,C.mem_supp_of_adj_mem_supp v.property p.1.property.symm⟩
    ⟨⟨u,p.1.property⟩,meshPathInComponent C n u p.2⟩

omit [Fintype V] in
def meshComponentNeighborEquiv (C : G.ConnectedComponent) (v : C) :
    {u : C // C.toSimpleGraph.Adj u v} ≃ {u : V // G.Adj u v.val} where
  toFun u := ⟨u.val.val,u.property⟩
  invFun u := ⟨⟨u.val,C.mem_supp_of_adj_mem_supp v.property u.property.symm⟩,u.property⟩
  left_inv u := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv u := by apply Subtype.ext; rfl

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ReducedInputsMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Main results after discharging the acyclic-twist and folding inputs. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

local instance instLinearOrderSumUnit_solutions_5 : LinearOrder (S⊕Unit) := Sum.Lex.linearOrder

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Main results after discharging standard embeddings, acyclic twists,
and folding. Only mesh nilpotence and the dynamical criteria remain. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
local instance instLinearOrderSumUnit_solutions_6 : LinearOrder (S⊕Unit) := Sum.Lex.linearOrder

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MeshQuiverAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite positive Cartan quivers satisfy the explicit mesh ideal bound. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A R : Type}
  [Fintype V]
  [Fintype A]
  (U : Set V)
  [Ring R]
  [Algebra ℂ R]
noncomputable local instance (priority := 2000) meshRegionDecEq : DecidableEq U := Classical.decEq U

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_MetricUnitCurves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concatenation of unit-speed curves and realization of distance. -/
namespace HarmonicArtin.ParabolicIntersections.GraphRealization
variable {X : Type} [MetricSpace X]

def HasCurve (x y : X) (L : ℝ) : Prop :=
  ∃ f : ℝ → X,(∀ s t,dist (f s) (f t) ≤ |s-t|) ∧ f 0=x ∧ f L=y

end HarmonicArtin.ParabolicIntersections.GraphRealization

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_NoncommutingGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Irreducibility is connectedness of the noncommutation graph. -/
namespace HarmonicArtin.ParabolicIntersections
variable {S : Type} (M : CoxeterMatrix S)

def noncommutingGraph : SimpleGraph S where
  Adj a b := a≠b ∧ M a b≠2
  symm := ⟨by
    intro a b h
    exact ⟨h.1.symm,fun he => h.2 ((M.symmetric a b).trans he)⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_OrbitEdgeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The connected subtree generated by an orbit of one edge. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (P : Subgroup G) (u v : V) (hne : u≠v)

def orbitEdgeGraph : SimpleGraph V where
  Adj x y := ∃ p∈P, (x=p • u ∧ y=p • v) ∨ (x=p • v ∧ y=p • u)
  symm := ⟨by
    rintro x y ⟨p,hp,h⟩
    exact ⟨p,hp,h.elim (fun h => Or.inr ⟨h.2,h.1⟩) (fun h => Or.inl ⟨h.2,h.1⟩)⟩⟩
  loopless := ⟨by
    rintro x ⟨p,_,h⟩
    rcases h with ⟨hu,hv⟩|⟨hv,hu⟩
    all_goals exact hne ((MulAction.toPerm p).injective (hu.symm.trans hv))⟩

def orbit_translate (p : G) (hp : p∈P) :
    orbitEdgeGraph P u v hne →g orbitEdgeGraph P u v hne where
  toFun := (p • ·)
  map_rel' := by
    rintro x y ⟨q,hq,hxy⟩
    refine ⟨p*q,P.mul_mem hp hq,?_⟩
    rcases hxy with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact Or.inl ⟨(mul_smul p q u).symm,(mul_smul p q v).symm⟩
    · exact Or.inr ⟨(mul_smul p q v).symm,(mul_smul p q u).symm⟩

variable {P u v hne}

def orbitVertices (P : Subgroup G) (u v : V) : Set V :=
  {w | ∃ p∈P, w=p • u ∨ w=p • v}

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeSegmentOccurrences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite translates of a segment inside a finite path

This is the finite-pattern input for constructing an acylindrical graph
from a tree action. The segment is in the actual tree and its pointwise
stabilizer is trivial; its occurrences are group elements, not formal labels.
-/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {G V : Type} [Group G] [MulAction G V]

/-- Group translates whose two endpoints occur in a specified finite path. -/
def segmentOccurrences (u v : V) (T : SimpleGraph V) {x y : V} (p : T.Walk x y) : Set G :=
  {g | g • u∈p.support ∧ g • v∈p.support}

/-- A path contains a translate of the fixed segment. In a tree the
endpoint condition also puts the entire translated segment in the path. -/
def ContainsSegment (u v : V) (T : SimpleGraph V) {x y : V} (p : T.Walk x y) : Prop :=
  (segmentOccurrences (G := G) u v T p).Nonempty


lemma segmentOccurrences_reverse (u v : V) (T : SimpleGraph V) {x y : V} (p : T.Walk x y) :
    segmentOccurrences (G := G) u v T p.reverse=segmentOccurrences u v T p := by
  ext g
  simp only [segmentOccurrences,Set.mem_ofPred_eq,SimpleGraph.Walk.support_reverse,List.mem_reverse]

lemma smul_mem_mapped_support (T : SimpleGraph V) (hA : PreservesAdj (G := G) T)
    {x y w : V} (p : T.Walk x y) (g h : G) :
    h • w∈(p.map (translate T hA g)).support ↔ (g⁻¹*h) • w∈p.support := by
  rw [SimpleGraph.Walk.support_map]
  constructor
  · intro hm
    obtain ⟨z,hz,he⟩ := List.mem_map.mp hm
    change g • z=h • w at he
    have hzw : z=(g⁻¹*h) • w := by
      have hh := congrArg (fun t : V => g⁻¹ • t) he
      simpa only [←mul_smul,inv_mul_cancel,one_smul] using hh
    exact hzw ▸ hz
  · intro hh
    refine List.mem_map.mpr ⟨(g⁻¹*h) • w,hh,?_⟩
    change g • ((g⁻¹*h) • w)=h • w
    rw [←mul_smul,mul_inv_cancel_left]

lemma segmentOccurrences_map (u v : V) (T : SimpleGraph V)
    (hA : PreservesAdj (G := G) T) {x y : V} (p : T.Walk x y) (g h : G) :
    h∈segmentOccurrences (G := G) u v T (p.map (translate T hA g)) ↔
      g⁻¹*h∈segmentOccurrences u v T p := by
  exact and_congr (smul_mem_mapped_support T hA p g h)
    (smul_mem_mapped_support T hA p g h)

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeShortcutMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tree paths are approximate geodesics in a graph with convex shortcuts. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {V : Type} (T H : SimpleGraph V)

/-- Every path shortcut includes all shorter shortcuts along the same tree path. -/
def PathSaturated : Prop := ∀ ⦃x y⦄, H.Adj x y →
  ∀ p : T.Walk x y,p.IsPath → ∀ a∈p.support,∀ b∈p.support,a≠b → H.Adj a b

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeAvoidingGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coning off paths that avoid a fixed orbit of segments

The vertices remain those of the original tree. A new edge joins the
endpoints of a path containing no translate of the chosen segment.
-/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (u v : V)

def avoidingGraph : SimpleGraph V where
  Adj x y := x≠y ∧ ∀ p : T.Walk x y,p.IsPath → ¬ContainsSegment (G := G) u v T p
  symm := ⟨by
    intro x y h
    refine ⟨h.1.symm,?_⟩
    intro p hp
    have hn := h.2 p.reverse hp.reverse
    simpa only [ContainsSegment,segmentOccurrences_reverse] using hn⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

lemma avoidingGraph_preservesAdj (hA : PreservesAdj (G := G) T) :
    PreservesAdj (G := G) (avoidingGraph (G := G) T u v) := by
  intro g x y hxy
  refine ⟨fun he => hxy.1 ((MulAction.toPerm g).injective he),?_⟩
  intro p hp hbad
  let q := (p.map (translate T hA g⁻¹)).copy (inv_smul_smul g x) (inv_smul_smul g y)
  have hq : q.IsPath := by
    apply (SimpleGraph.Walk.isPath_copy _ _ _).mpr
    exact hp.map (MulAction.toPerm g⁻¹).injective
  apply hxy.2 q hq
  obtain ⟨a,ha⟩ := hbad
  refine ⟨g⁻¹*a,?_⟩
  have hm := (segmentOccurrences_map u v T hA p g⁻¹ (g⁻¹*a)).mpr ?_
  · change (g⁻¹*a) • u∈q.support ∧ (g⁻¹*a) • v∈q.support
    have hsup : q.support=(p.map (translate T hA g⁻¹)).support :=
      SimpleGraph.Walk.support_copy _ _ _
    rw [hsup]
    exact hm
  · simpa only [inv_inv,mul_inv_cancel_left] using ha

/-- If the chosen segment has at least two edges, every original edge
remains an edge after coning. -/
lemma le_avoidingGraph (hT : T.IsAcyclic) (hA : PreservesAdj (G := G) T)
    (hne : u≠v) (hnadj : ¬T.Adj u v) : T≤avoidingGraph (G := G) T u v := by
  intro x y hxy
  refine ⟨hxy.ne,?_⟩
  intro p hp hbad
  have he : p=hxy.toWalk :=
    congrArg Subtype.val (hT.subsingleton_path x y |>.elim ⟨p,hp⟩ ⟨_,.of_adj hxy⟩)
  obtain ⟨g,hgu,hgv⟩ := hbad
  rw [he] at hgu hgv
  simp only [SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_nil,
    List.mem_cons,List.not_mem_nil,or_false] at hgu hgv
  have hadj : T.Adj (g • u) (g • v) := by
    rcases hgu with hx|hy <;> rcases hgv with hx'|hy'
    · exact False.elim (hne ((MulAction.toPerm g).injective (hx.trans hx'.symm)))
    · rw [hx,hy']
      exact hxy
    · rw [hy,hx']
      exact hxy.symm
    · exact False.elim (hne ((MulAction.toPerm g).injective (hy.trans hy'.symm)))
  have h := hA g⁻¹ hadj
  simp only [inv_smul_smul] at h
  exact hnadj h

lemma avoidingGraph_connected (hT : T.IsTree) (hA : PreservesAdj (G := G) T)
    (hne : u≠v) (hnadj : ¬T.Adj u v) : (avoidingGraph (G := G) T u v).Connected :=
  hT.connected.mono (le_avoidingGraph T u v hT.isAcyclic hA hne hnadj)

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeShortcutHyperbolic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gromov hyperbolicity of a tree with convex shortcuts. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} (T H : SimpleGraph V)

noncomputable def graphProduct (o x y : V) : ℝ :=
  ((H.dist o x : ℝ)+H.dist o y-H.dist x y)/2

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreePeriodicPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Iterating a tree segment without backtracking produces an actual translation axis. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (hA : PreservesAdj (G := G) T)

abbrev shiftHom (g : G) : T →g T := ⟨(g • ·),hA g⟩

def periodicPath (g : G) {x : V} (p : T.Walk x (g • x)) :
    (n : ℕ) → T.Walk x (g^n • x)
  | 0 => (.nil : T.Walk x x).copy rfl (by simp)
  | n+1 => ((periodicPath g p n).append (p.map (shiftHom T hA (g^n)))).copy rfl
      (by change g^n • (g • x)=g^(n+1) • x; rw [←mul_smul,←pow_succ])

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeTranslationSegment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reflecting a segment at both ends constructs a tree translation. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (hA : PreservesAdj (G := G) T)

abbrev actPath (g : G) {x y : V} (p : T.Walk x y) : T.Walk (g • x) (g • y) :=
  p.map ⟨(g • ·),hA g⟩

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeBoundaryRays
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct directions of tree rays determine distinct shortcut-boundary points. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {G V : Type} [Group G] [MulAction G V]
variable (T H : SimpleGraph V)

variable (hA : PreservesAdj (G := G) T)

def inverseSegment (g : G) {x : V} (p : T.Walk x (g • x)) : T.Walk x (g⁻¹ • x) :=
  (actPath T hA g⁻¹ p.reverse).copy (by simp) rfl

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_TreeSegmentBallCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform counts for translates of a free segment near a path vertex. -/
namespace HarmonicArtin.ParabolicIntersections.TreeAction
variable {G V : Type} [Group G] [MulAction G V]
variable (T : SimpleGraph V) (u v : V)

def localSegmentOccurrences {x y : V} (p : T.Walk x y) (b : V) (L : ℕ) : Set G :=
  {g | (g • u∈p.support ∧ T.dist b (g • u)≤L) ∧
    (g • v∈p.support ∧ T.dist b (g • v)≤L)}

end HarmonicArtin.ParabolicIntersections.TreeAction

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_UnconditionalMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Unconditional parabolic intersections and closure

The spherical mesh input is proved by weighted path contractions and finite
Jones--Wenzl projections. Together with the proved standard embeddings,
folding, and acyclic evaluation, this discharges every input to Theorem 1.1
and Corollary 1.2 of paper 082-03. The dynamical corollary below still names
its separate published geometric input explicitly.
-/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

local instance instLinearOrderSumUnit_solutions_7 : LinearOrder (S⊕Unit) := Sum.Lex.linearOrder

end HarmonicArtin.ParabolicIntersections

end OAI
end

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_VisualAmalgam
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual amalgamated-product presentation of a visual splitting.
The factors and edge group are the standard subgroups of the given Artin
group, and the inverse homomorphism is constructed from its braid relators. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} (M : CoxeterMatrix S) (Y Z : Set S)

def visualSide : Bool → Set S
  | false => Y
  | true => Z

lemma visualSplit_cover (hsplit : IsVisualSplit M Y Z) (s : S) : s∈Y ∨ s∈Z := by
  change s∈Y∪Z
  rw [hsplit.1]
  trivial

lemma visualSplit_finite_edge (hsplit : IsVisualSplit M Y Z) (s t : S)
    (hm : M s t≠0) : ∃ b, s∈visualSide Y Z b ∧ t∈visualSide Y Z b := by
  by_cases hsY : s∈Y
  · by_cases htY : t∈Y
    · exact ⟨false,hsY,htY⟩
    · have htZ := (visualSplit_cover M Y Z hsplit t).resolve_left htY
      by_cases hsZ : s∈Z
      · exact ⟨true,hsZ,htZ⟩
      · exact False.elim (hm (hsplit.2.2.2 s ⟨hsY,hsZ⟩ t ⟨htZ,htY⟩))
  · have hsZ := (visualSplit_cover M Y Z hsplit s).resolve_left hsY
    by_cases htZ : t∈Z
    · exact ⟨true,hsZ,htZ⟩
    · have htY := (visualSplit_cover M Y Z hsplit t).resolve_right htZ
      exact False.elim (hm ((M.symmetric s t).trans
        (hsplit.2.2.2 t ⟨htY,htZ⟩ s ⟨hsZ,hsY⟩)))

end HarmonicArtin.ParabolicIntersections

end OAI
end


