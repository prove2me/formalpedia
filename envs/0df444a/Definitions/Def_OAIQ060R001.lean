-- Prove2me | Definitions.Def_OAIQ060R001
-- name    : OAIQ060R001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T23:47:34.092115+00:00
-- url     : https://prove2.me/theorems/5fd06e7f-07ae-4d48-8acd-4a9a3238a435
-- title:
--   Definitions bundle OAIQ060R001 of the split of OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 374 declarations of OpenAI's Lean: 299 definitions, 1 inductive type or structure, 15 instances and 59 theorems. The definitions and types are `OAI.SharpRamseyFive.FlagConstruction.DualPoint`, `OAI.SharpRamseyFive.FlagConstruction.Flag`, `OAI.SharpRamseyFive.FlagConstruction.Incident`, `OAI.SharpRamseyFive.FlagConstruction.Point`, `OAI.SharpRamseyFive.FlagConstruction.Space`, `OAI.SharpRamseyFive.FlagConstruction.graph`, `OAI.SharpRamseyFive.GlobalRadial.badCenters`, `OAI.SharpRamseyFive.GlobalRadial.localLines`, `OAI.SharpRamseyFive.GlobalRadial.richCenters`, `OAI.SharpRamseyFive.GreedyTraining.Captured`, `OAI.SharpRamseyFive.GreedyTraining.Stop`, `OAI.SharpRamseyFive.GreedyTraining.best`, `OAI.SharpRamseyFive.GreedyTraining.cell`, `OAI.SharpRamseyFive.GreedyTraining.chosen`, `OAI.SharpRamseyFive.GreedyTraining.clippedPart`, `OAI.SharpRamseyFive.GreedyTraining.firstAt`, `OAI.SharpRamseyFive.GreedyTraining.greedyList`, `OAI.SharpRamseyFive.GreedyTraining.headIndex`, `OAI.SharpRamseyFive.GreedyTraining.ownCell`, `OAI.SharpRamseyFive.GreedyTraining.peelLength`, `OAI.SharpRamseyFive.GreedyTraining.peelSet`, `OAI.SharpRamseyFive.GreedyTraining.publicOwn`, `OAI.SharpRamseyFive.GreedyTraining.publicRegion`, `OAI.SharpRamseyFive.GreedyTraining.queryPart`, `OAI.SharpRamseyFive.GreedyTraining.remaining`, `OAI.SharpRamseyFive.GreedyTraining.retained`, `OAI.SharpRamseyFive.GreedyTraining.stopIndex`, `OAI.SharpRamseyFive.GreedyTraining.twoPublicOwn`, `OAI.SharpRamseyFive.HighParameters.cap`, `OAI.SharpRamseyFive.HighParameters.degree`, `OAI.SharpRamseyFive.HighParameters.multiplicity`, `OAI.SharpRamseyFive.HighParameters.threshold`, `OAI.SharpRamseyFive.HighPlaneBudget.capturedPairs`, `OAI.SharpRamseyFive.HighPlaneBudget.headAt`, `OAI.SharpRamseyFive.HighPlaneBudget.highExceptions`, `OAI.SharpRamseyFive.HighPlaneBudget.residualExceptions`, `OAI.SharpRamseyFive.HighPlaneBudget.residualPairs`, `OAI.SharpRamseyFive.HighPlaneBudget.residualPlanes`, `OAI.SharpRamseyFive.HighPlaneBudget.richAt`, `OAI.SharpRamseyFive.HighPlaneBudget.tail` and 260 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `RamseyFive_Bounds_DensityUpper`, `RamseyFive_Bounds_PrimeConstruction`, `RamseyFive_Decoding_Best`, `RamseyFive_Decoding_Beta`, `RamseyFive_Decoding_CoordinateMap`, `RamseyFive_Decoding_FinsetEquivPositions`, `RamseyFive_Decoding_FreshPublicValidation`, `RamseyFive_Decoding_MetadataCodec`, `RamseyFive_Decoding_Nonpairs`, `RamseyFive_Decoding_OffFiberPairs`, `RamseyFive_Decoding_ProducedCapExclusion`, `RamseyFive_Decoding_PublicTraining`, `RamseyFive_Decoding_ReverseCap`, `RamseyFive_Decoding_ReverseParameters`, `RamseyFive_Decoding_RichCenters`, `RamseyFive_Decoding_Swap`, `RamseyFive_Decoding_Threshold`, `RamseyFive_Decoding_Training`, `RamseyFive_Decoding_UniversalFresh`, `RamseyFive_Decoding_UniversalReverse`, `RamseyFive_Entropy_AllWindowCost`, `RamseyFive_Entropy_BaseFiniteCost`, `RamseyFive_Entropy_FinalMarking`, `RamseyFive_Entropy_FreshPublicFamily`, `RamseyFive_Entropy_HighBudgetPoly`, `RamseyFive_Entropy_HighExceptions`, `RamseyFive_Entropy_HighMomentBudget`, `RamseyFive_Entropy_IteratedBudgets`, `RamseyFive_Entropy_LogContractionDrop`, `RamseyFive_Entropy_LowBudgetPoly`, `RamseyFive_Entropy_LowMomentBudget`, `RamseyFive_Entropy_MarkedActualBudget`, `RamseyFive_Entropy_MeanTreeFailure`, `RamseyFive_Entropy_MetadataAlphabet`, `RamseyFive_Entropy_MetadataBudget`, `RamseyFive_Entropy_OrderedRetention`, `RamseyFive_Entropy_OrientedTreeCost`, `RamseyFive_Entropy_ReadyFailure`, `RamseyFive_Entropy_ReverseMessageCost`, `RamseyFive_Entropy_ScoreFiniteCost`, `RamseyFive_Entropy_SelectedRestriction`, `RamseyFive_Entropy_SubsetEncoding`, `RamseyFive_Entropy_Tail`, `RamseyFive_Entropy_TreeWeights`, `RamseyFive_Entropy_UniformCutoff`, `RamseyFive_Entropy_UniversalFreshCost`, `RamseyFive_Geometry_AmbientPairPublic`, `RamseyFive_Geometry_BaseFinitePublic`, `RamseyFive_Geometry_BasePublicFamily`, `RamseyFive_Geometry_ConcretePivot`, `RamseyFive_Geometry_DimensionFourHighLaw`, `RamseyFive_Geometry_DimensionFourLowAmbient`, `RamseyFive_Geometry_DimensionalScale`, `RamseyFive_Geometry_ExceptionalCenters`, `RamseyFive_Geometry_FiniteFamily`, `RamseyFive_Geometry_FiniteNode`, `RamseyFive_Geometry_FiniteTreeFailure`, `RamseyFive_Geometry_FlagGraph`, `RamseyFive_Geometry_FlatPoints`, `RamseyFive_Geometry_FlatSection`, `RamseyFive_Geometry_GeneralReversedCode`, `RamseyFive_Geometry_GeometryScaleOrientedLower`, `RamseyFive_Geometry_HighGeometryClosure`, `RamseyFive_Geometry_HighPairVariance`, `RamseyFive_Geometry_HighPolyConstant`, `RamseyFive_Geometry_HyperplaneHigh`, `RamseyFive_Geometry_IncidencesDegrees`, `RamseyFive_Geometry_LargeCells`, `RamseyFive_Geometry_LevelTargetBounds`, `RamseyFive_Geometry_LocalLines`, `RamseyFive_Geometry_MomentOrder`, `RamseyFive_Geometry_MomentPolynomialTail`, `RamseyFive_Geometry_OrderedTargetRetention`, `RamseyFive_Geometry_OrientedTreePotential`, `RamseyFive_Geometry_OriginalReadiness`, `RamseyFive_Geometry_Outside`, `RamseyFive_Geometry_OverlapDyads`, `RamseyFive_Geometry_OwnQuery`, `RamseyFive_Geometry_Peeling`, `RamseyFive_Geometry_PeelingGeometry`, `RamseyFive_Geometry_PencilCount`, `RamseyFive_Geometry_PlaneExceptions`, `RamseyFive_Geometry_PointStrength`, `RamseyFive_Geometry_ProjectiveExpectedLevelLoss`, `RamseyFive_Geometry_PublicDecoder`, `RamseyFive_Geometry_Q`, `RamseyFive_Geometry_RadialAlternatives`, `RamseyFive_Geometry_RadialOffException`, `RamseyFive_Geometry_ReversedBasePublic`, `RamseyFive_Geometry_RichHyperplaneVariance`, `RamseyFive_Geometry_SampledPoints`, `RamseyFive_Geometry_ScoreDegreeLowNormalized`, `RamseyFive_Geometry_ScoredMessage`, `RamseyFive_Geometry_SubspacePointsEquiv`, `RamseyFive_Geometry_SurvivorRank`, `RamseyFive_Geometry_TargetCaps`, `RamseyFive_Geometry_TargetRetention`, `RamseyFive_Geometry_ThreeBranch`, `RamseyFive_Geometry_ThreePublicDefs`, `RamseyFive_Geometry_TrainingLineCard`, `RamseyFive_Geometry_TreeFailure`, `RamseyFive_Geometry_TreeShape`, `RamseyFive_Geometry_TwoFinitePublic`, `RamseyFive_Iteration_CodedWindowStage`, `RamseyFive_Iteration_HighWindowStage`, `RamseyFive_Iteration_PolarIteration`, `RamseyFive_Iteration_Scale`, `RamseyFive_Iteration_StageState`, `RamseyFive_Iteration_TerminalStream`, `RamseyFive_Iteration_WindowStage`, `RamseyFive_Marking_AllHistoryWindowLoss`, `RamseyFive_Marking_BandEndpoints`, `RamseyFive_Marking_ChooseLevel`, `RamseyFive_Marking_ClassPrepared`, `RamseyFive_Marking_ClassifiedStream`, `RamseyFive_Marking_CompressionStage`, `RamseyFive_Marking_DomainTransport`, `RamseyFive_Marking_HighDomainEndpoints`, `RamseyFive_Marking_HighSampleRetention`, `RamseyFive_Marking_MarkedStreamExtraction`, `RamseyFive_Marking_MarkingClassDomains`, `RamseyFive_Marking_MarkingClasses`, `RamseyFive_Marking_MarkingEndpoints`, `RamseyFive_Marking_ReciprocalBands`, `RamseyFive_Marking_ReciprocalDomainCaps`, `RamseyFive_Marking_ReciprocalLevelProducer`, `RamseyFive_Marking_ReciprocalNumerics`, `RamseyFive_Marking_ReciprocalStageArithmetic`, `RamseyFive_Marking_ScanRecordPresent`, `RamseyFive_Marking_State`, `RamseyFive_Marking_SurvivingWindowCode`, `RamseyFive_Marking_TwoScan`, `RamseyFive_Marking_TwoScanContext`, `RamseyFive_Marking_WindowCodeDomains`, `RamseyFive_Marking_WindowDeletionCount`, `RamseyFive_Marking_WindowSmallFailure`, `RamseyFive_Marking_WindowTargetRetention`, `RamseyFive_Probability_Aggregate`, `RamseyFive_Probability_FailureCount`, `RamseyFive_Probability_MeasurePreservingSplitSchedule`, `RamseyFive_Probability_MeasurePublicTable`, `RamseyFive_Probability_OwnFraction`, `RamseyFive_Probability_PoissonProposal`, `RamseyFive_Probability_PublicCapLaw`, `RamseyFive_Probability_SumPoissonPow`, `RamseyFive_Streams_HighActualExtraction`, `RamseyFive_Streams_PreparedStream`, `RamseyFive_Streams_SelectedTuple`, `RamseyFive_Trees_AmbientEviction`, `RamseyFive_Trees_HistoryPrivateStream`, `RamseyFive_Trees_PivotPotential`, `RamseyFive_Trees_PivotTree`, `RamseyFive_Trees_ReachedFailure`, `RamseyFive_Trees_SurvivingWindows`, `RamseyFive_Trees_TargetTrims`, `RamseyFive_Trees_TreeDecoder`, `RamseyFive_Trees_TreeExposure`, `RamseyFive_Trees_TreeOrder`, `RamseyFive_Trees_TreeOriginalTrims`, `SharpRamsey_Entropy_AnchorEventsRealized`, `SharpRamsey_Entropy_CompleteProgramWeight`, `SharpRamsey_Entropy_ForcedHits`, `SharpRamsey_Entropy_IntegralTypicalScoreSq`, `SharpRamsey_Entropy_LabelledFilterCard`, `SharpRamsey_Entropy_NewEvents`, `SharpRamsey_Entropy_PoissonLaw`, `SharpRamsey_Entropy_ShiftKernelSum`, `SharpRamsey_Entropy_TwoAnchorCrossCost`, `SharpRamsey_Entropy_WitnessList`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ060R002` and `OAIQ060R003`; the statements `OAI.SharpRamseyFive.ParameterHierarchy.eventually_reciprocal_code_budget`, `OAI.SharpRamseyFive.ParameterHierarchy.eventually_reciprocal_packing`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_high_peel_exceptions`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_exceptions`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_half_exceptions`, `OAI.SharpRamseyFive.ScoreGeometry.hyperplanePeelExceptions_card` and `OAI.SharpRamseyFive.primeConstruction`; the proofs of `OAI.SharpRamseyFive.ParameterHierarchy.eventually_reciprocal_code_budget`, `OAI.SharpRamseyFive.ParameterHierarchy.eventually_reciprocal_packing`, `OAI.SharpRamseyFive.ProjectiveRichLines.quantitative_card_mul_le` and `OAI.SharpRamseyFive.main`.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ060_R5.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_SubspacePointsEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

open scoped LinearAlgebra.Projectivization
open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def subspacePointsEquiv (W : Submodule K V) :
    ℙ K W ≃ {p : ℙ K V // p.submodule ≤ W} := by
  let f : ℙ K W → {p : ℙ K V // p.submodule ≤ W} := fun p =>
    ⟨Projectivization.map W.subtype W.injective_subtype p, by
      induction p using Projectivization.ind with | h v hv =>
      rw [Projectivization.map_mk, Projectivization.submodule_mk,
        Submodule.span_singleton_le_iff_mem]
      exact v.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q hpq
    exact Projectivization.map_injective W.subtype W.injective_subtype
      (congrArg Subtype.val hpq)
  · intro p
    have hp : p.val.rep ∈ W := by
      apply p.property
      rw [Projectivization.submodule_eq]
      exact Submodule.mem_span_singleton_self _
    let v : W := ⟨p.val.rep, hp⟩
    have hv : v ≠ 0 := fun h => p.val.rep_nonzero (congrArg Subtype.val h)
    refine ⟨Projectivization.mk K v hv, ?_⟩
    apply Subtype.ext
    exact p.val.mk_rep

theorem card_subspacePoints [Finite K] (W : Submodule K V) :
    Nat.card {p : ℙ K V // p.submodule ≤ W} =
      ∑ i ∈ Finset.range (finrank K W), Nat.card K ^ i := by
  rw [← Nat.card_congr (subspacePointsEquiv W)]
  exact Projectivization.card_of_finrank K W rfl

lemma finrank_sup_points {a a' : ℙ K V} (haa : a ≠ a') :
    finrank K (a.submodule ⊔ a'.submodule : Submodule K V) = 2 := by
  have hli := Projectivization.independent_iff.mp
    ((Projectivization.independent_pair_iff_ne a a').mpr haa)
  have hr : Set.range (Projectivization.rep ∘ ![a, a']) = {a.rep, a'.rep} := by
    ext x
    simp only [Set.mem_range, Function.comp_apply, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have h := finrank_span_eq_card hli
  rw [hr, show ({a.rep, a'.rep} : Set V) = {a.rep} ∪ {a'.rep} by ext; simp [or_comm],
    Submodule.span_union, ← a.submodule_eq, ← a'.submodule_eq] at h
  simpa using h

open scoped Classical

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_Q
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
open scoped Classical
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

def Q (q d : ℕ) : ℕ := ∑ i ∈ Finset.range (d + 1), q ^ i

lemma Q_pos (q d : ℕ) : 0 < Q q d := by
  apply Finset.sum_pos'
  · intros; exact Nat.zero_le _
  · exact ⟨0, Finset.mem_range.mpr (by omega), by simp⟩

omit [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))] in
lemma card_points {d : ℕ} (hdim : finrank K V = d + 1) :
    Fintype.card (ℙ K V) = Q (Nat.card K) d := by
  rw [Fintype.card_eq_nat_card]
  exact Projectivization.card_of_finrank K V hdim

omit [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma card_hyperplanes {d : ℕ} (hdim : finrank K V = d + 1) :
    Fintype.card (ℙ K (Module.Dual K V)) = Q (Nat.card K) d := by
  rw [Fintype.card_eq_nat_card]
  exact Projectivization.card_of_finrank K (Module.Dual K V)
    (Subspace.dual_finrank_eq.trans hdim)

lemma Q_recurrence {q d : ℕ} (hd : 1 ≤ d) : Q q d = q * Q q (d-1) + 1 := by
  have he : d - 1 + 1 = d := by omega
  simp only [Q, he]
  exact geom_sum_succ

lemma density_lower {d : ℕ} (hd : 1 ≤ d) :
    1 / (2 * (Nat.card K : ℝ)) ≤
      (Q (Nat.card K) (d-1) : ℝ) / Q (Nat.card K) d := by
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hm : 0 < Q (Nat.card K) (d-1) := Q_pos _ _
  have hn : 0 < Q (Nat.card K) d := Q_pos _ _
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [one_mul, Q_recurrence hd]
  push_cast
  have hq' : (2 : ℝ) ≤ Nat.card K := by exact_mod_cast hq
  have hm' : (1 : ℝ) ≤ Q (Nat.card K) (d-1) := by exact_mod_cast hm
  nlinarith

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Bounds_DensityUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

lemma density_upper {d : ℕ} (hd : 1 ≤ d) :
    (Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d ≤ 1/(Nat.card K:ℝ) := by
  have hq : (0:ℝ) < Nat.card K := by exact_mod_cast (Finite.one_lt_card (α:=K)).le
  have hQ : (0:ℝ) < Q (Nat.card K) d := by exact_mod_cast Q_pos (Nat.card K) d
  have hrec : (Q (Nat.card K) d:ℝ)=Nat.card K*Q (Nat.card K) (d-1)+1 := by
    exact_mod_cast Q_recurrence (q:=Nat.card K) hd
  apply (div_le_div_iff₀ hQ hq).mpr
  nlinarith

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Bounds_PrimeConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Classical
open Finset
namespace SharpRamseyFive
open Filter SimpleGraph
open scoped Topology

def PrimeConstruction (η : ℝ) : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → q.Prime →
    ∃ G : SimpleGraph (Fin ⌊(q:ℝ)^4*Real.log q⌋₊),
      G.CliqueFree 5 ∧ Gᶜ.CliqueFree ⌊(q:ℝ)*(Real.log q)^(1+η)⌋₊

end SharpRamseyFive

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Best
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.GreedyTraining
open scoped BigOperators Classical
variable {V I : Type*} [DecidableEq V] [LinearOrder I]

omit [LinearOrder I] in
lemma maximizers_nonempty (F : Finset I) (hF : F.Nonempty) (shape : I → Finset V)
    (X : Finset V) :
    (F.filter fun a => ∀ b ∈ F, (X ∩ shape b).card ≤ (X ∩ shape a).card).Nonempty := by
  obtain ⟨a,ha,hm⟩ := Finset.exists_max_image F (fun a => (X ∩ shape a).card) hF
  exact ⟨a,Finset.mem_filter.mpr ⟨ha,hm⟩⟩

noncomputable def best (F : Finset I) (hF : F.Nonempty) (shape : I → Finset V)
    (X : Finset V) : I :=
  (F.filter fun a => ∀ b ∈ F, (X ∩ shape b).card ≤ (X ∩ shape a).card).min'
    (maximizers_nonempty F hF shape X)

noncomputable def remaining (F : Finset I) (hF : F.Nonempty) (shape : I → Finset V)
    (X : Finset V) : ℕ → Finset V
  | 0 => X
  | k+1 => remaining F hF shape X k \ shape (best F hF shape (remaining F hF shape X k))

noncomputable def chosen (F : Finset I) (hF : F.Nonempty) (shape : I → Finset V)
    (X : Finset V) (k : ℕ) : I := best F hF shape (remaining F hF shape X k)

noncomputable def cell (F : Finset I) (hF : F.Nonempty) (shape : I → Finset V)
    (X : Finset V) (k : ℕ) : Finset V :=
  remaining F hF shape X k ∩ shape (chosen F hF shape X k)

variable (F : Finset I) (hF : F.Nonempty) (shape : I → Finset V) (X : Finset V)

lemma cell_card_add_remaining (k : ℕ) :
    (cell F hF shape X k).card + (remaining F hF shape X (k+1)).card =
      (remaining F hF shape X k).card := by
  exact Finset.card_inter_add_card_sdiff _ _

lemma sum_card_add_remaining (k : ℕ) :
    (∑ j ∈ Finset.range k, (cell F hF shape X j).card) + (remaining F hF shape X k).card = X.card := by
  induction k with
  | zero => simp [remaining]
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hh := cell_card_add_remaining F hF shape X k
    omega

def Stop (threshold k : ℕ) : Prop :=
  X.card ≤ 2*(X.card-(remaining F hF shape X k).card) ∨
    (cell F hF shape X k).card < threshold

lemma exists_stop (threshold : ℕ) (hthreshold : 0 < threshold) :
    ∃ k ≤ X.card, Stop F hF shape X threshold k := by
  by_contra hn
  push Not at hn
  have hpos (j : ℕ) (hj : j ∈ Finset.range X.card) : 1 ≤ (cell F hF shape X j).card := by
    have hns := hn j (Nat.le_of_lt (Finset.mem_range.mp hj))
    simp only [Stop,not_or,not_lt] at hns
    omega
  have hs := Finset.sum_le_sum hpos
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at hs
  have hc := sum_card_add_remaining F hF shape X X.card
  have hnlast := hn X.card le_rfl
  apply hnlast
  left
  omega

noncomputable def stopIndex (threshold : ℕ) (hthreshold : 0 < threshold) : ℕ :=
  Nat.find (Exists.imp (fun _ hk => hk.2) (exists_stop F hF shape X threshold hthreshold))

noncomputable def retained (threshold : ℕ) (hthreshold : 0 < threshold) : Finset V :=
  if X.card ≤ 2*(X.card-(remaining F hF shape X (stopIndex F hF shape X threshold hthreshold)).card)
  then X \ remaining F hF shape X (stopIndex F hF shape X threshold hthreshold)
  else remaining F hF shape X (stopIndex F hF shape X threshold hthreshold)

noncomputable def headIndex (J cap : ℕ) : ℕ :=
  Nat.find (show ∃ k, J ≤ k ∨ (cell F hF shape X k).card ≤ cap from ⟨J,Or.inl le_rfl⟩)

noncomputable def firstAt (J : ℕ) (x : V) : ℕ :=
  Nat.find (show ∃ j, J ≤ j ∨ x ∈ shape (chosen F hF shape X j) from ⟨J,Or.inl le_rfl⟩)

noncomputable def ownCell (J : ℕ) (x : V) : Finset V :=
  if firstAt F hF shape X J x < J then cell F hF shape X (firstAt F hF shape X J x) else ∅

end SharpRamseyFive.GreedyTraining

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Beta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ParameterHierarchy
open Filter Asymptotics
open scoped Topology

def beta (η : ℝ) : ℝ := η / 10000000

def L (η σ D : ℝ) : ℝ := D * σ ^ (8 * beta η)
def P (η σ D R : ℝ) : ℝ := L η σ D * R

structure Range (η σ D R : ℝ) : Prop where
  dlo : σ ^ beta η ≤ D
  dhi : D ≤ σ ^ (1 - η/2)
  rlo : σ ^ beta η ≤ R
  rhi : R ≤ 2 * σ ^ beta η + 2

end SharpRamseyFive.ParameterHierarchy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_CoordinateMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.ScalarExtension
open scoped LinearAlgebra.Projectivization
variable {K L I : Type*} [Field K] [Field L] [Algebra K L]

def coordinateMap : (I → K) →ₛₗ[algebraMap K L] (I → L) where
  toFun v := algebraMap K L ∘ v
  map_add' u v := by ext i; simp
  map_smul' a v := by ext i; simp

end SharpRamseyFive.ScalarExtension

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_FinsetEquivPositions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive
open scoped Classical
noncomputable section
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
def equivPositions (e : A≃B) (S : Finset A) : Finset B := S.map e.toEmbedding
end
end SharpRamseyFive

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_ReverseCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ReverseCap
open scoped Classical BigOperators
variable {A B : Type*} [Fintype B]

noncomputable def neighbors (R : A→B→Prop) (a : A) : Finset B :=
  Finset.univ.filter (R a)

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Nonpairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SkewPairCounting
open scoped BigOperators
variable {I : Type*} [DecidableEq I]

def nonpairs (R : I → I → Prop) [DecidableRel R] (S : Finset I) : Finset (I × I) :=
  (S ×ˢ S).filter fun p => p.1 ≠ p.2 ∧ ¬R p.1 p.2

end SharpRamseyFive.SkewPairCounting

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ExceptionalCenters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.RichPlaneGeometry
open Module SharpRamseyFive.ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

noncomputable def dualOfHyperplane {d : ℕ} (hdim : finrank K V = d+1)
    (A : Submodule K V) (hA : finrank K A = d) : ℙ K (Module.Dual K V) :=
  Projectivization.mk'' A.dualAnnihilator (by
    have hh := Subspace.finrank_add_finrank_dualAnnihilator_eq A
    rw [hA,hdim] at hh
    omega)

end SharpRamseyFive.RichPlaneGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_RichHyperplaneVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.RichPlaneGeometry

open Module SharpRamseyFive.ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def pointsInSubspace (H : Submodule K V) (X : Finset (ℙ K V)) :
    Finset (ℙ K H) :=
  (X.subtype (fun p => p.submodule ≤ H)).map (subspacePointsEquiv H).symm.toEmbedding

end SharpRamseyFive.RichPlaneGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FlatPoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ProjectiveTraining
open Module RichPlaneGeometry GreedyTraining
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

noncomputable def flatPoints (A : Submodule K V) : Finset (ℙ K V) := by
  let : Finite V := Module.finite_of_finite K
  let : Fintype (ℙ K V) := Fintype.ofFinite _
  exact Finset.univ.filter fun x => x.submodule ≤ A

variable {I : Type*} [LinearOrder I]
  (F : Finset I) (hF : F.Nonempty) (P : I → Submodule K V) (X : Finset (ℙ K V))

noncomputable def cellRichLines (L : Finset (Submodule K V)) (j M : ℕ) :
    Finset (Submodule K V) :=
  L.filter fun A => A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j) ∧
    M ≤ ((cell F hF (fun i => flatPoints (P i)) X j).filter fun y => y.submodule ≤ A).card

noncomputable def capturedLineCenters (J M : ℕ) (A : Submodule K V) :
    Finset (ℙ K V) :=
  (flatPoints A).filter fun x => M ≤
    (((X \ remaining F hF (fun i => flatPoints (P i)) X J) \
      ownCell F hF (fun i => flatPoints (P i)) X J x).filter fun y => y.submodule ≤ A).card

end SharpRamseyFive.ProjectiveTraining

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_RichCenters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.GlobalRadial
open Module ProjectiveTraining GreedyTraining
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

noncomputable def richCenters (S : Finset (ℙ K V))
    (O : ℙ K V → Finset (ℙ K V)) (δ a : ℝ) (A : Submodule K V) : Finset (ℙ K V) :=
  (flatPoints A).filter fun x => a ≤ δ*((S \ (O x ∪ {x})).filter
    fun y => y.submodule ≤ A).card

end SharpRamseyFive.GlobalRadial

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_OffFiberPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.NondominantOverlap
open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical

section Finite
variable {I D : Type*} [DecidableEq I] [DecidableEq D]
noncomputable def offFiberPairs (f : I → D) (X : Finset I) : Finset (I × I) :=
  (X ×ˢ X).filter fun p => f p.1 ≠ f p.2

end Finite

end SharpRamseyFive.NondominantOverlap

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_PoissonLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.StaticCertificates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def poissonLaw (rate : ι → ℝ≥0) : Measure (ι → ℕ) :=
  Measure.pi (fun i => poissonMeasure (rate i))

instance flat_HighMomentRecovered_3 (rate : ι → ℝ≥0) : IsProbabilityMeasure (poissonLaw rate) := by
  unfold poissonLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def positiveEvent (C : Finset ι) : Set (ι → ℕ) :=
  (C : Set ι).pi (fun _ => ({0} : Set ℕ)ᶜ)

noncomputable def certificateIndicator (C : Finset ι) (ω : ι → ℕ) : ℝ :=
  (positiveEvent C).indicator (fun _ => 1) ω

noncomputable def weight (rate : ι → ℝ≥0) (C : Finset ι) : ℝ :=
  ∏ i ∈ C, (rate i : ℝ)

end SharpRamseyFive.StaticCertificates
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_TwoAnchorCrossCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

open scoped BigOperators

namespace SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.StaticCertificates
open scoped BigOperators NNReal

variable {V H D B : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B]

variable (lines : H → Finset D)

noncomputable def pairMoment (rate : D → ℝ≥0) (K : ℕ) : ℝ :=
  ∑ h : H, ∑ h' : {h' : H // h' ≠ h},
    ((Fintype.card B : ℝ) * ∑ d ∈ lines h ∩ lines h'.val, (rate d : ℝ)) ^ K

end SharpRamseyFive.WeightedPrograms
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_NewEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
namespace SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.StaticCertificates
open scoped BigOperators NNReal
variable {V H D B : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B]
variable (lines : H → Finset D)

noncomputable def uniformAnchorBudget (K : ℕ) (mass : ℝ) : ℝ :=
  K * Fintype.card V + Fintype.card B * mass

noncomputable def branchingBound (rate : D → ℝ≥0) (denom b mass : ℝ)
    (K N₁ N₂ : ℕ) (low : Bool) : ℝ :=
  ((Fintype.card V : ℝ) * Fintype.card H / denom) / b ^ 8 +
    (if low then Fintype.card V ^ 2 * (N₁ : ℝ) *
      uniformAnchorBudget (V := V) (B := B) K mass / denom else 0) +
    (Fintype.card V ^ 3 * (N₂ : ℝ) *
      uniformAnchorBudget (V := V) (B := B) K mass ^ 2 / denom) * b +
    Fintype.card V ^ 2 * pairMoment (B := B) lines rate K / denom ^ 2

end SharpRamseyFive.WeightedPrograms

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpRamseyFive.ResidualCertificate

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def rootProbability : unitInterval := ⟨1 / 20, by norm_num⟩

noncomputable def rootMeasure : Measure (V → Bool) :=
  Measure.pi (fun _ => bernoulliMeasure true false rootProbability)

instance flat_HighMomentRecovered_6 : IsProbabilityMeasure (rootMeasure (V := V)) := by
  unfold rootMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def selected (ω : V → Bool) : Finset V :=
  Finset.univ.filter (fun v => ω v = true)

def voidEvent (W : Finset V) : Set (V → Bool) :=
  (W : Set V).pi (fun _ => {false})

noncomputable def voidIndicator (W : Finset V) (ω : V → Bool) : ℝ :=
  (voidEvent W).indicator (fun _ => 1) ω

noncomputable def badIndicator (W : Finset V) (ω : V → Bool) : ℝ :=
  if (W ∩ selected ω).card < 2 then 1 else 0

end SharpRamseyFive.ResidualCertificate
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_WitnessList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.ResidualCertificate
variable {V : Type*} [Fintype V] [DecidableEq V]

section SharedHitGeometry

open scoped Classical

variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

noncomputable def batchesOn (hit : B → D → Prop) (T : Finset D) : Finset B :=
  T.biUnion (fun d => Finset.univ.filter (fun r => hit r d))

end SharedHitGeometry
end SharpRamseyFive.ResidualCertificate
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_AnchorEventsRealized
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.ResidualCertificate
variable {V : Type*} [Fintype V] [DecidableEq V]
section SharedHitGeometry
open scoped Classical
variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

noncomputable def pairEvents (T : Finset B) (d : T → D) : Finset (B × D) :=
  T.attach.image (fun r => (r.val, d r))

end SharedHitGeometry

end SharpRamseyFive.ResidualCertificate

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_IntegralTypicalScoreSq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*}

def untouchedBatches {R : ℕ} (touched : Fin R → Bool) : Finset (Fin R) :=
  Finset.univ.filter (fun r => touched r = false)

end SharpRamseyFive.PoissonScore
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_ForcedHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*}

def hitBatches {R : ℕ} (i : ι) (ω : Fin R → ι → ℕ) : Finset (Fin R) :=
  Finset.univ.filter (fun r => ω r i ≠ 0)

def overloaded {R : ℕ} (s : Finset ι) (J : ℕ) : Set (Fin R → ι → ℕ) :=
  {ω | ∃ i ∈ s, J ≤ (hitBatches i ω).card}

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

noncomputable def partitionEquiv (label : ι → κ) :
    (ι → ℕ) ≃ᵐ (∀ c : κ, {i : ι // label i = c} → ℕ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : ι => ℕ) (Equiv.sigmaFiberEquiv label)).symm.trans
    (MeasurableEquiv.piCurry (fun (c : κ) (_ : {i : ι // label i = c}) => ℕ))

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
@[simp] lemma partitionEquiv_apply (label : ι → κ) (ω : ι → ℕ) (c : κ)
    (i : {i : ι // label i = c}) : partitionEquiv label ω c i = ω i := rfl

noncomputable def externalEquiv (label : ι → Option κ) :
    (ι → ℕ) ≃ᵐ ((∀ c : κ, {i : ι // label i = some c} → ℕ) ×
      ({i : ι // label i = none} → ℕ)) :=
  (partitionEquiv label).trans (MeasurableEquiv.piOptionEquivProd
    (fun c : Option κ => {i : ι // label i = c} → ℕ))
end SharpRamseyFive.PoissonScore
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_CompleteProgramWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpRamseyFive.SelectionBridge
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore
open SharpRamseyFive.WeightedPrograms
open Classical
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]

def labelled (f : V → H) (v : V) : H × V := (f v, v)

end SharpRamseyFive.SelectionBridge
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_LabelledFilterCard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpRamseyFive.ResidualElimination
open scoped BigOperators
open Classical
variable {V H : Type} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

def Agrees (E : Finset V) (g f : V → H) : Prop := ∀ v ∉ E, f v = g v

noncomputable def completionSum (E : Finset V) (g : V → H) (F : (V → H) → ℝ) : ℝ :=
  ∑ f : V → H, if Agrees E g f then F f else 0

noncomputable def term (a : V → (V → H) → ℝ) (B : Finset V → (V → H) → ℝ)
    (E S : Finset V) (f : V → H) : ℝ := (∏ u ∈ S, a u f) * B (E \ S) f

end SharpRamseyFive.ResidualElimination

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_ShiftKernelSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpRamseyFive.WeightedPrograms

open scoped BigOperators

variable {V H D B I : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B] [DecidableEq I]

variable (lines : H → Finset D)

def DistinctPairs (H : Type*) := Σ h : H, {h' : H // h' ≠ h}

instance flat_HighMomentRecovered_7 : Fintype (DistinctPairs H) := by unfold DistinctPairs; infer_instance

noncomputable def strength (a : D → ℝ≥0) (p : DistinctPairs H) : ℝ :=
  ∑ d ∈ lines p.1 ∩ lines p.2.val, (a d : ℝ)

end SharpRamseyFive.WeightedPrograms

namespace SharpRamseyFive.ResidualElimination
open scoped BigOperators
open Classical
variable {V H : Type} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

noncomputable def patch (g : V → H) (T : Finset V) (x : T → H) : V → H :=
  fun u => if hu : u ∈ T then x ⟨u,hu⟩ else g u

end SharpRamseyFive.ResidualElimination
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_Outside
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable (x : ℙ K V)

noncomputable def outsideAt (S O : Finset (ℙ K V)) :
    Finset {y : ℙ K V // x ≠ y} := (S \ O).subtype (fun y => x ≠ y)

end
open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_LocalLines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.GlobalRadial
open Module ProjectiveTraining GreedyTraining
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

noncomputable def localLines (S : Finset (ℙ K V)) (O : ℙ K V → Finset (ℙ K V))
    (δ a : ℝ) (L : Finset (Submodule K V)) (x : ℙ K V) :=
  L.filter fun A => x ∈ richCenters S O δ a A

noncomputable def badCenters (S : Finset (ℙ K V)) (O : ℙ K V → Finset (ℙ K V))
    (δ a : ℝ) (L : Finset (Submodule K V)) (Q : Finset (ℙ K V)) (D : ℝ) :=
  Q.filter fun x => D ≤ ((localLines S O δ a L x).card:ℝ)

end SharpRamseyFive.GlobalRadial

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_Aggregate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {D : Type*} [Fintype D] [DecidableEq D]

noncomputable def aggregate (label : ι→D) (ω : ι→ℕ) (d : D) : ℕ :=
  ∑ i : {i // label i=d},ω i

noncomputable def aggregateRate (label : ι→D) (rate : ι→ℝ≥0) (d : D) : ℝ≥0 :=
  ∑ i : {i // label i=d},rate i

end

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_Scale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreRegularity
open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def scale (d : ℕ) (n : ℝ) : ℝ := (Nat.card K:ℝ)^d/n

def familyCell {J : Type*} (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V)) :
    Option J→Finset (ℙ K V) | none => S | some j => C j

noncomputable def threshold {J : Type*} : Option J→ℝ | none => 1/10 | some _ => 1/50

end SharpRamseyFive.ScoreRegularity

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_OwnFraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreRegularity

section
open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable [Finite K] [Fintype (ℙ K (Dual K V))]

noncomputable def ownFraction (S A B : Finset (ℙ K V)) : ℝ :=
  ((A∪B).card:ℝ)/(S.card:ℝ)

end

open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical

end SharpRamseyFive.ScoreRegularity

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PointStrength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*}
  [Field K]
  [AddCommGroup V]
  [Module K V]
  [Finite K]
  [FiniteDimensional K V]
  [Fintype (ℙ K V)]
  [Fintype (ℙ K (Dual K V))]
  (x : ℙ K V)

noncomputable def pointStrength (S : Finset (ℙ K V)) : ℝ≥0 :=
  (Nat.card K:ℝ≥0)/S.card

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_MeasurePreservingSplitSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SharpRamseyFive.ScoreAcceptance
open scoped BigOperators Classical
variable {V H : Type*} [DecidableEq V] [DecidableEq H]

noncomputable def accepted (U sampled : Finset V) (A : V → ℝ) (threshold : ℝ) :=
  U.filter fun x => x∈sampled ∨ A x<threshold

end SharpRamseyFive.ScoreAcceptance

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_OwnQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]

def ownQuery (x : ℙ K V) (S O : Finset (ℙ K V)) (y : S) : Prop :=
  y.val∈O ∨ x=y.val

noncomputable def outsideEquiv (x : ℙ K V) (S O : Finset (ℙ K V)) :
    {y : S // ¬ownQuery x S O y} ≃ outsideAt x S O where
  toFun y := ⟨⟨y.val.val,(not_or.mp y.property).2⟩,
    Finset.mem_subtype.mpr (Finset.mem_sdiff.mpr ⟨y.val.property,(not_or.mp y.property).1⟩)⟩
  invFun y := ⟨⟨y.val.val,(Finset.mem_sdiff.mp (Finset.mem_subtype.mp y.property)).1⟩,
    not_or.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_subtype.mp y.property)).2,y.val.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

end

open Module ProjectiveIncidence ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]

def Unsampled (x : ℙ K V) (S : Finset (ℙ K V)) {R : ℕ} (ω : Fin R→S→ℕ) : Prop :=
  ∀r y,x=y.val → ω r y=0

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PencilCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

open Module ProjectiveIncidence ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]

noncomputable def ownSupport (S O : Finset (ℙ K V)) : Finset S :=
  Finset.univ.filter fun y => y.val∈O

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_SumPoissonPow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def sampleCount {R : ℕ} (ω : Fin R→ι→ℕ) : ℕ := ∑r,∑i,ω r i

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_SampledPoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def sampledPoints (S : Finset (ℙ K V)) {R : ℕ} (ω : Fin R→S→ℕ) : Finset (ℙ K V) :=
  S.filter fun x => ¬Unsampled x S ω

end

open Module ProjectiveIncidence ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore ScoreAcceptance
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_MeasurePublicTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.MeasurePublicTable
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
variable {α : Type*}

noncomputable def firstIndex (E : Set α) {N : ℕ} (t : Fin N→α) : Option (Fin N) :=
  if h : (Finset.univ.filter (fun i=>t i∈E)).Nonempty then
    some ((Finset.univ.filter (fun i=>t i∈E)).min' h) else none

end SharpRamseyFive.MeasurePublicTable

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_PoissonProposal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.PoissonScore

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def ambientSuccess (H : Finset ι) {R : ℕ} (E : Set (Fin R→H→ℕ)) : Set (Fin R→ι→ℕ) :=
  {ω | (∀r i,i∉H → ω r i=0) ∧ (fun r (i : H)=>ω r i)∈E}

end

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PublicDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore ScoreAcceptance
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def publicSamples (U : Finset (ℙ K V)) {R : ℕ}
    (ω : Fin R→ℙ K V→ℕ) : Finset (ℙ K V) :=
  U.filter fun x=>∃r,ω r x≠0

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_UniformCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore ScoreAcceptance MeasurePublicTable
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def scoreSearchCost (S U : Finset (ℙ K V)) (P τ : ℝ) : ℝ :=
  Real.log ((U.card:ℝ)/S.card)*(2*(Nat.card K:ℝ)*P)+(8*P*τ+Real.log 4)

noncomputable def scoreCutoff (S U : Finset (ℙ K V)) (P τ : ℝ) : ℕ :=
  ⌈(Nat.card K:ℝ)*Real.exp (scoreSearchCost S U P τ)⌉₊

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_PublicCapLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ReverseCap
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

def ValidCap (S U : Finset A) (M : ℝ) (Y : Finset A) : Prop :=
  Y⊆U ∧ (Y.card:ℝ)≤M ∧ (9:ℝ)/10*S.card≤(S∩Y).card

omit [Fintype A] in
lemma ValidCap.source_nonempty {S U Y : Finset A} {M : ℝ}
    (h : ValidCap S U M Y) (hS : S.Nonempty) : (S∩Y).Nonempty := by
  apply Finset.card_pos.mp
  have hs : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hh := h.2.2
  have : (0:ℝ)<(S∩Y).card := lt_of_lt_of_le (by positivity) hh
  exact_mod_cast this

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_ProducedCapExclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ReverseCap
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

def Excludes (a : A) : Option (Finset A)→Prop
  | none => False
  | some Y => a∉Y

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_FreshPublicFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ReverseCap
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

noncomputable def cardCutoff (q : ℝ) (m w n : ℕ) : ℕ :=
  ⌈q/((9:ℝ)/10*((m:ℝ)/w)^n)⌉₊

abbrev FreshTape (W : Finset B) (n : ℕ) (q : ℝ) :=
  (m : Fin (W.card+1))→Fin (cardCutoff q m W.card n)→Fin n→B

abbrev FreshMessage (W : Finset B) (n : ℕ) (q : ℝ) :=
  (m : Fin (W.card+1))×Fin (cardCutoff q m W.card n)

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Training
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.GreedyTraining
open scoped BigOperators Classical
variable {A I : Type*} [DecidableEq A] [LinearOrder I]

def Captured (F : Finset I) (hF : F.Nonempty) (shape : I→Finset A)
    (X : Finset A) (k : ℕ) (hk : 0<k) : Prop :=
  X.card≤2*(X.card-(remaining F hF shape X (stopIndex F hF shape X k hk)).card)

noncomputable def peelSet (enabled : Prop) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (k : ℕ) (hk : 0<k) : Finset A :=
  if enabled then retained F hF shape X k hk else X

noncomputable def peelLength (enabled : Prop) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (k : ℕ) (hk : 0<k) : ℕ :=
  if enabled ∧ Captured F hF shape X k hk then stopIndex F hF shape X k hk else 0

noncomputable def clippedPart (S : Finset A) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (J : ℕ) : Option (Fin J)→Finset A
  | none => ∅
  | some i => S∩cell F hF shape X i

noncomputable def queryPart (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (J : ℕ) (x : A) : Option (Fin J) :=
  if h : firstAt F hF shape X J x<J then some ⟨firstAt F hF shape X J x,h⟩ else none

end SharpRamseyFive.GreedyTraining

namespace SharpRamseyFive.TrainingCells
open scoped BigOperators Classical
variable {A H P : Type*} [DecidableEq A] [Fintype H] [Fintype P]

noncomputable def family (C : H→Finset A) (D : P→Finset A) : H⊕P⊕(H×P)→Finset A
  | Sum.inl i => C i
  | Sum.inr (Sum.inl j) => D j
  | Sum.inr (Sum.inr ij) => C ij.1∩D ij.2

end SharpRamseyFive.TrainingCells

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_PublicTraining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.GreedyTraining

section
open MeasurePublicTable
open scoped BigOperators Classical
variable {A I : Type*} [DecidableEq A] [LinearOrder I]

noncomputable def publicRegion {J : ℕ} (L : Fin J→Finset A) (i : Fin J) : Finset A :=
  (L i).filter fun x=>∀ j : Fin J, j < i → x ∉ L j

noncomputable def publicOwn {J : ℕ} (L : Fin J→Finset A) (x : A) : Finset A :=
  match firstIndex {B | x∈B} L with
  | none => ∅
  | some i => publicRegion L i

noncomputable def greedyList (F : Finset I) (hF : F.Nonempty) (shape : I→Finset A)
    (X : Finset A) (J : ℕ) : Fin J→Finset A := fun i=>shape (chosen F hF shape X i)

end

open TrainingCells
open scoped Classical BigOperators
variable {A I J : Type*} [DecidableEq A] [LinearOrder I] [LinearOrder J]

noncomputable def twoPublicOwn {h p : ℕ} (LH : Fin h→Finset A) (LP : Fin p→Finset A)
    (x : A) : Finset A := publicOwn LH x∪publicOwn LP x

end SharpRamseyFive.GreedyTraining

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Threshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.HighParameters
open scoped BigOperators

noncomputable def threshold (q n a : ℝ) : ℕ := ⌊n*a/(64*q)⌋₊
noncomputable def cap (q a : ℝ) : ℕ := ⌈1024*q^2/a⌉₊
noncomputable def multiplicity (q n a : ℝ) : ℕ := ⌈134217728*q^6/(n^2*a^3)⌉₊
noncomputable def degree (q n a χ : ℝ) : ℕ := ⌈34359738368*q^6/(n^2*a^4)*Real.exp χ⌉₊

end SharpRamseyFive.HighParameters

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_LargeCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ProjectiveTraining
open Module RichPlaneGeometry GreedyTraining
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]
variable {I : Type*} [LinearOrder I]
  (F : Finset I) (hF : F.Nonempty) (P : I → Submodule K V) (X : Finset (ℙ K V))

noncomputable def largeCells (J : ℕ) (c : ℝ) : Finset ℕ :=
  (Finset.range J).filter fun j => c ≤ (cell F hF (fun i => flatPoints (P i)) X j).card

noncomputable def largeCellIntersections (J : ℕ) (c : ℝ) : Finset (ℙ K V) :=
  ((largeCells F hF P X J c) ×ˢ (largeCells F hF P X J c)).biUnion fun ij =>
    if ij.1 = ij.2 then ∅ else
    flatPoints (P (chosen F hF (fun i => flatPoints (P i)) X ij.1)) ∩
    flatPoints (P (chosen F hF (fun i => flatPoints (P i)) X ij.2))

noncomputable def headPlaneCenters (J H M : ℕ) (c : ℝ) (A : Submodule K V) : Finset (ℙ K V) :=
  (flatPoints A).filter fun x =>
    (∃ j < H, A ≤ P (chosen F hF (fun i => flatPoints (P i)) X j)) ∧
    2*M ≤ ((X \ ownCell F hF (fun i => flatPoints (P i)) X J x).filter fun y => y.submodule ≤ A).card ∧
    x ∉ largeCellIntersections F hF P X H c

end SharpRamseyFive.ProjectiveTraining

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_Tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.HighPlaneBudget

section
open Module GreedyTraining ProjectiveTraining RichPlaneGeometry
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]
  {I : Type*} [LinearOrder I]
  (F : Finset I) (hF : F.Nonempty) (P : I → Submodule K V) (X : Finset (ℙ K V))

noncomputable def tail (J cap : ℕ) : Finset (ℙ K V) :=
  remaining F hF (fun i => flatPoints (P i)) X (headIndex F hF (fun i => flatPoints (P i)) X J cap) \
    remaining F hF (fun i => flatPoints (P i)) X J

noncomputable def tailPlanes (L : Finset (Submodule K V)) (J cap M : ℕ) :=
  L.filter fun A => M ≤ ((tail F hF P X J cap).filter fun x => x.submodule ≤ A).card

noncomputable def headAt (L : Finset (Submodule K V)) (J cap M : ℕ) (c : ℝ) (x : ℙ K V) :=
  L.filter fun A => x ∈ headPlaneCenters F hF P X J
    (headIndex F hF (fun i => flatPoints (P i)) X J cap) M c A

noncomputable def richAt (L : Finset (Submodule K V)) (J M : ℕ) (x : ℙ K V) :=
  L.filter fun A => x.submodule ≤ A ∧ 2*M ≤
    (((X \ remaining F hF (fun i => flatPoints (P i)) X J) \
      ownCell F hF (fun i => flatPoints (P i)) X J x).filter fun y => y.submodule ≤ A).card

end

open Module GreedyTraining ProjectiveTraining RichPlaneGeometry
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]
  {I : Type*} [LinearOrder I]
  (F : Finset I) (hF : F.Nonempty) (P : I → Submodule K V) (X : Finset (ℙ K V))

noncomputable def capturedPairs (G : Finset (Submodule K V)) (J M : ℕ) (x : ℙ K V) :=
  (G ×ˢ G).filter fun p => p.1 ≠ p.2 ∧ 2*M ≤
    (((X \ remaining F hF (fun i => flatPoints (P i)) X J) \
      ownCell F hF (fun i => flatPoints (P i)) X J x).filter fun y => y.submodule ≤ p.1 ⊓ p.2).card

end SharpRamseyFive.HighPlaneBudget

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_HighExceptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.HighPlaneBudget

section
open Module GreedyTraining ProjectiveTraining HighParameters
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]
  {I : Type*} [LinearOrder I]
  (F : Finset I) (hF : F.Nonempty) (P : I → Submodule K V) (X : Finset (ℙ K V))

noncomputable def highExceptions (L : Finset (Submodule K V)) (J : ℕ)
    (a χ : ℝ) (Y : Finset (ℙ K V)) : Finset (ℙ K V) :=
  let q : ℝ := Nat.card K
  let n : ℝ := X.card
  let M := threshold q n a
  let C := HighParameters.cap q a
  let D := degree q n a χ
  largeCellIntersections F hF P X (headIndex F hF (fun i => flatPoints (P i)) X J C) (n*a/1024) ∪
  (Y.filter fun x => D ≤ (headAt F hF P X L J C M (n*a/1024) x).card) ∪
  (Y.filter fun x => D ≤ ((tailPlanes F hF P X L J C M).filter fun A => x.submodule ≤ A).card)

end

open Module RichPlaneGeometry HighParameters
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

noncomputable def residualPlanes (L : Finset (Submodule K V))
    (X : Finset (ℙ K V)) (M : ℕ) :=
  L.filter fun A => M ≤ (X.filter fun x => x.submodule ≤ A).card

noncomputable def residualExceptions (L : Finset (Submodule K V))
    (X Y : Finset (ℙ K V)) (a χ : ℝ) :=
  Y.filter fun x => degree (Nat.card K) X.card a χ ≤
    ((residualPlanes L X (threshold (Nat.card K) X.card a)).filter fun A => x.submodule≤A).card

noncomputable def residualPairs (G : Finset (Submodule K V))
    (X : Finset (ℙ K V)) (M : ℕ) :=
  (G ×ˢ G).filter fun p => p.1 ≠ p.2 ∧ M≤(X.filter fun y => y.submodule≤p.1⊓p.2).card

end SharpRamseyFive.HighPlaneBudget

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_OverlapDyads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type}
  [Field K]
  [AddCommGroup V]
  [Module K V]
  [FiniteDimensional K V]
  [Finite K]
  (x : ℙ K V)

noncomputable def overlapDyads (X : Finset {y : ℙ K V // x≠y}) : Finset ℕ :=
  Finset.range (Nat.clog 2 X.card+1)

end

open Module ProjectiveIncidence PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_MomentPolynomialTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type}
  [Field K]
  [AddCommGroup V]
  [Module K V]
  [FiniteDimensional K V]
  [Finite K]
  (x : ℙ K V)

noncomputable def boundedOverlapDyads (X : Finset {y : ℙ K V // x≠y})
    (δ : ℝ≥0) (m : ℝ) : Finset ℕ :=
  (overlapDyads x X).filter fun i => (δ:ℝ)*2^i ≤ m

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_RadialAlternatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

noncomputable def strengthDyads (m : ℕ) (δ : ℝ≥0) : Finset ℕ :=
  (Finset.range (Nat.clog 2 m+1)).filter fun i => (δ:ℝ)*2^i≤2

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

noncomputable def radialExceptions (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)) (q n χ : ℝ) :=
  (strengthDyads S.card δ).biUnion fun i =>
    badCenters S O δ (((δ:ℝ)*2^i)/2) Lines Q (q^4/n^2*Real.exp χ/(((δ:ℝ)*2^i)/2)^100)

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PeelingGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining HighPlaneBudget
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]
  {I : Type} [LinearOrder I]

noncomputable def highPlaneExceptions (F : Finset I) (hF : F.Nonempty)
    (Flat : I→Submodule K V) (X S : Finset (ℙ K V)) (Planes : Finset (Submodule K V))
    (j : ℕ) (δ : ℝ≥0) (χ : ℝ) (Q : Finset (ℙ K V)) : Finset (ℙ K V) :=
  (strengthDyads S.card δ).biUnion fun i =>
    if (Nat.card K:ℝ)^2<(X.card:ℝ)*((δ:ℝ)*2^i)^99
    then highExceptions F hF Flat X Planes j ((δ:ℝ)*2^i) χ Q else ∅

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ScoreDegreeLowNormalized
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

open Module ProjectiveIncidence PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

noncomputable def certificateMajorant (Q M B b L : ℝ) (p R k N₁ N₂ : ℕ) : ℝ :=
  B*(1+(((p:ℝ)*(Q*p)/B)/b^8+
    (p:ℝ)^2*(N₁*p)*((k:ℝ)*p+R*(2*L))/B+
    ((p:ℝ)^3*(N₂*p)*((k:ℝ)*p+R*(2*L))^2/B)*b+
    (p:ℝ)^2*((p:ℝ)^2*((R*L)^k*M+Q*(R*(2*L))^k))/B^2))

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_LowMomentBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

noncomputable def lowMomentBudget (Q M A B b L : ℝ) (p R N₁ N₂ : ℕ) : ℝ :=
  certificateMajorant Q M B b L p R 200 N₁ N₂ +
    (1+(p:ℝ)^200*A)+B+(Q/B+(p:ℝ)^200*(M/B))

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_RadialOffException
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

noncomputable def geometryScale (q : ℕ) (n : ℝ) : ℝ := (q:ℝ)^4/n
noncomputable def dyadFactor (m : ℕ) (χ : ℝ) : ℝ := 2^200*(Nat.clog 2 m+1)*Real.exp (2*χ)
def pencilAlphabet (q k : ℕ) : ℕ := ∑ i∈Finset.range k,q^i

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_TrainingLineCard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

open Module ProjectiveIncidence PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

noncomputable def highCertificateMajorant (Q M B b L : ℝ) (p R k N₂ : ℕ) : ℝ :=
  B*(1+(((p:ℝ)*(Q*p)/B)/b^8+
    ((p:ℝ)^3*(N₂*p)*((k:ℝ)*p+R*(2*L))^2/B)*b+
    (p:ℝ)^2*((p:ℝ)^2*((R*L)^k*M+Q*(R*(2*L))^k))/B^2))

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_HighMomentBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

noncomputable def highMomentBudget (Q M A B b L : ℝ) (p R N₂ : ℕ) : ℝ :=
  highCertificateMajorant Q M B b L p R 200 N₂ +
    (1+(p:ℝ)^200*A)+B+(Q/B+(p:ℝ)^200*(M/B))

end

open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

noncomputable def pencilHighBudget (q m : ℕ) (n χ b L : ℝ) (p R : ℕ) : ℝ :=
  highMomentBudget (pencilAlphabet q 4) (dyadFactor m χ*(geometryScale q n)^2)
    (dyadFactor m χ*geometryScale q n) (geometryScale q n) b L p R
      (pencilAlphabet q 2)

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_HighBudgetPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry
open scoped BigOperators

noncomputable def highBudgetPoly (a p P : ℝ) : ℝ :=
  3+40*p^2+20*p^4*(200*p+2*P)^2+
    p^4*(P^200*a+400*(2*P)^200)+2*p^200*a+400

end SharpRamseyFive.ScoreGeometry

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_HighPolyConstant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry
open Filter ParameterHierarchy
open scoped Topology

noncomputable def highPolyConstant (k c : ℝ) : ℝ :=
  403+40*k^2+20*k^4*(200*k+2)^2+k^4*(c+400*2^(200:ℕ))+2*k^200*c

end SharpRamseyFive.ScoreGeometry

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_LowBudgetPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry
open scoped BigOperators

noncomputable def lowBudgetPoly (a s p P : ℝ) : ℝ :=
  highBudgetPoly a p P+s*p^3*(200*p+2*P)

open Filter Asymptotics ParameterHierarchy
open scoped Topology

end SharpRamseyFive.ScoreGeometry

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_MomentOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry

section
open Filter Asymptotics ParameterHierarchy
open scoped Topology

noncomputable def momentOrder (σ P : ℝ) : ℕ := 2*⌈5000*σ/P⌉₊
noncomputable def residualOrder (σ : ℝ) : ℕ := ⌈1000*Real.log σ⌉₊+1

end

open Filter ParameterHierarchy
open scoped Topology

noncomputable def localTruncConstant : ℝ := 24*2^(200:ℕ)*8^(4900:ℕ)

end SharpRamseyFive.ScoreGeometry

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_DimensionalScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry

section
open scoped BigOperators

noncomputable def dimensionalScale (q d : ℕ) (n : ℝ) : ℝ := (q:ℝ)^d/n

end

open Filter ParameterHierarchy
open scoped Topology

end SharpRamseyFive.ScoreGeometry

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_FailureCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
variable {Ω X : Type*} [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]

noncomputable def failureCount (U : Finset X) (P : X→Ω→Prop) (ω : Ω) : ℝ :=
  (U.filter fun x => P x ω).card

end

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_Peeling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining HighPlaneBudget
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

noncomputable def residualPlaneExceptions (Planes : Finset (Submodule K V))
    (X S Q : Finset (ℙ K V)) (δ : ℝ≥0) (χ : ℝ) : Finset (ℙ K V) :=
  (strengthDyads S.card δ).biUnion fun i =>
    if (Nat.card K:ℝ)^2<(X.card:ℝ)*((δ:ℝ)*2^i)^99
    then residualExceptions Planes X Q ((δ:ℝ)*2^i) χ else ∅

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PlaneExceptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open ParameterHierarchy Filter
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

noncomputable def ambientStrongExceptions {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [Finite K] [FiniteDimensional K V]
    (σ P : ℝ) (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)) : Finset (ℙ K V) :=
  if (S.card:ℝ)≤(Nat.card K:ℝ)^2*Real.exp (-4*P) then ∅
  else badCenters S O (pointStrength S) (1/(100*(momentOrder σ P:ℝ))) Lines Q 1

end

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_FreshPublicValidation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ReverseCap

open scoped Classical
variable {A : Type*} [Fintype A]

def CaptureBound (T U : Finset A) (c M : ℝ) (W : Finset A) : Prop :=
  W⊆U ∧ (W.card:ℝ)≤M ∧ c*T.card≤(T∩W).card

omit [Fintype A] in
lemma CaptureBound.nonempty {T U W : Finset A} {c M : ℝ}
    (h : CaptureBound T U c M W) (hT : T.Nonempty) (hc : 0 < c) :
    (T∩W).Nonempty := by
  apply Finset.card_pos.mp
  have ht : (0:ℝ)<T.card := by exact_mod_cast hT.card_pos
  exact_mod_cast (lt_of_lt_of_le (mul_pos hc ht) h.2.2)
end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_MetadataAlphabet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Metadata
open scoped BigOperators Classical

def TwoListCode (V : Type*) (h p B : ℕ) :=
  (Fin h→Fin 5→V) × (Fin p→Fin 5→V) × Fin (B+1) ×
    (Fin h→Fin (B+1)) × (Fin p→Fin (B+1)) × (Fin h×Fin p→Fin (B+1))

instance instFintypeTwoListCode {V : Type*} [Fintype V] (h p B : ℕ) : Fintype (TwoListCode V h p B) :=
  inferInstanceAs (Fintype (_ × _ × _ × _ × _ × _))

def ListProfile (H J : ℕ) := {z : Fin (H+1)×Fin (H+1) // z.1.val*z.2.val≤J}

instance instFintypeListProfile (H J : ℕ) : Fintype (ListProfile H J) :=
  inferInstanceAs (Fintype {profile : Fin (H+1)×Fin (H+1) // profile.1.val*profile.2.val≤J})

def TrainingCode (V : Type*) (H J B : ℕ) :=
  (r : ListProfile H J) × TwoListCode V r.val.1.val r.val.2.val B

instance instFintypeTrainingCode {V : Type*} [Fintype V] (H J B : ℕ) : Fintype (TrainingCode V H J B) :=
  inferInstanceAs (Fintype ((r : ListProfile H J) × TwoListCode V r.val.1.val r.val.2.val B))

instance instNonemptyTrainingCode {V : Type*} [Nonempty V] (H J B : ℕ) : Nonempty (TrainingCode V H J B) := by
  classical
  refine ⟨⟨⟨(⟨0,by omega⟩,⟨0,by omega⟩),by simp⟩,?_,?_,?_,?_,?_,?_⟩⟩
  · exact fun _ _=>Classical.choice inferInstance
  · exact fun _ _=>Classical.choice inferInstance
  · exact ⟨0,by omega⟩
  · exact fun _=>⟨0,by omega⟩
  · exact fun _=>⟨0,by omega⟩
  · exact fun _=>⟨0,by omega⟩

end SharpRamseyFive.Metadata

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_MetadataBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Metadata
open scoped Classical

noncomputable def listCap (σ : ℝ) : ℕ := ⌈4*Real.exp (σ/2)⌉₊
noncomputable def productCap (σ : ℝ) : ℕ := ⌈4*Real.exp (13*σ/15)⌉₊

end SharpRamseyFive.Metadata

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_MetadataCodec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Metadata

section
open Module GreedyTraining MeasurePublicTable ProjectiveTraining
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [Fintype (ℙ K V)]

omit [FiniteDimensional K V] [Finite K] in
lemma projective_card_le_vectors [Finite V] (S : Finset (ℙ K V)) : S.card≤Nat.card V := by
  have hi : Function.Injective (fun x : ℙ K V=>x.rep) := by
    intro x y h
    rw [←x.mk_rep,←y.mk_rep]
    congr 1
  have hS : S.card≤Nat.card (ℙ K V) := by
    simpa only [Nat.card_eq_fintype_card] using Finset.card_le_univ S
  exact hS.trans (Nat.card_le_card_of_injective _ hi)

noncomputable def decodeH {h p B : ℕ} (c : TwoListCode V h p B) : Fin h→Finset (ℙ K V) :=
  fun i=>flatPoints (Submodule.span K (Set.range (c.1 i)))
noncomputable def decodeP {h p B : ℕ} (c : TwoListCode V h p B) : Fin p→Finset (ℙ K V) :=
  fun i=>flatPoints (Submodule.span K (Set.range (c.2.1 i)))
noncomputable def decodeOwn {h p B : ℕ} (c : TwoListCode V h p B) (x : ℙ K V) : Finset (ℙ K V) :=
  twoPublicOwn (decodeH c) (decodeP c) x

noncomputable def decodeOwnCount {h p B : ℕ} (c : TwoListCode V h p B) (x : ℙ K V) : ℕ :=
  let ih := firstIndex {F | x∈F} (decodeH c)
  let ip := firstIndex {F | x∈F} (decodeP c)
  (ih.elim 0 (fun i=>(c.2.2.2.1 i).val))+
    (ip.elim 0 (fun i=>(c.2.2.2.2.1 i).val))-
      (ih.elim 0 (fun i=>ip.elim 0 (fun j=>(c.2.2.2.2.2 (i,j)).val)))

omit [Fintype (ℙ K V)]

noncomputable def decodeBaseScore {h p B : ℕ} (c : TwoListCode V h p B) (L : ℝ) (x : ℙ K V) : ℝ :=
  Real.exp (-L*(1-(decodeOwnCount c x:ℝ)/c.2.2.1.val))

end

open Module GreedyTraining ProjectiveTraining
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [Fintype V] [Fintype (ℙ K V)]

omit [Fintype V] [Fintype (ℙ K V)] in
lemma vector_card_le_exp (σ : ℝ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5) :
    (Nat.card V:ℝ)≤Real.exp (5*σ) := by
  have hq1 : 1≤Nat.card K := Nat.card_pos
  have hh : Nat.card V≤Nat.card K^5 := by
    rw [Module.natCard_eq_pow_finrank (K:=K)]
    exact Nat.pow_le_pow_right hq1 hd
  have he : (Nat.card K:ℝ)^5=Real.exp (5*σ) := by
    rw [←hq,←Real.exp_nat_mul];norm_num
  exact (by exact_mod_cast hh : (Nat.card V:ℝ)≤(Nat.card K:ℝ)^5).trans_eq he

noncomputable def messageOwn {H J B : ℕ} (c : TrainingCode V H J B) (x : ℙ K V) : Finset (ℙ K V) :=
  decodeOwn c.2 x
noncomputable def messageBase {H J B : ℕ} (c : TrainingCode V H J B) (L : ℝ) (x : ℙ K V) : ℝ :=
  decodeBaseScore c.2 L x

end SharpRamseyFive.Metadata

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_ReverseParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ReverseCap
open scoped Classical

noncomputable def reverseLength (q gap : ℝ) : ℕ := ⌈20*q*(gap+1)⌉₊

lemma reverseLength_spec (q gap : ℝ) (hq : 1≤q) (hg : 0≤gap) :
    0 < reverseLength q gap ∧ 20*q*gap ≤ reverseLength q gap ∧
    (reverseLength q gap:ℝ)≤21*q*(gap+1) := by
  have hq' : 0<q := by linarith
  have hp : 0<20*q*(gap+1) := by positivity
  have hl := Nat.le_ceil (20*q*(gap+1))
  have hu := Nat.ceil_lt_add_one hp.le
  refine ⟨Nat.ceil_pos.mpr hp,?_,?_⟩
  · dsimp [reverseLength]
    nlinarith only [hl,hq']
  · dsimp [reverseLength]
    have hh : 1≤q*(gap+1) := by nlinarith
    nlinarith only [hu,hh]

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Swap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.RepresentativeAverage
open scoped BigOperators Classical
variable {B A : Type*} [Fintype B] [Fintype A]

noncomputable def swapAt (b : B) : ((B → A) × A) ≃ ((B → A) × A) :=
  Function.Involutive.toPerm (fun z => (Function.update z.1 b z.2,z.1 b)) (by
    intro z
    apply Prod.ext
    · funext c
      by_cases h : c=b
      · subst c
        simp
      · simp [Function.update_of_ne h]
    · simp)

end SharpRamseyFive.RepresentativeAverage

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_UniversalFresh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ReverseCap
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

abbrev FreshIndex (B : Type*) [Fintype B] (H : ℕ) :=
  {W : Finset B // W.Nonempty} × Fin (H+1)
abbrev UniversalFresh (B : Type*) [Fintype B] (H : ℕ) (q : ℝ) :=
  (i : FreshIndex B H)→FreshTape i.1.1 i.2 q
end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_UniversalReverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ReverseCap
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

abbrev UniversalFreshMessage (W : Finset B) (H : ℕ) (q : ℝ) :=
  (n : Fin (H+1)) × FreshMessage W n q

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_SubsetEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SubsetEncoding
open scoped Classical BigOperators

variable {α : Type*} [Fintype α]

abbrev Alphabet (U : Finset α) (n : ℕ) := {A : Finset α // A⊆U ∧ A.card=n}

noncomputable def encode (S U : Finset α) (hSU : S⊆U) : Fin (Fintype.card (Alphabet U S.card)) :=
  Fintype.equivFin (Alphabet U S.card) ⟨S,hSU,rfl⟩

noncomputable def decode (U : Finset α) (n : ℕ) (i : Fin (Fintype.card (Alphabet U n))) : Finset α :=
  ((Fintype.equivFin (Alphabet U n)).symm i).1

end SharpRamseyFive.SubsetEncoding

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence SubsetEncoding
open scoped Classical LinearAlgebra.Projectivization BigOperators NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def sizeScoreCutoff (U : Finset (ℙ K V)) (n : ℕ) (P τ : ℝ) : ℕ :=
  ⌈(Nat.card K:ℝ)*Real.exp
    (Real.log ((U.card:ℝ)/n)*(2*(Nat.card K:ℝ)*P)+(8*P*τ+Real.log 4))⌉₊

noncomputable def baseAlphabet (U : Finset (ℙ K V)) (n : ℕ) (P τ : ℝ) : Type _ :=
  if (n:ℝ)≤100*(Nat.card K:ℝ)*P then
    Fin (Fintype.card (Alphabet U n))
  else Fin (sizeScoreCutoff U n P τ) × Fin (Fintype.card (ℙ K (Dual K V))+1)

noncomputable instance instFintypeBaseAlphabet (U : Finset (ℙ K V)) (n : ℕ) (P τ : ℝ) :
    Fintype (baseAlphabet U n P τ) := by
  unfold baseAlphabet
  split <;> infer_instance

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_BasePublicFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence SubsetEncoding
open MeasureTheory ProbabilityTheory PoissonScore
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

abbrev BaseTape (U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) :=
  (n : Fin (Fintype.card (ℙ K V)+1)) → Fin (sizeScoreCutoff U n P τ) → Fin R → ℙ K V → ℕ

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ScoredMessage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence Metadata
open scoped Classical LinearAlgebra.Projectivization NNReal BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

abbrev ScoredPayload (U : Finset (ℙ K V)) (n : ℕ) (σ P τ : ℝ) :=
  TrainingCode V (listCap σ) (productCap σ) (Nat.card V) ×
    (Fin (sizeScoreCutoff U n P τ) × Fin (Fintype.card (ℙ K (Dual K V))+1))
abbrev ScoredMessage (U : Finset (ℙ K V)) (σ P τ : ℝ) :=
  (n : Fin (Fintype.card (ℙ K V)+1)) × ScoredPayload U n σ P τ

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ReverseMessageCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ReverseCap
open Module ScoreGeometry Metadata ProjectiveIncidence
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Fintype (ℙ K (Dual K V))] in
lemma projective_enclosure_gap (σ : ℝ) (hq : Real.exp σ=Nat.card K)
    (hd : finrank K V≤5) (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U) :
    0≤Real.log ((U.card:ℝ)/S.card) ∧ Real.log ((U.card:ℝ)/S.card)≤5*σ := by
  have hs : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hs1 : (1:ℝ)≤S.card := by exact_mod_cast hS.card_pos
  have hsu : (S.card:ℝ)≤U.card := by exact_mod_cast Finset.card_le_card hSU
  have hu : (0:ℝ)<U.card := hs.trans_le hsu
  have hv := vector_card_le_exp (K:=K) (V:=V) σ hq hd
  have hU : (U.card:ℝ)≤Nat.card V := by exact_mod_cast projective_card_le_vectors U
  have hdiv : (U.card:ℝ)/S.card≤Real.exp (5*σ) :=
    (div_le_self hu.le hs1).trans (hU.trans hv)
  refine ⟨Real.log_nonneg ((le_div_iff₀ hs).mpr (by simpa using hsu)),?_⟩
  simpa only [Real.log_exp] using Real.log_le_log (div_pos hu hs) hdiv

omit [Fintype (ℙ K (Dual K V))] in
lemma reverseLength_universal_bound (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K)
    (hd : finrank K V≤5) (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U) :
    reverseLength (Nat.card K) (Real.log ((U.card:ℝ)/S.card))≤1000*(Nat.card K)^2 := by
  have hs := projective_enclosure_gap σ hq hd S U hS hSU
  have hq1 : (1:ℝ)≤Nat.card K := by rw [←hq];exact Real.one_le_exp_iff.mpr (by linarith)
  have hσq : σ≤Nat.card K := by rw [←hq];linarith only [Real.add_one_le_exp σ]
  have hn := (reverseLength_spec (Nat.card K) _ hq1 hs.1).2.2
  have hgb : Real.log ((U.card:ℝ)/S.card)+1≤6*(Nat.card K:ℝ) := by linarith only [hs.2,hσq,hq1]
  have hm := mul_le_mul_of_nonneg_left hgb (show (0:ℝ)≤21*(Nat.card K:ℝ) by positivity)
  have hres : (reverseLength (Nat.card K) (Real.log ((U.card:ℝ)/S.card)):ℝ)≤1000*(Nat.card K:ℝ)^2 := by
    nlinarith only [hn,hm,sq_nonneg (Nat.card K:ℝ)]
  exact_mod_cast hres

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_GeometryScaleOrientedLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry

open Filter ParameterHierarchy
open scoped Topology

noncomputable def globalTruncConstant : ℝ := 4*2^(5000:ℕ)+32*333024*8^(4998:ℕ)

end SharpRamseyFive.ScoreGeometry

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_HighGeometryClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

lemma geometric_card_le (q d : ℕ) (hq : 2≤q) :
    (∑ i∈Finset.range (d+1),q^i) ≤ 2*q^d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ]
    have hq' : 2*q^d≤q^(d+1) := by
      rw [pow_succ]
      simpa only [mul_comm] using Nat.mul_le_mul_left (q^d) hq
    omega

omit [FiniteDimensional K V] in
lemma projective_card_le_two_pow [Fintype (ℙ K V)] {d : ℕ}
    (hdim : finrank K V=d+1) (hq : 2≤Nat.card K) :
    Fintype.card (ℙ K V)≤2*Nat.card K^d := by
  rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hdim]
  exact geometric_card_le _ _ hq

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_HyperplaneHigh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining HighPlaneBudget GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V J : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [LinearOrder J]

noncomputable def hyperplanePeelExceptions (F : Finset J) (hF : F.Nonempty)
    (Flat : J→Submodule K V) (X XH S : Finset (ℙ K V))
    (Planes : Finset (Submodule K V)) (j : ℕ) (δ : ℝ≥0) (χ : ℝ) (Q : Finset (ℙ K V)) : Finset (ℙ K V) :=
  if XH=X\remaining F hF (fun i=>flatPoints (Flat i)) X j
  then highPlaneExceptions F hF Flat X S Planes j δ χ Q
  else residualPlaneExceptions Planes XH S Q δ χ

end

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial PoissonScore
open Filter ParameterHierarchy MeasureTheory
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_DimensionFourLowAmbient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open ParameterHierarchy Filter
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

noncomputable def ambientHalfStrongExceptions {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [Finite K] [FiniteDimensional K V]
    (σ P : ℝ) (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)) : Finset (ℙ K V) :=
  if (S.card:ℝ)≤(Nat.card K:ℝ)^2*Real.exp (-4*P) then ∅
  else badCenters S O (pointStrength S) ((1/(100*(momentOrder σ P:ℝ)))/2) Lines Q 1

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FlatSection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveRestriction

section
open Module ProjectiveIncidence ProjectiveTraining
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def flatEmbedding (A : Submodule K V) : ℙ K A ↪ ℙ K V :=
  ⟨Projectivization.map A.subtype A.injective_subtype,
    Projectivization.map_injective A.subtype A.injective_subtype⟩

noncomputable def flatSection (A : Submodule K V) (X : Finset (ℙ K V)) : Finset (ℙ K A) :=
  X.preimage (flatEmbedding A) (flatEmbedding A).injective.injOn

end

open Module ProjectiveIncidence ProjectiveTraining
open scoped LinearAlgebra.Projectivization Classical BigOperators

end SharpRamseyFive.ProjectiveRestriction

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ThreeBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy MeasurePublicTable Metadata ProjectiveRestriction
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology
variable {K I J : Type*} [Field K] [Finite K] [Fintype I] [LinearOrder J]
  [Fintype (I→K)] [Fintype (ℙ K (I→K))] [Fintype (ℙ K (Dual K (I→K)))]

abbrev ThreeBranch (σ : ℝ) (F : Finset J) :=
  Unit ⊕ ((Fin (Fintype.card (ℙ K (I→K))+1) ×
    TrainingCode (I→K) (listCap σ) (productCap σ) (Nat.card (I→K))) ⊕
    ({a : J // a∈F} × Fin (Nat.log 2 (Nat.card K)+1)))

end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ProjectiveTraining
open Module
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype V]

noncomputable def flatEnumeration : Fin (Fintype.card (Submodule K V))→Submodule K V :=
  (Fintype.equivFin (Submodule K V)).symm
noncomputable def flatIndices (d : ℕ) : Finset (Fin (Fintype.card (Submodule K V))) :=
  Finset.univ.filter fun i=>finrank K (flatEnumeration (K:=K) (V:=V) i)=d
omit [Finite K] [FiniteDimensional K V] in
lemma flatIndices_rank (d : ℕ) (i) (hi : i∈flatIndices (K:=K) (V:=V) d) :
    finrank K (flatEnumeration i)=d := (Finset.mem_filter.mp hi).2
end SharpRamseyFive.ProjectiveTraining

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_DimensionFourHighLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy MeasurePublicTable Metadata ProjectiveRestriction
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology
variable {K I J : Type*} [Field K] [Finite K] [Fintype I] [LinearOrder J]
  [Fintype (I→K)] [Fintype (ℙ K (I→K))] [Fintype (ℙ K (Dual K (I→K)))]

abbrev FourBranch (σ : ℝ) (F H : Finset J) :=
  Unit ⊕ ((Bool × Fin (Fintype.card (ℙ K (I→K))+1) ×
    TrainingCode (I→K) (listCap σ) (productCap σ) (Nat.card (I→K))) ⊕
    (({a : J // a∈F} × Fin (Nat.log 2 ((Nat.card K)^2)+1)) ⊕
     ({a : J // a∈H} × Fin (Nat.log 2 (Nat.card K)+1))))

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_UniversalFreshCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ReverseCap
open scoped Classical BigOperators
variable {A B : Type*} [Fintype B]

noncomputable def universalFreshCost (W : Finset B) (H : ℕ) (q : ℝ)
    (m : UniversalFreshMessage W H q) : ℝ :=
  Real.log (H+1:ℝ)+Real.log (W.card+1:ℝ)+
    Real.log (Fintype.card (Fin (cardCutoff q m.2.1 W.card m.1)):ℝ)

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_AmbientPairPublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ProjectiveIncidence
open Module ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

abbrev AmbientPairTape (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] (H : ℕ) (q : ℝ) :=
  UniversalFresh (ℙ K V) H q × UniversalFresh (ℙ K (Dual K V)) H q
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_BaseFinitePublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

abbrev BaseMessage (U : Finset (ℙ K V)) (P τ : ℝ) :=
  (n : Fin (Fintype.card (ℙ K V)+1)) × baseAlphabet U n P τ
abbrev BaseTable (U : Finset (ℙ K V)) (P τ : ℝ) := BaseMessage U P τ→Finset (ℙ K V)

end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence Metadata
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

abbrev ScoreTable (U : Finset (ℙ K V)) (σ P τ : ℝ) :=
  ScoredMessage U σ P τ→Finset (ℙ K V)
end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ScoreFiniteCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence Metadata
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
noncomputable def scoreFiniteCost (U : Finset (ℙ K V)) (σ P τ : ℝ)
    (m : ScoredMessage U σ P τ) : ℝ :=
  Real.log (Fintype.card (ℙ K V)+1:ℝ)+Real.log (Fintype.card (ScoredPayload U m.1 σ P τ):ℝ)

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ReversedBasePublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

abbrev ReversedBaseTape (UT : Finset (ℙ K (Dual K V))) (P τ : ℝ) (H : ℕ) (q : ℝ) :=
  BaseTable UT P τ × UniversalFresh (ℙ K (Dual K V)) H q

abbrev ReversedBaseMessage (UT : Finset (ℙ K (Dual K V))) (P τ : ℝ) (H : ℕ) (q : ℝ)
    (t : ReversedBaseTape UT P τ H q) :=
  (m : BaseMessage UT P τ) × UniversalFreshMessage (t.1 m) H q

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_TwoFinitePublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

abbrev TwoPublicTape (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (H : ℕ) (q : ℝ) := BaseTable U P τ × ReversedBaseTape UT P τ H q
abbrev TwoPublicMessage (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (H : ℕ) (q : ℝ) (t : TwoPublicTape U UT P τ H q) :=
  BaseMessage U P τ ⊕ ReversedBaseMessage UT P τ H q t.2
end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_BaseFiniteCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def baseFiniteCost (U : Finset (ℙ K V)) (P τ : ℝ) (m : BaseMessage U P τ) : ℝ :=
  Real.log (Fintype.card (ℙ K V)+1:ℝ)+Real.log (Fintype.card (baseAlphabet U m.1 P τ):ℝ)

end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

noncomputable def reversedBaseCost (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (H : ℕ) (q : ℝ) (t : ReversedBaseTape UT P τ H q)
    (m : ReversedBaseMessage UT P τ H q t) : ℝ :=
  baseFiniteCost UT P τ m.1+universalFreshCost (t.1 m.1) H q m.2

end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

noncomputable def twoPublicCost (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (H : ℕ) (q : ℝ) (t : TwoPublicTape U UT P τ H q) :
    TwoPublicMessage U UT P τ H q t→ℝ
  | Sum.inl m => Real.log 2+baseFiniteCost U P τ m
  | Sum.inr m => Real.log 2+reversedBaseCost UT P τ H q t.2 m

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ThreePublicDefs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining ProjectiveRestriction
open Metadata ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K : Type} [Field K] [Finite K] [Fintype K]
  [Fintype (ℙ K (Fin 4→K))] [Fintype (ℙ K (Dual K (Fin 4→K)))]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K A)]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K A))]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K (Dual K A)))]

abbrev ThreePublicIndex (K : Type) [Field K] [Finite K] [Fintype K]
    [Fintype (ℙ K (Fin 4→K))] (σ : ℝ) :=
  ThreeBranch (K:=K) (I:=Fin 4) σ (flatIndices (K:=K) (V:=Fin 4→K) 3)

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_GeneralReversedCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V Ω : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] [Fintype Ω]

abbrev GeneralReversedTape (Ω : Type*) (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    [Fintype (ℙ K (Dual K V))] (H : ℕ) (q : ℝ) :=
  Ω × UniversalFresh (ℙ K (Dual K V)) H q
abbrev GeneralReversedMessage (M : Ω→Type*) (dec : ∀t,M t→Finset (ℙ K (Dual K V)))
    (H : ℕ) (q : ℝ) (t : GeneralReversedTape Ω K V H q) :=
  (m : M t.1) × UniversalFreshMessage (dec t.1 m) H q
noncomputable def generalReversedCost (M : Ω→Type*) (dec : ∀t,M t→Finset (ℙ K (Dual K V)))
    (cost : ∀t,M t→ℝ) (H : ℕ) (q : ℝ) (t : GeneralReversedTape Ω K V H q)
    (m : GeneralReversedMessage M dec H q t) : ℝ :=
  cost t.1 m.1+universalFreshCost (dec t.1 m.1) H q m.2

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FiniteFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining ProjectiveRestriction
open Metadata ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K : Type} [Field K] [Finite K] [Fintype K]
  [Fintype (ℙ K (Fin 5→K))] [Fintype (ℙ K (Dual K (Fin 5→K)))]
  [∀ A : Submodule K (Fin 5→K),Fintype (ℙ K A)]
  [∀ A : Submodule K (Fin 5→K),Fintype (ℙ K (Dual K A))]
  [∀ A : Submodule K (Fin 5→K),Fintype (ℙ K (Dual K (Dual K A)))]
abbrev FourPublicIndex (K : Type) [Field K] [Finite K] [Fintype K]
    [Fintype (ℙ K (Fin 5→K))] (σ : ℝ) :=
  FourBranch (K:=K) (I:=Fin 5) σ (flatIndices (K:=K) (V:=Fin 5→K) 3)
    (flatIndices (K:=K) (V:=Fin 5→K) 4)

end

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy MeasurePublicTable Metadata
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FiniteNode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

open Module ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

lemma nonempty_of_positive_trim {α : Type*} (A A₀ : Finset α) (hA₀ : A₀.Nonempty)
    (δ : ℝ) (hδ : 0<δ) (htrim : δ*A₀.card≤A.card) : A.Nonempty := by
  exact Finset.card_pos.mp (Nat.cast_pos.mp (lt_of_lt_of_le
    (mul_pos hδ (by exact_mod_cast hA₀.card_pos)) htrim))

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_PivotPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.PivotTree

noncomputable def potential (uA uB Q : ℝ) : ℝ := max 0 (Real.log (uA*uB/Q))

end SharpRamseyFive.PivotTree

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_PivotTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.PivotTree
open BinaryTree

def balanced (lo : ℕ) : ℕ → BinaryTree ℕ
  | 0 => .nil
  | n+1 => .node (lo+n/2) (balanced lo (n/2))
      (balanced (lo+n/2+1) (n-n/2))
termination_by n => n

def inorder {α : Type*} : BinaryTree α → List α
  | .nil => []
  | .node a l r => inorder l ++ a :: inorder r

lemma balanced_nodes (lo n : ℕ) : (balanced lo n).numNodes=n := by
  induction n using Nat.strong_induction_on generalizing lo with
  | h n ih =>
    cases n with
    | zero => simp [balanced]
    | succ n =>
      rw [balanced,BinaryTree.numNodes,ih (n/2) (by omega),ih (n-n/2) (by omega)]
      omega

lemma balanced_inorder (lo n : ℕ) : inorder (balanced lo n)=List.range' lo n := by
  induction n using Nat.strong_induction_on generalizing lo with
  | h n ih =>
    cases n with
    | zero => simp [balanced,inorder]
    | succ n =>
      rw [balanced,inorder,ih (n/2) (by omega),ih (n-n/2) (by omega)]
      rw [←List.range'_succ]
      have he : lo+n/2=lo+1*(n/2) := by omega
      rw [he,List.range'_append]
      have he' : n/2+(n-n/2+1)=n+1 := by omega
      rw [he']

end SharpRamseyFive.PivotTree

namespace SharpRamseyFive.TreeCodec
open BinaryTree
open scoped Classical
universe u v w z
variable {A : Type u} {C : Type v} [Fintype C]
  (Ω : A→C→Type w) (M : ∀a c,Ω a c→Type z)

def Tape : BinaryTree A→Type (max v w)
  | .nil => PUnit
  | .node a l r => (∀c,Ω a c) × Tape l × Tape r

noncomputable instance tapeFintype [∀a c,Fintype (Ω a c)] (t : BinaryTree A) : Fintype (Tape Ω t) := by
  induction t with
  | nil => exact inferInstanceAs (Fintype PUnit)
  | node a l r hl hr =>
    letI := hl
    letI := hr
    exact inferInstanceAs (Fintype ((∀c,Ω a c)×Tape Ω l×Tape Ω r))

variable (left right : ∀a c t,M a c t→C)

def Message : (b : BinaryTree A)→Tape Ω b→C→Type (max z v w)
  | .nil,_,_ => PUnit
  | .node a l r,ω,c => Option ((m : M a c (ω.1 c)) ×
      Message l ω.2.1 (left a c (ω.1 c) m) × Message r ω.2.2 (right a c (ω.1 c) m))

noncomputable instance messageFintype [∀a c t,Fintype (M a c t)]
    (b : BinaryTree A) (ω : Tape Ω b) (c : C) : Fintype (Message Ω M left right b ω c) := by
  induction b generalizing c with
  | nil => exact inferInstanceAs (Fintype PUnit)
  | node a l r hl hr =>
    letI (m : M a c (ω.1 c)) := hl ω.2.1 (left a c (ω.1 c) m)
    letI (m : M a c (ω.1 c)) := hr ω.2.2 (right a c (ω.1 c) m)
    exact inferInstanceAs (Fintype (Option ((m : M a c (ω.1 c))×
      Message Ω M left right l ω.2.1 (left a c (ω.1 c) m)×
      Message Ω M left right r ω.2.2 (right a c (ω.1 c) m))))

noncomputable def encoded (enc : ∀a c t,Option (M a c t)) :
    (b : BinaryTree A)→(ω : Tape Ω b)→(c : C)→Message Ω M left right b ω c
  | .nil,_,_ => PUnit.unit
  | .node a l r,ω,c => (enc a c (ω.1 c)).map fun m=>⟨m,
      encoded enc l ω.2.1 (left a c (ω.1 c) m),
      encoded enc r ω.2.2 (right a c (ω.1 c) m)⟩

def retained : (b : BinaryTree A)→(ω : Tape Ω b)→(c : C)→
    Message Ω M left right b ω c→BinaryTree A
  | .nil,_,_,_ => .nil
  | .node _ _ _,_,_,none => .nil
  | .node a l r,ω,c,some ⟨m,ml,mr⟩ => .node a
      (retained l ω.2.1 (left a c (ω.1 c) m) ml)
      (retained r ω.2.2 (right a c (ω.1 c) m) mr)

noncomputable def cost (localCost : ∀a c t,M a c t→ℝ) :
    (b : BinaryTree A)→(ω : Tape Ω b)→(c : C)→Message Ω M left right b ω c→ℝ
  | .nil,_,_,_ => 0
  | .node _ _ _,_,_,none => 0
  | .node a l r,ω,c,some ⟨m,ml,mr⟩ => localCost a c (ω.1 c) m+
      cost localCost l ω.2.1 (left a c (ω.1 c) m) ml+
      cost localCost r ω.2.2 (right a c (ω.1 c) m) mr

end SharpRamseyFive.TreeCodec

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ConcretePivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module ReverseCap ScoreGeometry BinaryTree
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

abbrev PivotContext (K V : Type) [Field K] [AddCommGroup V] [Module K V] :=
  Finset (ℙ K V)×Finset (ℙ K (Dual K V))

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_TreeWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpRamseyFive.TreeCodec
open BinaryTree
open scoped Classical BigOperators
universe u v w z
variable {A : Type u} {C : Type v} [Fintype C]
  (Ω : A→C→Type w) (M : ∀a c,Ω a c→Type z)
  (left right : ∀a c t,M a c t→C)

noncomputable def slotCost (localCost : ∀a c t,M a c t→ℝ) :
    (b : BinaryTree A)→(ω : Tape Ω b)→(c : C)→Message Ω M left right b ω c→ℝ
  | .nil,_,_,_ => 0
  | .node _ _ _,_,_,none => Real.log 2
  | .node a l r,ω,c,some ⟨m,ml,mr⟩ => Real.log 2+localCost a c (ω.1 c) m+
      slotCost localCost l ω.2.1 (left a c (ω.1 c) m) ml+
      slotCost localCost r ω.2.2 (right a c (ω.1 c) m) mr

end SharpRamseyFive.TreeCodec
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_OrientedTreePotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module ReverseCap ScoreGeometry PivotTree BinaryTree
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

noncomputable def pivotPotential (C : PivotContext K V) : ℝ :=
  potential C.1.card C.2.card ((Nat.card K:ℝ)^5)

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_OrientedTreeCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module ReverseCap ScoreGeometry PivotTree BinaryTree Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology

noncomputable def nodeChargeConstant : ℝ :=
  32120+21*(12-Real.log ((9:ℝ)/100000)-Real.log ((9:ℝ)/10))
end

open Module ReverseCap ScoreGeometry PivotTree BinaryTree Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology BigOperators

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_AmbientEviction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ReverseCap
open scoped Classical BigOperators
variable {A Ω : Type*} [Fintype A] [Fintype Ω]

noncomputable def ambientTest : Option (Finset A)→Finset A
  | none => Finset.univ
  | some Y => Y

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_TreeExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.TreeCodec
open BinaryTree
open scoped Classical BigOperators
universe u v w z s
variable {A : Type u} {C : Type v} [Fintype C]
  (Ω : A → C → Type w) [∀ a c, Fintype (Ω a c)]
  (M : ∀ a c, Ω a c → Type z)
  (left right : ∀ a c t, M a c t → C)

def Address : BinaryTree A → Type
  | .nil => Empty
  | .node _ l r => Unit ⊕ Address l ⊕ Address r

noncomputable instance addressFintype (b : BinaryTree A) : Fintype (Address b) := by
  induction b with
  | nil => exact inferInstanceAs (Fintype Empty)
  | node a l r ihl ihr =>
    letI := ihl
    letI := ihr
    exact inferInstanceAs (Fintype (Unit ⊕ Address l ⊕ Address r))

def label : (b : BinaryTree A) → Address b → A
  | .nil, j => nomatch j
  | .node a _ _, .inl _ => a
  | .node _ l _, .inr (.inl j) => label l j
  | .node _ _ r, .inr (.inr j) => label r j

variable {D : Type s}

noncomputable def probe (enc : ∀ a c t, Option (M a c t))
    (test : ∀ a c, Ω a c → Option D) :
    (b : BinaryTree A) → Tape Ω b → C → Address b → Option D
  | .nil, _, _, j => nomatch j
  | .node a _ _, ω, c, .inl _ => test a c (ω.1 c)
  | .node a l _, ω, c, .inr (.inl j) =>
      ((enc a c (ω.1 c)).map (left a c (ω.1 c))).elim none
        (fun c' => probe enc test l ω.2.1 c' j)
  | .node a _ r, ω, c, .inr (.inr j) =>
      ((enc a c (ω.1 c)).map (right a c (ω.1 c))).elim none
        (fun c' => probe enc test r ω.2.2 c' j)

noncomputable def observe (enc : ∀ a c t, Option (M a c t))
    (out : ∀ a c t, M a c t → D) :
    (b : BinaryTree A) → Tape Ω b → C → Address b → Option D :=
  probe Ω M left right enc (fun a c t => (enc a c t).map (out a c t))

end SharpRamseyFive.TreeCodec

namespace SharpRamseyFive.TreeCodec
open BinaryTree
open scoped Classical BigOperators
universe u v w z s
variable {A : Type u}
  {C : Type v}
  [Fintype C]
  (Ω : A → C → Type w)
  [∀ a c, Fintype (Ω a c)]

variable (M : ∀ a c, Ω a c → Type z)
  (left right : ∀ a c t, M a c t → C)

noncomputable def contextAt (enc : ∀ a c t, Option (M a c t)) :
    (b : BinaryTree A) → Tape Ω b → C → Address b → Option C :=
  probe Ω M left right enc (fun _ c _ => some c)

def pathBudget (ρL ρR : A → ℝ) : (b : BinaryTree A) → Address b → ℝ
  | .nil, j => nomatch j
  | .node _ _ _, .inl _ => 0
  | .node a l _, .inr (.inl j) => ρL a + pathBudget ρL ρR l j
  | .node a _ r, .inr (.inr j) => ρR a + pathBudget ρL ρR r j

end SharpRamseyFive.TreeCodec

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_TreeOriginalTrims
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.TreeCodec

section
open BinaryTree ReverseCap
open scoped Classical BigOperators
universe u v w z
variable {I : Type u}
  {A B : Type v}
  [Fintype A]
  [Fintype B]
  (Ω : I → (Finset A × Finset B) → Type w)
  [∀ i c, Fintype (Ω i c)]
  (M : ∀ i c, Ω i c → Type z)
  (out : ∀ i c t, M i c t → Finset A × Finset B)

noncomputable def capLeft (i : I) (c : Finset A × Finset B) (t : Ω i c)
    (m : M i c t) : Finset A × Finset B := (c.1 ∩ (out i c t m).1, c.2)
noncomputable def capRight (i : I) (c : Finset A × Finset B) (t : Ω i c)
    (m : M i c t) : Finset A × Finset B := (c.1, c.2 ∩ (out i c t m).2)

end

open BinaryTree
open scoped Classical BigOperators
universe u v w z
variable {I : Type u}

def pathSum : (b : BinaryTree I) → (Address b → ℝ) → Address b → ℝ
  | .nil, _, j => nomatch j
  | .node _ _ _, f, .inl _ => f (.inl ())
  | .node _ l _, f, .inr (.inl j) => f (.inl ()) + pathSum l (fun k => f (.inr (.inl k))) j
  | .node _ _ r, f, .inr (.inr j) => f (.inl ()) + pathSum r (fun k => f (.inr (.inr k))) j

variable {C : Type v} [Fintype C]
  (Ω : I → C → Type w) [∀ i c, Fintype (Ω i c)]
  (M : ∀ i c, Ω i c → Type z) (left right : ∀ i c t, M i c t → C)
  (enc : ∀ i c t, Option (M i c t))

noncomputable def abortAt (b : BinaryTree I) (ω : Tape Ω b) (c : C) (j : Address b) : Option Bool :=
  probe Ω M left right enc (fun i c t => some (enc i c t).isNone) b ω c j
noncomputable def successAt (b : BinaryTree I) (ω : Tape Ω b) (c : C) (j : Address b) : Option Unit :=
  observe Ω M left right enc (fun _ _ _ _ => ()) b ω c j

end SharpRamseyFive.TreeCodec

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_TreeDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.TreeCodec
open BinaryTree
open scoped Classical
universe u v w z s
variable {A : Type u} {C : Type v} [Fintype C]
  (Ω : A→C→Type w) [∀ a c,Fintype (Ω a c)]
  (M : ∀ a c,Ω a c→Type z) (left right : ∀ a c t,M a c t→C)
  {D : Type s}

def decodedAt (out : ∀ a c t,M a c t→D) :
    (b : BinaryTree A)→(ω : Tape Ω b)→(c : C)→
    Message Ω M left right b ω c→Address b→Option D
  | .nil,_,_,_,j => nomatch j
  | .node _ _ _,_,_,none,_ => none
  | .node a _ _,ω,c,some ⟨m,_,_⟩,.inl _ => some (out a c (ω.1 c) m)
  | .node a l _,ω,c,some ⟨m,ml,_⟩,.inr (.inl j) =>
      decodedAt out l ω.2.1 (left a c (ω.1 c) m) ml j
  | .node a _ r,ω,c,some ⟨m,_,mr⟩,.inr (.inr j) =>
      decodedAt out r ω.2.2 (right a c (ω.1 c) m) mr j

end SharpRamseyFive.TreeCodec

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_TargetCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
noncomputable section
local instance (priority := high) actualTargetCapsPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P

end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_TreeOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.TreeCodec
open BinaryTree
open scoped Classical BigOperators
variable {I J : Type*} [Preorder I] [Preorder J]

def Ordered : BinaryTree I→Prop
  | .nil=>True
  | .node a l r=>(∀ j:Address l,label l j≤a) ∧
      (∀ j:Address r,a≤label r j) ∧ Ordered l ∧ Ordered r

omit [Preorder I] in
lemma label_mem_inorder (b : BinaryTree I) (j : Address b) : label b j∈PivotTree.inorder b := by
  induction b with
  | nil=>exact nomatch j
  | node a l r ihl ihr=>
    rcases j with j | (j | j)
    · simp [label,PivotTree.inorder]
    · exact List.mem_append_left _ (ihl j)
    · exact List.mem_append_right _ (List.mem_cons_of_mem a (ihr j))

omit [Preorder I] in
lemma exists_address_of_mem (b : BinaryTree I) (a : I) (ha : a∈PivotTree.inorder b) :
    ∃ j:Address b,label b j=a := by
  induction b with
  | nil=>simp [PivotTree.inorder] at ha
  | node v l r ihl ihr=>
    rcases List.mem_append.mp ha with h | h
    · obtain ⟨j,hj⟩:=ihl h
      exact ⟨.inr (.inl j),hj⟩
    · rcases List.mem_cons.mp h with h | h
      · exact ⟨.inl (),h.symm⟩
      · obtain ⟨j,hj⟩:=ihr h
        exact ⟨.inr (.inr j),hj⟩

omit [Preorder I] [Preorder J] in
lemma label_map_mem (g : I→J) (b : BinaryTree I) (j : Address (b.map g)) :
    ∃ k:Address b,label (b.map g) j=g (label b k) := by
  induction b with
  | nil=>exact nomatch j
  | node a l r ihl ihr=>
    rcases j with j | (j | j)
    · exact ⟨.inl (),rfl⟩
    · obtain ⟨k,hk⟩:=ihl j
      exact ⟨.inr (.inl k),hk⟩
    · obtain ⟨k,hk⟩:=ihr j
      exact ⟨.inr (.inr k),hk⟩

omit [Preorder I] [Preorder J] in
lemma map_nodes (g : I→J) (b : BinaryTree I) : (b.map g).numNodes=b.numNodes := by
  induction b with
  | nil=>rfl
  | node a l r ihl ihr=>simp only [BinaryTree.map,BinaryTree.numNodes,ihl,ihr]
end SharpRamseyFive.TreeCodec

namespace SharpRamseyFive.PivotTree
open BinaryTree TreeCodec
lemma balanced_label_bounds (lo n : ℕ) (j : Address (balanced lo n)) :
    lo≤label (balanced lo n) j ∧ label (balanced lo n) j<lo+n := by
  have h:=label_mem_inorder (balanced lo n) j
  rw [balanced_inorder,List.mem_range'] at h
  obtain ⟨i,hi,he⟩:=h
  constructor <;> omega

def finiteBalanced (n : ℕ) : BinaryTree (Fin (n+1)) :=
  (balanced 0 n).map (fun i=>⟨min i n,Nat.lt_succ_of_le (min_le_right _ _)⟩)

lemma finiteBalanced_nodes (n : ℕ) : (finiteBalanced n).numNodes=n := by
  rw [finiteBalanced,map_nodes,balanced_nodes]

lemma finiteBalanced_label_lt (n : ℕ) (j : Address (finiteBalanced n)) :
    (label (finiteBalanced n) j).val<n := by
  obtain ⟨k,hk⟩:=label_map_mem (fun i=>⟨min i n,Nat.lt_succ_of_le (min_le_right _ _)⟩ : ℕ→Fin (n+1))
    (balanced 0 n) j
  change (label ((balanced 0 n).map _) j).val<n
  rw [hk]
  have h:=(balanced_label_bounds 0 n k).2
  change min _ n<n
  omega
end SharpRamseyFive.PivotTree

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_TreeShape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.TreeCodec
open BinaryTree
open scoped Classical
variable {I J : Type*}
lemma inorder_map (g : I→J) (b : BinaryTree I) :
    PivotTree.inorder (b.map g)=(PivotTree.inorder b).map g := by
  induction b with
  | nil=>rfl
  | node a l r ihl ihr=>simp only [BinaryTree.map,PivotTree.inorder,List.map_append,
      List.map_cons,ihl,ihr]

lemma address_card (b : BinaryTree I) : Fintype.card (Address b)=b.numNodes := by
  induction b with
  | nil=>rfl
  | node a l r ihl ihr=>
    have he : Fintype.card (Address (.node a l r)) = Fintype.card (Unit ⊕ (Address l ⊕ Address r)) :=
      Fintype.card_congr (Equiv.refl _)
    rw [he,Fintype.card_sum,Fintype.card_sum,Fintype.card_unit,ihl,ihr]
    simp only [BinaryTree.numNodes]
    omega
end SharpRamseyFive.TreeCodec
namespace SharpRamseyFive.PivotTree
open TreeCodec
open scoped Classical
noncomputable section

def finiteRank (n : ℕ) (j : Address (finiteBalanced n)) : Fin n :=
  ⟨(label (finiteBalanced n) j).val,finiteBalanced_label_lt n j⟩

lemma finiteRank_surjective (n : ℕ) : Function.Surjective (finiteRank n) := by
  intro i
  let a : Fin (n+1):=⟨i.val,Nat.lt_succ_of_lt i.isLt⟩
  have ha : a∈inorder (finiteBalanced n) := by
    rw [finiteBalanced,inorder_map,balanced_inorder]
    apply List.mem_map.mpr
    refine ⟨i.val,?_,?_⟩
    · rw [List.mem_range']
      exact ⟨i.val,i.isLt,by simp⟩
    · apply Fin.ext
      exact min_eq_left i.isLt.le
  obtain ⟨j,hj⟩:=exists_address_of_mem (finiteBalanced n) a ha
  refine ⟨j,?_⟩
  apply Fin.ext
  exact congrArg (fun a : Fin (n+1)=>a.val) hj

def finiteRankEquiv (n : ℕ) : Address (finiteBalanced n) ≃ Fin n :=
  Equiv.ofBijective (finiteRank n) ((Fintype.bijective_iff_surjective_and_card (finiteRank n)).mpr
    ⟨finiteRank_surjective n,by rw [address_card,finiteBalanced_nodes,Fintype.card_fin]⟩)

@[simp] lemma finiteRankEquiv_apply (n : ℕ) (j : Address (finiteBalanced n)) :
    finiteRankEquiv n j=finiteRank n j := rfl

end
end SharpRamseyFive.PivotTree

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ReadyFailure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module ReverseCap ScoreGeometry Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
noncomputable section
local instance (priority := high) actualReadyFailurePropDecidable (P : Prop) : Decidable P := Classical.propDecidable P

end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_ReachedFailure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.TreeCodec
open BinaryTree
open scoped Classical BigOperators
noncomputable section
local instance (priority := high) allPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P
universe u v w z
variable {I : Type u} {C : Type v} [Fintype C]
  (Ω : I → C → Type w) [∀ i c, Fintype (Ω i c)]
  (M : ∀ i c, Ω i c → Type z) (left right : ∀ i c t, M i c t → C)
  (enc : ∀ i c t, Option (M i c t))

noncomputable def flagTest (P : ∀ i c, Ω i c → Prop) :=
  fun i c t => if P i c t then some () else none

noncomputable def flagAt (P : ∀ i c, Ω i c → Prop)
    (b : BinaryTree I) (ω : Tape Ω b) (c : C) (j : Address b) : Option Unit :=
  probe Ω M left right enc (flagTest Ω P) b ω c j

end
end SharpRamseyFive.TreeCodec

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_MeanTreeFailure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.TreeCodec
open BinaryTree
open scoped Classical BigOperators
noncomputable section
local instance (priority := high) meanTreePropDecidable (P : Prop) : Decidable P := Classical.propDecidable P
universe u v w z s
end
end SharpRamseyFive.TreeCodec

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_OriginalReadiness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
local instance (priority := high) allPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P
end
end

open Module ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
local instance (priority := high) levelReadinessPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P
end

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_TreeFailure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
local instance (priority := high) actualTreeFailurePropDecidable (P : Prop) : Decidable P := Classical.propDecidable P
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FiniteTreeFailure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module ReverseCap ScoreGeometry BinaryTree TreeCodec Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization BigOperators NNReal Topology
noncomputable section
local instance (priority := high) actualFiniteFailurePropDecidable (P : Prop) : Decidable P := Classical.propDecidable P

end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_OrderedRetention
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module ReverseCap ScoreGeometry BinaryTree TreeCodec Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization BigOperators NNReal Topology
noncomputable section
local instance (priority := high) orderedRetentionPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P

end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_TargetTrims
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
local instance (priority := high) actualTargetTrimsPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_LevelTargetBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
local instance (priority := high) levelTargetBoundsPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_TargetRetention
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
local instance (priority := high) actualTargetRetentionPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_OrderedTargetRetention
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module ReverseCap ScoreGeometry BinaryTree TreeCodec Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization BigOperators NNReal Topology
noncomputable section
local instance (priority := high) orderedTargetPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P

end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_SurvivorRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.PivotTree
open scoped Classical
noncomputable section
variable {w : ℕ}

def survivorRank (E : Finset (Fin w)) (v : Fin w) : Fin (w+1) :=
  ⟨(E.filter fun u=>u<v).card,by
    have h := (Finset.card_le_card (Finset.filter_subset (fun u=>u<v) E)).trans
      (Finset.card_le_univ E)
    simp only [Fintype.card_fin] at h
    omega⟩

lemma survivorRank_orderEmb (E : Finset (Fin w)) (j : Fin E.card) :
    (survivorRank E (E.orderEmbOfFin rfl j)).val=j.val := by
  have he : E.filter (fun u=>u<E.orderEmbOfFin rfl j)=
      (Finset.Iio j).image (E.orderEmbOfFin rfl) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_image,Finset.mem_Iio]
    constructor
    · rintro ⟨hu,huj⟩
      let i := (E.orderIsoOfFin rfl).symm ⟨u,hu⟩
      have hi : E.orderEmbOfFin rfl i=u := congrArg Subtype.val
        ((E.orderIsoOfFin rfl).apply_symm_apply ⟨u,hu⟩)
      exact ⟨i,(E.orderEmbOfFin rfl).lt_iff_lt.mp (by simpa only [hi] using huj),hi⟩
    · rintro ⟨i,hij,rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem ..,(E.orderEmbOfFin rfl).strictMono hij⟩
  change (E.filter _).card=j.val
  rw [he,Finset.card_image_of_injective _ (E.orderEmbOfFin rfl).injective]
  exact Fin.card_Iio j

lemma survivorRank_mem_lt (E : Finset (Fin w)) (v : Fin w) (hv : v∈E) :
    (survivorRank E v).val<E.card := by
  let j := (E.orderIsoOfFin rfl).symm ⟨v,hv⟩
  have hj : E.orderEmbOfFin rfl j=v := congrArg Subtype.val
    ((E.orderIsoOfFin rfl).apply_symm_apply ⟨v,hv⟩)
  rw [←hj,survivorRank_orderEmb]
  exact j.isLt

end
end SharpRamseyFive.PivotTree

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ProjectiveExpectedLevelLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

lemma Q_le_power {q d : ℕ} (hq : 2 ≤ q) : (Q q d:ℝ) ≤ (q:ℝ)^(d+1) := by
  have hg : (Q q d:ℝ)*((q:ℝ)-1)=(q:ℝ)^(d+1)-1 := by
    simpa only [Q,Nat.cast_sum,Nat.cast_pow] using geom_sum_mul (q:ℝ) (d+1)
  have hqR : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hn : (0:ℝ) ≤ Q q d := Nat.cast_nonneg _
  nlinarith [mul_nonneg hn (sub_nonneg.mpr hqR)]

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_LogContractionDrop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open scoped BigOperators Classical

lemma log_contraction_drop (x y δ : ℝ) (hx : 1≤x) (hy : 0≤y) (hδ : 0≤δ)
    (hc : y≤(1-δ)*x) : Real.log (1+y)≤Real.log (1+x)-δ/2 := by
  have hx0 : 0<1+x := by linarith
  have hy0 : 0<1+y := by linarith
  have hh := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
  rw [Real.log_div hy0.ne' hx0.ne'] at hh
  have hd : (1+y)/(1+x)-1≤ -δ/2 := by
    have hrat : (1+y)/(1+x)≤1-δ/2 := by
      apply (div_le_iff₀ hx0).mpr
      nlinarith [mul_nonneg hδ (show 0≤x-1 by linarith)]
    linarith
  linarith

lemma telescoping_drop (f : ℕ → ℝ) (e : ℕ → ℝ) (N : ℕ)
    (hstep : ∀ i<N,f (i+1)≤f i-e i) :
    f N≤f 0-∑ i∈Finset.range N,e i := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hi := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    have hh := hstep N (Nat.lt_succ_self N)
    rw [Finset.sum_range_succ]
    linarith

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_IncidencesDegrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

lemma density_upper {d : ℕ} (hd : 1≤d) :
    (Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d ≤ 1/(Nat.card K:ℝ) := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K)).le
  have hQ : (0:ℝ)<Q (Nat.card K) d := by exact_mod_cast Q_pos (Nat.card K) d
  apply (div_le_div_iff₀ hQ hq).mpr
  have hr : (Q (Nat.card K) d:ℝ)=(Nat.card K:ℝ)*Q (Nat.card K) (d-1)+1 := by
    exact_mod_cast Q_recurrence (q := Nat.card K) hd
  nlinarith

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_State
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V Y : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [Fintype (ℙ K V)]

lemma subspace_finset_card (W : Submodule K V) :
    (Finset.univ.filter fun p : ℙ K V => p.submodule≤W).card =
      ∑ i∈Finset.range (finrank K W),Nat.card K^i := by
  rw [←Fintype.card_subtype,←Nat.card_eq_fintype_card]
  exact card_subspacePoints W

noncomputable def memberships (W : Y → Submodule K V) (Z : Finset Y) (b : ℙ K V) : ℕ :=
  (Z.filter fun y => b.submodule≤W y).card

lemma sum_memberships (W : Y → Submodule K V) (Z : Finset Y) (l : ℕ)
    (hW : ∀ y∈Z,finrank K (W y)=l) :
    (∑ b : ℙ K V,(memberships W Z b:ℝ)) =
      (Z.card:ℝ)*(∑ i∈Finset.range l,(Nat.card K:ℝ)^i) := by
  simp only [memberships,←Finset.sum_boole]
  rw [Finset.sum_comm]
  have hh (y : Y) (hy : y∈Z) :
      (∑ b : ℙ K V,if b.submodule≤W y then (1:ℝ) else 0)=
        ∑ i∈Finset.range l,(Nat.card K:ℝ)^i := by
    rw [Finset.sum_boole,subspace_finset_card,hW y hy]
    push_cast
    rfl
  rw [Finset.sum_congr rfl hh,Finset.sum_const,nsmul_eq_mul]

lemma q_mul_geometric_bound (q : ℝ) (hq : 2≤q) (l : ℕ) :
    q*(∑ i∈Finset.range l,q^i)≤2*q^l := by
  have hp := pow_nonneg (by linarith : 0≤q) l
  have hs := Finset.sum_nonneg (fun i (_ : i∈Finset.range l) => pow_nonneg (by linarith : 0≤q) i)
  have he := geom_sum_mul q l
  have hn := mul_nonneg hs (by linarith : 0≤q-2)
  nlinarith

theorem popular_count (W : Y → Submodule K V) (Z : Finset Y) (hZ : Z.Nonempty)
    (l : ℕ) (hW : ∀ y∈Z,finrank K (W y)=l) :
    ((Finset.univ.filter fun b : ℙ K V =>
      (Z.card:ℝ)/(16*Nat.card K)≤ memberships W Z b).card:ℝ) ≤
      32*(Nat.card K:ℝ)^l := by
  let B := Finset.univ.filter fun b : ℙ K V =>
      (Z.card:ℝ)/(16*Nat.card K)≤ memberships W Z b
  have hq : (2:ℝ)≤Nat.card K := by exact_mod_cast Finite.one_lt_card (α := K)
  have hZpos : (0:ℝ)<Z.card := by exact_mod_cast Finset.card_pos.mpr hZ
  have hs : (B.card:ℝ)*((Z.card:ℝ)/(16*Nat.card K))≤∑ b:ℙ K V,(memberships W Z b:ℝ) := by
    calc
      _ = ∑ b∈B,(Z.card:ℝ)/(16*Nat.card K) := by simp
      _ ≤ ∑ b∈B,(memberships W Z b:ℝ) := Finset.sum_le_sum fun b hb => (Finset.mem_filter.mp hb).2
      _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg (fun _ => by positivity)
  rw [sum_memberships W Z l hW] at hs
  have hm := mul_le_mul_of_nonneg_right hs (show (0:ℝ)≤16*Nat.card K by positivity)
  have he : (B.card:ℝ)*((Z.card:ℝ)/(16*Nat.card K))*(16*Nat.card K)=B.card*Z.card := by
    have hq0 : (Nat.card K:ℝ)≠0 := by linarith
    field_simp
  rw [he] at hm
  have hgeom := q_mul_geometric_bound (Nat.card K:ℝ) hq l
  have hc : (B.card:ℝ)*Z.card ≤ (32*(Nat.card K:ℝ)^l)*Z.card := by
    nlinarith [mul_le_mul_of_nonneg_right hgeom (show (0:ℝ)≤16*Z.card by positivity)]
  change (B.card:ℝ) ≤ 32*(Nat.card K:ℝ)^l
  exact (mul_le_mul_iff_left₀ hZpos).mp (by simpa only [mul_comm] using hc)

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ChooseLevel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Fintype (ℙ K (Dual K V))] in
lemma coannihilator_card_bound (hdim : finrank K V=5)
    (W : Submodule K (Dual K V)) (r : ℕ) (hr : finrank K W=r) (hr4 : r≤4) :
    ((Finset.univ.filter fun a : ℙ K V => a.submodule≤W.dualCoannihilator).card:ℝ)≤
      2*(Nat.card K:ℝ)^(4-r) := by
  have hd := Subspace.finrank_add_finrank_dualCoannihilator_eq W
  rw [hr,hdim] at hd
  have hdc : finrank K W.dualCoannihilator=5-r := by omega
  have hcard : ((Finset.univ.filter fun a : ℙ K V => a.submodule≤W.dualCoannihilator).card:ℝ)=
      ∑ i∈Finset.range (5-r),(Nat.card K:ℝ)^i := by
    rw [subspace_finset_card,hdc]
    push_cast
    rfl
  rw [hcard]
  have hq : (2:ℝ)≤Nat.card K := by exact_mod_cast Finite.one_lt_card (α := K)
  have hh:=q_mul_geometric_bound (Nat.card K:ℝ) hq (5-r)
  have he : 5-r=(4-r)+1 := by omega
  rw [he,pow_succ] at hh
  rw [he]
  nlinarith

end

open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ScanRecordPresent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

open Module SharpRamseyFive.ProjectiveIncidence
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
local instance finiteMarkingDecEq (N : ℕ) : DecidableEq (Fin N) := Classical.decEq _

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_TwoScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.Marking

open Module SharpRamseyFive.ProjectiveIncidence
open scoped Classical LinearAlgebra.Projectivization BigOperators
local instance concreteMarkingDecEq (N : ℕ) : DecidableEq (Fin N) := Classical.decEq _

end SharpRamseyFive.Marking

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_MarkingEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
local instance markingEndpointsPointDecEq : DecidableEq (ℙ K V) := Classical.decEq _
local instance markingEndpointsDualDecEq : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _

end

open Module SharpRamseyFive.ProjectiveIncidence
open scoped Classical LinearAlgebra.Projectivization BigOperators

def clampParameter (q M : ℝ) : ℝ := max (Real.log q) (min (4*Real.log q) (Real.log M))

lemma exp_clampParameter {q M : ℝ} (hq : 0<q) (hM : 0<M) :
    Real.exp (clampParameter q M)=max q (min (q^4) M) := by
  unfold clampParameter
  rw [Real.exp_monotone.map_max, Real.exp_monotone.map_min, Real.exp_log hq,
    show (4:ℝ)*Real.log q=(4:ℕ)*Real.log q by norm_num, Real.exp_nat_mul,
    Real.exp_log hq, Real.exp_log hM]

lemma clampParameter_bounds {q M : ℝ} (hq : 1≤q) :
    Real.log q ≤ clampParameter q M ∧ clampParameter q M≤4*Real.log q := by
  have hs : 0≤Real.log q := Real.log_nonneg hq
  exact ⟨le_max_left _ _,max_le (by linarith) (min_le_left _ _)⟩

lemma clamped_reciprocal_caps {q M A B : ℝ} (hq : 1≤q) (hM : 0<M)
    (hA : 0≤A) (_hB : 0≤B) (hAa : A≤2*q^4) (hBa : B≤2*q^4)
    (hAM : A*M≤16*q^5) (hBM : B≤5*M) :
    A≤32*Real.exp (5*Real.log q-clampParameter q M) ∧
    B≤32*Real.exp (clampParameter q M) := by
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hq4 : q≤q^4 := by nlinarith [sq_nonneg (q-1), sq_nonneg (q^2-1)]
  have hexp := exp_clampParameter hq0 hM
  have hnum : Real.exp (5*Real.log q)=q^5 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hq0] using Real.exp_nat_mul (Real.log q) 5
  rw [Real.exp_sub, hnum, hexp, ←mul_div_assoc]
  by_cases hMq : M≤q
  · have he : max q (min (q^4) M)=q := max_eq_left ((min_le_right _ _).trans hMq)
    rw [he]
    constructor
    · apply (le_div_iff₀ hq0).mpr
      nlinarith [mul_le_mul_of_nonneg_right hAa hq0.le, pow_pos hq0 5]
    · linarith
  · by_cases hM4 : M≤q^4
    · have he : max q (min (q^4) M)=M := by rw [min_eq_right hM4, max_eq_right (le_of_not_ge hMq)]
      rw [he]
      constructor
      · apply (le_div_iff₀ hM).mpr
        nlinarith [pow_pos hq0 5]
      · linarith
    · have he : max q (min (q^4) M)=q^4 := by rw [min_eq_left (le_of_not_ge hM4),max_eq_right hq4]
      rw [he]
      constructor
      · apply (le_div_iff₀ (pow_pos hq0 4)).mpr
        have hh := mul_le_mul_of_nonneg_left (le_of_not_ge hM4) hA
        nlinarith [pow_pos hq0 5]
      · linarith

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
local instance clampedPointDecEq : DecidableEq (ℙ K V) := Classical.decEq _
local instance clampedDualDecEq : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _

end SharpRamseyFive.Marking

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReciprocalBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence
open scoped Classical LinearAlgebra.Projectivization BigOperators

def BandCondition (σ K u : ℝ) (i : Fin 7) : Prop :=
  if i.val%2=0 then |u-((i.val/2+1:ℕ):ℝ)*σ|≤K
  else ((i.val/2+1:ℕ):ℝ)*σ+K<u ∧ u<((i.val/2+2:ℕ):ℝ)*σ-K

lemma exists_reciprocal_band {σ K u : ℝ} (hK : 0≤K)
    (hlo : σ≤u) (hhi : u≤4*σ) : ∃ i : Fin 7,BandCondition σ K u i := by
  by_cases h0 : u≤σ+K
  · refine ⟨0,?_⟩
    simp only [BandCondition];norm_num
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  by_cases h1 : u<2*σ-K
  · refine ⟨1,?_⟩
    norm_num [BandCondition]
    exact ⟨by linarith,h1⟩
  by_cases h2 : u≤2*σ+K
  · refine ⟨2,?_⟩
    norm_num [BandCondition]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  by_cases h3 : u<3*σ-K
  · refine ⟨3,?_⟩
    norm_num [BandCondition]
    exact ⟨by linarith,h3⟩
  by_cases h4 : u≤3*σ+K
  · refine ⟨4,?_⟩
    norm_num [BandCondition]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  by_cases h5 : u<4*σ-K
  · refine ⟨5,?_⟩
    norm_num [BandCondition]
    exact ⟨by linarith,h5⟩
  · refine ⟨6,?_⟩
    norm_num [BandCondition]
    exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma popular_reciprocal_caps {q A B : ℝ} {r s : ℕ} (hq : 1≤q)
    (hr : 1 ≤ r) (hr4 : r≤4) (hrs : r+s≤5)
    (hA : A≤32*q^s) (hB : B≤32*q^r) :
    Real.log q≤(r:ℝ)*Real.log q ∧ (r:ℝ)*Real.log q≤4*Real.log q ∧
    A≤32*Real.exp (5*Real.log q-(r:ℝ)*Real.log q) ∧
    B≤32*Real.exp ((r:ℝ)*Real.log q) := by
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hσ := Real.log_nonneg hq
  have he (n : ℕ) : Real.exp ((n:ℝ)*Real.log q)=q^n := by
    rw [Real.exp_nat_mul,Real.exp_log hq0]
  refine ⟨?_,?_,?_,?_⟩
  · have : (1:ℝ) ≤ r := by exact_mod_cast hr
    nlinarith
  · have : (r:ℝ)≤4 := by exact_mod_cast hr4
    nlinarith
  · have ht : (s:ℝ)*Real.log q≤5*Real.log q-(r:ℝ)*Real.log q := by
      have : (r:ℝ)+s≤5 := by exact_mod_cast hrs
      nlinarith
    exact hA.trans (mul_le_mul_of_nonneg_left (by rw [←he s];exact Real.exp_le_exp.mpr ht) (by norm_num))
  · simpa only [he] using hB

end

open Module SharpRamseyFive.ProjectiveIncidence
open scoped Classical LinearAlgebra.Projectivization BigOperators

end SharpRamseyFive.Marking

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReciprocalLevelProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

def reciprocalBadMass (s d C₀ : ℝ) : ℝ := Real.exp (-s)+50*(d+C₀)/s

end
end SharpRamseyFive.Marking

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_SurvivingWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.PivotTree
open TreeCodec
open scoped Classical
noncomputable section
variable {w : ℕ}

def survivingOriginal (E : Finset (Fin w)) (hE : E.Nonempty) : Fin (E.card+1)→Fin w :=
  fun i=>E.orderEmbOfFin rfl ⟨min i.val (E.card-1),by
    have h:=Finset.card_pos.mpr hE
    omega⟩

lemma survivingOriginal_mem (E : Finset (Fin w)) (hE : E.Nonempty) (i : Fin (E.card+1)) :
    survivingOriginal E hE i∈E := Finset.orderEmbOfFin_mem ..

end
end SharpRamseyFive.PivotTree

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_SurvivingWindowCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
local instance swcProp (P : Prop) : Decidable P := Classical.propDecidable P
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_WindowDeletionCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Windows
open scoped Classical BigOperators
noncomputable section
variable {w r : ℕ}
local instance deletionTargetDE : DecidableEq (Fin w×Fin (2*r)) := Classical.decEq _

end
end SharpRamseyFive.Windows

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
local instance allWindowProp (P : Prop) : Decidable P := Classical.propDecidable P
local instance allWindowTDE (w n : ℕ) : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_AllWindowCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree Marking Windows
open ParameterHierarchy Filter
open scoped Classical BigOperators LinearAlgebra.Projectivization Topology NNReal
noncomputable section

local instance costBDE_ra49b6c_1 (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
def windowCodeBudget (σ q P b : ℝ) (w H : ℕ) : ℝ :=
  let X:=nodeChargeConstant*q*P
  Real.log (w+1)+
    (X*H*(3*σ+Real.log 4+(b+1+2*Real.log (320/((9:ℝ)/100000)+320))*w)+
      (Real.log 2+X*(b+1+P))*w)+(2*(w:ℝ)+1)*Real.log 2

end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Streams_SelectedTuple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open scoped BigOperators Classical
variable {α ι : Type*} [Fintype α] [Fintype ι]

noncomputable def completionEquiv (I : Finset ι) (v : I → α) :
    {s : ι → α // ∀ i : I,s i.val = v i} ≃ ({i : ι // i ∉ I} → α) where
  toFun s i := s.val i.val
  invFun w := ⟨fun i => if h : i ∈ I then v ⟨i,h⟩ else w ⟨i,h⟩,by
    intro i
    simp only [i.property, dite_true]⟩
  left_inv s := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ I
    · simp only [hi,dite_true]
      exact (s.property ⟨i,hi⟩).symm
    · simp only [hi,dite_false]
  right_inv w := by
    funext i
    simp only [i.property,dite_false]

end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_StageState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open scoped Classical BigOperators
noncomputable section
variable {α β γ Ω κ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype Ω] [Fintype κ]

def reverseEmbedding {n l : ℕ} (e : Fin l↪o Fin n) : Fin l↪o Fin n where
  toFun i:=(e i.rev).rev
  inj' := Fin.rev_injective.comp (e.injective.comp Fin.rev_injective)
  map_rel_iff' := by
    intro i j
    change (e i.rev).rev≤(e j.rev).rev ↔ i≤j
    rw [Fin.rev_le_rev,e.le_iff_le,Fin.rev_le_rev]

end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_MarkingClassDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] {N : ℕ}
local instance classDomainPointDE : DecidableEq (ℙ K V) := Classical.decEq _
local instance classDomainDualDE : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _
local instance classDomainDualDualDE : DecidableEq (ℙ K (Dual K (Dual K V))) := Classical.decEq _

lemma endpoint_card_mono {A B : Type*} [DecidableEq A] [DecidableEq B]
    {S T : Finset (A×B)} (h : S ⊆ T) :
    ((S.image Prod.fst).card:ℝ) ≤ (T.image Prod.fst).card ∧
    ((S.image Prod.snd).card:ℝ) ≤ (T.image Prod.snd).card := by
  constructor  <;> exact_mod_cast Finset.card_le_card (Finset.image_subset_image h)

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_MarkingClasses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section

abbrev SlotClass := Fin 7 ⊕ (Fin 7 ⊕ (Fin 5 × Fin 5))

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_TwoScanContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence
open scoped Classical LinearAlgebra.Projectivization BigOperators
local instance scanContextDecEq (N : ℕ) : DecidableEq (Fin N) := Classical.decEq _
end

open Module SharpRamseyFive.ProjectiveIncidence
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V κ : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype κ] {N l : ℕ}
local instance markedClassFinDE (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

local instance markedClassPointDE_ra49b6c_1 : DecidableEq (ℙ K V) := Classical.decEq _
local instance markedClassDualDE_ra49b6c_1 : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _
def expensiveBound (K V : Type) [Field K] [AddCommGroup V] [Module K V]
    [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] : ℝ :=
  800*(Nat.card K:ℝ)*(Real.log (1+Fintype.card (ℙ K (Dual K V)))+
    Real.log (1+Fintype.card (ℙ K V)))

end SharpRamseyFive.Marking

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_MarkedStreamExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence
open SharpRamseyFive.SelectedTuple
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n l : ℕ} {admissible : (Fin N→α)→Prop}
local instance streamClassFinDE (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_MarkedActualBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence SelectedTuple
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n l : ℕ} {admissible : (Fin N→α)→Prop}
local instance mabFinDE (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_AllHistoryWindowLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
local instance allHistBDE_ra49b6c_1 (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance allHistTDE (w n : ℕ) : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_HistoryPrivateStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence Windows Marking
open scoped Classical LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype Ω] [Fintype κ] [Fintype α]
  {N w n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}
local instance hpsBDE : DecidableEq (Fin w×Bool) := Classical.decEq _
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_SelectedRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence Windows Marking
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {Ω κ α β : Type} [Fintype Ω] [Fintype κ] [Fintype α] [Fintype β]
  {N n l : ℕ} {admissible : (Fin N→α)→Prop}
local instance srFinDE (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_DomainTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
local instance dtPDE : DecidableEq (ℙ K V) := Classical.decEq _
local instance dtDDE : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _
local instance dtDDDE : DecidableEq (ℙ K (Dual K (Dual K V))) := Classical.decEq _

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Streams_PreparedStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence Windows Marking
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n l : ℕ} {admissible : (Fin N→α)→Prop}
local instance psFinDE (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_HighPairVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.HighSamples
open Module SharpRamseyFive.ProjectiveIncidence
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

abbrev SampleFlag := ℙ K V × ℙ K (Dual K V)

end
end SharpRamseyFive.HighSamples

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_HighSampleRetention
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence
open SharpRamseyFive.HighSamples
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
local instance highRepDE : DecidableEq (ℙ K V) := Classical.decEq _
local instance highRepDualDE : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReciprocalDomainCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module ProjectiveIncidence Windows
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype I]

variable {B A T : Type} [Fintype B] [Fintype A] [Fintype T] [Nonempty A]
local instance reciprocalHistoryDE : DecidableEq ((B×A)⊕T) := Classical.decEq _

end
end

open Module ProjectiveIncidence Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical LinearAlgebra.Projectivization BigOperators

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Streams_HighActualExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.HighSamples
open Module SharpRamseyFive.ProjectiveIncidence
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype Ω] [Fintype κ]

local instance highExtractionFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

end
end SharpRamseyFive.HighSamples

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_HighWindowStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence Windows Marking HighSamples
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}
local instance hwsBDE : DecidableEq (Fin 1×Bool) := Classical.decEq _
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_HighDomainEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module ProjectiveIncidence HighSamples
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
local instance hdePDE : DecidableEq (ℙ K V) := Classical.decEq _
local instance hdeDDE : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _

end
end

open Module SharpRamseyFive.ProjectiveIncidence
open SharpRamseyFive.HighSamples SharpRamseyFive.Windows
open scoped Classical LinearAlgebra.Projectivization BigOperators

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_FinalMarking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
local instance finalMarkingDecEq (N : ℕ) : DecidableEq (Fin N) := Classical.decEq _
end
end SharpRamseyFive.Marking

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence Windows Marking
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
local instance cfmFinDE (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_WindowCodeDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence Windows ReverseCap ScoreGeometry PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
local instance wcdBDE_ra49b6c_1 (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
def codeDomainSlack (k s : ℝ) := k+2*s+Real.log 4+1+Real.log (2*(320/((9:ℝ)/100000)+320)^2)
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReciprocalStageArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real Marking ProjectiveIncidence SelectedTuple
open scoped Topology NNReal
noncomputable section

def domainSlackConstant : ℝ := 4+Real.log 4+Real.log (2*(320/(9/100000)+320)^2)

end
end SharpRamseyFive.ParameterHierarchy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_IteratedBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real
open scoped Topology
noncomputable section

def iterD (σ η : ℝ) : ℕ→ℝ
  | 0 => σ^beta η*(1+10*σ*σ^(-η))
  | n+1 => σ^beta η*(1+iterD σ η n*σ^(-η/3)+
      domainSlackConstant*iterD σ η n*σ^(6*beta η)*σ^(-η))
def iterA (σ η : ℝ) : ℕ→ℝ
  | 0 => 0
  | n+1 => iterD σ η n*σ^(-η/3)
def iterDelta (σ η : ℝ) : ℕ→ℝ
  | 0 => 10*σ
  | n+1 => domainSlackConstant*iterD σ η n*σ^(6*beta η)
end
end SharpRamseyFive.ParameterHierarchy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_BandEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Filter Real
noncomputable section
def bandLo (σ width : ℝ) (b : Fin 7) : ℝ :=
  if b.val%2=0 then ((b.val/2+1:ℕ):ℝ)*σ-width else σ
def bandHi (σ width : ℝ) (b : Fin 7) : ℝ :=
  if b.val%2=0 then ((b.val/2+1:ℕ):ℝ)*σ+width else 4*σ
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ClassifiedStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence SelectedTuple
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n l : ℕ} {admissible : (Fin N→α)→Prop}
local instance csFinDE (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_WindowStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence Windows Marking PivotTree ReverseCap ScoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N w n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}
local instance awsBDE : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance awsTDE : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_CodedWindowStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence Windows Marking PivotTree ReverseCap ScoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N w n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}
local instance cwsBDE_ra49b6c_1 : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance cwsTDE : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReciprocalNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Filter Asymptotics Real
open scoped Topology
noncomputable section

def publicRetentionError (σ b H : ℝ) : ℝ :=
  let q:=Real.exp σ
  let ε:=σ^(-2000*b)/q
  H*(20*H*(50*q/(9*((9/100000)*(9/10))))*(4*Real.exp 1)^2*(320016*ε)+
    (q/(σ^(-1000*b)))*(4*Real.exp 1)^2*(320016*ε)+5*Real.exp (-q))+
    (20*H+2)*(50*q/(9*((9/100000)*(9/10))))*(4*Real.exp 1)*(160008*ε)

def publicRetentionEnvelope (σ b : ℝ) : ℝ :=
  (20*(50/(9*((9/100000)*(9/10))))*(4*Real.exp 1)^2*320016)*σ^(-1998*b)+
    ((4*Real.exp 1)^2*320016)*σ^(-999*b)+5*(σ^b*Real.exp (-σ))+
    (20*(50/(9*((9/100000)*(9/10))))*(4*Real.exp 1)*160008)*σ^(-1999*b)+
    (2*(50/(9*((9/100000)*(9/10))))*(4*Real.exp 1)*160008)*σ^(-2000*b)

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_WindowTargetRetention
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal Topology
noncomputable section
local instance (priority := high) winRetPropDE (P : Prop) : Decidable P := Classical.propDecidable P

end
end

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal Topology

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_WindowSmallFailure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

open Module ProjectiveIncidence Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal Topology
noncomputable section
local instance arlBDE_ra49b6c_1 (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance arlTDE (w n : ℕ) : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
end

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ClassPrepared
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence SelectedTuple
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n l : ℕ} {admissible : (Fin N→α)→Prop}
local instance cpFinDE (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

end
end SharpRamseyFive.Marking

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence Windows Marking
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
local instance cmFinDE (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_CompressionStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence Windows Marking Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal
noncomputable section

local instance acsFinDE_ra49b6c_1 (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
def markingStageConstant (c : ℝ) : ℝ:=(39*(19201+Real.log 800))/(c/200)
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_TerminalStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple

section
open Module ProjectiveIncidence Windows Marking Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
local instance tsFinDE (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

end

end

open scoped Classical BigOperators
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]

def firstWitness {N n : ℕ} (hn : n≤N) (P : (Fin N→α)→(Fin n↪o Fin N)→Prop)
    (s : Fin N→α) : Fin n↪o Fin N :=
  if h : ∃ e,P s e then h.choose else
    { toFun := fun i=>⟨i.val,lt_of_lt_of_le i.isLt hn⟩
      inj' := by intro i j h; exact Fin.ext (congrArg (fun x : Fin N=>x.val) h)
      map_rel_iff' := by intro i j; rfl }

end

end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FlagGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FlagConstruction

open scoped LinearAlgebra.Projectivization
open Module

variable {K : Type*} [Field K]
abbrev Space (K : Type*) := Fin 5 → K
abbrev Point (K : Type*) [Field K] := ℙ K (Space K)
abbrev DualPoint (K : Type*) [Field K] := ℙ K (Module.Dual K (Space K))

def Incident (a : Point K) (b : DualPoint K) : Prop :=
  a.submodule ≤ LinearMap.ker b.rep

abbrev Flag (K : Type*) [Field K] :=
  {ab : Point K × DualPoint K // Incident ab.1 ab.2}

def graph {N : ℕ} (X : Fin N → Flag K) : SimpleGraph (Fin N) where
  Adj i j := (i < j ∧ Incident (X i).1.1 (X j).1.2 ∧
      ¬ Incident (X j).1.1 (X i).1.2) ∨
    (j < i ∧ Incident (X j).1.1 (X i).1.2 ∧
      ¬ Incident (X i).1.1 (X j).1.2)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro i; simp⟩

end SharpRamseyFive.FlagConstruction

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_PolarIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence Windows Marking Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section

def iterLength (n : ℕ) : ℕ→ℕ
  | 0 => n
  | i+1 => iterLength n i/20000

end
end SharpRamseyFive.SelectedTuple

end OAI
end


