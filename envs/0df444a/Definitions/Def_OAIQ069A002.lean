-- Prove2me | Definitions.Def_OAIQ069A002
-- name    : OAIQ069A002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T01:43:04.102506+00:00
-- url     : https://prove2.me/theorems/b40c6957-516b-4e26-915c-dedaf229dc11
-- title:
--   Definitions bundle OAIQ069A002 of the split of OpenAI, Hardness of finding large independent sets in three-colorable graphs (result family 106)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LargeIndependentSets.mainTheoremReal`, carved from OpenAI's openai/math development (OpenAI, *Hardness of finding large independent sets in three-colorable graphs (result family 106)*, OpenAI Math Release, September 24, 2026, result family 106, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 560 declarations of OpenAI's Lean: 357 definitions, 11 inductive types or structures, 33 instances and 159 theorems. The definitions and types are `OAI.IndependentSetsGames.Foundations.CorrelatedSampling.eventMass`, `OAI.IndependentSetsGames.Foundations.CorrelatedSampling.firstAccepted`, `OAI.IndependentSetsGames.Foundations.CorrelatedSampling.firstHitWeight`, `OAI.IndependentSetsGames.Foundations.CorrelatedSampling.geometricMass`, `OAI.IndependentSetsGames.Foundations.CorrelatedSampling.goodFirstIndicator`, `OAI.IndependentSetsGames.Foundations.CorrelatedSampling.goodFirstMass`, `OAI.IndependentSetsGames.Foundations.CorrelatedSampling.goodLabel`, `OAI.IndependentSetsGames.Foundations.CorrelatedSampling.localDiagonal`, `OAI.IndependentSetsGames.Foundations.CorrelatedSampling.localSample`, `OAI.IndependentSetsGames.Foundations.CorrelatedSampling.profileThresholds`, `OAI.IndependentSetsGames.Foundations.CorrelatedSampling.totalVariation`, `OAI.IndependentSetsGames.Foundations.CorrelatedSampling.traceAverage`, `OAI.IndependentSetsGames.Foundations.CorrelatedSampling.uniformRejectionRate`, `OAI.IndependentSetsGames.Foundations.CorrelatedSampling.unionMass`, `OAI.IndependentSetsGames.Foundations.Games.KernelSampling.Seed`, `OAI.IndependentSetsGames.Foundations.Games.KernelSampling.completedLeft`, `OAI.IndependentSetsGames.Foundations.Games.KernelSampling.completedRight`, `OAI.IndependentSetsGames.Foundations.Games.KernelSampling.readLeft`, `OAI.IndependentSetsGames.Foundations.Games.KernelSampling.readRight`, `OAI.IndependentSetsGames.Foundations.Information.IsProbability`, `OAI.IndependentSetsGames.Foundations.Information.SupportedBy`, `OAI.IndependentSetsGames.Foundations.Information.conditionalKernel`, `OAI.IndependentSetsGames.Foundations.Information.coordinateMarginal`, `OAI.IndependentSetsGames.Foundations.Information.firstMarginal`, `OAI.IndependentSetsGames.Foundations.Information.hellingerSquared`, `OAI.IndependentSetsGames.Foundations.Information.independentProduct`, `OAI.IndependentSetsGames.Foundations.Information.posterior`, `OAI.IndependentSetsGames.Foundations.Information.posteriorOrOriginal`, `OAI.IndependentSetsGames.Foundations.Information.relativeEntropy`, `OAI.IndependentSetsGames.Foundations.Information.secondMarginal`, `OAI.IndependentSetsGames.Foundations.Information.totalVariation`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Addresses.values`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Cleanup.actualCost`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Cleanup.clearTapes`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.CompareLoop.comparisonTime`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Initialization.time`, `OAI.IndependentSetsGames.Foundations.PCP.AssignmentTester.disagree`, `OAI.IndependentSetsGames.Foundations.PCP.AssignmentTester.distance`, `OAI.IndependentSetsGames.Foundations.PCP.AssignmentTester.truth`, `OAI.IndependentSetsGames.Foundations.PCP.CayleySampling.FalseFiber` and 328 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `IndependentSets_Encoding_BinaryEvents`, `IndependentSets_Encoding_BinaryNameTables`, `IndependentSets_Encoding_BinaryNormalize`, `IndependentSets_Encoding_BinarySyntax`, `IndependentSets_Encoding_GeometryExpr`, `IndependentSets_Encoding_GraphPrinter`, `IndependentSets_Encoding_Normalizer`, `IndependentSets_Expansion_CayleySpectral`, `IndependentSets_Expansion_CayleyTailCount`, `IndependentSets_Expansion_CloudRounding`, `IndependentSets_Expansion_Expanders`, `IndependentSets_Expansion_Indicators`, `IndependentSets_Expansion_LazySmoothing`, `IndependentSets_Expansion_PoweringDecoding`, `IndependentSets_Expansion_PoweringGap`, `IndependentSets_Expansion_PoweringNumeric`, `IndependentSets_Expansion_PoweringPortReindex`, `IndependentSets_Expansion_PoweringReturn`, `IndependentSets_Expansion_PoweringTableLayout`, `IndependentSets_Expansion_PoweringWitness`, `IndependentSets_Expansion_SpectralReturn`, `IndependentSets_Expansion_Supported`, `IndependentSets_Expansion_Supported2`, `IndependentSets_Expansion_ZigzagSpectral`, `IndependentSets_Fourier_Fourier`, `IndependentSets_Geometry_CoordinateDerivative`, `IndependentSets_Geometry_CoordinateMean`, `IndependentSets_Geometry_DeletedLayerEquiv`, `IndependentSets_Geometry_GeometryAntipodes`, `IndependentSets_Geometry_GeometryDistance`, `IndependentSets_Geometry_GeometryLocations`, `IndependentSets_Geometry_GeometryNaming`, `IndependentSets_Geometry_GeometryOutput`, `IndependentSets_Geometry_PatternInvariant`, `IndependentSets_Geometry_RationalLaw`, `IndependentSets_Geometry_Uniform`, `IndependentSets_Geometry_Witness`, `IndependentSets_Machines_Initialization`, `IndependentSets_Machines_PCPGapMachine`, `IndependentSets_PCP_Addresses`, `IndependentSets_PCP_AssignmentTester`, `IndependentSets_PCP_BoundedIteration`, `IndependentSets_PCP_CircleRound`, `IndependentSets_PCP_ClausePolynomial`, `IndependentSets_PCP_Cleanup`, `IndependentSets_PCP_CodeComposition`, `IndependentSets_PCP_CompareLoop`, `IndependentSets_PCP_EmitRows`, `IndependentSets_PCP_GeometryPointTable`, `IndependentSets_PCP_LabelCoverData`, `IndependentSets_PCP_Minimum`, `IndependentSets_PCP_TargetLC`, `IndependentSets_Reduction_ArbitraryRealJunta`, `IndependentSets_Reduction_AuxiliaryJointMeasurable`, `IndependentSets_Reduction_Bits`, `IndependentSets_Reduction_CellLaw`, `IndependentSets_Reduction_Circle`, `IndependentSets_Reduction_CircleCost`, `IndependentSets_Reduction_Cube`, `IndependentSets_Reduction_DeletedProjection`, `IndependentSets_Reduction_EnumerationSimple`, `IndependentSets_Reduction_ExtensionLaw`, `IndependentSets_Reduction_FiniteParameterSelection`, `IndependentSets_Reduction_FiniteScan`, `IndependentSets_Reduction_FloydLoop`, `IndependentSets_Reduction_Full`, `IndependentSets_Reduction_FullAbsorptionSquare`, `IndependentSets_Reduction_Heavy`, `IndependentSets_Reduction_IndexedBlocks`, `IndependentSets_Reduction_InfluenceSqParamMeasurable`, `IndependentSets_Reduction_IntegerEdgeTest`, `IndependentSets_Reduction_Law`, `IndependentSets_Reduction_ListIndex`, `IndependentSets_Reduction_MapEquiv`, `IndependentSets_Reduction_Mix`, `IndependentSets_Reduction_Mixed`, `IndependentSets_Reduction_OccurrenceTuple`, `IndependentSets_Reduction_Parameters`, `IndependentSets_Reduction_RowBitsEquiv`, `IndependentSets_Reduction_SamplerParameters`, `IndependentSets_Reduction_Simple`, `IndependentSets_Reduction_SimplexLaw`, `IndependentSets_Reduction_Small`, `IndependentSets_Reduction_SquareNorm`, `IndependentSets_Reduction_SubchainBase`, `IndependentSets_Reduction_SubchainView`, `IndependentSets_Reduction_SwapCoords`, `IndependentSets_Reduction_SwapOccurrence`, `IndependentSets_Reduction_TargetRead`, `IndependentSets_Reduction_ThresholdDecidable`, `IndependentSets_Reduction_Total`, `IndependentSets_Reduction_UniformLaw`, `IndependentSets_Reduction_WalkLength`, `IndependentSets_Repetition_Basic2`, `IndependentSets_Repetition_CayleySampling`, `IndependentSets_Repetition_Conditionals`, `IndependentSets_Repetition_CoordinateCompletion`, `IndependentSets_Repetition_DistributionIdentities`, `IndependentSets_Repetition_Finite`, `IndependentSets_Repetition_FiniteGame`, `IndependentSets_Repetition_FiniteTrials`, `IndependentSets_Repetition_KernelSampling`, `IndependentSets_Repetition_MaskedVariation`, `IndependentSets_Repetition_Mixture`, `IndependentSets_Repetition_Overlap`, `IndependentSets_Repetition_PartialReveal`, `IndependentSets_Repetition_Pinsker`, `IndependentSets_Repetition_ProfileBounds`, `IndependentSets_Repetition_ProfileCorrection`, `IndependentSets_Repetition_Rectangle`, `IndependentSets_Repetition_Rectangle2`, `IndependentSets_Repetition_Reveal`, `IndependentSets_Repetition_RevealFactorization`, `IndependentSets_Repetition_Scalar`, `IndependentSets_Repetition_ScalarCell`, `IndependentSets_Repetition_ScalarSampleInfluence`, `IndependentSets_Repetition_SelectedInformation`, `IndependentSets_Repetition_SelectedJoint`, `IndependentSets_Repetition_SelectedMarginal`, `IndependentSets_Repetition_SelectedProfileBudget`, `IndependentSets_Repetition_SelectedProfiles`, `IndependentSets_Repetition_SelectionSequence`, `IndependentSets_Repetition_SharedSampling`, `IndependentSets_Repetition_SideInformation`, `IndependentSets_Repetition_TraceLaw`.
--
--   **Imports.** It imports the published bundle `Def_IndependentSets`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ069A004` and `OAIQ069A005`; the statement `OAI.LargeIndependentSets.actual_aligned_fiber`; the proof of `OAI.LargeIndependentSets.actual_aligned_fiber`.
-- source:
--   OpenAI, Hardness of finding large independent sets in three-colorable graphs (result family 106), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 106; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Hardness-of-finding-large-independent-sets-in-three-colorable-graphs-September-24-2026/Hardness-of-finding-large-independent-sets-in-three-colorable-graphs-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 1581d4c

import Mathlib
import Definitions.Def_IndependentSets

section
-- module Solutions.OAIQ069_INDEP.Compat
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
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_ListIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open Filter

abbrev ListIndex (s : ℕ) (X : Type*) :=
  {I : Finset X // I.Nonempty ∧ I.card ≤ s}

abbrev ListSlot (s d : ℕ) (X : Type*) := ListIndex s X × Fin d

abbrev EqualityData (s d : ℕ) (X : Type*) := ListSlot s d X → ListSlot s d X → Bool

def IsPattern {s d : ℕ} {X : Type*} [LinearOrder X]
    (C : EqualityData s d X) : Prop :=
  (∀ a b, C a b = true → C b a = true) ∧
  (∀ a b c, C a b = true → C b c = true → C a c = true) ∧
  (∀ a b, C a b = true → a.1 = b.1 → a.2 = b.2) ∧
  (∀ a b, (∀ x ∈ a.1.val, ∀ y ∈ b.1.val, x < y) → C a b = false)

abbrev ListPattern (s d : ℕ) (X : Type*) [LinearOrder X] :=
  {C : EqualityData s d X // IsPattern C}

noncomputable instance instFintypeListPattern (s d : ℕ) (X : Type*) [LinearOrder X] [Fintype X] :
    Fintype (ListPattern s d X) := Fintype.ofFinite _

instance instInhabitedListPattern (s d : ℕ) (X : Type*) [LinearOrder X] : Inhabited (ListPattern s d X) :=
  ⟨⟨fun _ _ => false, by simp [IsPattern]⟩⟩

def ListIndex.map {s : ℕ} {X Y : Type*} (e : X ↪ Y) (I : ListIndex s X) :
    ListIndex s Y :=
  ⟨I.val.map e, I.property.1.map, by simpa using I.property.2⟩

def ListSlot.map {s d : ℕ} {X Y : Type*} (e : X ↪ Y) (a : ListSlot s d X) :
    ListSlot s d Y := (ListIndex.map e a.1, a.2)

def ListPattern.restrict {s d : ℕ} {X Y : Type*} [LinearOrder X] [LinearOrder Y]
    (e : X ↪o Y) (C : ListPattern s d Y) : ListPattern s d X :=
  ⟨fun a b => C.val (ListSlot.map e.toEmbedding a) (ListSlot.map e.toEmbedding b), by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b h; exact C.property.1 _ _ h
    · intro a b c hab hbc; exact C.property.2.1 _ _ _ hab hbc
    · intro a b h hab
      exact C.property.2.2.1 _ _ h (congrArg (ListIndex.map e.toEmbedding) hab)
    · intro a b hsep
      apply C.property.2.2.2
      intro x hx y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hy
      exact e.strictMono (hsep i hi j hj)⟩

noncomputable def patternCutValues {s d : ℕ} (C : ListPattern s d ℚ)
    (a : ListSlot s d ℚ) : Set ℝ :=
  insert ((a.1.val.min' a.1.property.1 : ℚ) : ℝ)
    {x | ∃ b : ListSlot s d ℚ, C.val a b = true ∧
      x = (b.1.val.min' b.1.property.1 : ℚ)}

noncomputable def patternCut {s d : ℕ} (C : ListPattern s d ℚ)
    (a : ListSlot s d ℚ) : ℝ := sSup (patternCutValues C a)

noncomputable def ListIndex.mapEquiv {s : ℕ} {X Y : Type*}
    [LinearOrder X] [LinearOrder Y] (e : X ≃o Y) : ListIndex s X ≃ ListIndex s Y where
  toFun := ListIndex.map e.toEmbedding
  invFun := ListIndex.map e.symm.toEmbedding
  left_inv I := by
    apply Subtype.ext
    ext x
    simp [ListIndex.map]
  right_inv I := by
    apply Subtype.ext
    ext x
    simp [ListIndex.map]

noncomputable def ListSlot.mapEquiv {s d : ℕ} {X Y : Type*}
    [LinearOrder X] [LinearOrder Y] (e : X ≃o Y) : ListSlot s d X ≃ ListSlot s d Y :=
  (ListIndex.mapEquiv e).prodCongr (Equiv.refl (Fin d))

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_PatternInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open MeasureTheory Set

def PatternInvariant {s d : ℕ} (μ : Measure (ListPattern s d ℚ)) : Prop :=
  ∀ e : ℚ ≃o ℚ, Measure.map (ListPattern.restrict e.toOrderEmbedding) μ = μ

def GloballyAligned {s d : ℕ} (C : ListPattern s d ℚ) : Prop :=
  ∀ a, C.val a a = true → ∃ i : ℚ, ∀ b, C.val a b = true → i ∈ b.1.val

def GoodPatternOn {s d : ℕ} {X : Type*} [LinearOrder X]
    (C : ListPattern s d X) (B : Finset X) : Prop :=
  ∀ a, a.1.val ⊆ B → C.val a a = true → ∃ i ∈ B,
    ∀ b, b.1.val ⊆ B → C.val a b = true → i ∈ b.1.val

noncomputable def ListIndex.inside {s : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (I : ListIndex s X) (h : I.val ⊆ B) : ListIndex s B := by
  classical
  refine ⟨I.val.subtype (· ∈ B), ?_, ?_⟩
  · obtain ⟨x, hx⟩ := I.property.1
    exact ⟨⟨x, h hx⟩, Finset.mem_subtype.mpr hx⟩
  · exact (Finset.card_subtype _ _).trans_le
      ((Finset.card_filter_le _ _).trans I.property.2)

noncomputable def ListSlot.inside {s d : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (a : ListSlot s d X) (h : a.1.val ⊆ B) : ListSlot s d B :=
  (a.1.inside B h, a.2)

noncomputable def liftData {s d : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (C : ListPattern s d B) : EqualityData s d X := by
  classical
  exact fun a b => if ha : a.1.val ⊆ B then
    if hb : b.1.val ⊆ B then C.val (a.inside B ha) (b.inside B hb) else false else false

lemma liftData_true_iff {s d : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (C : ListPattern s d B) (a b : ListSlot s d X) :
    liftData B C a b = true ↔ ∃ ha : a.1.val ⊆ B, ∃ hb : b.1.val ⊆ B,
      C.val (a.inside B ha) (b.inside B hb) = true := by
  classical
  simp only [liftData]
  split_ifs <;> simp_all

noncomputable def ListPattern.lift {s d : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (C : ListPattern s d B) : ListPattern s d X := by
  classical
  refine ⟨liftData B C, ?_, ?_, ?_, ?_⟩
  · intro a b h
    obtain ⟨ha, hb, hab⟩ := (liftData_true_iff B C a b).mp h
    exact (liftData_true_iff B C b a).mpr ⟨hb, ha, C.property.1 _ _ hab⟩
  · intro a b c hab hbc
    obtain ⟨ha, hb, hab⟩ := (liftData_true_iff B C a b).mp hab
    obtain ⟨_, hc, hbc⟩ := (liftData_true_iff B C b c).mp hbc
    exact (liftData_true_iff B C a c).mpr ⟨ha, hc, C.property.2.1 _ _ _ hab hbc⟩
  · intro a b hab habI
    obtain ⟨ha, hb, hab⟩ := (liftData_true_iff B C a b).mp hab
    apply C.property.2.2.1 _ _ hab
    change ListIndex.inside B a.1 ha = ListIndex.inside B b.1 hb
    apply Subtype.ext
    change a.1.val.subtype (· ∈ B) = b.1.val.subtype (· ∈ B)
    rw [congrArg Subtype.val habI]
  · intro a b hsep
    apply Bool.eq_false_iff.mpr
    intro hab
    obtain ⟨ha, hb, hab⟩ := (liftData_true_iff B C a b).mp hab
    have hf := C.property.2.2.2 (a.inside B ha) (b.inside B hb) (by
      intro x hx y hy
      exact hsep x.val (Finset.mem_subtype.mp hx) y.val (Finset.mem_subtype.mp hy))
    exact Bool.false_ne_true (hf.symm.trans hab)

noncomputable def ListPattern.extendFin {s d n : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (h : B.card = n) (C : ListPattern s d (Fin n)) : ListPattern s d X :=
  (C.restrict (B.orderIsoOfFin h).symm.toOrderEmbedding).lift B

lemma ListPattern.measurable_restrict {s d : ℕ} {X Y : Type*}
    [LinearOrder X] [LinearOrder Y] (e : X ↪o Y) :
    Measurable (ListPattern.restrict (s := s) (d := d) e) := by
  apply Measurable.subtype_mk
  apply Measurable.of_eval; intro a
  apply Measurable.of_eval; intro b
  exact (measurable_pi_apply (ListSlot.map e.toEmbedding b)).comp
    ((measurable_pi_apply (ListSlot.map e.toEmbedding a) :
      Measurable (fun C : EqualityData s d Y => C (ListSlot.map e.toEmbedding a))).comp
      measurable_subtype_coe)

noncomputable def restrictionLaw {s d : ℕ} {X Y : Type*}
    [LinearOrder X] [LinearOrder Y] (e : X ↪o Y)
    (μ : ProbabilityMeasure (ListPattern s d Y)) : ProbabilityMeasure (ListPattern s d X) :=
  μ.map (ListPattern.measurable_restrict e).aemeasurable

open Filter
open scoped Topology

instance patternMetrizable (s d : ℕ) (X : Type*) [LinearOrder X] [Countable X] :
    TopologicalSpace.MetrizableSpace (ListPattern s d X) := by
  have : TopologicalSpace.MetrizableSpace (EqualityData s d X) := inferInstance
  exact TopologicalSpace.MetrizableSpace.subtype {C : EqualityData s d X | IsPattern C}

instance patternSecondCountable (s d : ℕ) (X : Type*) [LinearOrder X] [Countable X] :
    SecondCountableTopology (ListPattern s d X) := by
  have : SecondCountableTopology (EqualityData s d X) := inferInstance
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable instance finitePatternLawMetric (s d n : ℕ) :
    MetricSpace (ProbabilityMeasure (ListPattern s d (Fin n))) :=
  by
    have := MeasureTheory.instMetrizableSpaceProbabilityMeasure (ListPattern s d (Fin n))
    exact TopologicalSpace.metrizableSpaceMetric _

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_Cleanup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Cleanup

open Turing
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

def clearTapes : {n : Nat} → (Fin n → K) → (K → List Bool) → K → List Bool
  | 0, _, base => base
  | n + 1, selected, base =>
      clearTapes (fun i : Fin n => selected i.succ) (Function.update base (selected 0) [])

def actualCost : {n : Nat} → (Fin n → K) → (K → List Bool) → Nat
  | 0, _, _ => 1
  | n + 1, selected, base =>
      actualCost (fun i : Fin n => selected i.succ) (Function.update base (selected 0) []) +
        ((base (selected 0)).length + 1)

theorem clearTapes_apply {n : Nat} (selected : Fin n → K) (base : K → List Bool) (k : K) :
    clearTapes selected base k = if ∃ i, selected i = k then [] else base k := by
  induction n generalizing base with
  | zero => simp [clearTapes]
  | succ n ih =>
      rw [clearTapes, ih]
      by_cases first : selected 0 = k
      · subst k
        simp [Function.update]
      · have notFirst : k ≠ selected 0 := Ne.symm first
        by_cases later : ∃ i : Fin n, selected i.succ = k <;>
          simp [Fin.exists_fin_succ, first, later, Function.update, notFirst]

theorem actualCost_le {n : Nat} (selected : Fin n → K) (base : K → List Bool) :
    actualCost selected base ≤ (∑ i, (base (selected i)).length) + n + 1 := by
  induction n generalizing base with
  | zero => simp [actualCost]
  | succ n ih =>
      have tailBound := ih (fun i : Fin n => selected i.succ)
        (Function.update base (selected 0) [])
      have sumBound :
          (∑ i : Fin n, ((Function.update base (selected 0) []) (selected i.succ)).length) ≤
            ∑ i : Fin n, (base (selected i.succ)).length := by
        apply Finset.sum_le_sum
        intro i _
        by_cases h : selected i.succ = selected 0 <;> simp [h]
      rw [actualCost, Fin.sum_univ_succ]
      omega

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Cleanup

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_AssignmentTester
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.AssignmentTester

open scoped BigOperators
open Finset

variable {A : Type*} [Fintype A] [DecidableEq A]

def truth (b : Bool) : ℝ := if b then 1 else 0

def disagree (a b : Bool) : ℝ := if a = b then 0 else 1

def distance {K : Type*} [Fintype K] (f g : K → Bool) : ℝ :=
  𝔼 k, disagree (f k) (g k)

end IndependentSetsGames.Foundations.PCP.AssignmentTester
end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_CodeComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.CodeComposition

open scoped BigOperators

def disagreement (a b : Bool) : ℝ := if a = b then 0 else 1

@[simp] theorem disagreement_self (a : Bool) : disagreement a a = 0 := by
  simp [disagreement]

def relativeDistance {X : Type*} [Fintype X] (f g : X → Bool) : ℝ :=
  𝔼 x, disagreement (f x) (g x)

@[simp] theorem relativeDistance_self {X : Type*} [Fintype X] (f : X → Bool) :
    relativeDistance f f = 0 := by
  simp [relativeDistance]

end IndependentSetsGames.Foundations.PCP.CodeComposition
end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_Cube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open scoped BigOperators

@[reducible] def Cube : ℕ → Type
  | 0 => Unit
  | n+1 => Bool × Cube n

instance cubeFintype : (n : ℕ) → Fintype (Cube n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => by
      letI := cubeFintype n
      exact inferInstanceAs (Fintype (Bool × Cube n))

instance cubeNonempty : (n : ℕ) → Nonempty (Cube n)
  | 0 => inferInstanceAs (Nonempty Unit)
  | n+1 => @instNonemptyProd Bool (Cube n) _ (cubeNonempty n)

noncomputable def mean {n : ℕ} (f : Cube n → ℝ) : ℝ := 𝔼 x, f x

noncomputable def evenPart {n : ℕ} (f : Cube (n+1) → ℝ) (x : Cube n) :=
  (f (false,x) + f (true,x)) / 2

noncomputable def oddPart {n : ℕ} (f : Cube (n+1) → ℝ) (x : Cube n) :=
  (f (false,x) - f (true,x)) / 2

noncomputable def noise (ρ : ℝ) : {n : ℕ} → (Cube n → ℝ) → Cube n → ℝ
  | 0, f, x => f x
  | _+1, f, (b,x) => noise ρ (evenPart f) x + (if b then -ρ else ρ) * noise ρ (oddPart f) x

end LargeIndependentSets.BooleanJunta

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Fourier_Fourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open scoped BigOperators

noncomputable def fourier : {n : ℕ} → (Cube n → ℝ) → Cube n → ℝ
  | 0, f, x => f x
  | _+1, f, (b,x) => if b then fourier (oddPart f) x else fourier (evenPart f) x

noncomputable def synth : {n : ℕ} → (Cube n → ℝ) → Cube n → ℝ
  | 0, f, x => f x
  | _+1, f, (b,x) => synth (fun s => f (false,s)) x +
      (if b then -1 else 1) * synth (fun s => f (true,s)) x

def bit : {n : ℕ} → Cube n → Fin n → Bool
  | _+1, (b,x), i => Fin.cases b (bit x) i

def degree : {n : ℕ} → Cube n → ℕ
  | 0, _ => 0
  | _+1, (b,x) => (if b then 1 else 0) + degree x

def flip : {n : ℕ} → Fin n → Cube n → Cube n
  | _+1, i, (b,x) => Fin.cases (!b,x) (fun j => (b,flip j x)) i

noncomputable def diff {n : ℕ} (i : Fin n) (f : Cube n → ℝ) (x : Cube n) : ℝ :=
  (f x - f (flip i x))/2

end LargeIndependentSets.BooleanJunta

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_Supported
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open scoped BigOperators
open scoped Classical

def Supported {n : ℕ} (S : Finset (Fin n)) (s : Cube n) : Prop :=
  ∀ i, bit s i = true → i ∈ S

noncomputable def walsh : {n : ℕ} → Cube n → Cube n → ℝ
  | 0, _, _ => 1
  | _+1, (b,s), (c,x) => (if b && c then -1 else 1) * walsh s x

noncomputable def truncate {n : ℕ} (S : Finset (Fin n)) (f : Cube n → ℝ) : Cube n → ℝ :=
  synth (fun s => if Supported S s then fourier f s else 0)

noncomputable def influence {n : ℕ} (f : Cube n → ℝ) (i : Fin n) : ℝ :=
  mean (fun x => |diff i f x|)

end LargeIndependentSets.BooleanJunta

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_Heavy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open scoped BigOperators Classical

noncomputable def heavy {n : ℕ} (θ : ℝ) (f : Cube n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => θ^2 < influence f i)

noncomputable def tailSet {n : ℕ} (S : Finset (Fin (n+1))) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.succ ∈ S)

@[simp] lemma mem_tailSet {n : ℕ} (S : Finset (Fin (n+1))) (i : Fin n) :
    i ∈ tailSet S ↔ i.succ ∈ S := by simp [tailSet]

noncomputable def merge : {n : ℕ} → Finset (Fin n) → Cube n → Cube n → Cube n
  | 0, _, x, _ => x
  | _+1, S, (b,x), (c,y) => (if 0 ∈ S then b else c, merge (tailSet S) x y)

end LargeIndependentSets.BooleanJunta

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_Bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open scoped BigOperators Classical

def ofBits : {n : ℕ} → (Fin n → Bool) → Cube n
  | 0, _ => ()
  | _+1, x => (x 0, ofBits (fun i => x i.succ))

@[simp] lemma bit_ofBits {n : ℕ} (x : Fin n → Bool) : bit (ofBits x) = x := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [ofBits, bit, Fin.cases_succ, ih]

@[simp] lemma ofBits_bit {n : ℕ} (x : Cube n) : ofBits (bit x) = x := by
  induction n with
  | zero => cases x; rfl
  | succ n ih =>
    obtain ⟨b,x⟩ := x
    simp only [ofBits, bit, Fin.cases_zero, Fin.cases_succ, ih]

def bitEquiv (n : ℕ) : Cube n ≃ (Fin n → Bool) where
  toFun := bit
  invFun := ofBits
  left_inv := ofBits_bit
  right_inv := bit_ofBits

noncomputable def bitInfluence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) (i : ι) : ℝ :=
  𝔼 x, |(f x - f (Function.update x i (!(x i))))/2|

def reindexBits {ι κ : Type*} (e : ι ≃ κ) : (κ → Bool) ≃ (ι → Bool) where
  toFun := fun x i => x (e i)
  invFun := fun x j => x (e.symm j)
  left_inv := by intro x; funext j; simp
  right_inv := by intro x; funext i; simp

end LargeIndependentSets.BooleanJunta

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_CompareLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.CompareLoop

open Turing

variable {q : Nat} {Λ : Type}

def comparisonTime (tailName headName : Nat) : Nat :=
  2 * (tailName + 2) + 2 * (headName + 2) + max (tailName + 1) (headName + 1) + 2

theorem comparisonTime_le_of_lt (tailName headName N : Nat)
    (hTail : tailName < N) (hHead : headName < N) :
    comparisonTime tailName headName ≤ 5 * N + 6 := by
  have hm : max (tailName + 1) (headName + 1) ≤ N := max_le (by omega) (by omega)
  unfold comparisonTime
  omega

end IndependentSetsGames.Foundations.PCP.AlphabetTable.CompareLoop

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_Minimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.ConstraintGraph

variable {V E A : Type*}

variable {W D B : Type*}

def labelingEquiv (vertices : V ≃ W) (labels : A ≃ B) : (V → A) ≃ (W → B) where
  toFun := fun labeling w => labels (labeling (vertices.symm w))
  invFun := fun labeling v => labels.symm (labeling (vertices v))
  left_inv := by intro labeling; funext v; simp
  right_inv := by intro labeling; funext w; simp

end IndependentSetsGames.Foundations.PCP.ConstraintGraph

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_Addresses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Addresses

def values (n m edge tail head : Nat) : Fin 5 → Nat := ![n, m, edge, tail, head]

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Addresses

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_EmitRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.EmitRows

open Turing

theorem vector_list_ofFn {α : Type} {n : Nat} (vector : Vector α n) :
    List.ofFn (fun index : Fin n => vector[index]) = vector.toList := by
  have equality := congrArg Vector.toList (Vector.ofFn_getElem (xs := vector))
  simpa only [Vector.toList_ofFn, Fin.getElem_fin] using equality

theorem flatMap_length_le {α β : Type} (items : List α) (f : α → List β)
    (bound : Nat) (bounded : ∀ item ∈ items, (f item).length ≤ bound) :
    (items.flatMap f).length ≤ items.length * bound := by
  induction items with
  | nil => simp
  | cons item items ih =>
    have hh := bounded item (by simp)
    have ht := ih (fun x hx => bounded x (by simp [hx]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

end IndependentSetsGames.Foundations.PCP.AlphabetTable.EmitRows

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_Initialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Initialization

open Turing

variable {q : Nat}

def time (N : Nat) : Nat := (6 * N + 11) + (7 * (3 * (N + 1) + 3) + 1)

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Initialization

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_BoundedIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BoundedIteration
open Turing

variable {α β : Type}

noncomputable def runtime (body length : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.X*(body.comp length + 2*length + 4) + 2*length + 4

lemma runtime_eval (body length : Polynomial ℕ) (n : ℕ) :
    (runtime body length).eval n = n*(body.eval (length.eval n)+2*length.eval n+4)+2*length.eval n+4 := by
  simp [runtime]

end LargeIndependentSets.BoundedIteration

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_LazySmoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.LazySmoothing

open scoped BigOperators

def bitCount {n : ℕ} (tape : Fin n → Bool) : ℕ :=
  ∑ i, if tape i then 1 else 0

noncomputable def binomialMean (n : ℕ) (g : ℕ → ℝ) : ℝ :=
  Finset.univ.expect (fun tape : Fin n → Bool => g (bitCount tape))

def splitTape (n : ℕ) : (Fin (n + 1) → Bool) ≃ (Bool × (Fin n → Bool)) where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := Fin.cases x.1 x.2
  left_inv x := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv _ := rfl

@[simp] theorem mean_const (n : ℕ) (c : ℝ) :
    binomialMean n (fun _ => c) = c := Fintype.expect_const c

@[simp] theorem mean_zero (g : ℕ → ℝ) : binomialMean 0 g = g 0 := by
  simp [binomialMean, bitCount]

def score (n k : ℕ) : ℝ := (n : ℝ) - 2 * (k : ℝ)

noncomputable def scoreMean (n : ℕ) (g : ℕ → ℝ) : ℝ :=
  binomialMean n (fun k => score n k * g k)

@[simp] theorem scoreMean_zero (g : ℕ → ℝ) : scoreMean 0 g = 0 := by
  simp [scoreMean, score]

end IndependentSetsGames.Foundations.PCP.LazySmoothing

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_SpectralReturn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.SpectralReturn

open scoped BigOperators

noncomputable section

def mean {A : Type*} [Fintype A] (f : A → ℝ) : ℝ := Finset.univ.expect f

def energy {A : Type*} [Fintype A] (f : A → ℝ) : ℝ := mean (fun x => (f x) ^ 2)

def correlation {A : Type*} [Fintype A] (f g : A → ℝ) : ℝ :=
  mean (fun x => f x * g x)

def edgeProfile {V D : Type*} [Fintype D] (bad : V × D → Bool) (v : V) : ℝ :=
  Finset.univ.expect (fun d => if bad (v, d) then 1 else 0)

def edgeDensity {V D : Type*} [Fintype V] [Fintype D] (bad : V × D → Bool) : ℝ :=
  mean (edgeProfile bad)

section Averages

variable {A B : Type*} [Fintype A] [Fintype B]

theorem mean_prod (f : A × B → ℝ) :
    mean f = mean (fun a => mean (fun b => f (a, b))) := by
  simpa only [mean, Finset.univ_product_univ] using
    Finset.expect_product (Finset.univ : Finset A) (Finset.univ : Finset B) f

@[simp] theorem mean_const [Nonempty A] (c : ℝ) : mean (fun _ : A => c) = c :=
  Fintype.expect_const c

end Averages

end
end IndependentSetsGames.Foundations.PCP.SpectralReturn

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_CayleySpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.CayleySpectral

open scoped BigOperators
open Finset

variable {I D : Type*}

def splitPortWord (n : Nat) : (Fin (n + 1) → D) ≃ D × (Fin n → D) where
  toFun p := (p 0, fun j => p j.succ)
  invFun z := Fin.cases z.1 z.2
  left_inv p := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

end IndependentSetsGames.Foundations.PCP.CayleySpectral
end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_CayleyTailCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.CayleyTailCount

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

def upperMasks (s : Finset α) (m : ℕ) : Finset (Finset α) :=
  s.powerset.filter fun t => 3 * m ≤ t.card

def lowerMasks (s : Finset α) (m : ℕ) : Finset (Finset α) :=
  s.powerset.filter fun t => t.card ≤ m

def badMasks (s : Finset α) (m : ℕ) : Finset (Finset α) :=
  lowerMasks s m ∪ upperMasks s m

omit [DecidableEq α] in

theorem upperMasks_weight (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    (upperMasks s m).card * 3 ^ (3 * m) ≤ 4 ^ (4 * m) := by
  calc
    _ = ∑ _t ∈ upperMasks s m, 3 ^ (3 * m) := by simp
    _ ≤ ∑ t ∈ upperMasks s m, 3 ^ t.card := by
      apply Finset.sum_le_sum
      intro t ht
      exact Nat.pow_le_pow_right (by decide) (Finset.mem_filter.mp ht).2
    _ ≤ ∑ t ∈ s.powerset, 3 ^ t.card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro t _ _
        exact Nat.zero_le _
    _ = 4 ^ s.card := by
      simpa using Finset.sum_pow_mul_eq_add_pow (3 : ℕ) 1 s
    _ = 4 ^ (4 * m) := by rw [hcard]

theorem lowerMasks_complement_image (s : Finset α) (m : ℕ)
    (hcard : s.card = 4 * m) :
    (lowerMasks s m).image (fun t => s \ t) = upperMasks s m := by
  ext u
  constructor
  · intro hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hts, htlo⟩ := Finset.mem_filter.mp ht
    have hsub := Finset.mem_powerset.mp hts
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
    rw [Finset.card_sdiff_of_subset hsub, hcard]
    omega
  · intro hu
    obtain ⟨hus, huhi⟩ := Finset.mem_filter.mp hu
    have hsub := Finset.mem_powerset.mp hus
    apply Finset.mem_image.mpr
    refine ⟨s \ u, ?_, Finset.sdiff_sdiff_eq_self hsub⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
    rw [Finset.card_sdiff_of_subset hsub, hcard]
    omega

theorem lowerMasks_card_eq_upperMasks (s : Finset α) (m : ℕ)
    (hcard : s.card = 4 * m) :
    (lowerMasks s m).card = (upperMasks s m).card := by
  have hinj : Set.InjOn (fun t : Finset α => s \ t) (lowerMasks s m) := by
    intro a ha b hb hab
    have has := Finset.mem_powerset.mp (Finset.mem_filter.mp ha).1
    have hbs := Finset.mem_powerset.mp (Finset.mem_filter.mp hb).1
    have h := congrArg (fun t : Finset α => s \ t) hab
    simpa only [Finset.sdiff_sdiff_eq_self has, Finset.sdiff_sdiff_eq_self hbs] using h
  calc
    _ = ((lowerMasks s m).image (fun t => s \ t)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ = _ := congrArg Finset.card (lowerMasks_complement_image s m hcard)

theorem ratio_le_of_weight (c m : ℕ)
    (h : c * 3 ^ (3 * m) ≤ 4 ^ (4 * m)) :
    (c : ℝ) / 2 ^ (4 * m) ≤ (16 / 27 : ℝ) ^ m := by
  have hc : (c : ℝ) * 3 ^ (3 * m) ≤ 4 ^ (4 * m) := by exact_mod_cast h
  have h3 : 0 < (3 : ℝ) ^ (3 * m) := by positivity
  have h2 : 0 < (2 : ℝ) ^ (4 * m) := by positivity
  calc
    _ ≤ ((4 : ℝ) ^ (4 * m) / 3 ^ (3 * m)) / 2 ^ (4 * m) :=
      div_le_div_of_nonneg_right ((le_div_iff₀ h3).mpr hc) h2.le
    _ = _ := by
      rw [pow_mul, pow_mul, pow_mul, ← div_pow, ← div_pow]
      norm_num

omit [DecidableEq α] in
theorem upperMasks_ratio_le (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((upperMasks s m).card : ℝ) / 2 ^ s.card ≤ (16 / 27 : ℝ) ^ m := by
  rw [hcard]
  exact ratio_le_of_weight _ m (upperMasks_weight s m hcard)

theorem lowerMasks_ratio_le (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((lowerMasks s m).card : ℝ) / 2 ^ s.card ≤ (16 / 27 : ℝ) ^ m := by
  rw [lowerMasks_card_eq_upperMasks s m hcard]
  exact upperMasks_ratio_le s m hcard

theorem badMasks_ratio_le_sharp (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((badMasks s m).card : ℝ) / 2 ^ s.card ≤ 2 * (16 / 27 : ℝ) ^ m := by
  have hc : ((badMasks s m).card : ℝ) ≤
      (lowerMasks s m).card + (upperMasks s m).card := by
    exact_mod_cast (Finset.card_union_le (lowerMasks s m) (upperMasks s m))
  have hpos : 0 < (2 : ℝ) ^ s.card := by positivity
  calc
    _ ≤ ((lowerMasks s m).card + (upperMasks s m).card : ℝ) / 2 ^ s.card :=
      div_le_div_of_nonneg_right hc hpos.le
    _ = ((lowerMasks s m).card : ℝ) / 2 ^ s.card +
        ((upperMasks s m).card : ℝ) / 2 ^ s.card := add_div _ _ _
    _ ≤ (16 / 27 : ℝ) ^ m + (16 / 27 : ℝ) ^ m :=
      add_le_add (lowerMasks_ratio_le s m hcard) (upperMasks_ratio_le s m hcard)
    _ = _ := by ring

theorem badMasks_ratio_le (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((badMasks s m).card : ℝ) / 2 ^ s.card ≤ 2 * (2 / 3 : ℝ) ^ m := by
  apply (badMasks_ratio_le_sharp s m hcard).trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by norm_num) (by norm_num) m) (by norm_num)

section Words

variable {D : Type*} [Fintype D]

def trueMask (word : D → Bool) : Finset D :=
  Finset.univ.filter fun i => word i = true

def countTrue (word : D → Bool) : ℕ := (trueMask word).card

def badWord (m : ℕ) (word : D → Bool) : Prop :=
  countTrue word ≤ m ∨ 3 * m ≤ countTrue word

instance instDecidableBadWord (m : ℕ) (word : D → Bool) : Decidable (badWord m word) :=
  inferInstanceAs (Decidable (countTrue word ≤ m ∨ 3 * m ≤ countTrue word))

def wordMaskEquiv [DecidableEq D] : (D → Bool) ≃ Finset D where
  toFun := trueMask
  invFun s i := decide (i ∈ s)
  left_inv word := by
    funext i
    cases h : word i <;> simp [trueMask, h]
  right_inv s := by
    ext i
    simp [trueMask]

theorem twoTail_probability [DecidableEq D] (m : ℕ) (hcard : Fintype.card D = 4 * m) :
    (𝔼 word : D → Bool, if badWord m word then (1 : ℝ) else 0) ≤
      2 * (2 / 3 : ℝ) ^ m := by
  classical
  have he : (𝔼 word : D → Bool, if badWord m word then (1 : ℝ) else 0) =
      (𝔼 s : Finset D, if s.card ≤ m ∨ 3 * m ≤ s.card then (1 : ℝ) else 0) := by
    apply Finset.expect_equiv (wordMaskEquiv (D := D))
    · intro word
      simp
    · intro word _
      rfl
  have hs : (Finset.univ.filter fun s : Finset D => s.card ≤ m ∨ 3 * m ≤ s.card) =
      badMasks (Finset.univ : Finset D) m := by
    ext s
    simp [badMasks, lowerMasks, upperMasks]
  rw [he, Fintype.expect_eq_sum_div_card, Finset.sum_boole, hs, Fintype.card_finset]
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Finset.card_univ] using
    badMasks_ratio_le (Finset.univ : Finset D) m (by simpa using hcard)

end Words

theorem union_bound_le_half (n m : ℕ) (hm : 3 * (n + 2) ≤ m) :
    (2 : ℝ) ^ n * (2 * (2 / 3 : ℝ) ^ m) ≤ 1 / 2 := by
  have hpow : (2 / 3 : ℝ) ^ m ≤ (2 / 3 : ℝ) ^ (3 * (n + 2)) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
  have hbase : (2 / 3 : ℝ) ^ (3 * (n + 2)) ≤ (1 / 2 : ℝ) ^ (n + 2) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by norm_num) (n + 2)
  calc
    _ ≤ (2 : ℝ) ^ n * (2 * (1 / 2 : ℝ) ^ (n + 2)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hpow.trans hbase) (by norm_num)) (by positivity)
    _ = 1 / 2 := by
      rw [pow_add, div_pow]
      norm_num
      field_simp
      norm_num

theorem seventh_power_size : (2 : ℕ) ^ 448 = (((2 : ℕ) ^ 16) ^ 7) ^ 4 := by
  rw [← pow_mul, ← pow_mul]

end IndependentSetsGames.Foundations.PCP.CayleyTailCount

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_CayleySampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.CayleySampling

open scoped BigOperators
open Finset

variable {V D : Type*}

abbrev FalseFiber (χ : V → Bool) := {x : V // χ x = false}

def falseRepresentative (χ : V → Bool) (flip : V → V)
    (hχ : ∀ x, χ (flip x) = !(χ x)) (x : V) : FalseFiber χ :=
  if h : χ x = false then ⟨x, h⟩
  else ⟨flip x, by cases hx : χ x <;> simp_all⟩

def booleanSplitEquiv (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) :
    V ≃ Bool × FalseFiber χ where
  toFun x := (χ x, falseRepresentative χ flip hχ x)
  invFun p := if p.1 then flip p.2.val else p.2.val
  left_inv x := by
    cases hx : χ x <;> simp [falseRepresentative, hx]
    exact hflip x
  right_inv p := by
    rcases p with ⟨b, x⟩
    apply Prod.ext
    · cases b <;> simp [hχ, x.property]
    · cases b <;> apply Subtype.ext <;>
        simp [falseRepresentative, hχ, x.property]
      exact hflip x.val

@[simp] theorem booleanSplitEquiv_fst (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) (x : V) :
    (booleanSplitEquiv χ flip hflip hχ x).1 = χ x := rfl

def sampleSplitEquiv (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) :
    (D → V) ≃ (D → Bool) × (D → FalseFiber χ) :=
  (Equiv.piCongrRight fun _ : D => booleanSplitEquiv χ flip hflip hχ).trans
    (Equiv.arrowProdEquivProdArrow D (fun _ => Bool) (fun _ => FalseFiber χ))

@[simp] theorem sampleSplitEquiv_fst (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) (g : D → V) :
    (sampleSplitEquiv χ flip hflip hχ g).1 = fun d => χ (g d) := rfl

theorem expect_boolean_samples [Fintype V] [Nonempty V] [Fintype D] [DecidableEq D]
    (χ : V → Bool) (flip : V → V) (hflip : Function.Involutive flip)
    (hχ : ∀ x, χ (flip x) = !(χ x)) (F : (D → Bool) → ℝ) :
    (𝔼 g : D → V, F (fun d => χ (g d))) = 𝔼 b : D → Bool, F b := by
  classical
  have : Nonempty (FalseFiber χ) :=
    ⟨falseRepresentative χ flip hχ (Classical.choice ‹Nonempty V›)⟩
  calc
    (𝔼 g : D → V, F (fun d => χ (g d))) =
        𝔼 p : (D → Bool) × (D → FalseFiber χ), F p.1 := by
      apply Fintype.expect_equiv (sampleSplitEquiv χ flip hflip hχ)
      intro g
      rfl
    _ = 𝔼 b : D → Bool, F b := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
      simp only [Fintype.expect_const]

end IndependentSetsGames.Foundations.PCP.CayleySampling
end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_Expanders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.Expanders

open scoped BigOperators
open CayleySpectral

def baseDimension : Nat := 448
def initialQuarterDegree : Nat := 2 ^ 14

end IndependentSetsGames.Foundations.PCP.Expanders
end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_ZigzagSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.ZigzagSpectral

open SpectralReturn

noncomputable section

variable {V D E : Type*}

def cloudMean [Fintype D] (f : V × D → ℝ) (v : V) : ℝ :=
  mean (fun d => f (v, d))

def liftCloud (f : V → ℝ) (x : V × D) : ℝ := f x.1

def projection [Fintype D] (f : V × D → ℝ) : V × D → ℝ :=
  liftCloud (cloudMean f)

def centered [Fintype D] (f : V × D → ℝ) : V × D → ℝ := f - projection f

end

end IndependentSetsGames.Foundations.PCP.ZigzagSpectral

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_PoweringDecoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PoweringDecoding

open scoped BigOperators

variable {Ω A : Type*} [Fintype Ω] [Nonempty Ω] [Fintype A] [Nonempty A]

noncomputable def mass (opinion : Ω → A) (a : A) : ℝ := by
  classical
  exact Finset.univ.expect (fun ω => if opinion ω = a then 1 else 0)

omit [Nonempty Ω] in
theorem exists_mode (opinion : Ω → A) :
    ∃ a : A, ∀ b : A, mass opinion b ≤ mass opinion a := by
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image (Finset.univ : Finset A)
    (mass opinion) Finset.univ_nonempty
  exact ⟨a, fun b => ha b (Finset.mem_univ b)⟩

noncomputable def mode (opinion : Ω → A) : A := Classical.choose (exists_mode opinion)

end IndependentSetsGames.Foundations.PCP.PoweringDecoding
noncomputable section

namespace IndependentSetsGames.Foundations.PCP.PoweringMoment

open scoped BigOperators

def bit (p : Prop) : ℝ := by
  classical
  exact if p then 1 else 0

def hits {I Ω : Type*} [Fintype I] (E : I → Ω → Prop) (ω : Ω) : ℝ :=
  ∑ i, bit (E i ω)

def mean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ := Finset.univ.expect f

end IndependentSetsGames.Foundations.PCP.PoweringMoment
end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_PoweringReturn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PoweringReturn

open SpectralReturn
open PoweringMoment (bit)

variable {V D : Type*}

def portConsEquiv (D : Type*) (n : Nat) :
    (D × (Fin n → D)) ≃ (Fin (n + 1) → D) where
  toFun z := Fin.cases z.1 z.2
  invFun r := (r 0, fun j => r j.succ)
  left_inv z := by
    apply Prod.ext
    · rfl
    · funext j
      rfl
  right_inv r := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j

end IndependentSetsGames.Foundations.PCP.PoweringReturn

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_PoweringWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PoweringMomentBound

open scoped BigOperators
open SpectralReturn PoweringReturn
open PoweringMoment (bit hits)

def windowIndex (n start m : Nat) (h : start + m ≤ n + 1) (i : Fin m) : Fin (n + 1) :=
  ⟨start + i.val, (Nat.add_lt_add_left i.isLt start).trans_le h⟩

end IndependentSetsGames.Foundations.PCP.PoweringMomentBound

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_PoweringNumeric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.PoweringSoundness

open scoped BigOperators
open SpectralReturn PoweringMomentBound
open PoweringMoment (bit hits)

variable {V D A : Type*}

def center (q M : Nat) : Nat := (4 * q * M) ^ 2

def gain (q M : Nat) (lambda : ℝ) : ℝ :=
  (1 / (2 * (q : ℝ))) ^ 4 * ((2 * M + 1 : Nat) : ℝ) /
    ((1 + 2 / (1 - lambda)) + 1)

end IndependentSetsGames.Foundations.PCP.PoweringSoundness
end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_CloudRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.CloudRounding

open scoped BigOperators

variable {X A D : Type*} [Fintype X] [Fintype A] [Fintype D]
variable [DecidableEq X] [DecidableEq A]

def colorSet (ell : X → A) (a : A) : Finset X :=
  Finset.univ.filter (fun x => ell x = a)

def minoritySet (ell : X → A) (m : A) : Finset X :=
  Finset.univ.filter (fun x => ell x ≠ m)

def directedCut (next : X × D → X) (S : Finset X) : Finset (X × D) :=
  Finset.univ.filter (fun xd => xd.1 ∈ S ∧ next xd ∉ S)

def disagreementSet (ell : X → A) (next : X × D → X) : Finset (X × D) :=
  Finset.univ.filter (fun xd => ell xd.1 ≠ ell (next xd))

abbrev Nonmajor (m : A) := {a : A // a ≠ m}

omit [DecidableEq X] in
theorem exists_max_color (ell : X → A) [Nonempty A] :
    ∃ m : A, ∀ a, (colorSet ell a).card ≤ (colorSet ell m).card := by
  classical
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ
    (fun a : A => (colorSet ell a).card) Finset.univ_nonempty
  exact ⟨m, fun a => hm a (Finset.mem_univ a)⟩

noncomputable def majority (ell : X → A) [Nonempty A] : A :=
  Classical.choose (exists_max_color ell)

def minorityEquiv (ell : X → A) (m : A) :
    (Σ a : Nonmajor m, ↥(colorSet ell a.val)) ≃ ↥(minoritySet ell m) where
  toFun t := ⟨t.2.val, by
    have hc : ell t.2.val = t.1.val := (Finset.mem_filter.mp t.2.property).2
    have hn : ell t.2.val ≠ m := fun h => t.1.property (hc.symm.trans h)
    simpa [minoritySet] using hn⟩
  invFun x :=
    ⟨⟨ell x.val, by simpa [minoritySet] using x.property⟩,
      ⟨x.val, by simp [colorSet]⟩⟩
  left_inv t := by
    rcases t with ⟨⟨a, ha⟩, ⟨x, hx⟩⟩
    have hxa : ell x = a := by simpa [colorSet] using hx
    cases hxa
    rfl
  right_inv x := by apply Subtype.ext; rfl

def minorityCutEmbedding (ell : X → A) (next : X × D → X) (m : A) :
    (Σ a : Nonmajor m, ↥(directedCut next (colorSet ell a.val))) ↪
      ↥(disagreementSet ell next) where
  toFun t := ⟨t.2.val, by
    have hc : ell t.2.val.1 = t.1.val ∧ ell (next t.2.val) ≠ t.1.val := by
      simpa [directedCut, colorSet] using t.2.property
    have hn : ell t.2.val.1 ≠ ell (next t.2.val) :=
      fun h => hc.2 (h.symm.trans hc.1)
    simpa [disagreementSet] using hn⟩
  inj' p q h := by
    rcases p with ⟨⟨a, ha⟩, ⟨x, hx⟩⟩
    rcases q with ⟨⟨b, hb⟩, ⟨y, hy⟩⟩
    have hxy : x = y := congrArg Subtype.val h
    cases hxy
    have hxa : ell x.1 = a := by
      have hc : ell x.1 = a ∧ ell (next x) ≠ a := by
        simpa [directedCut, colorSet] using hx
      exact hc.1
    have hxb : ell x.1 = b := by
      have hc : ell x.1 = b ∧ ell (next x) ≠ b := by
        simpa [directedCut, colorSet] using hy
      exact hc.1
    have hab : a = b := hxa.symm.trans hxb
    cases hab
    rfl

end IndependentSetsGames.Foundations.PCP.CloudRounding

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_Indicators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace IndependentSetsGames.Foundations.PCP.SpectralCut

open scoped BigOperators
open SpectralReturn

section Indicators
variable {V : Type*} [Fintype V] [DecidableEq V]

def indicator (S : Finset V) (v : V) : ℝ := if v ∈ S then 1 else 0

end Indicators

end IndependentSetsGames.Foundations.PCP.SpectralCut
end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_PoweringGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PoweringFinalConstants

abbrev Alphabet := Fin 6 → Bool

@[simp] theorem card_alphabet : Fintype.card Alphabet = 64 := by
  norm_num [Alphabet, Fintype.card_fun]

end IndependentSetsGames.Foundations.PCP.PoweringFinalConstants

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_PoweringPortReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace IndependentSetsGames.Foundations.PCP.PoweringPortReindex
open SpectralReturn PoweringSoundness

variable {V D E A : Type*}

def wordEquiv (ports : D ≃ E) (n : Nat) : (Fin n → D) ≃ (Fin n → E) where
  toFun p := fun i => ports (p i)
  invFun p := fun i => ports.symm (p i)
  left_inv p := by funext i; exact ports.symm_apply_apply (p i)
  right_inv p := by funext i; exact ports.apply_symm_apply (p i)

end IndependentSetsGames.Foundations.PCP.PoweringPortReindex

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_KernelSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Games

open scoped BigOperators
noncomputable section

namespace KernelSampling

abbrev Seed (Q₁ Q₂ A B : Type*) := (Q₁ → A) × (Q₂ → B)

def readLeft {Q₁ Q₂ A B : Type*} (seed : Seed Q₁ Q₂ A B) (q : Q₁) : A := seed.1 q
def readRight {Q₁ Q₂ A B : Type*} (seed : Seed Q₁ Q₂ A B) (q : Q₂) : B := seed.2 q

variable {I A B S : Type*} [DecidableEq I]

def completedLeft (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : A × S) : I → A :=
  Function.update (readLeft seed q) j q.1

def completedRight (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : B × S) : I → B :=
  Function.update (readRight seed q) j q.1

@[simp] theorem completedLeft_coordinate (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : A × S) :
    completedLeft j seed q j = q.1 := by simp [completedLeft]

@[simp] theorem completedRight_coordinate (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : B × S) :
    completedRight j seed q j = q.1 := by simp [completedRight]

end KernelSampling
end
end IndependentSetsGames.Foundations.Games

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_Finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Information

section

open scoped BigOperators

variable {α : Type*} [Fintype α]

def IsProbability (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

def SupportedBy (p q : α → ℝ) : Prop := ∀ a, p a ≠ 0 → q a ≠ 0

noncomputable def relativeEntropy (p q : α → ℝ) : ℝ :=
  ∑ a, p a * Real.log (p a / q a)

noncomputable def totalVariation (p q : α → ℝ) : ℝ :=
  (∑ a, |p a - q a|) / 2

noncomputable def posterior (p w : α → ℝ) (z : ℝ) : α → ℝ :=
  fun a => p a * w a / z

end

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def firstMarginal (p : α × β → ℝ) (a : α) : ℝ := ∑ b, p (a, b)

noncomputable def secondMarginal (p : α × β → ℝ) (b : β) : ℝ := ∑ a, p (a, b)

theorem firstMarginal_isProbability (p : α × β → ℝ) (hp : IsProbability p) :
    IsProbability (firstMarginal p) := by
  constructor
  · intro a
    exact Finset.sum_nonneg (fun b _ => hp.1 (a, b))
  · simpa only [firstMarginal, Fintype.sum_prod_type] using hp.2

theorem point_le_firstMarginal (p : α × β → ℝ) (hp : IsProbability p) (a : α) (b : β) :
    p (a, b) ≤ firstMarginal p a := by
  classical
  exact Finset.single_le_sum (fun b _ => hp.1 (a, b)) (Finset.mem_univ b)

end IndependentSetsGames.Foundations.Information

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_Conditionals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def conditionalKernel
    (p : α × β → ℝ) (fallback : β → ℝ) (a : α) (b : β) : ℝ := by
  classical
  exact if firstMarginal p a = 0 then fallback b
    else p (a, b) / firstMarginal p a

end IndependentSetsGames.Foundations.Information

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_Reveal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def revealEndpoint (q : X × Y) (side : Bool) : X ⊕ Y :=
  if side then Sum.inr q.2 else Sum.inl q.1

end
end IndependentSetsGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_MaskedVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Repetition
open scoped BigOperators
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]

def maskedJoint (p : S × (X × Y) → ℝ) : (S × (X ⊕ Y)) × (X × Y) → ℝ := fun z =>
  (if z.1.2 = Sum.inl z.2.1 then p (z.1.1, z.2) / 2 else 0) +
  (if z.1.2 = Sum.inr z.2.2 then p (z.1.1, z.2) / 2 else 0)

theorem sum_maskedJoint (p : S × (X × Y) → ℝ) :
    (∑ z, maskedJoint p z) = ∑ z, p z := by
  classical
  have hrow (s : S) (q : X × Y) :
      (∑ r : X ⊕ Y, maskedJoint p ((s,r),q)) = p (s,q) := by
    simp [maskedJoint]
  calc
    _ = ∑ s : S, ∑ r : X ⊕ Y, ∑ q : X × Y, maskedJoint p ((s,r),q) := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ s : S, ∑ q : X × Y, p (s,q) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
      simp_rw [hrow]
    _ = _ := (Fintype.sum_prod_type _).symm

theorem maskedJoint_isProbability_iff (p : S × (X × Y) → ℝ) :
    Information.IsProbability (maskedJoint p) ↔ Information.IsProbability p := by
  classical
  constructor
  · intro h
    constructor
    · intro z
      have hp := h.1 ((z.1,Sum.inl z.2.1),z.2)
      simp [maskedJoint] at hp
      linarith
    · rw [← sum_maskedJoint]
      exact h.2
  · intro h
    constructor
    · intro z
      have hp : 0 ≤ p (z.1.1,z.2) / 2 := div_nonneg (h.1 _) (by norm_num)
      dsimp [maskedJoint]
      split_ifs <;> linarith
    · rw [sum_maskedJoint]
      exact h.2

end
end IndependentSetsGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_PartialReveal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Repetition
open scoped BigOperators
noncomputable section
variable {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def mergeAt {R : Type*} (j : I) (a : R) (rest : {i : I // i ≠ j} → R) : I → R :=
  fun i => if h : i = j then a else rest ⟨i,h⟩

omit [Fintype I] in
@[simp] theorem mergeAt_self {R : Type*} (j : I) (a : R) (rest : {i : I // i ≠ j} → R) :
    mergeAt j a rest j = a := by simp [mergeAt]

omit [Fintype I] in
@[simp] theorem mergeAt_other {R : Type*} (j : I) (a : R)
    (rest : {i : I // i ≠ j} → R) (i : {i : I // i ≠ j}) :
    mergeAt j a rest i.1 = rest i := by simp [mergeAt, i.property]

def revealSplitEquiv (j : I) :
    ((T × (I → X ⊕ Y)) × (X × Y)) ≃
      (((T × ({i : I // i ≠ j} → X ⊕ Y)) × (X ⊕ Y)) × (X × Y)) where
  toFun z := (((z.1.1, fun i => z.1.2 i.1), z.1.2 j), z.2)
  invFun z := ((z.1.1.1, mergeAt j z.1.2 z.1.1.2), z.2)
  left_inv z := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext i
        by_cases h : i = j <;> simp [mergeAt, h]
    · rfl
  right_inv z := by
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · rfl
        · funext i
          exact mergeAt_other j z.1.2 z.1.1.2 i
      · exact mergeAt_self j z.1.2 z.1.1.2
    · rfl

end
end IndependentSetsGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_Pinsker
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Information

section

open scoped BigOperators

variable {α : Type*} [Fintype α]

noncomputable def hellingerSquared (p q : α → ℝ) : ℝ :=
  ∑ a, (Real.sqrt (p a) - Real.sqrt (q a)) ^ 2

end

open scoped BigOperators

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]

noncomputable def coordinateMarginal (p : (ι → α) → ℝ) (i : ι) (a : α) : ℝ := by
  classical
  exact ∑ x, if x i = a then p x else 0

noncomputable def independentProduct (q : ι → α → ℝ) (x : ι → α) : ℝ := ∏ i, q i (x i)

theorem independentProduct_isProbability (q : ι → α → ℝ) (hq : ∀ i, IsProbability (q i)) :
    IsProbability (independentProduct q) := by
  classical
  constructor
  · intro x
    exact Finset.prod_nonneg (fun i _ => (hq i).1 (x i))
  · simp only [independentProduct, ← Fintype.prod_sum, (hq _).2, Finset.prod_const_one]

end IndependentSetsGames.Foundations.Information

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_SideInformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Information
open scoped BigOperators

noncomputable def posteriorOrOriginal
    {A : Type*} [Fintype A] (p e : A → ℝ) (z : ℝ) : A → ℝ := by
  classical
  exact if 0 < z then posterior p e z else p

end IndependentSetsGames.Foundations.Information

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_SelectedInformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

def mergeCoordinates {Ω : Type*} {n : Nat} (selected : Finset (Fin n))
    (fixed : selected → Ω) (remaining : {i : Fin n // i ∉ selected} → Ω) : Fin n → Ω :=
  fun i => if h : i ∈ selected then fixed ⟨i,h⟩ else remaining ⟨i,h⟩

def coordinateSplitEquiv {Ω : Type*} {n : Nat} (selected : Finset (Fin n)) :
    (Fin n → Ω) ≃ ((selected → Ω) × ({i : Fin n // i ∉ selected} → Ω)) where
  toFun x := (fun i => x i.1, fun i => x i.1)
  invFun x := mergeCoordinates selected x.1 x.2
  left_inv x := by funext i; simp [mergeCoordinates]
  right_inv x := by
    apply Prod.ext <;> funext i <;> simp [mergeCoordinates, i.property]

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]
  {n : Nat}

abbrev SelectedLabels (selected : Finset (Fin n)) :=
  (selected → A₁) × (selected → A₂)

def selectedQuestionTuple (selected : Finset (Fin n))
    (fixed : selected → Q₁ × Q₂)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    (Fin n → Q₁) × (Fin n → Q₂) :=
  (fun i => (mergeCoordinates selected fixed remaining i).1,
   fun i => (mergeCoordinates selected fixed remaining i).2)

abbrev SelectedInput (Q₁ Q₂ : Type*) {n : Nat} (selected : Finset (Fin n)) :=
  (selected → Q₁ × Q₂) × ({i : Fin n // i ∉ selected} → Q₁ ⊕ Q₂)

end
end IndependentSetsGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_SelectedJoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Repetition

open scoped BigOperators
open Information

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def kernelPushforward (p : α → ℝ) (kernel : α → β → ℝ) : β → ℝ :=
  fun b => ∑ a, p a * kernel a b

end IndependentSetsGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_SelectedMarginal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedObservationEquiv (selected : Finset (Fin n)) :
    ((SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
      (Q₁ × Q₂)) ≃
    ((((selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
      ({i : Fin n // i ∉ selected} → Q₁ ⊕ Q₂)) × (Q₁ × Q₂)) where
  toFun z := (((z.1.1.1,z.1.2),z.1.1.2),z.2)
  invFun z := (((z.1.1.1,z.1.2),z.1.1.2),z.2)
  left_inv _ := rfl
  right_inv _ := rfl

end
end IndependentSetsGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_Mixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.Repetition
open scoped BigOperators
open Games Information

theorem isProbability_comp_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (p : B → ℝ) (hp : IsProbability p) :
    IsProbability (fun a => p (e a)) := by
  constructor
  · intro a
    exact hp.1 _
  · rw [e.sum_comp]
    exact hp.2

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

abbrev SelectedCommonData (selected : Finset (Fin n))
    (j : {i : Fin n // i ∉ selected}) :=
  ((selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
    ({i : {i : Fin n // i ∉ selected} // i ≠ j} → Q₁ ⊕ Q₂)

end IndependentSetsGames.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_Overlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Repetition

open scoped BigOperators
open Information

noncomputable def discountedCommonMass {X S : Type*} [Fintype X] [Fintype S]
    (p a b : X × S → ℝ) (t : X → ℝ) : ℝ :=
  ∑ z, min (p z) (min (a z) (b z)) / (1 + t z.1)

noncomputable def diagonalWeights {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) : X × S × S → ℝ := by
  classical
  exact fun z => if z.2.1 = z.2.2 then p (z.1, z.2.1) else 0

theorem diagonalWeights_isProbability {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) (hp : IsProbability p) : IsProbability (diagonalWeights p) := by
  classical
  constructor
  · intro z
    dsimp [diagonalWeights]
    split
    · exact hp.1 _
    · exact le_rfl
  · simpa [diagonalWeights, Fintype.sum_prod_type] using hp.2

end IndependentSetsGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_Basic2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.CorrelatedSampling

def firstAccepted {σ : Type*} (accept : σ → Bool) : List σ → Option σ
  | [] => none
  | proposal :: rest =>
      if accept proposal then some proposal else firstAccepted accept rest

noncomputable section FiniteWeights

variable {α : Type*} [Fintype α]

def totalVariation (p q : α → ℝ) : ℝ := (∑ a, |p a - q a|) / 2

def unionMass (p q : α → ℝ) : ℝ := ∑ a, max (p a) (q a)

end FiniteWeights

end IndependentSetsGames.Foundations.CorrelatedSampling

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_FiniteTrials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.CorrelatedSampling

noncomputable section

variable {σ : Type*} [Fintype σ]

def eventMass (w : σ → ℝ) (event : σ → Bool) : ℝ :=
  ∑ s, if event s then w s else 0

def geometricMass (r : ℝ) : Nat → ℝ
  | 0 => 0
  | n + 1 => 1 + r * geometricMass r n

def firstHitWeight (w : σ → ℝ) (accept : σ → Bool) : Nat → Option σ → ℝ
  | 0, none => 1
  | 0, some _ => 0
  | n + 1, none => eventMass w (fun s => !(accept s)) * firstHitWeight w accept n none
  | n + 1, some s =>
      (if accept s then w s else 0) +
        eventMass w (fun s => !(accept s)) * firstHitWeight w accept n (some s)

def goodFirstMass (w : σ → ℝ) (accept good : σ → Bool) (n : Nat) : ℝ :=
  ∑ s, if good s then firstHitWeight w accept n (some s) else 0

end

end IndependentSetsGames.Foundations.CorrelatedSampling

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_TraceLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.CorrelatedSampling

section

variable {σ : Type*} [Fintype σ]

def traceAverage (w : σ → ℝ) : Nat → (List σ → ℝ) → ℝ
  | 0, observable => observable []
  | n + 1, observable => ∑ s, w s * traceAverage w n (fun tail => observable (s :: tail))

variable [DecidableEq σ]

def goodFirstIndicator (accept good : σ → Bool) (proposals : List σ) : ℝ :=
  match firstAccepted accept proposals with
  | none => 0
  | some s => if good s then 1 else 0

end

end IndependentSetsGames.Foundations.CorrelatedSampling

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_Rectangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.CorrelatedSampling

section

variable {α : Type*} [Fintype α]

theorem sum_div_const {ι : Type*} [Fintype ι] (f : ι → ℝ) (c : ℝ) :
    (∑ i, f i) / c = ∑ i, f i / c := by
  simp only [div_eq_mul_inv, Finset.sum_mul]

end

variable {σ α : Type*} [Fintype σ] [DecidableEq σ] [DecidableEq α]

def localSample (accept : σ → Bool) (decode : σ → α) (fallback : α)
    (proposals : List σ) : α :=
  ((firstAccepted accept proposals).map decode).getD fallback

def localDiagonal (left right : σ → Bool) (decode : σ → α) (fallback a : α)
    (proposals : List σ) : ℝ :=
  if localSample left decode fallback proposals = a ∧
      localSample right decode fallback proposals = a then 1 else 0

def goodLabel (left right : σ → Bool) (decode : σ → α) (a : α) (s : σ) : Bool :=
  (left s && right s) && decide (decode s = a)

end IndependentSetsGames.Foundations.CorrelatedSampling

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_Rectangle2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.CorrelatedSampling

open scoped BigOperators

def profileThresholds {κ S : Type*} [Fintype κ] [Fintype S]
    (P : κ → S → ℝ) : List ℝ := by
  classical
  exact (Finset.univ.toList : List (κ × S)).map (fun ks => P ks.1 ks.2)

variable {Q₁ Q₂ S : Type*} [Fintype Q₁] [Fintype Q₂] [Fintype S]

def uniformRejectionRate (S : Type*) [Fintype S] : ℝ :=
  1 - 1 / (Fintype.card S : ℝ)

end IndependentSetsGames.Foundations.CorrelatedSampling

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_SharedSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

universe u

def TraceSeed (σ : Type u) : Nat → Type u
  | 0 => PUnit
  | n + 1 => σ × TraceSeed σ n

instance traceSeedFintype {σ : Type*} [Fintype σ] (n : Nat) : Fintype (TraceSeed σ n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact inferInstanceAs (Fintype (σ × TraceSeed σ n))

instance traceSeedUniqueZero {σ : Type*} : Unique (TraceSeed σ 0) :=
  inferInstanceAs (Unique PUnit)

def traceList {σ : Type*} : (n : Nat) → TraceSeed σ n → List σ
  | 0, _ => []
  | n + 1, seed => seed.1 :: traceList n seed.2

open CorrelatedSampling

end
end IndependentSetsGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_DistributionIdentities
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Repetition.CompletedSampling

open scoped BigOperators
open Games

noncomputable section

variable {X Y S Γ U V : Type*}
  [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ] [Fintype U] [Fintype V]
  [DecidableEq X] [DecidableEq Y] [DecidableEq S]

abbrev Seed (Γ X Y S U V : Type*) :=
  Γ × KernelSampling.Seed (X × S) (Y × S) U V

def left (sL : Γ → X → S) (seed : Seed Γ X Y S U V) (x : X) : U :=
  KernelSampling.readLeft seed.2 (x, sL seed.1 x)

def right (sR : Γ → Y → S) (seed : Seed Γ X Y S U V) (y : Y) : V :=
  KernelSampling.readRight seed.2 (y, sR seed.1 y)

end
end IndependentSetsGames.Foundations.Repetition.CompletedSampling

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_CoordinateCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.Repetition.CompletedSampling
open scoped BigOperators
open Games

variable {I X Y S Γ : Type*}
  [Fintype I] [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y] [DecidableEq S]

def coordinateLeft (j : I) (sL : Γ → X → S)
    (seed : Seed Γ X Y S (I → X) (I → Y)) (x : X) : I → X :=
  KernelSampling.completedLeft j seed.2 (x, sL seed.1 x)

def coordinateRight (j : I) (sR : Γ → Y → S)
    (seed : Seed Γ X Y S (I → X) (I → Y)) (y : Y) : I → Y :=
  KernelSampling.completedRight j seed.2 (y, sR seed.1 y)

omit [Fintype I] [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ]
  [DecidableEq X] [DecidableEq Y] [DecidableEq S] in
@[simp] theorem coordinateLeft_preserves (j : I) (sL : Γ → X → S)
    (seed : Seed Γ X Y S (I → X) (I → Y)) (x : X) :
    coordinateLeft j sL seed x j = x := by
  simp [coordinateLeft]

omit [Fintype I] [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ]
  [DecidableEq X] [DecidableEq Y] [DecidableEq S] in
@[simp] theorem coordinateRight_preserves (j : I) (sR : Γ → Y → S)
    (seed : Seed Γ X Y S (I → X) (I → Y)) (y : Y) :
    coordinateRight j sR seed y j = y := by
  simp [coordinateRight]

end IndependentSetsGames.Foundations.Repetition.CompletedSampling

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_Scalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Repetition

noncomputable def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

@[simp] theorem logTwo_one : logTwo 1 = 0 := by simp [logTwo]

def ScalarRecurrence (p : ℕ → ℝ) (n : ℕ) (v ell : ℝ) : Prop :=
  ∀ m, m < n → p (m + 1) ≤ p m * (v + 15 * Real.sqrt
    (((m : ℝ) * ell + logTwo (1 / p m)) / ((n : ℝ) - m)))

end IndependentSetsGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_ProfileCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.Repetition.ProfileCorrection
open scoped BigOperators
open IndependentSetsGames.Foundations.Information
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

def seedQuestionMarginal (p : X × (S × Y) → ℝ) : X × S → ℝ :=
  firstMarginal (fun z : (X × S) × Y => p (z.1.1, (z.1.2, z.2)))

theorem seedQuestionMarginal_isProbability (p : X × (S × Y) → ℝ)
    (hp : IsProbability p) : IsProbability (seedQuestionMarginal p) := by
  apply firstMarginal_isProbability
  constructor
  · intro z
    exact hp.1 _
  · have h := hp.2
    simp only [Fintype.sum_prod_type] at h ⊢
    exact h

end IndependentSetsGames.Foundations.Repetition.ProfileCorrection
namespace IndependentSetsGames.Foundations.Repetition

open scoped BigOperators

variable {ι α β : Type*} [Fintype ι] [DecidableEq α] [DecidableEq β]

variable {X Y : Type*} [Fintype X] [Fintype Y]

def normalizedWeight (weight : X → ℝ) : X → ℝ :=
  fun x => weight x / ∑ x', weight x'

theorem normalizedWeight_isProbability (weight : X → ℝ)
    (hweight : ∀ x, 0 ≤ weight x) (hmass : 0 < ∑ x, weight x) :
    (∀ x, 0 ≤ normalizedWeight weight x) ∧ (∑ x, normalizedWeight weight x) = 1 := by
  constructor
  · intro x
    exact div_nonneg (hweight x) hmass.le
  · simp only [normalizedWeight, div_eq_mul_inv, ← Finset.sum_mul, mul_inv_cancel₀ hmass.ne']

end IndependentSetsGames.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_ProfileBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.Repetition
open scoped BigOperators
open Games Information
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

def leftCommonMarginal (p : S × (X × Y) → ℝ) : X × S → ℝ :=
  fun z => ∑ y, p (z.2,(z.1,y))

def leftCommonProfile (p : S × (X × Y) → ℝ) (fallback : S → ℝ) : X → S → ℝ :=
  conditionalKernel (leftCommonMarginal p) fallback

def swapSeedLeft : (X × (S × Y)) ≃ (S × (X × Y)) where
  toFun z := (z.2.1,(z.1,z.2.2))
  invFun z := (z.2.1,(z.1,z.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem leftCommonMarginal_isProbability (p : S × (X × Y) → ℝ)
    (hp : IsProbability p) : IsProbability (leftCommonMarginal p) := by
  exact ProfileCorrection.seedQuestionMarginal_isProbability
    (fun z => p (swapSeedLeft z)) (isProbability_comp_equiv swapSeedLeft p hp)

def swapQuestionEndpoints : (S × (Y × X)) ≃ (S × (X × Y)) where
  toFun z := (z.1,(z.2.2,z.2.1))
  invFun z := (z.1,(z.2.2,z.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

def rightCommonMarginal (p : S × (X × Y) → ℝ) : Y × S → ℝ :=
  fun z => ∑ x, p (z.2,(x,z.1))

def rightCommonProfile (p : S × (X × Y) → ℝ) (fallback : S → ℝ) : Y → S → ℝ :=
  conditionalKernel (rightCommonMarginal p) fallback

end IndependentSetsGames.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_SelectedProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.Repetition

open scoped BigOperators
open Games Information

variable {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def revealDataSplitEquiv (j : I) :
    (T × (I → X ⊕ Y)) ≃ ((T × ({i : I // i ≠ j} → X ⊕ Y)) × (X ⊕ Y)) where
  toFun z := ((z.1, fun i => z.2 i.1), z.2 j)
  invFun z := (z.1.1, mergeAt j z.2 z.1.2)
  left_inv z := by
    apply Prod.ext
    · rfl
    · funext i
      by_cases h : i = j <;> simp [mergeAt, h]
  right_inv z := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext i
        exact mergeAt_other j z.2 z.1.2 i
    · exact mergeAt_self j z.2 z.1.2

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedObservationDataEquiv (selected : Finset (Fin n)) :
    (SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ≃
      (((selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
        ({i : Fin n // i ∉ selected} → Q₁ ⊕ Q₂)) where
  toFun z := ((z.1.1,z.2),z.1.2)
  invFun z := ((z.1.1,z.2),z.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

end IndependentSetsGames.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_SelectedProfileBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.Repetition

open Games
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedLocalAnswers {Q A : Type*} (strategy : (Fin n → Q) → (Fin n → A))
    (selected : Finset (Fin n)) (fixed : selected → Q)
    (remaining : {i : Fin n // i ∉ selected} → Q) : selected → A :=
  fun i => strategy (mergeCoordinates selected fixed remaining) i.1

def selectedLocalTest {Q A : Type*} (strategy : (Fin n → Q) → (Fin n → A))
    (selected : Finset (Fin n)) (fixed : selected → Q) (label : selected → A)
    (remaining : {i : Fin n // i ∉ selected} → Q) : ℝ := by
  classical
  exact if selectedLocalAnswers strategy selected fixed remaining = label then 1 else 0

theorem selectedLocalTest_nonnegative {Q A : Type*} (strategy : (Fin n → Q) → (Fin n → A))
    (selected : Finset (Fin n)) (fixed : selected → Q) (label : selected → A)
    (remaining : {i : Fin n // i ∉ selected} → Q) :
    0 ≤ selectedLocalTest strategy selected fixed label remaining := by
  classical
  unfold selectedLocalTest
  split <;> norm_num

end IndependentSetsGames.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_RevealFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.Repetition

open scoped BigOperators
open Games

section LocalNormalization

variable {I X Y : Type*} [Fintype I] [DecidableEq I]
  [Fintype X] [Fintype Y]

def completionTupleEquiv : (I → X × Y) ≃ ((I → X) × (I → Y)) where
  toFun u := (fun i => (u i).1, fun i => (u i).2)
  invFun z := fun i => (z.1 i, z.2 i)
  left_inv u := by funext i; rfl
  right_inv z := by cases z; rfl

end LocalNormalization

end IndependentSetsGames.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_SelectionSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Repetition.SelectionSequence

noncomputable def nextSet {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j)
    (S : Finset (Fin n)) : Finset (Fin n) :=
  if hs : S.card < n then insert (Classical.choose (witness S hs)) S else S

noncomputable def selectedSet {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j) : Nat → Finset (Fin n)
  | 0 => ∅
  | m + 1 => nextSet Step witness (selectedSet Step witness m)

def SetStep {n : Nat} (P : Finset (Fin n) → ℝ) (v ell : ℝ)
    (S : Finset (Fin n)) (j : Fin n) : Prop :=
  P (insert j S) ≤ P S *
    (v + 15 * Real.sqrt (((S.card : ℝ) * ell + logTwo (1 / P S)) /
      ((n : ℝ) - S.card)))

end IndependentSetsGames.Foundations.Repetition.SelectionSequence

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Integration.SourceParameters

def rate (gap : ℚ) : ℚ := 1 - gap ^ 3 / 100000

end IndependentSetsGames.Integration.SourceParameters

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_WalkLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped ENNReal NNReal

def walkLength {X : Type*} (w : X → X → ℝ≥0∞) (x : X) : List X → X → ℝ≥0∞
  | [], y => w x y
  | z :: zs, y => w x z + walkLength w z zs y

noncomputable def pathDistance {X : Type*} (w : X → X → ℝ≥0∞) (x y : X) : ℝ≥0∞ :=
  ⨅ zs : List X, walkLength w x zs y

lemma pathDistance_le_link {X : Type*} (w : X → X → ℝ≥0∞) (x y : X) :
    pathDistance w x y ≤ w x y :=
  iInf_le_of_le [] le_rfl

lemma walkLength_append {X : Type*} (w : X → X → ℝ≥0∞) (x y z : X)
    (p q : List X) :
    walkLength w x (p ++ y :: q) z = walkLength w x p y + walkLength w y q z := by
  induction p generalizing x with
  | nil => rfl
  | cons a p ih => simp only [List.cons_append, walkLength, ih, add_assoc]

lemma pathDistance_self {X : Type*} (w : X → X → ℝ≥0∞)
    (hrefl : ∀ x, w x x = 0) (x : X) : pathDistance w x x = 0 := by
  exact le_antisymm ((pathDistance_le_link w x x).trans_eq (hrefl x)) bot_le

lemma pathDistance_triangle {X : Type*} (w : X → X → ℝ≥0∞) (x y z : X) :
    pathDistance w x z ≤ pathDistance w x y + pathDistance w y z := by
  unfold pathDistance
  rw [ENNReal.iInf_add]
  apply le_iInf
  intro p
  rw [ENNReal.add_iInf]
  apply le_iInf
  intro q
  exact iInf_le_of_le (p ++ y :: q) (le_of_eq (walkLength_append w x y z p q))

lemma walkLength_map {X : Type*} (w : X → X → ℝ≥0∞) (T : X → X)
    (hw : ∀ x y, w (T x) (T y) = w x y) (x y : X) (p : List X) :
    walkLength w (T x) (p.map T) (T y) = walkLength w x p y := by
  induction p generalizing x with
  | nil => exact hw x y
  | cons a p ih => simp only [List.map_cons, walkLength, hw, ih]

lemma pathDistance_invariant {X : Type*} (w : X → X → ℝ≥0∞) (T : X → X)
    (hT : Function.Involutive T) (hw : ∀ x y, w (T x) (T y) = w x y)
    (x y : X) : pathDistance w (T x) (T y) = pathDistance w x y := by
  have hle (x y : X) : pathDistance w (T x) (T y) ≤ pathDistance w x y := by
    apply le_iInf
    intro p
    exact iInf_le_of_le (p.map T) (le_of_eq (walkLength_map w T hw x y p))
  apply le_antisymm (hle x y)
  simpa only [hT x, hT y] using hle (T x) (T y)

lemma walkLength_reverse {X : Type*} (w : X → X → ℝ≥0∞)
    (hsymm : ∀ x y, w x y = w y x) (x y : X) (p : List X) :
    walkLength w y p.reverse x = walkLength w x p y := by
  induction p generalizing x y with
  | nil => exact hsymm y x
  | cons a p ih =>
      rw [List.reverse_cons, walkLength_append, ih, walkLength, walkLength,
        hsymm a x, add_comm]

lemma pathDistance_symm {X : Type*} (w : X → X → ℝ≥0∞)
    (hsymm : ∀ x y, w x y = w y x) (x y : X) :
    pathDistance w x y = pathDistance w y x := by
  have hle (x y : X) : pathDistance w x y ≤ pathDistance w y x := by
    apply le_iInf
    intro p
    exact iInf_le_of_le p.reverse (le_of_eq (walkLength_reverse w hsymm y x p))
  exact le_antisymm (hle x y) (hle y x)

noncomputable abbrev linkPseudoEMetric {X : Type*} (w : X → X → ℝ≥0∞)
    (hrefl : ∀ x, w x x = 0) (hsymm : ∀ x y, w x y = w y x) :
    PseudoEMetricSpace X :=
  PseudoEMetricSpace.ofEDist (pathDistance w) (pathDistance_self w hrefl)
    (pathDistance_symm w hsymm) (pathDistance_triangle w)

noncomputable def circleRep (z : UnitAddCircle) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) 0 z).val

noncomputable def circleColor (z : UnitAddCircle) : Fin 3 :=
  if circleRep z < 1 / 3 then 0 else if circleRep z < 2 / 3 then 1 else 2

structure ProjectionSystem (Q : Type*) (M : Q → Type*) where
  imposed : ∀ q q', (M q → M q') → Prop

abbrev GridLocation {Q : Type*} (M : Q → Type*) (D : ℕ) :=
  Σ q, M q → ZMod D

def ProjectionSystem.Consistent {Q : Type*} {M : Q → Type*}
    (S : ProjectionSystem Q M) (a : ∀ q, M q) : Prop :=
  ∀ q q' π, S.imposed q q' π → π (a q) = a q'

inductive ProjectionSystem.ForwardZero {Q : Type*} {M : Q → Type*}
    (S : ProjectionSystem Q M) (D : ℕ) : GridLocation M D → GridLocation M D → Prop
  | link (q q' : Q) (π : M q → M q') (hπ : S.imposed q q' π) (v : M q' → ZMod D) :
    S.ForwardZero D ⟨q, v ∘ π⟩ ⟨q', v⟩

def ProjectionSystem.ZeroLink {Q : Type*} {M : Q → Type*}
    (S : ProjectionSystem Q M) (D : ℕ) (x y : GridLocation M D) : Prop :=
  S.ForwardZero D x y ∨ S.ForwardZero D y x

noncomputable def copyLength {Q : Type*} {M : Q → Type*} {D : ℕ} [NeZero D]
    (x y : GridLocation M D) : ℝ≥0∞ := by
  classical
  exact if h : x.1 = y.1 then
    ⨆ k : M x.1, edist (ZMod.toAddCircle (x.2 k)) (ZMod.toAddCircle (y.2 (h ▸ k)))
  else ⊤

@[simp] lemma copyLength_same {Q : Type*} {M : Q → Type*} {D : ℕ} [NeZero D]
    (q : Q) (f g : M q → ZMod D) :
    copyLength (⟨q, f⟩ : GridLocation M D) ⟨q, g⟩ =
      ⨆ k, edist (ZMod.toAddCircle (f k)) (ZMod.toAddCircle (g k)) := by
  simp [copyLength]

noncomputable def ProjectionSystem.linkLength {Q : Type*} {M : Q → Type*}
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D]
    (x y : GridLocation M D) : ℝ≥0∞ := by
  classical
  exact if S.ZeroLink D x y then 0 else copyLength x y

noncomputable def gridPhase {Q : Type*} {M : Q → Type*} {D : ℕ} [NeZero D]
    (a : ∀ q, M q) (x : GridLocation M D) : UnitAddCircle :=
  ZMod.toAddCircle (x.2 (a x.1))

def gridAntipode {Q : Type*} {M : Q → Type*} {D : ℕ}
    (x : GridLocation M D) : GridLocation M D :=
  ⟨x.1, fun k => x.2 k + ((D / 2 : ℕ) : ZMod D)⟩

lemma gridAntipode_involutive {Q : Type*} {M : Q → Type*} {D : ℕ} (hD : Even D) :
    Function.Involutive (gridAntipode : GridLocation M D → GridLocation M D) := by
  have htwo : (D / 2) + (D / 2) = D := by
    obtain ⟨n, hn⟩ := hD
    omega
  have hzero : ((D / 2 : ℕ) : ZMod D) + ((D / 2 : ℕ) : ZMod D) = 0 := by
    rw [← Nat.cast_add, htwo]
    exact ZMod.natCast_self D
  rintro ⟨q, f⟩
  simp only [gridAntipode, add_assoc, hzero, add_zero]

lemma copyLength_self {Q : Type*} {M : Q → Type*} {D : ℕ} [NeZero D]
    (x : GridLocation M D) : copyLength x x = 0 := by
  rcases x with ⟨q, f⟩
  simp [copyLength_same]

lemma copyLength_symm {Q : Type*} {M : Q → Type*} {D : ℕ} [NeZero D]
    (x y : GridLocation M D) : copyLength x y = copyLength y x := by
  classical
  rcases x with ⟨q, f⟩
  rcases y with ⟨q', g⟩
  by_cases h : q = q'
  · subst q'
    simp only [copyLength_same, edist_comm]
  · simp [copyLength, h, Ne.symm h]

lemma zeroLink_symm {Q : Type*} {M : Q → Type*} (S : ProjectionSystem Q M)
    {D : ℕ} (x y : GridLocation M D) : S.ZeroLink D x y ↔ S.ZeroLink D y x :=
  or_comm

lemma linkLength_self {Q : Type*} {M : Q → Type*} (S : ProjectionSystem Q M)
    {D : ℕ} [NeZero D] (x : GridLocation M D) : S.linkLength x x = 0 := by
  classical
  simp [ProjectionSystem.linkLength, copyLength_self]

lemma linkLength_symm {Q : Type*} {M : Q → Type*} (S : ProjectionSystem Q M)
    {D : ℕ} [NeZero D] (x y : GridLocation M D) :
    S.linkLength x y = S.linkLength y x := by
  classical
  simp only [ProjectionSystem.linkLength, zeroLink_symm S x y, copyLength_symm x y]

lemma forwardZero_antipode {Q : Type*} {M : Q → Type*} (S : ProjectionSystem Q M)
    {D : ℕ} {x y : GridLocation M D} (h : S.ForwardZero D x y) :
    S.ForwardZero D (gridAntipode x) (gridAntipode y) := by
  cases h with
  | link q q' π hπ v =>
      exact .link q q' π hπ (fun k => v k + ((D / 2 : ℕ) : ZMod D))

lemma zeroLink_antipode {Q : Type*} {M : Q → Type*} (S : ProjectionSystem Q M)
    {D : ℕ} {x y : GridLocation M D} (h : S.ZeroLink D x y) :
    S.ZeroLink D (gridAntipode x) (gridAntipode y) := by
  rcases h with h | h
  · exact Or.inl (forwardZero_antipode S h)
  · exact Or.inr (forwardZero_antipode S h)

lemma zeroLink_antipode_iff {Q : Type*} {M : Q → Type*} (S : ProjectionSystem Q M)
    {D : ℕ} (hD : Even D) (x y : GridLocation M D) :
    S.ZeroLink D (gridAntipode x) (gridAntipode y) ↔ S.ZeroLink D x y := by
  constructor
  · intro h
    simpa only [gridAntipode_involutive hD x, gridAntipode_involutive hD y]
      using zeroLink_antipode S h
  · exact zeroLink_antipode S

lemma copyLength_antipode {Q : Type*} {M : Q → Type*} {D : ℕ} [NeZero D]
    (x y : GridLocation M D) : copyLength (gridAntipode x) (gridAntipode y) =
      copyLength x y := by
  classical
  rcases x with ⟨q, f⟩
  rcases y with ⟨q', g⟩
  by_cases h : q = q'
  · subst q'
    simp only [gridAntipode, copyLength_same, map_add, edist_add_right]
  · simp [copyLength, gridAntipode, h]

lemma linkLength_antipode {Q : Type*} {M : Q → Type*} (S : ProjectionSystem Q M)
    {D : ℕ} [NeZero D] (hD : Even D) (x y : GridLocation M D) :
    S.linkLength (gridAntipode x) (gridAntipode y) = S.linkLength x y := by
  classical
  simp only [ProjectionSystem.linkLength, zeroLink_antipode_iff S hD,
    copyLength_antipode]

lemma twisted_pathDistance_symm {Q : Type*} {M : Q → Type*}
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D] (hD : Even D)
    (x y : GridLocation M D) :
    pathDistance S.linkLength x (gridAntipode y) =
      pathDistance S.linkLength y (gridAntipode x) := by
  calc
    _ = pathDistance S.linkLength (gridAntipode x) y := by
      simpa only [gridAntipode_involutive hD y] using
        (pathDistance_invariant S.linkLength gridAntipode (gridAntipode_involutive hD)
          (linkLength_antipode S hD) x (gridAntipode y)).symm
    _ = _ := pathDistance_symm S.linkLength (linkLength_symm S) _ _

noncomputable def gridGraph {Q : Type*} {M : Q → Type*}
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D] (hD : Even D)
    {V : Type*} (location : V → GridLocation M D) : SimpleGraph V where
  Adj u v := u ≠ v ∧ pathDistance S.linkLength (location u) (gridAntipode (location v)) ≤
    ENNReal.ofReal (1 / 8)
  symm := ⟨by
    intro u v h
    exact ⟨Ne.symm h.1, by
      rw [twisted_pathDistance_symm S hD]
      exact h.2⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_LabelCoverData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped ENNReal NNReal

structure LabelCoverData (U V L R C : Type*) where
  left : C → U
  right : C → V
  project : C → L → R

def LabelCoverData.Satisfied {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    (ℓ : U → L) (ρ : V → R) : Prop :=
  ∀ c, lc.project c (ℓ (lc.left c)) = ρ (lc.right c)

def MixedTuple (A B : Type*) (n i : ℕ) :=
  {x : Fin n → B ⊕ A // ∀ h, (x h).isLeft = decide (h.val < i)}

noncomputable def MixedTuple.map {A B A' B' : Type*} {n i : ℕ}
    (l : A → A') (r : B → B') (x : MixedTuple A B n i) : MixedTuple A' B' n i :=
  ⟨fun h => Sum.map r l (x.val h), by
    intro h
    simpa only [Sum.isLeft_map] using x.property h⟩

abbrev LayerQuestion (U V : Type*) (n : ℕ) :=
  Σ i : Fin (n + 1), MixedTuple U V n i.val

abbrev LayerAnswer {U V : Type*} (L R : Type*) {n : ℕ}
    (q : LayerQuestion U V n) := MixedTuple L R n q.1.val

noncomputable def productLabeling {U V L R : Type*} {n : ℕ}
    (ℓ : U → L) (ρ : V → R) (q : LayerQuestion U V n) : LayerAnswer L R q :=
  MixedTuple.map ℓ ρ q.2

noncomputable def distanceBump (d : ℝ≥0∞) : ℝ :=
  if d = ⊤ then 0 else max (1 - 32 * d.toReal) 0

@[simp] lemma distanceBump_zero : distanceBump 0 = 1 := by
  norm_num [distanceBump]

noncomputable def setBump {X : Type*} [PseudoEMetricSpace X] (A : Set X) (x : X) : ℝ :=
  distanceBump (Metric.infEDist x A)

noncomputable def oddBump {X : Type*} [PseudoEMetricSpace X]
    (T : X → X) (A : Set X) (x : X) : ℝ := setBump A x - setBump A (T x)

noncomputable def gridBump {Q : Type*} {M : Q → Type*}
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D]
    (A : Set (GridLocation M D)) (x : GridLocation M D) : ℝ := by
  letI := linkPseudoEMetric (S.linkLength (D := D)) (linkLength_self S) (linkLength_symm S)
  exact oddBump gridAntipode A x

noncomputable def finiteMcShane {G X : Type*} [Fintype G] [Nonempty G]
    [PseudoMetricSpace X] (e : G → X) (f : G → ℝ) (L : ℝ≥0) (x : X) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun y => f y + L * dist x (e y))

def clipUnit (x : ℝ) : ℝ := max (-1) (min 1 x)

noncomputable def finiteOddExtension {G X : Type*} [Fintype G] [Nonempty G]
    [PseudoMetricSpace X] (e : G → X) (f : G → ℝ) (L : ℝ≥0) (T : X → X) (x : X) : ℝ :=
  (clipUnit (finiteMcShane e f L x) - clipUnit (finiteMcShane e f L (T x))) / 2

noncomputable def torusAntipode {ι : Type*} (x : ι → UnitAddCircle) : ι → UnitAddCircle :=
  fun k => x k + ((1 / 2 : ℝ) : UnitAddCircle)

noncomputable def torusGrid {ι : Type*} {D : ℕ} [NeZero D]
    (x : ι → ZMod D) : ι → UnitAddCircle := fun k => ZMod.toAddCircle (x k)

noncomputable def tupleExtension {Q : Type*} {M : Q → Type*} [∀ q, Fintype (M q)]
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D]
    (A : Set (GridLocation M D)) (q : Q) (x : M q → UnitAddCircle) : ℝ := by
  classical
  exact finiteOddExtension torusGrid (fun u => gridBump S A ⟨q, u⟩) 64 torusAntipode x

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_OccurrenceTuple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets

section
open scoped Classical

def occurrenceTuple {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} (c : Fin n → C) (i : ℕ) : MixedTuple U V n i :=
  ⟨fun h => if h.val < i then Sum.inl (lc.right (c h)) else Sum.inr (lc.left (c h)), by
    intro h
    by_cases hh : h.val < i <;> simp [hh]⟩

def occurrenceQuestion {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} (c : Fin n → C) (i : Fin (n+1)) : LayerQuestion U V n :=
  ⟨i, occurrenceTuple lc c i.val⟩

def chainComposite {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} (c : Fin n → C) (i j : ℕ) (hij : i ≤ j) :
    MixedTuple L R n i → MixedTuple L R n j :=
  fun x => ⟨fun h => if i ≤ h.val ∧ h.val < j then
      Sum.inl ((x.val h).elim id (lc.project (c h))) else x.val h, by
    intro h
    by_cases hh : i ≤ h.val ∧ h.val < j
    · simp [hh]
    · have he : (h.val < i) = (h.val < j) := propext (by omega)
      simp [hh, x.property h, he]⟩

@[simp] lemma chainComposite_self {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} (c : Fin n → C) (i : ℕ) (hi : i ≤ i) (x : MixedTuple L R n i) :
    chainComposite lc c i i hi x = x := by
  apply Subtype.ext
  funext h
  simp [chainComposite, show ¬(i ≤ h.val ∧ h.val < i) from by omega]

end

open scoped Classical BigOperators
noncomputable def paddedList {X : Type*} (A : Finset X) (d : ℕ) (x₀ : X) (i : Fin d) : X :=
  if hi : i.val < A.card then (A.equivFin.symm ⟨i.val, hi⟩).val else x₀

def LabelCoverData.Sound {U V L R C : Type*} [Fintype C]
    (lc : LabelCoverData U V L R C) (σ : ℝ) : Prop :=
  ∀ (l : U → L) (r : V → R),
    ((Finset.univ.filter (fun c => lc.project c (l (lc.left c)) = r (lc.right c))).card : ℝ) ≤
      σ * Fintype.card C

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_CoordinateDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.CubeGradient
open MeasureTheory Set
open scoped BigOperators NNReal Classical

noncomputable def coordinateDerivative {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (i : Fin n) (x : Fin n → ℝ) : ℝ := deriv (f ∘ Function.update x i) (x i)

end LargeIndependentSets.CubeGradient

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_ScalarCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open MeasureTheory Set
open scoped NNReal BigOperators Classical

noncomputable def scalarCell : {m : ℕ} → Cube m → ℝ → ℝ
  | 0, _, y => y
  | _+1, (b,q), y => ((if b then 1 else 0) + scalarCell q y)/2

noncomputable def scalarAvg {m : ℕ} (f : ℝ → ℝ) (q : Cube m) : ℝ :=
  ∫ y in (0:ℝ)..1, f (scalarCell q y)

noncomputable def variation (f : ℝ → ℝ) : ℝ := ∫ y in (0:ℝ)..1, |deriv f y|

noncomputable def halfInput (b : Bool) (y : ℝ) : ℝ := ((if b then 1 else 0)+y)/2

end LargeIndependentSets.BooleanJunta

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_UniformLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open MeasureTheory Set
open scoped BigOperators Classical NNReal ENNReal

instance cubeMeasurable (m : ℕ) : MeasurableSpace (Cube m) := ⊤
instance cubeSingleton (m : ℕ) : MeasurableSingletonClass (Cube m) := ⟨fun _ => trivial⟩

noncomputable def uniformLaw (α : Type*) [Fintype α] [Nonempty α] [MeasurableSpace α] : Measure α :=
  (PMF.uniformOfFintype α).toMeasure

instance uniformLaw_probability (α : Type*) [Fintype α] [Nonempty α] [MeasurableSpace α] :
    IsProbabilityMeasure (uniformLaw α) := by unfold uniformLaw; infer_instance

noncomputable def unitLaw : Measure ℝ := volume.restrict (Icc (0:ℝ) 1)

instance unitLaw_probability : IsProbabilityMeasure unitLaw := by
  constructor
  norm_num [unitLaw, Measure.restrict_apply_univ]

noncomputable def scalarSampler (m : ℕ) (p : Cube m × ℝ) : ℝ := scalarCell p.1 p.2

end LargeIndependentSets.BooleanJunta

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_ScalarSampleInfluence
attribute [-instance] _root_.OAI.LargeIndependentSets.BooleanJunta.cubeMeasurable _root_.OAI.LargeIndependentSets.BooleanJunta.cubeSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open MeasureTheory Set
open scoped BigOperators Classical NNReal ENNReal

noncomputable def scalarSampleInfluence {m : ℕ} (f : ℝ → ℝ) (i : Fin m) : ℝ :=
  mean (fun q : Cube m => ∫ y in (0:ℝ)..1,
    |(f (scalarCell q y) - f (scalarCell (flip i q) y))/2|)

end LargeIndependentSets.BooleanJunta

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_Mix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.ProductAveraging
open MeasureTheory Set
open scoped BigOperators Classical

noncomputable def mix {ι α : Type*} (S : Finset ι) (p : (ι → α) × (ι → α)) : ι → α :=
  fun i => if i ∈ S then p.1 i else p.2 i

end LargeIndependentSets.ProductAveraging

namespace LargeIndependentSets.BooleanJunta
open MeasureTheory Set
open scoped BigOperators Classical NNReal ENNReal

noncomputable def unitCubeLaw (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi (fun _ => unitLaw)
instance unitCubeLaw_probability (n : ℕ) : IsProbabilityMeasure (unitCubeLaw n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => unitLaw)))

noncomputable def seedLaw (m : ℕ) : Measure (Cube m × ℝ) := (uniformLaw (Cube m)).prod unitLaw
instance seedLaw_probability (m : ℕ) : IsProbabilityMeasure (seedLaw m) := by unfold seedLaw; infer_instance
noncomputable def seedCubeLaw (n m : ℕ) : Measure (Fin n → Cube m × ℝ) :=
  Measure.pi (fun _ => seedLaw m)
instance seedCubeLaw_probability (n m : ℕ) : IsProbabilityMeasure (seedCubeLaw n m) := by
  unfold seedCubeLaw; infer_instance

noncomputable def cubeSampler {n m : ℕ} (p : Fin n → Cube m × ℝ) : Fin n → ℝ :=
  fun i => scalarSampler m (p i)

noncomputable def flipSeed {m : ℕ} (k : Fin m) (t : Cube m × ℝ) : Cube m × ℝ :=
  (flip k t.1, t.2)

noncomputable def sampledDiff {n m : ℕ} (f : (Fin n → ℝ) → ℝ)
    (i : Fin n) (k : Fin m) (p : Fin n → Cube m × ℝ) : ℝ :=
  |(f (cubeSampler p) - f (cubeSampler (Function.update p i (flipSeed k (p i)))))/2|

end LargeIndependentSets.BooleanJunta

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_CellLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open MeasureTheory Set
open scoped BigOperators Classical NNReal ENNReal

noncomputable def cellLaw (n m : ℕ) : Measure (Fin n → Cube m) := uniformLaw (Fin n → Cube m)
instance cellLaw_probability (n m : ℕ) : IsProbabilityMeasure (cellLaw n m) :=
  inferInstanceAs (IsProbabilityMeasure (uniformLaw (Fin n → Cube m)))

noncomputable def cellPoint {n m : ℕ} (q : Fin n → Cube m) : Fin n → ℝ :=
  fun i => scalarCell (q i) 0

noncomputable def rowFlip {n m : ℕ} (i : Fin n) (k : Fin m) (q : Fin n → Cube m) :
    Fin n → Cube m := Function.update q i (flip k (q i))
noncomputable def rowInfluence {n m : ℕ} (h : (Fin n → Cube m) → ℝ)
    (i : Fin n) (k : Fin m) : ℝ := 𝔼 q, |(h q-h (rowFlip i k q))/2|

end LargeIndependentSets.BooleanJunta

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_RowBitsEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open MeasureTheory Set
open scoped BigOperators Classical NNReal ENNReal

def rowBitsEquiv (n m : ℕ) : (Fin n → Cube m) ≃ ((Fin n × Fin m) → Bool) where
  toFun q ik := bit (q ik.1) ik.2
  invFun b i := ofBits (fun k => b (i,k))
  left_inv q := by funext i; exact ofBits_bit (q i)
  right_inv b := by funext ik; simp

end LargeIndependentSets.BooleanJunta

namespace LargeIndependentSets.ProductAveraging
open MeasureTheory Set
open scoped BigOperators Classical

noncomputable def average {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) (S : Finset ι) (f : (ι → α) → ℝ) (x : ι → α) : ℝ :=
  ∫ y, f (mix S (x,y)) ∂Measure.pi (fun _ : ι => μ)

end LargeIndependentSets.ProductAveraging

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_CoordinateMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.ProductAveraging
open MeasureTheory Set
open scoped BigOperators Classical

noncomputable def coordinateMean {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) (i : ι) (f : (ι → α) → ℝ) (x : ι → α) : ℝ :=
  ∫ t, f (Function.update x i t) ∂μ

noncomputable def influenceSq {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) (i : ι) (f : (ι → α) → ℝ) : ℝ :=
  ∫ x, (f x-coordinateMean μ i f x)^2 ∂Measure.pi (fun _ : ι => μ)

end LargeIndependentSets.ProductAveraging

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_SwapCoords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.ProductAveraging
open MeasureTheory Set
open scoped BigOperators Classical

noncomputable def swapCoords {ι α : Type*} (S : Finset ι) (p : (ι → α) × (ι → α)) :=
  (mix S p, mix S p.swap)

noncomputable def subsetEnergy {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) (S : Finset ι) (f : (ι → α) → ℝ) : ℝ :=
  ∫ p : (ι→α)×(ι→α), (f p.1-f (mix Sᶜ p))^2
    ∂(Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ))

end LargeIndependentSets.ProductAveraging

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_Circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open MeasureTheory Set
open scoped BigOperators Classical NNReal

abbrev Circle := AddCircle (1:ℝ)
instance circleProbability : IsProbabilityMeasure (volume : Measure Circle) where
  measure_univ := by simp [Circle]
noncomputable def realToTorus {n : ℕ} (x : Fin n → ℝ) : Fin n → Circle := fun i => (x i : Circle)

end LargeIndependentSets

namespace LargeIndependentSets.ProductAveraging
open MeasureTheory Set
open scoped BigOperators Classical NNReal
noncomputable def reindex {ι κ α : Type*} (e : ι ≃ κ) (x : ι → α) : κ → α := x ∘ e.symm

end LargeIndependentSets.ProductAveraging

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_ArbitraryRealJunta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.PhaseTest
open MeasureTheory Set
open scoped BigOperators Classical NNReal
abbrev Circle := AddCircle (1:ℝ)
instance circleProbability : IsProbabilityMeasure (volume : Measure Circle) where
  measure_univ := by simp [Circle]
noncomputable def rotationLaw : Measure ℝ := volume.restrict (Ico 0 1)
instance rotationProbability : IsProbabilityMeasure rotationLaw where
  measure_univ := by simp [rotationLaw]
noncomputable def representative (x : Circle) : ℝ := (AddCircle.equivIco (1:ℝ) 0 x).val
noncomputable def rotate (z : Circle) (x : ℝ) : ℝ := representative ((x : Circle)+z)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type*} [∀ i, Fintype (M i)]
variable {κ τ : Type*}

noncomputable def phase (p : ∀ j, κ → M j) (t : ι → ℝ) (θ : (Sigma M) → ℝ) : κ → Circle :=
  fun k => ∑ j, ((t j * θ ⟨j,p j k⟩ : ℝ) : Circle)
noncomputable def auxiliary (p : ∀ j, κ → M j) (r : κ → τ) (a : τ → ι)
    (t : ι → ℝ) (θ : Sigma M → ℝ) (z : ι → Circle) : κ → Circle :=
  fun k => z (a (r k)) + phase p t θ k
noncomputable def blockShift (q : ∀ j, M j → τ) (a : τ → ι) (j : ι)
    (z : ι → Circle) (θ : Sigma M → ℝ) : Sigma M → ℝ :=
  fun c => if c.1 = j then rotate (z (a (q c.1 c.2))) (θ c) else θ c

end LargeIndependentSets.PhaseTest

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_ExtensionLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets

section
open MeasureTheory Set
open Filter
open scoped Topology

noncomputable def extensionLaw {s d n : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (h : B.card = n)
    (μ : ProbabilityMeasure (ListPattern s d (Fin n))) :
    ProbabilityMeasure (ListPattern s d X) :=
  μ.map (measurable_of_finite (ListPattern.extendFin B h)).aemeasurable

noncomputable def embeddingInside {n k : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (hB : B.card = k) (e : Fin n ↪o X) (h : ∀ i, e i ∈ B) :
    Fin n ↪o Fin k :=
  ({ toFun := fun i => ⟨e i, h i⟩
     inj' := fun _ _ he => e.injective (congrArg Subtype.val he)
     map_rel_iff' := e.map_rel_iff } : Fin n ↪o B).trans
      (B.orderIsoOfFin hB).symm.toOrderEmbedding

noncomputable def rationalExhaustion (k : ℕ) : Finset ℚ :=
  (Finset.range k).map (Denumerable.eqv ℚ).symm.toEmbedding

end

open Filter

noncomputable def tailLarge : ℕ → (Finset ℕ → Prop) → Prop
  | 0, P => P ∅
  | n + 1, P => ∀ᶠ x in (Filter.hyperfilter ℕ : Filter ℕ), tailLarge n (fun S => P (insert x S))

def RamseyInvariant (n : ℕ) (P : Finset ℕ → Prop) (H : Finset ℕ) : Prop :=
  ∀ S ⊆ H, S.card ≤ n → tailLarge (n - S.card) (fun T => P (S ∪ T))

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_Small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets

section
def Small {r : ℕ} (s : ℕ) (I : Finset (Fin r)) : Prop :=
  I.Nonempty ∧ I.card ≤ s

def Separated {r : ℕ} (I J : Finset (Fin r)) : Prop :=
  ∀ i ∈ I, ∀ j ∈ J, i < j

def Aligned {r : ℕ} {M : Type} (A : Finset (Fin r) → Finset M)
    (B : Finset (Fin r)) : Prop :=
  ∃ a : M → Fin r, (∀ x, a x ∈ B) ∧
    ∀ I, I.Nonempty → I ⊆ B → ∀ x ∈ A I, a x ∈ I

structure LayerLaw (r s : ℕ) where
  weight : Finset (Fin r) → ℚ
  nonneg : ∀ B, 0 ≤ weight B
  total : ∑ B, weight B = 1
  support : ∀ B, B.card ≠ s → weight B = 0

noncomputable def LayerLaw.badMass {r s : ℕ} (μ : LayerLaw r s)
    {M : Type} (A : Finset (Fin r) → Finset M) : ℚ := by
  classical
  exact ∑ B, if Aligned A B then 0 else μ.weight B

def DistributionalAlignment : Prop :=
  ∀ s d : ℕ, 1 ≤ s → 1 ≤ d → ∀ η : ℝ, 0 < η →
    ∃ r : ℕ, s ≤ r ∧ ∃ μ : LayerLaw r s,
      ∀ (M : Type) [DecidableEq M] (A : Finset (Fin r) → Finset M),
        (∀ I, Small s I → (A I).card ≤ d) →
        (∀ I J, Small s I → Small s J → Separated I J → Disjoint (A I) (A J)) →
        (μ.badMass A : ℝ) ≤ η

open scoped Classical BigOperators

noncomputable def actualSlot {s d r : ℕ} {M : Type*}
    (A : Finset (Fin r) → Finset M) (a : ListSlot s d (Fin r)) : Option M :=
  if h : a.2.val < (A a.1.val).card then
    some ((A a.1.val).equivFin.symm ⟨a.2.val, h⟩).val else none

lemma actualSlot_some_mem {s d r : ℕ} {M : Type*}
    (A : Finset (Fin r) → Finset M) (a : ListSlot s d (Fin r)) (x : M)
    (h : actualSlot A a = some x) : x ∈ A a.1.val := by
  unfold actualSlot at h
  split_ifs at h with ha
  · have he := Option.some.inj h
    exact he ▸ ((A a.1.val).equivFin.symm ⟨a.2.val, ha⟩).property

lemma actualSlot_unique {s d r : ℕ} {M : Type*}
    (A : Finset (Fin r) → Finset M) (a b : ListSlot s d (Fin r))
    (hI : a.1 = b.1) (he : actualSlot A a = actualSlot A b)
    (ha : actualSlot A a ≠ none) : a.2 = b.2 := by
  obtain ⟨I, i⟩ := a
  obtain ⟨J, j⟩ := b
  dsimp at hI
  subst J
  unfold actualSlot at he ha
  split_ifs at he with hi hj
  · apply Fin.ext
    have h := (A I.val).equivFin.symm.injective (Subtype.ext (Option.some.inj he))
    exact congrArg (fun z : Fin (A I.val).card => z.val) h
  · exact False.elim (ha (by simp [hi]))

noncomputable def actualPattern {s d r : ℕ} {M : Type*}
    (A : Finset (Fin r) → Finset M)
    (hsep : ∀ I J, Small s I → Small s J → Separated I J → Disjoint (A I) (A J)) :
    ListPattern s d (Fin r) :=
  ⟨fun a b => decide (actualSlot A a = actualSlot A b ∧ actualSlot A a ≠ none), by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b h
      have hh := of_decide_eq_true h
      exact decide_eq_true (And.intro hh.1.symm (hh.1 ▸ hh.2))
    · intro a b c hab hbc
      have hab' := of_decide_eq_true hab
      have hbc' := of_decide_eq_true hbc
      exact decide_eq_true ⟨hab'.1.trans hbc'.1, hab'.2⟩
    · intro a b h hab
      have hh := of_decide_eq_true h
      exact actualSlot_unique A a b hab hh.1 hh.2
    · intro a b hsep'
      apply decide_eq_false
      rintro ⟨he, hne⟩
      obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hne
      have ha := actualSlot_some_mem A a x hx
      have hb := actualSlot_some_mem A b x (he.symm.trans hx)
      exact Finset.disjoint_left.mp (hsep a.1.val b.1.val a.1.property b.1.property hsep') ha hb⟩

end

noncomputable def ListSlot.pullbackFin {s d n : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (hB : B.card = n) (a : ListSlot s d X) (ha : a.1.val ⊆ B) :
    ListSlot s d (Fin n) :=
  ListSlot.map (B.orderIsoOfFin hB).symm.toEmbedding (a.inside B ha)

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_SubchainView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped Classical BigOperators

@[ext] structure SubchainView (U V L R : Type*) (n : ℕ) (I : Finset (Fin (n+1))) where
  question : ∀ j : I, MixedTuple U V n j.val.val
  projection : ∀ i j : I, i.val ≤ j.val →
    MixedTuple L R n i.val.val → MixedTuple L R n j.val.val

def chainView {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} (c : Fin n → C) (I : Finset (Fin (n+1))) : SubchainView U V L R n I where
  question j := occurrenceTuple lc c j.val.val
  projection i j hij := chainComposite lc c i.val.val j.val.val hij

abbrev SubchainCoord (L R : Type*) (n : ℕ) (I : Finset (Fin (n+1))) :=
  Σ j : I, MixedTuple L R n j.val.val

noncomputable def leftEntry {L R : Type*} [Nonempty L] {n i : ℕ}
    (h : Fin n) (x : MixedTuple L R n i) : L := (x.val h).elim (fun _ => Classical.arbitrary L) id
noncomputable def rightEntry {L R : Type*} [Nonempty R] {n i : ℕ}
    (h : Fin n) (x : MixedTuple L R n i) : R := (x.val h).elim id (fun _ => Classical.arbitrary R)

noncomputable def terminalList {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} (c : Fin n → C) (I : Finset (Fin (n+1)))
    (S : Finset (SubchainCoord L R n I)) : Finset (MixedTuple L R n n) :=
  S.image (fun x => chainComposite lc c x.1.val.val n (by have := x.1.val.isLt; omega) x.2)

noncomputable def ownQuestionList {C U X : Type*} (q : C → U) (f : C → Finset X)
    (u : U) : Finset X :=
  if h : ∃ c, q c = u then f h.choose else ∅

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_DeletedLayerEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open MeasureTheory ProductAveraging PhaseTest
open scoped BigOperators Classical NNReal

def deletedLayerEquiv {n : ℕ} {B : Finset (Fin (n+1))} (i : B) :
    {j : B // j ≠ i} ≃ (B.erase i.val) where
  toFun j := ⟨j.val.val, Finset.mem_erase.mpr ⟨fun h => j.property (Subtype.ext h), j.val.property⟩⟩
  invFun j := ⟨⟨j.val, (Finset.mem_erase.mp j.property).2⟩,
    fun h => (Finset.mem_erase.mp j.property).1 (congrArg Subtype.val h)⟩
  left_inv j := by cases j; rfl
  right_inv j := by cases j; rfl

def deletedCoordEquiv {L R : Type} {n : ℕ} {B : Finset (Fin (n+1))} (i : B) :
    (Sigma fun j : {j : B // j ≠ i} => MixedTuple L R n j.val.val.val) ≃
      SubchainCoord L R n (B.erase i.val) where
  toFun d := ⟨deletedLayerEquiv i d.1, d.2⟩
  invFun d := ⟨(deletedLayerEquiv i).symm d.1, d.2⟩
  left_inv d := by cases d; rfl
  right_inv d := by cases d; rfl

lemma deletion_nonempty {n : ℕ} {B : Finset (Fin (n+1))} (hB : 2 ≤ B.card) (i : B) :
    (B.erase i.val).Nonempty := by
  apply Finset.card_pos.mp
  rw [Finset.card_erase_of_mem i.property]
  omega

lemma deletion_small {n s : ℕ} {B : Finset (Fin (n+1))} (hB : 2 ≤ B.card) (hBs : B.card ≤ s)
    (i : B) : Small s (B.erase i.val) :=
  ⟨deletion_nonempty hB i, (Finset.card_le_card (Finset.erase_subset _ _)).trans hBs⟩

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Encoding_Normalizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.Coefficient
open scoped BigOperators Classical

noncomputable def normalizer (m : ℕ) (ρ : ℝ) : ℝ := ∑ k : Fin (m+1), ρ^k.val
noncomputable def levelMass (m : ℕ) (ρ : ℝ) (k : Fin (m+1)) : ℝ :=
  ρ^k.val / normalizer m ρ
noncomputable def mass {ι : Type*} [Fintype ι] (m : ℕ) (ρ : ℝ)
    (t : ι → Fin (m+1)) : ℝ := ∏ i, levelMass m ρ (t i)

noncomputable def lower {ι : Type*} [DecidableEq ι] {m : ℕ}
    (i : ι) (t : ι → Fin (m+1)) : ι → Fin (m+1) :=
  Function.update t i ⟨(t i).val - 1, by omega⟩

end LargeIndependentSets.Coefficient

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_Full
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.Coefficient
open MeasureTheory Set
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def Full {m : ℕ} (t : ι → Fin (m+1)) : Prop := ∃ i, (t i).val = m

end LargeIndependentSets.Coefficient

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_InfluenceSqParamMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.PhaseTest
open MeasureTheory Set
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type*} [∀ j, Fintype (M j)]
variable {κ κ' τ : Type*}

def eraseCoord (i : ι) : (Sigma fun j : {j : ι // j ≠ i} => M j.val) → Sigma M :=
  fun c => ⟨c.1.val,c.2⟩

def restrictRotations (i : ι) (θ : Sigma M → ℝ) :
    (Sigma fun j : {j : ι // j ≠ i} => M j.val) → ℝ := θ ∘ eraseCoord i

end LargeIndependentSets.PhaseTest

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_SquareNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.ProductAveraging
open MeasureTheory Set
open scoped BigOperators Classical
noncomputable def squareNorm {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) : ℝ :=
  Real.sqrt (∫ x, (f x)^2 ∂μ)

noncomputable def influenceNorm {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) (i : ι) (f : (ι → α) → ℝ) : ℝ := Real.sqrt (influenceSq μ i f)
end LargeIndependentSets.ProductAveraging

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_AuxiliaryJointMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.Coefficient
open scoped Classical
noncomputable def value {m : ℕ} (k : Fin (m+1)) : ℝ := k.val / (m:ℝ)
end LargeIndependentSets.Coefficient

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_FullAbsorptionSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open scoped BigOperators Classical

def gridIndex : {k : ℕ} → Cube k → ℕ
  | 0, _ => 0
  | k+1, (b,x) => (if b then 2^k else 0) + gridIndex x
lemma gridIndex_lt {k : ℕ} (x : Cube k) : gridIndex x < 2^k := by
  induction k with
  | zero => simp [gridIndex]
  | succ k ih =>
    rcases x with ⟨b,x⟩
    have hx := ih x
    have hp : 0 < 2^k := by positivity
    cases b <;> simp only [gridIndex, Bool.false_eq_true, ↓reduceIte, zero_add, pow_succ] <;> omega
lemma gridIndex_injective (k : ℕ) : Function.Injective (@gridIndex k) := by
  induction k with
  | zero => intro x y _; exact Subsingleton.elim _ _
  | succ k ih =>
    intro ⟨b,x⟩ ⟨c,y⟩ he
    have hx := gridIndex_lt x
    have hy := gridIndex_lt y
    cases b <;> cases c <;> simp only [gridIndex, Bool.false_eq_true, ↓reduceIte, zero_add] at he
    · exact Prod.ext rfl (ih he)
    · omega
    · omega
    · exact Prod.ext rfl (ih (Nat.add_left_cancel he))
lemma cube_card (k : ℕ) : Fintype.card (Cube k) = 2^k := by
  induction k with
  | zero => simp [Cube]
  | succ k ih =>
    change Fintype.card (Bool × Cube k) = _
    simp only [Fintype.card_prod, Fintype.card_bool, ih, pow_succ]
    omega
noncomputable def gridEquiv (k : ℕ) : Cube k ≃ Fin (2^k) :=
  Equiv.ofBijective (fun x => ⟨gridIndex x, gridIndex_lt x⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun x y h => gridIndex_injective k (congrArg Fin.val h), by simp [cube_card]⟩)
end LargeIndependentSets.BooleanJunta

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_SubchainBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open MeasureTheory
open scoped Classical BigOperators NNReal
open PhaseTest ProductAveraging

noncomputable instance mixedTupleFintype {A B : Type*} [Fintype A] [Fintype B] (n i : ℕ) :
    Fintype (MixedTuple A B n i) := by
  classical
  unfold MixedTuple
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def subchainBase {n : ℕ} (I : Finset (Fin (n+1))) (hI : I.Nonempty) : I :=
  ⟨I.min' hI, I.min'_mem hI⟩

lemma subchainBase_le {n : ℕ} (I : Finset (Fin (n+1))) (hI : I.Nonempty) (j : I) :
    (subchainBase I hI).val ≤ j.val := Finset.min'_le _ _ j.property

noncomputable def viewFunction {U V L R : Type} {n : ℕ}
    (F : ∀ q : LayerQuestion U V n, (LayerAnswer L R q → Circle) → ℝ)
    {I : Finset (Fin (n+1))} (hI : I.Nonempty) (v : SubchainView U V L R n I)
    {m : ℕ} (t : I → Fin (m+1)) (θ : SubchainCoord L R n I → ℝ) : ℝ :=
  F ⟨(subchainBase I hI).val, v.question (subchainBase I hI)⟩
    (phase (fun j => v.projection (subchainBase I hI) j (subchainBase_le I hI j))
      (fun j => Coefficient.value (t j)) θ)

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_DeletedProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets

section
open MeasureTheory ProductAveraging PhaseTest
open scoped BigOperators Classical NNReal

variable {U V L R C : Type}
variable {n : ℕ} (lc : LabelCoverData U V L R C) (chain : Fin n → C)

noncomputable def deletedProjection {B : Finset (Fin (n+1))} (hB : 2 ≤ B.card) (i : B)
    (j : {j : B // j ≠ i}) :
    MixedTuple L R n (subchainBase (B.erase i.val) (deletion_nonempty hB i)).val.val →
      MixedTuple L R n j.val.val.val :=
  chainComposite lc chain _ _ (subchainBase_le _ (deletion_nonempty hB i) (deletedLayerEquiv i j))

noncomputable def ruleUnion {s m : ℕ}
    (rule : ∀ (I : Finset (Fin (n+1))), Small s I →
      SubchainView U V L R n I → (I → Fin (m+1)) → Finset (SubchainCoord L R n I))
    (I : Finset (Fin (n+1))) (v : SubchainView U V L R n I) : Finset (SubchainCoord L R n I) :=
  if hI : Small s I then Finset.univ.biUnion (rule I hI v) else ∅

end

section
open MeasureTheory ProductAveraging PhaseTest
open scoped BigOperators Classical NNReal
variable {U V L R C : Type} [Fintype L] [Fintype R]
variable {n s m : ℕ} (lc : LabelCoverData U V L R C) (chain : Fin n → C)

noncomputable def deletedRule
    (rule : ∀ (I : Finset (Fin (n+1))), Small s I →
      SubchainView U V L R n I → (I → Fin (m+1)) → Finset (SubchainCoord L R n I))
    {B : Finset (Fin (n+1))} (hB : 2 ≤ B.card) (hBs : B.card ≤ s) (i : B)
    (t : {j : B // j ≠ i} → Fin (m+1)) :
    Finset (Sigma fun j : {j : B // j ≠ i} => MixedTuple L R n j.val.val.val) :=
  (rule (B.erase i.val) (deletion_small hB hBs i) (chainView lc chain _)
    (fun j => t ((deletedLayerEquiv i).symm j))).image (deletedCoordEquiv i).symm

end

open MeasureTheory ProductAveraging PhaseTest Coefficient BooleanJunta
open scoped BigOperators Classical NNReal

noncomputable def fiberSquare {U V L R C : Type} [Fintype L] [Fintype R]
    {n : ℕ} (lc : LabelCoverData U V L R C) (chain : Fin n → C)
    (F : ∀ q : LayerQuestion U V n, (LayerAnswer L R q → Circle) → ℝ)
    (B : Finset (Fin (n+1))) (hB : B.Nonempty) (m : ℕ) (ρ : ℝ) (k : ℕ) : ℝ :=
  ∑ t : B → Fin (m+1), mass m ρ t *
    𝔼 v : SubchainCoord L R n B → Cube k,
      (viewFunction F hB (chainView lc chain B) t (fun c => scalarCell (v c) 0))^2

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_FiniteParameterSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.PhaseTest
open scoped BigOperators Classical
open Coefficient BooleanJunta
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type} [∀ j, Fintype (M j)]
variable {κ : Type} [Fintype κ]

def gridLocation (p : ∀ j, κ → M j) {m P : ℕ}
    (t : ι → Fin (m+1)) (θ : Sigma M → Fin P) : κ → ZMod (m*P) :=
  fun k => ∑ j, ((t j).val * (θ ⟨j,p j k⟩).val : ℕ)

end LargeIndependentSets.PhaseTest

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_RationalLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped Classical BigOperators

structure RationalLaw (O : Type*) [Fintype O] where
  weight : O → ℚ
  nonneg : ∀ o, 0 ≤ weight o
  total : ∑ o, weight o = 1

namespace RationalLaw
variable {O : Type*} [Fintype O]

def denominator (p : RationalLaw O) : ℕ := ∏ o, (p.weight o).den

def copies (p : RationalLaw O) (o : O) : ℕ :=
  (p.denominator / (p.weight o).den) * (p.weight o).num.toNat

lemma denominator_pos (p : RationalLaw O) : 0 < p.denominator := by
  apply Finset.prod_pos
  intro o _; exact Rat.den_pos _

lemma denominator_dvd (p : RationalLaw O) (o : O) :
    (p.weight o).den ∣ p.denominator := Finset.dvd_prod_of_mem _ (Finset.mem_univ o)

lemma copies_eq (p : RationalLaw O) (o : O) :
    (p.copies o : ℚ) = p.denominator * p.weight o := by
  have hnum : 0 ≤ (p.weight o).num := Rat.num_nonneg.mpr (p.nonneg o)
  have hden : ((p.weight o).den : ℚ) ≠ 0 := by
    exact_mod_cast (Rat.den_pos (p.weight o)).ne'
  have hdiv : (p.denominator / (p.weight o).den : ℕ) * (p.weight o).den = p.denominator :=
    Nat.div_mul_cancel (p.denominator_dvd o)
  have hdiv' : ((p.denominator / (p.weight o).den : ℕ) : ℚ) * (p.weight o).den = p.denominator := by
    exact_mod_cast hdiv
  have hnum' : ((p.weight o).num.toNat : ℚ) = (p.weight o).num := by
    exact_mod_cast Int.toNat_of_nonneg hnum
  rw [copies, Nat.cast_mul, hnum']
  rw [← Rat.mul_den_eq_num]
  calc
    _ = (((p.denominator / (p.weight o).den : ℕ) : ℚ) * (p.weight o).den) * p.weight o := by ring
    _ = _ := by rw [hdiv']

lemma total_copies (p : RationalLaw O) : ∑ o, p.copies o = p.denominator := by
  have h : (∑ o, (p.copies o : ℚ)) = p.denominator := by
    simp_rw [p.copies_eq]
    rw [← Finset.mul_sum, p.total, mul_one]
  exact_mod_cast h

abbrev Expanded (p : RationalLaw O) := Σ o : O, Fin (p.copies o)

lemma card_expanded (p : RationalLaw O) : Fintype.card p.Expanded = p.denominator := by
  simp only [Expanded, Fintype.card_sigma, Fintype.card_fin, p.total_copies]

noncomputable instance expandedNonempty (p : RationalLaw O) : Nonempty p.Expanded :=
  Fintype.card_pos_iff.mp (by rw [p.card_expanded]; exact p.denominator_pos)

abbrev Vertices (p : RationalLaw O) (C : Type*) (n : ℕ) := (Fin n → C) × p.Expanded

end RationalLaw

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_Uniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.RationalLaw
open scoped BigOperators Classical
variable {I : Type*} [Fintype I]

noncomputable def uniform (I : Type*) [Fintype I] [Nonempty I] : RationalLaw I where
  weight _ := 1 / Fintype.card I
  nonneg _ := by positivity
  total := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h : (Fintype.card I : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp

noncomputable def bind (p : RationalLaw I) {J : I → Type*} [∀ i, Fintype (J i)]
    (q : ∀ i, RationalLaw (J i)) : RationalLaw (Sigma J) where
  weight o := p.weight o.1 * (q o.1).weight o.2
  nonneg o := mul_nonneg (p.nonneg _) ((q _).nonneg _)
  total := by
    simp only [Fintype.sum_sigma, ← Finset.mul_sum, fun i => (q i).total, mul_one]
    exact p.total

noncomputable def pi [DecidableEq I] {J : I → Type*} [∀ i, Fintype (J i)]
    (q : ∀ i, RationalLaw (J i)) : RationalLaw (∀ i, J i) where
  weight x := ∏ i, (q i).weight (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => (q i).nonneg _)
  total := by
    rw [← Fintype.prod_sum]
    simp only [fun i => (q i).total, Finset.prod_const_one]

end LargeIndependentSets.RationalLaw

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_Law
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.Coefficient
open scoped BigOperators Classical

noncomputable def law (m : ℕ) {ρ : ℚ} (hρ : 0 ≤ ρ) : RationalLaw (Fin (m+1)) where
  weight j := ρ^j.val / ∑ k : Fin (m+1), ρ^k.val
  nonneg j := div_nonneg (pow_nonneg hρ _) (Finset.sum_nonneg (fun k _ => pow_nonneg hρ _))
  total := by
    have hp : 0 < ∑ k : Fin (m+1), ρ^k.val := by
      have h := Finset.single_le_sum (f:=fun k : Fin (m+1) => ρ^k.val)
        (fun j _ => pow_nonneg hρ _) (Finset.mem_univ (0 : Fin (m+1)))
      have h1 : (1:ℚ) ≤ ∑ k : Fin (m+1), ρ^k.val := by simpa using h
      exact lt_of_lt_of_le (by norm_num : (0:ℚ)<1) h1
    rw [← Finset.sum_div, div_self hp.ne']

end LargeIndependentSets.Coefficient

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_Supported2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped BigOperators Classical
open BooleanJunta PhaseTest Coefficient

abbrev SamplerOutcome (L R : Type) (n s m k : ℕ) :=
  Σ B : {B : Finset (Fin (n+1)) // B.card = s},
    Σ _t : B.val → Fin (m+1), SubchainCoord L R n B.val → Cube k

lemma supported_nonempty {n s : ℕ} (hs : 0 < s)
    (B : {B : Finset (Fin (n+1)) // B.card = s}) : B.val.Nonempty :=
  Finset.card_pos.mp (by omega)

noncomputable def sampleLocation {U V L R C : Type} [Fintype L] [Fintype R]
    {n s m k : ℕ} (lc : LabelCoverData U V L R C) (chain : Fin n → C) (hs : 0 < s)
    (o : SamplerOutcome L R n s m k) :
    GridLocation (LayerAnswer L R (U:=U) (V:=V) (n:=n)) (m*2^k) :=
  let b := subchainBase o.1.val (supported_nonempty hs o.1)
  ⟨occurrenceQuestion lc chain b.val,
    gridLocation (fun j : o.1.val =>
      chainComposite lc chain b.val.val j.val.val (subchainBase_le _ _ j))
      o.2.1 (fun c => gridEquiv k (o.2.2 c))⟩

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_FiniteGame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped BigOperators

noncomputable def finiteGame {I J : Type*} [Fintype I] [Fintype J]
    (b : I → J → ℝ) (p : I → ℝ) (q : J → ℝ) : ℝ :=
  ∑ i, ∑ j, p i * q j * b i j

def finiteProbabilitySimplex (Index : Type*) [Fintype Index] : Set (Index → ℝ) :=
  { weights | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1 }

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_SimplexLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open MeasureTheory
open scoped BigOperators
open scoped Classical

noncomputable def simplexLaw {J : Type*} [Fintype J] [MeasurableSpace J]
    (q : J → ℝ) (hq : q ∈ finiteProbabilitySimplex J) : ProbabilityMeasure J := by
  let p : PMF J := PMF.ofFintype (fun j => ENNReal.ofReal (q j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hq.1 j), hq.2, ENNReal.ofReal_one])
  exact ⟨p.toMeasure, (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_CircleRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped ENNReal NNReal

noncomputable def circleRound (D : ℕ) (x : UnitAddCircle) : ZMod D :=
  (⌊(D : ℝ) * circleRep x⌋₊ : ZMod D)

noncomputable def torusRound {ι : Type*} (D : ℕ) (x : ι → UnitAddCircle) : ι → ZMod D :=
  fun k => circleRound D (x k)

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_SwapOccurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped Classical BigOperators

def swapOccurrence {C : Type*} {n : ℕ} (h : Fin n) :
    ((Fin n → C) × C) → ((Fin n → C) × C) :=
  fun p => (Function.update p.1 h p.2, p.1 h)

def ListsSeparated {r s : ℕ} {M : Type*} (A : Finset (Fin r) → Finset M) : Prop :=
  ∀ I J, Small s I → Small s J → Separated I J → Disjoint (A I) (A J)

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_SamplerParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped Classical BigOperators
open MeasureTheory PhaseTest

structure SamplerParameters where
  n : ℕ
  s : ℕ
  hs : 0 < s
  m : ℕ
  hm : 0 < m
  k : ℕ
  hk : 1 ≤ k
  ρ : ℚ
  hρ : 0 ≤ ρ
  μ : LayerLaw (n+1) s

namespace SamplerParameters
instance instNeZeroNatHMulMHPowOfNatK (p : SamplerParameters) : NeZero (p.m*2^p.k) :=
  ⟨Nat.ne_of_gt (Nat.mul_pos p.hm (by positivity))⟩

lemma even (p : SamplerParameters) : Even (p.m*2^p.k) := by
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one p.hk))
  refine ⟨p.m*2^k, ?_⟩
  rw [hk,pow_succ]
  ring

end SamplerParameters

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_Simple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped Classical BigOperators

namespace Graph

noncomputable def ofSimple {W : Type} [Fintype W] [Nonempty W] (H : SimpleGraph W) : Graph where
  vertices := Fintype.card W
  nonempty := Fintype.card_pos
  adj u v := decide (H.Adj ((Fintype.equivFin W).symm u) ((Fintype.equivFin W).symm v))
  symm u v := by simp only [decide_eq_decide]; exact H.adj_comm _ _
  loopless u := by simp

def clique (q : ℕ) (hq : 0 < q) : Graph where
  vertices := q
  nonempty := hq
  adj u v := decide (u ≠ v)
  symm u v := by simp [ne_comm]
  loopless u := by simp

end Graph

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_ClausePolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open IndependentSetsGames.Foundations
open scoped Classical
noncomputable section

lemma frame_length (b : List Bool) : (frame b).length = 2*b.length+1 := by
  induction b with
  | nil => rfl
  | cons b bs ih => simp only [frame,List.length_cons,ih]; omega

end
end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_Total
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets

namespace ShortestPaths
open scoped ENNReal

def pivot {X A : Type*} [Min A] [Add A] (w : X → X → A) (k : X) (x y : X) : A :=
  min (w x y) (w x k + w k y)

def closure {X A : Type*} [Min A] [Add A] (w : X → X → A) : List X → X → X → A
  | [] => w
  | k::ks => closure (pivot w k) ks

lemma pivot_le {X : Type*} (w : X → X → ℝ≥0∞) (k x y : X) : pivot w k x y ≤ w x y :=
  min_le_left _ _

lemma pivot_at {X : Type*} (w : X → X → ℝ≥0∞) (k x y : X) :
    pivot w k x y ≤ pivot w k x k + pivot w k k y := by
  simp only [pivot, min_eq_left (le_self_add), min_eq_left (le_add_self)]
  exact min_le_right _ _

lemma pivot_preserves {X : Type*} (w : X → X → ℝ≥0∞) (k z : X)
    (h : ∀ x y, w x y ≤ w x z + w z y) :
    ∀ x y, pivot w k x y ≤ pivot w k x z + pivot w k z y := by
  intro x y
  unfold pivot
  rw [min_add,add_min,add_min]
  apply le_min
  · apply le_min
    · exact (min_le_left _ _).trans (h x y)
    · exact (min_le_right _ _).trans (by
        simpa only [add_assoc,add_comm,add_left_comm] using add_le_add_right (h x k) (w k y))
  · apply le_min
    · exact (min_le_right _ _).trans (by
        simpa only [add_assoc,add_comm,add_left_comm] using add_le_add_left (h k y) (w x k))
    · exact (min_le_right _ _).trans (by
        have hh : w x k + w k y ≤ w x k + (w k z + w z k) + w k y :=
          add_le_add le_self_add le_rfl
        simpa only [add_assoc,add_comm,add_left_comm] using hh)

lemma closure_le {X : Type*} (w : X → X → ℝ≥0∞) (ks : List X) (x y : X) :
    closure w ks x y ≤ w x y := by
  induction ks generalizing w with
  | nil => exact le_rfl
  | cons k ks ih => exact (ih _).trans (pivot_le _ _ _ _)

lemma closure_preserves {X : Type*} (w : X → X → ℝ≥0∞) (ks : List X) (z : X)
    (h : ∀ x y, w x y ≤ w x z + w z y) :
    ∀ x y, closure w ks x y ≤ closure w ks x z + closure w ks z y := by
  induction ks generalizing w with
  | nil => exact h
  | cons k ks ih => exact ih _ (pivot_preserves w k z h)

lemma closure_at {X : Type*} (w : X → X → ℝ≥0∞) (ks : List X) {z : X} (hz : z ∈ ks) :
    ∀ x y, closure w ks x y ≤ closure w ks x z + closure w ks z y := by
  induction ks generalizing w with
  | nil => simp at hz
  | cons k ks ih =>
    rcases List.mem_cons.mp hz with he | hz
    · subst z
      exact closure_preserves _ ks k (pivot_at w k)
    · exact ih _ hz

lemma distance_le_closure {X : Type*} (w : X → X → ℝ≥0∞) (ks : List X) (x y : X) :
    pathDistance w x y ≤ closure w ks x y := by
  have h : ∀ (v : X → X → ℝ≥0∞), (∀ x y, pathDistance w x y ≤ v x y) →
      ∀ x y, pathDistance w x y ≤ closure v ks x y := by
    induction ks with
    | nil => intro v hv; exact hv
    | cons k ks ih =>
      intro v hv
      apply ih
      intro x y
      exact le_min (hv x y) ((pathDistance_triangle w x k y).trans (add_le_add (hv x k) (hv k y)))
  exact h w (pathDistance_le_link w) x y

theorem closure_eq_distance {X : Type*} (w : X → X → ℝ≥0∞) (ks : List X)
    (hks : ∀ z, z ∈ ks) (x y : X) : closure w ks x y = pathDistance w x y := by
  apply le_antisymm ?_ (distance_le_closure w ks x y)
  apply le_iInf
  intro zs
  induction zs generalizing x with
  | nil => exact closure_le w ks x y
  | cons z zs ih =>
    exact (closure_at w ks (hks z) x y).trans (add_le_add (closure_le w ks x z) (ih z))

lemma closure_map {X A B : Type*} [Min A] [Add A] [Min B] [Add B]
    (f : A → B) (hfmin : ∀ a b, f (min a b) = min (f a) (f b))
    (hfadd : ∀ a b, f (a+b) = f a+f b) (w : X → X → A) (ks : List X) :
    (fun x y => f (closure w ks x y)) = closure (fun x y => f (w x y)) ks := by
  induction ks generalizing w with
  | nil => rfl
  | cons k ks ih =>
    simp only [closure]
    rw [ih]
    congr 1
    funext x y
    simp only [pivot,hfmin,hfadd]

abbrev Matrix (n : ℕ) := Vector (Vector ℕ∞ n) n

def Matrix.get {n : ℕ} (a : Matrix n) (i j : Fin n) : ℕ∞ := a[i.val][j.val]

def Matrix.pivot {n : ℕ} (a : Matrix n) (k : Fin n) : Matrix n :=
  letI : Min ℕ∞ := @LinearOrder.toMin ℕ∞ instLinearOrderENat
  Vector.ofFn (fun i => Vector.ofFn (fun j => ShortestPaths.pivot a.get k i j))

def Matrix.run {n : ℕ} (a : Matrix n) : List (Fin n) → Matrix n
  | [] => a
  | k::ks => (a.pivot k).run ks

lemma Matrix.run_get {n : ℕ} (a : Matrix n) (ks : List (Fin n)) :
    (a.run ks).get = closure a.get ks := by
  induction ks generalizing a with
  | nil => rfl
  | cons k ks ih =>
    rw [Matrix.run,ih]
    simp only [closure]
    congr 1
    funext i j
    simp [Matrix.pivot, Matrix.get]

def Matrix.allPairs {n : ℕ} (a : Matrix n) : Matrix n := a.run (List.finRange n)

end ShortestPaths
end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_FiniteScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.FiniteScan
open Turing
open scoped BigOperators

structure State (m : ℕ) where
  input : List Bool
  k : ℕ
  history : ℕ → Fin m

def initial {m : ℕ} (q : Fin m) (input : List Bool) : State m := ⟨input,0,fun _ => q⟩

def step {m : ℕ} (δ : Fin m → Bool → Fin m) (s : State m) : State m where
  input := s.input
  k := s.k+1
  history := if h : s.k < s.input.length then
    Function.update s.history (s.k+1) (δ (s.history s.k) s.input[s.k]) else s.history

noncomputable def lengthPolynomial (m : ℕ) : Polynomial ℕ :=
  (3+2*Polynomial.X)*(2*Polynomial.X+Polynomial.C (m+2))

lemma lengthPolynomial_eval (m N : ℕ) :
    (lengthPolynomial m).eval N = (3+2*N)*(2*N+m+2) := by
  simp [lengthPolynomial,Nat.add_assoc]

end LargeIndependentSets.FiniteScan

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Encoding_BinarySyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BinarySyntax

inductive Phase where
  | headerMark | headerPayload
  | widthStart | widthBit0
  | widthMark1 (b : Bool) | widthBit1 (b : Bool)
  | widthMark2 (b c : Bool)
  | sign (remaining : Fin 3) (first : Bool)
  | mark (remaining : Fin 3)
  | payload (remaining : Fin 3)
  | bad
  deriving DecidableEq, Fintype

def after (r : Fin 3) : Phase :=
  if h : r.val=0 then .widthStart else .sign ⟨r.val-1,by omega⟩ false

def width (n : Fin 4) : Phase :=
  if h : n.val=0 then .widthStart else .sign ⟨n.val-1,by omega⟩ true

def transition : Phase → Bool → Phase
  | .headerMark, true => .headerPayload
  | .headerMark, false => .widthStart
  | .headerPayload, _ => .headerMark
  | .widthStart, true => .widthBit0
  | .widthStart, false => .widthStart
  | .widthBit0, b => .widthMark1 b
  | .widthMark1 b, true => .widthBit1 b
  | .widthMark1 b, false => if b then .sign 0 true else .widthStart
  | .widthBit1 b, c => .widthMark2 b c
  | .widthMark2 b c, false => if c then .sign (if b then 2 else 1) true
      else if b then .sign 0 true else .widthStart
  | .widthMark2 _ _, true => .bad
  | .sign r _, _ => .mark r
  | .mark r, true => .payload r
  | .mark r, false => after r
  | .payload r, _ => .mark r
  | .bad, _ => .bad

def run (q : Phase) (s : List Bool) : Phase := s.foldl transition q

@[simp] lemma run_nil (q : Phase) : run q [] = q := rfl
@[simp] lemma run_cons (q : Phase) (b : Bool) (s : List Bool) :
    run q (b::s) = run (transition q b) s := rfl

noncomputable def phaseEquiv : Phase ≃ Fin (Fintype.card Phase) := Fintype.equivFin Phase
noncomputable def finiteTransition (q : Fin (Fintype.card Phase)) (b : Bool) :=
  phaseEquiv (transition (phaseEquiv.symm q) b)

lemma finite_run (q : Phase) (s : List Bool) :
    s.foldl finiteTransition (phaseEquiv q) = phaseEquiv (run q s) := by
  induction s generalizing q with
  | nil => rfl
  | cons b s ih => simpa [List.foldl_cons,finiteTransition,run,transition] using ih (transition q b)

end LargeIndependentSets.BinarySyntax

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Encoding_BinaryEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BinarySyntax

inductive Mark where
  | first (r : Fin 3)
  | empty
  deriving DecidableEq

def event : Phase → Bool → Option Mark
  | .sign r true, _ => some (.first r)
  | .widthStart, false => some .empty
  | _, _ => none

def shift (k : ℕ) (xs : List (ℕ × Mark)) : List (ℕ × Mark) :=
  xs.map (fun x => (k+x.1,x.2))

@[simp] lemma shift_nil (k : ℕ) : shift k []=[] := rfl
@[simp] lemma shift_cons (k : ℕ) (p : ℕ) (e : Mark) (xs : List (ℕ × Mark)) :
    shift k ((p,e)::xs)=(k+p,e)::shift k xs := rfl
@[simp] lemma shift_append (k : ℕ) (a b : List (ℕ × Mark)) :
    shift k (a++b)=shift k a++shift k b := List.map_append
@[simp] lemma shift_shift (j k : ℕ) (xs : List (ℕ × Mark)) :
    shift j (shift k xs)=shift (j+k) xs := by simp [shift,List.map_map,Function.comp_def,Nat.add_assoc]
@[simp] lemma shift_zero (xs : List (ℕ × Mark)) : shift 0 xs=xs := by simp [shift]

def events (q : Phase) : List Bool → List (ℕ × Mark)
  | [] => []
  | b::s => ((event q b).toList.map (fun e => (0,e))) ++ shift 1 (events (transition q b) s)

def clauseMark (C : List Literal) : ℕ × Mark :=
  if C=[] then (0,.empty) else ((nameBits C.length).length,.first ⟨(C.length-1)%3,Nat.mod_lt _ (by decide)⟩)

end LargeIndependentSets.BinarySyntax

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Encoding_BinaryNameTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BinaryNames
open scoped BigOperators

def raw (s : List Bool) (i : ℕ) : Bool := (s[i]?).getD false

lemma raw_out (s : List Bool) (i : ℕ) (hi : s.length ≤ i) : raw s i = false := by
  simp [raw,List.getElem?_eq_none hi]

lemma end_exists (s : List Bool) (p : ℕ) : ∃ t, raw s (p+1+2*t) = false :=
  ⟨s.length,raw_out s _ (by omega)⟩

def nameLength (s : List Bool) (p : ℕ) : ℕ := Nat.find (end_exists s p)

lemma nameLength_le (s : List Bool) (p : ℕ) : nameLength s p ≤ s.length :=
  Nat.find_min' _ (raw_out s _ (by omega))
lemma nameLength_end (s : List Bool) (p : ℕ) : raw s (p+1+2*nameLength s p) = false :=
  Nat.find_spec (end_exists s p)
lemma nameLength_before (s : List Bool) (p j : ℕ) (hj : j<nameLength s p) :
    raw s (p+1+2*j) = true := by
  have h := Nat.find_min (end_exists s p) hj
  cases he : raw s (p+1+2*j) <;> simp_all

def payload (s : List Bool) (p : ℕ) : List Bool :=
  (List.range (nameLength s p)).map (fun j => raw s (p+2+2*j))

lemma payload_eq_iff (s : List Bool) (p q : ℕ) :
    payload s p = payload s q ↔ nameLength s p = nameLength s q ∧
      ∀ j<nameLength s p, raw s (p+2+2*j) = raw s (q+2+2*j) := by
  constructor
  · intro h
    have hl : nameLength s p=nameLength s q := by simpa [payload] using congrArg List.length h
    refine ⟨hl,?_⟩
    intro j hj
    have he := congrArg (fun l : List Bool => l[j]?) h
    simpa [payload,List.getElem?_range,hl,hl ▸ hj] using he
  · rintro ⟨hl,he⟩
    unfold payload
    rw [← hl]
    apply List.map_congr_left
    intro j hj
    exact he j (List.mem_range.mp hj)

lemma key_exists (s : List Bool) (p : ℕ) :
    ∃ q, q ≤ s.length ∧ payload s q = payload s (min p s.length) :=
  ⟨min p s.length,Nat.min_le_right _ _,rfl⟩

def key (s : List Bool) (p : ℕ) : ℕ := Nat.find (key_exists s p)
lemma key_le (s : List Bool) (p : ℕ) : key s p ≤ s.length := (Nat.find_spec (key_exists s p)).1

def next (s : List Bool) (p : ℕ) : ℕ := p+2+2*nameLength s p

end LargeIndependentSets.BinaryNames

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Encoding_BinaryNormalize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BinaryNormalize
open BinarySyntax BinaryNames
open IndependentSetsGames.Foundations

abbrev varCount (s : List Bool) : ℕ := s.length+1

def eventAt (s : List Bool) (p : ℕ) : Option Mark :=
  event (run .headerMark (s.take p)) (raw s p)

end LargeIndependentSets.BinaryNormalize

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_CircleCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
namespace ShortestPaths
open scoped ENNReal

def circleCost {D : ℕ} (x y : ZMod D) : ℕ :=
  min (x-y).val (D-(x-y).val)

lemma circleCost_dist {D : ℕ} [NeZero D] (x y : ZMod D) :
    dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) = (circleCost x y : ℝ)/D := by
  rw [dist_eq_norm,← map_sub,ZMod.toAddCircle_apply]
  have hh := AddCircle.norm_div_natCast (p:=(1:ℝ)) (m:=(x-y).val) (n:=D)
  simpa only [mul_one,one_mul,Nat.mod_eq_of_lt (ZMod.val_lt _),circleCost] using hh

lemma circleCost_edist {D : ℕ} [NeZero D] (x y : ZMod D) :
    edist (ZMod.toAddCircle x) (ZMod.toAddCircle y) = (circleCost x y : ℝ≥0∞)/D := by
  have hd : 0 < (D:ℝ) := by exact_mod_cast (NeZero.pos D)
  rw [edist_dist,circleCost_dist,ENNReal.ofReal_div_of_pos hd]
  simp only [ENNReal.ofReal_natCast]

lemma natSupCast {α : Type*} (s : Finset α) (f : α → ℕ) :
    ((s.sup f : ℕ) : ℝ≥0∞) = s.sup (fun a => (f a : ℝ≥0∞)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sup_insert,Finset.sup_insert,← ih]
    by_cases h : f a ≤ s.sup f
    · have hc : (f a : ℝ≥0∞) ≤ ((s.sup f : ℕ) : ℝ≥0∞) := by exact_mod_cast h
      simp only [max_eq_right h,max_eq_right hc]
    · have h' := le_of_lt (lt_of_not_ge h)
      have hc : ((s.sup f : ℕ) : ℝ≥0∞) ≤ (f a : ℝ≥0∞) := by exact_mod_cast h'
      simp only [max_eq_left h',max_eq_left hc]

def copyCost {Q : Type*} [DecidableEq Q] {M : Q → Type*} [∀ q, Fintype (M q)]
    {D : ℕ} (x y : GridLocation M D) : ℕ∞ :=
  if h : x.1 = y.1 then
    (Finset.univ.sup (fun k : M x.1 => circleCost (x.2 k) (y.2 (h ▸ k))) : ℕ)
  else ⊤

lemma copyCost_exact {Q : Type*} [DecidableEq Q] {M : Q → Type*} [∀ q, Fintype (M q)]
    {D : ℕ} [NeZero D] (x y : GridLocation M D) :
    (copyCost x y : ℝ≥0∞)/(D:ℝ≥0∞) = copyLength x y := by
  unfold copyCost copyLength
  split_ifs with h
  · simp only [ENat.toENNReal_coe,natSupCast,Finset.sup_eq_iSup,Finset.mem_univ,
      iSup_pos,ENNReal.iSup_div,circleCost_edist]
  · exact ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top D)

lemma forwardZero_iff {Q : Type*} {M : Q → Type*} (S : ProjectionSystem Q M)
    {D : ℕ} (x y : GridLocation M D) :
    S.ForwardZero D x y ↔ ∃ π : M x.1 → M y.1, S.imposed x.1 y.1 π ∧ x.2 = y.2 ∘ π := by
  constructor
  · intro h
    cases h with
    | link q q' π h v => exact ⟨π,h,rfl⟩
  · rintro ⟨π,hπ,h⟩
    rcases x with ⟨q,x⟩
    rcases y with ⟨q',y⟩
    dsimp at *
    rw [h]
    exact .link q q' π hπ y

instance forwardZero_decidable {Q : Type*} {M : Q → Type*}
    [∀ q, Fintype (M q)] [∀ q, DecidableEq (M q)]
    (S : ProjectionSystem Q M) [∀ q q' π, Decidable (S.imposed q q' π)]
    {D : ℕ} [NeZero D] (x y : GridLocation M D) : Decidable (S.ForwardZero D x y) :=
  decidable_of_iff _ (forwardZero_iff S x y).symm

instance zeroLink_decidable {Q : Type*} {M : Q → Type*}
    [∀ q, Fintype (M q)] [∀ q, DecidableEq (M q)]
    (S : ProjectionSystem Q M) [∀ q q' π, Decidable (S.imposed q q' π)]
    {D : ℕ} [NeZero D] (x y : GridLocation M D) : Decidable (S.ZeroLink D x y) :=
  inferInstanceAs (Decidable (S.ForwardZero D x y ∨ S.ForwardZero D y x))

def linkCost {Q : Type*} [DecidableEq Q] {M : Q → Type*}
    [∀ q, Fintype (M q)] [∀ q, DecidableEq (M q)]
    (S : ProjectionSystem Q M) [∀ q q' π, Decidable (S.imposed q q' π)]
    {D : ℕ} [NeZero D] (x y : GridLocation M D) : ℕ∞ :=
  if S.ZeroLink D x y then 0 else copyCost x y

lemma linkCost_exact {Q : Type*} [DecidableEq Q] {M : Q → Type*}
    [∀ q, Fintype (M q)] [∀ q, DecidableEq (M q)]
    (S : ProjectionSystem Q M) [∀ q q' π, Decidable (S.imposed q q' π)]
    {D : ℕ} [NeZero D] (x y : GridLocation M D) :
    (linkCost S x y : ℝ≥0∞)/(D:ℝ≥0∞) = S.linkLength x y := by
  unfold linkCost ProjectionSystem.linkLength
  split_ifs
  · simp
  · exact copyCost_exact x y

lemma scaled_min (d : ℝ≥0∞) (a b : ℕ∞) :
    ((min a b : ℕ∞) : ℝ≥0∞)/d = min ((a:ℝ≥0∞)/d) ((b:ℝ≥0∞)/d) := by
  rcases le_total a b with h | h
  · have hh := ENNReal.div_le_div_right (ENat.toENNReal_le.mpr h) d
    simp only [min_eq_left h,min_eq_left hh]
  · have hh := ENNReal.div_le_div_right (ENat.toENNReal_le.mpr h) d
    simp only [min_eq_right h,min_eq_right hh]

lemma Matrix.scaled_allPairs_exact {n : ℕ} (a : Matrix n) (D : ℕ) (i j : Fin n) :
    (a.allPairs.get i j : ℝ≥0∞)/(D:ℝ≥0∞) =
      pathDistance (fun x y => (a.get x y : ℝ≥0∞)/(D:ℝ≥0∞)) i j := by
  rw [Matrix.allPairs,Matrix.run_get]
  have hm := congrFun (congrFun (closure_map (fun z : ℕ∞ => (z:ℝ≥0∞)/(D:ℝ≥0∞))
    (scaled_min _) (fun a b => by rw [ENat.toENNReal_add,ENNReal.add_div])
    a.get (List.finRange n)) i) j
  rw [hm]
  exact closure_eq_distance _ _ (fun z => List.mem_finRange z) i j

lemma walkLength_reindex {X Y : Type*} (e : X → Y) (w : Y → Y → ℝ≥0∞) (x : X)
    (zs : List X) (y : X) :
    walkLength (fun x y => w (e x) (e y)) x zs y = walkLength w (e x) (zs.map e) (e y) := by
  induction zs generalizing x with
  | nil => rfl
  | cons z zs ih => simp only [walkLength,List.map_cons,ih]

end ShortestPaths
end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_GeometryNaming
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace LargeIndependentSets.ShortestPaths

open scoped ENNReal

lemma pathDistance_surjective {X Y : Type*} (e : X → Y) (he : Function.Surjective e)
    (w : Y → Y → ℝ≥0∞) (x y : X) :
    pathDistance (fun a b => w (e a) (e b)) x y = pathDistance w (e x) (e y) := by
  unfold pathDistance
  apply le_antisymm
  · apply le_iInf
    intro zs
    obtain ⟨ws,hws⟩ := List.map_surjective_iff.mpr he zs
    apply iInf_le_of_le ws
    rw [walkLength_reindex,hws]
  · apply le_iInf
    intro zs
    rw [walkLength_reindex]
    exact iInf_le_of_le (zs.map e) le_rfl

theorem cover_allPairs_exact {Q : Type*} [DecidableEq Q] {M : Q → Type*}
    [∀ q, Fintype (M q)] [∀ q, DecidableEq (M q)]
    (S : ProjectionSystem Q M) [∀ q q' π, Decidable (S.imposed q q' π)]
    {D : ℕ} [NeZero D] {n : ℕ} (e : Fin n → GridLocation M D)
    (he : Function.Surjective e) (i j : Fin n) :
    let a : Matrix n := Vector.ofFn (fun x => Vector.ofFn (fun y => linkCost S (e x) (e y)))
    (a.allPairs.get i j : ℝ≥0∞)/(D : ℝ≥0∞) = pathDistance S.linkLength (e i) (e j) := by
  dsimp only
  rw [Matrix.scaled_allPairs_exact]
  have hh : (fun x y : Fin n =>
      ((Matrix.get (Vector.ofFn (fun x => Vector.ofFn (fun y => linkCost S (e x) (e y)))) x y : ℝ≥0∞) /
        (D : ℝ≥0∞))) = (fun x y => S.linkLength (e x) (e y)) := by
    funext x y
    simpa only [Matrix.get,Vector.getElem_ofFn] using linkCost_exact S (e x) (e y)
  rw [hh,pathDistance_surjective e he]

end LargeIndependentSets.ShortestPaths

namespace LargeIndependentSets.GeometryNames

section
open scoped ENNReal Classical BigOperators

def mixed {U V : Type*} {n : ℕ} (u : Fin n → U) (v : Fin n → V) (i : ℕ) :
    MixedTuple U V n i :=
  ⟨fun k => if k.val < i then Sum.inl (v k) else Sum.inr (u k),by
    intro k; by_cases hk : k.val < i <;> simp [hk]⟩

@[simp] lemma mixed_val {U V : Type*} {n : ℕ} (u : Fin n → U) (v : Fin n → V)
    (i : ℕ) (k : Fin n) : (mixed u v i).val k =
      if k.val < i then Sum.inl (v k) else Sum.inr (u k) := rfl

lemma mixed_surjective {U V : Type*} [Nonempty U] [Nonempty V] {n i : ℕ}
    (q : MixedTuple U V n i) : ∃ u v, mixed u v i=q := by
  let u : Fin n → U := fun k => (q.val k).elim (fun _ => Classical.choice inferInstance) id
  let v : Fin n → V := fun k => (q.val k).elim id (fun _ => Classical.choice inferInstance)
  refine ⟨u,v,Subtype.ext ?_⟩
  funext k
  have h := q.property k
  cases he : q.val k with
  | inl a =>
    have hk : k.val < i := by simpa [he] using h.symm
    simp [mixed,u,v,he,hk]
  | inr a =>
    have hk : ¬k.val < i := by simpa [he] using h.symm
    simp [mixed,u,v,he,hk]

abbrev StaticPoint (L R : Type) (n D : ℕ) :=
  Σ i : Fin (n+1), MixedTuple L R n i.val → ZMod D

def decode {U V L R : Type} {n D : ℕ}
    (u : Fin n → U) (v : Fin n → V) (a : StaticPoint L R n D) :
    GridLocation (LayerAnswer L R (U:=U) (V:=V) (n:=n)) D :=
  ⟨⟨a.1,mixed u v a.1.val⟩,a.2⟩

lemma decode_surjective {U V L R : Type} [Nonempty U] [Nonempty V] {n D : ℕ}
    (x : GridLocation (LayerAnswer L R (U:=U) (V:=V) (n:=n)) D) :
    ∃ u v a, decode u v a=x := by
  rcases x with ⟨⟨i,q⟩,x⟩
  obtain ⟨u,v,h⟩ := mixed_surjective q
  refine ⟨u,v,⟨i,x⟩,?_⟩
  cases h
  rfl

abbrev Node (L R : Type) (n D nu nv : ℕ) :=
  ((Fin n → Fin nu) × (Fin n → Fin nv)) × StaticPoint L R n D

def nodeDecode {L R : Type} {n D nu nv : ℕ} (x : Node L R n D nu nv) :=
  decode x.1.1 x.1.2 x.2

lemma nodeDecode_surjective {L R : Type} {n D nu nv : ℕ} (hu : 0<nu) (hv : 0<nv) :
    Function.Surjective (@nodeDecode L R n D nu nv) := by
  let : Nonempty (Fin nu) := ⟨⟨0,hu⟩⟩
  let : Nonempty (Fin nv) := ⟨⟨0,hv⟩⟩
  intro x
  obtain ⟨u,v,a,h⟩ := decode_surjective x
  exact ⟨((u,v),a),h⟩

def nodeEquiv (L R : Type) [Fintype L] [Fintype R] (n D nu nv : ℕ) [NeZero D] :
    Node L R n D nu nv ≃ Fin ((nu^n*nv^n)*Fintype.card (StaticPoint L R n D)) :=
  (Equiv.prodCongr ((Equiv.prodCongr finFunctionFinEquiv finFunctionFinEquiv).trans
    finProdFinEquiv) (Fintype.equivFin (StaticPoint L R n D))).trans finProdFinEquiv

def names (L R : Type) [Fintype L] [Fintype R] (n D nu nv : ℕ) [NeZero D] :=
  fun i => nodeDecode ((nodeEquiv L R n D nu nv).symm i)

lemma names_surjective (L R : Type) [Fintype L] [Fintype R] (n D nu nv : ℕ) [NeZero D]
    (hu : 0<nu) (hv : 0<nv) : Function.Surjective (names L R n D nu nv) :=
  (nodeDecode_surjective hu hv).comp (nodeEquiv L R n D nu nv).symm.surjective

end

open scoped Classical

def QuestionStep {U V L R C : Type} {n : ℕ} (lc : LabelCoverData U V L R C)
    (h : Fin n) (c : C) (u u' : Fin n → U) (v v' : Fin n → V) : Prop :=
  u h=lc.left c ∧ v' h=lc.right c ∧
    ∀ k, k≠h → if k.val<h.val then v k=v' k else u k=u' k

lemma questionStep_iff {U V L R C : Type} {n : ℕ} (lc : LabelCoverData U V L R C)
    (h : Fin n) (c : C) (u u' : Fin n → U) (v v' : Fin n → V) :
    QuestionStep lc h c u u' v v' ↔
      (mixed u v h.val).val h=Sum.inr (lc.left c) ∧
      (mixed u' v' (h.val+1)).val h=Sum.inl (lc.right c) ∧
      ∀ k, k≠h → (mixed u v h.val).val k=(mixed u' v' (h.val+1)).val k := by
  simp only [QuestionStep,mixed_val,lt_self_iff_false,ite_false,Sum.inr.injEq,
    Nat.lt_succ_self,ite_true,Sum.inl.injEq]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply forall_congr'
  intro k
  by_cases hk : k=h
  · simp [hk]
  · have hne : k.val≠h.val := fun e => hk (Fin.ext e)
    by_cases hl : k.val<h.val
    · simp [hk,hl,show k.val<h.val+1 by omega]
    · simp [hk,hl,show ¬k.val<h.val+1 by omega]

end LargeIndependentSets.GeometryNames

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Encoding_GeometryExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.GeometryNames
open scoped Classical BigOperators
noncomputable section

variable (L R : Type) [Fintype L] [Fintype R] (n D : ℕ) [NeZero D]

abbrev staticCount := Fintype.card (StaticPoint L R n D)

lemma staticCount_pos : 0 < staticCount L R n D := by
  let : Nonempty (StaticPoint L R n D) := ⟨⟨⟨0,by omega⟩,fun _ => 0⟩⟩
  exact Fintype.card_pos

def sameQuestion {U V : Type} (u u' : Fin n → U) (v v' : Fin n → V)
    (a b : StaticPoint L R n D) : Prop :=
  a.1=b.1 ∧ ∀ k, if k.val<a.1.val then v k=v' k else u k=u' k

omit [Fintype L] [Fintype R] [NeZero D] in
lemma sameQuestion_iff {U V : Type} (u u' : Fin n → U) (v v' : Fin n → V)
    (a b : StaticPoint L R n D) :
    sameQuestion L R n D u u' v v' a b ↔ (decode u v a).1=(decode u' v' b).1 := by
  rcases a with ⟨i,a⟩
  rcases b with ⟨j,b⟩
  simp only [sameQuestion,decode]
  constructor
  · rintro ⟨rfl,h⟩
    congr 1
    apply Subtype.ext
    funext k
    have hk := h k
    by_cases hl : k.val < i.val <;> simpa [mixed_val,hl] using hk
  · intro h
    have hij : i=j := congrArg Sigma.fst h
    subst j
    refine ⟨rfl,?_⟩
    have hq : mixed u v i.val=mixed u' v' i.val := Sigma.mk.inj_iff.mp h |>.2 |> eq_of_heq
    intro k
    have hh := congrFun (congrArg Subtype.val hq) k
    by_cases hl : k.val < i.val <;> simpa [mixed_val,hl] using hh

end
end LargeIndependentSets.GeometryNames

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Encoding_GraphPrinter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.GraphPrinter
open scoped Classical
noncomputable section

lemma matrix_eq (G : Graph) :
    (List.finRange G.vertices).flatMap (fun i => (List.finRange G.vertices).map (G.adj i)) =
      List.ofFn (fun i : Fin (G.vertices*G.vertices) => G.adj i.divNat i.modNat) := by
  rw [List.ofFn_mul]
  simp only [List.ofFn_eq_map,List.flatMap_def]
  congr 1
  apply List.map_congr_left
  intro i _
  apply List.map_congr_left
  intro j _
  congr 1
  · apply Fin.ext
    simp only [Fin.divNat]
    rw [Nat.add_comm (i.val * G.vertices),Nat.add_mul_div_right _ _ G.nonempty,Nat.div_eq_of_lt j.isLt,Nat.zero_add]
  · apply Fin.ext
    simp [Fin.modNat,Nat.mod_eq_of_lt j.isLt]

end
end LargeIndependentSets.GraphPrinter

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_PoweringTableLayout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PoweringTableLayout

theorem vector_toList_ofFn {α : Type*} {m : Nat} (rows : Vector α m) :
    rows.toList = List.ofFn (fun i : Fin m => rows[i]) := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp

theorem vector_blocks {α : Type*} {m vertices width : Nat}
    (sameCount : m = vertices * width) (rows : Vector α m) :
    rows.toList = (List.finRange vertices).flatMap (fun v =>
      List.ofFn (fun j : Fin width =>
        rows[Fin.cast sameCount.symm (finProdFinEquiv (v, j))])) := by
  have atIndex (v : Fin vertices) (j : Fin width)
      (h : v.val * width + j.val < vertices * width) :
      (⟨v.val * width + j.val, h⟩ : Fin (vertices * width)) =
        finProdFinEquiv (v, j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.add_comm, Nat.mul_comm]
  rw [vector_toList_ofFn rows,
    List.ofFn_congr sameCount (fun i : Fin m => rows[i]), List.ofFn_mul]
  simp only [atIndex, List.finRange, List.flatMap_def, List.map_ofFn]
  rfl

end IndependentSetsGames.Foundations.PCP.PoweringTableLayout

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_FloydLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.FloydCarry
open ShortestPaths
open Turing
open scoped BigOperators

noncomputable def lengthPolynomial (B : ℕ) : Polynomial ℕ :=
  (3+Polynomial.X*Polynomial.X+Polynomial.X)*(2*Polynomial.X+Polynomial.C (B+2))

lemma lengthPolynomial_eval (B N : ℕ) :
    (lengthPolynomial B).eval N=(3+N*N+N)*(2*N+B+2) := by
  simp [lengthPolynomial,Nat.add_assoc]

end LargeIndependentSets.FloydCarry

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_IntegerEdgeTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.ShortestPaths
open scoped ENNReal

lemma integer_edge_test {D : ℕ} [NeZero D] (c : ℕ∞) :
    (c:ℝ≥0∞)/(D:ℝ≥0∞) ≤ ENNReal.ofReal (1/8) ↔ 8*c ≤ (D:ℕ∞) := by
  induction c using ENat.recTopCoe with
  | top => simp [ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top D)]
  | coe c =>
    have hd : 0 < (D:ℝ) := by exact_mod_cast (NeZero.pos D)
    have hD : (D:ℝ≥0∞) ≠ 0 := by exact_mod_cast (NeZero.ne D)
    rw [← ENNReal.toReal_le_toReal (ENNReal.div_ne_top (by simp) hD) (by simp)]
    simp only [ENat.toENNReal_coe,ENNReal.toReal_div,ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/8)]
    rw [div_le_iff₀ hd]
    have hr : (c:ℝ) ≤ 1/8*(D:ℝ) ↔ 8*(c:ℝ) ≤ (D:ℝ) := by constructor <;> intro h <;> linarith
    rw [hr]
    have he : (8:ℕ∞)*(c:ℕ∞) = ((8*c:ℕ):ℕ∞) := by norm_cast
    rw [he,ENat.natCast_le_natCast]
    exact_mod_cast Iff.rfl

end LargeIndependentSets.ShortestPaths

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_GeometryDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.GeometryNames
open ShortestPaths
open Turing
open scoped Classical BigOperators ENNReal
noncomputable section

variable (L R : Type) [Fintype L] [Fintype R] (n D : ℕ) [NeZero D]

omit [NeZero D] in
lemma enat_eighth (c : ℕ∞) : 8*c≤(D:ℕ∞) ↔ c≤((D/8:ℕ):ℕ∞) := by
  induction c using ENat.recTopCoe with
  | top => simp
  | coe c =>
    have hh : (8:ℕ∞)*(c:ℕ∞)=((8*c:ℕ):ℕ∞) := by norm_cast
    rw [hh,ENat.natCast_le_natCast,ENat.natCast_le_natCast]
    omega

end
end LargeIndependentSets.GeometryNames

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_GeometryPointTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.GeometryNames
open scoped Classical
noncomputable section
variable (L R : Type) [Fintype L] [Fintype R] (n D : ℕ) [NeZero D]

def pointEquiv : StaticPoint L R n D ≃ Fin (staticCount L R n D) :=
  Fintype.equivFin (StaticPoint L R n D)

lemma nodeEquiv_val {nu nv : ℕ} (x : Node L R n D nu nv) :
    (nodeEquiv L R n D nu nv x).val=
      (pointEquiv L R n D x.2).val+staticCount L R n D*
        ((finFunctionFinEquiv x.1.2).val+nv^n*(finFunctionFinEquiv x.1.1).val) := rfl

end
end LargeIndependentSets.GeometryNames

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_GeometryAntipodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.GeometryNames
open ShortestPaths
open scoped Classical BigOperators ENNReal
noncomputable section

variable (L R : Type) [Fintype L] [Fintype R] (n D : ℕ) [NeZero D]

def antiPoint (s : StaticPoint L R n D) : StaticPoint L R n D :=
  ⟨s.1,fun k => s.2 k + ((D/2:ℕ):ZMod D)⟩

end
end LargeIndependentSets.GeometryNames

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_Witness
attribute [-instance] _root_.OAI.LargeIndependentSets.mixedTupleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets

instance (priority := 1100) mixedTupleComputableFintype {A B : Type*} [Fintype A] [Fintype B]
    (n i : ℕ) : Fintype (MixedTuple A B n i) :=
  inferInstanceAs (Fintype {x : Fin n → B ⊕ A // ∀ h, (x h).isLeft = decide (h.val < i)})

instance mixedTupleDecidableEq {A B : Type*} [DecidableEq A] [DecidableEq B]
    (n i : ℕ) : DecidableEq (MixedTuple A B n i) :=
  inferInstanceAs (DecidableEq {x : Fin n → B ⊕ A // ∀ h, (x h).isLeft = decide (h.val < i)})

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_GeometryLocations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.GeometryNames
open PhaseTest Coefficient
open scoped Classical BigOperators
noncomputable section
attribute [-instance] mixedTupleComputableFintype mixedTupleDecidableEq

variable (L R : Type) [Fintype L] [Fintype R] (p : SamplerParameters)

def scheduleLC (f : Fin p.n → L → R) : LabelCoverData Unit Unit L R (Fin p.n) :=
  ⟨fun _ => (),fun _ => (),f⟩

attribute [instance 1100] mixedTupleComputableFintype
attribute [instance] mixedTupleDecidableEq
end
end LargeIndependentSets.GeometryNames

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_ThresholdDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets

namespace Graph

def ofEnumeration {W : Type} (H : SimpleGraph W) [DecidableRel H.Adj] {n : ℕ}
    (hn : 0<n) (e : Fin n ≃ W) : Graph where
  vertices := n
  nonempty := hn
  adj i j := decide (H.Adj (e i) (e j))
  symm i j := by simp only [decide_eq_decide]; exact H.adj_comm _ _
  loopless i := by simp

end Graph
end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_Mixed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.Graph

structure Renaming (G H : Graph) where
  equiv : Fin G.vertices ≃ Fin H.vertices
  adj_eq : ∀ i j, G.adj i j = H.adj (equiv i) (equiv j)

namespace Renaming
variable {G H : Graph}

def symm (e : Renaming G H) : Renaming H G where
  equiv := e.equiv.symm
  adj_eq i j := by simpa using (e.adj_eq (e.equiv.symm i) (e.equiv.symm j)).symm

end Renaming
end LargeIndependentSets.Graph

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_EnumerationSimple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets

section
open scoped Classical

namespace Graph
noncomputable def enumeration_to_simple {W : Type} [Fintype W] [Nonempty W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {n : ℕ} (hn : 0<n) (e : Fin n ≃ W) :
    Renaming (ofEnumeration H hn e) (ofSimple H) where
  equiv := e.trans (Fintype.equivFin W)
  adj_eq i j := by
    simp only [ofEnumeration,ofSimple,decide_eq_decide]
    change H.Adj (e i) (e j) ↔
      H.Adj ((Fintype.equivFin W).symm ((Fintype.equivFin W) (e i)))
        ((Fintype.equivFin W).symm ((Fintype.equivFin W) (e j)))
    simp

end Graph

attribute [-instance] mixedTupleComputableFintype mixedTupleDecidableEq

attribute [instance 1100] mixedTupleComputableFintype
attribute [instance] mixedTupleDecidableEq
end

namespace SamplerParameters
open scoped BigOperators
attribute [-instance] mixedTupleComputableFintype mixedTupleDecidableEq

attribute [instance] mixedTupleDecidableEq
attribute [instance 1100] mixedTupleComputableFintype

open scoped Classical
attribute [-instance] mixedTupleDecidableEq mixedTupleComputableFintype
attribute [instance 1100] mixedTupleComputableFintype
attribute [instance] mixedTupleDecidableEq

end SamplerParameters
end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_GeometryOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.GeometryNames
open ShortestPaths
open Turing
open scoped Classical BigOperators ENNReal
noncomputable section
attribute [-instance] mixedTupleComputableFintype mixedTupleDecidableEq

variable (L R : Type) [Fintype L] [Fintype R] (p : SamplerParameters) (q : ℕ) (hq : 0<q)

lemma equal_adj {G H : Graph} (h : G=H) (i j : Fin G.vertices) :
    G.adj i j=H.adj (Fin.cast (congrArg Graph.vertices h) i) (Fin.cast (congrArg Graph.vertices h) j) := by
  subst H
  rfl

lemma clique_adj {G : Graph} (h : G=Graph.clique q hq) (i j : Fin G.vertices) :
    G.adj i j=decide (i≠j) := by
  subst G
  rfl

attribute [instance 1100] mixedTupleComputableFintype
attribute [instance] mixedTupleDecidableEq
end
end LargeIndependentSets.GeometryNames

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_IndexedBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.IndexedBlocks

lemma range_blocks {α : Type*} (f : ℕ → ℕ → α) (k : ℕ) (hk : 0<k) (n : ℕ) :
    (List.range (k*n)).map (fun i => f (i/k) (i%k)) =
      (List.range n).flatMap (fun j => (List.range k).map (f j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ,List.range_add,List.map_append,ih,List.range_succ,List.flatMap_append]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_map]
    congr 1
    apply List.map_congr_left
    intro j hj
    have hj' := List.mem_range.mp hj
    have hd : (k*n+j)/k=n := by
      rw [Nat.add_comm,Nat.add_mul_div_left _ _ hk,Nat.div_eq_of_lt hj',Nat.zero_add]
    simp [hd,Nat.mod_eq_of_lt hj']

end LargeIndependentSets.IndexedBlocks

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_PCPGapMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BinaryNormalize
open BinarySyntax BinaryNames
open IndependentSetsGames.Foundations
open scoped BigOperators

def eventCode : Option Mark → ℕ
  | none => 0
  | some .empty => 1
  | some (.first r) => 2+r.val

def sourcePosition (s : List Bool) (p r j : ℕ) : ℕ :=
  if j=1 ∧ 1 ≤ r then next s p else
    if j=2 ∧ 2 ≤ r then next s (next s p) else p

def blockValue (s : List Bool) (p i : ℕ) : ℕ :=
  let tag := eventCode (eventAt s p)
  let slot := (i/2)%3
  if 2 ≤ tag ∧ i<6 then
    let pos := sourcePosition s p (tag-2) slot
    if i%2=0 then key s pos else if raw s pos then 1 else 0
  else if i%2=0 then 0
  else if tag=1 then (if 6 ≤ i then 1 else 0)
  else if slot=1 then 0 else 1

def tableCount (s : List Bool) : ℕ := 2+12*s.length

def tableValue (s : List Bool) (w : ℕ) : ℕ :=
  if w=0 then s.length+1 else if w=1 then 2*s.length
  else blockValue s ((w-2)/12) ((w-2)%12)

end LargeIndependentSets.BinaryNormalize

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_TargetLC
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace LargeIndependentSets.LabelCoverData
open scoped Classical
variable {U V L R C U' V' C' : Type}

def reindex (lc : LabelCoverData U V L R C) (eu : U ≃ U') (ev : V ≃ V') (ec : C ≃ C') :
    LabelCoverData U' V' L R C' where
  left c := eu (lc.left (ec.symm c))
  right c := ev (lc.right (ec.symm c))
  project c := lc.project (ec.symm c)

end LargeIndependentSets.LabelCoverData

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_MapEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open IndependentSetsGames.Foundations
open PCP

namespace NamedReduction
attribute [-instance] mixedTupleComputableFintype mixedTupleDecidableEq

attribute [instance 1100] mixedTupleComputableFintype
attribute [instance] mixedTupleDecidableEq

instance cubeDecidableEq : (k : ℕ) → DecidableEq (BooleanJunta.Cube k)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | k+1 => by
    letI := cubeDecidableEq k
    exact inferInstanceAs (DecidableEq (Bool × BooleanJunta.Cube k))

attribute [-instance] mixedTupleComputableFintype mixedTupleDecidableEq
attribute [instance 1100] mixedTupleComputableFintype
attribute [instance] mixedTupleDecidableEq

end NamedReduction
end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_TargetRead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace LargeIndependentSets.TargetRead
open IndependentSetsGames.Foundations
open PCP
open scoped Classical BigOperators

lemma block_get {α β : Type} (d : β) (f : α → List β) (k : ℕ) (hl : ∀ x, (f x).length=k)
    (xs : List α) (c : Fin xs.length) (j : ℕ) (hj : j<k) :
    ((xs.flatMap f)[k*c.val+j]?).getD d=((f xs[c])[j]?).getD d := by
  induction xs with
  | nil => exact Fin.elim0 c
  | cons x xs ih =>
    rcases c with ⟨c,hc⟩
    cases c with
    | zero =>
      simp only [List.flatMap_cons,Nat.mul_zero,Nat.zero_add]
      rw [List.getElem?_append_left (by simpa [hl] using hj)]
      rfl
    | succ c =>
      have hc' : c<xs.length := by simpa using hc
      simp only [List.flatMap_cons,Nat.mul_succ]
      rw [List.getElem?_append_right (by rw [hl]; omega),hl]
      have he : k*c+k+j-k=k*c+j := by omega
      rw [he]
      exact ih ⟨c,hc'⟩

end LargeIndependentSets.TargetRead
namespace LargeIndependentSets.TargetRepair
open IndependentSetsGames.Foundations
open PCP
open TargetRead
open scoped Classical BigOperators

def bit (b : Bool) : ℕ := if b then 1 else 0
@[simp] lemma bit_eq (b c : Bool) : bit b=bit c ↔ b=c := by cases b <;> cases c <;> decide
lemma bit_decide (p : Prop) [Decidable p] : bit (decide p)=(if p then 1 else 0) := by
  by_cases h : p <;> simp [bit,h]
@[simp] lemma bit_ne_zero (b : Bool) : bit b≠0 ↔ b=true := by cases b <;> decide

lemma indicator_ne (p : Prop) [Decidable p] : (if p then (1:ℕ) else 0)≠0 ↔ p := by
  by_cases h : p <;> simp [h]

end LargeIndependentSets.TargetRepair

end

end OAI
end


