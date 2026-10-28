-- Prove2me | Definitions.Def_OAIQ086U002
-- name    : OAIQ086U002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T16:05:30.916237+00:00
-- url     : https://prove2.me/theorems/e554c8aa-550c-4cbb-9dd9-e995b7531242
-- title:
--   Definitions bundle OAIQ086U002 of the split of OpenAI, The Unique Games Theorem
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniqueGamesTheorem.theorem11`, carved from OpenAI's openai/math development (OpenAI, *The Unique Games Theorem*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1058 declarations of OpenAI's Lean: 548 definitions, 24 inductive types or structures, 30 instances and 456 theorems. The definitions and types are `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularMetadata.overhead`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularMetadata.querySteps`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalClean.Alphabet`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalClean.Tape`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalClean.cleanupSteps`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalClean.cleanupTapes`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalClean.timeBound`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalRow.Alphabet`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalRow.Tape`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalRow.fields`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalRow.lookupTape`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalRow.timeBound`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.sumDecidableEq`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Fuel.guard`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Fuel.increment`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.CopyPhase`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.CopyPhase.enumList`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.Extra`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.Extra.enumList`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.Field`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.Field.enumList`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.CopyPhase`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.CopyPhase.enumList`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.counterStacks`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.sumDecidableEq`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularVertexBlock.portBits`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularVertexBlock.rowSizeBound`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRepeat.loopBudget`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRepeat.oneStep`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryEqualityBit.Alphabet`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryEqualityBit.Label`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryEqualityBit.Label.enumList`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryEqualityBit.State`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryEqualityBit.clean`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryEqualityBit.compareSteps`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryEqualityBit.copySteps`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryEqualityBit.emit`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryEqualityBit.exitAt`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryEqualityBit.steps`, `OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalEnumeration.sharedTapeEquiv` and 532 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `UniqueGames_Analysis_MatrixEnergy`, `UniqueGames_Analysis_ParityLemmas`, `UniqueGames_Foundations_Basic`, `UniqueGames_Foundations_KernelSampling`, `UniqueGames_Foundations_LabelBound`, `UniqueGames_Foundations_PinskerLemmas`, `UniqueGames_Foundations_Rectangle`, `UniqueGames_Foundations_SamplingLemmas`, `UniqueGames_Foundations_SharedProfiles`, `UniqueGames_Gadgets_ActualGadgetLemmas`, `UniqueGames_Gadgets_AdaptivePathsLemmas`, `UniqueGames_Gadgets_BaseConstruction`, `UniqueGames_Gadgets_BlockDescentLemmas`, `UniqueGames_Gadgets_ConcatenationLemmas`, `UniqueGames_Gadgets_NonlinearRecurrenceLemmas`, `UniqueGames_Gadgets_OrientedBlockKernel`, `UniqueGames_Gadgets_QuadraticStageNoise`, `UniqueGames_Gadgets_QuotientLemmas`, `UniqueGames_Games_CompletedSamplingLemmas`, `UniqueGames_Games_FactorizationLemmas`, `UniqueGames_Games_MaskedVariation`, `UniqueGames_Games_Overlap`, `UniqueGames_Games_PartialRevealLemmas`, `UniqueGames_Games_SelectedCommonMarginalLemmas`, `UniqueGames_Games_SelectedInformationLemmas`, `UniqueGames_Games_SelectionSequence`, `UniqueGames_Games_Variation`, `UniqueGames_Inverse_EqualityFiber`, `UniqueGames_Inverse_KMSAffineRestrictionComplementLemmas`, `UniqueGames_Inverse_KMSAffineRestrictionPresentationLemmas`, `UniqueGames_Inverse_KMSAnalyticHybridCoordinatesRankLemmas`, `UniqueGames_Inverse_KMSAnalyticHybridEnergyImageTransportLemmas`, `UniqueGames_Inverse_KMSAnalyticHybridEnergyLemmas`, `UniqueGames_Inverse_KMSBasisComparisonLemmas`, `UniqueGames_Inverse_KMSFoundationLemmas`, `UniqueGames_Inverse_KMSFourthMomentMixedScalarLemmas`, `UniqueGames_Inverse_KMSKernelOrbitsFourierLemmas`, `UniqueGames_Inverse_KMSLowLevelLemmas`, `UniqueGames_Inverse_MatrixChartIntervalsLemmas`, `UniqueGames_Inverse_MatrixChartLemmas`, `UniqueGames_Inverse_RowErasureLemmas`, `UniqueGames_Inverse_RowErasureMatrixLemmas`, `UniqueGames_Inverse_ShortcodeFromGrassmannLemmas`, `UniqueGames_Machines_MachineRegularMetadata`, `UniqueGames_Machines_MachineRegularOriginalBody`, `UniqueGames_Machines_MachineRegularOriginalClean`, `UniqueGames_Machines_MachineRegularOriginalRow`, `UniqueGames_Machines_MachineRegularOwnerBody`, `UniqueGames_Machines_MachineRegularOwnerCleanup`, `UniqueGames_Machines_MachineRegularTable`, `UniqueGames_Machines_MachineRegularTableTrace`, `UniqueGames_Machines_MachineRegularVertexBlock`, `UniqueGames_Machines_MachineRepeat`, `UniqueGames_Machines_MachineUnaryEqualityBit`, `UniqueGames_Machines_PoweringGlobalEnumerationLemmas`, `UniqueGames_Machines_PoweringMachineEqualityField`, `UniqueGames_Machines_PoweringMachineFinish`, `UniqueGames_Machines_PoweringMachineInitialize`, `UniqueGames_Machines_PoweringMachineLoop`, `UniqueGames_Machines_PoweringMachineRelationLemmas`, `UniqueGames_Machines_PoweringMachineRowBody`, `UniqueGames_Machines_PoweringPlanBudget`, `UniqueGames_PCP_Addresses`, `UniqueGames_PCP_AlphabetGraphLemmas`, `UniqueGames_PCP_AlphabetReductionLemmas`, `UniqueGames_PCP_AlphabetRetractionLemmas`, `UniqueGames_PCP_AlphabetTableBoundsLemmas`, `UniqueGames_PCP_AmplificationIteration`, `UniqueGames_PCP_AssignmentTester`, `UniqueGames_PCP_CayleySampling`, `UniqueGames_PCP_CayleyTailCount`, `UniqueGames_PCP_CleanupLemmas`, `UniqueGames_PCP_Clone100`, `UniqueGames_PCP_CloudRoundingLemmas`, `UniqueGames_PCP_CodeComposition`, `UniqueGames_PCP_CompareLoop`, `UniqueGames_PCP_EmitRows`, `UniqueGames_PCP_ExpandersLemmas`, `UniqueGames_PCP_FinalBooleanVerifier`, `UniqueGames_PCP_FinalConstantsLemmas`, `UniqueGames_PCP_FoldedEquationLemmas`, `UniqueGames_PCP_HonestTestLemmas`, `UniqueGames_PCP_InitialGraphLemmas`, `UniqueGames_PCP_Initialization`, `UniqueGames_PCP_InputLemmas`, `UniqueGames_PCP_MachineRawInitialTable`, `UniqueGames_PCP_PortTableLookup`, `UniqueGames_PCP_PoweringLabelsLemmas`, `UniqueGames_PCP_PoweringPortReindexLemmas`, `UniqueGames_PCP_PoweringTableLayout`, `UniqueGames_PCP_PoweringTableSemanticsLemmas`, `UniqueGames_PCP_PoweringTablesLemmas`, `UniqueGames_PCP_PreprocessingPaddingOffsets`, `UniqueGames_PCP_PreprocessingRegularLoopWordsLemmas`, `UniqueGames_PCP_PreprocessingTablesLemmas`, `UniqueGames_PCP_RawInitialMachineBody`, `UniqueGames_PCP_RawInitialMachineCleanup`, `UniqueGames_PCP_RawInitialMachineFinish`, `UniqueGames_PCP_RawInitialMachineLoop`, `UniqueGames_PCP_RawInitialMachineReadClause`, `UniqueGames_PCP_RawInitialMachineRows`, `UniqueGames_PCP_RawInitialMachineStart`, `UniqueGames_PCP_RawInitialTablesLemmas`, `UniqueGames_PCP_RuntimeModel`, `UniqueGames_PCP_Setup`, `UniqueGames_PCP_SourceAddressArithmeticLemmas`, `UniqueGames_PCP_SourceContextClear`, `UniqueGames_PCP_SourceContextLoad`, `UniqueGames_PCP_SourceDescriptorEmissionLemmas`, `UniqueGames_PCP_SourceFieldArrayLemmas`, `UniqueGames_PCP_SourceGapLemmas`, `UniqueGames_PCP_SourceHeaderCounts`, `UniqueGames_PCP_SourceHonestLemmas`, `UniqueGames_PCP_SourceLoopInitLemmas`, `UniqueGames_PCP_SourceNoiseParameterLemmas`, `UniqueGames_PCP_SourceQueryLoopLemmas`, `UniqueGames_PCP_SourceSignaturePrepareLemmas`, `UniqueGames_PCP_SourceTupleBound`, `UniqueGames_PCP_VertexPadding`, `UniqueGames_PCP_ZigzagGraphsLemmas`, `UniqueGames_Quadratic_Alignment`, `UniqueGames_Quadratic_AlignmentCertificateLemmas`, `UniqueGames_Quadratic_Block`, `UniqueGames_Quadratic_BlockCounting`, `UniqueGames_Quadratic_BlockDimension`, `UniqueGames_Quadratic_BlockKernelLemmas`, `UniqueGames_Quadratic_BlockNoise`, `UniqueGames_Quadratic_BlockNoiseProbabilityLemmas`, `UniqueGames_Quadratic_BlockRestriction`, `UniqueGames_Quadratic_BlockSpanLemmas`, `UniqueGames_Quadratic_GenericFieldChoice`, `UniqueGames_Quadratic_GenericSeparationLemmas`, `UniqueGames_Quadratic_HarmonicLoss`, `UniqueGames_Quadratic_OrientedRestrictionLemmas`, `UniqueGames_Quadratic_TraceDual`, `UniqueGames_Quadratic_UniformSubspaces`, `UniqueGames_Reduction_ActualCanonicalLemmas`, `UniqueGames_Reduction_FinalParametersLemmas`, `UniqueGames_Reduction_IncidenceProbabilityLemmas`, `UniqueGames_Soundness_ConditionalReindex`, `UniqueGames_Soundness_PartnerLinearLemmas`, `UniqueGames_Soundness_SubsetIntersectionLemmas`, `UniqueGames_Soundness_ZeroInformationLemmas`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ086U003`, `OAIQ086U004` and `OAIQ086U005`.
-- source:
--   OpenAI, The Unique Games Theorem, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Unique-Games-Theorem-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Std

section
-- module Solutions.OAIQ086_UG.Compat
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
in d13f23b (Kadison similarity, oaiq-075). -/
noncomputable instance starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_ParityLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Actual splitting of linear-map questions and their uniform laws. -/

noncomputable section

open scoped BigOperators

namespace UniqueGamesTheorem.Fourier.SplitMaps

variable {K E C D : Type*} [CommSemiring K]
    [AddCommMonoid E] [Module K E]
    [AddCommMonoid C] [Module K C]
    [AddCommMonoid D] [Module K D]

/-- A question into the symbol/perpendicular product is exactly a pair of
independent coordinate questions. -/
def codomainSplit : (E →ₗ[K] C × D) ≃ₗ[K] (E →ₗ[K] C) × (E →ₗ[K] D) :=
  (LinearMap.prodEquiv K).symm

@[simp] theorem codomainSplit_symm_apply (X : E →ₗ[K] C) (Z : E →ₗ[K] D) :
    codomainSplit.symm (X, Z) = X.prod Z := rfl

end UniqueGamesTheorem.Fourier.SplitMaps

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_MatrixEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Fourier.MatrixEnergy

open scoped BigOperators

variable {Q : Type*} {I : Q → Type*} [Fintype Q] [∀ q, Fintype (I q)]

/-- Squared coefficient energy, averaged using the supplied question weights. -/
noncomputable def energy (weight : Q → ℝ) (a : (q : Q) → I q → ℝ) : ℝ :=
  ∑ q, weight q * ∑ i, a q i ^ 2

/-- Squared energy retained by a coordinate projection. -/
noncomputable def cutoffEnergy (weight : Q → ℝ) (keep : (q : Q) → I q → Prop)
    (a : (q : Q) → I q → ℝ) : ℝ := by
  classical
  exact ∑ q, weight q * ∑ i, if keep q i then a q i ^ 2 else 0

/-- Diagonal spectral quadratic form. -/
noncomputable def spectralEnergy (weight : Q → ℝ) (eigen a : (q : Q) → I q → ℝ) : ℝ :=
  ∑ q, weight q * ∑ i, eigen q i * a q i ^ 2

section LinearMaps

variable {E F : Type*}
variable [AddCommGroup E]
  [AddCommGroup F]

/-- Color indicator of one actual labeling. -/
noncomputable def colorIndicator {X Y : Type*} (label : X → Y) (y : Y) : X → ℝ := by
  classical
  exact fun x => if label x = y then 1 else 0

end LinearMaps

end UniqueGamesTheorem.Fourier.MatrixEnergy

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finite prerequisites for Holenstein's consistent sampling argument (Lemma 5.2).

`firstAccepted` is an actual bounded rejection sampler on a shared finite list
of proposals. `first_union_common` proves its synchronization property.
The remaining theorems establish the exact overlap/union mass formulas and the
agreement lower bound used to analyze a first accepted shared proposal.

No infinite random process or locally computable embedding is asserted here.
-/

namespace UniqueGamesTheorem.Foundations.CorrelatedSampling

noncomputable section FiniteWeights

variable {α : Type*} [Fintype α]

/-- Total variation for real-valued finite mass functions. Distribution
normalization is supplied explicitly in theorems that need it. -/
def totalVariation (p q : α → ℝ) : ℝ := (∑ a, |p a - q a|) / 2

def unionMass (p q : α → ℝ) : ℝ := ∑ a, max (p a) (q a)

theorem totalVariation_nonneg (p q : α → ℝ) : 0 ≤ totalVariation p q := by
  unfold totalVariation
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by norm_num)

theorem max_abs_identity (x y : ℝ) : 2 * max x y - |x - y| = x + y := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

/-- The union of two probability masses is exactly one plus their TV. -/
theorem unionMass_eq (p q : α → ℝ) (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) :
    unionMass p q = 1 + totalVariation p q := by
  have h := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun a _ => max_abs_identity (p a) (q a))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hp, hq] at h
  unfold unionMass totalVariation
  linarith

end FiniteWeights

end UniqueGamesTheorem.Foundations.CorrelatedSampling

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_KernelSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Exact sampling of two conditional kernels from one finite weighted shared seed.
The seed consists of independent full response tables and is independent of the
questions. Supported-coordinate repairs preserve the sampled laws and enforce
the designated coordinate even on seeds of weight zero. The seed is not claimed
to be uniform: the kernel weights may be arbitrary real numbers.
-/

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators
noncomputable section

namespace KernelSampling

/-- A single seed supplies a full local table to each side. -/
abbrev Seed (Q₁ Q₂ A B : Type*) := (Q₁ → A) × (Q₂ → B)

def readLeft {Q₁ Q₂ A B : Type*} (seed : Seed Q₁ Q₂ A B) (q : Q₁) : A := seed.1 q
def readRight {Q₁ Q₂ A B : Type*} (seed : Seed Q₁ Q₂ A B) (q : Q₂) : B := seed.2 q

section Completion

variable {I A B S : Type*} [DecidableEq I]

/-- Restore the designated coordinate on every left table read. -/
def completedLeft (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : A × S) : I → A :=
  Function.update (readLeft seed q) j q.1

/-- Restore the designated coordinate on every right table read. -/
def completedRight (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : B × S) : I → B :=
  Function.update (readRight seed q) j q.1

@[simp] theorem completedLeft_coordinate (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : A × S) :
    completedLeft j seed q j = q.1 := by simp [completedLeft]

@[simp] theorem completedRight_coordinate (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : B × S) :
    completedRight j seed q j = q.1 := by simp [completedRight]

theorem update_eq_of_coordinate (xs : I → A) (j : I) (a : A)
    (h : xs j = a) : Function.update xs j a = xs := by
  funext i
  by_cases hi : i = j <;> simp [Function.update, hi, h]

end Completion

end KernelSampling
end
end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_Rectangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! An actual finite probability rectangle implementing all thresholds from a
fixed finite list. The seed distribution is shared; each local acceptance test
depends only on its own density. -/

namespace UniqueGamesTheorem.Foundations.CorrelatedSampling

noncomputable section

variable {α : Type*} [Fintype α]

theorem max_mem_thresholds (thresholds : List ℝ) {x y : ℝ} (hx : x ∈ thresholds)
    (hy : y ∈ thresholds) : max x y ∈ thresholds := by
  by_cases h : x ≤ y <;> simp [max_def, h, hx, hy]

end

end UniqueGamesTheorem.Foundations.CorrelatedSampling

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_LabelBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Per-label diagonal lower bounds for the actual finite shared sampler.
These bounds retain the output label, which is necessary for comparing the
sampler's output distribution with a prescribed diagonal distribution. -/

namespace UniqueGamesTheorem.Foundations.CorrelatedSampling

noncomputable section

variable {σ α : Type*} [Fintype σ] [DecidableEq σ] [DecidableEq α]

def goodLabel (left right : σ → Bool) (decode : σ → α) (a : α) (s : σ) : Bool :=
  (left s && right s) && decide (decode s = a)

end

end UniqueGamesTheorem.Foundations.CorrelatedSampling

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_SamplingLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finite real probability vectors and information inequalities.

`relativeEntropy` uses the natural logarithm and a real-valued finite sum.
Its theorems require support containment, so a positive numerator is never
silently assigned finite divergence against a zero denominator.
-/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {α : Type*} [Fintype α]

def SupportedBy (p q : α → ℝ) : Prop := ∀ a, p a ≠ 0 → q a ≠ 0

noncomputable def relativeEntropy (p q : α → ℝ) : ℝ :=
  ∑ a, p a * Real.log (p a / q a)

noncomputable def posterior (p w : α → ℝ) (z : ℝ) : α → ℝ :=
  fun a => p a * w a / z

omit [Fintype α] in
theorem posterior_supportedBy (p w : α → ℝ) (z : ℝ) :
    SupportedBy (posterior p w z) p := by
  intro a ha hp
  exact ha (by simp [posterior, hp])

theorem mul_log_div_ge_sub {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x - y ≤ x * Real.log (x / y) := by
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hx hy)
  have hm := mul_le_mul_of_nonneg_left h hx.le
  have he : x * (1 - (x / y)⁻¹) = x - y := by
    field_simp [hx.ne', hy.ne']
  rwa [he] at hm

end UniqueGamesTheorem.Foundations.Information

end

section

/-! Finite product-reference entropy decomposition, including zero-probability fibers. -/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def firstMarginal (p : α × β → ℝ) (a : α) : ℝ := ∑ b, p (a, b)

noncomputable def secondMarginal (p : α × β → ℝ) (b : β) : ℝ := ∑ a, p (a, b)

end UniqueGamesTheorem.Foundations.Information

end

section

/-!
Conditional laws on finite spaces, with a normalized default on null rows.
The default remains a probability law when a new input law charges a row
that had zero probability in the original joint distribution.
-/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def conditionalKernel
    (p : α × β → ℝ) (fallback : β → ℝ) (a : α) (b : β) : ℝ := by
  classical
  exact if firstMarginal p a = 0 then fallback b
    else p (a, b) / firstMarginal p a

end UniqueGamesTheorem.Foundations.Information

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_PinskerLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
A finite Pinsker inequality with a nonoptimal constant, sufficient for the
information bound used by Holenstein: TV(p,q)^2 ≤ D_nat(p || q).
The proof factors the L1 distance through square roots and uses log t ≤ t-1.
-/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {α : Type*} [Fintype α]

noncomputable def hellingerSquared (p q : α → ℝ) : ℝ :=
  ∑ a, (Real.sqrt (p a) - Real.sqrt (q a)) ^ 2

theorem sqrt_distance_le_relativeEntropy_term {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hs : x ≠ 0 → y ≠ 0) :
    (Real.sqrt x - Real.sqrt y)^2 ≤ x * Real.log (x / y) - x + y := by
  by_cases hxzero : x = 0
  · subst x
    simp [Real.sq_sqrt hy]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
  have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm (hs hxzero))
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.2 hypos
  have hlog := Real.log_le_sub_one_of_pos (div_pos hsy hsx)
  have hlogid : Real.log (Real.sqrt y / Real.sqrt x) =
      -(Real.log (x / y)) / 2 := by
    rw [Real.log_div hsy.ne' hsx.ne', Real.log_sqrt hy, Real.log_sqrt hx,
      Real.log_div hxzero (hs hxzero)]
    ring
  have hprod : x * (Real.sqrt y / Real.sqrt x) = Real.sqrt x * Real.sqrt y := by
    calc
      x * (Real.sqrt y / Real.sqrt x) = (Real.sqrt x)^2 * (Real.sqrt y / Real.sqrt x) := by
        rw [Real.sq_sqrt hx]
      _ = Real.sqrt x * Real.sqrt y := by field_simp [hsx.ne']
  have hm := mul_le_mul_of_nonneg_left hlog hx
  rw [hlogid, mul_sub, mul_one, hprod] at hm
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]

end UniqueGamesTheorem.Foundations.Information

end

section

/-! Tensorization and conditioning for finite independent coordinates. -/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]

noncomputable def coordinateMarginal (p : (ι → α) → ℝ) (i : ι) (a : α) : ℝ := by
  classical
  exact ∑ x, if x i = a then p x else 0

noncomputable def independentProduct (q : ι → α → ℝ) (x : ι → α) : ℝ := ∏ i, q i (x i)

theorem marginal_expectation (p : (ι → α) → ℝ) (i : ι) (f : α → ℝ) :
    (∑ x, p x * f (x i)) = ∑ a, coordinateMarginal p i a * f a := by
  classical
  simp only [coordinateMarginal, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_mul]

theorem posterior_coordinate_supportedBy (q : ι → α → ℝ) (w : (ι → α) → ℝ)
    (z : ℝ) (i : ι) :
    SupportedBy (coordinateMarginal (posterior (independentProduct q) w z) i) (q i) := by
  classical
  intro a ha hqa
  apply ha
  unfold coordinateMarginal
  apply Finset.sum_eq_zero
  intro x _
  by_cases hxa : x i = a
  · have hzprod : independentProduct q x = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simpa only [hxa] using hqa)
    simp [hxa, posterior, hzprod]
  · simp [hxa]

end UniqueGamesTheorem.Foundations.Information

end

section

/-! Finite side-information conditioning bound from tensorization and log-sum.
All zero likelihood rows have an explicit normalized fallback. -/
namespace UniqueGamesTheorem.Foundations.Information
open scoped BigOperators

noncomputable def posteriorOrOriginal
    {A : Type*} [Fintype A] (p e : A → ℝ) (z : ℝ) : A → ℝ := by
  classical
  exact if 0 < z then posterior p e z else p

end UniqueGamesTheorem.Foundations.Information

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_SharedProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
A single finite rectangle proposal law for two finite families of distributions.
The subdivision includes every density appearing in either family.  Consequently
the local samplers share a seed space independently of their particular inputs.
-/

namespace UniqueGamesTheorem.Foundations.CorrelatedSampling

open scoped BigOperators

noncomputable section

def profileThresholds {κ S : Type*} [Fintype κ] [Fintype S]
    (P : κ → S → ℝ) : List ℝ := by
  classical
  exact (Finset.univ.toList : List (κ × S)).map (fun ks => P ks.1 ks.2)

theorem mem_profileThresholds {κ S : Type*} [Fintype κ] [Fintype S]
    (P : κ → S → ℝ) (k : κ) (s : S) : P k s ∈ profileThresholds P := by
  classical
  exact List.mem_map.mpr ⟨(k, s), by simp, rfl⟩

variable {Q₁ Q₂ S : Type*} [Fintype Q₁] [Fintype Q₂] [Fintype S]

def uniformRejectionRate (S : Type*) [Fintype S] : ℝ :=
  1 - 1 / (Fintype.card S : ℝ)

theorem uniformRejectionRate_nonnegative (S : Type*) [Fintype S] [Nonempty S] :
    0 ≤ uniformRejectionRate S := by
  have hc : (0 : ℝ) < Fintype.card S := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have hc₁ : (1 : ℝ) ≤ Fintype.card S := by
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos : 0 < Fintype.card S))
  apply sub_nonneg.mpr
  exact (div_le_iff₀ hc).2 (by simpa using hc₁)

theorem uniformRejectionRate_lt_one (S : Type*) [Fintype S] [Nonempty S] :
    uniformRejectionRate S < 1 := by
  have hc : (0 : ℝ) < Fintype.card S := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have hp : (0 : ℝ) < 1 / (Fintype.card S : ℝ) := div_pos (by norm_num) hc
  dsimp [uniformRejectionRate]
  linarith

theorem exists_uniformRejectionRate_pow_lt (S : Type*) [Fintype S] [Nonempty S]
    (η : ℝ) (hη : 0 < η) : ∃ n : ℕ, uniformRejectionRate S ^ n < η := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
    (uniformRejectionRate_nonnegative S) (uniformRejectionRate_lt_one S)
  exact (ht.eventually (gt_mem_nhds hη)).exists

end

end UniqueGamesTheorem.Foundations.CorrelatedSampling

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Gadgets_ConcatenationLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Gadget

open scoped BigOperators

section Parent

variable {k I P R X B : Type*} [CommRing k] [Fintype I]
variable [AddCommGroup P] [Module k P]
variable [AddCommGroup R] [Module k R]
variable [AddCommGroup X] [Module k X]
variable [AddCommGroup B] [Module k B]

/-- Sum of the oriented block inclusions on the child logical symbols. -/
def aggregate (J : I → B →ₗ[k] X × B) : (I → B) →ₗ[k] X × B where
  toFun v := ∑ i, J i (v i)
  map_add' u v := by simp [Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum]

/-- The same aggregate, evaluated on actual child shifts. -/
def shiftAggregate (J : I → B →ₗ[k] X × B) (lam : R →ₗ[k] B) :
    (I → R) →ₗ[k] X × B where
  toFun h := aggregate J (fun i => lam (h i))
  map_add' u v := by simp [aggregate, Finset.sum_add_distrib]
  map_smul' c v := by simp [aggregate, Finset.smul_sum]

/-- The parent shift space: precisely the child shifts with zero first
aggregate coordinate. -/
def parentShifts (J : I → B →ₗ[k] X × B) (lam : R →ₗ[k] B) :
    Submodule k (I → R) :=
  LinearMap.ker ((LinearMap.fst k X B).comp (shiftAggregate J lam))

/-- Parent logical translation, the second aggregate coordinate. -/
def parentLogical (J : I → B →ₗ[k] X × B) (lam : R →ₗ[k] B) :
    parentShifts J lam →ₗ[k] B :=
  ((LinearMap.snd k X B).comp (shiftAggregate J lam)).comp
    (parentShifts J lam).subtype

/-- Embedding parent shifts in the actual product of child input spaces. -/
def parentEmbed (J : I → B →ₗ[k] X × B) (lam : R →ₗ[k] B)
    (e : R →ₗ[k] P) : parentShifts J lam →ₗ[k] (I → P) where
  toFun h i := e (h.val i)
  map_add' u v := by ext; simp
  map_smul' c v := by ext; simp

theorem parentEmbed_injective (J : I → B →ₗ[k] X × B) (lam : R →ₗ[k] B)
    (e : R →ₗ[k] P) (he : Function.Injective e) :
    Function.Injective (parentEmbed J lam e) := by
  intro u v huv
  apply Subtype.ext
  funext i
  exact he (congrFun huv i)

theorem shiftAggregate_surjective (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (lam : R →ₗ[k] B)
    (hlam : Function.Surjective lam) : Function.Surjective (shiftAggregate J lam) := by
  classical
  intro v
  obtain ⟨u, hu⟩ := hJ v
  choose h hh using fun i => hlam (u i)
  refine ⟨h, ?_⟩
  have heq : (fun i => lam (h i)) = u := funext hh
  change aggregate J (fun i => lam (h i)) = v
  rw [heq, hu]

theorem parentLogical_surjective (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (lam : R →ₗ[k] B)
    (hlam : Function.Surjective lam) : Function.Surjective (parentLogical J lam) := by
  intro b
  obtain ⟨h, hh⟩ := shiftAggregate_surjective J hJ lam hlam (0, b)
  have hm : h ∈ parentShifts J lam := by
    change (shiftAggregate J lam h).1 = 0
    rw [hh]
  refine ⟨⟨h, hm⟩, ?_⟩
  change (shiftAggregate J lam h).2 = b
  rw [hh]

def parentOutput (J : I → B →ₗ[k] X × B) (C : P → B) (Q : X → B)
    (u : I → P) : B :=
  let v := aggregate J (fun i => C (u i))
  v.2 + Q v.1

/-- Child equivariance gives the actual aggregate translation formula. -/
theorem aggregate_output_shift (J : I → B →ₗ[k] X × B)
    (e : R →ₗ[k] P) (lam : R →ₗ[k] B) (C : P → B)
    (hC : ∀ u h, C (u + e h) = C u + lam h)
    (u : I → P) (h : I → R) :
    aggregate J (fun i => C (u i + e (h i))) =
      aggregate J (fun i => C (u i)) + shiftAggregate J lam h := by
  simp only [hC]
  change aggregate J ((fun i => C (u i)) + (fun i => lam (h i))) = _
  exact (aggregate J).map_add _ _

/-- Parent equivariance is derived for the kernel-defined shift space. -/
theorem parentOutput_equivariant (J : I → B →ₗ[k] X × B)
    (e : R →ₗ[k] P) (lam : R →ₗ[k] B) (C : P → B) (Q : X → B)
    (hC : ∀ u h, C (u + e h) = C u + lam h)
    (u : I → P) (h : parentShifts J lam) :
    parentOutput J C Q (u + parentEmbed J lam e h) =
      parentOutput J C Q u + parentLogical J lam h := by
  have hzero : (shiftAggregate J lam h.val).1 = 0 := h.property
  unfold parentOutput
  change (aggregate J (fun i => C (u i + e (h.val i)))).2 +
    Q (aggregate J (fun i => C (u i + e (h.val i)))).1 = _
  rw [aggregate_output_shift J e lam C hC]
  simp only [Prod.fst_add, Prod.snd_add, hzero, add_zero]
  change _ = _ + (shiftAggregate J lam h.val).2
  abel

end Parent

end UniqueGamesTheorem.Gadget

end

section

namespace UniqueGamesTheorem.Gadget.Enlargement

open scoped BigOperators Classical

noncomputable section

/-- Uniform finite probability, kept rational because the gadget noise is a
pushforward of finite uniform choices. -/
def probability {Ω : Type*} [Fintype Ω] (p : Ω → Prop) : ℚ :=
  (Nat.card {x : Ω // p x} : ℚ) / (Nat.card Ω : ℚ)

/-- Automorphisms act transitively on the nonzero vectors. This follows by
extending an isomorphism between the two one-dimensional spans. -/
theorem exists_equiv_map_nonzero {F V : Type*} [Field F]
    [AddCommGroup V] [Module F V] (x y : V) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ e : V ≃ₗ[F] V, e x = y := by
  let ex := LinearEquiv.toSpanNonzeroSingleton F V x hx
  let ey := LinearEquiv.toSpanNonzeroSingleton F V y hy
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  refine ⟨e, ?_⟩
  have h := (he (ex 1)).symm
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
  simpa [ex, ey] using h

abbrev LinearInjection (F B K : Type*) [Field F] [AddCommGroup B]
    [Module F B] [AddCommGroup K] [Module F K] :=
  {L : B →ₗ[F] K // Function.Injective L}

theorem linearInjection_nonempty_of_finrank_le {F B K : Type*} [Field F]
    [AddCommGroup B] [Module F B] [FiniteDimensional F B]
    [AddCommGroup K] [Module F K] [FiniteDimensional F K]
    (h : Module.finrank F B ≤ Module.finrank F K) :
    Nonempty (LinearInjection F B K) := by
  obtain ⟨L, hL⟩ := finrank_le_iff_exists_linearMap.mp h
  exact ⟨⟨L, hL⟩⟩

/-- Postcomposition permutes all linear injections, including their uniform
finite distribution. -/
def postcompose {F B K : Type*} [Field F] [AddCommGroup B] [Module F B]
    [AddCommGroup K] [Module F K] (e : K ≃ₗ[F] K) :
    LinearInjection F B K ≃ LinearInjection F B K where
  toFun L := ⟨e.toLinearMap.comp L.1, e.injective.comp L.2⟩
  invFun L := ⟨e.symm.toLinearMap.comp L.1, e.symm.injective.comp L.2⟩
  left_inv L := by
    apply Subtype.ext
    ext x
    exact e.symm_apply_apply (L.1 x)
  right_inv L := by
    apply Subtype.ext
    ext x
    exact e.apply_symm_apply (L.1 x)

theorem injection_eval_ne_zero {F B K : Type*} [Field F] [AddCommGroup B]
    [Module F B] [AddCommGroup K] [Module F K]
    (L : LinearInjection F B K) {b : B} (hb : b ≠ 0) : L.1 b ≠ 0 := by
  intro h
  apply hb
  apply L.2
  simpa using h

/-- Every nonzero target vector is hit by an injection at any prescribed
nonzero base vector. This is the surjectivity ingredient of the product-shift
map used before taking the quotient. -/
theorem exists_injection_hitting_nonzero {F B K : Type*} [Field F]
    [AddCommGroup B] [Module F B] [FiniteDimensional F B]
    [AddCommGroup K] [Module F K] [FiniteDimensional F K]
    (h : Module.finrank F B ≤ Module.finrank F K)
    (b : B) (hb : b ≠ 0) (x : K) (hx : x ≠ 0) :
    ∃ L : LinearInjection F B K, L.1 b = x := by
  obtain ⟨L⟩ := linearInjection_nonempty_of_finrank_le h
  obtain ⟨e, he⟩ := exists_equiv_map_nonzero (F := F) (L.1 b) x
    (injection_eval_ne_zero L hb) hx
  exact ⟨postcompose e L, he⟩

/-- The product-shift map before the final quotient. -/
def productShift {F B K : Type*} [Field F] [AddCommGroup B] [Module F B]
    [AddCommGroup K] [Module F K] [Fintype (LinearInjection F B K)] :
    (LinearInjection F B K → B) →ₗ[F] K where
  toFun b := ∑ L : LinearInjection F B K, L.1 (b L)
  map_add' b c := by simp [map_add, Finset.sum_add_distrib]
  map_smul' t b := by simp [map_smul, Finset.smul_sum]

theorem productShift_surjective {F B K : Type*} [Field F]
    [AddCommGroup B] [Module F B] [FiniteDimensional F B]
    [AddCommGroup K] [Module F K] [FiniteDimensional F K]
    [Fintype (LinearInjection F B K)]
    (h : Module.finrank F B ≤ Module.finrank F K)
    (b : B) (hb : b ≠ 0) :
    Function.Surjective (productShift (F := F) (B := B) (K := K)) := by
  intro x
  by_cases hx : x = 0
  · subst x
    exact ⟨0, map_zero _⟩
  · obtain ⟨L, hL⟩ := exists_injection_hitting_nonzero h b hb x hx
    refine ⟨fun L' => if L' = L then b else 0, ?_⟩
    simpa [productShift, apply_ite] using hL

/-- Sum of the injectively relabeled base outputs before quotienting. -/
def enlargedOutput {F B K V : Type*} [Field F]
    [AddCommGroup B] [Module F B] [AddCommGroup K] [Module F K]
    [Fintype (LinearInjection F B K)] (C : V → B)
    (x : LinearInjection F B K → V) : K := ∑ L : LinearInjection F B K, L.1 (C (x L))

/-- Equivariance of the nonlinear sum under the full product of base shifts. -/
theorem enlargedOutput_shift {F B K V : Type*} [Field F]
    [AddCommGroup B] [Module F B] [AddCommGroup K] [Module F K]
    [AddCommGroup V] [Module F V] [Fintype (LinearInjection F B K)]
    (C : V → B) (i : B →ₗ[F] V)
    (hC : ∀ x b, C (x + i b) = C x + b)
    (x : LinearInjection F B K → V) (b : LinearInjection F B K → B) :
    enlargedOutput C (fun L => x L + i (b L)) =
      enlargedOutput C x + productShift b := by
  simp [enlargedOutput, productShift, hC, map_add, Finset.sum_add_distrib]

end

end UniqueGamesTheorem.Gadget.Enlargement

end

section

namespace UniqueGamesTheorem.Gadget.Harmonic

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

/-- The finite harmonic potential, by its exact rational recurrence. -/
def harmonic : ℕ → ℚ
  | 0 => 0
  | r + 1 => harmonic r + (↑(r + 1))⁻¹

@[simp] theorem harmonic_zero : harmonic 0 = 0 := rfl

@[simp] theorem harmonic_succ (r : ℕ) :
    harmonic (r + 1) = harmonic r + (↑(r + 1))⁻¹ := rfl

/-- Rational expectation under uniform sampling on a finite space. -/
def average (f : Ω → ℚ) : ℚ := Finset.univ.expect f

/-- Probability of a decidable event in the finite experiment. -/
def probability (p : Ω → Prop) [DecidablePred p] : ℚ :=
  average (fun ω => if p ω then 1 else 0)

@[simp] theorem average_const [Nonempty Ω] (c : ℚ) :
    average (fun _ : Ω => c) = c :=
  Finset.expect_const Finset.univ_nonempty c

def badRankCoefficient (r₀ : ℕ) : ℚ := harmonic r₀ * 2 ^ r₀

def depth (r₀ : ℕ) (θ : ℚ) : ℕ := ⌊harmonic r₀ / (8 * θ)⌋₊

end UniqueGamesTheorem.Gadget.Harmonic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Gadgets_AdaptivePathsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# From full character lifts to linear-map detection

If a target linear map is injective on the logical alphabet, a linear left
inverse of that restriction turns all logical characters into a full lift.
Detection by this lift implies that the target map does not annihilate the
noise. The left inverse is proved to exist by the vector-space splitting
theorem; it is not an additional premise.
-/

namespace UniqueGamesTheorem.Gadget.DetectionBridge

open Harmonic

variable {K B V E Ω : Type*} [Field K]
variable [AddCommGroup B] [Module K B] [AddCommGroup V] [Module K V]
variable [AddCommGroup E] [Module K E] [Fintype Ω]

/-- Every logical character is extended to the ambient input space. -/
def IsFullLift (ι : B →ₗ[K] V)
    (ψ : Module.Dual K B →ₗ[K] Module.Dual K V) : Prop :=
  ∀ (z : Module.Dual K B) (b : B), ψ z (ι b) = z b

/-- Detection by any member of a character family. Classical decidability
only selects an event indicator on the finite noise sample space. -/
noncomputable def characterDetection (noise : Ω → V)
    (ψ : Module.Dual K B →ₗ[K] Module.Dual K V) : ℚ := by
  classical
  exact probability (fun ω => ∃ z : Module.Dual K B, ψ z (noise ω) ≠ 0)

end UniqueGamesTheorem.Gadget.DetectionBridge

end

section

/-!
# Common-parent factorization before fresh orientation

This is the linear algebra in the lift-factorization lemma of v2 Section 2.
The map `gamma` is obtained from the whole parent family and the first
aggregate coordinate. It is chosen once, before any child is selected.
No rank, genericity, or independence assumption is needed for this step.
-/

namespace UniqueGamesTheorem.Gadget

section Factorization

variable {k S T X B : Type*} [Field k]
variable [AddCommGroup S] [Module k S]
variable [AddCommGroup T] [Module k T]
variable [AddCommGroup X] [Module k X]
variable [AddCommGroup B] [Module k B]

/-- A linear family vanishing on the kernel of a surjection factors as one
linear family on the target. In particular the factor is linear in its
character parameter, rather than a separate arbitrary choice for each one. -/
theorem family_factors_of_ker
    (f : T →ₗ[k] X) (hf : Function.Surjective f)
    (ψ : S →ₗ[k] (T →ₗ[k] k))
    (hker : ∀ z t, f t = 0 → ψ z t = 0) :
    ∃ γ : S →ₗ[k] (X →ₗ[k] k), ∀ z t, ψ z t = γ z (f t) := by
  obtain ⟨σ, hσ⟩ := f.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hf)
  have hσ_apply (x : X) : f (σ x) = x := congrArg (fun g : X →ₗ[k] X => g x) hσ
  let γ : S →ₗ[k] (X →ₗ[k] k) :=
    { toFun := fun z => (ψ z).comp σ
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  refine ⟨γ, fun z t => ?_⟩
  have hz := hker z (t - σ (f t)) (by rw [map_sub, hσ_apply, sub_self])
  have heq : ψ z t - ψ z (σ (f t)) = 0 := by simpa only [map_sub] using hz
  exact sub_eq_zero.mp heq

/-- The common first-coordinate character of a parent lift. `ψ z` is the
parent character on child shifts, `ζ z` its prescribed logical character,
and `(a,b)` the aggregate. A parent shift is exactly a tuple with `a=0`.
The conclusion quantifies one `γ` before all tuples and all later children. -/
theorem common_parent_factorization
    (a : T →ₗ[k] X) (b : T →ₗ[k] B) (ha : Function.Surjective a)
    (ψ : S →ₗ[k] (T →ₗ[k] k)) (ζ : S →ₗ[k] (B →ₗ[k] k))
    (hlift : ∀ z t, a t = 0 → ψ z t = ζ z (b t)) :
    ∃ γ : S →ₗ[k] (X →ₗ[k] k),
      ∀ z t, ψ z t = γ z (a t) + ζ z (b t) := by
  let η : S →ₗ[k] (T →ₗ[k] k) :=
    { toFun := fun z => ψ z - (ζ z).comp b
      map_add' := by intros; ext; simp; abel
      map_smul' := by intros; ext; simp [smul_sub] }
  obtain ⟨γ, hγ⟩ := family_factors_of_ker a ha η (by
    intro z t ht
    change ψ z t - ζ z (b t) = 0
    rw [hlift z t ht, sub_self])
  refine ⟨γ, fun z t => ?_⟩
  have h := hγ z t
  change ψ z t - ζ z (b t) = γ z (a t) at h
  exact (sub_eq_iff_eq_add).mp h

/-- For a surjective aggregate, its first coordinate is surjective. -/
theorem aggregate_fst_surjective (A : T →ₗ[k] X × B)
    (hA : Function.Surjective A) :
    Function.Surjective ((LinearMap.fst k X B).comp A) := by
  intro x
  obtain ⟨t, ht⟩ := hA (x, 0)
  exact ⟨t, congrArg Prod.fst ht⟩

end Factorization

end UniqueGamesTheorem.Gadget

end

section

/-!
# Every parent lift has one common map before the child is selected

This specializes the kernel factorization to the actual product construction.
It derives the child logical characters from a parent lift; it does not assume
independence of the lift and an incoming orientation.
-/

namespace UniqueGamesTheorem.Gadget

open scoped BigOperators

variable {k I P R X B S : Type*} [Field k] [Fintype I] [DecidableEq I]
variable [AddCommGroup P] [Module k P]
variable [AddCommGroup R] [Module k R]
variable [AddCommGroup X] [Module k X]
variable [AddCommGroup B] [Module k B]
variable [AddCommGroup S] [Module k S]

/-- Inclusion of all child shifts before imposing the parent kernel condition. -/
def tupleEmbed (e : R →ₗ[k] P) : (I → R) →ₗ[k] (I → P) where
  toFun h i := e (h i)
  map_add' u v := by ext; simp
  map_smul' c v := by ext; simp

omit [Fintype I] in
theorem tupleEmbed_single (e : R →ₗ[k] P) (i : I) (h : R) :
    tupleEmbed e (Pi.single i h) = Pi.single i (e h) := by
  ext j
  by_cases hij : i = j
  · subst j; simp [tupleEmbed]
  · simp [tupleEmbed, hij]

theorem shiftAggregate_single (J : I → B →ₗ[k] X × B)
    (lam : R →ₗ[k] B) (i : I) (h : R) :
    shiftAggregate J lam (Pi.single i h) = J i (lam h) := by
  classical
  simp [shiftAggregate, aggregate, Pi.single_apply, apply_ite, map_zero]

/-- Actual parent lifts factor through the same aggregate first-coordinate
family on all child shifts. The existential `γ` occurs before both `i` and `h`.
This is the common-parent requirement used before revealing fresh orientation. -/
theorem parent_lift_common_child
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J))
    (e : R →ₗ[k] P) (lam : R →ₗ[k] B) (hlam : Function.Surjective lam)
    (ψ : S →ₗ[k] ((I → P) →ₗ[k] k)) (ζ : S →ₗ[k] (B →ₗ[k] k))
    (hlift : ∀ z (h : parentShifts J lam),
      ψ z (parentEmbed J lam e h) = ζ z (parentLogical J lam h)) :
    ∃ γ : S →ₗ[k] (X →ₗ[k] k), ∀ i z h,
      ψ z (Pi.single i (e h)) =
        γ z (J i (lam h)).1 + ζ z (J i (lam h)).2 := by
  let a := (LinearMap.fst k X B).comp (shiftAggregate J lam)
  let b := (LinearMap.snd k X B).comp (shiftAggregate J lam)
  let Ψ : S →ₗ[k] ((I → R) →ₗ[k] k) :=
    { toFun := fun z => (ψ z).comp (tupleEmbed e)
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  have ha : Function.Surjective a :=
    aggregate_fst_surjective _ (shiftAggregate_surjective J hJ lam hlam)
  obtain ⟨γ, hγ⟩ := common_parent_factorization a b ha Ψ ζ (by
    intro z h hh
    exact hlift z ⟨h, hh⟩)
  refine ⟨γ, fun i z h => ?_⟩
  have heq := hγ z (Pi.single i h)
  change ψ z (tupleEmbed e (Pi.single i h)) =
    γ z (shiftAggregate J lam (Pi.single i h)).1 +
      ζ z (shiftAggregate J lam (Pi.single i h)).2 at heq
  simpa only [tupleEmbed_single, shiftAggregate_single] using heq

end UniqueGamesTheorem.Gadget

end

section

/-!
# Fresh finite orientations

The rank is fixed before the fresh isomorphism is sampled.  The finite
counting identities below do not require the subsequent lift to be independent
of that isomorphism.  In particular, an event concerning the oriented subspace
may be tested after arbitrary earlier choices have been fixed.
-/

noncomputable section

open scoped BigOperators
open Module

namespace UniqueGamesTheorem.Gadget.Orientation

section LinearOrientation

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]

/-- The finite Grassmannian at a rank chosen before orientation. -/
def RankSpace (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (r : ℕ) :=
  {E : Submodule K V // finrank K E = r}

instance rankSpaceAction (r : ℕ) : MulAction (V ≃ₗ[K] V) (RankSpace K V r) where
  smul a E := ⟨E.val.map a.toLinearMap, (a.finrank_map_eq E.val).trans E.property⟩
  one_smul E := by
    apply Subtype.ext
    exact E.val.map_id
  mul_smul a b E := by
    apply Subtype.ext
    exact E.val.map_comp b.toLinearMap a.toLinearMap

variable {B U : Type*} [AddCommGroup B] [Module K B]
    [AddCommGroup U] [Module K U]

/-- Choosing a reference isomorphism identifies all orientations with the
automorphism group of the target. -/
def orientationEquiv (J₀ : B ≃ₗ[K] U) : (B ≃ₗ[K] U) ≃ (U ≃ₗ[K] U) where
  toFun J := J₀.symm.trans J
  invFun a := J₀.trans a
  left_inv J := by ext x; simp
  right_inv a := by ext x; simp

/-- Dualization is a bijection on finite-dimensional isomorphisms.  This
connects uniform primal orientations to uniform character-space orientations. -/
def dualOrientationEquiv [FiniteDimensional K B] [FiniteDimensional K U] :
    (B ≃ₗ[K] U) ≃ (Module.Dual K U ≃ₗ[K] Module.Dual K B) where
  toFun J := J.dualMap
  invFun e := ((Module.evalEquiv K B).trans e.dualMap).trans (Module.evalEquiv K U).symm
  left_inv J := by
    ext b
    apply (Module.evalEquiv K U).injective
    ext φ
    simp
  right_inv e := by
    ext φ b
    simp

end LinearOrientation

end UniqueGamesTheorem.Gadget.Orientation

end

end

section

/-!
# Fresh orientations of nonzero perturbations

This is the nonzero-symbol uniformity step in the latent-noise recurrence.
The perturbation is fixed before the orientation, and zero is excluded from
both sample spaces explicitly.
-/

noncomputable section

open scoped BigOperators

namespace UniqueGamesTheorem.Gadget.OrientationVectors

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem equiv_apply_ne_zero {B U : Type*} [AddCommGroup B] [Module K B]
    [AddCommGroup U] [Module K U] (J : B ≃ₗ[K] U) {b : B} (hb : b ≠ 0) :
    J b ≠ 0 := by
  intro h
  apply hb
  exact J.injective (h.trans (map_zero J).symm)

instance nonzeroAction : MulAction (V ≃ₗ[K] V) {x : V // x ≠ 0} where
  smul a x := ⟨a x.val, equiv_apply_ne_zero a x.property⟩
  one_smul x := by apply Subtype.ext; rfl
  mul_smul a b x := by apply Subtype.ext; rfl

end UniqueGamesTheorem.Gadget.OrientationVectors

end

end

section

namespace UniqueGamesTheorem.Gadget.Parameters

open Harmonic
open scoped BigOperators

/-- Computable rank exceeding any prescribed rational harmonic level. -/
def rankFor (level : ℚ) : ℕ := 2 ^ ⌈2 * level⌉₊

/-- Strictly positive genericity error meeting the harmonic bad-rank budget. -/
def genericityError (r₀ : ℕ) : ℚ := 1 / (2 * (badRankCoefficient r₀ + 1))

/-- Explicit threshold depending only on the requested nonlinear error. -/
def initialRank (p : ℚ) : ℕ := rankFor (8 * (p⁻¹ + 1))

end UniqueGamesTheorem.Gadget.Parameters

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Gadgets_QuotientLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Gadget.Quotient

variable {𝕜 P B : Type*} [Ring 𝕜]
variable [AddCommGroup P] [Module 𝕜 P] [AddCommGroup B] [Module 𝕜 B]

/-- The logical kernel viewed as a submodule of the ambient input space. -/
def shiftKernel (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) : Submodule 𝕜 P :=
  (LinearMap.ker lam).map R.subtype

abbrev Space (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) := P ⧸ shiftKernel R lam

def projection (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) :
    P →ₗ[𝕜] Space R lam := (shiftKernel R lam).mkQ

theorem projection_surjective (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) :
    Function.Surjective (projection R lam) := (shiftKernel R lam).mkQ_surjective

theorem mem_shiftKernel (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (x : P) :
    x ∈ shiftKernel R lam ↔ ∃ h : R, lam h = 0 ∧ (h : P) = x := Iff.rfl

theorem projection_eq_zero (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (h : R) :
    projection R lam (h : P) = 0 ↔ lam h = 0 := by
  change (Submodule.Quotient.mk (h : P) : Space R lam) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, mem_shiftKernel]
  constructor
  · rintro ⟨k, hk, hkh⟩
    have : k = h := Subtype.ext hkh
    simpa [this] using hk
  · intro hh
    exact ⟨h, hh, rfl⟩

/-- Inclusion of the quotient shift space into the ambient quotient. -/
def quotientShift (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) :
    (R ⧸ LinearMap.ker lam) →ₗ[𝕜] Space R lam :=
  (LinearMap.ker lam).liftQ ((projection R lam).comp R.subtype) (by
    intro h hh
    exact (projection_eq_zero R lam h).mpr hh)

@[simp] theorem quotientShift_mk (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (h : R) :
    quotientShift R lam (Submodule.Quotient.mk h) = projection R lam (h : P) := rfl

/-- The logical alphabet is realized as actual linear shifts of the quotient. -/
noncomputable def logicalShift (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) : B →ₗ[𝕜] Space R lam :=
  (quotientShift R lam).comp (lam.quotKerEquivOfSurjective hlam).symm.toLinearMap

@[simp] theorem logicalShift_lambda (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) (h : R) :
    logicalShift R lam hlam (lam h) = projection R lam (h : P) := by
  simp [logicalShift, LinearMap.quotKerEquivOfSurjective_symm_apply]

theorem logicalShift_injective (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) : Function.Injective (logicalShift R lam hlam) := by
  intro a b hab
  obtain ⟨h, rfl⟩ := hlam a
  obtain ⟨k, rfl⟩ := hlam b
  rw [logicalShift_lambda, logicalShift_lambda] at hab
  have hz : projection R lam ((h - k : R) : P) = 0 := by
    change projection R lam ((h : P) - (k : P)) = 0
    rw [map_sub, hab, sub_self]
  have := (projection_eq_zero R lam (h - k)).mp hz
  exact sub_eq_zero.mp (by simpa only [map_sub] using this)

/-- Equivariance under every allowed shift; no linearity of `C` is assumed. -/
def Equivariant (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (C : P → B) : Prop :=
  ∀ (u : P) (h : R), C (u + (h : P)) = C u + lam h

/-- Translating by a logical shift bijects output fibers even after conditioning
on an arbitrary shift-invariant event. -/
def conditionedShiftEquiv (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (C : P → B) (hC : Equivariant R lam C) (D : P → Prop)
    (hD : ∀ (u : P) (h : R), D (u + (h : P)) ↔ D u) (b : B) (h : R) :
    {u : P // C u = b ∧ D u} ≃ {u : P // C u = b + lam h ∧ D u} where
  toFun u := ⟨u.val + (h : P), by
    exact ⟨(hC u.val h).trans (congrArg (fun x => x + lam h) u.property.1),
      (hD u.val h).mpr u.property.2⟩⟩
  invFun u := ⟨u.val + ((-h : R) : P), by
    constructor
    · rw [hC u.val (-h), u.property.1, map_neg, add_neg_cancel_right]
    · exact (hD u.val (-h)).mpr u.property.2⟩
  left_inv u := Subtype.ext (by simp)
  right_inv u := Subtype.ext (by simp)

/-- Surjectivity makes all output fibers equally large inside an invariant
event, without assuming that this event has positive probability. -/
noncomputable def conditionedFiberEquiv (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) (C : P → B) (hC : Equivariant R lam C)
    (D : P → Prop) (hD : ∀ (u : P) (h : R), D (u + (h : P)) ↔ D u)
    (b c : B) : {u : P // C u = b ∧ D u} ≃ {u : P // C u = c ∧ D u} := by
  classical
  let h : R := Classical.choose (hlam (c - b))
  have hh : lam h = c - b := Classical.choose_spec (hlam (c - b))
  have he : b + lam h = c := by rw [hh, add_comm, sub_add_cancel]
  simpa only [he] using conditionedShiftEquiv R lam C hC D hD b h

/-- Splitting an invariant event into its output fibers. -/
def conditionedSigmaEquiv (C : P → B) (D : P → Prop) :
    {u : P // D u} ≃ Σ b : B, {u : P // C u = b ∧ D u} where
  toFun u := ⟨C u.val, ⟨u.val, rfl, u.property⟩⟩
  invFun u := ⟨u.2.val, u.2.property.2⟩
  left_inv _ := rfl
  right_inv := by rintro ⟨b, u, hu, hD⟩; cases hu; rfl

/-- An invariant event factors as an independent logical output and one fiber. -/
noncomputable def conditionedProductEquiv (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) (C : P → B) (hC : Equivariant R lam C)
    (D : P → Prop) (hD : ∀ (u : P) (h : R), D (u + (h : P)) ↔ D u) (b : B) :
    {u : P // D u} ≃ B × {u : P // C u = b ∧ D u} :=
  ((conditionedSigmaEquiv C D).trans
    (Equiv.sigmaCongrRight (fun c => conditionedFiberEquiv R lam hlam C hC D hD c b))).trans
    (Equiv.sigmaEquivProd _ _)

@[simp] theorem conditionedProductEquiv_fst (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) (C : P → B) (hC : Equivariant R lam C)
    (D : P → Prop) (hD : ∀ (u : P) (h : R), D (u + (h : P)) ↔ D u) (b : B)
    (u : {u : P // D u}) :
    (conditionedProductEquiv R lam hlam C hC D hD b u).1 = C u.val := rfl

theorem output_constant_on_fibers (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (C : P → B) (hC : Equivariant R lam C) (x y : P)
    (hxy : projection R lam x = projection R lam y) : C x = C y := by
  have hm : x - y ∈ shiftKernel R lam := (Submodule.Quotient.eq _).mp hxy
  obtain ⟨h, hh, hval⟩ := (mem_shiftKernel R lam _).mp hm
  have he : y + (h : P) = x := by rw [hval, add_comm, sub_add_cancel]
  simpa only [he, hh, add_zero] using hC y h

def output (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (C : P → B) (hC : Equivariant R lam C) : Space R lam → B :=
  _root_.Quotient.lift C (fun _ _ h =>
    output_constant_on_fibers R lam C hC _ _ (_root_.Quotient.sound h))

@[simp] theorem output_projection (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (C : P → B) (hC : Equivariant R lam C) (u : P) :
    output R lam C hC (projection R lam u) = C u := rfl

theorem output_equivariant (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (hlam : Function.Surjective lam) (C : P → B) (hC : Equivariant R lam C)
    (x : Space R lam) (b : B) :
    output R lam C hC (x + logicalShift R lam hlam b) = output R lam C hC x + b := by
  obtain ⟨u, rfl⟩ := projection_surjective R lam x
  obtain ⟨h, rfl⟩ := hlam b
  rw [logicalShift_lambda, ← map_add, output_projection, output_projection]
  exact hC u h

/-- Translation by the logical kernel parametrizes a quotient fiber. -/
def fiberMap (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B) (a : P) :
    shiftKernel R lam → {u : P // projection R lam u = projection R lam a} :=
  fun h => ⟨a + (h : P), by
    have hh : projection R lam (h : P) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr h.property
    rw [map_add, hh, add_zero]⟩

end UniqueGamesTheorem.Gadget.Quotient

/-!
# Conditional uniformity by translation averaging

For uniform finite input, an equivariant output is uniform even conditional on
any shift-invariant observable.  The observable need not have a finite range.
The proof averages translations directly and therefore never divides by a
conditioning probability.  In particular it applies to the output difference
at a fixed perturbation, and to an independent finite noise choice.
-/

namespace UniqueGamesTheorem.Gadget

section

universe u v

/-- An equivariant finite stage, including its concrete finite noise sampler. -/
structure Stage (k : Type u) (B : Type v) [CommRing k]
    [AddCommGroup B] [Module k B] where
  Input : Type v
  Shift : Type v
  Noise : Type v
  [inputAdd : AddCommGroup Input]
  [inputModule : Module k Input]
  [shiftAdd : AddCommGroup Shift]
  [shiftModule : Module k Shift]
  [inputFinite : Finite Input]
  [shiftFinite : Finite Shift]
  [noiseFinite : Finite Noise]
  [noiseNonempty : Nonempty Noise]
  embed : Shift →ₗ[k] Input
  embed_injective : Function.Injective embed
  logical : Shift →ₗ[k] B
  logical_surjective : Function.Surjective logical
  output : Input → B
  equivariant : ∀ u h, output (u + embed h) = output u + logical h
  noise : Noise → Input

attribute [instance] Stage.inputAdd Stage.inputModule Stage.shiftAdd Stage.shiftModule
  Stage.inputFinite Stage.shiftFinite Stage.noiseFinite Stage.noiseNonempty

namespace Stage

variable {k : Type u} {B : Type v} [CommRing k]
variable [AddCommGroup B] [Module k B] [Finite B]

/-- The height-zero input, shift and uniform noise alphabet. -/
def base : Stage k B where
  Input := B
  Shift := B
  Noise := B
  embed := LinearMap.id
  embed_injective := Function.injective_id
  logical := LinearMap.id
  logical_surjective := Function.surjective_id
  output := id
  equivariant := by intros; rfl
  noise := id

variable {I X : Type v} [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module k X]

/-- One complete recursive level, with actual single-coordinate leaf noise. -/
noncomputable def next (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (Q : X → B)
    (s : Stage k B) : Stage k B where
  Input := I → s.Input
  Shift := parentShifts J s.logical
  Noise := I × s.Noise
  embed := parentEmbed J s.logical s.embed
  embed_injective := parentEmbed_injective J s.logical s.embed s.embed_injective
  logical := parentLogical J s.logical
  logical_surjective := parentLogical_surjective J hJ s.logical s.logical_surjective
  output := parentOutput J s.output Q
  equivariant := parentOutput_equivariant J s.embed s.logical s.output Q s.equivariant
  noise := fun t => Pi.single t.1 (s.noise t.2)

/-- The finite stage at any natural height, using the same alphabet and block
family at every level. Surjectivity and equivariance have been proved by the
constructor, and hence are available at every height without extra hypotheses. -/
noncomputable def iterate (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (Q : X → B) : ℕ → Stage k B
  | 0 => base
  | n + 1 => next J hJ Q (iterate J hJ Q n)

@[simp] theorem iterate_zero (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (Q : X → B) :
    iterate J hJ Q 0 = base := rfl

@[simp] theorem iterate_succ (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (Q : X → B) (n : ℕ) :
    iterate J hJ Q (n + 1) = next J hJ Q (iterate J hJ Q n) := rfl

end Stage

end

/-!
# Actual lifts and their descendant restrictions

Every descendant lift is constructed by a linear section of the child image.
Its detection on the child noise implies detection by the parent family on
the actual embedded noise. The common parent family is chosen before the
child index; only the image section is chosen after that index is known.
-/

universe u v

variable {k : Type u} {B : Type v} [Field k]
variable [AddCommGroup B] [Module k B]

/-- A linear lift of a logical character subspace to the actual stage input. -/
structure Lift (s : Stage k B) (S : Submodule k (B →ₗ[k] k)) where
  family : S →ₗ[k] (s.Input →ₗ[k] k)
  agrees : ∀ z h, family z (s.embed h) = z.val (s.logical h)

/-- Restricting a lift preserves its prescribed logical characters. -/
def Lift.restrict {s : Stage k B} {S T : Submodule k (B →ₗ[k] k)}
    (L : Lift s T) (hST : S ≤ T) : Lift s S where
  family := L.family.comp (Submodule.inclusion hST)
  agrees := by intro z h; exact L.agrees _ h

variable {I X : Type v} [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module k X]

/-- Linear insertion into one physical input coordinate. -/
def singleInput (i : I) (P : Type v) [AddCommGroup P] [Module k P] :
    P →ₗ[k] (I → P) where
  toFun p := Pi.single i p
  map_add' a b := by ext j; by_cases h : i = j <;> simp [h]
  map_smul' c p := by ext j; by_cases h : i = j <;> simp [h]

/-- The logical map of a child, obtained from the common parent first-coordinate
map and the prescribed logical character. -/
def childCharacter (J : I → B →ₗ[k] X × B)
    {S : Submodule k (B →ₗ[k] k)} (γ : S →ₗ[k] (X →ₗ[k] k)) (i : I) :
    S →ₗ[k] (B →ₗ[k] k) where
  toFun z := (γ z).comp ((LinearMap.fst k X B).comp (J i)) +
    z.val.comp ((LinearMap.snd k X B).comp (J i))
  map_add' a b := by ext; simp; abel
  map_smul' c z := by ext; simp [smul_add]

theorem exists_common_child_character
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J))
    (Q : X → B) (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) :
    ∃ γ : S →ₗ[k] (X →ₗ[k] k), ∀ i z h,
      L.family z (Pi.single i (s.embed h)) = childCharacter J γ i z (s.logical h) := by
  have hlift : ∀ z (h : parentShifts J s.logical),
      L.family z (parentEmbed J s.logical s.embed h) =
        z.val (parentLogical J s.logical h) := by
    intro z h
    exact L.agrees z h
  have hcommon := parent_lift_common_child (S := S) J hJ s.embed s.logical
    s.logical_surjective
  obtain ⟨γ, hγ⟩ := hcommon L.family S.subtype hlift
  exact ⟨γ, fun i z h => hγ i z h⟩

/-- The descendant family using a section of the actual image. -/
def descendantFamily {s : Stage k B} {S : Submodule k (B →ₗ[k] k)}
    (ψ : S →ₗ[k] ((I → s.Input) →ₗ[k] k)) (i : I)
    (φ : S →ₗ[k] (B →ₗ[k] k))
    (sectionMap : LinearMap.range φ →ₗ[k] S) :
    LinearMap.range φ →ₗ[k] (s.Input →ₗ[k] k) where
  toFun z := (ψ (sectionMap z)).comp (singleInput i s.Input)
  map_add' a b := by ext; simp
  map_smul' c z := by ext; simp

/-- Every child image carries a genuine child lift. The section is constructed
by ordinary linear algebra and is chosen without any later path or leaf symbol. -/
theorem exists_descendant_lift
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J))
    (Q : X → B) (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S)
    (γ : S →ₗ[k] (X →ₗ[k] k))
    (hγ : ∀ i z h, L.family z (Pi.single i (s.embed h)) =
      childCharacter J γ i z (s.logical h)) (i : I) :
    ∃ (L' : Lift s (LinearMap.range (childCharacter J γ i)))
      (sectionMap : LinearMap.range (childCharacter J γ i) →ₗ[k] S),
      (∀ z, childCharacter J γ i (sectionMap z) = z.val) ∧
      (∀ z p, L'.family z p = L.family (sectionMap z) (Pi.single i p)) := by
  let φ : S →ₗ[k] (B →ₗ[k] k) := childCharacter J γ i
  let : Module.Free k (LinearMap.range φ) :=
    Module.Free.of_divisionRing k (LinearMap.range φ)
  let : Module.Projective k (LinearMap.range φ) := Module.Projective.of_free
  obtain ⟨σ, hσ⟩ := φ.rangeRestrict.exists_rightInverse_of_surjective
    φ.range_rangeRestrict
  have hσ' (z : LinearMap.range φ) : φ (σ z) = z.val :=
    congrArg Subtype.val (congrArg (fun f => f z) hσ)
  let L' : Lift s (LinearMap.range φ) :=
    { family := descendantFamily L.family i φ σ
      agrees := by
        intro z h
        change L.family (σ z) (Pi.single i (s.embed h)) = z.val (s.logical h)
        rw [hγ, hσ'] }
  exact ⟨L', σ, hσ', fun z p => rfl⟩

end UniqueGamesTheorem.Gadget

namespace UniqueGamesTheorem.Gadget.Descent

universe u v

variable {k : Type u} {B I X : Type v} [Field k]
variable [AddCommGroup B] [Module k B] [Finite B] [FiniteDimensional k B]
variable [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module k X]

variable (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J)) (Q : X → B)

noncomputable def commonGamma (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) : S →ₗ[k] (X →ₗ[k] k) :=
  Classical.choose (exists_common_child_character J hJ Q s S L)

omit [Finite B] [FiniteDimensional k B] in
theorem commonGamma_spec (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) (z : S) (h : s.Shift) :
    L.family z (Pi.single i (s.embed h)) =
      childCharacter J (commonGamma J hJ Q s S L) i z (s.logical h) :=
  Classical.choose_spec (exists_common_child_character J hJ Q s S L) i z h

noncomputable def childDomain (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) : Submodule k (B →ₗ[k] k) :=
  LinearMap.range (childCharacter J (commonGamma J hJ Q s S L) i)

noncomputable def childLift (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) :
    Lift s (childDomain J hJ Q s S L i) :=
  Classical.choose (exists_descendant_lift J hJ Q s S L
    (commonGamma J hJ Q s S L) (commonGamma_spec J hJ Q s S L) i)

noncomputable def childSection (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) :
    childDomain J hJ Q s S L i →ₗ[k] S :=
  Classical.choose (Classical.choose_spec (exists_descendant_lift J hJ Q s S L
    (commonGamma J hJ Q s S L) (commonGamma_spec J hJ Q s S L) i))

/-- Terminal logical rank along the actual recursively sampled path. The
final uniform symbol is ignored by this rank function. -/
noncomputable def leafRank
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J)) (Q : X → B) :
    (n : ℕ) → (S : Submodule k (B →ₗ[k] k)) →
    Lift (Stage.iterate J hJ Q n) S → (Stage.iterate J hJ Q n).Noise → ℕ
  | 0, S, _, _ => Module.finrank k S
  | n + 1, S, L, t => leafRank J hJ Q n
      (childDomain J hJ Q (Stage.iterate J hJ Q n) S L t.1)
      (childLift J hJ Q (Stage.iterate J hJ Q n) S L t.1) t.2

end UniqueGamesTheorem.Gadget.Descent

/-!
# Harmonic potential for the actual recursively selected lifts

This is the adaptive induction on the concrete descendant lift construction.
The first outgoing step may begin at a bad subspace; every later orientation
is fresh. Accordingly the bound has one initial bad-space penalty, which
vanishes for the fixed generic top subspace.
-/

namespace UniqueGamesTheorem.Gadget.DescentProbability

open Harmonic Descent

universe u v

variable {k : Type u} {B I X : Type v} [Field k]
variable [AddCommGroup B] [Module k B] [Finite B] [FiniteDimensional k B]
variable [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module k X]

variable (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J)) (Q : X → B)

noncomputable instance noiseFintype (n : ℕ) : Fintype (Stage.iterate J hJ Q n).Noise := by
  induction n with
  | zero => exact Fintype.ofFinite B
  | succ n ih =>
    exact inferInstanceAs (Fintype (I × (Stage.iterate J hJ Q n).Noise))

noncomputable def terminalPotential (n : ℕ) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.iterate J hJ Q n) S) : ℚ :=
  average (fun t => UniqueGamesTheorem.Gadget.Harmonic.harmonic (leafRank J hJ Q n S L t))

omit [FiniteDimensional k B] in
@[simp] theorem terminalPotential_zero (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.iterate J hJ Q 0) S) :
    terminalPotential J hJ Q 0 S L = UniqueGamesTheorem.Gadget.Harmonic.harmonic (Module.finrank k S) := by
  change average (fun _ : (Stage.iterate J hJ Q 0).Noise =>
    UniqueGamesTheorem.Gadget.Harmonic.harmonic (Module.finrank k S)) = _
  exact average_const _

end UniqueGamesTheorem.Gadget.DescentProbability

namespace UniqueGamesTheorem.Gadget.LeafDetection

open Harmonic Descent DescentProbability

universe v

variable {B I X : Type v}
variable [AddCommGroup B] [Module (ZMod 2) B] [Finite B] [FiniteDimensional (ZMod 2) B]
variable [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module (ZMod 2) X]

variable (J : I → B →ₗ[ZMod 2] X × B)
variable (hJ : Function.Surjective (aggregate J)) (Q : X → B)

noncomputable def survivalProbability (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q n) S) : ℚ :=
  probability (fun t => 0 < leafRank J hJ Q n S L t)

noncomputable def detectionProbability (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q n) S) : ℚ := by
  classical
  exact probability (fun t => ∃ z : S, L.family z ((Stage.iterate J hJ Q n).noise t) ≠ 0)

omit [FiniteDimensional (ZMod 2) B] in
@[simp] theorem survivalProbability_zero
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q 0) S) :
    survivalProbability J hJ Q 0 S L =
      if 0 < Module.finrank (ZMod 2) S then 1 else 0 := by
  change average (fun _ : (Stage.iterate J hJ Q 0).Noise =>
    if 0 < Module.finrank (ZMod 2) S then (1 : ℚ) else 0) = _
  exact average_const _

end UniqueGamesTheorem.Gadget.LeafDetection

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Gadgets_NonlinearRecurrenceLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Gadget.NonlinearRecurrence

open scoped BigOperators

variable {k I P R X B : Type*} [CommRing k]
variable [Fintype I] [DecidableEq I]
variable [AddCommGroup P] [Module k P] [Fintype P]
variable [AddCommGroup R] [Module k R]
variable [AddCommGroup X] [Module k X] [Fintype X]
variable [AddCommGroup B] [Module k B] [Fintype B] [DecidableEq B]

def change (F : X × B → B) (p d : X × B) : ℚ :=
  if F (p + d) ≠ F p then 1 else 0

omit [Fintype X] [Fintype B] in
@[simp] theorem change_zero (F : X × B → B) (p : X × B) : change F p 0 = 0 := by
  simp [change]

end UniqueGamesTheorem.Gadget.NonlinearRecurrence

end

section

namespace UniqueGamesTheorem.Gadget.StageQuotient

universe u v

variable {k : Type u} {B : Type v} [CommRing k]
variable [AddCommGroup B] [Module k B]

def shifts (s : Stage k B) : Submodule k s.Input := LinearMap.range s.embed

noncomputable def shiftEquiv (s : Stage k B) : s.Shift ≃ₗ[k] shifts s :=
  LinearEquiv.ofInjective s.embed s.embed_injective

@[simp] theorem shiftEquiv_coe (s : Stage k B) (h : s.Shift) :
    ((shiftEquiv s h : shifts s) : s.Input) = s.embed h := rfl

@[simp] theorem embed_shiftEquiv_symm (s : Stage k B) (h : shifts s) :
    s.embed ((shiftEquiv s).symm h) = (h : s.Input) :=
  LinearEquiv.ofInjective_symm_apply s.embed h

noncomputable def logical (s : Stage k B) : shifts s →ₗ[k] B :=
  s.logical.comp (shiftEquiv s).symm.toLinearMap

@[simp] theorem logical_shiftEquiv (s : Stage k B) (h : s.Shift) :
    logical s (shiftEquiv s h) = s.logical h := by
  simp [logical]

theorem logical_surjective (s : Stage k B) : Function.Surjective (logical s) := by
  intro b
  obtain ⟨h, hh⟩ := s.logical_surjective b
  exact ⟨shiftEquiv s h, (logical_shiftEquiv s h).trans hh⟩

theorem equivariant (s : Stage k B) :
    Quotient.Equivariant (shifts s) (logical s) s.output := by
  intro u h
  have he := s.equivariant u ((shiftEquiv s).symm h)
  simpa only [embed_shiftEquiv_symm, logical, LinearMap.comp_apply,
    LinearEquiv.coe_coe] using he

abbrev Space (s : Stage k B) := Quotient.Space (shifts s) (logical s)

noncomputable def projection (s : Stage k B) : s.Input →ₗ[k] Space s :=
  Quotient.projection (shifts s) (logical s)

theorem projection_surjective (s : Stage k B) : Function.Surjective (projection s) :=
  Quotient.projection_surjective (shifts s) (logical s)

instance spaceFinite (s : Stage k B) : Finite (Space s) :=
  Finite.of_surjective (projection s) (projection_surjective s)

noncomputable def shift (s : Stage k B) : B →ₗ[k] Space s :=
  Quotient.logicalShift (shifts s) (logical s) (logical_surjective s)

theorem shift_injective (s : Stage k B) : Function.Injective (shift s) :=
  Quotient.logicalShift_injective (shifts s) (logical s) (logical_surjective s)

@[simp] theorem shift_logical (s : Stage k B) (h : s.Shift) :
    shift s (s.logical h) = projection s (s.embed h) := by
  rw [← logical_shiftEquiv s h]
  exact Quotient.logicalShift_lambda (shifts s) (logical s) (logical_surjective s)
    (shiftEquiv s h)

noncomputable def output (s : Stage k B) : Space s → B :=
  Quotient.output (shifts s) (logical s) s.output (equivariant s)

@[simp] theorem output_projection (s : Stage k B) (u : s.Input) :
    output s (projection s u) = s.output u := rfl

theorem output_equivariant (s : Stage k B) (x : Space s) (b : B) :
    output s (x + shift s b) = output s x + b :=
  Quotient.output_equivariant (shifts s) (logical s) (logical_surjective s)
    s.output (equivariant s) x b

/-- Original finite noise choices, pushed through the actual quotient map. -/
noncomputable def noise (s : Stage k B) : s.Noise → Space s :=
  fun t => projection s (s.noise t)

/-- The quotient is again a finite stage; its logical map is now the identity. -/
noncomputable def toStage [Finite B] (s : Stage k B) : Stage k B where
  Input := Space s
  Shift := B
  Noise := s.Noise
  embed := shift s
  embed_injective := shift_injective s
  logical := LinearMap.id
  logical_surjective := Function.surjective_id
  output := output s
  equivariant := output_equivariant s
  noise := noise s

end UniqueGamesTheorem.Gadget.StageQuotient

end

section

noncomputable section

namespace UniqueGamesTheorem.Gadget.EnlargementConstruction

open scoped BigOperators Classical
open Enlargement

universe u

variable {B K V N : Type u}
variable [AddCommGroup B] [Module (ZMod 2) B] [Fintype B]
variable [FiniteDimensional (ZMod 2) B]
variable [AddCommGroup K] [Module (ZMod 2) K] [Fintype K]
variable [FiniteDimensional (ZMod 2) K]
variable [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable [Fintype N] [Nonempty N]

abbrev Copies (B K : Type u) [AddCommGroup B] [Module (ZMod 2) B]
    [AddCommGroup K] [Module (ZMod 2) K] := LinearInjection (ZMod 2) B K

/-- A concrete finite enumeration exists because an injection is determined
by its finite function table. -/
@[instance_reducible]
noncomputable def copiesFintype : Fintype (Copies B K) :=
  Fintype.ofInjective (fun L : Copies B K => (L.1 : B → K)) (by
    intro L M h
    apply Subtype.ext
    exact LinearMap.ext (congrFun h))

local instance enlargementCopiesFintype : Fintype (Copies B K) := copiesFintype

def productEmbed (i : B →ₗ[ZMod 2] V) :
    (Copies B K → B) →ₗ[ZMod 2] (Copies B K → V) where
  toFun b L := i (b L)
  map_add' b c := by ext L; exact map_add i (b L) (c L)
  map_smul' t b := by ext L; exact map_smul i t (b L)

omit [Fintype B] [FiniteDimensional (ZMod 2) B] [Fintype K]
  [FiniteDimensional (ZMod 2) K] [Fintype V] in
theorem productEmbed_injective (i : B →ₗ[ZMod 2] V)
    (hi : Function.Injective i) : Function.Injective (productEmbed (K := K) i) := by
  intro b c h
  funext L
  apply hi
  exact congrFun h L

/-- The product before the quotient. Its finite noise sampler first chooses
an injection uniformly, then independently chooses the original base noise. -/
def productStage (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0) : Stage (ZMod 2) K := by
  letI : Nonempty (Copies B K) := linearInjection_nonempty_of_finrank_le hdim
  exact
    { Input := Copies B K → V
      Shift := Copies B K → B
      Noise := Copies B K × N
      embed := productEmbed i
      embed_injective := productEmbed_injective i hi
      logical := productShift
      logical_surjective := productShift_surjective hdim b₀ hb₀
      output := enlargedOutput C
      equivariant := enlargedOutput_shift C i hC
      noise := fun t => Pi.single t.1 (noise t.2) }

/-- Restriction of a linear observer on the quotient to one base-input copy. -/
def copyObserver {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0)
    (T : StageQuotient.Space (productStage i hi C hC noise hdim b₀ hb₀) →ₗ[ZMod 2] E)
    (L : Copies B K) : V →ₗ[ZMod 2] E :=
  T.comp ((StageQuotient.projection (productStage i hi C hC noise hdim b₀ hb₀)).comp
    (LinearMap.single (R := ZMod 2) (φ := fun _ : Copies B K => V) L))

end UniqueGamesTheorem.Gadget.EnlargementConstruction

end

end

section

/-!
# Detection survives the logical-kernel quotient

A full family of logical characters on the quotient pulls back to a full
lift on the original stage. Its detection event is the same pointwise.
Combining this with the proved left-inverse construction gives detection of
every linear map injective on the quotient's logical subspace.
-/

namespace UniqueGamesTheorem.Gadget.QuotientDetection

open Harmonic DetectionBridge
open scoped Classical

universe u v

variable {k : Type u} {B : Type v} [Field k]
variable [AddCommGroup B] [Module k B] [Finite B]

noncomputable def pullbackFullLift (s : Stage k B)
    (ψ : Module.Dual k B →ₗ[k] Module.Dual k (StageQuotient.Space s))
    (hψ : IsFullLift (StageQuotient.shift s) ψ) :
    Lift s (⊤ : Submodule k (Module.Dual k B)) where
  family :=
    { toFun z := (ψ z.val).comp (StageQuotient.projection s)
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  agrees := by
    intro z h
    change ψ z.val (StageQuotient.projection s (s.embed h)) = z.val (s.logical h)
    rw [← StageQuotient.shift_logical]
    exact hψ z.val (s.logical h)

end UniqueGamesTheorem.Gadget.QuotientDetection

end

section

/-!
# Exact finite-stage nonlinear noise law

This packages the one-level recurrence for the actual recursive `Stage`, solves
it at every height, and proves that the ambient-kernel quotient preserves it.
The averaged block kernel remains an explicit argument for later instantiation
with the concrete quadratic family.
-/

namespace UniqueGamesTheorem.Gadget.StageNoiseRecurrence

open scoped BigOperators

noncomputable def average {A : Type*} [Finite A] (f : A → ℚ) : ℚ :=
  letI := Fintype.ofFinite A
  𝔼 a, f a

universe u v

variable {k : Type u} {B : Type v} [CommRing k] [AddCommGroup B] [Module k B]

/-- Uniform finite input and the stage's actual uniform finite noise choices. -/
noncomputable def error (s : Stage k B) : ℚ := by
  classical
  exact average (fun n : s.Noise => average (fun u : s.Input =>
    if s.output (u + s.noise n) ≠ s.output u then 1 else 0))

end UniqueGamesTheorem.Gadget.StageNoiseRecurrence

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Gadgets_ActualGadgetLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Actual finite binary-vector-space gadgets and their uniform experiments.
The existence statement is the target of the recursive construction, not an
assumed theorem. Noise is indexed by a nonempty finite type; repeated vector
values therefore keep their intended multiplicities. -/

namespace UniqueGamesTheorem.Gadget.ActualGadget

abbrev F2 := ZMod 2

structure Data (C : Type) [AddCommGroup C] [Module F2 C] where
  Ambient : Type
  [ambientAddCommGroup : AddCommGroup Ambient]
  [ambientModule : Module F2 Ambient]
  [ambientFintype : Fintype Ambient]
  embed : C →ₗ[F2] Ambient
  embed_injective : Function.Injective embed
  f : Ambient → C
  equivariant : ∀ x c, f (x + embed c) = f x + c
  NoiseIndex : Type
  [noiseFintype : Fintype NoiseIndex]
  [noiseNonempty : Nonempty NoiseIndex]
  noise : NoiseIndex → Ambient

attribute [instance] Data.ambientAddCommGroup Data.ambientModule Data.ambientFintype
attribute [instance] Data.noiseFintype Data.noiseNonempty

variable {C : Type} [AddCommGroup C] [Module F2 C]

/-- The actual output-change indicator before taking a finite average. -/
noncomputable def failureIndicator (g : Data C) (sample : g.Ambient × g.NoiseIndex) : ℚ := by
  classical
  exact if g.f (sample.1 + g.noise sample.2) = g.f sample.1 then 0 else 1

/-- Uniform ambient input, independently uniform noise-list index. -/
noncomputable def stabilityError (g : Data C) : ℚ :=
  Finset.univ.expect (failureIndicator g)

/-- The actual zero-image event for a linear map. -/
noncomputable def kernelIndicator (g : Data C) {P : Type}
    [AddCommGroup P] [Module F2 P] (S : g.Ambient →ₗ[F2] P) (i : g.NoiseIndex) : ℚ := by
  classical
  exact if S (g.noise i) = 0 then 1 else 0

noncomputable def kernelError (g : Data C) {P : Type}
    [AddCommGroup P] [Module F2 P] (S : g.Ambient →ₗ[F2] P) : ℚ :=
  Finset.univ.expect (kernelIndicator g S)

/-- The stability and dispersion claim of Theorem 3.4 for fixed errors and rank. -/
def Satisfies (g : Data C) (ζ ν : ℚ) (r : Nat) : Prop :=
  stabilityError g ≤ ζ ∧
  ∀ (P : Type) [AddCommGroup P] [Module F2 P] (S : g.Ambient →ₗ[F2] P),
    r ≤ Module.finrank F2 (S.comp g.embed).range → kernelError g S ≤ ν

end UniqueGamesTheorem.Gadget.ActualGadget

end

section

noncomputable section

namespace UniqueGamesTheorem.Gadget.StageData

open scoped BigOperators Classical
open UniqueGamesTheorem.Gadget

variable {C : Type} [AddCommGroup C] [Module (ZMod 2) C]

/-- The normalized stage's actual data, with its original finite noise choices.
Passing the inclusion explicitly avoids dependent casts of the shift carrier. -/
def toData (s : Stage (ZMod 2) C) (embed : C →ₗ[ZMod 2] s.Input)
    (hinj : Function.Injective embed)
    (hEquiv : ∀ u c, s.output (u + embed c) = s.output u + c) : ActualGadget.Data C where
  Ambient := s.Input
  ambientFintype := Fintype.ofFinite s.Input
  embed := embed
  embed_injective := hinj
  f := s.output
  equivariant := hEquiv
  NoiseIndex := s.Noise
  noiseFintype := Fintype.ofFinite s.Noise
  noise := s.noise

end UniqueGamesTheorem.Gadget.StageData

end

end

section

/-!
# Constant-detection enlargement endpoint

The finite base alphabet and its rank threshold are fixed before the target
logical space. The resulting actual gadget has the same nonlinear error and
linear kernel error at most `7/8`.
-/

noncomputable section

namespace UniqueGamesTheorem.Gadget.EnlargementEndpoint

open scoped Classical
open Enlargement EnlargementConstruction
open UniqueGamesTheorem.Gadget

variable {B K V N : Type}
variable [AddCommGroup B] [Module (ZMod 2) B] [Fintype B]
variable [FiniteDimensional (ZMod 2) B]
variable [AddCommGroup K] [Module (ZMod 2) K] [Fintype K]
variable [FiniteDimensional (ZMod 2) K]
variable [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable [Fintype N] [Nonempty N]

def data (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0) : ActualGadget.Data K :=
  let s := productStage i hi C hC noise hdim b₀ hb₀
  StageData.toData (StageQuotient.toStage s) (StageQuotient.shift s)
    (StageQuotient.shift_injective s) (StageQuotient.output_equivariant s)

end UniqueGamesTheorem.Gadget.EnlargementEndpoint

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_Block
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Quadratic

abbrev Vec (F : Type*) := Fin 3 → F

variable {F : Type*} [Field F]

/-- The three-coordinate quadratic block from equation (2.4). -/
def Q (x : Vec F) : Vec F := ![x 1 * x 2, x 0 * x 2, x 0 * x 1]

/-- Its polar cross-terms.  In characteristic two these equal
`Q (x + a) + Q x + Q a`. -/
def D (x a : Vec F) : Vec F :=
  ![x 1 * a 2 + a 1 * x 2, x 0 * a 2 + a 0 * x 2,
    x 0 * a 1 + a 0 * x 1]

/-- Field dot product, with all three coordinates displayed. -/
def dot (v y : Vec F) : F := v 0 * y 0 + v 1 * y 1 + v 2 * y 2

@[simp] theorem Q_zero : Q (0 : Vec F) = 0 := by
  ext i
  fin_cases i <;> simp [Q]

theorem Q_add (x a : Vec F) : Q (x + a) = Q x + Q a + D x a := by
  ext i
  fin_cases i <;> simp [Q, D] <;> ring

@[simp] theorem D_zero_left (a : Vec F) : D 0 a = 0 := by
  ext i
  fin_cases i <;> simp [D]

@[simp] theorem D_zero_right (x : Vec F) : D x 0 = 0 := by
  ext i
  fin_cases i <;> simp [D]

@[simp] theorem dot_zero_right (v : Vec F) : dot v 0 = 0 := by simp [dot]
@[simp] theorem dot_zero_left (y : Vec F) : dot 0 y = 0 := by simp [dot]

theorem dot_add_right (v y z : Vec F) : dot v (y + z) = dot v y + dot v z := by
  simp [dot]
  ring

theorem dot_smul_right (v y : Vec F) (t : F) : dot v (t • y) = t * dot v y := by
  simp [dot, smul_eq_mul]
  ring

theorem dot_smul_left (v y : Vec F) (t : F) : dot (t • v) y = t * dot v y := by
  simp [dot, smul_eq_mul]
  ring

/-- The field line generated by `v`. -/
def line (v : Vec F) : Submodule F (Vec F) := Submodule.span F {v}

/-- The field hyperplane perpendicular to the generator of the line. -/
def hyperplane (v : Vec F) : Submodule F (Vec F) where
  carrier := {y | dot v y = 0}
  zero_mem' := dot_zero_right v
  add_mem' := by
    intro y z hy hz
    rw [Set.mem_ofPred_eq, dot_add_right, hy, hz, add_zero]
  smul_mem' := by
    intro t y hy
    rw [Set.mem_ofPred_eq, dot_smul_right, hy, mul_zero]

@[simp] theorem mem_hyperplane (v y : Vec F) : y ∈ hyperplane v ↔ dot v y = 0 := Iff.rfl

theorem mem_line_iff (v a : Vec F) : a ∈ line v ↔ ∃ t : F, t • v = a :=
  Submodule.mem_span_singleton

section CharacteristicTwo

variable [CharP F 2]

@[simp] theorem vec_add_self (x : Vec F) : x + x = 0 := by
  ext i
  exact CharTwo.add_self_eq_zero (x i)

theorem cross_self_zero (u w s t : F) :
    (t * u) * (s * w) + (s * u) * (t * w) = 0 := by
  calc
    _ = (t * s * u * w) + (t * s * u * w) := by ring
    _ = 0 := CharTwo.add_self_eq_zero _

/-- The polar expression vanishes on any pair of vectors in the same field line. -/
theorem D_smul_smul_zero (v : Vec F) (t s : F) : D (t • v) (s • v) = 0 := by
  ext i
  fin_cases i <;> simp [D, smul_eq_mul, cross_self_zero]

/-- Every cross-term arising from a shift along `Fv` is perpendicular to `v`. -/
theorem dot_D_smul (v x : Vec F) (t : F) : dot v (D x (t • v)) = 0 := by
  change v 0 * (x 1 * (t * v 2) + (t * v 1) * x 2) +
      v 1 * (x 0 * (t * v 2) + (t * v 0) * x 2) +
      v 2 * (x 0 * (t * v 1) + (t * v 0) * x 1) = 0
  calc
    _ = (t * (v 0 * v 2 * x 1 + v 0 * v 1 * x 2 + v 1 * v 2 * x 0)) +
        (t * (v 0 * v 2 * x 1 + v 0 * v 1 * x 2 + v 1 * v 2 * x 0)) := by ring
    _ = 0 := CharTwo.add_self_eq_zero _

theorem D_mem_hyperplane (v x a : Vec F) (ha : a ∈ line v) :
    D x a ∈ hyperplane v := by
  obtain ⟨t, rfl⟩ := (mem_line_iff v a).mp ha
  exact dot_D_smul v x t

theorem D_eq_zero_of_mem_line (v a b : Vec F)
    (ha : a ∈ line v) (hb : b ∈ line v) : D a b = 0 := by
  obtain ⟨t, rfl⟩ := (mem_line_iff v a).mp ha
  obtain ⟨s, rfl⟩ := (mem_line_iff v b).mp hb
  exact D_smul_smul_zero v t s

/-- The restriction of the quadratic map to one field line is additive. -/
theorem Q_add_of_mem_line (v a b : Vec F)
    (ha : a ∈ line v) (hb : b ∈ line v) : Q (a + b) = Q a + Q b := by
  rw [Q_add, D_eq_zero_of_mem_line v a b ha hb, add_zero]

variable [Algebra (ZMod 2) F]

/-- The block space `U_A`, as an actual binary submodule.  Membership uses
`y + Q a` because subtraction equals addition in characteristic two. -/
def U (v : Vec F) : Submodule (ZMod 2) (Vec F × Vec F) where
  carrier := {p | p.1 ∈ line v ∧ dot v (p.2 + Q p.1) = 0}
  zero_mem' := by simp [Q_zero]
  add_mem' := by
    intro p q hp hq
    refine ⟨(line v).add_mem hp.1 hq.1, ?_⟩
    change dot v ((p.2 + q.2) + Q (p.1 + q.1)) = 0
    rw [Q_add_of_mem_line v p.1 q.1 hp.1 hq.1]
    have h : (p.2 + q.2) + (Q p.1 + Q q.1) =
        (p.2 + Q p.1) + (q.2 + Q q.1) := by ac_rfl
    rw [h, dot_add_right, hp.2, hq.2, add_zero]
  smul_mem' := by
    intro c p hp
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl
    · simp [Q_zero]
    · simpa using hp

@[simp] theorem mem_U (v : Vec F) (p : Vec F × Vec F) :
    p ∈ U v ↔ p.1 ∈ line v ∧ dot v (p.2 + Q p.1) = 0 := Iff.rfl

theorem pair_mem_U (v a w : Vec F) (ha : a ∈ line v) (hw : w ∈ hyperplane v) :
    (a, Q a + w) ∈ U v := by
  refine ⟨ha, ?_⟩
  change dot v (Q a + w + Q a) = 0
  have h : Q a + w + Q a = w + (Q a + Q a) := by ac_rfl
  simpa [h] using hw

end CharacteristicTwo
end UniqueGamesTheorem.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_BlockCounting
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact field-line count for the quadratic block's erasure probability. -/

namespace UniqueGamesTheorem.Quadratic

/-- Actual one-dimensional field directions, with proportional nonzero
vectors identified. -/
abbrev FieldLine (F : Type*) [Field F] := Projectivization F (Vec F)

variable {F : Type*} [Field F]

/-- A chosen nonzero generator, only used with generator-independent data. -/
noncomputable def lineGenerator (A : FieldLine F) : Vec F := A.rep

theorem lineGenerator_ne_zero (A : FieldLine F) : lineGenerator A ≠ 0 :=
  A.rep_nonzero

theorem line_lineGenerator (A : FieldLine F) : line (lineGenerator A) = A.submodule :=
  A.submodule_eq.symm

variable [Finite F]

/-- The denominator of the block erasure probability is exactly `q²+q+1`. -/
theorem card_FieldLine : Nat.card (FieldLine F) = Nat.card F ^ 2 + Nat.card F + 1 := by
  have h := Projectivization.card_of_finrank F (Vec F) (n := 3)
    (Module.finrank_fin_fun (R := F))
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one, add_comm, add_left_comm, add_assoc] using h

theorem card_FieldLine_pos : 0 < Nat.card (FieldLine F) := by
  rw [card_FieldLine]
  exact Nat.succ_pos _

end UniqueGamesTheorem.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_BlockDimension
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The binary-linear parametrization and dimension of the v2 quadratic block. -/

namespace UniqueGamesTheorem.Quadratic

variable {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]

abbrev lineBinary (v : Vec F) : Submodule (ZMod 2) (Vec F) :=
  (line v).restrictScalars (ZMod 2)

abbrev hyperplaneBinary (v : Vec F) : Submodule (ZMod 2) (Vec F) :=
  (hyperplane v).restrictScalars (ZMod 2)

omit [Algebra (ZMod 2) F] in
theorem Q_cancel (a w : Vec F) : Q a + (w + Q a) = w := by
  calc
    _ = w + (Q a + Q a) := by ac_rfl
    _ = w := by rw [vec_add_self, add_zero]

/-- The parametrization `(a,w) ↦ (a,Q(a)+w)` is a binary-linear bijection.
It is not asserted to be field-linear: squaring along a field line is only
binary-linear. -/
def blockParametrization (v : Vec F) :
    (lineBinary v × hyperplaneBinary v) ≃ₗ[ZMod 2] U v where
  toFun p := ⟨((p.1 : Vec F), Q (p.1 : Vec F) + (p.2 : Vec F)),
    pair_mem_U v p.1 p.2 p.1.2 p.2.2⟩
  invFun p := (⟨p.1.1, p.2.1⟩, ⟨p.1.2 + Q p.1.1, p.2.2⟩)
  left_inv := by
    intro p
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      change Q (p.1 : Vec F) + (p.2 : Vec F) + Q (p.1 : Vec F) = p.2
      have h : Q (p.1 : Vec F) + (p.2 : Vec F) + Q (p.1 : Vec F) =
          Q (p.1 : Vec F) + ((p.2 : Vec F) + Q (p.1 : Vec F)) := by rw [add_assoc]
      rw [h, Q_cancel]
  right_inv := by
    intro p
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact Q_cancel p.1.1 p.1.2
  map_add' := by
    intro p q
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change Q ((p.1 : Vec F) + (q.1 : Vec F)) + ((p.2 : Vec F) + (q.2 : Vec F)) =
        (Q (p.1 : Vec F) + (p.2 : Vec F)) + (Q (q.1 : Vec F) + (q.2 : Vec F))
      rw [Q_add_of_mem_line v p.1 q.1 p.1.2 q.1.2]
      ac_rfl
  map_smul' := by
    intro c p
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl
    · apply Subtype.ext
      apply Prod.ext <;> simp [Q_zero]
    · simp

/-- The dot-product functional over the large field. -/
def dotLinear (v : Vec F) : Vec F →ₗ[F] F where
  toFun := dot v
  map_add' := dot_add_right v
  map_smul' := by intro t y; exact dot_smul_right v y t

omit [CharP F 2] [Algebra (ZMod 2) F] in
@[simp] theorem dotLinear_apply (v y : Vec F) : dotLinear v y = dot v y := rfl

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem dotLinear_ker (v : Vec F) : LinearMap.ker (dotLinear v) = hyperplane v := rfl

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem dotLinear_surjective (v : Vec F) (hv : v ≠ 0) :
    Function.Surjective (dotLinear v) := by
  classical
  have hi : ∃ i : Fin 3, v i ≠ 0 := by
    by_cases h : ∀ i, v i = 0
    · exact False.elim (hv (funext h))
    · exact not_forall.mp h
  obtain ⟨i, hi⟩ := hi
  intro z
  refine ⟨Pi.single i (z / v i), ?_⟩
  have hsingle (j : Fin 3) (a : F) : dot v (Pi.single j a) = v j * a := by
    fin_cases j <;> simp [dot]
  change dot v (Pi.single i (z / v i)) = z
  rw [hsingle]
  calc
    v i * (z / v i) = (v i * (v i)⁻¹) * z := by ring
    _ = z := by rw [mul_inv_cancel₀ hi, one_mul]

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem finrank_hyperplane (v : Vec F) (hv : v ≠ 0) :
    Module.finrank F (hyperplane v) = 2 := by
  have h := (dotLinear v).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (dotLinear_surjective v hv),
    finrank_top, Module.finrank_self, dotLinear_ker,
    Module.finrank_fin_fun] at h
  omega

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem finrank_line (v : Vec F) (hv : v ≠ 0) :
    Module.finrank F (line v) = 1 :=
  finrank_span_singleton hv

variable [FiniteDimensional (ZMod 2) F]

omit [CharP F 2] [FiniteDimensional (ZMod 2) F] in
theorem finrank_lineBinary (v : Vec F) (hv : v ≠ 0) :
    Module.finrank (ZMod 2) (lineBinary v) = Module.finrank (ZMod 2) F := by
  rw [← Module.finrank_mul_finrank (ZMod 2) F (lineBinary v),
    ((line v).restrictScalarsEquiv (ZMod 2)).finrank_eq, finrank_line v hv, mul_one]

omit [CharP F 2] [FiniteDimensional (ZMod 2) F] in
theorem finrank_hyperplaneBinary (v : Vec F) (hv : v ≠ 0) :
    Module.finrank (ZMod 2) (hyperplaneBinary v) = 2 * Module.finrank (ZMod 2) F := by
  rw [← Module.finrank_mul_finrank (ZMod 2) F (hyperplaneBinary v),
    ((hyperplane v).restrictScalarsEquiv (ZMod 2)).finrank_eq, finrank_hyperplane v hv,
    mul_comm]

/-- If the field has binary dimension `d`, every nonzero-generator block has
binary dimension `3d`, the dimension of its input/output alphabet. -/
theorem finrank_U (v : Vec F) (hv : v ≠ 0) :
    Module.finrank (ZMod 2) (U v) = 3 * Module.finrank (ZMod 2) F := by
  rw [← (blockParametrization v).finrank_eq, Module.finrank_prod,
    finrank_lineBinary v hv, finrank_hyperplaneBinary v hv]
  omega

theorem finrank_U_eq_finrank_vec (v : Vec F) (hv : v ≠ 0) :
    Module.finrank (ZMod 2) (U v) = Module.finrank (ZMod 2) (Vec F) := by
  rw [finrank_U v hv, ← Module.finrank_mul_finrank (ZMod 2) F (Vec F),
    Module.finrank_fin_fun, mul_comm]

end UniqueGamesTheorem.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_BlockNoise
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Exact nonlinear change count for a quadratic block

For every fixed input, a shear of the line/hyperplane parametrization makes
the output difference the hyperplane coordinate. This proves the uniform
change count before any recursion or random orientation is introduced.
-/

namespace UniqueGamesTheorem.Quadratic

variable {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The block's nonlinear observable. -/
def blockObservable (p : Vec F × Vec F) : Vec F := p.2 + Q p.1

omit [Algebra (ZMod 2) F] in
theorem blockObservable_difference (p u : Vec F × Vec F) :
    blockObservable (p + u) + blockObservable p =
      u.2 + Q u.1 + D p.1 u.1 := by
  change (p.2 + u.2) + Q (p.1 + u.1) + (p.2 + Q p.1) = _
  rw [Q_add]
  calc
    _ = u.2 + Q u.1 + D p.1 u.1 + (p.2 + p.2) + (Q p.1 + Q p.1) := by
      ac_rfl
    _ = _ := by rw [vec_add_self, vec_add_self, add_zero, add_zero]

/-- Translation by the polar term permutes the vertical hyperplane. -/
def hyperplaneNoiseShift (v x a : Vec F) (ha : a ∈ line v) :
    hyperplane v ≃ hyperplane v where
  toFun w := ⟨(w : Vec F) + D x a,
    (hyperplane v).add_mem w.property (D_mem_hyperplane v x a ha)⟩
  invFun w := ⟨(w : Vec F) + D x a,
    (hyperplane v).add_mem w.property (D_mem_hyperplane v x a ha)⟩
  left_inv w := by
    apply Subtype.ext
    change ((w : Vec F) + D x a) + D x a = w
    rw [add_assoc, vec_add_self, add_zero]
  right_inv w := by
    apply Subtype.ext
    change ((w : Vec F) + D x a) + D x a = w
    rw [add_assoc, vec_add_self, add_zero]

/-- The polar shear preserves the first coordinate and is its own inverse. -/
def noiseParameterShift (v x : Vec F) :
    (lineBinary v × hyperplaneBinary v) ≃ (lineBinary v × hyperplaneBinary v) where
  toFun p := (p.1, hyperplaneNoiseShift v x p.1 p.1.property p.2)
  invFun p := (p.1, hyperplaneNoiseShift v x p.1 p.1.property p.2)
  left_inv p := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change ((p.2 : Vec F) + D x p.1) + D x p.1 = p.2
      rw [add_assoc, vec_add_self, add_zero]
  right_inv p := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change ((p.2 : Vec F) + D x p.1) + D x p.1 = p.2
      rw [add_assoc, vec_add_self, add_zero]

/-- Coordinates in which the nonlinear output difference is just the second
coordinate, for every fixed input `x`. -/
def blockNoiseCoordinates (v x : Vec F) : U v ≃ (lineBinary v × hyperplaneBinary v) :=
  (blockParametrization v).toEquiv.symm.trans (noiseParameterShift v x)

theorem blockObservable_difference_eq_noiseCoordinate
    (v : Vec F) (p : Vec F × Vec F) (u : U v) :
    blockObservable (p + (u : Vec F × Vec F)) + blockObservable p =
      ((blockNoiseCoordinates v p.1 u).2 : Vec F) :=
  blockObservable_difference p u

omit [Algebra (ZMod 2) F] in
theorem vec_add_eq_zero_iff (x y : Vec F) : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    have h' := congrArg (fun z : Vec F => z + y) h
    simpa only [add_assoc, vec_add_self, add_zero, zero_add] using h'
  · rintro rfl
    exact vec_add_self _

theorem blockObservable_changes_iff (v : Vec F) (p : Vec F × Vec F) (u : U v) :
    blockObservable (p + (u : Vec F × Vec F)) ≠ blockObservable p ↔
      (blockNoiseCoordinates v p.1 u).2 ≠ 0 := by
  apply not_congr
  rw [← vec_add_eq_zero_iff, blockObservable_difference_eq_noiseCoordinate]
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    exact congrArg (fun w : hyperplaneBinary v => (w : Vec F)) h

theorem blockObservable_change_ne_zero (v : Vec F) (p : Vec F × Vec F) (u : U v)
    (h : blockObservable (p + (u : Vec F × Vec F)) ≠ blockObservable p) : u ≠ 0 := by
  intro hu
  subst u
  exact h (by simp)

/-- Changed perturbations correspond exactly to an arbitrary line coordinate
and a nonzero hyperplane coordinate. In particular this is uniform in `p`. -/
def changedCoordinatesEquiv (v : Vec F) (p : Vec F × Vec F) :
    {u : U v // blockObservable (p + (u : Vec F × Vec F)) ≠ blockObservable p} ≃
      (lineBinary v × {w : hyperplaneBinary v // w ≠ 0}) :=
  ((blockNoiseCoordinates v p.1).subtypeEquiv
    (p := fun u : U v =>
      blockObservable (p + (u : Vec F × Vec F)) ≠ blockObservable p)
    (q := fun u : lineBinary v × hyperplaneBinary v => u.2 ≠ 0)
    (fun u => blockObservable_changes_iff v p u)).trans
    { toFun := fun u => (u.1.1, ⟨u.1.2, u.2⟩)
      invFun := fun u => ⟨(u.1, u.2.1), u.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end UniqueGamesTheorem.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_BlockNoiseProbabilityLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact rational expectation for the quadratic block's conditioned noise. -/

namespace UniqueGamesTheorem.Quadratic

open scoped BigOperators

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The uniform noise space after conditioning the perturbation to be nonzero. -/
abbrev NonzeroBlock (v : Vec F) := {u : U v // u ≠ 0}

/-- Exact uniform expectation of the nonlinear-change indicator. -/
def nonzeroBlockChangeProbability (v : Vec F) (p : Vec F × Vec F) : ℚ := by
  classical
  exact Finset.univ.expect fun u : NonzeroBlock v =>
    if blockObservable (p + (u.val : Vec F × Vec F)) ≠ blockObservable p then 1 else 0

/-- The zero perturbation is never a changed perturbation, so conditioning
does not remove any element from the change event. -/
def conditionedChangedEquiv (v : Vec F) (p : Vec F × Vec F) :
    {u : NonzeroBlock v //
      blockObservable (p + (u.val : Vec F × Vec F)) ≠ blockObservable p} ≃
    {u : U v // blockObservable (p + (u : Vec F × Vec F)) ≠ blockObservable p} where
  toFun u := ⟨u.val.val, u.property⟩
  invFun u := ⟨⟨u.val, blockObservable_change_ne_zero v p u.val u.property⟩, u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

end

end UniqueGamesTheorem.Quadratic

end

section

namespace UniqueGamesTheorem.Quadratic

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- An orientation identifies the common binary alphabet with a line's block. -/
abbrev BlockOrientation (A : FieldLine F) :=
  Vec F ≃ₗ[ZMod 2] U (lineGenerator A)

noncomputable instance fieldLineFintype : Fintype (FieldLine F) := Fintype.ofFinite _

instance finiteBlockOrientation (A : FieldLine F) : Finite (BlockOrientation A) :=
  DFunLike.finite _

noncomputable instance blockOrientationFintype (A : FieldLine F) :
    Fintype (BlockOrientation A) := Fintype.ofFinite _

/-- Existence uses the proved dimension of the actual quadratic block. -/
noncomputable def chosenBlockOrientation (A : FieldLine F) : BlockOrientation A :=
  LinearEquiv.ofFinrankEq (Vec F) (U (lineGenerator A))
    (finrank_U_eq_finrank_vec (lineGenerator A) (lineGenerator_ne_zero A)).symm

/-- Composing with one fixed orientation identifies all orientations with
automorphisms of the common binary alphabet. -/
noncomputable def blockOrientationEquiv (A : FieldLine F) :
    BlockOrientation A ≃ (Vec F ≃ₗ[ZMod 2] Vec F) where
  toFun J := J.trans (chosenBlockOrientation A).symm
  invFun J := J.trans (chosenBlockOrientation A)
  left_inv J := by
    apply LinearEquiv.ext
    intro x
    exact (chosenBlockOrientation A).apply_symm_apply (J x)
  right_inv J := by
    apply LinearEquiv.ext
    intro x
    exact (chosenBlockOrientation A).symm_apply_apply (J x)

abbrev BlockOrientationIndex (F : Type*) [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] := Σ A : FieldLine F, BlockOrientation A

noncomputable def blockOrientationIndexEquiv :
    BlockOrientationIndex F ≃ FieldLine F × (Vec F ≃ₗ[ZMod 2] Vec F) where
  toFun p := (p.1, blockOrientationEquiv p.1 p.2)
  invFun p := ⟨p.1, (blockOrientationEquiv p.1).symm p.2⟩
  left_inv := by
    rintro ⟨A, J⟩
    simp
  right_inv := by
    rintro ⟨A, J⟩
    simp

end UniqueGamesTheorem.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Gadgets_OrientedBlockKernel
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

open scoped BigOperators

namespace UniqueGamesTheorem.Gadget.OrientedBlockKernel

open Quadratic

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The actual binary-linear embedding belonging to an oriented child. -/
def orientedBlockLinear (i : BlockOrientationIndex F) :
    Vec F →ₗ[ZMod 2] Vec F × Vec F :=
  (U (lineGenerator i.1)).subtype.comp i.2.toLinearMap

/-- The nonlinear-change indicator for the actual oriented quadratic block. -/
def orientedBlockChange (i : BlockOrientationIndex F) (p : Vec F × Vec F)
    (d : Vec F) : ℚ := by
  classical
  exact if blockObservable (p + orientedBlockLinear i d) ≠ blockObservable p then 1 else 0

end UniqueGamesTheorem.Gadget.OrientedBlockKernel

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_Alignment
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Quadratic

open Module
open scoped BigOperators Matrix

noncomputable section

variable {R F V ι n E : Type*}
variable [Field R] [Field F] [Algebra R F]
variable [AddCommGroup V] [Module R V]
variable [Fintype ι] [Fintype n]

/-- The `|n| * |ι|` alignment columns for a fixed parametrization and input set.
The input set is represented by any map `point : E → V`; no injectivity is
needed for the exact algebraic equivalence. -/
def alignmentMatrix (b : Basis ι R V) (point : E → V) (z : V → n → F) :
    Matrix E (n × ι) F :=
  fun e ij => algebraMap R F (b.repr (point e) ij.2) * z (point e) ij.1

end

end UniqueGamesTheorem.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_BlockSpanLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The spanning clause of Lemma `latent-block`.  Three coordinate lines
already suffice.  Horizontal coordinate vectors lie in their own block;
vertical coordinate vectors lie in either of the other two blocks.
-/

namespace UniqueGamesTheorem.Quadratic

variable {F : Type*} [Field F]

/-- The three standard coordinate vectors of the quadratic block. -/
def basisCoord (i : Fin 3) : Vec F := Pi.single i 1

theorem basisCoord_ne_zero (i : Fin 3) : (basisCoord i : Vec F) ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp [basisCoord] at hi

@[simp] theorem Q_smul_basisCoord (t : F) (i : Fin 3) :
    Q (t • (basisCoord i : Vec F)) = 0 := by
  ext k
  fin_cases i <;> fin_cases k <;> simp [Q, basisCoord]

theorem dot_smul_basisCoord_of_ne (t : F) (i j : Fin 3) (hij : i ≠ j) :
    dot (basisCoord j : Vec F) (t • (basisCoord i : Vec F)) = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [dot, basisCoord]

variable [CharP F 2] [Algebra (ZMod 2) F]

theorem horizontal_mem_U_basisCoord (t : F) (i : Fin 3) :
    (t • basisCoord i, (0 : Vec F)) ∈ U (basisCoord i) := by
  refine ⟨(mem_line_iff _ _).mpr ⟨t, rfl⟩, ?_⟩
  change dot (basisCoord i) (0 + Q (t • basisCoord i)) = 0
  simp

theorem vertical_mem_U_basisCoord_of_ne (t : F) (i j : Fin 3) (hij : i ≠ j) :
    ((0 : Vec F), t • basisCoord i) ∈ U (basisCoord j) := by
  refine ⟨(line _).zero_mem, ?_⟩
  change dot (basisCoord j) (t • basisCoord i + Q 0) = 0
  simpa using dot_smul_basisCoord_of_ne t i j hij

/-- The binary span of the three coordinate block spaces. -/
def coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F) :=
  (U (basisCoord 0) ⊔ U (basisCoord 1)) ⊔ U (basisCoord 2)

theorem U_basisCoord_le_coordinateBlockSpan (i : Fin 3) :
    U (basisCoord i) ≤ (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) := by
  fin_cases i
  · exact le_trans le_sup_left le_sup_left
  · exact le_trans le_sup_right le_sup_left
  · exact le_sup_right

theorem horizontal_mem_coordinateBlockSpan (t : F) (i : Fin 3) :
    (t • basisCoord i, (0 : Vec F)) ∈
      (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) :=
  U_basisCoord_le_coordinateBlockSpan i (horizontal_mem_U_basisCoord t i)

theorem vertical_mem_coordinateBlockSpan (t : F) (i : Fin 3) :
    ((0 : Vec F), t • basisCoord i) ∈
      (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) := by
  have h (j : Fin 3) (hij : i ≠ j) :
      ((0 : Vec F), t • basisCoord i) ∈
        (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) :=
    U_basisCoord_le_coordinateBlockSpan j (vertical_mem_U_basisCoord_of_ne t i j hij)
  fin_cases i
  · exact h 1 (by decide)
  · exact h 0 (by decide)
  · exact h 0 (by decide)

/-- Every pair is a sum of three horizontal and three vertical coordinate
pairs, all already in the sum of the coordinate blocks. -/
theorem mem_coordinateBlockSpan (p : Vec F × Vec F) :
    p ∈ (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) := by
  let S : Submodule (ZMod 2) (Vec F × Vec F) := coordinateBlockSpan
  have hh : (p.1, (0 : Vec F)) ∈ S := by
    have h := S.add_mem
      (S.add_mem (horizontal_mem_coordinateBlockSpan (p.1 0) 0)
        (horizontal_mem_coordinateBlockSpan (p.1 1) 1))
      (horizontal_mem_coordinateBlockSpan (p.1 2) 2)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ext i <;> fin_cases i <;> simp [basisCoord]
  have hv : ((0 : Vec F), p.2) ∈ S := by
    have h := S.add_mem
      (S.add_mem (vertical_mem_coordinateBlockSpan (p.2 0) 0)
        (vertical_mem_coordinateBlockSpan (p.2 1) 1))
      (vertical_mem_coordinateBlockSpan (p.2 2) 2)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ext i <;> fin_cases i <;> simp [basisCoord]
  have h := S.add_mem hh hv
  simpa only [Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta] using h

theorem coordinateBlockSpan_eq_top :
    (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) = ⊤ := by
  apply top_unique
  intro p _
  exact mem_coordinateBlockSpan p

/-- The block spaces for all nonzero line generators span the whole ambient
binary vector space.  The proof uses just the three coordinate generators. -/
theorem iSup_U_nonzero_eq_top :
    (⨆ v : {v : Vec F // v ≠ 0}, U v.1) = ⊤ := by
  apply top_unique
  rw [← coordinateBlockSpan_eq_top (F := F)]
  unfold coordinateBlockSpan
  refine sup_le (sup_le ?_ ?_) ?_
  · exact le_iSup (fun v : {v : Vec F // v ≠ 0} => U v.1)
      ⟨basisCoord 0, basisCoord_ne_zero 0⟩
  · exact le_iSup (fun v : {v : Vec F // v ≠ 0} => U v.1)
      ⟨basisCoord 1, basisCoord_ne_zero 1⟩
  · exact le_iSup (fun v : {v : Vec F // v ≠ 0} => U v.1)
      ⟨basisCoord 2, basisCoord_ne_zero 2⟩

end UniqueGamesTheorem.Quadratic

end

section

namespace UniqueGamesTheorem.Quadratic

open scoped BigOperators

/-- Degree-two evaluation space. Repeated indices are allowed, so on binary
points this also contains every degree-one evaluation. -/
def quadraticEvaluationSpan {F X I : Type*} [Field F]
    (c : I → X → F) : Submodule F (X → F) :=
  Submodule.span F (Set.range fun ij : I × I => fun x => c ij.1 x * c ij.2 x)

/-- Degree-three evaluation space. Repeated indices recover all lower
positive degrees on binary points. -/
def cubicEvaluationSpan {F X I : Type*} [Field F]
    (c : I → X → F) : Submodule F (X → F) :=
  Submodule.span F
    (Set.range fun ijk : I × I × I => fun x => c ijk.1 x * c ijk.2.1 x * c ijk.2.2 x)

end UniqueGamesTheorem.Quadratic

end

section

/-!
A concrete mathematical family of finite binary fields of unbounded size.
The extension degree is chosen from numerical thresholds alone, before the
logical output dimension of the latent gadget is selected.
-/

namespace UniqueGamesTheorem.Quadratic

/-- The degree-`d` binary Galois field.  Cardinality statements below require
`d > 0`; the degenerate exponent zero is deliberately excluded. -/
abbrev BinaryField (d : ℕ) := GaloisField 2 d

/-- A deliberately simple explicit upper choice; optimization of the field
size is irrelevant because these thresholds are fixed before the input. -/
def fieldDegree (cardThreshold rankThreshold : ℕ) : ℕ :=
  cardThreshold + rankThreshold + 1

end UniqueGamesTheorem.Quadratic

end

section

/-!
# Separation of polynomial parity classes

The genericity argument uses monomials with distinct squarefree
exponent vectors. Polynomial coefficients in the original variables become
polynomials in squares after adjoining their square roots. The lemmas below
prove the resulting coefficient separation directly, without assuming an
algebraic independence witness.
-/

namespace UniqueGamesTheorem.Quadratic

open MvPolynomial
open scoped BigOperators

variable {σ ι R : Type*} [CommSemiring R]

/-- Exponents zero or one represent parity classes. -/
def SquarefreeExponent (a : σ →₀ ℕ) : Prop := ∀ k, a k < 2

noncomputable def blockExponent {κ J : Type*} [Finite κ] [Finite J]
    (v : κ → J) : (κ × J) →₀ ℕ := by
  classical
  exact Finsupp.equivFunOnFinite.symm (fun x => if x.2 = v x.1 then 1 else 0)

@[simp] theorem blockExponent_apply {κ J : Type*} [Finite κ] [Finite J] [DecidableEq J]
    (v : κ → J) (x : κ × J) :
    blockExponent v x = if x.2 = v x.1 then 1 else 0 := by
  classical
  by_cases h : x.2 = v x.1 <;> simp [blockExponent, h]

end UniqueGamesTheorem.Quadratic

end

section

/-!
# Polynomial parity obstruction

This supplies the algebraic obstruction step in the genericity proof.
Squaring a cleared dual row exposes its distinct squarefree parity classes.
No genericity or minor-existence conclusion is assumed here.
-/

namespace UniqueGamesTheorem.Quadratic

open MvPolynomial
open scoped BigOperators
open scoped nonZeroDivisors

variable {σ : Type*}

section Obstruction

variable {J X : Type*} [Fintype J] [Fintype X]

/-- The universal coordinate `z_i(t)` with the `x_ij` as indeterminates. -/
noncomputable def universalLinearForm (t : J → ZMod 2) (i : Fin 3) :
    MvPolynomial (Fin 3 × J) (ZMod 2) :=
  ∑ j, C (t j) * MvPolynomial.X (i, j)

/-- Polynomial alignment columns; every lift is one linear combination of
these columns. -/
noncomputable def universalAlignmentColumn (t : X → J → ZMod 2)
    (ij : Fin 3 × J) (x : X) : MvPolynomial (Fin 3 × J) (ZMod 2) :=
  C (t x ij.2) * universalLinearForm (t x) ij.1

/-- Coefficient obtained by pairing a polynomial row with a cubic binary
evaluation. -/
noncomputable def cubicPairing (t : X → J → ZMod 2)
    (p : X → MvPolynomial (Fin 3 × J) (ZMod 2)) (v : Fin 3 → J) :
    MvPolynomial (Fin 3 × J) (ZMod 2) :=
  ∑ x, p x * C (∏ i, t x (v i))

/-- Clearing the rational dual's denominator and squaring gives this one
polynomial obstruction to simultaneous alignment. Its degree is finite and
depends only on the fixed set of inputs. -/
noncomputable def alignmentObstruction (t : X → J → ZMod 2)
    (p : X → MvPolynomial (Fin 3 × J) (ZMod 2)) :
    MvPolynomial (Fin 3 × J) (ZMod 2) :=
  ∑ x, p x ^ 2 * ∏ i, universalLinearForm (t x) i

end Obstruction

end UniqueGamesTheorem.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_GenericSeparationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Polynomial obstructions to collapsed or proportional binary inputs

One linear polynomial detects each nonzero input. One quadratic polynomial
detects each pair of distinct nonzero binary inputs. The witnesses are proved
nonzero by explicit coordinate-selector evaluations. Together with the
alignment obstruction they yield a finite product whose zero set contains
every failure of genericity. An `O_r(1/q)` bound suffices here.
-/

namespace UniqueGamesTheorem.Quadratic

open MvPolynomial

section Polynomial

variable {J : Type*} [Fintype J]

/-- Set the first two rows of the indeterminate matrix to coordinate
selectors. The third row is zero. -/
noncomputable def selectorAssignment (j k : J) : (Fin 3 × J) → ZMod 2 := by
  classical
  exact fun x => if x.1 = 0 then (if x.2 = j then 1 else 0)
    else if x.1 = 1 then (if x.2 = k then 1 else 0) else 0

/-- A two-row determinant, with subtraction equal to addition in
characteristic two. -/
noncomputable def universalPairMinor (t u : J → ZMod 2) :
    MvPolynomial (Fin 3 × J) (ZMod 2) :=
  universalLinearForm t 0 * universalLinearForm u 1 +
    universalLinearForm t 1 * universalLinearForm u 0

end Polynomial

end UniqueGamesTheorem.Quadratic

end

section

/-!
# Finite-field polynomial exceptional events

The nonzero polynomial obstruction for each fixed input set gives a uniform
bound over all linear lifts.  Its coefficients lie in the binary prime field,
so its degree is fixed before the extension field is chosen.  The theorems
below keep this order explicit and combine finitely many obstructions without
any union over maps.
-/

namespace UniqueGamesTheorem.Quadratic

open scoped BigOperators

noncomputable section

variable {K F : Type*} [Field K] [Field F] [Fintype F]

/-- The exact uniform probability on an explicit finite assignment space. -/
def assignmentProbability {n : ℕ} (event : (Fin n → F) → Prop) : ℚ≥0 := by
  classical
  exact ((Finset.univ.filter event).card : ℚ≥0) / (Fintype.card F : ℚ≥0) ^ n

end

end UniqueGamesTheorem.Quadratic

end

section

/-!
# Polynomial exceptional events on arbitrary finite variable sets

Reindexing the variable set transports both the polynomial and the uniform
assignment space. Thus the checked finite-field zero bound applies directly
to the three-by-r variables in the genericity proof, without changing the
degree or taking a union over possible linear lifts.
-/

namespace UniqueGamesTheorem.Quadratic

open scoped BigOperators

noncomputable section

variable {σ τ K F : Type*} [Field K] [Field F] [Fintype F]

/-- Reindexing an assignment transports it contravariantly along the variable
equivalence. -/
def reindexAssignments (e : σ ≃ τ) : (σ → F) ≃ (τ → F) where
  toFun x := fun t => x (e.symm t)
  invFun y := fun s => y (e s)
  left_inv x := by funext s; simp
  right_inv y := by funext t; simp

/-- Uniform assignment probability for an arbitrary finite variable set. -/
def finiteAssignmentProbability [Fintype σ] (event : (σ → F) → Prop) : ℚ≥0 := by
  classical
  exact ((Finset.univ.filter event).card : ℚ≥0) /
    (Fintype.card F : ℚ≥0) ^ Fintype.card σ

end

end UniqueGamesTheorem.Quadratic

end

section

/-!
# Rank-loss accounting for quadratic blocks

A nonzero kernel character determines the field line of a lossy block.  On
a generic space there is at most one such character on each field line, so
the rank drops by at most one.  Counting the possible determining characters
also bounds the number of lossy lines.  These are deterministic statements;
the random orientation may be selected only after this data is fixed.
-/

namespace UniqueGamesTheorem.Quadratic

noncomputable section

variable {R V W I : Type*} [Field R]
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

variable [Fintype V] [Fintype I] [DecidableEq I]

/-- The actual finite event of a child map having a nonzero kernel. -/
def lossIndices (f : I → V →ₗ[R] W) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => ∃ v : V, v ≠ 0 ∧ f i v = 0)

def alignedCharacters (aligned : V → Prop) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => v ≠ 0 ∧ aligned v)

end

end UniqueGamesTheorem.Quadratic

end

section

namespace UniqueGamesTheorem.Quadratic

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
theorem squareMap_injective : Function.Injective (fun x : F => x ^ 2) := by
  intro x y h
  change x ^ 2 = y ^ 2 at h
  have hs : (x + y) ^ 2 = 0 := by
    rw [CharTwo.add_sq, h, CharTwo.add_self_eq_zero]
  have hz : x + y = 0 := (sq_eq_zero_iff).mp hs
  exact (add_eq_zero_iff_eq_neg.mp hz).trans (CharTwo.neg_eq y)

/-- The unique square root, obtained by bijectivity of the finite square map. -/
noncomputable def squareRoot (c : F) : F :=
  Classical.choose (Finite.surjective_of_injective squareMap_injective c)

@[simp] theorem squareRoot_sq (c : F) : squareRoot c ^ 2 = c :=
  Classical.choose_spec (Finite.surjective_of_injective squareMap_injective c)

@[simp] theorem squareRoot_of_sq (c : F) : squareRoot (c ^ 2) = c := by
  apply squareMap_injective
  exact squareRoot_sq _

end UniqueGamesTheorem.Quadratic

end

section

namespace UniqueGamesTheorem.Quadratic

open Module
open scoped BigOperators

noncomputable section

section AlignmentEvents

variable {R F V ι n : Type*}
variable [Field R] [Field F] [Algebra R F]
variable [AddCommGroup V] [Module R V]
variable [Fintype V] [Fintype ι] [Fintype n]

/-- Nonzero inputs aligned by a specified linear lift. -/
def alignmentEvent (z : V → n → F) (g : V →ₗ[R] (n → F)) (c : V → F) :
    Finset V := by
  classical
  exact Finset.univ.filter (fun v => v ≠ 0 ∧ (∑ i, z v i * g v i) = c v)

end AlignmentEvents

section BinaryGenericity

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The cubic square-root right hand side of the alignment equation. -/
def alignmentRightHandSide (z : Fin 3 → F) : F := squareRoot (z 0 * z 1 * z 2)

/-- The complete genericity predicate. The universal linear
map quantifier occurs inside the property of the selected subspace. -/
def IsGeneric (S : Submodule (ZMod 2) (Fin 3 → F)) : Prop := by
  classical
  exact
    (∀ z w : S, z ≠ 0 → w ≠ 0 →
      (∃ t : F, (z : Fin 3 → F) = t • (w : Fin 3 → F)) → z = w) ∧
    (∀ g : S →ₗ[ZMod 2] (Fin 3 → F),
      (alignmentEvent (R := ZMod 2) (fun z : S => (z : Fin 3 → F)) g
        (fun z : S => alignmentRightHandSide (z : Fin 3 → F))).card ≤
          3 * Module.finrank (ZMod 2) S)

end BinaryGenericity

end

end UniqueGamesTheorem.Quadratic

end

section

/-!
# The finite nongeneric fraction

This definition records the actual uniform event on the rank-indexed
Grassmannian.
-/

noncomputable section

open UniqueGamesTheorem.Gadget.Orientation

namespace UniqueGamesTheorem.Quadratic

/-- The actual uniform fraction of nongeneric rank-`r` binary subspaces. -/
def nongenericFraction (F : Type*) [Field F] [Fintype F] [CharP F 2]
    [Algebra (ZMod 2) F] (r : ℕ) : ℚ :=
  (Nat.card {S : RankSpace (ZMod 2) (Fin 3 → F) r // ¬IsGeneric S.1} : ℚ) /
    Nat.card (RankSpace (ZMod 2) (Fin 3 → F) r)

end UniqueGamesTheorem.Quadratic

end

end

section

/-! The actual random binary-linear parametrization used in the genericity proof. -/

namespace UniqueGamesTheorem.Quadratic

open Module
open scoped BigOperators

noncomputable section

variable {F J : Type*} [Field F] [Algebra (ZMod 2) F] [Fintype J]

/-- Independent field entries specify a binary-linear map into `F³`. -/
def parameterMap (x : (Fin 3 × J) → F) : (J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F) :=
  (Pi.basisFun (ZMod 2) J).constr (ZMod 2) (fun j i => x (i, j))

theorem parameterMap_basis (x : (Fin 3 × J) → F) (j : J) (i : Fin 3) :
    parameterMap x ((Pi.basisFun (ZMod 2) J) j) i = x (i, j) := by
  exact congrFun ((Pi.basisFun (ZMod 2) J).constr_basis (ZMod 2)
    (fun j i => x (i, j)) j) i

end

end UniqueGamesTheorem.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_AlignmentCertificateLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact correspondence between uniform field entries and all binary-linear maps. -/

namespace UniqueGamesTheorem.Quadratic

noncomputable section

variable {F J : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F] [Fintype J]

/-- Every binary-linear map is determined by its freely chosen field-valued
basis entries, with no rejection or nonuniform multiplicity. -/
def parameterMapEquiv : ((Fin 3 × J) → F) ≃
    ((J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F)) where
  toFun := parameterMap
  invFun g ij := g ((Pi.basisFun (ZMod 2) J) ij.2) ij.1
  left_inv x := by
    funext ij
    exact parameterMap_basis x ij.2 ij.1
  right_inv g := by
    apply (Pi.basisFun (ZMod 2) J).ext
    intro j
    funext i
    exact parameterMap_basis _ j i

end

end UniqueGamesTheorem.Quadratic

end

section

/-! A single finite polynomial certifies injectivity and pair separation of
the actual binary-linear parametrization. -/

namespace UniqueGamesTheorem.Quadratic

open MvPolynomial
open scoped BigOperators

noncomputable section

variable (J : Type*) [Fintype J]

def nonzeroBinaryInputs : Finset (J → ZMod 2) := by
  classical
  exact Finset.univ.erase 0

def distinctNonzeroBinaryPairs : Finset ((J → ZMod 2) × (J → ZMod 2)) := by
  classical
  exact Finset.univ.filter (fun tu => tu.1 ≠ 0 ∧ tu.2 ≠ 0 ∧ tu.1 ≠ tu.2)

def separationPolynomial : MvPolynomial (Fin 3 × J) (ZMod 2) :=
  (∏ t ∈ nonzeroBinaryInputs J, universalLinearForm t 0) *
    ∏ tu ∈ distinctNonzeroBinaryPairs J, universalPairMinor tu.1 tu.2

end

end UniqueGamesTheorem.Quadratic

end

section

namespace UniqueGamesTheorem.Quadratic

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The field trace to the binary prime field. -/
noncomputable abbrev traceBinary : F →ₗ[ZMod 2] ZMod 2 := Algebra.trace (ZMod 2) F

omit [CharP F 2] in
/-- The trace pairing detects every nonzero field element. -/
theorem trace_mul_vanish_iff (a : F) :
    (∀ t : F, traceBinary (t * a) = 0) ↔ a = 0 := by
  constructor
  · intro h
    apply (traceForm_nondegenerate (ZMod 2) F).1 a
    intro t
    simpa only [Algebra.traceForm_apply, mul_comm] using h t
  · rintro rfl
    simp

end UniqueGamesTheorem.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_BlockKernelLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.DescentProbability.noiseFintype _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Character kernels on quadratic blocks

The character with horizontal coefficient `g` and vertical coefficient `z`
annihilates the block attached to `Fz` precisely when the alignment
equation holds.  The predicate below is annihilation of the actual binary
submodule, rather than an abstract replacement for that condition.
-/

namespace UniqueGamesTheorem.Quadratic

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The binary character with separate horizontal and vertical coefficients. -/
noncomputable def blockCharacter (g z : Vec F) (p : Vec F × Vec F) : ZMod 2 :=
  traceBinary (dot g p.1 + dot z p.2)

/-- Literal annihilation of every vector in the block attached to `v`. -/
def BlockAnnihilates (g z v : Vec F) : Prop :=
  ∀ p ∈ U v, blockCharacter g z p = 0

omit [Finite F] in
/-- The binary block is independent of the nonzero generator of its field line. -/
theorem U_smul_ne_zero (v : Vec F) {t : F} (ht : t ≠ 0) : U (t • v) = U v := by
  have hl : line (t • v) = line v :=
    Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ht) v
  ext p
  simp only [mem_U, hl, dot_smul_left, mul_eq_zero, ht, false_or]

omit [Finite F] in
theorem U_eq_of_nonzero_mem_line {v z : Vec F} (hz : z ≠ 0)
    (hm : z ∈ line v) : U z = U v := by
  obtain ⟨t, rfl⟩ := (mem_line_iff v z).mp hm
  have ht : t ≠ 0 := by
    intro ht
    apply hz
    simp [ht]
  exact U_smul_ne_zero v ht

end UniqueGamesTheorem.Quadratic

end

section

/-! Surjectivity of the actual all-lines/all-orientations parent aggregate. -/

noncomputable section

open scoped BigOperators

namespace UniqueGamesTheorem.Quadratic

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
variable [Fintype (BlockOrientationIndex F)]

def blockEmbedding (i : BlockOrientationIndex F) :
    Vec F →ₗ[ZMod 2] Vec F × Vec F :=
  (U (lineGenerator i.1)).subtype.comp i.2.toLinearMap

def blockAggregate : (BlockOrientationIndex F → Vec F) →ₗ[ZMod 2] Vec F × Vec F :=
  Gadget.aggregate (blockEmbedding (F := F))

theorem blockAggregate_single [DecidableEq (BlockOrientationIndex F)]
    (i : BlockOrientationIndex F) (b : Vec F) :
    blockAggregate (Pi.single i b) = blockEmbedding i b := by
  classical
  change (∑ j : BlockOrientationIndex F,
    blockEmbedding j ((Pi.single i b : BlockOrientationIndex F → Vec F) j)) = _
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem fieldLine_block_le_range_aggregate (A : FieldLine F) :
    U (lineGenerator A) ≤ LinearMap.range (blockAggregate (F := F)) := by
  classical
  intro p hp
  let J := chosenBlockOrientation A
  let i : BlockOrientationIndex F := ⟨A, J⟩
  obtain ⟨b, hb⟩ := J.surjective ⟨p, hp⟩
  refine ⟨Pi.single i b, ?_⟩
  rw [blockAggregate_single]
  change ((J b : U (lineGenerator A)) : Vec F × Vec F) = p
  exact congrArg Subtype.val hb

/-- All blocks occur in the actual pair-indexed aggregate.  Their already
proved span is the entire horizontal/vertical space, so the aggregate is
surjective, as required by the recursive shift construction. -/
theorem blockAggregate_surjective : Function.Surjective (blockAggregate (F := F)) := by
  have hspan : (⨆ v : {v : Vec F // v ≠ 0}, U v.1) ≤
      LinearMap.range (blockAggregate (F := F)) := by
    apply iSup_le
    intro v
    let A : FieldLine F := Projectivization.mk F v.1 v.2
    have hl : line (lineGenerator A) = line v.1 := by
      simpa only [A, Projectivization.submodule_mk, line] using line_lineGenerator A
    have hm : lineGenerator A ∈ line v.1 := by
      rw [← hl]
      exact (mem_line_iff _ _).mpr ⟨1, one_smul _ _⟩
    have hu := U_eq_of_nonzero_mem_line (lineGenerator_ne_zero A) hm
    simpa only [hu] using fieldLine_block_le_range_aggregate A
  rw [iSup_U_nonzero_eq_top] at hspan
  exact LinearMap.range_eq_top.mp (top_unique hspan)

theorem aggregate_blockEmbedding_surjective :
    Function.Surjective (Gadget.aggregate (blockEmbedding (F := F))) :=
  blockAggregate_surjective

end UniqueGamesTheorem.Quadratic

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_BlockRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Actual child restriction maps

A common-parent lift `g` gives a binary linear map from its logical character
space into the dual of each quadratic block.  Its kernel is literal character
annihilation, so the trace calculation and the all-lifts genericity predicate
apply directly to this map.
-/

namespace UniqueGamesTheorem.Quadratic

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Fintype F] [CharP F 2] [Algebra (ZMod 2) F] in
theorem dot_add_first_p0 (x y z : Vec F) :
    dot (x + y) z = dot x z + dot y z := by
  simp only [dot, Pi.add_apply]
  ring

/-- The actual trace character as a binary linear functional. -/
def blockCharacterLinear (g z : Vec F) :
    (Vec F × Vec F) →ₗ[ZMod 2] ZMod 2 where
  toFun := blockCharacter g z
  map_add' := by
    intro p q
    simp only [blockCharacter, Prod.fst_add, Prod.snd_add, dot_add_right, map_add]
    ring
  map_smul' := by
    intro c p
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl <;> simp [blockCharacter]

/-- Restriction to one block, linear in the logical character `z`. -/
def blockRestriction (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (v : Vec F) :
    S →ₗ[ZMod 2] ((U v) →ₗ[ZMod 2] ZMod 2) where
  toFun z := (blockCharacterLinear (g z) z).comp (U v).subtype
  map_add' := by
    intro z w
    ext p
    simp only [LinearMap.comp_apply, blockCharacterLinear, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.add_apply, map_add, Submodule.coe_add,
      blockCharacter, dot_add_first_p0, map_add]
    ring
  map_smul' := by
    intro c z
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl <;> ext p <;>
      simp [blockCharacterLinear, blockCharacter]

omit [Fintype F] in
@[simp] theorem blockRestriction_apply (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (v : Vec F) (z : S) (p : U v) :
    blockRestriction S g v z p = blockCharacter (g z) z p := rfl

end

end UniqueGamesTheorem.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_OrientedRestrictionLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Orientation-independent character kernels

Changing the binary parametrization of a block only pulls its dual back along
a linear equivalence.  This leaves the logical kernel unchanged and places
all child maps in one fixed dual space for the finite counting argument.
-/

namespace UniqueGamesTheorem.Quadratic

noncomputable section

variable {F B : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
variable [AddCommGroup B] [Module (ZMod 2) B]

/-- The actual child restriction after a choice of block orientation. -/
def orientedBlockRestriction (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (v : Vec F) (J : B ≃ₗ[ZMod 2] U v) :
    S →ₗ[ZMod 2] (B →ₗ[ZMod 2] ZMod 2) :=
  J.dualMap.toLinearMap.comp (blockRestriction S g v)

omit [Fintype F] in
@[simp] theorem orientedBlockRestriction_apply
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    (v : Vec F) (J : B ≃ₗ[ZMod 2] U v) (z : S) (b : B) :
    orientedBlockRestriction S g v J z b = blockCharacter (g z) z (J b) := rfl

end

end UniqueGamesTheorem.Quadratic

end

section

/-!
# At most `3r` actual lossy field lines

The genericity bound applies to the common-parent lift before a line or an
orientation is chosen.  A nonzero kernel character determines exactly one
projective field line, and its actual kernel equation implies alignment.
-/

namespace UniqueGamesTheorem.Quadratic

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

local instance instFintypeFieldLine : Fintype (FieldLine F) := Fintype.ofFinite _
local instance instFintypeSubtypeVecMemSubmoduleZModOfNatNat (S : Submodule (ZMod 2) (Vec F)) : Fintype S := by
  classical
  exact Subtype.fintype (Membership.mem S)

/-- A total projective-line map; the default is irrelevant on nonzero characters. -/
def characterFieldLine (A₀ : FieldLine F) (z : Vec F) : FieldLine F := by
  classical
  exact if hz : z = 0 then A₀ else Projectivization.mk F z hz

/-- All maps have the same binary dual codomain, despite their different blocks. -/
def fieldLineRestrictions (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A) :
    FieldLine F → S →ₗ[ZMod 2] (Vec F →ₗ[ZMod 2] ZMod 2) :=
  fun A => orientedBlockRestriction S g (lineGenerator A) (J A)

end

end UniqueGamesTheorem.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_HarmonicLoss
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Harmonic loss for the actual quadratic child maps

The probabilistic hypotheses of the harmonic accounting lemmas are discharged
here by the proved field-line kernel criterion and genericity count.
-/

namespace UniqueGamesTheorem.Quadratic

open scoped BigOperators
open UniqueGamesTheorem.Gadget.Harmonic

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

local instance instFintypeFieldLine_1 : Fintype (FieldLine F) := Fintype.ofFinite _
local instance instFintypeSubtypeVecMemSubmoduleZModOfNatNat_1 (S : Submodule (ZMod 2) (Vec F)) : Fintype S := by
  classical
  exact Subtype.fintype (Membership.mem S)

def fieldLineTheta (F : Type*) [Field F] [Finite F] : ℚ :=
  (Nat.card (FieldLine F) : ℚ)⁻¹

/-- The image dimension of the actual oriented child restriction map. -/
def nextBlockRank (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A)
    (A : FieldLine F) : ℕ :=
  Module.finrank (ZMod 2) (fieldLineRestrictions S g J A).range

end

end UniqueGamesTheorem.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_TraceDual
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Trace coordinates for families of binary characters

The trace pairing identifies the binary dual of `F³` with `F³` itself.  Its
inverse is linear, so a common-parent family of binary functionals produces
one binary-linear lift `g`, as required by the all-lifts genericity theorem.
-/

namespace UniqueGamesTheorem.Quadratic

noncomputable section

variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]

omit [Finite F] [Algebra (ZMod 2) F] in
theorem dot_add_first_p1 (x y z : Vec F) :
    dot (x + y) z = dot x z + dot y z := by
  simp only [dot, Pi.add_apply]
  ring

/-- The trace dot product, as an actual binary bilinear form. -/
def traceDotForm : LinearMap.BilinForm (ZMod 2) (Vec F) where
  toFun z :=
    { toFun := fun y => traceBinary (dot z y)
      map_add' := by
        intro x y
        rw [dot_add_right, map_add]
      map_smul' := by
        intro c y
        have hc : c = 0 ∨ c = 1 := by
          fin_cases c
          · exact Or.inl rfl
          · exact Or.inr rfl
        rcases hc with rfl | rfl <;> simp }
  map_add' := by
    intro z w
    apply LinearMap.ext
    intro y
    change traceBinary (dot (z + w) y) =
      traceBinary (dot z y) + traceBinary (dot w y)
    rw [dot_add_first_p1, map_add]
  map_smul' := by
    intro c z
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl <;> ext y <;> simp

omit [Finite F] in
@[simp] theorem traceDotForm_apply (z y : Vec F) :
    traceDotForm z y = traceBinary (dot z y) := rfl

/-- Nondegeneracy holds coordinate by coordinate over the finite field. -/
theorem traceDotForm_nondegenerate :
    (traceDotForm (F := F)).Nondegenerate := by
  constructor
  · intro z hz
    ext i
    apply (trace_mul_vanish_iff (z i)).mp
    intro t
    have h := hz (Pi.single i t)
    have hd : dot z (Pi.single i t) = t * z i := by
      fin_cases i <;> simp [dot, mul_comm]
    simpa only [traceDotForm_apply, hd] using h
  · intro z hz
    ext i
    apply (trace_mul_vanish_iff (z i)).mp
    intro t
    have h := hz (Pi.single i t)
    have hd : dot (Pi.single i t) z = t * z i := by
      fin_cases i <;> simp [dot]
    simpa only [traceDotForm_apply, hd] using h

/-- The exact binary trace-pairing identification. -/
def traceDualEquiv : Vec F ≃ₗ[ZMod 2] (Vec F →ₗ[ZMod 2] ZMod 2) :=
  traceDotForm.toDual traceDotForm_nondegenerate

@[simp] theorem traceDualEquiv_apply (z y : Vec F) :
    traceDualEquiv z y = traceBinary (dot z y) := rfl

@[simp] theorem traceDualEquiv_symm_apply
    (γ : Vec F →ₗ[ZMod 2] ZMod 2) (y : Vec F) :
    traceBinary (dot (traceDualEquiv.symm γ) y) = γ y := by
  change traceDualEquiv (traceDualEquiv.symm γ) y = γ y
  rw [LinearEquiv.apply_symm_apply]

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- Taking trace coordinates preserves linear dependence on the family index. -/
def representTraceFamily (γ : W →ₗ[ZMod 2] (Vec F →ₗ[ZMod 2] ZMod 2)) :
    W →ₗ[ZMod 2] Vec F :=
  traceDualEquiv.symm.toLinearMap.comp γ

end

end UniqueGamesTheorem.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Gadgets_BlockDescentLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniqueGamesTheorem

namespace Gadget.BlockDescent

open Quadratic OrientedBlockKernel

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

abbrev BinaryDual := Vec F →ₗ[ZMod 2] ZMod 2

/-- Coordinates of a binary character subspace under the trace pairing. -/
def traceSpace (S : Submodule (ZMod 2) (BinaryDual (F := F))) :
    Submodule (ZMod 2) (Vec F) := S.map traceDualEquiv.symm.toLinearMap

def traceSpaceEquiv (S : Submodule (ZMod 2) (BinaryDual (F := F))) :
    S ≃ₗ[ZMod 2] traceSpace S :=
  Submodule.equivMapOfInjective traceDualEquiv.symm.toLinearMap
    traceDualEquiv.symm.injective S

omit [CharP F 2] in
@[simp] theorem traceSpaceEquiv_apply_val
    (S : Submodule (ZMod 2) (BinaryDual (F := F))) (z : S) :
    (traceSpaceEquiv S z).val = traceDualEquiv.symm z.val := rfl

/-- One binary-linear lift on the trace-coordinate domain, obtained from the
single common parent map. It is fixed before the outgoing line/orientation. -/
def traceLift (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) : traceSpace S →ₗ[ZMod 2] Vec F :=
  representTraceFamily (γ.comp (traceSpaceEquiv S).symm.toLinearMap)

end Gadget.BlockDescent

namespace Gadget.FreshGenericity

open scoped BigOperators Classical
open Module

open Orientation Quadratic BlockDescent OrientedBlockKernel

section RankTransport

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]

/-- A fixed coordinate equivalence transports the complete rank-indexed
Grassmannian bijectively, so it preserves its uniform distribution. -/
def rankSpaceEquiv (e : V ≃ₗ[K] W) (r : ℕ) : RankSpace K V r ≃ RankSpace K W r :=
  (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv (fun S => by
    change finrank K S = r ↔ finrank K (S.map e.toLinearMap) = r
    rw [e.finrank_map_eq])

@[simp] theorem rankSpaceEquiv_apply (e : V ≃ₗ[K] W) (r : ℕ)
    (S : RankSpace K V r) :
    (rankSpaceEquiv e r S).val = S.val.map e.toLinearMap := rfl

local instance linearMapFintype [Fintype V] [Fintype W] : Fintype (V →ₗ[K] W) :=
  Fintype.ofInjective (fun f : V →ₗ[K] W => (f : V → W)) DFunLike.coe_injective

local instance linearEquivFintype [Fintype V] [Fintype W] : Fintype (V ≃ₗ[K] W) :=
  Fintype.ofInjective (fun e : V ≃ₗ[K] W => (e : V → W)) DFunLike.coe_injective

local instance submoduleFintype [Fintype V] : Fintype (Submodule K V) :=
  Fintype.ofInjective (fun S : Submodule K V => (S : Set V)) SetLike.coe_injective

local instance rankSpaceFintype [Fintype V] (r : ℕ) : Fintype (RankSpace K V r) :=
  inferInstanceAs (Fintype {S : Submodule K V // finrank K S = r})

end RankTransport

attribute [local instance] linearMapFintype linearEquivFintype submoduleFintype rankSpaceFintype

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

/-- Nongenericity includes the universal lift quantifier in `IsGeneric`.
The field's simultaneous bound includes rank zero as well. -/
def bad (S : Submodule (ZMod 2) (BinaryDual (F := F))) : Prop :=
  ¬ IsGeneric (traceSpace S)

end Gadget.FreshGenericity

/-!
# Outgoing harmonic loss for the actual adaptive child map

Uniform sampling of the concrete pair `(field line, binary orientation)` has
the uniform field-line marginal. The child rank is independent of orientation,
so the proved quadratic kernel count gives the outgoing conditional loss for
the common map produced by every parent lift.
-/

namespace Gadget.OutgoingHarmonic

open Quadratic OrientedBlockKernel BlockDescent Harmonic

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

local instance instFiniteLinearEquivZModOfNatNatIdVec : Finite (Vec F ≃ₗ[ZMod 2] Vec F) := DFunLike.finite _
local instance instFintypeLinearEquivZModOfNatNatIdVec : Fintype (Vec F ≃ₗ[ZMod 2] Vec F) := Fintype.ofFinite _

def outgoingLoss (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) : ℚ :=
  average (fun i : BlockOrientationIndex F => UniqueGamesTheorem.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) -
    UniqueGamesTheorem.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) (childCharacter orientedBlockLinear γ i).range))

end Gadget.OutgoingHarmonic

namespace Gadget.BaseDetection

open Quadratic OrientedBlockKernel BlockDescent Harmonic
open Descent DescentProbability LeafDetection
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
variable [DecidableEq (BlockOrientationIndex F)] [Nonempty (BlockOrientationIndex F)]

/-- Turn the fixed generic vector subspace into its actual logical characters. -/
def logicalCharacters (S : Submodule (ZMod 2) (Vec F)) :
    Submodule (ZMod 2) (BinaryDual (F := F)) :=
  S.map traceDualEquiv.toLinearMap

end Gadget.BaseDetection

end UniqueGamesTheorem

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Gadgets_QuadraticStageNoise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

namespace UniqueGamesTheorem.Gadget.QuadraticStageNoise

open scoped BigOperators Classical
open Quadratic

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

local instance indexDecidableEq : DecidableEq (BlockOrientationIndex F) := Classical.decEq _

local instance automorphismFinite : Finite (Vec F ≃ₗ[ZMod 2] Vec F) := DFunLike.finite _
noncomputable local instance automorphismFintype : Fintype (Vec F ≃ₗ[ZMod 2] Vec F) :=
  Fintype.ofFinite _

local instance indexNonempty : Nonempty (BlockOrientationIndex F) := by
  have hA : Nonempty (FieldLine F) := Fintype.card_pos_iff.mp (by
    simpa only [Nat.card_eq_fintype_card] using (card_FieldLine_pos (F := F)))
  obtain ⟨A⟩ := hA
  exact ⟨⟨A, chosenBlockOrientation A⟩⟩

def rate (F : Type*) [Fintype F] : ℚ :=
  1 - 1 / ((Nat.card F : ℚ) ^ 2 + (Nat.card F : ℚ) + 1)

/-- The actual recursive spaces, shifts, outputs and finite leaf-noise sampler. -/
noncomputable def stage (n : ℕ) : Stage (ZMod 2) (Vec F) :=
  Stage.iterate (blockEmbedding (F := F)) aggregate_blockEmbedding_surjective Q n

/-- The logical alphabet is an actual injected shift subspace after quotient. -/
noncomputable def quotientStage (n : ℕ) : Stage (ZMod 2) (Vec F) :=
  StageQuotient.toStage (stage (F := F) n)

end UniqueGamesTheorem.Gadget.QuadraticStageNoise

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_UniformSubspaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Uniform injective parameter maps induce the uniform law on subspaces of the
specified rank.  The proof uses actual transitivity of ambient linear
automorphisms on injections, not an assumed distributional premise.
-/

noncomputable section

open scoped BigOperators
open Module
open UniqueGamesTheorem.Gadget.Orientation

namespace UniqueGamesTheorem.Quadratic.UniformSubspaces

variable {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- A linear parameter map with its injectivity proof. -/
def Injection (K V W : Type*) [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] :=
  {J : V →ₗ[K] W // Function.Injective J}

instance injectionAction : MulAction (W ≃ₗ[K] W) (Injection K V W) where
  smul a J := ⟨a.toLinearMap.comp J.val, a.injective.comp J.property⟩
  one_smul J := by
    apply Subtype.ext
    ext x
    rfl
  mul_smul a b J := by
    apply Subtype.ext
    ext x
    rfl

/-- The image has the dimension of the parameter space. -/
def image (J : Injection K V W) : RankSpace K W (finrank K V) :=
  ⟨LinearMap.range J.val, LinearMap.finrank_range_of_inj J.property⟩

end UniqueGamesTheorem.Quadratic.UniformSubspaces

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Quadratic_GenericFieldChoice
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# One field for every rank up to a fixed threshold

The extension degree is chosen using only the rank threshold and the requested
genericity error.  In particular it is fixed before the logical dimension in
the later enlargement construction.  A generic top-rank space exists in the
same field.
-/

namespace UniqueGamesTheorem.Quadratic

open scoped BigOperators
open UniqueGamesTheorem.Gadget.Orientation

noncomputable section

noncomputable instance binaryFieldFintype (d : ℕ) : Fintype (BinaryField d) :=
  Fintype.ofFinite _

end

end UniqueGamesTheorem.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Gadgets_BaseConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# The finite base gadget with arbitrarily small nonlinear change

The harmonic rank and genericity error are chosen first. A single finite field
then supplies all required genericity statements, and the actual recursion is
run to its harmonic depth. The kernel quotient injects the logical alphabet.
Every linear map injective there detects at least one quarter of the noise.
-/

namespace UniqueGamesTheorem.Gadget.BaseConstruction

open Quadratic QuadraticStageNoise Harmonic Parameters
open scoped Classical

noncomputable section

variable {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

local instance indexDecidableEq : DecidableEq (BlockOrientationIndex F) := Classical.decEq _

end

end UniqueGamesTheorem.Gadget.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_FactorizationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The finite product algebra of dependency breaking.

Revealing one endpoint of each independently sampled question pair turns the
remaining question weight into a product of two separate functions, one for
each player. Further separate restrictions on the players' answers preserve
this product. The final theorem normalizes the displayed weights, rather than
assuming conditional independence as an abstract hypothesis.
-/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators

noncomputable section

variable {ι α β : Type*} [Fintype ι] [DecidableEq α] [DecidableEq β]

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem productWeight_mass (left : X → ℝ) (right : Y → ℝ) :
    (∑ xy : X × Y, left xy.1 * right xy.2) =
      (∑ x, left x) * (∑ y, right y) := by
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

end

end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! Replacing the input marginal of an actual conditional profile. -/
namespace UniqueGamesTheorem.Foundations.Repetition.ProfileCorrection
open scoped BigOperators
open UniqueGamesTheorem.Foundations.Information
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

def seedQuestionMarginal (p : X × (S × Y) → ℝ) : X × S → ℝ :=
  firstMarginal (fun z : (X × S) × Y => p (z.1.1, (z.1.2, z.2)))

omit [Fintype X] in
theorem seedQuestionMarginal_first (p : X × (S × Y) → ℝ) :
    firstMarginal (seedQuestionMarginal p) = firstMarginal p := by
  funext x
  simp only [seedQuestionMarginal, firstMarginal, Fintype.sum_prod_type]

end
end UniqueGamesTheorem.Foundations.Repetition.ProfileCorrection

end

section

namespace UniqueGamesTheorem.Foundations.Repetition

noncomputable def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- A real cutoff gives a valid step at every integer strictly below it. -/
theorem cutoff_step {v ell : ℝ} {n m : ℕ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hell : 1 ≤ ell)
    (hm : (m : ℝ) < (n : ℝ) * (1 - v) ^ 2 / (2925 * ell)) :
    2700 * (m : ℝ) * ell ≤ (1 - v) ^ 2 * ((n : ℝ) - m) := by
  have hell0 : 0 < ell := by linarith
  have hd : (1 - v) ^ 2 ≤ 1 := by nlinarith
  have hmul : (m : ℝ) * (2925 * ell) < (n : ℝ) * (1 - v) ^ 2 :=
    (lt_div_iff₀ (by positivity : 0 < 2925 * ell)).1 hm
  have hdell : (1 - v) ^ 2 ≤ 225 * ell := by linarith
  have hprod := mul_le_mul_of_nonneg_left hdell (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  nlinarith

theorem cutoff_le_length {v ell : ℝ} (n : ℕ)
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hell : 1 ≤ ell) :
    (n : ℝ) * (1 - v) ^ 2 / (2925 * ell) ≤ n := by
  have hell0 : 0 < ell := by linarith
  apply (div_le_iff₀ (by positivity : 0 < 2925 * ell)).2
  have hd : (1 - v) ^ 2 ≤ 2925 * ell := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- The loss in one real-power block is cubic in the initial gap. -/
theorem block_contraction {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) :
    ((1 + v) / 2) ^ ((1 - v) ^ 2 / 2925 : ℝ) ≤
      1 - (1 - v) ^ 3 / 5850 := by
  have hd : (1 - v) ^ 2 ≤ 1 := by nlinarith
  have hb := rpow_one_add_le_one_add_mul_self
    (s := -(1 - v) / 2) (p := (1 - v) ^ 2 / 2925)
    (by linarith) (by positivity) (by nlinarith)
  have hbase : 1 + -(1 - v) / 2 = (1 + v) / 2 := by ring
  have hrhs : 1 + (1 - v) ^ 2 / 2925 * (-(1 - v) / 2) =
      1 - (1 - v) ^ 3 / 5850 := by ring
  rwa [hbase, hrhs] at hb

end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_Variation
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finite total-variation operations used by the dependency-breaking argument.
All statements concern the displayed real weight functions. In particular,
conditioning rescales actual restricted weights, and kernels act by finite sums.
-/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators
open Information

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Applying a finite stochastic kernel, forgetting its input. -/
noncomputable def kernelPushforward (p : α → ℝ) (kernel : α → β → ℝ) : β → ℝ :=
  fun b => ∑ a, p a * kernel a b

end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_MaskedVariation
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact variation decomposition for the two choices of revealed endpoint.
The support of the actual reveal profiles makes both branch identities valid,
including zero-probability revealed endpoints. -/
namespace UniqueGamesTheorem.Foundations.Repetition
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

omit [Fintype S] in
theorem maskedJoint_firstMarginal_inl (p : S × (X × Y) → ℝ) (s : S) (x : X) :
    Information.firstMarginal (maskedJoint p) (s, Sum.inl x) =
      (∑ y, p (s, (x, y))) / 2 := by
  simp [Information.firstMarginal, maskedJoint, Fintype.sum_prod_type,
    div_eq_mul_inv, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp

omit [Fintype S] in
theorem maskedJoint_firstMarginal_inr (p : S × (X × Y) → ℝ) (s : S) (y : Y) :
    Information.firstMarginal (maskedJoint p) (s, Sum.inr y) =
      (∑ x, p (s, (x, y))) / 2 := by
  simp [Information.firstMarginal, maskedJoint, Fintype.sum_prod_type,
    div_eq_mul_inv, Finset.sum_mul]

theorem abs_half_sub_half_mul (a b c : ℝ) :
    |a / 2 - b / 2 * c| = |a - b * c| / 2 := by
  rw [show a / 2 - b / 2 * c = (a - b * c) / 2 by ring, abs_div]
  norm_num

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_SelectedInformationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Concrete selected-coordinate questions and answer labels for the
side-information inequality. The event is the actual repeated game's selected
success event. -/
namespace UniqueGamesTheorem.Foundations.Repetition
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
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! The selected-success likelihood factors into a fixed verifier check and
two separate tests on the local deterministic answers. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open Games
noncomputable section
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

omit [Fintype Q₁] [Fintype Q₂] [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedQuestionTuple_left (selected : Finset (Fin n))
    (fixed : selected → Q₁ × Q₂) (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    (selectedQuestionTuple selected fixed remaining).1 =
      mergeCoordinates selected (fun i => (fixed i).1) (fun i => (remaining i).1) := by
  funext i
  simp only [selectedQuestionTuple, mergeCoordinates]
  split <;> rfl

omit [Fintype Q₁] [Fintype Q₂] [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedQuestionTuple_right (selected : Finset (Fin n))
    (fixed : selected → Q₁ × Q₂) (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    (selectedQuestionTuple selected fixed remaining).2 =
      mergeCoordinates selected (fun i => (fixed i).2) (fun i => (remaining i).2) := by
  funext i
  simp only [selectedQuestionTuple, mergeCoordinates]
  split <;> rfl

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_PartialRevealLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Removing one independent reveal from the explicit product law. The
likelihood can be any function of the questions and outside data. -/
namespace UniqueGamesTheorem.Foundations.Repetition
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
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! The side-information estimate for the explicit coordinate marginals of
the selected-answer/reveal law, followed by removal of one reveal variable. -/
namespace UniqueGamesTheorem.Foundations.Repetition
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
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! Conversion of the actual selected-label information bound into the
alphabet budget, followed by finite averaging over unused coordinates. -/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : ℕ}

theorem selectedLabels_card (selected : Finset (Fin n)) :
    Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) =
      (Fintype.card A₁ * Fintype.card A₂) ^ selected.card := by
  simp [SelectedLabels, Fintype.card_prod, mul_pow]

theorem unusedCoordinates_card (selected : Finset (Fin n)) :
    Fintype.card {i : Fin n // i ∉ selected} = n - selected.card := by
  classical
  simp

theorem unusedCoordinates_card_real (selected : Finset (Fin n)) :
    (Fintype.card {i : Fin n // i ∉ selected} : ℝ) = (n : ℝ) - selected.card := by
  have hs : selected.card ≤ n := by simpa using Finset.card_le_univ selected
  rw [unusedCoordinates_card, Nat.cast_sub hs]

theorem sqrt_budget_factor (a b : ℝ) (ha : 0 < a) :
    Real.sqrt (a * b) = a * Real.sqrt (b / a) := by
  have he : a * b = a ^ 2 * (b / a) := by
    field_simp
  rw [he, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq (le_of_lt ha)]

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! The common data used by the two local simulators is the actual
selected-answer law with only the embedded coordinate's reveal removed. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

abbrev SelectedCommonData (selected : Finset (Fin n))
    (j : {i : Fin n // i ∉ selected}) :=
  ((selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
    ({i : {i : Fin n // i ∉ selected} // i ≠ j} → Q₁ ⊕ Q₂)

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! Conditional common-data profiles, with their error measured against the
actual endpoint-reveal reference and the actual question marginal. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
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

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

def swapQuestionEndpoints : (S × (Y × X)) ≃ (S × (X × Y)) where
  toFun z := (z.1,(z.2.2,z.2.1))
  invFun z := (z.1,(z.2.2,z.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

def rightCommonMarginal (p : S × (X × Y) → ℝ) : Y × S → ℝ :=
  fun z => ∑ x, p (z.2,(x,z.1))

def rightCommonProfile (p : S × (X × Y) → ℝ) (fallback : S → ℝ) : Y → S → ℝ :=
  conditionalKernel (rightCommonMarginal p) fallback

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_Overlap
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Direct diagonal-overlap comparison for the finite correlated sampler.
All quantities are finite weight arrays; no reference sampler or embedding
claim is assumed. The final theorem consumes the per-label lower bound that
is proved for the actual finite threshold sampler in CorrelatedSampling.
-/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators
open Information

theorem min_half_formula (x y : ℝ) :
    min x y = (x + y - |x - y|) / 2 := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem discount_le_self {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    c / (1 + t) ≤ c := by
  apply (div_le_iff₀ (by linarith : 0 < 1 + t)).2
  nlinarith [mul_nonneg hc ht]

theorem discount_loss_le_mul {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    c - c / (1 + t) ≤ c * t := by
  have hd : 0 < 1 + t := by linarith
  have hid : c - c / (1 + t) = c * t / (1 + t) := by
    field_simp [hd.ne']
    ring
  rw [hid]
  apply (div_le_iff₀ hd).2
  nlinarith [mul_nonneg (mul_nonneg hc ht) ht]

noncomputable def discountedCommonMass {X S : Type*} [Fintype X] [Fintype S]
    (p a b : X × S → ℝ) (t : X → ℝ) : ℝ :=
  ∑ z, min (p z) (min (a z) (b z)) / (1 + t z.1)

noncomputable def diagonalWeights {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) : X × S × S → ℝ := by
  classical
  exact fun z => if z.2.1 = z.2.2 then p (z.1, z.2.1) else 0

end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_SelectedCommonMarginalLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The common-data law has exactly the actual selected-event question marginal.
Removing the fair endpoint reveal and regrouping the outside data preserve
the embedded question pair. -/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators
open Games Information
noncomputable section

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

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-!
Actual local completions of the unused questions, conditioned on common data
and the player's own embedded question. The raw row factors are explicit
finite weights. Their normalization reconstructs the actual selected common
law, including zero rows. The fallback independently samples base marginal
questions and then inserts the local input at the embedded coordinate.
-/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

section LocalNormalization

variable {I X Y : Type*} [Fintype I] [DecidableEq I]
  [Fintype X] [Fintype Y]

def completionTupleEquiv : (I → X × Y) ≃ ((I → X) × (I → Y)) where
  toFun u := (fun i => (u i).1, fun i => (u i).2)
  invFun z := fun i => (z.1 i, z.2 i)
  left_inv u := by funext i; rfl
  right_inv z := by cases z; rfl

end LocalNormalization

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_SelectionSequence
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Repetition.SelectionSequence

theorem exists_unused {n : Nat} (S : Finset (Fin n)) (hcard : S.card < n) :
    ∃ j : Fin n, j ∉ S := by
  classical
  apply Classical.byContradiction
  intro h
  have hall : ∀ j : Fin n, j ∈ S := by
    intro j
    apply Classical.byContradiction
    intro hj
    exact h ⟨j, hj⟩
  have hfull : S = Finset.univ :=
    Finset.ext (fun j => iff_of_true (hall j) (Finset.mem_univ j))
  have hbad : n < n := by
    simpa only [hfull, Finset.card_univ, Fintype.card_fin] using hcard
  exact Nat.lt_irrefl n hbad

/-- Insert a chosen unused coordinate while there are coordinates remaining. -/
noncomputable def nextSet {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j)
    (S : Finset (Fin n)) : Finset (Fin n) :=
  if hs : S.card < n then insert (Classical.choose (witness S hs)) S else S

/-- A total sequence, constant after all `n` coordinates have been selected. -/
noncomputable def selectedSet {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j) : Nat → Finset (Fin n)
  | 0 => ∅
  | m + 1 => nextSet Step witness (selectedSet Step witness m)

theorem selectedSet_subset_succ {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j) (m : Nat) :
    selectedSet Step witness m ⊆ selectedSet Step witness (m + 1) := by
  change selectedSet Step witness m ⊆ nextSet Step witness (selectedSet Step witness m)
  unfold nextSet
  split
  · exact Finset.subset_insert _ _
  · exact le_rfl

theorem selectedSet_monotone {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j) :
    Monotone (selectedSet Step witness) :=
  monotone_nat_of_le_succ (selectedSet_subset_succ Step witness)

open UniqueGamesTheorem.Foundations.Games

end UniqueGamesTheorem.Foundations.Repetition.SelectionSequence

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_CompletedSamplingLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Finite local completion after correlated sampling

One independent seed contains the original shared seed and two full response
tables. Its local reads give exactly the mixture of the requested completion
kernels. Applying those kernels contracts total variation. On a diagonal
target the same construction uses one common selected label.
-/

namespace UniqueGamesTheorem.Foundations.Repetition.CompletedSampling

open scoped BigOperators
open Games

noncomputable section

section Completion

variable {X Y S Γ U V : Type*}
  [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ] [Fintype U] [Fintype V]
  [DecidableEq X] [DecidableEq Y] [DecidableEq S]

/-- The independent original seed and two full local completion tables. -/
abbrev Seed (Γ X Y S U V : Type*) :=
  Γ × KernelSampling.Seed (X × S) (Y × S) U V

def left (sL : Γ → X → S) (seed : Seed Γ X Y S U V) (x : X) : U :=
  KernelSampling.readLeft seed.2 (x, sL seed.1 x)

def right (sR : Γ → Y → S) (seed : Seed Γ X Y S U V) (y : Y) : V :=
  KernelSampling.readRight seed.2 (y, sR seed.1 y)

end Completion

section CoordinateCompletion

variable {I X Y S Γ : Type*}
  [Fintype I] [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y] [DecidableEq S]

/-- Restore the left input coordinate even on completion tables of weight zero. -/
def coordinateLeft (j : I) (sL : Γ → X → S)
    (seed : Seed Γ X Y S (I → X) (I → Y)) (x : X) : I → X :=
  KernelSampling.completedLeft j seed.2 (x, sL seed.1 x)

/-- Restore the right input coordinate even on completion tables of weight zero. -/
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

end CoordinateCompletion

end

end UniqueGamesTheorem.Foundations.Repetition.CompletedSampling

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_EqualityFiber
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finite equality-fiber extraction for the Grassmann-to-matrix route.

These elementary results do not assume a shortcode inverse theorem.  They
separate the equality test, the retention of a nonempty output fiber, and the
subsequent removal of zero perturbation factors.  The dimension-uniform
Grassmann expansion theorem remains a separate mathematical obligation.
-/

namespace UniqueGamesTheorem.Inverse.EqualityFiber

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Information

variable {X Y : Type*} [Fintype X] [Fintype Y]

def fiberMass (p : X → ℝ) (f : X → Y) (y : Y) : ℝ := by
  classical
  exact ∑ x, if f x = y then p x else 0

def fiberFlow (p : X → ℝ) (k : X → X → ℝ) (f : X → Y) (y : Y) : ℝ := by
  classical
  exact ∑ x, p x * ∑ x', k x x' * if f x = y ∧ f x' = y then 1 else 0

def equalityAcceptance (p : X → ℝ) (k : X → X → ℝ) (f : X → Y) : ℝ := by
  classical
  exact ∑ x, p x * ∑ x', k x x' * if f x = f x' then 1 else 0

end
end UniqueGamesTheorem.Inverse.EqualityFiber

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSAffineRestrictionComplementLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
An explicit splitting of a linear functional with a chosen unit preimage.
Both directions retain the chosen vector, permitting compatible splittings of
nested spaces and subspaces in the KMS argument.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticFunctionalSplit

variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- Split off the coordinate measured by `a`, using the prescribed vector `t`.
The kernel coordinate is exactly `x - a x • t`. -/
def splitEquiv (a : F →ₗ[K] K) (t : F) (ht : a t = 1) :
    F ≃ₗ[K] (a.ker × K) where
  toFun x := (⟨x - a x • t, by simp [LinearMap.mem_ker, ht]⟩, a x)
  invFun p := (p.1 : F) + p.2 • t
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change x + y - a (x + y) • t = (x - a x • t) + (y - a y • t)
      rw [map_add, add_smul]
      abel
    · exact a.map_add x y
  map_smul' c x := by
    apply Prod.ext
    · apply Subtype.ext
      change c • x - a (c • x) • t = c • (x - a x • t)
      simp [smul_sub, smul_smul]
    · exact a.map_smul c x
  left_inv x := by
    change x - a x • t + a x • t = x
    exact sub_add_cancel _ _
  right_inv p := by
    have hp : a (p.1 : F) = 0 := p.1.property
    apply Prod.ext
    · apply Subtype.ext
      change (p.1 : F) + p.2 • t - a ((p.1 : F) + p.2 • t) • t = p.1
      simp [hp, ht]
    · change a ((p.1 : F) + p.2 • t) = p.2
      simp [hp, ht]

@[simp] theorem splitEquiv_apply_snd (a : F →ₗ[K] K) (t : F) (ht : a t = 1) (x : F) :
    (splitEquiv a t ht x).2 = a x := rfl

@[simp] theorem splitEquiv_apply_fst_coe (a : F →ₗ[K] K) (t : F) (ht : a t = 1) (x : F) :
    ((splitEquiv a t ht x).1 : F) = x - a x • t := rfl

@[simp] theorem splitEquiv_symm_apply (a : F →ₗ[K] K) (t : F) (ht : a t = 1)
    (p : a.ker × K) :
    (splitEquiv a t ht).symm p = (p.1 : F) + p.2 • t := rfl

@[simp] theorem splitEquiv_symm_apply_zero (a : F →ₗ[K] K) (t : F) (ht : a t = 1)
    (b : a.ker) : (splitEquiv a t ht).symm (b, 0) = (b : F) := by
  simp

@[simp] theorem splitEquiv_apply_ker (a : F →ₗ[K] K) (t : F) (ht : a t = 1)
    (b : a.ker) : splitEquiv a t ht (b : F) = (b, 0) := by
  apply (splitEquiv a t ht).symm.injective
  simp

@[simp] theorem splitEquiv_apply_unit (a : F →ₗ[K] K) (t : F) (ht : a t = 1) :
    splitEquiv a t ht t = (0, 1) := by
  apply (splitEquiv a t ht).symm.injective
  simp

end UniqueGamesTheorem.Inverse.KMSAnalyticFunctionalSplit

end

section

/-!
Compatible one-coordinate splittings of two surjections with a common target.
A single target coordinate is lifted through both maps. The three resulting
linear equivalences put both surjections into the product of their kernel
restriction with the identity on the binary field.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticCompatibleSplitting

noncomputable section

abbrev F2 := ZMod 2

variable {I F K : Type*}
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup F] [Module F2 F]
  [AddCommGroup K] [Module F2 K]

/-- Data of one common coordinate and compatible section vectors. All maps
and all smaller spaces below are constructed from these original data. -/
structure CompatibleSplitting (π : I →ₗ[F2] K) (A : F →ₗ[F2] K) where
  functional : K →ₗ[F2] F2
  targetVector : K
  functional_targetVector : functional targetVector = 1
  leftVector : I
  leftVector_image : π leftVector = targetVector
  rightVector : F
  rightVector_image : A rightVector = targetVector
  left_surjective : Function.Surjective π
  right_surjective : Function.Surjective A

namespace CompatibleSplitting

variable {π : I →ₗ[F2] K} {A : F →ₗ[F2] K}

abbrev K0 (s : CompatibleSplitting π A) := s.functional.ker
abbrev J (s : CompatibleSplitting π A) := (s.functional.comp π).ker
abbrev B (s : CompatibleSplitting π A) := (s.functional.comp A).ker

def targetEquiv (s : CompatibleSplitting π A) : K ≃ₗ[F2] (s.K0 × F2) :=
  KMSAnalyticFunctionalSplit.splitEquiv s.functional s.targetVector
    s.functional_targetVector

def leftEquiv (s : CompatibleSplitting π A) : I ≃ₗ[F2] (s.J × F2) :=
  KMSAnalyticFunctionalSplit.splitEquiv (s.functional.comp π) s.leftVector
    (by change s.functional (π s.leftVector) = 1
        rw [s.leftVector_image, s.functional_targetVector])

def rightEquiv (s : CompatibleSplitting π A) : F ≃ₗ[F2] (s.B × F2) :=
  KMSAnalyticFunctionalSplit.splitEquiv (s.functional.comp A) s.rightVector
    (by change s.functional (A s.rightVector) = 1
        rw [s.rightVector_image, s.functional_targetVector])

/-- The remaining part of the left surjection is its literal restriction. -/
def leftMap (s : CompatibleSplitting π A) : s.J →ₗ[F2] s.K0 :=
  (π.comp (s.functional.comp π).ker.subtype).codRestrict s.functional.ker
    (fun x => x.property)

/-- The remaining part of the right surjection is its literal restriction. -/
def rightMap (s : CompatibleSplitting π A) : s.B →ₗ[F2] s.K0 :=
  (A.comp (s.functional.comp A).ker.subtype).codRestrict s.functional.ker
    (fun x => x.property)

@[simp] theorem leftMap_apply_val (s : CompatibleSplitting π A) (x : s.J) :
    (s.leftMap x : K) = π x := rfl

@[simp] theorem rightMap_apply_val (s : CompatibleSplitting π A) (x : s.B) :
    (s.rightMap x : K) = A x := rfl

@[simp] theorem leftEquiv_symm_apply (s : CompatibleSplitting π A) (x : s.J × F2) :
    s.leftEquiv.symm x = (x.1 : I) + x.2 • s.leftVector := rfl

@[simp] theorem rightEquiv_symm_apply (s : CompatibleSplitting π A) (x : s.B × F2) :
    s.rightEquiv.symm x = (x.1 : F) + x.2 • s.rightVector := rfl

@[simp] theorem targetEquiv_symm_apply (s : CompatibleSplitting π A) (x : s.K0 × F2) :
    s.targetEquiv.symm x = (x.1 : K) + x.2 • s.targetVector := rfl

end CompatibleSplitting

/-- Positive target dimension supplies a basis coordinate; surjectivity
supplies its two lifts. No additional splitting hypothesis is required. -/
theorem exists_compatibleSplitting [FiniteDimensional F2 K]
    (π : I →ₗ[F2] K) (A : F →ₗ[F2] K)
    (hπ : Function.Surjective π) (hA : Function.Surjective A)
    (hdim : 0 < Module.finrank F2 K) : Nonempty (CompatibleSplitting π A) := by
  classical
  let b := Module.finBasis F2 K
  let j : Fin (Module.finrank F2 K) := ⟨0, hdim⟩
  obtain ⟨i, hi⟩ := hπ (b j)
  obtain ⟨f, hf⟩ := hA (b j)
  refine ⟨⟨b.coord j, b j, ?_, i, hi, f, hf, hπ, hA⟩⟩
  simp

def chooseSplit [FiniteDimensional F2 K]
    (π : I →ₗ[F2] K) (A : F →ₗ[F2] K)
    (hπ : Function.Surjective π) (hA : Function.Surjective A)
    (hdim : 0 < Module.finrank F2 K) : CompatibleSplitting π A :=
  Classical.choice (exists_compatibleSplitting π A hπ hA hdim)

end
end UniqueGamesTheorem.Inverse.KMSAnalyticCompatibleSplitting

end

section

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridCoordinates

variable {R A W D B C : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

/-- The chosen block compression: restrict to `B`, then forget `A`. -/
def compressBlock (S : (B × C) →ₗ[R] (A × (W × D))) : B →ₗ[R] (W × D) :=
  (LinearMap.snd R A (W × D)).comp (S.comp (LinearMap.inl R B C))

@[simp] theorem compressBlock_apply
    (S : (B × C) →ₗ[R] (A × (W × D))) (b : B) :
    compressBlock S b = (S (b, 0)).2 := rfl

/-- Coordinates of a map whose compression is `(z,0)`. -/
structure Coordinates (z : B →ₗ[R] W) where
  alpha : (B × C) →ₗ[R] A
  psi : (B × C) →ₗ[R] W
  psi_left : psi.comp (LinearMap.inl R B C) = z
  v : C →ₗ[R] D

@[ext] theorem Coordinates.ext {z : B →ₗ[R] W} {p q : Coordinates (A := A) (D := D)
    (C := C) z} (ha : p.alpha = q.alpha) (hp : p.psi = q.psi) (hv : p.v = q.v) : p = q := by
  cases p
  cases q
  cases ha
  cases hp
  cases hv
  rfl

/-- Assemble the three blocks. The last coordinate vanishes on `B`. -/
def assemble {z : B →ₗ[R] W} (p : Coordinates (A := A) (D := D) (C := C) z) :
    (B × C) →ₗ[R] (A × (W × D)) :=
  p.alpha.prod (p.psi.prod (p.v.comp (LinearMap.snd R B C)))

@[simp] theorem assemble_apply {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) (x : B × C) :
    assemble p x = (p.alpha x, p.psi x, p.v x.2) := rfl

@[simp] theorem compressBlock_assemble {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) :
    compressBlock (assemble p) = z.prod (0 : B →ₗ[R] D) := by
  apply LinearMap.ext
  intro b
  have hp : p.psi (b, 0) = z b :=
    congrArg (fun L : (B →ₗ[R] W) => L b) p.psi_left
  simp [compressBlock, assemble, hp]

/-- Extract the unique coordinates from an actual compressed-fiber element. -/
def extract (z : B →ₗ[R] W)
    (S : {S : (B × C) →ₗ[R] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[R] D)}) :
    Coordinates (A := A) (D := D) (C := C) z where
  alpha := (LinearMap.fst R A (W × D)).comp S.val
  psi := (LinearMap.fst R W D).comp ((LinearMap.snd R A (W × D)).comp S.val)
  psi_left := by
    apply LinearMap.ext
    intro b
    exact congrArg (fun L : B →ₗ[R] (W × D) => (L b).1) S.property
  v := (LinearMap.snd R W D).comp
    ((LinearMap.snd R A (W × D)).comp (S.val.comp (LinearMap.inr R B C)))

@[simp] theorem assemble_extract (z : B →ₗ[R] W)
    (S : {S : (B × C) →ₗ[R] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[R] D)}) :
    assemble (extract z S) = S.val := by
  apply LinearMap.ext
  rintro ⟨b, c⟩
  have hzero : (S.val (b, 0)).2.2 = 0 :=
    congrArg (fun L : B →ₗ[R] (W × D) => (L b).2) S.property
  have hlast : (S.val (b, c)).2.2 = (S.val (0, c)).2.2 := by
    calc
      _ = (S.val ((b, 0) + (0, c))).2.2 := by simp
      _ = (S.val (b, 0)).2.2 + (S.val (0, c)).2.2 := by rw [map_add]; rfl
      _ = _ := by rw [hzero, zero_add]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · exact hlast.symm

@[simp] theorem extract_assemble {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) :
    extract z ⟨assemble p, compressBlock_assemble p⟩ = p := by
  apply Coordinates.ext
  · apply LinearMap.ext
    intro x
    rfl
  · apply LinearMap.ext
    intro x
    rfl
  · apply LinearMap.ext
    intro c
    rfl

/-- An exact compressed-fiber parametrization, valid over any ring. -/
def compressedFiberEquiv (z : B →ₗ[R] W) :
    {S : (B × C) →ₗ[R] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[R] D)} ≃
      Coordinates (A := A) (D := D) (C := C) z where
  toFun := extract z
  invFun p := ⟨assemble p, compressBlock_assemble p⟩
  left_inv S := Subtype.ext (assemble_extract z S)
  right_inv := extract_assemble

end UniqueGamesTheorem.Inverse.KMSAnalyticHybridCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSAnalyticHybridCoordinatesRankLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The exact injection/surjection factorization of the adapted coordinates. -/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridCoordinates

variable {R A W D B C : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

/-- The small frequency map before its last coordinate is embedded into `D`. -/
def fullCoordinates {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) :
    (B × C) →ₗ[R] (A × (W × C)) :=
  p.alpha.prod (p.psi.prod (LinearMap.snd R B C))

/-- The injection chosen by the last block, keeping the first two blocks fixed. -/
def embedLast (v : C →ₗ[R] D) : (A × (W × C)) →ₗ[R] (A × (W × D)) :=
  (LinearMap.id : A →ₗ[R] A).prodMap ((LinearMap.id : W →ₗ[R] W).prodMap v)

@[simp] theorem embedLast_apply (v : C →ₗ[R] D) (x : A × (W × C)) :
    embedLast v x = (x.1, x.2.1, v x.2.2) := rfl

end UniqueGamesTheorem.Inverse.KMSAnalyticHybridCoordinates

end

section

/-!
# Partition frequencies by their actual image

A map with image `W` is uniquely a surjection onto `W`, followed by the
subspace inclusion. Consequently a sum over rank-`q` frequencies splits
exactly over dimension-`q` image subspaces and surjections onto each image.
The identities hold for arbitrary real weights and use no analytic estimate.
-/

noncomputable section

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical

variable {R B U : Type*} [Ring R]
  [AddCommGroup B] [Module R B] [AddCommGroup U] [Module R U]

/-- The inclusion of the target subspace preserves the prescribed image of
a surjective map. -/
theorem range_subtype_comp_of_surjective (W : Submodule R U)
    (z : B →ₗ[R] W) (hz : Function.Surjective z) :
    (W.subtype.comp z).range = W := by
  ext u
  constructor
  · rintro ⟨b, rfl⟩
    exact (z b).property
  · intro hu
    obtain ⟨b, hb⟩ := hz ⟨u, hu⟩
    exact ⟨b, congrArg Subtype.val hb⟩

/-- The full fixed-image fiber, with its canonical surjective coordinates. -/
def fixedImageEquivSurjection (W : Submodule R U) :
    {z : B →ₗ[R] U // z.range = W} ≃
      {z : B →ₗ[R] W // Function.Surjective z} where
  toFun z := ⟨z.val.codRestrict W (fun b => z.property.le (LinearMap.mem_range_self z.val b)), by
    intro w
    have hw : w.val ∈ z.val.range := z.property.symm ▸ w.property
    obtain ⟨b, hb⟩ := hw
    exact ⟨b, Subtype.ext hb⟩⟩
  invFun z := ⟨W.subtype.comp z.val, range_subtype_comp_of_surjective W z.val z.property⟩
  left_inv z := by
    apply Subtype.ext
    apply LinearMap.ext
    intro b
    rfl
  right_inv z := by
    apply Subtype.ext
    apply LinearMap.ext
    intro b
    apply Subtype.ext
    rfl

@[simp] theorem fixedImageEquivSurjection_symm_val (W : Submodule R U)
    (z : {z : B →ₗ[R] W // Function.Surjective z}) :
    ((fixedImageEquivSurjection W).symm z).val = W.subtype.comp z.val := rfl

@[simp] theorem fixedImageEquivSurjection_apply_coe (W : Submodule R U)
    (z : {z : B →ₗ[R] U // z.range = W}) (b : B) :
    ((fixedImageEquivSurjection W z).val b : U) = z.val b := rfl

/-- Frequencies of an exact rank. -/
abbrev ImageRankFrequency (q : ℕ) :=
  {z : B →ₗ[R] U // Module.finrank R z.range = q}

/-- Actual image subspaces of the required dimension. -/
abbrev RankImage (R U : Type*) [Ring R] [AddCommGroup U] [Module R U] (q : ℕ) :=
  {W : Submodule R U // Module.finrank R W = q}

/-- The image classification of an exact-rank frequency. -/
def frequencyImage (q : ℕ) (z : ImageRankFrequency (R := R) (B := B) (U := U) q) :
    RankImage R U q := ⟨z.val.range, z.property⟩

/-- Removing the redundant rank certificate from a fixed-image fiber. -/
def frequencyImageFiberEquiv (q : ℕ) (W : RankImage R U q) :
    {z : ImageRankFrequency (R := R) (B := B) (U := U) q // frequencyImage q z = W} ≃
      {z : B →ₗ[R] U // z.range = W.val} where
  toFun z := ⟨z.val.val, congrArg Subtype.val z.property⟩
  invFun z := ⟨⟨z.val, by rw [z.property]; exact W.property⟩, Subtype.ext z.property⟩
  left_inv z := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; rfl

/-- Exact rank frequencies are in bijection with a choice of actual image
and a surjective map onto it. -/
def rankFrequencyImageEquiv (q : ℕ) :
    ImageRankFrequency (R := R) (B := B) (U := U) q ≃
      Σ W : RankImage R U q, {z : B →ₗ[R] W.val // Function.Surjective z} :=
  (Equiv.sigmaFiberEquiv (frequencyImage (R := R) (B := B) (U := U) q)).symm.trans
    (Equiv.sigmaCongrRight fun W =>
      (frequencyImageFiberEquiv q W).trans (fixedImageEquivSurjection W.val))

@[simp] theorem rankFrequencyImageEquiv_symm_val (q : ℕ)
    (p : Σ W : RankImage R U q, {z : B →ₗ[R] W.val // Function.Surjective z}) :
    ((rankFrequencyImageEquiv q).symm p).val = p.1.val.subtype.comp p.2.val := rfl

section ImageCoordinates

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Coordinates adapted to a prescribed image and any chosen complement. -/
def imageCoordinates (W D : Submodule K V) (h : IsCompl W D) : V ≃ₗ[K] (W × D) :=
  (Submodule.prodEquivOfIsCompl W D h).symm

/-- Vectors in the prescribed image have zero complementary coordinate. -/
@[simp] theorem imageCoordinates_subtype (W D : Submodule K V) (h : IsCompl W D)
    (w : W) : imageCoordinates W D h (w : V) = (w, 0) :=
  Submodule.prodEquivOfIsCompl_symm_apply_left W D h w

end ImageCoordinates
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end

section

/-!
# Fixed kernels and injective quotient maps

Linear maps with a prescribed kernel are in explicit bijection with injective
maps from the corresponding quotient. This elementary counting foundation
works over any ring, and in particular over the binary field used by KMS.
No expansion or rank-level estimate is assumed.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticKernelCount

noncomputable section

variable {R E F : Type*} [Ring R]
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

/-- Composing an injective map with the quotient projection has exactly the
prescribed kernel. -/
theorem ker_comp_mkQ (K : Submodule R F) (J : (F ⧸ K) →ₗ[R] E)
    (hJ : Function.Injective J) : (J.comp K.mkQ).ker = K := by
  rw [LinearMap.ker_comp_of_ker_eq_bot K.mkQ (LinearMap.ker_eq_bot.mpr hJ),
    Submodule.ker_mkQ]

/-- Every map with kernel `K` factors uniquely through an injective quotient
map; the inverse sends that quotient map to its composition with `K.mkQ`. -/
def fixedKernelEquivQuotientInjection (K : Submodule R F) :
    {S : F →ₗ[R] E // S.ker = K} ≃
      {J : (F ⧸ K) →ₗ[R] E // Function.Injective J} where
  toFun S := ⟨K.liftQ S.val S.property.symm.le,
    LinearMap.ker_eq_bot.mp (K.ker_liftQ_eq_bot S.val _ S.property.le)⟩
  invFun J := ⟨J.val.comp K.mkQ, ker_comp_mkQ K J.val J.property⟩
  left_inv S := by
    apply Subtype.ext
    exact K.liftQ_mkQ S.val _
  right_inv J := by
    apply Subtype.ext
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := K.mkQ_surjective q
    rfl

@[simp]
theorem fixedKernelEquiv_apply_mkQ (K : Submodule R F)
    (S : {S : F →ₗ[R] E // S.ker = K}) (x : F) :
    (fixedKernelEquivQuotientInjection K S).val (K.mkQ x) = S.val x := rfl

@[simp]
theorem fixedKernelEquiv_symm_apply (K : Submodule R F)
    (J : {J : (F ⧸ K) →ₗ[R] E // Function.Injective J}) :
    ((fixedKernelEquivQuotientInjection K).symm J).val = J.val.comp K.mkQ := rfl

/-- Quotient factorization leaves the image subspace unchanged. -/
theorem range_forward (K : Submodule R F)
    (S : {S : F →ₗ[R] E // S.ker = K}) :
    (fixedKernelEquivQuotientInjection K S).val.range = S.val.range :=
  K.range_liftQ S.val _

/-- A prescribed kernel fixes the rank to the dimension of its quotient. -/
theorem fixedKernel_finrank_eq_quotient (K : Submodule R F)
    (S : {S : F →ₗ[R] E // S.ker = K}) :
    Module.finrank R S.val.range = Module.finrank R (F ⧸ K) := by
  rw [← range_forward K S]
  exact LinearMap.finrank_range_of_inj (fixedKernelEquivQuotientInjection K S).property

end
end UniqueGamesTheorem.Inverse.KMSAnalyticKernelCount

end

section

/-!
Binary linear functionals are determined by their kernels. The statement
includes the zero functional; no choice of a nonzero normalization is needed.
Injective linear images retain the same uniqueness property.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

variable {E F : Type*}
  [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]

/-- A binary functional is determined by its zero set. -/
theorem binary_functional_eq_of_ker_eq
    {a b : E →ₗ[ZMod 2] ZMod 2} (h : a.ker = b.ker) : a = b := by
  have scalar_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  apply LinearMap.ext
  intro x
  have hzero : a x = 0 ↔ b x = 0 := by
    change x ∈ a.ker ↔ x ∈ b.ker
    rw [h]
  rcases scalar_cases (a x) with ha | ha
  · exact ha.trans (hzero.mp ha).symm
  · rcases scalar_cases (b x) with hb | hb
    · exact False.elim (zero_ne_one ((hzero.mpr hb).symm.trans ha))
    · exact ha.trans hb.symm

/-- The image of a binary functional's kernel under an injective linear map
still determines that functional uniquely. -/
theorem binary_functional_eq_of_map_ker_eq
    (X : E →ₗ[ZMod 2] F) (hX : Function.Injective X)
    {a b : E →ₗ[ZMod 2] ZMod 2}
    (h : a.ker.map X = b.ker.map X) : a = b := by
  exact binary_functional_eq_of_ker_eq (Submodule.map_injective_of_injective hX h)

end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

section

/-!
# Equal fibers for restricted basis completion

A fixed independent tuple may have vectors outside the restricting submodule.
Nevertheless, any two nonempty fibers of independent completions inside that
submodule are equivalent. The change of basis fixes the fixed tuple, and its
difference from the identity has image in the restricting submodule.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparisonPseudorandom

noncomputable section
open scoped Classical

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {q t : ℕ}

/-- Ordered completions in `W` of `Q` to an independent spanning tuple for `L`. -/
def RestrictedCompletion (Q : Fin q → V) (W L : Submodule K V) :=
  {z : Fin t → W //
    LinearIndependent K (Sum.elim Q (fun i => (z i : V))) ∧
      Submodule.span K (Set.range (Sum.elim Q (fun i => (z i : V)))) = L}

variable {Q : Fin q → V} {W L M N : Submodule K V}

/-- A completion, regarded as a basis of the resulting subspace. -/
def completionBasis (z : RestrictedCompletion (t := t) Q W L) :
    Module.Basis (Fin q ⊕ Fin t) K L :=
  (Module.Basis.span z.property.1).map (LinearEquiv.ofEq _ _ z.property.2)

@[simp] theorem completionBasis_coe
    (z : RestrictedCompletion (t := t) Q W L) (i : Fin q ⊕ Fin t) :
    (completionBasis z i : V) = Sum.elim Q (fun j => (z.val j : V)) i := by
  simp [completionBasis]

/-- Recover a restricted completion from a basis having the prescribed prefix. -/
def completionOfBasis (b : Module.Basis (Fin q ⊕ Fin t) K L)
    (hQ : ∀ i, (b (Sum.inl i) : V) = Q i)
    (hW : ∀ i, (b (Sum.inr i) : V) ∈ W) :
    RestrictedCompletion (t := t) Q W L := by
  have hb : Sum.elim Q (fun i => ((⟨b (Sum.inr i), hW i⟩ : W) : V)) =
      fun i => (b i : V) := by
    funext i
    cases i with
    | inl i => exact (hQ i).symm
    | inr i => rfl
  refine ⟨fun i => ⟨b (Sum.inr i), hW i⟩, ?_, ?_⟩
  · rw [hb]
    exact b.linearIndependent.map' L.subtype (by simp)
  · rw [hb]
    calc
      Submodule.span K (Set.range fun i => (b i : V)) =
          (Submodule.span K (Set.range b)).map L.subtype := by
        rw [Submodule.map_span, ← Set.range_comp]
        rfl
      _ = L := by rw [b.span_eq]; simp

/-- The unique basis change carrying the first completion to the second. -/
def completionSpanEquiv
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) : L ≃ₗ[K] M :=
  (completionBasis x).equiv (completionBasis y) (Equiv.refl _)

@[simp] theorem completionSpanEquiv_basis
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) (i : Fin q ⊕ Fin t) :
    completionSpanEquiv x y (completionBasis x i) = completionBasis y i := by
  simp [completionSpanEquiv]

@[simp] theorem completionSpanEquiv_symm
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) :
    (completionSpanEquiv x y).symm = completionSpanEquiv y x := by
  simp [completionSpanEquiv]

/-- Changing the completion changes every vector by an element of `W`. -/
theorem completionSpanEquiv_sub_mem
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) (v : L) :
    (completionSpanEquiv x y v : V) - (v : V) ∈ W := by
  let d : L →ₗ[K] V := M.subtype.comp (completionSpanEquiv x y).toLinearMap - L.subtype
  have hd : (⊤ : Submodule K L) ≤ W.comap d := by
    rw [← (completionBasis x).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change d (completionBasis x i) ∈ W
    change (completionSpanEquiv x y (completionBasis x i) : V) -
      (completionBasis x i : V) ∈ W
    rw [completionSpanEquiv_basis]
    cases i with
    | inl i => simp
    | inr i =>
      simpa only [completionBasis_coe, Sum.elim_inr] using
        W.sub_mem (y.val i).property (x.val i).property
  exact hd (Submodule.mem_top : v ∈ (⊤ : Submodule K L))

/-- The basis change preserves membership in `W`, without requiring `Q ⊆ W`. -/
theorem completionSpanEquiv_mem_iff
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) (v : L) :
    (completionSpanEquiv x y v : V) ∈ W ↔ (v : V) ∈ W := by
  have hd := completionSpanEquiv_sub_mem x y v
  constructor
  · intro hv
    exact (W.sub_mem_iff_right hv).mp hd
  · intro hv
    exact (W.sub_mem_iff_left hv).mp hd

/-- Transport every restricted completion along one fixed basis change. -/
def transportCompletion
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M)
    (z : RestrictedCompletion (t := t) Q W L) :
    RestrictedCompletion (t := t) Q W M :=
  completionOfBasis ((completionBasis z).map (completionSpanEquiv x y))
    (by
      intro i
      have h : completionBasis z (Sum.inl i) = completionBasis x (Sum.inl i) := by
        apply Subtype.ext
        simp
      simp [Module.Basis.map_apply, h])
    (by
      intro i
      change (completionSpanEquiv x y (completionBasis z (Sum.inr i)) : V) ∈ W
      apply (completionSpanEquiv_mem_iff x y _).mpr
      simp)

@[simp] theorem transportCompletion_coe
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M)
    (z : RestrictedCompletion (t := t) Q W L) (i : Fin t) :
    ((transportCompletion x y z).val i : V) =
      (completionSpanEquiv x y (completionBasis z (Sum.inr i)) : V) := rfl

theorem transportCompletion_inverse
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M)
    (z : RestrictedCompletion (t := t) Q W L) :
    transportCompletion y x (transportCompletion x y z) = z := by
  apply Subtype.ext
  funext i
  apply Subtype.ext
  rw [transportCompletion_coe]
  have hb : completionBasis (transportCompletion x y z) (Sum.inr i) =
      completionSpanEquiv x y (completionBasis z (Sum.inr i)) := by
    apply Subtype.ext
    simp
  rw [hb, ← completionSpanEquiv_symm, LinearEquiv.symm_apply_apply]
  simp

/-- All nonempty restricted-completion fibers are equivalent. -/
def restrictedCompletionEquiv
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) :
    RestrictedCompletion (t := t) Q W L ≃ RestrictedCompletion (t := t) Q W M where
  toFun := transportCompletion x y
  invFun := transportCompletion y x
  left_inv := transportCompletion_inverse x y
  right_inv := transportCompletion_inverse y x

end
end UniqueGamesTheorem.Inverse.KMSBasisComparisonPseudorandom

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSAffineRestrictionPresentationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Actual Hybrid derivative energy in product coordinates

Parseval and affine restriction merge the selected Fourier coefficients over
each actual compressed frequency. For a product splitting, explicit linear
equivalences identify the quotient by the first factor with the second factor,
and the first-factor subspace with its original space. Reindexing the frequency
sum therefore introduces no multiplicity or normalization factor.
-/

noncomputable section

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical

section ProductEquivalences

variable {R A U B C : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup U] [Module R U]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]

/-- The second projection descends through the first-factor quotient. -/
def quotientRightMap :
    ((A × U) ⧸ LinearMap.range (LinearMap.inl R A U)) →ₗ[R] U :=
  (LinearMap.range (LinearMap.inl R A U)).liftQ (LinearMap.snd R A U) (by
    rintro x ⟨a, rfl⟩
    rfl)

end ProductEquivalences

end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSFourthMomentMixedScalarLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Scalar accounting for the genuine point-restriction induction. All ambient
weights remain explicit. A global rank cap R gives a dimension-independent
factor per fixed point; the proof does not assume any mixed-norm estimate.
-/

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment

/-- A deliberately generous rank-dependent cost for one fixed point. -/
def mixedStepFactor (R : ℕ) : ℝ := 2 ^ (2 * R + 2)

end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

section

/-! Exact counts of injective binary linear maps. Evaluating a map on a
chosen domain basis is a bijection with linearly independent image families.
The count uses the proved finite-field independent-family enumeration. -/

namespace UniqueGamesTheorem.Inverse.KMSInjectionCount

open scoped BigOperators

noncomputable section

abbrev F2 := ZMod 2

variable (I E : Type*) [AddCommGroup I] [Module F2 I]
  [AddCommGroup E] [Module F2 E]

/-- The actual number of injective linear maps, with no asymptotic convention. -/
def beta : ℕ := Nat.card {J : I →ₗ[F2] E // Function.Injective J}

/-- A domain basis turns injective maps into independent image families. -/
def injectiveEquivIndependent {ι : Type*} (b : Module.Basis ι F2 I) :
    {J : I →ₗ[F2] E // Function.Injective J} ≃
      {s : ι → E // LinearIndependent F2 s} where
  toFun J := ⟨J.val ∘ b, b.linearIndependent.map' J.val (LinearMap.ker_eq_bot.mpr J.property)⟩
  invFun s := ⟨b.constr F2 s.val, b.injective_constr_of_linearIndependent s.property⟩
  left_inv J := by
    apply Subtype.ext
    exact b.constr_self F2 J.val
  right_inv s := by
    apply Subtype.ext
    funext i
    exact b.constr_basis F2 s.val i

end
end UniqueGamesTheorem.Inverse.KMSInjectionCount

end

section

/-!
The common kernel index for binary maps of fixed rank and for surjective maps
to a fixed comparison space. Both maps below send an actual linear map to its
literal kernel; quotient dimensions follow from the first isomorphism theorem.
-/

namespace UniqueGamesTheorem.Inverse.KMSKernelFiberCard

noncomputable section

abbrev F2 := ZMod 2

variable (F E I : Type*)
  [AddCommGroup F] [Module F2 F]
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup I] [Module F2 I]

abbrev KernelClass :=
  {K : Submodule F2 F // Module.finrank F2 (F ⧸ K) = Module.finrank F2 I}

abbrev RankFrequency :=
  {S : F →ₗ[F2] E // Module.finrank F2 S.range = Module.finrank F2 I}

abbrev FullFrequency := {T : F →ₗ[F2] I // Function.Surjective T}

variable {F E I}

def rankKernel (S : RankFrequency F E I) : KernelClass F I :=
  ⟨S.val.ker, S.val.quotKerEquivRange.finrank_eq.trans S.property⟩

def fullKernel (T : FullFrequency F I) : KernelClass F I :=
  ⟨T.val.ker, (T.val.quotKerEquivOfSurjective T.property).finrank_eq⟩

@[simp] theorem rankKernel_val (S : RankFrequency F E I) :
    (rankKernel S).val = S.val.ker := rfl

@[simp] theorem fullKernel_val (T : FullFrequency F I) :
    (fullKernel T).val = T.val.ker := rfl

end
end UniqueGamesTheorem.Inverse.KMSKernelFiberCard

end

section

/-!
Every kernel class is realized by both families of maps. The witnesses are
constructed from a linear equivalence of the quotient with the comparison
space, followed (for the rank family) by an injection into the ambient space.
No uniformity or fiber-count assertion is assumed.
-/

namespace UniqueGamesTheorem.Inverse.KMSKernelFiberCard

open KMSAnalyticKernelCount

noncomputable section

variable {F E I : Type*}
  [AddCommGroup F] [Module F2 F] [FiniteDimensional F2 F]
  [AddCommGroup E] [Module F2 E] [FiniteDimensional F2 E]
  [AddCommGroup I] [Module F2 I] [FiniteDimensional F2 I]

/-- Equal quotient dimension gives an actual linear equivalence. -/
def quotientEquiv (K : KernelClass F I) : (F ⧸ K.val) ≃ₗ[F2] I :=
  Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq K.property)

end
end UniqueGamesTheorem.Inverse.KMSKernelFiberCard

end

section

/-!
Exact kernel-fiber cardinalities. Factoring through the actual quotient turns
the fixed-kernel fiber into injections, and a quotient equivalence identifies
these with the binary injection count. Restricting to the prescribed rank or
to surjections does not remove any member of the corresponding fiber.
-/

namespace UniqueGamesTheorem.Inverse.KMSKernelFiberCard

open KMSAnalyticKernelCount KMSInjectionCount
open scoped Classical

noncomputable section

variable {F E I J : Type*}
  [AddCommGroup F] [Module F2 F]
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup J] [Module F2 J]

/-- Changing the domain by a linear equivalence preserves the set of actual
injective linear maps. -/
def injectionEquivOfDomainEquiv (e : J ≃ₗ[F2] I) :
    {u : J →ₗ[F2] E // Function.Injective u} ≃
      {u : I →ₗ[F2] E // Function.Injective u} where
  toFun u := ⟨u.val.comp e.symm.toLinearMap, u.property.comp e.symm.injective⟩
  invFun u := ⟨u.val.comp e.toLinearMap, u.property.comp e.injective⟩
  left_inv u := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change u.val (e.symm (e x)) = u.val x
    rw [e.symm_apply_apply]
  right_inv u := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change u.val (e (e.symm x)) = u.val x
    rw [e.apply_symm_apply]

variable [FiniteDimensional F2 F] [FiniteDimensional F2 I]

/-- A fixed-kernel fiber is in explicit bijection with injections from the
comparison space. This includes the zero-dimensional comparison space. -/
def fixedKernelEquivInjection (K : KernelClass F I) :
    {S : F →ₗ[F2] E // S.ker = K.val} ≃
      {J : I →ₗ[F2] E // Function.Injective J} :=
  (fixedKernelEquivQuotientInjection K.val).trans
    (injectionEquivOfDomainEquiv (quotientEquiv K))

/-- The kernel condition already forces the rank condition. -/
def rankFiberEquivFixedKernel (K : KernelClass F I) :
    {S : RankFrequency F E I // rankKernel S = K} ≃
      {S : F →ₗ[F2] E // S.ker = K.val} where
  toFun S := ⟨S.val.val, congrArg Subtype.val S.property⟩
  invFun S := ⟨⟨S.val,
    (fixedKernel_finrank_eq_quotient K.val S).trans K.property⟩,
    Subtype.ext S.property⟩
  left_inv S := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv S := by
    apply Subtype.ext
    rfl

omit [FiniteDimensional F2 F] in
/-- A map into the comparison space with this kernel has full range. -/
theorem surjective_of_kernel_class (K : KernelClass F I)
    (T : F →ₗ[F2] I) (hT : T.ker = K.val) : Function.Surjective T := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  exact (fixedKernel_finrank_eq_quotient K.val ⟨T, hT⟩).trans K.property

/-- The kernel condition already forces surjectivity onto the comparison
space. -/
def fullFiberEquivFixedKernel (K : KernelClass F I) :
    {T : FullFrequency F I // fullKernel T = K} ≃
      {T : F →ₗ[F2] I // T.ker = K.val} where
  toFun T := ⟨T.val.val, congrArg Subtype.val T.property⟩
  invFun T := ⟨⟨T.val, surjective_of_kernel_class K T.val T.property⟩,
    Subtype.ext T.property⟩
  left_inv T := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv T := by
    apply Subtype.ext
    rfl

end
end UniqueGamesTheorem.Inverse.KMSKernelFiberCard

end

section

/-!
Equal kernels give the same orbit under invertible postcomposition.
The canonical range equivalence comes from the first isomorphism theorem;
Mathlib's finite-dimensional subspace extension theorem then extends it to an
automorphism of the ambient codomain. No orbit or counting premise is assumed.
-/

namespace UniqueGamesTheorem.Inverse.KMSKernelOrbits

noncomputable section

variable {K E F : Type*} [DivisionRing K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

/-- The range identification induced by a common kernel. -/
def rangeEquivOfKerEq (S T : F →ₗ[K] E) (hker : S.ker = T.ker) :
    S.range ≃ₗ[K] T.range :=
  S.quotKerEquivRange.symm ≪≫ₗ
    Submodule.quotEquivOfEq S.ker T.ker hker ≪≫ₗ T.quotKerEquivRange

end
end UniqueGamesTheorem.Inverse.KMSKernelOrbits

end

section

namespace UniqueGamesTheorem.Inverse.KMSMomentScalar

noncomputable section
open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

def IsBoolean (f : X → ℝ) : Prop := ∀ x, f x = 0 ∨ f x = 1

end
end UniqueGamesTheorem.Inverse.KMSMomentScalar

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSFoundationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.KMS

noncomputable section
open scoped BigOperators Classical

section FiniteDensity

variable {Ω : Type*} [DecidableEq Ω]

/-- Relative density, with value zero when the conditioning set is empty. -/
def relativeDensity (S I : Finset Ω) : ℝ :=
  ((S ∩ I).card : ℝ) / I.card

end FiniteDensity

end
end UniqueGamesTheorem.Inverse.KMS

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_MatrixChartLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.MatrixChart

variable {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

/-- The lower end of an interval is given by a spanning list of graph vectors. -/
def lowerRows {ι : Type*} (d : ι → X) (s : ι → Y) : Submodule K (X × Y) :=
  Submodule.span K (Set.range fun i => (d i, s i))

def upperColumns {ι : Type*} (t : ι → X →ₗ[K] K) (q : ι → Y →ₗ[K] K) :
    Submodule K (X × Y) :=
  ⨅ i, LinearMap.ker ((q i).comp (LinearMap.snd K X Y) -
    (t i).comp (LinearMap.fst K X Y))

end UniqueGamesTheorem.Inverse.MatrixChart

end

section

/-!
Exact finite counts for the Grassmann graph comparison in Section 4.
The quotient-line parametrization is independent of any expansion theorem.
-/

namespace UniqueGamesTheorem.Inverse.MatrixChart

open Module

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- One-dimensional vector subspaces. -/
abbrev Lines (K E : Type*) [Field K] [AddCommGroup E] [Module K E] :=
  {L : Submodule K E // finrank K L = 1}

/-- Hyperplanes, expressed without truncated dimension subtraction. -/
abbrev Hyperplanes (K E : Type*) [Field K] [AddCommGroup E] [Module K E] :=
  {H : Submodule K E // finrank K H + 1 = finrank K E}

/-- Dual annihilation bijects hyperplanes with lines in the dual space. -/
noncomputable def hyperplanesEquivDualLines [FiniteDimensional K E] :
    Hyperplanes K E ≃ Lines K (Module.Dual K E) where
  toFun H := ⟨H.val.dualAnnihilator, by
    have h := Subspace.finrank_add_finrank_dualAnnihilator_eq H.val
    have hH := H.property
    omega⟩
  invFun L := ⟨L.val.dualCoannihilator, by
    have h := Subspace.finrank_add_finrank_dualCoannihilator_eq L.val
    rw [L.property] at h
    omega⟩
  left_inv H := by
    apply Subtype.ext
    exact Subspace.dualAnnihilator_dualCoannihilator_eq
  right_inv L := by
    apply Subtype.ext
    exact Subspace.dualCoannihilator_dualAnnihilator_eq

/-- A dimension identity for the quotient correspondence, retaining addition. -/
theorem finrank_map_mkQ_add [FiniteDimensional K E]
    (H W : Submodule K E) (hHW : H ≤ W) :
    finrank K (W.map H.mkQ) + finrank K H = finrank K W := by
  have h := LinearMap.finrank_range_add_finrank_ker (H.mkQ.comp W.subtype)
  have hr : LinearMap.range (H.mkQ.comp W.subtype) = W.map H.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk : LinearMap.ker (H.mkQ.comp W.subtype) = H.comap W.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  rw [hr, hk, (Submodule.comapSubtypeEquivOfLe hHW).finrank_eq] at h
  exact h

/-- One-dimensional extensions of a subspace. -/
abbrev Extensions (H : Submodule K E) :=
  {W : Submodule K E // H ≤ W ∧ finrank K W = finrank K H + 1}

/-- The quotient correspondence identifies extensions with quotient lines. -/
noncomputable def extensionsEquivLines [FiniteDimensional K E]
    (H : Submodule K E) : Extensions H ≃ Lines K (E ⧸ H) where
  toFun W := ⟨W.val.map H.mkQ, by
    have h := finrank_map_mkQ_add H W.val W.property.1
    rw [W.property.2] at h
    omega⟩
  invFun L := ⟨L.val.comap H.mkQ, Submodule.le_comap_mkQ H L.val, by
    have h := finrank_map_mkQ_add H (L.val.comap H.mkQ)
      (Submodule.le_comap_mkQ H L.val)
    have heq : (L.val.comap H.mkQ).map H.mkQ = L.val :=
      Submodule.map_comap_eq_self (by simp)
    rw [heq, L.property] at h
    omega⟩
  left_inv W := by
    apply Subtype.ext
    simp [Submodule.comap_map_mkQ, sup_eq_right.mpr W.property.1]
  right_inv L := by
    apply Subtype.ext
    exact Submodule.map_comap_eq_self (by simp)

end UniqueGamesTheorem.Inverse.MatrixChart

end

section

/-!
The full Grassmann degree, by choosing the intersection hyperplane and a
different one-dimensional extension. No graph regularity is assumed.
-/

namespace UniqueGamesTheorem.Inverse.MatrixChart

open Module

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

abbrev HyperplanesBelow (L : Submodule K E) :=
  {H : Submodule K E // H ≤ L ∧ finrank K H + 1 = finrank K L}

noncomputable def hyperplanesBelowEquiv (L : Submodule K E) :
    HyperplanesBelow L ≃ Hyperplanes K L where
  toFun H := ⟨H.val.comap L.subtype, by
    rw [(Submodule.comapSubtypeEquivOfLe H.property.1).finrank_eq]
    exact H.property.2⟩
  invFun H := ⟨H.val.map L.subtype, Submodule.map_subtype_le L H.val, by
    rw [Submodule.finrank_map_subtype_eq]
    exact H.property⟩
  left_inv H := by
    apply Subtype.ext
    simp [Submodule.map_comap_subtype, inf_eq_right.mpr H.property.1]
  right_inv H := by
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective Subtype.val_injective H.val

/-- Distinct one-dimensional extensions intersect in their common base. -/
theorem inf_eq_base_of_distinct_extensions [FiniteDimensional K E]
    (H L W : Submodule K E) (hHL : H ≤ L) (hHW : H ≤ W)
    (hL : finrank K L = finrank K H + 1)
    (hW : finrank K W = finrank K H + 1) (hWL : W ≠ L) :
    L ⊓ W = H := by
  apply le_antisymm
  · by_contra hn
    have hlt : H < L ⊓ W := lt_of_le_of_ne (le_inf hHL hHW) (by
      intro heq
      exact hn heq.ge)
    have hd := Submodule.finrank_lt_finrank_of_lt hlt
    have hi := Submodule.finrank_mono (show L ⊓ W ≤ L from inf_le_left)
    have heq : L ⊓ W = L := Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
    have hLW : L ≤ W := by rw [← heq]; exact inf_le_right
    exact hWL (Submodule.eq_of_le_of_finrank_eq hLW (hL.trans hW.symm)).symm
  · exact le_inf hHL hHW

abbrev NeighborExtensionData (L : Submodule K E) :=
  (H : HyperplanesBelow L) × {W : Extensions H.val // W.val ≠ L}

end UniqueGamesTheorem.Inverse.MatrixChart

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_MatrixChartIntervalsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
For a fixed nonzero binary functional, all updates with a prescribed image
form one affine coset of the image of its kernel. This is an exact fiber
equivalence, so it retains the multiplicities needed for uniform sampling.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]

/-- Vectors external to the starting image which give the same updated image. -/
abbrev FixedFunctionalNeighborFiber (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) (y₀ : F) :=
  {y : F // y ∉ X.range ∧
    (X + a.smulRight y).range = (X + a.smulRight y₀).range}

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

section

/-!
The complete pair fiber of the ordered-basis neighbor sampler. Equal updated
images determine the binary functional exactly. The remaining ambiguity is
the affine kernel coset, of cardinality `2 ^ (dim E - 1)`.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]

abbrev OutsideNeighborFactors (X : E →ₗ[ZMod 2] F) :=
  {a : E →ₗ[ZMod 2] ZMod 2 // a ≠ 0} × {y : F // y ∉ X.range}

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

section

/-! Exact chart-to-Grassmann degree comparison over the binary field. -/

namespace UniqueGamesTheorem.Inverse.MatrixChart

open Module

variable {ell m : ℕ}

abbrev CoordinateMatrix (ell m : ℕ) :=
  (Fin ell → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)

end UniqueGamesTheorem.Inverse.MatrixChart

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSBasisComparisonLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Constant ordered-basis fibers

An injective linear map with a fixed range is exactly an ordered basis of that
range. Choosing one such basis identifies this fiber with the automorphisms of
the domain. The generic finite-fiber lemma below proves uniformity, including
the complete normalization in the rational density identity.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

noncomputable section
open scoped BigOperators Classical

section UniformFibers

variable {X Y G : Type*}

/-- Trivializing equal-size fibers identifies the full sample space with a
product; the first coordinate remains the original quotient map. -/
def fiberProductEquiv (f : X → Y) (e : ∀ y, {x : X // f x = y} ≃ G) : X ≃ Y × G :=
  (Equiv.sigmaFiberEquiv f).symm.trans (Equiv.sigmaEquivProdOfEquiv e)

@[simp] theorem fiberProductEquiv_fst (f : X → Y)
    (e : ∀ y, {x : X // f x = y} ≃ G) (x : X) :
    (fiberProductEquiv f e x).1 = f x := rfl

end UniformFibers

section LinearFibers

variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]

/-- The actual fiber of injective maps over a specified range subspace. -/
def RangeFiber (L : Submodule K F) :=
  {X : E →ₗ[K] F // Function.Injective X ∧ LinearMap.range X = L}

/-- A range fiber is the set of linear equivalences onto that range. -/
def rangeFiberEquiv (L : Submodule K F) : RangeFiber (E := E) L ≃ (E ≃ₗ[K] L) where
  toFun X := LinearEquiv.ofBijective
    (X.val.codRestrict L (fun x =>
      X.property.2.le (LinearMap.mem_range_self X.val x)))
    ⟨fun _ _ h => X.property.1 (congrArg Subtype.val h), by
      intro y
      have hy : (y : F) ∈ LinearMap.range X.val := X.property.2.ge y.property
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩⟩
  invFun e := ⟨L.subtype.comp e.toLinearMap,
    (Submodule.subtype_injective L).comp e.injective, by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact (e x).property
      · intro hy
        obtain ⟨x, hx⟩ := e.surjective ⟨y, hy⟩
        exact ⟨x, congrArg Subtype.val hx⟩⟩
  left_inv X := by
    apply Subtype.ext
    ext x
    rfl
  right_inv e := by
    ext x
    rfl

/-- After choosing one basis of a subspace, its ordered-basis fiber is exactly
the domain's automorphism group. -/
def rangeFiberEquivAut {L : Submodule K F} (e : E ≃ₗ[K] L) :
    RangeFiber (E := E) L ≃ (E ≃ₗ[K] E) :=
  (rangeFiberEquiv L).trans
    { toFun := fun a => a.trans e.symm
      invFun := fun a => a.trans e
      left_inv := by intro a; ext x; simp
      right_inv := by intro a; ext x; simp }

end LinearFibers

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSKernelOrbitsFourierLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact coefficient arrays in an adapted hybrid fiber. -/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy
noncomputable section
open scoped BigOperators Classical
open KMSAnalyticHybridCoordinates

variable {R A W D B C : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

/-- The unnormalized fiber of extensions of one compressed frequency. -/
abbrev Extension (z : B →ₗ[R] W) :=
  {ψ : (B × C) →ₗ[R] W // ψ.comp (LinearMap.inl R B C) = z}

/-- The coordinate record has precisely three independent entries. -/
def coordinatesDataEquiv (z : B →ₗ[R] W) :
    Coordinates (A := A) (D := D) (C := C) z ≃
      ((B × C) →ₗ[R] A) × (Extension (C := C) z) × (C →ₗ[R] D) where
  toFun p := (p.alpha, ⟨p.psi, p.psi_left⟩, p.v)
  invFun p := ⟨p.1, p.2.1.val, p.2.1.property, p.2.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by rcases p with ⟨a, ⟨ψ, hψ⟩, v⟩; rfl

def compressedFiberDataEquiv (z : B →ₗ[R] W) :
    {S : (B × C) →ₗ[R] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[R] D)} ≃
      ((B × C) →ₗ[R] A) × (Extension (C := C) z) × (C →ₗ[R] D) :=
  (compressedFiberEquiv z).trans (coordinatesDataEquiv z)

end
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSAnalyticHybridEnergyImageTransportLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Product Hybrid energy from actual mixed slices

The derivative's exact rank support is partitioned by its actual compressed
image. Each image is put in complement coordinates, and the proved coefficient
factorization bounds that contribution by an actual mixed slice. The finite
image, extension, and complementary-map counts fit the mixed denominator.
The sole analytic premise is the displayed uniform bound on actual slices.
-/

noncomputable section

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open KMSFourthMoment

local instance (priority := 2000) classicalSurjective {X Y : Type*} :
    DecidablePred (Function.Surjective : (X → Y) → Prop) :=
  fun g => Classical.propDecidable (Function.Surjective g)

end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSLowLevelLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The spectral cutoff step of KMS on the actual full uniform rank-one noise.
The low-level fourth-moment estimate remains an explicit input to the last
combining lemma; none of these statements asserts that estimate or expansion.
The multiplier is reused from the proved uniform-subspace kernel count.
-/

namespace UniqueGamesTheorem.Inverse.KMSLowLevel
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Inverse.KMSMomentScalar

section FiniteCutoff
variable {I : Type*} [Fintype I]

def rankEnergy (rank : I → ℕ) (a : I → ℝ) (i : ℕ) : ℝ :=
  ∑ s, if rank s = i then a s ^ 2 else 0

end FiniteCutoff

end
end UniqueGamesTheorem.Inverse.KMSLowLevel

end

section

/-!
The closed KMS mixed restriction estimate. The fixed-character base in the
point induction is discharged by the actual homogeneous character theorem.
Only basis invariance and the transparent local affine squared-density bound
remain; no Fourier-energy or missing-estimate premise occurs here.
-/

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical

universe u v

variable {E A I J : Type u}
  {F : Type v}
  [AddCommGroup E]
  [AddCommGroup A]
  [AddCommGroup I]
  [AddCommGroup J]
  [AddCommGroup F]
  [Fintype E]
  [Fintype A]
  [Fintype I]
  [Fintype J]
  [Fintype F]

/-- A single uniform constant for all fixed-point dimensions at rank at most R. -/
def mixedRankConstant (R : ℕ) : ℝ := (2 : ℝ) ^ (4 * R * R) * mixedStepFactor R ^ R

end
end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_RowErasureLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.RowErasure

open scoped BigOperators

noncomputable section

/-- One independent replacement value per matrix entry, not per row fiber. -/
def replaceOn {X Y : Type*} (B : X → Prop) (f replacement : X → Y) : X → Y := by
  classical
  exact fun x => if B x then replacement x else f x

/-- A matrix belongs to the erased union exactly when at least one row map
provides good advice there. -/
def goodUnion {A X : Type*} (good : A → X → Prop) (x : X) : Prop :=
  ∃ a, good a x

end
end UniqueGamesTheorem.Inverse.RowErasure

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_RowErasureMatrixLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finite partition estimates for a selector fixed by visible data. The observation
fibers need not have equal sizes. Each local counting inequality is summed over
the actual fibers, then divided by the size of the hidden sample space.
-/

namespace UniqueGamesTheorem.Inverse.RowErasure.SelectionPartition

open scoped BigOperators Classical

noncomputable section

variable {X S : Type*} [Fintype X] [Fintype S]

def fiber (observe : X → S) (s : S) : Finset X :=
  Finset.univ.filter fun x => observe x = s

def event (observe : X → S) (good : S → Prop) (chosen : S → Finset X)
    (x : X) : Prop :=
  good (observe x) ∧ x ∈ chosen (observe x)

def matchEvent (observe : X → S) (good : S → Prop) (chosen : S → Finset X)
    (hit : S → X → Prop) (x : X) : Prop :=
  event observe good chosen x ∧ hit (observe x) x

end
end UniqueGamesTheorem.Inverse.RowErasure.SelectionPartition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSAnalyticHybridEnergyLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Explicit dimension-independent constants for the KMS mixed-energy
argument and the generic A5 aggregation. The eventual expansion theorem only
uses positivity and finiteness of these constants, so no rank cutoff exception
or comparison with another rank-level constant is needed. -/

namespace UniqueGamesTheorem.Inverse.KMSMomentConstants
noncomputable section
open KMSFourthMoment

/-- The constant after the genuine mixed-energy estimate and A5 aggregation. -/
def fourthMomentConstant (r : ℕ) : ℝ := 2 ^ (109 * r * r + 2 * r)

end
end UniqueGamesTheorem.Inverse.KMSMomentConstants

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_ShortcodeFromGrassmannLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped Classical
open MatrixChart

/-- The exact self-loop mass when independent uniform binary factors include
zero. The overlap of the two zero events is subtracted once. -/
def zeroFactorMass (ell m : ℕ) : ℝ :=
  ((2 : ℝ) ^ ell)⁻¹ + ((2 : ℝ) ^ m)⁻¹ - ((2 : ℝ) ^ (ell + m))⁻¹

end
end UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceNoiseParameterLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
An executable finite-noise denominator for a positive rational target error.
Using the stored rational denominator avoids rounding, searches, and choice.
-/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceNoiseParameter

/-- A positive rational has numerator at least one, so its reciprocal
denominator is no larger than the rational itself. Adding two also ensures
the noise parameter is at most one half for every input. -/
def noiseDenominator (ξ : ℚ) : ℕ := ξ.den + 2

theorem noiseDenominator_ge_two (ξ : ℚ) : 2 ≤ noiseDenominator ξ := by
  unfold noiseDenominator
  omega

theorem noiseDenominator_pos (ξ : ℚ) : 0 < noiseDenominator ξ :=
  lt_of_lt_of_le (by decide) (noiseDenominator_ge_two ξ)

/-- The actual computed reciprocal noise is below every positive target. -/
theorem noiseDenominator_inv_le {ξ : ℚ} (hξ : 0 < ξ) :
    (noiseDenominator ξ : ℚ)⁻¹ ≤ ξ := by
  have hn : (1 : ℤ) ≤ ξ.num := by
    have h := Rat.num_pos.mpr hξ
    omega
  have hnq : (1 : ℚ) ≤ (ξ.num : ℚ) := by exact_mod_cast hn
  have hd : (0 : ℚ) < (ξ.den : ℚ) := by exact_mod_cast ξ.den_pos
  calc
    (noiseDenominator ξ : ℚ)⁻¹ = 1 / (noiseDenominator ξ : ℚ) := inv_eq_one_div _
    _ ≤ 1 / (ξ.den : ℚ) := by
      apply one_div_le_one_div_of_le hd
      exact_mod_cast (show ξ.den ≤ noiseDenominator ξ by
        unfold noiseDenominator
        omega)
    _ ≤ (ξ.num : ℚ) / (ξ.den : ℚ) := div_le_div_of_nonneg_right hnq hd.le
    _ = ξ := ξ.num_div_den

end UniqueGamesTheorem.Foundations.Hastad.SourceNoiseParameter

end

section

/-! The parity projection and finite Fourier decoder used in Håstad's
three-query argument. Probabilities are explicit finite sums. -/

noncomputable section

namespace UniqueGamesTheorem.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- A purely algebraic decay estimate used instead of exponential bounds. -/
theorem scaled_geometric_power_le_one {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) (n : Nat) :
    (n : ℝ) * (1 - t) * t ^ n ≤ 1 := by
  have hsum : (n : ℝ) * t ^ n ≤ ∑ j ∈ Finset.range n, t ^ j := by
    calc
      (n : ℝ) * t ^ n = ∑ _j ∈ Finset.range n, t ^ n := by simp
      _ ≤ ∑ j ∈ Finset.range n, t ^ j := by
        apply Finset.sum_le_sum
        intro j hj
        exact pow_le_pow_of_le_one ht ht' (Nat.le_of_lt (Finset.mem_range.mp hj))
  have hm := mul_le_mul_of_nonneg_right hsum (sub_nonneg.mpr ht')
  rw [geom_sum_mul_neg] at hm
  have hp : 0 ≤ t ^ n := pow_nonneg ht _
  nlinarith

theorem noise_decay_bound {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 2)
    {k : Nat} (hk : 0 < k) :
    4 * ε * ((1 - 2 * ε) ^ k) ^ 2 ≤ 1 / (k : ℝ) := by
  have h := scaled_geometric_power_le_one (t := 1 - 2 * ε)
    (by linarith) (by linarith) (2 * k)
  have hkp : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  apply (le_div_iff₀ hkp).mpr
  have hpow : (1 - 2 * ε) ^ (2 * k) = ((1 - 2 * ε) ^ k) ^ 2 := by
    rw [Nat.mul_comm, pow_mul]
  rw [hpow] at h
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at h
  nlinarith

end UniqueGamesTheorem.Foundations.Hastad

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_AssignmentTester
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! A concrete constant-query proximity tester for a finite relation.

The proof oracle is a Boolean function on the Boolean functions on the finite
set of legal assignments. The tests are BLR linearity, self-corrected AND,
self-corrected unit, and comparison with a queried input coordinate.
The oracle's size depends exponentially on the number of legal assignments;
this is a fixed-relation construction, not a polynomial-size tester for an
arbitrary input formula. All tests below are explicit finite expectations.
-/

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.AssignmentTester

open UniqueGamesTheorem.Foundations.Hastad
open scoped BigOperators
open Finset

variable {A : Type*} [Fintype A] [DecidableEq A]

def truth (b : Bool) : ℝ := if b then 1 else 0

def disagree (a b : Bool) : ℝ := if a = b then 0 else 1

theorem truth_nonneg (b : Bool) : 0 ≤ truth b := by cases b <;> norm_num [truth]

theorem disagree_nonneg (a b : Bool) : 0 ≤ disagree a b := by
  cases a <;> cases b <;> norm_num [disagree]

theorem disagree_xor_le (a b c d : Bool) :
    disagree (a ^^ b) (c ^^ d) ≤ disagree a c + disagree b d := by
  cases a <;> cases b <;> cases c <;> cases d <;> norm_num [disagree]

def distance {K : Type*} [Fintype K] (f g : K → Bool) : ℝ :=
  𝔼 k, disagree (f k) (g k)

theorem four_truth_lower (e₀ e₁ d : Bool) :
    (1 : ℝ) ≤ truth e₀ + truth (e₀ ^^ d) + truth e₁ + truth (e₁ ^^ (!d)) := by
  cases e₀ <;> cases e₁ <;> cases d <;> norm_num [truth]

theorem truth_xor (a b : Bool) : truth (a ^^ b) = disagree a b := by
  cases a <;> cases b <;> norm_num [truth, disagree]

theorem disagree_triangle (a b c : Bool) :
    disagree a c ≤ disagree a b + disagree b c := by
  cases a <;> cases b <;> cases c <;> norm_num [disagree]

theorem and_disagree_transfer (p₀ p₁ p₂ q₀ q₁ q₂ : Bool) :
    disagree p₀ (p₁ && p₂) ≤ disagree q₀ (q₁ && q₂) +
      disagree q₀ p₀ + disagree q₁ p₁ + disagree q₂ p₂ := by
  cases p₀ <;> cases p₁ <;> cases p₂ <;>
    cases q₀ <;> cases q₁ <;> cases q₂ <;> norm_num [disagree]

variable {K : Type*} [Fintype K] [Nonempty K]

theorem truth_not_decide_eq (a b : Bool) : truth (!(decide (a = b))) = disagree a b := by
  cases a <;> cases b <;> norm_num [truth, disagree]

end UniqueGamesTheorem.Foundations.PCP.AssignmentTester

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_CodeComposition
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.CodeComposition

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Hastad

def disagreement (a b : Bool) : ℝ := if a = b then 0 else 1

@[simp] theorem disagreement_self (a : Bool) : disagreement a a = 0 := by
  simp [disagreement]

theorem disagreement_nonnegative (a b : Bool) : 0 ≤ disagreement a b := by
  cases a <;> cases b <;> norm_num [disagreement]

theorem disagreement_comm (a b : Bool) : disagreement a b = disagreement b a := by
  simp [disagreement, eq_comm]

theorem disagreement_triangle (a b c : Bool) :
    disagreement a c ≤ disagreement a b + disagreement b c := by
  cases a <;> cases b <;> cases c <;> norm_num [disagreement]

def relativeDistance {X : Type*} [Fintype X] (f g : X → Bool) : ℝ :=
  𝔼 x, disagreement (f x) (g x)

@[simp] theorem relativeDistance_self {X : Type*} [Fintype X] (f : X → Bool) :
    relativeDistance f f = 0 := by
  simp [relativeDistance]

theorem relativeDistance_nonnegative {X : Type*} [Fintype X] (f g : X → Bool) :
    0 ≤ relativeDistance f g :=
  Finset.expect_nonneg (fun _ _ => disagreement_nonnegative _ _)

theorem relativeDistance_comm {X : Type*} [Fintype X] (f g : X → Bool) :
    relativeDistance f g = relativeDistance g f := by
  simp only [relativeDistance, disagreement_comm]

theorem relativeDistance_triangle {X : Type*} [Fintype X] (f g h : X → Bool) :
    relativeDistance f h ≤ relativeDistance f g + relativeDistance g h := by
  rw [relativeDistance, relativeDistance, relativeDistance,
    ← Finset.expect_add_distrib]
  exact Finset.expect_le_expect (fun _ _ => disagreement_triangle _ _ _)

end UniqueGamesTheorem.Foundations.PCP.CodeComposition

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_AlphabetReductionLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.ConstraintGraph

variable {V E A : Type*}

section Reindex

variable {W D B : Type*}

def labelingEquiv (vertices : V ≃ W) (labels : A ≃ B) : (V → A) ≃ (W → B) where
  toFun := fun labeling w => labels (labeling (vertices.symm w))
  invFun := fun labeling v => labels.symm (labeling (vertices v))
  left_inv := by intro labeling; funext v; simp
  right_inv := by intro labeling; funext w; simp

end Reindex

end UniqueGamesTheorem.Foundations.PCP.ConstraintGraph

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_InitialGraphLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Actual indicator counting and the second-moment rejection estimate.
The hypotheses describe event inclusion and moment bounds, while the
Cauchy--Schwarz conclusion and all positivity properties are proved here. -/

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.PoweringMoment

open scoped BigOperators

def bit (p : Prop) : ℝ := by
  classical
  exact if p then 1 else 0

def hits {I Ω : Type*} [Fintype I] (E : I → Ω → Prop) (ω : Ω) : ℝ :=
  ∑ i, bit (E i ω)

def mean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ := Finset.univ.expect f

theorem bit_nonneg (p : Prop) : 0 ≤ bit p := by
  classical
  by_cases hp : p <;> simp [bit, hp]

theorem bit_sq (p : Prop) : bit p ^ 2 = bit p := by
  classical
  by_cases hp : p <;> simp [bit, hp]

theorem bit_mul (p q : Prop) : bit p * bit q = bit (p ∧ q) := by
  classical
  by_cases hp : p <;> by_cases hq : q <;> simp [bit, hp, hq]

theorem bit_mono {p q : Prop} (hpq : p → q) : bit p ≤ bit q := by
  classical
  by_cases hp : p
  · simp [bit, hp, hpq hp]
  · have hz : bit p = 0 := by simp [bit, hp]
    rw [hz]
    exact bit_nonneg q

theorem hits_nonneg {I Ω : Type*} [Fintype I] (E : I → Ω → Prop) (ω : Ω) :
    0 ≤ hits E ω := Finset.sum_nonneg (fun i _ => bit_nonneg (E i ω))

theorem mean_nonneg {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ mean f := Finset.expect_nonneg (fun ω _ => hf ω)

theorem mean_hits {I Ω : Type*} [Fintype I] [Fintype Ω] (E : I → Ω → Prop) :
    mean (hits E) = ∑ i, mean (fun ω => bit (E i ω)) := by
  exact Finset.expect_sum_comm _ _ _

theorem second_moment_eq {I Ω : Type*} [Fintype I] [Fintype Ω]
    (E : I → Ω → Prop) :
    mean (fun ω => hits E ω ^ 2) =
      ∑ i, ∑ j, mean (fun ω => bit (E i ω ∧ E j ω)) := by
  simp only [hits, pow_two, Finset.sum_mul, Finset.mul_sum, bit_mul,
    mean, Finset.expect_sum_comm]
  exact Finset.sum_comm

theorem mean_witness_sq_le {I Ω : Type*} [Fintype I] [Fintype Ω]
    (E W : I → Ω → Prop) (reject : Ω → Prop)
    (hWE : ∀ i ω, W i ω → E i ω)
    (hWR : ∀ i ω, W i ω → reject ω) :
    mean (hits W) ^ 2 ≤
      mean (fun ω => bit (reject ω)) * mean (fun ω => hits E ω ^ 2) := by
  classical
  have hNH (ω : Ω) : hits W ω ≤ hits E ω :=
    Finset.sum_le_sum (fun i _ => bit_mono (hWE i ω))
  have hzero (ω : Ω) (hr : ¬ reject ω) : hits W ω = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hw : ¬ W i ω := fun h => hr (hWR i ω h)
    simp [bit, hw]
  have hsupport (ω : Ω) : bit (reject ω) * hits W ω = hits W ω := by
    by_cases hr : reject ω
    · simp [bit, hr]
    · rw [hzero ω hr]
      simp
  have hCS := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (fun ω => bit (reject ω)) (hits W)
  have hsquares : mean (fun ω => hits W ω ^ 2) ≤ mean (fun ω => hits E ω ^ 2) := by
    apply Finset.expect_le_expect
    intro ω _
    simpa only [pow_two] using
      (mul_le_mul (hNH ω) (hNH ω) (hits_nonneg W ω) (hits_nonneg E ω))
  calc
    _ ≤ mean (fun ω => bit (reject ω)) * mean (fun ω => hits W ω ^ 2) := by
      simpa only [mean, hsupport, bit_sq] using hCS
    _ ≤ _ := mul_le_mul_of_nonneg_left hsquares
      (mean_nonneg _ (fun ω => bit_nonneg (reject ω)))

theorem rejection_lower_bound {I Ω : Type*} [Fintype I] [Fintype Ω]
    (E W : I → Ω → Prop) (reject : Ω → Prop)
    (hWE : ∀ i ω, W i ω → E i ω)
    (hWR : ∀ i ω, W i ω → reject ω)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hfirst : a ≤ mean (hits W))
    (hsecond : mean (fun ω => hits E ω ^ 2) ≤ b) :
    a ^ 2 / b ≤ mean (fun ω => bit (reject ω)) := by
  have hN : 0 ≤ mean (hits W) := mean_nonneg _ (hits_nonneg W)
  have hρ : 0 ≤ mean (fun ω => bit (reject ω)) :=
    mean_nonneg _ (fun ω => bit_nonneg (reject ω))
  have haSq : a ^ 2 ≤ mean (hits W) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hfirst hfirst ha.le hN
  have hCS := mean_witness_sq_le E W reject hWE hWR
  apply (div_le_iff₀ hb).2
  exact haSq.trans (hCS.trans (mul_le_mul_of_nonneg_left hsecond hρ))

end UniqueGamesTheorem.Foundations.PCP.PoweringMoment

end

end

section

/-!
# The scalar bound for all positive error densities

The first lemma bounds a ratio using only a nonnegative coefficient bounded
by a positive cutoff. The second applies it to a positive natural count and
the first- and second-moment expressions in the powering argument.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringNumeric

/-- A bounded nonnegative coefficient gives the required ratio bound both
below and above the cutoff `1/t`. -/
theorem min_density_ratio (ε C k t : ℝ)
    (hε : 0 < ε) (hC : 0 < C) (hk : 0 ≤ k)
    (ht : 0 < t) (hkt : k ≤ t) :
    min ε (1 / t) / (C + 1) ≤ ε / (C + k * ε) := by
  have hx : 0 ≤ min ε (1 / t) :=
    le_min hε.le (one_div_nonneg.mpr ht.le)
  have hxt : min ε (1 / t) * t ≤ 1 :=
    (le_div_iff₀ ht).mp (min_le_right ε (1 / t))
  have hkx : k * min ε (1 / t) ≤ 1 := by
    calc
      k * min ε (1 / t) ≤ t * min ε (1 / t) :=
        mul_le_mul_of_nonneg_right hkt hx
      _ ≤ 1 := by simpa only [mul_comm] using hxt
  have hC1 : 0 < C + 1 := by positivity
  have hden : 0 < C + k * ε :=
    add_pos_of_pos_of_nonneg hC (mul_nonneg hk hε.le)
  apply (div_le_div_iff₀ hC1 hden).2
  calc
    min ε (1 / t) * (C + k * ε) =
        C * min ε (1 / t) + ε * (k * min ε (1 / t)) := by ring
    _ ≤ C * ε + ε * 1 :=
      add_le_add
        (mul_le_mul_of_nonneg_left (min_le_left ε (1 / t)) hC.le)
        (mul_le_mul_of_nonneg_left hkx hε.le)
    _ = ε * (C + 1) := by ring

/-- A positive natural count supplies `0 ≤ m - 1`. After cancelling the
positive mass `m*ε`, the ratio of moments dominates a constant times
`min ε (1/t)`. No sign condition on `α` is needed for its fourth power. -/
theorem count_moment_ratio_lower (α ε C t : ℝ) (m : ℕ)
    (hm : 0 < m) (hε : 0 < ε) (hC : 0 < C) (ht : 0 < t)
    (hmt : (m : ℝ) - 1 ≤ t) :
    (α ^ 4 * (m : ℝ) / (C + 1)) * min ε (1 / t) ≤
      (α ^ 2 * (m : ℝ) * ε) ^ 2 /
        ((m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε)) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hm)
  have hk : 0 ≤ (m : ℝ) - 1 := sub_nonneg.mpr hm1
  have hden : 0 < C + ((m : ℝ) - 1) * ε :=
    add_pos_of_pos_of_nonneg hC (mul_nonneg hk hε.le)
  have hαm : 0 ≤ α ^ 4 * (m : ℝ) := by positivity
  have hratio := min_density_ratio ε C ((m : ℝ) - 1) t hε hC hk ht hmt
  calc
    (α ^ 4 * (m : ℝ) / (C + 1)) * min ε (1 / t) =
        (α ^ 4 * (m : ℝ)) * (min ε (1 / t) / (C + 1)) := by ring
    _ ≤ (α ^ 4 * (m : ℝ)) * (ε / (C + ((m : ℝ) - 1) * ε)) :=
      mul_le_mul_of_nonneg_left hratio hαm
    _ = (α ^ 2 * (m : ℝ) * ε) ^ 2 /
        ((m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε)) := by
      field_simp [ne_of_gt hm0, ne_of_gt hε, ne_of_gt hden]

end UniqueGamesTheorem.Foundations.PCP.PoweringNumeric

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PoweringLabelsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Modal decoding is an actual maximum of finite empirical letter masses.
Its reciprocal-alphabet lower bound is derived from their total mass one. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringDecoding

open scoped BigOperators

variable {Ω A : Type*} [Fintype Ω] [Nonempty Ω] [Fintype A] [Nonempty A]

noncomputable def mass (opinion : Ω → A) (a : A) : ℝ := by
  classical
  exact Finset.univ.expect (fun ω => if opinion ω = a then 1 else 0)

omit [Nonempty A] in
theorem mass_sum (opinion : Ω → A) : (∑ a, mass opinion a) = 1 := by
  classical
  calc
    (∑ a, mass opinion a) =
        (Finset.univ : Finset Ω).expect
          (fun ω => ∑ a : A, if opinion ω = a then (1 : ℝ) else 0) :=
      (Finset.expect_sum_comm (Finset.univ : Finset Ω) (Finset.univ : Finset A)
        (fun ω a => if opinion ω = a then (1 : ℝ) else 0)).symm
    _ = (Finset.univ : Finset Ω).expect (fun _ => (1 : ℝ)) := by
      apply Finset.expect_congr rfl
      intro ω _
      simp
    _ = 1 := Finset.expect_const Finset.univ_nonempty 1

omit [Nonempty Ω] in
theorem exists_mode (opinion : Ω → A) :
    ∃ a : A, ∀ b : A, mass opinion b ≤ mass opinion a := by
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image (Finset.univ : Finset A)
    (mass opinion) Finset.univ_nonempty
  exact ⟨a, fun b => ha b (Finset.mem_univ b)⟩

noncomputable def mode (opinion : Ω → A) : A := Classical.choose (exists_mode opinion)

omit [Nonempty Ω] in
theorem mode_max (opinion : Ω → A) (b : A) :
    mass opinion b ≤ mass opinion (mode opinion) :=
  Classical.choose_spec (exists_mode opinion) b

theorem mode_mass_lower (opinion : Ω → A) :
    1 / (Fintype.card A : ℝ) ≤ mass opinion (mode opinion) := by
  have hk : 0 < (Fintype.card A : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hsum : (1 : ℝ) ≤ mass opinion (mode opinion) * (Fintype.card A : ℝ) := by
    calc
      (1 : ℝ) = ∑ a : A, mass opinion a := (mass_sum opinion).symm
      _ ≤ ∑ _a : A, mass opinion (mode opinion) :=
        Finset.sum_le_sum (fun a _ => mode_max opinion a)
      _ = mass opinion (mode opinion) * (Fintype.card A : ℝ) := by simp [mul_comm]
  exact (div_le_iff₀ hk).2 hsum

end UniqueGamesTheorem.Foundations.PCP.PoweringDecoding

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_AlphabetRetractionLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.SpectralReturn

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

theorem mean_eq_sum_div_card (f : A → ℝ) :
    mean f = (∑ x, f x) / (Fintype.card A : ℝ) :=
  Fintype.expect_eq_sum_div_card f

theorem mean_equiv (e : A ≃ B) (f : B → ℝ) :
    mean (fun x => f (e x)) = mean f :=
  Fintype.expect_equiv e _ _ (fun _ => rfl)

theorem mean_prod (f : A × B → ℝ) :
    mean f = mean (fun a => mean (fun b => f (a, b))) := by
  simpa only [mean, Finset.univ_product_univ] using
    Finset.expect_product (Finset.univ : Finset A) (Finset.univ : Finset B) f

/-- The finite Cauchy--Schwarz inequality, in the chosen normalized convention. -/
theorem correlation_sq_le (f g : A → ℝ) :
    correlation f g ^ 2 ≤ energy f * energy g :=
  Finset.expect_mul_sq_le_sq_mul_sq Finset.univ f g

end Averages

end

end UniqueGamesTheorem.Foundations.PCP.SpectralReturn

end

section

/-!
# Walsh diagonalization of actual Boolean-cube Cayley graphs

Every port is an indexed generator. The rotation keeps the port and adds its
generator by pointwise xor, so loops and repeated generators keep their full
multiplicity. The Fourier multiplier and energy estimate are proved for this
actual averaging operator; no Fourier/operator compatibility is assumed.
-/

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.CayleySpectral

open scoped BigOperators
open Finset
open UniqueGamesTheorem.Foundations.Hastad

variable {I D : Type*}

/-- Expose the first actual port in a finite port word. -/
def splitPortWord (n : Nat) : (Fin (n + 1) → D) ≃ D × (Fin n → D) where
  toFun p := (p 0, fun j => p j.succ)
  invFun z := Fin.cases z.1 z.2
  left_inv p := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

end UniqueGamesTheorem.Foundations.PCP.CayleySpectral

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_CayleySampling
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.CayleySampling

open scoped BigOperators
open Finset
open UniqueGamesTheorem.Foundations.Hastad

variable {V D : Type*}

/-- The common fiber left after separating a Boolean character's sign. -/
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

end UniqueGamesTheorem.Foundations.PCP.CayleySampling

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_CayleyTailCount
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Actual finite binary-word tail counts for the proposed Cayley base graph.

No expander, independence, spectral, or random-generator existence result is
assumed here.
-/

namespace UniqueGamesTheorem.Foundations.PCP.CayleyTailCount

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

def upperMasks (s : Finset α) (m : ℕ) : Finset (Finset α) :=
  s.powerset.filter fun t => 3 * m ≤ t.card

def lowerMasks (s : Finset α) (m : ℕ) : Finset (Finset α) :=
  s.powerset.filter fun t => t.card ≤ m

def badMasks (s : Finset α) (m : ℕ) : Finset (Finset α) :=
  lowerMasks s m ∪ upperMasks s m

omit [DecidableEq α] in
/-- Weight every actual upper-tail mask by at least `3 ^ (3 * m)`. -/
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

/-- Complementation preserves multiplicity and exchanges the two closed tails. -/
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

/-- All words occur once, so subset counting keeps the actual uniform law. -/
def wordMaskEquiv [DecidableEq D] : (D → Bool) ≃ Finset D where
  toFun := trueMask
  invFun s i := decide (i ∈ s)
  left_inv word := by
    funext i
    cases h : word i <;> simp [trueMask, h]
  right_inv s := by
    ext i
    simp [trueMask]

/-- Actual real uniform expectation on binary words, including both closed tails. -/
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

/-- Numerical budget for a union bound over at most `2 ^ n` frequencies. -/
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

end UniqueGamesTheorem.Foundations.PCP.CayleyTailCount

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_InputLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
An actual fixed-alphabet TM2 parser for the complete Boolean relation table.
The finite syntax contains one slot reader for each of the `q*q` coordinates.
Each reader consumes `[false]` or `[true,false]`, stores the bit, and clears the
head register. No parser outcome or execution trace is an assumption.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.ReadRelation

open Turing

variable {K Λ σ : Type} [DecidableEq K] {q : Nat}

abbrev Alphabet (_ : K) := Bool

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.ReadRelation

end

section

/-! Additive smoothing of the actual fair Boolean-tape length law.  This is
the finite-probability input to the lazy-walk amplification argument. -/

namespace UniqueGamesTheorem.Foundations.PCP.LazySmoothing

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

theorem bitCount_succ {n : ℕ} (x : Fin (n + 1) → Bool) :
    bitCount x = (if x 0 then 1 else 0) + bitCount (fun i => x i.succ) := by
  exact Fin.sum_univ_succ _

theorem mean_congr {n : ℕ} {f g : ℕ → ℝ} (h : ∀ k, f k = g k) :
    binomialMean n f = binomialMean n g := by
  unfold binomialMean
  exact Finset.expect_congr rfl (fun x _ => h (bitCount x))

@[simp] theorem mean_const (n : ℕ) (c : ℝ) :
    binomialMean n (fun _ => c) = c := Fintype.expect_const c

theorem mean_add (n : ℕ) (f g : ℕ → ℝ) :
    binomialMean n (fun k => f k + g k) = binomialMean n f + binomialMean n g :=
  Finset.expect_add_distrib _ _ _

theorem mean_sub (n : ℕ) (f g : ℕ → ℝ) :
    binomialMean n (fun k => f k - g k) = binomialMean n f - binomialMean n g :=
  Finset.expect_sub_distrib _ _ _

theorem mean_mul (n : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    binomialMean n (fun k => c * f k) = c * binomialMean n f := by
  exact (Finset.mul_expect Finset.univ (fun x : Fin n → Bool => f (bitCount x)) c).symm

@[simp] theorem mean_zero (g : ℕ → ℝ) : binomialMean 0 g = g 0 := by
  simp [binomialMean, bitCount]

theorem expect_bool (f : Bool → ℝ) : Finset.univ.expect f = (f false + f true) / 2 := by
  rw [Finset.expect_eq_sum_div_card]
  simp [Fintype.univ_bool, add_comm]

theorem mean_succ (n : ℕ) (g : ℕ → ℝ) :
    binomialMean (n + 1) g =
      (binomialMean n g + binomialMean n (fun k => g (k + 1))) / 2 := by
  unfold binomialMean
  rw [Fintype.expect_equiv (splitTape n)
    (fun x => g (bitCount x))
    (fun x => g ((if x.1 then 1 else 0) + bitCount x.2))
    (fun x => congrArg g (bitCount_succ x))]
  rw [← Finset.univ_product_univ, Finset.expect_product, expect_bool]
  simp [Nat.add_comm]

def score (n k : ℕ) : ℝ := (n : ℝ) - 2 * (k : ℝ)

noncomputable def scoreMean (n : ℕ) (g : ℕ → ℝ) : ℝ :=
  binomialMean n (fun k => score n k * g k)

@[simp] theorem scoreMean_zero (g : ℕ → ℝ) : scoreMean 0 g = 0 := by
  simp [scoreMean, score]

theorem scoreMean_succ (n : ℕ) (g : ℕ → ℝ) :
    scoreMean (n + 1) g =
      ((scoreMean n g + binomialMean n g) +
       (scoreMean n (fun k => g (k + 1)) -
        binomialMean n (fun k => g (k + 1)))) / 2 := by
  unfold scoreMean
  rw [mean_succ]
  have h₁ : (fun k => score (n + 1) k * g k) =
      (fun k => score n k * g k + g k) := by
    funext k
    simp only [score, Nat.cast_add, Nat.cast_one]
    ring
  have h₂ : (fun k => score (n + 1) (k + 1) * g (k + 1)) =
      (fun k => score n k * g (k + 1) - g (k + 1)) := by
    funext k
    simp only [score, Nat.cast_add, Nat.cast_one]
    ring
  rw [h₁, h₂, mean_add, mean_sub]

/-- Exact finite integration by parts for the fair Boolean-tape law. -/
theorem score_identity (n : ℕ) (g : ℕ → ℝ) :
    scoreMean (n + 1) g = ((n : ℝ) + 1) / 2 *
      (binomialMean n g - binomialMean n (fun k => g (k + 1))) := by
  induction n generalizing g with
  | zero => simp [scoreMean_succ]; ring
  | succ n ih =>
    rw [scoreMean_succ, ih g, ih (fun k => g (k + 1))]
    simp only [mean_succ, Nat.cast_add, Nat.cast_one]
    ring

theorem score_mean_zero (n : ℕ) : binomialMean n (score n) = 0 := by
  cases n with
  | zero => simp [score]
  | succ n =>
    have h := score_identity n (fun _ => 1)
    simpa [scoreMean] using h

/-- The score variance is proved from the actual tape distribution. -/
theorem score_second_moment (n : ℕ) :
    binomialMean n (fun k => score n k ^ 2) = (n : ℝ) := by
  cases n with
  | zero => simp [score]
  | succ n =>
    have h := score_identity n (score (n + 1))
    have hd : binomialMean n (score (n + 1)) -
        binomialMean n (fun k => score (n + 1) (k + 1)) = 2 := by
      rw [← mean_sub]
      calc
        _ = binomialMean n (fun _ => 2) := by
          apply mean_congr
          intro k
          simp only [score, Nat.cast_add, Nat.cast_one]
          ring
        _ = 2 := mean_const _ _
    rw [hd] at h
    simpa [scoreMean, pow_two] using h

theorem score_difference (n : ℕ) (g : ℕ → ℝ) :
    scoreMean (n + 1) g = ((n : ℝ) + 1) *
      (binomialMean n g - binomialMean (n + 1) g) := by
  rw [score_identity, mean_succ]
  ring

/-- Cauchy--Schwarz yields an adjacent-length bound without any support or
small-parameter caveat.  The square form avoids introducing square roots. -/
theorem adjacent_difference_sq (n : ℕ) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) :
    4 * ((n : ℝ) + 1) *
      (binomialMean n g - binomialMean (n + 1) g) ^ 2 ≤ 1 := by
  have hc : binomialMean (n + 1)
      (fun k => score (n + 1) k * (g k - 1 / 2)) = scoreMean (n + 1) g := by
    calc
      _ = binomialMean (n + 1) (fun k =>
          score (n + 1) k * g k - (1 / 2) * score (n + 1) k) := by
        apply mean_congr
        intro k
        ring
      _ = scoreMean (n + 1) g := by
        rw [mean_sub, mean_mul, score_mean_zero]
        simp [scoreMean]
  have hv : binomialMean (n + 1) (fun k => (g k - 1 / 2) ^ 2) ≤ 1 / 4 := by
    apply Finset.expect_le Finset.univ_nonempty
    intro tape _
    have h₀ := (hg (bitCount tape)).1
    have h₁ := (hg (bitCount tape)).2
    have hp := mul_nonneg h₀ (sub_nonneg.mpr h₁)
    nlinarith
  have hcs : (binomialMean (n + 1)
        (fun k => score (n + 1) k * (g k - 1 / 2))) ^ 2 ≤
      binomialMean (n + 1) (fun k => score (n + 1) k ^ 2) *
        binomialMean (n + 1) (fun k => (g k - 1 / 2) ^ 2) :=
    Finset.expect_mul_sq_le_sq_mul_sq Finset.univ _ _
  rw [hc, score_difference, score_second_moment] at hcs
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hm := mul_le_mul_of_nonneg_left hv (le_of_lt hn)
  simp only [Nat.cast_add, Nat.cast_one] at hcs
  apply (mul_le_mul_iff_left₀ hn).mp
  nlinarith

theorem adjacent_difference_le (n : ℕ) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (r : ℝ) (hr : 0 < r)
    (hrn : r ^ 2 ≤ 4 * ((n : ℝ) + 1)) :
    |binomialMean n g - binomialMean (n + 1) g| ≤ 1 / r := by
  have hs := adjacent_difference_sq n g hg
  have hd := sq_nonneg (binomialMean n g - binomialMean (n + 1) g)
  have hh := mul_le_mul_of_nonneg_right hrn hd
  rw [le_div_iff₀ hr]
  have ha := sq_abs (binomialMean n g - binomialMean (n + 1) g)
  have hp : 0 ≤ |binomialMean n g - binomialMean (n + 1) g| * r :=
    mul_nonneg (abs_nonneg _) (le_of_lt hr)
  nlinarith [sq_nonneg (|binomialMean n g - binomialMean (n + 1) g| * r - 1)]

theorem mean_shift_le (n d : ℕ) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (r : ℝ) (hr : 0 < r)
    (hrn : r ^ 2 ≤ 4 * ((n : ℝ) + 1)) :
    |binomialMean (n + d) g - binomialMean n g| ≤ (d : ℝ) / r := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hrnd : r ^ 2 ≤ 4 * ((n + d : ℕ) + 1 : ℝ) := by
      push_cast
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
      linarith
    have ha := adjacent_difference_le (n + d) g hg r hr hrnd
    rw [abs_sub_comm] at ha
    calc
      _ ≤ |binomialMean (n + d + 1) g - binomialMean (n + d) g| +
          |binomialMean (n + d) g - binomialMean n g| := abs_sub_le _ _ _
      _ ≤ 1 / r + (d : ℝ) / r := add_le_add ha ih
      _ = ((d + 1 : ℕ) : ℝ) / r := by push_cast; ring

theorem mean_ordered_difference_le (m n : ℕ) (hmn : m ≤ n) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (r : ℝ) (hr : 0 < r)
    (hrm : r ^ 2 ≤ 4 * ((m : ℝ) + 1)) :
    |binomialMean n g - binomialMean m g| ≤ ((n - m : ℕ) : ℝ) / r := by
  simpa [Nat.add_sub_of_le hmn] using mean_shift_le m (n - m) g hg r hr hrm

theorem mean_window_le (N M m : ℕ) (hlo : N - M ≤ m) (hhi : m ≤ N + M)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1)
    (r : ℝ) (hr : 0 < r) (hbase : r ^ 2 ≤ 4 * (((N - M : ℕ) : ℝ) + 1)) :
    |binomialMean m g - binomialMean N g| ≤ (M : ℝ) / r := by
  by_cases hmN : m ≤ N
  · have hrm : r ^ 2 ≤ 4 * ((m : ℝ) + 1) := by
      have : ((N - M : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hlo
      linarith
    have h := mean_ordered_difference_le m N hmN g hg r hr hrm
    rw [abs_sub_comm] at h
    refine h.trans (div_le_div_of_nonneg_right ?_ (le_of_lt hr))
    have : N - m ≤ M := by omega
    exact_mod_cast this
  · have hNm : N ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hmN)
    have hrN : r ^ 2 ≤ 4 * ((N : ℝ) + 1) := by
      have : ((N - M : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N M
      linarith
    have h := mean_ordered_difference_le N m hNm g hg r hr hrN
    refine h.trans (div_le_div_of_nonneg_right ?_ (le_of_lt hr))
    have : m - N ≤ M := by omega
    exact_mod_cast this

/-- A convenient square center for a fixed alphabet. -/
theorem square_window_le (q M m : ℕ) (hq : 1 ≤ q) (hM : 1 ≤ M)
    (hlo : (4 * q * M) ^ 2 - M ≤ m) (hhi : m ≤ (4 * q * M) ^ 2 + M)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) :
    |binomialMean m g - binomialMean ((4 * q * M) ^ 2) g| ≤ 1 / (4 * (q : ℝ)) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hR : (4 : ℝ) * M ≤ ((4 * q * M : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hRM : (M : ℝ) ≤ (((4 * q * M : ℕ) : ℝ)) ^ 2 := by nlinarith
  have hMN : M ≤ (4 * q * M) ^ 2 := by exact_mod_cast hRM
  have hr : (0 : ℝ) < ((4 * q * M : ℕ) : ℝ) := by linarith
  have hb : (((4 * q * M : ℕ) : ℝ)) ^ 2 ≤
      4 * (((((4 * q * M) ^ 2 - M : ℕ)) : ℝ) + 1) := by
    rw [Nat.cast_sub hMN, Nat.cast_pow]
    nlinarith
  have h := mean_window_le ((4 * q * M) ^ 2) M m hlo hhi g hg
    ((4 * q * M : ℕ) : ℝ) hr hb
  have he : (M : ℝ) / ((4 * q * M : ℕ) : ℝ) = 1 / (4 * (q : ℝ)) := by
    push_cast
    have hq0 : (q : ℝ) ≠ 0 := by linarith
    have hM0 : (M : ℝ) ≠ 0 := by linarith
    field_simp
  rw [he] at h
  exact h

/-- A modal event of probability at least `1/q` retains probability `1/(2q)`
throughout the middle window used in lazy-walk powering. -/
theorem modal_transfer (q M m : ℕ) (hq : 1 ≤ q) (hM : 1 ≤ M)
    (hlo : (4 * q * M) ^ 2 - M ≤ m) (hhi : m ≤ (4 * q * M) ^ 2 + M)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1)
    (hmodal : 1 / (q : ℝ) ≤ binomialMean ((4 * q * M) ^ 2) g) :
    1 / (2 * (q : ℝ)) ≤ binomialMean m g := by
  have h := square_window_le q M m hq hM hlo hhi g hg
  have hqR : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hrec : 0 < 1 / (q : ℝ) := one_div_pos.mpr hqR
  have he₁ : 1 / (4 * (q : ℝ)) = (1 / (q : ℝ)) / 4 := by ring
  have he₂ : 1 / (2 * (q : ℝ)) = (1 / (q : ℝ)) / 2 := by ring
  rw [he₁] at h
  rw [he₂]
  have hl := (abs_le.mp h).1
  linarith

end UniqueGamesTheorem.Foundations.PCP.LazySmoothing

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_ExpandersLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
# Finite existence of the Cayley expander base

The sample space is the actual finite type of indexed Boolean-cube generators.
For each nonzero character, the checked sign sampling equivalence supplies its
uniform word law. A finite union bound then selects a generator family whose
nonconstant character biases are small. There is no random-graph hypothesis.

The fixed numbers below are manipulated symbolically; no enumeration of the
generator sample space is executed. The subsequent square-and-zigzag family
is a separate construction.
-/

namespace UniqueGamesTheorem.Foundations.PCP.Expanders

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Hastad
open CayleySpectral

def baseDimension : Nat := 448
def initialQuarterDegree : Nat := 2 ^ 14

end UniqueGamesTheorem.Foundations.PCP.Expanders

/-! Exact changes of finite vertex and port coordinates. The graph rotation and
its normalized averaging operator are transported by the same equivalences. -/

namespace UniqueGamesTheorem.Foundations.PCP.GraphTransport

open SpectralReturn

variable {V W D E : Type*}

variable [Fintype V] [Fintype W] [Fintype D] [Fintype E]

theorem energy_reindex (vertices : V ≃ W) (f : W → ℝ) :
    energy (fun v => f (vertices v)) = energy f :=
  mean_equiv vertices (fun w => f w ^ 2)

end UniqueGamesTheorem.Foundations.PCP.GraphTransport

/-! Spectral contraction for the actual Boolean-flag lazy port graph. The
operator identity is proved in `PoweringLazy`; the estimate here averages the
elementary two-term square inequality. -/

namespace UniqueGamesTheorem.Foundations.PCP.LazySpectral

open SpectralReturn

variable {V D : Type*}

theorem half_sum_sq_le (a b : ℝ) : ((a + b) / 2) ^ 2 ≤ (a ^ 2 + b ^ 2) / 2 := by
  nlinarith [sq_nonneg (a - b)]

end UniqueGamesTheorem.Foundations.PCP.LazySpectral

/-! Actual finite walk averages and their operator representations.
All changes of probability coordinates come from explicit equivalences. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringReturn

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

end UniqueGamesTheorem.Foundations.PCP.PoweringReturn

/-! The second moment of the actual marked-edge count in a consecutive walk
window. Pair events are reduced to the checked spectral return operator. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringMomentBound

open scoped BigOperators
open SpectralReturn PoweringReturn
open PoweringMoment (bit hits)

def windowIndex (n start m : Nat) (h : start + m ≤ n + 1) (i : Fin m) : Fin (n + 1) :=
  ⟨start + i.val, (Nat.add_lt_add_left i.isLt start).trans_le h⟩

end UniqueGamesTheorem.Foundations.PCP.PoweringMomentBound

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_ZigzagGraphsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Energy contraction for the actual zigzag graph

The proof splits a function into its cloud average and its cloud-centered
part. All operators are the actual graph averages from `ZigzagGraphs`.
-/

namespace UniqueGamesTheorem.Foundations.PCP.ZigzagSpectral

open SpectralReturn

noncomputable section

variable {V D E : Type*}

def liftCloud (f : V → ℝ) (x : V × D) : ℝ := f x.1

end

end UniqueGamesTheorem.Foundations.PCP.ZigzagSpectral

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_CloudRoundingLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Actual finite counting for rounding copied dart labels. Minority color classes
are small enough for the cloud's directed-cut expansion. Their boundary darts
inject into all label disagreements. A separate endpoint charge counts at
most two affected original darts per changed copied label.
-/

namespace UniqueGamesTheorem.Foundations.PCP.CloudRounding

open scoped BigOperators

theorem dart_rejection_count_le
    {E V A : Type*} [Fintype E] [DecidableEq A]
    (tail : E → V) (reverse : E ≃ E) (accepts : E → A → A → Bool)
    (ell : E → A) (rounded : V → A) :
    (Finset.univ.filter (fun e =>
      accepts e (rounded (tail e)) (rounded (tail (reverse e))) = false)).card ≤
    (Finset.univ.filter (fun e => accepts e (ell e) (ell (reverse e)) = false)).card +
      2 * (Finset.univ.filter (fun e => ell e ≠ rounded (tail e))).card := by
  classical
  let R : Finset E := Finset.univ.filter (fun e =>
    accepts e (rounded (tail e)) (rounded (tail (reverse e))) = false)
  let B : Finset E := Finset.univ.filter (fun e =>
    accepts e (ell e) (ell (reverse e)) = false)
  let M : Finset E := Finset.univ.filter (fun e => ell e ≠ rounded (tail e))
  let MR : Finset E := Finset.univ.filter (fun e =>
    ell (reverse e) ≠ rounded (tail (reverse e)))
  have hrev : MR.card = M.card := by
    have hsets : MR = M.map reverse.symm.toEmbedding := by
      ext e
      constructor
      · intro he
        apply Finset.mem_map.mpr
        refine ⟨reverse e, ?_, reverse.symm_apply_apply e⟩
        simpa [MR, M] using he
      · intro he
        obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp he
        simpa [MR, M] using hd
    rw [hsets, Finset.card_map]
  have hsub : R ⊆ (B ∪ M) ∪ MR := by
    intro e he
    by_cases hl : ell e = rounded (tail e)
    · by_cases hr : ell (reverse e) = rounded (tail (reverse e))
      · have hb : e ∈ B := by simpa [B, R, hl, hr] using he
        exact Finset.mem_union_left _ (Finset.mem_union_left _ hb)
      · exact Finset.mem_union_right _ (by simp [MR, hr])
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [M, hl]))
  change R.card ≤ B.card + 2 * M.card
  calc
    R.card ≤ ((B ∪ M) ∪ MR).card := Finset.card_le_card hsub
    _ ≤ (B ∪ M).card + MR.card := Finset.card_union_le _ _
    _ ≤ (B.card + M.card) + MR.card :=
      Nat.add_le_add_right (Finset.card_union_le B M) _
    _ = B.card + 2 * M.card := by rw [hrev]; omega

section CloudCounts

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

omit [DecidableEq X] in
theorem majority_maximal (ell : X → A) [Nonempty A] (a : A) :
    (colorSet ell a).card ≤ (colorSet ell (majority ell)).card :=
  Classical.choose_spec (exists_max_color ell) a

omit [Fintype A] in
/-- Every nonchosen color occupies at most half the cloud. -/
theorem nonchosen_color_twice_le (ell : X → A) (m : A)
    (maximal : ∀ a, (colorSet ell a).card ≤ (colorSet ell m).card)
    (a : A) (ha : a ≠ m) :
    2 * (colorSet ell a).card ≤ Fintype.card X := by
  have hd : Disjoint (colorSet ell a) (colorSet ell m) := by
    apply Finset.disjoint_left.mpr
    intro x hx hm
    have hxa : ell x = a := by simpa [colorSet] using hx
    have hxm : ell x = m := by simpa [colorSet] using hm
    exact ha (hxa.symm.trans hxm)
  have hu : (colorSet ell a).card + (colorSet ell m).card ≤ Fintype.card X := by
    calc
      _ = (colorSet ell a ∪ colorSet ell m).card :=
        (Finset.card_union_of_disjoint hd).symm
      _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card X := Finset.card_univ
  have hm := maximal a
  omega

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

omit [DecidableEq X] in
theorem minority_card_eq_sum (ell : X → A) (m : A) :
    (minoritySet ell m).card = ∑ a : Nonmajor m, (colorSet ell a.val).card := by
  have h := Fintype.card_congr (minorityEquiv ell m)
  simpa only [Fintype.card_sigma, Fintype.card_coe] using h.symm

/-- The tail label determines the forgotten minority color. -/
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

theorem minority_cut_sum_le (ell : X → A) (next : X × D → X) (m : A) :
    (∑ a : Nonmajor m, (directedCut next (colorSet ell a.val)).card) ≤
      (disagreementSet ell next).card := by
  have h := Fintype.card_le_of_injective
    (minorityCutEmbedding ell next m) (minorityCutEmbedding ell next m).injective
  simpa only [Fintype.card_sigma, Fintype.card_coe] using h

/-- Sum genuine directed-cut expansion over the nonchosen color classes. -/
theorem minority_expansion_bound (ell : X → A) (next : X × D → X) (m : A)
    (h : ℚ)
    (maximal : ∀ a, (colorSet ell a).card ≤ (colorSet ell m).card)
    (expansion : ∀ S : Finset X, S.card ≤ Fintype.card X / 2 →
      h * (S.card : ℚ) ≤ ((directedCut next S).card : ℚ)) :
    h * ((minoritySet ell m).card : ℚ) ≤ ((disagreementSet ell next).card : ℚ) := by
  have each (a : Nonmajor m) :
      h * ((colorSet ell a.val).card : ℚ) ≤
        ((directedCut next (colorSet ell a.val)).card : ℚ) := by
    apply expansion
    have ha := nonchosen_color_twice_le ell m maximal a.val a.property
    omega
  calc
    h * ((minoritySet ell m).card : ℚ) =
        ∑ a : Nonmajor m, h * ((colorSet ell a.val).card : ℚ) := by
      rw [minority_card_eq_sum, Nat.cast_sum, Finset.mul_sum]
    _ ≤ ∑ a : Nonmajor m, ((directedCut next (colorSet ell a.val)).card : ℚ) :=
      Finset.sum_le_sum (fun a _ => each a)
    _ ≤ ((disagreementSet ell next).card : ℚ) := by
      exact_mod_cast minority_cut_sum_le ell next m

end CloudCounts

end UniqueGamesTheorem.Foundations.PCP.CloudRounding

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PreprocessingPaddingOffsets
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The executable dummy numbering is the sum of earlier cloud sizes plus
the local dummy index. This connects the actual list search in vertexOrder
with unary prefix-sum routines, without changing the chosen enumeration. -/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingOffsets

open scoped BigOperators

theorem sigma_length {A : Type*} (sizes : A → Nat) (xs : List A) :
    (xs.sigma (fun x => List.finRange (sizes x))).length = (xs.map sizes).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.sigma_cons, ih]

end UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingOffsets

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRepeat
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed finite TM2 interpreter for a unary number of runs of a fixed
certified machine. The counter is data on a separate tape. Every body run is
lifted from an actual `TM2OutputsInTime` witness, and all transfers are executed
by the checked finite transfer loops. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRepeat
open Turing

def oneStep {α : Type*} (step : α → Option α) (a b : α)
    (h : step a = some b) : StateTransition.EvalsToInTime step a (some b) 1 where
  steps := 1
  evals_in_steps := by change step a = some b; exact h
  steps_le_m := le_refl _

variable (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool) (output : M.Γ M.k₁ ≃ Bool)

/-- Running time after the parser: actual body budgets, two transfers per
body result, one guard per iteration, and the final transfer and empty guard. -/
def loopBudget : Nat → (Nat → List Bool) → (Nat → Nat) → Nat
  | 0, words, _ => 2*(words 0).length+3
  | count+1, words, budgets => budgets 0 + 2*(words 1).length+3 +
      loopBudget count (fun i => words (i+1)) (fun i => budgets (i+1))

end UniqueGamesTheorem.Foundations.Complexity.MachineRepeat

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularOriginalRow
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Machine execution for an inherited regularization row

The machine reads the original reverse index from the physically stored input
table. The unread working copy then starts at the 4096 original predicate
fields; a fixed finite Boolean block copy retains exactly those fields. Unary
arithmetic computes the new reverse index, and the checked row emitter appends
the three physical fields. No input table or unbounded arithmetic function is
stored in the machine's finite state or instructions.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalRow

open Turing
open PCP

/-! ## The actual stored row and its input word boundaries -/

/-! ## One fixed finite program -/

abbrev Tape := Fin 10
abbrev Alphabet (_ : Tape) := Bool

def lookupTape (i : Fin 5) : Tape := ⟨i.val + 1, by omega⟩

theorem lookupTape_injective : Function.Injective lookupTape := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [lookupTape] at hv
  omega

theorem source_outside (i : Fin 5) : (0 : Tape) ≠ lookupTape i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [lookupTape] at hv
  omega

def fields : Fin 3 → Tape := Fin.cases 0 (Fin.cases 6 (fun _ => 7))

@[simp] theorem fields_zero : fields 0 = 0 := rfl
@[simp] theorem fields_one : fields 1 = 6 := rfl
@[simp] theorem fields_two : fields 2 = 7 := rfl

theorem fields_separate (i : Fin 3) : fields i ≠ 8 ∧ fields i ≠ 5 := by
  fin_cases i <;> decide

/-! ## Physical intermediate tape states -/

section Execution

variable {Λ σ : Type}

theorem join_trace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

end Execution

def timeBound (q inputLength outputLength : Nat) : Nat :=
  (4 * q + 17) * inputLength + 2 * outputLength + 4 * q + 32795

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalRow

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularMetadata
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual metadata preparation for an original regularized vertex. The
shared 27-tape row interface is preserved, with two explicit extra outputs
for padding count and geometric level. Family generation is a subsequent
stage and owns the rotor tape. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularMetadata

open Turing
open UniqueGamesTheorem.Foundations.PCP

variable {σ : Type}

theorem join_trace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

def querySteps (v x : Nat) : Nat := 2 * (x + 2) + 2 * (v + 2) + 1

def overhead (N x v : Nat) : Nat :=
  (2*x + 5*N + 6) + 2 + (N+1) + 2*(x+2) + 2*(v+2) + 1 +
    (5*N + 3*(v+x+2) + 6) + (v+x+3) + (N+1) + 2 + (v+2) + 2

theorem overhead_le (N x v : Nat) (hx : x ≤ N) (hv : v ≤ N) :
    overhead N x v ≤ 40*(N+1) := by
  unfold overhead
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularMetadata

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_CleanupLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-stack cleanup. Each selected stack is drained using the
checked pop loop, followed by one transition resetting the finite state.
Repeated selections are allowed; they only reduce the cost upper bound. -/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Cleanup

open Turing
open Complexity
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

/-- Actual tape family after the selected stacks have been drained in order. -/
def clearTapes : {n : Nat} → (Fin n → K) → (K → List Bool) → K → List Bool
  | 0, _, base => base
  | n + 1, selected, base =>
      clearTapes (fun i : Fin n => selected i.succ) (Function.update base (selected 0) [])

/-- Exact number of transitions, including the final state-reset transition. -/
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

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Cleanup

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PoweringTablesLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Executable tables of the actual powering graph

The input rotor and every base predicate are stored finite vectors. The output
has one row for each start vertex, bounded port word, and orientation, with the
two orientations adjacent. Every complete predicate table is generated from the
bounded first-address lookup test. Degree and walk length fix the output alphabet;
neither the alphabet nor an address list depends on the input vertex count.
-/

/-!
# Actual graph data consumed by the powered-row machine

The data fields are computed from the stored rotor and base relations. The
endpoint masks compare actual bounded word endpoints, in `allAddresses` order.
Their first true positions equal the already checked canonical address indices.

Reversing a row swaps the two masks and transposes each base predicate. Thus
one fixed row machine handles both directions. Its label lookup depends only
on the fixed degree and radius. The final identities describe the exact unary
input fields and the exact serialized relation emitted for a stored output row.

These are semantic producer-to-emitter identities. A machine implementation
that computes the input data from the serialized rotor is a separate frontend.
-/

/-! A fixed powered-row data block is reduced to two concrete instruction
forms: follow a fixed port word and read one stored predicate entry, or follow
two fixed words and compare their endpoint identifiers. The plan depends only
on the fixed degree, radius, word and orientation. Its interpretation is exactly
the data block consumed by the checked row transducer. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringFieldPlan

open UniqueGamesTheorem.Foundations.Complexity

variable {V D : Type*}

/-- The actual ports before a selected time, with no vertex-dependent choice. -/
def tailPorts : (n : Nat) → (Fin (n + 1) → D) → Fin (n + 1) → List D
  | 0, _, _ => []
  | n + 1, p, k => Fin.cases [] (fun j => p 0 :: tailPorts n (fun i => p i.succ) j) k

theorem tailPorts_length : ∀ (n : Nat) (p : Fin (n + 1) → D) (k : Fin (n + 1)),
    (tailPorts n p k).length = k.val := by
  intro n
  induction n with
  | zero => intro p k; have hk := Fin.eq_zero k; subst k; rfl
  | succ n ih =>
      intro p k
      refine Fin.cases rfl (fun j => ?_) k
      simp only [tailPorts, Fin.cases_succ, List.length_cons, ih, Fin.val_succ]

def headPorts (n : Nat) (p : Fin (n + 1) → D) (k : Fin (n + 1)) : List D :=
  tailPorts n p k ++ [p k]

/-- Static commands; all changing vertex identifiers remain inputs to evaluation. -/
inductive Instruction (d : Nat) where
  | relation (ports : List (Fin d)) (port : Fin d) (left right : Fin 64)
  | equal (left right : List (Fin d))

/-- The number of shared trajectory tapes needed by a single instruction. -/
def Instruction.radius {d : Nat} : Instruction d → Nat
  | .relation ports _ _ _ => ports.length
  | .equal left right => max left.length right.length

end UniqueGamesTheorem.Foundations.PCP.PoweringFieldPlan

/-! Exact tail and reverse-index fields of the actual powering-table rows.
The reverse address is affine in the live starting vertex; the coefficient
and offset depend only on the fixed degree, word, and orientation. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringRowHeaderSemantics

open UniqueGamesTheorem.Foundations.Complexity

variable {vertices d : Nat}

def blockSize (d n : Nat) : Nat := 2 * d ^ (n + 1)

end UniqueGamesTheorem.Foundations.PCP.PoweringRowHeaderSemantics

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PoweringTableSemanticsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
# Exact semantics of the executable powering tables

The explicit label and dart bijections preserve every actual edge test and
every rejected directed occurrence. The inverse label map covers all encoded
assignments, so satisfiability and uniform rejection-count bounds transport
without any consistency restriction on padded labels.
-/

/-!
# The actual first moment of an endpoint-opinion witness

The pivot factorization is applied to actual finite walks. Its two endpoint
operator bounds are obtained from the proved lazy-graph mixture and smoothing
theorem. No witness-event probability law is assumed.
-/

/-! The actual graph-powering soundness bound. Modal endpoint opinions give
the first moment, spectral return gives the second moment, and an actual
checked path constraint turns each witness into rejection. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringSoundness

open scoped BigOperators
open SpectralReturn PoweringMomentBound
open PoweringMoment (bit hits)

variable {V D A : Type*}

def center (q M : Nat) : Nat := (4 * q * M) ^ 2

theorem le_center (q M : Nat) (hq : 1 ≤ q) (hM : 1 ≤ M) : M ≤ center q M := by
  have hfour : 1 ≤ 4 * q := by omega
  have hx : M ≤ 4 * q * M := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right M hfour
  have hone : 1 ≤ 4 * q * M := hM.trans hx
  have hsquare : 4 * q * M ≤ (4 * q * M) * (4 * q * M) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (4 * q * M) hone
  exact hx.trans (by simpa only [center, pow_two] using hsquare)

def gain (q M : Nat) (lambda : ℝ) : ℝ :=
  (1 / (2 * (q : ℝ))) ^ 4 * ((2 * M + 1 : Nat) : ℝ) /
    ((1 + 2 / (1 - lambda)) + 1)

end UniqueGamesTheorem.Foundations.PCP.PoweringSoundness

namespace UniqueGamesTheorem.Foundations.PCP.PoweringGap

open SpectralReturn PoweringSoundness

variable {V D A : Type*}

theorem gain_nonneg (q M : Nat) (lambda : ℝ) (hlambda : lambda < 1) :
    0 ≤ gain q M lambda := by
  have hden : 0 < 1 - lambda := sub_pos.mpr hlambda
  unfold gain
  positivity

end UniqueGamesTheorem.Foundations.PCP.PoweringGap

/-! Actual directed-cut expansion from the graph's zero-mean spectral
certificate. Parallel edges and loops retain their indexed port multiplicities. -/
namespace UniqueGamesTheorem.Foundations.PCP.SpectralCut

open scoped BigOperators
open SpectralReturn

section Indicators
variable {V : Type*} [Fintype V] [DecidableEq V]

def indicator (S : Finset V) (v : V) : ℝ := if v ∈ S then 1 else 0

omit [Fintype V] in
theorem indicator_nonnegative (S : Finset V) (v : V) : 0 ≤ indicator S v := by
  unfold indicator
  split_ifs <;> norm_num
end Indicators

end UniqueGamesTheorem.Foundations.PCP.SpectralCut

/-!
# Uniform restriction of Boolean tapes

Restricting a uniformly sampled Boolean function to a decidable subset gives
the uniform law on functions on that subset.  The subset and its complement
may be empty: their Boolean function spaces still contain the constant-false
function.  Extending by false gives a canonical full-domain oracle address.
-/

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_AlphabetGraphLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetGraph

open UniqueGamesTheorem.Foundations.Hastad
open scoped BigOperators

variable {V E A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem expect_prod {I J : Type*} [Fintype I] [Fintype J] (f : I × J → ℝ) :
    (𝔼 z : I × J, f z) = 𝔼 i : I, 𝔼 j : J, f (i, j) := by
  simpa only [Finset.univ_product_univ] using
    Finset.expect_product (Finset.univ : Finset I) (Finset.univ : Finset J) f

theorem expect_rejection_eq_count {I : Type*} [Fintype I] (b : I → Bool) :
    (𝔼 i : I, AssignmentTester.truth (!(b i))) =
      ((Finset.univ.filter (fun i => b i = false)).card : ℝ) / Fintype.card I := by
  rw [Fintype.expect_eq_sum_div_card]
  congr 1
  calc
    (∑ i : I, AssignmentTester.truth (!(b i))) = ∑ i : I, if b i = false then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      cases b i <;> norm_num [AssignmentTester.truth]
    _ = _ := Finset.sum_boole _ _

end UniqueGamesTheorem.Foundations.PCP.AlphabetGraph

end

/-!
# Real gap and exact size of the alphabet graph

The gap bound is obtained directly from the two checked rejection-count
inequalities. The finite graph's size is linear in the old vertices and darts,
with an explicit coefficient determined only by the old alphabet cardinality.
-/

/-!
# Explicit orders for the alphabet-reduction table

All executable maps use Boolean digits, finite sums, and division/remainder.
No enumeration is chosen from a cardinality proof. Cube coordinate zero is the
least significant bit; pairs of coordinates use row-major order. Event blocks
are ordered by their original dart, followed by the local event. Vertices put
events before vertex addresses before edge addresses. Each event has twelve
ordered darts: six slots, with false then true orientation at each slot.
-/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_AlphabetTableBoundsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.VerifierToCNF

theorem zero_false_count_iff_all (bits : List Bool) :
    bits.count false = 0 ↔ bits.all id = true := by
  induction bits with
  | nil => simp
  | cons b bits ih => cases b <;> simp [ih]

theorem ofFn_getElem_of_length {α : Type*} (xs : List α) (n : Nat) (h : xs.length = n) :
    List.ofFn (fun i : Fin n => xs[i.val]'(by rw [h]; exact i.isLt)) = xs := by
  subst n
  exact List.ofFn_getElem

theorem count_false_map_sum {α : Type*} (xs : List α) (f : α → Bool) :
    (xs.map f).count false = (xs.map (fun x => if f x then 0 else 1)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases h : f x <;> simp [h, ih, Nat.add_comm]

theorem nat_sum_map_le {α : Type*} (xs : List α) (f g : α → Nat)
    (bound : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (bound x (by simp)) (ih (fun y hy => bound y (by simp [hy])))

end UniqueGamesTheorem.Foundations.PCP.VerifierToCNF

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_FinalBooleanVerifier
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.FinalBooleanVerifier

variable {V E : Type*} {n m : Nat}

theorem count_false_map_filter {α : Type*} (xs : List α) (f : α → Bool) :
    (xs.map f).count false = (xs.filter (fun x => decide (f x = false))).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : f x <;> simp [h, ih, Nat.add_comm]

theorem count_false_finRange (f : Fin m → Bool) :
    ((List.finRange m).map f).count false =
      (Finset.univ.filter (fun e : Fin m => f e = false)).card := by
  classical
  calc
    _ = ((List.finRange m).filter (fun e => decide (f e = false))).length :=
      count_false_map_filter _ _
    _ = (((List.finRange m).filter (fun e => decide (f e = false))).toFinset).card :=
      (List.toFinset_card_of_nodup ((List.nodup_finRange m).filter _)).symm
    _ = _ := by
      congr 1
      ext e
      simp

end UniqueGamesTheorem.Foundations.PCP.FinalBooleanVerifier

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularOriginalClean
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Reusable inherited-row execution with actual cleanup

Five concrete drain loops remove the query delimiter, unread scan suffix,
raw reverse field, computed reverse field, and copied relation. With initially
empty work tapes, the only final tape change is the appended output row. The
index on tape zero and input table on tape one are both preserved.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalClean

open Turing PCP

abbrev Tape := MachineRegularOriginalRow.Tape
abbrev Alphabet := MachineRegularOriginalRow.Alphabet

def cleanupTapes (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update base 2 []) 3 []) 4 []) 6 []) 7 []

def cleanupSteps (base : Tape → List Bool) : Nat :=
  ((base 2).length + 1) + ((base 3).length + 1) + ((base 4).length + 1) +
    ((base 6).length + 1) + ((base 7).length + 1)

theorem join_trace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

def timeBound (q inputLength outputLength : Nat) : Nat :=
  (5 * q + 20) * inputLength + 2 * outputLength + 5 * q + 40995

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalClean

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_VertexPadding
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.VertexPadding

open scoped BigOperators

variable {V D A : Type*}

def extendLabeling (extra : ℕ) (defaultA : A) (labeling : V → A) : V ⊕ Fin extra → A :=
  Sum.elim labeling (fun _ => defaultA)

end UniqueGamesTheorem.Foundations.PCP.VertexPadding

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularVertexBlock
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual regularized vertex-block execution

The finite internal-port loop invokes the checked row machine for every port in
order. Each invocation restores the shared 27-tape frame. Inherited-row stages
use fixed tape placements and finite state permutations.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularVertexBlock

open Turing PCP

variable {σ Λ : Type}

/-- A prefix of the emitted rows, defined without any execution hypothesis. -/
def portBits {q : Nat} (bits : Fin q → List Bool) : Nat → List Bool
  | 0 => []
  | k + 1 => portBits bits k ++ if h : k < q then bits ⟨k, h⟩ else []

theorem joinTrace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

/-- Uniform bound on a serialized row in the actual output table. -/
def rowSizeBound (q vertices : Nat) : Nat := vertices + vertices * (q + 1) + 8192

theorem portBits_length_le {q : Nat} (bits : Fin q → List Bool) (bound : Nat)
    (hbits : ∀ p, (bits p).length ≤ bound) (k : Nat) :
    (portBits bits k).length ≤ k * bound := by
  induction k with
  | zero => simp only [portBits, List.length_nil, Nat.zero_mul, le_refl]
  | succ k ih =>
    rw [portBits, List.length_append]
    split_ifs with h
    · have hp := hbits ⟨k, h⟩
      rw [Nat.succ_mul]
      exact Nat.add_le_add ih hp
    · simp only [List.length_nil, Nat.add_zero]
      exact ih.trans (Nat.mul_le_mul_right bound (by omega))

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularVertexBlock

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularOriginalBody
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# One actual original-vertex body of regularization

The finite code composes physical metadata preparation, expander-family
materialization, all vertex rows, and seven metadata drain loops. The outer
loop owns the global vertex counter and keeps it unchanged during this body.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBody

open Turing PCP

theorem joinTrace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBody

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularOwnerCleanup
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup

open Turing

/-- Constructor-by-constructor equality for a fixed sum of tape alphabets. -/
def sumDecidableEq {A B : Type} (left : DecidableEq A) (right : DecidableEq B) :
    DecidableEq (A ⊕ B)
  | .inl a, .inl b => match left a b with
      | .isTrue h => .isTrue (congrArg (Sum.inl : A → A ⊕ B) h)
      | .isFalse h => .isFalse (fun e => h (Sum.inl.inj e))
  | .inr a, .inr b => match right a b with
      | .isTrue h => .isTrue (congrArg (Sum.inr : B → A ⊕ B) h)
      | .isFalse h => .isFalse (fun e => h (Sum.inr.inj e))
  | .inl _, .inr _ => .isFalse (by intro h; cases h)
  | .inr _, .inl _ => .isFalse (by intro h; cases h)

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PoweringPortReindexLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact transport of powering through a change of ports. The target's actual
address selector is pulled back, so no compatibility of enumeration orders or
consistency restriction on raw padded labels is needed. -/

noncomputable section
namespace UniqueGamesTheorem.Foundations.PCP.PoweringPortReindex
open SpectralReturn PoweringSoundness

variable {V D E A : Type*}

def wordEquiv (ports : D ≃ E) (n : Nat) : (Fin n → D) ≃ (Fin n → E) where
  toFun p := fun i => ports (p i)
  invFun p := fun i => ports.symm (p i)
  left_inv p := by funext i; exact ports.symm_apply_apply (p i)
  right_inv p := by funext i; exact ports.apply_symm_apply (p i)

end UniqueGamesTheorem.Foundations.PCP.PoweringPortReindex

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_FinalConstantsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# The fixed constants in the actual powering estimate

The six-bit alphabet has 64 letters. The middle window, endpoint length,
spectral parameter and composition loss in the checked powering theorem give
exactly the constants used in the final amplification round. Large natural
constants remain symbolic in these calculations.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringFinalConstants

abbrev Alphabet := Fin 6 → Bool

@[simp] theorem card_alphabet : Fintype.card Alphabet = 64 := by
  norm_num [Alphabet, Fintype.card_fun]

/-- The spectral denominator is exactly 66 at the fixed return parameter. -/
theorem spectral_denominator_eq :
    (1 + 2 / (1 - (31 / 32 : ℝ))) + 1 = 66 := by
  norm_num

end UniqueGamesTheorem.Foundations.PCP.PoweringFinalConstants

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PreprocessingTablesLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Bounds on actual metadata, stored rotor words, and emitted prefixes. These
are size estimates used inside separately proved machine executions. -/
namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingMachineBounds
open UniqueGamesTheorem.Foundations.Complexity
open scoped BigOperators

/-- A two-parameter bound for the complete unary graph codec. -/
noncomputable def tablePolynomial (a b : Nat) : Polynomial Nat :=
  Polynomial.C a * Polynomial.X + Polynomial.C b * Polynomial.X + 2 +
    (Polynomial.C b * Polynomial.X) *
      (Polynomial.C a * Polynomial.X + Polynomial.C b * Polynomial.X + 8192)

end UniqueGamesTheorem.Foundations.PCP.PreprocessingMachineBounds

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_RawInitialTablesLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit structural numberings of the raw 3SAT incidence graph. Unused
declared variable names are retained; their unary input header pays for them.
The graph has one dummy vertex and one tautological loop, even for an empty
formula. No input-dependent choice of a finite enumeration is made. -/

/-! Polynomial arithmetic for the actual initial-machine phase counts. The
separate execution theorem must connect these counts to the concrete program. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineBudget

open Complexity

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 100 * Polynomial.X ^ 2 + Polynomial.C 60000 * Polynomial.X +
    Polynomial.C 100

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineBudget

/-! Explicit finite predicates and numeric row words of the initial incidence table.
Every relation retains all 4096 entries, including repetitions. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialRows

abbrev Signs := Bool × Bool × Bool
abbrev Names := Nat × Nat × Nat

def dummyWords (n m : Nat) : List Nat :=
  [n + m, 6 * m] ++ List.replicate 4096 1

/-! Exact ordered rows of the initial incidence table. Every relation retains
all 4096 entries, including repetitions; this is a list identity, not a runtime bound. -/

/-- The list induced by an explicit numbering, in increasing numeric order. -/
def orderedList {α : Type*} {n : Nat} (e : α ≃ Fin n) : List α :=
  List.ofFn e.symm

theorem orderedList_cast {α : Type*} {m n : Nat} (e : α ≃ Fin m) (h : m = n) :
    orderedList (e.trans (finCongr h)) = orderedList e := by
  subst n
  rfl

end UniqueGamesTheorem.Foundations.PCP.RawInitialRows

/-! The concrete numbered amplification round, with one fixed base expander.
Every intermediate is an actual stored table, with explicit finite coordinates.
The running-time certificate is a separate theorem about these same functions. -/

/-! Gap amplification for the actual numbered table round. The fixed base
expander is the only supplied construction datum with a spectral certificate. -/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PreprocessingRegularLoopWordsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Prefix and suffix invariants for regular-table row loops

These finite block identities apply to original-vertex blocks, to dummy blocks
within an owner, and to whole owner blocks. They expose exactly the next emitted
block while preserving the codec's established order.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularLoopWords

/-- Bits emitted by the first `k` blocks. -/
def blocksPrefix {n : Nat} (f : Fin n → List Bool) (k : Nat) : List Bool :=
  ((List.ofFn f).take k).flatten

/-- Bits remaining after the first `k` blocks. -/
def blocksSuffix {n : Nat} (f : Fin n → List Bool) (k : Nat) : List Bool :=
  ((List.ofFn f).drop k).flatten

@[simp] theorem blocksPrefix_zero {n : Nat} (f : Fin n → List Bool) :
    blocksPrefix f 0 = [] := by
  simp only [blocksPrefix, List.take_zero, List.flatten_nil]

@[simp] theorem blocksPrefix_all {n : Nat} (f : Fin n → List Bool) :
    blocksPrefix f n = (List.ofFn f).flatten := by
  have h : (List.ofFn f).take n = List.ofFn f := by
    simpa only [List.length_ofFn] using (List.take_length (l := List.ofFn f))
  exact congrArg List.flatten h

theorem blocksPrefix_succ {n : Nat} (f : Fin n → List Bool) (k : Nat) (h : k < n) :
    blocksPrefix f (k + 1) = blocksPrefix f k ++ f ⟨k, h⟩ := by
  unfold blocksPrefix
  rw [List.take_succ_eq_append_getElem
    (show k < (List.ofFn f).length by simpa only [List.length_ofFn] using h)]
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.getElem_ofFn]

@[simp] theorem blocksSuffix_zero {n : Nat} (f : Fin n → List Bool) :
    blocksSuffix f 0 = (List.ofFn f).flatten := by
  simp only [blocksSuffix, List.drop_zero]

@[simp] theorem blocksSuffix_all {n : Nat} (f : Fin n → List Bool) :
    blocksSuffix f n = [] := by
  have h : (List.ofFn f).drop n = [] := by
    simpa only [List.length_ofFn] using (List.drop_length (l := List.ofFn f))
  exact congrArg List.flatten h

/-- The completed and remaining portions partition the original bitstream. -/
theorem blocksPrefix_append_suffix {n : Nat} (f : Fin n → List Bool) (k : Nat) :
    blocksPrefix f k ++ blocksSuffix f k = (List.ofFn f).flatten := by
  unfold blocksPrefix blocksSuffix
  rw [← List.flatten_append, List.take_append_drop]

end UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularLoopWords

end

section

/-! Bounds on the actual output prefixes used by the regularization loops.
The bounds include the stored headers and all earlier original/owner blocks.
They concern actual serialized words; machine executions are proved separately. -/
namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularBounds

open PreprocessingRegularLoopWords
open UniqueGamesTheorem.Foundations.Complexity
open scoped BigOperators

theorem blocksPrefix_length_le {n : Nat} (f : Fin n → List Bool) (k : Nat) :
    (blocksPrefix f k).length ≤ (List.ofFn f).flatten.length := by
  have h := congrArg List.length (blocksPrefix_append_suffix f k)
  simp only [List.length_append] at h
  omega

end UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularBounds

end

section

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineModel

open Turing Complexity Hastad

abbrev Signs := Bool × Bool × Bool
abbrev State := Signs × Option Bool

inductive CopyPhase
  | tailVariables (slot : Fin 3)
  | tailIndex (slot : Fin 3)
  | variableName (slot : Fin 3)
  | reverseIndex (slot : Fin 3) (orientation : Bool)
  | dummyVariables | dummyIndex | dummyReverse
  deriving DecidableEq, Fintype

inductive Label
  | headerStart (slot : Fin 2) | headerLoop (slot : Fin 2)
  | scanN | restoreN | scanM1 | restoreM1 | closeFirst
  | scanM6 | restoreM6 | closeSecond | initializeIndex | guard
  | fieldStart (slot : Fin 6) | fieldLoop (slot : Fin 6) | loadSigns
  | scan (phase : CopyPhase) | restore (phase : CopyPhase)
  | closeTail (slot : Fin 3) (orientation : Bool)
  | closeReverse (slot : Fin 3) (orientation : Bool)
  | relation (slot : Fin 3) (orientation : Bool)
  | cleanupField (slot : Fin 6) | incrementIndex
  | closeDummyTail | closeDummyReverse | dummyRelation
  | cleanupFinal (slot : Fin 3) | reset | finalReverse
  deriving DecidableEq, Fintype

def initialState : State := ((false, false, false), none)

def stateKeys : List State :=
  [false, true].flatMap fun a => [false, true].flatMap fun b =>
    [false, true].flatMap fun c =>
      [none, some false, some true].map fun register => ((a, b, c), register)

theorem stateKeys_complete (state : State) : state ∈ stateKeys := by
  rcases state with ⟨⟨a, b, c⟩, register⟩
  cases a <;> cases b <;> cases c <;> cases register with
  | none => simp [stateKeys]
  | some bit => cases bit <;> simp [stateKeys]

def copyScale : CopyPhase → Nat
  | .reverseIndex _ _ | .dummyReverse => 6
  | _ => 1

def copyNext : CopyPhase → Label
  | .tailVariables slot => .scan (.tailIndex slot)
  | .tailIndex slot => .closeTail slot false
  | .variableName slot => .closeTail slot true
  | .reverseIndex slot orientation => .closeReverse slot orientation
  | .dummyVariables => .scan .dummyIndex
  | .dummyIndex => .closeDummyTail
  | .dummyReverse => .closeDummyReverse

def relationNext (slot : Fin 3) (orientation : Bool) : Label :=
  if orientation then
    if h : slot.val + 1 < 3 then .scan (.tailVariables ⟨slot.val + 1, h⟩)
    else .cleanupField 0
  else .scan (.variableName slot)

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineModel

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularOwnerBody
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual execution and exact runtime of the fixed dummy-owner program. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody

open Turing PCP
open PreprocessingRegularLoopWords

theorem joinTrace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularTable
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual regular-table construction

The header subroutine reads the two original graph headers, computes the
padding total by the actual prefix machine, performs unary addition and
constant multiplication, and appends both resulting header fields. The
outer vertex routines are assembled from actual metadata and row programs.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable

open Turing
open UniqueGamesTheorem.Foundations.PCP

namespace Header

inductive Extra
  | m | index | work | scratch | vertices | darts | emit | output
  deriving DecidableEq

protected abbrev Extra.enumList : List Extra := [.m, .index, .work, .scratch, .vertices, .darts,
  .emit, .output]

protected theorem Extra.enumList_nodup : Extra.enumList.Nodup := by decide

instance instFintypeExtra : Fintype Extra where
  elems := ⟨Extra.enumList, Extra.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Field
  | vertices | darts
  deriving DecidableEq

protected abbrev Field.enumList : List Field := [.vertices, .darts]

protected theorem Field.enumList_nodup : Field.enumList.Nodup := by decide

instance instFintypeField : Fintype Field where
  elems := ⟨Field.enumList, Field.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive CopyPhase
  | count | rEmit | nEmit
  deriving DecidableEq

protected abbrev CopyPhase.enumList : List CopyPhase := [.count, .rEmit, .nEmit]

protected theorem CopyPhase.enumList_nodup : CopyPhase.enumList.Nodup := by decide

instance instFintypeCopyPhase : Fintype CopyPhase where
  elems := ⟨CopyPhase.enumList, CopyPhase.enumList_nodup⟩
  complete x := by cases x <;> decide

variable {σ : Type}

theorem appendTrace {α : Type} (f : α → α) {a b : Nat} {x y z : α}
    (hs : f^[a] x = y) (ht : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, hs, ht]

end Header

namespace Fuel

variable {K Λ σ : Type} [DecidableEq K]

/-- The outer loop consumes one real unary fuel bit. The zero delimiter is
consumed on exit; its temporary finite register is reset on both branches. -/
def guard (fuel : K) (body : Λ) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool) :=
  .pop fuel (fun s bit => (s.1, bit))
    (.branch (fun s => s.2.getD false)
      (.load (fun s => (s.1, none)) (.goto fun _ => body))
      (.load (fun s => (s.1, none))
        (match exit with | some label => .goto fun _ => label | none => .halt)))

/-- Unary successor needs one physical push and no unbounded register. -/
def increment (counter : K) (next : Λ) : TM2.Stmt (fun _ : K => Bool) Λ σ :=
  .push counter (fun _ => true) (.goto fun _ => next)

end Fuel

namespace Top

def sumDecidableEq {A B : Type} (left : DecidableEq A) (right : DecidableEq B) :
    DecidableEq (A ⊕ B)
  | .inl a, .inl b => match left a b with
      | .isTrue h => .isTrue (congrArg (Sum.inl : A → A ⊕ B) h)
      | .isFalse h => .isFalse (fun e => h (Sum.inl.inj e))
  | .inr a, .inr b => match right a b with
      | .isTrue h => .isTrue (congrArg (Sum.inr : B → A ⊕ B) h)
      | .isFalse h => .isFalse (fun e => h (Sum.inr.inj e))
  | .inl _, .inr _ => .isFalse (by intro h; cases h)
  | .inr _, .inl _ => .isFalse (by intro h; cases h)

inductive CopyPhase
  | old | owner
  deriving DecidableEq

protected abbrev CopyPhase.enumList : List CopyPhase := [.old, .owner]

protected theorem CopyPhase.enumList_nodup : CopyPhase.enumList.Nodup := by decide

instance instFintypeCopyPhase : Fintype CopyPhase where
  elems := ⟨CopyPhase.enumList, CopyPhase.enumList_nodup⟩
  complete x := by cases x <;> decide

def counterStacks (old owners dummy work : List Bool) : Fin 4 → List Bool :=
  ![old, owners, dummy, work]

theorem joinTrace_p0 {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

end Top

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularTableTrace
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top

open Turing
open UniqueGamesTheorem.Foundations.PCP

theorem joinTrace_p1 {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

theorem normalizeEmptyAppend {A : Type*} (output : List Bool → A)
    (bits : List Bool) : output ([] ++ bits) = output bits :=
  congrArg output (List.nil_append bits)

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineUnaryEqualityBit
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineUnaryEqualityBit

open Turing

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := (A × Bool × Option Bool) × Option Bool

def clean (ambient : A) : State A := ((ambient, false, none), none)

inductive Label
  | seedLeft | scanLeft | restoreLeft
  | seedRight | scanRight | restoreRight
  | compare | equal | different
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.seedLeft, .scanLeft, .restoreLeft, .seedRight,
  .scanRight, .restoreRight, .compare, .equal, .different]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

/-- Two fixed exits, each containing only literal push instructions. -/
def emit (destination : K) (bit : Bool) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .push destination (fun _ => false)
    (if bit then .push destination (fun _ => true) (exitAt exit) else exitAt exit)

def copySteps (n : Nat) : Nat := 2 * (n + 1) + 1
def compareSteps (a b : Nat) : Nat := max (a + 1) (b + 1) + 1
def steps (a b : Nat) : Nat := copySteps a + copySteps b + compareSteps a b + 1

theorem steps_le (a b : Nat) : steps a b ≤ 3 * (a + b) + 9 := by
  unfold steps copySteps compareSteps
  omega

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.Complexity.MachineUnaryEqualityBit

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PortTableLookup
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Exact word offsets in executable port tables

These are optional list-lookup equalities for the unary-word stream consumed by
the lookup machine. They expose the stored tail, reverse index, and predicate
bit at their actual positions in the existing graph-table serialization.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PortTableLookup

theorem flatMap_word {α β : Type*} (f : α → List β)
    (width j : Nat) (hj : j < width) :
    ∀ (rows : List α), (∀ a ∈ rows, (f a).length = width) →
      ∀ (i : Nat) (row : α), rows[i]? = some row →
        (rows.flatMap f)[width * i + j]? = (f row)[j]? := by
  intro rows
  induction rows with
  | nil =>
      intro _ i row selected
      simp at selected
  | cons a rows ih =>
      intro hwidth i row selected
      have ha : (f a).length = width := hwidth a (by simp)
      cases i with
      | zero =>
          have heq : a = row := by simpa using selected
          subst row
          simp only [Nat.mul_zero, Nat.zero_add, List.flatMap_cons]
          exact List.getElem?_append_left (by omega)
      | succ i =>
          have selected' : rows[i]? = some row := by simpa using selected
          have hskip : (f a).length ≤ width * (i + 1) + j := by
            rw [ha, Nat.mul_add, Nat.mul_one]
            omega
          have hoff : width * (i + 1) + j - (f a).length = width * i + j := by
            rw [ha, Nat.mul_add, Nat.mul_one]
            omega
          rw [List.flatMap_cons, List.getElem?_append_right hskip, hoff]
          exact ih (fun b hb => hwidth b (by simp [hb])) i row selected'

end UniqueGamesTheorem.Foundations.PCP.PortTableLookup

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_PoweringMachineRelationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRelation

open Turing
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

abbrev Alphabet (_ : K) := Bool

def address (vertex : Fin n) (port : Fin d) (position : Fin 4096) : Nat :=
  (4098 * d) * vertex.val + (4098 * port.val + 4 + position.val)

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRelation

/-! A rotor step on the live unary port-table encoding. First read the reverse
dart identifier; then read that dart's tail vertex. This uses no division or
runtime graph data in finite control. Both positional selections are proved
from the actual serialization. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRotor

open Turing
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

abbrev Alphabet (_ : K) := Bool

def reverseRole (i : Fin 5) : Fin 7 :=
  if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 4 else 6

def endpointRole (i : Fin 5) : Fin 7 :=
  if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 5 else 6

theorem reverseRole_injective : Function.Injective reverseRole := by decide
theorem endpointRole_injective : Function.Injective endpointRole := by decide
theorem source_outside_reverse : ∀ i, (1 : Fin 7) ≠ reverseRole i := by decide
theorem reverse_outside_endpoint : ∀ i, (4 : Fin 7) ≠ endpointRole i := by decide

def reverseTapes (tape : Fin 7 → K) : Fin 5 → K := tape ∘ reverseRole
def endpointTapes (tape : Fin 7 → K) : Fin 5 → K := tape ∘ endpointRole

def reverseAddress (vertex : Fin n) (port : Fin d) : Nat :=
  (4098 * d) * vertex.val + (4098 * port.val + 3)

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRotor

/-! Fixed port words are executed by a finite chain of actual rotor programs.
The six shared tapes hold table, query, scan, reverse identifier, scratch and
output. Each walk position has a separate physical vertex tape. The final
unary copy also handles the empty word and preserves the starting vertex. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineWord

open Turing
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

abbrev Alphabet (_ : K) := Bool
abbrev Tape (t : Nat) := Fin 6 ⊕ Fin (t + 1)

def first (t : Nat) : Fin (t + 1) := ⟨0, by omega⟩

def shift (t : Nat) : Tape t → Tape (t + 1) := Sum.map id Fin.succ

theorem shift_injective (t : Nat) : Function.Injective (shift t) := by
  intro a b h
  cases a <;> cases b <;> simp_all [shift]

def rotorRole (t : Nat) (i : Fin 7) : Tape (t + 1) :=
  if i = 0 then .inl 0 else if i = 1 then .inr (first (t + 1)) else
  if i = 2 then .inl 1 else if i = 3 then .inl 2 else
  if i = 4 then .inl 3 else if i = 5 then .inr (first t).succ else .inl 4

theorem rotorRole_injective (t : Nat) : Function.Injective (rotorRole t) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [rotorRole, first, Fin.ext_iff]

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineWord

/-! A fixed shared tape layout for the actual powering field subroutines.
The vertex identifiers live on physical tapes. The trajectory capacity is
fixed by `max`; each bounded word uses its first `t` trajectory tapes. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineTapes

abbrev Tape (max : Nat) := Fin 11 ⊕ Fin max

def table (max : Nat) : Tape max := .inl 0
def start (max : Nat) : Tape max := .inl 1
def query (max : Nat) : Tape max := .inl 2
def scan (max : Nat) : Tape max := .inl 3
def reverse (max : Nat) : Tape max := .inl 4
def scratch (max : Nat) : Tape max := .inl 5
def leftEndpoint (max : Nat) : Tape max := .inl 6
def rightEndpoint (max : Nat) : Tape max := .inl 7
def leftCopy (max : Nat) : Tape max := .inl 8
def rightCopy (max : Nat) : Tape max := .inl 9
def rowOutput (max : Nat) : Tape max := .inl 10

def endpoint (max : Nat) (target : Bool) : Tape max :=
  if target then rightEndpoint max else leftEndpoint max

@[simp] theorem endpoint_false (max : Nat) : endpoint max false = leftEndpoint max := rfl
@[simp] theorem endpoint_true (max : Nat) : endpoint max true = rightEndpoint max := rfl

/-- Table, query, scan, reverse identifier, scratch, selected endpoint. -/
def wordSharedRole (target : Bool) (i : Fin 6) : Fin 11 :=
  if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 3 else
  if i = 3 then 4 else if i = 4 then 5 else if target then 7 else 6

/-- Position zero is the caller's starting vertex; later positions are the
separate physical trajectory tapes. -/
def trajectoryPlacement {t max : Nat} (h : t ≤ max) : Fin (t + 1) → Tape max :=
  Fin.cases (start max) (fun i => .inr (Fin.castLE h i))

def wordPlacement {t max : Nat} (h : t ≤ max) (target : Bool) :
    PoweringMachineWord.Tape t → Tape max
  | .inl i => .inl (wordSharedRole target i)
  | .inr i => trajectoryPlacement h i

@[simp] theorem wordPlacement_inl_zero {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 0) = table max := rfl
@[simp] theorem wordPlacement_inl_one {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 1) = query max := rfl
@[simp] theorem wordPlacement_inl_two {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 2) = scan max := rfl
@[simp] theorem wordPlacement_inl_three {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 3) = reverse max := rfl
@[simp] theorem wordPlacement_inl_four {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 4) = scratch max := rfl
@[simp] theorem wordPlacement_inl_five {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 5) = endpoint max target := by cases target <;> rfl
@[simp] theorem wordPlacement_first {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inr (PoweringMachineWord.first t)) = start max := rfl
@[simp] theorem wordPlacement_succ {t max : Nat} (h : t ≤ max) (target : Bool) (i : Fin t) :
    wordPlacement h target (.inr i.succ) = .inr (Fin.castLE h i) := rfl

def relationPlacement (max : Nat) (i : Fin 6) : Tape max :=
  .inl (if i = 0 then 6 else if i = 1 then 0 else if i = 2 then 2 else
    if i = 3 then 3 else if i = 4 then 10 else 5)

@[simp] theorem relationPlacement_zero (max : Nat) : relationPlacement max 0 = leftEndpoint max := rfl
@[simp] theorem relationPlacement_one (max : Nat) : relationPlacement max 1 = table max := rfl
@[simp] theorem relationPlacement_two (max : Nat) : relationPlacement max 2 = query max := rfl
@[simp] theorem relationPlacement_three (max : Nat) : relationPlacement max 3 = scan max := rfl
@[simp] theorem relationPlacement_four (max : Nat) : relationPlacement max 4 = rowOutput max := rfl
@[simp] theorem relationPlacement_five (max : Nat) : relationPlacement max 5 = scratch max := rfl

def equalityPlacement (max : Nat) (i : Fin 6) : Tape max :=
  .inl (if i = 0 then 6 else if i = 1 then 7 else if i = 2 then 8 else
    if i = 3 then 9 else if i = 4 then 5 else 10)

@[simp] theorem equalityPlacement_zero (max : Nat) : equalityPlacement max 0 = leftEndpoint max := rfl
@[simp] theorem equalityPlacement_one (max : Nat) : equalityPlacement max 1 = rightEndpoint max := rfl
@[simp] theorem equalityPlacement_two (max : Nat) : equalityPlacement max 2 = leftCopy max := rfl
@[simp] theorem equalityPlacement_three (max : Nat) : equalityPlacement max 3 = rightCopy max := rfl
@[simp] theorem equalityPlacement_four (max : Nat) : equalityPlacement max 4 = scratch max := rfl
@[simp] theorem equalityPlacement_five (max : Nat) : equalityPlacement max 5 = rowOutput max := rfl

theorem wordSharedRole_injective (target : Bool) : Function.Injective (wordSharedRole target) := by
  cases target <;> decide

theorem wordSharedRole_ne_start (target : Bool) :
    ∀ i : Fin 6, wordSharedRole target i ≠ 1 := by
  cases target <;> decide

theorem trajectoryPlacement_injective {t max : Nat} (ht : t ≤ max) :
    Function.Injective (trajectoryPlacement ht) := by
  intro a b
  refine Fin.cases ?_ (fun i => ?_) a
  · refine Fin.cases ?_ (fun j => ?_) b
    · intro _
      rfl
    · intro h
      change (Sum.inl (1 : Fin 11) : Tape max) = .inr (Fin.castLE ht j) at h
      cases h
  · refine Fin.cases ?_ (fun j => ?_) b
    · intro h
      change (Sum.inr (Fin.castLE ht i) : Tape max) = .inl (1 : Fin 11) at h
      cases h
    · intro h
      change (Sum.inr (Fin.castLE ht i) : Tape max) = .inr (Fin.castLE ht j) at h
      have hc : Fin.castLE ht i = Fin.castLE ht j := Sum.inr.inj h
      have hv : i.val = j.val := congrArg (fun x : Fin max => x.val) hc
      have hij : i = j := Fin.ext hv
      exact congrArg Fin.succ hij

theorem wordShared_ne_trajectory {t max : Nat} (ht : t ≤ max) (target : Bool)
    (i : Fin 6) :
    ∀ j : Fin (t + 1),
      (Sum.inl (wordSharedRole target i) : Tape max) ≠ trajectoryPlacement ht j := by
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · intro h
    change (Sum.inl (wordSharedRole target i) : Tape max) = .inl (1 : Fin 11) at h
    exact wordSharedRole_ne_start target i (Sum.inl.inj h)
  · intro h
    change (Sum.inl (wordSharedRole target i) : Tape max) = .inr (Fin.castLE ht k) at h
    cases h

/-- Every tape used by a bounded word is placed on its own physical tape. -/
theorem wordPlacement_injective {t max : Nat} (ht : t ≤ max) (target : Bool) :
    Function.Injective (wordPlacement ht target) := by
  intro a b h
  cases a with
  | inl i =>
      cases b with
      | inl j =>
          exact congrArg Sum.inl (wordSharedRole_injective target (Sum.inl.inj h))
      | inr j =>
          exact False.elim (wordShared_ne_trajectory ht target i j h)
  | inr i =>
      cases b with
      | inl j =>
          exact False.elim (wordShared_ne_trajectory ht target j i h.symm)
      | inr j =>
          exact congrArg Sum.inr (trajectoryPlacement_injective ht h)

theorem relationPlacement_injective (max : Nat) : Function.Injective (relationPlacement max) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [relationPlacement]

theorem equalityPlacement_injective (max : Nat) : Function.Injective (equalityPlacement max) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [equalityPlacement]

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineTapes

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_PoweringMachineEqualityField
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Actual producer for equality of two bounded walk endpoints

The two port words are fixed finite control. Each executes against the live
rotor table from the same preserved starting vertex. Their endpoint fields
are compared by the physical unary equality primitive. The emitted field is
the Boolean equality of the two actual walk endpoints.

Work tapes may retain arbitrary histories. The table, start, scratch and two
comparison copies satisfy exact frame theorems. There is no execution or
running-time premise in the composite trace theorem.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineEqualityField

open Turing
open PCP

variable {K Λ A : Type} [DecidableEq K]
variable {max l r n d : Nat}

abbrev Alphabet (_ : K) := Bool
abbrev Tape := PoweringMachineTapes.Tape
abbrev State := MachineUnaryEqualityBit.State

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {u v : Nat}
    (first : f^[u] a = b) (second : f^[v] b = c) : f^[u + v] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineEqualityField

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_PoweringMachineLoop
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-control preparation and enumeration for the powered-table
machine. The degree and radius determine a fixed multiplier `B = 2*d^t`.
Only the input vertex count varies at runtime, and it is stored on unary
tapes. The header machine consumes a cloned first input field, preserving
its unread suffix, and writes the three fields needed by the outer loop.

The row enumeration lemmas specify the canonical suffix invariant used with
`MachineCountedLoop`. They do not stand in for the caller's per-row machine
traces, which must be supplied by the actual walk and relation evaluator. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineLoop

open Turing

inductive HeaderTape
  | source | counter | vertices | darts
  deriving DecidableEq

protected abbrev HeaderTape.enumList : List HeaderTape := [.source, .counter, .vertices, .darts]

protected theorem HeaderTape.enumList_nodup : HeaderTape.enumList.Nodup := by decide

instance instFintypeHeaderTape : Fintype HeaderTape where
  elems := ⟨HeaderTape.enumList, HeaderTape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive HeaderLabel
  | initialize_ | scan
  deriving DecidableEq

protected abbrev HeaderLabel.enumList : List HeaderLabel := [.initialize_, .scan]

protected theorem HeaderLabel.enumList_nodup : HeaderLabel.enumList.Nodup := by decide

instance instFintypeHeaderLabel : Fintype HeaderLabel where
  elems := ⟨HeaderLabel.enumList, HeaderLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev HeaderAlphabet (_ : HeaderTape) := Bool
abbrev HeaderState (σ : Type) := σ × Option Bool

/-- A syntactic chain of a fixed number of true-bit pushes. -/
def pushTrue {K Λ σ : Type} (destination : K) : Nat →
    TM2.Stmt (fun _ : K => Bool) Λ σ → TM2.Stmt (fun _ : K => Bool) Λ σ
  | 0, next => next
  | count + 1, next => pushTrue destination count (.push destination (fun _ => true) next)

theorem stepAux_pushTrue {K Λ σ : Type} [DecidableEq K]
    (destination : K) (count : Nat) (next : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (pushTrue destination count next) state tapes =
      TM2.stepAux next state
        (Function.update tapes destination (List.replicate count true ++ tapes destination)) := by
  induction count generalizing next with
  | zero => simp [pushTrue]
  | succ count ih =>
    rw [pushTrue, ih]
    simp [TM2.stepAux, List.replicate_succ, Function.update_idem]

/-- Each true bit from the first input field contributes one counter bit,
one vertex-header bit, and `B` dart-header bits. No numeric register is used. -/
def headerProgram {σ : Type} (B : Nat) :
    HeaderLabel → TM2.Stmt HeaderAlphabet HeaderLabel (HeaderState σ)
  | .initialize_ =>
      .push .counter (fun _ => false)
        (.push .vertices (fun _ => false)
          (.push .darts (fun _ => false)
            (.load (fun state => (state.1, none)) (.goto fun _ => .scan))))
  | .scan =>
      .pop .source (fun state head => (state.1, head))
        (.branch (fun state => state.2.getD false)
          (.push .counter (fun _ => true)
            (.push .vertices (fun _ => true)
              (pushTrue .darts B
                (.load (fun state => (state.1, none)) (.goto fun _ => .scan)))))
          (.load (fun state => (state.1, none)) .halt))

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineLoop

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_PoweringMachineInitialize
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Actual powering initialization on the common finite tape set. The first
unary input field is copied by the affine machine and consumed by the checked
header program. The original input and every unrelated tape are preserved.
No runtime graph or vertex count is captured by the finite program. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize

open Turing
open PoweringMachineLoop

abbrev ExtraTape (max : Nat) := PoweringMachineTapes.Tape max ⊕ Unit
abbrev GlobalTape (max : Nat) := HeaderTape ⊕ ExtraTape max

def finalOutput (max : Nat) : GlobalTape max := .inr (.inr ())

/-- The unary start vertex and outer counter occupy the same physical tape. -/
def commonPlacement (max : Nat) (tape : PoweringMachineTapes.Tape max) : GlobalTape max :=
  if tape = PoweringMachineTapes.start max then .inl .counter else .inr (.inl tape)

theorem commonPlacement_injective (max : Nat) : Function.Injective (commonPlacement max) := by
  intro a b h
  by_cases ha : a = PoweringMachineTapes.start max <;>
    by_cases hb : b = PoweringMachineTapes.start max <;>
      simp_all [commonPlacement]

@[simp] theorem commonPlacement_start (max : Nat) :
    commonPlacement max (PoweringMachineTapes.start max) = .inl .counter := by
  simp [commonPlacement]

@[simp] theorem commonPlacement_table (max : Nat) :
    commonPlacement max (PoweringMachineTapes.table max) =
      .inr (.inl (PoweringMachineTapes.table max)) := by
  simp [commonPlacement, PoweringMachineTapes.table, PoweringMachineTapes.start]

@[simp] theorem commonPlacement_scratch (max : Nat) :
    commonPlacement max (PoweringMachineTapes.scratch max) =
      .inr (.inl (PoweringMachineTapes.scratch max)) := by
  simp [commonPlacement, PoweringMachineTapes.scratch, PoweringMachineTapes.start]

@[simp] theorem commonPlacement_rowOutput (max : Nat) :
    commonPlacement max (PoweringMachineTapes.rowOutput max) =
      .inr (.inl (PoweringMachineTapes.rowOutput max)) := by
  simp [commonPlacement, PoweringMachineTapes.rowOutput, PoweringMachineTapes.start]

theorem commonPlacement_ne_finalOutput (max : Nat) (tape : PoweringMachineTapes.Tape max) :
    commonPlacement max tape ≠ finalOutput max := by
  by_cases h : tape = PoweringMachineTapes.start max <;>
    simp [commonPlacement, finalOutput, h]

theorem commonPlacement_ne_header (max : Nat) (tape : PoweringMachineTapes.Tape max)
    (field : HeaderTape) (hne : field ≠ .counter) :
    commonPlacement max tape ≠ .inl field := by
  by_cases h : tape = PoweringMachineTapes.start max <;>
    simp [commonPlacement, h, Ne.symm hne]

def castTapes {K : Type} {Γ Δ : K → Type} (h : Γ = Δ)
    (tapes : ∀ k, List (Γ k)) : ∀ k, List (Δ k) := h ▸ tapes

def castStatement {K Λ σ : Type} {Γ Δ : K → Type} (h : Γ = Δ)
    (q : TM2.Stmt Γ Λ σ) : TM2.Stmt Δ Λ σ := h ▸ q

def castConfiguration {K Λ σ : Type} {Γ Δ : K → Type} (h : Γ = Δ)
    (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Δ Λ σ := h ▸ c

theorem castTapes_apply {K : Type} {Γ Δ : K → Type} (h : Γ = Δ)
    (tapes : ∀ k, List (Γ k)) (k : K) :
    castTapes h tapes k = cast (congrArg (fun alphabet => List (alphabet k)) h) (tapes k) := by
  cases h
  rfl

theorem castConfiguration_mk {K Λ σ : Type} {Γ Δ : K → Type} (h : Γ = Δ)
    (label : Option Λ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    castConfiguration h ⟨label, state, tapes⟩ = ⟨label, state, castTapes h tapes⟩ := by
  cases h
  rfl

theorem stepAux_cast {K Λ σ : Type} [DecidableEq K]
    {Γ Δ : K → Type} (h : Γ = Δ) (q : TM2.Stmt Γ Λ σ)
    (state : σ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (castStatement h q) state (castTapes h tapes) =
      castConfiguration h (TM2.stepAux q state tapes) := by
  cases h
  rfl

def mergeTapes {max : Nat} (header : HeaderTape → List Bool)
    (extra : ExtraTape max → List Bool) : GlobalTape max → List Bool
  | .inl k => header k
  | .inr e => extra e

def initialGlobalTapes {max : Nat} (extra : ExtraTape max → List Bool) :
    GlobalTape max → List Bool := mergeTapes (fun _ => []) extra

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_PoweringGlobalEnumerationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Explicit executable enumeration of the global powering tapes

The four header tapes come first, followed by the eleven shared roles, the
bounded trajectory tapes, and the final output tape. Both directions use
constructor cases and arithmetic sum encodings. No enumeration is selected
from a cardinality theorem.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalEnumeration

open PoweringMachineLoop PoweringMachineInitialize

/-- The single extra output tape occupies its unique local index. -/
def unitTapeEquiv : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv u := by cases u; rfl
  right_inv i := (Fin.eq_zero i).symm

def sharedTapeEquiv (max : Nat) : PoweringMachineTapes.Tape max ≃ Fin (11 + max) :=
  finSumFinEquiv

end UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalEnumeration

/-! A concrete relation-field producer: execute a fixed word from the live
start vertex, then read the predicate at the reached vertex and fixed port.
All instructions use the shared tape layout and preserve the finite row
buffer. No execution premise is supplied by the caller. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRelationField

open Turing
open PCP

variable {K Λ A : Type} [DecidableEq K]
variable {n d max : Nat}

abbrev Alphabet (_ : K) := Bool

def lookupTapes (placement : PoweringMachineTapes.Tape max → K) (i : Fin 5) : K :=
  placement (PoweringMachineTapes.relationPlacement max i.succ)

omit [DecidableEq K] in
theorem lookupTapes_injective (placement : PoweringMachineTapes.Tape max → K)
    (distinct : Function.Injective placement) : Function.Injective (lookupTapes placement) := by
  intro i j h
  exact (Fin.succ_injective _) ((PoweringMachineTapes.relationPlacement_injective max) (distinct h))

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRelationField

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineField

open Turing PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {n d max : Nat}

abbrev Tape := PoweringMachineTapes.Tape

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineField

/-! The concrete finite program that produces an entire powered-row input
block. Its static control executes the field plan backwards, so prepending each
computed unary Boolean field leaves the canonical serialized block in order. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachinePlan

open Turing PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {vertices d max : Nat}

abbrev Command (d max : Nat) := {op : Instruction d // op.radius ≤ max}

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachinePlan

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRowHeaders

open Turing
open PCP PoweringRowHeaderSemantics
open PoweringMachineTapes

variable {K Λ σ : Type} [DecidableEq K]
variable {vertices d max : Nat}

/-- The existing word placement, with its result directed to row-output 10. -/
def headerPlacement {t max : Nat} (h : t ≤ max) : PoweringMachineWord.Tape t → Tape max :=
  (Equiv.swap (leftEndpoint max) (rowOutput max)) ∘ wordPlacement h false

theorem headerPlacement_injective {t max : Nat} (h : t ≤ max) :
    Function.Injective (headerPlacement h) :=
  (Equiv.swap (leftEndpoint max) (rowOutput max)).injective.comp (wordPlacement_injective h false)

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRowHeaders

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_PoweringMachineFinish
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Physical output headers followed by complete work-tape cleanup

The finite program first copies the dart-count word onto the existing row
output, then copies the vertex-count word, and finally drains every tape except
the output. Both unary header values are read from physical tapes; they do not
parameterize the program. Header sources and their unread suffixes are restored
by the two copies before cleanup. The final configuration contains the full
encoded header and rows on the output tape and empty words on every other tape.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish

open Turing

variable {K Λ σ : Type} [DecidableEq K] {N : Nat}

abbrev Alphabet (_ : K) := Bool

def copySteps (n m : Nat) : Nat := (2 * (m + 1) + 1) + (2 * (n + 1) + 1)

theorem copySteps_eq (n m : Nat) : copySteps n m = 2 * (n + m) + 6 := by
  unfold copySteps
  omega

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_PoweringPlanBudget
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Execution budget of the concrete powered-row field plan

The cost is the sum of the actual relation and endpoint-comparison transition
counts. Each fixed command scans only the serialized input graph. The execution
certificates below instantiate the concrete plan trace; no execution witness or
running-time bound is assumed.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringPlanBudget

open Turing PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {vertices d max : Nat}

/-- A common bound for either concrete field operation of radius at most `max`. -/
def fieldBudget (max inputLength : Nat) : Nat :=
  (28 * max + 10) * inputLength + 24 * max + 15

end UniqueGamesTheorem.Foundations.Complexity.PoweringPlanBudget

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_PoweringMachineRowBody
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRowBody

open Turing PCP

variable {K Λ : Type} [DecidableEq K] {vertices d : Nat}

abbrev capacity (n : Nat) := 2 * (n + 1)

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRowBody

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_Addresses
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Affine numeric fields of the alphabet-reduction table

The five unbounded unary inputs are n, m, e, tail, head, in that order.
Every field uses a fixed list of natural coefficients and one bounded offset.
For a fixed local event and slot, the query field's coefficient list does not
depend on the input predicate. The predicate changes only its bounded offset.
Evaluation uses the same `Emitter.affineValue` as the actual unary emitter.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Addresses

open UniqueGamesTheorem.Foundations.Hastad

abbrev Terms := List (Fin 5 × Nat)

structure Field (bound : Nat) where
  terms : Terms
  offset : Fin bound

def values (n m edge tail head : Nat) : Fin 5 → Nat := ![n, m, edge, tail, head]

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Addresses

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_AmplificationIteration
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The finite iteration and size arithmetic for an amplification transformation.
The transformation itself must be supplied by the actual graph construction;
these theorems do not assert that such a transformation exists.  In particular,
the polynomial size estimate below is not a machine runtime certificate.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AmplificationIteration

theorem min_double_min (u cap : ℝ) (hc : 0 ≤ cap) :
    min (2 * min u cap) cap = min (2 * u) cap := by
  by_cases hu : u ≤ cap
  · rw [min_eq_left hu]
  · have hcu : cap ≤ u := le_of_not_ge hu
    rw [min_eq_right hcu, min_eq_right (by linarith : cap ≤ 2 * cap),
      min_eq_right (by linarith : cap ≤ 2 * u)]

/-- A concrete logarithmic iteration count, including the zero input. -/
def rounds (n : Nat) : Nat := Nat.log2 n + 1

theorem rounds_large (n : Nat) : n < 2 ^ rounds n := by
  simpa [rounds, Nat.log2_eq_log_two] using
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n)

end UniqueGamesTheorem.Foundations.PCP.AmplificationIteration

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_ActualCanonicalLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.ActualCanonical

open scoped BigOperators

universe u v w
variable {Name : Type u} {Id : Type v} {R : Type w}
variable {k : Nat}
variable [AddCommGroup R]
  [DecidableEq R]

def singletonTriple (i : Fin 3) (c : R) : Fin 3 → R := Pi.single i c

end UniqueGamesTheorem.Reduction.ActualCanonical

end

section

namespace UniqueGamesTheorem.Reduction.CloneGap

variable {α : Type*} {β : Type*} {Name : Type}

theorem count_const (xs : List α) (b : Bool) :
    xs.countP (fun _ => b) = if b then xs.length else 0 := by
  cases b <;> simp

end UniqueGamesTheorem.Reduction.CloneGap

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_FoldedEquationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Hastad.FoldedEquation

open UniqueGamesTheorem.Reduction.CloneGap
open scoped BigOperators

variable {I J : Type}

theorem xor_corrections (a b c u v w : Bool) :
    ((a ^^ b ^^ c) == (u ^^ v ^^ w)) =
      !((a ^^ u) ^^ (b ^^ v) ^^ (c ^^ w)) := by
  cases a <;> cases b <;> cases c <;> cases u <;> cases v <;> cases w <;> rfl

end UniqueGamesTheorem.Foundations.Hastad.FoldedEquation

end

section

namespace UniqueGamesTheorem.Outer.Clone100Counting

open scoped BigOperators

abbrev Index := Fin 100
abbrev Triple := Index × Index × Index

def sign (b : Bool) : ℚ := if b then -1 else 1

def bias (f : Index → Bool) : ℚ := (∑ i, sign (f i)) / 100

/-- A deterministic majority, resolving a zero bias to `false`. -/
def majorityBit (f : Index → Bool) : Bool := decide (bias f < 0)

def parityIndicator (a b c rhs : Bool) : ℚ :=
  if (xor (xor a b) c) == rhs then 1 else 0

def unconditionedScore (p q r : Index → Bool) (rhs : Bool) : ℚ :=
  (∑ t : Triple, parityIndicator (p t.1) (q t.2.1) (r t.2.2) rhs) / 1000000

theorem independent_product_sum (p q r : Index → ℚ) :
    (∑ t : Triple, p t.1 * q t.2.1 * r t.2.2) =
      (∑ i, p i) * (∑ j, q j) * (∑ k, r k) := by
  simp only [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  simp_rw [← Finset.sum_mul]
  simp_rw [← Finset.mul_sum]
  simp_rw [← Finset.sum_mul]

def conditionedScore (good : Triple → Prop) [DecidablePred good]
    (p q r : Index → Bool) (rhs : Bool) : ℚ :=
  (∑ t : {t : Triple // good t},
    parityIndicator (p t.val.1) (q t.val.2.1) (r t.val.2.2) rhs) / 970200

end UniqueGamesTheorem.Outer.Clone100Counting

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_Clone100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Outer.Clone100

open UniqueGamesTheorem.Reduction CloneGap
open Clone100Counting
open scoped BigOperators

noncomputable section

theorem count_as_sum {A : Type} (xs : List A) (p : A → Bool) :
    (xs.countP p : ℚ) = (xs.map (fun x => if p x then (1 : ℚ) else 0)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases h : p x <;> simp [h, ih, add_comm]

end
end UniqueGamesTheorem.Outer.Clone100

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_RuntimeModel
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The finite registers and physical tape roles of the alphabet-table machine.
Input-sized numbers occur only on unary tapes. The comparison and emitter
register layouts are related by explicit, executable product rearrangements.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.RuntimeModel

open Turing
open UniqueGamesTheorem.Foundations.Complexity

inductive Tape
  | original | cursor | scan | vertices | darts | counter | edge
  | tail | reverseIndex | head | scratch | indexScan
  | compareLeft | compareRight | reversed | output
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.original, .cursor, .scan, .vertices, .darts,
  .counter, .edge, .tail, .reverseIndex, .head, .scratch, .indexScan, .compareLeft, .compareRight,
  .reversed, .output]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Alphabet (_ : Tape) := Bool

/-- Self-loop flag, comparison mismatch flag, and second head register. -/
abbrev Flags := Bool × Bool × Option Bool

def setupPorts : Fin 7 → Tape :=
  ![.original, .cursor, .vertices, .darts, .counter, .scratch, .edge]

def headPorts : Fin 6 → Tape :=
  ![.original, .reverseIndex, .scan, .indexScan, .head, .scratch]

def rowSources : Fin 5 → Tape := ![.vertices, .darts, .edge, .tail, .head]
def headerSources : Fin 2 → Tape := ![.vertices, .darts]
def fieldPorts : Fin 3 → Tape := ![.tail, .reverseIndex, .head]

def cleanupPorts : Fin 15 → Tape :=
  ![.original, .cursor, .scan, .vertices, .darts, .counter, .edge,
    .tail, .reverseIndex, .head, .scratch, .indexScan, .compareLeft, .compareRight, .reversed]

theorem cleanupPorts_cover (tape : Tape) (h : tape ≠ .output) :
    ∃ i, cleanupPorts i = tape := by
  cases tape
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨6, rfl⟩
  · exact ⟨7, rfl⟩
  · exact ⟨8, rfl⟩
  · exact ⟨9, rfl⟩
  · exact ⟨10, rfl⟩
  · exact ⟨11, rfl⟩
  · exact ⟨12, rfl⟩
  · exact ⟨13, rfl⟩
  · exact ⟨14, rfl⟩
  · exact (h rfl).elim

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.RuntimeModel

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_CompareLoop
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.CompareLoop

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open RuntimeModel

inductive Label
  | leftFirst | leftSecond | rightFirst | rightSecond | compare
  | equalStore | differentStore
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.leftFirst, .leftSecond, .rightFirst,
  .rightSecond, .compare, .equalStore, .differentStore]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

variable {q : Nat} {Λ : Type}

def comparisonTime (tailName headName : Nat) : Nat :=
  2 * (tailName + 2) + 2 * (headName + 2) + max (tailName + 1) (headName + 1) + 2

theorem comparisonTime_le_of_lt (tailName headName N : Nat)
    (hTail : tailName < N) (hHead : headName < N) :
    comparisonTime tailName headName ≤ 5 * N + 6 := by
  have hm : max (tailName + 1) (headName + 1) ≤ N := max_le (by omega) (by omega)
  unfold comparisonTime
  omega

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.CompareLoop

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_EmitRows
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The actual alphabet-reduction row template. The old predicate and the loop flag
are finite registers. All unbounded quantities reside in five preserved unary
tapes. The fixed event/slot/orientation order is retained without deduplication.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.EmitRows

open Turing
open UniqueGamesTheorem.Foundations.Complexity

abbrev Context (q : Nat) := Vector Bool (q * q) × Bool

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

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.EmitRows

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_HonestTestLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceTape

open scoped BigOperators

section Expectations

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem expect_prod (H : X × Y → ℝ) :
    (𝔼 p : X × Y, H p) = 𝔼 x : X, 𝔼 y : Y, H (x, y) := by
  simpa only [Finset.univ_product_univ] using
    (Finset.expect_product (Finset.univ : Finset X) (Finset.univ : Finset Y) H)

end Expectations

end UniqueGamesTheorem.Foundations.Hastad.SourceTape

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_Setup
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Setup

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

abbrev Ports (K : Type) := Fin 7 → K

inductive Label
  | copyFirst | copySecond | verticesStart | verticesLoop
  | dartsStart | dartsLoop | counterFirst | counterSecond | initialize_
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.copyFirst, .copySecond, .verticesStart,
  .verticesLoop, .dartsStart, .dartsLoop, .counterFirst, .counterSecond, .initialize_]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Setup

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_Initialization
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual setup-to-guard execution of the alphabet-table driver. The preserved
input is parsed by Setup; the finite header template runs through an explicit
state equivalence. The resulting loop invariant is a complete tape equation.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Initialization

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

def time (N : Nat) : Nat := (6 * N + 11) + (7 * (3 * (N + 1) + 3) + 1)

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Initialization

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_RawInitialMachineReadClause
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Read exactly one concrete six-field CNF clause in the actual global machine,
then execute its real sign-loading instruction. No extra finish transition
is inserted. Every unrelated tape and the unread input suffix are preserved.
-/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause

open Turing Complexity Hastad RawInitialMachineModel

theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_RawInitialMachineCleanup
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
Actual cleanup of all six clause-field tapes followed by the global unary
index increment. The output accumulator, unread input, and other caller tapes
are preserved, and no additional finish instruction is assumed.
-/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineCleanup

open Turing Complexity RawInitialMachineModel RawInitialMachineReadClause

theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineCleanup

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_RawInitialMachineStart
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
Actual execution of the raw initial graph machine from its standard input
configuration to the first clause-loop guard. The unread clause bits are
preserved verbatim, and all tape contents at the boundary are explicit.
-/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineStart

open Turing Complexity Hastad RawInitialMachineModel

theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineStart

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_RawInitialMachineRows
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! The six incidence rows are emitted by the actual finite program, with
their exact order, full relation lists, transition count, and tape frame. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineRows

open Turing Complexity RawInitialMachineModel


theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineRows

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_RawInitialMachineBody
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! One complete clause iteration of the actual initial graph machine. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineBody

open Turing Complexity RawInitialMachineModel
open RawInitialMachineReadClause RawInitialMachineRows RawInitialMachineBudget

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineBody

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_RawInitialMachineFinish
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact execution of the dummy-row and final cleanup/reversal phases. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineFinish

open Turing Complexity RawInitialMachineModel

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineFinish

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_RawInitialMachineLoop
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact execution of the clause loop, in the original occurrence order. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoop

open Turing Complexity RawInitialMachineModel
open RawInitialMachineBudget RawInitialMachineBody RawInitialMachineFinish

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoop

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_MachineRawInitialTable
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The actual finite machine computing the initial graph's full serialized
table. The runtime bound counts every parse, row, cleanup and output reversal. -/

namespace UniqueGamesTheorem.Foundations.PCP.MachineRawInitialTable

open Turing Complexity RawInitialMachineModel
open RawInitialMachineBudget RawInitialMachineLoop

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.PCP.MachineRawInitialTable

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PoweringTableLayout
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Vertex-major serialization of the actual powering table

Each vertex contributes a fixed number of consecutive stored dart rows. The
identities below group the actual vector, including every predicate entry, and
then apply the shared word codec. They do not assume an output layout or assert
a machine running time. Unary bit lengths can vary with the stored indices.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringTableLayout

open UniqueGamesTheorem.Foundations.Complexity

/-- One adjacent orientation pair for each recorded port word. -/
def blockSize (d n : Nat) : Nat := 2 * d ^ (n + 1)

theorem vector_toList_ofFn {α : Type*} {m : Nat} (rows : Vector α m) :
    rows.toList = List.ofFn (fun i : Fin m => rows[i]) := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp

/-- Regroup a stored vector without changing, omitting, or permuting a row. -/
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

end UniqueGamesTheorem.Foundations.PCP.PoweringTableLayout

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceAddressArithmeticLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceBounds

open UniqueGamesTheorem.Reduction

/-- The two padded long-code tables and one global dummy bit. -/
def bitCountFormula (n m u : ℕ) : ℕ :=
  n ^ u * 2 ^ (2 ^ u) + m ^ u * 2 ^ (8 ^ u) + 1

/-- Depends on the fixed repetition count alone. -/
def bitCoefficient (u : ℕ) : ℕ := 2 ^ (2 ^ u) + 2 ^ (8 ^ u) + 1

end UniqueGamesTheorem.Foundations.Hastad.SourceBounds

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceFieldArrayLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceClauseLookup

open Turing
open UniqueGamesTheorem.Foundations.Complexity

inductive Label
  | copyOut | copyBack | headerFirst | headerSecond | guard
  | skip (slot : Fin 6)
  | read (slot : Fin 7 × Bool)
  deriving DecidableEq, Fintype

def skipLabel (r : Nat) : Label := if h : r < 6 then .skip ⟨r, h⟩ else .guard
def headerLabel (r : Nat) : Label :=
  if r = 0 then .headerFirst else if r = 1 then .headerSecond else .guard

noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 4 * Polynomial.X + Polynomial.C 10

theorem timePolynomial_eval (L : Nat) : timePolynomial.eval L = 4 * L + 10 := by
  simp [timePolynomial]

end UniqueGamesTheorem.Foundations.Hastad.SourceClauseLookup

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceContextLoad
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! A shared-arena context loader. Its finite program copies each selected
clause index, executes the checked lookup, and clears consumed scratch tapes.
Tuple digits and arbitrary extra tapes are protected throughout. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad

open Turing UniqueGamesTheorem.Foundations.Complexity

inductive Label (u : Nat)
  | copyOut (coordinate : Fin u) | copyBack (coordinate : Fin u)
  | lookup (coordinate : Fin u) (localLabel : SourceClauseLookup.Label)
  | clearWork (coordinate : Fin u) | clearIndex (coordinate : Fin u)
  | done
  deriving DecidableEq, Fintype

variable {u : Nat} {Extra : Type}

variable [DecidableEq Extra]

def placedLabel (j : Fin u) : Option SourceClauseLookup.Label → Option (Label u)
  | none => some (.clearWork j)
  | some l => some (.lookup j l)

def nextLabel (j : Fin u) : Label u :=
  if h : j.val + 1 < u then .copyOut ⟨j.val + 1, h⟩ else .done

def labelAt (r : Nat) : Label u :=
  if h : r < u then .copyOut ⟨r, h⟩ else .done

theorem nextLabel_eq (j : Fin u) : nextLabel j = labelAt (j.val + 1) := rfl

def polaritySlot (s : Fin 3) : Fin 6 := ⟨2 * s.val + 1, by omega⟩

end UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceContextClear
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceContextClear

open Turing Complexity

variable {u : Nat} {Extra : Type}

variable [DecidableEq Extra]

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.Hastad.SourceContextClear

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceHonestLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual global addresses use three input-dependent base registers.
Every local query contributes only a fixed finite selector and fixed offset,
so a finite control table can select a base and emit its unary offset. -/

/-! Actual fixed-coefficient affine address construction. A finite literal phase
loads the coefficient, the checked width-two Horner machine reads coefficient
and preserved offset with the rank as its radix, then the literal field is
actually consumed. All operands and work stacks are restored. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceBasePhase

open Turing Complexity

def digits (coefficient offset : Nat) (i : Nat) : Nat :=
  if i = 0 then coefficient else offset

end UniqueGamesTheorem.Foundations.Hastad.SourceBasePhase

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceDescriptorEmissionLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Emit one fixed descriptor equation from three preserved unary base registers.
The output order is first address, second address, third address, RHS. The actual
stack program emits those fields in reverse order. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceEquationEmit

open Turing Complexity
open UniqueGamesTheorem.Reduction.CloneGap

inductive Label
  | seed | thirdDrain | thirdFork | thirdEmit
  | secondDrain | secondFork | secondEmit | firstDrain | firstFork | firstEmit
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.seed, .thirdDrain, .thirdFork, .thirdEmit,
  .secondDrain, .secondFork, .secondEmit, .firstDrain, .firstFork, .firstEmit]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (σ : Type) := σ × Option Bool

end UniqueGamesTheorem.Foundations.Hastad.SourceEquationEmit

namespace UniqueGamesTheorem.Foundations.Hastad.SourceRankPhase

open Turing Complexity
open scoped BigOperators

def rank {width : Nat} (radix : Nat) (digits : Fin width → Nat) : Nat :=
  ∑ i : Fin width, digits i * radix ^ i.val

def reverseDigits {width : Nat} (digits : Fin width → Nat) (i : Nat) : Nat :=
  if h : i < width then digits (Fin.rev ⟨i, h⟩) else 0

@[simp] theorem reverseDigits_apply {width : Nat} (digits : Fin width → Nat) (i : Fin width) :
    reverseDigits digits i.val = digits i.rev := by
  simp [reverseDigits, i.isLt]

end UniqueGamesTheorem.Foundations.Hastad.SourceRankPhase

namespace UniqueGamesTheorem.Foundations.Hastad.SourceSignLoad

open Turing
open UniqueGamesTheorem.Foundations.Complexity

variable {u : ℕ} {K Λ τ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

end UniqueGamesTheorem.Foundations.Hastad.SourceSignLoad

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceLoopInitLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceLoopInit

open Turing UniqueGamesTheorem.Foundations.Complexity

inductive Label (u : Nat)
  | inputCopyOut | inputCopyBack | read (slot : Fin 3 × Bool) | clearWork
  | seed (j : Fin u) | digitCopyOut (j : Fin u) | digitCopyBack (j : Fin u)
  | trim (j : Fin u) | done
  deriving DecidableEq, Fintype

variable {u : Nat} {Extra : Type}

def labelAt (r : Nat) : Label u := if h : r < u then .seed ⟨r, h⟩ else .done

variable [DecidableEq Extra]

noncomputable def timePolynomial (u : Nat) : Polynomial Nat :=
  Polynomial.C (2 * u + 3) * Polynomial.X + Polynomial.C (6 * u + 7)

theorem timePolynomial_eval (u L : Nat) :
    (timePolynomial u).eval L = (2 * u + 3) * L + 6 * u + 7 := by
  simp [timePolynomial, Nat.add_assoc]

end UniqueGamesTheorem.Foundations.Hastad.SourceLoopInit

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceSignaturePrepareLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual numbered equation list has exactly the acceptance bounded by
the private Fourier decoder. Only the repeated base-game value is an input
here; list semantics and all finite sampling laws are supplied. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceTestAppend

open Turing Complexity
open SourceEquationEmit

structure Layout (K : Type) where
  sources : Fin 3 → K
  temporary : K
  scratch : K
  accumulator : K
  sourceTemporary : ∀ side, sources side ≠ temporary
  sourceScratch : ∀ side, sources side ≠ scratch
  sourceAccumulator : ∀ side, sources side ≠ accumulator
  temporaryScratch : temporary ≠ scratch
  temporaryAccumulator : temporary ≠ accumulator
  scratchAccumulator : scratch ≠ accumulator

variable {K Λ : Type} [DecidableEq K]

def resultTapes (layout : Layout K) (base : K → List Bool) (bits : List Bool) : K → List Bool :=
  Function.update base layout.accumulator (bits.reverse ++ base layout.accumulator)

end UniqueGamesTheorem.Foundations.Hastad.SourceTestAppend

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceQueryLoopLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual fixed finite traversal of all query/noise tapes. The finite
control contains one branch for each prescribed tape. The input-dependent
signature and the three address bases remain in registers throughout. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceQueryLoop

open Turing Complexity

variable {K Λ : Type} [DecidableEq K]

theorem resultTapes_append (layout : SourceTestAppend.Layout K) (base : K → List Bool)
    (first second : List Bool) :
    SourceTestAppend.resultTapes layout
      (SourceTestAppend.resultTapes layout base first) second =
      SourceTestAppend.resultTapes layout base (first ++ second) := by
  funext k
  by_cases hk : k = layout.accumulator
  · subst k
    simp [SourceTestAppend.resultTapes, List.reverse_append, List.append_assoc]
  · simp [SourceTestAppend.resultTapes, hk]

end UniqueGamesTheorem.Foundations.Hastad.SourceQueryLoop

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceHeaderCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceHeaderCounts

open Turing Complexity

noncomputable section

variable {u D : Nat} {K Λ σ : Type}

variable [DecidableEq K]

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end

end UniqueGamesTheorem.Foundations.Hastad.SourceHeaderCounts

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceTupleBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Uniform polynomial bounds for the actual tuple-body phase budgets.
The budget being bounded is the one used by the checked machine traces. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceTupleBound

open Complexity

variable {u D : Nat}

noncomputable def rankPolynomial (u : Nat) : Polynomial Nat := Polynomial.X ^ u
noncomputable def numberPolynomial (u : Nat) : Polynomial Nat :=
  Polynomial.C (SourceBounds.bitCoefficient u) * Polynomial.X ^ u

@[simp] theorem rankPolynomial_eval (u L : Nat) : (rankPolynomial u).eval L = L ^ u := by
  simp [rankPolynomial]
@[simp] theorem numberPolynomial_eval (u L : Nat) :
    (numberPolynomial u).eval L = SourceBounds.bitCoefficient u * L ^ u := by
  simp [numberPolynomial]

noncomputable def finishPolynomial (u : Nat) : Polynomial Nat :=
  Polynomial.C 1 + (numberPolynomial u + Polynomial.C 2) + Polynomial.C 2 +
    (Polynomial.C (6 * u) * (Polynomial.X + Polynomial.C 1) + Polynomial.C 1) + Polynomial.C 1

theorem finishPolynomial_eval (u L : Nat) :
    (finishPolynomial u).eval L =
      1 + (SourceBounds.bitCoefficient u * L ^ u + 2) + 2 + (6 * u * (L + 1) + 1) + 1 := by
  simp only [finishPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, numberPolynomial_eval]

end UniqueGamesTheorem.Foundations.Hastad.SourceTupleBound

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Soundness_PartnerLinearLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Soundness.RepetitionUpper

/-- An elementary Archimedean bound for rational parameters. -/
theorem exists_pos_nat_gt (x : Rat) : ∃ n : Nat, 0 < n ∧ x < (n : Rat) := by
  refine ⟨x.ceil.toNat + 1, by omega, ?_⟩
  have hceil := Rat.le_ceil (x := x)
  have hint : x.ceil ≤ (x.ceil.toNat : Int) := by omega
  have hcast := Rat.intCast_le_intCast.mpr hint
  simp only [Rat.intCast_natCast] at hcast
  rw [Rat.natCast_add, Rat.natCast_ofNat]
  grind

/-- The estimate `b^n ≤ 1 / (1+n(1-b))` without division. -/
theorem power_mul_growth_le_one (b : Rat) (hb : 0 ≤ b) (hb' : b ≤ 1)
    (n : Nat) : b ^ n * (1 + (n : Rat) * (1 - b)) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hn := Rat.natCast_nonneg (a := n)
      have hc : 0 ≤ 1 - b := by grind
      have hnc : 0 ≤ ((n : Rat) + 1) * (1 - b) :=
        Rat.mul_nonneg (by grind) hc
      have hscaled := Rat.mul_le_mul_of_nonneg_right hb' hnc
      have hstep : b * (1 + ((n : Rat) + 1) * (1 - b)) ≤
          1 + (n : Rat) * (1 - b) := by grind
      have hprod := Rat.mul_le_mul_of_nonneg_left hstep (Rat.pow_nonneg (n := n) hb)
      simp only [Rat.pow_succ, Rat.natCast_add, Rat.natCast_ofNat]
      grind

/-- Positive powers of a rational base below one eventually fall below every
positive rational threshold; this supplies the search target in (4.4). -/
theorem exists_power_lt (b threshold : Rat) (hb : 0 ≤ b) (hb' : b < 1)
    (ht : 0 < threshold) : ∃ n : Nat, 0 < n ∧ b ^ n < threshold := by
  have hc : 0 < 1 - b := by grind
  have hden : 0 < threshold * (1 - b) := Rat.mul_pos ht hc
  obtain ⟨n, hn, hlarge⟩ := exists_pos_nat_gt (1 / (threshold * (1 - b)))
  refine ⟨n, hn, ?_⟩
  have hlarge' := (Rat.div_lt_iff hden).mp hlarge
  have hn' := Rat.natCast_nonneg (a := n)
  have hg : 0 ≤ 1 + (n : Rat) * (1 - b) := by
    have h := Rat.mul_nonneg hn' (Rat.le_of_lt hc)
    grind
  have hbnd := power_mul_growth_le_one b hb (Rat.le_of_lt hb') n
  apply Rat.not_le.mp
  intro hbad
  have hmul := Rat.mul_le_mul_of_nonneg_right hbad hg
  grind

end UniqueGamesTheorem.Soundness.RepetitionUpper

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_FinalParametersLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Integration.SourceParameters

def rate (gap : ℚ) : ℚ := 1 - gap ^ 3 / 100000

theorem rate_bounds {gap : ℚ} (hgap : 0 < gap) (hgap1 : gap ≤ 1) :
    0 < rate gap ∧ rate gap < 1 := by
  have hcube : gap ^ 3 ≤ 1 := pow_le_one₀ hgap.le hgap1
  have hcubePos : 0 < gap ^ 3 := pow_pos hgap _
  constructor <;> unfold rate <;> linarith

theorem fourth_power_comparison {gap : ℚ} (hgap : 0 ≤ gap) (hgap1 : gap ≤ 1) :
    1 - (gap : ℝ) ^ 3 / 6000 ≤ (rate gap : ℝ) ^ 4 := by
  have hg : (0 : ℝ) ≤ gap := by exact_mod_cast hgap
  have hg1 : (gap : ℝ) ≤ 1 := by exact_mod_cast hgap1
  have hc : (gap : ℝ) ^ 3 ≤ 1 := pow_le_one₀ hg hg1
  have hc0 : 0 ≤ (gap : ℝ) ^ 3 := pow_nonneg hg _
  have hb := one_add_mul_le_pow (a := -(gap : ℝ) ^ 3 / 100000)
    (by linarith : (-2 : ℝ) ≤ -(gap : ℝ) ^ 3 / 100000) 4
  have hr : (rate gap : ℝ) = 1 - (gap : ℝ) ^ 3 / 100000 := by
    simp only [rate, Rat.cast_sub, Rat.cast_one, Rat.cast_div,
      Rat.cast_pow, Rat.cast_ofNat]
  rw [hr]
  calc
    _ ≤ 1 + 4 * (-(gap : ℝ) ^ 3 / 100000) := by linarith
    _ ≤ _ := by simpa only [Nat.cast_ofNat, sub_eq_add_neg, neg_div] using hb

/-- The answer alphabet product is 16, so its binary logarithm is four.
This converts the genuine repetition theorem's real exponent to a rational
base raised to the integral repetition length. -/
theorem four_bit_rate_comparison {gap : ℚ}
    (hgap : 0 < gap) (hgap1 : gap ≤ 1) (n : Nat) :
    (1 - (gap : ℝ) ^ 3 / 6000) ^ ((n : ℝ) / 4) ≤ (rate gap : ℝ) ^ n := by
  have hg : (0 : ℝ) ≤ gap := by exact_mod_cast hgap.le
  have hg1 : (gap : ℝ) ≤ 1 := by exact_mod_cast hgap1
  have hc : (gap : ℝ) ^ 3 ≤ 1 := pow_le_one₀ hg hg1
  have hr : (0 : ℝ) ≤ rate gap := by exact_mod_cast (rate_bounds hgap hgap1).1.le
  calc
    _ ≤ ((rate gap : ℝ) ^ 4) ^ ((n : ℝ) / 4) :=
      Real.rpow_le_rpow (by linarith) (fourth_power_comparison hgap.le hgap1) (by positivity)
    _ = (rate gap : ℝ) ^ ((4 : ℝ) * ((n : ℝ) / 4)) :=
      (Real.rpow_natCast_mul hr 4 ((n : ℝ) / 4)).symm
    _ = (rate gap : ℝ) ^ (n : ℝ) := by congr 1; ring
    _ = _ := Real.rpow_natCast _ _

def sourceThreshold (D : Nat) (δ : ℚ) : ℚ := 4 * (D : ℚ)⁻¹ * δ ^ 2

theorem sourceThreshold_pos {D : Nat} (hD : 0 < D) {δ : ℚ} (hδ : 0 < δ) :
    0 < sourceThreshold D δ := by
  unfold sourceThreshold
  positivity

theorem exists_repetition_length {gap δ : ℚ} (hgap : 0 < gap) (hgap1 : gap ≤ 1)
    (hδ : 0 < δ) {D : Nat} (hD : 0 < D) :
    ∃ u : Nat, 0 < u ∧ (rate gap) ^ u < sourceThreshold D δ :=
  UniqueGamesTheorem.Soundness.RepetitionUpper.exists_power_lt (rate gap) (sourceThreshold D δ)
    (rate_bounds hgap hgap1).1.le (rate_bounds hgap hgap1).2 (sourceThreshold_pos hD hδ)

/-- Exact rational search, independent of the input formula. -/
def repetitionLength (gap δ : ℚ) (hgap : 0 < gap) (hgap1 : gap ≤ 1)
    (hδ : 0 < δ) (D : Nat) (hD : 0 < D) : Nat :=
  Nat.find (exists_repetition_length hgap hgap1 hδ hD)

theorem repetitionLength_spec (gap δ : ℚ) (hgap : 0 < gap) (hgap1 : gap ≤ 1)
    (hδ : 0 < δ) (D : Nat) (hD : 0 < D) :
    0 < repetitionLength gap δ hgap hgap1 hδ D hD ∧
      rate gap ^ repetitionLength gap δ hgap hgap1 hδ D hD < sourceThreshold D δ :=
  Nat.find_spec (exists_repetition_length hgap hgap1 hδ hD)

theorem repetitionLength_real_bound (gap δ : ℚ) (hgap : 0 < gap) (hgap1 : gap ≤ 1)
    (hδ : 0 < δ) (D : Nat) (hD : 0 < D) :
    (rate gap : ℝ) ^ repetitionLength gap δ hgap hgap1 hδ D hD ≤
      4 * (D : ℝ)⁻¹ * (δ : ℝ) ^ 2 := by
  have h := (repetitionLength_spec gap δ hgap hgap1 hδ D hD).2.le
  unfold sourceThreshold at h
  have hr := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at hr
  exact hr

end UniqueGamesTheorem.Integration.SourceParameters

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceGapLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Foundations.Hastad.SourceGap

section Repetition

open UniqueGamesTheorem.Integration.SourceParameters
open UniqueGamesTheorem.Reduction

theorem third_pos {η : ℚ} (hη : 0 < η) : 0 < η / 3 := by positivity

theorem third_le_one {η : ℚ} (hη : η ≤ 1) : η / 3 ≤ 1 := by linarith

/-- The repetition count is computed once from the gap, target error, and
noise denominator, independently of the input formula. -/
def repetitionCount (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (D : ℕ) (hD : 0 < D) : ℕ :=
  repetitionLength (η / 3) ξ (third_pos hη) (third_le_one hη1) hξ D hD

end Repetition

open SourceNoiseParameter UniqueGamesTheorem.Reduction

end UniqueGamesTheorem.Foundations.Hastad.SourceGap



end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_IncidenceProbabilityLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Actual finite incidence-game probabilities for Proposition 4.3.
The referee samples an occurrence and one of three slots independently and
uniformly. Alice sees its occurrence; Bob sees only its variable name.
-/

namespace UniqueGamesTheorem.Reduction.IncidenceProbability

open scoped BigOperators

variable {Variable Index Coin Occurrence : Type*}

theorem sum_bool_indicator_eq_count_ofFn {n : Nat} (p : Fin n → Bool) :
    (∑ i, if p i then (1 : ℚ) else 0) = ((List.ofFn p).countP id : ℚ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ, List.ofFn_succ, List.countP_cons, ih]
    cases p 0 <;> simp [add_comm]

/-- Uniform Boolean-event probability is the indexed list's exact occurrence count. -/
theorem expect_bool_indicator_eq_count_ofFn {n : Nat} (p : Fin n → Bool) :
    Finset.univ.expect (fun i : Fin n => if p i then (1 : ℚ) else 0) =
      ((List.ofFn p).countP id : ℚ) / n := by
  rw [Fintype.expect_eq_sum_div_card, sum_bool_indicator_eq_count_ofFn]
  simp

end UniqueGamesTheorem.Reduction.IncidenceProbability

end

section

namespace UniqueGamesTheorem.Reduction.SourceProbability

theorem count_complement {α : Type*} (es : List α) (p : α → Bool) :
    es.countP (fun e => !p e) + es.countP p = es.length := by
  induction es with
  | nil => simp
  | cons e es ih =>
    cases hp : p e <;> simp [hp] at * <;> omega

end UniqueGamesTheorem.Reduction.SourceProbability

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Soundness_ZeroInformationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Soundness.ZeroInformation

/-! ## The observation fibre is a Cartesian product -/

/-! ## Exact weighted finite counting -/

/-! ## Position-indexed row maps -/

/-! ## Complete private-input reconstruction -/

/-- A total fixed decoder for a retained index. On supported (o,n) it is uniquely
determined by the distinctness of the three names. -/
noncomputable def decodeIndex {O N : Type} (name : O → Fin 3 → N)
    (occurrence : O) (n : N) : Fin 3 := by
  classical
  exact if h : ∃ i, name occurrence i = n then Classical.choose h else 0

def reconstructQuestion {P X : Type} (hidden : P → Bool) (inside outside : P → X) : P → X :=
  fun j => if hidden j then inside j else outside j

end UniqueGamesTheorem.Soundness.ZeroInformation

open scoped BigOperators

namespace UniqueGamesTheorem.Soundness.ConditionalIncidences

noncomputable section

def incidence {O N : Type} (name : O → Fin 3 → N) (draw : O × Fin 3) : O × N :=
  (draw.1, name draw.1 draw.2)

end

end UniqueGamesTheorem.Soundness.ConditionalIncidences

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Soundness_ConditionalReindex
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Explicit hidden-coordinate enumeration in the actual conditional law. -/

namespace UniqueGamesTheorem.Soundness.ConditionalIncidences
open scoped BigOperators

def coordinateReindex {A B X : Type} (e : B ≃ A) : (A → X) ≃ (B → X) where
  toFun f := fun b => f (e b)
  invFun g := fun a => g (e.symm a)
  left_inv f := by
    funext a
    exact congrArg f (e.apply_symm_apply a)
  right_inv g := by
    funext b
    exact congrArg g (e.symm_apply_apply b)

end UniqueGamesTheorem.Soundness.ConditionalIncidences

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Soundness_SubsetIntersectionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Full slot indices and the actual partner law

Uniform indices at all positions restrict to uniform indices on an active set.
The explicit restriction/complement equivalence proves this sampling fact. The
dependent partner average then equals sampling the active set followed by all
slot indices, including unused indices outside the active set. Finally, the
coordinatewise occurrence/slot draw is related to that same law.
-/

namespace UniqueGamesTheorem.Soundness.PartnerFullSampling

open scoped BigOperators

noncomputable section

def restrictIndices {P X : Type*} (J : Finset P) (indices : P → X) : ↥J → X :=
  fun j => indices j.val

/-- The values inside and outside a finite set reconstruct the full tuple. -/
def restrictionProductEquiv {P X : Type*} [DecidableEq P] (J : Finset P) :
    (P → X) ≃ ((↥J → X) × ({j : P // j ∉ J} → X)) where
  toFun indices := (restrictIndices J indices, fun j => indices j.val)
  invFun parts := fun j =>
    if hj : j ∈ J then parts.1 ⟨j, hj⟩ else parts.2 ⟨j, hj⟩
  left_inv indices := by
    funext j
    by_cases hj : j ∈ J <;> simp [restrictIndices, hj]
  right_inv parts := by
    apply Prod.ext
    · funext j
      simp [restrictIndices, j.property]
    · funext j
      simp [j.property]

end

end UniqueGamesTheorem.Soundness.PartnerFullSampling

end

end OAI
end


