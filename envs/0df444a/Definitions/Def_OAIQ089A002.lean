-- Prove2me | Definitions.Def_OAIQ089A002
-- name    : OAIQ089A002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T02:51:15.901481+00:00
-- url     : https://prove2.me/theorems/12848644-97c2-41bf-8273-495c2b7e9a20
-- title:
--   Definitions bundle OAIQ089A002 of the split of OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 695 declarations of OpenAI's Lean: 417 definitions, 12 inductive types or structures, 14 instances and 252 theorems. The definitions and types are `OAI.ContingencyTables.CountingAmplifiedProgram.budgetPolynomial`, `OAI.ContingencyTables.CountingBaseProgram.cellBits`, `OAI.ContingencyTables.CountingBranchProgram.Accurate`, `OAI.ContingencyTables.CountingCoefficientBounds.coefficientPolynomial`, `OAI.ContingencyTables.CountingInputParser.cells`, `OAI.ContingencyTables.CountingInputParser.offset`, `OAI.ContingencyTables.CountingInputParser.parameters`, `OAI.ContingencyTables.CountingInputParser.rest`, `OAI.ContingencyTables.CountingMarkerBounds.paddingPolynomial`, `OAI.ContingencyTables.CountingOracleWordBounds.binBound`, `OAI.ContingencyTables.CountingOracleWordBounds.binPolynomial`, `OAI.ContingencyTables.CountingOracleWordBounds.estimatorBound`, `OAI.ContingencyTables.CountingOracleWordBounds.estimatorPolynomial`, `OAI.ContingencyTables.CountingOracleWordBounds.innerPolynomial`, `OAI.ContingencyTables.CountingOracleWordBounds.medianPolynomial`, `OAI.ContingencyTables.CountingOracleWordBounds.sampleBound`, `OAI.ContingencyTables.CountingOracleWordBounds.samplePolynomial`, `OAI.ContingencyTables.CountingOracleWordBounds.timeBound`, `OAI.ContingencyTables.CountingOracleWordBounds.timePolynomial`, `OAI.ContingencyTables.CountingPhaseSchedule.returnCap`, `OAI.ContingencyTables.CountingPhaseSchedule.tolerance`, `OAI.ContingencyTables.CountingPositiveWordBound.widthPolynomial`, `OAI.ContingencyTables.CountingPublicInputBounds.size`, `OAI.ContingencyTables.CountingPublicTerminalBounds.basicPolynomial`, `OAI.ContingencyTables.CountingTerminalBounds.coefficientPolynomial`, `OAI.ContingencyTables.CountingTerminalBounds.cutoffPolynomial`, `OAI.ContingencyTables.CountingTerminalBounds.gridPolynomial`, `OAI.ContingencyTables.CountingTerminalBounds.phasePolynomial`, `OAI.ContingencyTables.CountingWordsBound.initialPolynomial`, `OAI.ContingencyTables.CountingWordsBound.phasePolynomial`, `OAI.ContingencyTables.CountingWordsBound.stagePolynomial`, `OAI.ContingencyTables.CountingWordsBound.stepPolynomial`, `OAI.ContingencyTables.CountingWordsBound.wordPolynomial`, `OAI.ContingencyTables.DegreeCompletion.completeDegree`, `OAI.ContingencyTables.DenseAffine.cellScale`, `OAI.ContingencyTables.DenseAffine.denseWidth`, `OAI.ContingencyTables.DenseAffine.entryCoeff`, `OAI.ContingencyTables.DenseAffine.entryOffset`, `OAI.ContingencyTables.DenseAffine.normalizedCoeff`, `OAI.ContingencyTables.DenseAffine.normalizedOffset` and 389 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `ContingencyTables_Counting_CountingAmplifiedLaw`, `ContingencyTables_Counting_CountingBaseProgram`, `ContingencyTables_Counting_CountingBranchSuccess`, `ContingencyTables_Counting_CountingCoefficientBounds`, `ContingencyTables_Counting_CountingInputParser`, `ContingencyTables_Counting_CountingMarkerBounds`, `ContingencyTables_Counting_CountingOracleWordBounds`, `ContingencyTables_Counting_CountingPhaseSchedule`, `ContingencyTables_Counting_CountingPositiveWordBound`, `ContingencyTables_Counting_CountingPublicInputBounds`, `ContingencyTables_Counting_CountingPublicTerminalBounds`, `ContingencyTables_Counting_CountingTerminalBounds`, `ContingencyTables_Counting_CountingWordsBound`, `ContingencyTables_Counting_EstimatorWordBanks`, `ContingencyTables_Counting_InitializationBrackets`, `ContingencyTables_Dense_DenseAffine`, `ContingencyTables_Dense_DenseAxisBits`, `ContingencyTables_Dense_DenseBooleanTrial`, `ContingencyTables_Dense_DenseBoundedTrial`, `ContingencyTables_Dense_DenseCoefficients`, `ContingencyTables_Dense_DenseCompletionProgram`, `ContingencyTables_Dense_DenseCutParameters`, `ContingencyTables_Dense_DenseEnumeratedMatrix`, `ContingencyTables_Dense_DenseErrorArithmetic`, `ContingencyTables_Dense_DenseExponentArithmetic`, `ContingencyTables_Dense_DenseGeometry`, `ContingencyTables_Dense_DenseLayerArithmetic`, `ContingencyTables_Dense_DenseLocalGeometry`, `ContingencyTables_Dense_DenseMatrixProgram`, `ContingencyTables_Dense_DenseMatrixWalk`, `ContingencyTables_Dense_DenseMixing`, `ContingencyTables_Dense_DenseNormalizeSemantics`, `ContingencyTables_Dense_DenseOffsets`, `ContingencyTables_Dense_DenseRationalKernel`, `ContingencyTables_Dense_DenseRegionVolume`, `ContingencyTables_Dense_DenseRegularity`, `ContingencyTables_Dense_DenseReindexedVolume`, `ContingencyTables_Dense_DenseScales`, `ContingencyTables_Dense_DensityLayers`, `ContingencyTables_Dense_GridBoundary`, `ContingencyTables_Dense_GridCover`, `ContingencyTables_Dense_GridIndexProgram`, `ContingencyTables_Dense_GridMass`, `ContingencyTables_Dense_GridMeasure`, `ContingencyTables_Machines_CompletionEnumerationProgram`, `ContingencyTables_Machines_DependentWordProgram`, `ContingencyTables_Machines_FiniteEncodedHistory`, `ContingencyTables_Machines_FiniteWordExecution`, `ContingencyTables_Machines_FiniteWordRejection`, `ContingencyTables_Machines_FiniteWordSlices`, `ContingencyTables_Machines_FiniteWordWalk`, `ContingencyTables_Machines_FirstSuccessProgram`, `ContingencyTables_Machines_FixedCardinalityLaw`, `ContingencyTables_Machines_InitialLocalChoices`, `ContingencyTables_Machines_IntegerMatrixProgram`, `ContingencyTables_Machines_LiteralProgram`, `ContingencyTables_Machines_NatListEquality`, `ContingencyTables_Machines_OffsetCountProgram`, `ContingencyTables_Machines_OnlineIntegerRetry`, `ContingencyTables_Machines_PairedCatalogProgram`, `ContingencyTables_Machines_PairedProfileProgram`, `ContingencyTables_Machines_PreparedOffsetCount`, `ContingencyTables_Machines_RepeatedFractionProgram`, `ContingencyTables_Machines_ResidualWeightProgram`, `ContingencyTables_Machines_RetryNumeratorProgram`, `ContingencyTables_Machines_ScheduledCountSemantics`, `ContingencyTables_Machines_TranslationDecisionProgram`, `ContingencyTables_Machines_VectorRetryProgram`, `ContingencyTables_Model`, `ContingencyTables_Parameters`, `ContingencyTables_Rooted_ForestCapacity`, `ContingencyTables_Rooted_ForestCut`, `ContingencyTables_Rooted_ForestPenaltyApplication`, `ContingencyTables_Rooted_ForestRootPenalty`, `ContingencyTables_Rooted_LargeMarginReference`, `ContingencyTables_Rooted_LargePairEnumeration`, `ContingencyTables_Rooted_RootedEstimatorWordSemantics`, `ContingencyTables_Rooted_TreeMarginalSignature`, `ContingencyTables_Sampling_AllSamplingProgram`, `ContingencyTables_Sampling_ExactCoreProgram`, `ContingencyTables_Sampling_ExactIntegerChoice`, `ContingencyTables_Sampling_ExactIntegerOnline`, `ContingencyTables_Sampling_ExactIntegerProgram`, `ContingencyTables_Sampling_ExactIntegerRetry`, `ContingencyTables_Sampling_FirstPaperCodeProposal`, `ContingencyTables_Sampling_FirstPaperCompletionLaws`, `ContingencyTables_Sampling_FirstPaperExposureVariance`, `ContingencyTables_Sampling_FirstPaperOuterBudget`, `ContingencyTables_Sampling_FirstPaperPreparedProposal`, `ContingencyTables_Sampling_FirstPaperProposal`, `ContingencyTables_Sampling_FirstPaperSmallKernel`, `ContingencyTables_Sampling_FirstPaperWordBudget`, `ContingencyTables_Sampling_GreedyFeasibleTable`, `ContingencyTables_Sampling_GreedyPublicProgram`, `ContingencyTables_Sampling_OriginalTableBox`, `ContingencyTables_Sampling_OriginalTableEnumeration`, `ContingencyTables_Sampling_Padding`, `ContingencyTables_Sampling_PhysicalEventBounds`, `ContingencyTables_Sampling_PhysicalExchangeMargins`, `ContingencyTables_Sampling_PhysicalPublicLaw`, `ContingencyTables_Sampling_PhysicalRetryTail`, `ContingencyTables_Sampling_ProfileCodeEquality`, `ContingencyTables_Sampling_ProfilePublicProgram`, `ContingencyTables_Sampling_ProfileSamplingProgram`, `ContingencyTables_Sampling_ProfileScheduleProgram`, `ContingencyTables_Sampling_ProfileVectorMeasureBounds`, `ContingencyTables_Sampling_ProfileWordProgram`, `ContingencyTables_Sampling_RepairPrefixes`, `ContingencyTables_Sampling_RepairResiduals`, `ContingencyTables_Sampling_ResidualMixture`, `ContingencyTables_Sampling_SmallCellCatalogProgram`, `ContingencyTables_Sampling_SmallChainBudget`, `ContingencyTables_Sampling_SmallContextCoordinates`, `ContingencyTables_Sampling_SmallContextFibres`, `ContingencyTables_Sampling_SmallProfileCode`, `ContingencyTables_Sampling_SmallProposal`, `ContingencyTables_Transport_AuxiliaryRepairMass`, `ContingencyTables_Transport_AxisProposalTest`, `ContingencyTables_Transport_BalancedSummation`, `ContingencyTables_Transport_BooleanEnumeration`, `ContingencyTables_Transport_BooleanIntegerLaw`, `ContingencyTables_Transport_BoundedProfileWalk`, `ContingencyTables_Transport_BoxGeometry`, `ContingencyTables_Transport_ContextAdjacentTransport`, `ContingencyTables_Transport_DegreeCompletion`, `ContingencyTables_Transport_DyadicAcceptance`, `ContingencyTables_Transport_EqualitySoftening`, `ContingencyTables_Transport_ExcessContextProfiles`, `ContingencyTables_Transport_FactorialSignatures`, `ContingencyTables_Transport_FiniteAcceptCounts`, `ContingencyTables_Transport_FiniteChoiceFibres`, `ContingencyTables_Transport_FiniteDependentLaw`, `ContingencyTables_Transport_FiniteExchangeDegree`, `ContingencyTables_Transport_FiniteExchangeObservables`, `ContingencyTables_Transport_FiniteExposureVariance`, `ContingencyTables_Transport_FiniteGraphPoincareBudget`, `ContingencyTables_Transport_FiniteGridWords`, `ContingencyTables_Transport_FiniteIndependentAverages`, `ContingencyTables_Transport_FiniteMetropolis`, `ContingencyTables_Transport_FiniteMetropolisTransport`, `ContingencyTables_Transport_FinitePartitionVariance`, `ContingencyTables_Transport_FinitePrefixVariance`, `ContingencyTables_Transport_FiniteRepairDegree`, `ContingencyTables_Transport_FiniteRepairVariance`, `ContingencyTables_Transport_FiniteSupportEnergy`, `ContingencyTables_Transport_FiniteSupportVariance`, `ContingencyTables_Transport_FiniteSymmetricEnergy`, `ContingencyTables_Transport_FiniteUniformHistory`, `ContingencyTables_Transport_FirstSuccess`, `ContingencyTables_Transport_IndexedTableLaw`, `ContingencyTables_Transport_InitialTransversals`, `ContingencyTables_Transport_IntegerChildLogConcavity`, `ContingencyTables_Transport_IntegerChildVariance`, `ContingencyTables_Transport_IntegerEquivLaw`, `ContingencyTables_Transport_IntegerFutureKernel`, `ContingencyTables_Transport_IntegerFutureSquare`, `ContingencyTables_Transport_IntegerLaw`, `ContingencyTables_Transport_IntegerLeafEnergy`, `ContingencyTables_Transport_IntegerLeafTransport`, `ContingencyTables_Transport_IntegerMatrixPoint`, `ContingencyTables_Transport_IntegerReflection`, `ContingencyTables_Transport_IntegerResidualCorrection`, `ContingencyTables_Transport_IntegerRootEstimate`, `ContingencyTables_Transport_IntegerTransportCoefficient`, `ContingencyTables_Transport_LaminarSignature`, `ContingencyTables_Transport_LineUnarySignature`, `ContingencyTables_Transport_ListBitProposal`, `ContingencyTables_Transport_MetropolisChain`, `ContingencyTables_Transport_NestedPenaltyApplication`, `ContingencyTables_Transport_NestedProductSignature`, `ContingencyTables_Transport_ObservableBounds`, `ContingencyTables_Transport_PositiveSequenceMinimum`, `ContingencyTables_Transport_ProductIntegerSignature`, `ContingencyTables_Transport_RealCompletion`, `ContingencyTables_Transport_RealKernelApproximation`, `ContingencyTables_Transport_RejectionLaw`, `ContingencyTables_Transport_RowMajorEnumeration`, `ContingencyTables_Transport_ScalarPenalty`, `ContingencyTables_Transport_SignedTransport`, `ContingencyTables_Transport_TableMarginTransport`, `ContingencyTables_Transport_TableTightening`, `ContingencyTables_Transport_TransversalCount`, `ContingencyTables_Transport_TwoLiftStates`, `ContingencyTables_Transport_UnaryMarkers`, `ContingencyTables_Transport_UniformPartialRejection`, `MatchingCount_Arithmetic_ArithmeticSize`, `MatchingCount_Complexity_AlphabetCompilerCost`, `MatchingCount_Complexity_GuardMachineBase`, `MatchingCount_Complexity_StackCompilerCost`, `MatchingCount_Graphs_AdaptiveStream`, `MatchingCount_Graphs_Cumulative`, `MatchingCount_Graphs_ExperimentSupport`, `MatchingCount_Machines_BoolPostCompiler`, `MatchingCount_Machines_CoinTM1`, `MatchingCount_Machines_CoinTM1Finite`, `MatchingCount_Machines_OnlineFold`, `MatchingCount_Machines_OnlineFrame`, `MatchingCount_Machines_PhysicalPost`, `MatchingCount_Machines_PhysicalProcess`, `MatchingCount_Machines_PhysicalProgram`, `MatchingCount_Machines_PhysicalRestriction`, `MatchingCount_Machines_PhysicalSequential`, `MatchingCount_Machines_SupportedCompiler`, `MatchingCount_Machines_TreeCanonical`, `MatchingCount_Machines_TreeListMore`, `MatchingCount_Sampling_ChosenChord`, `MatchingCount_Sampling_Component`, `MatchingCount_Sampling_Sym2Order`, `MatchingCount_Tapes_BlockMap`, `MatchingCount_Tapes_Codec`, `MatchingCount_Tapes_CoinAlphabet`, `MatchingCount_Tapes_CoinStack`, `MatchingCount_Tapes_CoinSupport`, `MatchingCount_Tapes_FixedAlphabetCompiler`, `MatchingCount_Tapes_FixedEncoding`, `MatchingCount_Tapes_Online`, `MatchingCount_Tapes_OnlineStackCompiler`, `MatchingCount_Tapes_OnlineWord`, `MatchingCount_Tapes_Packed`, `MatchingCount_Tapes_PackedExecution`, `MatchingCount_Tapes_Physical`, `MatchingCount_Tapes_PhysicalAlphabet`, `MatchingCount_Tapes_StackWords`, `MatchingCount_Tapes_TapeTools`.
--
--   **Imports.** It imports the published bundle `Def_ContingencyTables`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ089A004` and `OAIQ089A005`.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_ContingencyTables

section
-- module Solutions.OAIQ089_CT.Compat
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
-- module Solutions.OAIQ089_CT.ContingencyTables_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Contingency tables with arbitrary margins

The feasible sets in result 200 are represented by natural-valued
matrices, without a positivity, balance, or sparsity restriction on
the margins. The finite encoding bound is proved rather than assumed.
-/

namespace ContingencyTables

open Finset

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The bound used in the exact correction's exhaustive branch. -/
theorem table_card_le (r : I → ℕ) (c : J → ℕ) :
    Fintype.card (Table r c) ≤ ((∑ i, r i) + 1) ^ (Fintype.card I * Fintype.card J) := by
  classical
  let encode : Table r c → I → J → Fin ((∑ i, r i) + 1) :=
    fun X i j => ⟨X.val i j, Nat.lt_succ_of_le (entry_le_total X.property i j)⟩
  have hinj : Function.Injective encode := by
    intro X Y h
    apply Subtype.ext
    funext i j
    exact congrArg Fin.val (congrFun (congrFun h i) j)
  have h := Fintype.card_le_of_injective encode hinj
  simpa only [Fintype.card_fun, Fintype.card_fin, ← pow_mul, Nat.mul_comm] using h

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BalancedSummation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Balanced-pair summation of two-removal forms

This is the finite unweighted closure step in paper 200-01,
Lemma `lem:pair-summation` (`D'=B`), and paper 200-02,
Lemma `lem:integer-signature`. The hypotheses describe the actual old/fresh
blocks and their adjacent cross entries. Cumulative coefficients are
constructed from those cross entries; no transport or closure conclusion is
assumed. In particular the zero-diagonal capacity-two case is included.
-/

namespace ContingencyTables

open scoped BigOperators
open LinearMap (BilinForm)

/-- First moment of the discrete second difference, with exact boundaries. -/
theorem sum_firstMoment_second_differences (a : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (j : ℝ) * (2 * a j - a (j - 1) - a (j + 1))) =
      ((n : ℝ) + 1) * a n - a 0 - (n : ℝ) * a (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring

/-- Second moment of the same difference. -/
theorem sum_secondMoment_second_differences (a : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (j : ℝ) ^ 2 * (2 * a j - a (j - 1) - a (j + 1))) =
      ((n : ℝ) + 1) ^ 2 * a n - (n : ℝ) ^ 2 * a (n + 1) + a 0 -
        2 * ∑ j ∈ Finset.range (n + 1), a j := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    have hs : (∑ j ∈ Finset.range (n + 1 + 1), a j) =
        (∑ j ∈ Finset.range (n + 1), a j) + a (n + 1) := Finset.sum_range_succ _ _
    rw [Finset.sum_range_succ, ih, hs]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring

/-- The exact weighted telescope in equation pair-weighted. The boundary
terms are scalar values, so invalid endpoint matrices are never needed. -/
theorem sum_weighted_second_differences (a : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (j : ℝ) * ((n : ℝ) - j) *
      (2 * a j - a (j - 1) - a (j + 1))) =
      2 * (∑ j ∈ Finset.range (n + 1), a j) - ((n : ℝ) + 1) * (a 0 + a n) := by
  calc
    _ = (n : ℝ) * (∑ j ∈ Finset.range (n + 1), (j : ℝ) *
          (2 * a j - a (j - 1) - a (j + 1))) -
        ∑ j ∈ Finset.range (n + 1), (j : ℝ) ^ 2 *
          (2 * a j - a (j - 1) - a (j + 1)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [sum_firstMoment_second_differences, sum_secondMoment_second_differences]
      ring

/-- Summation of the local inequalities with the actual nonnegative
weights. Only interior inequalities are required. -/
theorem weighted_second_differences_bound (a v : ℕ → ℝ) (n : ℕ)
    (ha0 : a 0 = 0) (han : a n = 0)
    (hlocal : ∀ j, 0 < j → j < n →
      2 * a j - a (j - 1) - a (j + 1) ≤ -v j) :
    2 * (∑ j ∈ Finset.range (n + 1), a j) ≤
      -(∑ j ∈ Finset.range (n + 1), (j : ℝ) * ((n : ℝ) - j) * v j) := by
  have hsum : (∑ j ∈ Finset.range (n + 1), (j : ℝ) * ((n : ℝ) - j) *
      (2 * a j - a (j - 1) - a (j + 1))) ≤
      ∑ j ∈ Finset.range (n + 1), (j : ℝ) * ((n : ℝ) - j) * (-v j) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
    by_cases hj0 : j = 0
    · subst j
      simp
    by_cases hjeq : j = n
    · subst j
      simp
    have hjr : (j : ℝ) ≤ n := by exact_mod_cast hjn
    apply mul_le_mul_of_nonneg_left (hlocal j (by omega) (by omega))
    exact mul_nonneg (Nat.cast_nonneg j) (sub_nonneg.mpr hjr)
  rw [sum_weighted_second_differences, ha0, han] at hsum
  simp only [add_zero, mul_zero, sub_zero, mul_neg, Finset.sum_neg_distrib] at hsum
  exact hsum

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FactorialSignatures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Factorial congruence for the two binary lifts

The integer-to-binary signature transfer in paper 200-02,
Lemma `lem:binary-signatures`. Coordinates with zero remaining copies
are allowed; a single remaining copy gives an invalid repeated removal.
The copy matrix is proved to be dominated by the integer form compressed
to group means. The difference is the nonnegative within-group variance.
-/

namespace ContingencyTables.FactorialSignatures

open scoped BigOperators Classical Matrix
open LinearMap (BilinForm)

variable {G : Type*} [Fintype G] [DecidableEq G]

abbrev Copies (n : G → ℕ) := (u : G) × Fin (n u)

noncomputable def groupAverage (n : G → ℕ) : (Copies n → ℝ) →ₗ[ℝ] (G → ℝ) where
  toFun x u := (∑ i : Fin (n u), x ⟨u, i⟩) / n u
  map_add' x y := by ext u; simp [Finset.sum_add_distrib, add_div]
  map_smul' a x := by
    ext u
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_div_assoc, RingHom.id_apply]

def groupIndicator (n : G → ℕ) (u : G) (i : Copies n) : ℝ := if i.1 = u then 1 else 0

def groupOuter (n : G → ℕ) (u : G) : Matrix (Copies n) (Copies n) ℝ :=
  fun i j => groupIndicator n u i * groupIndicator n u j

noncomputable def withinCoefficient (n : G → ℕ) (H : Matrix G G ℝ) (c : ℝ) (u : G) : ℝ :=
  c * H u u / ((n u : ℝ) * (n u - 1 : ℕ))

noncomputable def normalizedMatrix (n : G → ℕ) (H : Matrix G G ℝ) (c : ℝ) :
    Matrix (Copies n) (Copies n) ℝ :=
  fun i j => c * H i.1 j.1 / ((n i.1 : ℝ) * n j.1)

noncomputable def scaledPullback (n : G → ℕ) (H : Matrix G G ℝ) :
    Matrix (Copies n) (Copies n) ℝ :=
  fun i j => (1 / (n i.1 : ℝ)) * H i.1 j.1 * (1 / (n j.1 : ℝ))

/-- Exact normalized copy matrix, including the within-group diagonal correction. -/
noncomputable def copyMatrix (n : G → ℕ) (H : Matrix G G ℝ) (c : ℝ) :
    Matrix (Copies n) (Copies n) ℝ :=
  normalizedMatrix n H c +
    ∑ u, (withinCoefficient n H c u / n u) • groupOuter n u -
      Matrix.diagonal (fun i : Copies n => withinCoefficient n H c i.1)

lemma grouped_form (n : G → ℕ) (H : Matrix G G ℝ) (x y : Copies n → ℝ) :
    (H.submatrix Sigma.fst Sigma.fst).toBilin' x y =
      H.toBilin' (fun u => ∑ i : Fin (n u), x ⟨u, i⟩)
        (fun u => ∑ i : Fin (n u), y ⟨u, i⟩) := by
  simp only [Matrix.toBilin'_apply, Matrix.submatrix_apply, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, ← Finset.sum_mul]

lemma groupOuter_form (n : G → ℕ) (u : G) (x y : Copies n → ℝ) :
    (groupOuter n u).toBilin' x y =
      (∑ i : Fin (n u), x ⟨u, i⟩) * ∑ i : Fin (n u), y ⟨u, i⟩ := by
  simp only [Matrix.toBilin'_apply, groupOuter, groupIndicator, Fintype.sum_sigma]
  simp [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma normalized_form (n : G → ℕ) (H : Matrix G G ℝ) (c : ℝ) (x y : Copies n → ℝ) :
    (normalizedMatrix n H c).toBilin' x y =
      c * H.toBilin' (groupAverage n x) (groupAverage n y) := by
  have heq : normalizedMatrix n H c = c • scaledPullback n H := by
    ext i j
    simp only [normalizedMatrix, scaledPullback, Matrix.smul_apply, smul_eq_mul,
      div_mul_eq_div_div]
    ring
  rw [heq]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  congr 1
  have hg := grouped_form n H (fun i => x i / n i.1) (fun i => y i / n i.1)
  convert hg using 1
  · rw [Matrix.toBilin'_apply, Matrix.toBilin'_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [Matrix.submatrix_apply, scaledPullback]
    ring
  · congr 1 <;> ext u <;> simp [groupAverage, Finset.sum_div]

lemma diagonal_form (n : G → ℕ) (d x : Copies n → ℝ) :
    (Matrix.diagonal d).toBilin' x x = ∑ i, d i * x i * x i := by
  rw [Matrix.toBilin'_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  ring

/-- The factorial copy form equals the integer form on group averages
minus the sum of within-group variances with their actual coefficients. -/
theorem copyMatrix_form (n : G → ℕ) (H : Matrix G G ℝ) (c : ℝ) (x : Copies n → ℝ) :
    (copyMatrix n H c).toBilin' x x =
      c * H.toBilin' (groupAverage n x) (groupAverage n x) -
        ∑ u, withinCoefficient n H c u *
          ((∑ i : Fin (n u), x ⟨u, i⟩ ^ 2) -
            (∑ i : Fin (n u), x ⟨u, i⟩) ^ 2 / n u) := by
  simp only [copyMatrix, map_sub, map_add, map_sum, map_smul,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, normalized_form, groupOuter_form,
    diagonal_form]
  simp only [Fintype.sum_sigma]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  have halg (a b d r : ℝ) : a * (b - d ^ 2 / r) = a * b - a / r * (d * d) := by ring
  simp_rw [halg, Finset.sum_sub_distrib, pow_two]
  ring

omit [Fintype G] [DecidableEq G] in
lemma within_variance_nonnegative (n : ℕ) (x : Fin n → ℝ) :
    0 ≤ (∑ i, x i ^ 2) - (∑ i, x i) ^ 2 / n := by
  by_cases hn : n = 0
  · subst n
    simp
  have hnr : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin n => (1 : ℝ)) x
  have hh : (∑ i, x i) ^ 2 ≤ (n : ℝ) * ∑ i, x i ^ 2 := by simpa using hcs
  exact sub_nonneg.mpr ((div_le_iff₀ hnr).mpr (by nlinarith [hh]))

omit [Fintype G] [DecidableEq G] in
lemma normalization_identity (n : ℕ) (a : ℝ) (hsmall : n < 2 → a = 0) :
    a / ((n : ℝ) * n) + (a / ((n : ℝ) * (n - 1 : ℕ))) / n =
      a / ((n : ℝ) * (n - 1 : ℕ)) := by
  by_cases hn : 2 ≤ n
  · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hn1 : (n : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    rw [hcast]
    field_simp
    ring
  · rw [hsmall (by omega)]
    simp

/-- The normalization has exactly the zero diagonal and the factorial
removal denominator, including single-copy and empty groups. -/
theorem copyMatrix_apply (n : G → ℕ) (H : Matrix G G ℝ) (c : ℝ)
    (hzero : ∀ u, n u < 2 → H u u = 0) (i j : Copies n) :
    copyMatrix n H c i j = if i = j then 0 else
      c * H i.1 j.1 / ((n i.1 : ℝ) *
        (if i.1 = j.1 then ((n i.1 - 1 : ℕ) : ℝ) else n j.1)) := by
  simp only [copyMatrix, normalizedMatrix, Matrix.sub_apply, Matrix.add_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, groupOuter, groupIndicator, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single i.1]
  · by_cases hg : i.1 = j.1
    · have hn := normalization_identity (n i.1) (c * H i.1 i.1)
        (fun h => by rw [hzero i.1 h, mul_zero])
      simp only [hg, ite_true, if_true, mul_one, withinCoefficient] at *
      rw [hn]
      by_cases hij : i = j <;> simp [hij]
    · have hij : i ≠ j := fun h => hg (congrArg Sigma.fst h)
      simp [hg, Ne.symm hg, hij]
  · intro u _ hu
    simp [Ne.symm hu]
  · simp


omit [Fintype G] in
/-- Distinct labeled copies give valid one-per-coordinate or repeated-coordinate removals. -/
lemma distinct_copy_counts (n : G → ℕ) (i j : Copies n) (hij : i ≠ j) :
    0 < n i.1 ∧ 0 < n j.1 - if j.1 = i.1 then 1 else 0 := by
  rcases i with ⟨u, a⟩
  rcases j with ⟨v, b⟩
  have hu : 0 < n u := lt_of_le_of_lt (Nat.zero_le _) a.isLt
  have hv : 0 < n v := lt_of_le_of_lt (Nat.zero_le _) b.isLt
  refine ⟨hu, ?_⟩
  by_cases huv : u = v
  · subst v
    have hab : a ≠ b := fun h => hij (congrArg (Sigma.mk u) h)
    have hn : 2 ≤ n u := by
      by_contra hn
      have ha : a.val = 0 := by omega
      have hb : b.val = 0 := by omega
      exact hab (Fin.ext (ha.trans hb.symm))
    simp only [ite_true, if_true]
    omega
  · simp [Ne.symm huv, hv]

def addTwo (r : G → ℕ) (u v : G) : G → ℕ :=
  fun w => r w + (if w = u then 1 else 0) + (if w = v then 1 else 0)


noncomputable def cellFactor (b x y : ℕ) : ℝ :=
  (x.factorial : ℝ) * y.factorial / b.factorial

noncomputable def complementCellFactor (b x y : ℕ) : ℝ :=
  ((b - x).factorial : ℝ) * (b - y).factorial / b.factorial

end ContingencyTables.FactorialSignatures

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerReflection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual box reflection and integer addition signatures

Reflection of every coordinate converts a valid two-addition entry into a
two-removal entry. A balanced summed pair is reflected by reversing its
finite index, so the same marginal closure applies to additions.
-/

namespace ContingencyTables.IntegerReflection

open scoped BigOperators Classical Matrix
open FactorialSignatures

variable {I : Type*} [Fintype I] [DecidableEq I]

def reflect (N z : I → ℕ) : I → ℕ := fun i => N i-z i

end ContingencyTables.IntegerReflection

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_LaminarSignature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The two-level laminar kernel in contingency-table weights

The factor groups in the sampling paper's laminar-signature lemma are line
coordinate sets, with one nested small-slot subset in each line. Row and
column coordinates belong to separate lines. The normalized kernel
decomposition gives the quadratic one-positive-direction property.
-/

namespace ContingencyTables

open scoped BigOperators
open LinearMap (BilinForm)

section TwoLevel

variable {I G : Type*} [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G]

/-- The normalized two-removal kernel: line factors and the nested small
coordinate factor are the only factors shared by two distinct indices. -/
def twoLevelKernel (line : I → G) (inner : I → Bool) (γ δ : G → ℝ) :
    Matrix I I ℝ := fun i j =>
  if line i = line j then
    γ (line i) * (if inner i = true ∧ inner j = true then δ (line i) else 1)
  else 1

/-- Indicator of one line-coordinate group. -/
def lineVector (line : I → G) (g : G) (i : I) : ℝ :=
  if line i = g then 1 else 0

/-- Indicator of the small-coordinate subgroup of one line. -/
def innerVector (line : I → G) (inner : I → Bool) (g : G) (i : I) : ℝ :=
  if line i = g ∧ inner i = true then 1 else 0

/-- The rank-one matrix associated with a vector. -/
def outerMatrix (v : I → ℝ) : Matrix I I ℝ := fun i j => v i * v j

/-- The linear sum of the coordinates weighted by `v`. -/
def vectorSum (v : I → ℝ) : (I → ℝ) →ₗ[ℝ] ℝ :=
  ∑ i, v i • LinearMap.proj i

omit [DecidableEq I] in
lemma vectorSum_apply (v x : I → ℝ) : vectorSum v x = ∑ i, v i * x i := by
  simp [vectorSum]

lemma outerMatrix_form (v x y : I → ℝ) :
    (outerMatrix v).toBilin' x y = vectorSum v x * vectorSum v y := by
  rw [Matrix.toBilin'_apply, vectorSum_apply, vectorSum_apply]
  simp only [outerMatrix]
  have hprod (i j : I) : x i * (v i * v j) * y j = (v i * x i) * (v j * y j) := by
    ring
  simp_rw [hprod, ← Finset.mul_sum]
  rw [← Finset.sum_mul]

omit [Fintype I] [DecidableEq I] in
/-- The precise rank-one-minus-blocks identity for the line/inner family. -/
theorem twoLevelKernel_decomposition (line : I → G) (inner : I → Bool) (γ δ : G → ℝ) :
    twoLevelKernel line inner γ δ =
      outerMatrix (fun _ : I => 1) -
        ∑ g, ((1 - γ g) • outerMatrix (lineVector line g) +
          (γ g * (1 - δ g)) • outerMatrix (innerVector line inner g)) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, outerMatrix]
  rw [Finset.sum_eq_single (line i)]
  · by_cases hline : line i = line j
    · by_cases hi : inner i = true <;> by_cases hj : inner j = true <;>
        simp [twoLevelKernel, lineVector, innerVector, hline, hi, hj]
      all_goals ring
    · have hline' : line j ≠ line i := Ne.symm hline
      simp [twoLevelKernel, lineVector, innerVector, hline, hline']
  · intro g _ hg
    have hg' : line i ≠ g := Ne.symm hg
    simp [lineVector, innerVector, hg']
  · simp

/-- The corresponding bilinear decomposition makes the squares explicit
when both arguments are equal. -/
theorem twoLevelKernel_form (line : I → G) (inner : I → Bool) (γ δ : G → ℝ)
    (x y : I → ℝ) :
    (twoLevelKernel line inner γ δ).toBilin' x y =
      vectorSum (fun _ : I => 1) x * vectorSum (fun _ : I => 1) y -
        ∑ g, ((1 - γ g) * (vectorSum (lineVector line g) x * vectorSum (lineVector line g) y) +
          (γ g * (1 - δ g)) *
            (vectorSum (innerVector line inner g) x * vectorSum (innerVector line inner g) y)) := by
  rw [twoLevelKernel_decomposition]
  simp only [map_sub, map_sum, map_add, map_smul, LinearMap.sub_apply,
    LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    outerMatrix_form]

/-- The bilinear kernel is symmetric even before positivity assumptions. -/
lemma twoLevelKernel_form_symm (line : I → G) (inner : I → Bool) (γ δ : G → ℝ)
    (x y : I → ℝ) :
    (twoLevelKernel line inner γ δ).toBilin' x y =
      (twoLevelKernel line inner γ δ).toBilin' y x := by
  rw [twoLevelKernel_form, twoLevelKernel_form]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro g _
    ring

/-- The normalized kernel is nonpositive on the zero-sum hyperplane. -/
theorem twoLevelKernel_nonpositive (line : I → G) (inner : I → Bool) (γ δ : G → ℝ)
    (hγ0 : ∀ g, 0 ≤ γ g) (hγ1 : ∀ g, γ g ≤ 1) (hδ1 : ∀ g, δ g ≤ 1)
    (v : I → ℝ) (hv : vectorSum (fun _ : I => 1) v = 0) :
    (twoLevelKernel line inner γ δ).toBilin' v v ≤ 0 := by
  rw [twoLevelKernel_form, hv, zero_mul, zero_sub]
  apply neg_nonpos.mpr
  apply Finset.sum_nonneg
  intro g _
  apply add_nonneg
  · exact mul_nonneg (sub_nonneg.mpr (hγ1 g)) (mul_self_nonneg _)
  · exact mul_nonneg (mul_nonneg (hγ0 g) (sub_nonneg.mpr (hδ1 g))) (mul_self_nonneg _)

def scaledMatrix (K : Matrix I I ℝ) (α : I → ℝ) : Matrix I I ℝ :=
  fun i j => α i * K i j * α j

/-- Undo diagonal normalization and subtract the entries corresponding to
invalid repeated removals. Zero scale coordinates also restore zero rows. -/
def weightedCorrection (K : Matrix I I ℝ) (W : ℝ) (α κ : I → ℝ) : Matrix I I ℝ :=
  W • scaledMatrix K α - Matrix.diagonal κ

lemma scaledMatrix_form (K : Matrix I I ℝ) (α x y : I → ℝ) :
    (scaledMatrix K α).toBilin' x y =
      K.toBilin' (fun i => α i * x i) (fun i => α i * y i) := by
  rw [Matrix.toBilin'_apply, Matrix.toBilin'_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp [scaledMatrix]
  ring

lemma diagonalMatrix_form (κ x y : I → ℝ) :
    (Matrix.diagonal κ).toBilin' x y = ∑ i, κ i * x i * y i := by
  rw [Matrix.toBilin'_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  ring

/-- The exact quadratic effect of scaling and invalid-diagonal removal. -/
theorem weightedCorrection_form (K : Matrix I I ℝ) (W : ℝ) (α κ x y : I → ℝ) :
    (weightedCorrection K W α κ).toBilin' x y =
      W * K.toBilin' (fun i => α i * x i) (fun i => α i * y i) -
        ∑ i, κ i * x i * y i := by
  simp only [weightedCorrection, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, scaledMatrix_form, diagonalMatrix_form]

end TwoLevel

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_LineUnarySignature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The line and unary factors of the bounded-table application

The bounded-table signature argument uses disjoint row/column line factors
and unary tree penalties. Factoring the product after two removals expresses
unary factors as nonnegative diagonal corrections of the line kernel.
-/

namespace ContingencyTables

open scoped BigOperators

section Products

variable {A : Type*} [Fintype A] [DecidableEq A]

def productTwoUpdates (a₀ a₁ a₂ : A → ℝ) (i j : A) : ℝ :=
  ∏ k, if k = i then (if k = j then a₂ k else a₁ k)
    else (if k = j then a₁ k else a₀ k)

/-- Exact factorization of the actual product after two coordinate changes,
including a repeated change of the same coordinate. -/
theorem productTwoUpdates_factor (a₀ a₁ a₂ : A → ℝ)
    (h₀ : ∀ k, a₀ k ≠ 0) (h₁ : ∀ k, a₁ k ≠ 0) (i j : A) :
    productTwoUpdates a₀ a₁ a₂ i j =
      (∏ k, a₀ k) * (a₁ i / a₀ i) * (a₁ j / a₀ j) *
        (if i = j then a₀ i * a₂ i / (a₁ i) ^ 2 else 1) := by
  have hterm (k : A) :
      (if k = i then (if k = j then a₂ k else a₁ k)
        else (if k = j then a₁ k else a₀ k)) =
      a₀ k * (if k = i then a₁ k / a₀ k else 1) *
        (if k = j then a₁ k / a₀ k else 1) *
        (if k = i ∧ i = j then a₀ k * a₂ k / (a₁ k) ^ 2 else 1) := by
    by_cases hi : k = i
    · subst k
      by_cases hij : i = j
      · subst j
        simp only [ite_true, if_true, and_self]
        field_simp [h₀ i, h₁ i]
      · simp only [ite_true, if_true, hij, ite_false, and_false, mul_one]
        field_simp [h₀ i]
    · by_cases hj : k = j
      · subst k
        simp only [hi, ite_false, ite_true, if_true, false_and, mul_one]
        field_simp [h₀ j]
      · simp [hi, hj]
  unfold productTwoUpdates
  simp_rw [hterm, Finset.prod_mul_distrib]
  have hlast : (∏ k, if k = i ∧ i = j then a₀ k * a₂ k / (a₁ k) ^ 2 else 1) =
      if i = j then a₀ i * a₂ i / (a₁ i) ^ 2 else 1 := by
    by_cases h : i = j <;> simp [h]
  rw [hlast]
  simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true, if_true]

end Products

section LineUnary

variable {I G : Type*} [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G]

/-- Values of every line factor and every unary factor after zero, one,
and two removals give exactly this two-removal matrix. -/
def lineUnaryRemoval (line : I → G) (a₀ a₁ a₂ : G → ℝ) (b₀ b₁ b₂ : I → ℝ) :
    Matrix I I ℝ := fun i j =>
  productTwoUpdates a₀ a₁ a₂ (line i) (line j) * productTwoUpdates b₀ b₁ b₂ i j

theorem lineUnaryRemoval_factor (line : I → G) (a₀ a₁ a₂ : G → ℝ) (b₀ b₁ b₂ : I → ℝ)
    (ha₀ : ∀ g, a₀ g ≠ 0) (ha₁ : ∀ g, a₁ g ≠ 0)
    (hb₀ : ∀ i, b₀ i ≠ 0) (hb₁ : ∀ i, b₁ i ≠ 0) (i j : I) :
    lineUnaryRemoval line a₀ a₁ a₂ b₀ b₁ b₂ i j =
      ((∏ g, a₀ g) * ∏ k, b₀ k) *
        ((a₁ (line i) / a₀ (line i)) * (b₁ i / b₀ i)) *
        ((a₁ (line j) / a₀ (line j)) * (b₁ j / b₀ j)) *
        (if line i = line j then a₀ (line i) * a₂ (line i) / (a₁ (line i)) ^ 2 else 1) *
        (if i = j then b₀ i * b₂ i / (b₁ i) ^ 2 else 1) := by
  rw [lineUnaryRemoval, productTwoUpdates_factor a₀ a₁ a₂ ha₀ ha₁,
    productTwoUpdates_factor b₀ b₁ b₂ hb₀ hb₁]
  ring

omit [Fintype I] [Fintype G] in
theorem normalized_line_unary_correction (line : I → G) (W : ℝ)
    (α : I → ℝ) (γ : G → ℝ) (δ : I → ℝ) :
    (fun i j => W * α i * α j * (if line i = line j then γ (line i) else 1) *
      (if i = j then δ i else 1)) =
    weightedCorrection (twoLevelKernel line (fun _ => false) γ (fun _ => 1)) W α
      (fun i => W * α i ^ 2 * γ (line i) * (1 - δ i)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [weightedCorrection, scaledMatrix, twoLevelKernel, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply, ite_true, if_true,
      Bool.false_eq_true, false_and, ite_false, mul_one]
    ring
  · by_cases hline : line i = line j <;>
      simp [weightedCorrection, scaledMatrix, twoLevelKernel, hij, hline] <;> ring

end LineUnary

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ProductIntegerSignature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Raw integer signatures of the actual line and unary product

The line groups are disjoint. Integer counts at zero are masked; a repeated
removal from a count below two uses a zero second-update factor. This
identifies the actual integer matrix, including its box boundaries, with a
congruence of the proved line/unary update matrix.
-/

namespace ContingencyTables.ProductIntegerSignature

open scoped BigOperators Classical Matrix
open FactorialSignatures

variable {I G : Type*} [Fintype I] [Fintype G]

noncomputable def activeMask (z : I → ℕ) : I → ℝ := fun i => if 0 < z i then 1 else 0

end ContingencyTables.ProductIntegerSignature

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_NestedProductSignature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The first paper's actual line and small-slot subgroup product

Each small-slot subgroup is contained in a disjoint line group. The literal
product after two removals is factored into the two-level kernel. Zero
integer counts are masked and invalid repeated removals subtract a
nonnegative diagonal.
-/

namespace ContingencyTables.NestedProductSignature

open scoped BigOperators Classical Matrix
open FactorialSignatures ProductIntegerSignature

variable {I G : Type*} [Fintype I] [Fintype G]

def unitExtension (c : G → ℝ) : Option G → ℝ := fun o => o.elim 1 c

def subgroup (line : I → G) (inner : I → Bool) (i : I) : Option G :=
  if inner i then some (line i) else none

noncomputable def nestedRemoval (line : I → G) (inner : I → Bool)
    (a₀ a₁ a₂ c₀ c₁ c₂ : G → ℝ) : Matrix I I ℝ := fun i j =>
  productTwoUpdates a₀ a₁ a₂ (line i) (line j) *
    productTwoUpdates (unitExtension c₀) (unitExtension c₁) (unitExtension c₂)
      (subgroup line inner i) (subgroup line inner j)

omit [Fintype I] in
lemma nestedRemoval_factor (line : I → G) (inner : I → Bool)
    (a₀ a₁ a₂ c₀ c₁ c₂ : G → ℝ)
    (ha₀ : ∀ g, a₀ g ≠ 0) (ha₁ : ∀ g, a₁ g ≠ 0)
    (hc₀ : ∀ g, c₀ g ≠ 0) (hc₁ : ∀ g, c₁ g ≠ 0) (i j : I) :
    nestedRemoval line inner a₀ a₁ a₂ c₀ c₁ c₂ i j =
      ((∏ g, a₀ g) * ∏ g, c₀ g) *
        ((a₁ (line i)/a₀ (line i)) * (if inner i then c₁ (line i)/c₀ (line i) else 1)) *
        ((a₁ (line j)/a₀ (line j)) * (if inner j then c₁ (line j)/c₀ (line j) else 1)) *
        twoLevelKernel line inner
          (fun g => a₀ g*a₂ g/(a₁ g)^2) (fun g => c₀ g*c₂ g/(c₁ g)^2) i j := by
  have hce₀ : ∀ g, unitExtension c₀ g ≠ 0 := by intro g; cases g <;> simp [unitExtension,hc₀]
  have hce₁ : ∀ g, unitExtension c₁ g ≠ 0 := by intro g; cases g <;> simp [unitExtension,hc₁]
  unfold nestedRemoval
  rw [productTwoUpdates_factor _ _ _ ha₀ ha₁,productTwoUpdates_factor _ _ _ hce₀ hce₁]
  simp only [Fintype.prod_option,unitExtension,Option.elim_none,Option.elim_some,one_mul]
  cases hi : inner i <;> cases hj : inner j <;> by_cases hline : line i=line j <;>
    simp [subgroup,hi,hj,hline,twoLevelKernel] <;> ring

lemma updates_nonnegative {A : Type*} [Fintype A] [DecidableEq A]
    (a₀ a₁ a₂ : A → ℝ) (ha₀ : ∀ k, 0 ≤ a₀ k) (ha₁ : ∀ k, 0 ≤ a₁ k) (ha₂ : ∀ k, 0 ≤ a₂ k)
    (i j : A) : 0 ≤ productTwoUpdates a₀ a₁ a₂ i j := by
  apply Finset.prod_nonneg
  intro k _
  split_ifs <;> first | exact ha₀ k | exact ha₁ k | exact ha₂ k

end ContingencyTables.NestedProductSignature

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ScalarPenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual positive scalar softening factors

Absolute affine deviations, positive parts and interval distances have
convex integer exponents. Their powers of two are positive log-concave
sequences, supplying the concrete line and unary factors of both papers.
-/

namespace ContingencyTables.ScalarPenalty

open scoped BigOperators

noncomputable def factor (A : ℝ) (p : ℕ → ℝ) (n : ℕ) : ℝ := (2:ℝ)^(-A*p n)

lemma factor_positive (A : ℝ) (p : ℕ → ℝ) (n : ℕ) : 0 < factor A p n :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- Convex discrete exponents give the exact scalar log-concavity test. -/
theorem factor_logConcave (A : ℝ) (hA : 0 ≤ A) (p : ℕ → ℝ) (n : ℕ)
    (hp : 2*p (n-1) ≤ p n+p (n-2)) :
    factor A p n * factor A p (n-2) ≤ (factor A p (n-1))^2 := by
  unfold factor
  rw [pow_two,← Real.rpow_add (by norm_num : (0:ℝ)<2),
    ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left hp hA]

lemma affine_midpoint (a b : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    2*(a+((n-1:ℕ):ℝ)*b) = (a+(n:ℝ)*b)+(a+((n-2:ℕ):ℝ)*b) := by
  rw [Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_sub hn]
  norm_num
  ring

lemma abs_affine_convex (a b : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    2*|a+((n-1:ℕ):ℝ)*b| ≤ |a+(n:ℝ)*b|+|a+((n-2:ℕ):ℝ)*b| := by
  have h := abs_add_le (a+(n:ℝ)*b) (a+((n-2:ℕ):ℝ)*b)
  rw [← affine_midpoint a b n hn,abs_mul] at h
  norm_num at h
  exact h

lemma max_convex (p q : ℕ → ℝ) (n : ℕ)
    (hp : 2*p (n-1) ≤ p n+p (n-2)) (hq : 2*q (n-1) ≤ q n+q (n-2)) :
    2*max (p (n-1)) (q (n-1)) ≤ max (p n) (q n)+max (p (n-2)) (q (n-2)) := by
  by_cases h : p (n-1) ≤ q (n-1)
  · rw [max_eq_right h]
    linarith [le_max_right (p n) (q n),le_max_right (p (n-2)) (q (n-2))]
  · rw [max_eq_left (le_of_not_ge h)]
    linarith [le_max_left (p n) (q n),le_max_left (p (n-2)) (q (n-2))]

/-- The row and column absolute-deviation softeners used in both papers. -/
theorem abs_factor_logConcave (A a b : ℝ) (hA : 0 ≤ A) (n : ℕ) (hn : 2 ≤ n) :
    factor A (fun k => |a+(k:ℝ)*b|) n * factor A (fun k => |a+(k:ℝ)*b|) (n-2) ≤
      (factor A (fun k => |a+(k:ℝ)*b|) (n-1))^2 :=
  factor_logConcave A hA _ n (abs_affine_convex a b n hn)

/-- Positive-part small-slot penalties of the first paper. -/
theorem positivePart_factor_logConcave (A a b : ℝ) (hA : 0 ≤ A) (n : ℕ) (hn : 2 ≤ n) :
    factor A (fun k => max (a+(k:ℝ)*b) 0) n * factor A (fun k => max (a+(k:ℝ)*b) 0) (n-2) ≤
      (factor A (fun k => max (a+(k:ℝ)*b) 0) (n-1))^2 := by
  apply factor_logConcave A hA
  exact max_convex (fun k => a+(k:ℝ)*b) (fun _ => 0) n
    (le_of_eq (affine_midpoint a b n hn)) (by simp)

end ContingencyTables.ScalarPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_NestedPenaltyApplication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The first paper's actual positive penalties and hard equality limit

Full row/column deviations give absolute affine line factors; the nested
small-slot residual constraints give positive-part affine factors. Their
product is exactly 2^(-L D). Balanced large-slot sums retain their proved
signature, and their finite limit is the exact zero-penalty indicator sum.
-/

namespace ContingencyTables.NestedPenaltyApplication

open scoped BigOperators Classical Matrix Topology
open Filter FactorialSignatures ProductIntegerSignature
open NestedProductSignature ScalarPenalty

variable {C G : Type*} [Fintype C] [Fintype G]

lemma prod_pow (L : ℝ) (p : G → ℝ) :
    (∏ g, (2:ℝ)^(-L*p g))=(2:ℝ)^(-L*∑ g, p g) := by
  rw [← Real.rpow_sum_of_pos (by norm_num : (0:ℝ)<2)]
  congr 1
  rw [Finset.mul_sum]

end ContingencyTables.NestedPenaltyApplication

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Signed cut equations for the actual physical table views

Small row and column views may disagree. Their two incidences therefore
remain separate in the cut formula. Large cells have a single physical
value at both endpoints, so every internal large-cell contribution cancels.
-/

namespace ContingencyTables.ForestCut

open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def rowDifference (small : I → J → Bool) (x z X : I → J → ℝ) (i : I) : ℝ :=
  ∑ j, if small i j then x i j-X i j else z i j-X i j

noncomputable def columnDifference (small : I → J → Bool) (q z X : I → J → ℝ) (j : J) : ℝ :=
  ∑ i, if small i j then q i j-X i j else z i j-X i j

/-- The interval bound needed in the equality-softening count argument
follows from the proved cut displacement estimate, with ample slack. -/
lemma physical_interval_of_displacement (d b X z : ℝ) (hd : 1 ≤ d) (hb : 0 ≤ b)
    (hX : 0 ≤ X ∧ X ≤ b) (hz : |z-X| ≤ 4*d*b) :
    -10*d*b ≤ z ∧ z ≤ 10*d*b := by
  have h := abs_le.mp hz
  have hdb : 0 ≤ d*b := mul_nonneg (by linarith) hb
  have hbdb : b ≤ d*b := by nlinarith
  constructor <;> nlinarith

end ContingencyTables.ForestCut

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestCapacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual bipartite cell forests and their completion intervals

The graph vertices are the original row and column labels. Capacities
are attached to unordered row-column edges. The deletion-component cut
is constructed from the maximizing forest, so the hypotheses of the
physical cut estimate follow from actual graph properties.
-/

namespace ContingencyTables.ForestCapacity

open scoped BigOperators Classical
open SimpleGraph
open ForestCut

variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype I] [Fintype J] in
lemma cell_edge_injective : Function.Injective
    (fun a : I×J => s(Sum.inl a.1,Sum.inr a.2)) := by
  rintro ⟨i,j⟩ ⟨i',j'⟩ h
  simpa only [Sym2.eq_iff,Prod.mk.injEq,Sum.inl.injEq,Sum.inr.injEq,
    Sum.inl_ne_inr,Sum.inr_ne_inl,false_and,or_false] using h

noncomputable def treeCell (T : SimpleGraph (I⊕J)) (i : I) (j : J) : Bool :=
  decide (T.Adj (.inl i) (.inr j))

end ContingencyTables.ForestCapacity

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_EqualitySoftening
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Root penalties and exact nonroot equations

Root lines carry their actual absolute-deviation penalty. Nonroot lines
carry a positive equality softener; its limit is the exact prescribed-line
indicator. Unary interval penalties include the companion's tree factors.
All balanced large-cell sums are performed before this finite limit.
-/

namespace ContingencyTables.EqualitySoftening

open scoped BigOperators Classical Matrix Topology
open Filter FactorialSignatures ProductIntegerSignature
open ScalarPenalty

variable {C G : Type*} [Fintype C] [Fintype G]

noncomputable def lineFactor (root : G → Bool) (rate offset slope : G → ℝ)
    (L : ℝ) (g : G) (n : ℕ) : ℝ :=
  factor (if root g then rate g else L) (fun k => |offset g+(k:ℝ)*slope g|) n

noncomputable def exactLineFactor (root : G → Bool) (rate offset slope : G → ℝ)
    (g : G) (n : ℕ) : ℝ :=
  if root g then factor (rate g) (fun k => |offset g+(k:ℝ)*slope g|) n
  else if |offset g+(n:ℝ)*slope g|=0 then 1 else 0

/-- A physical affine coordinate, including a reflected tree coordinate. -/
noncomputable def affineDistance (ell slope cap : ℝ) (n : ℕ) : ℝ :=
  max 0 (max (-(ell+(n:ℝ)*slope)) (ell+(n:ℝ)*slope-cap))

lemma affineDistance_convex (ell slope cap : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    2*affineDistance ell slope cap (n-1) ≤
      affineDistance ell slope cap n+affineDistance ell slope cap (n-2) := by
  unfold affineDistance
  apply max_convex (fun _ => 0)
    (fun k => max (-(ell+(k:ℝ)*slope)) (ell+(k:ℝ)*slope-cap)) n
  · simp
  · apply max_convex (fun k => -(ell+(k:ℝ)*slope))
      (fun k => ell+(k:ℝ)*slope-cap) n
    · have h := affine_midpoint (-ell) (-slope) n hn
      first | (convert le_of_eq h using 1 <;> ring) | exact (le_of_eq (by ring)).trans ((le_of_eq h).trans (le_of_eq (by ring)))
    · have h := affine_midpoint (ell-cap) slope n hn
      first | (convert le_of_eq h using 1 <;> ring) | exact (le_of_eq (by ring)).trans ((le_of_eq h).trans (le_of_eq (by ring)))

noncomputable def unaryFactor (rate ell slope cap : C → ℝ) (i : C) (n : ℕ) : ℝ :=
  factor (rate i) (affineDistance (ell i) (slope i) (cap i)) n

end ContingencyTables.EqualitySoftening

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestPenaltyApplication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Literal companion row/column and unary tree penalties

The physical row view is ell+x; the physical column view is ell+M-y.
The line groups are the disjoint original row and column coordinates.
Roots are the actual chosen component roots of the large-cell forest.
Only the false (row) coordinate of each tree cell carries its interval
penalty. Thus the concrete exact factor family is precisely the source's
nonroot indicator times its root/tree penalty weight.
-/

namespace ContingencyTables.ForestPenaltyApplication

open scoped BigOperators Classical Matrix
open SimpleGraph
open EqualitySoftening ProductIntegerSignature ScalarPenalty
open ForestCapacity

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def physicalRow (ell : I → J → ℤ) (z : ((I×J)×Bool) → ℕ) (i : I) (j : J) : ℝ :=
  (ell i j:ℝ)+z ((i,j),false)

noncomputable def physicalColumn (ell : I → J → ℤ) (M : I → J → ℕ)
    (z : ((I×J)×Bool) → ℕ) (i : I) (j : J) : ℝ :=
  (ell i j:ℝ)+M i j-z ((i,j),true)

noncomputable def lineOffset (ell : I → J → ℤ) (M : I → J → ℕ)
    (r : I → ℤ) (c : J → ℤ) : I⊕J → ℝ :=
  Sum.elim (fun i => (∑ j, (ell i j:ℝ))-r i)
    (fun j => (∑ i, ((ell i j:ℝ)+M i j))-c j)

noncomputable def deviation (ell : I → J → ℤ) (M : I → J → ℕ)
    (r : I → ℤ) (c : J → ℤ) (z : ((I×J)×Bool) → ℕ) : I⊕J → ℝ :=
  Sum.elim (fun i => (∑ j, physicalRow ell z i j)-r i)
    (fun j => (∑ i, physicalColumn ell M z i j)-c j)

noncomputable def unaryRate (T : SimpleGraph (I⊕J)) (b : I → J → ℕ)
    (alpha : ℝ) (a : (I×J)×Bool) : ℝ :=
  if a.2=false ∧ T.Adj (.inl a.1.1) (.inr a.1.2) then alpha/b a.1.1 a.1.2 else 0

noncomputable def unaryEll (ell : I → J → ℤ) (a : (I×J)×Bool) : ℝ := ell a.1.1 a.1.2

def unarySlope (_ : (I×J)×Bool) : ℝ := 1

noncomputable def unaryCap (b : I → J → ℕ) (a : (I×J)×Bool) : ℝ := b a.1.1 a.1.2

noncomputable def treePenalty (T : SimpleGraph (I⊕J)) (b : I → J → ℕ)
    (ell : I → J → ℤ) (z : ((I×J)×Bool) → ℕ) : ℝ :=
  ∑ i, ∑ j, if T.Adj (.inl i) (.inr j) then
    affineDistance (ell i j) 1 (b i j) (z ((i,j),false))/(b i j:ℝ) else 0

end ContingencyTables.ForestPenaltyApplication

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_LargePairEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Physical indexing of all balanced large-cell pairs

The recursively added pairs are identified with the actual finite cells,
and their assignments with the dependent product of the physical finite
intervals. No extra coordinate or assignment multiplicity is introduced.
-/

namespace ContingencyTables.LargePairEnumeration

open scoped BigOperators Classical

universe u

/-- Widths in the explicit order supplied by a finite cell enumeration. -/
def widths : {n : ℕ} → (Fin n → ℕ) → List ℕ
  | 0,_ => []
  | _+1,M => M 0::widths (fun i => M i.succ)

lemma widths_lower {n : ℕ} (M : Fin n → ℕ) (h : ∀ i, 2≤M i) :
    ∀ w ∈ widths M, 2≤w := by
  induction n with
  | zero => intro w hw; exact False.elim (List.not_mem_nil hw)
  | succ n ih =>
    intro w hw
    simp only [widths,List.mem_cons] at hw
    rcases hw with rfl|hw
    · exact h 0
    · exact ih (fun i => M i.succ) (fun i => h i.succ) w hw

def pairSuccEquiv (n : ℕ) : ((Fin n×Bool)⊕Bool) ≃ Fin (n+1)×Bool where
  toFun
    | .inl (i,b) => (i.succ,b)
    | .inr b => (0,b)
  invFun p := Fin.cases (.inr p.2) (fun i => .inl (i,p.2)) p.1
  left_inv p := by cases p with
    | inl p => rcases p with ⟨i,b⟩; rfl
    | inr b => rfl
  right_inv p := by
    rcases p with ⟨i,b⟩
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

def joinedProfile {S : Type*} {n : ℕ} (M : Fin n → ℕ) (z : S → ℕ)
    (a : (i : Fin n) → Fin (M i+1)) : S⊕(Fin n×Bool) → ℕ
  | .inl s => z s
  | .inr (i,b) => if b then M i-(a i).val else (a i).val

end ContingencyTables.LargePairEnumeration

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_TwoLiftStates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual paired states and the two factorial weights

Every physical cell contains an arbitrary finite bundle of paired labels.
The plain and one-hole/one-full predicates imply the exact cell count
identities. Thus the literal subset lifts agree on plain states and obey
the manuscript's W² comparison on every actual chain state.
-/

namespace ContingencyTables.TwoLiftStates

open scoped BigOperators Classical Matrix
open FactorialSignatures

variable {P C : Type*} [Fintype P] [Fintype C]

noncomputable def occupancy (S : Set (P × Bool)) (p : P) : ℕ :=
  (if (p,false) ∈ S then 1 else 0) + (if (p,true) ∈ S then 1 else 0)

end ContingencyTables.TwoLiftStates

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_GridBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cut faces of a unit grid

The geometric step in the dense sampler's conductance proof: two points
in differently labelled open bins at sup distance less than `r ≤ 1` are
within `r` of a common closed face of oppositely labelled axis neighbours.
A coordinate path avoids any general-position assumption at simultaneous
grid crossings.
-/

namespace ContingencyTables.GridBoundary

variable {I : Type*} [DecidableEq I]

def mixed (a b : I → ℤ) (S : Finset I) : I → ℤ :=
  fun i => if i ∈ S then b i else a i

theorem cut_edge_aux (P : (I → ℤ) → Prop) (a b : I → ℤ)
    (ha : P a) (K : Finset I) (hb : ¬ P (mixed a b K)) :
    ∃ S i, S ⊆ K ∧ i ∈ K ∧ i ∉ S ∧ P (mixed a b S) ∧
      ¬ P (mixed a b (insert i S)) := by
  classical
  induction K using Finset.induction_on with
  | empty =>
    have heq : mixed a b ∅ = a := by ext i; simp [mixed]
    exact False.elim (hb (heq.symm ▸ ha))
  | @insert i K hi ih =>
    by_cases hK : P (mixed a b K)
    · exact ⟨K, i, Finset.subset_insert _ _, Finset.mem_insert_self _ _, hi, hK, hb⟩
    · obtain ⟨S, j, hS, hj, hjS, hPS, hPj⟩ := ih hK
      exact ⟨S, j, hS.trans (Finset.subset_insert _ _), Finset.mem_insert_of_mem hj,
        hjS, hPS, hPj⟩

/-- A change of labels along a coordinate path occurs on an axis edge. -/
theorem cut_edge [Fintype I] (P : (I → ℤ) → Prop) (a b : I → ℤ)
    (ha : P a) (hb : ¬ P b) :
    ∃ S i, i ∉ S ∧ P (mixed a b S) ∧ ¬ P (mixed a b (insert i S)) := by
  have heq : mixed a b Finset.univ = b := by ext i; simp [mixed]
  have hb' : ¬ P (mixed a b Finset.univ) := by rw [heq]; exact hb
  obtain ⟨S, i, _, _, hi, hS, hSi⟩ := cut_edge_aux P a b ha Finset.univ hb'
  exact ⟨S, i, hi, hS, hSi⟩

def OpenBin (a : I → ℤ) (x : I → ℝ) : Prop :=
  ∀ i, (a i : ℝ) < x i ∧ x i < (a i : ℝ) + 1

def ClosedBin (a : I → ℤ) (x : I → ℝ) : Prop :=
  ∀ i, (a i : ℝ) ≤ x i ∧ x i ≤ (a i : ℝ) + 1

theorem short_bin_indices (a b : ℤ) (x z r : ℝ)
    (hx : (a : ℝ) < x ∧ x < (a : ℝ) + 1)
    (hz : (b : ℝ) < z ∧ z < (b : ℝ) + 1)
    (hd : |z - x| < r) (hr : r ≤ 1) (hab : a ≠ b) :
    b = a + 1 ∨ a = b + 1 := by
  have hd' := abs_lt.mp hd
  have hba : b < a + 2 := by
    exact_mod_cast (show (b : ℝ) < (a : ℝ) + 2 by linarith)
  have hab' : a < b + 2 := by
    exact_mod_cast (show (a : ℝ) < (b : ℝ) + 2 by linarith)
  omega

theorem clamp_near (a x z r : ℝ)
    (hx : a < x ∧ x < a + 1) (hd : |z - x| < r) :
    ∃ w, a ≤ w ∧ w ≤ a + 1 ∧ |z - w| < r := by
  have hr : 0 < r := lt_of_le_of_lt (abs_nonneg _) hd
  have hd' := abs_lt.mp hd
  by_cases hza : z < a
  · refine ⟨a, le_rfl, by linarith, ?_⟩
    rw [abs_of_neg (by linarith : z - a < 0)]
    linarith
  · by_cases haz : a + 1 < z
    · refine ⟨a + 1, by linarith, le_rfl, ?_⟩
      rw [abs_of_pos (by linarith : 0 < z - (a + 1))]
      linarith
    · exact ⟨z, le_of_not_gt hza, le_of_not_gt haz, by simpa using hr⟩

theorem adjacent_boundary (a b : ℤ) (x z r : ℝ)
    (hx : (a : ℝ) < x ∧ x < (a : ℝ) + 1)
    (hz : (b : ℝ) < z ∧ z < (b : ℝ) + 1)
    (hd : |z - x| < r) (hab : b = a + 1 ∨ a = b + 1) :
    (a : ℝ) ≤ max (a : ℝ) b ∧ max (a : ℝ) b ≤ (a : ℝ) + 1 ∧
    (b : ℝ) ≤ max (a : ℝ) b ∧ max (a : ℝ) b ≤ (b : ℝ) + 1 ∧
    |z - max (a : ℝ) b| < r := by
  have hd' := abs_lt.mp hd
  rcases hab with hab | hab
  · have heq : (b : ℝ) = (a : ℝ) + 1 := by exact_mod_cast hab
    rw [max_eq_right (by linarith : (a : ℝ) ≤ b)]
    refine ⟨by linarith, by linarith, le_rfl, by linarith, ?_⟩
    rw [abs_of_pos (by linarith : 0 < z - (b : ℝ))]
    linarith
  · have heq : (a : ℝ) = (b : ℝ) + 1 := by exact_mod_cast hab
    rw [max_eq_left (by linarith : (b : ℝ) ≤ a)]
    refine ⟨le_rfl, by linarith, by linarith, by linarith, ?_⟩
    rw [abs_of_neg (by linarith : z - (a : ℝ) < 0)]
    linarith

/-- The terminal point of a short displacement lies near an actual cut
face. The intermediate bins use only the two endpoint indices in each
coordinate, so they stay inside any rectangular grid containing them. -/
theorem near_cut_face [Fintype I] (P : (I → ℤ) → Prop)
    (a b : I → ℤ) (x z : I → ℝ) (r : ℝ)
    (ha : OpenBin a x) (hb : OpenBin b z)
    (hd : ∀ i, |z i - x i| < r) (hr : r ≤ 1)
    (hPa : P a) (hPb : ¬ P b) :
    ∃ S i w, i ∉ S ∧ P (mixed a b S) ∧ ¬ P (mixed a b (insert i S)) ∧
      (b i = a i + 1 ∨ a i = b i + 1) ∧
      ClosedBin (mixed a b S) w ∧ ClosedBin (mixed a b (insert i S)) w ∧
      (∀ j, |z j - w j| < r) := by
  classical
  obtain ⟨S, i, hi, hS, hSi⟩ := cut_edge P a b hPa hPb
  have hneq : a i ≠ b i := by
    intro heq
    apply hSi
    have hmix : mixed a b (insert i S) = mixed a b S := by
      ext j
      by_cases hj : j = i
      · subst j
        simp [mixed, hi, heq]
      · simp [mixed, hj]
    rwa [hmix]
  have hadj := short_bin_indices (a i) (b i) (x i) (z i) r (ha i) (hb i) (hd i) hr hneq
  have hface := adjacent_boundary (a i) (b i) (x i) (z i) r (ha i) (hb i) (hd i) hadj
  have hnear (j : I) : ∃ w, ((mixed a b S j : ℤ) : ℝ) ≤ w ∧
      w ≤ (mixed a b S j : ℝ) + 1 ∧ |z j - w| < r := by
    by_cases hj : j ∈ S
    · refine ⟨z j, ?_, ?_, ?_⟩
      · simpa [mixed, hj] using (hb j).1.le
      · simpa [mixed, hj] using (hb j).2.le
      · simpa using lt_of_le_of_lt (abs_nonneg _) (hd j)
    · simpa [mixed, hj] using clamp_near (a j) (x j) (z j) r (ha j) (hd j)
  choose v hv using hnear
  let w : I → ℝ := Function.update v i (max (a i : ℝ) (b i))
  refine ⟨S, i, w, hi, hS, hSi, hadj, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j = i
    · subst j
      have hp := And.intro hface.1 hface.2.1
      simpa [w, mixed, hi] using hp
    · have hp := And.intro (hv j).1 (hv j).2.1
      simpa [w, hj] using hp
  · intro j
    by_cases hj : j = i
    · subst j
      have hp := And.intro hface.2.2.1 hface.2.2.2.1
      simpa [w, mixed] using hp
    · have hp := And.intro (hv j).1 (hv j).2.1
      simpa [w, mixed, hj] using hp
  · intro j
    by_cases hj : j = i
    · subst j
      simpa [w] using hface.2.2.2.2
    · simpa [w, hj] using (hv j).2.2

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_GridMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Volume and mass of grid face neighbourhoods

The exact tube volume and a finite integral-cover bound used to turn the
interpolation shell gain into a weighted cut estimate.
-/

namespace ContingencyTables.GridBoundary

open MeasureTheory
open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

def tubeLower (a : I → ℤ) (i : I) (r : ℝ) : I → ℝ :=
  fun j => if j = i then (a j : ℝ) + 1 - r else (a j : ℝ) - r

def tubeUpper (a : I → ℤ) (_i : I) (r : ℝ) : I → ℝ :=
  fun j => (a j : ℝ) + 1 + r

/-- An open rectangular neighbourhood of the positive `i`-face of a bin. -/
def faceTube (a : I → ℤ) (i : I) (r : ℝ) : Set (I → ℝ) :=
  Set.pi Set.univ fun j => Set.Ioo (tubeLower a i r j) (tubeUpper a i r j)

theorem faceTube_measurable (a : I → ℤ) (i : I) (r : ℝ) :
    MeasurableSet (faceTube a i r) := by
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ioo

omit [Fintype I] in
theorem tube_width (a : I → ℤ) (i j : I) (r : ℝ) :
    tubeUpper a i r j - tubeLower a i r j = if j = i then 2 * r else 1 + 2 * r := by
  by_cases h : j = i <;> simp [tubeUpper, tubeLower, h] <;> ring

theorem product_one_exception (u v : ℝ) (i : I) :
    (∏ j : I, if j = i then u else v) = u * v ^ (Fintype.card I - 1) := by
  have heq : (fun j : I => if j = i then u else v) = Function.update (fun _ => v) i u := by
    ext j
    by_cases hj : j = i <;> simp [hj]
  rw [heq, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp [Finset.sdiff_singleton_eq_erase]

theorem faceTube_volume (a : I → ℤ) (i : I) (r : ℝ) (hr : 0 ≤ r) :
    volume (faceTube a i r) =
      ENNReal.ofReal (2 * r * (1 + 2 * r) ^ (Fintype.card I - 1)) := by
  rw [faceTube, Real.volume_pi_Ioo]
  simp_rw [tube_width]
  rw [← ENNReal.ofReal_prod_of_nonneg]
  · rw [product_one_exception]
  · intro j _
    split_ifs <;> positivity

theorem faceTube_volume_toReal (a : I → ℤ) (i : I) (r : ℝ) (hr : 0 ≤ r) :
    (volume (faceTube a i r)).toReal =
      2 * r * (1 + 2 * r) ^ (Fintype.card I - 1) := by
  rw [faceTube_volume a i r hr, ENNReal.toReal_ofReal (by positivity)]

theorem reverse_bernoulli (u : ℝ) (hu : 0 ≤ u) (n : ℕ) :
    (1 + u) ^ n * (1 - (n : ℝ) * u) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have haux : (1 + u) * (1 - ((n : ℝ) + 1) * u) ≤ 1 - (n : ℝ) * u := by
      have h := mul_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity) (sq_nonneg u)
      nlinarith
    calc
      (1 + u) ^ (n + 1) * (1 - ((n + 1 : ℕ) : ℝ) * u) =
          (1 + u) ^ n * ((1 + u) * (1 - ((n : ℝ) + 1) * u)) := by
        rw [pow_succ, Nat.cast_add, Nat.cast_one]
        ring
      _ ≤ (1 + u) ^ n * (1 - (n : ℝ) * u) :=
        mul_le_mul_of_nonneg_left haux (pow_nonneg (by linarith) _)
      _ ≤ 1 := ih

/-- The manuscript's tube-volume bound follows without an exponential
estimate: the relevant power is at most two by reverse Bernoulli. -/
theorem faceTube_volume_le_one (a : I → ℤ) (i : I) (r : ℝ)
    (hr : 0 ≤ r) (hr₁ : r ≤ 1 / 4)
    (hsize : (Fintype.card I - 1 : ℕ) * (2 * r) ≤ (1 / 2 : ℝ)) :
    (volume (faceTube a i r)).toReal ≤ 1 := by
  rw [faceTube_volume_toReal a i r hr]
  have hpow := pow_nonneg (show 0 ≤ 1 + 2 * r by linarith) (Fintype.card I - 1)
  have hbern := reverse_bernoulli (2 * r) (by linarith) (Fintype.card I - 1)
  have htwo : (1 + 2 * r) ^ (Fintype.card I - 1) ≤ 2 := by nlinarith
  nlinarith

omit [Fintype I] in
/-- A point near the positive face belongs to its rectangular tube. -/
theorem mem_faceTube_of_near (a : I → ℤ) (i : I) (r : ℝ) (z w : I → ℝ)
    (hw : ClosedBin a w) (hwi : w i = (a i : ℝ) + 1)
    (hd : ∀ j, |z j - w j| < r) : z ∈ faceTube a i r := by
  intro j _
  have h := abs_lt.mp (hd j)
  by_cases hj : j = i
  · subst j
    simp only [tubeLower, tubeUpper, ite_true, if_true]
    rw [hwi] at h
    constructor <;> linarith
  · simp only [tubeLower, tubeUpper, hj, ite_false]
    have hwj := hw j
    constructor <;> linarith

end ContingencyTables.GridBoundary

namespace ContingencyTables

open MeasureTheory
open scoped BigOperators

/-- Integrating a finite cover, allowing overlap and a null exceptional set.
This applies to the face tubes after removing grid hyperplanes. -/
theorem integral_finite_cover {X K : Type*} [MeasurableSpace X] [Fintype K]
    {μ : Measure X} (S : Set X) (E : K → Set X) (ρ : X → ℝ)
    (hS : MeasurableSet S) (hE : ∀ k, MeasurableSet (E k))
    (hiS : IntegrableOn ρ S μ) (hiE : ∀ k, IntegrableOn ρ (E k) μ)
    (hpos : ∀ k x, x ∈ E k → 0 ≤ ρ x)
    (hcover : ∀ᵐ x ∂μ, x ∈ S → ∃ k, x ∈ E k) :
    (∫ x in S, ρ x ∂μ) ≤ ∑ k, ∫ x in E k, ρ x ∂μ := by
  classical
  have hterm (k : K) (x : X) : 0 ≤ (E k).indicator ρ x := by
    by_cases hx : x ∈ E k
    · simpa [hx] using hpos k x hx
    · simp [hx]
  have hmono : S.indicator ρ ≤ᵐ[μ] fun x => ∑ k, (E k).indicator ρ x := by
    filter_upwards [hcover] with x hx
    by_cases hxS : x ∈ S
    · obtain ⟨k, hk⟩ := hx hxS
      simpa [hxS, hk] using
        (Finset.single_le_sum (fun j _ => hterm j x) (Finset.mem_univ k))
    · simpa [hxS] using Finset.sum_nonneg (fun k _ => hterm k x)
  have hint (k : K) : Integrable ((E k).indicator ρ) μ :=
    (hiE k).integrable_indicator (hE k)
  have hbound := integral_mono_ae (hiS.integrable_indicator hS)
    (integrable_finsetSum Finset.univ fun k _ => hint k) hmono
  rw [integral_indicator hS, integral_finsetSum Finset.univ (fun k _ => hint k)] at hbound
  simpa only [integral_indicator (hE _)] using hbound

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BoxGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-box geometry for the conditional conductance argument

Finite unions of grid boxes remain finite unions of boxes under weighted
Minkowski interpolation, giving the domain hypothesis of Prékopa–Leindler.
-/

namespace ContingencyTables.PublishedInputs

open MeasureTheory

theorem scalar_box_interpolation (t a b c d z : ℝ)
    (ht : 0 < t) (ht1 : t < 1) (hab : a < b) (hcd : c < d)
    (hz : (1 - t) * a + t * c < z ∧ z < (1 - t) * b + t * d) :
    ∃ w : ℝ × ℝ, a < w.1 ∧ w.1 < b ∧ c < w.2 ∧ w.2 < d ∧
      z = (1 - t) * w.1 + t * w.2 := by
  let D := (1 - t) * (b - a) + t * (d - c)
  have hD : 0 < D := add_pos (mul_pos (sub_pos.mpr ht1) (sub_pos.mpr hab))
    (mul_pos ht (sub_pos.mpr hcd))
  let wgt := (z - ((1 - t) * a + t * c)) / D
  have hwgt : 0 < wgt := div_pos (sub_pos.mpr hz.1) hD
  have hwgt1 : wgt < 1 := by
    apply (div_lt_one hD).mpr
    dsimp [D]
    linarith [hz.2]
  refine ⟨(a + wgt * (b - a), c + wgt * (d - c)), ?_, ?_, ?_, ?_, ?_⟩
  · linarith [mul_pos hwgt (sub_pos.mpr hab)]
  · nlinarith [mul_pos (sub_pos.mpr hwgt1) (sub_pos.mpr hab)]
  · linarith [mul_pos hwgt (sub_pos.mpr hcd)]
  · nlinarith [mul_pos (sub_pos.mpr hwgt1) (sub_pos.mpr hcd)]
  · dsimp [wgt]
    field_simp
    dsimp [D]
    ring

theorem weighted_geometric_doubling (a b t : ℝ) (ha : 0 < a)
    (hb : 2 * a ≤ b) (ht : 0 ≤ t) :
    (2 : ℝ) ^ t * a ≤ a ^ (1 - t) * b ^ t := by
  have hab : 0 ≤ 2 * a := by positivity
  have hr := Real.rpow_le_rpow hab hb ht
  calc
    (2 : ℝ) ^ t * a = a ^ (1 - t) * (2 * a) ^ t := by
      rw [Real.mul_rpow (by norm_num) ha.le]
      have heq := Real.rpow_add ha (1 - t) t
      have hexp : (1 - t) + t = 1 := by ring
      rw [hexp, Real.rpow_one] at heq
      calc
        (2 : ℝ) ^ t * a = (2 : ℝ) ^ t * (a ^ (1 - t) * a ^ t) :=
          congrArg (fun z => (2 : ℝ) ^ t * z) heq
        _ = a ^ (1 - t) * ((2 : ℝ) ^ t * a ^ t) := by ring
    _ ≤ a ^ (1 - t) * b ^ t :=
      mul_le_mul_of_nonneg_left hr (Real.rpow_nonneg ha.le _)

end ContingencyTables.PublishedInputs

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_GridCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite cut-face cover of the interpolation shell

The continuous shell in the conductance argument is covered, except for
the null grid hyperplanes, by the finite collection of interior cut-face
tubes. No exterior faces or segment general-position hypotheses occur.
-/

namespace ContingencyTables.GridBoundary

open MeasureTheory

variable {I : Type*} [Fintype I] [DecidableEq I]

def Cube (K : ℕ) (x : I → ℝ) : Prop := ∀ j, 0 < x j ∧ x j < (K : ℝ)

omit [Fintype I] [DecidableEq I] in
theorem interpolation_short {K : ℕ} (x y : I → ℝ) (t : ℝ)
    (hx : Cube K x) (hy : Cube K y) (ht : 0 < t) (ht₁ : t < 1) :
    Cube K (fun j => (1 - t) * x j + t * y j) ∧
      ∀ j, |((1 - t) * x j + t * y j) - x j| < t * K := by
  constructor
  · intro j
    have hxt := mul_pos (sub_pos.mpr ht₁) (hx j).1
    have hyt := mul_pos ht (hy j).1
    have hxu := mul_lt_mul_of_pos_left (hx j).2 (sub_pos.mpr ht₁)
    have hyu := mul_lt_mul_of_pos_left (hy j).2 ht
    constructor <;> nlinarith
  · intro j
    have hdiff : |y j - x j| < (K : ℝ) := by
      apply abs_lt.mpr
      constructor <;> linarith [(hx j).1, (hx j).2, (hy j).1, (hy j).2]
    have heq : (1 - t) * x j + t * y j - x j = t * (y j - x j) := by ring
    rw [heq, abs_mul, abs_of_pos ht]
    exact mul_lt_mul_of_pos_left hdiff ht

omit [DecidableEq I] in
/-- The only excluded points lie on countably many null hyperplanes. -/
theorem ae_off_grid : ∀ᵐ z : I → ℝ ∂volume, ∀ j (k : ℤ), z j ≠ (k : ℝ) := by
  apply ae_all_iff.mpr
  intro j
  apply ae_all_iff.mpr
  intro k
  simpa only [MeasureTheory.volume_pi] using
    (MeasureTheory.Measure.ae_eval_ne (fun _ : I => (volume : Measure ℝ)) j (k : ℝ))

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_GridMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Continuous mass and weighted grid cuts

Unit bins have disjoint interiors and exact volume one. Their continuous
mass is compared with the discrete weights, and the finite shell cover
converts interpolation gain into a weighted cut-face sum.
-/

namespace ContingencyTables.GridBoundary

open MeasureTheory
open scoped BigOperators

variable {q K : ℕ}

def ambientBox (q K : ℕ) : Set (Fin q → ℝ) :=
  Set.Icc (fun _ => 0) (fun _ => (K : ℝ))

theorem cube_closure : closure {x : Fin q → ℝ | Cube K x} ⊆ ambientBox q K := by
  apply isClosed_Icc.closure_subset_iff.mpr
  intro x hx
  exact ⟨fun j => (hx j).1.le, fun j => (hx j).2.le⟩

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_MetropolisChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite weighted Metropolis chain

The holding probability, stationary law, and cut flow are proved from
positive weights, symmetric proposals, and the proposal-degree bound.
Only the final Poincaré consequence uses the explicit published Cheeger input.
-/

namespace ContingencyTables.MetropolisChain

open scoped BigOperators Classical

noncomputable section

variable {X : Type*} [Fintype X] [Nonempty X]

def move (w : X → ℝ) (Adj : X → X → Prop) (β : ℝ) (x y : X) : ℝ :=
  if Adj x y then β * min 1 (w y / w x) else 0

theorem accept_mass (a b : ℝ) (ha : 0 < a) :
    a * min 1 (b / a) = min a b := by
  rw [mul_min_of_nonneg _ _ ha.le, mul_one, mul_div_cancel₀ _ (ne_of_gt ha)]

omit [Fintype X] [Nonempty X] in
theorem move_nonnegative (w : X → ℝ) (hw : ∀ x, 0 < w x)
    (Adj : X → X → Prop) (β : ℝ) (hβ : 0 ≤ β) (x y : X) :
    0 ≤ move w Adj β x y := by
  unfold move
  split_ifs
  · exact mul_nonneg hβ (le_min (by norm_num) (div_nonneg (hw y).le (hw x).le))
  · exact le_rfl

omit [Nonempty X] in
theorem move_row_bound (w : X → ℝ) (Adj : X → X → Prop) (β : ℝ) (hβ : 0 ≤ β)
    (D : ℕ) (hdegree : ∀ x, (Finset.univ.filter (Adj x)).card ≤ D)
    (hproposal : (D : ℝ) * β ≤ 1 / 2) (x : X) : ∑ y, move w Adj β x y ≤ 1 / 2 := by
  calc
    _ ≤ ∑ y : X, if Adj x y then β else 0 := by
      apply Finset.sum_le_sum
      intro y _
      unfold move
      split_ifs
      · exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hβ).trans_eq (mul_one β)
      · exact le_rfl
    _ = ((Finset.univ.filter (Adj x)).card : ℝ) * β := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ (D : ℝ) * β := mul_le_mul_of_nonneg_right (by exact_mod_cast hdegree x) hβ
    _ ≤ 1 / 2 := hproposal

end

end ContingencyTables.MetropolisChain

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_Padding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Padding and the successful-table bijection

Padding a designated rectangle by a fixed amount gives a bijection from
original tables to enlarged-margin tables whose entries dominate the
padding. Each successful joint object therefore yields exactly one table.
-/

namespace ContingencyTables

open Finset
open scoped Classical

variable {I J : Type*} [Fintype I] [Fintype J]

def paddedRows (r : I → ℕ) (P : I → J → ℕ) : I → ℕ := fun i => r i + ∑ j, P i j
def paddedColumns (c : J → ℕ) (P : I → J → ℕ) : J → ℕ := fun j => c j + ∑ i, P i j

section SuccessFraction

variable [DecidableEq I] [DecidableEq J]

def largePadding (K : Finset (I × J)) (L : ℕ) : I → J → ℕ :=
  fun i j => if (i, j) ∈ K then L else 0

end SuccessFraction

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ResidualMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact correction by a finite residual mixture

Finite probability arithmetic gives the residual correction used in exact
sampling. The construction is that of Göbel, Liu, Manurangsi and Pappik,
*Perfect sampling from rapidly mixing Markov chains*, arXiv:2410.00882v2
(2024), §3.1, Algorithm 1 and Theorem 6.

All probabilities are rational, as required for the finite fair-bit sampler.
-/

open scoped BigOperators

namespace ContingencyTables.ResidualMixture

variable {α : Type*} [Fintype α]

variable [Nonempty α]

/-- The integer numerator in equation `eq:residual-integers` of 200-01.
Here `Q = 2^R`, `T = 2^D`, and `a x` is the tabulated dyadic numerator. -/
def residualNumerator (Q T : ℤ) (a : α → ℤ) (x : α) : ℤ :=
  Q * T - (Fintype.card α : ℤ) * (T - 1) * a x

omit [Nonempty α] in
/-- The residual integer weights have the exact required total. -/
lemma residualNumerator_total (Q T : ℤ) (a : α → ℤ) (ha : ∑ x, a x = Q) :
    ∑ x, residualNumerator Q T a x = (Fintype.card α : ℤ) * Q := by
  simp only [residualNumerator, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, ha]
  ring

end ContingencyTables.ResidualMixture

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Parameter arithmetic for the samplers

The manuscript's padding and rare tabulation estimates give explicit
inequalities for successful unpadding and expected correction cost.
-/

namespace ContingencyTables

open scoped BigOperators

theorem padding_error_le_half (d s : ℕ) (hd : 14 ≤ d) (hs : s ≤ d) :
    (s : ℝ) * (4 * (d : ℝ) ^ 12 * (d : ℝ) ^ 3 / (d : ℝ) ^ 20) ≤ 1 / 2 := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd₁₄ : (14 : ℝ) ≤ d := by exact_mod_cast hd
  have hs' : (s : ℝ) ≤ d := by exact_mod_cast hs
  have hfour : (8 : ℝ) ≤ (d : ℝ) ^ 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 14) hd₁₄ 4
    norm_num at h
    linarith
  have htwenty : (d : ℝ) ^ 20 = (d : ℝ) ^ 16 * (d : ℝ) ^ 4 := by ring
  have hpow : (0 : ℝ) ≤ (d : ℝ) ^ 16 := by positivity
  have hlarge := mul_le_mul_of_nonneg_left hfour hpow
  have hnum : 8 * (s : ℝ) * (d : ℝ) ^ 12 * (d : ℝ) ^ 3 ≤ (d : ℝ) ^ 20 := by
    calc
      _ ≤ 8 * (d : ℝ) * (d : ℝ) ^ 12 * (d : ℝ) ^ 3 := by gcongr
      _ = 8 * (d : ℝ) ^ 16 := by ring
      _ ≤ (d : ℝ) ^ 20 := by rw [htwenty]; linarith
  rw [← mul_div_assoc, div_le_iff₀ (pow_pos hd₀ 20)]
  nlinarith

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer bin widths for dense blocks

The free-cell width is the actual integer quotient `floor(s/B)`, where
`s=min(Rᵢ,Pⱼ)`. Large margins give the two-sided scale comparison used in
the dense rejection sampler.
-/

namespace ContingencyTables.DenseAffine

theorem integer_width_bounds (s B : ℕ) (hB : 0 < B) (hs : 2 * B ≤ s) :
    (s : ℝ) / (2 * B) ≤ (s / B : ℕ) ∧ (s / B : ℕ) ≤ (s : ℝ) / B := by
  have hq : 0 < s / B := Nat.div_pos (by omega) hB
  have hmod := Nat.mod_lt s hB
  have hid := Nat.mod_add_div s B
  have hscale : s ≤ 2 * B * (s / B) := by nlinarith
  constructor
  · apply (div_le_iff₀ (show (0 : ℝ) < 2 * B by positivity)).mpr
    have hscale' : (s : ℝ) ≤ 2 * (B : ℝ) * (s / B : ℕ) := by exact_mod_cast hscale
    nlinarith
  · exact Nat.cast_div_le

theorem dense_width_positive (d s : ℕ) (hd : 14 ≤ d) (hs : d ^ 12 ≤ s) :
    0 < s / d ^ 8 := by
  have hd₀ : 0 < d := by omega
  have hpow : d ^ 8 ≤ d ^ 12 := by
    apply Nat.pow_le_pow_right (by omega : 1 ≤ d)
    decide
  exact Nat.div_pos (hpow.trans hs) (pow_pos hd₀ _)

theorem dense_width_bounds (d s : ℕ) (hd : 14 ≤ d) (hs : d ^ 12 ≤ s) :
    (s : ℝ) / (2 * (d : ℝ) ^ 8) ≤ (s / d ^ 8 : ℕ) ∧
      (s / d ^ 8 : ℕ) ≤ (s : ℝ) / (d : ℝ) ^ 8 := by
  have hd₀ : 0 < d := by omega
  have hfour : 2 ≤ d ^ 4 := by
    have h := Nat.le_self_pow (show 4 ≠ 0 by decide) d
    omega
  have hscale : 2 * d ^ 8 ≤ d ^ 12 := by
    calc
      2 * d ^ 8 ≤ d ^ 4 * d ^ 8 := Nat.mul_le_mul_right _ hfour
      _ = d ^ 12 := by ring
  simpa only [Nat.cast_pow] using
    integer_width_bounds s (d ^ 8) (pow_pos hd₀ _) (hscale.trans hs)

/-- The product `A*d/B=d⁻³` is at most one with the actual integer
parameter choices. This controls the density within each unit bin. -/
theorem dense_exponent_change_scale (d : ℕ) (hd : 14 ≤ d) :
    (d : ℝ) ^ 4 * d / (d : ℝ) ^ 8 ≤ 1 := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd₁ : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  apply (div_le_one (pow_pos hd₀ _)).mpr
  calc
    (d : ℝ) ^ 4 * d = (d : ℝ) ^ 5 := by ring
    _ ≤ (d : ℝ) ^ 8 := pow_le_pow_right₀ hd₁ (by decide)

end ContingencyTables.DenseAffine

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCutParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical interpolation parameters of the dense bin chain -/

namespace ContingencyTables.GridBoundary

noncomputable def denseInterpolation (d K : ℕ) : ℝ := 1 / (4 * (d : ℝ) * K)

theorem denseInterpolation_bounds (d K q : ℕ) (hd : 14 ≤ d) (hK : 1 ≤ K) (hq : q ≤ d) :
    0 < denseInterpolation d K ∧ denseInterpolation d K < 1 ∧
      denseInterpolation d K * K ≤ 1 / 4 ∧
      (q - 1 : ℕ) * (2 * (denseInterpolation d K * K)) ≤ (1 / 2 : ℝ) := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd₁ : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hK₀ : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hK₁ : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have heq : denseInterpolation d K * K = 1 / (4 * (d : ℝ)) := by
    unfold denseInterpolation
    field_simp
  refine ⟨by unfold denseInterpolation; positivity, ?_, ?_, ?_⟩
  · unfold denseInterpolation
    apply (div_lt_one (by positivity)).mpr
    nlinarith
  · rw [heq]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  · rw [heq]
    have hqd : ((q - 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast (Nat.sub_le q 1).trans hq
    calc
      _ ≤ (d : ℝ) * (2 * (1 / (4 * (d : ℝ)))) := by gcongr
      _ = 1 / 2 := by field_simp; ring

theorem two_rpow_gain (t : ℝ) (ht : 0 ≤ t) : t / 2 ≤ (2 : ℝ) ^ t - 1 := by
  have hl := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at hl
  have he := Real.add_one_le_exp (Real.log 2 * t)
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith [mul_le_mul_of_nonneg_right hl ht]

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Free coordinates of a dense completion block

`none` denotes the pivot row or column. The free coordinates are the other
cells. These are the manuscript's actual affine completion formulas; the
row and column constraints hold identically, and feasible tables are
uniquely determined by their free cells.
-/

namespace ContingencyTables.DenseAffine

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

theorem table_unique (X Y : Option I → Option J → ℝ)
    (hrows : ∀ i, ∑ j, X i j = ∑ j, Y i j)
    (hcols : ∀ j, ∑ i, X i j = ∑ i, Y i j)
    (hfree : ∀ i j, X (some i) (some j) = Y (some i) (some j)) : X = Y := by
  have hr (i : I) : X (some i) none = Y (some i) none := by
    have h := hrows (some i)
    simp only [Fintype.sum_option, hfree] at h
    linarith
  have hc (j : J) : X none (some j) = Y none (some j) := by
    have h := hcols (some j)
    simp only [Fintype.sum_option, hfree] at h
    linarith
  have hnn : X none none = Y none none := by
    have h := hrows none
    simp only [Fintype.sum_option, hc] at h
    linarith
  funext i j
  cases i <;> cases j
  · exact hnn
  · exact hc _
  · exact hr _
  · exact hfree _ _

end ContingencyTables.DenseAffine

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coefficients of normalized dense entries

Reordering maximum margins to the pivot makes each contributing free-cell
scale no larger than the dependent-cell scale. Thus every normalized
coefficient is bounded by `1/B`, as required by the actual penalty proof.
-/

namespace ContingencyTables.DenseAffine

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def entryOffset (R : Option I → ℝ) (P : Option J → ℝ) : Option I × Option J → ℝ
  | (some _, some _) => 0
  | (some i, none) => R (some i)
  | (none, some j) => P (some j)
  | (none, none) => R none - ∑ j, P (some j)

def entryCoeff (w : I → J → ℝ) : (Option I × Option J) → (I × J) → ℝ
  | (some i, some j), p => if p = (i, j) then w i j else 0
  | (some i, none), p => if p.1 = i then -w p.1 p.2 else 0
  | (none, some j), p => if p.2 = j then -w p.1 p.2 else 0
  | (none, none), p => w p.1 p.2

def cellScale (R : Option I → ℝ) (P : Option J → ℝ)
    (g : Option I × Option J) : ℝ := min (R g.1) (P g.2)

omit [Fintype I] [Fintype J] in
theorem entryCoeff_bound (R : Option I → ℝ) (P : Option J → ℝ) (w : I → J → ℝ)
    (B : ℝ) (hB : 0 < B)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hw : ∀ i j, 0 ≤ w i j)
    (hwidth : ∀ i j, w i j ≤ cellScale R P (some i, some j) / B)
    (hscale : ∀ g, 0 ≤ cellScale R P g) (g : Option I × Option J) (p : I × J) :
    |entryCoeff w g p| ≤ cellScale R P g / B := by
  rcases g with ⟨i, j⟩
  cases i with
  | none =>
    cases j with
    | none =>
      simp only [entryCoeff, abs_of_nonneg (hw p.1 p.2)]
      exact (hwidth p.1 p.2).trans (div_le_div_of_nonneg_right
        (min_le_min (hRmax p.1) (hPmax p.2)) hB.le)
    | some j =>
      by_cases hp : p.2 = j
      · simp only [entryCoeff, hp, ite_true, if_true, abs_neg, abs_of_nonneg (hw p.1 j)]
        exact (hwidth p.1 j).trans (div_le_div_of_nonneg_right
          (min_le_min_right _ (hRmax p.1)) hB.le)
      · simp only [entryCoeff, hp, ite_false, abs_zero]
        exact div_nonneg (hscale _) hB.le
  | some i =>
    cases j with
    | none =>
      by_cases hp : p.1 = i
      · simp only [entryCoeff, hp, ite_true, if_true, abs_neg, abs_of_nonneg (hw i p.2)]
        exact (hwidth i p.2).trans (div_le_div_of_nonneg_right
          (min_le_min_left _ (hPmax p.2)) hB.le)
      · simp only [entryCoeff, hp, ite_false, abs_zero]
        exact div_nonneg (hscale _) hB.le
    | some j =>
      by_cases hp : p = (i, j)
      · simp only [entryCoeff, hp, ite_true, if_true, abs_of_nonneg (hw i j)]
        exact hwidth i j
      · simp only [entryCoeff, hp, ite_false, abs_zero]
        exact div_nonneg (hscale _) hB.le

omit [Fintype I] [Fintype J] in
theorem normalized_coeff_bound (R : Option I → ℝ) (P : Option J → ℝ)
    (w : I → J → ℝ) (B : ℝ) (hB : 0 < B)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hw : ∀ i j, 0 ≤ w i j)
    (hwidth : ∀ i j, w i j ≤ cellScale R P (some i, some j) / B)
    (hscale : ∀ g, 0 < cellScale R P g) (g : Option I × Option J) (p : I × J) :
    |entryCoeff w g p / cellScale R P g| ≤ 1 / B := by
  rw [abs_div, abs_of_pos (hscale g)]
  calc
    _ ≤ (cellScale R P g / B) / cellScale R P g :=
      div_le_div_of_nonneg_right (entryCoeff_bound R P w B hB hRmax hPmax hw hwidth
        (fun g => (hscale g).le) g p) (hscale g).le
    _ = 1 / B := by field_simp [ne_of_gt (hscale g), ne_of_gt hB]

end ContingencyTables.DenseAffine

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Regularity of the dense sampler's actual penalty

The natural margins, maximum pivots, integer quotient widths, and actual
parameters A=d⁴, B=d⁸ determine the penalty. Its regularity and scaled
change bounds follow from the normalized affine coefficients.
-/

namespace ContingencyTables.DenseAffine

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def denseWidth (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ) (i : I) (j : J) : ℝ :=
  ((min (R (some i)) (P (some j)) / d ^ 8 : ℕ) : ℝ)

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem dense_cellScale_pos (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (g : Option I × Option J) :
    0 < cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g := by
  change 0 < min (R g.1 : ℝ) (P g.2 : ℝ)
  apply lt_min
  · exact_mod_cast (lt_of_lt_of_le (pow_pos (show 0 < d by omega) _) (hR g.1))
  · exact_mod_cast (lt_of_lt_of_le (pow_pos (show 0 < d by omega) _) (hP g.2))

omit [Fintype I] [Fintype J] in
theorem dense_normalized_coeff_bound (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (g : Option I × Option J) (p : I × J) :
    |entryCoeff (denseWidth R P d) g p /
      cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g| ≤ 1 / (d : ℝ) ^ 8 := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  apply normalized_coeff_bound _ _ _ _ (by positivity)
    (fun i => by exact_mod_cast hRmax i) (fun j => by exact_mod_cast hPmax j)
    (fun i j => Nat.cast_nonneg _)
    (fun i j => ?_) (dense_cellScale_pos R P d hd hR hP) g p
  have hmin : d ^ 12 ≤ min (R (some i)) (P (some j)) := le_min (hR _) (hP _)
  simpa only [denseWidth, cellScale, Nat.cast_min] using
    (dense_width_bounds d _ hd hmin).2

end ContingencyTables.DenseAffine

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RealCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Real completions with prescribed lower bounds

The dense geometric argument needs one strictly feasible normalized table.
Residual nonnegative real margins are completed by a rank-one table; this
is enough for the analytic interior-point argument and makes no algorithmic
claim about integral flow preprocessing.
-/

namespace ContingencyTables

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

theorem real_table_exists (r : I → ℝ) (c : J → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hc : ∀ j, 0 ≤ c j)
    (htotal : ∑ i, r i = ∑ j, c j) :
    ∃ X : I → J → ℝ, (∀ i j, 0 ≤ X i j) ∧
      (∀ i, ∑ j, X i j = r i) ∧ (∀ j, ∑ i, X i j = c j) := by
  by_cases hzero : ∑ i, r i = 0
  · have hr₀ (i : I) : r i = 0 := by
      have h := Finset.single_le_sum (fun a _ => hr a) (Finset.mem_univ i)
      linarith [hr i]
    have hc₀ (j : J) : c j = 0 := by
      have h := Finset.single_le_sum (fun a _ => hc a) (Finset.mem_univ j)
      rw [← htotal, hzero] at h
      linarith [hc j]
    exact ⟨fun _ _ => 0, by simp, by simp [hr₀], by simp [hc₀]⟩
  · have hN : 0 < ∑ i, r i := lt_of_le_of_ne
      (Finset.sum_nonneg fun i _ => hr i) (Ne.symm hzero)
    refine ⟨fun i j => r i * c j / (∑ i, r i), ?_, ?_, ?_⟩
    · intro i j
      exact div_nonneg (mul_nonneg (hr i) (hc j)) hN.le
    · intro i
      rw [← Finset.sum_div, ← Finset.mul_sum, ← htotal]
      field_simp
    · intro j
      rw [← Finset.sum_div, ← Finset.sum_mul]
      field_simp

theorem lower_bounded_real_table (r : I → ℝ) (c : J → ℝ) (lower : I → J → ℝ)
    (htotal : ∑ i, r i = ∑ j, c j)
    (hrow : ∀ i, ∑ j, lower i j ≤ r i) (hcol : ∀ j, ∑ i, lower i j ≤ c j) :
    ∃ X : I → J → ℝ, (∀ i j, lower i j ≤ X i j) ∧
      (∀ i, ∑ j, X i j = r i) ∧ (∀ j, ∑ i, X i j = c j) := by
  let r₀ : I → ℝ := fun i => r i - ∑ j, lower i j
  let c₀ : J → ℝ := fun j => c j - ∑ i, lower i j
  have ht : ∑ i, r₀ i = ∑ j, c₀ j := by
    simp only [r₀, c₀, Finset.sum_sub_distrib, htotal]
    rw [Finset.sum_comm (f := lower)]
  obtain ⟨Y, hY, hR, hC⟩ := real_table_exists r₀ c₀
    (fun i => sub_nonneg.mpr (hrow i)) (fun j => sub_nonneg.mpr (hcol j)) ht
  refine ⟨fun i j => lower i j + Y i j, ?_, ?_, ?_⟩
  · intro i j
    linarith [hY i j]
  · intro i
    rw [Finset.sum_add_distrib, hR]
    dsimp [r₀]
    ring
  · intro j
    rw [Finset.sum_add_distrib, hC]
    dsimp [c₀]
    ring

/-- Assigning `min(rᵢ,cⱼ)/(2d)` to every cell leaves nonnegative residual
margins whenever each dimension is at most `d`. -/
theorem strict_real_completion (r : I → ℝ) (c : J → ℝ) (d : ℝ)
    (hd : 0 < d) (hr : ∀ i, 0 ≤ r i) (hc : ∀ j, 0 ≤ c j)
    (hrows : (Fintype.card I : ℝ) ≤ d) (hcols : (Fintype.card J : ℝ) ≤ d)
    (htotal : ∑ i, r i = ∑ j, c j) :
    ∃ X : I → J → ℝ, (∀ i j, min (r i) (c j) / (2 * d) ≤ X i j) ∧
      (∀ i, ∑ j, X i j = r i) ∧ (∀ j, ∑ i, X i j = c j) := by
  apply lower_bounded_real_table r c (fun i j => min (r i) (c j) / (2 * d)) htotal
  · intro i
    calc
      (∑ j, min (r i) (c j) / (2 * d)) ≤ ∑ _j : J, r i / (2 * d) := by
        apply Finset.sum_le_sum
        intro j _
        exact div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
      _ = Fintype.card J * (r i / (2 * d)) := by simp
      _ ≤ d * (r i / (2 * d)) := mul_le_mul_of_nonneg_right hcols
        (div_nonneg (hr i) (by positivity))
      _ ≤ r i := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (show 0 < 2 * d by positivity)).mpr
        nlinarith [hr i]
  · intro j
    calc
      (∑ i, min (r i) (c j) / (2 * d)) ≤ ∑ _i : I, c j / (2 * d) := by
        apply Finset.sum_le_sum
        intro i _
        exact div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = Fintype.card I * (c j / (2 * d)) := by simp
      _ ≤ d * (c j / (2 * d)) := mul_le_mul_of_nonneg_right hrows
        (div_nonneg (hc j) (by positivity))
      _ ≤ c j := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (show 0 < 2 * d by positivity)).mpr
        nlinarith [hc j]

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Feasible region and interior point of the dense block

These statements use the actual integer margins and quotient widths. Every
feasible real completion lies in the declared scaled cube, and one scaled
completion has normalized slack at least `1/(2d)` in every cell.
-/

namespace ContingencyTables.DenseAffine

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem denseWidth_pos (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j) (i : I) (j : J) :
    0 < denseWidth R P d i j := by
  unfold denseWidth
  exact_mod_cast dense_width_positive d (min (R (some i)) (P (some j))) hd
    (le_min (hR _) (hP _))

end ContingencyTables.DenseAffine

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseLocalGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Feasible bins and exponent bounds for dense rejection

These bounds use the actual quotient widths and margin-derived penalty.
In particular, every bin containing a feasible point has weight one.
-/

namespace ContingencyTables.GridBoundary

open scoped BigOperators

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q K : ℕ}

theorem denseGridSize_pos (d : ℕ) (hd : 14 ≤ d) : 1 ≤ 4 * d ^ 8 := by
  have hd₀ : 0 < d := by omega
  exact Nat.succ_le_of_lt (Nat.mul_pos (by decide) (pow_pos hd₀ _))

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseMixing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical Poincaré and point mixing for the dense bin sampler -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators

noncomputable section

theorem dense_min_mass_exponential (d q : ℕ) (hd : 14 ≤ d) (hq : q ≤ d) :
    Real.exp (-(d : ℝ) ^ 10) ≤
      (2 : ℝ) ^ (-(4 * (d : ℝ) ^ 5)) / (4 * (d : ℝ) ^ 8) ^ q := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd₁ : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hk : (0 : ℝ) < 4 * (d : ℝ) ^ 8 := by positivity
  have hl₂ : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlK : Real.log (4 * (d : ℝ) ^ 8) ≤ 4 * (d : ℝ) ^ 8 := by
    have h := Real.log_le_sub_one_of_pos hk
    linarith
  have hq' : (q : ℝ) ≤ d := by exact_mod_cast hq
  have hp : (d : ℝ) ^ 5 ≤ (d : ℝ) ^ 9 := pow_le_pow_right₀ hd₁ (by decide)
  have hsum : 4 * (d : ℝ) ^ 5 * Real.log 2 +
      (q : ℝ) * Real.log (4 * (d : ℝ) ^ 8) ≤ (d : ℝ) ^ 10 := by
    calc
      _ ≤ 4 * (d : ℝ) ^ 5 + (q : ℝ) * (4 * (d : ℝ) ^ 8) := by
        have h1 := mul_le_mul_of_nonneg_left hl₂ (show (0 : ℝ) ≤ 4 * (d : ℝ) ^ 5 by positivity)
        have h2 := mul_le_mul_of_nonneg_left hlK (show (0 : ℝ) ≤ q by positivity)
        linarith
      _ ≤ 4 * (d : ℝ) ^ 9 + d * (4 * (d : ℝ) ^ 8) := by gcongr
      _ = 8 * (d : ℝ) ^ 9 := by ring
      _ ≤ d * (d : ℝ) ^ 9 := by
        apply mul_le_mul_of_nonneg_right (by exact_mod_cast (show 8 ≤ d by omega)) (by positivity)
      _ = _ := by ring
  have hpow : (4 * (d : ℝ) ^ 8) ^ q =
      Real.exp ((q : ℝ) * Real.log (4 * (d : ℝ) ^ 8)) := by
    rw [Real.exp_nat_mul, Real.exp_log hk]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), hpow, ← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem dense_mixing_time_arithmetic (d q h : ℕ) (hd : 14 ≤ d) (hq : q ≤ d) :
    Real.exp (-((d ^ 50 * (h + 1) ^ 2 : ℕ) : ℝ) / (d : ℝ) ^ 32) /
        ((2 : ℝ) ^ (-(4 * (d : ℝ) ^ 5)) / (4 * (d : ℝ) ^ 8) ^ q) ≤
      (2 : ℝ) ^ (-(4 * ((h : ℝ) + d))) := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have h₉ : 8 ≤ d ^ 9 := (show 8 ≤ d by omega).trans (Nat.le_self_pow (by decide) d)
  have h₈ : 2 ≤ d ^ 8 := (show 2 ≤ d by omega).trans (Nat.le_self_pow (by decide) d)
  have h₁₀ : 8 * d ≤ d ^ 10 := by
    calc
      _ ≤ d ^ 9 * d := Nat.mul_le_mul_right d h₉
      _ = _ := by ring
  have h₁₈ : 2 * d ^ 10 ≤ d ^ 18 := by
    calc
      _ ≤ d ^ 8 * d ^ 10 := Nat.mul_le_mul_right _ h₈
      _ = _ := by ring
  have hbase : (d : ℝ) ^ 10 + 4 * d + 4 ≤ (d : ℝ) ^ 18 := by
    exact_mod_cast (show d ^ 10 + 4 * d + 4 ≤ d ^ 18 by omega)
  have hh : (0 : ℝ) ≤ h := by positivity
  have hquad : (h : ℝ) + 1 ≤ ((h : ℝ) + 1) ^ 2 := by nlinarith
  have htime : (d : ℝ) ^ 10 + 4 * ((h : ℝ) + d) ≤
      (d : ℝ) ^ 18 * ((h : ℝ) + 1) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hbase (show 0 ≤ (h : ℝ) + 1 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hquad (show (0 : ℝ) ≤ (d : ℝ) ^ 18 by positivity)
    nlinarith [show (0 : ℝ) ≤ (d : ℝ) ^ 10 * h by positivity]
  calc
    _ ≤ Real.exp (-((d ^ 50 * (h + 1) ^ 2 : ℕ) : ℝ) / (d : ℝ) ^ 32) /
        Real.exp (-(d : ℝ) ^ 10) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _)
        (dense_min_mass_exponential d q hd hq)
    _ = Real.exp (-(d : ℝ) ^ 18 * ((h : ℝ) + 1) ^ 2 + (d : ℝ) ^ 10) := by
      rw [← Real.exp_sub]
      congr 1
      push_cast
      field_simp
      ring
    _ ≤ Real.exp (-(4 * ((h : ℝ) + d))) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ (2 : ℝ) ^ (-(4 * ((h : ℝ) + d))) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      apply Real.exp_le_exp.mpr
      have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      nlinarith

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseLayerArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical finite-layer sum for dense rejection -/

namespace ContingencyTables.DenseAffine

open scoped BigOperators

theorem dense_layer_sum (d : ℕ) (hd : 14 ≤ d) (N : ℕ) :
    4 * (∑ j ∈ Finset.range N, (2 : ℝ) ^ (-(j : ℝ)) *
      Real.exp (2 * (d : ℝ) ^ 2 * ((d : ℝ) / (d : ℝ) ^ 8 + ((j : ℝ) + 1) / (d : ℝ) ^ 4))) ≤ 16 := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  let a := 2 / (d : ℝ) ^ 2
  let b := 2 / (d : ℝ) ^ 5
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have htwo : (16 : ℝ) ≤ (d : ℝ) ^ 2 := by
    exact_mod_cast (show 16 ≤ d ^ 2 from
      (by norm_num : 16 ≤ 4 ^ 2).trans (Nat.pow_le_pow_left (by omega : 4 ≤ d) 2))
  have hfive : (16 : ℝ) ≤ (d : ℝ) ^ 5 := by
    exact_mod_cast (show 16 ≤ d ^ 5 from
      (by norm_num : 16 ≤ 4 ^ 5).trans (Nat.pow_le_pow_left (by omega : 4 ≤ d) 5))
  have ha₈ : a ≤ 1 / 8 := by
    dsimp [a]
    apply (div_le_iff₀ (pow_pos hd₀ 2)).mpr
    nlinarith
  have hb₈ : b ≤ 1 / 8 := by
    dsimp [b]
    apply (div_le_iff₀ (pow_pos hd₀ 5)).mpr
    nlinarith
  have hquarter : Real.exp (1 / 4 : ℝ) ≤ 4 / 3 := by
    have h := Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
    norm_num at h ⊢
    exact h
  have hexp : Real.exp (a + b) ≤ 4 / 3 :=
    (Real.exp_le_exp.mpr (by linarith : a + b ≤ 1 / 4)).trans hquarter
  have hratio : Real.exp a / 2 ≤ 2 / 3 := by
    have h := (Real.exp_le_exp.mpr (by linarith : a ≤ 1 / 4)).trans hquarter
    linarith
  have hterm (j : ℕ) : (2 : ℝ) ^ (-(j : ℝ)) *
      Real.exp (2 * (d : ℝ) ^ 2 * ((d : ℝ) / (d : ℝ) ^ 8 + ((j : ℝ) + 1) / (d : ℝ) ^ 4)) ≤
      (4 / 3 : ℝ) * (2 / 3 : ℝ) ^ j := by
    have heq : 2 * (d : ℝ) ^ 2 * ((d : ℝ) / (d : ℝ) ^ 8 + ((j : ℝ) + 1) / (d : ℝ) ^ 4) =
        (a + b) + (j : ℝ) * a := by
      dsimp [a, b]
      field_simp
      ring
    calc
      _ = Real.exp (a + b) * (Real.exp a / 2) ^ j := by
        rw [heq, Real.exp_add, Real.exp_nat_mul, Real.rpow_neg (by norm_num), Real.rpow_natCast,
          div_pow]
        ring
      _ ≤ _ := mul_le_mul hexp (pow_le_pow_left₀ (by positivity) hratio j)
        (by positivity) (by norm_num)
  have hgeom : (∑ j ∈ Finset.range N, (2 / 3 : ℝ) ^ j) ≤ 3 := by
    have h := geom_sum_mul_neg (2 / 3 : ℝ) N
    have hp : 0 ≤ (2 / 3 : ℝ) ^ N := by positivity
    nlinarith
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range N) => hterm j)
  rw [← Finset.mul_sum] at hsum
  nlinarith

end ContingencyTables.DenseAffine

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseRegionVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inner-polytope and penalty-sublevel volume for the actual margins -/

namespace ContingencyTables.DenseAffine

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def normalizedOffset (R : Option I → ℕ) (P : Option J → ℕ) (g : Option I × Option J) : ℝ :=
  entryOffset (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g /
    cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g

def normalizedCoeff (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (g : Option I × Option J) (p : I × J) : ℝ :=
  entryCoeff (denseWidth R P d) g p /
    cellScale (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) g

theorem dense_inner_contraction (d : ℕ) (hd : 14 ≤ d) (q : ℕ) (hq : q ≤ d) :
    0 ≤ 4 * (d : ℝ) ^ 2 / (d : ℝ) ^ 8 ∧
    4 * (d : ℝ) ^ 2 / (d : ℝ) ^ 8 ≤ 1 ∧
    (1 / 2 : ℝ) ≤ (1 - 4 * (d : ℝ) ^ 2 / (d : ℝ) ^ 8) ^ q := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd₁ : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  let α := 4 * (d : ℝ) ^ 2 / (d : ℝ) ^ 8
  have hα : 0 ≤ α := by positivity
  have hp : 8 * d ^ 3 ≤ d ^ 8 := by
    have hfive : 8 ≤ d ^ 5 := (show 8 ≤ d by omega).trans (Nat.le_self_pow (by decide) d)
    calc
      _ ≤ d ^ 5 * d ^ 3 := Nat.mul_le_mul_right _ hfive
      _ = _ := by ring
  have hsmall : (d : ℝ) * α ≤ 1 / 2 := by
    have hp' : 8 * (d : ℝ) ^ 3 ≤ (d : ℝ) ^ 8 := by exact_mod_cast hp
    have heq : (d : ℝ) * α = 4 * (d : ℝ) ^ 3 / (d : ℝ) ^ 8 := by dsimp [α]; ring
    rw [heq]
    apply (div_le_iff₀ (pow_pos hd₀ 8)).mpr
    nlinarith
  have hα₁ : α ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hd₁ hα
    nlinarith
  have hq' : (q : ℝ) ≤ d := by exact_mod_cast hq
  have hbern := one_add_mul_le_pow (a := -α) (by linarith : -2 ≤ -α) q
  have hqα := mul_le_mul_of_nonneg_right hq' hα
  refine ⟨hα, hα₁, ?_⟩
  change (1 / 2 : ℝ) ≤ (1 - α) ^ q
  have heq : 1 + -α = 1 - α := by ring
  rw [heq] at hbern
  nlinarith

end

end ContingencyTables.DenseAffine

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DensityLayers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A finite penalty-layer bound

The actual dense cube has bounded exponent, so a finite layer sum suffices
for its normalizer. This avoids any infinite layer decomposition.
-/

namespace ContingencyTables.DenseWeights

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

def layerSet {X : Type*} (A : ℝ) (p : X → ℝ) (j : ℕ) : Set X :=
  {x | A * p x ≤ (j : ℝ) + 1}

end

end ContingencyTables.DenseWeights

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseReindexedVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Volume-preserving free-coordinate indexing for the dense sampler -/

namespace ContingencyTables.GridBoundary

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

omit [DecidableEq I] [DecidableEq J] in
theorem volume_dense_reindex (e : I × J ≃ Fin q) (S : Set (I × J → ℝ)) :
    volume {x : Fin q → ℝ | (fun p => x (e p)) ∈ S} = volume S := by
  have hm : (MeasurableEquiv.piCongrLeft (fun _ : I × J => ℝ) e.symm :
      (Fin q → ℝ) → (I × J → ℝ)) = (fun x p => x (e p)) := by
    ext x p
    have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : I × J => ℝ) e.symm x (e p)
    simpa only [Equiv.symm_apply_apply] using h
  have h := (volume_measurePreserving_piCongrLeft (fun _ : I × J => ℝ) e.symm).measure_preimage_equiv S
  rw [hm] at h
  exact h

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerFutureSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The integer transport recursion's future square identity

The three new--new removal entries partition by the same resulting pair.
Their coefficients give an exact nonnegative square, without a signature
assumption on the weighted future form.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Matrix
open FactorialSignatures

lemma sum_range_shift (n s : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range (n+s), if s ≤ j then f (j-s) else 0) =
      ∑ k ∈ Finset.range n, f k := by
  rw [Nat.add_comm n s, Finset.sum_range_add]
  have hz : (∑ j ∈ Finset.range s, if s ≤ j then f (j-s) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [show ¬s ≤ j by have := Finset.mem_range.mp hj; omega]
  rw [hz, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  simp

lemma sum_range_truncate (n s : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range (n+s), if j < n then f j else 0) =
      ∑ k ∈ Finset.range n, f k := by
  rw [Finset.sum_range_add]
  have hz : (∑ j ∈ Finset.range s, if n+j < n then f (n+j) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    simp
  rw [hz, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  simp [Finset.mem_range.mp hj]

lemma sum_middle_shift (n : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range (n+3), if 1 ≤ j ∧ j ≤ n+1 then f (j-1) else 0) =
      ∑ k ∈ Finset.range (n+1), f k := by
  rw [show n+3 = (n+2)+1 by omega, Finset.sum_range_succ]
  simp only [show ¬(1 ≤ n+2 ∧ n+2 ≤ n+1) by omega, ite_false, add_zero]
  convert sum_range_shift (n+1) 1 f using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro j hj
  have hjn := Finset.mem_range.mp hj
  simp [show j ≤ n+1 by omega]

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerFutureKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The weighted future-slot kernel

Weights a(M-a) are used inside the finite box 0≤a≤M. The common
nonnegative kernel identifies the integer transport's future correction
matrix.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Matrix
open FactorialSignatures

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Exchange the current and future pairs, leaving all old coordinates
fixed. This makes the common summation domain explicit. -/
def swapPairs : ((I ⊕ Bool) ⊕ Bool) ≃ ((I ⊕ Bool) ⊕ Bool) where
  toFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr b) => .inr b
    | .inr b => .inl (.inr b)
  invFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr b) => .inr b
    | .inr b => .inl (.inr b)
  left_inv x := by rcases x with (i | b) | b <;> rfl
  right_inv x := by rcases x with (i | b) | b <;> rfl

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_SignedTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Signed transport at a leaf and at a paired split

The signed-clique inequality, local potential increment and future quadratic
conservation give the counting paper's fixed-degree transport estimate.
Positivity of weights at unrelated degrees is unnecessary.
-/

namespace ContingencyTables.SignedTransport

open scoped BigOperators
open LinearMap (BilinForm)

section Clique

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The unordered complete exchange energy, expressed as half the ordered
sum, with the manuscript's minimum-endpoint conductance. -/
noncomputable def cliqueEnergy (m W H : I → ℝ) : ℝ :=
  (∑ i, ∑ j, min (W i * m i) (W j * m j) * (H i - H j) ^ 2) / 2

/-- A star uses each unordered edge once, so its energy is at most the
complete unordered exchange energy. -/
lemma star_energy_le (E : I → I → ℝ)
    (hE : ∀ i j, 0 ≤ E i j) (hsymm : ∀ i j, E i j = E j i)
    (hdiag : ∀ i, E i i = 0) (hub : I) :
    ∑ i, E i hub ≤ (∑ i, ∑ j, E i j) / 2 := by
  have hrest : (∑ i ∈ Finset.univ.erase hub, E i hub) ≤
      ∑ i ∈ Finset.univ.erase hub, ∑ j, E i j := by
    apply Finset.sum_le_sum
    intro i _
    exact Finset.single_le_sum (fun j _ => hE i j) (Finset.mem_univ hub)
  rw [Finset.sum_erase (f := fun i => E i hub) _ (hdiag hub)] at hrest
  have htotal := Finset.sum_erase_add Finset.univ (fun i => ∑ j, E i j)
    (Finset.mem_univ hub)
  have hrow : (∑ j, E hub j) = ∑ j, E j hub := by simp_rw [hsymm hub]
  rw [hrow] at htotal
  linarith

end Clique

end ContingencyTables.SignedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerLeafTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer leaf cliques, allowing invalid holes of zero weight -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical
open SignedTransport

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The leaf-clique estimate for raw masses. Invalid removals may have
zero mass; no artificial positive weight is assigned to those vertices. -/
theorem raw_leaf_transport (m h H : I → ℝ) (hm : ∀ i, 0 ≤ m i)
    (hbalance : ∑ i, m i * h i = 0) :
    (∑ i, m i * h i * H i) ^ 2 ≤
      (∑ i, m i * h i ^ 2) * cliqueEnergy m (fun _ => 1) H := by
  cases isEmpty_or_nonempty I with
  | inl he => simp [cliqueEnergy]
  | inr hn =>
    obtain ⟨hub, _, hhub⟩ := Finset.exists_max_image Finset.univ m Finset.univ_nonempty
    have hdemand : (∑ i, m i * h i * (H i-H hub)) = ∑ i, m i * h i * H i := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hbalance,
        zero_mul, sub_zero]
    have hcs : (∑ i, m i * h i * (H i-H hub)) ^ 2 ≤
        (∑ i, m i * h i ^ 2) * ∑ i, m i * (H i-H hub) ^ 2 := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      · intro i _
        exact mul_nonneg (hm i) (sq_nonneg _)
      · intro i _
        exact mul_nonneg (hm i) (sq_nonneg _)
      · intro i _
        exact le_of_eq (by ring)
    have hstar : (∑ i, m i * (H i-H hub) ^ 2) ≤ cliqueEnergy m (fun _ => 1) H := by
      have hs := star_energy_le
        (fun i j => min (m i) (m j) * (H i-H j)^2)
        (fun i j => mul_nonneg (le_min (hm i) (hm j)) (sq_nonneg _))
        (by intro i j; rw [min_comm]; ring) (by intro i; simp) hub
      simp_rw [min_eq_left (hhub _ (Finset.mem_univ _))] at hs
      simpa only [cliqueEnergy, one_mul] using hs
    rw [hdemand] at hcs
    exact hcs.trans (mul_le_mul_of_nonneg_left hstar
      (Finset.sum_nonneg (fun i _ => mul_nonneg (hm i) (sq_nonneg _))))

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerLeafEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual leaf energy as a finite sum of complete displays -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical
open FactorialSignatures

universe u

noncomputable def edgeTerm {C : Type*} (F H : (C → ℕ) → ℝ)
    (e : (C → ℕ) × (C → ℕ)) : ℝ :=
  min (F e.1) (F e.2) * (H e.1-H e.2)^2

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteExchangeDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A literal finite list of all unit-exchange neighbors -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped Classical
open FactorialSignatures

variable {C : Type*} [DecidableEq C]

/-- The ordered pair records the coordinate raised and the coordinate lowered. -/
def exchangeTarget (X : C → ℕ) (i j : C) : C → ℕ := fun a =>
  X a+(if a=i then 1 else 0)-(if a=j then 1 else 0)

noncomputable def exchangeCandidates [Fintype C] (X : C → ℕ) : Finset (C → ℕ) :=
  Finset.univ.image (fun p : C×C => exchangeTarget X p.1 p.2)

theorem exchangeCandidates_card_le [Fintype C] (X : C → ℕ) :
    (exchangeCandidates X).card ≤ (Fintype.card C)^2 := by
  unfold exchangeCandidates
  exact (Finset.card_image_le).trans_eq (by simp only [Finset.card_univ,Fintype.card_prod,pow_two])

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_GuardMachineBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.MachineCost
open Turing

def statementCost {Γ Λ σ : Type*} : TM1.Stmt Γ Λ σ → ℕ
  | .move _ q => statementCost q+1
  | .write _ q => statementCost q+1
  | .load _ q => statementCost q
  | .branch _ q r => max (statementCost q) (statementCost r)
  | .goto _ => 1
  | .halt => 1

variable {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
variable (M : Λ → TM1.Stmt Γ Λ σ)

noncomputable def programCost [Fintype Λ] : ℕ := Finset.univ.sup (fun l=>statementCost (M l))
end MatchingFPRAS.MachineCost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_StackCompilerCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.StackCost
open Turing Turing.TM2to1 Turing.TM2to1.Λ' MachineCost

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [DecidableEq K]

def accesses : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => accesses q+1
  | .peek _ _ q => accesses q+1
  | .pop _ _ q => accesses q+1
  | .load _ q => accesses q
  | .branch _ q r => max (accesses q) (accesses r)
  | .goto _ => 0
  | .halt => 0
def StackBound (S : ∀ k,List (Γ k)) (H : ℕ) : Prop := ∀ k,(S k).length≤H
end MatchingFPRAS.StackCost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_BoolPostCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.BoolPostCompiler
open Turing MachineCost
open scoped Classical

def up : PointedMap Bool Symbol := ⟨fun b=>if b then 1 else 0,rfl⟩
def down : PointedMap Symbol Bool := ⟨fun a=>decide (a=1),rfl⟩
end MatchingFPRAS.BoolPostCompiler

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_AlphabetCompilerCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.AlphabetCost
open Turing Turing.TM1 Turing.TM1to1 MachineCost

variable {Γ Λ σ : Type*} [Inhabited Γ]

def writesCount : TM1.Stmt Γ Λ σ → ℕ
  | .move _ q => writesCount q
  | .write _ q => writesCount q+1
  | .load _ q => writesCount q
  | .branch _ q r => max (writesCount q) (writesCount r)
  | .goto _ => 0
  | .halt => 0
end MatchingFPRAS.AlphabetCost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_SupportedCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.SupportedCompiler
open Turing MachineCost
open scoped Classical

variable {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
variable (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) (hS : TM1.Supports M S)
noncomputable def cost : ℕ := S.sup (fun l=>statementCost (M l))
end MatchingFPRAS.SupportedCompiler

namespace MatchingFPRAS.AlphabetCost
open Turing MachineCost SupportedCompiler
open scoped Classical

variable {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
variable {n : ℕ} (enc : Γ → List.Vector Bool n) (dec : List.Vector Bool n → Γ)
  (enc0 : enc default = List.Vector.replicate n false)
  (encdec : ∀ a,dec (enc a)=a) (M : Λ → TM1.Stmt Γ Λ σ)
  (S : Finset Λ) (hS : TM1.Supports M S)
include encdec hS
noncomputable def supportedWrites : ℕ := S.sup (fun l=>writesCount (M l))
end MatchingFPRAS.AlphabetCost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_FixedAlphabetCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FixedAlphabetCompiler
open Turing MachineCost
open scoped Classical

variable {Γ Λ σ : Type*} [Inhabited Γ] [Fintype Γ] [Inhabited Λ]
  [Inhabited σ] [Fintype σ]
variable {w : ℕ} (enc : Γ → List.Vector Bool w) (dec : List.Vector Bool w → Γ)
  (enc0 : enc default = List.Vector.replicate w false)
  (encdec : ∀ a,dec (enc a)=a) (M : Λ → TM1.Stmt Γ Λ σ)
  (S : Finset Λ) (hS : TM1.Supports M S)
def bitsWord (input : List Γ) : List Bool := input.flatMap (fun a=>(enc a).toList)
def word (input : List Γ) : List Symbol := (bitsWord enc input).map BoolPostCompiler.up
end MatchingFPRAS.FixedAlphabetCompiler

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_FixedEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FixedEncoding
variable (Γ : Type*) [Fintype Γ] [Inhabited Γ]
noncomputable def enc (a : Γ) : List.Vector Bool (Fintype.card Γ) := by
  classical
  exact List.Vector.ofFn (fun i=>decide (a≠default ∧ Fintype.equivFin Γ a=i))
lemma blank : enc Γ default=List.Vector.replicate (Fintype.card Γ) false := by
  classical
  apply List.Vector.ext
  intro i
  simp [enc]
noncomputable def dec : List.Vector Bool (Fintype.card Γ) → Γ := Function.invFun (enc Γ)
end MatchingFPRAS.FixedEncoding

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_StackWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.StackWords
open Turing MachineCost

variable {K : Type*} {Γ : K → Type*}
def rows (S : ∀ k,List (Γ k)) (H : ℕ) : List (∀ k,Option (Γ k)) :=
  List.ofFn (fun i : Fin H=>fun k=>(S k).reverse[i.val]?)
def word (S : ∀ k,List (Γ k)) (H : ℕ) : List (TM2to1.Γ' K Γ) :=
  (true,(rows S H).headI)::((rows S H).tail.map (fun a=>(false,a)))
variable {Λ σ : Type*} [Inhabited Λ] [Inhabited σ]
variable [DecidableEq K] [Fintype K] [∀ k,Fintype (Γ k)] [Fintype σ]
variable {w : ℕ} (enc : TM2to1.Γ' K Γ → List.Vector Bool w)
  (dec : List.Vector Bool w → TM2to1.Γ' K Γ)
  (enc0 : enc default=List.Vector.replicate w false)
  (encdec : ∀ a,dec (enc a)=a)
  (M : Λ → TM2.Stmt Γ Λ σ) (S : Finset Λ) (hs : TM2.Supports M S)
def encoded (S₀ : ∀ k,List (Γ k)) (H : ℕ) : List Symbol :=
  FixedAlphabetCompiler.word enc (word S₀ H)
end MatchingFPRAS.StackWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Sampling_ChosenChord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Cells.CycleData

variable {L : Type*}
  [DecidableEq L]
  {G : SimpleGraph L}
  {m : ℕ}

@[ext] structure CellIndex where
  x : ℕ
  p : ℕ
  q : ℕ
  y : ℕ
  deriving DecidableEq

end MatchingFPRAS.Cells.CycleData

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Arithmetic_ArithmeticSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.StackComposition
open Turing MachineCost

variable {K Λ P σ : Type*} {Γ : K → Type*} [DecidableEq K]
variable [Inhabited Λ] [Inhabited P]
omit [DecidableEq K] in
lemma supports_univ [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ) : TM2.Supports M Finset.univ := by
  constructor
  · simp
  · intro l _
    induction M l with
    | push k a q ih | peek k a q ih | pop k a q ih | load a q ih => exact ih
    | branch p q r ihq ihr => exact ⟨ihq,ihr⟩
    | goto l => simp [TM2.SupportsStmt]
    | halt => trivial

open Turing MachineCost

end MatchingFPRAS.StackComposition

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Graphs_Cumulative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteChoice

open Finset

def cumulative {r : ℕ} (p : Fin r → ℚ) (i : ℕ) : ℚ := ∑ j, if j.val < i then p j else 0

lemma cumulative_total {r : ℕ} (p : Fin r → ℚ) (hs : ∑ j, p j = 1) : cumulative p r = 1 := by
  simp only [cumulative,Fin.isLt,ite_true, if_true]; exact hs

lemma options_pos {r : ℕ} (p : Fin r → ℚ) (hs : ∑ j, p j = 1) : 0 < r := by
  by_contra h
  have hr : r=0 := by omega
  subst r
  simp at hs

def candidates {r K : ℕ} (p : Fin r → ℚ) (J : Fin K) : Finset (Fin r) :=
  Finset.univ.filter (fun i => (J.val:ℚ)/K < cumulative p (i.val+1))

lemma candidates_nonempty {r K : ℕ} (p : Fin r → ℚ) (hs : ∑ j, p j = 1)
    (hK : 0 < K) (J : Fin K) : (candidates p J).Nonempty := by
  have hr := options_pos p hs
  refine ⟨⟨r-1,by omega⟩,?_⟩
  simp only [candidates,Finset.mem_filter,Finset.mem_univ,true_and]
  have he : r-1+1=r := by omega
  rw [he,cumulative_total p hs]
  apply (div_lt_one (by exact_mod_cast hK : (0:ℚ)<K)).mpr
  exact_mod_cast J.isLt

def choose {r K : ℕ} (p : Fin r → ℚ) (hs : ∑ j, p j = 1) (hK : 0 < K) (J : Fin K) : Fin r :=
  (candidates p J).min' (candidates_nonempty p hs hK J)

def outputLaw {r K : ℕ} (p : Fin r → ℚ) (hs : ∑ j, p j = 1) (hK : 0 < K) (i : Fin r) : ℚ :=
  ((Finset.univ.filter (fun J : Fin K => choose p hs hK J=i)).card:ℚ)/K




def gridInterval (K : ℕ) (a b : ℚ) : Finset ℕ :=
  (Finset.range K).filter (fun j => a ≤ (j:ℚ)/K ∧ (j:ℚ)/K < b)

end MatchingFPRAS.FiniteChoice

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Sampling_Component
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport.Sparse

open Finset

variable {Ω : Type*} [Fintype Ω] [LinearOrder Ω] [DecidableEq Ω]

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [LinearOrder E]

variable (ends : E → Sym2 V)

local instance finsetOrder : LinearOrder (Finset E) :=
  LinearOrder.lift' toColex toColex.injective

end MatchingFPRAS.Transport.Sparse

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeCanonical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A : Type}

def dedupStep [DecidableEq A] (x : A×List A) : List A := if x.1∈x.2 then x.2 else x.1::x.2

variable (r : A → A → Prop) [DecidableRel r]
def insertStep (x : A×(A×(List A×List A))) : A×(List A×List A) :=
  (x.2.1,(x.1::x.2.2.1,if r x.2.1 x.1 then x.2.1::x.1::x.2.2.1 else x.1::x.2.2.2))
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerRootEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Root auxiliary defects in the raw integer transport bound -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Matrix

noncomputable def rootCoefficients (s t : ℝ) : Bool → ℝ :=
  fun b => if b then -(1/t) else 1/s

lemma root_potential (s t : ℝ) (hs : 0 < s) (ht : 0<t) :
    (∑ b : Bool, (if b then t else s) * rootCoefficients s t b ^ 2) = 1/s+1/t := by
  simp only [Fintype.sum_bool, rootCoefficients, Bool.false_eq_true, ↓reduceIte, neg_sq]
  field_simp [ne_of_gt hs, ne_of_gt ht]
  ring

/-- Only the off-diagonal auxiliary defects can increase the root bound;
nonnegative diagonal two-hole masses contribute with the opposite sign. -/
theorem root_future_bound (B : Matrix Bool Bool ℝ) (s t K c : ℝ)
    (hs : 0 < s) (ht : 0<t) (hsymm : B true false = B false true)
    (haa : 0≤B false false) (hbb : 0≤B true true)
    (hab : B false true ≤ K*c) :
    -B.toBilin' (rootCoefficients s t) (rootCoefficients s t) ≤ 2*K*c/(s*t) := by
  have heq : B.toBilin' (rootCoefficients s t) (rootCoefficients s t) =
      B false false/s^2 - 2*B false true/(s*t) + B true true/t^2 := by
    simp only [Matrix.toBilin'_apply, Fintype.sum_bool, rootCoefficients, Bool.false_eq_true, ↓reduceIte, hsymm]
    ring
  rw [heq]
  have ha : 0 ≤ B false false/s^2 := div_nonneg haa (sq_nonneg _)
  have hb : 0 ≤ B true true/t^2 := div_nonneg hbb (sq_nonneg _)
  have hc : 2*B false true/(s*t) ≤ 2*K*c/(s*t) := by
    simpa only [mul_assoc] using div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hab (show (0:ℝ)≤2 by norm_num)) (mul_pos hs ht).le
  linarith

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_PositiveSequenceMinimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Endpoint minimum for a positive finite log-concave sequence

This is the finite inequality needed by the conditional-variance paths.
After one strict decrease, the local product inequality forces every
subsequent step to decrease, so there can be no valley between endpoints.
-/

namespace ContingencyTables

lemma positive_sequence_drop (a : ℕ → ℝ) (N k : ℕ)
    (hpos : ∀ i, i ≤ N → 0 < a i)
    (hlog : ∀ i, i+2 ≤ N → a i*a (i+2) ≤ (a (i+1))^2)
    (hk : k+2 ≤ N) (hdrop : a (k+1)<a k) : a (k+2)<a (k+1) := by
  have h0 := hpos k (by omega)
  have h1 := hpos (k+1) (by omega)
  have h2 := hlog k hk
  by_contra hn
  have hnext : a (k+1) ≤ a (k+2) := le_of_not_gt hn
  have hprod := mul_le_mul_of_nonneg_left hnext h0.le
  have hstrict := mul_lt_mul_of_pos_right hdrop h1
  nlinarith

/-- Only positivity and the local three-term product inequality are
needed, on the finite interval actually used by the application. -/
theorem positive_sequence_minimum (a : ℕ → ℝ) (N i j k : ℕ)
    (hpos : ∀ n, n ≤ N → 0 < a n)
    (hlog : ∀ n, n+2 ≤ N → a n*a (n+2) ≤ (a (n+1))^2)
    (hij : i ≤ j) (hjk : j ≤ k) (hkN : k ≤ N) : min (a i) (a k) ≤ a j := by
  by_cases hleft : a i ≤ a j
  · exact (min_le_left _ _).trans hleft
  · have hex : ∃ r, i ≤ r ∧ r<j ∧ a (r+1)<a r := by
      by_contra hn
      have hstep : ∀ r, i ≤ r → r<j → a r ≤ a (r+1) := by
        intro r hir hrj
        by_contra hr
        exact hn ⟨r,hir,hrj,lt_of_not_ge hr⟩
      have hm : ∀ n, i ≤ n → n ≤ j → a i ≤ a n := by
        intro n hin
        induction n,hin using Nat.le_induction with
        | base => intro _; exact le_rfl
        | succ n hin ih =>
          intro hnj
          exact (ih (by omega)).trans (hstep n hin (by omega))
      exact hleft (hm j hij le_rfl)
    obtain ⟨r,hir,hrj,hdrop⟩ := hex
    have hdecrease : ∀ n, r ≤ n → n+1 ≤ N → a (n+1)<a n := by
      intro n hrn
      induction n,hrn using Nat.le_induction with
      | base => intro _; exact hdrop
      | succ n hrn ih =>
        intro hnN
        exact positive_sequence_drop a N n hpos hlog (by omega) (ih (by omega))
    have hm : ∀ n, j ≤ n → n ≤ k → a n ≤ a j := by
      intro n hjn
      induction n,hjn using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ n hjn ih =>
        intro hnk
        exact (hdecrease n (by omega) (by omega)).le.trans (ih (by omega))
    exact (min_le_right _ _).trans (hm k hjk le_rfl)

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerChildLogConcavity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional child masses have no internal valley

The actual two-coordinate removal form gives the local log-concavity
inequality. The endpoint-minimum property passes to the hard-zero limit.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Topology Matrix
open FactorialSignatures Filter

def childProfile (U k : ℕ) : Bool → ℕ := fun b => if b then U-k else k

lemma childProfile_total (U k : ℕ) (hk : k ≤ U) : (∑ b, childProfile U k b)=U := by
  simp only [Fintype.sum_bool,childProfile,Bool.false_eq_true,↓reduceIte]
  omega

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_RepairPrefixes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal repair values and row-major prefix preservation -/

namespace ContingencyTables

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def RowMajorBefore [LT I] [LT J] (s t : I×J) : Prop :=
  s.1<t.1 ∨ s.1=t.1 ∧ s.2<t.2

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
lemma RowMajorBefore.trans [LinearOrder I] [LinearOrder J] {r s t : I×J}
    (hrs : RowMajorBefore r s) (hst : RowMajorBefore s t) : RowMajorBefore r t := by
  rcases hrs with hrs|⟨hrs,hc⟩
  · rcases hst with hst|⟨hst,_⟩
    · exact Or.inl (lt_trans hrs hst)
    · exact Or.inl (hst ▸ hrs)
  · rcases hst with hst|⟨hst,htc⟩
    · exact Or.inl (hrs ▸ hst)
    · exact Or.inr ⟨hrs.trans hst,lt_trans hc htc⟩

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
lemma RowMajorBefore.ne [LinearOrder I] [LinearOrder J] {s t : I×J}
    (h : RowMajorBefore s t) : s ≠ t := by
  intro he
  subst t
  rcases h with h|⟨_,h⟩ <;> exact lt_irrefl _ h

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_RepairResiduals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original residual bounds are preserved by the literal repair

Only a small source entry is lowered. Every large entry is unchanged or
increased. Since full row and column-view totals are preserved, the
small row/column sums cannot increase.
-/

namespace ContingencyTables

open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

noncomputable def largeRow (small : I → J → Bool) (X : I → J → ℕ) (i : I) : ℕ :=
  ∑ j, if small i j then 0 else X i j

noncomputable def largeColumnView (small : I → J → Bool) (Q : I → J → ℕ) (j : J) : ℕ :=
  ∑ i, if small i j then 0 else Q i j

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallContextFibres
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual small-prefix fibres and conditional repair

Only small cells in the row-major prefix are fixed. Large completions
remain free and retain their full counting multiplicity.
-/

namespace ContingencyTables.SmallContextFibres

open scoped BigOperators Classical
open LargePairEnumeration

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def SmallPrefix [LT I] [LT J] (small : I → J → Bool) (s : I×J)
    (σ : I×J → ℕ) (X : I → J → ℕ) : Prop :=
  ∀ i j, small i j=true → RowMajorBefore (i,j) s → X i j=σ (i,j)

end ContingencyTables.SmallContextFibres

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallContextCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual row-major small-prefix coordinate splitting

The retained prefix is precisely the earlier small cells. The remaining
ordinary cells all follow the next exposed cell, which is the condition
needed for the completion-retaining conditional repair injection.
-/

namespace ContingencyTables.SmallContextCoordinates

open scoped Classical
open LargePairEnumeration

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

lemma rowMajor_trichotomy (s t : I×J) : RowMajorBefore s t ∨ s=t ∨ RowMajorBefore t s := by
  rcases lt_trichotomy s.1 t.1 with h|h|h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy s.2 t.2 with hc|hc|hc
    · exact Or.inl (Or.inr ⟨h,hc⟩)
    · exact Or.inr (Or.inl (Prod.ext h hc))
    · exact Or.inr (Or.inr (Or.inr ⟨h.symm,hc⟩))
  · exact Or.inr (Or.inr (Or.inl h))

/-- Pack the prefix, special pair and suffix into the cell split. -/
def splitPairEquiv (P T : Type u) :
    ((P×Bool) ⊕ (Bool ⊕ (T×Bool))) ≃ (P ⊕ (Unit ⊕ T))×Bool where
  toFun
    | .inl (p,b) => (.inl p,b)
    | .inr (.inl b) => (.inr (.inl ()),b)
    | .inr (.inr (t,b)) => (.inr (.inr t),b)
  invFun
    | (.inl p,b) => .inl (p,b)
    | (.inr (.inl _),b) => .inr (.inl b)
    | (.inr (.inr t),b) => .inr (.inr (t,b))
  left_inv x := by rcases x with ⟨p,b⟩|b|⟨t,b⟩ <;> rfl
  right_inv x := by rcases x with ⟨p|(_|t),b⟩ <;> rfl

end ContingencyTables.SmallContextCoordinates

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ExcessContextProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical defect profiles in the auxiliary context kernel -/

namespace ContingencyTables.ExcessContextProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres
open LargePairEnumeration
open IntegerWeightedTransport

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

def auxRoot (U l : ℕ) : Bool → ℕ := fun b => if b then U-l else l-1

end ContingencyTables.ExcessContextProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_AuxiliaryRepairMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional repair bounds the literal auxiliary kernel mass -/

namespace ContingencyTables.ExcessContextProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres
open LargePairEnumeration
open IntegerWeightedTransport

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

lemma finite_injective_sum_le {X Y : Type*} [Fintype X] [Fintype Y]
    (j : X → Y) (hj : Function.Injective j) (g : Y → ℝ) (hg : ∀ y, 0 ≤ g y) :
    (∑ x, g (j x)) ≤ ∑ y, g y := by
  calc
    _ = ∑ y ∈ Finset.univ.image j, g y :=
      (Finset.sum_image (fun x _ y _ he => hj he)).symm
    _ ≤ ∑ y, g y := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun y _ _ => hg y)

end ContingencyTables.ExcessContextProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerTransportCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Eliminating the actual auxiliary-defect coefficient

Conditional repair bounds each auxiliary defect fibre by one endpoint
child. The elementary reciprocal calculation below converts their sum
into the manuscript's uniform adjacent-mean transport constant.
-/

namespace ContingencyTables.IntegerWeightedTransport

lemma root_coefficient_bound (s t K c d : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hK : 0 ≤ K) (hc : c ≤ d*max s t) :
    min s t*(1/s+1/t+K*c/(s*t)) ≤ 2+K*d := by
  wlog hst : s ≤ t generalizing s t
  · have h := this t s ht hs (by simpa only [max_comm] using hc) (le_of_not_ge hst)
    simpa only [min_comm,mul_comm t s,add_comm (1/t) (1/s)] using h
  rw [min_eq_left hst,max_eq_right hst] at *
  have he : s*(1/s+1/t+K*c/(s*t))=1+s/t+K*(c/t) := by
    field_simp
  rw [he]
  have hst' : s/t ≤ 1 := (div_le_one ht).mpr hst
  have hc' : c/t ≤ d := (div_le_iff₀ ht).mpr hc
  have hkc := mul_le_mul_of_nonneg_left hc' hK
  linarith

/-- The hard root transport and the proved repair domination give the
uniform adjacent-mean estimate used in exposure variance. -/
theorem repaired_root_transport (s t c d W E Δ : ℝ)
    (hs : 0 < s) (ht : 0 < t) (hE : 0 ≤ E)
    (hc : c ≤ d*max s t)
    (htransport : Δ^2 ≤ (1/s+1/t+2*(W+1)^2*c/(s*t))*E) :
    min s t*Δ^2 ≤ (2+2*d*(W+1)^2)*E := by
  have hcoef := root_coefficient_bound s t (2*(W+1)^2) c d hs ht (by positivity) hc
  calc
    _ ≤ min s t*((1/s+1/t+2*(W+1)^2*c/(s*t))*E) :=
      mul_le_mul_of_nonneg_left htransport (le_min hs.le ht.le)
    _ = (min s t*(1/s+1/t+2*(W+1)^2*c/(s*t)))*E := by ring
    _ ≤ (2+(2*(W+1)^2)*d)*E := mul_le_mul_of_nonneg_right hcoef hE
    _ = _ := by ring

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ContextAdjacentTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Adjacent physical exposure means with the repaired coefficient -/

namespace ContingencyTables.ExcessContextProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres
open LargePairEnumeration
open IntegerWeightedTransport
open FactorialSignatures

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

def rootDisplay (U l : ℕ) : Bool → ℕ := fun b => if b then U-l+1 else l

lemma rootDisplay_total (U l : ℕ) (hlU : l ≤ U) :
    (∑ b, rootDisplay U l b)=U+1 := by
  simp only [rootDisplay,Fintype.sum_bool,Bool.false_eq_true,↓reduceIte]
  omega

lemma widths_constant_mem (U : ℕ) {n : ℕ} (w : ℕ)
    (hw : w ∈ widths (fun _ : Fin n => U)) : w=U := by
  induction n with
  | zero => exact False.elim (List.not_mem_nil hw)
  | succ n ih =>
    simp only [widths,List.mem_cons] at hw
    exact hw.elim id ih

end ContingencyTables.ExcessContextProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerChildVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Between-child variance from raw integer transport

The no-valley bound for child masses turns adjacent transport into a
bound on every pair of child means. Finite Cauchy--Schwarz and the exact
weighted pair formula then bound the between-child variance.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical

lemma range_difference_sum (H : ℕ → ℝ) (a n : ℕ) :
    (∑ j ∈ Finset.range n, (H (a+j)-H (a+j+1)))=H a-H (a+n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih]; simp only [Nat.add_succ]; ring

lemma path_square (H : ℕ → ℝ) (a n : ℕ) :
    (H a-H (a+n))^2 ≤ (n:ℝ)*∑ j ∈ Finset.range n, (H (a+j)-H (a+j+1))^2 := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range n)
    (r := fun j => H (a+j)-H (a+j+1)) (f := fun _ => (1:ℝ))
    (g := fun j => (H (a+j)-H (a+j+1))^2)
    (fun _ _ => zero_le_one) (fun _ _ => sq_nonneg _) (fun _ _ => by simp)
  simpa only [range_difference_sum,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] using h

lemma minimum_pair_coefficient (x y Z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hZ : 0 < Z) (hxZ : x ≤ Z) (hyZ : y ≤ Z) : x*y/Z ≤ min x y := by
  apply le_min
  · apply (div_le_iff₀ hZ).mpr
    exact mul_le_mul_of_nonneg_left hyZ hx
  · apply (div_le_iff₀ hZ).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hxZ hy

lemma child_pair_path_bound (z H : ℕ → ℝ) (U a b : ℕ) (Z A E : ℝ)
    (hz : ∀ j ≤ U, 0 ≤ z j) (hZ : 0 < Z) (hzZ : ∀ j ≤ U, z j ≤ Z)
    (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hminimum : ∀ a j b, a ≤ j → j ≤ b → b ≤ U → min (z a) (z b) ≤ z j)
    (hadj : ∀ j, j < U → min (z j) (z (j+1))*(H j-H (j+1))^2 ≤ A*E)
    (ha : a ≤ U) (hb : b ≤ U) :
    z a*z b/Z*(H a-H b)^2 ≤ (U:ℝ)^2*A*E := by
  wlog hab : a ≤ b generalizing a b
  · have h := this b a hb ha (by omega)
    have hsq : (H b-H a)^2=(H a-H b)^2 := by ring
    simpa only [mul_comm (z b) (z a),hsq] using h
  have hmin : 0 ≤ min (z a) (z b) := le_min (hz a ha) (hz b hb)
  have hn : b-a ≤ U := by omega
  have hpath := path_square H a (b-a)
  rw [Nat.add_sub_of_le hab] at hpath
  have hcoef := minimum_pair_coefficient (z a) (z b) Z (hz a ha) (hz b hb)
    hZ (hzZ a ha) (hzZ b hb)
  have hsteps : ∑ j ∈ Finset.range (b-a),
      min (z a) (z b)*(H (a+j)-H (a+j+1))^2 ≤ (b-a:ℕ)* (A*E) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (b-a), A*E := by
        apply Finset.sum_le_sum
        intro j hj
        have hjn := Finset.mem_range.mp hj
        have hjU : a+j < U := by omega
        have hm : min (z a) (z b) ≤ min (z (a+j)) (z (a+j+1)) := by
          apply le_min
          · exact hminimum a (a+j) b (by omega) (by omega) hb
          · exact hminimum a (a+j+1) b (by omega) (by omega) hb
        exact (mul_le_mul_of_nonneg_right hm (sq_nonneg _)).trans (hadj (a+j) hjU)
      _ = _ := by simp
  have hnreal : (b-a:ℕ) ≤ (U:ℝ) := by exact_mod_cast hn
  have hAE : 0 ≤ A*E := mul_nonneg hA hE
  calc
    _ ≤ min (z a) (z b)*(H a-H b)^2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
    _ ≤ min (z a) (z b)*((b-a:ℕ)*
        ∑ j ∈ Finset.range (b-a), (H (a+j)-H (a+j+1))^2) :=
      mul_le_mul_of_nonneg_left hpath hmin
    _ = (b-a:ℕ)*(∑ j ∈ Finset.range (b-a),
        min (z a) (z b)*(H (a+j)-H (a+j+1))^2) := by rw [←Finset.mul_sum]; ring
    _ ≤ (b-a:ℕ)*((b-a:ℕ)*(A*E)) :=
      mul_le_mul_of_nonneg_left hsteps (Nat.cast_nonneg _)
    _ ≤ (U:ℝ)*((U:ℝ)*(A*E)) := by
      gcongr
    _ = _ := by ring

lemma finite_pair_square {X : Type*} [Fintype X] (w H : X → ℝ) :
    (∑ x, ∑ y, w x*w y*(H x-H y)^2)=
      2*(∑ x, w x)*(∑ x, w x*(H x)^2)-2*(∑ x, w x*H x)^2 := by
  have he (x y : X) : w x*w y*(H x-H y)^2=
      (w x*(H x)^2)*w y+w x*(w y*(H y)^2)-2*((w x*H x)*(w y*H y)) := by ring
  have hinner (x : X) : (∑ y, w x*w y*(H x-H y)^2)=
      (w x*(H x)^2)*(∑ y, w y)+w x*(∑ y, w y*(H y)^2)-
        2*((w x*H x)*(∑ y, w y*H y)) := by
    simp_rw [he,Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum]
  simp_rw [hinner,Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul]
  ring

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteExposureVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite exposure variance with zero-mass children

The exact variance decomposition uses only finite nonnegative weights.
A child of mass zero has zero moment, so its mean can be set to zero.
This is the algebraic decomposition iterated by the small-slot exposure.
-/

namespace ContingencyTables.FiniteExposureVariance

open scoped BigOperators Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]

noncomputable def mean (w H : X → ℝ) : ℝ := (∑ x, w x*H x)/(∑ x, w x)

noncomputable def variance (w H : X → ℝ) : ℝ := ∑ x, w x*(H x-mean w H)^2

omit [Fintype Y] in
lemma zero_mass_weights (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hz : (∑ x, w x)=0) :
    ∀ x, w x=0 := by
  intro x
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hw y)).mp hz x (Finset.mem_univ x)

omit [Fintype Y] in
lemma mean_moment (w H : X → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ x, w x)*mean w H=∑ x, w x*H x := by
  by_cases hz : (∑ x, w x)=0
  · have h := zero_mass_weights w hw hz
    simp only [mean,h,zero_mul,Finset.sum_const_zero]
  · unfold mean
    field_simp

omit [Fintype Y] in
lemma mean_second (w H : X → ℝ) :
    (∑ x, w x)*(mean w H)^2=(∑ x, w x*H x)^2/(∑ x, w x) := by
  by_cases hz : (∑ x, w x)=0
  · simp only [mean,hz,div_zero,zero_mul]
  · unfold mean
    field_simp

end ContingencyTables.FiniteExposureVariance

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallCellCatalogProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enumerating the actual small cells from binary margins -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

abbrev CellCatalogInput := (List ℕ×List ℕ)×ℕ

def smallCellTest (z : CellCatalogInput×(ℕ×ℕ)) : Bool :=
  decide (z.1.1.1.getD z.2.1 0<z.1.2 ∨ z.1.1.2.getD z.2.2 0<z.1.2)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseOffsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unique bin and offset encoding of free integer entries -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators

def gridCoordinateFin (K : ℕ) : Set.Icc (0 : ℤ) ((K : ℤ) - 1) ≃ Fin K where
  toFun z := ⟨z.val.toNat, by
    have hcast : (z.val.toNat : ℤ) = z.val := Int.toNat_of_nonneg z.property.1
    have hhi := z.property.2
    omega⟩
  invFun v := ⟨(v.val : ℤ), by constructor <;> omega⟩
  left_inv z := by
    apply Subtype.ext
    exact Int.toNat_of_nonneg z.property.1
  right_inv v := by
    apply Fin.ext
    exact Int.toNat_natCast _

variable {I J : Type*} [Fintype I] [Fintype J]
variable {q : ℕ}

abbrev Offset (w : I × J → ℕ) := ∀ p, Fin (w p)
abbrev FreeBox (w : I × J → ℕ) (K : ℕ) := ∀ p, Fin (K * w p)

def integerWidth (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ) (p : I × J) : ℕ :=
  min (R (some p.1)) (P (some p.2)) / d ^ 8

omit [Fintype I] [Fintype J] in
theorem integerWidth_pos (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j) (p : I × J) :
    0 < integerWidth R P d p :=
  DenseAffine.dense_width_positive d _ hd (le_min (hR _) (hP _))

omit [Fintype I] [Fintype J] in
theorem free_entry_lt_box (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (p : I × J) (z : ℕ) (hz : z ≤ min (R (some p.1)) (P (some p.2))) :
    z < (4 * d ^ 8) * integerWidth R P d p := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hb := (DenseAffine.dense_width_bounds d (min (R (some p.1)) (P (some p.2))) hd
    (le_min (hR _) (hP _))).1
  have hs : min (R (some p.1)) (P (some p.2)) ≤
      (2 * d ^ 8) * integerWidth R P d p := by
    have h := (div_le_iff₀ (show (0 : ℝ) < 2 * (d : ℝ) ^ 8 by positivity)).mp hb
    have h' : min (R (some p.1)) (P (some p.2)) ≤
        integerWidth R P d p * (2 * d ^ 8) := by exact_mod_cast h
    simpa only [Nat.mul_comm] using h'
  have hw := integerWidth_pos R P d hd hR hP p
  have hd8 : 0 < d ^ 8 := pow_pos (show 0 < d by omega) _
  nlinarith [Nat.mul_pos hd8 hw]

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FirstSuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# First-success law and finite-law error bounds

The bounded outer sampler repeats independent trials and uses a fixed
feasible fallback. Its geometric output law has a stationary uniform-mixture
specialization. Total-variation bounds are preserved by deterministic output
maps.
-/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators
open ResidualMixture

variable {α β : Type*} [Fintype α] [Fintype β]

lemma geometric_balance (f : ℚ) (J : ℕ) :
    (1 - f) * (∑ j ∈ Finset.range J, f ^ j) + f ^ J = 1 := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith [ih]

/-- The exact first-success-or-fallback mass from the manuscript. -/
def outputMass [DecidableEq α] (g : α → ℚ) (f : ℚ) (J : ℕ) (fallback z : α) : ℚ :=
  g z * (∑ j ∈ Finset.range J, f ^ j) + if z = fallback then f ^ J else 0

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseRationalKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational transition and walk laws for the actual dense bin chain -/

namespace ContingencyTables.GridBoundary

open ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def rationalProposal (d : ℕ) : ℚ := 1 / (2 : ℚ) ^ Nat.clog 2 (8 * d)

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseBoundedTrial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite dense trial with bounded independent offset draws -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical
open ResidualMixture FirstSuccess

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def offsetCoordinateEquiv (e : I × J ≃ Fin q) (w : I × J → ℕ) :
    (∀ j : Fin q, Fin (w (e.symm j))) ≃ Offset w :=
  (Equiv.piCongrLeft' (fun p => Fin (w p)) e).symm

theorem inverse_two_pow_cast (n : ℕ) :
    ((1 / (2 : ℚ) ^ n : ℚ) : ℝ) = (2 : ℝ) ^ (-(n : ℝ)) := by
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat]
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  exact one_div _

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RejectionLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite repeated-trial laws and their approximation error -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture

noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

omit [Fintype β] in
theorem outputMass_succ (g : β → ℚ) (f : ℚ) (n : ℕ) (fallback z : β) :
    outputMass g f (n + 1) fallback z = g z + f * outputMass g f n fallback z := by
  have h := geometric_balance f n
  have hg := congrArg (fun x : ℚ => g z * x) h
  unfold outputMass
  rw [Finset.sum_range_succ, pow_succ]
  split_ifs <;> nlinarith [hg]

end

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteWordWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact laws of a walk driven by independent fixed-length Boolean words -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

def uniformMapMass {A : Type*} [Fintype A] (f : A → α) (y : α) : ℚ :=
  (∑ x, if f x = y then (1 : ℚ) else 0) / Fintype.card A

omit [Fintype α] in
theorem uniformMapMass_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → α) (y : α) : uniformMapMass (f ∘ e) y = uniformMapMass f y := by
  unfold uniformMapMass
  rw [Fintype.card_congr e]
  congr 1
  exact e.sum_comp (fun x => if f x = y then (1 : ℚ) else 0)

theorem finite_fiber_sum {A : Type*} [Fintype A] (f : A → α) (g : α → ℚ) :
    (∑ y, (∑ x, if f x = y then (1 : ℚ) else 0) * g y) = ∑ x, g (f x) := by
  simp_rw [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]

theorem uniformMapMass_prod {A B : Type*} [Fintype A] [Fintype B]
    (f : A → α) (g : α → B → α) (y : α) :
    uniformMapMass (fun z : A × B => g (f z.1) z.2) y =
      ∑ s, uniformMapMass f s * uniformMapMass (g s) y := by
  unfold uniformMapMass
  simp only [Fintype.card_prod, Nat.cast_mul, div_mul_div_comm, ← Finset.sum_div,
    Fintype.sum_prod_type]
  rw [finite_fiber_sum]

end

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseExponentArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Natural arithmetic for the dense acceptance exponent

Each integral completion entry is represented by a difference of two
natural numbers. The rational floor in the geometric definition is then
an ordinary natural quotient, including zero denominators.
-/

namespace ContingencyTables.GridBoundary
open scoped BigOperators Classical

def componentExponent (d s positive negative : ℕ) : ℕ :=
  (d^4*d^8*negative-d^4*(d^8*positive+d*s))/(s*d^8)

variable {I J : Type*} [Fintype I] [Fintype J]

def integerParts (R : Option I → ℕ) (P : Option J → ℕ) (z : I×J → ℕ) :
    Option I → Option J → ℕ×ℕ
  | some i,some j => (z (i,j),0)
  | some i,none => (R (some i),∑ j,z (i,j))
  | none,some j => (P (some j),∑ i,z (i,j))
  | none,none => (R none+∑ i,∑ j,z (i,j),∑ j,P (some j))

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCompletionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Signed dependent entries from binary margin and matrix lists -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped
open scoped BigOperators

def marginCode {m : ℕ} (R : Option (Fin m) → ℕ) : List ℕ :=
  R none::List.ofFn (fun i => R (some i))

def optionIndex {m : ℕ} : Option (Fin m) → ℕ
  | none => 0
  | some i => i.val+1

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RowMajorEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Increasing enumeration of the actual finite small cells -/

namespace ContingencyTables.RowMajorEnumeration

open scoped Classical
open SmallContextCoordinates

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

abbrev LexCells (small : I → J → Bool) :=
  {a : I×ₗJ // small (ofLex a).1 (ofLex a).2=true}

def earlierFinEquiv {n : ℕ} (k : Fin n) : Fin k.val ≃ {j : Fin n // j<k} where
  toFun a := ⟨⟨a.val,by have ha := a.isLt; have hk := k.isLt; omega⟩,a.isLt⟩
  invFun a := ⟨a.val.val,a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def laterFinEquiv {n : ℕ} (k : Fin n) : Fin (n-k.val-1) ≃ {j : Fin n // k<j} where
  toFun a := ⟨⟨k.val+1+a.val,by have ha := a.isLt; have hk := k.isLt; omega⟩,by
    change k.val<k.val+1+a.val
    omega⟩
  invFun a := ⟨a.val.val-k.val-1,by have ha := a.val.isLt; have hk := a.property; omega⟩
  left_inv a := by apply Fin.ext; dsimp only; omega
  right_inv a := by apply Subtype.ext; apply Fin.ext; have ha := a.property; dsimp only; omega

end ContingencyTables.RowMajorEnumeration

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperExposureVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual first-paper per-context exposure variance bound -/

namespace ContingencyTables.ExcessContextProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres
open LargePairEnumeration IntegerWeightedTransport

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma exposure_coefficient (U n d : ℕ) (hd : 1 ≤ d) (hn : n ≤ d) :
    ((U:ℝ)+1)^4*(2+2*n*((U:ℝ)+1)^2) ≤ 4*d*((U:ℝ)+1)^6 := by
  have hn' : (n:ℝ) ≤ d := by exact_mod_cast hn
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hq : (1:ℝ) ≤ ((U:ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) U]
  have hdq : (1:ℝ) ≤ d*((U:ℝ)+1)^2 := hq.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hd' (sq_nonneg ((U:ℝ)+1)))
  have hnum : (2:ℝ)+2*n*((U:ℝ)+1)^2 ≤ 4*d*((U:ℝ)+1)^2 := by
    have hh := mul_le_mul_of_nonneg_right hn' (sq_nonneg ((U:ℝ)+1))
    nlinarith
  calc
    _ ≤ ((U:ℝ)+1)^4*(4*d*((U:ℝ)+1)^2) :=
      mul_le_mul_of_nonneg_left hnum (by positivity)
    _ = _ := by ring

end ContingencyTables.ExcessContextProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FinitePartitionVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact variance decomposition for finite physical prefix partitions -/

namespace ContingencyTables.FiniteExposureVariance

open scoped BigOperators Classical

variable {X C D : Type*} [Fintype X] [Fintype C] [Fintype D]

noncomputable def fibreWeight (w : X → ℝ) (π : X → C) (c : C) : X → ℝ :=
  fun x => if π x=c then w x else 0

omit [Fintype X] [Fintype C] [Fintype D] in
lemma fibreWeight_mul (w H : X → ℝ) (π : X → C) (c : C) (x : X) :
    fibreWeight (fun x => w x*H x) π c x=fibreWeight w π c x*H x := by
  simp only [fibreWeight,ite_mul,zero_mul]

omit [Fintype X] [Fintype C] [Fintype D] in
lemma fibreWeight_nonnegative (w : X → ℝ) (hw : ∀ x,0 ≤ w x) (π : X → C) (c : C) :
    ∀ x,0 ≤ fibreWeight w π c x := by
  intro x
  unfold fibreWeight
  split_ifs
  · exact hw x
  · exact le_rfl

noncomputable def partitionVariance (w H : X → ℝ) (π : X → C) : ℝ :=
  ∑ c,variance (fibreWeight w π c) H

noncomputable def partitionContribution (w H : X → ℝ) (π : X → C) (ρ : X → D) : ℝ :=
  ∑ c,variance (fun d => ∑ x,fibreWeight (fibreWeight w π c) ρ d x)
    (fun d => mean (fibreWeight (fibreWeight w π c) ρ d) H)

omit [Fintype X] [Fintype C] [Fintype D] in
lemma fibreWeight_pair (w : X → ℝ) (π : X → C) (ρ : X → D) (c : C) (d : D) :
    fibreWeight (fibreWeight w π c) ρ d=fibreWeight w (fun x => (π x,ρ x)) (c,d) := by
  funext x
  unfold fibreWeight
  simp only [Prod.mk.injEq]
  by_cases hc : π x=c <;> by_cases hd : ρ x=d <;> simp only [hc,hd,↓reduceIte,and_self,
    false_and,and_false]

omit [Fintype D] in
lemma partitionVariance_reindex {E : Type*} [Fintype E] (e : C ≃ E)
    (w H : X → ℝ) (π : X → C) :
    partitionVariance w H (fun x => e (π x))=partitionVariance w H π := by
  unfold partitionVariance
  symm
  apply Fintype.sum_equiv e
  intro c
  congr 1
  funext x
  simp only [fibreWeight,Equiv.apply_eq_iff_eq]

end ContingencyTables.FiniteExposureVariance

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FinitePrefixVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Variance telescoping for literal finite coordinate prefixes -/

namespace ContingencyTables.FiniteExposureVariance

open scoped BigOperators Classical

def restriction {A : Type*} {q : ℕ} (k : ℕ) (hk : k ≤ q)
    (a : Fin q → A) : Fin k → A := fun i => a ⟨i.val,lt_of_lt_of_le i.isLt hk⟩

def prefixSnocEquiv (A : Type*) (k : ℕ) : ((Fin k → A)×A) ≃ (Fin (k+1) → A) :=
  (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ => A))

lemma restriction_snoc {A : Type*} {q k : ℕ} (hk : k < q) (a : Fin q → A) :
    prefixSnocEquiv A k (restriction k (Nat.le_of_lt hk) a,a ⟨k,hk⟩)=
      restriction (k+1) hk a := by
  change Fin.snoc (restriction k (Nat.le_of_lt hk) a) (a ⟨k,hk⟩)=restriction (k+1) hk a
  have hi : restriction k (Nat.le_of_lt hk) a=Fin.init (restriction (k+1) hk a) := rfl
  rw [hi]
  exact Fin.snoc_init_self _

variable {A : Type*} [Fintype A] {q : ℕ}

noncomputable def prefixVariance (w H : (Fin q → A) → ℝ) (k : ℕ) (hk : k ≤ q) : ℝ :=
  partitionVariance w H (restriction k hk)

noncomputable def prefixContribution (w H : (Fin q → A) → ℝ) (k : Fin q) : ℝ :=
  partitionContribution w H (restriction k.val (Nat.le_of_lt k.isLt)) (fun a => a k)

end ContingencyTables.FiniteExposureVariance

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteChoiceFibres
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite fibre sums with their literal subtype enumeration -/

namespace ContingencyTables.FiniteExposureVariance

open scoped BigOperators Classical

lemma double_fibreWeight_mul {X C D : Type*} (w H : X → ℝ)
    (π : X → C) (ρ : X → D) (c : C) (d : D) (x : X) :
    fibreWeight (fibreWeight (fun a => w a*H a) π c) ρ d x=
      fibreWeight (fibreWeight w π c) ρ d x*H x := by
  rw [fibreWeight_pair,fibreWeight_mul,← fibreWeight_pair]

theorem double_fibre_sum {X C D : Type*} [Fintype X]
    (w : X → ℝ) (π : X → C) (ρ : X → D) (c : C) (d : D)
    [Fintype {x : X // π x=c ∧ ρ x=d}] :
    (∑ x,fibreWeight (fibreWeight w π c) ρ d x)=
      ∑ x : {x : X // π x=c ∧ ρ x=d},w x.val := by
  have he (x : X) : fibreWeight (fibreWeight w π c) ρ d x=
      if π x=c ∧ ρ x=d then w x else 0 := by
    unfold fibreWeight
    by_cases hp : π x=c <;> by_cases hρ : ρ x=d <;>
      simp only [hp,hρ,↓reduceIte,and_self,false_and,and_false]
  calc
    _ = ∑ x,if π x=c ∧ ρ x=d then w x else 0 := Finset.sum_congr rfl (fun x _ => he x)
    _ = ∑ x ∈ Finset.univ.filter (fun x => π x=c ∧ ρ x=d),w x := (Finset.sum_filter _ _).symm
    _ = _ := Finset.sum_subtype _ (by simp) w

end ContingencyTables.FiniteExposureVariance

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteSymmetricEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Repair edges are charged once in a symmetric physical graph -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical

noncomputable def pairTerm {X : Type*} (f H : X → ℝ) (p : X×X) : ℝ :=
  min (f p.1) (f p.2)*(H p.1-H p.2)^2

noncomputable def symmetricEnergy {X : Type*} (E : Finset (X×X)) (f H : X → ℝ) : ℝ :=
  (∑ p ∈ E,pairTerm f H p)/2

lemma pairTerm_nonnegative {X : Type*} (f H : X → ℝ) (hf : ∀ x,0 ≤ f x) (p : X×X) :
    0 ≤ pairTerm f H p := mul_nonneg (le_min (hf _) (hf _)) (sq_nonneg _)

lemma pairTerm_reverse {X : Type*} (f H : X → ℝ) (x y : X) :
    pairTerm f H (y,x)=pairTerm f H (x,y) := by
  unfold pairTerm
  rw [min_comm]
  congr 1
  ring

theorem symmetricEnergy_mono {X : Type*} (E F : Finset (X×X)) (hEF : E ⊆ F)
    (f H : X → ℝ) (hf : ∀ x,0 ≤ f x) : symmetricEnergy E f H ≤ symmetricEnergy F f H := by
  unfold symmetricEnergy
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact Finset.sum_le_sum_of_subset_of_nonneg hEF (fun p _ _ => pairTerm_nonnegative f H hf p)

/-- Distinct defects give distinct unoriented repair edges. Both directed
copies together use twice their weight and hence cancel the energy's half. -/
theorem repair_energy_le {X D : Type*} [Fintype D] (E : Finset (X×X))
    (f H : X → ℝ) (hf : ∀ x,0 ≤ f x) (x y : D → X)
    (hx : Function.Injective x) (hxy : ∀ d e,x d≠y e)
    (hforward : ∀ d,(x d,y d) ∈ E) (hreverse : ∀ d,(y d,x d) ∈ E) :
    (∑ d,pairTerm f H (x d,y d)) ≤ symmetricEnergy E f H := by
  let a := fun d => (x d,y d)
  let b := fun d => (y d,x d)
  let A := Finset.univ.image a
  let B := Finset.univ.image b
  have ha : Function.Injective a := fun d e he => hx (congrArg Prod.fst he)
  have hb : Function.Injective b := fun d e he => hx (congrArg Prod.snd he)
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨d,_,hd⟩ := Finset.mem_image.mp hp
    obtain ⟨e,_,he⟩ := Finset.mem_image.mp hq
    exact hxy d e (congrArg Prod.fst (hd.trans he.symm))
  have hsub : A ∪ B ⊆ E := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp|hp
    · obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hp
      exact hforward d
    · obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hp
      exact hreverse d
  have hA : (∑ p ∈ A,pairTerm f H p)=∑ d,pairTerm f H (x d,y d) :=
    Finset.sum_image (fun d _ e _ he => ha he)
  have hB : (∑ p ∈ B,pairTerm f H p)=∑ d,pairTerm f H (x d,y d) := by
    rw [Finset.sum_image (fun d _ e _ he => hb he)]
    apply Finset.sum_congr rfl
    intro d _
    exact pairTerm_reverse f H (x d) (y d)
  have hs : 2*(∑ d,pairTerm f H (x d,y d)) ≤ ∑ p ∈ E,pairTerm f H p := by
    calc
      _ = ∑ p ∈ A ∪ B,pairTerm f H p := by rw [Finset.sum_union hdis,hA,hB]; ring
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => pairTerm_nonnegative f H hf p)
  unfold symmetricEnergy
  linarith

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteRepairVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite variance extension along completion-retaining repairs -/

namespace ContingencyTables.FiniteExposureVariance

open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

omit [Fintype X] in
lemma square_repair_split (x y a : ℝ) : (x-a)^2 ≤ 2*(x-y)^2+2*(y-a)^2 := by
  nlinarith [sq_nonneg (x-2*y+a)]

omit [Fintype X] in
lemma repair_center_mass {B D T : Type*} [Fintype B] [Fintype D] [Fintype T]
    (w : B → ℝ) (v : D → ℝ) (H : B → ℝ) (R : D → B) (label : D → T)
    (hw : ∀ b,0 ≤ w b) (hdom : ∀ d,v d ≤ w (R d))
    (hinj : Function.Injective (fun d => (label d,R d))) (a : ℝ) :
    (∑ d,v d*(H (R d)-a)^2) ≤ Fintype.card T*∑ b,w b*(H b-a)^2 := by
  calc
    _ ≤ ∑ d,w (R d)*(H (R d)-a)^2 :=
      Finset.sum_le_sum (fun d _ => mul_le_mul_of_nonneg_right (hdom d) (sq_nonneg _))
    _ ≤ ∑ p : T×B,w p.2*(H p.2-a)^2 :=
      ExcessContextProfiles.finite_injective_sum_le (fun d => (label d,R d)) hinj
        (fun p => w p.2*(H p.2-a)^2) (fun p => mul_nonneg (hw _) (sq_nonneg _))
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

end ContingencyTables.FiniteExposureVariance

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteGraphPoincareBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The source polynomial coefficient for the repaired graph -/

namespace ContingencyTables.FiniteExposureVariance

open scoped BigOperators Classical

lemma graph_poincare_coefficient (d U : ℕ) (hd : 1 ≤ d) (hU : 1 ≤ U) :
    ((1+2*(d:ℝ)^2)*4*(d:ℝ)^2*((U:ℝ)+1)^6+2) ≤ 770*(d:ℝ)^4*(U:ℝ)^6 := by
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hU' : (1:ℝ) ≤ U := by exact_mod_cast hU
  have hd2 : (1:ℝ) ≤ (d:ℝ)^2 := by nlinarith
  have hd4 : (1:ℝ) ≤ (d:ℝ)^4 := by nlinarith [sq_nonneg ((d:ℝ)^2-1)]
  have hU6 : (1:ℝ) ≤ (U:ℝ)^6 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hU' 6
    simpa only [one_pow] using h
  have hbig : (1:ℝ) ≤ (d:ℝ)^4*(U:ℝ)^6 := by nlinarith
  have hplus : ((U:ℝ)+1)^6 ≤ (2*(U:ℝ))^6 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 6
  calc
    _ ≤ (3*(d:ℝ)^2)*4*(d:ℝ)^2*(2*(U:ℝ))^6+2 := by
      have hc : (1+2*(d:ℝ)^2)*4*(d:ℝ)^2 ≤ (3*(d:ℝ)^2)*4*(d:ℝ)^2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by nlinarith :
          1+2*(d:ℝ)^2 ≤ 3*(d:ℝ)^2) (by norm_num)) (sq_nonneg _)
      exact add_le_add (mul_le_mul hc hplus (by positivity) (by positivity)) le_rfl
    _ = 768*(d:ℝ)^4*(U:ℝ)^6+2 := by ring
    _ ≤ _ := by nlinarith

end ContingencyTables.FiniteExposureVariance

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteSupportVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing zero-weight states preserves finite weighted variance -/

namespace ContingencyTables.FiniteExposureVariance

open scoped BigOperators Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- An injective encoding may omit only states of weight zero. -/
theorem sum_support_embedding (e : X → Y) (he : Function.Injective e)
    (w : Y → ℝ) (hw : ∀ y ∉ Set.range e,w y=0) (H : Y → ℝ) :
    (∑ x,w (e x)*H (e x))=∑ y,w y*H y := by
  apply Fintype.sum_of_injective e he _ _
  · intro y hy
    rw [hw y hy,zero_mul]
  · intro x
    rfl

theorem mean_support_embedding (e : X → Y) (he : Function.Injective e)
    (w : Y → ℝ) (hw : ∀ y ∉ Set.range e,w y=0) (H : Y → ℝ) :
    mean (fun x => w (e x)) (fun x => H (e x))=mean w H := by
  have hm : (∑ x,w (e x))=∑ y,w y :=
    Fintype.sum_of_injective e he _ _ hw (fun _ => rfl)
  unfold mean
  rw [sum_support_embedding e he w hw H,hm]

theorem variance_support_embedding (e : X → Y) (he : Function.Injective e)
    (w : Y → ℝ) (hw : ∀ y ∉ Set.range e,w y=0) (H : Y → ℝ) :
    variance (fun x => w (e x)) (fun x => H (e x))=variance w H := by
  unfold variance
  rw [mean_support_embedding e he w hw H]
  exact sum_support_embedding e he w hw (fun y => (H y-mean w H)^2)

omit [Fintype Y] in
/-- In particular, restriction to the strictly positive support does not
change any weighted variance, including the empty-support case. -/
theorem variance_positive_support (w H : X → ℝ) (hw : ∀ x,0 ≤ w x) :
    variance (fun x : {x // 0 < w x} => w x.val)
      (fun x => H x.val)=variance w H := by
  apply variance_support_embedding Subtype.val Subtype.val_injective w
  intro x hx
  have hn : ¬0 < w x := by
    intro hp
    exact hx ⟨⟨x,hp⟩,rfl⟩
  exact le_antisymm (le_of_not_gt hn) (hw x)

end ContingencyTables.FiniteExposureVariance

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteRepairDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite list of designated and inverse repair neighbors -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped Classical

variable {X D T : Type*} [Fintype D] [Fintype T]

omit [Fintype T] in
/-- If the source encoding is injective there is at most one outgoing
repair at a fixed state. -/
theorem outgoing_repair_card_le (x y : D → X) (hx : Function.Injective x) (v : X) :
    ((Finset.univ.filter (fun d => x d=v)).image y).card ≤ 1 := by
  have hsmall : (Finset.univ.filter (fun d => x d=v)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact hx ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
  exact Finset.card_image_le.trans hsmall

/-- The ordered defect type and repaired profile identify the source.
Consequently a fixed target has at most one inverse repair of each type. -/
theorem incoming_repair_card_le (x y : D → X) (label : D → T)
    (h : Function.Injective (fun d => (label d,y d))) (v : X) :
    ((Finset.univ.filter (fun d => y d=v)).image x).card ≤ Fintype.card T := by
  let S := {d : D // y d=v}
  have hlabel : Function.Injective (fun d : S => label d.val) := by
    intro a b he
    apply Subtype.ext
    exact h (Prod.ext he (a.property.trans b.property.symm))
  have hcard : Fintype.card S ≤ Fintype.card T := Fintype.card_le_of_injective _ hlabel
  have he : (Finset.univ.filter (fun d => y d=v)).card=Fintype.card S := by
    symm
    exact Fintype.card_subtype _
  exact Finset.card_image_le.trans (he.le.trans hcard)

noncomputable def repairNeighbors (x y : D → X) (v : X) : Finset X :=
  ((Finset.univ.filter (fun d => x d=v)).image y) ∪
    ((Finset.univ.filter (fun d => y d=v)).image x)

omit [Fintype T] in
lemma mem_repairNeighbors_forward (x y : D → X) (v : X) (d : D) (h : x d=v) :
    y d ∈ repairNeighbors x y v := by
  unfold repairNeighbors
  exact Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨d,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩)

omit [Fintype T] in
lemma mem_repairNeighbors_reverse (x y : D → X) (v : X) (d : D) (h : y d=v) :
    x d ∈ repairNeighbors x y v := by
  unfold repairNeighbors
  exact Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨d,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩)

theorem repairNeighbors_card_le (x y : D → X) (hx : Function.Injective x) (label : D → T)
    (h : Function.Injective (fun d => (label d,y d))) (v : X) :
    (repairNeighbors x y v).card ≤ 1+Fintype.card T := by
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add (outgoing_repair_card_le x y hx v) (incoming_repair_card_le x y label h v))

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteSupportEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricting a finite weighted graph to its positive states -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical

variable {X Y : Type*} [Fintype X]

omit [Fintype X] in
lemma pairTerm_eq_zero_left (f H : Y → ℝ) (hf : ∀ y,0 ≤ f y) (a b : Y)
    (ha : f a=0) : pairTerm f H (a,b)=0 := by
  simp only [pairTerm,ha,min_eq_left (hf b),zero_mul]

omit [Fintype X] in
lemma pairTerm_eq_zero_right (f H : Y → ℝ) (hf : ∀ y,0 ≤ f y) (a b : Y)
    (hb : f b=0) : pairTerm f H (a,b)=0 := by
  simp only [pairTerm,hb,min_eq_right (hf a),zero_mul]

/-- Only endpoints with nonzero weight need to occur in the embedding.
The ambient graph may still contain zero-weight vertices. -/
theorem symmetricEnergy_restrict (E : Finset (Y×Y)) (f H : Y → ℝ)
    (hf : ∀ y,0 ≤ f y) (i : X → Y) (hi : Function.Injective i)
    (hsupport : ∀ p ∈ E,(f p.1≠0 → ∃ x,i x=p.1) ∧ (f p.2≠0 → ∃ x,i x=p.2)) :
    symmetricEnergy E f H=
      (∑ x,∑ y,if (i x,i y) ∈ E then
        min (f (i x)) (f (i y))*(H (i x)-H (i y))^2 else 0)/2 := by
  let j : X×X → Y×Y := fun p => (i p.1,i p.2)
  let S := (Finset.univ : Finset (X×X)).filter (fun p => j p ∈ E)
  have hj : Function.Injective j := by
    intro a b h
    exact Prod.ext (hi (congrArg Prod.fst h)) (hi (congrArg Prod.snd h))
  have hsub : S.image j ⊆ E := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_filter.mp hq).2
  have hz (p : Y×Y) (hp : p ∈ E) (hn : p ∉ S.image j) : pairTerm f H p=0 := by
    by_cases h₁ : f p.1=0
    · exact pairTerm_eq_zero_left f H hf p.1 p.2 h₁
    by_cases h₂ : f p.2=0
    · exact pairTerm_eq_zero_right f H hf p.1 p.2 h₂
    obtain ⟨x,hx⟩ := (hsupport p hp).1 h₁
    obtain ⟨y,hy⟩ := (hsupport p hp).2 h₂
    have he : j (x,y)=p := Prod.ext hx hy
    exact False.elim (hn (Finset.mem_image.mpr ⟨(x,y),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [he]; exact hp⟩,he⟩))
  unfold symmetricEnergy
  rw [← Finset.sum_subset hsub hz,Finset.sum_image (fun a _ b _ h => hj h)]
  dsimp only [S]
  rw [Finset.sum_filter,Fintype.sum_prod_type]
  rfl

theorem symmetricEnergy_restrict_observable (E : Finset (Y×Y)) (f H : Y → ℝ)
    (hf : ∀ y,0 ≤ f y) (i : X → Y) (hi : Function.Injective i)
    (hsupport : ∀ p ∈ E,(f p.1≠0 → ∃ x,i x=p.1) ∧ (f p.2≠0 → ∃ x,i x=p.2))
    (h : X → ℝ) (hh : ∀ x,H (i x)=h x) :
    symmetricEnergy E f H=
      (∑ x,∑ y,if (i x,i y) ∈ E then
        min (f (i x)) (f (i y))*(h x-h y)^2 else 0)/2 := by
  rw [symmetricEnergy_restrict E f H hf i hi hsupport]
  simp_rw [hh]

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallChainBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual first-paper small-chain constants -/

namespace ContingencyTables

lemma small_chain_poincare_constant (d : ℕ) (hd : 14 ≤ d) :
    128*(d:ℝ)^2*(770*(d:ℝ)^4*((d^20:ℕ):ℝ)^6) ≤ (d:ℝ)^160 := by
  have hcoef : (98560:ℝ) ≤ (d:ℝ)^34 := by
    exact_mod_cast (show 98560 ≤ d^34 from
      (by norm_num : 98560 ≤ 14^34).trans (Nat.pow_le_pow_left hd 34))
  calc
    _ = 98560*(d:ℝ)^126 := by push_cast; ring
    _ ≤ (d:ℝ)^34*(d:ℝ)^126 := mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = _ := by ring

lemma completion_rejection_lt_half (d : ℕ) (hd : 14 ≤ d) :
    40*(d:ℝ)^5/((d^12:ℕ):ℝ) < 1/2 := by
  have hpos : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hp : (80:ℝ) < (d:ℝ)^7 := by
    exact_mod_cast (show 80 < d^7 from
      lt_of_lt_of_le (by norm_num : 80 < 14^7) (Nat.pow_le_pow_left hd 7))
  have hmul : 80*(d:ℝ)^5 < (d:ℝ)^12 := by
    calc
      _ < (d:ℝ)^7*(d:ℝ)^5 := mul_lt_mul_of_pos_right hp (pow_pos hpos 5)
      _ = _ := by ring
  push_cast
  apply (div_lt_iff₀ (pow_pos hpos 12)).mpr
  linarith

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallProposal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's exact dyadic small-chain proposal -/

namespace ContingencyTables

noncomputable def smallProposal (d : ℕ) : ℝ := 1/(2:ℝ)^(Nat.clog 2 (32*d^2))

lemma smallProposal_bounds (d : ℕ) (hd : 1 ≤ d) :
    0 < smallProposal d ∧ 1/(64*(d:ℝ)^2) ≤ smallProposal d ∧
      smallProposal d ≤ 1/(32*(d:ℝ)^2) := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hn : 1 < 32*d^2 := by nlinarith
  have hlo := Nat.le_pow_clog (by decide : 1 < 2) (32*d^2)
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hn
  have he : 2^Nat.clog 2 (32*d^2) = 2^(Nat.clog 2 (32*d^2)).pred*2 := by
    conv_lhs => rw [← Nat.succ_pred_eq_of_pos (Nat.clog_pos (by decide : 1 < 2) hn)]
    exact pow_succ _ _
  have hhi : 2^Nat.clog 2 (32*d^2) ≤ 64*d^2 := by rw [he]; omega
  have hloR : 32*(d:ℝ)^2 ≤ (2:ℝ)^Nat.clog 2 (32*d^2) := by exact_mod_cast hlo
  have hhiR : (2:ℝ)^Nat.clog 2 (32*d^2) ≤ 64*(d:ℝ)^2 := by exact_mod_cast hhi
  refine ⟨by unfold smallProposal; positivity,?_,?_⟩
  · exact one_div_le_one_div_of_le (by positivity) hhiR
  · exact one_div_le_one_div_of_le (by positivity) hloR

lemma smallProposal_degree (d : ℕ) (hd : 1 ≤ d) :
    ((5*d^2+1:ℕ):ℝ)*smallProposal d ≤ 1/2 := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hsq : (1:ℝ) ≤ (d:ℝ)^2 := by exact_mod_cast (show 1 ≤ d^2 by nlinarith)
  have hm := mul_le_mul_of_nonneg_left (smallProposal_bounds d hd).2.2
    (show (0:ℝ) ≤ (5*d^2+1:ℕ) by positivity)
  apply hm.trans
  rw [mul_one_div]
  apply (div_le_iff₀ (show (0:ℝ) < 32*(d:ℝ)^2 by positivity)).mpr
  push_cast
  nlinarith

lemma smallProposal_poincare_budget (d : ℕ) (hd : 14 ≤ d) :
    2*(770*(d:ℝ)^4*((d^20:ℕ):ℝ)^6)/smallProposal d ≤ (d:ℝ)^160 := by
  have hp := smallProposal_bounds d (by omega)
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hrecip : 1/smallProposal d ≤ 64*(d:ℝ)^2 := by
    apply (div_le_iff₀ hp.1).mpr
    have hh := (div_le_iff₀ (show (0:ℝ) < 64*(d:ℝ)^2 by positivity)).mp hp.2.1
    nlinarith
  calc
    _ = (2*(770*(d:ℝ)^4*((d^20:ℕ):ℝ)^6))*(1/smallProposal d) := by ring
    _ ≤ (2*(770*(d:ℝ)^4*((d^20:ℕ):ℝ)^6))*(64*(d:ℝ)^2) :=
      mul_le_mul_of_nonneg_left hrecip (by positivity)
    _ = 128*(d:ℝ)^2*(770*(d:ℝ)^4*((d^20:ℕ):ℝ)^6) := by ring
    _ ≤ _ := small_chain_poincare_constant d hd

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteExchangeObservables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unit exchanges change each selected coordinate sum by at most two -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical
open FactorialSignatures

variable {C : Type*} [Fintype C] [DecidableEq C]

noncomputable def linearObservable (a : C → ℤ) (z : C → ℕ) : ℤ := ∑ k,a k*(z k:ℤ)

end ContingencyTables.IntegerWeightedTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalExchangeMargins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual padded residual margins change by at most two on exchange edges -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextFibres IntegerWeightedTransport

lemma nat_residual_difference (r P A B : ℕ) (hA : A ≤ r) (hB : B ≤ r) :
    |((r-A+P:ℕ):ℤ)-((r-B+P:ℕ):ℤ)|=|(A:ℤ)-B| := by
  rw [Nat.cast_add,Nat.cast_add,Nat.cast_sub hA,Nat.cast_sub hB]
  have he : (r:ℤ)-A+P-((r:ℤ)-B+P) = -((A:ℤ)-B) := by ring
  rw [he,abs_neg]

universe u

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperSmallKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact rational law of the actual small-state completion chain -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open ResidualMixture FirstSuccess

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def smallProposalRat (d : ℕ) : ℚ := 1/(2:ℚ)^Nat.clog 2 (32*d^2)

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_TableMarginTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Changing equal margin descriptions without changing entries -/

namespace ContingencyTables
variable {I J : Type*} [Fintype I] [Fintype J]

def tableMarginTransport (r r' : I → ℕ) (c c' : J → ℕ)
    (hr : r=r') (hc : c=c') : Table r c ≃ Table r' c' where
  toFun X := ⟨X.val,by rw [←hr,←hc]; exact X.property⟩
  invFun X := ⟨X.val,by rw [hr,hc]; exact X.property⟩
  left_inv X := rfl
  right_inv X := rfl

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteDependentLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact joint laws with a finite state-dependent completion space -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture

variable {X : Type*} {Y : X → Type*} [Fintype X] [∀ x,Fintype (Y x)]

variable [Nonempty X] [∀ x,Nonempty (Y x)]

instance dependentJointNonempty : Nonempty ((x : X) × Y x) :=
  ⟨⟨Classical.choice ‹Nonempty X›, Classical.choice (inferInstance : Nonempty (Y (Classical.choice ‹Nonempty X›)))⟩⟩

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_GreedyFeasibleTable
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A dimension-recursive feasible table constructor

The constructor removes a column on each inner call and a row on each
outer call. Large binary margins are never processed one unit at a time.
-/

namespace ContingencyTables.GreedyFeasibleTable

open scoped BigOperators

structure RowSplit (n : ℕ) where
  assigned : Fin n → ℕ
  remaining : Fin n → ℕ
  unused : ℕ

def splitRow : {n : ℕ} → ℕ → (Fin n → ℕ) → RowSplit n
  | 0,a,_ => ⟨Fin.elim0,Fin.elim0,a⟩
  | _n+1,a,c =>
    let b := min a (c 0)
    let tail := splitRow (a-b) (fun i => c i.succ)
    ⟨Fin.cons b tail.assigned,Fin.cons (c 0-b) tail.remaining,tail.unused⟩

lemma splitRow_columns {n : ℕ} (a : ℕ) (c : Fin n → ℕ) (i : Fin n) :
    (splitRow a c).assigned i+(splitRow a c).remaining i=c i := by
  induction n generalizing a with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [splitRow,Fin.cons_zero]
      omega
    · simpa only [splitRow,Fin.cons_succ] using ih (a-min a (c 0)) (fun j => c j.succ) j

lemma splitRow_balance {n : ℕ} (a : ℕ) (c : Fin n → ℕ) :
    (∑ i,(splitRow a c).assigned i)+(splitRow a c).unused=a := by
  induction n generalizing a with
  | zero => simp [splitRow]
  | succ n ih =>
    have ht := ih (a-min a (c 0)) (fun j => c j.succ)
    simp only [splitRow,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
    omega

lemma splitRow_unused {n : ℕ} (a : ℕ) (c : Fin n → ℕ) :
    (splitRow a c).unused=a-∑ i,c i := by
  induction n generalizing a with
  | zero => simp [splitRow]
  | succ n ih =>
    simpa only [splitRow,Fin.sum_univ_succ] using
      (ih (a-min a (c 0)) (fun j => c j.succ)).trans (by omega)

lemma splitRow_sum {n : ℕ} (a : ℕ) (c : Fin n → ℕ) (ha : a ≤ ∑ i,c i) :
    (∑ i,(splitRow a c).assigned i)=a := by
  have hb := splitRow_balance a c
  rw [splitRow_unused,Nat.sub_eq_zero_of_le ha,add_zero] at hb
  exact hb

lemma splitRow_remaining_sum {n : ℕ} (a : ℕ) (c : Fin n → ℕ) :
    (∑ i,(splitRow a c).remaining i)=(∑ i,c i)-a := by
  have hc : (∑ i,(splitRow a c).assigned i)+(∑ i,(splitRow a c).remaining i)=∑ i,c i := by
    rw [←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => splitRow_columns a c i)
  have hb := splitRow_balance a c
  rw [splitRow_unused] at hb
  omega

def matrix : {m n : ℕ} → (Fin m → ℕ) → (Fin n → ℕ) → Fin m → Fin n → ℕ
  | 0,_,_,_ => Fin.elim0
  | _m+1,_,r,c =>
    let row := splitRow (r 0) c
    Fin.cons row.assigned (matrix (fun i => r i.succ) row.remaining)

/-- The arithmetic constructor fills any equal-total natural margins. -/
theorem matrix_hasMargins {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (htotal : (∑ i,r i)=∑ j,c j) : HasMargins (matrix r c) r c := by
  induction m generalizing c with
  | zero =>
    constructor
    · intro i
      exact Fin.elim0 i
    · intro j
      have hc : c j ≤ ∑ k,c k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      simp only [Fin.sum_univ_zero] at htotal
      simp only [Fin.sum_univ_zero]
      omega
  | succ m ih =>
    have ha : r 0 ≤ ∑ j,c j := by
      rw [Fin.sum_univ_succ] at htotal
      omega
    have htail : (∑ i : Fin m,r i.succ)=∑ j,(splitRow (r 0) c).remaining j := by
      rw [splitRow_remaining_sum]
      rw [Fin.sum_univ_succ] at htotal
      omega
    have hm := ih (fun i => r i.succ) (splitRow (r 0) c).remaining htail
    constructor
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa only [matrix,Fin.cons_zero] using splitRow_sum (r 0) c ha
      · simpa only [matrix,Fin.cons_succ] using hm.1 i
    · intro j
      simpa only [matrix,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,hm.2 j] using
        splitRow_columns (r 0) c j

/-- A literal, dimension-recursive fallback for the sampling algorithm. -/
def table {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (htotal : (∑ i,r i)=∑ j,c j) : Table r c := ⟨matrix r c,matrix_hasMargins r c htotal⟩

end ContingencyTables.GreedyFeasibleTable

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseAxisBits
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact proposal frequencies from a bounded fair-bit integer -/

namespace ContingencyTables.GridBoundary

open scoped Classical

theorem dense_proposal_code_bound (d q : ℕ) (hq : q ≤ d) :
    q * 2 ≤ 2 ^ Nat.clog 2 (8 * d) := by
  exact (by omega : q * 2 ≤ 8 * d).trans (Nat.le_pow_clog (by decide) (8 * d))

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_DyadicAcceptance
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite-bit Metropolis acceptance

A uniform integer encoded by the allotted fair bits is compared with a
power of two. Extra bits are padding; their number does not change the
acceptance probability.
-/

namespace ContingencyTables.FairBits

open scoped BigOperators

abbrev acceptDyadic (gap allowance : ℕ) (z : Fin (2 ^ allowance)) : Prop :=
  z.val < 2 ^ (allowance - gap)

theorem acceptDyadic_count (gap allowance : ℕ) :
    (Finset.univ.filter (acceptDyadic gap allowance)).card = 2 ^ (allowance - gap) := by
  change (Finset.univ.filter (fun z : Fin (2 ^ allowance) => z.val < 2 ^ (allowance - gap))).card = _
  rw [Fin.card_filter_val_lt, min_eq_right]
  exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)

theorem acceptDyadic_probability (gap allowance : ℕ) (h : gap ≤ allowance) :
    ((Finset.univ.filter (acceptDyadic gap allowance)).card : ℝ) / (2 : ℝ) ^ allowance =
      1 / (2 : ℝ) ^ gap := by
  rw [acceptDyadic_count gap allowance, Nat.cast_pow, Nat.cast_ofNat]
  have ha : allowance = (allowance - gap) + gap := by omega
  have hden : (2 : ℝ) ^ allowance = 2 ^ (allowance - gap) * 2 ^ gap := by
    conv_lhs => rw [ha, pow_add]
  rw [hden]
  simpa only [one_div] using div_mul_cancel_left₀
    (by positivity : (2 : ℝ) ^ (allowance - gap) ≠ 0) ((2 : ℝ) ^ gap)

theorem dyadic_ratio_min (a b : ℕ) :
    min (1 : ℝ) ((1 / (2 : ℝ) ^ b) / (1 / (2 : ℝ) ^ a)) =
      1 / (2 : ℝ) ^ (b - a) := by
  by_cases hab : a ≤ b
  · have he : b = a + (b - a) := by omega
    have hr : ((1 / (2 : ℝ) ^ b) / (1 / (2 : ℝ) ^ a)) = 1 / (2 : ℝ) ^ (b - a) := by
      conv_lhs => rw [he, pow_add]
      field_simp
    rw [hr, min_eq_right]
    simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (show (1 : ℝ) ≤ 2 ^ (b - a) from one_le_pow₀ (by norm_num))
  · have hba : b ≤ a := by omega
    have he : a = b + (a - b) := by omega
    have hr : ((1 / (2 : ℝ) ^ b) / (1 / (2 : ℝ) ^ a)) = (2 : ℝ) ^ (a - b) := by
      conv_lhs => rw [he, pow_add]
      field_simp
    rw [hr, Nat.sub_eq_zero_of_le hba, pow_zero, div_one, min_eq_left]
    exact one_le_pow₀ (by norm_num)

end ContingencyTables.FairBits

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteMetropolis
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite proposal-and-acceptance experiments -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture

noncomputable section

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
variable [DecidableEq α] [Nonempty β] [Nonempty γ]

def finiteAcceptStep (a : α) (proposal : β → Option α) (accept : α → γ → Prop)
    (z : β × γ) : α :=
  match proposal z.1 with
  | none => a
  | some b => if accept b z.2 then b else a

omit [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [Nonempty β] [Nonempty γ] in
theorem finiteAcceptStep_eq_iff (a b : α) (proposal : β → Option α) (accept : α → γ → Prop)
    (z : β × γ) (hab : a ≠ b) :
    finiteAcceptStep a proposal accept z = b ↔ proposal z.1 = some b ∧ accept b z.2 := by
  cases hp : proposal z.1 with
  | none => simp [finiteAcceptStep, hp, hab]
  | some c =>
    by_cases hcb : c = b
    · subst c
      simp [finiteAcceptStep, hp, hab]
    · by_cases hc : accept c z.2 <;> simp [finiteAcceptStep, hp, hc, hcb, hab]

end

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseBooleanTrial
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full dense trial as one bounded unbiased Boolean word -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical
open ResidualMixture FirstSuccess FairBits

noncomputable section

def dependentWordEquiv {q : ℕ} (k : Fin q → ℕ) :
    (Fin (∑ j, k j) → Bool) ≃ (∀ j, Fin (k j) → Bool) :=
  (Equiv.arrowCongr finSigmaFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.piCurry (fun _ _ => Bool))

end

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseErrorArithmetic
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Error budget of the bounded dense rejection schedule -/

namespace ContingencyTables.GridBoundary

theorem succ_le_two_pow (h : ℕ) : h + 1 ≤ 2 ^ h := by
  exact Nat.succ_le_of_lt Nat.lt_two_pow_self

theorem square_le_two_pow (d : ℕ) (hd : 4 ≤ d) : d ^ 2 ≤ 2 ^ d := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ d hd ih =>
    calc
      (d + 1) ^ 2 ≤ 2 * d ^ 2 := by nlinarith
      _ ≤ 2 * 2 ^ d := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (d + 1) := by rw [pow_succ, Nat.mul_comm]

theorem dense_trial_error_budget (d h : ℕ) (hd : 14 ≤ d) :
    ((d ^ 4 * (h + 1) * (1 + d) : ℕ) : ℝ) *
      (2 : ℝ) ^ (-(4 * ((h : ℝ) + d))) ≤ (2 : ℝ) ^ (-(h : ℝ) - 2) := by
  have hd2 : (d : ℝ) ^ 2 ≤ (2 : ℝ) ^ d := by exact_mod_cast square_le_two_pow d (by omega)
  have hd4 : (d : ℝ) ^ 4 ≤ (2 : ℝ) ^ (2 * d) := by
    calc
      _ = ((d : ℝ) ^ 2) ^ 2 := by ring
      _ ≤ ((2 : ℝ) ^ d) ^ 2 := pow_le_pow_left₀ (by positivity) hd2 _
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have hh : (h : ℝ) + 1 ≤ (2 : ℝ) ^ h := by
    exact_mod_cast succ_le_two_pow h
  have hd1 : (1 : ℝ) + d ≤ (2 : ℝ) ^ d := by
    exact_mod_cast (show 1 + d ≤ 2 ^ d by simpa only [Nat.add_comm] using succ_le_two_pow d)
  have hprod : ((d ^ 4 * (h + 1) * (1 + d) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ ((h : ℝ) + 3 * d) := by
    push_cast
    calc
      _ ≤ (2 : ℝ) ^ (2 * d) * (2 : ℝ) ^ h * (2 : ℝ) ^ d := by gcongr
      _ = _ := by
        rw [← pow_add, ← pow_add, ← Real.rpow_natCast]
        congr 1
        push_cast
        ring
  calc
    _ ≤ (2 : ℝ) ^ ((h : ℝ) + 3 * d) * (2 : ℝ) ^ (-(4 * ((h : ℝ) + d))) :=
      mul_le_mul_of_nonneg_right hprod (by positivity)
    _ = (2 : ℝ) ^ (-(3 * (h : ℝ) + d)) := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      have hd' : (14 : ℝ) ≤ d := by exact_mod_cast hd
      have hh' : (0 : ℝ) ≤ h := Nat.cast_nonneg _
      linarith)

theorem dense_failure_error_budget (d h : ℕ) (hd : 14 ≤ d) :
    (63 / 64 : ℝ) ^ (d ^ 4 * (h + 1)) ≤ (2 : ℝ) ^ (-(h : ℝ) - 2) := by
  have hd4 : 128 ≤ d ^ 4 := by nlinarith [show 14 ^ 4 ≤ d ^ 4 from Nat.pow_le_pow_left hd _]
  have hs : (63 / 64 : ℝ) ≤ Real.exp (-(1 / 64 : ℝ)) := by
    linarith [Real.add_one_le_exp (-(1 / 64 : ℝ))]
  calc
    _ ≤ (Real.exp (-(1 / 64 : ℝ))) ^ (d ^ 4 * (h + 1)) :=
      pow_le_pow_left₀ (by norm_num) hs _
    _ = Real.exp (-(((d ^ 4 * (h + 1) : ℕ) : ℝ) / 64)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (-(2 * ((h : ℝ) + 1))) := by
      apply Real.exp_le_exp.mpr
      have h' : (128 : ℝ) ≤ (d : ℝ) ^ 4 := by exact_mod_cast hd4
      push_cast
      nlinarith [show (0 : ℝ) ≤ h from Nat.cast_nonneg h]
    _ ≤ (2 : ℝ) ^ (-(2 * ((h : ℝ) + 1))) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      apply Real.exp_le_exp.mpr
      have hl : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hh' : (0 : ℝ) ≤ h := Nat.cast_nonneg _
      nlinarith
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      have hh' : (0 : ℝ) ≤ h := Nat.cast_nonneg _
      linarith)

theorem dense_total_error_budget (d h : ℕ) (hd : 14 ≤ d) :
    (63 / 64 : ℝ) ^ (d ^ 4 * (h + 1)) +
      ((d ^ 4 * (h + 1) * (1 + d) : ℕ) : ℝ) *
        (2 : ℝ) ^ (-(4 * ((h : ℝ) + d))) ≤ (2 : ℝ) ^ (-(h : ℝ)) := by
  have hf := dense_failure_error_budget d h hd
  have ht := dense_trial_error_budget d h hd
  have heq : (2 : ℝ) ^ (-(h : ℝ) - 2) = (2 : ℝ) ^ (-(h : ℝ)) / 4 := by
    rw [Real.rpow_sub (by norm_num)]
    norm_num
  rw [heq] at hf ht
  linarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-(h : ℝ))]

end ContingencyTables.GridBoundary

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteWordRejection
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Repeated rejection implemented by one finite independent Boolean array -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture FairBits

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

def wordRetry {k : ℕ} (f : (Fin k → Bool) → Option α) (fallback : α) :
    (n : ℕ) → (Fin n → Fin k → Bool) → α
  | 0, _ => fallback
  | n + 1, bits => (f (bits 0)).getD (wordRetry f fallback n (Fin.tail bits))

end

end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ListBitProposal
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dyadic proposals from an explicit list without repeated entries -/

namespace ContingencyTables.FairBits
open scoped BigOperators Classical
open ResidualMixture FirstSuccess

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [Fintype X] [DecidableEq X] in
lemma listIndex_eq_iff (xs : List X) (hn : xs.Nodup) (k : ℕ)
    (hlen : xs.length ≤ 2^k) (i : ℕ) (hi : i<xs.length)
    (b : Fin (2^k)) : xs[b.val]?=some xs[i] ↔ b=⟨i,hi.trans_le hlen⟩ := by
  constructor
  · intro hb
    obtain ⟨hb,hval⟩ := List.getElem?_eq_some_iff.mp hb
    apply Fin.ext
    exact hn.getElem_inj_iff.mp hval
  · intro hb
    subst b
    exact List.getElem?_eq_getElem hi

end ContingencyTables.FairBits

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeListMore
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B X : Type}

def listMin (x : List ℕ×ℕ) : ℕ := x.1.foldl min x.2
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallProfileCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal lists encode exactly the positive physical states -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres
open ProfilePrograms

noncomputable section
variable {m n q : ℕ}
  (small : Fin m → Fin n → Bool)

lemma ofFn_getD (xs : List ℕ) (h : xs.length=q) :
    List.ofFn (fun i : Fin q => xs.getD i.val 0)=xs := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using h.symm
  · intro i hi hj
    simp only [List.getElem_ofFn,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,
      Option.getD_some]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileCodeEquality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial equality and duplicate removal for profile codes -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

def listEntryEqual (z : (List ℕ×List ℕ)×ℕ) : Bool :=
  decide (z.1.1.getD z.2 0=z.1.2.getD z.2 0)

def listNatTest (z : List ℕ×List ℕ) : Bool :=
  decide (z.1.length=z.2.length) &&
    (List.range z.1.length).all (fun i => listEntryEqual (z,i))

lemma listNatTest_iff (z : List ℕ×List ℕ) : listNatTest z=true ↔ z.1=z.2 := by
  rcases z with ⟨xs,ys⟩
  simp only [listNatTest,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_range,
    listEntryEqual]
  constructor
  · rintro ⟨hlen,h⟩
    apply List.ext_getElem hlen
    intro i hi hj
    have he := h i hi
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem hj,Option.getD_some,decide_eq_true_eq] using he
  · rintro rfl
    simp

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperProposal
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The explicit small-state proposal realizes the proved ideal kernel -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open ResidualMixture FirstSuccess

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)

lemma smallProposalRat_cast (n : ℕ) : (smallProposalRat n:ℝ)=smallProposal n := by
  simp only [smallProposalRat,smallProposal,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperCodeProposal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The compiled neighbor draw has the small-chain proposal law -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres
open ProfilePrograms FirstSuccess FairBits

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

lemma getElem_filterMap_total {A C : Type*} (f : A → Option C) (xs : List A)
    (h : ∀ a∈xs,∃ b,f a=some b) (i : ℕ) :
    (xs[i]?).bind f=(xs.filterMap f)[i]? := by
  induction xs generalizing i with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨b,hb⟩ := h a (by simp)
    have ht : ∀ a∈xs,∃ b,f a=some b := fun a ha => h a (by simp [ha])
    cases i with
    | zero => simp [hb]
    | succ i => simpa only [List.getElem?_cons_succ,List.filterMap_cons,hb] using ih ht i

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperPreparedProposal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparing the complete proposal input from binary margin lists -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def marginDimension (z : List ℕ×List ℕ) : ℕ := 10+(z.1.length+1)*(z.2.length+1)

def marginThreshold (z : List ℕ×List ℕ) : ℕ := (marginDimension z)^20

abbrev RawProfileInput := (List ℕ×List ℕ)×(List ℕ×List ℕ)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_DependentWordProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Splitting a binary word at input-dependent coordinate widths -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

def chunkIndices (z : List ℕ×List Bool) : List ℕ := List.range z.1.length

open scoped BigOperators

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestRootPenalty
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual root residuals of the integral forest completion

Summing a root-path flow gives the prescribed demand minus the total
demand in the component. This formula also applies at roots and on
singleton components, where the nonroot-only margin lemma is vacuous.
-/

namespace ContingencyTables.ForestRootPenalty

open scoped BigOperators Classical
open SimpleGraph

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def smallDemand (small : I → J → Bool) (X x q : I → J → ℤ) : I⊕J → ℤ :=
  Sum.elim (fun i => ∑ j, if small i j then X i j-x i j else 0)
    (fun j => ∑ i, if small i j then q i j-X i j else 0)

end ContingencyTables.ForestRootPenalty

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FixedCardinalityLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sequential uniform sampling of a subset of prescribed size

The head is included with probability k/n; conditional on that choice,
the same rule is applied to the remaining coordinates. The exact mass
is k!(n-k)!/n!, matching the factorial factor in the companion lift.
-/

namespace ContingencyTables.FixedCardinalityLaw

open ResidualMixture FirstSuccess
open scoped BigOperators Classical
noncomputable section

def count {n : ℕ} (v : Fin n → Bool) : ℕ := ∑ i,if v i then 1 else 0

def factorialMass (n k : ℕ) : ℚ := (k.factorial:ℚ)*((n-k).factorial:ℚ)/(n.factorial:ℚ)

end
end ContingencyTables.FixedCardinalityLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteIndependentAverages
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concentration of averages of actual independent finite experiments -/

namespace ContingencyTables.FiniteIndependentAverages

open scoped BigOperators

noncomputable section

variable {X : Type*} [Fintype X] [Nonempty X]

def sampleSum (g : X → ℝ) (N : ℕ) (xs : Fin N → X) : ℝ := ∑ i,g (xs i)

def sampleAverage (g : X → ℝ) (N : ℕ) (xs : Fin N → X) : ℝ := sampleSum g N xs/N

end

end ContingencyTables.FiniteIndependentAverages

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_RealKernelApproximation
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Accumulating rational implementation errors against a real kernel

The exact companion weights may be real. The implemented probabilities
are rational; comparison takes place after their canonical real cast.
-/

namespace ContingencyTables.RealKernelApproximation
open scoped BigOperators Classical
open ResidualMixture FirstSuccess

noncomputable section
variable {X Y : Type*} [Fintype X] [Fintype Y]

def distance (p q : X → ℝ) : ℝ := (∑ x,|p x-q x|)/2

lemma distance_event (p q : X → ℝ) (hmass : ∑ x,p x=∑ x,q x) (S : Finset X) :
    |(∑ x∈S,p x)-(∑ x∈S,q x)| ≤ distance p q := by
  have hz : (∑ x ∈ S, (p x-q x))+(∑ x ∈ Sᶜ, (p x-q x))=0 := by
    rw [Finset.sum_add_sum_compl,Finset.sum_sub_distrib,hmass,sub_self]
  have hc : (∑ x ∈ Sᶜ, (p x-q x))= -(∑ x ∈ S, (p x-q x)) := by linarith
  have ha := Finset.abs_sum_le_sum_abs (fun x => p x-q x) S
  have hb := Finset.abs_sum_le_sum_abs (fun x => p x-q x) Sᶜ
  rw [hc,abs_neg] at hb
  have hs := add_le_add ha hb
  rw [Finset.sum_add_sum_compl] at hs
  rw [←Finset.sum_sub_distrib]
  unfold distance
  linarith

end
end ContingencyTables.RealKernelApproximation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_InitializationBrackets
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact local factorial sums for the companion's initial multipliers

These are the four brackets in the manuscript's exact initialization
formula. The full-pair case reduces to an explicitly evaluated quadratic
sum, so the rational initializer uses no factorial evaluation oracle.
-/

namespace ContingencyTables.InitializationBrackets

open scoped BigOperators
open Nat

noncomputable def bracket (b u v : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (b-u-v+1),
    ((b-u-v).choose k:ℝ)*((k+v)!:ℝ)*((b-u-v-k+v)!:ℝ))/(b !:ℝ)

end ContingencyTables.InitializationBrackets

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_InitialLocalChoices
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initialization brackets are actual sums over remaining row labels -/

namespace ContingencyTables.InitialLocalChoices

open scoped BigOperators Classical
open Nat
open InitializationBrackets

noncomputable def localWeight (b u v : ℕ) (S : Finset (Fin (b-u-v))) : ℝ :=
  ((S.card+v)!:ℝ)*((b-u-v-S.card+v)!:ℝ)/(b !:ℝ)

end ContingencyTables.InitialLocalChoices

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_InitialTransversals
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The initial transversal sum is an actual finite row-label choice sum

For every cell, a choice of row labels gives exactly one paired
transversal. Its factorial weight is the local factorial weight used in
the evaluated initialization brackets.
-/

namespace ContingencyTables.InitialTransversals

open scoped BigOperators Classical
open Nat
open TwoLiftStates InitialLocalChoices

variable {C : Type*} [Fintype C] (b : C → ℕ)

noncomputable def denominator : ℝ := ∏ c, ((b c)!:ℝ)

end ContingencyTables.InitialTransversals

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_DegreeCompletion
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Positive completion of a single valid degree

A fixed-degree weight is extended by the constant weight one on every
other degree. All off-degree signatures are proved, and all coefficient
sums at the original degree are unchanged. This lets the existing general
nonnegative-derivative theorem retain contracted coordinates without
assuming positivity or signatures of the original weight at other degrees.
-/

namespace ContingencyTables.DegreeCompletion

open scoped BigOperators Classical Topology

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

noncomputable def completeDegree (f : Set Γ → ℝ) (k : ℕ) (A : Set Γ) : ℝ :=
  if A.ncard = k then f A else 1

end ContingencyTables.DegreeCompletion

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ObservableBounds
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Observable and trace bounds on the actual valid-degree chain

Positive completion is used only to instantiate the existing finite-chain
constructor. All its state weights, conductances, and conditional projections
are proved equal to the original valid-degree quantities.
-/

namespace ContingencyTables.ObservableBounds

open scoped BigOperators Classical
open DegreeCompletion

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

/-- The manuscript's observable constant. -/
def observableConstant (p q : ℝ) : ℝ :=
  10*p^4*(9*(p*(1+8*p*q^2))+2*(8+32*p*q^3))

end ContingencyTables.ObservableBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_TreeMarginalSignature
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual one-tree physical marginal before the equality limit

One physical cell is retained as its doubled Boolean pair. Every other
physical cell, including small capacities zero and one, is summed at
balance. The resulting positive scalar sequence has the proved raw
log-concavity and finite interpolation bounds.
-/

namespace ContingencyTables.TreeMarginalSignature

open scoped BigOperators Classical Matrix Topology
open Filter ForestPenaltyApplication
open LargePairEnumeration EqualitySoftening IntegerWeightedTransport

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def keep (t a : I×J) : Bool := decide (a=t)

end ContingencyTables.TreeMarginalSignature

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_TransversalCount
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact binomial/factorial cancellation in a transversal normalizer

Every small integer profile has a product of binomial numbers of label
preimages. Its factorial lift contributes the inverse product, so the
actual transversal normalizer is exactly the raw integer-profile sum.
-/

namespace ContingencyTables.TransversalCount

open scoped BigOperators Classical
open TwoLiftStates InitialTransversals InitialLocalChoices

variable {C : Type*} [Fintype C] (b : C → ℕ)

noncomputable def cardAt (c : C) (S : Finset (Fin (b c))) : Fin (b c+1) :=
  ⟨S.card,by have h := Finset.card_le_univ S; simpa using Nat.lt_succ_of_le h⟩

end ContingencyTables.TransversalCount

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPhaseSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit scalar schedules for the adaptive counting phases

Every precision and sample length below is a rational or natural arithmetic
expression. In particular the dyadic exponents use a polynomial reciprocal
allowance, so no real logarithm is evaluated by the algorithm.
-/

namespace ContingencyTables.CountingPhaseSchedule

open scoped BigOperators

/-- Per-phase logarithmic tolerance. -/
def tolerance (H : ℕ) (epsilon : ℚ) : ℚ := epsilon/(800*(H+1))

def returnCap (p H tau : ℕ) : ℕ := 65536*(H+1)^2*(tau+1)*(p^2+1)

end ContingencyTables.CountingPhaseSchedule

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteUniformHistory
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact independent-word law of a finite adaptive-history experiment -/

namespace ContingencyTables.FiniteUniformHistory

open scoped BigOperators Classical

noncomputable section
variable {X : Type*} [Fintype X] [Nonempty X]

def kernel (_ : List X) (_ : X) : ℝ := 1/Fintype.card X

end
end ContingencyTables.FiniteUniformHistory

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_OffsetCountProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact binary tabulation of the bounded offset law -/

namespace ContingencyTables.OffsetCountPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

abbrev Input := (ℕ×ℕ)×ℕ

end ContingencyTables.OffsetCountPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_TableTightening
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous tightening and translation by attained cell minima

The hypotheses here are exactly the extremum properties proved for the
executed searches. The maps preserve all tables, with explicit inverse
addition and with both endpoints of every translated interval attained.
-/

namespace ContingencyTables.TableTightening

open scoped BigOperators

variable {m n : ℕ}

lemma lower_sums (X l : Fin m→Fin n→ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ)
    (hm : HasMargins X r c) (hl : ∀ i j,l i j≤X i j) :
    (∀ i,(∑ j,l i j) ≤ r i) ∧ (∀ j,(∑ i,l i j) ≤ c j) := by
  constructor
  · intro i
    rw [←hm.1 i]
    exact Finset.sum_le_sum (fun j _=>hl i j)
  · intro j
    rw [←hm.2 j]
    exact Finset.sum_le_sum (fun i _=>hl i j)

end ContingencyTables.TableTightening

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FirstSuccessProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial first-success selection for a supplied list of trial words -/

namespace ContingencyTables.FirstSuccessProgram
open MatchingFPRAS.TreeTyped

variable {A B W : Type}
  [Inhabited B]

def firstSome : List (Option B) → Option B
  | [] => none
  | none::xs => firstSome xs
  | Option.some x::_ => Option.some x

def retry (f : A×W → Option B) (z : (A×B)×List W) : B :=
  (firstSome (z.2.map (fun w => f (z.1.1,w)))).getD z.1.2

end ContingencyTables.FirstSuccessProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingBaseProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the capacity-bit and dimension inputs to the counting schedule -/

namespace ContingencyTables.CountingBaseProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

def cellBits (x : ℕ) : ℕ := (x+1).size

end ContingencyTables.CountingBaseProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PairedCatalogProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing paired-coordinate metadata from a binary profile

Consecutive coordinates are paired by the bounded list scan
(0,1),(2,3),.... This is the exact metadata of the canonical paired-label
order, rather than a catalog supplied as an external oracle.
-/

namespace ContingencyTables.PairedCatalogProgram

open MatchingFPRAS.TreeTyped ProfilePrograms

def pairList {α : Type*} : List α → List (α×Bool)
  | [] => []
  | a::xs => (a,false)::(a,true)::pairList xs

lemma pairList_length {α : Type*} (xs : List α) : (pairList xs).length=2*xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [pairList,List.length_cons,ih]; omega

end ContingencyTables.PairedCatalogProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PairedProfileProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reading the two cell counts from the actual paired code

The block widths come from the stored capacity list. Each count scans
only supplied code entries and clips them to one, including on malformed
input. No numeric capacity controls an unbounded allocation.
-/

namespace ContingencyTables.PairedProfileProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

def interleave : List (ℕ × ℕ) → List ℕ
  | [] => []
  | p :: ps => p.1 :: p.2 :: interleave ps

lemma interleave_length (xs : List (ℕ × ℕ)) : (interleave xs).length=2*xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [interleave,List.length_cons,ih]; omega

end ContingencyTables.PairedProfileProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_EstimatorWordBanks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact disjoint word layout of one weight estimator

There is one bank of ratio samples for every phase, followed by one bank
of correction samples. Each correction sample has its own walk and bin
words. This is the literal layout used by the executable allocator.
-/

namespace ContingencyTables.EstimatorWordBanks

open DensePrograms GridBoundary FairBits
open scoped Classical

abbrev Banks (j S r t b : ℕ) :=
  (Fin j → Fin S → Fin r → Bool) ×
    (Fin S → (Fin t → Bool) × (Fin b → Bool))

end ContingencyTables.EstimatorWordBanks

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_IntegerMatrixProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary integer matrix propagation for exact law tabulation -/

namespace ContingencyTables.IntegerMatrixPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators

def matrixTotal (B : List (List ℕ)) : ℕ := (B.map List.sum).sum

end ContingencyTables.IntegerMatrixPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorWordSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed estimator consumes exactly its independent sample banks -/

namespace ContingencyTables.RootedEstimatorWordProgram

open MatchingFPRAS
open DensePrograms GridBoundary
open scoped Classical

def recodeBanks {j S r t b r' t' b' : ℕ} (hr : r=r') (ht : t=t') (hb : b=b') :
    EstimatorWordBanks.Banks j S r t b ≃ EstimatorWordBanks.Banks j S r' t' b' :=
  Equiv.cast (by rw [hr,ht,hb])

end ContingencyTables.RootedEstimatorWordProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_RepeatedFractionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent repetition of a finite-word rational program

The public confidence amplification only groups bits already supplied
on the tape. Its binary count cannot cause an unbounded allocation.
-/

namespace ContingencyTables.RepeatedFractionProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

variable {X : Type}
abbrev Input (X : Type) := (X×(ℕ×ℕ))×List Bool

open GridBoundary

end ContingencyTables.RepeatedFractionProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingCoefficientBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numeric polynomial bounds for the computed terminal coefficient -/

namespace ContingencyTables.CountingCoefficientBounds
noncomputable section

open Polynomial

def coefficientPolynomial : Polynomial ℕ := 2048*X*(20*(3*X+1))^2*X

end
end ContingencyTables.CountingCoefficientBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingTerminalBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial numeric bounds for the three terminal controls -/

namespace ContingencyTables.CountingTerminalBounds
open Polynomial CountingCoefficientBounds
noncomputable section

def coefficientPolynomial : Polynomial ℕ := CountingCoefficientBounds.coefficientPolynomial.comp (2*X)
def gridPolynomial : Polynomial ℕ := 16*coefficientPolynomial*X^2
def cutoffPolynomial : Polynomial ℕ := 100*X*gridPolynomial
def phasePolynomial : Polynomial ℕ := 10*coefficientPolynomial*X^2*(cutoffPolynomial+1)

end
end ContingencyTables.CountingTerminalBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPublicInputBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounding counting parameters by the public binary input -/

namespace ContingencyTables.CountingPublicInputBounds
open MatchingFPRAS Algorithms
open scoped BigOperators
noncomputable section

def size {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon delta : ℚ) : ℕ :=
  (encodeCountingInput r c b epsilon delta).length+⌈epsilon⁻¹⌉₊+Nat.clog 2 ⌈delta⁻¹⌉₊+1

end
end ContingencyTables.CountingPublicInputBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingAmplifiedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact law and public word budget of outer confidence repetition -/
namespace ContingencyTables.CountingAmplifiedProgram
open MatchingFPRAS GridBoundary Polynomial CountingPublicInputBounds
open scoped Classical
noncomputable section

variable {m n : ℕ}

def budgetPolynomial (p : Polynomial ℕ) : Polynomial ℕ := 64*X*p

end
end ContingencyTables.CountingAmplifiedProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Sampling_Sym2Order
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

open Finset

variable {V L : Type*} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]

@[instance_reducible] def sym2Order : LinearOrder (Sym2 V) :=
  LinearOrder.lift' (fun e=>toLex (Sym2.sortEquiv e).val)
    (fun _ _ h=>Sym2.sortEquiv.injective (Subtype.ext (toLex.injective h)))

attribute [local instance] sym2Order

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Transport

open Finset

variable {V L : Type*} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]

variable {bags : V → Finset L}

attribute [local instance] sym2Order



open Finset

variable {V L : Type*} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]

variable {bags : V → Finset L} {G : SimpleGraph L}

attribute [local instance] sym2Order

@[instance_reducible] def prodOrder {A B : Type*} [LinearOrder A] [LinearOrder B] :
    LinearOrder (A×B) := LinearOrder.lift' toLex toLex.injective

@[instance_reducible] def sumOrder {A B : Type*} [LinearOrder A] [LinearOrder B] :
    LinearOrder (A⊕B) := LinearOrder.lift' toLex toLex.injective

attribute [local instance] prodOrder sumOrder



open Finset

attribute [local instance] sym2Order

attribute [local instance] prodOrder sumOrder

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Codec
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralCodec
open TreeTyped

def parts (a : Symbol) : List Bool×List Bool :=
  (List.replicate a.val false,List.replicate (7-a.val) false)

def fromBit (b : Bool) : Symbol := if b then 2 else 1
def natWord (n : ℕ) : List Symbol := (n.bits.map fromBit)++[3]
end MatchingFPRAS.LiteralCodec

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_GreedyPublicProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Parsing the public margins and printing the greedy matrix

All operations are existing binary list programs. The bounded take and
drop operations also terminate polynomially on malformed headers.
-/

namespace ContingencyTables.GreedyFeasibleTable
open MatchingFPRAS TreeTyped LiteralCodec
open scoped BigOperators

/-- The first two natural numbers give the lengths of the two margins. -/
def marginLists (ns : List ℕ) : List ℕ × List ℕ :=
  let m := ns.headD 0
  let n := ns.tail.headD 0
  let rest := ns.tail.tail
  (rest.take m,(rest.drop m).take n)

def printMatrix (rows : List (List ℕ)) : List Symbol :=
  rows.flatMap (fun row => row.flatMap encodeNat)

end ContingencyTables.GreedyFeasibleTable

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingInputParser
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Parsing the public cell-bounded counting input

Dimensions only delimit bounded list slices. The matrix layout uses the
lengths of the parsed margin lists, so malformed headers do not create
unbounded numeric loops. Positive rational parameters use their natural
numerator and denominator, exactly as in the public tape encoding.
-/

namespace ContingencyTables.CountingInputParser
open MatchingFPRAS MatchingFPRAS.TreeTyped
open DensePrograms

def offset (ns : List ℕ) : ℕ := 2+ns.headD 0+ns.tail.headD 0

def rest (ns : List ℕ) : List ℕ := ns.drop (offset ns)

def cells (ns : List ℕ) : ℕ :=
  (GreedyFeasibleTable.marginLists ns).1.length*(GreedyFeasibleTable.marginLists ns).2.length

def parameters (ns : List ℕ) : List ℕ := (rest ns).drop (cells ns)

end ContingencyTables.CountingInputParser

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Graphs_AdaptiveStream
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream
open Finset

abbrev Bits (n : ℕ) := Fin n → Bool
abbrev Stream := ℕ → Bool

def shift (n : ℕ) (b : Stream) : Stream := fun i => b (n+i)
@[simp] lemma shift_zero (b : Stream) : shift 0 b=b := by funext i; simp [shift]
def extend {n : ℕ} (b : Bits n) : Stream := fun i => if h : i<n then b ⟨i,h⟩ else false

def concat {n m : ℕ} (a : Bits n) (b : Bits m) : Bits (n+m) := Fin.append a b

def split (n m : ℕ) : Bits (n+m) ≃ Bits n × Bits m where
  toFun b := (fun i=>b (Fin.castAdd m i), fun j=>b (Fin.natAdd n j))
  invFun b := concat b.1 b.2
  left_inv b := by funext i; exact Fin.addCases (by simp [concat]) (by simp [concat]) i
  right_inv b := by ext i <;> simp [concat]

@[simp] lemma concat_left {n m : ℕ} (a : Bits n) (b : Bits m) (i : Fin n) :
    concat a b (Fin.castAdd m i)=a i := by simp [concat]
@[simp] lemma concat_right {n m : ℕ} (a : Bits n) (b : Bits m) (i : Fin m) :
    concat a b (Fin.natAdd n i)=b i := by simp [concat]

noncomputable def average {n : ℕ} (f : Bits n → ℚ) : ℚ :=
  (∑ b,f b)/(2:ℚ)^n

inductive Experiment (α : Type) where
  | done (a : α)
  | read (next : Bool → Experiment α)
  | delay (ticks : ℕ) (next : Experiment α)

namespace Experiment
variable {α β : Type}

def cost : Experiment α → ℕ
  | .done _ => 0
  | .read f => 1+max (cost (f false)) (cost (f true))
  | .delay n p => n+cost p

def run : Experiment α → Stream → α × ℕ
  | .done a,_ => (a,0)
  | .read f,b => let r := run (f (b 0)) (shift 1 b); (r.1,1+r.2)
  | .delay n p,b => let r := run p (shift n b); (r.1,n+r.2)

def mean : Experiment α → (α → ℚ) → ℚ
  | .done a,f => f a
  | .read p,f => (mean (p false) f+mean (p true) f)/2
  | .delay _ p,f => mean p f

def bind : Experiment α → (α → Experiment β) → Experiment β
  | .done a,f => f a
  | .read p,f => .read (fun b=>(p b).bind f)
  | .delay n p,f => .delay n (p.bind f)

lemma mean_bind (p : Experiment α) (q : α → Experiment β) (f : β → ℚ) :
    (p.bind q).mean f=p.mean (fun a=>(q a).mean f) := by
  induction p with
  | done a => rfl
  | read p ih => simp [bind,mean,ih]
  | delay n p ih => exact ih

lemma cost_bind_le (p : Experiment α) (q : α → Experiment β) (N : ℕ)
    (hq : ∀ a,(q a).cost ≤ N) : (p.bind q).cost ≤ p.cost+N := by
  induction p with
  | done a => simpa only [bind,cost,Nat.zero_add] using hq a
  | read p ih =>
    simp only [bind,cost]
    have h0:=ih false
    have h1:=ih true
    omega
  | delay n p ih => simpa only [bind,cost,Nat.add_assoc] using Nat.add_le_add_left ih n

def map (f : α → β) (p : Experiment α) : Experiment β := p.bind (fun a=>.done (f a))

@[simp] lemma cost_map (f : α → β) (p : Experiment α) : (p.map f).cost=p.cost := by
  induction p with
  | done a => rfl
  | read p ih => simp only [map,bind,cost]; change 1+max ((p false).map f).cost ((p true).map f).cost=_; rw [ih false,ih true]
  | delay n p ih => change n+(p.map f).cost=n+p.cost; rw [ih]

lemma mean_map (f : α → β) (p : Experiment α) (g : β → ℚ) :
    (p.map f).mean g=p.mean (fun a=>g (f a)) := by simp [map,mean_bind,mean]

def word : (n : ℕ) → Experiment (Bits n)
  | 0 => .done Fin.elim0
  | n+1 => .read (fun b=>(word n).map (Fin.cons b))

@[simp] lemma cost_word (n : ℕ) : (word n).cost=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [word,cost,cost_map,ih,max_self]; omega

end Experiment
end MatchingFPRAS.PhysicalStream

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Graphs_ExperimentSupport
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream.Experiment
variable {α β : Type}
def All : Experiment α → (α → Prop) → Prop
  | .done a,P => P a
  | .read f,P => All (f false) P ∧ All (f true) P
  | .delay _ p,P => All p P
lemma All.mono {p : Experiment α} {P Q : α → Prop} (h : All p P) (hPQ : ∀ a,P a→Q a) : All p Q := by
  induction p with
  | done a => exact hPQ a h
  | read p ih => exact ⟨ih false h.1,ih true h.2⟩
  | delay n p ih => exact ih h
lemma mean_nonneg (p : Experiment α) (f : α → ℚ) (h : All p (fun a=>0≤f a)) : 0≤p.mean f := by
  induction p with
  | done a => exact h
  | read p ih => exact div_nonneg (add_nonneg (ih false h.1) (ih true h.2)) (by norm_num)
  | delay n p ih => exact ih h
lemma all_true (p : Experiment α) : All p (fun _=>True) := by
  induction p with
  | done a => trivial
  | read p ih => exact ⟨ih false,ih true⟩
  | delay n p ih => exact ih
lemma all_indicator (p : Experiment α) (P : α → Prop) [DecidablePred P] :
    All p P ↔ p.mean (fun a=>if P a then 0 else 1)=0 := by
  induction p with
  | done a => simp [All,mean]
  | delay n p ih => exact ih
  | read p ih =>
    have hz (b : Bool) : 0≤(p b).mean (fun a=>if P a then 0 else 1) :=
      mean_nonneg _ _ ((all_true _).mono (by intro a _; split <;> norm_num))
    simp only [All,mean,ih]
    constructor
    · rintro ⟨h0,h1⟩; rw [h0,h1]; norm_num
    · intro h
      have h0:=hz false
      have h1:=hz true
      constructor <;> linarith
lemma all_of_mean_eq {p q : Experiment α} (h : ∀ f : α → ℚ,q.mean f=p.mean f)
    (P : α → Prop) (hp : All p P) : All q P := by
  classical
  rw [all_indicator,h,←all_indicator]
  exact hp
lemma cost_bind_le_of_all (p : Experiment α) (q : α → Experiment β) (N : ℕ)
    (h : All p (fun a=>(q a).cost≤N)) : (p.bind q).cost≤p.cost+N := by
  induction p with
  | done a => simpa only [All,bind,cost,Nat.zero_add] using h
  | read p ih =>
    have h0:=ih false h.1
    have h1:=ih true h.2
    simp only [cost,bind]
    omega
  | delay n p ih => simpa only [bind,cost,Nat.add_assoc] using Nat.add_le_add_left (ih h) n

variable {α : Type}
def worst : Experiment α → (α → ℕ) → ℕ
  | .done a,f => f a
  | .read p,f => max (worst (p false) f) (worst (p true) f)
  | .delay _ p,f => worst p f
lemma all_worst (p : Experiment α) (f : α → ℕ) : All p (fun a=>f a≤p.worst f) := by
  induction p with
  | done a => exact le_rfl
  | read p ih => exact ⟨(ih false).mono (fun a ha=>ha.trans (le_max_left _ _)),
      (ih true).mono (fun a ha=>ha.trans (le_max_right _ _))⟩
  | delay n p ih => exact ih
end MatchingFPRAS.PhysicalStream.Experiment

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_PhysicalPost
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q R : Type} [Inhabited Γ]

structure Cfg (Γ Q : Type) [Inhabited Γ] where
  state : Option Q
  tape : Tape Γ

abbrev Table (Γ Q : Type) := Q → Γ → Bool → Option (Q × TM0.Stmt Γ)

def tick (M : Table Γ Q) (c : Cfg Γ Q) (b : Bool) : Cfg Γ Q :=
  match c.state with
  | none => c
  | some q => match M q c.tape.head b with
    | none => ⟨none,c.tape⟩
    | some (q',a) => ⟨some q',match a with
      | .move d => c.tape.move d
      | .write s => c.tape.write s⟩

def execute (M : Table Γ Q) : ℕ → Cfg Γ Q → Stream → Cfg Γ Q
  | 0,c,_ => c
  | n+1,c,b => execute M n (tick M c (b 0)) (shift 1 b)

def experiment (M : Table Γ Q) : ℕ → Cfg Γ Q → Experiment (Cfg Γ Q)
  | 0,c => .done c
  | n+1,c => .read (fun b=>experiment M n (tick M c b))

variable [Fintype Q] [Inhabited Q]

noncomputable def enumeration : Q ≃ Fin (Fintype.card Q-1+1) := by
  let e : Q ≃ Fin (Fintype.card Q-1+1) := Fintype.equivFinOfCardEq
    (Nat.sub_add_cancel Fintype.card_pos).symm
  exact e.trans (Equiv.swap (e default) 0)

@[simp] lemma enumeration_default : enumeration (Q:=Q) default=0 := by
  classical
  simp only [enumeration,Equiv.trans_apply,Equiv.swap_apply_left]

noncomputable def machine (M : Table Symbol Q) : RandomMachine where
  states := Fintype.card Q-1
  transition q a b := (M ((enumeration (Q:=Q)).symm q) a b).map
    (fun qa=>(enumeration qa.1,qa.2))

noncomputable def sealCfg (M : Table Symbol Q) (c : Cfg Symbol Q) : Configuration (machine M) :=
  ⟨c.state.map enumeration,c.tape⟩

end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_CoinTM1
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.CoinTM1
open Turing MachineCost PhysicalStream

variable {Γ Λ σ : Type} [Inhabited Γ]

abbrev Node (Γ Λ σ : Type) := Λ ⊕ TM1.Stmt Γ Λ σ
abbrev State (Γ Λ σ : Type) := Node Γ Λ σ × σ
abbrev Coins (Λ : Type) := Λ → Option (Bool → Λ)

def aux (a : Γ) : TM1.Stmt Γ Λ σ → σ → Option (State Γ Λ σ × TM0.Stmt Γ)
  | .move d q,v => some ((.inr q,v),.move d)
  | .write f q,v => some ((.inr q,v),.write (f a v))
  | .load f q,v => aux a q (f a v)
  | .branch f q r,v => if f a v then aux a q v else aux a r v
  | .goto f,v => some ((.inl (f a v),v),.write a)
  | .halt,_ => none

def table (M : Λ → TM1.Stmt Γ Λ σ) (coin : Coins Λ) : PhysicalPost.Table Γ (State Γ Λ σ)
  | (.inl l,v),a,b => match coin l with
    | none => aux a (M l) v
    | some f => some ((.inl (f b),v),.write a)
  | (.inr q,v),a,_ => aux a q v

def pending (q : TM1.Stmt Γ Λ σ) (v : σ) (T : Tape Γ) : PhysicalPost.Cfg Γ (State Γ Λ σ) :=
  ⟨some (.inr q,v),T⟩

def trCfg (c : TM1.Cfg Γ Λ σ) : PhysicalPost.Cfg Γ (State Γ Λ σ) :=
  ⟨c.l.map (fun l=>(Sum.inl l,c.var)),c.Tape⟩

end MatchingFPRAS.CoinTM1

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_PhysicalRestriction
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q : Type} [Inhabited Γ]

def Supported (M : Table Γ Q) (S : Finset Q) : Prop :=
  ∀ q ∈ S, ∀ a b q' act,M q a b=some (q',act) → q'∈S

noncomputable def restrict (M : Table Γ Q) (S : Finset Q) (_h : Supported M S) :
    Table Γ {q // q∈S} := by
  classical
  exact fun q a b=>(M q.val a b).map (fun qa=>
    ((if hm:qa.1∈S then ⟨qa.1,hm⟩ else q),qa.2))

def liftCfg (S : Finset Q) (c : Cfg Γ {q // q∈S}) : Cfg Γ Q :=
  ⟨c.state.map Subtype.val,c.tape⟩

noncomputable def restrictedMachine (M : Table Symbol Q) (S : Finset Q)
    (h : Supported M S) (q₀ : Q) (hq₀ : q₀∈S) : RandomMachine :=
  letI : Inhabited {q //q∈S}:=⟨⟨q₀,hq₀⟩⟩
  machine (restrict M S h)

end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_CoinTM1Finite
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.CoinTM1
open Turing
open scoped Classical

variable {Γ Λ σ : Type} [Inhabited Λ] [Fintype σ]

noncomputable def nodes (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) : Finset (Node Γ Λ σ) :=
  S.disjSum (S.biUnion (fun l=>TM1.stmts₁ (M l)))
noncomputable def states (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) : Finset (State Γ Λ σ) :=
  (nodes M S) ×ˢ Finset.univ

omit [Inhabited Λ] [Fintype σ] in
lemma node_entry {M : Λ → TM1.Stmt Γ Λ σ} {S : Finset Λ} {l : Λ} (h : l∈S) :
    Sum.inl l∈nodes M S := by simp only [nodes,Finset.inl_mem_disjSum]; exact h
omit [Inhabited Λ] [Fintype σ] in
lemma node_pending {M : Λ → TM1.Stmt Γ Λ σ} {S : Finset Λ} {q : TM1.Stmt Γ Λ σ}
    (h : some q∈TM1.stmts M S) : Sum.inr q∈nodes M S := by
  simpa only [nodes,Finset.inr_mem_disjSum,TM1.stmts,Finset.some_mem_insertNone] using h
omit [Inhabited Λ] in
lemma state_mem {M : Λ → TM1.Stmt Γ Λ σ} {S : Finset Λ} {q : Node Γ Λ σ} {v : σ}
    (h : q∈nodes M S) : (q,v)∈states M S := by
  simp only [states,Finset.mem_product,Finset.mem_univ,and_true]; exact h

lemma aux_supported {M : Λ → TM1.Stmt Γ Λ σ} {S : Finset Λ}
    (hs : TM1.Supports M S) (a : Γ) (q : TM1.Stmt Γ Λ σ)
    (hq : some q∈TM1.stmts M S) (v : σ) (q' : State Γ Λ σ) (act : TM0.Stmt Γ)
    (he : aux a q v=some (q',act)) : q'∈states M S := by
  classical
  induction q generalizing v q' act with
  | move d q ih =>
    simp only [aux,Option.some.injEq,Prod.mk.injEq] at he
    rcases he with ⟨rfl,rfl⟩
    apply state_mem
    apply node_pending
    exact TM1.stmts_trans (by simp only [TM1.stmts₁,Finset.mem_insert]; exact Or.inr TM1.stmts₁_self) hq
  | write f q ih =>
    simp only [aux,Option.some.injEq,Prod.mk.injEq] at he
    rcases he with ⟨rfl,rfl⟩
    apply state_mem
    apply node_pending
    exact TM1.stmts_trans (by simp only [TM1.stmts₁,Finset.mem_insert]; exact Or.inr TM1.stmts₁_self) hq
  | load f q ih =>
    exact ih (TM1.stmts_trans (by simp only [TM1.stmts₁,Finset.mem_insert]; exact Or.inr TM1.stmts₁_self) hq) _ _ _ he
  | branch f q r ihq ihr =>
    simp only [aux] at he
    split_ifs at he with hf
    · exact ihq (TM1.stmts_trans (by simp only [TM1.stmts₁,Finset.mem_insert,Finset.mem_union]; exact Or.inr (Or.inl TM1.stmts₁_self)) hq) _ _ _ he
    · exact ihr (TM1.stmts_trans (by simp only [TM1.stmts₁,Finset.mem_insert,Finset.mem_union]; exact Or.inr (Or.inr TM1.stmts₁_self)) hq) _ _ _ he
  | goto f =>
    simp only [aux,Option.some.injEq,Prod.mk.injEq] at he
    rcases he with ⟨rfl,rfl⟩
    exact state_mem (node_entry (TM1.stmts_supportsStmt hs hq a v))
  | halt => simp [aux] at he

theorem table_supported (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) (hs : TM1.Supports M S)
    (coin : Coins Λ) (hc : ∀ l∈S,∀ f,coin l=some f→∀ b,f b∈S) :
    PhysicalPost.Supported (table M coin) (states M S) := by
  intro q hq a b q' act he
  have hn : q.1∈nodes M S := (Finset.mem_product.mp hq).1
  rcases q with ⟨l,v⟩
  cases l with
  | inl l =>
    have hl : l∈S := by simpa only [nodes,Finset.inl_mem_disjSum] using hn
    simp only [table] at he
    split at he
    · apply aux_supported hs a (M l) _ v q' act he
      simp only [TM1.stmts,Finset.some_mem_insertNone,Finset.mem_biUnion]
      exact ⟨l,hl,TM1.stmts₁_self⟩
    · rename_i f hf
      simp only [Option.some.injEq,Prod.mk.injEq] at he
      rcases he with ⟨rfl,rfl⟩
      exact state_mem (node_entry (hc l hl f hf b))
  | inr q =>
    apply aux_supported hs a q _ v q' act he
    simpa only [nodes,Finset.inr_mem_disjSum,TM1.stmts,Finset.some_mem_insertNone] using hn

end MatchingFPRAS.CoinTM1

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_CoinAlphabet
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.CoinAlphabet
open Turing TM1 TM1to1 MachineCost

variable {Γ Λ σ : Type} [Inhabited Γ]
def safe (p : Λ → Prop) : Λ' Γ Λ σ → Prop
  | .normal l => p l
  | .write _ _ => True

def coins (c : CoinTM1.Coins Λ) : CoinTM1.Coins (Λ' Γ Λ σ)
  | .normal l => (c l).map (fun f b=>.normal (f b))
  | .write _ _ => none

end MatchingFPRAS.CoinAlphabet

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_CoinStack
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.CoinStack
open Turing TM2to1 TM2to1.Λ' MachineCost StackCost

variable {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]

def safe (p : Λ → Prop) : Λ' K Γ Λ σ → Prop
  | .normal l => p l
  | .go _ _ _ | .ret _ => True

def coins (c : CoinTM1.Coins Λ) : CoinTM1.Coins (Λ' K Γ Λ σ)
  | .normal l => (c l).map (fun f b=>.normal (f b))
  | .go _ _ _ | .ret _ => none

end MatchingFPRAS.CoinStack

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_CoinSupport
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.CoinAlphabet
open Turing
open scoped Classical

variable {Γ Λ σ : Type} [Inhabited Γ] [Fintype Γ]
omit [Inhabited Γ] in
lemma normal_not_writes (l : Λ) (q : TM1.Stmt Γ Λ σ) : TM1to1.Λ'.normal l∉TM1to1.writes q := by
  induction q <;> simp_all [TM1to1.writes]
omit [Inhabited Γ] in
lemma normal_mem (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) (l : Λ) :
    TM1to1.Λ'.normal l∈TM1to1.trSupp M S ↔ l∈S := by
  simp only [TM1to1.trSupp,Finset.mem_biUnion,Finset.mem_insert,TM1to1.Λ'.normal.injEq,
    normal_not_writes,or_false]
  constructor
  · rintro ⟨l',hl',rfl⟩; exact hl'
  · intro hl; exact ⟨l,hl,rfl⟩
omit [Inhabited Γ] in
lemma coins_supported (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) (c : CoinTM1.Coins Λ)
    (hc : ∀ l∈S,∀ f,c l=some f→∀ b,f b∈S) :
    ∀ l∈TM1to1.trSupp M S,∀ f,coins c l=some f→∀ b,f b∈TM1to1.trSupp M S := by
  intro l hl f hf b
  cases l with
  | normal l =>
    have hl':= (normal_mem M S l).mp hl
    simp only [coins,Option.map_eq_some_iff] at hf
    obtain ⟨g,hg,rfl⟩:=hf
    exact (normal_mem M S (g b)).mpr (hc l hl' g hg b)
  | write a q => simp [coins] at hf
end MatchingFPRAS.CoinAlphabet

namespace MatchingFPRAS.CoinStack
open Turing TM2to1
open scoped Classical

variable {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]
omit [DecidableEq K] in
lemma normal_not_internal (l : Λ) (q : TM2.Stmt Γ Λ σ) : Λ'.normal l∉trStmts₁ q := by
  induction q using stmtStRec with
  | run k o q ih => simp_all [trStmts₁_run]
  | load f q ih => exact ih
  | branch f q r ihq ihr => simp_all [trStmts₁]
  | goto f => simp [trStmts₁]
  | halt => simp [trStmts₁]
omit [DecidableEq K] in
lemma normal_mem (M : Λ → TM2.Stmt Γ Λ σ) (S : Finset Λ) (l : Λ) :
    Λ'.normal l∈trSupp M S ↔ l∈S := by
  simp only [trSupp,Finset.mem_biUnion,Finset.mem_insert,Λ'.normal.injEq,
    normal_not_internal,or_false]
  constructor
  · rintro ⟨l',hl',rfl⟩; exact hl'
  · intro hl; exact ⟨l,hl,rfl⟩
omit [DecidableEq K] in
lemma coins_supported (M : Λ → TM2.Stmt Γ Λ σ) (S : Finset Λ) (c : CoinTM1.Coins Λ)
    (hc : ∀ l∈S,∀ f,c l=some f→∀ b,f b∈S) :
    ∀ l∈trSupp M S,∀ f,coins c l=some f→∀ b,f b∈trSupp M S := by
  intro l hl f hf b
  cases l with
  | normal l =>
    have hl':= (normal_mem M S l).mp hl
    simp only [coins,Option.map_eq_some_iff] at hf
    obtain ⟨g,hg,rfl⟩:=hf
    exact (normal_mem M S (g b)).mpr (hc l hl' g hg b)
  | go k o q => simp [coins] at hf
  | ret q => simp [coins] at hf
end MatchingFPRAS.CoinStack

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_PhysicalProcess
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q α β : Type} [Inhabited Γ]

inductive Implements (M : Table Γ Q) (out : α → Cfg Γ Q) :
    Cfg Γ Q → Experiment α → Prop
  | done (a) : Implements M out (out a) (.done a)
  | read (c) (f : Bool → Experiment α)
      (h : ∀ b,Implements M out (tick M c b) (f b)) : Implements M out c (.read f)
  | delay (c d) (n : ℕ) (p : Experiment α)
      (step : ∀ b : Stream,execute M n c b=d)
      (rest : Implements M out d p) : Implements M out c (.delay n p)

end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_PhysicalAlphabet
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream BoolPostCompiler

variable {Q : Type}

def liftBool (M : Table Bool Q) : Table Symbol Q := fun q a b=>
  (M q (down a) b).map (fun qa=>(qa.1,qa.2.map up))
def upCfg (c : Cfg Bool Q) : Cfg Symbol Q := ⟨c.state,c.tape.map up⟩
lemma liftBool_supported (M : Table Bool Q) (S : Finset Q) (hS : Supported M S) :
    Supported (liftBool M) S := by
  intro q hq a b q' act he
  simp only [liftBool,Option.map_eq_some_iff] at he
  obtain ⟨⟨q'',act'⟩,h,e⟩:=he
  have hqq : q''=q':=congrArg Prod.fst e
  subst q''
  exact hS q hq (down a) b q' act' h
end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_OnlineStackCompiler
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineStack
open Turing MachineCost PhysicalStream
open scoped Classical

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
  [∀ k,Fintype (Γ k)] [Inhabited Λ] [Fintype Λ] [Inhabited σ] [Fintype σ]
abbrev Alpha (K : Type) (Γ : K → Type) := TM2to1.Γ' K Γ
abbrev L1 (K : Type) (Γ : K → Type) (Λ σ : Type) := TM2to1.Λ' K Γ Λ σ
abbrev L2 (K : Type) (Γ : K → Type) (Λ σ : Type) := TM1to1.Λ' (Alpha K Γ) (L1 K Γ Λ σ) σ
abbrev Q (K : Type) (Γ : K → Type) (Λ σ : Type) := CoinTM1.State Bool (L2 K Γ Λ σ) σ

noncomputable def height (S : ∀ k,List (Γ k)) : ℕ := Finset.univ.sup (fun k=>(S k).length)
noncomputable def stackCfg (c : TM2.Cfg Γ Λ σ) : TM1.Cfg (Alpha K Γ) (L1 K Γ Λ σ) σ :=
  ⟨c.l.map TM2to1.Λ'.normal,c.var,Tape.mk₁ (StackWords.word c.stk (height c.stk))⟩

variable (M : Λ → TM2.Stmt Γ Λ σ) (coin : CoinTM1.Coins Λ)
noncomputable def program1 := TM2to1.tr M
noncomputable def enc := FixedEncoding.enc (Alpha K Γ)
noncomputable def dec := FixedEncoding.dec (Alpha K Γ)
lemma enc0 : enc (K:=K) (Γ:=Γ) default=List.Vector.replicate (Fintype.card (Alpha K Γ)) false :=
  FixedEncoding.blank (Alpha K Γ)
noncomputable def program2 := TM1to1.tr (enc (K:=K) (Γ:=Γ)) dec (program1 M)
noncomputable def support1 := TM2to1.trSupp M Finset.univ
noncomputable def support2 := TM1to1.trSupp (program1 M) (support1 M)
noncomputable def coin2 := CoinAlphabet.coins (Γ:=Alpha K Γ) (σ:=σ) (CoinStack.coins (Γ:=Γ) (σ:=σ) coin)
noncomputable def table := CoinTM1.table (program2 M) (coin2 coin)
noncomputable def states := CoinTM1.states (program2 M) (support2 M)
omit [Fintype K] [∀ k,Fintype (Γ k)] [Inhabited σ] [Fintype σ] in
lemma supports1 [Fintype K] [∀ k,Fintype (Γ k)] [Inhabited σ] [Fintype σ] :
    TM1.Supports (program1 M) (support1 M) :=
  TM2to1.tr_supports M (StackComposition.supports_univ M)
lemma supports2 : TM1.Supports (program2 M) (support2 M) :=
  TM1to1.tr_supports enc dec (program1 M) (supports1 M)
omit [Inhabited Λ] [Inhabited σ] [Fintype σ] in
lemma coin2_supported [Inhabited Λ] [Inhabited σ] [Fintype σ] :
    ∀ l∈support2 M,∀ f,coin2 coin l=some f→∀ b,f b∈support2 M :=
  CoinAlphabet.coins_supported (program1 M) (support1 M) _
    (CoinStack.coins_supported M Finset.univ coin (fun _ _ _ _ _=>Finset.mem_univ _))
lemma table_supported : PhysicalPost.Supported (table M coin) (states M) :=
  CoinTM1.table_supported (program2 M) (support2 M) (supports2 M) (coin2 coin) (coin2_supported M coin)
noncomputable def cfg (c : TM2.Cfg Γ Λ σ) : PhysicalPost.Cfg Bool (Q K Γ Λ σ) :=
  CoinTM1.trCfg (TM1to1.trCfg enc enc0 (stackCfg c))

noncomputable def accesses : ℕ := Finset.univ.sup (fun l=>StackCost.accesses (M l))
noncomputable def overhead : ℕ :=
  (AlphabetCost.supportedWrites (program1 M) (support1 M)+1)*
    SupportedCompiler.cost (program2 M) (support2 M)

noncomputable def initialState : Q K Γ Λ σ :=
  (.inl (.normal (.normal default)),default)
lemma initialState_mem : initialState (K:=K) (Γ:=Γ) (Λ:=Λ) (σ:=σ)∈states M := by
  apply CoinTM1.state_mem
  apply CoinTM1.node_entry
  apply (CoinAlphabet.normal_mem _ _ _).mpr
  exact (CoinStack.normal_mem M Finset.univ default).mpr (Finset.mem_univ default)

end MatchingFPRAS.OnlineStack

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Online
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineStack
open Turing MachineCost PhysicalStream

variable {K Λ σ α : Type} {Γ : K → Type} [DecidableEq K]

inductive Executes (M : Λ → TM2.Stmt Γ Λ σ) (coin : CoinTM1.Coins Λ)
    (out : α → TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ σ → Experiment α → Prop
  | done (a) : Executes M coin out (out a) (.done a)
  | read (l v S) (f : Bool → Λ) (p : Bool → Experiment α)
      (hf : coin l=some f)
      (rest : ∀ b,Executes M coin out ⟨some (f b),v,S⟩ (p b)) :
      Executes M coin out ⟨some l,v,S⟩ (.read p)
  | step (l v S) (p : Experiment α) (safe : coin l=none)
      (rest : Executes M coin out (TM2.stepAux (M l) v S) p) :
      Executes M coin out ⟨some l,v,S⟩ (.delay 1 p)

namespace Executes
variable {M : Λ → TM2.Stmt Γ Λ σ} {coin : CoinTM1.Coins Λ}
  {out : α → TM2.Cfg Γ Λ σ} {c : TM2.Cfg Γ Λ σ} {p : Experiment α}
lemma bind {β : Type} (h : Executes M coin out c p) (q : α → Experiment β)
    (out' : β → TM2.Cfg Γ Λ σ) (hq : ∀ a,Executes M coin out' (out a) (q a)) :
    Executes M coin out' c (p.bind q) := by
  induction h with
  | done a => exact hq a
  | read l v S f p hf rest ih => exact .read l v S f _ hf ih
  | step l v S p safe rest ih => exact .step l v S _ safe ih

variable [Fintype K] [∀ k,Fintype (Γ k)] [Inhabited Λ] [Fintype Λ]
  [Inhabited σ] [Fintype σ]

noncomputable def factor (M : Λ → TM2.Stmt Γ Λ σ) (H n : ℕ) : ℕ :=
  overhead M*(1+2*accesses M*(H+n*accesses M+1))+1
end Executes
end MatchingFPRAS.OnlineStack

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_PhysicalSequential
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q R α β : Type} [Inhabited Γ]

def seq (M : Table Γ Q) (N : Table Γ R) (r₀ : R) : Table Γ (Q⊕R)
  | .inl q,a,b => match M q a b with
    | none => some (.inr r₀,.write a)
    | some (q',act) => some (.inl q',act)
  | .inr r,a,b => (N r a b).map (fun ra=>(Sum.inr ra.1,ra.2))
def leftCfg (r₀ : R) (c : Cfg Γ Q) : Cfg Γ (Q⊕R) :=
  ⟨some (c.state.elim (Sum.inr r₀) Sum.inl),c.tape⟩
def rightCfg (c : Cfg Γ R) : Cfg Γ (Q⊕R) := ⟨c.state.map Sum.inr,c.tape⟩

def early (M : Table Γ Q) : ℕ→Cfg Γ Q→Experiment (Cfg Γ Q)
  | 0,c => .done c
  | n+1,c => match c.state with
    | none => .done c
    | some _ => .read (fun b=>early M n (tick M c b))
omit [Inhabited Γ] in
lemma seq_supported [Inhabited Γ] (M : Table Γ Q) (N : Table Γ R) (r₀ : R)
    (S : Finset Q) (T : Finset R) (hM : Supported M S) (hN : Supported N T) (hr : r₀∈T) :
    Supported (seq M N r₀) (S.disjSum T) := by
  intro q hq a b q' act he
  cases q with
  | inl q =>
    have hq':q∈S := Finset.inl_mem_disjSum.mp hq
    cases h:M q a b with
    | none => simp only [seq,h,Option.some.injEq,Prod.mk.injEq] at he;rcases he with ⟨rfl,rfl⟩;exact Finset.inr_mem_disjSum.mpr hr
    | some x =>
      rcases x with ⟨v,ac⟩
      simp only [seq,h,Option.some.injEq,Prod.mk.injEq] at he
      rcases he with ⟨rfl,rfl⟩
      exact Finset.inl_mem_disjSum.mpr (hM q hq' a b v ac h)
  | inr r =>
    simp only [seq,Option.map_eq_some_iff] at he
    obtain ⟨⟨r',ac⟩,hh,e⟩:=he
    cases e
    exact Finset.inr_mem_disjSum.mpr (hN r (Finset.inr_mem_disjSum.mp hq) a b r' ac hh)
end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_TapeTools
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralTape
open Turing MachineCost

variable {Γ Λ σ : Type} [Inhabited Γ]
@[simp] lemma mk₂_head (a : Γ) (L R : List Γ) : (Tape.mk₂ L (a::R)).head=a := rfl
@[simp] lemma mk₂_right (a : Γ) (L R : List Γ) :
    (Tape.mk₂ L (a::R)).move .right=Tape.mk₂ (a::L) R := by
  simp [Tape.mk₂,ListBlank.cons_mk]
@[simp] lemma mk₂_left (a : Γ) (L R : List Γ) :
    (Tape.mk₂ (a::L) R).move .left=Tape.mk₂ L (a::R) := by
  simp [Tape.mk₂,ListBlank.cons_mk]
@[simp] lemma mk₂_write (a b : Γ) (L R : List Γ) :
    (Tape.mk₂ L (a::R)).write b=Tape.mk₂ L (b::R) := by
  simp [Tape.mk₂,ListBlank.cons_mk]

def select [DecidableEq σ] (vs : List σ) (f : σ→TM1.Stmt Γ Λ σ)
    (fallback : TM1.Stmt Γ Λ σ) : TM1.Stmt Γ Λ σ :=
  vs.foldr (fun v tail=>.branch (fun _ s=>decide (s=v)) (f v) tail) fallback

def writeLeft (xs : List Γ) (q : TM1.Stmt Γ Λ σ) : TM1.Stmt Γ Λ σ :=
  xs.foldr (fun a tail=>.write (fun _ _=>a) (.move .left tail)) q

def eraseToLeft (n : ℕ) (q : TM1.Stmt Γ Λ σ) : TM1.Stmt Γ Λ σ :=
  Nat.rec q (fun _ tail=>.move .left (.write (fun _ _=>default) tail)) n

variable {I : Type} [DecidableEq I]
def grab (is : List I) (q : TM1.Stmt Γ Λ (I→Γ)) : TM1.Stmt Γ Λ (I→Γ) :=
  is.foldr (fun i tail=>.load (fun a v=>Function.update v i a) (.move .right tail)) q
end MatchingFPRAS.LiteralTape

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Physical
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralTape
open Turing MachineCost PhysicalStream

variable {Γ Λ σ : Type} [Inhabited Γ] [Inhabited Λ] [Fintype Λ] [Fintype σ] [Inhabited σ]
omit [Inhabited Γ] [Fintype σ] [Inhabited σ] in
lemma supports_univ (M : Λ→TM1.Stmt Γ Λ σ) : TM1.Supports M Finset.univ := by
  classical
  refine ⟨Finset.mem_univ _,fun l _=>?_⟩
  induction M l with
  | move d q ih => exact ih
  | write f q ih => exact ih
  | load f q ih => exact ih
  | branch f q r ih jh => exact ⟨ih,jh⟩
  | goto f => exact fun a v=>Finset.mem_univ _
  | halt => trivial
noncomputable def table (M : Λ→TM1.Stmt Γ Λ σ) := CoinTM1.table M (fun _=>none)
noncomputable def states (M : Λ→TM1.Stmt Γ Λ σ) := CoinTM1.states M Finset.univ
omit [Inhabited Γ] [Inhabited σ] in
lemma supported (M : Λ→TM1.Stmt Γ Λ σ) : PhysicalPost.Supported (table M) (states M) :=
  CoinTM1.table_supported M Finset.univ (supports_univ M) (fun _=>none) (by simp)
omit [Inhabited Γ] [Inhabited Λ] [Inhabited σ] in
lemma entry_mem (M : Λ→TM1.Stmt Γ Λ σ) (l : Λ) (v : σ) : (Sum.inl l,v)∈states M :=
  CoinTM1.state_mem (CoinTM1.node_entry (Finset.mem_univ _))
end MatchingFPRAS.LiteralTape

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_PhysicalProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q A B : Type} [Inhabited Γ]

structure Program where
  State : Type
  table : Table Symbol State
  states : Finset State
  supported : Supported table states
  entry : State
  entry_mem : entry∈states
namespace Program
noncomputable def seq (P R : Program) : Program where
  State := P.State⊕R.State
  table := PhysicalPost.seq P.table R.table R.entry
  states := P.states.disjSum R.states
  supported := seq_supported _ _ _ _ _ P.supported R.supported R.entry_mem
  entry := .inl P.entry
  entry_mem := Finset.inl_mem_disjSum.mpr P.entry_mem
noncomputable def machine (P : Program) : RandomMachine :=
  restrictedMachine P.table P.states P.supported P.entry P.entry_mem

def initial (P : Program) (T : Tape Symbol) : Cfg Symbol P.State := ⟨some P.entry,T⟩
def final (P : Program) (T : Tape Symbol) : Cfg Symbol P.State := ⟨none,T⟩
def Realizes (P : Program) (input : Tape Symbol) (f : Experiment (Tape Symbol)) (N : ℕ) : Prop :=
  ∃ p : Experiment (Tape Symbol),Implements P.table P.final (P.initial input) p ∧
    (∀ h,p.mean h=f.mean h) ∧ p.cost≤N

def earlyTapes (P : Program) (n : ℕ) (T : Tape Symbol) : Experiment (Tape Symbol) :=
  (early P.table n (P.initial T)).map Cfg.tape

noncomputable def ofTM1 {Λ σ : Type} [Inhabited Λ] [Fintype Λ] [Inhabited σ] [Fintype σ]
    (M : Λ→TM1.Stmt Symbol Λ σ) (l : Λ) (v : σ) : Program where
  State := CoinTM1.State Symbol Λ σ
  table := LiteralTape.table M
  states := LiteralTape.states M
  supported := LiteralTape.supported M
  entry := (.inl l,v)
  entry_mem := LiteralTape.entry_mem M l v
end Program
end MatchingFPRAS.PhysicalPost

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_BlockMap
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralBlockMap
open Turing LiteralTape

inductive Label
  | start | read | seek | back | stopSep | stopOut
  deriving DecidableEq, Inhabited
instance instFintypeLabel : Fintype Label := ⟨{.start,.read,.seek,.back,.stopSep,.stopOut}, by intro a; cases a <;> simp⟩
abbrev Block (w : ℕ) := Fin w→Symbol
noncomputable def code (w : ℕ) (h : Block w→List Symbol) (header : List Symbol) :
    Label→TM1.Stmt Symbol Label (Block w)
  | .start => .move .left (.write (fun _ _=>7) (.move .left (.write (fun _ _=>6)
      (.move .right (.move .right (.goto (fun _ _=>.read)))))))
  | .read => grab (List.finRange w)
      (.branch (fun _ b=>decide (b=fun _=>0))
        (.move .left (.goto (fun _ _=>.stopSep)))
        (.move .left (.write (fun _ _=>7) (eraseToLeft w (.move .left (.goto (fun _ _=>.seek)))))))
  | .seek => .branch (fun a _=>decide (a=6))
      (select Finset.univ.toList (fun b=>.write (fun _ _=>0)
        (writeLeft (h b).reverse (.write (fun _ _=>6) (.move .right (.goto (fun _ _=>.back)))))) .halt)
      (.move .left (.goto (fun _ _=>.seek)))
  | .back => .branch (fun a _=>decide (a=7))
      (.move .right (.goto (fun _ _=>.read)))
      (.move .right (.goto (fun _ _=>.back)))
  | .stopSep => .branch (fun a _=>decide (a=7))
      (.write (fun _ _=>0) (.move .left (.goto (fun _ _=>.stopOut))))
      (.move .left (.goto (fun _ _=>.stopSep)))
  | .stopOut => .branch (fun a _=>decide (a=6))
      (.write (fun _ _=>0) (writeLeft header.reverse (.write (fun _ _=>0) (.move .right .halt))))
      (.move .left (.goto (fun _ _=>.stopOut)))
variable (w : ℕ) (h : Block w→List Symbol) (header : List Symbol)

def working (out : List Symbol) (gap : ℕ) (input : List Symbol) : Tape Symbol :=
  Tape.mk₂ (7::(List.replicate gap 0++out.reverse++[6])) input

def budget (H n s : ℕ) : ℕ := (n+1)*(3+w+H+2*(s+n*(H+w)))

end MatchingFPRAS.LiteralBlockMap

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Packed
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralPacked
open TreeTyped

lemma map_enc_length {α : Type} [Fintype α] [Inhabited α] (a : α) :
    ((FixedEncoding.enc α a).toList.map BoolPostCompiler.up).length=Fintype.card α := by
  rw [List.length_map]
  exact (FixedEncoding.enc α a).2
lemma flatMap_uniform_length {α β : Type} (as : List α) (f : α→List β) (w : ℕ)
    (h : ∀ a,(f a).length=w) : (as.flatMap f).length=as.length*w := by
  induction as with
  | nil => simp
  | cons a as ih => simp only [List.flatMap_cons,List.length_append,h,ih,List.length_cons,Nat.add_mul,Nat.one_mul];omega
end MatchingFPRAS.LiteralPacked

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_PackedExecution
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralPacked
open Turing LiteralTape LiteralBlockMap

def singletonBlock (a : Symbol) : Block 1 := fun _=>a
end MatchingFPRAS.LiteralPacked

namespace MatchingFPRAS.LiteralTape
open Turing MachineCost

variable {Γ Λ σ : Type} [Inhabited Γ]
def eraseRight (n : ℕ) (q : TM1.Stmt Γ Λ σ) : TM1.Stmt Γ Λ σ :=
  Nat.rec q (fun _ tail=>.write (fun _ _=>default) (.move .right tail)) n
noncomputable def eraseCode (n : ℕ) : Unit→TM1.Stmt Symbol Unit Unit := fun _=>eraseRight n .halt
end MatchingFPRAS.LiteralTape

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_LiteralProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Public binary input and output for typed finite programs

Literal packing is independent of the counting algorithm. Its cost includes every packing, execution, and printing step.
-/

namespace ContingencyTables.LiteralProgram
open MatchingFPRAS Turing PhysicalPost PhysicalStream LiteralPacked TreeTyped Polynomial

/-- A polynomial representing the exact elementary block-map cost. -/
noncomputable def budgetPolynomial (w H : ℕ) (p q : Polynomial ℕ) : Polynomial ℕ :=
  (p+1)*(C (3+w+H)+2*(q+p*C (H+w)))

end ContingencyTables.LiteralProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_OnlineFold
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTree
open TreeTyped
open Turing MachineCost PhysicalStream OnlineStack

variable {A B : Type}

def foldM (f : A×B → Experiment B) : List A → B → Experiment B
  | [],b => .done b
  | a::as,b => (f (a,b)).bind (foldM f as)
end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_OnlineFrame
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTree
open TreeTyped
open Turing MachineCost PhysicalStream OnlineStack

variable {A B C D : Type}
namespace Second

inductive Point where | split | save | body | pop | cons | halt
  deriving DecidableEq, Inhabited
instance instFintypePoint : Fintype Point := ⟨{.split,.save,.body,.pop,.cons,.halt},by intro p; cases p <;> simp⟩
end Second

end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_OnlineWord
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineWord
open PhysicalStream TreeTyped OnlineTree

def prepend : ℕ → List Bool → Experiment (List Bool)
  | 0,acc => .done acc
  | n+1,acc => .read (fun b=>prepend n (b::acc))

def reverseBits (n : ℕ) : Bits n ≃ Bits n where
  toFun w i:=w i.rev
  invFun w i:=w i.rev
  left_inv w:=by funext i; simp
  right_inv w:=by funext i; simp

def step (x : ℕ×List Bool) : Experiment (List Bool) := .read (fun b=>.done (b::x.2))
lemma fold_step (as : List ℕ) (acc : List Bool) :
    OnlineTree.foldM step as acc=prepend as.length acc := by
  induction as generalizing acc with
  | nil => rfl
  | cons a as ih => simp only [OnlineTree.foldM,step,Experiment.bind,ih,List.length_cons,prepend]

end MatchingFPRAS.OnlineWord

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteWordExecution
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing a computed finite Boolean sampler

The program reads a fresh word on the physical online machine, preserves
the input, and runs the deterministic binary sampler on that word.
-/

namespace ContingencyTables.FiniteWordExecution
open MatchingFPRAS MatchingFPRAS.PhysicalStream Polynomial

variable {A B : Type}

def source (n : A → ℕ) (a : A) : Experiment (List Bool) := OnlineWord.prepend (n a) []

def experiment (n : A → ℕ) (f : A×List Bool → B) (a : A) : Experiment B :=
  (source n a).map (fun bs => f (a,bs))

end ContingencyTables.FiniteWordExecution

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingBranchSuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Accuracy of the public dispatcher from its positive counting branch -/
namespace ContingencyTables.CountingBranchProgram
open MatchingFPRAS GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

abbrev Accurate (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) (q : ℚ) : Prop :=
  (1-(epsilon:ℝ))*(Fintype.card (BoundedTable r c b):ℝ) ≤ (q:ℝ) ∧
    (q:ℝ) ≤ (1+(epsilon:ℝ))*(Fintype.card (BoundedTable r c b):ℝ)

end
end ContingencyTables.CountingBranchProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingOracleWordBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial word sizes for the executed density oracle -/

namespace ContingencyTables.CountingOracleWordBounds
open GridBoundary
open Polynomial
open scoped BigOperators Classical
noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

def timeBound (M E : ℕ) : ℕ :=
  2*(10000*M^2*M)^2*(M+M*M+2+4096*E)
def sampleBound (M E : ℕ) : ℕ := 65536*(M+1)*E^2
def binBound (M E : ℕ) : ℕ := M*(M+1+4*(4096*M*E+M))
def estimatorBound (M E : ℕ) : ℕ :=
  M*(sampleBound M E*(timeBound M E*(9*M)))+
    sampleBound M E*(timeBound M E*(9*M)+binBound M E)

def innerPolynomial : Polynomial ℕ := 400*(X+1)*X
def timePolynomial : Polynomial ℕ :=
  2*(10000*X^2*X)^2*(X+X*X+2+4096*innerPolynomial)
def samplePolynomial : Polynomial ℕ := 65536*(X+1)*innerPolynomial^2
def binPolynomial : Polynomial ℕ := X*(X+1+4*(4096*X*innerPolynomial+X))
def estimatorPolynomial : Polynomial ℕ :=
  X*(samplePolynomial*(timePolynomial*(9*X)))+
    samplePolynomial*(timePolynomial*(9*X)+binPolynomial)
def medianPolynomial : Polynomial ℕ := 64*(X+1)*estimatorPolynomial

end
end ContingencyTables.CountingOracleWordBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingMarkerBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial space for the executed power-approximation markers -/
namespace ContingencyTables.CountingMarkerBounds
open Polynomial
noncomputable section

def paddingPolynomial : Polynomial ℕ := 409600*(X+1)*X

end
end ContingencyTables.CountingMarkerBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPublicTerminalBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Public polynomial bounds for the terminal grid and phase controls -/

namespace ContingencyTables.CountingPublicTerminalBounds
open CountingTerminalBounds CountingPublicInputBounds
open Polynomial
open scoped Classical
noncomputable section
variable {m n : ℕ}

def basicPolynomial : Polynomial ℕ := X*cutoffPolynomial+cutoffPolynomial+phasePolynomial+X+1

end
end ContingencyTables.CountingPublicTerminalBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingWordsBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial bound for the complete adaptive counting word

The bound includes every reserved restart, oracle and observation word,
including the words unused on unsuccessful paths.
-/

namespace ContingencyTables.CountingWordsBound
open CountingOracleWordBounds Polynomial
open scoped BigOperators Classical
noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

def initialPolynomial : Polynomial ℕ := X*(X+1)*(X*(3*X+1)+1+X)
def stepPolynomial : Polynomial ℕ := 1+(X^2+((medianPolynomial+medianPolynomial)+X))
def stagePolynomial : Polynomial ℕ := X*((X+1)*stepPolynomial)
def phasePolynomial : Polynomial ℕ :=
  initialPolynomial+X*stagePolynomial+(X*stepPolynomial+(X+1)*(medianPolynomial+medianPolynomial))
def wordPolynomial : Polynomial ℕ := X*(X*phasePolynomial)

end
end ContingencyTables.CountingWordsBound

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseNormalizeSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Correctness of computed maximal-margin normalization -/

namespace ContingencyTables.DensePrograms
open GridBoundary FairBits ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section

def indexPermutation {m : ℕ} (p : Fin (m+1)) : Option (Fin m) ≃ Option (Fin m) :=
  (finSuccEquiv m).symm.trans ((Equiv.swap 0 p).trans (finSuccEquiv m))

lemma finSuccEquiv_symm_none (m : ℕ) : (finSuccEquiv m).symm none=0 := by
  apply (finSuccEquiv m).injective
  simp only [Equiv.apply_symm_apply,finSuccEquiv_zero]

end
end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_LargeMarginReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computed reference coordinates for the large completion rectangle -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms SmallContextCoordinates SmallContextFibres
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ}

def optionIndexEquiv (k : ℕ) (hk : 0 < k) : Option (Fin (k-1)) ≃ Fin k := by
  cases k with
  | zero => omega
  | succ k => exact (finSuccEquiv k).symm

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_TranslationDecisionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary arithmetic for the completion translation test -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms
open scoped BigOperators

abbrev MarginPair := List ℕ×List ℕ
abbrev TranslationCell := (MarginPair×MarginPair)×(ℕ×ℕ)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BoundedProfileWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial loop for the encoded small-profile walk -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

abbrev ProfileWord := List Bool×List Bool

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteMetropolisTransport
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact observable transport of optional proposals and acceptance -/

namespace ContingencyTables.FiniteObservableTransport

open scoped Classical
noncomputable section

variable {X P Q U V : Type*} [Fintype P] [Fintype Q] [Fintype U] [Fintype V]

def proposedMove (start : X) (pick : Option X) (accept : X → U → Bool) (bits : U) : X :=
  match pick with
  | none => start
  | some next => if accept next bits then next else start

end
end ContingencyTables.FiniteObservableTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteWordSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact bounded list slices of a finite Boolean word -/

namespace ContingencyTables.FiniteWordSlices

open FairBits

abbrev Fields (p q k : ℕ) :=
  (Fin 1 → Bool) × ((Fin p → Bool) × (((Fin q → Bool) × (Fin q → Bool)) × (Fin k → Bool)))

end ContingencyTables.FiniteWordSlices

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteEncodedHistory
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complete histories under an encoded transition law -/

namespace ContingencyTables.FiniteObservableTransport

open scoped Classical

def traceAfter {C U : Type*} (step : C → U → C) (c : C) : List U → List C
  | [] => []
  | u::us => let d := step c u; d::traceAfter step d us

def traceStates {C U : Type*} (step : C → U → C) (c : C) (us : List U) : List C :=
  c::traceAfter step c us

end ContingencyTables.FiniteObservableTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPositiveWordBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Public polynomial bounds for the executed positive counting words -/
namespace ContingencyTables.CountingPositiveWordBound
open MatchingFPRAS MatchingFPRAS.TreeTyped CountingPublicInputBounds Polynomial
open scoped Classical
noncomputable section
variable {m n : ℕ}

def widthPolynomial : Polynomial ℕ :=
  CountingWordsBound.wordPolynomial+CountingMarkerBounds.paddingPolynomial+2*X+1

end
end ContingencyTables.CountingPositiveWordBound

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_NatListEquality
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary list equality for matching tabulated states and outputs -/

namespace ContingencyTables.NatListEquality
open MatchingFPRAS MatchingFPRAS.TreeTyped

def indices (z : List ℕ×List ℕ) : List ℕ := List.range z.1.length

def atEqual (z : (List ℕ×List ℕ)×ℕ) : Bool := decide (z.1.1.getD z.2 0=z.1.2.getD z.2 0)

def listEqual (z : List ℕ×List ℕ) : Bool :=
  decide (z.1.length=z.2.length) && (indices z).all (fun i => atEqual (z,i))

end ContingencyTables.NatListEquality

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_AxisProposalTest
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Testing dense adjacency by the polynomial list of signed directions -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary

abbrev AxisNumberData := (ℕ×List ℕ)×ℕ

abbrev ProposalTestData := (ℕ×List ℕ)×List ℕ

def proposalIndices (z : ProposalTestData) : List ℕ := List.range (2*z.1.2.length)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteAcceptCounts
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer transition counts without enumerating acceptance bits -/

namespace ContingencyTables.FiniteAcceptCounts
open ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [Nonempty β]

def denominator (K : ℕ) : ℕ := Fintype.card β * 2^K

def offCount (a : α) (proposal : β → Option α) (gap : α → ℕ) (K : ℕ) (b : α) : ℕ :=
  if b=a then 0 else
    (Finset.univ.filter (fun z => proposal z=some b)).card * 2^(K-gap b)

def row (a : α) (proposal : β → Option α) (gap : α → ℕ) (K : ℕ) (b : α) : ℕ :=
  offCount a proposal gap K b +
    if b=a then denominator (β := β) K - ∑ x,offCount a proposal gap K x else 0

lemma denominator_pos (K : ℕ) : 0<denominator (β := β) K := by
  unfold denominator
  exact Nat.mul_pos Fintype.card_pos (by positivity)

end
end ContingencyTables.FiniteAcceptCounts

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseMatrixProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial assembly of the dense count matrix in column order -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators Classical

abbrev CountMatrixContext := (List Bool×ℕ)×((List ℕ×List ℕ)×ℕ)
abbrev CountMatrixData := CountMatrixContext×List (List ℕ)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseMatrixWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary matrix propagation of the implemented dense walk -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators Classical

abbrev MatrixWalkData := (List Bool×CountMatrixData)×List ℕ

def initialEntry (z : List ℕ×List ℕ) : ℕ :=
  if NatListEquality.listEqual z then 1 else 0

def initialVector (z : List (List ℕ)×List ℕ) : List ℕ :=
  z.1.map (fun a => initialEntry (z.2,a))

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteGridWords
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit finite-box state enumeration, independent of sampling precision -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators

abbrev GridEnumerationData := List Bool×ℕ

def clippedGridPowerInput (z : GridEnumerationData×ℕ) : ℕ×ℕ :=
  (z.1.2,min z.2 z.1.1.length)

abbrev GridCoordinateData := (GridEnumerationData×ℕ)×ℕ

def gridCoordinateIndices (z : GridEnumerationData×ℕ) : List ℕ := List.range z.1.1.length

def gridDigitEquiv (K : ℕ) : Fin K ≃ Set.Icc (0:ℤ) ((K:ℤ)-1) where
  toFun x := ⟨(x.val:ℤ),by
    change 0≤(x.val:ℤ) ∧ (x.val:ℤ)≤(K:ℤ)-1
    have hx := x.isLt
    omega⟩
  invFun x := ⟨x.val.toNat,by
    have hx0 : 0≤x.val := x.property.1
    have hxK : x.val≤(K:ℤ)-1 := x.property.2
    omega⟩
  left_inv x := by ext; simp
  right_inv x := by
    apply Subtype.ext
    have hx0 : 0≤x.val := x.property.1
    dsimp
    omega

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseEnumeratedMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing every state of the dense transition table -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators

abbrev EnumeratedMatrixInput := CountMatrixContext×List Bool

def enumerationData (z : EnumeratedMatrixInput) : GridEnumerationData :=
  (z.2,4*z.1.2.2^8)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_GridIndexProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary indexing into the explicitly enumerated grid -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators

abbrev GridIndexData := List ℕ×ℕ

def gridIndexPowerInput (z : GridIndexData×ℕ) : GridEnumerationData×ℕ :=
  (((z.1.1.map (fun _ => false)),z.1.2),z.2)

def gridIndexIndices (z : GridIndexData) : List ℕ := List.range z.1.length

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CompletionEnumerationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit free-box enumeration with binary completion tests -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms
open scoped BigOperators Classical

abbrev CompletionMargins := List ℕ×List ℕ

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_OnlineIntegerRetry
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed online machine for repeat-until-success -/

namespace ContingencyTables.OnlineIntegerRetry
open MatchingFPRAS
open MatchingFPRAS.OnlineStack
open MatchingFPRAS.PhysicalStream

inductive Label where
  | prepare | trial | decode | test | retry | finish | halt
  deriving DecidableEq, Inhabited

instance instFintypeLabel : Fintype Label := ⟨{.prepare,.trial,.decode,.test,.retry,.finish,.halt}, by
  intro x; cases x <;> simp⟩

end ContingencyTables.OnlineIntegerRetry

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerLaw
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer counts for the finite stages of law tabulation -/

namespace ContingencyTables
open scoped BigOperators

/-- Counts of equally likely slots. The denominator is explicit so that
composition can reserve ignored bits without enumerating them. -/
structure IntegerLaw (A : Type*) [Fintype A] (Q : ℕ) where
  count : A → ℕ
  total : ∑ a,count a=Q

namespace IntegerLaw
open ResidualMixture FirstSuccess
open scoped Classical
noncomputable section
variable {A B : Type*} [Fintype A] [Fintype B] {Q P : ℕ}

def rebase (p : IntegerLaw A Q) (h : Q=P) : IntegerLaw A P :=
  ⟨p.count,p.total.trans h⟩

def scale (p : IntegerLaw A Q) (P : ℕ) : IntegerLaw A (Q*P) where
  count a := p.count a*P
  total := by rw [←Finset.sum_mul,p.total]

def point [DecidableEq A] (Q : ℕ) (a : A) : IntegerLaw A Q where
  count b := if b=a then Q else 0
  total := by simp

def push [DecidableEq B] (p : IntegerLaw A Q) (f : A → B) : IntegerLaw B Q where
  count b := ∑ a,if f a=b then p.count a else 0
  total := by
    rw [Finset.sum_comm]
    simpa using p.total

def bind (p : IntegerLaw A Q) (K : A → IntegerLaw B P) : IntegerLaw B (Q*P) where
  count b := ∑ a,p.count a*(K a).count b
  total := by
    rw [Finset.sum_comm]
    simp only [←Finset.mul_sum,(K _).total,←Finset.sum_mul,p.total]

def product (p : IntegerLaw A Q) (q : IntegerLaw B P) : IntegerLaw (A×B) (Q*P) where
  count x := p.count x.1*q.count x.2
  total := by
    rw [Fintype.sum_prod_type]
    simp only [←Finset.mul_sum,q.total,←Finset.sum_mul,p.total]

variable [DecidableEq A]

def retryCount (p : IntegerLaw (Option A) Q) (fallback : A) : ℕ → A → ℕ
  | 0,a => if a=fallback then 1 else 0
  | N+1,a => p.count (some a)*Q^N+p.count none*retryCount p fallback N a

lemma retryCount_total (p : IntegerLaw (Option A) Q) (fallback : A) (N : ℕ) :
    ∑ a,retryCount p fallback N a=Q^N := by
  induction N with
  | zero => simp [retryCount]
  | succ N ih =>
    have ht:=p.total
    rw [Fintype.sum_option] at ht
    simp only [retryCount,Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum,ih]
    rw [←add_mul,add_comm,ht,pow_succ']

def retry (p : IntegerLaw (Option A) Q) (fallback : A) (N : ℕ) : IntegerLaw A (Q^N) :=
  ⟨retryCount p fallback N,retryCount_total p fallback N⟩

end
end IntegerLaw
end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PreparedOffsetCount
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary evaluation of the offset numerator product -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary FairBits
open scoped BigOperators

/-- A shared bit allowance, widths, actual bit lengths and offsets. -/
abbrev PreparedOffsetData := ((List Bool×List ℕ)×List ℕ)×List ℕ

def preparedOffsetIndices (z : PreparedOffsetData) : List ℕ := List.range z.1.1.2.length

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_RetryNumeratorProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary first-success numerators via a two-coordinate recurrence -/

namespace ContingencyTables.RetryNumeratorPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

/-- Unary trial count; denominator, failure count, success count, fallback match. -/
abbrev Input := List Bool×((ℕ×ℕ)×(ℕ×Bool))

def setup (z : Input) : ℕ×(List (List ℕ)×List ℕ) :=
  (z.1.length,([[z.2.1.2,z.2.2.1],[0,z.2.1.1]],[(if z.2.2.2 then 1 else 0),1]))

def recurrence (Q phi alpha initial : ℕ) : ℕ → ℕ
  | 0 => initial
  | n+1 => phi*recurrence Q phi alpha initial n+alpha*Q^n

end ContingencyTables.RetryNumeratorPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_VectorRetryProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # First-success propagation of an entire vector of integer counts -/

namespace ContingencyTables.VectorRetryPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators

/-- Trial marker, denominator, success counts, fallback index. -/
abbrev Input := (List Bool×ℕ)×(List ℕ×ℕ)

def failure (z : Input) : ℕ := z.1.2-z.2.1.sum

def entryInput (z : Input×ℕ) : RetryNumeratorPrograms.Input :=
  (z.1.1.1,((z.1.1.2,failure z.1),(z.1.2.1.getD z.2 0,decide (z.2=z.1.2.2))))

def indices (z : Input) : List ℕ := List.range z.2.1.length

end ContingencyTables.VectorRetryPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerResidualCorrection
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer realization of the exact residual correction law -/

namespace ContingencyTables.IntegerResidualCorrection
open ResidualMixture
open scoped BigOperators Classical
noncomputable section

variable {A : Type*} [Fintype A] [Nonempty A] {Q : ℕ}

def count (p : IntegerLaw A Q) (T : ℕ) (a : A) : ℕ :=
  (residualNumerator Q T (fun x => (p.count x : ℤ)) a).toNat

lemma denominator_pos (hQ : 0<Q) : 0<Fintype.card A*Q :=
  Nat.mul_pos Fintype.card_pos hQ

end
end ContingencyTables.IntegerResidualCorrection

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ResidualWeightProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary computation of the rare branch's integer weights -/

namespace ContingencyTables.ResidualWeightPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

abbrev Input := (ℕ×ℕ)×(ℕ×ℕ)

/-- Common denominator, inverse branch probability, number of tables,
and the ordinary draw's numerator. -/
def count (z : Input) : ℕ := z.1.1*z.1.2-z.2.1*(z.1.2-1)*z.2.2

end ContingencyTables.ResidualWeightPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperOuterBudget
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The first paper's explicit trial and approximation budgets -/

namespace ContingencyTables

def outerTrials (d k : ℕ) : ℕ := d^4*(k+1)
def outerSteps (d b k : ℕ) : ℕ := d^200*(k+b)^2
def outerAccuracy (d b k : ℕ) : ℕ := d^4*(k+b)^2

lemma two_pow_le_exp_nat (n : ℕ) : (2:ℝ)^n ≤ Real.exp (n:ℝ) := by
  have hbase : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  simpa only [← Real.exp_nat_mul,mul_one] using pow_le_pow_left₀ (by norm_num) hbase n

lemma exp_neg_nat_le_inverse_two_pow (n : ℕ) :
    Real.exp (-(n:ℝ)) ≤ 1/(2:ℝ)^n := by
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by positivity) (two_pow_le_exp_nat n)

lemma outer_failure_error (d k : ℕ) (hd : 14 ≤ d) :
    Real.exp (-(outerTrials d k:ℝ)/(2*(1+(d:ℝ)^2))) ≤ 1/(2:ℝ)^(k+2) := by
  have hdR : (14:ℝ) ≤ d := by exact_mod_cast hd
  have hsq : (196:ℝ) ≤ (d:ℝ)^2 := by nlinarith
  have hc : 4*(1+(d:ℝ)^2) ≤ (d:ℝ)^4 := by nlinarith [sq_nonneg ((d:ℝ)^2-2)]
  have hm := mul_le_mul_of_nonneg_right hc (show 0 ≤ (k:ℝ)+1 by positivity)
  have ht : (k:ℝ)+2 ≤ (outerTrials d k:ℝ)/(2*(1+(d:ℝ)^2)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    dsimp only [outerTrials]
    push_cast
    nlinarith [mul_nonneg (show (0:ℝ) ≤ k by positivity) (show 0 ≤ 1+(d:ℝ)^2 by positivity)]
  exact (Real.exp_le_exp.mpr (by
    rw [neg_div]
    push_cast
    exact neg_le_neg ht)).trans (exp_neg_nat_le_inverse_two_pow (k+2))

lemma outer_mixing_error (d b k C : ℕ) (hd : 14 ≤ d) (hb : d ≤ b) (hk : 1 ≤ k)
    (hC : C+1 ≤ 2^b) :
    (outerTrials d k:ℝ)*((C+1:ℕ):ℝ)^(2*d)*
      Real.exp (-(outerSteps d b k:ℝ)/(d:ℝ)^160) ≤ 1/(2:ℝ)^(k+2) := by
  let t : ℝ := (k:ℝ)+b
  have ht : 15 ≤ t := by dsimp only [t]; exact_mod_cast (show 15 ≤ k+b by omega)
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdt : (d:ℝ) ≤ t := by dsimp only [t]; exact_mod_cast (show d ≤ k+b by omega)
  have hbt : (b:ℝ) ≤ t := by dsimp only [t]; linarith [Nat.cast_nonneg k (α := ℝ)]
  have hkt : (k:ℝ) ≤ t := by dsimp only [t]; linarith [Nat.cast_nonneg b (α := ℝ)]
  have hde : (d:ℝ) ≤ Real.exp (d:ℝ) := by linarith [Real.add_one_le_exp (d:ℝ)]
  have hke : (k:ℝ)+1 ≤ Real.exp ((k:ℝ)+1) := by
    linarith [Real.add_one_le_exp ((k:ℝ)+1)]
  have hJ : (outerTrials d k:ℝ) ≤ Real.exp (4*(d:ℝ)+k+1) := by
    calc
      _ = (d:ℝ)^4*((k:ℝ)+1) := by simp only [outerTrials,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
      _ ≤ (Real.exp (d:ℝ))^4*Real.exp ((k:ℝ)+1) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hde 4) hke (by positivity) (by positivity)
      _ = _ := by rw [← Real.exp_nat_mul,← Real.exp_add]; congr 1; norm_num; ring
  have hCe : (C+1:ℕ) ≤ Real.exp (b:ℝ) :=
    (show ((C+1:ℕ):ℝ) ≤ (2:ℝ)^b by exact_mod_cast hC).trans (two_pow_le_exp_nat b)
  have hCP : (((C+1:ℕ):ℝ))^(2*d) ≤ Real.exp (2*(d:ℝ)*b) := by
    calc
      _ ≤ (Real.exp (b:ℝ))^(2*d) := pow_le_pow_left₀ (by positivity) hCe _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hcoef : (3:ℝ) ≤ (d:ℝ)^40 := by
    exact_mod_cast ((show 3 ≤ d by omega).trans (Nat.le_self_pow (by decide) d))
  have hdb : (d:ℝ)*b ≤ t^2 := by
    have hh := mul_le_mul hdt hbt (by positivity : (0:ℝ) ≤ b) (by linarith : 0 ≤ t)
    nlinarith
  have hexp : 4*(d:ℝ)+k+1+2*(d:ℝ)*b+((k:ℝ)+2) ≤ (d:ℝ)^40*t^2 := by
    have hh := mul_le_mul_of_nonneg_right hcoef (sq_nonneg t)
    nlinarith
  calc
    _ ≤ Real.exp (4*(d:ℝ)+k+1)*Real.exp (2*(d:ℝ)*b)*
        Real.exp (-(outerSteps d b k:ℝ)/(d:ℝ)^160) :=
      mul_le_mul_of_nonneg_right (mul_le_mul hJ hCP (by positivity) (by positivity)) (by positivity)
    _ = Real.exp (4*(d:ℝ)+k+1+2*(d:ℝ)*b-(d:ℝ)^40*t^2) := by
      rw [← Real.exp_add,← Real.exp_add]
      congr 1
      dsimp only [outerSteps,t]
      push_cast
      field_simp
      ring
    _ ≤ Real.exp (-((k+2:ℕ):ℝ)) := Real.exp_le_exp.mpr (by push_cast; linarith)
    _ ≤ _ := exp_neg_nat_le_inverse_two_pow (k+2)

lemma nat_pow_le_two_pow (n a : ℕ) : n^a ≤ 2^(n*a) := by
  calc
    _ ≤ (2^n)^a := Nat.pow_le_pow_left n.lt_two_pow_self.le a
    _ = _ := (pow_mul _ _ _).symm

lemma outer_product_bit_bound (d b k : ℕ) (hd : 14 ≤ d) (hb : d ≤ b) (hk : 1 ≤ k) :
    outerTrials d k*(outerSteps d b k+1)*2^(k+2) ≤ 2^(outerAccuracy d b k) := by
  let t := k+b
  have ht : 15 ≤ t := by dsimp only [t]; omega
  have hpT : 1 ≤ outerSteps d b k := by
    dsimp only [outerSteps]
    have hd0 : 0 < d := by omega
    have ht0 : 0 < k+b := by omega
    exact Nat.succ_le_of_lt (Nat.mul_pos (pow_pos hd0 _) (pow_pos ht0 _))
  have hJ : outerTrials d k ≤ 2^(4*d+k+1) := by
    unfold outerTrials
    calc
      _ ≤ 2^(d*4)*2^(k+1) := Nat.mul_le_mul (nat_pow_le_two_pow d 4) (k+1).lt_two_pow_self.le
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hT : outerSteps d b k+1 ≤ 2^(200*d+2*t+1) := by
    have hm : outerSteps d b k ≤ 2^(200*d+2*t) := by
      unfold outerSteps
      calc
        _ ≤ 2^(d*200)*2^((k+b)*2) := Nat.mul_le_mul (nat_pow_le_two_pow d 200)
          (nat_pow_le_two_pow (k+b) 2)
        _ = _ := by rw [← pow_add]; congr 1; dsimp only [t]; omega
    calc
      _ ≤ 2*outerSteps d b k := by omega
      _ ≤ 2*2^(200*d+2*t) := Nat.mul_le_mul_left 2 hm
      _ = _ := by rw [pow_succ]; omega
  have hexp : (4*d+k+1)+(200*d+2*t+1)+(k+2) ≤ outerAccuracy d b k := by
    have hcoef : 209 ≤ d^4 := (by norm_num : 209 ≤ 14^4).trans (Nat.pow_le_pow_left hd 4)
    have htq : t ≤ t^2 := Nat.le_self_pow (by decide) t
    have hm := Nat.mul_le_mul hcoef htq
    have hdt : d ≤ t := by dsimp only [t]; omega
    have hkt : k ≤ t := by dsimp only [t]; omega
    change _ ≤ d^4*t^2
    omega
  calc
    _ ≤ (2^(4*d+k+1)*2^(200*d+2*t+1))*2^(k+2) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul hJ hT)
    _ = 2^((4*d+k+1)+(200*d+2*t+1)+(k+2)) := by rw [← pow_add,← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hexp

lemma outer_approximation_error (d b k : ℕ) (hd : 14 ≤ d) (hb : d ≤ b) (hk : 1 ≤ k) :
    (outerTrials d k:ℝ)*(outerSteps d b k+1)/(2:ℝ)^(outerAccuracy d b k) ≤
      1/(2:ℝ)^(k+2) := by
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simp only [one_mul]
  exact_mod_cast outer_product_bit_bound d b k hd hb hk

theorem outer_total_error (d b k C : ℕ) (hd : 14 ≤ d) (hb : d ≤ b) (hk : 1 ≤ k)
    (hC : C+1 ≤ 2^b) :
    Real.exp (-(outerTrials d k:ℝ)/(2*(1+(d:ℝ)^2)))+
      (outerTrials d k:ℝ)*((C+1:ℕ):ℝ)^(2*d)*
        Real.exp (-(outerSteps d b k:ℝ)/(d:ℝ)^160)+
      (outerTrials d k:ℝ)*(outerSteps d b k+1)/(2:ℝ)^(outerAccuracy d b k) ≤
      1/(2:ℝ)^k := by
  have h₁ := outer_failure_error d k hd
  have h₂ := outer_mixing_error d b k C hd hb hk hC
  have h₃ := outer_approximation_error d b k hd hb hk
  have he : 4*(1/(2:ℝ)^(k+2))=1/(2:ℝ)^k := by
    rw [pow_add]
    norm_num
    field_simp
  have hp : 0 ≤ 1/(2:ℝ)^(k+2) := by positivity
  linarith

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileWordProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Parsing the independent words of the physical outer trial -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

/-- The schedule contains the number of steps and the two step widths. -/
abbrev ProfileWordSchedule := (ℕ×ℕ)×ℕ
abbrev ProfileWordInput := ProfileWordSchedule×List Bool

def splitProfileWord (z : ℕ×List Bool) : ProfileWord := (z.2.take z.1,z.2.drop z.1)

def profileWordWidth (z : ProfileWordInput) : ℕ := z.1.1.2+z.1.2

def profileWalkWidth (z : ProfileWordInput) : ℕ := z.1.1.1*profileWordWidth z

def profileTerminalWord (z : ProfileWordInput) : List Bool := z.2.drop (profileWalkWidth z)

open FairBits GridBoundary
open scoped Classical
end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileScheduleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the complete outer sampling schedule from binary margins -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

abbrev SamplingParameters := (List ℕ×List ℕ)×ℕ

def marginPadding (z : List ℕ×List ℕ) : ℕ := (marginDimension z)^12

def marginStateBound (z : List ℕ×List ℕ) : ℕ := (((z.1.sum+(marginDimension z*marginPadding z))+marginThreshold z)+2)

def marginBinaryLength (z : List ℕ×List ℕ) : ℕ := (marginDimension z+(Nat.clog 2) ((marginStateBound z+2)))

def parameterDimension (z : SamplingParameters) : ℕ := marginDimension z.1

def parameterBinaryLength (z : SamplingParameters) : ℕ := marginBinaryLength z.1

def parameterTrials (z : SamplingParameters) : ℕ := ((parameterDimension z)^4*(z.2+1))

def parameterSteps (z : SamplingParameters) : ℕ := ((parameterDimension z)^200*((z.2+parameterBinaryLength z))^2)

def parameterAccuracy (z : SamplingParameters) : ℕ := ((parameterDimension z)^4*((z.2+parameterBinaryLength z))^2)

def parameterProposalWidth (z : SamplingParameters) : ℕ := (Nat.clog 2) ((32*(parameterDimension z)^2))

def parameterCompletionWidth (z : SamplingParameters) : ℕ := (25*((((parameterDimension z+parameterBinaryLength z)+parameterAccuracy z)+1))^62)

def parameterWordCount (z : SamplingParameters) : ℕ := (parameterTrials z*((parameterSteps z*(parameterProposalWidth z+parameterCompletionWidth z))+parameterCompletionWidth z))

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileSamplingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparing and executing the complete profile sampler -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

def samplingSchedule (z : SamplingParameters) : ProfileWordSchedule :=
  ((parameterSteps z,parameterProposalWidth z),parameterCompletionWidth z)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfilePublicProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sampler's public binary parser and matrix printer -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped MatchingFPRAS.LiteralCodec
open DensePrograms

/-- Safely locate the precision field after the two margin vectors. -/
def samplingPrecision (ns : List ℕ) : ℕ :=
  (ns.drop (2+ns.headD 0+ns.tail.headD 0)).headD 0

def samplingInput (ns : List ℕ) : SamplingParameters :=
  (GreedyFeasibleTable.marginLists ns,samplingPrecision ns)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_AllSamplingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single computed sampler for large and all-small rectangles -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

def parameterUnitWords (z : SamplingParameters) : ℕ :=
  parameterTrials z*(parameterSteps z*parameterProposalWidth z)

attribute [local irreducible] parameterUnitWords

abbrev SamplingWordInput := SamplingParameters×List Bool

def unitSamplingBits (z : SamplingWordInput) : List Bool :=
  z.2.take (parameterUnitWords z.1)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalTableEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enumerating original tables by all their bounded entries -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

/-- Dummy leading margins reuse the rectangular free-array layout only. -/
def originalLayoutMargins (z : CompletionMargins) : CompletionMargins := (0::z.1,0::z.2)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalTableBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full original-table box and its unique feasible entries -/

namespace ContingencyTables.OriginalTableBox
open DensePrograms ProfilePrograms
open scoped BigOperators Classical
noncomputable section

abbrev Box (m n N : ℕ) := Fin (m*n) → Fin (N+1)
abbrev Index (m n N : ℕ) := Fin ((N+1)^(m*n))

def matrix {m n N : ℕ} (z : Box m n N) : Fin m → Fin n → ℕ :=
  fun i j => (z (finProdFinEquiv (i,j))).val

end
end ContingencyTables.OriginalTableBox

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_UnaryMarkers
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the bounded unary loop markers used in tabulation -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

def unaryMarkers (n : ℕ) : List Bool := (List.range n).map (fun _ => false)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IndexedTableLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Embedding accepted-table laws into the computed completion list -/

namespace ContingencyTables.IndexedTableLaw
open scoped BigOperators Classical
noncomputable section
variable {m n N Q : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)

abbrev Index (m n N : ℕ) := Fin ((N+1)^(m*n))

end
end ContingencyTables.IndexedTableLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerEquivLaw
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer laws under bijective coordinate changes -/

namespace ContingencyTables.IntegerLaw
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] {Q : ℕ}

/-- A coordinate permutation leaves the common denominator unchanged. -/
def equiv (p : IntegerLaw A Q) (e : A ≃ B) : IntegerLaw B Q where
  count b := p.count (e.symm b)
  total := (e.symm.sum_comp p.count).trans p.total

@[simp] lemma equiv_count (p : IntegerLaw A Q) (e : A ≃ B) (b : B) :
    (p.equiv e).count b=p.count (e.symm b) := rfl

end ContingencyTables.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BooleanEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enumerating only the short proposal word -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

def digitBool (a : ℕ) : Bool := decide (a=1)

def booleanEnumeration (s : ℕ) : Fin (2^s) ≃ (Fin s → Bool) :=
  finFunctionFinEquiv.symm.trans (Equiv.piCongrRight (fun _ => finTwoEquiv))

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BooleanIntegerLaw
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent Boolean words combined with cached integer laws -/

namespace ContingencyTables.IntegerLaw
open FirstSuccess FairBits ResidualMixture
open scoped BigOperators Classical
noncomputable section

def boolean (n : ℕ) : IntegerLaw (Fin n → Bool) (2^n) where
  count _ := 1
  total := by simp

variable {B C : Type*} [Fintype B] [Fintype C] [DecidableEq C]

/-- A short proposal word and an independently drawn cached completion
reserve their full combined word length. -/
def booleanFinish {s f : ℕ} (p : IntegerLaw B (2^f))
    (finish : (Fin s → Bool) → B → C) : IntegerLaw C (2^(s+f)) :=
  (((boolean s).product p).push (fun z => finish z.1 z.2)).rebase (pow_add 2 s f).symm

end
end ContingencyTables.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperCompletionLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual finite-word completion laws for the implemented small chain -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open ResidualMixture FirstSuccess FairBits

lemma dyadicError_cast (n : ℕ) : ((1/(2:ℚ)^n:ℚ):ℝ)=(2:ℝ)^(-(n:ℝ)) := by
  simp only [one_div,Rat.cast_inv,Rat.cast_pow,Rat.cast_ofNat,
    Real.rpow_neg_natCast,zpow_neg,zpow_natCast]


end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_UniformPartialRejection
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rejecting a uniform finite object through an explicit successful bijection -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture

noncomputable section
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
variable (p : S → Prop) (e : A ≃ {s // p s})

def partialEquivDraw (s : S) : Option A :=
  if h : p s then some (e.symm ⟨s,h⟩) else none

omit [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] in
lemma partialEquivDraw_eq_some (s : S) (a : A) :
    partialEquivDraw p e s=some a ↔ s=(e a).val := by
  constructor
  · intro h
    unfold partialEquivDraw at h
    split_ifs at h with hs
    · have hh := congrArg (fun a => (e a).val) (Option.some.inj h)
      simpa only [Equiv.apply_symm_apply] using hh
  · intro h
    subst s
    simp [partialEquivDraw,(e a).property]

end
end ContingencyTables.FirstSuccess

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerMatrixPoint
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Propagating an executable point mass through an integer matrix -/

namespace ContingencyTables.IntegerMatrixPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

def pointEntry (z : ℕ×ℕ) : ℕ := if z.2=z.1 then 1 else 0

def pointVector (z : List (List ℕ)×ℕ) : List ℕ :=
  (List.range z.1.length).map (fun j => pointEntry (z.2,j))

end ContingencyTables.IntegerMatrixPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ScheduledCountSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The scheduled executable numerator vector is the public sampler's law -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms
open SmallContextCoordinates OriginalTableBox ResidualMixture FirstSuccess
open scoped BigOperators Classical
noncomputable section

lemma dyadic_trialDenom (N s f : ℕ) :
    (2:ℕ)^(N*(s+f)+f)=(2^(s+f))^N*2^f := by
  rw [pow_add,←pow_mul]
  congr 2
  exact Nat.mul_comm _ _


end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactIntegerChoice
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact integer-weighted choice for the residual correction branch -/

namespace ContingencyTables.ExactIntegerChoice
open MatchingFPRAS MatchingFPRAS.FiniteChoice ResidualMixture FirstSuccess FairBits
open scoped BigOperators Classical

noncomputable section
variable {r : ℕ} (w : Fin r → ℕ)

def totalWeight : ℕ := ∑ i,w i

def normalized : Fin r → ℚ := fun i => (w i:ℚ)/totalWeight w

def prefixWeight (n : ℕ) : ℕ := ∑ i,if i.val<n then w i else 0

lemma normalized_total (h : 0<totalWeight w) : ∑ i,normalized w i=1 := by
  simp only [normalized,←Finset.sum_div,←Nat.cast_sum]
  exact div_self (by exact_mod_cast h.ne' : (totalWeight w:ℚ)≠0)

/-- One bounded trial rejects only the unused terminal indices. -/
def intervalTrial {V Q : ℕ} (_h : V≤Q) (j : Fin Q) : Option (Fin V) :=
  if hj : j.val<V then some ⟨j.val,hj⟩ else none

/-- A rational choice with integer weights, after a single binary rejection
trial. The sum of these masses is totalWeight / 2^k. -/
def weightedTrial (h : 0<totalWeight w) {Q : ℕ} (hQ : totalWeight w≤Q)
    (j : Fin Q) : Option (Fin r) :=
  (intervalTrial hQ j).map (choose (normalized w) (normalized_total w h) h)

end
end ContingencyTables.ExactIntegerChoice

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactIntegerProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary execution of an exact integer-weighted rejection trial -/

namespace ContingencyTables.ExactIntegerPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms

abbrev Input := List ℕ×List Bool

end ContingencyTables.ExactIntegerPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactIntegerRetry
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact law and geometric tail of integer rejection -/

namespace ContingencyTables.ExactIntegerChoice
open MatchingFPRAS ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section
variable {r Q : ℕ} (w : Fin r → ℕ) (h : 0<totalWeight w) [NeZero Q]
variable (hQ : totalWeight w≤Q)

def failure : ℚ := 1-(totalWeight w:ℚ)/Q

end
end ContingencyTables.ExactIntegerChoice

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactIntegerOnline
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete fair-bit integer trial used by exact correction -/

namespace ContingencyTables.ExactIntegerOnline
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream
open ExactIntegerChoice ExactIntegerPrograms FirstSuccess ResidualMixture
open scoped BigOperators Classical

def trialBits (w : List ℕ) : ℕ := Nat.clog 2 w.sum

end ContingencyTables.ExactIntegerOnline

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalRetryTail
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical halting tails from finite rejection prefixes -/

namespace ContingencyTables.PhysicalRetryTail
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost
open scoped BigOperators Classical

variable {Γ Q B : Type} [Inhabited Γ]

def live (c : Cfg Γ Q) : ℚ := if c.state=none then 0 else 1

def tail (M : _root_.OAI.MatchingFPRAS.PhysicalPost.Table Γ Q) (c : Cfg Γ Q) (n : ℕ) : ℝ :=
  ((experiment M n c).mean live:ℝ)

end ContingencyTables.PhysicalRetryTail

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperWordBudget
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial bound for the full first-paper Boolean word -/

namespace ContingencyTables

/-- Each outer trial contains a small walk and a fresh completion word. -/
def smallSamplerWordBudget (d b k : ℕ) : ℕ :=
  let f := 25*(d+b+outerAccuracy d b k+1)^62
  outerTrials d k*(outerSteps d b k*(Nat.clog 2 (32*d^2)+f)+f)

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactCoreProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One finite control graph for the ordinary and unbounded correction branches -/

namespace ContingencyTables.ExactCoreProgram
open MatchingFPRAS
open MatchingFPRAS.PhysicalStream MatchingFPRAS.OnlineStack
open ProfilePrograms DensePrograms

inductive Phase where
  | prepare | gate | choose | ordinaryInput | ordinary | rareInput | prepareRare | retry | halt
  deriving DecidableEq, Inhabited

instance instFintypePhase : Fintype Phase := ⟨{.prepare,.gate,.choose,.ordinaryInput,.ordinary,
  .rareInput,.prepareRare,.retry,.halt},by intro x; cases x <;> simp⟩

end ContingencyTables.ExactCoreProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalEventBounds
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Terminal-event bounds from finite stopping prefixes -/

namespace ContingencyTables.PhysicalEventBounds
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing
open scoped BigOperators Classical
noncomputable section
variable {Γ Q A : Type} [Inhabited Γ]

def event (P : Cfg Γ Q → Prop) (c : Cfg Γ Q) : ℚ := if P c then 1 else 0

end
end ContingencyTables.PhysicalEventBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalPublicLaw
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Public probabilities and physical terminal events -/

namespace ContingencyTables.PhysicalPublicLaw
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing
open PhysicalEventBounds
open scoped BigOperators Classical
noncomputable section

def outputs {Q : Type} (as : List Symbol) (d : Cfg Symbol Q) : Prop :=
  d.state=none ∧ d.tape.right₀=ListBlank.mk as

end
end ContingencyTables.PhysicalPublicLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileVectorMeasureBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform bounds for the executed nested trial-vector loops -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

noncomputable def vectorMeasurePolynomial : Polynomial ℕ :=
  let mat := (X+1)^2*(4*X+7)
  let terminal := (X+1)*(8*X+8)
  X*(mat+terminal+6*X+2)+X*(X+1)+5*X+2

end ContingencyTables.ProfilePrograms

end OAI
end


