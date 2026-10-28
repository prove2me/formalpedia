-- Prove2me | Definitions.Def_OAIQ086U001
-- name    : OAIQ086U001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T16:07:44.484981+00:00
-- url     : https://prove2.me/theorems/cdb5de85-83d9-43bc-a9b7-5e03e9772505
-- title:
--   Definitions bundle OAIQ086U001 of the split of OpenAI, The Unique Games Theorem
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniqueGamesTheorem.theorem11`, carved from OpenAI's openai/math development (OpenAI, *The Unique Games Theorem*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2217 declarations of OpenAI's Lean: 1172 definitions, 120 inductive types or structures, 47 instances and 878 theorems. The definitions and types are `OAI.UniqueGamesTheorem.Clean.WeightedPartition.fibre`, `OAI.UniqueGamesTheorem.Clean.cleanBit`, `OAI.UniqueGamesTheorem.Clean.maskCount`, `OAI.UniqueGamesTheorem.Decoder.ActualGoodRows.goodRowMass`, `OAI.UniqueGamesTheorem.Decoder.ActualSpectral.eta`, `OAI.UniqueGamesTheorem.Decoder.ConstantSelection.conditionalMass`, `OAI.UniqueGamesTheorem.Decoder.ConstantSelection.decodingMass`, `OAI.UniqueGamesTheorem.Decoder.ConstantSelection.variationBudget`, `OAI.UniqueGamesTheorem.Decoder.ConstantSelection.visibleMass`, `OAI.UniqueGamesTheorem.Decoder.NoiseSampler.samplerLaw`, `OAI.UniqueGamesTheorem.Decoder.PaddedLaw.pushforwardWeight`, `OAI.UniqueGamesTheorem.Decoder.SparseLaw.independentWeights`, `OAI.UniqueGamesTheorem.Decoder.SparseLaw.lineCount`, `OAI.UniqueGamesTheorem.Decoder.SparseLaw.mixture`, `OAI.UniqueGamesTheorem.Decoder.SparseLaw.singletonPairWeights`, `OAI.UniqueGamesTheorem.Decoder.SparseLaw.singletonSamplerWeights`, `OAI.UniqueGamesTheorem.Decoder.SparseLaw.uniformChiSquare`, `OAI.UniqueGamesTheorem.Decoder.SparseLaw.uniformWeights`, `OAI.UniqueGamesTheorem.Decoder.UniformFibers.selectedFiberEquiv`, `OAI.UniqueGamesTheorem.Decoder.VisibleTransfer.fiberEvent`, `OAI.UniqueGamesTheorem.Explicit.BipartiteGame`, `OAI.UniqueGamesTheorem.Explicit.BipartiteGame.Satisfied`, `OAI.UniqueGamesTheorem.Explicit.BipartiteGame.maxSatisfied`, `OAI.UniqueGamesTheorem.Explicit.BipartiteGame.satisfiedCount`, `OAI.UniqueGamesTheorem.Explicit.BipartiteGame.value`, `OAI.UniqueGamesTheorem.Explicit.MachineClone100.indices`, `OAI.UniqueGamesTheorem.Explicit.MachineClone100.triples`, `OAI.UniqueGamesTheorem.Explicit.MachineClone100Certified.timePolynomial`, `OAI.UniqueGamesTheorem.Explicit.MachineClone100Cleanup.cleanupSteps`, `OAI.UniqueGamesTheorem.Explicit.MachineClone100Cleanup.clearFields`, `OAI.UniqueGamesTheorem.Explicit.MachineClone100Loop.Record`, `OAI.UniqueGamesTheorem.Explicit.MachineClone100Loop.recordWords`, `OAI.UniqueGamesTheorem.Explicit.MachineClone100Model.Alphabet`, `OAI.UniqueGamesTheorem.Explicit.MachineClone100Model.Context`, `OAI.UniqueGamesTheorem.Explicit.MachineClone100Model.Label`, `OAI.UniqueGamesTheorem.Explicit.MachineClone100Model.State`, `OAI.UniqueGamesTheorem.Explicit.MachineClone100Model.Tape`, `OAI.UniqueGamesTheorem.Explicit.MachineClone100Model.cleanupNext`, `OAI.UniqueGamesTheorem.Explicit.MachineClone100Model.contextNext`, `OAI.UniqueGamesTheorem.Explicit.MachineClone100Model.contextOffset` and 1252 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `UniqueGames_Analysis_MatrixCharactersLemmas`, `UniqueGames_Decoding_ActualSpectralLemmas`, `UniqueGames_Decoding_AdviceFibersLemmas`, `UniqueGames_Decoding_MaskMomentLemmas`, `UniqueGames_Decoding_PaddedLaw`, `UniqueGames_Decoding_SparseLawLemmas`, `UniqueGames_Decoding_VisibleTransferLemmas`, `UniqueGames_Decoding_WeightedPartition`, `UniqueGames_Foundations_Basic`, `UniqueGames_Foundations_FiniteTrialsLemmas`, `UniqueGames_Foundations_LabelBound`, `UniqueGames_Foundations_PinskerLemmas`, `UniqueGames_Foundations_Rectangle`, `UniqueGames_Foundations_SamplingLemmas`, `UniqueGames_Games_FinishBoundsLemmas`, `UniqueGames_Games_ProductLemmas`, `UniqueGames_Games_ProductMachineSemantics`, `UniqueGames_Games_ProductTarget`, `UniqueGames_Games_SelectedCommonMarginalLemmas`, `UniqueGames_Games_SubdivisionTarget`, `UniqueGames_Games_UniformTarget`, `UniqueGames_Inverse_AffineWitnessLemmas`, `UniqueGames_Inverse_AffineWitnessNormalizationLemmas`, `UniqueGames_Inverse_KMSFoundationLemmas`, `UniqueGames_Inverse_MatrixChartIntervalsLemmas`, `UniqueGames_Inverse_MatrixChartLemmas`, `UniqueGames_Inverse_RowErasureLemmas`, `UniqueGames_Inverse_RowErasureMatrixLemmas`, `UniqueGames_Inverse_ShortcodeInterfaceLemmas`, `UniqueGames_Machines_FinalCNFLoopLemmas`, `UniqueGames_Machines_FinalCNFMachineLemmas`, `UniqueGames_Machines_FinalCNFOutputLemmas`, `UniqueGames_Machines_FinalCNFPattern`, `UniqueGames_Machines_FinalCNFRowPlanLemmas`, `UniqueGames_Machines_FinalCNFTemplate`, `UniqueGames_Machines_GraphCounterFinish`, `UniqueGames_Machines_GraphCounterModel`, `UniqueGames_Machines_GraphCounterStartLemmas`, `UniqueGames_Machines_MachineAppendAt`, `UniqueGames_Machines_MachineCanonicalOutputLemmas`, `UniqueGames_Machines_MachineCeilingPower`, `UniqueGames_Machines_MachineClone100`, `UniqueGames_Machines_MachineClone100Certified`, `UniqueGames_Machines_MachineClone100Loop`, `UniqueGames_Machines_MachineClone100TableLemmas`, `UniqueGames_Machines_MachineClone100Triples`, `UniqueGames_Machines_MachineCloudCount`, `UniqueGames_Machines_MachineCloudPadding`, `UniqueGames_Machines_MachineCloudPrefix`, `UniqueGames_Machines_MachineCloudRankLemmas`, `UniqueGames_Machines_MachineCompositionLemmas`, `UniqueGames_Machines_MachineDrainManyLemmas`, `UniqueGames_Machines_MachineExpanderFamily`, `UniqueGames_Machines_MachineExpanderFamilyBoundsLemmas`, `UniqueGames_Machines_MachineExpanderFamilyLoop`, `UniqueGames_Machines_MachineExpanderRow`, `UniqueGames_Machines_MachineExpanderRowCleanup`, `UniqueGames_Machines_MachineExpanderRowDivision`, `UniqueGames_Machines_MachineExpanderRowEmitLemmas`, `UniqueGames_Machines_MachineExpanderTableLoop`, `UniqueGames_Machines_MachineExpanderTableProgramLemmas`, `UniqueGames_Machines_MachineExpanderTableRows`, `UniqueGames_Machines_MachineFiniteAlphabet`, `UniqueGames_Machines_MachineFixedCopiesLemmas`, `UniqueGames_Machines_MachineFixedDivMod`, `UniqueGames_Machines_MachineInitialHeaders`, `UniqueGames_Machines_MachineLazyRows`, `UniqueGames_Machines_MachineLazyTable`, `UniqueGames_Machines_MachineLazyTableRuntime`, `UniqueGames_Machines_MachineLemmas`, `UniqueGames_Machines_MachineLogCounter`, `UniqueGames_Machines_MachineLookupCore`, `UniqueGames_Machines_MachineLookupDiscard`, `UniqueGames_Machines_MachineLookupLemmas`, `UniqueGames_Machines_MachineOverlayRows`, `UniqueGames_Machines_MachineOverlayTable`, `UniqueGames_Machines_MachinePaddedExpanderFamilyBoundsLemmas`, `UniqueGames_Machines_MachinePaddedOverlay`, `UniqueGames_Machines_MachinePaddingRowsLemmas`, `UniqueGames_Machines_MachinePortReindex`, `UniqueGames_Machines_MachineProductFieldLemmas`, `UniqueGames_Machines_MachineProductGatherBoundsLemmas`, `UniqueGames_Machines_MachineProductHeadersFrameLemmas`, `UniqueGames_Machines_MachineProductProgram`, `UniqueGames_Machines_MachineProductRuntime`, `UniqueGames_Machines_MachineProductSeed`, `UniqueGames_Machines_MachineRadixStepLemmas`, `UniqueGames_Machines_MachineRegularDummyRow`, `UniqueGames_Machines_MachineRegularFamily`, `UniqueGames_Machines_MachineRegularInternalRow`, `UniqueGames_Machines_MachineRegularMetadata`, `UniqueGames_Machines_MachineRepeat`, `UniqueGames_Machines_MachineSingleOrbitFinishLemmas`, `UniqueGames_Machines_MachineSingleOrbitProgramLemmas`, `UniqueGames_Machines_MachineSubdivisionBody`, `UniqueGames_Machines_MachineSubdivisionBodySpecLemmas`, `UniqueGames_Machines_MachineSubdivisionDynamicRowsLemmas`, `UniqueGames_Machines_MachineSubdivisionTableRead`, `UniqueGames_Machines_MachineSubroutineLemmas`, `UniqueGames_Machines_MachineTableSplit`, `UniqueGames_Machines_MachineTransducerCopy`, `UniqueGames_Machines_MachineTupleOdometer`, `UniqueGames_Machines_MachineUnaryAddAt`, `UniqueGames_Machines_MachineUnaryAffineAt`, `UniqueGames_Machines_MachineUnaryLessAtLemmas`, `UniqueGames_Machines_MachineUnaryMultiply`, `UniqueGames_Machines_MachineUniformCopyOrder`, `UniqueGames_Machines_MachineUniformRun`, `UniqueGames_Machines_MachineVertexPadding`, `UniqueGames_Machines_PoweringMachineRow`, `UniqueGames_PCP_AlphabetGraphLemmas`, `UniqueGames_PCP_AlphabetReductionLemmas`, `UniqueGames_PCP_AlphabetRetractionLemmas`, `UniqueGames_PCP_AlphabetTableBoundsLemmas`, `UniqueGames_PCP_AmplificationIteration`, `UniqueGames_PCP_AssignmentTester`, `UniqueGames_PCP_ClauseVerifierLemmas`, `UniqueGames_PCP_CleanupLemmas`, `UniqueGames_PCP_Clone100`, `UniqueGames_PCP_Clone100Triples`, `UniqueGames_PCP_CloudRoundingLemmas`, `UniqueGames_PCP_CodeComposition`, `UniqueGames_PCP_Emitter`, `UniqueGames_PCP_ExpanderRowControlLemmas`, `UniqueGames_PCP_ExpanderTableEnumeration`, `UniqueGames_PCP_ExpanderTables`, `UniqueGames_PCP_ExpandersLemmas`, `UniqueGames_PCP_FinalBooleanVerifier`, `UniqueGames_PCP_FinalConstantsLemmas`, `UniqueGames_PCP_FinalTableFormula`, `UniqueGames_PCP_FoldedEquationLemmas`, `UniqueGames_PCP_FourierResponseLemmas`, `UniqueGames_PCP_GenericGraphTables`, `UniqueGames_PCP_GraphTables`, `UniqueGames_PCP_HonestTestLemmas`, `UniqueGames_PCP_InitialGraphLemmas`, `UniqueGames_PCP_InputLemmas`, `UniqueGames_PCP_OverlayLemmas`, `UniqueGames_PCP_PoweringLabelsLemmas`, `UniqueGames_PCP_PoweringOpinionTables`, `UniqueGames_PCP_PoweringOpinionsLemmas`, `UniqueGames_PCP_PoweringTableSemanticsLemmas`, `UniqueGames_PCP_PoweringTablesLemmas`, `UniqueGames_PCP_Preprocessing`, `UniqueGames_PCP_PreprocessingLazyWords`, `UniqueGames_PCP_PreprocessingOverlayTables`, `UniqueGames_PCP_PreprocessingOverlayWords`, `UniqueGames_PCP_PreprocessingPaddingOffsets`, `UniqueGames_PCP_PreprocessingPaddingTables`, `UniqueGames_PCP_PreprocessingPaddingWords`, `UniqueGames_PCP_PreprocessingRegularLoopWordsLemmas`, `UniqueGames_PCP_PreprocessingRegularTablesLemmas`, `UniqueGames_PCP_PreprocessingTablesLemmas`, `UniqueGames_PCP_QueriesLemmas`, `UniqueGames_PCP_RawInitialTablesLemmas`, `UniqueGames_PCP_SourceContextLoad`, `UniqueGames_PCP_SourceFieldArrayLemmas`, `UniqueGames_PCP_SourceHeaderAccumulate`, `UniqueGames_PCP_SourceHeaderCounts`, `UniqueGames_PCP_SourceHonestLemmas`, `UniqueGames_PCP_SourceLoopInitLemmas`, `UniqueGames_PCP_SourceMachine`, `UniqueGames_PCP_SourceNoiseParameterLemmas`, `UniqueGames_PCP_SourceOccurrences`, `UniqueGames_PCP_SourceQueryLoopLemmas`, `UniqueGames_PCP_SourceQueryOrderLemmas`, `UniqueGames_PCP_SourceRuntimeSpace`, `UniqueGames_PCP_SourceSignaturePrepareLemmas`, `UniqueGames_PCP_VertexPadding`, `UniqueGames_PCP_ZigzagGraphsLemmas`, `UniqueGames_Reduction_ActualCanonicalLemmas`, `UniqueGames_Reduction_ActualCompleteness`, `UniqueGames_Reduction_AddressMachineSpace`, `UniqueGames_Reduction_AddressOdometerSchedule`, `UniqueGames_Reduction_AddressOutcomeSpecs`, `UniqueGames_Reduction_AddressTupleBody`, `UniqueGames_Reduction_AddressTupleBudget`, `UniqueGames_Reduction_AddressTuplePolynomialLemmas`, `UniqueGames_Reduction_CanonicalBodyTemplateLemmas`, `UniqueGames_Reduction_CloneMachineModelLemmas`, `UniqueGames_Reduction_EncodingLemmas`, `UniqueGames_Reduction_ExplicitLemmas`, `UniqueGames_Reduction_FixedOutcomes`, `UniqueGames_Reduction_GapSemanticsLemmas`, `UniqueGames_Reduction_MachineAddressEdgeLemmas`, `UniqueGames_Reduction_MachineAddressHeaders`, `UniqueGames_Reduction_MachineFieldTemplate`, `UniqueGames_Reduction_MachineRhsLoad`, `UniqueGames_Reduction_MachineTemplateAddress`, `UniqueGames_Reduction_MachineTransducer`, `UniqueGames_Reduction_ParameterSelection`, `UniqueGames_Reduction_RealTargetLemmas`, `UniqueGames_Reduction_SourceEquationLookupLemmas`, `UniqueGames_Repetition_AnalyticCheegerLemmas`, `UniqueGames_Repetition_AnalyticRateLemmas`, `UniqueGames_Repetition_CollisionLemmas`, `UniqueGames_Repetition_RoundingPaddingLemmas`, `UniqueGames_Repetition_RoundingSampling`, `UniqueGames_Repetition_RoundingThresholdLemmas`, `UniqueGames_Repetition_TensorAlgebraLemmas`.
--
--   **Imports.** It imports the published bundle `Def_UniqueGamesTheorem`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ086U003`, `OAIQ086U004` and `OAIQ086U005`.
-- source:
--   OpenAI, The Unique Games Theorem, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Unique-Games-Theorem-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_UniqueGamesTheorem

section
-- module Solutions.OAIQ086_UG.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_MatrixCharactersLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Normalized Fourier analysis of finite binary linear-map spaces

The coefficient normalization is uniform expectation on the primal space. The
Parseval sum over frequencies is an unnormalized sum. The underlying complex
Fourier system is the actual trace-character family on the finite additive group.
Completeness is proved directly from character cancellation and finite sums.
-/

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixFourier

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate
open Finset

section FiniteGroup

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Uniformly normalized complex Fourier coefficient. -/
def fourierCoeff (f : G → ℂ) (ψ : AddChar G ℂ) : ℂ :=
  𝔼 x, f x * star (ψ x)

end FiniteGroup

section LinearMaps

variable {E F : Type*}
variable [AddCommGroup E]
  [AddCommGroup F]

theorem complex_ofReal_expect {J : Type*} [Fintype J] (f : J → ℝ) :
    ((𝔼 j, f j : ℝ) : ℂ) = 𝔼 j, (f j : ℂ) := by
  simp only [Fintype.expect_eq_sum_div_card, Complex.ofReal_div, Complex.ofReal_natCast]
  congr 1
  exact map_sum Complex.ofRealHom f Finset.univ

end LinearMaps

end UniqueGamesTheorem.Fourier.MatrixFourier

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_AdviceFibersLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Finite latent samplers and their actual spectral law

This bridge counts all sampler outcomes, including repeated vectors and the
zero vector.  Uniform sampler detection is exactly the complement of the
matrix operator's annihilation multiplier.
-/

noncomputable section
open scoped BigOperators Classical

namespace UniqueGamesTheorem.Decoder.NoiseSampler

section FiniteLaw

variable {Noise V : Type*} [Fintype Noise] [Fintype V]

/-- The real pushforward of the uniform law on sampler outcomes. -/
def samplerLaw (noise : Noise → V) (v : V) : ℝ := by
  classical
  exact ∑ n, if noise n = v then (Fintype.card Noise : ℝ)⁻¹ else 0

end FiniteLaw

end UniqueGamesTheorem.Decoder.NoiseSampler

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_AffineWitnessLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.AffineWitness

abbrev F2 := ZMod 2

variable {D C R : Type*}
  [AddCommGroup D] [Module F2 D]
  [AddCommGroup C] [Module F2 C]
  [AddCommGroup R] [Module F2 R]

theorem add_self_binary (c : C) : c + c = 0 := by
  have h : (1 : F2) + 1 = 0 := by decide
  calc
    c + c = (1 : F2) • c + (1 : F2) • c := by simp
    _ = ((1 : F2) + 1) • c := (add_smul _ _ _).symm
    _ = 0 := by rw [h, zero_smul]

/-- A simultaneous row fiber and column slice, based at `M₀`. Agreement on
`Z` is exactly agreement with all column specifications spanning `Z`. -/
def InSlice (A : C →ₗ[F2] R) (Z : Submodule F2 D)
    (M₀ M : D →ₗ[F2] C) : Prop :=
  A.comp M = A.comp M₀ ∧ ∀ w ∈ Z, M w = M₀ w

/-- Changing the representative also changes the affine intercept. -/
theorem translate_target (A : C →ₗ[F2] R) (Z : Submodule F2 D)
    (M₀ M : D →ₗ[F2] C) (hM : InSlice A Z M₀ M)
    (z w : D) (hw : w ∈ Z) (u : C) :
    M (z + w) + (u + M₀ w) = M z + u := by
  rw [map_add, hM.2 w hw]
  calc
    (M z + M₀ w) + (u + M₀ w) = (M z + u) + (M₀ w + M₀ w) := by
      ac_rfl
    _ = M z + u := by rw [add_self_binary, add_zero]

theorem no_affine_representative (e : D →ₗ[F2] F2) (Z : Submodule F2 D)
    (z : D) (h : ¬ ∃ w ∈ Z, e (z + w) = 1) :
    e z = 0 ∧ ∀ w ∈ Z, e w = 0 := by
  have scalar_cases : ∀ a : F2, a = 0 ∨ a = 1 := by decide
  have hz : e z = 0 := by
    rcases scalar_cases (e z) with hz | hz
    · exact hz
    · exact False.elim (h ⟨0, Z.zero_mem, by simpa using hz⟩)
  refine ⟨hz, ?_⟩
  intro w hw
  rcases scalar_cases (e w) with hw0 | hw1
  · exact hw0
  · exact False.elim (h ⟨w, hw, by rw [map_add, hz, zero_add, hw1]⟩)

/-- Rank-one translation in the row kernel. -/
def shift (e : D →ₗ[F2] F2) (h : C) (M : D →ₗ[F2] C) : D →ₗ[F2] C :=
  M + e.smulRight h

@[simp] theorem shift_apply (e : D →ₗ[F2] F2) (h : C)
    (M : D →ₗ[F2] C) (x : D) : shift e h M x = M x + e x • h := rfl

@[simp] theorem shift_zero (e : D →ₗ[F2] F2) (M : D →ₗ[F2] C) :
    shift e 0 M = M := by
  ext x
  simp

theorem shift_add (e : D →ₗ[F2] F2) (h k : C) (M : D →ₗ[F2] C) :
    shift e (h + k) M = shift e h (shift e k M) := by
  ext x
  simp only [shift_apply, smul_add]
  ac_rfl

theorem shift_preserves_slice (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ M : D →ₗ[F2] C)
    (heZ : ∀ w ∈ Z, e w = 0) (h : A.ker) (hM : InSlice A Z M₀ M) :
    InSlice A Z M₀ (shift e h M) := by
  constructor
  · ext x
    have hx := LinearMap.congr_fun hM.1 x
    have hh : A (h : C) = 0 := h.property
    simpa only [LinearMap.comp_apply, shift_apply, map_add, map_smul,
      hh, smul_zero, add_zero] using hx
  · intro w hw
    simp only [shift_apply, heZ w hw, zero_smul, add_zero]
    exact hM.2 w hw

theorem shift_preserves_target (e : D →ₗ[F2] F2) (z : D) (hz : e z = 0)
    (u h : C) (M : D →ₗ[F2] C) :
    shift e h M z + u = M z + u := by
  simp only [shift_apply, hz, zero_smul, add_zero]

/-- Normalization preserves every affine target value on the complete slice. -/
theorem normalize (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C) (z : D) (u : C)
    (h : ∃ w ∈ Z, e (z + w) = 1) :
    ∃ z' : D, ∃ u' : C, e z' = 1 ∧
      ∀ M, InSlice A Z M₀ M → M z' + u' = M z + u := by
  obtain ⟨w, hw, he⟩ := h
  exact ⟨z + w, u + M₀ w, he, fun M hM => translate_target A Z M₀ M hM z w hw u⟩

end UniqueGamesTheorem.Inverse.AffineWitness

end

section

/-! Conversion between explicitly listed affine column specifications and the
span-based slice used in first-bit normalization. -/

namespace UniqueGamesTheorem.Inverse.AffineWitness

variable {D C R ι : Type*}
  [AddCommGroup D] [Module F2 D]
  [AddCommGroup C] [Module F2 C]
  [AddCommGroup R] [Module F2 R]

theorem columns_iff_span (q : ι → D) (t : ι → C)
    (M₀ M : D →ₗ[F2] C) (hM₀ : ∀ i, M₀ (q i) = t i) :
    (∀ i, M (q i) = t i) ↔
      ∀ w ∈ Submodule.span F2 (Set.range q), M w = M₀ w := by
  constructor
  · intro hM w hw
    apply LinearMap.eqOn_span (s := Set.range q) (x := w) ?_ hw
    rintro _ ⟨i, rfl⟩
    exact (hM i).trans (hM₀ i).symm
  · intro hM i
    exact (hM (q i) (Submodule.subset_span ⟨i, rfl⟩)).trans (hM₀ i)

/-- A nonempty explicit affine row/column system is precisely the based slice.
The right-hand sides `S₀` and `t` are retained without homogenization. -/
theorem explicit_slice_iff (A : C →ₗ[F2] R) (S₀ : D →ₗ[F2] R)
    (q : ι → D) (t : ι → C) (M₀ M : D →ₗ[F2] C)
    (hrow : A.comp M₀ = S₀) (hcol : ∀ i, M₀ (q i) = t i) :
    (A.comp M = S₀ ∧ ∀ i, M (q i) = t i) ↔
      InSlice A (Submodule.span F2 (Set.range q)) M₀ M := by
  unfold InSlice
  rw [hrow, columns_iff_span q t M₀ M hcol]

end UniqueGamesTheorem.Inverse.AffineWitness

end

section

/-!
# Agreement counting for a folded action

A function that changes by an injectively encoded group element under a group
action can agree with an invariant target on at most one point per orbit.  The
proof injects the product of the acting group and the agreement set into the
underlying finite space.  Freeness of the action is not an additional premise:
the folding law and injectivity of the encoding force the needed freeness.

Only elementary group and finite-cardinality infrastructure is used here.
-/

namespace UniqueGamesTheorem.Inverse

variable {H X Y : Type*} [AddGroup H] [AddGroup Y]

/-- Translates of distinct agreement witnesses are distinct.  The encoding need
not be given as a homomorphism: only its injectivity and the displayed folding
identity are needed for this conclusion. -/
theorem folded_action_injective
    (shift : H → X → X)
    (shift_zero : ∀ x, shift 0 x = x)
    (shift_add : ∀ h k x, shift (h + k) x = shift h (shift k x))
    (embed : H → Y) (embed_injective : Function.Injective embed)
    (F target : X → Y)
    (folded : ∀ h x, F (shift h x) = F x + embed h)
    (target_invariant : ∀ h x, target (shift h x) = target x) :
    Function.Injective
      (fun a : H × {x : X // F x = target x} => shift a.1 a.2.val) := by
  intro a b hab
  have htarget : target a.2.val = target b.2.val := by
    calc
      target a.2.val = target (shift a.1 a.2.val) :=
        (target_invariant a.1 a.2.val).symm
      _ = target (shift b.1 b.2.val) := congrArg target hab
      _ = target b.2.val := target_invariant b.1 b.2.val
  have hfold : F a.2.val + embed a.1 = F b.2.val + embed b.1 := by
    calc
      F a.2.val + embed a.1 = F (shift a.1 a.2.val) :=
        (folded a.1 a.2.val).symm
      _ = F (shift b.1 b.2.val) := congrArg F hab
      _ = F b.2.val + embed b.1 := folded b.1 b.2.val
  rw [a.2.property, b.2.property, htarget] at hfold
  have hh : a.1 = b.1 := embed_injective (add_left_cancel hfold)
  have hx : a.2.val = b.2.val := by
    have hshift : shift a.1 a.2.val = shift a.1 b.2.val := by
      simpa only [hh] using hab
    have hinverse := congrArg (shift (-a.1)) hshift
    simpa only [← shift_add, neg_add_cancel, shift_zero] using hinverse
  exact Prod.ext hh (Subtype.ext hx)

/-- The agreement set of a folded function with an invariant target occupies
at most the reciprocal of the size of the acting group, in denominator-free
finite-cardinality form. -/
theorem folded_action_card_mul_agreement_le
    [Fintype H] [Fintype X] [DecidableEq Y]
    (shift : H → X → X)
    (shift_zero : ∀ x, shift 0 x = x)
    (shift_add : ∀ h k x, shift (h + k) x = shift h (shift k x))
    (embed : H → Y) (embed_injective : Function.Injective embed)
    (F target : X → Y)
    (folded : ∀ h x, F (shift h x) = F x + embed h)
    (target_invariant : ∀ h x, target (shift h x) = target x) :
    Fintype.card H * Fintype.card {x : X // F x = target x} ≤
      Fintype.card X := by
  simpa only [Fintype.card_prod] using
    Fintype.card_le_of_injective
      (fun a : H × {x : X // F x = target x} => shift a.1 a.2.val)
      (folded_action_injective shift shift_zero shift_add embed embed_injective
        F target folded target_invariant)

end UniqueGamesTheorem.Inverse

end

section

/-!
# Finite indicator expectations as conditional cardinality ratios

These identities use the complete finite sample set in the denominator.  They
also cover the empty set, for which both the expectation and the ratio are zero.
The equivalence variant transfers both the event and the sample space, so no
conditioning factor is lost when changing representations of a slice.
-/

namespace UniqueGamesTheorem.Inverse

open scoped BigOperators

variable {X Y : Type*}

/-- Filtering a finite sample set counts the same objects as first restricting
to the sample set and then imposing the event predicate. -/
theorem card_finset_subtype_eq_filter_card (s : Finset X)
    (p : X → Prop) [DecidablePred p] :
    Nat.card {x : s // p x.val} = (s.filter p).card := by
  classical
  let e : {x : s // p x.val} ≃ ↥(s.filter p) :=
    { toFun := fun x =>
        ⟨x.val.val, Finset.mem_filter.mpr ⟨x.val.property, x.property⟩⟩
      invFun := fun x =>
        ⟨⟨x.val, (Finset.mem_filter.mp x.property).1⟩,
          (Finset.mem_filter.mp x.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (Nat.card_eq_finsetCard _)

/-- An indicator's expectation on a finite set is its agreement count divided
by the cardinality of that same finite set. -/
theorem finset_expect_indicator_eq_card_ratio (s : Finset X)
    (p : X → Prop) [DecidablePred p] :
    s.expect (fun x => if p x then (1 : ℝ) else 0) =
      (Nat.card {x : s // p x.val} : ℝ) / (Nat.card s : ℝ) := by
  rw [Finset.expect_eq_sum_div_card, Finset.sum_boole,
    card_finset_subtype_eq_filter_card, Nat.card_eq_finsetCard]

/-- A bijection preserving the event preserves its count. No choice of a
`Fintype` enumeration is involved in this identity. -/
theorem nat_card_subtype_equiv (e : X ≃ Y) (p : X → Prop) (q : Y → Prop)
    (h : ∀ x, p x ↔ q (e x)) :
    Nat.card {x : X // p x} = Nat.card {y : Y // q y} :=
  Nat.card_congr (e.subtypeEquiv h)

/-- Transfer the indicator expectation through an equivalence of the complete
finite sample space, including the denominator of the conditional law. -/
theorem finset_expect_indicator_eq_card_ratio_of_equiv (s : Finset X)
    (p : X → Prop) [DecidablePred p] (e : ↥s ≃ Y) (q : Y → Prop)
    (h : ∀ x : s, p x.val ↔ q (e x)) :
    s.expect (fun x => if p x then (1 : ℝ) else 0) =
      (Nat.card {y : Y // q y} : ℝ) / (Nat.card Y : ℝ) := by
  rw [finset_expect_indicator_eq_card_ratio,
    nat_card_subtype_equiv e (fun x => p x.val) q h, Nat.card_congr e]

end UniqueGamesTheorem.Inverse

end

section

/-!
# Size of a binary row kernel

An `r`-row linear constraint on `ℓ` binary coordinates leaves a kernel with at
least `2^(ℓ-r)` elements.  This does not require independent constraint rows.
The exponent uses natural subtraction, so the assertion also covers `r > ℓ`.
The argument is rank--nullity followed by the exact finite-field cardinality
formula; it does not use any inverse theorem or rank-level inequality.
-/

namespace UniqueGamesTheorem.Inverse

/-- Even dependent binary row constraints remove at most one dimension per
row. -/
theorem binary_kernel_finrank_lower {ℓ r : ℕ}
    (A : (Fin ℓ → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) :
    ℓ - r ≤ Module.finrank (ZMod 2) A.ker := by
  have hnull : Module.finrank (ZMod 2) A.range +
      Module.finrank (ZMod 2) A.ker = ℓ := by
    simpa only [Module.finrank_fin_fun] using A.finrank_range_add_finrank_ker
  have hrange : Module.finrank (ZMod 2) A.range ≤ r := by
    simpa only [Module.finrank_fin_fun] using A.range.finrank_le
  apply Nat.sub_le_iff_le_add.mpr
  calc
    ℓ = Module.finrank (ZMod 2) A.ker +
        Module.finrank (ZMod 2) A.range := hnull.symm.trans (Nat.add_comm _ _)
    _ ≤ Module.finrank (ZMod 2) A.ker + r :=
      Nat.add_le_add_left hrange _

/-- The cardinality of the binary row kernel is at least `2^(ℓ-r)`. -/
theorem binary_kernel_card_lower {ℓ r : ℕ}
    (A : (Fin ℓ → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) :
    2 ^ (ℓ - r) ≤ Nat.card A.ker := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  exact Nat.pow_le_pow_right (by decide) (binary_kernel_finrank_lower A)

end UniqueGamesTheorem.Inverse

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

/-- Return the first proposal accepted by the given test, or report exhaustion. -/
def firstAccepted {σ : Type*} (accept : σ → Bool) : List σ → Option σ
  | [] => none
  | proposal :: rest =>
      if accept proposal then some proposal else firstAccepted accept rest

/-- If the first proposal accepted by either sampler is accepted by both,
the two samplers return exactly that same proposal. -/
theorem first_union_common {σ : Type*} (left right : σ → Bool)
    (proposals : List σ) (proposal : σ)
    (hfirst : firstAccepted (fun s => left s || right s) proposals = some proposal)
    (hleft : left proposal = true) (hright : right proposal = true) :
    firstAccepted left proposals = some proposal ∧
      firstAccepted right proposals = some proposal := by
  induction proposals with
  | nil => simp [firstAccepted] at hfirst
  | cons head tail ih =>
      by_cases hl : left head = true
      · have heq : head = proposal := by
          simpa [firstAccepted, hl] using hfirst
        subst head
        simp [firstAccepted, hleft, hright]
      · by_cases hr : right head = true
        · have heq : head = proposal := by
            simpa [firstAccepted, hl, hr] using hfirst
          subst head
          exact False.elim (hl hleft)
        · have htail : firstAccepted (fun s => left s || right s) tail = some proposal := by
            simpa [firstAccepted, hl, hr] using hfirst
          simpa [firstAccepted, hl, hr] using ih htail

end UniqueGamesTheorem.Foundations.CorrelatedSampling

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_FiniteTrialsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Exact finite probability mass of a bounded rejection process.

Each trial independently draws from a finite mass function `w`. Its first
accepted proposal is represented by `some proposal`; exhaustion is `none`.
The recursive definition exposes the one-step probability transition. We prove
normalization, nonnegativity, the exact survival probability, and an exact
agreement-event formula with the finite-truncation error.
-/

namespace UniqueGamesTheorem.Foundations.CorrelatedSampling

noncomputable section

variable {σ : Type*} [Fintype σ]

def eventMass (w : σ → ℝ) (event : σ → Bool) : ℝ :=
  ∑ s, if event s then w s else 0

theorem eventMass_nonneg (w : σ → ℝ) (event : σ → Bool) (hw : ∀ s, 0 ≤ w s) :
    0 ≤ eventMass w event := by
  apply Finset.sum_nonneg
  intro s _
  split <;> simp_all

theorem eventMass_complement (w : σ → ℝ) (event : σ → Bool)
    (hw : ∑ s, w s = 1) :
    eventMass w event + eventMass w (fun s => !(event s)) = 1 := by
  unfold eventMass
  rw [← Finset.sum_add_distrib]
  calc
    ∑ s, ((if event s then w s else 0) + (if !event s then w s else 0)) = ∑ s, w s := by
      apply Finset.sum_congr rfl
      intro s _
      cases event s <;> simp
    _ = 1 := hw

def geometricMass (r : ℝ) : Nat → ℝ
  | 0 => 0
  | n + 1 => 1 + r * geometricMass r n

theorem geometricMass_identity (r : ℝ) (n : Nat) :
    (1 - r) * geometricMass r n = 1 - r ^ n := by
  induction n with
  | zero => simp [geometricMass]
  | succ n ih =>
      simp only [geometricMass, pow_succ]
      calc
        (1 - r) * (1 + r * geometricMass r n) =
            (1 - r) + r * ((1 - r) * geometricMass r n) := by ring
        _ = 1 - r ^ n * r := by rw [ih]; ring

/-- Probability transition for a finite first-acceptance process. A successful
first trial contributes its own mass; a rejected first trial continues with
one fewer trial. -/
def firstHitWeight (w : σ → ℝ) (accept : σ → Bool) : Nat → Option σ → ℝ
  | 0, none => 1
  | 0, some _ => 0
  | n + 1, none => eventMass w (fun s => !(accept s)) * firstHitWeight w accept n none
  | n + 1, some s =>
      (if accept s then w s else 0) +
        eventMass w (fun s => !(accept s)) * firstHitWeight w accept n (some s)

theorem firstHitWeight_some (w : σ → ℝ) (accept : σ → Bool) (n : Nat) (s : σ) :
    firstHitWeight w accept n (some s) =
      (if accept s then w s else 0) *
        geometricMass (eventMass w (fun s => !(accept s))) n := by
  induction n with
  | zero => simp [firstHitWeight, geometricMass]
  | succ n ih =>
      rw [firstHitWeight, geometricMass, ih]
      ring

/-- Probability that the first accepted proposal satisfies an additional test.
For two threshold samplers, take `accept = left || right` and `good = left && right`.
`first_union_common` gives deterministic agreement on this event. -/
def goodFirstMass (w : σ → ℝ) (accept good : σ → Bool) (n : Nat) : ℝ :=
  ∑ s, if good s then firstHitWeight w accept n (some s) else 0

theorem goodFirstMass_eq (w : σ → ℝ) (accept good : σ → Bool) (n : Nat) :
    goodFirstMass w accept good n =
      eventMass w (fun s => accept s && good s) *
        geometricMass (eventMass w (fun s => !(accept s))) n := by
  unfold goodFirstMass eventMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [firstHitWeight_some]
  cases ha : accept s <;> cases hg : good s <;> simp [ha, hg, eventMass]

/-- Exact finite geometric law: the first accepted proposal lies in the good
part with probability (good accepted mass / total accepted mass) times the
probability of seeing any accepted proposal within the trial bound. -/
theorem goodFirstMass_exact (w : σ → ℝ) (accept good : σ → Bool)
    (hw : ∑ s, w s = 1) (ha : eventMass w accept ≠ 0) (n : Nat) :
    goodFirstMass w accept good n =
      eventMass w (fun s => accept s && good s) / eventMass w accept *
        (1 - eventMass w (fun s => !(accept s)) ^ n) := by
  rw [goodFirstMass_eq]
  have hc := eventMass_complement w accept hw
  have hg := geometricMass_identity (eventMass w (fun s => !(accept s))) n
  have hgeom : eventMass w accept *
      geometricMass (eventMass w (fun s => !(accept s))) n =
      1 - eventMass w (fun s => !(accept s)) ^ n := by
    have heq : eventMass w accept = 1 - eventMass w (fun s => !(accept s)) := by linarith
    rw [heq, hg]
  rw [← hgeom]
  field_simp

theorem commonMass_le_acceptMass (w : σ → ℝ) (accept good : σ → Bool)
    (hw : ∀ s, 0 ≤ w s) :
    eventMass w (fun s => accept s && good s) ≤ eventMass w accept := by
  apply Finset.sum_le_sum
  intro s _
  cases ha : accept s <;> cases hg : good s <;> simp [ha, hg, hw s]

/-- A finite truncation loses at most its exhaustion probability in addition
to the conditional bad-first-proposal probability. All quantities are exact
finite sums; the rightmost term is the explicit geometric tail. -/
theorem goodFirstMass_lower_bound (w : σ → ℝ) (accept good : σ → Bool)
    (hw : ∀ s, 0 ≤ w s) (hw_sum : ∑ s, w s = 1)
    (ha : 0 < eventMass w accept) (n : Nat) :
    eventMass w (fun s => accept s && good s) / eventMass w accept -
        eventMass w (fun s => !(accept s)) ^ n ≤ goodFirstMass w accept good n := by
  rw [goodFirstMass_exact w accept good hw_sum (ne_of_gt ha) n]
  have hratio : eventMass w (fun s => accept s && good s) / eventMass w accept ≤ 1 := by
    apply (div_le_one ha).2
    exact commonMass_le_acceptMass w accept good hw
  have htail : 0 ≤ eventMass w (fun s => !(accept s)) ^ n :=
    pow_nonneg (eventMass_nonneg w (fun s => !(accept s)) hw) n
  nlinarith

end

end UniqueGamesTheorem.Foundations.CorrelatedSampling

end

section

/-! A finite exact replacement for uniform real thresholds. A list of real
thresholds subdivides [0,1]. Each resulting interval is an atom with weight its
length. Every inserted threshold has exactly its stated acceptance mass. -/

namespace UniqueGamesTheorem.Foundations.CorrelatedSampling

noncomputable section

structure ThresholdInterval where
  lo : ℝ
  hi : ℝ
  valid : lo ≤ hi

def splitPoint (I : ThresholdInterval) (t : ℝ) : ℝ := max I.lo (min t I.hi)

def splitLeft (I : ThresholdInterval) (t : ℝ) : ThresholdInterval :=
  ⟨I.lo, splitPoint I t, le_max_left _ _⟩

def splitRight (I : ThresholdInterval) (t : ℝ) : ThresholdInterval :=
  ⟨splitPoint I t, I.hi, max_le I.valid (min_le_right _ _)⟩

def cutAt (r : ℝ) (I : ThresholdInterval) : Prop := I.hi ≤ r ∨ r ≤ I.lo

def intervalCDF (r : ℝ) (I : ThresholdInterval) : ℝ := min r I.hi - min r I.lo

theorem split_cdf (I : ThresholdInterval) (t r : ℝ) :
    intervalCDF r (splitLeft I t) + intervalCDF r (splitRight I t) = intervalCDF r I := by
  unfold intervalCDF splitLeft splitRight
  ring

theorem accepted_interval_mass (I : ThresholdInterval) (r : ℝ) (hc : cutAt r I) :
    (if I.lo < r then I.hi - I.lo else 0) = intervalCDF r I := by
  by_cases hl : I.lo < r
  · have hu : I.hi ≤ r := hc.resolve_right (not_le_of_gt hl)
    simp [hl, intervalCDF, min_eq_right hu, min_eq_right (le_of_lt hl)]
  · have hr : r ≤ I.lo := le_of_not_gt hl
    simp [hl, intervalCDF, min_eq_left hr, min_eq_left (hr.trans I.valid)]

theorem splitLeft_cut (I : ThresholdInterval) (t : ℝ) : cutAt t (splitLeft I t) := by
  by_cases h : I.lo ≤ t
  · exact Or.inl (max_le h (min_le_left _ _))
  · exact Or.inr (le_of_lt (lt_of_not_ge h))

theorem splitRight_cut (I : ThresholdInterval) (t : ℝ) : cutAt t (splitRight I t) := by
  by_cases h : t ≤ I.hi
  · right
    change t ≤ max I.lo (min t I.hi)
    rw [min_eq_left h]
    exact le_max_right _ _
  · exact Or.inl (le_of_lt (lt_of_not_ge h))

theorem splitLeft_preserves_cut (I : ThresholdInterval) (t r : ℝ) (h : cutAt r I) :
    cutAt r (splitLeft I t) := by
  rcases h with h | h
  · exact Or.inl ((max_le I.valid (min_le_right _ _)).trans h)
  · exact Or.inr h

theorem splitRight_preserves_cut (I : ThresholdInterval) (t r : ℝ) (h : cutAt r I) :
    cutAt r (splitRight I t) := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans (le_max_left _ _))

def splitAll (t : ℝ) : List ThresholdInterval → List ThresholdInterval
  | [] => []
  | I :: rest => splitLeft I t :: splitRight I t :: splitAll t rest

def unitThresholdInterval : ThresholdInterval := ⟨0, 1, by norm_num⟩

def thresholdPartition : List ℝ → List ThresholdInterval
  | [] => [unitThresholdInterval]
  | t :: rest => splitAll t (thresholdPartition rest)

def sumOnIntervals (f : ThresholdInterval → ℝ) : List ThresholdInterval → ℝ
  | [] => 0
  | I :: rest => f I + sumOnIntervals f rest

theorem sumOn_splitAll (f : ThresholdInterval → ℝ) (t : ℝ)
    (hf : ∀ I, f (splitLeft I t) + f (splitRight I t) = f I)
    (intervals : List ThresholdInterval) :
    sumOnIntervals f (splitAll t intervals) = sumOnIntervals f intervals := by
  induction intervals with
  | nil => rfl
  | cons I rest ih =>
      simp only [splitAll, sumOnIntervals, ih]
      rw [← add_assoc, hf]

theorem partition_sum (f : ThresholdInterval → ℝ)
    (hf : ∀ t I, f (splitLeft I t) + f (splitRight I t) = f I)
    (thresholds : List ℝ) :
    sumOnIntervals f (thresholdPartition thresholds) = f unitThresholdInterval := by
  induction thresholds with
  | nil => simp [thresholdPartition, sumOnIntervals]
  | cons t rest ih =>
      rw [thresholdPartition, sumOn_splitAll f t (hf t), ih]

theorem partition_total_mass (thresholds : List ℝ) :
    sumOnIntervals (fun I => I.hi - I.lo) (thresholdPartition thresholds) = 1 := by
  have h := partition_sum (fun I => I.hi - I.lo)
    (fun t I => by simp only [splitLeft, splitRight]; ring) thresholds
  simpa [unitThresholdInterval] using h

theorem partition_cdf (thresholds : List ℝ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    sumOnIntervals (intervalCDF r) (thresholdPartition thresholds) = r := by
  have h := partition_sum (intervalCDF r) (fun t I => split_cdf I t r) thresholds
  simpa [intervalCDF, unitThresholdInterval, min_eq_left h1, min_eq_right h0] using h

theorem splitAll_new_cuts (intervals : List ThresholdInterval) (t : ℝ) :
    ∀ I ∈ splitAll t intervals, cutAt t I := by
  induction intervals with
  | nil => intro I h; simp [splitAll] at h
  | cons J rest ih =>
      intro I h
      rcases List.mem_cons.mp h with h | h
      · subst I; exact splitLeft_cut J t
      · rcases List.mem_cons.mp h with h | h
        · subst I; exact splitRight_cut J t
        · exact ih I h

theorem splitAll_preserves_cuts (intervals : List ThresholdInterval) (t r : ℝ) :
    (∀ I ∈ intervals, cutAt r I) → ∀ I ∈ splitAll t intervals, cutAt r I := by
  induction intervals with
  | nil => intro _ I h; simp [splitAll] at h
  | cons J rest ih =>
      intro hc I h
      have hJ : cutAt r J := hc J (by simp)
      have hrest : ∀ K ∈ rest, cutAt r K := fun K hK => hc K (by simp [hK])
      rcases List.mem_cons.mp h with h | h
      · subst I; exact splitLeft_preserves_cut J t r hJ
      · rcases List.mem_cons.mp h with h | h
        · subst I; exact splitRight_preserves_cut J t r hJ
        · exact ih hrest I h

theorem partition_cuts (thresholds : List ℝ) (r : ℝ) :
    r ∈ thresholds → ∀ I ∈ thresholdPartition thresholds, cutAt r I := by
  induction thresholds with
  | nil => intro hr; simp at hr
  | cons t rest ih =>
      intro hr
      rcases List.mem_cons.mp hr with h | h
      · subst r; exact splitAll_new_cuts (thresholdPartition rest) t
      · exact splitAll_preserves_cuts (thresholdPartition rest) t r (ih h)

theorem sumOnIntervals_congr (f g : ThresholdInterval → ℝ) (intervals : List ThresholdInterval) :
    (∀ I ∈ intervals, f I = g I) → sumOnIntervals f intervals = sumOnIntervals g intervals := by
  induction intervals with
  | nil => intro _; rfl
  | cons J rest ih =>
      intro h
      have hJ := h J (by simp)
      have hr : ∀ I ∈ rest, f I = g I := fun I hI => h I (by simp [hI])
      simp only [sumOnIntervals, hJ, ih hr]

theorem partition_acceptance_mass (thresholds : List ℝ) (r : ℝ)
    (hr : r ∈ thresholds) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    sumOnIntervals (fun I => if I.lo < r then I.hi - I.lo else 0)
      (thresholdPartition thresholds) = r := by
  calc
    _ = sumOnIntervals (intervalCDF r) (thresholdPartition thresholds) :=
      sumOnIntervals_congr _ _ _ (fun I hI =>
        accepted_interval_mass I r (partition_cuts thresholds r hr I hI))
    _ = r := partition_cdf thresholds r h0 h1

theorem sum_interval_get (f : ThresholdInterval → ℝ) (intervals : List ThresholdInterval) :
    (∑ i : Fin intervals.length, f intervals[i]) = sumOnIntervals f intervals := by
  induction intervals with
  | nil => simp [sumOnIntervals]
  | cons I rest ih =>
      simpa [Fin.sum_univ_succ, sumOnIntervals] using congrArg (fun x : ℝ => f I + x) ih

end

end UniqueGamesTheorem.Foundations.CorrelatedSampling

end

section

/-!
Connect the rejection sampler's executable list recursion to exact finite
probabilities. `traceAverage` is a finite nested sum over independent proposals;
it introduces no assumed probability law. The main theorem computes the actual
mass of each output of `firstAccepted` under those nested sums.
-/

namespace UniqueGamesTheorem.Foundations.CorrelatedSampling

noncomputable section

variable {σ : Type*} [Fintype σ]

/-- Expectation over a length-n list of independent proposals with mass `w`.
This is defined directly as a finite nested weighted sum. -/
def traceAverage (w : σ → ℝ) : Nat → (List σ → ℝ) → ℝ
  | 0, observable => observable []
  | n + 1, observable => ∑ s, w s * traceAverage w n (fun tail => observable (s :: tail))

theorem traceAverage_const (w : σ → ℝ) (hw : ∑ s, w s = 1) (n : Nat) (c : ℝ) :
    traceAverage w n (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih => simp [traceAverage, ih, ← Finset.sum_mul, hw]

theorem traceAverage_mono (w : σ → ℝ) (hw : ∀ s, 0 ≤ w s) (n : Nat)
    (f g : List σ → ℝ) (hfg : ∀ xs, f xs ≤ g xs) :
    traceAverage w n f ≤ traceAverage w n g := by
  induction n generalizing f g with
  | zero => exact hfg []
  | succ n ih =>
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left
        (ih (fun tail => f (s :: tail)) (fun tail => g (s :: tail))
          (fun tail => hfg (s :: tail))) (hw s)

theorem traceAverage_sum {ι : Type*} [Fintype ι] (w : σ → ℝ) (n : Nat)
    (f : ι → List σ → ℝ) :
    traceAverage w n (fun xs => ∑ i, f i xs) = ∑ i, traceAverage w n (f i) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      simp only [traceAverage]
      simp_rw [ih, Finset.mul_sum]
      exact Finset.sum_comm

variable [DecidableEq σ]

/-- The recursively constructed first-hit distribution is the actual law
of the finite shared-list rejection sampler. -/
theorem firstAccepted_law (w : σ → ℝ) (accept : σ → Bool)
    (hw : ∑ s, w s = 1) (n : Nat) (output : Option σ) :
    traceAverage w n (fun proposals =>
      if firstAccepted accept proposals = output then 1 else 0) =
      firstHitWeight w accept n output := by
  classical
  induction n generalizing output with
  | zero => cases output <;> simp [traceAverage, firstAccepted, firstHitWeight]
  | succ n ih =>
      have hstep : traceAverage w (n + 1) (fun proposals =>
          if firstAccepted accept proposals = output then 1 else 0) =
          ∑ s, w s * (if accept s then (if some s = output then 1 else 0)
            else firstHitWeight w accept n output) := by
        unfold traceAverage
        apply Finset.sum_congr rfl
        intro s _
        congr 1
        by_cases hs : accept s = true
        · simp [firstAccepted, hs, traceAverage_const w hw]
        · simpa [firstAccepted, hs] using ih output
      rw [hstep]
      cases output with
      | none =>
          simp only [Option.some_ne_none, ite_false, firstHitWeight]
          rw [eventMass, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro s _
          cases accept s <;> simp
      | some t =>
          simp only [Option.some.injEq, firstHitWeight]
          calc
            ∑ s, w s * (if accept s then (if s = t then 1 else 0)
                else firstHitWeight w accept n (some t)) =
              ∑ s, ((if s = t then (if accept s then w s else 0) else 0) +
                (if !(accept s) then w s else 0) * firstHitWeight w accept n (some t)) := by
                  apply Finset.sum_congr rfl
                  intro s _
                  by_cases he : s = t
                  · subst s
                    by_cases hs : accept t = true <;> simp [hs]
                  · by_cases hs : accept s = true <;> simp [hs, he]
            _ = (if accept t then w t else 0) +
                eventMass w (fun s => !(accept s)) * firstHitWeight w accept n (some t) := by
                  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
                  simp [eventMass]

/-- Indicator of the first accepted proposal passing a second test. -/
def goodFirstIndicator (accept good : σ → Bool) (proposals : List σ) : ℝ :=
  match firstAccepted accept proposals with
  | none => 0
  | some s => if good s then 1 else 0

theorem goodFirstIndicator_expansion (accept good : σ → Bool) (proposals : List σ) :
    goodFirstIndicator accept good proposals =
      ∑ s, if good s then (if firstAccepted accept proposals = some s then 1 else 0) else 0 := by
  classical
  cases h : firstAccepted accept proposals with
  | none => simp [goodFirstIndicator, h]
  | some t =>
      simp only [goodFirstIndicator, h, Option.some.injEq]
      calc
        (if good t then (1 : ℝ) else 0) =
            ∑ s, if t = s then (if good s then (1 : ℝ) else 0) else 0 := by simp
        _ = ∑ s, if good s then (if t = s then (1 : ℝ) else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro s _
          by_cases hg : good s = true <;> by_cases ht : t = s <;> simp [hg, ht]

/-- Exact good-event probability of the actual bounded sampler. -/
theorem goodFirstIndicator_law (w : σ → ℝ) (accept good : σ → Bool)
    (hw : ∑ s, w s = 1) (n : Nat) :
    traceAverage w n (goodFirstIndicator accept good) = goodFirstMass w accept good n := by
  classical
  change traceAverage w n (fun xs => goodFirstIndicator accept good xs) = _
  simp_rw [goodFirstIndicator_expansion]
  rw [traceAverage_sum]
  unfold goodFirstMass
  apply Finset.sum_congr rfl
  intro s _
  by_cases hg : good s = true
  · simpa [hg] using firstAccepted_law w accept hw n (some s)
  · simp [hg, traceAverage_const w hw]

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

def IsProbability (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

noncomputable def totalVariation (p q : α → ℝ) : ℝ :=
  (∑ a, |p a - q a|) / 2

end UniqueGamesTheorem.Foundations.Information

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_FinishBoundsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Scalar estimates for the construction. These lemmas
only perform the stated rounding/subdivision/repetition arithmetic; they do
not assume or assert an unproved repetition theorem or hardness result.
-/

namespace UniqueGamesTheorem.Explicit.FinishBounds

theorem subdivision_completeness (vH vB d τ : ℝ)
    (hH : 1 - d ≤ vH)
    (hround : |vB - (1 - (1 - vH) / 4)| ≤ τ / 4) :
    1 - (d + τ) / 4 ≤ vB := by
  have h := (abs_le.mp hround).1
  linarith

theorem subdivision_soundness (vH vB τ : ℝ)
    (hH : vH ≤ 99 / 100) (hτ : τ ≤ 1 / 200)
    (hround : |vB - (1 - (1 - vH) / 4)| ≤ τ / 4) :
    vB ≤ 1 - 1 / 800 := by
  have h := (abs_le.mp hround).2
  linarith

/-- The full completeness loss after the coordinatewise product labeling. -/
theorem final_completeness (vB vG d τ ε₀ ε : ℝ) (t : Nat) (ht : 0 < t)
    (hB : 1 - (d + τ) / 4 ≤ vB)
    (hG : 1 - (t : ℝ) * (1 - vB) ≤ vG)
    (hd : d ≤ ε₀ / t) (hτ : τ ≤ ε₀ / t)
    (hε₀ : 0 ≤ ε₀) (hε : ε₀ ≤ ε) :
    1 - ε ≤ vG := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hd' := (le_div_iff₀ ht').mp hd
  have hτ' := (le_div_iff₀ ht').mp hτ
  have hB' : (t : ℝ) * (1 - vB) ≤ t * ((d + τ) / 4) :=
    mul_le_mul_of_nonneg_left (by linarith) ht'.le
  nlinarith

end UniqueGamesTheorem.Explicit.FinishBounds

end

section

/-!
Finite occurrence presentations used by the rounding/subdivision construction.
An occurrence has its own identifier: its endpoints need not be distinct and
different occurrences may have the same endpoints. The bipartite target records
injectivity of the pair of endpoints, which is precisely the required simplicity.
No hardness or analytic premise enters these structures.
-/

namespace UniqueGamesTheorem.Explicit

structure OccurrenceGame (V E A : Type*) where
  source : E → V
  target : E → V
  permutation : E → Equiv.Perm A

structure BipartiteGame (L R E A : Type*) where
  left : E → L
  right : E → R
  permutation : E → Equiv.Perm A
  simple : Function.Injective (fun e => (left e, right e))

namespace BipartiteGame

def Satisfied {L R E A : Type*} (G : BipartiteGame L R E A)
    (leftLabeling : L → A) (rightLabeling : R → A) (e : E) : Prop :=
  rightLabeling (G.right e) = G.permutation e (leftLabeling (G.left e))

instance satisfiedDecidable {L R E A : Type*} [DecidableEq A]
    (G : BipartiteGame L R E A) (a : L → A) (b : R → A) (e : E) :
    Decidable (G.Satisfied a b e) := inferInstanceAs (Decidable (_ = _))

end BipartiteGame

end UniqueGamesTheorem.Explicit

end

section

/-!
The four-edge subdivision.
Every input occurrence has its own three interior vertices, even when
the original endpoints coincide or another occurrence has the same endpoints.
The left/right presentation inverts the permutation on the fourth edge.
-/

namespace UniqueGamesTheorem.Explicit

open scoped BigOperators

namespace OccurrenceGame

variable {V E A : Type*} [Fintype E] [DecidableEq A]

def satisfiedCount (g : OccurrenceGame V E A) (a : V → A) : Nat :=
  ∑ e, if g.permutation e (a (g.source e)) = a (g.target e) then 1 else 0

variable [Fintype V] [Fintype A]

noncomputable def maxSatisfied (g : OccurrenceGame V E A) : Nat := by
  classical
  exact Finset.univ.sup (satisfiedCount g)

noncomputable def value (g : OccurrenceGame V E A) : ℝ :=
  (maxSatisfied g : ℝ) / Fintype.card E

theorem satisfiedCount_le_maxSatisfied (g : OccurrenceGame V E A) (a : V → A) :
    satisfiedCount g a ≤ maxSatisfied g := by
  classical
  exact Finset.le_sup (f := satisfiedCount g) (Finset.mem_univ a)

theorem maxSatisfied_attained [Nonempty A] (g : OccurrenceGame V E A) :
    ∃ a, satisfiedCount g a = maxSatisfied g := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (satisfiedCount g)
  exact ⟨a, ha.symm⟩

end OccurrenceGame

namespace BipartiteGame

variable {L R E A : Type*} [Fintype E] [DecidableEq A]

def satisfiedCount (g : BipartiteGame L R E A) (a : L → A) (b : R → A) : Nat :=
  ∑ e, if g.permutation e (a (g.left e)) = b (g.right e) then 1 else 0

variable [Fintype L] [Fintype R] [Fintype A]

noncomputable def maxSatisfied (g : BipartiteGame L R E A) : Nat := by
  classical
  exact Finset.univ.sup (fun ab : (L → A) × (R → A) => satisfiedCount g ab.1 ab.2)

noncomputable def value (g : BipartiteGame L R E A) : ℝ :=
  (maxSatisfied g : ℝ) / Fintype.card E

theorem satisfiedCount_le_maxSatisfied (g : BipartiteGame L R E A)
    (a : L → A) (b : R → A) : satisfiedCount g a b ≤ maxSatisfied g := by
  classical
  exact Finset.le_sup (f := fun ab : (L → A) × (R → A) => satisfiedCount g ab.1 ab.2)
    (Finset.mem_univ (a, b))

theorem maxSatisfied_attained [Nonempty A] (g : BipartiteGame L R E A) :
    ∃ a b, satisfiedCount g a b = maxSatisfied g := by
  classical
  obtain ⟨⟨a, b⟩, _, hab⟩ := Finset.exists_mem_eq_sup Finset.univ
    Finset.univ_nonempty
    (fun ab : (L → A) × (R → A) => satisfiedCount g ab.1 ab.2)
  exact ⟨a, b, hab.symm⟩

end BipartiteGame

namespace Subdivision

variable {V E A : Type*}

/-- Original vertices and the middle vertices `q_e`. -/
abbrev Left (V E : Type*) := V ⊕ E

/-- `false` is `p_e`, and `true` is `r_e`. -/
abbrev Right (E : Type*) := E × Bool

abbrev Edge (E : Type*) := E × Fin 4

def left (g : OccurrenceGame V E A) (ei : Edge E) : Left V E :=
  if ei.2 = 0 then Sum.inl (g.source ei.1)
  else if ei.2 = 3 then Sum.inl (g.target ei.1)
  else Sum.inr ei.1

def right (ei : Edge E) : Right E := (ei.1, decide (2 ≤ ei.2.val))

def permutation (g : OccurrenceGame V E A) (ei : Edge E) : Equiv.Perm A :=
  if ei.2 = 3 then (g.permutation ei.1).symm else Equiv.refl A

/-- The private occurrence identifier prevents parallel edges after subdivision.
This also handles a loop, which becomes a genuine four-cycle. -/
theorem endpoints_injective (g : OccurrenceGame V E A) :
    Function.Injective (fun ei : Edge E => (left g ei, right ei)) := by
  rintro ⟨e, i⟩ ⟨f, j⟩ h
  have hef : e = f := congrArg (fun x => x.2.1) h
  subst f
  fin_cases i <;> fin_cases j <;> simp_all [left, right]

def game (g : OccurrenceGame V E A) :
    BipartiteGame (Left V E) (Right E) (Edge E) A where
  left := left g
  right := right
  permutation := permutation g
  simple := endpoints_injective g

/-- Restrict any output labeling to the original vertices. -/
def restrict (a : Left V E → A) : V → A := fun v => a (Sum.inl v)

def extendLeft (g : OccurrenceGame V E A) (a : V → A) : Left V E → A :=
  Sum.elim a (fun e => a (g.source e))

def extendRight (g : OccurrenceGame V E A) (a : V → A) : Right E → A :=
  fun eb => a (g.source eb.1)

@[simp] theorem restrict_extendLeft (g : OccurrenceGame V E A) (a : V → A) :
    restrict (extendLeft g a) = a := rfl

variable [DecidableEq A]

/-- The strongest possible path score for fixed endpoint labels is exactly
three plus the old satisfaction indicator. -/
theorem local_count_le (ρ : Equiv.Perm A) (u p q r v : A) :
    (if u = p then 1 else 0) + (if q = p then 1 else 0) +
      (if q = r then 1 else 0) + (if ρ.symm v = r then 1 else 0) ≤
        3 + (if ρ u = v then 1 else 0 : Nat) := by
  by_cases h₀ : u = p <;> by_cases h₁ : q = p <;>
    by_cases h₂ : q = r <;> by_cases h₃ : ρ.symm v = r <;>
    by_cases h : ρ u = v <;> simp_all [Equiv.symm_apply_eq]

theorem local_count_extend (ρ : Equiv.Perm A) (u v : A) :
    (if u = u then 1 else 0) + (if u = u then 1 else 0) +
      (if u = u then 1 else 0) + (if ρ.symm v = u then 1 else 0) =
        3 + (if ρ u = v then 1 else 0 : Nat) := by
  by_cases h : ρ u = v
  · have h' : ρ.symm v = u := by rw [← h, ρ.symm_apply_apply]
    simp [h, h']
  · have h' : ρ.symm v ≠ u := by
      intro he
      apply h
      rw [← he, ρ.apply_symm_apply]
    simp [h, h']

theorem count_on_occurrence_le (g : OccurrenceGame V E A)
    (a : Left V E → A) (b : Right E → A) (e : E) :
    (∑ i : Fin 4, if (game g).permutation (e, i) (a ((game g).left (e, i))) =
        b ((game g).right (e, i)) then 1 else 0) ≤
      3 + (if g.permutation e (restrict a (g.source e)) =
        restrict a (g.target e) then 1 else 0 : Nat) := by
  rw [Fin.sum_univ_four]
  exact local_count_le (g.permutation e)
      (a (Sum.inl (g.source e))) (b (e, false)) (a (Sum.inr e))
      (b (e, true)) (a (Sum.inl (g.target e)))

theorem count_on_occurrence_extend (g : OccurrenceGame V E A) (a : V → A) (e : E) :
    (∑ i : Fin 4, if (game g).permutation (e, i)
      (extendLeft g a ((game g).left (e, i))) =
        extendRight g a ((game g).right (e, i)) then 1 else 0) =
      3 + (if g.permutation e (a (g.source e)) = a (g.target e) then 1 else 0 : Nat) := by
  rw [Fin.sum_univ_four]
  simpa [game, permutation, left, right, extendLeft, extendRight] using
    local_count_extend (g.permutation e) (a (g.source e)) (a (g.target e))

variable [Fintype E]

theorem satisfiedCount_le (g : OccurrenceGame V E A)
    (a : Left V E → A) (b : Right E → A) :
    (game g).satisfiedCount a b ≤
      3 * Fintype.card E + g.satisfiedCount (restrict a) := by
  unfold BipartiteGame.satisfiedCount OccurrenceGame.satisfiedCount
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ e, (3 + (if g.permutation e (restrict a (g.source e)) =
        restrict a (g.target e) then 1 else 0 : Nat)) :=
      Finset.sum_le_sum (fun e _ => count_on_occurrence_le g a b e)
    _ = _ := by simp [Finset.sum_add_distrib, Nat.mul_comm]

/-- Fresh interiors can be assigned independently, so the upper bound is attained. -/
theorem satisfiedCount_extend (g : OccurrenceGame V E A) (a : V → A) :
    (game g).satisfiedCount (extendLeft g a) (extendRight g a) =
      3 * Fintype.card E + g.satisfiedCount a := by
  unfold BipartiteGame.satisfiedCount OccurrenceGame.satisfiedCount
  rw [Fintype.sum_prod_type]
  simp_rw [count_on_occurrence_extend]
  simp [Finset.sum_add_distrib, Nat.mul_comm]

@[simp] theorem edge_count : Fintype.card (Edge E) = 4 * Fintype.card E := by
  simp [Edge, Nat.mul_comm]

@[simp] theorem left_count [Fintype V] :
    Fintype.card (Left V E) = Fintype.card V + Fintype.card E := by
  simp [Left]

@[simp] theorem right_count : Fintype.card (Right E) = 2 * Fintype.card E := by
  simp [Right, Nat.mul_comm]

variable [Fintype V] [Fintype A] [Nonempty A]

theorem maxSatisfied_eq (g : OccurrenceGame V E A) :
    (game g).maxSatisfied = 3 * Fintype.card E + g.maxSatisfied := by
  classical
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro ab _
    exact (satisfiedCount_le g ab.1 ab.2).trans
      (Nat.add_le_add_left (g.satisfiedCount_le_maxSatisfied (restrict ab.1)) _)
  · obtain ⟨a, ha⟩ := g.maxSatisfied_attained
    rw [← ha, ← satisfiedCount_extend]
    exact BipartiteGame.satisfiedCount_le_maxSatisfied _ _ _

theorem value_eq [Nonempty E] (g : OccurrenceGame V E A) :
    (game g).value = 1 - (1 - g.value) / 4 := by
  have hE : (Fintype.card E : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [BipartiteGame.value, maxSatisfied_eq, edge_count, OccurrenceGame.value]
  push_cast
  field_simp [hE]
  ring

end Subdivision

end UniqueGamesTheorem.Explicit

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_RowErasureLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.RowErasure

open scoped BigOperators

noncomputable section

def indicator (p : Prop) : ℝ := by
  classical
  exact if p then 1 else 0

@[simp] theorem indicator_true : indicator True = 1 := by simp [indicator]
@[simp] theorem indicator_false : indicator False = 0 := by simp [indicator]

def uniformMass {X : Type*} [Fintype X] (p : X → Prop) : ℝ :=
  Finset.univ.expect fun x => indicator (p x)

/-- Sample a uniform matrix, then an independent uniform row map. -/
def adviceMass {A X : Type*} [Fintype A] [Fintype X]
    (good : A → X → Prop) : ℝ :=
  Finset.univ.expect fun x => uniformMass fun a => good a x

end
end UniqueGamesTheorem.Inverse.RowErasure

end

section

/-!
Every nonempty affine row/column slice is an affine copy of the full space of
linear maps from the column quotient into the row kernel. This gives exact
uniform-law transport and preserves the affine evaluation offset.
-/

namespace UniqueGamesTheorem.Inverse.RowErasureSliceQuotient

noncomputable section

variable {R E K L : Type*} [Field R]
  [AddCommGroup E] [AddCommGroup K] [AddCommGroup L]
  [Module R E] [Module R K] [Module R L]

/-- The linear part of the affine parametrization. -/
def direction (A : K →ₗ[R] L) (Q : Submodule R E)
    (N : (E ⧸ Q) →ₗ[R] A.ker) : E →ₗ[R] K :=
  A.ker.subtype.comp (N.comp Q.mkQ)

@[simp] theorem direction_apply (A : K →ₗ[R] L) (Q : Submodule R E)
    (N : (E ⧸ Q) →ₗ[R] A.ker) (x : E) :
    direction A Q N x = (N (Q.mkQ x) : K) := rfl

/-- Quotient descent of a linear map which vanishes on the column span and
takes values in the common row kernel. -/
theorem exists_direction_of_row_and_column (A : K →ₗ[R] L)
    (Q : Submodule R E) (B : E →ₗ[R] K)
    (hQ : Q ≤ B.ker) (hA : LinearMap.range B ≤ A.ker) :
    ∃ N : (E ⧸ Q) →ₗ[R] A.ker, direction A Q N = B := by
  let B' : E →ₗ[R] A.ker := B.codRestrict A.ker
    (fun x => hA ⟨x, rfl⟩)
  have hQ' : Q ≤ B'.ker := by
    intro q hq
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change B q = 0
    exact hQ hq
  refine ⟨Q.liftQ B' hQ', ?_⟩
  ext x
  rfl

theorem direction_injective (A : K →ₗ[R] L) (Q : Submodule R E) :
    Function.Injective (direction A Q) := by
  intro N P h
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := Q.mkQ_surjective x
  apply Subtype.ext
  exact congrArg (fun f : E →ₗ[R] K => f v) h

/-- The concrete affine slice around any one point satisfying its equations. -/
def AffineSlice (A : K →ₗ[R] L) (Q : Submodule R E) (M₀ : E →ₗ[R] K) :=
  {M : E →ₗ[R] K // A.comp M = A.comp M₀ ∧ ∀ q ∈ Q, M q = M₀ q}

def ofQuotient (A : K →ₗ[R] L) (Q : Submodule R E) (M₀ : E →ₗ[R] K)
    (N : (E ⧸ Q) →ₗ[R] A.ker) : AffineSlice A Q M₀ := by
  refine ⟨M₀ + direction A Q N, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    change A (M₀ x + (N (Q.mkQ x) : K)) = A (M₀ x)
    rw [map_add, show A (N (Q.mkQ x) : K) = 0 from (N (Q.mkQ x)).property,
      add_zero]
  · intro q hq
    have hz : Q.mkQ q = 0 := (Submodule.Quotient.mk_eq_zero Q).mpr hq
    simp [direction, hz]

@[simp] theorem ofQuotient_val (A : K →ₗ[R] L) (Q : Submodule R E)
    (M₀ : E →ₗ[R] K) (N : (E ⧸ Q) →ₗ[R] A.ker) :
    (ofQuotient A Q M₀ N).val = M₀ + direction A Q N := rfl

theorem ofQuotient_bijective (A : K →ₗ[R] L) (Q : Submodule R E)
    (M₀ : E →ₗ[R] K) : Function.Bijective (ofQuotient A Q M₀) := by
  constructor
  · intro N P h
    apply direction_injective A Q
    exact add_left_cancel (congrArg Subtype.val h)
  · intro M
    have hQ : Q ≤ (M.val - M₀).ker := by
      intro q hq
      change M.val q - M₀ q = 0
      exact sub_eq_zero.mpr (M.property.2 q hq)
    have hA : LinearMap.range (M.val - M₀) ≤ A.ker := by
      rintro y ⟨x, rfl⟩
      change A (M.val x - M₀ x) = 0
      rw [map_sub]
      apply sub_eq_zero.mpr
      exact congrArg (fun f : E →ₗ[R] L => f x) M.property.1
    obtain ⟨N, hN⟩ := exists_direction_of_row_and_column A Q (M.val - M₀) hQ hA
    refine ⟨N, ?_⟩
    apply Subtype.ext
    rw [ofQuotient_val, hN]
    simpa only [← add_sub_assoc] using add_sub_cancel_left M₀ M.val

/-- Uniform free quotient maps parametrize exactly the original affine slice. -/
def equiv (A : K →ₗ[R] L) (Q : Submodule R E) (M₀ : E →ₗ[R] K) :
    ((E ⧸ Q) →ₗ[R] A.ker) ≃ AffineSlice A Q M₀ :=
  Equiv.ofBijective (ofQuotient A Q M₀) (ofQuotient_bijective A Q M₀)

@[simp] theorem equiv_apply (A : K →ₗ[R] L) (Q : Submodule R E)
    (M₀ : E →ₗ[R] K) (N : (E ⧸ Q) →ₗ[R] A.ker) :
    equiv A Q M₀ N = ofQuotient A Q M₀ N := rfl

end
end UniqueGamesTheorem.Inverse.RowErasureSliceQuotient

end

section

namespace UniqueGamesTheorem.Inverse.RowErasure

open scoped BigOperators

noncomputable section

variable {X Y A S D : Type*}

/-- Each description includes its row map, row value, column equations and
affine target. `points_row` is the necessary relationship to actual row advice. -/
structure SliceFamily (X Y A S D : Type*) where
  advice : A → X → S
  rowMap : D → A
  rowValue : D → S
  points : D → Finset X
  target : D → X → Y
  points_row : ∀ d x, x ∈ points d → advice (rowMap d) x = rowValue d

def SliceFamily.agreement (F : SliceFamily X Y A S D) (f : X → Y) (d : D) : ℝ :=
  (F.points d).expect fun x => indicator (f x = F.target d x)

def SliceFamily.GoodAdvice (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) : Prop :=
  ∃ d, F.rowMap d = a ∧ F.rowValue d = s ∧ (F.points d).Nonempty ∧
    α / 2 ≤ F.agreement f d

def SliceFamily.goodAt (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X) : Prop :=
  F.GoodAdvice f α a (F.advice a x)

end
end UniqueGamesTheorem.Inverse.RowErasure

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_AffineWitnessNormalizationLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The finite orbit count completing the first-bit witness normalization.
The assumption in `normalize_of_good_count` is precisely that agreement is
strictly greater than the reciprocal of the row-kernel cardinality, expressed
without division. It is a quantitative goodness hypothesis, not an inverse
theorem or a nonlinear rank premise.
-/

namespace UniqueGamesTheorem.Inverse.AffineWitness

variable {D C R : Type*}
  [AddCommGroup D] [Module F2 D]
  [AddCommGroup C] [Module F2 C]
  [AddCommGroup R] [Module F2 R]

/-- The actual simultaneous row/column slice, including its affine offsets. -/
abbrev Slice (A : C →ₗ[F2] R) (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C) :=
  {M : D →ₗ[F2] C // InSlice A Z M₀ M}

def sliceShift (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C)
    (heZ : ∀ w ∈ Z, e w = 0) (h : A.ker) (M : Slice A Z M₀) :
    Slice A Z M₀ :=
  ⟨shift e h M, shift_preserves_slice e A Z M₀ M heZ h M.property⟩

theorem sliceShift_zero (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C)
    (heZ : ∀ w ∈ Z, e w = 0) (M : Slice A Z M₀) :
    sliceShift e A Z M₀ heZ 0 M = M := by
  apply Subtype.ext
  exact shift_zero e M.val

theorem sliceShift_add (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C)
    (heZ : ∀ w ∈ Z, e w = 0) (h k : A.ker) (M : Slice A Z M₀) :
    sliceShift e A Z M₀ heZ (h + k) M =
      sliceShift e A Z M₀ heZ h (sliceShift e A Z M₀ heZ k M) := by
  apply Subtype.ext
  exact shift_add e (h : C) (k : C) M.val

/-- If the affine coset misses first bit one, folding limits agreement to one
point per row-kernel orbit. No rank-level inequality is used. -/
theorem agreement_count_le [Finite D] [Finite C]
    (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C) (z : D) (u : C)
    (F : (D →ₗ[F2] C) → C)
    (hfold : ∀ (h : A.ker) M, F (shift e h M) = F M + h)
    (hno : ¬ ∃ w ∈ Z, e (z + w) = 1) :
    Nat.card A.ker * Nat.card {M : Slice A Z M₀ // F M = M.val z + u} ≤
      Nat.card (Slice A Z M₀) := by
  classical
  let : Fintype D := Fintype.ofFinite D
  let : Fintype C := Fintype.ofFinite C
  let : Fintype (D →ₗ[F2] C) := Fintype.ofInjective DFunLike.coe DFunLike.coe_injective
  obtain ⟨hz, heZ⟩ := no_affine_representative e Z z hno
  have hcount := folded_action_card_mul_agreement_le
    (sliceShift e A Z M₀ heZ)
    (sliceShift_zero e A Z M₀ heZ)
    (sliceShift_add e A Z M₀ heZ)
    (fun h : A.ker => (h : C)) Subtype.val_injective
    (fun M : Slice A Z M₀ => F M)
    (fun M : Slice A Z M₀ => M.val z + u)
    (fun h M => hfold h M)
    (fun h M => shift_preserves_target e z hz u h M)
  simpa only [Nat.card_eq_fintype_card] using hcount

/-- A good affine witness has a first-bit-one representative with an adjusted
intercept, agreeing with the original target on every matrix of its slice. -/
theorem normalize_of_good_count [Finite D] [Finite C]
    (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C) (z : D) (u : C)
    (F : (D →ₗ[F2] C) → C)
    (hfold : ∀ (h : A.ker) M, F (shift e h M) = F M + h)
    (hgood : Nat.card (Slice A Z M₀) <
      Nat.card A.ker * Nat.card {M : Slice A Z M₀ // F M = M.val z + u}) :
    ∃ z' : D, ∃ u' : C, e z' = 1 ∧
      ∀ M, InSlice A Z M₀ M → M z' + u' = M z + u := by
  apply normalize e A Z M₀ z u
  by_contra hno
  exact (not_lt_of_ge (agreement_count_le e A Z M₀ z u F hfold hno)) hgood

end UniqueGamesTheorem.Inverse.AffineWitness

end

section

/-! The probability form of first-bit witness normalization. -/

namespace UniqueGamesTheorem.Inverse.AffineWitness

variable {D C R : Type*}
  [AddCommGroup D] [Module F2 D]
  [AddCommGroup C] [Module F2 C]
  [AddCommGroup R] [Module F2 R]

/-- An agreement lower bound above the inverse row-kernel size produces a
first-bit-one representative while preserving the entire affine target. -/
theorem normalize_of_density [Finite D] [Finite C]
    (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C) (z : D) (u : C)
    (F : (D →ₗ[F2] C) → C)
    (hfold : ∀ (h : A.ker) M, F (shift e h M) = F M + h)
    (η : ℝ)
    (hgood : η ≤
      (Nat.card {M : Slice A Z M₀ // F M = M.val z + u} : ℝ) /
        (Nat.card (Slice A Z M₀) : ℝ))
    (hsize : 1 < η * (Nat.card A.ker : ℝ)) :
    ∃ z' : D, ∃ u' : C, e z' = 1 ∧
      ∀ M, InSlice A Z M₀ M → M z' + u' = M z + u := by
  classical
  let : Fintype D := Fintype.ofFinite D
  let : Fintype C := Fintype.ofFinite C
  let : Fintype (D →ₗ[F2] C) := Fintype.ofInjective DFunLike.coe DFunLike.coe_injective
  let : Nonempty (Slice A Z M₀) := ⟨⟨M₀, rfl, fun _ _ => rfl⟩⟩
  have hpos : (0 : ℝ) < (Nat.card (Slice A Z M₀) : ℝ) := by
    exact_mod_cast Nat.card_pos (α := Slice A Z M₀)
  have hmass := (le_div_iff₀ hpos).mp hgood
  have hmul := mul_le_mul_of_nonneg_right hmass
    (Nat.cast_nonneg (α := ℝ) (Nat.card A.ker))
  have hstrict := mul_lt_mul_of_pos_right hsize hpos
  apply normalize_of_good_count e A Z M₀ z u F hfold
  have hreal : (Nat.card (Slice A Z M₀) : ℝ) <
      (Nat.card A.ker : ℝ) *
        (Nat.card {M : Slice A Z M₀ // F M = M.val z + u} : ℝ) := by
    nlinarith only [hmul, hstrict]
  exact_mod_cast hreal

end UniqueGamesTheorem.Inverse.AffineWitness

end

section

namespace UniqueGamesTheorem.Inverse.AffineWitness

theorem first_bit_witness {m ℓ r : ℕ}
    (e : (Fin m → F2) →ₗ[F2] F2)
    (A : (Fin ℓ → F2) →ₗ[F2] (Fin r → F2))
    (Z : Submodule F2 (Fin m → F2))
    (M₀ : (Fin m → F2) →ₗ[F2] (Fin ℓ → F2))
    (z : Fin m → F2) (u : Fin ℓ → F2)
    (F : ((Fin m → F2) →ₗ[F2] (Fin ℓ → F2)) → (Fin ℓ → F2))
    (hfold : ∀ (h : A.ker) M, F (shift e h M) = F M + h)
    (α : ℝ) (hα : 0 < α)
    (hgood : α / 2 ≤
      (Nat.card {M : Slice A Z M₀ // F M = M.val z + u} : ℝ) /
        (Nat.card (Slice A Z M₀) : ℝ))
    (hsmall : 1 / (2 : ℝ) ^ (ℓ - r) < α / 8) :
    ∃ z' : Fin m → F2, ∃ u' : Fin ℓ → F2, e z' = 1 ∧
      ∀ M, InSlice A Z M₀ M → M z' + u' = M z + u := by
  have hpow : (0 : ℝ) < 2 ^ (ℓ - r) := pow_pos (by norm_num) _
  have hsep := (div_lt_iff₀ hpow).mp hsmall
  have hk : (2 : ℝ) ^ (ℓ - r) ≤ (Nat.card A.ker : ℝ) := by
    exact_mod_cast binary_kernel_card_lower A
  have hscale := mul_le_mul_of_nonneg_left hk hα.le
  have hsize : 1 < (α / 2) * (Nat.card A.ker : ℝ) := by
    nlinarith only [hsep, hscale]
  exact normalize_of_density e A Z M₀ z u F hfold (α / 2) hgood hsize

end UniqueGamesTheorem.Inverse.AffineWitness

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSFoundationLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.KMS

noncomputable section
open scoped BigOperators Classical

abbrev F2 := ZMod 2
abbrev Ambient (n : ℕ) := Fin n → F2

/-- Actual `ell`-dimensional subspaces of the ambient binary vector space. -/
def Vertex (n ell : ℕ) :=
  {L : Submodule F2 (Ambient n) // Module.finrank F2 L = ell}

/-- A neighbor is distinct and meets the vertex in a hyperplane. The explicit
distinctness also makes the definition harmless at dimension zero. -/
def Adjacent {n ell : ℕ} (L M : Vertex n ell) : Prop :=
  L ≠ M ∧ Module.finrank F2 ↥(L.val ⊓ M.val : Submodule F2 (Ambient n)) + 1 = ell

end
end UniqueGamesTheorem.Inverse.KMS

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_MatrixChartLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.MatrixChart

variable {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

/-- The first coordinate identifies the graph with its domain. -/
def graphEquiv (T : X →ₗ[K] Y) : X ≃ₗ[K] T.graph where
  toFun x := ⟨(x, T x), rfl⟩
  invFun x := x.val.1
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    exact Prod.ext rfl x.property.symm
  map_add' _ _ := by
    apply Subtype.ext
    exact Prod.ext rfl (map_add T _ _)
  map_smul' _ _ := by
    apply Subtype.ext
    exact Prod.ext rfl (map_smul T _ _)

theorem graph_injective : Function.Injective (LinearMap.graph (R := K) (M := X) (M₂ := Y)) := by
  intro T U h
  apply LinearMap.ext
  intro x
  have hx : (x, T x) ∈ U.graph := h ▸ (show (x, T x) ∈ T.graph from rfl)
  exact hx

/-- Common graph vectors correspond exactly to the kernel of the difference. -/
def intersectionEquiv (T U : X →ₗ[K] Y) :
    LinearMap.ker (T - U) ≃ₗ[K] (T.graph ⊓ U.graph : Submodule K (X × Y)) where
  toFun x := ⟨(x.val, T x.val), by
    refine ⟨rfl, ?_⟩
    have hx : T x.val - U x.val = 0 := x.property
    exact sub_eq_zero.mp hx⟩
  invFun x := ⟨x.val.1, by
    change T x.val.1 - U x.val.1 = 0
    exact sub_eq_zero.mpr (x.property.1.symm.trans x.property.2)⟩
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    exact Prod.ext rfl x.property.1.symm
  map_add' _ _ := by
    apply Subtype.ext
    exact Prod.ext rfl (map_add T _ _)
  map_smul' _ _ := by
    apply Subtype.ext
    exact Prod.ext rfl (map_smul T _ _)

theorem finrank_graph [FiniteDimensional K X] (T : X →ₗ[K] Y) :
    Module.finrank K T.graph = Module.finrank K X :=
  (graphEquiv T).finrank_eq.symm

/-- Rank-nullity in the graph chart, without truncated natural subtraction. -/
theorem finrank_intersection_add_rank [FiniteDimensional K X] (T U : X →ₗ[K] Y) :
    Module.finrank K (T.graph ⊓ U.graph : Submodule K (X × Y)) +
      Module.finrank K (LinearMap.range (T - U)) = Module.finrank K X := by
  rw [← (intersectionEquiv T U).finrank_eq, Nat.add_comm]
  exact LinearMap.finrank_range_add_finrank_ker (T - U)

/-- Grassmann adjacency within the chart is exactly rank-one difference. -/
theorem adjacent_iff_rank_one [FiniteDimensional K X] (T U : X →ₗ[K] Y) :
    Module.finrank K (T.graph ⊓ U.graph : Submodule K (X × Y)) + 1 =
        Module.finrank K X ↔
      Module.finrank K (LinearMap.range (T - U)) = 1 := by
  have h := finrank_intersection_add_rank T U
  omega

/-- A nonzero rank-one perturbation gives an adjacent graph vertex. -/
theorem adjacent_rank_one_step [FiniteDimensional K X]
    (T : X →ₗ[K] Y) (a : X →ₗ[K] K) (l : Y) (ha : a ≠ 0) (hl : l ≠ 0) :
    Module.finrank K (T.graph ⊓ (T + a.smulRight l).graph :
      Submodule K (X × Y)) + 1 = Module.finrank K X := by
  apply (adjacent_iff_rank_one T (T + a.smulRight l)).mpr
  have heq : T - (T + a.smulRight l) = (-a).smulRight l := by
    apply LinearMap.ext
    intro x
    simp
  rw [heq, LinearMap.range_smulRight_apply (neg_ne_zero.mpr ha)]
  exact finrank_span_singleton hl

end UniqueGamesTheorem.Inverse.MatrixChart

end

section

/-! Concrete matrix coordinates for the graph chart. In particular the upper
interval equations become `M q = t`, while the lower equations become `dᵀ M = sᵀ`.
The right-hand sides are retained; none of these slices is required to be linear.
-/

namespace UniqueGamesTheorem.Inverse.MatrixChart

open Matrix

variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]

abbrev matrixGraph (M : Matrix ι κ K) : Submodule K ((ι → K) × (κ → K)) :=
  M.vecMulLinear.graph

omit [Fintype κ] in
@[simp] theorem mem_matrixGraph (M : Matrix ι κ K) (x : ι → K) (y : κ → K) :
    (x, y) ∈ matrixGraph M ↔ y = M.transpose *ᵥ x := by
  rw [Matrix.mulVec_transpose]
  rfl

omit [Fintype κ] in
theorem matrixGraph_injective : Function.Injective (matrixGraph (K := K) (ι := ι) (κ := κ)) := by
  classical
  intro M N h
  have hh : M.vecMulLinear = N.vecMulLinear := graph_injective h
  exact (LinearMap.toMatrixRight' (R := K)).symm.injective hh

/-- A coordinate vector as a linear functional, for the standard dot pairing. -/
abbrev dotFunctional (x : ι → K) : (ι → K) →ₗ[K] K := dotProductBilin K K x

theorem dotFunctional_injective : Function.Injective (dotFunctional (K := K) (ι := ι)) := by
  intro x y h
  apply dotProduct_eq x y
  intro z
  exact congrArg (fun f : (ι → K) →ₗ[K] K => f z) h

omit [Fintype κ] in
/-- The graph always has the row dimension, including degenerate zero dimensions. -/
theorem finrank_matrixGraph (M : Matrix ι κ K) :
    Module.finrank K (matrixGraph M) = Fintype.card ι := by
  rw [finrank_graph]
  simp

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

abbrev GrassmannNeighbors (L : Submodule K E) :=
  {W : Submodule K E // finrank K W = finrank K L ∧
    finrank K (L ⊓ W : Submodule K E) + 1 = finrank K L}

end UniqueGamesTheorem.Inverse.MatrixChart

end

section

/-!
The local neighbor law for the ordered-basis lift used in KMS Lemma 2.7.
The map is an arbitrary injective linear map, not a matrix graph chart.
An update in a direction outside its image stays injective, and its image
intersects the original image in exactly the transported functional kernel.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

open Module

variable {K E F : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

/-- The actual rank-one update of an ordered basis map. -/
def rankOneUpdate (X : E →ₗ[K] F) (a : E →ₗ[K] K) (y : F) : E →ₗ[K] F :=
  X + a.smulRight y

@[simp] theorem rankOneUpdate_apply (X : E →ₗ[K] F) (a : E →ₗ[K] K)
    (y : F) (x : E) : rankOneUpdate X a y x = X x + a x • y := rfl

/-- An outside direction returns to the original image exactly when its
coefficient vanishes. This does not require injectivity of `X`. -/
theorem rankOneUpdate_mem_range_iff (X : E →ₗ[K] F) (a : E →ₗ[K] K)
    {y : F} (hy : y ∉ LinearMap.range X) (x : E) :
    rankOneUpdate X a y x ∈ LinearMap.range X ↔ a x = 0 := by
  constructor
  · intro h
    have hs : a x • y ∈ LinearMap.range X := by
      have hh := (LinearMap.range X).sub_mem h (LinearMap.mem_range_self X x)
      simpa only [rankOneUpdate_apply, add_sub_cancel_left] using hh
    by_contra ha
    exact hy (((LinearMap.range X).smul_mem_iff ha).mp hs)
  · intro ha
    simpa only [rankOneUpdate_apply, ha, zero_smul, add_zero] using
      LinearMap.mem_range_self X x

/-- Rank-one perturbation in an outside direction preserves independence. -/
theorem injective_rankOneUpdate (X : E →ₗ[K] F) (hX : Function.Injective X)
    (a : E →ₗ[K] K) {y : F} (hy : y ∉ LinearMap.range X) :
    Function.Injective (rankOneUpdate X a y) := by
  apply (injective_iff_map_eq_zero (rankOneUpdate X a y)).mpr
  intro x hx
  have ha : a x = 0 := (rankOneUpdate_mem_range_iff X a hy x).mp
    (by rw [hx]; exact (LinearMap.range X).zero_mem)
  have hxx : X x = 0 := by simpa only [rankOneUpdate_apply, ha, zero_smul,
    add_zero] using hx
  exact hX (by simpa only [map_zero] using hxx)

/-- Exact intersection, retaining the functional rather than only its rank. -/
theorem range_inf_rankOneUpdate (X : E →ₗ[K] F) (a : E →ₗ[K] K)
    {y : F} (hy : y ∉ LinearMap.range X) :
    LinearMap.range X ⊓ LinearMap.range (rankOneUpdate X a y) =
      (LinearMap.ker a).map X := by
  ext z
  constructor
  · rintro ⟨hz, x, hx⟩
    have ha : a x = 0 := (rankOneUpdate_mem_range_iff X a hy x).mp
      (by rw [hx]; exact hz)
    refine ⟨x, ha, ?_⟩
    simpa only [rankOneUpdate_apply, ha, zero_smul, add_zero] using hx
  · rintro ⟨x, hx, rfl⟩
    refine ⟨LinearMap.mem_range_self X x, x, ?_⟩
    have ha : a x = 0 := hx
    simp only [rankOneUpdate_apply, ha, zero_smul, add_zero]

/-- The updated image is a genuine Grassmann neighbor, with the full
ambient neighbor predicate rather than its chart restriction. -/
noncomputable def rankOneUpdateNeighbor [FiniteDimensional K E]
    (X : E →ₗ[K] F) (hX : Function.Injective X)
    (a : E →ₗ[K] K) (ha : a ≠ 0)
    (y : F) (hy : y ∉ LinearMap.range X) :
    MatrixChart.GrassmannNeighbors (LinearMap.range X) :=
  ⟨LinearMap.range (rankOneUpdate X a y), by
    constructor
    · rw [LinearMap.finrank_range_of_inj (injective_rankOneUpdate X hX a hy),
        LinearMap.finrank_range_of_inj hX]
    · rw [range_inf_rankOneUpdate X a hy,
        ← (Submodule.equivMapOfInjective X hX (LinearMap.ker a)).finrank_eq,
        LinearMap.finrank_range_of_inj hX]
      exact Module.Dual.finrank_ker_add_one_of_ne_zero ha⟩

@[simp] theorem rankOneUpdateNeighbor_val [FiniteDimensional K E]
    (X : E →ₗ[K] F) (hX : Function.Injective X)
    (a : E →ₗ[K] K) (ha : a ≠ 0) (y : F) (hy : y ∉ LinearMap.range X) :
    (rankOneUpdateNeighbor X hX a ha y hy).val =
      LinearMap.range (rankOneUpdate X a y) := rfl

end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

section

/-! Transport the product-coordinate chart into the actual Grassmann vertices
used by the KMS boundary. The transport is a proved ambient linear equivalence.
-/

namespace UniqueGamesTheorem.Inverse.MatrixChart

open Matrix

/-- Concatenate the two coordinate blocks of the chart ambient space. -/
def coordinateJoin (K : Type*) [Field K] (ell m : Nat) :
    ((Fin ell → K) × (Fin m → K)) ≃ₗ[K] (Fin (ell + m) → K) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin ell) (Fin m) K K).symm.trans
    (LinearEquiv.funCongrLeft K K finSumFinEquiv.symm)

/-- A matrix as an actual Grassmann vertex on `ell + m` binary coordinates. -/
def matrixVertex {ell m : Nat} (M : Matrix (Fin ell) (Fin m) (ZMod 2)) :
    KMS.Vertex (ell + m) ell :=
  ⟨(matrixGraph M).map (coordinateJoin (ZMod 2) ell m).toLinearMap, by
    rw [LinearEquiv.finrank_map_eq, finrank_matrixGraph, Fintype.card_fin]⟩

theorem matrixVertex_injective {ell m : Nat} :
    Function.Injective (matrixVertex (ell := ell) (m := m)) := by
  intro M N h
  apply matrixGraph_injective
  apply Submodule.map_injective_of_injective (coordinateJoin (ZMod 2) ell m).injective
  exact congrArg Subtype.val h

theorem finrank_matrixVertex_intersection {ell m : Nat}
    (M N : Matrix (Fin ell) (Fin m) (ZMod 2)) :
    Module.finrank (ZMod 2) ((matrixVertex M).val ⊓ (matrixVertex N).val :
      Submodule (ZMod 2) (KMS.Ambient (ell + m))) =
      Module.finrank (ZMod 2) (matrixGraph M ⊓ matrixGraph N :
        Submodule (ZMod 2) ((Fin ell → ZMod 2) × (Fin m → ZMod 2))) := by
  change Module.finrank (ZMod 2)
    ((matrixGraph M).map (coordinateJoin (ZMod 2) ell m).toLinearMap ⊓
      (matrixGraph N).map (coordinateJoin (ZMod 2) ell m).toLinearMap :
        Submodule (ZMod 2) (KMS.Ambient (ell + m))) = _
  rw [← Submodule.map_inf _ (coordinateJoin (ZMod 2) ell m).injective,
    LinearEquiv.finrank_map_eq]

/-- Exact correspondence with the KMS adjacency predicate, including its
explicit inequality requirement. -/
theorem adjacent_matrixVertex_iff {ell m : Nat}
    (M N : Matrix (Fin ell) (Fin m) (ZMod 2)) :
    KMS.Adjacent (matrixVertex M) (matrixVertex N) ↔
      Module.finrank (ZMod 2) (LinearMap.range (M.vecMulLinear - N.vecMulLinear)) = 1 := by
  have hdim : Module.finrank (ZMod 2) (Fin ell → ZMod 2) = ell := by simp
  constructor
  · intro h
    apply (adjacent_iff_rank_one M.vecMulLinear N.vecMulLinear).mp
    rw [hdim]
    rw [← finrank_matrixVertex_intersection M N]
    exact h.2
  · intro h
    refine ⟨?_, ?_⟩
    · intro heq
      have hMN : M = N := matrixVertex_injective heq
      subst N
      have hh := (adjacent_iff_rank_one M.vecMulLinear M.vecMulLinear).mpr h
      rw [inf_idem, finrank_graph] at hh
      omega
    · rw [finrank_matrixVertex_intersection]
      simpa only [hdim] using
        (adjacent_iff_rank_one M.vecMulLinear N.vecMulLinear).mpr h

noncomputable section

/-- The finite matrix chart in the Grassmann vertex type. -/
def matrixChart (ell m : Nat) : Finset (KMS.Vertex (ell + m) ell) := by
  classical
  exact Finset.univ.image (matrixVertex (ell := ell) (m := m))

@[simp] theorem mem_matrixChart {ell m : Nat} (L : KMS.Vertex (ell + m) ell) :
    L ∈ matrixChart ell m ↔
      ∃ M : Matrix (Fin ell) (Fin m) (ZMod 2), matrixVertex M = L := by
  classical
  simp [matrixChart]

end

end UniqueGamesTheorem.Inverse.MatrixChart

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_MatrixChartIntervalsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Exact rank-one sampling in the binary matrix chart. Nonzero pairs of a
functional and a vector represent rank-one maps uniquely over `ZMod 2`.
Thus uniform nonzero factors give uniform rank-one maps. Zero factors are
excluded explicitly; no conditioned/unconditioned sampling is identified.
-/

namespace UniqueGamesTheorem.Inverse.MatrixChart

section ArbitraryField

variable {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

/-- Every map with one-dimensional range is a nonzero functional times a
nonzero vector. This existence statement is valid over any field. -/
theorem exists_smulRight_of_rank_one (T : X →ₗ[K] Y)
    (hT : Module.finrank K T.range = 1) :
    ∃ (a : X →ₗ[K] K) (l : Y), a ≠ 0 ∧ l ≠ 0 ∧ T = a.smulRight l := by
  classical
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hT
  let a : X →ₗ[K] K := e.symm.toLinearMap.comp T.rangeRestrict
  have ha : a ≠ 0 := LinearMap.surjective_iff_ne_zero.mp
    (e.symm.surjective.comp T.surjective_rangeRestrict)
  have hl : (e 1 : Y) ≠ 0 := by
    intro h
    have he : e 1 = e 0 := by
      apply Subtype.ext
      simp at h
    exact one_ne_zero (e.injective he)
  refine ⟨a, (e 1 : Y), ha, hl, ?_⟩
  apply LinearMap.ext
  intro x
  have h : a x • e 1 = T.rangeRestrict x := by
    calc
      a x • e 1 = e (a x • (1 : K)) := (e.map_smul _ _).symm
      _ = e (a x) := by rw [smul_eq_mul, mul_one]
      _ = T.rangeRestrict x := e.apply_symm_apply _
  exact (congrArg Subtype.val h).symm

/-- The exact algebraic characterization of nonzero rank-one maps. -/
theorem rank_one_iff_exists_smulRight (T : X →ₗ[K] Y) :
    Module.finrank K T.range = 1 ↔
      ∃ (a : X →ₗ[K] K) (l : Y), a ≠ 0 ∧ l ≠ 0 ∧ T = a.smulRight l := by
  constructor
  · exact exists_smulRight_of_rank_one T
  · rintro ⟨a, l, ha, hl, rfl⟩
    rw [LinearMap.range_smulRight_apply ha]
    exact finrank_span_singleton hl

end ArbitraryField

section Binary

variable {X Y : Type*}
  [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

/-- Over the two-element field there is no nontrivial rescaling ambiguity. -/
theorem binary_smulRight_unique
    {a b : X →ₗ[ZMod 2] ZMod 2} {l k : Y}
    (ha : a ≠ 0) (hl : l ≠ 0)
    (h : a.smulRight l = b.smulRight k) : a = b ∧ l = k := by
  obtain ⟨x, hx⟩ := a.surjective ha 1
  have hx' : l = b x • k := by
    simpa only [LinearMap.smulRight_apply, hx, one_smul] using
      LinearMap.congr_fun h x
  have scalar_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hlk : l = k := by
    rcases scalar_cases (b x) with hb | hb
    · exact False.elim (hl (by simpa only [hb, zero_smul] using hx'))
    · simpa only [hb, one_smul] using hx'
  refine ⟨?_, hlk⟩
  apply LinearMap.ext
  intro y
  apply smul_left_injective (ZMod 2) hl
  have hy := LinearMap.congr_fun h y
  simpa only [LinearMap.smulRight_apply, ← hlk] using hy

/-- Ordered nonzero factors, with functional coordinate first. -/
abbrev BinaryRankOneFactors (X Y : Type*)
    [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y] :=
  {a : X →ₗ[ZMod 2] ZMod 2 // a ≠ 0} × {l : Y // l ≠ 0}

/-- The actual linear maps whose range has dimension one. -/
abbrev BinaryRankOneMaps (X Y : Type*)
    [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y] :=
  {T : X →ₗ[ZMod 2] Y // Module.finrank (ZMod 2) T.range = 1}

def binaryRankOneMap (p : BinaryRankOneFactors X Y) : BinaryRankOneMaps X Y :=
  ⟨p.1.val.smulRight p.2.val,
    (rank_one_iff_exists_smulRight _).mpr
      ⟨p.1.val, p.2.val, p.1.property, p.2.property, rfl⟩⟩

theorem binary_smulRight_injective :
    Function.Injective (binaryRankOneMap (X := X) (Y := Y)) := by
  intro p q h
  obtain ⟨ha, hl⟩ := binary_smulRight_unique p.1.property p.2.property
    (congrArg Subtype.val h)
  exact Prod.ext (Subtype.ext ha) (Subtype.ext hl)

theorem binary_smulRight_surjective :
    Function.Surjective (binaryRankOneMap (X := X) (Y := Y)) := by
  intro T
  obtain ⟨a, l, ha, hl, h⟩ := exists_smulRight_of_rank_one T.val T.property
  exact ⟨(⟨a, ha⟩, ⟨l, hl⟩), Subtype.ext h.symm⟩

/-- Bijection justifying uniform rank-one sampling by independent uniform
nonzero factors. The inverse uses choice only to select the proved unique pair. -/
noncomputable def binaryRankOneEquiv :
    BinaryRankOneFactors X Y ≃ BinaryRankOneMaps X Y :=
  Equiv.ofBijective binaryRankOneMap
    ⟨binary_smulRight_injective, binary_smulRight_surjective⟩

@[simp] theorem binaryRankOneEquiv_apply (p : BinaryRankOneFactors X Y) :
    (binaryRankOneEquiv p).val = p.1.val.smulRight p.2.val := rfl

end Binary

end UniqueGamesTheorem.Inverse.MatrixChart

end

section

/-!
Rank-one differences parametrize the actual Grassmann neighbors that remain
in the matrix chart. The equivalences retain the graph subspaces themselves,
so cardinalities and uniform sampling can be transported to the graph.
-/

namespace UniqueGamesTheorem.Inverse.MatrixChart

variable {X Y : Type*}
  [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]
  [FiniteDimensional (ZMod 2) X]

/-- Coordinate matrices adjacent to a fixed graph matrix. -/
abbrev BinaryChartNeighbors (T : X →ₗ[ZMod 2] Y) :=
  {U : X →ₗ[ZMod 2] Y //
    Module.finrank (ZMod 2) (T.graph ⊓ U.graph : Submodule (ZMod 2) (X × Y)) + 1 =
      Module.finrank (ZMod 2) X}

/-- The actual adjacent subspaces that lie in the graph chart. -/
abbrev BinaryGraphChartNeighbors (T : X →ₗ[ZMod 2] Y) :=
  {L : Submodule (ZMod 2) (X × Y) //
    (∃ U : X →ₗ[ZMod 2] Y, L = U.graph) ∧
      Module.finrank (ZMod 2) (T.graph ⊓ L : Submodule (ZMod 2) (X × Y)) + 1 =
        Module.finrank (ZMod 2) X}

/-- Difference from a fixed matrix is an exact bijection between rank-one
maps and adjacent matrices. Subtraction also makes this construction valid
without invoking characteristic-two simplification. -/
def rankOneEquivChartNeighbors (T : X →ₗ[ZMod 2] Y) :
    BinaryRankOneMaps X Y ≃ BinaryChartNeighbors T where
  toFun D := ⟨T - D.val, (adjacent_iff_rank_one T (T - D.val)).mpr (by
    have he : T - (T - D.val) = D.val := sub_sub_cancel T D.val
    rw [he]
    exact D.property)⟩
  invFun U := ⟨T - U.val, (adjacent_iff_rank_one T U.val).mp U.property⟩
  left_inv D := by
    apply Subtype.ext
    change T - (T - D.val) = D.val
    exact sub_sub_cancel T D.val
  right_inv U := by
    apply Subtype.ext
    change T - (T - U.val) = U.val
    exact sub_sub_cancel T U.val

def graphChartNeighbor (T : X →ₗ[ZMod 2] Y)
    (U : BinaryChartNeighbors T) : BinaryGraphChartNeighbors T :=
  ⟨U.val.graph, ⟨U.val, rfl⟩, U.property⟩

omit [FiniteDimensional (ZMod 2) X] in
theorem graphChartNeighbor_injective (T : X →ₗ[ZMod 2] Y) :
    Function.Injective (graphChartNeighbor T) := by
  intro U V h
  apply Subtype.ext
  exact graph_injective (congrArg Subtype.val h)

omit [FiniteDimensional (ZMod 2) X] in
theorem graphChartNeighbor_surjective (T : X →ₗ[ZMod 2] Y) :
    Function.Surjective (graphChartNeighbor T) := by
  intro L
  obtain ⟨U, hU⟩ := L.property.1
  have h :
      Module.finrank (ZMod 2) (T.graph ⊓ U.graph : Submodule (ZMod 2) (X × Y)) + 1 =
        Module.finrank (ZMod 2) X := by
    rw [← hU]
    exact L.property.2
  exact ⟨⟨U, h⟩, Subtype.ext hU.symm⟩

noncomputable def chartNeighborsEquivGraphNeighbors (T : X →ₗ[ZMod 2] Y) :
    BinaryChartNeighbors T ≃ BinaryGraphChartNeighbors T :=
  Equiv.ofBijective (graphChartNeighbor T)
    ⟨graphChartNeighbor_injective T, graphChartNeighbor_surjective T⟩

/-- The complete nonzero-factor sampling equivalence, ending in actual
Grassmann subspaces in the chart. -/
noncomputable def binaryFactorsEquivGraphNeighbors (T : X →ₗ[ZMod 2] Y) :
    BinaryRankOneFactors X Y ≃ BinaryGraphChartNeighbors T :=
  binaryRankOneEquiv.trans
    ((rankOneEquivChartNeighbors T).trans (chartNeighborsEquivGraphNeighbors T))

@[simp] theorem binaryFactorsEquivGraphNeighbors_apply (T : X →ₗ[ZMod 2] Y)
    (p : BinaryRankOneFactors X Y) :
    (binaryFactorsEquivGraphNeighbors T p).val =
      (T - p.1.val.smulRight p.2.val).graph := rfl

end UniqueGamesTheorem.Inverse.MatrixChart

end

section

/-! Extract actual vector-valued row/column data from an arbitrary interval.
The equation counts are the dimension/codimension of that interval, and no
homogeneity is imposed on the equation right-hand sides.
-/

namespace UniqueGamesTheorem.Inverse.MatrixChart

open Matrix

variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]

theorem dotFunctional_surjective :
    Function.Surjective (dotFunctional (K := K) (ι := ι)) := by
  classical
  intro f
  refine ⟨fun i => f (Pi.single i 1), ?_⟩
  apply (Pi.basisFun K ι).ext
  intro i
  change (fun j => f (Pi.single j 1)) ⬝ᵥ (Pi.basisFun K ι i) =
    f (Pi.basisFun K ι i)
  simp

end UniqueGamesTheorem.Inverse.MatrixChart

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_ShortcodeInterfaceLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Fixed-length descriptions for the row-erasure union bound. Row and column
equation lists are padded with zero equations. Targets retain both the linear
coefficient and the affine intercept. Thus the finite description count is
exactly `2^((2r+1)(ell+m))`, including descriptions with empty solution sets.
-/

namespace UniqueGamesTheorem.Inverse.RowErasureDescriptions

open scoped BigOperators

noncomputable section

/-- Add vacuous equations after the original finite list. -/
def padZero {n r : ℕ} {V : Type*} [Zero V] (f : Fin n → V) : Fin r → V :=
  fun i => if h : i.val < n then f ⟨i.val, h⟩ else 0

end
end UniqueGamesTheorem.Inverse.RowErasureDescriptions

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_RowErasureMatrixLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Visible selection of a row-erasure witness. The selected description depends
only on the fixed table function, the row map, and the observed row value.
The full sampled matrix enters only the later event testing its membership in
the already selected slice. Classical choice fixes one witness once and for all;
proof irrelevance makes the choice independent of the goodness proof.
-/

namespace UniqueGamesTheorem.Inverse.RowErasure

noncomputable section

variable {X Y A S D : Type*}

def SliceFamily.chosenDescription (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) : D :=
  Classical.choose hgood

theorem SliceFamily.chosenDescription_spec (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) :
    F.rowMap (F.chosenDescription f α a s hgood) = a ∧
      F.rowValue (F.chosenDescription f α a s hgood) = s ∧
      (F.points (F.chosenDescription f α a s hgood)).Nonempty ∧
      α / 2 ≤ F.agreement f (F.chosenDescription f α a s hgood) :=
  Classical.choose_spec hgood

/-- A total visible selector. Bad advice has no selected witness. -/
def SliceFamily.selectedDescription (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) : Option D := by
  classical
  exact if hgood : F.GoodAdvice f α a s then
    some (F.chosenDescription f α a s hgood) else none

/-- Good visible advice and the selected column restrictions on the hidden
matrix. The selector receives only its observed row value. -/
def SliceFamily.selectedEvent (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X) : Prop :=
  ∃ d, F.selectedDescription f α a (F.advice a x) = some d ∧ x ∈ F.points d

def SliceFamily.selectedMatch (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X) : Prop :=
  ∃ d, F.selectedDescription f α a (F.advice a x) = some d ∧
    x ∈ F.points d ∧ f x = F.target d x

end
end UniqueGamesTheorem.Inverse.RowErasure

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineCompositionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Static concatenation of finitely many concrete subroutines on common
tapes. The labels are a finite disjoint sum; no runtime instruction counter
or list is placed in the machine state. The simulation theorem composes the
actual local traces with exactly their summed transition counts. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineFiniteSequence

open Turing

variable {Command : Type} (LocalLabel : Command → Type)

def Label : List Command → Type
  | [] => Empty
  | command :: commands => LocalLabel command ⊕ Label commands

instance labelFintype [∀ command, Fintype (LocalLabel command)]
    (commands : List Command) : Fintype (Label LocalLabel commands) := by
  induction commands with
  | nil => exact inferInstanceAs (Fintype Empty)
  | cons command commands ih =>
      letI := ih
      exact inferInstanceAs (Fintype (LocalLabel command ⊕ Label LocalLabel commands))

instance labelDecidableEq [∀ command, DecidableEq (LocalLabel command)]
    (commands : List Command) : DecidableEq (Label LocalLabel commands) := by
  induction commands with
  | nil => exact inferInstanceAs (DecidableEq Empty)
  | cons command commands ih =>
      letI := ih
      exact inferInstanceAs (DecidableEq (LocalLabel command ⊕ Label LocalLabel commands))

variable (main : ∀ command, LocalLabel command)
variable {K Λ σ : Type} {Γ : K → Type}

def entry : (commands : List Command) → (Label LocalLabel commands → Λ) → Option Λ → Option Λ
  | [], _, exit => exit
  | command :: _, labels, _ => some (labels (.inl (main command)))

variable (localInstruction : ∀ command, (LocalLabel command → Λ) → Option Λ →
  LocalLabel command → TM2.Stmt Γ Λ σ)

def instruction : (commands : List Command) → (Label LocalLabel commands → Λ) → Option Λ →
    Label LocalLabel commands → TM2.Stmt Γ Λ σ
  | [], _, _, label => nomatch label
  | command :: commands, labels, exit, .inl label =>
      localInstruction command (fun l => labels (.inl l))
        (entry LocalLabel main commands (fun l => labels (.inr l)) exit) label
  | _ :: commands, labels, exit, .inr label =>
      instruction commands (fun l => labels (.inr l)) exit label

variable {Data : Type} (result : Command → Data → Data) (cost : Command → Data → Nat)

def resultOf : List Command → Data → Data
  | [], data => data
  | command :: commands, data => resultOf commands (result command data)

def steps : List Command → Data → Nat
  | [], _ => 0
  | command :: commands, data => cost command data + steps commands (result command data)

end UniqueGamesTheorem.Foundations.Complexity.MachineFiniteSequence

end

section

/-!
# An actual finite machine for a fixed-size Boolean block map

The program parameters `N`, `M`, and `F` are fixed. The local register has
exactly `N` bits. A syntactic chain of `N` pops fills that register, and a
syntactic chain of `M` pushes writes `F` of the register. No instruction
applies `F` to an unbounded word. An arbitrary ambient state is preserved,
and the local register is reset before the optional continuation.

TM2 executes a whole finite statement in one transition. The push bound
below separately records the exact `M` pushes in this statement.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineFixedBlockMap

open Turing

abbrev Buffer (N : Nat) := Fin N → Bool

def emptyBuffer (N : Nat) : Buffer N := fun _ => false

section Chains

variable {K Λ σ : Type} {N : Nat}

/-- Proof-level description of the finite register updates. -/
def fill (slots : List (Fin N)) (bits buffer : Buffer N) : Buffer N :=
  slots.foldl (fun buffer i => Function.update buffer i (bits i)) buffer

end Chains

section Block

variable {K Λ σ : Type} {N M : Nat}

def finishAt (exit : Option Λ) : TM2.Stmt (fun _ : K => Bool) Λ σ :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

end Block

end UniqueGamesTheorem.Foundations.Complexity.MachineFixedBlockMap

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

namespace UniqueGamesTheorem.Foundations.Target

theorem Instance.constraintCount_positive {q : Nat} (game : Instance q) :
    0 < game.constraints.length := by
  cases h : game.constraints with
  | nil => exact False.elim (game.nonempty h)
  | cons constraint rest => simp

end UniqueGamesTheorem.Foundations.Target

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineSubroutineLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Concrete forward-table serialization of unique games. The parser reconstructs
an inverse by finite search and checks both inverse laws. Constraint occurrences,
including repeated parallel edges, are preserved in their original list order. -/

namespace UniqueGamesTheorem.Foundations.Complexity

open Target

def parseLabel (alphabet value : Nat) : Option (Fin alphabet) :=
  if bounded : value < alphabet then some ⟨value, bounded⟩ else none

end UniqueGamesTheorem.Foundations.Complexity

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Pure list specification for destructive zero-based unary table lookup.
These are serialization identities and bit-count bounds, not TM2 runtime
certificates. The connection to actual transitions is in `MachineLookup`.
-/
namespace UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec

/-! Bounds on the proposed lookup recurrence. A separate machine proof must
identify these counts with actual transition traces. -/

def steps : List Nat → Nat → Nat
  | [], i => 2 * i + 2
  | n :: _, 0 => n + 3
  | n :: ns, i + 1 => n + 2 + steps ns i

end UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec

end

section

/-!
One actual TM2 transition tests and decrements a zero-delimited unary counter.
The guard peeks before branching: a true bit is popped, while a false delimiter
is retained. Both branches clear the one-bit register and preserve the ambient
state. There is no assumed execution trace or input-dependent finite program.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

/-- A single finite statement: inspect the counter, decrement a positive
counter, and jump to the body or exit. The zero delimiter is never consumed. -/
def guard (counter : K) (bodyLabel exitLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .peek counter (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.pop counter (fun state _ => (state.1, none)) (.goto fun _ => bodyLabel))
      (.load (fun state => (state.1, none)) (.goto fun _ => exitLabel)))

end UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter

end

section

/-!
Counted loops in one actual TM2 program. A unary guard is executed once before
each caller body and once more at zero. The caller supplies only individual
body traces, each returning to the guard with the same counter remainder.

Schedules are indexed by the remaining count: body `r` takes ambient state
`r + 1` to ambient state `r`. Consequently the run starts at index `n` and
ends at index zero. Bodies may change the ambient state and unprotected tapes.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCountedLoop

open Turing
open scoped BigOperators
open MachineUnaryCounter

variable {K Λ σ : Type} [DecidableEq K]

/-- Exactly `n` supplied body blocks and `n + 1` concrete guard transitions. -/
def totalSteps (cost : Nat → Nat) (n : Nat) : Nat :=
  (∑ r ∈ Finset.range n, cost r) + n + 1

@[simp] theorem totalSteps_zero (cost : Nat → Nat) : totalSteps cost 0 = 1 := by
  simp [totalSteps]

theorem totalSteps_succ (cost : Nat → Nat) (n : Nat) :
    totalSteps cost (n + 1) = (totalSteps cost n + cost n) + 1 := by
  simp only [totalSteps, Finset.sum_range_succ]
  omega

theorem totalSteps_le (cost : Nat → Nat) (n B : Nat)
    (bodyBound : ∀ r, r < n → cost r ≤ B) :
    totalSteps cost n ≤ n * (B + 1) + 1 := by
  have hsum : (∑ r ∈ Finset.range n, cost r) ≤ n * B := by
    calc
      (∑ r ∈ Finset.range n, cost r) ≤ ∑ _r ∈ Finset.range n, B :=
        Finset.sum_le_sum (fun r hr => bodyBound r (Finset.mem_range.mp hr))
      _ = n * B := by simp
  simpa only [totalSteps, Nat.mul_add, Nat.mul_one] using
    Nat.add_le_add_right (Nat.add_le_add_right hsum n) 1

end UniqueGamesTheorem.Foundations.Complexity.MachineCountedLoop

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_GapSemanticsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact bridges between the integer-encoded target gaps and acceptance rates.
Repeated constraint entries retain their multiplicity in every definition. -/

namespace UniqueGamesTheorem.Integration.GapSemantics

open UniqueGamesTheorem.Foundations.Target

def satisfactionRate {q : Nat} (g : Instance q) (labeling : Fin g.vertices → Fin q) : ℚ :=
  (countSatisfied labeling g.constraints : ℚ) / g.constraints.length

theorem countSatisfied_eq_sum {n q : Nat} (labeling : Fin n → Fin q)
    (constraints : List (Constraint n q)) :
    countSatisfied labeling constraints =
      (constraints.map (fun c => if c.satisfied labeling then (1 : Nat) else 0)).sum := by
  induction constraints with
  | nil => rfl
  | cons c cs ih => simp [countSatisfied, ih]

theorem countSatisfied_ofFn {m n q : Nat} (labeling : Fin n → Fin q)
    (constraints : Fin m → Constraint n q) :
    countSatisfied labeling (List.ofFn constraints) =
      ∑ i, if (constraints i).satisfied labeling then (1 : Nat) else 0 := by
  rw [countSatisfied_eq_sum, List.map_ofFn, List.sum_ofFn]
  rfl

end UniqueGamesTheorem.Integration.GapSemantics

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_RealTargetLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The value of the actual finite Unique Games instance is its maximum satisfied
constraint fraction. Maximization ranges over every finite vertex labeling;
the denominator counts stored constraint occurrences, including repetitions.
The natural-number maximum totalizes an empty labeling type at zero. The
attainment and threshold equivalences require a positive alphabet.
-/

namespace UniqueGamesTheorem.Integration.InstanceValue

open UniqueGamesTheorem.Foundations
open Target

/-- The maximum number of satisfied occurrences among all vertex labelings. -/
def maxSatisfied {q : Nat} (g : Instance q) : Nat :=
  Finset.univ.sup (fun labeling : Fin g.vertices → Fin q =>
    countSatisfied labeling g.constraints)

theorem countSatisfied_le_maxSatisfied {q : Nat} (g : Instance q)
    (labeling : Fin g.vertices → Fin q) :
    countSatisfied labeling g.constraints ≤ maxSatisfied g := by
  unfold maxSatisfied
  exact Finset.le_sup
    (f := fun labeling : Fin g.vertices → Fin q => countSatisfied labeling g.constraints)
    (Finset.mem_univ labeling)

theorem maxSatisfied_attained {q : Nat} (g : Instance q) (hq : 0 < q) :
    ∃ labeling : Fin g.vertices → Fin q,
      countSatisfied labeling g.constraints = maxSatisfied g := by
  have inhabited : (Finset.univ : Finset (Fin g.vertices → Fin q)).Nonempty :=
    ⟨fun _ => ⟨0, hq⟩, Finset.mem_univ _⟩
  obtain ⟨labeling, _, hmax⟩ := Finset.exists_mem_eq_sup Finset.univ inhabited
    (fun labeling : Fin g.vertices → Fin q => countSatisfied labeling g.constraints)
  exact ⟨labeling, hmax.symm⟩

end UniqueGamesTheorem.Integration.InstanceValue

end

section

/-! Injective vertex addresses may leave unused output vertices. The actual
instance is obtained by mapping endpoints in the original constraint list;
constraint order, multiplicity, and permutation tables are retained exactly. -/

namespace UniqueGamesTheorem.Integration.VertexEmbedding

open UniqueGamesTheorem.Foundations.Target
open GapSemantics TranslationTarget

/-- The extension is only used as a semantic witness, not by the instance constructor. -/
noncomputable def extendLabeling {n m q : Nat} (f : Fin n → Fin m)
    (labeling : Fin n → Fin q) (defaultLabel : Fin q) (v : Fin m) : Fin q := by
  classical
  exact if h : ∃ u, f u = v then labeling (Classical.choose h) else defaultLabel

end UniqueGamesTheorem.Integration.VertexEmbedding

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_MaskMomentLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Clean

open scoped BigOperators

noncomputable section

/-- The exact mask, including the empty mask at `k = 0`. -/
def maskCount {k : ℕ} (mask : Fin k → Bool) : ℕ :=
  (Finset.univ.filter fun i => mask i = true).card

variable {E : Type*} [Fintype E] [Nonempty E]

/-- `origin` is instantiated by the zero advice slope. Keeping it explicit also
shows that every specified slope has exactly the same chance. -/
def cleanBit (origin : E) (sample : Bool × E) : Bool := by
  classical
  exact sample.1 && decide (sample.2 = origin)

end
end UniqueGamesTheorem.Clean

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_SparseLawLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The finite calculation of projected total variation. The three singleton
lines are averaged before the divergence is taken; projection choices are
not part of the compared sample space. Coordinates are independently sampled
occurrences, irrespective of whether their equation IDs coincide.
-/

namespace UniqueGamesTheorem.Decoder.SparseLaw

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Information

noncomputable section

variable {α : Type*} [Fintype α]

def uniformWeights (α : Type*) [Fintype α] : α → ℝ :=
  fun _ => 1 / Fintype.card α

theorem uniformWeights_pos [Nonempty α] (a : α) : 0 < uniformWeights α a := by
  exact div_pos (by norm_num) (Nat.cast_pos.mpr Fintype.card_pos)

theorem uniformWeights_isProbability [Nonempty α] :
    IsProbability (uniformWeights α) := by
  constructor
  · exact fun a => (uniformWeights_pos a).le
  · simp [uniformWeights, Fintype.card_ne_zero]

/-- Pearson divergence against the uniform law, written with its constant
denominator cleared. `uniformChiSquare_eq_pearson` identifies the actual
likelihood-ratio definition. -/
def uniformChiSquare (p : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ) * ∑ a, (p a - uniformWeights α a) ^ 2

def mixture (β : ℝ) (p : α → ℝ) : α → ℝ :=
  fun a => (1 - β) * uniformWeights α a + β * p a

def independentWeights (p : α → ℝ) (k : ℕ) : (Fin k → α) → ℝ :=
  fun x => ∏ i, p (x i)

theorem independentWeights_isProbability (p : α → ℝ) (hp : IsProbability p)
    (k : ℕ) : IsProbability (independentWeights p k) := by
  constructor
  · intro x
    exact Finset.prod_nonneg fun i _ => hp.1 (x i)
  · change (∑ x : Fin k → α, ∏ i, p (x i)) = 1
    rw [← Fintype.sum_pow, hp.2, one_pow]

section Singleton

variable (V : Type*) [Fintype V] [Zero V] [DecidableEq V]

/-- At the origin all three singleton lines contribute. -/
def lineCount (z : V × V) : ℝ :=
  (if z.2 = 0 then 1 else 0) + (if z.1 = 0 then 1 else 0) +
    (if z.1 = z.2 then 1 else 0)

/-- The average of the laws of `(a,0)`, `(0,a)`, and `(a,a)` for uniform `a`. -/
def singletonPairWeights (z : V × V) : ℝ := lineCount V z / (3 * Fintype.card V)

/-- Explicit finite pushforward of the three equally likely singleton choices.
The same uniform slope supplies both entries of the diagonal choice. -/
def singletonSamplerWeights (z : V × V) : ℝ :=
  ((∑ a : V, if (a, 0) = z then uniformWeights V a else 0) +
    (∑ a : V, if (0, a) = z then uniformWeights V a else 0) +
    (∑ a : V, if (a, a) = z then uniformWeights V a else 0)) / 3

end Singleton

end
end UniqueGamesTheorem.Decoder.SparseLaw

end

section

namespace UniqueGamesTheorem.Decoder.ConstantSelection

open UniqueGamesTheorem.Foundations.Information
open SparseLaw

noncomputable section

/-- Probability of actual visible data carrying a transferred witness. -/
def visibleMass (α g₀ : ℝ) (ell r : ℕ) : ℝ :=
  α * g₀ / (8 * (2 : ℝ) ^ (ell * r))

/-- Independent private decoding success on a transferred witness. -/
def conditionalMass (α : ℝ) (ell r : ℕ) : ℝ :=
  (α / 8) ^ 2 / (2 : ℝ) ^ (ell * r) / (2 : ℝ) ^ r

def decodingMass (α g₀ : ℝ) (ell r : ℕ) : ℝ :=
  visibleMass α g₀ ell r * conditionalMass α ell r

/-- The whole-table TV budget includes the coefficient of both compared
events in the witness-margin inequality. -/
def variationBudget (α g₀ : ℝ) (ell r : ℕ) : ℝ :=
  visibleMass α g₀ ell r / (1 + α / 4)

end
end UniqueGamesTheorem.Decoder.ConstantSelection

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_ActualCanonicalLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.CloneGap

variable {α : Type*} {β : Type*} {Name : Type}

abbrev Index := Nat

end UniqueGamesTheorem.Reduction.CloneGap

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_EncodingLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Computable binary alphabet indexing and full translation permutation tables.
The labels are actual `Fin (2^s)` entries in the target instance format.
-/

namespace UniqueGamesTheorem.Reduction.Encoding

open Integration.BinaryLinear
open Foundations.Target

/-- Number the left side first and the right side second. -/
def sideEquiv (n : Nat) : Bool × Fin n ≃ Fin (2*n) :=
  (finTwoEquiv.symm.prodCongr (Equiv.refl (Fin n))).trans finProdFinEquiv

@[simp] theorem sideEquiv_false_val {count : Nat} (i : Fin count) :
    (sideEquiv count (false, i)).val = i.val := by
  simp [sideEquiv, finProdFinEquiv, finTwoEquiv]

@[simp] theorem sideEquiv_true_val {count : Nat} (i : Fin count) :
    (sideEquiv count (true, i)).val = count + i.val := by
  simp [sideEquiv, finProdFinEquiv, finTwoEquiv, Nat.add_comm]

section ImageNumbering

variable {Q V : Type*} [DecidableEq V]

/-- Canonical vertex bodies are compared using their actual decidable equality.
`List.dedup` fixes a deterministic order by retaining the last occurrence. -/
def imageVertices (queries : List Q) (body : Q → V) : List V :=
  (queries.map body).dedup

theorem mem_imageVertices {queries : List Q} {body : Q → V} {v : V} :
    v ∈ imageVertices queries body ↔ ∃ q ∈ queries, body q = v := by
  simp [imageVertices]

theorem imageVertices_nodup (queries : List Q) (body : Q → V) :
    (imageVertices queries body).Nodup := List.nodup_dedup _

abbrev ImageVertex (queries : List Q) (body : Q → V) :=
  {v : V // v ∈ imageVertices queries body}

/-- A computable numbering using `idxOf`; its inverse looks up that index.
It involves no chosen `Fintype.equivFin`. -/
def imageEquiv (queries : List Q) (body : Q → V) :
    ImageVertex queries body ≃ Fin (imageVertices queries body).length :=
  (List.Nodup.getEquiv _ (imageVertices_nodup queries body)).symm

theorem imageVertices_range (queries : List Q) (body : Q → V)
    (full : ∀ q, q ∈ queries) (v : V) :
    v ∈ imageVertices queries body ↔ v ∈ Set.range body := by
  simp [mem_imageVertices, full, Set.mem_range]

end ImageNumbering

end UniqueGamesTheorem.Reduction.Encoding

end

section

/-! Internal serialization of canonical orbit bodies. Each record occupies nine
natural-number words, so record boundaries are independent of the tag. The
outer complement coordinate occupies one leading word. These are injectivity,
deduplication, and output-size statements, not machine running-time claims. -/

namespace UniqueGamesTheorem.Reduction.CanonicalEncoding

open Integration.BinaryLinear
open Foundations.Complexity

def wordBound (n m s d : Nat) : Nat := n + m + 2^s + 2^d + 3

end UniqueGamesTheorem.Reduction.CanonicalEncoding

end

section

/-! Direct canonical-body addresses. The fixed list of canonical words is
interpreted in big-endian order, matching forward Horner steps `B*acc+digit`.
Unused addresses represent isolated vertices. These are semantic encoding and
polynomial-size results, not an assumed machine implementation. -/

namespace UniqueGamesTheorem.Reduction.CanonicalAddress

open CanonicalEncoding

/-- Most-significant-word first, with leading zero words retained in the
fixed-length domain. Mathlib's `ofDigits` uses the opposite list order. -/
def radix (B : Nat) (words : List Nat) : Nat := Nat.ofDigits B words.reverse

theorem radix_eq_foldl (B : Nat) (words : List Nat) :
    radix B words = words.foldl (fun acc digit => B * acc + digit) 0 := by
  unfold radix
  rw [Nat.ofDigits_eq_foldr, List.foldr_reverse]
  simp only [Nat.cast_id, Nat.add_comm]

/-- One larger than the proved bound on every canonical word. -/
def base (n m s d : Nat) : Nat := wordBound n m s d + 1

end UniqueGamesTheorem.Reduction.CanonicalAddress

end

section

namespace UniqueGamesTheorem.Reduction.CanonicalWordTemplate

open Foundations.Complexity CanonicalEncoding

/-- A literal word or a reference to one of the four saved input fields. -/
inductive Token
  | literal (value : Nat)
  | name (index : Fin 3)
  | occurrence
  deriving DecidableEq, Repr

def evalToken (names : Fin 3 → Nat) (occurrence : Nat) : Token → Nat
  | .literal value => value
  | .name index => names index
  | .occurrence => occurrence

def evalTemplate (names : Fin 3 → Nat) (occurrence : Nat)
    (tokens : List Token) : List Nat :=
  tokens.map (evalToken names occurrence)

def blankTemplate : List Token :=
  [.literal 0, .literal 0, .literal 0, .literal 0, .literal 0,
    .literal 0, .literal 0, .literal 0, .literal 0]

end UniqueGamesTheorem.Reduction.CanonicalWordTemplate

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceNoiseParameterLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Real Walsh analysis on finite Boolean cubes. The basis and inversion
identities are proved from the explicit coordinate characters. -/

noncomputable section

namespace UniqueGamesTheorem.Foundations.Hastad

open scoped BigOperators
open Finset

abbrev Cube (I : Type*) := I → Bool

def bitSign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem bitSign_sq (b : Bool) : bitSign b ^ 2 = 1 := by
  cases b <;> norm_num [bitSign]

def cubeXor {I : Type*} (x y : Cube I) : Cube I := fun i => x i ^^ y i

def walsh {I : Type*} [Fintype I] [DecidableEq I] (s x : Cube I) : ℝ :=
  ∏ i, bitSign (s i && x i)

@[simp] theorem walsh_sq {I : Type*} [Fintype I] [DecidableEq I] (s x : Cube I) :
    walsh s x ^ 2 = 1 := by
  simp [walsh, ← Finset.prod_pow]

def coefficient {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → ℝ) (s : Cube I) : ℝ :=
  𝔼 x, f x * walsh s x

end UniqueGamesTheorem.Foundations.Hastad

end

end

section

noncomputable section

namespace UniqueGamesTheorem.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- The third queried Boolean table is `g * (f ∘ π) * μ` in sign notation. -/
def thirdQuery (π : J → I) (f : Cube I) (g μ : Cube J) : Cube J :=
  cubeXor g (cubeXor (fun y => f (π y)) μ)

end UniqueGamesTheorem.Foundations.Hastad

end

end

section

/-! Explicit half-table storage, odd folding, and conditioning on the finite
set of satisfying local assignments for Håstad's test. -/

noncomputable section

namespace UniqueGamesTheorem.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

def cubeFlip (f : Cube I) : Cube I := fun i => !(f i)

omit [Fintype I] [DecidableEq I] in
@[simp] theorem cubeFlip_cubeFlip (f : Cube I) : cubeFlip (cubeFlip f) = f := by
  funext i
  simp [cubeFlip]

@[simp] theorem bitSign_not (b : Bool) : bitSign (!b) = -bitSign b := by
  cases b <;> norm_num [bitSign]

def representative (i₀ : I) (f : Cube I) : Cube I :=
  if f i₀ then cubeFlip f else f

omit [Fintype I] [DecidableEq I] in
theorem representative_at (i₀ : I) (f : Cube I) :
    representative i₀ f i₀ = false := by
  cases hf : f i₀ <;> simp [representative, cubeFlip, hf]

abbrev HalfCube (i₀ : I) := {f : Cube I // f i₀ = false}

def canonicalInput (i₀ : I) (f : Cube I) : HalfCube i₀ :=
  ⟨representative i₀ f, representative_at i₀ f⟩

/-- One stored bit and one explicit sign correction for every queried table. -/
def foldedAnswer (i₀ : I) (table : HalfCube i₀ → Bool) (f : Cube I) : Bool :=
  table (canonicalInput i₀ f) ^^ f i₀

def coordinateMask (i : I) : Cube I := fun j => decide (j = i)

def cubeToggle (i : I) (f : Cube I) : Cube I :=
  cubeXor f (coordinateMask i)

omit [Fintype I] in
@[simp] theorem cubeToggle_twice (i : I) (f : Cube I) :
    cubeToggle i (cubeToggle i f) = f := by
  funext j
  change ((f j ^^ coordinateMask i j) ^^ coordinateMask i j) = f j
  cases f j <;> cases coordinateMask i j <;> rfl

def restrictQuery (valid : I → Bool) (f : Cube I) :
    Cube {i : I // valid i = true} := fun i => f i.val

def conditionedFoldedAnswer (valid : I → Bool) (i₀ : {i : I // valid i = true})
    (table : HalfCube i₀ → Bool) (f : Cube I) : Bool :=
  foldedAnswer i₀ table (restrictQuery valid f)

end UniqueGamesTheorem.Foundations.Hastad

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_ExplicitLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.Explicit

variable {α β : Type*}

/-- A Cartesian product that preserves repetitions in each input list. -/
def pairs (xs : List α) (ys : List β) : List (α × β) :=
  xs.flatMap fun x => ys.map fun y => (x, y)

theorem length_pairs (xs : List α) (ys : List β) :
    (pairs xs ys).length = xs.length * ys.length := by
  induction xs with
  | nil => simp [pairs]
  | cons x xs ih =>
    simp only [pairs, List.flatMap_cons, List.length_append, List.length_map,
      List.length_cons] at *
    rw [ih, Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem mem_pairs {xs : List α} {ys : List β} {x : α} {y : β} :
    (x, y) ∈ pairs xs ys ↔ x ∈ xs ∧ y ∈ ys := by
  simp [pairs]

/-- Enumerate all words of length `k` over an explicitly listed alphabet. -/
def words (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | k + 1 => (pairs alphabet (words alphabet k)).map fun p => p.1 :: p.2

/-- The formula in Equation (4.21). -/
def edgeCount (m k dimR noiseCount : Nat) : Nat :=
  m^k * 2^((2*k + 1)*(dimR + 1)) * noiseCount

end UniqueGamesTheorem.Reduction.Explicit

end

section

/-! Actual finite linear-map enumeration for the free homogeneous coordinates.
The lists contain linear maps themselves, constructed by finite coordinate sums.
Their exhaustiveness and lack of repetitions identify the list with the uniform
map experiment. No machine running-time claim follows just from their lengths.
-/

namespace UniqueGamesTheorem.Reduction.ActualEnumeration

open Integration.BinaryLinear
open UniqueGamesTheorem.Reduction.Explicit
open scoped BigOperators

variable {α β N : Type*} {m n k s d noiseCount : Nat}

theorem nodup_pairs {xs : List α} {ys : List β} (hx : xs.Nodup) (hy : ys.Nodup) :
    (pairs xs ys).Nodup := hx.product hy

/-- Exhaustive finite-function enumeration with a specified value list. -/
def functions (values : List α) : (n : Nat) → List (Fin n → α)
  | 0 => [Fin.elim0]
  | n + 1 => (pairs values (functions values n)).map
      (fun p => Fin.cons p.1 p.2)

theorem length_functions (values : List α) (n : Nat) :
    (functions values n).length = values.length^n := by
  induction n with
  | zero => simp [functions]
  | succ n ih => simp [functions, length_pairs, ih, pow_succ, Nat.mul_comm]

theorem mem_functions {values : List α} (full : ∀ a, a ∈ values)
    (f : Fin n → α) : f ∈ functions values n := by
  induction n with
  | zero =>
    have : f = Fin.elim0 := by funext i; exact Fin.elim0 i
    simp [functions, this]
  | succ n ih =>
    apply List.mem_map.mpr
    exact ⟨(f 0, Fin.tail f), mem_pairs.mpr ⟨full _, ih _⟩, Fin.cons_self_tail f⟩

theorem nodup_functions {values : List α} (distinct : values.Nodup) (n : Nat) :
    (functions values n).Nodup := by
  induction n with
  | zero => simp [functions]
  | succ n ih =>
    apply (nodup_pairs distinct ih).map
    intro x y h
    apply Prod.ext
    · exact congrFun h 0
    · funext i
      exact congrFun h i.succ

section Coefficients

variable (k : Nat) (R : Type*) [AddCommGroup R] [Module F2 R]

abbrev Coefficients := R × (Fin k → R × R)

end Coefficients

end UniqueGamesTheorem.Reduction.ActualEnumeration

end

section

/-!
# Realizing the existing Håstad noise law with a finite uniform tape

A tape contains one element of `Fin D` per coordinate. The corresponding noise
bit is true exactly when that element has value zero. For `D > 0`, its law is
exactly `Foundations.Hastad.noiseWeight ((D : ℝ)⁻¹)`.

The construction also permits an empty coordinate type and `D = 1`.
-/

namespace UniqueGamesTheorem.Reduction.FiniteNoise

open scoped BigOperators

def realizedBit {D : Nat} (z : Fin D) : Bool := decide (z.val = 0)

def realizedNoise {A : Type*} {D : Nat} (z : A → Fin D) : A → Bool :=
  fun a => realizedBit (z a)

end UniqueGamesTheorem.Reduction.FiniteNoise

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_ActualSpectralLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction

namespace UniqueGamesTheorem.Decoder.ActualSpectral

open NoiseSampler

def eta (r : Nat) : ℝ := ((2 : ℝ) ^ r)⁻¹ / 16

end UniqueGamesTheorem.Decoder.ActualSpectral

end

end

section

namespace UniqueGamesTheorem.Decoder.ActualGoodRows

open Integration.BinaryLinear Reduction
open Inverse Inverse.RowErasure
open scoped BigOperators Classical

noncomputable section

def goodRowMass (rstar s r : ℕ) : ℝ :=
  10 * ActualSpectral.eta rstar ^ 2 / (2 : ℝ) ^ (s * r)

end
end UniqueGamesTheorem.Decoder.ActualGoodRows

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_PaddedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Actual linear-map realization of the sparse padded-table experiment.
The finite sample has one independent full pair or singleton coefficient at
each occurrence position and one independent homogeneous intercept. Its map
is formed by composing a genuine map on the raw projected target with the
actual parity projection. The third position contributes its parity-dependent
intercept; it is not treated as a homogeneous two-coordinate projection.
-/

namespace UniqueGamesTheorem.Decoder.PaddedLaw

open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open SparseLaw

noncomputable section
attribute [local instance] Classical.propDecidable

section FinitePushforward

variable {α B : Type*} [Fintype α]

def pushforwardWeight (p : α → ℝ) (f : α → B) (y : B) : ℝ :=
  ∑ x, if f x = y then p x else 0

end FinitePushforward

end
end UniqueGamesTheorem.Decoder.PaddedLaw

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_VisibleTransferLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Decoder.VisibleTransfer

open scoped BigOperators

noncomputable section

variable {Ω D : Type*} [Fintype Ω] [Fintype D]

/-- The part of an event in one actual visible-data fiber. -/
def fiberEvent (observe : Ω → D) (d : D) (event : Ω → Bool) : Ω → Bool := by
  classical
  exact fun x => decide (observe x = d) && event x

end
end UniqueGamesTheorem.Decoder.VisibleTransfer

end

section

namespace UniqueGamesTheorem.Decoder.UniformFibers

open scoped BigOperators Classical

noncomputable section

variable {Ω D Y : Type*}

def selectedFiberEquiv (observe : Ω → D) (d : D) (slice : Ω → Bool)
    (e : Y ≃ {x : Ω // observe x = d}) :
    {x : Ω // VisibleTransfer.fiberEvent observe d slice x = true} ≃
      {y : Y // slice (e y).val = true} where
  toFun x := by
    have hx : observe x.val = d ∧ slice x.val = true := by
      simpa only [VisibleTransfer.fiberEvent, Bool.and_eq_true, decide_eq_true_eq] using x.property
    refine ⟨e.symm ⟨x.val, hx.1⟩, ?_⟩
    simpa only [Equiv.apply_symm_apply] using hx.2
  invFun y := ⟨(e y.val).val, by
    simp only [VisibleTransfer.fiberEvent, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨(e y.val).property, y.property⟩⟩
  left_inv x := by
    apply Subtype.ext
    dsimp
    simp only [Equiv.apply_symm_apply]
  right_inv y := by
    apply Subtype.ext
    exact e.symm_apply_apply y.val

end
end UniqueGamesTheorem.Decoder.UniformFibers

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_WeightedPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Weighted total probability for the public clean-coordinate observation.
The observation may have zero-probability fibres. Only its positive fibres
require a conditional bound; the identity itself is proved from finite sums.
-/

namespace UniqueGamesTheorem.Clean.WeightedPartition

open scoped BigOperators

noncomputable section

variable {Ω H : Type*} [Fintype Ω] [Fintype H] [DecidableEq H]

def fibre (observe : Ω → H) (h : H) : Ω → Bool :=
  fun x => decide (observe x = h)

end
end UniqueGamesTheorem.Clean.WeightedPartition

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

theorem sum_div_const {ι : Type*} [Fintype ι] (f : ι → ℝ) (c : ℝ) :
    (∑ i, f i) / c = ∑ i, f i / c := by
  simp only [div_eq_mul_inv, Finset.sum_mul]

abbrev RectangleSeed (thresholds : List ℝ) (α : Type*) :=
  α × Fin (thresholdPartition thresholds).length

def rectangleWeight (thresholds : List ℝ) (seed : RectangleSeed thresholds α) : ℝ :=
  ((thresholdPartition thresholds)[seed.2].hi - (thresholdPartition thresholds)[seed.2].lo) /
    (Fintype.card α : ℝ)

def rectangleAccept (thresholds : List ℝ) (density : α → ℝ)
    (seed : RectangleSeed thresholds α) : Bool :=
  decide ((thresholdPartition thresholds)[seed.2].lo < density seed.1)

theorem rectangleWeight_nonnegative (thresholds : List ℝ) (seed : RectangleSeed thresholds α) :
    0 ≤ rectangleWeight thresholds seed :=
  div_nonneg (sub_nonneg.mpr ((thresholdPartition thresholds)[seed.2].valid)) (by positivity)

theorem rectangleWeight_normalized [Nonempty α] (thresholds : List ℝ) :
    ∑ seed : RectangleSeed thresholds α, rectangleWeight thresholds seed = 1 := by
  rw [Fintype.sum_prod_type]
  have hrow (a : α) : (∑ i, rectangleWeight thresholds (a, i)) =
      1 / (Fintype.card α : ℝ) := by
    unfold rectangleWeight
    rw [← sum_div_const, sum_interval_get (fun I => I.hi - I.lo), partition_total_mass]
  simp_rw [hrow]
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [hc]

theorem rectangle_row_mass (thresholds : List ℝ) (density : α → ℝ) (a : α)
    (hm : density a ∈ thresholds) (h0 : 0 ≤ density a) (h1 : density a ≤ 1) :
    (∑ i, if rectangleAccept thresholds density (a, i) then
      rectangleWeight thresholds (a, i) else 0) = density a / (Fintype.card α : ℝ) := by
  calc
    _ = (∑ i : Fin (thresholdPartition thresholds).length,
        if (thresholdPartition thresholds)[i].lo < density a then
          (thresholdPartition thresholds)[i].hi - (thresholdPartition thresholds)[i].lo else 0) /
        (Fintype.card α : ℝ) := by
      rw [sum_div_const]
      apply Finset.sum_congr rfl
      intro i _
      simp [rectangleAccept, rectangleWeight, ite_div]
    _ = density a / (Fintype.card α : ℝ) := by
      rw [sum_interval_get (fun I => if I.lo < density a then I.hi - I.lo else 0),
        partition_acceptance_mass thresholds (density a) hm h0 h1]

theorem rectangle_acceptance_mass (thresholds : List ℝ) (density : α → ℝ)
    (hm : ∀ a, density a ∈ thresholds) (h0 : ∀ a, 0 ≤ density a)
    (h1 : ∀ a, density a ≤ 1) :
    eventMass (rectangleWeight thresholds) (rectangleAccept thresholds density) =
      (∑ a, density a) / (Fintype.card α : ℝ) := by
  unfold eventMass
  rw [Fintype.sum_prod_type]
  simp_rw [rectangle_row_mass thresholds density _ (hm _) (h0 _) (h1 _)]
  rw [sum_div_const]

omit [Fintype α] in theorem rectangle_and (thresholds : List ℝ) (p q : α → ℝ) :
    (fun seed => rectangleAccept thresholds p seed && rectangleAccept thresholds q seed) =
      rectangleAccept thresholds (fun a => min (p a) (q a)) := by
  funext seed
  simp [rectangleAccept]

theorem min_mem_thresholds (thresholds : List ℝ) {x y : ℝ} (hx : x ∈ thresholds)
    (hy : y ∈ thresholds) : min x y ∈ thresholds := by
  by_cases h : x ≤ y <;> simp [min_def, h, hx, hy]

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

def localSample (accept : σ → Bool) (decode : σ → α) (fallback : α)
    (proposals : List σ) : α :=
  ((firstAccepted accept proposals).map decode).getD fallback

end

end UniqueGamesTheorem.Foundations.CorrelatedSampling

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_ClauseVerifierLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceContexts

open Target

abbrev I (u : ℕ) := Fin u → Bool

@[simp] theorem card_I (u : ℕ) : Fintype.card (I u) = 2 ^ u := by simp [I]

end UniqueGamesTheorem.Foundations.Hastad.SourceContexts

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineLogCounter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
An actual logarithmic-round counter. Unary input is stripped to a raw tally;
each positive round emits one tally and halves the remaining input by pairing
symbols. The zero input emits one round explicitly. All tapes except the
canonical output are empty at termination.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineLogCounter

open Turing

def bitLength (n : Nat) : Nat := if n = 0 then 0 else n.log2 + 1

@[simp] theorem bitLength_zero : bitLength 0 = 0 := rfl

theorem bitLength_positive {n : Nat} (h : n ≠ 0) : bitLength n = n.log2 + 1 := by
  simp [bitLength, h]

def increments (n : Nat) (started : Bool) : Nat :=
  if n = 0 then (if started then 0 else 1) else bitLength n

@[simp] theorem increments_true (n : Nat) : increments n true = bitLength n := by
  by_cases hn : n = 0 <;> simp [increments, hn]

theorem increments_false (n : Nat) : increments n false = n.log2 + 1 := by
  by_cases hn : n = 0
  · subst n; rfl
  · simp [increments, bitLength, hn]

def coreTime (n : Nat) : Nat :=
  if h : n = 0 then 1 else n + n / 2 + 3 + coreTime (n / 2)
termination_by n
decreasing_by omega

@[simp] theorem coreTime_zero : coreTime 0 = 1 := by rw [coreTime]; rfl

theorem coreTime_positive {n : Nat} (h : n ≠ 0) :
    coreTime n = n + n / 2 + 3 + coreTime (n / 2) := by
  rw [coreTime, dite_eq_right h]

theorem coreTime_bound (n : Nat) : coreTime n ≤ 6 * n + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n; simp
    · rw [coreTime_positive hn]
      have smaller : n / 2 < n := by omega
      have bound := ih (n / 2) smaller
      omega

abbrev Alphabet (_ : Fin 3) := Bool
abbrev State := (Bool × Bool) × Option Bool

def initialState : State := ((false, false), none)

def rawTapes (input scratch output : List Bool) : Fin 3 → List Bool
  | 0 => input
  | 1 => scratch
  | 2 => output

theorem update_input (input scratch output replacement : List Bool) :
    Function.update (rawTapes input scratch output) 0 replacement = rawTapes replacement scratch output := by
  funext k
  fin_cases k <;> rfl

theorem update_scratch (input scratch output replacement : List Bool) :
    Function.update (rawTapes input scratch output) 1 replacement = rawTapes input replacement output := by
  funext k
  fin_cases k <;> rfl

theorem update_output (input scratch output replacement : List Bool) :
    Function.update (rawTapes input scratch output) 2 replacement = rawTapes input scratch replacement := by
  funext k
  fin_cases k <;> rfl

def stripLoop : TM2.Stmt Alphabet (Fin 5) State :=
  .pop 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.push 1 (fun _ => true) (.goto fun _ => (1 : Fin 5)))
      (.load (fun _ => initialState) (.goto fun _ => 4)))

def guardLoop : TM2.Stmt Alphabet (Fin 5) State :=
  .peek 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.push 2 (fun _ => true)
        (.load (fun _ => ((false, true), none)) (.goto fun _ => 3)))
      (.branch (fun state => state.1.2)
        (.load (fun _ => initialState) .halt)
        (.push 2 (fun _ => true) (.load (fun _ => initialState) .halt))))

def halfLoop : TM2.Stmt Alphabet (Fin 5) State :=
  .pop 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.branch (fun state => state.1.1)
        (.push 1 (fun _ => true)
          (.load (fun state => ((false, state.1.2), state.2)) (.goto fun _ => 3)))
        (.load (fun state => ((true, state.1.2), state.2)) (.goto fun _ => 3)))
      (.load (fun state => ((false, state.1.2), none)) (.goto fun _ => 4)))

def totalTime (n : Nat) : Nat := 2 * n + 3 + coreTime n

theorem totalTime_bound (n : Nat) : totalTime n ≤ 8 * n + 4 := by
  have bound := coreTime_bound n
  unfold totalTime
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachineLogCounter

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_GraphCounterModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed Boolean-stack program prepending the logarithmic round count to
a graph table. It copies the original word, adds its two unary header values,
runs the actual logarithm machine, then emits the counter and original word. -/

namespace UniqueGamesTheorem.Foundations.Complexity.GraphCounterModel

open Turing

inductive ExtraTape where
  | input | archive | scratch | output
  deriving DecidableEq

protected abbrev ExtraTape.enumList : List ExtraTape := [.input, .archive, .scratch, .output]

protected theorem ExtraTape.enumList_nodup : ExtraTape.enumList.Nodup := by decide

instance instFintypeExtraTape : Fintype ExtraTape where
  elems := ⟨ExtraTape.enumList, ExtraTape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive ExtraLabel where
  | copyFirst | copySecond | seed | headerFirst | headerSecond
  | clearInput | clockCopy | archiveCopy | finalReverse
  deriving DecidableEq

protected abbrev ExtraLabel.enumList : List ExtraLabel := [.copyFirst, .copySecond, .seed,
  .headerFirst, .headerSecond, .clearInput, .clockCopy, .archiveCopy, .finalReverse]

protected theorem ExtraLabel.enumList_nodup : ExtraLabel.enumList.Nodup := by decide

instance instFintypeExtraLabel : Fintype ExtraLabel where
  elems := ⟨ExtraLabel.enumList, ExtraLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape := Fin 3 ⊕ ExtraTape
abbrev Label := Fin 5 ⊕ ExtraLabel
abbrev Alphabet (_ : Tape) := Bool
abbrev State := MachineLogCounter.State × Option Bool

def initialState : State := (MachineLogCounter.initialState, none)

def clockLabel : Option (Fin 5) → Option Label
  | none => some (.inr .clearInput)
  | some l => some (.inl l)

/-- Homogeneous Boolean embedding of the fixed logarithm program. -/
def clockStatement : TM2.Stmt MachineLogCounter.Alphabet (Fin 5) MachineLogCounter.State →
    TM2.Stmt Alphabet Label State
  | .push k f next => .push (.inl k) (fun state => f state.1) (clockStatement next)
  | .peek k f next => .peek (.inl k) (fun state x => (f state.1 x, state.2)) (clockStatement next)
  | .pop k f next => .pop (.inl k) (fun state x => (f state.1 x, state.2)) (clockStatement next)
  | .load f next => .load (fun state => (f state.1, state.2)) (clockStatement next)
  | .branch f yes no => .branch (fun state => f state.1) (clockStatement yes) (clockStatement no)
  | .goto f => .goto (fun state => .inl (f state.1))
  | .halt => .goto (fun _ => .inr .clearInput)

def readHeader (again next : Label) : TM2.Stmt Alphabet Label State :=
  .pop (.inr .input) (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.push (.inl 0) (fun _ => true) (.goto fun _ => again))
      (.load (fun state => (state.1, none)) (.goto fun _ => next)))

def clockTapes (tapes : Fin 3 → List Bool) (extra : ExtraTape → List Bool) : Tape → List Bool
  | .inl k => tapes k
  | .inr k => extra k

def clockConfiguration (extra : ExtraTape → List Bool) (register : Option Bool)
    (c : TM2.Cfg MachineLogCounter.Alphabet (Fin 5) MachineLogCounter.State) :
    TM2.Cfg Alphabet Label State := ⟨clockLabel c.l, (c.var, register), clockTapes c.stk extra⟩

theorem clockTapes_update (tapes : Fin 3 → List Bool) (extra : ExtraTape → List Bool)
    (k : Fin 3) (word : List Bool) :
    clockTapes (Function.update tapes k word) extra =
      Function.update (clockTapes tapes extra) (.inl k) word := by
  funext tape
  cases tape <;> simp [clockTapes, Function.comp_def]

theorem clockStatement_simulation (extra : ExtraTape → List Bool) (register : Option Bool)
    (statement : TM2.Stmt MachineLogCounter.Alphabet (Fin 5) MachineLogCounter.State)
    (state : MachineLogCounter.State) (tapes : Fin 3 → List Bool) :
    TM2.stepAux (clockStatement statement) (state, register) (clockTapes tapes extra) =
      clockConfiguration extra register (TM2.stepAux statement state tapes) := by
  induction statement generalizing state tapes with
  | push k f next ih =>
      simp only [clockStatement, TM2.stepAux, clockTapes]
      rw [← clockTapes_update]
      exact ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
      simpa only [clockStatement, TM2.stepAux, clockTapes] using ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
      simp only [clockStatement, TM2.stepAux, clockTapes]
      rw [← clockTapes_update]
      exact ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih =>
      simpa only [clockStatement, TM2.stepAux] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
      cases h : f state with
      | false => simpa only [clockStatement, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
      | true => simpa only [clockStatement, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto f => rfl
  | halt => rfl

end UniqueGamesTheorem.Foundations.Complexity.GraphCounterModel

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_GraphCounterFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual cleanup and emission of the counter followed by the preserved graph. -/

namespace UniqueGamesTheorem.Foundations.Complexity.GraphCounterFinish

open Turing GraphCounterModel

def extraTapes (rest original : List Bool) : ExtraTape → List Bool
  | .input => rest
  | .archive => original
  | _ => []

def frame (input archive counter reversed output : List Bool) : Tape → List Bool
  | .inl i => if i = 2 then counter else []
  | .inr .input => input
  | .inr .archive => archive
  | .inr .scratch => reversed
  | .inr .output => output

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.Complexity.GraphCounterFinish

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_AssignmentTester
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

omit [Fintype A] [DecidableEq A] in
@[simp] theorem cubeXor_right_twice (f g : Cube A) :
    cubeXor (cubeXor f g) g = f := by
  funext a
  change ((f a ^^ g a) ^^ g a) = f a
  cases f a <;> cases g a <;> rfl

def flipAt (i : A) (f : Cube A) : Cube A :=
  fun j => if j = i then !(f j) else f j

omit [Fintype A] in
@[simp] theorem flipAt_twice (i : A) (f : Cube A) : flipAt i (flipAt i f) = f := by
  funext j
  by_cases h : j = i <;> simp [flipAt, h]

def cubeAnd (f g : Cube A) : Cube A := fun a => f a && g a

variable {K : Type*} [Fintype K] [Nonempty K]

/-- The actual six oracle addresses for each test. Unused slots repeat an
address already queried, so every event has the same fixed six-slot format. -/
def eventQueries (label : A → K → Bool) (kind : Fin 4) (k : K)
    (f g r₀ r₁ r₂ : Cube A) (slot : Fin 6) : K ⊕ Cube A :=
  if kind = 0 then
    if slot = 0 then .inr f else if slot = 1 then .inr g else .inr (cubeXor f g)
  else if kind = 1 then
    if slot = 0 then .inr r₀ else
    if slot = 1 then .inr (cubeXor r₀ (cubeAnd f g)) else
    if slot = 2 then .inr r₁ else
    if slot = 3 then .inr (cubeXor r₁ f) else
    if slot = 4 then .inr r₂ else .inr (cubeXor r₂ g)
  else if kind = 2 then
    if slot = 0 then .inr r₀ else .inr (cubeXor r₀ (fun _ => true))
  else
    if slot = 0 then .inl k else
    if slot = 1 then .inr r₀ else .inr (cubeXor r₀ (fun a => label a k))

def eventAccepts (kind : Fin 4) (b : Fin 6 → Bool) : Bool :=
  if kind = 0 then decide ((b 0 ^^ b 1) = b 2)
  else if kind = 1 then decide ((b 0 ^^ b 1) = ((b 2 ^^ b 3) && (b 4 ^^ b 5)))
  else if kind = 2 then (b 0 ^^ b 1)
  else decide (b 0 = (b 1 ^^ b 2))

end UniqueGamesTheorem.Foundations.PCP.AssignmentTester

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_CodeComposition
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

/-- The encoding is a literal coordinate read from a finite Boolean truth table. -/
def codeword {A : Type*} (a : A) : Cube A → Bool := fun x => x a

/-- Two equal-sized blocks, indexed by a side bit and a common coordinate. -/
def pairWord {X : Type*} (left right : X → Bool) : Bool × X → Bool :=
  fun p => if p.1 then right p.2 else left p.2

end UniqueGamesTheorem.Foundations.PCP.CodeComposition

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_AlphabetReductionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The explicit assignment tester applied to the encoded satisfying pairs of an
actual finite edge predicate.  The resulting soundness loss is independent of
the alphabet size.  Uniform padding of the finite sample space and assembly of
the global incidence graph are separate constructions.
-/

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetReduction

open UniqueGamesTheorem.Foundations.Hastad
open CodeComposition

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

abbrev LegalPair (accepts : A → A → Bool) :=
  {p : A × A // accepts p.1 p.2 = true}

abbrev InputCoordinate (A : Type*) := Bool × Cube A

def pairEncoding (accepts : A → A → Bool) (p : LegalPair accepts) :
    InputCoordinate A → Bool :=
  pairWord (codeword p.1.1) (codeword p.1.2)

end UniqueGamesTheorem.Foundations.PCP.AlphabetReduction

end

end

section

namespace UniqueGamesTheorem.Foundations.PCP

structure ConstraintGraph (V E A : Type*) where
  reverse : E ≃ E
  reverse_involutive : Function.Involutive reverse
  tail : E → V
  accepts : E → A → A → Bool
  reverse_accepts : ∀ e a b, accepts (reverse e) b a = accepts e a b

namespace ConstraintGraph

variable {V E A : Type*}

def head (G : ConstraintGraph V E A) (e : E) : V := G.tail (G.reverse e)

@[simp] theorem head_reverse (G : ConstraintGraph V E A) (e : E) :
    G.head (G.reverse e) = G.tail e := by
  simp only [head, G.reverse_involutive e]

def edgeSatisfied (G : ConstraintGraph V E A) (labeling : V → A) (e : E) : Bool :=
  G.accepts e (labeling (G.tail e)) (labeling (G.head e))

@[simp] theorem edgeSatisfied_reverse (G : ConstraintGraph V E A)
    (labeling : V → A) (e : E) :
    G.edgeSatisfied labeling (G.reverse e) = G.edgeSatisfied labeling e := by
  simpa only [edgeSatisfied, head, G.reverse_involutive e] using
    G.reverse_accepts e (labeling (G.tail e)) (labeling (G.tail (G.reverse e)))

def rejectedDarts [Fintype E] (G : ConstraintGraph V E A) (labeling : V → A) :
    Finset E := Finset.univ.filter (fun e => G.edgeSatisfied labeling e = false)

def rejectionCount [Fintype E] (G : ConstraintGraph V E A) (labeling : V → A) : Nat :=
  (G.rejectedDarts labeling).card

end ConstraintGraph

end UniqueGamesTheorem.Foundations.PCP

end

section

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.ConstraintGraph

variable {V E A : Type*}

section Reindex

variable {W D B : Type*}

/-- Explicit changes of vertex, dart, and label coordinates. -/
def reindex (G : ConstraintGraph V E A) (vertices : V ≃ W) (darts : E ≃ D)
    (labels : A ≃ B) : ConstraintGraph W D B where
  reverse := darts.symm.trans (G.reverse.trans darts)
  reverse_involutive := by
    intro d
    change darts (G.reverse (darts.symm (darts (G.reverse (darts.symm d))))) = d
    rw [darts.symm_apply_apply, G.reverse_involutive, darts.apply_symm_apply]
  tail := fun d => vertices (G.tail (darts.symm d))
  accepts := fun d a b => G.accepts (darts.symm d) (labels.symm a) (labels.symm b)
  reverse_accepts := by
    intro d a b
    simpa only [Equiv.trans_apply, darts.symm_apply_apply] using
      G.reverse_accepts (darts.symm d) (labels.symm a) (labels.symm b)

end Reindex

end UniqueGamesTheorem.Foundations.PCP.ConstraintGraph

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_GraphTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Executable directed-dart tables for the fixed 64-label alphabet

The header gives vertex and dart counts. Every dart has one ordered row:
tail index, reverse-dart index, and 4096 Boolean predicate entries. Entry
`b + 64 * a` is the predicate at labels `(a,b)`. All fields, including bits
as 0/1 words, use the existing zero-delimited unary natural-word codec.

The decoder checks all index bounds, row counts, predicate lengths, reverse
involution, predicate transpose, and absence of trailing fields. Directed rows
preserve loops, self-reversing darts, and repeated constraint occurrences.
The size theorems concern the full encoded table, not a machine runtime.
-/

namespace UniqueGamesTheorem.Foundations.PCP.GraphTables

open UniqueGamesTheorem.Foundations.Complexity

abbrev Label := Fin 64
abbrev RelationTable := Vector Bool 4096

/-- The fixed row-major ordering of the complete predicate table. -/
def relationIndex : Label × Label ≃ Fin 4096 := finProdFinEquiv

def relationAt (table : RelationTable) (a b : Label) : Bool :=
  table[relationIndex (a, b)]

def relationOf (predicate : Label → Label → Bool) : RelationTable :=
  Vector.ofFn (fun i => predicate (relationIndex.symm i).1 (relationIndex.symm i).2)

@[simp] theorem relationAt_relationOf (predicate : Label → Label → Bool) (a b : Label) :
    relationAt (relationOf predicate) a b = predicate a b := by
  simp [relationAt, relationOf]

/-- The row itself is finite data; index bounds are checked while parsing. -/
structure DartRow (vertices darts : Nat) where
  tail : Fin vertices
  reverseIndex : Fin darts
  relation : RelationTable

abbrev Rows (vertices darts : Nat) := Vector (DartRow vertices darts) darts

def reverseAt {n m : Nat} (rows : Rows n m) (e : Fin m) : Fin m :=
  rows[e].reverseIndex

def acceptsAt {n m : Nat} (rows : Rows n m) (e : Fin m) (a b : Label) : Bool :=
  relationAt rows[e].relation a b

/-- The two graph laws are decidable finite checks on the stored rows. -/
def Valid {n m : Nat} (rows : Rows n m) : Prop :=
  (∀ e, reverseAt rows (reverseAt rows e) = e) ∧
  (∀ e a b, acceptsAt rows (reverseAt rows e) b a = acceptsAt rows e a b)

instance instDecidableValid {n m : Nat} (rows : Rows n m) : Decidable (Valid rows) := by
  unfold Valid
  infer_instance

structure Table where
  vertices : Nat
  darts : Nat
  rows : Rows vertices darts
  valid : Valid rows

/-- The ordered list serialized by the codec. Equal rows remain separate. -/
def rowList (table : Table) : List (DartRow table.vertices table.darts) := table.rows.toList

@[simp] theorem rowList_length (table : Table) : (rowList table).length = table.darts := by
  simp [rowList]

/-- Decode validated finite data into the actual constraint-graph semantics. -/
def semantics (table : Table) : ConstraintGraph (Fin table.vertices) (Fin table.darts) Label where
  reverse :=
    { toFun := reverseAt table.rows
      invFun := reverseAt table.rows
      left_inv := table.valid.1
      right_inv := table.valid.1 }
  reverse_involutive := table.valid.1
  tail e := table.rows[e].tail
  accepts := acceptsAt table.rows
  reverse_accepts := table.valid.2

@[simp] theorem semantics_reverse (table : Table) (e : Fin table.darts) :
    (semantics table).reverse e = table.rows[e].reverseIndex := rfl

@[simp] theorem semantics_tail (table : Table) (e : Fin table.darts) :
    (semantics table).tail e = table.rows[e].tail := rfl

@[simp] theorem semantics_accepts (table : Table) (e : Fin table.darts) (a b : Label) :
    (semantics table).accepts e a b = relationAt table.rows[e].relation a b := rfl

def graphRows {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) Label) : Rows n m :=
  Vector.ofFn (fun e => ⟨G.tail e, G.reverse e, relationOf (G.accepts e)⟩)

@[simp] theorem reverseAt_graphRows {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) :
    reverseAt (graphRows G) e = G.reverse e := by
  simp [reverseAt, graphRows]

@[simp] theorem acceptsAt_graphRows {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) (a b : Label) :
    acceptsAt (graphRows G) e a b = G.accepts e a b := by
  simp [acceptsAt, graphRows]

theorem graphRows_valid {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) Label) :
    Valid (graphRows G) := by
  constructor
  · intro e
    simpa using G.reverse_involutive e
  · intro e a b
    simpa using G.reverse_accepts e a b

def ofGraph {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) Label) : Table :=
  ⟨n, m, graphRows G, graphRows_valid G⟩

@[simp] theorem semantics_ofGraph_reverse {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) :
    (semantics (ofGraph G)).reverse e = G.reverse e := by
  exact reverseAt_graphRows G e

@[simp] theorem semantics_ofGraph_tail {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) :
    (semantics (ofGraph G)).tail e = G.tail e := by
  change (graphRows G)[e.val].tail = G.tail e
  simp only [graphRows, Vector.getElem_ofFn]

@[simp] theorem semantics_ofGraph_accepts {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) (a b : Label) :
    (semantics (ofGraph G)).accepts e a b = G.accepts e a b := by
  exact acceptsAt_graphRows G e a b

@[simp] theorem semantics_ofGraph_edgeSatisfied {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (labeling : Fin n → Label) (e : Fin m) :
    (semantics (ofGraph G)).edgeSatisfied labeling e = G.edgeSatisfied labeling e := by
  simp [ConstraintGraph.edgeSatisfied, ConstraintGraph.head]

theorem constraintGraph_ext {V E A : Type*} {G H : ConstraintGraph V E A}
    (hr : ∀ e, G.reverse e = H.reverse e) (ht : G.tail = H.tail)
    (hp : G.accepts = H.accepts) : G = H := by
  cases G with
  | mk reverse hinv tail accepts htranspose =>
    cases H with
    | mk reverse' hinv' tail' accepts' htranspose' =>
      dsimp only at hr ht hp
      have he : reverse = reverse' := Equiv.ext hr
      cases he
      cases ht
      cases hp
      rfl

/-- Complete semantic graph roundtrip, including its actual reversal map. -/
@[simp] theorem semantics_ofGraph {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) : semantics (ofGraph G) = G := by
  apply constraintGraph_ext
  · exact semantics_ofGraph_reverse G
  · funext e
    exact semantics_ofGraph_tail G e
  · funext e a b
    exact semantics_ofGraph_accepts G e a b

@[simp] theorem semantics_ofGraph_rejectionCount {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (labeling : Fin n → Label) :
    (semantics (ofGraph G)).rejectionCount labeling = G.rejectionCount labeling := by
  rw [semantics_ofGraph]
  rfl

/-- Explicit enumerations determine every vertex name, dart position, and
predicate label. No hidden choice of a graph representation is made. -/
def enumeratedGraph {V E A : Type*} {n m : Nat} (G : ConstraintGraph V E A)
    (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m) (labelOrder : A ≃ Label) :
    ConstraintGraph (Fin n) (Fin m) Label where
  reverse := (dartOrder.symm.trans G.reverse).trans dartOrder
  reverse_involutive e := by
    change dartOrder (G.reverse (dartOrder.symm
      (dartOrder (G.reverse (dartOrder.symm e))))) = e
    rw [dartOrder.symm_apply_apply, G.reverse_involutive, dartOrder.apply_symm_apply]
  tail e := vertexOrder (G.tail (dartOrder.symm e))
  accepts e a b := G.accepts (dartOrder.symm e) (labelOrder.symm a) (labelOrder.symm b)
  reverse_accepts e a b := by
    change G.accepts (dartOrder.symm (dartOrder (G.reverse (dartOrder.symm e))))
      (labelOrder.symm b) (labelOrder.symm a) = _
    rw [dartOrder.symm_apply_apply]
    exact G.reverse_accepts _ _ _

def ofEnumeratedGraph {V E A : Type*} {n m : Nat} (G : ConstraintGraph V E A)
    (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m) (labelOrder : A ≃ Label) : Table :=
  ofGraph (enumeratedGraph G vertexOrder dartOrder labelOrder)

def bitWord (b : Bool) : Nat := if b then 1 else 0

def parseBit : Nat → Option Bool
  | 0 => some false
  | 1 => some true
  | _ => none

@[simp] theorem parseBit_bitWord (b : Bool) : parseBit (bitWord b) = some b := by
  cases b <;> rfl

@[simp] theorem parseBits_bitWords (bits : List Bool) :
    (bits.map bitWord).mapM parseBit = some bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [ih]

def relationWords (relation : RelationTable) : List Nat := relation.toList.map bitWord

@[simp] theorem relationWords_length (relation : RelationTable) :
    (relationWords relation).length = 4096 := by simp [relationWords]

def parseRelation (words : List Nat) : Option RelationTable := do
  let bits ← words.mapM parseBit
  if length_ok : bits.length = 4096 then
    some ⟨bits.toArray, by simpa using length_ok⟩
  else none

@[simp] theorem parseRelation_encoded (relation : RelationTable) :
    parseRelation (relationWords relation) = some relation := by
  unfold parseRelation relationWords
  rw [parseBits_bitWords]
  simp
  exact Vector.toArray_toList

def rowWords {n m : Nat} (row : DartRow n m) : List Nat :=
  [row.tail.val, row.reverseIndex.val] ++ relationWords row.relation

end UniqueGamesTheorem.Foundations.PCP.GraphTables

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_GenericGraphTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Executable directed graph tables over a fixed finite alphabet

The alphabet size `q` is fixed by the encoding, not encoded as a variable input
field. The header stores vertex and directed-dart counts. Each ordered dart row
stores its tail, reverse index, and every `q*q` predicate bit in order `b+q*a`.
All fields use the existing unary natural-word codec. Decoding validates graph
laws and preserves loops and repeated darts. Size bounds count the complete
serialized table and make no running-time assertion.
-/

namespace UniqueGamesTheorem.Foundations.PCP.GenericGraphTables

open UniqueGamesTheorem.Foundations.Complexity

abbrev Label (q : Nat) := Fin q
abbrev RelationTable (q : Nat) := Vector Bool (q * q)

variable {q : Nat}

/-- The fixed row-major ordering of the complete predicate table. -/
def relationIndex (q : Nat) : (Label q) × (Label q) ≃ Fin (q * q) := finProdFinEquiv

def relationAt (table : (RelationTable q)) (a b : (Label q)) : Bool :=
  table[(relationIndex q) (a, b)]

def relationOf (predicate : (Label q) → (Label q) → Bool) : (RelationTable q) :=
  Vector.ofFn (fun i => predicate ((relationIndex q).symm i).1 ((relationIndex q).symm i).2)

@[simp] theorem relationAt_relationOf (predicate : (Label q) → (Label q) → Bool) (a b : (Label q)) :
    relationAt (relationOf predicate) a b = predicate a b := by
  simp [relationAt, relationOf]

/-- The row itself is finite data; index bounds are checked while parsing. -/
structure DartRow (q vertices darts : Nat) where
  tail : Fin vertices
  reverseIndex : Fin darts
  relation : (RelationTable q)

abbrev Rows (q vertices darts : Nat) := Vector (DartRow q vertices darts) darts

def reverseAt {n m : Nat} (rows : Rows q n m) (e : Fin m) : Fin m :=
  rows[e].reverseIndex

def acceptsAt {n m : Nat} (rows : Rows q n m) (e : Fin m) (a b : (Label q)) : Bool :=
  relationAt rows[e].relation a b

/-- The two graph laws are decidable finite checks on the stored rows. -/
def Valid {n m : Nat} (rows : Rows q n m) : Prop :=
  (∀ e, reverseAt rows (reverseAt rows e) = e) ∧
  (∀ e a b, acceptsAt rows (reverseAt rows e) b a = acceptsAt rows e a b)

structure Table (q : Nat) where
  vertices : Nat
  darts : Nat
  rows : Rows q vertices darts
  valid : Valid rows

/-- The ordered list serialized by the codec. Equal rows remain separate. -/
def rowList (table : (Table q)) : List (DartRow q table.vertices table.darts) := table.rows.toList

@[simp] theorem rowList_length (table : (Table q)) : (rowList table).length = table.darts := by
  simp [rowList]

/-- Decode validated finite data into the actual constraint-graph semantics. -/
def semantics (table : (Table q)) : ConstraintGraph (Fin table.vertices) (Fin table.darts) (Label q) where
  reverse :=
    { toFun := reverseAt table.rows
      invFun := reverseAt table.rows
      left_inv := table.valid.1
      right_inv := table.valid.1 }
  reverse_involutive := table.valid.1
  tail e := table.rows[e].tail
  accepts := acceptsAt table.rows
  reverse_accepts := table.valid.2

@[simp] theorem semantics_reverse (table : (Table q)) (e : Fin table.darts) :
    (semantics table).reverse e = table.rows[e].reverseIndex := rfl

@[simp] theorem semantics_tail (table : (Table q)) (e : Fin table.darts) :
    (semantics table).tail e = table.rows[e].tail := rfl

@[simp] theorem semantics_accepts (table : (Table q)) (e : Fin table.darts) (a b : (Label q)) :
    (semantics table).accepts e a b = relationAt table.rows[e].relation a b := rfl

def graphRows {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) (Label q)) : Rows q n m :=
  Vector.ofFn (fun e => ⟨G.tail e, G.reverse e, relationOf (G.accepts e)⟩)

@[simp] theorem reverseAt_graphRows {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) :
    reverseAt (graphRows G) e = G.reverse e := by
  simp [reverseAt, graphRows]

@[simp] theorem acceptsAt_graphRows {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) (a b : (Label q)) :
    acceptsAt (graphRows G) e a b = G.accepts e a b := by
  simp [acceptsAt, graphRows]

theorem graphRows_valid {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) (Label q)) :
    Valid (graphRows G) := by
  constructor
  · intro e
    simpa using G.reverse_involutive e
  · intro e a b
    simpa using G.reverse_accepts e a b

def ofGraph {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) (Label q)) : (Table q) :=
  ⟨n, m, graphRows G, graphRows_valid G⟩

@[simp] theorem semantics_ofGraph_reverse {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) :
    (semantics (ofGraph G)).reverse e = G.reverse e := by
  exact reverseAt_graphRows G e

@[simp] theorem semantics_ofGraph_tail {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) :
    (semantics (ofGraph G)).tail e = G.tail e := by
  change (graphRows G)[e.val].tail = G.tail e
  simp only [graphRows, Vector.getElem_ofFn]

@[simp] theorem semantics_ofGraph_accepts {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) (a b : (Label q)) :
    (semantics (ofGraph G)).accepts e a b = G.accepts e a b := by
  exact acceptsAt_graphRows G e a b

@[simp] theorem semantics_ofGraph_edgeSatisfied {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (labeling : Fin n → (Label q)) (e : Fin m) :
    (semantics (ofGraph G)).edgeSatisfied labeling e = G.edgeSatisfied labeling e := by
  simp [ConstraintGraph.edgeSatisfied, ConstraintGraph.head]

theorem constraintGraph_ext {V E A : Type*} {G H : ConstraintGraph V E A}
    (hr : ∀ e, G.reverse e = H.reverse e) (ht : G.tail = H.tail)
    (hp : G.accepts = H.accepts) : G = H := by
  cases G with
  | mk reverse hinv tail accepts htranspose =>
    cases H with
    | mk reverse' hinv' tail' accepts' htranspose' =>
      dsimp only at hr ht hp
      have he : reverse = reverse' := Equiv.ext hr
      cases he
      cases ht
      cases hp
      rfl

/-- Complete semantic graph roundtrip, including its actual reversal map. -/
@[simp] theorem semantics_ofGraph {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) : semantics (ofGraph G) = G := by
  apply constraintGraph_ext
  · exact semantics_ofGraph_reverse G
  · funext e
    exact semantics_ofGraph_tail G e
  · funext e a b
    exact semantics_ofGraph_accepts G e a b

@[simp] theorem semantics_ofGraph_rejectionCount {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (labeling : Fin n → (Label q)) :
    (semantics (ofGraph G)).rejectionCount labeling = G.rejectionCount labeling := by
  rw [semantics_ofGraph]
  rfl

/-- Explicit enumerations determine every vertex name, dart position, and
predicate label. No hidden choice of a graph representation is made. -/
def enumeratedGraph {V E A : Type*} {n m : Nat} (G : ConstraintGraph V E A)
    (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m) (labelOrder : A ≃ (Label q)) :
    ConstraintGraph (Fin n) (Fin m) (Label q) where
  reverse := (dartOrder.symm.trans G.reverse).trans dartOrder
  reverse_involutive e := by
    change dartOrder (G.reverse (dartOrder.symm
      (dartOrder (G.reverse (dartOrder.symm e))))) = e
    rw [dartOrder.symm_apply_apply, G.reverse_involutive, dartOrder.apply_symm_apply]
  tail e := vertexOrder (G.tail (dartOrder.symm e))
  accepts e a b := G.accepts (dartOrder.symm e) (labelOrder.symm a) (labelOrder.symm b)
  reverse_accepts e a b := by
    change G.accepts (dartOrder.symm (dartOrder (G.reverse (dartOrder.symm e))))
      (labelOrder.symm b) (labelOrder.symm a) = _
    rw [dartOrder.symm_apply_apply]
    exact G.reverse_accepts _ _ _

def ofEnumeratedGraph {V E A : Type*} {n m : Nat} (G : ConstraintGraph V E A)
    (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m) (labelOrder : A ≃ (Label q)) : (Table q) :=
  ofGraph (enumeratedGraph G vertexOrder dartOrder labelOrder)

def bitWord (b : Bool) : Nat := if b then 1 else 0

def relationWords (relation : (RelationTable q)) : List Nat := relation.toList.map bitWord

@[simp] theorem relationWords_length (relation : (RelationTable q)) :
    (relationWords relation).length = (q * q) := by simp [relationWords]

def rowWords {n m : Nat} (row : DartRow q n m) : List Nat :=
  [row.tail.val, row.reverseIndex.val] ++ relationWords row.relation

def tableWords (table : (Table q)) : List Nat :=
  [table.vertices, table.darts] ++ (rowList table).flatMap rowWords

@[simp] theorem rowWords_length {n m : Nat} (row : DartRow q n m) :
    (rowWords row).length = (q * q + 2) := by
  simp only [rowWords, List.length_append, List.length_cons, List.length_nil,
    relationWords_length]
  omega

end UniqueGamesTheorem.Foundations.PCP.GenericGraphTables

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_InputLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Serialization boundaries and direct row lookup for the shared executable
fixed-alphabet graph codec. The alphabet is a fixed parameter. Rows remain in
their stored order, including repeated darts and loops. Word offsets are fixed;
bit offsets are represented by actual encoded prefixes because unary fields
have data-dependent lengths. These are data identities, not runtime certificates.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Input

open UniqueGamesTheorem.Foundations.Complexity

export GenericGraphTables (Label RelationTable DartRow Rows Valid Table
  relationIndex relationAt relationOf relationAt_relationOf
  reverseAt acceptsAt rowList rowList_length semantics semantics_reverse
  semantics_tail semantics_accepts ofGraph semantics_ofGraph ofEnumeratedGraph
  bitWord relationWords relationWords_length rowWords rowWords_length
  tableWords )

variable {q n m : Nat}

/-- Exact decomposition before, at, and after a selected stored row. -/
theorem rowsWords_split (rows : List (DartRow q n m)) (e : Nat)
    (he : e < rows.length) :
    rows.flatMap rowWords = (rows.take e).flatMap rowWords ++
      (rowWords rows[e] ++ (rows.drop (e + 1)).flatMap rowWords) := by
  have hs : rows.take e ++ rows[e] :: rows.drop (e + 1) = rows := by
    rw [List.getElem_cons_drop he, List.take_append_drop]
  have hw := congrArg (fun rs : List (DartRow q n m) => rs.flatMap rowWords) hs
  simpa only [List.flatMap_append, List.flatMap_cons, List.append_assoc] using hw.symm

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Input

end

section

/-!
An actual fixed-alphabet TM2 parser for the complete Boolean relation table.
The finite syntax contains one slot reader for each of the `q*q` coordinates.
Each reader consumes `[false]` or `[true,false]`, stores the bit, and clears the
head register. No parser outcome or execution trace is an assumption.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.ReadRelation

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K] {q : Nat}

/-- The relation register is a finite tuple of bits, with no unbounded storage. -/
def relationEquiv (q : Nat) : RelationTable q ≃ (Fin (q * q) → Bool) where
  toFun relation i := relation[i.val]
  invFun := Vector.ofFn
  left_inv relation := Vector.ofFn_getElem
  right_inv bits := by funext i; simp

/-- Executable enumeration used when assembling the finite machine state. -/
@[instance_reducible] def relationFintype (q : Nat) : Fintype (RelationTable q) :=
  Fintype.ofEquiv (Fin (q * q) → Bool) (relationEquiv q).symm

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.ReadRelation

end

section

/-!
Concrete bridges between graph cardinality and the length of the validated
unary table encoding. These bounds supply the input-length and intermediate
encoding estimates used by actual machine trace composition; they are not
themselves a machine execution certificate.
-/

namespace UniqueGamesTheorem.Foundations.PCP.GraphTableComplexity

open UniqueGamesTheorem.Foundations.Complexity
open Polynomial

noncomputable def encodingPolynomial (q : Nat) : Polynomial Nat :=
  X ^ 2 + C (2 * (q * q) + 1) * X + C 2

theorem encodingPolynomial_eval (q n : Nat) :
    (encodingPolynomial q).eval n = n ^ 2 + (2 * (q * q) + 1) * n + 2 := by
  simp [encodingPolynomial]

theorem encodingPolynomial_mono (q : Nat) {n m : Nat} (hnm : n ≤ m) :
    (encodingPolynomial q).eval n ≤ (encodingPolynomial q).eval m := by
  rw [encodingPolynomial_eval, encodingPolynomial_eval]
  exact Nat.add_le_add_right
    (Nat.add_le_add (Nat.pow_le_pow_left hnm 2) (Nat.mul_le_mul_left _ hnm)) 2

theorem rowBound_le_polynomial (q vertices darts : Nat) :
    vertices + darts + 2 + darts * (vertices + darts + 2 * (q * q)) ≤
      (encodingPolynomial q).eval (vertices + darts) := by
  have hd : darts ≤ vertices + darts := Nat.le_add_left darts vertices
  calc
    _ ≤ vertices + darts + 2 +
        (vertices + darts) * (vertices + darts + 2 * (q * q)) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hd) _
    _ = _ := by rw [encodingPolynomial_eval]; ring

end UniqueGamesTheorem.Foundations.PCP.GraphTableComplexity

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_GraphCounterStartLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual archive-copy and unary-header addition before the embedded logarithm
machine. The two header values stay on tapes; they never enter finite control. -/

namespace UniqueGamesTheorem.Foundations.Complexity.GraphCounterModel

open Turing

def startExtra (input archive : List Bool) : ExtraTape → List Bool
  | .input => input
  | .archive => archive
  | _ => []

def startMemory (input archive sum : List Bool) : Tape → List Bool
  | .inl k => if k = 0 then sum else []
  | .inr k => startExtra input archive k

theorem startMemory_input_update (input archive sum replacement : List Bool) :
    Function.update (startMemory input archive sum) (.inr .input) replacement =
      startMemory replacement archive sum := by
  funext tape
  cases tape with
  | inl k => simp [startMemory]
  | inr k => cases k <;> simp [startMemory, startExtra]

theorem startMemory_sum_update (input archive sum replacement : List Bool) :
    Function.update (startMemory input archive sum) (.inl 0) replacement =
      startMemory input archive replacement := by
  funext tape
  cases tape with
  | inl k => by_cases h : k = 0 <;> simp [startMemory, h]
  | inr k => simp [startMemory]

end UniqueGamesTheorem.Foundations.Complexity.GraphCounterModel

/-! A complete finite machine adding the actual logarithmic graph-round count
as a unary prefix, preserving every bit of the original validated graph table. -/

/-! Generic placement of the odometer-digit initialization used in
`Hastad.SourceLoopInit`. This extracts its seed/copy/trim scheme from the
formula/header parser: the actual checked copy loop preserves the radix and
scratch, and a single positive-unary pop leaves the remaining count.
The finite program depends on the fixed digit width, not on the radix value. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineOdometerInit
open Turing

inductive Tape (k : Nat)
  | radix | scratch | current (j : Fin k) | remaining (j : Fin k)
  deriving DecidableEq, Fintype

inductive Label (k : Nat)
  | seed (j : Fin k) | copyOut (j : Fin k) | copyBack (j : Fin k) | trim (j : Fin k)
  | done
  deriving DecidableEq, Fintype

variable {k : Nat} {K Λ σ : Type} [DecidableEq K]

def labelAt (labels : Label k → Λ) (r : Nat) : Λ :=
  if h : r < k then labels (.seed ⟨r,h⟩) else labels .done

end UniqueGamesTheorem.Foundations.Complexity.MachineOdometerInit

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegisterEmit

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

end UniqueGamesTheorem.Foundations.Complexity.MachineRegisterEmit

/-!
A concrete sequential composition of two finite TM2 programs. The first output
is transferred to a temporary stack and then to the second input. Both loops
execute actual transitions and reset their shared register on exit. Static
renaming changes neither a stack word nor the number of executed transitions.
-/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRepeat
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

inductive ExtraTape
  | counter | temporary | output
  deriving DecidableEq

protected abbrev ExtraTape.enumList : List ExtraTape := [.counter, .temporary, .output]

protected theorem ExtraTape.enumList_nodup : ExtraTape.enumList.Nodup := by decide

instance instFintypeExtraTape : Fintype ExtraTape where
  elems := ⟨ExtraTape.enumList, ExtraTape.enumList_nodup⟩
  complete x := by cases x <;> decide
inductive Phase
  | parse | guard | bodyToTemp | tempToBody | finalToTemp | tempToOutput
  deriving DecidableEq

protected abbrev Phase.enumList : List Phase := [.parse, .guard, .bodyToTemp, .tempToBody,
  .finalToTemp, .tempToOutput]

protected theorem Phase.enumList_nodup : Phase.enumList.Nodup := by decide

instance instFintypePhase : Fintype Phase where
  elems := ⟨Phase.enumList, Phase.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape (M : FinTM2) := M.K ⊕ ExtraTape
abbrev Label (M : FinTM2) := M.Λ ⊕ Phase
abbrev State (M : FinTM2) := M.σ × Option (M.Γ M.k₀)

def extraTapes (M : FinTM2) (counter temporary output : List (M.Γ M.k₀)) :
    ExtraTape → List (M.Γ M.k₀)
  | .counter => counter
  | .temporary => temporary
  | .output => output

end UniqueGamesTheorem.Foundations.Complexity.MachineRepeat

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineFiniteAlphabet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finiteness of every alphabet of the actual machines used by the reduction.
`FinTM2` already bundles finitely many tapes, control labels and register states,
but its alphabet field only requires the input tape alphabet to be finite.
This additional property is preserved by the actual sequential and repetition
constructors; it does not replace or alter their execution certificates.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet

open Turing

/-! Every physical tape has a finite alphabet. Together with `M.kFin`, this
also makes the disjoint union of all physical tape alphabets finite. -/

theorem of_homogeneous (M : FinTM2) {α : Type} [Finite α]
    (alphabet : ∀ k, M.Γ k = α) : FiniteAlphabet M := by
  intro k
  rw [alphabet k]
  infer_instance

/-- All concrete Boolean-stack machines satisfy the stronger alphabet condition. -/
theorem of_bool (M : FinTM2) (alphabet : ∀ k, M.Γ k = Bool) : FiniteAlphabet M :=
  of_homogeneous M alphabet

end UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_ProductTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Explicit numbered permutation-table outputs for bipartite graphs and products.
All numbering maps are supplied as actual equivalences; the product uses the
computable radix equivalence with division/remainder inverse, never an arbitrary
finite-type enumeration. The value bridge preserves every list occurrence.
-/

namespace UniqueGamesTheorem.Explicit.ProductTarget

open UniqueGamesTheorem.Foundations
open Target
open MachineOutputContract
open scoped BigOperators

variable {L R E : Type*} {q N M : ℕ}

section Value

variable [Fintype E]

def mergeLabelings (vertices : (L ⊕ R) ≃ Fin N)
    (left : L → Fin q) (right : R → Fin q) : Fin N → Fin q :=
  fun v => Sum.elim left right (vertices.symm v)

@[simp] theorem mergeLabelings_left (vertices : (L ⊕ R) ≃ Fin N)
    (left : L → Fin q) (right : R → Fin q) (x : L) :
    mergeLabelings vertices left right (vertices (Sum.inl x)) = left x := by
  simp [mergeLabelings]

@[simp] theorem mergeLabelings_right (vertices : (L ⊕ R) ≃ Fin N)
    (left : L → Fin q) (right : R → Fin q) (y : R) :
    mergeLabelings vertices left right (vertices (Sum.inr y)) = right y := by
  simp [mergeLabelings]

end Value

/-- The explicit address and `ofDigits` share the same least-significant-first
coordinate order, with no restriction on the radix beyond the digit type. -/
theorem address_eq_ofDigits {n t : ℕ} (f : Fin t → Fin n) :
    (finFunctionFinEquiv f : ℕ) = Nat.ofDigits n (List.ofFn (fun i => (f i : ℕ))) := by
  have hmap :
      (List.ofFn (fun i => (f i : ℕ))).mapIdx (fun i a => a * n ^ i) =
        List.ofFn (fun i : Fin t => (f i : ℕ) * n ^ (i : ℕ)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  rw [finFunctionFinEquiv_apply, Nat.ofDigits_eq_sum_mapIdx, hmap, List.sum_ofFn]

/-- A forward Horner controller reads the coordinate words in reverse order.
This is a word-order identity, separate from its machine execution theorem. -/
theorem address_eq_horner {n t : ℕ} (f : Fin t → Fin n) :
    (finFunctionFinEquiv f : ℕ) =
      (List.ofFn (fun i => (f i : ℕ))).reverse.foldl
        (fun acc digit => n * acc + digit) 0 := by
  rw [address_eq_ofDigits, Nat.ofDigits_eq_foldr, List.foldl_reverse]
  simp only [Nat.cast_id, Nat.add_comm]

end UniqueGamesTheorem.Explicit.ProductTarget

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Repetition_AnalyticCheegerLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finite threshold-overlap estimates used in the Dinur--Steurer argument.
These statements are numerical inequalities, not parallel-repetition premises.
The Boolean gate keeps the constraint predicate inside the overlap energy.
Weights need not be normalized: a finite auxiliary measure is permitted.
-/

namespace UniqueGamesTheorem.Repetition.Analytic

open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι]

def quadraticMass (w f g : ι → ℝ) : ℝ :=
  ∑ i, w i * ((f i) ^ 2 + (g i) ^ 2) / 2

def gatedCorrelation (w f g : ι → ℝ) (gate : ι → Bool) : ℝ :=
  ∑ i, if gate i then w i * f i * g i else 0

def gatedMinimum (w f g : ι → ℝ) (gate : ι → Bool) : ℝ :=
  ∑ i, if gate i then w i * min ((f i) ^ 2) ((g i) ^ 2) else 0

def gatedMaximum (w f g : ι → ℝ) (gate : ι → Bool) : ℝ :=
  ∑ i, if gate i then w i * max ((f i) ^ 2) ((g i) ^ 2) else 0

theorem gatedCorrelation_nonnegative (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    0 ≤ gatedCorrelation w f g gate := by
  apply Finset.sum_nonneg
  intro i _
  split
  · exact mul_nonneg (mul_nonneg (hw i) (hf i)) (hg i)
  · exact le_rfl

theorem gatedCorrelation_le_mass (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) : gatedCorrelation w f g gate ≤ quadraticMass w f g := by
  apply Finset.sum_le_sum
  intro i _
  split
  · have hfg : f i * g i ≤ ((f i) ^ 2 + (g i) ^ 2) / 2 := by
      nlinarith [sq_nonneg (f i - g i)]
    simpa only [← mul_assoc, mul_div_assoc] using mul_le_mul_of_nonneg_left hfg (hw i)
  · exact div_nonneg (mul_nonneg (hw i) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
      (by norm_num)

theorem gatedMinimum_nonnegative (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) : 0 ≤ gatedMinimum w f g gate := by
  apply Finset.sum_nonneg
  intro i _
  split
  · exact mul_nonneg (hw i) (le_min (sq_nonneg _) (sq_nonneg _))
  · exact le_rfl

theorem gatedMinimum_add_maximum_le (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) :
    gatedMinimum w f g gate + gatedMaximum w f g gate ≤ 2 * quadraticMass w f g := by
  unfold gatedMinimum gatedMaximum quadraticMass
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : gate i = true
  · simp only [hi, ↓reduceIte]
    have h := min_add_max ((f i) ^ 2) ((g i) ^ 2)
    rw [← mul_add, h]
    ring_nf
    exact le_rfl
  · simp only [hi, Bool.false_eq_true, ↓reduceIte, zero_add]
    have := hw i
    positivity

/-- A gated finite Cauchy--Schwarz estimate. This is the algebraic heart of
the threshold-rounding inequality, with no independence assumption. -/
theorem gatedCorrelation_sq_le_min_mul_max (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) :
    gatedCorrelation w f g gate ^ 2 ≤
      gatedMinimum w f g gate * gatedMaximum w f g gate := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i _
    split
    · exact mul_nonneg (hw i) (le_min (sq_nonneg _) (sq_nonneg _))
    · exact le_rfl
  · intro i _
    split
    · exact mul_nonneg (hw i) ((sq_nonneg (f i)).trans (le_max_left _ _))
    · exact le_rfl
  · intro i _
    by_cases hi : gate i = true
    · simp only [hi, ↓reduceIte]
      rcases le_total ((f i) ^ 2) ((g i) ^ 2) with h | h
      · rw [min_eq_left h, max_eq_right h]
        ring_nf
        exact le_rfl
      · rw [min_eq_right h, max_eq_left h]
        ring_nf
        exact le_rfl
    · simp [hi]

theorem gatedCorrelation_sq_le_min_quadratic (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) :
    gatedCorrelation w f g gate ^ 2 ≤
      gatedMinimum w f g gate *
        (2 * quadraticMass w f g - gatedMinimum w f g gate) := by
  have hmax := gatedMinimum_add_maximum_le w f g gate hw
  have hmin := gatedMinimum_nonnegative w f g gate hw
  exact (gatedCorrelation_sq_le_min_mul_max w f g gate hw).trans
    (mul_le_mul_of_nonneg_left (by linarith) hmin)

/-- The near-perfect form suffices for alphabet-independent repetition.
The total squared mass may be at most one, rather than exactly one. -/
theorem gatedMinimum_near_one (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) {η : ℝ} (hη : 0 ≤ η) (hη₁ : η ≤ 1)
    (hmass : quadraticMass w f g ≤ 1)
    (hcorrelation : 1 - η ≤ gatedCorrelation w f g gate) :
    1 - Real.sqrt (2 * η) ≤ gatedMinimum w f g gate := by
  have hmin := gatedMinimum_nonnegative w f g gate hw
  have h := gatedCorrelation_sq_le_min_quadratic w f g gate hw
  have hcorr : 0 ≤ gatedCorrelation w f g gate := by linarith
  have hsqcorr : (1 - η) ^ 2 ≤ gatedCorrelation w f g gate ^ 2 := by
    nlinarith
  have hupper : gatedMinimum w f g gate *
      (2 * quadraticMass w f g - gatedMinimum w f g gate) ≤
      gatedMinimum w f g gate * (2 - gatedMinimum w f g gate) := by
    apply mul_le_mul_of_nonneg_left _ hmin
    linarith
  have hsq : (1 - gatedMinimum w f g gate) ^ 2 ≤ 2 * η := by
    nlinarith [sq_nonneg η]
  have hsqrt := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hη)
  nlinarith [Real.sqrt_nonneg (2 * η)]

/-- Unit-mass form for the joint question-pair and auxiliary-coordinate law. -/
theorem gatedMinimum_unit_mass (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hmass : quadraticMass w f g = 1) :
    1 - Real.sqrt (2 * (1 - gatedCorrelation w f g gate)) ≤
      gatedMinimum w f g gate := by
  have hc₀ := gatedCorrelation_nonnegative w f g gate hw hf hg
  have hc₁ := gatedCorrelation_le_mass w f g gate hw
  rw [hmass] at hc₁
  apply gatedMinimum_near_one w f g gate hw
  · linarith
  · linarith
  · exact hmass.le
  · linarith

end
end UniqueGamesTheorem.Repetition.Analytic

end

section

/-!
Scalar parameter selection for the v2 repetition rate.

These results concern powers of real numbers only. In particular, they do not
assert a parallel-repetition theorem for games. The exponent depends only on
the gap and the desired error; no alphabet or logical dimension occurs here.
-/

namespace UniqueGamesTheorem.Repetition

/-- The scalar rate appearing in the alphabet-independent repetition estimate. -/
noncomputable def dsRate (gap : ℝ) : ℝ := 1 - gap ^ 2 / 16

theorem dsRate_nonneg {gap : ℝ} (hgap₀ : 0 ≤ gap) (hgap₁ : gap ≤ 1) :
    0 ≤ dsRate gap := by
  dsimp [dsRate]
  nlinarith

end UniqueGamesTheorem.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Repetition_AnalyticRateLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Repetition

theorem sequence_le_power {r : ℝ} (hr : 0 ≤ r) (c : ℕ → ℝ)
    (hzero : c 0 ≤ 1) (hstep : ∀ n, c (n + 1) ≤ r * c n) :
    ∀ n, c n ≤ r ^ n := by
  intro n
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
      calc
        c (n + 1) ≤ r * c n := hstep n
        _ ≤ r * r ^ n := mul_le_mul_of_nonneg_left ih hr
        _ = r ^ (n + 1) := by rw [pow_succ, mul_comm]

theorem squared_rate_le_dsRate_sq {gap : ℝ}
    (_hgap₀ : 0 ≤ gap) (_hgap₁ : gap ≤ 1) :
    1 - gap ^ 2 / 8 ≤ dsRate gap ^ 2 := by
  dsimp [dsRate]
  nlinarith only [sq_nonneg (gap ^ 2)]

theorem rate_of_squared_collision_recurrence {gap : ℝ}
    (hgap₀ : 0 ≤ gap) (hgap₁ : gap ≤ 1)
    (c v : ℕ → ℝ) (hzero : c 0 ≤ 1)
    (hstep : ∀ n, c (n + 1) ≤ (1 - gap ^ 2 / 8) * c n)
    (hvalue : ∀ n, v n ^ 2 ≤ c n) :
    ∀ n, v n ≤ dsRate gap ^ n := by
  have hr : 0 ≤ 1 - gap ^ 2 / 8 := by nlinarith
  have hpow := sequence_le_power hr c hzero hstep
  intro n
  apply le_of_sq_le_sq _ (pow_nonneg (dsRate_nonneg hgap₀ hgap₁) n)
  calc
    v n ^ 2 ≤ c n := hvalue n
    _ ≤ (1 - gap ^ 2 / 8) ^ n := hpow n
    _ ≤ (dsRate gap ^ 2) ^ n :=
      pow_le_pow_left₀ hr (squared_rate_le_dsRate_sq hgap₀ hgap₁) n
    _ = (dsRate gap ^ n) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

end UniqueGamesTheorem.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_ProductLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
The independent graph product in the last step of the reduction.

Edges are tuples of actual base edges.  The endpoint maps remain injective,
the edge law is exactly uniform, and the associated game agrees with ordinary
parallel repetition for every pair of local strategies, including strategies
depending on their whole question tuples.  Only the completeness lower bound
uses coordinatewise strategies; no repetition soundness bound is assumed here.
-/

/-!
The actual ordered full-table instance of the final independent product.
Caller-supplied coordinate numberings are used explicitly. Edges are emitted in
increasing mixed-radix address, with division/remainder decoding; the two vertex
blocks and the entire permutation table use the same coordinate convention.
-/

/-!
Machine-friendly product numbering on the common global vertex base.
Both endpoints use the same radix, so the machine needs neither a right-side
subtraction nor a final offset. Mixed-side tuples are isolated vertices. For a
positive repetition count the first coordinate supplies a total bipartition.
-/

namespace UniqueGamesTheorem.Explicit.ProductPaddedOutput

open UniqueGamesTheorem.Foundations
open Target
open MachineOutputContract
open ProductTarget
open scoped BigOperators

namespace Embedded

variable {L R E : Type*} {q N M : ℕ}

variable [Fintype L] [Fintype R] [Fintype E]

noncomputable def extendLabelings [Nonempty (Fin q)]
    (vertices : (L ⊕ R) ↪ Fin N) (left : L → Fin q) (right : R → Fin q) :
    Fin N → Fin q :=
  Function.extend vertices (Sum.elim left right) (fun _ => Classical.choice inferInstance)

end Embedded

end UniqueGamesTheorem.Explicit.ProductPaddedOutput

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineDrainManyLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual cleanup of a finite list of work tapes

Each list position supplies one fixed drain label. The finite-sequence theorem
composes the checked physical drains; neither the list nor a runtime tape index
is stored in the register. Repeated tape names are allowed. The cleanup bound
uses the lengths before cleanup, since draining can only shorten a tape.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineDrainMany

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev Tapes (K : Type) := K → List Bool
abbrev LocalLabel (_ : K) := Unit
abbrev Label (chosen : List K) := MachineFiniteSequence.Label (LocalLabel (K := K)) chosen
abbrev Data (K : Type) := Tapes K × Option Bool

def entry (chosen : List K) (labels : Label chosen → Λ) (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry (LocalLabel (K := K)) (fun _ => ()) chosen labels exit

def result (source : K) (data : Data K) : Data K :=
  (Function.update data.1 source [], none)

def cost (source : K) (data : Data K) : Nat := (data.1 source).length + 1

def finalTapes : List K → Tapes K → Tapes K
  | [], base => base
  | source :: chosen, base => finalTapes chosen (Function.update base source [])

def finalRegister : List K → Option Bool → Option Bool
  | [], register => register
  | _ :: _, _ => none

omit [DecidableEq K] in
@[simp] theorem finalRegister_none (chosen : List K) : finalRegister chosen none = none := by
  cases chosen <;> rfl

def steps : List K → Tapes K → Nat
  | [], _ => 0
  | source :: chosen, base => (base source).length + 1 +
      steps chosen (Function.update base source [])

@[simp] theorem sequence_result (chosen : List K) (base : Tapes K) (register : Option Bool) :
    MachineFiniteSequence.resultOf result chosen (base, register) =
      (finalTapes chosen base, finalRegister chosen register) := by
  induction chosen generalizing base register with
  | nil => rfl
  | cons source chosen ih =>
      change MachineFiniteSequence.resultOf result chosen (Function.update base source [], none) =
        (finalTapes chosen (Function.update base source []), none)
      rw [ih, finalRegister_none]

@[simp] theorem sequence_steps (chosen : List K) (base : Tapes K) (register : Option Bool) :
    MachineFiniteSequence.steps result cost chosen (base, register) = steps chosen base := by
  induction chosen generalizing base register with
  | nil => rfl
  | cons source chosen ih =>
      simp only [MachineFiniteSequence.steps, result, cost, steps, ih]

/-- Selected tapes are empty; every other tape word is preserved. -/
theorem finalTapes_apply (chosen : List K) (base : Tapes K) (k : K) :
    finalTapes chosen base k = if k ∈ chosen then [] else base k := by
  induction chosen generalizing base with
  | nil => simp [finalTapes]
  | cons source chosen ih =>
      rw [finalTapes, ih]
      by_cases h : k = source
      · subst k
        simp
      · simp [List.mem_cons, h]

def lengthSum (chosen : List K) (base : Tapes K) : Nat :=
  (chosen.map (fun k => (base k).length)).sum

omit [DecidableEq K] in
theorem lengthSum_mono (chosen : List K) (first second : Tapes K)
    (h : ∀ k, (first k).length ≤ (second k).length) :
    lengthSum chosen first ≤ lengthSum chosen second := by
  induction chosen with
  | nil => exact Nat.le_refl 0
  | cons source chosen ih =>
      simp only [lengthSum, List.map_cons, List.sum_cons] at ih ⊢
      exact Nat.add_le_add (h source) ih

/-- This upper bound remains valid when the cleanup list repeats tapes. -/
theorem steps_le (chosen : List K) (base : Tapes K) :
    steps chosen base ≤ lengthSum chosen base + chosen.length := by
  induction chosen generalizing base with
  | nil => simp [steps, lengthSum]
  | cons source chosen ih =>
      have hshort : ∀ k, ((Function.update base source []) k).length ≤ (base k).length := by
        intro k
        by_cases h : k = source
        · subst k
          simp
        · simp [Function.update_of_ne h]
      have hsum := lengthSum_mono chosen (Function.update base source []) base hshort
      have htail := ih (Function.update base source [])
      simp only [steps, lengthSum, List.map_cons, List.sum_cons, List.length_cons] at hsum htail ⊢
      omega

theorem steps_le_uniform (chosen : List K) (base : Tapes K) (bound : Nat)
    (h : ∀ k, (base k).length ≤ bound) :
    steps chosen base ≤ chosen.length * (bound + 1) := by
  have hsum : lengthSum chosen base ≤ chosen.length * bound := by
    induction chosen with
    | nil => simp [lengthSum]
    | cons source chosen ih =>
        simp only [lengthSum, List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul,
          Nat.one_mul] at ih ⊢
        have hs := h source
        omega
  have hc := steps_le chosen base
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- An executable complete cleanup list from an explicit finite enumeration. -/
def workTapes {N : Nat} (enumeration : Fin N ≃ K) (output : K) : List K :=
  (List.ofFn (fun i => enumeration i)).filter (fun k => decide (k ≠ output))

@[simp] theorem mem_workTapes {N : Nat} (enumeration : Fin N ≃ K) (output k : K) :
    k ∈ workTapes enumeration output ↔ k ≠ output := by
  have hmem : k ∈ List.ofFn (fun i => enumeration i) := by
    apply List.mem_ofFn.mpr
    exact ⟨enumeration.symm k, enumeration.apply_symm_apply k⟩
  simp [workTapes, hmem]

theorem workTapes_length_le {N : Nat} (enumeration : Fin N ≃ K) (output : K) :
    (workTapes enumeration output).length ≤ N := by
  simpa only [workTapes, List.length_ofFn] using
    List.length_filter_le (fun k => decide (k ≠ output)) (List.ofFn (fun i => enumeration i))

/-- The tape component of the actual halted configuration: only output remains. -/
def haltTapes (output : K) (word : List Bool) : Tapes K :=
  fun k => if k = output then word else []

theorem finalTapes_workTapes {N : Nat} (enumeration : Fin N ≃ K) (output : K)
    (base : Tapes K) :
    finalTapes (workTapes enumeration output) base = haltTapes output (base output) := by
  funext k
  rw [finalTapes_apply]
  by_cases h : k = output
  · subst k
    simp [haltTapes]
  · simp [haltTapes, h]

end UniqueGamesTheorem.Foundations.Complexity.MachineDrainMany

/-!
Preserved comparisons of actual field stacks and their finite equality profile.
All whole-word equalities below are specifications of finite-head comparison.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineFieldProfile

open Turing

abbrev Profile (q : Nat) := Fin q → Fin q → Bool

def equalityProfile {q : Nat} (words : Fin q → List Bool) : Profile q :=
  fun i j => decide (words i = words j)

def setEntry {q : Nat} (profile : Profile q) (pair : Fin q × Fin q) (bit : Bool) : Profile q :=
  Function.update profile pair.1 (Function.update (profile pair.1) pair.2 bit)

theorem setEntry_apply {q : Nat} (profile : Profile q) (pair : Fin q × Fin q)
    (bit : Bool) (i j : Fin q) :
    setEntry profile pair bit i j = if (i, j) = pair then bit else profile i j := by
  rcases pair with ⟨a, b⟩
  by_cases hi : i = a <;> by_cases hj : j = b <;> simp [setEntry, hi, hj]

def setExpected {q : Nat} (words : Fin q → List Bool) (profile : Profile q)
    (pair : Fin q × Fin q) : Profile q :=
  setEntry profile pair (equalityProfile words pair.1 pair.2)

def foldProfile {q : Nat} (words : Fin q → List Bool) (initial : Profile q)
    (cells : List (Fin q × Fin q)) : Profile q := cells.foldl (setExpected words) initial

theorem foldProfile_apply {q : Nat} (words : Fin q → List Bool) (initial : Profile q)
    (cells : List (Fin q × Fin q)) (i j : Fin q) :
    foldProfile words initial cells i j =
      if (i, j) ∈ cells then equalityProfile words i j else initial i j := by
  induction cells generalizing initial with
  | nil => rfl
  | cons pair rest ih =>
    change foldProfile words (setExpected words initial pair) rest i j = _
    rw [ih]
    by_cases hrest : (i, j) ∈ rest
    · simp [hrest]
    · by_cases hpair : (i, j) = pair
      · subst pair
        simp [hrest, setExpected, setEntry_apply]
      · simp [hrest, hpair, setExpected, setEntry_apply]

abbrev Tape (q : Nat) := Fin q ⊕ Fin 3
abbrev Label {q : Nat} (cells : List (Fin q × Fin q)) := Fin (cells.length + 1) × Fin 7

def labelAt {q : Nat} (cells : List (Fin q × Fin q)) (r : Nat) (phase : Fin 7) : Label cells :=
  (⟨min r cells.length, by omega⟩, phase)

def pairTime {q : Nat} (words : Fin q → List Bool) (pair : Fin q × Fin q) : Nat :=
  2 * ((words pair.1).length + 1) + 2 * ((words pair.2).length + 1) +
    max (words pair.1).length (words pair.2).length + 2

def prefixProfile {q : Nat} (words : Fin q → List Bool) (initial : Profile q)
    (cells : List (Fin q × Fin q)) (r : Nat) : Profile q :=
  foldProfile words initial (cells.take r)

def prefixTime {q : Nat} (words : Fin q → List Bool)
    (cells : List (Fin q × Fin q)) (r : Nat) : Nat :=
  ((cells.take r).map (pairTime words)).sum

theorem prefixProfile_succ {q : Nat} (words : Fin q → List Bool) (initial : Profile q)
    (cells : List (Fin q × Fin q)) (r : Nat) (hr : r < cells.length) :
    prefixProfile words initial cells (r + 1) =
      setExpected words (prefixProfile words initial cells r) cells[r] := by
  unfold prefixProfile foldProfile
  rw [List.take_succ_eq_append_getElem hr, List.foldl_append]
  rfl

theorem prefixTime_succ {q : Nat} (words : Fin q → List Bool)
    (cells : List (Fin q × Fin q)) (r : Nat) (hr : r < cells.length) :
    prefixTime words cells (r + 1) = prefixTime words cells r + pairTime words cells[r] := by
  unfold prefixTime
  rw [List.take_succ_eq_append_getElem hr, List.map_append, List.sum_append]
  rfl

def allPairs (q : Nat) : List (Fin q × Fin q) :=
  (List.finRange q).flatMap fun i => (List.finRange q).map fun j => (i, j)

theorem mem_allPairs {q : Nat} (i j : Fin q) : (i, j) ∈ allPairs q := by
  simp [allPairs]

theorem length_allPairs (q : Nat) : (allPairs q).length = q * q := by
  simp [allPairs, List.length_flatMap]

theorem foldProfile_allPairs {q : Nat} (words : Fin q → List Bool) (initial : Profile q) :
    foldProfile words initial (allPairs q) = equalityProfile words := by
  funext i j
  simp [foldProfile_apply, mem_allPairs]

theorem pairTime_le {q : Nat} (words : Fin q → List Bool) (L : Nat)
    (hL : ∀ i, (words i).length ≤ L) (pair : Fin q × Fin q) :
    pairTime words pair ≤ 5 * L + 6 := by
  have hi := hL pair.1
  have hj := hL pair.2
  have hm := max_le hi hj
  dsimp only [pairTime]
  omega

theorem totalTime_le {q : Nat} (words : Fin q → List Bool) (L : Nat)
    (hL : ∀ i, (words i).length ≤ L) (cells : List (Fin q × Fin q)) :
    (cells.map (pairTime words)).sum ≤ cells.length * (5 * L + 6) := by
  induction cells with
  | nil => simp
  | cons pair rest ih =>
    have hp := pairTime_le words L hL pair
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

end UniqueGamesTheorem.Foundations.Complexity.MachineFieldProfile

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceMachine

open Turing
open UniqueGamesTheorem.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

/-- Seed the destination delimiter before scanning the unary payload. -/
def fieldStart (destination : K) (loopLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .push destination (fun _ => false) (.goto fun _ => loopLabel)

def fieldTapes (source destination : K) (base : K → List Bool)
    (input output : List Bool) : K → List Bool :=
  Function.update (Function.update base source input) destination output

@[simp] theorem fieldTapes_source (source destination : K) (hne : source ≠ destination)
    (base : K → List Bool) (input output : List Bool) :
    fieldTapes source destination base input output source = input := by
  simp [fieldTapes, hne]

@[simp] theorem fieldTapes_destination (source destination : K)
    (base : K → List Bool) (input output : List Bool) :
    fieldTapes source destination base input output destination = output := by
  simp [fieldTapes]

@[simp] theorem fieldTapes_self (source destination : K) (base : K → List Bool) :
    fieldTapes source destination base (base source) (base destination) = base := by
  simp [fieldTapes]

theorem fieldTapes_other (source destination p : K)
    (hpS : p ≠ source) (hpD : p ≠ destination)
    (base : K → List Bool) (input output : List Bool) :
    fieldTapes source destination base input output p = base p := by
  simp [fieldTapes, hpS, hpD]

theorem update_field_source (source destination : K) (hne : source ≠ destination)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (fieldTapes source destination base input output) source replacement =
      fieldTapes source destination base replacement output := by
  funext p
  by_cases hs : p = source
  · subst p; simp [fieldTapes, hne]
  · by_cases hd : p = destination
    · subst p; simp [fieldTapes, Ne.symm hne]
    · simp [fieldTapes, hs, hd]

theorem update_field_destination (source destination : K)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (fieldTapes source destination base input output) destination replacement =
      fieldTapes source destination base input replacement := by
  simp [fieldTapes]

theorem fieldStartStep (source destination : K)
    (startLabel loopLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStart : program startLabel = fieldStart destination loopLabel)
    (base : K → List Bool) (input output : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some startLabel, (ambient, register), fieldTapes source destination base input output⟩ =
      some ⟨some loopLabel, (ambient, register),
        fieldTapes source destination base input (false :: output)⟩ := by
  change some (TM2.stepAux (program startLabel) (ambient, register)
    (fieldTapes source destination base input output)) = _
  rw [atStart]
  simp [fieldStart, TM2.stepAux, update_field_destination]

def fieldNext (start : Fin 4 → Λ) (exit : Option Λ) (j : Fin 4) : Option Λ :=
  match j.val with
  | 0 => some (start 1)
  | 1 => some (start 2)
  | 2 => some (start 3)
  | _ => exit

end UniqueGamesTheorem.Foundations.Hastad.SourceMachine

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineLookupCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite control for destructive unary-indexed table lookup. The guard decreases
the index even when the table is exhausted. Selection tests for an empty table
before writing the destination. All tests inspect just one finite head register.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineLookup

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def discard (source : K) (loopLabel returnLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.goto fun _ => loopLabel)
      (.load (fun state => (state.1, none)) (.goto fun _ => returnLabel)))

/-- Check that a field exists before seeding its destination delimiter. -/
def select (source destination : K) (copyLabel rejected : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .peek source (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (Hastad.SourceMachine.fieldStart destination copyLabel)
      (.load (fun state => (state.1, none)) (.goto fun _ => rejected)))

inductive Label
  | guard | skip | select | copy | accepted | rejected
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.guard, .skip, .select, .copy, .accepted,
  .rejected]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

/-- Three caller tapes with every other tape retained verbatim. -/
def tapes (index source destination : K) (base : K → List Bool)
    (counter input output : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base index counter) source input)
    destination output

@[simp] theorem tapes_index (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination)
    (base : K → List Bool) (counter input output : List Bool) :
    tapes index source destination base counter input output index = counter := by
  simp [tapes, his, hid]

@[simp] theorem tapes_source (index source destination : K)
    (hsd : source ≠ destination) (base : K → List Bool)
    (counter input output : List Bool) :
    tapes index source destination base counter input output source = input := by
  simp [tapes, hsd]

@[simp] theorem tapes_destination (index source destination : K)
    (base : K → List Bool) (counter input output : List Bool) :
    tapes index source destination base counter input output destination = output := by
  simp [tapes]

theorem tapes_other (index source destination p : K)
    (hi : p ≠ index) (hs : p ≠ source) (hd : p ≠ destination)
    (base : K → List Bool) (counter input output : List Bool) :
    tapes index source destination base counter input output p = base p := by
  simp [tapes, hi, hs, hd]

theorem update_index (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination)
    (base : K → List Bool) (counter input output replacement : List Bool) :
    Function.update (tapes index source destination base counter input output) index replacement =
      tapes index source destination base replacement input output := by
  funext p
  by_cases hi : p = index
  · subst p; simp [tapes, his, hid]
  · by_cases hs : p = source
    · subst p; by_cases hs : source = destination <;> simp [tapes, hi, hs, Ne.symm hid]
    · by_cases hd : p = destination
      · subst p; simp [tapes, hi]
      · simp [tapes, hi, hs, hd]

theorem update_source (index source destination : K) (hsd : source ≠ destination)
    (base : K → List Bool) (counter input output replacement : List Bool) :
    Function.update (tapes index source destination base counter input output) source replacement =
      tapes index source destination base counter replacement output := by
  funext p
  by_cases hs : p = source
  · subst p; simp [tapes, hsd]
  · by_cases hd : p = destination
    · subst p; simp [tapes, hs]
    · simp [tapes, hs, hd]

theorem update_destination (index source destination : K)
    (base : K → List Bool) (counter input output replacement : List Bool) :
    Function.update (tapes index source destination base counter input output)
      destination replacement = tapes index source destination base counter input replacement := by
  simp [tapes]

theorem fieldTapes_eq (index source destination : K) (hsd : source ≠ destination)
    (base : K → List Bool) (counter input output input' output' : List Bool) :
    Hastad.SourceMachine.fieldTapes source destination
      (tapes index source destination base counter input output) input' output' =
      tapes index source destination base counter input' output' := by
  rw [Hastad.SourceMachine.fieldTapes, update_source _ _ _ hsd, update_destination]

end UniqueGamesTheorem.Foundations.Complexity.MachineLookup

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineLookupDiscard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Execution of the destructive field-discard loop in an arbitrary ambient TM2
program. The scanner consumes a unary payload and its delimiter, preserves the
ambient state and other tapes, and clears its head register on return. At EOF it
returns immediately, leaving the tapes unchanged.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineLookup

open Turing

variable {K Λ σ : Type} [DecidableEq K]

theorem discardStep_delimiter (source : K) (loopLabel returnLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = discard source loopLabel returnLabel)
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, register), Function.update base source (false :: suffix)⟩ =
      some ⟨some returnLabel, (ambient, none), Function.update base source suffix⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (Function.update base source (false :: suffix))) = _
  rw [atLoop]
  simp [discard, TM2.stepAux]

theorem discardStep_true (source : K) (loopLabel returnLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = discard source loopLabel returnLabel)
    (base : K → List Bool) (input : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, register), Function.update base source (true :: input)⟩ =
      some ⟨some loopLabel, (ambient, some true), Function.update base source input⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (Function.update base source (true :: input))) = _
  rw [atLoop]
  simp [discard, TM2.stepAux]

end UniqueGamesTheorem.Foundations.Complexity.MachineLookup

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineUnaryAffineAt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAffineAt

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def finish (restoreLabel : Λ) : TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .load (fun s => (s.1,none)) (.goto (fun _ => restoreLabel))

inductive Label
  | seed | scan | restore
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.seed, .scan, .restore]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

end UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAffineAt

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineLookupLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual traces for the fixed unary lookup machine. Successful lookup preserves
an arbitrary unread table suffix. Rejection relative to a list's end is stated
only for its complete, unframed encoding, so no hidden endpoint is assumed.
-/

/-! Actual lookup from a preserved table. A fresh copy is prefixed to the scan
stack before each access. The old scan suffix is retained and need not be
cleared between accesses. No graph/table data occurs in finite control. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePreservingLookup

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

inductive Label
  | copyFirst | copySecond | lookup (l : MachineLookup.Label)
  deriving DecidableEq, Fintype

end UniqueGamesTheorem.Foundations.Complexity.MachinePreservingLookup

namespace UniqueGamesTheorem.Foundations.Complexity.MachineAffineLookup

open Turing

variable {K Λ σ : Type} [DecidableEq K]

inductive Label
  | seed | scan | restore | copyFirst | copySecond
  | lookup (l : MachineLookup.Label)
  deriving DecidableEq, Fintype

end UniqueGamesTheorem.Foundations.Complexity.MachineAffineLookup

/-!
A fixed-width gather from an input-resident table. Every coordinate index lives
on a unary tape. The coefficient and coordinate-dependent offsets alone live
in finite control. Actual preserving affine lookup instructions read each
requested field, and the proof below composes their traces. This is the gather
phase of product-row construction, before the fixed-width Horner phase.
-/

namespace UniqueGamesTheorem.Explicit.MachineProductGather

open Turing
open UniqueGamesTheorem.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K]

/-- Shared original table, query, scan and copy scratch, then input coordinate
fields and the corresponding gathered output fields. -/
abbrev Tape (width : Nat) := Fin 4 ⊕ (Fin width ⊕ Fin width)

def shift (width : Nat) : Tape width → Tape (width + 1) :=
  Sum.map id (Sum.map Fin.succ Fin.succ)

theorem shift_injective (width : Nat) : Function.Injective (shift width) := by
  intro a b h
  rcases a with a | (a | a) <;> rcases b with b | (b | b) <;> simp_all [shift]

def lookupRole (width : Nat) : Fin 5 → Tape (width + 1)
  | 0 => .inl 0
  | 1 => .inl 1
  | 2 => .inl 2
  | 3 => .inr (.inr 0)
  | 4 => .inl 3

theorem lookupRole_injective (width : Nat) : Function.Injective (lookupRole width) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [lookupRole]

def Label : Nat → Type
  | 0 => Unit
  | width + 1 => MachineAffineLookup.Label ⊕ Label width

instance labelFintype (width : Nat) : Fintype (Label width) := by
  induction width with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ width ih =>
    letI := ih
    exact inferInstanceAs (Fintype (MachineAffineLookup.Label ⊕ Label width))

instance labelDecidableEq (width : Nat) : DecidableEq (Label width) := by
  induction width with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ width ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (MachineAffineLookup.Label ⊕ Label width))

def entry : (width : Nat) → Label width
  | 0 => ()
  | _ + 1 => .inl .seed

end UniqueGamesTheorem.Explicit.MachineProductGather

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineProductGatherBoundsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds on the actual work stacks left by the preserving gather. These
bounds justify clearing the query/scan remnants after each product field;
they are consequences of the exact tape formulas, not runtime assumptions. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePreservingLookupClean

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

inductive Label
  | run (label : MachinePreservingLookup.Label)
  | cleanup
  deriving DecidableEq, Fintype

end UniqueGamesTheorem.Foundations.Complexity.MachinePreservingLookupClean

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineUnaryAddAt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

end UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_MachineTransducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Reduction.MachineTransducer

open Turing
open UniqueGamesTheorem.Foundations.Complexity

variable {Q : Type} [Fintype Q]

/-- The semantic output, with the control state updated after each input bit. -/
def output (transition : Q → Bool → Q) (emit : Q → Bool → List Bool) :
    Q → List Bool → List Bool
  | _, [] => []
  | state, symbol :: input =>
      emit state symbol ++ output transition emit (transition state symbol) input

end UniqueGamesTheorem.Reduction.MachineTransducer

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineTransducerCopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.MachineTransducerCopy

open Turing

variable {K Λ σ Q : Type} [DecidableEq K]

abbrev Alphabet (K : Type) (_ : K) := Bool
abbrev State (σ Q : Type) := (σ × Q) × Option Bool

def scanLoop (source scratch : K) (initial : Q)
    (emitterLabel : Q → Bool → Λ) (restoreLabel : Λ) :
    TM2.Stmt (Alphabet K) Λ (State σ Q) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.push scratch (fun state => state.2.getD false)
        (.goto fun state => emitterLabel state.1.2 (state.2.getD false)))
      (.load (fun state => ((state.1.1, initial), none)) (.goto fun _ => restoreLabel)))

end UniqueGamesTheorem.Foundations.Complexity.MachineTransducerCopy

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineUnaryMultiply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
An actual five-stack unary multiplication subroutine. Both isolated input
fields are preserved. The product field prefixes the previous output stack;
the counter and scratch return empty and all other stacks are framed.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineUnaryMultiply

open Turing
open scoped BigOperators

inductive Label
  | copyDrain | copyFork | seed | guard | scan | emitFalse | emitTrue | restore | finish
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.copyDrain, .copyFork, .seed, .guard, .scan,
  .emitFalse, .emitTrue, .restore, .finish]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

variable {K Λ σ : Type}

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := (σ × Unit) × Option Bool

def transition (_ : Unit) (_ : Bool) : Unit := ()
def payload (_ : Unit) (bit : Bool) : List Bool := if bit then [true] else []

def emitterLabel (labels : Label → Λ) (_ : Unit) (bit : Bool) : Λ :=
  if bit then labels .emitTrue else labels .emitFalse

variable [DecidableEq K]

def bodySteps (a : ℕ) : ℕ := 3 * (a + 1) + 2
def steps (a b : ℕ) : ℕ := 3 * a * b + 8 * b + 7

theorem totalSteps_eq (a b : ℕ) :
    MachineCountedLoop.totalSteps (fun _ => bodySteps a) b = b * (bodySteps a + 1) + 1 := by
  simp [MachineCountedLoop.totalSteps, Nat.mul_add, Nat.add_assoc]

end UniqueGamesTheorem.Foundations.Complexity.MachineUnaryMultiply

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRadixStepLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
One actual Horner step on unary field stacks. Multiplication and addition are
executions of the same finite program. All three operands are preserved; only
the output stack receives a new field and both work stacks return empty.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRadixStep

open Turing

inductive Label
  | multiply (label : MachineUnaryMultiply.Label)
  | digitDrain | digitFork | add | finish
  deriving DecidableEq, Fintype

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (σ : Type) := MachineUnaryMultiply.State σ

variable {K Λ σ : Type}

/-- Multiplication uses radix, accumulator, output, counter, and scratch,
skipping the independently preserved digit stack. -/
def multiplySlots (slots : Fin 6 ↪ K) : Fin 5 ↪ K :=
  (Fin.succAboveEmb (2 : Fin 6)).trans slots

@[simp] theorem multiplySlots_zero (slots : Fin 6 ↪ K) : multiplySlots slots 0 = slots 0 := rfl
@[simp] theorem multiplySlots_one (slots : Fin 6 ↪ K) : multiplySlots slots 1 = slots 1 := rfl
@[simp] theorem multiplySlots_two (slots : Fin 6 ↪ K) : multiplySlots slots 2 = slots 3 := rfl
@[simp] theorem multiplySlots_three (slots : Fin 6 ↪ K) : multiplySlots slots 3 = slots 4 := rfl
@[simp] theorem multiplySlots_four (slots : Fin 6 ↪ K) : multiplySlots slots 4 = slots 5 := rfl

variable [DecidableEq K]

def steps (radix acc digit : ℕ) : ℕ := 3 * radix * acc + 8 * acc + 3 * digit + 13

end UniqueGamesTheorem.Foundations.Complexity.MachineRadixStep

/-!
Fixed-width Horner traversal by actual radix steps. Two accumulators alternate:
a radix step writes into the empty alternate, then the previous accumulator is
consumed. The base, digit fields, and arbitrary external tapes are preserved.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineHorner

open Turing

variable {K Λ σ : Type} {width : Nat}

abbrev Layout (width : Nat) := Fin 6 ⊕ Fin width
abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := MachineRadixStep.State σ

def parity : Nat → Bool
  | 0 => false
  | n + 1 => !(parity n)

def accumulator (flip : Bool) : Fin 6 := if flip then 2 else 1

@[simp] theorem accumulator_ne (flip : Bool) : accumulator flip ≠ accumulator (!flip) := by
  cases flip <;> decide

def radixLayout (flip : Bool) (i : Fin width) : Fin 6 ↪ Layout width where
  toFun
    | 0 => .inl 0
    | 1 => .inl (accumulator flip)
    | 2 => .inr i
    | 3 => .inl (accumulator (!flip))
    | 4 => .inl 4
    | 5 => .inl 5
  inj' := by
    intro a b h
    cases flip <;> fin_cases a <;> fin_cases b <;> simp [accumulator] at h ⊢

def radixSlots (slots : Layout width ↪ K) (i : Fin width) : Fin 6 ↪ K :=
  (radixLayout (parity i.val) i).trans slots

@[simp] theorem radixSlots_base (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 0 = slots (.inl 0) := rfl
@[simp] theorem radixSlots_acc (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 1 = slots (.inl (accumulator (parity i.val))) := rfl
@[simp] theorem radixSlots_digit (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 2 = slots (.inr i) := rfl
@[simp] theorem radixSlots_out (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 3 = slots (.inl (accumulator (parity (i.val + 1)))) := rfl
@[simp] theorem radixSlots_counter (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 4 = slots (.inl 4) := rfl
@[simp] theorem radixSlots_scratch (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 5 = slots (.inl 5) := rfl

inductive Label (width : Nat)
  | start
  | radix (i : Fin width) (inner : MachineRadixStep.Label)
  | clear (i : Fin width)
  | finishDrain | finishRestore
  deriving DecidableEq, Fintype

def entryLabel (width n : Nat) : Label width :=
  if h : n < width then .radix ⟨n, h⟩ (.multiply .copyDrain) else .finishDrain

variable [DecidableEq K]

def value (radix : Nat) (digits : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => radix * value radix digits n + digits n

def stepCost (radix acc digit : Nat) : Nat :=
  MachineRadixStep.steps radix acc digit + acc + 1

def prefixSteps (radix : Nat) (digits : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => prefixSteps radix digits n + stepCost radix (value radix digits n) (digits n)

structure Clean (slots : Layout width ↪ K) (base : K → List Bool) : Prop where
  accA : base (slots (.inl 1)) = []
  accB : base (slots (.inl 2)) = []
  counter : base (slots (.inl 4)) = []
  scratch : base (slots (.inl 5)) = []

omit [DecidableEq K] in
theorem Clean.acc {slots : Layout width ↪ K} {base : K → List Bool}
    (clean : Clean slots base) (flip : Bool) : base (slots (.inl (accumulator flip))) = [] := by
  cases flip
  · exact clean.accA
  · exact clean.accB

def steps (radix : Nat) (digits : Nat → Nat) (width : Nat) : Nat :=
  prefixSteps radix digits width + 2 * value radix digits width + 5

omit [DecidableEq K] in
theorem value_eq_foldl (radix : Nat) (digits : Nat → Nat) (n : Nat) :
    value radix digits n =
      ((List.range n).map digits).foldl (fun acc digit => radix * acc + digit) 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [value, List.range_succ, List.map_append, List.foldl_append]
    simp only [List.map_singleton, List.foldl_cons, List.foldl_nil, ← ih]

omit [DecidableEq K] in
/-- A magnitude bound accommodates arbitrary digits, including fixed polynomial
coefficients larger than the radix. No bounded-digit assumption is needed for
execution correctness. -/
theorem value_add_one_le (radix : Nat) (digits : Nat → Nat) (width magnitude : Nat)
    (radixBound : radix ≤ magnitude)
    (digitBound : ∀ i, i < width → digits i ≤ magnitude)
    (n : Nat) (hn : n ≤ width) : value radix digits n + 1 ≤ (magnitude + 1) ^ n := by
  induction n with
  | zero => simp [value]
  | succ n ih =>
    have hn' : n < width := by omega
    have hm := Nat.mul_le_mul_right (value radix digits n) radixBound
    calc
      value radix digits (n + 1) + 1 ≤ (magnitude + 1) * (value radix digits n + 1) := by
        rw [value]
        have hd := digitBound n hn'
        nlinarith
      _ ≤ (magnitude + 1) * (magnitude + 1) ^ n :=
        Nat.mul_le_mul_left _ (ih (by omega))
      _ = (magnitude + 1) ^ (n + 1) := by rw [pow_succ]; ac_rfl

omit [DecidableEq K] in
theorem value_le (radix : Nat) (digits : Nat → Nat) (width magnitude : Nat)
    (radixBound : radix ≤ magnitude)
    (digitBound : ∀ i, i < width → digits i ≤ magnitude)
    (n : Nat) (hn : n ≤ width) : value radix digits n ≤ (magnitude + 1) ^ width := by
  have h := value_add_one_le radix digits width magnitude radixBound digitBound n hn
  exact (Nat.le_trans (Nat.le_add_right _ _) h).trans
    (Nat.pow_le_pow_right (Nat.succ_pos _) hn)

def perDigitBound (width magnitude : Nat) : Nat :=
  3 * magnitude * (magnitude + 1) ^ width + 9 * (magnitude + 1) ^ width + 3 * magnitude + 14

omit [DecidableEq K] in
theorem stepCost_le (radix acc digit width magnitude : Nat)
    (radixBound : radix ≤ magnitude) (accBound : acc ≤ (magnitude + 1) ^ width)
    (digitBound : digit ≤ magnitude) :
    stepCost radix acc digit ≤ perDigitBound width magnitude := by
  have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 3 radixBound) accBound
  unfold stepCost MachineRadixStep.steps perDigitBound
  omega

omit [DecidableEq K] in
theorem prefixSteps_le (radix : Nat) (digits : Nat → Nat) (width magnitude : Nat)
    (radixBound : radix ≤ magnitude)
    (digitBound : ∀ i, i < width → digits i ≤ magnitude)
    (n : Nat) (hn : n ≤ width) :
    prefixSteps radix digits n ≤ n * perDigitBound width magnitude := by
  induction n with
  | zero => simp [prefixSteps]
  | succ n ih =>
    have hn' : n < width := by omega
    have ha := value_le radix digits width magnitude radixBound digitBound n (by omega)
    have hc := stepCost_le radix (value radix digits n) (digits n) width magnitude
      radixBound ha (digitBound n hn')
    rw [prefixSteps]
    calc
      prefixSteps radix digits n + stepCost radix (value radix digits n) (digits n) ≤
          n * perDigitBound width magnitude + perDigitBound width magnitude :=
        Nat.add_le_add (ih (by omega)) hc
      _ = (n + 1) * perDigitBound width magnitude := by rw [Nat.add_mul, Nat.one_mul]

noncomputable def timePolynomial (width : Nat) : Polynomial Nat :=
  Polynomial.C width *
    (3 * Polynomial.X * (Polynomial.X + 1) ^ width +
      9 * (Polynomial.X + 1) ^ width + 3 * Polynomial.X + 14) +
    2 * (Polynomial.X + 1) ^ width + 5

omit [DecidableEq K] in
@[simp] theorem timePolynomial_eval (width magnitude : Nat) :
    (timePolynomial width).eval magnitude =
      width * perDigitBound width magnitude + 2 * (magnitude + 1) ^ width + 5 := by
  simp [timePolynomial, perDigitBound]

omit [DecidableEq K] in
theorem steps_le_timePolynomial (radix : Nat) (digits : Nat → Nat) (width magnitude : Nat)
    (radixBound : radix ≤ magnitude)
    (digitBound : ∀ i, i < width → digits i ≤ magnitude) :
    steps radix digits width ≤ (timePolynomial width).eval magnitude := by
  have hp := prefixSteps_le radix digits width magnitude radixBound digitBound width (Nat.le_refl _)
  have hv := value_le radix digits width magnitude radixBound digitBound width (Nat.le_refl _)
  rw [timePolynomial_eval]
  unfold steps
  omega

open scoped BigOperators

end UniqueGamesTheorem.Foundations.Complexity.MachineHorner

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineProductFieldLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One actual product-output field: gather the fixed number of coordinate
values from the input table, evaluate their common-radix code by Horner, move
the resulting word into the reversed output accumulator, and clear the gather
work. All input fields and the input table are preserved. -/

namespace UniqueGamesTheorem.Explicit.MachineProductField

section

open Turing
open UniqueGamesTheorem.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K] {width : Nat}

/-- Gather's table/query/scan/scratch and coordinate tapes; then radix, two
Horner accumulators, counter, scratch, isolated field output, global output. -/
abbrev Layout (width : Nat) := MachineProductGather.Tape width ⊕ Fin 7

def gatherSlots (slots : Layout width ↪ K) : MachineProductGather.Tape width ↪ K :=
  Function.Embedding.trans (Function.Embedding.inl) slots

def clearTapes (slots : Layout width ↪ K) : List K :=
  [slots (.inl (.inl 1)), slots (.inl (.inl 2))] ++
    List.ofFn (fun i : Fin width => slots (.inl (.inr (.inr i))))

abbrev Label (slots : Layout width ↪ K) :=
  MachineProductGather.Label width ⊕
    (MachineHorner.Label width ⊕ (Unit ⊕ MachineDrainMany.Label (clearTapes slots)))

def entry (slots : Layout width ↪ K) : Label slots :=
  .inl (MachineProductGather.entry width)

/-- Conditions on real input/work stacks; arbitrary output suffixes remain
permitted. The two query/scan tapes are empty at a row boundary. -/
structure Ready (slots : Layout width ↪ K) (base : K → List Bool) : Prop where
  query : base (slots (.inl (.inl 1))) = []
  scan : base (slots (.inl (.inl 2))) = []
  gatherScratch : base (slots (.inl (.inl 3))) = []
  fields : ∀ i, base (slots (.inl (.inr (.inr i)))) = []
  accA : base (slots (.inr 1)) = []
  accB : base (slots (.inr 2)) = []
  counter : base (slots (.inr 3)) = []
  hornerScratch : base (slots (.inr 4)) = []
  output : base (slots (.inr 5)) = []

end

/-! The product-field machine restores every work tape and appends precisely
one field to the reversed output. This boundary is strong enough to compose
all fields and every odometer visit without retaining an unbounded history. -/

open UniqueGamesTheorem.Foundations.Complexity

variable {K : Type} [DecidableEq K] {width : Nat}

omit [DecidableEq K] in
@[simp] theorem mem_clearTapes (slots : Layout width ↪ K) (k : K) :
    k ∈ clearTapes slots ↔ k = slots (.inl (.inl 1)) ∨
      k = slots (.inl (.inl 2)) ∨ ∃ i, k = slots (.inl (.inr (.inr i))) := by
  simp [clearTapes, List.mem_ofFn, eq_comm]

omit [DecidableEq K] in
theorem extra_not_mem_clearTapes (slots : Layout width ↪ K) (i : Fin 7) :
    slots (.inr i) ∉ clearTapes slots := by
  simp only [mem_clearTapes]
  rintro (h | h | ⟨j, h⟩)
  · exact slots.injective.ne (by simp) h
  · exact slots.injective.ne (by simp) h
  · exact slots.injective.ne (by simp) h

omit [DecidableEq K] in
theorem Ready.empty_clearTapes (slots : Layout width ↪ K) (base : K → List Bool)
    (ready : Ready slots base) (k : K) (member : k ∈ clearTapes slots) : base k = [] := by
  rcases (mem_clearTapes slots k).mp member with rfl | rfl | ⟨i, rfl⟩
  · exact ready.query
  · exact ready.scan
  · exact ready.fields i

/-- The output update preserves all work-tape entry conditions. -/
theorem Ready.output_update (slots : Layout width ↪ K) (base : K → List Bool)
    (ready : Ready slots base) (word : List Bool) :
    Ready slots (Function.update base (slots (.inr 6)) word) := by
  have other (a : Layout width) (h : a ≠ .inr 6) :
      Function.update base (slots (.inr 6)) word (slots a) = base (slots a) :=
    Function.update_of_ne (slots.injective.ne h) _ _
  constructor
  · rw [other _ (by simp)]; exact ready.query
  · rw [other _ (by simp)]; exact ready.scan
  · rw [other _ (by simp)]; exact ready.gatherScratch
  · intro i; rw [other _ (by simp)]; exact ready.fields i
  · rw [other _ (by simp)]; exact ready.accA
  · rw [other _ (by simp)]; exact ready.accB
  · rw [other _ (by simp)]; exact ready.counter
  · rw [other _ (by simp)]; exact ready.hornerScratch
  · rw [other _ (by simp)]; exact ready.output

omit [DecidableEq K] in
theorem clearTapes_length (slots : Layout width ↪ K) : (clearTapes slots).length = width + 2 := by
  simp [clearTapes]

end UniqueGamesTheorem.Explicit.MachineProductField

/-! Actual power-header emission by fixed-width Horner evaluation of
`[1,0,...,0]`, followed by physical transfer to the reverse accumulator. -/

namespace UniqueGamesTheorem.Explicit.MachineProductPower

open Turing
open UniqueGamesTheorem.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K] {exponent : Nat}

def digits (i : Nat) : Nat := if i = 0 then 1 else 0

theorem value_eq (radix exponent : Nat) : MachineHorner.value radix digits (exponent + 1) = radix ^ exponent := by
  induction exponent with
  | zero => simp [MachineHorner.value, digits]
  | succ exponent ih =>
    rw [MachineHorner.value, ih]
    simp [digits, pow_succ, Nat.mul_comm]

abbrev Label (exponent : Nat) := MachineHorner.Label (exponent + 1) ⊕ Unit

def steps (radix exponent : Nat) : Nat :=
  MachineHorner.steps radix digits (exponent + 1) + radix ^ exponent + 2

noncomputable def timePolynomial (exponent : Nat) : Polynomial Nat :=
  MachineHorner.timePolynomial (exponent + 1) +
    (Polynomial.X + 1) ^ exponent + 2

theorem steps_le (radix exponent magnitude : Nat) (bounded : radix ≤ magnitude)
    (positive : 1 ≤ magnitude) : steps radix exponent ≤ (timePolynomial exponent).eval magnitude := by
  have digitBound : ∀ i, i < exponent + 1 → digits i ≤ magnitude := by
    intro i hi; unfold digits; split <;> omega
  have h := MachineHorner.steps_le_timePolynomial radix digits (exponent + 1) magnitude bounded digitBound
  have hp : radix ^ exponent ≤ (magnitude + 1) ^ exponent :=
    Nat.pow_le_pow_left (by omega) _
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_ofNat]
  unfold steps
  omega

end UniqueGamesTheorem.Explicit.MachineProductPower

/-! A finite row-field schedule. Endpoint fields use the input vertex radix;
permutation fields use the fixed alphabet radix. The complete list of columns
is in finite control, while all row indices, table entries and radix magnitudes
remain data on tapes. -/

namespace UniqueGamesTheorem.Explicit.MachineProductRow

open Turing
open UniqueGamesTheorem.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K] {width : Nat}

abbrev Layout (width : Nat) := MachineProductField.Layout width ⊕ Unit
abbrev Command (width : Nat) := Bool × (Fin width → Nat)

/-- Only the radix tape is switched between endpoint and alphabet fields. -/
def fieldRole (useAlphabet : Bool) : MachineProductField.Layout width → Layout width
  | .inr 0 => if useAlphabet then .inr () else .inl (.inr 0)
  | tape => .inl tape

theorem fieldRole_injective (useAlphabet : Bool) :
    Function.Injective (fieldRole (width := width) useAlphabet) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => simpa [fieldRole] using h
    | inr b => fin_cases b <;> cases useAlphabet <;> simp [fieldRole] at h
  | inr a =>
    cases b with
    | inl b => fin_cases a <;> cases useAlphabet <;> simp [fieldRole] at h
    | inr b => fin_cases a <;> fin_cases b <;> cases useAlphabet <;> simp_all [fieldRole]

def fieldSlots (slots : Layout width ↪ K) (useAlphabet : Bool) :
    MachineProductField.Layout width ↪ K :=
  Function.Embedding.trans ⟨fieldRole useAlphabet, fieldRole_injective useAlphabet⟩ slots

abbrev LocalLabel (slots : Layout width ↪ K) (command : Command width) :=
  MachineProductField.Label (fieldSlots slots command.1)

abbrev Label (slots : Layout width ↪ K) (commands : List (Command width)) :=
  MachineFiniteSequence.Label (LocalLabel slots) commands

def localMain (slots : Layout width ↪ K) (command : Command width) : LocalLabel slots command :=
  MachineProductField.entry (fieldSlots slots command.1)

def entry (slots : Layout width ↪ K) (commands : List (Command width))
    (labels : Label slots commands → Λ) (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry (LocalLabel slots) (localMain slots) commands labels exit

def outputTape (slots : Layout width ↪ K) : K := slots (.inl (.inr 6))

end UniqueGamesTheorem.Explicit.MachineProductRow

/-! Polynomial bounds for actual field and row traces. The output accumulator
is excluded from local cleanup and is never rescanned by row emission. -/

namespace UniqueGamesTheorem.Explicit.MachineProductBounds

open UniqueGamesTheorem.Foundations.Complexity

variable {K : Type} [DecidableEq K] {width : Nat}

noncomputable def fieldPolynomial (width : Nat) : Polynomial Nat :=
  Polynomial.C width * (7 * Polynomial.X + 6) + 1 +
    MachineHorner.timePolynomial width + (Polynomial.X + 1) ^ width + 2 +
    Polynomial.C (width + 2) * (Polynomial.C width * (Polynomial.X + 1) + 1)

@[simp] theorem fieldPolynomial_eval (width magnitude : Nat) :
    (fieldPolynomial width).eval magnitude =
      width * (7 * magnitude + 6) + 1 + (MachineHorner.timePolynomial width).eval magnitude +
        (magnitude + 1) ^ width + 2 + (width + 2) * (width * (magnitude + 1) + 1) := by
  simp [fieldPolynomial]

end UniqueGamesTheorem.Explicit.MachineProductBounds

/-! Fixed natural polynomials are represented by literal Horner coefficients.
The coefficient representation is independent of the machine input. The actual
machine wrapper is built from the shared physical unary Horner subroutine. -/

namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.PolynomialMachine

noncomputable def coefficientPolynomial : List Nat → Polynomial Nat
  | [] => 0
  | a :: rest => coefficientPolynomial rest * Polynomial.X + Polynomial.C a

theorem coefficientPolynomial_eval (cs : List Nat) (n : Nat) :
    (coefficientPolynomial cs).eval n = cs.foldr (fun digit value => value * n + digit) 0 := by
  induction cs with
  | nil => simp [coefficientPolynomial]
  | cons a rest ih => simp [coefficientPolynomial, ih]

theorem coefficientPolynomial_eval_reverse (cs : List Nat) (n : Nat) :
    (coefficientPolynomial cs).eval n =
      cs.reverse.foldl (fun value digit => value * n + digit) 0 := by
  rw [coefficientPolynomial_eval, List.foldr_eq_foldl_reverse]

/-- An actual finite coefficient list for every fixed natural polynomial.
No evaluation of an input is included in this static representation choice. -/
noncomputable def coefficients (p : Polynomial Nat) :
    {cs : List Nat // coefficientPolynomial cs = p} := by
  refine Polynomial.recOnHorner p ?_ ?_ ?_
  · exact ⟨[], rfl⟩
  · intro q a hq ha ih
    rcases ih with ⟨cs, hcs⟩
    cases cs with
    | nil =>
      refine ⟨[a], ?_⟩
      rw [← hcs]
      simp [coefficientPolynomial]
    | cons b rest =>
      refine ⟨(b + a) :: rest, ?_⟩
      rw [← hcs]
      simp only [coefficientPolynomial, Polynomial.C_add, add_assoc]
  · intro q hq ih
    rcases ih with ⟨cs, hcs⟩
    refine ⟨0 :: cs, ?_⟩
    simp only [coefficientPolynomial, Polynomial.C_0, add_zero, hcs]

noncomputable def highCoefficients (p : Polynomial Nat) : List Nat :=
  (coefficients p).val.reverse

noncomputable def width (p : Polynomial Nat) : Nat := (highCoefficients p).length

noncomputable def digit (p : Polynomial Nat) (i : Nat) : Nat :=
  if hi : i < width p then (highCoefficients p)[i] else 0

theorem highCoefficients_foldl (p : Polynomial Nat) (n : Nat) :
    (highCoefficients p).foldl (fun value digit => value * n + digit) 0 = p.eval n := by
  calc
    _ = (coefficientPolynomial (coefficients p).val).eval n :=
      (coefficientPolynomial_eval_reverse (coefficients p).val n).symm
    _ = p.eval n := congrArg (fun q : Polynomial Nat => q.eval n) (coefficients p).property

theorem range_map_digit (p : Polynomial Nat) :
    (List.range (width p)).map (digit p) = highCoefficients p := by
  apply List.ext_getElem
  · simp [width]
  · intro i hi hj
    simp [digit, width, hj]

section LiteralFields

open Turing

variable {K Λ σ : Type} [DecidableEq K]

def prependFieldsTapes (word : K → List Bool) : List K →
    (K → List Bool) → K → List Bool
  | [], tapes => tapes
  | k :: rest, tapes =>
      prependFieldsTapes word rest (Function.update tapes k (word k ++ tapes k))

theorem prependFieldsTapes_apply (word : K → List Bool) (indices : List K)
    (hn : indices.Nodup) (tapes : K → List Bool) (k : K) :
    prependFieldsTapes word indices tapes k =
      if k ∈ indices then word k ++ tapes k else tapes k := by
  induction indices generalizing tapes with
  | nil => simp [prependFieldsTapes]
  | cons j rest ih =>
    have hnodup := List.nodup_cons.mp hn
    rw [prependFieldsTapes, ih hnodup.2]
    by_cases hkj : k = j
    · subst k
      simp [hnodup.1]
    · simp [hkj]

def popN (k : K) : Nat → TM2.Stmt (fun _ : K => Bool) Λ σ →
    TM2.Stmt (fun _ : K => Bool) Λ σ
  | 0, continuation => continuation
  | n + 1, continuation => .pop k (fun state _ => state) (popN k n continuation)

theorem stepAux_popN (k : K) (n : Nat)
    (continuation : TM2.Stmt (fun _ : K => Bool) Λ σ) (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (popN k n continuation) state tapes =
      TM2.stepAux continuation state (Function.update tapes k ((tapes k).drop n)) := by
  induction n generalizing tapes with
  | zero => simp [popN]
  | succ n ih =>
    simp only [popN, TM2.stepAux]
    rw [ih]
    simp only [Function.update_self, Function.update_idem, List.drop_tail]

def clearFieldsTapes (count : K → Nat) : List K → (K → List Bool) → K → List Bool
  | [], tapes => tapes
  | k :: rest, tapes => clearFieldsTapes count rest
      (Function.update tapes k ((tapes k).drop (count k)))

theorem clearFieldsTapes_apply (count : K → Nat) (indices : List K)
    (hn : indices.Nodup) (tapes : K → List Bool) (k : K) :
    clearFieldsTapes count indices tapes k =
      if k ∈ indices then (tapes k).drop (count k) else tapes k := by
  induction indices generalizing tapes with
  | nil => simp [clearFieldsTapes]
  | cons j rest ih =>
    have hnodup := List.nodup_cons.mp hn
    rw [clearFieldsTapes, ih hnodup.2]
    by_cases hkj : k = j
    · subst k
      simp [hnodup.1]
    · simp [hkj]

end LiteralFields

noncomputable section

def prefixValuePolynomial (digits : Nat → Nat) : Nat → Polynomial Nat
  | 0 => 0
  | i + 1 => Polynomial.X * prefixValuePolynomial digits i + Polynomial.C (digits i)

def prefixCostPolynomial (digits : Nat → Nat) : Nat → Polynomial Nat
  | 0 => 0
  | i + 1 => prefixCostPolynomial digits i +
      Polynomial.C 3 * Polynomial.X * prefixValuePolynomial digits i +
      Polynomial.C 9 * prefixValuePolynomial digits i + Polynomial.C (3 * digits i + 14)

theorem prefixValuePolynomial_eval (digits : Nat → Nat) (i n : Nat) :
    (prefixValuePolynomial digits i).eval n = MachineHorner.value n digits i := by
  induction i with
  | zero => simp [prefixValuePolynomial, MachineHorner.value]
  | succ i ih => simp [prefixValuePolynomial, MachineHorner.value, ih]

theorem prefixCostPolynomial_eval (digits : Nat → Nat) (i n : Nat) :
    (prefixCostPolynomial digits i).eval n = MachineHorner.prefixSteps n digits i := by
  induction i with
  | zero => simp [prefixCostPolynomial, MachineHorner.prefixSteps]
  | succ i ih =>
    simp only [prefixCostPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, prefixValuePolynomial_eval, ih,
      MachineHorner.prefixSteps, MachineHorner.stepCost, MachineRadixStep.steps]
    ring

end

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.PolynomialMachine

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_ProductMachineSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The exact table lookups and field schedule consumed by the product machine.
The table contains rows only: the three input header words have already been
consumed, so each affine lookup has coefficient `q+2` and no header offset.
-/

namespace UniqueGamesTheorem.Explicit.ProductMachineSemantics

open UniqueGamesTheorem.Foundations
open Target
open Complexity
open MachineOutputContract

variable {n q t : ℕ}

def reverseDigits (fields : Fin t → ℕ) (i : ℕ) : ℕ :=
  if h : i < t then fields (Fin.rev ⟨i, h⟩) else 0

@[simp] theorem reverseDigits_at (fields : Fin t → ℕ) (i : Fin t) :
    reverseDigits fields i.val = fields i.rev := by simp [reverseDigits, i.isLt]

theorem reverseDigits_words (fields : Fin t → ℕ) :
    (List.range t).map (reverseDigits fields) = (List.ofFn fields).reverse := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hi' : i < t := by simpa using hi
    simp only [List.getElem_map, List.getElem_range, reverseDigits, hi', ↓reduceDIte,
      List.getElem_reverse, List.getElem_ofFn, List.length_ofFn, Fin.rev]
    apply congrArg fields
    apply Fin.ext
    change t - (i + 1) = t - 1 - i
    omega

theorem horner_ofFin {radix : ℕ} (fields : Fin t → Fin radix) :
    MachineHorner.value radix (reverseDigits (fun i => (fields i : ℕ))) t =
      (finFunctionFinEquiv fields : ℕ) := by
  rw [MachineHorner.value_eq_foldl, reverseDigits_words,
    ← ProductTarget.address_eq_horner]

def sourceCommand (t : ℕ) : MachineProductRow.Command t := (false, fun _ => 0)
def targetCommand (t : ℕ) : MachineProductRow.Command t := (false, fun _ => 1)
def imageCommand (q t : ℕ) (a : Fin (q ^ t)) : MachineProductRow.Command t :=
  (true, fun i => 2 + (finFunctionFinEquiv.symm a i).val)

/-- The complete fixed-alphabet row schedule: two endpoints followed by every
forward-table entry in increasing numeric label order. -/
def commands (q t : ℕ) : List (MachineProductRow.Command t) :=
  sourceCommand t :: targetCommand t :: (List.finRange (q ^ t)).map (imageCommand q t)

theorem commands_length (q t : ℕ) : (commands q t).length = q ^ t + 2 := by
  simp [commands]

end UniqueGamesTheorem.Explicit.ProductMachineSemantics

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_SelectedCommonMarginalLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Actual finite shared seed laws for the bounded correlated sampler. -/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators
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

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_MachineFieldTemplate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.MachineFieldTemplate

open Turing
open UniqueGamesTheorem.Foundations.Complexity

variable {q : Nat} {K Λ σ : Type}

inductive Token (q : Nat)
  | literal (bits : List Bool)
  | copy (field : Fin q)
  deriving DecidableEq

def tokenOutput (fields : Fin q → List Bool) : Token q → List Bool
  | .literal bits => bits
  | .copy j => fields j

def templateOutput (tokens : List (Token q)) (fields : Fin q → List Bool) : List Bool :=
  tokens.flatMap (tokenOutput fields)

def tokenSteps (fields : Fin q → List Bool) : Token q → Nat
  | .literal _ => 1
  | .copy j => 3 * (fields j).length + 3

def workSteps (tokens : List (Token q)) (fields : Fin q → List Bool) : Nat :=
  (tokens.map (tokenSteps fields)).sum

def templateSteps (tokens : List (Token q)) (fields : Fin q → List Bool) : Nat :=
  workSteps tokens fields + 1

def copiedLength (tokens : List (Token q)) (fields : Fin q → List Bool) : Nat :=
  (tokens.map (fun t => match t with | .literal _ => 0 | .copy j => (fields j).length)).sum

inductive Label (m : Nat)
  | entry (index : Fin m)
  | scan (index : Fin m)
  | emit (index : Fin m) (symbol : Bool)
  | restore (index : Fin m)
  | done
  deriving DecidableEq, Fintype

abbrev State (σ : Type) := (σ × Unit) × Option Bool
abbrev Alphabet (_ : K) := Bool

def reset (state : State σ) : State σ := ((state.1.1, ()), none)

@[simp] theorem reset_reset (state : State σ) : reset (reset state) = reset state := rfl

def startAt (m i : Nat) : Label m :=
  if h : i < m then .entry ⟨i, h⟩ else .done

def jump (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def identityEmit (_ : Unit) (b : Bool) : List Bool := [b]

variable [DecidableEq K]

def outputTapes (base : K → List Bool) (output : K) (bits : List Bool) : K → List Bool :=
  Function.update base output (bits.reverse ++ base output)

@[simp] theorem outputTapes_self (base : K → List Bool) (output : K) :
    outputTapes base output [] = base := by simp [outputTapes]

@[simp] theorem outputTapes_output (base : K → List Bool) (output : K) (bits : List Bool) :
    outputTapes base output bits output = bits.reverse ++ base output := by simp [outputTapes]

theorem outputTapes_other (base : K → List Bool) (output : K) (bits : List Bool)
    (tape : K) (different : tape ≠ output) :
    outputTapes base output bits tape = base tape := by simp [outputTapes, different]

theorem outputTapes_append (base : K → List Bool) (output : K) (first second : List Bool) :
    outputTapes (outputTapes base output first) output second =
      outputTapes base output (first ++ second) := by
  simp [outputTapes, List.reverse_append, List.append_assoc]

theorem fieldValues_outputTapes (field : Fin q → K) (output : K)
    (fieldOutput : ∀ j, field j ≠ output) (base : K → List Bool) (bits : List Bool) :
    (fun j => outputTapes base output bits (field j)) = (fun j => base (field j)) := by
  funext j
  exact outputTapes_other base output bits _ (fieldOutput j)

theorem identity_output (bits : List Bool) :
    MachineTransducer.output (fun (_ : Unit) _ => ()) identityEmit () bits = bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [MachineTransducer.output, identityEmit, ih]

theorem chain {α : Type*} {f : α → α} {x y z : α} {m n : Nat}
    (first : f^[m] x = y) (second : f^[n] y = z) : f^[n + m] x = z := by
  rw [Function.iterate_add_apply, first, second]

theorem templateSteps_le (tokens : List (Token q)) (fields : Fin q → List Bool) :
    templateSteps tokens fields ≤ 3 * copiedLength tokens fields + 3 * tokens.length + 1 := by
  have workBound : workSteps tokens fields ≤
      3 * copiedLength tokens fields + 3 * tokens.length := by
    induction tokens with
    | nil => simp [workSteps, copiedLength]
    | cons token tokens ih =>
        cases token <;>
          simp only [workSteps, copiedLength, List.map_cons, List.sum_cons,
            tokenSteps, List.length_cons] at * <;> omega
  unfold templateSteps
  omega

end UniqueGamesTheorem.Reduction.MachineFieldTemplate

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineFixedCopiesLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
A fixed number of copies of an arbitrary bit stream, by a real finite-alphabet
machine. This is the uniform-rounding stream primitive: copying a header-free
occurrence stream `C` times gives multiplicity `C` to every listed occurrence.
The input is preserved during the copy phase, physically drained, and replaced
by the forward-order result. No unbounded word is stored in finite control.
-/

namespace UniqueGamesTheorem.Explicit.MachineFixedCopies

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Reduction

def copies (C : Nat) (word : List Bool) : List Bool :=
  (List.replicate C word).flatten

@[simp] theorem copies_zero (word : List Bool) : copies 0 word = [] := rfl

@[simp] theorem copies_succ (C : Nat) (word : List Bool) :
    copies (C + 1) word = word ++ copies C word := by
  simp [copies, List.replicate_succ]

@[simp] theorem copies_length (C : Nat) (word : List Bool) :
    (copies C word).length = C * word.length := by
  induction C with
  | zero => simp
  | succ C ih => simp [ih, Nat.add_mul, Nat.add_comm]

end UniqueGamesTheorem.Explicit.MachineFixedCopies

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionRows

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Target
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Reduction

/-- The semantic subdivision numbering: originals and middle vertices on the
left, then two private right vertices for each occurrence. -/
def subdivisionVertexWords (n Q u v e : Nat) : Fin 5 → Nat
  | 0 => u
  | 1 => n + Q + 2 * e
  | 2 => n + e
  | 3 => n + Q + 2 * e + 1
  | 4 => v

end UniqueGamesTheorem.Explicit.MachineSubdivisionRows

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_SubdivisionTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Concrete numbered, full-table output for the four-edge subdivision.
Original vertices keep their names. The new names are `n+e`, `n+Q+2e`,
and `n+Q+2e+1`, and each input occurrence emits four consecutive rows.
-/

namespace UniqueGamesTheorem.Explicit.SubdivisionTarget

open UniqueGamesTheorem.Foundations Target
open MachineOutputContract
open scoped BigOperators

/-- Number `p_e` by `2e` and `r_e` by `2e+1`. -/
def numericRightEquiv (Q : Nat) : Fin Q × Bool ≃ Fin (Q * 2) :=
  (Equiv.prodCongr (Equiv.refl (Fin Q)) finTwoEquiv.symm).trans finProdFinEquiv

@[simp] theorem numericRightEquiv_false_val (Q : Nat) (e : Fin Q) :
    (numericRightEquiv Q (e, false)).val = 2 * e.val := by
  change 0 + 2 * e.val = 2 * e.val
  exact Nat.zero_add _

@[simp] theorem numericRightEquiv_true_val (Q : Nat) (e : Fin Q) :
    (numericRightEquiv Q (e, true)).val = 2 * e.val + 1 := by
  change 1 + 2 * e.val = 2 * e.val + 1
  exact Nat.add_comm _ _

/-- Original vertices, middle vertices, then interleaved `p_e,r_e`. -/
def numericVertexEquiv (n Q : Nat) :
    (Fin n ⊕ Fin Q) ⊕ (Fin Q × Bool) ≃ Fin (n + 3 * Q) :=
  ((Equiv.sumCongr
      (finSumFinEquiv : Fin n ⊕ Fin Q ≃ Fin (n + Q))
      (numericRightEquiv Q)).trans
    (finSumFinEquiv : Fin (n + Q) ⊕ Fin (Q * 2) ≃ Fin ((n + Q) + Q * 2))).trans
      (finCongr (by ring : (n + Q) + Q * 2 = n + 3 * Q))

@[simp] theorem numericVertexEquiv_original_val (n Q : Nat) (v : Fin n) :
    (numericVertexEquiv n Q (Sum.inl (Sum.inl v))).val = v.val := rfl

@[simp] theorem numericVertexEquiv_middle_val (n Q : Nat) (e : Fin Q) :
    (numericVertexEquiv n Q (Sum.inl (Sum.inr e))).val = n + e.val := rfl

@[simp] theorem numericVertexEquiv_p_val (n Q : Nat) (e : Fin Q) :
    (numericVertexEquiv n Q (Sum.inr (e, false))).val = n + Q + 2 * e.val := by
  change n + Q + (0 + 2 * e.val) = n + Q + 2 * e.val
  rw [Nat.zero_add]

@[simp] theorem numericVertexEquiv_r_val (n Q : Nat) (e : Fin Q) :
    (numericVertexEquiv n Q (Sum.inr (e, true))).val = n + Q + 2 * e.val + 1 := by
  change n + Q + (1 + 2 * e.val) = n + Q + 2 * e.val + 1
  omega

/-- The occurrence `e` occupies output indices `4e,4e+1,4e+2,4e+3`. -/
def numericEdgeEquiv (Q : Nat) : Fin (4 * Q) ≃ Fin Q × Fin 4 :=
  (finCongr (Nat.mul_comm 4 Q)).trans finProdFinEquiv.symm

@[simp] theorem numericEdgeEquiv_symm_val (Q : Nat) (e : Fin Q) (i : Fin 4) :
    ((numericEdgeEquiv Q).symm (e, i)).val = 4 * e.val + i.val := by
  change i.val + 4 * e.val = 4 * e.val + i.val
  exact Nat.add_comm _ _

end UniqueGamesTheorem.Explicit.SubdivisionTarget

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineUniformCopyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
An exact ordering bridge for uniform copies.

Largest-remainder output groups copies of each occurrence together. A fixed
whole-word copying machine instead repeats the entire occurrence list. These
lists are permutations, not equal serializations. The permutation preserves
every selected occurrence count and the target's actual `countSatisfied`.
-/

namespace UniqueGamesTheorem.MachineUniformCopyOrder

def copyMajor {α : Type*} (C : Nat) (edges : List α) : List α :=
  (List.replicate C edges).flatten

open UniqueGamesTheorem.Foundations.Target

end UniqueGamesTheorem.MachineUniformCopyOrder

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_UniformTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Explicit.UniformTarget

open UniqueGamesTheorem.Foundations Target Complexity
open UniqueGamesTheorem.Integration
open MachineUniformCopyOrder

theorem copy_length {α : Type*} (C : Nat) (xs : List α) :
    (copyMajor C xs).length = C * xs.length := by
  induction C with
  | zero => simp [copyMajor]
  | succ C ih =>
    simp [copyMajor, List.replicate_succ, List.flatten_cons, Nat.add_mul,
      Nat.add_comm]

end UniqueGamesTheorem.Explicit.UniformTarget

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_CleanupLemmas
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

abbrev Alphabet (_ : K) := Bool

/-- Reset both the ambient finite state and the drain register before exiting. -/
def finish (initial : σ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .load (fun _ => (initial, none))
    (match exit with | none => .halt | some label => .goto fun _ => label)

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Cleanup

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Lookup

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

/-- A fixed finite chain skips Boolean unary words. A true head causes one
additional delimiter pop; a false head is already the complete zero word.
Only the one-bit head register is examined. -/
def skipBits (source : K) : Nat →
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) →
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | 0, next => .load (fun state => (state.1, none)) next
  | count + 1, next =>
      let rest := skipBits source count next
      .pop source (fun state head => (state.1, head))
        (.branch (fun state => state.2.getD false)
          (.pop source (fun state _ => (state.1, none)) rest)
          (.load (fun state => (state.1, none)) rest))

inductive Label
  | guard | skipTail | skipReverse | skipPredicate | select | copy
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.guard, .skipTail, .skipReverse, .skipPredicate,
  .select, .copy]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev HeadTapes (K : Type) := Fin 6 → K

noncomputable def headTimePolynomial : Polynomial Nat :=
  Polynomial.C 7 * Polynomial.X + Polynomial.C 5

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Lookup

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_Emitter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual finite TM2 templates for affine unary fields and finite relation bits.
Commands write in forward bit order onto a stack, so their concatenated result
appears reversed in the accumulator. Every unbounded operand is read from an
isolated unary tape and restored by the checked preserving transducer.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Emitter

open Turing
open UniqueGamesTheorem.Foundations.Complexity

/-- All varying literals are finite: one Boolean or one bounded offset. -/
inductive Command (h : Nat) (σ : Type) (bound : Nat)
  | literal (word : List Bool)
  | bit (value : σ → Bool)
  | bounded (value : σ → Fin bound)
  | scaled (source : Fin h) (coefficient : Nat)
  | scaledIf (source : Fin h) (coefficient : Nat) (active : σ → Bool)

inductive Phase (bound : Nat)
  | entry | emit (symbol : Bool) | restore | offset (value : Fin bound)
  | scanIf (active : Bool) | emitIf (active symbol : Bool)
  deriving DecidableEq, Fintype

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (σ : Type) := (σ × Unit) × Option Bool

def transition (_ : Unit) (_ : Bool) : Unit := ()
def payload (coefficient : Nat) (_ : Unit) (symbol : Bool) : List Bool :=
  if symbol then List.replicate coefficient true else []

variable {K Λ σ : Type} {h bound : Nat} [DecidableEq K]

abbrev Label (count bound : Nat) := Fin (count + 1) × Phase bound

def labelAt (count bound r : Nat) (phase : Phase bound) : Label count bound :=
  (⟨min r count, by omega⟩, phase)

def commandAt {count : Nat} (commands : Fin count → Command h σ bound) (r : Nat) :
    Command h σ bound :=
  if hr : r < count then commands ⟨r, hr⟩ else .literal []

def resultTapes (output : K) (base : K → List Bool) (bits : List Bool) : K → List Bool :=
  Function.update base output (bits.reverse ++ base output)

@[simp] theorem resultTapes_output (output : K) (base : K → List Bool) (bits : List Bool) :
    resultTapes output base bits output = bits.reverse ++ base output := by
  simp [resultTapes]

def listCommands (commands : List (Command h σ bound)) :
    Fin commands.length → Command h σ bound := fun i => commands[i]

def affineCommands (terms : List (Fin h × Nat)) (offset : σ → Fin bound) :
    List (Command h σ bound) :=
  terms.map (fun term => .scaled term.1 term.2) ++ [.bounded offset, .literal [false]]

def affineValue (terms : List (Fin h × Nat)) (values : Fin h → Nat) (offset : Nat) : Nat :=
  (terms.map (fun term => term.2 * values term.1)).sum + offset

@[simp] theorem affineCommands_length (terms : List (Fin h × Nat)) (offset : σ → Fin bound) :
    (affineCommands terms offset).length = terms.length + 2 := by
  simp [affineCommands]

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Emitter

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_InitialGraphLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The initial finite constraint graph of an arbitrary concrete 3CNF formula.
Clause and variable vertices use one eight-element alphabet. Variable labels
are the canonical triples `(bit, false, false)`; clause labels are arbitrary
triples. Every incidence has two directed darts, including repeated names.
A tautological dummy loop keeps the graph nonempty for empty formulas.

Name compaction precedes the public construction. The resulting vertex count
is at most `4*m+1`, and the dart count is exactly `6*m+1`. Unsatisfiability gives
an inverse-size gap, not a constant gap. No PCP theorem is assumed or claimed.
-/

namespace UniqueGamesTheorem.Foundations.PCP.InitialGraph

open Target

abbrev Label := Bool × Bool × Bool
@[simp] theorem card_label : Fintype.card Label = 8 := by
  simp [Label, Fintype.card_prod]

def variableValid (label : Label) : Bool :=
  decide (label.2.1 = false ∧ label.2.2 = false)

end UniqueGamesTheorem.Foundations.PCP.InitialGraph

end

section

/-! Reversible regular port graphs and their actual finite walks. Vertices may
repeat; loops and parallel edges retain their distinct ports. The rotation
map sends an outgoing dart to its arrival dart and is an involution. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringWalks

structure PortGraph (V D : Type*) where
  rot : (V × D) ≃ (V × D)
  rot_involutive : Function.Involutive rot

abbrev Edge (V D : Type*) := V × D
abbrev Walk (V D : Type*) (t : Nat) := V × (Fin t → D)

variable {V D : Type*}

def next (G : PortGraph V D) (v : V) (d : D) : V := (G.rot (v, d)).1

@[simp] theorem rot_rot (G : PortGraph V D) (e : Edge V D) :
    G.rot (G.rot e) = e := G.rot_involutive e

def walkEnd (G : PortGraph V D) : V → List D → V
  | v, [] => v
  | v, d :: ds => walkEnd G (next G v d) ds

@[simp] theorem walkEnd_nil (G : PortGraph V D) (v : V) : walkEnd G v [] = v := rfl

@[simp] theorem walkEnd_cons (G : PortGraph V D) (v : V) (d : D) (ds : List D) :
    walkEnd G v (d :: ds) = walkEnd G (next G v d) ds := rfl

theorem walkEnd_append (G : PortGraph V D) (v : V) (as bs : List D) :
    walkEnd G v (as ++ bs) = walkEnd G (walkEnd G v as) bs := by
  induction as generalizing v with
  | nil => rfl
  | cons d ds ih => exact ih (next G v d)

/-- Exposes the first dart and the independent remaining port word. -/
def splitHead (V D : Type*) (n : Nat) :
    Walk V D (n + 1) ≃ ((V × D) × (Fin n → D)) where
  toFun w := ((w.1, w.2 0), fun j => w.2 j.succ)
  invFun z := (z.1.1, Fin.cases z.1.2 z.2)
  left_inv w := by
    apply Prod.ext
    · rfl
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

/-- Advance across the first edge while retaining its reverse port. -/
def rotateHead (G : PortGraph V D) (n : Nat) : Walk V D (n + 1) ≃ Walk V D (n + 1) :=
  (splitHead V D n).trans
    ((Equiv.prodCongr G.rot (Equiv.refl (Fin n → D))).trans (splitHead V D n).symm)

@[simp] theorem rotateHead_vertex (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1)) :
    (rotateHead G n w).1 = next G w.1 (w.2 0) := rfl

@[simp] theorem rotateHead_zero (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1)) :
    (rotateHead G n w).2 0 = (G.rot (w.1, w.2 0)).2 := rfl

@[simp] theorem rotateHead_succ (G : PortGraph V D) (n : Nat)
    (w : Walk V D (n + 1)) (j : Fin n) :
    (rotateHead G n w).2 j.succ = w.2 j.succ := rfl

def wordEnd (G : PortGraph V D) : (n : Nat) → V → (Fin n → D) → V
  | 0, v, _ => v
  | n + 1, v, p => wordEnd G n (next G v (p 0)) (fun j => p j.succ)

def endpoint (G : PortGraph V D) {n : Nat} (w : Walk V D n) : V :=
  wordEnd G n w.1 w.2

def advanceTail {n : Nat} (G : PortGraph V D) (w : Walk V D (n + 1)) : Walk V D n :=
  ((G.rot (w.1, w.2 0)).1, fun j => w.2 j.succ)

/-- The dart at the indicated time, computed by the actual preceding steps. -/
def edgeAt (G : PortGraph V D) :
    (n : Nat) → Walk V D (n + 1) → Fin (n + 1) → Edge V D
  | 0, w, _ => (w.1, w.2 0)
  | n + 1, w, k => Fin.cases (w.1, w.2 0)
      (fun j => edgeAt G n (advanceTail G w) j) k

end UniqueGamesTheorem.Foundations.PCP.PoweringWalks

end

section

/-!
Cloud replacement for arbitrary finite constraint graphs. The new vertices are
the old darts; internal ports enforce equality inside each cloud, and one
external port applies the original constraint. Dummy loop darts allow padding
each cloud independently before replacement.

The supplied cloud port graphs are explicit parameters; no expansion or
soundness claim is assumed.
-/

open scoped BigOperators

namespace UniqueGamesTheorem.Foundations.PCP.DegreeReplacement

open PoweringWalks

variable {V E A D : Type*}

/-- The darts departing a specified vertex. -/
abbrev Cloud (G : ConstraintGraph V E A) (v : V) := {e : E // G.tail e = v}

def cloudIndexEquiv (G : ConstraintGraph V E A) :
    (E × D) ≃ (Σ v : V, Cloud G v × D) where
  toFun p := ⟨G.tail p.1, (⟨p.1, rfl⟩, p.2)⟩
  invFun p := (p.2.1.val, p.2.2)
  left_inv _ := rfl
  right_inv := by
    rintro ⟨v, ⟨⟨e, he⟩, d⟩⟩
    cases he
    rfl

def cloudRotation (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    (Σ v : V, Cloud G v × D) ≃ (Σ v : V, Cloud G v × D) :=
  Equiv.sigmaCongrRight (fun v => (H v).rot)

theorem cloudRotation_involutive (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    Function.Involutive (cloudRotation G H) := by
  rintro ⟨v, p⟩
  change (⟨v, (H v).rot ((H v).rot p)⟩ : Σ v : V, Cloud G v × D) = ⟨v, p⟩
  rw [(H v).rot_involutive p]

/-- Conjugate the disjoint union of cloud rotations into global dart coordinates. -/
def innerRotation (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) : (E × D) ≃ (E × D) :=
  ((cloudIndexEquiv G).trans (cloudRotation G H)).trans (cloudIndexEquiv G).symm

theorem innerRotation_involutive (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    Function.Involutive (innerRotation G H) := by
  intro p
  apply (cloudIndexEquiv G).injective
  simp only [innerRotation, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact cloudRotation_involutive G H _

theorem innerRotation_tail (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (e : E) (d : D) :
    G.tail (innerRotation G H (e, d)).1 = G.tail e := by
  change G.tail (((H (G.tail e)).rot (⟨e, rfl⟩, d)).1.val) = G.tail e
  exact ((H (G.tail e)).rot (⟨e, rfl⟩, d)).1.property

/-- Internal ports rotate inside a cloud; the extra port reverses an old dart. -/
def replacementStep (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) : E × (D ⊕ Unit) → E × (D ⊕ Unit)
  | (e, Sum.inl d) =>
      let p := innerRotation G H (e, d)
      (p.1, Sum.inl p.2)
  | (e, Sum.inr u) => (G.reverse e, Sum.inr u)

theorem replacementStep_involutive (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    Function.Involutive (replacementStep G H) := by
  rintro ⟨e, p⟩
  rcases p with d | u
  · change ((innerRotation G H (innerRotation G H (e, d))).1,
        (Sum.inl ((innerRotation G H (innerRotation G H (e, d))).2) : D ⊕ Unit)) =
      (e, Sum.inl d)
    rw [innerRotation_involutive G H (e, d)]
  · change (G.reverse (G.reverse e), (Sum.inr u : D ⊕ Unit)) = (e, Sum.inr u)
    rw [G.reverse_involutive e]

def replacementPortGraph (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) : PortGraph E (D ⊕ Unit) where
  rot :=
    { toFun := replacementStep G H
      invFun := replacementStep G H
      left_inv := replacementStep_involutive G H
      right_inv := replacementStep_involutive G H }
  rot_involutive := replacementStep_involutive G H

/-- The equality constraints and inherited original constraints on the actual rotation. -/
def replacementGraph [DecidableEq A] (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    ConstraintGraph E (E × (D ⊕ Unit)) A where
  reverse := (replacementPortGraph G H).rot
  reverse_involutive := (replacementPortGraph G H).rot_involutive
  tail := Prod.fst
  accepts p a b := match p.2 with
    | Sum.inl _ => decide (a = b)
    | Sum.inr _ => G.accepts p.1 a b
  reverse_accepts := by
    rintro ⟨e, p⟩ a b
    rcases p with d | u
    · change decide (b = a) = decide (a = b)
      simp [eq_comm]
    · exact G.reverse_accepts e a b

def liftLabel (G : ConstraintGraph V E A) (labeling : V → A) : E → A :=
  fun e => labeling (G.tail e)

@[simp] theorem replacement_satisfied_inl [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (labeling : V → A) (e : E) (d : D) :
    (replacementGraph G H).edgeSatisfied (liftLabel G labeling) (e, Sum.inl d) =
      true := by
  change decide (labeling (G.tail e) =
    labeling (G.tail (innerRotation G H (e, d)).1)) = true
  rw [innerRotation_tail G H e d]
  simp

@[simp] theorem replacement_satisfied_inr [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (labeling : V → A) (e : E) (u : Unit) :
    (replacementGraph G H).edgeSatisfied (liftLabel G labeling) (e, Sum.inr u) =
      G.edgeSatisfied labeling e := rfl

/-- Additional darts are attached to their specified original vertex. -/
abbrev PaddedDart (_G : ConstraintGraph V E A) (dummy : V → Type*) :=
  E ⊕ (Σ v : V, dummy v)

def paddedOwner (G : ConstraintGraph V E A) (dummy : V → Type*) :
    PaddedDart G dummy → V
  | Sum.inl e => G.tail e
  | Sum.inr z => z.1

def paddedReverse (G : ConstraintGraph V E A) (dummy : V → Type*) :
    PaddedDart G dummy ≃ PaddedDart G dummy :=
  Equiv.sumCongr G.reverse (Equiv.refl (Σ v : V, dummy v))

theorem paddedReverse_involutive (G : ConstraintGraph V E A) (dummy : V → Type*) :
    Function.Involutive (paddedReverse G dummy) := by
  intro z
  cases z with
  | inl e =>
    change (Sum.inl (G.reverse (G.reverse e)) : PaddedDart G dummy) = Sum.inl e
    rw [G.reverse_involutive e]
  | inr z => rfl

/-- Dummy darts are self-reversing loops with an always-accepting constraint. -/
def paddedGraph (G : ConstraintGraph V E A) (dummy : V → Type*) :
    ConstraintGraph V (PaddedDart G dummy) A where
  reverse := paddedReverse G dummy
  reverse_involutive := paddedReverse_involutive G dummy
  tail := paddedOwner G dummy
  accepts e a b := match e with
    | Sum.inl e => G.accepts e a b
    | Sum.inr _ => true
  reverse_accepts := by
    intro e a b
    cases e with
    | inl e => exact G.reverse_accepts e a b
    | inr z => rfl

@[simp] theorem padded_satisfied_inl (G : ConstraintGraph V E A)
    (dummy : V → Type*) (labeling : V → A) (e : E) :
    (paddedGraph G dummy).edgeSatisfied labeling (Sum.inl e) =
      G.edgeSatisfied labeling e := rfl

@[simp] theorem padded_satisfied_inr (G : ConstraintGraph V E A)
    (dummy : V → Type*) (labeling : V → A) (z : Σ v : V, dummy v) :
    (paddedGraph G dummy).edgeSatisfied labeling (Sum.inr z) = true := rfl

def paddedReplacementPortGraph (G : ConstraintGraph V E A) (dummy : V → Type*)
    (H : ∀ v, PortGraph (Cloud (paddedGraph G dummy) v) D) :
    PortGraph (PaddedDart G dummy) (D ⊕ Unit) :=
  replacementPortGraph (paddedGraph G dummy) H

def paddedReplacementGraph [DecidableEq A]
    (G : ConstraintGraph V E A) (dummy : V → Type*)
    (H : ∀ v, PortGraph (Cloud (paddedGraph G dummy) v) D) :
    ConstraintGraph (PaddedDart G dummy) (PaddedDart G dummy × (D ⊕ Unit)) A :=
  replacementGraph (paddedGraph G dummy) H

end UniqueGamesTheorem.Foundations.PCP.DegreeReplacement

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PoweringLabelsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Full-radius local opinions use a common alphabet indexed by bounded
port addresses. Every opinion is decoded through a fixed address selector;
arbitrary alphabet symbols need not agree on colliding addresses. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringLabels

open PoweringWalks
open scoped BigOperators

variable {V D A : Type*}

abbrev PortWords (D : Type*) (t : Nat) := (n : Fin (t + 1)) × (Fin n.val → D)

def Ball (G : PortGraph V D) (t : Nat) (v : V) :=
  {u : V // ∃ n, n ≤ t ∧ ∃ p : Fin n → D, wordEnd G n v p = u}

def wordToBall (G : PortGraph V D) (t : Nat) (v : V) (w : PortWords D t) : Ball G t v :=
  ⟨wordEnd G w.1.val v w.2, w.1.val, Nat.le_of_lt_succ w.1.isLt, w.2, rfl⟩

theorem wordToBall_surjective (G : PortGraph V D) (t : Nat) (v : V) :
    Function.Surjective (wordToBall G t v) := by
  intro u
  obtain ⟨n, hn, p, hp⟩ := u.property
  refine ⟨⟨⟨n, Nat.lt_succ_of_le hn⟩, p⟩, ?_⟩
  exact Subtype.ext hp

structure AddressSelector (G : PortGraph V D) (t : Nat) (v : V) where
  address : Ball G t v → PortWords D t
  correct : ∀ u, wordToBall G t v (address u) = u

/-- Executable first-match search, with a proof that a match is present. -/
def scanWitness {A : Type*} (p : A → Prop) [DecidablePred p] :
    (xs : List A) → (∃ a ∈ xs, p a) → {a // p a}
  | [], h => False.elim (by simp at h)
  | a :: xs, h =>
    if ha : p a then ⟨a, ha⟩ else
      scanWitness p xs (by
        obtain ⟨b, hb, hp⟩ := h
        rcases List.mem_cons.mp hb with he | hm
        · exact False.elim (ha (he ▸ hp))
        · exact ⟨b, hm, hp⟩)

/-- A concrete complete address list supplies a computational selector. Its
length depends on the degree and radius, not on the ambient vertex count. -/
def listSelector [DecidableEq V] (G : PortGraph V D) (t : Nat) (v : V)
    (addresses : List (PortWords D t)) (complete : ∀ w, w ∈ addresses) :
    AddressSelector G t v where
  address u := (scanWitness (fun w => (wordToBall G t v w).val = u.val) addresses (by
    obtain ⟨w, hw⟩ := wordToBall_surjective G t v u
    exact ⟨w, complete w, congrArg Subtype.val hw⟩)).val
  correct u := Subtype.ext (scanWitness
    (fun w => (wordToBall G t v w).val = u.val) addresses (by
      obtain ⟨w, hw⟩ := wordToBall_surjective G t v u
      exact ⟨w, complete w, congrArg Subtype.val hw⟩)).property

abbrev PaddedLabel (D : Type*) (t : Nat) (A : Type*) := PortWords D t → A

def decode {G : PortGraph V D} {t : Nat} {v : V} (S : AddressSelector G t v)
    (a : PaddedLabel D t A) : Ball G t v → A := fun u => a (S.address u)

end UniqueGamesTheorem.Foundations.PCP.PoweringLabels

end

section

/-!
# Executable bounded port-address enumeration

For a port alphabet `Fin d`, the lists below enumerate every word of every
length at most the fixed radius. The resulting first-match selector searches
these addresses and never enumerates the ambient vertex type.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringAddresses

open PoweringWalks PoweringLabels
open scoped BigOperators

variable {V : Type*}

/-- All words of a specified length, ordered first by their head port. -/
def allWords (d : Nat) : (n : Nat) → List (Fin n → Fin d)
  | 0 => [Fin.elim0]
  | n + 1 => (List.finRange d).flatMap fun a =>
      (allWords d n).map fun p => Fin.cases a p

theorem mem_allWords (d : Nat) :
    ∀ n (p : Fin n → Fin d), p ∈ allWords d n := by
  intro n
  induction n with
  | zero =>
    intro p
    simp only [allWords, List.mem_singleton]
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    intro p
    simp only [allWords, List.mem_flatMap, List.mem_map]
    refine ⟨p 0, List.mem_finRange (p 0), (fun j => p j.succ), ih _, ?_⟩
    funext j
    exact Fin.cases rfl (fun _ => rfl) j

/-- The complete address list, including the unique empty word. -/
def allAddresses (d t : Nat) : List (PortWords (Fin d) t) :=
  (List.finRange (t + 1)).flatMap fun n =>
    (allWords d n.val).map fun p => Sigma.mk n p

theorem mem_allAddresses (d t : Nat) (w : PortWords (Fin d) t) :
    w ∈ allAddresses d t := by
  rcases w with ⟨n, p⟩
  unfold allAddresses
  apply List.mem_flatMap.mpr
  refine ⟨n, List.mem_finRange n, ?_⟩
  exact List.mem_map.mpr ⟨p, mem_allWords d n.val p, rfl⟩

/-- A fully executable selector from the explicit bounded address list. -/
def finitePortSelector {d : Nat} [DecidableEq V] (G : PortGraph V (Fin d))
    (t : Nat) (v : V) : AddressSelector G t v :=
  listSelector G t v (allAddresses d t) (mem_allAddresses d t)

end UniqueGamesTheorem.Foundations.PCP.PoweringAddresses

end

section

/-!
# Executable integer encodings for the powering construction

All encodings below have explicit inverses. They use the arithmetic finite
function, sigma, and product equivalences rather than choosing enumerations
from cardinality proofs. Word digits use the head-major convention; addresses
are grouped by increasing word length. A dart is numbered first by its vertex,
then its word, with its two orientations adjacent.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringEnumeration

open PoweringLabels
open scoped BigOperators

/-- The number of words with length at most `t`, including the empty word. -/
def addressCount (d t : Nat) : Nat := ∑ i : Fin (t + 1), d ^ i.val

/-- Reverse the digit positions before using the little-endian arithmetic
encoding from mathlib. Both directions are the same executable operation. -/
def reverseWordEquiv (d n : Nat) : (Fin n → Fin d) ≃ (Fin n → Fin d) where
  toFun p i := p i.rev
  invFun p i := p i.rev
  left_inv p := by funext i; simp only [Fin.rev_rev]
  right_inv p := by funext i; simp only [Fin.rev_rev]

/-- An executable bijection from fixed-length port words to their ranks. -/
def wordEquiv (d n : Nat) : (Fin n → Fin d) ≃ Fin (d ^ n) :=
  (reverseWordEquiv d n).trans finFunctionFinEquiv

/-- Arithmetic prefix sums give a rank for every bounded-length address. -/
def addressEquiv (d t : Nat) : PortWords (Fin d) t ≃ Fin (addressCount d t) :=
  (Equiv.sigmaCongrRight (fun i : Fin (t + 1) => wordEquiv d i.val)).trans
    finSigmaFinEquiv

/-- A padded label is a base-`q` integer whose digits are indexed by the
explicit bounded-address equivalence. -/
def paddedLabelEquiv (d t q : Nat) :
    PaddedLabel (Fin d) t (Fin q) ≃ Fin (q ^ addressCount d t) :=
  ((addressEquiv d t).arrowCongr (Equiv.refl (Fin q))).trans
    (wordEquiv q (addressCount d t))

/-- False and true are the adjacent orientation digits zero and one. -/
def orientationEquiv : Bool ≃ Fin 2 := finTwoEquiv.symm

@[simp] theorem orientationEquiv_false : orientationEquiv false = 0 := rfl
@[simp] theorem orientationEquiv_true : orientationEquiv true = 1 := rfl

/-- A vertex's block consists of one adjacent orientation pair per word. -/
def dartBlockEquiv (d n : Nat) :
    ((Fin (n + 1) → Fin d) × Bool) ≃ Fin (2 * d ^ (n + 1)) :=
  ((wordEquiv d (n + 1)).prodCongr orientationEquiv).trans
    (finProdFinEquiv.trans (finCongr (Nat.mul_comm (d ^ (n + 1)) 2)))

/-- The tuple permutation putting the vertex before its word and orientation. -/
def dartVertexEquiv (vertices d n : Nat) :
    (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) ≃
      (Fin vertices × ((Fin (n + 1) → Fin d) × Bool)) where
  toFun x := (x.2.1, (x.2.2, x.1))
  invFun x := (x.2.2, (x.1, x.2.1))
  left_inv x := by rcases x with ⟨b, v, p⟩; rfl
  right_inv x := by rcases x with ⟨v, p, b⟩; rfl

/-- Executable vertex-major dart numbering, with adjacent orientations. -/
def dartEquiv (vertices d n : Nat) :
    (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) ≃
      Fin (2 * vertices * d ^ (n + 1)) :=
  (dartVertexEquiv vertices d n).trans
    (((Equiv.refl (Fin vertices)).prodCongr (dartBlockEquiv d n)).trans
      (finProdFinEquiv.trans
        (finCongr (show vertices * (2 * d ^ (n + 1)) =
          2 * vertices * d ^ (n + 1) by ac_rfl))))

def decodeWord (d n : Nat) : Fin (d ^ n) → (Fin n → Fin d) := (wordEquiv d n).symm

def encodeAddress (d t : Nat) : PortWords (Fin d) t → Fin (addressCount d t) :=
  addressEquiv d t

def encodeLabel (d t q : Nat) :
    PaddedLabel (Fin d) t (Fin q) → Fin (q ^ addressCount d t) := paddedLabelEquiv d t q

def decodeLabel (d t q : Nat) :
    Fin (q ^ addressCount d t) → PaddedLabel (Fin d) t (Fin q) :=
  (paddedLabelEquiv d t q).symm

@[simp] theorem decodeLabel_encodeLabel (d t q : Nat) (a : PaddedLabel (Fin d) t (Fin q)) :
    decodeLabel d t q (encodeLabel d t q a) = a := (paddedLabelEquiv d t q).symm_apply_apply a

@[simp] theorem encodeLabel_decodeLabel (d t q : Nat) (i : Fin (q ^ addressCount d t)) :
    encodeLabel d t q (decodeLabel d t q i) = i := (paddedLabelEquiv d t q).apply_symm_apply i

@[simp] theorem decodeLabel_apply (d t q : Nat) (i : Fin (q ^ addressCount d t))
    (w : PortWords (Fin d) t) :
    decodeLabel d t q i w = decodeWord q (addressCount d t) i (encodeAddress d t w) := rfl

end UniqueGamesTheorem.Foundations.PCP.PoweringEnumeration

end

section

/-!
# Full-radius access to the endpoints of each actual walk edge

The tail of each traversed edge is reachable from the walk's start. Its head
is reachable from the walk's end by reversing the remaining suffix with the
actual arrival ports. These facts supply values in the two neighborhood-ball
types used by the endpoint label decoders.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringReach

open PoweringWalks PoweringLabels

variable {V D : Type*}

def ReachLE (G : PortGraph V D) (t : Nat) (u v : V) : Prop :=
  ∃ l, l ≤ t ∧ ∃ p : Fin l → D, wordEnd G l u p = v

theorem reach_refl (G : PortGraph V D) (t : Nat) (u : V) : ReachLE G t u u :=
  ⟨0, Nat.zero_le t, Fin.elim0, rfl⟩

theorem reach_mono {G : PortGraph V D} {s t : Nat} {u v : V}
    (hst : s ≤ t) (h : ReachLE G s u v) : ReachLE G t u v := by
  obtain ⟨l, hl, p, hp⟩ := h
  exact ⟨l, hl.trans hst, p, hp⟩

theorem reach_prepend (G : PortGraph V D) {t : Nat} (u : V) (d : D) {v : V}
    (h : ReachLE G t (next G u d) v) : ReachLE G (t + 1) u v := by
  obtain ⟨l, hl, p, hp⟩ := h
  refine ⟨l + 1, Nat.succ_le_succ hl,
    (fun i : Fin (l + 1) => Fin.cases d p i), ?_⟩
  simpa only [wordEnd, Fin.cases_zero, Fin.cases_succ] using hp

/-- Reversal records each arrival port, not the original outgoing port. -/
def reversePorts (G : PortGraph V D) : V → List D → List D
  | _, [] => []
  | v, d :: ds => reversePorts G (next G v d) ds ++ [(G.rot (v, d)).2]

theorem reversePorts_length (G : PortGraph V D) (v : V) (ds : List D) :
    (reversePorts G v ds).length = ds.length := by
  induction ds generalizing v with
  | nil => rfl
  | cons d ds ih => simp [reversePorts, ih]

theorem walkEnd_reversePorts (G : PortGraph V D) (v : V) (ds : List D) :
    walkEnd G (walkEnd G v ds) (reversePorts G v ds) = v := by
  induction ds generalizing v with
  | nil => rfl
  | cons d ds ih =>
    change walkEnd G (walkEnd G (next G v d) ds)
      (reversePorts G (next G v d) ds ++ [(G.rot (v, d)).2]) = v
    rw [walkEnd_append, ih]
    change (G.rot (G.rot (v, d))).1 = v
    exact congrArg Prod.fst (G.rot_involutive (v, d))

theorem wordEnd_eq_walkEnd_ofFn (G : PortGraph V D) :
    ∀ n v (p : Fin n → D), wordEnd G n v p = walkEnd G v (List.ofFn p) := by
  intro n
  induction n with
  | zero => intro v p; rfl
  | succ n ih =>
    intro v p
    rw [List.ofFn_succ, walkEnd_cons]
    exact ih (next G v (p 0)) (fun j => p j.succ)

theorem reach_reverse {G : PortGraph V D} {t : Nat} {u v : V}
    (h : ReachLE G t u v) : ReachLE G t v u := by
  obtain ⟨l, hl, p, hp⟩ := h
  refine ⟨(reversePorts G u (List.ofFn p)).length, ?_,
    (reversePorts G u (List.ofFn p)).get, ?_⟩
  · simpa only [reversePorts_length, List.length_ofFn] using hl
  · rw [wordEnd_eq_walkEnd_ofFn, List.ofFn_get]
    have hlist : walkEnd G u (List.ofFn p) = v := by
      rw [← wordEnd_eq_walkEnd_ofFn]
      exact hp
    rw [← hlist, walkEnd_reversePorts]

/-- The actual prefix places each traversed edge's tail in the start ball. -/
theorem tail_reach (G : PortGraph V D) :
    ∀ (n : Nat) (w : Walk V D (n + 1)) (k : Fin (n + 1)),
      ReachLE G (n + 1) w.1 (edgeAt G n w k).1 := by
  intro n
  induction n with
  | zero =>
    intro w k
    exact reach_refl G 1 w.1
  | succ n ih =>
    intro w k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact reach_refl G (n + 2) w.1
    · exact reach_prepend G w.1 (w.2 0) (ih (advanceTail G w) j)

/-- The suffix proceeds from the traversed edge's head to the walk endpoint. -/
theorem head_reach_endpoint (G : PortGraph V D) :
    ∀ (n : Nat) (w : Walk V D (n + 1)) (k : Fin (n + 1)),
      ReachLE G (n + 1) (G.rot (edgeAt G n w k)).1 (endpoint G w) := by
  intro n
  induction n with
  | zero =>
    intro w k
    exact reach_refl G 1 (G.rot (w.1, w.2 0)).1
  | succ n ih =>
    intro w k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact ⟨n + 1, Nat.le_succ (n + 1), (fun j => w.2 j.succ), rfl⟩
    · exact reach_mono (Nat.le_succ (n + 1)) (ih (advanceTail G w) j)

def tailFromStart (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1))
    (k : Fin (n + 1)) : Ball G (n + 1) w.1 :=
  ⟨(edgeAt G n w k).1, tail_reach G n w k⟩

def headFromEnd (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1))
    (k : Fin (n + 1)) : Ball G (n + 1) (endpoint G w) :=
  ⟨(G.rot (edgeAt G n w k)).1, reach_reverse (head_reach_endpoint G n w k)⟩

@[simp] theorem tailFromStart_val (G : PortGraph V D) (n : Nat)
    (w : Walk V D (n + 1)) (k : Fin (n + 1)) :
    (tailFromStart G n w k).val = (edgeAt G n w k).1 := rfl

@[simp] theorem headFromEnd_val (G : PortGraph V D) (n : Nat)
    (w : Walk V D (n + 1)) (k : Fin (n + 1)) :
    (headFromEnd G n w k).val = (G.rot (edgeAt G n w k)).1 := rfl

end UniqueGamesTheorem.Foundations.PCP.PoweringReach

end

section

/-!
An actual incidence constraint graph for a finite Boolean verifier with q queries.
Left labels are complete local answer tuples. Their validity includes consistency
at repeated proof addresses. A dart checks the tuple at the least position naming
its proof address. Both sides use the same 2^q-element alphabet; arbitrary right
labels are explicitly decoded by their first coordinate, and honest right labels
are constant tuples. Every incidence is represented by two opposite darts.

The count theorem proves a loss of exactly q in a supplied verifier rejection
fraction. It supplies a concrete construction, not a PCP-hardness premise. The
generic count statements permit an empty event type and introduce no dummy darts.
-/

namespace UniqueGamesTheorem.Foundations.PCP.QueryIncidence

structure Verifier (E X : Type*) (q : Nat) where
  query : E → Fin q → X
  accepts : E → (Fin q → Bool) → Bool

abbrev Label (q : Nat) := Fin q → Bool
abbrev Vertex (E X : Type*) := E ⊕ X
abbrev Dart (E : Type*) (q : Nat) := (E × Fin q) × Bool

variable {E X : Type*} {q : Nat}

def zeroSlot (positive : 0 < q) : Fin q := ⟨0, positive⟩

def decodeRight (positive : 0 < q) (label : Label q) : Bool := label (zeroSlot positive)

def encodeRight (bit : Bool) : Label q := fun _ => bit

@[simp] theorem decode_encodeRight (positive : 0 < q) (bit : Bool) :
    decodeRight positive (encodeRight bit) = bit := rfl

def canonicalSlot [DecidableEq X] (T : Verifier E X q) (event : E) (i : Fin q) : Fin q :=
  Fin.find (fun j => T.query event j = T.query event i) ⟨i, rfl⟩

def RepeatedConsistent (T : Verifier E X q) (event : E) (label : Label q) : Prop :=
  ∀ i j, T.query event i = T.query event j → label i = label j

instance repeatedConsistentDecidable [DecidableEq X]
    (T : Verifier E X q) (event : E) (label : Label q) :
    Decidable (RepeatedConsistent T event label) := by
  unfold RepeatedConsistent
  infer_instance

def LeftValid (T : Verifier E X q) (event : E) (label : Label q) : Prop :=
  T.accepts event label = true ∧ RepeatedConsistent T event label

instance leftValidDecidable [DecidableEq X]
    (T : Verifier E X q) (event : E) (label : Label q) :
    Decidable (LeftValid T event label) := by
  unfold LeftValid
  infer_instance

def incidenceAccept [DecidableEq X] (T : Verifier E X q) (positive : 0 < q)
    (event : E) (slot : Fin q) (left right : Label q) : Bool :=
  decide (LeftValid T event left) &&
    decide (left (canonicalSlot T event slot) = decodeRight positive right)

def reverse : Dart E q → Dart E q := fun d => (d.1, !d.2)

theorem reverse_involutive : Function.Involutive (reverse : Dart E q → Dart E q) := by
  rintro ⟨⟨event, slot⟩, orientation⟩
  cases orientation <;> rfl

def reverseEquiv : Dart E q ≃ Dart E q where
  toFun := reverse
  invFun := reverse
  left_inv := reverse_involutive
  right_inv := reverse_involutive

def tail (T : Verifier E X q) : Dart E q → Vertex E X
  | ((event, _), false) => .inl event
  | ((event, slot), true) => .inr (T.query event slot)

def predicate [DecidableEq X] (T : Verifier E X q) (positive : 0 < q) :
    Dart E q → Label q → Label q → Bool
  | ((event, slot), false), a, b => incidenceAccept T positive event slot a b
  | ((event, slot), true), a, b => incidenceAccept T positive event slot b a

def graph [DecidableEq X] (T : Verifier E X q) (positive : 0 < q) :
    ConstraintGraph (Vertex E X) (Dart E q) (Label q) where
  reverse := reverseEquiv
  reverse_involutive := reverse_involutive
  tail := tail T
  accepts := predicate T positive
  reverse_accepts := by
    rintro ⟨⟨event, slot⟩, orientation⟩ a b
    cases orientation <;> rfl

@[simp] theorem card_label (q : Nat) : Fintype.card (Label q) = 2 ^ q := by
  simp [Label]

@[simp] theorem card_vertex [Fintype E] [Fintype X] :
    Fintype.card (Vertex E X) = Fintype.card E + Fintype.card X := by
  simp [Vertex, Fintype.card_sum]

@[simp] theorem card_dart [Fintype E] :
    Fintype.card (Dart E q) = 2 * q * Fintype.card E := by
  simp [Dart, Fintype.card_prod, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

end UniqueGamesTheorem.Foundations.PCP.QueryIncidence

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_AlphabetRetractionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Pull a graph predicate back through a surjective label decoder.  This preserves
every rejection count after decoding.  A concrete section embeds the initial
eight-label graph into the fixed 64-label alphabet used throughout amplification.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetRetraction

variable {V E A B : Type*}

def pullback (G : ConstraintGraph V E A) (decode : B → A) : ConstraintGraph V E B where
  reverse := G.reverse
  reverse_involutive := G.reverse_involutive
  tail := G.tail
  accepts := fun e b c => G.accepts e (decode b) (decode c)
  reverse_accepts := fun e b c => G.reverse_accepts e (decode b) (decode c)

@[simp] theorem edgeSatisfied_pullback (G : ConstraintGraph V E A)
    (decode : B → A) (labeling : V → B) (e : E) :
    (pullback G decode).edgeSatisfied labeling e =
      G.edgeSatisfied (decode ∘ labeling) e := rfl

@[simp] theorem rejectionCount_pullback [Fintype E] (G : ConstraintGraph V E A)
    (decode : B → A) (labeling : V → B) :
    (pullback G decode).rejectionCount labeling =
      G.rejectionCount (decode ∘ labeling) := rfl

abbrev Label64 := QueryIncidence.Label 6

def decode64 (label : Label64) : InitialGraph.Label := (label 0, label 1, label 2)

def encode64 (label : InitialGraph.Label) : Label64 :=
  fun i => if i = 0 then label.1 else if i = 1 then label.2.1 else label.2.2

@[simp] theorem decode_encode64 (label : InitialGraph.Label) :
    decode64 (encode64 label) = label := by
  rcases label with ⟨a, b, c⟩
  rfl

end UniqueGamesTheorem.Foundations.PCP.AlphabetRetraction

end

section

namespace UniqueGamesTheorem.Foundations.PCP.SpectralReturn

open PoweringWalks
open scoped BigOperators

noncomputable section

def averagingOperator {V D : Type*} [Fintype D] (G : PortGraph V D)
    (f : V → ℝ) (v : V) : ℝ := Finset.univ.expect (fun d => f (G.rot (v, d)).1)

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
open PoweringWalks

variable {I D : Type*}

def zeroFrequency : Cube I := fun _ => false

theorem cubeXor_cancel_right (x y : Cube I) :
    cubeXor (cubeXor x y) y = x := by
  funext i
  cases hx : x i <;> cases hy : y i <;> simp [cubeXor, hx, hy]

@[simp] theorem cubeXor_zeroFrequency (x : Cube I) :
    cubeXor x zeroFrequency = x := by
  funext i
  cases hx : x i <;> simp [cubeXor, zeroFrequency, hx]

def rotate (g : D → Cube I) (p : Cube I × D) : Cube I × D :=
  (cubeXor p.1 (g p.2), p.2)

theorem rotate_involutive (g : D → Cube I) : Function.Involutive (rotate g) := by
  rintro ⟨x, d⟩
  change (cubeXor (cubeXor x (g d)) (g d), d) = (x, d)
  rw [cubeXor_cancel_right]

/-- The undirected regular port graph generated by the indexed cube vectors. -/
def cayleyGraph (g : D → Cube I) : PortGraph (Cube I) D where
  rot :=
    { toFun := rotate g
      invFun := rotate g
      left_inv := rotate_involutive g
      right_inv := rotate_involutive g }
  rot_involutive := rotate_involutive g

@[simp] theorem cayleyGraph_rot (g : D → Cube I) (x : Cube I) (d : D) :
    (cayleyGraph g).rot (x, d) = (cubeXor x (g d), d) := rfl

section Finite

variable [Fintype I] [DecidableEq I] [Fintype D]

/-- Average along the actual outgoing ports of the Cayley graph. -/
def cayleyAverage (g : D → Cube I) (f : Cube I → ℝ) (x : Cube I) : ℝ :=
  𝔼 d, f ((cayleyGraph g).rot (x, d)).1

omit [Fintype I] [DecidableEq I] in
@[simp] theorem averagingOperator_cayleyGraph (g : D → Cube I) (f : Cube I → ℝ) :
    SpectralReturn.averagingOperator (cayleyGraph g) f = cayleyAverage g f := rfl

@[simp] theorem coefficient_zeroFrequency (f : Cube I → ℝ) :
    coefficient f zeroFrequency = 𝔼 x, f x := by
  simp [coefficient, zeroFrequency, walsh, bitSign]

end Finite

end UniqueGamesTheorem.Foundations.PCP.CayleySpectral

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_ExpandersLemmas
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

def initialDegree : Nat := 2 ^ 16
def basePower : Nat := 7

def baseDegree : Nat := initialDegree ^ basePower

end UniqueGamesTheorem.Foundations.PCP.Expanders

/-! Exact changes of finite vertex and port coordinates. The graph rotation and
its normalized averaging operator are transported by the same equivalences. -/

namespace UniqueGamesTheorem.Foundations.PCP.GraphTransport

open PoweringWalks SpectralReturn

variable {V W D E : Type*}

def reindex (G : PortGraph V D) (vertices : V ≃ W) (ports : D ≃ E) :
    PortGraph W E where
  rot := (Equiv.prodCongr vertices ports).symm.trans
    (G.rot.trans (Equiv.prodCongr vertices ports))
  rot_involutive := by
    intro x
    change (Equiv.prodCongr vertices ports)
        (G.rot ((Equiv.prodCongr vertices ports).symm
          ((Equiv.prodCongr vertices ports)
            (G.rot ((Equiv.prodCongr vertices ports).symm x))))) = x
    rw [Equiv.symm_apply_apply, G.rot_involutive, Equiv.apply_symm_apply]

@[simp] theorem reindex_rot (G : PortGraph V D) (vertices : V ≃ W)
    (ports : D ≃ E) (v : V) (d : D) :
    (reindex G vertices ports).rot (vertices v, ports d) =
      (vertices (G.rot (v, d)).1, ports (G.rot (v, d)).2) := by
  simp [reindex, Equiv.trans_apply, Prod.map]

end UniqueGamesTheorem.Foundations.PCP.GraphTransport

section

/-! The actual half-lazy port graph retains a Boolean stay/step flag and an
ordinary port. This supplies the concrete graph underlying Boolean-tape
length smoothing. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringWalks

variable {V D : Type*}

def lazyRotate (G : PortGraph V D) : Edge V (Bool × D) → Edge V (Bool × D)
  | (v, (false, d)) => (v, (false, d))
  | (v, (true, d)) => ((G.rot (v, d)).1, (true, (G.rot (v, d)).2))

theorem lazyRotate_involutive (G : PortGraph V D) :
    Function.Involutive (lazyRotate G) := by
  rintro ⟨v, b, d⟩
  cases b with
  | false => rfl
  | true =>
    exact congrArg (fun e : V × D => (e.1, (true, e.2))) (rot_rot G (v, d))

def lazyGraph (G : PortGraph V D) : PortGraph V (Bool × D) where
  rot := {
    toFun := lazyRotate G
    invFun := lazyRotate G
    left_inv := lazyRotate_involutive G
    right_inv := lazyRotate_involutive G }
  rot_involutive := lazyRotate_involutive G

@[simp] theorem lazyGraph_rot_false (G : PortGraph V D) (v : V) (d : D) :
    (lazyGraph G).rot (v, (false, d)) = (v, (false, d)) := rfl

@[simp] theorem lazyGraph_rot_true (G : PortGraph V D) (v : V) (d : D) :
    (lazyGraph G).rot (v, (true, d)) = ((G.rot (v, d)).1, (true, (G.rot (v, d)).2)) := rfl

end UniqueGamesTheorem.Foundations.PCP.PoweringWalks

end

/-! Spectral contraction for the actual Boolean-flag lazy port graph. The
operator identity is proved in `PoweringLazy`; the estimate here averages the
elementary two-term square inequality. -/

/-! Actual finite walk averages and their operator representations.
All changes of probability coordinates come from explicit equivalences. -/

/-! The second moment of the actual marked-edge count in a consecutive walk
window. Pair events are reduced to the checked spectral return operator. -/

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PoweringOpinionsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# The actual constraint-graph powering test

Every recorded port walk gives two directed darts. Reversal flips an
orientation bit while preserving the recorded walk. The common vertex
alphabet is the full-radius padded local-label alphabet. The test checks the
actual base constraint at every traversed edge using the two endpoint labels.

Honest local encodings give perfect completeness. A decoded bad edge together
with the two matching local opinions forces rejection of the actual test.
Neither conclusion is assumed as a rejection-inclusion or distribution law.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringTest

open PoweringWalks PoweringLabels PoweringReach

variable {V D A : Type*}

/-- Check all base constraints along the recorded walk. The reach certificates
select genuine vertices in the two full-radius neighborhood balls. -/
def pathAccepts (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (w : Walk V D (n + 1)) (a b : PaddedLabel D (n + 1) A) : Bool :=
  decide (∀ k : Fin (n + 1),
    accepts (edgeAt G n w k)
      (decode (selectors w.1) a (tailFromStart G n w k))
      (decode (selectors (endpoint G w)) b (headFromEnd G n w k)) = true)

abbrev Dart (V D : Type*) (n : Nat) := Bool × Walk V D (n + 1)

/-- Reversal preserves the recorded walk and changes its direction flag. -/
def reverseDart (V D : Type*) (n : Nat) : Dart V D n ≃ Dart V D n where
  toFun d := (!d.1, d.2)
  invFun d := (!d.1, d.2)
  left_inv := by
    rintro ⟨b, w⟩
    cases b <;> rfl
  right_inv := by
    rintro ⟨b, w⟩
    cases b <;> rfl

theorem reverseDart_involutive (V D : Type*) (n : Nat) :
    Function.Involutive (reverseDart V D n) := by
  rintro ⟨b, w⟩
  cases b <;> rfl

/-- An actual powered constraint graph, with a common raw alphabet at all
vertices. Its reversal law is witnessed by the orientation bit. -/
def poweredGraph (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v) :
    ConstraintGraph V (Dart V D n) (PaddedLabel D (n + 1) A) where
  reverse := reverseDart V D n
  reverse_involutive := reverseDart_involutive V D n
  tail d := if d.1 then endpoint G d.2 else d.2.1
  accepts d a b := if d.1 then pathAccepts G accepts n selectors d.2 b a
    else pathAccepts G accepts n selectors d.2 a b
  reverse_accepts := by
    rintro ⟨direction, w⟩ a b
    cases direction <;> rfl

@[simp] theorem poweredGraph_tail_false (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v) (w : Walk V D (n + 1)) :
    (poweredGraph G accepts n selectors).tail (false, w) = w.1 := rfl

@[simp] theorem poweredGraph_tail_true (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v) (w : Walk V D (n + 1)) :
    (poweredGraph G accepts n selectors).tail (true, w) = endpoint G w := rfl

end UniqueGamesTheorem.Foundations.PCP.PoweringTest

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_PoweringMachineRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Finite tape program for a powered relation row

The radius, address count, and powered alphabet size are fixed machine
parameters. The machine consumes live base predicate bits and endpoint-match
bits. Its finite register selects the first matching address, looks up the two
fixed powered labels, and conjoins the bounded list of base predicates.

Both input and output bits use the graph-table unary natural-word codec.
The theorems below describe actual TM2 transitions, not assumed execution
costs. Producing this input block from live graph rotor lookups is a separate
frontend composition obligation; no graph table occurs in the machine's
finite transition function.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRow

open Turing
open MachineFixedBlockMap
open UniqueGamesTheorem.Foundations.PCP

abbrev Field (S : Nat) := (GraphTables.Label × GraphTables.Label) ⊕ (Fin S ⊕ Fin S)

def inputSize (t S : Nat) : Nat := t * (4096 + (S + S))

def fieldEquiv (S : Nat) : Field S ≃ Fin (4096 + (S + S)) :=
  (Equiv.sumCongr GraphTables.relationIndex
    (finSumFinEquiv : (Fin S ⊕ Fin S) ≃ Fin (S + S))).trans finSumFinEquiv

def inputEquiv (t S : Nat) : (Fin t × Field S) ≃ Fin (inputSize t S) :=
  (Equiv.prodCongr (Equiv.refl (Fin t)) (fieldEquiv S)).trans finProdFinEquiv

/-- The scan order is the fixed increasing finite-index order. -/
def firstMatch {S : Nat} (mask : Fin S → Bool) : Option (Fin S) :=
  (List.ofFn id).find? mask

def encodeBit (b : Bool) : List Bool := if b then [true, false] else [false]

def encodeBits : List Bool → List Bool
  | [] => []
  | b :: bits => encodeBit b ++ encodeBits bits

@[simp] theorem encodeBits_append (xs ys : List Bool) :
    encodeBits (xs ++ ys) = encodeBits xs ++ encodeBits ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [encodeBits, ih, List.append_assoc]

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRow

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_CloudRoundingLemmas
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

section GraphRounding

open DegreeReplacement PoweringWalks

variable {V E A D : Type*} [Fintype V] [Fintype E] [Fintype A] [Fintype D]
variable [DecidableEq V] [DecidableEq E] [DecidableEq A]

omit [Fintype V] [Fintype E] [Fintype A] [Fintype D] [DecidableEq V] [DecidableEq E] in
@[simp] theorem copied_satisfied_inl (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) (e : E) (d : D) :
    (replacementGraph G H).edgeSatisfied ell (e, Sum.inl d) =
      decide (ell e = ell (innerRotation G H (e, d)).1) := rfl

omit [Fintype V] [Fintype E] [Fintype A] [Fintype D] [DecidableEq V] [DecidableEq E] in
@[simp] theorem copied_satisfied_inr (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) (e : E) (u : Unit) :
    (replacementGraph G H).edgeSatisfied ell (e, Sum.inr u) =
      G.accepts e (ell e) (ell (G.reverse e)) := rfl

end GraphRounding

end UniqueGamesTheorem.Foundations.PCP.CloudRounding

end

section

/-!
# Executable regular constraint tables on the fixed 64-label alphabet

Every pair `(vertex,port)` has one stored reverse index and one complete
4096-bit relation. Flat row `port + ports * vertex` has its tail implicitly
fixed by that pair. Rotation uses the stored vector lookup, followed by the
inverse row-index bijection. Loops and repeated directed occurrences remain
distinct rows.

Serialization uses the existing `GraphTables` codec: header `[vertices,darts]`
with `darts=vertices*ports`, then tail/reverse/4096 bit words per row.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PortTables

open PoweringWalks

abbrev Label := GraphTables.Label

def rowIndex (vertices ports : Nat) :
    Fin vertices × Fin ports ≃ Fin (vertices * ports) := finProdFinEquiv

@[simp] theorem rowIndex_val (n d : Nat) (e : Fin n × Fin d) :
    (rowIndex n d e).val = e.2.val + d * e.1.val := rfl

/-- Finite executable input data, with the two graph laws certified on lookup. -/
structure Table (vertices ports : Nat) where
  reverseIndex : Vector (Fin (vertices * ports)) (vertices * ports)
  relations : Vector GraphTables.RelationTable (vertices * ports)
  involutive : Function.Involutive
    (fun i : Fin (vertices * ports) => reverseIndex[i])
  transpose : ∀ (i : Fin (vertices * ports)) (a b : Label),
    GraphTables.relationAt relations[reverseIndex[i]] b a =
      GraphTables.relationAt relations[i] a b

variable {n d : Nat}

/-- One reverse-index lookup and the fixed mixed-radix decoding. -/
def rotation (table : Table n d) (e : Fin n × Fin d) : Fin n × Fin d :=
  (rowIndex n d).symm table.reverseIndex[rowIndex n d e]

/-- Lookup of the full stored binary predicate. -/
def accepts (table : Table n d) (e : Fin n × Fin d) (a b : Label) : Bool :=
  GraphTables.relationAt table.relations[rowIndex n d e] a b

@[simp] theorem rowIndex_rotation (table : Table n d) (e : Fin n × Fin d) :
    rowIndex n d (rotation table e) = table.reverseIndex[rowIndex n d e] := by
  exact (rowIndex n d).apply_symm_apply _

theorem rotation_involutive (table : Table n d) : Function.Involutive (rotation table) := by
  intro e
  simp only [rotation, Equiv.apply_symm_apply]
  exact (congrArg (rowIndex n d).symm (table.involutive (rowIndex n d e))).trans
    ((rowIndex n d).symm_apply_apply e)

theorem accepts_rotation (table : Table n d) (e : Fin n × Fin d) (a b : Label) :
    accepts table (rotation table e) b a = accepts table e a b := by
  simpa only [accepts, rowIndex_rotation] using table.transpose (rowIndex n d e) a b

/-- The actual reversible regular port graph represented by the vectors. -/
def portGraph (table : Table n d) : PortGraph (Fin n) (Fin d) where
  rot :=
    { toFun := rotation table
      invFun := rotation table
      left_inv := rotation_involutive table
      right_inv := rotation_involutive table }
  rot_involutive := rotation_involutive table

@[simp] theorem portGraph_rot (table : Table n d) (e : Fin n × Fin d) :
    (portGraph table).rot e = rotation table e := rfl

/-- Constraint-graph semantics, with each vertex-port pair a distinct dart. -/
def baseGraph (table : Table n d) : ConstraintGraph (Fin n) (Fin n × Fin d) Label where
  reverse := (portGraph table).rot
  reverse_involutive := rotation_involutive table
  tail := Prod.fst
  accepts := accepts table
  reverse_accepts := accepts_rotation table

@[simp] theorem baseGraph_reverse (table : Table n d) (e : Fin n × Fin d) :
    (baseGraph table).reverse e = rotation table e := rfl

@[simp] theorem baseGraph_tail (table : Table n d) (e : Fin n × Fin d) :
    (baseGraph table).tail e = e.1 := rfl

@[simp] theorem baseGraph_head (table : Table n d) (e : Fin n × Fin d) :
    (baseGraph table).head e = (rotation table e).1 := rfl

@[simp] theorem baseGraph_accepts (table : Table n d) (e : Fin n × Fin d) (a b : Label) :
    (baseGraph table).accepts e a b = accepts table e a b := rfl

/-- Materialize a reversible port graph and its predicates into the fixed rows. -/
def ofPortGraph (G : PortGraph (Fin n) (Fin d))
    (predicate : (Fin n × Fin d) → Label → Label → Bool)
    (htranspose : ∀ e a b, predicate (G.rot e) b a = predicate e a b) : Table n d where
  reverseIndex := Vector.ofFn (fun i => rowIndex n d (G.rot ((rowIndex n d).symm i)))
  relations := Vector.ofFn (fun i => GraphTables.relationOf (predicate ((rowIndex n d).symm i)))
  involutive := by
    intro i
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
      Equiv.symm_apply_apply]
    exact (congrArg (rowIndex n d) (G.rot_involutive ((rowIndex n d).symm i))).trans
      ((rowIndex n d).apply_symm_apply i)
  transpose := by
    intro i a b
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
      Equiv.symm_apply_apply, GraphTables.relationAt_relationOf]
    exact htranspose ((rowIndex n d).symm i) a b

@[simp] theorem rotation_ofPortGraph (G : PortGraph (Fin n) (Fin d))
    (predicate : (Fin n × Fin d) → Label → Label → Bool)
    (htranspose : ∀ e a b, predicate (G.rot e) b a = predicate e a b)
    (e : Fin n × Fin d) : rotation (ofPortGraph G predicate htranspose) e = G.rot e := by
  simp only [rotation, ofPortGraph, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
    Equiv.symm_apply_apply]

@[simp] theorem accepts_ofPortGraph (G : PortGraph (Fin n) (Fin d))
    (predicate : (Fin n × Fin d) → Label → Label → Bool)
    (htranspose : ∀ e a b, predicate (G.rot e) b a = predicate e a b)
    (e : Fin n × Fin d) (a b : Label) :
    accepts (ofPortGraph G predicate htranspose) e a b = predicate e a b := by
  simp only [accepts, ofPortGraph, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
    Equiv.symm_apply_apply, GraphTables.relationAt_relationOf]

end UniqueGamesTheorem.Foundations.PCP.PortTables

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PoweringOpinionTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Bounded first-address tables for actual powering constraints

For a graph with numbered vertices and ports, each stored local-opinion index
is the first address in `allAddresses` that reaches the requested vertex.
The search traverses bounded port words, never the ambient vertex set.

The walk table stores one base dart and two address indices per traversed
edge. Looking up the endpoint labels at those indices gives exactly the
existing `finitePortSelector` decoders, including when addresses collide.
The resulting finite table predicate equals the actual powering predicate.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables

open PoweringWalks PoweringLabels PoweringAddresses PoweringReach
open scoped BigOperators

variable {X A : Type*}

theorem match_in_tail (p : X → Prop) {a : X} {xs : List X}
    (h : ∃ b ∈ a :: xs, p b) (ha : ¬p a) : ∃ b ∈ xs, p b := by
  obtain ⟨b, hb, hp⟩ := h
  rcases List.mem_cons.mp hb with he | hm
  · exact False.elim (ha (he ▸ hp))
  · exact ⟨b, hm, hp⟩

def firstIndex (p : X → Prop) [DecidablePred p] :
    (xs : List X) → (∃ a ∈ xs, p a) → Fin xs.length
  | [], h => False.elim (by simp at h)
  | a :: xs, h =>
    if ha : p a then ⟨0, Nat.zero_lt_succ xs.length⟩ else
      (firstIndex p xs (match_in_tail p h ha)).succ

/-- The stored index selects the very same first address as `scanWitness`,
not just an address with the same endpoint. -/
theorem get_firstIndex (p : X → Prop) [DecidablePred p] :
    ∀ (xs : List X) (h : ∃ a ∈ xs, p a),
      xs.get (firstIndex p xs h) = (scanWitness p xs h).val := by
  intro xs
  induction xs with
  | nil => intro h; simp at h
  | cons a xs ih =>
    intro h
    by_cases ha : p a
    · simp [firstIndex, scanWitness, ha]
    · simpa only [firstIndex, scanWitness, ha, dite_false, List.get_cons_succ'] using
        ih (match_in_tail p h ha)

/-- A local label slot is an index into the explicit bounded address list. -/
abbrev AddressIndex (d t : Nat) := Fin (allAddresses d t).length

variable {vertices d : Nat}

def addressIndex (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) : AddressIndex d t :=
  firstIndex (fun w => (wordToBall G t center w).val = u.val)
    (allAddresses d t) (by
      obtain ⟨w, hw⟩ := wordToBall_surjective G t center u
      exact ⟨w, mem_allAddresses d t w, congrArg Subtype.val hw⟩)

theorem addressIndex_get (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) :
    (allAddresses d t).get (addressIndex G t center u) =
      (finitePortSelector G t center).address u := by
  change (allAddresses d t).get (firstIndex
    (fun w => (wordToBall G t center w).val = u.val) (allAddresses d t) _) =
      (scanWitness _ _ _).val
  exact get_firstIndex _ _ _

abbrev LabelTable (d t : Nat) (A : Type*) := Vector A (allAddresses d t).length

/-- Materialize a padded label in the common address order. -/
def labelTable {t : Nat} (a : PaddedLabel (Fin d) t A) : LabelTable d t A :=
  Vector.ofFn fun i => a ((allAddresses d t).get i)

@[simp] theorem labelTable_get {t : Nat} (a : PaddedLabel (Fin d) t A)
    (i : AddressIndex d t) :
    (labelTable a)[i] = a ((allAddresses d t).get i) := by
  simp [labelTable]

/-- Exact evaluation bridge for every local target, with no consistency
assumption on labels at distinct addresses that reach the same vertex. -/
theorem labelTable_addressIndex (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) (a : PaddedLabel (Fin d) t A) :
    (labelTable a)[addressIndex G t center u] =
      decode (finitePortSelector G t center) a u := by
  rw [labelTable_get, addressIndex_get]
  rfl

/-- One finite row for each constraint checked along a recorded walk. -/
structure WalkOpinionRow (vertices d t : Nat) where
  edge : Edge (Fin vertices) (Fin d)
  tailIndex : AddressIndex d t
  headIndex : AddressIndex d t

abbrev WalkRows (vertices d n : Nat) := Vector (WalkOpinionRow vertices d (n + 1)) (n + 1)

/-- The only target vertices inspected are the actual edge endpoints. -/
def walkRows (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) : WalkRows vertices d n :=
  Vector.ofFn fun k =>
    { edge := edgeAt G n w k
      tailIndex := addressIndex G (n + 1) w.1 (tailFromStart G n w k)
      headIndex := addressIndex G (n + 1) (endpoint G w) (headFromEnd G n w k) }

@[simp] theorem walkRows_edge (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1)) :
    (walkRows G n w)[k].edge = edgeAt G n w k := by
  simp [walkRows]

@[simp] theorem walkRows_tail_value (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1))
    (a : PaddedLabel (Fin d) (n + 1) A) :
    (labelTable a)[(walkRows G n w)[k].tailIndex] =
      decode (finitePortSelector G (n + 1) w.1) a (tailFromStart G n w k) := by
  simpa only [walkRows, Fin.getElem_fin, Vector.getElem_ofFn] using
    labelTable_addressIndex G (n + 1) w.1 (tailFromStart G n w k) a

@[simp] theorem walkRows_head_value (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1))
    (b : PaddedLabel (Fin d) (n + 1) A) :
    (labelTable b)[(walkRows G n w)[k].headIndex] =
      decode (finitePortSelector G (n + 1) (endpoint G w)) b (headFromEnd G n w k) := by
  simpa only [walkRows, Fin.getElem_fin, Vector.getElem_ofFn] using
    labelTable_addressIndex G (n + 1) (endpoint G w) (headFromEnd G n w k) b

end UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PoweringTablesLemmas
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

namespace UniqueGamesTheorem.Foundations.PCP.PoweringTables

open PoweringWalks PoweringLabels PoweringAddresses PoweringEnumeration

/-- Program-constant output alphabet size for degree `d` and walk length `n+1`. -/
def labelCount (d n : Nat) : Nat := 64 ^ addressCount d (n + 1)

/-- Number of directed recorded-walk occurrences, including orientation. -/
def dartCount (vertices d n : Nat) : Nat := 2 * vertices * d ^ (n + 1)

end UniqueGamesTheorem.Foundations.PCP.PoweringTables

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

namespace UniqueGamesTheorem.Foundations.PCP.PoweringRowData

open UniqueGamesTheorem.Foundations.Complexity
open Turing
open PoweringMachineRow MachineFixedBlockMap
open PoweringWalks PoweringLabels PoweringAddresses PoweringReach
open PoweringOpinionTables PoweringEnumeration

variable {vertices d : Nat}

/-- An actual endpoint comparison; it has no reachability oracle input. -/
def endpointMask (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center target : Fin vertices) (i : AddressIndex d t) : Bool :=
  decide ((wordToBall G t center ((allAddresses d t).get i)).val = target)

def slotCount (d n : Nat) : Nat := (allAddresses d (n + 1)).length

end UniqueGamesTheorem.Foundations.PCP.PoweringRowData

/-! A fixed powered-row data block is reduced to two concrete instruction
forms: follow a fixed port word and read one stored predicate entry, or follow
two fixed words and compare their endpoint identifiers. The plan depends only
on the fixed degree, radius, word and orientation. Its interpretation is exactly
the data block consumed by the checked row transducer. -/

/-! Exact tail and reverse-index fields of the actual powering-table rows.
The reverse address is affine in the live starting vertex; the coefficient
and offset depend only on the fixed degree, word, and orientation. -/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PoweringTableSemanticsLemmas
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

/-! Actual directed-cut expansion from the graph's zero-mean spectral
certificate. Parallel edges and loops retain their indexed port multiplicities. -/

/-!
# Uniform restriction of Boolean tapes

Restricting a uniformly sampled Boolean function to a decidable subset gives
the uniform law on functions on that subset.  The subset and its complement
may be empty: their Boolean function spaces still contain the constant-false
function.  Extending by false gives a canonical full-domain oracle address.
-/

namespace UniqueGamesTheorem.Foundations.PCP.UniformRestriction

open scoped BigOperators

variable {B : Type*} (p : B → Prop)

/-- The values of a full Boolean tape on the legal coordinates. -/
def restrict (f : B → Bool) : {b // p b} → Bool := fun b => f b.1

variable [DecidablePred p]

/-- Extend a tape on legal coordinates by false on every other coordinate. -/
def extend (g : {b // p b} → Bool) : B → Bool :=
  fun b => if hb : p b then g ⟨b, hb⟩ else false

omit [DecidablePred p] in
@[simp] theorem restrict_apply (f : B → Bool) (b : {b // p b}) :
    restrict p f b = f b.1 := rfl

@[simp] theorem extend_apply_of_mem (g : {b // p b} → Bool) (b : B) (hb : p b) :
    extend p g b = g ⟨b, hb⟩ := by
  simp [extend, hb]

@[simp] theorem extend_apply_of_not_mem (g : {b // p b} → Bool) (b : B)
    (hb : ¬ p b) : extend p g b = false := by
  simp [extend, hb]

@[simp] theorem restrict_extend (g : {b // p b} → Bool) :
    restrict p (extend p g) = g := by
  funext b
  simp [restrict, extend, b.property]

end UniqueGamesTheorem.Foundations.PCP.UniformRestriction

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_AlphabetGraphLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetGraph

open UniqueGamesTheorem.Foundations.Hastad
open scoped BigOperators

abbrev Address (V E A : Type*) := (V × Cube A) ⊕ (E × Cube (A × A))

abbrev LocalEvent (A : Type*) := Fin 4 × AlphabetReduction.InputCoordinate A ×
  Cube (A × A) × Cube (A × A) × Cube (A × A) × Cube (A × A) × Cube (A × A)

abbrev Event (E A : Type*) := E × LocalEvent A

variable {V E A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

abbrev legal (G : ConstraintGraph V E A) (e : E) (p : A × A) : Prop :=
  G.accepts e p.1 p.2 = true

instance legalDecidable (G : ConstraintGraph V E A) (e : E) :
    DecidablePred (legal G e) :=
  fun p => inferInstanceAs (Decidable (G.accepts e p.1 p.2 = true))

def restrictTape (G : ConstraintGraph V E A) (e : E) (f : Cube (A × A)) :
    Cube (AlphabetReduction.LegalPair (G.accepts e)) := UniformRestriction.restrict (legal G e) f

def extendTape (G : ConstraintGraph V E A) (e : E)
    (f : Cube (AlphabetReduction.LegalPair (G.accepts e))) : Cube (A × A) :=
  UniformRestriction.extend (legal G e) f

def globalizeQuery (G : ConstraintGraph V E A) (e : E) :
    AlphabetReduction.InputCoordinate A ⊕ Cube (AlphabetReduction.LegalPair (G.accepts e)) → Address V E A
  | .inl (side, tape) => .inl ((if side then G.head e else G.tail e), tape)
  | .inr tape => .inr (e, extendTape G e tape)

def verifier (G : ConstraintGraph V E A) : QueryIncidence.Verifier (Event E A) (Address V E A) 6 where
  query := fun (e, kind, k, f, g, r₀, r₁, r₂) slot =>
    globalizeQuery G e (AssignmentTester.eventQueries (AlphabetReduction.pairEncoding (G.accepts e)) kind k
      (restrictTape G e f) (restrictTape G e g) (restrictTape G e r₀)
      (restrictTape G e r₁) (restrictTape G e r₂) slot)
  accepts := fun (_, kind, _, _, _, _, _, _) b => AssignmentTester.eventAccepts kind b

def vertexBlock (assignment : Address V E A → Bool) (v : V) : Cube A → Bool :=
  fun tape => assignment (.inl (v, tape))

omit [Nonempty A] in
@[simp] theorem card_event [Fintype E] :
    Fintype.card (Event E A) = Fintype.card E * Fintype.card (LocalEvent A) :=
  Fintype.card_prod _ _

def honestAssignment (G : ConstraintGraph V E A) (labeling : V → A) : Address V E A → Bool
  | .inl (v, tape) => tape (labeling v)
  | .inr (e, tape) => tape (labeling (G.tail e), labeling (G.head e))

omit [Fintype A] [DecidableEq A] [Nonempty A] in
@[simp] theorem honest_vertexBlock (G : ConstraintGraph V E A) (labeling : V → A) (v : V) :
    vertexBlock (honestAssignment G labeling) v = CodeComposition.codeword (labeling v) := rfl

def graph [DecidableEq V] [DecidableEq E] (G : ConstraintGraph V E A) :
    ConstraintGraph (QueryIncidence.Vertex (Event E A) (Address V E A))
      (QueryIncidence.Dart (Event E A) 6) (QueryIncidence.Label 6) := QueryIncidence.graph (verifier G) (by omega)

end UniqueGamesTheorem.Foundations.PCP.AlphabetGraph

end

/-!
# Real gap and exact size of the alphabet graph

The gap bound is obtained directly from the two checked rejection-count
inequalities. The finite graph's size is linear in the old vertices and darts,
with an explicit coefficient determined only by the old alphabet cardinality.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetGraphBounds

open scoped BigOperators

/-- The number of local verifier events for an alphabet with `q` symbols. -/
def localEventFactor (q : Nat) : Nat :=
  4 * (2 * 2 ^ q) * (2 ^ (q * q)) ^ 5

def vertexFactor (q : Nat) : Nat := localEventFactor q + 2 ^ (q * q)

def dartFactor (q : Nat) : Nat := 12 * localEventFactor q

def sizeFactor (q : Nat) : Nat := 2 ^ q + vertexFactor q + dartFactor q

theorem sizeFactor_positive (q : Nat) : 0 < sizeFactor q := by
  have hp : (0 : Nat) < 2 ^ q := pow_pos (by decide) q
  unfold sizeFactor
  omega

end UniqueGamesTheorem.Foundations.PCP.AlphabetGraphBounds

/-!
# Explicit orders for the alphabet-reduction table

All executable maps use Boolean digits, finite sums, and division/remainder.
No enumeration is chosen from a cardinality proof. Cube coordinate zero is the
least significant bit; pairs of coordinates use row-major order. Event blocks
are ordered by their original dart, followed by the local event. Vertices put
events before vertex addresses before edge addresses. Each event has twelve
ordered darts: six slots, with false then true orientation at each slot.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration

open UniqueGamesTheorem.Foundations.Hastad
open scoped BigOperators

def bitValue (bit : Bool) : Nat := if bit then 1 else 0

def boolEquiv : Bool ≃ Fin 2 := finTwoEquiv.symm

@[simp] theorem boolEquiv_val (bit : Bool) : (boolEquiv bit).val = bitValue bit := by
  cases bit <;> rfl

/-- Left component first, with the right component varying fastest. -/
def productEquiv {A B : Type*} {a b : Nat} (left : A ≃ Fin a) (right : B ≃ Fin b) :
    A × B ≃ Fin (a * b) :=
  (Equiv.prodCongr left right).trans finProdFinEquiv

@[simp] theorem productEquiv_val {A B : Type*} {a b : Nat}
    (left : A ≃ Fin a) (right : B ≃ Fin b) (x : A) (y : B) :
    (productEquiv left right (x, y)).val = (left x).val * b + (right y).val := by
  change (right y).val + b * (left x).val = _
  simp [Nat.mul_comm, Nat.add_comm]

/-- The complete left block precedes the complete right block. -/
def sumEquiv {A B : Type*} {a b : Nat} (left : A ≃ Fin a) (right : B ≃ Fin b) :
    A ⊕ B ≃ Fin (a + b) :=
  (Equiv.sumCongr left right).trans finSumFinEquiv

@[simp] theorem sumEquiv_inl_val {A B : Type*} {a b : Nat}
    (left : A ≃ Fin a) (right : B ≃ Fin b) (x : A) :
    (sumEquiv left right (.inl x)).val = (left x).val := rfl

@[simp] theorem sumEquiv_inr_val {A B : Type*} {a b : Nat}
    (left : A ≃ Fin a) (right : B ≃ Fin b) (y : B) :
    (sumEquiv left right (.inr y)).val = a + (right y).val := rfl

def tapeCount (q : Nat) : Nat := 2 ^ q
def pairTapeCount (q : Nat) : Nat := 2 ^ (q * q)
def fiveTapeCount (q : Nat) : Nat := pairTapeCount q ^ 5
def localCount (q : Nat) : Nat := 4 * (2 * tapeCount q) * fiveTapeCount q
def eventCount (m q : Nat) : Nat := m * localCount q
def addressCount (n m q : Nat) : Nat := n * tapeCount q + m * pairTapeCount q
def vertexCount (n m q : Nat) : Nat := eventCount m q + addressCount n m q
def dartCount (m q : Nat) : Nat := eventCount m q * 12

/-- Explicit binary rank/unrank; the inverse extracts digits by division and
remainder, as supplied by the executable `finFunctionFinEquiv`. -/
def cubeEquiv (q : Nat) : Cube (Fin q) ≃ Fin (tapeCount q) :=
  (Equiv.arrowCongr (Equiv.refl (Fin q)) boolEquiv).trans finFunctionFinEquiv

def pairIndex (q : Nat) : Fin q × Fin q ≃ Fin (q * q) := finProdFinEquiv

def pairCubeEquiv (q : Nat) : Cube (Fin q × Fin q) ≃ Fin (pairTapeCount q) :=
  (Equiv.arrowCongr (pairIndex q) (Equiv.refl Bool)).trans (cubeEquiv (q * q))

def inputCoordinateEquiv (q : Nat) :
    AlphabetReduction.InputCoordinate (Fin q) ≃ Fin (2 * tapeCount q) :=
  productEquiv boolEquiv (cubeEquiv q)

def fivePairTapesEquiv (q : Nat) :
    (Cube (Fin q × Fin q) × Cube (Fin q × Fin q) × Cube (Fin q × Fin q) ×
      Cube (Fin q × Fin q) × Cube (Fin q × Fin q)) ≃ Fin (fiveTapeCount q) :=
  (productEquiv (pairCubeEquiv q)
    (productEquiv (pairCubeEquiv q)
      (productEquiv (pairCubeEquiv q)
        (productEquiv (pairCubeEquiv q) (pairCubeEquiv q))))).trans
    (finCongr (by simp [fiveTapeCount, pow_succ, Nat.mul_assoc]))

def localEventEquiv (q : Nat) : AlphabetGraph.LocalEvent (Fin q) ≃ Fin (localCount q) :=
  (productEquiv (Equiv.refl (Fin 4))
    (productEquiv (inputCoordinateEquiv q) (fivePairTapesEquiv q))).trans
    (finCongr (by simp [localCount, Nat.mul_assoc]))

def eventEquiv (m q : Nat) :
    AlphabetGraph.Event (Fin m) (Fin q) ≃ Fin (eventCount m q) :=
  productEquiv (Equiv.refl (Fin m)) (localEventEquiv q)

def addressEquiv (n m q : Nat) :
    AlphabetGraph.Address (Fin n) (Fin m) (Fin q) ≃ Fin (addressCount n m q) :=
  sumEquiv (productEquiv (Equiv.refl (Fin n)) (cubeEquiv q))
    (productEquiv (Equiv.refl (Fin m)) (pairCubeEquiv q))

def vertexEquiv (n m q : Nat) :
    QueryIncidence.Vertex (AlphabetGraph.Event (Fin m) (Fin q))
      (AlphabetGraph.Address (Fin n) (Fin m) (Fin q)) ≃ Fin (vertexCount n m q) :=
  sumEquiv (eventEquiv m q) (addressEquiv n m q)

def dartEquiv (m q : Nat) :
    QueryIncidence.Dart (AlphabetGraph.Event (Fin m) (Fin q)) 6 ≃ Fin (dartCount m q) :=
  (productEquiv (productEquiv (eventEquiv m q) (Equiv.refl (Fin 6))) boolEquiv).trans
    (finCongr (by simp [dartCount, Nat.mul_assoc]))

def labelEquiv : QueryIncidence.Label 6 ≃ Fin 64 := cubeEquiv 6

@[simp] theorem inputCoordinateEquiv_val (q : Nat) (side : Bool) (tape : Cube (Fin q)) :
    (inputCoordinateEquiv q (side, tape)).val =
      bitValue side * tapeCount q + (cubeEquiv q tape).val := by
  simp [inputCoordinateEquiv]

@[simp] theorem eventEquiv_val (m q : Nat) (edge : Fin m)
    (sample : AlphabetGraph.LocalEvent (Fin q)) :
    (eventEquiv m q (edge, sample)).val = edge.val * localCount q +
      (localEventEquiv q sample).val := by
  change (localEventEquiv q sample).val + localCount q * edge.val = _
  simp [Nat.mul_comm, Nat.add_comm]

@[simp] theorem addressEquiv_inl_val (n m q : Nat) (vertex : Fin n)
    (tape : Cube (Fin q)) :
    (addressEquiv n m q (.inl (vertex, tape))).val =
      vertex.val * tapeCount q + (cubeEquiv q tape).val := by
  change (cubeEquiv q tape).val + tapeCount q * vertex.val = _
  simp [Nat.mul_comm, Nat.add_comm]

@[simp] theorem addressEquiv_inr_val (n m q : Nat) (edge : Fin m)
    (tape : Cube (Fin q × Fin q)) :
    (addressEquiv n m q (.inr (edge, tape))).val =
      n * tapeCount q + (edge.val * pairTapeCount q + (pairCubeEquiv q tape).val) := by
  change n * tapeCount q + ((pairCubeEquiv q tape).val + pairTapeCount q * edge.val) = _
  simp [Nat.mul_comm, Nat.add_comm]

@[simp] theorem vertexEquiv_event_val (n m q : Nat)
    (event : AlphabetGraph.Event (Fin m) (Fin q)) :
    (vertexEquiv n m q (.inl event)).val = (eventEquiv m q event).val := rfl

@[simp] theorem vertexEquiv_vertexAddress_val (n m q : Nat) (vertex : Fin n)
    (tape : Cube (Fin q)) :
    (vertexEquiv n m q (.inr (.inl (vertex, tape)))).val =
      eventCount m q + (vertex.val * tapeCount q + (cubeEquiv q tape).val) := by
  change eventCount m q + (addressEquiv n m q (.inl (vertex, tape))).val = _
  rw [addressEquiv_inl_val]

@[simp] theorem vertexEquiv_edgeAddress_val (n m q : Nat) (edge : Fin m)
    (tape : Cube (Fin q × Fin q)) :
    (vertexEquiv n m q (.inr (.inr (edge, tape)))).val =
      eventCount m q + (n * tapeCount q +
        (edge.val * pairTapeCount q + (pairCubeEquiv q tape).val)) := by
  change eventCount m q + (addressEquiv n m q (.inr (edge, tape))).val = _
  rw [addressEquiv_inr_val]

@[simp] theorem dartEquiv_val (m q : Nat)
    (event : AlphabetGraph.Event (Fin m) (Fin q)) (slot : Fin 6) (orientation : Bool) :
    (dartEquiv m q ((event, slot), orientation)).val =
      (eventEquiv m q event).val * 12 + slot.val * 2 + bitValue orientation := by
  change (boolEquiv orientation).val + 2 * (slot.val + 6 * (eventEquiv m q event).val) = _
  rw [boolEquiv_val]
  omega

/-- A reusable explicit increasing-index enumeration. -/
def ordered {A : Type*} {count : Nat} (order : A ≃ Fin count) : List A :=
  List.ofFn order.symm

@[simp] theorem ordered_length {A : Type*} {count : Nat} (order : A ≃ Fin count) :
    (ordered order).length = count := by simp [ordered]

@[simp] theorem ordered_refl (n : Nat) : ordered (Equiv.refl (Fin n)) = List.finRange n := rfl

@[simp] theorem ordered_bool : ordered boolEquiv = [false, true] := rfl

def localEvents (q : Nat) : List (AlphabetGraph.LocalEvent (Fin q)) :=
  ordered (localEventEquiv q)

@[simp] theorem localEvents_length (q : Nat) : (localEvents q).length = localCount q :=
  ordered_length _

@[simp] theorem card_cube (q : Nat) : Fintype.card (Cube (Fin q)) = tapeCount q := by
  simpa using Fintype.card_congr (cubeEquiv q)

@[simp] theorem card_pairCube (q : Nat) :
    Fintype.card (Cube (Fin q × Fin q)) = pairTapeCount q := by
  simpa using Fintype.card_congr (pairCubeEquiv q)

@[simp] theorem card_localEvent (q : Nat) :
    Fintype.card (AlphabetGraph.LocalEvent (Fin q)) = localCount q := by
  simpa using Fintype.card_congr (localEventEquiv q)

@[simp] theorem card_event (m q : Nat) :
    Fintype.card (AlphabetGraph.Event (Fin m) (Fin q)) = eventCount m q := by
  simpa using Fintype.card_congr (eventEquiv m q)

@[simp] theorem card_address (n m q : Nat) :
    Fintype.card (AlphabetGraph.Address (Fin n) (Fin m) (Fin q)) = addressCount n m q := by
  simpa using Fintype.card_congr (addressEquiv n m q)

@[simp] theorem card_vertex (n m q : Nat) :
    Fintype.card (QueryIncidence.Vertex (AlphabetGraph.Event (Fin m) (Fin q))
      (AlphabetGraph.Address (Fin n) (Fin m) (Fin q))) = vertexCount n m q := by
  simpa using Fintype.card_congr (vertexEquiv n m q)

@[simp] theorem card_dart (m q : Nat) :
    Fintype.card (QueryIncidence.Dart (AlphabetGraph.Event (Fin m) (Fin q)) 6) =
      dartCount m q := by
  simpa using Fintype.card_congr (dartEquiv m q)

@[simp] theorem localCount_formula (q : Nat) :
    localCount q = 4 * (2 * 2 ^ q) * (2 ^ (q * q)) ^ 5 := rfl

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_QueriesLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Executable six-query generation on fixed full Boolean cubes. The event
type is exactly `AlphabetGraph.LocalEvent`, including all five full tapes.
Only the returned joint-table addresses are masked outside the input relation;
no legal-pair enumeration or change of sample multiplicities occurs. -/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Queries

open UniqueGamesTheorem.Foundations.Hastad

abbrev RawQuery (q : Nat) :=
  (Bool × Cube (Fin q)) ⊕ Cube (Fin q × Fin q)

abbrev LocalEvent (q : Nat) := AlphabetGraph.LocalEvent (Fin q)

/-- Canonical full-cube proof address: every illegal coordinate is false. -/
def mask {q : Nat} (P : Fin q → Fin q → Bool) (f : Cube (Fin q × Fin q)) :
    Cube (Fin q × Fin q) := fun p => if P p.1 p.2 then f p else false

def xorTape {A : Type*} (f g : Cube A) : Cube A := fun a => f a ^^ g a

def andTape {A : Type*} (f g : Cube A) : Cube A := fun a => f a && g a

/-- The coordinate value of the paired input codeword before masking. -/
def inputPairTape {q : Nat} (k : Bool × Cube (Fin q)) : Cube (Fin q × Fin q) :=
  fun p => if k.1 then k.2 p.2 else k.2 p.1

/-- Actual six queries, computed directly from fixed full tapes and P.
Padding slots repeat precisely the addresses used by `eventQueries`. -/
def query {q : Nat} (P : Fin q → Fin q → Bool) (event : LocalEvent q)
    (slot : Fin 6) : RawQuery q :=
  match event with
  | (kind, k, f, g, r₀, r₁, r₂) =>
    if kind = 0 then
      if slot = 0 then .inr (mask P f) else
      if slot = 1 then .inr (mask P g) else .inr (mask P (xorTape f g))
    else if kind = 1 then
      if slot = 0 then .inr (mask P r₀) else
      if slot = 1 then .inr (mask P (xorTape r₀ (andTape f g))) else
      if slot = 2 then .inr (mask P r₁) else
      if slot = 3 then .inr (mask P (xorTape r₁ f)) else
      if slot = 4 then .inr (mask P r₂) else .inr (mask P (xorTape r₂ g))
    else if kind = 2 then
      if slot = 0 then .inr (mask P r₀) else
        .inr (mask P (xorTape r₀ (fun _ => true)))
    else
      if slot = 0 then .inl k else
      if slot = 1 then .inr (mask P r₀) else
        .inr (mask P (xorTape r₀ (inputPairTape k)))

/-- Attach the actual endpoints and edge identifier to a local raw address. -/
def globalize {q : Nat} {V E : Type*} (tail head : V) (edge : E) :
    RawQuery q → AlphabetGraph.Address V E (Fin q)
  | .inl (side, tape) => .inl ((if side then head else tail), tape)
  | .inr tape => .inr (edge, tape)

@[simp] theorem mask_idempotent {q : Nat} (P : Fin q → Fin q → Bool)
    (f : Cube (Fin q × Fin q)) : mask P (mask P f) = mask P f := by
  funext p
  cases hp : P p.1 p.2 <;> simp [mask, hp]

/-- Proof-only comparison map: extend the original legal-coordinate addresses.
The executable `query` function above never calls this map. -/
def extendQuery {q : Nat} (P : Fin q → Fin q → Bool) :
    AlphabetReduction.InputCoordinate (Fin q) ⊕ Cube (AlphabetReduction.LegalPair P) →
      RawQuery q
  | .inl k => .inl k
  | .inr tape => .inr (UniformRestriction.extend (fun p : Fin q × Fin q => P p.1 p.2 = true) tape)

/-- Pointwise equality with the existing tester after restricting all five
full input tapes and canonically extending the resulting query. The statement
does not require any legal pair to exist. -/
theorem query_eq_extend_eventQueries {q : Nat} (P : Fin q → Fin q → Bool)
    (kind : Fin 4) (k : AlphabetReduction.InputCoordinate (Fin q))
    (f g r₀ r₁ r₂ : Cube (Fin q × Fin q)) (slot : Fin 6) :
    query P (kind, k, f, g, r₀, r₁, r₂) slot =
      extendQuery P (AssignmentTester.eventQueries (AlphabetReduction.pairEncoding P) kind k
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) f)
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) g)
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) r₀)
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) r₁)
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) r₂) slot) := by
  by_cases hk₀ : kind = 0 <;> by_cases hk₁ : kind = 1 <;> by_cases hk₂ : kind = 2 <;>
    simp only [query, AssignmentTester.eventQueries, hk₀, hk₁, hk₂, ite_true, if_true, ite_false]
  all_goals split_ifs <;> simp_all only [extendQuery]
  all_goals rfl

theorem globalize_extendQuery {q : Nat} {V E : Type*}
    (G : ConstraintGraph V E (Fin q)) (e : E)
    (x : AlphabetReduction.InputCoordinate (Fin q) ⊕
      Cube (AlphabetReduction.LegalPair (G.accepts e))) :
    globalize (G.tail e) (G.head e) e (extendQuery (G.accepts e) x) =
      AlphabetGraph.globalizeQuery G e x := by
  cases x with
  | inl k => cases k; rfl
  | inr tape => rfl

/-- The executable raw queries are exactly the actual verifier queries after
attaching the endpoints and edge tag. This includes self-loops, duplicate
queries, empty legal relations, and every original five-tape event. -/
theorem globalize_query {q : Nat} {V E : Type*}
    (G : ConstraintGraph V E (Fin q)) (e : E) (event : LocalEvent q) (slot : Fin 6) :
    globalize (G.tail e) (G.head e) e (query (G.accepts e) event slot) =
      (AlphabetGraph.verifier G).query (e, event) slot := by
  rcases event with ⟨kind, k, f, g, r₀, r₁, r₂⟩
  rw [query_eq_extend_eventQueries]
  exact globalize_extendQuery G e _

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Queries

end

section

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Relations

open Hastad
open Queries

variable {q : Nat}

/-- Exact local address comparison. A loop identifies the two endpoint tables;
the joint edge table is always disjoint from every endpoint table. -/
def sameAddress (selfLoop : Bool) : RawQuery q → RawQuery q → Bool
  | .inl (side, f), .inl (side', g) => ((side == side') || selfLoop) && decide (f = g)
  | .inr f, .inr g => decide (f = g)
  | _, _ => false

@[simp] theorem sameAddress_refl (selfLoop : Bool) (x : RawQuery q) :
    sameAddress selfLoop x x = true := by
  rcases x with ⟨side, f⟩ | f <;> simp [sameAddress]

theorem globalize_eq_iff {V E : Type*} [DecidableEq V]
    (tail head : V) (edge : E) (selfLoop : Bool)
    (hloop : selfLoop = decide (tail = head)) (x y : RawQuery q) :
    globalize tail head edge x = globalize tail head edge y ↔
      sameAddress selfLoop x y = true := by
  rcases x with ⟨side, f⟩ | f <;> rcases y with ⟨side', g⟩ | g
  · cases side <;> cases side'
    · simp [globalize, sameAddress]
    · simp [globalize, sameAddress, hloop]
    · simp [globalize, sameAddress, hloop,
        show head = tail ↔ tail = head from eq_comm]
    · simp [globalize, sameAddress]
  · simp [globalize, sameAddress]
  · simp [globalize, sameAddress]
  · simp [globalize, sameAddress]

def eqProfile (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (i j : Fin 6) : Bool := sameAddress selfLoop (queries i) (queries j)

@[simp] theorem eqProfile_refl (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (i : Fin 6) : eqProfile selfLoop queries i i = true := sameAddress_refl _ _

/-- Search the fixed six positions for the least occurrence of an address. -/
def canonicalSlot (selfLoop : Bool) (queries : Fin 6 → RawQuery q) (i : Fin 6) : Fin 6 :=
  Fin.find (fun j => eqProfile selfLoop queries j i = true) ⟨i, eqProfile_refl _ _ _⟩

def RepeatedConsistent (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (label : QueryIncidence.Label 6) : Prop :=
  ∀ i j, eqProfile selfLoop queries i j = true → label i = label j

instance repeatedConsistentDecidable (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (label : QueryIncidence.Label 6) : Decidable (RepeatedConsistent selfLoop queries label) := by
  unfold RepeatedConsistent
  infer_instance

def incidenceAccept (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (accept : QueryIncidence.Label 6 → Bool) (slot : Fin 6)
    (left right : QueryIncidence.Label 6) : Bool :=
  decide (accept left = true ∧ RepeatedConsistent selfLoop queries left) &&
    decide (left (canonicalSlot selfLoop queries slot) = right 0)

def predicate (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (accept : QueryIncidence.Label 6 → Bool) (slot : Fin 6) (orientation : Bool)
    (a b : QueryIncidence.Label 6) : Bool :=
  if orientation then incidenceAccept selfLoop queries accept slot b a
  else incidenceAccept selfLoop queries accept slot a b

/-- The old predicate is read in the same row-major order as a graph row. -/
def oldPredicate (old : Vector Bool (q * q)) (a b : Fin q) : Bool :=
  old[(finProdFinEquiv (a, b) : Fin (q * q))]

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Relations

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_AlphabetTableBoundsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.VerifierToCNF

open Target

abbrev BoolTriple := Bool × Bool × Bool

def tripleValue (t : BoolTriple) : Bool := (t.1 || t.2.1) || t.2.2

def chainView : List Bool → List Bool → List BoolTriple
  | [a, b, c], [] => [(a, b, c)]
  | a :: b :: rest, y :: ys => (a, b, y) :: chainView ((!y) :: rest) ys
  | _, _ => []

def fillBits (bits : List Bool) : List Bool :=
  match bits with
  | a :: b :: c :: d :: rest =>
      (!(a || b)) :: fillBits ((a || b) :: c :: d :: rest)
  | _ => []
termination_by bits.length
decreasing_by simp_wf

theorem chainView_length (bits ys : List Bool)
    (size : bits.length = ys.length + 3) :
    (chainView bits ys).length = ys.length + 1 := by
  induction ys generalizing bits with
  | nil =>
    match bits with
    | [a, b, c] => rfl
    | [] => simp at size
    | [_] => simp at size
    | [_, _] => simp at size
    | _ :: _ :: _ :: _ :: rest =>
      simp only [List.length_cons, List.length_nil] at size
      omega
  | cons y ys ih =>
    match bits with
    | [] => simp at size
    | [_] => simp only [List.length_cons, List.length_nil] at size; omega
    | a :: b :: rest =>
      have smaller : ((!y) :: rest).length = ys.length + 3 := by
        simp only [List.length_cons] at *
        omega
      have h := ih ((!y) :: rest) smaller
      simpa only [chainView, List.length_cons] using congrArg (fun n => n + 1) h

theorem fillBits_length (bits : List Bool) (size : 3 ≤ bits.length) :
    (fillBits bits).length + 3 = bits.length := by
  match bits with
  | [] => simp at size
  | [_] => simp at size
  | [_, _] => simp at size
  | [a, b, c] => simp [fillBits]
  | a :: b :: c :: d :: rest =>
    have ih := fillBits_length ((a || b) :: c :: d :: rest) (by simp)
    rw [fillBits]
    change (fillBits ((a || b) :: c :: d :: rest)).length + 1 + 3 = rest.length + 4
    simp only [List.length_cons] at ih
    omega
termination_by bits.length
decreasing_by simp_wf

abbrev Pattern (q : Nat) := Fin q → Bool

/-- The enumeration visits only the fixed-size truth table, never proof assignments. -/
def patterns : (q : Nat) → List (Pattern q)
  | 0 => [Fin.elim0]
  | q + 1 => (patterns q).flatMap (fun p => [Fin.cases false p, Fin.cases true p])

theorem flatMap_pair_length {α β : Type*} (xs : List α) (f g : α → β) :
    (xs.flatMap (fun x => [f x, g x])).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil, ih]
    omega

theorem patterns_length (q : Nat) : (patterns q).length = 2 ^ q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [patterns, flatMap_pair_length, ih, Nat.pow_succ]
    exact Nat.mul_comm _ _

abbrev PatternIndex (q : Nat) := Fin (patterns q).length
def patternAt (q : Nat) (p : PatternIndex q) : Pattern q := (patterns q)[p.val]

/-- Finite test data, with no soundness or complexity assumption. -/
structure FiniteVerifier (q : Nat) where
  «variables» : Nat
  events : Nat
  query : Fin events → Fin q → Fin «variables»
  accepts : Fin events → Pattern q → Bool

def auxiliaryCount {q : Nat} (V : FiniteVerifier q) : Nat :=
  V.events * (patterns q).length * (q - 3)

def outputVariables {q : Nat} (V : FiniteVerifier q) : Nat := V.variables + auxiliaryCount V

def oldIndex {q : Nat} (V : FiniteVerifier q) (v : Fin V.variables) : Fin (outputVariables V) :=
  Fin.castAdd (auxiliaryCount V) v

def freshIndex {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) (j : Fin (q - 3)) : Fin (outputVariables V) :=
  Fin.natAdd V.variables (finProdFinEquiv (finProdFinEquiv (e, p), j))

theorem freshIndex_value {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) (j : Fin (q - 3)) :
    (freshIndex V e p j).val =
      V.variables + ((e.val * (patterns q).length + p.val) * (q - 3) + j.val) := by
  simp [freshIndex, Fin.natAdd, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

def auxiliaryNames {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) : List (Fin (outputVariables V)) :=
  List.ofFn (freshIndex V e p)

def restrictAssignment {q : Nat} (V : FiniteVerifier q)
    (B : Fin (outputVariables V) → Bool) : Fin V.variables → Bool :=
  fun v => B (oldIndex V v)

theorem length_flatMap_constant {α β : Type*} (xs : List α) (f : α → List β) (k : Nat)
    (lengths : ∀ x ∈ xs, (f x).length = k) : (xs.flatMap f).length = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := lengths x (by simp)
    have ht := ih (fun y hy => lengths y (by simp [hy]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, hx, ht,
      Nat.add_mul, Nat.one_mul]
    omega

theorem twelve_query_factor : 2 ^ 12 * (12 - 2) = 40960 := by decide

end UniqueGamesTheorem.Foundations.PCP.VerifierToCNF

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_FinalBooleanVerifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.FinalBooleanVerifier

open Target

abbrev Label := Fin 6 → Bool

variable {V E : Type*} {n m : Nat}

def bitIndex (vertices : V ≃ Fin n) (v : V) (j : Fin 6) : Fin (n * 6) :=
  finProdFinEquiv (vertices v, j)

def labelsOfBits (vertices : V ≃ Fin n) (assignment : Fin (n * 6) → Bool) : V → Label :=
  fun v j => assignment (bitIndex vertices v j)

def bitsOfLabels (vertices : V ≃ Fin n) (labeling : V → Label) : Fin (n * 6) → Bool :=
  fun k =>
    let pair : Fin n × Fin 6 := finProdFinEquiv.symm k
    labeling (vertices.symm pair.1) pair.2

@[simp] theorem labelsOfBits_bitsOfLabels (vertices : V ≃ Fin n) (labeling : V → Label) :
    labelsOfBits vertices (bitsOfLabels vertices labeling) = labeling := by
  funext v j
  simp only [labelsOfBits, bitsOfLabels, bitIndex, Equiv.symm_apply_apply]

theorem twelve_query_auxiliary_factor : 2 ^ 12 * (12 - 3) = 36864 := by decide

end UniqueGamesTheorem.Foundations.PCP.FinalBooleanVerifier

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_FinalCNFMachineLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual finite-machine phases for the final twelve-query verifier conversion.
The graph codec stores a relation bit as the unary natural 0 or 1. The reader
below consumes those variable-length codewords, rather than treating the row
as an already available raw Boolean block. Its finite register size is fixed
at 4096 for the final alphabet, independent of the graph input size.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine

open Turing
open PCP

namespace Program

open PCP.AlphabetTable

inductive Tape
  | input | output | accumulator | scratch | vertices | darts | tail | head | rowIndex
  | archive | reverseIndex | scanWork | indexWork
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .output, .accumulator, .scratch, .vertices,
  .darts, .tail, .head, .rowIndex, .archive, .reverseIndex, .scanWork, .indexWork]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

def values (vertices darts tail head row : Nat) : Fin 5 → Nat :=
  Fin.cases vertices (Fin.cases darts (Fin.cases tail (Fin.cases head (fun _ => row))))

def source : Fin 5 → Tape :=
  Fin.cases .vertices (Fin.cases .darts (Fin.cases .tail (Fin.cases .head (fun _ => .rowIndex))))

inductive Label (headerCount rowCount : Nat)
  | copyFirst | copySecond | startVertices | readVertices | startDarts | readDarts | seedIndex
  | header (label : Emitter.Label headerCount 36864)
  | headerClearTail | headerClearHead
  | guard | startTail | readTail | startReverse | readReverse
  | headTableFirst | headTableSecond | headIndexFirst | headIndexSecond
  | headHeaderVertices | headHeaderDarts | headLookup (label : Lookup.Label)
  | readRelation
  | row (label : Emitter.Label rowCount 36864)
  | clearTail | clearHead | clearReverse | nextRow | reverseOutput
  deriving DecidableEq, Fintype

def headRoles : Fin 6 → Tape :=
  Fin.cases .archive (Fin.cases .reverseIndex (Fin.cases .scanWork
    (Fin.cases .indexWork (Fin.cases .head (fun _ => .scratch)))))

theorem headRoles_injective : Function.Injective headRoles := by
  decide

theorem source_ne_scratch (i : Fin 5) : source i ≠ Tape.scratch := by
  fin_cases i <;> decide

theorem source_ne_accumulator (i : Fin 5) : source i ≠ Tape.accumulator := by
  fin_cases i <;> decide

end Program

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFCleanup

open Turing
open FinalCNFMachine.Program (Tape )

section Redirect

variable {K Λ Λ' σ : Type} {Γ : K → Type} [DecidableEq K]

def redirectLabel (labels : Λ → Λ') (haltTarget : Option Λ') : Option Λ → Option Λ'
  | none => haltTarget
  | some label => some (labels label)

def redirectCfg (labels : Λ → Λ') (haltTarget : Option Λ') (cfg : TM2.Cfg Γ Λ σ) :
    TM2.Cfg Γ Λ' σ :=
  ⟨redirectLabel labels haltTarget cfg.l, cfg.var, cfg.stk⟩

/-- Structural redirection changes only the destinations of goto and halt. -/
def redirectStmt (labels : Λ → Λ') (haltTarget : Option Λ') :
    TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ' σ
  | .push k f next => .push k f (redirectStmt labels haltTarget next)
  | .peek k f next => .peek k f (redirectStmt labels haltTarget next)
  | .pop k f next => .pop k f (redirectStmt labels haltTarget next)
  | .load f next => .load f (redirectStmt labels haltTarget next)
  | .branch test yes no => .branch test
      (redirectStmt labels haltTarget yes) (redirectStmt labels haltTarget no)
  | .goto label => .goto (fun state => labels (label state))
  | .halt => match haltTarget with
    | none => .halt
    | some label => .goto (fun _ => label)

theorem stepAux_redirect (labels : Λ → Λ') (haltTarget : Option Λ')
    (stmt : TM2.Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (redirectStmt labels haltTarget stmt) state tapes =
      redirectCfg labels haltTarget (TM2.stepAux stmt state tapes) := by
  induction stmt generalizing state tapes with
  | push k f next ih => exact ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih => exact ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
      exact ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih => exact ih (f state) tapes
  | branch test yes no ihYes ihNo =>
      cases h : test state with
      | false => simpa only [redirectStmt, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
      | true => simpa only [redirectStmt, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto label => rfl
  | halt => cases haltTarget <;> rfl

end Redirect

/-- The raw machine has thirteen tapes. These are precisely the twelve
non-output tapes, including the original input and retained archive. -/
def chosen : List Tape :=
  [.input, .accumulator, .scratch, .vertices, .darts, .tail, .head,
    .rowIndex, .archive, .reverseIndex, .scanWork, .indexWork]

@[simp] theorem chosen_length : chosen.length = 12 := rfl

@[simp] theorem mem_chosen (tape : Tape) : tape ∈ chosen ↔ tape ≠ .output := by
  cases tape <;> simp [chosen]

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFCleanup

/-!
The concrete final-CNF machine's entry phase. It archives its complete input,
reads the two unary size fields, emits the exact formula header, and reaches
the row guard. The transition witness is assembled from actual program calls.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

open Turing
open PCP.AlphabetTable

/-- Explicit tape frame used during the header phase; all unlisted work tapes
are empty. The archive is separate from the unread input. -/
def headerFrame (input archive vertices darts rowIndex tail head accumulator : List Bool) :
    Tape → List Bool
  | .input => input
  | .archive => archive
  | .vertices => vertices
  | .darts => darts
  | .rowIndex => rowIndex
  | .tail => tail
  | .head => head
  | .accumulator => accumulator
  | _ => []

def headerInputTapes (input : List Bool) : Tape → List Bool :=
  headerFrame input [] [] [] [] [] [] []

/-- A fixed polynomial in the complete encoded input length. -/
noncomputable def headerTimePolynomial : Polynomial Nat :=
  Polynomial.C 25 * Polynomial.X + Polynomial.C 52

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_FinalCNFPattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Concrete relation addresses for the final Boolean verifier

Six-bit labels use the already checked executable little-endian enumeration.
A twelve-bit CNF pattern is split into its two endpoint labels, then addressed
in the graph table's row-major order. This fixed address map uses the actual
`VerifierToCNF.patternAt` enumeration, so no assumed correspondence between
two enumeration orders is needed. The graph interpretation is an explicit
relabeling of the validated table semantics.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern

open PCP
open scoped BigOperators

abbrev Label := FinalBooleanVerifier.Label

def leftHalf (bits : VerifierToCNF.Pattern 12) : Label :=
  fun j => bits (Fin.castAdd 6 j)

def rightHalf (bits : VerifierToCNF.Pattern 12) : Label :=
  fun j => bits (Fin.natAdd 6 j)

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_FinalCNFTemplate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Fixed literal templates for the twelve-query converter. All control data have
constant size: twelve query references, nine auxiliary references, ten clauses,
and three literal slots. Pattern bits remain symbolic throughout the proof.

These templates specify the actual serialized rows.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFTemplate

open Target PCP

inductive Reference where
  | query : Fin 12 → Reference
  | auxiliary : Fin 9 → Reference
  deriving DecidableEq

structure LiteralTemplate where
  reference : Reference
  positive : Bool
  deriving DecidableEq

abbrev ClauseTemplate := Vector LiteralTemplate 3

def queryLiteral (bits : Fin 12 → Bool) (i : Fin 12) : LiteralTemplate :=
  ⟨.query i, !(bits i)⟩

def auxiliaryLiteral (j : Fin 9) (positive : Bool) : LiteralTemplate :=
  ⟨.auxiliary j, positive⟩

def tautologyTemplate : ClauseTemplate :=
  #v[⟨.query 0, true⟩, ⟨.query 0, false⟩, ⟨.query 0, true⟩]

/-- The same prefix-chain clauses used by `splitLong`, in their output order. -/
def chainTemplates (bits : Fin 12 → Bool) : Vector ClauseTemplate 10 :=
  #v[
    #v[queryLiteral bits 0, queryLiteral bits 1, auxiliaryLiteral 0 true],
    #v[auxiliaryLiteral 0 false, queryLiteral bits 2, auxiliaryLiteral 1 true],
    #v[auxiliaryLiteral 1 false, queryLiteral bits 3, auxiliaryLiteral 2 true],
    #v[auxiliaryLiteral 2 false, queryLiteral bits 4, auxiliaryLiteral 3 true],
    #v[auxiliaryLiteral 3 false, queryLiteral bits 5, auxiliaryLiteral 4 true],
    #v[auxiliaryLiteral 4 false, queryLiteral bits 6, auxiliaryLiteral 5 true],
    #v[auxiliaryLiteral 5 false, queryLiteral bits 7, auxiliaryLiteral 6 true],
    #v[auxiliaryLiteral 6 false, queryLiteral bits 8, auxiliaryLiteral 7 true],
    #v[auxiliaryLiteral 7 false, queryLiteral bits 9, auxiliaryLiteral 8 true],
    #v[auxiliaryLiteral 8 false, queryLiteral bits 10, queryLiteral bits 11]]

def blockTemplates (accepted : Bool) (bits : Fin 12 → Bool) : Vector ClauseTemplate 10 :=
  if accepted then Vector.replicate 10 tautologyTemplate else chainTemplates bits

def templates (accepted : Bool) (bits : Fin 12 → Bool) : List ClauseTemplate :=
  (blockTemplates accepted bits).toList

/-- Fixed clause/slot indexing for the machine's finite emission plan. -/
def literalAt (accepted : Bool) (bits : Fin 12 → Bool)
    (clause : Fin 10) (slot : Fin 3) : LiteralTemplate :=
  (blockTemplates accepted bits)[clause][slot]

@[simp] theorem templates_length (accepted : Bool) (bits : Fin 12 → Bool) :
    (templates accepted bits).length = 10 := Vector.length_toList

theorem templates_true (bits : Fin 12 → Bool) :
    templates true bits = List.replicate 10 tautologyTemplate := by rfl

theorem templates_false (bits : Fin 12 → Bool) :
    templates false bits = (chainTemplates bits).toList := by rfl

def literalWords (index : Reference → Nat) (literal : LiteralTemplate) : List Nat :=
  [index literal.reference, if literal.positive then 1 else 0]

def clauseWords (index : Reference → Nat) (clause : ClauseTemplate) : List Nat :=
  literalWords index clause[0] ++ literalWords index clause[1] ++ literalWords index clause[2]

def words (accepted : Bool) (bits : Fin 12 → Bool) (index : Reference → Nat) : List Nat :=
  (templates accepted bits).flatMap (clauseWords index)

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFTemplate

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_FinalCNFRowPlanLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
The fixed finite emission plan for one directed graph row. All choices based
on the relation are functions of its 4096-bit finite register. Vertex counts,
endpoint names and row indices are read by preserving unary scans.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

open PCP PCP.AlphabetTable

section Templates

open FinalCNFTemplate

def referenceValue (vertices tail head row pattern : Nat) : Reference → Nat
  | .query i => if i.val < 6 then 6 * tail + i.val else 6 * head + (i.val - 6)
  | .auxiliary j => 6 * vertices + 36864 * row + (9 * pattern + j.val)

def auxiliaryFlag : Reference → Bool
  | .query _ => false
  | .auxiliary _ => true

def tailFlag : Reference → Bool
  | .query i => decide (i.val < 6)
  | .auxiliary _ => false

def headFlag : Reference → Bool
  | .query i => decide (6 ≤ i.val)
  | .auxiliary _ => false

end Templates

/-!
Actual finite-machine execution of the final converter's row phases. These
certificates use the concrete program statements, preserve all other tapes,
and expose the precise concatenated output of the fixed emission plan.
-/

open Turing

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineFixedDivMod
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) (d : Nat) := (σ × Fin d) × Option Bool

def residue (d : Nat) (positive : 0 < d) (n : Nat) : Fin d :=
  ⟨n % d, Nat.mod_lt n positive⟩

def nextResidue (d : Nat) (positive : 0 < d) (r : Fin d) : Fin d :=
  residue d positive (r.val + 1)

theorem nextResidue_residue (d : Nat) (positive : 0 < d) (n : Nat) :
    nextResidue d positive (residue d positive n) = residue d positive (n + 1) := by
  apply Fin.ext
  change (n % d + 1) % d = (n + 1) % d
  simp only [Nat.add_mod, Nat.mod_mod]

def scanLoop (d : Nat) (positive : 0 < d) (source quotient : K)
    (scanLabel : Λ) (emitterLabel : Fin d → Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ d) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.branch (fun state => decide ((nextResidue d positive state.1.2).val = 0))
        (.push quotient (fun _ => true)
          (.load (fun state => ((state.1.1, nextResidue d positive state.1.2), state.2))
            (.goto fun _ => scanLabel)))
        (.load (fun state => ((state.1.1, nextResidue d positive state.1.2), state.2))
          (.goto fun _ => scanLabel)))
      (.push source (fun _ => false) (.goto fun state => emitterLabel state.1.2)))

end UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_ZigzagGraphsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Actual graph squares and zigzag products

Rotations operate on actual vertex-port pairs. All returned ports are retained,
including ports belonging to loops and parallel edges. Each construction is a
palindrome of involutions and hence defines a reversible regular port graph.
-/

namespace UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs

open PoweringWalks

variable {V D E : Type*}

/-- Regard a checked involution as a permutation with the same inverse. -/
def involutionEquiv {A : Type*} (f : A → A) (hf : Function.Involutive f) : A ≃ A where
  toFun := f
  invFun := f
  left_inv := hf
  right_inv := hf

/-- A palindrome of two involutions is itself an involution. -/
theorem palindrome_involutive {A : Type*} (B P : A ≃ A)
    (hB : Function.Involutive B) (hP : Function.Involutive P) :
    Function.Involutive (B.trans (P.trans B)) := by
  intro x
  change B (P (B (B (P (B x))))) = x
  rw [hB, hP, hB]

/-- Cross an original edge using the first port; retain its return port. -/
def squareFirst (G : PortGraph V D) (s : V × (D × D)) : V × (D × D) :=
  let step := G.rot (s.1, s.2.1)
  (step.1, (step.2, s.2.2))

theorem squareFirst_involutive (G : PortGraph V D) : Function.Involutive (squareFirst G) := by
  rintro ⟨v, d₁, d₂⟩
  change ((G.rot (G.rot (v, d₁))).1, ((G.rot (G.rot (v, d₁))).2, d₂)) =
    (v, (d₁, d₂))
  rw [G.rot_involutive]

def squareSwap (s : V × (D × D)) : V × (D × D) := (s.1, (s.2.2, s.2.1))

theorem squareSwap_involutive : Function.Involutive (squareSwap (V := V) (D := D)) := by
  rintro ⟨v, d₁, d₂⟩
  rfl

/-- The actual graph square. The two return ports appear in reverse order. -/
def square (G : PortGraph V D) : PortGraph V (D × D) := by
  let B := involutionEquiv (squareFirst G) (squareFirst_involutive G)
  let P := involutionEquiv (squareSwap (V := V) (D := D)) squareSwap_involutive
  exact
    { rot := B.trans (P.trans B)
      rot_involutive := palindrome_involutive B P
        (squareFirst_involutive G) squareSwap_involutive }

@[simp] theorem square_rot_apply (G : PortGraph V D) (v : V) (d₁ d₂ : D) :
    (square G).rot (v, (d₁, d₂)) =
      let first := G.rot (v, d₁)
      let second := G.rot (first.1, d₂)
      (second.1, (second.2, first.2)) := rfl

@[simp] theorem square_next (G : PortGraph V D) (v : V) (d₁ d₂ : D) :
    next (square G) v (d₁, d₂) = next G (next G v d₁) d₂ := rfl

/-- One inner step in a cloud, retaining its return port and the unused port. -/
def cloudFirst (H : PortGraph D E) (s : (V × D) × (E × E)) :
    (V × D) × (E × E) :=
  let step := H.rot (s.1.2, s.2.1)
  ((s.1.1, step.1), (step.2, s.2.2))

theorem cloudFirst_involutive (H : PortGraph D E) :
    Function.Involutive (cloudFirst (V := V) H) := by
  rintro ⟨⟨v, d⟩, ⟨e₁, e₂⟩⟩
  change ((v, (H.rot (H.rot (d, e₁))).1), ((H.rot (H.rot (d, e₁))).2, e₂)) =
    ((v, d), (e₁, e₂))
  rw [H.rot_involutive]

/-- Cross the outer graph edge and swap the two inner ports. -/
def crossCloud (G : PortGraph V D) (s : (V × D) × (E × E)) :
    (V × D) × (E × E) := (G.rot s.1, (s.2.2, s.2.1))

theorem crossCloud_involutive (G : PortGraph V D) :
    Function.Involutive (crossCloud (E := E) G) := by
  rintro ⟨x, e₁, e₂⟩
  change (G.rot (G.rot x), (e₁, e₂)) = (x, (e₁, e₂))
  rw [G.rot_involutive]

/-- The actual zigzag product: inner step, outer edge, inner step. -/
def zigzag (G : PortGraph V D) (H : PortGraph D E) : PortGraph (V × D) (E × E) := by
  let B := involutionEquiv (cloudFirst (V := V) H) (cloudFirst_involutive H)
  let P := involutionEquiv (crossCloud (E := E) G) (crossCloud_involutive G)
  exact
    { rot := B.trans (P.trans B)
      rot_involutive := palindrome_involutive B P
        (cloudFirst_involutive H) (crossCloud_involutive G) }

@[simp] theorem zigzag_rot_apply (G : PortGraph V D) (H : PortGraph D E)
    (v : V) (d : D) (e₁ e₂ : E) :
    (zigzag G H).rot ((v, d), (e₁, e₂)) =
      let first := H.rot (d, e₁)
      let middle := G.rot (v, first.1)
      let last := H.rot (middle.2, e₂)
      ((middle.1, last.1), (last.2, first.2)) := rfl

/-! ## Exact averaging operators -/

end UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs

end

section

/-!
# A concrete finite family from the Cayley base

The initial graph has one vertex and the fixed number of loop ports. Each
subsequent graph is the actual square-and-zigzag construction. Consequently
the vertex sizes are exact powers of one fixed integer, including size one.
The finite base is selected from the proved existence theorem.
-/

namespace UniqueGamesTheorem.Foundations.PCP.ExpanderFamily

open PoweringWalks SpectralReturn Expanders

def growth : Nat := baseDegree ^ 4

theorem growth_gt_one : 1 < growth := by
  norm_num [growth, baseDegree, initialDegree, basePower]

/-- The least geometric level covering a requested size. `Nat.clog` is the
ordinary finite ceiling logarithm algorithm. -/
def level (k : Nat) : Nat := Nat.clog growth k

def size (k : Nat) : Nat := growth ^ level k

theorem le_size (k : Nat) : k ≤ size k := Nat.le_pow_clog growth_gt_one k

theorem size_le_mul {k : Nat} (hk : 0 < k) : size k ≤ growth * k := by
  by_cases hk1 : k = 1
  · subst k
    simpa [size, level] using growth_gt_one.le
  · have hk2 : 1 < k := by omega
    have hl : 0 < level k := Nat.clog_pos growth_gt_one hk2
    have hp : growth ^ (level k).pred < k :=
      Nat.pow_pred_clog_lt_self growth_gt_one hk2
    have he : (level k).pred + 1 = level k := Nat.succ_pred_eq_of_pos hl
    calc
      size k = growth ^ ((level k).pred + 1) := by rw [he]; rfl
      _ = growth * growth ^ (level k).pred := by rw [pow_succ, Nat.mul_comm]
      _ ≤ growth * k := Nat.mul_le_mul_left growth hp.le

end UniqueGamesTheorem.Foundations.PCP.ExpanderFamily

end

section

/-!
# Padding actual tail fibers to the geometric graph-family sizes

Every nonempty cloud is padded to the next family size. Empty clouds stay
empty, so their old vertices do not create new darts. Explicit equivalences
identify padded tail fibers and partition all darts by their original tails.
These facts give the global size bound without an expansion assumption.
-/

namespace UniqueGamesTheorem.Foundations.PCP.CloudPadding

open scoped BigOperators
open DegreeReplacement

variable {V E A : Type*}

/-- The actual padded tail fiber contains old darts and exactly the dummy
darts indexed by that tail, with transport along the sigma index equality. -/
def paddedCloudEquiv (G : ConstraintGraph V E A) (dummy : V → Type*) (v : V) :
    Cloud (paddedGraph G dummy) v ≃ Cloud G v ⊕ dummy v where
  toFun := by
    rintro ⟨e, he⟩
    rcases e with e | ⟨w, d⟩
    · exact Sum.inl ⟨e, he⟩
    · change w = v at he
      cases he
      exact Sum.inr d
  invFun := fun z => match z with
    | Sum.inl e => ⟨Sum.inl e.val, e.property⟩
    | Sum.inr d => ⟨Sum.inr ⟨v, d⟩, rfl⟩
  left_inv := by
    rintro ⟨e, he⟩
    rcases e with e | ⟨w, d⟩
    · rfl
    · change w = v at he
      cases he
      rfl
  right_inv := by
    intro z
    cases z <;> rfl

/-- Every original dart occurs in exactly one cloud. -/
def dartCloudEquiv (G : ConstraintGraph V E A) : E ≃ Σ v : V, Cloud G v where
  toFun e := ⟨G.tail e, ⟨e, rfl⟩⟩
  invFun z := z.2.val
  left_inv _ := rfl
  right_inv := by
    rintro ⟨v, ⟨e, he⟩⟩
    cases he
    rfl

section Finite

variable [Fintype V] [DecidableEq V] [Fintype E]

theorem sum_card_cloud (G : ConstraintGraph V E A) :
    (∑ v, Fintype.card (Cloud G v)) = Fintype.card E := by
  simpa only [Fintype.card_sigma] using (Fintype.card_congr (dartCloudEquiv G)).symm

end Finite

end UniqueGamesTheorem.Foundations.PCP.CloudPadding

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_ExpanderTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.ExpanderTables

open PoweringWalks SpectralReturn

def rowIndex (v d : Nat) : Fin v × Fin d ≃ Fin (v * d) := finProdFinEquiv

theorem rowIndex_val (v d : Nat) (x : Fin v × Fin d) :
    (rowIndex v d x).val = x.2.val + d * x.1.val := rfl

/-- Stored reverse-dart indices, with a proof of the finite involution law. -/
structure Table (v d : Nat) where
  rows : Vector (Fin (v * d)) (v * d)
  involutive : Function.Involutive (fun i : Fin (v * d) => rows[i])

def reverseIndex {v d : Nat} (table : Table v d) (i : Fin (v * d)) : Fin (v * d) :=
  table.rows[i]

def lookup {v d : Nat} (table : Table v d) (x : Fin v × Fin d) : Fin v × Fin d :=
  (rowIndex v d).symm (reverseIndex table (rowIndex v d x))

theorem lookup_involutive {v d : Nat} (table : Table v d) :
    Function.Involutive (lookup table) := by
  intro x
  simp only [lookup, Equiv.apply_symm_apply]
  exact (congrArg (rowIndex v d).symm (table.involutive (rowIndex v d x))).trans
    ((rowIndex v d).symm_apply_apply x)

def graph {v d : Nat} (table : Table v d) : PortGraph (Fin v) (Fin d) where
  rot := ZigzagGraphs.involutionEquiv (lookup table) (lookup_involutive table)
  rot_involutive := lookup_involutive table

@[simp] theorem graph_rot {v d : Nat} (table : Table v d) (x : Fin v × Fin d) :
    (graph table).rot x = lookup table x := rfl

def ofGraph {v d : Nat} (G : PortGraph (Fin v) (Fin d)) : Table v d where
  rows := Vector.ofFn (fun i => rowIndex v d (G.rot ((rowIndex v d).symm i)))
  involutive := by
    intro i
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, Equiv.symm_apply_apply]
    exact (congrArg (rowIndex v d) (G.rot_involutive ((rowIndex v d).symm i))).trans
      ((rowIndex v d).apply_symm_apply i)

@[simp] theorem lookup_ofGraph {v d : Nat} (G : PortGraph (Fin v) (Fin d))
    (x : Fin v × Fin d) : lookup (ofGraph G) x = G.rot x := by
  simp only [lookup, reverseIndex, ofGraph, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
    Equiv.symm_apply_apply]

theorem graph_ext {V D : Type*} {G H : PortGraph V D}
    (h : ∀ x, G.rot x = H.rot x) : G = H := by
  have hr : G.rot = H.rot := Equiv.ext h
  cases G
  cases H
  cases hr
  rfl

@[simp] theorem graph_ofGraph {v d : Nat} (G : PortGraph (Fin v) (Fin d)) :
    graph (ofGraph G) = G := graph_ext (lookup_ofGraph G)

/-- Explicit mixed-radix vertex coordinates for one square/zigzag step. -/
def vertexIndex (v q : Nat) : Fin v × (Fin q × Fin q) ≃ Fin (v * (q * q)) :=
  (Equiv.prodCongr (Equiv.refl _) (rowIndex q q)).trans (rowIndex v (q * q))

/-- The actual square/zigzag graph, expressed in the table's integer coordinates. -/
def stepGraph {v d : Nat} (G : Table v (d * d))
    (H : Table ((d * d) * (d * d)) d) :
    PortGraph (Fin (v * ((d * d) * (d * d)))) (Fin (d * d)) :=
  GraphTransport.reindex
    (ZigzagGraphs.zigzag (ZigzagGraphs.square (graph G))
      (GraphTransport.reindex (graph H) (rowIndex (d * d) (d * d)).symm (Equiv.refl _)))
    (vertexIndex v (d * d)) (rowIndex d d)

/-- Materialize every row of the next table in the declared order. -/
def step {v d : Nat} (G : Table v (d * d))
    (H : Table ((d * d) * (d * d)) d) :
    Table (v * ((d * d) * (d * d))) (d * d) := ofGraph (stepGraph G H)

/-- A row uses exactly the displayed four lookups in already stored tables. -/
def stepLookup {v d : Nat} (G : Table v (d * d))
    (H : Table ((d * d) * (d * d)) d)
    (x : Fin (v * ((d * d) * (d * d))) × Fin (d * d)) :
    Fin (v * ((d * d) * (d * d))) × Fin (d * d) :=
  let vc := (rowIndex v ((d * d) * (d * d))).symm x.1
  let ports := (rowIndex d d).symm x.2
  let first := lookup H (vc.2, ports.1)
  let squarePorts := (rowIndex (d * d) (d * d)).symm first.1
  let outerFirst := lookup G (vc.1, squarePorts.1)
  let outerSecond := lookup G (outerFirst.1, squarePorts.2)
  let last := lookup H (rowIndex (d * d) (d * d) (outerSecond.2, outerFirst.2), ports.2)
  (rowIndex v ((d * d) * (d * d)) (outerSecond.1, last.1),
    rowIndex d d (last.2, first.2))

theorem lookup_step {v d : Nat} (G : Table v (d * d))
    (H : Table ((d * d) * (d * d)) d)
    (x : Fin (v * ((d * d) * (d * d))) × Fin (d * d)) :
    lookup (step G H) x = stepLookup G H x := by
  simp [step, stepGraph, GraphTransport.reindex,
    Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.prodCongr_symm, Equiv.refl_apply, vertexIndex, Equiv.apply_symm_apply,
    ZigzagGraphs.zigzag, ZigzagGraphs.square, ZigzagGraphs.involutionEquiv,
    ZigzagGraphs.cloudFirst, ZigzagGraphs.crossCloud, graph_rot,
    stepLookup, Prod.map, Equiv.symm_symm]
  all_goals repeat' constructor

def initial (d : Nat) : Table 1 (d * d) :=
  ofGraph { rot := Equiv.refl _, rot_involutive := fun _ => rfl }

def vertexCount (q : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => vertexCount q n * (q * q)

theorem vertexCount_eq (q n : Nat) : vertexCount q n = (q * q) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [vertexCount, ih, pow_succ]

theorem vertexCount_positive {q : Nat} (hq : 0 < q) (n : Nat) :
    0 < vertexCount q n := by
  rw [vertexCount_eq]
  exact Nat.pow_pos (Nat.mul_pos hq hq)

/-- A bottom-up vector of rotation rows. The recursive result is passed once
to `step`, whose row formula reads only that already materialized table. -/
def family {d : Nat} (H : Table ((d * d) * (d * d)) d) :
    (n : Nat) → Table (vertexCount (d * d) n) (d * d)
  | 0 => initial d
  | n + 1 => step (family H n) H

end UniqueGamesTheorem.Foundations.PCP.ExpanderTables

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_ExpanderRowControlLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.ExpanderRowControl

open ExpanderTables

abbrev degree (d : Nat) : Nat := d * d
abbrev cloudSize (d : Nat) : Nat := degree d * degree d
abbrev rowFactor (d : Nat) : Nat := cloudSize d * degree d

/-- The encoded vertex of `firstH` already stores both square ports.
The two graph-return registers and final-H register are overwritten by the
corresponding callbacks. Every field is bounded independently of table size. -/
structure Control (d : Nat) where
  firstH : Fin (cloudSize d) × Fin d
  lastInput : Fin d
  firstG : Fin (degree d)
  secondG : Fin (degree d)
  lastH : Fin (cloudSize d) × Fin d
  deriving DecidableEq, Fintype

def squarePorts {d : Nat} (s : Control d) : Fin (degree d) × Fin (degree d) :=
  (rowIndex (degree d) (degree d)).symm s.firstH.1

/-- Consume the finite cloud coordinate and input port, and perform the first
lookup in the fixed table. Initial register values need no inhabitance choice. -/
def start {d : Nat} (H : Table (cloudSize d) d)
    (cloud : Fin (cloudSize d)) (port : Fin (degree d)) : Control d :=
  let ports := (rowIndex d d).symm port
  let first := lookup H (cloud, ports.1)
  let square := (rowIndex (degree d) (degree d)).symm first.1
  { firstH := first
    lastInput := ports.2
    firstG := square.1
    secondG := square.2
    lastH := first }

def receiveFirst {d : Nat} (s : Control d) (returnedPort : Fin (degree d)) : Control d :=
  { s with firstG := returnedPort }

/-- The second graph remainder completes the final lookup in the fixed table.
The square return ports are ordered second, first, as in `stepLookup`. -/
def receiveSecond {d : Nat} (H : Table (cloudSize d) d)
    (s : Control d) (returnedPort : Fin (degree d)) : Control d :=
  { s with
    secondG := returnedPort
    lastH := lookup H
      (rowIndex (degree d) (degree d) (returnedPort,s.firstG),s.lastInput) }

def firstOffset {d : Nat} (s : Control d) : Fin (degree d) := (squarePorts s).1
def secondOffset {d : Nat} (s : Control d) : Fin (degree d) := (squarePorts s).2

def outputPort {d : Nat} (s : Control d) : Fin (degree d) :=
  rowIndex d d (s.lastH.2,s.firstH.2)

/-- The entire bounded contribution to the emitted row: output port plus
`q` times output cloud, with `q = d*d`. -/
def outputOffset {d : Nat} (s : Control d) : Fin (rowFactor d) :=
  rowIndex (cloudSize d) (degree d) (s.lastH.1,outputPort s)

def firstAddress {d : Nat} (vertex : Nat) (s : Control d) : Nat :=
  degree d * vertex + (firstOffset s).val

def secondAddress {d : Nat} (vertex : Nat) (s : Control d) : Nat :=
  degree d * vertex + (secondOffset s).val

def outputAddress {d : Nat} (vertex : Nat) (s : Control d) : Nat :=
  rowFactor d * vertex + (outputOffset s).val

@[simp] theorem firstOffset_receiveFirst {d : Nat} (s : Control d) (r : Fin (degree d)) :
    firstOffset (receiveFirst s r) = firstOffset s := rfl

@[simp] theorem secondOffset_receiveFirst {d : Nat} (s : Control d) (r : Fin (degree d)) :
    secondOffset (receiveFirst s r) = secondOffset s := rfl

@[simp] theorem receiveFirst_port {d : Nat} (s : Control d) (r : Fin (degree d)) :
    (receiveFirst s r).firstG = r := rfl

@[simp] theorem receiveSecond_port {d : Nat} (H : Table (cloudSize d) d)
    (s : Control d) (r : Fin (degree d)) : (receiveSecond H s r).secondG = r := rfl

theorem firstAddress_eq_rowIndex {v d : Nat} (vertex : Fin v) (s : Control d) :
    firstAddress vertex.val s =
      (rowIndex v (degree d) (vertex,firstOffset s)).val := by
  rw [rowIndex_val]
  exact Nat.add_comm _ _

theorem secondAddress_eq_rowIndex {v d : Nat} (vertex : Fin v) (s : Control d) :
    secondAddress vertex.val s =
      (rowIndex v (degree d) (vertex,secondOffset s)).val := by
  rw [rowIndex_val]
  exact Nat.add_comm _ _

theorem rowIndex_lookup {v q : Nat} (G : Table v q) (x : Fin v × Fin q) :
    rowIndex v q (lookup G x) = reverseIndex G (rowIndex v q x) := by
  simp only [lookup, Equiv.apply_symm_apply]

def outputPair {v d : Nat} (vertex : Fin v) (s : Control d) :
    Fin (v * cloudSize d) × Fin (degree d) :=
  (rowIndex v (cloudSize d) (vertex,s.lastH.1),outputPort s)

theorem outputAddress_eq_rowIndex {v d : Nat} (vertex : Fin v) (s : Control d) :
    outputAddress vertex.val s =
      (rowIndex (v * cloudSize d) (degree d) (outputPair vertex s)).val := by
  simp only [outputAddress, outputOffset, outputPair, rowIndex_val, rowFactor]
  ring

/-- Pure row semantics: exactly two lookups in the input table. The two fixed
H lookups occur inside `start` and `receiveSecond`. This is not a machine trace. -/
def evaluateRow {v d : Nat} (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (cloud : Fin (cloudSize d)) (port : Fin (degree d)) :
    Fin v × Control d :=
  let s₀ := start H cloud port
  let g₁ := lookup G (vertex,firstOffset s₀)
  let s₁ := receiveFirst s₀ g₁.2
  let g₂ := lookup G (g₁.1,secondOffset s₁)
  (g₂.1, receiveSecond H s₁ g₂.2)

/-- The finite callback sequence computes exactly the previously checked
square/zigzag lookup, including both reversed square ports. -/
theorem evaluateRow_eq_lookup_step {v d : Nat}
    (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (cloud : Fin (cloudSize d)) (port : Fin (degree d)) :
    outputPair (evaluateRow G H vertex cloud port).1 (evaluateRow G H vertex cloud port).2 =
      lookup (step G H) (rowIndex v (cloudSize d) (vertex,cloud),port) := by
  rw [lookup_step]
  simp only [evaluateRow, start, receiveFirst, receiveSecond, firstOffset, secondOffset,
    squarePorts, outputPair, outputPort, stepLookup, Equiv.symm_apply_apply]

theorem outputAddress_eq_step_row {v d : Nat}
    (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (cloud : Fin (cloudSize d)) (port : Fin (degree d)) :
    outputAddress (evaluateRow G H vertex cloud port).1.val (evaluateRow G H vertex cloud port).2 =
      (rowIndex (v * cloudSize d) (degree d)
        (lookup (step G H) (rowIndex v (cloudSize d) (vertex,cloud),port))).val := by
  rw [outputAddress_eq_rowIndex, evaluateRow_eq_lookup_step]

/-- The emitted natural number is the actual stored row, not just an
extensionally equivalent endpoint pair. -/
theorem outputAddress_eq_step_reverseIndex {v d : Nat}
    (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (cloud : Fin (cloudSize d)) (port : Fin (degree d)) :
    outputAddress (evaluateRow G H vertex cloud port).1.val (evaluateRow G H vertex cloud port).2 =
      (reverseIndex (step G H) (rowIndex (v * cloudSize d) (degree d)
        (rowIndex v (cloudSize d) (vertex,cloud),port))).val := by
  rw [outputAddress_eq_step_row, rowIndex_lookup]

end UniqueGamesTheorem.Foundations.PCP.ExpanderRowControl

end

section

/-!
# Raw natural-word serialization of actual expander rotation tables

The list keeps the stored row order `port + degree * vertex`; no header is
inserted. Lookup equalities and complete unary output lengths are data facts,
not machine execution certificates. Kernel-checked with Lean 4.33.1.
-/

namespace UniqueGamesTheorem.Foundations.PCP.ExpanderTableWords

open ExpanderTables
open UniqueGamesTheorem.Foundations.Complexity (encodeWords )

variable {v d : ℕ}

def rotationWords (table : Table v d) : List Nat := table.rows.toList.map Fin.val

@[simp] theorem rotationWords_length (table : Table v d) :
    (rotationWords table).length = v * d := by
  simp [rotationWords]

theorem rotationWords_getElem (table : Table v d) (i : ℕ) (hi : i < v * d) :
    (rotationWords table)[i]'(by simpa only [rotationWords_length] using hi) =
      (reverseIndex table ⟨i, hi⟩).val := by
  simp only [rotationWords, List.getElem_map, Vector.getElem_toList,
    reverseIndex, Fin.getElem_fin]

/-- The exact zero-based lookup hypothesis consumed by the machine lookup API. -/
theorem rotationWords_getElem? (table : Table v d) (i : Fin (v * d)) :
    (rotationWords table)[i.val]? = some (reverseIndex table i).val := by
  apply List.getElem?_eq_some_iff.mpr
  exact ⟨by simpa only [rotationWords_length] using i.isLt,
    rotationWords_getElem table i.val i.isLt⟩

theorem rotationWords_entry_lt (table : Table v d) (n : ℕ)
    (hn : n ∈ rotationWords table) : n < v * d := by
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hn
  exact a.isLt

/-- The serialized reverse index decodes to the actual table lookup. -/
theorem rotationWords_lookup (table : Table v d) (x : Fin v × Fin d) :
    (rotationWords table)[(rowIndex v d x).val]? =
      some (rowIndex v d (lookup table x)).val := by
  simpa only [lookup, Equiv.apply_symm_apply] using
    rotationWords_getElem? table (rowIndex v d x)

/-- Both the input and output use port-first mixed-radix row coordinates. -/
theorem rotationWords_row_order (table : Table v d) (x : Fin v × Fin d) :
    (rotationWords table)[x.2.val + d * x.1.val]? =
      some ((lookup table x).2.val + d * (lookup table x).1.val) := by
  simpa only [rowIndex_val] using rotationWords_lookup table x

end UniqueGamesTheorem.Foundations.PCP.ExpanderTableWords

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_FinalCNFLoopLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

inductive Tape
  | inputVertex | table | output
  | emitScratch | queryReverse | queryIndex
  | lookupOutput | lookupWork | lookupRestore
  | quotientFirst | quotientSecond | remainderFirst | remainderSecond
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.inputVertex, .table, .output, .emitScratch,
  .queryReverse, .queryIndex, .lookupOutput, .lookupWork, .lookupRestore, .quotientFirst,
  .quotientSecond, .remainderFirst, .remainderSecond]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Label (d : Nat)
  | initialize_
  | firstEmit (label : PCP.AlphabetTable.Emitter.Label 3 (degree d))
  | firstReverse
  | firstLookup (label : MachinePreservingLookupClean.Label)
  | firstScan
  | firstResidue (r : Fin (degree d))
  | clearQuery
  | secondEmit (label : PCP.AlphabetTable.Emitter.Label 3 (degree d))
  | secondReverse
  | secondLookup (label : MachinePreservingLookupClean.Label)
  | secondScan
  | secondResidue (r : Fin (degree d))
  | outputEmit (label : PCP.AlphabetTable.Emitter.Label 3 (rowFactor d))
  | cleanup (i : Fin 6)
  | done
  deriving DecidableEq, Fintype

abbrev Ambient (ρ : Type) (d : Nat) := ρ × Control d
abbrev State (ρ : Type) (d : Nat) :=
  PCP.AlphabetTable.Emitter.State (Ambient ρ d × Fin (degree d))

/-- The residue and the emitter's unit field are just permuted; no tape is
read or written by this static change of finite state coordinates. -/
def divisionStates (ρ : Type) (d : Nat) :
    MachineFixedDivMod.State (Ambient ρ d × Unit) (degree d) ≃ State ρ d where
  toFun s := (((s.1.1.1, s.1.2), ()), s.2)
  invFun s := (((s.1.1.1, ()), s.1.1.2), s.2)
  left_inv := by rintro ⟨⟨⟨a, u⟩, r⟩, b⟩; cases u; rfl
  right_inv := by rintro ⟨⟨⟨a, r⟩, u⟩, b⟩; cases u; rfl

def firstFinish {ρ : Type} {d : Nat} (s : Ambient ρ d × Unit)
    (r : Fin (degree d)) : Ambient ρ d × Unit :=
  ((s.1.1, receiveFirst s.1.2 r), ())

def lookupTape : Fin 5 → Tape
  | ⟨0, _⟩ => .table
  | ⟨1, _⟩ => .queryIndex
  | ⟨2, _⟩ => .lookupWork
  | ⟨3, _⟩ => .lookupOutput
  | _ => .lookupRestore

def dirtyTape : Fin 6 → Tape
  | ⟨0, _⟩ => .queryIndex
  | ⟨1, _⟩ => .lookupOutput
  | ⟨2, _⟩ => .quotientFirst
  | ⟨3, _⟩ => .quotientSecond
  | ⟨4, _⟩ => .remainderFirst
  | _ => .remainderSecond

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_AmplificationIteration
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

def run {X : Type*} (step : X → X) : Nat → X → X
  | 0, x => x
  | n + 1, x => step (run step n x)

end UniqueGamesTheorem.Foundations.PCP.AmplificationIteration

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_OverlayLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Overlay a regular constraint graph with an actual regular port graph whose
new constraints always accept. The port sets are disjoint, so all original
rejected darts are retained exactly. The averaging operator is the actual
degree-weighted mixture of the two graph averages.
-/

open scoped BigOperators

namespace UniqueGamesTheorem.Foundations.PCP.Overlay

open PoweringWalks SpectralReturn

variable {V D E A : Type*}

def originalPortGraph (G : ConstraintGraph V (V × D) A) : PortGraph V D where
  rot := G.reverse
  rot_involutive := G.reverse_involutive

def rotate (G : PortGraph V D) (H : PortGraph V E) :
    V × (D ⊕ E) → V × (D ⊕ E)
  | (v, Sum.inl d) => ((G.rot (v, d)).1, Sum.inl (G.rot (v, d)).2)
  | (v, Sum.inr e) => ((H.rot (v, e)).1, Sum.inr (H.rot (v, e)).2)

theorem rotate_involutive (G : PortGraph V D) (H : PortGraph V E) :
    Function.Involutive (rotate G H) := by
  rintro ⟨v, p⟩
  rcases p with d | e
  · exact congrArg (fun a : V × D => (a.1, (Sum.inl a.2 : D ⊕ E)))
      (G.rot_involutive (v, d))
  · exact congrArg (fun a : V × E => (a.1, (Sum.inr a.2 : D ⊕ E)))
      (H.rot_involutive (v, e))

def portGraph (G : PortGraph V D) (H : PortGraph V E) : PortGraph V (D ⊕ E) where
  rot :=
    { toFun := rotate G H
      invFun := rotate G H
      left_inv := rotate_involutive G H
      right_inv := rotate_involutive G H }
  rot_involutive := rotate_involutive G H

@[simp] theorem portGraph_rot_inl (G : PortGraph V D) (H : PortGraph V E)
    (v : V) (d : D) :
    (portGraph G H).rot (v, Sum.inl d) =
      ((G.rot (v, d)).1, Sum.inl (G.rot (v, d)).2) := rfl

@[simp] theorem portGraph_rot_inr (G : PortGraph V D) (H : PortGraph V E)
    (v : V) (e : E) :
    (portGraph G H).rot (v, Sum.inr e) =
      ((H.rot (v, e)).1, Sum.inr (H.rot (v, e)).2) := rfl

/-- Keep the original tests and add always-accepting tests on the overlay ports. -/
def constraintGraph (G : ConstraintGraph V (V × D) A) (H : PortGraph V E) :
    ConstraintGraph V (V × (D ⊕ E)) A where
  reverse := (portGraph (originalPortGraph G) H).rot
  reverse_involutive := (portGraph (originalPortGraph G) H).rot_involutive
  tail := Prod.fst
  accepts p a b := match p.2 with
    | Sum.inl d => G.accepts (p.1, d) a b
    | Sum.inr _ => true
  reverse_accepts := by
    rintro ⟨v, p⟩ a b
    rcases p with d | e
    · exact G.reverse_accepts (v, d) a b
    · rfl

@[simp] theorem constraintGraph_tail (G : ConstraintGraph V (V × D) A)
    (H : PortGraph V E) : (constraintGraph G H).tail = Prod.fst := rfl

@[simp] theorem constraintGraph_portGraph (G : ConstraintGraph V (V × D) A)
    (H : PortGraph V E) :
    originalPortGraph (constraintGraph G H) = portGraph (originalPortGraph G) H := rfl

@[simp] theorem edgeSatisfied_inl (G : ConstraintGraph V (V × D) A)
    (H : PortGraph V E) (htail : G.tail = Prod.fst)
    (labeling : V → A) (v : V) (d : D) :
    (constraintGraph G H).edgeSatisfied labeling (v, Sum.inl d) =
      G.edgeSatisfied labeling (v, d) := by
  change G.accepts (v, d) (labeling v) (labeling (G.reverse (v, d)).1) =
    G.accepts (v, d) (labeling (G.tail (v, d)))
      (labeling (G.tail (G.reverse (v, d))))
  rw [htail]

@[simp] theorem edgeSatisfied_inr (G : ConstraintGraph V (V × D) A)
    (H : PortGraph V E) (labeling : V → A) (v : V) (e : E) :
    (constraintGraph G H).edgeSatisfied labeling (v, Sum.inr e) = true := rfl

end UniqueGamesTheorem.Foundations.PCP.Overlay

end

section

/-! Lazification of the actual constraint graph. Original ports retain their
tests; the equally many stay-put ports always accept. The reverse is precisely
the existing lazy port-graph rotation used by the spectral and walk lemmas. -/
namespace UniqueGamesTheorem.Foundations.PCP.LazyConstraint

open scoped BigOperators
open PoweringWalks

variable {V D A : Type*}

def constraintGraph (G : ConstraintGraph V (V × D) A) :
    ConstraintGraph V (V × (Bool × D)) A where
  reverse := (lazyGraph (Overlay.originalPortGraph G)).rot
  reverse_involutive := (lazyGraph (Overlay.originalPortGraph G)).rot_involutive
  tail := Prod.fst
  accepts e a b := if e.2.1 then G.accepts (e.1,e.2.2) a b else true
  reverse_accepts := by
    rintro ⟨v,b,d⟩ a c
    cases b with
    | false => rfl
    | true => exact G.reverse_accepts (v,d) a c

@[simp] theorem constraintGraph_tail (G : ConstraintGraph V (V × D) A) :
    (constraintGraph G).tail = Prod.fst := rfl

@[simp] theorem constraintGraph_reverse (G : ConstraintGraph V (V × D) A) :
    (constraintGraph G).reverse = (lazyGraph (Overlay.originalPortGraph G)).rot := rfl

@[simp] theorem constraintGraph_portGraph (G : ConstraintGraph V (V × D) A) :
    Overlay.originalPortGraph (constraintGraph G) =
      lazyGraph (Overlay.originalPortGraph G) := rfl

@[simp] theorem edgeSatisfied_false (G : ConstraintGraph V (V × D) A)
    (labeling : V → A) (v : V) (d : D) :
    (constraintGraph G).edgeSatisfied labeling (v,(false,d)) = true := rfl

@[simp] theorem edgeSatisfied_true (G : ConstraintGraph V (V × D) A)
    (htail : G.tail = Prod.fst) (labeling : V → A) (v : V) (d : D) :
    (constraintGraph G).edgeSatisfied labeling (v,(true,d)) =
      G.edgeSatisfied labeling (v,d) := by
  change G.accepts (v,d) (labeling v) (labeling (G.reverse (v,d)).1) =
    G.accepts (v,d) (labeling (G.tail (v,d)))
      (labeling (G.tail (G.reverse (v,d))))
  rw [htail]

end UniqueGamesTheorem.Foundations.PCP.LazyConstraint

end

section

/-!
# Executable indexing of the actual outgoing-dart clouds

Clouds are enumerated by filtering the input table's increasing dart-index
list. Ranking searches that list, and selection reads its indexed entry.
The same functions work for empty clouds without selecting a default dart.
Padded cloud indices put all old darts first and the dummy indices afterward.
All data functions below are executable; their proofs establish the connection
to the semantic graph's actual tail fibers.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex

open scoped BigOperators
open GraphTables DegreeReplacement

/-- An explicit complete list supplies both directions of a finite encoding.
The forward direction searches the list; its inverse performs list indexing. -/
def listEquiv {α : Type*} [BEq α] [LawfulBEq α] (xs : List α)
    (nodup : xs.Nodup) (complete : ∀ a, a ∈ xs) : α ≃ Fin xs.length where
  toFun a := ⟨xs.idxOf a, List.idxOf_lt_length_of_mem (complete a)⟩
  invFun i := xs.get i
  left_inv a := List.idxOf_get _
  right_inv i := by
    apply Fin.ext
    exact List.get_idxOf nodup i

@[simp] theorem listEquiv_val {α : Type*} [BEq α] [LawfulBEq α]
    (xs : List α) (nodup : xs.Nodup) (complete : ∀ a, a ∈ xs) (a : α) :
    (listEquiv xs nodup complete a).val = xs.idxOf a := rfl

@[simp] theorem listEquiv_symm_apply {α : Type*} [BEq α] [LawfulBEq α]
    (xs : List α) (nodup : xs.Nodup) (complete : ∀ a, a ∈ xs)
    (i : Fin xs.length) : (listEquiv xs nodup complete).symm i = xs.get i := rfl

end UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex

end

section

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingLevels

def levelLoop (g k : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, e, s => (e, s)
  | fuel + 1, e, s =>
      if k ≤ s then (e, s)
      else levelLoop g k fuel (e + 1) (s * g)

/-- At most `fuel` continuing iterations can increment the exponent. -/
theorem levelLoop_level_le (g k fuel e s : Nat) :
    (levelLoop g k fuel e s).1 ≤ e + fuel := by
  induction fuel generalizing e s with
  | zero => simp only [levelLoop, Nat.add_zero, le_refl]
  | succ fuel ih =>
      simp only [levelLoop]
      split
      · omega
      · have h := ih (e + 1) (s * g)
        omega

/-- The carried size remains the exact power of the carried exponent. -/
theorem levelLoop_power (g k fuel e : Nat) :
    (levelLoop g k fuel e (g ^ e)).2 =
      g ^ (levelLoop g k fuel e (g ^ e)).1 := by
  induction fuel generalizing e with
  | zero => rfl
  | succ fuel ih =>
      simp only [levelLoop]
      split
      · rfl
      · simpa only [pow_succ] using ih (e + 1)

theorem levelLoop_covers (g k fuel e s : Nat) (hg : 1 < g)
    (hs : 0 < s) (hbudget : k ≤ s + fuel) :
    k ≤ (levelLoop g k fuel e s).2 := by
  induction fuel generalizing e s with
  | zero => simpa only [levelLoop, Nat.add_zero] using hbudget
  | succ fuel ih =>
      simp only [levelLoop]
      split
      · assumption
      · apply ih
        · exact Nat.mul_pos hs (by omega)
        · have htwo : 2 ≤ g := by omega
          have hmul : s * 2 ≤ s * g := Nat.mul_le_mul_left s htwo
          omega

/-- The search never passes an exponent whose power already covers the
request. This remains true even without a sufficient fuel budget. -/
theorem levelLoop_le_of_covering_power (g k fuel e j : Nat)
    (he : e ≤ j) (hj : k ≤ g ^ j) :
    (levelLoop g k fuel e (g ^ e)).1 ≤ j := by
  induction fuel generalizing e with
  | zero => exact he
  | succ fuel ih =>
      simp only [levelLoop]
      split
      · exact he
      · rename_i hnot
        have hne : e ≠ j := by
          intro h
          subst e
          exact hnot hj
        have hnext : e + 1 ≤ j := by omega
        simpa only [pow_succ] using ih (e + 1) hnext

def searchResult (k : Nat) : Nat × Nat :=
  levelLoop ExpanderFamily.growth k k 0 1

/-- An executable exponent, computed with at most `k` multiplications. -/
def boundedLevel (k : Nat) : Nat := (searchResult k).1

/-- The algorithm returns the power it has already computed. -/
def paddedSize (k : Nat) : Nat := (searchResult k).2

end UniqueGamesTheorem.Foundations.PCP.PreprocessingLevels

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PreprocessingOverlayTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables

open PoweringWalks

/-- Old ports precede expander ports. -/
def overlayPorts (d e : Nat) : (Fin d ⊕ Fin e) ≃ Fin (d + e) := finSumFinEquiv

@[simp] theorem overlayPorts_inl_val (d e : Nat) (i : Fin d) :
    (overlayPorts d e (Sum.inl i)).val = i.val := rfl

@[simp] theorem overlayPorts_inr_val (d e : Nat) (i : Fin e) :
    (overlayPorts d e (Sum.inr i)).val = d + i.val := rfl

/-- False/stay ports occupy rows `0,...,d-1`; true/move ports occupy
rows `d,...,2*d-1`, before the vertex offset is added. -/
def lazyPorts (d : Nat) : (Bool × Fin d) ≃ Fin (2 * d) :=
  (Equiv.prodCongr finTwoEquiv.symm (Equiv.refl (Fin d))).trans finProdFinEquiv

@[simp] theorem lazyPorts_false_val (d : Nat) (i : Fin d) :
    (lazyPorts d (false, i)).val = i.val := by
  simp [lazyPorts, finTwoEquiv, finProdFinEquiv]

@[simp] theorem lazyPorts_true_val (d : Nat) (i : Fin d) :
    (lazyPorts d (true, i)).val = i.val + d := by
  simp [lazyPorts, finTwoEquiv, finProdFinEquiv]

end UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_VertexPadding
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.VertexPadding

open scoped BigOperators

variable {V D A : Type*}

/-- Original darts use the original reversal; dummy darts stay fixed. -/
def reverseFunction (G : ConstraintGraph V (V × D) A) (extra : ℕ) :
    (V ⊕ Fin extra) × D → (V ⊕ Fin extra) × D
  | (Sum.inl v, d) => (Sum.inl (G.reverse (v, d)).1, (G.reverse (v, d)).2)
  | (Sum.inr w, d) => (Sum.inr w, d)

theorem reverseFunction_involutive (G : ConstraintGraph V (V × D) A) (extra : ℕ) :
    Function.Involutive (reverseFunction G extra) := by
  rintro ⟨v | w, d⟩
  · change (Sum.inl (G.reverse (G.reverse (v, d))).1,
      (G.reverse (G.reverse (v, d))).2) = (Sum.inl v, d)
    rw [G.reverse_involutive]
  · rfl

/-- Actual regular padding by an arbitrary finite number of dummy vertices. -/
def pad (G : ConstraintGraph V (V × D) A) (extra : ℕ) :
    ConstraintGraph (V ⊕ Fin extra) ((V ⊕ Fin extra) × D) A where
  reverse := {
    toFun := reverseFunction G extra
    invFun := reverseFunction G extra
    left_inv := reverseFunction_involutive G extra
    right_inv := reverseFunction_involutive G extra }
  reverse_involutive := reverseFunction_involutive G extra
  tail := Prod.fst
  accepts := fun e a b => match e.1 with
    | Sum.inl v => G.accepts (v, e.2) a b
    | Sum.inr _ => true
  reverse_accepts := by
    rintro ⟨v | w, d⟩ a b
    · change G.accepts (G.reverse (v, d)) b a = G.accepts (v, d) a b
      exact G.reverse_accepts (v, d) a b
    · rfl

@[simp] theorem pad_tail (G : ConstraintGraph V (V × D) A) (extra : ℕ) :
    (pad G extra).tail = Prod.fst := rfl

@[simp] theorem pad_reverse_inl (G : ConstraintGraph V (V × D) A) (extra : ℕ)
    (v : V) (d : D) :
    (pad G extra).reverse (Sum.inl v, d) =
      (Sum.inl (G.reverse (v, d)).1, (G.reverse (v, d)).2) := rfl

@[simp] theorem pad_reverse_inr (G : ConstraintGraph V (V × D) A) (extra : ℕ)
    (w : Fin extra) (d : D) :
    (pad G extra).reverse (Sum.inr w, d) = (Sum.inr w, d) := rfl

@[simp] theorem edgeSatisfied_inl (G : ConstraintGraph V (V × D) A)
    (htail : G.tail = Prod.fst) (extra : ℕ) (labeling : V ⊕ Fin extra → A)
    (v : V) (d : D) :
    (pad G extra).edgeSatisfied labeling (Sum.inl v, d) =
      G.edgeSatisfied (fun v => labeling (Sum.inl v)) (v, d) := by
  change G.accepts (v, d) (labeling (Sum.inl v))
      (labeling (Sum.inl (G.reverse (v, d)).1)) =
    G.accepts (v, d) (labeling (Sum.inl (G.tail (v, d))))
      (labeling (Sum.inl (G.tail (G.reverse (v, d)))))
  rw [htail]

@[simp] theorem edgeSatisfied_inr (G : ConstraintGraph V (V × D) A) (extra : ℕ)
    (labeling : V ⊕ Fin extra → A) (w : Fin extra) (d : D) :
    (pad G extra).edgeSatisfied labeling (Sum.inr w, d) = true := rfl

end UniqueGamesTheorem.Foundations.PCP.VertexPadding

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_Preprocessing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.Preprocessing

open PoweringWalks SpectralReturn

variable {V E A : Type*} [Fintype V] [Fintype E] [Fintype A]
  [DecidableEq V] [DecidableEq E] [DecidableEq A] [Nonempty E] [Nonempty A]

def degree : Nat := 2 * (2 * Expanders.baseDegree ^ 2 + 1)
def sizeFactor : Nat := ExpanderFamily.growth ^ 2 * degree

end UniqueGamesTheorem.Foundations.PCP.Preprocessing

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_FinalConstantsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.FinalConstants

def alphabet : Nat := 64
def compositionLoss : Nat := 12288
def denominator : Nat := 16 * alphabet ^ 4 * 66 * compositionLoss
def windowHalf : Nat := denominator * Preprocessing.sizeFactor
def smoothingScale : Nat := 4 * alphabet * windowHalf
def endpointLength : Nat := smoothingScale ^ 2

end UniqueGamesTheorem.Foundations.PCP.FinalConstants

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PreprocessingRegularTablesLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Executable degree replacement on the actual finite constraint rows

Vertices are numbered by first listing the original darts, then the dummy
darts in original-vertex order. Each local cloud uses its explicit filtered
dart list. Internal ports carry equality; the final port retains the original
constraint, or an always-accepting loop at a dummy dart. The constructor is
total, including inputs with no darts. The fixed base expander is supplied
once; every input-dependent operation is an explicit finite calculation.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables

open scoped BigOperators
open PoweringWalks DegreeReplacement

/-- Dummy coordinates, in increasing original vertex and local index order. -/
def paddingList {n : Nat} (padding : Fin n → Nat) :
    List (Σ v : Fin n, Fin (padding v)) :=
  (List.finRange n).sigma (fun v => List.finRange (padding v))

theorem paddingList_nodup {n : Nat} (padding : Fin n → Nat) :
    (paddingList padding).Nodup :=
  (List.nodup_finRange n).sigma (fun v => List.nodup_finRange (padding v))

theorem mem_paddingList {n : Nat} (padding : Fin n → Nat)
    (z : Σ v : Fin n, Fin (padding v)) : z ∈ paddingList padding := by
  rcases z with ⟨v, k⟩
  simp only [paddingList, List.mem_sigma, List.mem_finRange, and_self]

def paddingListOrder {n : Nat} (padding : Fin n → Nat) :
    (Σ v : Fin n, Fin (padding v)) ≃ Fin (paddingList padding).length :=
  PreprocessingCloudIndex.listEquiv (paddingList padding)
    (paddingList_nodup padding) (mem_paddingList padding)

theorem paddingList_length {n : Nat} (padding : Fin n → Nat) :
    (paddingList padding).length = ∑ v, padding v := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using
    (Fintype.card_congr (paddingListOrder padding)).symm

/-- Explicit list search/get indexing, with an erased cardinality cast. -/
def paddingOrder {n : Nat} (padding : Fin n → Nat) :
    (Σ v : Fin n, Fin (padding v)) ≃ Fin (∑ v, padding v) :=
  (paddingListOrder padding).trans (finCongr (paddingList_length padding))

def unitOrder : Unit ≃ Fin 1 where
  toFun _ := ⟨0, Nat.zero_lt_one⟩
  invFun _ := ()
  left_inv u := by cases u; rfl
  right_inv k := Subsingleton.elim _ _

/-- Internal cloud ports precede the one inherited-constraint port. -/
def portOrder (q : Nat) : (Fin q ⊕ Unit) ≃ Fin (q + 1) :=
  (Equiv.sumCongr (Equiv.refl _) unitOrder).trans finSumFinEquiv

def internalDegree : Nat := Expanders.baseDegree * Expanders.baseDegree

end UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables

/-!
# Exact serialized family tables at actual regularization vertices

The geometric family maps request zero to a one-vertex table. Empty clouds in
regularization instead remain empty. The bridge therefore requires positive
cloud size, derived here from each actual original or dummy vertex.
-/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PreprocessingPaddingOffsets
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

open PreprocessingRegularTables
open scoped BigOperators

theorem idxOf_map_injective {A B : Type*} [DecidableEq A] [DecidableEq B]
    (f : A → B) (hf : Function.Injective f) (xs : List A) (a : A) :
    (xs.map f).idxOf (f a) = xs.idxOf a := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : x = a
    · subst x; simp
    · simp [List.idxOf_cons_ne, h, hf.ne h, ih]

theorem sigma_idxOf {A : Type*} [DecidableEq A] (sizes : A → Nat)
    (xs : List A) (a : A) (ha : a ∈ xs) (j : Fin (sizes a)) :
    (xs.sigma (fun x => List.finRange (sizes x))).idxOf ⟨a, j⟩ =
      ((xs.take (xs.idxOf a)).map sizes).sum + j.val := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.sigma_cons]
    by_cases h : x = a
    · subst x
      have hm : (⟨a, j⟩ : Σ x, Fin (sizes x)) ∈
          (List.finRange (sizes a)).map (Sigma.mk a) := by
        exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩
      rw [List.idxOf_append_of_mem hm,
        idxOf_map_injective (Sigma.mk a) (fun x y h => by cases h; rfl),
        List.idxOf_finRange]
      simp
    · have hm : (⟨a, j⟩ : Σ x, Fin (sizes x)) ∉
          (List.finRange (sizes x)).map (Sigma.mk x) := by
        intro hm
        rcases List.mem_map.mp hm with ⟨k, _, hk⟩
        exact h (congrArg Sigma.fst hk)
      rw [List.idxOf_append_of_notMem hm, List.length_map, List.length_finRange,
        ih (List.mem_of_ne_of_mem (Ne.symm h) ha), List.idxOf_cons_ne xs h]
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      omega

def offset {n : Nat} (padding : Fin n → Nat) (k : Nat) : Nat :=
  (((List.finRange n).take k).map padding).sum

@[simp] theorem offset_zero {n : Nat} (padding : Fin n → Nat) : offset padding 0 = 0 := by
  simp [offset]

end UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingOffsets

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PreprocessingPaddingTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Executable whole-vertex padding of regular constraint tables

The first `n` vertex rows retain their old rotation and complete relation
tables. Every additional vertex has one self-reversing, always-accepting loop
at each port. An explicit finite sum equivalence identifies these stored rows
with `VertexPadding.pad`; rejection counts are preserved for every labeling.

The construction materializes finite vectors. No machine runtime bound is
claimed here.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables

open PoweringWalks PortTables

variable {n m d : Nat}

/-- Old vertices occupy the initial interval and dummy vertices the final one. -/
def vertexEquiv (h : n ≤ m) : Fin n ⊕ Fin (m - n) ≃ Fin m :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le h))

@[simp] theorem vertexEquiv_inl (h : n ≤ m) (v : Fin n) :
    vertexEquiv h (Sum.inl v) = v.castLE h := rfl

@[simp] theorem vertexEquiv_inr_val (h : n ≤ m) (v : Fin (m - n)) :
    (vertexEquiv h (Sum.inr v)).val = n + v.val := rfl

@[simp] theorem vertexEquiv_symm_old (h : n ≤ m) (v : Fin n) :
    (vertexEquiv h).symm (v.castLE h) = Sum.inl v :=
  (vertexEquiv h).symm_apply_apply (Sum.inl v)

/-- The port number is retained by the coordinate conversion. -/
def dartEquiv (h : n ≤ m) :
    (Fin n ⊕ Fin (m - n)) × Fin d ≃ Fin m × Fin d :=
  Equiv.prodCongr (vertexEquiv h) (Equiv.refl _)

@[simp] theorem dartEquiv_apply (h : n ≤ m)
    (v : Fin n ⊕ Fin (m - n)) (p : Fin d) :
    dartEquiv h (v, p) = (vertexEquiv h v, p) := rfl

end UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PreprocessingTablesLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Concrete preprocessing table algorithm

Given one fixed expander base table, this function computes regularized
cloud rows, pads the whole vertex set, overlays a stored family table, and
adds the half-lazy rows. It is total even on zero-dart input tables. The
bounds below concern actual output data; an actual TM2 execution certificate
is a separate theorem and is not inferred from these size bounds.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingTables

open PreprocessingRegularTables

def degree : Nat := 2 * ((internalDegree + 1) + internalDegree)

end UniqueGamesTheorem.Foundations.PCP.PreprocessingTables

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_FoldedEquationLemmas
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

/-- Left and right stored tables have disjoint variable names. -/
abbrev Address (i₀ : I) (j₀ : J) := HalfCube i₀ ⊕ HalfCube j₀

/-- Cancellation of the two copies of `g j₀` leaves this explicit RHS. -/
def rhsCorrection (π : J → I) (i₀ : I) (j₀ : J)
    (f : Cube I) (μ : Cube J) : Bool := f i₀ ^^ f (π j₀) ^^ μ j₀

end UniqueGamesTheorem.Foundations.Hastad.FoldedEquation

end

section

/-!
Actual equations for clause contexts having no valid local assignment. The
right answer is the constant false bit, represented by two occurrences of one
dummy variable. Those occurrences cancel for every assignment. The remaining
left answer is folded, so its uniform bias is exactly zero.
-/

namespace UniqueGamesTheorem.Foundations.Hastad

open UniqueGamesTheorem.Reduction.CloneGap
open scoped BigOperators

namespace EmptyContext

variable {I : Type}

/-- A left half-table address or the one dummy address. -/
abbrev Address (i₀ : I) := HalfCube i₀ ⊕ Unit

end EmptyContext
end UniqueGamesTheorem.Foundations.Hastad

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_FourierResponseLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Weighted question averaging and the actual finite-game consequence of the
Håstad decoder. The game value is the maximum over deterministic private answer
tables; the Fourier responses are derandomized by the checked table law. -/

noncomputable section
namespace UniqueGamesTheorem.Foundations.Hastad

open scoped BigOperators
open Finset

variable {Q₁ Q₂ I J : Type*}
  [Fintype Q₁] [DecidableEq Q₁] [Fintype Q₂] [DecidableEq Q₂]
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype J] [DecidableEq J] [Nonempty J]

/-- Storage distinguishes an actually empty legal domain from a folded table
over its legal assignments. The empty case needs no nonexistent fold point. -/
inductive ConditionedOracle (valid : J → Bool) where
  | empty (noLegal : ∀ j, valid j = false)
  | stored (j₀ : {j : J // valid j = true}) (table : HalfCube j₀ → Bool)

def ConditionedOracle.answer {valid : J → Bool} : ConditionedOracle valid → Cube J → Bool
  | .empty _ => fun _ => false
  | .stored j₀ table => conditionedFoldedAnswer valid j₀ table

end UniqueGamesTheorem.Foundations.Hastad

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_HonestTestLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceTape

open scoped BigOperators
open UniqueGamesTheorem.Reduction.FiniteNoise

/-- Two full Boolean query tables and one finite noise entry per right index. -/
abbrev TestTape (I J : Type*) (D : ℕ) :=
  Cube I × ((J → Fin D) × Cube J)

end UniqueGamesTheorem.Foundations.Hastad.SourceTape

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineTupleOdometer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineTupleOdometer

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def increment (current remaining : K) (doneLabel resetLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .peek remaining (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.pop remaining (fun state _ => (state.1, none))
        (.push current (fun _ => true) (.goto fun _ => doneLabel)))
      (.load (fun state => (state.1, none)) (.goto fun _ => resetLabel)))

section AscendingCycle

open scoped BigOperators

def cycleSteps (cost : ℕ → ℕ) (maximum count : ℕ) : ℕ :=
  (∑ r ∈ Finset.range (count + 1), cost r) + count + maximum + 2

theorem cycleSteps_zero (cost : ℕ → ℕ) (maximum : ℕ) :
    cycleSteps cost maximum 0 = (maximum + 2) + cost 0 := by
  simp [cycleSteps, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem cycleSteps_succ (cost : ℕ → ℕ) (maximum count : ℕ) :
    cycleSteps cost maximum (count + 1) =
      (cycleSteps cost maximum count + 1) + cost (count + 1) := by
  simp only [cycleSteps, Finset.sum_range_succ]
  omega

end AscendingCycle

section Order

omit [DecidableEq K]

open scoped BigOperators

def tupleOrder (n q : ℕ) : List (Fin q → Fin n) :=
  List.ofFn (finFunctionFinEquiv (m := n) (n := q)).symm

/-- Dimension zero visits the unique empty tuple once, even at radix zero. -/
theorem tupleOrder_dimension_zero (n : ℕ) :
    tupleOrder n 0 = [fun i => Fin.elim0 i] := by
  simp only [tupleOrder, pow_zero, List.ofFn_succ, List.ofFn_zero, List.cons.injEq,
    and_true]
  funext i
  exact Fin.elim0 i

theorem tupleRank_snoc {n q : ℕ} (tail : Fin q → Fin n) (d : Fin n) :
    (finFunctionFinEquiv (Fin.snoc tail d)).val =
      (finFunctionFinEquiv tail).val + d.val * n ^ q := by
  rw [finFunctionFinEquiv_apply, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  rfl

theorem tupleOrder_snoc (n q : ℕ) :
    tupleOrder n (q + 1) = (List.ofFn (fun d : Fin n => d)).flatMap
      (fun d => (tupleOrder n q).map (fun tail => Fin.snoc tail d)) := by
  change List.ofFn (fun rank : Fin (n ^ q * n) =>
    (finFunctionFinEquiv (m := n) (n := q + 1)).symm rank) = _
  rw [List.ofFn_mul']
  simp only [tupleOrder, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext d
  apply congrArg List.ofFn
  funext rank
  dsimp only [Function.comp_apply]
  apply finFunctionFinEquiv.injective
  apply Fin.ext
  erw [Equiv.apply_symm_apply, tupleRank_snoc, Equiv.apply_symm_apply]
  simp [Nat.mul_comm, Nat.add_comm]

end Order

section Nested

open scoped BigOperators

/-- Explicit caller state and tape endpoints for one level of the nested
loop. Compatibility with its child schedules is checked by their types. -/
structure CycleSchedule (K σ : Type) where
  currentSuffix : List Bool
  remainingSuffix : List Bool
  ambient : ℕ → σ
  register : ℕ → Option Bool
  base : ℕ → K → List Bool

abbrev Configuration (K Λ σ : Type) :=
  TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool)

omit [DecidableEq K] in
/-- Exact concrete-counter overhead for a complete positive-radix nesting. -/
def counterOverhead (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | q + 1 => n * (counterOverhead n q + 2)

namespace NestedCycle

variable {n : ℕ} {current remaining : ℕ → K} {bodyLabel : Λ}
  {checkLabel resetLabel : ℕ → Λ}
  {program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)}

def reverseDigit (d : Fin n) : Fin n := ⟨n - 1 - d.val, by omega⟩

end NestedCycle

omit [DecidableEq K] in
theorem counterOverhead_le (n q : ℕ) (hn : 0 < n) :
    counterOverhead n q ≤ 2 * q * n ^ q := by
  induction q with
  | zero => simp [counterOverhead]
  | succ q ih =>
    have hp : 1 ≤ n ^ q := by apply Nat.one_le_pow; exact hn
    have h := Nat.mul_le_mul_left n (Nat.add_le_add_right ih 2)
    have htwo : 2 ≤ 2 * n ^ q := Nat.mul_le_mul_left 2 hp
    have hinner : 2 * q * n ^ q + 2 ≤ 2 * (q + 1) * n ^ q := by
      rw [Nat.mul_add, Nat.add_mul]
      omega
    exact h.trans (by
      simpa only [counterOverhead, pow_succ, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm] using Nat.mul_le_mul_left n hinner)

end Nested

end UniqueGamesTheorem.Foundations.Complexity.MachineTupleOdometer

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_CanonicalBodyTemplateLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.CanonicalBodyTemplate

open Integration.BinaryLinear Foundations.Complexity CanonicalEncoding
open scoped BigOperators

variable {k : Nat}

inductive Token (k : Nat)
  | literal (value : Nat)
  | field (position : Fin k) (index : Fin 4)
  deriving DecidableEq, Repr

def evalToken (fields : Fin k → Fin 4 → Nat) : Token k → Nat
  | .literal value => value
  | .field position index => fields position index

def evalTemplate (fields : Fin k → Fin 4 → Nat) (tokens : List (Token k)) : List Nat :=
  tokens.map (evalToken fields)

def nameField (j : Fin 3) : Fin 4 := ⟨j.val, Nat.lt_trans j.isLt (by decide)⟩

def recordFields (names : Fin 3 → Nat) (occurrence : Nat) (i : Fin 4) : Nat :=
  if h : i.val < 3 then names ⟨i.val, h⟩ else occurrence

@[simp] theorem recordFields_name (names : Fin 3 → Nat) (occurrence : Nat) (j : Fin 3) :
    recordFields names occurrence (nameField j) = names j := by
  simp [recordFields, nameField, j.isLt]

@[simp] theorem recordFields_occurrence (names : Fin 3 → Nat) (occurrence : Nat) :
    recordFields names occurrence 3 = occurrence := by simp [recordFields]

def sourceFields {n m k : Nat} (occ : Fin k → Fin m) (names : Fin m → Fin 3 → Fin n)
    (j : Fin k) : Fin 4 → Nat :=
  recordFields (fun i => (names (occ j) i).val) (occ j).val

end UniqueGamesTheorem.Reduction.CanonicalBodyTemplate

end

section

/-! Lower a complete canonical-body template to the actual field-template
machine. There are four saved fields per query position, numbered by
`field + 4 * position`. The template constants depend only on finite coefficient
and RHS data; names and occurrence identifiers remain saved tape contents. -/

namespace UniqueGamesTheorem.Reduction.CanonicalBodyMachine

open Integration.BinaryLinear Foundations.Complexity CanonicalEncoding

variable {k : Nat}

def fieldEquiv (k : Nat) : (Fin k × Fin 4) ≃ Fin (4*k) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm k 4))

def fieldIndex (position : Fin k) (field : Fin 4) : Fin (4*k) :=
  fieldEquiv k (position, field)

@[simp] theorem fieldIndex_val (position : Fin k) (field : Fin 4) :
    (fieldIndex position field).val = field.val + 4 * position.val := rfl

end UniqueGamesTheorem.Reduction.CanonicalBodyMachine

end

section

/-! Exact coordinate-order bridge from the checked tuple odometer to the
outer reduction's occurrence enumeration. The odometer changes coordinate zero
fastest; `ActualEnumeration.functions` changes it slowest. Reading saved digit
`j.rev` as query coordinate `j` matches the complete ordered list. No primitive
machine or assumed whole-loop runtime is introduced here. -/

namespace UniqueGamesTheorem.Reduction.OccurrenceTupleOrder

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineTupleOdometer

variable {α : Type*}

/-- Read the physical saved digit positions in reverse coordinate order. -/
def readCoordinates {m k : Nat} (digits : Fin k → Fin m) : Fin k → Fin m :=
  digits ∘ Fin.rev

@[simp] theorem readCoordinates_apply {m k : Nat} (digits : Fin k → Fin m) (j : Fin k) :
    readCoordinates digits j = digits j.rev := rfl

@[simp] theorem readCoordinates_involutive {m k : Nat} (digits : Fin k → Fin m) :
    readCoordinates (readCoordinates digits) = digits := by
  funext j
  simp only [readCoordinates_apply, Fin.rev_rev]

theorem readCoordinates_snoc {m k : Nat} (tail : Fin k → Fin m) (d : Fin m) :
    readCoordinates (Fin.snoc tail d) = Fin.cons d (readCoordinates tail) :=
  Fin.snoc_comp_rev d tail

/-- Exact equality of occurrence lists after reading saved digits in reverse
coordinate order. This includes dimension zero and radix zero. -/
theorem tupleOrder_readCoordinates (m k : Nat) :
    (MachineTupleOdometer.tupleOrder m k).map readCoordinates =
      ActualEnumeration.functions (List.finRange m) k := by
  induction k with
  | zero =>
    rw [MachineTupleOdometer.tupleOrder_dimension_zero]
    change [readCoordinates (fun i : Fin 0 => Fin.elim0 i)] = [Fin.elim0]
    congr 1
  | succ k ih =>
    have each (d : Fin m) :
        ((MachineTupleOdometer.tupleOrder m k).map (fun tail => Fin.snoc tail d)).map
          readCoordinates =
        (ActualEnumeration.functions (List.finRange m) k).map (Fin.cons d) := by
      calc
        _ = ((MachineTupleOdometer.tupleOrder m k).map readCoordinates).map (Fin.cons d) := by
          simp only [List.map_map, Function.comp_def, readCoordinates_snoc]
        _ = _ := by rw [ih]
    rw [MachineTupleOdometer.tupleOrder_snoc]
    change ((List.finRange m).flatMap (fun d =>
      (MachineTupleOdometer.tupleOrder m k).map (fun tail => Fin.snoc tail d))).map
      readCoordinates = _
    simp only [List.map_flatMap, each]
    simp only [ActualEnumeration.functions, Explicit.pairs, List.map_flatMap,
      List.map_map, Function.comp_def]

/-- An arbitrary exact emitted list, including serialized edge bytes, inherits
the order identity. There is no permutation or counting-only replacement. -/
theorem functions_flatMap (m k : Nat) (emit : (Fin k → Fin m) → List α) :
    (ActualEnumeration.functions (List.finRange m) k).flatMap emit =
      (MachineTupleOdometer.tupleOrder m k).flatMap
        (fun digits => emit (readCoordinates digits)) := by
  rw [← tupleOrder_readCoordinates]
  exact List.flatMap_map readCoordinates emit _

end UniqueGamesTheorem.Reduction.OccurrenceTupleOrder

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceOccurrences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Executable radix numbering of padded global long-code tables and an ordered
equation occurrence list. The code enumerates random tapes, not distinct
equations: coinciding equations and repeated variable occurrences are retained.
-/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences

open UniqueGamesTheorem.Reduction.CloneGap
open scoped BigOperators

/-- A concrete, reversible finite encoding. Constructors below specify the
actual arithmetic; no arbitrary `Fintype.equivFin` is used. -/
structure Encoding (α : Type) where
  size : ℕ
  code : α ≃ Fin size

namespace Encoding

def fin (n : ℕ) : Encoding (Fin n) := ⟨n, Equiv.refl _⟩
def bool : Encoding Bool := ⟨2, finTwoEquiv.symm⟩
def unit : Encoding Unit := ⟨1, finOneEquiv.symm⟩

/-- The second component is the low-order block coordinate. -/
def prod {α β : Type} (a : Encoding α) (b : Encoding β) : Encoding (α × β) :=
  ⟨a.size * b.size, (Equiv.prodCongr a.code b.code).trans finProdFinEquiv⟩

/-- The right summand follows the whole left block. -/
def sum {α β : Type} (a : Encoding α) (b : Encoding β) : Encoding (α ⊕ β) :=
  ⟨a.size + b.size, (Equiv.sumCongr a.code b.code).trans finSumFinEquiv⟩

/-- Function coordinate zero is the least significant radix digit. -/
def function {α β : Type} (a : Encoding α) (b : Encoding β) : Encoding (α → β) where
  size := b.size ^ a.size
  code := (show (α → β) ≃ (Fin a.size → Fin b.size) from
    { toFun := fun f i => b.code (f (a.code.symm i))
      invFun := fun f x => b.code.symm (f (a.code x))
      left_inv := by intro f; funext x; simp
      right_inv := by intro f; funext i; simp }).trans finFunctionFinEquiv

def enumerate {α : Type} (a : Encoding α) : List α := List.ofFn a.code.symm

@[simp] theorem length_enumerate {α : Type} (a : Encoding α) :
    a.enumerate.length = a.size := by simp [enumerate]

theorem mem_enumerate {α : Type} (a : Encoding α) (x : α) : x ∈ a.enumerate := by
  rw [enumerate, List.mem_ofFn']
  exact ⟨a.code x, a.code.symm_apply_apply x⟩

end Encoding

/-- A terminating first-valid search on the explicitly ordered ambient list. -/
def findValid {J : Type} (valid : J → Bool) : List J → Option {j : J // valid j = true}
  | [] => none
  | j :: rest => if h : valid j = true then some ⟨j, h⟩ else findValid valid rest

section ConcreteSource

open SourceContexts
open UniqueGamesTheorem.Reduction.FiniteNoise

def leftAnchor (u : ℕ) : I u := fun _ => false

end ConcreteSource

end UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences

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

namespace UniqueGamesTheorem.Foundations.Hastad.SourceAddressDescriptors

open Target SourceContexts SourceOccurrences
open UniqueGamesTheorem.Reduction.CloneGap

abbrev Descriptor := Fin 3 × ℕ

def realize (base : Fin 3 → ℕ) (d : Descriptor) : ℕ := d.2 + base d.1

end UniqueGamesTheorem.Foundations.Hastad.SourceAddressDescriptors

/-! Actual fixed-coefficient affine address construction. A finite literal phase
loads the coefficient, the checked width-two Horner machine reads coefficient
and preserved offset with the rank as its radix, then the literal field is
actually consumed. All operands and work stacks are restored. -/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceFieldArrayLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceFieldArray

open Turing
open UniqueGamesTheorem.Foundations.Complexity SourceMachine

variable {K Λ σ : Type} [DecidableEq K]

/-- Extend finite indices harmlessly outside the range used by the machine. -/
def boundedIndex (q j : Nat) : Fin (q + 1) := ⟨min j q, by omega⟩

@[simp] theorem boundedIndex_val {q j : Nat} (hj : j ≤ q) :
    (boundedIndex q j).val = j := Nat.min_eq_left hj

def startLabel (q j : Nat) : Fin (q + 1) × Bool := (boundedIndex q j, false)
def loopLabel (q j : Nat) : Fin (q + 1) × Bool := (boundedIndex q j, true)

end UniqueGamesTheorem.Foundations.Hastad.SourceFieldArray

namespace UniqueGamesTheorem.Foundations.Hastad.SourceClauseLookup

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open SourceMachine

inductive Tape
  | formula | index | work | scratch | field (slot : Fin 6)
  deriving DecidableEq, Fintype

end UniqueGamesTheorem.Foundations.Hastad.SourceClauseLookup

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceContextLoad
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

inductive Tape (u : Nat) (Extra : Type)
  | formula | index | work | scratch | copyScratch
  | current (coordinate : Fin u) | remaining (coordinate : Fin u)
  | field (coordinate : Fin u) (slot : Fin 6)
  | extra (value : Extra)
  deriving DecidableEq, Fintype

variable {u : Nat} {Extra : Type}

variable [DecidableEq Extra]

def variableSlot (s : Fin 3) : Fin 6 := ⟨2 * s.val, by omega⟩

end UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceLoopInitLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceLoopInit

open Turing UniqueGamesTheorem.Foundations.Complexity
open SourceMachine

inductive HeaderTape
  | variableCount | clauseCount
  deriving DecidableEq

end UniqueGamesTheorem.Foundations.Hastad.SourceLoopInit

namespace UniqueGamesTheorem.Foundations.Hastad.SourceRuntimeFinish

open Turing Complexity

variable {K Λ σ : Type} [DecidableEq K]

abbrev Label (clearKeys : List K) := MachineDrainMany.Label clearKeys ⊕ Bool
abbrev Tapes (K : Type) := K → List Bool

def entry (clearKeys : List K) (labels : Label clearKeys → Λ) : Option Λ :=
  MachineDrainMany.entry clearKeys (fun l => labels (.inl l)) (some (labels (.inr false)))

def canonicalTapes (output : K) (word : List Bool) : Tapes K :=
  Function.update (fun _ => []) output word

def finishCost (clearKeys : List K) (accumulator : K) (base : Tapes K) : Nat :=
  MachineDrainMany.steps clearKeys base + (base accumulator).length + 2

variable [Fintype K]
open scoped BigOperators

def totalLength (base : Tapes K) : Nat := ∑ k, (base k).length

theorem totalLength_erase (base : Tapes K) (source : K) :
    totalLength (Function.update base source []) + (base source).length = totalLength base := by
  calc
    _ = ∑ k, (((Function.update base source []) k).length +
        if k = source then (base source).length else 0) := by
      simp [totalLength, Finset.sum_add_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases h : k = source
      · subst k
        simp
      · simp [h]

/-- Each physical pop removes one stored symbol; repeated clear keys add only
the extra empty-tape loop test after their first occurrence. -/
theorem drain_conservation (clearKeys : List K) (base : Tapes K) :
    MachineDrainMany.steps clearKeys base +
      totalLength (MachineDrainMany.finalTapes clearKeys base) =
        totalLength base + clearKeys.length := by
  induction clearKeys generalizing base with
  | nil => simp [MachineDrainMany.steps, MachineDrainMany.finalTapes]
  | cons source rest ih =>
      have h := ih (Function.update base source [])
      have erase := totalLength_erase base source
      simp only [MachineDrainMany.steps, MachineDrainMany.finalTapes, List.length_cons]
      omega

end UniqueGamesTheorem.Foundations.Hastad.SourceRuntimeFinish

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceSignaturePrepareLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceContextPrepare

open Turing UniqueGamesTheorem.Foundations.Complexity
open Target PCP SourceContexts SourceOccurrences

abbrev LoadState := Unit × Option Bool

end UniqueGamesTheorem.Foundations.Hastad.SourceContextPrepare

/-! The actual numbered equation list has exactly the acceptance bounded by
the private Fourier decoder. Only the repeated base-game value is an input
here; list semantics and all finite sampling laws are supplied. -/

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

namespace UniqueGamesTheorem.Foundations.Hastad.SourceOdometerSchedule

open Turing Complexity MachineTupleOdometer

variable {u m : ℕ} {Extra Λ σ : Type} [DecidableEq Extra]

def allBits {q : ℕ} (bits : (Fin q → Fin m) → List Bool) : List Bool :=
  (tupleOrder m q).flatMap bits

def blocks {q : ℕ} (bits : (Fin (q + 1) → Fin m) → List Bool) (d : ℕ) : List Bool :=
  if h : d < m then allBits (fun c => bits (Fin.snoc c ⟨d, h⟩)) else []

end UniqueGamesTheorem.Foundations.Hastad.SourceOdometerSchedule

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceHeaderAccumulate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate

open Turing UniqueGamesTheorem.Foundations.Complexity

structure Layout (K : Type) where
  bits : K
  count : K
  accumulator : K
  bits_count : bits ≠ count
  bits_accumulator : bits ≠ accumulator
  count_accumulator : count ≠ accumulator

end UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate

end

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

def leftValue (u n : Nat) : Nat := 2 ^ (2 ^ u) * n ^ u
def rightValue (u m : Nat) : Nat := 2 ^ (8 ^ u) * m ^ u
def dummyValue (u n m : Nat) : Nat := leftValue u n + rightValue u m
def bitValue (u n m : Nat) : Nat := dummyValue u n m + 1

inductive Kind
  | left | right | occurrences
  deriving DecidableEq

inductive Control
  | variableCount | clauseCount | leftBlockSize | rightTemporary | dummyIndex
  | bitCount | occurrenceCount | accA | accB | counter | scratch
  deriving DecidableEq

end

end UniqueGamesTheorem.Foundations.Hastad.SourceHeaderCounts

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceQueryOrderLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace UniqueGamesTheorem.Foundations.Hastad.SourceRuntimeModel

open Turing Complexity SourceContexts SourceOccurrences


inductive BodyWork (Extra : Type)
  | leftBlock | dummy | bitCount | occurrenceCount
  | zero | rank | rightBase | leftBase
  | accA | accB | counter | arithScratch | coefficient
  | queryTemporary | queryScratch | accumulator
  | extra (value : Extra)
  deriving DecidableEq, Fintype

abbrev ArithmeticState := MachineHorner.State Unit

end UniqueGamesTheorem.Foundations.Hastad.SourceRuntimeModel



namespace UniqueGamesTheorem.Foundations.Hastad.SourceTupleTape

open Turing Complexity SourceContexts SourceRuntimeModel


structure Snapshot where
  rank : List Bool := []
  rightBase : List Bool := []
  leftBase : List Bool := []
  zero : List Bool := []
  emitted : List Bool := []
  deriving DecidableEq, Inhabited

end UniqueGamesTheorem.Foundations.Hastad.SourceTupleTape

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceRuntimeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Intermediate tape-space bounds derived from actual successful machine
prefixes, and their use in the separately checked physical finalizer. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceRuntimeSpace

open Turing Complexity
open scoped BigOperators

attribute [local instance] FinTM2.kFin

/-- All stacks are counted, even when their symbol types differ. -/
def configurationLength (tm : FinTM2) (cfg : tm.Cfg) : Nat :=
  ∑ k : tm.K, (cfg.stk k).length

theorem initial_configurationLength (tm : FinTM2) (input : List (tm.Γ tm.k₀)) :
    configurationLength tm (initList tm input) = input.length := by
  have point (k : tm.K) : ((initList tm input).stk k).length =
      if k = tm.k₀ then input.length else 0 := by
    by_cases h : k = tm.k₀
    · subst k
      simp [initList]
    · simp [initList, h]
  simp [configurationLength, point]

/-- This equality only identifies the actual endpoint stacks with a Boolean
finalizer's stacks. It makes no execution or time assumption. -/
theorem totalLength_eq_configurationLength (tm : FinTM2) (finish : tm.Cfg)
    (base : tm.K → List Bool)
    (sameLengths : ∀ k, (base k).length = (finish.stk k).length) :
    SourceRuntimeFinish.totalLength base = configurationLength tm finish := by
  exact Finset.sum_congr rfl (fun k _ => sameLengths k)

end UniqueGamesTheorem.Foundations.Hastad.SourceRuntimeSpace

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_FinalTableFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The exact table-to-formula converter used by the final CNF machine.
Its semantic count premise is explicit; amplification supplies that premise
elsewhere. The converter chooses no vertex or dart numbering. -/

namespace UniqueGamesTheorem.Foundations.PCP.FinalTableFormula

open Target Complexity

/-- A fixed quadratic in the full serialized input length. -/
noncomputable def sizePolynomial : Polynomial Nat :=
  Polynomial.C 77824 * Polynomial.X + Polynomial.C 2 +
    (Polynomial.C 40960 * Polynomial.X) *
      (Polynomial.C 3 * (Polynomial.C 36864 * Polynomial.X + Polynomial.C 2))

theorem sizePolynomial_eval (N : Nat) :
    sizePolynomial.eval N = 77824 * N + 2 + (40960 * N) * (3 * (36864 * N + 2)) := by
  simp [sizePolynomial]

end UniqueGamesTheorem.Foundations.PCP.FinalTableFormula

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_FinalCNFOutputLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
The final machine's complete output stream is the exact serialization of its
actual formula. This identity includes the two size fields, every clause and
literal field, and all unary delimiters. No desired output equality is assumed.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

open PCP

noncomputable def rowTimePolynomial : Polynomial Nat :=
  Polynomial.C 860160 * (Polynomial.C 3 * (Polynomial.X + Polynomial.C 1) + Polynomial.C 3) +
    Polynomial.C 12 * Polynomial.X + Polynomial.C 15

/-!
The complete polynomial-time machine certificate for converting a validated
64-label graph table into its actual 3CNF formula. The proof composes the real
input parser, all row executions, output reversal, and private-tape cleanup.
-/

open Turing


end UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineAppendAt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.MachineAppendAt

open Turing

variable {K Λ σ β : Type} [DecidableEq K]

abbrev Alphabet (β : Type) (_ : K) := β

end UniqueGamesTheorem.Foundations.Complexity.MachineAppendAt

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineCanonicalOutputLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Canonical output for finite Boolean machines

A raw machine may halt with retained metadata and a changed finite state.
This wrapper redirects its halt to a fixed list of actual tape drains, then
executes one state-reset instruction. The output tape is preserved and the
result is literally `haltList`. Its cost follows from the raw execution and
the maximum number of pushes in a raw statement.

The cleanup list is fixed with the program, not selected from the input.
It may contain repetitions and may be empty when output is the only tape.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCanonicalOutput

open Turing

/-- The homogeneous parts of a finite machine, without dependent alphabet casts. -/
structure Program (K Λ σ : Type) where
  input : K
  output : K
  main : Λ
  initial : σ
  code : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ

section Structural

variable {K Λ Λ' σ : Type} [DecidableEq K]

def extendedLabel (labels : Λ → Λ') (haltTarget : Option Λ') : Option Λ → Option Λ'
  | none => haltTarget
  | some label => some (labels label)

def extendedCfg (labels : Λ → Λ') (haltTarget : Option Λ') (register : Option Bool)
    (cfg : TM2.Cfg (fun _ : K => Bool) Λ σ) :
    TM2.Cfg (fun _ : K => Bool) Λ' (σ × Option Bool) :=
  ⟨extendedLabel labels haltTarget cfg.l, (cfg.var, register), cfg.stk⟩

/-- Add one finite scratch register while preserving each raw transition. -/
def extendedStmt (labels : Λ → Λ') (haltTarget : Option Λ') :
    TM2.Stmt (fun _ : K => Bool) Λ σ →
      TM2.Stmt (fun _ : K => Bool) Λ' (σ × Option Bool)
  | .push k f next => .push k (fun state => f state.1)
      (extendedStmt labels haltTarget next)
  | .peek k f next => .peek k (fun state symbol => (f state.1 symbol, state.2))
      (extendedStmt labels haltTarget next)
  | .pop k f next => .pop k (fun state symbol => (f state.1 symbol, state.2))
      (extendedStmt labels haltTarget next)
  | .load f next => .load (fun state => (f state.1, state.2))
      (extendedStmt labels haltTarget next)
  | .branch test yes no => .branch (fun state => test state.1)
      (extendedStmt labels haltTarget yes) (extendedStmt labels haltTarget no)
  | .goto label => .goto (fun state => labels (label state.1))
  | .halt => match haltTarget with
    | none => .halt
    | some label => .goto (fun _ => label)

theorem stepAux_extended (labels : Λ → Λ') (haltTarget : Option Λ')
    (stmt : TM2.Stmt (fun _ : K => Bool) Λ σ) (state : σ)
    (register : Option Bool) (tapes : K → List Bool) :
    TM2.stepAux (extendedStmt labels haltTarget stmt) (state, register) tapes =
      extendedCfg labels haltTarget register (TM2.stepAux stmt state tapes) := by
  induction stmt generalizing state tapes with
  | push k f next ih => exact ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih => exact ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
      exact ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih => exact ih (f state) tapes
  | branch test yes no ihYes ihNo =>
      cases h : test state with
      | false =>
          simpa only [extendedStmt, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
      | true =>
          simpa only [extendedStmt, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto label => rfl
  | halt => cases haltTarget <;> rfl

end Structural

variable {K Λ σ : Type} [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype σ]

def sourceMachine (P : Program K Λ σ) : FinTM2 where
  K := K
  k₀ := P.input
  k₁ := P.output
  Γ _ := Bool
  Λ := Λ
  main := P.main
  σ := σ
  initialState := P.initial
  m := P.code

abbrev Label (Λ : Type) (chosen : List K) := Λ ⊕ (MachineDrainMany.Label chosen ⊕ Unit)

def cleanupLabel (chosen : List K) : MachineDrainMany.Label chosen → Label Λ chosen :=
  fun label => .inr (.inl label)

def resetLabel (chosen : List K) : Label Λ chosen := .inr (.inr ())

def cleanupEntry (chosen : List K) : Option (Label Λ chosen) :=
  MachineDrainMany.entry chosen (cleanupLabel chosen) (some (resetLabel chosen))

end UniqueGamesTheorem.Foundations.Complexity.MachineCanonicalOutput

namespace UniqueGamesTheorem.Foundations.Complexity.MachineTableRows

open Turing
open PCP.GraphTables

inductive Label
  | relationRead | relationRestore | reverseRead | reverseRestore
  | tailRead | tailRestore | appendOld | appendRow | appendBack
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.relationRead, .relationRestore, .reverseRead,
  .reverseRestore, .tailRead, .tailRestore, .appendOld, .appendRow, .appendBack]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

/-- Exact row field concatenation at the level of stored bits. -/
def fieldBits (fields : Fin 3 → K) (base : K → List Bool) : List Bool :=
  base (fields 0) ++ base (fields 1) ++ base (fields 2)

def fieldSize (fields : Fin 3 → K) (base : K → List Bool) : Nat :=
  (base (fields 0)).length + (base (fields 1)).length + (base (fields 2)).length

end UniqueGamesTheorem.Foundations.Complexity.MachineTableRows

/-!
Actual finite control for the dummy self-loop rows of one padded vertex.
The port count is a fixed program parameter. Vertex and reverse-dart indices
remain on unary tapes, and each row advances the reverse index by one actual
push. The all-true relation is a fixed literal field, initialized once.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineDummyRows

open Turing
open PCP.GraphTables

/-- The actual 64-by-64 always-accepting relation. -/
def trueRelation : RelationTable := Vector.replicate 4096 true

/-- One initialization label and ten labels per fixed port. -/
abbrev Label (d : Nat) := Unit ⊕ (Fin d × (MachineTableRows.Label ⊕ Unit))

def start (d : Nat) : Label d := .inl ()
def rowLabel {d : Nat} (p : Fin d) (stage : MachineTableRows.Label) : Label d :=
  .inr (p, .inl stage)
def bumpLabel {d : Nat} (p : Fin d) : Label d := .inr (p, .inr ())

def fields : Fin 3 → Fin 6 := fun i => i.castLE (by decide)

/-- The only data-changing index operation is a tape push, below. This
function chooses a finite continuation among the fixed port-control labels. -/
def afterPort {d : Nat} (p : Fin d) : Option (Label d) :=
  if h : p.val + 1 < d then some (rowLabel ⟨p.val + 1, h⟩ .relationRead) else none

def entry (d : Nat) : Option (Label d) :=
  if h : 0 < d then some (rowLabel ⟨0, h⟩ .relationRead) else none

variable {σ : Type}

abbrev Alphabet (_ : Fin 6) := Bool

def continueAt {d : Nat} (exit : Option (Label d)) :
    TM2.Stmt Alphabet (Label d) (σ × Option Bool) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

theorem stepAux_continueAt {d : Nat} (exit : Option (Label d))
    (state : σ × Option Bool) (tapes : Fin 6 → List Bool) :
    TM2.stepAux (continueAt exit) state tapes = ⟨exit, state, tapes⟩ := by
  cases exit <;> rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineDummyRows

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineCeilingPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCeilingPower

open Turing
open UniqueGamesTheorem.Foundations.PCP

inductive Tape
  | input | work | power | saved | level | fuel | spare | product
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .work, .power, .saved, .level, .fuel,
  .spare, .product]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Label
  | init | fuelFirst | fuelSecond | guard | copyFirst | copySecond
  | compare | restore | decide | scale | transfer | cleanup
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.init, .fuelFirst, .fuelSecond, .guard,
  .copyFirst, .copySecond, .compare, .restore, .decide, .scale, .transfer, .cleanup]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Alphabet (_ : Tape) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

def memory (input work power saved level fuel spare product : List Bool) : Tape → List Bool
  | .input => input
  | .work => work
  | .power => power
  | .saved => saved
  | .level => level
  | .fuel => fuel
  | .spare => spare
  | .product => product

@[simp] theorem update_work (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .work x = memory a x c d e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_power (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .power x = memory a b x d e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_saved (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .saved x = memory a b c x e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_level (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .level x = memory a b c d x f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_fuel (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .fuel x = memory a b c d e x g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_product (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .product x = memory a b c d e f g x := by
  funext k; cases k <;> rfl

variable {σ : Type}

def compareLoop : TM2.Stmt Alphabet Label (State σ) :=
  .pop .work (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.peek .power (fun state head => (state.1, head))
        (.branch (fun state => state.2.getD false)
          (.pop .power (fun state _ => (state.1, none))
            (.push .saved (fun _ => true) (.goto fun _ => .compare)))
          (.load (fun state => ((state.1.1, true), none)) (.goto fun _ => .compare))))
      (.load (fun state => (state.1, none)) (.goto fun _ => .restore)))

def overflow (flag : Bool) (x p : Nat) : Bool := flag || decide (p < x)

theorem appendTrace {α : Type*} (f : α → α) {a b c : α} {s t : Nat}
    (hs : f^[s] a = b) (ht : f^[t] b = c) : f^[s + t] a = c := by
  rw [Nat.add_comm s t, Function.iterate_add_apply, hs, ht]

def prefixTime (k p : Nat) : Nat := (1 + 2 * (k + 2)) + (k + min k p + 2) + 1

def coreTime (g k : Nat) : Nat → Nat → Nat
  | 0, _ => 3
  | f + 1, p => prefixTime k p +
      if k ≤ p then f + 2 else (p + g * p + 2) + coreTime g k f (p * g)

def roundBudget (g k : Nat) : Nat := (g + 8) * (k + 1) + 16

theorem prefixTime_le (k p : Nat) : prefixTime k p ≤ 4 * k + 8 := by
  have h := Nat.min_le_left k p
  unfold prefixTime
  omega

theorem prefixTime_le_roundBudget (g k p : Nat) : prefixTime k p ≤ roundBudget g k := by
  have h := prefixTime_le k p
  unfold roundBudget
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

theorem continuingTime_le (g k p : Nat) (h : p < k) :
    prefixTime k p + (p + g * p + 2) ≤ roundBudget g k := by
  have hprefix := prefixTime_le k p
  have hmul := Nat.mul_le_mul_left g h.le
  unfold roundBudget
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

def totalTime (g k : Nat) : Nat := 1 + 2 * (k + 2) + coreTime g k k 1

def timeBound (g k : Nat) : Nat := (g + 8) * (k + 1) ^ 2 + 18 * (k + 1) + 3

/-- The bound is one fixed quadratic polynomial in the actual unary input
length. Its coefficient may depend on the fixed growth factor. -/
noncomputable def timePolynomial (g : Nat) : Polynomial Nat :=
  Polynomial.C (g + 8) * Polynomial.X ^ 2 + 18 * Polynomial.X + 3

end UniqueGamesTheorem.Foundations.Complexity.MachineCeilingPower

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineClone100TableLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Model

open UniqueGamesTheorem.Reduction

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad

inductive Tape
  | input | header | counter | field (slot : Fin 4) | scratch | reversed | output
  deriving DecidableEq, Fintype

abbrev Context (D : Nat) := Fin 2 ⊕ (Fin D × Fin 4)
abbrev State (D : Nat) := (Unit × Context D) × Option Bool
abbrev Alphabet (_ : Tape) := Bool

inductive Label (D : Nat)
  | headerStart (slot : Fin 2)
  | headerLoop (slot : Fin 2)
  | setup (context : Context D)
  | scan (context : Context D)
  | emit (context control : Context D) (symbol : Bool)
  | restore (context : Context D)
  | clearHeader
  | guard
  | fieldStart (slot : Fin 4)
  | fieldLoop (slot : Fin 4)
  | cleanup (slot : Fin 4)
  | finalCounter
  | finalReverse
  deriving DecidableEq, Fintype

def defaultControl (D : Nat) : Context D := .inl 0
def initialState (D : Nat) : State D := (((), defaultControl D), none)

def headerTape (j : Fin 2) : Tape := if j.val = 0 then .header else .counter

def contextSource {D : Nat} : Context D → Tape
  | .inl j => headerTape j
  | .inr p => .field p.2

def contextScale {D : Nat} : Context D → Nat
  | .inl j => if j.val = 0 then 100 else D
  | .inr p => if p.2.val < 3 then 100 else 1

def tripleField (t : Nat × Nat × Nat) (j : Fin 4) : Nat :=
  match j.val with
  | 0 => t.1
  | 1 => t.2.1
  | 2 => t.2.2
  | _ => 0

def contextOffset (triples : List (Nat × Nat × Nat)) : Context triples.length → Nat
  | .inl _ => 0
  | .inr p => tripleField (triples.get p.1) p.2

def contextNext {D : Nat} : Context D → Option (Label D)
  | .inl j => if j.val = 0 then some (.setup (.inl 1)) else some .clearHeader
  | .inr (i, j) =>
      if hj : j.val + 1 < 4 then some (.setup (.inr (i, ⟨j.val + 1, hj⟩)))
      else if hi : i.val + 1 < D then some (.setup (.inr (⟨i.val + 1, hi⟩, 0)))
      else some (.cleanup 0)

def cleanupNext {D : Nat} (j : Fin 4) : Label D :=
  if hj : j.val + 1 < 4 then .cleanup ⟨j.val + 1, hj⟩ else .guard

def drain {D : Nat} (tape : Tape) (again next : Label D) :
    TM2.Stmt Alphabet (Label D) (State D) :=
  .pop tape (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.goto fun _ => again)
      (.load (fun state => (state.1, none)) (.goto fun _ => next)))

end UniqueGamesTheorem.Explicit.MachineClone100Model

end

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Affine

open UniqueGamesTheorem.Reduction

open UniqueGamesTheorem.Foundations.Complexity
open MachineClone100Model

/-- Identity control transitions reduce exactly to fixed symbol substitution. -/
theorem output_eq_flatMap {Q : Type} [Fintype Q]
    (emit : Q → Bool → List Bool) (q : Q) (input : List Bool) :
    MachineTransducer.output (fun state _ => state) emit q input =
      input.flatMap (emit q) := by
  induction input with
  | nil => rfl
  | cons b input ih =>
    simp only [MachineTransducer.output, List.flatMap_cons, ih]

end UniqueGamesTheorem.Explicit.MachineClone100Affine

end

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Cleanup

open UniqueGamesTheorem.Reduction

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineClone100Model

variable {D : Nat}

/-- The finite drain statement pops one symbol and retains the ambient control. -/
theorem drainStep_cons (tape : Tape) (again next : Label D)
    (program : Label D → TM2.Stmt Alphabet (Label D) (State D))
    (atAgain : program again = drain tape again next)
    (base : Tape → List Bool) (bit : Bool) (input : List Bool)
    (control : Unit × Context D) (register : Option Bool) :
    TM2.step program
      ⟨some again, (control, register), Function.update base tape (bit :: input)⟩ =
      some ⟨some again, (control, some bit), Function.update base tape input⟩ := by
  change some (TM2.stepAux (program again) (control, register)
    (Function.update base tape (bit :: input))) = _
  rw [atAgain]
  simp [drain, TM2.stepAux]

/-- The exit transition observes the empty tape and resets the optional bit. -/
theorem drainStep_nil (tape : Tape) (again next : Label D)
    (program : Label D → TM2.Stmt Alphabet (Label D) (State D))
    (atAgain : program again = drain tape again next)
    (base : Tape → List Bool) (control : Unit × Context D) (register : Option Bool) :
    TM2.step program
      ⟨some again, (control, register), Function.update base tape []⟩ =
      some ⟨some next, (control, none), Function.update base tape []⟩ := by
  change some (TM2.stepAux (program again) (control, register)
    (Function.update base tape [])) = _
  rw [atAgain]
  simp [drain, TM2.stepAux]

/-- The four explicit updates made by the successive cleanup labels. -/
def clearFields (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (Function.update (Function.update (Function.update base
    (.field 0) []) (.field 1) []) (.field 2) []) (.field 3) []

@[simp] theorem clearFields_field (base : Tape → List Bool) (j : Fin 4) :
    clearFields base (.field j) = [] := by
  fin_cases j <;> simp [clearFields]

@[simp] theorem clearFields_input (base : Tape → List Bool) :
    clearFields base .input = base .input := by simp [clearFields]
@[simp] theorem clearFields_header (base : Tape → List Bool) :
    clearFields base .header = base .header := by simp [clearFields]
@[simp] theorem clearFields_counter (base : Tape → List Bool) :
    clearFields base .counter = base .counter := by simp [clearFields]
@[simp] theorem clearFields_scratch (base : Tape → List Bool) :
    clearFields base .scratch = base .scratch := by simp [clearFields]
@[simp] theorem clearFields_reversed (base : Tape → List Bool) :
    clearFields base .reversed = base .reversed := by simp [clearFields]
@[simp] theorem clearFields_output (base : Tape → List Bool) :
    clearFields base .output = base .output := by simp [clearFields]

def cleanupSteps (base : Tape → List Bool) : Nat :=
  (base (.field 0)).length + (base (.field 1)).length +
    (base (.field 2)).length + (base (.field 3)).length + 4

end UniqueGamesTheorem.Explicit.MachineClone100Cleanup

end

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Context

open UniqueGamesTheorem.Reduction

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineClone100Model

theorem contextSource_ne_scratch {D : Nat} (context : Context D) :
    contextSource context ≠ Tape.scratch := by
  cases context with
  | inl slot =>
    simp only [contextSource, headerTape]
    split <;> simp
  | inr pair => simp [contextSource]

theorem contextSource_ne_reversed {D : Nat} (context : Context D) :
    contextSource context ≠ Tape.reversed := by
  cases context with
  | inl slot =>
    simp only [contextSource, headerTape]
    split <;> simp
  | inr pair => simp [contextSource]

end UniqueGamesTheorem.Explicit.MachineClone100Context

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineClone100Triples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Triples

open UniqueGamesTheorem.Reduction

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineClone100Model MachineClone100Context MachineClone100Affine

theorem chain {α : Type*} {f : α → α} {x y z : α} {m n : Nat}
    (first : f^[m] x = y) (second : f^[n] y = z) : f^[n + m] x = z := by
  rw [Function.iterate_add_apply, first, second]

def affineRecord (a b c rhs : Nat) (t : Nat × Nat × Nat) : List Nat :=
  [t.1 + 100 * a, t.2.1 + 100 * b, t.2.2 + 100 * c, rhs]

end UniqueGamesTheorem.Explicit.MachineClone100Triples

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineClone100Loop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Loop

open UniqueGamesTheorem.Reduction

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad
open MachineClone100Model

structure Record where
  a : Nat
  b : Nat
  c : Nat
  rhs : Nat

def recordWords (r : Record) : List Nat := [r.a, r.b, r.c, r.rhs]

end UniqueGamesTheorem.Explicit.MachineClone100Loop

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineClone100Certified
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Certified

open UniqueGamesTheorem.Reduction

open Turing
open UniqueGamesTheorem.Foundations.Complexity

noncomputable def timePolynomial (copies : Nat) : Polynomial Nat :=
  Polynomial.C (300 * copies) * Polynomial.X * Polynomial.X +
    Polynomial.C (120 + 18 * copies) * Polynomial.X + Polynomial.C 23

theorem timePolynomial_eval (copies length : Nat) :
    (timePolynomial copies).eval length =
      (300 * copies) * length * length + (120 + 18 * copies) * length + 23 := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]

theorem numericalBudget (D N n m B out : Nat)
    (hn : n ≤ N) (hm : m ≤ N) (hB : B ≤ N)
    (ho : out ≤ (300 * D) * N * N + (100 + 3 * D) * N + 2) :
    (out + 2) + (((2 + 3 * D) * B + (9 + 12 * D) * m + 1) +
      (5 * n + 4 * m + 18)) ≤ (300 * D) * N * N + (120 + 18 * D) * N + 23 := by
  have hn' := Nat.mul_le_mul_left 5 hn
  have hm' := Nat.mul_le_mul_left (13 + 12 * D) hm
  have hb' := Nat.mul_le_mul_left (2 + 3 * D) hB
  calc
    _ = 5 * n + (13 + 12 * D) * m + (2 + 3 * D) * B + out + 21 := by ring
    _ ≤ 5 * N + (13 + 12 * D) * N + (2 + 3 * D) * N +
        ((300 * D) * N * N + (100 + 3 * D) * N + 2) + 21 := by omega
    _ = _ := by ring

end UniqueGamesTheorem.Explicit.MachineClone100Certified

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_Clone100Triples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The concrete clone sample space. Global distinctness is a stronger
conditioning rule than distinctness only at repeated original variables.
It retains the same 3/100 bound and makes the number of copies uniform. -/

namespace UniqueGamesTheorem.Outer.Clone100Triples

abbrev Index := Fin 100
abbrev Triple := Index × Index × Index

def good (t : Triple) : Prop :=
  t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2

instance instDecidablePredTripleGood : DecidablePred good := fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

abbrev GoodTriple := {t : Triple // good t}

def toEmbedding (t : GoodTriple) : Fin 3 ↪ Index where
  toFun := ![t.val.1, t.val.2.1, t.val.2.2]
  inj' := by
    have h01 := t.property.1
    have h02 := t.property.2.1
    have h12 := t.property.2.2
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

def fromEmbedding (f : Fin 3 ↪ Index) : GoodTriple :=
  ⟨(f 0, f 1, f 2), by
    constructor
    · exact fun h => (by decide : (0 : Fin 3) ≠ 1) (f.injective h)
    constructor
    · exact fun h => (by decide : (0 : Fin 3) ≠ 2) (f.injective h)
    · exact fun h => (by decide : (1 : Fin 3) ≠ 2) (f.injective h)⟩

def embeddingEquiv : GoodTriple ≃ (Fin 3 ↪ Index) where
  toFun := toEmbedding
  invFun := fromEmbedding
  left_inv t := by
    apply Subtype.ext
    rfl
  right_inv f := by
    ext i
    fin_cases i <;> rfl

theorem card_goodTriple : Fintype.card GoodTriple = 970200 := by
  rw [Fintype.card_congr embeddingEquiv, Fintype.card_embedding_eq]
  norm_num [Nat.descFactorial_succ]

end UniqueGamesTheorem.Outer.Clone100Triples

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
open Clone100Triples
open scoped BigOperators

noncomputable section

def triples : List GoodTriple := Finset.univ.toList

theorem triples_length : triples.length = 970200 := by
  simp [triples, card_goodTriple]

def nameEquiv (n : Nat) : Fin n × Fin 100 ≃ Fin (n * 100) := finProdFinEquiv

end
end UniqueGamesTheorem.Outer.Clone100

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineClone100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Explicit.MachineClone100

open Turing UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Foundations.Complexity

noncomputable section

def indices (t : Outer.Clone100Triples.GoodTriple) : Nat × Nat × Nat :=
  (t.val.1.val, t.val.2.1.val, t.val.2.2.val)

def triples : List (Nat × Nat × Nat) := Outer.Clone100.triples.map indices

theorem triples_length : triples.length = 970200 := by
  simp [triples, Outer.Clone100.triples_length]

theorem triples_nonempty : triples ≠ [] := by
  apply List.length_pos_iff.mp
  rw [triples_length]
  decide

theorem serialized_polynomial (D N n m : Nat) (hn : n ≤ N) (hm : m ≤ N) :
    n * 100 + m * D + 2 + m * D * (300 * n + 2) ≤
      (300 * D) * N * N + (100 + 3 * D) * N + 2 := by
  have hproduct := Nat.mul_le_mul_left (300 * D) (Nat.mul_le_mul hm hn)
  have hvariables := Nat.mul_le_mul_left 100 hn
  have hoccurrences := Nat.mul_le_mul_left (3 * D) hm
  calc
    _ = (300 * D) * (m * n) + 100 * n + (3 * D) * m + 2 := by ring
    _ ≤ (300 * D) * (N * N) + 100 * N + (3 * D) * N + 2 :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hproduct hvariables) hoccurrences)
        (Nat.le_refl 2)
    _ = _ := by ring

end

end UniqueGamesTheorem.Explicit.MachineClone100

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineCloudCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCloudCount

open Turing

inductive Tape
  | original | work | target | scratch | count | spare
  deriving DecidableEq

abbrev Alphabet (_ : Tape) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

def memory (original work target scratch count spare : List Bool) : Tape → List Bool
  | .original => original
  | .work => work
  | .target => target
  | .scratch => scratch
  | .count => count
  | .spare => spare

@[simp] theorem memory_original (a b c d e f : List Bool) :
    memory a b c d e f .original = a := rfl
@[simp] theorem memory_work (a b c d e f : List Bool) :
    memory a b c d e f .work = b := rfl
@[simp] theorem memory_target (a b c d e f : List Bool) :
    memory a b c d e f .target = c := rfl
@[simp] theorem memory_scratch (a b c d e f : List Bool) :
    memory a b c d e f .scratch = d := rfl
@[simp] theorem memory_count (a b c d e f : List Bool) :
    memory a b c d e f .count = e := rfl
@[simp] theorem memory_spare (a b c d e f : List Bool) :
    memory a b c d e f .spare = f := rfl

@[simp] theorem update_memory_work (a b c d e f x : List Bool) :
    Function.update (memory a b c d e f) .work x = memory a x c d e f := by
  funext k
  cases k <;> rfl
@[simp] theorem update_memory_target (a b c d e f x : List Bool) :
    Function.update (memory a b c d e f) .target x = memory a b x d e f := by
  funext k
  cases k <;> rfl
@[simp] theorem update_memory_scratch (a b c d e f x : List Bool) :
    Function.update (memory a b c d e f) .scratch x = memory a b c x e f := by
  funext k
  cases k <;> rfl
@[simp] theorem update_memory_count (a b c d e f x : List Bool) :
    Function.update (memory a b c d e f) .count x = memory a b c d x f := by
  funext k
  cases k <;> rfl

variable {Λ σ : Type}

def finishField (restore : Λ) : TM2.Stmt Alphabet Λ (State σ) :=
  .load (fun state => ((state.1.1, false), none)) (.goto fun _ => restore)

def fieldLoop (again restore : Λ) : TM2.Stmt Alphabet Λ (State σ) :=
  .pop .work (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.peek .target (fun state head => (state.1, head))
        (.branch (fun state => state.2.getD false)
          (.pop .target (fun state _ => (state.1, none))
            (.push .scratch (fun _ => true) (.goto fun _ => again)))
          (.load (fun state => ((state.1.1, true), none)) (.goto fun _ => again))))
      (.peek .target (fun state head => (state.1, head))
        (.branch (fun state => !state.1.2 && !(state.2.getD false))
          (.push .count (fun _ => true) (finishField restore))
          (finishField restore))))

/-- Specification only: equality of the original natural values, unless an
earlier step has already detected overflow. -/
def hit (flag : Bool) (x v : Nat) : Nat := if flag = false ∧ x = v then 1 else 0

inductive Label
  | copyFirst | copySecond | headerFirst | headerSecond | row | field | restore
  | skip (i : Fin 4097)
  deriving DecidableEq, Fintype

def skipLabel (i : Nat) : Label :=
  if h : i < 4097 then .skip ⟨i, h⟩ else .row

def rowEntry : TM2.Stmt Alphabet Label (State σ) :=
  .peek .work (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.load (fun state => ((state.1.1, false), none)) (.goto fun _ => .field))
      (.load (fun state => ((state.1.1, false), none)) .halt))

abbrev Row := Nat × List Nat

def rowWords (r : Row) : List Nat := r.1 :: r.2

def rowsHits (v : Nat) : List Row → Nat
  | [] => 0
  | r :: rs => (if r.1 = v then 1 else 0) + rowsHits v rs

open UniqueGamesTheorem.Foundations.PCP

theorem rowsHits_eq_filter (v : Nat) (rs : List Row) :
    rowsHits v rs = (rs.filter (fun r => decide (r.1 = v))).length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      by_cases h : r.1 = v <;> simp [rowsHits, h, ih, Nat.add_comm]

end UniqueGamesTheorem.Foundations.Complexity.MachineCloudCount

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineCloudPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual cloud counting, geometric padding, and unary subtraction

One finite program places the checked cloud counter and geometric search on
shared tapes. Its final phase physically subtracts the preserved cloud size
from the computed power. A head test handles the empty cloud separately.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCloudPadding

open Turing
open UniqueGamesTheorem.Foundations.PCP

/- Static placement of homogeneous tapes, with an explicit finite partial
inverse. Complement tapes are preserved by every simulated transition. -/
namespace Placement

variable {K K' Λ Λ' σ : Type}

def tapes (view : K' → Option K) (source : K → List Bool)
    (extra : K' → List Bool) : K' → List Bool :=
  fun j => match view j with
    | some k => source k
    | none => extra j

def label (labels : Λ → Λ') (exit : Option Λ') : Option Λ → Option Λ'
  | some l => some (labels l)
  | none => exit

def configuration (view : K' → Option K) (labels : Λ → Λ') (exit : Option Λ')
    (extra : K' → List Bool) (c : TM2.Cfg (fun _ : K => Bool) Λ σ) :
    TM2.Cfg (fun _ : K' => Bool) Λ' σ :=
  ⟨label labels exit c.l, c.var, tapes view c.stk extra⟩

def statement (tape : K → K') (labels : Λ → Λ') (exit : Option Λ') :
    TM2.Stmt (fun _ : K => Bool) Λ σ → TM2.Stmt (fun _ : K' => Bool) Λ' σ
  | .push k f next => .push (tape k) f (statement tape labels exit next)
  | .peek k f next => .peek (tape k) f (statement tape labels exit next)
  | .pop k f next => .pop (tape k) f (statement tape labels exit next)
  | .load f next => .load f (statement tape labels exit next)
  | .branch f yes no => .branch f (statement tape labels exit yes) (statement tape labels exit no)
  | .goto f => .goto (fun state => labels (f state))
  | .halt => match exit with
    | some l => .goto (fun _ => l)
    | none => .halt

variable [DecidableEq K] [DecidableEq K']

omit [DecidableEq K] [DecidableEq K'] in
theorem tapes_apply (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (source : K → List Bool) (extra : K' → List Bool) (k : K) :
    tapes view source extra (tape k) = source k := by
  simp only [tapes, left]

theorem tapes_update (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (source : K → List Bool) (extra : K' → List Bool) (k : K) (w : List Bool) :
    tapes view (Function.update source k w) extra =
      Function.update (tapes view source extra) (tape k) w := by
  funext j
  by_cases h : j = tape k
  · subst j
    simp [tapes, left]
  · cases hv : view j with
    | none => simp [tapes, hv, h]
    | some i =>
      have hi : i ≠ k := by
        intro hi
        subst i
        exact h (right j k hv).symm
      simp [tapes, hv, h, hi]

theorem stepAux_simulation (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Λ → Λ') (exit : Option Λ') (extra : K' → List Bool)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (state : σ) (source : K → List Bool) :
    TM2.stepAux (statement tape labels exit q) state (tapes view source extra) =
      configuration view labels exit extra (TM2.stepAux q state source) := by
  induction q generalizing state source with
  | push k f next ih =>
    simp only [statement, TM2.stepAux, tapes_apply tape view left]
    rw [← tapes_update tape view left right]
    exact ih state (Function.update source k (f state :: source k))
  | peek k f next ih =>
    simpa only [statement, TM2.stepAux, tapes_apply tape view left] using
      ih (f state (source k).head?) source
  | pop k f next ih =>
    simp only [statement, TM2.stepAux, tapes_apply tape view left]
    rw [← tapes_update tape view left right]
    exact ih (f state (source k).head?) (Function.update source k (source k).tail)
  | load f next ih => simpa only [statement, TM2.stepAux] using ih (f state) source
  | branch f yes no ihYes ihNo =>
    cases h : f state with
    | false => simpa only [statement, TM2.stepAux, h, Bool.cond_false] using ihNo state source
    | true => simpa only [statement, TM2.stepAux, h, Bool.cond_true] using ihYes state source
  | goto f => rfl
  | halt => cases exit <;> rfl

theorem step_simulation (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Λ → Λ') (exit : Option Λ') (extra : K' → List Bool)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (target : Λ' → TM2.Stmt (fun _ : K' => Bool) Λ' σ)
    (atLabels : ∀ l, target (labels l) = statement tape labels exit (source l))
    (a b : TM2.Cfg (fun _ : K => Bool) Λ σ) (h : TM2.step source a = some b) :
    TM2.step target (configuration view labels exit extra a) =
      some (configuration view labels exit extra b) := by
  cases a with
  | mk l state sourceTapes =>
    cases l with
    | none => simp [TM2.step] at h
    | some l =>
      have hb : TM2.stepAux (source l) state sourceTapes = b := Option.some.inj h
      rw [← hb]
      change some (TM2.stepAux (target (labels l)) state (tapes view sourceTapes extra)) = _
      rw [atLabels, stepAux_simulation tape view left right]

end Placement

inductive Tape
  | table | query | count | work | scratch | spare | power | level | fuel | product
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.table, .query, .count, .work, .scratch, .spare,
  .power, .level, .fuel, .product]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Label
  | init | countCode (l : MachineCloudCount.Label)
  | branch | powerCode (l : MachineCeilingPower.Label)
  | subtract | restore
  deriving DecidableEq, Fintype

abbrev Alphabet (_ : Tape) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

def memory (table query count work scratch spare power level fuel product : List Bool) :
    Tape → List Bool
  | .table => table
  | .query => query
  | .count => count
  | .work => work
  | .scratch => scratch
  | .spare => spare
  | .power => power
  | .level => level
  | .fuel => fuel
  | .product => product

@[simp] theorem update_count (a b c d e f g h i j x : List Bool) :
    Function.update (memory a b c d e f g h i j) .count x = memory a b x d e f g h i j := by
  funext k; cases k <;> rfl
@[simp] theorem update_scratch (a b c d e f g h i j x : List Bool) :
    Function.update (memory a b c d e f g h i j) .scratch x = memory a b c d x f g h i j := by
  funext k; cases k <;> rfl
@[simp] theorem update_power (a b c d e f g h i j x : List Bool) :
    Function.update (memory a b c d e f g h i j) .power x = memory a b c d e f x h i j := by
  funext k; cases k <;> rfl

@[simp] theorem update_level (a b c d e f g h i j x : List Bool) :
    Function.update (memory a b c d e f g h i j) .level x = memory a b c d e f g x i j := by
  funext k; cases k <;> rfl

def countTape : MachineCloudCount.Tape → Tape
  | .original => .table
  | .target => .query
  | .count => .count
  | .work => .work
  | .scratch => .scratch
  | .spare => .spare

def countView : Tape → Option MachineCloudCount.Tape
  | .table => some .original
  | .query => some .target
  | .count => some .count
  | .work => some .work
  | .scratch => some .scratch
  | .spare => some .spare
  | _ => none

theorem countView_left (k : MachineCloudCount.Tape) : countView (countTape k) = some k := by
  cases k <;> rfl
theorem countView_right (j : Tape) (k : MachineCloudCount.Tape)
    (h : countView j = some k) : countTape k = j := by
  cases j <;> cases k <;> simp_all [countView, countTape]

def powerTape : MachineCeilingPower.Tape → Tape
  | .input => .count
  | .work => .work
  | .power => .power
  | .saved => .scratch
  | .level => .level
  | .fuel => .fuel
  | .spare => .spare
  | .product => .product

def powerView : Tape → Option MachineCeilingPower.Tape
  | .count => some .input
  | .work => some .work
  | .power => some .power
  | .scratch => some .saved
  | .level => some .level
  | .fuel => some .fuel
  | .spare => some .spare
  | .product => some .product
  | _ => none

theorem powerView_left (k : MachineCeilingPower.Tape) : powerView (powerTape k) = some k := by
  cases k <;> rfl
theorem powerView_right (j : Tape) (k : MachineCeilingPower.Tape)
    (h : powerView j = some k) : powerTape k = j := by
  cases j <;> cases k <;> simp_all [powerView, powerTape]

@[simp] theorem countMemory (a b c d e f g h i j : List Bool) :
    Placement.tapes countView (MachineCloudCount.memory a d b e c f)
      (memory a b c d e f g h i j) = memory a b c d e f g h i j := by
  funext k; cases k <;> rfl

@[simp] theorem powerMemory (a b c d e f g h i j : List Bool) :
    Placement.tapes powerView (MachineCeilingPower.memory c d g e h i f j)
      (memory a b c d e f g h i j) = memory a b c d e f g h i j := by
  funext k; cases k <;> rfl

theorem countTapes (a b c d e f : List Bool) (extra : Tape → List Bool) :
    Placement.tapes countView (MachineCloudCount.memory a d b e c f) extra =
      memory a b c d e f (extra .power) (extra .level) (extra .fuel) (extra .product) := by
  funext k; cases k <;> rfl

theorem powerTapes (c d g e h i f j : List Bool) (extra : Tape → List Bool) :
    Placement.tapes powerView (MachineCeilingPower.memory c d g e h i f j) extra =
      memory (extra .table) (extra .query) c d e f g h i j := by
  funext k; cases k <;> rfl

variable {σ : Type}

def subtractLoop : TM2.Stmt Alphabet Label (State σ) :=
  .pop .count (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.pop .power (fun state _ => (state.1, none))
        (.push .scratch (fun _ => true) (.goto fun _ => .subtract)))
      (.push .count (fun _ => false)
        (.load (fun state => (state.1, none)) (.goto fun _ => .restore))))

theorem appendTrace {α : Type} (f : α → α) {a b : Nat} {x y z : α}
    (hs : f^[a] x = y) (ht : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, hs, ht]

def postTime (k : Nat) : Nat :=
  1 + if k = 0 then 0 else MachineCeilingPower.totalTime ExpanderFamily.growth k + (2 * k + 2)

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C (ExpanderFamily.growth + 8) * Polynomial.X ^ 2 + 25 * Polynomial.X + 10

end UniqueGamesTheorem.Foundations.Complexity.MachineCloudPadding

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineCloudPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCloudPrefix

open Turing
open UniqueGamesTheorem.Foundations.PCP
open scoped BigOperators

inductive Tape
  | inner (k : MachineCloudPadding.Tape)
  | bound | remaining | total
  deriving DecidableEq, Fintype

inductive Label
  | init | copyFirst | copySecond | guard | done
  | padding (l : MachineCloudPadding.Label)
  | add | clearCount | clearLevel | increment
  deriving DecidableEq, Fintype

abbrev Alphabet (_ : Tape) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

def memory (inner : MachineCloudPadding.Tape → List Bool) (bound remaining total : List Bool) :
    Tape → List Bool
  | .inner k => inner k
  | .bound => bound
  | .remaining => remaining
  | .total => total

def frame (table query count power level bound remaining total : List Bool) : Tape → List Bool :=
  memory (MachineCloudPadding.memory table query count [] [] [] power level [] []) bound remaining total

@[simp] theorem frame_query (a b c d e f g h : List Bool) :
    frame a b c d e f g h (.inner .query) = b := rfl
@[simp] theorem frame_count (a b c d e f g h : List Bool) :
    frame a b c d e f g h (.inner .count) = c := rfl
@[simp] theorem frame_power (a b c d e f g h : List Bool) :
    frame a b c d e f g h (.inner .power) = d := rfl
@[simp] theorem frame_level (a b c d e f g h : List Bool) :
    frame a b c d e f g h (.inner .level) = e := rfl
@[simp] theorem frame_bound (a b c d e f g h : List Bool) :
    frame a b c d e f g h .bound = f := rfl
@[simp] theorem frame_remaining (a b c d e f g h : List Bool) :
    frame a b c d e f g h .remaining = g := rfl
@[simp] theorem frame_total (a b c d e f g h : List Bool) :
    frame a b c d e f g h .total = h := rfl

@[simp] theorem update_frame_query (a b c d e f g h x : List Bool) :
    Function.update (frame a b c d e f g h) (.inner .query) x =
      frame a x c d e f g h := by
  funext k; cases k with
  | inner k => cases k <;> rfl
  | bound => rfl
  | remaining => rfl
  | total => rfl
@[simp] theorem update_frame_count (a b c d e f g h x : List Bool) :
    Function.update (frame a b c d e f g h) (.inner .count) x =
      frame a b x d e f g h := by
  funext k; cases k with
  | inner k => cases k <;> rfl
  | bound => rfl
  | remaining => rfl
  | total => rfl
@[simp] theorem update_frame_power (a b c d e f g h x : List Bool) :
    Function.update (frame a b c d e f g h) (.inner .power) x =
      frame a b c x e f g h := by
  funext k; cases k with
  | inner k => cases k <;> rfl
  | bound => rfl
  | remaining => rfl
  | total => rfl
@[simp] theorem update_frame_level (a b c d e f g h x : List Bool) :
    Function.update (frame a b c d e f g h) (.inner .level) x =
      frame a b c d x f g h := by
  funext k; cases k with
  | inner k => cases k <;> rfl
  | bound => rfl
  | remaining => rfl
  | total => rfl
@[simp] theorem update_frame_remaining (a b c d e f g h x : List Bool) :
    Function.update (frame a b c d e f g h) .remaining x =
      frame a b c d e f x h := by
  funext k; cases k <;> rfl
@[simp] theorem update_frame_total (a b c d e f g h x : List Bool) :
    Function.update (frame a b c d e f g h) .total x =
      frame a b c d e f g x := by
  funext k; cases k <;> rfl

def paddingView : Tape → Option MachineCloudPadding.Tape
  | .inner k => some k
  | _ => none

theorem paddingView_left (k : MachineCloudPadding.Tape) : paddingView (.inner k) = some k := rfl

theorem paddingView_right (j : Tape) (k : MachineCloudPadding.Tape)
    (h : paddingView j = some k) : Tape.inner k = j := by
  cases j <;> simp_all [paddingView]

theorem placedTapes (inner : MachineCloudPadding.Tape → List Bool) (extra : Tape → List Bool) :
    MachineCloudPadding.Placement.tapes paddingView inner extra =
      memory inner (extra .bound) (extra .remaining) (extra .total) := by
  funext j; cases j <;> rfl

variable {σ : Type}

theorem appendTrace {α : Type} (f : α → α) {a b : Nat} {x y z : α}
    (hs : f^[a] x = y) (ht : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, hs, ht]

/-- Uniform budget for one vertex iteration, including unary addition and
cleanup. Its input argument bounds the complete table length. -/
def cycleBudget (L : Nat) : Nat :=
  (ExpanderFamily.growth + 8) * (2 * L) ^ 2 + 25 * (2 * L) + 10 +
    (ExpanderFamily.growth + 2) * L + 5

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.X *
      (Polynomial.C (ExpanderFamily.growth + 8) * (2 * Polynomial.X) ^ 2 +
        25 * (2 * Polynomial.X) + 10 +
          Polynomial.C (ExpanderFamily.growth + 2) * Polynomial.X + 5) +
    2 * (Polynomial.X + 1) + 3

end UniqueGamesTheorem.Foundations.Complexity.MachineCloudPrefix

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineCloudRankLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCloudRank

open Turing MachineCloudCount

variable {σ : Type}

@[simp] theorem update_memory_spare (a b c d e f x : List Bool) :
    Function.update (memory a b c d e f) .spare x = memory a b c d e x := by
  funext k
  cases k <;> rfl

inductive RankLabel
  | queryFirst | querySecond | querySkip | tableFirst | tableSecond
  | headerFirst | headerSecond | row | field | restore | done
  | skip (i : Fin 4097)
  deriving DecidableEq, Fintype

def rankSkip (i : Nat) : RankLabel :=
  if h : i < 4097 then .skip ⟨i, h⟩ else .row

/-- In a filtered list, the rank of a retained entry is the number of retained
entries preceding its first original occurrence. This is a specification lemma. -/
theorem idxOf_filter_prefix {α : Type*} [BEq α] [LawfulBEq α]
    (p : α → Bool) (a : α) (hp : p a = true) :
    ∀ xs : List α, a ∈ xs →
      (xs.filter p).idxOf a = ((xs.take (xs.idxOf a)).filter p).length := by
  classical
  intro xs
  induction xs with
  | nil => intro ha; simp at ha
  | cons b xs ih =>
      intro ha
      by_cases hba : b = a
      · subst b
        simp [hp]
      · have ha' : a ∈ xs := by simpa [hba, Ne.symm hba] using ha
        cases hb : p b <;>
          simp [hba, hb, ih ha']

open UniqueGamesTheorem.Foundations.PCP

end UniqueGamesTheorem.Foundations.Complexity.MachineCloudRank

/-! Actual inverse cloud numbering. The input table and query are copied
preservingly. A unary working rank decreases only on equal stored tail
fields; a separate unary row position increases on every skipped row.
Only finite phase flags and symbol registers occur in the control state. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCloudSelect

open Turing
open MachineCloudCount (Row rowWords rowsHits )

abbrev BaseTape := MachineCloudCount.Tape
abbrev BaseAlphabet := MachineCloudCount.Alphabet
abbrev BaseState (σ : Type) := MachineCloudCount.State σ

inductive BaseLabel
  | queryFirst | querySecond | querySkip | tableFirst | tableSecond
  | headerFirst | headerSecond | field | restore | done | clearWork | clearRank
  | skip (i : Fin 4097)
  deriving DecidableEq, Fintype

def skipLabel (i : Nat) : BaseLabel :=
  if h : i < 4097 then .skip ⟨i, h⟩ else .done

variable {σ : Type}

inductive Phase
  | checking | advancing | finishing
  deriving DecidableEq

protected abbrev Phase.enumList : List Phase := [.checking, .advancing, .finishing]

protected theorem Phase.enumList_nodup : Phase.enumList.Nodup := by decide

instance instFintypePhase : Fintype Phase where
  elems := ⟨Phase.enumList, Phase.enumList_nodup⟩
  complete x := by cases x <;> decide
inductive Control
  | initialize_ | dispatch
  deriving DecidableEq

protected abbrev Control.enumList : List Control := [.initialize_, .dispatch]

protected theorem Control.enumList_nodup : Control.enumList.Nodup := by decide

instance instFintypeControl : Fintype Control where
  elems := ⟨Control.enumList, Control.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape := BaseTape ⊕ Unit
abbrev Label := BaseLabel ⊕ Control
abbrev State (σ : Type) := BaseState σ × Phase

open UniqueGamesTheorem.Foundations.PCP

end UniqueGamesTheorem.Foundations.Complexity.MachineCloudSelect

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineExpanderRowDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The two actual division phases of the expander-row program. Static state
conjugation connects the fixed-divisor machine to the common emitter state.
Only the concrete statement placement equations are premises; no phase trace
or whole-row execution is assumed. Each phase has exactly `n + 2` transitions.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {K Λ ρ : Type} [DecidableEq K] [Fintype ρ]

@[simp] theorem divisionStates_apply (ρ : Type) (d : Nat)
    (s : MachineFixedDivMod.State (Ambient ρ d × Unit) (degree d)) :
    divisionStates ρ d s = (((s.1.1.1, s.1.2), ()), s.2) := rfl

/-- The common row state at a division boundary, with its local residue reset. -/
def divisionState {d : Nat} (positive : 0 < d) (ambient : ρ) (control : Control d)
    (register : Option Bool) : State ρ d :=
  ((((ambient, control),
    MachineFixedDivMod.residue (degree d) (Nat.mul_pos positive positive) 0), ()), register)

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineExpanderTableProgramLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

inductive ExtraTape
  | vertexCount | result
  deriving DecidableEq

protected abbrev ExtraTape.enumList : List ExtraTape := [.vertexCount, .result]

protected theorem ExtraTape.enumList_nodup : ExtraTape.enumList.Nodup := by decide

instance instFintypeExtraTape : Fintype ExtraTape where
  elems := ⟨ExtraTape.enumList, ExtraTape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive OuterLabel
  | initialize_ | vertexGuard | prepareRow | afterRow | reverseOutput | done
  deriving DecidableEq

protected abbrev OuterLabel.enumList : List OuterLabel := [.initialize_, .vertexGuard, .prepareRow,
  .afterRow, .reverseOutput, .done]

protected theorem OuterLabel.enumList_nodup : OuterLabel.enumList.Nodup := by decide

instance instFintypeOuterLabel : Fintype OuterLabel where
  elems := ⟨OuterLabel.enumList, OuterLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Label (d : Nat) := MachineExpanderRow.Label d ⊕ OuterLabel
abbrev Position (d : Nat) := Fin (rowFactor d)
abbrev State (ρ : Type) (d : Nat) := MachineExpanderRow.State ρ d × Position d

variable {ρ : Type} [Fintype ρ]

def rowReturn (d : Nat) : Option (Label d) := some (.inr .afterRow)

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

inductive ExtraTape
  | remainingLevel | currentSize | unaryScratch | tableReverse
  deriving DecidableEq

protected abbrev ExtraTape.enumList : List ExtraTape := [.remainingLevel, .currentSize,
  .unaryScratch, .tableReverse]

protected theorem ExtraTape.enumList_nodup : ExtraTape.enumList.Nodup := by decide

instance instFintypeExtraTape : Fintype ExtraTape where
  elems := ⟨ExtraTape.enumList, ExtraTape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive AffinePhase
  | copyCount | multiplySize
  deriving DecidableEq

protected abbrev AffinePhase.enumList : List AffinePhase := [.copyCount, .multiplySize]

protected theorem AffinePhase.enumList_nodup : AffinePhase.enumList.Nodup := by decide

instance instFintypeAffinePhase : Fintype AffinePhase where
  elems := ⟨AffinePhase.enumList, AffinePhase.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive AffineLabel
  | seed | scan | restore
  deriving DecidableEq

protected abbrev AffineLabel.enumList : List AffineLabel := [.seed, .scan, .restore]

protected theorem AffineLabel.enumList_nodup : AffineLabel.enumList.Nodup := by decide

instance instFintypeAffineLabel : Fintype AffineLabel where
  elems := ⟨AffineLabel.enumList, AffineLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive OuterLabel
  | initialize_
  | levelGuard
  | affine (phase : AffinePhase) (label : AffineLabel)
  | clearOldTable | reverseResult | reverseTable | clearCurrentSize
  | drainInputVertex | drainVertexCount | done
  deriving DecidableEq, Fintype

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineExpanderRowCleanup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

@[simp] theorem dirtyTape_zero : dirtyTape 0 = .queryIndex := rfl
@[simp] theorem dirtyTape_one : dirtyTape 1 = .lookupOutput := rfl
@[simp] theorem dirtyTape_two : dirtyTape 2 = .quotientFirst := rfl
@[simp] theorem dirtyTape_three : dirtyTape 3 = .quotientSecond := rfl
@[simp] theorem dirtyTape_four : dirtyTape 4 = .remainderFirst := rfl
@[simp] theorem dirtyTape_five : dirtyTape 5 = .remainderSecond := rfl

variable {K Λ ρ : Type} [DecidableEq K]

def cleanupTapes (ports : Tape → K) (base : K → List Bool) : K → List Bool :=
  Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update base (ports .queryIndex) [])
            (ports .lookupOutput) [])
          (ports .quotientFirst) [])
        (ports .quotientSecond) [])
      (ports .remainderFirst) [])
    (ports .remainderSecond) []

def cleanupSteps (ports : Tape → K) (base : K → List Bool) : Nat :=
  ((base (ports .queryIndex)).length + 1) +
  ((base (ports .lookupOutput)).length + 1) +
  ((base (ports .quotientFirst)).length + 1) +
  ((base (ports .quotientSecond)).length + 1) +
  ((base (ports .remainderFirst)).length + 1) +
  ((base (ports .remainderSecond)).length + 1)

@[simp] theorem cleanupTapes_dirty (ports : Tape → K) (distinct : Function.Injective ports)
    (base : K → List Bool) (i : Fin 6) :
    cleanupTapes ports base (ports (dirtyTape i)) = [] := by
  fin_cases i <;>
    simp [cleanupTapes, distinct.eq_iff]

@[simp] theorem cleanupTapes_table (ports : Tape → K) (distinct : Function.Injective ports)
    (base : K → List Bool) :
    cleanupTapes ports base (ports .table) = base (ports .table) := by
  simp [cleanupTapes, distinct.eq_iff]

@[simp] theorem cleanupTapes_inputVertex (ports : Tape → K)
    (distinct : Function.Injective ports) (base : K → List Bool) :
    cleanupTapes ports base (ports .inputVertex) = base (ports .inputVertex) := by
  simp [cleanupTapes, distinct.eq_iff]

@[simp] theorem cleanupTapes_output (ports : Tape → K) (distinct : Function.Injective ports)
    (base : K → List Bool) :
    cleanupTapes ports base (ports .output) = base (ports .output) := by
  simp [cleanupTapes, distinct.eq_iff]

theorem join_trace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

variable [Fintype ρ] {d : Nat}

def initializedTapes (ports : Tape → K) (base : K → List Bool) : K → List Bool :=
  Function.update
    (Function.update
      (Function.update
        (Function.update base (ports .quotientFirst) (false :: base (ports .quotientFirst)))
        (ports .quotientSecond) (false :: base (ports .quotientSecond)))
      (ports .remainderFirst) (false :: base (ports .remainderFirst)))
    (ports .remainderSecond) (false :: base (ports .remainderSecond))

def clearedQueryTapes (ports : Tape → K) (base : K → List Bool) : K → List Bool :=
  Function.update
    (Function.update base (ports .queryIndex) (base (ports .queryIndex)).tail)
    (ports .lookupOutput) (base (ports .lookupOutput)).tail

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineExpanderRowEmitLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

section

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.AlphabetTable

/-- One scaled scan/restore, one bounded offset, the delimiter, and final jump. -/
def emitSteps (n : Nat) : Nat := 3 * (n + 1) + 6

end

/-!
# Actual lookup and reversal phases of the expander row program

The Boolean phase selector chooses the first or second occurrence of the same
preserving lookup. The selected word is proved to be the actual stored reverse
index of the supplied graph row. All execution facts follow from the concrete
program statements; no phase execution is assumed.
-/

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineExpanderRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Complete execution of one expander-table row

The actual finite program performs both stored-table lookups, splits their
results by its fixed degree, emits the resulting square/zigzag reverse index,
and clears its work tapes. Its transition bound is linear in the unary input
table length. The output accumulator and finite caller state are arbitrary.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords PCP.AlphabetTable

theorem concatenate {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_ExpanderTableEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Exact row enumeration and accumulator contents for an expander-table step

The outer loop enumerates original vertices, and the inner loop enumerates
cloud/port positions in increasing mixed-radix order. The resulting list is
the actual next table's stored rotation-word list. Prefix and reverse-encoding
identities describe data accumulated by a row loop; they assert no runtime.
-/

namespace UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration

open ExpanderTables ExpanderRowControl ExpanderTableWords
open UniqueGamesTheorem.Foundations.Complexity

variable {v d : Nat}

/-- Input position in the actual next table, with port varying fastest. -/
def globalIndex (vertex : Fin v) (position : Fin (rowFactor d)) :
    Fin ((v * cloudSize d) * degree d) :=
  let pair := (rowIndex (cloudSize d) (degree d)).symm position
  rowIndex (v * cloudSize d) (degree d)
    (rowIndex v (cloudSize d) (vertex, pair.1), pair.2)

theorem globalIndex_val (vertex : Fin v) (position : Fin (rowFactor d)) :
    (globalIndex vertex position).val = position.val + rowFactor d * vertex.val := by
  let pair := (rowIndex (cloudSize d) (degree d)).symm position
  have hp := congrArg Fin.val
    ((rowIndex (cloudSize d) (degree d)).apply_symm_apply position)
  change pair.2.val + degree d * pair.1.val = position.val at hp
  change pair.2.val + degree d * (pair.1.val + cloudSize d * vertex.val) = _
  calc
    _ = (pair.2.val + degree d * pair.1.val) + rowFactor d * vertex.val := by
      dsimp only [rowFactor]
      ring
    _ = position.val + rowFactor d * vertex.val := by rw [hp]

theorem ofFn_cast {α : Type*} {n m : Nat} (h : n = m) (f : Fin m → α) :
    List.ofFn (fun i : Fin n => f (Fin.cast h i)) = List.ofFn f := by
  cases h
  rfl

end UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineExpanderTableRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual execution of all expander-table positions for one vertex

The inner loop calls the complete row machine once per fixed cloud/port position.
The returned state and the successful machine execution are constructed together.
Neither a row execution nor an inner-loop execution is a caller premise.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

def singleStep {α : Type*} (step : α → Option α) (a b : α)
    (h : step a = some b) : StateTransition.EvalsToInTime step a (some b) 1 where
  steps := 1
  evals_in_steps := by change step a = some b; exact h
  steps_le_m := Nat.le_refl _

def sequence {α : Type*} {step : α → Option α} {a b c : α} {m n : Nat}
    (first : StateTransition.EvalsToInTime step a (some b) m)
    (second : StateTransition.EvalsToInTime step b (some c) n) :
    StateTransition.EvalsToInTime step a (some c) (m + n) := by
  simpa only [Nat.add_comm n m] using
    StateTransition.EvalsToInTime.trans step m n a b (some c) first second

def widen {α : Type*} {step : α → Option α} {a : α} {b : Option α} {m n : Nat}
    (run : StateTransition.EvalsToInTime step a b m) (bound : m ≤ n) :
    StateTransition.EvalsToInTime step a b n where
  toEvalsTo := run.toEvalsTo
  steps_le_m := run.steps_le_m.trans bound

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineExpanderTableLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual outer vertex iteration for expander tables

The invariant is the reversed unary encoding of all completed vertices. Each
positive unary guard invokes the proved complete fixed-position row loop;
the zero guard enters the actual output-reversal phase. No execution premise
is supplied by the caller.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

def boundarySingleStep {S : Type*} (f : S → Option S) (a b : S)
    (h : f a = some b) : StateTransition.EvalsToInTime f a (some b) 1 where
  steps := 1
  evals_in_steps := by change f a = some b; exact h
  steps_le_m := Nat.le_refl _

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineExpanderFamilyBoundsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounds for materializing the actual expander family

The costs use the encoded old and new rotation tables, and the already checked
table-machine polynomial. The finite sum follows the actual recursive table
family. These arithmetic lemmas introduce no execution assumptions and make no
claim that the output is polynomial in an isolated binary level parameter.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamilyBounds

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

theorem vertexCount_monotone {q : Nat} (positive : 0 < q) :
    Monotone (vertexCount q) := by
  intro m n hmn
  rw [vertexCount_eq, vertexCount_eq]
  exact Nat.pow_le_pow_right (Nat.mul_pos positive positive) hmn

theorem level_le_vertexCount {q : Nat} (growth : 1 < q * q) (level : Nat) :
    level ≤ vertexCount q level := by
  have positive : 0 < q := by nlinarith
  induction level with
  | zero => exact Nat.zero_le _
  | succ level ih =>
    have hpos := vertexCount_positive positive level
    have hmul := Nat.mul_le_mul_left (vertexCount q level)
      (show 2 ≤ q * q by omega)
    change level + 1 ≤ vertexCount q level * (q * q)
    nlinarith

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamilyBounds

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineExpanderFamilyLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual counted repetition of complete table-expansion cycles. The input
counter is physically decremented, and the invariant carries the exact table
at the completed family level. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineExpanderFamilyBounds

def familySingleStep {S : Type*} (f : S → Option S) (a b : S)
    (h : f a = some b) : StateTransition.EvalsToInTime f a (some b) 1 where
  steps := 1
  evals_in_steps := by change f a = some b; exact h
  steps_le_m := Nat.le_refl _

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineExpanderFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineExpanderFamilyBounds

def singleFamilyStep {S : Type*} (f : S → Option S) (a b : S)
    (h : f a = some b) : StateTransition.EvalsToInTime f a (some b) 1 where
  steps := 1
  evals_in_steps := by change f a = some b; exact h
  steps_le_m := Nat.le_refl _

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineInitialHeaders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Actual caller-program traces for non-destructive unary-prefix emission and
the two headers of the raw initial graph. Unread suffixes are never scanned.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineInitialHeaders

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

theorem replicate_append_cons (n : ℕ) (xs : List Bool) :
    List.replicate n true ++ true :: xs = List.replicate (n + 1) true ++ xs := by
  rw [List.replicate_add]
  simp

theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.Complexity.MachineInitialHeaders

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachinePortReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePortReindex

open Turing

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) (d : Nat) := MachineFixedDivMod.State A d

def clean (d : Nat) (positive : 0 < d) (ambient : A) : State A d :=
  ((ambient, MachineFixedDivMod.residue d positive 0), none)

inductive Label (d : Nat)
  | copySeed | copyScan | copyRestore | initialize_ | divide
  | emit (r : Fin d)
  | affineScan | affineRestore | drainQuotient | finish
  deriving DecidableEq, Fintype

def exitAt {d : Nat} (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A d) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def steps (d j : Nat) : Nat := 3 * j + 3 * (j / d) + 11

def value (d c b j : Nat) : Nat := c * (j / d) + (j % d) + b

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem lazy_value (d j : Nat) : value d (2 * d) d j =
    2 * d * (j / d) + d + (j % d) := by
  unfold value
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachinePortReindex

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PreprocessingLazyWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact codec expansion of the executable lazy graph table. Each vertex
contributes its `d` always-accepting selfloops, followed by its `d` stored
constraints with the reverse field changed by the displayed div/mod map. -/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingLazyWords

open PortTables GraphTables PreprocessingOverlayTables
open UniqueGamesTheorem.Foundations.Complexity

variable {n d : Nat}

/-- The machine's fixed-degree numerical map for an old reverse-row index. -/
def reverseMap (d j : Nat) : Nat := 2 * d * (j / d) + d + j % d

/-- Finite mixed-radix indexing agrees with the actual row-vector order. -/
theorem ofFn_rowIndex {α : Type*} (f : Fin (n * d) → α) :
    List.ofFn f = (List.ofFn fun v : Fin n =>
      List.ofFn fun p : Fin d => f (rowIndex n d (v, p))).flatten := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  congr 1
  funext v
  congr 1
  funext p
  apply congrArg f
  apply Fin.ext
  simp only [rowIndex_val]
  ac_rfl

end UniqueGamesTheorem.Foundations.PCP.PreprocessingLazyWords

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineLazyRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineLazyRows

open Turing PCP.GraphTables
open PCP.PreprocessingLazyWords (reverseMap )

variable {K Λ A : Type} [DecidableEq K]

abbrev Label (d : Nat) := MachinePortReindex.Label d ⊕ MachineTableRows.Label
abbrev State (A : Type) (d : Nat) := MachinePortReindex.State A d

/-- Tape roles: tail, old reverse, relation, scratch, divided copy,
quotient, new reverse, accumulated output, row buffer. -/
def addressIndex : Fin 5 → Fin 9 := ![1, 3, 4, 5, 6]

theorem addressIndex_injective : Function.Injective addressIndex := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [addressIndex]

def fields (tape : Fin 9 → K) : Fin 3 → K := ![tape 0, tape 6, tape 2]

def bodyIndex (i : Fin 9) : Fin 10 := i.castSucc

theorem bodyIndex_injective : Function.Injective bodyIndex := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 10 => k.val) h

inductive StreamLabel (d : Nat)
  | tailStart | tailRead | reverseStart | reverseRead | copyRelation
  | row (stage : Label d)
  | clearTail | clearOld | clearRelation | clearNew
  deriving DecidableEq, Fintype

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

abbrev VertexLabel (d : Nat) := Fin (d + 1) × Option (StreamLabel d)

def valueBound (c b m : Nat) : Nat := c * m + m + b
def rowSizeBound (c b n m : Nat) : Nat := n + valueBound c b m + 8194
def rowCostBound (c b n m : Nat) : Nat :=
  2 * n + 8 * m + valueBound c b m + 4 * rowSizeBound c b n m + 8224

end UniqueGamesTheorem.Foundations.Complexity.MachineLazyRows

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineTableSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
A fixed five-tape machine physically copies a graph table, preserves the
original input, and splits its two unary header fields from the copied rows.
The exact trace is ambient-state polymorphic for static machine placement.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit

open Turing

abbrev Tape := Fin 5
abbrev State (σ : Type) := σ × Option Bool

inductive Label
  | copyFirst | copySecond | startVertices | readVertices | startDarts | readDarts
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.copyFirst, .copySecond, .startVertices,
  .readVertices, .startDarts, .readDarts]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

/-- Tape 0 is protected input, 1 is the working row stream, 2 is scratch,
and 3 and 4 hold the extracted vertex and dart counts. -/
def tapes (original work vertices darts : List Bool) : Tape → List Bool :=
  fun k => if k = 0 then original else if k = 1 then work
    else if k = 3 then vertices else if k = 4 then darts else []

def initialTapes (input : List Bool) : Tape → List Bool := tapes input [] [] []

noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 4 * Polynomial.X + Polynomial.C 6

@[simp] theorem timePolynomial_eval (length : Nat) :
    timePolynomial.eval length = 4 * length + 6 := by simp [timePolynomial]

end UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineLazyTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual whole-table lazy-graph machine, with fixed positive old degree.
All unbounded counts and addresses reside on unary tapes. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineLazyTable

open Turing PCP

inductive Tape
  | input | output | source | vertices | darts | fuel | vertex | reverse
  | tail | old | relation | scratch | divided | quotient | newReverse | rowBuffer
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .output, .source, .vertices, .darts, .fuel,
  .vertex, .reverse, .tail, .old, .relation, .scratch, .divided, .quotient, .newReverse,
  .rowBuffer]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

def splitRoles : Fin 5 → Tape := ![.input, .source, .scratch, .vertices, .darts]
def splitView : Tape → Option (Fin 5)
  | .input => some 0 | .source => some 1 | .scratch => some 2
  | .vertices => some 3 | .darts => some 4 | _ => none

def dummyRoles : Fin 6 → Tape := ![.tail, .reverse, .relation, .rowBuffer, .output, .scratch]
def dummyView : Tape → Option (Fin 6)
  | .tail => some 0 | .reverse => some 1 | .relation => some 2
  | .rowBuffer => some 3 | .output => some 4 | .scratch => some 5 | _ => none

def oldRoles : Fin 10 → Tape :=
  ![.tail, .old, .relation, .scratch, .divided, .quotient, .newReverse,
    .output, .rowBuffer, .source]

theorem splitRoles_left (i : Fin 5) : splitView (splitRoles i) = some i := by
  fin_cases i <;> rfl

theorem splitRoles_right (t : Tape) (i : Fin 5) (h : splitView t = some i) : splitRoles i = t := by
  cases t <;> fin_cases i <;> simp_all [splitView, splitRoles]

theorem dummyRoles_left (i : Fin 6) : dummyView (dummyRoles i) = some i := by
  fin_cases i <;> rfl

theorem dummyRoles_right (t : Tape) (i : Fin 6) (h : dummyView t = some i) : dummyRoles i = t := by
  cases t <;> fin_cases i <;> simp_all [dummyView, dummyRoles]

theorem oldRoles_injective : Function.Injective oldRoles := by decide

inductive Label (d : Nat)
  | split (label : MachineTableSplit.Label)
  | dartSeed | dartScan | dartRestore | vertexSeed | vertexScan | vertexRestore
  | fuelFirst | fuelSecond | seedCounters | guard | copyVertexFirst | copyVertexSecond
  | dummy (label : MachineDummyRows.Label d)
  | clearDummyTail | clearDummyRelation
  | oldRows (label : MachineLazyRows.VertexLabel d)
  | nextVertex | clearVertices | clearDarts | clearFuel | clearVertex | clearReverse
  deriving DecidableEq, Fintype

def frame (input source output vertices darts fuel vertex reverse : List Bool) : Tape → List Bool
  | .input => input | .source => source | .output => output
  | .vertices => vertices | .darts => darts | .fuel => fuel
  | .vertex => vertex | .reverse => reverse | _ => []

def initialTapes (input : List Bool) : Tape → List Bool := frame input [] [] [] [] [] [] []

def finalTapes (input output : List Bool) : Tape → List Bool := frame input [] output [] [] [] [] []

theorem joinTrace {X : Type} {f : X → X} {a b c : X} {s t : Nat}
    (first : f^[s] a = b) (second : f^[t] b = c) : f^[s + t] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem frame_old_empty (input source output vertices darts fuel vertex reverse : List Bool)
    (i : Fin 10) (h7 : i ≠ 7) (h9 : i ≠ 9) :
    frame input source output vertices darts fuel vertex reverse (oldRoles i) = [] := by
  fin_cases i <;> simp_all [frame, oldRoles]

def finishSteps (d n m v : Nat) : Nat := n + m + v + 2 * d * v + 11

def remaining (n r : Nat) : List (Fin n) := (List.finRange n).drop r

@[simp] theorem remaining_zero (n : Nat) : remaining n 0 = List.finRange n := by simp [remaining]
@[simp] theorem remaining_done (n : Nat) : remaining n n = [] := by simp [remaining]

theorem remaining_cons (n r : Nat) (h : r < n) :
    remaining n r = ⟨r, h⟩ :: remaining n (r + 1) := by
  unfold remaining
  rw [List.drop_eq_getElem_cons (l := List.finRange n) (i := r) (by simpa using h)]
  simp

noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.C (1000000 * (d + 1) ^ 3 + 100) * (Polynomial.X + 1) ^ 3

@[simp] theorem timePolynomial_eval (d L : Nat) :
    (timePolynomial d).eval L = (1000000 * (d + 1) ^ 3 + 100) * (L + 1) ^ 3 := by
  simp [timePolynomial]

@[simp] theorem finalTapes_input (input output : List Bool) : finalTapes input output .input = input := rfl
@[simp] theorem finalTapes_output (input output : List Bool) : finalTapes input output .output = output := rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineLazyTable

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineLazyTableRuntime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Canonical polynomial-time computation of the executable lazy preprocessing map.
The raw machine's retained original input is physically drained by the checked
canonical-output wrapper before it reaches the standard `haltList` endpoint.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineLazyTableRuntime

open Turing PCP
open MachineLazyTable (Tape Label )

/-- A fixed explicit list of every non-output tape, independent of input data. -/
def cleanupTapes : List Tape :=
  [.input, .source, .vertices, .darts, .fuel, .vertex, .reverse,
    .tail, .old, .relation, .scratch, .divided, .quotient, .newReverse, .rowBuffer]

end UniqueGamesTheorem.Foundations.Complexity.MachineLazyTableRuntime

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PreprocessingOverlayWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact stored-row and codec expansion of the executable overlay. Within
each vertex block, all original ports precede all expander ports. -/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayWords

open PortTables GraphTables PreprocessingOverlayTables
open Complexity

variable {n d e : Nat}

def oldReverseMap (d e j : Nat) : Nat := (d + e) * (j / d) + j % d
def expanderReverseMap (d e j : Nat) : Nat := (d + e) * (j / e) + d + j % e

end UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayWords

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineOverlayRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineOverlayRows

open Turing
open PCP.GraphTables PCP.PreprocessingOverlayWords

variable {K Λ A : Type} [DecidableEq K]

abbrev State (A : Type) (e : Nat) := MachinePortReindex.State A e

inductive Label (e : Nat)
  | loadStart | loadLoop | seedRelation
  | row (stage : MachineLazyRows.Label e)
  | drainOld | drainNew | drainRelation
  deriving DecidableEq, Fintype

/-- The row body's nine tapes retain their numbering; tape 9 is the stream. -/
def bodyIndex (i : Fin 9) : Fin 10 := i.castSucc

theorem bodyIndex_injective : Function.Injective bodyIndex := by
  intro i j h
  exact Fin.castSucc_injective 9 h

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

/-! The fixed-degree vertex loop has one finite label block per port, plus
one terminal boundary. The stored row values do not occur in its program. -/

abbrev VertexLabel (e : Nat) := Fin (e + 1) × Option (Label e)

def valueBound (d e B : Nat) : Nat := (d + e) * B + B + d

theorem value_le (d e j B : Nat) (hj : j ≤ B) :
    MachinePortReindex.value e (d + e) d j ≤ valueBound d e B := by
  have hdiv := (Nat.div_le_self j e).trans hj
  have hmod := (Nat.mod_le j e).trans hj
  have hmul := Nat.mul_le_mul_left (d + e) hdiv
  unfold MachinePortReindex.value valueBound
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachineOverlayRows

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineOverlayTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineOverlayTable

variable {AmbientState : Type}

open Turing
open PCP PCP.GraphTables PCP.PreprocessingOverlayWords
open MachineCloudPadding

abbrev Tape := Fin 5 ⊕ Fin 12

def graphArchive : Tape := .inl 0
def graphStream : Tape := .inl 1
def scratch : Tape := .inl 2
def vertexCount : Tape := .inl 3
def dartCount : Tape := .inl 4
def expanderArchive : Tape := .inr 0
def expanderStream : Tape := .inr 1
def fuel : Tape := .inr 2
def vertex : Tape := .inr 3
def tail : Tape := .inr 4
def oldReverse : Tape := .inr 5
def relation : Tape := .inr 6
def dividedCopy : Tape := .inr 7
def quotient : Tape := .inr 8
def newReverse : Tape := .inr 9
def rowBuffer : Tape := .inr 10
def output : Tape := .inr 11

def oldTapes : Fin 10 → Tape :=
  ![tail, oldReverse, relation, scratch, dividedCopy, quotient, newReverse,
    output, rowBuffer, graphStream]

def expanderTapes : Fin 10 → Tape :=
  ![tail, oldReverse, relation, scratch, dividedCopy, quotient, newReverse,
    output, rowBuffer, expanderStream]

theorem oldTapes_injective : Function.Injective oldTapes := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [oldTapes, tail, oldReverse, relation, scratch, dividedCopy, quotient,
      newReverse, output, rowBuffer, graphStream]

theorem expanderTapes_injective : Function.Injective expanderTapes := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [expanderTapes, tail, oldReverse, relation, scratch, dividedCopy, quotient,
      newReverse, output, rowBuffer, expanderStream]

inductive MainLabel (d e : Nat)
  | copyHFirst | copyHSecond
  | countSeed | countScan | countRestore
  | headerSeed | headerScan | headerRestore
  | fuelSeed | fuelScan | fuelRestore | vertexSeed | guard
  | old (stage : MachineLazyRows.VertexLabel d)
  | tailSeed | tailScan | tailRestore
  | expander (stage : MachineOverlayRows.VertexLabel e)
  | drainTail | increment
  | drainFuel | drainVertex | drainVertexCount | drainDartCount
  deriving DecidableEq, Fintype

abbrev Label (d e : Nat) := MachineTableSplit.Label ⊕ MainLabel d e

def next {oldDegree expanderDegree : Nat} (l : MainLabel oldDegree expanderDegree) :
    Option (Label oldDegree expanderDegree) := some (.inr l)

def extraTapes (rawH : List Bool) : Fin 12 → List Bool :=
  fun i => if i = 0 then rawH else []

def splitView : Tape → Option (Fin 5)
  | .inl i => some i
  | .inr _ => none

def combine (left : Fin 5 → List Bool) (rawH : List Bool) : Tape → List Bool
  | .inl i => left i
  | .inr i => extraTapes rawH i

def initialTapes (graph rawH : List Bool) : Tape → List Bool :=
  combine (MachineTableSplit.initialTapes graph) rawH

theorem placedTapes (left : Fin 5 → List Bool) (rawH : List Bool) :
    Placement.tapes splitView left (initialTapes [] rawH) = combine left rawH := by
  funext k
  cases k <;> rfl

/-- Every unnamed work tape is empty at these phase boundaries. -/
def memory (g h gs hs n m f v t out : List Bool) : Tape → List Bool
  | .inl i => ![g, gs, [], n, m] i
  | .inr i => ![h, hs, f, v, t, [], [], [], [], [], [], out] i

@[simp] theorem memory_graphArchive (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out graphArchive = g := rfl
@[simp] theorem memory_graphStream (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out graphStream = gs := rfl
@[simp] theorem memory_scratch (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out scratch = [] := rfl
@[simp] theorem memory_vertexCount (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out vertexCount = n := rfl
@[simp] theorem memory_dartCount (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out dartCount = m := rfl
@[simp] theorem memory_expanderArchive (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out expanderArchive = h := rfl
@[simp] theorem memory_expanderStream (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out expanderStream = hs := rfl
@[simp] theorem memory_fuel (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out fuel = f := rfl
@[simp] theorem memory_vertex (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out vertex = v := rfl
@[simp] theorem memory_tail (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out tail = t := rfl
@[simp] theorem memory_oldReverse (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out oldReverse = [] := rfl
@[simp] theorem memory_relation (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out relation = [] := rfl
@[simp] theorem memory_dividedCopy (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out dividedCopy = [] := rfl
@[simp] theorem memory_quotient (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out quotient = [] := rfl
@[simp] theorem memory_newReverse (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out newReverse = [] := rfl
@[simp] theorem memory_rowBuffer (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out rowBuffer = [] := rfl
@[simp] theorem memory_output (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out output = out := rfl

@[simp] theorem update_output (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) output x = memory g h gs hs n m f v t x := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_expanderStream (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) expanderStream x =
      memory g h gs x n m f v t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_graphStream (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) graphStream x =
      memory g h x hs n m f v t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_fuel (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) fuel x = memory g h gs hs n m x v t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_vertex (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) vertex x = memory g h gs hs n m f x t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_tail (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) tail x = memory g h gs hs n m f v x out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_vertexCount (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) vertexCount x = memory g h gs hs x m f v t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_dartCount (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) dartCount x = memory g h gs hs n x f v t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

def preparationSteps (n : Nat) (h : List Bool) : Nat := 2 * (h.length + 1) + 6 * (n + 1) + 4

def remaining {n : Nat} (block : Fin n → List Bool) (k : Nat) : List Bool :=
  ((List.ofFn block).drop k).flatten
def emittedPrefix {n : Nat} (block : Fin n → List Bool) (k : Nat) : List Bool :=
  ((List.ofFn block).take k).flatten

theorem remaining_step {n : Nat} (block : Fin n → List Bool) (v : Fin n) :
    remaining block v.val = block v ++ remaining block (v.val + 1) := by
  have hs := List.getElem_cons_drop (as := List.ofFn block) (i := v.val)
    (by simpa only [List.length_ofFn] using v.isLt)
  unfold remaining
  rw [← hs]
  simp only [List.flatten_cons, List.getElem_ofFn, Fin.eta]

theorem prefix_step {n : Nat} (block : Fin n → List Bool) (v : Fin n) :
    emittedPrefix block (v.val + 1) = emittedPrefix block v.val ++ block v := by
  unfold emittedPrefix
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_ofFn] using v.isLt)]
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.getElem_ofFn, Fin.eta]

@[simp] theorem remaining_zero {n : Nat} (block : Fin n → List Bool) :
    remaining block 0 = (List.ofFn block).flatten := by simp [remaining]
@[simp] theorem remaining_end {n : Nat} (block : Fin n → List Bool) :
    remaining block n = [] := by
  unfold remaining
  rw [List.drop_eq_nil_iff.mpr (by simpa only [List.length_ofFn] using (Nat.le_refl n)), List.flatten_nil]
@[simp] theorem prefix_zero {n : Nat} (block : Fin n → List Bool) : emittedPrefix block 0 = [] := by
  simp [emittedPrefix]
@[simp] theorem prefix_end {n : Nat} (block : Fin n → List Bool) :
    emittedPrefix block n = (List.ofFn block).flatten := by
  unfold emittedPrefix
  have ht : (List.ofFn block).take n = List.ofFn block :=
    List.take_of_length_le (by simpa only [List.length_ofFn] using (Nat.le_refl n))
  rw [ht]

def cleanupSteps (n m : Nat) : Nat := 2 * n + m + 8

theorem flatMap_length_le {α : Type*} (items : List α) (f : α → List Bool)
    (B : Nat) (bounded : ∀ x ∈ items, (f x).length ≤ B) :
    (items.flatMap f).length ≤ items.length * B := by
  induction items with
  | nil => simp
  | cons x xs ih =>
      have hx := bounded x (by simp)
      have ht := ih (fun y hy => bounded y (by simp [hy]))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [Nat.add_mul, Nat.one_mul]
      omega

theorem flatten_length_le (items : List (List Bool)) (B : Nat)
    (bounded : ∀ x ∈ items, x.length ≤ B) : items.flatten.length ≤ items.length * B := by
  simpa only [List.flatMap_id] using flatMap_length_le items id B bounded

def oldSize (d e n : Nat) : Nat := MachineLazyRows.rowSizeBound (d + e) 0 n (n * d)

end UniqueGamesTheorem.Foundations.Complexity.MachineOverlayTable

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachinePaddedExpanderFamilyBoundsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily

open Turing

section TableCoordinates

open PCP.ExpanderTables PCP.ExpanderRowControl

abbrev fixedDegree := PCP.Expanders.baseDegree

open MachineCloudPadding PCP.ExpanderTableWords

end TableCoordinates


/-!
# Actual requested-size to expander-table computation

One finite program physically computes the padding level and then constructs
the complete corresponding rotation table. The level output of the first
phase is the input tape of the second phase. The actual execution preserves
the request, retains the padded size, and has a fixed polynomial time bound
in the unary request length.
-/

open MachineCloudPadding

end UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachinePaddingRowsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddingRows

open Turing

inductive Control
  | initialize_ | guard | bump
  deriving DecidableEq

protected abbrev Control.enumList : List Control := [.initialize_, .guard, .bump]

protected theorem Control.enumList_nodup : Control.enumList.Nodup := by decide

instance instFintypeControl : Fintype Control where
  elems := ⟨Control.enumList, Control.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape := Fin 6 ⊕ Unit
abbrev Label (d : Nat) := MachineDummyRows.Label d ⊕ Control
abbrev State := (Unit × Option Bool) × Unit

def bodyEntry (d : Nat) (hd : 0 < d) : Label d :=
  .inl (MachineDummyRows.rowLabel ⟨0, hd⟩ .relationRead)

end UniqueGamesTheorem.Foundations.Complexity.MachinePaddingRows

/-! Polynomial bounds for the actual outer padding-loop recurrence. No
execution or cost premise is introduced: the recurrence is the one matched
to the concrete machine by `MachinePaddingRows.loopTrace`. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddingBounds

/-- A common row-size bound for all remaining vertices and ports. -/
def rowBound (d v e count : Nat) : Nat := v + count + e + (count + 1) * d + 8194

/-- This bound is invariant when one vertex and its `d` reverse indices
have been consumed from the remaining outer-loop count. -/
theorem rowBound_next (d v e count : Nat) :
    rowBound d (v + 1) (e + d) count = rowBound d v e (count + 1) := by
  simp only [rowBound, Nat.add_mul, Nat.one_mul]
  omega

theorem blockRow_le_rowBound (d v e count : Nat) :
    v + e + d + 8194 ≤ rowBound d v e (count + 1) := by
  simp only [rowBound, Nat.add_mul, Nat.one_mul]
  omega

def rowCap (d size : Nat) : Nat := size + (size + 1) * d + 8194

noncomputable def rowPolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.X + (Polynomial.X + 1) * Polynomial.C d + Polynomial.C 8194

/-- A cubic polynomial for fixed degree, including the final zero-fuel
guard. The one-time relation initializer can be accounted for separately. -/
noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.X * (Polynomial.C d *
    (Polynomial.C 4 * rowPolynomial d +
      Polynomial.C 2 * (Polynomial.X + Polynomial.X * Polynomial.C d * rowPolynomial d) +
      Polynomial.C 10) + Polynomial.C 2) + 1

end UniqueGamesTheorem.Foundations.Complexity.MachinePaddingBounds

/-! Polynomial-time certificate for the actual varying-length padding loop,
including its one-time relation initialization. The input vertex, reverse
index, fuel, and accumulated output are all measured as physically stored
bits. This is a reusable stage of the graph-table transformation. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddingCertificate

open MachinePaddingRows

noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  MachinePaddingBounds.timePolynomial d + 1

end UniqueGamesTheorem.Foundations.Complexity.MachinePaddingCertificate

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PreprocessingPaddingWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Exact serialization of whole-vertex padding

The original dart rows remain in their original order, with every old tail,
reverse index, and relation bit unchanged. The suffix is exactly the bit stream
emitted by the checked dummy-vertex machine, starting at vertex `n` and dart
`n*d`. This is an equality for the actual table codec, with no runtime premise.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingWords

open Complexity PortTables

variable {n m d : Nat}

/-- Mixed-radix row order is vertex-major, then increasing port order. -/
theorem flatten_ofFn_rowIndex {α : Type*} (f : Fin (n * d) → List α) :
    (List.ofFn f).flatten =
      (List.ofFn (fun v : Fin n =>
        (List.ofFn (fun p : Fin d => f (rowIndex n d (v, p)))).flatten)).flatten := by
  rw [List.ofFn_mul, List.flatten_flatten, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext v
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext p
  apply congrArg f
  apply Fin.ext
  simp only [rowIndex_val, Nat.mul_comm, Nat.add_comm]

end UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingWords

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineVertexPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Vertex padding from the original serialized port graph

Header counters, the geometric padding count, and the initial row buffer
are generated by physical tape operations before the checked row emitter.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineVertexPadding

open Turing
open UniqueGamesTheorem.Foundations.PCP
open MachineCloudPadding

inductive Tape
  | original | output | vertex | edge | power | level | fuel | relation
  | scratch | work | saved | product | rowWork | rowSpare
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.original, .output, .vertex, .edge, .power, .level,
  .fuel, .relation, .scratch, .work, .saved, .product, .rowWork, .rowSpare]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Label (d : Nat)
  | splitCode (l : MachineTableSplit.Label)
  | powerCode (l : MachineCeilingPower.Label)
  | dartSeed | dartScan | dartRestore | vertexSeed | vertexScan | vertexRestore
  | copyFirst | copySecond | subtractCode (l : MachineCloudPadding.Label)
  | rowsCode (l : MachinePaddingRows.Label d)
  | cleanVertex | cleanEdge | cleanPower | cleanRelation | cleanFuel
  deriving DecidableEq, Fintype

abbrev Alphabet (_ : Tape) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

/-- All unnamed work stacks are empty at the phase boundaries below. -/
def memory (input output vertex edge power level fuel relation : List Bool) : Tape → List Bool
  | .original => input
  | .output => output
  | .vertex => vertex
  | .edge => edge
  | .power => power
  | .level => level
  | .fuel => fuel
  | .relation => relation
  | _ => []

@[simp] theorem update_output (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .output x = memory a x c d e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_vertex (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .vertex x = memory a b x d e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_edge (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .edge x = memory a b c x e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_power (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .power x = memory a b c d x f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_fuel (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .fuel x = memory a b c d e f x h := by
  funext k; cases k <;> rfl
@[simp] theorem update_relation (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .relation x = memory a b c d e f g x := by
  funext k; cases k <;> rfl

def powerTape : MachineCeilingPower.Tape → Tape
  | .input => .vertex
  | .work => .work
  | .power => .power
  | .saved => .saved
  | .level => .level
  | .fuel => .fuel
  | .spare => .scratch
  | .product => .product
def powerView : Tape → Option MachineCeilingPower.Tape
  | .vertex => some .input
  | .work => some .work
  | .power => some .power
  | .saved => some .saved
  | .level => some .level
  | .fuel => some .fuel
  | .scratch => some .spare
  | .product => some .product
  | _ => none

theorem powerView_left (k : MachineCeilingPower.Tape) : powerView (powerTape k) = some k := by
  cases k <;> rfl
theorem powerView_right (j : Tape) (k : MachineCeilingPower.Tape)
    (h : powerView j = some k) : powerTape k = j := by
  cases j <;> cases k <;> simp_all [powerView, powerTape]

def subtractTape : MachineCloudPadding.Tape → Tape
  | .table => .original
  | .query => .output
  | .count => .vertex
  | .work => .work
  | .scratch => .saved
  | .spare => .scratch
  | .power => .fuel
  | .level => .level
  | .fuel => .product
  | .product => .rowSpare
def subtractView : Tape → Option MachineCloudPadding.Tape
  | .original => some .table
  | .output => some .query
  | .vertex => some .count
  | .work => some .work
  | .saved => some .scratch
  | .scratch => some .spare
  | .fuel => some .power
  | .level => some .level
  | .product => some .fuel
  | .rowSpare => some .product
  | _ => none

theorem subtractView_left (k : MachineCloudPadding.Tape) :
    subtractView (subtractTape k) = some k := by cases k <;> rfl
theorem subtractView_right (j : Tape) (k : MachineCloudPadding.Tape)
    (h : subtractView j = some k) : subtractTape k = j := by
  cases j <;> cases k <;> simp_all [subtractView, subtractTape]

def rowTape : MachinePaddingRows.Tape → Tape
  | .inl k => (![.vertex, .edge, .relation, .rowWork, .output, .rowSpare] : Fin 6 → Tape) k
  | .inr _ => .fuel
def rowView : Tape → Option MachinePaddingRows.Tape
  | .vertex => some (.inl 0)
  | .edge => some (.inl 1)
  | .relation => some (.inl 2)
  | .rowWork => some (.inl 3)
  | .output => some (.inl 4)
  | .rowSpare => some (.inl 5)
  | .fuel => some (.inr ())
  | _ => none

theorem rowView_left (k : MachinePaddingRows.Tape) : rowView (rowTape k) = some k := by
  rcases k with k | k
  · fin_cases k <;> rfl
  · cases k; rfl
theorem rowView_right (j : Tape) (k : MachinePaddingRows.Tape)
    (h : rowView j = some k) : rowTape k = j := by
  rcases k with k | k
  · cases j <;> fin_cases k <;> simp_all [rowView, rowTape]
  · cases k; cases j <;> simp_all [rowView, rowTape]

def rowStateEquiv (σ : Type) : (MachinePaddingRows.State × (σ × Bool)) ≃ State σ where
  toFun x := (x.2, x.1.1.2)
  invFun x := ((((), x.2), ()), x.1)
  left_inv := by rintro ⟨⟨⟨⟨⟩, r⟩, ⟨⟩⟩, a⟩; rfl
  right_inv := by rintro ⟨a, r⟩; rfl

theorem appendTrace {α : Type} (f : α → α) {a b : Nat} {x y z : α}
    (hs : f^[a] x = y) (ht : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, hs, ht]

theorem powerTapes (input output vertex edge power level : List Bool) :
    Placement.tapes powerView (MachineCeilingPower.memory vertex [] power [] level [] [] [])
      (memory input output [] edge [] [] [] []) = memory input output vertex edge power level [] [] := by
  funext k; cases k <;> rfl

theorem subtractTapes (input output vertex edge power level fuel : List Bool) :
    Placement.tapes subtractView
      (MachineCloudPadding.memory input output vertex [] [] [] fuel level [] [])
      (memory [] [] [] edge power [] [] []) =
      memory input output vertex edge power level fuel [] := by
  funext k; cases k <;> rfl

def cleanupTime (d m : Nat) : Nat := 2 * m + m * d + 8201

def intermediateCoefficient (d : Nat) : Nat := (d + 2) * ExpanderFamily.growth + 8

noncomputable def intermediatePolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.C (intermediateCoefficient d) * (Polynomial.X + 1)

noncomputable def otherPolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.C (ExpanderFamily.growth + 8) * (Polynomial.X + 1) ^ 2 +
    Polynomial.C ((d + 8) * ExpanderFamily.growth + 24) * (Polynomial.X + 1) + 8222

noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  otherPolynomial d + (MachinePaddingCertificate.timePolynomial d).comp (intermediatePolynomial d)

end UniqueGamesTheorem.Foundations.Complexity.MachineVertexPadding

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachinePaddedOverlay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Physical composition of vertex padding, expander generation, and overlay

The level produced by vertex padding is the family machine's actual input
stack. The two resulting archives are the overlay machine's actual archive
stacks. Static tape placement and finite-state framing preserve the original
input; no copying or recomputation is hidden in a phase boundary.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlay

open Turing MachineCloudPadding
open PCP

abbrev baseDegree := Expanders.baseDegree
abbrev overlayDegree := PreprocessingRegularTables.internalDegree

variable {d : Nat}

/-- The actual padded vertex count is linear in the original encoded size. -/
noncomputable def sizePolynomial : Polynomial Nat :=
  Polynomial.C ExpanderFamily.growth * (Polynomial.X + 1)

/-- Full unary lengths of both physical archives, including all graph
predicate entries, all delimiters, and all expander reverse addresses. -/
noncomputable def archivePolynomial (d : Nat) : Polynomial Nat :=
  let s := sizePolynomial
  s + s * Polynomial.C d + 2 +
    (s * Polynomial.C d) * (s + s * Polynomial.C d + 8192) +
    (s * Polynomial.C overlayDegree) * (s * Polynomial.C overlayDegree + 1)

end UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlay

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineProductSeed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite literal setup sequence. Its list is fixed with the machine; no
input word or unbounded address is stored in finite control. -/

namespace UniqueGamesTheorem.Explicit.MachineProductSeed

open Turing
open UniqueGamesTheorem.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K]

abbrev Command (K : Type) := K × List Bool
abbrev LocalLabel (_ : Command K) := Unit
abbrev Label (commands : List (Command K)) := MachineFiniteSequence.Label LocalLabel commands

def entry (commands : List (Command K)) (labels : Label commands → Λ) (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry LocalLabel (fun _ => ()) commands labels exit

def result (command : Command K) (base : K → List Bool) : K → List Bool :=
  Function.update base command.1 (command.2 ++ base command.1)

def finalTapes (commands : List (Command K)) (base : K → List Bool) : K → List Bool :=
  MachineFiniteSequence.resultOf result commands base

@[simp] theorem sequence_steps (commands : List (Command K)) (base : K → List Bool) :
    MachineFiniteSequence.steps result (fun _ _ => 1) commands base = commands.length := by
  induction commands generalizing base with
  | nil => rfl
  | cons command commands ih =>
    simp only [MachineFiniteSequence.steps, ih, List.length_cons]
    omega

theorem finalTapes_frame (commands : List (Command K)) (base : K → List Bool)
    (k : K) (outside : ∀ command ∈ commands, k ≠ command.1) :
    finalTapes commands base k = base k := by
  induction commands generalizing base with
  | nil => rfl
  | cons command commands ih =>
    change finalTapes commands (result command base) k = base k
    rw [ih _ (fun c hc => outside c (by simp [hc]))]
    exact Function.update_of_ne (outside command (by simp)) _ _

theorem finalTapes_field (commands : List (Command K))
    (nodup : (commands.map Prod.fst).Nodup) (base : K → List Bool)
    (command : Command K) (member : command ∈ commands) :
    finalTapes commands base command.1 = command.2 ++ base command.1 := by
  induction commands generalizing base with
  | nil => simp at member
  | cons first rest ih =>
    simp only [List.map_cons, List.nodup_cons] at nodup
    rcases List.mem_cons.mp member with rfl | member
    · change finalTapes rest (result command base) command.1 = _
      rw [finalTapes_frame rest _ command.1]
      · simp [result]
      · intro c hc he
        exact nodup.1 (List.mem_map.mpr ⟨c, hc, he.symm⟩)
    · have ne : command.1 ≠ first.1 := by
        intro h
        exact nodup.1 (List.mem_map.mpr ⟨command, member, h⟩)
      change finalTapes rest (result first base) command.1 = _
      rw [ih nodup.2 _ member, result, Function.update_of_ne ne]

end UniqueGamesTheorem.Explicit.MachineProductSeed

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineProductProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Explicit.MachineProductProgram

open Turing
open UniqueGamesTheorem.Foundations
open Complexity Hastad


abbrev Extra (t : Nat) := Fin 10 ⊕ Fin (t + 1)
abbrev State := MachineHorner.State Unit

end UniqueGamesTheorem.Explicit.MachineProductProgram

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineProductHeadersFrameLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! Concrete header and initialized work-tape frames for the product machine. -/



/-! Three actual header reads for the fixed-alphabet, fixed-power product
machine. The constraint table stays in its original order on the formula tape. -/



/-! Actual literal initialization of the finitely many product power digits. -/

namespace UniqueGamesTheorem.Explicit.MachineProductHeaders

open Turing
open UniqueGamesTheorem.Foundations Target Complexity Hastad
open MachineProductProgram


noncomputable section




/-! Complete actual initialization of the independent-product machine. -/





def timePolynomial (t : Nat) : Polynomial Nat :=
  Polynomial.X + 3 + Polynomial.C (t + 2) +
    Polynomial.C 2 * (MachineProductPower.timePolynomial t).comp (Polynomial.X + 1) + 1 +
    Polynomial.C t * (Polynomial.C 2 * Polynomial.X + 6) + 1

end
end UniqueGamesTheorem.Explicit.MachineProductHeaders



/-! Whole tuple traversal of the concrete product program. The odometer theorem
is instantiated by the proved actual row trace, not by an assumed row machine. -/



/-! Exact final cleanup and binary-output identification for the product
controller. The final runtime bound is derived from actual stack lengths. -/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineProductRuntime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! The complete explicit product computation. Every execution phase is supplied
by the actual controller; the cleanup bound follows from the space reached by
its actual prefix. The exponent and alphabet enter only the fixed program. -/

namespace UniqueGamesTheorem.Explicit.MachineProductRuntime

open Turing
open UniqueGamesTheorem.Foundations Target Complexity Hastad
open MachineProductProgram


noncomputable section

def loopPolynomial (q t : Nat) : Polynomial Nat :=
  (Polynomial.C (q ^ t + 2) * MachineProductBounds.fieldPolynomial t +
    Polynomial.C (2 * t)) * Polynomial.X ^ t

def prefixPolynomial (q t : Nat) : Polynomial Nat :=
  MachineProductHeaders.timePolynomial t + loopPolynomial q t

end

end UniqueGamesTheorem.Explicit.MachineProductRuntime

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularDummyRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual inherited-row emission for a dummy vertex

The fixed program preserves the physical unary vertex index on tape zero,
computes its inherited reverse index on tape one, invokes the actual one-port
dummy-row emitter, and drains the computed index and fixed true relation.
Tape four accumulates output. Tapes one, two, three, and five are empty at both
boundaries. The degree is fixed program data, not an input-dependent control
parameter.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularDummyRow

open Turing PCP.GraphTables

abbrev Tape := Fin 6
abbrev Alphabet (_ : Tape) := Bool
abbrev State (σ : Type) := σ × Option Bool

inductive Label
  | affine (stage : MachineUnaryAffineAt.Label)
  | row (stage : MachineDummyRows.Label 1)
  | reverse | relation
  deriving DecidableEq, Fintype

def reverseIndex (q x : Nat) : Nat := (q + 1) * x + q

theorem join_trace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

/-- For each fixed degree, the exact cost is linear in index and prior output. -/
def timeBound (q x outputLength : Nat) : Nat :=
  (5 * q + 11) * x + 2 * outputLength + 5 * q + 40986

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularDummyRow

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Materializing a cloud rotor inside the regularization machine

Core tape 4 contains the unary cloud size and core tape 7 receives the complete
forward rotor table. The actual family computation runs on private tapes;
three retained unary words are then physically drained. All other core tapes
are preserved and all private tapes are empty on return.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily

open Turing
open MachineCloudPadding

abbrev CoreTape := Fin 27

theorem appendTrace {α : Type} (f : α → α) {a b : Nat} {x y z : α}
    (hs : f^[a] x = y) (ht : f^[b] y = z) : f^[a+b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, hs, ht]

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineUnaryLessAtLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical comparison of two unary fields. Matched true bits are saved on
two empty scratch stacks. The first delimiter determines the comparison, then
both saved prefixes are restored. All input suffixes and other tapes survive. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

/-- Slots 0 and 1 are the operands; slots 2 and 3 are their saved prefixes. -/
def tapes (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update (Function.update base
    (slots 0) left) (slots 1) right) (slots 2) savedLeft) (slots 3) savedRight

@[simp] theorem tapes_left (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 0) = left := by
  simp [tapes, slots.injective.eq_iff]

@[simp] theorem tapes_right (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 1) = right := by
  simp [tapes, slots.injective.eq_iff]

@[simp] theorem tapes_savedLeft (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 2) = savedLeft := by
  simp [tapes, slots.injective.eq_iff]

@[simp] theorem tapes_savedRight (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 3) = savedRight := by
  simp [tapes]

def stop (result : Bool) (restoreLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .load (fun s => ((s.1.1, result), none)) (.goto fun _ => restoreLabel)

def scan (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .peek (slots 0) (fun s head => (s.1, head))
    (.branch (fun s => s.2.getD false)
      (.peek (slots 1) (fun s head => (s.1, head))
        (.branch (fun s => s.2.getD false)
          (.pop (slots 0) (fun s _ => s)
            (.pop (slots 1) (fun s _ => s)
              (.push (slots 2) (fun _ => true)
                (.push (slots 3) (fun _ => true) (.goto fun _ => scanLabel)))))
          (stop false restoreLabel)))
      (.peek (slots 1) (fun s head => (s.1, head))
        (.branch (fun s => s.2.getD false)
          (stop true restoreLabel) (stop false restoreLabel))))

inductive Label where
  | scan
  | restoreLeft
  | restoreRight
  deriving DecidableEq

instance instFintypeLabel : Fintype Label where
  elems := { .scan, .restoreLeft, .restoreRight }
  complete l := by cases l <;> simp

def steps (a b : Nat) : Nat := 3 * (min a b + 1)

end UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt

/-!
Actual unary-guard iteration for a logarithmic number of rounds. Semantic
cardinality grows by a fixed linear factor. A separate encoding polynomial
bounds each intermediate word; it is never iterated as a size recurrence.
The body hypotheses are individual executions of the supplied finite program.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.PCPIterationMachine

open Turing
open MachineCountedLoop

def rounds (n : Nat) : Nat := n.log2 + 1

theorem rounds_le (n : Nat) : rounds n ≤ n + 1 :=
  Nat.add_le_add_right (Nat.log2_le_self n) 1

theorem two_pow_rounds_le (n : Nat) : 2 ^ rounds n ≤ 2 * (n + 1) := by
  by_cases hn : n = 0
  · subst n; decide
  · have h := Nat.log2_self_le hn
    simp only [rounds, pow_succ]
    omega

/-- The exponent is a fixed growth constant, independent of the input. -/
theorem growth_pow_rounds_le (growth n : Nat) :
    growth ^ rounds n ≤ (2 * (n + 1)) ^ growth := by
  calc
    growth ^ rounds n ≤ (2 ^ growth) ^ rounds n :=
      Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self (n := growth))) _
    _ = (2 ^ rounds n) ^ growth := by simp only [← pow_mul, Nat.mul_comm]
    _ ≤ (2 * (n + 1)) ^ growth := Nat.pow_le_pow_left (two_pow_rounds_le n) growth

def sizeEnvelope (growth n : Nat) : Nat := (n + 1) * (2 * (n + 1)) ^ growth

/-- This recurrence concerns semantic cardinality, not unary encoding length. -/
theorem semanticSize_geometric (sizes : Nat → Nat) (growth n : Nat)
    (initialBound : sizes 0 ≤ n + 1)
    (growthBound : ∀ i, i < rounds n → sizes (i + 1) ≤ growth * sizes i)
    (i : Nat) (hi : i ≤ rounds n) : sizes i ≤ (n + 1) * growth ^ i := by
  induction i with
  | zero => simpa only [pow_zero, Nat.mul_one] using initialBound
  | succ i ih =>
    have ilt : i < rounds n := by omega
    calc
      sizes (i + 1) ≤ growth * sizes i := growthBound i ilt
      _ ≤ growth * ((n + 1) * growth ^ i) :=
        Nat.mul_le_mul_left growth (ih (by omega))
      _ = (n + 1) * growth ^ (i + 1) := by rw [pow_succ]; ac_rfl

theorem semanticSize_bound (sizes : Nat → Nat) (growth n : Nat)
    (growthPositive : 0 < growth)
    (initialBound : sizes 0 ≤ n + 1)
    (growthBound : ∀ i, i < rounds n → sizes (i + 1) ≤ growth * sizes i)
    (i : Nat) (hi : i ≤ rounds n) : sizes i ≤ sizeEnvelope growth n := by
  calc
    sizes i ≤ (n + 1) * growth ^ i :=
      semanticSize_geometric sizes growth n initialBound growthBound i hi
    _ ≤ (n + 1) * growth ^ rounds n :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right growthPositive hi)
    _ ≤ sizeEnvelope growth n :=
      Nat.mul_le_mul_left _ (growth_pow_rounds_le growth n)

noncomputable def sizePolynomial (growth : Nat) : Polynomial Nat :=
  (Polynomial.X + 1) * (2 * (Polynomial.X + 1)) ^ growth

@[simp] theorem sizePolynomial_eval (growth n : Nat) :
    (sizePolynomial growth).eval n = sizeEnvelope growth n := by
  simp [sizePolynomial, sizeEnvelope]

end UniqueGamesTheorem.Foundations.Complexity.PCPIterationMachine

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularInternalRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Physical construction of an internal regularization row

The input values belong on unary tapes. The cloud degree and the queried port
are the only arithmetic parameters fixed in finite control. The stored cloud
rotation supplies both the destination's local index and the return port.
The final row contains the full fixed equality predicate.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow

open Turing
open PCP

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

inductive FinishLabel
  | seedReturn | copyReturn | restoreReturn | affine | restoreTarget | equality
  | row (stage : MachineTableRows.Label)
  | clearReverse | clearEquality
  deriving DecidableEq, Fintype

/-- Tail, selected global target, returned port, scratch, reverse field,
equality field, row buffer, accumulated output. -/
def finishFields (tape : Fin 8 → K) : Fin 3 → K := fun i =>
  if i = 0 then tape 0 else if i = 1 then tape 4 else tape 5

omit [DecidableEq K] in
@[simp] theorem finishFields_zero (tape : Fin 8 → K) : finishFields tape 0 = tape 0 := rfl
omit [DecidableEq K] in
@[simp] theorem finishFields_one (tape : Fin 8 → K) : finishFields tape 1 = tape 4 := rfl
omit [DecidableEq K] in
@[simp] theorem finishFields_two (tape : Fin 8 → K) : finishFields tape 2 = tape 5 := rfl

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

inductive RotorLabel (q : Nat)
  | lookup (stage : MachineAffineLookup.Label)
  | initialize_ | divide | emit (r : Fin q)
  deriving DecidableEq, Fintype

def rotorLookupTapes (tape : Fin 8 → K) (j : Fin 5) : K :=
  tape ⟨j.val + 1, by omega⟩

omit [DecidableEq K] in
theorem rotorLookupTapes_injective (tape : Fin 8 → K) (h : Function.Injective tape) :
    Function.Injective (rotorLookupTapes tape) := by
  intro i j hij
  have hv := congrArg Fin.val (h hij)
  apply Fin.ext
  simpa only [Fin.val_mk, Nat.add_left_inj] using hv

omit [DecidableEq K] in
theorem rotorLookupTapes_outside (tape : Fin 8 → K) (h : Function.Injective tape)
    (i : Fin 5) : tape 0 ≠ rotorLookupTapes tape i := by
  intro he
  have hv := congrArg Fin.val (h he)
  change 0 = i.val + 1 at hv
  omega

inductive SelectExtraTape
  | localIndex | owner | cloudSize | prefixOffset | darts
  | savedLeft | savedRight | localWork | sizeWork
  deriving DecidableEq

abbrev SelectState (σ : Type) := MachineUnaryLessAt.State (σ × MachineCloudSelect.Phase)

def selectStateEquiv (σ : Type) : (MachineCloudSelect.State σ × Unit) ≃ SelectState σ where
  toFun s := (((s.1.1.1.1, s.1.2), s.1.1.1.2), s.1.1.2)
  invFun s := ((((s.1.1.1, s.1.2), s.2), s.1.1.2), ())
  left_inv s := by rcases s with ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, ⟨⟩⟩; rfl
  right_inv s := by rcases s with ⟨⟨⟨a, b⟩, c⟩, d⟩; rfl

inductive SelectCopy
  | oldLocal | oldOwner | dummyLocal | dummySize | dummyDifference
  deriving DecidableEq

protected abbrev SelectCopy.enumList : List SelectCopy := [.oldLocal, .oldOwner, .dummyLocal,
  .dummySize, .dummyDifference]

protected theorem SelectCopy.enumList_nodup : SelectCopy.enumList.Nodup := by decide

instance instFintypeSelectCopy : Fintype SelectCopy where
  elems := ⟨SelectCopy.enumList, SelectCopy.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive SelectAdd
  | prefixOffset | darts
  deriving DecidableEq

protected abbrev SelectAdd.enumList : List SelectAdd := [.prefixOffset, .darts]

protected theorem SelectAdd.enumList_nodup : SelectAdd.enumList.Nodup := by decide

instance instFintypeSelectAdd : Fintype SelectAdd where
  elems := ⟨SelectAdd.enumList, SelectAdd.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive SelectAddStage
  | scan | restore
  deriving DecidableEq

protected abbrev SelectAddStage.enumList : List SelectAddStage := [.scan, .restore]

protected theorem SelectAddStage.enumList_nodup : SelectAddStage.enumList.Nodup := by decide

instance instFintypeSelectAddStage : Fintype SelectAddStage where
  elems := ⟨SelectAddStage.enumList, SelectAddStage.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive SelectControl
  | compare (stage : MachineUnaryLessAt.Label)
  | choose
  | copy (kind : SelectCopy) (stage : MachineUnaryAffineAt.Label)
  | subtract
  | add (kind : SelectAdd) (stage : SelectAddStage)
  | cleanup (i : Fin 5)
  deriving DecidableEq, Fintype

abbrev SelectLabel := MachineCloudSelect.Label ⊕ SelectControl

def afterCleanup (i : Fin 5) : Option SelectLabel :=
  if h : i.val + 1 < 5 then some (.inr (.cleanup ⟨i.val + 1, h⟩)) else none

abbrev CoreTape := Fin 27

def dummySelectSteps (j k o m : Nat) : Nat :=
  (2 * (j + 1) + 1) + (2 * (k + 1) + 1) + (k + 1) +
    (2 * (j - k + 1) + 1) + 2 * (o + 1) + 2 * (m + 1) + (j + k + 7)

theorem dummySelectSteps_eq (j k o m : Nat) (h : k ≤ j) :
    dummySelectSteps j k o m = 5 * j + 2 * k + 2 * o + 2 * m + 21 := by
  unfold dummySelectSteps
  omega

/-- The fixed core rotor roles use the agreed reusable 27-tape frame. -/
def coreRotorTapes : Fin 8 → CoreTape := ![3, 7, 10, 11, 12, 9, 13, 14]

/-- Tail, selected destination, return port, scratch and emitted row fields. -/
def coreFinishTapes : Fin 8 → CoreTape := ![1, 15, 14, 9, 24, 25, 26, 8]

def coreCleanupTape : Fin 10 → CoreTape := ![10, 11, 12, 13, 14, 15, 9, 16, 17, 18]

/-- For fixed cloud degree q this is affine in the lengths and unary values
on the actual input tapes. All relation/cleanup constants are included. -/
def coreTimeBound (q graphLength rotorLength x v i k o m outputLength : Nat) : Nat :=
  (5 * q + 32) * rotorLength + 10 * graphLength + 2 * i + 13 * v + 5 * k +
    (5 * q + 10) * (m + o) + 4 * x + 2 * outputLength + 8 * q + 41066

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularMetadata
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

inductive Extra
  | padding | level
  deriving DecidableEq

protected abbrev Extra.enumList : List Extra := [.padding, .level]

abbrev Tape := Fin 27 ⊕ Extra
abbrev Alphabet (_ : Tape) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

variable {σ : Type}

/-- Boundary data is a specification of physical tape contents, never part
of the machine's finite control state. All eighteen core work tapes are empty. -/
structure Data where
  table : List Bool
  globalIndex : List Bool
  owner : List Bool
  localRank : List Bool
  count : List Bool
  offset : List Bool
  darts : List Bool
  rotor : List Bool
  output : List Bool
  padding : List Bool
  level : List Bool

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularMetadata

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineSingleOrbitProgramLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Physical postprocessing of the two-side address codec. The program reads
`2*C,q,m`, writes `C,q,m`, and replaces each row `u,C+v,table` by `u,v,table`.
Only the fixed alphabet size `q` occurs in finite control. All input-dependent
integers reside on unary tapes. Six Bool tapes suffice.
-/

namespace UniqueGamesTheorem.Explicit.MachineSingleOrbitProgram

open Turing
open UniqueGamesTheorem.Foundations.Complexity UniqueGamesTheorem.Foundations.Hastad
open UniqueGamesTheorem.Reduction

inductive Tape
  | input | capacity | saved | remaining | accumulator | output
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .capacity, .saved, .remaining,
  .accumulator, .output]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev State := Unit × Option Bool

def initialState : State := ((), none)

def clearKeys : List Tape := [.input, .capacity, .saved, .remaining]

inductive Label (q : Nat)
  | start | halfFirst | halfSecond | alphabet | count | guard
  | source | subtract | restore | target
  | table (completed : Fin (q + 1))
  | finishStart
  | finish (localLabel : SourceRuntimeFinish.Label clearKeys)
  deriving DecidableEq, Fintype

/-- Consume one complete unary field, including its delimiter, appending its
reverse to the output accumulator. All other tapes are unchanged. -/
def copyField {q : Nat} (loopLabel exitLabel : Label q) :
    TM2.Stmt (fun _ : Tape => Bool) (Label q) State :=
  .pop .input (fun state head => (state.1, head))
    (.push .accumulator (fun state => state.2.getD false)
      (.branch (fun state => state.2.getD false)
        (.goto fun _ => loopLabel)
        (.load (fun _ => initialState) (.goto fun _ => exitLabel))))

theorem accumulator_not_mem_clearKeys : Tape.accumulator ∉ clearKeys := by decide
theorem output_not_mem_clearKeys : Tape.output ∉ clearKeys := by decide

theorem clearKeys_covers (tape : Tape) (ha : tape ≠ .accumulator)
    (ho : tape ≠ .output) : tape ∈ clearKeys := by
  cases tape <;> simp_all [clearKeys]

end UniqueGamesTheorem.Explicit.MachineSingleOrbitProgram

/-! Exact streaming traces in the single-orbit postprocessor. -/

namespace UniqueGamesTheorem.Explicit.MachineSingleOrbitStreams

open Turing UniqueGamesTheorem.Foundations.Complexity
open MachineSingleOrbitProgram

def tapes (input capacity saved remaining accumulator output : List Bool) : Tape → List Bool
  | .input => input
  | .capacity => capacity
  | .saved => saved
  | .remaining => remaining
  | .accumulator => accumulator
  | .output => output

@[simp] theorem tapes_input (i c s r a o : List Bool) : tapes i c s r a o .input = i := rfl
@[simp] theorem tapes_capacity (i c s r a o : List Bool) : tapes i c s r a o .capacity = c := rfl
@[simp] theorem tapes_saved (i c s r a o : List Bool) : tapes i c s r a o .saved = s := rfl
@[simp] theorem tapes_remaining (i c s r a o : List Bool) : tapes i c s r a o .remaining = r := rfl
@[simp] theorem tapes_accumulator (i c s r a o : List Bool) : tapes i c s r a o .accumulator = a := rfl
@[simp] theorem tapes_output (i c s r a o : List Bool) : tapes i c s r a o .output = o := rfl

@[simp] theorem update_tapes (i c s r a o : List Bool) (t : Tape) (word : List Bool) :
    Function.update (tapes i c s r a o) t word =
      tapes (if t = .input then word else i) (if t = .capacity then word else c)
        (if t = .saved then word else s) (if t = .remaining then word else r)
        (if t = .accumulator then word else a) (if t = .output then word else o) := by
  cases t <;> funext k <;> cases k <;> simp [tapes]

def cfg {q : Nat} (label : Label q) (register : Option Bool)
    (i c s r a o : List Bool) : TM2.Cfg (fun _ : Tape => Bool) (Label q) State :=
  ⟨some label, ((), register), tapes i c s r a o⟩

end UniqueGamesTheorem.Explicit.MachineSingleOrbitStreams

/-! Physical unary header conversion, with an exact TM2 transition count. -/

/-! Actual subtraction of the right-side address offset, preserving the unary
capacity tape for every later edge. -/

/-! Complete ordered row traversal of the physical one-orbit postprocessor. -/

namespace UniqueGamesTheorem.Explicit.MachineSingleOrbitRows

open Turing UniqueGamesTheorem.Foundations.Complexity UniqueGamesTheorem.Foundations.Target
open MachineSingleOrbitProgram MachineSingleOrbitStreams

theorem joinTrace {α : Type*} {f : α → α} {x y z : α} {m n : Nat}
    (h : f^[m] x = y) (h' : f^[n] y = z) : f^[n + m] x = z := by
  rw [Function.iterate_add_apply, h, h']

end UniqueGamesTheorem.Explicit.MachineSingleOrbitRows

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineSingleOrbitFinishLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Actual tape cleanup, accumulator reversal, and halt for the one-orbit
postprocessor. The time bound is derived from an actual executed prefix. -/

/-!
Complete finite-machine postprocessing of the doubled address representation.
Every input field and row is physically processed. The time polynomial is in
the literal input bit length, including the final reversal and all tape cleanup.
-/

namespace UniqueGamesTheorem.Explicit.MachineSingleOrbitRuntime

open Turing UniqueGamesTheorem.Foundations.Complexity UniqueGamesTheorem.Foundations.Target
open MachineSingleOrbitProgram MachineSingleOrbitStreams
open MachineSingleOrbitRows

def prefixPolynomial : Polynomial Nat :=
  Polynomial.X + (Polynomial.X + Polynomial.C 4) * Polynomial.X + Polynomial.C 2

end UniqueGamesTheorem.Explicit.MachineSingleOrbitRuntime

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineSubdivisionDynamicRowsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Four-edge subdivision row emission with a physical permutation-table field.

The program depends only on the fixed identity table. Five saved endpoint words
and the entire final forward permutation table are physical tape contents. In
particular an input-dependent permutation is not inserted into a program label
or literal instruction. The last row is oriented `v → r`; for binary-vector
translations its table equals the inverse table of the original `u → v` edge.
-/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionDynamicRows

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Target
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Reduction

def tokens (identity : List Bool) : List (MachineFieldTemplate.Token 6) :=
  [.copy 0, .copy 1, .literal identity,
   .copy 2, .copy 1, .literal identity,
   .copy 2, .copy 3, .literal identity,
   .copy 4, .copy 3, .copy 5]

@[simp] theorem tokens_length (identity : List Bool) :
    (tokens identity).length = 12 := rfl

end UniqueGamesTheorem.Explicit.MachineSubdivisionDynamicRows

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionProgram

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad
open UniqueGamesTheorem.Reduction

inductive Tape
  | input | vertices | alphabetHeader | occurrences | remaining
  | newVertices | newEdges | u | v | middle | first | last
  | permutation | permutationReverse | affineScratch | copyScratch
  | accumulator | output
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .vertices, .alphabetHeader, .occurrences,
  .remaining, .newVertices, .newEdges, .u, .v, .middle, .first, .last, .permutation,
  .permutationReverse, .affineScratch, .copyScratch, .accumulator, .output]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev State := MachineFieldTemplate.State Unit

def initialState : State := (((), ()), none)

def headerField : Fin 3 → Tape
  | 0 => .vertices
  | 1 => .alphabetHeader
  | 2 => .occurrences

def rowField : Fin 6 → Tape
  | 0 => .u
  | 1 => .first
  | 2 => .middle
  | 3 => .last
  | 4 => .v
  | 5 => .permutation

def newHeaderField : Fin 2 → Tape
  | 0 => .newVertices
  | 1 => .newEdges

/-- Nine fixed affine passes initialize_ headers, the loop counter, and all three
private vertex indices. `none` means accumulate into the existing unary word. -/
structure InitOp where
  source : Tape
  destination : Tape
  coefficient : Nat
  seed : Option Nat

def initOp : Fin 9 → InitOp
  | 0 => ⟨.vertices, .newVertices, 1, some 0⟩
  | 1 => ⟨.occurrences, .newVertices, 3, none⟩
  | 2 => ⟨.occurrences, .newEdges, 4, some 0⟩
  | 3 => ⟨.vertices, .middle, 1, some 0⟩
  | 4 => ⟨.vertices, .first, 1, some 0⟩
  | 5 => ⟨.occurrences, .first, 1, none⟩
  | 6 => ⟨.vertices, .last, 1, some 1⟩
  | 7 => ⟨.occurrences, .last, 1, none⟩
  | 8 => ⟨.occurrences, .remaining, 1, some 0⟩

def clearKeys : List Tape :=
  [.input, .vertices, .alphabetHeader, .occurrences, .remaining,
   .newVertices, .newEdges, .u, .v, .middle, .first, .last,
   .permutation, .permutationReverse, .affineScratch, .copyScratch]

theorem clearKeys_covers (k : Tape) :
    k ∈ clearKeys ∨ k = .accumulator ∨ k = .output := by
  cases k <;> simp [clearKeys]

theorem accumulator_not_mem_clearKeys : Tape.accumulator ∉ clearKeys := by decide
theorem output_not_mem_clearKeys : Tape.output ∉ clearKeys := by decide

end UniqueGamesTheorem.Explicit.MachineSubdivisionProgram

/-! Actual cleanup, output reversal, and polynomial finishing overhead. -/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionFinish

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad
open MachineSubdivisionProgram

theorem covers (k : Tape) (ha : k ≠ .accumulator) (ho : k ≠ .output) :
    k ∈ clearKeys := by
  rcases clearKeys_covers k with h | h | h
  · exact h
  · exact False.elim (ha h)
  · exact False.elim (ho h)

end UniqueGamesTheorem.Explicit.MachineSubdivisionFinish

/-! Exact execution of the three input-header reads of subdivision. -/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionHeaders

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad
open MachineSubdivisionProgram

def inputTapes (bits : List Bool) : Tape → List Bool :=
  fun k => if k = .input then bits else []

end UniqueGamesTheorem.Explicit.MachineSubdivisionHeaders

/-! Physical header arithmetic and private-vertex initialization. -/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionInit

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Reduction
open MachineSubdivisionProgram

theorem source_ne_scratch (i : Fin 9) : (initOp i).source ≠ Tape.affineScratch := by
  fin_cases i <;> simp [initOp]

theorem source_ne_destination (i : Fin 9) : (initOp i).source ≠ (initOp i).destination := by
  fin_cases i <;> simp [initOp]

theorem scratch_ne_destination (i : Fin 9) : Tape.affineScratch ≠ (initOp i).destination := by
  fin_cases i <;> simp [initOp]

def sourceValue (n Q : Nat) : Fin 9 → Nat
  | 0 => n
  | 1 => Q
  | 2 => Q
  | 3 => n
  | 4 => n
  | 5 => Q
  | 6 => n
  | 7 => Q
  | 8 => Q

def beforeValue (n : Nat) : Fin 9 → Nat
  | 0 => 0
  | 1 => n
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => n
  | 6 => 0
  | 7 => n + 1
  | 8 => 0

def afterValue (n Q : Nat) (i : Fin 9) : Nat :=
  (initOp i).coefficient * sourceValue n Q i + (initOp i).seed.getD (beforeValue n i)

def stageCost (n Q : Nat) : Nat := 2 * (n + Q + 1) + 1

theorem sourceValue_le (n Q : Nat) (i : Fin 9) : sourceValue n Q i ≤ n + Q := by
  fin_cases i <;> simp [sourceValue]

end UniqueGamesTheorem.Explicit.MachineSubdivisionInit

/-! Literal output-header emission and the initial occurrence-loop frame. -/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineSubdivisionTableRead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Actual execution of the subdivision controller's full-table reader.
The reader consumes exactly the fixed number of zero-delimited table entries,
retains the unread input suffix, and reverses the saved table into forward order.
No table entry is stored in finite control; only the number of delimiters is.
-/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionTableRead

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Reduction
open MachineSubdivisionProgram

def tapes (base : Tape → List Bool) (input reversed : List Bool) : Tape → List Bool :=
  Function.update (Function.update base Tape.input input) Tape.permutationReverse reversed

@[simp] theorem tapes_input (base : Tape → List Bool) (input reversed : List Bool) :
    tapes base input reversed .input = input := by simp [tapes]

@[simp] theorem tapes_reverse (base : Tape → List Bool) (input reversed : List Bool) :
    tapes base input reversed .permutationReverse = reversed := by simp [tapes]

theorem update_input (base : Tape → List Bool) (input reversed replacement : List Bool) :
    Function.update (tapes base input reversed) .input replacement =
      tapes base replacement reversed := by
  funext k
  cases k <;> simp [tapes]

theorem update_reverse (base : Tape → List Bool) (input reversed replacement : List Bool) :
    Function.update (tapes base input reversed) .permutationReverse replacement =
      tapes base input replacement := by
  funext k
  cases k <;> simp [tapes]

def finalTapes (base : Tape → List Bool) (suffix bits : List Bool) : Tape → List Bool :=
  Function.update (tapes base suffix []) .permutation (bits ++ base .permutation)

@[simp] theorem finalTapes_input (base : Tape → List Bool) (suffix bits : List Bool) :
    finalTapes base suffix bits .input = suffix := by simp [finalTapes]

@[simp] theorem finalTapes_reverse (base : Tape → List Bool) (suffix bits : List Bool) :
    finalTapes base suffix bits .permutationReverse = [] := by simp [finalTapes]

@[simp] theorem finalTapes_permutation (base : Tape → List Bool) (suffix bits : List Bool) :
    finalTapes base suffix bits .permutation = bits ++ base .permutation := by simp [finalTapes]

end UniqueGamesTheorem.Explicit.MachineSubdivisionTableRead

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineSubdivisionBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
One whole occurrence iteration of the actual subdivision controller.
The proved trace includes both endpoint loads, the dynamic full-table reader,
the four-row template, all three local drains, and private-index increments.
-/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionBody

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad
open UniqueGamesTheorem.Reduction
open MachineSubdivisionProgram

def incrementTapes (base : Tape → List Bool) : Tape → List Bool :=
  Function.update
    (Function.update (Function.update base .middle (true :: base .middle))
      .first (true :: true :: base .first))
    .last (true :: true :: base .last)

theorem rowField_ne_scratch (j : Fin 6) : rowField j ≠ Tape.copyScratch := by
  fin_cases j <;> decide

theorem rowField_ne_accumulator (j : Fin 6) : rowField j ≠ Tape.accumulator := by
  fin_cases j <;> decide

end UniqueGamesTheorem.Explicit.MachineSubdivisionBody

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineSubdivisionBodySpecLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Exact tape framing, row serialization, and a uniform polynomial bound for
the already constructed whole subdivision-body execution. -/

/-! Concrete frames and literal row words for the subdivision occurrence loop. -/

/-! The actual streamed bytes coincide with the numbered semantic subdivision.
The controller copies the last table unchanged, so its input contract explicitly
requires involutive tables; binary translations satisfy this condition. -/

/-! Complete physical occurrence traversal of the subdivision program. -/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionLoop

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Target
open UniqueGamesTheorem.Foundations.Complexity
open MachineSubdivisionProgram

def bodyBound (n q Q : Nat) : Nat := 100 * (n + 3 * Q + q * (q + 1) + 1)

end UniqueGamesTheorem.Explicit.MachineSubdivisionLoop

/-! The complete finite subdivision machine, including its polynomial runtime
in the actual serialized input length and exact full-table output. -/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionRuntime

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Target
open UniqueGamesTheorem.Foundations.Complexity
open MachineSubdivisionProgram

def prefixPolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.X * (Polynomial.C 100 *
    (Polynomial.C 4 * Polynomial.X + Polynomial.C (q * (q + 1)) + 1) + 1) +
    Polynomial.C 62 * Polynomial.X + Polynomial.C (q + 50)

end UniqueGamesTheorem.Explicit.MachineSubdivisionRuntime

/-! A real finite program for uniform whole-instance copying. It reads three
headers, physically multiplies the occurrence count by the fixed constant,
copies the header-free body the same fixed number of times, and clears all
working tapes. No input-dependent data are placed in finite control. -/

namespace UniqueGamesTheorem.Explicit.MachineUniformProgram

open Turing UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Foundations.Complexity UniqueGamesTheorem.Foundations.Hastad

inductive Tape
  | input | vertices | alphabet | occurrences | newOccurrences
  | affineScratch | copyScratch | accumulator | output
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .vertices, .alphabet, .occurrences,
  .newOccurrences, .affineScratch, .copyScratch, .accumulator, .output]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev State := MachineFieldTemplate.State Unit

def initialState : State := (((), ()), none)

def headerField : Fin 3 → Tape
  | 0 => .vertices
  | 1 => .alphabet
  | 2 => .occurrences

def emitField : Fin 4 → Tape
  | 0 => .vertices
  | 1 => .alphabet
  | 2 => .newOccurrences
  | 3 => .input

def tokens (C : Nat) : List (MachineFieldTemplate.Token 4) :=
  [.copy 0, .copy 1, .copy 2] ++ List.replicate C (.copy 3)

def clearKeys : List Tape :=
  [.input, .vertices, .alphabet, .occurrences, .newOccurrences,
    .affineScratch, .copyScratch]

inductive Label (C : Nat)
  | headerStart (i : Fin 3)
  | headerRead (i : Fin 3)
  | scale (phase : Fin 3)
  | emit (label : MachineFieldTemplate.Label (tokens C).length)
  | finishStart
  | finish (label : SourceRuntimeFinish.Label clearKeys)
  deriving DecidableEq, Fintype

def headerNext {C : Nat} (i : Fin 3) : Label C :=
  if h : i.val + 1 < 3 then .headerStart ⟨i.val + 1, h⟩ else .scale 0

def emitEntry (C : Nat) : Label C :=
  .emit (MachineFieldTemplate.startAt (tokens C).length 0)

theorem accumulator_not_mem_clearKeys : Tape.accumulator ∉ clearKeys := by decide
theorem output_not_mem_clearKeys : Tape.output ∉ clearKeys := by decide

end UniqueGamesTheorem.Explicit.MachineUniformProgram

/-! Exact execution of the three input-header reads of uniform copying. -/

namespace UniqueGamesTheorem.Explicit.MachineUniformHeaders

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad
open MachineUniformProgram

def inputTapes (bits : List Bool) : Tape → List Bool :=
  fun k => if k = .input then bits else []

end UniqueGamesTheorem.Explicit.MachineUniformHeaders

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineUniformRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Whole-instance uniform copying: exact physical header arithmetic, repeated
body emission, actual cleanup, and a polynomial bound in the input codec length. -/

namespace UniqueGamesTheorem.Explicit.MachineUniformRun

open Turing UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Foundations Target
open UniqueGamesTheorem.Foundations.Complexity UniqueGamesTheorem.Foundations.Hastad
open MachineUniformProgram

theorem repeated_template (C : Nat) (fields : Fin 4 → List Bool) :
    MachineFieldTemplate.templateOutput (List.replicate C (.copy 3)) fields =
      MachineUniformCopyOrder.copyMajor C (fields 3) := by
  induction C with
  | zero => rfl
  | succ C ih =>
    simp only [List.replicate_succ, MachineFieldTemplate.templateOutput,
      List.flatMap_cons, MachineFieldTemplate.tokenOutput,
      MachineUniformCopyOrder.copyMajor, List.flatten_cons] at *
    rw [ih]

noncomputable def prefixPolynomial (C : Nat) : Polynomial Nat :=
  Polynomial.C (3 * C + 6) * Polynomial.X + Polynomial.C (3 * C + 16)

end UniqueGamesTheorem.Explicit.MachineUniformRun

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_RawInitialTablesLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit structural numberings of the raw 3SAT incidence graph. Unused
declared variable names are retained; their unary input header pays for them.
The graph has one dummy vertex and one tautological loop, even for an empty
formula. No input-dependent choice of a finite enumeration is made. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialTables

open Target GraphTables

def unitOrder : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv _ := rfl
  right_inv i := by fin_cases i; rfl

end UniqueGamesTheorem.Foundations.PCP.RawInitialTables

/-! Polynomial arithmetic for the actual initial-machine phase counts. The
separate execution theorem must connect these counts to the concrete program. -/

/-! Explicit finite predicates and numeric row words of the initial incidence table.
Every relation retains all 4096 entries, including repetitions. -/

/-! The concrete numbered amplification round, with one fixed base expander.
Every intermediate is an actual stored table, with explicit finite coordinates.
The running-time certificate is a separate theorem about these same functions. -/

namespace UniqueGamesTheorem.Foundations.PCP.RoundTables

/-- Initialized fixed data keep enormous constant powers symbolic in the kernel.
The stored equality proves the exact requested parameter; no value is assumed. -/
opaque fixedWalkParameter : {n : Nat // n = 2 * FinalConstants.endpointLength} :=
  ⟨2 * FinalConstants.endpointLength, rfl⟩

def walkParameter : Nat := fixedWalkParameter.val

theorem degree_positive : 0 < PreprocessingTables.degree := by
  unfold PreprocessingTables.degree
  omega

theorem dartFactor_positive (q : Nat) : 0 < AlphabetGraphBounds.dartFactor q := by
  unfold AlphabetGraphBounds.dartFactor AlphabetGraphBounds.localEventFactor
  positivity

end UniqueGamesTheorem.Foundations.PCP.RoundTables

/-! Gap amplification for the actual numbered table round. The fixed base
expander is the only supplied construction datum with a spectral certificate. -/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PreprocessingRegularLoopWordsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineModel

open Turing Complexity Hastad

inductive Tape
  | input | variables | counter | index | field (slot : Fin 6)
  | scratch | reversed | output
  deriving DecidableEq, Fintype

def nameField (slot : Fin 3) : Fin 6 := ⟨2 * slot.val, by omega⟩

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineModel

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_ActualCompleteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Actual finite-distribution identities for completeness. -/
namespace UniqueGamesTheorem.Reduction.ActualCompleteness

open UniqueGamesTheorem.Integration.BinaryLinear
open scoped BigOperators

section Source

theorem expect_function_apply {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [Nonempty Ω]
    (j : I) (f : Ω → ℚ) :
    (𝔼 U : I → Ω, f (U j)) = 𝔼 w : Ω, f w := by
  classical
  calc
    (𝔼 U : I → Ω, f (U j)) =
        𝔼 p : Ω × ({j' : I // j' ≠ j} → Ω), f p.1 := by
      apply Fintype.expect_equiv (Equiv.funSplitAt j Ω)
      intro U
      rfl
    _ = 𝔼 w : Ω, f w := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
      simp only [Fintype.expect_const]

end Source

section ActualLabeling
noncomputable section

theorem expect_pair {I J : Type*} [Fintype I] [Fintype J] (f : I × J → ℚ) :
    (𝔼 p : I × J, f p) = 𝔼 i : I, 𝔼 j : J, f (i, j) :=
  Finset.expect_product _ _ _

end
end ActualLabeling

end UniqueGamesTheorem.Reduction.ActualCompleteness

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_MachineRhsLoad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.MachineRhsLoad

open Turing
open UniqueGamesTheorem.Foundations.Complexity

abbrev State (k : Nat) (σ : Type) := (((Fin k → Bool) × σ) × Unit) × Option Bool
abbrev Alphabet {K : Type} (_ : K) := Bool

def rhs {k σ} (state : State k σ) : Fin k → Bool := state.1.1.1

def setRhs {k σ} (state : State k σ) (values : Fin k → Bool) : State k σ :=
  (((values, state.1.1.2), state.1.2), state.2)

@[simp] theorem rhs_setRhs {k σ} (state : State k σ) (values : Fin k → Bool) :
    rhs (setRhs state values) = values := rfl

@[simp] theorem setRhs_setRhs {k σ} (state : State k σ)
    (first second : Fin k → Bool) : setRhs (setRhs state first) second = setRhs state second := rfl

@[simp] theorem setRhs_same {k σ} (state : State k σ) : setRhs state (rhs state) = state := rfl

def fill {k : Nat} (values initial : Fin k → Bool) (cells : List (Fin k)) : Fin k → Bool :=
  cells.foldl (fun current i => Function.update current i (values i)) initial

theorem fill_apply {k : Nat} (values initial : Fin k → Bool) (cells : List (Fin k))
    (i : Fin k) : fill values initial cells i = if i ∈ cells then values i else initial i := by
  induction cells generalizing initial with
  | nil => simp [fill]
  | cons j cells ih =>
    change fill values (Function.update initial j (values j)) cells i = _
    rw [ih]
    by_cases hi : i ∈ cells
    · simp [hi]
    · by_cases hij : i = j
      · subst j; simp [hi]
      · simp [hi, hij]

theorem fill_all {k : Nat} (values initial : Fin k → Bool) :
    fill values initial (List.finRange k) = values := by
  funext i
  rw [fill_apply]
  simp only [List.mem_finRange, ↓reduceIte]

section Program

variable {k : Nat} {K Λ σ : Type} [DecidableEq K]

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State k σ) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def peekChain (field : Fin k → K) (exit : Option Λ) :
    List (Fin k) → TM2.Stmt (Alphabet (K := K)) Λ (State k σ)
  | [] => finish exit
  | i :: rest =>
    .peek (field i) (fun state head =>
      setRhs state (Function.update (rhs state) i (head.getD false)))
      (peekChain field exit rest)

def statement (field : Fin k → K) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State k σ) := peekChain field exit (List.finRange k)

def readRhs (field : Fin k → K) (tapes : K → List Bool) : Fin k → Bool :=
  fun i => (tapes (field i)).head?.getD false

theorem stepAux_peekChain (field : Fin k → K) (exit : Option Λ)
    (cells : List (Fin k)) (state : State k σ) (tapes : K → List Bool) :
    TM2.stepAux (peekChain field exit cells) state tapes =
      ⟨exit, setRhs state (fill (readRhs field tapes) (rhs state) cells), tapes⟩ := by
  induction cells generalizing state with
  | nil => cases exit <;> rfl
  | cons i rest ih =>
    simp only [peekChain, TM2.stepAux]
    rw [ih]
    rfl

theorem stepAux_statement (field : Fin k → K) (exit : Option Λ)
    (state : State k σ) (tapes : K → List Bool) :
    TM2.stepAux (statement field exit) state tapes =
      ⟨exit, setRhs state (readRhs field tapes), tapes⟩ := by
  rw [statement, stepAux_peekChain, fill_all]

end Program

end UniqueGamesTheorem.Reduction.MachineRhsLoad

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_MachineTemplateAddress
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! A fixed canonical-word template followed by actual radix-address execution.
The program is determined by the fixed tokens and tape layout. Numeric field
values enter only the tape invariants and execution theorem, never the labels. -/

namespace UniqueGamesTheorem.Reduction.MachineTemplateAddress

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad

inductive Tape (q width : Nat)
  | field (i : Fin q)
  | radix | output | reversed | forward | copyScratch
  | accA | accB | counter | hornerScratch
  | digit (i : Fin width)
  deriving DecidableEq, Fintype

abbrev State (σ : Type) := (σ × Unit) × Option Bool
abbrev Alphabet {K : Type} (_ : K) := Bool

variable {q width : Nat} {K Λ σ : Type} [DecidableEq K]

def chosen (slots : Tape q width ↪ K) : List K := List.ofFn (fun i => slots (.digit i))

omit [DecidableEq K] in
@[simp] theorem mem_chosen (slots : Tape q width ↪ K) (tape : K) :
    tape ∈ chosen slots ↔ ∃ i, slots (.digit i) = tape := by
  simp [chosen, List.mem_ofFn]

abbrev Label (m width : Nat) (cleanup : List K) :=
  MachineFieldTemplate.Label m ⊕ Unit ⊕ (Fin (width + 1) × Bool) ⊕
    MachineHorner.Label width ⊕ MachineDrainMany.Label cleanup

def emitLabel {m : Nat} {cleanup : List K} (l : MachineFieldTemplate.Label m) :
    Label m width cleanup := .inl l
def reverseLabel {m : Nat} {cleanup : List K} : Label m width cleanup := .inr (.inl ())
def parseLabel {m : Nat} {cleanup : List K} (l : Fin (width + 1) × Bool) :
    Label m width cleanup := .inr (.inr (.inl l))
def hornerLabel {m : Nat} {cleanup : List K} (l : MachineHorner.Label width) :
    Label m width cleanup := .inr (.inr (.inr (.inl l)))
def cleanupLabel {m : Nat} {cleanup : List K} (l : MachineDrainMany.Label cleanup) :
    Label m width cleanup := .inr (.inr (.inr (.inr l)))

def parseDestination (slots : Tape q width ↪ K) (i : Nat) : K :=
  if h : i < width then slots (.digit ⟨i, h⟩) else slots .forward

omit [DecidableEq K] in
@[simp] theorem parseDestination_below (slots : Tape q width ↪ K) (i : Nat) (hi : i < width) :
    parseDestination slots i = slots (.digit ⟨i, hi⟩) := by simp [parseDestination, hi]

structure Clean (slots : Tape q width ↪ K) (base : K → List Bool) : Prop where
  reversed : base (slots .reversed) = []
  forward : base (slots .forward) = []
  copyScratch : base (slots .copyScratch) = []
  accA : base (slots .accA) = []
  accB : base (slots .accB) = []
  counter : base (slots .counter) = []
  hornerScratch : base (slots .hornerScratch) = []
  digit : ∀ j, base (slots (.digit j)) = []

def digits (values : List Nat) (i : Nat) : Nat := values[i]?.getD 0

omit [DecidableEq K] in
theorem copiedLength_le (tokens : List (MachineFieldTemplate.Token q))
    (fields : Fin q → List Bool) (M : Nat) (bounded : ∀ j, (fields j).length ≤ M) :
    MachineFieldTemplate.copiedLength tokens fields ≤ tokens.length * M := by
  induction tokens with
  | nil => simp [MachineFieldTemplate.copiedLength]
  | cons token tokens ih =>
    cases token with
    | literal bits =>
      simp only [MachineFieldTemplate.copiedLength, List.map_cons, List.sum_cons,
        List.length_cons, Nat.zero_add] at *
      nlinarith
    | copy j =>
      simp only [MachineFieldTemplate.copiedLength, List.map_cons, List.sum_cons,
        List.length_cons] at *
      have h := bounded j
      nlinarith

omit [DecidableEq K] in
theorem lengthSum_le (selected : List K) (base : K → List Bool) (bound : Nat)
    (bounded : ∀ tape ∈ selected, (base tape).length ≤ bound) :
    MachineDrainMany.lengthSum selected base ≤ selected.length * bound := by
  induction selected with
  | nil => simp [MachineDrainMany.lengthSum]
  | cons tape selected ih =>
    have ht := bounded tape (by simp)
    have hs := ih (fun t ht => bounded t (by simp [ht]))
    simp only [MachineDrainMany.lengthSum, List.map_cons, List.sum_cons,
      List.length_cons] at *
    nlinarith

/-- A fixed polynomial in a magnitude bounding input fields, the serialized
word list, the radix, and the digits. Width and token count are static. -/
noncomputable def timePolynomial (tokenCount width : Nat) : Polynomial Nat :=
  MachineHorner.timePolynomial width +
    Polynomial.C (3 * tokenCount + width + 2) * Polynomial.X +
    Polynomial.C (3 * tokenCount + 3 * width + 3)

omit [DecidableEq K] in
theorem timePolynomial_eval (tokenCount width M : Nat) :
    (timePolynomial tokenCount width).eval M =
      (MachineHorner.timePolynomial width).eval M +
      (3 * tokenCount + width + 2) * M + (3 * tokenCount + 3 * width + 3) := by
  simp [timePolynomial]

end UniqueGamesTheorem.Reduction.MachineTemplateAddress

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_MachineAddressEdgeLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual edge emission from two fixed address templates. Capacity is copied
before unary addition, so the original capacity tape is preserved. All local
labels and literal instructions depend only on fixed templates and layout. -/

namespace UniqueGamesTheorem.Reduction.MachineAddressEdge

open Turing
open UniqueGamesTheorem.Foundations.Complexity
abbrev State (σ : Type) := (σ × Unit) × Option Bool
abbrev Alphabet {K : Type} (_ : K) := Bool

variable {q width : Nat} {K Λ σ : Type} [DecidableEq K]

abbrev Label (leftLength rightLength width : Nat) (cleanup : List K) :=
  MachineTemplateAddress.Label leftLength width cleanup ⊕ MachineTemplateAddress.Label rightLength width cleanup ⊕ Fin 7

def leftLabel {ml mr : Nat} {cleanup : List K} (label : MachineTemplateAddress.Label ml width cleanup) :
    Label ml mr width cleanup := .inl label
def rightLabel {ml mr : Nat} {cleanup : List K} (label : MachineTemplateAddress.Label mr width cleanup) :
    Label ml mr width cleanup := .inr (.inl label)
def plumbing {ml mr : Nat} {cleanup : List K} (index : Fin 7) :
    Label ml mr width cleanup := .inr (.inr index)

/-- A fixed polynomial in a common magnitude bound for the input fields,
serialized words, radix, capacity, and digits. -/
noncomputable def timePolynomial (leftCount rightCount width : Nat) : Polynomial Nat :=
  MachineTemplateAddress.timePolynomial leftCount width +
    MachineTemplateAddress.timePolynomial rightCount width +
    2 * (Polynomial.X + 1) ^ width + 4 * Polynomial.X + 12

omit [DecidableEq K] in
theorem timePolynomial_eval (leftCount rightCount width M : Nat) :
    (timePolynomial leftCount rightCount width).eval M =
      (MachineTemplateAddress.timePolynomial leftCount width).eval M +
      (MachineTemplateAddress.timePolynomial rightCount width).eval M +
      2 * (M + 1) ^ width + 4 * M + 12 := by
  simp [timePolynomial]

end UniqueGamesTheorem.Reduction.MachineAddressEdge

/-! Execute all fixed outcome rows after the existing RHS loader. A single
dispatcher freezes the loaded finite RHS vector into labels. Every row is an
actual address-edge phase; no row-run or whole-loop execution is assumed.
Program definitions contain only fixed templates, literal permutations, and
tape/label placement. Numeric names, radix, and capacity occur only in tapes
and the semantic correctness hypotheses. -/

namespace UniqueGamesTheorem.Reduction.MachineOutcomeRows

open Turing
open UniqueGamesTheorem.Foundations.Complexity

structure Spec (q width : Nat) where
  left : List (MachineFieldTemplate.Token q)
  right : List (MachineFieldTemplate.Token q)
  permutation : List Bool

/-- Numeric interpretations are proof-side data, separate from the program. -/
structure Values (width : Nat) where
  left : List Nat
  right : List Nat
  left_length : left.length = width
  right_length : right.length = width

abbrev Rhs (k : Nat) := Fin k → Bool
abbrev Row (k q width : Nat) := Rhs k → Spec q width
abbrev State (k : Nat) (σ : Type) := MachineRhsLoad.State k σ
abbrev Alphabet {K : Type} (_ : K) := Bool

variable {k q width : Nat} {K Λ σ : Type} [DecidableEq K]

def selected (rows : List (Row k q width)) (rhs : Rhs k) : List (Spec q width) :=
  rows.map (fun row => row rhs)

@[simp] theorem selected_length (rows : List (Row k q width)) (rhs : Rhs k) :
    (selected rows rhs).length = rows.length := by simp [selected]

/-- Sum of fixed row polynomials; the additional constant is the dispatcher.
This proof-side polynomial contains no runtime input field values. -/
noncomputable def timePolynomial (rows : List (Spec q width)) : Polynomial Nat :=
  (rows.map (fun row => MachineAddressEdge.timePolynomial
    row.left.length row.right.length width)).sum + 1

end UniqueGamesTheorem.Reduction.MachineOutcomeRows

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_CloneMachineModelLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Affine word emission in the actual clone-table machine

The shared machine keeps its context fixed while copying one saved word. Its
finite transducer therefore acts by a fixed symbol substitution. The lemmas
below identify that substitution with the established unary encoding of
`offset + scale * value`, including all header and equation-field contexts.
Scale, offset, and the triple-table length remain symbolic.
-/

namespace UniqueGamesTheorem.Reduction.CloneMachineAffine

open UniqueGamesTheorem.Foundations.Complexity

/-- Identity control transitions reduce exactly to fixed symbol substitution. -/
theorem output_eq_flatMap {Q : Type} [Fintype Q]
    (emit : Q → Bool → List Bool) (q : Q) (input : List Bool) :
    MachineTransducer.output (fun state _ => state) emit q input =
      input.flatMap (emit q) := by
  induction input with
  | nil => rfl
  | cons b input ih =>
    simp only [MachineTransducer.output, List.flatMap_cons, ih]

end UniqueGamesTheorem.Reduction.CloneMachineAffine

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_MachineAddressHeaders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace UniqueGamesTheorem.Reduction.MachineAddressHeaders

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad

namespace Prefix

inductive Label
  | copyOut | copyBack | read (slot : Fin 3 × Bool) | clear
  deriving DecidableEq, Fintype

def readStart (r : Nat) : Label := .read (SourceFieldArray.boundedIndex 2 r, false)
def readLoop (r : Nat) : Label := .read (SourceFieldArray.boundedIndex 2 r, true)

variable {K Λ σ : Type} [DecidableEq K]

def destination (slots : Fin 5 ↪ K) (r : Nat) : K := if r = 0 then slots 2 else slots 3

def copied (slots : Fin 5 ↪ K) (base : K → List Bool) : K → List Bool :=
  Function.update base (slots 1) (base (slots 0))

end Prefix

def baseConstant (s d : Nat) : Nat := 2 ^ s + 2 ^ d + 4
def radix (s d n m : Nat) : Nat := n + m + baseConstant s d
def capacity (k s d n m : Nat) : Nat := (radix s d n m) ^ (1 + 9 * k)
def edgeFactor (k s d noiseCount : Nat) : Nat :=
  2 ^ ((2 * k + 1) * (s + d + 1)) * noiseCount
def edgeCount (k s d noiseCount m : Nat) : Nat := edgeFactor k s d noiseCount * m ^ k

noncomputable section

inductive Kind
  | capacity | edges
  deriving DecidableEq

protected abbrev Kind.enumList : List Kind := [.capacity, .edges]

protected theorem Kind.enumList_nodup : Kind.enumList.Nodup := by decide

instance instFintypeKind : Fintype Kind where
  elems := ⟨Kind.enumList, Kind.enumList_nodup⟩
  complete x := by cases x <;> decide

def polynomial (k s d noiseCount : Nat) : Kind → Polynomial Nat
  | .capacity => Polynomial.X ^ (1 + 9 * k)
  | .edges => Polynomial.C (edgeFactor k s d noiseCount) * Polynomial.X ^ k

@[simp] theorem polynomial_capacity_eval (k s d noiseCount B : Nat) :
    (polynomial k s d noiseCount .capacity).eval B = B ^ (1 + 9 * k) := by
  simp [polynomial]

@[simp] theorem polynomial_edges_eval (k s d noiseCount m : Nat) :
    (polynomial k s d noiseCount .edges).eval m = edgeCount k s d noiseCount m := by
  simp [polynomial, edgeCount]

namespace Arithmetic

inductive Control
  | variableCount | occurrenceCount | baseValue | capacity | temporary | reversed
  | accA | accB | counter | scratch
  deriving DecidableEq

protected abbrev Control.enumList : List Control := [.variableCount, .occurrenceCount, .baseValue,
  .capacity, .temporary, .reversed, .accA, .accB, .counter, .scratch]

protected theorem Control.enumList_nodup : Control.enumList.Nodup := by decide

instance instFintypeControl : Fintype Control where
  elems := ⟨Control.enumList, Control.enumList_nodup⟩
  complete x := by cases x <;> decide

def inputControl : Kind → Control
  | .capacity => .baseValue | .edges => .occurrenceCount

def outputControl : Kind → Control
  | .capacity => .capacity | .edges => .temporary

def controlSlots (kind : Kind) : Fin 6 ↪ Control where
  toFun i := match i.val with
    | 0 => inputControl kind | 1 => .accA | 2 => .accB
    | 3 => outputControl kind | 4 => .counter | _ => .scratch
  inj' := by
    intro i j h
    cases kind <;> fin_cases i <;> fin_cases j <;> cases h <;> rfl

variable {k s d noiseCount : Nat} {K Λ σ : Type}

variable [DecidableEq K]

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end Arithmetic

end

end UniqueGamesTheorem.Reduction.MachineAddressHeaders

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_SourceEquationLookupLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.SourceEquationLookup

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad
open SourceMachine
inductive Tape
  | source | index | work | scratch | field (slot : Fin 4)
  deriving DecidableEq, Fintype

inductive Label
  | copyOut | copyBack | headerFirst | headerSecond | guard
  | skip (slot : Fin 4)
  | read (slot : Fin 5 × Bool)
  deriving DecidableEq, Fintype

def fieldDestination (r : Nat) : Tape := .field ⟨min r 3, by omega⟩
def readStart (r : Nat) : Label := .read (SourceFieldArray.boundedIndex 4 r, false)
def readLoop (r : Nat) : Label := .read (SourceFieldArray.boundedIndex 4 r, true)
def skipLabel (r : Nat) : Label := if h : r < 4 then .skip ⟨r, h⟩ else .guard
def headerLabel (r : Nat) : Label :=
  if r = 0 then .headerFirst else if r = 1 then .headerSecond else .guard

variable {σ : Type}

noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 4 * Polynomial.X + Polynomial.C 8

theorem timePolynomial_eval (L : Nat) : timePolynomial.eval L = 4 * L + 8 := by
  simp [timePolynomial]

end UniqueGamesTheorem.Reduction.SourceEquationLookup

end

section

namespace UniqueGamesTheorem.Reduction.MachineSourceTuple

open Turing UniqueGamesTheorem.Foundations.Complexity

inductive Tape (width : Nat) (Extra : Type)
  | source | index | work | scratch | copyScratch
  | savedIndex (coordinate : Fin width)
  | field (coordinate : Fin width) (slot : Fin 4)
  | extra (value : Extra)
  deriving DecidableEq, Fintype

inductive Label (width : Nat)
  | copyOut (coordinate : Fin width) | copyBack (coordinate : Fin width)
  | lookup (coordinate : Fin width) (localLabel : SourceEquationLookup.Label)
  | clearWork (coordinate : Fin width) | clearIndex (coordinate : Fin width)
  | done
  deriving DecidableEq, Fintype

variable {width : Nat} {Extra σ : Type}

variable [DecidableEq Extra]

def placedLabel (j : Fin width) : Option SourceEquationLookup.Label → Option (Label width)
  | none => some (.clearWork j)
  | some l => some (.lookup j l)

def nextLabel (j : Fin width) : Label width :=
  if h : j.val + 1 < width then .copyOut ⟨j.val + 1, h⟩ else .done

def labelAt (r : Nat) : Label width :=
  if h : r < width then .copyOut ⟨r, h⟩ else .done

theorem nextLabel_eq (j : Fin width) : nextLabel j = labelAt (j.val + 1) := rfl

def nameSlot (s : Fin 3) : Fin 4 := ⟨s.val, by omega⟩

end UniqueGamesTheorem.Reduction.MachineSourceTuple

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_AddressMachineSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.AddressMachineSpace

open UniqueGamesTheorem.Foundations.Complexity

abbrev Control (k : Nat) := ((Fin k → Bool) × Unit) × Unit
abbrev State (k : Nat) := Control k × Option Bool

def initialState (k : Nat) : State k := (((fun _ => false, ()), ()), none)

end UniqueGamesTheorem.Reduction.AddressMachineSpace

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_AddressOdometerSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Reduction.AddressOdometerSchedule

open Turing
open UniqueGamesTheorem.Foundations.Complexity MachineTupleOdometer
open UniqueGamesTheorem.Foundations.Hastad


noncomputable section

variable {k s d noiseCount m : ℕ} {Λ σ : Type}

def blockPrefix (blocks : ℕ → List Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => blockPrefix blocks n ++ blocks n

end
end UniqueGamesTheorem.Reduction.AddressOdometerSchedule

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_FixedOutcomes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.FixedOutcomes

open Integration.BinaryLinear
open ActualEnumeration UniqueGamesTheorem.Reduction.Explicit

variable {N : Type*}

def occurrenceTuples (m k : Nat) : List (Fin k → Fin m) :=
  functions (List.finRange m) k

theorem pairs_associate {Left Middle Right : Type*}
    (xs : List Left) (ys : List Middle) (zs : List Right) :
    pairs (pairs xs ys) zs =
      xs.flatMap (fun x => (pairs ys zs).map (fun p => ((x, p.1), p.2))) := by
  simp only [pairs, List.flatMap_assoc, List.flatMap_map, List.map_flatMap,
    List.map_map, Function.comp_def]

end UniqueGamesTheorem.Reduction.FixedOutcomes

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_AddressOutcomeSpecs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Reduction.AddressOutcomeSpecs

open Integration.BinaryLinear Foundations.Complexity
open Integration

abbrev Spec (k : Nat) := MachineOutcomeRows.Spec (4*k) (1+9*k)
abbrev Values (k : Nat) := MachineOutcomeRows.Values (1+9*k)

end UniqueGamesTheorem.Reduction.AddressOutcomeSpecs

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_AddressTupleBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Integration.AddressTupleBody

open Turing Reduction Foundations.Complexity
open AddressMachineSpace


variable {k s d noiseCount : Nat} {Λ : Type}

abbrev BodyState (k : Nat) := AddressMachineSpace.State k

end UniqueGamesTheorem.Integration.AddressTupleBody

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_AddressTupleBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Integration.AddressTupleBudget

open Reduction Foundations.Complexity
open AddressTupleBody


variable {k s d noiseCount : Nat}

def radixBound (s d L : Nat) : Nat := L + (2^s + 2^d + 4)

def magnitude (k s d L : Nat) : Nat :=
  (L+1) + radixBound s d L + (radixBound s d L)^(1+9*k) +
    (1+9*k)*(radixBound s d L+1) + 1

noncomputable def magnitudePolynomial (k s d : Nat) : Polynomial Nat :=
  (Polynomial.X+1) + (Polynomial.X+Polynomial.C (2^s+2^d+4)) +
    (Polynomial.X+Polynomial.C (2^s+2^d+4))^(1+9*k) +
    Polynomial.C (1+9*k)*(Polynomial.X+Polynomial.C (2^s+2^d+4)+1) + 1

@[simp] theorem magnitudePolynomial_eval (k s d L : Nat) :
    (magnitudePolynomial k s d).eval L = magnitude k s d L := by
  simp only [magnitudePolynomial, magnitude, radixBound, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_one]

theorem field_length_le_magnitude (k s d L : Nat) : L+1 ≤ magnitude k s d L := by
  unfold magnitude
  omega

theorem eval_sum_constant {α : Type} (items : List α) (p : Polynomial Nat) (M : Nat) :
    ((items.map (fun _ => p)).sum).eval M = items.length*p.eval M := by
  induction items with
  | nil => simp
  | cons item items ih =>
    simp only [List.map_cons, List.sum_cons, Polynomial.eval_add, List.length_cons,
      Nat.add_mul, Nat.one_mul, ih]
    omega

theorem lengthSum_le_of_mem {K : Type} [DecidableEq K]
    (chosen : List K) (base : K → List Bool) (M : Nat)
    (bounded : ∀ tape ∈ chosen, (base tape).length ≤ M) :
    MachineDrainMany.lengthSum chosen base ≤ chosen.length*M := by
  induction chosen with
  | nil => simp [MachineDrainMany.lengthSum]
  | cons tape chosen ih =>
    have first := bounded tape (by simp)
    have rest := ih (fun t ht => bounded t (List.mem_cons_of_mem tape ht))
    simp only [MachineDrainMany.lengthSum, List.map_cons, List.sum_cons,
      List.length_cons, Nat.add_mul, Nat.one_mul] at *
    omega

end UniqueGamesTheorem.Integration.AddressTupleBudget

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_AddressTuplePolynomialLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace UniqueGamesTheorem.Reduction.AddressMachineProgram

open Turing Foundations.Complexity Foundations.Hastad Integration


noncomputable section

abbrev State (k : Nat) := AddressMachineSpace.State k

end
end UniqueGamesTheorem.Reduction.AddressMachineProgram



/-!
The actual address machine's final bridge, cleanup, reversal, and halt. The
polynomial cleanup bound follows from space used by the supplied actual prefix
execution. The complete reduction supplies that prefix in `MachineAddressGame`.
-/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_ParameterSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The outer error parameters are fixed before the latent gadget or its alphabet.
We use the same positive reciprocal integer for the latent noise budget and
the rounding tolerance. This permitted specialization makes uniform occurrence
rounding an exact fixed-copy operation. The later parity error is chosen only
after the tuple length has been fixed.
-/

namespace UniqueGamesTheorem.ParameterSelection
noncomputable section

structure OuterParameters (ε δ : ℝ) where
  epsilon0 : ℚ
  delta0 : ℚ
  epsilon0_pos : 0 < epsilon0
  delta0_pos : 0 < delta0
  epsilon0_le : (epsilon0 : ℝ) ≤ ε
  delta0_le : (delta0 : ℝ) ≤ δ
  repetitions : ℕ
  repetitions_pos : 0 < repetitions
  soundness_rate : (1 - (1 : ℝ) / 10240000) ^ repetitions ≤ delta0
  copies : ℕ
  copies_large : 200 ≤ copies
  reciprocal_pos : (0 : ℚ) < 1 / copies
  reciprocal_small : 1 / (copies : ℚ) ≤ 1 / 200
  reciprocal_budget : 1 / (copies : ℚ) ≤ epsilon0 / repetitions

namespace OuterParameters

variable {ε δ : ℝ} (P : OuterParameters ε δ)

def pStar : ℚ := 1 / P.copies

theorem pStar_pos : 0 < P.pStar := P.reciprocal_pos

end OuterParameters
end
end UniqueGamesTheorem.ParameterSelection

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Repetition_CollisionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finite conditional projection kernels for the Dinur--Steurer argument.
The outer distribution samples the right question and the inner distribution
samples the left question conditional on it. These are genuine normalized
finite distributions; no norm inequality or repetition claim is a field.
-/

namespace UniqueGamesTheorem.Repetition
open scoped BigOperators
noncomputable section

namespace ProjectionKernel
variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

def vectorMass (f : Ω → Q₁ → A₁ → ℝ) (x : Q₁) : ℝ :=
  ∑ ω, (∑ a, f ω x a) ^ 2

end ProjectionKernel
end
end UniqueGamesTheorem.Repetition

end

section

/-!
Determinization of a nonnegative vector with one label chosen per vertex.
Every vertex retains its total mass. The objective is an arbitrary nonnegative
weighted sum of squares of linear functionals, so coefficients may have either
sign. Sampling complete label tables gives the original vector as its mean;
finite variance and an attained maximum then supply a deterministic table.
-/

namespace UniqueGamesTheorem.Repetition

open scoped BigOperators

noncomputable section

variable {V A T : Type*} [Fintype V] [Fintype A] [Fintype T]

/-- The mass at each vertex, before or after determinization. -/
def rowMass (h : V → A → ℝ) (v : V) : ℝ := ∑ a, h v a

/-- Move the full mass of each row to its selected label. -/
def deterministicVector [DecidableEq A] (h : V → A → ℝ) (labels : V → A)
    (v : V) (a : A) : ℝ :=
  if a = labels v then rowMass h v else 0

omit [Fintype V] in
@[simp] theorem deterministicVector_rowMass [DecidableEq A]
    (h : V → A → ℝ) (labels : V → A) (v : V) :
    rowMass (deterministicVector h labels) v = rowMass h v := by
  simp [rowMass, deterministicVector]

omit [Fintype V] in
theorem rowMass_nonnegative (h : V → A → ℝ) (hh : ∀ v a, 0 ≤ h v a) (v : V) :
    0 ≤ rowMass h v :=
  Finset.sum_nonneg (fun a _ => hh v a)

omit [Fintype V] in
theorem deterministicVector_nonnegative [DecidableEq A] (h : V → A → ℝ)
    (hh : ∀ v a, 0 ≤ h v a) (labels : V → A) (v : V) (a : A) :
    0 ≤ deterministicVector h labels v a := by
  unfold deterministicVector
  split
  · exact rowMass_nonnegative h hh v
  · exact le_rfl

@[simp] theorem deterministicVector_linear_image [DecidableEq A]
    (h : V → A → ℝ) (labels : V → A) (c : V → A → ℝ) :
    (∑ v, ∑ a, c v a * deterministicVector h labels v a) =
      ∑ v, c v (labels v) * rowMass h v := by
  simp [deterministicVector, mul_ite]

omit [Fintype V] in
theorem entry_eq_zero_of_rowMass_eq_zero (h : V → A → ℝ)
    (hh : ∀ v a, 0 ≤ h v a) (v : V) (hz : rowMass h v = 0) (a : A) :
    h v a = 0 := by
  have hle : h v a ≤ rowMass h v :=
    Finset.single_le_sum (fun b _ => hh v b) (Finset.mem_univ a)
  exact le_antisymm (hz ▸ hle) (hh v a)

end

end UniqueGamesTheorem.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Repetition_RoundingPaddingLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Finite vertex-specific padding of nonnegative vectors to unit squared row
mass. The new coordinates can only increase any nonnegative relation energy. -/

namespace UniqueGamesTheorem.Repetition

open scoped BigOperators

noncomputable section

variable {V A Ω E : Type*} [Fintype V] [Fintype Ω] [Fintype E]

def rowSquareMass (f : V → Ω → ℝ) (v : V) : ℝ := ∑ ω, (f v ω) ^ 2

def paddedAmplitude [DecidableEq V] (f : V → Ω → ℝ) (v : V) : Ω ⊕ V → ℝ
  | Sum.inl ω => f v ω
  | Sum.inr w => if v = w then Real.sqrt (1 - rowSquareMass f v) else 0

def paddedLabel (a : V → Ω → A) (fallback : A) (v : V) : Ω ⊕ V → A
  | Sum.inl ω => a v ω
  | Sum.inr _ => fallback

omit [Fintype V] in
theorem paddedAmplitude_nonnegative [DecidableEq V] (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) (v : V) (ω : Ω ⊕ V) :
    0 ≤ paddedAmplitude f v ω := by
  cases ω with
  | inl ω => exact hf v ω
  | inr w =>
      simp only [paddedAmplitude]
      split
      · exact Real.sqrt_nonneg _
      · exact le_rfl

end
end UniqueGamesTheorem.Repetition

end

section

/-!
The collision norm as an actual finite distribution on symmetrized edges.
An edge retains the hidden common right question, while each label remains a
function of its own left question.  Projection uniqueness turns the sum over
common right answers into a Boolean compatibility predicate exactly.
-/

namespace UniqueGamesTheorem.Repetition.ProjectionKernel

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

abbrev SymmetricEdge (Q₁ Q₂ : Type*) := Q₂ × Q₁ × Q₁

def symmetricLeft (e : SymmetricEdge Q₁ Q₂) : Q₁ := e.2.1

def symmetricRight (e : SymmetricEdge Q₁ Q₂) : Q₁ := e.2.2

/-- A coordinate has one possible nonzero label at each question. -/
def singleLabelVector (a : Q₁ → Ω → A₁) (f : Q₁ → Ω → ℝ)
    (ω : Ω) (x : Q₁) (b : A₁) : ℝ := by
  classical
  exact if a x ω = b then f x ω else 0

end
end UniqueGamesTheorem.Repetition.ProjectionKernel

end

section

/-!
Apply finite positive-vector determinization to the actual projection kernel.
The target coordinates retain both the right question and the right answer.
The selected label may depend on the auxiliary coordinate, but only on its own
left question. Every question's squared vector mass is preserved exactly.
-/

namespace UniqueGamesTheorem.Repetition.ProjectionKernel

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

/-- The amplitude at a question is the sum of its original label entries. -/
def vectorAmplitude (h : Ω → Q₁ → A₁ → ℝ) (x : Q₁) (ω : Ω) : ℝ :=
  rowMass (h ω) x

omit [Fintype Q₁] [Fintype Ω] in
theorem vectorAmplitude_nonnegative (h : Ω → Q₁ → A₁ → ℝ)
    (hh : ∀ ω x a, 0 ≤ h ω x a) (x : Q₁) (ω : Ω) :
    0 ≤ vectorAmplitude h x ω :=
  rowMass_nonnegative (h ω) (hh ω) x

omit [Fintype Q₁] in
@[simp] theorem rowSquareMass_vectorAmplitude (h : Ω → Q₁ → A₁ → ℝ) (x : Q₁) :
    rowSquareMass (vectorAmplitude h) x = vectorMass h x := rfl

end

end UniqueGamesTheorem.Repetition.ProjectionKernel

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Repetition_RoundingSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Correlated rounding of finite partial assignments of equal density. A common
finite list of seeds is scanned locally at every vertex. An edge succeeds when
the first seed accepted by either endpoint is a jointly accepted good seed.
The finite truncation error is at most `(1 - density)^n`. Maximizing over the finite
set of deterministic labelings removes that error. No infinite random seed or
assumed rounding principle is used.
-/

namespace UniqueGamesTheorem.Repetition

open UniqueGamesTheorem.Foundations.CorrelatedSampling
open UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators

noncomputable section

variable {V S A : Type*} [Fintype V] [Fintype S] [Fintype A]

def partialSample (accept : V → S → Bool) (label : V → S → A)
    (fallback : A) (proposals : List S) (v : V) : A :=
  localSample (accept v) (label v) fallback proposals

omit [Fintype V] [Fintype S] [Fintype A] in
theorem first_good_relation_le (accept : V → S → Bool)
    (label : V → S → A) (R : V → V → A → A → Bool)
    (fallback : A) (x y : V) (proposals : List S) :
    goodFirstIndicator (fun s => accept x s || accept y s)
      (fun s => accept x s && accept y s && R x y (label x s) (label y s)) proposals ≤
    (if R x y (partialSample accept label fallback proposals x)
      (partialSample accept label fallback proposals y) then 1 else 0) := by
  classical
  cases hfirst : firstAccepted (fun s => accept x s || accept y s) proposals with
  | none =>
      simp only [goodFirstIndicator, hfirst]
      split <;> norm_num
  | some s =>
      by_cases hg : (accept x s && accept y s && R x y (label x s) (label y s)) = true
      · have hp : (accept x s = true ∧ accept y s = true) ∧
            R x y (label x s) (label y s) = true := by simpa using hg
        have hs := first_union_common (accept x) (accept y) proposals s hfirst hp.1.1 hp.1.2
        simp [goodFirstIndicator, hfirst, partialSample, localSample,
          hs.1, hs.2, hp.1.1, hp.1.2, hp.2]
      · simp only [goodFirstIndicator, hfirst, hg, Bool.false_eq_true, ite_false]
        split <;> norm_num

theorem partial_ratio_bound {g u density : ℝ} (hdensity : 0 < density)
    (hg : 0 ≤ g) (hlu : density ≤ u) (hug : u + g ≤ 2 * density) :
    2 * (g / density) - 1 ≤ g / u := by
  have hu : 0 < u := lt_of_lt_of_le hdensity hlu
  apply (le_div_iff₀ hu).2
  by_cases hsgn : 2 * (g / density) - 1 ≤ 0
  · exact (mul_nonpos_of_nonpos_of_nonneg hsgn hu.le).trans hg
  · have hcoeff : 0 ≤ 2 * g - density := by
      have hd : 1 < 2 * g / density := by
        rw [mul_div_assoc]
        linarith
      have := (lt_div_iff₀ hdensity).mp hd
      linarith
    have hm := mul_le_mul_of_nonneg_left hug hcoeff
    have heq : (2 * (g / density) - 1) * u = ((2 * g - density) * u) / density := by
      field_simp [ne_of_gt hdensity]
    rw [heq]
    apply (div_le_iff₀ hdensity).2
    nlinarith [sq_nonneg (density - g)]

end
end UniqueGamesTheorem.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Repetition_RoundingThresholdLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Exact finite threshold expansion for unit vectors.  A shared seed chooses one
coordinate and one atom of the common threshold partition.  Squared amplitudes
are acceptance probabilities, and joint acceptance has the coordinatewise
minimum law.  The construction permits arbitrary vertex-dependent labels and
arbitrary relations between their labels.
-/

namespace UniqueGamesTheorem.Repetition

open scoped BigOperators
open Foundations CorrelatedSampling

noncomputable section

variable {V Ω A : Type*} [Fintype V] [Fintype Ω]

/-- All squared amplitudes, including repetitions, determine a single shared
finite threshold partition. -/
def thresholdLevels (f : V → Ω → ℝ) : List ℝ := by
  classical
  exact (Finset.univ : Finset (V × Ω)).toList.map (fun p => f p.1 p.2 ^ 2)

theorem square_mem_thresholdLevels (f : V → Ω → ℝ) (x : V) (ω : Ω) :
    f x ω ^ 2 ∈ thresholdLevels f := by
  classical
  apply List.mem_map.mpr
  exact ⟨(x, ω), by simp, rfl⟩

/-- The seed is a coordinate and a finite threshold interval. -/
abbrev ThresholdSeed (f : V → Ω → ℝ) := RectangleSeed (thresholdLevels f) Ω

def thresholdAccept (f : V → Ω → ℝ) (x : V) : ThresholdSeed f → Bool :=
  rectangleAccept (thresholdLevels f) (fun ω => f x ω ^ 2)

/-- Labels use only the local vertex and the shared coordinate. -/
def thresholdLabel (f : V → Ω → ℝ) (a : V → Ω → A) (x : V)
    (seed : ThresholdSeed f) : A := a x seed.1

def thresholdRate (Ω : Type*) [Fintype Ω] : ℝ := 1 / Fintype.card Ω

theorem thresholdRate_positive [Nonempty Ω] : 0 < thresholdRate Ω := by
  unfold thresholdRate
  exact one_div_pos.mpr (by exact_mod_cast Fintype.card_pos (α := Ω))

omit [Fintype V] in
theorem square_le_one_of_row_norm (f : V → Ω → ℝ)
    (hnorm : ∀ x, ∑ ω, f x ω ^ 2 = 1) (x : V) (ω : Ω) : f x ω ^ 2 ≤ 1 := by
  calc
    _ ≤ ∑ t, f x t ^ 2 :=
      Finset.single_le_sum (fun t _ => sq_nonneg (f x t)) (Finset.mem_univ ω)
    _ = 1 := hnorm x

end

end UniqueGamesTheorem.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Repetition_TensorAlgebraLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finite-sum tensor factorization used by projection-game collision operators.
No restriction to coordinatewise strategies occurs: `f` below is an arbitrary
function of both input questions and both input answers.
-/

namespace UniqueGamesTheorem.Repetition

open scoped BigOperators

noncomputable section

variable {X A Y B U D Z C I : Type*}
  [Fintype X] [Fintype A] [Fintype U] [Fintype D] [Fintype I]

/-- Apply a finite real kernel. Output indices need no finiteness assumption. -/
def kernelApply (K : Y → B → X → A → ℝ) (f : X → A → ℝ) (y : Y) (b : B) : ℝ :=
  ∑ x, ∑ a, K y b x a * f x a

/-- Independent tensor of two kernels. -/
def tensorKernel (K : Y → B → X → A → ℝ) (L : Z → C → U → D → ℝ)
    (yz : Y × Z) (bc : B × C) (xu : X × U) (ad : A × D) : ℝ :=
  K yz.1 bc.1 xu.1 ad.1 * L yz.2 bc.2 xu.2 ad.2

/-- Applying the tensor first applies `L` separately for every fixed input of
`K`, and then applies `K`. This is valid for arbitrary coupled inputs. -/
theorem kernelApply_tensor
    (K : Y → B → X → A → ℝ) (L : Z → C → U → D → ℝ)
    (f : (X × U) → (A × D) → ℝ) (y : Y) (z : Z) (b : B) (c : C) :
    kernelApply (tensorKernel K L) f (y,z) (b,c) =
      kernelApply K (fun x a => kernelApply L (fun u d => f (x,u) (a,d)) z c) y b := by
  classical
  simp only [kernelApply, tensorKernel, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Finset.mul_sum, mul_assoc]

/-- Summing a family of input functions commutes with the finite operator. -/
theorem kernelApply_sum
    (K : Y → B → X → A → ℝ) (f : I → X → A → ℝ) (y : Y) (b : B) :
    kernelApply K (fun x a => ∑ i, f i x a) y b =
      ∑ i, kernelApply K (f i) y b := by
  classical
  simp only [kernelApply, Finset.mul_sum]
  calc
    (∑ x, ∑ a, ∑ i, K y b x a * f i x a) =
        ∑ x, ∑ i, ∑ a, K y b x a * f i x a := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

theorem kernelApply_smul
    (K : Y → B → X → A → ℝ) (f : X → A → ℝ) (r : ℝ) (y : Y) (b : B) :
    kernelApply K (fun x a => r * f x a) y b = r * kernelApply K f y b := by
  simp only [kernelApply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro a _
  exact mul_left_comm _ _ _

end
end UniqueGamesTheorem.Repetition

end

section

/-! Homogeneous normalization for finite nonnegative vector assignments. -/

namespace UniqueGamesTheorem.Repetition.ProjectionKernel
open scoped BigOperators
noncomputable section

variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

omit [Fintype Q₁] in
theorem vectorMass_smul (f : Ω → Q₁ → A₁ → ℝ) (r : ℝ) (x : Q₁) :
    vectorMass (fun ω x a => r * f ω x a) x = r ^ 2 * vectorMass f x := by
  unfold vectorMass
  simp_rw [← Finset.mul_sum, mul_pow]
  exact (Finset.mul_sum _ _ _).symm

omit [Fintype Q₁] in
theorem entry_eq_zero_of_vectorMass_nonpositive
    (f : Ω → Q₁ → A₁ → ℝ) (hf : ∀ ω x a, 0 ≤ f ω x a)
    (hmass : ∀ x, vectorMass f x ≤ 0) (ω : Ω) (x : Q₁) (a : A₁) :
    f ω x a = 0 := by
  classical
  have hsquare : (∑ b, f ω x b) ^ 2 ≤ vectorMass f x :=
    Finset.single_le_sum (fun τ _ => sq_nonneg (∑ b, f τ x b)) (Finset.mem_univ ω)
  have hsum : ∑ b, f ω x b = 0 := by
    nlinarith [hmass x, sq_nonneg (∑ b, f ω x b)]
  have hentry : f ω x a ≤ ∑ b, f ω x b :=
    Finset.single_le_sum (fun b _ => hf ω x b) (Finset.mem_univ a)
  rw [hsum] at hentry
  exact le_antisymm hentry (hf ω x a)

end
end UniqueGamesTheorem.Repetition.ProjectionKernel

end

end OAI
end


