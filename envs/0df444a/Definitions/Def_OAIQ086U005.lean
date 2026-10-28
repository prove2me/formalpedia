-- Prove2me | Definitions.Def_OAIQ086U005
-- name    : OAIQ086U005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T16:19:57.456409+00:00
-- url     : https://prove2.me/theorems/1a7914a0-2329-4f2a-b811-c446d4f0aefb
-- title:
--   Definitions bundle OAIQ086U005 of the split of OpenAI, The Unique Games Theorem
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniqueGamesTheorem.theorem11`, carved from OpenAI's openai/math development (OpenAI, *The Unique Games Theorem*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1083 declarations of OpenAI's Lean: 392 definitions, 4 inductive types or structures, 29 instances and 658 theorems. The definitions and types are `OAI.UniqueGamesTheorem.Decoder.ActualMatrixContradiction.expectationOf`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBodyBounds.blockPolynomial`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBodyBounds.cleanupPolynomial`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBodyBounds.corePolynomial`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBodyBounds.outputPolynomial`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBodyBounds.rowPolynomial`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBodyBounds.wide`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBodyBounds.blockPolynomial`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBodyBounds.cleanupPolynomial`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBodyBounds.corePolynomial`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBodyBounds.loopPolynomial`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBodyBounds.outputPolynomial`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBodyBounds.prePolynomial`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBodyBounds.rowPolynomial`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBodyBounds.wide`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.arithmeticPolynomial`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.timePolynomial`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularVertexBlock.dummyTimeBound`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularVertexBlock.originalTimeBound`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularVertexBlock.portTimeBound`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryEqualityBit.bitEncoding`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryEqualityBit.compareStateEquiv`, `OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalEnumeration.enumeration`, `OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalEnumeration.extraTapeEquiv`, `OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalEnumeration.globalTapeEquiv`, `OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalEnumeration.headerTapeEquiv`, `OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineEqualityField.Label`, `OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineEqualityField.entry`, `OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineField.Label`, `OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineField.entry`, `OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.Label`, `OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterD`, `OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders`, `OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.steps`, `OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.FinishLabel`, `OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.Tape`, `OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.enumeration`, `OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.headerDarts`, `OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.headerVertices`, `OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.inputTape` and 356 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `UniqueGames_Analysis_MatrixEnergy`, `UniqueGames_Analysis_MatrixNoiseLemmas`, `UniqueGames_Analysis_MatrixRestrictions`, `UniqueGames_Decoding_ActualMatrixContradiction`, `UniqueGames_Foundations_Conditioning`, `UniqueGames_Foundations_FiniteTrialsLemmas`, `UniqueGames_Foundations_KernelSampling`, `UniqueGames_Foundations_LabelBound`, `UniqueGames_Foundations_MixtureLemmas`, `UniqueGames_Foundations_PinskerLemmas`, `UniqueGames_Foundations_Rectangle`, `UniqueGames_Foundations_SamplingLemmas`, `UniqueGames_Foundations_SharedProfiles`, `UniqueGames_Foundations_ValueLemmas`, `UniqueGames_Games_CompletedSamplingLemmas`, `UniqueGames_Games_FactorizationLemmas`, `UniqueGames_Games_FinishBoundsLemmas`, `UniqueGames_Games_MaskedVariation`, `UniqueGames_Games_Overlap`, `UniqueGames_Games_PartialRevealLemmas`, `UniqueGames_Games_SelectedCommonMarginalLemmas`, `UniqueGames_Games_SelectedInformationLemmas`, `UniqueGames_Games_SelectionSequence`, `UniqueGames_Games_Variation`, `UniqueGames_Inverse_KMSAnalyticHybridEnergyLemmas`, `UniqueGames_Inverse_KMSBasisComparisonLemmas`, `UniqueGames_Inverse_KMSBasisComparisonPseudorandomTupleMapLemmas`, `UniqueGames_Inverse_KMSFoundationLemmas`, `UniqueGames_Inverse_MatrixChartIntervalsLemmas`, `UniqueGames_Inverse_MatrixChartLemmas`, `UniqueGames_Inverse_RowErasureLemmas`, `UniqueGames_Inverse_RowErasureTail`, `UniqueGames_Machines_MachineLemmas`, `UniqueGames_Machines_MachineRegularOriginalBodyBounds`, `UniqueGames_Machines_MachineRegularOwnerBody`, `UniqueGames_Machines_MachineRegularOwnerBodyBounds`, `UniqueGames_Machines_MachineRegularTable`, `UniqueGames_Machines_MachineRegularVertexBlock`, `UniqueGames_Machines_MachineSubroutineLemmas`, `UniqueGames_Machines_MachineUnaryEqualityBit`, `UniqueGames_Machines_PoweringGlobalEnumerationLemmas`, `UniqueGames_Machines_PoweringMachineEqualityField`, `UniqueGames_Machines_PoweringMachineFinish`, `UniqueGames_Machines_PoweringMachineInitialize`, `UniqueGames_Machines_PoweringMachineLoop`, `UniqueGames_Machines_PoweringMachineOuterLoopLemmas`, `UniqueGames_Machines_PoweringMachineRelationLemmas`, `UniqueGames_Machines_PoweringMachineRowBody`, `UniqueGames_Machines_PoweringMachineVertex`, `UniqueGames_Machines_PoweringPolynomialBudgetLemmas`, `UniqueGames_PCP_Addresses`, `UniqueGames_PCP_AlphabetGraphLemmas`, `UniqueGames_PCP_AlphabetReductionLemmas`, `UniqueGames_PCP_AlphabetRetractionLemmas`, `UniqueGames_PCP_AlphabetTableBoundsLemmas`, `UniqueGames_PCP_AmplificationIteration`, `UniqueGames_PCP_AssignmentTester`, `UniqueGames_PCP_Body`, `UniqueGames_PCP_CayleySampling`, `UniqueGames_PCP_CayleyTailCount`, `UniqueGames_PCP_ClauseVerifierLemmas`, `UniqueGames_PCP_CleanupLemmas`, `UniqueGames_PCP_Clone100`, `UniqueGames_PCP_Clone100Triples`, `UniqueGames_PCP_CloudRoundingLemmas`, `UniqueGames_PCP_CodeComposition`, `UniqueGames_PCP_CompareLoop`, `UniqueGames_PCP_EmitRows`, `UniqueGames_PCP_Emitter`, `UniqueGames_PCP_ExpanderTables`, `UniqueGames_PCP_ExpandersLemmas`, `UniqueGames_PCP_FinalBooleanVerifier`, `UniqueGames_PCP_FinalConstantsLemmas`, `UniqueGames_PCP_FoldedEquationLemmas`, `UniqueGames_PCP_FourierResponseLemmas`, `UniqueGames_PCP_GenericGraphTables`, `UniqueGames_PCP_GraphTables`, `UniqueGames_PCP_HonestTestLemmas`, `UniqueGames_PCP_InitialGraphLemmas`, `UniqueGames_PCP_InputLemmas`, `UniqueGames_PCP_LoopInitializationLemmas`, `UniqueGames_PCP_NameCompaction`, `UniqueGames_PCP_OverlayLemmas`, `UniqueGames_PCP_PoweringLabelsLemmas`, `UniqueGames_PCP_PoweringOpinionTables`, `UniqueGames_PCP_PoweringOpinionsLemmas`, `UniqueGames_PCP_PoweringPortReindexLemmas`, `UniqueGames_PCP_PoweringTableLayout`, `UniqueGames_PCP_PoweringTableSemanticsLemmas`, `UniqueGames_PCP_PoweringTablesLemmas`, `UniqueGames_PCP_Preprocessing`, `UniqueGames_PCP_PreprocessingPaddingOffsets`, `UniqueGames_PCP_PreprocessingRegularLoopWordsLemmas`, `UniqueGames_PCP_PreprocessingRegularSoundness`, `UniqueGames_PCP_PreprocessingTableSpectral`, `UniqueGames_PCP_PreprocessingTablesLemmas`, `UniqueGames_PCP_RawInitialMachineFinish`, `UniqueGames_PCP_RawInitialMachineLoopData`, `UniqueGames_PCP_RawInitialMachinePhases`, `UniqueGames_PCP_RawInitialMachineRows`, `UniqueGames_PCP_RawInitialMachineStart`, `UniqueGames_PCP_RawInitialTablesLemmas`, `UniqueGames_PCP_RuntimeModel`, `UniqueGames_PCP_Setup`, `UniqueGames_PCP_SourceContextClear`, `UniqueGames_PCP_SourceDescriptorEmissionLemmas`, `UniqueGames_PCP_SourceFieldArrayLemmas`, `UniqueGames_PCP_SourceGapLemmas`, `UniqueGames_PCP_SourceHeaderCounts`, `UniqueGames_PCP_SourceHonestLemmas`, `UniqueGames_PCP_SourceIncidence`, `UniqueGames_PCP_SourceLoopInitLemmas`, `UniqueGames_PCP_SourceNoiseParameterLemmas`, `UniqueGames_PCP_SourceOccurrences`, `UniqueGames_PCP_SourceQueryLoopLemmas`, `UniqueGames_PCP_SourceTupleBody`, `UniqueGames_PCP_TableGapReductionLemmas`, `UniqueGames_PCP_VertexPadding`, `UniqueGames_PCP_ZigzagGraphsLemmas`, `UniqueGames_Reduction_ActualCanonicalLemmas`, `UniqueGames_Reduction_ActualSourceLemmas`, `UniqueGames_Reduction_EncodingLemmas`, `UniqueGames_Reduction_ExplicitLemmas`, `UniqueGames_Reduction_FinalParametersLemmas`, `UniqueGames_Reduction_NoiseEnumerationLemmas`, `UniqueGames_Reduction_ParameterSelection`, `UniqueGames_Soundness_ActualCanonicalPullbackLemmas`, `UniqueGames_Soundness_ActualPointAnswers`, `UniqueGames_Soundness_ConditionalLocality`, `UniqueGames_Soundness_ConditionalSimulationLemmas`, `UniqueGames_Soundness_ExpectationComparisonLemmas`, `UniqueGames_Soundness_PartnerLinearLemmas`, `UniqueGames_Soundness_PartnerMapCoordinates`, `UniqueGames_Soundness_RawTargetLawLemmas`, `UniqueGames_Soundness_ZeroInformationLemmas`.
--
--   **Imports.** It imports the published bundle `Def_UniqueGamesTheorem`; the bundles `OAIQ086U000`, `OAIQ086U001` and `OAIQ086U002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ086U008` and `OAIQ086U009`; the proof of `OAI_UniqueGamesTheorem_Gadget_exists_split_gadget`.
-- source:
--   OpenAI, The Unique Games Theorem, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Unique-Games-Theorem-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_UniqueGamesTheorem
import Definitions.Def_OAIQ086U000
import Definitions.Def_OAIQ086U001
import Definitions.Def_OAIQ086U002

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_MatrixRestrictions
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Fourier.MatrixRestrictions

open UniqueGamesTheorem.Integration.BinaryLinear
open scoped BigOperators

variable {E C : Type*} [AddCommGroup E] [Module F2 E]
    [AddCommGroup C] [Module F2 C]

/-- A dual map killed by the quotient has a unique factor with values in `W`.
This is the exact finite object counted in the parity argument of Lemma 5.3. -/
def quotientKernelEquiv (W : Submodule F2 E) :
    {T : C →ₗ[F2] E // W.mkQ.comp T = 0} ≃ (C →ₗ[F2] W) where
  toFun T := T.val.codRestrict W (fun x => by
    apply (Submodule.Quotient.mk_eq_zero W).mp
    exact congrArg (fun f : C →ₗ[F2] (E ⧸ W) => f x) T.property)
  invFun T := ⟨W.subtype.comp T, by
    apply LinearMap.ext
    intro x
    exact (Submodule.Quotient.mk_eq_zero W).mpr (T x).property⟩
  left_inv T := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    rfl
  right_inv T := by
    apply LinearMap.ext
    intro x
    rfl

end UniqueGamesTheorem.Fourier.MatrixRestrictions

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_MatrixEnergy
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Fourier.MatrixEnergy

open scoped BigOperators

variable {Q : Type*} {I : Q → Type*} [Fintype Q] [∀ q, Fintype (I q)]

section LinearMaps

open MatrixCharacters MatrixFourier

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- Fourier coefficient array for a family of labelings, including color as
part of the component index. -/
noncomputable def labelingCoeff {Y : Type*}
    (label : Q → (E →ₗ[F2] F) → Y) (qy : Q × Y) (S : F →ₗ[F2] E) : ℝ :=
  linearCoeff (colorIndicator (label qy.1) qy.2) S

end LinearMaps

end UniqueGamesTheorem.Fourier.MatrixEnergy

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_MatrixNoiseLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The actual rank-one averaging operator on finite binary matrix spaces.
The outer weights describe any finite law for `v`; the functional `ℓ` is
uniform. Normalization is needed for eigenvalue bounds, not diagonalization. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace UniqueGamesTheorem.Fourier.MatrixNoise

open scoped BigOperators Matrix
open UniqueGamesTheorem.Integration.BinaryLinear (Vector)
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier

section LinearMaps

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

def linearNoiseOperator [Fintype F] [Fintype (E →ₗ[F2] F2)]
    (weight : F → ℝ) (f : (E →ₗ[F2] F) → ℂ) (X : E →ₗ[F2] F) : ℂ :=
  ∑ v, (weight v : ℂ) * (𝔼 ℓ : E →ₗ[F2] F2, f (X + ℓ.smulRight v))

/-- Weighted probability that the dual map annihilates the sampled noise vector. -/
def linearNoiseEigenvalue [Fintype F] (weight : F → ℝ) (S : F →ₗ[F2] E) : ℝ :=
  ∑ v, weight v * if S v = 0 then 1 else 0

def linearRealNoiseOperator [Fintype F] [Fintype (E →ₗ[F2] F2)]
    (weight : F → ℝ) (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) : ℝ :=
  ∑ v, weight v * (𝔼 ℓ : E →ₗ[F2] F2, f (X + ℓ.smulRight v))

end LinearMaps

end UniqueGamesTheorem.Fourier.MatrixNoise

end

end

section

/-! Products and the fourth moment for the actual binary trace Fourier model. -/

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixProducts

open scoped BigOperators
open MatrixCharacters MatrixFourier

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]

variable [Fintype (E →ₗ[F2] F)]

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (F →ₗ[F2] E)]

/-- Frequency convolution, with counting measure on the frequency space. -/
def coefficientConvolution (f g : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) : ℝ :=
  ∑ T : F →ₗ[F2] E, linearCoeff f T * linearCoeff g (S + T)

end UniqueGamesTheorem.Fourier.MatrixProducts

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_FiniteTrialsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finite two-player games with actual joint question distributions.

An answer function receives only its own player's question. In a repeated game,
that question is the entire tuple, so a repeated strategy need not act separately
on coordinates. The predicate may reject invalid answers depending on questions.
All probabilities below are actual finite sums of real weights.
-/

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators

noncomputable section

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

/-- Local question reconstruction and answer decoding never expose the other
player's question to a strategy. Any fixed advice is an ordinary fixed parameter
of these functions. -/
def simulatedStrategy {R₁ R₂ B₁ B₂ : Type*}
    (questionMap₁ : Q₁ → R₁) (questionMap₂ : Q₂ → R₂)
    (answerMap₁ : Q₁ → B₁ → A₁) (answerMap₂ : Q₂ → B₂ → A₂)
    (strategy : Strategy R₁ R₂ B₁ B₂) : Strategy Q₁ Q₂ A₁ A₂ :=
  (fun x => answerMap₁ x (strategy.1 (questionMap₁ x)),
   fun y => answerMap₂ y (strategy.2 (questionMap₂ y)))

end Game

end

end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_Conditioning
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Conditioning of actual finite distributions and the selected-coordinate chain
rule used in parallel repetition. A normalized conditional distribution is only
constructed when the conditioning event has strictly positive probability.
-/

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators

noncomputable section

namespace FiniteDistribution

variable {Ω : Type*} [Fintype Ω]

theorem probability_inter_eq_mul_conditional (μ : FiniteDistribution Ω)
    (given event : Ω → Bool) (positive : 0 < μ.probability given) :
    μ.probability (fun x => given x && event x) =
      μ.probability given * (μ.condition given positive).probability event := by
  have h := (eq_div_iff (ne_of_gt positive)).mp
    (μ.probability_condition given event positive)
  simpa only [mul_comm] using h.symm

end FiniteDistribution

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  {n : Nat}

theorem selectedWins_insert (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (coordinate : Fin n) :
    G.selectedWins strategy (insert coordinate selected) =
      fun questions =>
        G.selectedWins strategy selected questions && G.coordinateWin strategy coordinate questions := by
  classical
  funext questions
  apply Bool.eq_iff_iff.mpr
  simp [selectedWins, and_comm]

theorem selectedSuccess_insert (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (coordinate : Fin n)
    (positive : 0 < G.selectedSuccess strategy selected) :
    G.selectedSuccess strategy (insert coordinate selected) =
      G.selectedSuccess strategy selected *
        ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).probability
          (G.coordinateWin strategy coordinate) := by
  unfold selectedSuccess
  rw [G.selectedWins_insert]
  exact (G.repetition n).questions.probability_inter_eq_mul_conditional _ _ positive

end Game

end

end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_MixtureLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Finite shared randomness is an actual convex mixture of distributions. -/

namespace UniqueGamesTheorem.Foundations.Games.FiniteDistribution

open scoped BigOperators
noncomputable section

variable {Seed Ω : Type*} [Fintype Seed] [Fintype Ω]

def mixture (seedLaw : FiniteDistribution Seed)
    (laws : Seed → FiniteDistribution Ω) : FiniteDistribution Ω where
  weight x := ∑ seed, seedLaw.weight seed * (laws seed).weight x
  nonnegative x := Finset.sum_nonneg fun seed _ =>
    mul_nonneg (seedLaw.nonnegative seed) ((laws seed).nonnegative x)
  normalized := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (laws _).normalized, mul_one]
    exact seedLaw.normalized

theorem probability_mixture (seedLaw : FiniteDistribution Seed)
    (laws : Seed → FiniteDistribution Ω) (event : Ω → Bool) :
    (seedLaw.mixture laws).probability event =
      ∑ seed, seedLaw.weight seed * (laws seed).probability event := by
  unfold probability mixture
  calc
    _ = ∑ x, ∑ seed,
        seedLaw.weight seed * (if event x then (laws seed).weight x else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      cases event x <;> simp
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro seed _
      rw [Finset.mul_sum]

theorem probability_mixture_le (seedLaw : FiniteDistribution Seed)
    (laws : Seed → FiniteDistribution Ω) (event : Ω → Bool) (bound : ℝ)
    (h : ∀ seed, (laws seed).probability event ≤ bound) :
    (seedLaw.mixture laws).probability event ≤ bound := by
  rw [probability_mixture]
  calc
    _ ≤ ∑ seed, seedLaw.weight seed * bound :=
      Finset.sum_le_sum fun seed _ =>
        mul_le_mul_of_nonneg_left (h seed) (seedLaw.nonnegative seed)
    _ = bound := by rw [← Finset.sum_mul, seedLaw.normalized, one_mul]

end
end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

end

section

/-! Exact finite total variation and its event-probability bound. -/

namespace UniqueGamesTheorem.Foundations.Games.FiniteDistribution

open scoped BigOperators
noncomputable section

variable {Ω : Type*} [Fintype Ω]

def totalVariation (μ ν : FiniteDistribution Ω) : ℝ :=
  (∑ x, |μ.weight x - ν.weight x|) / 2

/-- A one-sided event difference is bounded by half the total absolute mass
difference. Normalization is used; the full absolute-mass sum would lose a
factor of two needed in the repetition argument. -/
theorem probability_sub_le_totalVariation (μ ν : FiniteDistribution Ω)
    (event : Ω → Bool) :
    μ.probability event - ν.probability event ≤ μ.totalVariation ν := by
  have pointwise (x : Ω) :
      2 * ((if event x then μ.weight x else 0) -
        (if event x then ν.weight x else 0)) ≤
      |μ.weight x - ν.weight x| + (μ.weight x - ν.weight x) := by
    have h₁ := le_abs_self (μ.weight x - ν.weight x)
    have h₂ := neg_le_abs (μ.weight x - ν.weight x)
    cases event x <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith
  have summed := Finset.sum_le_sum (s := Finset.univ) fun x _ => pointwise x
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    μ.normalized, ν.normalized, sub_self, add_zero] at summed
  unfold probability totalVariation
  linarith

theorem probability_le_add_totalVariation (μ ν : FiniteDistribution Ω)
    (event : Ω → Bool) :
    μ.probability event ≤ ν.probability event + μ.totalVariation ν := by
  have h := μ.probability_sub_le_totalVariation ν event
  linarith

end
end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_ValueLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Question-dependent stochastic responses are derandomized by sampling complete
answer tables independently before the questions. The table law, marginal law,
and mixture identity are proved from finite products and sums. No derandomization
principle is assumed as a hypothesis or axiom.
-/

namespace UniqueGamesTheorem.Foundations.Games
open scoped BigOperators
noncomputable section

namespace Game
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]

def responseTableLaw (responses₁ : Q₁ → FiniteDistribution A₁)
    (responses₂ : Q₂ → FiniteDistribution A₂) :
    FiniteDistribution (Strategy Q₁ Q₂ A₁ A₂) := by
  classical
  exact (FiniteDistribution.table responses₁).product (FiniteDistribution.table responses₂)

end Game
end
end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_SamplingLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Exact finite sampling laws used to identify verifier distributions with repeated
game question laws. These are finite sum/product identities, not independence
assumptions about an unspecified distribution.
-/

namespace UniqueGamesTheorem.Foundations.Games.FiniteDistribution
open scoped BigOperators
noncomputable section

theorem expectation_uniform {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    (uniform Ω).expectation f = (∑ x, f x) / (Fintype.card Ω : ℝ) := by
  unfold expectation uniform
  rw [← Finset.mul_sum]
  simp [div_eq_mul_inv, mul_comm]

end
end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

end

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

theorem posterior_isProbability (p w : α → ℝ) (hp : IsProbability p)
    (hw : ∀ a, 0 ≤ w a) {z : ℝ} (hz : 0 < z)
    (hmass : ∑ a, p a * w a = z) : IsProbability (posterior p w z) := by
  constructor
  · intro a
    exact div_nonneg (mul_nonneg (hp.1 a) (hw a)) hz.le
  · simp only [posterior, div_eq_mul_inv, ← Finset.sum_mul, hmass,
      mul_inv_cancel₀ hz.ne']

theorem relativeEntropy_nonneg (p q : α → ℝ) (hp : IsProbability p)
    (hq : IsProbability q) (hs : SupportedBy p q) : 0 ≤ relativeEntropy p q := by
  have hpoint : ∀ a, p a - q a ≤ p a * Real.log (p a / q a) := by
    intro a
    by_cases hpa : p a = 0
    · simp only [hpa, zero_sub, zero_div, zero_mul]
      exact neg_nonpos.mpr (hq.1 a)
    · exact mul_log_div_ge_sub (lt_of_le_of_ne (hp.1 a) (Ne.symm hpa))
        (lt_of_le_of_ne (hq.1 a) (Ne.symm (hs a hpa)))
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simpa [relativeEntropy, Finset.sum_sub_distrib, hp.2, hq.2] using hsum

theorem posterior_relativeEntropy_le (p w : α → ℝ) (hp : IsProbability p)
    (hw : ∀ a, 0 ≤ w a) (hw_one : ∀ a, w a ≤ 1) {z : ℝ} (hz : 0 < z)
    (hmass : ∑ a, p a * w a = z) :
    relativeEntropy (posterior p w z) p ≤ Real.log (1 / z) := by
  have hpost := posterior_isProbability p w hp hw hz hmass
  have hpoint : ∀ a, posterior p w z a * Real.log (posterior p w z a / p a) ≤
      posterior p w z a * Real.log (1 / z) := by
    intro a
    by_cases hpa : posterior p w z a = 0
    · simp [hpa]
    have hpne := posterior_supportedBy p w z a hpa
    have hppos : 0 < p a := lt_of_le_of_ne (hp.1 a) (Ne.symm hpne)
    have hpostpos : 0 < posterior p w z a :=
      lt_of_le_of_ne (hpost.1 a) (Ne.symm hpa)
    have hr : posterior p w z a / p a = w a / z := by
      dsimp [posterior]
      field_simp [hpne, hz.ne']
    apply mul_le_mul_of_nonneg_left _ (hpost.1 a)
    apply Real.log_le_log (div_pos hpostpos hppos)
    rw [hr]
    exact div_le_div_of_nonneg_right (hw_one a) hz.le
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simpa only [relativeEntropy, ← Finset.sum_mul, hpost.2, one_mul] using hsum

theorem totalVariation_nonneg (p q : α → ℝ) : 0 ≤ totalVariation p q := by
  exact div_nonneg (Finset.sum_nonneg (fun a _ => abs_nonneg (p a - q a))) (by norm_num)

theorem totalVariation_symm (p q : α → ℝ) : totalVariation p q = totalVariation q p := by
  simp only [totalVariation, abs_sub_comm]

/-- Finite weighted Cauchy–Schwarz for probability weights. The summands
need not be nonnegative. -/
theorem weighted_sum_sq_le (w x : α → ℝ) (hw : IsProbability w) :
    (∑ a, w a * x a)^2 ≤ ∑ a, w a * (x a)^2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α)
    (fun a => Real.sqrt (w a)) (fun a => Real.sqrt (w a) * x a)
  have hfirst : ∀ a, Real.sqrt (w a) * (Real.sqrt (w a) * x a) = w a * x a := by
    intro a
    rw [← mul_assoc, Real.mul_self_sqrt (hw.1 a)]
  have hsecond : ∀ a, (Real.sqrt (w a) * x a)^2 = w a * (x a)^2 := by
    intro a
    rw [mul_pow, Real.sq_sqrt (hw.1 a)]
  simpa only [hfirst, hsecond, Real.sq_sqrt (hw.1 _), hw.2, one_mul] using hcs

end UniqueGamesTheorem.Foundations.Information

end

section

/-! Finite product-reference entropy decomposition, including zero-probability fibers. -/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

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

theorem conditionalKernel_isProbability
    (p : α × β → ℝ) (fallback : β → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback) (a : α) :
    IsProbability (conditionalKernel p fallback a) := by
  classical
  by_cases hm : firstMarginal p a = 0
  · simpa only [IsProbability, conditionalKernel, ite_eq_left hm] using hf
  · constructor
    · intro b
      simp only [conditionalKernel, ite_eq_right hm]
      exact div_nonneg (hp.1 (a, b))
        ((firstMarginal_isProbability p hp).1 a)
    · simp only [conditionalKernel, ite_eq_right hm, div_eq_mul_inv, ← Finset.sum_mul]
      change firstMarginal p a * (firstMarginal p a)⁻¹ = 1
      exact mul_inv_cancel₀ hm

theorem marginal_mul_conditionalKernel
    (p : α × β → ℝ) (fallback : β → ℝ)
    (hp : IsProbability p) (a : α) (b : β) :
    firstMarginal p a * conditionalKernel p fallback a b = p (a, b) := by
  classical
  by_cases hm : firstMarginal p a = 0
  · have hpoint := point_le_firstMarginal p hp a b
    rw [hm] at hpoint
    have hz : p (a, b) = 0 := le_antisymm hpoint (hp.1 (a, b))
    simp [conditionalKernel, hm, hz]
  · simp only [conditionalKernel, ite_eq_right hm]
    calc
      firstMarginal p a * (p (a, b) / firstMarginal p a)
          = p (a, b) *
              (firstMarginal p a / firstMarginal p a) := by ring
      _ = p (a, b) := by rw [div_self hm, mul_one]

theorem kernelProduct_isProbability
    (r : α → ℝ) (k : α → β → ℝ)
    (hr : IsProbability r) (hk : ∀ a, IsProbability (k a)) :
    IsProbability (fun ab : α × β => r ab.1 * k ab.1 ab.2) := by
  constructor
  · intro ab
    exact mul_nonneg (hr.1 ab.1) ((hk ab.1).1 ab.2)
  · simp only [Fintype.sum_prod_type, ← Finset.mul_sum,
      (hk _).2, mul_one, hr.2]

end UniqueGamesTheorem.Foundations.Information

end

section

/-! Exact interfaces between the information vectors and finite game laws. -/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

theorem gameLaw_isProbability (μ : Games.FiniteDistribution α) : IsProbability μ.weight :=
  ⟨μ.nonnegative, μ.normalized⟩

def toGameLaw (p : α → ℝ) (hp : IsProbability p) : Games.FiniteDistribution α where
  weight := p
  nonnegative := hp.1
  normalized := hp.2

noncomputable def gameConditionalKernel (μ : Games.FiniteDistribution (α × β))
    (fallback : Games.FiniteDistribution β) (a : α) : Games.FiniteDistribution β :=
  toGameLaw (conditionalKernel μ.weight fallback.weight a)
    (conditionalKernel_isProbability μ.weight fallback.weight
      (gameLaw_isProbability μ) (gameLaw_isProbability fallback) a)

theorem gameConditionalKernel_recombine (μ : Games.FiniteDistribution (α × β))
    (fallback : Games.FiniteDistribution β) (a : α) (b : β) :
    firstMarginal μ.weight a * (gameConditionalKernel μ fallback a).weight b =
      μ.weight (a, b) :=
  marginal_mul_conditionalKernel μ.weight fallback.weight (gameLaw_isProbability μ) a b

end UniqueGamesTheorem.Foundations.Information

end

section

/-! Statistical distance under finite kernels and event restriction. -/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

theorem totalVariation_joint_common_weights (w : α → ℝ) (p q : α → β → ℝ)
    (hw : ∀ a, 0 ≤ w a) :
    totalVariation (fun ab : α × β => w ab.1 * p ab.1 ab.2)
      (fun ab : α × β => w ab.1 * q ab.1 ab.2) =
        ∑ a, w a * totalVariation (p a) (q a) := by
  have hpoint : ∀ a b, |w a * p a b - w a * q a b| = w a * |p a b - q a b| := by
    intro a b
    rw [← mul_sub, abs_mul, abs_of_nonneg (hw a)]
  simp only [totalVariation, Fintype.sum_prod_type, hpoint, ← Finset.mul_sum,
    div_eq_mul_inv, Finset.sum_mul, mul_assoc]

theorem totalVariation_joint_common_kernel (p q : α → ℝ) (k : α → β → ℝ)
    (hk : ∀ a, IsProbability (k a)) :
    totalVariation (fun ab : α × β => p ab.1 * k ab.1 ab.2)
      (fun ab : α × β => q ab.1 * k ab.1 ab.2) = totalVariation p q := by
  have hpoint : ∀ a b, |p a * k a b - q a * k a b| = |p a - q a| * k a b := by
    intro a b
    rw [← sub_mul, abs_mul, abs_of_nonneg ((hk a).1 b)]
  simp only [totalVariation, Fintype.sum_prod_type, hpoint, ← Finset.mul_sum,
    (hk _).2, mul_one]

theorem weighted_coordinate_sum_sq_le
    (w : α → ℝ) (d : α → β → ℝ) (C : α → ℝ)
    (hw : IsProbability w)
    (hbudget : ∀ a, w a * (∑ b, d a b ^ 2) ≤ w a * C a) :
    (∑ b, ∑ a, w a * d a b)^2 ≤
      (Fintype.card β : ℝ) * (∑ a, w a * C a) := by
  have hv := Finset.sum_le_sum
    (fun b (_ : b ∈ (Finset.univ : Finset β)) =>
      weighted_sum_sq_le w (fun a => d a b) hw)
  have he :
      (∑ b, ∑ a, w a * d a b ^ 2) =
        ∑ a, w a * (∑ b, d a b ^ 2) := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [he] at hv
  have hb := Finset.sum_le_sum
    (fun a (_ : a ∈ (Finset.univ : Finset α)) => hbudget a)
  have hs := hv.trans hb
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset β)
    (fun b => ∑ a, w a * d a b) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one] at hcs
  calc
    (∑ b, ∑ a, w a * d a b)^2
        ≤ (∑ b, (∑ a, w a * d a b)^2) *
            (Fintype.card β : ℝ) := hcs
    _ = (Fintype.card β : ℝ) *
          (∑ b, (∑ a, w a * d a b)^2) := mul_comm _ _
    _ ≤ (Fintype.card β : ℝ) * (∑ a, w a * C a) :=
      mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)

end UniqueGamesTheorem.Foundations.Information

end

section

/-! Finite log-sum estimates, including the side-information entropy budget. -/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {α : Type*} [Fintype α]

theorem normalize_isProbability (b : α → ℝ) (hb : ∀ a, 0 ≤ b a)
    {B : ℝ} (hB : 0 < B) (hmass : ∑ a, b a = B) :
    IsProbability (fun a => b a / B) := by
  constructor
  · intro a
    exact div_nonneg (hb a) hB.le
  · simp only [div_eq_mul_inv, ← Finset.sum_mul, hmass, mul_inv_cancel₀ hB.ne']

theorem relativeEntropy_normalize_right (p b : α → ℝ) (hp : IsProbability p)
    (hs : SupportedBy p b) {B : ℝ} (hB : 0 < B) :
    relativeEntropy p (fun a => b a / B) = relativeEntropy p b + Real.log B := by
  have hpoint : ∀ a, p a * Real.log (p a / (b a / B)) =
      p a * Real.log (p a / b a) + p a * Real.log B := by
    intro a
    by_cases hpa : p a = 0
    · simp [hpa]
    have hbne := hs a hpa
    rw [Real.log_div hpa (div_ne_zero hbne hB.ne'), Real.log_div hbne hB.ne',
      Real.log_div hpa hbne]
    ring
  simp only [relativeEntropy, hpoint, Finset.sum_add_distrib, ← Finset.sum_mul, hp.2, one_mul]

theorem neg_relativeEntropy_le_log_mass (p b : α → ℝ) (hp : IsProbability p)
    (hb : ∀ a, 0 ≤ b a) (hs : SupportedBy p b) {B : ℝ} (hB : 0 < B)
    (hmass : ∑ a, b a = B) : -relativeEntropy p b ≤ Real.log B := by
  have hs' : SupportedBy p (fun a => b a / B) :=
    fun a ha => div_ne_zero (hs a ha) hB.ne'
  have hnonneg := relativeEntropy_nonneg p (fun a => b a / B) hp
    (normalize_isProbability b hb hB hmass) hs'
  rw [relativeEntropy_normalize_right p b hp hs hB] at hnonneg
  linarith

/-- Entropy budget for a finite posterior indexed by side information.
The baseline masses `b` may have total mass `B`, rather than one. In the
application, `b(t,v)=P_T(t)` and `B` is the number of possible side labels. -/
theorem posterior_weighted_log_inverse_le (p b c : α → ℝ) (hp : IsProbability p)
    (hb : ∀ a, 0 ≤ b a) {z B : ℝ} (hz : 0 < z) (hB : 0 < B)
    (hmass : ∑ a, b a = B) (hpost : ∀ a, p a = b a * c a / z) :
    (∑ a, p a * Real.log (1 / c a)) ≤ Real.log (B / z) := by
  have hs : SupportedBy p b := by
    intro a ha hba
    apply ha
    rw [hpost, hba, zero_mul, zero_div]
  have hpoint : ∀ a, p a * Real.log (1 / c a) =
      p a * Real.log (1 / z) - p a * Real.log (p a / b a) := by
    intro a
    by_cases hpa : p a = 0
    · simp [hpa]
    have hbne := hs a hpa
    have hcne : c a ≠ 0 := by
      intro hca
      apply hpa
      rw [hpost, hca, mul_zero, zero_div]
    have hratio : p a / b a = c a / z := by
      rw [hpost]
      field_simp [hbne, hz.ne']
    rw [hratio, Real.log_div hcne hz.ne', Real.log_div one_ne_zero hcne,
      Real.log_div one_ne_zero hz.ne', Real.log_one]
    ring
  have hid : (∑ a, p a * Real.log (1 / c a)) =
      Real.log (1 / z) - relativeEntropy p b := by
    simp only [hpoint, Finset.sum_sub_distrib, ← Finset.sum_mul, hp.2, one_mul,
      relativeEntropy]
  have hkl := neg_relativeEntropy_le_log_mass p b hp hb hs hB hmass
  rw [hid, Real.log_div hB.ne' hz.ne', Real.log_div one_ne_zero hz.ne', Real.log_one]
  linarith

end UniqueGamesTheorem.Foundations.Information

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_PinskerLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

theorem hellingerSquared_le_relativeEntropy (p q : α → ℝ) (hp : IsProbability p)
    (hq : IsProbability q) (hs : SupportedBy p q) :
    hellingerSquared p q ≤ relativeEntropy p q := by
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) =>
    sqrt_distance_le_relativeEntropy_term (hp.1 a) (hq.1 a) (hs a))
  simpa only [hellingerSquared, relativeEntropy, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, hp.2, hq.2, sub_add_cancel] using hsum

theorem totalVariation_sq_le_hellingerSquared (p q : α → ℝ) (hp : IsProbability p)
    (hq : IsProbability q) : totalVariation p q ^ 2 ≤ hellingerSquared p q := by
  have hfactor : ∀ a, |Real.sqrt (p a) - Real.sqrt (q a)| *
      (Real.sqrt (p a) + Real.sqrt (q a)) = |p a - q a| := by
    intro a
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
      ← abs_mul]
    congr 1
    nlinarith [Real.sq_sqrt (hp.1 a), Real.sq_sqrt (hq.1 a)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α)
    (fun a => |Real.sqrt (p a) - Real.sqrt (q a)|)
    (fun a => Real.sqrt (p a) + Real.sqrt (q a))
  simp only [hfactor, sq_abs] at hcs
  have hpoint : ∀ a, (Real.sqrt (p a) + Real.sqrt (q a)) ^ 2 ≤ 2 * (p a + q a) := by
    intro a
    nlinarith [sq_nonneg (Real.sqrt (p a) - Real.sqrt (q a)),
      Real.sq_sqrt (hp.1 a), Real.sq_sqrt (hq.1 a)]
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, hp.2, hq.2] at hsum
  have hnonneg : 0 ≤ ∑ a, (Real.sqrt (p a) - Real.sqrt (q a)) ^ 2 :=
    Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hsum hnonneg
  dsimp [totalVariation, hellingerSquared]
  nlinarith

theorem totalVariation_sq_le_relativeEntropy (p q : α → ℝ) (hp : IsProbability p)
    (hq : IsProbability q) (hs : SupportedBy p q) :
    totalVariation p q ^ 2 ≤ relativeEntropy p q :=
  (totalVariation_sq_le_hellingerSquared p q hp hq).trans
    (hellingerSquared_le_relativeEntropy p q hp hq hs)

end UniqueGamesTheorem.Foundations.Information

end

section

/-! Tensorization and conditioning for finite independent coordinates. -/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]

theorem coordinateMarginal_isProbability (p : (ι → α) → ℝ) (hp : IsProbability p) (i : ι) :
    IsProbability (coordinateMarginal p i) := by
  classical
  constructor
  · intro a
    apply Finset.sum_nonneg
    intro x _
    split_ifs
    · exact hp.1 x
    · exact le_rfl
  · simp only [coordinateMarginal]
    rw [Finset.sum_comm]
    simpa using hp.2

theorem point_le_coordinateMarginal (p : (ι → α) → ℝ) (hp : IsProbability p)
    (i : ι) (x : ι → α) : p x ≤ coordinateMarginal p i (x i) := by
  classical
  have h := Finset.single_le_sum
    (f := fun y : ι → α => if y i = x i then p y else 0)
    (fun y _ => by split_ifs; exact hp.1 y; exact le_rfl) (Finset.mem_univ x)
  simpa [coordinateMarginal] using h

theorem independentProduct_isProbability (q : ι → α → ℝ) (hq : ∀ i, IsProbability (q i)) :
    IsProbability (independentProduct q) := by
  classical
  constructor
  · intro x
    exact Finset.prod_nonneg (fun i _ => (hq i).1 (x i))
  · simp only [independentProduct, ← Fintype.prod_sum, (hq _).2, Finset.prod_const_one]

theorem joint_supportedBy_product_coordinateMarginals (p : (ι → α) → ℝ)
    (hp : IsProbability p) : SupportedBy p (independentProduct (coordinateMarginal p)) := by
  intro x hx
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact ne_of_gt ((lt_of_le_of_ne (hp.1 x) (Ne.symm hx)).trans_le
    (point_le_coordinateMarginal p hp i x))

theorem relativeEntropy_independent_reference (p : (ι → α) → ℝ) (q : ι → α → ℝ)
    (hp : IsProbability p) (_hq : ∀ i, IsProbability (q i))
    (hs : ∀ i, SupportedBy (coordinateMarginal p i) (q i)) :
    relativeEntropy p (independentProduct q) =
      relativeEntropy p (independentProduct (coordinateMarginal p)) +
        ∑ i, relativeEntropy (coordinateMarginal p i) (q i) := by
  classical
  have hpoint : ∀ x : ι → α, p x * Real.log (p x / independentProduct q x) =
      p x * Real.log (p x / independentProduct (coordinateMarginal p) x) +
        ∑ i, p x * Real.log (coordinateMarginal p i (x i) / q i (x i)) := by
    intro x
    by_cases hx : p x = 0
    · simp [hx]
    have hm : ∀ i, coordinateMarginal p i (x i) ≠ 0 := by
      intro i
      exact ne_of_gt ((lt_of_le_of_ne (hp.1 x) (Ne.symm hx)).trans_le
        (point_le_coordinateMarginal p hp i x))
    have hqne : ∀ i, q i (x i) ≠ 0 := fun i => hs i (x i) (hm i)
    have hmp : (∏ i, coordinateMarginal p i (x i)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => hm i)
    have hqp : (∏ i, q i (x i)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => hqne i)
    simp only [independentProduct, Real.log_div hx hmp, Real.log_div hx hqp,
      Real.log_prod (fun i _ => hm i), Real.log_prod (fun i _ => hqne i)]
    simp_rw [Real.log_div (hm _) (hqne _)]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    ring
  calc
    relativeEntropy p (independentProduct q) =
        ∑ x, (p x * Real.log (p x / independentProduct (coordinateMarginal p) x) +
          ∑ i, p x * Real.log (coordinateMarginal p i (x i) / q i (x i))) := by
      exact Finset.sum_congr rfl (fun x _ => hpoint x)
    _ = relativeEntropy p (independentProduct (coordinateMarginal p)) +
        ∑ i, ∑ x, p x * Real.log (coordinateMarginal p i (x i) / q i (x i)) := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      rfl
    _ = relativeEntropy p (independentProduct (coordinateMarginal p)) +
        ∑ i, relativeEntropy (coordinateMarginal p i) (q i) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact marginal_expectation p i (fun a => Real.log (coordinateMarginal p i a / q i a))

theorem coordinate_relativeEntropy_sum_le (p : (ι → α) → ℝ) (q : ι → α → ℝ)
    (hp : IsProbability p) (hq : ∀ i, IsProbability (q i))
    (hs : ∀ i, SupportedBy (coordinateMarginal p i) (q i)) :
    (∑ i, relativeEntropy (coordinateMarginal p i) (q i)) ≤
      relativeEntropy p (independentProduct q) := by
  rw [relativeEntropy_independent_reference p q hp hq hs]
  exact le_add_of_nonneg_left (relativeEntropy_nonneg _ _ hp
    (independentProduct_isProbability _ (coordinateMarginal_isProbability p hp))
    (joint_supportedBy_product_coordinateMarginals p hp))

theorem coordinate_totalVariation_sq_sum_le (p : (ι → α) → ℝ) (q : ι → α → ℝ)
    (hp : IsProbability p) (hq : ∀ i, IsProbability (q i))
    (hs : ∀ i, SupportedBy (coordinateMarginal p i) (q i)) :
    (∑ i, totalVariation (coordinateMarginal p i) (q i) ^ 2) ≤
      relativeEntropy p (independentProduct q) := by
  exact (Finset.sum_le_sum (fun i _ => totalVariation_sq_le_relativeEntropy _ _
    (coordinateMarginal_isProbability p hp i) (hq i) (hs i))).trans
      (coordinate_relativeEntropy_sum_le p q hp hq hs)

/-- The finite independent-coordinate conditioning inequality underlying
Holenstein Lemma 4.1, with natural logarithms. `w x` is the conditional
probability of the event given the coordinate tuple `x`. -/
theorem posterior_coordinate_totalVariation_sq_sum_le_log
    (q : ι → α → ℝ) (hq : ∀ i, IsProbability (q i)) (w : (ι → α) → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hw_one : ∀ x, w x ≤ 1) {z : ℝ} (hz : 0 < z)
    (hmass : ∑ x, independentProduct q x * w x = z) :
    (∑ i, totalVariation
      (coordinateMarginal (posterior (independentProduct q) w z) i) (q i) ^ 2) ≤
        Real.log (1 / z) := by
  have hp := independentProduct_isProbability q hq
  exact (coordinate_totalVariation_sq_sum_le _ q
    (posterior_isProbability _ w hp hw hz hmass) hq
    (posterior_coordinate_supportedBy q w z)).trans
      (posterior_relativeEntropy_le _ w hp hw hw_one hz hmass)

end UniqueGamesTheorem.Foundations.Information

end

section

/-! Finite side-information conditioning bound from tensorization and log-sum.
All zero likelihood rows have an explicit normalized fallback. -/
namespace UniqueGamesTheorem.Foundations.Information
open scoped BigOperators

theorem mass_mul_posteriorOrOriginal
    {A : Type*} [Fintype A] (p e : A → ℝ)
    (hp : IsProbability p) (he : ∀ a, 0 ≤ e a)
    {c : ℝ} (hmass : ∑ a, p a * e a = c) (x : A) :
    c * posteriorOrOriginal p e c x = p x * e x := by
  classical
  by_cases hc : 0 < c
  · simp only [posteriorOrOriginal, ite_eq_left hc, posterior]
    field_simp [hc.ne']
  · have hcnonneg : 0 ≤ c := by
      rw [← hmass]
      exact Finset.sum_nonneg (fun a _ => mul_nonneg (hp.1 a) (he a))
    have hc0 : c = 0 := le_antisymm (le_of_not_gt hc) hcnonneg
    have hpoint := Finset.single_le_sum
      (fun a (_ : a ∈ (Finset.univ : Finset A)) => mul_nonneg (hp.1 a) (he a))
      (Finset.mem_univ x)
    rw [hmass, hc0] at hpoint
    have hzero : p x * e x = 0 := le_antisymm hpoint (mul_nonneg (hp.1 x) (he x))
    simp [posteriorOrOriginal, hc0, hzero]

theorem weighted_coordinate_posterior_recombine
    {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]
    (p e : (I → A) → ℝ) (hp : IsProbability p) (he : ∀ x, 0 ≤ e x)
    {c : ℝ} (hmass : ∑ x, p x * e x = c) (b z : ℝ) (i : I) (a : A) :
    (b * c / z) * coordinateMarginal (posteriorOrOriginal p e c) i a =
      (b / z) * ∑ x, if x i = a then p x * e x else 0 := by
  classical
  simp only [coordinateMarginal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hxa : x i = a
  · simp only [ite_eq_left hxa]
    calc
      (b * c / z) * posteriorOrOriginal p e c x =
          (b / z) * (c * posteriorOrOriginal p e c x) := by ring
      _ = (b / z) * (p x * e x) := by
        rw [mass_mul_posteriorOrOriginal p e hp he hmass x]
  · simp [hxa]

variable {J I A : Type*}
variable [Fintype J] [Fintype I] [Fintype A] [DecidableEq I]

theorem side_information_bound
    (w b c : J → ℝ)
    (q : J → I → A → ℝ)
    (e : J → (I → A) → ℝ)
    (hw : IsProbability w)
    (hb : ∀ j, 0 ≤ b j)
    (hq : ∀ j i, IsProbability (q j i))
    (he : ∀ j x, 0 ≤ e j x)
    (he_one : ∀ j x, e j x ≤ 1)
    (hmass : ∀ j, ∑ x, independentProduct (q j) x * e j x = c j)
    {z B : ℝ} (hz : 0 < z) (hB : 0 < B)
    (hbase : ∑ j, b j = B)
    (hweight : ∀ j, w j = b j * c j / z) :
    (∑ i, totalVariation
      (fun ja : J × A => w ja.1 * coordinateMarginal
        (posteriorOrOriginal (independentProduct (q ja.1))
          (e ja.1) (c ja.1)) i ja.2)
      (fun ja : J × A => w ja.1 * q ja.1 i ja.2)) ≤
      Real.sqrt ((Fintype.card I : ℝ) * Real.log (B / z)) := by
  classical
  let d : J → I → ℝ := fun j i => totalVariation
    (coordinateMarginal
      (posteriorOrOriginal (independentProduct (q j)) (e j) (c j)) i)
    (q j i)
  have hbudget : ∀ j,
      w j * (∑ i, d j i ^ 2) ≤ w j * Real.log (1 / c j) := by
    intro j
    by_cases hwzero : w j = 0
    · simp [hwzero]
    have hcne : c j ≠ 0 := by
      intro hczero
      apply hwzero
      rw [hweight j, hczero, mul_zero, zero_div]
    have hcnonneg : 0 ≤ c j := by
      rw [← hmass j]
      exact Finset.sum_nonneg (fun x _ => mul_nonneg
        ((independentProduct_isProbability (q j) (hq j)).1 x) (he j x))
    have hcpos : 0 < c j := lt_of_le_of_ne hcnonneg (Ne.symm hcne)
    have hlocal := posterior_coordinate_totalVariation_sq_sum_le_log
      (q j) (hq j) (e j) (he j) (he_one j) hcpos (hmass j)
    have hweighted := mul_le_mul_of_nonneg_left hlocal (hw.1 j)
    simpa only [d, posteriorOrOriginal, ite_eq_left hcpos] using hweighted
  have hcs := weighted_coordinate_sum_sq_le
    w d (fun j => Real.log (1 / c j)) hw hbudget
  have hlog := posterior_weighted_log_inverse_le w b c hw hb hz hB hbase hweight
  have hsq : (∑ i, ∑ j, w j * d j i)^2 ≤
      (Fintype.card I : ℝ) * Real.log (B / z) :=
    hcs.trans (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _))
  have htv : ∀ i, totalVariation
      (fun ja : J × A => w ja.1 * coordinateMarginal
        (posteriorOrOriginal (independentProduct (q ja.1))
          (e ja.1) (c ja.1)) i ja.2)
      (fun ja : J × A => w ja.1 * q ja.1 i ja.2) =
      ∑ j, w j * d j i := by
    intro i
    exact totalVariation_joint_common_weights w
      (fun j => coordinateMarginal
        (posteriorOrOriginal (independentProduct (q j)) (e j) (c j)) i)
      (fun j => q j i) hw.1
  simp_rw [htv]
  have hradicand : 0 ≤ (Fintype.card I : ℝ) * Real.log (B / z) :=
    (sq_nonneg _).trans hsq
  have hsqrt := Real.sq_sqrt hradicand
  have hsqrt_nonneg := Real.sqrt_nonneg ((Fintype.card I : ℝ) * Real.log (B / z))
  nlinarith

variable {T V : Type*} [Fintype T] [Fintype V] [Nonempty V]

/-- Finite Corollary 4.3 in natural-log normalization, for actual likelihood
profiles of the event jointly with the finite side label. -/
theorem finite_side_information_bound
    (pT : T → ℝ) (q : T → I → A → ℝ)
    (e : T × V → (I → A) → ℝ) (c w : T × V → ℝ)
    (hpT : IsProbability pT)
    (hq : ∀ t i, IsProbability (q t i))
    (he : ∀ tv x, 0 ≤ e tv x)
    (he_sum : ∀ t x, (∑ v, e (t, v) x) ≤ 1)
    (hc : ∀ tv, ∑ x, independentProduct (q tv.1) x * e tv x = c tv)
    {z : ℝ} (hz : 0 < z)
    (hZ : ∑ tv, pT tv.1 * c tv = z)
    (hweight : ∀ tv, w tv = pT tv.1 * c tv / z) :
    (∑ i, totalVariation
      (fun tva : (T × V) × A => w tva.1 * coordinateMarginal
        (posteriorOrOriginal (independentProduct (q tva.1.1))
          (e tva.1) (c tva.1)) i tva.2)
      (fun tva : (T × V) × A => w tva.1 * q tva.1.1 i tva.2)) ≤
      Real.sqrt ((Fintype.card I : ℝ) *
        (Real.log (Fintype.card V : ℝ) + Real.log (1 / z))) := by
  classical
  have hcnonneg : ∀ tv, 0 ≤ c tv := by
    intro tv
    rw [← hc tv]
    exact Finset.sum_nonneg (fun x _ => mul_nonneg
      ((independentProduct_isProbability (q tv.1) (hq tv.1)).1 x) (he tv x))
  have hw : IsProbability w := by
    constructor
    · intro tv
      rw [hweight tv]
      exact div_nonneg (mul_nonneg (hpT.1 tv.1) (hcnonneg tv)) hz.le
    · simp_rw [hweight, div_eq_mul_inv]
      rw [← Finset.sum_mul, hZ, mul_inv_cancel₀ hz.ne']
  have he_one : ∀ tv x, e tv x ≤ 1 := by
    intro tv x
    have hsingle : e tv x ≤ ∑ v, e (tv.1, v) x :=
      Finset.single_le_sum (fun v _ => he (tv.1, v) x) (Finset.mem_univ tv.2)
    exact hsingle.trans (he_sum tv.1 x)
  have hB : 0 < (Fintype.card V : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hbase : (∑ tv : T × V, pT tv.1) = (Fintype.card V : ℝ) := by
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← Finset.mul_sum, hpT.2, mul_one]
  have h := side_information_bound w (fun tv : T × V => pT tv.1) c
    (fun tv => q tv.1) e hw (fun tv => hpT.1 tv.1) (fun tv => hq tv.1)
    he he_one hc hz hB hbase hweight
  have hlog : Real.log ((Fintype.card V : ℝ) / z) =
      Real.log (Fintype.card V : ℝ) + Real.log (1 / z) := by
    rw [Real.log_div hB.ne' hz.ne', Real.log_div one_ne_zero hz.ne', Real.log_one]
    ring
  simpa only [hlog] using h

end UniqueGamesTheorem.Foundations.Information

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineSubroutineLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.MachineStateFrame

open Turing

variable {K Λ Λ' σ τ : Type} {Γ : K → Type}

variable [DecidableEq K]

theorem stepAux_simulation (labels : Λ → Λ') (exit : Option Λ')
    (q : TM2.Stmt Γ Λ σ) (state : σ) (ambient : τ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (statement labels exit q) (state, ambient) tapes =
      configuration labels exit ambient (TM2.stepAux q state tapes) := by
  rw [statement, MachineSubroutine.stepAux_simulation, frame_stepAux]
  rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineStateFrame

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity

def formulaEncoding : Computability.Encoding Target.Formula Bool where
  encode := formulaBits
  decode := decodeFormulaBits
  decode_encode := decodeFormulaBits_encoded

open Target

end UniqueGamesTheorem.Foundations.Complexity

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_ActualCanonicalLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.ActualCanonical

open Integration.BinaryLinear ActualHomogeneous
open scoped BigOperators

universe u v w
variable {Name : Type u} {Id : Type v} {R : Type w}
variable {k : Nat}
variable [AddCommGroup R] [Module F2 R] [DecidableEq R]

def Represents (b : Fin k → F2) (z : R) (a : Fin k → Fin 3 → R)
    (X : E k →ₗ[F2] R) : Prop := ∀ x, ambientEval b z a x = X x

end UniqueGamesTheorem.Reduction.ActualCanonical

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Soundness_ZeroInformationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalSimulation.firstInputFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
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

/-- The first reconstruction receives only fixed outside occurrence/name data,
the fixed raw coefficients, and the inside occurrence draw. -/
noncomputable def reconstructFirst {P R O N : Type} (positions : List P)
    (single hidden : P → Bool) (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (name : O → Fin 3 → N) (insideOccurrences outsideOccurrences : P → O)
    (outsideNames : P → N) : FirstInput P R O :=
  firstInput positions single zeta0 zeta1 zeta2 omega
    (reconstructQuestion hidden insideOccurrences outsideOccurrences)
    (fun j => decodeIndex name (outsideOccurrences j) (outsideNames j))

/-- The second reconstruction receives no inside occurrence: only inside names. -/
def reconstructSecond {P R O N : Type} (positions : List P)
    (single hidden : P → Bool) (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (outsideOccurrences : P → O) (insideNames outsideNames : P → N) : SecondInput P R O N :=
  secondInput positions single zeta0 zeta1 zeta2 omega outsideOccurrences
    (reconstructQuestion hidden insideNames outsideNames)

end UniqueGamesTheorem.Soundness.ZeroInformation

open scoped BigOperators

namespace UniqueGamesTheorem.Soundness.ConditionalIncidences

noncomputable section

def outsideRecord {P O N : Type} (K : Finset P) (name : O → Fin 3 → N)
    (sample : Draw P O) : PositionOutside K → O × N :=
  fun j => incidence name (sample j.val)

def zeroSet {P D : Type} [DecidableEq P] [Zero D] [DecidableEq D]
    (J : Finset P) (gamma : RawCoefficients J D) : Finset P :=
  J.attach.filter (fun j => gamma (some (.inr j)) = 0) |>.map ⟨Subtype.val, Subtype.val_injective⟩

theorem mem_zeroSet {P D : Type} [DecidableEq P] [Zero D] [DecidableEq D]
    (J : Finset P) (gamma : RawCoefficients J D) (j : P) :
    j ∈ zeroSet J gamma ↔ ∃ hj : j ∈ J, gamma (some (.inr ⟨j, hj⟩)) = 0 := by
  simp [zeroSet]

abbrev RawSample {P : Type} (J : Finset P) (D O : Type) :=
  RawCoefficients J D × Draw P O

/-- H fixes gamma and the outside incidence pairs. K is a deterministic function
of gamma, so including K explicitly in H gives precisely this same event. -/
abbrev RawObservationFibre {P D O N : Type} [DecidableEq P] [Zero D] [DecidableEq D]
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N) :=
  {sample : RawSample J D O // sample.1 = gamma ∧
    outsideRecord (zeroSet J gamma) name sample.2 = observed}

instance rawObservationFibreFintype {P D O N : Type} [Fintype P] [DecidableEq P]
    [Fintype D] [Zero D] [DecidableEq D] [Fintype O]
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N) :
    Fintype (RawObservationFibre J name gamma observed) := Fintype.ofFinite _

end

end UniqueGamesTheorem.Soundness.ConditionalIncidences

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Soundness_ConditionalLocality
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalSimulation.firstInputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Complete local private inputs after fixing H

The constructors here consume only the appropriate zero-set question tuple:
occurrences for the first player, names for the second. A single reference sample
from the positive observation fibre is fixed once as part of H-dependent advice.
It supplies arbitrary padding at hidden positions and never depends on the actual
remaining sample. The reconstruction theorems prove equality of the complete
question-plus-row input, and the row maps restrict to the actual equation spaces
as shown in `ZeroInformation.supplied_map_pullback`.
-/

namespace UniqueGamesTheorem.Soundness.ConditionalIncidences

noncomputable section

def fillHidden {P X : Type} [DecidableEq P] (K : Finset P)
    (fallback : P → X) (inside : PositionInside K → X) : P → X :=
  fun j => if hj : j ∈ K then inside ⟨j, hj⟩ else fallback j

theorem zeroSet_subset {P D : Type} [DecidableEq P] [Zero D] [DecidableEq D]
    (J : Finset P) (gamma : RawCoefficients J D) : zeroSet J gamma ⊆ J := by
  intro j hj
  exact ((mem_zeroSet J gamma j).mp hj).choose

variable {P R O N : Type} [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
  (J : Finset P) (name : O → Fin 3 → N)
  (gamma : RawCoefficients J (ZeroInformation.Bits R))
  (observed : PositionOutside (zeroSet J gamma) → O × N)

def localFirstFromH (reference : RawObservationFibre J name gamma observed)
    (insideOccurrences : PositionInside (zeroSet J gamma) → O) :
    ZeroInformation.FirstInput P R O :=
  ZeroInformation.reconstructFirst Finset.univ.toList
    (membershipBool J) (membershipBool (zeroSet J gamma)) (gamma none)
    (fullCoefficient J gamma 0) (fullCoefficient J gamma 1) (singleCoefficient J gamma)
    name
    (fillHidden (zeroSet J gamma) (fun j => (reference.val.2 j).1) insideOccurrences)
    (fun j => (reference.val.2 j).1)
    (fun j => name (reference.val.2 j).1 (reference.val.2 j).2)

def localSecondFromH (reference : RawObservationFibre J name gamma observed)
    (insideNames : PositionInside (zeroSet J gamma) → N) :
    ZeroInformation.SecondInput P R O N :=
  ZeroInformation.reconstructSecond Finset.univ.toList
    (membershipBool J) (membershipBool (zeroSet J gamma)) (gamma none)
    (fullCoefficient J gamma 0) (fullCoefficient J gamma 1) (singleCoefficient J gamma)
    (fun j => (reference.val.2 j).1)
    (fillHidden (zeroSet J gamma)
      (fun j => name (reference.val.2 j).1 (reference.val.2 j).2) insideNames)
    (fun j => name (reference.val.2 j).1 (reference.val.2 j).2)

omit [DecidableEq R] in
theorem localFirstFromH_question_inside
    (reference : RawObservationFibre J name gamma observed)
    (insideOccurrences : PositionInside (zeroSet J gamma) → O)
    (j : PositionInside (zeroSet J gamma)) :
    (localFirstFromH J name gamma observed reference insideOccurrences).question j.val =
      insideOccurrences j := by
  simp [localFirstFromH, ZeroInformation.reconstructFirst, ZeroInformation.firstInput,
    ZeroInformation.reconstructQuestion, fillHidden, membershipBool, j.property]

omit [DecidableEq R] in
theorem localSecondFromH_question_inside
    (reference : RawObservationFibre J name gamma observed)
    (insideNames : PositionInside (zeroSet J gamma) → N)
    (j : PositionInside (zeroSet J gamma)) :
    (localSecondFromH J name gamma observed reference insideNames).question j.val =
      Sum.inr (insideNames j) := by
  have hjJ : j.val ∈ J := zeroSet_subset J gamma j.property
  simp [localSecondFromH, ZeroInformation.reconstructSecond, ZeroInformation.secondInput,
    ZeroInformation.partnerQuestion, ZeroInformation.reconstructQuestion,
    fillHidden, membershipBool, j.property, hjJ]

end

end UniqueGamesTheorem.Soundness.ConditionalIncidences

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Soundness_ExpectationComparisonLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Soundness.IncidenceExtraction

/-!
The next definitions separate local strategies from arbitrary joint strategies.
Each question reconstruction and each answer extraction has access to only one
player's question. A value conditioned on by an analysis may occur as a fixed
parameter of a `LocalSimulation`; it cannot become an additional random input.
-/

structure LocalSimulation
    {InnerQA InnerQB InnerA InnerB OuterQA OuterQB OuterA OuterB : Type}
    (inner : Game InnerQA InnerQB InnerA InnerB)
    (outer : Game OuterQA OuterQB OuterA OuterB) where
  questionA : InnerQA → OuterQA
  questionB : InnerQB → OuterQB
  answerA : InnerQA → OuterA → InnerA
  answerB : InnerQB → OuterB → InnerB
  sound : ∀ qa qb a b,
    outer.accepts (questionA qa) (questionB qb) a b →
    inner.accepts qa qb (answerA qa a) (answerB qb b)

def LocalSimulation.induced
    {InnerQA InnerQB InnerA InnerB OuterQA OuterQB OuterA OuterB : Type}
    {inner : Game InnerQA InnerQB InnerA InnerB}
    {outer : Game OuterQA OuterQB OuterA OuterB}
    (r : LocalSimulation inner outer)
    (s : Strategies OuterQA OuterQB OuterA OuterB) :
    Strategies InnerQA InnerQB InnerA InnerB where
  first qa := r.answerA qa (s.first (r.questionA qa))
  second qb := r.answerB qb (s.second (r.questionB qb))

end UniqueGamesTheorem.Soundness.IncidenceExtraction

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Soundness_PartnerLinearLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Soundness.PartnerLinear

open PartnerProjection
open UniqueGamesTheorem.Integration.BinaryLinear (F2 ofBit toBit scalar_cases ofBit_toBit
  toBit_ofBit ofBit_xor)

variable {P : Type} (rhs active : P → Bool) (slot : P → Slot)

noncomputable instance sourceFintype [Fintype P] : Fintype (SourcePoint rhs) := by
  classical
  exact Fintype.ofEquiv (SourceCoordinates P) (sourceEquiv rhs).symm

noncomputable instance partnerFintype [Fintype P] : Fintype (PartnerPoint rhs active) := by
  classical
  exact Fintype.ofEquiv (PartnerCoordinates active) (partnerEquiv rhs active).symm

noncomputable instance sourceFiniteDimensional [Fintype P] :
    FiniteDimensional F2 (SourcePoint rhs) :=
  (sourceLinearEquiv rhs).symm.finiteDimensional

noncomputable instance partnerFiniteDimensional [Fintype P] :
    FiniteDimensional F2 (PartnerPoint rhs active) :=
  (partnerLinearEquiv rhs active).symm.finiteDimensional

end UniqueGamesTheorem.Soundness.PartnerLinear

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Soundness_PartnerMapCoordinates
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Every partner linear map has independent raw coefficient coordinates

The coefficient index is exactly `ConditionalIncidences.RawSlot`: one global
coefficient, two coefficients at every full position, and one at every single
position.  The coordinate bijection below is for every actual partner linear
map, and its finite-uniform-law theorem has no distributional hypothesis.
-/

open scoped BigOperators

namespace UniqueGamesTheorem.Soundness.PartnerMapCoordinates

open PartnerProjection
open ConditionalIncidences (PositionInside PositionOutside RawSlot RawCoefficients )
open UniqueGamesTheorem.Integration.BinaryLinear (F2 ofBit toBit)

noncomputable section

variable {P : Type} [DecidableEq P] (rhs : P → Bool) (J : Finset P)

variable [Fintype P]

variable (R : Type) [AddCommGroup R] [Module F2 R]

instance partnerMapsFintype [Fintype R] :
    Fintype (PartnerPoint rhs (activeOf J) →ₗ[F2] R) := by
  classical
  exact Fintype.ofEquiv (RawCoefficients J R) (mapEquiv rhs J R).toEquiv

end

end UniqueGamesTheorem.Soundness.PartnerMapCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Soundness_ActualCanonicalPullbackLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Canonical-row descent for every actual partner linear map. -/

namespace UniqueGamesTheorem.Soundness.ActualCanonicalPullback

open scoped BigOperators
open PartnerProjection PartnerMapCoordinates
open ConditionalIncidences
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction

noncomputable section

variable {k : Nat} (rhsB : Fin k → Bool) (J : Finset (Fin k))
variable (R : Type) [AddCommGroup R] [Module F2 R]

def selectedFree (b : Fin k → F2) (slot : Fin k → Slot)
    (v : ActualHomogeneous.E k) (j : Fin k) : F2 :=
  match slot j with
  | .first => (v.2 j).1
  | .second => (v.2 j).2
  | .third => b j * v.1 + (v.2 j).1 + (v.2 j).2

def ambientCoefficients (gamma : RawCoefficients J R) (slot : Fin k → Slot)
    (j : Fin k) (i : Fin 3) : R :=
  if hj : j ∈ J then
    if i = ConcreteExtraction.slotIndex (slot j) then gamma (some (.inr ⟨j,hj⟩)) else 0
  else if i = 0 then gamma (some (.inl (⟨j,hj⟩,0)))
    else if i = 1 then gamma (some (.inl (⟨j,hj⟩,1))) else 0

def freePullback (gamma : RawCoefficients J R) (slot : Fin k → Slot) :
    ActualHomogeneous.E k →ₗ[F2] R :=
  (mapEquiv rhsB J R gamma).comp
    ((PartnerLinear.projection rhsB (activeOf J) slot).comp
      (PartnerLinear.sourceLinearEquiv rhsB).symm.toLinearMap)

def outsideInsideEquiv : (PositionOutside J ⊕ PositionInside J) ≃ Fin k where
  toFun j := Sum.elim Subtype.val Subtype.val j
  invFun j := if hj : j ∈ J then Sum.inr ⟨j,hj⟩ else Sum.inl ⟨j,hj⟩
  left_inv j := by
    cases j with
    | inl j => simp [j.property]
    | inr j => simp [j.property]
  right_inv j := by
    by_cases hj : j ∈ J <;> simp [hj]

end
end UniqueGamesTheorem.Soundness.ActualCanonicalPullback

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_FactorizationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Normalized local completion laws derived from their actual product weights.
Zero rows use explicit default laws and satisfy the same recombination identity.
-/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Exact reconstruction from two separately normalized local completion
laws, valid even when either unnormalized row has mass zero. -/
theorem local_completion_recombination
    (left : X → ℝ) (right : Y → ℝ)
    (hl : ∀ x, 0 ≤ left x) (hr : ∀ y, 0 ≤ right y)
    (defaultLeft : FiniteDistribution X) (defaultRight : FiniteDistribution Y)
    (c : ℝ) (x : X) (y : Y) :
    (c * (∑ z, left z) * (∑ z, right z)) *
      ((normalizeOr left hl defaultLeft).weight x *
        (normalizeOr right hr defaultRight).weight y) = c * left x * right y := by
  calc
    _ = c * ((∑ z, left z) * (normalizeOr left hl defaultLeft).weight x) *
        ((∑ z, right z) * (normalizeOr right hr defaultRight).weight y) := by ring
    _ = _ := by rw [sum_mul_normalizeOr, sum_mul_normalizeOr]

/-- The row mass appearing in reconstruction is the actual sum of product
weights, not an assumed marginal identity. -/
theorem factorized_completion_row
    (left : X → ℝ) (right : Y → ℝ)
    (hl : ∀ x, 0 ≤ left x) (hr : ∀ y, 0 ≤ right y)
    (defaultLeft : FiniteDistribution X) (defaultRight : FiniteDistribution Y)
    (c : ℝ) (xy : X × Y) :
    (∑ z : X × Y, c * left z.1 * right z.2) *
      ((normalizeOr left hl defaultLeft).product
        (normalizeOr right hr defaultRight)).weight xy = c * left xy.1 * right xy.2 := by
  have hm : (∑ z : X × Y, c * left z.1 * right z.2) =
      c * (∑ z, left z) * (∑ z, right z) := by
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [productWeight_mass]
  rw [hm]
  exact local_completion_recombination left right hl hr defaultLeft defaultRight c xy.1 xy.2

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-!
Local embedding to single-game strategy transfer for Holenstein's argument.
The embedding law below is explicitly sampled from a finite shared seed and
the base game's actual joint question law. Its distance from the desired
conditioned law is an explicit total-variation expression. Constructing an
embedding with a sufficiently small distance is a separate proof obligation.
-/

namespace UniqueGamesTheorem.Foundations.Games.Game

noncomputable section

variable {Q₁ Q₂ A₁ A₂ R₁ R₂ B₁ B₂ Seed : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂] [Fintype Seed]
  [Nonempty A₁] [Nonempty A₂]

def localEmbeddingLaw (G : Game Q₁ Q₂ A₁ A₂)
    (seedLaw : FiniteDistribution Seed)
    (left : Seed → Q₁ → R₁) (right : Seed → Q₂ → R₂) :
    FiniteDistribution (R₁ × R₂) :=
  seedLaw.mixture fun seed =>
    G.questions.pushforward fun q => (left seed q.1, right seed q.2)

/-- A single tested coordinate under an arbitrary full-tuple question law. -/
def coordinateGame (G : Game Q₁ Q₂ A₁ A₂) {n : Nat} (coordinate : Fin n)
    (law : FiniteDistribution ((Fin n → Q₁) × (Fin n → Q₂))) :
    Game (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂) where
  questions := law
  accepts x y a b := G.accepts (x coordinate) (y coordinate) (a coordinate) (b coordinate)

end
end UniqueGamesTheorem.Foundations.Games.Game

end

section

/-! Replacing the input marginal of an actual conditional profile. -/
namespace UniqueGamesTheorem.Foundations.Repetition.ProfileCorrection
open scoped BigOperators
open UniqueGamesTheorem.Foundations.Information
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

theorem seedQuestionMarginal_isProbability (p : X × (S × Y) → ℝ)
    (hp : IsProbability p) : IsProbability (seedQuestionMarginal p) := by
  apply firstMarginal_isProbability
  constructor
  · intro z
    exact hp.1 _
  · have h := hp.2
    simp only [Fintype.sum_prod_type] at h ⊢
    exact h

theorem totalVariation_triangle {Ω : Type*} [Fintype Ω]
    (p c d : Ω → ℝ) :
    totalVariation p d ≤ totalVariation p c + totalVariation c d := by
  unfold totalVariation
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun x _ => abs_sub_le (p x) (c x) (d x))
  rw [Finset.sum_add_distrib] at h
  linarith

theorem left_profile_correction
    (p : X × (S × Y) → ℝ) (μ : X × Y → ℝ)
    (fallbackS : S → ℝ) (fallbackY : Y → ℝ)
    (hp : IsProbability p) (hμ : IsProbability μ)
    (hS : IsProbability fallbackS) (hY : IsProbability fallbackY) :
    totalVariation p (fun z => μ (z.1, z.2.2) *
      conditionalKernel (seedQuestionMarginal p) fallbackS z.1 z.2.1) ≤
    totalVariation p (fun z => seedQuestionMarginal p (z.1, z.2.1) *
      conditionalKernel μ fallbackY z.1 z.2.2) +
    totalVariation (firstMarginal p) (firstMarginal μ) := by
  let σ := seedQuestionMarginal p
  let L := conditionalKernel σ fallbackS
  let M := conditionalKernel μ fallbackY
  let k : X → S × Y → ℝ := fun x sy => L x sy.1 * M x sy.2
  let c : X × (S × Y) → ℝ := fun z => σ (z.1,z.2.1) * M z.1 z.2.2
  let d : X × (S × Y) → ℝ := fun z => μ (z.1,z.2.2) * L z.1 z.2.1
  have hσ : IsProbability σ := seedQuestionMarginal_isProbability p hp
  have hk : ∀ x, IsProbability (k x) := by
    intro x
    exact kernelProduct_isProbability (L x) (fun _ : S => M x)
      (conditionalKernel_isProbability σ fallbackS hσ hS x)
      (fun _ => conditionalKernel_isProbability μ fallbackY hμ hY x)
  have hc : c = fun z => firstMarginal σ z.1 * k z.1 z.2 := by
    funext z
    change σ (z.1,z.2.1) * M z.1 z.2.2 =
      firstMarginal σ z.1 * (L z.1 z.2.1 * M z.1 z.2.2)
    rw [← mul_assoc, marginal_mul_conditionalKernel σ fallbackS hσ]
  have hd : d = fun z => firstMarginal μ z.1 * k z.1 z.2 := by
    funext z
    change μ (z.1,z.2.2) * L z.1 z.2.1 =
      firstMarginal μ z.1 * (L z.1 z.2.1 * M z.1 z.2.2)
    calc
      _ = (firstMarginal μ z.1 * M z.1 z.2.2) * L z.1 z.2.1 := by
        rw [marginal_mul_conditionalKernel μ fallbackY hμ]
      _ = _ := by ring
  have hmiddle : totalVariation c d =
      totalVariation (firstMarginal σ) (firstMarginal μ) := by
    rw [hc, hd]
    exact totalVariation_joint_common_kernel _ _ k hk
  have result := totalVariation_triangle p c d
  rw [hmiddle] at result
  have hmarg : firstMarginal σ = firstMarginal p := seedQuestionMarginal_first p
  rw [hmarg] at result
  exact result
end
end UniqueGamesTheorem.Foundations.Repetition.ProfileCorrection

end

section

/-! The actual single-coordinate dependency-breaking reveal distribution.
The tag records which endpoint of the question pair was revealed. -/

namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem revealLaw_weight (μ : FiniteDistribution (X × Y)) (q : X × Y) (r : X ⊕ Y) :
    (revealLaw μ).weight (q,r) =
      (if r = Sum.inl q.1 then μ.weight q / 2 else 0) +
      (if r = Sum.inr q.2 then μ.weight q / 2 else 0) := by
  classical
  rcases q with ⟨x,y⟩
  simp only [revealLaw, FiniteDistribution.pushforward, FiniteDistribution.product,
    Fintype.sum_prod_type, Prod.mk.injEq, ite_and]
  simp [revealEndpoint, FiniteDistribution.uniform, div_eq_mul_inv, add_comm, eq_comm]

/-- The default row still preserves the displayed endpoint if that endpoint
has zero probability in the base question law. -/
def revealFallback (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) :
    FiniteDistribution (X × Y) :=
  match r with
  | Sum.inl x => μ.pushforward (fun q => (x,q.2))
  | Sum.inr y => μ.pushforward (fun q => (q.1,y))

def revealProfile (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) :
    FiniteDistribution (X × Y) :=
  gameConditionalKernel (revealFirstLaw μ) (revealFallback μ r) r

theorem revealProfile_inl_support (μ : FiniteDistribution (X × Y))
    (x : X) (q : X × Y) (h : q.1 ≠ x) :
    (revealProfile μ (Sum.inl x)).weight q = 0 := by
  classical
  rcases q with ⟨x',y⟩
  dsimp at h
  simp only [revealProfile, gameConditionalKernel, toGameLaw, conditionalKernel]
  split
  · simp [revealFallback, FiniteDistribution.pushforward, Fintype.sum_prod_type,
      Prod.mk.injEq, Ne.symm h]
  · simp [revealLaw_weight, Ne.symm h]

theorem revealProfile_inr_support (μ : FiniteDistribution (X × Y))
    (y : Y) (q : X × Y) (h : q.2 ≠ y) :
    (revealProfile μ (Sum.inr y)).weight q = 0 := by
  classical
  rcases q with ⟨x,y'⟩
  dsimp at h
  simp only [revealProfile, gameConditionalKernel, toGameLaw, conditionalKernel]
  split
  · simp [revealFallback, FiniteDistribution.pushforward, Fintype.sum_prod_type,
      Prod.mk.injEq, Ne.symm h]
  · simp [revealLaw_weight, Ne.symm h]

def revealInputLaw (μ : FiniteDistribution (X × Y)) : FiniteDistribution (X ⊕ Y) :=
  (revealLaw μ).pushforward Prod.snd

theorem revealInputLaw_weight (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) :
    (revealInputLaw μ).weight r = firstMarginal (revealFirstLaw μ).weight r := by
  classical
  cases r <;>
    simp [revealInputLaw, FiniteDistribution.pushforward, firstMarginal, Fintype.sum_prod_type]

/-- The conditional product representation is proved from the sampled law,
including reveal values with zero probability. -/
theorem reveal_profile_recombination (μ : FiniteDistribution (X × Y))
    (r : X ⊕ Y) (q : X × Y) :
    (revealInputLaw μ).weight r * (revealProfile μ r).weight q =
      (revealLaw μ).weight (q,r) := by
  rw [revealInputLaw_weight]
  exact gameConditionalKernel_recombine (revealFirstLaw μ) (revealFallback μ r) r q

theorem revealInputLaw_inl (μ : FiniteDistribution (X × Y)) (x : X) :
    (revealInputLaw μ).weight (Sum.inl x) = (∑ y, μ.weight (x,y)) / 2 := by
  classical
  rw [revealInputLaw_weight]
  simp [firstMarginal, Fintype.sum_prod_type, revealLaw_weight, div_eq_mul_inv]
  rw [Finset.sum_comm]
  simp [← Finset.sum_mul]

theorem revealInputLaw_inr (μ : FiniteDistribution (X × Y)) (y : Y) :
    (revealInputLaw μ).weight (Sum.inr y) = (∑ x, μ.weight (x,y)) / 2 := by
  classical
  rw [revealInputLaw_weight]
  simp [firstMarginal, Fintype.sum_prod_type, revealLaw_weight,
    div_eq_mul_inv, ← Finset.sum_mul]

theorem revealProfile_inl_diagonal (μ : FiniteDistribution (X × Y)) (x : X) (y : Y) :
    (revealProfile μ (Sum.inl x)).weight (x,y) =
      conditionalKernel μ.weight (μ.pushforward Prod.snd).weight x y := by
  classical
  have hm : firstMarginal (revealFirstLaw μ).weight (Sum.inl x) =
      firstMarginal μ.weight x / 2 := by
    rw [← revealInputLaw_weight, revealInputLaw_inl]
    rfl
  have hf : (revealFallback μ (Sum.inl x)).weight (x,y) =
      (μ.pushforward Prod.snd).weight y := by
    simp [revealFallback, FiniteDistribution.pushforward, Prod.mk.injEq]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : q.2 = y <;> simp [hq]
  simp only [revealProfile, gameConditionalKernel, toGameLaw, conditionalKernel, hm]
  by_cases h : firstMarginal μ.weight x = 0
  · simpa [h] using hf
  · have hh : firstMarginal μ.weight x / 2 ≠ 0 := div_ne_zero h (by norm_num)
    simp only [ite_eq_right h, ite_eq_right hh, revealFirstLaw_weight, revealLaw_weight,
      ite_true, if_true, Sum.inl_ne_inr, ite_false, add_zero]
    field_simp

theorem revealProfile_inr_diagonal (μ : FiniteDistribution (X × Y)) (x : X) (y : Y) :
    (revealProfile μ (Sum.inr y)).weight (x,y) =
      conditionalKernel (μ.transport (Equiv.prodComm X Y)).weight
        (μ.pushforward Prod.fst).weight y x := by
  classical
  have hm : firstMarginal (revealFirstLaw μ).weight (Sum.inr y) =
      firstMarginal (μ.transport (Equiv.prodComm X Y)).weight y / 2 := by
    rw [← revealInputLaw_weight, revealInputLaw_inr]
    rfl
  have hf : (revealFallback μ (Sum.inr y)).weight (x,y) =
      (μ.pushforward Prod.fst).weight x := by
    simp [revealFallback, FiniteDistribution.pushforward, Prod.mk.injEq]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : q.1 = x <;> simp [hq]
  simp only [revealProfile, gameConditionalKernel, toGameLaw, conditionalKernel, hm]
  by_cases h : firstMarginal (μ.transport (Equiv.prodComm X Y)).weight y = 0
  · simpa [h] using hf
  · have hh : firstMarginal (μ.transport (Equiv.prodComm X Y)).weight y / 2 ≠ 0 :=
      div_ne_zero h (by norm_num)
    simp only [ite_eq_right h, ite_eq_right hh, revealFirstLaw_weight, revealLaw_weight,
      ite_true, if_true, Sum.inr_ne_inl, ite_false, zero_add]
    change (μ.weight (x,y) / 2) / (firstMarginal (μ.transport (Equiv.prodComm X Y)).weight y / 2) =
      μ.weight (x,y) / firstMarginal (μ.transport (Equiv.prodComm X Y)).weight y
    field_simp

theorem revealLaw_sum_left (μ : FiniteDistribution (X × Y)) (q : X × Y) :
    (∑ x, (revealLaw μ).weight (q, Sum.inl x)) = μ.weight q / 2 := by
  classical
  simp [revealLaw_weight]

theorem revealLaw_sum_right (μ : FiniteDistribution (X × Y)) (q : X × Y) :
    (∑ y, (revealLaw μ).weight (q, Sum.inr y)) = μ.weight q / 2 := by
  classical
  simp [revealLaw_weight]

/-- A conditional product of independently revealed coordinates has its
exact point weight. This is the product identity used by the information
bound, derived from the single-coordinate sampled distribution. -/
theorem reveal_product_factorization {ι : Type*} [Fintype ι]
    (μ : FiniteDistribution (X × Y)) (r : ι → X ⊕ Y) (q : ι → X × Y) :
    (∏ i, (revealInputLaw μ).weight (r i)) *
      (∏ i, (revealProfile μ (r i)).weight (q i)) =
        ∏ i, (revealLaw μ).weight (q i,r i) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact reveal_profile_recombination μ (r i) (q i)

theorem reveal_product_forget {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : FiniteDistribution (X × Y)) (q : ι → X × Y) :
    (∑ r : ι → X ⊕ Y,
      (∏ i, (revealInputLaw μ).weight (r i)) *
        (∏ i, (revealProfile μ (r i)).weight (q i))) =
      ∏ i, μ.weight (q i) := by
  classical
  simp_rw [reveal_product_factorization]
  calc
    _ = ∏ i, ∑ r : X ⊕ Y, (revealLaw μ).weight (q i,r) :=
      (Fintype.prod_sum (fun (i : ι) (r : X ⊕ Y) => (revealLaw μ).weight (q i,r))).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Fintype.sum_sum_type, revealLaw_sum_left, revealLaw_sum_right]
      ring

/-- Marginalizing the reveal variables restores the original independent
question law for every observable, including the selected-win likelihood. -/
theorem reveal_product_expectation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : FiniteDistribution (X × Y)) (f : (ι → X × Y) → ℝ) :
    (∑ r : ι → X ⊕ Y,
      (∏ i, (revealInputLaw μ).weight (r i)) *
        ∑ q : ι → X × Y, (∏ i, (revealProfile μ (r i)).weight (q i)) * f q) =
      ∑ q : ι → X × Y, (∏ i, μ.weight (q i)) * f q := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  rw [reveal_product_forget]

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

namespace UniqueGamesTheorem.Foundations.Repetition

@[simp] theorem logTwo_one : logTwo 1 = 0 := by simp [logTwo]

theorem logTwo_inv_le_of_half_pow_le {p : ℝ} (m : ℕ)
    (h : (1 / 2 : ℝ) ^ m ≤ p) : logTwo (1 / p) ≤ m := by
  have hp : 0 < p := (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) m).trans_le h
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) m) h
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [Real.log_pow, hhalf] at hlog
  unfold logTwo
  rw [one_div, Real.log_inv]
  apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
  nlinarith

/-- A nonzero step below the cutoff contracts by `(1+v)/2`. -/
theorem contraction_step {v ell : ℝ} {n m : ℕ} {p next : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hell : 1 ≤ ell)
    (hm : 1 ≤ m) (hmn : m < n) (hp : 0 ≤ p)
    (hmono : next ≤ p)
    (hprev : p ≤ ((1 + v) / 2) ^ m)
    (hcut : 2700 * (m : ℝ) * ell ≤ (1 - v) ^ 2 * ((n : ℝ) - m))
    (hstep : next ≤ p * (v + 15 * Real.sqrt
      (((m : ℝ) * ell + logTwo (1 / p)) / ((n : ℝ) - m)))) :
    next ≤ ((1 + v) / 2) ^ (m + 1) := by
  by_cases hsmall : p ≤ ((1 + v) / 2) ^ (m + 1)
  · exact hmono.trans hsmall
  have hq : (1 / 2 : ℝ) ≤ (1 + v) / 2 := by linarith
  have hhalf : (1 / 2 : ℝ) ^ (m + 1) ≤ p :=
    (pow_le_pow_left₀ (by norm_num) hq (m + 1)).trans (le_of_not_ge hsmall)
  have hlog := logTwo_inv_le_of_half_pow_le (m + 1) hhalf
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : 0 < (n : ℝ) - m := by
    have hmnreal : (m : ℝ) < n := by exact_mod_cast hmn
    linarith
  have hmell : (m : ℝ) ≤ (m : ℝ) * ell := by nlinarith
  have hbudget : (m : ℝ) * ell + logTwo (1 / p) ≤ 3 * (m : ℝ) * ell := by
    simp only [Nat.cast_add, Nat.cast_one] at hlog
    nlinarith
  have hsqrt : Real.sqrt
      (((m : ℝ) * ell + logTwo (1 / p)) / ((n : ℝ) - m)) ≤ (1 - v) / 30 := by
    apply (Real.sqrt_le_left (by linarith : 0 ≤ (1 - v) / 30)).2
    apply (div_le_iff₀ hden).2
    nlinarith
  have hfactor : v + 15 * Real.sqrt
      (((m : ℝ) * ell + logTwo (1 / p)) / ((n : ℝ) - m)) ≤ (1 + v) / 2 := by
    linarith
  calc
    next ≤ p * (v + 15 * Real.sqrt
        (((m : ℝ) * ell + logTwo (1 / p)) / ((n : ℝ) - m))) := hstep
    _ ≤ p * ((1 + v) / 2) := mul_le_mul_of_nonneg_left hfactor hp
    _ ≤ ((1 + v) / 2) ^ m * ((1 + v) / 2) :=
      mul_le_mul_of_nonneg_right hprev (by linarith)
    _ = ((1 + v) / 2) ^ (m + 1) := (pow_succ _ _).symm

/-- The explicit recurrence obtained from a `15*sqrt` embedding error. -/
def ScalarRecurrence (p : ℕ → ℝ) (n : ℕ) (v ell : ℝ) : Prop :=
  ∀ m, m < n → p (m + 1) ≤ p m * (v + 15 * Real.sqrt
    (((m : ℝ) * ell + logTwo (1 / p m)) / ((n : ℝ) - m)))

/-- Induction to the ceiling of the real cutoff repairs the integer-rounding
omission in the printed scalar proof. -/
theorem decay_to_cutoff (p : ℕ → ℝ) (n : ℕ) {v ell : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hell : 1 ≤ ell)
    (hp0 : p 0 = 1) (hpnonneg : ∀ m, 0 ≤ p m)
    (hpmono : Antitone p) (hrec : ScalarRecurrence p n v ell) :
    p n ≤ ((1 + v) / 2) ^
      ((n : ℝ) * (1 - v) ^ 2 / (2925 * ell)) := by
  let T : ℝ := (n : ℝ) * (1 - v) ^ 2 / (2925 * ell)
  let M : ℕ := Nat.ceil T
  have hMn : M ≤ n := Nat.ceil_le.mpr (cutoff_le_length n hv0 hv1 hell)
  have hind : ∀ m, m ≤ M → p m ≤ ((1 + v) / 2) ^ m := by
    intro m
    induction m with
    | zero => intro _; simp [hp0]
    | succ m ih =>
        intro hmM
        have hmM' : m < M := Nat.lt_of_succ_le hmM
        have hmn : m < n := hmM'.trans_le hMn
        have hprev := ih (Nat.le_of_lt hmM')
        by_cases hm0 : m = 0
        · subst m
          have hinit : p 1 ≤ v := by
            have hs := hrec 0 hmn
            simpa [hp0] using hs
          simpa using hinit.trans (by linarith : v ≤ (1 + v) / 2)
        · have hmT : (m : ℝ) < T := Nat.lt_ceil.mp hmM'
          exact contraction_step hv0 hv1 hell (Nat.one_le_iff_ne_zero.mpr hm0)
            hmn (hpnonneg m) (hpmono (Nat.le_succ m)) hprev
            (cutoff_step hv0 hv1 hell hmT) (hrec m hmn)
  have hq0 : 0 < (1 + v) / 2 := by linarith
  have hq1 : (1 + v) / 2 ≤ 1 := by linarith
  calc
    p n ≤ p M := hpmono hMn
    _ ≤ ((1 + v) / 2) ^ M := hind M le_rfl
    _ = ((1 + v) / 2) ^ (M : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ ((1 + v) / 2) ^ T :=
      Real.rpow_le_rpow_of_exponent_ge hq0 hq1 (Nat.le_ceil T)

/-- Numerical endpoint of Holenstein's recurrence, with the published constant
6000. This theorem assumes only a concrete scalar recurrence, not any game
value bound. The derivation of that recurrence for games is separate. -/
theorem scalar_bound_6000 (p : ℕ → ℝ) (n : ℕ) {v ell : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hell : 1 ≤ ell)
    (hp0 : p 0 = 1) (hpnonneg : ∀ m, 0 ≤ p m)
    (hpmono : Antitone p) (hrec : ScalarRecurrence p n v ell) :
    p n ≤ (1 - (1 - v) ^ 3 / 6000) ^ ((n : ℝ) / ell) := by
  have hell0 : 0 < ell := by linarith
  have hq0 : 0 ≤ (1 + v) / 2 := by linarith
  have hexp : 0 ≤ (n : ℝ) / ell := by positivity
  have hblock := block_contraction hv0 hv1
  have hweak : 1 - (1 - v) ^ 3 / 5850 ≤ 1 - (1 - v) ^ 3 / 6000 := by
    have : 0 ≤ (1 - v) ^ 3 := by positivity
    nlinarith
  calc
    p n ≤ ((1 + v) / 2) ^
        ((n : ℝ) * (1 - v) ^ 2 / (2925 * ell)) :=
      decay_to_cutoff p n hv0 hv1 hell hp0 hpnonneg hpmono hrec
    _ = (((1 + v) / 2) ^ ((1 - v) ^ 2 / 2925 : ℝ)) ^ ((n : ℝ) / ell) := by
      rw [← Real.rpow_mul hq0]
      congr 1
      ring
    _ ≤ (1 - (1 - v) ^ 3 / 6000) ^ ((n : ℝ) / ell) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hq0 _) (hblock.trans hweak) hexp

end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_KernelSampling
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

namespace FiniteDistribution

/-- A full response table of nonzero weight uses a supported answer in every row. -/
theorem table_row_weight_ne_zero
    {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q]
    (responses : Q → FiniteDistribution A) (answers : Q → A)
    (h : (table responses).weight answers ≠ 0) (q : Q) :
    (responses q).weight (answers q) ≠ 0 := by
  intro hq
  apply h
  change (∏ r, (responses r).weight (answers r)) = 0
  exact Finset.prod_eq_zero (Finset.mem_univ q) hq

end FiniteDistribution

namespace KernelSampling

/-- The fixed weighted seed law; it does not depend on the sampled questions. -/
def seedLaw {Q₁ Q₂ A B : Type*}
    [Fintype Q₁] [Fintype Q₂] [Fintype A] [Fintype B]
    [DecidableEq Q₁] [DecidableEq Q₂]
    (left : Q₁ → FiniteDistribution A) (right : Q₂ → FiniteDistribution B) :
    FiniteDistribution (Seed Q₁ Q₂ A B) :=
  (FiniteDistribution.table left).product (FiniteDistribution.table right)

end KernelSampling
end
end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_FinishBoundsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact composition identities for finite distribution maps. -/
namespace UniqueGamesTheorem.Foundations.Games.FiniteDistribution
open scoped BigOperators
noncomputable section
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

theorem weight_eq_probability_singleton [DecidableEq A] (μ : FiniteDistribution A) (a : A) :
    μ.weight a = μ.probability (fun x => decide (x = a)) := by
  classical
  simp [probability]

theorem expectation_pushforward (μ : FiniteDistribution A) (f : A → B) (h : B → ℝ) :
    (μ.pushforward f).expectation h = μ.expectation (fun a => h (f a)) := by
  classical
  simp only [expectation, pushforward, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

end
end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_Variation
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

theorem totalVariation_triangle (p q r : α → ℝ) :
    totalVariation p r ≤ totalVariation p q + totalVariation q r := by
  have hpoint : ∀ a, |p a - r a| ≤ |p a - q a| + |q a - r a| := by
    intro a
    have := abs_add_le (p a - q a) (q a - r a)
    simpa only [sub_add_sub_cancel] using this
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simp only [Finset.sum_add_distrib] at hsum
  unfold totalVariation
  linarith

theorem totalVariation_kernelPushforward_le (p q : α → ℝ) (kernel : α → β → ℝ)
    (hk : ∀ a, IsProbability (kernel a)) :
    totalVariation (kernelPushforward p kernel) (kernelPushforward q kernel) ≤
      totalVariation p q := by
  have hpoint : ∀ b,
      |kernelPushforward p kernel b - kernelPushforward q kernel b| ≤
        ∑ a, |p a - q a| * kernel a b := by
    intro b
    simp only [kernelPushforward, ← Finset.sum_sub_distrib, ← sub_mul]
    have h := Finset.abs_sum_le_sum_abs (fun a => (p a - q a) * kernel a b) Finset.univ
    have habs : ∀ a, |kernel a b| = kernel a b := fun a => abs_of_nonneg ((hk a).1 b)
    simpa only [abs_mul, habs] using h
  have hsum := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset β)) => hpoint b)
  rw [Finset.sum_comm] at hsum
  simp only [← Finset.mul_sum, (hk _).2, mul_one] at hsum
  exact div_le_div_of_nonneg_right hsum (by norm_num : (0 : ℝ) ≤ 2)

end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_MaskedVariation
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

def maskedModel (μ : Games.FiniteDistribution (X × Y)) (p : S × (X × Y) → ℝ) :
    (S × (X ⊕ Y)) × (X × Y) → ℝ := fun z =>
  Information.firstMarginal (maskedJoint p) z.1 * (revealProfile μ z.1.2).weight z.2

def leftRevealModel (μ : Games.FiniteDistribution (X × Y)) (p : S × (X × Y) → ℝ) :
    S × (X × Y) → ℝ := fun z =>
  (∑ y, p (z.1, (z.2.1, y))) * (revealProfile μ (Sum.inl z.2.1)).weight z.2

def rightRevealModel (μ : Games.FiniteDistribution (X × Y)) (p : S × (X × Y) → ℝ) :
    S × (X × Y) → ℝ := fun z =>
  (∑ x, p (z.1, (x, z.2.2))) * (revealProfile μ (Sum.inr z.2.2)).weight z.2

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

omit [Fintype S] in
theorem abs_masked_inl (μ : Games.FiniteDistribution (X × Y))
    (p : S × (X × Y) → ℝ) (s : S) (u x : X) (y : Y) :
    |maskedJoint p ((s, Sum.inl u), (x, y)) - maskedModel μ p ((s, Sum.inl u), (x, y))| =
      if x = u then |p (s, (x, y)) - leftRevealModel μ p (s, (x, y))| / 2 else 0 := by
  by_cases hx : x = u
  · subst x
    simp only [maskedModel, maskedJoint_firstMarginal_inl]
    simpa [maskedJoint, leftRevealModel] using
      abs_half_sub_half_mul (p (s, (u, y))) (∑ v, p (s, (u, v)))
        ((revealProfile μ (Sum.inl u)).weight (u, y))
  · have hs := revealProfile_inl_support μ u (x, y) hx
    simp [maskedJoint, maskedModel, hs, hx, Ne.symm hx]

omit [Fintype S] in
theorem abs_masked_inr (μ : Games.FiniteDistribution (X × Y))
    (p : S × (X × Y) → ℝ) (s : S) (v : Y) (x : X) (y : Y) :
    |maskedJoint p ((s, Sum.inr v), (x, y)) - maskedModel μ p ((s, Sum.inr v), (x, y))| =
      if y = v then |p (s, (x, y)) - rightRevealModel μ p (s, (x, y))| / 2 else 0 := by
  by_cases hy : y = v
  · subst y
    simp only [maskedModel, maskedJoint_firstMarginal_inr]
    simpa [maskedJoint, rightRevealModel] using
      abs_half_sub_half_mul (p (s, (x, v))) (∑ u, p (s, (u, v)))
        ((revealProfile μ (Sum.inr v)).weight (x, v))
  · have hs := revealProfile_inr_support μ v (x, y) hy
    simp [maskedJoint, maskedModel, hs, hy, Ne.symm hy]

theorem masked_totalVariation_identity (μ : Games.FiniteDistribution (X × Y))
    (p : S × (X × Y) → ℝ) :
    2 * Information.totalVariation (maskedJoint p) (maskedModel μ p) =
      Information.totalVariation p (leftRevealModel μ p) +
        Information.totalVariation p (rightRevealModel μ p) := by
  have hleft (s : S) :
      (∑ u : X, ∑ q : X × Y,
        |maskedJoint p ((s, Sum.inl u), q) - maskedModel μ p ((s, Sum.inl u), q)|) =
      (∑ q : X × Y, |p (s, q) - leftRevealModel μ p (s, q)|) / 2 := by
    simp_rw [Fintype.sum_prod_type, abs_masked_inl]
    simp [Finset.sum_ite_irrel, div_eq_mul_inv, Finset.sum_mul]
  have hright (s : S) :
      (∑ v : Y, ∑ q : X × Y,
        |maskedJoint p ((s, Sum.inr v), q) - maskedModel μ p ((s, Sum.inr v), q)|) =
      (∑ q : X × Y, |p (s, q) - rightRevealModel μ p (s, q)|) / 2 := by
    have hcollapse :
        (∑ v : Y, ∑ q : X × Y,
          |maskedJoint p ((s, Sum.inr v), q) - maskedModel μ p ((s, Sum.inr v), q)|) =
        ∑ v : Y, ∑ x : X, |p (s, (x, v)) - rightRevealModel μ p (s, (x, v))| / 2 := by
      simp [Fintype.sum_prod_type, abs_masked_inr]
    rw [hcollapse, Finset.sum_comm]
    simp [Fintype.sum_prod_type, div_eq_mul_inv, Finset.sum_mul]
  have hmass :
      (∑ z : (S × (X ⊕ Y)) × (X × Y), |maskedJoint p z - maskedModel μ p z|) =
      ((∑ z : S × (X × Y), |p z - leftRevealModel μ p z|) +
       (∑ z : S × (X × Y), |p z - rightRevealModel μ p z|)) / 2 := by
    calc
      _ = ∑ s : S,
          ((∑ u : X, ∑ q : X × Y, |maskedJoint p ((s, Sum.inl u), q) - maskedModel μ p ((s, Sum.inl u), q)|) +
           (∑ v : Y, ∑ q : X × Y, |maskedJoint p ((s, Sum.inr v), q) - maskedModel μ p ((s, Sum.inr v), q)|)) := by
        simp only [Fintype.sum_prod_type, Fintype.sum_sum_type]
      _ = ∑ s : S,
          ((∑ q : X × Y, |p (s, q) - leftRevealModel μ p (s, q)|) / 2 +
           (∑ q : X × Y, |p (s, q) - rightRevealModel μ p (s, q)|) / 2) := by
        simp_rw [hleft, hright]
      _ = _ := by
        simp [Fintype.sum_prod_type, div_eq_mul_inv, Finset.sum_add_distrib, Finset.sum_mul, add_mul]
  unfold Information.totalVariation
  rw [hmass]
  ring

theorem leftRevealModel_totalVariation_le (μ : Games.FiniteDistribution (X × Y))
    (p : S × (X × Y) → ℝ) :
    Information.totalVariation p (leftRevealModel μ p) ≤
      2 * Information.totalVariation (maskedJoint p) (maskedModel μ p) := by
  rw [masked_totalVariation_identity]
  linarith [Information.totalVariation_nonneg p (rightRevealModel μ p)]

theorem rightRevealModel_totalVariation_le (μ : Games.FiniteDistribution (X × Y))
    (p : S × (X × Y) → ℝ) :
    Information.totalVariation p (rightRevealModel μ p) ≤
      2 * Information.totalVariation (maskedJoint p) (maskedModel μ p) := by
  rw [masked_totalVariation_identity]
  linarith [Information.totalVariation_nonneg p (leftRevealModel μ p)]

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_SelectedInformationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]
  {n : Nat}

def selectedAnswerLabel
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (questions : (Fin n → Q₁) × (Fin n → Q₂)) :
    SelectedLabels (A₁ := A₁) (A₂ := A₂) selected :=
  (fun i => strategy.1 questions.1 i.1, fun i => strategy.2 questions.2 i.1)

def selectedLikelihood (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (fixed : selected → Q₁ × Q₂)
    (label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) : ℝ := by
  classical
  let questions := selectedQuestionTuple selected fixed remaining
  exact if selectedAnswerLabel strategy selected questions = label then
    (if G.selectedWins strategy selected questions then 1 else 0) else 0

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedLikelihood_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (fixed : selected → Q₁ × Q₂)
    (label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    0 ≤ selectedLikelihood G strategy selected fixed label remaining := by
  classical
  dsimp only [selectedLikelihood]
  split_ifs <;> norm_num

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedLikelihood_sum (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (fixed : selected → Q₁ × Q₂)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    (∑ label, selectedLikelihood G strategy selected fixed label remaining) =
      if G.selectedWins strategy selected (selectedQuestionTuple selected fixed remaining)
      then 1 else 0 := by
  classical
  simp [selectedLikelihood]

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedLikelihood_sum_le_one (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (fixed : selected → Q₁ × Q₂)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    (∑ label, selectedLikelihood G strategy selected fixed label remaining) ≤ 1 := by
  rw [selectedLikelihood_sum]
  split <;> norm_num

def selectedSplitLaw (G : Game Q₁ Q₂ A₁ A₂) (selected : Finset (Fin n)) :
    FiniteDistribution ((selected → Q₁ × Q₂) ×
      ({i : Fin n // i ∉ selected} → Q₁ × Q₂)) :=
  (FiniteDistribution.table (fun _ : selected => G.questions)).product
    (FiniteDistribution.table (fun _ : {i : Fin n // i ∉ selected} => G.questions))

def selectedInputLaw (G : Game Q₁ Q₂ A₁ A₂) (selected : Finset (Fin n)) :
    FiniteDistribution (SelectedInput Q₁ Q₂ selected) :=
  (FiniteDistribution.table (fun _ : selected => G.questions)).product
    (FiniteDistribution.table (fun _ : {i : Fin n // i ∉ selected} => revealInputLaw G.questions))

def selectedInputProfile (G : Game Q₁ Q₂ A₁ A₂) (selected : Finset (Fin n))
    (t : SelectedInput Q₁ Q₂ selected) (i : {i : Fin n // i ∉ selected}) :
    FiniteDistribution (Q₁ × Q₂) := revealProfile G.questions (t.2 i)

def selectedSideMass (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (tv : SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ :=
  ∑ u, independentProduct (fun i => (selectedInputProfile G selected tv.1 i).weight) u *
    selectedLikelihood G strategy selected tv.1.1 tv.2 u

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedSideMass_sum (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (t : SelectedInput Q₁ Q₂ selected) :
    (∑ v, selectedSideMass G strategy selected (t,v)) =
      ∑ u, independentProduct (fun i => (selectedInputProfile G selected t i).weight) u *
        (if G.selectedWins strategy selected (selectedQuestionTuple selected t.1 u)
        then 1 else 0) := by
  classical
  simp only [selectedSideMass]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, selectedLikelihood_sum]

def selectedSideWeight (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (tv : SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ :=
  (selectedInputLaw G selected).weight tv.1 * selectedSideMass G strategy selected tv /
    G.selectedSuccess strategy selected

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! Conditioning bounds for the actual repeated-game question marginals.
The likelihood and its normalizer are derived from the selected-win event.
The final estimate retains only the unselected coordinates. -/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators
open Games Information

noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]
  {n : Nat}

def selectedTupleLikelihood (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (questions : Fin n → Q₁ × Q₂) : ℝ :=
  if G.selectedWins strategy selected (Game.tupleQuestionEquiv n questions) then 1 else 0

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedTupleLikelihood_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (questions : Fin n → Q₁ × Q₂) :
    0 ≤ selectedTupleLikelihood G strategy selected questions := by
  unfold selectedTupleLikelihood
  split <;> norm_num

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedTupleLikelihood_le_one (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (questions : Fin n → Q₁ × Q₂) :
    selectedTupleLikelihood G strategy selected questions ≤ 1 := by
  unfold selectedTupleLikelihood
  split <;> norm_num

/-- The coordinate pair under the actual repeated question law conditioned on
the selected wins, rather than a separately postulated posterior law. -/
def selectedQuestionMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (i : Fin n) : FiniteDistribution (Q₁ × Q₂) :=
  ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).pushforward
    (fun questions => (questions.1 i, questions.2 i))

theorem selectedQuestionMarginal_weight (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (i : Fin n) :
    (selectedQuestionMarginal G strategy selected positive i).weight =
      coordinateMarginal
        (posterior (independentProduct (fun _ : Fin n => G.questions.weight))
          (selectedTupleLikelihood G strategy selected) (G.selectedSuccess strategy selected)) i := by
  classical
  funext a
  simp only [selectedQuestionMarginal, FiniteDistribution.pushforward,
    FiniteDistribution.condition, coordinateMarginal]
  refine Fintype.sum_equiv (Game.tupleQuestionEquiv (Q₁ := Q₁) (Q₂ := Q₂) n).symm _ _ ?_
  intro questions
  cases he : G.selectedWins strategy selected questions <;>
    simp [Game.repetition_question_weight, Game.tupleQuestionEquiv,
      posterior, independentProduct, selectedTupleLikelihood, Game.selectedSuccess, he]

end

end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! The actual full selected-answer and reveal law conditioned on success.
Its factorization is derived from the explicit independent question law. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedJointWeight (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (z : (SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
      ({i : Fin n // i ∉ selected} → Q₁ × Q₂)) : ℝ :=
  (selectedInputLaw G selected).weight z.1.1 *
    independentProduct (fun i => (selectedInputProfile G selected z.1.1 i).weight) z.2 *
      selectedLikelihood G strategy selected z.1.1.1 z.1.2 z.2 /
        G.selectedSuccess strategy selected

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedJointWeight_firstMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (tv) :
    firstMarginal (selectedJointWeight G strategy selected) tv =
      selectedSideWeight G strategy selected tv := by
  simp only [firstMarginal, selectedJointWeight, selectedSideWeight, selectedSideMass,
    div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Pointwise product formula for the actual conditional joint law. The
selected-answer test depends on the question tuples, and not on any reveal. -/
theorem selectedJointWeight_factorization (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (tv) (u) :
    selectedJointWeight G strategy selected (tv,u) =
      (∏ i : selected, G.questions.weight (tv.1.1 i)) *
        (∏ i : {i : Fin n // i ∉ selected}, (revealLaw G.questions).weight (u i,tv.1.2 i)) *
          selectedLikelihood G strategy selected tv.1.1 tv.2 u /
            G.selectedSuccess strategy selected := by
  unfold selectedJointWeight
  simp only [selectedInputLaw, FiniteDistribution.product, FiniteDistribution.table,
    independentProduct, selectedInputProfile]
  rw [mul_assoc (∏ i : selected, G.questions.weight (tv.1.1 i)), reveal_product_factorization]

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

def selectedLabelAccepts (G : Game Q₁ Q₂ A₁ A₂) (selected : Finset (Fin n))
    (fixed : selected → Q₁ × Q₂)
    (label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : Bool := by
  classical
  exact decide (∀ i : selected, G.accepts (fixed i).1 (fixed i).2 (label.1 i) (label.2 i) = true)

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedWins_of_answerLabel (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (fixed : selected → Q₁ × Q₂)
    (label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂)
    (hlabel : selectedAnswerLabel strategy selected (selectedQuestionTuple selected fixed remaining) = label) :
    G.selectedWins strategy selected (selectedQuestionTuple selected fixed remaining) =
      selectedLabelAccepts G selected fixed label := by
  classical
  have hleft (i : selected) := congrArg (fun l => l.1 i) hlabel
  have hright (i : selected) := congrArg (fun l => l.2 i) hlabel
  apply Bool.eq_iff_iff.mpr
  simp only [Game.selectedWins, selectedLabelAccepts, decide_eq_true_eq]
  constructor
  · intro h i
    have hi := h i.1 i.property
    simpa [Game.coordinateWin, selectedQuestionTuple, mergeCoordinates, i.property,
      ← hleft i, ← hright i, selectedAnswerLabel] using hi
  · intro h i hi
    have hv := h ⟨i,hi⟩
    simpa [Game.coordinateWin, selectedQuestionTuple, mergeCoordinates, hi,
      ← hleft ⟨i,hi⟩, ← hright ⟨i,hi⟩, selectedAnswerLabel] using hv

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedLikelihood_factorization (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (fixed : selected → Q₁ × Q₂)
    (label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    selectedLikelihood G strategy selected fixed label remaining =
      (if selectedLabelAccepts G selected fixed label then 1 else 0) *
        selectedLocalTest strategy.1 selected (fun i => (fixed i).1) label.1 (fun i => (remaining i).1) *
        selectedLocalTest strategy.2 selected (fun i => (fixed i).2) label.2 (fun i => (remaining i).2) := by
  classical
  have he : selectedAnswerLabel strategy selected (selectedQuestionTuple selected fixed remaining) =
      (selectedLocalAnswers strategy.1 selected (fun i => (fixed i).1) (fun i => (remaining i).1),
       selectedLocalAnswers strategy.2 selected (fun i => (fixed i).2) (fun i => (remaining i).2)) := by
    simp only [selectedAnswerLabel,
      selectedQuestionTuple_left, selectedQuestionTuple_right]
    rfl
  by_cases hl : selectedLocalAnswers strategy.1 selected (fun i => (fixed i).1)
      (fun i => (remaining i).1) = label.1
  · by_cases hr : selectedLocalAnswers strategy.2 selected (fun i => (fixed i).2)
        (fun i => (remaining i).2) = label.2
    · have hlabel : selectedAnswerLabel strategy selected (selectedQuestionTuple selected fixed remaining) = label := by
        rw [he, hl, hr]
      simp only [selectedLikelihood, ite_eq_left hlabel,
        selectedWins_of_answerLabel G strategy selected fixed label remaining hlabel,
        selectedLocalTest, ite_eq_left hl, ite_eq_left hr, mul_one]
    · have hn : selectedAnswerLabel strategy selected (selectedQuestionTuple selected fixed remaining) ≠ label := by
        intro h
        rw [he] at h
        exact hr (congrArg Prod.snd h)
      simp [selectedLikelihood, hn, selectedLocalTest, hl, hr]
  · have hn : selectedAnswerLabel strategy selected (selectedQuestionTuple selected fixed remaining) ≠ label := by
      intro h
      rw [he] at h
      exact hl (congrArg Prod.fst h)
    simp [selectedLikelihood, hn, selectedLocalTest, hl]

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_PartialRevealLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

def partialRevealWeight (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (u : I → X × Y) : ℝ :=
  μ.weight (u j) * ∏ i : {i : I // i ≠ j}, (revealLaw μ).weight (u i.1,rest i)

theorem product_reveal_at (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (r : X ⊕ Y) (rest : {i : I // i ≠ j} → X ⊕ Y) (u : I → X × Y) :
    (∏ i, (revealLaw μ).weight (u i,mergeAt j r rest i)) =
      (if r = Sum.inl (u j).1 then partialRevealWeight μ j rest u / 2 else 0) +
      (if r = Sum.inr (u j).2 then partialRevealWeight μ j rest u / 2 else 0) := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ j]
  simp only [mergeAt_self, mergeAt_other, revealLaw_weight]
  by_cases hl : r = Sum.inl (u j).1 <;> by_cases hr : r = Sum.inr (u j).2 <;>
    simp [hl, hr, partialRevealWeight, revealLaw_weight] <;> ring

def partialRevealMarginal (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    (T × ({i : I // i ≠ j} → X ⊕ Y)) × (X × Y) → ℝ := by
  classical
  exact fun z => ∑ u, if u j = z.2 then
    partialRevealWeight μ j z.1.2 u * likelihood z.1.1 u else 0

def fullRevealMarginal (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    (T × (I → X ⊕ Y)) × (X × Y) → ℝ := by
  classical
  exact fun z => ∑ u, if u j = z.2 then
    (∏ i, (revealLaw μ).weight (u i,z.1.2 i)) * likelihood z.1.1 u else 0

omit [Fintype T] in
theorem fullRevealMarginal_merge (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) (t : T)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (r : X ⊕ Y) (q : X × Y) :
    fullRevealMarginal μ j likelihood ((t,mergeAt j r rest),q) =
      maskedJoint (partialRevealMarginal μ j likelihood) (((t,rest),r),q) := by
  classical
  unfold fullRevealMarginal
  simp_rw [product_reveal_at]
  have hpoint (u : I → X × Y) :
      (if u j = q then
        ((if r = Sum.inl (u j).1 then partialRevealWeight μ j rest u / 2 else 0) +
         (if r = Sum.inr (u j).2 then partialRevealWeight μ j rest u / 2 else 0)) *
          likelihood t u else 0) =
      (if r = Sum.inl q.1 then
        (if u j = q then partialRevealWeight μ j rest u * likelihood t u else 0) / 2 else 0) +
      (if r = Sum.inr q.2 then
        (if u j = q then partialRevealWeight μ j rest u * likelihood t u else 0) / 2 else 0) := by
    by_cases hu : u j = q
    · rw [hu]
      by_cases hl : r = Sum.inl q.1 <;> by_cases hr : r = Sum.inr q.2 <;>
        simp [hl, hr] <;> ring
    · simp [hu]
  simp_rw [hpoint]
  simp [maskedJoint, partialRevealMarginal, Finset.sum_add_distrib,
    Finset.sum_ite_irrel, div_eq_mul_inv, Finset.sum_mul]

def fullRevealModel (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    (T × (I → X ⊕ Y)) × (X × Y) → ℝ := fun z =>
  Information.firstMarginal (fullRevealMarginal μ j likelihood) z.1 *
    (revealProfile μ (z.1.2 j)).weight z.2

omit [Fintype T] in
theorem fullRevealModel_merge (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) (t : T)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (r : X ⊕ Y) (q : X × Y) :
    fullRevealModel μ j likelihood ((t,mergeAt j r rest),q) =
      maskedModel μ (partialRevealMarginal μ j likelihood) (((t,rest),r),q) := by
  simp only [fullRevealModel, Information.firstMarginal, fullRevealMarginal_merge,
    mergeAt_self, maskedModel]

theorem totalVariation_comp_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (p q : B → ℝ) :
    Information.totalVariation (fun a => p (e a)) (fun a => q (e a)) =
      Information.totalVariation p q := by
  unfold Information.totalVariation
  congr 1
  exact e.sum_comp (fun b => |p b - q b|)

/-- The variation quantity for the explicit full reveal law equals the
two-branch masked quantity after extracting one reveal coordinate. -/
theorem fullReveal_totalVariation (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    Information.totalVariation (fullRevealMarginal μ j likelihood) (fullRevealModel μ j likelihood) =
      Information.totalVariation (maskedJoint (partialRevealMarginal μ j likelihood))
        (maskedModel μ (partialRevealMarginal μ j likelihood)) := by
  calc
    _ = Information.totalVariation
        (fun z => fullRevealMarginal μ j likelihood ((revealSplitEquiv (T := T) j).symm z))
        (fun z => fullRevealModel μ j likelihood ((revealSplitEquiv (T := T) j).symm z)) :=
      (totalVariation_comp_equiv (revealSplitEquiv (T := T) j).symm _ _).symm
    _ = _ := by
      congr 1 <;> funext z
      · exact fullRevealMarginal_merge μ j likelihood z.1.1.1 z.1.1.2 z.1.2 z.2
      · exact fullRevealModel_merge μ j likelihood z.1.1.1 z.1.1.2 z.1.2 z.2

theorem leftReveal_full_error (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    Information.totalVariation (partialRevealMarginal μ j likelihood)
      (leftRevealModel μ (partialRevealMarginal μ j likelihood)) ≤
      2 * Information.totalVariation (fullRevealMarginal μ j likelihood)
        (fullRevealModel μ j likelihood) := by
  rw [fullReveal_totalVariation]
  exact leftRevealModel_totalVariation_le μ _

theorem rightReveal_full_error (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    Information.totalVariation (partialRevealMarginal μ j likelihood)
      (rightRevealModel μ (partialRevealMarginal μ j likelihood)) ≤
      2 * Information.totalVariation (fullRevealMarginal μ j likelihood)
        (fullRevealModel μ j likelihood) := by
  rw [fullReveal_totalVariation]
  exact rightRevealModel_totalVariation_le μ _

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! The actual sum-tagged reveal law separates into local endpoint factors.
The fair reveal probability is retained in those factors. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games
noncomputable section
variable {I X Y : Type*} [Fintype I] [DecidableEq I]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def revealLeftFactor (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) (x : X) : ℝ :=
  match r with
  | Sum.inl u => if x = u then 1 else 0
  | Sum.inr v => μ.weight (x,v) / 2

def revealRightFactor (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) (y : Y) : ℝ :=
  match r with
  | Sum.inl u => μ.weight (u,y) / 2
  | Sum.inr v => if y = v then 1 else 0

omit [DecidableEq Y] in
theorem revealLeftFactor_nonnegative (μ : FiniteDistribution (X × Y))
    (r : X ⊕ Y) (x : X) : 0 ≤ revealLeftFactor μ r x := by
  cases r with
  | inl u => simp only [revealLeftFactor]; split <;> norm_num
  | inr v => exact div_nonneg (μ.nonnegative _) (by norm_num)

omit [DecidableEq X] in
theorem revealRightFactor_nonnegative (μ : FiniteDistribution (X × Y))
    (r : X ⊕ Y) (y : Y) : 0 ≤ revealRightFactor μ r y := by
  cases r with
  | inl u => exact div_nonneg (μ.nonnegative _) (by norm_num)
  | inr v => simp only [revealRightFactor]; split <;> norm_num

theorem revealLaw_factorization (μ : FiniteDistribution (X × Y))
    (r : X ⊕ Y) (x : X) (y : Y) :
    (revealLaw μ).weight ((x,y),r) =
      revealLeftFactor μ r x * revealRightFactor μ r y := by
  rw [revealLaw_weight]
  cases r with
  | inl u =>
    by_cases h : x = u
    · subst x; simp [revealLeftFactor, revealRightFactor]
    · simp [revealLeftFactor, revealRightFactor, h, Ne.symm h]
  | inr v =>
    by_cases h : y = v
    · subst y; simp [revealLeftFactor, revealRightFactor]
    · simp [revealLeftFactor, revealRightFactor, h, Ne.symm h]

def partialLeftFactor (μ : FiniteDistribution (X × Y)) (j : I)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (x : I → X) : ℝ :=
  ∏ i, revealLeftFactor μ (rest i) (x i.1)

def partialRightFactor (μ : FiniteDistribution (X × Y)) (j : I)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (y : I → Y) : ℝ :=
  ∏ i, revealRightFactor μ (rest i) (y i.1)

theorem partialRevealWeight_factorization (μ : FiniteDistribution (X × Y)) (j : I)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (u : I → X × Y) :
    partialRevealWeight μ j rest u =
      μ.weight (u j) * partialLeftFactor μ j rest (fun i => (u i).1) *
        partialRightFactor μ j rest (fun i => (u i).2) := by
  have hpoint (i : {i : I // i ≠ j}) :
      (revealLaw μ).weight (u i.1,rest i) =
        revealLeftFactor μ (rest i) (u i.1).1 * revealRightFactor μ (rest i) (u i.1).2 :=
    revealLaw_factorization μ (rest i) (u i.1).1 (u i.1).2
  simp only [partialRevealWeight, partialLeftFactor, partialRightFactor,
    hpoint, Finset.prod_mul_distrib]
  ring

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

def selectedRawMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) :
    (SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
      (Q₁ × Q₂) → ℝ := by
  classical
  exact fun z => ∑ u, if u j = z.2 then selectedJointWeight G strategy selected (z.1,u) else 0

theorem selectedPosterior_eq_raw (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) (tv) (q) :
    selectedSideWeight G strategy selected tv * coordinateMarginal
      (posteriorOrOriginal
        (independentProduct (fun i => (selectedInputProfile G selected tv.1 i).weight))
        (selectedLikelihood G strategy selected tv.1.1 tv.2)
        (selectedSideMass G strategy selected tv)) j q =
      selectedRawMarginal G strategy selected j (tv,q) := by
  classical
  rw [selectedSideWeight]
  have h := weighted_coordinate_posterior_recombine
    (independentProduct (fun i => (selectedInputProfile G selected tv.1 i).weight))
    (selectedLikelihood G strategy selected tv.1.1 tv.2)
    (independentProduct_isProbability _
      (fun i => gameLaw_isProbability (selectedInputProfile G selected tv.1 i)))
    (selectedLikelihood_nonnegative G strategy selected tv.1.1 tv.2)
    (c := selectedSideMass G strategy selected tv) rfl
    ((selectedInputLaw G selected).weight tv.1) (G.selectedSuccess strategy selected) j q
  rw [h]
  simp only [Finset.mul_sum, selectedRawMarginal, selectedJointWeight]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : u j = q
  · simp only [ite_eq_left hu]
    ring
  · simp [hu]

theorem selectedRawMarginal_firstMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) (tv) :
    firstMarginal (selectedRawMarginal G strategy selected j) tv =
      selectedSideWeight G strategy selected tv := by
  classical
  simp only [firstMarginal, selectedRawMarginal]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  exact selectedJointWeight_firstMarginal G strategy selected tv

def selectedOutsideLikelihood (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (t : (selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected)
    (u : {i : Fin n // i ∉ selected} → Q₁ × Q₂) : ℝ :=
  (∏ i : selected, G.questions.weight (t.1 i)) *
    selectedLikelihood G strategy selected t.1 t.2 u / G.selectedSuccess strategy selected

theorem selectedRawMarginal_fullReveal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) (z) :
    selectedRawMarginal G strategy selected j
        ((selectedObservationEquiv (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected).symm z) =
      fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected) z := by
  classical
  change selectedRawMarginal G strategy selected j
    (((z.1.1.1,z.1.2),z.1.1.2),z.2) = _
  simp only [selectedRawMarginal, fullRevealMarginal]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : u j = z.2
  · simp only [ite_eq_left hu, selectedJointWeight_factorization, selectedOutsideLikelihood]
    ring
  · simp [hu]

theorem selectedRawReference_fullReveal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) (z) :
    (fun w => selectedSideWeight G strategy selected w.1 *
      (selectedInputProfile G selected w.1.1 j).weight w.2)
        ((selectedObservationEquiv (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected).symm z) =
      fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected) z := by
  change selectedSideWeight G strategy selected ((z.1.1.1,z.1.2),z.1.1.2) *
    (revealProfile G.questions (z.1.2 j)).weight z.2 = _
  rw [← selectedRawMarginal_firstMarginal G strategy selected j]
  unfold firstMarginal fullRevealModel
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  exact selectedRawMarginal_fullReveal G strategy selected j (z.1,q)

theorem selected_raw_error_eq_fullReveal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) :
    totalVariation (selectedRawMarginal G strategy selected j)
      (fun z => selectedSideWeight G strategy selected z.1 *
        (selectedInputProfile G selected z.1.1 j).weight z.2) =
      totalVariation (fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected)) := by
  rw [← totalVariation_comp_equiv
    (selectedObservationEquiv (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected).symm]
  congr 1 <;> funext z
  · exact selectedRawMarginal_fullReveal G strategy selected j z
  · exact selectedRawReference_fullReveal G strategy selected j z

def selectedInformationRadius (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) : ℝ :=
  Real.sqrt ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
    (Real.log (Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ) +
      Real.log (1 / G.selectedSuccess strategy selected)))

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

theorem log_le_logTwo {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ logTwo x := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htwo_le : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  unfold logTwo
  apply (le_div_iff₀ htwo).2
  simpa using mul_le_mul_of_nonneg_left htwo_le hlog

theorem selectedLabels_log_le [Nonempty A₁] [Nonempty A₂]
    (selected : Finset (Fin n)) (ell : ℝ)
    (hell : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell) :
    Real.log (Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ) ≤
      (selected.card : ℝ) * ell := by
  have ha : (1 : ℝ) ≤ Fintype.card A₁ := by exact_mod_cast Fintype.card_pos (α := A₁)
  have hb : (1 : ℝ) ≤ Fintype.card A₂ := by exact_mod_cast Fintype.card_pos (α := A₂)
  have hab : (1 : ℝ) ≤ (Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ) := by nlinarith
  rw [selectedLabels_card, Nat.cast_pow, Nat.cast_mul, Real.log_pow]
  exact mul_le_mul_of_nonneg_left ((log_le_logTwo hab).trans hell) (Nat.cast_nonneg _)

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

theorem isProbability_comp_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (p : B → ℝ) (hp : IsProbability p) :
    IsProbability (fun a => p (e a)) := by
  constructor
  · intro a
    exact hp.1 _
  · rw [e.sum_comp]
    exact hp.2

theorem partialRevealMarginal_isProbability
    {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (μ : FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ)
    (hp : IsProbability (fullRevealMarginal μ j likelihood)) :
    IsProbability (partialRevealMarginal μ j likelihood) := by
  apply (maskedJoint_isProbability_iff _).mp
  have h := isProbability_comp_equiv (revealSplitEquiv (T := T) j).symm _ hp
  have he : (fun z => fullRevealMarginal μ j likelihood
      ((revealSplitEquiv (T := T) j).symm z)) =
      maskedJoint (partialRevealMarginal μ j likelihood) := by
    funext z
    exact fullRevealMarginal_merge μ j likelihood z.1.1.1 z.1.1.2 z.1.2 z.2
  rw [he] at h
  exact h

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

theorem firstMarginal_totalVariation_le (r t : X × Y → ℝ) :
    totalVariation (firstMarginal r) (firstMarginal t) ≤ totalVariation r t := by
  unfold totalVariation firstMarginal
  simp_rw [← Finset.sum_sub_distrib]
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun x _ => Finset.abs_sum_le_sum_abs (fun y : Y => r (x,y)-t (x,y)) Finset.univ)
  rw [Fintype.sum_prod_type]
  linarith

theorem leftCommonMarginal_isProbability (p : S × (X × Y) → ℝ)
    (hp : IsProbability p) : IsProbability (leftCommonMarginal p) := by
  exact ProfileCorrection.seedQuestionMarginal_isProbability
    (fun z => p (swapSeedLeft z)) (isProbability_comp_equiv swapSeedLeft p hp)

theorem leftCommonProfile_isProbability (p : S × (X × Y) → ℝ) (fallback : S → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback) (x : X) :
    IsProbability (leftCommonProfile p fallback x) :=
  conditionalKernel_isProbability _ _ (leftCommonMarginal_isProbability p hp) hf x

theorem leftCommonProfile_error [DecidableEq X] [DecidableEq Y]
    (p : S × (X × Y) → ℝ) (μ : FiniteDistribution (X × Y)) (fallback : S → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback) :
    totalVariation p (fun z => μ.weight z.2 * leftCommonProfile p fallback z.2.1 z.1) ≤
      totalVariation p (leftRevealModel μ p) + totalVariation (secondMarginal p) μ.weight := by
  let e := swapSeedLeft (S := S) (X := X) (Y := Y)
  let p' : X × (S × Y) → ℝ := fun z => p (e z)
  have h := ProfileCorrection.left_profile_correction p' μ.weight fallback
    (μ.pushforward Prod.snd).weight
    (isProbability_comp_equiv e p hp) (gameLaw_isProbability μ) hf
    (gameLaw_isProbability (μ.pushforward Prod.snd))
  have hs : ProfileCorrection.seedQuestionMarginal p' = leftCommonMarginal p := rfl
  have hc : (fun z : X × (S × Y) => ProfileCorrection.seedQuestionMarginal p' (z.1,z.2.1) *
      conditionalKernel μ.weight (μ.pushforward Prod.snd).weight z.1 z.2.2) =
      fun z => leftRevealModel μ p (e z) := by
    funext z
    change (∑ y, p (z.2.1,(z.1,y))) *
      conditionalKernel μ.weight (μ.pushforward Prod.snd).weight z.1 z.2.2 =
      (∑ y, p (z.2.1,(z.1,y))) *
        (revealProfile μ (Sum.inl z.1)).weight (z.1,z.2.2)
    rw [revealProfile_inl_diagonal]
  have hd : (fun z : X × (S × Y) => μ.weight (z.1,z.2.2) *
      conditionalKernel (ProfileCorrection.seedQuestionMarginal p') fallback z.1 z.2.1) =
      fun z => μ.weight (e z).2 * leftCommonProfile p fallback (e z).2.1 (e z).1 := rfl
  rw [hc, hd] at h
  change totalVariation (fun z => p (e z)) _ ≤
    totalVariation (fun z => p (e z)) _ + _ at h
  rw [totalVariation_comp_equiv e p (leftRevealModel μ p)] at h
  rw [totalVariation_comp_equiv e p
    (fun z => μ.weight z.2 * leftCommonProfile p fallback z.2.1 z.1)] at h
  have hm : firstMarginal p' = firstMarginal (secondMarginal p) := by
    funext x
    simp only [firstMarginal, secondMarginal, Fintype.sum_prod_type, p', e, swapSeedLeft]
    exact Finset.sum_comm
  rw [hm] at h
  exact h.trans (add_le_add le_rfl (firstMarginal_totalVariation_le (secondMarginal p) μ.weight))

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

theorem rightCommonProfile_isProbability (p : S × (X × Y) → ℝ) (fallback : S → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback) (y : Y) :
    IsProbability (rightCommonProfile p fallback y) :=
  leftCommonProfile_isProbability (fun z => p (swapQuestionEndpoints z)) fallback
    (isProbability_comp_equiv swapQuestionEndpoints p hp) hf y

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_Rectangle
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

theorem rectangle_label_mass [DecidableEq α] (thresholds : List ℝ) (density : α → ℝ) (a : α)
    (hm : ∀ x, density x ∈ thresholds) (h0 : ∀ x, 0 ≤ density x)
    (h1 : ∀ x, density x ≤ 1) :
    eventMass (rectangleWeight thresholds)
      (fun seed => rectangleAccept thresholds density seed && decide (seed.1 = a)) =
      density a / (Fintype.card α : ℝ) := by
  unfold eventMass
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ x : α, if x = a then density x / (Fintype.card α : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x = a
      · simpa [hx] using rectangle_row_mass thresholds density x (hm x) (h0 x) (h1 x)
      · simp [hx]
    _ = density a / (Fintype.card α : ℝ) := by simp

omit [Fintype α] in theorem rectangle_or (thresholds : List ℝ) (p q : α → ℝ) :
    (fun seed => rectangleAccept thresholds p seed || rectangleAccept thresholds q seed) =
      rectangleAccept thresholds (fun a => max (p a) (q a)) := by
  funext seed
  simp [rectangleAccept]

theorem rectangle_union_mass (thresholds : List ℝ) (p q : α → ℝ)
    (hpm : ∀ a, p a ∈ thresholds) (hqm : ∀ a, q a ∈ thresholds)
    (hp0 : ∀ a, 0 ≤ p a) (_hq0 : ∀ a, 0 ≤ q a)
    (hp1 : ∀ a, p a ≤ 1) (hq1 : ∀ a, q a ≤ 1) :
    eventMass (rectangleWeight thresholds)
      (fun seed => rectangleAccept thresholds p seed || rectangleAccept thresholds q seed) =
      unionMass p q / (Fintype.card α : ℝ) := by
  rw [rectangle_or]
  exact rectangle_acceptance_mass thresholds _
    (fun a => max_mem_thresholds thresholds (hpm a) (hqm a))
    (fun a => (hp0 a).trans (le_max_left _ _)) (fun a => max_le (hp1 a) (hq1 a))

theorem rectangle_common_label_mass [DecidableEq α] (thresholds : List ℝ)
    (p q : α → ℝ) (a : α)
    (hpm : ∀ x, p x ∈ thresholds) (hqm : ∀ x, q x ∈ thresholds)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hp1 : ∀ x, p x ≤ 1) (_hq1 : ∀ x, q x ≤ 1) :
    eventMass (rectangleWeight thresholds)
      (fun seed => (rectangleAccept thresholds p seed && rectangleAccept thresholds q seed) &&
        decide (seed.1 = a)) = min (p a) (q a) / (Fintype.card α : ℝ) := by
  have hand := congrFun (rectangle_and thresholds p q)
  simp_rw [hand]
  exact rectangle_label_mass thresholds _ a
    (fun x => min_mem_thresholds thresholds (hpm x) (hqm x))
    (fun x => le_min (hp0 x) (hq0 x)) (fun x => (min_le_left _ _).trans (hp1 x))

end

end UniqueGamesTheorem.Foundations.CorrelatedSampling

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_LabelBound
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

def localDiagonal (left right : σ → Bool) (decode : σ → α) (fallback a : α)
    (proposals : List σ) : ℝ :=
  if localSample left decode fallback proposals = a ∧
      localSample right decode fallback proposals = a then 1 else 0

omit [Fintype σ] [DecidableEq σ] in
theorem common_first_label_lower (left right : σ → Bool) (decode : σ → α)
    (fallback a : α) (proposals : List σ) :
    goodFirstIndicator (fun s => left s || right s) (goodLabel left right decode a) proposals ≤
      localDiagonal left right decode fallback a proposals := by
  cases hfirst : firstAccepted (fun s => left s || right s) proposals with
  | none =>
      simp only [goodFirstIndicator, hfirst]
      unfold localDiagonal
      split_ifs <;> norm_num
  | some s =>
      by_cases hc : goodLabel left right decode a s = true
      · have hparts : (left s = true ∧ right s = true) ∧ decode s = a := by
          simpa [goodLabel] using hc
        have h := first_union_common left right proposals s hfirst hparts.1.1 hparts.1.2
        simp [goodFirstIndicator, hfirst, hc, localDiagonal, localSample, h.1, h.2, hparts.2]
      · have hn : 0 ≤ localDiagonal left right decode fallback a proposals := by
          unfold localDiagonal
          split_ifs <;> norm_num
        simpa [goodFirstIndicator, hfirst, hc] using hn

omit [DecidableEq σ] in theorem union_goodLabel_mass
    (w : σ → ℝ) (left right : σ → Bool) (decode : σ → α) (a : α) :
    eventMass w (fun s => (left s || right s) && goodLabel left right decode a s) =
      eventMass w (goodLabel left right decode a) := by
  unfold eventMass
  apply Finset.sum_congr rfl
  intro s _
  cases hl : left s <;> cases hr : right s <;> simp [goodLabel, hl, hr]

/-- The finite shared-list sampler's mass on the particular diagonal output
(a,a) is at least the common-first-label mass. Exhaustion uses a fixed local
fallback; its contribution is nonnegative and is not counted in this bound. -/
theorem finite_label_diagonal_bound (w : σ → ℝ) (left right : σ → Bool)
    (decode : σ → α) (fallback a : α) (hw : ∀ s, 0 ≤ w s)
    (hw_sum : ∑ s, w s = 1) (hu : 0 < eventMass w (fun s => left s || right s)) (n : Nat) :
    eventMass w (goodLabel left right decode a) / eventMass w (fun s => left s || right s) *
        (1 - eventMass w (fun s => !(left s || right s)) ^ n) ≤
      traceAverage w n (localDiagonal left right decode fallback a) := by
  have h := traceAverage_mono w hw n _ _ (common_first_label_lower left right decode fallback a)
  rw [goodFirstIndicator_law w _ _ hw_sum n,
    goodFirstMass_exact w _ _ hw_sum (ne_of_gt hu) n,
    union_goodLabel_mass] at h
  exact h

section Rectangle

variable [Fintype α] [Nonempty α]

/-- Concrete normalized-density instance of the per-label bound. All random
proposals come from the finite rectangle constructed from `thresholds`. -/
theorem rectangle_label_diagonal_bound (thresholds : List ℝ) (p q : α → ℝ)
    (fallback a : α)
    (hpm : ∀ x, p x ∈ thresholds) (hqm : ∀ x, q x ∈ thresholds)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hp1 : ∀ x, p x ≤ 1) (hq1 : ∀ x, q x ≤ 1)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) (n : Nat) :
    min (p a) (q a) / (1 + totalVariation p q) *
        (1 - eventMass (rectangleWeight thresholds)
          (fun s => !(rectangleAccept thresholds p s || rectangleAccept thresholds q s)) ^ n) ≤
      traceAverage (rectangleWeight thresholds) n
        (localDiagonal (rectangleAccept thresholds p) (rectangleAccept thresholds q)
          Prod.fst fallback a) := by
  have hc : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  have hU : 0 < unionMass p q := by
    rw [unionMass_eq p q hpsum hqsum]
    linarith [totalVariation_nonneg p q]
  have hmass := rectangle_union_mass thresholds p q hpm hqm hp0 hq0 hp1 hq1
  have hu : 0 < eventMass (rectangleWeight thresholds)
      (fun s => rectangleAccept thresholds p s || rectangleAccept thresholds q s) := by
    rw [hmass]
    exact div_pos hU hc
  have h := finite_label_diagonal_bound (rectangleWeight thresholds)
    (rectangleAccept thresholds p) (rectangleAccept thresholds q) Prod.fst fallback a
    (rectangleWeight_nonnegative thresholds) (rectangleWeight_normalized thresholds) hu n
  unfold goodLabel at h
  rw [rectangle_common_label_mass thresholds p q a hpm hqm hp0 hq0 hp1 hq1, hmass] at h
  have hratio : (min (p a) (q a) / (Fintype.card α : ℝ)) /
      (unionMass p q / (Fintype.card α : ℝ)) = min (p a) (q a) / unionMass p q := by
    field_simp
  rw [hratio, unionMass_eq p q hpsum hqsum] at h
  exact h

end Rectangle

end

end UniqueGamesTheorem.Foundations.CorrelatedSampling

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_SharedProfiles
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
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

theorem distribution_weight_le_one {S : Type*} [Fintype S]
    (μ : Games.FiniteDistribution S) (s : S) : μ.weight s ≤ 1 := by
  calc
    μ.weight s ≤ ∑ t, μ.weight t :=
      Finset.single_le_sum (fun t _ => μ.nonnegative t) (Finset.mem_univ s)
    _ = 1 := μ.normalized

variable {Q₁ Q₂ S : Type*} [Fintype Q₁] [Fintype Q₂] [Fintype S]

def sharedProfileThresholds (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) : List ℝ :=
  profileThresholds (fun (k : Q₁ ⊕ Q₂) s => (Sum.elim L R k).weight s)

theorem left_mem_sharedProfileThresholds (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (x : Q₁) (s : S) :
    (L x).weight s ∈ sharedProfileThresholds L R := by
  exact mem_profileThresholds _ (Sum.inl x) s

theorem right_mem_sharedProfileThresholds (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (y : Q₂) (s : S) :
    (R y).weight s ∈ sharedProfileThresholds L R := by
  exact mem_profileThresholds _ (Sum.inr y) s

abbrev SharedProfileSeed (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) :=
  RectangleSeed (sharedProfileThresholds L R) S

def sharedProfileLeft (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (x : Q₁) : SharedProfileSeed L R → Bool :=
  rectangleAccept (sharedProfileThresholds L R) (L x).weight

def sharedProfileRight (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (y : Q₂) : SharedProfileSeed L R → Bool :=
  rectangleAccept (sharedProfileThresholds L R) (R y).weight

def sharedProfileReject (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (x : Q₁) (y : Q₂) : ℝ :=
  eventMass (rectangleWeight (sharedProfileThresholds L R))
    (fun s => !(sharedProfileLeft L R x s || sharedProfileRight L R y s))

end

end UniqueGamesTheorem.Foundations.CorrelatedSampling

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_Overlap
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

theorem sum_min_one_sub_tv {Ω : Type*} [Fintype Ω]
    (p q : Ω → ℝ) (hp : IsProbability p) (hq : IsProbability q) :
    (∑ z, min (p z) (q z)) = 1 - totalVariation p q := by
  classical
  simp_rw [min_half_formula]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, hp.2, hq.2, totalVariation]
  ring

/-- The direct common-mass argument, with its exact finite-array premises. -/
theorem discounted_common_mass_bounds {X S : Type*} [Fintype X] [Fintype S]
    (p a b : X × S → ℝ) (μ t : X → ℝ)
    (hp : IsProbability p) (ha : IsProbability a) (hb : IsProbability b)
    (ht : ∀ x, 0 ≤ t x)
    (hrow : ∀ x, (∑ s, a (x, s)) = μ x)
    (htv : (∑ x, μ x * t x) = totalVariation a b) :
    1 - 2 * totalVariation p a - 2 * totalVariation p b ≤ discountedCommonMass p a b t ∧
      discountedCommonMass p a b t ≤ 1 := by
  classical
  let C : X × S → ℝ := fun z => min (p z) (min (a z) (b z))
  have hC0 : ∀ z, 0 ≤ C z := by
    intro z
    exact le_min (hp.1 z) (le_min (ha.1 z) (hb.1 z))
  have hCp : ∀ z, C z ≤ p z := by
    intro z
    exact min_le_left _ _
  have hCa : ∀ z, C z ≤ a z := by
    intro z
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hmass : 1 - totalVariation p a - totalVariation p b ≤ ∑ z, C z := by
    have hpoint : ∀ z, min (p z) (a z) + min (p z) (b z) - p z ≤ C z := by
      intro z
      dsimp [C]
      refine le_min ?_ (le_min ?_ ?_)
      · linarith [min_le_left (p z) (a z), min_le_left (p z) (b z)]
      · linarith [min_le_right (p z) (a z), min_le_left (p z) (b z)]
      · linarith [min_le_right (p z) (b z), min_le_left (p z) (a z)]
    have hsum := Finset.sum_le_sum
      (fun z (_ : z ∈ (Finset.univ : Finset (X × S))) => hpoint z)
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
    rw [sum_min_one_sub_tv p a hp ha, sum_min_one_sub_tv p b hp hb, hp.2] at hsum
    linarith
  have hrowC : ∀ x, (∑ s, C (x, s)) ≤ μ x := by
    intro x
    calc
      (∑ s, C (x, s)) ≤ ∑ s, a (x, s) := Finset.sum_le_sum (fun s _ => hCa (x, s))
      _ = μ x := hrow x
  have hweighted : (∑ z, C z * t z.1) ≤ totalVariation a b := by
    rw [← htv, Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro x _
    change (∑ s, C (x, s) * t x) ≤ μ x * t x
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrowC x) (ht x)
  have hloss : (∑ z, C z) - discountedCommonMass p a b t ≤ ∑ z, C z * t z.1 := by
    change (∑ z, C z) - (∑ z, C z / (1 + t z.1)) ≤ ∑ z, C z * t z.1
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun z _ => discount_loss_le_mul (hC0 z) (ht z.1))
  have htriangle : totalVariation a b ≤ totalVariation p a + totalVariation p b := by
    have h := totalVariation_triangle a p b
    rw [totalVariation_symm a p] at h
    exact h
  have hupper : discountedCommonMass p a b t ≤ 1 := by
    change (∑ z, C z / (1 + t z.1)) ≤ 1
    calc
      _ ≤ ∑ z, p z := Finset.sum_le_sum
        (fun z _ => (discount_le_self (hC0 z) (ht z.1)).trans (hCp z))
      _ = 1 := hp.2
  exact ⟨by linarith, hupper⟩

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

theorem diagonal_overlap_identity {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) (sim : X × S × S → ℝ)
    (hp : IsProbability p) (hsim : IsProbability sim) :
    totalVariation sim (diagonalWeights p) =
      1 - ∑ z : X × S, min (p z) (sim (z.1, z.2, z.2)) := by
  classical
  have h := sum_min_one_sub_tv sim (diagonalWeights p) hsim (diagonalWeights_isProbability p hp)
  have heq : (∑ z, min (sim z) (diagonalWeights p z)) =
      ∑ z : X × S, min (p z) (sim (z.1, z.2, z.2)) := by
    simp only [Fintype.sum_prod_type, diagonalWeights]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro s _
    have hpoint : ∀ s', min (sim (x, s, s')) (if s = s' then p (x, s) else 0) =
        if s = s' then min (p (x, s)) (sim (x, s, s')) else 0 := by
      intro s'
      by_cases he : s = s'
      · simp [he, min_comm]
      · simp [he, min_eq_right (hsim.1 (x, s, s'))]
    simp only [hpoint]
    simp
  rw [heq] at h
  linarith

/-- The per-label diagonal guarantee implies direct TV control even when the
target's question marginal differs from the simulator's question marginal. -/
theorem diagonal_sampler_totalVariation_le {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) (μ : X → ℝ) (L R : X → S → ℝ)
    (sim : X × S × S → ℝ) (hp : IsProbability p) (hμ : IsProbability μ)
    (hL : ∀ x, IsProbability (L x)) (hR : ∀ x, IsProbability (R x))
    (hsim : IsProbability sim) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hdiag : ∀ x s, μ x * min (L x s) (R x s) /
      (1 + totalVariation (L x) (R x)) * (1 - τ) ≤ sim (x, s, s)) :
    totalVariation sim (diagonalWeights p) ≤
      2 * totalVariation p (fun z => μ z.1 * L z.1 z.2) +
      2 * totalVariation p (fun z => μ z.1 * R z.1 z.2) + τ := by
  classical
  let a : X × S → ℝ := fun z => μ z.1 * L z.1 z.2
  let b : X × S → ℝ := fun z => μ z.1 * R z.1 z.2
  let t : X → ℝ := fun x => totalVariation (L x) (R x)
  let C : X × S → ℝ := fun z => min (p z) (min (a z) (b z))
  have ha : IsProbability a := kernelProduct_isProbability μ L hμ hL
  have hb : IsProbability b := kernelProduct_isProbability μ R hμ hR
  have ht : ∀ x, 0 ≤ t x := fun x => totalVariation_nonneg (L x) (R x)
  have hrow : ∀ x, (∑ s, a (x, s)) = μ x := by
    intro x
    simp only [a, ← Finset.mul_sum, (hL x).2, mul_one]
  have htv : (∑ x, μ x * t x) = totalVariation a b :=
    (totalVariation_joint_common_weights μ L R hμ.1).symm
  obtain ⟨hBlower, hBupper⟩ := discounted_common_mass_bounds p a b μ t hp ha hb ht hrow htv
  have hpoint : ∀ z : X × S,
      (1 - τ) * (C z / (1 + t z.1)) ≤ min (p z) (sim (z.1, z.2, z.2)) := by
    intro z
    have hden : 0 < 1 + t z.1 := by linarith [ht z.1]
    have hC0 : 0 ≤ C z := le_min (hp.1 z) (le_min (ha.1 z) (hb.1 z))
    have hCp : C z ≤ p z := min_le_left _ _
    have hdisc0 : 0 ≤ C z / (1 + t z.1) := div_nonneg hC0 hden.le
    have hmin : min (a z) (b z) = μ z.1 * min (L z.1 z.2) (R z.1 z.2) := by
      dsimp [a, b]
      rcases le_total (L z.1 z.2) (R z.1 z.2) with h | h
      · rw [min_eq_left h, min_eq_left (mul_le_mul_of_nonneg_left h (hμ.1 z.1))]
      · rw [min_eq_right h, min_eq_right (mul_le_mul_of_nonneg_left h (hμ.1 z.1))]
    have hCmin : C z ≤ μ z.1 * min (L z.1 z.2) (R z.1 z.2) := by
      rw [← hmin]
      exact min_le_right _ _
    apply le_min
    · calc
        _ ≤ 1 * (C z / (1 + t z.1)) :=
          mul_le_mul_of_nonneg_right (by linarith) hdisc0
        _ ≤ C z := by simpa using discount_le_self hC0 (ht z.1)
        _ ≤ p z := hCp
    · have hd := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hCmin hden.le) (by linarith : 0 ≤ 1 - τ)
      calc
        _ ≤ (1 - τ) * (μ z.1 * min (L z.1 z.2) (R z.1 z.2) / (1 + t z.1)) := hd
        _ ≤ sim (z.1, z.2, z.2) := by
          simpa only [t, mul_comm] using hdiag z.1 z.2
  have hsum := Finset.sum_le_sum (fun z (_ : z ∈ (Finset.univ : Finset (X × S))) => hpoint z)
  rw [← Finset.mul_sum] at hsum
  change (1 - τ) * discountedCommonMass p a b t ≤ _ at hsum
  rw [diagonal_overlap_identity p sim hp hsim]
  have hτB := mul_le_mul_of_nonneg_left hBupper hτ0
  change 1 - _ ≤ 2 * totalVariation p a + 2 * totalVariation p b + τ
  nlinarith

end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_SelectedCommonMarginalLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

theorem partialRevealMarginal_secondMarginal
    (μ : FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    secondMarginal (partialRevealMarginal μ j likelihood) =
      secondMarginal (fullRevealMarginal μ j likelihood) := by
  classical
  funext q
  calc
    _ = ∑ z : (T × ({i : I // i ≠ j} → X ⊕ Y)) × (X ⊕ Y),
        maskedJoint (partialRevealMarginal μ j likelihood) (z,q) := by
      simp [secondMarginal, Fintype.sum_prod_type, maskedJoint]
    _ = _ := by
      apply Fintype.sum_equiv (revealDataSplitEquiv (T := T) j).symm
      intro z
      exact (fullRevealMarginal_merge μ j likelihood z.1.1 z.1.2 z.2 q).symm

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

theorem selectedFullReveal_secondMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) :
    secondMarginal (fullRevealMarginal G.questions j
      (selectedOutsideLikelihood G strategy selected)) =
        secondMarginal (selectedRawMarginal G strategy selected j) := by
  classical
  funext q
  apply Fintype.sum_equiv
    (selectedObservationDataEquiv (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected).symm
  intro z
  exact (selectedRawMarginal_fullReveal G strategy selected j (z,q)).symm

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

def updatedTableFallback (μ : FiniteDistribution X) (j : I) (x : X) :
    FiniteDistribution (I → X) :=
  (FiniteDistribution.table (fun _ : I => μ)).pushforward
    (fun l => Function.update l j x)

theorem updatedTableFallback_zero (μ : FiniteDistribution X) (j : I) (x : X)
    (l : I → X) (hne : l j ≠ x) :
    (updatedTableFallback μ j x).weight l = 0 := by
  classical
  simp only [updatedTableFallback, FiniteDistribution.pushforward]
  apply Finset.sum_eq_zero
  intro t _
  apply ite_eq_right
  intro h
  have he := congrFun h j
  exact hne (by simpa only [Function.update_self] using he.symm)

theorem normalizeOr_weight_eq_zero_of_zero
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (fallback : FiniteDistribution X)
    (x : X) (hraw : w x = 0) (hdefault : fallback.weight x = 0) :
    (normalizeOr w hw fallback).weight x = 0 := by
  classical
  unfold normalizeOr
  split
  · change normalizedWeight w x = 0
    simp only [normalizedWeight, hraw, zero_div]
  · exact hdefault

end LocalNormalization

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedLeftRaw (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (x : Q₁) (l : {i : Fin n // i ∉ selected} → Q₁) : ℝ :=
  (if l j = x then 1 else 0) * partialLeftFactor G.questions j s.2 l *
    selectedLocalTest strategy.1 selected (fun i => (s.1.1 i).1) s.1.2.1 l

def selectedRightRaw (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (y : Q₂) (r : {i : Fin n // i ∉ selected} → Q₂) : ℝ :=
  (if r j = y then 1 else 0) * partialRightFactor G.questions j s.2 r *
    selectedLocalTest strategy.2 selected (fun i => (s.1.1 i).2) s.1.2.2 r

omit [DecidableEq Q₂] in
theorem selectedLeftRaw_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (x : Q₁) (l : {i : Fin n // i ∉ selected} → Q₁) :
    0 ≤ selectedLeftRaw G strategy selected j s x l := by
  apply mul_nonneg
  · apply mul_nonneg
    · split <;> norm_num
    · exact Finset.prod_nonneg (fun i _ => revealLeftFactor_nonnegative G.questions (s.2 i) (l i.1))
  · exact selectedLocalTest_nonnegative _ _ _ _ _

omit [DecidableEq Q₁] in
theorem selectedRightRaw_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (y : Q₂) (r : {i : Fin n // i ∉ selected} → Q₂) :
    0 ≤ selectedRightRaw G strategy selected j s y r := by
  apply mul_nonneg
  · apply mul_nonneg
    · split <;> norm_num
    · exact Finset.prod_nonneg (fun i _ => revealRightFactor_nonnegative G.questions (s.2 i) (r i.1))
  · exact selectedLocalTest_nonnegative _ _ _ _ _

def selectedLeftCompletion (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (x : Q₁) : FiniteDistribution ({i : Fin n // i ∉ selected} → Q₁) :=
  normalizeOr (selectedLeftRaw G strategy selected j s x)
    (selectedLeftRaw_nonnegative G strategy selected j s x)
    (updatedTableFallback (G.questions.pushforward Prod.fst) j x)

def selectedRightCompletion (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (y : Q₂) : FiniteDistribution ({i : Fin n // i ∉ selected} → Q₂) :=
  normalizeOr (selectedRightRaw G strategy selected j s y)
    (selectedRightRaw_nonnegative G strategy selected j s y)
    (updatedTableFallback (G.questions.pushforward Prod.snd) j y)

omit [DecidableEq Q₂] in
theorem selectedLeftCompletion_zero (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (x : Q₁) (l : {i : Fin n // i ∉ selected} → Q₁) (hne : l j ≠ x) :
    (selectedLeftCompletion G strategy selected j s x).weight l = 0 := by
  apply normalizeOr_weight_eq_zero_of_zero
  · simp only [selectedLeftRaw, ite_eq_right hne, zero_mul]
  · exact updatedTableFallback_zero _ j x l hne

omit [DecidableEq Q₁] in
theorem selectedRightCompletion_zero (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (y : Q₂) (r : {i : Fin n // i ∉ selected} → Q₂) (hne : r j ≠ y) :
    (selectedRightCompletion G strategy selected j s y).weight r = 0 := by
  apply normalizeOr_weight_eq_zero_of_zero
  · simp only [selectedRightRaw, ite_eq_right hne, zero_mul]
  · exact updatedTableFallback_zero _ j y r hne

def selectedCompletionScale (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (xy : Q₁ × Q₂) : ℝ :=
  G.questions.weight xy * (∏ i : selected, G.questions.weight (s.1.1 i)) *
    (if selectedLabelAccepts G selected s.1.1 s.1.2 then 1 else 0) /
      G.selectedSuccess strategy selected

/-- Pointwise factorization of the actual selected common-data row. -/
theorem selected_completion_factorization (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (xy : Q₁ × Q₂)
    (l : {i : Fin n // i ∉ selected} → Q₁)
    (r : {i : Fin n // i ∉ selected} → Q₂) :
    selectedCompletionScale G strategy selected j s xy *
        selectedLeftRaw G strategy selected j s xy.1 l *
        selectedRightRaw G strategy selected j s xy.2 r =
      if (l j, r j) = xy then
        partialRevealWeight G.questions j s.2 (fun i => (l i,r i)) *
          selectedOutsideLikelihood G strategy selected s.1 (fun i => (l i,r i))
      else 0 := by
  rcases xy with ⟨x,y⟩
  by_cases hl : l j = x <;> by_cases hr : r j = y
  · rw [ite_eq_left (Prod.ext hl hr), partialRevealWeight_factorization]
    cases hacc : selectedLabelAccepts G selected s.1.1 s.1.2 <;>
      simp [selectedOutsideLikelihood, selectedLikelihood_factorization,
        selectedCompletionScale, selectedLeftRaw, selectedRightRaw, hl, hr, hacc]
    ring
  · simp [selectedLeftRaw, selectedRightRaw, hl, hr, Prod.mk.injEq]
  · simp [selectedLeftRaw, selectedRightRaw, hl, hr, Prod.mk.injEq]
  · simp [selectedLeftRaw, selectedRightRaw, hl, hr, Prod.mk.injEq]

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! The actual local completion mixture reproduces the repeated question law
conditioned on the selected wins. All hidden coordinates and reveal variables
are explicitly summed out. -/

namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games
noncomputable section

theorem partialRevealWeight_forget
    {I X Y : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (μ : FiniteDistribution (X × Y)) (j : I) (u : I → X × Y) :
    (∑ rest : {i : I // i ≠ j} → X ⊕ Y, partialRevealWeight μ j rest u) =
      ∏ i, μ.weight (u i) := by
  have h := reveal_product_forget μ (fun i : {i : I // i ≠ j} => u i.1)
  simp_rw [reveal_product_factorization] at h
  simp only [partialRevealWeight, ← Finset.mul_sum]
  rw [h]
  exact (Fintype.prod_eq_mul_prod_subtype_ne (fun i => μ.weight (u i)) j).symm

theorem partialReveal_event_forget
    {I X Y : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (μ : FiniteDistribution (X × Y)) (j : I) (f : (I → X × Y) → ℝ) :
    (∑ rest : {i : I // i ≠ j} → X ⊕ Y,
      ∑ u : I → X × Y, partialRevealWeight μ j rest u * f u) =
      ∑ u, (∏ i, μ.weight (u i)) * f u := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.sum_mul, partialRevealWeight_forget]

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedFullLeftCompletion (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (q : Q₁ × SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j) :
    FiniteDistribution (Fin n → Q₁) :=
  (selectedLeftCompletion G strategy selected j q.2 q.1).pushforward
    (mergeCoordinates selected (fun i => (q.2.1.1 i).1))

def selectedFullRightCompletion (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (q : Q₂ × SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j) :
    FiniteDistribution (Fin n → Q₂) :=
  (selectedRightCompletion G strategy selected j q.2 q.1).pushforward
    (mergeCoordinates selected (fun i => (q.2.1.1 i).2))

omit [DecidableEq Q₂] in
theorem selectedFullLeftCompletion_support (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (q : Q₁ × SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (l : Fin n → Q₁) (h : (selectedFullLeftCompletion G strategy selected j q).weight l ≠ 0) :
    l j.1 = q.1 := by
  classical
  by_contra hne
  apply h
  simp only [selectedFullLeftCompletion, FiniteDistribution.pushforward]
  apply Finset.sum_eq_zero
  intro t _
  split
  · rename_i he
    apply selectedLeftCompletion_zero
    intro ht
    apply hne
    have hcoord := congrFun he j.1
    simpa [mergeCoordinates, j.property, ht] using hcoord.symm
  · rfl

omit [DecidableEq Q₁] in
theorem selectedFullRightCompletion_support (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (q : Q₂ × SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (r : Fin n → Q₂) (h : (selectedFullRightCompletion G strategy selected j q).weight r ≠ 0) :
    r j.1 = q.1 := by
  classical
  by_contra hne
  apply h
  simp only [selectedFullRightCompletion, FiniteDistribution.pushforward]
  apply Finset.sum_eq_zero
  intro t _
  split
  · rename_i he
    apply selectedRightCompletion_zero
    intro ht
    apply hne
    have hcoord := congrFun he j.1
    simpa [mergeCoordinates, j.property, ht] using hcoord.symm
  · rfl

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! Actual finite shared seed laws for the bounded correlated sampler. -/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

universe u

/-- The law of the two local outputs, driven by a seed chosen independently
of the question pair. Local maps receive only their own question. -/
def sharedOutputLaw {X Y S Seed : Type*}
    [Fintype X] [Fintype Y] [Fintype S] [Fintype Seed] [DecidableEq S]
    (μ : FiniteDistribution (X × Y)) (seedLaw : FiniteDistribution Seed)
    (left : Seed → X → S) (right : Seed → Y → S) :
    FiniteDistribution ((X × Y) × S × S) :=
  (μ.product seedLaw).pushforward
    (fun z => (z.1, left z.2 z.1.1, right z.2 z.1.2))

theorem sharedOutputLaw_weight {X Y S Seed : Type*}
    [Fintype X] [Fintype Y] [Fintype S] [Fintype Seed] [DecidableEq S]
    (μ : FiniteDistribution (X × Y)) (seedLaw : FiniteDistribution Seed)
    (left : Seed → X → S) (right : Seed → Y → S) (x : X) (y : Y) (a b : S) :
    (sharedOutputLaw μ seedLaw left right).weight ((x,y),a,b) =
      μ.weight (x,y) * seedLaw.expectation
        (fun seed => if left seed x = a ∧ right seed y = b then 1 else 0) := by
  classical
  simp only [sharedOutputLaw, FiniteDistribution.pushforward,
    FiniteDistribution.product, Fintype.sum_prod_type, Prod.mk.injEq]
  simp only [and_assoc, ite_and]
  simp [FiniteDistribution.expectation, Finset.mul_sum, mul_ite]

section Rectangle

open CorrelatedSampling

variable {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S]
  [Nonempty S] [DecidableEq S]

def samplerLocal (thresholds : List ℝ) (profile : X → FiniteDistribution S)
    (fallback : S) (n : Nat) (seed : TraceSeed (RectangleSeed thresholds S) n)
    (x : X) : S :=
  localSample (rectangleAccept thresholds (profile x).weight) Prod.fst fallback
    (traceList n seed)

omit [Nonempty S] [DecidableEq S] in
theorem probability_weight_le_one (μ : FiniteDistribution S) (s : S) : μ.weight s ≤ 1 := by
  calc
    μ.weight s ≤ ∑ t, μ.weight t :=
      Finset.single_le_sum (fun t _ => μ.nonnegative t) (Finset.mem_univ s)
    _ = 1 := μ.normalized

end Rectangle

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_SelectionSequence
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Repetition.SelectionSequence

theorem selectedSet_card {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j) (m : Nat) :
    (selectedSet Step witness m).card = min m n := by
  induction m with
  | zero => simp [selectedSet]
  | succ m ih =>
    by_cases hm : m < n
    · have hc : (selectedSet Step witness m).card = m := by
        simpa only [Nat.min_eq_left (Nat.le_of_lt hm)] using ih
      have hs : (selectedSet Step witness m).card < n := by
        simpa only [hc] using hm
      rw [selectedSet, nextSet, dite_eq_left hs,
        Finset.card_insert_of_notMem ((Classical.choose_spec (witness _ hs)).1),
        hc, Nat.min_eq_left (Nat.succ_le_of_lt hm)]
    · have hc : (selectedSet Step witness m).card = n := by
        simpa only [Nat.min_eq_right (Nat.le_of_not_gt hm)] using ih
      have hs : ¬(selectedSet Step witness m).card < n := by
        rw [hc]
        exact Nat.not_lt.mpr (Nat.le_refl n)
      rw [selectedSet, nextSet, dite_eq_right hs, hc,
        Nat.min_eq_right (Nat.le_trans (Nat.le_of_not_gt hm) (Nat.le_succ m))]

theorem selectedSet_univ {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j) :
    selectedSet Step witness n = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  simp [selectedSet_card]

theorem selectedSet_step {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j)
    (m : Nat) (hm : m < n) :
    ∃ j, j ∉ selectedSet Step witness m ∧
      selectedSet Step witness (m + 1) = insert j (selectedSet Step witness m) ∧
      Step (selectedSet Step witness m) j := by
  have hc : (selectedSet Step witness m).card = m := by
    rw [selectedSet_card, Nat.min_eq_left (Nat.le_of_lt hm)]
  have hs : (selectedSet Step witness m).card < n := by simpa only [hc] using hm
  let j := Classical.choose (witness (selectedSet Step witness m) hs)
  have hj := Classical.choose_spec (witness (selectedSet Step witness m) hs)
  refine ⟨j, hj.1, ?_, hj.2⟩
  simp only [selectedSet, nextSet, dite_eq_left hs, j]

/-- The multiplicative scalar inequality for one actual selected-set update. -/
def SetStep {n : Nat} (P : Finset (Fin n) → ℝ) (v ell : ℝ)
    (S : Finset (Fin n)) (j : Fin n) : Prop :=
  P (insert j S) ≤ P S *
    (v + 15 * Real.sqrt (((S.card : ℝ) * ell + logTwo (1 / P S)) /
      ((n : ℝ) - S.card)))

/-- At zero success, any unused coordinate is safe and no conditioning occurs. -/
theorem totalSetStep {n : Nat} (P : Finset (Fin n) → ℝ) (v ell : ℝ)
    (hnonneg : ∀ S, 0 ≤ P S) (hanti : Antitone P)
    (hpositive : ∀ S, S.card < n → 0 < P S →
      ∃ j, j ∉ S ∧ SetStep P v ell S j) :
    ∀ S, S.card < n → ∃ j, j ∉ S ∧ SetStep P v ell S j := by
  intro S hcard
  by_cases hp : 0 < P S
  · exact hpositive S hcard hp
  · obtain ⟨j, hj⟩ := exists_unused S hcard
    have hz : P S = 0 := le_antisymm (le_of_not_gt hp) (hnonneg S)
    have hnext : P (insert j S) = 0 := le_antisymm
      ((hanti (Finset.subset_insert j S)).trans (le_of_eq hz)) (hnonneg (insert j S))
    refine ⟨j, hj, ?_⟩
    simpa only [SetStep, hnext, hz, zero_mul] using (le_refl (0 : ℝ))

/-- Construct the scalar sequence from actual selected-set probabilities. -/
theorem exists_scalar_sequence {n : Nat} (P : Finset (Fin n) → ℝ) (v ell : ℝ)
    (hempty : P ∅ = 1) (hnonneg : ∀ S, 0 ≤ P S) (hanti : Antitone P)
    (hpositive : ∀ S, S.card < n → 0 < P S →
      ∃ j, j ∉ S ∧ SetStep P v ell S j) :
    ∃ p : Nat → ℝ, p 0 = 1 ∧ (∀ m, 0 ≤ p m) ∧ Antitone p ∧
      ScalarRecurrence p n v ell ∧ p n = P Finset.univ := by
  let witness := totalSetStep P v ell hnonneg hanti hpositive
  let sets := selectedSet (SetStep P v ell) witness
  let p := fun m => P (sets m)
  refine ⟨p, ?_, ?_, ?_, ?_, ?_⟩
  · change P (selectedSet (SetStep P v ell) witness 0) = 1
    simpa only [selectedSet] using hempty
  · intro m
    exact hnonneg (sets m)
  · intro i j hij
    exact hanti (selectedSet_monotone (SetStep P v ell) witness hij)
  · intro m hm
    obtain ⟨j, _, hnext, hbound⟩ :=
      selectedSet_step (SetStep P v ell) witness m hm
    have hc : (selectedSet (SetStep P v ell) witness m).card = m := by
      rw [selectedSet_card, Nat.min_eq_left (Nat.le_of_lt hm)]
    change P (selectedSet (SetStep P v ell) witness (m + 1)) ≤ _
    rw [hnext]
    simpa only [SetStep, hc] using hbound
  · change P (selectedSet (SetStep P v ell) witness n) = P Finset.univ
    rw [selectedSet_univ]

open UniqueGamesTheorem.Foundations.Games

end UniqueGamesTheorem.Foundations.Repetition.SelectionSequence

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_CompletedSamplingLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

section DistributionIdentities

variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

theorem mixture_totalVariation_le (μ ν : FiniteDistribution A)
    (K : A → FiniteDistribution B) :
    (μ.mixture K).totalVariation (ν.mixture K) ≤ μ.totalVariation ν := by
  simpa only [FiniteDistribution.totalVariation, FiniteDistribution.mixture,
    Information.totalVariation, kernelPushforward] using
      totalVariation_kernelPushforward_le μ.weight ν.weight
        (fun a => (K a).weight) (fun a => Information.gameLaw_isProbability (K a))

end DistributionIdentities

section Diagonal

variable {Z S : Type*} [Fintype Z] [Fintype S]

def diagonalLaw (σ : FiniteDistribution (Z × S)) : FiniteDistribution (Z × S × S) :=
  Information.toGameLaw (diagonalWeights σ.weight)
    (diagonalWeights_isProbability _ (Information.gameLaw_isProbability σ))

end Diagonal

section Completion

variable {X Y S Γ U V : Type*}
  [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ] [Fintype U] [Fintype V]
  [DecidableEq X] [DecidableEq Y] [DecidableEq S]

def seedLaw (γ : FiniteDistribution Γ)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    FiniteDistribution (Seed Γ X Y S U V) :=
  γ.product (KernelSampling.seedLaw L R)

def completionKernel (L : X × S → FiniteDistribution U)
    (R : Y × S → FiniteDistribution V) (z : (X × Y) × S × S) :
    FiniteDistribution (U × V) :=
  (L (z.1.1, z.2.1)).product (R (z.1.2, z.2.2))

/-- This is the shared-seed mixture used by `Game.localEmbeddingLaw`. -/
def outputLaw (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    FiniteDistribution (U × V) :=
  (seedLaw γ L R).mixture (fun seed =>
    μ.pushforward (fun q => (left sL seed q.1, right sR seed q.2)))

end Completion

section CoordinateCompletion

variable {I X Y S Γ : Type*}
  [Fintype I] [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y] [DecidableEq S]

def coordinateOutputLaw (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (j : I) (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution (I → X))
    (R : Y × S → FiniteDistribution (I → Y)) :
    FiniteDistribution ((I → X) × (I → Y)) :=
  (seedLaw γ L R).mixture (fun seed => μ.pushforward
    (fun q => (coordinateLeft j sL seed q.1, coordinateRight j sR seed q.2)))

end CoordinateCompletion

end

end UniqueGamesTheorem.Foundations.Repetition.CompletedSampling

end

section

/-! The two actual conditional common-data profiles used by the shared
sampler, with explicit normalized default laws on all null inputs. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

theorem finiteDistribution_nonempty {A : Type*} [Fintype A] (μ : FiniteDistribution A) :
    Nonempty A := by
  have hsum : (∑ a, μ.weight a) ≠ 0 := by rw [μ.normalized]; norm_num
  obtain ⟨a, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact ⟨a⟩

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedQuestionRadius_le_informationRadius [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) :
    Real.sqrt ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
      Real.log (1 / G.selectedSuccess strategy selected)) ≤
      selectedInformationRadius G strategy selected := by
  have hcard : (1 : ℝ) ≤ Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) := by
    exact_mod_cast (Nat.succ_le_of_lt
      (Fintype.card_pos : 0 < Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected)))
  have hlog := Real.log_nonneg hcard
  have hnonneg : 0 ≤ (Fintype.card {i : Fin n // i ∉ selected} : ℝ) := Nat.cast_nonneg _
  unfold selectedInformationRadius
  apply Real.sqrt_le_sqrt
  nlinarith

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_ActualSourceLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.ActualSource

open UniqueGamesTheorem.Integration.BinaryLinear

attribute [instance] SplitGadget.noiseFintype SplitGadget.noiseNonempty

end UniqueGamesTheorem.Reduction.ActualSource

end

section

/-! Transport of actual gadgets to the split coordinate model used by the reduction. -/

namespace UniqueGamesTheorem.Integration.SplitGadget

open BinaryLinear

variable {R : Type} [AddCommGroup R] [Module F2 R] [FiniteDimensional F2 R]

open UniqueGamesTheorem.Gadget.ActualGadget (Data stabilityError failureIndicator kernelError Satisfies)
open UniqueGamesTheorem.Reduction.ActualSource

/-- Move all ambient vectors through a linear equivalence, retaining the same
noise indices and their multiplicities. -/
noncomputable def transport {s d : Nat} (g : Data (Vector s))
    (φ : g.Ambient ≃ₗ[F2] Ambient s d)
    (he : ∀ c, φ (g.embed c) = (c, 0)) : SplitGadget s d where
  f x := g.f (φ.symm x)
  equivariant x c := by
    have hc : φ.symm (c, 0) = g.embed c := by rw [← he c]; simp
    rw [map_add, hc]
    exact g.equivariant (φ.symm x) c
  NoiseIndex := g.NoiseIndex
  noiseFintype := g.noiseFintype
  noiseNonempty := g.noiseNonempty
  noise i := φ (g.noise i)

end UniqueGamesTheorem.Integration.SplitGadget

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_FinalParametersLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Integration.SourceParameters

theorem logTwo_sixteen : UniqueGamesTheorem.Foundations.Repetition.logTwo 16 = 4 := by
  unfold UniqueGamesTheorem.Foundations.Repetition.logTwo
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  simp [hlog]

end UniqueGamesTheorem.Integration.SourceParameters

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Soundness_RawTargetLawLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalSimulation.firstInputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Concrete finite averaging for the projection upper bound

The coefficient samples here are actual functions `Fin t → (Fin m → ZMod 2)`.
Their law is the normalized finite uniform sum over all such functions. The
binomial moment formula is proved from this sum, without an independence or
binomial-distribution premise.
-/

namespace UniqueGamesTheorem.Soundness.RepeatedGameBounds

open scoped BigOperators

noncomputable section

/-! ## Actual weighted winning probabilities under a local simulation -/

open Foundations.Games

namespace Simulation

abbrev PredicateStrategies := IncidenceExtraction.Strategies

variable {QA QB A B OA OB X Y : Type}
  [Fintype QA] [Fintype QB] [Fintype A] [Fintype B]
  [Fintype OA] [Fintype OB] [Fintype X] [Fintype Y]

/-- Pass a Boolean verifier predicate to the already checked deterministic
local-reconstruction and incidence-extraction interface. -/
def predicateGame (G : Game QA QB A B) : PredicateGame QA QB A B :=
  ⟨fun qa qb a b => G.accepts qa qb a b = true⟩

def strategyPair (s : PredicateStrategies QA QB A B) : Strategy QA QB A B :=
  (s.first, s.second)

end Simulation

/-! ## The actual named projection predicate -/

namespace ActualProjection

open IncidenceExtraction

/-- At a single coordinate, actual projection acceptance supplies an accepted
named-incidence answer with no access to the retained index. -/
theorem accepts_implies_named_incidence
    {P R O N : Type} (g : Incidence O N) (single : P → Bool)
    (qa : ZeroInformation.FirstInput P R O)
    (qb : ZeroInformation.SecondInput P R O N)
    (answerA : FirstAnswer P) (answerB : SecondAnswer P)
    (h : accepts g single qa qb answerA answerB)
    (j : P) (hj : single j = true) (name : N)
    (hname : qb.question j = Sum.inr name) :
    g.namedAccepts (qa.question j) name (answerA.2 j) (answerB.2.2 j) := by
  obtain ⟨hvalid, hone, indices, hquestions, hproject⟩ := h
  refine ⟨indices j, ?_, ?_, ?_⟩
  · have hq := congrFun hquestions j
    simp [ZeroInformation.partnerQuestion, hj, hname] at hq
    exact hq.symm
  · simpa [hone] using hvalid j
  · subst answerB
    simp [project, ZeroInformation.projectSingles, hj]

end ActualProjection

end
end UniqueGamesTheorem.Soundness.RepeatedGameBounds

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Soundness_ActualPointAnswers
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Conversion of actual binary linear points to the named projection answers. -/

namespace UniqueGamesTheorem.Soundness.ActualPointAnswers
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open PartnerProjection PartnerMapCoordinates RawPartnerTarget
open RepeatedGameBounds

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : Nat}

def sourceTau : ActualHomogeneous.E k →ₗ[F2] F2 := LinearMap.fst F2 F2 _

end
end UniqueGamesTheorem.Soundness.ActualPointAnswers

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Soundness_ConditionalSimulationLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The genuine conditional experiment is the reconstructed repeated-game law. -/

namespace UniqueGamesTheorem.Soundness.ConditionalGameLaw
open scoped BigOperators
open Foundations.Games
open ConditionalIncidences ConditionalSimulation IncidenceExtraction RepeatedGameBounds

noncomputable section
attribute [local instance] Classical.propDecidable

variable {P R O N : Type}
  [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

def reconstructedEvent (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (e : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N))
    (questions : Fin (zeroSet J gamma).card → O × N) : Prop :=
  strategy.wins (ActualProjection.predicateGame (R := R) g (membershipBool J))
    (localFirstFromH J g.name gamma observed reference (fun j => (questions (e.symm j)).1))
    (localSecondFromH J g.name gamma observed reference (fun j => (questions (e.symm j)).2))

end
end UniqueGamesTheorem.Soundness.ConditionalGameLaw

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceNoiseParameterLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

theorem bitSign_xor (b c : Bool) :
    bitSign (b ^^ c) = bitSign b * bitSign c := by
  cases b <;> cases c <;> norm_num [bitSign]

theorem walsh_symm {I : Type*} [Fintype I] [DecidableEq I] (s x : Cube I) :
    walsh s x = walsh x s := by
  simp [walsh, Bool.and_comm]

theorem walsh_xor {I : Type*} [Fintype I] [DecidableEq I] (s x y : Cube I) :
    walsh s (cubeXor x y) = walsh s x * walsh s y := by
  simp only [walsh, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [cubeXor]
  cases s i <;> cases x i <;> cases y i <;> norm_num [bitSign]

theorem coordinate_orthogonality (s t : Bool) :
    (∑ x : Bool, bitSign (s && x) * bitSign (t && x)) =
      if s = t then 2 else 0 := by
  cases s <;> cases t <;> norm_num [bitSign, Fintype.sum_bool]

theorem walsh_sum_orthogonality {I : Type*} [Fintype I] [DecidableEq I]
    (s t : Cube I) :
    (∑ x, walsh s x * walsh t x) =
      if s = t then (Fintype.card (Cube I) : ℝ) else 0 := by
  classical
  simp only [walsh, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : I) (b : Bool) =>
    bitSign (s i && b) * bitSign (t i && b))]
  simp only [coordinate_orthogonality]
  by_cases h : s = t
  · subst t
    simp
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact ite_eq_right hi

theorem walsh_orthogonality {I : Type*} [Fintype I] [DecidableEq I]
    (s t : Cube I) :
    (𝔼 x, walsh s x * walsh t x) = if s = t then 1 else 0 := by
  classical
  rw [Fintype.expect_eq_sum_div_card, walsh_sum_orthogonality]
  split_ifs <;> simp

theorem walsh_inversion {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → ℝ) (x : Cube I) :
    (∑ s, coefficient f s * walsh s x) = f x := by
  classical
  unfold coefficient
  simp_rw [Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  have h (y : Cube I) :
      (∑ s, (f y * walsh s y) * walsh s x) =
        f y * (if y = x then (Fintype.card (Cube I) : ℝ) else 0) := by
    simp only [mul_assoc, ← Finset.mul_sum]
    congr 1
    simp_rw [walsh_symm (x := y), walsh_symm (x := x)]
    exact walsh_sum_orthogonality y x
  simp_rw [h]
  rw [Fintype.expect_eq_sum_div_card]
  simp

theorem walsh_inner {I : Type*} [Fintype I] [DecidableEq I] (f g : Cube I → ℝ) :
    (∑ s, coefficient f s * coefficient g s) = 𝔼 x, f x * g x := by
  classical
  unfold coefficient
  simp_rw [Finset.mul_expect]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro x _
  have h : (∑ s, (𝔼 y, f y * walsh s y) * (g x * walsh s x)) =
      g x * (∑ s, coefficient f s * walsh s x) := by
    simp only [Finset.mul_sum, coefficient]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [h, walsh_inversion]
  ring

theorem walsh_parseval {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → ℝ) :
    (∑ s, coefficient f s ^ 2) = 𝔼 x, f x ^ 2 := by
  simpa [pow_two] using walsh_inner f f

theorem sign_parseval {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → Bool) :
    (∑ s, coefficient (fun x => bitSign (f x)) s ^ 2) = 1 := by
  rw [walsh_parseval]
  simp

end UniqueGamesTheorem.Foundations.Hastad

end

end

section

noncomputable section

namespace UniqueGamesTheorem.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def support (s : Cube I) : Finset I := Finset.univ.filter fun i => s i = true

def noiseWeight (ε : ℝ) (μ : Cube I) : ℝ :=
  ∏ i, if μ i then ε else 1 - ε

theorem noiseWeight_sum (ε : ℝ) : (∑ μ : Cube I, noiseWeight ε μ) = 1 := by
  unfold noiseWeight
  rw [← Fintype.prod_sum (fun (_ : I) (b : Bool) => if b then ε else 1 - ε)]
  simp

theorem noise_walsh (ε : ℝ) (s : Cube I) :
    (∑ μ, noiseWeight ε μ * walsh s μ) = (1 - 2 * ε) ^ (support s).card := by
  unfold noiseWeight walsh
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i b =>
    (if b then ε else 1 - ε) * bitSign (s i && b))]
  have hc (i : I) : (∑ b : Bool,
      (if b then ε else 1 - ε) * bitSign (s i && b)) =
        if s i then 1 - 2 * ε else 1 := by
    cases s i <;> simp [bitSign]
    ring
  simp_rw [hc]
  simp [support, Finset.prod_ite]

/-- Walsh autocorrelation, proved by expanding the explicit basis. -/
theorem walsh_autocorrelation (B : Cube J → ℝ) (h : Cube J) :
    (𝔼 g, B g * B (cubeXor g h)) =
      ∑ s, coefficient B s ^ 2 * walsh s h := by
  conv_lhs =>
    enter [2, g, 2]
    rw [← walsh_inversion B (cubeXor g h)]
  simp_rw [Finset.mul_sum, walsh_xor]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have hterm : (fun g => B g * (coefficient B s * (walsh s g * walsh s h))) =
      (fun g => (coefficient B s * walsh s h) * (B g * walsh s g)) := by
    funext g
    ring
  rw [hterm, ← Finset.mul_expect]
  change (coefficient B s * walsh s h) * coefficient B s = _
  ring

def projectedCoefficient (π : J → I) (A : Cube I → ℝ) (s : Cube J) : ℝ :=
  𝔼 f, A f * walsh s (fun y => f (π y))

def testBias (ε : ℝ) (π : J → I) (A : Cube I → ℝ) (B : Cube J → ℝ) : ℝ :=
  𝔼 f, ∑ μ, noiseWeight ε μ * A f *
    (𝔼 g, B g * B (thirdQuery π f g μ))

theorem testBias_fourier (ε : ℝ) (π : J → I)
    (A : Cube I → ℝ) (B : Cube J → ℝ) :
    testBias ε π A B = ∑ s,
      projectedCoefficient π A s * coefficient B s ^ 2 *
        (1 - 2 * ε) ^ (support s).card := by
  unfold testBias thirdQuery
  simp_rw [walsh_autocorrelation, Finset.mul_sum]
  conv_lhs =>
    enter [2, f]
    rw [Finset.sum_comm]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have hterm (f : Cube I) :
      (∑ μ, noiseWeight ε μ * A f *
        (coefficient B s ^ 2 * walsh s (cubeXor (fun y => f (π y)) μ))) =
      (A f * walsh s (fun y => f (π y))) * coefficient B s ^ 2 *
        (1 - 2 * ε) ^ (support s).card := by
    simp_rw [walsh_xor]
    have heq (μ : Cube J) : noiseWeight ε μ * A f *
        (coefficient B s ^ 2 * (walsh s (fun y => f (π y)) * walsh s μ)) =
      ((A f * walsh s (fun y => f (π y))) * coefficient B s ^ 2) *
        (noiseWeight ε μ * walsh s μ) := by ring
    simp_rw [heq]
    rw [← Finset.mul_sum, noise_walsh]
  simp_rw [hterm, ← Finset.expect_mul]
  rfl

def testAcceptance (ε : ℝ) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool) : ℝ :=
  𝔼 f, ∑ μ, noiseWeight ε μ *
    (𝔼 g, if A f ^^ B g ^^ B (thirdQuery π f g μ) then 0 else 1)

theorem threeBit_indicator (a b c : Bool) :
    (if a ^^ b ^^ c then (0 : ℝ) else 1) =
      (1 + bitSign a * bitSign b * bitSign c) / 2 := by
  cases a <;> cases b <;> cases c <;> norm_num [bitSign]

/-- Actual acceptance is one half plus one half of the three-answer correlation. -/
theorem testAcceptance_eq (ε : ℝ) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool) :
    testAcceptance ε π A B =
      (1 + testBias ε π (fun f => bitSign (A f)) (fun g => bitSign (B g))) / 2 := by
  unfold testAcceptance testBias
  simp_rw [threeBit_indicator, div_eq_mul_inv,
    ← Finset.expect_mul, Finset.expect_add_distrib]
  simp only [Fintype.expect_const]
  have hterm (f : Cube I) (μ : Cube J) :
      noiseWeight ε μ * ((1 + 𝔼 g,
        bitSign (A f) * bitSign (B g) * bitSign (B (thirdQuery π f g μ))) * 2⁻¹) =
      (noiseWeight ε μ + noiseWeight ε μ * bitSign (A f) *
        (𝔼 g, bitSign (B g) * bitSign (B (thirdQuery π f g μ)))) * 2⁻¹ := by
    simp_rw [mul_assoc (bitSign (A f)), ← Finset.mul_expect]
    ring
  simp_rw [hterm, ← Finset.sum_mul, Finset.sum_add_distrib, noiseWeight_sum,
    ← Finset.expect_mul, Finset.expect_add_distrib]
  simp

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

theorem sum_cubeFlip (F : Cube I → ℝ) : (∑ f, F (cubeFlip f)) = ∑ f, F f := by
  refine Finset.sum_bij (fun f _ => cubeFlip f) ?_ ?_ ?_ ?_
  · intro f _
    exact Finset.mem_univ _
  · intro f _ g _ h
    have h' := congrArg cubeFlip h
    simpa only [cubeFlip_cubeFlip] using h'
  · intro g _
    exact ⟨cubeFlip g, Finset.mem_univ _, cubeFlip_cubeFlip g⟩
  · intro f _
    rfl

theorem coefficient_zero_of_odd (F : Cube I → ℝ)
    (hF : ∀ f, F (cubeFlip f) = -F f) :
    coefficient F (fun _ => false) = 0 := by
  have hs : (∑ f, F f) = 0 := by
    have h := sum_cubeFlip F
    simp_rw [hF, Finset.sum_neg_distrib] at h
    linarith
  simp [coefficient, walsh, bitSign, Fintype.expect_eq_sum_div_card, hs]

theorem coefficient_sign_zero_of_folded (A : Cube I → Bool)
    (hA : ∀ f, A (cubeFlip f) = !(A f)) :
    coefficient (fun f => bitSign (A f)) (fun _ => false) = 0 := by
  apply coefficient_zero_of_odd
  intro f
  rw [hA, bitSign_not]

omit [Fintype I] [DecidableEq I] in
theorem representative_flip (i₀ : I) (f : Cube I) :
    representative i₀ (cubeFlip f) = representative i₀ f := by
  cases hf : f i₀ <;> simp [representative, cubeFlip, hf]

omit [Fintype I] [DecidableEq I] in
theorem canonicalInput_flip (i₀ : I) (f : Cube I) :
    canonicalInput i₀ (cubeFlip f) = canonicalInput i₀ f := by
  apply Subtype.ext
  exact representative_flip i₀ f

omit [Fintype I] [DecidableEq I] in
theorem foldedAnswer_flip (i₀ : I) (table : HalfCube i₀ → Bool) (f : Cube I) :
    foldedAnswer i₀ table (cubeFlip f) = !(foldedAnswer i₀ table f) := by
  unfold foldedAnswer
  rw [canonicalInput_flip]
  change (table (canonicalInput i₀ f) ^^ !(f i₀)) =
    !(table (canonicalInput i₀ f) ^^ f i₀)
  cases table (canonicalInput i₀ f) <;> cases f i₀ <;> rfl

theorem foldedAnswer_zero_coefficient (i₀ : I) (table : HalfCube i₀ → Bool) :
    coefficient (fun f => bitSign (foldedAnswer i₀ table f)) (fun _ => false) = 0 :=
  coefficient_sign_zero_of_folded _ (foldedAnswer_flip i₀ table)

omit [Fintype I] [DecidableEq I] in
theorem foldedAnswer_dictator (i₀ i : I) (f : Cube I) :
    foldedAnswer i₀ (fun h => h.val i) f = f i := by
  cases hf : f i₀ <;> cases hi : f i <;>
    simp [foldedAnswer, canonicalInput, representative, cubeFlip, hf, hi]

theorem walsh_coordinateMask (s : Cube I) (i : I) :
    walsh s (coordinateMask i) = bitSign (s i) := by
  unfold walsh
  rw [Finset.prod_eq_single i]
  · simp [coordinateMask]
  · intro j _ hj
    simp [coordinateMask, hj, bitSign]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem walsh_cubeToggle (s : Cube I) (i : I) (f : Cube I) (hs : s i = true) :
    walsh s (cubeToggle i f) = -walsh s f := by
  rw [cubeToggle, walsh_xor, walsh_coordinateMask, hs]
  simp [bitSign]

theorem sum_cubeToggle (i : I) (F : Cube I → ℝ) :
    (∑ f, F (cubeToggle i f)) = ∑ f, F f := by
  refine Finset.sum_bij (fun f _ => cubeToggle i f) ?_ ?_ ?_ ?_
  · intro f _
    exact Finset.mem_univ _
  · intro f _ g _ h
    have h' := congrArg (cubeToggle i) h
    simpa only [cubeToggle_twice] using h'
  · intro g _
    exact ⟨cubeToggle i g, Finset.mem_univ _, cubeToggle_twice i g⟩
  · intro f _
    rfl

omit [Fintype I] in
theorem restrictQuery_cubeToggle (valid : I → Bool) (i : I)
    (hi : valid i = false) (f : Cube I) :
    restrictQuery valid (cubeToggle i f) = restrictQuery valid f := by
  funext j
  have hj : j.val ≠ i := by
    intro heq
    have hp := j.property
    rw [heq, hi] at hp
    contradiction
  simp [restrictQuery, cubeToggle, cubeXor, coordinateMask, hj]

theorem conditioned_coefficient_zero_invalid (valid : I → Bool)
    (B : Cube {i : I // valid i = true} → ℝ) (s : Cube I) (i : I)
    (hi : valid i = false) (hs : s i = true) :
    coefficient (fun f => B (restrictQuery valid f)) s = 0 := by
  have hsum := sum_cubeToggle i (fun f => B (restrictQuery valid f) * walsh s f)
  simp_rw [restrictQuery_cubeToggle valid i hi, walsh_cubeToggle s i _ hs,
    mul_neg, Finset.sum_neg_distrib] at hsum
  have hz : (∑ f, B (restrictQuery valid f) * walsh s f) = 0 := by linarith
  simp [coefficient, Fintype.expect_eq_sum_div_card, hz]

/-- Every coordinate returned from a nonzero conditioned Fourier mask is an
actual valid local assignment, proved from the concrete restriction map. -/
theorem conditioned_coefficient_support (valid : I → Bool)
    (B : Cube {i : I // valid i = true} → ℝ) (s : Cube I)
    (hne : coefficient (fun f => B (restrictQuery valid f)) s ≠ 0) :
    ∀ i ∈ support s, valid i = true := by
  intro i hi
  have hs := (Finset.mem_filter.mp hi).2
  cases hv : valid i
  · exact False.elim (hne (conditioned_coefficient_zero_invalid valid B s i hv hs))
  · rfl

omit [Fintype I] [DecidableEq I] in
theorem conditionedFoldedAnswer_dictator (valid : I → Bool)
    (i₀ i : {i : I // valid i = true}) (f : Cube I) :
    conditionedFoldedAnswer valid i₀ (fun h => h.val i) f = f i.val := by
  exact foldedAnswer_dictator i₀ i (restrictQuery valid f)

end UniqueGamesTheorem.Foundations.Hastad

end

end

section

/-! The parity projection and finite Fourier decoder used in Håstad's
three-query argument. Probabilities are explicit finite sums. -/

noncomputable section

namespace UniqueGamesTheorem.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def parityProjection (π : J → I) (s : Cube J) : Cube I := fun i =>
  decide (Odd ((support s).filter fun y => π y = i).card)

theorem walsh_support (s x : Cube I) :
    walsh s x = ∏ i ∈ support s, bitSign (x i) := by
  unfold walsh support
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _
  cases s i <;> simp [bitSign]

theorem sign_power_parity (b : Bool) (n : Nat) :
    bitSign b ^ n = bitSign (decide (Odd n) && b) := by
  cases b
  · simp [bitSign]
  · simp only [Bool.and_true, bitSign, ite_true, if_true, decide_eq_true_eq]
    rw [neg_one_pow_eq_ite]
    by_cases h : Even n
    · simp [h, Nat.not_odd_iff_even.mpr h]
    · simp [h, Nat.not_even_iff_odd.mp h]

theorem walsh_pullback (π : J → I) (s : Cube J) (f : Cube I) :
    walsh s (fun y => f (π y)) = walsh (parityProjection π s) f := by
  rw [walsh_support]
  rw [← Finset.prod_fiberwise' (support s) π (fun i => bitSign (f i))]
  unfold walsh parityProjection
  apply Finset.prod_congr rfl
  intro i _
  simp only [Finset.prod_const]
  exact sign_power_parity (f i) _

theorem projectedCoefficient_eq (π : J → I) (A : Cube I → ℝ) (s : Cube J) :
    projectedCoefficient π A s = coefficient A (parityProjection π s) := by
  simp only [projectedCoefficient, coefficient, walsh_pullback]

omit [DecidableEq J] in
theorem projection_has_preimage (π : J → I) (s : Cube J) (i : I)
    (hi : i ∈ support (parityProjection π s)) :
    ∃ y ∈ support s, π y = i := by
  have hodd : Odd ((support s).filter fun y => π y = i).card := by
    have hbit := (Finset.mem_filter.mp hi).2
    simpa only [parityProjection, decide_eq_true_eq] using hbit
  have hp : 0 < ((support s).filter fun y => π y = i).card := by
    obtain ⟨n, hn⟩ := hodd
    omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hp
  exact ⟨y, (Finset.mem_filter.mp hy).1, (Finset.mem_filter.mp hy).2⟩

def zeroMask : Cube I := fun _ => false

omit [DecidableEq I] in
theorem support_eq_empty_iff (s : Cube I) : support s = ∅ ↔ s = zeroMask := by
  constructor
  · intro h
    funext i
    have hi : i ∉ support s := by rw [h]; simp
    have : s i ≠ true := by simpa [support] using hi
    cases hs : s i <;> simp_all [zeroMask]
  · intro h
    subst s
    simp [zeroMask, support]

omit [Fintype I] [DecidableEq J] in
theorem parityProjection_zero (π : J → I) :
    parityProjection π (zeroMask : Cube J) = zeroMask := by
  funext i
  simp [parityProjection, support, zeroMask]

/-- Choose uniform coordinates in the two masks and check the projection.
An empty support contributes zero. -/
def agreementProbability (π : J → I) (a : Cube I) (b : Cube J) : ℝ :=
  (∑ i ∈ support a, (((support b).filter fun y => π y = i).card : ℝ)) /
    ((support a).card * (support b).card : ℝ)

omit [DecidableEq J] in
theorem agreementProbability_nonneg (π : J → I) (a : Cube I) (b : Cube J) :
    0 ≤ agreementProbability π a b := by
  unfold agreementProbability
  apply div_nonneg
  · exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  · exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

omit [DecidableEq J] in
theorem agreementProbability_projection (π : J → I) (b : Cube J)
    (ha : (support (parityProjection π b)).Nonempty) :
    1 / ((support b).card : ℝ) ≤ agreementProbability π (parityProjection π b) b := by
  have hca : (0 : ℝ) < (support (parityProjection π b)).card :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr ha)
  have hb : (support b).Nonempty := by
    obtain ⟨i, hi⟩ := ha
    obtain ⟨y, hy, _⟩ := projection_has_preimage π b i hi
    exact ⟨y, hy⟩
  have hcb : (0 : ℝ) < (support b).card := Nat.cast_pos.mpr (Finset.card_pos.mpr hb)
  have hsum : ((support (parityProjection π b)).card : ℝ) ≤
      ∑ i ∈ support (parityProjection π b),
        (((support b).filter fun y => π y = i).card : ℝ) := by
    calc
      _ = ∑ _i ∈ support (parityProjection π b), (1 : ℝ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨y, hy, hπ⟩ := projection_has_preimage π b i hi
        have hp : 0 < ((support b).filter fun y => π y = i).card :=
          Finset.card_pos.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hπ⟩⟩
        exact_mod_cast hp
  unfold agreementProbability
  apply (div_le_div_iff₀ hcb (mul_pos hca hcb)).mpr
  nlinarith

/-- Select independent Walsh masks by squared coefficients and uniform points
in each support. The two selections use only the respective private tables. -/
def decoderSuccess (π : J → I) (A : Cube I → Bool) (B : Cube J → Bool) : ℝ :=
  ∑ b, coefficient (fun g => bitSign (B g)) b ^ 2 *
    (∑ a, coefficient (fun f => bitSign (A f)) a ^ 2 * agreementProbability π a b)

def decodingEnergy (π : J → I) (A : Cube I → ℝ) (B : Cube J → ℝ) : ℝ :=
  ∑ b, projectedCoefficient π A b ^ 2 * coefficient B b ^ 2 / (support b).card

theorem decodingEnergy_le_success (π : J → I) (A : Cube I → Bool) (B : Cube J → Bool)
    (hzero : coefficient (fun f => bitSign (A f)) zeroMask = 0) :
    decodingEnergy π (fun f => bitSign (A f)) (fun g => bitSign (B g)) ≤
      decoderSuccess π A B := by
  unfold decodingEnergy decoderSuccess
  apply Finset.sum_le_sum
  intro b _
  rw [projectedCoefficient_eq]
  have hsum :
      coefficient (fun f => bitSign (A f)) (parityProjection π b) ^ 2 *
        agreementProbability π (parityProjection π b) b ≤
      ∑ a, coefficient (fun f => bitSign (A f)) a ^ 2 * agreementProbability π a b := by
    apply Finset.single_le_sum (s := Finset.univ)
      (f := fun a => coefficient (fun f => bitSign (A f)) a ^ 2 * agreementProbability π a b)
    · intro a _
      exact mul_nonneg (sq_nonneg _) (agreementProbability_nonneg π a b)
    · exact Finset.mem_univ _
  have hm := mul_le_mul_of_nonneg_left hsum
    (sq_nonneg (coefficient (fun g => bitSign (B g)) b))
  by_cases ha : (support (parityProjection π b)).Nonempty
  · have hagree := agreementProbability_projection π b ha
    have ht := mul_le_mul_of_nonneg_left hagree
      (mul_nonneg (sq_nonneg (coefficient (fun f => bitSign (A f))
        (parityProjection π b))) (sq_nonneg (coefficient (fun g => bitSign (B g)) b)))
    have heq : coefficient (fun f => bitSign (A f)) (parityProjection π b) ^ 2 *
        coefficient (fun g => bitSign (B g)) b ^ 2 / (support b).card =
      (coefficient (fun f => bitSign (A f)) (parityProjection π b) ^ 2 *
        coefficient (fun g => bitSign (B g)) b ^ 2) * (1 / (support b).card) := by ring
    rw [heq]
    exact ht.trans (by convert hm using 1; ring)
  · have hempty : support (parityProjection π b) = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
    have hz := (support_eq_empty_iff _).mp hempty
    simpa [hz, hzero] using hm

theorem bias_sq_le_weighted_energy (ε : ℝ) (π : J → I)
    (A : Cube I → ℝ) (B : Cube J → Bool) :
    testBias ε π A (fun g => bitSign (B g)) ^ 2 ≤
      ∑ b, (projectedCoefficient π A b * coefficient (fun g => bitSign (B g)) b *
        (1 - 2 * ε) ^ (support b).card) ^ 2 := by
  rw [testBias_fourier]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun b => projectedCoefficient π A b * coefficient (fun g => bitSign (B g)) b *
      (1 - 2 * ε) ^ (support b).card)
    (fun b => coefficient (fun g => bitSign (B g)) b)
  rw [sign_parseval, mul_one] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem decoder_four_epsilon_bias_sq (ε : ℝ) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2)
    (hzero : coefficient (fun f => bitSign (A f)) zeroMask = 0) :
    4 * ε * testBias ε π (fun f => bitSign (A f)) (fun g => bitSign (B g)) ^ 2 ≤
      decoderSuccess π A B := by
  apply le_trans _ (decodingEnergy_le_success π A B hzero)
  have hcs := mul_le_mul_of_nonneg_left
    (bias_sq_le_weighted_energy ε π (fun f => bitSign (A f)) B)
    (by linarith : 0 ≤ 4 * ε)
  apply hcs.trans
  rw [Finset.mul_sum]
  unfold decodingEnergy
  apply Finset.sum_le_sum
  intro b _
  by_cases hk : 0 < (support b).card
  · have hd := noise_decay_bound hε hε' hk
    have hm := mul_le_mul_of_nonneg_left hd
      (mul_nonneg (sq_nonneg (projectedCoefficient π (fun f => bitSign (A f)) b))
        (sq_nonneg (coefficient (fun g => bitSign (B g)) b)))
    first | (convert hm using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hm.trans (le_of_eq (by ring)))
  · have hb : support b = ∅ := Finset.card_eq_zero.mp (by omega)
    have hbzero := (support_eq_empty_iff b).mp hb
    subst b
    simp [projectedCoefficient_eq, parityProjection_zero, hzero, support, zeroMask]

/-- A concrete folded half-table discharges the zero-coefficient condition. -/
theorem folded_decoder_bound (ε : ℝ) (π : J → I)
    (i₀ : I) (table : HalfCube i₀ → Bool) (B : Cube J → Bool)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    4 * ε * testBias ε π (fun f => bitSign (foldedAnswer i₀ table f))
      (fun g => bitSign (B g)) ^ 2 ≤ decoderSuccess π (foldedAnswer i₀ table) B := by
  exact decoder_four_epsilon_bias_sq ε π (foldedAnswer i₀ table) B hε hε'
    (foldedAnswer_zero_coefficient i₀ table)

def validAgreementProbability (valid : J → Bool) (π : J → I)
    (a : Cube I) (b : Cube J) : ℝ :=
  (∑ i ∈ support a,
    (((support b).filter fun y => π y = i ∧ valid y = true).card : ℝ)) /
    ((support a).card * (support b).card : ℝ)

omit [DecidableEq J] in
theorem validAgreementProbability_eq (valid : J → Bool) (π : J → I)
    (a : Cube I) (b : Cube J) (hb : ∀ y ∈ support b, valid y = true) :
    validAgreementProbability valid π a b = agreementProbability π a b := by
  unfold validAgreementProbability agreementProbability
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro y hy
  simp [hb y hy]

def validDecoderSuccess (valid : J → Bool) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool) : ℝ :=
  ∑ b, coefficient (fun g => bitSign (B g)) b ^ 2 *
    (∑ a, coefficient (fun f => bitSign (A f)) a ^ 2 *
      validAgreementProbability valid π a b)

/-- Clause validity in the decoded game follows from the concrete conditioned
table; no Fourier-support hypothesis is passed to this theorem. -/
theorem conditioned_validDecoderSuccess (valid : J → Bool) (π : J → I)
    (A : Cube I → Bool) (j₀ : {j : J // valid j = true})
    (table : HalfCube j₀ → Bool) :
    validDecoderSuccess valid π A (conditionedFoldedAnswer valid j₀ table) =
      decoderSuccess π A (conditionedFoldedAnswer valid j₀ table) := by
  unfold validDecoderSuccess decoderSuccess
  apply Finset.sum_congr rfl
  intro b _
  by_cases hc : coefficient (fun g => bitSign (conditionedFoldedAnswer valid j₀ table g)) b = 0
  · simp [hc]
  · have hb : ∀ y ∈ support b, valid y = true := by
      apply conditioned_coefficient_support valid (fun g => bitSign (foldedAnswer j₀ table g)) b
      exact hc
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [validAgreementProbability_eq valid π a b hb]

theorem conditioned_folded_decoder_bound (ε : ℝ) (π : J → I) (valid : J → Bool)
    (i₀ : I) (tableA : HalfCube i₀ → Bool)
    (j₀ : {j : J // valid j = true}) (tableB : HalfCube j₀ → Bool)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    4 * ε * testBias ε π (fun f => bitSign (foldedAnswer i₀ tableA f))
      (fun g => bitSign (conditionedFoldedAnswer valid j₀ tableB g)) ^ 2 ≤
      validDecoderSuccess valid π (foldedAnswer i₀ tableA)
        (conditionedFoldedAnswer valid j₀ tableB) := by
  rw [conditioned_validDecoderSuccess]
  exact folded_decoder_bound ε π i₀ tableA
    (conditionedFoldedAnswer valid j₀ tableB) hε hε'

end UniqueGamesTheorem.Foundations.Hastad

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_EncodingLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The finite set of realizable orbit records.  Vertices are the image of the
actual canonical-data map, so equal retained data from different questions
become one vertex.  The two sides remain distinct. -/

namespace UniqueGamesTheorem.Reduction.ActualOrbit

open UniqueGamesTheorem.Integration.BinaryLinear

universe u v

variable {Q : Type u} {T : Type v} {s d : Nat}

instance vertexNonempty [Nonempty Q] (can : Q → Ambient s d × T) :
    Nonempty (Vertex can) := Nonempty.map (vertex can) inferInstance

end UniqueGamesTheorem.Reduction.ActualOrbit

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_ExplicitLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
open UniqueGamesTheorem.Foundations.Hastad (noiseWeight)

theorem realizedBit_eq_true_iff {D : Nat} (positive : 0 < D) (z : Fin D) :
    realizedBit z = true ↔ z = ⟨0, positive⟩ := by
  simp [realizedBit, Fin.ext_iff]

/-- The two fibers of a coordinate have their actual normalized finite counts. -/
theorem coordinate_fiber_sum {D : Nat} (positive : 0 < D) (b : Bool) :
    (∑ z : Fin D, if realizedBit z = b then (D : ℝ)⁻¹ else 0) =
      if b then (D : ℝ)⁻¹ else 1 - (D : ℝ)⁻¹ := by
  have hd : (D : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt positive
  have ht : (∑ z : Fin D, if realizedBit z = true then (D : ℝ)⁻¹ else 0) =
      (D : ℝ)⁻¹ := by
    simp_rw [realizedBit_eq_true_iff positive]
    simp
  have htotal :
      (∑ z : Fin D, if realizedBit z = false then (D : ℝ)⁻¹ else 0) +
      (∑ z : Fin D, if realizedBit z = true then (D : ℝ)⁻¹ else 0) = 1 := by
    rw [← Finset.sum_add_distrib]
    have he (z : Fin D) :
        (if realizedBit z = false then (D : ℝ)⁻¹ else 0) +
          (if realizedBit z = true then (D : ℝ)⁻¹ else 0) = (D : ℝ)⁻¹ := by
      cases realizedBit z <;> simp
    simp_rw [he]
    simp [hd]
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, if_true]
  · linarith
  · exact ht

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Product distributivity computes the mass of every complete Boolean noise vector. -/
theorem noiseWeight_eq_fiber_sum {D : Nat} (positive : 0 < D) (μ : A → Bool) :
    noiseWeight ((D : ℝ)⁻¹) μ =
      ∑ z : A → Fin D,
        ∏ a, if realizedBit (z a) = μ a then (D : ℝ)⁻¹ else 0 := by
  rw [← Fintype.prod_sum (fun (a : A) (z : Fin D) =>
    if realizedBit z = μ a then (D : ℝ)⁻¹ else 0)]
  unfold noiseWeight
  apply Finset.prod_congr rfl
  intro a _
  exact (coordinate_fiber_sum positive (μ a)).symm

omit [DecidableEq A] in
theorem fiber_product_eq_indicator {D : Nat} (z : A → Fin D) (μ : A → Bool) :
    (∏ a, if realizedBit (z a) = μ a then (D : ℝ)⁻¹ else 0) =
      if realizedNoise z = μ then ((D : ℝ)⁻¹) ^ Fintype.card A else 0 := by
  classical
  by_cases h : realizedNoise z = μ
  · rw [ite_eq_left h]
    have ha (a : A) : realizedBit (z a) = μ a := congrFun h a
    simp [ha]
  · rw [ite_eq_right h]
    obtain ⟨a, ha⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    exact ite_eq_right ha

/-- Exact pushforward law for every observable, using the existing noise weight. -/
theorem expect_realizedNoise {D : Nat} (positive : 0 < D) (H : (A → Bool) → ℝ) :
    (𝔼 z : A → Fin D, H (realizedNoise z)) =
      ∑ μ : A → Bool, noiseWeight ((D : ℝ)⁻¹) μ * H μ := by
  classical
  symm
  simp_rw [noiseWeight_eq_fiber_sum positive, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [fiber_product_eq_indicator]
  have he (z : A → Fin D) :
      (∑ μ : A → Bool,
        (if realizedNoise z = μ then ((D : ℝ)⁻¹) ^ Fintype.card A else 0) * H μ) =
      ((D : ℝ)⁻¹) ^ Fintype.card A * H (realizedNoise z) := by
    simp [eq_comm]
  simp_rw [he]
  rw [Fintype.expect_eq_sum_div_card]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [div_eq_mul_inv, inv_pow]
  rw [← Finset.mul_sum]
  exact mul_comm _ _

end UniqueGamesTheorem.Reduction.FiniteNoise

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_NoiseEnumerationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! An explicit enumeration of noise indices, retaining repeated vector values.
This additional data leaves `SplitGadget` unchanged and supplies an executable
ordering for the edge list. -/

namespace UniqueGamesTheorem.Reduction.ActualSource

open scoped BigOperators

namespace NoiseEnumeration

variable {s d : Nat} {g : SplitGadget s d}

noncomputable def ofFintype (g : SplitGadget s d) : NoiseEnumeration g where
  indices := Finset.univ.toList
  nodup := Finset.nodup_toList _
  complete i := by simp

end NoiseEnumeration
end UniqueGamesTheorem.Reduction.ActualSource

end

section

/-! Finite noise tables for the executable outer reduction. Positions, including
positions containing equal vectors, remain distinct sample outcomes. -/

namespace UniqueGamesTheorem.Integration.NoiseTables

open BinaryLinear UniqueGamesTheorem.Reduction.ActualSource

variable {s d : Nat}

namespace Table

/-- The inverse equivalence is used only to prove the probability identity;
the forward noise lookup is ordinary finite-list indexing. -/
noncomputable def positionEquiv (g : SplitGadget s d) (en : NoiseEnumeration g) :
    Fin (ofEnumeration g en).vectors.length ≃ g.NoiseIndex := by
  classical
  exact (finCongr (ofEnumeration_length g en)).trans
    (en.nodup.getEquivOfForallMemList en.indices en.complete)

end Table
end UniqueGamesTheorem.Integration.NoiseTables

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

def equalityAcceptance {X Y E : Type*} [Fintype E]
    (left right : E → X) (f : X → Y) : ℝ :=
  uniformMass fun e => f (left e) = f (right e)

end
end UniqueGamesTheorem.Inverse.RowErasure

end

section

namespace UniqueGamesTheorem.Inverse.RowErasure

open scoped BigOperators

noncomputable section

variable {X Y A S D : Type*}

def SliceFamily.erasedUnion (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) : X → Prop :=
  goodUnion (F.goodAt f α)

/-- Only randomized entries count; an unchanged entry contributes zero, even
when its old label already matches the target. -/
def SliceFamily.randomizedAgreement (F : SliceFamily X Y A S D)
    (B : X → Prop) (replacement : X → Y) (d : D) : ℝ :=
  (F.points d).expect fun x => indicator (B x ∧ replacement x = F.target d x)

end
end UniqueGamesTheorem.Inverse.RowErasure

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_RowErasureTail
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.RowErasure

open scoped BigOperators Classical

noncomputable section

def randomizedMatches {X Y : Type*} (s : Finset X) (B : X → Prop)
    (target replacement : X → Y) : ℝ :=
  ∑ x ∈ s, indicator (B x ∧ replacement x = target x)

end
end UniqueGamesTheorem.Inverse.RowErasure

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSFoundationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.KMS

noncomputable section
open scoped BigOperators Classical

instance vertexFinite (n ell : ℕ) : Finite (Vertex n ell) := by
  let : Finite (Submodule F2 (Ambient n)) :=
    Finite.of_injective (fun L : Submodule F2 (Ambient n) => (L : Set (Ambient n)))
      SetLike.coe_injective
  exact inferInstanceAs (Finite {L : Submodule F2 (Ambient n) //
    Module.finrank F2 L = ell})

instance vertexFintype (n ell : ℕ) : Fintype (Vertex n ell) := Fintype.ofFinite _

def neighbors {n ell : ℕ} (L : Vertex n ell) : Finset (Vertex n ell) :=
  Finset.univ.filter (Adjacent L)

/-- Uniform start in `S`, followed by a uniform Grassmann neighbor. -/
def retention {n ell : ℕ} (S : Finset (Vertex n ell)) : ℝ :=
  (∑ L ∈ S, relativeDensity S (neighbors L)) / S.card

/-- The actual interval `A ≤ L ≤ B` among the `ell`-dimensional vertices. -/
def interval {n ell : ℕ} (A B : Submodule F2 (Ambient n)) :
    Finset (Vertex n ell) :=
  Finset.univ.filter fun L => A ≤ L.val ∧ L.val ≤ B

/-- The parameter order needed from KMS, including a nonempty dense interval.
The parameters `r` and `alpha` must be fixed before `ell`, and the ambient threshold may then depend
on `ell`. A bound with `alpha = 2^(-ell)` does not meet this interface. -/
def ExpansionPrinciple : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
      ∃ r : ℕ, 1 ≤ r ∧ ∃ ell₀ : ℕ, ∀ ell : ℕ, ell₀ ≤ ell →
        ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          ∀ S : Finset (Vertex n ell), S.Nonempty → ζ ≤ retention S →
            ∃ A B : Submodule F2 (Ambient n),
              A ≤ B ∧ Module.finrank F2 A + (n - Module.finrank F2 B) ≤ r ∧
                (S ∩ interval A B).Nonempty ∧ α ≤ relativeDensity S (interval A B)

end
end UniqueGamesTheorem.Inverse.KMS

end

section

/-!
# Restricted densities in the ordered-basis lift

The prefix vectors are arbitrary: they may be dependent, and they need not lie
in the subspace from which the remaining vectors are sampled. The relevant
Grassmann interval has lower endpoint `span Q` and upper endpoint `span Q ⊔ W`.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparisonPseudorandom

noncomputable section
open scoped BigOperators Classical
open KMS

variable {n q t : ℕ}

def prefixSpan (Q : Fin q → Ambient n) : Submodule F2 (Ambient n) :=
  Submodule.span F2 (Set.range Q)

def joinedTuple (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (z : Fin t → W) : (Fin q ⊕ Fin t) → Ambient n :=
  Sum.elim Q (fun i => (z i : Ambient n))

abbrev IndependentCompletion (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) :=
  {z : Fin t → W // LinearIndependent F2 (joinedTuple Q W z)}

def completionVertex (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (z : IndependentCompletion (t := t) Q W) : Vertex n (q + t) :=
  ⟨Submodule.span F2 (Set.range (joinedTuple Q W z.val)), by
    simpa using finrank_span_eq_card z.property⟩

theorem prefix_le_completion (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (z : IndependentCompletion (t := t) Q W) :
    prefixSpan Q ≤ (completionVertex Q W z).val := by
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨Sum.inl i, rfl⟩

theorem completion_le_sup (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (z : IndependentCompletion (t := t) Q W) :
    (completionVertex Q W z).val ≤ prefixSpan Q ⊔ W := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  cases i with
  | inl i =>
      exact (le_sup_left : prefixSpan Q ≤ prefixSpan Q ⊔ W)
        (Submodule.subset_span ⟨i, rfl⟩)
  | inr i =>
      exact (le_sup_right : W ≤ prefixSpan Q ⊔ W) (z.val i).property

theorem completion_mem_interval (Q : Fin q → Ambient n)
    (W : Submodule F2 (Ambient n)) (z : IndependentCompletion (t := t) Q W) :
    completionVertex Q W z ∈ interval (prefixSpan Q) (prefixSpan Q ⊔ W) := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    prefix_le_completion Q W z, completion_le_sup Q W z⟩

def GrassmannPseudorandom {ell : ℕ} (S : Finset (Vertex n ell))
    (r : ℕ) (ε : ℝ) : Prop :=
  ∀ A B : Submodule F2 (Ambient n), A ≤ B →
    Module.finrank F2 A + (n - Module.finrank F2 B) ≤ r →
      relativeDensity S (interval A B) ≤ ε

def completionEvent (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) (z : Fin t → W) : Prop :=
  ∃ h : LinearIndependent F2 (joinedTuple Q W z), completionVertex Q W ⟨z, h⟩ ∈ S

/-- The denominator counts *all* remaining tuples drawn uniformly from W.
Dependent completions are rejected, without conditioning away their mass. -/
def restrictedLiftDensity (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) : ℝ :=
  (Nat.card {z : Fin t → W // completionEvent S Q W z} : ℝ) /
    Nat.card (Fin t → W)

def TuplePseudorandom {ell : ℕ} (S : Finset (Vertex n ell))
    (r : ℕ) (ε : ℝ) : Prop :=
  ∀ q t : ℕ, ∀ h : q + t = ell, ∀ Q : Fin q → Ambient n,
    ∀ W : Submodule F2 (Ambient n), q + (n - Module.finrank F2 W) ≤ r →
      restrictedLiftDensity (h.symm ▸ S) Q W ≤ ε

abbrev IntervalVertex (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) :=
  ↥(interval (ell := q + t) (prefixSpan Q) (prefixSpan Q ⊔ W))

def completionIntervalVertex (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (z : IndependentCompletion (t := t) Q W) : IntervalVertex (t := t) Q W :=
  ⟨completionVertex Q W z, completion_mem_interval Q W z⟩

def completionFiberEquiv (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (L : IntervalVertex (t := t) Q W) :
    {z : IndependentCompletion (t := t) Q W // completionIntervalVertex Q W z = L} ≃
      RestrictedCompletion (t := t) Q W L.val.val where
  toFun z := ⟨z.val.val, z.val.property,
    congrArg (fun M => M.val.val) z.property⟩
  invFun z := ⟨⟨z.val, z.property.1⟩, Subtype.ext (Subtype.ext z.property.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

def completionEventEquiv (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) :
    {z : Fin t → W // completionEvent S Q W z} ≃
      {z : IndependentCompletion (t := t) Q W // completionVertex Q W z ∈ S} where
  toFun z := ⟨⟨z.val, z.property.choose⟩, z.property.choose_spec⟩
  invFun z := ⟨z.val.val, z.val.property, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def intervalEventEquiv (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) :
    {L : IntervalVertex (t := t) Q W // L.val ∈ S} ≃
      ↥(S ∩ interval (prefixSpan Q) (prefixSpan Q ⊔ W)) where
  toFun L := ⟨L.val.val, Finset.mem_inter.mpr ⟨L.property, L.val.property⟩⟩
  invFun L := ⟨⟨L.val, (Finset.mem_inter.mp L.property).2⟩,
    (Finset.mem_inter.mp L.property).1⟩
  left_inv _ := rfl
  right_inv _ := rfl

end
end UniqueGamesTheorem.Inverse.KMSBasisComparisonPseudorandom

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

/-!
The full Grassmann degree, by choosing the intersection hyperplane and a
different one-dimensional extension. No graph regularity is assumed.
-/

namespace UniqueGamesTheorem.Inverse.MatrixChart

open Module

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- Each neighbor has a unique intersection hyperplane and extension. -/
noncomputable def neighborsEquivExtensionData [FiniteDimensional K E]
    (L : Submodule K E) : GrassmannNeighbors L ≃ NeighborExtensionData L where
  toFun W :=
    ⟨⟨L ⊓ W.val, inf_le_left, W.property.2⟩,
      ⟨⟨W.val, inf_le_right, W.property.1.trans W.property.2.symm⟩, by
        intro heq
        have h := W.property.2
        rw [heq, inf_idem] at h
        omega⟩⟩
  invFun d := ⟨d.2.val.val, by
    have hI := inf_eq_base_of_distinct_extensions d.1.val L d.2.val.val
      d.1.property.1 d.2.val.property.1 d.1.property.2.symm
      d.2.val.property.2 d.2.property
    exact ⟨d.2.val.property.2.trans d.1.property.2,
      by rw [hI]; exact d.1.property.2⟩⟩
  left_inv W := by rfl
  right_inv d := by
    rcases d with ⟨⟨H, hHL, hH⟩, ⟨⟨W, hHW, hW⟩, hWL⟩⟩
    have hI := inf_eq_base_of_distinct_extensions H L W hHL hHW hH.symm hW hWL
    cases hI
    rfl

end UniqueGamesTheorem.Inverse.MatrixChart

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_MatrixChartIntervalsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

theorem add_image_not_mem_range (X : E →ₗ[ZMod 2] F)
    {y : F} (hy : y ∉ X.range) (z : E) : y + X z ∉ X.range := by
  intro h
  exact hy (by simpa using X.range.sub_mem h (X.mem_range_self z))

/-- Kernel translations of the perturbation vector preserve its image. -/
theorem range_update_add_kernel (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) (y : F) (z : a.ker) :
    (X + a.smulRight (y + X z)).range = (X + a.smulRight y).range := by
  have hz : a z = 0 := z.property
  have hforward (x : E) :
      (X + a.smulRight (y + X z)) x =
        (X + a.smulRight y) (x + a x • z) := by
    simp [hz, smul_add]
    abel
  have hbackward (x : E) :
      (X + a.smulRight y) x =
        (X + a.smulRight (y + X z)) (x - a x • z) := by
    simp [hz, smul_add]
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨x + a x • z, (hforward x).symm⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨x - a x • z, (hbackward x).symm⟩

/-- The affine parametrization of a fixed-functional image fiber. -/
def fixedFunctionalFiberMap (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    a.ker → FixedFunctionalNeighborFiber X a y₀ :=
  fun z => ⟨y₀ + X z, add_image_not_mem_range X hy₀ z,
    range_update_add_kernel X a y₀ z⟩

theorem fixedFunctionalFiberMap_injective (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) (a : E →ₗ[ZMod 2] ZMod 2)
    {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    Function.Injective (fixedFunctionalFiberMap X a hy₀) := by
  intro z w h
  apply Subtype.ext
  apply hX
  exact add_left_cancel (congrArg Subtype.val h)

theorem fixedFunctionalFiberMap_surjective (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) (ha : a ≠ 0)
    {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    Function.Surjective (fixedFunctionalFiberMap X a hy₀) := by
  intro y
  obtain ⟨x, hx⟩ := a.surjective ha 1
  have hmem : X x + y.val ∈ (X + a.smulRight y₀).range := by
    exact y.property.2.le ⟨x, by simp [hx]⟩
  obtain ⟨t, ht⟩ := hmem
  have hbinary : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hat : a t = 1 := by
    rcases hbinary (a t) with hat | hat
    · have he : X t = X x + y.val := by simpa [hat] using ht
      have hy : y.val = X (t - x) := by
        rw [map_sub, he]
        abel
      exact False.elim (y.property.1 ⟨t - x, hy.symm⟩)
    · exact hat
  have hz : t - x ∈ a.ker := by
    change a (t - x) = 0
    simp [hat, hx]
  refine ⟨⟨t - x, hz⟩, ?_⟩
  apply Subtype.ext
  change y₀ + X (t - x) = y.val
  have he : X t + y₀ = X x + y.val := by simpa [hat] using ht
  calc
    y₀ + X (t - x) = (X t + y₀) - X x := by rw [map_sub]; abel
    _ = y.val := by rw [he]; abel

/-- Exact constant-multiplicity fiber over an updated subspace. -/
def fixedFunctionalNeighborFiberEquiv (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) (a : E →ₗ[ZMod 2] ZMod 2)
    (ha : a ≠ 0) {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    a.ker ≃ FixedFunctionalNeighborFiber X a y₀ :=
  Equiv.ofBijective (fixedFunctionalFiberMap X a hy₀)
    ⟨fixedFunctionalFiberMap_injective X hX a hy₀,
      fixedFunctionalFiberMap_surjective X a ha hy₀⟩

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

abbrev OutsideNeighborPairFiber (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) (y : F) :=
  {p : OutsideNeighborFactors X //
    (rankOneUpdate X p.1.val p.2.val).range = (rankOneUpdate X a y).range}

/-- The common-parent intersection recovers the binary functional uniquely. -/
theorem functional_eq_of_update_range_eq (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) {a b : E →ₗ[ZMod 2] ZMod 2}
    {y z : F} (hy : y ∉ X.range) (hz : z ∉ X.range)
    (h : (rankOneUpdate X a y).range = (rankOneUpdate X b z).range) :
    a = b := by
  apply binary_functional_eq_of_map_ker_eq X hX
  rw [← range_inf_rankOneUpdate X a hy, ← range_inf_rankOneUpdate X b hz, h]

def fixedToPairFiber (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) (ha : a ≠ 0) (y₀ : F) :
    FixedFunctionalNeighborFiber X a y₀ → OutsideNeighborPairFiber X a y₀ :=
  fun y => ⟨(⟨a, ha⟩, ⟨y.val, y.property.1⟩), y.property.2⟩

theorem fixedToPairFiber_injective (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) (ha : a ≠ 0) (y₀ : F) :
    Function.Injective (fixedToPairFiber X a ha y₀) := by
  intro y z h
  apply Subtype.ext
  exact congrArg (fun p => p.val.2.val) h

theorem fixedToPairFiber_surjective (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) (a : E →ₗ[ZMod 2] ZMod 2)
    (ha : a ≠ 0) {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    Function.Surjective (fixedToPairFiber X a ha y₀) := by
  intro p
  have haeq : p.val.1.val = a :=
    functional_eq_of_update_range_eq X hX p.val.2.property hy₀ p.property
  have he : (X + a.smulRight p.val.2.val).range =
      (X + a.smulRight y₀).range := by
    simpa only [rankOneUpdate, haeq] using p.property
  refine ⟨⟨p.val.2.val, p.val.2.property, he⟩, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext haeq.symm
  · rfl

/-- Every pair in a fixed neighbor fiber has the same functional. -/
def fixedFunctionalEquivPairFiber (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) (a : E →ₗ[ZMod 2] ZMod 2)
    (ha : a ≠ 0) {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    FixedFunctionalNeighborFiber X a y₀ ≃ OutsideNeighborPairFiber X a y₀ :=
  Equiv.ofBijective (fixedToPairFiber X a ha y₀)
    ⟨fixedToPairFiber_injective X a ha y₀,
      fixedToPairFiber_surjective X hX a ha hy₀⟩

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

section

/-! Exact full-neighbor count in the KMS vertex representation. -/

namespace UniqueGamesTheorem.Inverse.MatrixChart

open Module

/-- Ambient linear equivalence transports the actual neighbor subspaces. -/
noncomputable def grassmannNeighborsMapEquiv
    {E F : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [AddCommGroup F] [Module (ZMod 2) F]
    (e : E ≃ₗ[ZMod 2] F) (L : Submodule (ZMod 2) E) :
    GrassmannNeighbors L ≃ GrassmannNeighbors (L.map e.toLinearMap) := by
  refine Equiv.subtypeEquiv (Submodule.orderIsoMapComap e).toEquiv ?_
  intro W
  change (_ ∧ _) ↔
    (finrank (ZMod 2) (W.map e.toLinearMap) =
        finrank (ZMod 2) (L.map e.toLinearMap) ∧
      finrank (ZMod 2) (L.map e.toLinearMap ⊓ W.map e.toLinearMap :
        Submodule (ZMod 2) F) + 1 =
        finrank (ZMod 2) (L.map e.toLinearMap))
  rw [← Submodule.map_inf e.toLinearMap e.injective]
  simp only [LinearEquiv.finrank_map_eq]

/-- Extrinsic submodule neighbors and the finite KMS neighbor predicate agree. -/
def kmsNeighborsEquiv {n ell : Nat} (L : KMS.Vertex n ell) :
    GrassmannNeighbors L.val ≃ {W : KMS.Vertex n ell // KMS.Adjacent L W} where
  toFun W := ⟨⟨W.val, W.property.1.trans L.property⟩, by
    refine ⟨?_, ?_⟩
    · intro h
      have hv := congrArg Subtype.val h
      have hd := W.property.2
      rw [← hv, inf_idem] at hd
      omega
    · exact W.property.2.trans L.property⟩
  invFun W := ⟨W.val.val, W.val.property.trans L.property.symm,
    W.property.2.trans L.property.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

end UniqueGamesTheorem.Inverse.MatrixChart

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSBasisComparisonLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# The ordered-basis lift of a Grassmann set

The ambient sample space contains every linear map, including singular maps.
The lift accepts exactly maps whose range is one of the specified
`ell`-dimensional subspaces. Thus dependence is rejected, rather than silently
conditioning the ambient uniform distribution on independence.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

noncomputable section
open scoped Classical

abbrev BasisMap (n ell : ℕ) := KMS.Ambient ell →ₗ[KMS.F2] KMS.Ambient n

instance basisMapFinite (n ell : ℕ) : Finite (BasisMap n ell) :=
  Finite.of_injective (fun X : BasisMap n ell => (X : KMS.Ambient ell → KMS.Ambient n))
    DFunLike.coe_injective

instance basisMapFintype (n ell : ℕ) : Fintype (BasisMap n ell) := Fintype.ofFinite _

/-- Membership in the lift, expressed by the actual linear-map range. -/
def InLift {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) (X : BasisMap n ell) : Prop :=
  ∃ L ∈ S, LinearMap.range X = L.val

/-- The lifted finite set in the whole map space. -/
def lift {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) : Finset (BasisMap n ell) :=
  Finset.univ.filter (InLift S)

@[simp] theorem mem_lift {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) : X ∈ lift S ↔ InLift S X := by
  simp [lift]

/-- Real Boolean indicator, in the orientation used by the matrix Fourier transform. -/
def liftedIndicator {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) : ℝ := if InLift S X then 1 else 0

/-- A map accepted by the lift has full column rank. -/
theorem injective_of_inLift {n ell : ℕ} {S : Finset (KMS.Vertex n ell)}
    {X : BasisMap n ell} (h : InLift S X) : Function.Injective X := by
  obtain ⟨L, _, hL⟩ := h
  have hr : Module.finrank KMS.F2 (LinearMap.range X) = ell := by
    rw [hL]
    exact L.property
  have hd := X.finrank_range_add_finrank_ker
  have he : Module.finrank KMS.F2 (KMS.Ambient ell) = ell := by
    simp [KMS.Ambient]
  have hk : Module.finrank KMS.F2 (LinearMap.ker X) = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)

/-- The actual Grassmann vertex represented by an injective map. -/
def rangeVertex {n ell : ℕ} (X : BasisMap n ell) (hX : Function.Injective X) :
    KMS.Vertex n ell :=
  ⟨LinearMap.range X, by
    rw [LinearMap.finrank_range_of_inj hX]
    simp [KMS.Ambient]⟩

theorem inLift_iff_rangeVertex_mem {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) (hX : Function.Injective X) :
    InLift S X ↔ rangeVertex X hX ∈ S := by
  constructor
  · rintro ⟨L, hL, hXL⟩
    have he : rangeVertex X hX = L := Subtype.ext hXL
    simpa only [he] using hL
  · intro h
    exact ⟨rangeVertex X hX, h, rfl⟩

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

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

/-- Every Grassmann vertex admits an ordered basis of the prescribed domain. -/
def vertexBasis {n ell : ℕ} (L : KMS.Vertex n ell) :
    KMS.Ambient ell ≃ₗ[KMS.F2] L.val :=
  LinearEquiv.ofFinrankEq _ _ (by simpa [KMS.Ambient] using L.property.symm)

instance basisAutomorphismFinite (ell : ℕ) :
    Finite (KMS.Ambient ell ≃ₗ[KMS.F2] KMS.Ambient ell) :=
  Finite.of_injective
    (fun e : KMS.Ambient ell ≃ₗ[KMS.F2] KMS.Ambient ell =>
      (e : KMS.Ambient ell → KMS.Ambient ell)) DFunLike.coe_injective

instance basisAutomorphismFintype (ell : ℕ) :
    Fintype (KMS.Ambient ell ≃ₗ[KMS.F2] KMS.Ambient ell) := Fintype.ofFinite _

/-- The range quotient restricted to the lifted event itself. -/
def liftRange {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : lift S) : S :=
  ⟨rangeVertex X.val (injective_of_inLift ((mem_lift S X.val).mp X.property)),
    (inLift_iff_rangeVertex_mem S X.val _).mp ((mem_lift S X.val).mp X.property)⟩

def liftRangeFiberEquiv {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) (L : S) :
    {X : lift S // liftRange S X = L} ≃
      RangeFiber (E := KMS.Ambient ell) L.val.val where
  toFun X := ⟨X.val.val, injective_of_inLift ((mem_lift S X.val.val).mp X.val.property),
    congrArg (fun Z : S => Z.val.val) X.property⟩
  invFun X := ⟨⟨X.val, (mem_lift S X.val).mpr ⟨L.val, L.property, X.property.2⟩⟩,
    Subtype.ext (Subtype.ext X.property.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

def liftRangeFiberAut {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) (L : S) :
    {X : lift S // liftRange S X = L} ≃
      (KMS.Ambient ell ≃ₗ[KMS.F2] KMS.Ambient ell) :=
  (liftRangeFiberEquiv S L).trans (rangeFiberEquivAut (vertexBasis L.val))

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

section

/-!
The good event for an ordered-basis rank-one update is that its functional
is nonzero and its direction lies outside the starting range. Its exact
finite cardinality gives the exceptional-mass bound without conditioning
either factor of the original uniform experiment.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

noncomputable section
open scoped Classical

abbrev Functional (ell : ℕ) := KMS.Ambient ell →ₗ[KMS.F2] KMS.F2

instance functionalFinite (ell : ℕ) : Finite (Functional ell) :=
  Finite.of_injective (fun a : Functional ell => (a : KMS.Ambient ell → KMS.F2))
    DFunLike.coe_injective

instance functionalFintype (ell : ℕ) : Fintype (Functional ell) := Fintype.ofFinite _

/-- Actual good pairs in the unconditioned product sample space. -/
def goodParameters {n ell : ℕ} (X : BasisMap n ell) :
    Finset (Functional ell × KMS.Ambient n) :=
  (Finset.univ.filter (fun a : Functional ell => a ≠ 0)) ×ˢ
    (Finset.univ.filter (fun y : KMS.Ambient n => y ∉ X.range))

@[simp] theorem mem_goodParameters {n ell : ℕ} (X : BasisMap n ell)
    (p : Functional ell × KMS.Ambient n) :
    p ∈ goodParameters X ↔ p.1 ≠ 0 ∧ p.2 ∉ X.range := by
  simp [goodParameters]

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

section

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

noncomputable section
open scoped BigOperators Classical

variable {E F : Type*}
  [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]
  [FiniteDimensional (ZMod 2) E] [FiniteDimensional (ZMod 2) F]

/-- The full-neighbor sampler on its exact good-event factor space. -/
def outsideNeighborSample (X : E →ₗ[ZMod 2] F) (hX : Function.Injective X)
    (p : OutsideNeighborFactors X) : MatrixChart.GrassmannNeighbors X.range :=
  rankOneUpdateNeighbor X hX p.1.val p.1.property p.2.val p.2.property

omit [FiniteDimensional (ZMod 2) F] in
@[simp] theorem outsideNeighborSample_val (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) (p : OutsideNeighborFactors X) :
    (outsideNeighborSample X hX p).val =
      (rankOneUpdate X p.1.val p.2.val).range := rfl

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSBasisComparisonPseudorandomTupleMapLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The restricted tuple law is the actual linear-map lift law in coordinates,
with all singular tuples still present in the uniform denominator. -/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparisonPseudorandom

noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison

variable {n q t : ℕ}

def tupleBasis (q t : ℕ) : Module.Basis (Fin q ⊕ Fin t) F2 (Ambient (q + t)) :=
  (Pi.basisFun F2 (Fin (q + t))).reindex finSumFinEquiv.symm

def tupleMap (x : (Fin q ⊕ Fin t) → Ambient n) : BasisMap n (q + t) :=
  (tupleBasis q t).constr F2 x

@[simp] theorem tupleMap_basis (x : (Fin q ⊕ Fin t) → Ambient n)
    (i : Fin q ⊕ Fin t) : tupleMap x (tupleBasis q t i) = x i :=
  (tupleBasis q t).constr_basis F2 x i

end
end UniqueGamesTheorem.Inverse.KMSBasisComparisonPseudorandom

end

section

/-!
The KMS restricted-tuple bound in any adapted basis, followed by an exact
uniform affine translation of the free coordinates. No generic rank-level
inequality is used: this is a change of coordinates for the actual lift.
-/

namespace UniqueGamesTheorem.Inverse.KMSAffineRestriction
noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom

variable {n ell q t r : ℕ} {ε : ℝ}

/-- Coordinates of a uniform linear map, translated by a fixed linear map,
are still exactly uniform. This also covers zero-dimensional free domains. -/
def affineCoordinates {E W : Type*}
    [AddCommGroup E] [Module F2 E] [AddCommGroup W] [Module F2 W]
    (b : Module.Basis (Fin t) F2 E) (T : E →ₗ[F2] W) :
    (E →ₗ[F2] W) ≃ (Fin t → W) :=
  ((b.constr F2).toEquiv).symm.trans (Equiv.addLeft (fun i => T (b i)))

@[simp] theorem affineCoordinates_apply {E W : Type*}
    [AddCommGroup E] [Module F2 E] [AddCommGroup W] [Module F2 W]
    (b : Module.Basis (Fin t) F2 E) (T H : E →ₗ[F2] W) (i : Fin t) :
    affineCoordinates b T H i = T (b i) + H (b i) := rfl

end
end UniqueGamesTheorem.Inverse.KMSAffineRestriction

end

section

/-!
Grassmann interval pseudorandomness controls actual arbitrary affine matrix
restrictions, at twice the restriction order. The proof chooses a bounded
prefix containing the vanishing subspace and all nonhomogeneous directions,
splits the exact quotient-map parameter law, and applies the tuple estimate.
-/

namespace UniqueGamesTheorem.Inverse.KMSAffineRestriction
noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom
open UniqueGamesTheorem.Fourier.MatrixRestrictions

variable {n ell q t : ℕ}

/-- Basis obtained from a genuine complementary domain decomposition. -/
def complementBasis (U E0 : Submodule F2 (Ambient ell)) (hc : IsCompl U E0)
    (bU : Module.Basis (Fin q) F2 U) (b0 : Module.Basis (Fin t) F2 E0) :
    Module.Basis (Fin q ⊕ Fin t) F2 (Ambient ell) :=
  (bU.prod b0).map (Submodule.prodEquivOfIsCompl U E0 hc)

@[simp] theorem complementBasis_inl (U E0 : Submodule F2 (Ambient ell))
    (hc : IsCompl U E0) (bU : Module.Basis (Fin q) F2 U)
    (b0 : Module.Basis (Fin t) F2 E0) (i : Fin q) :
    complementBasis U E0 hc bU b0 (Sum.inl i) = (bU i : Ambient ell) := by
  simp [complementBasis, Module.Basis.prod_apply]

@[simp] theorem complementBasis_inr (U E0 : Submodule F2 (Ambient ell))
    (hc : IsCompl U E0) (bU : Module.Basis (Fin q) F2 U)
    (b0 : Module.Basis (Fin t) F2 E0) (i : Fin t) :
    complementBasis U E0 hc bU b0 (Sum.inr i) = (b0 i : Ambient ell) := by
  simp [complementBasis, Module.Basis.prod_apply]

/-- The affine center restricted to directions whose images already lie in W. -/
def freeCenter (E0 : Submodule F2 (Ambient ell)) (W : Submodule F2 (Ambient n))
    (T : BasisMap n ell) (hE0 : E0 ≤ LinearMap.ker (W.mkQ.comp T)) : E0 →ₗ[F2] W :=
  (T.comp E0.subtype).codRestrict W fun x =>
    (Submodule.Quotient.mk_eq_zero W).mp (hE0 x.property)

@[simp] theorem freeCenter_coe (E0 : Submodule F2 (Ambient ell))
    (W : Submodule F2 (Ambient n)) (T : BasisMap n ell)
    (hE0 : E0 ≤ LinearMap.ker (W.mkQ.comp T)) (x : E0) :
    (freeCenter E0 W T hE0 x : Ambient n) = T x := rfl

end
end UniqueGamesTheorem.Inverse.KMSAffineRestriction

end

section

/-!
# Ordered-basis retention versus Grassmann retention

This is the sampling comparison in KMS Lemma 2.7. The original experiment
uses all functionals and all directions, including zero. Its good event
induces exactly the full Grassmann-neighbor law; all other outcomes contribute
at most their explicit probability mass. Initial bases push forward uniformly
to the original Grassmann set.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

noncomputable section
open scoped BigOperators Classical

/-- The complete rank-one update experiment at a specified starting map. -/
def fullStepRetention {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) : ℝ :=
  𝔼 p : Functional ell × KMS.Ambient n,
    liftedIndicator S (rankOneUpdate X p.1 p.2)

/-- Start uniformly in the lifted set, then run the unconditioned update. -/
def liftRetention {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) : ℝ :=
  𝔼 X : lift S, fullStepRetention S X.val

/-- Equivalence of the two explicit presentations of the good sampling event. -/
def goodParametersEquiv {n ell : ℕ} (X : BasisMap n ell) :
    goodParameters X ≃ OutsideNeighborFactors X where
  toFun p := ⟨⟨p.val.1, ((mem_goodParameters X p.val).mp p.property).1⟩,
    ⟨p.val.2, ((mem_goodParameters X p.val).mp p.property).2⟩⟩
  invFun p := ⟨(p.1.val, p.2.val),
    (mem_goodParameters X _).mpr ⟨p.1.property, p.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The indicator's density in the full linear-map space. -/
def liftDensity {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) : ℝ :=
  𝔼 X : BasisMap n ell, liftedIndicator S X

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

section

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

noncomputable section
open scoped Classical
open KMSBasisComparisonPseudorandom

/-- The precise analytic obligation at the ordered-basis lift. Its constants
are fixed before the tuple length, which is fixed before the ambient size. -/
def LiftExpansionPrinciple : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∃ r ell₀ : ℕ, ∀ ell : ℕ, ell₀ ≤ ell →
        ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          ∀ S : Finset (KMS.Vertex n ell), S.Nonempty →
            TuplePseudorandom S r ε → liftRetention S ≤ ζ

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

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

/-!
The selected column event under the actual uniform matrix and row-map samples.
The witness is fixed by visible row advice before testing the hidden matrix.
Fiber sizes are retained explicitly; no uniformity of row values is assumed.
The final averaging lemmas also allow arbitrary nonnegative context weights.
-/

namespace UniqueGamesTheorem.Inverse.RowErasure

noncomputable section
open scoped BigOperators

variable {X Y A S D : Type*}

def SliceFamily.selectedPoints (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) : Finset X :=
  match F.selectedDescription f α a s with
  | none => ∅
  | some d => F.points d

def SliceFamily.selectedHit (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) (x : X) : Prop :=
  ∃ d, F.selectedDescription f α a s = some d ∧ f x = F.target d x

end
end UniqueGamesTheorem.Inverse.RowErasure

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_Clone100Triples
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
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

instance instNonemptyGoodTriple : Nonempty GoodTriple :=
  ⟨⟨(0, 1, 2), by decide⟩⟩

end UniqueGamesTheorem.Outer.Clone100Triples

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_FoldedEquationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
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

def storedAssignment {i₀ : I} {j₀ : J}
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool) :
    Address i₀ j₀ → Bool := Sum.elim tableA tableB

theorem correction_eq (π : J → I) (i₀ : I) (j₀ : J)
    (f : Cube I) (g μ : Cube J) :
    (f i₀ ^^ g j₀ ^^ thirdQuery π f g μ j₀) = rhsCorrection π i₀ j₀ f μ := by
  change (f i₀ ^^ g j₀ ^^ (g j₀ ^^ (f (π j₀) ^^ μ j₀))) =
    (f i₀ ^^ f (π j₀) ^^ μ j₀)
  cases f i₀ <;> cases g j₀ <;> cases f (π j₀) <;> cases μ j₀ <;> rfl

theorem restrict_thirdQuery (valid : J → Bool) (π : J → I)
    (f : Cube I) (g μ : Cube J) :
    restrictQuery valid (thirdQuery π f g μ) =
      thirdQuery (fun j : {j : J // valid j = true} => π j.val) f
        (restrictQuery valid g) (restrictQuery valid μ) := rfl

end UniqueGamesTheorem.Foundations.Hastad.FoldedEquation

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_AssignmentTester
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

theorem disagree_eq (a b : Bool) :
    disagree a b = (1 - bitSign a * bitSign b) / 2 := by
  cases a <;> cases b <;> norm_num [disagree, bitSign]

def parity (s f : Cube A) : Bool :=
  decide (Odd ((Finset.univ.filter fun a => s a && f a = true).card))

theorem bitSign_parity (s f : Cube A) : bitSign (parity s f) = walsh s f := by
  have hw : walsh s f = (-1 : ℝ) ^
      (Finset.univ.filter fun a => s a && f a = true).card := by
    simp [walsh, bitSign, Finset.prod_ite]
  rw [hw]
  simpa [parity, bitSign] using
    (sign_power_parity true (Finset.univ.filter fun a => s a && f a = true).card).symm

theorem bitSign_injective : Function.Injective bitSign := by
  intro a b h
  cases a <;> cases b <;> simp_all [bitSign] <;> linarith

theorem parity_xor (s f g : Cube A) :
    parity s (cubeXor f g) = (parity s f ^^ parity s g) := by
  apply bitSign_injective
  rw [bitSign_parity, bitSign_xor, bitSign_parity, bitSign_parity, walsh_xor]

omit [Fintype A] [DecidableEq A] in
theorem cubeXor_comm (f g : Cube A) : cubeXor f g = cubeXor g f := by
  funext a
  simp [cubeXor, Bool.xor_comm]

theorem expect_cubeXor (F : Cube A → ℝ) (g : Cube A) :
    (𝔼 f, F (cubeXor f g)) = 𝔼 f, F f := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  congr 1
  refine Finset.sum_bij (fun f _ => cubeXor f g) ?_ ?_ ?_ ?_
  · intro f _
    exact Finset.mem_univ _
  · intro f _ h _ heq
    have hh := congrArg (fun x => cubeXor x g) heq
    simpa only [cubeXor_right_twice] using hh
  · intro f _
    exact ⟨cubeXor f g, Finset.mem_univ _, cubeXor_right_twice f g⟩
  · intro f _
    rfl

theorem distance_parity (F : Cube A → Bool) (s : Cube A) :
    distance F (parity s) = (1 - coefficient (fun f => bitSign (F f)) s) / 2 := by
  unfold distance
  simp_rw [disagree_eq, bitSign_parity, div_eq_mul_inv,
    ← Finset.expect_mul, Finset.expect_sub_distrib]
  simp only [Fintype.expect_const]
  rfl

def blrReject (F : Cube A → Bool) : ℝ :=
  𝔼 f, 𝔼 g, disagree (F f ^^ F g) (F (cubeXor f g))

theorem blrReject_nonneg (F : Cube A → Bool) : 0 ≤ blrReject F := by
  apply Finset.expect_nonneg
  intro f _
  apply Finset.expect_nonneg
  intro g _
  exact disagree_nonneg _ _

theorem blr_correlation (F : Cube A → Bool) :
    (𝔼 f, 𝔼 g, bitSign (F f) * bitSign (F g) * bitSign (F (cubeXor f g))) =
      ∑ s, coefficient (fun f => bitSign (F f)) s ^ 3 := by
  simp_rw [mul_assoc, ← Finset.mul_expect]
  conv_lhs =>
    enter [2, f, 2, 2, g, 2, 1]
    rw [cubeXor_comm]
  simp_rw [walsh_autocorrelation, Finset.mul_sum]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have heq (f : Cube A) : bitSign (F f) *
      (coefficient (fun f => bitSign (F f)) s ^ 2 * walsh s f) =
    coefficient (fun f => bitSign (F f)) s ^ 2 * (bitSign (F f) * walsh s f) := by ring
  simp_rw [heq, ← Finset.mul_expect]
  change coefficient (fun f => bitSign (F f)) s ^ 2 *
    coefficient (fun f => bitSign (F f)) s = _
  ring

theorem blrReject_fourier (F : Cube A → Bool) :
    blrReject F = (1 - ∑ s, coefficient (fun f => bitSign (F f)) s ^ 3) / 2 := by
  unfold blrReject
  simp_rw [disagree_eq, bitSign_xor, div_eq_mul_inv,
    ← Finset.expect_mul, Finset.expect_sub_distrib]
  simp only [Fintype.expect_const]
  rw [blr_correlation]

/-- The actual BLR test yields a nearby parity, with no stability theorem
or Fourier-structure hypothesis assumed. -/
theorem blr_near_parity (F : Cube A → Bool) :
    ∃ s : Cube A, distance F (parity s) ≤ blrReject F := by
  classical
  let c := coefficient (fun f => bitSign (F f))
  have hmass : (∑ s, c s ^ 2) = 1 := sign_parseval F
  have hlarge : ∃ s, (∑ t, c t ^ 3) ≤ c s := by
    by_contra hn
    push Not at hn
    have hpos : ∃ s, 0 < c s ^ 2 := by
      by_contra hh
      push Not at hh
      have hz := Finset.sum_nonpos (s := Finset.univ) (fun s _ => hh s)
      linarith
    obtain ⟨s₀, hs₀⟩ := hpos
    have hle (s : Cube A) (_ : s ∈ Finset.univ) :
        c s ^ 3 ≤ (∑ t, c t ^ 3) * c s ^ 2 := by
      have h := mul_le_mul_of_nonneg_right (hn s).le (sq_nonneg (c s))
      nlinarith
    have hlt : c s₀ ^ 3 < (∑ t, c t ^ 3) * c s₀ ^ 2 := by
      have h := mul_lt_mul_of_pos_right (hn s₀) hs₀
      nlinarith
    have hsum := Finset.sum_lt_sum hle ⟨s₀, Finset.mem_univ _, hlt⟩
    rw [← Finset.mul_sum, hmass, mul_one] at hsum
    exact (lt_irrefl _ hsum)
  obtain ⟨s, hs⟩ := hlarge
  refine ⟨s, ?_⟩
  rw [distance_parity, blrReject_fourier]
  dsimp [c] at hs
  linarith

def selfCorrect (F : Cube A → Bool) (x r : Cube A) : Bool :=
  F r ^^ F (cubeXor r x)

theorem parity_selfCorrect (s x r : Cube A) :
    (parity s r ^^ parity s (cubeXor r x)) = parity s x := by
  rw [parity_xor]
  cases parity s r <;> cases parity s x <;> rfl

/-- The two actual oracle queries recover the parity at every requested x. -/
theorem selfCorrect_error (F : Cube A → Bool) (s x : Cube A) :
    (𝔼 r, disagree (selfCorrect F x r) (parity s x)) ≤ 2 * distance F (parity s) := by
  have hle (r : Cube A) :
      disagree (selfCorrect F x r) (parity s x) ≤
      disagree (F r) (parity s r) +
        disagree (F (cubeXor r x)) (parity s (cubeXor r x)) := by
    rw [← parity_selfCorrect s x r]
    exact disagree_xor_le _ _ _ _
  have h := Finset.expect_le_expect (s := Finset.univ) (fun r _ => hle r)
  rw [Finset.expect_add_distrib,
    expect_cubeXor (fun r => disagree (F r) (parity s r)) x] at h
  change _ ≤ distance F (parity s) + distance F (parity s) at h
  linarith

def singleMask (i : A) : Cube A := fun j => decide (j = i)

omit [Fintype A] in
theorem flipAt_eq_xor (i : A) (f : Cube A) : flipAt i f = cubeXor f (singleMask i) := by
  funext j
  by_cases h : j = i <;> simp [flipAt, cubeXor, singleMask, h]

theorem expect_flipAt (F : Cube A → ℝ) (i : A) :
    (𝔼 f, F (flipAt i f)) = 𝔼 f, F f := by
  simp_rw [flipAt_eq_xor]
  exact expect_cubeXor F _

theorem walsh_singleMask (s : Cube A) (i : A) :
    walsh s (singleMask i) = bitSign (s i) := by
  unfold walsh
  rw [Finset.prod_eq_single i]
  · simp [singleMask]
  · intro j _ hj
    simp [singleMask, hj, bitSign]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem parity_singleMask (s : Cube A) (i : A) : parity s (singleMask i) = s i := by
  apply bitSign_injective
  rw [bitSign_parity, walsh_singleMask]

theorem parity_flipAt (s : Cube A) (i : A) (f : Cube A) (hs : s i = true) :
    parity s (flipAt i f) = !(parity s f) := by
  rw [flipAt_eq_xor, parity_xor, parity_singleMask, hs]
  cases parity s f <;> rfl

def andLawFailure (s f g : Cube A) : Bool :=
  parity s (cubeAnd f g) ^^ (parity s f && parity s g)

theorem andLawFailure_flipAt_second (s : Cube A) (i : A) (f g : Cube A)
    (hi : s i = true) :
    andLawFailure s f (flipAt i g) =
      (andLawFailure s f g ^^ (parity s f ^^ f i)) := by
  have hAnd : cubeAnd f (flipAt i g) =
      (if f i then flipAt i (cubeAnd f g) else cubeAnd f g) := by
    funext a
    by_cases ha : a = i
    · subst a
      cases hfi : f i <;> simp [cubeAnd, flipAt, hfi]
    · cases hfi : f i <;> simp [cubeAnd, flipAt, ha]
  have hg := parity_flipAt s i g hi
  have hfg := parity_flipAt s i (cubeAnd f g) hi
  cases hfi : f i <;> cases hf : parity s f <;>
    cases hg₀ : parity s g <;> cases ha : parity s (cubeAnd f g) <;>
    simp [andLawFailure, hAnd, hg, hfg, hfi, hf, hg₀, ha]

/-- Every parity involving two or more distinct coordinates violates Boolean
AND with probability at least one quarter under two independent queries. -/
theorem parity_and_rejection (s : Cube A) (i j : A)
    (hi : s i = true) (hj : s j = true) (hij : i ≠ j) :
    (1 : ℝ) / 4 ≤ 𝔼 f, 𝔼 g, truth (andLawFailure s f g) := by
  have hpoint (f g : Cube A) : (1 : ℝ) ≤
      truth (andLawFailure s f g) + truth (andLawFailure s f (flipAt i g)) +
      truth (andLawFailure s (flipAt j f) g) +
      truth (andLawFailure s (flipAt j f) (flipAt i g)) := by
    rw [andLawFailure_flipAt_second s i f g hi,
      andLawFailure_flipAt_second s i (flipAt j f) g hi]
    have hD : (parity s (flipAt j f) ^^ (flipAt j f) i) =
        !(parity s f ^^ f i) := by
      rw [parity_flipAt s j f hj]
      simp only [flipAt, ite_eq_right hij]
      cases hf : parity s f <;> cases hfi : f i <;> simp
    rw [hD]
    exact four_truth_lower _ _ _
  have havg := Finset.expect_le_expect (s := Finset.univ) (fun f _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun g _ => hpoint f g))
  simp only [Finset.expect_add_distrib, Fintype.expect_const] at havg
  have hinner (f : Cube A) :
      (𝔼 g, truth (andLawFailure s f (flipAt i g))) =
        𝔼 g, truth (andLawFailure s f g) :=
    expect_flipAt (fun g => truth (andLawFailure s f g)) i
  have houter : (𝔼 f, 𝔼 g, truth (andLawFailure s (flipAt j f) g)) =
      𝔼 f, 𝔼 g, truth (andLawFailure s f g) :=
    expect_flipAt (fun f => 𝔼 g, truth (andLawFailure s f g)) j
  simp only [hinner, houter] at havg
  linarith

/-- Six oracle queries, using three independent self-correction masks. -/
def andReject (F : Cube A → Bool) : ℝ :=
  𝔼 f, 𝔼 g, 𝔼 r₀, 𝔼 r₁, 𝔼 r₂,
    disagree (selfCorrect F (cubeAnd f g) r₀)
      (selfCorrect F f r₁ && selfCorrect F g r₂)

def unitReject (F : Cube A → Bool) : ℝ :=
  𝔼 r, disagree (selfCorrect F (fun _ => true) r) true

variable {K : Type*} [Fintype K] [Nonempty K]

/-- One original input query and two proof-oracle queries. -/
def inputReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) : ℝ :=
  𝔼 k, 𝔼 r, disagree (σ k) (selfCorrect F (fun a => label a k) r)

def testerReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) : ℝ :=
  (blrReject F + andReject F + unitReject F + inputReject label σ F) / 4

theorem andReject_nonneg (F : Cube A → Bool) : 0 ≤ andReject F := by
  apply Finset.expect_nonneg
  intro f _
  apply Finset.expect_nonneg
  intro g _
  apply Finset.expect_nonneg
  intro r₀ _
  apply Finset.expect_nonneg
  intro r₁ _
  apply Finset.expect_nonneg
  intro r₂ _
  exact disagree_nonneg _ _

theorem unitReject_nonneg (F : Cube A → Bool) : 0 ≤ unitReject F := by
  apply Finset.expect_nonneg
  intro r _
  exact disagree_nonneg _ _

omit [Nonempty K] in
theorem inputReject_nonneg (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) :
    0 ≤ inputReject label σ F := by
  apply Finset.expect_nonneg
  intro k _
  apply Finset.expect_nonneg
  intro r _
  exact disagree_nonneg _ _

theorem andReject_transfer (F : Cube A → Bool) (s : Cube A) :
    (𝔼 f, 𝔼 g, truth (andLawFailure s f g)) ≤
      andReject F + 6 * distance F (parity s) := by
  have hlocal (f g : Cube A) : truth (andLawFailure s f g) ≤
      (𝔼 r₀, 𝔼 r₁, 𝔼 r₂,
        disagree (selfCorrect F (cubeAnd f g) r₀)
          (selfCorrect F f r₁ && selfCorrect F g r₂)) +
      6 * distance F (parity s) := by
    have hp (r₀ r₁ r₂ : Cube A) := and_disagree_transfer
      (parity s (cubeAnd f g)) (parity s f) (parity s g)
      (selfCorrect F (cubeAnd f g) r₀) (selfCorrect F f r₁) (selfCorrect F g r₂)
    have havg := Finset.expect_le_expect (s := Finset.univ) (fun r₀ _ =>
      Finset.expect_le_expect (s := Finset.univ) (fun r₁ _ =>
        Finset.expect_le_expect (s := Finset.univ) (fun r₂ _ => hp r₀ r₁ r₂)))
    simp only [Finset.expect_add_distrib, Fintype.expect_const] at havg
    have h₀ := selfCorrect_error F s (cubeAnd f g)
    have h₁ := selfCorrect_error F s f
    have h₂ := selfCorrect_error F s g
    rw [andLawFailure, truth_xor]
    linarith
  have h := Finset.expect_le_expect (s := Finset.univ) (fun f _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun g _ => hlocal f g))
  simpa only [Finset.expect_add_distrib, Fintype.expect_const, andReject] using h

theorem parity_zero (f : Cube A) : parity (fun _ => false) f = false := by
  apply bitSign_injective
  rw [bitSign_parity]
  simp [walsh, bitSign]

theorem unitReject_zero_parity (F : Cube A → Bool) :
    1 - 2 * distance F (parity (fun _ => false)) ≤ unitReject F := by
  have herr := selfCorrect_error F (fun _ => false) (fun _ => true)
  simp only [parity_zero] at herr
  have heq : unitReject F +
      (𝔼 r, disagree (selfCorrect F (fun _ => true) r) false) = 1 := by
    unfold unitReject
    rw [← Finset.expect_add_distrib]
    have hp (b : Bool) : disagree b true + disagree b false = 1 := by
      cases b <;> norm_num [disagree]
    simp only [hp, Fintype.expect_const]
  linarith

theorem parity_singleMask_eval (a : A) (f : Cube A) :
    parity (singleMask a) f = f a := by
  apply bitSign_injective
  rw [bitSign_parity, walsh_symm, walsh_singleMask]

theorem inputReject_transfer (label : A → K → Bool) (σ : K → Bool)
    (F : Cube A → Bool) (a : A) :
    distance σ (label a) ≤ inputReject label σ F +
      2 * distance F (parity (singleMask a)) := by
  have hlocal (k : K) : disagree (σ k) (label a k) ≤
      (𝔼 r, disagree (σ k) (selfCorrect F (fun a => label a k) r)) +
        2 * distance F (parity (singleMask a)) := by
    have hp (r : Cube A) := disagree_triangle (σ k)
      (selfCorrect F (fun a => label a k) r) (label a k)
    have havg := Finset.expect_le_expect (s := Finset.univ) (fun r _ => hp r)
    simp only [Fintype.expect_const, Finset.expect_add_distrib] at havg
    have herr := selfCorrect_error F (singleMask a) (fun a => label a k)
    simp only [parity_singleMask_eval] at herr
    linarith
  have h := Finset.expect_le_expect (s := Finset.univ) (fun k _ => hlocal k)
  simpa only [Finset.expect_add_distrib, Fintype.expect_const, inputReject, distance] using h

/-- Proximity soundness of the actual four finite tests. The only promise
is the property being tested: the queried input is δ-far from every legal label. -/
theorem tester_proximity_soundness (label : A → K → Bool) (σ : K → Bool)
    (F : Cube A → Bool) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4)
    (hfar : ∀ a, δ ≤ distance σ (label a)) :
    δ / 256 ≤ testerReject label σ F := by
  have hblr := blrReject_nonneg F
  have hand := andReject_nonneg F
  have hunit := unitReject_nonneg F
  have hin := inputReject_nonneg label σ F
  by_cases hb : δ / 64 ≤ blrReject F
  · unfold testerReject
    linarith
  obtain ⟨s, hs⟩ := blr_near_parity F
  by_cases hz : s = fun _ => false
  · subst s
    have hu := unitReject_zero_parity F
    unfold testerReject
    linarith
  have hsome : ∃ i, s i = true := by
    by_contra hh
    push Not at hh
    apply hz
    funext i
    have h := hh i
    cases hi : s i <;> simp_all
  obtain ⟨i, hi⟩ := hsome
  by_cases htwo : ∃ j, i ≠ j ∧ s j = true
  · obtain ⟨j, hij, hj⟩ := htwo
    have ha := parity_and_rejection s i j hi hj hij
    have ht := andReject_transfer F s
    unfold testerReject
    linarith
  · have heq : s = singleMask i := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [singleMask, hi]
      · have hj : s j = false := by
          cases hv : s j
          · rfl
          · exact False.elim (htwo ⟨j, Ne.symm hji, hv⟩)
        simp [singleMask, hji, hj]
    subst s
    have ht := inputReject_transfer label σ F i
    have hf := hfar i
    unfold testerReject
    linarith

omit [Fintype A] [DecidableEq A] in
theorem selfCorrect_dictator (a : A) (x r : Cube A) :
    selfCorrect (fun f => f a) x r = x a := by
  change (r a ^^ (r a ^^ x a)) = x a
  cases r a <;> cases x a <;> rfl

def oracleAnswer (σ : K → Bool) (F : Cube A → Bool) : K ⊕ Cube A → Bool :=
  Sum.elim σ F

def eventReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (kind : Fin 4) (k : K) (f g r₀ r₁ r₂ : Cube A) : ℝ :=
  truth (!(eventAccepts kind (fun slot =>
    oracleAnswer σ F (eventQueries label kind k f g r₀ r₁ r₂ slot))))

section

omit [Fintype A] [DecidableEq A] [Fintype K] [Nonempty K]

theorem eventReject_blr (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventReject label σ F 0 k f g r₀ r₁ r₂ =
      disagree (F f ^^ F g) (F (cubeXor f g)) := by
  simp [eventReject, eventAccepts, eventQueries, oracleAnswer, truth_not_decide_eq]

theorem eventReject_and (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventReject label σ F 1 k f g r₀ r₁ r₂ =
      disagree (selfCorrect F (cubeAnd f g) r₀)
        (selfCorrect F f r₁ && selfCorrect F g r₂) := by
  simp [eventReject, eventAccepts, eventQueries, oracleAnswer,
    truth_not_decide_eq, selfCorrect]

theorem eventReject_unit (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventReject label σ F 2 k f g r₀ r₁ r₂ =
      disagree (selfCorrect F (fun _ => true) r₀) true := by
  simp only [eventReject, eventAccepts, eventQueries, oracleAnswer]
  norm_num
  change truth (!(selfCorrect F (fun _ => true) r₀)) =
    disagree (selfCorrect F (fun _ => true) r₀) true
  cases selfCorrect F (fun _ => true) r₀ <;> norm_num [truth, disagree]

theorem eventReject_input (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventReject label σ F 3 k f g r₀ r₁ r₂ =
      disagree (σ k) (selfCorrect F (fun a => label a k) r₀) := by
  simp [eventReject, eventAccepts, eventQueries, oracleAnswer,
    truth_not_decide_eq, selfCorrect]

/-- The honest proof satisfies each explicit event separately, including all
padding slots, so it supplies actual satisfying labels in the incidence graph. -/
theorem event_perfect_completeness (label : A → K → Bool) (a : A)
    (kind : Fin 4) (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventAccepts kind (fun slot => oracleAnswer (label a) (fun x => x a)
      (eventQueries label kind k f g r₀ r₁ r₂ slot)) = true := by
  have hkind : kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by omega
  have hreject : eventReject label (label a) (fun x => x a) kind k f g r₀ r₁ r₂ = 0 := by
    rcases hkind with h | h | h | h <;> subst kind
    · simp [eventReject_blr, cubeXor, disagree]
    · simp [eventReject_and, selfCorrect_dictator, cubeAnd, disagree]
    · simp [eventReject_unit, selfCorrect_dictator, disagree]
    · simp [eventReject_input, selfCorrect_dictator, disagree]
  unfold eventReject at hreject
  cases h : eventAccepts kind (fun slot => oracleAnswer (label a) (fun x => x a)
    (eventQueries label kind k f g r₀ r₁ r₂ slot)) <;> simp_all [truth]

end

/-- One finite uniform sample space for the executable six-address test. -/
def explicitTesterReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) : ℝ :=
  𝔼 kind : Fin 4, 𝔼 k, 𝔼 f, 𝔼 g, 𝔼 r₀, 𝔼 r₁, 𝔼 r₂,
    eventReject label σ F kind k f g r₀ r₁ r₂

theorem explicitTesterReject_eq (label : A → K → Bool) (σ : K → Bool)
    (F : Cube A → Bool) : explicitTesterReject label σ F = testerReject label σ F := by
  unfold explicitTesterReject
  rw [Fintype.expect_eq_sum_div_card]
  simp [Fin.sum_univ_succ, eventReject_blr, eventReject_and, eventReject_unit,
    eventReject_input, testerReject, blrReject, andReject, unitReject, inputReject, add_assoc]

theorem explicit_proximity_soundness (label : A → K → Bool) (σ : K → Bool)
    (F : Cube A → Bool) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4)
    (hfar : ∀ a, δ ≤ distance σ (label a)) :
    δ / 256 ≤ explicitTesterReject label σ F := by
  rw [explicitTesterReject_eq]
  exact tester_proximity_soundness label σ F hδ hδ' hfar

end UniqueGamesTheorem.Foundations.PCP.AssignmentTester

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_CodeComposition
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

theorem disagreement_eq_sign (a b : Bool) :
    disagreement a b = (1 - bitSign a * bitSign b) / 2 := by
  cases a <;> cases b <;> norm_num [disagreement, bitSign]

theorem relativeDistance_eq_sign {X : Type*} [Fintype X] [Nonempty X]
    (f g : X → Bool) :
    relativeDistance f g = (1 - 𝔼 x, bitSign (f x) * bitSign (g x)) / 2 := by
  simp only [relativeDistance, disagreement_eq_sign]
  rw [← Finset.expect_div, Finset.expect_sub_distrib]
  simp

def singletonMask {A : Type*} [DecidableEq A] (a : A) : Cube A :=
  fun i => decide (i = a)

theorem walsh_singletonMask {A : Type*} [Fintype A] [DecidableEq A]
    (a : A) (x : Cube A) : walsh (singletonMask a) x = bitSign (x a) := by
  classical
  unfold walsh singletonMask
  rw [Finset.prod_eq_single a]
  · simp
  · intro b _ hba
    simp [hba, bitSign]
  · simp

theorem singletonMask_ne {A : Type*} [DecidableEq A] {a b : A} (hab : a ≠ b) :
    singletonMask a ≠ singletonMask b := by
  intro h
  have he := congrFun h a
  simp [singletonMask, hab] at he

theorem codeword_distance {A : Type*} [Fintype A] [DecidableEq A]
    {a b : A} (hab : a ≠ b) :
    relativeDistance (codeword a) (codeword b) = 1 / 2 := by
  rw [relativeDistance_eq_sign]
  have horth := walsh_orthogonality (singletonMask a) (singletonMask b)
  rw [ite_eq_right (singletonMask_ne hab)] at horth
  simp_rw [walsh_singletonMask] at horth
  change (1 - 𝔼 x : Cube A, bitSign (x a) * bitSign (x b)) / 2 = 1 / 2
  rw [horth]
  norm_num

theorem exists_nearest {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (f : Cube A → Bool) :
    ∃ a : A, ∀ b : A, relativeDistance f (codeword a) ≤ relativeDistance f (codeword b) := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.exists_min_image Finset.univ
    (fun a : A => relativeDistance f (codeword a)) Finset.univ_nonempty
  exact ⟨a, fun b => ha b (Finset.mem_univ b)⟩

/-- Classical choice is used only for the soundness analysis, not the output algorithm. -/
def nearest {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] (f : Cube A → Bool) : A :=
  Classical.choose (exists_nearest f)

theorem nearest_minimal {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (f : Cube A → Bool) (a : A) :
    relativeDistance f (codeword (nearest f)) ≤ relativeDistance f (codeword a) :=
  Classical.choose_spec (exists_nearest f) a

theorem distance_from_other_codeword {A : Type*} [Fintype A] [DecidableEq A]
    [Nonempty A] (f : Cube A → Bool) {a : A} (ha : a ≠ nearest f) :
    1 / 4 ≤ relativeDistance f (codeword a) := by
  have htri := relativeDistance_triangle (codeword (nearest f)) f (codeword a)
  rw [codeword_distance (Ne.symm ha), relativeDistance_comm (codeword (nearest f)) f] at htri
  have hmin := nearest_minimal f a
  linarith

theorem pairWord_distance {X : Type*} [Fintype X] [Nonempty X]
    (left right left' right' : X → Bool) :
    relativeDistance (pairWord left right) (pairWord left' right') =
      (relativeDistance left left' + relativeDistance right right') / 2 := by
  classical
  simp [relativeDistance, Fintype.expect_eq_sum_div_card, Fintype.card_prod,
    Fintype.sum_prod_type, pairWord]
  ring

/-- Every satisfying encoded pair is far from a pair whose nearest decoding rejects. -/
theorem rejected_pair_far {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (accepts : A → A → Bool) (left right : Cube A → Bool)
    (hbad : accepts (nearest left) (nearest right) = false)
    (a b : A) (hgood : accepts a b = true) :
    1 / 8 ≤ relativeDistance (pairWord left right)
      (pairWord (codeword a) (codeword b)) := by
  rw [pairWord_distance]
  have hleft := relativeDistance_nonnegative left (codeword a)
  have hright := relativeDistance_nonnegative right (codeword b)
  by_cases ha : a = nearest left
  · have hb : b ≠ nearest right := by
      intro hb
      rw [ha, hb, hbad] at hgood
      cases hgood
    have hsep := distance_from_other_codeword right hb
    linarith
  · have hsep := distance_from_other_codeword left ha
    linarith

end UniqueGamesTheorem.Foundations.PCP.CodeComposition

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_AlphabetReductionLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

def edgeTesterReject (accepts : A → A → Bool) (left right : Cube A → Bool)
    (F : Cube (LegalPair accepts) → Bool) : ℝ :=
  AssignmentTester.explicitTesterReject (pairEncoding accepts) (pairWord left right) F

theorem rejected_edge_tester_bound (accepts : A → A → Bool)
    (left right : Cube A → Bool)
    (F : Cube (LegalPair accepts) → Bool)
    (hbad : accepts (nearest left) (nearest right) = false) :
    1 / 2048 ≤ edgeTesterReject accepts left right F := by
  have hfar (p : LegalPair accepts) :
      (1 / 8 : ℝ) ≤ AssignmentTester.distance (pairWord left right) (pairEncoding accepts p) := by
    have h := rejected_pair_far accepts left right hbad p.1.1 p.1.2 p.2
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  have h := AssignmentTester.explicit_proximity_soundness (pairEncoding accepts)
    (pairWord left right) F (δ := 1 / 8) (by norm_num) (by norm_num) hfar
  norm_num at h
  exact h

end UniqueGamesTheorem.Foundations.PCP.AlphabetReduction

end

end

section

namespace UniqueGamesTheorem.Foundations.PCP

namespace ConstraintGraph

variable {V E A : Type*}

def Satisfiable (G : ConstraintGraph V E A) : Prop :=
  ∃ labeling : V → A, ∀ e, G.edgeSatisfied labeling e = true

theorem mem_rejectedDarts [Fintype E] (G : ConstraintGraph V E A)
    (labeling : V → A) (e : E) :
    e ∈ G.rejectedDarts labeling ↔ G.edgeSatisfied labeling e = false := by
  simp [rejectedDarts]

theorem rejected_exists_of_not_satisfiable (G : ConstraintGraph V E A)
    (unsat : ¬ G.Satisfiable) (labeling : V → A) :
    ∃ e, G.edgeSatisfied labeling e = false := by
  classical
  by_contra none
  apply unsat
  refine ⟨labeling, fun e => ?_⟩
  have notFalse : G.edgeSatisfied labeling e ≠ false := by
    intro h
    exact none ⟨e, h⟩
  cases h : G.edgeSatisfied labeling e <;> simp_all

theorem rejectionCount_positive [Fintype E] (G : ConstraintGraph V E A)
    (unsat : ¬ G.Satisfiable) (labeling : V → A) :
    1 ≤ G.rejectionCount labeling := by
  obtain ⟨e, he⟩ := G.rejected_exists_of_not_satisfiable unsat labeling
  exact Finset.one_le_card.mpr ⟨e, (G.mem_rejectedDarts labeling e).mpr he⟩

end ConstraintGraph

end UniqueGamesTheorem.Foundations.PCP

end

section

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.ConstraintGraph

variable {V E A : Type*}

section Minimum

variable [Fintype V] [Fintype E] [Fintype A] [Nonempty A]

def rejectionCounts (G : ConstraintGraph V E A) : Finset Nat := by
  classical
  exact Finset.univ.image G.rejectionCount

theorem rejectionCounts_nonempty (G : ConstraintGraph V E A) :
    G.rejectionCounts.Nonempty := by
  classical
  exact Finset.univ_nonempty.image G.rejectionCount

def minimumRejections (G : ConstraintGraph V E A) : Nat :=
  G.rejectionCounts.min' G.rejectionCounts_nonempty

theorem minimumRejections_le (G : ConstraintGraph V E A) (labeling : V → A) :
    G.minimumRejections ≤ G.rejectionCount labeling := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨labeling, Finset.mem_univ _, rfl⟩)

theorem exists_minimizer (G : ConstraintGraph V E A) :
    ∃ labeling : V → A, G.rejectionCount labeling = G.minimumRejections := by
  classical
  have h := Finset.min'_mem G.rejectionCounts G.rejectionCounts_nonempty
  obtain ⟨labeling, _, heq⟩ := Finset.mem_image.mp h
  exact ⟨labeling, heq⟩

omit [Fintype V] [Fintype A] [Nonempty A] in
theorem rejectionCount_eq_zero_iff (G : ConstraintGraph V E A) (labeling : V → A) :
    G.rejectionCount labeling = 0 ↔ ∀ e, G.edgeSatisfied labeling e = true := by
  classical
  constructor
  · intro h e
    have hempty : G.rejectedDarts labeling = ∅ := Finset.card_eq_zero.mp h
    cases he : G.edgeSatisfied labeling e with
    | false =>
        have hm := (G.mem_rejectedDarts labeling e).mpr he
        rw [hempty] at hm
        simp at hm
    | true => rfl
  · intro h
    simp [rejectionCount, rejectedDarts, h]

theorem minimumRejections_eq_zero_iff (G : ConstraintGraph V E A) :
    G.minimumRejections = 0 ↔ G.Satisfiable := by
  constructor
  · intro h
    obtain ⟨labeling, heq⟩ := G.exists_minimizer
    exact ⟨labeling, (G.rejectionCount_eq_zero_iff labeling).mp (heq.trans h)⟩
  · rintro ⟨labeling, h⟩
    have hc := (G.rejectionCount_eq_zero_iff labeling).mpr h
    exact Nat.eq_zero_of_le_zero (hc ▸ G.minimumRejections_le labeling)

def gap (G : ConstraintGraph V E A) : ℝ :=
  (G.minimumRejections : ℝ) / Fintype.card E

theorem gap_nonnegative (G : ConstraintGraph V E A) : 0 ≤ G.gap :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- A lower bound on the actual minimum is exactly the universal count bound. -/
theorem le_gap_iff [Nonempty E] (G : ConstraintGraph V E A) (ε : ℝ) :
    ε ≤ G.gap ↔ ∀ labeling : V → A,
      ε * Fintype.card E ≤ (G.rejectionCount labeling : ℝ) := by
  have he : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  change ε ≤ (G.minimumRejections : ℝ) / Fintype.card E ↔ _
  rw [le_div_iff₀ he]
  constructor
  · intro h labeling
    exact h.trans (Nat.cast_le.mpr (G.minimumRejections_le labeling))
  · intro h
    obtain ⟨labeling, heq⟩ := G.exists_minimizer
    simpa only [heq] using h labeling

theorem inverse_card_le_gap_of_unsatisfiable [Nonempty E]
    (G : ConstraintGraph V E A) (unsat : ¬ G.Satisfiable) :
    1 / (Fintype.card E : ℝ) ≤ G.gap := by
  apply (G.le_gap_iff _).mpr
  intro labeling
  have he : (Fintype.card E : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : (1 : ℝ) ≤ (G.rejectionCount labeling : ℝ) := by
    exact_mod_cast G.rejectionCount_positive unsat labeling
  simpa only [div_mul_cancel₀ _ he] using hc

end Minimum

section Reindex

variable {W D B : Type*}

theorem reindex_edgeSatisfied (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B)
    (labeling : V → A) (e : E) :
    (G.reindex vertices darts labels).edgeSatisfied (labelingEquiv vertices labels labeling)
      (darts e) = G.edgeSatisfied labeling e := by
  simp [reindex, labelingEquiv, edgeSatisfied, head, Equiv.trans_apply]

theorem reindex_rejectionCount [Fintype E] [Fintype D] (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B) (labeling : V → A) :
    (G.reindex vertices darts labels).rejectionCount (labelingEquiv vertices labels labeling) =
      G.rejectionCount labeling := by
  classical
  unfold rejectionCount
  symm
  apply Finset.card_bij (fun e _ => darts e)
  · intro e he
    rw [mem_rejectedDarts, reindex_edgeSatisfied]
    exact (G.mem_rejectedDarts labeling e).mp he
  · intro e _ f _ h
    exact darts.injective h
  · intro d hd
    refine ⟨darts.symm d, ?_, darts.apply_symm_apply d⟩
    rw [mem_rejectedDarts]
    rw [← reindex_edgeSatisfied G vertices darts labels labeling (darts.symm d)]
    rw [darts.apply_symm_apply]
    exact (mem_rejectedDarts _ _ _).mp hd

variable [Fintype V] [Fintype E] [Fintype A] [Nonempty A]
  [Fintype W] [Fintype D] [Fintype B] [Nonempty B]

omit [Nonempty A] [Nonempty B] in
theorem rejectionCounts_reindex (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B) :
    (G.reindex vertices darts labels).rejectionCounts = G.rejectionCounts := by
  classical
  ext n
  simp only [rejectionCounts, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨labeling, hn⟩
    refine ⟨(labelingEquiv vertices labels).symm labeling, ?_⟩
    rw [← reindex_rejectionCount G vertices darts labels,
      Equiv.apply_symm_apply]
    exact hn
  · rintro ⟨labeling, hn⟩
    refine ⟨labelingEquiv vertices labels labeling, ?_⟩
    rw [reindex_rejectionCount]
    exact hn

theorem minimumRejections_reindex (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B) :
    (G.reindex vertices darts labels).minimumRejections = G.minimumRejections := by
  unfold minimumRejections
  simp only [rejectionCounts_reindex]

theorem satisfiable_reindex (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B) :
    (G.reindex vertices darts labels).Satisfiable ↔ G.Satisfiable := by
  rw [← minimumRejections_eq_zero_iff, minimumRejections_reindex,
    minimumRejections_eq_zero_iff]

end Reindex

end UniqueGamesTheorem.Foundations.PCP.ConstraintGraph

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_GraphTables
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
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

theorem enumeratedGraph_edgeSatisfied {V E A : Type*} {n m : Nat}
    (G : ConstraintGraph V E A) (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m)
    (labelOrder : A ≃ Label) (labeling : V → A) (e : E) :
    (enumeratedGraph G vertexOrder dartOrder labelOrder).edgeSatisfied
      (fun v => labelOrder (labeling (vertexOrder.symm v))) (dartOrder e) =
        G.edgeSatisfied labeling e := by
  simp [ConstraintGraph.edgeSatisfied, ConstraintGraph.head, enumeratedGraph]

/-- Every directed occurrence contributes once before and after enumeration. -/
theorem enumeratedGraph_rejectionCount {V E A : Type*} [Fintype E] {n m : Nat}
    (G : ConstraintGraph V E A) (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m)
    (labelOrder : A ≃ Label) (labeling : V → A) :
    (enumeratedGraph G vertexOrder dartOrder labelOrder).rejectionCount
      (fun v => labelOrder (labeling (vertexOrder.symm v))) = G.rejectionCount labeling := by
  classical
  unfold ConstraintGraph.rejectionCount
  symm
  apply Finset.card_equiv dartOrder
  intro e
  simp only [ConstraintGraph.mem_rejectedDarts, enumeratedGraph_edgeSatisfied]

end UniqueGamesTheorem.Foundations.PCP.GraphTables

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_GenericGraphTables
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
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

variable {q : Nat}

instance instDecidableValid {n m : Nat} (rows : Rows q n m) : Decidable (Valid rows) := by
  unfold Valid
  infer_instance

theorem enumeratedGraph_edgeSatisfied {V E A : Type*} {n m : Nat}
    (G : ConstraintGraph V E A) (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m)
    (labelOrder : A ≃ (Label q)) (labeling : V → A) (e : E) :
    (enumeratedGraph G vertexOrder dartOrder labelOrder).edgeSatisfied
      (fun v => labelOrder (labeling (vertexOrder.symm v))) (dartOrder e) =
        G.edgeSatisfied labeling e := by
  simp [ConstraintGraph.edgeSatisfied, ConstraintGraph.head, enumeratedGraph]

/-- Every directed occurrence contributes once before and after enumeration. -/
theorem enumeratedGraph_rejectionCount {V E A : Type*} [Fintype E] {n m : Nat}
    (G : ConstraintGraph V E A) (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m)
    (labelOrder : A ≃ (Label q)) (labeling : V → A) :
    (enumeratedGraph G vertexOrder dartOrder labelOrder).rejectionCount
      (fun v => labelOrder (labeling (vertexOrder.symm v))) = G.rejectionCount labeling := by
  classical
  unfold ConstraintGraph.rejectionCount
  symm
  apply Finset.card_equiv dartOrder
  intro e
  simp only [ConstraintGraph.mem_rejectedDarts, enumeratedGraph_edgeSatisfied]

end UniqueGamesTheorem.Foundations.PCP.GenericGraphTables

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_InputLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
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
open UniqueGamesTheorem.Foundations.Complexity
open GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K] {q : Nat}

abbrev State (σ : Type) (q : Nat) := (σ × RelationTable q) × Option Bool

@[instance_reducible] def stateFintype (σ : Type) (q : Nat) [Fintype σ] :
    Fintype (State σ q) := by
  letI := relationFintype q
  exact inferInstance

/-- Read one encoded Boolean into a fixed slot of the finite relation register. -/
def readSlot (source : K) (i : Fin (q * q))
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q)) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q) :=
  .pop source
    (fun state head =>
      ((state.1.1, state.1.2.set i.val (head.getD false) i.isLt), head))
    (.branch (fun state => state.2.getD false)
      (.pop source (fun state _ => (state.1, none)) next)
      (.load (fun state => (state.1, none)) next))

theorem stepAux_readSlot (source : K) (i : Fin (q * q)) (bit : Bool)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q))
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (initial : RelationTable q) (register : Option Bool) :
    TM2.stepAux (readSlot source i next) ((ambient, initial), register)
      (Function.update base source (encodeWord (bitWord bit) ++ suffix)) =
      TM2.stepAux next ((ambient, initial.set i.val bit i.isLt), none)
        (Function.update base source suffix) := by
  cases bit <;> simp [readSlot, TM2.stepAux, bitWord, encodeWord]

def readSlots (source : K) : List (Fin (q * q)) →
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q) →
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q)
  | [], next => .load (fun state => (state.1, none)) next
  | i :: indices, next => readSlot source i (readSlots source indices next)

def indexedWords (relation : RelationTable q) (indices : List (Fin (q * q))) : List Nat :=
  indices.map (fun i => bitWord relation[i.val])

def fillSlots (relation : RelationTable q) : List (Fin (q * q)) →
    RelationTable q → RelationTable q
  | [], initial => initial
  | i :: indices, initial =>
      fillSlots relation indices (initial.set i.val relation[i.val] i.isLt)

theorem fillSlots_preserves_correct (relation : RelationTable q)
    (indices : List (Fin (q * q))) (initial : RelationTable q) (i : Fin (q * q))
    (hcorrect : initial[i.val] = relation[i.val]) :
    (fillSlots relation indices initial)[i.val] = relation[i.val] := by
  induction indices generalizing initial with
  | nil => exact hcorrect
  | cons j indices ih =>
    apply ih
    by_cases hji : j.val = i.val
    · simp [hji]
    · simp [hji, hcorrect]

theorem fillSlots_mem (relation : RelationTable q) (indices : List (Fin (q * q)))
    (initial : RelationTable q) (i : Fin (q * q)) (hi : i ∈ indices) :
    (fillSlots relation indices initial)[i.val] = relation[i.val] := by
  induction indices generalizing initial with
  | nil => simp at hi
  | cons j indices ih =>
    change (fillSlots relation indices (initial.set j.val relation[j.val] j.isLt))[i.val] = _
    rcases List.mem_cons.mp hi with h | h
    · subst j
      apply fillSlots_preserves_correct
      simp
    · exact ih _ h

theorem fillSlots_finRange (relation initial : RelationTable q) :
    fillSlots relation (List.finRange (q * q)) initial = relation := by
  apply Vector.ext
  intro i hi
  exact fillSlots_mem relation (List.finRange (q * q)) initial ⟨i, hi⟩
    (List.mem_finRange _)

theorem indexedWords_finRange (relation : RelationTable q) :
    indexedWords relation (List.finRange (q * q)) = relationWords relation := by
  have h : (List.finRange (q * q)).map (fun i => relation[i.val]) = relation.toList := by
    rw [List.finRange, List.map_ofFn]
    change List.ofFn (fun i : Fin (q * q) => relation[i.val]) = relation.toList
    rw [← Vector.toList_ofFn, Vector.ofFn_getElem]
  calc
    _ = ((List.finRange (q * q)).map (fun i => relation[i.val])).map bitWord := by
      simp only [indexedWords, List.map_map, Function.comp_def]
    _ = relation.toList.map bitWord := congrArg (fun bits : List Bool => bits.map bitWord) h
    _ = _ := rfl

/-- Each stored register bit is obtained from its actual serialized field. -/
theorem stepAux_readSlots (source : K) (indices : List (Fin (q * q)))
    (relation : RelationTable q)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q))
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (initial : RelationTable q) (register : Option Bool) :
    TM2.stepAux (readSlots source indices next) ((ambient, initial), register)
      (Function.update base source (encodeWords (indexedWords relation indices) ++ suffix)) =
      TM2.stepAux next ((ambient, fillSlots relation indices initial), none)
        (Function.update base source suffix) := by
  induction indices generalizing initial register with
  | nil => simp [readSlots, fillSlots, indexedWords, encodeWords, TM2.stepAux]
  | cons i indices ih =>
    simp only [readSlots, indexedWords, List.map_cons, encodeWords, List.append_assoc, fillSlots]
    rw [stepAux_readSlot]
    exact ih _ none

/-- Fixed finite program fragment; it can be inserted before any continuation. -/
def readRelation (source : K)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q)) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q) :=
  readSlots source (List.finRange (q * q)) next

theorem stepAux_readRelation (source : K) (relation : RelationTable q)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q))
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (initial : RelationTable q) (register : Option Bool) :
    TM2.stepAux (readRelation source next) ((ambient, initial), register)
      (Function.update base source (encodeWords (relationWords relation) ++ suffix)) =
      TM2.stepAux next ((ambient, relation), none) (Function.update base source suffix) := by
  simpa only [readRelation, indexedWords_finRange, fillSlots_finRange] using
    stepAux_readSlots source (List.finRange (q * q)) relation next
      base suffix ambient initial register

def parser (source : K) (exitLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q) :=
  readRelation source (.goto fun _ => exitLabel)

theorem parserStep (source : K) (readLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ q))
    (atRead : program readLabel = parser source exitLabel)
    (base : K → List Bool) (relation : RelationTable q) (suffix : List Bool)
    (ambient : σ) (initial : RelationTable q) (register : Option Bool) :
    TM2.step program
      ⟨some readLabel, ((ambient, initial), register),
        Function.update base source (encodeWords (relationWords relation) ++ suffix)⟩ =
      some ⟨some exitLabel, ((ambient, relation), none), Function.update base source suffix⟩ := by
  change some (TM2.stepAux (program readLabel) ((ambient, initial), register)
    (Function.update base source (encodeWords (relationWords relation) ++ suffix))) = _
  rw [atRead, parser, stepAux_readRelation]
  rfl

/-- One transition executes the fixed chain of `q*q` slot readers. -/
theorem parserTrace (source : K) (readLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ q))
    (atRead : program readLabel = parser source exitLabel)
    (base : K → List Bool) (relation : RelationTable q) (suffix : List Bool)
    (ambient : σ) (initial : RelationTable q) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some readLabel, ((ambient, initial), register),
        Function.update base source (encodeWords (relationWords relation) ++ suffix)⟩) =
      some ⟨some exitLabel, ((ambient, relation), none), Function.update base source suffix⟩ := by
  simpa only [Function.iterate_one, MachineComposition.advance_some] using
    parserStep source readLabel exitLabel program atRead base relation suffix ambient initial register

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.ReadRelation

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

open UniqueGamesTheorem.Reduction CloneGap ActualSource
open Clone100Triples Clone100Counting
open scoped BigOperators

noncomputable section

def lift {n : Nat} (a : Fin n → Bool) : Fin (n * 100) → Bool :=
  fun v => a ((nameEquiv n).symm v).1

def majority {n : Nat} (a : Fin (n * 100) → Bool) : Fin n → Bool :=
  fun v => majorityBit (fun i => a (nameEquiv n (v, i)))

end
end UniqueGamesTheorem.Outer.Clone100

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_CleanupLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
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

@[simp] theorem clearTapes_selected {n : Nat} (selected : Fin n → K)
    (base : K → List Bool) (i : Fin n) : clearTapes selected base (selected i) = [] := by
  rw [clearTapes_apply, ite_eq_left ⟨i, rfl⟩]

theorem clearTapes_unselected {n : Nat} (selected : Fin n → K)
    (base : K → List Bool) (k : K) (notSelected : ∀ i, selected i ≠ k) :
    clearTapes selected base k = base k := by
  rw [clearTapes_apply]
  simp [notSelected]

/-- Enumerating exactly the nonoutput stacks yields the standard final tape
family. Repeated selected stacks are permitted. -/
theorem clearTapes_outputOnly {n : Nat} (selected : Fin n → K)
    (output : K) (base : K → List Bool)
    (excludesOutput : ∀ i, selected i ≠ output)
    (coversOther : ∀ k, k ≠ output → ∃ i, selected i = k) :
    clearTapes selected base = fun k => if k = output then base output else [] := by
  funext k
  by_cases h : k = output
  · subst k
    simp [clearTapes_unselected selected base output excludesOutput]
  · rw [clearTapes_apply]
    simp [h, coversOther k h]

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Cleanup

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_Emitter
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
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
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ : Type} {h bound : Nat} [DecidableEq K]

/-- The finite relation table is encoded one actual Boolean branch at a time. -/
def bitCommands (bits : List (σ → Bool)) : List (Command h σ bound) := bits.map .bit

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Emitter

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_ClauseVerifierLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP

open Target

def matchingSlots (a b : ClauseAnswer) : Nat :=
  (if a.first = b.first then 1 else 0) +
  (if a.second = b.second then 1 else 0) +
  (if a.third = b.third then 1 else 0)

theorem matchingSlots_le (a b : ClauseAnswer) : matchingSlots a b ≤ 3 := by
  rcases a with ⟨a₁,a₂,a₃⟩
  rcases b with ⟨b₁,b₂,b₃⟩
  cases a₁ <;> cases a₂ <;> cases a₃ <;> cases b₁ <;> cases b₂ <;> cases b₃ <;> decide

theorem matchingSlots_eq_three (a b : ClauseAnswer) : matchingSlots a b = 3 ↔ a = b := by
  rcases a with ⟨a₁,a₂,a₃⟩
  rcases b with ⟨b₁,b₂,b₃⟩
  cases a₁ <;> cases a₂ <;> cases a₃ <;> cases b₁ <;> cases b₂ <;> cases b₃ <;> decide

def acceptedSlots {n : Nat} (clause : Clause n) (alice bob : ClauseAnswer) : Nat :=
  if localSatisfies clause alice then matchingSlots alice bob else 0

def clauseFailure {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) : Nat :=
  if clause.eval assignment then 0 else 1

abbrev AliceStrategy (formula : Formula) := Fin formula.clauses.length → ClauseAnswer
abbrev BobStrategy (formula : Formula) := Fin formula.variables → Bool

def allIndices (formula : Formula) : List (Fin formula.clauses.length) :=
  List.finRange formula.clauses.length

end UniqueGamesTheorem.Foundations.PCP

end

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceContexts

open Target PCP

instance clauseAnswerInhabited : Inhabited ClauseAnswer := ⟨⟨false, false, false⟩⟩

instance slotInhabited : Inhabited Slot := ⟨.first⟩

theorem validJ_satisfies (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (j : J u) (hj : validJ F c j = true) (t : Fin u) :
    localSatisfies (clauseAt F (c t)) (j t) = true :=
  ((validJ_eq_true_iff F c j).mp hj).1 t

theorem validJ_consistent (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (j : J u) (hj : validJ F c j = true) (t : Fin u) (s : Slot)
    (t' : Fin u) (s' : Slot)
    (hname : nameAt (clauseAt F (c t)) s = nameAt (clauseAt F (c t')) s') :
    answerAt (j t) s = answerAt (j t') s' :=
  ((validJ_eq_true_iff F c j).mp hj).2 t t' s s' hname

theorem validJ_localConsistent (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (j : J u) (hj : validJ F c j = true) (t : Fin u) :
    localConsistent (clauseAt F (c t)) (j t) = true := by
  apply (localConsistent_eq_true_iff _ _).mpr
  intro s s' hs
  exact validJ_consistent F c j hj t s t s' hs

theorem canonicalSlot_name {n : ℕ} (clause : Clause n) (v : Fin n)
    (hv : ∃ s, nameAt clause s = v) : nameAt clause (canonicalSlot clause v) = v := by
  by_cases hfirst : nameAt clause .first = v
  · simp [canonicalSlot, hfirst]
  by_cases hsecond : nameAt clause .second = v
  · simp [canonicalSlot, hfirst, hsecond]
  obtain ⟨s, hs⟩ := hv
  cases s with
  | first => exact False.elim (hfirst hs)
  | second => exact False.elim (hsecond hs)
  | third => simpa [canonicalSlot, hfirst, hsecond] using hs

theorem baseAccepts_implies_sampled (F : Formula) (c : Fin F.clauses.length)
    (s : Slot) (i : Bool) (j : ClauseAnswer)
    (h : baseAccepts F (nameAt (clauseAt F c) s) c i j = true) :
    (localSatisfies (clauseAt F c) j && decide (answerAt j s = i)) = true := by
  obtain ⟨hsat, hcons, heq⟩ := (baseAccepts_eq_true_iff F _ _ _ _).mp h
  have hname := canonicalSlot_name (clauseAt F c) (nameAt (clauseAt F c) s) ⟨s, rfl⟩
  have hans := (localConsistent_eq_true_iff _ _).mp hcons s
    (canonicalSlot (clauseAt F c) (nameAt (clauseAt F c) s)) hname.symm
  simp [hsat, hans.trans heq]

end UniqueGamesTheorem.Foundations.Hastad.SourceContexts

end

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature

open Target PCP SourceContexts

def signatureEquiv (u : ℕ) :
    Signature u ≃ (Position u → Bool) × NameProfile u × SlotContext u where
  toFun σ := (σ.signs, σ.sameName, σ.selected)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv σ := by cases σ; rfl
  right_inv p := by rcases p with ⟨a, b, c⟩; rfl

instance signatureFintype (u : ℕ) : Fintype (Signature u) :=
  Fintype.ofEquiv ((Position u → Bool) × NameProfile u × SlotContext u)
    (signatureEquiv u).symm

end UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_NameCompaction
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
An explicit name compaction for finite three-literal CNF formulas. Only the
occurring names are scanned: the declared variable count is never enumerated.
Both assignment transports preserve every clause evaluation and therefore
every finite clause-score gap. The encoding bound is a size theorem; a machine
running-time bound and the constant-gap PCP construction remain separate.
-/

namespace UniqueGamesTheorem.Foundations.PCP.NameCompaction

open UniqueGamesTheorem.Foundations.Target

def evaluationList (F : Formula) (A : Fin F.variables → Bool) : List Bool :=
  F.clauses.map (fun c => c.eval A)

def failedCount (F : Formula) (A : Fin F.variables → Bool) : Nat :=
  (evaluationList F A).count false

theorem evaluations_allIndices (F : Formula) (A : Fin F.variables → Bool) :
    ((allIndices F).map (fun i => (clauseAt F i).eval A)) = evaluationList F A := by
  calc
    _ = (List.ofFn (fun i : Fin F.clauses.length => F.clauses[i.val])).map
        (fun c => c.eval A) := by
      simp only [allIndices, List.finRange, clauseAt, List.map_ofFn, Function.comp_def]
    _ = _ := by rw [List.ofFn_getElem]; rfl

end UniqueGamesTheorem.Foundations.PCP.NameCompaction

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_InitialGraphLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
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

def variableLabel (value : Bool) : Label := (value, false, false)

end UniqueGamesTheorem.Foundations.PCP.InitialGraph

end

section

/-! Reversible regular port graphs and their actual finite walks. Vertices may
repeat; loops and parallel edges retain their distinct ports. The rotation
map sends an outgoing dart to its arrival dart and is an involution. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringWalks

variable {V D : Type*}

def headTailEquiv (V D : Type*) (n : Nat) :
    Walk V D (n + 1) ≃ (Walk V D n × D) where
  toFun w := ((w.1, fun j => w.2 j.succ), w.2 0)
  invFun z := (z.1.1, Fin.cases z.2 z.1.2)
  left_inv w := by
    apply Prod.ext
    · rfl
    · funext j
      exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

/-- Isolate any actual path edge. Previously traversed ports are replaced by
their arrival ports, so the change of coordinates remains invertible. -/
def pivotEquiv (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) →
      (Walk V D (n + 1) ≃ (Edge V D × (Fin n → D)))
  | 0, _ => splitHead V D 0
  | n + 1, k => Fin.cases (splitHead V D (n + 1))
      (fun j => (rotateHead G (n + 1)).trans
        ((headTailEquiv V D (n + 1)).trans
          ((Equiv.prodCongr (pivotEquiv G n j) (Equiv.refl D)).trans
            (headTailEquiv (Edge V D) D n).symm))) k

theorem pivotEquiv_fst (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 1)),
      (pivotEquiv G n k w).1 = edgeAt G n w k := by
  intro n
  induction n with
  | zero => intro k w; rfl
  | succ n ih =>
    intro k w
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · change (pivotEquiv G n j (advanceTail G w)).1 =
        edgeAt G n (advanceTail G w) j
      exact ih j (advanceTail G w)

theorem edgeAt_port (G : PortGraph V D) :
    ∀ (n : Nat) (w : Walk V D (n + 1)) (k : Fin (n + 1)),
      (edgeAt G n w k).2 = w.2 k := by
  intro n
  induction n with
  | zero =>
    intro w k
    have hk : k = 0 := Fin.eq_zero k
    subst k
    rfl
  | succ n ih =>
    intro w k
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · exact ih (advanceTail G w) j

theorem pivotEquiv_succ_apply (G : PortGraph V D)
    (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 2)) :
    pivotEquiv G (n + 1) k.succ w =
      ((pivotEquiv G n k (advanceTail G w)).1,
       Fin.cases (G.rot (w.1, w.2 0)).2
         (pivotEquiv G n k (advanceTail G w)).2) := rfl

def leftFromPivot (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) → V → (Fin n → D) → V
  | 0, _, v, _ => v
  | n + 1, k, v, r => Fin.cases v
      (fun j => next G (leftFromPivot G n j v (fun m => r m.succ)) (r 0)) k

def rightFromPivot (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) → Edge V D → (Fin n → D) → V
  | 0, _, e, _ => next G e.1 e.2
  | n + 1, k, e, r => Fin.cases
      (wordEnd G (n + 1) (next G e.1 e.2) r)
      (fun j => rightFromPivot G n j e (fun m => r m.succ)) k

theorem leftFromPivot_actual (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 1)),
      leftFromPivot G n k (pivotEquiv G n k w).1.1 (pivotEquiv G n k w).2 = w.1 := by
  intro n
  induction n with
  | zero => intro k w; rfl
  | succ n ih =>
    intro k w
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · rw [pivotEquiv_succ_apply]
      change next G
        (leftFromPivot G n j (pivotEquiv G n j (advanceTail G w)).1.1
          (pivotEquiv G n j (advanceTail G w)).2)
        (G.rot (w.1, w.2 0)).2 = w.1
      rw [ih j (advanceTail G w)]
      change (G.rot ((G.rot (w.1, w.2 0)).1, (G.rot (w.1, w.2 0)).2)).1 = w.1
      exact congrArg Prod.fst (rot_rot G (w.1, w.2 0))

theorem rightFromPivot_actual (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 1)),
      rightFromPivot G n k (pivotEquiv G n k w).1 (pivotEquiv G n k w).2 =
        endpoint G w := by
  intro n
  induction n with
  | zero => intro k w; rfl
  | succ n ih =>
    intro k w
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · rw [pivotEquiv_succ_apply]
      change rightFromPivot G n j (pivotEquiv G n j (advanceTail G w)).1
        (pivotEquiv G n j (advanceTail G w)).2 = endpoint G w
      rw [ih j (advanceTail G w)]
      rfl

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

theorem replacement_complete [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (labeling : V → A) (h : ∀ e, G.edgeSatisfied labeling e = true) :
    ∀ p, (replacementGraph G H).edgeSatisfied (liftLabel G labeling) p = true := by
  rintro ⟨e, p⟩
  rcases p with d | u
  · exact replacement_satisfied_inl G H labeling e d
  · rw [replacement_satisfied_inr]
    exact h e

theorem rejectionCount_eq_sum [Fintype E] (G : ConstraintGraph V E A)
    (labeling : V → A) :
    G.rejectionCount labeling =
      ∑ e, if G.edgeSatisfied labeling e = false then 1 else 0 := by
  classical
  simp only [ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts,
    Finset.card_eq_sum_ones, Finset.sum_filter]

theorem padded_complete (G : ConstraintGraph V E A) (dummy : V → Type*)
    (labeling : V → A) (h : ∀ e, G.edgeSatisfied labeling e = true) :
    ∀ c, (paddedGraph G dummy).edgeSatisfied labeling c = true := by
  intro c
  cases c with
  | inl e => exact h e
  | inr z => rfl

theorem padded_rejectionCount [Fintype V] [Fintype E]
    (G : ConstraintGraph V E A) (dummy : V → Type*) [∀ v, Fintype (dummy v)]
    (labeling : V → A) :
    (paddedGraph G dummy).rejectionCount labeling = G.rejectionCount labeling := by
  classical
  simp only [rejectionCount_eq_sum, Fintype.sum_sum_type]
  simp
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rfl

end UniqueGamesTheorem.Foundations.PCP.DegreeReplacement

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PoweringLabelsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Relations.repeatedConsistentDecidable _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
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

instance finitePortWords [Finite D] (t : Nat) : Finite (PortWords D t) := by
  let := Fintype.ofFinite D
  exact Finite.of_fintype _

instance finiteBall [Finite D] (G : PortGraph V D) (t : Nat) (v : V) :
    Finite (Ball G t v) :=
  Finite.of_surjective (wordToBall G t v) (wordToBall_surjective G t v)

def encode (G : PortGraph V D) (t : Nat) (v : V) (ℓ : Ball G t v → A) :
    PaddedLabel D t A := fun w => ℓ (wordToBall G t v w)

theorem decode_encode {G : PortGraph V D} {t : Nat} {v : V}
    (S : AddressSelector G t v) (ℓ : Ball G t v → A) :
    decode S (encode G t v ℓ) = ℓ := by
  funext u
  change ℓ (wordToBall G t v (S.address u)) = ℓ u
  rw [S.correct]

end UniqueGamesTheorem.Foundations.PCP.PoweringLabels

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

theorem dartBlockEquiv_val (d n : Nat) (p : Fin (n + 1) → Fin d) (b : Bool) :
    (dartBlockEquiv d n (p, b)).val =
      2 * (wordEquiv d (n + 1) p).val + (orientationEquiv b).val := by
  change (orientationEquiv b).val + 2 * (wordEquiv d (n + 1) p).val = _
  exact Nat.add_comm _ _

theorem dartEquiv_val (vertices d n : Nat) (b : Bool) (v : Fin vertices)
    (p : Fin (n + 1) → Fin d) :
    (dartEquiv vertices d n (b, (v, p))).val =
      (2 * d ^ (n + 1)) * v.val +
        2 * (wordEquiv d (n + 1) p).val + (orientationEquiv b).val := by
  change (dartBlockEquiv d n (p, b)).val + (2 * d ^ (n + 1)) * v.val = _
  rw [dartBlockEquiv_val]
  omega

def encodeDart (vertices d n : Nat) :
    (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) →
      Fin (2 * vertices * d ^ (n + 1)) := dartEquiv vertices d n

def decodeDart (vertices d n : Nat) :
    Fin (2 * vertices * d ^ (n + 1)) →
      (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) := (dartEquiv vertices d n).symm

@[simp] theorem decodeDart_encodeDart (vertices d n : Nat)
    (e : Bool × (Fin vertices × (Fin (n + 1) → Fin d))) :
    decodeDart vertices d n (encodeDart vertices d n e) = e :=
  (dartEquiv vertices d n).symm_apply_apply e

@[simp] theorem encodeDart_decodeDart (vertices d n : Nat)
    (i : Fin (2 * vertices * d ^ (n + 1))) :
    encodeDart vertices d n (decodeDart vertices d n i) = i :=
  (dartEquiv vertices d n).apply_symm_apply i

end UniqueGamesTheorem.Foundations.PCP.PoweringEnumeration

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

variable {E X : Type*} {q : Nat}

def response (T : Verifier E X q) (assignment : X → Bool) (event : E) : Label q :=
  fun i => assignment (T.query event i)

theorem canonicalSlot_query [DecidableEq X] (T : Verifier E X q) (event : E) (i : Fin q) :
    T.query event (canonicalSlot T event i) = T.query event i :=
  Fin.find_spec (p := fun j => T.query event j = T.query event i) ⟨i, rfl⟩

theorem edgeSatisfied_eq_incidence [DecidableEq X] (T : Verifier E X q)
    (positive : 0 < q) (labeling : Vertex E X → Label q)
    (event : E) (slot : Fin q) (orientation : Bool) :
    (graph T positive).edgeSatisfied labeling ((event, slot), orientation) =
      incidenceAccept T positive event slot (labeling (.inl event))
        (labeling (.inr (T.query event slot))) := by
  cases orientation <;> rfl

def honestLabeling (T : Verifier E X q) (assignment : X → Bool) : Vertex E X → Label q
  | .inl event => response T assignment event
  | .inr address => encodeRight (assignment address)

theorem honest_leftValid (T : Verifier E X q) (assignment : X → Bool) (event : E)
    (accepted : T.accepts event (response T assignment event) = true) :
    LeftValid T event (response T assignment event) := by
  refine ⟨accepted, ?_⟩
  intro i j hij
  exact congrArg assignment hij

theorem honest_incidence [DecidableEq X] (T : Verifier E X q) (positive : 0 < q)
    (assignment : X → Bool) (event : E)
    (accepted : T.accepts event (response T assignment event) = true) (slot : Fin q) :
    incidenceAccept T positive event slot
      (honestLabeling T assignment (.inl event))
      (honestLabeling T assignment (.inr (T.query event slot))) = true := by
  simp only [incidenceAccept, Bool.and_eq_true, honestLabeling,
    decode_encodeRight]
  refine ⟨_root_.decide_eq_true (honest_leftValid T assignment event accepted), ?_⟩
  exact _root_.decide_eq_true (congrArg assignment (canonicalSlot_query T event slot))

theorem perfect_completeness [DecidableEq X] (T : Verifier E X q) (positive : 0 < q)
    (assignment : X → Bool)
    (accepted : ∀ event, T.accepts event (response T assignment event) = true) :
    ∀ dart, (graph T positive).edgeSatisfied (honestLabeling T assignment) dart = true := by
  rintro ⟨⟨event, slot⟩, orientation⟩
  rw [edgeSatisfied_eq_incidence]
  exact honest_incidence T positive assignment event (accepted event) slot

theorem satisfiable_of_verifier_satisfiable [DecidableEq X] (T : Verifier E X q)
    (positive : 0 < q)
    (sat : ∃ assignment : X → Bool,
      ∀ event, T.accepts event (response T assignment event) = true) :
    (graph T positive).Satisfiable := by
  obtain ⟨assignment, h⟩ := sat
  exact ⟨honestLabeling T assignment, perfect_completeness T positive assignment h⟩

def decodedAssignment (positive : 0 < q) (labeling : Vertex E X → Label q) : X → Bool :=
  fun address => decodeRight positive (labeling (.inr address))

theorem incidenceAccept_true [DecidableEq X] (T : Verifier E X q) (positive : 0 < q)
    (event : E) (slot : Fin q) (left right : Label q)
    (accepted : incidenceAccept T positive event slot left right = true) :
    T.accepts event left = true ∧ RepeatedConsistent T event left ∧
      left (canonicalSlot T event slot) = decodeRight positive right := by
  simp only [incidenceAccept, Bool.and_eq_true] at accepted
  have hvalid : LeftValid T event left := _root_.of_decide_eq_true accepted.1
  exact ⟨hvalid.1, hvalid.2, _root_.of_decide_eq_true accepted.2⟩

theorem all_incidences_imply_event [DecidableEq X] (T : Verifier E X q)
    (positive : 0 < q) (labeling : Vertex E X → Label q) (event : E)
    (accepted : ∀ slot, incidenceAccept T positive event slot (labeling (.inl event))
      (labeling (.inr (T.query event slot))) = true) :
    T.accepts event (response T (decodedAssignment positive labeling) event) = true := by
  have first := incidenceAccept_true T positive event (zeroSlot positive) _ _
    (accepted (zeroSlot positive))
  have labels_equal : labeling (.inl event) = response T (decodedAssignment positive labeling) event := by
    funext slot
    have info := incidenceAccept_true T positive event slot _ _ (accepted slot)
    exact (first.2.1 slot (canonicalSlot T event slot)
      (canonicalSlot_query T event slot).symm).trans info.2.2
  rw [← labels_equal]
  exact first.1

theorem rejected_event_forces_slot [DecidableEq X] (T : Verifier E X q)
    (positive : 0 < q) (labeling : Vertex E X → Label q) (event : E)
    (rejected : T.accepts event (response T (decodedAssignment positive labeling) event) = false) :
    ∃ slot, incidenceAccept T positive event slot (labeling (.inl event))
      (labeling (.inr (T.query event slot))) = false := by
  classical
  by_contra none
  have all : ∀ slot, incidenceAccept T positive event slot (labeling (.inl event))
      (labeling (.inr (T.query event slot))) = true := by
    intro slot
    cases h : incidenceAccept T positive event slot (labeling (.inl event))
        (labeling (.inr (T.query event slot))) with
    | false => exact False.elim (none ⟨slot, h⟩)
    | true => rfl
  have h := all_incidences_imply_event T positive labeling event all
  rw [rejected] at h
  cases h

def rejectedEvents [Fintype E] (T : Verifier E X q) (assignment : X → Bool) : Finset E :=
  Finset.univ.filter (fun event => T.accepts event (response T assignment event) = false)

def verifierRejectionCount [Fintype E] (T : Verifier E X q) (assignment : X → Bool) : Nat :=
  (rejectedEvents T assignment).card

/-- Every rejected event contributes two distinct rejected darts, one in each
orientation. A classical witness is used only in this counting proof. -/
theorem rejection_count_bound [Fintype E] [DecidableEq X]
    (T : Verifier E X q) (positive : 0 < q) (labeling : Vertex E X → Label q) :
    2 * verifierRejectionCount T (decodedAssignment positive labeling) ≤
      (graph T positive).rejectionCount labeling := by
  classical
  let failed := rejectedEvents T (decodedAssignment positive labeling)
  have witnesses : ∀ event, event ∈ failed →
      ∃ slot, incidenceAccept T positive event slot (labeling (.inl event))
        (labeling (.inr (T.query event slot))) = false := by
    intro event he
    apply rejected_event_forces_slot T positive labeling event
    simpa [failed, rejectedEvents] using he
  let chosen := fun event he => Classical.choose (witnesses event he)
  let inject : (failed.product (Finset.univ : Finset Bool)) →
      (graph T positive).rejectedDarts labeling := fun p =>
    ⟨((p.val.1, chosen p.val.1 (Finset.mem_product.mp p.property).1), p.val.2), by
      apply (ConstraintGraph.mem_rejectedDarts _ _ _).mpr
      rw [edgeSatisfied_eq_incidence]
      exact Classical.choose_spec (witnesses p.val.1 (Finset.mem_product.mp p.property).1)⟩
  have injective : Function.Injective inject := by
    intro a b h
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun d => d.val.1.1) h
    · exact congrArg (fun d => d.val.2) h
  have bound := Finset.card_le_card_of_injective injective
  simpa [failed, verifierRejectionCount, ConstraintGraph.rejectionCount,
    Finset.card_product, Nat.mul_comm] using bound

end UniqueGamesTheorem.Foundations.PCP.QueryIncidence

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_AlphabetRetractionLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

theorem satisfiable_pullback_iff (G : ConstraintGraph V E A)
    (decode : B → A) (encode : A → B) (sectionLaw : ∀ a, decode (encode a) = a) :
    (pullback G decode).Satisfiable ↔ G.Satisfiable := by
  constructor
  · rintro ⟨labeling, h⟩
    exact ⟨decode ∘ labeling, h⟩
  · rintro ⟨labeling, h⟩
    refine ⟨encode ∘ labeling, fun e => ?_⟩
    change G.accepts e (decode (encode (labeling (G.tail e))))
      (decode (encode (labeling (G.head e)))) = true
    simpa only [ConstraintGraph.edgeSatisfied, sectionLaw] using h e

end UniqueGamesTheorem.Foundations.PCP.AlphabetRetraction

end

section

namespace UniqueGamesTheorem.Foundations.PCP.SpectralReturn

open PoweringWalks
open scoped BigOperators

noncomputable section

def iterateOperator {V D : Type*} [Fintype D] (G : PortGraph V D) :
    Nat → (V → ℝ) → (V → ℝ)
  | 0, f => f
  | n + 1, f => averagingOperator G (iterateOperator G n f)

def markedStep {V D : Type*} [Fintype D] (G : PortGraph V D)
    (bad : V × D → Bool) (f : V → ℝ) (v : V) : ℝ :=
  Finset.univ.expect (fun d => if bad (v, d) then f (G.rot (v, d)).1 else 0)

def returnMass {V D : Type*} [Fintype V] [Fintype D]
    (G : PortGraph V D) (bad : V × D → Bool) (gap : Nat) : ℝ :=
  mean (markedStep G bad (iterateOperator G gap (edgeProfile bad)))

structure SpectralCertificate {V D : Type*} [Fintype V] [Fintype D]
    (G : PortGraph V D) (lambda : ℝ) : Prop where
  nonnegative : 0 ≤ lambda
  lt_one : lambda < 1
  contraction : ∀ f : V → ℝ, mean f = 0 →
    energy (averagingOperator G f) ≤ lambda ^ 2 * energy f

section Averages

variable {A B : Type*} [Fintype A] [Fintype B]

@[simp] theorem mean_const [Nonempty A] (c : ℝ) : mean (fun _ : A => c) = c :=
  Fintype.expect_const c

theorem mean_add (f g : A → ℝ) :
    mean (fun x => f x + g x) = mean f + mean g :=
  Finset.expect_add_distrib _ f g

theorem mean_sub (f g : A → ℝ) :
    mean (fun x => f x - g x) = mean f - mean g :=
  Finset.expect_sub_distrib _ f g

theorem mean_mul_left (c : ℝ) (f : A → ℝ) :
    mean (fun x => c * f x) = c * mean f :=
  (Finset.mul_expect _ f c).symm

theorem mean_mul_right (f : A → ℝ) (c : ℝ) :
    mean (fun x => f x * c) = mean f * c :=
  (Finset.expect_mul _ f c).symm

theorem mean_nonnegative (f : A → ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ mean f :=
  Finset.expect_nonneg (fun x _ => hf x)

theorem mean_mono {f g : A → ℝ} (h : ∀ x, f x ≤ g x) : mean f ≤ mean g :=
  Finset.expect_le_expect (fun x _ => h x)

theorem energy_nonnegative (f : A → ℝ) : 0 ≤ energy f :=
  mean_nonnegative _ (fun x => sq_nonneg (f x))

theorem energy_sub_const [Nonempty A] (f : A → ℝ) (c : ℝ) :
    energy (fun x => f x - c) = energy f - 2 * c * mean f + c ^ 2 := by
  have h : (fun x => (f x - c) ^ 2) =
      (fun x => (f x) ^ 2 - (2 * c) * f x + c ^ 2) := by
    funext x
    ring
  unfold energy
  rw [h, mean_add, mean_sub, mean_mul_left, mean_const]

theorem correlation_sub_const [Nonempty A] (f g : A → ℝ) (c d : ℝ) :
    correlation (fun x => f x - c) (fun x => g x - d) =
      correlation f g - d * mean f - c * mean g + c * d := by
  have h : (fun x => (f x - c) * (g x - d)) =
      (fun x => f x * g x - d * f x - c * g x + c * d) := by
    funext x
    ring
  unfold correlation
  rw [h, mean_add, mean_sub, mean_sub, mean_mul_left, mean_mul_left, mean_const]

end Averages

section Graph

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
  (G : PortGraph V D)

omit [Nonempty V] in
theorem mean_operator (f : V → ℝ) : mean (averagingOperator G f) = mean f := by
  calc
    mean (averagingOperator G f) = mean (fun e : V × D => f (G.rot e).1) :=
      (mean_prod (fun e : V × D => f (G.rot e).1)).symm
    _ = mean (fun e : V × D => f e.1) := mean_equiv G.rot (fun e => f e.1)
    _ = mean (fun v : V => mean (fun _ : D => f v)) :=
      mean_prod (fun e : V × D => f e.1)
    _ = mean f := by simp only [mean_const]

omit [Fintype V] [Nonempty V] in
theorem operator_sub_const (f : V → ℝ) (c : ℝ) :
    averagingOperator G (fun v => f v - c) = fun v => averagingOperator G f v - c := by
  funext v
  change mean (fun d => f (G.rot (v, d)).1 - c) = _
  rw [mean_sub, mean_const]
  rfl

omit [Nonempty V] in
theorem mean_iterate (n : Nat) (f : V → ℝ) : mean (iterateOperator G n f) = mean f := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterateOperator, mean_operator, ih]

omit [Fintype V] [Nonempty V] in
theorem iterate_sub_const (n : Nat) (f : V → ℝ) (c : ℝ) :
    iterateOperator G n (fun v => f v - c) = fun v => iterateOperator G n f v - c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterateOperator, ih, operator_sub_const]; rfl

omit [Nonempty V] [Nonempty D] in
/-- Reversal moves the first marked edge to its endpoint. The profile therefore
appears at the endpoint, before the `gap` remaining vertex transitions. -/
theorem mean_markedStep (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (f : V → ℝ) :
    mean (markedStep G bad f) = correlation (edgeProfile bad) f := by
  calc
    mean (markedStep G bad f) =
        mean (fun e : V × D => if bad e then f (G.rot e).1 else 0) := by
      exact (mean_prod (fun e : V × D => if bad e then f (G.rot e).1 else 0)).symm
    _ = mean (fun e : V × D => if bad (G.rot e)
          then f (G.rot (G.rot e)).1 else 0) :=
      (mean_equiv G.rot (fun e : V × D => if bad e then f (G.rot e).1 else 0)).symm
    _ = mean (fun e : V × D => if bad e then f e.1 else 0) := by
      congr 1
      funext e
      rw [reversal e, G.rot_involutive e]
    _ = mean (fun v => mean (fun d => if bad (v, d) then f v else 0)) :=
      mean_prod (fun e : V × D => if bad e then f e.1 else 0)
    _ = correlation (edgeProfile bad) f := by
      unfold correlation
      congr 1
      funext v
      have h : (fun d => if bad (v, d) then f v else 0) =
          (fun d => (if bad (v, d) then (1 : ℝ) else 0) * f v) := by
        funext d
        cases bad (v, d) <;> simp
      rw [h, mean_mul_right]
      rfl

omit [Nonempty V] [Nonempty D] in
theorem returnMass_eq_correlation (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (gap : Nat) :
    returnMass G bad gap = correlation (edgeProfile bad)
      (iterateOperator G gap (edgeProfile bad)) :=
  mean_markedStep G bad reversal _

omit [Nonempty V] in
theorem iterate_energy_bound (lambda : ℝ) (certificate : SpectralCertificate G lambda)
    (f : V → ℝ) (hf : mean f = 0) (n : Nat) :
    energy (iterateOperator G n f) ≤ (lambda ^ n) ^ 2 * energy f := by
  induction n with
  | zero => simp [iterateOperator]
  | succ n ih =>
      calc
        energy (iterateOperator G (n + 1) f) ≤
            lambda ^ 2 * energy (iterateOperator G n f) :=
          certificate.contraction _ ((mean_iterate G n f).trans hf)
        _ ≤ lambda ^ 2 * ((lambda ^ n) ^ 2 * energy f) :=
          mul_le_mul_of_nonneg_left ih (sq_nonneg lambda)
        _ = (lambda ^ (n + 1)) ^ 2 * energy f := by rw [pow_succ]; ring

omit [Nonempty V] in
theorem zero_mean_correlation_bound (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (f : V → ℝ)
    (hf : mean f = 0) (n : Nat) :
    correlation f (iterateOperator G n f) ≤ lambda ^ n * energy f := by
  have hsq : correlation f (iterateOperator G n f) ^ 2 ≤
      (lambda ^ n * energy f) ^ 2 := by
    calc
      _ ≤ energy f * energy (iterateOperator G n f) := correlation_sq_le _ _
      _ ≤ energy f * ((lambda ^ n) ^ 2 * energy f) :=
        mul_le_mul_of_nonneg_left (iterate_energy_bound G lambda certificate f hf n)
          (energy_nonnegative f)
      _ = _ := by ring
  exact le_of_sq_le_sq hsq
    (mul_nonneg (pow_nonneg certificate.nonnegative n) (energy_nonnegative f))

theorem correlation_centered (f : V → ℝ) (n : Nat) :
    correlation f (iterateOperator G n f) = mean f ^ 2 +
      correlation (fun v => f v - mean f)
        (iterateOperator G n (fun v => f v - mean f)) := by
  rw [iterate_sub_const, correlation_sub_const, mean_iterate]
  ring

end Graph

section Profiles

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]

omit [Fintype V] [Nonempty V] [Nonempty D] in
theorem edgeProfile_nonnegative (bad : V × D → Bool) (v : V) : 0 ≤ edgeProfile bad v :=
  mean_nonnegative _ (fun d => by cases bad (v, d) <;> norm_num)

omit [Fintype V] [Nonempty V] in
theorem edgeProfile_le_one (bad : V × D → Bool) (v : V) : edgeProfile bad v ≤ 1 := by
  change mean (fun d => if bad (v, d) then (1 : ℝ) else 0) ≤ 1
  calc
    _ ≤ mean (fun _ : D => (1 : ℝ)) := mean_mono (fun d => by
      cases bad (v, d) <;> norm_num)
    _ = 1 := mean_const _

omit [Nonempty V] [Nonempty D] in
theorem edgeDensity_nonnegative (bad : V × D → Bool) : 0 ≤ edgeDensity bad :=
  mean_nonnegative _ (edgeProfile_nonnegative bad)

omit [Nonempty V] in
theorem edgeProfile_energy_le_density (bad : V × D → Bool) :
    energy (edgeProfile bad) ≤ edgeDensity bad :=
  mean_mono (fun v => by
    have h0 := edgeProfile_nonnegative bad v
    have h1 := edgeProfile_le_one bad v
    nlinarith)

theorem edgeProfile_centered_energy (bad : V × D → Bool) :
    energy (fun v => edgeProfile bad v - edgeDensity bad) ≤
      edgeDensity bad * (1 - edgeDensity bad) := by
  rw [energy_sub_const]
  have h := edgeProfile_energy_le_density bad
  change energy (edgeProfile bad) - 2 * edgeDensity bad * edgeDensity bad +
    edgeDensity bad ^ 2 ≤ _
  nlinarith

/-- Sharp return bound. No division by the bad-edge density occurs, so the empty
bad set is covered. `gap = 0` gives the adjacent-edge upper bound `epsilon`. -/
theorem returnMass_le_sharp (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (gap : Nat) :
    returnMass G bad gap ≤ edgeDensity bad ^ 2 +
      lambda ^ gap * (edgeDensity bad * (1 - edgeDensity bad)) := by
  rw [returnMass_eq_correlation G bad reversal, correlation_centered]
  have hzero : mean (fun v => edgeProfile bad v - edgeDensity bad) = 0 := by
    rw [mean_sub, mean_const]
    simp only [edgeDensity, sub_self]
  have hc := zero_mean_correlation_bound G lambda certificate
    (fun v => edgeProfile bad v - edgeDensity bad) hzero gap
  have hv := mul_le_mul_of_nonneg_left (edgeProfile_centered_energy bad)
    (pow_nonneg certificate.nonnegative gap)
  change edgeDensity bad ^ 2 + _ ≤ _
  exact add_le_add (le_refl _) (hc.trans hv)

/-- The simple bound used in the second-moment estimate. -/
theorem returnMass_le (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (gap : Nat) :
    returnMass G bad gap ≤ edgeDensity bad ^ 2 + edgeDensity bad * lambda ^ gap := by
  have h := returnMass_le_sharp G lambda certificate bad reversal gap
  have hvar : edgeDensity bad * (1 - edgeDensity bad) ≤ edgeDensity bad := by
    nlinarith [sq_nonneg (edgeDensity bad)]
  have hm := mul_le_mul_of_nonneg_left hvar (pow_nonneg certificate.nonnegative gap)
  nlinarith

end Profiles

/-- The finite geometric-series bound that absorbs forward and reverse returns.
It applies to every finite window, with no limiting probability argument. -/
theorem geometric_sum_le (lambda : ℝ) (h0 : 0 ≤ lambda) (h1 : lambda < 1) (n : Nat) :
    (∑ k ∈ Finset.range n, lambda ^ k) ≤ 1 / (1 - lambda) := by
  have hsum : (∑ k ∈ Finset.range n, lambda ^ k) * (1 - lambda) = 1 - lambda ^ n := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, pow_succ]; nlinarith
  have hden : 0 < 1 - lambda := by linarith
  apply (le_div_iff₀ hden).2
  rw [hsum]
  linarith [pow_nonneg h0 n]

section ReturnSums

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]

/-- The return contribution from one marked edge, over a finite forward window. -/
theorem sum_returnMass_le (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (n : Nat) :
    (∑ gap ∈ Finset.range n, returnMass G bad gap) ≤
      (n : ℝ) * edgeDensity bad ^ 2 + edgeDensity bad / (1 - lambda) := by
  calc
    _ ≤ ∑ gap ∈ Finset.range n,
        (edgeDensity bad ^ 2 + edgeDensity bad * lambda ^ gap) :=
      Finset.sum_le_sum (fun gap _ => returnMass_le G lambda certificate bad reversal gap)
    _ = (n : ℝ) * edgeDensity bad ^ 2 +
        edgeDensity bad * (∑ gap ∈ Finset.range n, lambda ^ gap) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (n : ℝ) * edgeDensity bad ^ 2 + edgeDensity bad * (1 / (1 - lambda)) :=
      add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left
          (geometric_sum_le lambda certificate.nonnegative certificate.lt_one n)
          (edgeDensity_nonnegative bad))
    _ = _ := by ring

/-- Sum over all distinct ordered-time pairs, counting each pair once.
The row for the later edge `j` has gaps `0,...,j-1`. -/
theorem triangular_returnMass_sum_le (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (n : Nat) :
    (∑ j ∈ Finset.range n, ∑ gap ∈ Finset.range j, returnMass G bad gap) ≤
      ((n : ℝ) * ((n : ℝ) - 1) / 2) * edgeDensity bad ^ 2 +
        (n : ℝ) * (edgeDensity bad / (1 - lambda)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hrow := sum_returnMass_le G lambda certificate bad reversal n
      have h := add_le_add ih hrow
      calc
        _ ≤ ((n : ℝ) * ((n : ℝ) - 1) / 2) * edgeDensity bad ^ 2 +
            (n : ℝ) * (edgeDensity bad / (1 - lambda)) +
            ((n : ℝ) * edgeDensity bad ^ 2 + edgeDensity bad / (1 - lambda)) := h
        _ = _ := by simp only [Nat.cast_add, Nat.cast_one]; ring

/-- The exact finite envelope needed after expanding the square of the hit
count. The diagonal contributes `n * epsilon`; both off-diagonal triangles
contribute twice the return sum. The actual walk-event identity is supplied by
`PoweringMoment` and `PoweringReturn`. -/
theorem secondMoment_return_envelope (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e) (n : Nat) :
    (n : ℝ) * edgeDensity bad +
        2 * (∑ j ∈ Finset.range n, ∑ gap ∈ Finset.range j, returnMass G bad gap) ≤
      (n : ℝ) * edgeDensity bad *
        (1 + 2 / (1 - lambda) + ((n : ℝ) - 1) * edgeDensity bad) := by
  calc
    _ ≤ (n : ℝ) * edgeDensity bad +
        2 * (((n : ℝ) * ((n : ℝ) - 1) / 2) * edgeDensity bad ^ 2 +
          (n : ℝ) * (edgeDensity bad / (1 - lambda))) :=
      add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left
          (triangular_returnMass_sum_le G lambda certificate bad reversal n) (by norm_num))
    _ = _ := by ring

end ReturnSums

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

/-- Uniform cube measure is invariant under this explicit xor translation. -/
def xorTranslation (y : Cube I) : Cube I ≃ Cube I where
  toFun x := cubeXor x y
  invFun x := cubeXor x y
  left_inv x := cubeXor_cancel_right x y
  right_inv x := cubeXor_cancel_right x y

/-- The generator of a powered port is the xor of its original port word. -/
def powerGenerators (g : D → Cube I) : (n : Nat) → (Fin n → D) → Cube I
  | 0, _ => zeroFrequency
  | n + 1, p => cubeXor (g (p 0)) (powerGenerators g n (fun j => p j.succ))

section Finite

variable [Fintype I] [DecidableEq I] [Fintype D]

/-- The eigenvalue is the empirical bias of the generator characters. -/
def eigenvalue (g : D → Cube I) (s : Cube I) : ℝ :=
  𝔼 d, walsh s (g d)

/-- Change variables through xor translation in the actual Fourier average. -/
theorem coefficient_xorTranslation (f : Cube I → ℝ) (s v : Cube I) :
    coefficient (fun x => f (cubeXor x v)) s = walsh s v * coefficient f s := by
  calc
    coefficient (fun x => f (cubeXor x v)) s =
        𝔼 x, f x * walsh s (cubeXor x v) := by
      unfold coefficient
      apply Fintype.expect_equiv (xorTranslation v)
      intro x
      change f (cubeXor x v) * walsh s x =
        f (cubeXor x v) * walsh s (cubeXor (cubeXor x v) v)
      rw [cubeXor_cancel_right]
    _ = 𝔼 x, (f x * walsh s x) * walsh s v := by
      apply Finset.expect_congr rfl
      intro x _
      rw [walsh_xor]
      ring
    _ = coefficient f s * walsh s v := by
      rw [← Finset.expect_mul]
      rfl
    _ = walsh s v * coefficient f s := mul_comm _ _

/-- Full Walsh diagonalization, obtained by swapping the two finite averages. -/
theorem coefficient_cayleyAverage (g : D → Cube I) (f : Cube I → ℝ) (s : Cube I) :
    coefficient (cayleyAverage g f) s = eigenvalue g s * coefficient f s := by
  calc
    coefficient (cayleyAverage g f) s =
        𝔼 x, 𝔼 d, f (cubeXor x (g d)) * walsh s x := by
      unfold coefficient cayleyAverage
      simp only [cayleyGraph_rot, Finset.expect_mul]
    _ = 𝔼 d, 𝔼 x, f (cubeXor x (g d)) * walsh s x := by
      rw [Finset.expect_comm]
    _ = 𝔼 d, walsh s (g d) * coefficient f s := by
      apply Finset.expect_congr rfl
      intro d _
      exact coefficient_xorTranslation f s (g d)
    _ = eigenvalue g s * coefficient f s := by
      rw [← Finset.expect_mul]
      rfl

/-- Uniform finite port-word splitting multiplies the actual eigenvalues. -/
theorem eigenvalue_powerGenerators (g : D → Cube I) (n : Nat) (s : Cube I) :
    eigenvalue (powerGenerators g n) s = eigenvalue g s ^ n := by
  induction n with
  | zero =>
    let : Nonempty (Fin 0 → D) := ⟨fun i => Fin.elim0 i⟩
    simp [eigenvalue, powerGenerators, zeroFrequency, walsh, bitSign]
  | succ n ih =>
    calc
      eigenvalue (powerGenerators g (n + 1)) s =
          𝔼 z : D × (Fin n → D),
            walsh s (cubeXor (g z.1) (powerGenerators g n z.2)) := by
        unfold eigenvalue
        apply Fintype.expect_equiv (splitPortWord n)
        intro p
        rfl
      _ = 𝔼 d, 𝔼 p : Fin n → D,
          walsh s (cubeXor (g d) (powerGenerators g n p)) := by
        exact SpectralReturn.mean_prod _
      _ = eigenvalue g s * eigenvalue (powerGenerators g n) s := by
        simp_rw [walsh_xor, ← Finset.mul_expect]
        rw [← Finset.expect_mul]
        rfl
      _ = eigenvalue g s ^ (n + 1) := by
        rw [ih, pow_succ, mul_comm]

/-- A bias bound on all nonconstant generator characters contracts the actual
mean-zero function energy. The constant coefficient is eliminated by its exact
identification with the mean, and every other coefficient is bounded termwise.
-/
theorem cayley_energy_contraction (g : D → Cube I) (lambda : ℝ) (_hlambda : 0 ≤ lambda)
    (hbias : ∀ s : Cube I, s ≠ zeroFrequency → |eigenvalue g s| ≤ lambda)
    (f : Cube I → ℝ) (hmean : (𝔼 x, f x) = 0) :
    (𝔼 x, cayleyAverage g f x ^ 2) ≤ lambda ^ 2 * (𝔼 x, f x ^ 2) := by
  classical
  have hzero : coefficient f zeroFrequency = 0 := by
    rw [coefficient_zeroFrequency]
    exact hmean
  calc
    (𝔼 x, cayleyAverage g f x ^ 2) =
        ∑ s, coefficient (cayleyAverage g f) s ^ 2 := (walsh_parseval _).symm
    _ = ∑ s, (eigenvalue g s * coefficient f s) ^ 2 := by
      simp only [coefficient_cayleyAverage]
    _ ≤ ∑ s, lambda ^ 2 * coefficient f s ^ 2 := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : s = zeroFrequency
      · subst s
        simp [hzero]
      · have hb := hbias s hs
        have hlo : -lambda ≤ eigenvalue g s := (abs_le.mp hb).1
        have hhi : eigenvalue g s ≤ lambda := (abs_le.mp hb).2
        have hprod : 0 ≤ (lambda - eigenvalue g s) * (lambda + eigenvalue g s) :=
          mul_nonneg (sub_nonneg.mpr hhi) (by linarith)
        have hsq : eigenvalue g s ^ 2 ≤ lambda ^ 2 := by nlinarith
        calc
          (eigenvalue g s * coefficient f s) ^ 2 =
              eigenvalue g s ^ 2 * coefficient f s ^ 2 := by rw [mul_pow]
          _ ≤ lambda ^ 2 * coefficient f s ^ 2 :=
            mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ = lambda ^ 2 * (𝔼 x, f x ^ 2) := by
      rw [← Finset.mul_sum, walsh_parseval]

/-- The Fourier proof supplies the graph certificate used in return bounds. -/
theorem cayley_spectralCertificate (g : D → Cube I) (lambda : ℝ)
    (hlambda : 0 ≤ lambda) (hlambdaone : lambda < 1)
    (hbias : ∀ s : Cube I, s ≠ zeroFrequency → |eigenvalue g s| ≤ lambda) :
    SpectralReturn.SpectralCertificate (cayleyGraph g) lambda where
  nonnegative := hlambda
  lt_one := hlambdaone
  contraction := by
    intro f hf
    change (𝔼 x, cayleyAverage g f x ^ 2) ≤ lambda ^ 2 * (𝔼 x, f x ^ 2)
    exact cayley_energy_contraction g lambda hlambda hbias f hf

theorem power_eigenvalue_bound (g : D → Cube I) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (hbias : ∀ s : Cube I, s ≠ zeroFrequency → |eigenvalue g s| ≤ lambda)
    (n : Nat) (s : Cube I) (hs : s ≠ zeroFrequency) :
    |eigenvalue (powerGenerators g n) s| ≤ lambda ^ n := by
  rw [eigenvalue_powerGenerators, abs_pow]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih (hbias s hs) (abs_nonneg _) (pow_nonneg hlambda _)

end Finite

end UniqueGamesTheorem.Foundations.PCP.CayleySpectral

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_CayleySampling
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
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

section Walsh

variable {I : Type*} [Fintype I] [DecidableEq I] [Fintype D] [DecidableEq D]

omit [DecidableEq I] in
theorem exists_true_of_ne_zero (s : Cube I) (hs : s ≠ fun _ => false) :
    ∃ i, s i = true := by
  by_contra h
  apply hs
  funext i
  cases hi : s i
  · rfl
  · exact False.elim (h ⟨i, hi⟩)

/-- Actual parity words from independently indexed uniform cube vectors have
exactly the uniform Boolean-word distribution. -/
theorem expect_parity_samples (s : Cube I) (hs : s ≠ fun _ => false)
    (F : (D → Bool) → ℝ) :
    (𝔼 g : D → Cube I, F (fun d => AssignmentTester.parity s (g d))) =
      𝔼 b : D → Bool, F b := by
  obtain ⟨i, hi⟩ := exists_true_of_ne_zero s hs
  exact expect_boolean_samples (AssignmentTester.parity s) (AssignmentTester.flipAt i)
    (AssignmentTester.flipAt_twice i)
    (fun x => AssignmentTester.parity_flipAt s i x hi) F

end Walsh

end UniqueGamesTheorem.Foundations.PCP.CayleySampling

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_CayleyTailCount
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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
open UniqueGamesTheorem.Foundations.Hastad (bitSign)

variable {α : Type*} [DecidableEq α]

section Words

variable {D : Type*} [Fintype D]

/-- The sign convention is the existing Walsh convention: false is +1, true is -1. -/
theorem bitSign_mean_eq [Nonempty D] (word : D → Bool) :
    (𝔼 i, bitSign (word i)) =
      1 - 2 * ((countTrue word : ℝ) / Fintype.card D) := by
  have hsign (b : Bool) : bitSign b = 1 - 2 * (if b = true then (1 : ℝ) else 0) := by
    cases b <;> norm_num [bitSign]
  calc
    _ = (𝔼 i : D, (1 - 2 * (if word i = true then (1 : ℝ) else 0))) := by
      apply Finset.expect_congr rfl
      intro i _
      exact hsign (word i)
    _ = 1 - 2 * (𝔼 i, if word i = true then (1 : ℝ) else 0) := by
      rw [Finset.expect_sub_distrib, ← Finset.mul_expect, Fintype.expect_const]
    _ = _ := by
      rw [Fintype.expect_eq_sum_div_card, Finset.sum_boole]
      rfl

/-- Excluding both closed integer tails bounds the actual mean Walsh sign. -/
theorem not_badWord_bias (m : ℕ) (hcard : Fintype.card D = 4 * m) (hm : 0 < m)
    (word : D → Bool) (hword : ¬ badWord m word) :
    |𝔼 i, bitSign (word i)| ≤ (1 / 2 : ℝ) := by
  have hD : 0 < Fintype.card D := by rw [hcard]; omega
  let : Nonempty D := Fintype.card_pos_iff.mp hD
  have hlo : m < countTrue word := lt_of_not_ge (not_or.mp hword).1
  have hhi : countTrue word < 3 * m := lt_of_not_ge (not_or.mp hword).2
  have hmr : 0 < (m : ℝ) := by exact_mod_cast hm
  have hlor : (m : ℝ) ≤ countTrue word := by exact_mod_cast hlo.le
  have hhir : (countTrue word : ℝ) ≤ 3 * m := by exact_mod_cast hhi.le
  have hden : 0 < 4 * (m : ℝ) := by positivity
  have hratioLo : (1 / 4 : ℝ) ≤ (countTrue word : ℝ) / (4 * m) :=
    (le_div_iff₀ hden).mpr (by nlinarith)
  have hratioHi : (countTrue word : ℝ) / (4 * m) ≤ (3 / 4 : ℝ) :=
    (div_le_iff₀ hden).mpr (by nlinarith)
  rw [bitSign_mean_eq word, hcard]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  apply abs_le.mpr
  constructor <;> linarith

end Words

end UniqueGamesTheorem.Foundations.PCP.CayleyTailCount

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_ExpandersLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

abbrev Generators (n m : Nat) := Fin (4 * m) → Cube (Fin n)

/-- The zero character is excluded from the bad-event count. -/
def badFrequency {n m : Nat} (g : Generators n m) (s : Cube (Fin n)) : ℝ :=
  if s = zeroFrequency then 0 else
    if CayleyTailCount.badWord m (fun d => AssignmentTester.parity s (g d)) then 1 else 0

def badMass {n m : Nat} (g : Generators n m) : ℝ :=
  ∑ s : Cube (Fin n), badFrequency g s

theorem badFrequency_nonnegative {n m : Nat}
    (g : Generators n m) (s : Cube (Fin n)) : 0 ≤ badFrequency g s := by
  unfold badFrequency
  split_ifs <;> norm_num

theorem mean_badFrequency_le {n m : Nat} (s : Cube (Fin n)) :
    (𝔼 g : Generators n m, badFrequency g s) ≤ 2 * (2 / 3 : ℝ) ^ m := by
  classical
  by_cases hs : s = zeroFrequency
  · simp only [badFrequency, ite_eq_left hs, Finset.expect_const_zero]
    positivity
  · have hs' : s ≠ (fun _ => false) := hs
    simp only [badFrequency, ite_eq_right hs]
    rw [CayleySampling.expect_parity_samples s hs'
      (fun w : Fin (4 * m) → Bool => if CayleyTailCount.badWord m w then (1 : ℝ) else 0)]
    exact CayleyTailCount.twoTail_probability m (by simp)

theorem mean_badMass_le (n m : Nat) (hm : 3 * (n + 2) ≤ m) :
    (𝔼 g : Generators n m, badMass g) ≤ 1 / 2 := by
  calc
    _ = ∑ s : Cube (Fin n), 𝔼 g : Generators n m, badFrequency g s := by
      unfold badMass
      rw [Finset.expect_sum_comm]
    _ ≤ ∑ _s : Cube (Fin n), 2 * (2 / 3 : ℝ) ^ m :=
      Finset.sum_le_sum (fun s _ => mean_badFrequency_le s)
    _ = (2 : ℝ) ^ n * (2 * (2 / 3 : ℝ) ^ m) := by
      simp [Cube]
    _ ≤ 1 / 2 := CayleyTailCount.union_bound_le_half n m hm

/-- Actual finite generators with a simultaneous bound for every nonconstant
Walsh character. The proof selects a point with bad-event count less than one.
-/
theorem exists_generators (n m : Nat) (hm : 3 * (n + 2) ≤ m) :
    ∃ g : Generators n m, ∀ s : Cube (Fin n),
      s ≠ zeroFrequency → |eigenvalue g s| ≤ (1 / 2 : ℝ) := by
  classical
  have hmpos : 0 < m := by omega
  let : Nonempty (Fin (4 * m)) := ⟨⟨0, by omega⟩⟩
  have havg : (𝔼 g : Generators n m, badMass g) < (1 : ℝ) :=
    lt_of_le_of_lt (mean_badMass_le n m hm) (by norm_num)
  obtain ⟨g, _, hg⟩ := Finset.exists_lt_of_expect_lt Finset.univ_nonempty havg
  refine ⟨g, fun s hs => ?_⟩
  have hgood : ¬ CayleyTailCount.badWord m
      (fun d => AssignmentTester.parity s (g d)) := by
    intro hbad
    have hsingle : badFrequency g s ≤ badMass g :=
      Finset.single_le_sum (fun t _ => badFrequency_nonnegative g t) (Finset.mem_univ s)
    simp only [badFrequency, ite_eq_right hs, ite_eq_left hbad] at hsingle
    exact (not_le_of_gt hg) hsingle
  unfold eigenvalue
  simp_rw [← AssignmentTester.bitSign_parity]
  exact CayleyTailCount.not_badWord_bias m (by simp) hmpos _ hgood

theorem base_arithmetic :
    4 * initialQuarterDegree = initialDegree ∧
    3 * (baseDimension + 2) ≤ initialQuarterDegree ∧
    (2 : Nat) ^ baseDimension = (initialDegree ^ basePower) ^ 4 ∧
    (1 / 2 : ℝ) ^ basePower ≤ 1 / 100 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [initialDegree, initialQuarterDegree]
  · norm_num [baseDimension, initialQuarterDegree]
  · unfold baseDimension initialDegree basePower
    rw [← pow_mul, ← pow_mul]
  · norm_num [basePower]

theorem exists_initial_generators :
    ∃ g : Generators baseDimension initialQuarterDegree,
      ∀ s : Cube (Fin baseDimension), s ≠ zeroFrequency →
        |eigenvalue g s| ≤ (1 / 2 : ℝ) :=
  exists_generators _ _ base_arithmetic.2.1

abbrev BaseVertex := Cube (Fin baseDimension)
abbrev BasePort := Fin basePower → Fin (4 * initialQuarterDegree)

theorem card_basePort : Fintype.card BasePort = baseDegree := by
  simp only [BasePort, Fintype.card_fun, Fintype.card_fin]
  rw [base_arithmetic.1]
  rfl

theorem card_baseVertex : Fintype.card BaseVertex = baseDegree ^ 4 := by
  simpa only [BaseVertex, Cube, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, baseDegree] using base_arithmetic.2.2.1

/-- A genuine finite regular graph with the exact degree/size relation needed
for zigzag. Its spectral certificate follows from the actual generator witness.
-/
theorem exists_baseGraph :
    ∃ H : PoweringWalks.PortGraph BaseVertex BasePort,
      SpectralReturn.SpectralCertificate H (1 / 100 : ℝ) := by
  obtain ⟨g, hg⟩ := exists_initial_generators
  refine ⟨cayleyGraph (powerGenerators g basePower), ?_⟩
  apply cayley_spectralCertificate
  · norm_num
  · norm_num
  · intro s hs
    exact (power_eigenvalue_bound g (1 / 2) (by norm_num) hg basePower s hs).trans
      base_arithmetic.2.2.2

end UniqueGamesTheorem.Foundations.PCP.Expanders

/-! Exact changes of finite vertex and port coordinates. The graph rotation and
its normalized averaging operator are transported by the same equivalences. -/

namespace UniqueGamesTheorem.Foundations.PCP.GraphTransport

open PoweringWalks SpectralReturn

variable {V W D E : Type*}

variable [Fintype V] [Fintype W] [Fintype D] [Fintype E]

omit [Fintype V] [Fintype W] in
theorem operator_reindex (G : PortGraph V D) (vertices : V ≃ W)
    (ports : D ≃ E) (f : W → ℝ) (w : W) :
    averagingOperator (reindex G vertices ports) f w =
      averagingOperator G (fun v => f (vertices v)) (vertices.symm w) := by
  unfold averagingOperator
  apply Fintype.expect_equiv ports.symm
  intro e
  rfl

/-- A coordinate change preserves the actual spectral certificate, including
the uniform measure on the port alphabet. -/
theorem reindex_spectralCertificate (G : PortGraph V D) (vertices : V ≃ W)
    (ports : D ≃ E) (lambda : ℝ) (certificate : SpectralCertificate G lambda) :
    SpectralCertificate (reindex G vertices ports) lambda where
  nonnegative := certificate.nonnegative
  lt_one := certificate.lt_one
  contraction := by
    intro f hf
    have hf' : mean (fun v => f (vertices v)) = 0 :=
      (mean_equiv vertices f).trans hf
    have h := certificate.contraction (fun v => f (vertices v)) hf'
    have hout : energy (averagingOperator (reindex G vertices ports) f) =
        energy (averagingOperator G (fun v => f (vertices v))) := by
      rw [← energy_reindex vertices]
      congr 1
      funext v
      rw [operator_reindex, vertices.symm_apply_apply]
    rw [hout, ← energy_reindex vertices f]
    exact h

end UniqueGamesTheorem.Foundations.PCP.GraphTransport

section

/-! The actual half-lazy port graph retains a Boolean stay/step flag and an
ordinary port. This supplies the concrete graph underlying Boolean-tape
length smoothing. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringLazy

open PoweringWalks SpectralReturn

variable {V D : Type*}

theorem operator_binomialMean [Fintype D] (G : PortGraph V D)
    (n : Nat) (g : Nat → V → ℝ) (v : V) :
    averagingOperator G (fun w => LazySmoothing.binomialMean n (fun k => g k w)) v =
      LazySmoothing.binomialMean n (fun k => averagingOperator G (g k) v) := by
  unfold averagingOperator LazySmoothing.binomialMean
  exact Finset.expect_comm Finset.univ Finset.univ
    (fun d tape => g (LazySmoothing.bitCount tape) (G.rot (v, d)).1)

theorem averagingOperator_lazy [Fintype D] [Nonempty D]
    (G : PortGraph V D) (f : V → ℝ) (v : V) :
    averagingOperator (lazyGraph G) f v = (f v + averagingOperator G f v) / 2 := by
  change mean (fun bd : Bool × D => f ((lazyGraph G).rot (v, bd)).1) = _
  rw [mean_prod]
  change Finset.univ.expect (fun b : Bool =>
    mean (fun d : D => f ((lazyGraph G).rot (v, (b, d))).1)) = _
  rw [LazySmoothing.expect_bool]
  simp only [lazyGraph_rot_false, lazyGraph_rot_true]
  rw [mean_const]
  rfl

/-- The exact Boolean-tape mixture for the actual lazy transition operator. -/
theorem iterate_lazy_eq_binomialMean [Fintype D] [Nonempty D]
    (G : PortGraph V D) (n : Nat) (f : V → ℝ) :
    iterateOperator (lazyGraph G) n f =
      fun v => LazySmoothing.binomialMean n (fun k => iterateOperator G k f v) := by
  induction n with
  | zero =>
    funext v
    simp [iterateOperator]
  | succ n ih =>
    funext v
    change averagingOperator (lazyGraph G) (iterateOperator (lazyGraph G) n f) v = _
    rw [ih, averagingOperator_lazy, operator_binomialMean, LazySmoothing.mean_succ]
    rfl

theorem iterate_mem_Icc [Fintype D] [Nonempty D]
    (G : PortGraph V D) (f : V → ℝ) (hf : ∀ w, f w ∈ Set.Icc (0 : ℝ) 1)
    (n : Nat) (v : V) : iterateOperator G n f v ∈ Set.Icc (0 : ℝ) 1 := by
  induction n generalizing v with
  | zero => exact hf v
  | succ n ih =>
    change mean (fun d : D => iterateOperator G n f (G.rot (v, d)).1) ∈ Set.Icc (0 : ℝ) 1
    constructor
    · exact mean_nonnegative _ (fun d => (ih ((G.rot (v, d)).1)).1)
    · calc
        mean (fun d : D => iterateOperator G n f (G.rot (v, d)).1) ≤
            mean (fun _ : D => (1 : ℝ)) :=
          mean_mono (fun d => (ih ((G.rot (v, d)).1)).2)
        _ = 1 := mean_const _

/-- The modal lower bound survives every allowed nearby actual lazy length. -/
theorem lazy_endpoint_modal_transfer [Fintype D] [Nonempty D]
    (G : PortGraph V D) (q M m : Nat) (hq : 1 ≤ q) (hM : 1 ≤ M)
    (hlo : (4 * q * M) ^ 2 - M ≤ m) (hhi : m ≤ (4 * q * M) ^ 2 + M)
    (f : V → ℝ) (hf : ∀ w, f w ∈ Set.Icc (0 : ℝ) 1) (v : V)
    (hmodal : 1 / (q : ℝ) ≤ iterateOperator (lazyGraph G) ((4 * q * M) ^ 2) f v) :
    1 / (2 * (q : ℝ)) ≤ iterateOperator (lazyGraph G) m f v := by
  rw [iterate_lazy_eq_binomialMean] at hmodal ⊢
  exact LazySmoothing.modal_transfer q M m hq hM hlo hhi
    (fun k => iterateOperator G k f v) (fun k => iterate_mem_Icc G f hf k v) hmodal

end UniqueGamesTheorem.Foundations.PCP.PoweringLazy

end

/-! Spectral contraction for the actual Boolean-flag lazy port graph. The
operator identity is proved in `PoweringLazy`; the estimate here averages the
elementary two-term square inequality. -/

namespace UniqueGamesTheorem.Foundations.PCP.LazySpectral

open PoweringWalks SpectralReturn

variable {V D : Type*}

/-- Lazification averages the input and one actual graph step, so its energy
is at most the corresponding average of the two energies. -/
theorem lazy_energy_le_average [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (f : V → ℝ) :
    energy (averagingOperator (lazyGraph G) f) ≤
      (energy f + energy (averagingOperator G f)) / 2 := by
  calc
    energy (averagingOperator (lazyGraph G) f) =
        mean (fun v => ((f v + averagingOperator G f v) / 2) ^ 2) := by
      unfold energy
      congr 1
      funext v
      rw [PoweringLazy.averagingOperator_lazy]
    _ ≤ mean (fun v => (f v ^ 2 + averagingOperator G f v ^ 2) / 2) :=
      mean_mono (fun v => half_sum_sq_le _ _)
    _ = mean (fun v => (1 / 2 : ℝ) * (f v ^ 2 + averagingOperator G f v ^ 2)) := by
      congr 1
      funext v
      ring
    _ = (1 / 2 : ℝ) * (energy f + energy (averagingOperator G f)) := by
      rw [mean_mul_left, mean_add]
      rfl
    _ = (energy f + energy (averagingOperator G f)) / 2 := by ring

/-- The concrete lazy graph inherits a squared-energy bound from an actual
certificate for its underlying graph. -/
theorem lazy_energy_bound [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (lambda : ℝ) (hG : SpectralCertificate G lambda)
    (f : V → ℝ) (hf : mean f = 0) :
    energy (averagingOperator (lazyGraph G) f) ≤
      ((1 + lambda ^ 2) / 2) * energy f := by
  calc
    energy (averagingOperator (lazyGraph G) f) ≤
        (energy f + energy (averagingOperator G f)) / 2 := lazy_energy_le_average G f
    _ ≤ (energy f + lambda ^ 2 * energy f) / 2 := by
      have h := hG.contraction f hf
      linarith
    _ = ((1 + lambda ^ 2) / 2) * energy f := by ring

/-- An actual `7/8` certificate gives the stated `31/32` certificate after
lazification: its intermediate squared-energy factor is `113/128`. -/
theorem lazy_certificate_31_32 [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (hG : SpectralCertificate G (7 / 8)) :
    SpectralCertificate (lazyGraph G) (31 / 32) where
  nonnegative := by norm_num
  lt_one := by norm_num
  contraction f hf := by
    have h := lazy_energy_bound G (7 / 8) hG f hf
    have hcoef : ((1 + (7 / 8 : ℝ) ^ 2) / 2) ≤ (31 / 32 : ℝ) ^ 2 := by norm_num
    exact h.trans (mul_le_mul_of_nonneg_right hcoef (energy_nonnegative f))

end UniqueGamesTheorem.Foundations.PCP.LazySpectral

/-! Actual finite walk averages and their operator representations.
All changes of probability coordinates come from explicit equivalences. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringReturn

open PoweringWalks SpectralReturn
open PoweringMoment (bit)

variable {V D : Type*}

theorem mean_word_cons_head [Fintype D] (n : Nat)
    (F : (Fin (n + 1) → D) → ℝ) :
    mean F = mean (fun d : D => mean (fun r : Fin n → D => F (Fin.cases d r))) := by
  calc
    mean F = mean (fun z : D × (Fin n → D) => F (Fin.cases z.1 z.2)) :=
      (mean_equiv (portConsEquiv D n) F).symm
    _ = _ := mean_prod _

theorem mean_word_cons_tail [Fintype D] (n : Nat)
    (F : (Fin (n + 1) → D) → ℝ) :
    mean F = mean (fun r : Fin n → D => mean (fun d : D => F (Fin.cases d r))) := by
  calc
    mean F = mean (fun z : (Fin n → D) × D => F (Fin.cases z.2 z.1)) :=
      (mean_equiv ((Equiv.prodComm (Fin n → D) D).trans (portConsEquiv D n)) F).symm
    _ = _ := mean_prod _

theorem iterateOperator_succ_right [Fintype D] (G : PortGraph V D)
    (n : Nat) (f : V → ℝ) :
    iterateOperator G n (averagingOperator G f) = iterateOperator G (n + 1) f := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (averagingOperator G) ih

theorem mean_wordEnd [Fintype D] [Nonempty D] (G : PortGraph V D) :
    ∀ (n : Nat) (v : V) (f : V → ℝ),
      mean (fun r : Fin n → D => f (wordEnd G n v r)) = iterateOperator G n f v := by
  intro n
  induction n with
  | zero =>
    intro v f
    change mean (fun _ : Fin 0 → D => f v) = f v
    exact mean_const _
  | succ n ih =>
    intro v f
    rw [mean_word_cons_head]
    change mean (fun d : D => mean (fun r : Fin n → D =>
      f (wordEnd G n (next G v d) r))) = _
    calc
      _ = mean (fun d : D => iterateOperator G n f (next G v d)) := by
        congr 1
        funext d
        exact ih (next G v d) f
      _ = iterateOperator G (n + 1) f v := rfl

/-- Conditional endpoint factorization at an arbitrary fixed pivot dart. -/
theorem mean_pivot_endpoints [Fintype D] [Nonempty D] (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (e : Edge V D) (φ ψ : V → ℝ),
      mean (fun r : Fin n → D =>
        φ (leftFromPivot G n k e.1 r) * ψ (rightFromPivot G n k e r)) =
        iterateOperator G k.val φ e.1 *
          iterateOperator G (n - k.val) ψ (next G e.1 e.2) := by
  intro n
  induction n with
  | zero =>
    intro k e φ ψ
    have hk : k = 0 := Fin.eq_zero k
    subst k
    change mean (fun _ : Fin 0 → D => φ e.1 * ψ (next G e.1 e.2)) =
      φ e.1 * ψ (next G e.1 e.2)
    exact mean_const _
  | succ n ih =>
    intro k e φ ψ
    refine Fin.cases ?_ (fun j => ?_) k
    · change mean (fun r : Fin (n + 1) → D =>
        φ e.1 * ψ (wordEnd G (n + 1) (next G e.1 e.2) r)) =
          φ e.1 * iterateOperator G (n + 1) ψ (next G e.1 e.2)
      rw [mean_mul_left, mean_wordEnd]
    · simp only [Fin.val_succ, Nat.add_sub_add_right]
      rw [mean_word_cons_tail]
      change mean (fun r : Fin n → D => mean (fun d : D =>
        φ (next G (leftFromPivot G n j e.1 r) d) *
          ψ (rightFromPivot G n j e r))) =
        iterateOperator G (j.val + 1) φ e.1 *
          iterateOperator G (n - j.val) ψ (next G e.1 e.2)
      calc
        _ = mean (fun r : Fin n → D =>
            averagingOperator G φ (leftFromPivot G n j e.1 r) *
              ψ (rightFromPivot G n j e r)) := by
          congr 1
          funext r
          rw [mean_mul_right]
          rfl
        _ = iterateOperator G j.val (averagingOperator G φ) e.1 *
            iterateOperator G (n - j.val) ψ (next G e.1 e.2) :=
          ih j e (averagingOperator G φ) ψ
        _ = _ := by rw [iterateOperator_succ_right]

/-- The pivot and both endpoint opinions are averaged over actual walks. -/
theorem mean_edge_endpoints [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (n : Nat) (k : Fin (n + 1)) (φ ψ : Edge V D → V → ℝ) :
    mean (fun w : Walk V D (n + 1) =>
      φ (edgeAt G n w k) w.1 * ψ (edgeAt G n w k) (endpoint G w)) =
      mean (fun e : Edge V D =>
        iterateOperator G k.val (φ e) e.1 *
          iterateOperator G (n - k.val) (ψ e) (next G e.1 e.2)) := by
  let F : Edge V D × (Fin n → D) → ℝ := fun z =>
    φ z.1 (leftFromPivot G n k z.1.1 z.2) *
      ψ z.1 (rightFromPivot G n k z.1 z.2)
  calc
    _ = mean (fun w => F (pivotEquiv G n k w)) := by
      congr 1
      funext w
      dsimp [F]
      rw [leftFromPivot_actual, rightFromPivot_actual, pivotEquiv_fst]
    _ = mean F := mean_equiv (pivotEquiv G n k) F
    _ = mean (fun e : Edge V D => mean (fun r : Fin n → D =>
        φ e (leftFromPivot G n k e.1 r) * ψ e (rightFromPivot G n k e r))) := mean_prod F
    _ = _ := by
      congr 1
      funext e
      exact mean_pivot_endpoints G n k e (φ e) (ψ e)

theorem bit_bool (b : Bool) : bit (b = true) = (if b then 1 else 0 : ℝ) := by
  cases b <;> simp [bit]

theorem mean_edge_bit [Fintype D] (bad : V × D → Bool) (v : V) :
    mean (fun d : D => bit (bad (v, d) = true)) = edgeProfile bad v := by
  simp only [bit_bool, mean, edgeProfile]

theorem mean_marked_bit [Fintype D] (G : PortGraph V D)
    (bad : V × D → Bool) (f : V → ℝ) (v : V) :
    mean (fun d : D => bit (bad (v, d) = true) * f (next G v d)) =
      markedStep G bad f v := by
  change mean (fun d : D => bit (bad (v, d) = true) * f (next G v d)) =
    mean (fun d : D => if bad (v, d) then f (next G v d) else 0)
  congr 1
  funext d
  cases bad (v, d) <;> simp [bit]

theorem edgeAt_zero (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1)) :
    edgeAt G n w 0 = (w.1, w.2 0) := by
  cases n <;> rfl

theorem word_first_hit_mean [Fintype D] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) (n : Nat) (v : V) :
    mean (fun p : Fin (n + 1) → D => bit (bad (edgeAt G n (v, p) 0) = true)) =
      edgeProfile bad v := by
  rw [mean_word_cons_head]
  simp_rw [edgeAt_zero]
  change mean (fun d : D => mean (fun _ : Fin n → D => bit (bad (v, d) = true))) = _
  calc
    _ = mean (fun d : D => bit (bad (v, d) = true)) := by simp only [mean_const]
    _ = edgeProfile bad v := mean_edge_bit bad v

theorem word_hit_mean [Fintype D] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) :
    ∀ (n : Nat) (v : V) (k : Fin (n + 1)),
      mean (fun p : Fin (n + 1) → D => bit (bad (edgeAt G n (v, p) k) = true)) =
        iterateOperator G k.val (edgeProfile bad) v := by
  intro n
  induction n with
  | zero =>
    intro v k
    have hk : k = 0 := Fin.eq_zero k
    subst k
    exact word_first_hit_mean G bad 0 v
  | succ n ih =>
    intro v k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact word_first_hit_mean G bad (n + 1) v
    · rw [mean_word_cons_head]
      change mean (fun d : D => mean (fun p : Fin (n + 1) → D =>
        bit (bad (edgeAt G n (next G v d, p) j) = true))) =
          averagingOperator G (iterateOperator G j.val (edgeProfile bad)) v
      calc
        _ = mean (fun d : D => iterateOperator G j.val (edgeProfile bad) (next G v d)) := by
          congr 1
          funext d
          exact ih (next G v d) j
        _ = _ := rfl

theorem word_pair_hit_mean [Fintype D] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) :
    ∀ (n : Nat) (v : V) (i j : Fin (n + 1)), i < j →
      mean (fun p : Fin (n + 1) → D =>
        bit (bad (edgeAt G n (v, p) i) = true) *
          bit (bad (edgeAt G n (v, p) j) = true)) =
        iterateOperator G i.val (markedStep G bad
          (iterateOperator G (j.val - i.val - 1) (edgeProfile bad))) v := by
  intro n
  induction n with
  | zero =>
    intro v i j hij
    have hi : i = 0 := Fin.eq_zero i
    have hj : j = 0 := Fin.eq_zero j
    subst i
    subst j
    exact ((lt_irrefl _) hij).elim
  | succ n ih =>
    intro v i
    refine Fin.cases ?_ (fun a => ?_) i
    · intro j
      refine Fin.cases ?_ (fun b => ?_) j
      · intro hij
        exact ((lt_irrefl _) hij).elim
      · intro _hij
        simp only [Fin.val_zero, Fin.val_succ, Nat.sub_zero, Nat.add_sub_cancel]
        rw [mean_word_cons_head]
        change mean (fun d : D => mean (fun p : Fin (n + 1) → D =>
          bit (bad (v, d) = true) * bit (bad (edgeAt G n (next G v d, p) b) = true))) =
          markedStep G bad (iterateOperator G b.val (edgeProfile bad)) v
        calc
          _ = mean (fun d : D => bit (bad (v, d) = true) *
              iterateOperator G b.val (edgeProfile bad) (next G v d)) := by
            congr 1
            funext d
            rw [mean_mul_left, word_hit_mean]
          _ = _ := mean_marked_bit G bad _ v
    · intro j
      refine Fin.cases ?_ (fun b => ?_) j
      · intro hij
        exact (Nat.not_lt_zero _ hij).elim
      · intro hij
        have hab : a < b := Nat.lt_of_succ_lt_succ hij
        simp only [Fin.val_succ, Nat.add_sub_add_right]
        rw [mean_word_cons_head]
        change mean (fun d : D => mean (fun p : Fin (n + 1) → D =>
          bit (bad (edgeAt G n (next G v d, p) a) = true) *
            bit (bad (edgeAt G n (next G v d, p) b) = true))) =
          averagingOperator G (iterateOperator G a.val (markedStep G bad
            (iterateOperator G (b.val - a.val - 1) (edgeProfile bad)))) v
        calc
          _ = mean (fun d : D => iterateOperator G a.val (markedStep G bad
              (iterateOperator G (b.val - a.val - 1) (edgeProfile bad))) (next G v d)) := by
            congr 1
            funext d
            exact ih (next G v d) a b hab
          _ = _ := rfl

theorem hit_mean [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) (n : Nat) (k : Fin (n + 1)) :
    mean (fun w : Walk V D (n + 1) => bit (bad (edgeAt G n w k) = true)) =
      edgeDensity bad := by
  calc
    _ = mean (fun v : V => mean (fun p : Fin (n + 1) → D =>
        bit (bad (edgeAt G n (v, p) k) = true))) :=
      mean_prod (A := V) (B := Fin (n + 1) → D)
        (fun w => bit (bad (edgeAt G n w k) = true))
    _ = mean (iterateOperator G k.val (edgeProfile bad)) := by
      congr 1
      funext v
      exact word_hit_mean G bad n v k
    _ = mean (edgeProfile bad) := mean_iterate G k.val _
    _ = _ := rfl

theorem pair_hit_mean [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) (n : Nat)
    (i j : Fin (n + 1)) (hij : i < j) :
    mean (fun w : Walk V D (n + 1) => bit (bad (edgeAt G n w i) = true) *
      bit (bad (edgeAt G n w j) = true)) = returnMass G bad (j.val - i.val - 1) := by
  calc
    _ = mean (fun v : V => mean (fun p : Fin (n + 1) → D =>
        bit (bad (edgeAt G n (v, p) i) = true) *
          bit (bad (edgeAt G n (v, p) j) = true))) :=
      mean_prod (A := V) (B := Fin (n + 1) → D)
        (fun w => bit (bad (edgeAt G n w i) = true) *
          bit (bad (edgeAt G n w j) = true))
    _ = mean (iterateOperator G i.val (markedStep G bad
        (iterateOperator G (j.val - i.val - 1) (edgeProfile bad)))) := by
      congr 1
      funext v
      exact word_pair_hit_mean G bad n v i j hij
    _ = mean (markedStep G bad
        (iterateOperator G (j.val - i.val - 1) (edgeProfile bad))) := mean_iterate G i.val _
    _ = _ := rfl

theorem pair_event_mean [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) (n : Nat)
    (i j : Fin (n + 1)) (hij : i < j) :
    mean (fun w : Walk V D (n + 1) =>
      bit (bad (edgeAt G n w i) = true ∧ bad (edgeAt G n w j) = true)) =
        returnMass G bad (j.val - i.val - 1) := by
  simpa only [PoweringMoment.bit_mul] using pair_hit_mean G bad n i j hij

end UniqueGamesTheorem.Foundations.PCP.PoweringReturn

/-! The second moment of the actual marked-edge count in a consecutive walk
window. Pair events are reduced to the checked spectral return operator. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringMomentBound

open scoped BigOperators
open PoweringWalks SpectralReturn PoweringReturn
open PoweringMoment (bit hits)

theorem symmetric_gap_matrix_sum (ε : ℝ) (r : Nat → ℝ) :
    ∀ (m : Nat) (f : Fin m → Fin m → ℝ),
      (∀ i j, f i j = f j i) → (∀ i, f i i = ε) →
      (∀ i j, i.val < j.val → f i j = r (j.val - i.val - 1)) →
      (∑ i, ∑ j, f i j) = (m : ℝ) * ε +
        2 * ∑ j ∈ Finset.range m, ∑ gap ∈ Finset.range j, r gap := by
  intro m
  induction m with
  | zero => intro f _hSym _hDiag _hUpper; simp
  | succ m ih =>
    intro f hSym hDiag hUpper
    have hOld : (∑ i : Fin m, ∑ j : Fin m, f i.castSucc j.castSucc) =
        (m : ℝ) * ε + 2 * ∑ j ∈ Finset.range m, ∑ gap ∈ Finset.range j, r gap := by
      apply ih (fun i j => f i.castSucc j.castSucc)
      · intro i j; exact hSym i.castSucc j.castSucc
      · intro i; exact hDiag i.castSucc
      · intro i j hij; exact hUpper i.castSucc j.castSucc hij
    have hLast : (∑ i : Fin m, f i.castSucc (Fin.last m)) =
        ∑ gap ∈ Finset.range m, r gap := by
      calc
        _ = ∑ i : Fin m, r (m - 1 - i.val) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hUpper i.castSucc (Fin.last m) i.isLt]
          simp only [Fin.val_last, Fin.val_castSucc]
          congr 1
          omega
        _ = ∑ i ∈ Finset.range m, r (m - 1 - i) :=
          Fin.sum_univ_eq_sum_range (fun i => r (m - 1 - i)) m
        _ = _ := Finset.sum_range_reflect r m
    have hLastRow : (∑ j : Fin m, f (Fin.last m) j.castSucc) =
        ∑ gap ∈ Finset.range m, r gap := by
      calc
        _ = ∑ j : Fin m, f j.castSucc (Fin.last m) := by
          apply Finset.sum_congr rfl
          intro j _
          exact hSym (Fin.last m) j.castSucc
        _ = _ := hLast
    calc
      (∑ i, ∑ j, f i j) =
          (∑ i : Fin m, ∑ j : Fin m, f i.castSucc j.castSucc) +
            (∑ i : Fin m, f i.castSucc (Fin.last m)) +
            (∑ j : Fin m, f (Fin.last m) j.castSucc) + f (Fin.last m) (Fin.last m) := by
        simp only [Fin.sum_univ_castSucc, Finset.sum_add_distrib]
        ring
      _ = (m : ℝ) * ε +
          2 * (∑ j ∈ Finset.range m, ∑ gap ∈ Finset.range j, r gap) +
          (∑ gap ∈ Finset.range m, r gap) + (∑ gap ∈ Finset.range m, r gap) + ε := by
        rw [hOld, hLast, hLastRow, hDiag]
      _ = ((m + 1 : Nat) : ℝ) * ε +
          2 * ∑ j ∈ Finset.range (m + 1), ∑ gap ∈ Finset.range j, r gap := by
        rw [Finset.sum_range_succ]
        simp only [Nat.cast_add, Nat.cast_one]
        ring

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]

def windowEvent (G : PortGraph V D) (bad : V × D → Bool)
    (n start m : Nat) (h : start + m ≤ n + 1) (i : Fin m) (w : Walk V D (n + 1)) : Prop :=
  bad (edgeAt G n w (windowIndex n start m h i)) = true

theorem window_second_moment_eq (G : PortGraph V D) (bad : V × D → Bool)
    (n start m : Nat) (h : start + m ≤ n + 1) :
    mean (fun w => hits (windowEvent G bad n start m h) w ^ 2) =
      (m : ℝ) * edgeDensity bad +
        2 * ∑ j ∈ Finset.range m, ∑ gap ∈ Finset.range j, returnMass G bad gap := by
  rw [show mean (fun w => hits (windowEvent G bad n start m h) w ^ 2) =
      ∑ i, ∑ j, mean (fun w => bit (windowEvent G bad n start m h i w ∧
        windowEvent G bad n start m h j w)) from
    PoweringMoment.second_moment_eq (windowEvent G bad n start m h)]
  apply symmetric_gap_matrix_sum
  · intro i j
    congr 1
    funext w
    simp only [and_comm]
  · intro i
    simp only [and_self]
    exact hit_mean G bad n (windowIndex n start m h i)
  · intro i j hij
    have hwin : windowIndex n start m h i < windowIndex n start m h j :=
      Nat.add_lt_add_left hij start
    have hp := pair_event_mean G bad n (windowIndex n start m h i)
      (windowIndex n start m h j) hwin
    simpa only [windowEvent, windowIndex, Nat.add_sub_add_left] using hp

/-- All moment terms come from actual walk events; the only analytic input
is the stated spectral contraction certificate of the given graph. -/
theorem window_second_moment_le (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate G lambda) (bad : V × D → Bool)
    (reversal : ∀ e, bad (G.rot e) = bad e)
    (n start m : Nat) (h : start + m ≤ n + 1) :
    mean (fun w => hits (windowEvent G bad n start m h) w ^ 2) ≤
      (m : ℝ) * edgeDensity bad *
        (1 + 2 / (1 - lambda) + ((m : ℝ) - 1) * edgeDensity bad) := by
  rw [window_second_moment_eq]
  exact secondMoment_return_envelope G lambda certificate bad reversal m

end UniqueGamesTheorem.Foundations.PCP.PoweringMomentBound

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PoweringOpinionsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Actual local-label opinions, modal decoding at the reference length, and
its proved persistence at nearby lazy-walk lengths. -/

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.PoweringOpinions

open PoweringWalks PoweringLabels SpectralReturn
open PoweringMoment (bit)

variable {V D A : Type*}

/-- Outside the full-radius neighborhood a fixed fallback makes the opinion
function total. Actual tested path vertices will be certified inside it. -/
def opinionAt (G : PortGraph V D) (t : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u v : V) : A := by
  classical
  exact if h : ∃ n, n ≤ t ∧ ∃ p : Fin n → D, wordEnd G n v p = u then
    decode (selectors v) (labels v) ⟨u, h⟩ else fallback

theorem opinionAt_eq_decode (G : PortGraph V D) (t : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (v : V) (u : Ball G t v) :
    opinionAt G t selectors labels fallback u.val v = decode (selectors v) (labels v) u := by
  classical
  simp [opinionAt, u.property]
  rfl

def honestLabels (G : PortGraph V D) (t : Nat) (assignment : V → A) :
    V → PaddedLabel D t A := fun v => encode G t v (fun u => assignment u.val)

variable [Fintype D] [Nonempty D] [Fintype A] [Nonempty A]

def sampleOpinion (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u : V) (p : Fin N → D) : A :=
  opinionAt G t selectors labels fallback u (wordEnd G N u p)

def decoded (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u : V) : A :=
  PoweringDecoding.mode (sampleOpinion G t N selectors labels fallback u)

def matchFn (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u v : V) : ℝ :=
  bit (opinionAt G t selectors labels fallback u v = decoded G t N selectors labels fallback u)

omit [Nonempty D] in
theorem matchFn_mem_Icc (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u v : V) :
    matchFn G t N selectors labels fallback u v ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  constructor
  · exact PoweringMoment.bit_nonneg _
  · unfold matchFn bit
    split <;> simp

/-- The reference-length modal lower bound is proved from actual port samples. -/
theorem decoded_modal_baseline (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u : V) :
    1 / (Fintype.card A : ℝ) ≤
      iterateOperator G N (matchFn G t N selectors labels fallback u) u := by
  have h := PoweringDecoding.mode_mass_lower (sampleOpinion G t N selectors labels fallback u)
  change 1 / (Fintype.card A : ℝ) ≤ mean (fun p : Fin N → D =>
    matchFn G t N selectors labels fallback u (wordEnd G N u p)) at h
  rwa [PoweringReturn.mean_wordEnd] at h

end UniqueGamesTheorem.Foundations.PCP.PoweringOpinions

end

end

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

open PoweringWalks PoweringLabels PoweringReach PoweringOpinions

variable {V D A : Type*}

/-- The base port predicates packaged as a constraint graph. -/
def baseGraph (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b) :
    ConstraintGraph V (Edge V D) A where
  reverse := G.rot
  reverse_involutive := G.rot_involutive
  tail := Prod.fst
  accepts := accepts
  reverse_accepts := reverse_accepts

theorem pathAccepts_eq_true_iff (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (w : Walk V D (n + 1)) (a b : PaddedLabel D (n + 1) A) :
    pathAccepts G accepts n selectors w a b = true ↔
      ∀ k : Fin (n + 1),
        accepts (edgeAt G n w k)
          (decode (selectors w.1) a (tailFromStart G n w k))
          (decode (selectors (endpoint G w)) b (headFromEnd G n w k)) = true := by
  simp [pathAccepts]

/-- Both directed copies evaluate the same original-start/original-end path
test. Uniformly doubling the darts therefore introduces no change of event. -/
theorem poweredGraph_edgeSatisfied (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A)
    (direction : Bool) (w : Walk V D (n + 1)) :
    (poweredGraph G accepts n selectors).edgeSatisfied labels (direction, w) =
      pathAccepts G accepts n selectors w (labels w.1) (labels (endpoint G w)) := by
  cases direction <;> rfl

/-- The actual directed-dart rejection average is exactly the recorded-walk
rejection average. Only the orientation-bit average is removed, so the vertex
type and the walk type are allowed to be empty. -/
theorem rejection_mean_eq_path_mean [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) :
    SpectralReturn.mean (fun d : Dart V D n => PoweringMoment.bit
      ((poweredGraph G accepts n selectors).edgeSatisfied labels d = false)) =
      SpectralReturn.mean (fun w : Walk V D (n + 1) => PoweringMoment.bit
        (pathAccepts G accepts n selectors w (labels w.1) (labels (endpoint G w)) = false)) := by
  rw [SpectralReturn.mean_prod]
  simp only [poweredGraph_edgeSatisfied, SpectralReturn.mean_const]

theorem pathAccepts_honest (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (assignment : V → A)
    (satisfies : ∀ e, accepts e (assignment e.1) (assignment (G.rot e).1) = true)
    (w : Walk V D (n + 1)) :
    pathAccepts G accepts n selectors w
      (honestLabels G (n + 1) assignment w.1)
      (honestLabels G (n + 1) assignment (endpoint G w)) = true := by
  apply (pathAccepts_eq_true_iff G accepts n selectors w _ _).2
  intro k
  simpa only [honestLabels, decode_encode, tailFromStart_val, headFromEnd_val] using
    satisfies (edgeAt G n w k)

/-- Perfect completeness for the actual powered graph and its common alphabet. -/
theorem perfect_completeness (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (assignment : V → A)
    (satisfies : ∀ e, accepts e (assignment e.1) (assignment (G.rot e).1) = true) :
    ∀ d, (poweredGraph G accepts n selectors).edgeSatisfied
      (honestLabels G (n + 1) assignment) d = true := by
  rintro ⟨direction, w⟩
  rw [poweredGraph_edgeSatisfied]
  exact pathAccepts_honest G accepts n selectors assignment satisfies w

theorem preserves_satisfiability (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (h : (baseGraph G accepts reverse_accepts).Satisfiable) :
    (poweredGraph G accepts n selectors).Satisfiable := by
  obtain ⟨assignment, satisfies⟩ := h
  refine ⟨honestLabels G (n + 1) assignment, ?_⟩
  apply perfect_completeness G accepts n selectors assignment
  intro e
  exact satisfies e

/-- Badness is computed from the actual base predicate and the decoded labels. -/
def decodedBad (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (assignment : V → A) (e : Edge V D) : Bool :=
  !(accepts e (assignment e.1) (assignment (G.rot e).1))

theorem decodedBad_eq_true_iff (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (assignment : V → A) (e : Edge V D) :
    decodedBad G accepts assignment e = true ↔
      accepts e (assignment e.1) (assignment (G.rot e).1) = false := by
  simp [decodedBad]

/-- The base reversal law makes the decoded bad-edge event rotor-invariant. -/
theorem decodedBad_rot (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (assignment : V → A) (e : Edge V D) :
    decodedBad G accepts assignment (G.rot e) = decodedBad G accepts assignment e := by
  have h := congrArg Bool.not
    (reverse_accepts e (assignment e.1) (assignment (G.rot e).1))
  simpa only [decodedBad, G.rot_involutive e] using h

/-- A bad decoded edge with matching opinions at its two true endpoints. -/
noncomputable def witness (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A)
    (assignment : V → A) (w : Walk V D (n + 1)) (k : Fin (n + 1)) : Prop :=
  decodedBad G accepts assignment (edgeAt G n w k) = true ∧
    opinionAt G (n + 1) selectors labels fallback (edgeAt G n w k).1 w.1 =
      assignment (edgeAt G n w k).1 ∧
    opinionAt G (n + 1) selectors labels fallback
      (G.rot (edgeAt G n w k)).1 (endpoint G w) =
        assignment (G.rot (edgeAt G n w k)).1

/-- The witness forces failure of the actual kth checked path constraint.
The opinion/decode identities use the genuine reach certificates. -/
theorem witness_implies_path_rejection (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A)
    (assignment : V → A) (w : Walk V D (n + 1)) (k : Fin (n + 1))
    (h : witness G accepts n selectors labels fallback assignment w k) :
    pathAccepts G accepts n selectors w (labels w.1) (labels (endpoint G w)) = false := by
  obtain ⟨hBad, hTail, hHead⟩ := h
  have hTailDecode :
      decode (selectors w.1) (labels w.1) (tailFromStart G n w k) =
        assignment (edgeAt G n w k).1 :=
    (opinionAt_eq_decode G (n + 1) selectors labels fallback w.1
      (tailFromStart G n w k)).symm.trans hTail
  have hHeadDecode :
      decode (selectors (endpoint G w)) (labels (endpoint G w))
          (headFromEnd G n w k) = assignment (G.rot (edgeAt G n w k)).1 :=
    (opinionAt_eq_decode G (n + 1) selectors labels fallback (endpoint G w)
      (headFromEnd G n w k)).symm.trans hHead
  have hFalse := (decodedBad_eq_true_iff G accepts assignment (edgeAt G n w k)).1 hBad
  cases hPath : pathAccepts G accepts n selectors w
      (labels w.1) (labels (endpoint G w)) with
  | false => rfl
  | true =>
      have hChecked := (pathAccepts_eq_true_iff G accepts n selectors w _ _).1 hPath k
      rw [hTailDecode, hHeadDecode, hFalse] at hChecked
      exact False.elim (Bool.noConfusion hChecked)

end UniqueGamesTheorem.Foundations.PCP.PoweringTest

end

section

/-!
# Actual rejection counts and sizes for the powering construction

Normalized rejection averages are the cardinal ratios of the corresponding
rejected-dart sets. These identities include empty finite types. Positivity
of the dart cardinality is required only when translating inequalities by
division. The powered dart count and common alphabet size are computed from
their actual product and function types.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringCounting

open PoweringWalks PoweringLabels PoweringTest
open scoped BigOperators

variable {V D A E : Type*}

/-- An arbitrary constraint graph's rejection probability is its actual
rejected-dart cardinal ratio, including the empty-dart case. -/
theorem constraint_rejection_mean_eq_count [Fintype E]
    (H : ConstraintGraph V E A) (labels : V → A) :
    SpectralReturn.mean (fun e : E => PoweringMoment.bit
      (H.edgeSatisfied labels e = false)) =
      (H.rejectionCount labels : ℝ) / (Fintype.card E : ℝ) := by
  classical
  rw [SpectralReturn.mean_eq_sum_div_card]
  simp only [PoweringMoment.bit, ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts]
  apply congrArg (fun x : ℝ => x / (Fintype.card E : ℝ))
  convert (Finset.sum_boole (R := ℝ)
    (fun e => H.edgeSatisfied labels e = false) Finset.univ) using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : H.edgeSatisfied labels e = false <;> simp [h]

/-- Multiplying a normalized lower bound by the actual positive dart count. -/
theorem constraint_rejection_lower_iff [Fintype E]
    (H : ConstraintGraph V E A) (labels : V → A)
    (hcard : 0 < Fintype.card E) (ε : ℝ) :
    ε ≤ SpectralReturn.mean (fun e : E => PoweringMoment.bit
      (H.edgeSatisfied labels e = false)) ↔
      ε * (Fintype.card E : ℝ) ≤ (H.rejectionCount labels : ℝ) := by
  rw [constraint_rejection_mean_eq_count]
  exact le_div_iff₀ (Nat.cast_pos.mpr hcard)

/-- The edge-profile definition equals its actual directed-edge indicator
mean without any nonemptiness assumption on vertices or ports. -/
theorem edgeDensity_eq_bit_mean [Fintype V] [Fintype D]
    (bad : Edge V D → Bool) :
    SpectralReturn.edgeDensity bad =
      SpectralReturn.mean (fun e : Edge V D => PoweringMoment.bit (bad e = true)) := by
  convert (SpectralReturn.mean_prod
    (fun e : Edge V D => PoweringMoment.bit (bad e = true))).symm using 1
  all_goals try with_reducible_and_instances rfl
  change SpectralReturn.mean (fun v => SpectralReturn.mean
    (fun d => if bad (v, d) then (1 : ℝ) else 0)) = _
  apply congrArg SpectralReturn.mean
  funext v
  apply congrArg SpectralReturn.mean
  funext d
  cases bad (v, d) <;> simp [PoweringMoment.bit]

/-- Decoded badness is exactly rejection in the actual base constraint graph. -/
theorem base_edgeDensity_eq_rejection_count [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (assignment : V → A) :
    SpectralReturn.edgeDensity (decodedBad G accepts assignment) =
      ((baseGraph G accepts reverse_accepts).rejectionCount assignment : ℝ) /
        (Fintype.card (Edge V D) : ℝ) := by
  calc
    _ = SpectralReturn.mean (fun e : Edge V D => PoweringMoment.bit
        (decodedBad G accepts assignment e = true)) := edgeDensity_eq_bit_mean _
    _ = SpectralReturn.mean (fun e : Edge V D => PoweringMoment.bit
        ((baseGraph G accepts reverse_accepts).edgeSatisfied assignment e = false)) := by
      apply congrArg SpectralReturn.mean
      funext e
      exact congrArg PoweringMoment.bit
        (propext (decodedBad_eq_true_iff G accepts assignment e))
    _ = _ := constraint_rejection_mean_eq_count _ _

theorem base_count_lower_to_density [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (assignment : V → A) (hcard : 0 < Fintype.card (Edge V D)) (ε : ℝ)
    (hcount : ε * (Fintype.card (Edge V D) : ℝ) ≤
      ((baseGraph G accepts reverse_accepts).rejectionCount assignment : ℝ)) :
    ε ≤ SpectralReturn.edgeDensity (decodedBad G accepts assignment) := by
  rw [base_edgeDensity_eq_rejection_count G accepts reverse_accepts assignment]
  exact (le_div_iff₀ (Nat.cast_pos.mpr hcard)).2 hcount

end UniqueGamesTheorem.Foundations.PCP.PoweringCounting

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_CloudRoundingLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finiteBall _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
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

def mismatchSet (G : ConstraintGraph V E A) (ell : E → A) (rounded : V → A) :
    Finset E :=
  Finset.univ.filter (fun e => ell e ≠ rounded (G.tail e))

def copiedRejectionCount (G : ConstraintGraph V E A) (ell : E → A) : Nat :=
  (Finset.univ.filter (fun e => G.accepts e (ell e) (ell (G.reverse e)) = false)).card

def innerDisagreementSet (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) : Finset (E × D) :=
  Finset.univ.filter (fun ed => ell ed.1 ≠ ell (innerRotation G H ed).1)

noncomputable def roundLabels [Nonempty A]
    (G : ConstraintGraph V E A) (ell : E → A) : V → A :=
  fun v => majority (fun e : Cloud G v => ell e.val)

/-- Every changed dart belongs to precisely one tail fiber. -/
def mismatchFiberEquiv (G : ConstraintGraph V E A) (ell : E → A)
    (rounded : V → A) :
    (Σ v, ↥(minoritySet (fun e : Cloud G v => ell e.val) (rounded v))) ≃
      ↥(mismatchSet G ell rounded) where
  toFun := by
    rintro ⟨v, ⟨⟨e, he⟩, hbad⟩⟩
    cases he
    exact ⟨e, by simpa [mismatchSet, minoritySet] using hbad⟩
  invFun e :=
    ⟨G.tail e.val, ⟨⟨e.val, rfl⟩, by
      simpa [mismatchSet, minoritySet] using e.property⟩⟩
  left_inv := by
    rintro ⟨v, ⟨⟨e, he⟩, hbad⟩⟩
    cases he
    rfl
  right_inv := by intro e; apply Subtype.ext; rfl

omit [Fintype A] [DecidableEq E] in
theorem mismatch_card_eq_sum (G : ConstraintGraph V E A) (ell : E → A)
    (rounded : V → A) :
    (mismatchSet G ell rounded).card =
      ∑ v, (minoritySet (fun e : Cloud G v => ell e.val) (rounded v)).card := by
  have h := Fintype.card_congr (mismatchFiberEquiv G ell rounded)
  simpa only [Fintype.card_sigma, Fintype.card_coe] using h.symm

/-- A cloud disagreement is the same actual internal dart in global coordinates. -/
def disagreementFiberEquiv (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) :
    (Σ v, ↥(disagreementSet (fun e : Cloud G v => ell e.val)
      (fun ed => ((H v).rot ed).1))) ≃ ↥(innerDisagreementSet G H ell) where
  toFun := by
    rintro ⟨v, ⟨⟨⟨e, he⟩, d⟩, hbad⟩⟩
    cases he
    refine ⟨(e, d), ?_⟩
    simpa [disagreementSet, innerDisagreementSet, innerRotation,
      cloudIndexEquiv, cloudRotation] using hbad
  invFun := by
    rintro ⟨⟨e, d⟩, hbad⟩
    refine ⟨G.tail e, ⟨(⟨e, rfl⟩, d), ?_⟩⟩
    simpa [disagreementSet, innerDisagreementSet, innerRotation,
      cloudIndexEquiv, cloudRotation] using hbad
  left_inv := by
    rintro ⟨v, ⟨⟨⟨e, he⟩, d⟩, hbad⟩⟩
    cases he
    rfl
  right_inv := by intro ed; apply Subtype.ext; rfl

omit [Fintype A] [DecidableEq E] in
theorem disagreement_card_eq_sum (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) :
    (innerDisagreementSet G H ell).card =
      ∑ v, (disagreementSet (fun e : Cloud G v => ell e.val)
        (fun ed => ((H v).rot ed).1)).card := by
  have h := Fintype.card_congr (disagreementFiberEquiv G H ell)
  simpa only [Fintype.card_sigma, Fintype.card_coe] using h.symm

/-- No uniform cloud-size hypothesis occurs in this finite sum. -/
theorem rounded_mismatch_expansion [Nonempty A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (ell : E → A) (h : ℚ)
    (expansion : ∀ v (S : Finset (Cloud G v)),
      S.card ≤ Fintype.card (Cloud G v) / 2 →
      h * (S.card : ℚ) ≤ ((directedCut (fun ed => ((H v).rot ed).1) S).card : ℚ)) :
    h * ((mismatchSet G ell (roundLabels G ell)).card : ℚ) ≤
      ((innerDisagreementSet G H ell).card : ℚ) := by
  rw [mismatch_card_eq_sum, disagreement_card_eq_sum, Nat.cast_sum, Nat.cast_sum,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  exact minority_expansion_bound (fun e : Cloud G v => ell e.val)
    (fun ed => ((H v).rot ed).1) (roundLabels G ell v) h
    (majority_maximal (fun e : Cloud G v => ell e.val)) (expansion v)

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq E] in
theorem rounded_endpoint_bound (G : ConstraintGraph V E A)
    (ell : E → A) (rounded : V → A) :
    G.rejectionCount rounded ≤ copiedRejectionCount G ell +
      2 * (mismatchSet G ell rounded).card :=
  dart_rejection_count_le G.tail G.reverse G.accepts ell rounded

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq E] in
/-- Exact rejection count for arbitrary copied labels, including cloud violations. -/
theorem replacement_rejection_split (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) :
    (replacementGraph G H).rejectionCount ell =
      copiedRejectionCount G ell + (innerDisagreementSet G H ell).card := by
  classical
  simp only [rejectionCount_eq_sum, Fintype.sum_prod_type, Fintype.sum_sum_type,
    copied_satisfied_inl, copied_satisfied_inr, decide_eq_false_iff_not,
    Fintype.sum_unique, Finset.sum_add_distrib]
  simp only [copiedRejectionCount, innerDisagreementSet, Finset.card_eq_sum_ones,
    Finset.sum_filter, Fintype.sum_prod_type]
  exact Nat.add_comm _ _

/-- Directed expansion by two pays for both changed endpoints exactly. -/
theorem replacement_soundness [Nonempty A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (expansion : ∀ v (S : Finset (Cloud G v)),
      S.card ≤ Fintype.card (Cloud G v) / 2 →
      2 * S.card ≤ (directedCut (fun ed => ((H v).rot ed).1) S).card)
    (ell : E → A) :
    G.rejectionCount (roundLabels G ell) ≤ (replacementGraph G H).rejectionCount ell := by
  have hc := rounded_mismatch_expansion G H ell 2 (by
    intro v S hS
    exact_mod_cast expansion v S hS)
  have hcNat : 2 * (mismatchSet G ell (roundLabels G ell)).card ≤
      (innerDisagreementSet G H ell).card := by exact_mod_cast hc
  rw [replacement_rejection_split]
  exact (rounded_endpoint_bound G ell (roundLabels G ell)).trans
    (Nat.add_le_add_left hcNat _)

/-- Padding changes the normalization, but never the rounded absolute rejection count. -/
theorem padded_replacement_soundness [Nonempty A]
    (G : ConstraintGraph V E A) (dummy : V → Type*) [∀ v, Fintype (dummy v)]
    [∀ v, DecidableEq (dummy v)]
    (H : ∀ v, PortGraph (Cloud (paddedGraph G dummy) v) D)
    (expansion : ∀ v (S : Finset (Cloud (paddedGraph G dummy) v)),
      S.card ≤ Fintype.card (Cloud (paddedGraph G dummy) v) / 2 →
      2 * S.card ≤ (directedCut (fun ed => ((H v).rot ed).1) S).card)
    (ell : PaddedDart G dummy → A) :
    G.rejectionCount (roundLabels (paddedGraph G dummy) ell) ≤
      (paddedReplacementGraph G dummy H).rejectionCount ell := by
  simpa only [paddedReplacementGraph, padded_rejectionCount] using
    replacement_soundness (paddedGraph G dummy) H expansion ell

end GraphRounding

end UniqueGamesTheorem.Foundations.PCP.CloudRounding

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PoweringOpinionTables
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
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

theorem firstIndex_matches (p : X → Prop) [DecidablePred p]
    (xs : List X) (h : ∃ a ∈ xs, p a) : p (xs.get (firstIndex p xs h)) := by
  rw [get_firstIndex]
  exact (scanWitness p xs h).property

/-- Every earlier stored address fails the matching predicate. -/
theorem firstIndex_is_first (p : X → Prop) [DecidablePred p] :
    ∀ (xs : List X) (h : ∃ a ∈ xs, p a) (j : Fin xs.length),
      j.val < (firstIndex p xs h).val → ¬p (xs.get j) := by
  intro xs
  induction xs with
  | nil => intro h; simp at h
  | cons a xs ih =>
    intro h j
    by_cases ha : p a
    · simp [firstIndex, ha]
    · refine Fin.cases (by intro _; exact ha) (fun i => ?_) j
      intro hi
      apply ih (match_in_tail p h ha) i
      exact Nat.lt_of_succ_lt_succ (by
        simpa only [firstIndex, ha, dite_false, Fin.val_succ] using hi)

variable {vertices d : Nat}

/-- Evaluate an already stored row vector by finite label lookups. The only
quantified type is the bounded set of walk positions. -/
def rowsAccepts {n : Nat} (accepts : Edge (Fin vertices) (Fin d) → A → A → Bool)
    (rows : WalkRows vertices d n) (a b : LabelTable d (n + 1) A) : Bool :=
  decide (∀ k : Fin (n + 1), accepts rows[k].edge a[rows[k].tailIndex]
    b[rows[k].headIndex] = true)

/-- The stored finite lookup predicate implements the actual powering test. -/
theorem rowsAccepts_walkRows (G : PortGraph (Fin vertices) (Fin d))
    (accepts : Edge (Fin vertices) (Fin d) → A → A → Bool) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1))
    (a b : PaddedLabel (Fin d) (n + 1) A) :
    rowsAccepts accepts (walkRows G n w) (labelTable a) (labelTable b) =
      PoweringTest.pathAccepts G accepts n (finitePortSelector G (n + 1)) w a b := by
  apply Bool.eq_iff_iff.mpr
  simp only [rowsAccepts, decide_eq_true_iff, PoweringTest.pathAccepts_eq_true_iff,
    walkRows_edge, walkRows_tail_value, walkRows_head_value]

end UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables

end

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

open PoweringWalks PoweringLabels PoweringAddresses PoweringReach PoweringRowData
open UniqueGamesTheorem.Foundations.Complexity PoweringMachineRow

variable {V D : Type*}

def addressPorts {d t : Nat} (i : PoweringOpinionTables.AddressIndex d t) : List (Fin d) :=
  List.ofFn ((allAddresses d t).get i).2

theorem addressPorts_length_le {d t : Nat} (i : PoweringOpinionTables.AddressIndex d t) :
    (addressPorts i).length ≤ t := by
  simp only [addressPorts, List.length_ofFn]
  exact Nat.le_of_lt_succ ((allAddresses d t).get i).1.isLt

end UniqueGamesTheorem.Foundations.PCP.PoweringFieldPlan

/-! Exact tail and reverse-index fields of the actual powering-table rows.
The reverse address is affine in the live starting vertex; the coefficient
and offset depend only on the fixed degree, word, and orientation. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringRowHeaderSemantics

open PoweringWalks PoweringEnumeration
open UniqueGamesTheorem.Foundations.Complexity

variable {vertices d : Nat}

def reverseOffset (d n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) : Nat :=
  2 * (wordEquiv d (n + 1) ports).val + (if direction then 0 else 1)

def reverseValue (d n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) : Nat :=
  blockSize d n * vertex.val + reverseOffset d n ports direction

end UniqueGamesTheorem.Foundations.PCP.PoweringRowHeaderSemantics

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PoweringTableSemanticsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
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

namespace UniqueGamesTheorem.Foundations.PCP.PoweringTableSemantics

open PoweringWalks PoweringLabels PoweringAddresses PoweringEnumeration PoweringTables

abbrev RawLabeling (vertices d n : Nat) :=
  Fin vertices → PaddedLabel (Fin d) (n + 1) (Fin 64)

end UniqueGamesTheorem.Foundations.PCP.PoweringTableSemantics

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
namespace UniqueGamesTheorem.Foundations.PCP.SpectralCut

open scoped BigOperators
open PoweringWalks SpectralReturn

section Indicators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mean_indicator (S : Finset V) :
    mean (indicator S) = (S.card : ℝ) / (Fintype.card V : ℝ) := by
  have hf : Finset.univ.filter (fun v : V => v ∈ S) = S := by
    ext v
    simp
  rw [mean_eq_sum_div_card]
  simp only [indicator, Finset.sum_boole, hf]

theorem energy_indicator (S : Finset V) : energy (indicator S) = mean (indicator S) := by
  unfold energy
  congr 1
  funext v
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

namespace UniqueGamesTheorem.Foundations.PCP.UniformRestriction

open scoped BigOperators

variable {B : Type*} (p : B → Prop)

variable [DecidablePred p]

variable [Fintype B] [DecidableEq B]

/-- Uniform full tapes induce exactly uniform legal-coordinate tapes. -/
theorem expect_restrict (h : ({b // p b} → Bool) → ℝ) :
    (𝔼 f : B → Bool, h (restrict p f)) = 𝔼 g : {b // p b} → Bool, h g := by
  calc
    (𝔼 f : B → Bool, h (restrict p f)) =
        𝔼 g : ({b // p b} → Bool) × ({b // ¬ p b} → Bool), h g.1 :=
      Fintype.expect_equiv (Equiv.piEquivPiSubtypeProd p (fun _ => Bool))
        _ _ (fun _ => rfl)
    _ = 𝔼 g : {b // p b} → Bool, 𝔼 _k : {b // ¬ p b} → Bool, h g := by
      simpa only [Finset.univ_product_univ] using
        Finset.expect_product
          (Finset.univ : Finset ({b // p b} → Bool))
          (Finset.univ : Finset ({b // ¬ p b} → Bool))
          (fun g : ({b // p b} → Bool) × ({b // ¬ p b} → Bool) => h g.1)
    _ = 𝔼 g : {b // p b} → Bool, h g := by
      simp only [Fintype.expect_const]

end UniqueGamesTheorem.Foundations.PCP.UniformRestriction

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_AlphabetGraphLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Relations.repeatedConsistentDecidable _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

def edgeOracle (G : ConstraintGraph V E A) (assignment : Address V E A → Bool) (e : E) :
    Cube (AlphabetReduction.LegalPair (G.accepts e)) → Bool :=
  fun tape => assignment (.inr (e, extendTape G e tape))

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem oracleAnswer_globalize (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) (e : E)
    (x : AlphabetReduction.InputCoordinate A ⊕ Cube (AlphabetReduction.LegalPair (G.accepts e))) :
    assignment (globalizeQuery G e x) =
      AssignmentTester.oracleAnswer
        (CodeComposition.pairWord (vertexBlock assignment (G.tail e))
          (vertexBlock assignment (G.head e))) (edgeOracle G assignment e) x := by
  rcases x with ⟨side, tape⟩ | tape
  · cases side <;> rfl
  · rfl

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem response_eq_local (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) (e : E) (kind : Fin 4)
    (k : AlphabetReduction.InputCoordinate A) (f g r₀ r₁ r₂ : Cube (A × A)) :
    QueryIncidence.response (verifier G) assignment (e, kind, k, f, g, r₀, r₁, r₂) =
      fun slot => AssignmentTester.oracleAnswer
        (CodeComposition.pairWord (vertexBlock assignment (G.tail e))
          (vertexBlock assignment (G.head e))) (edgeOracle G assignment e)
        (AssignmentTester.eventQueries (AlphabetReduction.pairEncoding (G.accepts e)) kind k
          (restrictTape G e f) (restrictTape G e g) (restrictTape G e r₀)
          (restrictTape G e r₁) (restrictTape G e r₂) slot) := by
  funext slot
  exact oracleAnswer_globalize G assignment e _

def eventReject (G : ConstraintGraph V E A) (assignment : Address V E A → Bool)
    (event : Event E A) : ℝ :=
  AssignmentTester.truth (!((verifier G).accepts event (QueryIncidence.response (verifier G) assignment event)))

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem eventReject_eq_local (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) (e : E) (kind : Fin 4)
    (k : AlphabetReduction.InputCoordinate A) (f g r₀ r₁ r₂ : Cube (A × A)) :
    eventReject G assignment (e, kind, k, f, g, r₀, r₁, r₂) =
      AssignmentTester.eventReject (AlphabetReduction.pairEncoding (G.accepts e))
        (CodeComposition.pairWord (vertexBlock assignment (G.tail e))
          (vertexBlock assignment (G.head e))) (edgeOracle G assignment e) kind k
        (restrictTape G e f) (restrictTape G e g) (restrictTape G e r₀)
        (restrictTape G e r₁) (restrictTape G e r₂) := by
  unfold eventReject
  rw [response_eq_local]
  rfl

def localAverage (G : ConstraintGraph V E A) (assignment : Address V E A → Bool)
    (e : E) : ℝ := 𝔼 sample : LocalEvent A, eventReject G assignment (e, sample)

/-- Iterating the checked one-tape restriction identity preserves independence. -/
theorem expect_restrict_five {B : Type*} [Fintype B] [DecidableEq B]
    (p : B → Prop) [DecidablePred p]
    (h : ({b // p b} → Bool) → ({b // p b} → Bool) → ({b // p b} → Bool) →
      ({b // p b} → Bool) → ({b // p b} → Bool) → ℝ) :
    (𝔼 f : B → Bool, 𝔼 g : B → Bool, 𝔼 r₀ : B → Bool,
      𝔼 r₁ : B → Bool, 𝔼 r₂ : B → Bool,
        h (UniformRestriction.restrict p f) (UniformRestriction.restrict p g)
          (UniformRestriction.restrict p r₀) (UniformRestriction.restrict p r₁)
          (UniformRestriction.restrict p r₂)) =
    𝔼 f : {b // p b} → Bool, 𝔼 g : {b // p b} → Bool,
      𝔼 r₀ : {b // p b} → Bool, 𝔼 r₁ : {b // p b} → Bool,
        𝔼 r₂ : {b // p b} → Bool, h f g r₀ r₁ r₂ := by
  rw [UniformRestriction.expect_restrict p
    (fun f => 𝔼 g : B → Bool, 𝔼 r₀ : B → Bool, 𝔼 r₁ : B → Bool,
      𝔼 r₂ : B → Bool, h f (UniformRestriction.restrict p g)
        (UniformRestriction.restrict p r₀) (UniformRestriction.restrict p r₁)
        (UniformRestriction.restrict p r₂))]
  apply Finset.expect_congr rfl
  intro f _
  rw [UniformRestriction.expect_restrict p
    (fun g => 𝔼 r₀ : B → Bool, 𝔼 r₁ : B → Bool, 𝔼 r₂ : B → Bool,
      h f g (UniformRestriction.restrict p r₀) (UniformRestriction.restrict p r₁)
        (UniformRestriction.restrict p r₂))]
  apply Finset.expect_congr rfl
  intro g _
  rw [UniformRestriction.expect_restrict p
    (fun r₀ => 𝔼 r₁ : B → Bool, 𝔼 r₂ : B → Bool,
      h f g r₀ (UniformRestriction.restrict p r₁) (UniformRestriction.restrict p r₂))]
  apply Finset.expect_congr rfl
  intro r₀ _
  rw [UniformRestriction.expect_restrict p
    (fun r₁ => 𝔼 r₂ : B → Bool, h f g r₀ r₁ (UniformRestriction.restrict p r₂))]
  apply Finset.expect_congr rfl
  intro r₁ _
  exact UniformRestriction.expect_restrict p (h f g r₀ r₁)

omit [Nonempty A] in
/-- Five independent full tapes restrict to five independent uniform legal tapes. -/
theorem localAverage_eq_tester (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) (e : E) :
    localAverage G assignment e = AlphabetReduction.edgeTesterReject (G.accepts e)
      (vertexBlock assignment (G.tail e)) (vertexBlock assignment (G.head e))
      (edgeOracle G assignment e) := by
  unfold localAverage AlphabetReduction.edgeTesterReject AssignmentTester.explicitTesterReject
  simp only [LocalEvent, expect_prod, eventReject_eq_local, restrictTape]
  apply Finset.expect_congr rfl
  intro kind _
  apply Finset.expect_congr rfl
  intro side _
  apply Finset.expect_congr rfl
  intro tape _
  exact expect_restrict_five (legal G e)
    (AssignmentTester.eventReject (AlphabetReduction.pairEncoding (G.accepts e))
      (CodeComposition.pairWord (vertexBlock assignment (G.tail e))
        (vertexBlock assignment (G.head e))) (edgeOracle G assignment e) kind (side, tape))

def average [Fintype E] (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) : ℝ :=
  𝔼 event : Event E A, eventReject G assignment event

def decodedLabeling (assignment : Address V E A → Bool) : V → A :=
  fun v => CodeComposition.nearest (vertexBlock assignment v)

theorem local_gap (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) (e : E) :
    AssignmentTester.truth (!(G.edgeSatisfied (decodedLabeling assignment) e)) / 2048 ≤
      localAverage G assignment e := by
  cases h : G.edgeSatisfied (decodedLabeling assignment) e with
  | false =>
      rw [localAverage_eq_tester]
      simpa [AssignmentTester.truth] using
        AlphabetReduction.rejected_edge_tester_bound (G.accepts e)
          (vertexBlock assignment (G.tail e)) (vertexBlock assignment (G.head e))
          (edgeOracle G assignment e) h
  | true =>
      simp only [Bool.not_true, AssignmentTester.truth, Bool.false_eq_true, ite_false, zero_div]
      apply Finset.expect_nonneg
      intro sample _
      exact AssignmentTester.truth_nonneg _

theorem average_gap [Fintype E] (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) :
    (𝔼 e : E, AssignmentTester.truth (!(G.edgeSatisfied (decodedLabeling assignment) e))) / 2048 ≤
      average G assignment := by
  unfold average
  rw [expect_prod, Finset.expect_div]
  exact Finset.expect_le_expect (fun e _ => local_gap G assignment e)

omit [Nonempty A] in
theorem average_eq_count [Fintype E] (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) :
    average G assignment = (QueryIncidence.verifierRejectionCount (verifier G) assignment : ℝ) /
      Fintype.card (Event E A) :=
  expect_rejection_eq_count _

/-- The actual event count has a uniform loss of 2048, with no edge-dependent
sample multiplicities. This count statement also permits an empty dart type. -/
theorem rejection_count_bound [Fintype E] (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) :
    Fintype.card (LocalEvent A) * G.rejectionCount (decodedLabeling assignment) ≤
      2048 * QueryIncidence.verifierRejectionCount (verifier G) assignment := by
  classical
  cases isEmpty_or_nonempty E with
  | inl empty =>
      let := empty
      simp [ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts]
  | inr inhabited =>
      let := inhabited
      have h := average_gap G assignment
      rw [average_eq_count, expect_rejection_eq_count, card_event, Nat.cast_mul,
        div_div] at h
      have he : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
      have hl : (0 : ℝ) < Fintype.card (LocalEvent A) := by
        exact_mod_cast Fintype.card_pos
      have hc := (div_le_div_iff₀ (mul_pos he (by norm_num)) (mul_pos he hl)).mp h
      have hc' :
          ((Fintype.card (LocalEvent A) : ℝ) *
            (G.rejectionCount (decodedLabeling assignment) : ℝ)) * Fintype.card E ≤
          (2048 * (QueryIncidence.verifierRejectionCount (verifier G) assignment : ℝ)) * Fintype.card E := by
        simpa only [ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts,
          mul_assoc, mul_comm, mul_left_comm] using hc
      have result := (mul_le_mul_iff_left₀ he).mp hc'
      exact_mod_cast result

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem honest_edgeOracle (G : ConstraintGraph V E A) (labeling : V → A) (e : E)
    (h : G.edgeSatisfied labeling e = true) :
    edgeOracle G (honestAssignment G labeling) e =
      fun tape => tape ⟨(labeling (G.tail e), labeling (G.head e)), h⟩ := by
  funext tape
  exact UniformRestriction.extend_apply_of_mem (legal G e) tape
    (labeling (G.tail e), labeling (G.head e)) h

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem honest_event (G : ConstraintGraph V E A) (labeling : V → A)
    (satisfied : ∀ e, G.edgeSatisfied labeling e = true) (event : Event E A) :
    (verifier G).accepts event (QueryIncidence.response (verifier G) (honestAssignment G labeling) event) =
      true := by
  rcases event with ⟨e, kind, k, f, g, r₀, r₁, r₂⟩
  rw [response_eq_local, honest_edgeOracle G labeling e (satisfied e)]
  simp only [honest_vertexBlock]
  exact AssignmentTester.event_perfect_completeness (AlphabetReduction.pairEncoding (G.accepts e))
    ⟨(labeling (G.tail e), labeling (G.head e)), satisfied e⟩ kind k
    (restrictTape G e f) (restrictTape G e g) (restrictTape G e r₀)
    (restrictTape G e r₁) (restrictTape G e r₂)

omit [DecidableEq A] [Nonempty A] in
theorem perfect_completeness [DecidableEq V] [DecidableEq E] (G : ConstraintGraph V E A)
    (satisfied : G.Satisfiable) : (graph G).Satisfiable := by
  obtain ⟨labeling, h⟩ := satisfied
  exact QueryIncidence.satisfiable_of_verifier_satisfiable (verifier G) (by omega)
    ⟨honestAssignment G labeling, honest_event G labeling h⟩

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

abbrev OutputVertex (V E A : Type*) :=
  QueryIncidence.Vertex (AlphabetGraph.Event E A) (AlphabetGraph.Address V E A)

abbrev OutputDart (E A : Type*) := QueryIncidence.Dart (AlphabetGraph.Event E A) 6

variable {V E A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

/-- Real gaps transfer without rational approximation, including an empty
old dart type. The loss is exactly `2048 * 6 = 12288`. -/
theorem gap_transfer_real [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : ConstraintGraph V E A) (eps : ℝ) (_eps_nonnegative : 0 ≤ eps)
    (source : ∀ labeling : V → A,
      eps * (Fintype.card E : ℝ) ≤ (G.rejectionCount labeling : ℝ))
    (labeling : OutputVertex V E A → QueryIncidence.Label 6) :
    (eps / 12288) * (Fintype.card (OutputDart E A) : ℝ) ≤
      ((AlphabetGraph.graph G).rejectionCount labeling : ℝ) := by
  let assignment := QueryIncidence.decodedAssignment (by decide : 0 < 6) labeling
  have htest :
      (Fintype.card (AlphabetGraph.LocalEvent A) : ℝ) *
          (G.rejectionCount (AlphabetGraph.decodedLabeling assignment) : ℝ) ≤
        2048 * (QueryIncidence.verifierRejectionCount (AlphabetGraph.verifier G) assignment : ℝ) := by
    exact_mod_cast AlphabetGraph.rejection_count_bound G assignment
  have hinc :
      2 * (QueryIncidence.verifierRejectionCount (AlphabetGraph.verifier G) assignment : ℝ) ≤
        ((AlphabetGraph.graph G).rejectionCount labeling : ℝ) := by
    exact_mod_cast QueryIncidence.rejection_count_bound
      (AlphabetGraph.verifier G) (by decide : 0 < 6) labeling
  have hscaled :
      eps * (Fintype.card E : ℝ) * (Fintype.card (AlphabetGraph.LocalEvent A) : ℝ) ≤
        2048 * (QueryIncidence.verifierRejectionCount (AlphabetGraph.verifier G) assignment : ℝ) := by
    calc
      _ = (Fintype.card (AlphabetGraph.LocalEvent A) : ℝ) *
          (eps * (Fintype.card E : ℝ)) := by ring
      _ ≤ (Fintype.card (AlphabetGraph.LocalEvent A) : ℝ) *
          (G.rejectionCount (AlphabetGraph.decodedLabeling assignment) : ℝ) :=
        mul_le_mul_of_nonneg_left (source (AlphabetGraph.decodedLabeling assignment))
          (Nat.cast_nonneg _)
      _ ≤ _ := htest
  change (eps / 12288) *
    (Fintype.card (QueryIncidence.Dart (AlphabetGraph.Event E A) 6) : ℝ) ≤ _
  rw [QueryIncidence.card_dart, AlphabetGraph.card_event]
  push_cast
  nlinarith

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

theorem dartEquiv_reverse_val (m q : Nat)
    (event : AlphabetGraph.Event (Fin m) (Fin q)) (slot : Fin 6) (orientation : Bool) :
    (dartEquiv m q (QueryIncidence.reverse ((event, slot), orientation))).val =
      (eventEquiv m q event).val * 12 + slot.val * 2 + bitValue (!orientation) :=
  dartEquiv_val m q event slot (!orientation)

theorem ordered_trans_finCongr {A : Type*} {a b : Nat}
    (order : A ≃ Fin a) (sameCount : a = b) :
    ordered (order.trans (finCongr sameCount)) = ordered order := by
  cases sameCount
  rfl

/-- Product enumeration visits the right factor completely at each left index. -/
theorem ordered_product {A B : Type*} {a b : Nat}
    (left : A ≃ Fin a) (right : B ≃ Fin b) :
    ordered (productEquiv left right) =
      (ordered left).flatMap (fun x => (ordered right).map (fun y => (x, y))) := by
  have atIndex (i : Fin a) (j : Fin b) (h : i.val * b + j.val < a * b) :
      (productEquiv left right).symm ⟨i.val * b + j.val, h⟩ =
        (left.symm i, right.symm j) := by
    have same : (⟨i.val * b + j.val, h⟩ : Fin (a * b)) = finProdFinEquiv (i, j) := by
      apply Fin.ext
      simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
    rw [same]
    simp [productEquiv]
  unfold ordered
  rw [List.ofFn_mul]
  simp only [atIndex, List.flatMap_def, List.map_ofFn, Function.comp_def]

theorem ordered_event (m q : Nat) :
    ordered (eventEquiv m q) =
      (List.finRange m).flatMap (fun edge => (localEvents q).map (fun event => (edge, event))) := by
  change ordered (productEquiv (Equiv.refl (Fin m)) (localEventEquiv q)) = _
  rw [ordered_product, ordered_refl]
  rfl

/-- Exact serialized occurrence order, including both orientations and every
repeated local query: edge, local event, slot, then false and true. -/
theorem ordered_dart (m q : Nat) :
    ordered (dartEquiv m q) =
      (List.finRange m).flatMap (fun edge =>
        (localEvents q).flatMap (fun event =>
          (List.finRange 6).flatMap (fun slot =>
            [(((edge, event), slot), false), (((edge, event), slot), true)]))) := by
  rw [dartEquiv]
  erw [ordered_trans_finCongr]
  rw [ordered_product, ordered_product, ordered_event]
  simp only [ordered_refl, ordered_bool, List.flatMap_assoc, List.flatMap_map,
    List.map_cons, List.map_nil]

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_AlphabetTableBoundsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.VerifierToCNF

open Target

theorem chainView_sound (bits ys : List Bool)
    (size : bits.length = ys.length + 3)
    (accepted : (chainView bits ys).all tripleValue = true) : bits.any id = true := by
  induction ys generalizing bits with
  | nil =>
    match bits with
    | [a, b, c] => simpa [chainView, tripleValue, Bool.or_assoc] using accepted
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
      have accepted' : tripleValue (a, b, y) = true ∧
          (chainView ((!y) :: rest) ys).all tripleValue = true := by
        simpa only [chainView, List.all_cons, Bool.and_eq_true] using accepted
      have tailAccepted := ih ((!y) :: rest) smaller accepted'.2
      cases a <;> cases b <;> cases y <;> simp_all [tripleValue]

theorem fillBits_correct (bits : List Bool) (size : 3 ≤ bits.length) :
    (chainView bits (fillBits bits)).all tripleValue = true ↔ bits.any id = true := by
  match bits with
  | [] => simp at size
  | [_] => simp at size
  | [_, _] => simp at size
  | [a, b, c] => simp [fillBits, chainView, tripleValue, Bool.or_assoc]
  | a :: b :: c :: d :: rest =>
    have ih := fillBits_correct ((a || b) :: c :: d :: rest) (by simp)
    have tautology : tripleValue (a, b, !(a || b)) = true := by
      cases a <;> cases b <;> rfl
    rw [fillBits]
    simp only [chainView, List.all_cons, Bool.not_not]
    rw [tautology]
    simp only [Bool.true_and]
    simpa [Bool.or_assoc] using ih
termination_by bits.length
decreasing_by simp_wf

theorem chainView_failed (bits ys : List Bool)
    (size : bits.length = ys.length + 3) (failed : bits.any id = false) :
    1 ≤ ((chainView bits ys).map tripleValue).count false := by
  by_contra none
  have zero : ((chainView bits ys).map tripleValue).count false = 0 := by omega
  have all := (zero_false_count_iff_all _).mp zero
  have accepted : (chainView bits ys).all tripleValue = true := by
    simpa only [List.all_map, Function.comp_def, id_eq] using all
  have impossible := chainView_sound bits ys size accepted
  rw [failed] at impossible
  contradiction

theorem mem_patterns (q : Nat) (p : Pattern q) : p ∈ patterns q := by
  induction q with
  | zero =>
    have h : p = Fin.elim0 := by funext i; exact Fin.elim0 i
    simp [patterns, h]
  | succ q ih =>
    let tail : Pattern q := fun i => p i.succ
    have htail : tail ∈ patterns q := ih tail
    have prefixEquality : Fin.cases (p 0) tail = p := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    apply List.mem_flatMap.mpr
    refine ⟨tail, htail, ?_⟩
    cases h : p 0 with
    | false =>
      have hp : Fin.cases false tail = p := by simpa only [h] using prefixEquality
      exact List.mem_cons.mpr (Or.inl hp.symm)
    | true =>
      have hp : Fin.cases true tail = p := by simpa only [h] using prefixEquality
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl hp.symm)))

theorem patternAt_surjective (q : Nat) (bits : Pattern q) :
    ∃ p : PatternIndex q, patternAt q p = bits := by
  obtain ⟨i, hi, h⟩ := List.getElem_of_mem (mem_patterns q bits)
  exact ⟨⟨i, hi⟩, h⟩

def eventValue {q : Nat} (V : FiniteVerifier q) (A : Fin V.variables → Bool)
    (e : Fin V.events) : Bool := V.accepts e (fun i => A (V.query e i))

def rejectedEventCount {q : Nat} (V : FiniteVerifier q) (A : Fin V.variables → Bool) : Nat :=
  ((List.finRange V.events).map (eventValue V A)).count false

end UniqueGamesTheorem.Foundations.PCP.VerifierToCNF

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_FinalBooleanVerifier
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.FinalBooleanVerifier

open Target

variable {V E : Type*} {n m : Nat}

@[simp] theorem bitsOfLabels_labelsOfBits (vertices : V ≃ Fin n)
    (assignment : Fin (n * 6) → Bool) : bitsOfLabels vertices (labelsOfBits vertices assignment) = assignment := by
  funext k
  simp only [bitsOfLabels, labelsOfBits, bitIndex, Equiv.apply_symm_apply, Prod.eta]

theorem all_satisfied_of_rejectionCount_zero [Fintype E] (G : ConstraintGraph V E Label)
    (labeling : V → Label) (zero : G.rejectionCount labeling = 0) :
    ∀ e, G.edgeSatisfied labeling e = true := by
  intro e
  cases h : G.edgeSatisfied labeling e with
  | true => rfl
  | false =>
    have member : e ∈ G.rejectedDarts labeling := (G.mem_rejectedDarts labeling e).mpr h
    have positive : 0 < G.rejectionCount labeling := Finset.card_pos.mpr ⟨e, member⟩
    omega

end UniqueGamesTheorem.Foundations.PCP.FinalBooleanVerifier

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_ZigzagGraphsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

/-! ## Exact averaging operators -/

noncomputable section

/-- Average only the inner cloud coordinate, keeping the outer vertex fixed. -/
def cloudOperator [Fintype E] (H : PortGraph D E) (f : V × D → ℝ) (x : V × D) : ℝ :=
  SpectralReturn.mean (fun e => f (x.1, (H.rot (x.2, e)).1))

/-- The permutation on cloud vertices induced by the actual outer rotation. -/
def graphPermutation (G : PortGraph V D) (f : V × D → ℝ) (x : V × D) : ℝ :=
  f (G.rot x)

/-- Uniform averaging on the graph square is two original averaging steps. -/
theorem averagingOperator_square [Fintype D] (G : PortGraph V D) (f : V → ℝ) :
    SpectralReturn.averagingOperator (square G) f =
      SpectralReturn.averagingOperator G (SpectralReturn.averagingOperator G f) := by
  funext v
  let w : D × D → ℝ := fun ds => f (G.rot ((G.rot (v, ds.1)).1, ds.2)).1
  change SpectralReturn.mean w =
    SpectralReturn.mean (fun d₁ => SpectralReturn.mean (fun d₂ => w (d₁, d₂)))
  exact SpectralReturn.mean_prod w

/-- The zigzag operator is precisely inner average, outer permutation, inner
average. This factorization follows from the actual rotation formula. -/
theorem averagingOperator_zigzag [Fintype E] (G : PortGraph V D)
    (H : PortGraph D E) (f : V × D → ℝ) :
    SpectralReturn.averagingOperator (zigzag G H) f =
      cloudOperator H (graphPermutation G (cloudOperator H f)) := by
  funext x
  rcases x with ⟨v, d⟩
  let w : E × E → ℝ := fun es =>
    let first := H.rot (d, es.1)
    let middle := G.rot (v, first.1)
    let last := H.rot (middle.2, es.2)
    f (middle.1, last.1)
  change SpectralReturn.mean w =
    SpectralReturn.mean (fun e₁ => SpectralReturn.mean (fun e₂ => w (e₁, e₂)))
  exact SpectralReturn.mean_prod w

end

end UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs

end

section

/-!
# Energy contraction for the actual zigzag graph

The proof splits a function into its cloud average and its cloud-centered
part. All operators are the actual graph averages from `ZigzagGraphs`.
-/

namespace UniqueGamesTheorem.Foundations.PCP.ZigzagSpectral

open PoweringWalks SpectralReturn ZigzagGraphs

noncomputable section

variable {V D E : Type*}

def cloudMean [Fintype D] (f : V × D → ℝ) (v : V) : ℝ :=
  mean (fun d => f (v, d))

def projection [Fintype D] (f : V × D → ℝ) : V × D → ℝ :=
  liftCloud (cloudMean f)

def centered [Fintype D] (f : V × D → ℝ) : V × D → ℝ := f - projection f

theorem mean_liftCloud [Fintype V] [Fintype D] [Nonempty D] (f : V → ℝ) :
    mean (liftCloud (D := D) f) = mean f := by
  change mean (fun x : V × D => f x.1) = mean f
  rw [mean_prod]
  simp only [mean_const]

theorem energy_liftCloud [Fintype V] [Fintype D] [Nonempty D] (f : V → ℝ) :
    energy (liftCloud (D := D) f) = energy f :=
  mean_liftCloud (D := D) (fun v => f v ^ 2)

theorem mean_cloudMean [Fintype V] [Fintype D] (f : V × D → ℝ) :
    mean (cloudMean f) = mean f := (mean_prod f).symm

theorem energy_prod [Fintype V] [Fintype D] (f : V × D → ℝ) :
    energy f = mean (fun v => energy (fun d => f (v, d))) :=
  mean_prod (fun x => f x ^ 2)

theorem cloudMean_centered_zero [Fintype D] [Nonempty D]
    (f : V × D → ℝ) (v : V) : cloudMean (centered f) v = 0 := by
  change mean (fun d => f (v, d) - cloudMean f v) = 0
  rw [mean_sub, mean_const]
  exact sub_self _

theorem energy_centered_eq_sub [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy (centered f) = energy f - energy (projection f) := by
  have hpoint (v : V) : energy (fun d => centered f (v, d)) =
      energy (fun d => f (v, d)) - (cloudMean f v) ^ 2 := by
    change energy (fun d => f (v, d) - cloudMean f v) = _
    rw [energy_sub_const]
    change energy (fun d => f (v, d)) - 2 * cloudMean f v * cloudMean f v +
      (cloudMean f v) ^ 2 = _
    ring
  have hproj : energy (projection f) = energy (cloudMean f) := energy_liftCloud _
  calc
    energy (centered f) = mean (fun v => energy (fun d => centered f (v, d))) :=
      energy_prod _
    _ = mean (fun v => energy (fun d => f (v, d)) - (cloudMean f v) ^ 2) := by
      congr 1
      funext v
      exact hpoint v
    _ = mean (fun v => energy (fun d => f (v, d))) -
        mean (fun v => (cloudMean f v) ^ 2) := mean_sub _ _
    _ = energy f - energy (projection f) := by
      rw [← energy_prod f, hproj]
      rfl

theorem projection_energy_decomposition [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy f = energy (projection f) + energy (centered f) := by
  rw [energy_centered_eq_sub]
  ring

theorem energy_centered_le [Fintype V] [Fintype D] [Nonempty D]
    (f : V × D → ℝ) : energy (centered f) ≤ energy f := by
  rw [energy_centered_eq_sub]
  exact sub_le_self _ (energy_nonnegative _)

/-- Squared normalized mean is bounded by normalized squared energy. -/
theorem mean_sq_le_energy {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) :
    mean f ^ 2 ≤ energy f := by
  have h := correlation_sq_le f (fun _ => 1)
  simpa [correlation, energy] using h

/-- Every actual reversible regular graph average is an energy contraction. -/
theorem averaging_energy_le [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
    (G : PortGraph V D) (f : V → ℝ) : energy (averagingOperator G f) ≤ energy f := by
  calc
    energy (averagingOperator G f) ≤ mean (averagingOperator G (fun v => f v ^ 2)) := by
      apply mean_mono
      intro v
      exact mean_sq_le_energy (fun d => f (G.rot (v, d)).1)
    _ = energy f := mean_operator G _

theorem cloudOperator_add [Fintype E] (H : PortGraph D E) (f g : V × D → ℝ) :
    cloudOperator H (f + g) = cloudOperator H f + cloudOperator H g := by
  funext x
  exact mean_add _ _

theorem cloudOperator_sub [Fintype E] (H : PortGraph D E) (f g : V × D → ℝ) :
    cloudOperator H (f - g) = cloudOperator H f - cloudOperator H g := by
  funext x
  exact mean_sub _ _

theorem cloudOperator_projection [Fintype D] [Fintype E] [Nonempty E]
    (H : PortGraph D E) (f : V × D → ℝ) : cloudOperator H (projection f) = projection f := by
  funext x
  change mean (fun _ : E => cloudMean f x.1) = cloudMean f x.1
  exact mean_const _

theorem cloudOperator_centered [Fintype D] [Fintype E] [Nonempty E]
    (H : PortGraph D E) (f : V × D → ℝ) :
    cloudOperator H (centered f) = cloudOperator H f - projection f := by
  unfold centered
  rw [cloudOperator_sub, cloudOperator_projection]

theorem graphPermutation_energy [Fintype V] [Fintype D] (G : PortGraph V D)
    (f : V × D → ℝ) : energy (graphPermutation G f) = energy f :=
  mean_equiv G.rot (fun x => f x ^ 2)

theorem cloud_energy_le [Fintype V] [Fintype D] [Fintype E]
    [Nonempty D] [Nonempty E] (H : PortGraph D E) (f : V × D → ℝ) :
    energy (cloudOperator H f) ≤ energy f := by
  calc
    energy (cloudOperator H f) =
        mean (fun v => energy (averagingOperator H (fun d => f (v, d)))) := energy_prod _
    _ ≤ mean (fun v => energy (fun d => f (v, d))) :=
      mean_mono (fun v => averaging_energy_le H _)
    _ = energy f := (energy_prod f).symm

theorem cloud_centered_contraction [Fintype V] [Fintype D] [Fintype E]
    (H : PortGraph D E) (lambda : ℝ) (hH : SpectralCertificate H lambda)
    (f : V × D → ℝ) (hzero : ∀ v, cloudMean f v = 0) :
    energy (cloudOperator H f) ≤ lambda ^ 2 * energy f := by
  calc
    energy (cloudOperator H f) =
        mean (fun v => energy (averagingOperator H (fun d => f (v, d)))) := energy_prod _
    _ ≤ mean (fun v => lambda ^ 2 * energy (fun d => f (v, d))) :=
      mean_mono (fun v => hH.contraction _ (hzero v))
    _ = lambda ^ 2 * mean (fun v => energy (fun d => f (v, d))) := mean_mul_left _ _
    _ = lambda ^ 2 * energy f := by rw [← energy_prod f]

theorem cloud_residual_bound [Fintype V] [Fintype D] [Fintype E]
    [Nonempty D] [Nonempty E] (H : PortGraph D E) (lambda : ℝ)
    (hH : SpectralCertificate H lambda) (f : V × D → ℝ) :
    energy (cloudOperator H f - projection f) ≤ lambda ^ 2 * energy f := by
  rw [← cloudOperator_centered H f]
  exact (cloud_centered_contraction H lambda hH (centered f)
    (cloudMean_centered_zero f)).trans
      (mul_le_mul_of_nonneg_left (energy_centered_le f) (sq_nonneg lambda))

/-- Cloud projection of the outer permutation is the genuine outer graph
average when its input is constant on each cloud. -/
theorem projection_graphPermutation_projection [Fintype D] (G : PortGraph V D)
    (f : V × D → ℝ) :
    projection (graphPermutation G (projection f)) =
      liftCloud (averagingOperator G (cloudMean f)) := rfl

theorem projected_outer_bound [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (lambda : ℝ) (hG : SpectralCertificate G lambda)
    (f : V × D → ℝ) (hf : mean f = 0) :
    energy (projection (graphPermutation G (projection f))) ≤
      lambda ^ 2 * energy (projection f) := by
  have hzero : mean (cloudMean f) = 0 := (mean_cloudMean f).trans hf
  have hleft : energy (projection (graphPermutation G (projection f))) =
      energy (averagingOperator G (cloudMean f)) := by
    rw [projection_graphPermutation_projection]
    exact energy_liftCloud _
  have hright : energy (projection f) = energy (cloudMean f) := energy_liftCloud _
  rw [hleft, hright]
  exact hG.contraction _ hzero

theorem energy_add_three_le {A : Type*} [Fintype A] (a b c : A → ℝ) :
    energy (a + b + c) ≤ 3 * (energy a + energy b + energy c) := by
  calc
    energy (a + b + c) ≤ mean (fun x => 3 * (a x ^ 2 + b x ^ 2 + c x ^ 2)) := by
      apply mean_mono
      intro x
      change (a x + b x + c x) ^ 2 ≤ 3 * (a x ^ 2 + b x ^ 2 + c x ^ 2)
      nlinarith [sq_nonneg (a x - b x), sq_nonneg (a x - c x), sq_nonneg (b x - c x)]
    _ = 3 * (energy a + energy b + energy c) := by
      rw [mean_mul_left, mean_add, mean_add]
      rfl

/-- A deliberately loose bound sufficient for the expander iteration. -/
theorem zigzag_energy_bound [Fintype V] [Fintype D] [Fintype E]
    [Nonempty D] [Nonempty E]
    (G : PortGraph V D) (H : PortGraph D E) (lambdaG lambdaH : ℝ)
    (hG : SpectralCertificate G lambdaG) (hH : SpectralCertificate H lambdaH)
    (f : V × D → ℝ) (hf : mean f = 0) :
    energy (averagingOperator (zigzag G H) f) ≤
      3 * (lambdaG ^ 2 + lambdaH ^ 2) * energy f := by
  let u := projection f
  let v := centered f
  let a := projection (graphPermutation G u)
  let b := cloudOperator H (graphPermutation G u) - a
  let c := cloudOperator H (graphPermutation G (cloudOperator H v))
  have hfactor : averagingOperator (zigzag G H) f = a + b + c := by
    rw [averagingOperator_zigzag]
    have hf' : f = u + v := by
      funext x
      change f x = projection f x + (f x - projection f x)
      ring
    have hbu : cloudOperator H u = u := cloudOperator_projection H f
    have hbf : cloudOperator H f = u + cloudOperator H v := by
      rw [hf', cloudOperator_add, hbu]
    rw [hbf]
    have hp : graphPermutation G (u + cloudOperator H v) =
        graphPermutation G u + graphPermutation G (cloudOperator H v) := rfl
    rw [hp, cloudOperator_add]
    change cloudOperator H (graphPermutation G u) + c =
      a + (cloudOperator H (graphPermutation G u) - a) + c
    funext x
    change cloudOperator H (graphPermutation G u) x + c x =
      a x + (cloudOperator H (graphPermutation G u) x - a x) + c x
    ring
  have ha : energy a ≤ lambdaG ^ 2 * energy u := projected_outer_bound G lambdaG hG f hf
  have hb : energy b ≤ lambdaH ^ 2 * energy u := by
    have h := cloud_residual_bound H lambdaH hH (graphPermutation G u)
    simpa only [graphPermutation_energy] using h
  have hc : energy c ≤ lambdaH ^ 2 * energy v := by
    calc
      energy c ≤ energy (graphPermutation G (cloudOperator H v)) := cloud_energy_le H _
      _ = energy (cloudOperator H v) := graphPermutation_energy G _
      _ ≤ lambdaH ^ 2 * energy v :=
        cloud_centered_contraction H lambdaH hH v (cloudMean_centered_zero f)
  rw [hfactor]
  calc
    energy (a + b + c) ≤ 3 * (energy a + energy b + energy c) := energy_add_three_le _ _ _
    _ ≤ 3 * (lambdaG ^ 2 * energy u + lambdaH ^ 2 * energy u + lambdaH ^ 2 * energy v) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add ha hb) hc) (by norm_num)
    _ ≤ 3 * (lambdaG ^ 2 + lambdaH ^ 2) * energy f := by
      have hdecomp : energy f = energy u + energy v := projection_energy_decomposition f
      rw [hdecomp]
      have hn := mul_nonneg (sq_nonneg lambdaG) (energy_nonnegative v)
      nlinarith

theorem square_certificate [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
    (G : PortGraph V D) (lambda : ℝ) (hG : SpectralCertificate G lambda) :
    SpectralCertificate (square G) (lambda ^ 2) where
  nonnegative := sq_nonneg lambda
  lt_one := by
    have hprod := mul_pos (sub_pos.mpr hG.lt_one)
      (show 0 < 1 + lambda by linarith [hG.nonnegative])
    nlinarith
  contraction f hf := by
    rw [averagingOperator_square]
    calc
      energy (averagingOperator G (averagingOperator G f)) ≤
          lambda ^ 2 * energy (averagingOperator G f) :=
        hG.contraction _ ((mean_operator G f).trans hf)
      _ ≤ lambda ^ 2 * (lambda ^ 2 * energy f) :=
        mul_le_mul_of_nonneg_left (hG.contraction f hf) (sq_nonneg lambda)
      _ = (lambda ^ 2) ^ 2 * energy f := by ring

/-- Squaring an outer graph with certificate `1/2`, then zigzagging with an
inner graph with certificate `1/100`, again has certificate `1/2`. -/
theorem square_zigzag_halfCertificate [Fintype V] [Fintype D] [Fintype E]
    [Nonempty V] [Nonempty D] [Nonempty E]
    (G : PortGraph V D) (H : PortGraph (D × D) E)
    (hG : SpectralCertificate G (1 / 2)) (hH : SpectralCertificate H (1 / 100)) :
    SpectralCertificate (zigzag (square G) H) (1 / 2) where
  nonnegative := by norm_num
  lt_one := by norm_num
  contraction f hf := by
    have h := zigzag_energy_bound (square G) H ((1 / 2 : ℝ) ^ 2) (1 / 100)
      (square_certificate G (1 / 2) hG) hH f hf
    have hcoef : 3 * (((1 / 2 : ℝ) ^ 2) ^ 2 + (1 / 100) ^ 2) ≤ (1 / 2 : ℝ) ^ 2 := by
      norm_num
    exact h.trans (mul_le_mul_of_nonneg_right hcoef (energy_nonnegative f))

end

end UniqueGamesTheorem.Foundations.PCP.ZigzagSpectral

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

abbrev Port := BasePort × BasePort
abbrev CloudPort := Port × Port

theorem card_port : Fintype.card Port = baseDegree ^ 2 := by
  change Fintype.card (BasePort × BasePort) = baseDegree ^ 2
  rw [Fintype.card_prod, card_basePort, pow_two]

theorem card_cloudPort : Fintype.card CloudPort = growth := by
  change Fintype.card (Port × Port) = growth
  rw [Fintype.card_prod, card_port]
  unfold growth
  ring

theorem port_degree_ge_eight : 8 ≤ Fintype.card Port := by
  rw [card_port]
  norm_num [baseDegree, initialDegree, basePower]

noncomputable def baseVertexEquiv : BaseVertex ≃ CloudPort :=
  Fintype.equivOfCardEq (card_baseVertex.trans card_cloudPort.symm)

noncomputable def baseOnCloud : PortGraph CloudPort BasePort :=
  GraphTransport.reindex (Classical.choose exists_baseGraph) baseVertexEquiv (Equiv.refl _)

theorem baseOnCloud_certificate : SpectralCertificate baseOnCloud (1 / 100 : ℝ) :=
  GraphTransport.reindex_spectralCertificate _ _ _ _ (Classical.choose_spec exists_baseGraph)

instance basePortNonempty : Nonempty BasePort :=
  ⟨fun _ => ⟨0, by norm_num [initialQuarterDegree]⟩⟩

end UniqueGamesTheorem.Foundations.PCP.ExpanderFamily

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_ExpanderTables
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.ExpanderTables

open PoweringWalks SpectralReturn

theorem step_certificate {v d : Nat} [NeZero v] [NeZero d]
    (G : Table v (d * d)) (H : Table ((d * d) * (d * d)) d)
    (hG : SpectralCertificate (graph G) (1 / 2 : ℝ))
    (hH : SpectralCertificate (graph H) (1 / 100 : ℝ)) :
    SpectralCertificate (graph (step G H)) (1 / 2 : ℝ) := by
  rw [step, graph_ofGraph]
  apply GraphTransport.reindex_spectralCertificate
  apply ZigzagSpectral.square_zigzag_halfCertificate
  · exact hG
  · exact GraphTransport.reindex_spectralCertificate _ _ _ _ hH

theorem initial_certificate (d : Nat) :
    SpectralCertificate (graph (initial d)) (1 / 2 : ℝ) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro f hf
  have hfun : f = fun _ => f 0 := funext (fun x => congrArg f (Subsingleton.elim x 0))
  have hm : mean f = f 0 := (congrArg mean hfun).trans (mean_const _)
  have hz : f 0 = 0 := hm.symm.trans hf
  rw [hfun, hz]
  simp [energy, mean, averagingOperator]

theorem family_certificate {d : Nat} [NeZero d]
    (H : Table ((d * d) * (d * d)) d)
    (hH : SpectralCertificate (graph H) (1 / 100 : ℝ)) (n : Nat) :
    SpectralCertificate (graph (family H n)) (1 / 2 : ℝ) := by
  induction n with
  | zero => exact initial_certificate d
  | succ n ih =>
    let : NeZero (vertexCount (d * d) n) :=
      ⟨Nat.ne_of_gt (vertexCount_positive (Nat.mul_pos (NeZero.pos d) (NeZero.pos d)) n)⟩
    exact step_certificate _ _ ih hH

/-- The only selected data is one fixed finite table, independent of the input. -/
theorem exists_base_table : ∃ H : Table
    ((Expanders.baseDegree * Expanders.baseDegree) *
      (Expanders.baseDegree * Expanders.baseDegree)) Expanders.baseDegree,
    SpectralCertificate (graph H) (1 / 100 : ℝ) := by
  classical
  have hv : Fintype.card ExpanderFamily.CloudPort =
      (Expanders.baseDegree * Expanders.baseDegree) *
        (Expanders.baseDegree * Expanders.baseDegree) := by
    rw [ExpanderFamily.card_cloudPort]
    unfold ExpanderFamily.growth
    ring
  let vertices := Fintype.equivFinOfCardEq hv
  let ports := Fintype.equivFinOfCardEq Expanders.card_basePort
  let G := GraphTransport.reindex ExpanderFamily.baseOnCloud vertices ports
  refine ⟨ofGraph G, ?_⟩
  rw [graph_ofGraph]
  exact GraphTransport.reindex_spectralCertificate _ _ _ _
    ExpanderFamily.baseOnCloud_certificate

end UniqueGamesTheorem.Foundations.PCP.ExpanderTables

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_AmplificationIteration
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

theorem run_gap {X : Type*} (step : X → X) (gap : X → ℝ)
    (cap : ℝ) (hc : 0 ≤ cap)
    (amplifies : ∀ x, min (2 * gap x) cap ≤ gap (step x))
    (n : Nat) (x : X) :
    min (2 ^ n * gap x) cap ≤ gap (run step n x) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    have hm : min (2 * min (2 ^ n * gap x) cap) cap ≤
        min (2 * gap (run step n x)) cap :=
      min_le_min (mul_le_mul_of_nonneg_left ih (by norm_num)) le_rfl
    rw [min_double_min _ _ hc] at hm
    have h := hm.trans (amplifies (run step n x))
    simpa [run, pow_succ, mul_assoc, mul_left_comm, mul_comm] using h

theorem run_preserves {X : Type*} (step : X → X) (P : X → Prop)
    (preserves : ∀ x, P x → P (step x)) (n : Nat) (x : X) (hx : P x) :
    P (run step n x) := by
  induction n with
  | zero => exact hx
  | succ n ih => exact preserves _ ih

/-- An inverse-size initial gap reaches the fixed threshold after the concrete loop. -/
theorem run_reaches_cap {X : Type*} (step : X → X) (gap : X → ℝ)
    (cap : ℝ) (hc : 0 ≤ cap) (hc1 : cap ≤ 1)
    (amplifies : ∀ x, min (2 * gap x) cap ≤ gap (step x))
    (n : Nat) (x : X) (hg : 0 ≤ gap x) (hstart : 1 ≤ (n : ℝ) * gap x) :
    cap ≤ gap (run step (rounds n) x) := by
  have hp : (n : ℝ) ≤ (2 : ℝ) ^ rounds n := by
    exact_mod_cast (Nat.le_of_lt (rounds_large n))
  have hcap : cap ≤ (2 : ℝ) ^ rounds n * gap x :=
    hc1.trans (hstart.trans (mul_le_mul_of_nonneg_right hp hg))
  have h := run_gap step gap cap hc amplifies (rounds n) x
  rwa [min_eq_right hcap] at h

end UniqueGamesTheorem.Foundations.PCP.AmplificationIteration

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_OverlayLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

/-- Every labeling rejects exactly the same number of darts before and after overlay. -/
theorem rejectionCount_eq [Fintype V] [Fintype D] [Fintype E]
    (G : ConstraintGraph V (V × D) A) (H : PortGraph V E)
    (htail : G.tail = Prod.fst) (labeling : V → A) :
    (constraintGraph G H).rejectionCount labeling = G.rejectionCount labeling := by
  classical
  simp only [DegreeReplacement.rejectionCount_eq_sum, Fintype.sum_prod_type,
    Fintype.sum_sum_type]
  simp [edgeSatisfied_inl G H htail]

section Averages

variable [Fintype V] [Fintype D] [Fintype E]

omit [Fintype V] in
/-- The normalized graph average weights the components by their actual port counts. -/
theorem operator_mix [Nonempty D] [Nonempty E]
    (G : PortGraph V D) (H : PortGraph V E) (f : V → ℝ) (v : V) :
    averagingOperator (portGraph G H) f v =
      (Fintype.card D : ℝ) / ((Fintype.card D : ℝ) + Fintype.card E) *
        averagingOperator G f v +
      (Fintype.card E : ℝ) / ((Fintype.card D : ℝ) + Fintype.card E) *
        averagingOperator H f v := by
  have hd : (0 : ℝ) < Fintype.card D := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card D)
  have he : (0 : ℝ) < Fintype.card E := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card E)
  change mean (fun p : D ⊕ E => f ((portGraph G H).rot (v, p)).1) = _
  rw [mean_eq_sum_div_card]
  simp only [Fintype.sum_sum_type, Fintype.card_sum, Nat.cast_add,
    portGraph_rot_inl, portGraph_rot_inr]
  unfold averagingOperator
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  field_simp [hd.ne', he.ne', (add_pos hd he).ne']

/-- Convexity of the squared energy, proved pointwise before taking the finite mean. -/
theorem energy_convex_mix (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (f g : V → ℝ) :
    energy (fun v => a * f v + b * g v) ≤ a * energy f + b * energy g := by
  calc
    energy (fun v => a * f v + b * g v) ≤
        mean (fun v => a * (f v) ^ 2 + b * (g v) ^ 2) := by
      apply mean_mono
      intro v
      have hnormalize := congrArg (fun t : ℝ => t * (a * (f v) ^ 2 + b * (g v) ^ 2)) hab
      have hnonneg := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (f v - g v))
      nlinarith
    _ = a * energy f + b * energy g := by
      rw [mean_add, mean_mul_left, mean_mul_left]
      rfl

/-- Actual overlay contraction from the supplied graph's spectral bound and
the proved energy contraction of an arbitrary reversible regular graph. -/
theorem energy_bound [Nonempty V] [Nonempty D] [Nonempty E]
    (G : PortGraph V D) (H : PortGraph V E) (lambda : ℝ)
    (certificate : SpectralCertificate H lambda) (f : V → ℝ) (hf : mean f = 0) :
    energy (averagingOperator (portGraph G H) f) ≤
      ((Fintype.card D : ℝ) + (Fintype.card E : ℝ) * lambda ^ 2) /
        ((Fintype.card D : ℝ) + Fintype.card E) * energy f := by
  let a : ℝ := (Fintype.card D : ℝ) / ((Fintype.card D : ℝ) + Fintype.card E)
  let b : ℝ := (Fintype.card E : ℝ) / ((Fintype.card D : ℝ) + Fintype.card E)
  have hd : (0 : ℝ) < Fintype.card D := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card D)
  have he : (0 : ℝ) < Fintype.card E := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card E)
  have hden : (0 : ℝ) < (Fintype.card D : ℝ) + Fintype.card E := add_pos hd he
  have ha : 0 ≤ a := div_nonneg hd.le hden.le
  have hb : 0 ≤ b := div_nonneg he.le hden.le
  have hab : a + b = 1 := by
    dsimp [a, b]
    rw [← add_div, div_self hden.ne']
  have hop : averagingOperator (portGraph G H) f =
      fun v => a * averagingOperator G f v + b * averagingOperator H f v := by
    funext v
    exact operator_mix G H f v
  calc
    energy (averagingOperator (portGraph G H) f) ≤
        a * energy (averagingOperator G f) + b * energy (averagingOperator H f) := by
      rw [hop]
      exact energy_convex_mix a b ha hb hab _ _
    _ ≤ a * energy f + b * (lambda ^ 2 * energy f) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (ZigzagSpectral.averaging_energy_le G f) ha)
        (mul_le_mul_of_nonneg_left (certificate.contraction f hf) hb)
    _ = _ := by
      dsimp [a, b]
      ring

/-- With one more original port than overlay ports, a half-spectral overlay
has squared contraction at most three quarters. -/
theorem energy_bound_three_quarters [Nonempty V]
    (G : PortGraph V D) (H : PortGraph V E)
    (hdegree : Fintype.card D = Fintype.card E + 1) (hpositive : 1 ≤ Fintype.card E)
    (certificate : SpectralCertificate H (1 / 2 : ℝ))
    (f : V → ℝ) (hf : mean f = 0) :
    energy (averagingOperator (portGraph G H) f) ≤ (3 / 4 : ℝ) * energy f := by
  let _ : Nonempty E := Fintype.card_pos_iff.mp (lt_of_lt_of_le Nat.zero_lt_one hpositive)
  let _ : Nonempty D := Fintype.card_pos_iff.mp (by omega)
  have he : (1 : ℝ) ≤ Fintype.card E := by exact_mod_cast hpositive
  have hd : (Fintype.card D : ℝ) = (Fintype.card E : ℝ) + 1 := by exact_mod_cast hdegree
  have hden : (0 : ℝ) < (Fintype.card D : ℝ) + Fintype.card E := by linarith
  have hcoefficient :
      ((Fintype.card D : ℝ) + (Fintype.card E : ℝ) * (1 / 2 : ℝ) ^ 2) /
        ((Fintype.card D : ℝ) + Fintype.card E) ≤ (3 / 4 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  exact (energy_bound G H (1 / 2) certificate f hf).trans
    (mul_le_mul_of_nonneg_right hcoefficient (energy_nonnegative f))

theorem spectralCertificate_seven_eighths [Nonempty V]
    (G : PortGraph V D) (H : PortGraph V E)
    (hdegree : Fintype.card D = Fintype.card E + 1) (hpositive : 1 ≤ Fintype.card E)
    (certificate : SpectralCertificate H (1 / 2 : ℝ)) :
    SpectralCertificate (portGraph G H) (7 / 8 : ℝ) where
  nonnegative := by norm_num
  lt_one := by norm_num
  contraction := by
    intro f hf
    exact (energy_bound_three_quarters G H hdegree hpositive certificate f hf).trans
      (mul_le_mul_of_nonneg_right (by norm_num : (3 / 4 : ℝ) ≤ (7 / 8 : ℝ) ^ 2)
        (energy_nonnegative f))

end Averages

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

/-- The equality holds for every labeling, including nonsatisfying ones. -/
theorem rejectionCount_eq [Fintype V] [Fintype D]
    (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst)
    (labeling : V → A) :
    (constraintGraph G).rejectionCount labeling = G.rejectionCount labeling := by
  classical
  simp only [DegreeReplacement.rejectionCount_eq_sum, Fintype.sum_prod_type,
    Fintype.sum_bool]
  simp [edgeSatisfied_true G htail]

end UniqueGamesTheorem.Foundations.PCP.LazyConstraint

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PreprocessingTableSpectral
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Spectral certificates for the actual materialized preprocessing tables.
Exact rotation identities transport the checked semantic overlay and lazy
estimates to the stored tables. No spectral premise is imposed on the
original constraint table in the overlay theorem.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingTableSpectral

open PoweringWalks SpectralReturn

theorem portGraph_ext {V D : Type*} {G H : PortGraph V D}
    (h : ∀ x, G.rot x = H.rot x) : G = H := by
  have hr : G.rot = H.rot := Equiv.ext h
  cases G
  cases H
  cases hr
  rfl

end UniqueGamesTheorem.Foundations.PCP.PreprocessingTableSpectral

end

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
open PoweringWalks PoweringLabels PoweringReach PoweringTest
open SpectralReturn PoweringSoundness

variable {V D E A : Type*}

def addressEquiv (ports : D ≃ E) (t : Nat) : PortWords D t ≃ PortWords E t where
  toFun w := ⟨w.1, wordEquiv ports w.1.val w.2⟩
  invFun w := ⟨w.1, (wordEquiv ports w.1.val).symm w.2⟩
  left_inv w := by rcases w with ⟨n,p⟩; simp
  right_inv w := by rcases w with ⟨n,p⟩; simp

/-- Pull target raw labels back to old port coordinates; this is a bijection. -/
def labelEquiv (ports : D ≃ E) (t : Nat) : PaddedLabel E t A ≃ PaddedLabel D t A where
  toFun a := fun w => a (addressEquiv ports t w)
  invFun a := fun w => a ((addressEquiv ports t).symm w)
  left_inv a := by funext w; simp
  right_inv a := by funext w; simp

variable (G : PortGraph V D) (H : PortGraph V E) (ports : D ≃ E)
variable (rotation : ∀ v d, H.rot (v, ports d) =
  ((G.rot (v,d)).1, ports (G.rot (v,d)).2))

include rotation

variable (accepts : Edge V E → A → A → Bool)

def pullAccepts : Edge V D → A → A → Bool :=
  fun e => accepts (e.1, ports e.2)

end UniqueGamesTheorem.Foundations.PCP.PoweringPortReindex

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_VertexPadding
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.VertexPadding

open scoped BigOperators

variable {V D A : Type*}

@[simp] theorem extendLabeling_inl (extra : ℕ) (defaultA : A) (labeling : V → A)
    (v : V) : extendLabeling extra defaultA labeling (Sum.inl v) = labeling v := rfl

@[simp] theorem extendLabeling_inr (extra : ℕ) (defaultA : A) (labeling : V → A)
    (w : Fin extra) : extendLabeling extra defaultA labeling (Sum.inr w) = defaultA := rfl

theorem rejectionCount_eq_sum {U E : Type*} [Fintype E]
    (G : ConstraintGraph U E A) (labeling : U → A) :
    G.rejectionCount labeling = ∑ e, if G.edgeSatisfied labeling e = false then 1 else 0 := by
  simp [ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts]

/-- Exact counts for every padded labeling, without any condition on dummy labels. -/
theorem pad_rejectionCount [Fintype V] [Fintype D]
    (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst) (extra : ℕ)
    (labeling : V ⊕ Fin extra → A) :
    (pad G extra).rejectionCount labeling =
      G.rejectionCount (fun v => labeling (Sum.inl v)) := by
  classical
  simp only [rejectionCount_eq_sum, Fintype.sum_prod_type, Fintype.sum_sum_type]
  simp only [edgeSatisfied_inl G htail, edgeSatisfied_inr]
  simp

end UniqueGamesTheorem.Foundations.PCP.VertexPadding

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_Preprocessing
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
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

theorem degree_positive : 0 < degree := by
  unfold degree
  omega

theorem sizeFactor_positive : 0 < sizeFactor := by
  have hg : 0 < ExpanderFamily.growth :=
    Nat.zero_lt_one.trans ExpanderFamily.growth_gt_one
  exact Nat.mul_pos (Nat.pow_pos hg) degree_positive

end UniqueGamesTheorem.Foundations.PCP.Preprocessing

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_FinalConstantsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Relations.repeatedConsistentDecidable _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.FinalConstants

def windowSize : Nat := 2 * windowHalf + 1
def walkLength : Nat := 2 * endpointLength + 1

noncomputable def gain : ℝ := (windowSize : ℝ) / denominator
noncomputable def cap : ℝ := 1 / (walkLength : ℝ)

theorem denominator_positive : 0 < denominator := by
  norm_num [denominator, alphabet, compositionLoss]

theorem windowHalf_positive : 0 < windowHalf :=
  Nat.mul_pos denominator_positive Preprocessing.sizeFactor_positive

theorem walkLength_positive : 0 < walkLength := by
  simp [walkLength]

theorem gain_large : 2 * (Preprocessing.sizeFactor : ℝ) ≤ gain := by
  have hd : (0 : ℝ) < denominator := by exact_mod_cast denominator_positive
  apply (le_div_iff₀ hd).2
  simp only [windowSize, windowHalf, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat]
  nlinarith

theorem cap_positive : 0 < cap := by
  exact one_div_pos.mpr (by exact_mod_cast walkLength_positive)

theorem cap_le_one : cap ≤ 1 := by
  apply (div_le_one (by exact_mod_cast walkLength_positive)).2
  exact_mod_cast walkLength_positive

/-- The exact fixed constants make a whole round double the input gap until
the fixed positive threshold `cap` is reached. -/
theorem composed_gap (epsilon : ℝ) (he : 0 ≤ epsilon) :
    min (2 * epsilon) cap ≤
      gain * min (epsilon / (Preprocessing.sizeFactor : ℝ))
        (1 / (walkLength : ℝ)) := by
  have hs : (0 : ℝ) < Preprocessing.sizeFactor := by
    exact_mod_cast Preprocessing.sizeFactor_positive
  have hs1 : (1 : ℝ) ≤ Preprocessing.sizeFactor := by
    exact_mod_cast Preprocessing.sizeFactor_positive
  have hg : 0 ≤ gain := le_trans (by positivity) gain_large
  rw [mul_min_of_nonneg _ _ hg]
  apply min_le_min
  · calc
      2 * epsilon = (2 * (Preprocessing.sizeFactor : ℝ)) *
          (epsilon / (Preprocessing.sizeFactor : ℝ)) := by field_simp
      _ ≤ gain * (epsilon / (Preprocessing.sizeFactor : ℝ)) :=
        mul_le_mul_of_nonneg_right gain_large (div_nonneg he hs.le)
  · change cap ≤ gain * cap
    have hgain : 1 ≤ gain := by linarith [gain_large]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hgain cap_positive.le

end UniqueGamesTheorem.Foundations.PCP.FinalConstants

end

section

/-!
The actual fixed-parameter graph transformation in one PCP amplification round.
It preprocesses the input graph, checks all edges of each bounded walk using
local endpoint labels, and applies the checked constant-query alphabet reduction.
The bounded address list is explicit fixed data shared by every input graph.
-/

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.AmplificationRound

abbrev Label := QueryIncidence.Label 6

end UniqueGamesTheorem.Foundations.PCP.AmplificationRound

end

end

section

/-!
# The fixed constants in the actual powering estimate

The six-bit alphabet has 64 letters. The middle window, endpoint length,
spectral parameter and composition loss in the checked powering theorem give
exactly the constants used in the final amplification round. Large natural
constants remain symbolic in these calculations.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringFinalConstants

/-- The actual six-bit alphabet gives the endpoint length fixed for the round. -/
theorem center_eq :
    PoweringSoundness.center (Fintype.card Alphabet) FinalConstants.windowHalf =
      FinalConstants.endpointLength := by
  rw [card_alphabet]
  rfl

/-- Prefix, pivot and suffix together have the fixed odd walk length. -/
theorem walkLength_eq :
    2 * PoweringSoundness.center (Fintype.card Alphabet) FinalConstants.windowHalf + 1 =
      FinalConstants.walkLength := by
  rw [center_eq]
  rfl

/-- Dividing the actual powering coefficient by the composition loss gives
the round coefficient exactly. The large window parameter is not evaluated. -/
theorem gain_eq :
    PoweringSoundness.gain 64 FinalConstants.windowHalf (31 / 32) / 12288 =
      FinalConstants.gain := by
  change
    (1 / (2 * (FinalConstants.alphabet : ℝ))) ^ 4 *
        (FinalConstants.windowSize : ℝ) /
        ((1 + 2 / (1 - (31 / 32 : ℝ))) + 1) /
        (FinalConstants.compositionLoss : ℝ) =
      (FinalConstants.windowSize : ℝ) / (FinalConstants.denominator : ℝ)
  rw [spectral_denominator_eq]
  have hden : (FinalConstants.denominator : ℝ) =
      16 * (FinalConstants.alphabet : ℝ) ^ 4 * 66 *
        (FinalConstants.compositionLoss : ℝ) := by
    simp only [FinalConstants.denominator, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [hden]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem gain_card_eq :
    PoweringSoundness.gain (Fintype.card Alphabet) FinalConstants.windowHalf (31 / 32) /
        12288 = FinalConstants.gain := by
  rw [card_alphabet]
  exact gain_eq

/-- Both the coefficient and cap in the actual estimate match the fixed
round constants, for every real error parameter. -/
theorem scaled_bound_eq (ε : ℝ) :
    (PoweringSoundness.gain (Fintype.card Alphabet) FinalConstants.windowHalf (31 / 32) *
        min ε
          (1 / ((2 * PoweringSoundness.center (Fintype.card Alphabet)
            FinalConstants.windowHalf + 1 : Nat) : ℝ))) / 12288 =
      FinalConstants.gain * min ε FinalConstants.cap := by
  rw [walkLength_eq]
  rw [mul_div_right_comm, gain_card_eq]
  rfl

/-- The composed powering and alphabet-reduction coefficient yields the
fixed doubling bound after the checked preprocessing loss. -/
theorem composed_scaled_gap (ε : ℝ) (hε : 0 ≤ ε) :
    min (2 * ε) FinalConstants.cap ≤
      (PoweringSoundness.gain (Fintype.card Alphabet) FinalConstants.windowHalf (31 / 32) *
        min (ε / (Preprocessing.sizeFactor : ℝ))
          (1 / ((2 * PoweringSoundness.center (Fintype.card Alphabet)
            FinalConstants.windowHalf + 1 : Nat) : ℝ))) / 12288 := by
  rw [scaled_bound_eq]
  exact FinalConstants.composed_gap ε hε

end UniqueGamesTheorem.Foundations.PCP.PoweringFinalConstants

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PreprocessingPaddingOffsets
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
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

theorem offset_all {n : Nat} (padding : Fin n → Nat) :
    offset padding n = ∑ v, padding v := by
  have ht : (List.finRange n).take n = List.finRange n := by simp
  unfold offset
  rw [ht, ← sigma_length padding (List.finRange n)]
  exact paddingList_length padding

end UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingOffsets

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PreprocessingRegularSoundness
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Soundness of the executable regularization tables

The fixed input base table is required only to have its proved spectral
certificate. Every positive cloud uses the actual recursively generated table
at its computed size. Its spectral certificate gives the precise cut bound
used by majority rounding. Empty clouds are handled by their zero cardinality.
Thus neither expansion nor the desired count comparison is an input premise.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularSoundness

open PoweringWalks DegreeReplacement SpectralReturn PreprocessingRegularTables

theorem internalDegree_ge_eight : 8 ≤ internalDegree := by
  simpa only [ExpanderFamily.card_port, internalDegree, pow_two] using
    ExpanderFamily.port_degree_ge_eight

theorem baseDegree_ne_zero : Expanders.baseDegree ≠ 0 := by
  intro h
  have hdegree := internalDegree_ge_eight
  simp only [internalDegree, h, Nat.zero_mul] at hdegree
  omega

end UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularSoundness

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PreprocessingTablesLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

theorem degree_eq : degree = Preprocessing.degree := by
  unfold degree internalDegree Preprocessing.degree
  rw [pow_two]
  omega

end UniqueGamesTheorem.Foundations.PCP.PreprocessingTables

end

section

/-! Bounds on actual metadata, stored rotor words, and emitted prefixes. These
are size estimates used inside separately proved machine executions. -/
namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingMachineBounds
open PreprocessingRegularTables PreprocessingCloudIndex
open UniqueGamesTheorem.Foundations.Complexity
open scoped BigOperators

theorem offset_le_sum {n : Nat} (p : Fin n → Nat) (k : Nat) :
    PreprocessingPaddingOffsets.offset p k ≤ ∑ v, p v := by
  have hfull : (List.finRange n).take n = List.finRange n := by simp
  have hsplit : PreprocessingPaddingOffsets.offset p k +
      (((List.finRange n).drop k).map p).sum =
      PreprocessingPaddingOffsets.offset p n := by
    simp only [PreprocessingPaddingOffsets.offset, hfull]
    rw [← List.sum_append, ← List.map_append, List.take_append_drop]
  rw [PreprocessingPaddingOffsets.offset_all] at hsplit
  omega

noncomputable def regularPolynomial : Polynomial Nat :=
  tablePolynomial ExpanderFamily.growth (ExpanderFamily.growth * (internalDegree + 1))

noncomputable def rotorPolynomial (q : Nat) : Polynomial Nat :=
  (Polynomial.C (ExpanderFamily.growth * q) * Polynomial.X) *
    (Polynomial.C (ExpanderFamily.growth * q) * Polynomial.X + 1)

end UniqueGamesTheorem.Foundations.PCP.PreprocessingMachineBounds

end

section

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.RoundGap

open AmplificationRound

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [Nonempty E]

def poweredLower (epsilon : ℝ) : ℝ :=
  PoweringSoundness.gain (Fintype.card Label) FinalConstants.windowHalf (31 / 32) *
    min (epsilon / (Preprocessing.sizeFactor : ℝ)) FinalConstants.cap

theorem poweredLower_nonnegative (epsilon : ℝ) (he : 0 ≤ epsilon) :
    0 ≤ poweredLower epsilon := by
  have hg := PoweringGap.gain_nonneg (Fintype.card Label)
    FinalConstants.windowHalf (31 / 32) (by norm_num)
  have hs : (0 : ℝ) < Preprocessing.sizeFactor := by
    exact_mod_cast Preprocessing.sizeFactor_positive
  exact mul_nonneg hg (le_min (div_nonneg he hs.le) FinalConstants.cap_positive.le)

end UniqueGamesTheorem.Foundations.PCP.RoundGap

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_FourierResponseLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The Fourier decoder is an actual finite law of private answers.  Empty
Fourier supports use an explicit fallback answer, making every response law
normalized even before folding has been imposed. -/

noncomputable section

namespace UniqueGamesTheorem.Foundations.Hastad

open scoped BigOperators
open Finset
open UniqueGamesTheorem.Foundations.Games

variable {I J : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]

def supportResponse (fallback : I) (s : Cube I) : FiniteDistribution I where
  weight i := if (support s).Nonempty then
    if i ∈ support s then 1 / ((support s).card : ℝ) else 0
    else if i = fallback then 1 else 0
  nonnegative i := by
    split_ifs <;> positivity
  normalized := by
    by_cases hs : (support s).Nonempty
    · have hc : ((support s).card : ℝ) ≠ 0 :=
        ne_of_gt (Nat.cast_pos.mpr (Finset.card_pos.mpr hs))
      simp [hs, hc]
    · simp [hs]

theorem supportResponse_expectation (fallback : I) (s : Cube I) (H : I → ℝ)
    (hs : (support s).Nonempty) :
    (supportResponse fallback s).expectation H =
      (∑ i ∈ support s, H i) / ((support s).card : ℝ) := by
  simp only [FiniteDistribution.expectation, supportResponse, hs, ite_true, if_true]
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_mem]
  simp only [div_eq_mul_inv, one_mul, Finset.univ_inter]
  rw [← Finset.mul_sum]
  ring

/-- Squared Fourier coefficients select a mask; a uniform support coordinate
selects the actual answer. Both stages use only this player's private table. -/
def fourierResponse (fallback : I) (F : Cube I → Bool) : FiniteDistribution I where
  weight i := ∑ s, coefficient (fun f => bitSign (F f)) s ^ 2 *
    (supportResponse fallback s).weight i
  nonnegative i := Finset.sum_nonneg fun s _ =>
    mul_nonneg (sq_nonneg _) ((supportResponse fallback s).nonnegative i)
  normalized := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, FiniteDistribution.normalized, mul_one]
    exact sign_parseval F

theorem fourierResponse_expectation (fallback : I) (F : Cube I → Bool)
    (H : I → ℝ) :
    (fourierResponse fallback F).expectation H =
      ∑ s, coefficient (fun f => bitSign (F f)) s ^ 2 *
        (supportResponse fallback s).expectation H := by
  unfold FiniteDistribution.expectation fourierResponse
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem response_expectation_nonnegative {K : Type*} [Fintype K]
    (law : FiniteDistribution K) (H : K → ℝ) (hH : ∀ k, 0 ≤ H k) :
    0 ≤ law.expectation H :=
  Finset.sum_nonneg fun k _ => mul_nonneg (law.nonnegative k) (hH k)

def validResponseAgreement (valid : J → Bool) (π : J → I)
    (fallbackI : I) (fallbackJ : J)
    (A : Cube I → Bool) (B : Cube J → Bool) : ℝ :=
  (fourierResponse fallbackI A).expectation fun i =>
    (fourierResponse fallbackJ B).expectation fun j =>
      if π j = i ∧ valid j = true then 1 else 0

theorem supportResponse_validAgreement (valid : J → Bool) (π : J → I)
    (fallbackI : I) (fallbackJ : J) (a : Cube I) (b : Cube J)
    (ha : (support a).Nonempty) (hb : (support b).Nonempty) :
    (supportResponse fallbackI a).expectation (fun i =>
      (supportResponse fallbackJ b).expectation (fun j =>
        if π j = i ∧ valid j = true then 1 else 0)) =
      validAgreementProbability valid π a b := by
  rw [supportResponse_expectation fallbackI a _ ha]
  simp_rw [supportResponse_expectation fallbackJ b _ hb, Finset.sum_boole]
  unfold validAgreementProbability
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  ring

theorem validAgreement_le_supportResponses (valid : J → Bool) (π : J → I)
    (fallbackI : I) (fallbackJ : J) (a : Cube I) (b : Cube J) :
    validAgreementProbability valid π a b ≤
      (supportResponse fallbackI a).expectation (fun i =>
        (supportResponse fallbackJ b).expectation (fun j =>
          if π j = i ∧ valid j = true then 1 else 0)) := by
  by_cases ha : (support a).Nonempty
  · by_cases hb : (support b).Nonempty
    · exact le_of_eq (supportResponse_validAgreement valid π fallbackI fallbackJ a b ha hb).symm
    · have he : support b = ∅ := Finset.not_nonempty_iff_eq_empty.mp hb
      simp only [validAgreementProbability, he, Finset.card_empty, Nat.cast_zero,
        mul_zero, div_zero]
      apply response_expectation_nonnegative
      intro i
      apply response_expectation_nonnegative
      intro j
      split_ifs <;> norm_num
  · have he : support a = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
    simp only [validAgreementProbability, he, Finset.sum_empty, Finset.card_empty,
      Nat.cast_zero, zero_mul, div_zero]
    apply response_expectation_nonnegative
    intro i
    apply response_expectation_nonnegative
    intro j
    split_ifs <;> norm_num

end UniqueGamesTheorem.Foundations.Hastad

end

end

section

/-! Weighted question averaging and the actual finite-game consequence of the
Håstad decoder. The game value is the maximum over deterministic private answer
tables; the Fourier responses are derandomized by the checked table law. -/

noncomputable section
namespace UniqueGamesTheorem.Foundations.Hastad

open scoped BigOperators
open Finset
open UniqueGamesTheorem.Foundations.Games

theorem distribution_sq_expectation_le {Ω : Type*} [Fintype Ω]
    (law : FiniteDistribution Ω) (F : Ω → ℝ) :
    law.expectation F ^ 2 ≤ law.expectation (fun x => F x ^ 2) := by
  let m := law.expectation F
  have h := response_expectation_nonnegative law (fun x => (F x - m) ^ 2)
    (fun x => sq_nonneg _)
  have he : law.expectation (fun x => (F x - m) ^ 2) =
      law.expectation (fun x => F x ^ 2) - m ^ 2 := by
    unfold FiniteDistribution.expectation
    calc
      _ = ∑ x, ((law.weight x * F x ^ 2 - 2 * m * (law.weight x * F x)) +
          law.weight x * m ^ 2) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.sum_mul, law.normalized]
        change (law.expectation (fun x => F x ^ 2) - 2 * m * m) + 1 * m ^ 2 = _
        simp only [FiniteDistribution.expectation]
        ring
  rw [he] at h
  dsimp [m] at h
  linarith

variable {Q₁ Q₂ I J : Type*}
  [Fintype Q₁] [DecidableEq Q₁] [Fintype Q₂] [DecidableEq Q₂]
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype J] [DecidableEq J] [Nonempty J]

def projectionGame (questions : FiniteDistribution (Q₁ × Q₂))
    (π : Q₁ → Q₂ → J → I) (valid : Q₂ → J → Bool) : Game Q₁ Q₂ I J where
  questions := questions
  accepts q₁ q₂ i j := decide (π q₁ q₂ j = i ∧ valid q₂ j = true)

def questionBias (ε : ℝ) (π : Q₁ → Q₂ → J → I)
    (A : Q₁ → Cube I → Bool) (B : Q₂ → Cube J → Bool) (q : Q₁ × Q₂) : ℝ :=
  testBias ε (π q.1 q.2) (fun f => bitSign (A q.1 f)) (fun g => bitSign (B q.2 g))

def questionAcceptance (ε : ℝ) (π : Q₁ → Q₂ → J → I)
    (A : Q₁ → Cube I → Bool) (B : Q₂ → Cube J → Bool) (q : Q₁ × Q₂) : ℝ :=
  testAcceptance ε (π q.1 q.2) (A q.1) (B q.2)

omit [DecidableEq Q₁] [DecidableEq Q₂] [Nonempty I] [Nonempty J] in
theorem questionAcceptance_eq (questions : FiniteDistribution (Q₁ × Q₂))
    (ε : ℝ) (π : Q₁ → Q₂ → J → I)
    (A : Q₁ → Cube I → Bool) (B : Q₂ → Cube J → Bool) :
    questions.expectation (questionAcceptance ε π A B) =
      (1 + questions.expectation (questionBias ε π A B)) / 2 := by
  unfold questionAcceptance
  simp_rw [testAcceptance_eq]
  unfold questionBias FiniteDistribution.expectation
  simp only [div_eq_mul_inv, mul_add, mul_one, ← mul_assoc,
    Finset.sum_add_distrib, ← Finset.sum_mul, questions.normalized]

def ConditionedOracle.fallback {valid : J → Bool} (default : J) :
    ConditionedOracle valid → J
  | .empty _ => default
  | .stored j₀ _ => j₀.val

omit [Nonempty I] [Nonempty J] in
theorem testBias_constant_right (ε : ℝ) (π : J → I) (A : Cube I → ℝ) :
    testBias ε π A (fun _ => 1) = 𝔼 f, A f := by
  unfold testBias
  simp only [mul_one, Fintype.expect_const]
  simp_rw [← Finset.sum_mul, noiseWeight_sum, one_mul]

omit [Nonempty I] [Nonempty J] in
theorem empty_conditioned_bias (ε : ℝ) (π : J → I)
    (i₀ : I) (tableA : HalfCube i₀ → Bool) :
    testBias ε π (fun f => bitSign (foldedAnswer i₀ tableA f))
      (fun _ => bitSign false) = 0 := by
  simp only [bitSign, Bool.false_eq_true, ite_false]
  rw [testBias_constant_right]
  have hz := foldedAnswer_zero_coefficient i₀ tableA
  simpa [coefficient, walsh, bitSign] using hz

end UniqueGamesTheorem.Foundations.Hastad

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_HonestTestLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Honest completeness of the actual three-query test. Compatible coordinate
dictators cancel the two uniform query tables, leaving exactly one noise bit.
The finite-tape form uses the proved product-noise pushforward law. -/

noncomputable section

namespace UniqueGamesTheorem.Foundations.Hastad

open scoped BigOperators
open UniqueGamesTheorem.Reduction.FiniteNoise

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- For compatible honest coordinates, the test parity is precisely the
selected noise coordinate, for every individual choice of query tables. -/
theorem dictator_test_parity (π : J → I) (i : I) (j : J) (hπ : π j = i)
    (f : Cube I) (g μ : Cube J) :
    (f i ^^ g j ^^ (thirdQuery π f g μ) j) = μ j := by
  simp only [thirdQuery, cubeXor, hπ]
  cases f i <;> cases g j <;> cases μ j <;> rfl

/-- The product noise law has the specified sign bias in every coordinate. -/
theorem noise_coordinate_sign (ε : ℝ) (j : J) :
    (∑ μ : Cube J, noiseWeight ε μ * bitSign (μ j)) = 1 - 2 * ε := by
  have hs : support (coordinateMask j) = {j} := by
    ext k
    simp [support, coordinateMask]
  have h := noise_walsh ε (coordinateMask j)
  simp_rw [walsh_symm (coordinateMask j), walsh_coordinateMask] at h
  simpa only [hs, Finset.card_singleton, pow_one] using h

/-- The probability of a false noise bit is exactly `1 - ε`. This is an
algebraic identity of the explicit product weights, valid for every real ε. -/
theorem noise_coordinate_false (ε : ℝ) (j : J) :
    (∑ μ : Cube J, noiseWeight ε μ * if μ j then (0 : ℝ) else 1) = 1 - ε := by
  have hind (b : Bool) : (if b then (0 : ℝ) else 1) =
      (1 + bitSign b) * (2 : ℝ)⁻¹ := by
    cases b <;> norm_num [bitSign]
  have ht (μ : Cube J) : noiseWeight ε μ * (if μ j then (0 : ℝ) else 1) =
      (noiseWeight ε μ + noiseWeight ε μ * bitSign (μ j)) * (2 : ℝ)⁻¹ := by
    rw [hind]
    ring
  simp_rw [ht]
  rw [← Finset.sum_mul, Finset.sum_add_distrib, noiseWeight_sum, noise_coordinate_sign]
  ring

/-- Exact honest acceptance for the actual three-bit test. -/
theorem testAcceptance_dictator (ε : ℝ) (π : J → I)
    (i : I) (j : J) (hπ : π j = i) :
    testAcceptance ε π (fun f => f i) (fun g => g j) = 1 - ε := by
  have hg (f : Cube I) (μ : Cube J) :
      (𝔼 g : Cube J, if f i ^^ g j ^^ (thirdQuery π f g μ) j then (0 : ℝ) else 1) =
        if μ j then 0 else 1 := by
    calc
      _ = 𝔼 _g : Cube J, if μ j then (0 : ℝ) else 1 := by
        apply Finset.expect_congr rfl
        intro g _
        rw [dictator_test_parity π i j hπ f g μ]
      _ = _ := Fintype.expect_const _
  change (𝔼 f : Cube I, ∑ μ : Cube J, noiseWeight ε μ *
    (𝔼 g : Cube J, if f i ^^ g j ^^ (thirdQuery π f g μ) j then (0 : ℝ) else 1)) = _
  simp_rw [hg]
  rw [Fintype.expect_const]
  exact noise_coordinate_false ε j

/-- The actual test using one uniform `Fin D` tape entry per noise coordinate. -/
def realizedTestAcceptance (D : Nat) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool) : ℝ :=
  𝔼 f : Cube I, 𝔼 z : J → Fin D, 𝔼 g : Cube J,
    if A f ^^ B g ^^ B (thirdQuery π f g (realizedNoise z)) then 0 else 1

/-- Exact equality between the finite uniform tape and the weighted product
noise test; no distributional acceptance premise is assumed. -/
theorem realizedTestAcceptance_eq_testAcceptance {D : Nat} (positive : 0 < D)
    (π : J → I) (A : Cube I → Bool) (B : Cube J → Bool) :
    realizedTestAcceptance D π A B = testAcceptance ((D : ℝ)⁻¹) π A B := by
  unfold realizedTestAcceptance testAcceptance
  apply Finset.expect_congr rfl
  intro f _
  exact expect_realizedNoise positive
    (fun μ => 𝔼 g : Cube J, if A f ^^ B g ^^ B (thirdQuery π f g μ) then 0 else 1)

end UniqueGamesTheorem.Foundations.Hastad

end

end

section

noncomputable section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceTape

open scoped BigOperators
open UniqueGamesTheorem.Reduction.FiniteNoise

section Tape

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] {D : ℕ}

theorem expect_testTape (H : TestTape I J D → ℝ) :
    (𝔼 t : TestTape I J D, H t) =
      𝔼 f : Cube I, 𝔼 z : J → Fin D, 𝔼 g : Cube J, H (f, z, g) := by
  rw [expect_prod]
  apply Finset.expect_congr rfl
  intro f _
  exact expect_prod _

def tapeAcceptance (D : ℕ) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool) : ℝ :=
  𝔼 t : TestTape I J D,
    if A t.1 ^^ B t.2.2 ^^ B (thirdQuery π t.1 t.2.2 (realizedNoise t.2.1))
      then 0 else 1

theorem tapeAcceptance_eq_realizedTestAcceptance (D : ℕ) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool) :
    tapeAcceptance D π A B = realizedTestAcceptance D π A B :=
  expect_testTape _

theorem tapeAcceptance_eq_testAcceptance (positive : 0 < D) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool) :
    tapeAcceptance D π A B = testAcceptance ((D : ℝ)⁻¹) π A B := by
  rw [tapeAcceptance_eq_realizedTestAcceptance,
    realizedTestAcceptance_eq_testAcceptance positive]

end Tape

end UniqueGamesTheorem.Foundations.Hastad.SourceTape

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceOccurrences
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
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

namespace Encoding

theorem card_eq_size {α : Type} [Fintype α] (a : Encoding α) :
    Fintype.card α = a.size := by
  simpa only [Fintype.card_fin] using Fintype.card_congr a.code

end Encoding

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

/-! Actual fixed-coefficient affine address construction. A finite literal phase
loads the coefficient, the checked width-two Horner machine reads coefficient
and preserved offset with the rank as its radix, then the literal field is
actually consumed. All operands and work stacks are restored. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceBasePhase

open Turing Complexity
open Target SourceContexts SourceOccurrences SourceAddressDescriptors
open UniqueGamesTheorem.Reduction.MachineSubstitution

inductive Label
  | seed
  | horner (label : MachineHorner.Label 2)
  | clear
  deriving DecidableEq, Fintype

def steps (coefficient rank offset : Nat) : Nat :=
  MachineHorner.steps rank (digits coefficient offset) 2 + coefficient + 2

noncomputable def timePolynomial (coefficient : Nat) : Polynomial Nat :=
  (MachineHorner.timePolynomial 2).comp (Polynomial.X + Polynomial.C coefficient) +
    Polynomial.C (coefficient + 2)

end UniqueGamesTheorem.Foundations.Hastad.SourceBasePhase

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
open MachineComposition SourceMachine

def fieldDestination (r : Nat) : Tape := .field ⟨min r 5, by omega⟩
def readStart (r : Nat) : Label := .read (SourceFieldArray.boundedIndex 6 r, false)
def readLoop (r : Nat) : Label := .read (SourceFieldArray.boundedIndex 6 r, true)

def scanSteps {n : Nat} (variableCount declaredClauses : Nat)
    (prior : List (Target.Clause n)) (clause : Target.Clause n) : Nat :=
  variableCount + declaredClauses + 2 +
    (encodeWords (prior.flatMap clauseWords)).length + prior.length + 1 +
    (encodeWords (clauseWords clause)).length + 7

def lookupSteps {n : Nat} (F : Target.Formula) (prior : List (Target.Clause n))
    (clause : Target.Clause n) : Nat :=
  2 * ((formulaBits F).length + 1) + scanSteps F.variables F.clauses.length prior clause

end UniqueGamesTheorem.Foundations.Hastad.SourceClauseLookup

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
open MachineComposition SourceMachine

protected abbrev HeaderTape.enumList : List HeaderTape := [.variableCount, .clauseCount]

protected theorem HeaderTape.enumList_nodup : HeaderTape.enumList.Nodup := by decide

instance instFintypeHeaderTape : Fintype HeaderTape where
  elems := ⟨HeaderTape.enumList, HeaderTape.enumList_nodup⟩
  complete x := by cases x <;> decide

variable {u : Nat} {Extra : Type}

def readStart (r : Nat) : Label u := .read (SourceFieldArray.boundedIndex 2 r, false)
def readLoop (r : Nat) : Label u := .read (SourceFieldArray.boundedIndex 2 r, true)

end UniqueGamesTheorem.Foundations.Hastad.SourceLoopInit

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceDescriptorEmissionLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
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
open SourceAddressDescriptors
open UniqueGamesTheorem.Reduction.CloneGap
open UniqueGamesTheorem.Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

def prefixTapes (destination : K) (base : K → List Bool) (written : List Nat) :
    K → List Bool := Function.update base destination (encodeWords written ++ base destination)

theorem prefixTapes_other (destination : K) (base : K → List Bool) (written : List Nat)
    (k : K) (hk : k ≠ destination) : prefixTapes destination base written k = base k := by
  simp [prefixTapes, hk]

end UniqueGamesTheorem.Foundations.Hastad.SourceEquationEmit

namespace UniqueGamesTheorem.Foundations.Hastad.SourceRankPhase

open Turing Complexity
open scoped BigOperators
open Target SourceContexts SourceOccurrences

theorem horner_value_sum (radix : Nat) (digits : Nat → Nat) (n : Nat) :
    MachineHorner.value radix digits n =
      ∑ i ∈ Finset.range n, digits i * radix ^ (n - 1 - i) := by
  induction n with
  | zero => simp [MachineHorner.value]
  | succ n ih =>
    rw [MachineHorner.value, ih, Finset.sum_range_succ, Finset.mul_sum]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, Nat.mul_one]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [show n - i = (n - 1 - i) + 1 by omega, pow_succ]
    ac_rfl

theorem horner_reverse_eq_rank {width : Nat} (radix : Nat) (digits : Fin width → Nat) :
    MachineHorner.value radix (reverseDigits digits) width = rank radix digits := by
  rw [horner_value_sum, Finset.sum_range]
  calc
    (∑ i : Fin width, reverseDigits digits i.val * radix ^ (width - 1 - i.val)) =
        ∑ i : Fin width, digits i.rev * radix ^ i.rev.val := by
      apply Finset.sum_congr rfl
      intro i _
      rw [reverseDigits_apply]
      have he : width - 1 - i.val = i.rev.val := by
        simp only [Fin.rev]
        omega
      rw [he]
    _ = rank radix digits := by
      simpa only [rank, Fin.revPerm_apply] using
        Equiv.sum_comp (Fin.revPerm (n := width)) (fun i => digits i * radix ^ i.val)

end UniqueGamesTheorem.Foundations.Hastad.SourceRankPhase

namespace UniqueGamesTheorem.Foundations.Hastad.SourceSignLoad

open Turing
open SourceLocalSignature
open UniqueGamesTheorem.Foundations.Complexity

variable {u : ℕ} {K Λ τ : Type} [DecidableEq K]

abbrev State (u : ℕ) (τ : Type) := Signature u × τ

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State u τ) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

/-- The head defaults make the finite program total on malformed tapes too;
the correctness theorem below supplies the actual unary-field representation. -/
def readSigns (field : Position u → K) (tapes : K → List Bool) : Position u → Bool :=
  fun p => (tapes (field p)).head?.getD false

end UniqueGamesTheorem.Foundations.Hastad.SourceSignLoad

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

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.Encoding

open UniqueGamesTheorem.Foundations.Complexity.MachineTupleOdometer

theorem enumerate_fin_function (n u : ℕ) :
    ((Encoding.fin u).function (Encoding.fin n)).enumerate = tupleOrder n u := by
  rfl

end UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.Encoding

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

open Turing Complexity MachineComposition

variable {u : Nat} {Extra : Type}

def entryLabel {K : Type} : (chosen : List K) → MachineDrainMany.Label chosen ⊕ Unit
  | [] => .inr ()
  | _ :: _ => .inl (.inl ())

variable [DecidableEq Extra]

theorem entryLabel_eq {K : Type} (chosen : List K) :
    MachineDrainMany.entry chosen
      (Sum.inl : MachineDrainMany.Label chosen → MachineDrainMany.Label chosen ⊕ Unit)
      (some (.inr ())) = some (entryLabel chosen) := by
  cases chosen <;> rfl

theorem lengthSum_update {K : Type} [DecidableEq K] (chosen : List K)
    (base : K → List Bool) (source : K) (h : source ∉ chosen) :
    MachineDrainMany.lengthSum chosen (Function.update base source []) =
      MachineDrainMany.lengthSum chosen base := by
  unfold MachineDrainMany.lengthSum
  congr 1
  apply List.map_congr_left
  intro k hk
  rw [Function.update_of_ne (by intro he; subst k; exact h hk)]

/-- Distinct chosen tapes make the pre-cleanup length sum the exact drain cost. -/
theorem steps_eq_of_nodup {K : Type} [DecidableEq K] (chosen : List K)
    (h : chosen.Nodup) (base : K → List Bool) :
    MachineDrainMany.steps chosen base =
      MachineDrainMany.lengthSum chosen base + chosen.length := by
  induction chosen generalizing base with
  | nil => rfl
  | cons source chosen ih =>
      obtain ⟨hn, hd⟩ := List.nodup_cons.mp h
      rw [MachineDrainMany.steps, ih hd, lengthSum_update chosen base source hn]
      simp only [MachineDrainMany.lengthSum, List.map_cons, List.sum_cons, List.length_cons]
      omega

end UniqueGamesTheorem.Foundations.Hastad.SourceContextClear

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
open MachineComposition

noncomputable section

protected abbrev Kind.enumList : List Kind := [.left, .right, .occurrences]

protected theorem Kind.enumList_nodup : Kind.enumList.Nodup := by decide

instance instFintypeKind : Fintype Kind where
  elems := ⟨Kind.enumList, Kind.enumList_nodup⟩
  complete x := by cases x <;> decide

end

end UniqueGamesTheorem.Foundations.Hastad.SourceHeaderCounts

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceTupleBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! One actual clause-tuple body. Its fixed finite control loads the context,
computes the shared right address base, traverses every selected-slot tuple and
query tape in their declared encoding order, and physically clears its work.
-/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceTupleBody

open Turing Complexity SourceContexts SourceOccurrences SourceLocalSignature
open SourceRuntimeModel SourceTupleTape


variable {u D : Nat} {Extra : Type}

def framed {K Λ Λ' σ τ S : Type} {Γ : K → Type}
    (e : σ × τ ≃ S) (labels : Λ → Λ') (exit : Option Λ') (q : TM2.Stmt Γ Λ σ) :
    TM2.Stmt Γ Λ' S :=
  MachineControl.statement id e (MachineStateFrame.statement labels exit q)

def framedConfiguration {K Λ Λ' σ τ S : Type} {Γ : K → Type}
    (e : σ × τ ≃ S) (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ' S :=
  MachineControl.configuration id e (MachineStateFrame.configuration labels exit ambient c)

section Frame

variable {K Λ Λ' σ τ S : Type} {Γ : K → Type} [DecidableEq K]

theorem framed_stepAux (e : σ × τ ≃ S) (labels : Λ → Λ') (exit : Option Λ')
    (q : TM2.Stmt Γ Λ σ) (state : σ) (ambient : τ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (framed e labels exit q) (e (state, ambient)) tapes =
      framedConfiguration e labels exit ambient (TM2.stepAux q state tapes) := by
  rw [framed, MachineControl.stepAux_simulation, MachineStateFrame.stepAux_simulation]
  rfl

theorem framed_step (e : σ × τ ≃ S) (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' S)
    (atLabels : ∀ l, target (labels l) = framed e labels exit (source l))
    (a b : TM2.Cfg Γ Λ σ) (h : TM2.step source a = some b) :
    TM2.step target (framedConfiguration e labels exit ambient a) =
      some (framedConfiguration e labels exit ambient b) := by
  rcases a with ⟨label, state, tapes⟩
  cases label with
  | none => cases h
  | some l =>
    change some (TM2.stepAux (source l) state tapes) = some b at h
    cases Option.some.inj h
    change some (TM2.stepAux (target (labels l)) (e (state, ambient)) tapes) = _
    rw [atLabels, framed_stepAux]

def framedExecution (e : σ × τ ≃ S) (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' S)
    (atLabels : ∀ l, target (labels l) = framed e labels exit (source l))
    {a b : TM2.Cfg Γ Λ σ} {budget : Nat}
    (run : StateTransition.EvalsToInTime (TM2.step source) a (some b) budget) :
    StateTransition.EvalsToInTime (TM2.step target)
      (framedConfiguration e labels exit ambient a)
      (some (framedConfiguration e labels exit ambient b)) budget :=
  MachineComposition.liftExecutionInTime _ _ (framedConfiguration e labels exit ambient)
    (framed_step e labels exit ambient source target atLabels) run

end Frame

end UniqueGamesTheorem.Foundations.Hastad.SourceTupleBody

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceGapLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-!
The actual finite graph iteration used by the mathematical PCP construction.
One fixed, explicitly supplied complete address list is shared by every round.
Each round constructs a new constraint graph. The scalar gap and size are the
actual minimum rejection fraction and actual finite cardinalities of that graph.

The final Boolean formula uses supplied vertex and dart numberings. These
theorems establish the finite objects and their size/gap properties, not a
machine running-time theorem or an independently encoded NP-hardness theorem.
-/

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.PCPIteration

def finalClauseGap : ℚ := 1 / (40960 * (FinalConstants.walkLength : ℚ))

end UniqueGamesTheorem.Foundations.PCP.PCPIteration

end

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

/-! Explicit finite predicates and numeric row words of the initial incidence table.
Every relation retains all 4096 entries, including repetitions. -/

/-! The concrete numbered amplification round, with one fixed base expander.
Every intermediate is an actual stored table, with explicit finite coordinates.
The running-time certificate is a separate theorem about these same functions. -/

namespace UniqueGamesTheorem.Foundations.PCP.RoundTables

theorem walkParameter_eq : walkParameter = 2 * FinalConstants.endpointLength :=
  fixedWalkParameter.property

end UniqueGamesTheorem.Foundations.PCP.RoundTables

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

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineModel

open Turing Complexity Hastad

abbrev Alphabet (_ : Tape) := Bool

def copySource : CopyPhase → Tape
  | .tailVariables _ | .dummyVariables => .variables
  | .variableName slot => .field (nameField slot)
  | _ => .index

def finalTape (slot : Fin 3) : Tape :=
  if slot.val = 0 then .variables else if slot.val = 1 then .counter else .index

def drain (tape : Tape) (again next : Label) : TM2.Stmt Alphabet Label State :=
  MachineDrain.drain tape again (some next)

def headerTape (slot : Fin 2) : Tape := if slot.val = 0 then .variables else .counter

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineModel

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_RawInitialMachinePhases
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual execution of the raw initial graph program's reusable phases. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachinePhases

open Turing Complexity RawInitialMachineModel

theorem copySource_ne_scratch (phase : CopyPhase) : copySource phase ≠ Tape.scratch := by
  cases phase <;> simp [copySource]

theorem copySource_ne_reversed (phase : CopyPhase) : copySource phase ≠ Tape.reversed := by
  cases phase <;> simp [copySource]

theorem bitWord_head (b : Bool) :
    (encodeWord (if b then 1 else 0)).head? = some b := by
  cases b <;> rfl

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachinePhases

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

def inputTapes (bits : List Bool) : Tape → List Bool
  | .input => bits
  | _ => []

def firstTapes (n m : ℕ) (clauseBits : List Bool) : Tape → List Bool
  | .input => encodeWord m ++ clauseBits
  | .variables => encodeWord n
  | _ => []

def counterTapes (n m : ℕ) (clauseBits : List Bool) : Tape → List Bool
  | .input => clauseBits
  | .variables => encodeWord n
  | .counter => encodeWord m
  | _ => []

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineStart

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_RawInitialMachineLoopData
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The exact input and output streams at successive clause-loop iterations.
These tape invariants use the actual word codecs and clause occurrence order. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData

open Target Complexity RawInitialMachineModel

def loopTapes (n i remaining : Nat) (input reversed : List Bool) : Tape → List Bool
  | .input => input
  | .variables => encodeWord n
  | .counter => encodeWord remaining
  | .index => encodeWord i
  | .reversed => reversed
  | _ => []

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData

end

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

open Turing Complexity RawInitialMachineModel RawInitialMachinePhases


def outputTapes (base : Tape → List Bool) (bits : List Bool) : Tape → List Bool :=
  Function.update base .reversed (bits ++ base .reversed)

@[simp] theorem outputTapes_reversed (base : Tape → List Bool) (bits : List Bool) :
    outputTapes base bits .reversed = bits ++ base .reversed := by simp [outputTapes]

@[simp] theorem outputTapes_twice (base : Tape → List Bool) (first second : List Bool) :
    outputTapes (outputTapes base first) second = outputTapes base (second ++ first) := by
  funext tape
  by_cases h : tape = .reversed
  · subst tape; simp [List.append_assoc]
  · simp [outputTapes, h]

theorem reverse_encodeWord_add (a b : ℕ) :
    (encodeWord b).reverse ++ List.replicate a true = (encodeWord (a + b)).reverse := by
  simp only [encodeWord, List.reverse_append, List.reverse_replicate, List.reverse_singleton]
  rw [Nat.add_comm a b, List.replicate_add]
  simp only [List.append_assoc]

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineRows

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

open Turing Complexity RawInitialMachineModel RawInitialMachinePhases

def tapes (varsWord counter index reversed output : List Bool) : Tape → List Bool
  | .variables => varsWord
  | .counter => counter
  | .index => index
  | .reversed => reversed
  | .output => output
  | _ => []

def finishTapes (n m : Nat) (rev : List Bool) : Tape → List Bool :=
  tapes (encodeWord n) [false] (encodeWord m) rev []

theorem update_reversed (varsWord counter index rev out word : List Bool) :
    Function.update (tapes varsWord counter index rev out) .reversed word =
      tapes varsWord counter index word out := by
  funext k
  cases k <;> simp [tapes]

theorem update_finish (n m : Nat) (rev word : List Bool) :
    Function.update (finishTapes n m rev) .reversed word = finishTapes n m word :=
  update_reversed _ _ _ _ _ _

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineFinish

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

open Turing MachineComposition PCP MachineRegularInternalRow
open PreprocessingCloudIndex PreprocessingRegularTables

variable {σ Λ : Type}

theorem portBits_eq {q : Nat} (bits : Fin q → List Bool) (k : Nat) (hk : k ≤ q) :
    portBits bits k = (List.ofFn (fun p : Fin k => bits ⟨p.val, lt_of_lt_of_le p.isLt hk⟩)).flatten := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : k < q := by omega
    rw [portBits, dite_eq_left h, ih (by omega), List.ofFn_succ_last, List.flatten_append]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    rfl

theorem portBits_all {q : Nat} (bits : Fin q → List Bool) :
    portBits bits q = (List.ofFn bits).flatten := by
  simpa only [Fin.eta] using portBits_eq bits q (Nat.le_refl q)

def portTimeBound (q graphLength rotorLength x v i k o m outputLength vertices : Nat) : Nat :=
  q * coreTimeBound q graphLength rotorLength x v i k o m
    (outputLength + q * rowSizeBound q vertices)

def originalTimeBound (q graphLength rotorLength x v i k o m outputLength vertices : Nat) : Nat :=
  portTimeBound q graphLength rotorLength x v i k o m outputLength vertices +
    MachineRegularOriginalClean.timeBound q graphLength
      (outputLength + q * rowSizeBound q vertices)

def dummyTimeBound (q graphLength rotorLength x v i k o m outputLength vertices : Nat) : Nat :=
  portTimeBound q graphLength rotorLength x v i k o m outputLength vertices +
    MachineRegularDummyRow.timeBound q x (outputLength + q * rowSizeBound q vertices)

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularVertexBlock

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularOriginalBodyBounds
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Polynomial runtime for the actual original-vertex body. The size parameter
includes the already accumulated output, so no output-prefix premise is used. -/
namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBodyBounds

open Turing MachineComposition PCP PreprocessingCloudIndex PreprocessingRegularTables
open PreprocessingMachineBounds MachineRegularOriginalBody

noncomputable def wide : Polynomial Nat := Polynomial.C (ExpanderFamily.growth + 1) * Polynomial.X
noncomputable def rowPolynomial (q : Nat) : Polynomial Nat :=
  wide + wide * Polynomial.C (q + 1) + 8192
noncomputable def outputPolynomial (q : Nat) : Polynomial Nat :=
  wide + Polynomial.C q * rowPolynomial q
noncomputable def corePolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C (5*q+32) * rotorPolynomial q + 10*wide + 2*wide + 13*wide + 5*wide +
    Polynomial.C (5*q+10)*(wide+wide) + 4*wide + 2*outputPolynomial q +
      Polynomial.C (8*q+41066)
noncomputable def blockPolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C q * corePolynomial q + Polynomial.C (5*q+20)*wide +
    2*outputPolynomial q + Polynomial.C (5*q+40995)
noncomputable def cleanupPolynomial (q : Nat) : Polynomial Nat := 6*wide + rotorPolynomial q + 13

theorem blockPolynomial_eval (q L : Nat) :
    (blockPolynomial q).eval L =
      MachineRegularVertexBlock.originalTimeBound q
        ((ExpanderFamily.growth+1)*L) ((rotorPolynomial q).eval L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L) := by
  simp only [blockPolynomial, corePolynomial, outputPolynomial, rowPolynomial, wide,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, MachineRegularVertexBlock.originalTimeBound,
    MachineRegularVertexBlock.portTimeBound, MachineRegularInternalRow.coreTimeBound,
    MachineRegularOriginalClean.timeBound, MachineRegularVertexBlock.rowSizeBound]
  ring

theorem originalTimeBound_le (q L R x v i k o m O V W R' : Nat)
    (hL : L ≤ W) (hR : R ≤ R') (hx : x ≤ W) (hv : v ≤ W)
    (hi : i ≤ W) (hk : k ≤ W) (ho : o ≤ W) (hm : m ≤ W)
    (hO : O ≤ W) (hV : V ≤ W) :
    MachineRegularVertexBlock.originalTimeBound q L R x v i k o m O V ≤
      MachineRegularVertexBlock.originalTimeBound q W R' W W W W W W W W := by
  unfold MachineRegularVertexBlock.originalTimeBound MachineRegularVertexBlock.portTimeBound
    MachineRegularInternalRow.coreTimeBound MachineRegularOriginalClean.timeBound
    MachineRegularVertexBlock.rowSizeBound
  gcongr

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBodyBounds

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

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable PreprocessingRegularLoopWords

theorem oneStep {A : Type} {f : A → Option A} {a b : A}
    (h : f a = some b) : (advance f)^[1] (some a) = some b := by
  simpa only [Function.iterate_one, advance_some] using h

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularOwnerBodyBounds
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Bounds for actual dummy-owner execution

The size parameter includes the old output length. During the owner loop,
newly emitted dummy blocks are bounded by the actual complete regularized
table codec. No hypothesis about a machine body's execution supplies a bound.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBodyBounds

open Turing MachineComposition PCP PreprocessingCloudIndex PreprocessingRegularTables
open PreprocessingMachineBounds PreprocessingRegularLoopWords

noncomputable def wide : Polynomial Nat := Polynomial.C (ExpanderFamily.growth + 1) * Polynomial.X

noncomputable def rowPolynomial (q : Nat) : Polynomial Nat :=
  wide + wide * Polynomial.C (q + 1) + 8192

noncomputable def outputPolynomial (q : Nat) : Polynomial Nat :=
  wide + regularPolynomial + Polynomial.C q * rowPolynomial q

noncomputable def corePolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C (5*q+32) * rotorPolynomial q + 10*wide + 2*wide + 13*wide + 5*wide +
    Polynomial.C (5*q+10)*(wide+wide) + 4*wide + 2*outputPolynomial q +
      Polynomial.C (8*q+41066)

noncomputable def blockPolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C q * corePolynomial q + Polynomial.C (5*q+11)*wide +
    2*outputPolynomial q + Polynomial.C (5*q+40986)

theorem blockPolynomial_eval (q L : Nat) :
    (blockPolynomial q).eval L =
      MachineRegularVertexBlock.dummyTimeBound q
        ((ExpanderFamily.growth+1)*L) ((rotorPolynomial q).eval L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L)
        (((ExpanderFamily.growth+1)*L) + regularPolynomial.eval L)
        ((ExpanderFamily.growth+1)*L) := by
  simp only [blockPolynomial, corePolynomial, outputPolynomial, rowPolynomial, wide,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, MachineRegularVertexBlock.dummyTimeBound,
    MachineRegularVertexBlock.portTimeBound, MachineRegularInternalRow.coreTimeBound,
    MachineRegularDummyRow.timeBound, MachineRegularVertexBlock.rowSizeBound]
  simp only [Nat.add_assoc]

theorem dummyTimeBound_le (q L R x v i k o m O V W R' O' : Nat)
    (hL : L ≤ W) (hR : R ≤ R') (hx : x ≤ W) (hv : v ≤ W)
    (hi : i ≤ W) (hk : k ≤ W) (ho : o ≤ W) (hm : m ≤ W)
    (hO : O ≤ O') (hV : V ≤ W) :
    MachineRegularVertexBlock.dummyTimeBound q L R x v i k o m O V ≤
      MachineRegularVertexBlock.dummyTimeBound q W R' W W W W W W O' W := by
  unfold MachineRegularVertexBlock.dummyTimeBound MachineRegularVertexBlock.portTimeBound
    MachineRegularInternalRow.coreTimeBound MachineRegularDummyRow.timeBound
    MachineRegularVertexBlock.rowSizeBound
  gcongr

noncomputable def prePolynomial : Polynomial Nat :=
  MachineCloudPadding.timePolynomial.comp (2*Polynomial.X+1) + 4*wide + 6

noncomputable def loopPolynomial : Polynomial Nat :=
  wide * (blockPolynomial internalDegree + 2)

noncomputable def cleanupPolynomial : Polynomial Nat :=
  6*wide + rotorPolynomial internalDegree + 13

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBodyBounds

end

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

open Turing MachineComposition
open UniqueGamesTheorem.Foundations.PCP

namespace Header

variable {σ : Type}

noncomputable def arithmeticPolynomial (q : Nat) : Polynomial Nat :=
  let X : Polynomial Nat := Polynomial.X
  let G : Polynomial Nat := Polynomial.C ExpanderFamily.growth * X
  let D : Polynomial Nat := Polynomial.C (ExpanderFamily.growth * (q + 1)) * X
  (12 * X + 11) + ((2 * (X + 2) + (G + 1)) + (2 * (G + 1) + 1)) +
    (((2 * (D + 2) + 2 * (G + 2)) + (2 * ((G + D + 2) + X) + 3)) + 1 + (X + 1) + 1)

noncomputable def timePolynomial (q : Nat) : Polynomial Nat :=
  MachineCloudPrefix.timePolynomial.comp (2 * Polynomial.X + 1) + arithmeticPolynomial q

end Header

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable

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
open MachineComposition

variable {K Λ A : Type} [DecidableEq K]

/-- Reassociate the actual three comparison registers into the shared state. -/
def compareStateEquiv (A : Type) : MachineCompare.State A ≃ State A where
  toFun s := ((s.1, s.2.1, s.2.2.1), s.2.2.2)
  invFun s := (s.1.1, s.1.2.1, s.1.2.2, s.2)
  left_inv := by rintro ⟨a, b, c, d⟩; rfl
  right_inv := by rintro ⟨⟨a, b, c⟩, d⟩; rfl

def bitEncoding (bit : Bool) : List Bool := encodeWord (if bit then 1 else 0)

theorem encodeWord_eq_iff (a b : Nat) : encodeWord a = encodeWord b ↔ a = b := by
  constructor
  · intro h
    have hlength := congrArg List.length h
    simp only [encodeWord_length] at hlength
    omega
  · rintro rfl
    rfl

theorem emit_step (destination : K) (bit : Bool) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (label : Λ) (atEmit : program label = emit destination bit exit)
    (state : State A) (base : K → List Bool) :
    TM2.step program ⟨some label, state, base⟩ =
      some ⟨exit, state,
        Function.update base destination (bitEncoding bit ++ base destination)⟩ := by
  change some (TM2.stepAux (program label) state base) = _
  rw [atEmit]
  cases bit <;> cases exit <;>
    simp [emit, exitAt, TM2.stepAux, bitEncoding, encodeWord, Function.update_idem]

end UniqueGamesTheorem.Foundations.Complexity.MachineUnaryEqualityBit

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

/-! A rotor step on the live unary port-table encoding. First read the reverse
dart identifier; then read that dart's tail vertex. This uses no division or
runtime graph data in finite control. Both positional selections are proved
from the actual serialization. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRotor

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

inductive Label
  | reverse (l : MachineAffineLookup.Label)
  | endpoint (l : MachineAffineLookup.Label)
  deriving DecidableEq, Fintype

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRotor

/-! Fixed port words are executed by a finite chain of actual rotor programs.
The six shared tapes hold table, query, scan, reverse identifier, scratch and
output. Each walk position has a separate physical vertex tape. The final
unary copy also handles the empty word and preserves the starting vertex. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineWord

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

def Label : Nat → Type
  | 0 => MachineUnaryAffineAt.Label
  | t + 1 => PoweringMachineRotor.Label ⊕ Label t

instance labelFintype (t : Nat) : Fintype (Label t) := by
  induction t with
  | zero => exact inferInstanceAs (Fintype MachineUnaryAffineAt.Label)
  | succ t ih =>
      letI := ih
      exact inferInstanceAs (Fintype (PoweringMachineRotor.Label ⊕ Label t))

instance labelDecidableEq (t : Nat) : DecidableEq (Label t) := by
  induction t with
  | zero => exact inferInstanceAs (DecidableEq MachineUnaryAffineAt.Label)
  | succ t ih =>
      letI := ih
      exact inferInstanceAs (DecidableEq (PoweringMachineRotor.Label ⊕ Label t))

def entry : (t : Nat) → Label t
  | 0 => .seed
  | _ + 1 => .inl (.reverse .seed)

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineWord

/-! A fixed shared tape layout for the actual powering field subroutines.
The vertex identifiers live on physical tapes. The trajectory capacity is
fixed by `max`; each bounded word uses its first `t` trajectory tapes. -/

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
open MachineComposition
open PCP

variable {K Λ A : Type} [DecidableEq K]
variable {max l r n d : Nat}

abbrev Label (l r : Nat) :=
  PoweringMachineWord.Label l ⊕ PoweringMachineWord.Label r ⊕ MachineUnaryEqualityBit.Label

def entry (l r : Nat) : Label l r := .inl (PoweringMachineWord.entry l)

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

def initialTapes (n : Nat) (suffix : List Bool) : HeaderTape → List Bool
  | .source => encodeWord n ++ suffix
  | _ => []

def scanTapes (B remaining processed : Nat) (suffix : List Bool) : HeaderTape → List Bool
  | .source => encodeWord remaining ++ suffix
  | .counter => encodeWord processed
  | .vertices => encodeWord processed
  | .darts => encodeWord (B * processed)

def finalTapes (B n : Nat) (suffix : List Bool) : HeaderTape → List Bool
  | .source => suffix
  | .counter => encodeWord n
  | .vertices => encodeWord n
  | .darts => encodeWord (B * n)

def scanConfiguration {σ : Type} (B remaining processed : Nat)
    (suffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.Cfg HeaderAlphabet HeaderLabel (HeaderState σ) :=
  ⟨some .scan, (ambient, register), scanTapes B remaining processed suffix⟩

def finalConfiguration {σ : Type} (B n : Nat) (suffix : List Bool) (ambient : σ) :
    TM2.Cfg HeaderAlphabet HeaderLabel (HeaderState σ) :=
  ⟨none, (ambient, none), finalTapes B n suffix⟩

theorem initializeStep {σ : Type} (B n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (headerProgram B)
      ⟨some .initialize_, (ambient, register), initialTapes n suffix⟩ =
        some (scanConfiguration B n 0 suffix ambient none) := by
  simp only [TM2.step, headerProgram, TM2.stepAux]
  congr 2
  funext tape
  cases tape <;> simp [initialTapes, scanTapes, encodeWord]

theorem scanStep_zero {σ : Type} (B processed : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (headerProgram B) (scanConfiguration B 0 processed suffix ambient register) =
      some (finalConfiguration B processed suffix ambient) := by
  simp only [TM2.step, scanConfiguration, headerProgram, TM2.stepAux,
    scanTapes, encodeWord, List.replicate_zero, List.nil_append, List.singleton_append,
    List.head?_cons, List.tail_cons, Option.getD_some, Bool.cond_false]
  congr 2
  funext tape
  cases tape <;> simp [finalTapes, scanTapes]

theorem scanStep_succ {σ : Type} (B remaining processed : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (headerProgram B)
      (scanConfiguration B (remaining + 1) processed suffix ambient register) =
      some (scanConfiguration B remaining (processed + 1) suffix ambient none) := by
  simp only [TM2.step, scanConfiguration, headerProgram, TM2.stepAux,
    scanTapes, encodeWord, List.replicate_succ, List.cons_append,
    List.head?_cons, List.tail_cons, Option.getD_some, Bool.cond_true]
  rw [stepAux_pushTrue]
  simp only [TM2.stepAux]
  congr 2
  funext tape
  cases tape <;>
    simp [scanTapes, encodeWord, Nat.mul_add, List.replicate_add,
      List.replicate_succ, List.append_assoc, Nat.add_comm,
      -List.replicate_append_replicate]

/-- The loop consumes precisely the unary field, including its delimiter. -/
theorem scanTrace {σ : Type} (B remaining processed : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (headerProgram B)))^[remaining + 1]
      (some (scanConfiguration B remaining processed suffix ambient register)) =
      some (finalConfiguration B (processed + remaining) suffix ambient) := by
  induction remaining generalizing processed register with
  | zero =>
    simpa only [Nat.add_zero, Nat.zero_add, Function.iterate_one, MachineComposition.advance_some] using
      scanStep_zero B processed suffix ambient register
  | succ remaining ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step (headerProgram B)))^[remaining + 1]
      (TM2.step (headerProgram B)
        (scanConfiguration B (remaining + 1) processed suffix ambient register)) = _
    rw [scanStep_succ, ih]
    simp only [Nat.add_comm, Nat.add_left_comm]

theorem headerTrace {σ : Type} (B n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (headerProgram B)))^[n + 2]
      (some ⟨some .initialize_, (ambient, register), initialTapes n suffix⟩) =
      some (finalConfiguration B n suffix ambient) := by
  rw [show n + 2 = (n + 1) + 1 by omega, Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step (headerProgram B)))^[n + 1]
    (TM2.step (headerProgram B)
      ⟨some .initialize_, (ambient, register), initialTapes n suffix⟩) = _
  rw [initializeStep]
  simpa only [Nat.zero_add] using scanTrace B n 0 suffix ambient none

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

abbrev Label := HeaderLabel ⊕ MachineUnaryAffineAt.Label

theorem boolAlphabet_eq (max : Nat) :
    MachineEmbedding.Alphabet HeaderAlphabet (fun _ : ExtraTape max => Bool) =
      (fun _ : GlobalTape max => Bool) := by
  funext tape
  cases tape <;> rfl

theorem castTapes_embedding {max : Nat} (header : HeaderTape → List Bool)
    (extra : ExtraTape max → List Bool) :
    castTapes (boolAlphabet_eq max) (MachineEmbedding.tapes header extra) =
      mergeTapes header extra := by
  funext tape
  rw [castTapes_apply]
  cases tape <;> rfl

@[simp] theorem final_counter (max B vertices : Nat) (extra : ExtraTape max → List Bool) :
    mergeTapes (finalTapes B vertices []) extra
      (commonPlacement max (PoweringMachineTapes.start max)) = encodeWord vertices := by
  simp [mergeTapes, finalTapes]

@[simp] theorem final_vertices (max B vertices : Nat) (extra : ExtraTape max → List Bool) :
    mergeTapes (finalTapes B vertices []) extra (.inl .vertices) = encodeWord vertices := rfl

@[simp] theorem final_darts (max B vertices : Nat) (extra : ExtraTape max → List Bool) :
    mergeTapes (finalTapes B vertices []) extra (.inl .darts) = encodeWord (B * vertices) := rfl

@[simp] theorem final_extra (max B vertices : Nat) (extra : ExtraTape max → List Bool)
    (tape : ExtraTape max) :
    mergeTapes (finalTapes B vertices []) extra (.inr tape) = extra tape := rfl

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

def headerTapeEquiv : HeaderTape ≃ Fin 4 where
  toFun
    | .source => 0
    | .counter => 1
    | .vertices => 2
    | .darts => 3
  invFun i := if i = 0 then .source else if i = 1 then .counter
    else if i = 2 then .vertices else .darts
  left_inv tape := by cases tape <;> rfl
  right_inv i := by fin_cases i <;> rfl

def extraTapeEquiv (max : Nat) : ExtraTape max ≃ Fin (11 + max + 1) :=
  (Equiv.sumCongr (sharedTapeEquiv max) unitTapeEquiv).trans finSumFinEquiv

/-- Exact arithmetic numbering of every physical global tape. -/
def globalTapeEquiv (max : Nat) : GlobalTape max ≃ Fin (4 + (11 + max + 1)) :=
  (Equiv.sumCongr headerTapeEquiv (extraTapeEquiv max)).trans finSumFinEquiv

/-- The executable equivalence consumed by Finish and DrainMany. -/
def enumeration (max : Nat) : Fin (4 + (11 + max + 1)) ≃ GlobalTape max :=
  (globalTapeEquiv max).symm

@[simp] theorem globalTapeEquiv_enumeration (max : Nat) (i : Fin (4 + (11 + max + 1))) :
    globalTapeEquiv max (enumeration max i) = i :=
  (globalTapeEquiv max).apply_symm_apply i

@[simp] theorem enumeration_globalTapeEquiv (max : Nat) (tape : GlobalTape max) :
    enumeration max (globalTapeEquiv max tape) = tape :=
  (globalTapeEquiv max).symm_apply_apply tape

@[simp] theorem source_index (max : Nat) :
    (globalTapeEquiv max (.inl .source)).val = 0 := rfl

@[simp] theorem counter_index (max : Nat) :
    (globalTapeEquiv max (.inl .counter)).val = 1 := rfl

@[simp] theorem vertices_index (max : Nat) :
    (globalTapeEquiv max (.inl .vertices)).val = 2 := rfl

@[simp] theorem darts_index (max : Nat) :
    (globalTapeEquiv max (.inl .darts)).val = 3 := rfl

@[simp] theorem finalOutput_index (max : Nat) :
    (globalTapeEquiv max (finalOutput max)).val = 4 + (11 + max) := rfl

end UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalEnumeration

/-! A concrete relation-field producer: execute a fixed word from the live
start vertex, then read the predicate at the reached vertex and fixed port.
All instructions use the shared tape layout and preserve the finite row
buffer. No execution premise is supplied by the caller. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRelationField

open Turing
open MachineComposition
open PCP

variable {K Λ A : Type} [DecidableEq K]
variable {n d max : Nat}

abbrev Label (path : List (Fin d)) := PoweringMachineWord.Label path.length ⊕ MachineAffineLookup.Label

omit [DecidableEq K] in
theorem source_outside_lookup (placement : PoweringMachineTapes.Tape max → K)
    (distinct : Function.Injective placement) :
    ∀ i, placement (.inl 6) ≠ lookupTapes placement i := by
  intro i h
  have heq : PoweringMachineTapes.relationPlacement max 0 = PoweringMachineTapes.relationPlacement max i.succ := by
    simpa [PoweringMachineTapes.leftEndpoint] using distinct h
  have hi := (PoweringMachineTapes.relationPlacement_injective max) heq
  have hv := congrArg Fin.val hi
  simp at hv

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRelationField

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineField

open Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {n d max : Nat}

def Label : Instruction d → Type
  | .relation path _ _ _ => PoweringMachineRelationField.Label path
  | .equal left right => PoweringMachineEqualityField.Label left.length right.length

instance labelFintype (op : Instruction d) : Fintype (Label op) := by
  cases op <;> dsimp only [Label] <;> infer_instance

instance labelDecidableEq (op : Instruction d) : DecidableEq (Label op) := by
  cases op <;> dsimp only [Label] <;> infer_instance

def entry : (op : Instruction d) → Label op
  | .relation path _ _ _ => .inl (PoweringMachineWord.entry path.length)
  | .equal left right => PoweringMachineEqualityField.entry left.length right.length

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineField

/-! The concrete finite program that produces an entire powered-row input
block. Its static control executes the field plan backwards, so prepending each
computed unary Boolean field leaves the canonical serialized block in order. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachinePlan

open Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {vertices d max : Nat}

abbrev LocalLabel (op : Command d max) := PoweringMachineField.Label op.val
abbrev Label (commands : List (Command d max)) := MachineFiniteSequence.Label LocalLabel commands

def entry (commands : List (Command d max)) (labels : Label commands → Λ) (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry LocalLabel (fun op => PoweringMachineField.entry op.val)
    commands labels exit

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachinePlan

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRowHeaders

open Turing MachineComposition
open PCP PoweringRowHeaderSemantics
open PoweringMachineTapes

variable {K Λ σ : Type} [DecidableEq K]
variable {vertices d max : Nat}

@[simp] theorem headerPlacement_table {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 0) = table max := by
  simp [headerPlacement, table, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_query {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 1) = query max := by
  simp [headerPlacement, query, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_scan {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 2) = scan max := by
  simp [headerPlacement, scan, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_reverse {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 3) = reverse max := by
  simp [headerPlacement, reverse, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_scratch {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 4) = scratch max := by
  simp [headerPlacement, scratch, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_output {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 5) = rowOutput max := by
  simp [headerPlacement]

@[simp] theorem headerPlacement_start {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inr (PoweringMachineWord.first t)) = start max := by
  simp [headerPlacement, start, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_succ {t max : Nat} (h : t ≤ max) (i : Fin t) :
    headerPlacement h (.inr i.succ) = .inr (Fin.castLE h i) := by
  simp [headerPlacement, leftEndpoint, rowOutput, Equiv.swap_apply_def]

abbrev Label (n : Nat) := MachineUnaryAffineAt.Label ⊕
  (MachineUnaryAffineAt.Label ⊕ PoweringMachineWord.Label (n + 1))

def entry (n : Nat) : Label n := .inl .seed

def tailEntry (n : Nat) (direction : Bool) : Label n :=
  if direction then .inr (.inr (PoweringMachineWord.entry (n + 1))) else .inr (.inl .seed)

def afterReverse (n : Nat) (placement : Tape max → K) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool) : K → List Bool :=
  Function.update base (placement (rowOutput max))
    (encodeWord (reverseValue d n vertex ports direction) ++ base (placement (rowOutput max)))

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

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K] {N : Nat}

abbrev Label (enumeration : Fin N ≃ K) (output : K) :=
  MachineUnaryAffineAt.Label ⊕ (MachineUnaryAffineAt.Label ⊕
    MachineDrainMany.Label (MachineDrainMany.workTapes enumeration output))

def afterD (output : K) (base : K → List Bool) (m : Nat) : K → List Bool :=
  Function.update base output (encodeWord m ++ base output)

def afterHeaders (output : K) (base : K → List Bool) (n m : Nat) : K → List Bool :=
  Function.update base output (encodeWords [n, m] ++ base output)

@[simp] theorem afterHeaders_output (output : K) (base : K → List Bool) (n m : Nat) :
    afterHeaders output base n m output = encodeWords [n, m] ++ base output := by
  simp only [afterHeaders, Function.update_self]

theorem afterHeaders_other (output : K) (base : K → List Bool) (n m : Nat)
    (k : K) (hk : k ≠ output) : afterHeaders output base n m k = base k :=
  Function.update_of_ne hk _ _

/-- Exact cleanup cost is computed on the actual post-copy tape contents. -/
def steps (enumeration : Fin N ≃ K) (output : K) (base : K → List Bool) (n m : Nat) : Nat :=
  copySteps n m + MachineDrainMany.steps (MachineDrainMany.workTapes enumeration output)
    (afterHeaders output base n m)

theorem afterHeaders_length_le (output : K) (base : K → List Bool) (n m bound : Nat)
    (bounded : ∀ k, (base k).length ≤ bound) (k : K) :
    (afterHeaders output base n m k).length ≤ bound + n + m + 2 := by
  by_cases hk : k = output
  · subst k
    rw [afterHeaders_output]
    have hb := bounded output
    simp only [List.length_append, encodeWords, encodeWord_length, List.length_nil]
    omega
  · rw [afterHeaders_other output base n m k hk]
    have hb := bounded k
    omega

/-- A uniform pre-cleanup stack bound gives a linear finishing budget. -/
theorem steps_le_uniform (enumeration : Fin N ≃ K) (output : K)
    (base : K → List Bool) (n m bound : Nat)
    (bounded : ∀ k, (base k).length ≤ bound) :
    steps enumeration output base n m ≤ 2 * (n + m) + 6 + N * (bound + n + m + 3) := by
  have hc := MachineDrainMany.steps_le_uniform (MachineDrainMany.workTapes enumeration output)
    (afterHeaders output base n m) (bound + n + m + 2)
    (afterHeaders_length_le output base n m bound bounded)
  have hl := MachineDrainMany.workTapes_length_le enumeration output
  have hm := Nat.mul_le_mul_right (bound + n + m + 3) hl
  rw [show bound + n + m + 2 + 1 = bound + n + m + 3 by omega] at hc
  unfold steps
  rw [copySteps_eq]
  exact Nat.add_le_add_left (hc.trans hm) _

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish

end

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

open Turing MachineComposition PCP
open MachineFixedBlockMap

variable {K Λ : Type} [DecidableEq K] {vertices d : Nat}

/-- Only the header phase directs shared output role 10 to the external output. -/
def headerPlacement {max : Nat} (placement : PoweringMachineTapes.Tape max → K)
    (output : K) (i : PoweringMachineTapes.Tape max) : K :=
  if i = .inl 10 then output else placement i

omit [DecidableEq K] in
@[simp] theorem headerPlacement_output {max : Nat}
    (placement : PoweringMachineTapes.Tape max → K) (output : K) :
    headerPlacement placement output (.inl 10) = output := by simp [headerPlacement]

omit [DecidableEq K] in
theorem headerPlacement_injective {max : Nat}
    (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) :
    Function.Injective (headerPlacement placement output) := by
  intro i j h
  by_cases hi : i = .inl 10
  · subst i
    by_cases hj : j = .inl 10
    · exact hj.symm
    · exact False.elim (outside j (by simpa [headerPlacement, hj] using h))
  · by_cases hj : j = .inl 10
    · subst j
      exact False.elim (outside i (by simpa [headerPlacement, hi] using h.symm))
    · exact distinct (by simpa [headerPlacement, hi, hj] using h)

omit [DecidableEq K] in
theorem headerPlacement_excludes_data {max : Nat}
    (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) :
    ∀ i, placement (.inl 10) ≠ headerPlacement placement output i := by
  intro i h
  by_cases hi : i = .inl 10
  · subst i
    exact outside _ (by simpa only [headerPlacement_output] using h.symm)
  · have heq : (.inl 10 : PoweringMachineTapes.Tape max) = i :=
      distinct (by simpa [headerPlacement, hi] using h)
    exact hi heq.symm

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRowBody

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
open PoweringTables PoweringEnumeration

theorem encodeWords_flatMap {α : Type*} (items : List α)
    (words : α → List Nat) :
    encodeWords (items.flatMap words) =
      items.flatMap (fun item => encodeWords (words item)) := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [List.flatMap_cons, encodeWords_append, ih]

end UniqueGamesTheorem.Foundations.PCP.PoweringTableLayout

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_PoweringMachineVertex
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineVertex

open Turing MachineComposition PCP

variable {K Λ : Type} [DecidableEq K] {vertices d n : Nat}

theorem encodeWords_flatMap {X : Type*} (xs : List X) (f : X → List Nat) :
    encodeWords (xs.flatMap f) = xs.flatMap (fun x => encodeWords (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineVertex

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_PoweringMachineOuterLoopLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual variable-size vertex enumeration. The finite guard decrements the
live unary counter, a one-step bridge enters the fixed vertex producer, and the
producer returns to the guard. Work tapes may change after every vertex. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineOuterLoop

open Turing MachineComposition PCP

variable {K Λ : Type} [DecidableEq K] {vertices d n : Nat}

abbrev Placement (K : Type) (n : Nat) := PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K

def counter (placement : Placement K n) (base : K → List Bool) (remaining : Nat) : K → List Bool :=
  MachineUnaryCounter.counterTapes (placement (.inl 1)) base remaining []

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineOuterLoop

/-!
# The fixed global powering machine

For fixed degree `d` and radius parameter `n`, this is one concrete finite
machine: initialization, unary vertex guard, the fixed vertex-row producer,
and output-header/cleanup instructions are connected by explicit labels.
Its definition takes no input graph, vertex count, or program callback.

The code equations below expose each actual branch for the separate runtime
proof. The variable-size input graph and counters reside on physical tapes.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal

open Turing

abbrev Tape (n : Nat) :=
  PoweringMachineInitialize.GlobalTape (PoweringMachineRowBody.capacity n)

def placement (n : Nat) :
    PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → Tape n :=
  PoweringMachineInitialize.commonPlacement (PoweringMachineRowBody.capacity n)

def inputTape (n : Nat) : Tape n :=
  placement n (PoweringMachineTapes.table (PoweringMachineRowBody.capacity n))

def outputTape (n : Nat) : Tape n :=
  PoweringMachineInitialize.finalOutput (PoweringMachineRowBody.capacity n)

def headerVertices (n : Nat) : Tape n := .inl PoweringMachineLoop.HeaderTape.vertices
def headerDarts (n : Nat) : Tape n := .inl PoweringMachineLoop.HeaderTape.darts

def enumeration (n : Nat) :
    Fin (4 + (11 + PoweringMachineRowBody.capacity n + 1)) ≃ Tape n :=
  PoweringGlobalEnumeration.enumeration (PoweringMachineRowBody.capacity n)

abbrev FinishLabel (n : Nat) := PoweringMachineFinish.Label (enumeration n) (outputTape n)

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal

/-!
# Concrete global configurations and tape separation

These lemmas specialize the checked initializer placement to the fixed global
machine. The final configuration is the actual `Turing.haltList`, with the
machine's clean initial register and only the output tape populated.
-/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_PoweringPolynomialBudgetLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finishing cost from the actual preceding machine execution

Every stack can grow by at most the fixed program's push bound in one
transition. Consequently an actual bounded execution from the standard input
configuration supplies the uniform stack bound needed by the finishing phase.
The bound below uses the same global machine for that preceding execution; no
separate tape-size hypothesis or numerical simulation is substituted for it.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringRuntimeBudget

open Turing

/-- Uniform stack growth along an actual execution, from any initial configuration. -/
theorem stackLength_le_of_execution (tm : FinTM2) (start finish : tm.Cfg)
    (initialBound priorBudget : Nat)
    (initial : ∀ k, (start.stk k).length ≤ initialBound)
    (prior : StateTransition.EvalsToInTime tm.step start (some finish) priorBudget)
    (k : tm.K) :
    (finish.stk k).length ≤ initialBound + priorBudget * Runtime.programPushBound tm := by
  have grown := Runtime.executionSizeBound tm.step (fun cfg => (cfg.stk k).length)
    (Runtime.programPushBound tm) (Runtime.stepStackLength tm k) prior
  exact grown.trans (Nat.add_le_add_right (initial k) _)

/-- Standard input initialization bounds every initial stack by the input length. -/
theorem stackLength_le_from_input (tm : FinTM2) (input : List (tm.Γ tm.k₀))
    (finish : tm.Cfg) (priorBudget : Nat)
    (prior : StateTransition.EvalsToInTime tm.step (initList tm input)
      (some finish) priorBudget) (k : tm.K) :
    (finish.stk k).length ≤ input.length + priorBudget * Runtime.programPushBound tm :=
  stackLength_le_of_execution tm (initList tm input) finish input.length priorBudget
    (Runtime.initialStackLength tm input) prior k

end UniqueGamesTheorem.Foundations.Complexity.PoweringRuntimeBudget

/-! Complete execution of the one fixed powering machine on the actual
port-table input and generic graph-table output encodings. The varying vertex
count remains on unary tapes throughout. -/

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

abbrev Ambient (q : Nat) := Flags × GenericGraphTables.RelationTable q
abbrev State (q : Nat) := Ambient q × Option Bool

def normal {q : Nat} (relation : GenericGraphTables.RelationTable q) (selfLoop : Bool) : State q :=
  (((selfLoop, false, none), relation), none)

def initial (q : Nat) : State q := normal (Vector.replicate (q * q) false) false

def context {q : Nat} (ambient : Ambient q) : GenericGraphTables.RelationTable q × Bool :=
  (ambient.2, ambient.1.1)

def compareEquiv (q : Nat) : State q ≃
    MachineCompare.State (GenericGraphTables.RelationTable q × Bool) where
  toFun s := ((s.1.2, s.1.1.1), s.1.1.2.1, s.1.1.2.2, s.2)
  invFun s := (((s.1.2, s.2.1, s.2.2.1), s.1.1), s.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem compareEquiv_normal {q : Nat}
    (relation : GenericGraphTables.RelationTable q) (selfLoop : Bool) :
    compareEquiv q (normal relation selfLoop) =
      ((relation, selfLoop), false, none, none) := rfl

def emitterEquiv (q : Nat) : ((Ambient q × Unit) × Option Bool) ≃ State q where
  toFun s := (s.1.1, s.2)
  invFun s := ((s.1, ()), s.2)
  left_inv s := by rcases s with ⟨⟨s, u⟩, r⟩; cases u; rfl
  right_inv _ := rfl

theorem setupPorts_injective : Function.Injective setupPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [setupPorts]

theorem headPorts_injective : Function.Injective headPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [headPorts]

theorem cleanupPorts_ne_output (i : Fin 15) : cleanupPorts i ≠ .output := by
  fin_cases i <;> simp [cleanupPorts]

variable {Λ : Type} {q : Nat}

def compareStatement (stmt : TM2.Stmt Alphabet Λ
    (MachineCompare.State (GenericGraphTables.RelationTable q × Bool))) :
    TM2.Stmt Alphabet Λ (State q) :=
  MachineControl.statement id (compareEquiv q).symm stmt

def emitterStatement (stmt : TM2.Stmt Alphabet Λ ((Ambient q × Unit) × Option Bool)) :
    TM2.Stmt Alphabet Λ (State q) :=
  MachineControl.statement id (emitterEquiv q) stmt

/-- Store the result chosen by the actual comparison's equal/different exit.
This does not compare tape contents in a register transition. -/
def storeLoop (value : Bool) (next : Λ) : TM2.Stmt Alphabet Λ (State q) :=
  .load (fun state => (((value, false, none), state.1.2), none)) (.goto fun _ => next)

theorem stepAux_storeLoop (value : Bool) (next : Λ) (state : State q)
    (base : Tape → List Bool) :
    TM2.stepAux (storeLoop value next) state base =
      ⟨some next, normal state.1.2 value, base⟩ := rfl

def nextRow (next : Λ) : TM2.Stmt Alphabet Λ (State q) :=
  .push .edge (fun _ => true)
    (.load (fun state => (state.1, none)) (.goto fun _ => next))

theorem stepAux_nextRow (next : Λ) (state : State q)
    (base : Tape → List Bool) (edge : Nat) (suffix : List Bool)
    (he : base .edge = encodeWord edge ++ suffix) :
    TM2.stepAux (nextRow next) state base =
      ⟨some next, (state.1, none),
        Function.update base .edge (encodeWord (edge + 1) ++ suffix)⟩ := by
  simp [nextRow, TM2.stepAux, he, encodeWord, List.replicate_succ]

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

variable {q : Nat} {Λ : Type}

theorem encodeWord_eq_iff (left right : Nat) :
    encodeWord left = encodeWord right ↔ left = right := by
  constructor
  · intro h
    have hh := congrArg List.length h
    simpa only [encodeWord_length, Nat.add_right_cancel_iff] using hh
  · rintro rfl
    rfl

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.CompareLoop

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
open Enumeration

def eval {bound : Nat} (field : Field bound) (inputs : Fin 5 → Nat) : Nat :=
  Emitter.affineValue field.terms inputs field.offset.val

/-- One q-only bound covers every coefficient and every finite offset. -/
def fieldBound (q : Nat) : Nat :=
  12 * localCount q + tapeCount q + pairTapeCount q + 1

theorem fieldBound_pos (q : Nat) : 0 < fieldBound q := by
  unfold fieldBound
  omega

theorem tapeCount_lt_bound (q : Nat) : tapeCount q < fieldBound q := by
  unfold fieldBound
  omega

theorem pairTapeCount_lt_bound (q : Nat) : pairTapeCount q < fieldBound q := by
  unfold fieldBound
  omega

theorem localCount_lt_bound (q : Nat) : localCount q < fieldBound q := by
  unfold fieldBound
  omega

theorem twelve_local_lt_bound (q : Nat) : 12 * localCount q < fieldBound q := by
  unfold fieldBound
  omega

def zeroOffset (q : Nat) : Fin (fieldBound q) := ⟨0, fieldBound_pos q⟩

def headerVertices (q : Nat) : Field (fieldBound q) :=
  ⟨[(0, tapeCount q), (1, localCount q + pairTapeCount q)], zeroOffset q⟩

def headerDarts (q : Nat) : Field (fieldBound q) :=
  ⟨[(1, 12 * localCount q)], zeroOffset q⟩

def vertexQueryTerms (q : Nat) (side : Bool) : Terms :=
  [(1, localCount q), (if side then 4 else 3, tapeCount q)]

def edgeQueryTerms (q : Nat) : Terms :=
  [(1, localCount q), (0, tapeCount q), (2, pairTapeCount q)]

theorem headerVertices_eval (q n m edge tail head : Nat) :
    eval (headerVertices q) (values n m edge tail head) = vertexCount n m q := by
  simp [eval, headerVertices, values, zeroOffset, Emitter.affineValue,
    vertexCount, eventCount, addressCount, Nat.mul_add,
    Nat.mul_comm, Nat.add_comm, Nat.add_assoc]

theorem headerDarts_eval (q n m edge tail head : Nat) :
    eval (headerDarts q) (values n m edge tail head) = dartCount m q := by
  simp [eval, headerDarts, values, zeroOffset, Emitter.affineValue,
    dartCount, eventCount, Nat.mul_comm, Nat.mul_assoc]

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Addresses

end

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
open Emitter

theorem bitValues_ofFn {σ : Type} {n : Nat}
    (relation : σ → Vector Bool n) (context : σ) :
    (List.ofFn (fun index : Fin n => fun state => (relation state)[index])).map
      (fun bit => if bit context then 1 else 0) =
      (relation context).toList.map GraphTables.bitWord := by
  rw [← vector_list_ofFn (relation context)]
  simp only [List.map_ofFn]
  rfl

theorem encodeWords_flatMap {α : Type} (items : List α) (words : α → List Nat) :
    encodeWords (items.flatMap words) = items.flatMap (fun item => encodeWords (words item)) := by
  induction items with
  | nil => rfl
  | cons item items ih => simp [encodeWords_append, ih]

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.EmitRows

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

def resultTapes (ports : Ports K) (base : K → List Bool)
    (n m : Nat) (rows : List Bool) : K → List Bool :=
  Function.update
    (Function.update
      (Function.update
        (Function.update (Function.update base (ports 1) rows)
          (ports 2) (encodeWord n)) (ports 3) (encodeWord m))
      (ports 4) (encodeWord m)) (ports 6) (encodeWord 0)

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Setup

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_Body
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
One actual iteration of the alphabet-table driver. The positive unary guard,
row parser, preserving head lookup, comparison, finite emission plan, three
drains, and unary index increment all execute inside `Driver.program`.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Body

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

def bodyTime (q N : Nat) : Nat :=
  (32 + 8 * (Enumeration.localCount q * (6 * (2 * 4104)))) * (N + 1)

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Body

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_LoopInitializationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
The concrete tapes produced by initialization satisfy the row-zero loop
invariant. Execution of initialization is proved separately by
`Initialization.initializeInTime`; this bridge identifies its resulting tapes.
-/



namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Loop


open Turing
open UniqueGamesTheorem.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

/-- A quadratic prefix allowance because the number of original rows is at
most the length of their fully encoded input table. -/
def prefixTime (q N : Nat) : Nat :=
  Initialization.time N + N * Body.bodyTime q N + 1

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Loop



namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Runtime

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open RuntimeModel


noncomputable def prefixPolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C 27 * Polynomial.X + Polynomial.C 54 +
    Polynomial.X *
      (Polynomial.C (32 + 8 * (Enumeration.localCount q * (6 * (2 * 4104)))) *
        (Polynomial.X + Polynomial.C 1)) + Polynomial.C 1

theorem prefixPolynomial_eval (q N : Nat) :
    (prefixPolynomial q).eval N = Loop.prefixTime q N := by
  simp only [prefixPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Loop.prefixTime,
    Initialization.time, Body.bodyTime]
  ring

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Runtime



/-! Every work tape of the actual alphabet-table machine stores Bool symbols.
This checks the work alphabets separately from the finite-machine structure's
input-alphabet condition, without changing the runtime certificate. -/



/-! The actual padding, expander overlay, and lazy-loop stages composed into
one polynomial-time finite machine. The initial degree-replacement stage is
assembled separately. -/
namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingFinishRuntime

open Turing UniqueGamesTheorem.Foundations.Complexity
open PreprocessingRegularTables

theorem finish_degree_positive (d : Nat) (hd : 0 < d) : 0 < d + internalDegree :=
  hd.trans_le (Nat.le_add_right d internalDegree)

end UniqueGamesTheorem.Foundations.PCP.PreprocessingFinishRuntime



/-! The complete actual preprocessing machine, including degree replacement,
vertex padding, explicit expander construction, overlay, and lazy edges. -/



/-!
Actual sequential finite-machine composition for the concrete numbered round.
The initial composition lemma isolates the preprocessing and powering execution
certificates with their shared bit codecs. The final endpoint supplies the
checked powering and alphabet machines, leaving only preprocessing explicit.
-/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_TableGapReductionLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! Both semantic implications for the actual stored-table 3SAT gap map.
The positive clause gap follows from the full actual repeated transformation.
The full map admits a polynomial-time machine. -/

namespace UniqueGamesTheorem.Foundations.PCP.TableGapReduction

open RoundTables SpectralReturn Target

theorem finalClauseGap_le_one : PCPIteration.finalClauseGap ≤ 1 := by
  have hw : (1 : ℚ) ≤ (FinalConstants.walkLength : ℚ) := by
    exact_mod_cast FinalConstants.walkLength_positive
  have hd : (0 : ℚ) < 40960 * (FinalConstants.walkLength : ℚ) := by positivity
  rw [PCPIteration.finalClauseGap, div_le_one hd]
  linarith

end UniqueGamesTheorem.Foundations.PCP.TableGapReduction



end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceIncidence
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Outer.SourceIncidence

open UniqueGamesTheorem.Reduction ActualSource
open UniqueGamesTheorem.Foundations Games Target PCP
open UniqueGamesTheorem.Soundness.IncidenceExtraction
open UniqueGamesTheorem.Clean.IncidenceGap
open scoped BigOperators

noncomputable section

theorem uniform_probability_eq_expect {n : Nat} [Nonempty (Fin n)]
    (p : Fin n → Bool) :
    (FiniteDistribution.uniform (Fin n)).probability p =
      (Finset.univ.expect (fun i => if p i then (1 : ℚ) else 0) : ℚ) := by
  rw [Fintype.expect_eq_sum_div_card]
  push_cast
  simp only [FiniteDistribution.probability, FiniteDistribution.uniform, Fintype.card_fin]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  cases p i <;> simp

end
end UniqueGamesTheorem.Outer.SourceIncidence

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_ActualMatrixContradiction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The contradiction uses the same actual seed and local decoder on both
sides. Its lower bound comes from full-table variation followed by visible
conditioning; its upper bound comes from the exact incidence sampler. -/

namespace UniqueGamesTheorem.Decoder.ActualMatrixContradiction

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d r : ℕ}

def expectationOf {X : Type*} {i : Fintype X}
    (μ : @FiniteDistribution X i) (f : X → ℝ) : ℝ :=
  @FiniteDistribution.expectation X i μ f

end
end UniqueGamesTheorem.Decoder.ActualMatrixContradiction

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_ParameterSelection
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

namespace OuterParameters

variable {ε δ : ℝ} (P : OuterParameters ε δ)

theorem exists_parity_error (k : ℕ) (hk : 0 < k) :
    ∃ ξ : ℚ, 0 < ξ ∧ ξ < 1 / 100 ∧
      ξ < P.epsilon0 / (2 * k * P.repetitions) := by
  have hdenom : (0 : ℚ) < 2 * k * P.repetitions := by
    exact mul_pos (mul_pos (by norm_num) (by exact_mod_cast hk))
      (by exact_mod_cast P.repetitions_pos)
  let ξ := min (1 / 100 : ℚ) (P.epsilon0 / (2 * k * P.repetitions)) / 2
  have hmin : 0 < min (1 / 100 : ℚ) (P.epsilon0 / (2 * k * P.repetitions)) :=
    lt_min (by norm_num) (div_pos P.epsilon0_pos hdenom)
  refine ⟨ξ, div_pos hmin (by norm_num), ?_, ?_⟩
  · have hle := min_le_left (1 / 100 : ℚ) (P.epsilon0 / (2 * k * P.repetitions))
    dsimp [ξ]
    linarith
  · have hle := min_le_right (1 / 100 : ℚ) (P.epsilon0 / (2 * k * P.repetitions))
    dsimp [ξ]
    linarith

/-- Both matrix-test completeness losses fit the budget fixed before the
alphabet, for the later chosen positive tuple length. -/
theorem matrix_error_budget (k : ℕ) (hk : 0 < k) (ξ : ℚ)
    (hξ : ξ ≤ P.epsilon0 / (2 * k * P.repetitions)) :
    (k : ℚ) * ξ + P.pStar / 2 ≤ P.epsilon0 / P.repetitions := by
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  have htq : (0 : ℚ) < P.repetitions := by exact_mod_cast P.repetitions_pos
  have hx := (le_div_iff₀ (mul_pos (mul_pos (by norm_num) hkq) htq)).mp hξ
  have hp := (le_div_iff₀ htq).mp P.reciprocal_budget
  apply (le_div_iff₀ htq).mpr
  dsimp [pStar]
  nlinarith

end OuterParameters
end
end UniqueGamesTheorem.ParameterSelection

end

end OAI
end


