-- Prove2me | Definitions.Def_OAIQ086U008
-- name    : OAIQ086U008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T16:37:31.402445+00:00
-- url     : https://prove2.me/theorems/4fc9ba34-e72d-4866-a0d6-6278fe174021
-- title:
--   Definitions bundle OAIQ086U008 of the split of OpenAI, The Unique Games Theorem
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniqueGamesTheorem.theorem11`, carved from OpenAI's openai/math development (OpenAI, *The Unique Games Theorem*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 951 declarations of OpenAI's Lean: 352 definitions, 8 inductive types or structures, 2 instances and 589 theorems. The definitions and types are `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularDummyRow.instruction`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow.CoreLabel`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow.coreAfterCleanup`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow.coreCleaned`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow.coreCleanupSteps`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow.coreEntry`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow.coreInputTapes`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow.coreInstruction`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow.coreSelectStateEquiv`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow.coreSelectTape`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow.coreSelectView`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow.coreSteps`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow.finishInstruction`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow.rawSelectProgram`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow.rotorFinalTapes`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow.rotorInstruction`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow.rotorSteps`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow.selectCleanState`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow.selectControl`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow.selectMemory`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow.selectProgram`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularMetadata.cloudData`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularMetadata.originalData`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularMetadata.ownerData`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularMetadata.ownerSteps`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularMetadata.prefixData`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularMetadata.queryFrame`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularMetadata.rankData`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalClean.Input`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalClean.instruction`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalClean.steps`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalRow.Input`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalRow.affined`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalRow.copied`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalRow.finalTapes`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalRow.instruction`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalRow.looked`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalRow.steps`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.BaseTable`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.CoreState` and 320 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `UniqueGames_Foundations_Conditioning`, `UniqueGames_Foundations_FiniteTrialsLemmas`, `UniqueGames_Foundations_KernelSampling`, `UniqueGames_Foundations_SamplingLemmas`, `UniqueGames_Foundations_SharedProfiles`, `UniqueGames_Foundations_ValueLemmas`, `UniqueGames_Games_CompletedSamplingLemmas`, `UniqueGames_Games_FactorizationLemmas`, `UniqueGames_Games_FinishBoundsLemmas`, `UniqueGames_Games_PartialRevealLemmas`, `UniqueGames_Games_SelectedCommonMarginalLemmas`, `UniqueGames_Games_SelectedInformationLemmas`, `UniqueGames_Games_SelectionSequence`, `UniqueGames_Inverse_RowErasureMatrixLemmas`, `UniqueGames_Machines_MachineRegularDummyRow`, `UniqueGames_Machines_MachineRegularInternalRow`, `UniqueGames_Machines_MachineRegularLift`, `UniqueGames_Machines_MachineRegularMetadata`, `UniqueGames_Machines_MachineRegularOriginalClean`, `UniqueGames_Machines_MachineRegularOriginalRow`, `UniqueGames_Machines_MachineRegularOwnerProgram`, `UniqueGames_Machines_MachineRegularTable`, `UniqueGames_Machines_MachineRegularVertexBlock`, `UniqueGames_Machines_MachineRepeat`, `UniqueGames_Machines_MachineUnaryEqualityBit`, `UniqueGames_Machines_MachineUnaryLessAtLemmas`, `UniqueGames_Machines_PoweringGlobalEnumerationLemmas`, `UniqueGames_Machines_PoweringInitializeFrame`, `UniqueGames_Machines_PoweringMachineEqualityField`, `UniqueGames_Machines_PoweringMachineFinish`, `UniqueGames_Machines_PoweringMachineInitialize`, `UniqueGames_Machines_PoweringMachineOuterLoopLemmas`, `UniqueGames_Machines_PoweringMachineRelationLemmas`, `UniqueGames_Machines_PoweringMachineRow`, `UniqueGames_Machines_PoweringMachineRowBody`, `UniqueGames_Machines_PoweringMachineVertex`, `UniqueGames_Machines_PoweringMasterState`, `UniqueGames_Machines_PoweringPlanBudget`, `UniqueGames_Machines_PoweringPolynomialBudgetLemmas`, `UniqueGames_PCP_Addresses`, `UniqueGames_PCP_AlphabetTableBoundsLemmas`, `UniqueGames_PCP_ClauseVerifierLemmas`, `UniqueGames_PCP_CleanupLemmas`, `UniqueGames_PCP_CompareLoop`, `UniqueGames_PCP_DriverLemmas`, `UniqueGames_PCP_EmitRows`, `UniqueGames_PCP_Emitter`, `UniqueGames_PCP_FinalBooleanVerifier`, `UniqueGames_PCP_FoldedEquationLemmas`, `UniqueGames_PCP_FourierResponseLemmas`, `UniqueGames_PCP_GenericGraphTables`, `UniqueGames_PCP_GraphTables`, `UniqueGames_PCP_HonestTestLemmas`, `UniqueGames_PCP_InitialGraphLemmas`, `UniqueGames_PCP_Initialization`, `UniqueGames_PCP_LoopInitializationLemmas`, `UniqueGames_PCP_LoopState`, `UniqueGames_PCP_NameCompaction`, `UniqueGames_PCP_OverlayLemmas`, `UniqueGames_PCP_PortTableLookup`, `UniqueGames_PCP_PoweringPortReindexLemmas`, `UniqueGames_PCP_PoweringTableLayout`, `UniqueGames_PCP_PoweringTableSemanticsLemmas`, `UniqueGames_PCP_PoweringTablesLemmas`, `UniqueGames_PCP_PreprocessingOverlayTables`, `UniqueGames_PCP_PreprocessingPaddingTables`, `UniqueGames_PCP_PreprocessingRegularLoopWordsLemmas`, `UniqueGames_PCP_PreprocessingRegularSoundness`, `UniqueGames_PCP_PreprocessingRegularTablesLemmas`, `UniqueGames_PCP_PreprocessingRegularWords`, `UniqueGames_PCP_PreprocessingTableSpectral`, `UniqueGames_PCP_PreprocessingTablesLemmas`, `UniqueGames_PCP_RawInitialMachineFinish`, `UniqueGames_PCP_RawInitialMachineStart`, `UniqueGames_PCP_RawInitialTablesLemmas`, `UniqueGames_PCP_RuntimeModel`, `UniqueGames_PCP_Setup`, `UniqueGames_PCP_SourceAddressArithmeticLemmas`, `UniqueGames_PCP_SourceContextClear`, `UniqueGames_PCP_SourceContextLoad`, `UniqueGames_PCP_SourceDescriptorEmissionLemmas`, `UniqueGames_PCP_SourceFieldArrayLemmas`, `UniqueGames_PCP_SourceHonestLemmas`, `UniqueGames_PCP_SourceLoopInitLemmas`, `UniqueGames_PCP_SourceOccurrences`, `UniqueGames_PCP_SourceQueryLoopLemmas`, `UniqueGames_PCP_SourceSignaturePrepareLemmas`, `UniqueGames_PCP_Table`, `UniqueGames_Reduction_FinalParametersLemmas`.
--
--   **Imports.** It imports the published bundle `Def_UniqueGamesTheorem`; the bundles `OAIQ086U003`, `OAIQ086U004` and `OAIQ086U005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ086U010` and `OAIQ086U011`; the statement `OAI_UniqueGamesTheorem_Decoder_MatrixGap_parameters_of_inverse`.
-- source:
--   OpenAI, The Unique Games Theorem, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Unique-Games-Theorem-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_UniqueGamesTheorem
import Definitions.Def_OAIQ086U003
import Definitions.Def_OAIQ086U004
import Definitions.Def_OAIQ086U005

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_FiniteTrialsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
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

/-- An acceptance implication under an exact question-law pushforward gives an
actual success-probability comparison for every pair of local strategies. -/
theorem success_le_of_localSimulation {R₁ R₂ B₁ B₂ : Type*}
    [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂]
    (G : Game Q₁ Q₂ A₁ A₂) (H : Game R₁ R₂ B₁ B₂)
    (questionMap₁ : Q₁ → R₁) (questionMap₂ : Q₂ → R₂)
    (answerMap₁ : Q₁ → B₁ → A₁) (answerMap₂ : Q₂ → B₂ → A₂)
    (questionLaw : H.questions =
      G.questions.pushforward (fun q => (questionMap₁ q.1, questionMap₂ q.2)))
    (acceptance : ∀ x y a b,
      H.accepts (questionMap₁ x) (questionMap₂ y) a b = true →
      G.accepts x y (answerMap₁ x a) (answerMap₂ y b) = true)
    (strategy : Strategy R₁ R₂ B₁ B₂) :
    H.success strategy ≤
      G.success (simulatedStrategy questionMap₁ questionMap₂ answerMap₁ answerMap₂ strategy) := by
  unfold success
  rw [questionLaw, FiniteDistribution.probability_pushforward]
  apply FiniteDistribution.probability_mono
  intro questions h
  exact acceptance questions.1 questions.2 _ _ h

theorem selectedWins_mono (G : Game Q₁ Q₂ A₁ A₂) {n : Nat}
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    {selected selected' : Finset (Fin n)} (h : selected ⊆ selected') :
    (G.repetition n).questions.probability (G.selectedWins strategy selected') ≤
      (G.repetition n).questions.probability (G.selectedWins strategy selected) := by
  apply FiniteDistribution.probability_mono
  intro questions hwin
  simp only [selectedWins, decide_eq_true_eq] at hwin ⊢
  intro i hi
  exact hwin i (h hi)

theorem selectedWins_univ (G : Game Q₁ Q₂ A₁ A₂) {n : Nat}
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    G.selectedWins strategy Finset.univ = (G.repetition n).wins strategy := by
  classical
  funext questions
  simp [selectedWins, coordinateWin, repetition, wins]

end Game

end

end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_Conditioning
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  {n : Nat}

theorem selectedSuccess_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) : 0 ≤ G.selectedSuccess strategy selected :=
  (G.repetition n).questions.probability_nonnegative _

theorem selectedSuccess_le_one (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) : G.selectedSuccess strategy selected ≤ 1 :=
  (G.repetition n).questions.probability_le_one _

theorem selectedSuccess_univ (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    G.selectedSuccess strategy Finset.univ = (G.repetition n).success strategy := by
  rw [selectedSuccess, G.selectedWins_univ]
  rfl

theorem selectedSuccess_antitone (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    Antitone (G.selectedSuccess strategy) := by
  intro selected selected' h
  exact G.selectedWins_mono strategy h

end Game

end

end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_ValueLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators

noncomputable section

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]

theorem value_nonnegative (G : Game Q₁ Q₂ A₁ A₂) : 0 ≤ G.value := by
  obtain ⟨strategy, h⟩ := G.exists_optimal_strategy
  rw [← h]
  exact G.success_nonnegative strategy

/-- Any fixed finite random seed merely chooses a deterministic strategy pair.
Separate private seeds are covered by taking their pair as `Seed`. -/
theorem randomized_success_le_value (G : Game Q₁ Q₂ A₁ A₂)
    {Seed : Type*} [Fintype Seed] (seedLaw : FiniteDistribution Seed)
    (strategies : Seed → Strategy Q₁ Q₂ A₁ A₂) :
    seedLaw.expectation (fun seed => G.success (strategies seed)) ≤ G.value := by
  unfold FiniteDistribution.expectation
  calc
    _ ≤ ∑ seed, seedLaw.weight seed * G.value := by
      apply Finset.sum_le_sum
      intro seed _
      exact mul_le_mul_of_nonneg_left (G.success_le_value _) (seedLaw.nonnegative seed)
    _ = G.value := by rw [← Finset.sum_mul, seedLaw.normalized, one_mul]

end Game

end

end UniqueGamesTheorem.Foundations.Games

end

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

namespace FiniteDistribution
variable {Ω Γ Q A : Type*} [Fintype Ω] [Fintype Γ] [Fintype Q] [Fintype A]

theorem table_eval_pushforward [DecidableEq Q]
    (responses : Q → FiniteDistribution A) (q₀ : Q) :
    (table responses).pushforward (fun answers => answers q₀) = responses q₀ := by
  classical
  apply eq_of_weight_eq
  intro a
  calc
    _ = (table responses).expectation
        (fun answers => if answers q₀ = a then 1 else 0) := by
      simp [pushforward, expectation, mul_ite]
    _ = (responses q₀).expectation (fun b => if b = a then 1 else 0) :=
      expectation_table_eval responses q₀ (fun b => if b = a then (1 : ℝ) else 0)
    _ = _ := by simp [expectation, mul_ite]

end FiniteDistribution

namespace Game
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem success_eq_question_expectation (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) :
    G.success strategy = G.questions.expectation
      (fun q => if G.wins strategy q then 1 else 0) := by
  simp [success, FiniteDistribution.probability,
    FiniteDistribution.expectation, mul_ite]

theorem table_success_eq_stochastic (G : Game Q₁ Q₂ A₁ A₂)
    (responses₁ : Q₁ → FiniteDistribution A₁)
    (responses₂ : Q₂ → FiniteDistribution A₂) :
    (responseTableLaw responses₁ responses₂).expectation G.success =
      G.stochasticSuccess responses₁ responses₂ := by
  classical
  unfold stochasticSuccess
  calc
    _ = (responseTableLaw responses₁ responses₂).expectation
        (fun strategy => G.questions.expectation
          (fun q => if G.wins strategy q then 1 else 0)) :=
      FiniteDistribution.expectation_congr _ (G.success_eq_question_expectation)
    _ = G.questions.expectation (fun q =>
        (responseTableLaw responses₁ responses₂).expectation
          (fun strategy => if G.wins strategy q then 1 else 0)) :=
      FiniteDistribution.expectation_comm _ _ _
    _ = _ := by
      apply FiniteDistribution.expectation_congr
      intro q
      rw [responseTableLaw, FiniteDistribution.expectation_product]
      change (FiniteDistribution.table responses₁).expectation
        (fun answers₁ => (FiniteDistribution.table responses₂).expectation
          (fun answers₂ =>
            if G.accepts q.1 q.2 (answers₁ q.1) (answers₂ q.2) then 1 else 0)) = _
      calc
        _ = (FiniteDistribution.table responses₁).expectation
            (fun answers₁ => (responses₂ q.2).expectation
              (fun b => if G.accepts q.1 q.2 (answers₁ q.1) b then 1 else 0)) := by
          apply FiniteDistribution.expectation_congr
          intro answers₁
          exact FiniteDistribution.expectation_table_eval responses₂ q.2
            (fun b => if G.accepts q.1 q.2 (answers₁ q.1) b then (1 : ℝ) else 0)
        _ = _ := FiniteDistribution.expectation_table_eval responses₁ q.1
          (fun a => (responses₂ q.2).expectation
            (fun b => if G.accepts q.1 q.2 a b then (1 : ℝ) else 0))

variable [Nonempty A₁] [Nonempty A₂]

theorem stochasticSuccess_le_value (G : Game Q₁ Q₂ A₁ A₂)
    (responses₁ : Q₁ → FiniteDistribution A₁)
    (responses₂ : Q₂ → FiniteDistribution A₂) :
    G.stochasticSuccess responses₁ responses₂ ≤ G.value := by
  classical
  rw [← G.table_success_eq_stochastic]
  exact G.randomized_success_le_value (responseTableLaw responses₁ responses₂) id

end Game
end
end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_KernelSampling
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

theorem pushforward_eq_of_agree_on_support
    {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteDistribution Ω) (f g : Ω → Γ)
    (h : ∀ x, μ.weight x ≠ 0 → f x = g x) :
    μ.pushforward f = μ.pushforward g := by
  classical
  apply eq_of_weight_eq
  intro y
  simp only [pushforward]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : μ.weight x = 0
  · simp [hx]
  · rw [h x hx]

/-- Applying separate maps to independent samples preserves their independence. -/
theorem product_pushforward
    {Ω Γ A B : Type*} [Fintype Ω] [Fintype Γ] [Fintype A] [Fintype B]
    (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ)
    (f : Ω → A) (g : Γ → B) :
    (μ.product ν).pushforward (fun z => (f z.1, g z.2)) =
      (μ.pushforward f).product (ν.pushforward g) := by
  classical
  apply eq_of_weight_eq
  rintro ⟨a, b⟩
  simp only [pushforward, product]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hx : f x = a <;> by_cases hy : g y = b <;> simp [hx, hy]

/-- Repairing table entries only off each row's support leaves its exact law intact. -/
theorem table_repair_pushforward
    {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q]
    (responses : Q → FiniteDistribution A) (repair : Q → A → A)
    (hrepair : ∀ q a, (responses q).weight a ≠ 0 → repair q a = a) (q : Q) :
    (table responses).pushforward (fun answers => repair q (answers q)) =
      responses q := by
  calc
    _ = (table responses).pushforward (fun answers => answers q) := by
      apply pushforward_eq_of_agree_on_support
      intro answers h
      exact hrepair q (answers q) (table_row_weight_ne_zero responses answers h q)
    _ = responses q := table_eval_pushforward responses q

end FiniteDistribution

namespace KernelSampling

/-- The two reads have exactly the product of the requested conditional laws. -/
theorem read_joint_pushforward {Q₁ Q₂ A B : Type*}
    [Fintype Q₁] [Fintype Q₂] [Fintype A] [Fintype B]
    [DecidableEq Q₁] [DecidableEq Q₂]
    (left : Q₁ → FiniteDistribution A) (right : Q₂ → FiniteDistribution B)
    (x : Q₁) (y : Q₂) :
    (seedLaw left right).pushforward (fun seed => (readLeft seed x, readRight seed y)) =
      (left x).product (right y) := by
  unfold seedLaw readLeft readRight
  rw [FiniteDistribution.product_pushforward
      (FiniteDistribution.table left) (FiniteDistribution.table right)
      (fun answers => answers x) (fun answers => answers y),
    FiniteDistribution.table_eval_pushforward, FiniteDistribution.table_eval_pushforward]

/-- Separate supported repairs retain the exact joint product law. -/
theorem repaired_joint_pushforward {Q₁ Q₂ A B : Type*}
    [Fintype Q₁] [Fintype Q₂] [Fintype A] [Fintype B]
    [DecidableEq Q₁] [DecidableEq Q₂]
    (left : Q₁ → FiniteDistribution A) (right : Q₂ → FiniteDistribution B)
    (repairLeft : Q₁ → A → A) (repairRight : Q₂ → B → B)
    (hleft : ∀ x a, (left x).weight a ≠ 0 → repairLeft x a = a)
    (hright : ∀ y b, (right y).weight b ≠ 0 → repairRight y b = b)
    (x : Q₁) (y : Q₂) :
    (seedLaw left right).pushforward (fun seed =>
      (repairLeft x (readLeft seed x), repairRight y (readRight seed y))) =
      (left x).product (right y) := by
  unfold seedLaw readLeft readRight
  rw [FiniteDistribution.product_pushforward
      (FiniteDistribution.table left) (FiniteDistribution.table right)
      (fun answers => repairLeft x (answers x)) (fun answers => repairRight y (answers y)),
    FiniteDistribution.table_repair_pushforward left repairLeft hleft,
    FiniteDistribution.table_repair_pushforward right repairRight hright]

section Completion

variable {I A B S : Type*} [DecidableEq I]

/-- Exact conditional completion from a finite weighted shared seed. The reads
always restore the specified coordinates, including on seeds of weight zero;
the support hypotheses ensure that this repair preserves the requested laws. -/
theorem completed_joint_pushforward
    [Fintype I] [Fintype A] [Fintype B] [Fintype S]
    [DecidableEq A] [DecidableEq B] [DecidableEq S]
    (left : (A × S) → FiniteDistribution (I → A))
    (right : (B × S) → FiniteDistribution (I → B)) (j : I)
    (hleft : ∀ q xs, (left q).weight xs ≠ 0 → xs j = q.1)
    (hright : ∀ q ys, (right q).weight ys ≠ 0 → ys j = q.1)
    (x : A × S) (y : B × S) :
    (seedLaw left right).pushforward
        (fun seed => (completedLeft j seed x, completedRight j seed y)) =
      (left x).product (right y) := by
  apply repaired_joint_pushforward left right
    (fun q xs => Function.update xs j q.1) (fun q ys => Function.update ys j q.1)
  · intro q xs h
    exact update_eq_of_coordinate xs j q.1 (hleft q xs h)
  · intro q ys h
    exact update_eq_of_coordinate ys j q.1 (hright q ys h)

end Completion

end KernelSampling
end
end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_SamplingLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Coordinate reindexing for actual finite distributions and repeated games.
The joint questions are iid across coordinates; coordinate-success events
need not be independent. Strategies permute each player's local questions
and answers, so the resulting strategies remain local.
-/

noncomputable section

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators

namespace FiniteDistribution

theorem pushforward_equiv {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteDistribution Ω) (e : Ω ≃ Γ) :
    μ.pushforward e = μ.transport e := by
  classical
  apply eq_of_weight_eq
  intro y
  simp only [pushforward, transport]
  have he : ∀ x : Ω, (e x = y) = (x = e.symm y) := by
    intro x
    apply propext
    constructor
    · intro h
      simpa using congrArg e.symm h
    · intro h
      rw [h, e.apply_symm_apply]
  simp_rw [he]
  simp

end FiniteDistribution

end UniqueGamesTheorem.Foundations.Games

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_SharedProfiles
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

variable {Q₁ Q₂ S : Type*} [Fintype Q₁] [Fintype Q₂] [Fintype S]

theorem sharedProfileReject_nonnegative [Nonempty S]
    (L : Q₁ → Games.FiniteDistribution S) (R : Q₂ → Games.FiniteDistribution S)
    (x : Q₁) (y : Q₂) : 0 ≤ sharedProfileReject L R x y := by
  exact eventMass_nonneg _ _
    (rectangleDistribution (α := S) (sharedProfileThresholds L R)).nonnegative

theorem sharedProfile_reject_le_rate [Nonempty S]
    (L : Q₁ → Games.FiniteDistribution S) (R : Q₂ → Games.FiniteDistribution S)
    (x : Q₁) (y : Q₂) : sharedProfileReject L R x y ≤ uniformRejectionRate S := by
  let thresholds := sharedProfileThresholds L R
  have hsum : (∑ s : RectangleSeed thresholds S, rectangleWeight thresholds s) = 1 :=
    (rectangleDistribution (α := S) thresholds).normalized
  have hcomp := eventMass_complement (rectangleWeight thresholds)
    (fun s => sharedProfileLeft L R x s || sharedProfileRight L R y s) hsum
  have hu : eventMass (rectangleWeight thresholds)
      (fun s => sharedProfileLeft L R x s || sharedProfileRight L R y s) =
      (1 + totalVariation (L x).weight (R y).weight) / (Fintype.card S : ℝ) := by
    change eventMass (rectangleWeight thresholds)
      (fun s => rectangleAccept thresholds (L x).weight s ||
        rectangleAccept thresholds (R y).weight s) = _
    rw [rectangle_union_mass thresholds (L x).weight (R y).weight
      (left_mem_sharedProfileThresholds L R x)
      (right_mem_sharedProfileThresholds L R y)
      (L x).nonnegative (R y).nonnegative
      (distribution_weight_le_one (L x)) (distribution_weight_le_one (R y))]
    rw [unionMass_eq (L x).weight (R y).weight (L x).normalized (R y).normalized]
  have hc : (0 : ℝ) < Fintype.card S := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have htv := totalVariation_nonneg (L x).weight (R y).weight
  have hquot : 1 / (Fintype.card S : ℝ) ≤
      (1 + totalVariation (L x).weight (R y).weight) / (Fintype.card S : ℝ) :=
    (div_le_div_iff_of_pos_right hc).2 (by linarith)
  rw [hu] at hcomp
  change eventMass (rectangleWeight thresholds)
    (fun s => !(sharedProfileLeft L R x s || sharedProfileRight L R y s)) ≤
      1 - 1 / (Fintype.card S : ℝ)
  linarith

end

end UniqueGamesTheorem.Foundations.CorrelatedSampling

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_FactorizationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

/-- Any finite shared-randomness local embedding yields a valid base-game
strategy after the seed is fixed. Total variation pays exactly for changing
the resulting question distribution to the desired one. -/
theorem success_le_value_add_embedding_distance
    (G : Game Q₁ Q₂ A₁ A₂) (H : Game R₁ R₂ B₁ B₂)
    (seedLaw : FiniteDistribution Seed)
    (left : Seed → Q₁ → R₁) (right : Seed → Q₂ → R₂)
    (answerLeft : Seed → Q₁ → B₁ → A₁)
    (answerRight : Seed → Q₂ → B₂ → A₂)
    (acceptance : ∀ seed x y a b,
      H.accepts (left seed x) (right seed y) a b = true →
      G.accepts x y (answerLeft seed x a) (answerRight seed y b) = true)
    (strategy : Strategy R₁ R₂ B₁ B₂) :
    H.success strategy ≤ G.value +
      H.questions.totalVariation (G.localEmbeddingLaw seedLaw left right) := by
  have localBound (seed : Seed) :
      (G.questions.pushforward (fun q => (left seed q.1, right seed q.2))).probability
        (H.wins strategy) ≤ G.value := by
    let embedded : Game R₁ R₂ B₁ B₂ :=
      { questions := G.questions.pushforward fun q => (left seed q.1, right seed q.2)
        accepts := H.accepts }
    change embedded.success strategy ≤ G.value
    exact (G.success_le_of_localSimulation embedded (left seed) (right seed)
      (answerLeft seed) (answerRight seed) rfl (acceptance seed) strategy).trans
      (G.success_le_value _)
  have mixtureBound :
      (G.localEmbeddingLaw seedLaw left right).probability (H.wins strategy) ≤ G.value :=
    seedLaw.probability_mixture_le _ _ _ localBound
  exact (H.questions.probability_le_add_totalVariation
    (G.localEmbeddingLaw seedLaw left right) (H.wins strategy)).trans
    (add_le_add mixtureBound (le_refl _))

/-- The strategy-extraction step used for a surviving coordinate after
conditioning on successes at other coordinates. It preserves full local
question dependence and uses no independence assumption on the target law. -/
theorem coordinate_probability_le_value_add_embedding_distance
    (G : Game Q₁ Q₂ A₁ A₂) {n : Nat} (coordinate : Fin n)
    (law : FiniteDistribution ((Fin n → Q₁) × (Fin n → Q₂)))
    (seedLaw : FiniteDistribution Seed)
    (left : Seed → Q₁ → Fin n → Q₁) (right : Seed → Q₂ → Fin n → Q₂)
    (left_preserves : ∀ seed x, left seed x coordinate = x)
    (right_preserves : ∀ seed y, right seed y coordinate = y)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    law.probability (G.coordinateWin strategy coordinate) ≤ G.value +
      law.totalVariation (G.localEmbeddingLaw seedLaw left right) := by
  apply G.success_le_value_add_embedding_distance (G.coordinateGame coordinate law)
    seedLaw left right (fun _ _ a => a coordinate) (fun _ _ b => b coordinate)
  intro seed x y a b h
  simpa only [coordinateGame, left_preserves, right_preserves] using h

end
end UniqueGamesTheorem.Foundations.Games.Game

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_FinishBoundsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
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

theorem pushforward_comp (μ : FiniteDistribution A) (f : A → B) (g : B → C) :
    (μ.pushforward f).pushforward g = μ.pushforward (fun a => g (f a)) := by
  classical
  apply eq_of_weight_eq
  intro c
  rw [weight_eq_probability_singleton, weight_eq_probability_singleton]
  simp only [probability_pushforward]

theorem transport_eq_pushforward (μ : FiniteDistribution A) (e : A ≃ B) :
    μ.transport e = μ.pushforward e := by
  classical
  apply eq_of_weight_eq
  intro b
  rw [weight_eq_probability_singleton, weight_eq_probability_singleton,
    probability_transport, probability_pushforward]

end
end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_SelectedInformationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

theorem iid_coordinate_split {Ω : Type*} [Fintype Ω] {n : Nat}
    (μ : FiniteDistribution Ω) (selected : Finset (Fin n)) :
    (μ.iid n).transport (coordinateSplitEquiv selected) =
      (FiniteDistribution.table (fun _ : selected => μ)).product
        (FiniteDistribution.table (fun _ : {i : Fin n // i ∉ selected} => μ)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change (∏ i, μ.weight (mergeCoordinates selected x.1 x.2 i)) =
    (∏ i : selected, μ.weight (x.1 i)) *
      ∏ i : {i : Fin n // i ∉ selected}, μ.weight (x.2 i)
  have h := Fintype.prod_subtype_mul_prod_subtype (fun i : Fin n => i ∈ selected)
    (fun i => μ.weight (mergeCoordinates selected x.1 x.2 i))
  have hi : Subtype.fintype (fun i : Fin n => i ∈ selected) =
      Finset.Subtype.fintype selected := Subsingleton.elim _ _
  rw [hi] at h
  calc
    _ = (∏ i : {i : Fin n // i ∈ selected},
        μ.weight (mergeCoordinates selected x.1 x.2 i.1)) *
        ∏ i : {i : Fin n // i ∉ selected},
          μ.weight (mergeCoordinates selected x.1 x.2 i.1) := h.symm
    _ = _ := by
      congr 1 <;> apply Finset.prod_congr rfl <;> intro i _ <;>
        simp [mergeCoordinates, i.property]

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]
  {n : Nat}

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedSplit_probability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) :
    (selectedSplitLaw G selected).probability
      (fun q => G.selectedWins strategy selected (selectedQuestionTuple selected q.1 q.2)) =
        G.selectedSuccess strategy selected := by
  rw [selectedSplitLaw, ← iid_coordinate_split, FiniteDistribution.probability_transport]
  change (G.questions.iid n).probability _ =
    ((G.questions.iid n).transport (Game.tupleQuestionEquiv n)).probability _
  rw [FiniteDistribution.probability_transport]
  apply congrArg (G.questions.iid n).probability
  funext q
  congr 1
  apply Prod.ext <;> funext i <;>
    simp [selectedQuestionTuple, coordinateSplitEquiv, mergeCoordinates, Game.tupleQuestionEquiv]

/-- The side-information normalizer is the actual selected-win probability
of the repeated strategy. No event-mass hypothesis is required. -/
theorem selectedSideMass_total (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) :
    (∑ tv, (selectedInputLaw G selected).weight tv.1 *
      selectedSideMass G strategy selected tv) = G.selectedSuccess strategy selected := by
  classical
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, selectedSideMass_sum]
  rw [Fintype.sum_prod_type]
  simp only [selectedInputLaw, FiniteDistribution.product, FiniteDistribution.table,
    selectedInputProfile, independentProduct]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  have hforget (fixed : selected → Q₁ × Q₂) :=
    reveal_product_expectation G.questions
      (fun u : {i : Fin n // i ∉ selected} → Q₁ × Q₂ =>
        if G.selectedWins strategy selected (selectedQuestionTuple selected fixed u)
        then (1 : ℝ) else 0)
  simp_rw [hforget]
  have h := selectedSplit_probability G strategy selected
  simpa [selectedSplitLaw, FiniteDistribution.probability, FiniteDistribution.product,
    FiniteDistribution.table, Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_assoc] using h

theorem selected_information_bound [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ i : {i : Fin n // i ∉ selected}, totalVariation
      (fun tva : (SelectedInput Q₁ Q₂ selected ×
        SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) × (Q₁ × Q₂) =>
        selectedSideWeight G strategy selected tva.1 * coordinateMarginal
          (posteriorOrOriginal
            (independentProduct (fun j => (selectedInputProfile G selected tva.1.1 j).weight))
            (selectedLikelihood G strategy selected tva.1.1.1 tva.1.2)
            (selectedSideMass G strategy selected tva.1)) i tva.2)
      (fun tva => selectedSideWeight G strategy selected tva.1 *
        (selectedInputProfile G selected tva.1.1 i).weight tva.2)) ≤
      Real.sqrt ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
        (Real.log (Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ) +
          Real.log (1 / G.selectedSuccess strategy selected))) := by
  exact finite_side_information_bound (selectedInputLaw G selected).weight
    (fun t i => (selectedInputProfile G selected t i).weight)
    (fun tv => selectedLikelihood G strategy selected tv.1.1 tv.2)
    (selectedSideMass G strategy selected) (selectedSideWeight G strategy selected)
    (gameLaw_isProbability _) (fun t i => gameLaw_isProbability _)
    (fun tv => selectedLikelihood_nonnegative G strategy selected tv.1.1 tv.2)
    (fun t => selectedLikelihood_sum_le_one G strategy selected t.1)
    (fun _ => rfl) positive (selectedSideMass_total G strategy selected) (fun _ => rfl)

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

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedTupleLikelihood_mass (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) :
    (∑ questions, independentProduct (fun _ : Fin n => G.questions.weight) questions *
      selectedTupleLikelihood G strategy selected questions) =
        G.selectedSuccess strategy selected := by
  classical
  change _ = ((G.questions.iid n).transport (Game.tupleQuestionEquiv n)).probability
    (G.selectedWins strategy selected)
  rw [FiniteDistribution.probability_transport]
  simp only [FiniteDistribution.probability, FiniteDistribution.iid, independentProduct,
    selectedTupleLikelihood, mul_ite, mul_one, mul_zero]

/-- The full-coordinate squared-distance bound specialized to the actual game
and actual selected event. -/
theorem selectedQuestionMarginal_totalVariation_sq_sum_le_log
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ i : Fin n,
      (selectedQuestionMarginal G strategy selected positive i).totalVariation G.questions ^ 2) ≤
        Real.log (1 / G.selectedSuccess strategy selected) := by
  classical
  change (∑ i : Fin n, Information.totalVariation
    (selectedQuestionMarginal G strategy selected positive i).weight G.questions.weight ^ 2) ≤ _
  simp_rw [selectedQuestionMarginal_weight]
  exact posterior_coordinate_totalVariation_sq_sum_le_log
    (fun _ : Fin n => G.questions.weight) (fun _ => gameLaw_isProbability G.questions)
    (selectedTupleLikelihood G strategy selected)
    (selectedTupleLikelihood_nonnegative G strategy selected)
    (selectedTupleLikelihood_le_one G strategy selected)
    positive (selectedTupleLikelihood_mass G strategy selected)

/-- Restricting to the unused coordinates does not spend any further
information budget. -/
theorem unselectedQuestionMarginal_totalVariation_sq_sum_le_log
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ i : {i : Fin n // i ∉ selected},
      (selectedQuestionMarginal G strategy selected positive i.1).totalVariation G.questions ^ 2) ≤
        Real.log (1 / G.selectedSuccess strategy selected) := by
  classical
  let d : Fin n → ℝ := fun i =>
    (selectedQuestionMarginal G strategy selected positive i).totalVariation G.questions
  have hfull := selectedQuestionMarginal_totalVariation_sq_sum_le_log G strategy selected positive
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun i : Fin n => i ∈ selected)
    (fun i => d i ^ 2)
  have hinst : Subtype.fintype (fun i : Fin n => i ∈ selected) =
      Finset.Subtype.fintype selected := Subsingleton.elim _ _
  rw [hinst] at hsplit
  have hselected : 0 ≤ ∑ i : {i : Fin n // i ∈ selected}, d i.1 ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  change (∑ i : {i : Fin n // i ∉ selected}, d i.1 ^ 2) ≤ _
  change (∑ i : Fin n, d i ^ 2) ≤ _ at hfull
  linarith

/-- The marginal-pair term used in Holenstein's dependency-breaking argument.
The estimate is valid also when there are no unused coordinates. -/
theorem unselectedQuestionMarginal_totalVariation_sum_le_sqrt
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ i : {i : Fin n // i ∉ selected},
      (selectedQuestionMarginal G strategy selected positive i.1).totalVariation G.questions) ≤
        Real.sqrt ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
          Real.log (1 / G.selectedSuccess strategy selected)) := by
  classical
  let d : {i : Fin n // i ∉ selected} → ℝ := fun i =>
    (selectedQuestionMarginal G strategy selected positive i.1).totalVariation G.questions
  have hsq := unselectedQuestionMarginal_totalVariation_sq_sum_le_log G strategy selected positive
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset {i : Fin n // i ∉ selected}) d (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hcs
  have hln : 0 ≤ Real.log (1 / G.selectedSuccess strategy selected) :=
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)).trans hsq
  have hcard : 0 ≤ (Fintype.card {i : Fin n // i ∉ selected} : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hsq hcard
  have hsqrt := Real.sq_sqrt (mul_nonneg hcard hln)
  have hsqrtpos := Real.sqrt_nonneg
    ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
      Real.log (1 / G.selectedSuccess strategy selected))
  change (∑ i, d i) ≤ _
  change (∑ i, d i ^ 2) ≤ _ at hsq
  change (Fintype.card {i : Fin n // i ∉ selected} : ℝ) * (∑ i, d i ^ 2) ≤ _ at hmul
  nlinarith

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

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedJointWeight_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (z) : 0 ≤ selectedJointWeight G strategy selected z := by
  apply div_nonneg
  · exact mul_nonneg
      (mul_nonneg ((selectedInputLaw G selected).nonnegative _)
        ((independentProduct_isProbability _
          (fun i => gameLaw_isProbability (selectedInputProfile G selected z.1.1 i))).1 z.2))
      (selectedLikelihood_nonnegative G strategy selected z.1.1.1 z.1.2 z.2)
  · exact G.selectedSuccess_nonnegative strategy selected

theorem selectedJointWeight_isProbability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    IsProbability (selectedJointWeight G strategy selected) := by
  constructor
  · exact selectedJointWeight_nonnegative G strategy selected
  · rw [Fintype.sum_prod_type]
    change (∑ tv, firstMarginal (selectedJointWeight G strategy selected) tv) = 1
    simp_rw [selectedJointWeight_firstMarginal, selectedSideWeight, div_eq_mul_inv]
    rw [← Finset.sum_mul, selectedSideMass_total, mul_inv_cancel₀ positive.ne']

def selectedJointLaw (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :=
  toGameLaw (selectedJointWeight G strategy selected)
    (selectedJointWeight_isProbability G strategy selected positive)

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-!
Identification of the auxiliary selected-answer/reveal law with the actual
repeated-game question law conditioned on selected-coordinate success.
The proof sums out answer labels and reveal variables before merging the
selected and unselected question coordinates.
-/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators
open Games Information
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedSplit_question_probability (G : Game Q₁ Q₂ A₁ A₂)
    (selected : Finset (Fin n))
    (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    (selectedSplitLaw G selected).probability
      (fun q => event (selectedQuestionTuple selected q.1 q.2)) =
        (G.repetition n).questions.probability event := by
  rw [selectedSplitLaw, ← iid_coordinate_split, FiniteDistribution.probability_transport]
  change (G.questions.iid n).probability _ =
    ((G.questions.iid n).transport (Game.tupleQuestionEquiv n)).probability event
  rw [FiniteDistribution.probability_transport]
  apply congrArg (G.questions.iid n).probability
  funext q
  congr 1
  apply Prod.ext <;> funext i <;>
    simp [selectedQuestionTuple, coordinateSplitEquiv, mergeCoordinates, Game.tupleQuestionEquiv]

/-- Marginalizing the actual likelihood against any question event gives
the joint probability of selected-coordinate success and that event. -/
theorem selectedJoint_eventMass (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    (∑ tv : SelectedInput Q₁ Q₂ selected ×
        SelectedLabels (A₁ := A₁) (A₂ := A₂) selected,
      (selectedInputLaw G selected).weight tv.1 *
        ∑ u, independentProduct
          (fun i => (selectedInputProfile G selected tv.1 i).weight) u *
            selectedLikelihood G strategy selected tv.1.1 tv.2 u *
              (if event (selectedQuestionTuple selected tv.1.1 u) then 1 else 0)) =
      (G.repetition n).questions.probability
        (fun q => G.selectedWins strategy selected q && event q) := by
  classical
  have hlabel (t : SelectedInput Q₁ Q₂ selected) :
      (∑ v, ∑ u, independentProduct
        (fun i => (selectedInputProfile G selected t i).weight) u *
          selectedLikelihood G strategy selected t.1 v u *
            (if event (selectedQuestionTuple selected t.1 u) then 1 else 0)) =
      ∑ u, independentProduct
        (fun i => (selectedInputProfile G selected t i).weight) u *
          (if G.selectedWins strategy selected (selectedQuestionTuple selected t.1 u) &&
            event (selectedQuestionTuple selected t.1 u) then 1 else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    rw [← Finset.sum_mul, ← Finset.mul_sum, selectedLikelihood_sum]
    cases hw : G.selectedWins strategy selected (selectedQuestionTuple selected t.1 u) <;>
      cases he : event (selectedQuestionTuple selected t.1 u) <;> simp
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, hlabel]
  rw [Fintype.sum_prod_type]
  simp only [selectedInputLaw, FiniteDistribution.product, FiniteDistribution.table,
    selectedInputProfile, independentProduct]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  have hforget (fixed : selected → Q₁ × Q₂) :=
    reveal_product_expectation G.questions
      (fun u : {i : Fin n // i ∉ selected} → Q₁ × Q₂ =>
        if G.selectedWins strategy selected (selectedQuestionTuple selected fixed u) &&
          event (selectedQuestionTuple selected fixed u) then (1 : ℝ) else 0)
  simp_rw [hforget]
  have h := selectedSplit_question_probability G selected
    (fun q => G.selectedWins strategy selected q && event q)
  simpa [selectedSplitLaw, FiniteDistribution.probability, FiniteDistribution.product,
    FiniteDistribution.table, Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_assoc] using h

theorem selectedJointLaw_question_probability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    (selectedJointLaw G strategy selected positive).probability
      (fun z => event (selectedQuestionTuple selected z.1.1.1 z.2)) =
        ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).probability
          event := by
  classical
  erw [FiniteDistribution.probability_condition]
  change
    (∑ z : (SelectedInput Q₁ Q₂ selected ×
        SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
          ({i : Fin n // i ∉ selected} → Q₁ × Q₂),
      if event (selectedQuestionTuple selected z.1.1.1 z.2)
      then selectedJointWeight G strategy selected z else 0) =
        (G.repetition n).questions.probability
          (fun q => G.selectedWins strategy selected q && event q) /
            G.selectedSuccess strategy selected
  calc
    _ = (∑ tv : SelectedInput Q₁ Q₂ selected ×
          SelectedLabels (A₁ := A₁) (A₂ := A₂) selected,
        (selectedInputLaw G selected).weight tv.1 *
          ∑ u, independentProduct
            (fun i => (selectedInputProfile G selected tv.1 i).weight) u *
              selectedLikelihood G strategy selected tv.1.1 tv.2 u *
                (if event (selectedQuestionTuple selected tv.1.1 u) then 1 else 0)) /
        G.selectedSuccess strategy selected := by
      conv_lhs => rw [Fintype.sum_prod_type]
      simp only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro tv _
      apply Finset.sum_congr rfl
      intro u _
      cases he : event (selectedQuestionTuple selected tv.1.1 u) <;>
        simp [selectedJointWeight, div_eq_mul_inv, mul_assoc]
    _ = _ := by rw [selectedJoint_eventMass]

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_PartialRevealLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

theorem selectedRawMarginal_isProbability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    IsProbability (selectedRawMarginal G strategy selected j) := by
  classical
  constructor
  · intro z
    apply Finset.sum_nonneg
    intro u _
    split
    · exact selectedJointWeight_nonnegative G strategy selected (z.1,u)
    · exact le_rfl
  · rw [Fintype.sum_prod_type]
    change (∑ tv, firstMarginal (selectedRawMarginal G strategy selected j) tv) = 1
    simp_rw [selectedRawMarginal_firstMarginal, selectedSideWeight, div_eq_mul_inv]
    rw [← Finset.sum_mul, selectedSideMass_total, mul_inv_cancel₀ positive.ne']

theorem selected_raw_information_bound [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected}, totalVariation
      (selectedRawMarginal G strategy selected j)
      (fun z => selectedSideWeight G strategy selected z.1 *
        (selectedInputProfile G selected z.1.1 j).weight z.2)) ≤
      Real.sqrt ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
        (Real.log (Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ) +
          Real.log (1 / G.selectedSuccess strategy selected))) := by
  have h := selected_information_bound G strategy selected positive
  simp_rw [selectedPosterior_eq_raw] at h
  exact h

theorem selected_fullReveal_information_bound [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected},
      totalVariation (fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected))) ≤
      Real.sqrt ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
        (Real.log (Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ) +
          Real.log (1 / G.selectedSuccess strategy selected))) := by
  have h := selected_raw_information_bound G strategy selected positive
  simp_rw [selected_raw_error_eq_fullReveal] at h
  exact h

theorem selected_leftReveal_error_sum [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected},
      totalVariation (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (leftRevealModel G.questions
          (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected)))) ≤
      2 * selectedInformationRadius G strategy selected := by
  calc
    _ ≤ ∑ j : {i : Fin n // i ∉ selected},
        2 * totalVariation (fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
          (fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected)) := by
      apply Finset.sum_le_sum
      intro j _
      exact leftReveal_full_error G.questions j _
    _ = 2 * ∑ j : {i : Fin n // i ∉ selected},
        totalVariation (fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
          (fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (selected_fullReveal_information_bound G strategy selected positive) (by norm_num)

theorem selected_rightReveal_error_sum [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected},
      totalVariation (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (rightRevealModel G.questions
          (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected)))) ≤
      2 * selectedInformationRadius G strategy selected := by
  calc
    _ ≤ ∑ j : {i : Fin n // i ∉ selected},
        2 * totalVariation (fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
          (fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected)) := by
      apply Finset.sum_le_sum
      intro j _
      exact rightReveal_full_error G.questions j _
    _ = 2 * ∑ j : {i : Fin n // i ∉ selected},
        totalVariation (fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
          (fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (selected_fullReveal_information_bound G strategy selected positive) (by norm_num)

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

omit [DecidableEq Q₁] [DecidableEq Q₂] in
/-- The actual selected-label radius is bounded by the base-two alphabet
budget. The unused-coordinate factor is a real subtraction, as in the scalar
recurrence. -/
theorem selectedInformationRadius_le [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (ell : ℝ)
    (hell : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell) :
    selectedInformationRadius G strategy selected ≤
      Real.sqrt (((n : ℝ) - selected.card) *
        ((selected.card : ℝ) * ell + logTwo (1 / G.selectedSuccess strategy selected))) := by
  have hprob : 1 ≤ 1 / G.selectedSuccess strategy selected := by
    apply (le_div_iff₀ positive).2
    simpa using G.selectedSuccess_le_one strategy selected
  have hbudget := add_le_add (selectedLabels_log_le (A₁ := A₁) (A₂ := A₂) selected ell hell)
    (log_le_logTwo hprob)
  unfold selectedInformationRadius
  rw [← unusedCoordinates_card_real selected]
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg _)

omit [DecidableEq Q₁] [DecidableEq Q₂] in
/-- An actual finite average over all unused coordinates yields the numerical
bound needed by the selected-success recurrence. No sign condition on the
individual errors is required. -/
theorem exists_coordinate_le_information_budget [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (ell : ℝ)
    (hell : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell)
    (hselected : selected.card < n)
    (error : {i : Fin n // i ∉ selected} → ℝ)
    (hsum : (∑ j, error j) ≤ 15 * selectedInformationRadius G strategy selected) :
    ∃ j : {i : Fin n // i ∉ selected}, error j ≤ 15 * Real.sqrt
      (((selected.card : ℝ) * ell + logTwo (1 / G.selectedSuccess strategy selected)) /
        ((n : ℝ) - selected.card)) := by
  classical
  have hcard : 0 < Fintype.card {i : Fin n // i ∉ selected} := by
    rw [unusedCoordinates_card]
    exact Nat.sub_pos_of_lt hselected
  let : Nonempty {i : Fin n // i ∉ selected} := Fintype.card_pos_iff.mp hcard
  have hden : 0 < (n : ℝ) - selected.card := by
    rw [← unusedCoordinates_card_real selected]
    exact_mod_cast hcard
  have htotal := hsum.trans (mul_le_mul_of_nonneg_left
    (selectedInformationRadius_le G strategy selected positive ell hell) (by norm_num : (0 : ℝ) ≤ 15))
  rw [sqrt_budget_factor _ _ hden] at htotal
  have havg : (∑ j, error j) ≤ ∑ _j : {i : Fin n // i ∉ selected},
      15 * Real.sqrt
        (((selected.card : ℝ) * ell + logTwo (1 / G.selectedSuccess strategy selected)) /
          ((n : ℝ) - selected.card)) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      unusedCoordinates_card_real, mul_assoc, mul_left_comm] using htotal
  obtain ⟨j, _, hj⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty havg
  exact ⟨j, hj⟩

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

theorem selected_fullReveal_isProbability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    IsProbability (fullRevealMarginal G.questions j
      (selectedOutsideLikelihood G strategy selected)) := by
  have h := isProbability_comp_equiv
    (selectedObservationEquiv (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected).symm
    _ (selectedRawMarginal_isProbability G strategy selected positive j)
  have he : (fun z => selectedRawMarginal G strategy selected j
      ((selectedObservationEquiv (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected).symm z)) =
      fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected) := by
    funext z
    exact selectedRawMarginal_fullReveal G strategy selected j z
  rw [he] at h
  exact h

def selectedCommonLaw (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j × (Q₁ × Q₂)) :=
  toGameLaw (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
    (partialRevealMarginal_isProbability G.questions j _
      (selected_fullReveal_isProbability G strategy selected positive j))

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

theorem swap_question_pushforward_snd (μ : FiniteDistribution (X × Y)) :
    ((μ.transport (Equiv.prodComm X Y)).pushforward Prod.snd) = μ.pushforward Prod.fst := by
  rw [FiniteDistribution.transport_eq_pushforward, FiniteDistribution.pushforward_comp]
  rfl

omit [Fintype S] in
theorem leftRevealModel_swap [DecidableEq X] [DecidableEq Y]
    (p : S × (X × Y) → ℝ) (μ : FiniteDistribution (X × Y)) (z : S × (Y × X)) :
    leftRevealModel (μ.transport (Equiv.prodComm X Y))
      (fun z => p (swapQuestionEndpoints z)) z = rightRevealModel μ p (swapQuestionEndpoints z) := by
  rcases z with ⟨s,y,x⟩
  change (∑ x', p (s,(x',y))) *
      (revealProfile (μ.transport (Equiv.prodComm X Y)) (Sum.inl y)).weight (y,x) =
    (∑ x', p (s,(x',y))) * (revealProfile μ (Sum.inr y)).weight (x,y)
  rw [revealProfile_inl_diagonal, revealProfile_inr_diagonal, swap_question_pushforward_snd]

theorem rightCommonProfile_error [DecidableEq X] [DecidableEq Y]
    (p : S × (X × Y) → ℝ) (μ : FiniteDistribution (X × Y)) (fallback : S → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback) :
    totalVariation p (fun z => μ.weight z.2 * rightCommonProfile p fallback z.2.2 z.1) ≤
      totalVariation p (rightRevealModel μ p) + totalVariation (secondMarginal p) μ.weight := by
  let e := swapQuestionEndpoints (S := S) (X := X) (Y := Y)
  let p' : S × (Y × X) → ℝ := fun z => p (e z)
  let μ' := μ.transport (Equiv.prodComm X Y)
  have h := leftCommonProfile_error p' μ' fallback (isProbability_comp_equiv e p hp) hf
  have hc : leftRevealModel μ' p' = fun z => rightRevealModel μ p (e z) := by
    funext z
    exact leftRevealModel_swap p μ z
  have hd : (fun z : S × (Y × X) => μ'.weight z.2 * leftCommonProfile p' fallback z.2.1 z.1) =
      fun z => μ.weight (e z).2 * rightCommonProfile p fallback (e z).2.2 (e z).1 := rfl
  rw [hc, hd] at h
  change totalVariation (fun z => p (e z)) _ ≤
    totalVariation (fun z => p (e z)) _ + _ at h
  rw [totalVariation_comp_equiv e p (rightRevealModel μ p)] at h
  rw [totalVariation_comp_equiv e p
    (fun z => μ.weight z.2 * rightCommonProfile p fallback z.2.2 z.1)] at h
  have hm : totalVariation (secondMarginal p') μ'.weight =
      totalVariation (secondMarginal p) μ.weight := by
    change totalVariation (fun yx => secondMarginal p ((Equiv.prodComm Y X) yx))
      (fun yx => μ.weight ((Equiv.prodComm Y X) yx)) = _
    exact totalVariation_comp_equiv (Equiv.prodComm Y X) _ _
  rw [hm] at h
  exact h

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_SelectedCommonMarginalLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

theorem selectedRawMarginal_secondMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    secondMarginal (selectedRawMarginal G strategy selected j) =
      (selectedQuestionMarginal G strategy selected positive j.1).weight := by
  classical
  funext q
  calc
    _ = (selectedJointLaw G strategy selected positive).probability
        (fun z => decide (z.2 j = q)) := by
      simp only [secondMarginal, selectedRawMarginal, FiniteDistribution.probability,
        selectedJointLaw, toGameLaw, Fintype.sum_prod_type, decide_eq_true_eq]
    _ = ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).probability
        (fun questions => decide ((questions.1 j.1,questions.2 j.1) = q)) := by
      have h := selectedJointLaw_question_probability G strategy selected positive
        (fun questions => decide ((questions.1 j.1,questions.2 j.1) = q))
      simpa [selectedQuestionTuple, mergeCoordinates, j.property] using h
    _ = _ := by
      rw [FiniteDistribution.weight_eq_probability_singleton, selectedQuestionMarginal,
        FiniteDistribution.probability_pushforward]

/-- The exact marginal identification needed to use the conditioned-question
information bound in the two local common-data profile errors. -/
theorem selectedCommonLaw_secondMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    secondMarginal (selectedCommonLaw G strategy selected positive j).weight =
      (selectedQuestionMarginal G strategy selected positive j.1).weight := by
  change secondMarginal (partialRevealMarginal G.questions j
    (selectedOutsideLikelihood G strategy selected)) = _
  rw [partialRevealMarginal_secondMarginal, selectedFullReveal_secondMarginal]
  exact selectedRawMarginal_secondMarginal G strategy selected positive j

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

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

theorem selectedCommonLaw_completion_row_mass (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (xy : Q₁ × Q₂) :
    (selectedCommonLaw G strategy selected positive j).weight (s,xy) =
      ∑ lr : ({i : Fin n // i ∉ selected} → Q₁) ×
          ({i : Fin n // i ∉ selected} → Q₂),
        selectedCompletionScale G strategy selected j s xy *
          selectedLeftRaw G strategy selected j s xy.1 lr.1 *
          selectedRightRaw G strategy selected j s xy.2 lr.2 := by
  classical
  change (∑ u, if u j = xy then partialRevealWeight G.questions j s.2 u *
    selectedOutsideLikelihood G strategy selected s.1 u else 0) = _
  rw [← (completionTupleEquiv (I := {i : Fin n // i ∉ selected})
    (X := Q₁) (Y := Q₂)).sum_comp]
  apply Finset.sum_congr rfl
  intro u _
  exact (selected_completion_factorization G strategy selected j s xy
    (fun i => (u i).1) (fun i => (u i).2)).symm

/-- Actual common-row mass times the two local completion probabilities is
the selected partial-reveal weight with its actual coordinate indicator. -/
theorem selected_completion_row_recombine (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (xy : Q₁ × Q₂)
    (l : {i : Fin n // i ∉ selected} → Q₁)
    (r : {i : Fin n // i ∉ selected} → Q₂) :
    (selectedCommonLaw G strategy selected positive j).weight (s,xy) *
      ((selectedLeftCompletion G strategy selected j s xy.1).product
        (selectedRightCompletion G strategy selected j s xy.2)).weight (l,r) =
      if (l j,r j) = xy then
        partialRevealWeight G.questions j s.2 (fun i => (l i,r i)) *
          selectedOutsideLikelihood G strategy selected s.1 (fun i => (l i,r i))
      else 0 := by
  rw [selectedCommonLaw_completion_row_mass]
  calc
    _ = selectedCompletionScale G strategy selected j s xy *
        selectedLeftRaw G strategy selected j s xy.1 l *
        selectedRightRaw G strategy selected j s xy.2 r :=
      factorized_completion_row
        (selectedLeftRaw G strategy selected j s xy.1)
        (selectedRightRaw G strategy selected j s xy.2)
        (selectedLeftRaw_nonnegative G strategy selected j s xy.1)
        (selectedRightRaw_nonnegative G strategy selected j s xy.2)
        (updatedTableFallback (G.questions.pushforward Prod.fst) j xy.1)
        (updatedTableFallback (G.questions.pushforward Prod.snd) j xy.2)
        (selectedCompletionScale G strategy selected j s xy) (l,r)
    _ = _ := selected_completion_factorization G strategy selected j s xy l r

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

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedOutsideLikelihood_event_sum (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    (∑ t : (selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected,
      ∑ u : {i : Fin n // i ∉ selected} → Q₁ × Q₂,
        (∏ i, G.questions.weight (u i)) * selectedOutsideLikelihood G strategy selected t u *
          (if event (selectedQuestionTuple selected t.1 u) then 1 else 0)) =
      (G.repetition n).questions.probability
        (fun q => G.selectedWins strategy selected q && event q) /
          G.selectedSuccess strategy selected := by
  classical
  have hlabel (fixed : selected → Q₁ × Q₂)
      (u : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
      (∑ label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected,
        (∏ i, G.questions.weight (u i)) *
          selectedOutsideLikelihood G strategy selected (fixed,label) u *
            (if event (selectedQuestionTuple selected fixed u) then 1 else 0)) =
      ((∏ i : selected, G.questions.weight (fixed i)) * (∏ i, G.questions.weight (u i)) *
        (if G.selectedWins strategy selected (selectedQuestionTuple selected fixed u) &&
          event (selectedQuestionTuple selected fixed u) then 1 else 0)) /
            G.selectedSuccess strategy selected := by
    calc
      _ = (∏ i, G.questions.weight (u i)) *
          (∏ i : selected, G.questions.weight (fixed i)) *
          (∑ label, selectedLikelihood G strategy selected fixed label u) *
          (if event (selectedQuestionTuple selected fixed u) then 1 else 0) /
            G.selectedSuccess strategy selected := by
        simp only [selectedOutsideLikelihood, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro label _
        ring
      _ = _ := by
        rw [selectedLikelihood_sum]
        cases hw : G.selectedWins strategy selected (selectedQuestionTuple selected fixed u) <;>
          cases he : event (selectedQuestionTuple selected fixed u) <;> simp
        ring
  calc
    _ = ∑ fixed : selected → Q₁ × Q₂,
        ∑ u : {i : Fin n // i ∉ selected} → Q₁ × Q₂,
          ∑ label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected,
            (∏ i, G.questions.weight (u i)) *
              selectedOutsideLikelihood G strategy selected (fixed,label) u *
                (if event (selectedQuestionTuple selected fixed u) then 1 else 0) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro fixed _
      rw [Finset.sum_comm]
    _ = (∑ fixed : selected → Q₁ × Q₂,
        ∑ u : {i : Fin n // i ∉ selected} → Q₁ × Q₂,
          (∏ i : selected, G.questions.weight (fixed i)) * (∏ i, G.questions.weight (u i)) *
            (if G.selectedWins strategy selected (selectedQuestionTuple selected fixed u) &&
              event (selectedQuestionTuple selected fixed u) then 1 else 0)) /
                G.selectedSuccess strategy selected := by
      simp_rw [hlabel]
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = _ := by
      congr 1
      have h := selectedSplit_question_probability G selected
        (fun q => G.selectedWins strategy selected q && event q)
      simpa [selectedSplitLaw, FiniteDistribution.probability, FiniteDistribution.product,
        FiniteDistribution.table, Fintype.sum_prod_type, mul_ite] using h

theorem selected_partial_event_total (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    (∑ s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j,
      ∑ u : {i : Fin n // i ∉ selected} → Q₁ × Q₂,
        partialRevealWeight G.questions j s.2 u *
          selectedOutsideLikelihood G strategy selected s.1 u *
            (if event (selectedQuestionTuple selected s.1.1 u) then 1 else 0)) =
      (G.repetition n).questions.probability
        (fun q => G.selectedWins strategy selected q && event q) /
          G.selectedSuccess strategy selected := by
  have hrest (t : (selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) :=
    partialReveal_event_forget G.questions j
      (fun u => selectedOutsideLikelihood G strategy selected t u *
        (if event (selectedQuestionTuple selected t.1 u) then 1 else 0))
  simp only [← mul_assoc] at hrest
  rw [Fintype.sum_prod_type]
  simp_rw [hrest]
  exact selectedOutsideLikelihood_event_sum G strategy selected event

theorem selected_full_completion_probability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (xy : Q₁ × Q₂) (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    ((selectedFullLeftCompletion G strategy selected j (xy.1,s)).product
      (selectedFullRightCompletion G strategy selected j (xy.2,s))).probability event =
    ∑ lr : ({i : Fin n // i ∉ selected} → Q₁) × ({i : Fin n // i ∉ selected} → Q₂),
      ((selectedLeftCompletion G strategy selected j s xy.1).product
        (selectedRightCompletion G strategy selected j s xy.2)).weight lr *
          (if event (selectedQuestionTuple selected s.1.1 (fun i => (lr.1 i,lr.2 i)))
            then 1 else 0) := by
  rw [selectedFullLeftCompletion, selectedFullRightCompletion,
    ← FiniteDistribution.product_pushforward, FiniteDistribution.probability_pushforward]
  unfold FiniteDistribution.probability
  apply Finset.sum_congr rfl
  intro lr _
  have he : selectedQuestionTuple selected s.1.1 (fun i => (lr.1 i,lr.2 i)) =
      (mergeCoordinates selected (fun i => (s.1.1 i).1) lr.1,
       mergeCoordinates selected (fun i => (s.1.1 i).2) lr.2) :=
    Prod.ext (selectedQuestionTuple_left selected s.1.1 _)
      (selectedQuestionTuple_right selected s.1.1 _)
  rw [he]
  cases hevent : event (mergeCoordinates selected (fun i => (s.1.1 i).1) lr.1,
    mergeCoordinates selected (fun i => (s.1.1 i).2) lr.2) <;> simp [hevent]

theorem selected_completion_event_row (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    (∑ xy : Q₁ × Q₂, (selectedCommonLaw G strategy selected positive j).weight (s,xy) *
      ((selectedFullLeftCompletion G strategy selected j (xy.1,s)).product
        (selectedFullRightCompletion G strategy selected j (xy.2,s))).probability event) =
    ∑ u : {i : Fin n // i ∉ selected} → Q₁ × Q₂,
      partialRevealWeight G.questions j s.2 u *
        selectedOutsideLikelihood G strategy selected s.1 u *
          (if event (selectedQuestionTuple selected s.1.1 u) then 1 else 0) := by
  classical
  have hpoint (xy : Q₁ × Q₂)
      (lr : ({i : Fin n // i ∉ selected} → Q₁) × ({i : Fin n // i ∉ selected} → Q₂)) :
      (selectedCommonLaw G strategy selected positive j).weight (s,xy) *
        ((selectedLeftCompletion G strategy selected j s xy.1).product
          (selectedRightCompletion G strategy selected j s xy.2)).weight lr =
      if (lr.1 j,lr.2 j) = xy then
        partialRevealWeight G.questions j s.2 (fun i => (lr.1 i,lr.2 i)) *
          selectedOutsideLikelihood G strategy selected s.1 (fun i => (lr.1 i,lr.2 i)) else 0 :=
    selected_completion_row_recombine G strategy selected positive j s xy lr.1 lr.2
  simp_rw [selected_full_completion_probability, Finset.mul_sum, ← mul_assoc,
    hpoint]
  have hsum (xy : Q₁ × Q₂) :
      (∑ lr : ({i : Fin n // i ∉ selected} → Q₁) × ({i : Fin n // i ∉ selected} → Q₂),
        (if (lr.1 j,lr.2 j) = xy then
          partialRevealWeight G.questions j s.2 (fun i => (lr.1 i,lr.2 i)) *
            selectedOutsideLikelihood G strategy selected s.1 (fun i => (lr.1 i,lr.2 i)) else 0) *
          (if event (selectedQuestionTuple selected s.1.1 (fun i => (lr.1 i,lr.2 i))) then 1 else 0)) =
      ∑ u : {i : Fin n // i ∉ selected} → Q₁ × Q₂,
        (if u j = xy then partialRevealWeight G.questions j s.2 u *
          selectedOutsideLikelihood G strategy selected s.1 u else 0) *
            (if event (selectedQuestionTuple selected s.1.1 u) then 1 else 0) := by
    exact ((completionTupleEquiv (I := {i : Fin n // i ∉ selected})
      (X := Q₁) (Y := Q₂)).sum_comp _).symm
  simp_rw [hsum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.sum_mul]
  simp

def selectedFullCompletionMixture (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    FiniteDistribution ((Fin n → Q₁) × (Fin n → Q₂)) :=
  ((selectedCommonLaw G strategy selected positive j).transport (Equiv.prodComm _ _)).mixture
    (fun z => (selectedFullLeftCompletion G strategy selected j (z.1.1,z.2)).product
      (selectedFullRightCompletion G strategy selected j (z.1.2,z.2)))

theorem selectedFullCompletionMixture_probability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected})
    (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    (selectedFullCompletionMixture G strategy selected positive j).probability event =
      ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).probability event := by
  erw [FiniteDistribution.probability_condition]
  rw [selectedFullCompletionMixture, FiniteDistribution.probability_mixture]
  simp only [FiniteDistribution.transport]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc
    _ = ∑ s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j,
        ∑ u : {i : Fin n // i ∉ selected} → Q₁ × Q₂,
          partialRevealWeight G.questions j s.2 u *
            selectedOutsideLikelihood G strategy selected s.1 u *
              (if event (selectedQuestionTuple selected s.1.1 u) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro s _
      exact selected_completion_event_row G strategy selected positive j s event
    _ = _ := selected_partial_event_total G strategy selected j event

/-- Exact equality with the actual repeated-game question law conditioned on
the selected wins, derived by summing the local completion rows. -/
theorem selectedFullCompletionMixture_eq_conditionedQuestions (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    selectedFullCompletionMixture G strategy selected positive j =
      (G.repetition n).questions.condition (G.selectedWins strategy selected) positive := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro q
  rw [FiniteDistribution.weight_eq_probability_singleton,
    FiniteDistribution.weight_eq_probability_singleton]
  exact selectedFullCompletionMixture_probability G strategy selected positive j _

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

section Rectangle

open CorrelatedSampling

variable {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S]
  [Nonempty S] [DecidableEq S]

def samplerOutputLaw (thresholds : List ℝ) (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (n : Nat) : FiniteDistribution ((X × Y) × S × S) :=
  sharedOutputLaw μ (traceSeedLaw (rectangleDistribution thresholds) n)
    (samplerLocal thresholds L fallback n) (samplerLocal thresholds R fallback n)

/-- The per-label estimate concerns the actual finite game-law
sampler with a shared seed independent of the input questions. -/
theorem samplerOutputLaw_diagonal (thresholds : List ℝ)
    (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (hL : ∀ x s, (L x).weight s ∈ thresholds)
    (hR : ∀ y s, (R y).weight s ∈ thresholds)
    (fallback : S) (n : Nat) (x : X) (y : Y) (a : S) :
    μ.weight (x,y) * min ((L x).weight a) ((R y).weight a) /
        (1 + Information.totalVariation (L x).weight (R y).weight) *
        (1 - eventMass (rectangleWeight thresholds)
          (fun s => !(rectangleAccept thresholds (L x).weight s ||
            rectangleAccept thresholds (R y).weight s)) ^ n) ≤
      (samplerOutputLaw thresholds μ L R fallback n).weight ((x,y),a,a) := by
  have h := rectangle_label_diagonal_bound thresholds (L x).weight (R y).weight
    fallback a (hL x) (hR y) (L x).nonnegative (R y).nonnegative
    (probability_weight_le_one (L x)) (probability_weight_le_one (R y))
    (L x).normalized (R y).normalized n
  rw [samplerOutputLaw, sharedOutputLaw_weight]
  have he : (traceSeedLaw (rectangleDistribution (α := S) thresholds) n).expectation
      (fun seed => if samplerLocal thresholds L fallback n seed x = a ∧
        samplerLocal thresholds R fallback n seed y = a then 1 else 0) =
      traceAverage (rectangleWeight thresholds) n
        (localDiagonal (rectangleAccept thresholds (L x).weight)
          (rectangleAccept thresholds (R y).weight) Prod.fst fallback a) := by
    exact traceSeedLaw_expectation (rectangleDistribution (α := S) thresholds) n
      (localDiagonal (rectangleAccept thresholds (L x).weight)
        (rectangleAccept thresholds (R y).weight) Prod.fst fallback a)
  rw [he]
  simp only [Information.totalVariation, CorrelatedSampling.totalVariation] at h ⊢
  simpa only [mul_div_assoc, mul_assoc] using
    mul_le_mul_of_nonneg_left h (μ.nonnegative (x,y))

theorem samplerOutputLaw_uniform_diagonal
    (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (n : Nat) (x : X) (y : Y) (a : S) :
    μ.weight (x,y) * min ((L x).weight a) ((R y).weight a) /
        (1 + Information.totalVariation (L x).weight (R y).weight) *
        (1 - uniformRejectionRate S ^ n) ≤
      (samplerOutputLaw (sharedProfileThresholds L R) μ L R fallback n).weight ((x,y),a,a) := by
  have hp := pow_le_pow_left₀ (sharedProfileReject_nonnegative L R x y)
    (sharedProfile_reject_le_rate L R x y) n
  have hco : 0 ≤ μ.weight (x,y) * min ((L x).weight a) ((R y).weight a) /
      (1 + Information.totalVariation (L x).weight (R y).weight) :=
    div_nonneg (mul_nonneg (μ.nonnegative (x,y))
      (le_min ((L x).nonnegative a) ((R y).nonnegative a)))
      (by linarith [Information.totalVariation_nonneg (L x).weight (R y).weight])
  have h := samplerOutputLaw_diagonal (sharedProfileThresholds L R) μ L R
    (left_mem_sharedProfileThresholds L R) (right_mem_sharedProfileThresholds L R)
    fallback n x y a
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_left hp 1) hco).trans h

/-- Actual finite shared sampler approximates any prescribed diagonal law.
Its error is derived from the two actual conditional profiles and its uniform
finite exhaustion probability. -/
theorem samplerOutputLaw_totalVariation
    (p : FiniteDistribution ((X × Y) × S)) (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (n : Nat) :
    Information.totalVariation
      (samplerOutputLaw (sharedProfileThresholds L R) μ L R fallback n).weight
      (diagonalWeights p.weight) ≤
      2 * Information.totalVariation p.weight (fun z => μ.weight z.1 * (L z.1.1).weight z.2) +
      2 * Information.totalVariation p.weight (fun z => μ.weight z.1 * (R z.1.2).weight z.2) +
      uniformRejectionRate S ^ n := by
  apply diagonal_sampler_totalVariation_le p.weight μ.weight
    (fun xy => (L xy.1).weight) (fun xy => (R xy.2).weight) _
    (Information.gameLaw_isProbability p) (Information.gameLaw_isProbability μ)
    (fun xy => Information.gameLaw_isProbability (L xy.1))
    (fun xy => Information.gameLaw_isProbability (R xy.2))
    (Information.gameLaw_isProbability _)
    (pow_nonneg (uniformRejectionRate_nonnegative S) n)
  · exact pow_le_one₀ (uniformRejectionRate_nonnegative S)
      (uniformRejectionRate_lt_one S).le
  · intro xy a
    exact samplerOutputLaw_uniform_diagonal μ L R fallback n xy.1 xy.2 a

theorem samplerOutputLaw_arbitrarily_close
    (p : FiniteDistribution ((X × Y) × S)) (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (η : ℝ) (hη : 0 < η) : ∃ n : Nat,
    Information.totalVariation
      (samplerOutputLaw (sharedProfileThresholds L R) μ L R fallback n).weight
      (diagonalWeights p.weight) ≤
      2 * Information.totalVariation p.weight (fun z => μ.weight z.1 * (L z.1.1).weight z.2) +
      2 * Information.totalVariation p.weight (fun z => μ.weight z.1 * (R z.1.2).weight z.2) + η := by
  obtain ⟨n,hn⟩ := exists_uniformRejectionRate_pow_lt S η hη
  exact ⟨n, (samplerOutputLaw_totalVariation p μ L R fallback n).trans
    (by linarith)⟩

end Rectangle

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_SelectionSequence
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Repetition.SelectionSequence

open UniqueGamesTheorem.Foundations.Games

section ActualGame

variable {Q₁ Q₂ A₁ A₂ : Type*}
variable [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
variable [Nonempty A₁] [Nonempty A₂]

def ConditionalCoordinateBound (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (ell : ℝ) : Prop :=
  ∀ (S : Finset (Fin n)) (_hcard : S.card < n)
    (hp : 0 < G.selectedSuccess strategy S),
    ∃ j, j ∉ S ∧
      (((G.repetition n).questions.condition (G.selectedWins strategy S) hp).probability
        (G.coordinateWin strategy j)) ≤
        G.value + 15 * Real.sqrt
          (((S.card : ℝ) * ell + logTwo (1 / G.selectedSuccess strategy S)) /
            ((n : ℝ) - S.card))

/-- Apply the proved scalar estimate to the success of an actual repeated-game
strategy. The conditional-coordinate bound is the sole game-theoretic premise. -/
theorem repetition_success_le_of_conditionalCoordinateBound
    (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    {v ell : ℝ} (hvalue : G.value ≤ v) (hv1 : v < 1) (hell : 1 ≤ ell)
    (hcoordinate : ConditionalCoordinateBound G n strategy ell) :
    (G.repetition n).success strategy ≤
      (1 - (1 - v)^3 / 6000)^((n : ℝ) / ell) := by
  have hpositive : ∀ S : Finset (Fin n), S.card < n →
      0 < G.selectedSuccess strategy S →
      ∃ j, j ∉ S ∧ SetStep (G.selectedSuccess strategy) v ell S j := by
    intro S hcard hp
    obtain ⟨j, hj, hbound⟩ := hcoordinate S hcard hp
    refine ⟨j, hj, ?_⟩
    change G.selectedSuccess strategy (insert j S) ≤ _
    rw [G.selectedSuccess_insert strategy S j hp]
    exact mul_le_mul_of_nonneg_left
      (hbound.trans (add_le_add hvalue (le_refl _))) (le_of_lt hp)
  obtain ⟨p, hp0, hpnonneg, hpmono, hrec, hpn⟩ :=
    exists_scalar_sequence (G.selectedSuccess strategy) v ell
      (G.selectedSuccess_empty strategy) (G.selectedSuccess_nonnegative strategy)
      (G.selectedSuccess_antitone strategy) hpositive
  have hbound := scalar_bound_6000 p n
    (G.value_nonnegative.trans hvalue) hv1 hell hp0 hpnonneg hpmono hrec
  rw [hpn, G.selectedSuccess_univ strategy] at hbound
  exact hbound

end ActualGame

end UniqueGamesTheorem.Foundations.Repetition.SelectionSequence

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_CompletedSamplingLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

theorem mixture_pushforward_base (μ : FiniteDistribution A) (f : A → B)
    (K : B → FiniteDistribution C) :
    (μ.pushforward f).mixture K = μ.mixture (fun a => K (f a)) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro c
  exact FiniteDistribution.expectation_pushforward μ f (fun b => (K b).weight c)

theorem product_pushforward_eq_mixture_right (μ : FiniteDistribution A)
    (ν : FiniteDistribution B) (f : A × B → C) :
    (μ.product ν).pushforward f =
      ν.mixture (fun b => μ.pushforward (fun a => f (a, b))) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro c
  simp only [FiniteDistribution.pushforward, FiniteDistribution.product,
    FiniteDistribution.mixture, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : f (a, b) = c <;> simp [h, mul_comm]

theorem product_product_pushforward_eq_mixture (μ : FiniteDistribution A)
    (ν : FiniteDistribution B) (κ : FiniteDistribution C) (f : A → B → C → D) :
    (μ.product (ν.product κ)).pushforward (fun z => f z.1 z.2.1 z.2.2) =
      (μ.product ν).mixture
        (fun z => κ.pushforward (fun c => f z.1 z.2 c)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro d
  simp only [FiniteDistribution.pushforward, FiniteDistribution.product,
    FiniteDistribution.mixture, Fintype.sum_prod_type]
  simp only [Finset.mul_sum, mul_ite, mul_zero, mul_assoc]

end DistributionIdentities

section Diagonal

variable {Z S : Type*} [Fintype Z] [Fintype S]

theorem diagonalLaw_eq_pushforward (σ : FiniteDistribution (Z × S)) :
    diagonalLaw σ = σ.pushforward (fun z => (z.1, z.2, z.2)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  rintro ⟨z, a, b⟩
  change diagonalWeights σ.weight (z, a, b) =
    (σ.pushforward (fun t => (t.1, t.2, t.2))).weight (z, a, b)
  simp only [diagonalWeights, FiniteDistribution.pushforward,
    Fintype.sum_prod_type, Prod.mk.injEq]
  by_cases hab : a = b
  · subst b
    simp [ite_and]
  · simp [hab, ite_and]

theorem diagonalLaw_mixture {T : Type*} [Fintype T]
    (σ : FiniteDistribution (Z × S)) (K : Z × S × S → FiniteDistribution T) :
    (diagonalLaw σ).mixture K = σ.mixture (fun z => K (z.1, z.2, z.2)) := by
  rw [diagonalLaw_eq_pushforward, mixture_pushforward_base]

end Diagonal

section Completion

variable {X Y S Γ U V : Type*}
  [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ] [Fintype U] [Fintype V]
  [DecidableEq X] [DecidableEq Y] [DecidableEq S]

theorem outputLaw_eq_product_pushforward
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    outputLaw μ γ sL sR L R =
      (μ.product (seedLaw γ L R)).pushforward
        (fun z => (left sL z.2 z.1.1, right sR z.2 z.1.2)) := by
  exact (product_pushforward_eq_mixture_right μ (seedLaw γ L R)
    (fun z : (X × Y) × Seed Γ X Y S U V =>
      (left sL z.2 z.1.1, right sR z.2 z.1.2))).symm

/-- The completion mixture is derived from actual local table reads. -/
theorem outputLaw_eq_mixture
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    outputLaw μ γ sL sR L R =
      (sharedOutputLaw μ γ sL sR).mixture (completionKernel L R) := by
  calc
    outputLaw μ γ sL sR L R =
        (μ.product γ).mixture (fun z =>
          (KernelSampling.seedLaw L R).pushforward (fun table =>
            (KernelSampling.readLeft table (z.1.1, sL z.2 z.1.1),
             KernelSampling.readRight table (z.1.2, sR z.2 z.1.2)))) := by
      rw [outputLaw_eq_product_pushforward]
      exact product_product_pushforward_eq_mixture μ γ (KernelSampling.seedLaw L R)
        (fun q seed table =>
          (KernelSampling.readLeft table (q.1, sL seed q.1),
           KernelSampling.readRight table (q.2, sR seed q.2)))
    _ = (μ.product γ).mixture (fun z =>
        completionKernel L R (z.1, sL z.2 z.1.1, sR z.2 z.1.2)) := by
      apply congrArg ((μ.product γ).mixture)
      funext z
      exact KernelSampling.read_joint_pushforward L R
        (z.1.1, sL z.2 z.1.1) (z.1.2, sR z.2 z.1.2)
    _ = (sharedOutputLaw μ γ sL sR).mixture (completionKernel L R) := by
      exact (mixture_pushforward_base (μ.product γ)
        (fun z => (z.1, sL z.2 z.1.1, sR z.2 z.1.2)) (completionKernel L R)).symm

omit [DecidableEq X] [DecidableEq Y] [DecidableEq S] in
/-- The diagonal target uses the same selected label for both completion rows. -/
theorem diagonalLaw_completion_mixture
    (σ : FiniteDistribution ((X × Y) × S))
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    (diagonalLaw σ).mixture (completionKernel L R) =
      σ.mixture (fun z => (L (z.1.1, z.2)).product (R (z.1.2, z.2))) := by
  exact diagonalLaw_mixture σ (completionKernel L R)

/-- Completing local outputs incurs no additional total-variation loss. -/
theorem outputLaw_totalVariation_le
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V)
    (σ : FiniteDistribution ((X × Y) × S)) :
    (outputLaw μ γ sL sR L R).totalVariation
        (σ.mixture (fun z => (L (z.1.1, z.2)).product (R (z.1.2, z.2)))) ≤
      (sharedOutputLaw μ γ sL sR).totalVariation (diagonalLaw σ) := by
  rw [outputLaw_eq_mixture, ← diagonalLaw_completion_mixture σ L R]
  exact mixture_totalVariation_le _ _ (completionKernel L R)

end Completion

section CoordinateCompletion

variable {I X Y S Γ : Type*}
  [Fintype I] [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y] [DecidableEq S]

/-- Supported coordinate repair preserves the exact completion mixture. -/
theorem coordinateOutputLaw_eq_mixture
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (j : I) (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution (I → X))
    (R : Y × S → FiniteDistribution (I → Y))
    (hL : ∀ q xs, (L q).weight xs ≠ 0 → xs j = q.1)
    (hR : ∀ q ys, (R q).weight ys ≠ 0 → ys j = q.1) :
    coordinateOutputLaw μ γ j sL sR L R =
      (sharedOutputLaw μ γ sL sR).mixture (completionKernel L R) := by
  calc
    coordinateOutputLaw μ γ j sL sR L R =
        (μ.product (seedLaw γ L R)).pushforward
          (fun z => (coordinateLeft j sL z.2 z.1.1,
            coordinateRight j sR z.2 z.1.2)) := by
      exact (product_pushforward_eq_mixture_right μ (seedLaw γ L R)
        (fun z : (X × Y) × Seed Γ X Y S (I → X) (I → Y) =>
          (coordinateLeft j sL z.2 z.1.1, coordinateRight j sR z.2 z.1.2))).symm
    _ = (μ.product γ).mixture (fun z =>
        (KernelSampling.seedLaw L R).pushforward (fun table =>
          (KernelSampling.completedLeft j table (z.1.1, sL z.2 z.1.1),
           KernelSampling.completedRight j table (z.1.2, sR z.2 z.1.2)))) := by
      exact product_product_pushforward_eq_mixture μ γ (KernelSampling.seedLaw L R)
        (fun q seed table =>
          (KernelSampling.completedLeft j table (q.1, sL seed q.1),
           KernelSampling.completedRight j table (q.2, sR seed q.2)))
    _ = (μ.product γ).mixture (fun z =>
        completionKernel L R (z.1, sL z.2 z.1.1, sR z.2 z.1.2)) := by
      apply congrArg ((μ.product γ).mixture)
      funext z
      exact KernelSampling.completed_joint_pushforward L R j hL hR
        (z.1.1, sL z.2 z.1.1) (z.1.2, sR z.2 z.1.2)
    _ = (sharedOutputLaw μ γ sL sR).mixture (completionKernel L R) := by
      exact (mixture_pushforward_base (μ.product γ)
        (fun z => (z.1, sL z.2 z.1.1, sR z.2 z.1.2)) (completionKernel L R)).symm

theorem coordinateOutputLaw_eq_outputLaw
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (j : I) (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution (I → X))
    (R : Y × S → FiniteDistribution (I → Y))
    (hL : ∀ q xs, (L q).weight xs ≠ 0 → xs j = q.1)
    (hR : ∀ q ys, (R q).weight ys ≠ 0 → ys j = q.1) :
    coordinateOutputLaw μ γ j sL sR L R = outputLaw μ γ sL sR L R := by
  rw [coordinateOutputLaw_eq_mixture μ γ j sL sR L R hL hR, outputLaw_eq_mixture]

theorem coordinateOutputLaw_totalVariation_le
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (j : I) (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution (I → X))
    (R : Y × S → FiniteDistribution (I → Y))
    (hL : ∀ q xs, (L q).weight xs ≠ 0 → xs j = q.1)
    (hR : ∀ q ys, (R q).weight ys ≠ 0 → ys j = q.1)
    (σ : FiniteDistribution ((X × Y) × S)) :
    (coordinateOutputLaw μ γ j sL sR L R).totalVariation
        (σ.mixture (fun z => (L (z.1.1, z.2)).product (R (z.1.2, z.2)))) ≤
      (sharedOutputLaw μ γ sL sR).totalVariation (diagonalLaw σ) := by
  rw [coordinateOutputLaw_eq_outputLaw μ γ j sL sR L R hL hR]
  exact outputLaw_totalVariation_le μ γ sL sR L R σ

end CoordinateCompletion

end

end UniqueGamesTheorem.Foundations.Repetition.CompletedSampling

end

section

/-! An explicit finite shared sampler followed by supported local completion
gives the coordinate success bound. No embedding-existence premise remains. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games CorrelatedSampling
noncomputable section
variable {Q₁ Q₂ A₁ A₂ S : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype S]
  [Nonempty A₁] [Nonempty A₂] [Nonempty S]
  [DecidableEq Q₁] [DecidableEq Q₂] [DecidableEq S] {n : Nat}

theorem coordinate_probability_le_value_of_local_completion
    (G : Game Q₁ Q₂ A₁ A₂) (j : Fin n)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (σ : FiniteDistribution ((Q₁ × Q₂) × S))
    (profileL : Q₁ → FiniteDistribution S) (profileR : Q₂ → FiniteDistribution S)
    (completionL : Q₁ × S → FiniteDistribution (Fin n → Q₁))
    (completionR : Q₂ × S → FiniteDistribution (Fin n → Q₂))
    (supportL : ∀ q xs, (completionL q).weight xs ≠ 0 → xs j = q.1)
    (supportR : ∀ q ys, (completionR q).weight ys ≠ 0 → ys j = q.1)
    (fallback : S) :
    (σ.mixture (fun z => (completionL (z.1.1,z.2)).product
      (completionR (z.1.2,z.2)))).probability (G.coordinateWin strategy j) ≤
      G.value +
        (2 * Information.totalVariation σ.weight
          (fun z => G.questions.weight z.1 * (profileL z.1.1).weight z.2) +
         2 * Information.totalVariation σ.weight
          (fun z => G.questions.weight z.1 * (profileR z.1.2).weight z.2)) := by
  let targetLaw := σ.mixture (fun z => (completionL (z.1.1,z.2)).product (completionR (z.1.2,z.2)))
  let δ := 2 * Information.totalVariation σ.weight
      (fun z => G.questions.weight z.1 * (profileL z.1.1).weight z.2) +
    2 * Information.totalVariation σ.weight
      (fun z => G.questions.weight z.1 * (profileR z.1.2).weight z.2)
  change targetLaw.probability (G.coordinateWin strategy j) ≤ G.value + δ
  by_contra h
  have gap : 0 < targetLaw.probability (G.coordinateWin strategy j) - (G.value + δ) :=
    sub_pos.mpr (lt_of_not_ge h)
  let η := (targetLaw.probability (G.coordinateWin strategy j) - (G.value + δ)) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨N,hN⟩ := samplerOutputLaw_arbitrarily_close σ G.questions profileL profileR fallback η hη
  let thresholds := sharedProfileThresholds profileL profileR
  let γ := traceSeedLaw (rectangleDistribution (α := S) thresholds) N
  let sL := samplerLocal thresholds profileL fallback N
  let sR := samplerLocal thresholds profileR fallback N
  have hvariation := CompletedSampling.coordinateOutputLaw_totalVariation_le
    G.questions γ j sL sR completionL completionR supportL supportR σ
  have hclose : (CompletedSampling.coordinateOutputLaw G.questions γ j sL sR completionL completionR).totalVariation targetLaw ≤ δ + η :=
    hvariation.trans hN
  have hsuccess := G.coordinate_probability_le_value_add_embedding_distance j targetLaw
    (CompletedSampling.seedLaw γ completionL completionR)
    (CompletedSampling.coordinateLeft j sL) (CompletedSampling.coordinateRight j sR)
    (CompletedSampling.coordinateLeft_preserves j sL)
    (CompletedSampling.coordinateRight_preserves j sR) strategy
  have hsym : targetLaw.totalVariation
      (G.localEmbeddingLaw (CompletedSampling.seedLaw γ completionL completionR)
        (CompletedSampling.coordinateLeft j sL) (CompletedSampling.coordinateRight j sR)) =
      (CompletedSampling.coordinateOutputLaw G.questions γ j sL sR completionL completionR).totalVariation targetLaw := by
    unfold FiniteDistribution.totalVariation
    congr 1
    apply Finset.sum_congr rfl
    intro q _
    exact abs_sub_comm _ _
  rw [hsym] at hsuccess
  dsimp [η] at hclose
  linarith

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! The two actual conditional common-data profiles used by the shared
sampler, with explicit normalized default laws on all null inputs. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedProfileFallback (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  (selectedCommonLaw G strategy selected positive j).pushforward Prod.fst

def selectedLeftProfile (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) (x : Q₁) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  toGameLaw
    (leftCommonProfile (selectedCommonLaw G strategy selected positive j).weight
      (selectedProfileFallback G strategy selected positive j).weight x)
    (leftCommonProfile_isProbability _ _
      (gameLaw_isProbability (selectedCommonLaw G strategy selected positive j))
      (gameLaw_isProbability (selectedProfileFallback G strategy selected positive j)) x)

def selectedRightProfile (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) (y : Q₂) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  toGameLaw
    (rightCommonProfile (selectedCommonLaw G strategy selected positive j).weight
      (selectedProfileFallback G strategy selected positive j).weight y)
    (rightCommonProfile_isProbability _ _
      (gameLaw_isProbability (selectedCommonLaw G strategy selected positive j))
      (gameLaw_isProbability (selectedProfileFallback G strategy selected positive j)) y)

def selectedLeftProfileError (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) : ℝ :=
  totalVariation (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedLeftProfile G strategy selected positive j z.2.1).weight z.1)

def selectedRightProfileError (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) : ℝ :=
  totalVariation (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedRightProfile G strategy selected positive j z.2.2).weight z.1)

theorem selectedLeftProfileError_le (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    selectedLeftProfileError G strategy selected positive j ≤
      totalVariation (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (leftRevealModel G.questions
          (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))) +
      totalVariation (secondMarginal (selectedCommonLaw G strategy selected positive j).weight)
        G.questions.weight :=
  leftCommonProfile_error _ G.questions _
    (gameLaw_isProbability (selectedCommonLaw G strategy selected positive j))
    (gameLaw_isProbability (selectedProfileFallback G strategy selected positive j))

theorem selectedRightProfileError_le (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    selectedRightProfileError G strategy selected positive j ≤
      totalVariation (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (rightRevealModel G.questions
          (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))) +
      totalVariation (secondMarginal (selectedCommonLaw G strategy selected positive j).weight)
        G.questions.weight :=
  rightCommonProfile_error _ G.questions _
    (gameLaw_isProbability (selectedCommonLaw G strategy selected positive j))
    (gameLaw_isProbability (selectedProfileFallback G strategy selected positive j))

def selectedSamplingTarget (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    FiniteDistribution ((Q₁ × Q₂) × SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  (selectedCommonLaw G strategy selected positive j).transport (Equiv.prodComm _ _)

theorem selectedSamplingTarget_left_error (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    totalVariation (selectedSamplingTarget G strategy selected positive j).weight
      (fun z => G.questions.weight z.1 * (selectedLeftProfile G strategy selected positive j z.1.1).weight z.2) =
      selectedLeftProfileError G strategy selected positive j := by
  exact totalVariation_comp_equiv
    (Equiv.prodComm (Q₁ × Q₂) (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j))
    (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedLeftProfile G strategy selected positive j z.2.1).weight z.1)

theorem selectedSamplingTarget_right_error (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    totalVariation (selectedSamplingTarget G strategy selected positive j).weight
      (fun z => G.questions.weight z.1 * (selectedRightProfile G strategy selected positive j z.1.2).weight z.2) =
      selectedRightProfileError G strategy selected positive j := by
  exact totalVariation_comp_equiv
    (Equiv.prodComm (Q₁ × Q₂) (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j))
    (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedRightProfile G strategy selected positive j z.2.2).weight z.1)

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

theorem selectedQuestionMarginal_error_sum [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected},
      (selectedQuestionMarginal G strategy selected positive j.1).totalVariation G.questions) ≤
      selectedInformationRadius G strategy selected :=
  (unselectedQuestionMarginal_totalVariation_sum_le_sqrt G strategy selected positive).trans
    (selectedQuestionRadius_le_informationRadius G strategy selected)

def selectedEmbeddingError (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) : ℝ :=
  2 * selectedLeftProfileError G strategy selected positive j +
    2 * selectedRightProfileError G strategy selected positive j

theorem selectedLeftProfileError_sum [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected}, selectedLeftProfileError G strategy selected positive j) ≤
      3 * selectedInformationRadius G strategy selected := by
  have hsum := Finset.sum_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset {i : Fin n // i ∉ selected})) =>
      selectedLeftProfileError_le G strategy selected positive j)
  simp_rw [selectedCommonLaw_secondMarginal] at hsum
  rw [Finset.sum_add_distrib] at hsum
  have hleft := selected_leftReveal_error_sum G strategy selected positive
  have hquestion := selectedQuestionMarginal_error_sum G strategy selected positive
  change (∑ j : {i : Fin n // i ∉ selected},
    Information.totalVariation (selectedQuestionMarginal G strategy selected positive j.1).weight
      G.questions.weight) ≤ _ at hquestion
  linarith

theorem selectedRightProfileError_sum [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected}, selectedRightProfileError G strategy selected positive j) ≤
      3 * selectedInformationRadius G strategy selected := by
  have hsum := Finset.sum_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset {i : Fin n // i ∉ selected})) =>
      selectedRightProfileError_le G strategy selected positive j)
  simp_rw [selectedCommonLaw_secondMarginal] at hsum
  rw [Finset.sum_add_distrib] at hsum
  have hright := selected_rightReveal_error_sum G strategy selected positive
  have hquestion := selectedQuestionMarginal_error_sum G strategy selected positive
  change (∑ j : {i : Fin n // i ∉ selected},
    Information.totalVariation (selectedQuestionMarginal G strategy selected positive j.1).weight
      G.questions.weight) ≤ _ at hquestion
  linarith

theorem selectedEmbeddingError_sum_le_fifteen [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected}, selectedEmbeddingError G strategy selected positive j) ≤
      15 * selectedInformationRadius G strategy selected := by
  have hl := selectedLeftProfileError_sum G strategy selected positive
  have hr := selectedRightProfileError_sum G strategy selected positive
  have hn : 0 ≤ selectedInformationRadius G strategy selected := Real.sqrt_nonneg _
  simp only [selectedEmbeddingError, Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! Quantitative parallel repetition for actual finite two-player games.
The coordinate bound is derived from the explicitly conditioned question law,
finite reveal variables, information estimates, shared rejection sampler,
and normalized local completions. The scalar recurrence is then applied to
the actual repeated strategy's success probability. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

theorem selected_coordinate_probability_le_value_add_error
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).probability
      (G.coordinateWin strategy j.1) ≤
        G.value + selectedEmbeddingError G strategy selected positive j := by
  classical
  let : Nonempty (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
    finiteDistribution_nonempty (selectedProfileFallback G strategy selected positive j)
  have h := coordinate_probability_le_value_of_local_completion G j.1 strategy
    (selectedSamplingTarget G strategy selected positive j)
    (selectedLeftProfile G strategy selected positive j)
    (selectedRightProfile G strategy selected positive j)
    (selectedFullLeftCompletion G strategy selected j)
    (selectedFullRightCompletion G strategy selected j)
    (selectedFullLeftCompletion_support G strategy selected j)
    (selectedFullRightCompletion_support G strategy selected j)
    (Classical.choice inferInstance)
  have htarget : (selectedSamplingTarget G strategy selected positive j).mixture
      (fun z => (selectedFullLeftCompletion G strategy selected j (z.1.1,z.2)).product
        (selectedFullRightCompletion G strategy selected j (z.1.2,z.2))) =
      (G.repetition n).questions.condition (G.selectedWins strategy selected) positive :=
    selectedFullCompletionMixture_eq_conditionedQuestions G strategy selected positive j
  rw [htarget, selectedSamplingTarget_left_error, selectedSamplingTarget_right_error] at h
  exact h

theorem holenstein_conditionalCoordinateBound
    (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (ell : ℝ)
    (halphabet : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell) :
    SelectionSequence.ConditionalCoordinateBound G n strategy ell := by
  intro selected hcard positive
  obtain ⟨j,hj⟩ := exists_coordinate_le_information_budget G strategy selected positive ell
    halphabet hcard (selectedEmbeddingError G strategy selected positive)
    (selectedEmbeddingError_sum_le_fifteen G strategy selected positive)
  exact ⟨j.1,j.property,
    (selected_coordinate_probability_le_value_add_error G strategy selected positive j).trans
      (add_le_add le_rfl hj)⟩

/-- Holenstein's explicit constant-6000 repetition estimate, for the actual
success probability of every finite deterministic repeated strategy. -/
theorem holenstein_repetition_success
    (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    {v ell : ℝ} (hvalue : G.value ≤ v) (hv : v < 1) (hell : 1 ≤ ell)
    (halphabet : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell) :
    (G.repetition n).success strategy ≤
      (1 - (1 - v)^3 / 6000)^((n : ℝ) / ell) :=
  SelectionSequence.repetition_success_le_of_conditionalCoordinateBound G n strategy
    hvalue hv hell (holenstein_conditionalCoordinateBound G n strategy ell halphabet)

/-- Quantitative parallel repetition of the actual maximum game value.
There is no repetition, embedding, information-budget, or independence premise. -/
theorem holenstein_repetition_value
    (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    {v ell : ℝ} (hvalue : G.value ≤ v) (hv : v < 1) (hell : 1 ≤ ell)
    (halphabet : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell) :
    (G.repetition n).value ≤
      (1 - (1 - v)^3 / 6000)^((n : ℝ) / ell) := by
  apply ((G.repetition n).value_le_iff _).2
  intro strategy
  exact holenstein_repetition_success G n strategy hvalue hv hell halphabet

end
end UniqueGamesTheorem.Foundations.Repetition

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

namespace UniqueGamesTheorem.Inverse.RowErasureMatrix

open UniqueGamesTheorem.Inverse.Shortcode
open UniqueGamesTheorem.Inverse.RowErasure
open UniqueGamesTheorem.Inverse.RowErasureDescriptions
open scoped BigOperators Classical

noncomputable section

abbrev Samples (ell m : ℕ) := Mat ell m × Vector ell × Vector m

end
end UniqueGamesTheorem.Inverse.RowErasureMatrix

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_GraphTables
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
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

/-- A concrete encoding suitable for the existing TM2 computation interface. -/
def encoding : Computability.Encoding Table Bool where
  encode := tableBits
  decode := decodeTableBits
  decode_encode := decodeTableBits_encoded

/-- At least one unary delimiter is stored for every field, including all
4096 entries of every predicate table. -/
theorem tableWords_length_le_bits (table : Table) :
    2 + 4098 * table.darts ≤ (tableBits table).length := by
  rw [tableBits, encodeWords_length, ← tableWords_length]
  omega

end UniqueGamesTheorem.Foundations.PCP.GraphTables

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_GenericGraphTables
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
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

theorem vertices_le_tableBits_length (table : (Table q)) :
    table.vertices ≤ (tableBits table).length := by
  simp only [tableBits, tableWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

end UniqueGamesTheorem.Foundations.PCP.GenericGraphTables

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

def inputConfig (M : FinTM2) (phase : Phase) (word counter : List (M.Γ M.k₀)) :
    TM2.Cfg (Symbols M) (Label M) (State M) :=
  ⟨some (.inr phase),(M.initialState,none),inputTapes M word counter⟩

def embedded (M : FinTM2) (counter : List (M.Γ M.k₀)) (c : M.Cfg) :
    TM2.Cfg (Symbols M) (Label M) (State M) :=
  MachineEmbedding.configuration (some (.inr .bodyToTemp)) (none : Option (M.Γ M.k₀))
    (extraTapes M counter [] []) c

def temporaryTapes (M : FinTM2) (word counter : List (M.Γ M.k₀)) : ∀k, List (Symbols M k) :=
  MachineEmbedding.tapes (fun _ => []) (extraTapes M counter word [])

def temporaryConfig (M : FinTM2) (phase : Phase) (word counter : List (M.Γ M.k₀)) :
    TM2.Cfg (Symbols M) (Label M) (State M) :=
  ⟨some (.inr phase),(M.initialState,none),temporaryTapes M word counter⟩

theorem inputTapes_update_input (M : FinTM2)
    (word counter replacement : List (M.Γ M.k₀)) :
    Function.update (inputTapes M word counter) (.inl M.k₀) replacement =
      inputTapes M replacement counter := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₀
    · subst k; simp [inputTapes, initList]
    · simp [inputTapes, initList, h]
  | inr k => simp [inputTapes]

theorem inputTapes_update_counter (M : FinTM2)
    (word counter replacement : List (M.Γ M.k₀)) :
    Function.update (inputTapes M word counter) (.inr .counter) replacement =
      inputTapes M word replacement := by
  funext k
  cases k with
  | inl k => simp [inputTapes]
  | inr k => cases k <;> simp [inputTapes, extraTapes]

variable (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool) (output : M.Γ M.k₁ ≃ Bool)

theorem parseStep_true (word counter : List (M.Γ M.k₀)) :
    (machine M input output).step
      (inputConfig M .parse (input.symm true :: word) counter) =
    some (inputConfig M .parse word (input.symm true :: counter)) := by
  change some (TM2.stepAux (auxProgram M input output .parse)
    (M.initialState,none) (inputTapes M (input.symm true :: word) counter)) = _
  simp [auxProgram, TM2.stepAux, inputTapes_update_input, inputTapes_update_counter,
    inputConfig]

theorem parseStep_false (word counter : List (M.Γ M.k₀)) :
    (machine M input output).step
      (inputConfig M .parse (input.symm false :: word) counter) =
    some (inputConfig M .guard word counter) := by
  change some (TM2.stepAux (auxProgram M input output .parse)
    (M.initialState,none) (inputTapes M (input.symm false :: word) counter)) = _
  simp [auxProgram, TM2.stepAux, inputTapes_update_input, inputTapes_update_counter,
    inputConfig]

theorem parseTrace (count : Nat) (word counter : List (M.Γ M.k₀)) :
    (MachineComposition.advance (machine M input output).step)^[count+1]
      (some (inputConfig M .parse ((encodeWord count).map input.symm ++ word) counter)) =
    some (inputConfig M .guard word (List.replicate count (input.symm true) ++ counter)) := by
  induction count generalizing counter with
  | zero =>
    simpa only [encodeWord, List.replicate_zero, List.nil_append, List.map_singleton,
      List.singleton_append, Nat.zero_add, Function.iterate_one, MachineComposition.advance_some]
      using! parseStep_false M input output word counter
  | succ count ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (machine M input output).step)^[count+1]
      ((machine M input output).step
        (inputConfig M .parse ((encodeWord (count+1)).map input.symm ++ word) counter)) = _
    simp only [encodeWord, List.replicate_succ, List.cons_append, List.map_cons,
      List.map_append, List.map_replicate]
    rw [parseStep_true]
    have h := ih (input.symm true :: counter)
    have hc : List.replicate count (input.symm true) ++ input.symm true :: counter =
        input.symm true :: (List.replicate count (input.symm true) ++ counter) := by
      rw [← List.singleton_append, ← List.append_assoc,
        ← List.replicate_succ', List.replicate_succ, List.cons_append]
    rw [hc] at h
    simpa only [encodeWord, List.map_append, List.map_replicate, List.map_singleton,
      List.map_nil, List.singleton_append, List.append_assoc] using! h

theorem guardStep_some (word counter : List (M.Γ M.k₀)) (symbol : M.Γ M.k₀) :
    (machine M input output).step (inputConfig M .guard word (symbol :: counter)) =
      some (embedded M counter (initList M word)) := by
  change some (TM2.stepAux (auxProgram M input output .guard)
    (M.initialState,none) (inputTapes M word (symbol :: counter))) = _
  simp [auxProgram, TM2.stepAux, inputTapes_update_counter,
    embedded, MachineEmbedding.configuration]
  exact ⟨rfl,rfl,rfl⟩

theorem guardStep_none (word : List (M.Γ M.k₀)) :
    (machine M input output).step (inputConfig M .guard word []) =
      some (inputConfig M .finalToTemp word []) := by
  change some (TM2.stepAux (auxProgram M input output .guard)
    (M.initialState,none) (inputTapes M word [])) = _
  simp [auxProgram, TM2.stepAux, inputTapes_update_counter, inputConfig]

/-- Lift the actual certified body run while preserving the remaining counter. -/
def bodyExecution (counter : List (M.Γ M.k₀))
    (word : List (M.Γ M.k₀)) (result : List (M.Γ M.k₁)) (budget : Nat)
    (run : TM2OutputsInTime M word (some result) budget) :
    StateTransition.EvalsToInTime (machine M input output).step
      (embedded M counter (initList M word))
      (some (embedded M counter (haltList M result))) budget :=
  MachineComposition.embeddedExecution (some (.inr .bodyToTemp : Label M))
    (none : Option (M.Γ M.k₀)) (extraTapes M counter [] []) M.m
    (auxProgram M input output) run

theorem bodyToTemp_tapes (result : List (M.Γ M.k₁)) (counter : List (M.Γ M.k₀)) :
    Reduction.MachineTransfer.tapesAt (.inl M.k₁) (.inr .temporary)
      (embedded M counter (haltList M result)).stk []
      (result.reverse.map (fun b => input.symm (output b))) =
    temporaryTapes M (result.reverse.map (fun b => input.symm (output b))) counter := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₁
    · subst k; simp [Reduction.MachineTransfer.tapesAt, temporaryTapes]
    · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, embedded,
        MachineEmbedding.configuration, haltList, h]
  | inr k =>
    cases k <;> simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, embedded,
      MachineEmbedding.configuration, extraTapes]

theorem tempToBody_tapes (word counter : List (M.Γ M.k₀)) :
    Reduction.MachineTransfer.tapesAt (Γ := Symbols M) (.inr .temporary) (.inl M.k₀)
      (temporaryTapes M word counter) [] word.reverse = inputTapes M word.reverse counter := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₀
    · subst k; simp [Reduction.MachineTransfer.tapesAt, inputTapes, initList]
    · simp [Reduction.MachineTransfer.tapesAt, inputTapes, temporaryTapes, initList, h]
  | inr k =>
    cases k <;> simp [Reduction.MachineTransfer.tapesAt, inputTapes, temporaryTapes, extraTapes]

theorem finalToTemp_tapes (word : List (M.Γ M.k₀)) :
    Reduction.MachineTransfer.tapesAt (Γ := Symbols M) (.inl M.k₀) (.inr .temporary)
      (inputTapes M word []) [] word.reverse = temporaryTapes M word.reverse [] := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₀
    · subst k; simp [Reduction.MachineTransfer.tapesAt, temporaryTapes]
    · simp [Reduction.MachineTransfer.tapesAt, inputTapes, temporaryTapes, initList, h]
  | inr k =>
    cases k <;> simp [Reduction.MachineTransfer.tapesAt, inputTapes, temporaryTapes, extraTapes]

theorem tempToOutput_tapes (word : List (M.Γ M.k₀)) :
    Reduction.MachineTransfer.tapesAt (Γ := Symbols M) (.inr .temporary) (.inr .output)
      (temporaryTapes M word []) [] word.reverse =
        (haltList (machine M input output) word.reverse).stk := by
  funext k
  cases k with
  | inl k => simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, haltList, machine]
  | inr k =>
    cases k <;> simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, haltList,
      machine, extraTapes]; rfl

def bodyToTemp (result : List (M.Γ M.k₁)) (counter : List (M.Γ M.k₀)) :
    StateTransition.EvalsToInTime (machine M input output).step
      (embedded M counter (haltList M result))
      (some (temporaryConfig M .tempToBody
        (result.reverse.map (fun b => input.symm (output b))) counter)) (result.length+1) := by
  have run := Reduction.MachineTransfer.transferAtInTime
    (Γ := Symbols M) (.inl M.k₁) (.inr .temporary) (by intro h; cases h)
    (fun b => input.symm (output b)) (input.symm false)
    (.inr .bodyToTemp) (some (.inr .tempToBody)) (program M input output) rfl
    (embedded M counter (haltList M result)).stk M.initialState none
  have hs : (embedded M counter (haltList M result)).stk (.inl M.k₁) = result := by
    simp [embedded, MachineEmbedding.configuration, haltList]
  have hd : (embedded M counter (haltList M result)).stk (.inr .temporary) = [] := rfl
  rw [hs,hd,List.append_nil,bodyToTemp_tapes] at run
  exact run

def tempToBody (word counter : List (M.Γ M.k₀)) :
    StateTransition.EvalsToInTime (machine M input output).step
      (temporaryConfig M .tempToBody word counter)
      (some (inputConfig M .guard word.reverse counter)) (word.length+1) := by
  have run := Reduction.MachineTransfer.transferAtInTime
    (Γ := Symbols M) (.inr .temporary) (.inl M.k₀) (by intro h; cases h)
    id (input.symm false) (.inr .tempToBody) (some (.inr .guard))
    (program M input output) rfl (temporaryTapes M word counter) M.initialState none
  simp only [temporaryTapes, MachineEmbedding.tapes, extraTapes,
    List.map_id, List.append_nil] at run
  rw [show Reduction.MachineTransfer.tapesAt (Γ := Symbols M) (.inr .temporary) (.inl M.k₀)
      (MachineEmbedding.tapes (fun _ => []) (extraTapes M counter word [])) [] word.reverse =
        inputTapes M word.reverse counter from tempToBody_tapes M word counter] at run
  exact run

def finalToTemp (word : List (M.Γ M.k₀)) :
    StateTransition.EvalsToInTime (machine M input output).step
      (inputConfig M .finalToTemp word [])
      (some (temporaryConfig M .tempToOutput word.reverse [])) (word.length+1) := by
  have run := Reduction.MachineTransfer.transferAtInTime
    (Γ := Symbols M) (.inl M.k₀) (.inr .temporary) (by intro h; cases h)
    id (input.symm false) (.inr .finalToTemp) (some (.inr .tempToOutput))
    (program M input output) rfl (inputTapes M word []) M.initialState none
  have hd : inputTapes M word [] (.inr .temporary) = [] := rfl
  rw [inputTapes_input,hd,List.map_id,List.append_nil,finalToTemp_tapes] at run
  exact run

def tempToOutput (word : List (M.Γ M.k₀)) :
    StateTransition.EvalsToInTime (machine M input output).step
      (temporaryConfig M .tempToOutput word [])
      (some (haltList (machine M input output) word.reverse)) (word.length+1) := by
  have run := Reduction.MachineTransfer.transferAtInTime
    (Γ := Symbols M) (.inr .temporary) (.inr .output) (by intro h; cases h)
    id (input.symm false) (.inr .tempToOutput) none
    (program M input output) rfl (temporaryTapes M word []) M.initialState none
  have hs : temporaryTapes M word [] (.inr .temporary) = word := rfl
  have hd : temporaryTapes M word [] (.inr .output) = [] := rfl
  rw [hs,hd,List.map_id,List.append_nil,tempToOutput_tapes] at run
  exact run

/-- Transfer the literal body output back to the input, preserving its order. -/
def bodyReturn (result : List (M.Γ M.k₁)) (counter : List (M.Γ M.k₀)) :
    StateTransition.EvalsToInTime (machine M input output).step
      (embedded M counter (haltList M result))
      (some (inputConfig M .guard (result.map (fun b => input.symm (output b))) counter))
      (2*(result.length+1)) := by
  have first := bodyToTemp M input output result counter
  have second := tempToBody M input output (result.reverse.map (fun b => input.symm (output b))) counter
  simp only [List.map_reverse,List.reverse_reverse,List.length_reverse,List.length_map] at first second
  have full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  exact { toEvalsTo := full.toEvalsTo, steps_le_m := by have h := full.steps_le_m; omega }

/-- Zero remaining iterations still run the actual final transfers and halt
with every tape other than the designated output empty. -/
def finish (word : List (M.Γ M.k₀)) :
    StateTransition.EvalsToInTime (machine M input output).step
      (inputConfig M .guard word []) (some (haltList (machine M input output) word))
      (2*word.length+3) := by
  have guard := oneStep _ _ _ (guardStep_none M input output word)
  have first := finalToTemp M input output word
  have second := tempToOutput M input output word.reverse
  simp only [List.reverse_reverse,List.length_reverse] at second
  have gfirst := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ guard first
  have full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ gfirst second
  exact { toEvalsTo := full.toEvalsTo, steps_le_m := by have h := full.steps_le_m; omega }

def loopExecution (count : Nat) (words : Nat → List Bool) (budgets : Nat → Nat)
    (runs : ∀ i, i < count → TM2OutputsInTime M ((words i).map input.symm)
      (some ((words (i+1)).map output.symm)) (budgets i)) :
    StateTransition.EvalsToInTime (machine M input output).step
      (inputConfig M .guard ((words 0).map input.symm)
        (List.replicate count (input.symm true)))
      (some (haltList (machine M input output) ((words count).map input.symm)))
      (loopBudget count words budgets) := by
  induction count generalizing words budgets with
  | zero =>
    simpa only [loopBudget,List.replicate_zero,List.length_map] using!
      finish M input output ((words 0).map input.symm)
  | succ count ih =>
    rw [List.replicate_succ]
    have guard := oneStep _ _ _ (guardStep_some M input output ((words 0).map input.symm)
      (List.replicate count (input.symm true)) (input.symm true))
    have body := bodyExecution M input output (List.replicate count (input.symm true))
      ((words 0).map input.symm) ((words 1).map output.symm) (budgets 0)
      (runs 0 (Nat.zero_lt_succ count))
    have returned := bodyReturn M input output ((words 1).map output.symm)
      (List.replicate count (input.symm true))
    have handoff : ((words 1).map output.symm).map (fun b => input.symm (output b)) =
        (words 1).map input.symm := by
      simp only [List.map_map,Function.comp_def,Equiv.apply_symm_apply]
    rw [handoff,List.length_map] at returned
    have tail := ih (fun i => words (i+1)) (fun i => budgets (i+1))
      (fun i hi => runs (i+1) (Nat.succ_lt_succ hi))
    have first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ guard body
    have second := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first returned
    have full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ second tail
    exact {
      toEvalsTo := full.toEvalsTo
      steps_le_m := by
        have h := full.steps_le_m
        simp only [loopBudget]
        omega
    }

theorem inputConfig_init (word : List (M.Γ M.k₀)) :
    inputConfig M .parse word [] = initList (machine M input output) word := by
  unfold inputConfig initList
  congr 1
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₀
    · subst k; simp [inputTapes,initList,machine]; rfl
    · simp [inputTapes,initList,machine,h]
  | inr k => cases k <;> simp [inputTapes,initList,machine,extraTapes]

def executeSequence (count : Nat) (words : Nat → List Bool) (budgets : Nat → Nat)
    (runs : ∀ i, i < count → TM2OutputsInTime M ((words i).map input.symm)
      (some ((words (i+1)).map output.symm)) (budgets i)) :
    TM2OutputsInTime (machine M input output)
      ((encodeWord count ++ words 0).map input.symm)
      (some ((words count).map input.symm))
      (count+1 + loopBudget count words budgets) := by
  let parsed : StateTransition.EvalsToInTime (machine M input output).step
      (inputConfig M .parse ((encodeWord count).map input.symm ++ (words 0).map input.symm) [])
      (some (inputConfig M .guard ((words 0).map input.symm)
        (List.replicate count (input.symm true)))) (count+1) := {
    steps := count+1
    evals_in_steps := by
      change (MachineComposition.advance (machine M input output).step)^[count+1]
        (some (inputConfig M .parse ((encodeWord count).map input.symm ++ (words 0).map input.symm) [])) = _
      simpa only [List.append_nil] using! parseTrace M input output count
        ((words 0).map input.symm) []
    steps_le_m := le_refl _
  }
  have body := loopExecution M input output count words budgets runs
  have full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ parsed body
  rw [inputConfig_init M input output] at full
  erw [List.map_append]
  simpa only [TM2OutputsInTime, Option.map_some, Nat.add_comm] using! full

omit M input output in
/-- Explicit sum form of the actual repeat budget. -/
theorem loopBudget_eq_sum (count : Nat) (words : Nat → List Bool) (budgets : Nat → Nat) :
    loopBudget count words budgets =
      (∑ i ∈ Finset.range count, (budgets i + 2*(words (i+1)).length+3)) +
      2*(words count).length+3 := by
  induction count generalizing words budgets with
  | zero => simp [loopBudget]
  | succ count ih =>
    rw [loopBudget, ih, Finset.sum_range_succ']
    simp only [Nat.zero_add]
    omega

omit M input output in
/-- A uniform bound along the executed sequence is enough to bound the actual
repeat runtime. No polynomial growth of an arbitrary iteration is asserted. -/
theorem loopBudget_le (count : Nat) (words : Nat → List Bool) (budgets : Nat → Nat)
    (bodyBound lengthBound : Nat)
    (hb : ∀i, i < count → budgets i ≤ bodyBound)
    (hl : ∀i, i ≤ count → (words i).length ≤ lengthBound) :
    loopBudget count words budgets ≤ count*(bodyBound+2*lengthBound+3)+2*lengthBound+3 := by
  rw [loopBudget_eq_sum]
  have hs : (∑ i ∈ Finset.range count, (budgets i+2*(words (i+1)).length+3)) ≤
      count*(bodyBound+2*lengthBound+3) := by
    calc
      _ ≤ ∑ i ∈ Finset.range count, (bodyBound+2*lengthBound+3) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := Finset.mem_range.mp hi
        have hbi := hb i hi'
        have hli := hl (i+1) hi'
        omega
      _ = _ := by simp
  have hlast := hl count (le_refl _)
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachineRepeat

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_ClauseVerifierLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.slotFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP

open Target

theorem honest_satisfies {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) :
    localSatisfies clause (honestAnswer clause assignment) = clause.eval assignment := rfl

theorem honest_answerAt {n : Nat} (clause : Clause n) (assignment : Fin n → Bool)
    (slot : Slot) : answerAt (honestAnswer clause assignment) slot =
      assignment (nameAt clause slot) := by
  cases slot <;> rfl

/-- A failed Bob clause forces one rejection among its three incidence events. -/
theorem local_rejection_bound {n : Nat} (clause : Clause n) (alice : ClauseAnswer)
    (bob : Fin n → Bool) :
    acceptedSlots clause alice (honestAnswer clause bob) + clauseFailure clause bob ≤ 3 := by
  have hle := matchingSlots_le alice (honestAnswer clause bob)
  by_cases hb : clause.eval bob = true
  · simp only [clauseFailure, hb, ↓reduceIte, Nat.add_zero]
    unfold acceptedSlots
    split <;> omega
  · have hfailure : clauseFailure clause bob = 1 := by simp [clauseFailure, hb]
    rw [hfailure]
    by_cases ha : localSatisfies clause alice = true
    · have hne : alice ≠ honestAnswer clause bob := by
        intro h
        subst alice
        exact hb ((honest_satisfies clause bob).symm.trans ha)
      have hlt : matchingSlots alice (honestAnswer clause bob) ≠ 3 := by
        intro h
        exact hne ((matchingSlots_eq_three _ _).mp h)
      simp only [acceptedSlots, ha, ↓reduceIte]
      omega
    · simp [acceptedSlots, ha]

/-- Explicit finite verifier. The occurrence and slot are randomness, never an
    additional argument supplied to Bob's strategy. -/
def accepts (formula : Formula) (alice : AliceStrategy formula) (bob : BobStrategy formula)
    (event : RandomEvent formula) : Bool :=
  localSatisfies (clauseAt formula event.1) (alice event.1) &&
    decide (answerAt (alice event.1) event.2 = bob (nameAt (clauseAt formula event.1) event.2))

def acceptedCount (formula : Formula) (alice : AliceStrategy formula)
    (bob : BobStrategy formula) : List (Fin formula.clauses.length) → Nat
  | [] => 0
  | i :: rest => acceptedSlots (clauseAt formula i) (alice i)
      (honestAnswer (clauseAt formula i) bob) + acceptedCount formula alice bob rest

def failureCount (formula : Formula) (bob : BobStrategy formula) :
    List (Fin formula.clauses.length) → Nat
  | [] => 0
  | i :: rest => clauseFailure (clauseAt formula i) bob + failureCount formula bob rest

end UniqueGamesTheorem.Foundations.PCP

end

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceContexts

open Target PCP

theorem sampledVariables_supported (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (s : SlotContext u) :
    ∀ t, ∃ slot, nameAt (clauseAt F (c t)) slot = sampledVariables F c s t :=
  fun t => ⟨s t, rfl⟩

theorem honestJ_valid (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (assignment : Fin F.variables → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    validJ F c (honestJ F c assignment) = true := by
  apply (validJ_eq_true_iff F c _).mpr
  constructor
  · intro t
    exact (honest_satisfies _ assignment).trans (hs _ (List.getElem_mem _))
  · intro t t' s s' hname
    simp only [honestJ, honest_answerAt]
    exact congrArg assignment hname

theorem pi_honest (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (v : VariableContext F u) (assignment : Fin F.variables → Bool)
    (hsupport : ∀ t, ∃ s, nameAt (clauseAt F (c t)) s = v t) :
    pi F c v (honestJ F c assignment) = honestI F v assignment := by
  funext t
  exact (honest_answerAt _ assignment _).trans
    (congrArg assignment (canonicalSlot_name _ _ (hsupport t)))

theorem pi_honest_sampled (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (assignment : Fin F.variables → Bool) :
    pi F c (sampledVariables F c s) (honestJ F c assignment) =
      honestI F (sampledVariables F c s) assignment :=
  pi_honest F c _ assignment (sampledVariables_supported F c s)

theorem projection_implies_coordinate_accepts (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (v : VariableContext F u) (i : I u) (j : J u)
    (hj : validJ F c j = true) (hpi : pi F c v j = i) (t : Fin u) :
    baseAccepts F (v t) (c t) (i t) (j t) = true := by
  exact (baseAccepts_eq_true_iff F _ _ _ _).mpr
    ⟨validJ_satisfies F c j hj t, validJ_localConsistent F c j hj t, congrFun hpi t⟩

end UniqueGamesTheorem.Foundations.Hastad.SourceContexts

end

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature

open Target PCP SourceContexts

/-- Exact equality with the actual contextual validity predicate, for every
answer tuple, including repeated variables within or across clauses. -/
theorem signature_validJ (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (j : J u) :
    signatureValid (ofContext F c s) j = validJ F c j := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have hs := of_decide_eq_true h
    apply (validJ_eq_true_iff F c j).mpr
    constructor
    · intro t
      exact (signatureSatisfies_ofContext F c s j t).symm.trans (hs.1 t)
    · intro t t' a a' hname
      apply hs.2 t t' a a'
      exact decide_eq_true hname
  · intro h
    have hs := (validJ_eq_true_iff F c j).mp h
    apply decide_eq_true
    constructor
    · intro t
      exact (signatureSatisfies_ofContext F c s j t).trans (hs.1 t)
    · intro t t' a a' heq
      exact hs.2 t t' a a' (of_decide_eq_true heq)

theorem signatureCanonicalSlot_ofContext (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (s : SlotContext u) (t : Fin u) :
    signatureCanonicalSlot (ofContext F c s) t =
      canonicalSlot (clauseAt F (c t)) (sampledVariables F c s t) := by
  by_cases hfirst : nameAt (clauseAt F (c t)) .first =
      nameAt (clauseAt F (c t)) (s t)
  · simp [signatureCanonicalSlot, canonicalSlot, ofContext, contextNameProfile,
      occurrenceName, sampledVariables, hfirst]
  · by_cases hsecond : nameAt (clauseAt F (c t)) .second =
        nameAt (clauseAt F (c t)) (s t)
    · simp [signatureCanonicalSlot, canonicalSlot, ofContext, contextNameProfile,
        occurrenceName, sampledVariables, hfirst, hsecond]
    · simp [signatureCanonicalSlot, canonicalSlot, ofContext, contextNameProfile,
        occurrenceName, sampledVariables, hfirst, hsecond]

/-- The actual canonical projection factors through the finite signature on
every label, without a validity hypothesis. -/
theorem signature_pi (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (j : J u) :
    signatureProjection (ofContext F c s) j = pi F c (sampledVariables F c s) j := by
  funext t
  simp only [signatureProjection, signatureCanonicalSlot_ofContext, pi]

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

theorem failureCount_evaluations (F : Formula) (A : Fin F.variables → Bool)
    (indices : List (Fin F.clauses.length)) :
    failureCount F A indices =
      (indices.map (fun i => (clauseAt F i).eval A)).count false := by
  induction indices with
  | nil => simp [failureCount]
  | cons i rest ih =>
    cases h : (clauseAt F i).eval A <;>
      simp [failureCount, clauseFailure, h, ih, Nat.add_comm]

/-- The semantic score is the checked verifier's actual failed-clause count. -/
theorem verifier_failureCount (F : Formula) (A : Fin F.variables → Bool) :
    failureCount F A (allIndices F) = failedCount F A := by
  rw [failureCount_evaluations, evaluations_allIndices]
  rfl

end UniqueGamesTheorem.Foundations.PCP.NameCompaction

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

instance vertexNonempty (F : Formula) : Nonempty (Vertex F) := ⟨dummyVertex F⟩

def honestLabeling (F : Formula) (A : Fin F.variables → Bool) : Vertex F → Label
  | .inl (.inl v) => variableLabel (A v)
  | .inl (.inr i) => fromClauseAnswer (honestAnswer (clauseAt F i) A)
  | .inr _ => variableLabel false

theorem clauseAnswer_eq_of_slots (a b : ClauseAnswer)
    (h : ∀ s, answerAt a s = answerAt b s) : a = b := by
  rcases a with ⟨a₀, a₁, a₂⟩
  rcases b with ⟨b₀, b₁, b₂⟩
  have h₀ : a₀ = b₀ := h .first
  have h₁ : a₁ = b₁ := h .second
  have h₂ : a₂ = b₂ := h .third
  cases h₀; cases h₁; cases h₂; rfl

end UniqueGamesTheorem.Foundations.PCP.InitialGraph

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_OverlayLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

theorem card_paddedCloud (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) :
    Fintype.card (PaddedCloud t padding v) = cloudSize t v + padding v := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (paddedCloudEquiv t padding v)

end UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularDummyRow
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
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

open Turing MachineComposition PCP.GraphTables

/-- The row subprogram is a static label placement of the checked emitter. -/
def instruction {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt Alphabet Λ (State σ)
  | .affine .seed => MachineUnaryAffineAt.seed 1 q (labels (.affine .scan))
  | .affine .scan => MachineUnaryAffineAt.scan 0 3 1 (q + 1)
      (labels (.affine .scan)) (labels (.affine .restore))
  | .affine .restore => Reduction.MachineTransfer.loopAt 3 0 id false
      (labels (.affine .restore)) (some (labels (.row (MachineDummyRows.start 1))))
  | .row stage => MachineCloudPadding.Placement.statement (id : Tape → Tape)
      (fun l => labels (.row l)) (some (labels .reverse))
      (MachineDummyRows.program 1 stage)
  | .reverse => MachineDrain.drain 1 (labels .reverse) (some (labels .relation))
  | .relation => MachineDrain.drain 2 (labels .relation) exit

/-- Both cleanup loops pop their entire physical fields. -/
theorem cleanupTraceAt {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (x e : Nat) (output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[
        ((encodeWord e).length + 1) + (MachineDummyRows.trueBits.length + 1)]
      (some ⟨some (labels .reverse), (ambient, register),
        MachineDummyRows.fieldTapes x e output⟩) =
      some ⟨exit, (ambient, none),
        Function.update (Function.update (MachineDummyRows.fieldTapes x e output) 1 []) 2 []⟩ := by
  let base := MachineDummyRows.fieldTapes x e output
  let mid := Function.update base (1 : Tape) []
  have first := MachineDrain.drainTrace (1 : Tape) (labels .reverse)
    (some (labels .relation)) program (code .reverse) base (base 1) ambient register
  have second := MachineDrain.drainTrace (2 : Tape) (labels .relation)
    exit program (code .relation) mid (mid 2) ambient none
  simp only [Function.update_eq_self] at first second
  have hreverse : base 1 = encodeWord e := rfl
  have hrelation : mid 2 = MachineDummyRows.trueBits := by
    simp only [mid, Function.update_of_ne (by decide : (2 : Tape) ≠ 1)]
    rfl
  rw [hreverse] at first
  rw [hrelation] at second
  exact join_trace first second

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularDummyRow

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineUnaryLessAtLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical comparison of two unary fields. Matched true bits are saved on
two empty scratch stacks. The first delimiter determines the comparison, then
both saved prefixes are restored. All input suffixes and other tapes survive. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

theorem comparisonTrace (slots : Fin 4 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step program))^[steps a b]
      (some ⟨some (labels .scan), ((ambient, flag), register),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix) [] []⟩) =
      some ⟨exit, ((ambient, decide (a < b)), none),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix) [] []⟩ := by
  have hscan := scanTrace slots (labels .scan) (labels .restoreLeft) program (atLabels .scan)
    base a b leftSuffix rightSuffix [] [] ambient flag register
  simp only [List.append_nil] at hscan
  have hwordLeft : List.replicate (min a b) true ++ (encodeWord (a - b) ++ leftSuffix) =
      encodeWord a ++ leftSuffix := by
    rw [MachineUnaryAffineAt.prepend_replicate_word,
      show min a b + (a - b) = a by omega]
  have hwordRight : List.replicate (min a b) true ++ (encodeWord (b - a) ++ rightSuffix) =
      encodeWord b ++ rightSuffix := by
    rw [MachineUnaryAffineAt.prepend_replicate_word,
      show min a b + (b - a) = b by omega]
  let middle := tapes slots base (encodeWord (a - b) ++ leftSuffix)
    (encodeWord (b - a) ++ rightSuffix) (List.replicate (min a b) true) (List.replicate (min a b) true)
  have hleft := Reduction.MachineTransfer.transferAt_fromTapes
    (Γ := fun _ : K => Bool) (σ := σ × Bool) (slots 2) (slots 0)
    (slots.injective.ne (by decide)) id false (labels .restoreLeft) (some (labels .restoreRight))
    program (by simpa only [statement] using atLabels .restoreLeft)
    middle (ambient, decide (a < b)) none
  change (advance (TM2.step program))^[(middle (slots 2)).length + 1]
    (some ⟨some (labels .restoreLeft), ((ambient, decide (a < b)), none), middle⟩) = _ at hleft
  simp only [middle, tapes_savedLeft, tapes_left, List.length_replicate, List.reverse_replicate,
    List.map_id, hwordLeft, transferLeft_tapes] at hleft
  let afterLeft := tapes slots base (encodeWord a ++ leftSuffix)
    (encodeWord (b - a) ++ rightSuffix) [] (List.replicate (min a b) true)
  have hright := Reduction.MachineTransfer.transferAt_fromTapes
    (Γ := fun _ : K => Bool) (σ := σ × Bool) (slots 3) (slots 1)
    (slots.injective.ne (by decide)) id false (labels .restoreRight) exit
    program (by simpa only [statement] using atLabels .restoreRight)
    afterLeft (ambient, decide (a < b)) none
  change (advance (TM2.step program))^[(afterLeft (slots 3)).length + 1]
    (some ⟨some (labels .restoreRight), ((ambient, decide (a < b)), none), afterLeft⟩) = _ at hright
  simp only [afterLeft, tapes_savedRight, tapes_right, List.length_replicate, List.reverse_replicate,
    List.map_id, hwordRight, transferRight_tapes] at hright
  have hfirst : (advance (TM2.step program))^[(min a b + 1) + (min a b + 1)]
      (some ⟨some (labels .scan), ((ambient, flag), register),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix) [] []⟩) =
      some ⟨some (labels .restoreRight), ((ambient, decide (a < b)), none), afterLeft⟩ := by
    rw [Function.iterate_add_apply, hscan]
    exact hleft
  rw [show steps a b = (min a b + 1) + ((min a b + 1) + (min a b + 1)) by
    unfold steps; omega, Function.iterate_add_apply, hfirst]
  exact hright

/-- Actual comparison on a caller frame: both complete operand tapes and all
other tapes are preserved, both scratch tapes remain empty, and the finite
result flag is precisely the strict comparison of the two unary values. -/
theorem lessThanTrace (slots : Fin 4 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix : List Bool)
    (leftWord : base (slots 0) = encodeWord a ++ leftSuffix)
    (rightWord : base (slots 1) = encodeWord b ++ rightSuffix)
    (leftEmpty : base (slots 2) = []) (rightEmpty : base (slots 3) = [])
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step program))^[steps a b]
      (some ⟨some (labels .scan), ((ambient, flag), register), base⟩) =
      some ⟨exit, ((ambient, decide (a < b)), none), base⟩ := by
  have h := comparisonTrace slots labels exit program atLabels base a b leftSuffix rightSuffix
    ambient flag register
  have hframe := tapes_self slots base
  rw [leftWord, rightWord, leftEmpty, rightEmpty] at hframe
  rw [hframe] at h
  exact h

end UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt

/-!
Actual unary-guard iteration for a logarithmic number of rounds. Semantic
cardinality grows by a fixed linear factor. A separate encoding polynomial
bounds each intermediate word; it is never iterated as a size recurrence.
The body hypotheses are individual executions of the supplied finite program.
-/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PreprocessingRegularTablesLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
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

theorem edgeSatisfied_ofCloudTables (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (labels : Fin (vertexCount t padding) → GraphTables.Label)
    (v : Vertex t padding) (p : Fin q ⊕ Unit) :
    (PortTables.baseGraph (ofCloudTables t padding tables)).edgeSatisfied labels
        (vertexOrder t padding v, portOrder q p) =
      (sourceGraph t padding tables).edgeSatisfied
        (fun z => labels (vertexOrder t padding z)) (v, p) := by
  change PortTables.accepts (ofCloudTables t padding tables)
    (vertexOrder t padding v, portOrder q p) (labels (vertexOrder t padding v))
    (labels (PortTables.rotation (ofCloudTables t padding tables)
      (vertexOrder t padding v, portOrder q p)).1) = _
  rw [rotation_ofCloudTables, accepts_ofCloudTables]
  rfl

/-- Numbering preserves the rejection count for every labeling. -/
theorem rejectionCount_ofCloudTables (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (labels : Fin (vertexCount t padding) → GraphTables.Label) :
    (PortTables.baseGraph (ofCloudTables t padding tables)).rejectionCount labels =
      (sourceGraph t padding tables).rejectionCount
        (fun z => labels (vertexOrder t padding z)) := by
  classical
  unfold ConstraintGraph.rejectionCount
  symm
  apply Finset.card_equiv (Equiv.prodCongr (vertexOrder t padding) (portOrder q))
  rintro ⟨v, p⟩
  simp only [ConstraintGraph.mem_rejectedDarts, Equiv.prodCongr_apply,
    Prod.map_apply, edgeSatisfied_ofCloudTables]

def liftedLabel (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (labels : Fin t.vertices → GraphTables.Label) :
    Fin (vertexCount t padding) → GraphTables.Label :=
  fun z => labels (paddedOwner (GraphTables.semantics t) (fun v => Fin (padding v))
    ((vertexOrder t padding).symm z))

end UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables

/-!
# Exact serialized family tables at actual regularization vertices

The geometric family maps request zero to a one-vertex table. Empty clouds in
regularization instead remain empty. The bridge therefore requires positive
cloud size, derived here from each actual original or dummy vertex.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingFamilyBridge

open PreprocessingCloudIndex PreprocessingRegularTables ExpanderTableWords
open UniqueGamesTheorem.Foundations.Complexity (encodeWords)

/-- An empty cloud has no padding vertices either. -/
theorem padding_zero_of_cloudSize_zero (t : GraphTables.Table) (v : Fin t.vertices)
    (hk : cloudSize t v = 0) : padding t v = 0 := by
  simp only [padding, hk, PreprocessingLevels.cloudPaddedSize_zero, Nat.sub_zero]

/-- Every actual dummy vertex also belongs to a positive original cloud. -/
theorem cloudSize_pos_of_dummy (t : GraphTables.Table) (v : Fin t.vertices)
    (j : Fin (padding t v)) : 0 < cloudSize t v := by
  by_contra h
  have hk := Nat.eq_zero_of_not_pos h
  have hp := padding_zero_of_cloudSize_zero t v hk
  have hj := j.isLt
  omega

end UniqueGamesTheorem.Foundations.PCP.PreprocessingFamilyBridge

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularInternalRow
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
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

open Turing MachineComposition
open PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ : Type} [DecidableEq K]

/-- A direct instantiation of the real affine getter on the actual rotor words. -/
theorem rotationLookupTrace {n q : Nat} (table : ExpanderTables.Table n q)
    (i : Fin n) (p : Fin q) (source : K) (tape : Fin 5 → K)
    (distinct : Function.Injective tape) (outside : ∀ a, source ≠ tape a)
    (labels : MachineAffineLookup.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (code : ∀ l, program (labels l) =
      MachineAffineLookup.instruction source tape q p.val labels exit l)
    (base : K → List Bool)
    (tableWord : base (tape 0) = encodeWords (ExpanderTableWords.rotationWords table))
    (scratchEmpty : base (tape 4) = []) (suffix : List Bool)
    (sourceWord : base source = encodeWord i.val ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[MachineAffineLookup.steps
        (ExpanderTableWords.rotationWords table) i.val q p.val]
      (some ⟨some (labels .seed), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), MachineAffineLookup.finalTapes tape base
        (ExpanderTableWords.rotationWords table) (q * i.val + p.val)
        (q * (ExpanderTables.lookup table (i, p)).1.val +
          (ExpanderTables.lookup table (i, p)).2.val)⟩ :=
  MachineAffineLookup.affineLookupTrace source tape distinct outside q p.val labels exit
    program code base _ tableWord scratchEmpty i.val suffix sourceWord _
    (selected_rotation table i p) ambient register

/-- The return port is copied from its physical unary tape before fixed-slope
arithmetic adds the actual selected global target. -/
def finishInstruction (q : Nat) (tape : Fin 8 → K) (labels : FinishLabel → Λ)
    (exit : Option Λ) : FinishLabel → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .seedReturn => MachineUnaryAffineAt.seed (tape 4) 0 (labels .copyReturn)
  | .copyReturn => MachineUnaryAffineAt.scan (tape 2) (tape 3) (tape 4) 1
      (labels .copyReturn) (labels .restoreReturn)
  | .restoreReturn => Reduction.MachineTransfer.loopAt (tape 3) (tape 2) id false
      (labels .restoreReturn) (some (labels .affine))
  | .affine => MachineUnaryAffineAt.scan (tape 1) (tape 3) (tape 4) (q + 1)
      (labels .affine) (labels .restoreTarget)
  | .restoreTarget => Reduction.MachineTransfer.loopAt (tape 3) (tape 1) id false
      (labels .restoreTarget) (some (labels .equality))
  | .equality => pushWord (tape 5) equalityBits.reverse
      (.goto fun _ => labels (.row .relationRead))
  | .row stage => MachineTableRows.routine (finishFields tape) (tape 6) (tape 7) (tape 3)
      (fun l => labels (.row l)) (some (labels .clearReverse)) stage
  | .clearReverse => MachineDrain.drain (tape 4) (labels .clearReverse)
      (some (labels .clearEquality))
  | .clearEquality => MachineDrain.drain (tape 5) (labels .clearEquality) exit

def rotorInstruction (q : Nat) (positive : 0 < q) (p : Fin q)
    (tape : Fin 8 → K) (labels : RotorLabel q → Λ) (exit : Option Λ) :
    RotorLabel q → TM2.Stmt (Alphabet (K := K)) Λ (MachineFixedDivMod.State σ q)
  | .lookup stage => MachineAffineLookup.instruction (tape 0) (rotorLookupTapes tape)
      q p.val (fun l => labels (.lookup l)) (some (labels .initialize_)) stage
  | .initialize_ => .push (tape 6) (fun _ => false)
      (.push (tape 7) (fun _ => false) (.goto fun _ => labels .divide))
  | .divide => MachineFixedDivMod.scanLoop q positive (tape 4) (tape 6)
      (labels .divide) (fun r => labels (.emit r))
  | .emit r => MachineFixedDivMod.emitter q positive (tape 7) exit r

def rotorFinalTapes {n q : Nat} (table : ExpanderTables.Table n q) (i : Fin n) (p : Fin q)
    (tape : Fin 8 → K) (base : K → List Bool) : K → List Bool :=
  MachineFixedDivMod.unaryTapes (tape 4) (tape 6) (tape 7)
    (MachineAffineLookup.finalTapes (rotorLookupTapes tape) base
      (ExpanderTableWords.rotationWords table) (q * i.val + p.val)
      (q * (ExpanderTables.lookup table (i, p)).1.val +
        (ExpanderTables.lookup table (i, p)).2.val))
    0 (ExpanderTables.lookup table (i, p)).1.val
      (ExpanderTables.lookup table (i, p)).2.val [] [] []

def rotorSteps {n q : Nat} (table : ExpanderTables.Table n q) (i : Fin n) (p : Fin q) : Nat :=
  MachineAffineLookup.steps (ExpanderTableWords.rotationWords table) i.val q p.val +
    1 + (q * (ExpanderTables.lookup table (i, p)).1.val +
      (ExpanderTables.lookup table (i, p)).2.val + 2)

/-- The actual stored reverse row is read and physically divided by the fixed
degree. Both output fields equal the coordinates of the actual table lookup. -/
theorem rotorTrace {n q : Nat} (positive : 0 < q) (table : ExpanderTables.Table n q)
    (i : Fin n) (p : Fin q) (tape : Fin 8 → K) (distinct : Function.Injective tape)
    (labels : RotorLabel q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (MachineFixedDivMod.State σ q))
    (code : ∀ l, program (labels l) = rotorInstruction q positive p tape labels exit l)
    (base : K → List Bool)
    (sourceWord : base (tape 0) = encodeWord i.val)
    (tableWord : base (tape 1) = encodeWords (ExpanderTableWords.rotationWords table))
    (flatEmpty : base (tape 4) = []) (scratchEmpty : base (tape 5) = [])
    (localEmpty : base (tape 6) = []) (returnEmpty : base (tape 7) = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[rotorSteps table i p]
      (some ⟨some (labels (.lookup .seed)),
        ((ambient, MachineFixedDivMod.residue q positive 0), register), base⟩) =
      some ⟨exit, ((ambient, MachineFixedDivMod.residue q positive 0), none),
        rotorFinalTapes table i p tape base⟩ := by
  have hd (a b : Fin 8) (h : a ≠ b) : tape a ≠ tape b := fun e => h (distinct e)
  let a := q * (ExpanderTables.lookup table (i, p)).1.val +
    (ExpanderTables.lookup table (i, p)).2.val
  let looked := MachineAffineLookup.finalTapes (rotorLookupTapes tape) base
    (ExpanderTableWords.rotationWords table) (q * i.val + p.val) a
  let initialized := Function.update (Function.update looked (tape 6) (encodeWord 0))
    (tape 7) (encodeWord 0)
  have lookupRun : (advance (TM2.step program))^[MachineAffineLookup.steps
      (ExpanderTableWords.rotationWords table) i.val q p.val]
      (some ⟨some (labels (.lookup .seed)),
        ((ambient, MachineFixedDivMod.residue q positive 0), register), base⟩) =
      some ⟨some (labels .initialize_),
        ((ambient, MachineFixedDivMod.residue q positive 0), none), looked⟩ := by
    exact rotationLookupTrace table i p (tape 0) (rotorLookupTapes tape)
      (rotorLookupTapes_injective tape distinct) (rotorLookupTapes_outside tape distinct)
      (fun l => labels (.lookup l)) (some (labels .initialize_)) program
      (fun l => code (.lookup l)) base tableWord scratchEmpty []
      (by simpa using sourceWord) (ambient, MachineFixedDivMod.residue q positive 0) register
  have lookedOther (k : Fin 8) (h2 : k ≠ 2) (h3 : k ≠ 3) (h4 : k ≠ 4) :
      looked (tape k) = base (tape k) := by
    exact MachineAffineLookup.finalTapes_other (rotorLookupTapes tape) base
      (ExpanderTableWords.rotationWords table) (q * i.val + p.val) a (tape k)
      (hd k 2 h2) (hd k 3 h3) (hd k 4 h4)
  have lookedFlat : looked (tape 4) = encodeWord a := by
    change MachineAffineLookup.finalTapes (rotorLookupTapes tape) base
      (ExpanderTableWords.rotationWords table) (q * i.val + p.val) a
      (rotorLookupTapes tape 3) = _
    rw [MachineAffineLookup.finalTapes_output]
    change encodeWord a ++ base (tape 4) = _
    rw [flatEmpty, List.append_nil]
  have initRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .initialize_),
        ((ambient, MachineFixedDivMod.residue q positive 0), none), looked⟩) =
      some ⟨some (labels .divide),
        ((ambient, MachineFixedDivMod.residue q positive 0), none), initialized⟩ := by
    change some (TM2.stepAux (program (labels .initialize_)) _ _) = _
    rw [code]
    simp [rotorInstruction, TM2.stepAux, initialized, encodeWord,
      lookedOther 6 (by decide) (by decide) (by decide),
      lookedOther 7 (by decide) (by decide) (by decide),
      hd 7 6 (by decide), localEmpty, returnEmpty]
  have initialFrame : MachineFixedDivMod.unaryTapes (tape 4) (tape 6) (tape 7)
      looked a 0 0 [] [] [] = initialized := by
    simp only [MachineFixedDivMod.unaryTapes, MachineFixedDivMod.tapes,
      MachineCopy.forkTapes, List.append_nil, ← lookedFlat, Function.update_eq_self,
      initialized]
  have finalFrame : MachineFixedDivMod.unaryTapes (tape 4) (tape 6) (tape 7)
      looked 0 (a / q) (a % q) [] [] [] = rotorFinalTapes table i p tape base := by
    dsimp only [a]
    rw [selected_rotation_div positive, selected_rotation_mod positive]
    rfl
  have divideRun : (advance (TM2.step program))^[a + 2]
      (some ⟨some (labels .divide),
        ((ambient, MachineFixedDivMod.residue q positive 0), none), initialized⟩) =
      some ⟨exit, ((ambient, MachineFixedDivMod.residue q positive 0), none),
        rotorFinalTapes table i p tape base⟩ := by
    simpa only [initialFrame, finalFrame] using
      MachineFixedDivMod.divModTrace q positive (tape 4) (tape 6) (tape 7)
        (hd 4 6 (by decide)) (hd 4 7 (by decide)) (hd 6 7 (by decide))
        (labels .divide) (fun r => labels (.emit r)) exit program (code .divide)
        (fun r => code (.emit r)) looked a [] [] [] ambient none
  exact joinTrace (joinTrace lookupRun initRun) divideRun

theorem rotorSteps_le {n q : Nat} (table : ExpanderTables.Table n q) (i : Fin n) (p : Fin q) :
    rotorSteps table i p ≤ 2 * i.val +
      5 * (encodeWords (ExpanderTableWords.rotationWords table)).length + n * q + 8 := by
  have hl := MachineAffineLookup.steps_le (ExpanderTableWords.rotationWords table)
    i.val q p.val _ (selected_rotation table i p)
  have hb := (ExpanderTables.rowIndex n q (ExpanderTables.lookup table (i, p))).isLt
  rw [ExpanderTables.rowIndex_val] at hb
  unfold rotorSteps
  omega

def selectControl : SelectControl → TM2.Stmt SelectAlphabet SelectLabel (SelectState σ)
  | .compare stage => MachineUnaryLessAt.statement compareSlots
      (fun s => .inr (.compare s)) (some (.inr .choose)) stage
  | .choose => .branch (fun s => s.1.2)
      (.load (fun s => ((s.1.1, false), none))
        (.goto fun _ => .inr (.copy .oldLocal .seed)))
      (.load (fun s => ((s.1.1, false), none))
        (.goto fun _ => .inr (.copy .dummyLocal .seed)))
  | .copy kind .seed => MachineUnaryAffineAt.seed (copyDestination kind) 0
      (.inr (.copy kind .scan))
  | .copy kind .scan => MachineUnaryAffineAt.scan (copySource kind) selectScratch
      (copyDestination kind) 1 (.inr (.copy kind .scan)) (.inr (.copy kind .restore))
  | .copy kind .restore => Reduction.MachineTransfer.loopAt selectScratch (copySource kind)
      id false (.inr (.copy kind .restore)) (some (afterCopy kind))
  | .subtract => MachineUnaryLessAt.scan subtractSlots (.inr .subtract)
      (.inr (.copy .dummyDifference .seed))
  | .add kind .scan => MachineUnaryAffineAt.scan (addSource kind) selectScratch selectOutput 1
      (.inr (.add kind .scan)) (.inr (.add kind .restore))
  | .add kind .restore => Reduction.MachineTransfer.loopAt selectScratch (addSource kind)
      id false (.inr (.add kind .restore)) (some (afterAdd kind))
  | .cleanup i => MachineDrain.drain (cleanupTape i) (.inr (.cleanup i)) (afterCleanup i)

/-- All arithmetic is on extra tapes. The old-dart branch literally contains
the shared selector program, with only static tape, label and state transport. -/
def rawSelectProgram : SelectLabel → TM2.Stmt RawSelectAlphabet SelectLabel (SelectState σ) :=
  MachineStateEquiv.program (selectStateEquiv σ)
    (MachineEmbedding.program (some (.inr (.cleanup 0))) MachineCloudSelect.program
      (fun control => MachineStateEquiv.statement (selectStateEquiv σ).symm
        (MachineAlphabetTransport.statement selectAlphabet_eq.symm (selectControl control))))

def selectProgram : SelectLabel → TM2.Stmt SelectAlphabet SelectLabel (SelectState σ) :=
  MachineAlphabetTransport.program selectAlphabet_eq rawSelectProgram

@[simp] theorem selectProgram_control (l : SelectControl) :
    selectProgram (σ := σ) (.inr l) = selectControl l := by
  change MachineAlphabetTransport.statement selectAlphabet_eq
    (MachineStateEquiv.statement (selectStateEquiv σ)
      (MachineStateEquiv.statement (selectStateEquiv σ).symm
        (MachineAlphabetTransport.statement selectAlphabet_eq.symm (selectControl l)))) = _
  have h := MachineStateEquiv.statement_symm_statement (selectStateEquiv σ).symm
    (MachineAlphabetTransport.statement selectAlphabet_eq.symm (selectControl (σ := σ) l))
  simp only [Equiv.symm_symm] at h
  rw [h]
  exact MachineAlphabetTransport.statement_roundtrip selectAlphabet_eq _

def selectCleanState (ambient : σ) (register : Option Bool) : SelectState σ :=
  (((ambient, .checking), false), register)

/-- One physical strict comparison decides the branch and preserves both
input indices. In particular equality belongs to the dummy branch. -/
theorem selectComparisonTrace (base : SelectTape → List Bool) (j k : Nat)
    (hj : base (.inr .localIndex) = encodeWord j)
    (hk : base (.inr .cloudSize) = encodeWord k)
    (hl : base (.inr .savedLeft) = []) (hr : base (.inr .savedRight) = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step selectProgram))^[MachineUnaryLessAt.steps j k + 1]
      (some ⟨some (.inr (.compare .scan)), selectCleanState ambient register, base⟩) =
      some ⟨some (.inr (.copy (if j < k then .oldLocal else .dummyLocal) .seed)),
        selectCleanState ambient none, base⟩ := by
  have h := MachineUnaryLessAt.lessThanTrace compareSlots
    (fun l => .inr (.compare l)) (some (.inr .choose)) selectProgram
    (fun l => by rw [selectProgram_control]; rfl)
    base j k [] [] (by change base (.inr .localIndex) = _; simpa only [List.append_nil] using hj)
    (by change base (.inr .cloudSize) = _; simpa only [List.append_nil] using hk) hl hr
    (ambient, MachineCloudSelect.Phase.checking) false register
  simp only [selectCleanState]
  rw [Function.iterate_succ_apply', h, advance_some]
  change some (TM2.stepAux (selectProgram (.inr .choose)) _ _) = _
  rw [selectProgram_control]
  by_cases hlt : j < k <;> simp [selectControl, TM2.stepAux, hlt]

/-- Actual preserving unary copy used to construct both the selector query
and the dummy-index operands. -/
theorem selectCopyTrace (kind : SelectCopy) (base : SelectTape → List Bool)
    (a : Nat) (hword : base (copySource kind) = encodeWord a)
    (hscratch : base selectScratch = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step selectProgram))^[2 * (a + 1) + 1]
      (some ⟨some (.inr (.copy kind .seed)), selectCleanState ambient register, base⟩) =
      some ⟨some (afterCopy kind), selectCleanState ambient none,
        Function.update base (copyDestination kind)
          (encodeWord a ++ base (copyDestination kind))⟩ := by
  have h₁ : copySource kind ≠ selectScratch := by cases kind <;> decide
  have h₂ : copySource kind ≠ copyDestination kind := by cases kind <;> decide
  have h₃ : selectScratch ≠ copyDestination kind := by cases kind <;> decide
  simpa only [Nat.one_mul, Nat.add_zero, selectCleanState] using
    MachineUnaryAffineAt.seededAffineTrace (copySource kind) selectScratch (copyDestination kind)
      h₁ h₂ h₃ 1 0 (.inr (.copy kind .seed)) (.inr (.copy kind .scan))
      (.inr (.copy kind .restore)) (some (afterCopy kind)) selectProgram
      (by rw [selectProgram_control]; rfl) (by rw [selectProgram_control]; rfl)
      (by rw [selectProgram_control]; rfl) base a [] (by simpa using hword) hscratch
      ((ambient, MachineCloudSelect.Phase.checking), false) register

/-- The two runtime addends are read physically; no input-dependent offset
is captured by a single finite instruction. -/
theorem selectAddTrace (kind : SelectAdd) (base : SelectTape → List Bool)
    (a b : Nat) (hword : base (addSource kind) = encodeWord a)
    (houtput : base selectOutput = encodeWord b) (hscratch : base selectScratch = [])
    (ambient : σ) :
    (advance (TM2.step selectProgram))^[2 * (a + 1)]
      (some ⟨some (.inr (.add kind .scan)), selectCleanState ambient none, base⟩) =
      some ⟨some (afterAdd kind), selectCleanState ambient none,
        Function.update base selectOutput (encodeWord (a + b))⟩ := by
  have h₁ : addSource kind ≠ selectScratch := by cases kind <;> decide
  have h₂ : addSource kind ≠ selectOutput := by cases kind <;> decide
  have h₃ : selectScratch ≠ selectOutput := by decide
  have frame (n : Nat) : MachineUnaryAffineAt.tapes (addSource kind) selectScratch selectOutput
      base (encodeWord a ++ []) [] (encodeWord n ++ []) =
        Function.update base selectOutput (encodeWord n) := by
    simp only [List.append_nil]
    rw [← hword, ← hscratch]
    simp only [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes, Function.update_eq_self]
  have h := MachineUnaryAffineAt.affineTrace (addSource kind) selectScratch selectOutput
    h₁ h₂ h₃ 1 (.inr (.add kind .scan)) (.inr (.add kind .restore))
    (some (afterAdd kind)) selectProgram
    (by rw [selectProgram_control]; rfl) (by rw [selectProgram_control]; rfl)
    base a b [] [] ((ambient, MachineCloudSelect.Phase.checking), false) none
  rw [frame, frame] at h
  rw [← houtput, Function.update_eq_self] at h
  simpa only [Nat.one_mul, selectCleanState] using h

inductive CoreLabel (q : Nat)
  | rotor (stage : RotorLabel q)
  | select (stage : SelectLabel)
  | finish (stage : FinishLabel)
  | cleanup (i : Fin 10)
  deriving DecidableEq, Fintype

def coreEntry (q : Nat) : CoreLabel q := .rotor (.lookup .seed)

def selectMemory (graph : List Bool) (j v k offset m : Nat)
    (query output savedLeft savedRight localWork sizeWork : List Bool) :
    SelectTape → List Bool :=
  selectToBoolTapes (MachineEmbedding.tapes
    (MachineCloudSelect.memory graph [] query [] [] [] output)
    (selectExtraMemory j v k offset m savedLeft savedRight localWork sizeWork))

@[simp] theorem selectMemory_query (graph : List Bool) (j v k o m : Nat)
    (query output a b c d : List Bool) :
    selectMemory graph j v k o m query output a b c d selectQuery = query := rfl

@[simp] theorem selectMemory_output (graph : List Bool) (j v k o m : Nat)
    (query output a b c d : List Bool) :
    selectMemory graph j v k o m query output a b c d selectOutput = output := rfl

@[simp] theorem selectMemory_scratch (graph : List Bool) (j v k o m : Nat)
    (query output a b c d : List Bool) :
    selectMemory graph j v k o m query output a b c d selectScratch = [] := rfl

@[simp] theorem selectMemory_extra (graph : List Bool) (j v k o m : Nat)
    (query output a b c d : List Bool) (z : SelectExtraTape) :
    selectMemory graph j v k o m query output a b c d (.inr z) =
      selectExtraMemory j v k o m a b c d z := rfl

@[simp] theorem update_selectMemory_query (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) selectQuery word =
      selectMemory graph j v k o m word output a b c d := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

@[simp] theorem update_selectMemory_output (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) selectOutput word =
      selectMemory graph j v k o m query word a b c d := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

@[simp] theorem update_selectMemory_local (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) (.inr .localWork) word =
      selectMemory graph j v k o m query output a b word d := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

@[simp] theorem update_selectMemory_size (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) (.inr .sizeWork) word =
      selectMemory graph j v k o m query output a b c word := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

@[simp] theorem update_selectMemory_left (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) (.inr .savedLeft) word =
      selectMemory graph j v k o m query output word b c d := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

@[simp] theorem update_selectMemory_right (graph : List Bool) (j v k o m : Nat)
    (query output a b c d word : List Bool) :
    Function.update (selectMemory graph j v k o m query output a b c d) (.inr .savedRight) word =
      selectMemory graph j v k o m query output a word c d := by
  funext z
  cases z with
  | inl z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => cases z; rfl
  | inr z => cases z <;> rfl

theorem selectCleanupTrace (graph : List Bool) (j v k o m : Nat)
    (query output a b c d : List Bool) (ambient : σ) :
    (advance (TM2.step selectProgram))^[query.length + c.length + d.length + a.length + b.length + 5]
      (some ⟨some (.inr (.cleanup 0)), selectCleanState ambient none,
        selectMemory graph j v k o m query output a b c d⟩) =
      some ⟨none, selectCleanState ambient none,
        selectMemory graph j v k o m [] output [] [] [] []⟩ := by
  have h0 := MachineDrain.drainTrace selectQuery (.inr (.cleanup 0))
    (some (.inr (.cleanup 1))) selectProgram
    (by rw [selectProgram_control]; rfl)
    (selectMemory graph j v k o m query output a b c d) query
    ((ambient, MachineCloudSelect.Phase.checking), false) none
  simp only [update_selectMemory_query] at h0
  have h1 := MachineDrain.drainTrace (.inr .localWork) (.inr (.cleanup 1))
    (some (.inr (.cleanup 2))) selectProgram
    (by rw [selectProgram_control]; rfl)
    (selectMemory graph j v k o m [] output a b c d) c
    ((ambient, MachineCloudSelect.Phase.checking), false) none
  simp only [update_selectMemory_local] at h1
  have h2 := MachineDrain.drainTrace (.inr .sizeWork) (.inr (.cleanup 2))
    (some (.inr (.cleanup 3))) selectProgram
    (by rw [selectProgram_control]; rfl)
    (selectMemory graph j v k o m [] output a b [] d) d
    ((ambient, MachineCloudSelect.Phase.checking), false) none
  simp only [update_selectMemory_size] at h2
  have h3 := MachineDrain.drainTrace (.inr .savedLeft) (.inr (.cleanup 3))
    (some (.inr (.cleanup 4))) selectProgram
    (by rw [selectProgram_control]; rfl)
    (selectMemory graph j v k o m [] output a b [] []) a
    ((ambient, MachineCloudSelect.Phase.checking), false) none
  simp only [update_selectMemory_left] at h3
  have h4 := MachineDrain.drainTrace (.inr .savedRight) (.inr (.cleanup 4))
    none selectProgram (by rw [selectProgram_control]; rfl)
    (selectMemory graph j v k o m [] output [] b [] []) b
    ((ambient, MachineCloudSelect.Phase.checking), false) none
  simp only [update_selectMemory_right] at h4
  have total := joinTrace (joinTrace (joinTrace (joinTrace h0 h1) h2) h3) h4
  have hn : query.length + c.length + d.length + a.length + b.length + 5 =
      ((((query.length + 1) + (c.length + 1)) + (d.length + 1)) + (a.length + 1)) +
        (b.length + 1) := by omega
  rw [hn]
  exact total

/-- The dummy branch uses the actual truncating-subtraction scan on copied
operands. The original local index, cloud size, prefix and dart count survive. -/
theorem selectDummyTrace (graph : List Bool) (j v k o m : Nat) (hk : k ≤ j)
    (ambient : σ) :
    (advance (TM2.step selectProgram))^[dummySelectSteps j k o m]
      (some ⟨some (.inr (.copy .dummyLocal .seed)), selectCleanState ambient none,
        selectMemory graph j v k o m [] [] [] [] [] []⟩) =
      some ⟨none, selectCleanState ambient none,
        selectMemory graph j v k o m [] (encodeWord (m + o + (j - k))) [] [] [] []⟩ := by
  have hjcopy := selectCopyTrace .dummyLocal
    (selectMemory graph j v k o m [] [] [] [] [] []) j rfl rfl ambient none
  simp only [copyDestination, afterCopy, selectMemory_extra, selectExtraMemory,
    update_selectMemory_local, List.append_nil] at hjcopy
  have hkcopy := selectCopyTrace .dummySize
    (selectMemory graph j v k o m [] [] [] [] (encodeWord j) []) k rfl rfl ambient none
  simp only [copyDestination, afterCopy, selectMemory_extra, selectExtraMemory,
    update_selectMemory_size, List.append_nil] at hkcopy
  have scanFrame (left right savedLeft savedRight : List Bool) :
      MachineUnaryLessAt.tapes subtractSlots
        (selectMemory graph j v k o m [] [] [] [] [] [])
        left right savedLeft savedRight =
      selectMemory graph j v k o m [] [] savedLeft savedRight left right := by
    simp only [MachineUnaryLessAt.tapes,
      show subtractSlots 0 = .inr .localWork from rfl,
      show subtractSlots 1 = .inr .sizeWork from rfl,
      show subtractSlots 2 = .inr .savedLeft from rfl,
      show subtractSlots 3 = .inr .savedRight from rfl,
      update_selectMemory_local, update_selectMemory_size,
      update_selectMemory_left, update_selectMemory_right]
  have hscan := MachineUnaryLessAt.scanTrace subtractSlots (.inr .subtract)
    (.inr (.copy .dummyDifference .seed)) selectProgram
    (by rw [selectProgram_control]; rfl)
    (selectMemory graph j v k o m [] [] [] [] [] [])
    j k [] [] [] [] (ambient, MachineCloudSelect.Phase.checking) false none
  simp only [List.append_nil, scanFrame, Nat.min_eq_right hk, Nat.sub_eq_zero_of_le hk,
    show ¬ j < k from Nat.not_lt_of_ge hk, decide_false] at hscan
  have hdiffcopy := selectCopyTrace .dummyDifference
    (selectMemory graph j v k o m [] [] (List.replicate k true) (List.replicate k true)
      (encodeWord (j - k)) (encodeWord 0)) (j - k) rfl rfl ambient none
  simp only [copyDestination, afterCopy, selectMemory_output, update_selectMemory_output, List.append_nil] at hdiffcopy
  have hprefix := selectAddTrace .prefixOffset
    (selectMemory graph j v k o m [] (encodeWord (j - k))
      (List.replicate k true) (List.replicate k true) (encodeWord (j - k)) (encodeWord 0))
    o (j - k) rfl rfl rfl ambient
  simp only [afterAdd, update_selectMemory_output] at hprefix
  have hm := selectAddTrace .darts
    (selectMemory graph j v k o m [] (encodeWord (o + (j - k)))
      (List.replicate k true) (List.replicate k true) (encodeWord (j - k)) (encodeWord 0))
    m (o + (j - k)) rfl rfl rfl ambient
  simp only [afterAdd, update_selectMemory_output, ← Nat.add_assoc] at hm
  have hcleanup := selectCleanupTrace graph j v k o m []
    (encodeWord (m + o + (j - k))) (List.replicate k true) (List.replicate k true)
    (encodeWord (j - k)) (encodeWord 0) ambient
  have hcleanSteps : ([] : List Bool).length + (encodeWord (j - k)).length + (encodeWord 0).length +
      (List.replicate k true).length + (List.replicate k true).length + 5 = j + k + 7 := by
    simp only [List.length_nil, encodeWord_length, List.length_replicate]
    omega
  rw [hcleanSteps] at hcleanup
  exact joinTrace (joinTrace (joinTrace (joinTrace (joinTrace (joinTrace
    hjcopy hkcopy) hscan) hdiffcopy) hprefix) hm) hcleanup

def coreSelectTape : SelectTape → CoreTape
  | .inl (.inl .original) => 0
  | .inl (.inl .work) => 17
  | .inl (.inl .target) => 16
  | .inl (.inl .scratch) => 9
  | .inl (.inl .count) => 18
  | .inl (.inl .spare) => 19
  | .inl (.inr ()) => 15
  | .inr .localIndex => 13
  | .inr .owner => 2
  | .inr .cloudSize => 4
  | .inr .prefixOffset => 5
  | .inr .darts => 6
  | .inr .savedLeft => 20
  | .inr .savedRight => 21
  | .inr .localWork => 22
  | .inr .sizeWork => 23

def coreSelectView : CoreTape → Option SelectTape :=
  ![some (.inl (.inl .original)), none, some (.inr .owner), none,
    some (.inr .cloudSize), some (.inr .prefixOffset), some (.inr .darts), none, none,
    some (.inl (.inl .scratch)), none, none, none, some (.inr .localIndex), none,
    some (.inl (.inr ())), some (.inl (.inl .target)), some (.inl (.inl .work)),
    some (.inl (.inl .count)), some (.inl (.inl .spare)),
    some (.inr .savedLeft), some (.inr .savedRight),
    some (.inr .localWork), some (.inr .sizeWork), none, none, none]

theorem coreSelectView_left (k : SelectTape) : coreSelectView (coreSelectTape k) = some k := by
  cases k with
  | inl k =>
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k; rfl
  | inr k => cases k <;> rfl

theorem coreSelectView_right (j : CoreTape) (k : SelectTape)
    (h : coreSelectView j = some k) : coreSelectTape k = j := by
  fin_cases j <;> simp [coreSelectView] at h
  all_goals subst k; rfl

def coreSelectStateEquiv (σ : Type) (q : Nat) :
    SelectState (σ × (MachineFixedBlockMap.Buffer 4096 × Fin q)) ≃ CoreState σ q where
  toFun s := ((s.1.1.1.1, (s.1.1.1.2.1, (s.1.1.1.2.2, (s.1.2, s.1.1.2)))), s.2)
  invFun s := ((((s.1.1, (s.1.2.1, s.1.2.2.1)), s.1.2.2.2.2), s.1.2.2.2.1), s.2)
  left_inv s := by rcases s with ⟨⟨⟨⟨a,⟨b,c⟩⟩,d⟩,e⟩,f⟩; rfl
  right_inv s := by rcases s with ⟨⟨a,⟨b,⟨c,⟨d,e⟩⟩⟩⟩,f⟩; rfl

def coreAfterCleanup {q : Nat} (labels : CoreLabel q → Λ) (exit : Option Λ) (i : Fin 10) :
    Option Λ :=
  if h : i.val + 1 < 10 then some (labels (.cleanup ⟨i.val + 1,h⟩)) else exit

/-- The whole internal-row program has only fixed q and p in its code. -/
def coreInstruction (q : Nat) (positive : 0 < q) (p : Fin q)
    (labels : CoreLabel q → Λ) (exit : Option Λ) :
    CoreLabel q → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q)
  | .rotor stage => MachineStateEquiv.statement (coreRotorStateEquiv σ q)
      (rotorInstruction q positive p coreRotorTapes
        (fun l => labels (.rotor l)) (some (labels (.select (.inr (.compare .scan))))) stage)
  | .select stage => MachineCloudPadding.Placement.statement coreSelectTape
      (fun l => labels (.select l)) (some (labels (.finish .seedReturn)))
      (MachineStateEquiv.statement (coreSelectStateEquiv σ q) (selectProgram stage))
  | .finish stage => finishInstruction q coreFinishTapes
      (fun l => labels (.finish l)) (some (labels (.cleanup 0))) stage
  | .cleanup i => MachineDrain.drain (coreCleanupTape i) (labels (.cleanup i))
      (coreAfterCleanup labels exit i)

@[simp] theorem coreMemory_update_output (graph : List Bool) (x v i k o m : Nat)
    (rotor output query scan flat localIndex returnPort selected newOutput : List Bool) :
    Function.update (coreMemory graph x v i k o m rotor output query scan flat
      localIndex returnPort selected) (8 : CoreTape) newOutput =
      coreMemory graph x v i k o m rotor newOutput query scan flat localIndex returnPort selected := by
  funext z
  fin_cases z <;> rfl

theorem coreRotorTapes_injective : Function.Injective coreRotorTapes := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [coreRotorTapes]

theorem coreFinishTapes_injective : Function.Injective coreFinishTapes := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [coreFinishTapes]

def coreCleaned (base : CoreTape → List Bool) : CoreTape → List Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
      (Function.update base 10 []) 11 []) 12 []) 13 []) 14 []) 15 []) 9 []) 16 []) 17 []) 18 []

def coreCleanupSteps (base : CoreTape → List Bool) : Nat :=
  (base 10).length + (base 11).length + (base 12).length + (base 13).length +
  (base 14).length + (base 15).length + (base 9).length + (base 16).length +
  (base 17).length + (base 18).length + 10

theorem coreCleanupTrace (q : Nat) (positive : 0 < q) (p : Fin q)
    (labels : CoreLabel q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = coreInstruction q positive p labels exit l)
    (base : CoreTape → List Bool)
    (ambient : σ × (MachineFixedBlockMap.Buffer 4096 ×
      (Fin q × (Bool × MachineCloudSelect.Phase)))) :
    (advance (TM2.step program))^[coreCleanupSteps base]
      (some ⟨some (labels (.cleanup 0)), (ambient, none), base⟩) =
      some ⟨exit, (ambient, none), coreCleaned base⟩ := by
  let b1 := Function.update base (10 : CoreTape) []
  have h0 := MachineDrain.drainTrace (10 : CoreTape) (labels (.cleanup 0))
    (some (labels (.cleanup 1))) program (code (.cleanup 0)) base (base 10) ambient none
  rw [Function.update_eq_self] at h0
  let b2 := Function.update b1 (11 : CoreTape) []
  have h1 := MachineDrain.drainTrace (11 : CoreTape) (labels (.cleanup 1))
    (some (labels (.cleanup 2))) program (code (.cleanup 1)) b1 (b1 11) ambient none
  rw [Function.update_eq_self] at h1
  have hw1 : b1 11 = base 11 := by simp [b1]
  rw [hw1] at h1
  let b3 := Function.update b2 (12 : CoreTape) []
  have h2 := MachineDrain.drainTrace (12 : CoreTape) (labels (.cleanup 2))
    (some (labels (.cleanup 3))) program (code (.cleanup 2)) b2 (b2 12) ambient none
  rw [Function.update_eq_self] at h2
  have hw2 : b2 12 = base 12 := by simp [b1, b2]
  rw [hw2] at h2
  let b4 := Function.update b3 (13 : CoreTape) []
  have h3 := MachineDrain.drainTrace (13 : CoreTape) (labels (.cleanup 3))
    (some (labels (.cleanup 4))) program (code (.cleanup 3)) b3 (b3 13) ambient none
  rw [Function.update_eq_self] at h3
  have hw3 : b3 13 = base 13 := by simp [b1, b2, b3]
  rw [hw3] at h3
  let b5 := Function.update b4 (14 : CoreTape) []
  have h4 := MachineDrain.drainTrace (14 : CoreTape) (labels (.cleanup 4))
    (some (labels (.cleanup 5))) program (code (.cleanup 4)) b4 (b4 14) ambient none
  rw [Function.update_eq_self] at h4
  have hw4 : b4 14 = base 14 := by simp [b1, b2, b3, b4]
  rw [hw4] at h4
  let b6 := Function.update b5 (15 : CoreTape) []
  have h5 := MachineDrain.drainTrace (15 : CoreTape) (labels (.cleanup 5))
    (some (labels (.cleanup 6))) program (code (.cleanup 5)) b5 (b5 15) ambient none
  rw [Function.update_eq_self] at h5
  have hw5 : b5 15 = base 15 := by simp [b1, b2, b3, b4, b5]
  rw [hw5] at h5
  let b7 := Function.update b6 (9 : CoreTape) []
  have h6 := MachineDrain.drainTrace (9 : CoreTape) (labels (.cleanup 6))
    (some (labels (.cleanup 7))) program (code (.cleanup 6)) b6 (b6 9) ambient none
  rw [Function.update_eq_self] at h6
  have hw6 : b6 9 = base 9 := by simp [b1, b2, b3, b4, b5, b6]
  rw [hw6] at h6
  let b8 := Function.update b7 (16 : CoreTape) []
  have h7 := MachineDrain.drainTrace (16 : CoreTape) (labels (.cleanup 7))
    (some (labels (.cleanup 8))) program (code (.cleanup 7)) b7 (b7 16) ambient none
  rw [Function.update_eq_self] at h7
  have hw7 : b7 16 = base 16 := by simp [b1, b2, b3, b4, b5, b6, b7]
  rw [hw7] at h7
  let b9 := Function.update b8 (17 : CoreTape) []
  have h8 := MachineDrain.drainTrace (17 : CoreTape) (labels (.cleanup 8))
    (some (labels (.cleanup 9))) program (code (.cleanup 8)) b8 (b8 17) ambient none
  rw [Function.update_eq_self] at h8
  have hw8 : b8 17 = base 17 := by simp [b1, b2, b3, b4, b5, b6, b7, b8]
  rw [hw8] at h8
  let b10 := Function.update b9 (18 : CoreTape) []
  have h9 := MachineDrain.drainTrace (18 : CoreTape) (labels (.cleanup 9))
    exit program (code (.cleanup 9)) b9 (b9 18) ambient none
  rw [Function.update_eq_self] at h9
  have hw9 : b9 18 = base 18 := by simp [b1, b2, b3, b4, b5, b6, b7, b8, b9]
  rw [hw9] at h9
  have total := (joinTrace (joinTrace (joinTrace (joinTrace (joinTrace (joinTrace (joinTrace (joinTrace (joinTrace h0 h1) h2) h3) h4) h5) h6) h7) h8) h9)
  have hn : coreCleanupSteps base =
      (base 10).length + 1 + ((base 11).length + 1) + ((base 12).length + 1) +
      ((base 13).length + 1) + ((base 14).length + 1) + ((base 15).length + 1) +
      ((base 9).length + 1) + ((base 16).length + 1) + ((base 17).length + 1) +
      ((base 18).length + 1) := by unfold coreCleanupSteps; omega
  rw [hn]
  exact total

theorem coreCleaned_memory (graph : List Bool) (x v i k o m : Nat)
    (rotor output query scan flat localIndex returnPort selected : List Bool) :
    coreCleaned (coreMemory graph x v i k o m rotor output query scan flat
      localIndex returnPort selected) =
      coreMemory graph x v i k o m rotor output [] [] [] [] [] [] := by
  funext z
  fin_cases z <;> rfl

theorem coreCleanupSteps_memory (graph : List Bool) (x v i k o m : Nat)
    (rotor output scan : List Bool) (j r z : Nat) :
    coreCleanupSteps (coreMemory graph x v i k o m rotor output
      (encodeWord 0) scan (encodeWord 0) (encodeWord j) (encodeWord r) (encodeWord z)) =
      scan.length + j + r + z + 15 := by
  change (encodeWord 0).length + scan.length + (encodeWord 0).length +
    (encodeWord j).length + (encodeWord r).length + (encodeWord z).length +
    ([] : List Bool).length + ([] : List Bool).length + ([] : List Bool).length +
    ([] : List Bool).length + 10 = _
  simp only [encodeWord_length, List.length_nil]
  omega

theorem coreRotorFinalFrame {n q : Nat} (table : ExpanderTables.Table n q) (i : Fin n) (p : Fin q)
    (graph : List Bool) (x v k o m : Nat) (output : List Bool) :
    rotorFinalTapes table i p coreRotorTapes
      (coreMemory graph x v i.val k o m
        (encodeWords (ExpanderTableWords.rotationWords table)) output [] [] [] [] [] []) =
    coreMemory graph x v i.val k o m
      (encodeWords (ExpanderTableWords.rotationWords table)) output (encodeWord 0)
      (encodeWords ((ExpanderTableWords.rotationWords table).drop (q * i.val + p.val + 1)))
      (encodeWord 0) (encodeWord (ExpanderTables.lookup table (i, p)).1.val)
      (encodeWord (ExpanderTables.lookup table (i, p)).2.val) [] := by
  funext z
  fin_cases z <;>
    simp [rotorFinalTapes, coreRotorTapes, rotorLookupTapes, coreMemory,
      MachineFixedDivMod.unaryTapes, MachineFixedDivMod.tapes, MachineCopy.forkTapes,
      MachineAffineLookup.finalTapes, MachinePreservingLookup.finalTapes, MachineLookup.tapes]

theorem coreRotorTrace {n q : Nat} (positive : 0 < q) (table : ExpanderTables.Table n q)
    (i : Fin n) (p : Fin q) (labels : CoreLabel q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = coreInstruction q positive p labels exit l)
    (graph : List Bool) (x v k o m : Nat) (output : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[rotorSteps table i p]
      (some ⟨some (labels (coreEntry q)), coreInitialState q positive ambient,
        coreMemory graph x v i.val k o m
          (encodeWords (ExpanderTableWords.rotationWords table)) output [] [] [] [] [] []⟩) =
      some ⟨some (labels (.select (.inr (.compare .scan)))), coreInitialState q positive ambient,
        coreMemory graph x v i.val k o m
          (encodeWords (ExpanderTableWords.rotationWords table)) output (encodeWord 0)
          (encodeWords ((ExpanderTableWords.rotationWords table).drop (q * i.val + p.val + 1)))
          (encodeWord 0) (encodeWord (ExpanderTables.lookup table (i, p)).1.val)
          (encodeWord (ExpanderTables.lookup table (i, p)).2.val) []⟩ := by
  let e := coreRotorStateEquiv σ q
  let backwards := MachineStateEquiv.program e.symm program
  have atRotor (l : RotorLabel q) :
      backwards (labels (.rotor l)) = rotorInstruction q positive p coreRotorTapes
        (fun l => labels (.rotor l)) (some (labels (.select (.inr (.compare .scan))))) l := by
    change MachineStateEquiv.statement e.symm (program (labels (.rotor l))) = _
    rw [code]
    exact MachineStateEquiv.statement_symm_statement e _
  have run := rotorTrace positive table i p coreRotorTapes coreRotorTapes_injective
    (fun l => labels (.rotor l)) (some (labels (.select (.inr (.compare .scan)))))
    backwards atRotor
    (coreMemory graph x v i.val k o m
      (encodeWords (ExpanderTableWords.rotationWords table)) output [] [] [] [] [] [])
    rfl rfl rfl rfl rfl rfl
    ((ambient, MachineFixedBlockMap.emptyBuffer 4096), (false, MachineCloudSelect.Phase.checking)) none
  have h := MachineStateEquiv.trace e backwards _ _ _ run
  have backForward : MachineStateEquiv.program e backwards = program := by
    have hp := MachineStateEquiv.program_symm_program e.symm program
    simpa only [Equiv.symm_symm, backwards] using hp
  rw [backForward] at h
  change (advance (TM2.step program))^[rotorSteps table i p]
    (some ⟨some (labels (coreEntry q)), coreInitialState q positive ambient,
      coreMemory graph x v i.val k o m
        (encodeWords (ExpanderTableWords.rotationWords table)) output [] [] [] [] [] []⟩) =
    some ⟨some (labels (.select (.inr (.compare .scan)))), coreInitialState q positive ambient,
      rotorFinalTapes table i p coreRotorTapes
        (coreMemory graph x v i.val k o m
          (encodeWords (ExpanderTableWords.rotationWords table)) output [] [] [] [] [] [])⟩ at h
  rw [coreRotorFinalFrame] at h
  exact h

theorem coreSelectFrame (graph : List Bool) (x v i k o m j : Nat)
    (rotor output query scan flat returnPort selected : List Bool) :
    MachineCloudPadding.Placement.tapes coreSelectView
      (selectMemory graph j v k o m [] selected [] [] [] [])
      (coreMemory graph x v i k o m rotor output query scan flat (encodeWord j) returnPort []) =
      coreMemory graph x v i k o m rotor output query scan flat (encodeWord j) returnPort selected := by
  funext z
  fin_cases z <;> rfl

def coreInputTapes (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PreprocessingCloudIndex.PaddedCloud t padding v)
    (output : List Bool) : CoreTape → List Bool :=
  coreMemory (GraphTables.tableBits t)
    (PreprocessingRegularTables.vertexOrder t padding x.val).val v.val
    (PreprocessingCloudIndex.paddedCloudRank t padding v x).val
    (PreprocessingCloudIndex.cloudSize t v) (PreprocessingPaddingOffsets.offset padding v.val) t.darts
    (encodeWords (ExpanderTableWords.rotationWords (tables v))) output [] [] [] [] [] []

def coreSteps (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PreprocessingCloudIndex.PaddedCloud t padding v)
    (p : Fin q) (outputLength : Nat) : Nat :=
  let rank := PreprocessingCloudIndex.paddedCloudRank t padding v x
  let step := ExpanderTables.lookup (tables v) (rank, p)
  let selected := PreprocessingInternalRows.selectedIndex t padding v step.1
  let suffixBits := encodeWords ((ExpanderTableWords.rotationWords (tables v)).drop
    (q * rank.val + p.val + 1))
  rotorSteps (tables v) rank p + selectionSteps t padding v step.1 +
    finishSteps q (PreprocessingRegularTables.vertexOrder t padding x.val).val
      selected step.2.val outputLength +
    (suffixBits.length + step.1.val + step.2.val + selected + 15)

theorem coreSteps_le (q : Nat) (positive : 0 < q) (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PreprocessingCloudIndex.PaddedCloud t padding v)
    (p : Fin q) (outputLength : Nat) :
    coreSteps t padding tables v x p outputLength ≤
      coreTimeBound q (GraphTables.tableBits t).length
        (encodeWords (ExpanderTableWords.rotationWords (tables v))).length
        (PreprocessingRegularTables.vertexOrder t padding x.val).val v.val
        (PreprocessingCloudIndex.paddedCloudRank t padding v x).val
        (PreprocessingCloudIndex.cloudSize t v)
        (PreprocessingPaddingOffsets.offset padding v.val) t.darts outputLength := by
  let rank := PreprocessingCloudIndex.paddedCloudRank t padding v x
  let step := ExpanderTables.lookup (tables v) (rank, p)
  let z := PreprocessingInternalRows.selectedIndex t padding v step.1
  let X := (PreprocessingRegularTables.vertexOrder t padding x.val).val
  let o := PreprocessingPaddingOffsets.offset padding v.val
  let L := (GraphTables.tableBits t).length
  let R := (encodeWords (ExpanderTableWords.rotationWords (tables v))).length
  let k := PreprocessingCloudIndex.cloudSize t v
  let tailBits := encodeWords ((ExpanderTableWords.rotationWords (tables v)).drop
    (q * rank.val + p.val + 1))
  have hN : k + padding v ≤ R := rotorSize_le_encodedLength positive (tables v)
  have hj : step.1.val ≤ R := step.1.isLt.le.trans hN
  have hr : step.2.val ≤ q := step.2.isLt.le
  have hz : z ≤ t.darts + o + R := by
    have h := selectedIndex_le t padding v step.1
    change z ≤ t.darts + o + step.1.val at h
    omega
  have hsize : (k + padding v) * q ≤ R := by
    dsimp only [R, k]
    rw [encodeWords_length, ExpanderTableWords.rotationWords_length]
    omega
  have hrotor : rotorSteps (tables v) rank p ≤ 2 * rank.val + 6 * R + 8 := by
    have h := rotorSteps_le (tables v) rank p
    change rotorSteps (tables v) rank p ≤ 2 * rank.val + 5 * R + (k + padding v) * q + 8 at h
    omega
  have hselect : selectionSteps t padding v step.1 ≤
      10 * L + 16 * R + 13 * v.val + 5 * k + 2 * o + 2 * t.darts + 57 := by
    have h := selectionSteps_le t padding v step.1
    change selectionSteps t padding v step.1 ≤
      10 * L + 16 * step.1.val + 13 * v.val + 5 * k + 2 * o + 2 * t.darts + 57 at h
    omega
  have hfinish : finishSteps q X z step.2.val outputLength ≤
      (5 * q + 7) * (t.darts + o + R) + 7 * q + 4 * X + 2 * outputLength + 40986 := by
    have h := finishSteps_le q X z step.2.val outputLength
    have hm := Nat.mul_le_mul_left (5 * q + 7) hz
    omega
  have htail : tailBits.length ≤ R := encodedDrop_length_le
    (ExpanderTableWords.rotationWords (tables v)) (q * rank.val + p.val + 1)
  have hcleanup : tailBits.length + step.1.val + step.2.val + z + 15 ≤
      R + R + q + (t.darts + o + R) + 15 := by omega
  calc
    coreSteps t padding tables v x p outputLength
        ≤ (2 * rank.val + 6 * R + 8) +
          (10 * L + 16 * R + 13 * v.val + 5 * k + 2 * o + 2 * t.darts + 57) +
          ((5 * q + 7) * (t.darts + o + R) + 7 * q + 4 * X + 2 * outputLength + 40986) +
          (R + R + q + (t.darts + o + R) + 15) :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hrotor hselect) hfinish) hcleanup
    _ = _ := by
      change _ = coreTimeBound q L R X v.val rank.val k o t.darts outputLength
      unfold coreTimeBound
      ring

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularLift
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable

open Turing MachineComposition

/-! The outer construction uses independent finite registers for its existing
subprograms. This transport combines tape placement, an untouched register
frame, and a static register equivalence, without adding any machine steps. -/
namespace Lift

open MachineCloudPadding

variable {K K' Λ Λ' σ τ υ : Type}

variable [DecidableEq K] [DecidableEq K']

theorem step (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Λ → Λ') (exit : Option Λ') (registers : (σ × τ) ≃ υ)
    (ambient : τ) (extra : K' → List Bool)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (target : Λ' → TM2.Stmt (fun _ : K' => Bool) Λ' υ)
    (code : ∀ l, target (labels l) = statement tape labels exit registers (source l))
    (a b : TM2.Cfg (fun _ : K => Bool) Λ σ) (h : TM2.step source a = some b) :
    TM2.step target (configuration view labels exit registers ambient extra a) =
      some (configuration view labels exit registers ambient extra b) := by
  cases a with
  | mk label state sourceTapes =>
    cases label with
    | none => simp [TM2.step] at h
    | some label =>
      have hb : TM2.stepAux (source label) state sourceTapes = b := Option.some.inj h
      rw [← hb]
      change some (TM2.stepAux (target (labels label)) (registers (state, ambient))
        (Placement.tapes view sourceTapes extra)) = _
      rw [code, stepAux tape view left right]

theorem trace (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Λ → Λ') (exit : Option Λ') (registers : (σ × τ) ≃ υ)
    (ambient : τ) (extra : K' → List Bool)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (target : Λ' → TM2.Stmt (fun _ : K' => Bool) Λ' υ)
    (code : ∀ l, target (labels l) = statement tape labels exit registers (source l))
    (steps : Nat) (a b : TM2.Cfg (fun _ : K => Bool) Λ σ)
    (run : (advance (TM2.step source))^[steps] (some a) = some b) :
    (advance (TM2.step target))^[steps]
      (some (configuration view labels exit registers ambient extra a)) =
      some (configuration view labels exit registers ambient extra b) :=
  liftSuccessfulTrace _ _ _
    (step tape view left right labels exit registers ambient extra source target code) steps a b run

end Lift

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_PoweringMachineRow
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
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

theorem rowAccept_eq_true {t S q : Nat}
    (labelAt : Fin q → Fin S → GraphTables.Label)
    (bits : Buffer (inputSize t S)) (a b : Fin q) :
    rowAccept labelAt bits a b = true ↔ ∀ k, edgeAccept labelAt bits k a b = true := by
  simp [rowAccept, List.all_eq_true, List.mem_ofFn]

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRow

end

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

open Turing MachineComposition
open PCP PCP.GraphTables PCP.PreprocessingRegularTables

/-! ## The actual stored row and its input word boundaries -/

theorem selected_reverse (t : Table) (e : Fin t.darts) :
    (GraphTables.tableWords t)[4098 * e.val + 3]? = some t.rows[e].reverseIndex.val := by
  have h := congrArg (fun words : List Nat => words[1]?) (tableWords_drop_row t e)
  simp only [List.getElem?_drop] at h
  rw [show 2 + 4098 * e.val + 1 = 4098 * e.val + 3 by omega] at h
  simpa [rowWords] using h

theorem remaining_relation (t : Table) (e : Fin t.darts) :
    (GraphTables.tableWords t).drop (4098 * e.val + 3 + 1) =
      relationWords t.rows[e].relation ++ suffixWords t e := by
  rw [show 4098 * e.val + 3 + 1 = (2 + 4098 * e.val) + 2 by omega,
    ← List.drop_drop, tableWords_drop_row]
  simp only [rowWords, List.cons_append, List.drop_succ_cons, List.drop_zero, List.nil_append]

/-! ## One fixed finite program -/

def instruction {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt Alphabet Λ (State σ)
  | .lookup l => MachineAffineLookup.instruction 0 lookupTape 4098 3
      (fun l => labels (.lookup l)) (some (labels .copyRelation)) l
  | .copyRelation => relationCopyAt 3 7 (some (labels .reverseSeed))
  | .reverseSeed => MachineUnaryAffineAt.seed 6 q (labels .reverseScan)
  | .reverseScan => MachineUnaryAffineAt.scan 4 5 6 (q + 1)
      (labels .reverseScan) (labels .reverseRestore)
  | .reverseRestore => Reduction.MachineTransfer.loopAt 5 4 id false
      (labels .reverseRestore) (some (labels (.emit .relationRead)))
  | .emit l => MachineTableRows.routine fields 8 9 5 (fun l => labels (.emit l)) exit l

/-! ## Physical intermediate tape states -/

def looked (t : Table) (e : Fin t.darts) (base : Tape → List Bool) : Tape → List Bool :=
  MachineAffineLookup.finalTapes lookupTape base (GraphTables.tableWords t) (4098 * e.val + 3)
    t.rows[e].reverseIndex.val

def copied (t : Table) (e : Fin t.darts) (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (Function.update (looked t e base) 3
    (encodeWords (suffixWords t e) ++ base 3)) 7
    (encodeWords (relationWords t.rows[e].relation) ++ base 7)

def affined (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    Tape → List Bool :=
  Function.update (copied t e base) 6
    (encodeWord ((q + 1) * t.rows[e].reverseIndex.val + q) ++ base 6)

theorem looked_other (t : Table) (e : Fin t.darts) (base : Tape → List Bool)
    (k : Tape) (h₂ : k ≠ 2) (h₃ : k ≠ 3) (h₄ : k ≠ 4) :
    looked t e base k = base k :=
  MachineAffineLookup.finalTapes_other lookupTape base _ _ _ k h₂ h₃ h₄

theorem looked_reverse (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    looked t e base 4 = encodeWord t.rows[e].reverseIndex.val ++ base 4 :=
  MachineAffineLookup.finalTapes_output lookupTape base _ _ _

theorem looked_relation (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    looked t e base 3 = encodeWords (relationWords t.rows[e].relation) ++
      (encodeWords (suffixWords t e) ++ base 3) := by
  change MachineLookup.tapes (2 : Tape) 3 4 base
    (encodeWord 0 ++ base 2)
    (encodeWords ((GraphTables.tableWords t).drop (4098 * e.val + 3 + 1)) ++ base 3)
    (encodeWord t.rows[e].reverseIndex.val ++ base 4) 3 = _
  rw [MachineLookup.tapes_source _ _ _ (by decide), remaining_relation, encodeWords_append]
  exact List.append_assoc _ _ _

theorem copied_other (t : Table) (e : Fin t.darts) (base : Tape → List Bool)
    (k : Tape) (h₂ : k ≠ 2) (h₃ : k ≠ 3) (h₄ : k ≠ 4) (h₇ : k ≠ 7) :
    copied t e base k = base k := by
  simp only [copied, Function.update_of_ne h₇, Function.update_of_ne h₃,
    looked_other t e base k h₂ h₃ h₄]

theorem copied_reverse (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    copied t e base 4 = encodeWord t.rows[e].reverseIndex.val ++ base 4 := by
  simp only [copied, Function.update_of_ne (by decide : (4 : Tape) ≠ 7),
    Function.update_of_ne (by decide : (4 : Tape) ≠ 3), looked_reverse]

theorem copied_relation (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    copied t e base 7 = encodeWords (relationWords t.rows[e].relation) ++ base 7 := by
  simp only [copied, Function.update_self]

theorem affined_other (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool)
    (k : Tape) (h₂ : k ≠ 2) (h₃ : k ≠ 3) (h₄ : k ≠ 4) (h₆ : k ≠ 6) (h₇ : k ≠ 7) :
    affined q t e base k = base k := by
  simp only [affined, Function.update_of_ne h₆, copied_other t e base k h₂ h₃ h₄ h₇]

theorem affined_reverse (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    affined q t e base 6 = encodeWord ((q + 1) * t.rows[e].reverseIndex.val + q) ++ base 6 := by
  simp only [affined, Function.update_self]

theorem affined_relation (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    affined q t e base 7 = encodeWords (relationWords t.rows[e].relation) ++ base 7 := by
  simp only [affined, Function.update_of_ne (by decide : (7 : Tape) ≠ 6), copied_relation]

/-- The input graph and dart index occur only as physically stored tape data. -/
structure Input (t : Table) (e : Fin t.darts) (base : Tape → List Bool) : Prop where
  indexWord : base 0 = encodeWord e.val
  tableWord : base 1 = tableBits t
  reverseEmpty : base 4 = []
  scratchEmpty : base 5 = []
  computedEmpty : base 6 = []
  relationEmpty : base 7 = []
  rowEmpty : base 8 = []

def steps (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) : Nat :=
  MachineAffineLookup.steps (GraphTables.tableWords t) e.val 4098 3 + 1 +
    (2 * (t.rows[e].reverseIndex.val + 1) + 1) + rowSteps q t e base

def finalTapes (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    Tape → List Bool :=
  Function.update (affined q t e base) 9 (base 9 ++ encodeWords (emittedWords q t e))

section Execution

variable {Λ σ : Type}

theorem lookupTrace (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (t : Table) (e : Fin t.darts) (base : Tape → List Bool) (input : Input t e base)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[MachineAffineLookup.steps (GraphTables.tableWords t) e.val 4098 3]
      (some ⟨some (labels (.lookup .seed)), ((ambient, zeroBuffer), register), base⟩) =
      some ⟨some (labels .copyRelation), ((ambient, zeroBuffer), none), looked t e base⟩ := by
  exact MachineAffineLookup.affineLookupTrace 0 lookupTape lookupTape_injective source_outside
    4098 3 (fun l => labels (.lookup l)) (some (labels .copyRelation)) program
    (fun l => code (.lookup l)) base (GraphTables.tableWords t) input.tableWord input.scratchEmpty
    e.val [] (by simpa only [List.append_nil] using input.indexWord)
    t.rows[e].reverseIndex.val (selected_reverse t e) (ambient, zeroBuffer) register

theorem copyTrace (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (t : Table) (e : Fin t.darts) (base : Tape → List Bool) (ambient : σ) :
    (advance (TM2.step program))^[1]
      (some ⟨some (labels .copyRelation), ((ambient, zeroBuffer), none), looked t e base⟩) =
      some ⟨some (labels .reverseSeed), ((ambient, zeroBuffer), none), copied t e base⟩ := by
  simp only [Function.iterate_one, advance_some]
  have run := relationCopy_step (3 : Tape) 7 (by decide) (labels .copyRelation)
    (some (labels .reverseSeed)) program (code .copyRelation) t.rows[e].relation
    (encodeWords (suffixWords t e) ++ base 3) (looked t e base) (looked_relation t e base)
    ambient zeroBuffer none
  rw [looked_other t e base 7 (by decide) (by decide) (by decide)] at run
  exact run

theorem affineTrace (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (t : Table) (e : Fin t.darts) (base : Tape → List Bool) (input : Input t e base)
    (ambient : σ) :
    (advance (TM2.step program))^[2 * (t.rows[e].reverseIndex.val + 1) + 1]
      (some ⟨some (labels .reverseSeed), ((ambient, zeroBuffer), none), copied t e base⟩) =
      some ⟨some (labels (.emit .relationRead)), ((ambient, zeroBuffer), none),
        affined q t e base⟩ := by
  have hsource : copied t e base 4 = encodeWord t.rows[e].reverseIndex.val ++ [] := by
    rw [copied_reverse, input.reverseEmpty]
  have hscratch : copied t e base 5 = [] := by
    rw [copied_other t e base 5 (by decide) (by decide) (by decide) (by decide), input.scratchEmpty]
  have run := MachineUnaryAffineAt.seededAffineTrace (4 : Tape) 5 6 (by decide) (by decide)
    (by decide) (q + 1) q (labels .reverseSeed) (labels .reverseScan) (labels .reverseRestore)
    (some (labels (.emit .relationRead))) program (code .reverseSeed) (code .reverseScan)
    (code .reverseRestore) (copied t e base) t.rows[e].reverseIndex.val [] hsource hscratch
    (ambient, zeroBuffer) none
  rw [copied_other t e base 6 (by decide) (by decide) (by decide) (by decide)] at run
  exact run

end Execution

theorem steps_le (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    steps q t e base ≤ timeBound q (tableBits t).length (base 9).length := by
  have hl := MachineAffineLookup.steps_le (GraphTables.tableWords t) e.val 4098 3
    t.rows[e].reverseIndex.val (selected_reverse t e)
  have htable := tableWords_length_le_bits t
  have he : e.val ≤ (tableBits t).length := by have he := e.isLt; omega
  have hr : t.rows[e].reverseIndex.val ≤ (tableBits t).length := by
    have hrlt := t.rows[e].reverseIndex.isLt
    omega
  have hrel := relationBits_length_le t.rows[e].relation
  have hmul := Nat.mul_le_mul_left (4 * (q + 1) + 2) hr
  change MachineAffineLookup.steps (GraphTables.tableWords t) e.val 4098 3 ≤
    2 * e.val + 5 * (tableBits t).length + 6 at hl
  unfold steps rowSteps timeBound emittedWords
  simp only [encodeWords, List.length_append, encodeWord_length]
  nlinarith

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

open Turing MachineComposition
open UniqueGamesTheorem.Foundations.PCP

variable {σ : Type}

def cloudData (t : GraphTables.Table) (v : Fin t.vertices) (data : Data) : Data :=
  { data with
    count := encodeWord (PreprocessingCloudIndex.cloudSize t v)
    padding := encodeWord (MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t v))
    level := encodeWord (PreprocessingLevels.boundedLevel (PreprocessingCloudIndex.cloudSize t v)) }

def prefixData (t : GraphTables.Table) (v : Fin t.vertices) (data : Data) : Data :=
  { data with offset := encodeWord (PreprocessingPaddingOffsets.offset
      (PreprocessingRegularTables.padding t) v.val) }

def ownerData (t : GraphTables.Table) (e : Fin t.darts) (data : Data) : Data :=
  { data with owner := encodeWord t.rows[e].tail.val }

def ownerSteps (t : GraphTables.Table) (e : Fin t.darts) : Nat :=
  MachineAffineLookup.steps (GraphTables.tableWords t) e.val 4098 2 + 2 +
    ((ownerRemainder t e).length + 1)

def queryFrame (data : Data) (v x : Nat) : Tape → List Bool :=
  Function.update (Function.update (frame data) (.inl 9) (rankQuery v x))
    (.inl 3) (encodeWord 0)

def rankData (t : GraphTables.Table) (v : Fin t.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics t) v) (data : Data) : Data :=
  { data with localRank := encodeWord (PreprocessingCloudIndex.cloudRank t v e).val }

def originalData (t : GraphTables.Table) (e : Fin t.darts) (data : Data) : Data :=
  cloudData t t.rows[e].tail (prefixData t t.rows[e].tail
    (rankData t t.rows[e].tail (originalMember t e) (ownerData t e data)))

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularMetadata

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

open Turing MachineComposition PCP PCP.GraphTables PCP.PreprocessingRegularTables

def instruction {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt Alphabet Λ (State σ)
  | .row l => MachineRegularOriginalRow.instruction q (fun l => labels (.row l))
      (some (labels .query)) l
  | .query => MachineDrain.drain 2 (labels .query) (some (labels .scan))
  | .scan => MachineDrain.drain 3 (labels .scan) (some (labels .rawReverse))
  | .rawReverse => MachineDrain.drain 4 (labels .rawReverse) (some (labels .computedReverse))
  | .computedReverse => MachineDrain.drain 6 (labels .computedReverse) (some (labels .relation))
  | .relation => MachineDrain.drain 7 (labels .relation) exit

theorem cleanupTraceAt {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (base : Tape → List Bool) (state : State σ) :
    (advance (TM2.step program))^[cleanupSteps base]
      (some ⟨some (labels .query), state, base⟩) =
      some ⟨exit, (state.1, none), cleanupTapes base⟩ := by
  let t1 := Function.update base (2 : Tape) []
  let t2 := Function.update t1 (3 : Tape) []
  let t3 := Function.update t2 (4 : Tape) []
  let t4 := Function.update t3 (6 : Tape) []
  have h0 := MachineDrain.drainTrace (2 : Tape) (labels .query) (some (labels .scan))
    program (code .query) base (base 2) state.1 state.2
  have h1 := MachineDrain.drainTrace (3 : Tape) (labels .scan) (some (labels .rawReverse))
    program (code .scan) t1 (t1 3) state.1 none
  have h2 := MachineDrain.drainTrace (4 : Tape) (labels .rawReverse) (some (labels .computedReverse))
    program (code .rawReverse) t2 (t2 4) state.1 none
  have h3 := MachineDrain.drainTrace (6 : Tape) (labels .computedReverse) (some (labels .relation))
    program (code .computedReverse) t3 (t3 6) state.1 none
  have h4 := MachineDrain.drainTrace (7 : Tape) (labels .relation) exit
    program (code .relation) t4 (t4 7) state.1 none
  simp only [Function.update_eq_self] at h0 h1 h2 h3 h4
  simp only [t1, t2, t3, t4, Function.update_of_ne (by decide : (3 : Tape) ≠ 2),
    Function.update_of_ne (by decide : (4 : Tape) ≠ 3),
    Function.update_of_ne (by decide : (4 : Tape) ≠ 2),
    Function.update_of_ne (by decide : (6 : Tape) ≠ 4),
    Function.update_of_ne (by decide : (6 : Tape) ≠ 3),
    Function.update_of_ne (by decide : (6 : Tape) ≠ 2),
    Function.update_of_ne (by decide : (7 : Tape) ≠ 6),
    Function.update_of_ne (by decide : (7 : Tape) ≠ 4),
    Function.update_of_ne (by decide : (7 : Tape) ≠ 3),
    Function.update_of_ne (by decide : (7 : Tape) ≠ 2)] at h1 h2 h3 h4
  exact join_trace (join_trace (join_trace (join_trace h0 h1) h2) h3) h4

structure Input (t : Table) (e : Fin t.darts) (base : Tape → List Bool) : Prop
    extends MachineRegularOriginalRow.Input t e base where
  queryEmpty : base 2 = []
  scanEmpty : base 3 = []

theorem cleanup_frame (q : Nat) (t : Table) (e : Fin t.darts)
    (base : Tape → List Bool) (input : Input t e base) :
    cleanupTapes (MachineRegularOriginalRow.finalTapes q t e base) =
      Function.update base 9
        (base 9 ++ encodeWords (MachineRegularOriginalRow.emittedWords q t e)) := by
  funext k
  fin_cases k <;>
    simp [cleanupTapes, MachineRegularOriginalRow.finalTapes,
      MachineRegularOriginalRow.affined, MachineRegularOriginalRow.copied,
      MachineRegularOriginalRow.looked, MachineAffineLookup.finalTapes,
      MachinePreservingLookup.finalTapes, MachineLookup.tapes,
      MachineRegularOriginalRow.lookupTape, input.queryEmpty, input.scanEmpty,
      input.reverseEmpty, input.computedEmpty, input.relationEmpty]

theorem suffix_length_le (t : Table) (e : Fin t.darts) :
    (encodeWords (MachineRegularOriginalRow.suffixWords t e)).length ≤ (tableBits t).length := by
  have hlength : (tableBits t).length =
      (encodeWords (MachineRegularOriginalRow.prefixWords t e)).length +
        ((encodeWords (rowWords t.rows[e])).length +
          (encodeWords (MachineRegularOriginalRow.suffixWords t e)).length) := by
    rw [tableBits, MachineRegularOriginalRow.tableWords_at_row,
      encodeWords_append, encodeWords_append, List.length_append, List.length_append]
  omega

theorem cleanupSteps_eq (q : Nat) (t : Table) (e : Fin t.darts)
    (base : Tape → List Bool) (input : Input t e base) :
    cleanupSteps (MachineRegularOriginalRow.finalTapes q t e base) =
      (encodeWords (MachineRegularOriginalRow.suffixWords t e)).length +
        (q + 2) * t.rows[e].reverseIndex.val + q +
          (encodeWords (relationWords t.rows[e].relation)).length + 8 := by
  have hquery : MachineRegularOriginalRow.finalTapes q t e base 2 = encodeWord 0 := by
    simp only [MachineRegularOriginalRow.finalTapes,
      Function.update_of_ne (by decide : (2 : Tape) ≠ 9), MachineRegularOriginalRow.affined,
      Function.update_of_ne (by decide : (2 : Tape) ≠ 6), MachineRegularOriginalRow.copied,
      Function.update_of_ne (by decide : (2 : Tape) ≠ 7),
      Function.update_of_ne (by decide : (2 : Tape) ≠ 3)]
    change MachineLookup.tapes (2 : Tape) 3 4 base
      (encodeWord 0 ++ base 2)
      (encodeWords ((GraphTables.tableWords t).drop (4098 * e.val + 3 + 1)) ++ base 3)
      (encodeWord t.rows[e].reverseIndex.val ++ base 4) 2 = _
    rw [MachineLookup.tapes_index _ _ _ (by decide) (by decide), input.queryEmpty,
      List.append_nil]
  have hscan : MachineRegularOriginalRow.finalTapes q t e base 3 =
      encodeWords (MachineRegularOriginalRow.suffixWords t e) := by
    simp only [MachineRegularOriginalRow.finalTapes,
      Function.update_of_ne (by decide : (3 : Tape) ≠ 9), MachineRegularOriginalRow.affined,
      Function.update_of_ne (by decide : (3 : Tape) ≠ 6), MachineRegularOriginalRow.copied,
      Function.update_of_ne (by decide : (3 : Tape) ≠ 7), Function.update_self,
      input.scanEmpty, List.append_nil]
  have hraw : MachineRegularOriginalRow.finalTapes q t e base 4 =
      encodeWord t.rows[e].reverseIndex.val := by
    simp only [MachineRegularOriginalRow.finalTapes,
      Function.update_of_ne (by decide : (4 : Tape) ≠ 9), MachineRegularOriginalRow.affined,
      Function.update_of_ne (by decide : (4 : Tape) ≠ 6), MachineRegularOriginalRow.copied_reverse,
      input.reverseEmpty, List.append_nil]
  have hcomputed : MachineRegularOriginalRow.finalTapes q t e base 6 =
      encodeWord ((q + 1) * t.rows[e].reverseIndex.val + q) := by
    simp only [MachineRegularOriginalRow.finalTapes,
      Function.update_of_ne (by decide : (6 : Tape) ≠ 9), MachineRegularOriginalRow.affined_reverse,
      input.computedEmpty, List.append_nil]
  have hrelation : MachineRegularOriginalRow.finalTapes q t e base 7 =
      encodeWords (relationWords t.rows[e].relation) := by
    simp only [MachineRegularOriginalRow.finalTapes,
      Function.update_of_ne (by decide : (7 : Tape) ≠ 9), MachineRegularOriginalRow.affined_relation,
      input.relationEmpty, List.append_nil]
  simp only [cleanupSteps, hquery, hscan, hraw, hcomputed, hrelation, encodeWord_length]
  ring

theorem cleanupSteps_le (q : Nat) (t : Table) (e : Fin t.darts)
    (base : Tape → List Bool) (input : Input t e base) :
    cleanupSteps (MachineRegularOriginalRow.finalTapes q t e base) ≤
      (q + 3) * (tableBits t).length + q + 8200 := by
  rw [cleanupSteps_eq q t e base input]
  have hsuffix := suffix_length_le t e
  have htable := tableWords_length_le_bits t
  have hr : t.rows[e].reverseIndex.val ≤ (tableBits t).length := by
    have hrlt := t.rows[e].reverseIndex.isLt
    omega
  have hmul := Nat.mul_le_mul_left (q + 2) hr
  have hrel := relationBits_length_le t.rows[e].relation
  nlinarith

def steps (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) : Nat :=
  MachineRegularOriginalRow.steps q t e base +
    cleanupSteps (MachineRegularOriginalRow.finalTapes q t e base)

theorem steps_le (q : Nat) (t : Table) (e : Fin t.darts)
    (base : Tape → List Bool) (input : Input t e base) :
    steps q t e base ≤ timeBound q (tableBits t).length (base 9).length := by
  have hrow := MachineRegularOriginalRow.steps_le q t e base
  have hclean := cleanupSteps_le q t e base input
  unfold steps timeBound MachineRegularOriginalRow.timeBound at *
  nlinarith

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalClean

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_CleanupLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
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

omit [DecidableEq K] in
@[simp] theorem instruction_finish {n : Nat} (selected : Fin n → K)
    (labels : Fin (n + 1) → Λ) (initial : σ) (exit : Option Λ) :
    instruction selected labels initial exit (Fin.last n) = finish initial exit := by
  simp [instruction]

/-- The trace is derived solely from the actual drain instructions and final
reset instruction. No execution of the entire cleanup is assumed. -/
theorem cleanupTrace {n : Nat} (selected : Fin n → K) (labels : Fin (n + 1) → Λ)
    (initial : σ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atDrain : ∀ i : Fin n, program (labels i.castSucc) =
      MachineDrain.drain (selected i) (labels i.castSucc) (some (labels i.succ)))
    (atFinish : program (labels (Fin.last n)) = finish initial exit)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[actualCost selected base]
      (some ⟨some (labels 0), (ambient, register), base⟩) =
      some ⟨exit, (initial, none), clearTapes selected base⟩ := by
  induction n generalizing base ambient register with
  | zero =>
      change some (TM2.stepAux (program (labels 0)) (ambient, register) base) = _
      rw [show program (labels 0) = finish initial exit from atFinish]
      cases exit <;> rfl
  | succ n ih =>
      rw [actualCost, Function.iterate_add_apply]
      have first := MachineDrain.drainTrace (selected 0) (labels (0 : Fin (n + 1)).castSucc)
        (some (labels (0 : Fin (n + 1)).succ)) program (atDrain 0)
        base (base (selected 0)) ambient register
      simp only [Function.update_eq_self, Fin.castSucc_zero] at first
      rw [first]
      exact ih (fun i : Fin n => selected i.succ) (fun i => labels i.succ)
        (fun i => atDrain i.succ) atFinish (Function.update base (selected 0) []) ambient none

/-- Actual cleanup execution, bounded using the original selected-stack lengths. -/
def cleanupInTime {n : Nat} (selected : Fin n → K) (labels : Fin (n + 1) → Λ)
    (initial : σ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atDrain : ∀ i : Fin n, program (labels i.castSucc) =
      MachineDrain.drain (selected i) (labels i.castSucc) (some (labels i.succ)))
    (atFinish : program (labels (Fin.last n)) = finish initial exit)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels 0), (ambient, register), base⟩
      (some ⟨exit, (initial, none), clearTapes selected base⟩)
      ((∑ i, (base (selected i)).length) + n + 1) where
  steps := actualCost selected base
  evals_in_steps := cleanupTrace selected labels initial exit program atDrain atFinish
    base ambient register
  steps_le_m := actualCost_le selected base

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Cleanup

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Lookup

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K]

def readRowTapes {q n m : Nat} (source tail reverse : K) (base : K → List Bool)
    (row : DartRow q n m) (suffix : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base source suffix)
    tail (encodeWord row.tail.val)) reverse (encodeWord row.reverseIndex.val)

def readRowCost {q n m : Nat} (row : DartRow q n m) : Nat :=
  row.tail.val + row.reverseIndex.val + 5

theorem readRowCost_table_le {q : Nat} (table : Table q) (e : Fin table.darts) :
    readRowCost table.rows[e] ≤ 2 * (tableBits table).length + 5 := by
  have ht := (Nat.le_of_lt table.rows[e].tail.isLt).trans
    (vertices_le_tableBits_length table)
  have hr := (Nat.le_of_lt table.rows[e].reverseIndex.isLt).trans
    (darts_le_tableBits_length table)
  unfold readRowCost
  omega

/-- Read both unary fields using actual copy loops, then execute the checked
fixed predicate parser. Only the two field destinations must initially be
empty; the cursor suffix and every unrelated tape are retained exactly. -/
def readRowInTime {q n m : Nat} (source tail reverse : K)
    (hst : source ≠ tail) (hsr : source ≠ reverse) (htr : tail ≠ reverse)
    (tailStart tailLoop reverseStart reverseLoop readLabel exitLabel : Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (ReadRelation.State σ q))
    (atTailStart : P tailStart = Hastad.SourceMachine.fieldStart tail tailLoop)
    (atTailLoop : P tailLoop =
      Hastad.SourceMachine.fieldLoop source tail tailLoop (some reverseStart))
    (atReverseStart : P reverseStart = Hastad.SourceMachine.fieldStart reverse reverseLoop)
    (atReverseLoop : P reverseLoop =
      Hastad.SourceMachine.fieldLoop source reverse reverseLoop (some readLabel))
    (atRead : P readLabel = ReadRelation.parser source exitLabel)
    (base : K → List Bool) (row : DartRow q n m) (suffix : List Bool)
    (hinput : base source = rowBits row ++ suffix)
    (hTail : base tail = []) (hReverse : base reverse = [])
    (ambient : σ) (initial : RelationTable q) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some tailStart, ((ambient, initial), register), base⟩
      (some ⟨some exitLabel, ((ambient, row.relation), none),
        readRowTapes source tail reverse base row suffix⟩)
      (readRowCost row) := by
  let relationInput := encodeWords (relationWords row.relation) ++ suffix
  let reverseInput := encodeWord row.reverseIndex.val ++ relationInput
  let t₁ := Hastad.SourceMachine.fieldTapes source tail base reverseInput
    (encodeWord row.tail.val)
  let t₂ := Hastad.SourceMachine.fieldTapes source reverse t₁ relationInput
    (encodeWord row.reverseIndex.val)
  have hinput₁ : base source = encodeWord row.tail.val ++ reverseInput := by
    simpa only [rowBits_eq, List.append_assoc, reverseInput, relationInput] using hinput
  have run₁ : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some tailStart, ((ambient, initial), register), base⟩
      (some ⟨some reverseStart, ((ambient, initial), none), t₁⟩)
      (row.tail.val + 2) := by
    simpa only [hTail, List.append_nil, t₁] using
      Hastad.SourceMachine.fieldInTime source tail hst tailStart tailLoop
        (some reverseStart) P atTailStart atTailLoop base row.tail.val reverseInput
        hinput₁ (ambient, initial) register
  have hinput₂ : t₁ source = encodeWord row.reverseIndex.val ++ relationInput := by
    simp only [t₁, Hastad.SourceMachine.fieldTapes_source source tail hst, reverseInput]
  have hreverse₁ : t₁ reverse = [] := by
    simp [t₁, Hastad.SourceMachine.fieldTapes, Ne.symm hsr, Ne.symm htr, hReverse]
  have run₂ : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some reverseStart, ((ambient, initial), none), t₁⟩
      (some ⟨some readLabel, ((ambient, initial), none), t₂⟩)
      (row.reverseIndex.val + 2) := by
    simpa only [hreverse₁, List.append_nil, t₂] using
      Hastad.SourceMachine.fieldInTime source reverse hsr reverseStart reverseLoop
        (some readLabel) P atReverseStart atReverseLoop t₁ row.reverseIndex.val relationInput
        hinput₂ (ambient, initial) none
  have hinput₃ : t₂ source = encodeWords (relationWords row.relation) ++ suffix := by
    simp only [t₂, Hastad.SourceMachine.fieldTapes_source source reverse hsr, relationInput]
  have hrestore : Function.update t₂ source
      (encodeWords (relationWords row.relation) ++ suffix) = t₂ := by
    rw [← hinput₃]
    exact Function.update_eq_self source t₂
  have hfinal : Function.update t₂ source suffix =
      readRowTapes source tail reverse base row suffix := by
    funext k
    by_cases hs : k = source
    · subst k
      simp [readRowTapes, hst, hsr]
    · by_cases ht : k = tail
      · subst k
        simp [t₂, t₁, Hastad.SourceMachine.fieldTapes, readRowTapes, hs, htr]
      · by_cases hr : k = reverse
        · subst k
          simp [t₂, Hastad.SourceMachine.fieldTapes, readRowTapes, hs]
        · simp [t₂, t₁, Hastad.SourceMachine.fieldTapes, readRowTapes, hs, ht, hr]
  have run₃ : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some readLabel, ((ambient, initial), none), t₂⟩
      (some ⟨some exitLabel, ((ambient, row.relation), none),
        readRowTapes source tail reverse base row suffix⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change (advance (TM2.step P))^[1] _ = _
      simpa only [hrestore, hfinal] using ReadRelation.parserTrace source readLabel exitLabel
        P atRead t₂ row.relation suffix ambient initial none
    steps_le_m := Nat.le_refl _ }
  let run₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ run₂
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁₂ run₃
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have ht := run.steps_le_m
  unfold readRowCost
  omega

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Lookup

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

theorem bitCommands_bits (bits : List (σ → Bool)) (values : Fin h → Nat) (ambient : σ) :
    (bitCommands (h := h) (bound := bound) bits).flatMap (commandBits values ambient) =
      encodeWords (bits.map (fun bit => if bit ambient then 1 else 0)) := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    simpa only [bitCommands, List.map_cons, List.flatMap_cons, commandBits, encodeWords]
      using congrArg (encodeWord (if bit ambient then 1 else 0) ++ ·) ih

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Emitter

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PoweringTablesLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineField.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineField.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
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

/-- The finite first-address predicate evaluator used for each stored row. -/
def rowAccepts {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n)
    (a b : Fin (labelCount d n)) : Bool :=
  let rows := PoweringOpinionTables.walkRows (PortTables.portGraph input) n e.2
  let left := PoweringOpinionTables.labelTable (decodeLabel d (n + 1) 64 a)
  let right := PoweringOpinionTables.labelTable (decodeLabel d (n + 1) 64 b)
  if e.1 then PoweringOpinionTables.rowsAccepts (PortTables.accepts input) rows right left
    else PoweringOpinionTables.rowsAccepts (PortTables.accepts input) rows left right

theorem rowAccepts_eq {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n)
    (a b : Fin (labelCount d n)) :
    rowAccepts input n e a b = (mathematicalGraph input n).accepts e
      (decodeLabel d (n + 1) 64 a) (decodeLabel d (n + 1) 64 b) := by
  rcases e with ⟨direction, w⟩
  cases direction <;>
    simp only [rowAccepts, mathematicalGraph, PoweringTest.poweredGraph, Bool.false_eq_true,
      ite_false, ite_true, if_true, PoweringOpinionTables.rowsAccepts_walkRows]

/-- Complete decoded semantics, with executable vertex, dart and label orders. -/
theorem semantics_table {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) :
    GenericGraphTables.semantics (table input n) =
      GenericGraphTables.enumeratedGraph (mathematicalGraph input n) (Equiv.refl _)
        (dartEquiv vertices d n) (paddedLabelEquiv d (n + 1) 64) :=
  GenericGraphTables.semantics_ofGraph _

/-- Each actual output relation entry is the bounded stored-opinion evaluator. -/
theorem table_accepts {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (i : Fin (dartCount vertices d n)) (a b : Fin (labelCount d n)) :
    GenericGraphTables.acceptsAt (table input n).rows i a b =
      rowAccepts input n (decodeDart vertices d n i) a b := by
  change (GenericGraphTables.semantics (table input n)).accepts i a b = _
  rw [semantics_table]
  exact (rowAccepts_eq input n (decodeDart vertices d n i) a b).symm

/-- The reverse row flips just the orientation in the recorded-walk encoding. -/
theorem table_reverse {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (direction : Bool) (w : Walk (Fin vertices) (Fin d) (n + 1)) :
    GenericGraphTables.reverseAt (table input n).rows (encodeDart vertices d n (direction, w)) =
      encodeDart vertices d n (!direction, w) := by
  change (GenericGraphTables.semantics (table input n)).reverse _ = _
  rw [semantics_table]
  change dartEquiv vertices d n ((mathematicalGraph input n).reverse
      ((dartEquiv vertices d n).symm (dartEquiv vertices d n (direction, w)))) =
    dartEquiv vertices d n (!direction, w)
  rw [(dartEquiv vertices d n).symm_apply_apply]
  rfl

/-- Serialized output in the shared generic graph codec. -/
def outputBits {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) : List Bool :=
  GenericGraphTables.tableBits (table input n)

/-- The actual function on variable-size regular input tables. -/
def transform (d n : Nat) (input : PortTables.Input d) : GenericGraphTables.Table (labelCount d n) :=
  table input.2 n

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

/-- The row machine scans the same increasing address-index order. -/
theorem firstMatch_of_first {S : Nat} (mask : Fin S → Bool) (i : Fin S)
    (hi : mask i = true) (hfirst : ∀ j : Fin S, j.val < i.val → mask j = false) :
    firstMatch mask = some i := by
  unfold firstMatch
  apply List.find?_ofFn_eq_some.mpr
  refine ⟨hi, i, rfl, ?_⟩
  intro j hj
  change ¬mask j = true
  simp [hfirst j hj]

theorem firstMatch_firstIndex {X : Type*} (p : X → Prop) [DecidablePred p]
    (xs : List X) (h : ∃ a ∈ xs, p a) :
    firstMatch (fun i : Fin xs.length => decide (p (xs.get i))) =
      some (firstIndex p xs h) := by
  apply firstMatch_of_first
  · exact decide_eq_true (firstIndex_matches p xs h)
  · intro j hj
    exact decide_eq_false (firstIndex_is_first p xs h j hj)

theorem firstMatch_endpointMask (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) :
    firstMatch (endpointMask G t center u.val) = some (addressIndex G t center u) := by
  unfold endpointMask addressIndex
  exact firstMatch_firstIndex
    (fun w : PortWords (Fin d) t => (wordToBall G t center w).val = u.val)
    (allAddresses d t) (by
      obtain ⟨w, hw⟩ := wordToBall_surjective G t center u
      exact ⟨w, mem_allAddresses d t w, congrArg Subtype.val hw⟩)

/-- This lookup is fixed by the reduction parameters, not the input graph. -/
def fixedLabelAt (d n : Nat) (a : Fin (PoweringTables.labelCount d n))
    (i : Fin (slotCount d n)) : GraphTables.Label :=
  decodeLabel d (n + 1) 64 a ((allAddresses d (n + 1)).get i)

theorem fixedLabelAt_addressIndex (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (center : Fin vertices) (u : Ball G (n + 1) center)
    (a : Fin (PoweringTables.labelCount d n)) :
    fixedLabelAt d n a (addressIndex G (n + 1) center u) =
      decode (finitePortSelector G (n + 1) center) (decodeLabel d (n + 1) 64 a) u := by
  simpa only [fixedLabelAt, labelTable_get] using
    labelTable_addressIndex G (n + 1) center u (decodeLabel d (n + 1) 64 a)

theorem firstMatch_walkBits_left (input : PortTables.Table vertices d) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1)) :
    firstMatch (leftMatches (walkBits input n w) k) = some
      (addressIndex (PortTables.portGraph input) (n + 1) w.1
        (tailFromStart (PortTables.portGraph input) n w k)) := by
  rw [leftMatches_walkBits]
  simpa only [tailFromStart_val, slotCount] using
    firstMatch_endpointMask (PortTables.portGraph input) (n + 1) w.1
      (tailFromStart (PortTables.portGraph input) n w k)

theorem firstMatch_walkBits_right (input : PortTables.Table vertices d) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1)) :
    firstMatch (rightMatches (walkBits input n w) k) = some
      (addressIndex (PortTables.portGraph input) (n + 1)
        (endpoint (PortTables.portGraph input) w)
        (headFromEnd (PortTables.portGraph input) n w k)) := by
  rw [rightMatches_walkBits]
  simpa only [headFromEnd_val, slotCount] using
    firstMatch_endpointMask (PortTables.portGraph input) (n + 1)
      (endpoint (PortTables.portGraph input) w) (headFromEnd (PortTables.portGraph input) n w k)

theorem edgeAccept_walkBits (input : PortTables.Table vertices d) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1))
    (a b : Fin (PoweringTables.labelCount d n)) :
    edgeAccept (fixedLabelAt d n) (walkBits input n w) k a b =
      PortTables.accepts input (edgeAt (PortTables.portGraph input) n w k)
        (decode (finitePortSelector (PortTables.portGraph input) (n + 1) w.1)
          (decodeLabel d (n + 1) 64 a) (tailFromStart (PortTables.portGraph input) n w k))
        (decode (finitePortSelector (PortTables.portGraph input) (n + 1)
          (endpoint (PortTables.portGraph input) w))
          (decodeLabel d (n + 1) 64 b) (headFromEnd (PortTables.portGraph input) n w k)) := by
  simp only [edgeAccept, firstMatch_walkBits_left, firstMatch_walkBits_right,
    basePredicate_walkBits, fixedLabelAt_addressIndex]

theorem rowAccept_walkBits (input : PortTables.Table vertices d) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1))
    (a b : Fin (PoweringTables.labelCount d n)) :
    rowAccept (fixedLabelAt d n) (walkBits input n w) a b =
      rowsAccepts (PortTables.accepts input) (walkRows (PortTables.portGraph input) n w)
        (labelTable (decodeLabel d (n + 1) 64 a))
        (labelTable (decodeLabel d (n + 1) 64 b)) := by
  rw [rowsAccepts_walkRows]
  apply Bool.eq_iff_iff.mpr
  simp only [rowAccept_eq_true, PoweringTest.pathAccepts_eq_true_iff, edgeAccept_walkBits]

theorem edgeAccept_transposeBits {t S q : Nat}
    (labelAt : Fin q → Fin S → GraphTables.Label)
    (bits : Buffer (inputSize t S)) (k : Fin t) (a b : Fin q) :
    edgeAccept labelAt (transposeBits bits) k a b = edgeAccept labelAt bits k b a := by
  simp only [edgeAccept, leftMatches_transposeBits, rightMatches_transposeBits]
  cases hl : firstMatch (leftMatches bits k) <;>
    cases hr : firstMatch (rightMatches bits k) <;>
    simp

theorem rowAccept_transposeBits {t S q : Nat}
    (labelAt : Fin q → Fin S → GraphTables.Label)
    (bits : Buffer (inputSize t S)) (a b : Fin q) :
    rowAccept labelAt (transposeBits bits) a b = rowAccept labelAt bits b a := by
  apply Bool.eq_iff_iff.mpr
  simp only [rowAccept_eq_true, edgeAccept_transposeBits]

/-- No match-mask or base-relation premise remains in the evaluator bridge. -/
theorem rowAccept_rowBits (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n)
    (a b : Fin (PoweringTables.labelCount d n)) :
    rowAccept (fixedLabelAt d n) (rowBits input n e) a b =
      PoweringTables.rowAccepts input n e a b := by
  rcases e with ⟨direction, w⟩
  cases direction <;>
    simp only [rowBits, Bool.false_eq_true, ite_false, ite_true, if_true,
      rowAccept_transposeBits, rowAccept_walkBits, PoweringTables.rowAccepts]

def dataWords (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) : List Nat :=
  (List.ofFn (rowBits input n e)).map GraphTables.bitWord

def dataTape (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) : List Bool :=
  encodeWords (dataWords input n e)

theorem dataTape_eq (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) :
    dataTape input n e = encodeBits (List.ofFn (rowBits input n e)) :=
  (encodeBits_graphWords _).symm

def emittedRelation (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) :
    GenericGraphTables.RelationTable (PoweringTables.labelCount d n) :=
  Vector.ofFn (rowBlock (fixedLabelAt d n) (rowBits input n e))

theorem rowBlock_unary (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) :
    encodeBits (List.ofFn (rowBlock (fixedLabelAt d n) (rowBits input n e))) =
      encodeWords (GenericGraphTables.relationWords (emittedRelation input n e)) := by
  have hbit : GraphTables.bitWord = GenericGraphTables.bitWord := by
    funext b
    cases b <;> rfl
  have h := encodeBits_graphWords
    (List.ofFn (rowBlock (fixedLabelAt d n) (rowBits input n e)))
  rw [hbit] at h
  simpa only [emittedRelation, GenericGraphTables.relationWords, Vector.toList_ofFn] using h

/-- The emitted bits are the relation of the actual numbered output row. -/
theorem emittedRelation_table (input : PortTables.Table vertices d) (n : Nat)
    (i : Fin (PoweringTables.dartCount vertices d n)) :
    emittedRelation input n (decodeDart vertices d n i) =
      (PoweringTables.table input n).rows[i].relation := by
  apply Vector.ext
  intro j hj
  have h := PoweringTables.table_accepts input n i
    ((GenericGraphTables.relationIndex (PoweringTables.labelCount d n)).symm ⟨j, hj⟩).1
    ((GenericGraphTables.relationIndex (PoweringTables.labelCount d n)).symm ⟨j, hj⟩).2
  have hindex : GenericGraphTables.relationIndex (PoweringTables.labelCount d n)
      (((GenericGraphTables.relationIndex (PoweringTables.labelCount d n)).symm ⟨j, hj⟩).1,
        ((GenericGraphTables.relationIndex (PoweringTables.labelCount d n)).symm ⟨j, hj⟩).2) =
        ⟨j, hj⟩ := by
    change GenericGraphTables.relationIndex (PoweringTables.labelCount d n)
      ((GenericGraphTables.relationIndex (PoweringTables.labelCount d n)).symm ⟨j, hj⟩) = _
    exact Equiv.apply_symm_apply _ _
  simp only [GenericGraphTables.acceptsAt, GenericGraphTables.relationAt, hindex,
    Fin.getElem_fin] at h
  simp only [emittedRelation, Vector.getElem_ofFn]
  change rowBlock (fixedLabelAt d n) (rowBits input n (decodeDart vertices d n i)) ⟨j, hj⟩ =
    (PoweringTables.table input n).rows[i].relation[j]
  change rowAccept (fixedLabelAt d n) (rowBits input n (decodeDart vertices d n i))
    ((GenericGraphTables.relationIndex (PoweringTables.labelCount d n)).symm ⟨j, hj⟩).1
    ((GenericGraphTables.relationIndex (PoweringTables.labelCount d n)).symm ⟨j, hj⟩).2 = _
  rw [rowAccept_rowBits]
  exact h.symm

end UniqueGamesTheorem.Foundations.PCP.PoweringRowData

/-! A fixed powered-row data block is reduced to two concrete instruction
forms: follow a fixed port word and read one stored predicate entry, or follow
two fixed words and compare their endpoint identifiers. The plan depends only
on the fixed degree, radius, word and orientation. Its interpretation is exactly
the data block consumed by the checked row transducer. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringFieldPlan

open PoweringWalks PoweringLabels PoweringAddresses PoweringReach PoweringRowData
open UniqueGamesTheorem.Foundations.Complexity PoweringMachineRow

variable {V D : Type*}

theorem walkEnd_tailPorts (G : PortGraph V D) :
    ∀ (n : Nat) (v : V) (p : Fin (n + 1) → D) (k : Fin (n + 1)),
      walkEnd G v (tailPorts n p k) = (edgeAt G n (v, p) k).1 := by
  intro n
  induction n with
  | zero => intro v p k; rfl
  | succ n ih =>
      intro v p k
      refine Fin.cases rfl (fun j => ?_) k
      exact ih (next G v (p 0)) (fun i => p i.succ) j

theorem walkEnd_headPorts (G : PortGraph V D) (n : Nat) (v : V)
    (p : Fin (n + 1) → D) (k : Fin (n + 1)) :
    walkEnd G v (headPorts n p k) = (G.rot (edgeAt G n (v, p) k)).1 := by
  rw [headPorts, walkEnd_append, walkEnd_tailPorts]
  change (G.rot ((edgeAt G n (v, p) k).1, p k)).1 = _
  have hp : (edgeAt G n (v, p) k).2 = p k := edgeAt_port G n (v, p) k
  rw [← hp]

theorem walkEnd_addressPorts {d t : Nat} (G : PortGraph V (Fin d)) (v : V)
    (i : PoweringOpinionTables.AddressIndex d t) :
    walkEnd G v (addressPorts i) = (wordToBall G t v ((allAddresses d t).get i)).val :=
  (wordEnd_eq_walkEnd_ofFn G _ _ _).symm

def evaluate {vertices d : Nat} (input : PortTables.Table vertices d)
    (start : Fin vertices) : Instruction d → Bool
  | .relation ports port a b => PortTables.accepts input
      (walkEnd (PortTables.portGraph input) start ports, port) a b
  | .equal left right => decide
      (walkEnd (PortTables.portGraph input) start left =
        walkEnd (PortTables.portGraph input) start right)

def fieldPlan {d : Nat} (n : Nat) (ports : Fin (n + 1) → Fin d)
    (k : Fin (n + 1)) : Field (slotCount d n) → Instruction d
  | .inl (a, b) => .relation (tailPorts n ports k) (ports k) a b
  | .inr (.inl i) => .equal (addressPorts i) (tailPorts n ports k)
  | .inr (.inr i) => .equal (List.ofFn ports ++ addressPorts i) (headPorts n ports k)

theorem evaluate_fieldPlan {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (start : Fin vertices) (ports : Fin (n + 1) → Fin d)
    (k : Fin (n + 1)) (field : Field (slotCount d n)) :
    evaluate input start (fieldPlan n ports k field) = walkData input n (start, ports) k field := by
  rcases field with ⟨a,b⟩ | i | i
  · simp only [evaluate, fieldPlan, walkData, walkEnd_tailPorts]
    have hp : (edgeAt (PortTables.portGraph input) n (start, ports) k).2 = ports k :=
      edgeAt_port (PortTables.portGraph input) n (start, ports) k
    rw [← hp]
  · simp only [evaluate, fieldPlan, walkData, endpointMask, walkEnd_tailPorts]
    have ha := walkEnd_addressPorts (t := n + 1) (PortTables.portGraph input) start i
    rw [ha]
  · simp only [evaluate, fieldPlan, walkData, endpointMask, walkEnd_append,
      walkEnd_headPorts]
    rw [← wordEnd_eq_walkEnd_ofFn]
    have ha := walkEnd_addressPorts (t := n + 1) (PortTables.portGraph input)
      (wordEnd (PortTables.portGraph input) (n + 1) start ports) i
    rw [ha]
    rfl

def directedFieldPlan {d : Nat} (n : Nat) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (k : Fin (n + 1)) (field : Field (slotCount d n)) : Instruction d :=
  fieldPlan n ports k (if direction then transposeField field else field)

theorem fieldPlan_radius {d : Nat} (n : Nat) (ports : Fin (n + 1) → Fin d)
    (k : Fin (n + 1)) (field : Field (slotCount d n)) :
    (fieldPlan n ports k field).radius ≤ 2 * (n + 1) := by
  have hk := k.isLt
  rcases field with ⟨a,b⟩ | i | i
  · simp only [fieldPlan, Instruction.radius, tailPorts_length]
    omega
  · have hi := addressPorts_length_le i
    simp only [fieldPlan, Instruction.radius, tailPorts_length]
    exact max_le (by omega) (by omega)
  · have hi := addressPorts_length_le i
    simp only [fieldPlan, Instruction.radius, headPorts, List.length_append,
      List.length_ofFn, List.length_singleton, tailPorts_length]
    exact max_le (by omega) (by omega)

theorem directedFieldPlan_radius {d : Nat} (n : Nat) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (k : Fin (n + 1)) (field : Field (slotCount d n)) :
    (directedFieldPlan n ports direction k field).radius ≤ 2 * (n + 1) :=
  fieldPlan_radius n ports k _

theorem evaluate_directedFieldPlan {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (start : Fin vertices) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (k : Fin (n + 1)) (field : Field (slotCount d n)) :
    evaluate input start (directedFieldPlan n ports direction k field) =
      rowData input n (direction, start, ports) k field :=
  evaluate_fieldPlan input n start ports k _

/-- The exact fixed sequence of data-producing commands, in serialized order. -/
def rowPlan {d : Nat} (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    List (Instruction d) :=
  List.ofFn fun i : Fin (inputSize (n + 1) (slotCount d n)) =>
    let pair := (inputEquiv (n + 1) (slotCount d n)).symm i
    directedFieldPlan n ports direction pair.1 pair.2

theorem evaluate_rowPlan {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (start : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    (rowPlan n ports direction).map (evaluate input start) =
      List.ofFn (rowBits input n (direction, start, ports)) := by
  rw [rowPlan, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  rw [evaluate_directedFieldPlan, rowBits_packData]
  rfl

theorem dataTape_eq_plan {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (start : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    dataTape input n (direction, start, ports) =
      encodeBits ((rowPlan n ports direction).map (evaluate input start)) := by
  rw [evaluate_rowPlan, dataTape_eq]

end UniqueGamesTheorem.Foundations.PCP.PoweringFieldPlan

/-! Exact tail and reverse-index fields of the actual powering-table rows.
The reverse address is affine in the live starting vertex; the coefficient
and offset depend only on the fixed degree, word, and orientation. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringRowHeaderSemantics

open PoweringWalks PoweringEnumeration
open UniqueGamesTheorem.Foundations.Complexity

variable {vertices d : Nat}

def tailVertex (input : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) : Fin vertices :=
  if direction then wordEnd (PortTables.portGraph input) (n + 1) vertex ports else vertex

def headerWords (input : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) : List Nat :=
  [(tailVertex input n vertex ports direction).val, reverseValue d n vertex ports direction]

/-- The stored tail is the recorded start or endpoint according to direction. -/
theorem table_tail (input : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    (PoweringTables.table input n).rows[encodeDart vertices d n (direction, vertex, ports)].tail =
      tailVertex input n vertex ports direction := by
  change (GenericGraphTables.semantics (PoweringTables.table input n)).tail
    (encodeDart vertices d n (direction, vertex, ports)) = _
  rw [PoweringTables.semantics_table]
  change (PoweringTables.mathematicalGraph input n).tail
    ((dartEquiv vertices d n).symm (dartEquiv vertices d n (direction, vertex, ports))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- The reverse address retains the word and changes only its direction bit. -/
theorem table_reverseValue (input : PortTables.Table vertices d) (n : Nat)
    (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    (PoweringTables.table input n).rows[encodeDart vertices d n
      (direction, vertex, ports)].reverseIndex.val = reverseValue d n vertex ports direction := by
  change (GenericGraphTables.reverseAt (PoweringTables.table input n).rows
    (encodeDart vertices d n (direction, vertex, ports))).val = _
  rw [PoweringTables.table_reverse, encodeDart, dartEquiv_val]
  cases direction <;>
    simp [reverseValue, blockSize, reverseOffset, orientationEquiv, Nat.add_assoc] <;> decide

theorem headerWords_eq (input : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    headerWords input n vertex ports direction =
      [(PoweringTables.table input n).rows[encodeDart vertices d n
        (direction, vertex, ports)].tail.val,
       (PoweringTables.table input n).rows[encodeDart vertices d n
        (direction, vertex, ports)].reverseIndex.val] := by
  rw [table_tail, table_reverseValue]
  rfl

/-- Prepending these two fields to the existing relation yields the exact
serialized row, preserving the rest of the output tape. -/
theorem header_relation_bits (input : PortTables.Table vertices d) (n : Nat)
    (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (suffix : List Bool) :
    encodeWords (headerWords input n vertex ports direction) ++
      (encodeWords (GenericGraphTables.relationWords
        (PoweringTables.table input n).rows[encodeDart vertices d n
          (direction, vertex, ports)].relation) ++ suffix) =
      encodeWords (GenericGraphTables.rowWords
        (PoweringTables.table input n).rows[encodeDart vertices d n
          (direction, vertex, ports)]) ++ suffix := by
  rw [headerWords_eq, ← List.append_assoc, ← encodeWords_append]
  rfl

end UniqueGamesTheorem.Foundations.PCP.PoweringRowHeaderSemantics

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PoweringTableSemanticsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

abbrev EncodedLabeling (vertices d n : Nat) :=
  Fin vertices → Fin (labelCount d n)

def encodeLabeling {vertices : Nat} (d n : Nat) (labels : RawLabeling vertices d n) :
    EncodedLabeling vertices d n :=
  fun v => encodeLabel d (n + 1) 64 (labels v)

def decodeLabeling {vertices : Nat} (d n : Nat) (labels : EncodedLabeling vertices d n) :
    RawLabeling vertices d n :=
  fun v => decodeLabel d (n + 1) 64 (labels v)

@[simp] theorem decodeLabeling_encodeLabeling {vertices : Nat} (d n : Nat)
    (labels : RawLabeling vertices d n) :
    decodeLabeling d n (encodeLabeling d n labels) = labels := by
  funext v
  exact decodeLabel_encodeLabel d (n + 1) 64 (labels v)

@[simp] theorem encodeLabeling_decodeLabeling {vertices : Nat} (d n : Nat)
    (labels : EncodedLabeling vertices d n) :
    encodeLabeling d n (decodeLabeling d n labels) = labels := by
  funext v
  exact encodeLabel_decodeLabel d (n + 1) 64 (labels v)

/-- Each enumerated directed occurrence evaluates its actual powering test. -/
theorem edgeSatisfied_encoded {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (labels : RawLabeling vertices d n)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) :
    (GenericGraphTables.semantics (table input n)).edgeSatisfied
      (encodeLabeling d n labels) (encodeDart vertices d n e) =
        (mathematicalGraph input n).edgeSatisfied labels e := by
  rw [semantics_table]
  unfold encodeLabeling encodeLabel encodeDart
  simpa using!
    GenericGraphTables.enumeratedGraph_edgeSatisfied (mathematicalGraph input n)
      (Equiv.refl _) (dartEquiv vertices d n) (paddedLabelEquiv d (n + 1) 64) labels e

/-- Exact rejected-dart counting, retaining both orientations and repeated walks. -/
theorem rejectionCount_encoded {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (labels : RawLabeling vertices d n) :
    (GenericGraphTables.semantics (table input n)).rejectionCount
      (encodeLabeling d n labels) = (mathematicalGraph input n).rejectionCount labels := by
  rw [semantics_table]
  unfold encodeLabeling encodeLabel
  simpa using!
    GenericGraphTables.enumeratedGraph_rejectionCount (mathematicalGraph input n)
      (Equiv.refl _) (dartEquiv vertices d n) (paddedLabelEquiv d (n + 1) 64) labels

theorem rejectionCount_decoded {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (labels : EncodedLabeling vertices d n) :
    (GenericGraphTables.semantics (table input n)).rejectionCount labels =
      (mathematicalGraph input n).rejectionCount (decodeLabeling d n labels) := by
  have h := rejectionCount_encoded input n (decodeLabeling d n labels)
  erw [encodeLabeling_decodeLabeling d n labels] at h
  exact h

/-- The denominator equality comes from the same explicit dart bijection. -/
theorem card_darts_eq_table {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) :
    Fintype.card (PoweringTest.Dart (Fin vertices) (Fin d) n) = (table input n).darts := by
  change Fintype.card (PoweringTest.Dart (Fin vertices) (Fin d) n) =
    2 * vertices * d ^ (n + 1)
  simpa only [Fintype.card_fin] using Fintype.card_congr (dartEquiv vertices d n)

/-- The table has a satisfying encoded assignment exactly when the powered graph does. -/
theorem satisfiable_iff {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) :
    (GenericGraphTables.semantics (table input n)).Satisfiable ↔
      (mathematicalGraph input n).Satisfiable := by
  constructor
  · rintro ⟨labels, satisfies⟩
    refine ⟨decodeLabeling d n labels, ?_⟩
    intro e
    have h := edgeSatisfied_encoded input n (decodeLabeling d n labels) e
    erw [encodeLabeling_decodeLabeling d n labels] at h
    exact h.symm.trans (satisfies (encodeDart vertices d n e))
  · rintro ⟨labels, satisfies⟩
    refine ⟨encodeLabeling d n labels, ?_⟩
    intro i
    have h := edgeSatisfied_encoded input n labels (decodeDart vertices d n i)
    rw [encodeDart_decodeDart vertices d n i] at h
    exact h.trans (satisfies (decodeDart vertices d n i))

/-- Perfect completeness from the actual stored base predicates. -/
theorem preserves_satisfiability {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (h : (PortTables.baseGraph input).Satisfiable) :
    (GenericGraphTables.semantics (table input n)).Satisfiable := by
  apply (satisfiable_iff input n).mpr
  exact PoweringTest.preserves_satisfiability (PortTables.portGraph input)
    (PortTables.accepts input) (PortTables.accepts_rotation input) n
    (finitePortSelector (PortTables.portGraph input) (n + 1)) h

/-- Uniform actual rejection-count gaps are invariant under the executable encoding. -/
theorem uniform_count_gap_iff {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (epsilon : ℝ) :
    (∀ labels : EncodedLabeling vertices d n,
      epsilon * ((table input n).darts : ℝ) ≤
        ((GenericGraphTables.semantics (table input n)).rejectionCount labels : ℝ)) ↔
    (∀ labels : RawLabeling vertices d n,
      epsilon * (Fintype.card (PoweringTest.Dart (Fin vertices) (Fin d) n) : ℝ) ≤
        ((mathematicalGraph input n).rejectionCount labels : ℝ)) := by
  constructor
  · intro h labels
    have hlabels := h (encodeLabeling d n labels)
    erw [rejectionCount_encoded input n labels, ← card_darts_eq_table input n] at hlabels
    exact hlabels
  · intro h labels
    rw [rejectionCount_decoded input n labels]
    have hlabels := h (decodeLabeling d n labels)
    rw [card_darts_eq_table input n] at hlabels
    exact hlabels

/-- Apply an established powering count bound to every encoded table labeling. -/
theorem uniform_count_gap {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (epsilon : ℝ)
    (hgap : ∀ labels : RawLabeling vertices d n,
      epsilon * (Fintype.card (PoweringTest.Dart (Fin vertices) (Fin d) n) : ℝ) ≤
        ((mathematicalGraph input n).rejectionCount labels : ℝ)) :
    ∀ labels : EncodedLabeling vertices d n,
      epsilon * ((table input n).darts : ℝ) ≤
        ((GenericGraphTables.semantics (table input n)).rejectionCount labels : ℝ) :=
  (uniform_count_gap_iff input n epsilon).mpr hgap

end UniqueGamesTheorem.Foundations.PCP.PoweringTableSemantics

/-!
# The actual first moment of an endpoint-opinion witness

The pivot factorization is applied to actual finite walks. Its two endpoint
operator bounds are obtained from the proved lazy-graph mixture and smoothing
theorem. No witness-event probability law is assumed.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringWitness

open PoweringWalks SpectralReturn PoweringReturn PoweringLazy
open PoweringMoment (bit)

variable {V D : Type*}

/-- A constant scalar passes through every iterate of the actual graph mean. -/
theorem iterate_mul_const [Fintype D] (G : PortGraph V D)
    (n : Nat) (c : ℝ) (h : V → ℝ) :
    iterateOperator G n (fun x => c * h x) =
      fun x => c * iterateOperator G n h x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change averagingOperator G (iterateOperator G n (fun x => c * h x)) =
      fun x => c * averagingOperator G (iterateOperator G n h) x
    rw [ih]
    funext v
    exact mean_mul_left c (fun d => iterateOperator G n h (G.rot (v, d)).1)

/-- The actual pivot dart is marked and both endpoint opinions pass their
tests. For indicator opinions this is the indicator of their conjunction. -/
noncomputable def endpointWitness (G : PortGraph V D) (bad : Edge V D → Bool)
    (φ ψ : Edge V D → V → ℝ) (n : Nat) (k : Fin (n + 1))
    (w : Walk V D (n + 1)) : ℝ :=
  bit (bad (edgeAt G n w k) = true) *
    φ (edgeAt G n w k) w.1 * ψ (edgeAt G n w k) (endpoint G w)

/-- Vertex-indexed opinions are tested at the two endpoints of the pivot dart. -/
noncomputable def vertexWitness (G : PortGraph V D) (bad : Edge V D → Bool)
    (f : V → V → ℝ) (n : Nat) (k : Fin (n + 1)) :
    Walk V D (n + 1) → ℝ :=
  endpointWitness G bad (fun e => f e.1) (fun e => f (next G e.1 e.2)) n k

/-- Pointwise bounds on the two genuine earlier-length graph iterates give
the witness first moment. The hypotheses are only needed on marked darts. -/
theorem endpoint_lower_bound [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (n : Nat) (k : Fin (n + 1)) (bad : Edge V D → Bool)
    (φ ψ : Edge V D → V → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hL : ∀ e, bad e = true → a ≤ iterateOperator G k.val (φ e) e.1)
    (hR : ∀ e, bad e = true →
      a ≤ iterateOperator G (n - k.val) (ψ e) (next G e.1 e.2)) :
    edgeDensity bad * a ^ 2 ≤ mean (endpointWitness G bad φ ψ n k) := by
  have hfactor : mean (endpointWitness G bad φ ψ n k) =
      mean (fun e : Edge V D =>
        (bit (bad e = true) * iterateOperator G k.val (φ e) e.1) *
          iterateOperator G (n - k.val) (ψ e) (next G e.1 e.2)) := by
    unfold endpointWitness
    rw [mean_edge_endpoints G n k (fun e x => bit (bad e = true) * φ e x) ψ]
    simp_rw [iterate_mul_const]
  have hbitMean : mean (fun e : Edge V D => bit (bad e = true)) = edgeDensity bad := by
    calc
      _ = mean (fun v : V => mean (fun d : D => bit (bad (v, d) = true))) :=
        mean_prod (A := V) (B := D) (fun e => bit (bad e = true))
      _ = edgeDensity bad := by simp only [mean_edge_bit, edgeDensity]
  calc
    edgeDensity bad * a ^ 2 =
        mean (fun e : Edge V D => bit (bad e = true) * a ^ 2) := by
      rw [mean_mul_right, hbitMean]
    _ ≤ mean (fun e : Edge V D =>
        (bit (bad e = true) * iterateOperator G k.val (φ e) e.1) *
          iterateOperator G (n - k.val) (ψ e) (next G e.1 e.2)) := by
      apply mean_mono
      intro e
      cases hb : bad e with
      | false => simp [bit]
      | true =>
        have hprod := mul_le_mul (hL e hb) (hR e hb) ha (ha.trans (hL e hb))
        simpa [bit, hb, pow_two] using hprod
    _ = mean (endpointWitness G bad φ ψ n k) := hfactor.symm

/-- The two endpoint-opinion tests each retain probability at least `1/(2q)`
at every middle pivot. The walk has `2N+1` edges, with `N=(4qM)^2`, so the
prefix and suffix lengths are exactly `k` and `2N-k`.

The only modal input is the actual centered lazy iterate at each vertex. It
will be supplied by the finite modal-opinion decoder, not by a witness law.
-/
theorem lazy_middle_witness_mean [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (q M : Nat) (hq : 1 ≤ q) (hM : 1 ≤ M)
    (k : Fin (2 * (4 * q * M) ^ 2 + 1))
    (hlo : (4 * q * M) ^ 2 - M ≤ k.val)
    (hhi : k.val ≤ (4 * q * M) ^ 2 + M)
    (bad : Edge V (Bool × D) → Bool) (f : V → V → ℝ)
    (hf : ∀ u w, f u w ∈ Set.Icc (0 : ℝ) 1)
    (hmodal : ∀ u, 1 / (q : ℝ) ≤
      iterateOperator (lazyGraph G) ((4 * q * M) ^ 2) (f u) u) :
    edgeDensity bad / (4 * (q : ℝ) ^ 2) ≤
      mean (vertexWitness (lazyGraph G) bad f (2 * (4 * q * M) ^ 2) k) := by
  have hk : k.val ≤ 2 * (4 * q * M) ^ 2 := Nat.le_of_lt_succ k.isLt
  have hslo : (4 * q * M) ^ 2 - M ≤ 2 * (4 * q * M) ^ 2 - k.val := by omega
  have hshi : 2 * (4 * q * M) ^ 2 - k.val ≤ (4 * q * M) ^ 2 + M := by omega
  have ha : (0 : ℝ) ≤ 1 / (2 * (q : ℝ)) := by positivity
  have hbound := endpoint_lower_bound (lazyGraph G) (2 * (4 * q * M) ^ 2) k bad
    (fun e => f e.1) (fun e => f (next (lazyGraph G) e.1 e.2))
    (1 / (2 * (q : ℝ))) ha
    (by
      intro e _
      exact lazy_endpoint_modal_transfer G q M k.val hq hM hlo hhi
        (f e.1) (hf e.1) e.1 (hmodal e.1))
    (by
      intro e _
      exact lazy_endpoint_modal_transfer G q M (2 * (4 * q * M) ^ 2 - k.val)
        hq hM hslo hshi (f (next (lazyGraph G) e.1 e.2))
        (hf (next (lazyGraph G) e.1 e.2)) (next (lazyGraph G) e.1 e.2)
        (hmodal (next (lazyGraph G) e.1 e.2)))
  have hscale : edgeDensity bad * (1 / (2 * (q : ℝ))) ^ 2 =
      edgeDensity bad / (4 * (q : ℝ) ^ 2) := by ring
  simpa only [vertexWitness, hscale] using hbound

end UniqueGamesTheorem.Foundations.PCP.PoweringWitness

/-! The actual graph-powering soundness bound. Modal endpoint opinions give
the first moment, spectral return gives the second moment, and an actual
checked path constraint turns each witness into rejection. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringSoundness

open scoped BigOperators
open PoweringWalks PoweringLabels PoweringOpinions PoweringTest
open SpectralReturn PoweringWitness PoweringMomentBound
open PoweringMoment (bit hits)

variable {V D A : Type*}

variable [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
  [Fintype A] [Nonempty A]

def decodedError (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n N : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A) : ℝ :=
  edgeDensity (decodedBad G accepts (decoded G (n + 1) N selectors labels fallback))

def poweredRejection (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) : ℝ :=
  mean (fun d : Dart V D n => bit ((poweredGraph G accepts n selectors).edgeSatisfied labels d = false))

omit [Fintype V] [Nonempty V] [Nonempty D] in
theorem witness_bit_eq (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n N : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A)
    (w : Walk V D (n + 1)) (k : Fin (n + 1)) :
    bit (witness G accepts n selectors labels fallback
      (decoded G (n + 1) N selectors labels fallback) w k) =
      vertexWitness G
        (decodedBad G accepts (decoded G (n + 1) N selectors labels fallback))
        (matchFn G (n + 1) N selectors labels fallback) n k w := by
  simp only [witness, vertexWitness, endpointWitness, matchFn,
    PoweringMoment.bit_mul, next, and_assoc]

omit [Nonempty V] in
theorem modal_witness_mean (G : PortGraph V D) (M : Nat) (hM : 1 ≤ M)
    (accepts : Edge V (Bool × D) → A → A → Bool)
    (selectors : ∀ v, AddressSelector (lazyGraph G) (2 * center (Fintype.card A) M + 1) v)
    (labels : V → PaddedLabel (Bool × D) (2 * center (Fintype.card A) M + 1) A)
    (fallback : A) (k : Fin (2 * center (Fintype.card A) M + 1))
    (hlo : center (Fintype.card A) M - M ≤ k.val)
    (hhi : k.val ≤ center (Fintype.card A) M + M) :
    decodedError (lazyGraph G) accepts (2 * center (Fintype.card A) M)
      (center (Fintype.card A) M) selectors labels fallback / (4 * (Fintype.card A : ℝ) ^ 2) ≤
      mean (fun w => bit (witness (lazyGraph G) accepts (2 * center (Fintype.card A) M)
        selectors labels fallback (decoded (lazyGraph G) (2 * center (Fintype.card A) M + 1)
          (center (Fintype.card A) M) selectors labels fallback) w k)) := by
  have h := lazy_middle_witness_mean G (Fintype.card A) M Fintype.card_pos hM k hlo hhi
    (decodedBad (lazyGraph G) accepts
      (decoded (lazyGraph G) (2 * center (Fintype.card A) M + 1)
        (center (Fintype.card A) M) selectors labels fallback))
    (matchFn (lazyGraph G) (2 * center (Fintype.card A) M + 1)
      (center (Fintype.card A) M) selectors labels fallback)
    (matchFn_mem_Icc (lazyGraph G) (2 * center (Fintype.card A) M + 1)
      (center (Fintype.card A) M) selectors labels fallback)
    (decoded_modal_baseline (lazyGraph G) (2 * center (Fintype.card A) M + 1)
      (center (Fintype.card A) M) selectors labels fallback)
  simp_rw [witness_bit_eq]
  convert h using 1 <;> rfl

/-- Positive decoded error forces rejection of the actual powered graph.
The cap and amplification coefficient are explicit constants. -/
theorem rejection_lower_bound (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate (lazyGraph G) lambda)
    (accepts : Edge V (Bool × D) → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts ((lazyGraph G).rot e) b a = accepts e a b)
    (M : Nat) (hM : 1 ≤ M)
    (selectors : ∀ v, AddressSelector (lazyGraph G) (2 * center (Fintype.card A) M + 1) v)
    (labels : V → PaddedLabel (Bool × D) (2 * center (Fintype.card A) M + 1) A)
    (fallback : A)
    (hε : 0 < decodedError (lazyGraph G) accepts (2 * center (Fintype.card A) M)
      (center (Fintype.card A) M) selectors labels fallback) :
    gain (Fintype.card A) M lambda *
        min (decodedError (lazyGraph G) accepts (2 * center (Fintype.card A) M)
          (center (Fintype.card A) M) selectors labels fallback)
          (1 / ((2 * center (Fintype.card A) M + 1 : Nat) : ℝ)) ≤
      poweredRejection (lazyGraph G) accepts (2 * center (Fintype.card A) M) selectors labels := by
  let q := Fintype.card A
  let N := center q M
  let n := 2 * N
  let m := 2 * M + 1
  let start := N - M
  let L := lazyGraph G
  let assignment := decoded L (n + 1) N selectors labels fallback
  let bad := decodedBad L accepts assignment
  let ε := edgeDensity bad
  let α : ℝ := 1 / (2 * (q : ℝ))
  let C : ℝ := 1 + 2 / (1 - lambda)
  have hNM : M ≤ N := le_center q M Fintype.card_pos hM
  have hw : start + m ≤ n + 1 := by dsimp [start, m, n]; omega
  let E := windowEvent L bad n start m hw
  let W : Fin m → Walk V (Bool × D) (n + 1) → Prop := fun i w =>
    witness L accepts n selectors labels fallback assignment w (windowIndex n start m hw i)
  let R : Walk V (Bool × D) (n + 1) → Prop := fun w =>
    pathAccepts L accepts n selectors w (labels w.1) (labels (endpoint L w)) = false
  have hWE : ∀ i w, W i w → E i w := by
    intro i w h
    exact h.1
  have hWR : ∀ i w, W i w → R w := by
    intro i w h
    exact witness_implies_path_rejection L accepts n selectors labels fallback assignment w
      (windowIndex n start m hw i) h
  have hpoint (i : Fin m) : ε / (4 * (q : ℝ) ^ 2) ≤ mean (fun w => bit (W i w)) := by
    have hlo : N - M ≤ (windowIndex n start m hw i).val := by
      dsimp [windowIndex, start]
      omega
    have hhi : (windowIndex n start m hw i).val ≤ N + M := by
      have hi := i.isLt
      dsimp [windowIndex, start]
      dsimp [m] at hi
      omega
    exact modal_witness_mean G M hM accepts selectors labels fallback
      (windowIndex n start m hw i) hlo hhi
  have hfirst : α ^ 2 * (m : ℝ) * ε ≤ mean (hits W) := by
    change α ^ 2 * (m : ℝ) * ε ≤ PoweringMoment.mean (hits W)
    rw [PoweringMoment.mean_hits]
    calc
      _ = ∑ _i : Fin m, ε / (4 * (q : ℝ) ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        dsimp [α]
        ring
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hpoint i)
  have hsecond : mean (fun w => hits E w ^ 2) ≤
      (m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε) :=
    window_second_moment_le L lambda certificate bad
      (decodedBad_rot L accepts reverse_accepts assignment) n start m hw
  have hε' : 0 < ε := hε
  have hm : 0 < m := by dsimp [m]; omega
  have hmReal : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hqReal : (0 : ℝ) < q := Nat.cast_pos.mpr Fintype.card_pos
  have hden : 0 < 1 - lambda := sub_pos.mpr certificate.lt_one
  have hC : 0 < C := by dsimp [C]; positivity
  have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hα : 0 < α := by dsimp [α]; positivity
  have ha : 0 < α ^ 2 * (m : ℝ) * ε := by positivity
  have hb : 0 < (m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε) := by
    have hdiff : 0 ≤ (m : ℝ) - 1 := sub_nonneg.mpr hmOne
    positivity
  have hCS := PoweringMoment.rejection_lower_bound E W R hWE hWR
    (α ^ 2 * (m : ℝ) * ε) ((m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε))
    ha hb hfirst hsecond
  have ht : (0 : ℝ) < ((n + 1 : Nat) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have hmn : m ≤ n + 1 := by dsimp [m, n]; omega
  have hmt : (m : ℝ) - 1 ≤ ((n + 1 : Nat) : ℝ) := by
    have hmnReal : (m : ℝ) ≤ ((n + 1 : Nat) : ℝ) := by exact_mod_cast hmn
    linarith
  have hratio := PoweringNumeric.count_moment_ratio_lower α ε C ((n + 1 : Nat) : ℝ)
    m hm hε' hC ht hmt
  change (α ^ 4 * (m : ℝ) / (C + 1)) * min ε (1 / ((n + 1 : Nat) : ℝ)) ≤ _
  change _ ≤ mean (fun d : Dart V (Bool × D) n =>
    bit ((poweredGraph L accepts n selectors).edgeSatisfied labels d = false))
  rw [rejection_mean_eq_path_mean]
  exact hratio.trans hCS

end UniqueGamesTheorem.Foundations.PCP.PoweringSoundness

namespace UniqueGamesTheorem.Foundations.PCP.PoweringGap

open PoweringWalks PoweringLabels PoweringOpinions PoweringTest
open SpectralReturn PoweringSoundness PoweringCounting

variable {V D A : Type*}

variable [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
  [Fintype A] [Nonempty A]

theorem uniform_count_gap (G : PortGraph V D) (lambda : ℝ)
    (certificate : SpectralCertificate (lazyGraph G) lambda)
    (accepts : Edge V (Bool × D) → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts ((lazyGraph G).rot e) b a = accepts e a b)
    (M : Nat) (hM : 1 ≤ M)
    (selectors : ∀ v, AddressSelector (lazyGraph G)
      (2 * center (Fintype.card A) M + 1) v)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hgap : ∀ assignment : V → A,
      epsilon * (Fintype.card (Edge V (Bool × D)) : ℝ) ≤
        ((baseGraph (lazyGraph G) accepts reverse_accepts).rejectionCount assignment : ℝ))
    (labels : V → PaddedLabel (Bool × D) (2 * center (Fintype.card A) M + 1) A) :
    (gain (Fintype.card A) M lambda *
      min epsilon (1 / ((2 * center (Fintype.card A) M + 1 : Nat) : ℝ))) *
        (Fintype.card (Dart V (Bool × D) (2 * center (Fintype.card A) M)) : ℝ) ≤
      ((poweredGraph (lazyGraph G) accepts (2 * center (Fintype.card A) M)
        selectors).rejectionCount labels : ℝ) := by
  classical
  let L := lazyGraph G
  let N := center (Fintype.card A) M
  let n := 2 * N
  let H := poweredGraph L accepts n selectors
  change (gain (Fintype.card A) M lambda *
      min epsilon (1 / ((n + 1 : Nat) : ℝ))) *
        (Fintype.card (Dart V (Bool × D) n) : ℝ) ≤
      (H.rejectionCount labels : ℝ)
  rcases eq_or_lt_of_le hepsilon with hzero | hpositive
  · rw [← hzero]
    have hcap : (0 : ℝ) ≤ 1 / ((n + 1 : Nat) : ℝ) := by positivity
    rw [min_eq_left hcap, mul_zero, zero_mul]
    exact Nat.cast_nonneg _
  · let fallback : A := Classical.choice (inferInstance : Nonempty A)
    let assignment := decoded L (n + 1) N selectors labels fallback
    have hdecoded : epsilon ≤ decodedError L accepts n N selectors labels fallback := by
      change epsilon ≤ edgeDensity (decodedBad L accepts assignment)
      exact base_count_lower_to_density L accepts reverse_accepts assignment
        Fintype.card_pos epsilon (hgap assignment)
    have herror : 0 < decodedError L accepts n N selectors labels fallback :=
      hpositive.trans_le hdecoded
    have hsound := PoweringSoundness.rejection_lower_bound G lambda certificate
      accepts reverse_accepts M hM selectors labels fallback herror
    have hgain : 0 ≤ gain (Fintype.card A) M lambda :=
      gain_nonneg (Fintype.card A) M lambda certificate.lt_one
    have hmin : min epsilon (1 / ((n + 1 : Nat) : ℝ)) ≤
        min (decodedError L accepts n N selectors labels fallback)
          (1 / ((n + 1 : Nat) : ℝ)) :=
      min_le_min hdecoded (le_refl _)
    have hlower : gain (Fintype.card A) M lambda *
        min epsilon (1 / ((n + 1 : Nat) : ℝ)) ≤
        poweredRejection L accepts n selectors labels :=
      (mul_le_mul_of_nonneg_left hmin hgain).trans hsound
    exact (constraint_rejection_lower_iff H labels Fintype.card_pos
      (gain (Fintype.card A) M lambda *
        min epsilon (1 / ((n + 1 : Nat) : ℝ)))).mp hlower

end UniqueGamesTheorem.Foundations.PCP.PoweringGap

/-! Actual directed-cut expansion from the graph's zero-mean spectral
certificate. Parallel edges and loops retain their indexed port multiplicities. -/
namespace UniqueGamesTheorem.Foundations.PCP.SpectralCut

open scoped BigOperators
open PoweringWalks SpectralReturn

variable {V D : Type*} [Fintype V] [Fintype D] [DecidableEq V]

def cut (G : PortGraph V D) (S : Finset V) : Finset (V × D) :=
  Finset.univ.filter (fun e => e.1 ∈ S ∧ (G.rot e).1 ∉ S)

section Nonempty
variable [Nonempty V] [Nonempty D] (G : PortGraph V D)

omit [Nonempty V] in
/-- The normalized cut count is exactly mean minus one-step correlation. -/
theorem cut_density_eq (S : Finset V) :
    ((cut G S).card : ℝ) / (Fintype.card (V × D) : ℝ) =
      mean (indicator S) - correlation (indicator S) (averagingOperator G (indicator S)) := by
  classical
  calc
    _ = mean (indicator (cut G S)) := (mean_indicator (cut G S)).symm
    _ = mean (fun e : V × D => indicator S e.1 -
        indicator S e.1 * indicator S (G.rot e).1) := by
      congr 1
      funext e
      by_cases hv : e.1 ∈ S <;> by_cases hw : (G.rot e).1 ∈ S <;>
        simp [indicator, cut, hv, hw]
    _ = mean (fun v => mean (fun d : D => indicator S v -
        indicator S v * indicator S (G.rot (v,d)).1)) := mean_prod _
    _ = mean (fun v => indicator S v -
        indicator S v * averagingOperator G (indicator S) v) := by
      congr 1
      funext v
      rw [mean_sub, mean_const, mean_mul_left]
      rfl
    _ = _ := mean_sub _ _

theorem cut_density_ge_variance
    (certificate : SpectralCertificate G (1/2)) (S : Finset V) :
    (1/2:ℝ) * mean (indicator S) * (1 - mean (indicator S)) ≤
      ((cut G S).card : ℝ) / (Fintype.card (V × D) : ℝ) := by
  let f := indicator S
  have hz : mean (fun v => f v - mean f) = 0 := by
    rw [mean_sub, mean_const, sub_self]
  have he : energy (fun v => f v - mean f) = mean f - mean f ^ 2 := by
    rw [energy_sub_const, energy_indicator]
    ring
  have hb := zero_mean_correlation_bound G (1/2) certificate
    (fun v => f v - mean f) hz 1
  have hc := correlation_centered G f 1
  simp only [iterateOperator, pow_one, he] at hb hc
  rw [cut_density_eq]
  change (1/2:ℝ) * mean f * (1 - mean f) ≤
    mean f - correlation f (averagingOperator G f)
  nlinarith

theorem cut_density_ge_quarter
    (certificate : SpectralCertificate G (1/2)) (S : Finset V)
    (hsmall : 2 * S.card ≤ Fintype.card V) :
    mean (indicator S) / 4 ≤
      ((cut G S).card : ℝ) / (Fintype.card (V × D) : ℝ) := by
  have hN : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hp0 : 0 ≤ mean (indicator S) := mean_nonnegative _ (indicator_nonnegative S)
  have hp : mean (indicator S) ≤ (1/2:ℝ) := by
    rw [mean_indicator]
    apply (div_le_iff₀ hN).mpr
    have hs : (2:ℝ) * (S.card : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hsmall
    nlinarith
  have hv := cut_density_ge_variance G certificate S
  have hprod := mul_nonneg hp0 (sub_nonneg.mpr hp)
  nlinarith

/-- The real cardinal estimate before removing denominators. -/
theorem cut_card_ge_quarter_degree
    (certificate : SpectralCertificate G (1/2)) (S : Finset V)
    (hsmall : 2 * S.card ≤ Fintype.card V) :
    (Fintype.card D : ℝ) * (S.card : ℝ) / 4 ≤ ((cut G S).card : ℝ) := by
  have hN : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hD : (0:ℝ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  have h := cut_density_ge_quarter G certificate S hsmall
  rw [Fintype.card_prod, Nat.cast_mul] at h
  have hh := (le_div_iff₀ (mul_pos hN hD)).mp h
  have he : mean (indicator S) / 4 *
      ((Fintype.card V : ℝ) * (Fintype.card D : ℝ)) =
        (Fintype.card D : ℝ) * (S.card : ℝ) / 4 := by
    rw [mean_indicator]
    field_simp [ne_of_gt hN]
  rw [he] at hh
  exact hh

theorem degree_mul_card_le_four_cut
    (certificate : SpectralCertificate G (1/2)) (S : Finset V)
    (hsmall : 2 * S.card ≤ Fintype.card V) :
    Fintype.card D * S.card ≤ 4 * (cut G S).card := by
  have h := cut_card_ge_quarter_degree G certificate S hsmall
  have hr : (Fintype.card D : ℝ) * (S.card : ℝ) ≤ 4 * ((cut G S).card : ℝ) := by
    linarith
  exact_mod_cast hr

end Nonempty

/-- The natural-number expansion used in cloud rounding. Empty vertex sets
are included; a degree of at least eight supplies the nonempty port type. -/
theorem cut_card_ge_twice (G : PortGraph V D)
    (certificate : SpectralCertificate G (1/2)) (hdegree : 8 ≤ Fintype.card D)
    (S : Finset V) (hsmall : 2 * S.card ≤ Fintype.card V) :
    2 * S.card ≤ (cut G S).card := by
  let : Nonempty D := Fintype.card_pos_iff.mp (by omega)
  rcases isEmpty_or_nonempty V with hV | hV
  · let := hV
    have hzero : Fintype.card V = 0 := Fintype.card_eq_zero
    have hs : S.card = 0 := by omega
    simp only [hs, mul_zero, Nat.zero_le]
  · let := hV
    have h := degree_mul_card_le_four_cut G certificate S hsmall
    have hdeg := Nat.mul_le_mul_right S.card hdegree
    omega

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
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_Table
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table

variable {q : Nat}

theorem semantics_rows_congr {n m : Nat} {left right : GraphTables.Rows n m}
    (h : left = right) (hl : GraphTables.Valid left) (hr : GraphTables.Valid right) :
    GraphTables.semantics (⟨n, m, left, hl⟩ : GraphTables.Table) =
      GraphTables.semantics (⟨n, m, right, hr⟩ : GraphTables.Table) := by
  subst right
  rfl

/-- Full decoded graph equality, including reversal, endpoints, and every predicate bit. -/
theorem semantics_build (input : GenericGraphTables.Table q) :
    GraphTables.semantics (build input) =
      GraphTables.enumeratedGraph (AlphabetGraph.graph (GenericGraphTables.semantics input))
        (Enumeration.vertexEquiv input.vertices input.darts q)
        (Enumeration.dartEquiv input.darts q) Enumeration.labelEquiv := by
  exact (semantics_rows_congr (rows_eq_graphRows input) (rows_valid input)
    (GraphTables.graphRows_valid _)).trans (GraphTables.semantics_ofGraph _)

theorem edgeSatisfied_build (input : GenericGraphTables.Table q)
    (labeling : QueryIncidence.Vertex (AlphabetGraph.Event (Fin input.darts) (Fin q))
      (AlphabetGraph.Address (Fin input.vertices) (Fin input.darts) (Fin q)) →
        QueryIncidence.Label 6)
    (dart : QueryIncidence.Dart (AlphabetGraph.Event (Fin input.darts) (Fin q)) 6) :
    (GraphTables.semantics (build input)).edgeSatisfied
      (fun v => Enumeration.labelEquiv
        (labeling ((Enumeration.vertexEquiv input.vertices input.darts q).symm v)))
      (Enumeration.dartEquiv input.darts q dart) =
        (AlphabetGraph.graph (GenericGraphTables.semantics input)).edgeSatisfied labeling dart := by
  rw [semantics_build]
  exact GraphTables.enumeratedGraph_edgeSatisfied _ _ _ _ labeling dart

theorem rejectionCount_build (input : GenericGraphTables.Table q)
    (labeling : QueryIncidence.Vertex (AlphabetGraph.Event (Fin input.darts) (Fin q))
      (AlphabetGraph.Address (Fin input.vertices) (Fin input.darts) (Fin q)) →
        QueryIncidence.Label 6) :
    (GraphTables.semantics (build input)).rejectionCount
      (fun v => Enumeration.labelEquiv
        (labeling ((Enumeration.vertexEquiv input.vertices input.darts q).symm v))) =
        (AlphabetGraph.graph (GenericGraphTables.semantics input)).rejectionCount labeling := by
  rw [semantics_build]
  exact GraphTables.enumeratedGraph_rejectionCount _ _ _ _ labeling

theorem perfect_completeness [Nonempty (Fin q)] (input : GenericGraphTables.Table q)
    (satisfied : (GenericGraphTables.semantics input).Satisfiable) :
    (GraphTables.semantics (build input)).Satisfiable := by
  obtain ⟨labeling, accepted⟩ :=
    AlphabetGraph.perfect_completeness (GenericGraphTables.semantics input) satisfied
  refine ⟨fun v => Enumeration.labelEquiv
    (labeling ((Enumeration.vertexEquiv input.vertices input.darts q).symm v)), ?_⟩
  intro index
  have h := edgeSatisfied_build input labeling
    ((Enumeration.dartEquiv input.darts q).symm index)
  have index_eq := (Enumeration.dartEquiv input.darts q).apply_symm_apply index
  rw [index_eq] at h
  exact h.trans (accepted _)

/-- The serialized row list follows the same explicit occurrence order as the vector. -/
theorem rowList_eq_ordered (input : GenericGraphTables.Table q) :
    GraphTables.rowList (build input) =
      (Enumeration.ordered (Enumeration.dartEquiv input.darts q)).map
        (rowFromDart input) := by
  change (Vector.ofFn (fun index => rowFromDart input
      ((Enumeration.dartEquiv input.darts q).symm index))).toList =
    (List.ofFn (Enumeration.dartEquiv input.darts q).symm).map (rowFromDart input)
  simp only [Vector.toList_ofFn, List.map_ofFn, Function.comp_def]

/-- Complete output words: two headers followed by every ordered row block. -/
theorem tableWords_eq_ordered (input : GenericGraphTables.Table q) :
    GraphTables.tableWords (build input) =
      [Enumeration.vertexCount input.vertices input.darts q,
        Enumeration.dartCount input.darts q] ++
        (Enumeration.ordered (Enumeration.dartEquiv input.darts q)).flatMap
          (fun dart => GraphTables.rowWords (rowFromDart input dart)) := by
  simp only [GraphTables.tableWords, rowList_eq_ordered, build_vertices, build_darts,
    List.flatMap_map]

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_AlphabetTableBoundsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTableBounds

open AlphabetTable

variable {q : Nat}

/-- The actual table output obeys the real gap bound, with no rational
approximation and with empty input dart sets allowed. -/
theorem gap_transfer_real (hq : 0 < q) (input : GenericGraphTables.Table q)
    (eps : ℝ) (eps_nonnegative : 0 ≤ eps)
    (source : ∀ labeling : Fin input.vertices → Fin q,
      eps * (input.darts : ℝ) ≤
        ((GenericGraphTables.semantics input).rejectionCount labeling : ℝ))
    (labeling : Fin (Table.build input).vertices → GraphTables.Label) :
    (eps / 12288) * ((Table.build input).darts : ℝ) ≤
      ((GraphTables.semantics (Table.build input)).rejectionCount labeling : ℝ) := by
  classical
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  let lifted := fun vertex => Enumeration.labelEquiv.symm
    (labeling (Enumeration.vertexEquiv input.vertices input.darts q vertex))
  have h := AlphabetGraphBounds.gap_transfer_real
    (GenericGraphTables.semantics input) eps eps_nonnegative
    (by simpa only [Fintype.card_fin] using source) lifted
  rw [Enumeration.card_dart] at h
  have counts := Table.rejectionCount_build input lifted
  have restored : (fun v : Fin (Table.build input).vertices => Enumeration.labelEquiv
      (lifted ((Enumeration.vertexEquiv input.vertices input.darts q).symm v))) = labeling := by
    funext v
    dsimp only [lifted]
    rw [Enumeration.labelEquiv.apply_symm_apply]
    exact congrArg labeling
      ((Enumeration.vertexEquiv input.vertices input.darts q).apply_symm_apply v)
  rw [restored] at counts
  rw [← counts] at h
  exact h

end UniqueGamesTheorem.Foundations.PCP.AlphabetTableBounds

end

section

namespace UniqueGamesTheorem.Foundations.PCP.VerifierToCNF

open Target

theorem forbiddenLiteral_false {q : Nat} (V : FiniteVerifier q) (A : Fin V.variables → Bool)
    (e : Fin V.events) (p : PatternIndex q) (i : Fin q) :
    (forbiddenLiteral V e p i).eval A = false ↔ A (V.query e i) = patternAt q p i := by
  cases hp : patternAt q p i <;> cases ha : A (V.query e i) <;>
    simp [forbiddenLiteral, Literal.eval, hp, ha]

theorem forbiddenClause_values {q : Nat} (V : FiniteVerifier q)
    (B : Fin (outputVariables V) → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (forbiddenClause V e p).map (fun l => l.eval B) =
      mismatchBits V (restrictAssignment V B) e p := by
  simp [forbiddenClause, mismatchBits, List.map_ofFn, Function.comp_def, liftLiteral, Literal.eval,
    restrictAssignment]

theorem mismatchBits_false {q : Nat} (V : FiniteVerifier q) (A : Fin V.variables → Bool)
    (e : Fin V.events) (p : PatternIndex q)
    (actual : ∀ i, A (V.query e i) = patternAt q p i) :
    (mismatchBits V A e p).any id = false := by
  apply List.any_eq_false.mpr
  intro b hb
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
  have h := (forbiddenLiteral_false V A e p i).mpr (actual i)
  simp [h]

theorem mismatchBits_true {q : Nat} (V : FiniteVerifier q) (A : Fin V.variables → Bool)
    (e : Fin V.events) (p : PatternIndex q) (honest : eventValue V A e = true)
    (rejected : V.accepts e (patternAt q p) = false) :
    (mismatchBits V A e p).any id = true := by
  cases h : (mismatchBits V A e p).any id with
  | true => rfl
  | false =>
    have none := List.any_eq_false.mp h
    have equal : (fun i => A (V.query e i)) = patternAt q p := by
      funext i
      apply (forbiddenLiteral_false V A e p i).mp
      have hi := none ((forbiddenLiteral V e p i).eval A)
        (List.mem_ofFn.mpr ⟨i, rfl⟩)
      cases hv : (forbiddenLiteral V e p i).eval A <;> simp_all
    have impossible : V.accepts e (patternAt q p) = true := by
      simpa only [eventValue, equal] using honest
    rw [rejected] at impossible
    contradiction

theorem extended_auxiliary_values {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.variables → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (auxiliaryNames V e p).map (extendAssignment V hq A) = fillBits (mismatchBits V A e p) := by
  simp only [auxiliaryNames, List.map_ofFn, Function.comp_def, extend_fresh, mismatchFill]
  exact ofFn_getElem_of_length _ _ (mismatchFill_length V hq A e p)

end UniqueGamesTheorem.Foundations.PCP.VerifierToCNF

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_FinalBooleanVerifier
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.FinalBooleanVerifier

open Target

variable {V E : Type*} {n m : Nat}

/-- Acceptance is the actual graph predicate on the two recovered labels. -/
theorem eventValue_eq (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (assignment : Fin (n * 6) → Bool) (e : Fin m) :
    VerifierToCNF.eventValue (verifier G vertices edges) assignment e =
      G.edgeSatisfied (labelsOfBits vertices assignment) (edges.symm e) := by
  simp only [VerifierToCNF.eventValue, Fin.addCases_left, Fin.addCases_right,
    ConstraintGraph.edgeSatisfied]
  rfl

/-- The enumeration preserves the exact directed-dart rejection count. -/
theorem rejection_count_eq [Fintype E] (G : ConstraintGraph V E Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) (assignment : Fin (n * 6) → Bool) :
    VerifierToCNF.rejectedEventCount (verifier G vertices edges) assignment =
      G.rejectionCount (labelsOfBits vertices assignment) := by
  classical
  change ((List.finRange m).map
    (VerifierToCNF.eventValue (verifier G vertices edges) assignment)).count false = _
  rw [count_false_finRange]
  change (Finset.univ.filter (fun e : Fin m =>
    VerifierToCNF.eventValue (verifier G vertices edges) assignment e = false)).card =
      (G.rejectedDarts (labelsOfBits vertices assignment)).card
  apply Finset.card_equiv edges.symm
  intro e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    ConstraintGraph.rejectedDarts, eventValue_eq]

theorem verifier_completeness (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (labeling : V → Label)
    (satisfied : ∀ e, G.edgeSatisfied labeling e = true) :
    ∀ e, VerifierToCNF.eventValue (verifier G vertices edges)
      (bitsOfLabels vertices labeling) e = true := by
  intro e
  rw [eventValue_eq, labelsOfBits_bitsOfLabels]
  exact satisfied (edges.symm e)

abbrev OutputAssignment (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) :=
  Fin (VerifierToCNF.outputVariables (verifier G vertices edges)) → Bool

def extractLabeling (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (assignment : OutputAssignment G vertices edges) : V → Label :=
  labelsOfBits vertices (VerifierToCNF.restrictAssignment (verifier G vertices edges) assignment)

end UniqueGamesTheorem.Foundations.PCP.FinalBooleanVerifier

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PreprocessingPaddingTables
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
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

/-- Exact occurrence counts for arbitrary labels on all old and added vertices. -/
theorem pad_rejectionCount (table : Table n d) (h : n ≤ m)
    (labeling : Fin m → Label) :
    (baseGraph (pad table h)).rejectionCount labeling =
      (baseGraph table).rejectionCount (fun v => labeling (v.castLE h)) := by
  classical
  calc
    (baseGraph (pad table h)).rejectionCount labeling =
        (sumGraph table m).rejectionCount (fun v => labeling (vertexEquiv h v)) := by
      unfold ConstraintGraph.rejectionCount
      symm
      apply Finset.card_equiv (dartEquiv h)
      intro e
      simp only [ConstraintGraph.mem_rejectedDarts, edgeSatisfied_pad_equiv]
    _ = (baseGraph table).rejectionCount (fun v => labeling (v.castLE h)) := by
      simpa only [sumGraph, vertexEquiv_inl] using
        VertexPadding.pad_rejectionCount (baseGraph table) rfl (m - n)
          (fun v => labeling (vertexEquiv h v))

/-- A particular padded labeling satisfies exactly when its old restriction does. -/
theorem pad_labeling_satisfies_iff (table : Table n d) (h : n ≤ m)
    (labeling : Fin m → Label) :
    (∀ e, (baseGraph (pad table h)).edgeSatisfied labeling e = true) ↔
      ∀ e, (baseGraph table).edgeSatisfied (fun v => labeling (v.castLE h)) e = true := by
  constructor
  · intro hs e
    simpa only [edgeSatisfied_pad_old] using hs (e.1.castLE h, e.2)
  · intro hs e
    obtain ⟨v, hv⟩ := (vertexEquiv h).surjective e.1
    have he : e = (vertexEquiv h v, e.2) := Prod.ext hv.symm rfl
    rw [he]
    cases v with
    | inl v => simpa only [vertexEquiv_inl, edgeSatisfied_pad_old] using hs (v, e.2)
    | inr v => exact edgeSatisfied_pad_new table h labeling v e.2

/-- A computable extension uses label zero on every dummy vertex. -/
def extendLabeling (h : n ≤ m) (labeling : Fin n → Label) : Fin m → Label :=
  fun v => Sum.elim labeling (fun _ => 0) ((vertexEquiv h).symm v)

@[simp] theorem extendLabeling_old (h : n ≤ m) (labeling : Fin n → Label) (v : Fin n) :
    extendLabeling h labeling (v.castLE h) = labeling v := by
  simp only [extendLabeling, vertexEquiv_symm_old, Sum.elim_inl]

theorem pad_satisfiable_iff (table : Table n d) (h : n ≤ m) :
    (baseGraph (pad table h)).Satisfiable ↔ (baseGraph table).Satisfiable := by
  constructor
  · rintro ⟨labeling, hs⟩
    exact ⟨fun v => labeling (v.castLE h), (pad_labeling_satisfies_iff table h labeling).1 hs⟩
  · rintro ⟨labeling, hs⟩
    refine ⟨extendLabeling h labeling, (pad_labeling_satisfies_iff table h _).2 ?_⟩
    simpa only [extendLabeling_old] using hs

end UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PreprocessingRegularWords
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Complete serialization of the actual regularized table

Each global vertex emits its internal ports in increasing order, then its
inherited port. Original darts are the first global vertices. Dummy vertices
follow in increasing owner and local-dummy order. These are identities for the
actual stored rows and existing codec, with arbitrary actual cloud tables.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords

open DegreeReplacement PreprocessingCloudIndex PreprocessingRegularTables Complexity
open scoped BigOperators

variable (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
variable (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)

def dummyVertexBits (v : Fin t.vertices) (j : Fin (padding v)) : List Bool :=
  vertexBits t padding tables (.inr ⟨v, j⟩)

/-- The inherited original row keeps the complete input predicate. -/
theorem inherited_original_words (e : Fin t.darts) :
    GraphTables.rowWords (actualRow t padding tables (.inl e) (.inr ())) =
      [e.val, (q + 1) * t.rows[e].reverseIndex.val + q] ++
        GraphTables.relationWords t.rows[e].relation := by
  simp only [GraphTables.rowWords, actualRow_tail, vertexOrder_original,
    inherited_original_reverse, inherited_original_relation]

/-- The inherited dummy row is an always-accepting self-loop. -/
theorem inherited_dummy_words (v : Fin t.vertices) (j : Fin (padding v)) :
    GraphTables.rowWords (actualRow t padding tables (.inr ⟨v, j⟩) (.inr ())) =
      [t.darts + PreprocessingPaddingOffsets.offset padding v.val + j.val,
        (q + 1) * (t.darts + PreprocessingPaddingOffsets.offset padding v.val + j.val) + q] ++
        GraphTables.relationWords MachineDummyRows.trueRelation := by
  simp only [GraphTables.rowWords, actualRow_tail,
    PreprocessingPaddingOffsets.vertexOrder_dummy_val,
    inherited_dummy_reverse, inherited_dummy_relation]

theorem encodeWords_flatMap {α : Type*} (xs : List α) (words : α → List Nat) :
    encodeWords (xs.flatMap words) = xs.flatMap (fun x => encodeWords (words x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

/-- The explicit padding list is the inverse enumeration of its numeric order. -/
theorem paddingOrder_ofFn :
    List.ofFn (paddingOrder padding).symm = paddingList padding := by
  calc
    List.ofFn (paddingOrder padding).symm =
        List.ofFn (fun i : Fin (paddingList padding).length =>
          (paddingOrder padding).symm (Fin.cast (paddingList_length padding) i)) :=
      List.ofFn_congr (paddingList_length padding).symm (paddingOrder padding).symm
    _ = paddingList padding := by
      change List.ofFn (fun i => (paddingList padding).get i) = _
      exact List.ofFn_get _

/-- Any global-vertex payload follows old darts, then the explicit dummy list. -/
theorem vertexOrder_ofFn {α : Type*} (f : Vertex t padding → α) :
    List.ofFn (fun i : Fin (vertexCount t padding) => f ((vertexOrder t padding).symm i)) =
      List.ofFn (fun e : Fin t.darts => f (.inl e)) ++
        (paddingList padding).map (fun z => f (.inr z)) := by
  change List.ofFn (fun i : Fin (t.darts + ∑ v, padding v) =>
    f ((vertexOrder t padding).symm i)) = _
  rw [List.ofFn_add]
  have hold (e : Fin t.darts) :
      (vertexOrder t padding).symm (e.castLE (Nat.le_add_right t.darts (∑ v, padding v))) =
        Sum.inl e := (vertexOrder t padding).symm_apply_apply (Sum.inl e)
  have hnew (i : Fin (∑ v, padding v)) :
      (vertexOrder t padding).symm (i.natAdd t.darts) =
        Sum.inr ((paddingOrder padding).symm i) := by
    apply (vertexOrder t padding).injective
    erw [Equiv.apply_symm_apply]
    change i.natAdd t.darts = Fin.natAdd t.darts
      ((paddingOrder padding) ((paddingOrder padding).symm i))
    rw [Equiv.apply_symm_apply]
  apply congrArg₂ (· ++ ·)
  · exact congrArg List.ofFn (funext (fun i => congrArg f (hold i)))
  · calc
      List.ofFn (fun i : Fin (∑ v, padding v) =>
          f ((vertexOrder t padding).symm (i.natAdd t.darts))) =
          List.ofFn (fun i => f (.inr ((paddingOrder padding).symm i))) :=
        congrArg List.ofFn (funext (fun i => congrArg f (hnew i)))
      _ = (List.ofFn (paddingOrder padding).symm).map (fun z => f (.inr z)) :=
        (List.map_ofFn (f := (paddingOrder padding).symm) (g := fun z => f (.inr z))).symm
      _ = _ := by rw [paddingOrder_ofFn]

/-- The stored dummy list uses exactly the nested owner/local-index loop order. -/
theorem paddingList_flatMap {α : Type*} (f : (Σ v : Fin t.vertices, Fin (padding v)) → List α) :
    (paddingList padding).flatMap f =
      (List.ofFn (fun v : Fin t.vertices =>
        (List.ofFn (fun j : Fin (padding v) => f ⟨v, j⟩)).flatten)).flatten := by
  simp only [paddingList, List.sigma, List.finRange, List.flatMap_def,
    List.map_flatten, List.flatten_flatten, List.map_ofFn, Function.comp_def]

end UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularVertexBlock
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
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

abbrev PortLabel (q : Nat) := Fin q × CoreLabel q

def portEntry (q : Nat) (labels : PortLabel q → Λ) (exit : Option Λ) (k : Nat) :
    Option Λ :=
  if h : k < q then some (labels (⟨k, h⟩, coreEntry q)) else exit

def portInstruction (q : Nat) (positive : 0 < q) (labels : PortLabel q → Λ)
    (exit : Option Λ) (l : PortLabel q) :
    TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q) :=
  coreInstruction q positive l.1 (fun s => labels (l.1, s))
    (portEntry q labels exit (l.1.val + 1)) l.2

def rowBits (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) : List Bool :=
  encodeWords (GraphTables.rowWords (PreprocessingInternalRows.row t padding tables v x p))

def portSteps (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PaddedCloud t padding v) (outputLength : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => portSteps t padding tables v x outputLength k +
      if h : k < q then coreSteps t padding tables v x ⟨k, h⟩
        (outputLength + (portBits (rowBits t padding tables v x) k).length) else 0

def originalTapes : MachineRegularOriginalClean.Tape → CoreTape :=
  ![1, 0, 10, 11, 12, 9, 24, 25, 26, 8]

def originalView : CoreTape → Option MachineRegularOriginalClean.Tape :=
  ![some 1, some 0, none, none, none, none, none, none, some 9, some 5,
    some 2, some 3, some 4, none, none, none, none, none, none, none,
    none, none, none, none, some 6, some 7, some 8]

theorem originalView_left (k : MachineRegularOriginalClean.Tape) :
    originalView (originalTapes k) = some k := by fin_cases k <;> rfl

theorem originalView_right (j : CoreTape) (k : MachineRegularOriginalClean.Tape)
    (h : originalView j = some k) : originalTapes k = j := by
  fin_cases j <;> simp [originalView] at h
  all_goals subst k; rfl

def originalCoreInstruction (q : Nat) (labels : MachineRegularOriginalClean.Label → Λ)
    (exit : Option Λ) (l : MachineRegularOriginalClean.Label) :
    TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q) :=
  MachineCloudPadding.Placement.statement originalTapes labels exit
    (MachineStateEquiv.statement (originalStateEquiv σ q)
      (MachineRegularOriginalClean.instruction q id none l))

theorem originalMemory_input (t : GraphTables.Table) (e : Fin t.darts) (output : List Bool) :
    MachineRegularOriginalClean.Input t e (originalMemory (GraphTables.tableBits t) e.val output) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩

theorem originalMemory_update (graph : List Bool) (x : Nat) (output output' : List Bool) :
    Function.update (originalMemory graph x output) (9 : MachineRegularOriginalClean.Tape) output' =
      originalMemory graph x output' := by funext j; fin_cases j <;> rfl

theorem originalFrame (graph : List Bool) (x v i k o m : Nat) (rotor output output' : List Bool) :
    MachineCloudPadding.Placement.tapes originalView (originalMemory graph x output')
      (coreMemory graph x v i k o m rotor output [] [] [] [] [] []) =
      coreMemory graph x v i k o m rotor output' [] [] [] [] [] [] := by
  funext j; fin_cases j <;> rfl

def dummyTapes : MachineRegularDummyRow.Tape → CoreTape := ![1, 24, 25, 9, 8, 26]

def dummyView : CoreTape → Option MachineRegularDummyRow.Tape :=
  ![none, some 0, none, none, none, none, none, none, some 4, some 3,
    none, none, none, none, none, none, none, none, none, none,
    none, none, none, none, some 1, some 2, some 5]

theorem dummyView_left (k : MachineRegularDummyRow.Tape) :
    dummyView (dummyTapes k) = some k := by fin_cases k <;> rfl

theorem dummyView_right (j : CoreTape) (k : MachineRegularDummyRow.Tape)
    (h : dummyView j = some k) : dummyTapes k = j := by
  fin_cases j <;> simp [dummyView] at h
  all_goals subst k; rfl

def dummyCoreInstruction (q : Nat) (labels : MachineRegularDummyRow.Label → Λ)
    (exit : Option Λ) (l : MachineRegularDummyRow.Label) :
    TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q) :=
  MachineCloudPadding.Placement.statement dummyTapes labels exit
    (MachineRegularDummyRow.instruction q id none l)

theorem dummyMemory_update (x : Nat) (output output' : List Bool) :
    Function.update (MachineRegularDummyRow.memory x output)
      (4 : MachineRegularDummyRow.Tape) output' = MachineRegularDummyRow.memory x output' := by
  funext j; fin_cases j <;> rfl

theorem dummyFrame (graph : List Bool) (x v i k o m : Nat) (rotor output output' : List Bool) :
    MachineCloudPadding.Placement.tapes dummyView (MachineRegularDummyRow.memory x output')
      (coreMemory graph x v i k o m rotor output [] [] [] [] [] []) =
      coreMemory graph x v i k o m rotor output' [] [] [] [] [] [] := by
  funext j; fin_cases j <;> rfl

inductive Label (q : Nat)
  | originalPort (l : PortLabel q)
  | dummyPort (l : PortLabel q)
  | original (l : MachineRegularOriginalClean.Label)
  | dummy (l : MachineRegularDummyRow.Label)
  deriving DecidableEq, Fintype

def originalEntry (q : Nat) (positive : 0 < q) : Label q :=
  .originalPort (⟨0, positive⟩, coreEntry q)

def dummyEntry (q : Nat) (positive : 0 < q) : Label q :=
  .dummyPort (⟨0, positive⟩, coreEntry q)

def instruction (q : Nat) (positive : 0 < q) (labels : Label q → Λ) (exit : Option Λ) :
    Label q → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q)
  | .originalPort l => portInstruction q positive (fun p => labels (.originalPort p))
      (some (labels (.original (.row (.lookup .seed))))) l
  | .dummyPort l => portInstruction q positive (fun p => labels (.dummyPort p))
      (some (labels (.dummy (.affine .seed)))) l
  | .original l => originalCoreInstruction q (fun s => labels (.original s)) exit l
  | .dummy l => dummyCoreInstruction q (fun s => labels (.dummy s)) exit l

def originalRowSteps (q : Nat) (t : GraphTables.Table) (e : Fin t.darts) (outputLength : Nat) : Nat :=
  MachineRegularOriginalClean.steps q t e
    (originalMemory (GraphTables.tableBits t) e.val (List.replicate outputLength false))

theorem originalRowSteps_eq (q : Nat) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    MachineRegularOriginalClean.steps q t e (originalMemory (GraphTables.tableBits t) e.val output) =
      originalRowSteps q t e output.length := by
  unfold originalRowSteps MachineRegularOriginalClean.steps
  rw [MachineRegularOriginalClean.cleanupSteps_eq q t e _ (originalMemory_input t e output),
    MachineRegularOriginalClean.cleanupSteps_eq q t e _
      (originalMemory_input t e (List.replicate output.length false))]
  simp only [MachineRegularOriginalRow.steps, MachineRegularOriginalRow.rowSteps,
    originalMemory, Matrix.cons_val, List.length_replicate]

theorem encodeWords_flatMap {A : Type*} (xs : List A) (words : A → List Nat) :
    encodeWords (xs.flatMap words) = xs.flatMap (fun x => encodeWords (words x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem encodeWords_pair (a b : Nat) (rest : List Nat) :
    encodeWords ([a, b] ++ rest) = encodeWord a ++ (encodeWord b ++ encodeWords rest) := rfl

theorem vertexBits_split (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PaddedCloud t padding v) :
    PreprocessingRegularWords.vertexBits t padding tables x.val =
      (List.ofFn (rowBits t padding tables v x)).flatten ++
        encodeWords (GraphTables.rowWords
          (PreprocessingRegularWords.actualRow t padding tables x.val (.inr ()))) := by
  unfold PreprocessingRegularWords.vertexBits PreprocessingRegularWords.vertexRows
  rw [List.flatMap_append, encodeWords_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [encodeWords_flatMap, List.flatMap_def, List.map_ofFn]
  rfl

def originalSteps (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (e : Fin t.darts) (outputLength : Nat) : Nat :=
  portSteps t padding tables t.rows[e].tail (oldCloud t padding e) outputLength q +
    originalRowSteps q t e (outputLength +
      (List.ofFn (rowBits t padding tables t.rows[e].tail (oldCloud t padding e))).flatten.length)

def dummySteps (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (j : Fin (padding v)) (outputLength : Nat) : Nat :=
  portSteps t padding tables v (paddedNew t padding v j) outputLength q +
    MachineRegularDummyRow.timeBound q (vertexOrder t padding (.inr ⟨v, j⟩)).val
      (outputLength + (List.ofFn (rowBits t padding tables v (paddedNew t padding v j))).flatten.length)

theorem rowBits_length_le (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (rowBits t padding tables v x p).length ≤ rowSizeBound q (vertexCount t padding) :=
  GraphTables.rowBits_length_le _

theorem allRowBits_length_le (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PaddedCloud t padding v) :
    (List.ofFn (rowBits t padding tables v x)).flatten.length ≤
      q * rowSizeBound q (vertexCount t padding) := by
  rw [← portBits_all]
  exact portBits_length_le _ _ (rowBits_length_le t padding tables v x) q

theorem portSteps_le (q : Nat) (positive : 0 < q) (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PaddedCloud t padding v) (outputLength : Nat) (n : Nat) (hn : n ≤ q) :
    portSteps t padding tables v x outputLength n ≤
      n * coreTimeBound q (GraphTables.tableBits t).length
        (encodeWords (ExpanderTableWords.rotationWords (tables v))).length
        (vertexOrder t padding x.val).val v.val (paddedCloudRank t padding v x).val
        (cloudSize t v) (PreprocessingPaddingOffsets.offset padding v.val) t.darts
        (outputLength + q * rowSizeBound q (vertexCount t padding)) := by
  induction n with
  | zero => simp only [portSteps, Nat.zero_mul, le_refl]
  | succ n ih =>
    have h : n < q := by omega
    have first := ih (by omega)
    have second := coreSteps_le q positive t padding tables v x ⟨n, h⟩
      (outputLength + (portBits (rowBits t padding tables v x) n).length)
    have hlen := portBits_length_le (rowBits t padding tables v x)
      (rowSizeBound q (vertexCount t padding)) (rowBits_length_le t padding tables v x) n
    have hmul := Nat.mul_le_mul_right (rowSizeBound q (vertexCount t padding)) (Nat.le_of_lt h)
    have hcost : coreSteps t padding tables v x ⟨n, h⟩
        (outputLength + (portBits (rowBits t padding tables v x) n).length) ≤
        coreTimeBound q (GraphTables.tableBits t).length
          (encodeWords (ExpanderTableWords.rotationWords (tables v))).length
          (vertexOrder t padding x.val).val v.val (paddedCloudRank t padding v x).val
          (cloudSize t v) (PreprocessingPaddingOffsets.offset padding v.val) t.darts
          (outputLength + q * rowSizeBound q (vertexCount t padding)) := by
      unfold coreTimeBound at second ⊢
      omega
    rw [portSteps, dite_eq_left h, Nat.succ_mul]
    exact Nat.add_le_add first hcost

theorem originalSteps_le (q : Nat) (positive : 0 < q) (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (e : Fin t.darts) (outputLength : Nat) :
    originalSteps t padding tables e outputLength ≤
      originalTimeBound q (GraphTables.tableBits t).length
        (encodeWords (ExpanderTableWords.rotationWords (tables t.rows[e].tail))).length
        e.val t.rows[e].tail.val (paddedCloudRank t padding t.rows[e].tail (oldCloud t padding e)).val
        (cloudSize t t.rows[e].tail) (PreprocessingPaddingOffsets.offset padding t.rows[e].tail.val)
        t.darts outputLength (vertexCount t padding) := by
  let v := t.rows[e].tail
  let x := oldCloud t padding e
  let extra := (List.ofFn (rowBits t padding tables v x)).flatten.length
  have hp := portSteps_le q positive t padding tables v x outputLength q le_rfl
  have hi := MachineRegularOriginalClean.steps_le q t e
    (originalMemory (GraphTables.tableBits t) e.val (List.replicate (outputLength + extra) false))
    (originalMemory_input t e (List.replicate (outputLength + extra) false))
  have hl := allRowBits_length_le t padding tables v x
  change originalRowSteps q t e (outputLength + extra) ≤
    MachineRegularOriginalClean.timeBound q (GraphTables.tableBits t).length
      (List.replicate (outputLength + extra) false).length at hi
  rw [List.length_replicate] at hi
  change portSteps t padding tables v x outputLength q +
    originalRowSteps q t e (outputLength + extra) ≤ _
  unfold originalTimeBound portTimeBound MachineRegularOriginalClean.timeBound at *
  have hx : (vertexOrder t padding x.val).val = e.val := rfl
  rw [hx] at hp
  dsimp only [v, x, extra] at *
  omega

theorem dummySteps_le (q : Nat) (positive : 0 < q) (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (j : Fin (padding v)) (outputLength : Nat) :
    dummySteps t padding tables v j outputLength ≤
      dummyTimeBound q (GraphTables.tableBits t).length
        (encodeWords (ExpanderTableWords.rotationWords (tables v))).length
        (vertexOrder t padding (.inr ⟨v, j⟩)).val v.val
        (paddedCloudRank t padding v (paddedNew t padding v j)).val
        (cloudSize t v) (PreprocessingPaddingOffsets.offset padding v.val)
        t.darts outputLength (vertexCount t padding) := by
  have hp := portSteps_le q positive t padding tables v (paddedNew t padding v j) outputLength q le_rfl
  have hl := allRowBits_length_le t padding tables v (paddedNew t padding v j)
  unfold dummySteps dummyTimeBound portTimeBound MachineRegularDummyRow.timeBound
  have hx : (paddedNew t padding v j).val = Sum.inr ⟨v, j⟩ := rfl
  rw [hx] at hp
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularVertexBlock

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PreprocessingOverlayTables
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables

open PoweringWalks

theorem constraintGraph_ext {V E A : Type*} {G H : ConstraintGraph V E A}
    (hreverse : ∀ e, G.reverse e = H.reverse e)
    (htail : ∀ e, G.tail e = H.tail e)
    (haccepts : ∀ e a b, G.accepts e a b = H.accepts e a b) : G = H := by
  rcases G with ⟨r, hi, t, p, hp⟩
  rcases H with ⟨r', hi', t', p', hp'⟩
  have hr : r = r' := Equiv.ext hreverse
  cases hr
  have ht : t = t' := funext htail
  cases ht
  have ha : p = p' := funext fun e => funext fun a => funext fun b => haccepts e a b
  cases ha
  rfl

theorem baseGraph_materialize {n d : Nat} {D : Type*}
    (G : ConstraintGraph (Fin n) (Fin n × D) PortTables.Label)
    (ports : D ≃ Fin d) (htail : G.tail = Prod.fst) :
    PortTables.baseGraph (materialize G ports) =
      G.reindex (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) ports) (Equiv.refl _) := by
  apply constraintGraph_ext
  · intro x
    rw [PortTables.baseGraph_reverse, rotation_materialize]
    rfl
  · intro x
    change x.1 = G.tail (x.1, ports.symm x.2)
    rw [htail]
  · intro x a b
    rw [PortTables.baseGraph_accepts, accepts_materialize]
    rfl

theorem overlay_semantics {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) :
    PortTables.baseGraph (overlay G H) =
      (Overlay.constraintGraph (PortTables.baseGraph G) (ExpanderTables.graph H)).reindex
        (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) (overlayPorts d e))
        (Equiv.refl _) :=
  baseGraph_materialize _ _ rfl

theorem lazy_semantics {n d : Nat} (G : PortTables.Table n d) :
    PortTables.baseGraph (lazy G) =
      (LazyConstraint.constraintGraph (PortTables.baseGraph G)).reindex
        (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) (lazyPorts d)) (Equiv.refl _) :=
  baseGraph_materialize _ _ rfl

end UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PreprocessingTableSpectral
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
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

/-- Materialization retains exactly the explicitly reindexed rotation. -/
theorem materialize_portGraph {n d : Nat} {D : Type*}
    (G : ConstraintGraph (Fin n) (Fin n × D) PortTables.Label)
    (ports : D ≃ Fin d) :
    PortTables.portGraph (PreprocessingOverlayTables.materialize G ports) =
      GraphTransport.reindex (Overlay.originalPortGraph G) (Equiv.refl _) ports := by
  apply portGraph_ext
  intro x
  rw [PortTables.portGraph_rot, PreprocessingOverlayTables.rotation_materialize]
  rfl

/-- The stored lazy graph is exactly the Boolean-flag lazy graph, with the
declared false-first port encoding. -/
theorem lazy_portGraph {n d : Nat} (G : PortTables.Table n d) :
    PortTables.portGraph (PreprocessingOverlayTables.lazy G) =
      GraphTransport.reindex (lazyGraph (PortTables.portGraph G))
        (Equiv.refl _) (PreprocessingOverlayTables.lazyPorts d) := by
  unfold PreprocessingOverlayTables.lazy
  rw [materialize_portGraph]
  rfl

end UniqueGamesTheorem.Foundations.PCP.PreprocessingTableSpectral

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PoweringPortReindexLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

def walkEquiv (ports : D ≃ E) (n : Nat) : Walk V D n ≃ Walk V E n :=
  Equiv.prodCongr (Equiv.refl V) (wordEquiv ports n)

variable (G : PortGraph V D) (H : PortGraph V E) (ports : D ≃ E)
variable (rotation : ∀ v d, H.rot (v, ports d) =
  ((G.rot (v,d)).1, ports (G.rot (v,d)).2))

include rotation

theorem wordEnd_map (n : Nat) (v : V) (p : Fin n → D) :
    wordEnd H n v (wordEquiv ports n p) = wordEnd G n v p := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    simp only [wordEnd, next, wordEquiv, Equiv.coe_fn_mk, rotation]
    exact ih _ _

theorem endpoint_map (n : Nat) (w : Walk V D n) :
    endpoint H (walkEquiv ports n w) = endpoint G w :=
  wordEnd_map G H ports rotation n w.1 w.2

theorem reach_iff (t : Nat) (v u : V) :
    (∃ n, n ≤ t ∧ ∃ p : Fin n → D, wordEnd G n v p = u) ↔
    (∃ n, n ≤ t ∧ ∃ p : Fin n → E, wordEnd H n v p = u) := by
  constructor
  · rintro ⟨n,hn,p,hp⟩
    exact ⟨n,hn,wordEquiv ports n p,(wordEnd_map G H ports rotation n v p).trans hp⟩
  · rintro ⟨n,hn,p,hp⟩
    refine ⟨n,hn,(wordEquiv ports n).symm p,?_⟩
    rw [← wordEnd_map G H ports rotation, Equiv.apply_symm_apply]
    exact hp

def ballEquiv (t : Nat) (v : V) : Ball G t v ≃ Ball H t v where
  toFun u := ⟨u.val,(reach_iff G H ports rotation t v u.val).mp u.property⟩
  invFun u := ⟨u.val,(reach_iff G H ports rotation t v u.val).mpr u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem wordToBall_map (t : Nat) (v : V) (w : PortWords D t) :
    wordToBall H t v (addressEquiv ports t w) =
      ballEquiv G H ports rotation t v (wordToBall G t v w) := by
  apply Subtype.ext
  exact wordEnd_map G H ports rotation w.1.val v w.2

/-- Use the target selector, including its concrete enumeration choices. -/
def pullSelector {t : Nat} {v : V} (S : AddressSelector H t v) :
    AddressSelector G t v where
  address u := (addressEquiv ports t).symm
    (S.address (ballEquiv G H ports rotation t v u))
  correct u := by
    apply (ballEquiv G H ports rotation t v).injective
    rw [← wordToBall_map, Equiv.apply_symm_apply, S.correct]

theorem decode_pullSelector {t : Nat} {v : V} (S : AddressSelector H t v)
    (a : PaddedLabel E t A) (u : Ball G t v) :
    decode (pullSelector G H ports rotation S) (labelEquiv ports t a) u =
      decode S a (ballEquiv G H ports rotation t v u) := by
  simp [decode, pullSelector, labelEquiv]

theorem decode_transport {t : Nat} (selectors : ∀v, AddressSelector H t v)
    (a : PaddedLabel E t A) {v w : V} (hvw : v = w)
    (u : Ball G t v) (u' : Ball H t w) (hu : u.val = u'.val) :
    decode (pullSelector G H ports rotation (selectors v)) (labelEquiv ports t a) u =
      decode (selectors w) a u' := by
  subst w
  rw [decode_pullSelector]
  congr 1
  exact Subtype.ext hu

theorem advanceTail_map (n : Nat) (w : Walk V D (n+1)) :
    advanceTail H (walkEquiv ports (n+1) w) =
      walkEquiv ports n (advanceTail G w) := by
  apply Prod.ext
  · change (H.rot (w.1, ports (w.2 0))).1 = (G.rot (w.1,w.2 0)).1
    rw [rotation]
  · rfl

theorem edgeAt_map (n : Nat) (w : Walk V D (n+1)) (k : Fin (n+1)) :
    edgeAt H n (walkEquiv ports (n+1) w) k =
      ((edgeAt G n w k).1, ports (edgeAt G n w k).2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    induction k using Fin.cases with
    | zero => rfl
    | succ k =>
      simp only [edgeAt, Fin.cases_succ]
      rw [advanceTail_map G H ports rotation]
      exact ih _ _

variable (accepts : Edge V E → A → A → Bool)

theorem pathAccepts_map (n : Nat) (selectors : ∀v, AddressSelector H (n+1) v)
    (w : Walk V D (n+1)) (a b : PaddedLabel E (n+1) A) :
    pathAccepts G (pullAccepts ports accepts) n
      (fun v => pullSelector G H ports rotation (selectors v)) w
      (labelEquiv ports (n+1) a) (labelEquiv ports (n+1) b) =
    pathAccepts H accepts n selectors (walkEquiv ports (n+1) w) a b := by
  classical
  unfold pathAccepts
  congr 1
  apply propext
  apply forall_congr'
  intro k
  have ht := decode_transport G H ports rotation selectors a rfl
    (tailFromStart G n w k) (tailFromStart H n (walkEquiv ports (n+1) w) k)
    (congrArg Prod.fst (edgeAt_map G H ports rotation n w k)).symm
  have hh := decode_transport G H ports rotation selectors b
    (endpoint_map G H ports rotation (n+1) w).symm
    (headFromEnd G n w k) (headFromEnd H n (walkEquiv ports (n+1) w) k)
    (by
      change (G.rot (edgeAt G n w k)).1 =
        (H.rot (edgeAt H n (walkEquiv ports (n+1) w) k)).1
      rw [edgeAt_map G H ports rotation, rotation])
  rw [ht, hh]
  simp only [pullAccepts, edgeAt_map G H ports rotation]
  rfl

def dartEquiv (n : Nat) : Dart V D n ≃ Dart V E n :=
  Equiv.prodCongr (Equiv.refl Bool) (walkEquiv ports (n+1))

theorem edgeSatisfied_map (n : Nat) (selectors : ∀v, AddressSelector H (n+1) v)
    (labels : V → PaddedLabel E (n+1) A) (e : Dart V D n) :
    (poweredGraph G (pullAccepts ports accepts) n
      (fun v => pullSelector G H ports rotation (selectors v))).edgeSatisfied
        (fun v => labelEquiv ports (n+1) (labels v)) e =
    (poweredGraph H accepts n selectors).edgeSatisfied labels (dartEquiv ports n e) := by
  rcases e with ⟨direction,w⟩
  rw [poweredGraph_edgeSatisfied]
  change _ = (poweredGraph H accepts n selectors).edgeSatisfied labels
    (direction, walkEquiv ports (n+1) w)
  rw [poweredGraph_edgeSatisfied, endpoint_map G H ports rotation]
  exact pathAccepts_map G H ports rotation accepts n selectors w _ _

theorem rejectionCount_map [Fintype V] [Fintype D] [Fintype E]
    (n : Nat) (selectors : ∀v, AddressSelector H (n+1) v)
    (labels : V → PaddedLabel E (n+1) A) :
    (poweredGraph G (pullAccepts ports accepts) n
      (fun v => pullSelector G H ports rotation (selectors v))).rejectionCount
        (fun v => labelEquiv ports (n+1) (labels v)) =
    (poweredGraph H accepts n selectors).rejectionCount labels := by
  classical
  unfold ConstraintGraph.rejectionCount
  apply Finset.card_bij (fun e _ => dartEquiv ports n e)
  · intro e he
    rw [ConstraintGraph.mem_rejectedDarts, ← edgeSatisfied_map G H ports rotation]
    exact (ConstraintGraph.mem_rejectedDarts _ _ _).mp he
  · intro e _ f _ h
    exact (dartEquiv ports n).injective h
  · intro e he
    refine ⟨(dartEquiv ports n).symm e, ?_, (dartEquiv ports n).apply_symm_apply e⟩
    rw [ConstraintGraph.mem_rejectedDarts, edgeSatisfied_map G H ports rotation,
      Equiv.apply_symm_apply]
    exact (ConstraintGraph.mem_rejectedDarts _ _ _).mp he

theorem pullReverse
    (reverse_accepts : ∀ e a b, accepts (H.rot e) b a = accepts e a b)
    (e : Edge V D) (a b : A) :
    pullAccepts ports accepts (G.rot e) b a = pullAccepts ports accepts e a b := by
  simpa only [pullAccepts, rotation] using reverse_accepts (e.1,ports e.2) a b

theorem base_edgeSatisfied_map
    (reverse_accepts : ∀ e a b, accepts (H.rot e) b a = accepts e a b)
    (assignment : V → A) (e : Edge V D) :
    (baseGraph G (pullAccepts ports accepts)
      (pullReverse G H ports rotation accepts reverse_accepts)).edgeSatisfied assignment e =
    (baseGraph H accepts reverse_accepts).edgeSatisfied assignment (e.1,ports e.2) := by
  change accepts (e.1,ports e.2) (assignment e.1) (assignment (G.rot e).1) =
    accepts (e.1,ports e.2) (assignment e.1) (assignment (H.rot (e.1,ports e.2)).1)
  rw [rotation]

theorem base_rejectionCount_map [Fintype V] [Fintype D] [Fintype E]
    (reverse_accepts : ∀ e a b, accepts (H.rot e) b a = accepts e a b)
    (assignment : V → A) :
    (baseGraph G (pullAccepts ports accepts)
      (pullReverse G H ports rotation accepts reverse_accepts)).rejectionCount assignment =
    (baseGraph H accepts reverse_accepts).rejectionCount assignment := by
  classical
  let e : Edge V D ≃ Edge V E := Equiv.prodCongr (Equiv.refl V) ports
  have edgeEq (x : Edge V D) :=
    base_edgeSatisfied_map G H ports rotation accepts reverse_accepts assignment x
  unfold ConstraintGraph.rejectionCount
  apply Finset.card_bij (fun x _ => e x)
  · intro x hx
    rw [ConstraintGraph.mem_rejectedDarts]
    change (baseGraph H accepts reverse_accepts).edgeSatisfied assignment (x.1,ports x.2) = false
    rw [← edgeEq]
    exact (ConstraintGraph.mem_rejectedDarts _ _ _).mp hx
  · intro x _ y _ h
    exact e.injective h
  · intro y hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [ConstraintGraph.mem_rejectedDarts, edgeEq]
    change (baseGraph H accepts reverse_accepts).edgeSatisfied assignment (e (e.symm y)) = false
    rw [e.apply_symm_apply]
    exact (ConstraintGraph.mem_rejectedDarts _ _ _).mp hy

omit rotation in
/-- The generic lazy-graph gap survives a genuine rotation-preserving port
change and the target's chosen selectors, for every raw target labeling. -/
theorem uniform_count_gap
    [Fintype V] [Fintype D] [Fintype E] [Nonempty V] [Nonempty D]
    [Fintype A] [Nonempty A]
    (G : PortGraph V D) (H : PortGraph V E) (ports : (Bool × D) ≃ E)
    (rotation : ∀ v d, H.rot (v, ports d) =
      (((lazyGraph G).rot (v,d)).1, ports ((lazyGraph G).rot (v,d)).2))
    (lambda : ℝ) (certificate : SpectralCertificate (lazyGraph G) lambda)
    (accepts : Edge V E → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (H.rot e) b a = accepts e a b)
    (M : Nat) (hM : 1 ≤ M)
    (selectors : ∀v, AddressSelector H (2*center (Fintype.card A) M+1) v)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hgap : ∀ assignment : V → A,
      epsilon * (Fintype.card (Edge V E) : ℝ) ≤
        ((baseGraph H accepts reverse_accepts).rejectionCount assignment : ℝ))
    (labels : V → PaddedLabel E (2*center (Fintype.card A) M+1) A) :
    (gain (Fintype.card A) M lambda *
      min epsilon (1 / ((2*center (Fintype.card A) M+1 : Nat) : ℝ))) *
        (Fintype.card (Dart V E (2*center (Fintype.card A) M)) : ℝ) ≤
      ((poweredGraph H accepts (2*center (Fintype.card A) M) selectors).rejectionCount labels : ℝ) := by
  have hbase : ∀ assignment : V → A,
      epsilon * (Fintype.card (Edge V (Bool × D)) : ℝ) ≤
      ((baseGraph (lazyGraph G) (pullAccepts ports accepts)
        (pullReverse (lazyGraph G) H ports rotation accepts reverse_accepts)).rejectionCount assignment : ℝ) := by
    intro assignment
    rw [base_rejectionCount_map (lazyGraph G) H ports rotation,
      Fintype.card_congr (Equiv.prodCongr (Equiv.refl V) ports)]
    exact hgap assignment
  have bound := PoweringGap.uniform_count_gap G lambda certificate
    (pullAccepts ports accepts)
    (pullReverse (lazyGraph G) H ports rotation accepts reverse_accepts) M hM
    (fun v => pullSelector (lazyGraph G) H ports rotation (selectors v))
    epsilon hepsilon hbase (fun v => labelEquiv ports _ (labels v))
  rw [rejectionCount_map (lazyGraph G) H ports rotation,
    Fintype.card_congr (dartEquiv (V := V) ports (2*center (Fintype.card A) M))] at bound
  exact bound

omit rotation in
/-- Gap bound for the actual numbered power table built from a lazified port
table. The spectral certificate is on the genuine Boolean-flag lazy graph. -/
theorem lazy_table_uniform_count_gap {vertices d : Nat}
    (input : PortTables.Table vertices d) (hv : 0 < vertices) (hd : 0 < d)
    (lambda : ℝ)
    (certificate : SpectralCertificate (lazyGraph (PortTables.portGraph input)) lambda)
    (M : Nat) (hM : 1 ≤ M) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hgap : ∀ assignment : Fin vertices → Fin 64,
      epsilon * (Fintype.card (Fin vertices × Fin (2*d)) : ℝ) ≤
        ((PortTables.baseGraph (PreprocessingOverlayTables.lazy input)).rejectionCount assignment : ℝ)) :
    ∀ labels : PoweringTableSemantics.EncodedLabeling vertices (2*d) (2*center 64 M),
    (gain 64 M lambda * min epsilon (1 / ((2*center 64 M+1 : Nat) : ℝ))) *
      ((PoweringTables.table (PreprocessingOverlayTables.lazy input) (2*center 64 M)).darts : ℝ) ≤
      ((GenericGraphTables.semantics
        (PoweringTables.table (PreprocessingOverlayTables.lazy input) (2*center 64 M))).rejectionCount labels : ℝ) := by
  let : Nonempty (Fin vertices) := ⟨⟨0,hv⟩⟩
  let : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  apply PoweringTableSemantics.uniform_count_gap
  intro labels
  have hrot : ∀ v p,
      (PortTables.portGraph (PreprocessingOverlayTables.lazy input)).rot
          (v, PreprocessingOverlayTables.lazyPorts d p) =
        (((lazyGraph (PortTables.portGraph input)).rot (v,p)).1,
          PreprocessingOverlayTables.lazyPorts d
            ((lazyGraph (PortTables.portGraph input)).rot (v,p)).2) := by
    intro v p
    rw [PreprocessingTableSpectral.lazy_portGraph]
    exact GraphTransport.reindex_rot _ (Equiv.refl _) _ v p
  have bound := uniform_count_gap (PortTables.portGraph input)
      (PortTables.portGraph (PreprocessingOverlayTables.lazy input))
      (PreprocessingOverlayTables.lazyPorts d) hrot lambda certificate
      (PortTables.accepts (PreprocessingOverlayTables.lazy input))
      (PortTables.accepts_rotation (PreprocessingOverlayTables.lazy input)) M hM
      (PoweringAddresses.finitePortSelector
        (PortTables.portGraph (PreprocessingOverlayTables.lazy input)) _) epsilon hepsilon
      hgap
  simp only [PortTables.Label, GraphTables.Label, Fintype.card_fin] at bound
  exact bound labels

omit rotation in
/-- The same exact table bound with a separately stored walk parameter. Its
proved equality may be used without evaluating a huge closed alphabet size. -/
theorem lazy_table_uniform_count_gap_at {vertices d : Nat}
    (input : PortTables.Table vertices d) (hv : 0 < vertices) (hd : 0 < d)
    (lambda : ℝ)
    (certificate : SpectralCertificate (lazyGraph (PortTables.portGraph input)) lambda)
    (M : Nat) (hM : 1 ≤ M) (n : Nat) (hn : n = 2*center 64 M)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hgap : ∀ assignment : Fin vertices → Fin 64,
      epsilon * (Fintype.card (Fin vertices × Fin (2*d)) : ℝ) ≤
        ((PortTables.baseGraph (PreprocessingOverlayTables.lazy input)).rejectionCount
          assignment : ℝ)) :
    ∀ labels : PoweringTableSemantics.EncodedLabeling vertices (2*d) n,
    (gain 64 M lambda * min epsilon (1 / ((n+1 : Nat) : ℝ))) *
      ((PoweringTables.table (PreprocessingOverlayTables.lazy input) n).darts : ℝ) ≤
      ((GenericGraphTables.semantics
        (PoweringTables.table (PreprocessingOverlayTables.lazy input) n)).rejectionCount
          labels : ℝ) := by
  subst n
  exact lazy_table_uniform_count_gap input hv hd lambda certificate M hM
    epsilon hepsilon hgap

end UniqueGamesTheorem.Foundations.PCP.PoweringPortReindex

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PreprocessingRegularSoundness
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

/-- Erasing a proof-equal table size preserves its exact spectral certificate. -/
theorem resizeTable_certificate {n m q : Nat} (h : n = m)
    (table : ExpanderTables.Table n q) (lambda : ℝ)
    (certificate : SpectralCertificate (ExpanderTables.graph table) lambda) :
    SpectralCertificate (ExpanderTables.graph (resizeTable h table)) lambda := by
  cases h
  exact certificate

theorem familyCloudTable_certificate_of_pos (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) (v : Fin t.vertices)
    (hk : 0 < PreprocessingCloudIndex.cloudSize t v) :
    SpectralCertificate (ExpanderTables.graph (familyCloudTable H t v)) (1 / 2 : ℝ) := by
  let : NeZero Expanders.baseDegree := ⟨baseDegree_ne_zero⟩
  unfold familyCloudTable
  rw [dite_eq_right (Nat.ne_of_gt hk)]
  apply resizeTable_certificate
  exact ExpanderTables.family_certificate H certificate _

theorem cloudGraphs_certificate_of_pos (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) (v : Fin t.vertices)
    (hk : 0 < PreprocessingCloudIndex.cloudSize t v) :
    SpectralCertificate (cloudGraphs t (padding t) (familyCloudTable H t) v)
      (1 / 2 : ℝ) := by
  exact GraphTransport.reindex_spectralCertificate _ _ _ _
    (familyCloudTable_certificate_of_pos H certificate t v hk)

/-- The exact finite cut inequality needed to pay for each changed cloud label. -/
theorem cloud_expansion (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) (v : Fin t.vertices)
    (S : Finset (PreprocessingCloudIndex.PaddedCloud t (padding t) v))
    (hsmall : S.card ≤
      Fintype.card (PreprocessingCloudIndex.PaddedCloud t (padding t) v) / 2) :
    2 * S.card ≤ (CloudRounding.directedCut
      (fun ed => ((cloudGraphs t (padding t) (familyCloudTable H t) v).rot ed).1) S).card := by
  by_cases hk : PreprocessingCloudIndex.cloudSize t v = 0
  · have hzero : Fintype.card (PreprocessingCloudIndex.PaddedCloud t (padding t) v) = 0 := by
      rw [PreprocessingCloudIndex.card_paddedCloud, cloudSize_add_padding, hk]
      rfl
    have hs : S.card = 0 := by omega
    simp only [hs, mul_zero, Nat.zero_le]
  · exact SpectralCut.cut_card_ge_twice
      (cloudGraphs t (padding t) (familyCloudTable H t) v)
      (cloudGraphs_certificate_of_pos H certificate t v (Nat.pos_of_ne_zero hk))
      (by simpa only [Fintype.card_fin] using internalDegree_ge_eight) S (by
        change 2 * S.card ≤
          Fintype.card (PreprocessingCloudIndex.PaddedCloud t (padding t) v)
        omega)

/-- Decode the actual numbered output labels by majority in each padded cloud. -/
noncomputable def roundLabels (t : GraphTables.Table)
    (labels : Fin (vertexCount t (padding t)) → GraphTables.Label) :
    Fin t.vertices → GraphTables.Label :=
  CloudRounding.roundLabels
    (paddedGraph (GraphTables.semantics t) (fun v => Fin (padding t v)))
    (fun z => labels (vertexOrder t (padding t) z))

/-- Direct soundness for the generated tables, with no matching-base premise. -/
theorem soundness (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table)
    (labels : Fin (vertexCount t (padding t)) → GraphTables.Label) :
    (GraphTables.semantics t).rejectionCount (roundLabels t labels) ≤
      (PortTables.baseGraph (regularize H t)).rejectionCount labels := by
  rw [regularize, rejectionCount_ofCloudTables]
  exact CloudRounding.padded_replacement_soundness (GraphTables.semantics t)
    (fun v => Fin (padding t v)) (cloudGraphs t (padding t) (familyCloudTable H t))
    (cloud_expansion H certificate t) (fun z => labels (vertexOrder t (padding t) z))

theorem completeness (H : BaseTable) (t : GraphTables.Table)
    (h : (GraphTables.semantics t).Satisfiable) :
    (PortTables.baseGraph (regularize H t)).Satisfiable := by
  obtain ⟨labels, hlabels⟩ := h
  refine ⟨liftedLabel t (padding t) labels, ?_⟩
  intro e
  obtain ⟨z, rfl⟩ :=
    (Equiv.prodCongr (vertexOrder t (padding t)) (portOrder internalDegree)).surjective e
  rcases z with ⟨v, p⟩
  change (PortTables.baseGraph (regularize H t)).edgeSatisfied
    (liftedLabel t (padding t) labels)
    (vertexOrder t (padding t) v, portOrder internalDegree p) = true
  rw [regularize, edgeSatisfied_ofCloudTables]
  simp only [liftedLabel, Equiv.symm_apply_apply]
  have hcomplete := replacement_complete
    (paddedGraph (GraphTables.semantics t) (fun v => Fin (padding t v)))
    (cloudGraphs t (padding t) (familyCloudTable H t)) labels
    (padded_complete (GraphTables.semantics t) (fun v => Fin (padding t v)) labels hlabels)
    (v, p)
  convert hcomplete using 1
  all_goals try with_reducible_and_instances rfl
  rfl

end UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularSoundness

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PreprocessingTablesLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Soundness and expansion of the actual executable preprocessing tables.
The fixed base-table spectral certificate is supplied by the proved expander
existence theorem; no output expansion or output gap is assumed. -/

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingGuarantees

open PoweringWalks SpectralReturn PreprocessingTables
open PreprocessingRegularTables (internalDegree regularize)

variable {n d e : Nat}

theorem overlay_rejectionCount (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (labels : Fin n → GraphTables.Label) :
    (PortTables.baseGraph (PreprocessingOverlayTables.overlay G H)).rejectionCount labels =
      (PortTables.baseGraph G).rejectionCount labels := by
  rw [PreprocessingOverlayTables.overlay_semantics]
  calc
    _ = (Overlay.constraintGraph (PortTables.baseGraph G) (ExpanderTables.graph H)).rejectionCount labels := by
      convert ConstraintGraph.reindex_rejectionCount
        (Overlay.constraintGraph (PortTables.baseGraph G) (ExpanderTables.graph H))
        (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _)
          (PreprocessingOverlayTables.overlayPorts d e)) (Equiv.refl _) labels using 1
      all_goals try with_reducible_and_instances rfl
      rfl
    _ = _ := Overlay.rejectionCount_eq _ _ rfl labels

theorem lazy_rejectionCount (G : PortTables.Table n d)
    (labels : Fin n → GraphTables.Label) :
    (PortTables.baseGraph (PreprocessingOverlayTables.lazy G)).rejectionCount labels =
      (PortTables.baseGraph G).rejectionCount labels := by
  rw [PreprocessingOverlayTables.lazy_semantics]
  calc
    _ = (LazyConstraint.constraintGraph (PortTables.baseGraph G)).rejectionCount labels := by
      convert ConstraintGraph.reindex_rejectionCount
        (LazyConstraint.constraintGraph (PortTables.baseGraph G))
        (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _)
          (PreprocessingOverlayTables.lazyPorts d)) (Equiv.refl _) labels using 1
      all_goals try with_reducible_and_instances rfl
      rfl
    _ = _ := LazyConstraint.rejectionCount_eq _ rfl labels

def restrictedLabel (t : GraphTables.Table)
    (labels : Fin (vertices t) → GraphTables.Label) :
    Fin (regularVertices t) → GraphTables.Label :=
  fun v => labels (v.castLE (PreprocessingLevels.le_paddedSize (regularVertices t)))

theorem rejectionCount_eq_regularized (H : BaseTable) (t : GraphTables.Table)
    (labels : Fin (vertices t) → GraphTables.Label) :
    (PortTables.baseGraph (preprocess H t)).rejectionCount labels =
      (PortTables.baseGraph (regularize H t)).rejectionCount (restrictedLabel t labels) := by
  unfold preprocess PreprocessingTables.degree
  rw [lazy_rejectionCount, overlay_rejectionCount]
  exact PreprocessingPaddingTables.pad_rejectionCount _ _ labels

def roundLabels (t : GraphTables.Table)
    (labels : Fin (vertices t) → GraphTables.Label) : Fin t.vertices → GraphTables.Label :=
  PreprocessingRegularSoundness.roundLabels t (restrictedLabel t labels)

theorem completeness (H : BaseTable) (t : GraphTables.Table)
    (h : (GraphTables.semantics t).Satisfiable) :
    (PortTables.baseGraph (preprocess H t)).Satisfiable := by
  have hp : (PortTables.baseGraph (padded H t)).Satisfiable :=
    (PreprocessingPaddingTables.pad_satisfiable_iff _ _).mpr
      (PreprocessingRegularSoundness.completeness H t h)
  obtain ⟨labels, hlabels⟩ := hp
  refine ⟨labels, ?_⟩
  apply (ConstraintGraph.rejectionCount_eq_zero_iff _ labels).mp
  unfold preprocess PreprocessingTables.degree
  rw [lazy_rejectionCount, overlay_rejectionCount]
  exact (ConstraintGraph.rejectionCount_eq_zero_iff _ labels).mpr hlabels

end UniqueGamesTheorem.Foundations.PCP.PreprocessingGuarantees

end

end

section

/-! Bounds on actual metadata, stored rotor words, and emitted prefixes. These
are size estimates used inside separately proved machine executions. -/
namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingMachineBounds
open PreprocessingRegularTables PreprocessingCloudIndex
open UniqueGamesTheorem.Foundations.Complexity
open scoped BigOperators

theorem cloudTotal_le_input (t : GraphTables.Table) (v : Fin t.vertices) :
    cloudSize t v + padding t v ≤ ExpanderFamily.growth * inputLength t := by
  rw [cloudSize_add_padding]
  exact (PreprocessingLevels.cloudPaddedSize_bounds _).2.trans
    (Nat.mul_le_mul_left _ (cloudSize_le_input t v))

theorem level_le_input (t : GraphTables.Table) (v : Fin t.vertices) :
    PreprocessingLevels.boundedLevel (cloudSize t v) ≤ inputLength t :=
  (PreprocessingLevels.boundedLevel_le_input _).trans (cloudSize_le_input t v)

theorem regularVertices_le_input (t : GraphTables.Table) :
    vertexCount t (padding t) ≤ ExpanderFamily.growth * inputLength t :=
  (vertexCount_le t).trans
    (Nat.mul_le_mul_left _ (GraphTables.darts_le_tableBits_length t))

theorem prefix_le_input (t : GraphTables.Table) (k : Nat) :
    PreprocessingPaddingOffsets.offset (padding t) k ≤
      ExpanderFamily.growth * inputLength t := by
  have hsum : (∑ v, padding t v) ≤ vertexCount t (padding t) := by
    unfold vertexCount
    omega
  exact (offset_le_sum (padding t) k).trans (hsum.trans (regularVertices_le_input t))

theorem tableBits_le_of_counts (t : GraphTables.Table) (a b L : Nat)
    (hv : t.vertices ≤ a * L) (he : t.darts ≤ b * L) :
    (GraphTables.tableBits t).length ≤ (tablePolynomial a b).eval L := by
  have hsum := Nat.add_le_add hv he
  have hprod := Nat.mul_le_mul he (Nat.add_le_add_right hsum 8192)
  have h := (GraphTables.tableBits_length_le t).trans
    (Nat.add_le_add (Nat.add_le_add_right hsum 2) hprod)
  simpa only [tablePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] using h

theorem regularBits_le (H : BaseTable) (t : GraphTables.Table) :
    (PortTables.tableBits (regularize H t)).length ≤
      regularPolynomial.eval (inputLength t) := by
  have hv : (PortTables.graphTable (regularize H t)).vertices ≤
      ExpanderFamily.growth * inputLength t := regularVertices_le_input t
  have he : (PortTables.graphTable (regularize H t)).darts ≤
      (ExpanderFamily.growth * (internalDegree + 1)) * inputLength t := by
    change vertexCount t (padding t) * (internalDegree + 1) ≤ _
    calc
      _ ≤ (ExpanderFamily.growth * inputLength t) * (internalDegree + 1) :=
        Nat.mul_le_mul_right _ hv
      _ = _ := by ac_rfl
  exact tableBits_le_of_counts (PortTables.graphTable (regularize H t)) _ _ _ hv he

theorem cloudRotorBits_le (t : GraphTables.Table) (v : Fin t.vertices) {q : Nat}
    (table : ExpanderTables.Table (cloudSize t v + padding t v) q) :
    (encodeWords (ExpanderTableWords.rotationWords table)).length ≤
      (rotorPolynomial q).eval (inputLength t) := by
  have hd : (cloudSize t v + padding t v) * q ≤
      (ExpanderFamily.growth * q) * inputLength t := by
    calc
      _ ≤ (ExpanderFamily.growth * inputLength t) * q :=
        Nat.mul_le_mul_right _ (cloudTotal_le_input t v)
      _ = _ := by ac_rfl
  have h := (ExpanderTableWords.encode_rotationWords_length_le table).trans
    (Nat.mul_le_mul hd (Nat.add_le_add_right hd 1))
  simpa only [rotorPolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one] using h

end UniqueGamesTheorem.Foundations.PCP.PreprocessingMachineBounds

end

section

/-! Executable, codec-compatible stage maps for the actual preprocessing
constructor. The decomposition below is an equality of its existing functions;
runtime certificates must be supplied by the respective concrete machines. -/
namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingStageMaps
open PreprocessingRegularTables

def regular (H : BaseTable) (t : GraphTables.Table) : PortTables.Input (internalDegree + 1) :=
  ⟨vertexCount t (PreprocessingRegularTables.padding t), regularize H t⟩

end UniqueGamesTheorem.Foundations.PCP.PreprocessingStageMaps

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

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialRows

open Target GraphTables RawInitialTables

def decodedLabel (a : GraphTables.Label) : InitialGraph.Label :=
  AlphabetRetraction.decode64 (labelOrder.symm a)

/-! Exact ordered rows of the initial incidence table. Every relation retains
all 4096 entries, including repetitions; this is a list identity, not a runtime bound. -/

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

/-! Bounds on the actual output prefixes used by the regularization loops.
The bounds include the stored headers and all earlier original/owner blocks.
They concern actual serialized words; machine executions are proved separately. -/
namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularBounds

open PreprocessingRegularTables PreprocessingRegularWords PreprocessingRegularLoopWords
open UniqueGamesTheorem.Foundations.Complexity
open scoped BigOperators

theorem offset_succ {n : Nat} (p : Fin n → Nat) (k : Nat) (h : k < n) :
    PreprocessingPaddingOffsets.offset p (k + 1) =
      PreprocessingPaddingOffsets.offset p k + p ⟨k, h⟩ := by
  unfold PreprocessingPaddingOffsets.offset
  rw [List.take_succ_eq_append_getElem (show k < (List.finRange n).length by simpa using h)]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, List.finRange, List.getElem_ofFn]

end UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularBounds

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularOwnerProgram
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual dummy-owner body of regularization

The owner is a physically stored unary index. The code computes its cloud
metadata, initializes local index and fuel, skips the family computation when
padding is zero, and otherwise generates one rotor for all dummy vertices of
this owner. Each vertex iteration consumes one fuel bit and increments both
physical vertex indices. The final checked addition and cleanup leave only the
updated global index, prefix, and accumulated output.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable
open PreprocessingRegularLoopWords

abbrev Data := MachineRegularMetadata.Data
abbrev CoreState := MachineRegularOriginalBody.CoreState
abbrev MetaState := MachineRegularOriginalBody.MetaState
abbrev BaseTable := PreprocessingRegularTables.BaseTable

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

open Turing MachineComposition
open UniqueGamesTheorem.Foundations.PCP

namespace Header

def nTape : Tape := .inl .bound
def queryTape : Tape := .inl (.inner .query)
def fuelTape : Tape := .inl .remaining
def sumTape : Tape := .inl .total
def mTape : Tape := .inr .m
def indexTape : Tape := .inr .index
def workTape : Tape := .inr .work
def scratchTape : Tape := .inr .scratch
def verticesTape : Tape := .inr .vertices
def emitTape : Tape := .inr .emit
def outputTape : Tape := .inr .output

def memory (inner : MachineCloudPrefix.Tape → List Bool)
    (m index work scratch vertices darts emit output : List Bool) : Tape → List Bool
  | .inl k => inner k
  | .inr .m => m
  | .inr .index => index
  | .inr .work => work
  | .inr .scratch => scratch
  | .inr .vertices => vertices
  | .inr .darts => darts
  | .inr .emit => emit
  | .inr .output => output

def frame (t n v f s m i w a N R e o : List Bool) : Tape → List Bool :=
  memory (MachineCloudPrefix.frame t v [] [] [] n f s) m i w a N R e o

end Header

namespace Top

abbrev BaseTable := PreprocessingRegularTables.BaseTable

end Top

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

def instruction (tape : Fin 6 → K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .seedLeft => MachineUnaryAffineAt.seed (tape 2) 0 (labels .scanLeft)
  | .scanLeft => MachineUnaryAffineAt.scan (tape 0) (tape 4) (tape 2) 1
      (labels .scanLeft) (labels .restoreLeft)
  | .restoreLeft => Reduction.MachineTransfer.loopAt (tape 4) (tape 0) id false
      (labels .restoreLeft) (some (labels .seedRight))
  | .seedRight => MachineUnaryAffineAt.seed (tape 3) 0 (labels .scanRight)
  | .scanRight => MachineUnaryAffineAt.scan (tape 1) (tape 4) (tape 3) 1
      (labels .scanRight) (labels .restoreRight)
  | .restoreRight => Reduction.MachineTransfer.loopAt (tape 4) (tape 1) id false
      (labels .restoreRight) (some (labels .compare))
  | .compare => MachineStateEquiv.statement (compareStateEquiv A)
      (MachineCompare.loop (tape 2) (tape 3) (labels .compare)
        (some (labels .equal)) (some (labels .different)))
  | .equal => emit (tape 5) true exit
  | .different => emit (tape 5) false exit

/-- Actual execution of the two copies, the translated comparison, and the
literal bit writer, inside any program containing the stated instructions. -/
theorem equalityTrace (tape : Fin 6 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction tape labels exit l)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix : List Bool)
    (leftWord : base (tape 0) = encodeWord a ++ leftSuffix)
    (rightWord : base (tape 1) = encodeWord b ++ rightSuffix)
    (leftEmpty : base (tape 2) = []) (rightEmpty : base (tape 3) = [])
    (scratchEmpty : base (tape 4) = []) (ambient : A) :
    (advance (TM2.step program))^[steps a b]
      (some ⟨some (labels .seedLeft), clean ambient, base⟩) =
      some ⟨exit, clean ambient,
        Function.update base (tape 5) (bitEncoding (decide (a = b)) ++ base (tape 5))⟩ := by
  have hd (i j : Fin 6) (hne : i ≠ j) : tape i ≠ tape j :=
    fun h => hne (distinct h)
  let midLeft := Function.update base (tape 2) (encodeWord a)
  let midBoth := Function.update midLeft (tape 3) (encodeWord b)
  have leftRun : (advance (TM2.step program))^[copySteps a]
      (some ⟨some (labels .seedLeft), clean ambient, base⟩) =
      some ⟨some (labels .seedRight), clean ambient, midLeft⟩ := by
    simpa only [copySteps, clean, midLeft, Nat.one_mul, Nat.add_zero,
      leftEmpty, List.append_nil] using
      MachineUnaryAffineAt.seededAffineTrace (tape 0) (tape 4) (tape 2)
        (hd 0 4 (by decide)) (hd 0 2 (by decide)) (hd 4 2 (by decide)) 1 0
        (labels .seedLeft) (labels .scanLeft) (labels .restoreLeft)
        (some (labels .seedRight)) program (atLabels .seedLeft)
        (atLabels .scanLeft) (atLabels .restoreLeft)
        base a leftSuffix leftWord scratchEmpty (ambient, false, none) none
  have rightSource : midLeft (tape 1) = encodeWord b ++ rightSuffix := by
    simpa [midLeft, hd 1 2 (by decide)] using rightWord
  have scratchAfterLeft : midLeft (tape 4) = [] := by
    simpa [midLeft, hd 4 2 (by decide)] using scratchEmpty
  have rightCopyAfterLeft : midLeft (tape 3) = [] := by
    simpa [midLeft, hd 3 2 (by decide)] using rightEmpty
  have rightRun : (advance (TM2.step program))^[copySteps b]
      (some ⟨some (labels .seedRight), clean ambient, midLeft⟩) =
      some ⟨some (labels .compare), clean ambient, midBoth⟩ := by
    simpa only [copySteps, clean, midBoth, Nat.one_mul, Nat.add_zero,
      rightCopyAfterLeft, List.append_nil] using
      MachineUnaryAffineAt.seededAffineTrace (tape 1) (tape 4) (tape 3)
        (hd 1 4 (by decide)) (hd 1 3 (by decide)) (hd 4 3 (by decide)) 1 0
        (labels .seedRight) (labels .scanRight) (labels .restoreRight)
        (some (labels .compare)) program (atLabels .seedRight)
        (atLabels .scanRight) (atLabels .restoreRight)
        midLeft b rightSuffix rightSource scratchAfterLeft (ambient, false, none) none
  have copyLeftWord : midBoth (tape 2) = encodeWord a := by
    simp [midBoth, midLeft, hd 2 3 (by decide)]
  have copyRightWord : midBoth (tape 3) = encodeWord b := by simp [midBoth]
  have restored : Reduction.MachineTransfer.tapesAt (tape 2) (tape 3) midBoth [] [] = base := by
    funext k
    by_cases hl : k = tape 2
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, midBoth, midLeft,
        hd 2 3 (by decide), leftEmpty]
    · by_cases hr : k = tape 3
      · subst k
        simp [Reduction.MachineTransfer.tapesAt, midBoth, midLeft, rightEmpty]
      · simp [Reduction.MachineTransfer.tapesAt, midBoth, midLeft, hl, hr]
  let back := MachineStateEquiv.program (compareStateEquiv A).symm program
  have atCompare : back (labels .compare) =
      MachineCompare.loop (tape 2) (tape 3) (labels .compare)
        (some (labels .equal)) (some (labels .different)) := by
    change MachineStateEquiv.statement (compareStateEquiv A).symm
      (program (labels .compare)) = _
    rw [atLabels .compare]
    exact MachineStateEquiv.statement_symm_statement (compareStateEquiv A) _
  have backForward : MachineStateEquiv.program (compareStateEquiv A) back = program := by
    funext l
    change MachineStateEquiv.statement (compareStateEquiv A)
      (MachineStateEquiv.statement (compareStateEquiv A).symm (program l)) = program l
    simpa only [Equiv.symm_symm] using
      MachineStateEquiv.statement_symm_statement (compareStateEquiv A).symm (program l)
  have compareRun : (advance (TM2.step program))^[compareSteps a b]
      (some ⟨some (labels .compare), clean ambient, midBoth⟩) =
      some ⟨if a = b then some (labels .equal) else some (labels .different),
        clean ambient, base⟩ := by
    have native := MachineCompare.compareTrace_fromTapes (tape 2) (tape 3)
      (hd 2 3 (by decide)) (labels .compare) (some (labels .equal))
      (some (labels .different)) back atCompare midBoth ambient none none
    rw [copyLeftWord, copyRightWord, restored] at native
    simp only [encodeWord_eq_iff, encodeWord_length] at native
    have transported := MachineStateEquiv.trace (compareStateEquiv A) back _ _ _ native
    rw [backForward] at transported
    simpa [MachineStateEquiv.configuration, compareStateEquiv, clean, compareSteps] using
      transported
  have emitRun : TM2.step program
      ⟨if a = b then some (labels .equal) else some (labels .different),
        clean ambient, base⟩ =
      some ⟨exit, clean ambient,
        Function.update base (tape 5) (bitEncoding (decide (a = b)) ++ base (tape 5))⟩ := by
    by_cases heq : a = b
    · simpa only [heq, ite_true, if_true, decide_true] using
        emit_step (tape 5) true exit program (labels .equal) (atLabels .equal)
          (clean ambient) base
    · simpa only [heq, ite_false, decide_false] using
        emit_step (tape 5) false exit program (labels .different) (atLabels .different)
          (clean ambient) base
  have copied := joinTrace leftRun rightRun
  have compared := joinTrace copied compareRun
  rw [steps, Function.iterate_succ_apply', compared, advance_some]
  exact emitRun

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

variable {n d : Nat}

theorem row_word (table : PortTables.Table n d) (i : Fin (n * d))
    (j : Nat) (hj : j < 4098) :
    (PortTables.tableWords table)[2 + 4098 * i.val + j]? =
      (GraphTables.rowWords (PortTables.flatRows table)[i])[j]? := by
  rw [PortTables.tableWords_eq]
  change (n :: n * d :: (PortTables.flatRows table).toList.flatMap
    GraphTables.rowWords)[2 + 4098 * i.val + j]? = _
  rw [show 2 + 4098 * i.val + j = (4098 * i.val + j + 1) + 1 by omega,
    List.getElem?_cons_succ, List.getElem?_cons_succ]
  apply flatMap_word GraphTables.rowWords 4098 j hj
    (PortTables.flatRows table).toList
    (fun row _ => GraphTables.rowWords_length row) i.val
    ((PortTables.flatRows table)[i])
  simp only [Vector.getElem?_toList, Vector.getElem?_eq_getElem i.isLt,
    Fin.getElem_fin]

/-- The first word of row `i` records the tail vertex. -/
theorem tail_word (table : PortTables.Table n d) (i : Fin (n * d)) :
    (PortTables.tableWords table)[2 + 4098 * i.val]? =
      some (((PortTables.rowIndex n d).symm i).1.val) := by
  have h := row_word table i 0 (by decide)
  simpa only [Nat.add_zero, GraphTables.rowWords, PortTables.flatRows,
    Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, List.cons_append,
    List.nil_append, List.getElem?_cons_zero] using h

/-- The second word of row `i` is the actual stored reverse index. -/
theorem reverse_word (table : PortTables.Table n d) (i : Fin (n * d)) :
    (PortTables.tableWords table)[3 + 4098 * i.val]? =
      some (table.reverseIndex[i].val) := by
  have h := row_word table i 1 (by decide)
  rw [show 2 + 4098 * i.val + 1 = 3 + 4098 * i.val by omega] at h
  simpa only [GraphTables.rowWords, PortTables.flatRows, Fin.getElem_fin,
    Vector.getElem_ofFn, Fin.eta, List.cons_append, List.nil_append,
    List.getElem?_cons_succ, List.getElem?_cons_zero] using h

/-- Relation position `j` is a stored Boolean, encoded as its zero-or-one word. -/
theorem relation_word (table : PortTables.Table n d) (i : Fin (n * d))
    (j : Fin 4096) :
    (PortTables.tableWords table)[4 + 4098 * i.val + j.val]? =
      some (GraphTables.bitWord table.relations[i][j]) := by
  have h := row_word table i (j.val + 2) (by omega)
  rw [show 2 + 4098 * i.val + (j.val + 2) = 4 + 4098 * i.val + j.val by omega] at h
  simpa only [GraphTables.rowWords, GraphTables.relationWords,
    PortTables.flatRows, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
    List.cons_append, List.nil_append, List.getElem?_cons_succ,
    List.getElem?_map, Vector.getElem?_toList,
    Vector.getElem?_eq_getElem j.isLt, Option.map_some] using h

/-- After the reverse-index lookup, the target row's tail is the rotor endpoint. -/
theorem rotation_head_word (table : PortTables.Table n d) (e : Fin n × Fin d) :
    (PortTables.tableWords table)[2 + 4098 * (table.reverseIndex[PortTables.rowIndex n d e]).val]? =
      some ((PortTables.rotation table e).1.val) :=
  tail_word table (table.reverseIndex[PortTables.rowIndex n d e])

end UniqueGamesTheorem.Foundations.PCP.PortTableLookup

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_PoweringMachineRelationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRelation

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

def value (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d)
    (position : Fin 4096) : Nat :=
  GraphTables.bitWord table.relations[PortTables.rowIndex n d (vertex, port)][position]

theorem selected (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d)
    (position : Fin 4096) :
    (PortTables.tableWords table)[address vertex port position]? =
      some (value table vertex port position) := by
  have h := PortTableLookup.relation_word table (PortTables.rowIndex n d (vertex, port)) position
  have hindex : address vertex port position =
      4 + 4098 * (PortTables.rowIndex n d (vertex, port)).val + position.val := by
    simp only [address, PortTables.rowIndex_val, Nat.mul_add, Nat.mul_assoc]
    omega
  rw [hindex]
  exact h

def instruction (source : K) (tape : Fin 5 → K) (port : Fin d) (position : Fin 4096)
    (labels : MachineAffineLookup.Label → Λ) (exit : Option Λ) :
    MachineAffineLookup.Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  MachineAffineLookup.instruction source tape (4098 * d)
    (4098 * port.val + 4 + position.val) labels exit

/-- Actual predicate access, with serialization selection discharged. -/
theorem relationTrace (source : K) (tape : Fin 5 → K)
    (distinct : Function.Injective tape) (outside : ∀ i, source ≠ tape i)
    (port : Fin d) (position : Fin 4096)
    (labels : MachineAffineLookup.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction source tape port position labels exit l)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool)
    (tableWord : base (tape 0) = PortTables.tableBits table) (scratchEmpty : base (tape 4) = [])
    (suffix : List Bool) (sourceWord : base source = encodeWord vertex.val ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[MachineAffineLookup.steps (PortTables.tableWords table)
      vertex.val (4098 * d) (4098 * port.val + 4 + position.val)]
      (some ⟨some (labels .seed), (ambient,register), base⟩) =
      some ⟨exit, (ambient,none), MachineAffineLookup.finalTapes tape base
        (PortTables.tableWords table) (address vertex port position) (value table vertex port position)⟩ :=
  MachineAffineLookup.affineLookupTrace source tape distinct outside
    (4098 * d) (4098 * port.val + 4 + position.val) labels exit program atLabels
    base (PortTables.tableWords table) tableWord scratchEmpty vertex.val suffix sourceWord
    (value table vertex port position) (selected table vertex port position) ambient register

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRelation

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

def instruction (tape : Fin 7 → K) (degree port : Nat)
    (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .reverse l => MachineAffineLookup.instruction (tape 1) (reverseTapes tape)
      (4098 * degree) (4098 * port + 3) (fun q => labels (.reverse q))
      (some (labels (.endpoint .seed))) l
  | .endpoint l => MachineAffineLookup.instruction (tape 4) (endpointTapes tape)
      4098 2 (fun q => labels (.endpoint q)) exit l

def reverseId (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d) : Nat :=
  table.reverseIndex[PortTables.rowIndex n d (vertex, port)].val

def endpointAddress (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d) : Nat :=
  4098 * reverseId table vertex port + 2

theorem reverse_selected (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d) :
    (PortTables.tableWords table)[reverseAddress vertex port]? =
      some (reverseId table vertex port) := by
  have h := PortTableLookup.reverse_word table (PortTables.rowIndex n d (vertex, port))
  have hindex : reverseAddress vertex port = 3 + 4098 * (PortTables.rowIndex n d (vertex, port)).val := by
    simp only [reverseAddress, PortTables.rowIndex_val, Nat.mul_add, Nat.mul_assoc]
    omega
  rw [hindex]
  exact h

theorem endpoint_selected (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d) :
    (PortTables.tableWords table)[endpointAddress table vertex port]? =
      some ((PortTables.rotation table (vertex, port)).1.val) := by
  have h := PortTableLookup.rotation_head_word table (vertex, port)
  simpa only [endpointAddress, reverseId, Nat.add_comm] using h

def afterReverse (tape : Fin 7 → K) (table : PortTables.Table n d)
    (vertex : Fin n) (port : Fin d) (base : K → List Bool) : K → List Bool :=
  MachineAffineLookup.finalTapes (reverseTapes tape) base (PortTables.tableWords table)
    (reverseAddress vertex port) (reverseId table vertex port)

def finalTapes (tape : Fin 7 → K) (table : PortTables.Table n d)
    (vertex : Fin n) (port : Fin d) (base : K → List Bool) : K → List Bool :=
  MachineAffineLookup.finalTapes (endpointTapes tape)
    (afterReverse tape table vertex port base) (PortTables.tableWords table)
    (endpointAddress table vertex port) ((PortTables.rotation table (vertex, port)).1.val)

def steps (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d) : Nat :=
  MachineAffineLookup.steps (PortTables.tableWords table) vertex.val (4098 * d) (4098 * port.val + 3) +
    MachineAffineLookup.steps (PortTables.tableWords table) (reverseId table vertex port) 4098 2

theorem rotorTrace (tape : Fin 7 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (port : Fin d)
    (atLabels : ∀ l, program (labels l) = instruction tape d port.val labels exit l)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool)
    (tableWord : base (tape 0) = PortTables.tableBits table)
    (scratchEmpty : base (tape 6) = []) (suffix : List Bool)
    (sourceWord : base (tape 1) = encodeWord vertex.val ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps table vertex port]
      (some ⟨some (labels (.reverse .seed)), (ambient,register), base⟩) =
      some ⟨exit, (ambient,none), finalTapes tape table vertex port base⟩ := by
  have hd (i j : Fin 7) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have hrDistinct : Function.Injective (reverseTapes tape) := distinct.comp reverseRole_injective
  have heDistinct : Function.Injective (endpointTapes tape) := distinct.comp endpointRole_injective
  have hrOutside : ∀ i, tape 1 ≠ reverseTapes tape i := fun i =>
    hd 1 (reverseRole i) (source_outside_reverse i)
  have heOutside : ∀ i, tape 4 ≠ endpointTapes tape i := fun i =>
    hd 4 (endpointRole i) (reverse_outside_endpoint i)
  have hreverse := MachineAffineLookup.affineLookupTrace (tape 1) (reverseTapes tape)
    hrDistinct hrOutside (4098 * d) (4098 * port.val + 3)
    (fun q => labels (.reverse q)) (some (labels (.endpoint .seed)))
    program (fun q => atLabels (.reverse q)) base (PortTables.tableWords table)
    tableWord scratchEmpty vertex.val suffix sourceWord (reverseId table vertex port)
    (reverse_selected table vertex port) ambient register
  let mid := afterReverse tape table vertex port base
  have hmidTable : mid (tape 0) = PortTables.tableBits table := by
    calc
      mid (tape 0) = base (tape 0) :=
        MachineAffineLookup.finalTapes_other _ _ _ _ _ _
          (hd 0 2 (by decide)) (hd 0 3 (by decide)) (hd 0 4 (by decide))
      _ = _ := tableWord
  have hmidScratch : mid (tape 6) = [] := by
    calc
      mid (tape 6) = base (tape 6) :=
        MachineAffineLookup.finalTapes_other _ _ _ _ _ _
          (hd 6 2 (by decide)) (hd 6 3 (by decide)) (hd 6 4 (by decide))
      _ = _ := scratchEmpty
  have hmidSource : mid (tape 4) = encodeWord (reverseId table vertex port) ++ base (tape 4) :=
    MachineAffineLookup.finalTapes_output _ _ _ _ _
  have hendpoint := MachineAffineLookup.affineLookupTrace (tape 4) (endpointTapes tape)
    heDistinct heOutside 4098 2 (fun q => labels (.endpoint q)) exit
    program (fun q => atLabels (.endpoint q)) mid (PortTables.tableWords table)
    hmidTable hmidScratch (reverseId table vertex port) (base (tape 4)) hmidSource
    ((PortTables.rotation table (vertex, port)).1.val)
    (endpoint_selected table vertex port) ambient none
  rw [steps, Nat.add_comm, Function.iterate_add_apply, hreverse]
  exact hendpoint

theorem finalTapes_endpoint (tape : Fin 7 → K) (distinct : Function.Injective tape)
    (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d) (base : K → List Bool) :
    finalTapes tape table vertex port base (tape 5) =
      encodeWord ((PortTables.rotation table (vertex, port)).1.val) ++ base (tape 5) := by
  have hd (i j : Fin 7) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  change MachineAffineLookup.finalTapes (endpointTapes tape) _ _ _ _ (endpointTapes tape 3) = _
  rw [MachineAffineLookup.finalTapes_output]
  congr 1
  exact MachineAffineLookup.finalTapes_other _ _ _ _ _ _
    (hd 5 2 (by decide)) (hd 5 3 (by decide)) (hd 5 4 (by decide))

theorem finalTapes_other (tape : Fin 7 → K) (table : PortTables.Table n d)
    (vertex : Fin n) (port : Fin d) (base : K → List Bool) (k : K)
    (h₂ : k ≠ tape 2) (h₃ : k ≠ tape 3) (h₄ : k ≠ tape 4) (h₅ : k ≠ tape 5) :
    finalTapes tape table vertex port base k = base k := by
  calc
    finalTapes tape table vertex port base k = afterReverse tape table vertex port base k :=
      MachineAffineLookup.finalTapes_other _ _ _ _ _ _ h₂ h₃ h₅
    _ = base k := MachineAffineLookup.finalTapes_other _ _ _ _ _ _ h₂ h₃ h₄

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

def copyInstruction (source scratch output : K)
    (labels : MachineUnaryAffineAt.Label → Λ) (exit : Option Λ) :
    MachineUnaryAffineAt.Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .seed => MachineUnaryAffineAt.seed output 0 (labels .scan)
  | .scan => MachineUnaryAffineAt.scan source scratch output 1 (labels .scan) (labels .restore)
  | .restore => Reduction.MachineTransfer.loopAt scratch source id false (labels .restore) exit

def instruction : (t : Nat) → (Tape t → K) → (Fin t → Fin d) →
    (Label t → Λ) → Option Λ → Label t →
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | 0, placement, _, labels, exit =>
      copyInstruction (placement (.inr (first 0))) (placement (.inl 4))
        (placement (.inl 5)) labels exit
  | t + 1, placement, ports, labels, exit => fun l =>
      match l with
      | .inl q => PoweringMachineRotor.instruction (placement ∘ rotorRole t) d (ports 0).val
          (fun z => labels (.inl z)) (some (labels (.inr (entry t)))) q
      | .inr q => instruction t (placement ∘ shift t) (fun j => ports j.succ)
          (fun z => labels (.inr z)) exit q

def steps (table : PortTables.Table n d) :
    (t : Nat) → Fin n → (Fin t → Fin d) → Nat
  | 0, vertex, _ => 2 * (vertex.val + 1) + 1
  | t + 1, vertex, ports => PoweringMachineRotor.steps table vertex (ports 0) +
      steps table t (PortTables.rotation table (vertex, ports 0)).1 (fun j => ports j.succ)

def finalTapes (table : PortTables.Table n d) :
    (t : Nat) → (Tape t → K) → Fin n → (Fin t → Fin d) → (K → List Bool) → K → List Bool
  | 0, placement, vertex, _, base =>
      Function.update base (placement (.inl 5)) (encodeWord vertex.val ++ base (placement (.inl 5)))
  | t + 1, placement, vertex, ports, base =>
      finalTapes table t (placement ∘ shift t) (PortTables.rotation table (vertex, ports 0)).1
        (fun j => ports j.succ)
        (PoweringMachineRotor.finalTapes (placement ∘ rotorRole t) table vertex (ports 0) base)

theorem finalTapes_other (table : PortTables.Table n d) (t : Nat)
    (placement : Tape t → K) (vertex : Fin n) (ports : Fin t → Fin d)
    (base : K → List Bool) (k : K)
    (hquery : k ≠ placement (.inl 1)) (hscan : k ≠ placement (.inl 2))
    (hreverse : k ≠ placement (.inl 3)) (houtput : k ≠ placement (.inl 5))
    (hpositions : ∀ i : Fin t, k ≠ placement (.inr i.succ)) :
    finalTapes table t placement vertex ports base k = base k := by
  induction t generalizing vertex base with
  | zero => simp only [finalTapes, Function.update_of_ne houtput]
  | succ t ih =>
      let mid := PoweringMachineRotor.finalTapes (placement ∘ rotorRole t) table vertex (ports 0) base
      calc
        finalTapes table (t + 1) placement vertex ports base k = mid k :=
          ih (placement ∘ shift t) (PortTables.rotation table (vertex, ports 0)).1
            (fun j => ports j.succ) mid hquery hscan hreverse houtput
            (fun i => hpositions i.succ)
        _ = base k := PoweringMachineRotor.finalTapes_other _ _ _ _ _ k
          hquery hscan hreverse (hpositions (first t))

/-- Actual execution together with its endpoint word. No trace or running-time
hypothesis is needed: the recursive proof composes the concrete instructions. -/
theorem wordTrace (table : PortTables.Table n d) (t : Nat)
    (placement : Tape t → K) (distinct : Function.Injective placement)
    (vertex : Fin n) (ports : Fin t → Fin d)
    (labels : Label t → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction t placement ports labels exit l)
    (base : K → List Bool) (tableWord : base (placement (.inl 0)) = PortTables.tableBits table)
    (scratchEmpty : base (placement (.inl 4)) = []) (suffix : List Bool)
    (sourceWord : base (placement (.inr (first t))) = encodeWord vertex.val ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps table t vertex ports]
      (some ⟨some (labels (entry t)), (ambient,register), base⟩) =
      some ⟨exit, (ambient,none), finalTapes table t placement vertex ports base⟩ ∧
    finalTapes table t placement vertex ports base (placement (.inl 5)) =
      encodeWord (PoweringWalks.wordEnd (PortTables.portGraph table) t vertex ports).val ++
        base (placement (.inl 5)) := by
  induction t generalizing vertex base suffix register with
  | zero =>
      have hd (i j : Tape 0) (hne : i ≠ j) : placement i ≠ placement j := fun h => hne (distinct h)
      have hrun := MachineUnaryAffineAt.seededAffineTrace
        (placement (.inr (first 0))) (placement (.inl 4)) (placement (.inl 5))
        (hd _ _ (by simp [first])) (hd _ _ (by simp [first])) (hd _ _ (by simp))
        1 0 (labels .seed) (labels .scan) (labels .restore) exit program
        (atLabels .seed) (atLabels .scan) (atLabels .restore)
        base vertex.val suffix sourceWord scratchEmpty ambient register
      constructor
      · simpa only [steps, entry, finalTapes, Nat.one_mul, Nat.add_zero] using hrun
      · simp only [finalTapes, Function.update_self, PoweringWalks.wordEnd]
  | succ t ih =>
      have hd (i j : Tape (t + 1)) (hne : i ≠ j) : placement i ≠ placement j :=
        fun h => hne (distinct h)
      have hrotor := PoweringMachineRotor.rotorTrace (placement ∘ rotorRole t)
        (distinct.comp (rotorRole_injective t)) (fun q => labels (.inl q))
        (some (labels (.inr (entry t)))) program (ports 0) (fun q => atLabels (.inl q))
        table vertex base tableWord scratchEmpty suffix sourceWord ambient register
      let mid := PoweringMachineRotor.finalTapes (placement ∘ rotorRole t) table vertex (ports 0) base
      have hmidTable : mid (placement (.inl 0)) = PortTables.tableBits table := by
        calc
          mid (placement (.inl 0)) = base (placement (.inl 0)) :=
            PoweringMachineRotor.finalTapes_other _ _ _ _ _ _
              (hd _ _ (by simp [rotorRole])) (hd _ _ (by simp [rotorRole]))
              (hd _ _ (by simp [rotorRole])) (hd _ _ (by simp [rotorRole, first]))
          _ = _ := tableWord
      have hmidScratch : mid (placement (.inl 4)) = [] := by
        calc
          mid (placement (.inl 4)) = base (placement (.inl 4)) :=
            PoweringMachineRotor.finalTapes_other _ _ _ _ _ _
              (hd _ _ (by simp [rotorRole])) (hd _ _ (by simp [rotorRole]))
              (hd _ _ (by simp [rotorRole])) (hd _ _ (by simp [rotorRole, first]))
          _ = _ := scratchEmpty
      have hmidOutput : mid (placement (.inl 5)) = base (placement (.inl 5)) :=
        PoweringMachineRotor.finalTapes_other _ _ _ _ _ _
          (hd _ _ (by simp [rotorRole])) (hd _ _ (by simp [rotorRole]))
          (hd _ _ (by simp [rotorRole])) (hd _ _ (by simp [rotorRole, first]))
      have hmidSource : mid (placement (.inr (first t).succ)) =
          encodeWord (PortTables.rotation table (vertex, ports 0)).1.val ++
            base (placement (.inr (first t).succ)) :=
        PoweringMachineRotor.finalTapes_endpoint _ (distinct.comp (rotorRole_injective t)) _ _ _ _
      have htail := ih (placement ∘ shift t) (distinct.comp (shift_injective t))
        (PortTables.rotation table (vertex, ports 0)).1 (fun j => ports j.succ)
        (fun q => labels (.inr q)) (fun q => atLabels (.inr q)) mid hmidTable hmidScratch
        (base (placement (.inr (first t).succ))) hmidSource none
      constructor
      · rw [steps, Nat.add_comm, Function.iterate_add_apply]
        simp only [entry]
        rw [hrotor]
        exact htail.1
      · change finalTapes table t (placement ∘ shift t)
          (PortTables.rotation table (vertex, ports 0)).1 (fun j => ports j.succ) mid
          ((placement ∘ shift t) (.inl 5)) = _
        rw [htail.2]
        change _ ++ mid (placement (.inl 5)) = _
        rw [hmidOutput]
        rfl

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

def instruction (hl : l ≤ max) (hr : r ≤ max) (placement : Tape max → K)
    (left : Fin l → Fin d) (right : Fin r → Fin d)
    (labels : Label l r → Λ) (exit : Option Λ) :
    Label l r → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .inl q => PoweringMachineWord.instruction l
      (placement ∘ PoweringMachineTapes.wordPlacement hl false) left
      (fun z => labels (.inl z))
      (some (labels (.inr (.inl (PoweringMachineWord.entry r))))) q
  | .inr (.inl q) => PoweringMachineWord.instruction r
      (placement ∘ PoweringMachineTapes.wordPlacement hr true) right
      (fun z => labels (.inr (.inl z)))
      (some (labels (.inr (.inr .seedLeft)))) q
  | .inr (.inr q) => MachineUnaryEqualityBit.instruction
      (placement ∘ PoweringMachineTapes.equalityPlacement max)
      (fun z => labels (.inr (.inr z))) exit q

def endpoint (graph : PortTables.Table n d) {t : Nat} (vertex : Fin n)
    (ports : Fin t → Fin d) : Fin n :=
  PoweringWalks.wordEnd (PortTables.portGraph graph) t vertex ports

def resultBit (graph : PortTables.Table n d) (vertex : Fin n)
    (left : Fin l → Fin d) (right : Fin r → Fin d) : Bool :=
  decide (endpoint graph vertex left = endpoint graph vertex right)

def wordTapes (graph : PortTables.Table n d) {t : Nat} (h : t ≤ max)
    (placement : Tape max → K) (target : Bool) (vertex : Fin n)
    (ports : Fin t → Fin d) (base : K → List Bool) : K → List Bool :=
  PoweringMachineWord.finalTapes graph t
    (placement ∘ PoweringMachineTapes.wordPlacement h target) vertex ports base

def finalTapes (graph : PortTables.Table n d) (hl : l ≤ max) (hr : r ≤ max)
    (placement : Tape max → K) (vertex : Fin n)
    (left : Fin l → Fin d) (right : Fin r → Fin d) (base : K → List Bool) :
    K → List Bool :=
  let afterLeft := wordTapes graph hl placement false vertex left base
  let afterBoth := wordTapes graph hr placement true vertex right afterLeft
  Function.update afterBoth (placement (.inl 10))
    (MachineUnaryEqualityBit.bitEncoding (resultBit graph vertex left right) ++
      afterBoth (placement (.inl 10)))

def steps (graph : PortTables.Table n d) (vertex : Fin n)
    (left : Fin l → Fin d) (right : Fin r → Fin d) : Nat :=
  PoweringMachineWord.steps graph l vertex left +
    PoweringMachineWord.steps graph r vertex right +
    MachineUnaryEqualityBit.steps (endpoint graph vertex left).val
      (endpoint graph vertex right).val

/-- The only variable-size work areas changed by a word are the declared
query, scan, reverse, selected endpoint, and trajectory tapes. -/
theorem wordTapes_other (graph : PortTables.Table n d) {t : Nat} (h : t ≤ max)
    (placement : Tape max → K) (target : Bool) (vertex : Fin n)
    (ports : Fin t → Fin d) (base : K → List Bool) (k : K)
    (hquery : k ≠ placement (.inl 2)) (hscan : k ≠ placement (.inl 3))
    (hreverse : k ≠ placement (.inl 4))
    (houtput : k ≠ placement (PoweringMachineTapes.endpoint max target))
    (hpositions : ∀ i : Fin max, k ≠ placement (.inr i)) :
    wordTapes graph h placement target vertex ports base k = base k := by
  apply PoweringMachineWord.finalTapes_other
  · simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_one,
      PoweringMachineTapes.query] using hquery
  · simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_two,
      PoweringMachineTapes.scan] using hscan
  · simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_three,
      PoweringMachineTapes.reverse] using hreverse
  · simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_five] using houtput
  · intro i
    simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_succ] using
      hpositions (Fin.castLE h i)

theorem wordTapes_role (graph : PortTables.Table n d) {t : Nat} (h : t ≤ max)
    (placement : Tape max → K) (distinct : Function.Injective placement)
    (target : Bool) (vertex : Fin n) (ports : Fin t → Fin d)
    (base : K → List Bool) (j : Fin 11)
    (hquery : j ≠ 2) (hscan : j ≠ 3) (hreverse : j ≠ 4)
    (houtput : j ≠ if target then 7 else 6) :
    wordTapes graph h placement target vertex ports base (placement (.inl j)) =
      base (placement (.inl j)) := by
  apply wordTapes_other
  · intro he
    exact hquery (Sum.inl.inj (distinct he))
  · intro he
    exact hscan (Sum.inl.inj (distinct he))
  · intro he
    exact hreverse (Sum.inl.inj (distinct he))
  · intro he
    apply houtput
    cases target <;> exact Sum.inl.inj (distinct he)
  · intro i he
    cases distinct he

theorem finalTapes_other (graph : PortTables.Table n d) (hl : l ≤ max) (hr : r ≤ max)
    (placement : Tape max → K) (vertex : Fin n)
    (left : Fin l → Fin d) (right : Fin r → Fin d) (base : K → List Bool) (k : K)
    (hquery : k ≠ placement (.inl 2)) (hscan : k ≠ placement (.inl 3))
    (hreverse : k ≠ placement (.inl 4)) (hleft : k ≠ placement (.inl 6))
    (hright : k ≠ placement (.inl 7)) (hrow : k ≠ placement (.inl 10))
    (hpositions : ∀ i : Fin max, k ≠ placement (.inr i)) :
    finalTapes graph hl hr placement vertex left right base k = base k := by
  unfold finalTapes
  rw [Function.update_of_ne hrow]
  rw [wordTapes_other graph hr placement true vertex right _ k
    hquery hscan hreverse hright hpositions]
  exact wordTapes_other graph hl placement false vertex left base k
    hquery hscan hreverse hleft hpositions

/-- This single statement covers table 0, start 1, scratch 5, and copies 8/9. -/
theorem finalTapes_role (graph : PortTables.Table n d) (hl : l ≤ max) (hr : r ≤ max)
    (placement : Tape max → K) (distinct : Function.Injective placement) (vertex : Fin n)
    (left : Fin l → Fin d) (right : Fin r → Fin d) (base : K → List Bool)
    (j : Fin 11) (hrole : j = 0 ∨ j = 1 ∨ j = 5 ∨ j = 8 ∨ j = 9) :
    finalTapes graph hl hr placement vertex left right base (placement (.inl j)) =
      base (placement (.inl j)) := by
  apply finalTapes_other
  all_goals first
    | (intro he; have hij := Sum.inl.inj (distinct he); rcases hrole with rfl | rfl | rfl | rfl | rfl <;> simp at hij)
    | (intro i he; cases distinct he)

theorem finalTapes_output (graph : PortTables.Table n d) (hl : l ≤ max) (hr : r ≤ max)
    (placement : Tape max → K) (distinct : Function.Injective placement) (vertex : Fin n)
    (left : Fin l → Fin d) (right : Fin r → Fin d) (base : K → List Bool) :
    finalTapes graph hl hr placement vertex left right base (placement (.inl 10)) =
      MachineUnaryEqualityBit.bitEncoding (resultBit graph vertex left right) ++
        base (placement (.inl 10)) := by
  unfold finalTapes
  rw [Function.update_self,
    wordTapes_role graph hr placement distinct true vertex right _ 10
      (by decide) (by decide) (by decide) (by decide),
    wordTapes_role graph hl placement distinct false vertex left base 10
      (by decide) (by decide) (by decide) (by decide)]

theorem fieldTrace (graph : PortTables.Table n d) (hl : l ≤ max) (hr : r ≤ max)
    (placement : Tape max → K) (distinct : Function.Injective placement)
    (vertex : Fin n) (left : Fin l → Fin d) (right : Fin r → Fin d)
    (labels : Label l r → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ q, program (labels q) = instruction hl hr placement left right labels exit q)
    (base : K → List Bool)
    (tableWord : base (placement (.inl 0)) = PortTables.tableBits graph)
    (scratchEmpty : base (placement (.inl 5)) = [])
    (leftCopyEmpty : base (placement (.inl 8)) = [])
    (rightCopyEmpty : base (placement (.inl 9)) = [])
    (suffix : List Bool) (sourceWord : base (placement (.inl 1)) = encodeWord vertex.val ++ suffix)
    (ambient : A) :
    (advance (TM2.step program))^[steps graph vertex left right]
      (some ⟨some (labels (entry l r)), MachineUnaryEqualityBit.clean ambient, base⟩) =
      some ⟨exit, MachineUnaryEqualityBit.clean ambient,
        finalTapes graph hl hr placement vertex left right base⟩ := by
  let afterLeft := wordTapes graph hl placement false vertex left base
  let afterBoth := wordTapes graph hr placement true vertex right afterLeft
  have leftFrame (j : Fin 11) (h2 : j ≠ 2) (h3 : j ≠ 3) (h4 : j ≠ 4) (h6 : j ≠ 6) :
      afterLeft (placement (.inl j)) = base (placement (.inl j)) :=
    wordTapes_role graph hl placement distinct false vertex left base j h2 h3 h4 h6
  have rightFrame (j : Fin 11) (h2 : j ≠ 2) (h3 : j ≠ 3) (h4 : j ≠ 4) (h7 : j ≠ 7) :
      afterBoth (placement (.inl j)) = afterLeft (placement (.inl j)) :=
    wordTapes_role graph hr placement distinct true vertex right afterLeft j h2 h3 h4 h7
  have bothFrame (j : Fin 11) (h2 : j ≠ 2) (h3 : j ≠ 3) (h4 : j ≠ 4)
      (h6 : j ≠ 6) (h7 : j ≠ 7) :
      afterBoth (placement (.inl j)) = base (placement (.inl j)) :=
    (rightFrame j h2 h3 h4 h7).trans (leftFrame j h2 h3 h4 h6)
  have leftRun := PoweringMachineWord.wordTrace graph l
    (placement ∘ PoweringMachineTapes.wordPlacement hl false)
    (distinct.comp (PoweringMachineTapes.wordPlacement_injective hl false)) vertex left
    (fun q => labels (.inl q))
    (some (labels (.inr (.inl (PoweringMachineWord.entry r))))) program
    (fun q => atLabels (.inl q)) base
    (by simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_zero,
      PoweringMachineTapes.table] using tableWord)
    (by simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_four,
      PoweringMachineTapes.scratch] using scratchEmpty)
    suffix (by simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_first,
      PoweringMachineTapes.start] using sourceWord)
    (ambient, false, none) none
  have rightTable : afterLeft (placement (.inl 0)) = PortTables.tableBits graph :=
    (leftFrame 0 (by decide) (by decide) (by decide) (by decide)).trans tableWord
  have rightScratch : afterLeft (placement (.inl 5)) = [] :=
    (leftFrame 5 (by decide) (by decide) (by decide) (by decide)).trans scratchEmpty
  have rightSource : afterLeft (placement (.inl 1)) = encodeWord vertex.val ++ suffix :=
    (leftFrame 1 (by decide) (by decide) (by decide) (by decide)).trans sourceWord
  have rightRun := PoweringMachineWord.wordTrace graph r
    (placement ∘ PoweringMachineTapes.wordPlacement hr true)
    (distinct.comp (PoweringMachineTapes.wordPlacement_injective hr true)) vertex right
    (fun q => labels (.inr (.inl q))) (some (labels (.inr (.inr .seedLeft)))) program
    (fun q => atLabels (.inr (.inl q))) afterLeft
    (by simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_zero,
      PoweringMachineTapes.table] using rightTable)
    (by simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_four,
      PoweringMachineTapes.scratch] using rightScratch)
    suffix (by simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_first,
      PoweringMachineTapes.start] using rightSource)
    (ambient, false, none) none
  have leftEndpoint : afterBoth (placement (.inl 6)) =
      encodeWord (endpoint graph vertex left).val ++ base (placement (.inl 6)) := by
    rw [rightFrame 6 (by decide) (by decide) (by decide) (by decide)]
    dsimp only [afterLeft, wordTapes]
    simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_five,
      PoweringMachineTapes.endpoint_false, PoweringMachineTapes.leftEndpoint,
      wordTapes, endpoint] using leftRun.2
  have rightEndpoint : afterBoth (placement (.inl 7)) =
      encodeWord (endpoint graph vertex right).val ++ afterLeft (placement (.inl 7)) := by
    dsimp only [afterBoth, wordTapes]
    simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_five,
      PoweringMachineTapes.endpoint_true, PoweringMachineTapes.rightEndpoint,
      wordTapes, endpoint] using rightRun.2
  have copiesLeft : afterBoth (placement (.inl 8)) = [] :=
    (bothFrame 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans leftCopyEmpty
  have copiesRight : afterBoth (placement (.inl 9)) = [] :=
    (bothFrame 9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans rightCopyEmpty
  have scratchBoth : afterBoth (placement (.inl 5)) = [] :=
    (bothFrame 5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans scratchEmpty
  have equalityRun := MachineUnaryEqualityBit.equalityTrace
    (placement ∘ PoweringMachineTapes.equalityPlacement max)
    (distinct.comp (PoweringMachineTapes.equalityPlacement_injective max))
    (fun q => labels (.inr (.inr q))) exit program (fun q => atLabels (.inr (.inr q)))
    afterBoth (endpoint graph vertex left).val (endpoint graph vertex right).val
    (base (placement (.inl 6))) (afterLeft (placement (.inl 7)))
    (by simpa only [Function.comp_apply, PoweringMachineTapes.equalityPlacement_zero,
      PoweringMachineTapes.leftEndpoint] using leftEndpoint)
    (by simpa only [Function.comp_apply, PoweringMachineTapes.equalityPlacement_one,
      PoweringMachineTapes.rightEndpoint] using rightEndpoint)
    (by simpa only [Function.comp_apply, PoweringMachineTapes.equalityPlacement_two,
      PoweringMachineTapes.leftCopy] using copiesLeft)
    (by simpa only [Function.comp_apply, PoweringMachineTapes.equalityPlacement_three,
      PoweringMachineTapes.rightCopy] using copiesRight)
    (by simpa only [Function.comp_apply, PoweringMachineTapes.equalityPlacement_four,
      PoweringMachineTapes.scratch] using scratchBoth)
    ambient
  have joined := joinTrace (joinTrace leftRun.1 rightRun.1) equalityRun
  simpa only [steps, entry, MachineUnaryEqualityBit.clean, Function.comp_apply,
    PoweringMachineTapes.equalityPlacement_five, PoweringMachineTapes.rowOutput,
    finalTapes, resultBit, Fin.ext_iff,
    afterLeft, afterBoth, wordTapes] using joined

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineEqualityField

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_PoweringMasterState
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Explicit common-register layout for the powering machine. The header,
word and affine routines use the trailing optional-bit register directly.
Comparison reassociates the finite registers; row evaluation moves the fixed
buffer to the final component. The row adapter below proves an actual step
of the caller's mixed program, rather than requiring that the entire program
be a translated copy of the row routine. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMasterState

open Turing
open MachineFixedBlockMap

abbrev OtherRegisters (N : Nat) := Buffer N × (Bool × Option Bool)
abbrev Master (N : Nat) := OtherRegisters N × Option Bool
abbrev CompareState (N : Nat) := Buffer N × (Bool × (Option Bool × Option Bool))
abbrev RowState (N : Nat) := (Bool × (Option Bool × Option Bool)) × Buffer N

/-- This is definitionally the state already used by the equality-bit producer. -/
def compareEquiv (N : Nat) : Master N ≃ CompareState N :=
  (MachineUnaryEqualityBit.compareStateEquiv (Buffer N)).symm

/-- All four finite components are retained by this register permutation. -/
def rowEquiv (N : Nat) : Master N ≃ RowState N where
  toFun state := ((state.1.2.1, (state.1.2.2, state.2)), state.1.1)
  invFun state := ((state.2, (state.1.1, state.1.2.1)), state.1.2.2)
  left_inv := by rintro ⟨⟨buffer, ⟨flag, left⟩⟩, right⟩; rfl
  right_inv := by rintro ⟨⟨flag, ⟨left, right⟩⟩, buffer⟩; rfl

@[simp] theorem compareEquiv_apply (N : Nat) (buffer : Buffer N)
    (flag : Bool) (left right : Option Bool) :
    compareEquiv N ((buffer, (flag, left)), right) = (buffer, (flag, (left, right))) := rfl

@[simp] theorem compareEquiv_symm_apply (N : Nat) (buffer : Buffer N)
    (flag : Bool) (left right : Option Bool) :
    (compareEquiv N).symm (buffer, (flag, (left, right))) = ((buffer, (flag, left)), right) := rfl

@[simp] theorem rowEquiv_apply (N : Nat) (buffer : Buffer N)
    (flag : Bool) (left right : Option Bool) :
    rowEquiv N ((buffer, (flag, left)), right) = ((flag, (left, right)), buffer) := rfl

@[simp] theorem rowEquiv_symm_apply (N : Nat) (buffer : Buffer N)
    (flag : Bool) (left right : Option Bool) :
    (rowEquiv N).symm ((flag, (left, right)), buffer) = ((buffer, (flag, left)), right) := rfl

def withBuffer {N : Nat} (buffer : Buffer N) : Master N :=
  ((buffer, (false, none)), none)

def clean (N : Nat) : Master N := withBuffer (emptyBuffer N)

@[simp] theorem equalityBit_clean {N : Nat} (buffer : Buffer N) :
    MachineUnaryEqualityBit.clean buffer = withBuffer buffer := rfl

@[simp] theorem rowEquiv_withBuffer {N : Nat} (buffer : Buffer N) :
    rowEquiv N (withBuffer buffer) = ((false, (none, none)), buffer) := rfl

@[simp] theorem compareEquiv_withBuffer {N : Nat} (buffer : Buffer N) :
    compareEquiv N (withBuffer buffer) = (buffer, (false, (none, none))) := rfl

/-- The row primitive clears only its own buffer; other finite registers survive. -/
def clearBuffer {N : Nat} (state : Master N) : Master N :=
  (rowEquiv N).symm ((rowEquiv N state).1, emptyBuffer N)

@[simp] theorem clearBuffer_apply {N : Nat} (buffer : Buffer N)
    (flag : Bool) (left right : Option Bool) :
    clearBuffer ((buffer, (flag, left)), right) =
      ((emptyBuffer N, (flag, left)), right) := rfl

@[simp] theorem clearBuffer_withBuffer {N : Nat} (buffer : Buffer N) :
    clearBuffer (withBuffer buffer) = clean N := rfl

section Row

variable {K Λ : Type} [DecidableEq K] {N M : Nat}

/-- Only this instruction block is translated into the common state. -/
def encodedBlockAt (src dst : K) (F : Buffer N → Buffer M) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (Master N) :=
  MachineStateEquiv.statement (rowEquiv N).symm
    (PoweringMachineRow.encodedBlockAt src dst F exit)

theorem stepAux_encodedBlockAt (src dst : K) (F : Buffer N → Buffer M)
    (exit : Option Λ) (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : Master N) (tapes : K → List Bool)
    (hinput : tapes src = PoweringMachineRow.encodeBits (List.ofFn bits) ++ suffix) :
    TM2.stepAux (encodedBlockAt src dst F exit) state tapes =
      { l := exit, var := clearBuffer state,
        stk := Function.update (Function.update tapes src suffix) dst
          (PoweringMachineRow.encodeBits (List.ofFn (F bits)) ++ tapes dst) } := by
  rw [encodedBlockAt, MachineStateEquiv.stepAux_transport_symm, Equiv.symm_symm]
  rw [PoweringMachineRow.stepAux_encodedBlockAt src dst F exit hne bits suffix
    (rowEquiv N state) tapes hinput]
  rfl

/-- Exact caller-program step, with no hypothesis about its other labels. -/
theorem step_encodedBlockAt (src dst : K) (F : Buffer N → Buffer M) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (Master N))
    (label : Λ) (atLabel : program label = encodedBlockAt src dst F exit)
    (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : Master N) (tapes : K → List Bool)
    (hinput : tapes src = PoweringMachineRow.encodeBits (List.ofFn bits) ++ suffix) :
    TM2.step program ⟨some label, state, tapes⟩ =
      some ⟨exit, clearBuffer state,
        Function.update (Function.update tapes src suffix) dst
          (PoweringMachineRow.encodeBits (List.ofFn (F bits)) ++ tapes dst)⟩ := by
  simp only [TM2.step, atLabel, stepAux_encodedBlockAt src dst F exit hne bits suffix state tapes hinput]

def rowAt {t S q : Nat} (src dst : K)
    (labelAt : Fin q → Fin S → PCP.GraphTables.Label) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (Master (PoweringMachineRow.inputSize t S)) :=
  encodedBlockAt src dst (PoweringMachineRow.rowBlock labelAt) exit

/-- The producer's clean finite controls and any previous buffer contents
become the completely clean master state after one genuine row transition. -/
theorem step_rowAt_clean {t S q : Nat} (src dst : K)
    (labelAt : Fin q → Fin S → PCP.GraphTables.Label) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ
      (Master (PoweringMachineRow.inputSize t S)))
    (label : Λ) (atLabel : program label = rowAt (t := t) src dst labelAt exit)
    (hne : src ≠ dst) (bits register : Buffer (PoweringMachineRow.inputSize t S))
    (suffix : List Bool) (tapes : K → List Bool)
    (hinput : tapes src = PoweringMachineRow.encodeBits (List.ofFn bits) ++ suffix) :
    TM2.step program ⟨some label, withBuffer register, tapes⟩ =
      some ⟨exit, clean (PoweringMachineRow.inputSize t S),
        Function.update (Function.update tapes src suffix) dst
          (PoweringMachineRow.encodeBits (List.ofFn (PoweringMachineRow.rowBlock labelAt bits)) ++
            tapes dst)⟩ := by
  simpa only [rowAt, clearBuffer_withBuffer] using
    step_encodedBlockAt src dst (PoweringMachineRow.rowBlock labelAt) exit
      program label atLabel hne bits suffix (withBuffer register) tapes hinput

end Row

end UniqueGamesTheorem.Foundations.Complexity.PoweringMasterState

end

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
open PoweringMachineLoop PoweringMasterState

def dropUnit (N : Nat) : (Master N × Unit) ≃ Master N where
  toFun := Prod.fst
  invFun state := (state, ())
  left_inv := by rintro ⟨state, ⟨⟩⟩; rfl
  right_inv := by intro state; rfl

/-- The native checked header statement is embedded and its inert extra
register removed. All four native header tapes keep their identities. -/
def headerStatement (max N B : Nat) (label : HeaderLabel) :
    TM2.Stmt (fun _ : GlobalTape max => Bool) Label (Master N) :=
  MachineStateEquiv.statement (dropUnit N)
    (castStatement (boolAlphabet_eq max)
      (MachineEmbedding.statement (Λextra := MachineUnaryAffineAt.Label)
        (τ := Unit) none (headerProgram (σ := OtherRegisters N) B label)))

def headerConfiguration {max N : Nat} (extra : ExtraTape max → List Bool)
    (c : TM2.Cfg HeaderAlphabet HeaderLabel (Master N)) :
    TM2.Cfg (fun _ : GlobalTape max => Bool) Label (Master N) :=
  ⟨c.l.map Sum.inl, c.var, mergeTapes c.stk extra⟩

theorem headerConfiguration_eq {max N : Nat} (extra : ExtraTape max → List Bool)
    (c : TM2.Cfg HeaderAlphabet HeaderLabel (Master N)) :
    headerConfiguration extra c =
      MachineStateEquiv.configuration (dropUnit N)
        (castConfiguration (boolAlphabet_eq max)
          (MachineEmbedding.configuration (Λextra := MachineUnaryAffineAt.Label)
            none () extra c)) := by
  cases c with
  | mk label state tapes =>
    simp only [MachineEmbedding.configuration, castConfiguration_mk,
      MachineStateEquiv.configuration, castTapes_embedding, dropUnit,
      Equiv.coe_fn_mk, headerConfiguration]
    cases label <;> rfl

theorem stepAux_headerStatement (max N B : Nat) (label : HeaderLabel)
    (state : Master N) (header : HeaderTape → List Bool)
    (extra : ExtraTape max → List Bool) :
    TM2.stepAux (headerStatement max N B label) state (mergeTapes header extra) =
      headerConfiguration extra (TM2.stepAux (headerProgram B label) state header) := by
  rw [headerStatement, MachineStateEquiv.stepAux_transport_symm]
  change MachineStateEquiv.configuration (dropUnit N)
    (TM2.stepAux (castStatement (boolAlphabet_eq max)
      (MachineEmbedding.statement none (headerProgram B label))) (state, ())
      (mergeTapes header extra)) = _
  rw [← castTapes_embedding, stepAux_cast, MachineEmbedding.stepAux_simulation]
  exact (headerConfiguration_eq extra _).symm

def program (max N B : Nat) : Label →
    TM2.Stmt (fun _ : GlobalTape max => Bool) Label (Master N)
  | .inl label => headerStatement max N B label
  | .inr .seed => MachineUnaryAffineAt.seed (.inl .source) 0 (.inr .scan)
  | .inr .scan => MachineUnaryAffineAt.scan
      (commonPlacement max (PoweringMachineTapes.table max))
      (commonPlacement max (PoweringMachineTapes.scratch max))
      (.inl .source) 1 (.inr .scan) (.inr .restore)
  | .inr .restore => Reduction.MachineTransfer.loopAt
      (commonPlacement max (PoweringMachineTapes.scratch max))
      (commonPlacement max (PoweringMachineTapes.table max))
      id false (.inr .restore) (some (.inl .initialize_))

theorem headerStep (max N B : Nat) (extra : ExtraTape max → List Bool)
    (a b : TM2.Cfg HeaderAlphabet HeaderLabel (Master N))
    (run : TM2.step (headerProgram B) a = some b) :
    TM2.step (program max N B) (headerConfiguration extra a) =
      some (headerConfiguration extra b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => simp [TM2.step] at run
    | some label =>
      have hb : TM2.stepAux (headerProgram B label) state tapes = b := Option.some.inj run
      rw [← hb]
      change some (TM2.stepAux (headerStatement max N B label) state
        (mergeTapes tapes extra)) = _
      rw [stepAux_headerStatement]

theorem headerTrace (max N B vertices : Nat) (extra : ExtraTape max → List Bool)
    (state : Master N) :
    (MachineComposition.advance (TM2.step (program max N B)))^[vertices + 2]
      (some ⟨some (.inl .initialize_), state,
        mergeTapes (initialTapes vertices []) extra⟩) =
      some ⟨none, (state.1, none), mergeTapes (finalTapes B vertices []) extra⟩ := by
  exact MachineComposition.liftSuccessfulTrace (TM2.step (headerProgram B))
    (TM2.step (program max N B)) (headerConfiguration extra)
    (headerStep max N B extra) (vertices + 2) _ _
    (PoweringMachineLoop.headerTrace B vertices [] state.1 state.2)

theorem copyFirstTrace (max N B vertices : Nat) (extra : ExtraTape max → List Bool)
    (suffix : List Bool)
    (input : extra (.inl (PoweringMachineTapes.table max)) = encodeWord vertices ++ suffix)
    (scratch : extra (.inl (PoweringMachineTapes.scratch max)) = [])
    (state : Master N) :
    (MachineComposition.advance (TM2.step (program max N B)))^[2 * (vertices + 1) + 1]
      (some ⟨some (.inr .seed), state, initialGlobalTapes extra⟩) =
      some ⟨some (.inl .initialize_), (state.1, none),
        mergeTapes (initialTapes vertices []) extra⟩ := by
  have copied := MachineUnaryAffineAt.seededAffineTrace
    (commonPlacement max (PoweringMachineTapes.table max))
    (commonPlacement max (PoweringMachineTapes.scratch max)) (.inl HeaderTape.source)
    (by
      intro heq
      have hroles := commonPlacement_injective max heq
      simp [PoweringMachineTapes.table, PoweringMachineTapes.scratch] at hroles)
    (by simp) (by simp) 1 0 (.inr .seed) (.inr .scan) (.inr .restore)
    (some (.inl .initialize_)) (program max N B) rfl rfl rfl
    (initialGlobalTapes extra) vertices suffix
    (by simpa [initialGlobalTapes, mergeTapes] using input)
    (by simpa [initialGlobalTapes, mergeTapes] using scratch) state.1 state.2
  have handoff : Function.update (initialGlobalTapes extra) (.inl HeaderTape.source)
      (encodeWord (1 * vertices + 0) ++ initialGlobalTapes extra (.inl .source)) =
      mergeTapes (initialTapes vertices []) extra := by
    funext tape
    cases tape with
    | inl field => cases field <;> simp [initialGlobalTapes, mergeTapes, initialTapes]
    | inr field => simp [initialGlobalTapes, mergeTapes]
  rw [handoff] at copied
  exact copied

/-- A concrete successful trace: copy the live input count, then execute the
existing header machine on that copy. Runtime is exactly `3*vertices+5`. -/
theorem initializeTrace (max N B vertices : Nat) (extra : ExtraTape max → List Bool)
    (suffix : List Bool)
    (input : extra (.inl (PoweringMachineTapes.table max)) = encodeWord vertices ++ suffix)
    (scratch : extra (.inl (PoweringMachineTapes.scratch max)) = [])
    (state : Master N) :
    (MachineComposition.advance (TM2.step (program max N B)))^[3 * vertices + 5]
      (some ⟨some (.inr .seed), state, initialGlobalTapes extra⟩) =
      some ⟨none, (state.1, none), mergeTapes (finalTapes B vertices []) extra⟩ := by
  rw [show 3 * vertices + 5 = (vertices + 2) + (2 * (vertices + 1) + 1) by omega,
    Function.iterate_add_apply, copyFirstTrace max N B vertices extra suffix input scratch state]
  exact headerTrace max N B vertices extra (state.1, none)

def initializeInTime (max N B vertices : Nat) (extra : ExtraTape max → List Bool)
    (suffix : List Bool)
    (input : extra (.inl (PoweringMachineTapes.table max)) = encodeWord vertices ++ suffix)
    (scratch : extra (.inl (PoweringMachineTapes.scratch max)) = [])
    (state : Master N) :
    StateTransition.EvalsToInTime (TM2.step (program max N B))
      ⟨some (.inr .seed), state, initialGlobalTapes extra⟩
      (some ⟨none, (state.1, none), mergeTapes (finalTapes B vertices []) extra⟩)
      (3 * vertices + 5) where
  steps := 3 * vertices + 5
  evals_in_steps := initializeTrace max N B vertices extra suffix input scratch state
  steps_le_m := Nat.le_refl _

/-- The five finite initialization labels can be placed in a caller's program.
The native halt becomes its chosen continuation in the very same transition. -/
def instruction {Λ : Type} (max N B : Nat) (labels : Label → Λ) (exit : Option Λ)
    (label : Label) : TM2.Stmt (fun _ : GlobalTape max => Bool) Λ (Master N) :=
  MachineSubroutine.statement labels exit (program max N B label)

def initializeAtInTime {Λ : Type} (max N B vertices : Nat)
    (labels : Label → Λ) (exit : Option Λ)
    (caller : Λ → TM2.Stmt (fun _ : GlobalTape max => Bool) Λ (Master N))
    (atLabels : ∀ label, caller (labels label) = instruction max N B labels exit label)
    (extra : ExtraTape max → List Bool) (suffix : List Bool)
    (input : extra (.inl (PoweringMachineTapes.table max)) = encodeWord vertices ++ suffix)
    (scratch : extra (.inl (PoweringMachineTapes.scratch max)) = [])
    (state : Master N) :
    StateTransition.EvalsToInTime (TM2.step caller)
      ⟨some (labels (.inr .seed)), state, initialGlobalTapes extra⟩
      (some ⟨exit, (state.1, none), mergeTapes (finalTapes B vertices []) extra⟩)
      (3 * vertices + 5) :=
  MachineSubroutine.execution labels exit (program max N B) caller atLabels
    (initializeInTime max N B vertices extra suffix input scratch state)

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_PoweringGlobalEnumerationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

abbrev State (A : Type) := MachineUnaryEqualityBit.State A

def endpoint (table : PortTables.Table n d) (vertex : Fin n) (path : List (Fin d)) : Fin n :=
  PoweringWalks.walkEnd (PortTables.portGraph table) vertex path

theorem endpoint_eq_wordEnd (table : PortTables.Table n d) (vertex : Fin n)
    (path : List (Fin d)) :
    endpoint table vertex path =
      PoweringWalks.wordEnd (PortTables.portGraph table) path.length vertex path.get := by
  rw [PoweringReach.wordEnd_eq_walkEnd_ofFn, List.ofFn_get]
  rfl

def bit (table : PortTables.Table n d) (vertex : Fin n) (path : List (Fin d))
    (port : Fin d) (left right : PortTables.Label) : Nat :=
  GraphTables.bitWord (PortTables.accepts table (endpoint table vertex path, port) left right)

def instruction (placement : PoweringMachineTapes.Tape max → K) (path : List (Fin d))
    (lengthBound : path.length ≤ max) (port : Fin d) (left right : PortTables.Label)
    (labels : Label path → Λ) (exit : Option Λ) :
    Label path → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .inl q => PoweringMachineWord.instruction path.length (placement ∘ PoweringMachineTapes.wordPlacement lengthBound false)
      path.get (fun z => labels (.inl z)) (some (labels (.inr .seed))) q
  | .inr q => PoweringMachineRelation.instruction (placement (.inl 6)) (lookupTapes placement)
      port (GraphTables.relationIndex (left, right)) (fun z => labels (.inr z)) exit q

def afterWord (placement : PoweringMachineTapes.Tape max → K) (path : List (Fin d))
    (lengthBound : path.length ≤ max) (table : PortTables.Table n d)
    (vertex : Fin n) (base : K → List Bool) : K → List Bool :=
  PoweringMachineWord.finalTapes table path.length (placement ∘ PoweringMachineTapes.wordPlacement lengthBound false)
    vertex path.get base

def finalTapes (placement : PoweringMachineTapes.Tape max → K) (path : List (Fin d))
    (lengthBound : path.length ≤ max) (port : Fin d) (left right : PortTables.Label)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool) : K → List Bool :=
  MachineAffineLookup.finalTapes (lookupTapes placement)
    (afterWord placement path lengthBound table vertex base) (PortTables.tableWords table)
    (PoweringMachineRelation.address (endpoint table vertex path) port
      (GraphTables.relationIndex (left, right))) (bit table vertex path port left right)

def steps (path : List (Fin d)) (port : Fin d) (left right : PortTables.Label)
    (table : PortTables.Table n d) (vertex : Fin n) : Nat :=
  PoweringMachineWord.steps table path.length vertex path.get +
    MachineAffineLookup.steps (PortTables.tableWords table) (endpoint table vertex path).val
      (4098 * d) (4098 * port.val + 4 + (GraphTables.relationIndex (left, right)).val)

theorem afterWord_frame (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (path : List (Fin d)) (lengthBound : path.length ≤ max)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool)
    (role : Fin 11) (h₂ : role ≠ 2) (h₃ : role ≠ 3) (h₄ : role ≠ 4) (h₆ : role ≠ 6) :
    afterWord placement path lengthBound table vertex base (placement (.inl role)) =
      base (placement (.inl role)) := by
  apply PoweringMachineWord.finalTapes_other
  · intro h; exact h₂ (by simpa [PoweringMachineTapes.query] using distinct h)
  · intro h; exact h₃ (by simpa [PoweringMachineTapes.scan] using distinct h)
  · intro h; exact h₄ (by simpa [PoweringMachineTapes.reverse] using distinct h)
  · intro h; exact h₆ (by simpa [PoweringMachineTapes.leftEndpoint] using distinct h)
  · intro i h
    have heq := distinct h
    simp at heq

/-- Table, start, scratch and both comparison stacks satisfy these numerical
inequalities, so their contents are preserved without an emptiness premise. -/
theorem finalTapes_frame (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (path : List (Fin d)) (lengthBound : path.length ≤ max)
    (port : Fin d) (left right : PortTables.Label)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool)
    (role : Fin 11) (h₂ : role ≠ 2) (h₃ : role ≠ 3) (h₄ : role ≠ 4)
    (h₆ : role ≠ 6) (h₁₀ : role ≠ 10) :
    finalTapes placement path lengthBound port left right table vertex base (placement (.inl role)) =
      base (placement (.inl role)) := by
  calc
    finalTapes placement path lengthBound port left right table vertex base (placement (.inl role)) =
        afterWord placement path lengthBound table vertex base (placement (.inl role)) := by
      apply MachineAffineLookup.finalTapes_other
      · intro h; exact h₂ (by simpa [lookupTapes, PoweringMachineTapes.query] using distinct h)
      · intro h; exact h₃ (by simpa [lookupTapes, PoweringMachineTapes.scan] using distinct h)
      · intro h; exact h₁₀ (by simpa [lookupTapes, PoweringMachineTapes.rowOutput] using distinct h)
    _ = _ := afterWord_frame placement distinct path lengthBound table vertex base role h₂ h₃ h₄ h₆

/-- Any caller tape outside the shared placement is preserved, including a
separate accumulator for already completed output rows. -/
theorem finalTapes_other (placement : PoweringMachineTapes.Tape max → K)
    (path : List (Fin d)) (lengthBound : path.length ≤ max)
    (port : Fin d) (left right : PortTables.Label)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool)
    (k : K) (outside : ∀ i, k ≠ placement i) :
    finalTapes placement path lengthBound port left right table vertex base k = base k := by
  calc
    finalTapes placement path lengthBound port left right table vertex base k =
        afterWord placement path lengthBound table vertex base k :=
      MachineAffineLookup.finalTapes_other _ _ _ _ _ _ (outside _) (outside _) (outside _)
    _ = base k := PoweringMachineWord.finalTapes_other _ _ _ _ _ _ _
      (outside _) (outside _) (outside _) (outside _) (fun i => outside _)

theorem fieldTrace (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (path : List (Fin d)) (lengthBound : path.length ≤ max)
    (port : Fin d) (left right : PortTables.Label)
    (labels : Label path → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction placement path lengthBound port left right labels exit l)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool)
    (tableWord : base (placement (.inl 0)) = PortTables.tableBits table)
    (scratchEmpty : base (placement (.inl 5)) = []) (suffix : List Bool)
    (sourceWord : base (placement (.inl 1)) = encodeWord vertex.val ++ suffix) (ambient : A) :
    (advance (TM2.step program))^[steps path port left right table vertex]
      (some ⟨some (labels (.inl (PoweringMachineWord.entry path.length))), MachineUnaryEqualityBit.clean ambient, base⟩) =
      some ⟨exit, MachineUnaryEqualityBit.clean ambient,
        finalTapes placement path lengthBound port left right table vertex base⟩ ∧
    finalTapes placement path lengthBound port left right table vertex base (placement (.inl 10)) =
      encodeWord (bit table vertex path port left right) ++ base (placement (.inl 10)) := by
  have hword := PoweringMachineWord.wordTrace table path.length (placement ∘ PoweringMachineTapes.wordPlacement lengthBound false)
    (distinct.comp (PoweringMachineTapes.wordPlacement_injective lengthBound false)) vertex path.get
    (fun q => labels (.inl q)) (some (labels (.inr .seed))) program
    (fun q => atLabels (.inl q)) base (by simpa [PoweringMachineTapes.table] using tableWord)
    (by simpa [PoweringMachineTapes.scratch] using scratchEmpty) suffix
    (by simpa [PoweringMachineTapes.start] using sourceWord) (ambient, false, none) none
  let mid := afterWord placement path lengthBound table vertex base
  have hmidTable : mid (placement (.inl 0)) = PortTables.tableBits table := by
    dsimp only [mid]
    rw [afterWord_frame placement distinct path lengthBound table vertex base 0
      (by decide) (by decide) (by decide) (by decide)]
    exact tableWord
  have hmidScratch : mid (placement (.inl 5)) = [] := by
    dsimp only [mid]
    rw [afterWord_frame placement distinct path lengthBound table vertex base 5
      (by decide) (by decide) (by decide) (by decide)]
    exact scratchEmpty
  have hmidOutput : mid (placement (.inl 10)) = base (placement (.inl 10)) :=
    afterWord_frame placement distinct path lengthBound table vertex base 10
      (by decide) (by decide) (by decide) (by decide)
  have hmidEndpoint : mid (placement (.inl 6)) = encodeWord (endpoint table vertex path).val ++
      base (placement (.inl 6)) := by
    dsimp only [mid, afterWord]
    simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_five, PoweringMachineTapes.endpoint_false,
      PoweringMachineTapes.leftEndpoint, ← endpoint_eq_wordEnd] using hword.2
  have hrelation := PoweringMachineRelation.relationTrace (placement (.inl 6)) (lookupTapes placement)
    (lookupTapes_injective placement distinct) (source_outside_lookup placement distinct)
    port (GraphTables.relationIndex (left, right)) (fun q => labels (.inr q)) exit program
    (fun q => atLabels (.inr q)) table (endpoint table vertex path) mid
    (by simpa [lookupTapes, PoweringMachineTapes.table] using hmidTable)
    (by simpa [lookupTapes, PoweringMachineTapes.scratch] using hmidScratch)
    (base (placement (.inl 6))) hmidEndpoint (ambient, false, none) none
  constructor
  · simp only [MachineUnaryEqualityBit.clean]
    rw [steps, Nat.add_comm, Function.iterate_add_apply, hword.1]
    exact hrelation
  · change MachineAffineLookup.finalTapes (lookupTapes placement) _ _ _ _ (lookupTapes placement 3) = _
    rw [MachineAffineLookup.finalTapes_output]
    change encodeWord (bit table vertex path port left right) ++ mid (placement (.inl 10)) = _
    rw [hmidOutput]

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRelationField

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineField

open Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {n d max : Nat}

abbrev State := MachineUnaryEqualityBit.State

def instruction (placement : Tape max → K) : (op : Instruction d) → op.radius ≤ max →
    (Label op → Λ) → Option Λ → Label op → TM2.Stmt (fun _ : K => Bool) Λ (State A)
  | .relation path port a b, bounded, labels, exit =>
      PoweringMachineRelationField.instruction placement path bounded port a b labels exit
  | .equal left right, bounded, labels, exit =>
      PoweringMachineEqualityField.instruction
        ((le_max_left _ _).trans bounded) ((le_max_right _ _).trans bounded)
        placement left.get right.get labels exit

def finalTapes (graph : PortTables.Table n d) (placement : Tape max → K)
    (vertex : Fin n) : (op : Instruction d) → op.radius ≤ max →
      (K → List Bool) → K → List Bool
  | .relation path port a b, bounded, base =>
      PoweringMachineRelationField.finalTapes placement path bounded port a b graph vertex base
  | .equal left right, bounded, base =>
      PoweringMachineEqualityField.finalTapes graph
        ((le_max_left _ _).trans bounded) ((le_max_right _ _).trans bounded)
        placement vertex left.get right.get base

def steps (graph : PortTables.Table n d) (vertex : Fin n) : Instruction d → Nat
  | .relation path port a b => PoweringMachineRelationField.steps path port a b graph vertex
  | .equal left right => PoweringMachineEqualityField.steps graph vertex left.get right.get

structure Ready (graph : PortTables.Table n d) (placement : Tape max → K)
    (vertex : Fin n) (suffix : List Bool) (tapes : K → List Bool) : Prop where
  table : tapes (placement (.inl 0)) = PortTables.tableBits graph
  source : tapes (placement (.inl 1)) = encodeWord vertex.val ++ suffix
  scratch : tapes (placement (.inl 5)) = []
  leftCopy : tapes (placement (.inl 8)) = []
  rightCopy : tapes (placement (.inl 9)) = []

theorem finalTapes_role (graph : PortTables.Table n d) (placement : Tape max → K)
    (distinct : Function.Injective placement) (vertex : Fin n)
    (op : Instruction d) (bounded : op.radius ≤ max) (base : K → List Bool)
    (j : Fin 11) (role : j = 0 ∨ j = 1 ∨ j = 5 ∨ j = 8 ∨ j = 9) :
    finalTapes graph placement vertex op bounded base (placement (.inl j)) =
      base (placement (.inl j)) := by
  cases op with
  | relation path port a b =>
      apply PoweringMachineRelationField.finalTapes_frame placement distinct path bounded
        port a b graph vertex base j
      all_goals rcases role with rfl | rfl | rfl | rfl | rfl <;> decide
  | equal left right =>
      exact PoweringMachineEqualityField.finalTapes_role graph _ _ placement distinct
        vertex left.get right.get base j role

theorem ready_finalTapes (graph : PortTables.Table n d) (placement : Tape max → K)
    (distinct : Function.Injective placement) (vertex : Fin n)
    (op : Instruction d) (bounded : op.radius ≤ max) (base : K → List Bool)
    (suffix : List Bool) (ready : Ready graph placement vertex suffix base) :
    Ready graph placement vertex suffix (finalTapes graph placement vertex op bounded base) := by
  constructor
  · rw [finalTapes_role graph placement distinct vertex op bounded base 0 (by simp)]
    exact ready.table
  · rw [finalTapes_role graph placement distinct vertex op bounded base 1 (by simp)]
    exact ready.source
  · rw [finalTapes_role graph placement distinct vertex op bounded base 5 (by simp)]
    exact ready.scratch
  · rw [finalTapes_role graph placement distinct vertex op bounded base 8 (by simp)]
    exact ready.leftCopy
  · rw [finalTapes_role graph placement distinct vertex op bounded base 9 (by simp)]
    exact ready.rightCopy

theorem finalTapes_other (graph : PortTables.Table n d) (placement : Tape max → K)
    (vertex : Fin n) (op : Instruction d) (bounded : op.radius ≤ max)
    (base : K → List Bool) (k : K) (outside : ∀ i, k ≠ placement i) :
    finalTapes graph placement vertex op bounded base k = base k := by
  cases op with
  | relation path port a b =>
      exact PoweringMachineRelationField.finalTapes_other placement path bounded port a b
        graph vertex base k outside
  | equal left right =>
      exact PoweringMachineEqualityField.finalTapes_other graph _ _ placement vertex
        left.get right.get base k (outside _) (outside _) (outside _) (outside _)
        (outside _) (outside _) (fun i => outside _)

theorem fieldTrace (graph : PortTables.Table n d) (placement : Tape max → K)
    (distinct : Function.Injective placement) (vertex : Fin n)
    (op : Instruction d) (bounded : op.radius ≤ max)
    (labels : Label op → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction placement op bounded labels exit l)
    (base : K → List Bool) (suffix : List Bool)
    (ready : Ready graph placement vertex suffix base) (ambient : A) :
    (advance (TM2.step program))^[steps graph vertex op]
      (some ⟨some (labels (entry op)), MachineUnaryEqualityBit.clean ambient, base⟩) =
      some ⟨exit, MachineUnaryEqualityBit.clean ambient,
        finalTapes graph placement vertex op bounded base⟩ := by
  cases op with
  | relation path port a b =>
      exact (PoweringMachineRelationField.fieldTrace placement distinct path bounded port a b
        labels exit program atLabels graph vertex base ready.table ready.scratch suffix
        ready.source ambient).1
  | equal left right =>
      exact PoweringMachineEqualityField.fieldTrace graph _ _ placement distinct
        vertex left.get right.get labels exit program atLabels base ready.table ready.scratch
        ready.leftCopy ready.rightCopy suffix ready.source ambient

theorem finalTapes_output (graph : PortTables.Table n d) (placement : Tape max → K)
    (distinct : Function.Injective placement) (vertex : Fin n)
    (op : Instruction d) (bounded : op.radius ≤ max) (base : K → List Bool)
    (suffix : List Bool) (ready : Ready graph placement vertex suffix base) :
    finalTapes graph placement vertex op bounded base (placement (.inl 10)) =
      PoweringMachineRow.encodeBit (evaluate graph vertex op) ++ base (placement (.inl 10)) := by
  cases op with
  | relation path port a b =>
      have h := (PoweringMachineRelationField.fieldTrace placement distinct path bounded port a b
        id none (PoweringMachineRelationField.instruction placement path bounded port a b id none)
        (fun _ => rfl) graph vertex base ready.table ready.scratch suffix ready.source ()).2
      have he : ∀ bit : Bool, encodeWord (GraphTables.bitWord bit) =
          PoweringMachineRow.encodeBit bit := by intro bit; cases bit <;> rfl
      simpa only [finalTapes, PoweringMachineRelationField.bit, PoweringMachineRelationField.endpoint,
        evaluate, he] using h
  | equal left right =>
      have h := PoweringMachineEqualityField.finalTapes_output graph
        ((le_max_left _ _).trans bounded) ((le_max_right _ _).trans bounded) placement distinct
        vertex left.get right.get base
      have he : ∀ bit : Bool, MachineUnaryEqualityBit.bitEncoding bit =
          PoweringMachineRow.encodeBit bit := by intro bit; cases bit <;> rfl
      simpa only [finalTapes, PoweringMachineEqualityField.resultBit, PoweringMachineEqualityField.endpoint,
        PoweringReach.wordEnd_eq_walkEnd_ofFn, List.ofFn_get, evaluate, he] using h

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineField

/-! The concrete finite program that produces an entire powered-row input
block. Its static control executes the field plan backwards, so prepending each
computed unary Boolean field leaves the canonical serialized block in order. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachinePlan

open Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {vertices d max : Nat}

def instruction (placement : PoweringMachineTapes.Tape max → K)
    (commands : List (Command d max)) (labels : Label commands → Λ) (exit : Option Λ) :
    Label commands → TM2.Stmt (fun _ : K => Bool) Λ (MachineUnaryEqualityBit.State A) :=
  MachineFiniteSequence.instruction LocalLabel (fun op => PoweringMachineField.entry op.val)
    (fun op => PoweringMachineField.instruction placement op.val op.property)
    commands labels exit

def result (graph : PortTables.Table vertices d) (placement : PoweringMachineTapes.Tape max → K)
    (vertex : Fin vertices) (op : Command d max) (base : K → List Bool) : K → List Bool :=
  PoweringMachineField.finalTapes graph placement vertex op.val op.property base

def finalTapes (graph : PortTables.Table vertices d) (placement : PoweringMachineTapes.Tape max → K)
    (vertex : Fin vertices) (commands : List (Command d max)) (base : K → List Bool) : K → List Bool :=
  MachineFiniteSequence.resultOf (result graph placement vertex) commands base

def steps (graph : PortTables.Table vertices d) (placement : PoweringMachineTapes.Tape max → K)
    (vertex : Fin vertices) (commands : List (Command d max)) (base : K → List Bool) : Nat :=
  MachineFiniteSequence.steps (result graph placement vertex)
    (fun op _ => PoweringMachineField.steps graph vertex op.val) commands base

theorem planTrace (graph : PortTables.Table vertices d)
    (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (vertex : Fin vertices) (commands : List (Command d max))
    (labels : Label commands → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineUnaryEqualityBit.State A))
    (atLabels : ∀ l, program (labels l) = instruction placement commands labels exit l)
    (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineField.Ready graph placement vertex suffix base) (ambient : A) :
    (advance (TM2.step program))^[steps graph placement vertex commands base]
      (some ⟨entry commands labels exit, MachineUnaryEqualityBit.clean ambient, base⟩) =
    some ⟨exit, MachineUnaryEqualityBit.clean ambient,
      finalTapes graph placement vertex commands base⟩ := by
  apply MachineFiniteSequence.trace LocalLabel (fun op => PoweringMachineField.entry op.val)
    (fun op => PoweringMachineField.instruction placement op.val op.property)
    (result graph placement vertex) (fun op _ => PoweringMachineField.steps graph vertex op.val)
    program (PoweringMachineField.Ready graph placement vertex suffix)
    (fun _ => MachineUnaryEqualityBit.clean ambient) id commands
  · intro op _ tapes good
    exact PoweringMachineField.ready_finalTapes graph placement distinct vertex op.val
      op.property tapes suffix good
  · intro op _ localLabels localExit atLocal tapes good
    exact PoweringMachineField.fieldTrace graph placement distinct vertex op.val op.property
      localLabels localExit program atLocal tapes suffix good ambient
  · exact atLabels
  · exact ready

theorem ready_finalTapes (graph : PortTables.Table vertices d)
    (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (vertex : Fin vertices) (commands : List (Command d max)) (base : K → List Bool)
    (suffix : List Bool) (ready : PoweringMachineField.Ready graph placement vertex suffix base) :
    PoweringMachineField.Ready graph placement vertex suffix
      (finalTapes graph placement vertex commands base) := by
  induction commands generalizing base with
  | nil => exact ready
  | cons op commands ih =>
      apply ih
      exact PoweringMachineField.ready_finalTapes graph placement distinct vertex op.val
        op.property base suffix ready

theorem finalTapes_output (graph : PortTables.Table vertices d)
    (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (vertex : Fin vertices) (commands : List (Command d max)) (base : K → List Bool)
    (suffix : List Bool) (ready : PoweringMachineField.Ready graph placement vertex suffix base) :
    finalTapes graph placement vertex commands base (placement (.inl 10)) =
      PoweringMachineRow.encodeBits ((commands.map (fun op => evaluate graph vertex op.val)).reverse) ++
        base (placement (.inl 10)) := by
  induction commands generalizing base with
  | nil => rfl
  | cons op commands ih =>
      have nextReady := PoweringMachineField.ready_finalTapes graph placement distinct vertex
        op.val op.property base suffix ready
      change finalTapes graph placement vertex commands
        (result graph placement vertex op base) (placement (.inl 10)) = _
      dsimp only [result]
      rw [ih _ nextReady, PoweringMachineField.finalTapes_output graph placement distinct vertex
        op.val op.property base suffix ready]
      simp only [List.map_cons, List.reverse_cons, PoweringMachineRow.encodeBits_append,
        PoweringMachineRow.encodeBits, List.append_nil,
        List.append_assoc]

/-- Each command of the actual row plan has a fixed bound of twice the radius. -/
def boundedRowPlan (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    List (Command d (2 * (n + 1))) :=
  List.ofFn fun i : Fin (PoweringMachineRow.inputSize (n + 1) (PoweringRowData.slotCount d n)) =>
    let pair := (PoweringMachineRow.inputEquiv (n + 1) (PoweringRowData.slotCount d n)).symm i
    ⟨directedFieldPlan n ports direction pair.1 pair.2,
      directedFieldPlan_radius n ports direction pair.1 pair.2⟩

theorem boundedRowPlan_values (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    (boundedRowPlan n ports direction).map Subtype.val = rowPlan n ports direction := by
  rw [boundedRowPlan, rowPlan, List.map_ofFn]
  rfl

theorem rowPlan_output (graph : PortTables.Table vertices d)
    (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (placement : PoweringMachineTapes.Tape (2 * (n + 1)) → K)
    (distinct : Function.Injective placement) (vertex : Fin vertices) (base : K → List Bool)
    (suffix : List Bool) (ready : PoweringMachineField.Ready graph placement vertex suffix base) :
    finalTapes graph placement vertex (boundedRowPlan n ports direction).reverse base
      (placement (.inl 10)) =
      PoweringRowData.dataTape graph n (direction, vertex, ports) ++ base (placement (.inl 10)) := by
  rw [finalTapes_output graph placement distinct vertex _ base suffix ready]
  rw [List.map_reverse, List.reverse_reverse, PoweringFieldPlan.dataTape_eq_plan]
  have h := congrArg (List.map (evaluate graph vertex)) (boundedRowPlan_values n ports direction)
  simpa only [List.map_map, Function.comp_def] using
    congrArg (fun bits => PoweringMachineRow.encodeBits bits ++ base (placement (.inl 10))) h

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachinePlan

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRowHeaders

open Turing MachineComposition
open PCP PoweringRowHeaderSemantics
open PoweringMachineTapes

variable {K Λ σ : Type} [DecidableEq K]
variable {vertices d max : Nat}

def affineInstruction (source work output : K) (coefficient offset : Nat)
    (labels : MachineUnaryAffineAt.Label → Λ) (exit : Option Λ) :
    MachineUnaryAffineAt.Label → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | .seed => MachineUnaryAffineAt.seed output offset (labels .scan)
  | .scan => MachineUnaryAffineAt.scan source work output coefficient (labels .scan) (labels .restore)
  | .restore => Reduction.MachineTransfer.loopAt work source id false (labels .restore) exit

/-- Only the coefficient, word, and direction are built into finite control. -/
def instruction (n : Nat) (h : n + 1 ≤ max) (placement : Tape max → K)
    (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (labels : Label n → Λ) (exit : Option Λ) :
    Label n → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | .inl q => affineInstruction (placement (start max)) (placement (scratch max))
      (placement (rowOutput max)) (blockSize d n) (reverseOffset d n ports direction)
      (fun z => labels (.inl z)) (some (labels (tailEntry n direction))) q
  | .inr (.inl q) => PoweringMachineWord.copyInstruction
      (placement (start max)) (placement (scratch max)) (placement (rowOutput max))
      (fun z => labels (.inr (.inl z))) exit q
  | .inr (.inr q) => PoweringMachineWord.instruction (n + 1)
      (placement ∘ headerPlacement h) ports (fun z => labels (.inr (.inr z))) exit q

def finalTapes (input : PortTables.Table vertices d) (n : Nat) (h : n + 1 ≤ max)
    (placement : Tape max → K) (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (base : K → List Bool) : K → List Bool :=
  let mid := afterReverse n placement vertex ports direction base
  if direction then
    PoweringMachineWord.finalTapes input (n + 1) (placement ∘ headerPlacement h) vertex ports mid
  else Function.update mid (placement (rowOutput max))
    (encodeWord vertex.val ++ mid (placement (rowOutput max)))

def steps (input : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) : Nat :=
  (2 * (vertex.val + 1) + 1) +
    if direction then PoweringMachineWord.steps input (n + 1) vertex ports
    else 2 * (vertex.val + 1) + 1

/-- Compose the actual affine and word/copy instructions. The trace and both
header values are derived; the only data premises describe the physical input. -/
theorem headerTrace (input : PortTables.Table vertices d) (n : Nat) (h : n + 1 ≤ max)
    (placement : Tape max → K) (distinct : Function.Injective placement)
    (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (labels : Label n → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction n h placement ports direction labels exit l)
    (base : K → List Bool) (tableWord : base (placement (table max)) = PortTables.tableBits input)
    (scratchEmpty : base (placement (scratch max)) = []) (suffix : List Bool)
    (sourceWord : base (placement (start max)) = encodeWord vertex.val ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps input n vertex ports direction]
      (some ⟨some (labels (entry n)), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), finalTapes input n h placement vertex ports direction base⟩ ∧
    finalTapes input n h placement vertex ports direction base (placement (rowOutput max)) =
      encodeWords (headerWords input n vertex ports direction) ++ base (placement (rowOutput max)) := by
  have hd (i j : Tape max) (hne : i ≠ j) : placement i ≠ placement j :=
    fun eq => hne (distinct eq)
  have hsourceOut : placement (start max) ≠ placement (rowOutput max) :=
    hd _ _ (by simp [start, rowOutput])
  have hscratchOut : placement (scratch max) ≠ placement (rowOutput max) :=
    hd _ _ (by simp [scratch, rowOutput])
  have htableOut : placement (table max) ≠ placement (rowOutput max) :=
    hd _ _ (by simp [table, rowOutput])
  let mid := afterReverse n placement vertex ports direction base
  have hrev := MachineUnaryAffineAt.seededAffineTrace
    (placement (start max)) (placement (scratch max)) (placement (rowOutput max))
    (hd _ _ (by simp [start, scratch])) hsourceOut hscratchOut
    (blockSize d n) (reverseOffset d n ports direction)
    (labels (.inl .seed)) (labels (.inl .scan)) (labels (.inl .restore))
    (some (labels (tailEntry n direction))) program
    (atLabels (.inl .seed)) (atLabels (.inl .scan)) (atLabels (.inl .restore))
    base vertex.val suffix sourceWord scratchEmpty ambient register
  have hreverseTrace : (advance (TM2.step program))^[2 * (vertex.val + 1) + 1]
      (some ⟨some (labels (entry n)), (ambient, register), base⟩) =
      some ⟨some (labels (tailEntry n direction)), (ambient, none), mid⟩ := by
    simpa only [entry, mid, afterReverse, reverseValue] using hrev
  have hmidSource : mid (placement (start max)) = encodeWord vertex.val ++ suffix := by
    simpa only [mid, afterReverse, Function.update_of_ne hsourceOut] using sourceWord
  have hmidScratch : mid (placement (scratch max)) = [] := by
    simpa only [mid, afterReverse, Function.update_of_ne hscratchOut] using scratchEmpty
  have hmidTable : mid (placement (table max)) = PortTables.tableBits input := by
    simpa only [mid, afterReverse, Function.update_of_ne htableOut] using tableWord
  cases direction with
  | false =>
    have hcopy := MachineUnaryAffineAt.seededAffineTrace
      (placement (start max)) (placement (scratch max)) (placement (rowOutput max))
      (hd _ _ (by simp [start, scratch])) hsourceOut hscratchOut 1 0
      (labels (.inr (.inl .seed))) (labels (.inr (.inl .scan)))
      (labels (.inr (.inl .restore))) exit program
      (atLabels (.inr (.inl .seed))) (atLabels (.inr (.inl .scan)))
      (atLabels (.inr (.inl .restore))) mid vertex.val suffix hmidSource hmidScratch ambient none
    constructor
    · rw [steps, ite_eq_right Bool.false_ne_true, Function.iterate_add_apply, hreverseTrace]
      simpa only [tailEntry, Bool.false_eq_true, ite_false, finalTapes, Nat.one_mul,
        Nat.add_zero] using hcopy
    · simp only [finalTapes, Bool.false_eq_true, ite_false, Function.update_self,
        afterReverse, headerWords, tailVertex, encodeWords, List.append_nil, List.append_assoc]
  | true =>
    have hword := PoweringMachineWord.wordTrace input (n + 1)
      (placement ∘ headerPlacement h) (distinct.comp (headerPlacement_injective h)) vertex ports
      (fun z => labels (.inr (.inr z))) exit program (fun z => atLabels (.inr (.inr z))) mid
      (by simpa only [Function.comp_apply, headerPlacement_table] using hmidTable)
      (by simpa only [Function.comp_apply, headerPlacement_scratch] using hmidScratch)
      suffix (by simpa only [Function.comp_apply, headerPlacement_start] using hmidSource) ambient none
    constructor
    · rw [steps, ite_eq_left rfl, Nat.add_comm, Function.iterate_add_apply, hreverseTrace]
      simpa only [tailEntry, ite_true, if_true, finalTapes] using hword.1
    · have hout := hword.2
      simp only [Function.comp_apply, headerPlacement_output] at hout
      simpa only [finalTapes, ite_true, if_true, mid, afterReverse, Function.update_self,
        headerWords, tailVertex, encodeWords, List.append_nil, List.append_assoc] using hout

theorem finalTapes_other (input : PortTables.Table vertices d) (n : Nat) (h : n + 1 ≤ max)
    (placement : Tape max → K) (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (base : K → List Bool) (k : K)
    (hquery : k ≠ placement (query max)) (hscan : k ≠ placement (scan max))
    (hreverse : k ≠ placement (reverse max)) (houtput : k ≠ placement (rowOutput max))
    (hpositions : ∀ i : Fin (n + 1), k ≠ placement (.inr (Fin.castLE h i))) :
    finalTapes input n h placement vertex ports direction base k = base k := by
  cases direction with
  | false => simp only [finalTapes, Bool.false_eq_true, ite_false,
      Function.update_of_ne houtput, afterReverse]
  | true =>
    let mid := afterReverse n placement vertex ports true base
    have hw := PoweringMachineWord.finalTapes_other input (n + 1)
      (placement ∘ headerPlacement h) vertex ports mid k
      (by simpa only [Function.comp_apply, headerPlacement_query] using hquery)
      (by simpa only [Function.comp_apply, headerPlacement_scan] using hscan)
      (by simpa only [Function.comp_apply, headerPlacement_reverse] using hreverse)
      (by simpa only [Function.comp_apply, headerPlacement_output] using houtput)
      (fun i => by simpa only [Function.comp_apply, headerPlacement_succ] using hpositions i)
    calc
      _ = mid k := hw
      _ = base k := by simp only [mid, afterReverse, Function.update_of_ne houtput]

/-- In particular, table 0, start 1, scratch 5, and saved endpoint/copy tapes
6--9 survive the header phase. Only roles 2, 3, 4, 10 and trajectory tapes may change. -/
theorem finalTapes_shared (input : PortTables.Table vertices d) (n : Nat) (h : n + 1 ≤ max)
    (placement : Tape max → K) (distinct : Function.Injective placement)
    (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (base : K → List Bool) (i : Fin 11)
    (hquery : i ≠ 2) (hscan : i ≠ 3) (hreverse : i ≠ 4) (houtput : i ≠ 10) :
    finalTapes input n h placement vertex ports direction base (placement (.inl i)) =
      base (placement (.inl i)) := by
  apply finalTapes_other input n h placement vertex ports direction base
  · intro heq; exact hquery (Sum.inl.inj (distinct heq))
  · intro heq; exact hscan (Sum.inl.inj (distinct heq))
  · intro heq; exact hreverse (Sum.inl.inj (distinct heq))
  · intro heq; exact houtput (Sum.inl.inj (distinct heq))
  · intro j heq; cases distinct heq

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

def copyInstruction (source scratch output : K)
    (labels : MachineUnaryAffineAt.Label → Λ) (exit : Option Λ) :
    MachineUnaryAffineAt.Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .seed => MachineUnaryAffineAt.seed output 0 (labels .scan)
  | .scan => MachineUnaryAffineAt.scan source scratch output 1 (labels .scan) (labels .restore)
  | .restore => Reduction.MachineTransfer.loopAt scratch source id false (labels .restore) exit

/-- The labels contain two fixed affine copies and one fixed list of drains. -/
def instruction (enumeration : Fin N ≃ K) (headerV headerD output scratch : K)
    (labels : Label enumeration output → Λ) :
    Label enumeration output → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .inl l => copyInstruction headerD scratch output (fun q => labels (.inl q))
      (some (labels (.inr (.inl .seed)))) l
  | .inr (.inl l) => copyInstruction headerV scratch output
      (fun q => labels (.inr (.inl q)))
      (MachineDrainMany.entry (MachineDrainMany.workTapes enumeration output)
        (fun q => labels (.inr (.inr q))) none) l
  | .inr (.inr l) => MachineDrainMany.instruction
      (MachineDrainMany.workTapes enumeration output) (fun q => labels (.inr (.inr q))) none l

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

open Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {vertices d max : Nat}

/-- This is the actual static instruction list's length, not a supplied bound. -/
@[simp] theorem boundedRowPlan_length (n : Nat)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    (PoweringMachinePlan.boundedRowPlan n ports direction).length =
      PoweringMachineRow.inputSize (n + 1) (PoweringRowData.slotCount d n) := by
  simp only [PoweringMachinePlan.boundedRowPlan, List.length_ofFn]

/-- For fixed degree and radius this is affine in the serialized graph length. -/
def rowBudget (d n inputLength : Nat) : Nat :=
  PoweringMachineRow.inputSize (n + 1) (PoweringRowData.slotCount d n) *
    fieldBudget (2 * (n + 1)) inputLength

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

open Turing MachineComposition PCP
open MachineFixedBlockMap

variable {K Λ : Type} [DecidableEq K] {vertices d : Nat}

abbrev bufferSize (d n : Nat) := PoweringMachineRow.inputSize (n + 1) (PoweringRowData.slotCount d n)
abbrev State (d n : Nat) := PoweringMasterState.Master (bufferSize d n)

def commands (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) :=
  (PoweringMachinePlan.boundedRowPlan n ports direction).reverse

abbrev Label (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) :=
  PoweringMachinePlan.Label (commands n ports direction) ⊕
    (Unit ⊕ PoweringMachineRowHeaders.Label n)

/-- A finite main label also exists for an empty command list. -/
def planMain {max : Nat} {E : Type}
    (ops : List (PoweringMachinePlan.Command d max)) (fallback : E) :
    PoweringMachinePlan.Label ops ⊕ E :=
  match ops with
  | [] => .inr fallback
  | op :: _ => .inl (.inl (PoweringMachineField.entry op.val))

theorem plan_entry_eq {max : Nat} {E : Type}
    (ops : List (PoweringMachinePlan.Command d max)) (fallback : E)
    (labels : PoweringMachinePlan.Label ops ⊕ E → Λ) :
    PoweringMachinePlan.entry ops (fun l => labels (.inl l))
      (some (labels (.inr fallback))) = some (labels (planMain ops fallback)) := by
  cases ops <;> rfl

def entry (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) : Label n ports direction :=
  planMain (commands n ports direction) (.inl ())

def instruction (n : Nat) (placement : PoweringMachineTapes.Tape (capacity n) → K)
    (output : K) (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (labels : Label n ports direction → Λ) (exit : Option Λ) :
    Label n ports direction → TM2.Stmt (fun _ : K => Bool) Λ (State d n)
  | .inl q => PoweringMachinePlan.instruction placement (commands n ports direction)
      (fun z => labels (.inl z)) (some (labels (.inr (.inl ())))) q
  | .inr (.inl _) => PoweringMasterState.rowAt (t := n + 1) (placement (.inl 10)) output
      (PoweringRowData.fixedLabelAt d n) (some (labels (.inr (.inr (PoweringMachineRowHeaders.entry n)))))
  | .inr (.inr q) => PoweringMachineRowHeaders.instruction n (by unfold capacity; omega)
      (headerPlacement placement output) ports direction (fun z => labels (.inr (.inr z))) exit q

def afterPlan (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool) : K → List Bool :=
  PoweringMachinePlan.finalTapes graph placement vertex (commands n ports direction) base

def rowRelation (graph : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) : List Bool :=
  encodeWords (GenericGraphTables.relationWords (PoweringTables.table graph n).rows[
    PoweringEnumeration.encodeDart vertices d n (direction, vertex, ports)].relation)

def rowWords (graph : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) : List Nat :=
  GenericGraphTables.rowWords (PoweringTables.table graph n).rows[
    PoweringEnumeration.encodeDart vertices d n (direction, vertex, ports)]

def afterEmit (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (output : K) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool) : K → List Bool :=
  let mid := afterPlan graph n placement vertex ports direction base
  Function.update (Function.update mid (placement (.inl 10)) []) output
    (rowRelation graph n vertex ports direction ++ mid output)

def finalTapes (graph : PortTables.Table vertices d)
    (n : Nat) (placement : PoweringMachineTapes.Tape (capacity n) → K) (output : K)
    (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (base : K → List Bool) : K → List Bool :=
  PoweringMachineRowHeaders.finalTapes graph n (by unfold capacity; omega)
    (headerPlacement placement output) vertex ports direction
    (afterEmit graph n placement output vertex ports direction base)

def planSteps {max : Nat} (graph : PortTables.Table vertices d) (vertex : Fin vertices) :
    List (PoweringMachinePlan.Command d max) → Nat
  | [] => 0
  | op :: ops => PoweringMachineField.steps graph vertex op.val + planSteps graph vertex ops

theorem planSteps_eq {max : Nat} (graph : PortTables.Table vertices d)
    (placement : PoweringMachineTapes.Tape max → K) (vertex : Fin vertices)
    (ops : List (PoweringMachinePlan.Command d max)) (base : K → List Bool) :
    PoweringMachinePlan.steps graph placement vertex ops base = planSteps graph vertex ops := by
  induction ops generalizing base with
  | nil => rfl
  | cons op ops ih =>
      change PoweringMachineField.steps graph vertex op.val +
        PoweringMachinePlan.steps graph placement vertex ops
          (PoweringMachinePlan.result graph placement vertex op base) = _
      rw [ih]
      rfl

def steps (graph : PortTables.Table vertices d) (vertex : Fin vertices)
    (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) : Nat :=
  planSteps graph vertex (commands n ports direction) + 1 +
    PoweringMachineRowHeaders.steps graph n vertex ports direction

def Ready (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (vertex : Fin vertices)
    (suffix : List Bool) (base : K → List Bool) : Prop :=
  PoweringMachineField.Ready graph placement vertex suffix base ∧ base (placement (.inl 10)) = []

theorem plan_other {max : Nat} (graph : PortTables.Table vertices d)
    (placement : PoweringMachineTapes.Tape max → K) (vertex : Fin vertices)
    (ops : List (PoweringMachinePlan.Command d max)) (base : K → List Bool)
    (k : K) (outside : ∀ i, k ≠ placement i) :
    PoweringMachinePlan.finalTapes graph placement vertex ops base k = base k := by
  induction ops generalizing base with
  | nil => rfl
  | cons op ops ih =>
      change PoweringMachinePlan.finalTapes graph placement vertex ops
        (PoweringMachinePlan.result graph placement vertex op base) k = _
      rw [ih]
      exact PoweringMachineField.finalTapes_other graph placement vertex op.val op.property base k outside

theorem afterEmit_data (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (output : K)
    (outside : ∀ i, output ≠ placement i) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool) :
    afterEmit graph n placement output vertex ports direction base (placement (.inl 10)) = [] := by
  simp only [afterEmit, Function.update_of_ne (Ne.symm (outside _)), Function.update_self]

theorem afterEmit_role (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool)
    (j : Fin 11) (hj : j ≠ 10) :
    afterEmit graph n placement output vertex ports direction base (placement (.inl j)) =
      afterPlan graph n placement vertex ports direction base (placement (.inl j)) := by
  have hdata : placement (.inl j) ≠ placement (.inl 10) := fun h => hj (Sum.inl.inj (distinct h))
  simp only [afterEmit, Function.update_of_ne (Ne.symm (outside _)), Function.update_of_ne hdata]

theorem afterEmit_ready (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool)
    (suffix : List Bool) (ready : Ready graph n placement vertex suffix base) :
    Ready graph n placement vertex suffix (afterEmit graph n placement output vertex ports direction base) := by
  have hp := PoweringMachinePlan.ready_finalTapes graph placement distinct vertex
    (commands n ports direction) base suffix ready.1
  constructor
  · constructor
    · rw [afterEmit_role graph n placement distinct output outside vertex ports direction base 0 (by decide)]
      exact hp.table
    · rw [afterEmit_role graph n placement distinct output outside vertex ports direction base 1 (by decide)]
      exact hp.source
    · rw [afterEmit_role graph n placement distinct output outside vertex ports direction base 5 (by decide)]
      exact hp.scratch
    · rw [afterEmit_role graph n placement distinct output outside vertex ports direction base 8 (by decide)]
      exact hp.leftCopy
    · rw [afterEmit_role graph n placement distinct output outside vertex ports direction base 9 (by decide)]
      exact hp.rightCopy
  · exact afterEmit_data graph n placement output outside vertex ports direction base

theorem finalTapes_data (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool) :
    finalTapes graph n placement output vertex ports direction base (placement (.inl 10)) = [] := by
  have hother := headerPlacement_excludes_data placement distinct output outside
  calc
    finalTapes graph n placement output vertex ports direction base (placement (.inl 10)) =
        afterEmit graph n placement output vertex ports direction base (placement (.inl 10)) :=
      PoweringMachineRowHeaders.finalTapes_other _ _ _ _ _ _ _ _ _
        (hother _) (hother _) (hother _) (hother _) (fun i => hother _)
    _ = [] := afterEmit_data graph n placement output outside vertex ports direction base

theorem finalTapes_ready (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool)
    (suffix : List Bool) (ready : Ready graph n placement vertex suffix base) :
    Ready graph n placement vertex suffix (finalTapes graph n placement output vertex ports direction base) := by
  have hm := afterEmit_ready graph n placement distinct output outside vertex ports direction base suffix ready
  have hrole (j : Fin 11) (h₂ : j ≠ 2) (h₃ : j ≠ 3) (h₄ : j ≠ 4) (h₁₀ : j ≠ 10) :
      finalTapes graph n placement output vertex ports direction base (placement (.inl j)) =
        afterEmit graph n placement output vertex ports direction base (placement (.inl j)) := by
    have h := PoweringMachineRowHeaders.finalTapes_shared graph n (by unfold capacity; omega)
      (headerPlacement placement output) (headerPlacement_injective placement distinct output outside)
      vertex ports direction (afterEmit graph n placement output vertex ports direction base) j h₂ h₃ h₄ h₁₀
    dsimp only [finalTapes]
    simpa only [headerPlacement, ite_eq_right (show (Sum.inl j : PoweringMachineTapes.Tape (capacity n)) ≠ .inl 10 from
      fun heq => h₁₀ (Sum.inl.inj heq))] using h
  constructor
  · constructor
    · rw [hrole 0 (by decide) (by decide) (by decide) (by decide)]; exact hm.1.table
    · rw [hrole 1 (by decide) (by decide) (by decide) (by decide)]; exact hm.1.source
    · rw [hrole 5 (by decide) (by decide) (by decide) (by decide)]; exact hm.1.scratch
    · rw [hrole 8 (by decide) (by decide) (by decide) (by decide)]; exact hm.1.leftCopy
    · rw [hrole 9 (by decide) (by decide) (by decide) (by decide)]; exact hm.1.rightCopy
  · exact finalTapes_data graph n placement distinct output outside vertex ports direction base

theorem finalTapes_other (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (output : K)
    (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (base : K → List Bool) (k : K) (hout : k ≠ output) (outside : ∀ i, k ≠ placement i) :
    finalTapes graph n placement output vertex ports direction base k = base k := by
  have hh : ∀ i, k ≠ headerPlacement placement output i := by
    intro i
    by_cases hi : i = .inl 10
    · simpa [headerPlacement, hi] using hout
    · simpa [headerPlacement, hi] using outside i
  calc
    finalTapes graph n placement output vertex ports direction base k =
        afterEmit graph n placement output vertex ports direction base k :=
      PoweringMachineRowHeaders.finalTapes_other _ _ _ _ _ _ _ _ _
        (hh _) (hh _) (hh _) (hh _) (fun i => hh _)
    _ = afterPlan graph n placement vertex ports direction base k := by
      simp only [afterEmit, Function.update_of_ne hout, Function.update_of_ne (outside _)]
    _ = base k := plan_other graph placement vertex _ base k outside

theorem rowBlock_eq_rowRelation (graph : PortTables.Table vertices d) (n : Nat)
    (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    PoweringMachineRow.encodeBits (List.ofFn (PoweringMachineRow.rowBlock
      (PoweringRowData.fixedLabelAt d n) (PoweringRowData.rowBits graph n (direction, vertex, ports)))) =
      rowRelation graph n vertex ports direction := by
  calc
    _ = encodeWords (GenericGraphTables.relationWords
        (PoweringRowData.emittedRelation graph n (direction, vertex, ports))) :=
      PoweringRowData.rowBlock_unary graph n (direction, vertex, ports)
    _ = _ := by
      have h := PoweringRowData.emittedRelation_table graph n
        (PoweringEnumeration.encodeDart vertices d n (direction, vertex, ports))
      rw [PoweringEnumeration.decodeDart_encodeDart] at h
      exact congrArg (fun relation : GenericGraphTables.RelationTable (PoweringTables.labelCount d n) =>
        encodeWords (GenericGraphTables.relationWords relation)) h

/-- The full serialized row is prepended to the caller's existing output. -/
theorem finalTapes_output (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool)
    (suffix : List Bool) (ready : Ready graph n placement vertex suffix base) :
    finalTapes graph n placement output vertex ports direction base output =
      encodeWords (rowWords graph n vertex ports direction) ++ base output := by
  have hm := afterEmit_ready graph n placement distinct output outside vertex ports direction base suffix ready
  have hh := (PoweringMachineRowHeaders.headerTrace graph n (by unfold capacity; omega)
    (headerPlacement placement output) (headerPlacement_injective placement distinct output outside)
    vertex ports direction id none
    (PoweringMachineRowHeaders.instruction n (by unfold capacity; omega)
      (headerPlacement placement output) ports direction id none) (fun _ => rfl)
    (afterEmit graph n placement output vertex ports direction base)
    (by simpa [headerPlacement, PoweringMachineTapes.table] using hm.1.table)
    (by simpa [headerPlacement, PoweringMachineTapes.scratch] using hm.1.scratch) suffix
    (by simpa [headerPlacement, PoweringMachineTapes.start] using hm.1.source) () none).2
  simp only [PoweringMachineTapes.rowOutput, headerPlacement_output] at hh
  calc
    finalTapes graph n placement output vertex ports direction base output =
        encodeWords (PoweringRowHeaderSemantics.headerWords graph n vertex ports direction) ++
          afterEmit graph n placement output vertex ports direction base output := hh
    _ = encodeWords (PoweringRowHeaderSemantics.headerWords graph n vertex ports direction) ++
        (rowRelation graph n vertex ports direction ++ base output) := by
      simp only [afterEmit, Function.update_self]
      rw [show afterPlan graph n placement vertex ports direction base output = base output from
        plan_other graph placement vertex _ base output outside]
    _ = _ := PoweringRowHeaderSemantics.header_relation_bits graph n vertex ports direction (base output)

/-- The complete row producer executes its concrete plan, one row transition,
and the concrete two-header writer. No local execution hypothesis is assumed. -/
theorem rowTrace (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (labels : Label n ports direction → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State d n))
    (atLabels : ∀ l, program (labels l) = instruction n placement output ports direction labels exit l)
    (base : K → List Bool) (suffix : List Bool) (ready : Ready graph n placement vertex suffix base) :
    (advance (TM2.step program))^[steps graph vertex n ports direction]
      (some ⟨some (labels (entry n ports direction)), PoweringMasterState.clean (bufferSize d n), base⟩) =
      some ⟨exit, PoweringMasterState.clean (bufferSize d n),
        finalTapes graph n placement output vertex ports direction base⟩ := by
  have hp := PoweringMachinePlan.planTrace graph placement distinct vertex (commands n ports direction)
    (fun q => labels (.inl q)) (some (labels (.inr (.inl ())))) program
    (fun q => atLabels (.inl q)) base suffix ready.1 (emptyBuffer (bufferSize d n))
  rw [planSteps_eq, plan_entry_eq] at hp
  let mid := afterPlan graph n placement vertex ports direction base
  have hinput : mid (placement (.inl 10)) = PoweringMachineRow.encodeBits
      (List.ofFn (PoweringRowData.rowBits graph n (direction, vertex, ports))) ++ [] := by
    dsimp only [mid, afterPlan, commands]
    have h := PoweringMachinePlan.rowPlan_output graph n ports direction placement distinct vertex base suffix ready.1
    simpa only [ready.2, List.append_nil, PoweringRowData.dataTape_eq] using h
  have hr := PoweringMasterState.step_rowAt_clean (t := n + 1) (placement (.inl 10)) output
    (PoweringRowData.fixedLabelAt d n)
    (some (labels (.inr (.inr (PoweringMachineRowHeaders.entry n))))) program (labels (.inr (.inl ())))
    (atLabels (.inr (.inl ()))) (Ne.symm (outside _))
    (PoweringRowData.rowBits graph n (direction, vertex, ports))
    (emptyBuffer (bufferSize d n)) [] mid hinput
  rw [rowBlock_eq_rowRelation] at hr
  have hm := afterEmit_ready graph n placement distinct output outside vertex ports direction base suffix ready
  have hh := (PoweringMachineRowHeaders.headerTrace graph n (by unfold capacity; omega)
    (headerPlacement placement output) (headerPlacement_injective placement distinct output outside)
    vertex ports direction (fun q => labels (.inr (.inr q))) exit program
    (fun q => atLabels (.inr (.inr q)))
    (afterEmit graph n placement output vertex ports direction base)
    (by simpa [headerPlacement, PoweringMachineTapes.table] using hm.1.table)
    (by simpa [headerPlacement, PoweringMachineTapes.scratch] using hm.1.scratch) suffix
    (by simpa [headerPlacement, PoweringMachineTapes.start] using hm.1.source)
    (emptyBuffer (bufferSize d n), false, none) none).1
  rw [steps, Nat.add_comm, Function.iterate_add_apply, Function.iterate_succ_apply']
  change (advance (TM2.step program))^[PoweringMachineRowHeaders.steps graph n vertex ports direction]
    (advance (TM2.step program) ((advance (TM2.step program))^[planSteps graph vertex (commands n ports direction)]
      (some ⟨some (labels (planMain (commands n ports direction) (.inl ()))),
        MachineUnaryEqualityBit.clean (emptyBuffer (bufferSize d n)), base⟩))) = _
  rw [hp]
  simp only [advance_some]
  change (advance (TM2.step program))^[PoweringMachineRowHeaders.steps graph n vertex ports direction]
    (TM2.step program ⟨some (labels (.inr (.inl ()))),
      PoweringMasterState.withBuffer (emptyBuffer (bufferSize d n)), mid⟩) = _
  rw [hr]
  exact hh

def budget (d n inputLength : Nat) : Nat :=
  PoweringPlanBudget.rowBudget d n inputLength + 1 +
    ((14 * (n + 1) + 4) * inputLength + 12 * (n + 1) + 6)

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

theorem dartCount_eq_vertex_blocks (vertices d n : Nat) :
    dartCount vertices d n = vertices * blockSize d n := by
  simp only [blockSize]
  unfold dartCount
  ac_rfl

/-- The index of a stored row within the consecutive block of vertex `v`. -/
def blockIndex {vertices : Nat} (d n : Nat) (v : Fin vertices)
    (j : Fin (blockSize d n)) : Fin (dartCount vertices d n) :=
  Fin.cast (dartCount_eq_vertex_blocks vertices d n).symm
    (finProdFinEquiv (v, j))

@[simp] theorem blockIndex_val {vertices : Nat} (d n : Nat) (v : Fin vertices)
    (j : Fin (blockSize d n)) :
    (blockIndex d n v j).val = blockSize d n * v.val + j.val := by
  change j.val + blockSize d n * v.val = blockSize d n * v.val + j.val
  exact Nat.add_comm _ _

/-- The consecutive block is the actual vertex-major recorded-walk order. -/
theorem blockIndex_eq_encodeDart {vertices : Nat} (d n : Nat) (v : Fin vertices)
    (p : Fin (n + 1) → Fin d) (direction : Bool) :
    blockIndex d n v (dartBlockEquiv d n (p, direction)) =
      encodeDart vertices d n (direction, (v, p)) := by
  apply Fin.ext
  erw [blockIndex_val]

/-- Exactly the stored rows at positions `B*v, ..., B*v+B-1`. -/
def vertexRows {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (v : Fin vertices) :
    List (GenericGraphTables.DartRow (labelCount d n) vertices (dartCount vertices d n)) :=
  List.ofFn (fun j : Fin (blockSize d n) => (table input n).rows[blockIndex d n v j])

/-- All fields of these stored rows, in their actual codec order. -/
def vertexRowWords {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (v : Fin vertices) : List Nat :=
  (vertexRows input n v).flatMap GenericGraphTables.rowWords

/-- Actual unary serialization of the complete vertex block. -/
def vertexRowBits {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (v : Fin vertices) : List Bool :=
  encodeWords (vertexRowWords input n v)

@[simp] theorem vertexRows_length {vertices d : Nat}
    (input : PortTables.Table vertices d) (n : Nat) (v : Fin vertices) :
    (vertexRows input n v).length = blockSize d n := by
  simp only [vertexRows]
  exact List.length_ofFn

/-- Every actual stored row occurs once in its vertex's consecutive block. -/
theorem rowList_eq_vertexRows {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) :
    GenericGraphTables.rowList (table input n) =
      (List.finRange vertices).flatMap (vertexRows input n) := by
  exact vector_blocks (dartCount_eq_vertex_blocks vertices d n) (table input n).rows

/-- The full word stream, including its two header fields, in vertex order. -/
theorem outputWords_vertexRows {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) :
    GenericGraphTables.tableWords (table input n) =
      [vertices, dartCount vertices d n] ++
        (List.finRange vertices).flatMap (vertexRowWords input n) := by
  change [vertices, dartCount vertices d n] ++
      (GenericGraphTables.rowList (table input n)).flatMap GenericGraphTables.rowWords = _
  rw [rowList_eq_vertexRows]
  erw [List.flatMap_assoc]
  rfl

theorem outputBits_vertexRows {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) :
    outputBits input n = encodeWords [vertices, dartCount vertices d n] ++
      (List.finRange vertices).flatMap (vertexRowBits input n) := by
  unfold outputBits GenericGraphTables.tableBits
  rw [outputWords_vertexRows, encodeWords_append, encodeWords_flatMap]
  rfl

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

abbrev Command (d n : Nat) := Fin (PoweringTableLayout.blockSize d n)

def ports {d n : Nat} (j : Command d n) : Fin (n + 1) → Fin d :=
  ((PoweringEnumeration.dartBlockEquiv d n).symm j).1

def direction {d n : Nat} (j : Command d n) : Bool :=
  ((PoweringEnumeration.dartBlockEquiv d n).symm j).2

def commands (d n : Nat) : List (Command d n) := (List.ofFn id).reverse

@[simp] theorem commands_length (d n : Nat) :
    (commands d n).length = PoweringTableLayout.blockSize d n := by
  simp only [commands, List.length_reverse, List.length_ofFn]

abbrev LocalLabel (j : Command d n) := PoweringMachineRowBody.Label n (ports j) (direction j)
abbrev SequenceLabel (ops : List (Command d n)) := MachineFiniteSequence.Label LocalLabel ops
abbrev Label (d n : Nat) := SequenceLabel (commands d n)
abbrev State (d n : Nat) := PoweringMachineRowBody.State d n

def sequenceEntry (ops : List (Command d n)) (labels : SequenceLabel ops → Λ)
    (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry LocalLabel
    (fun j => PoweringMachineRowBody.entry n (ports j) (direction j)) ops labels exit

def entry (d n : Nat) (labels : Label d n → Λ) (exit : Option Λ) : Option Λ :=
  sequenceEntry (commands d n) labels exit

def sequenceInstruction (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (ops : List (Command d n)) (labels : SequenceLabel ops → Λ)
    (exit : Option Λ) : SequenceLabel ops → TM2.Stmt (fun _ : K => Bool) Λ (State d n) :=
  MachineFiniteSequence.instruction LocalLabel
    (fun j => PoweringMachineRowBody.entry n (ports j) (direction j))
    (fun j => PoweringMachineRowBody.instruction n placement output (ports j) (direction j))
    ops labels exit

def instruction (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (labels : Label d n → Λ) (exit : Option Λ) :
    Label d n → TM2.Stmt (fun _ : K => Bool) Λ (State d n) :=
  sequenceInstruction n placement output (commands d n) labels exit

def result (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (j : Command d n) (base : K → List Bool) :
    K → List Bool :=
  PoweringMachineRowBody.finalTapes graph n placement output vertex (ports j) (direction j) base

def sequenceTapes (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (ops : List (Command d n)) (base : K → List Bool) :
    K → List Bool :=
  MachineFiniteSequence.resultOf (result graph n placement output vertex) ops base

def finalTapes (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (base : K → List Bool) : K → List Bool :=
  sequenceTapes graph n placement output vertex (commands d n) base

def sequenceSteps (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (ops : List (Command d n)) (base : K → List Bool) : Nat :=
  MachineFiniteSequence.steps (result graph n placement output vertex)
    (fun j _ => PoweringMachineRowBody.steps graph vertex n (ports j) (direction j)) ops base

def costSum (graph : PortTables.Table vertices d) (vertex : Fin vertices) (n : Nat) :
    List (Command d n) → Nat
  | [] => 0
  | j :: ops => PoweringMachineRowBody.steps graph vertex n (ports j) (direction j) +
      costSum graph vertex n ops

theorem sequenceSteps_eq (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (ops : List (Command d n)) (base : K → List Bool) :
    sequenceSteps graph n placement output vertex ops base = costSum graph vertex n ops := by
  induction ops generalizing base with
  | nil => rfl
  | cons j ops ih =>
      change PoweringMachineRowBody.steps graph vertex n (ports j) (direction j) +
        sequenceSteps graph n placement output vertex ops
          (result graph n placement output vertex j base) = _
      rw [ih]
      rfl

def steps (graph : PortTables.Table vertices d) (vertex : Fin vertices) (n : Nat) : Nat :=
  costSum graph vertex n (commands d n)

def budget (d n inputLength : Nat) : Nat :=
  PoweringTableLayout.blockSize d n * PoweringMachineRowBody.budget d n inputLength

theorem sequenceTrace (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (ops : List (Command d n))
    (labels : SequenceLabel ops → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State d n))
    (atLabels : ∀ l, program (labels l) = sequenceInstruction n placement output ops labels exit l)
    (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    (advance (TM2.step program))^[sequenceSteps graph n placement output vertex ops base]
      (some ⟨sequenceEntry ops labels exit,
        PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n), base⟩) =
      some ⟨exit, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        sequenceTapes graph n placement output vertex ops base⟩ := by
  apply MachineFiniteSequence.trace LocalLabel
    (fun j => PoweringMachineRowBody.entry n (ports j) (direction j))
    (fun j => PoweringMachineRowBody.instruction n placement output (ports j) (direction j))
    (result graph n placement output vertex)
    (fun j _ => PoweringMachineRowBody.steps graph vertex n (ports j) (direction j))
    program (PoweringMachineRowBody.Ready graph n placement vertex suffix)
    (fun _ => PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n)) id ops
  · intro j _ tapes good
    exact PoweringMachineRowBody.finalTapes_ready graph n placement distinct output outside
      vertex (ports j) (direction j) tapes suffix good
  · intro j _ localLabels localExit atLocal tapes good
    exact PoweringMachineRowBody.rowTrace graph n placement distinct output outside vertex
      (ports j) (direction j) localLabels localExit program atLocal tapes suffix good
  · exact atLabels
  · exact ready

theorem vertexTrace (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (labels : Label d n → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State d n))
    (atLabels : ∀ l, program (labels l) = instruction n placement output labels exit l)
    (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    (advance (TM2.step program))^[steps graph vertex n]
      (some ⟨entry d n labels exit,
        PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n), base⟩) =
      some ⟨exit, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        finalTapes graph n placement output vertex base⟩ := by
  have h := sequenceTrace graph n placement distinct output outside vertex (commands d n)
    labels exit program atLabels base suffix ready
  rw [sequenceSteps_eq] at h
  exact h

theorem sequenceTapes_ready (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (ops : List (Command d n)) (base : K → List Bool)
    (suffix : List Bool) (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    PoweringMachineRowBody.Ready graph n placement vertex suffix
      (sequenceTapes graph n placement output vertex ops base) := by
  induction ops generalizing base with
  | nil => exact ready
  | cons j ops ih =>
      apply ih
      exact PoweringMachineRowBody.finalTapes_ready graph n placement distinct output outside
        vertex (ports j) (direction j) base suffix ready

theorem finalTapes_ready (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    PoweringMachineRowBody.Ready graph n placement vertex suffix
      (finalTapes graph n placement output vertex base) :=
  sequenceTapes_ready graph n placement distinct output outside vertex (commands d n) base suffix ready

theorem sequenceTapes_other (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (ops : List (Command d n)) (base : K → List Bool)
    (k : K) (hout : k ≠ output) (outside : ∀ i, k ≠ placement i) :
    sequenceTapes graph n placement output vertex ops base k = base k := by
  induction ops generalizing base with
  | nil => rfl
  | cons j ops ih =>
      change sequenceTapes graph n placement output vertex ops
        (result graph n placement output vertex j base) k = _
      rw [ih]
      exact PoweringMachineRowBody.finalTapes_other graph n placement output vertex
        (ports j) (direction j) base k hout outside

theorem finalTapes_other (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (base : K → List Bool)
    (k : K) (hout : k ≠ output) (outside : ∀ i, k ≠ placement i) :
    finalTapes graph n placement output vertex base k = base k :=
  sequenceTapes_other graph n placement output vertex (commands d n) base k hout outside

def rowBits (graph : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (j : Command d n) : List Bool :=
  encodeWords (PoweringMachineRowBody.rowWords graph n vertex (ports j) (direction j))

/-- Decoding a command gives exactly its existing vertex-block row index. -/
theorem blockIndex_eq_encodeDart (n : Nat) (vertex : Fin vertices) (j : Command d n) :
    PoweringTableLayout.blockIndex d n vertex j =
      PoweringEnumeration.encodeDart vertices d n (direction j, vertex, ports j) := by
  have h := PoweringTableLayout.blockIndex_eq_encodeDart d n vertex (ports j) (direction j)
  simp only [ports, direction, Prod.mk.eta] at h
  erw [Equiv.apply_symm_apply] at h
  exact h

theorem rowBits_eq (graph : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (j : Command d n) :
    rowBits graph n vertex j = encodeWords (GenericGraphTables.rowWords
      (PoweringTables.table graph n).rows[PoweringTableLayout.blockIndex d n vertex j]) := by
  rw [blockIndex_eq_encodeDart]
  rfl

theorem rows_eq_vertexRowBits (graph : PortTables.Table vertices d) (n : Nat)
    (vertex : Fin vertices) :
    (List.ofFn id : List (Command d n)).flatMap (rowBits graph n vertex) =
      PoweringTableLayout.vertexRowBits graph n vertex := by
  have hrows : (List.ofFn id : List (Command d n)).map
      (fun j => (PoweringTables.table graph n).rows[PoweringTableLayout.blockIndex d n vertex j]) =
      List.ofFn (fun j : Command d n =>
        (PoweringTables.table graph n).rows[PoweringTableLayout.blockIndex d n vertex j]) := by
    simp only [List.map_ofFn, Function.comp_id]
  calc
    _ = (List.ofFn id : List (Command d n)).flatMap (fun j => encodeWords
        (GenericGraphTables.rowWords
          (PoweringTables.table graph n).rows[PoweringTableLayout.blockIndex d n vertex j])) := by
      apply congrArg (List.flatMap · (List.ofFn id))
      funext j
      exact rowBits_eq graph n vertex j
    _ = PoweringTableLayout.vertexRowBits graph n vertex := by
      unfold PoweringTableLayout.vertexRowBits PoweringTableLayout.vertexRowWords
        PoweringTableLayout.vertexRows
      rw [encodeWords_flatMap]
      erw [← hrows, List.flatMap_map]
      rfl

theorem sequenceTapes_output (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (ops : List (Command d n)) (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    sequenceTapes graph n placement output vertex ops base output =
      ops.reverse.flatMap (rowBits graph n vertex) ++ base output := by
  induction ops generalizing base with
  | nil => rfl
  | cons j ops ih =>
      have nextReady := PoweringMachineRowBody.finalTapes_ready graph n placement distinct
        output outside vertex (ports j) (direction j) base suffix ready
      change sequenceTapes graph n placement output vertex ops
        (result graph n placement output vertex j base) output = _
      dsimp only [result]
      rw [ih _ nextReady, PoweringMachineRowBody.finalTapes_output graph n placement distinct
        output outside vertex (ports j) (direction j) base suffix ready]
      simp only [List.reverse_cons, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.append_assoc, rowBits]

theorem finalTapes_output (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    finalTapes graph n placement output vertex base output =
      PoweringTableLayout.vertexRowBits graph n vertex ++ base output := by
  rw [finalTapes, sequenceTapes_output graph n placement distinct output outside vertex
    (commands d n) base suffix ready]
  simp only [commands, List.reverse_reverse, rows_eq_vertexRowBits]

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineVertex

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_PoweringMachineOuterLoopLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
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

abbrev State := PoweringMachineVertex.State

structure Ready (graph : PortTables.Table vertices d) (n : Nat) (placement : Placement K n)
    (base : K → List Bool) : Prop where
  table : base (placement (.inl 0)) = PortTables.tableBits graph
  scratch : base (placement (.inl 5)) = []
  leftCopy : base (placement (.inl 8)) = []
  rightCopy : base (placement (.inl 9)) = []
  data : base (placement (.inl 10)) = []

theorem counter_other (placement : Placement K n) (distinct : Function.Injective placement)
    (base : K → List Bool) (remaining : Nat) (j : Fin 11) (hj : j ≠ 1) :
    counter placement base remaining (placement (.inl j)) = base (placement (.inl j)) := by
  apply MachineUnaryCounter.counterTapes_other
  intro h
  exact hj (Sum.inl.inj (distinct h))

theorem ready_vertex (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (distinct : Function.Injective placement)
    (base : K → List Bool) (ready : Ready graph n placement base) (vertex : Fin vertices) :
    PoweringMachineRowBody.Ready graph n placement vertex [] (counter placement base vertex.val) := by
  constructor
  · constructor
    · rw [counter_other placement distinct base vertex.val 0 (by decide)]
      exact ready.table
    · simp only [counter, MachineUnaryCounter.counterTapes_counter]
    · rw [counter_other placement distinct base vertex.val 5 (by decide)]
      exact ready.scratch
    · rw [counter_other placement distinct base vertex.val 8 (by decide)]
      exact ready.leftCopy
    · rw [counter_other placement distinct base vertex.val 9 (by decide)]
      exact ready.rightCopy
  · rw [counter_other placement distinct base vertex.val 10 (by decide)]
    exact ready.data

omit [DecidableEq K] in
theorem ready_of_vertex (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (base : K → List Bool) (vertex : Fin vertices)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex [] base) :
    Ready graph n placement base :=
  ⟨ready.1.table, ready.1.scratch, ready.1.leftCopy, ready.1.rightCopy, ready.2⟩

def vertexStart (d n : Nat) (labels : PoweringMachineVertex.Label d n → Λ) (guardLabel : Λ) : Λ :=
  (PoweringMachineVertex.entry d n labels (some guardLabel)).getD guardLabel

theorem vertexEntry (d n : Nat) (labels : PoweringMachineVertex.Label d n → Λ) (guardLabel : Λ) :
    PoweringMachineVertex.entry d n labels (some guardLabel) =
      some (vertexStart d n labels guardLabel) := by
  unfold vertexStart PoweringMachineVertex.entry PoweringMachineVertex.sequenceEntry
  have h : ∀ (commands : List (PoweringMachineVertex.Command d n))
      (labels : MachineFiniteSequence.Label PoweringMachineVertex.LocalLabel commands → Λ),
      MachineFiniteSequence.entry PoweringMachineVertex.LocalLabel
        (fun j => PoweringMachineRowBody.entry n
          (PoweringMachineVertex.ports j) (PoweringMachineVertex.direction j))
        commands labels (some guardLabel) =
      some ((MachineFiniteSequence.entry PoweringMachineVertex.LocalLabel
        (fun j => PoweringMachineRowBody.entry n
          (PoweringMachineVertex.ports j) (PoweringMachineVertex.direction j))
        commands labels (some guardLabel)).getD guardLabel) := by
    intro commands labels
    cases commands <;> rfl
  exact h _ labels

def bridge (d n : Nat) (labels : PoweringMachineVertex.Label d n → Λ) (guardLabel : Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (State d n) :=
  .goto (fun _ => vertexStart d n labels guardLabel)

/-- The exact tapes produced by repeatedly executing the actual vertex body. -/
def finalTapes (graph : PortTables.Table vertices d) (n : Nat) (placement : Placement K n)
    (output : K) : (remaining : Nat) → remaining ≤ vertices → (K → List Bool) → K → List Bool
  | 0, _, base => counter placement base 0
  | r + 1, bounded, base =>
      finalTapes graph n placement output r (by omega)
        (PoweringMachineVertex.finalTapes graph n placement output ⟨r, by omega⟩
          (counter placement base r))

def steps (graph : PortTables.Table vertices d) (n : Nat) :
    (remaining : Nat) → remaining ≤ vertices → Nat
  | 0, _ => 1
  | r + 1, bounded =>
      2 + PoweringMachineVertex.steps graph ⟨r, by omega⟩ n + steps graph n r (by omega)

theorem finalTapes_ready (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i)
    (remaining : Nat) (bounded : remaining ≤ vertices) (base : K → List Bool)
    (ready : Ready graph n placement base) :
    Ready graph n placement (finalTapes graph n placement output remaining bounded base) := by
  induction remaining generalizing base with
  | zero =>
      constructor
      · rw [finalTapes, counter_other placement distinct base 0 0 (by decide)]
        exact ready.table
      · rw [finalTapes, counter_other placement distinct base 0 5 (by decide)]
        exact ready.scratch
      · rw [finalTapes, counter_other placement distinct base 0 8 (by decide)]
        exact ready.leftCopy
      · rw [finalTapes, counter_other placement distinct base 0 9 (by decide)]
        exact ready.rightCopy
      · rw [finalTapes, counter_other placement distinct base 0 10 (by decide)]
        exact ready.data
  | succ r ih =>
      apply ih
      apply ready_of_vertex graph n placement _ (⟨r, by omega⟩ : Fin vertices)
      exact PoweringMachineVertex.finalTapes_ready graph n placement distinct output outside
        ⟨r, by omega⟩ _ [] (ready_vertex graph n placement distinct base ready _)

def prefixRows (graph : PortTables.Table vertices d) (n : Nat) : Nat → List Bool
  | 0 => []
  | r + 1 => prefixRows graph n r ++
      if h : r < vertices then PoweringTableLayout.vertexRowBits graph n ⟨r, h⟩ else []

theorem prefixRows_ofFn (graph : PortTables.Table vertices d) (n remaining : Nat)
    (bounded : remaining ≤ vertices) :
    prefixRows graph n remaining =
      (List.ofFn (fun i : Fin remaining =>
        PoweringTableLayout.vertexRowBits graph n (Fin.castLE bounded i))).flatten := by
  induction remaining with
  | zero => rfl
  | succ r ih =>
      have hr : r < vertices := by omega
      rw [prefixRows, dite_eq_left hr, List.ofFn_succ_last, List.flatten_append]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
      change prefixRows graph n r ++ PoweringTableLayout.vertexRowBits graph n ⟨r, hr⟩ =
        (List.ofFn (fun i : Fin r => PoweringTableLayout.vertexRowBits graph n
          (Fin.castLE (show r ≤ vertices by omega) i))).flatten ++
          PoweringTableLayout.vertexRowBits graph n ⟨r, hr⟩
      rw [ih]

theorem prefixRows_all (graph : PortTables.Table vertices d) (n : Nat) :
    prefixRows graph n vertices =
      (List.finRange vertices).flatMap (PoweringTableLayout.vertexRowBits graph n) := by
  rw [prefixRows_ofFn graph n vertices (Nat.le_refl _)]
  simp only [List.finRange, List.flatMap_def, List.map_ofFn]
  rfl

theorem finalTapes_output (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i)
    (remaining : Nat) (bounded : remaining ≤ vertices) (base : K → List Bool)
    (ready : Ready graph n placement base) :
    finalTapes graph n placement output remaining bounded base output =
      prefixRows graph n remaining ++ base output := by
  induction remaining generalizing base with
  | zero =>
      exact MachineUnaryCounter.counterTapes_other (placement (.inl 1)) output (outside _)
        base 0 []
  | succ r ih =>
      let vertex : Fin vertices := ⟨r, by omega⟩
      let current := counter placement base r
      have vertexReady := ready_vertex graph n placement distinct base ready vertex
      have nextReady := PoweringMachineVertex.finalTapes_ready graph n placement distinct
        output outside vertex current [] vertexReady
      change finalTapes graph n placement output r (by omega)
        (PoweringMachineVertex.finalTapes graph n placement output vertex current) output = _
      rw [ih (by omega) _ (ready_of_vertex graph n placement _ vertex nextReady),
        PoweringMachineVertex.finalTapes_output graph n placement distinct output outside
          vertex current [] vertexReady]
      have hc : current output = base output :=
        MachineUnaryCounter.counterTapes_other (placement (.inl 1)) output (outside _) base r []
      rw [hc, prefixRows, dite_eq_left vertex.isLt, List.append_assoc]

theorem finalTapes_other (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (output : K) (remaining : Nat)
    (bounded : remaining ≤ vertices) (base : K → List Bool)
    (k : K) (hout : k ≠ output) (outside : ∀ i, k ≠ placement i) :
    finalTapes graph n placement output remaining bounded base k = base k := by
  induction remaining generalizing base with
  | zero => exact MachineUnaryCounter.counterTapes_other _ _ (outside _) base 0 []
  | succ r ih =>
      rw [finalTapes, ih, PoweringMachineVertex.finalTapes_other graph n placement output
        ⟨r, by omega⟩ _ k hout outside]
      exact MachineUnaryCounter.counterTapes_other _ _ (outside _) base r []

theorem loopTrace (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i)
    (guardLabel bridgeLabel exitLabel : Λ) (labels : PoweringMachineVertex.Label d n → Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State d n))
    (atGuard : program guardLabel =
      MachineUnaryCounter.guard (placement (.inl 1)) bridgeLabel exitLabel)
    (atBridge : program bridgeLabel = bridge d n labels guardLabel)
    (atVertex : ∀ l, program (labels l) =
      PoweringMachineVertex.instruction n placement output labels (some guardLabel) l)
    (remaining : Nat) (bounded : remaining ≤ vertices) (base : K → List Bool)
    (ready : Ready graph n placement base) :
    (advance (TM2.step program))^[steps graph n remaining bounded]
      (some ⟨some guardLabel, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        counter placement base remaining⟩) =
      some ⟨some exitLabel, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        finalTapes graph n placement output remaining bounded base⟩ := by
  let initial := PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n)
  induction remaining generalizing base with
  | zero =>
      simpa only [steps, finalTapes, counter, initial, PoweringMasterState.clean,
        PoweringMasterState.withBuffer] using
        MachineUnaryCounter.guardTrace_zero (placement (.inl 1)) guardLabel bridgeLabel exitLabel
          program atGuard base [] initial.1 none
  | succ r ih =>
      let vertex : Fin vertices := ⟨r, by omega⟩
      let current := counter placement base r
      let next := PoweringMachineVertex.finalTapes graph n placement output vertex current
      have vertexReady : PoweringMachineRowBody.Ready graph n placement vertex [] current :=
        ready_vertex graph n placement distinct base ready vertex
      have nextVertexReady := PoweringMachineVertex.finalTapes_ready graph n placement distinct
        output outside vertex current [] vertexReady
      have nextReady : Ready graph n placement next :=
        ready_of_vertex graph n placement next vertex nextVertexReady
      have sameCounter : counter placement next r = next := by
        have hs := nextVertexReady.1.source
        change next (placement (.inl 1)) = encodeWord r ++ [] at hs
        unfold counter MachineUnaryCounter.counterTapes
        rw [← hs]
        exact Function.update_eq_self _ _
      have tailRun := ih (by omega) next nextReady
      rw [sameCounter] at tailRun
      have guardRun : advance (TM2.step program)
          (some ⟨some guardLabel, initial, counter placement base (r + 1)⟩) =
          some ⟨some bridgeLabel, initial, current⟩ := by
        simpa only [advance_some, current, counter, initial, PoweringMasterState.clean,
          PoweringMasterState.withBuffer] using
          MachineUnaryCounter.guardStep_succ (placement (.inl 1)) guardLabel bridgeLabel exitLabel
            program atGuard base r [] initial.1 none
      have bridgeRun : advance (TM2.step program)
          (some ⟨some bridgeLabel, initial, current⟩) =
          some ⟨PoweringMachineVertex.entry d n labels (some guardLabel), initial, current⟩ := by
        change some (TM2.stepAux (program bridgeLabel) initial current) = _
        rw [atBridge, vertexEntry]
        rfl
      have vertexRun := PoweringMachineVertex.vertexTrace graph n placement distinct output outside
        vertex labels (some guardLabel) program atVertex current [] vertexReady
      change (advance (TM2.step program))^[2 + PoweringMachineVertex.steps graph vertex n +
          steps graph n r (by omega)]
        (some ⟨some guardLabel, initial, counter placement base (r + 1)⟩) = _
      rw [show 2 + PoweringMachineVertex.steps graph vertex n + steps graph n r (by omega) =
          (steps graph n r (by omega) + PoweringMachineVertex.steps graph vertex n) + 1 + 1 by omega,
        Function.iterate_succ_apply, guardRun, Function.iterate_succ_apply, bridgeRun,
        Function.iterate_add_apply, vertexRun]
      exact tailRun

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

abbrev State (d n : Nat) :=
  PoweringMasterState.Master (PoweringMachineRowBody.bufferSize d n)

abbrev Label (d n : Nat) := PoweringMachineInitialize.Label ⊕
  (Bool ⊕ (PoweringMachineVertex.Label d n ⊕ FinishLabel n))

instance labelFintype (d n : Nat) : Fintype (Label d n) :=
  inferInstanceAs (Fintype (PoweringMachineInitialize.Label ⊕
    (Bool ⊕ (PoweringMachineVertex.Label d n ⊕ FinishLabel n))))

def initLabels (d n : Nat) : PoweringMachineInitialize.Label → Label d n := Sum.inl
def guardLabel (d n : Nat) : Label d n := .inr (.inl false)
def bridgeLabel (d n : Nat) : Label d n := .inr (.inl true)

def vertexLabels (d n : Nat) (label : PoweringMachineVertex.Label d n) : Label d n :=
  .inr (.inr (.inl label))

def finishLabels (d n : Nat) (label : FinishLabel n) : Label d n :=
  .inr (.inr (.inr label))

/-- Finish first copies the dart-count field, then the vertex-count field. -/
def finishEntry (d n : Nat) : Label d n := finishLabels d n (.inl .seed)

/-- Initialization first clones the input's live vertex-count field. -/
def main (d n : Nat) : Label d n := initLabels d n (.inr .seed)

/-- The complete program, fixed solely by the reduction parameters. -/
def program (d n : Nat) :
    Label d n → TM2.Stmt (fun _ : Tape n => Bool) (Label d n) (State d n)
  | .inl label => PoweringMachineInitialize.instruction
      (PoweringMachineRowBody.capacity n) (PoweringMachineRowBody.bufferSize d n)
      (PCP.PoweringTableLayout.blockSize d n) (initLabels d n) (some (guardLabel d n)) label
  | .inr (.inl false) => MachineUnaryCounter.guard
      (placement n (PoweringMachineTapes.start (PoweringMachineRowBody.capacity n)))
      (bridgeLabel d n) (finishEntry d n)
  | .inr (.inl true) => PoweringMachineOuterLoop.bridge d n (vertexLabels d n) (guardLabel d n)
  | .inr (.inr (.inl label)) => PoweringMachineVertex.instruction n (placement n) (outputTape n)
      (vertexLabels d n) (some (guardLabel d n)) label
  | .inr (.inr (.inr label)) => PoweringMachineFinish.instruction (enumeration n)
      (headerVertices n) (headerDarts n) (outputTape n)
      (placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)))
      (finishLabels d n) label

@[simp] theorem atInit (d n : Nat) (label : PoweringMachineInitialize.Label) :
    program d n (initLabels d n label) = PoweringMachineInitialize.instruction
      (PoweringMachineRowBody.capacity n) (PoweringMachineRowBody.bufferSize d n)
      (PCP.PoweringTableLayout.blockSize d n) (initLabels d n) (some (guardLabel d n)) label := rfl

@[simp] theorem atGuard (d n : Nat) :
    program d n (guardLabel d n) = MachineUnaryCounter.guard
      (placement n (PoweringMachineTapes.start (PoweringMachineRowBody.capacity n)))
      (bridgeLabel d n) (finishEntry d n) := rfl

@[simp] theorem atBridge (d n : Nat) :
    program d n (bridgeLabel d n) =
      PoweringMachineOuterLoop.bridge d n (vertexLabels d n) (guardLabel d n) := rfl

@[simp] theorem atVertex (d n : Nat) (label : PoweringMachineVertex.Label d n) :
    program d n (vertexLabels d n label) = PoweringMachineVertex.instruction n
      (placement n) (outputTape n) (vertexLabels d n) (some (guardLabel d n)) label := rfl

@[simp] theorem atFinish (d n : Nat) (label : FinishLabel n) :
    program d n (finishLabels d n label) = PoweringMachineFinish.instruction (enumeration n)
      (headerVertices n) (headerDarts n) (outputTape n)
      (placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)))
      (finishLabels d n) label := rfl

/-- All state and control spaces are explicit finite types; only the tapes
hold variable-size data. -/
def machine (d n : Nat) : FinTM2 where
  K := Tape n
  k₀ := inputTape n
  k₁ := outputTape n
  Γ _ := Bool
  Λ := Label d n
  main := main d n
  σ := State d n
  initialState := PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n)
  m := program d n

@[simp] theorem machine_code (d n : Nat) (label : Label d n) :
    (machine d n).m label = program d n label := rfl

@[simp] theorem machine_main (d n : Nat) : (machine d n).main = main d n := rfl

@[simp] theorem machine_initialState (d n : Nat) :
    (machine d n).initialState = PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n) := rfl

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal

/-!
# Concrete global configurations and tape separation

These lemmas specialize the checked initializer placement to the fixed global
machine. The final configuration is the actual `Turing.haltList`, with the
machine's clean initial register and only the output tape populated.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration

open Turing PoweringMachineGlobal

theorem headerVertices_ne_placement (n : Nat)
    (tape : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n)) :
    headerVertices n ≠ placement n tape :=
  Ne.symm (PoweringMachineInitialize.commonPlacement_ne_header
    (PoweringMachineRowBody.capacity n) tape .vertices (by decide))

theorem headerDarts_ne_placement (n : Nat)
    (tape : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n)) :
    headerDarts n ≠ placement n tape :=
  Ne.symm (PoweringMachineInitialize.commonPlacement_ne_header
    (PoweringMachineRowBody.capacity n) tape .darts (by decide))

theorem headerVertices_ne_output (n : Nat) : headerVertices n ≠ outputTape n := by
  simp [headerVertices, outputTape, PoweringMachineInitialize.finalOutput]

theorem headerDarts_ne_output (n : Nat) : headerDarts n ≠ outputTape n := by
  simp [headerDarts, outputTape, PoweringMachineInitialize.finalOutput]

theorem headerVertices_ne_scratch (n : Nat) :
    headerVertices n ≠
      placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)) :=
  headerVertices_ne_placement n _

theorem headerDarts_ne_scratch (n : Nat) :
    headerDarts n ≠
      placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)) :=
  headerDarts_ne_placement n _

/-- A Boolean tape alphabet is constant, so the type-equality transport in
the bundled machine's dependent stack specification leaves its word intact. -/
@[simp] theorem boolList_mpr_eq (h : List Bool = List Bool) (bits : List Bool) :
    h.mpr bits = bits := rfl

/-- The dependent stack definition in `haltList` is exactly the Boolean output
tape shape produced by the checked finite cleanup program. -/
theorem haltList_tapes (d n : Nat) (output : List Bool) :
    (Turing.haltList (machine d n) output).stk =
      MachineDrainMany.haltTapes (outputTape n) output := by
  funext tape
  simp only [machine]
  rfl

/-- Exact identity with the global machine's actual output specification. -/
theorem haltList_eq (d n : Nat) (output : List Bool) :
    Turing.haltList (machine d n) output =
      (⟨none, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        MachineDrainMany.haltTapes (outputTape n) output⟩ : (machine d n).Cfg) := by
  change (⟨none, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
      (Turing.haltList (machine d n) output).stk⟩ : (machine d n).Cfg) = _
  exact congrArg
    (fun tapes => (⟨none, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
      tapes⟩ : (machine d n).Cfg)) (haltList_tapes d n output)

end UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_PoweringInitializeFrame
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame

open Turing PCP

variable {vertices d : Nat}

/-- The extra tapes initially contain only the live serialized table. -/
def initialExtra (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineInitialize.ExtraTape (PoweringMachineRowBody.capacity n) → List Bool :=
  fun tape => if tape = .inl (PoweringMachineTapes.table (PoweringMachineRowBody.capacity n))
    then PortTables.tableBits graph else []

@[simp] theorem initialExtra_table (graph : PortTables.Table vertices d) (n : Nat) :
    initialExtra graph n (.inl (PoweringMachineTapes.table (PoweringMachineRowBody.capacity n))) =
      PortTables.tableBits graph := by simp [initialExtra]

@[simp] theorem initialExtra_scratch (graph : PortTables.Table vertices d) (n : Nat) :
    initialExtra graph n
      (.inl (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n))) = [] := by
  simp [initialExtra, PoweringMachineTapes.table, PoweringMachineTapes.scratch]

/-- Exact frame left by initialization, including the preserved input table. -/
def preparedTapes (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineGlobal.Tape n → List Bool :=
  PoweringMachineInitialize.mergeTapes
    (PoweringMachineLoop.finalTapes (PoweringTableLayout.blockSize d n) vertices [])
    (initialExtra graph n)

theorem prepared_commonRole (graph : PortTables.Table vertices d) (n : Nat)
    (j : Fin 11) (hne : j ≠ 1) :
    preparedTapes graph n (PoweringMachineGlobal.placement n (.inl j)) =
      if j = 0 then PortTables.tableBits graph else [] := by
  simp [preparedTapes, PoweringMachineGlobal.placement,
    PoweringMachineInitialize.commonPlacement, PoweringMachineTapes.start,
    PoweringMachineInitialize.mergeTapes, initialExtra, PoweringMachineTapes.table, hne]

theorem prepared_ready (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineOuterLoop.Ready graph n (PoweringMachineGlobal.placement n)
      (preparedTapes graph n) := by
  constructor
  · simpa using prepared_commonRole graph n 0 (by decide)
  · simpa using prepared_commonRole graph n 5 (by decide)
  · simpa using prepared_commonRole graph n 8 (by decide)
  · simpa using prepared_commonRole graph n 9 (by decide)
  · simpa using prepared_commonRole graph n 10 (by decide)

@[simp] theorem prepared_start (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (PoweringMachineGlobal.placement n (.inl 1)) =
      encodeWord vertices := by
  simpa only [preparedTapes, PoweringMachineGlobal.placement, PoweringMachineTapes.start] using
    PoweringMachineInitialize.final_counter (PoweringMachineRowBody.capacity n)
      (PoweringTableLayout.blockSize d n) vertices (initialExtra graph n)

/-- Installing the outer-loop counter changes nothing: it is already present. -/
theorem prepared_counter (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineOuterLoop.counter (PoweringMachineGlobal.placement n)
      (preparedTapes graph n) vertices = preparedTapes graph n := by
  unfold PoweringMachineOuterLoop.counter MachineUnaryCounter.counterTapes
  rw [List.append_nil, ← prepared_start graph n]
  simp only [Function.update_eq_self]

@[simp] theorem prepared_output (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (PoweringMachineGlobal.outputTape n) = [] := by
  simp [preparedTapes, PoweringMachineGlobal.outputTape, PoweringMachineInitialize.finalOutput,
    PoweringMachineInitialize.mergeTapes, initialExtra]

@[simp] theorem prepared_vertices (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (PoweringMachineGlobal.headerVertices n) = encodeWord vertices := rfl

@[simp] theorem prepared_darts (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (PoweringMachineGlobal.headerDarts n) =
      encodeWord (PoweringTableLayout.blockSize d n * vertices) := rfl

@[simp] theorem prepared_source (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (.inl PoweringMachineLoop.HeaderTape.source) = [] := rfl

def preparedCfg (graph : PortTables.Table vertices d) (n : Nat) :
    (PoweringMachineGlobal.machine d n).Cfg :=
  ⟨some (PoweringMachineGlobal.guardLabel d n),
    PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n), preparedTapes graph n⟩

/-- A homogeneous Boolean description of the machine's literal initial stacks. -/
theorem initialGlobalTapes_eq (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineInitialize.initialGlobalTapes (initialExtra graph n) =
      fun tape => if tape = PoweringMachineGlobal.inputTape n
        then PortTables.tableBits graph else [] := by
  funext tape
  cases tape with
  | inl field =>
    simp [PoweringMachineInitialize.initialGlobalTapes, PoweringMachineInitialize.mergeTapes,
      PoweringMachineGlobal.inputTape, PoweringMachineGlobal.placement,
      PoweringMachineInitialize.commonPlacement_table]
  | inr field =>
    simp [PoweringMachineInitialize.initialGlobalTapes, PoweringMachineInitialize.mergeTapes,
      PoweringMachineGlobal.inputTape, PoweringMachineGlobal.placement,
      PoweringMachineInitialize.commonPlacement_table, initialExtra]

theorem machine_initialStacks (d n : Nat) (input : List Bool) :
    (initList (PoweringMachineGlobal.machine d n) input).stk =
      fun tape => if tape = PoweringMachineGlobal.inputTape n then input else [] := by
  funext tape
  rfl

/-- The trace starts at `Turing.initList`, with no assumed prepared work tapes. -/
theorem initList_eq (graph : PortTables.Table vertices d) (n : Nat) :
    initList (PoweringMachineGlobal.machine d n) (PortTables.tableBits graph) =
      ⟨some (PoweringMachineGlobal.main d n),
        PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        PoweringMachineInitialize.initialGlobalTapes (initialExtra graph n)⟩ := by
  have ht := (machine_initialStacks d n (PortTables.tableBits graph)).trans
    (initialGlobalTapes_eq graph n).symm
  exact congrArg (TM2.Cfg.mk _ _) ht

/-- The first serialized input field is the actual number of vertices. -/
theorem tableBits_head (graph : PortTables.Table vertices d) :
    PortTables.tableBits graph = encodeWord vertices ++
      encodeWords (PortTables.tableWords graph).tail := rfl

/-- Initialization of the actual global program from its literal input list.
Every work-tape readiness property follows from the explicit final frame. -/
def initializeInTime (graph : PortTables.Table vertices d) (n : Nat) :
    StateTransition.EvalsToInTime (PoweringMachineGlobal.machine d n).step
      (initList (PoweringMachineGlobal.machine d n) (PortTables.tableBits graph))
      (some (preparedCfg graph n)) (3 * vertices + 5) := by
  rw [initList_eq]
  exact PoweringMachineInitialize.initializeAtInTime
    (PoweringMachineRowBody.capacity n) (PoweringMachineRowBody.bufferSize d n)
    (PoweringTableLayout.blockSize d n) vertices
    (PoweringMachineGlobal.initLabels d n) (some (PoweringMachineGlobal.guardLabel d n))
    (PoweringMachineGlobal.program d n) (PoweringMachineGlobal.atInit d n)
    (initialExtra graph n) (encodeWords (PortTables.tableWords graph).tail)
    (by rw [initialExtra_table, tableBits_head]) (initialExtra_scratch graph n)
    (PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n))

end UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame

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

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringPolynomialBudget

open PCP

/-- Initial setup, the actual vertex loop, and the bridge to cleanup. -/
def preBudget (d n vertices inputLength : Nat) : Nat :=
  (3 * vertices + 5) +
    (vertices * (PoweringMachineVertex.budget d n inputLength + 2) + 1)

/-- Cleanup after a preceding run bounded by `prior`, with fixed stack count
and fixed maximum number of pushes per machine transition. -/
def finishBudget (d n pushBound tapeCount vertices inputLength prior : Nat) : Nat :=
  2 * (vertices + PoweringTableLayout.blockSize d n * vertices) + 6 +
    tapeCount * (inputLength + prior * pushBound + vertices +
      PoweringTableLayout.blockSize d n * vertices + 3)

def totalBudget (d n pushBound tapeCount vertices inputLength : Nat) : Nat :=
  preBudget d n vertices inputLength +
    finishBudget d n pushBound tapeCount vertices inputLength
      (preBudget d n vertices inputLength)

theorem preBudget_mono_vertices (d n inputLength : Nat) {v w : Nat} (h : v ≤ w) :
    preBudget d n v inputLength ≤ preBudget d n w inputLength := by
  have hthree := Nat.mul_le_mul_left 3 h
  have hloop := Nat.mul_le_mul_right (PoweringMachineVertex.budget d n inputLength + 2) h
  unfold preBudget
  omega

theorem finishBudget_mono (d n pushBound tapeCount inputLength : Nat)
    {v w prior later : Nat} (hvertices : v ≤ w) (hprior : prior ≤ later) :
    finishBudget d n pushBound tapeCount v inputLength prior ≤
      finishBudget d n pushBound tapeCount w inputLength later := by
  have hdarts := Nat.mul_le_mul_left (PoweringTableLayout.blockSize d n) hvertices
  have hheader := Nat.mul_le_mul_left 2 (Nat.add_le_add hvertices hdarts)
  have hgrowth := Nat.mul_le_mul_right pushBound hprior
  have hinside : inputLength + prior * pushBound + v +
      PoweringTableLayout.blockSize d n * v + 3 ≤
      inputLength + later * pushBound + w + PoweringTableLayout.blockSize d n * w + 3 := by
    omega
  have hclear := Nat.mul_le_mul_left tapeCount hinside
  unfold finishBudget
  omega

theorem totalBudget_mono_vertices (d n pushBound tapeCount inputLength : Nat)
    {v w : Nat} (hvertices : v ≤ w) :
    totalBudget d n pushBound tapeCount v inputLength ≤
      totalBudget d n pushBound tapeCount w inputLength := by
  have hpre := preBudget_mono_vertices d n inputLength hvertices
  unfold totalBudget
  exact Nat.add_le_add hpre
    (finishBudget_mono d n pushBound tapeCount inputLength hvertices hpre)

/-- The exact affine polynomial of one concrete row body. -/
noncomputable def rowTime (d n : Nat) : Polynomial Nat :=
  Polynomial.C (PoweringMachineRowBody.bufferSize d n) *
      (Polynomial.C (28 * (2 * (n + 1)) + 10) * Polynomial.X +
        Polynomial.C (24 * (2 * (n + 1)) + 15)) + Polynomial.C 1 +
    (Polynomial.C (14 * (n + 1) + 4) * Polynomial.X +
      Polynomial.C (12 * (n + 1)) + Polynomial.C 6)

@[simp] theorem rowTime_eval (d n inputLength : Nat) :
    (rowTime d n).eval inputLength = PoweringMachineRowBody.budget d n inputLength := by
  simp only [rowTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, PoweringMachineRowBody.budget, PoweringPlanBudget.rowBudget,
    PoweringPlanBudget.fieldBudget, PoweringMachineRowBody.bufferSize, Nat.add_assoc]

/-- The actual fixed number of row commands multiplies the row polynomial. -/
noncomputable def vertexTime (d n : Nat) : Polynomial Nat :=
  Polynomial.C (PoweringTableLayout.blockSize d n) * rowTime d n

@[simp] theorem vertexTime_eval (d n inputLength : Nat) :
    (vertexTime d n).eval inputLength = PoweringMachineVertex.budget d n inputLength := by
  simp only [vertexTime, Polynomial.eval_mul, Polynomial.eval_C, rowTime_eval,
    PoweringMachineVertex.budget]

/-- Replace the vertex count by the input length in the actual setup/loop bound. -/
noncomputable def preTime (d n : Nat) : Polynomial Nat :=
  (Polynomial.C 3 * Polynomial.X + Polynomial.C 5) +
    (Polynomial.X * (vertexTime d n + Polynomial.C 2) + Polynomial.C 1)

@[simp] theorem preTime_eval (d n inputLength : Nat) :
    (preTime d n).eval inputLength = preBudget d n inputLength inputLength := by
  simp only [preTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, vertexTime_eval, preBudget]

/-- The explicit final polynomial. All coefficients depend only on the fixed
degree/radius and the chosen finite machine's push bound and tape count. -/
noncomputable def time (d n pushBound tapeCount : Nat) : Polynomial Nat :=
  preTime d n +
    (Polynomial.C 2 *
        (Polynomial.X + Polynomial.C (PoweringTableLayout.blockSize d n) * Polynomial.X) +
      Polynomial.C 6 + Polynomial.C tapeCount *
        (Polynomial.X + preTime d n * Polynomial.C pushBound + Polynomial.X +
          Polynomial.C (PoweringTableLayout.blockSize d n) * Polynomial.X + Polynomial.C 3))

@[simp] theorem time_eval (d n pushBound tapeCount inputLength : Nat) :
    (time d n pushBound tapeCount).eval inputLength =
      totalBudget d n pushBound tapeCount inputLength inputLength := by
  simp only [time, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, preTime_eval, totalBudget, finishBudget]

/-- The actual vertex count may be strictly smaller than the input length. -/
theorem totalBudget_le_time (d n pushBound tapeCount vertices inputLength : Nat)
    (hvertices : vertices ≤ inputLength) :
    totalBudget d n pushBound tapeCount vertices inputLength ≤
      (time d n pushBound tapeCount).eval inputLength := by
  rw [time_eval]
  exact totalBudget_mono_vertices d n pushBound tapeCount inputLength hvertices

/-- Numerical bounds on two actual phases can use the same fixed polynomial. -/
theorem execution_budget_le_time (d n pushBound tapeCount vertices inputLength : Nat)
    (hvertices : vertices ≤ inputLength) {preSteps finishSteps : Nat}
    (hpre : preSteps ≤ preBudget d n vertices inputLength)
    (hfinish : finishSteps ≤ finishBudget d n pushBound tapeCount vertices inputLength
      (preBudget d n vertices inputLength)) :
    preSteps + finishSteps ≤ (time d n pushBound tapeCount).eval inputLength := by
  calc
    preSteps + finishSteps ≤ totalBudget d n pushBound tapeCount vertices inputLength := by
      unfold totalBudget
      exact Nat.add_le_add hpre hfinish
    _ ≤ (time d n pushBound tapeCount).eval inputLength :=
      totalBudget_le_time d n pushBound tapeCount vertices inputLength hvertices

end UniqueGamesTheorem.Foundations.Complexity.PoweringPolynomialBudget

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

/-- Cleanup's concrete tape count is the size of the global tape enumeration. -/
abbrev tapeCount (radius : Nat) : Nat :=
  4 + (11 + PoweringMachineRowBody.capacity radius + 1)

/-- The actual global prefix execution supplies every finishing stack bound.
The physical header premises are used by `PoweringMachineFinish.traceAt`; this
arithmetic consequence of that prefix is valid for any two proposed header values. -/
theorem finish_steps_le_of_execution (d radius : Nat) (input : List Bool)
    (before : (PoweringMachineGlobal.machine d radius).Cfg)
    (priorBudget vertices darts : Nat)
    (prior : StateTransition.EvalsToInTime (PoweringMachineGlobal.machine d radius).step
      (initList (PoweringMachineGlobal.machine d radius) input) (some before) priorBudget) :
    PoweringMachineFinish.steps (PoweringMachineGlobal.enumeration radius)
      (PoweringMachineGlobal.outputTape radius) before.stk vertices darts ≤
      2 * (vertices + darts) + 6 + tapeCount radius *
        (input.length + priorBudget * Runtime.programPushBound
          (PoweringMachineGlobal.machine d radius) + vertices + darts + 3) := by
  exact PoweringMachineFinish.steps_le_uniform (PoweringMachineGlobal.enumeration radius)
    (PoweringMachineGlobal.outputTape radius) before.stk vertices darts
    (input.length + priorBudget * Runtime.programPushBound (PoweringMachineGlobal.machine d radius))
    (stackLength_le_from_input (PoweringMachineGlobal.machine d radius) input before priorBudget prior)

end UniqueGamesTheorem.Foundations.Complexity.PoweringRuntimeBudget

/-! Complete execution of the one fixed powering machine on the actual
port-table input and generic graph-table output encodings. The varying vertex
count remains on unary tapes throughout. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRuntime

open Turing MachineComposition PCP PoweringMachineGlobal

variable {vertices d : Nat}

/-- The actual work tapes after all vertex blocks, before final headers. -/
def beforeFinish (graph : PortTables.Table vertices d) (n : Nat) : Tape n → List Bool :=
  PoweringMachineOuterLoop.finalTapes graph n (placement n) (outputTape n)
    vertices (Nat.le_refl _) (PoweringInitializeFrame.preparedTapes graph n)

def finishConfiguration (graph : PortTables.Table vertices d) (n : Nat) : (machine d n).Cfg :=
  ⟨some (finishEntry d n), PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
    beforeFinish graph n⟩

/-- Initialization and the actual outer loop's proved budgets. -/
def beforeFinishBudget (graph : PortTables.Table vertices d) (n : Nat) : Nat :=
  (3 * vertices + 5) + (vertices *
    (PoweringMachineVertex.budget d n (PortTables.tableBits graph).length + 2) + 1)

theorem beforeFinish_ready (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineOuterLoop.Ready graph n (placement n) (beforeFinish graph n) :=
  PoweringMachineOuterLoop.finalTapes_ready graph n (placement n)
    (PoweringMachineInitialize.commonPlacement_injective _)
    (outputTape n) (fun i => Ne.symm (PoweringMachineInitialize.commonPlacement_ne_finalOutput _ i))
    vertices (Nat.le_refl _) (PoweringInitializeFrame.preparedTapes graph n)
    (PoweringInitializeFrame.prepared_ready graph n)

theorem beforeFinish_output (graph : PortTables.Table vertices d) (n : Nat) :
    beforeFinish graph n (outputTape n) =
      (List.finRange vertices).flatMap (PoweringTableLayout.vertexRowBits graph n) := by
  rw [beforeFinish, PoweringMachineOuterLoop.finalTapes_output graph n (placement n)
    (PoweringMachineInitialize.commonPlacement_injective _) (outputTape n)
    (fun i => Ne.symm (PoweringMachineInitialize.commonPlacement_ne_finalOutput _ i))
    vertices (Nat.le_refl _) (PoweringInitializeFrame.preparedTapes graph n)
    (PoweringInitializeFrame.prepared_ready graph n),
    PoweringMachineOuterLoop.prefixRows_all, PoweringInitializeFrame.prepared_output,
    List.append_nil]

theorem beforeFinish_vertices (graph : PortTables.Table vertices d) (n : Nat) :
    beforeFinish graph n (headerVertices n) = encodeWord vertices := by
  rw [beforeFinish, PoweringMachineOuterLoop.finalTapes_other graph n (placement n)
    (outputTape n) vertices (Nat.le_refl _) (PoweringInitializeFrame.preparedTapes graph n)
    (headerVertices n) (PoweringGlobalConfiguration.headerVertices_ne_output n)
    (fun i => Ne.symm (PoweringMachineInitialize.commonPlacement_ne_header _ i .vertices (by decide)))]
  exact PoweringInitializeFrame.prepared_vertices graph n

theorem beforeFinish_darts (graph : PortTables.Table vertices d) (n : Nat) :
    beforeFinish graph n (headerDarts n) =
      encodeWord (PoweringTableLayout.blockSize d n * vertices) := by
  rw [beforeFinish, PoweringMachineOuterLoop.finalTapes_other graph n (placement n)
    (outputTape n) vertices (Nat.le_refl _) (PoweringInitializeFrame.preparedTapes graph n)
    (headerDarts n) (PoweringGlobalConfiguration.headerDarts_ne_output n)
    (fun i => Ne.symm (PoweringMachineInitialize.commonPlacement_ne_header _ i .darts (by decide)))]
  exact PoweringInitializeFrame.prepared_darts graph n

/-- The serialized result is exactly the actual powering table, including its
header and every relation bit, in the existing output codec. -/
theorem serialized_eq (graph : PortTables.Table vertices d) (n : Nat) :
    encodeWords [vertices, PoweringTableLayout.blockSize d n * vertices] ++
      beforeFinish graph n (outputTape n) = PoweringTables.outputBits graph n := by
  rw [beforeFinish_output, PoweringTableLayout.outputBits_vertexRows]
  congr 2
  rw [PoweringTableLayout.dartCount_eq_vertex_blocks, Nat.mul_comm]

/-- The actual final-copy/cleanup cost on the tapes obtained from the loop. -/
def finishSteps (graph : PortTables.Table vertices d) (n : Nat) : Nat :=
  PoweringMachineFinish.steps (enumeration n) (outputTape n) (beforeFinish graph n)
    vertices (PoweringTableLayout.blockSize d n * vertices)

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRuntime

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

def eventOffset (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q)) : Fin (fieldBound q) :=
  ⟨(localEventEquiv q event).val,
    (localEventEquiv q event).isLt.trans (localCount_lt_bound q)⟩

def rawQueryOffset (q : Nat) : Queries.RawQuery q → Fin (fieldBound q)
  | .inl (_, tape) =>
    ⟨(cubeEquiv q tape).val, (cubeEquiv q tape).isLt.trans (tapeCount_lt_bound q)⟩
  | .inr tape =>
    ⟨(pairCubeEquiv q tape).val, (pairCubeEquiv q tape).isLt.trans (pairTapeCount_lt_bound q)⟩

def reverseOffset (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) : Fin (fieldBound q) :=
  ⟨(localEventEquiv q event).val * 12 + slot.val * 2 + bitValue (!orientation), by
    have he := (localEventEquiv q event).isLt
    have hs := slot.isLt
    have hb : bitValue (!orientation) < 2 := by
      simpa only [boolEquiv_val] using (boolEquiv (!orientation)).isLt
    have hbound := twelve_local_lt_bound q
    omega⟩

def eventVertexField (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q)) :
    Field (fieldBound q) :=
  ⟨[(2, localCount q)], eventOffset q event⟩

def rawQueryTerms (q : Nat) : Queries.RawQuery q → Terms
  | .inl (side, _) => vertexQueryTerms q side
  | .inr _ => edgeQueryTerms q

def rawQueryField (q : Nat) (query : Queries.RawQuery q) : Field (fieldBound q) :=
  ⟨rawQueryTerms q query, rawQueryOffset q query⟩

def reverseDartField (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) : Field (fieldBound q) :=
  ⟨[(2, 12 * localCount q)], reverseOffset q event slot orientation⟩

theorem eventVertexField_eval (n m q : Nat) (edge : Fin m)
    (event : AlphabetGraph.LocalEvent (Fin q)) (tail head : Nat) :
    eval (eventVertexField q event) (values n m edge.val tail head) =
      (vertexEquiv n m q (.inl (edge, event))).val := by
  rw [vertexEquiv_event_val, eventEquiv_val]
  simp [eval, eventVertexField, eventOffset, values, Emitter.affineValue, Nat.mul_comm]

theorem rawQueryField_eval (n m q : Nat) (edge : Fin m) (tail head : Fin n)
    (query : Queries.RawQuery q) :
    eval (rawQueryField q query) (values n m edge.val tail.val head.val) =
      (vertexEquiv n m q (.inr (Queries.globalize tail head edge query))).val := by
  cases query with
  | inl query =>
    rcases query with ⟨side, tape⟩
    cases side <;>
      simp [eval, rawQueryField, rawQueryTerms, vertexQueryTerms, rawQueryOffset,
        values, Emitter.affineValue, Queries.globalize, eventCount,
        Nat.mul_comm, Nat.add_assoc]
  | inr tape =>
    simp [eval, rawQueryField, rawQueryTerms, edgeQueryTerms, rawQueryOffset,
      values, Emitter.affineValue, Queries.globalize, eventCount,
      Nat.mul_comm, Nat.add_assoc]

theorem reverseDartField_eval (n m q : Nat) (edge : Fin m)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool)
    (tail head : Nat) :
    eval (reverseDartField q event slot orientation) (values n m edge.val tail head) =
      (dartEquiv m q (QueryIncidence.reverse (((edge, event), slot), orientation))).val := by
  rw [dartEquiv_reverse_val, eventEquiv_val]
  simp [eval, reverseDartField, reverseOffset, values, Emitter.affineValue,
    Nat.mul_add, Nat.mul_comm, Nat.mul_assoc,
    Nat.add_assoc]

def queryEventTerms (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) : Terms :=
  rawQueryTerms q (Queries.query (fun _ _ => false) event slot)

theorem rawQueryTerms_query (q : Nat) (P : Fin q → Fin q → Bool)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) :
    rawQueryTerms q (Queries.query P event slot) = queryEventTerms q event slot := by
  rcases event with ⟨kind, ⟨side, tape⟩, f, g, r₀, r₁, r₂⟩
  by_cases hk₀ : kind = 0 <;> by_cases hk₁ : kind = 1 <;> by_cases hk₂ : kind = 2 <;>
    simp only [queryEventTerms, Queries.query, hk₀, hk₁, hk₂, ite_true, if_true, ite_false]
  all_goals split_ifs <;> rfl

def queryEventOffset (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (P : Fin q → Fin q → Bool) : Fin (fieldBound q) :=
  rawQueryOffset q (Queries.query P event slot)

/-- The sole predicate-dependent component is a bounded finite-state offset. -/
def fieldForQueryEvent (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (P : Fin q → Fin q → Bool) : Field (fieldBound q) :=
  ⟨queryEventTerms q event slot, queryEventOffset q event slot P⟩

theorem fieldForQueryEvent_eq_rawQueryField (q : Nat)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6)
    (P : Fin q → Fin q → Bool) :
    fieldForQueryEvent q event slot P = rawQueryField q (Queries.query P event slot) := by
  unfold fieldForQueryEvent queryEventOffset rawQueryField
  rw [rawQueryTerms_query]

theorem fieldForQueryEvent_eval (n m q : Nat) (edge : Fin m) (tail head : Fin n)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6)
    (P : Fin q → Fin q → Bool) :
    eval (fieldForQueryEvent q event slot P) (values n m edge.val tail.val head.val) =
      (vertexEquiv n m q
        (.inr (Queries.globalize tail head edge (Queries.query P event slot)))).val := by
  rw [fieldForQueryEvent_eq_rawQueryField]
  exact rawQueryField_eval n m q edge tail head _

def dartTailTerms (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) : Terms :=
  if orientation then queryEventTerms q event slot else [(2, localCount q)]

def dartTailOffset (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) (P : Fin q → Fin q → Bool) : Fin (fieldBound q) :=
  if orientation then queryEventOffset q event slot P else eventOffset q event

def fieldForDartTail (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) (P : Fin q → Fin q → Bool) : Field (fieldBound q) :=
  ⟨dartTailTerms q event slot orientation, dartTailOffset q event slot orientation P⟩

theorem fieldForDartTail_eval (n m q : Nat) (edge : Fin m) (tail head : Fin n)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool)
    (P : Fin q → Fin q → Bool) :
    eval (fieldForDartTail q event slot orientation P)
      (values n m edge.val tail.val head.val) =
      (vertexEquiv n m q (if orientation then
        .inr (Queries.globalize tail head edge (Queries.query P event slot))
        else .inl (edge, event))).val := by
  cases orientation with
  | false => exact eventVertexField_eval n m q edge event tail.val head.val
  | true => exact fieldForQueryEvent_eval n m q edge tail head event slot P

theorem rawQueryTerms_length_le (q : Nat) (query : Queries.RawQuery q) :
    (rawQueryTerms q query).length ≤ 3 := by
  cases query with
  | inl query => rcases query with ⟨side, tape⟩; simp [rawQueryTerms, vertexQueryTerms]
  | inr tape => simp [rawQueryTerms, edgeQueryTerms]

theorem queryEventTerms_length_le (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) : (queryEventTerms q event slot).length ≤ 3 :=
  rawQueryTerms_length_le q _

theorem dartTailTerms_length_le (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) :
    (dartTailTerms q event slot orientation).length ≤ 3 := by
  cases orientation with
  | false => simp [dartTailTerms]
  | true => exact queryEventTerms_length_le q event slot

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Addresses

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

variable {Λ : Type} {q : Nat}

/-- One-step simulations transport complete timed executions through the
explicit finite register permutations. -/
def transportInTime {K τ υ : Type} [DecidableEq K] {Γ : K → Type}
    (e : τ ≃ υ) (p : Λ → TM2.Stmt Γ Λ τ)
    {start finish : TM2.Cfg Γ Λ τ} {budget : Nat}
    (run : StateTransition.EvalsToInTime (TM2.step p) start (some finish) budget) :
    StateTransition.EvalsToInTime (TM2.step (MachineControl.program (Equiv.refl Λ) e p))
      (MachineControl.configuration id e start)
      (some (MachineControl.configuration id e finish)) budget := by
  apply MachineComposition.liftExecutionInTime _ _ (MachineControl.configuration id e) _ run
  intro a b hab
  have h := MachineControl.step_simulation (Equiv.refl Λ) e p a
  rw [hab] at h
  exact h

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

/-- A composable block with exactly seven internal control labels. -/
def statement (labels : Label → Λ) (next : Λ) :
    Label → TM2.Stmt Alphabet Λ (State q)
  | .leftFirst => compareStatement (MachineFieldProfile.copyStatement
      (Reduction.MachineTransfer.loopAt .tail .scratch id false
        (labels .leftFirst) (some (labels .leftSecond))))
  | .leftSecond => compareStatement (MachineFieldProfile.copyStatement
      (MachineCopy.forkLoop .scratch .tail .compareLeft false
        (labels .leftSecond) (some (labels .rightFirst))))
  | .rightFirst => compareStatement (MachineFieldProfile.copyStatement
      (Reduction.MachineTransfer.loopAt .head .scratch id false
        (labels .rightFirst) (some (labels .rightSecond))))
  | .rightSecond => compareStatement (MachineFieldProfile.copyStatement
      (MachineCopy.forkLoop .scratch .head .compareRight false
        (labels .rightSecond) (some (labels .compare))))
  | .compare => compareStatement (MachineCompare.loop .compareLeft .compareRight
      (labels .compare) (some (labels .equalStore)) (some (labels .differentStore)))
  | .equalStore => storeLoop true next
  | .differentStore => storeLoop false next

theorem compareProgram_at
    (program : Λ → TM2.Stmt Alphabet Λ (State q)) (label : Λ)
    (stmt : TM2.Stmt Alphabet Λ
      (MachineCompare.State (GenericGraphTables.RelationTable q × Bool)))
    (atLabel : program label = compareStatement stmt) :
    (MachineControl.program (Equiv.refl Λ) (compareEquiv q) program) label = stmt := by
  change MachineControl.statement id (compareEquiv q) (program label) = stmt
  rw [atLabel]
  exact MachineFieldProfile.statement_roundtrip (compareEquiv q) stmt

/-- Compare arbitrary words while restoring every tape, including work tapes.
All program hypotheses specify only the statements at the seven labels. -/
def compareWordsInTime (labels : Label → Λ) (next : Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State q))
    (atLabel : ∀ label, program (labels label) = statement labels next label)
    (base : Tape → List Bool)
    (hLeft : base .compareLeft = []) (hRight : base .compareRight = [])
    (hScratch : base .scratch = [])
    (relation : GenericGraphTables.RelationTable q) (oldLoop : Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .leftFirst), normal relation oldLoop, base⟩
      (some ⟨some next, normal relation (decide (base .tail = base .head)), base⟩)
      (2 * ((base .tail).length + 1) + 2 * ((base .head).length + 1) +
        max (base .tail).length (base .head).length + 2) := by
  let view := MachineControl.program (Equiv.refl Λ) (compareEquiv q) program
  have compared := MachineFieldProfile.nonDestructiveCompareInTime
    Tape.tail Tape.head Tape.compareLeft Tape.compareRight Tape.scratch
    (by decide) (by decide) (by decide)
    (labels .leftFirst) (labels .leftSecond) (labels .rightFirst)
    (labels .rightSecond) (labels .compare)
    (some (labels .equalStore)) (some (labels .differentStore)) view
    (compareProgram_at program _ _ (atLabel .leftFirst))
    (compareProgram_at program _ _ (atLabel .leftSecond))
    (compareProgram_at program _ _ (atLabel .rightFirst))
    (compareProgram_at program _ _ (atLabel .rightSecond))
    (compareProgram_at program _ _ (atLabel .compare))
    base hLeft hRight hScratch (relation, oldLoop)
  have restoredProgram :
      MachineControl.program (Equiv.refl Λ) (compareEquiv q).symm view = program := by
    funext label
    exact MachineFieldProfile.statement_roundtrip (compareEquiv q).symm (program label)
  have transported := transportInTime (compareEquiv q).symm view compared
  rw [restoredProgram] at transported
  have copied : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .leftFirst), normal relation oldLoop, base⟩
      (some ⟨if base .tail = base .head then some (labels .equalStore)
        else some (labels .differentStore), normal relation oldLoop, base⟩)
      (2 * ((base .tail).length + 1) + 2 * ((base .head).length + 1) +
        max (base .tail).length (base .head).length + 1) := by
    simpa [MachineControl.configuration, compareEquiv, MachineFieldProfile.normalState,
      normal] using transported
  have stored : StateTransition.EvalsToInTime (TM2.step program)
      ⟨if base .tail = base .head then some (labels .equalStore)
        else some (labels .differentStore), normal relation oldLoop, base⟩
      (some ⟨some next, normal relation (decide (base .tail = base .head)), base⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change TM2.step program
        ⟨if base .tail = base .head then some (labels .equalStore)
          else some (labels .differentStore), normal relation oldLoop, base⟩ = _
      by_cases heq : base .tail = base .head
      · simp [heq, TM2.step, atLabel, statement, stepAux_storeLoop, normal]
      · simp [heq, TM2.step, atLabel, statement, stepAux_storeLoop, normal]
    steps_le_m := Nat.le_refl _
  }
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ copied stored
  exact { toEvalsTo := run.toEvalsTo, steps_le_m := by have h := run.steps_le_m; omega }

/-- The stored flag is equality of the actual unary endpoint names. -/
def compareInTime (labels : Label → Λ) (next : Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State q))
    (atLabel : ∀ label, program (labels label) = statement labels next label)
    (base : Tape → List Bool) (tailName headName : Nat)
    (hTail : base .tail = encodeWord tailName) (hHead : base .head = encodeWord headName)
    (hLeft : base .compareLeft = []) (hRight : base .compareRight = [])
    (hScratch : base .scratch = [])
    (relation : GenericGraphTables.RelationTable q) (oldLoop : Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .leftFirst), normal relation oldLoop, base⟩
      (some ⟨some next, normal relation (decide (tailName = headName)), base⟩)
      (comparisonTime tailName headName) := by
  have run := compareWordsInTime labels next program atLabel base hLeft hRight hScratch
    relation oldLoop
  simpa only [hTail, hHead, encodeWord_eq_iff, encodeWord_length, comparisonTime,
    Nat.add_assoc] using run

def rowLoop (table : GenericGraphTables.Table q) (e : Fin table.darts) : Bool :=
  decide (table.rows[e].tail.val = table.rows[table.rows[e].reverseIndex].tail.val)

def rowState (table : GenericGraphTables.Table q) (e : Fin table.darts) : State q :=
  normal table.rows[e].relation (rowLoop table e)

def compareRowInTime (labels : Label → Λ) (next : Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State q))
    (atLabel : ∀ label, program (labels label) = statement labels next label)
    (table : GenericGraphTables.Table q) (e : Fin table.darts)
    (base : Tape → List Bool)
    (hTail : base .tail = encodeWord table.rows[e].tail.val)
    (hHead : base .head = encodeWord table.rows[table.rows[e].reverseIndex].tail.val)
    (hLeft : base .compareLeft = []) (hRight : base .compareRight = [])
    (hScratch : base .scratch = []) (oldLoop : Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .leftFirst), normal table.rows[e].relation oldLoop, base⟩
      (some ⟨some next, rowState table e, base⟩) (5 * table.vertices + 6) := by
  let run := compareInTime labels next program atLabel base _ _ hTail hHead
    hLeft hRight hScratch table.rows[e].relation oldLoop
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  exact run.steps_le_m.trans (comparisonTime_le_of_lt _ _ _
    table.rows[e].tail.isLt table.rows[table.rows[e].reverseIndex].tail.isLt)

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
open Emitter

abbrev RowCommand (q : Nat) := Command 5 (Context q) (Addresses.fieldBound q)

def relationBits (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) : List (Context q → Bool) :=
  List.ofFn fun index : Fin 4096 => fun context =>
    (Relations.relationFromTable context.1 context.2 event slot orientation)[index]

theorem relationBits_values (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) (context : Context q) :
    (relationBits q event slot orientation).map (fun bit => if bit context then 1 else 0) =
      GraphTables.relationWords
        (Relations.relationFromTable context.1 context.2 event slot orientation) := by
  exact bitValues_ofFn (fun state : Context q =>
    Relations.relationFromTable state.1 state.2 event slot orientation) context

/-- Two actual affine fields followed by the 4096 stored relation entries. -/
def rowCommands (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) : List (RowCommand q) :=
  affineCommands (Addresses.dartTailTerms q event slot orientation)
      (fun context => Addresses.dartTailOffset q event slot orientation
        (Relations.oldPredicate context.1)) ++
    affineCommands (Addresses.reverseDartField q event slot orientation).terms
      (fun _ => (Addresses.reverseDartField q event slot orientation).offset) ++
    bitCommands (relationBits q event slot orientation)

def rowContext {q : Nat} (input : GenericGraphTables.Table q) (edge : Fin input.darts) : Context q :=
  let old := input.rows[edge]
  (old.relation, decide (old.tail = input.rows[old.reverseIndex].tail))

def rowValues {q : Nat} (input : GenericGraphTables.Table q)
    (edge : Fin input.darts) : Fin 5 → Nat :=
  let old := input.rows[edge]
  Addresses.values input.vertices input.darts edge.val old.tail.val
    input.rows[old.reverseIndex].tail.val

theorem encodedRow {n m : Nat} (row : GraphTables.DartRow n m) :
    encodeWords (GraphTables.rowWords row) =
      encodeWord row.tail.val ++ (encodeWord row.reverseIndex.val ++
        encodeWords (GraphTables.relationWords row.relation)) := by
  simp only [GraphTables.rowWords, List.cons_append, List.nil_append, encodeWords]

/-- The executable command semantics equals the precise stored row, including
the orientation-specific tail, reverse index, and every predicate bit. -/
theorem rowCommands_bits {q : Nat} (input : GenericGraphTables.Table q)
    (edge : Fin input.darts) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) :
    (rowCommands q event slot orientation).flatMap
      (commandBits (rowValues input edge) (rowContext input edge)) =
      encodeWords (GraphTables.rowWords
        (Table.rowFromDart input (((edge, event), slot), orientation))) := by
  rw [rowCommands, List.flatMap_append, List.flatMap_append,
    affineCommands_bits, affineCommands_bits, bitCommands_bits, relationBits_values]
  have htail := Addresses.fieldForDartTail_eval input.vertices input.darts q edge
    input.rows[edge].tail input.rows[input.rows[edge].reverseIndex].tail event slot orientation
    (Relations.oldPredicate input.rows[edge].relation)
  have hreverse := Addresses.reverseDartField_eval input.vertices input.darts q edge
    event slot orientation input.rows[edge].tail.val
      input.rows[input.rows[edge].reverseIndex].tail.val
  let row := Table.rowFromDart input (((edge, event), slot), orientation)
  have tailEq : affineValue (Addresses.dartTailTerms q event slot orientation)
      (rowValues input edge) (Addresses.dartTailOffset q event slot orientation
        (Relations.oldPredicate (rowContext input edge).1)).val = row.tail.val := htail
  have reverseEq : affineValue (Addresses.reverseDartField q event slot orientation).terms
      (rowValues input edge) (Addresses.reverseDartField q event slot orientation).offset.val =
      row.reverseIndex.val := hreverse
  have relationEq : Relations.relationFromTable (rowContext input edge).1
      (rowContext input edge).2 event slot orientation = row.relation := rfl
  rw [encodedRow]
  have combined := congrArg₂ (fun a b : List Bool => a ++ b)
    (congrArg encodeWord tailEq)
    (congrArg₂ (fun a b : List Bool => a ++ b) (congrArg encodeWord reverseEq)
      (congrArg (fun relation => encodeWords (GraphTables.relationWords relation)) relationEq))
  simpa only [List.append_assoc] using combined

/-- One old dart emits every local event, then all six slots, false orientation
before true. These loops are fixed by q and form part of the finite template. -/
def blockCommands (q : Nat) : List (RowCommand q) :=
  (Enumeration.localEvents q).flatMap fun event =>
    (List.finRange 6).flatMap fun slot =>
      [false, true].flatMap fun orientation => rowCommands q event slot orientation

def blockWords {q : Nat} (input : GenericGraphTables.Table q)
    (edge : Fin input.darts) : List Nat :=
  (Enumeration.localEvents q).flatMap fun event =>
    (List.finRange 6).flatMap fun slot =>
      [false, true].flatMap fun orientation =>
        GraphTables.rowWords (Table.rowFromDart input (((edge, event), slot), orientation))

theorem tableWords_eq_blocks {q : Nat}
    (input : GenericGraphTables.Table q) :
    GraphTables.tableWords (Table.build input) =
      [Enumeration.vertexCount input.vertices input.darts q,
        Enumeration.dartCount input.darts q] ++
      (List.finRange input.darts).flatMap (blockWords input) := by
  rw [Table.tableWords_eq_ordered, Enumeration.ordered_dart]
  unfold blockWords
  simp only [List.flatMap_assoc, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

/-- Headers use only the preserved n and m tapes; all relation registers may
still have their initial values. -/
def headerCommands (q : Nat) (σ : Type) : List (Command 2 σ (Addresses.fieldBound q)) :=
  affineCommands [(0, Enumeration.tapeCount q),
      (1, Enumeration.localCount q + Enumeration.pairTapeCount q)]
      (fun _ => Addresses.zeroOffset q) ++
    affineCommands [(1, 12 * Enumeration.localCount q)] (fun _ => Addresses.zeroOffset q)

theorem headerCommands_bits {σ : Type} (q n m : Nat) (ambient : σ) :
    (headerCommands q σ).flatMap (commandBits ![n, m] ambient) =
      encodeWords [Enumeration.vertexCount n m q, Enumeration.dartCount m q] := by
  rw [headerCommands, List.flatMap_append, affineCommands_bits, affineCommands_bits]
  have vertices : affineValue
      [(0, Enumeration.tapeCount q), (1, Enumeration.localCount q + Enumeration.pairTapeCount q)]
      ![n, m] (Addresses.zeroOffset q).val = Enumeration.vertexCount n m q := by
    exact Addresses.headerVertices_eval q n m 0 0 0
  have darts : affineValue [(1, 12 * Enumeration.localCount q)] ![n, m]
      (Addresses.zeroOffset q).val = Enumeration.dartCount m q := by
    exact Addresses.headerDarts_eval q n m 0 0 0
  rw [vertices, darts]
  simp [encodeWords]

@[simp] theorem headerCommands_length (q : Nat) (σ : Type) :
    (headerCommands q σ).length = 7 := by
  simp [headerCommands, affineCommands_length]

theorem blockCommands_bits {q : Nat} (input : GenericGraphTables.Table q)
    (edge : Fin input.darts) :
    (blockCommands q).flatMap (commandBits (rowValues input edge) (rowContext input edge)) =
      encodeWords (blockWords input edge) := by
  simp only [blockCommands, blockWords, List.flatMap_assoc, encodeWords_flatMap,
    rowCommands_bits]

theorem rowCommands_length_le (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) : (rowCommands q event slot orientation).length ≤ 4104 := by
  have htail := Addresses.dartTailTerms_length_le q event slot orientation
  simp only [rowCommands, List.length_append, affineCommands_length,
    Addresses.reverseDartField, List.length_cons, List.length_nil,
    bitCommands, List.length_map, relationBits, List.length_ofFn]
  omega

theorem blockCommands_length_le (q : Nat) :
    (blockCommands q).length ≤ Enumeration.localCount q * (6 * (2 * 4104)) := by
  unfold blockCommands
  apply le_trans (flatMap_length_le _ _ (6 * (2 * 4104)) ?_) (by simp)
  intro event _
  apply le_trans (flatMap_length_le _ _ (2 * 4104) ?_) (by simp)
  intro slot _
  apply le_trans (flatMap_length_le _ _ 4104 ?_) (by simp)
  intro orientation _
  exact rowCommands_length_le q event slot orientation

/-- Preserve additional finite parser/driver registers through a projection. -/
def blockCommandsIn {σ : Type} (q : Nat) (context : σ → Context q) :
    List (Command 5 σ (Addresses.fieldBound q)) :=
  (blockCommands q).map (fun command => command.mapAmbient context)

theorem blockCommandsIn_bits {σ : Type} {q : Nat}
    (input : GenericGraphTables.Table q) (edge : Fin input.darts)
    (context : σ → Context q) (ambient : σ) (hcontext : context ambient = rowContext input edge) :
    (blockCommandsIn q context).flatMap (commandBits (rowValues input edge) ambient) =
      encodeWords (blockWords input edge) := by
  simp only [blockCommandsIn, List.flatMap_map, commandBits_mapAmbient]
  rw [hcontext]
  exact blockCommands_bits input edge

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

def statement (ports : Ports K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .copyFirst => Reduction.MachineTransfer.loopAt (ports 0) (ports 5) id false
      (labels .copyFirst) (some (labels .copySecond))
  | .copySecond => MachineCopy.forkLoop (ports 5) (ports 0) (ports 1) false
      (labels .copySecond) (some (labels .verticesStart))
  | .verticesStart => SourceMachine.fieldStart (ports 2) (labels .verticesLoop)
  | .verticesLoop => SourceMachine.fieldLoop (ports 1) (ports 2)
      (labels .verticesLoop) (some (labels .dartsStart))
  | .dartsStart => SourceMachine.fieldStart (ports 3) (labels .dartsLoop)
  | .dartsLoop => SourceMachine.fieldLoop (ports 1) (ports 3)
      (labels .dartsLoop) (some (labels .counterFirst))
  | .counterFirst => Reduction.MachineTransfer.loopAt (ports 3) (ports 5) id false
      (labels .counterFirst) (some (labels .counterSecond))
  | .counterSecond => MachineCopy.forkLoop (ports 5) (ports 3) (ports 4) false
      (labels .counterSecond) (some (labels .initialize_))
  | .initialize_ => .push (ports 6) (fun _ => false)
      (.load (fun state => (state.1, none)) (Reduction.MachineTransfer.exitAt (ports 6) exit))

/-- Actual program placement is the only execution premise. Header values and
unread row bits specify the input, and every auxiliary role starts empty. -/
def setupInTime (ports : Ports K) (distinct : Function.Injective ports)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ label, program (labels label) = statement ports labels exit label)
    (base : K → List Bool) (n m : Nat) (rows : List Bool)
    (initial : ∀ i : Fin 7, base (ports i) =
      if i = 0 then encodeWord n ++ (encodeWord m ++ rows) else [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .copyFirst), (ambient, register), base⟩
      (some ⟨exit, (ambient, none), resultTapes ports base n m rows⟩)
      (2 * (encodeWord n ++ (encodeWord m ++ rows)).length + n + 3 * m + 11) := by
  let input := encodeWord n ++ (encodeWord m ++ rows)
  let t₀ := Function.update base (ports 1) input
  let t₁ := SourceMachine.afterField (ports 1) (ports 2) t₀ n (encodeWord m ++ rows)
  let t₂ := SourceMachine.afterField (ports 1) (ports 3) t₁ m rows
  let t₃ := Function.update t₂ (ports 4) (encodeWord m)
  have hne {i j : Fin 7} (h : i ≠ j) : ports i ≠ ports j := fun e => h (distinct e)
  have run₀ := MachineCopy.copyInTime (ports 0) (ports 1) (ports 5)
    (hne (by decide)) (hne (by decide)) (hne (by decide)) false
    (labels .copyFirst) (labels .copySecond) (some (labels .verticesStart))
    program (atLabels .copyFirst) (atLabels .copySecond) base
    (by simp [initial]) ambient register
  have hb0 : base (ports 0) = input := by simpa [input] using initial 0
  have hb1 : base (ports 1) = [] := by simpa using initial 1
  rw [hb0, hb1, List.append_nil] at run₀
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (labels .copyFirst), (ambient, register), base⟩
    (some ⟨some (labels .verticesStart), (ambient, none), t₀⟩)
    (2 * (input.length + 1)) at run₀
  have run₁ := SourceMachine.fieldInTime (ports 1) (ports 2) (hne (by decide))
    (labels .verticesStart) (labels .verticesLoop) (some (labels .dartsStart))
    program (atLabels .verticesStart) (atLabels .verticesLoop)
    t₀ n (encodeWord m ++ rows) (by simp [t₀, input]) ambient none
  have run₂ := SourceMachine.fieldInTime (ports 1) (ports 3) (hne (by decide))
    (labels .dartsStart) (labels .dartsLoop) (some (labels .counterFirst))
    program (atLabels .dartsStart) (atLabels .dartsLoop)
    t₁ m rows (by simp [t₁, SourceMachine.afterField, distinct.eq_iff]) ambient none
  have h₂m : t₂ (ports 3) = encodeWord m := by
    simp [t₂, t₁, t₀, SourceMachine.afterField, SourceMachine.fieldTapes,
      distinct.eq_iff, initial]
  have h₂c : t₂ (ports 4) = [] := by
    simp [t₂, t₁, t₀, SourceMachine.afterField, SourceMachine.fieldTapes,
      distinct.eq_iff, initial]
  have h₂s : t₂ (ports 5) = [] := by
    simp [t₂, t₁, t₀, SourceMachine.afterField, SourceMachine.fieldTapes,
      distinct.eq_iff, initial]
  have run₃ := MachineCopy.copyInTime (ports 3) (ports 4) (ports 5)
    (hne (by decide)) (hne (by decide)) (hne (by decide)) false
    (labels .counterFirst) (labels .counterSecond) (some (labels .initialize_))
    program (atLabels .counterFirst) (atLabels .counterSecond) t₂ h₂s ambient none
  rw [h₂m, h₂c, List.append_nil, encodeWord_length] at run₃
  have h₃e : t₃ (ports 6) = [] := by
    simp [t₃, t₂, t₁, t₀, SourceMachine.afterField, SourceMachine.fieldTapes,
      distinct.eq_iff, initial]
  have hresult : Function.update t₃ (ports 6) [false] =
      resultTapes ports base n m rows := by
    funext tape
    by_cases h1 : tape = ports 1
    · subst tape; simp [t₃, t₂, t₁, t₀, SourceMachine.afterField,
        SourceMachine.fieldTapes, resultTapes, distinct.eq_iff]
    · by_cases h2 : tape = ports 2
      · subst tape; simp [t₃, t₂, t₁, t₀, SourceMachine.afterField,
          SourceMachine.fieldTapes, resultTapes, distinct.eq_iff, initial]
      · by_cases h3 : tape = ports 3
        · subst tape; simp [t₃, t₂, t₁, t₀, SourceMachine.afterField,
            SourceMachine.fieldTapes, resultTapes, distinct.eq_iff, initial]
        · simp [t₃, t₂, t₁, t₀, SourceMachine.afterField, SourceMachine.fieldTapes,
            resultTapes, Function.update_apply, h1, h2, h3, encodeWord]
  have run₄ : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .initialize_), (ambient, none), t₃⟩
      (some ⟨exit, (ambient, none), resultTapes ports base n m rows⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change some (TM2.stepAux (program (labels .initialize_)) (ambient, none) t₃) = _
      rw [atLabels]
      cases exit <;> simp [statement, TM2.stepAux, Reduction.MachineTransfer.exitAt,
        h₃e, hresult]
    steps_le_m := Nat.le_refl _ }
  let r₀₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₀ run₁
  let r₀₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₀₁ run₂
  let r₀₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₀₁₂ run₃
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₀₁₂₃ run₄
  exact {
    toEvalsTo := run.toEvalsTo
    steps_le_m := by
      have h := run.steps_le_m
      dsimp [input] at h
      omega }

/-- Specialization to the checked graph-table codec. The bound follows from
the actual copy and delimiter-scan traces above. -/
def tableSetupInTime {q : Nat} (ports : Ports K) (distinct : Function.Injective ports)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ label, program (labels label) = statement ports labels exit label)
    (base : K → List Bool) (table : GenericGraphTables.Table q)
    (initial : ∀ i : Fin 7, base (ports i) =
      if i = 0 then GenericGraphTables.tableBits table else [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .copyFirst), (ambient, register), base⟩
      (some ⟨exit, (ambient, none), resultTapes ports base table.vertices table.darts
        (encodeWords ((GenericGraphTables.rowList table).flatMap GenericGraphTables.rowWords))⟩)
      (6 * (GenericGraphTables.tableBits table).length + 11) := by
  have hb := Input.tableBits_header table
  let run := setupInTime ports distinct labels exit program atLabels base
    table.vertices table.darts
    (encodeWords ((GenericGraphTables.rowList table).flatMap GenericGraphTables.rowWords))
    (by intro i; rw [initial i, hb]) ambient register
  have hn := GenericGraphTables.vertices_le_tableBits_length table
  have hm := GenericGraphTables.darts_le_tableBits_length table
  exact {
    toEvalsTo := run.toEvalsTo
    steps_le_m := by
      have h := run.steps_le_m
      have hlen := congrArg List.length hb
      omega }

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Setup

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_DriverLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Driver

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad
open RuntimeModel

def headerPlan (q : Nat) := EmitRows.headerCommands q (Ambient q)
def rowPlan (q : Nat) := EmitRows.blockCommandsIn q (@context q)

inductive Label (q : Nat)
  | setup (label : Setup.Label)
  | header (label : Emitter.Label (headerPlan q).length (Addresses.fieldBound q))
  | guard | tailStart | tailLoop | reverseStart | reverseLoop | readPredicate
  | headCopyFirst | headCopySecond | indexCopyFirst | indexCopySecond
  | headVertices | headDarts | headLookup (label : Lookup.Label)
  | compare (label : CompareLoop.Label)
  | emit (label : Emitter.Label (rowPlan q).length (Addresses.fieldBound q))
  | clearField (slot : Fin 3)
  | increment | reverseOutput | cleanup (slot : Fin 16)
  deriving DecidableEq, Fintype

def headerEntry (q : Nat) : Label q :=
  .header (Emitter.labelAt (headerPlan q).length (Addresses.fieldBound q) 0 .entry)

def rowEntry (q : Nat) : Label q :=
  .emit (Emitter.labelAt (rowPlan q).length (Addresses.fieldBound q) 0 .entry)

def clearNext {q : Nat} (slot : Fin 3) : Label q :=
  if h : slot.val < 2 then .clearField ⟨slot.val + 1, by omega⟩ else .increment

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Driver

/-! The actual final driver phases: reverse the accumulated output, drain all
fifteen nonoutput stacks, reset the finite state, and reach `haltList`.
Polynomial resource bounds below require an actual preceding execution. -/

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

/-- Exact Boolean semantics, with the three stored bits read from one assignment.
There is no distinct-address assumption. -/
theorem equation_satisfied (π : J → I) (i₀ : I) (j₀ : J)
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool)
    (f : Cube I) (g μ : Cube J) :
    satisfied (equation π i₀ j₀ f g μ) (storedAssignment tableA tableB) =
      !(foldedAnswer i₀ tableA f ^^ foldedAnswer j₀ tableB g ^^
        foldedAnswer j₀ tableB (thirdQuery π f g μ)) := by
  change ((tableA (canonicalInput i₀ f) ^^ tableB (canonicalInput j₀ g) ^^
      tableB (canonicalInput j₀ (thirdQuery π f g μ))) == rhsCorrection π i₀ j₀ f μ) = _
  rw [← correction_eq π i₀ j₀ f g μ]
  exact xor_corrections _ _ _ _ _ _

/-- Repeated variable occurrences retain XOR multiplicity and cancel in pairs. -/
theorem satisfied_repeated_right {Name : Type} (e : Equation Name)
    (assignment : Name → Bool) (h : e.second = e.third) :
    satisfied e assignment = (assignment e.first == e.rhs) := by
  unfold satisfied
  rw [← h]
  cases assignment e.first <;> cases assignment e.second <;> cases e.rhs <;> rfl

theorem conditionedEquation_satisfied (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true})
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool)
    (f : Cube I) (g μ : Cube J) :
    satisfied (conditionedEquation valid π i₀ j₀ f g μ) (storedAssignment tableA tableB) =
      !(foldedAnswer i₀ tableA f ^^ conditionedFoldedAnswer valid j₀ tableB g ^^
        conditionedFoldedAnswer valid j₀ tableB (thirdQuery π f g μ)) := by
  unfold conditionedEquation
  rw [equation_satisfied]
  simp only [conditionedFoldedAnswer, restrict_thirdQuery]

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

theorem satisfied_mapEquation {Name Name' : Type} (rename : Name → Name')
    (e : Equation Name) (assignment : Name' → Bool) :
    satisfied (mapEquation rename e) assignment = satisfied e (assignment ∘ rename) := rfl

namespace EmptyContext

variable {I : Type}

/-- Exact semantics for every assignment, including an arbitrary dummy bit. -/
theorem equation_satisfied (i₀ : I) (assignment : Address i₀ → Bool) (f : Cube I) :
    satisfied (equation i₀ f) assignment =
      !(foldedAnswer i₀ (fun h => assignment (.inl h)) f) := by
  rw [FoldedEquation.satisfied_repeated_right (equation i₀ f) assignment rfl]
  change (assignment (.inl (canonicalInput i₀ f)) == f i₀) =
    !(assignment (.inl (canonicalInput i₀ f)) ^^ f i₀)
  cases assignment (.inl (canonicalInput i₀ f)) <;> cases f i₀ <;> rfl

end EmptyContext
end UniqueGamesTheorem.Foundations.Hastad

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_FourierResponseLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

theorem validDecoderSuccess_le_response (valid : J → Bool) (π : J → I)
    (fallbackI : I) (fallbackJ : J) (A : Cube I → Bool) (B : Cube J → Bool) :
    validDecoderSuccess valid π A B ≤
      validResponseAgreement valid π fallbackI fallbackJ A B := by
  unfold validDecoderSuccess validResponseAgreement
  rw [FiniteDistribution.expectation_comm]
  rw [fourierResponse_expectation fallbackJ B]
  apply Finset.sum_le_sum
  intro b _
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  rw [FiniteDistribution.expectation_comm]
  rw [fourierResponse_expectation fallbackI A]
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact validAgreement_le_supportResponses valid π fallbackI fallbackJ a b

/-- Local soundness now bounds the success of two genuine normalized answer
laws. No assumption about randomized decoding or its normalization remains. -/
theorem conditioned_folded_response_bound (ε : ℝ) (π : J → I) (valid : J → Bool)
    (i₀ : I) (tableA : HalfCube i₀ → Bool)
    (j₀ : {j : J // valid j = true}) (tableB : HalfCube j₀ → Bool)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    4 * ε * testBias ε π (fun f => bitSign (foldedAnswer i₀ tableA f))
      (fun g => bitSign (conditionedFoldedAnswer valid j₀ tableB g)) ^ 2 ≤
      validResponseAgreement valid π i₀ j₀.val (foldedAnswer i₀ tableA)
        (conditionedFoldedAnswer valid j₀ tableB) :=
  (conditioned_folded_decoder_bound ε π valid i₀ tableA j₀ tableB hε hε').trans
    (validDecoderSuccess_le_response valid π i₀ j₀.val _ _)

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

variable {Q₁ Q₂ I J : Type*}
  [Fintype Q₁] [DecidableEq Q₁] [Fintype Q₂] [DecidableEq Q₂]
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype J] [DecidableEq J] [Nonempty J]

omit [Nonempty I] [Nonempty J] in
theorem conditionedOracle_response_bound (ε : ℝ) (π : J → I) (valid : J → Bool)
    (i₀ : I) (tableA : HalfCube i₀ → Bool) (default : J)
    (right : ConditionedOracle valid) (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    4 * ε * testBias ε π (fun f => bitSign (foldedAnswer i₀ tableA f))
      (fun g => bitSign (right.answer g)) ^ 2 ≤
      validResponseAgreement valid π i₀ (right.fallback default)
        (foldedAnswer i₀ tableA) right.answer := by
  cases right with
  | empty noLegal =>
      simp only [ConditionedOracle.answer, ConditionedOracle.fallback,
        empty_conditioned_bias, pow_two, mul_zero]
      unfold validResponseAgreement
      apply response_expectation_nonnegative
      intro i
      apply response_expectation_nonnegative
      intro j
      split_ifs <;> norm_num
  | stored j₀ table =>
      exact conditioned_folded_response_bound ε π valid i₀ tableA j₀ table hε hε'

/-- The game bound includes inconsistent clause tuples, whose legal local
domain is empty and whose implemented right oracle is constant. -/
theorem conditionedOracle_game_decoder_bound
    (questions : FiniteDistribution (Q₁ × Q₂))
    (ε : ℝ) (π : Q₁ → Q₂ → J → I) (valid : Q₂ → J → Bool)
    (i₀ : Q₁ → I) (tableA : ∀ q, HalfCube (i₀ q) → Bool)
    (default : J) (right : ∀ q, ConditionedOracle (valid q))
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    4 * ε * questions.expectation (questionBias ε π
      (fun q => foldedAnswer (i₀ q) (tableA q)) (fun q => (right q).answer)) ^ 2 ≤
      (projectionGame questions π valid).value := by
  let A := fun q => foldedAnswer (i₀ q) (tableA q)
  let B := fun q => (right q).answer
  let bias := questionBias ε π A B
  calc
    _ ≤ 4 * ε * questions.expectation (fun q => bias q ^ 2) :=
      mul_le_mul_of_nonneg_left (distribution_sq_expectation_le questions bias) (by linarith)
    _ = questions.expectation (fun q => 4 * ε * bias q ^ 2) := by
      unfold FiniteDistribution.expectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ ≤ questions.expectation (fun q =>
        validResponseAgreement (valid q.2) (π q.1 q.2) (i₀ q.1)
          ((right q.2).fallback default) (A q.1) (B q.2)) := by
      unfold FiniteDistribution.expectation
      apply Finset.sum_le_sum
      intro q _
      apply mul_le_mul_of_nonneg_left _ (questions.nonnegative q)
      exact conditionedOracle_response_bound ε (π q.1 q.2) (valid q.2)
        (i₀ q.1) (tableA q.1) default (right q.2) hε hε'
    _ = (projectionGame questions π valid).stochasticSuccess
        (fun q => fourierResponse (i₀ q) (A q))
        (fun q => fourierResponse ((right q).fallback default) (B q)) := by
      simp [Game.stochasticSuccess, projectionGame, validResponseAgreement]
    _ ≤ _ := Game.stochasticSuccess_le_value _ _ _

theorem conditionedOracle_acceptance_bound
    (questions : FiniteDistribution (Q₁ × Q₂))
    (ε δ : ℝ) (π : Q₁ → Q₂ → J → I) (valid : Q₂ → J → Bool)
    (i₀ : Q₁ → I) (tableA : ∀ q, HalfCube (i₀ q) → Bool)
    (default : J) (right : ∀ q, ConditionedOracle (valid q))
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2) (hδ : 0 ≤ δ)
    (hvalue : (projectionGame questions π valid).value ≤ 4 * ε * δ ^ 2) :
    questions.expectation (questionAcceptance ε π
      (fun q => foldedAnswer (i₀ q) (tableA q)) (fun q => (right q).answer)) ≤
      (1 + δ) / 2 := by
  have hd := conditionedOracle_game_decoder_bound questions ε π valid i₀ tableA
    default right hε hε'
  have hpos : 0 < 4 * ε := by positivity
  have hs := le_of_mul_le_mul_left (hd.trans hvalue) hpos
  rw [questionAcceptance_eq]
  nlinarith

end UniqueGamesTheorem.Foundations.Hastad

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_HonestTestLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.slotFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace UniqueGamesTheorem.Foundations.Hastad.SourceGame

open scoped BigOperators
open Target PCP Games SourceContexts

theorem eventLaw_probability (F : Formula) (hne : F.clauses ≠ [])
    (P : RandomEvent F → Bool) :
    (eventLaw F hne).probability P =
      (∑ e : RandomEvent F, if P e then (1 : ℝ) else 0) /
        (3 * F.clauses.length : ℕ) := by
  classical
  simp only [eventLaw, FiniteDistribution.uniform, FiniteDistribution.probability]
  simp_rw [div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  cases P e <;> simp [RandomEvent, Fintype.card_prod, card_slot, Nat.mul_comm]

theorem sum_slots (H : Slot → ℝ) :
    (∑ s : Slot, H s) = H .first + H .second + H .third := by
  have hu : (Finset.univ : Finset Slot) = {.first, .second, .third} := by
    ext s
    cases s <;> simp
  rw [hu]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    reduceCtorEq, or_self, not_false_eq_true, Finset.sum_singleton]
  ring

theorem sum_slot_accepts (F : Formula) (alice : AliceStrategy F)
    (bob : BobStrategy F) (c : Fin F.clauses.length) :
    (∑ s : Slot, if accepts F alice bob (c,s) then (1 : ℝ) else 0) =
      (acceptedSlots (clauseAt F c) (alice c)
        (honestAnswer (clauseAt F c) bob) : ℕ) := by
  rw [sum_slots]
  by_cases hs : localSatisfies (clauseAt F c) (alice c) = true
  · by_cases h₁ : (alice c).first = bob (clauseAt F c)[0].variableIndex <;>
      by_cases h₂ : (alice c).second = bob (clauseAt F c)[1].variableIndex <;>
      by_cases h₃ : (alice c).third = bob (clauseAt F c)[2].variableIndex <;>
      norm_num [accepts, hs, acceptedSlots, matchingSlots, honestAnswer, answerAt, nameAt,
        h₁, h₂, h₃]
  · simp [accepts, acceptedSlots, hs]

theorem failureCount_eq_sum_map (F : Formula) (bob : BobStrategy F)
    (cs : List (Fin F.clauses.length)) :
    failureCount F bob cs =
      (cs.map (fun c => clauseFailure (clauseAt F c) bob)).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [failureCount, List.map_cons, List.sum_cons, ih]

theorem failureCount_allIndices (F : Formula) (bob : BobStrategy F) :
    failureCount F bob (allIndices F) =
      ∑ c : Fin F.clauses.length, clauseFailure (clauseAt F c) bob := by
  rw [failureCount_eq_sum_map]
  unfold allIndices
  rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]

/-- The local three-slot rejection inequality controls the actual uniform
incidence law, including repeated variable names and repeated clauses. -/
theorem verifier_probability_plus_failure (F : Formula) (hne : F.clauses ≠ [])
    (alice : AliceStrategy F) (bob : BobStrategy F) :
    (eventLaw F hne).probability (accepts F alice bob) +
      (failureCount F bob (allIndices F) : ℝ) / (3 * F.clauses.length : ℕ) ≤ 1 := by
  have hm : (0 : ℝ) < (3 * F.clauses.length : ℕ) := by
    exact_mod_cast Nat.mul_pos (by decide : 0 < 3) (List.length_pos_iff.mpr hne)
  have hlocal (c : Fin F.clauses.length) :
      (∑ s : Slot, if accepts F alice bob (c,s) then (1 : ℝ) else 0) +
        (clauseFailure (clauseAt F c) bob : ℝ) ≤ 3 := by
    rw [sum_slot_accepts]
    exact_mod_cast local_rejection_bound (clauseAt F c) (alice c) bob
  have hsum := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset _)) => hlocal c)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [eventLaw_probability, failureCount_allIndices]
  push_cast
  push_cast at hm
  rw [Fintype.sum_prod_type, ← add_div]
  apply (div_le_one hm).mpr
  simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_comm] using hsum

theorem base_success_le_verifier (F : Formula) (hne : F.clauses ≠ [])
    (strategy : Strategy (Fin F.variables) (Fin F.clauses.length) Bool ClauseAnswer) :
    (baseGame F hne).success strategy ≤
      (eventLaw F hne).probability (accepts F strategy.2 strategy.1) := by
  unfold Game.success baseGame
  rw [FiniteDistribution.probability_pushforward]
  apply FiniteDistribution.probability_mono
  intro e he
  exact baseAccepts_implies_sampled F e.1 e.2 _ _ he

/-- A concrete clause-count gap supplies the base-game value bound. -/
theorem base_value_le_of_clause_gap (F : Formula) (hne : F.clauses ≠ [])
    (δ : ℝ) (hgap : ∀ bob : BobStrategy F,
      δ * F.clauses.length ≤ (failureCount F bob (allIndices F) : ℝ)) :
    (baseGame F hne).value ≤ 1 - δ / 3 := by
  apply (Game.value_le_iff _ _).mpr
  intro strategy
  have hbase := base_success_le_verifier F hne strategy
  have hprob := verifier_probability_plus_failure F hne strategy.2 strategy.1
  have hm : (0 : ℝ) < F.clauses.length :=
    Nat.cast_pos.mpr (List.length_pos_iff.mpr hne)
  have hg : δ / 3 ≤ (failureCount F strategy.1 (allIndices F) : ℝ) /
      (3 * F.clauses.length : ℕ) := by
    have hden : (0 : ℝ) < (3 * F.clauses.length : ℕ) := by
      exact_mod_cast Nat.mul_pos (by decide : 0 < 3) (List.length_pos_iff.mpr hne)
    apply (le_div_iff₀ hden).mpr
    calc
      δ / 3 * (3 * F.clauses.length : ℕ) = δ * F.clauses.length := by push_cast; ring
      _ ≤ _ := hgap strategy.1
  linarith

theorem pushforward_comp {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (μ : FiniteDistribution X) (f : X → Y) (g : Y → Z) :
    (μ.pushforward f).pushforward g = μ.pushforward (g ∘ f) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  simp only [FiniteDistribution.pushforward]
  calc
    _ = ∑ y : Y, ∑ x : X, if f x = y then
        (if g y = z then μ.weight x else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : g y = z <;> simp [h]
    _ = _ := by rw [Finset.sum_comm]; simp

theorem expectation_pushforward {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : FiniteDistribution X) (f : X → Y) (H : Y → ℝ) :
    (μ.pushforward f).expectation H = μ.expectation (H ∘ f) := by
  classical
  simp only [FiniteDistribution.expectation, FiniteDistribution.pushforward,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_mul]

def repeatedVisible (F : Formula) (u : ℕ) (events : Fin u → RandomEvent F) :
    VariableContext F u × ClauseContext F u :=
  (fun t => nameAt (clauseAt F (events t).1) (events t).2,
   fun t => (events t).1)

/-- This identifies the repeated game law with the actual uniformly sampled
incidence tuples, retaining all collisions of their visible questions. -/
theorem repeated_questions (F : Formula) (hne : F.clauses ≠ []) (u : ℕ) :
    ((baseGame F hne).repetition u).questions =
      ((eventLaw F hne).iid u).pushforward (repeatedVisible F u) := by
  change (((eventLaw F hne).pushforward (visibleQuestion F)).iid u).transport
    (Game.tupleQuestionEquiv u) = _
  rw [FiniteDistribution.iid_pushforward, ← FiniteDistribution.pushforward_equiv,
    pushforward_comp]
  rfl

theorem repeated_expectation (F : Formula) (hne : F.clauses ≠ []) (u : ℕ)
    (H : VariableContext F u × ClauseContext F u → ℝ) :
    ((baseGame F hne).repetition u).questions.expectation H =
      𝔼 events : Fin u → RandomEvent F, H (repeatedVisible F u events) := by
  let : Nonempty (RandomEvent F) := event_nonempty F hne
  rw [repeated_questions, expectation_pushforward]
  change ((FiniteDistribution.uniform (RandomEvent F)).iid u).expectation _ = _
  rw [FiniteDistribution.iid_uniform, FiniteDistribution.expectation_uniform,
    Fintype.expect_eq_sum_div_card]
  rfl

/-- The concrete constructor enumerates clause tuples and slot tuples as
separate lexicographic factors; this is exactly the same question law. -/
theorem repeated_expectation_split (F : Formula) (hne : F.clauses ≠ []) (u : ℕ)
    (H : VariableContext F u × ClauseContext F u → ℝ) :
    ((baseGame F hne).repetition u).questions.expectation H =
      𝔼 c : ClauseContext F u, 𝔼 s : SlotContext u,
        H (sampledVariables F c s, c) := by
  rw [repeated_expectation]
  calc
    _ = 𝔼 p : ClauseContext F u × SlotContext u,
        H (sampledVariables F p.1 p.2, p.1) :=
      Fintype.expect_equiv
        (Game.tupleQuestionEquiv (Q₁ := Fin F.clauses.length) (Q₂ := Slot) u)
        _ _ (fun _ => rfl)
    _ = _ := SourceTape.expect_prod _

def sourceProjectionGame (F : Formula) (hne : F.clauses ≠ []) (u : ℕ) :
    Game (VariableContext F u) (ClauseContext F u) (I u) (J u) :=
  projectionGame ((baseGame F hne).repetition u).questions
    (fun v c => pi F c v) (validJ F)

/-- The projection game has exactly the repeated question law, and its
legal right answers satisfy every coordinate of the original game. -/
theorem projection_value_le_repetition (F : Formula) (hne : F.clauses ≠ [])
    (u : ℕ) :
    (sourceProjectionGame F hne u).value ≤ ((baseGame F hne).repetition u).value := by
  apply (Game.value_le_iff _ _).mpr
  intro strategy
  have h : (sourceProjectionGame F hne u).success strategy ≤
      ((baseGame F hne).repetition u).success strategy := by
    apply FiniteDistribution.probability_mono
    intro q hq
    have hlegal : pi F q.2 q.1 (strategy.2 q.2) = strategy.1 q.1 ∧
        validJ F q.2 (strategy.2 q.2) = true := by
      simpa only [Game.wins, sourceProjectionGame, projectionGame,
        decide_eq_true_eq] using hq
    apply (Game.repetition_accepts_iff _ _ _ _ _ _).mpr
    intro t
    exact projection_implies_coordinate_accepts F q.2 q.1
      (strategy.1 q.1) (strategy.2 q.2) hlegal.2 hlegal.1 t
  exact h.trans (Game.success_le_value _ strategy)

theorem source_acceptance_le_split (F : Formula) (hne : F.clauses ≠ []) (u : ℕ)
    (ε δ : ℝ) (i₀ : VariableContext F u → I u)
    (tableA : ∀ v, HalfCube (i₀ v) → Bool)
    (right : ∀ c : ClauseContext F u, ConditionedOracle (validJ F c))
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2) (hδ : 0 ≤ δ)
    (hvalue : ((baseGame F hne).repetition u).value ≤ 4 * ε * δ ^ 2) :
    (𝔼 c : ClauseContext F u, 𝔼 s : SlotContext u,
      testAcceptance ε (pi F c (sampledVariables F c s))
        (foldedAnswer (i₀ (sampledVariables F c s)) (tableA (sampledVariables F c s)))
        (right c).answer) ≤ (1 + δ) / 2 := by
  have h := conditionedOracle_acceptance_bound
    ((baseGame F hne).repetition u).questions ε δ (fun v c => pi F c v)
    (validJ F) i₀ tableA (fun _ => default) right hε hε' hδ
    ((projection_value_le_repetition F hne u).trans hvalue)
  rw [repeated_expectation_split] at h
  exact h

end UniqueGamesTheorem.Foundations.Hastad.SourceGame

end

end

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

def rowsBits (input : GenericGraphTables.Table q) : List Bool :=
  encodeWords ((GenericGraphTables.rowList input).flatMap GenericGraphTables.rowWords)

def headerBits (input : GenericGraphTables.Table q) : List Bool :=
  encodeWords [Enumeration.vertexCount input.vertices input.darts q,
    Enumeration.dartCount input.darts q]

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Initialization

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_LoopState
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Exact tape invariant for the old-dart loop. The cursor stores the remaining
input rows, while the reversed tape stores precisely the output headers and
the blocks already emitted. The scan and index-scan tapes are unconstrained:
the next lookup prefixes fresh copies and retains old residues as suffixes.
Finite control state is specified by the actual execution theorems using this
tape invariant.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState

open UniqueGamesTheorem.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

def inputBits (input : GenericGraphTables.Table q) : List Bool :=
  GenericGraphTables.tableBits input

/-- The output headers are included even before the first old row is read. -/
def prefixWords (input : GenericGraphTables.Table q) (e : Nat) : List Nat :=
  [Enumeration.vertexCount input.vertices input.darts q,
    Enumeration.dartCount input.darts q] ++
    ((List.finRange input.darts).take e).flatMap (EmitRows.blockWords input)

def prefixBits (input : GenericGraphTables.Table q) (e : Nat) : List Bool :=
  encodeWords (prefixWords input e)

def cursorWords (input : GenericGraphTables.Table q) (e : Nat) : List Nat :=
  ((GenericGraphTables.rowList input).drop e).flatMap GenericGraphTables.rowWords

def cursorBits (input : GenericGraphTables.Table q) (e : Nat) : List Bool :=
  encodeWords (cursorWords input e)

@[simp] theorem prefixWords_zero (input : GenericGraphTables.Table q) :
    prefixWords input 0 =
      [Enumeration.vertexCount input.vertices input.darts q,
        Enumeration.dartCount input.darts q] := by
  simp [prefixWords]

@[simp] theorem prefixBits_zero (input : GenericGraphTables.Table q) :
    prefixBits input 0 = encodeWords
      [Enumeration.vertexCount input.vertices input.darts q,
        Enumeration.dartCount input.darts q] := by
  rw [prefixBits, prefixWords_zero]

theorem prefixWords_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    prefixWords input (e + 1) =
      prefixWords input e ++ EmitRows.blockWords input ⟨e, he⟩ := by
  have bound : e < (List.finRange input.darts).length := by simpa using he
  have take := List.take_succ_eq_append_getElem bound
  have atIndex : (List.finRange input.darts)[e]'bound = (⟨e, he⟩ : Fin input.darts) := by
    simp
  rw [atIndex] at take
  unfold prefixWords
  rw [take, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem prefixBits_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    prefixBits input (e + 1) =
      prefixBits input e ++ encodeWords (EmitRows.blockWords input ⟨e, he⟩) := by
  rw [prefixBits, prefixWords_succ input e he, encodeWords_append]
  rfl

theorem prefixBits_reverse_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    (prefixBits input (e + 1)).reverse =
      (encodeWords (EmitRows.blockWords input ⟨e, he⟩)).reverse ++
        (prefixBits input e).reverse := by
  rw [prefixBits_succ input e he, List.reverse_append]

theorem prefixWords_full (input : GenericGraphTables.Table q) :
    prefixWords input input.darts = GraphTables.tableWords (Table.build input) := by
  have allRows : (List.finRange input.darts).take input.darts = List.finRange input.darts := by
    apply List.take_of_length_le
    simp
  unfold prefixWords
  rw [allRows]
  exact (EmitRows.tableWords_eq_blocks input).symm

/-- At the terminal guard the stored prefix is the complete concrete output encoding. -/
theorem prefixBits_full (input : GenericGraphTables.Table q) :
    prefixBits input input.darts = GraphTables.tableBits (Table.build input) := by
  rw [prefixBits, prefixWords_full]
  rfl

@[simp] theorem cursorBits_zero (input : GenericGraphTables.Table q) :
    cursorBits input 0 =
      encodeWords ((GenericGraphTables.rowList input).flatMap GenericGraphTables.rowWords) := by
  simp [cursorBits, cursorWords]

theorem cursorWords_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    cursorWords input e =
      GenericGraphTables.rowWords input.rows[(⟨e, he⟩ : Fin input.darts)] ++
      cursorWords input (e + 1) := by
  have bound : e < (GenericGraphTables.rowList input).length := by
    simpa only [GenericGraphTables.rowList_length] using he
  unfold cursorWords
  rw [List.drop_eq_getElem_cons bound, List.flatMap_cons]
  simp only [GenericGraphTables.rowList, Vector.getElem_toList, Fin.getElem_fin]

theorem cursorBits_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    cursorBits input e =
      encodeWords (GenericGraphTables.rowWords input.rows[(⟨e, he⟩ : Fin input.darts)]) ++
      cursorBits input (e + 1) := by
  rw [cursorBits, cursorWords_succ input e he, encodeWords_append]
  rfl

@[simp] theorem cursorBits_full (input : GenericGraphTables.Table q) :
    cursorBits input input.darts = [] := by
  have finished := List.drop_length (l := GenericGraphTables.rowList input)
  rw [GenericGraphTables.rowList_length] at finished
  unfold cursorBits cursorWords
  rw [finished]
  rfl

/-- Guard-to-guard tape contract. Only scan and indexScan may contain residues. -/
structure Ready (input : GenericGraphTables.Table q) (e : Nat)
    (base : Tape → List Bool) : Prop where
  le_darts : e ≤ input.darts
  original : base .original = inputBits input
  cursor : base .cursor = cursorBits input e
  vertices : base .vertices = encodeWord input.vertices
  darts : base .darts = encodeWord input.darts
  counter : base .counter = encodeWord (input.darts - e)
  edge : base .edge = encodeWord e
  tail : base .tail = []
  reverseIndex : base .reverseIndex = []
  head : base .head = []
  scratch : base .scratch = []
  compareLeft : base .compareLeft = []
  compareRight : base .compareRight = []
  output : base .output = []
  reversed : base .reversed = (prefixBits input e).reverse

theorem Ready.counter_succ {input : GenericGraphTables.Table q} {e : Nat}
    {base : Tape → List Bool} (ready : Ready input e base) (he : e < input.darts) :
    base .counter = encodeWord (input.darts - (e + 1) + 1) := by
  rw [ready.counter]
  congr 1
  omega

theorem Ready.counter_at_end {input : GenericGraphTables.Table q}
    {base : Tape → List Bool} (ready : Ready input input.darts base) :
    base .counter = encodeWord 0 := by
  simpa only [Nat.sub_self] using ready.counter

theorem Ready.reversed_at_end {input : GenericGraphTables.Table q}
    {base : Tape → List Bool} (ready : Ready input input.darts base) :
    base .reversed = (GraphTables.tableBits (Table.build input)).reverse := by
  rw [ready.reversed, prefixBits_full]

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState

end

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



/-! Every work tape of the actual alphabet-table machine stores Bool symbols.
This checks the work alphabets separately from the finite-machine structure's
input-alphabet condition, without changing the runtime certificate. -/



/-! The actual padding, expander overlay, and lazy-loop stages composed into
one polynomial-time finite machine. The initial degree-replacement stage is
assembled separately. -/
namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingFinishRuntime

open Turing UniqueGamesTheorem.Foundations.Complexity
open PreprocessingRegularTables

def finish (H : PreprocessingTables.BaseTable) (d : Nat) (input : PortTables.Input d) :
    PortTables.Input (2 * (d + internalDegree)) :=
  PreprocessingStageMaps.lazy (d + internalDegree)
    (PreprocessingStageMaps.paddedOverlay H d input)

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

theorem trueRelationWords :
    GraphTables.relationWords (GraphTables.relationOf (fun _ _ => true)) =
      List.replicate 4096 1 := by
  unfold GraphTables.relationWords
  rw [GraphTables.relationOf, Vector.toList_ofFn, List.map_ofFn]
  exact List.ofFn_const 4096 1

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineFinish

end

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

def headerTapes (n m : ℕ) (clauseBits : List Bool) : Tape → List Bool
  | .input => clauseBits
  | .variables => encodeWord n
  | .counter => encodeWord m
  | .reversed => (encodeWords [n + m + 1, 6 * m + 1]).reverse
  | _ => []

/-- Complete machine frame at the first clause-loop guard. -/
def startTapes (n m : ℕ) (clauseBits : List Bool) : Tape → List Bool
  | .input => clauseBits
  | .variables => encodeWord n
  | .counter => encodeWord m
  | .index => [false]
  | .reversed => (encodeWords [n + m + 1, 6 * m + 1]).reverse
  | _ => []

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineStart

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceOccurrences
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

section LocalEquations

variable {V C I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem conditionedOccurrence_satisfied
    (vE : Encoding V) (cE : Encoding C) (iE : Encoding I) (jE : Encoding J)
    (v : V) (c : C) (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true})
    (bits : Fin (globalEncoding vE cE iE jE).size → Bool)
    (f : Cube I) (g μ : Cube J) :
    satisfied (conditionedOccurrence vE cE iE jE v c valid π i₀ j₀ f g μ) bits =
      !(foldedAnswer i₀ (fun h => bits ((globalEncoding vE cE iE jE).code (.inl (v, h.val)))) f ^^
        conditionedFoldedAnswer valid j₀
          (fun h => bits ((globalEncoding vE cE iE jE).code
            (.inr (.inl (c, extendRestricted valid h.val))))) g ^^
        conditionedFoldedAnswer valid j₀
          (fun h => bits ((globalEncoding vE cE iE jE).code
            (.inr (.inl (c, extendRestricted valid h.val))))) (thirdQuery π f g μ)) := by
  rw [conditionedOccurrence, satisfied_mapEquation]
  let tableA : HalfCube i₀ → Bool :=
    fun h => bits ((globalEncoding vE cE iE jE).code (.inl (v, h.val)))
  let tableB : HalfCube j₀ → Bool :=
    fun h => bits ((globalEncoding vE cE iE jE).code
      (.inr (.inl (c, extendRestricted valid h.val))))
  have hbits : bits ∘ localAddress vE cE iE jE v c valid i₀ j₀ =
      FoldedEquation.storedAssignment tableA tableB := by
    funext a
    cases a <;> rfl
  rw [hbits]
  exact FoldedEquation.conditionedEquation_satisfied valid π i₀ j₀ tableA tableB f g μ

end LocalEquations

theorem countP_cast_eq_sum {α : Type} (xs : List α) (p : α → Bool) :
    (xs.countP p : ℝ) = (xs.map (fun x => if p x then (1 : ℝ) else 0)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases hp : p x <;> simp [hp, ih, add_comm]

theorem countP_enumerate {Tape : Type} [Fintype Tape]
    (tape : Encoding Tape) (p : Tape → Bool) :
    (tape.enumerate.countP p : ℝ) = ∑ x, if p x then (1 : ℝ) else 0 := by
  rw [countP_cast_eq_sum]
  simp only [Encoding.enumerate, List.map_ofFn, List.sum_ofFn]
  exact Fintype.sum_equiv tape.code.symm _ _ (fun _ => rfl)

/-- Exact satisfaction fraction of the actual ordered equation list equals
the uniform random-tape expectation, even when equations or addresses repeat. -/
theorem occurrenceList_acceptance {Tape Name : Type} [Fintype Tape]
    (tape : Encoding Tape) (emit : Tape → Equation Name) (bits : Name → Bool) :
    ((occurrenceList tape emit).countP (fun e => satisfied e bits) : ℝ) /
        (occurrenceList tape emit).length =
      𝔼 x, if satisfied (emit x) bits then (1 : ℝ) else 0 := by
  rw [occurrenceList_length, Fintype.expect_eq_sum_div_card, tape.card_eq_size]
  congr 1
  simpa only [occurrenceList, List.countP_map, Function.comp_def] using
    countP_enumerate tape (fun x => satisfied (emit x) bits)

end UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceAddressArithmeticLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceAddressArithmetic

open scoped BigOperators
open Target SourceContexts SourceOccurrences

theorem variable_rank (F : Formula) (u : ℕ) (v : VariableContext F u) :
    ((variableEncoding F u).code v).val =
      ∑ t : Fin u, (v t).val * F.variables ^ t.val := rfl

theorem clause_rank (F : Formula) (u : ℕ) (c : ClauseContext F u) :
    ((clauseEncoding F u).code c).val =
      ∑ t : Fin u, (c t).val * F.clauses.length ^ t.val := rfl

theorem left_address (F : Formula) (u : ℕ) (v : VariableContext F u) (f : Cube (I u)) :
    ((proofEncoding F u).code (.inl (v, f))).val =
      (((iEncoding u).function Encoding.bool).code f).val +
        2 ^ (2 ^ u) * ((variableEncoding F u).code v).val := rfl

theorem right_address (F : Formula) (u : ℕ) (c : ClauseContext F u) (g : Cube (J u)) :
    ((proofEncoding F u).code (.inr (.inl (c, g)))).val =
      F.variables ^ u * 2 ^ (2 ^ u) +
        ((((jEncoding u).function Encoding.bool).code g).val +
          2 ^ (8 ^ u) * ((clauseEncoding F u).code c).val) := rfl

theorem dummy_address (F : Formula) (u : ℕ) :
    (dummyIndex F u).val =
      F.variables ^ u * 2 ^ (2 ^ u) + F.clauses.length ^ u * 2 ^ (8 ^ u) := by
  change F.variables ^ u * 2 ^ (2 ^ u) +
    (F.clauses.length ^ u * 2 ^ (8 ^ u) + 0) = _
  omega

end UniqueGamesTheorem.Foundations.Hastad.SourceAddressArithmetic

end

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceBounds

open Target
open UniqueGamesTheorem.Reduction

theorem formulaBits_length (F : Formula) :
    (Complexity.formulaBits F).length = F.variables + F.clauses.length + 2 +
      (Complexity.encodeWords (F.clauses.flatMap Complexity.clauseWords)).length := by
  simp only [Complexity.formulaBits, Complexity.formulaWords,
    Complexity.encodeWords_append, List.length_append, Complexity.encodeWords,
    Complexity.encodeWord_length, List.length_nil]
  omega

theorem formulaBits_length_ge_variables (F : Formula) :
    F.variables ≤ (Complexity.formulaBits F).length := by
  rw [formulaBits_length]
  omega

theorem formulaBits_length_ge_clauses (F : Formula) :
    F.clauses.length ≤ (Complexity.formulaBits F).length := by
  rw [formulaBits_length]
  omega

theorem formulaBits_length_ge_two (F : Formula) :
    2 ≤ (Complexity.formulaBits F).length := by
  rw [formulaBits_length]
  omega

theorem one_le_input_power (F : Formula) (u : ℕ) :
    1 ≤ (Complexity.formulaBits F).length ^ u := by
  apply Nat.one_le_pow
  have h := formulaBits_length_ge_two F
  omega

theorem bitCountFormula_le_input (F : Formula) (u : ℕ) :
    bitCountFormula F.variables F.clauses.length u ≤
      bitCoefficient u * (Complexity.formulaBits F).length ^ u := by
  have hn := Nat.pow_le_pow_left (formulaBits_length_ge_variables F) u
  have hm := Nat.pow_le_pow_left (formulaBits_length_ge_clauses F) u
  have hpos := one_le_input_power F u
  unfold bitCountFormula bitCoefficient
  calc
    _ ≤ (Complexity.formulaBits F).length ^ u * 2 ^ (2 ^ u) +
        (Complexity.formulaBits F).length ^ u * 2 ^ (8 ^ u) +
        (Complexity.formulaBits F).length ^ u :=
      Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_right _ hn) (Nat.mul_le_mul_right _ hm)) hpos
    _ = _ := by ring

open SourceOccurrences SourceContexts

/-- The executable radix enumeration has the same fixed size. -/
theorem testTapeEncoding_size (u D : ℕ) :
    (SourceOccurrences.testTapeEncoding u D).size =
      2 ^ (2 ^ u) * (D ^ (8 ^ u) * 2 ^ (8 ^ u)) := rfl

/-- Bound on the actual variable count, including padded addresses and dummy. -/
theorem nBits_le_input (F : Formula) (u : ℕ) :
    nBits F u ≤ bitCoefficient u * (Complexity.formulaBits F).length ^ u := by
  have h := bitCountFormula_le_input F u
  simpa only [nBits_eq, bitCountFormula, Nat.add_assoc] using h

end UniqueGamesTheorem.Foundations.Hastad.SourceBounds

end

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.Encoding

variable {α β γ : Type}

theorem prod_decode_pair (a : Encoding α) (b : Encoding β)
    (i : Fin a.size) (j : Fin b.size) :
    (a.prod b).code.symm (finProdFinEquiv (i, j)) =
      (a.code.symm i, b.code.symm j) := by
  change (a.code.symm (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1,
    b.code.symm (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2) = _
  rw [Equiv.symm_apply_apply]

theorem prod_decode_mk (a : Encoding α) (b : Encoding β)
    (i : Fin a.size) (j : Fin b.size)
    (h : i.val * b.size + j.val < a.size * b.size) :
    (a.prod b).code.symm ⟨i.val * b.size + j.val, h⟩ =
      (a.code.symm i, b.code.symm j) := by
  have he : (⟨i.val * b.size + j.val, h⟩ : Fin (a.size * b.size)) =
      finProdFinEquiv (i, j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  change (a.code.symm (finProdFinEquiv.symm (⟨i.val * b.size + j.val, h⟩ :
    Fin (a.size * b.size))).1,
    b.code.symm (finProdFinEquiv.symm (⟨i.val * b.size + j.val, h⟩ :
    Fin (a.size * b.size))).2) = _
  rw [he]
  exact prod_decode_pair a b i j

/-- Increasing product rank enumerates the first factor outside and the
second factor inside, including when either factor is empty. -/
theorem enumerate_prod (a : Encoding α) (b : Encoding β) :
    (a.prod b).enumerate =
      a.enumerate.flatMap (fun x => b.enumerate.map (fun y => (x, y))) := by
  change List.ofFn (fun q : Fin (a.size * b.size) =>
    (a.code.symm (finProdFinEquiv.symm q).1,
     b.code.symm (finProdFinEquiv.symm q).2)) = _
  rw [List.ofFn_mul]
  simp only [enumerate, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  exact prod_decode_mk a b i j _

end UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.Encoding

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceFieldArrayLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceClauseLookup

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition SourceMachine

/-- Ten binary stacks and fixed finite control. Every loop scans one actual bit
or tests one actual counter bit; there is no arithmetic oracle in the state. -/
def program : Label → TM2.Stmt (fun _ : Tape => Bool) Label (Unit × Option Bool)
  | .copyOut => Reduction.MachineTransfer.loopAt .formula .scratch id false
      .copyOut (some .copyBack)
  | .copyBack => MachineCopy.forkLoop .scratch .formula .work false
      .copyBack (some .headerFirst)
  | .headerFirst => MachineLookup.discard .work .headerFirst .headerSecond
  | .headerSecond => MachineLookup.discard .work .headerSecond .guard
  | .guard => MachineUnaryCounter.guard .index (skipLabel 0) (readStart 0)
  | .skip slot => MachineLookup.discard .work (.skip slot) (skipLabel (slot.val + 1))
  | .read slot =>
      if slot.1.val < 6 then
        if slot.2 then
          fieldLoop .work (fieldDestination slot.1.val) (.read (slot.1, true))
            (some (readStart (slot.1.val + 1)))
        else fieldStart (fieldDestination slot.1.val) (.read (slot.1, true))
      else SourceFieldArray.finish .work none

theorem atSkip (r : Nat) (hr : r < 6) :
    program (skipLabel r) = MachineLookup.discard .work (skipLabel r) (skipLabel (r + 1)) := by
  simp [skipLabel, hr, program]

theorem atReadStart (r : Nat) (hr : r < 6) :
    program (readStart r) = fieldStart (fieldDestination r) (readLoop r) := by
  simp [program, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

theorem atReadLoop (r : Nat) (hr : r < 6) :
    program (readLoop r) = fieldLoop .work (fieldDestination r) (readLoop r)
      (some (readStart (r + 1))) := by
  simp [program, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

theorem atReadDone : program (readStart 6) = SourceFieldArray.finish .work none := by
  simp [program, readStart, SourceFieldArray.boundedIndex]

theorem scanTapes_other (base : Tape → List Bool) (i : Nat)
    (indexSuffix input : List Bool) (p : Tape) (hi : p ≠ .index) (hw : p ≠ .work) :
    scanTapes base i indexSuffix input p = base p := by
  simp [scanTapes, MachineUnaryCounter.counterTapes, hi, hw]

theorem update_scanTapes_work (base : Tape → List Bool) (i : Nat)
    (indexSuffix input replacement : List Bool) :
    Function.update (scanTapes base i indexSuffix input) .work replacement =
      scanTapes base i indexSuffix replacement := by
  funext p
  cases p <;> simp [scanTapes, MachineUnaryCounter.counterTapes]

theorem fieldDestination_eq (j : Fin 6) : fieldDestination j.val = .field j := by
  unfold fieldDestination
  congr 1
  apply Fin.ext
  exact Nat.min_eq_left (by omega)

theorem fieldDestination_injective_below (r s : Nat) (hr : r < 6) (hs : s < 6)
    (he : fieldDestination r = fieldDestination s) : r = s := by
  have hv := congrArg (fun t : Tape => match t with | .field j => j.val | _ => 6) he
  simpa [fieldDestination, Nat.min_eq_left (show r ≤ 5 by omega),
    Nat.min_eq_left (show s ≤ 5 by omega)] using hv

theorem lookupSteps_le_input (F : Target.Formula) (prior : List (Target.Clause F.variables))
    (clause : Target.Clause F.variables) (after : List (Target.Clause F.variables))
    (hsplit : F.clauses = prior ++ clause :: after) :
    lookupSteps F prior clause ≤ 4 * (formulaBits F).length + 10 := by
  have hlength : (formulaBits F).length = F.variables + F.clauses.length + 2 +
      (encodeWords (prior.flatMap clauseWords)).length +
      (encodeWords (clauseWords clause)).length +
      (encodeWords (after.flatMap clauseWords)).length := by
    simp only [formulaBits, formulaWords, encodeWords_append, List.length_append,
      encodeWords, encodeWord_length, List.length_nil]
    rw [hsplit]
    simp only [List.flatMap_append, List.flatMap_cons, encodeWords_append, List.length_append]
    omega
  have hp : prior.length ≤ F.clauses.length := by
    rw [hsplit, List.length_append, List.length_cons]
    omega
  unfold lookupSteps scanSteps
  omega

end UniqueGamesTheorem.Foundations.Hastad.SourceClauseLookup

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceContextLoad
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
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
open MachineComposition

variable {u : Nat} {Extra : Type}

variable [DecidableEq Extra]

theorem fill_update (j : Fin u) (base : Tape u Extra → List Bool)
    (localTapes : SourceClauseLookup.Tape → List Bool) (p : SourceClauseLookup.Tape)
    (value : List Bool) :
    fill j base (Function.update localTapes p value) =
      Function.update (fill j base localTapes) (place j p) value := by
  funext k
  cases k <;> cases p <;> simp [fill, place, Function.update_apply]
  all_goals split <;> simp_all

def placedConfiguration (j : Fin u) (base : Tape u Extra → List Bool)
    (c : TM2.Cfg (fun _ : SourceClauseLookup.Tape => Bool)
      SourceClauseLookup.Label (Unit × Option Bool)) :
    TM2.Cfg (fun _ : Tape u Extra => Bool) (Label u) (Unit × Option Bool) :=
  ⟨placedLabel j c.l, c.var, fill j base c.stk⟩

def placedStatement (j : Fin u) :
    TM2.Stmt (fun _ : SourceClauseLookup.Tape => Bool)
      SourceClauseLookup.Label (Unit × Option Bool) →
    TM2.Stmt (fun _ : Tape u Extra => Bool) (Label u) (Unit × Option Bool)
  | .push k f next => .push (place j k) f (placedStatement j next)
  | .peek k f next => .peek (place j k) f (placedStatement j next)
  | .pop k f next => .pop (place j k) f (placedStatement j next)
  | .load f next => .load f (placedStatement j next)
  | .branch f yes no => .branch f (placedStatement j yes) (placedStatement j no)
  | .goto f => .goto (fun state => .lookup j (f state))
  | .halt => .goto (fun _ => .clearWork j)

theorem placed_stepAux (j : Fin u) (base : Tape u Extra → List Bool)
    (q : TM2.Stmt (fun _ : SourceClauseLookup.Tape => Bool)
      SourceClauseLookup.Label (Unit × Option Bool))
    (state : Unit × Option Bool) (localTapes : SourceClauseLookup.Tape → List Bool) :
    TM2.stepAux (placedStatement j q) state (fill j base localTapes) =
      placedConfiguration j base (TM2.stepAux q state localTapes) := by
  induction q generalizing state localTapes with
  | push k f next ih =>
    simp only [placedStatement, TM2.stepAux, fill_place]
    rw [← fill_update]
    exact ih state _
  | peek k f next ih =>
    simpa only [placedStatement, TM2.stepAux, fill_place] using ih (f state _) localTapes
  | pop k f next ih =>
    simp only [placedStatement, TM2.stepAux, fill_place]
    rw [← fill_update]
    exact ih (f state _) _
  | load f next ih => simpa only [placedStatement, TM2.stepAux] using ih (f state) localTapes
  | branch f yes no ihYes ihNo =>
    cases h : f state
    · simpa only [placedStatement, TM2.stepAux, h, Bool.cond_false] using ihNo state localTapes
    · simpa only [placedStatement, TM2.stepAux, h, Bool.cond_true] using ihYes state localTapes
  | goto f => rfl
  | halt => rfl

def program : Label u → TM2.Stmt (fun _ : Tape u Extra => Bool)
    (Label u) (Unit × Option Bool)
  | .copyOut j => Reduction.MachineTransfer.loopAt (.current j) .copyScratch id false
      (.copyOut j) (some (.copyBack j))
  | .copyBack j => MachineCopy.forkLoop .copyScratch (.current j) .index false
      (.copyBack j) (some (.lookup j .copyOut))
  | .lookup j l => placedStatement j (SourceClauseLookup.program l)
  | .clearWork j => MachineDrain.drain .work (.clearWork j) (some (.clearIndex j))
  | .clearIndex j => MachineDrain.drain .index (.clearIndex j) (some (nextLabel j))
  | .done => .halt

theorem placed_step (j : Fin u) (base : Tape u Extra → List Bool)
    (a b : TM2.Cfg (fun _ : SourceClauseLookup.Tape => Bool)
      SourceClauseLookup.Label (Unit × Option Bool))
    (h : TM2.step SourceClauseLookup.program a = some b) :
    TM2.step program (placedConfiguration j base a) =
      some (placedConfiguration j base b) := by
  cases a with
  | mk l state localTapes =>
    cases l with
    | none => contradiction
    | some l =>
      change some (TM2.stepAux (SourceClauseLookup.program l) state localTapes) = some b at h
      cases Option.some.inj h
      change some (TM2.stepAux (placedStatement j (SourceClauseLookup.program l))
        state (fill j base localTapes)) = _
      rw [placed_stepAux]

def copiedTapes (j : Fin u) (base : Tape u Extra → List Bool) : Tape u Extra → List Bool :=
  Function.update base .index (base (.current j))

omit [DecidableEq Extra] in
theorem coordinateOutput_other_field {n : Nat} (j k : Fin u) (s : Fin 6)
    (clause : Target.Clause n) (base : Tape u Extra → List Bool) (h : k ≠ j) :
    coordinateOutput j clause base (.field k s) = base (.field k s) := by
  simp [coordinateOutput, h]

theorem suffix_length_le_input (F : Target.Formula) (i : Nat) :
    (encodeWords ((F.clauses.drop i).flatMap clauseWords)).length ≤ (formulaBits F).length := by
  have hs := List.take_append_drop i F.clauses
  have he : formulaBits F = encodeWords [F.variables, F.clauses.length] ++
      encodeWords ((F.clauses.take i).flatMap clauseWords) ++
      encodeWords ((F.clauses.drop i).flatMap clauseWords) := by
    conv_lhs => rw [formulaBits, formulaWords, ← hs]
    simp only [List.flatMap_append, encodeWords_append, List.append_assoc]
    rw [hs]
  rw [he, List.length_append, List.length_append]
  omega

theorem clauses_length_le_input (F : Target.Formula) :
    F.clauses.length ≤ (formulaBits F).length := by
  simp only [formulaBits, encodeWords_length, formulaWords_length]
  omega

def polarityField (j : Fin u) (s : Fin 3) : Tape u Extra := .field j (polaritySlot s)

theorem clauseWords_variable {n : Nat} (clause : Target.Clause n) (s : Fin 3) :
    (clauseWords clause)[(variableSlot s).val]'(by simp) = clause[s.val].variableIndex.val := by
  obtain ⟨s, hs⟩ := s
  have h : s = 0 ∨ s = 1 ∨ s = 2 := by omega
  rcases h with rfl | rfl | rfl <;> rfl

theorem clauseWords_polarity {n : Nat} (clause : Target.Clause n) (s : Fin 3) :
    (clauseWords clause)[(polaritySlot s).val]'(by simp) =
      if clause[s.val].positive then 1 else 0 := by
  obtain ⟨s, hs⟩ := s
  have h : s = 0 ∨ s = 1 ∨ s = 2 := by omega
  rcases h with rfl | rfl | rfl <;> rfl

end UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceContextClear
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceContextClear

open Turing Complexity MachineComposition

variable {u : Nat} {Extra : Type}

variable [DecidableEq Extra]

theorem variables_add_two_le_input (F : Target.Formula) :
    F.variables + 2 ≤ (formulaBits F).length := by
  simp only [formulaBits, formulaWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

end UniqueGamesTheorem.Foundations.Hastad.SourceContextClear

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceHonestLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.slotFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceLocalEquation

open Target SourceContexts SourceOccurrences SourceLocalSignature
open UniqueGamesTheorem.Reduction.CloneGap
open UniqueGamesTheorem.Reduction.FiniteNoise

def signatureEncoding (u : ℕ) : Encoding (Signature u) :=
  let position := (Encoding.fin u).prod slotEncoding
  let fields := (position.function Encoding.bool).prod
    ((position.function (position.function Encoding.bool)).prod (slotContextEncoding u))
  ⟨fields.size, (signatureEquiv u).trans fields.code⟩

theorem mapEquation_comp {A B C : Type} (g : B → C) (f : A → B) (e : Equation A) :
    mapEquation g (mapEquation f e) = mapEquation (g ∘ f) e := rfl

end UniqueGamesTheorem.Foundations.Hastad.SourceLocalEquation

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

abbrev Layout := MachineHorner.Layout 2

theorem horner_value (coefficient rank offset : Nat) :
    MachineHorner.value rank (digits coefficient offset) 2 = coefficient * rank + offset := by
  simp [MachineHorner.value, digits, Nat.mul_comm]

def operandLength (rank offset : Nat) : Nat :=
  (encodeWord rank).length + (encodeWord offset).length

theorem timePolynomial_eval (coefficient n : Nat) :
    (timePolynomial coefficient).eval n =
      (MachineHorner.timePolynomial 2).eval (n + coefficient) + coefficient + 2 := by
  simp [timePolynomial, Polynomial.eval_comp, Nat.add_assoc]

theorem steps_le_timePolynomial (coefficient rank offset : Nat) :
    steps coefficient rank offset ≤ (timePolynomial coefficient).eval (operandLength rank offset) := by
  have hr : rank ≤ operandLength rank offset + coefficient := by
    simp only [operandLength, encodeWord_length]
    omega
  have hd : ∀ i, i < 2 → digits coefficient offset i ≤ operandLength rank offset + coefficient := by
    intro i _
    simp only [digits, operandLength, encodeWord_length]
    split <;> omega
  have h := MachineHorner.steps_le_timePolynomial rank (digits coefficient offset) 2
    (operandLength rank offset + coefficient) hr hd
  rw [timePolynomial_eval]
  unfold steps
  omega

variable {K Λ σ : Type} [DecidableEq K]

def statement (slots : Layout ↪ K) (coefficient : Nat) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .seed => pushWord (slots (.inr 0)) (encodeWord coefficient).reverse
      (.goto fun _ => labels (.horner .start))
  | .horner label => MachineHorner.statement slots (fun l => labels (.horner l))
      (some (labels .clear)) label
  | .clear => MachineHorner.drainLoop (slots (.inr 0)) (labels .clear) exit

def program (slots : Layout ↪ K) (coefficient : Nat) :
    Label → TM2.Stmt (fun _ : K => Bool) Label (MachineHorner.State σ) :=
  statement slots coefficient id none

def coefficientTapes (slots : Layout ↪ K) (base : K → List Bool) (coefficient : Nat) : K → List Bool :=
  Function.update base (slots (.inr 0)) (encodeWord coefficient)

/-- Exact affine execution, including coefficient initialization and cleanup. -/
theorem affineTrace (slots : Layout ↪ K) (coefficient : Nat) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots coefficient labels exit label)
    (base : K → List Bool) (rank offset : Nat)
    (rankWord : base (slots (.inl 0)) = encodeWord rank)
    (offsetWord : base (slots (.inr 1)) = encodeWord offset)
    (coefficientEmpty : base (slots (.inr 0)) = [])
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps coefficient rank offset]
      (some ⟨some (labels .seed), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none),
        MachineHorner.resultTapes slots base (coefficient * rank + offset)⟩ := by
  have hc (i : Fin 6) : slots (.inl i) ≠ slots (.inr 0) := slots.injective.ne (by simp)
  have hd : slots (.inr 1) ≠ slots (.inr 0) := slots.injective.ne (by decide)
  let seeded := coefficientTapes slots base coefficient
  have hseed : (MachineComposition.advance (TM2.step p))^[1]
      (some ⟨some (labels .seed), ((ambient, ()), register), base⟩) =
      some ⟨some (labels (.horner .start)), ((ambient, ()), register), seeded⟩ := by
    change some (TM2.stepAux (p (labels .seed)) ((ambient, ()), register) base) = _
    rw [atLabels .seed]
    simp only [statement, stepAux_pushWord, List.reverse_reverse, TM2.stepAux,
      coefficientEmpty, List.append_nil, seeded, coefficientTapes]
  have hradix : seeded (slots (.inl 0)) = encodeWord rank := by
    simp [seeded, coefficientTapes, hc, rankWord]
  have hdigits : ∀ i : Fin 2, seeded (slots (.inr i)) = encodeWord (digits coefficient offset i.val) := by
    intro i
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · simp [seeded, coefficientTapes, digits]
    · simp [seeded, coefficientTapes, digits, hd, offsetWord]
  have hclean : MachineHorner.Clean slots seeded := {
    accA := by simpa only [seeded, coefficientTapes, Function.update_of_ne (hc 1)] using clean.accA
    accB := by simpa only [seeded, coefficientTapes, Function.update_of_ne (hc 2)] using clean.accB
    counter := by simpa only [seeded, coefficientTapes, Function.update_of_ne (hc 4)] using clean.counter
    scratch := by simpa only [seeded, coefficientTapes, Function.update_of_ne (hc 5)] using clean.scratch
  }
  have hhorner := MachineHorner.hornerTrace slots (fun l => labels (.horner l))
    (some (labels .clear)) p (fun l => atLabels (.horner l)) seeded rank
    (digits coefficient offset) hradix hdigits hclean ambient register
  rw [horner_value] at hhorner
  let after := MachineHorner.resultTapes slots seeded (coefficient * rank + offset)
  have hafter : after (slots (.inr 0)) = encodeWord coefficient := by
    simp [after, MachineHorner.resultTapes, Ne.symm (hc 3), seeded, coefficientTapes]
  have hstart : Function.update after (slots (.inr 0)) (encodeWord coefficient ++ []) = after := by
    rw [List.append_nil, ← hafter, Function.update_eq_self]
  have hfinish : Function.update after (slots (.inr 0)) [] =
      MachineHorner.resultTapes slots base (coefficient * rank + offset) := by
    funext k
    by_cases ho : k = slots (.inl 3)
    · subst k
      simp [after, MachineHorner.resultTapes, seeded, coefficientTapes, hc 3]
    · by_cases hk : k = slots (.inr 0)
      · subst k
        simp [MachineHorner.resultTapes, Ne.symm (hc 3), coefficientEmpty]
      · simp [after, MachineHorner.resultTapes, seeded, coefficientTapes, ho, hk]
  have hclear := MachineHorner.drainTrace (slots (.inr 0)) (labels .clear) exit p
    (atLabels .clear) after coefficient [] ambient none
  rw [hstart, hfinish] at hclear
  rw [show steps coefficient rank offset = (coefficient + 1) +
      (MachineHorner.steps rank (digits coefficient offset) 2 + 1) by unfold steps; omega,
    Function.iterate_add_apply, Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step p))^[coefficient + 1]
    ((MachineComposition.advance (TM2.step p))^[MachineHorner.steps rank (digits coefficient offset) 2]
      ((MachineComposition.advance (TM2.step p))^[1]
        (some ⟨some (labels .seed), ((ambient, ()), register), base⟩))) = _
  rw [hseed, hhorner]
  exact hclear

def affineInPolynomialTime (slots : Layout ↪ K) (coefficient : Nat) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots coefficient labels exit label)
    (base : K → List Bool) (rank offset : Nat)
    (rankWord : base (slots (.inl 0)) = encodeWord rank)
    (offsetWord : base (slots (.inr 1)) = encodeWord offset)
    (coefficientEmpty : base (slots (.inr 0)) = [])
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .seed), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (coefficient * rank + offset)⟩)
      ((timePolynomial coefficient).eval (operandLength rank offset)) where
  steps := steps coefficient rank offset
  evals_in_steps := affineTrace slots coefficient labels exit p atLabels base rank offset
    rankWord offsetWord coefficientEmpty clean ambient register
  steps_le_m := steps_le_timePolynomial coefficient rank offset

end UniqueGamesTheorem.Foundations.Hastad.SourceBasePhase

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceDescriptorEmissionLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.slotFintype
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

def rhsBit (e : Equation Descriptor) : Nat := if e.rhs then 1 else 0

def steps (values : Fin 3 → Nat) (e : Equation Descriptor) : Nat :=
  2 * (values e.first.1 + values e.second.1 + values e.third.1) + 16

variable {K Λ σ : Type} [DecidableEq K]

def statement (sources : Fin 3 → K) (destination scratch : K)
    (e : Equation Descriptor) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .seed => pushWord destination (encodeWord (rhsBit e)).reverse
      (.goto fun _ => labels .thirdDrain)
  | .thirdDrain => Reduction.MachineTransfer.loopAt (sources e.third.1) scratch id false
      (labels .thirdDrain) (some (labels .thirdFork))
  | .thirdFork => MachineCopy.forkLoop scratch (sources e.third.1) destination false
      (labels .thirdFork) (some (labels .thirdEmit))
  | .thirdEmit => MachineRegisterEmit.emitStatement destination e.third.2
      (some (labels .secondDrain))
  | .secondDrain => Reduction.MachineTransfer.loopAt (sources e.second.1) scratch id false
      (labels .secondDrain) (some (labels .secondFork))
  | .secondFork => MachineCopy.forkLoop scratch (sources e.second.1) destination false
      (labels .secondFork) (some (labels .secondEmit))
  | .secondEmit => MachineRegisterEmit.emitStatement destination e.second.2
      (some (labels .firstDrain))
  | .firstDrain => Reduction.MachineTransfer.loopAt (sources e.first.1) scratch id false
      (labels .firstDrain) (some (labels .firstFork))
  | .firstFork => MachineCopy.forkLoop scratch (sources e.first.1) destination false
      (labels .firstFork) (some (labels .firstEmit))
  | .firstEmit => MachineRegisterEmit.emitStatement destination e.first.2 exit

end UniqueGamesTheorem.Foundations.Hastad.SourceEquationEmit

namespace UniqueGamesTheorem.Foundations.Hastad.SourceRankPhase

open Turing Complexity
open scoped BigOperators
open Target SourceContexts SourceOccurrences SourceAddressArithmetic

variable {K Λ σ : Type} {width : Nat}

variable [DecidableEq K]

omit [DecidableEq K] in
theorem clean_reverseSlots (slots : MachineHorner.Layout width ↪ K) (base : K → List Bool)
    (clean : MachineHorner.Clean slots base) : MachineHorner.Clean (reverseSlots slots) base where
  accA := by simpa only [reverseSlots_control] using clean.accA
  accB := by simpa only [reverseSlots_control] using clean.accB
  counter := by simpa only [reverseSlots_control] using clean.counter
  scratch := by simpa only [reverseSlots_control] using clean.scratch

def statement (slots : MachineHorner.Layout width ↪ K)
    (labels : MachineHorner.Label width → Λ) (exit : Option Λ) :
    MachineHorner.Label width → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ) :=
  MachineHorner.statement (reverseSlots slots) labels exit

def program (slots : MachineHorner.Layout width ↪ K) :
    MachineHorner.Label width → TM2.Stmt (fun _ : K => Bool)
      (MachineHorner.Label width) (MachineHorner.State σ) :=
  statement slots id none

/-- Exact execution using existing digit fields; only the destination changes. -/
theorem rankTrace (slots : MachineHorner.Layout width ↪ K)
    (labels : MachineHorner.Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix : Nat) (digits : Fin width → Nat)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigits : ∀ i, base (slots (.inr i)) = encodeWord (digits i))
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[
      MachineHorner.steps radix (reverseDigits digits) width]
      (some ⟨some (labels .start), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (rank radix digits)⟩ := by
  have h := MachineHorner.hornerTrace (reverseSlots slots) labels exit p atLabels base radix
    (reverseDigits digits) operandRadix
    (fun i => by simpa only [reverseSlots_digit, reverseDigits_apply] using operandDigits i.rev)
    (clean_reverseSlots slots base clean) ambient register
  rw [horner_reverse_eq_rank] at h
  simpa only [MachineHorner.resultTapes, reverseSlots_control] using h

def rankInPolynomialTime (slots : MachineHorner.Layout width ↪ K)
    (labels : MachineHorner.Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix : Nat) (digits : Fin width → Nat)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigits : ∀ i, base (slots (.inr i)) = encodeWord (digits i))
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool)
    (magnitude : Nat) (radixBound : radix ≤ magnitude) (digitBound : ∀ i, digits i ≤ magnitude) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .start), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (rank radix digits)⟩)
      ((MachineHorner.timePolynomial width).eval magnitude) where
  steps := MachineHorner.steps radix (reverseDigits digits) width
  evals_in_steps := rankTrace slots labels exit p atLabels base radix digits operandRadix
    operandDigits clean ambient register
  steps_le_m := MachineHorner.steps_le_timePolynomial radix (reverseDigits digits) width magnitude
    radixBound (fun i hi => by simpa only [reverseDigits, dite_eq_left hi] using digitBound (Fin.rev ⟨i, hi⟩))

end UniqueGamesTheorem.Foundations.Hastad.SourceRankPhase

namespace UniqueGamesTheorem.Foundations.Hastad.SourceSignLoad

open Turing
open SourceLocalSignature
open UniqueGamesTheorem.Foundations.Complexity

/-- An explicit computable enumeration, without an arbitrary finite-type
equivalence. Slots occur first, second, third within each clause coordinate. -/
def positions (u : ℕ) : List (Position u) :=
  ((SourceOccurrences.Encoding.fin u).prod SourceOccurrences.slotEncoding).enumerate

theorem mem_positions {u : ℕ} (p : Position u) : p ∈ positions u :=
  SourceOccurrences.Encoding.mem_enumerate _ p

/-- The mathematical result of the individual finite sign-register writes. -/
def fillSigns {u : ℕ} (values initial : Position u → Bool)
    (cells : List (Position u)) : Position u → Bool :=
  cells.foldl (fun signs p => Function.update signs p (values p)) initial

theorem fillSigns_apply {u : ℕ} (values initial : Position u → Bool)
    (cells : List (Position u)) (p : Position u) :
    fillSigns values initial cells p = if p ∈ cells then values p else initial p := by
  induction cells generalizing initial with
  | nil => simp [fillSigns]
  | cons q cells ih =>
    change fillSigns values (Function.update initial q (values q)) cells p = _
    rw [ih]
    by_cases hp : p ∈ cells
    · simp [hp]
    · by_cases hpq : p = q
      · subst q; simp [hp]
      · simp [hp, hpq]

theorem fillSigns_positions {u : ℕ} (values initial : Position u → Bool) :
    fillSigns values initial (positions u) = values := by
  funext p
  rw [fillSigns_apply]
  simp only [mem_positions, ↓reduceIte]

variable {u : ℕ} {K Λ τ : Type} [DecidableEq K]

/-- Each statement reads only the head of one supplied polarity field. The
other signature fields and the entire ambient-register component are copied. -/
def peekChain (field : Position u → K) (exit : Option Λ) :
    List (Position u) → TM2.Stmt (Alphabet (K := K)) Λ (State u τ)
  | [] => finish exit
  | p :: rest =>
    .peek (field p) (fun state head =>
      ({state.1 with signs := Function.update state.1.signs p (head.getD false)}, state.2))
      (peekChain field exit rest)

def statement (field : Position u → K) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State u τ) :=
  peekChain field exit (positions u)

theorem stepAux_peekChain (field : Position u → K) (exit : Option Λ)
    (cells : List (Position u)) (initial : Signature u) (ambient : τ)
    (tapes : K → List Bool) :
    TM2.stepAux (peekChain field exit cells) (initial, ambient) tapes =
      ⟨exit, ({initial with signs := fillSigns (readSigns field tapes) initial.signs cells},
        ambient), tapes⟩ := by
  induction cells generalizing initial with
  | nil => cases exit <;> rfl
  | cons p rest ih =>
    simp only [peekChain, TM2.stepAux]
    rw [ih]
    rfl

theorem stepAux_statement (field : Position u → K) (exit : Option Λ)
    (initial : Signature u) (ambient : τ) (tapes : K → List Bool) :
    TM2.stepAux (statement field exit) (initial, ambient) tapes =
      ⟨exit, ({initial with signs := readSigns field tapes}, ambient), tapes⟩ := by
  rw [statement, stepAux_peekChain, fillSigns_positions]

omit [DecidableEq K] in
theorem readSigns_of_unary (field : Position u → K) (tapes : K → List Bool)
    (values : Position u → Bool) (suffix : Position u → List Bool)
    (hfields : ∀ p, tapes (field p) = encodeWord (if values p then 1 else 0) ++ suffix p) :
    readSigns field tapes = values := by
  funext p
  rw [readSigns, hfields]
  cases values p <;> rfl

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
open MachineComposition SourceMachine

variable {u : Nat} {Extra : Type}

def headerDestination (r : Nat) : Tape u Extra := if r = 0 then variableHeader else clauseHeader

def program : Label u → TM2.Stmt (fun _ : Tape u Extra => Bool) (Label u) (Unit × Option Bool)
  | .inputCopyOut => Reduction.MachineTransfer.loopAt .formula .scratch id false
      .inputCopyOut (some .inputCopyBack)
  | .inputCopyBack => MachineCopy.forkLoop .scratch .formula .work false
      .inputCopyBack (some (readStart 0))
  | .read slot => if slot.1.val < 2 then
      if slot.2 then fieldLoop .work (headerDestination slot.1.val) (.read (slot.1, true))
        (some (readStart (slot.1.val + 1)))
      else fieldStart (headerDestination slot.1.val) (.read (slot.1, true))
    else SourceFieldArray.finish .work (some .clearWork)
  | .clearWork => MachineDrain.drain .work .clearWork (some (labelAt 0))
  | .seed j => .push (.current j) (fun _ => false) (.goto fun _ => .digitCopyOut j)
  | .digitCopyOut j => Reduction.MachineTransfer.loopAt clauseHeader .copyScratch id false
      (.digitCopyOut j) (some (.digitCopyBack j))
  | .digitCopyBack j => MachineCopy.forkLoop .copyScratch clauseHeader (.remaining j) false
      (.digitCopyBack j) (some (.trim j))
  | .trim j => .pop (.remaining j) (fun state _ => state) (.goto fun _ => labelAt (j.val + 1))
  | .done => .halt

theorem atReadStart (r : Nat) (hr : r < 2) :
    program (u := u) (Extra := Extra) (readStart r) =
      fieldStart (headerDestination r) (readLoop r) := by
  simp [program, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

theorem atReadLoop (r : Nat) (hr : r < 2) :
    program (u := u) (Extra := Extra) (readLoop r) = fieldLoop .work (headerDestination r)
      (readLoop r) (some (readStart (r + 1))) := by
  simp [program, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

theorem atReadDone : program (u := u) (Extra := Extra) (readStart 2) =
    SourceFieldArray.finish .work (some .clearWork) := by
  simp [program, readStart]

variable [DecidableEq Extra]

def copiedInput (base : Tape u Extra → List Bool) : Tape u Extra → List Bool :=
  Function.update base .work (base .formula)

def digitInTime (j : Fin u) (m : Nat) (hm : 0 < m) (base : Tape u Extra → List Bool)
    (hcount : base clauseHeader = encodeWord m)
    (hcurrent : base (.current j) = []) (hremaining : base (.remaining j) = [])
    (hscratch : base .copyScratch = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.seed j), ((), none), base⟩
      (some ⟨some (labelAt (j.val + 1)), ((), none), digitOutput j m base⟩)
      (2 * m + 6) := by
  let seeded := Function.update base (.current j) (encodeWord 0)
  have seedRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.seed j), ((), none), base⟩
      (some ⟨some (.digitCopyOut j), ((), none), seeded⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
    change TM2.step program ⟨some (.seed j), ((), none), base⟩ = _
    simp [program, TM2.step, TM2.stepAux, seeded, hcurrent, encodeWord]
  have copying := MachineCopy.copyInTime clauseHeader (.remaining j) .copyScratch
    (by simp [clauseHeader]) (by simp [clauseHeader]) (by simp)
    false (.digitCopyOut j) (.digitCopyBack j) (some (.trim j)) program rfl rfl seeded
    (by simpa [seeded] using hscratch) () none
  let copied := Function.update seeded (.remaining j) (encodeWord m)
  have he : Function.update seeded (.remaining j)
      (seeded clauseHeader ++ seeded (.remaining j)) = copied := by
    have hcount' : base (.extra (.inl .clauseCount)) = encodeWord m := hcount
    simp [copied, seeded, clauseHeader, hremaining, hcount']
  rw [he] at copying
  have trimRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.trim j), ((), none), copied⟩
      (some ⟨some (labelAt (j.val + 1)), ((), none), digitOutput j m base⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
    change TM2.step program ⟨some (.trim j), ((), none), copied⟩ = _
    have hn : m = (m - 1) + 1 := by omega
    have htail : (encodeWord m).tail = encodeWord (m - 1) := by
      conv_lhs => rw [hn]
      simp [encodeWord, List.replicate_succ]
    simp [program, TM2.step, TM2.stepAux, copied, seeded, digitOutput, htail]
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ seedRun copying) trimRun
  refine { steps := joined.steps, evals_in_steps := joined.evals_in_steps, steps_le_m := ?_ }
  apply Nat.le_trans joined.steps_le_m
  have hs : seeded clauseHeader = encodeWord m := by simpa [seeded, clauseHeader] using hcount
  rw [hs, encodeWord_length]
  omega

def prefixInTime (m : Nat) (hm : 0 < m) (base : Tape u Extra → List Bool)
    (hcount : base clauseHeader = encodeWord m)
    (hcurrent : ∀ j, base (.current j) = []) (hremaining : ∀ j, base (.remaining j) = [])
    (hscratch : base .copyScratch = []) (r : Nat) (hr : r ≤ u) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((), none), base⟩
      (some ⟨some (labelAt r), ((), none), stageTapes m base r⟩)
      (r * (2 * m + 6)) := by
  induction r with
  | zero => exact { steps := 0, evals_in_steps := rfl, steps_le_m := by omega }
  | succ r ih =>
    have hru : r < u := by omega
    let j : Fin u := ⟨r, hru⟩
    let before := stageTapes m base r
    have one := digitInTime j m hm before
      (by dsimp only [before]; rw [stageTapes_frame _ _ _ _ (by simp [clauseHeader]) (by simp [clauseHeader])]; exact hcount)
      (by simp [before, stageTapes_current, j, hcurrent])
      (by simp [before, stageTapes_remaining, j, hremaining])
      (by dsimp only [before]; rw [stageTapes_frame _ _ _ _ (by simp) (by simp)]; exact hscratch)
    have one' : StateTransition.EvalsToInTime (TM2.step program)
        ⟨some (labelAt r), ((), none), before⟩
        (some ⟨some (labelAt (r + 1)), ((), none), stageTapes m base (r + 1)⟩)
        (2 * m + 6) := by
      simpa only [labelAt, dite_eq_left hru, j, stageTapes, before] using one
    have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
      (ih (by omega)) one'
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm] using joined

def digitsInTime (m : Nat) (hm : 0 < m) (base : Tape u Extra → List Bool)
    (hcount : base clauseHeader = encodeWord m)
    (hcurrent : ∀ j, base (.current j) = []) (hremaining : ∀ j, base (.remaining j) = [])
    (hscratch : base .copyScratch = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((), none), base⟩
      (some ⟨none, ((), none), stageTapes m base u⟩)
      (u * (2 * m + 6) + 1) := by
  have initialRun := prefixInTime m hm base hcount hcurrent hremaining hscratch u (Nat.le_refl _)
  have doneRun : StateTransition.EvalsToInTime (TM2.step (program (Extra := Extra)))
      ⟨some (labelAt u), ((), none), stageTapes m base u⟩
      (some ⟨none, ((), none), stageTapes m base u⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
    change TM2.step program ⟨some (labelAt u), ((), none), stageTapes m base u⟩ = _
    simp only [labelAt, Nat.lt_irrefl, ↓reduceDIte]
    rfl
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ initialRun doneRun

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

namespace UniqueGamesTheorem.Foundations.Hastad.SourceContextPrepare

open Turing UniqueGamesTheorem.Foundations.Complexity
open Target PCP SourceContexts SourceOccurrences SourceLocalSignature

abbrev Arena (u : Nat) (Extra : Type) := SourceContextLoad.Tape u Extra

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

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceLoopOrder

open Complexity Complexity.MachineTupleOdometer
open Target SourceContexts SourceOccurrences
open UniqueGamesTheorem.Reduction

theorem inputBits_eq_header_records (input : SourceEncoding.Input) :
    SourceEncoding.inputBits input =
      encodeWords [input.variables, input.equations.length] ++
        input.equations.flatMap (fun e => encodeWords (SourceEncoding.equationWords e)) := by
  unfold SourceEncoding.inputBits SourceEncoding.inputWords
  rw [encodeWords_append]
  congr 1
  induction input.equations with
  | nil => rfl
  | cons e es ih =>
    simp only [List.flatMap_cons, encodeWords_append, ih]

end UniqueGamesTheorem.Foundations.Hastad.SourceLoopOrder

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_FinalParametersLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Integration.SourceParameters

/-- The actual finite game's repetition rate, with its answer cardinality
checked as an ordinary finite count. No repetition estimate is assumed. -/
theorem game_repetition_rate {Q₁ Q₂ A₁ A₂ : Type*}
    [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
    [Nonempty A₁] [Nonempty A₂] [DecidableEq Q₁] [DecidableEq Q₂]
    (G : UniqueGamesTheorem.Foundations.Games.Game Q₁ Q₂ A₁ A₂)
    {gap : ℚ} (hgap : 0 < gap) (hgap1 : gap ≤ 1)
    (hcards : Fintype.card A₁ * Fintype.card A₂ = 16)
    (hvalue : G.value ≤ 1 - (gap : ℝ)) (n : Nat) :
    (G.repetition n).value ≤ (rate gap : ℝ) ^ n := by
  have hg : (0 : ℝ) < gap := by exact_mod_cast hgap
  have halphabet : UniqueGamesTheorem.Foundations.Repetition.logTwo
      ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ 4 := by
    rw [← Nat.cast_mul, hcards]
    exact logTwo_sixteen.le
  have h := UniqueGamesTheorem.Foundations.Repetition.holenstein_repetition_value
    G n hvalue (by linarith) (by norm_num : (1 : ℝ) ≤ 4) halphabet
  simp only [sub_sub_cancel] at h
  exact h.trans (four_bit_rate_comparison hgap hgap1 n)

end UniqueGamesTheorem.Integration.SourceParameters

end

end OAI
end


