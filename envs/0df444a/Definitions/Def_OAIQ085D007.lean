-- Prove2me | Definitions.Def_OAIQ085D007
-- name    : OAIQ085D007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T15:57:06.168895+00:00
-- url     : https://prove2.me/theorems/cce17d6c-0e51-47a7-b1e4-bdabc1bdab79
-- title:
--   Definitions bundle OAIQ085D007 of the split of OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 629 declarations of OpenAI's Lean: 329 definitions, 7 inductive types or structures, 12 instances and 281 theorems. The definitions and types are `OAI.DFVSGames.Appendix.Derivatives.HybridIndex`, `OAI.DFVSGames.Appendix.Derivatives.hybridDerivative`, `OAI.DFVSGames.Appendix.Derivatives.hybridMomentSum`, `OAI.DFVSGames.Appendix.Derivatives.hybridProjector`, `OAI.DFVSGames.Appendix.Derivatives.hybridSelectorEnergy`, `OAI.DFVSGames.Appendix.Derivatives.rankProjector`, `OAI.DFVSGames.Appendix.Derivatives.selectorMultiplicity`, `OAI.DFVSGames.Appendix.Derivatives.spectralProjector`, `OAI.DFVSGames.Appendix.NaturalTransport.dualFactor`, `OAI.DFVSGames.Appendix.NaturalTransport.outputFactor`, `OAI.DFVSGames.Appendix.NaturalTransport.quotientFactor`, `OAI.DFVSGames.Appendix.Restriction.compressFrequency`, `OAI.DFVSGames.BinaryFormula.Formula.Satisfiable`, `OAI.DFVSGames.BinaryLanguage.language`, `OAI.DFVSGames.BinaryLanguage.rejectBinary`, `OAI.DFVSGames.BinaryLanguage.totalParsed`, `OAI.DFVSGames.BinaryLanguage.totalRename`, `OAI.DFVSGames.BinaryRenameWords.clauseLiterals`, `OAI.DFVSGames.BinaryRenameWords.literals`, `OAI.DFVSGames.BinaryRenameWords.token`, `OAI.DFVSGames.BinaryRenameWords.tokens`, `OAI.DFVSGames.BinaryTokenMachine.tokens`, `OAI.DFVSGames.BinaryTotalInputMachine.rejectedWord`, `OAI.DFVSGames.Clean.ActualAdviceBridge.displayedQuestion`, `OAI.DFVSGames.Clean.ActualAdviceBridge.encodedMapCoefficients`, `OAI.DFVSGames.Clean.ActualAdviceBridge.indexSlot`, `OAI.DFVSGames.Clean.ActualAdviceBridge.mapBitsEquiv`, `OAI.DFVSGames.Clean.ActualAdviceBridge.projection`, `OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.Policies`, `OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.extendTargetKernel`, `OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.firstResponse`, `OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.fixedMapSuccess`, `OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.responses`, `OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.secondResponse`, `OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.success`, `OAI.DFVSGames.Clean.AdviceImageLaw.coefficientsSplitEquiv`, `OAI.DFVSGames.Clean.AdviceImageLaw.columnImage`, `OAI.DFVSGames.Clean.AdviceImageLaw.columnSplitEquiv`, `OAI.DFVSGames.Clean.AdviceImageLaw.imageKernelEquiv`, `OAI.DFVSGames.Clean.AdviceImageLaw.rangePoint` and 296 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `DirectedFeedback_Analysis_Deletion`, `DirectedFeedback_Analysis_MatrixCharacters`, `DirectedFeedback_Analysis_MatrixNoise`, `DirectedFeedback_Analysis_NoiseEnumeration`, `DirectedFeedback_Analysis_PrivateFourier`, `DirectedFeedback_Encoding_ActualGoodRows`, `DirectedFeedback_Encoding_Bounds`, `DirectedFeedback_Encoding_CanonicalWordTemplate`, `DirectedFeedback_Encoding_ExpanderTableWords`, `DirectedFeedback_Encoding_FormulaEncoding`, `DirectedFeedback_Encoding_InstanceEquivalences`, `DirectedFeedback_Encoding_RawPrivateTable`, `DirectedFeedback_Encoding_VerifierCNF`, `DirectedFeedback_Games_ActualAdviceStochasticBridge`, `DirectedFeedback_Games_ActualAdviceUpper`, `DirectedFeedback_Games_ActualCanonical`, `DirectedFeedback_Games_AddressTupleBody`, `DirectedFeedback_Games_AdviceLaw`, `DirectedFeedback_Games_CanonicalAddress`, `DirectedFeedback_Games_ConditionalIncidences`, `DirectedFeedback_Games_Derivatives`, `DirectedFeedback_Games_ExpanderFamily`, `DirectedFeedback_Games_Explicit`, `DirectedFeedback_Games_FieldArray`, `DirectedFeedback_Games_FinalParameters`, `DirectedFeedback_Games_FinishReduction`, `DirectedFeedback_Games_InitialGraph`, `DirectedFeedback_Games_KMSAnalyticHybridEnergyFiber`, `DirectedFeedback_Games_KMSAnalyticSmallTransport`, `DirectedFeedback_Games_KernelCardinality`, `DirectedFeedback_Games_NaturalTransport`, `DirectedFeedback_Games_PartnerFullSampling`, `DirectedFeedback_Games_Product`, `DirectedFeedback_Games_ProductLaw`, `DirectedFeedback_Games_ProfileCorrection`, `DirectedFeedback_Games_RowErasureSliceQuotient`, `DirectedFeedback_Games_SignaturePrepare`, `DirectedFeedback_Games_StageData`, `DirectedFeedback_Games_Target`, `DirectedFeedback_Games_TestEmit`, `DirectedFeedback_Games_UniformReduction`, `DirectedFeedback_Machines_ContextLoad`, `DirectedFeedback_Machines_MachineBinaryNameMachine`, `DirectedFeedback_Machines_MachineBinaryRenameMachine`, `DirectedFeedback_Machines_MachineBinaryTokenMachine`, `DirectedFeedback_Machines_MachineBinaryTotalInputMachine`, `DirectedFeedback_Machines_MachineCloudCount`, `DirectedFeedback_Machines_MachineCloudPadding`, `DirectedFeedback_Machines_MachineCloudSelect`, `DirectedFeedback_Machines_MachineEmbedding`, `DirectedFeedback_Machines_MachineLookupSpec`, `DirectedFeedback_Machines_MachinePreservingLookupClean`, `DirectedFeedback_Machines_MachineProductPower`, `DirectedFeedback_Machines_MachineRegularMetadata`, `DirectedFeedback_Machines_MachineSingleOrbitCodec`, `DirectedFeedback_Machines_MachineStateEquiv`, `DirectedFeedback_Machines_MachineSubdivisionLoop`, `DirectedFeedback_Machines_MachineSubdivisionRows`, `DirectedFeedback_Machines_MachineSubstitution`, `DirectedFeedback_Machines_MachineTemplateAddress`, `DirectedFeedback_Machines_MachineTransducer`, `DirectedFeedback_Machines_MachineUnaryAdd`, `DirectedFeedback_Machines_PoweringMachineWord`, `DirectedFeedback_Machines_RawInitialMachineFinish`, `DirectedFeedback_Machines_RuntimeFinish`, `DirectedFeedback_Machines_Tape`, `DirectedFeedback_Machines_TupleOrder`, `DirectedFeedback_Probability_Basic`, `DirectedFeedback_Probability_KMSFourthMomentMixedRestriction`, `DirectedFeedback_Probability_KMSFourthMomentZoomTransport`, `DirectedFeedback_Probability_Mixture`, `DirectedFeedback_Probability_RepeatedGameBounds`, `DirectedFeedback_RankGraph_Clone100Counting`, `DirectedFeedback_RankGraph_CloneGap`, `DirectedFeedback_RankGraph_MachineClone100Finish`, `DirectedFeedback_RankGraph_SumBox`.
--
--   **Imports.** It imports the bundles `OAIQ085D000` and `OAIQ085D001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ085D012`, `OAIQ085D013`, `OAIQ085D014`, `OAIQ085D015`, `OAIQ085D016` and `OAIQ085D017`; the statement `OAI.DFVSGames.Decoder.MatrixGap.parameters_of_inverse`.
-- source:
--   OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ085D000
import Definitions.Def_OAIQ085D001

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineEmbedding

open Turing.TM2

variable {K E Λ Λextra σ τ : Type} {Γ : K → Type} {Δ : E → Type}

def configuration (haltTarget : Option (Λ ⊕ Λextra)) (extraState : τ)
    (extraTapes : ∀ e, List (Δ e)) (c : Cfg Γ Λ σ) :
    Cfg (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ) where
  l := label haltTarget c.l
  var := (c.var, extraState)
  stk := tapes c.stk extraTapes

def statement (haltTarget : Option (Λ ⊕ Λextra)) :
    Stmt Γ Λ σ → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ)
  | .push k f next => .push (.inl k) (fun st => f st.1) (statement haltTarget next)
  | .peek k f next => .peek (.inl k) (fun st v => (f st.1 v, st.2))
      (statement haltTarget next)
  | .pop k f next => .pop (.inl k) (fun st v => (f st.1 v, st.2))
      (statement haltTarget next)
  | .load f next => .load (fun st => (f st.1, st.2)) (statement haltTarget next)
  | .branch f yes no => .branch (fun st => f st.1)
      (statement haltTarget yes) (statement haltTarget no)
  | .goto f => .goto (fun st => .inl (f st.1))
  | .halt => match haltTarget with
      | none => .halt
      | some l => .goto (fun _ => l)

variable [DecidableEq K] [DecidableEq E]

theorem tapes_update (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e))
    (k : K) (value : List (Γ k)) :
    tapes (Function.update source k value) extra =
      Function.update (tapes source extra) (.inl k) value := by
  funext j
  cases j with
  | inl j =>
    by_cases h : j = k
    · subst j
      simp [Function.update]
    · simp [Function.update, h]
  | inr e => simp [Function.update]

theorem stepAux_simulation (haltTarget : Option (Λ ⊕ Λextra))
    (extraState : τ) (extraTapes : ∀ e, List (Δ e))
    (q : Stmt Γ Λ σ) (state : σ) (source : ∀ k, List (Γ k)) :
    stepAux (statement haltTarget q) (state, extraState) (tapes source extraTapes) =
      configuration haltTarget extraState extraTapes (stepAux q state source) := by
  induction q generalizing state source with
  | push k f next ih =>
    simp only [statement, stepAux, tapes_inl]
    rw [← tapes_update]
    exact ih state (Function.update source k (f state :: source k))
  | peek k f next ih =>
    simpa only [statement, stepAux, tapes_inl] using
      ih (f state (source k).head?) source
  | pop k f next ih =>
    simp only [statement, stepAux, tapes_inl]
    rw [← tapes_update]
    exact ih (f state (source k).head?) (Function.update source k (source k).tail)
  | load f next ih =>
    simpa only [statement, stepAux] using ih (f state) source
  | branch f yes no ihYes ihNo =>
    cases h : f state with
    | false => simpa only [statement, stepAux, h, Bool.cond_false] using ihNo state source
    | true => simpa only [statement, stepAux, h, Bool.cond_true] using ihYes state source
  | goto f => rfl
  | halt => cases haltTarget <;> rfl

def program (haltTarget : Option (Λ ⊕ Λextra)) (source : Λ → Stmt Γ Λ σ)
    (extra : Λextra → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ)) :
    Λ ⊕ Λextra → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ)
  | .inl l => statement haltTarget (source l)
  | .inr l => extra l

theorem step_running (haltTarget : Option (Λ ⊕ Λextra))
    (extraState : τ) (extraTapes : ∀ e, List (Δ e))
    (source : Λ → Stmt Γ Λ σ)
    (extra : Λextra → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ))
    (l : Λ) (state : σ) (sourceTapes : ∀ k, List (Γ k)) :
    step (program haltTarget source extra)
      (configuration haltTarget extraState extraTapes ⟨some l, state, sourceTapes⟩) =
      some (configuration haltTarget extraState extraTapes
        (stepAux (source l) state sourceTapes)) := by
  change some (stepAux (statement haltTarget (source l)) (state, extraState)
    (tapes sourceTapes extraTapes)) = _
  rw [stepAux_simulation]

theorem step_simulation (haltTarget : Option (Λ ⊕ Λextra))
    (extraState : τ) (extraTapes : ∀ e, List (Δ e))
    (source : Λ → Stmt Γ Λ σ)
    (extra : Λextra → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ))
    (a b : Cfg Γ Λ σ) (h : step source a = some b) :
    step (program haltTarget source extra)
      (configuration haltTarget extraState extraTapes a) =
      some (configuration haltTarget extraState extraTapes b) := by
  cases a with
  | mk l state sourceTapes =>
    cases l with
    | none => simp [step] at h
    | some l =>
      have hb : stepAux (source l) state sourceTapes = b := Option.some.inj h
      rw [← hb]
      exact step_running haltTarget extraState extraTapes source extra l state sourceTapes

end DFVSGames.Foundations.Complexity.MachineEmbedding


namespace DFVSGames.Foundations.Complexity.MachineComposition

def embeddedExecution {K E Λ Λextra σ τ : Type} {Γ : K → Type} {Δ : E → Type}
    [DecidableEq K] [DecidableEq E]
    (haltTarget : Option (Λ ⊕ Λextra)) (extraState : τ)
    (extraTapes : ∀ e, List (Δ e))
    (source : Λ → Turing.TM2.Stmt Γ Λ σ)
    (extra : Λextra → Turing.TM2.Stmt (MachineEmbedding.Alphabet Γ Δ)
      (Λ ⊕ Λextra) (σ × τ))
    {start finish : Turing.TM2.Cfg Γ Λ σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime (Turing.TM2.step source)
      start (some finish) budget) :
    StateTransition.EvalsToInTime (Turing.TM2.step (MachineEmbedding.program haltTarget source extra))
      (MachineEmbedding.configuration haltTarget extraState extraTapes start)
      (some (MachineEmbedding.configuration haltTarget extraState extraTapes finish)) budget :=
  liftExecutionInTime (Turing.TM2.step source)
    (Turing.TM2.step (MachineEmbedding.program haltTarget source extra))
    (MachineEmbedding.configuration haltTarget extraState extraTapes)
    (MachineEmbedding.step_simulation haltTarget extraState extraTapes source extra) execution

end DFVSGames.Foundations.Complexity.MachineComposition


namespace DFVSGames.Foundations.Complexity.MachineCopy

open Turing

variable {K Λ σ β : Type} [DecidableEq K]

def drainedTapes (source scratch : K) (base : K → List β) : K → List β :=
  Reduction.MachineTransfer.tapesAt source scratch base [] (base source).reverse

end DFVSGames.Foundations.Complexity.MachineCopy

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Target
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Target

def Formula.Satisfiable (formula : Formula) : Prop :=
  ∃ assignment : Fin formula.«variables» → Bool,
    ∀ clause ∈ formula.clauses, clause.eval assignment = true

def countSatisfied {n q : Nat} (labeling : Fin n → Fin q) :
    List (Constraint n q) → Nat
  | [] => 0
  | constraint :: rest =>
      (if constraint.satisfied labeling then 1 else 0) + countSatisfied labeling rest

end DFVSGames.Foundations.Target


namespace DFVSGames.Foundations.Complexity

open Target

theorem literalBits_length_le {n : Nat} (literal : Literal n) :
    (encodeWords (literalWords literal)).length ≤ n + 2 := by
  have hindex := literal.variableIndex.isLt
  cases hp : literal.positive <;> simp [literalWords, hp]

theorem clauseBits_length_le {n : Nat} (clause : Clause n) :
    (encodeWords (clauseWords clause)).length ≤ 3 * (n + 2) := by
  have h0 := literalBits_length_le clause[0]
  have h1 := literalBits_length_le clause[1]
  have h2 := literalBits_length_le clause[2]
  simp only [clauseWords, encodeWords_append, List.length_append]
  omega

theorem clausesBits_length_le {n : Nat} (clauses : List (Clause n)) :
    (encodeWords (clauses.flatMap clauseWords)).length ≤ clauses.length * (3 * (n + 2)) := by
  induction clauses with
  | nil => simp [encodeWords]
  | cons clause clauses ih =>
      have hc := clauseBits_length_le clause
      simp only [List.flatMap_cons, encodeWords_append, List.length_append,
        List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem formulaBits_length_le (formula : Formula) :
    (formulaBits formula).length ≤
      formula.«variables» + formula.clauses.length + 2 +
        formula.clauses.length * (3 * (formula.«variables» + 2)) := by
  have h := clausesBits_length_le formula.clauses
  simp only [formulaBits, formulaWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

end DFVSGames.Foundations.Complexity


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_SumBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.BinaryFormula

def Formula.Satisfiable (F : Formula) : Prop :=
  ∃ assignment : Nat → Bool, ∀ clause ∈ F.clauses, clause.eval assignment = true

end DFVSGames.BinaryFormula

namespace DFVSGames.BinaryEncoding

open BinaryFormula

theorem formulaBits_length (formula : Formula) :
    (formulaBits formula).length =
      7 * formula.clauses.length + 2 * namesBitSize formula.clauses + 1 :=
  clausesBits_length formula.clauses

end DFVSGames.BinaryEncoding


namespace DFVSGames.Foundations.Complexity.Runtime

theorem maxLabelPushes_ge {K : Type} {Γ : K → Type} {Λ σ : Type}
    (program : Λ → Turing.TM2.Stmt Γ Λ σ) (labels : List Λ) (label : Λ)
    (member : label ∈ labels) :
    statementPushBound (program label) ≤ maxLabelPushes program labels := by
  induction labels with
  | nil => simp at member
  | cons first rest ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

theorem statement_le_programPushBound (tm : Turing.FinTM2) (label : tm.Λ) :
    statementPushBound (tm.m label) ≤ programPushBound tm := by
  apply maxLabelPushes_ge
  simpa using tm.ΛFin.complete label

theorem stepAuxStackLength {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]
    (stmt : Turing.TM2.Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) (k : K) :
    ((Turing.TM2.stepAux stmt state tapes).stk k).length ≤
      (tapes k).length + statementPushBound stmt := by
  induction stmt generalizing state tapes with
  | push j f next ih =>
      have changed : ((Function.update tapes j (f state :: tapes j)) k).length ≤
          (tapes k).length + 1 := by
        by_cases same : k = j
        · subst k; simp
        · simp [Function.update, same]
      have h := ih state (Function.update tapes j (f state :: tapes j))
      simp only [Turing.TM2.stepAux, statementPushBound]
      omega
  | peek j f next ih =>
      simpa only [Turing.TM2.stepAux, statementPushBound] using
        ih (f state (tapes j).head?) tapes
  | pop j f next ih =>
      have changed : ((Function.update tapes j (tapes j).tail) k).length ≤
          (tapes k).length := by
        by_cases same : k = j
        · subst k; simp
        · simp [Function.update, same]
      have h := ih (f state (tapes j).head?) (Function.update tapes j (tapes j).tail)
      simp only [Turing.TM2.stepAux, statementPushBound]
      omega
  | load f next ih =>
      simpa only [Turing.TM2.stepAux, statementPushBound] using ih (f state) tapes
  | branch condition yes no ihYes ihNo =>
      cases decision : condition state with
      | false =>
          have h := ihNo state tapes
          have hm := Nat.le_max_right (statementPushBound yes) (statementPushBound no)
          simp only [Turing.TM2.stepAux, statementPushBound, decision, Bool.cond_false]
          omega
      | true =>
          have h := ihYes state tapes
          have hm := Nat.le_max_left (statementPushBound yes) (statementPushBound no)
          simp only [Turing.TM2.stepAux, statementPushBound, decision, Bool.cond_true]
          omega
  | goto f => simp [Turing.TM2.stepAux, statementPushBound]
  | halt => simp [Turing.TM2.stepAux, statementPushBound]

theorem iterateSizeBound_inline_Runtime {α : Type} (f : α → α) (size : α → Nat) (C : Nat)
    (oneStep : ∀ x, size (f x) ≤ size x + C) (n : Nat) (x : α) :
    size ((f^[n]) x) ≤ size x + n * C := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := oneStep ((f^[n]) x)
      have bound : size (f ((f^[n]) x)) ≤ size x + (n + 1) * C := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      simpa only [Function.iterate_succ_apply'] using bound

theorem executionSizeBound {σ : Type} (step : σ → Option σ) (size : σ → Nat) (C : Nat)
    (oneStep : ∀ a b, step a = some b → size b ≤ size a + C)
    {start finish : σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime step start (some finish) budget) :
    size finish ≤ size start + budget * C := by
  let liftedSize : Option σ → Nat := fun state => (state.map size).getD 0
  have liftedStep : ∀ state : Option σ,
      liftedSize (state.bind step) ≤ liftedSize state + C := by
    intro state
    cases state with
    | none => simp [liftedSize]
    | some a =>
        cases transition : step a with
        | none => simp [liftedSize, transition]
        | some b => simpa [liftedSize, transition] using oneStep a b transition
  have bound := iterateSizeBound_inline_Runtime (fun state : Option σ => state.bind step)
    liftedSize C liftedStep execution.steps (some start)
  change liftedSize ((flip bind step)^[execution.steps] (some start)) ≤ _ at bound
  rw [execution.evals_in_steps] at bound
  simp only [liftedSize, Option.map_some, Option.getD_some] at bound
  exact Nat.le_trans bound (Nat.add_le_add_left
    (Nat.mul_le_mul_right C execution.steps_le_m) _)

theorem stepStackLength (tm : Turing.FinTM2) (k : tm.K) (a b : tm.Cfg)
    (transition : tm.step a = some b) :
    (b.stk k).length ≤ (a.stk k).length + programPushBound tm := by
  cases a with
  | mk label state tapes =>
      cases label with
      | none => simp [Turing.FinTM2.step, Turing.TM2.step] at transition
      | some label =>
          have result := Option.some.inj transition
          rw [← result]
          exact Nat.le_trans (stepAuxStackLength _ _ _ _)
            (Nat.add_le_add_left (statement_le_programPushBound tm label) _)

theorem initialStackLength (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀)) (k : tm.K) :
    ((Turing.initList tm input).stk k).length ≤ input.length := by
  simp only [Turing.initList]
  split
  next same => subst k; exact Nat.le_refl _
  next _ => simp

@[simp] theorem haltedOutputLength (tm : Turing.FinTM2) (output : List (tm.Γ tm.k₁)) :
    ((Turing.haltList tm output).stk tm.k₁).length = output.length := by
  simp [Turing.haltList]

theorem outputLength_le (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀))
    (output : List (tm.Γ tm.k₁)) (budget : Nat)
    (execution : Turing.TM2OutputsInTime tm input (some output) budget) :
    output.length ≤ input.length + budget * programPushBound tm := by
  have bound := executionSizeBound tm.step (fun cfg => (cfg.stk tm.k₁).length)
    (programPushBound tm) (stepStackLength tm tm.k₁) execution
  calc
    output.length = ((Turing.haltList tm output).stk tm.k₁).length := (haltedOutputLength tm output).symm
    _ ≤ ((Turing.initList tm input).stk tm.k₁).length + budget * programPushBound tm := bound
    _ ≤ input.length + budget * programPushBound tm :=
      Nat.add_le_add_right (initialStackLength tm input tm.k₁) _

theorem encodedOutputLength {α β αΓ βΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (certificate : Turing.TM2ComputableInPolyTime ea eb f) (a : α) :
    (eb (f a)).length ≤
      (Polynomial.X + Polynomial.C (programPushBound certificate.tm) * certificate.time).eval
        (ea a).length := by
  have bound := outputLength_le certificate.tm _ _ _ (certificate.outputsFun a)
  simpa only [List.length_map, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C, Nat.mul_comm] using bound

end DFVSGames.Foundations.Complexity.Runtime

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineSubstitution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineStackSwap

open Turing.TM2

variable {A B C Λ σ : Type}
  {ΓA : A → Type} {ΓB : B → Type} {ΓC : C → Type}

abbrev Alphabet (ΓA : A → Type) (ΓB : B → Type) (ΓC : C → Type) :=
  MachineEmbedding.Alphabet ΓA (MachineEmbedding.Alphabet ΓB ΓC)

def tapes (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) :
    ∀ j, List (Alphabet ΓB ΓA ΓC j)
  | .inl b => source (.inr (.inl b))
  | .inr (.inl a) => source (.inl a)
  | .inr (.inr c) => source (.inr (.inr c))

@[simp] theorem tapes_first (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) (a : A) :
    tapes source (.inr (.inl a)) = source (.inl a) := rfl
@[simp] theorem tapes_second (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) (b : B) :
    tapes source (.inl b) = source (.inr (.inl b)) := rfl
@[simp] theorem tapes_third (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) (c : C) :
    tapes source (.inr (.inr c)) = source (.inr (.inr c)) := rfl

def configuration (c : Cfg (Alphabet ΓA ΓB ΓC) Λ σ) :
    Cfg (Alphabet ΓB ΓA ΓC) Λ σ where
  l := c.l
  var := c.var
  stk := tapes c.stk

def statement : Stmt (Alphabet ΓA ΓB ΓC) Λ σ → Stmt (Alphabet ΓB ΓA ΓC) Λ σ
  | .push (.inl a) f next => .push (.inr (.inl a)) f (statement next)
  | .push (.inr (.inl b)) f next => .push (.inl b) f (statement next)
  | .push (.inr (.inr c)) f next => .push (.inr (.inr c)) f (statement next)
  | .peek (.inl a) f next => .peek (.inr (.inl a)) f (statement next)
  | .peek (.inr (.inl b)) f next => .peek (.inl b) f (statement next)
  | .peek (.inr (.inr c)) f next => .peek (.inr (.inr c)) f (statement next)
  | .pop (.inl a) f next => .pop (.inr (.inl a)) f (statement next)
  | .pop (.inr (.inl b)) f next => .pop (.inl b) f (statement next)
  | .pop (.inr (.inr c)) f next => .pop (.inr (.inr c)) f (statement next)
  | .load f next => .load f (statement next)
  | .branch f yes no => .branch f (statement yes) (statement no)
  | .goto f => .goto f
  | .halt => .halt

variable [DecidableEq A] [DecidableEq B] [DecidableEq C]

theorem tapes_update_first (source : ∀ k, List (Alphabet ΓA ΓB ΓC k))
    (a : A) (value : List (ΓA a)) :
    tapes (Function.update source (.inl a) value) =
      Function.update (tapes source) (.inr (.inl a)) value := by
  funext j
  rcases j with b | a' | c
  · simp [Function.update]
  · by_cases h : a' = a
    · subst a'; simp [Function.update]
    · simp [Function.update, h]
  · simp [Function.update]

theorem tapes_update_second (source : ∀ k, List (Alphabet ΓA ΓB ΓC k))
    (b : B) (value : List (ΓB b)) :
    tapes (Function.update source (.inr (.inl b)) value) =
      Function.update (tapes source) (.inl b) value := by
  funext j
  rcases j with b' | a | c
  · by_cases h : b' = b
    · subst b'; simp [Function.update]
    · simp [Function.update, h]
  · simp [Function.update]
  · simp [Function.update]

theorem tapes_update_third (source : ∀ k, List (Alphabet ΓA ΓB ΓC k))
    (c : C) (value : List (ΓC c)) :
    tapes (Function.update source (.inr (.inr c)) value) =
      Function.update (tapes source) (.inr (.inr c)) value := by
  funext j
  rcases j with b | a | c'
  · simp [Function.update]
  · simp [Function.update]
  · by_cases h : c' = c
    · subst c'; simp [Function.update]
    · simp [Function.update, h]

theorem stepAux_simulation (q : Stmt (Alphabet ΓA ΓB ΓC) Λ σ)
    (state : σ) (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) :
    stepAux (statement q) state (tapes source) =
      configuration (stepAux q state source) := by
  induction q generalizing state source with
  | push k f next ih =>
    rcases k with a | b | c
    · simp only [statement, stepAux, tapes_first]
      rw [← tapes_update_first]
      exact ih state (Function.update source (.inl a) (f state :: source (.inl a)))
    · simp only [statement, stepAux, tapes_second]
      rw [← tapes_update_second]
      exact ih state (Function.update source (.inr (.inl b))
        (f state :: source (.inr (.inl b))))
    · simp only [statement, stepAux, tapes_third]
      rw [← tapes_update_third]
      exact ih state (Function.update source (.inr (.inr c))
        (f state :: source (.inr (.inr c))))
  | peek k f next ih =>
    rcases k with a | b | c
    · simpa only [statement, stepAux, tapes_first] using
        ih (f state (source (.inl a)).head?) source
    · simpa only [statement, stepAux, tapes_second] using
        ih (f state (source (.inr (.inl b))).head?) source
    · simpa only [statement, stepAux, tapes_third] using
        ih (f state (source (.inr (.inr c))).head?) source
  | pop k f next ih =>
    rcases k with a | b | c
    · simp only [statement, stepAux, tapes_first]
      rw [← tapes_update_first]
      exact ih (f state (source (.inl a)).head?)
        (Function.update source (.inl a) (source (.inl a)).tail)
    · simp only [statement, stepAux, tapes_second]
      rw [← tapes_update_second]
      exact ih (f state (source (.inr (.inl b))).head?)
        (Function.update source (.inr (.inl b)) (source (.inr (.inl b))).tail)
    · simp only [statement, stepAux, tapes_third]
      rw [← tapes_update_third]
      exact ih (f state (source (.inr (.inr c))).head?)
        (Function.update source (.inr (.inr c)) (source (.inr (.inr c))).tail)
  | load f next ih => simpa only [statement, stepAux] using ih (f state) source
  | branch f yes no ihYes ihNo =>
    cases h : f state with
    | false => simpa only [statement, stepAux, h, Bool.cond_false] using ihNo state source
    | true => simpa only [statement, stepAux, h, Bool.cond_true] using ihYes state source
  | goto f => rfl
  | halt => rfl

end DFVSGames.Foundations.Complexity.MachineStackSwap


namespace DFVSGames.Foundations.Complexity.MachineSequential

open Turing

abbrev Symbols (first second : FinTM2) : Tape first second → Type :=
  MachineEmbedding.Alphabet first.Γ
    (MachineEmbedding.Alphabet second.Γ (fun _ : Unit => second.Γ second.k₀))

def firstStatement (first second : FinTM2) (q : first.Stmt) :
    TM2.Stmt (Symbols first second) (Label first second) (State first second) :=
  MachineControl.statement id (firstStates first second)
    (MachineEmbedding.statement (some (bridgeLabel first second false)) q)

def secondStatement (first second : FinTM2) (q : second.Stmt) :
    TM2.Stmt (Symbols first second) (Label first second) (State first second) :=
  MachineControl.statement (secondLabels first second) (secondStates first second)
    (MachineStackSwap.statement
      (MachineEmbedding.statement
        (Δ := MachineEmbedding.Alphabet first.Γ (fun _ : Unit => second.Γ second.k₀))
        (Λextra := Bool ⊕ first.Λ) none q))

def firstConfiguration (first second : FinTM2) (c : first.Cfg) :
    TM2.Cfg (Symbols first second) (Label first second) (State first second) :=
  MachineControl.configuration id (firstStates first second)
    (MachineEmbedding.configuration (some (bridgeLabel first second false))
      (second.initialState, (none : Register second)) (fun _ => []) c)

def secondConfiguration (first second : FinTM2) (c : second.Cfg) :
    TM2.Cfg (Symbols first second) (Label first second) (State first second) :=
  MachineControl.configuration (secondLabels first second) (secondStates first second)
    (MachineStackSwap.configuration
      (MachineEmbedding.configuration
        (Δ := MachineEmbedding.Alphabet first.Γ (fun _ : Unit => second.Γ second.k₀))
        (Λextra := Bool ⊕ first.Λ) none
        (first.initialState, (none : Register second)) (fun _ => []) c))

def temporaryTapes (first second : FinTM2) (word : List (second.Γ second.k₀)) :
    ∀ k, List (Symbols first second k)
  | .inl _ => []
  | .inr (.inl _) => []
  | .inr (.inr _) => word

def temporaryConfiguration (first second : FinTM2) (word : List (second.Γ second.k₀)) :
    TM2.Cfg (Symbols first second) (Label first second) (State first second) :=
  ⟨some (bridgeLabel first second true),
    ((first.initialState, second.initialState), none), temporaryTapes first second word⟩

theorem firstTransfer_tapes (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (word : List (first.Γ first.k₁)) :
    Reduction.MachineTransfer.tapesAt (.inl first.k₁) (.inr (.inr ()))
      (firstConfiguration first second (haltList first word)).stk [] (word.reverse.map relabel) =
        temporaryTapes first second (word.reverse.map relabel) := by
  funext k
  rcases k with k | k | k
  · by_cases h : k = first.k₁
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, temporaryTapes]
    · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, firstConfiguration,
        MachineControl.configuration, MachineEmbedding.configuration, MachineEmbedding.tapes,
        haltList, h]
  · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, firstConfiguration,
      MachineControl.configuration, MachineEmbedding.configuration, MachineEmbedding.tapes]
  · cases k
    simp [Reduction.MachineTransfer.tapesAt, temporaryTapes]

theorem secondTransfer_tapes (first second : FinTM2) (word : List (second.Γ second.k₀)) :
    Reduction.MachineTransfer.tapesAt (Γ := Symbols first second)
      (.inr (.inr ())) (.inr (.inl second.k₀))
      (temporaryTapes first second word) [] word.reverse =
        (secondConfiguration first second (initList second word.reverse)).stk := by
  funext k
  rcases k with k | k | k
  · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, secondConfiguration,
      MachineControl.configuration, MachineStackSwap.configuration, MachineStackSwap.tapes,
      MachineEmbedding.configuration, MachineEmbedding.tapes]
  · by_cases h : k = second.k₀
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, secondConfiguration,
        MachineControl.configuration, MachineStackSwap.configuration, MachineStackSwap.tapes,
        MachineEmbedding.configuration, MachineEmbedding.tapes, initList]
    · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, secondConfiguration,
        MachineControl.configuration, MachineStackSwap.configuration, MachineStackSwap.tapes,
        MachineEmbedding.configuration, MachineEmbedding.tapes, initList, h]
  · cases k
    simp [Reduction.MachineTransfer.tapesAt, secondConfiguration,
      MachineControl.configuration, MachineStackSwap.configuration, MachineStackSwap.tapes,
      MachineEmbedding.configuration, MachineEmbedding.tapes]

end DFVSGames.Foundations.Complexity.MachineSequential

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineTransducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Reduction.MachineFieldTemplate

open Turing
open DFVSGames.Foundations.Complexity
open MachineSubstitution (pushWord stepAux_pushWord)

variable {q : Nat} {K Λ σ : Type}

def tokenOutput (fields : Fin q → List Bool) : Token q → List Bool
  | .literal bits => bits
  | .copy j => fields j

def templateOutput (tokens : List (Token q)) (fields : Fin q → List Bool) : List Bool :=
  tokens.flatMap (tokenOutput fields)

end DFVSGames.Reduction.MachineFieldTemplate

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_RuntimeFinish
attribute [-instance] _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineUnaryAffineAt

open Turing
open MachineComposition
open Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

def seed (destination : K) (offset : Nat) (scanLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  pushWord destination (encodeWord offset).reverse (.goto (fun _ => scanLabel))

end DFVSGames.Foundations.Complexity.MachineUnaryAffineAt


namespace DFVSGames.Integration.GapSemantics

open DFVSGames.Foundations.Target

def satisfactionRate {q : Nat} (g : Instance q) (labeling : Fin g.vertices → Fin q) : ℚ :=
  (countSatisfied labeling g.constraints : ℚ) / g.constraints.length

theorem countSatisfied_eq_sum {n q : Nat} (labeling : Fin n → Fin q)
    (constraints : List (Constraint n q)) :
    countSatisfied labeling constraints =
      (constraints.map (fun c => if c.satisfied labeling then (1 : Nat) else 0)).sum := by
  induction constraints with
  | nil => rfl
  | cons c cs ih => simp [countSatisfied, ih]

end DFVSGames.Integration.GapSemantics

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_InstanceEquivalences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Integration.InstanceEquivalences

open DFVSGames.Foundations.Target
open GapSemantics

theorem rename_count {n m q : Nat} (e : Fin n ≃ Fin m)
    (constraints : List (Constraint n q)) (labeling : Fin m → Fin q) :
    countSatisfied labeling (constraints.map (renameConstraint e)) =
      countSatisfied (labeling ∘ e) constraints := by
  induction constraints with
  | nil => rfl
  | cons c cs ih =>
      by_cases hc : c.satisfied (labeling ∘ e) = true <;> simp [countSatisfied, ih, hc]

theorem countSatisfied_perm {n q : Nat} (labeling : Fin n → Fin q)
    {constraints constraints' : List (Constraint n q)}
    (h : constraints.Perm constraints') :
    countSatisfied labeling constraints = countSatisfied labeling constraints' := by
  rw [countSatisfied_eq_sum, countSatisfied_eq_sum]
  exact (h.map (fun c => if c.satisfied labeling then (1 : Nat) else 0)).sum_eq

theorem satisfactionRate_eq_of_rename_perm {q : Nat} (g h : Instance q)
    (e : Fin g.vertices ≃ Fin h.vertices)
    (hp : h.constraints.Perm (g.constraints.map (renameConstraint e)))
    (labeling : Fin h.vertices → Fin q) :
    satisfactionRate h labeling = satisfactionRate g (labeling ∘ e) := by
  have hcount := countSatisfied_perm labeling hp
  rw [rename_count] at hcount
  have hlength := hp.length_eq
  simp only [List.length_map] at hlength
  unfold satisfactionRate
  rw [hcount, hlength]

end DFVSGames.Integration.InstanceEquivalences


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_FormulaEncoding
attribute [-instance] _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.PartnerLinear.partnerModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Integration.InstanceValue

open DFVSGames.Foundations
open Target

def maxSatisfied {q : Nat} (g : Instance q) : Nat :=
  Finset.univ.sup (fun labeling : Fin g.vertices → Fin q =>
    countSatisfied labeling g.constraints)

noncomputable def value {q : Nat} (g : Instance q) : ℝ :=
  (maxSatisfied g : ℝ) / g.constraints.length

theorem countSatisfied_le_maxSatisfied {q : Nat} (g : Instance q)
    (labeling : Fin g.vertices → Fin q) :
    countSatisfied labeling g.constraints ≤ maxSatisfied g := by
  unfold maxSatisfied
  exact Finset.le_sup
    (f := fun labeling : Fin g.vertices → Fin q => countSatisfied labeling g.constraints)
    (Finset.mem_univ labeling)

theorem labeling_rate_le_value {q : Nat} (g : Instance q)
    (labeling : Fin g.vertices → Fin q) :
    (countSatisfied labeling g.constraints : ℝ) / g.constraints.length ≤ value g := by
  apply div_le_div_of_nonneg_right
  · exact_mod_cast countSatisfied_le_maxSatisfied g labeling
  · exact Nat.cast_nonneg _

theorem satisfactionRate_le_value {q : Nat} (g : Instance q)
    (labeling : Fin g.vertices → Fin q) :
    (GapSemantics.satisfactionRate g labeling : ℝ) ≤ value g := by
  simpa [GapSemantics.satisfactionRate] using labeling_rate_le_value g labeling

end DFVSGames.Integration.InstanceValue


namespace DFVSGames.Integration.BinaryLinear

open BinaryCoordinates

theorem ofBit_xor : ∀ a b : Bool, ofBit (a ^^ b) = ofBit a + ofBit b := by decide

end DFVSGames.Integration.BinaryLinear


namespace DFVSGames.Integration.TranslationTarget

open DFVSGames.Foundations
open Target

def IsTranslationInstance {q s : Nat} (coordinates : Fin q ≃ BinaryLinear.Vector s)
    (g : Instance q) : Prop :=
  ∀ constraint ∈ g.constraints, ∃ shift : BinaryLinear.Vector s,
    ∀ label : Fin q,
      coordinates (constraint.permutation.images[label]) = coordinates label + shift

end DFVSGames.Integration.TranslationTarget


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineSubdivisionRows
attribute [-instance] _root_.OAI.DFVSGames.Soundness.PartnerLinear.partnerModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Reduction.Encoding

open Integration.BinaryLinear
open Foundations.Target

theorem translationTable_satisfied_iff {s : Nat}
    (a b cLeft cRight : Integration.BinaryLinear.Vector s) :
    (translationTable a b).images[alphabetEquiv s cLeft] = alphabetEquiv s cRight ↔
      cLeft + a + b = cRight := by
  rw [translationTable_images]
  exact (alphabetEquiv s).injective.eq_iff


end DFVSGames.Reduction.Encoding


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Analysis_Deletion
attribute [-instance] _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DFVSGames.Soundness.PartnerLinear.partnerModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Fourier.MatrixRestrictions

open DFVSGames.Integration.BinaryLinear
open scoped BigOperators

variable {E C : Type*} [AddCommGroup E] [Module F2 E]
    [AddCommGroup C] [Module F2 C]

def translate (W : Submodule F2 E)
    (C' : Submodule F2 C) (X : (E →ₗ[F2] C))
    (A : Parameter W C') : (E →ₗ[F2] C) := X + embed W C' A

def embedding (W : Submodule F2 E) (C' : Submodule F2 C) :
    Parameter W C' →ₗ[F2] (E →ₗ[F2] C) where
  toFun := embed W C'
  map_add' A B := by
    apply LinearMap.ext
    intro x
    rfl
  map_smul' a A := by
    apply LinearMap.ext
    intro x
    rfl

noncomputable def order (W : Submodule F2 E) (C' : Submodule F2 C) : Nat :=
  Module.finrank F2 W + Module.finrank F2 (C ⧸ C')

def restrict (f : (E →ₗ[F2] C) → ℝ) (W : Submodule F2 E)
    (C' : Submodule F2 C) (X : E →ₗ[F2] C) : Parameter W C' → ℝ :=
  fun A => f (translate W C' X A)

noncomputable instance parameterFintype [Finite E] [Finite C]
    (W : Submodule F2 E) (C' : Submodule F2 C) : Fintype (Parameter W C') := by
  classical
  letI : Fintype E := Fintype.ofFinite E
  letI : Fintype C' := Fintype.ofFinite C'
  exact Fintype.ofInjective (fun A : Parameter W C' => (A : (E ⧸ W) → C'))
    DFunLike.coe_injective

end DFVSGames.Fourier.MatrixRestrictions


namespace DFVSGames.Reduction.ActualOrbit

open DFVSGames.Integration.BinaryLinear

universe u v

variable {Q : Type u} {T : Type v} {s d : Nat}

def unfold (can : Q → Ambient s d × T) (label : Vertex can → Vector s) (q : Q) :
    Vector s := label (vertex can q) + offset can q

theorem add_self_vector (c : Vector s) : c + c = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (c i)

theorem add_cancel_vector (a b : Vector s) : (a + b) + b = a := by
  rw [add_assoc, add_self_vector, add_zero]

theorem constraint_iff_unfolded (can : Q → Ambient s d × T)
    (labelL labelR : Vertex can → Vector s) (q r : Q) :
    (labelL (vertex can q) + offset can q) + offset can r = labelR (vertex can r) ↔
      unfold can labelL q = unfold can labelR r := by
  constructor
  · intro h
    have h' := congrArg (fun c => c + offset can r) h
    simpa only [add_cancel_vector, unfold] using h'
  · intro h
    have h' := congrArg (fun c => c + offset can r) h
    simpa only [add_cancel_vector, unfold] using h'

end DFVSGames.Reduction.ActualOrbit

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Analysis_MatrixCharacters
attribute [-instance] _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DFVSGames.Soundness.PartnerLinear.partnerModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace DFVSGames.Fourier.MatrixCharacters

open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear

theorem tracePair_ext_right {n m : Nat} {S T : Matrix (Fin m) (Fin n) F2}
    (h : ∀ X, tracePair X S = tracePair X T) : S = T :=
  Matrix.ext_iff_trace_mul_left.mpr h

theorem binarySign_injective : Function.Injective binarySign := by
  intro a b h
  rcases scalar_cases a with rfl | rfl <;>
    rcases scalar_cases b with rfl | rfl
  · rfl
  · have hf : (1 : ℂ) = -1 := by simpa using h
    exact False.elim (one_ne_zero ((CharZero.eq_neg_self_iff).mp hf))
  · have hf : (1 : ℂ) = -1 := by simpa using h.symm
    exact False.elim (one_ne_zero ((CharZero.eq_neg_self_iff).mp hf))
  · rfl

theorem binarySign_real (a : F2) : ((binarySign a).re : ℂ) = binarySign a := by
  unfold binarySign
  split <;> simp

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

theorem linearTracePair_eq_matrix_tracePair {n m : Nat}
    (bE : Module.Basis (Fin m) F2 E) (bF : Module.Basis (Fin n) F2 F)
    (X : E →ₗ[F2] F) (S : F →ₗ[F2] E) :
    linearTracePair X S =
      tracePair (LinearMap.toMatrix bE bF X) (LinearMap.toMatrix bF bE S) := by
  change LinearMap.trace F2 F (X.comp S) =
    Matrix.trace (LinearMap.toMatrix bE bF X * LinearMap.toMatrix bF bE S)
  rw [LinearMap.trace_eq_matrix_trace F2 bF, LinearMap.toMatrix_comp bF bE bF]

theorem linearTraceCharacter_real (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    ((linearTraceCharacter S X).re : ℂ) = linearTraceCharacter S X := binarySign_real _

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

theorem linearTracePair_swap (X : E →ₗ[F2] F) (S : F →ₗ[F2] E) :
    linearTracePair X S = linearTracePair S X :=
  LinearMap.trace_comp_comm' S X

theorem linearTraceCharacter_swap (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    linearTraceCharacter S X = linearTraceCharacter X S := by
  simp only [linearTraceCharacter_apply, linearTracePair_swap X S]

theorem linearTracePair_ext_right {S T : F →ₗ[F2] E}
    (h : ∀ X, linearTracePair X S = linearTracePair X T) : S = T := by
  classical
  let bE := Module.finBasis F2 E
  let bF := Module.finBasis F2 F
  apply (LinearMap.toMatrix bF bE).injective
  apply tracePair_ext_right
  intro X
  obtain ⟨X', rfl⟩ := (LinearMap.toMatrix bE bF).surjective X
  exact (linearTracePair_eq_matrix_tracePair bE bF X' S).symm.trans
    ((h X').trans (linearTracePair_eq_matrix_tracePair bE bF X' T))

theorem linearTraceCharacter_injective :
    Function.Injective (linearTraceCharacter (E := E) (F := F)) := by
  intro S T h
  apply linearTracePair_ext_right
  intro X
  apply binarySign_injective
  exact congrArg (fun ψ : AddChar (E →ₗ[F2] F) ℂ => ψ X) h

theorem linearTraceCharacter_eq_zero_iff (S : F →ₗ[F2] E) :
    linearTraceCharacter S = 0 ↔ S = 0 := by
  rw [← linearTraceCharacter_zero, linearTraceCharacter_injective.eq_iff]

theorem sum_linearTraceCharacter [Fintype (E →ₗ[F2] F)] (S : F →ₗ[F2] E) :
    ∑ X, linearTraceCharacter S X =
      if S = 0 then (Fintype.card (E →ₗ[F2] F) : ℂ) else 0 := by
  classical
  rw [AddChar.sum_eq_ite]
  simp only [linearTraceCharacter_eq_zero_iff]

end DFVSGames.Fourier.MatrixCharacters
end

noncomputable section

namespace DFVSGames.Fourier.MatrixFourier

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate
open Finset
open DFVSGames.Fourier.MatrixCharacters

section FiniteGroup

variable {G : Type*} [AddCommGroup G] [Fintype G]

omit [AddCommGroup G] in
theorem star_expect (f : G → ℂ) :
    star (𝔼 x, f x) = 𝔼 x, star (f x) := by
  simp [Fintype.expect_eq_sum_div_card]

theorem star_fourierCoeff (f : G → ℂ) (ψ : AddChar G ℂ) :
    star (fourierCoeff f ψ) = 𝔼 x, star (f x) * ψ x := by
  rw [fourierCoeff, star_expect]
  simp [star_mul, mul_comm]

end FiniteGroup

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

def linearCoeff (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) : ℝ :=
  𝔼 X, f X * (linearTraceCharacter S X).re

theorem card_linearMap_reverse :
    Fintype.card (F →ₗ[F2] E) = Fintype.card (E →ₗ[F2] F) := by
  classical
  let bE := Module.finBasis F2 E
  let bF := Module.finBasis F2 F
  calc
    Fintype.card (F →ₗ[F2] E) =
        Fintype.card (Matrix (Fin (Module.finrank F2 E))
          (Fin (Module.finrank F2 F)) F2) :=
      Fintype.card_congr (LinearMap.toMatrix bF bE).toEquiv
    _ = Fintype.card (Matrix (Fin (Module.finrank F2 F))
          (Fin (Module.finrank F2 E)) F2) := by
      exact Fintype.card_congr
        { toFun := Matrix.transpose
          invFun := Matrix.transpose
          left_inv := Matrix.transpose_transpose
          right_inv := Matrix.transpose_transpose }
    _ = Fintype.card (E →ₗ[F2] F) :=
      (Fintype.card_congr (LinearMap.toMatrix bE bF).toEquiv).symm

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem linearTraceCharacter_star (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    star (linearTraceCharacter S X) = linearTraceCharacter S X := by
  calc
    _ = star (((linearTraceCharacter S X).re : ℝ) : ℂ) :=
      congrArg star (linearTraceCharacter_real S X).symm
    _ = ((linearTraceCharacter S X).re : ℂ) := by simp
    _ = linearTraceCharacter S X := linearTraceCharacter_real S X

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem linearMap_add_eq_zero_iff (X Y : E →ₗ[F2] F) :
    X + Y = 0 ↔ X = Y := by
  have htwo : (1 + 1 : F2) = 0 := by decide
  have hself : Y + Y = 0 := by
    have h := congrArg (fun c : F2 => c • Y) htwo
    simpa only [add_smul, one_smul, zero_smul] using h
  have hneg : -Y = Y := neg_eq_iff_add_eq_zero.mpr hself
  rw [add_eq_zero_iff_eq_neg, hneg]

theorem linear_character_kernel (X Y : E →ₗ[F2] F) :
    ∑ S : F →ₗ[F2] E, star (linearTraceCharacter S X) * linearTraceCharacter S Y =
      if X = Y then (Fintype.card (E →ₗ[F2] F) : ℂ) else 0 := by
  classical
  calc
    _ = ∑ S : F →ₗ[F2] E, linearTraceCharacter S (X + Y) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [linearTraceCharacter_star, AddChar.map_add_eq_mul]
    _ = ∑ S : F →ₗ[F2] E, linearTraceCharacter (X + Y) S := by
      apply Finset.sum_congr rfl
      intro S _
      exact linearTraceCharacter_swap S (X + Y)
    _ = if X + Y = 0 then (Fintype.card (F →ₗ[F2] E) : ℂ) else 0 :=
      sum_linearTraceCharacter (X + Y)
    _ = _ := by rw [linearMap_add_eq_zero_iff, card_linearMap_reverse]

theorem linear_complex_inversion (f : (E →ₗ[F2] F) → ℂ) (Y : E →ₗ[F2] F) :
    ∑ S : F →ₗ[F2] E, fourierCoeff f (linearTraceCharacter S) *
      linearTraceCharacter S Y = f Y := by
  classical
  simp only [fourierCoeff]
  simp_rw [Finset.expect_mul, mul_assoc]
  rw [← Finset.expect_sum_comm]
  simp_rw [← Finset.mul_sum, linear_character_kernel]
  rw [Finset.expect_eq_sum_div_card]
  simp [mul_ite]

theorem linear_complex_parseval (f g : (E →ₗ[F2] F) → ℂ) :
    ∑ S : F →ₗ[F2] E, star (fourierCoeff f (linearTraceCharacter S)) *
      fourierCoeff g (linearTraceCharacter S) = 𝔼 X, star (f X) * g X := by
  simp_rw [star_fourierCoeff, Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro X _
  calc
    (∑ S : F →ₗ[F2] E, (star (f X) * linearTraceCharacter S X) *
        fourierCoeff g (linearTraceCharacter S)) =
        star (f X) * ∑ S : F →ₗ[F2] E,
          fourierCoeff g (linearTraceCharacter S) * linearTraceCharacter S X := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ac_rfl
    _ = star (f X) * g X := by rw [linear_complex_inversion]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_complex (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    (linearCoeff f S : ℂ) =
      fourierCoeff (fun X => (f X : ℂ)) (linearTraceCharacter S) := by
  rw [linearCoeff, complex_ofReal_expect, fourierCoeff]
  apply Finset.expect_congr rfl
  intro X _
  rw [Complex.ofReal_mul, linearTraceCharacter_real, linearTraceCharacter_star]

theorem linear_parseval_inner (f g : (E →ₗ[F2] F) → ℝ) :
    ∑ S : F →ₗ[F2] E, linearCoeff f S * linearCoeff g S =
      𝔼 X, f X * g X := by
  apply Complex.ofReal_injective
  calc
    ((∑ S : F →ₗ[F2] E, linearCoeff f S * linearCoeff g S : ℝ) : ℂ) =
        ∑ S : F →ₗ[F2] E,
          star (fourierCoeff (fun X => (f X : ℂ)) (linearTraceCharacter S)) *
            fourierCoeff (fun X => (g X : ℂ)) (linearTraceCharacter S) := by
      change Complex.ofRealHom (∑ S : F →ₗ[F2] E, linearCoeff f S * linearCoeff g S) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro S _
      rw [← linearCoeff_complex, ← linearCoeff_complex]
      simp
    _ = 𝔼 X, star (f X : ℂ) * (g X : ℂ) := linear_complex_parseval _ _
    _ = ((𝔼 X, f X * g X : ℝ) : ℂ) := by
      rw [complex_ofReal_expect]
      simp

theorem linear_parseval (f : (E →ₗ[F2] F) → ℝ) :
    ∑ S : F →ₗ[F2] E, linearCoeff f S ^ 2 = 𝔼 X, f X ^ 2 := by
  simpa only [pow_two] using linear_parseval_inner f f

end DFVSGames.Fourier.MatrixFourier
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Analysis_MatrixNoise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DFVSGames.Fourier.MatrixNoise

open scoped BigOperators Matrix
open DFVSGames.Integration.BinaryLinear (Vector)
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixFourier

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

def evaluationCharacter (w : E) : AddChar (E →ₗ[F2] F2) ℂ where
  toFun ℓ := binarySign (ℓ w)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp only [LinearMap.add_apply, binarySign_add]

@[simp] theorem evaluationCharacter_apply (w : E) (ℓ : E →ₗ[F2] F2) :
    evaluationCharacter w ℓ = binarySign (ℓ w) := rfl

end DFVSGames.Fourier.MatrixNoise
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineSubdivisionLoop
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Hastad.SourceContexts.clauseAnswerFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.PCP

open Target

def honestAnswer {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) : ClauseAnswer :=
  ⟨assignment clause[0].variableIndex, assignment clause[1].variableIndex,
   assignment clause[2].variableIndex⟩

end DFVSGames.Foundations.PCP

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineBinaryNameMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.BinaryNameMachine

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition
open DFVSGames.Reduction.MachineTransfer

section Program

variable {K Λ A : Type} [DecidableEq K]

theorem update_source_inline_MachineBinaryNameMachine (source destination : K) (distinct : source ≠ destination)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt source destination base input output) source replacement =
      tapesAt source destination base replacement output := by
  funext k
  by_cases hs : k = source
  · subst k; simp [tapesAt, distinct]
  · by_cases hd : k = destination
    · subst k; simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hs, hd]

theorem update_destination_inline_MachineBinaryNameMachine (source destination : K)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt source destination base input output) destination replacement =
      tapesAt source destination base input replacement := by
  simp [tapesAt]

variable (source destination : K) (distinct : source ≠ destination)
variable (again : Λ) (accepted rejected : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atScan : program again = scan source destination again accepted rejected)
variable (base : K → List Bool) (ambient : A)

include distinct atScan

theorem step_empty (output : List Bool) (last register : Option Bool) :
    TM2.step program
      ⟨some again, (ambient, last, register), tapesAt source destination base [] output⟩ =
      some ⟨rejected, clean ambient, tapesAt source destination base [] output⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atScan]
  simp [scan, TM2.stepAux, distinct, update_source_inline_MachineBinaryNameMachine]

theorem step_end (rest output : List Bool) (last register : Option Bool) :
    TM2.step program
      ⟨some again, (ambient, last, register),
        tapesAt source destination base (false :: rest) output⟩ =
      some ⟨if last.getD true then accepted else rejected, clean ambient,
        tapesAt source destination base rest output⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atScan]
  cases h : last.getD true <;>
    simp [scan, TM2.stepAux, distinct, update_source_inline_MachineBinaryNameMachine, h]

theorem step_truncated (output : List Bool) (last register : Option Bool) :
    TM2.step program
      ⟨some again, (ambient, last, register), tapesAt source destination base [true] output⟩ =
      some ⟨rejected, clean ambient, tapesAt source destination base [] output⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atScan]
  simp [scan, TM2.stepAux, distinct, update_source_inline_MachineBinaryNameMachine]

theorem step_digit (bit : Bool) (rest output : List Bool) (last register : Option Bool) :
    TM2.step program
      ⟨some again, (ambient, last, register),
        tapesAt source destination base (true :: bit :: rest) output⟩ =
      some ⟨some again, (ambient, some bit, none),
        tapesAt source destination base rest (bit :: output)⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atScan]
  simp [scan, TM2.stepAux, distinct, update_source_inline_MachineBinaryNameMachine, update_destination_inline_MachineBinaryNameMachine]

theorem scanTrace (input output : List Bool) (last register : Option Bool) :
    (advance (TM2.step program))^[steps input]
      (some ⟨some again, (ambient, last, register),
        tapesAt source destination base input output⟩) =
      some ⟨if (scanSpec input output last).accepted then accepted else rejected,
        clean ambient, tapesAt source destination base
          (scanSpec input output last).remaining (scanSpec input output last).reversedPayload⟩ := by
  induction input using List.twoStepInduction generalizing output last register with
  | nil =>
      simpa only [steps, scanSpec, Bool.false_eq_true, ite_false,
        Function.iterate_one, advance_some] using
        step_empty source destination distinct again accepted rejected program atScan base ambient
          output last register
  | singleton flag =>
      cases flag
      · have h := step_end source destination distinct again accepted rejected program atScan
          base ambient [] output last register
        cases hlast : last.getD true <;>
          simpa [steps, scanSpec, hlast] using h
      · simpa only [steps, scanSpec, Bool.false_eq_true, ite_false,
          Function.iterate_one, advance_some] using
          step_truncated source destination distinct again accepted rejected program atScan base ambient
            output last register
  | cons_cons flag bit rest ih _ =>
      cases flag
      · have h := step_end source destination distinct again accepted rejected program atScan
          base ambient (bit :: rest) output last register
        cases hlast : last.getD true <;>
          simpa [steps, scanSpec, hlast] using h
      · rw [steps, Function.iterate_succ_apply]
        simp only [advance_some]
        rw [step_digit source destination distinct again accepted rejected program atScan]
        exact ih (bit :: output) (some bit) none

theorem framedTrace (bits suffix output : List Bool) (register : Option Bool) :
    (advance (TM2.step program))^[bits.length + 1]
      (some ⟨some again, (ambient, none, register),
        tapesAt source destination base (frame bits ++ suffix) output⟩) =
      some ⟨if canonical bits then accepted else rejected, clean ambient,
        tapesAt source destination base suffix (bits.reverse ++ output)⟩ := by
  have h := scanTrace source destination distinct again accepted rejected program atScan
    base ambient (frame bits ++ suffix) output none register
  cases hlast : (finalDigit bits none).getD true <;>
    simpa [steps_frame, scanSpec_frame, canonical, hlast] using h

end Program

end DFVSGames.BinaryNameMachine


namespace DFVSGames.BinaryParsing

open BinaryEncoding BinaryFormula

theorem frame_eq (bits : List Bool) : BinaryNameMachine.frame bits = frame bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [BinaryNameMachine.frame, frame, ih]

theorem canonical_iff (bits : List Bool) :
    BinaryNameMachine.canonical bits = true ↔ (bitsValue bits).bits = bits := by
  induction bits with
  | nil => simp [BinaryNameMachine.canonical, BinaryNameMachine.finalDigit, bitsValue]
  | cons bit bits ih =>
      cases bits with
      | nil => cases bit <;> decide
      | cons next bits =>
          rw [canonical_cons_cons, ih]
          constructor
          · intro htail
            have hn : bitsValue (next :: bits) ≠ 0 := by
              intro hz
              rw [hz, Nat.zero_bits] at htail
              contradiction
            rw [bitsValue, Nat.bits_append_bit _ bit (fun h => False.elim (hn h)), htail]
          · intro hfull
            calc
              (bitsValue (next :: bits)).bits =
                  (Nat.bit bit (bitsValue (next :: bits))).div2.bits := by rw [Nat.div2_bit]
              _ = (Nat.bit bit (bitsValue (next :: bits))).bits.tail :=
                Nat.div2_bits_eq_tail _
              _ = (bit :: next :: bits).tail := congrArg List.tail hfull
              _ = next :: bits := rfl

@[simp] theorem canonical_nat_bits (name : Nat) :
    BinaryNameMachine.canonical name.bits = true := by
  apply (canonical_iff _).mpr
  rw [bitsValue_bits]

theorem parseFrame_sound (input digits rest : List Bool)
    (parsed : parseFrame input = some (digits, rest)) : input = frame digits ++ rest := by
  induction input using List.twoStepInduction generalizing digits rest with
  | nil => simp [parseFrame] at parsed
  | singleton flag =>
      cases flag
      · simp only [parseFrame, Option.some.injEq, Prod.mk.injEq] at parsed
        rcases parsed with ⟨rfl, rfl⟩
        rfl
      · simp [parseFrame] at parsed
  | cons_cons flag bit input ih _ =>
      cases flag
      · simp only [parseFrame, Option.some.injEq, Prod.mk.injEq] at parsed
        rcases parsed with ⟨rfl, rfl⟩
        rfl
      · cases h : parseFrame input with
        | none => simp [parseFrame, h] at parsed
        | some pair =>
            rcases pair with ⟨ds, tail⟩
            have hs := ih ds tail h
            simp [parseFrame, h] at parsed
            rcases parsed with ⟨rfl, rfl⟩
            simp [frame, hs]

theorem parseName_sound (input : List Bool) (name : Nat) (rest : List Bool)
    (parsed : parseName input = some (name, rest)) : input = nameBits name ++ rest := by
  cases h : parseFrame input with
  | none => simp [parseName, h] at parsed
  | some pair =>
      rcases pair with ⟨digits, tail⟩
      by_cases canonical : digits = (bitsValue digits).bits
      · simp only [parseName, h, Option.bind_eq_bind, Option.bind_some] at parsed
        rw [ite_eq_left canonical] at parsed
        simp only [Option.some.injEq, Prod.mk.injEq] at parsed
        rcases parsed with ⟨rfl, rfl⟩
        have hs := parseFrame_sound input digits tail h
        exact hs.trans (congrArg (fun ds => frame ds ++ tail) canonical)
      · simp only [parseName, h, Option.bind_eq_bind, Option.bind_some, ite_eq_right canonical] at parsed
        cases parsed

theorem parseLiteral_sound (input : List Bool) (literal : Literal) (rest : List Bool)
    (parsed : parseLiteral input = some (literal, rest)) :
    input = literalBits literal ++ rest := by
  cases input with
  | nil => simp [parseLiteral] at parsed
  | cons sign input =>
      cases h : parseName input with
      | none => simp [parseLiteral, h] at parsed
      | some pair =>
          rcases pair with ⟨name, tail⟩
          have hs := parseName_sound input name tail h
          simp [parseLiteral, h] at parsed
          rcases parsed with ⟨rfl, rfl⟩
          simp [literalBits, hs]

theorem parseClause_sound (input : List Bool) (clause : Clause) (rest : List Bool)
    (parsed : parseClause input = some (clause, rest)) : input = clauseBits clause ++ rest := by
  cases ha : parseLiteral input with
  | none => simp [parseClause, ha] at parsed
  | some first =>
      rcases first with ⟨a, afterA⟩
      cases hb : parseLiteral afterA with
      | none => simp [parseClause, ha, hb] at parsed
      | some second =>
          rcases second with ⟨b, afterB⟩
          cases hc : parseLiteral afterB with
          | none => simp [parseClause, ha, hb, hc] at parsed
          | some third =>
              rcases third with ⟨c, afterC⟩
              have hA := parseLiteral_sound input a afterA ha
              have hB := parseLiteral_sound afterA b afterB hb
              have hC := parseLiteral_sound afterB c afterC hc
              have pairEq : (#v[a, b, c], afterC) = (clause, rest) := by
                apply Option.some.inj
                simpa only [parseClause, ha, hb, hc, Option.bind_eq_bind,
                  Option.bind_some, Option.pure_def] using parsed
              rcases Prod.mk.inj pairEq with ⟨rfl, rfl⟩
              simp [clauseBits, hA, hB, hC, List.append_assoc]

theorem parseClauses_sound (fuel : Nat) (input : List Bool)
    (clauses : List Clause) (rest : List Bool)
    (parsed : parseClauses fuel input = some (clauses, rest)) :
    input = clausesBits clauses ++ rest := by
  induction fuel generalizing input clauses rest with
  | zero => simp [parseClauses] at parsed
  | succ fuel ih =>
      cases input with
      | nil => simp [parseClauses] at parsed
      | cons flag input =>
          cases flag
          · simp only [parseClauses, Option.some.injEq, Prod.mk.injEq] at parsed
            rcases parsed with ⟨rfl, rfl⟩
            rfl
          · cases hc : parseClause input with
            | none => simp [parseClauses, hc] at parsed
            | some first =>
                rcases first with ⟨clause, afterClause⟩
                cases hs : parseClauses fuel afterClause with
                | none => simp [parseClauses, hc, hs] at parsed
                | some remaining =>
                    rcases remaining with ⟨cs, tail⟩
                    have hC := parseClause_sound input clause afterClause hc
                    have hS := ih afterClause cs tail hs
                    simp [parseClauses, hc, hs] at parsed
                    rcases parsed with ⟨rfl, rfl⟩
                    simp [clausesBits, hC, hS, List.append_assoc]

theorem decodeFormula_sound (input : List Bool) (formula : Formula)
    (parsed : decodeFormula input = some formula) : input = formulaBits formula := by
  cases h : parseClauses (input.length + 1) input with
  | none => simp [decodeFormula, h] at parsed
  | some pair =>
      rcases pair with ⟨clauses, rest⟩
      by_cases empty : rest = []
      · subst rest
        simp [decodeFormula, h] at parsed
        subst formula
        simpa only [formulaBits, List.append_nil] using
          parseClauses_sound (input.length + 1) input clauses [] h
      · simp [decodeFormula, h, empty] at parsed

end DFVSGames.BinaryParsing


namespace DFVSGames.BinaryOccurrenceRename

open BinaryFormula DFVSGames.Foundations

theorem renamed_satisfiable_iff (F : Formula) : (renamed F).Satisfiable ↔ F.Satisfiable := by
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨extendAssignment F A, ?_⟩
    intro c mem
    have hc : clause F c mem ∈ (renamed F).clauses :=
      List.mem_map.mpr ⟨⟨c, mem⟩, by simp, rfl⟩
    exact (clause_eval_extend F c mem A).symm.trans (hA _ hc)
  · rintro ⟨A, hA⟩
    refine ⟨restrictAssignment F A, ?_⟩
    intro c mem
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp mem
    exact (clause_eval_restrict F original.val original.property A).trans
      (hA original.val original.property)

theorem nat_bits_injective : Function.Injective Nat.bits := by
  intro a b same
  have decoded := congrArg BinaryEncoding.bitsValue same
  simpa only [BinaryEncoding.bitsValue_bits] using decoded

theorem idxOf_binary_payloads (names : List Nat) (name : Nat) :
    (names.map Nat.bits).idxOf name.bits = names.idxOf name := by
  induction names with
  | nil => rfl
  | cons first names ih =>
      by_cases same : first = name
      · subst first
        simp
      · have different : first.bits ≠ name.bits := fun h => same (nat_bits_injective h)
        simp only [List.map_cons, List.idxOf_cons, beq_false_of_ne same,
          beq_false_of_ne different, ih]

theorem renamed_encoding_bound (F : Formula) :
    (Complexity.formulaBits (renamed F)).length ≤
      9 * F.clauses.length * F.clauses.length + 10 * F.clauses.length + 2 := by
  have h := Complexity.formulaBits_length_le (renamed F)
  simp only [renamed_clause_count, renamed_variable_count] at h
  nlinarith

end DFVSGames.BinaryOccurrenceRename


namespace DFVSGames.BinaryLanguage

open DFVSGames.Foundations

def rejectBinary : BinaryFormula.Formula where
  clauses := [#v[⟨0, true⟩, ⟨0, true⟩, ⟨0, true⟩],
    #v[⟨0, false⟩, ⟨0, false⟩, ⟨0, false⟩]]

theorem rejectBinary_unsatisfiable : ¬rejectBinary.Satisfiable := by
  rintro ⟨assignment, satisfied⟩
  have positive := satisfied #v[⟨0, true⟩, ⟨0, true⟩, ⟨0, true⟩]
    (by simp [rejectBinary])
  have negative := satisfied #v[⟨0, false⟩, ⟨0, false⟩, ⟨0, false⟩]
    (by simp [rejectBinary])
  cases h : assignment 0 <;>
    simp [BinaryFormula.Clause.eval, BinaryFormula.Literal.eval, h] at positive negative

def language (input : List Bool) : Prop :=
  ∃ formula, BinaryEncoding.decodeFormula input = some formula ∧ formula.Satisfiable

def totalParsed (input : List Bool) : BinaryFormula.Formula :=
  (BinaryEncoding.decodeFormula input).getD rejectBinary

def totalRename (input : List Bool) : Target.Formula :=
  BinaryOccurrenceRename.renamed (totalParsed input)

theorem totalParsed_satisfiable_iff (input : List Bool) :
    (totalParsed input).Satisfiable ↔ language input := by
  cases parsed : BinaryEncoding.decodeFormula input with
  | none => simp [totalParsed, parsed, rejectBinary_unsatisfiable, language]
  | some formula => simp [totalParsed, parsed, language]

theorem totalRename_satisfiable_iff (input : List Bool) :
    (totalRename input).Satisfiable ↔ language input := by
  exact (BinaryOccurrenceRename.renamed_satisfiable_iff (totalParsed input)).trans
    (totalParsed_satisfiable_iff input)

theorem language_encoded (formula : BinaryFormula.Formula) :
    language (BinaryEncoding.formulaBits formula) ↔ formula.Satisfiable := by
  simp [language]

end DFVSGames.BinaryLanguage


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_Basic
attribute [-instance] _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Games

open scoped BigOperators

noncomputable section

namespace FiniteDistribution

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

def expectation (μ : FiniteDistribution Ω) (f : Ω → ℝ) : ℝ :=
  ∑ x, μ.weight x * f x

end FiniteDistribution

end

end DFVSGames.Foundations.Games


namespace DFVSGames.Foundations.Games
open scoped BigOperators
noncomputable section

namespace Game
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]

def stochasticSuccess (G : Game Q₁ Q₂ A₁ A₂)
    (responses₁ : Q₁ → FiniteDistribution A₁)
    (responses₂ : Q₂ → FiniteDistribution A₂) : ℝ :=
  G.questions.expectation (fun q =>
    (responses₁ q.1).expectation (fun a =>
      (responses₂ q.2).expectation (fun b =>
        if G.accepts q.1 q.2 a b then 1 else 0)))

end Game
end
end DFVSGames.Foundations.Games


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Product
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineLookup

open Turing

variable {K Λ σ : Type} [DecidableEq K]

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

end DFVSGames.Foundations.Complexity.MachineLookup

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineLookupSpec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachinePreservingLookup

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def initialTapes (tape : Fin 5 → K) (base : K → List Bool)
    (index : Nat) (indexSuffix workSuffix output : List Bool) : K → List Bool :=
  MachineLookup.tapes (tape 1) (tape 2) (tape 3) base
    (encodeWord index ++ indexSuffix) workSuffix output

end DFVSGames.Foundations.Complexity.MachinePreservingLookup

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineUnaryAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineHorner

open Turing

variable {K Λ σ : Type} {width : Nat}

def drainLoop (tape : K) (loopLabel : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .pop tape (fun state bit => (state.1, bit))
    (.branch (fun state => state.2.getD false)
      (.goto fun _ => loopLabel)
      (.load (fun state => (state.1, none)) (Reduction.MachineTransfer.exitAt tape exit)))

open scoped BigOperators

end DFVSGames.Foundations.Complexity.MachineHorner

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineProductPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineOdometerInit
open Turing

variable {k : Nat} {K Λ σ : Type} [DecidableEq K]

def digitOutput (tape : Tape k → K) (j : Fin k) (m : Nat) (base : K → List Bool) :
    K → List Bool :=
  Function.update (Function.update base (tape (.current j)) (encodeWord 0))
    (tape (.remaining j)) (encodeWord (m-1))

theorem digitOutput_frame (tape : Tape k → K) (j : Fin k) (m : Nat)
    (base : K → List Bool) (p : K) (hc : p ≠ tape (.current j))
    (hr : p ≠ tape (.remaining j)) : digitOutput tape j m base p = base p := by
  simp [digitOutput,hc,hr]

variable (tape : Tape k → K)
  (distinct : Function.Injective tape)
  (labels : Label k → Λ)
  (exit : Option Λ)
  (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))

def stageTapes (tape : Tape k → K) (m : Nat) (base : K → List Bool) : Nat → K → List Bool
  | 0 => base
  | r+1 => if h : r < k then digitOutput tape ⟨r,h⟩ m (stageTapes tape m base r)
      else stageTapes tape m base r

theorem stageTapes_frame (m : Nat) (base : K → List Bool) (r : Nat)
    (p : K) (hc : ∀j, p ≠ tape (.current j)) (hr : ∀j, p ≠ tape (.remaining j)) :
    stageTapes tape m base r p = base p := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [stageTapes]
    split
    · rw [digitOutput_frame _ _ _ _ _ (hc _) (hr _),ih]
    · exact ih

include distinct in
theorem stageTapes_current (m : Nat) (base : K → List Bool) (r : Nat) (j : Fin k) :
    stageTapes tape m base r (tape (.current j)) =
      if j.val < r then encodeWord 0 else base (tape (.current j)) := by
  induction r with
  | zero => simp [stageTapes]
  | succ r ih =>
    simp only [stageTapes]
    split
    next hr =>
      by_cases hj : j = (⟨r,hr⟩ : Fin k)
      · subst j; simp [digitOutput,distinct.eq_iff]
      · rw [digitOutput_frame _ _ _ _ _
          (distinct.ne (by simpa using hj)) (distinct.ne (by simp)),ih]
        have hval : j.val ≠ r := by intro h; apply hj; exact Fin.ext h
        have he : j.val < r+1 ↔ j.val < r := by omega
        simp only [he]
    next hr =>
      rw [ih]
      have hjr : j.val < r := by omega
      have hjr' : j.val < r+1 := by omega
      simp only [hjr,hjr',ite_true, if_true]

include distinct in
theorem stageTapes_remaining (m : Nat) (base : K → List Bool) (r : Nat) (j : Fin k) :
    stageTapes tape m base r (tape (.remaining j)) =
      if j.val < r then encodeWord (m-1) else base (tape (.remaining j)) := by
  induction r with
  | zero => simp [stageTapes]
  | succ r ih =>
    simp only [stageTapes]
    split
    next hr =>
      by_cases hj : j = (⟨r,hr⟩ : Fin k)
      · subst j; simp [digitOutput]
      · rw [digitOutput_frame _ _ _ _ _
          (distinct.ne (by simp)) (distinct.ne (by simpa using hj)),ih]
        have hval : j.val ≠ r := by intro h; apply hj; exact Fin.ext h
        have he : j.val < r+1 ↔ j.val < r := by omega
        simp only [he]
    next hr =>
      rw [ih]
      have hjr : j.val < r := by omega
      have hjr' : j.val < r+1 := by omega
      simp only [hjr,hjr',ite_true, if_true]

include distinct in
theorem output_current (m : Nat) (base : K → List Bool) (j : Fin k) :
    stageTapes tape m base k (tape (.current j)) = encodeWord 0 := by
  rw [stageTapes_current tape distinct]
  exact ite_eq_left j.isLt

include distinct in
theorem output_remaining (m : Nat) (base : K → List Bool) (j : Fin k) :
    stageTapes tape m base k (tape (.remaining j)) = encodeWord (m-1) := by
  rw [stageTapes_remaining tape distinct]
  exact ite_eq_left j.isLt

end DFVSGames.Foundations.Complexity.MachineOdometerInit

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_FieldArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceFieldArray

open Turing
open DFVSGames.Foundations.Complexity SourceMachine

variable {K Λ σ : Type} [DecidableEq K]

def finish (source : K) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .load (fun state => (state.1, none)) (Reduction.MachineTransfer.exitAt source exit)

end DFVSGames.Foundations.Hastad.SourceFieldArray


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_ContextLoad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceContextLoad

open Turing DFVSGames.Foundations.Complexity
open MachineComposition

variable {u : Nat} {Extra : Type}

variable [DecidableEq Extra]

def stageTapes (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) : Nat → Tape u Extra → List Bool
  | 0 => base
  | r + 1 => if h : r < u then
      coordinateOutput ⟨r, h⟩ F.clauses[(tuple ⟨r, h⟩).val] (stageTapes F tuple base r)
    else stageTapes F tuple base r

omit [DecidableEq Extra] in
theorem stageTapes_frame (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (r : Nat) (p : Tape u Extra)
    (hi : p ≠ .index) (hw : p ≠ .work) (hf : ∀ j s, p ≠ .field j s) :
    stageTapes F tuple base r p = base p := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [stageTapes]
    split
    · cases p <;> simp_all [coordinateOutput]
    · exact ih

end DFVSGames.Foundations.Hastad.SourceContextLoad


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_CloneGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Reduction.CloneGap

variable {Element OtherElement : Type*}

variable {Name : Type}

def satisfied (e : Equation Name) (g : Name → Bool) : Bool :=
  (xor (xor (g e.first) (g e.second)) (g e.third)) == e.rhs

end DFVSGames.Reduction.CloneGap


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_Tape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceContexts

open Target PCP

def honestJ (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (assignment : Fin F.«variables» → Bool) : J u :=
  fun t => honestAnswer (clauseAt F (c t)) assignment

def honestI (F : Formula) {u : ℕ} (v : VariableContext F u)
    (assignment : Fin F.«variables» → Bool) : I u :=
  fun t => assignment (v t)

end DFVSGames.Foundations.Hastad.SourceContexts


namespace DFVSGames.Reduction.SourceEncoding

open DFVSGames.Foundations.Complexity

def inputBits (input : Input) : List Bool := encodeWords (inputWords input)

end DFVSGames.Reduction.SourceEncoding

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_TestEmit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineTupleOdometer

open Turing
open Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K]

def increment (current remaining : K) (doneLabel resetLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .peek remaining (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.pop remaining (fun state _ => (state.1, none))
        (.push current (fun _ => true) (.goto fun _ => doneLabel)))
      (.load (fun state => (state.1, none)) (.goto fun _ => resetLabel)))

def reset (current remaining : K) (resetLabel carryLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  MachineUnaryAddAt.loop current remaining resetLabel (some carryLabel)

open scoped BigOperators

end DFVSGames.Foundations.Complexity.MachineTupleOdometer

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_TupleOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.Complexity.MachineTupleOdometer
open Turing
open Reduction.MachineTransfer
variable {K Λ σ : Type} [DecidableEq K]
section Order
omit [DecidableEq K]
open scoped BigOperators

theorem tupleOrder_dimension_zero (n : ℕ) :
    tupleOrder n 0 = [fun i => Fin.elim0 i] := by
  simp only [tupleOrder, pow_zero, List.ofFn_succ, List.ofFn_zero, List.cons.injEq,
    and_true]
  funext i
  exact Fin.elim0 i

theorem tupleOrder_snoc (n q : ℕ) :
    tupleOrder n (q + 1) = (List.ofFn (fun d : Fin n => d)).flatMap
      (fun d => (tupleOrder n q).map (fun tail => Fin.snoc tail d)) := by
  rw [tupleOrder, List.ofFn_congr (Nat.pow_succ n q), List.ofFn_mul']
  simp only [tupleOrder, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext d
  apply congrArg List.ofFn
  funext rank
  dsimp only [Function.comp_apply]
  apply finFunctionFinEquiv.injective
  apply Fin.ext
  rw [Equiv.apply_symm_apply, tupleRank_snoc, Equiv.apply_symm_apply]
  simp [Nat.mul_comm, Nat.add_comm]

end Order


end DFVSGames.Foundations.Complexity.MachineTupleOdometer


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_FinishReduction
attribute [-instance] _root_.OAI.DFVSGames.Soundness.PartnerLinear.partnerAddCommGroup _root_.OAI.DFVSGames.Soundness.PartnerLinear.partnerModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Soundness.PartnerProjection

def addTriple (x y : Triple) : Triple :=
  ⟨x.first.xor y.first, x.second.xor y.second, x.third.xor y.third⟩

theorem parity_add (x y : Triple) :
    parity (addTriple x y) = (parity x).xor (parity y) := by
  rcases x with ⟨a, b, c⟩
  rcases y with ⟨d, e, f⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

theorem retained_add (s : Slot) (x y : Triple) :
    retained s (addTriple x y) = (retained s x).xor (retained s y) := by
  cases s <;> rfl

theorem retained_zero (s : Slot) : retained s zeroTriple = false := by
  cases s <;> rfl

variable {Position : Type} (rhs active : Position → Bool) (slot : Position → Slot)

structure SourcePoint where
  homogeneous : Bool
  coordinates : Position → Triple
  valid : ∀ j, parity (coordinates j) = (rhs j && homogeneous)

theorem source_ext {x y : SourcePoint rhs}
    (hh : x.homogeneous = y.homogeneous) (hx : x.coordinates = y.coordinates) : x = y := by
  cases x
  cases y
  cases hh
  cases hx
  rfl

def project (x : SourcePoint rhs) : PartnerPoint rhs active where
  homogeneous := x.homogeneous
  full := fun j => if active j then zeroTriple else x.coordinates j
  single := fun j => if active j then retained (slot j) (x.coordinates j) else false
  full_zero := by intro j hj; simp [hj]
  full_valid := by intro j hj; simpa [hj] using x.valid j
  single_zero := by intro j hj; simp [hj]

def zeroSource : SourcePoint rhs where
  homogeneous := false
  coordinates := fun _ => zeroTriple
  valid := by intro j; simp [parity, zeroTriple]

def zeroPartner : PartnerPoint rhs active where
  homogeneous := false
  full := fun _ => zeroTriple
  single := fun _ => false
  full_zero := by intros; rfl
  full_valid := by intros; simp [parity, zeroTriple]
  single_zero := by intros; rfl

def addSource (x y : SourcePoint rhs) : SourcePoint rhs where
  homogeneous := x.homogeneous.xor y.homogeneous
  coordinates := fun j => addTriple (x.coordinates j) (y.coordinates j)
  valid := by
    intro j
    rw [parity_add, x.valid, y.valid, and_xor]

def addPartner (x y : PartnerPoint rhs active) : PartnerPoint rhs active where
  homogeneous := x.homogeneous.xor y.homogeneous
  full := fun j => addTriple (x.full j) (y.full j)
  single := fun j => (x.single j).xor (y.single j)
  full_zero := by
    intro j hj
    rw [x.full_zero j hj, y.full_zero j hj]
    rfl
  full_valid := by
    intro j hj
    rw [parity_add, x.full_valid j hj, y.full_valid j hj, and_xor]
  single_zero := by
    intro j hj
    rw [x.single_zero j hj, y.single_zero j hj]
    rfl

theorem project_add (x y : SourcePoint rhs) :
    project rhs active slot (addSource rhs x y) =
      addPartner rhs active (project rhs active slot x) (project rhs active slot y) := by
  apply partner_ext
  · rfl
  · funext j
    cases hj : active j <;> simp [project, addSource, addPartner, hj, addTriple, zeroTriple]
  · funext j
    cases hj : active j <;> simp [project, addSource, addPartner, hj, retained_add]

theorem project_zero :
    project rhs active slot (zeroSource rhs) = zeroPartner rhs active := by
  apply partner_ext
  · rfl
  · funext j
    cases active j <;> simp [project, zeroSource, zeroPartner]
  · funext j
    cases active j <;> simp [project, zeroSource, zeroPartner, retained_zero]

end DFVSGames.Soundness.PartnerProjection

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KernelCardinality
attribute [-instance] _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Soundness.PartnerLinear

open PartnerProjection
open DFVSGames.Integration.BinaryLinear (F2 ofBit toBit scalar_cases ofBit_toBit
  toBit_ofBit ofBit_xor)

variable {P : Type} (rhs active : P → Bool) (slot : P → Slot)

abbrev SourceCoordinates (P : Type) := F2 × (P → F2 × F2)

def sourceCoordinates (x : SourcePoint rhs) : SourceCoordinates P :=
  (ofBit x.homogeneous, fun j => (ofBit (x.coordinates j).first, ofBit (x.coordinates j).second))

def sourceFromCoordinates (v : SourceCoordinates P) : SourcePoint rhs where
  homogeneous := toBit v.1
  coordinates := fun j => complete .first (rhs j && toBit v.1)
    (toBit (v.2 j).1) (toBit (v.2 j).2)
  valid := by intro j; exact parity_complete _ _ _ _

def sourceEquiv : SourcePoint rhs ≃ SourceCoordinates P where
  toFun := sourceCoordinates rhs
  invFun := sourceFromCoordinates rhs
  left_inv x := by
    apply source_ext rhs
    · exact toBit_ofBit _
    · funext j
      change complete .first (rhs j && toBit (ofBit x.homogeneous))
        (toBit (ofBit (x.coordinates j).first))
        (toBit (ofBit (x.coordinates j).second)) = x.coordinates j
      simp only [toBit_ofBit, ← x.valid j]
      exact complete_coordinates .first (x.coordinates j)
  right_inv v := by
    apply Prod.ext
    · exact ofBit_toBit _
    · funext j
      apply Prod.ext <;> exact ofBit_toBit _

noncomputable instance sourceAddCommGroup : AddCommGroup (SourcePoint rhs) :=
  (sourceEquiv rhs).addCommGroup

noncomputable instance sourceModule : Module F2 (SourcePoint rhs) :=
  (sourceEquiv rhs).addEquiv.module F2

noncomputable def sourceLinearEquiv : SourcePoint rhs ≃ₗ[F2] SourceCoordinates P :=
  (sourceEquiv rhs).addEquiv.linearEquiv F2

theorem source_add (x y : SourcePoint rhs) : x + y = addSource rhs x y := by
  apply (sourceEquiv rhs).injective
  change sourceEquiv rhs ((sourceEquiv rhs).symm (sourceEquiv rhs x + sourceEquiv rhs y)) = _
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · exact (ofBit_xor _ _).symm
  · funext j
    apply Prod.ext <;> exact (ofBit_xor _ _).symm

theorem source_zero : (0 : SourcePoint rhs) = zeroSource rhs := by
  apply (sourceEquiv rhs).injective
  change sourceEquiv rhs ((sourceEquiv rhs).symm 0) = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem partner_add (x y : PartnerPoint rhs active) : x + y = addPartner rhs active x y := by
  apply (partnerEquiv rhs active).injective
  change partnerEquiv rhs active ((partnerEquiv rhs active).symm
    (partnerEquiv rhs active x + partnerEquiv rhs active y)) = _
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · exact (ofBit_xor _ _).symm
  · apply Prod.ext
    · funext j
      apply Prod.ext <;> exact (ofBit_xor _ _).symm
    · funext j
      exact (ofBit_xor _ _).symm

theorem partner_zero : (0 : PartnerPoint rhs active) = zeroPartner rhs active := by
  apply (partnerEquiv rhs active).injective
  change partnerEquiv rhs active ((partnerEquiv rhs active).symm 0) = _
  rw [Equiv.apply_symm_apply]
  rfl

noncomputable def projection : SourcePoint rhs →ₗ[F2] PartnerPoint rhs active where
  toFun := project rhs active slot
  map_add' x y := by rw [source_add, partner_add]; exact project_add rhs active slot x y
  map_smul' c x := by
    rcases scalar_cases c with rfl | rfl
    · change project rhs active slot ((0 : F2) • x) = (0 : F2) • project rhs active slot x
      rw [zero_smul, zero_smul, source_zero, partner_zero, project_zero]
    · simp

end DFVSGames.Soundness.PartnerLinear


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ConditionalIncidences
attribute [-instance] _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped BigOperators

namespace DFVSGames.Soundness.ConditionalIncidences

noncomputable section

abbrev RawCoefficients {P : Type} (J : Finset P) (D : Type) := RawSlot J → D

end

end DFVSGames.Soundness.ConditionalIncidences
end

section

open scoped BigOperators

namespace DFVSGames.Soundness.PartnerMapCoordinates

open PartnerProjection
open ConditionalIncidences (PositionInside PositionOutside RawSlot RawCoefficients )
open DFVSGames.Integration.BinaryLinear (F2 ofBit toBit)

noncomputable section

variable {P : Type} [DecidableEq P] (rhs : P → Bool) (J : Finset P)

variable [Fintype P]

def partnerBasis : Module.Basis (RawSlot J) F2 (PartnerPoint rhs (activeOf J)) :=
  Module.Basis.ofEquivFun (pointEquiv rhs J)

variable (R : Type) [AddCommGroup R] [Module F2 R]

def mapEquiv : RawCoefficients J R ≃ₗ[F2] (PartnerPoint rhs (activeOf J) →ₗ[F2] R) :=
  (partnerBasis rhs J).constr F2

theorem mapEquiv_apply (gamma : RawCoefficients J R) (y : PartnerPoint rhs (activeOf J)) :
    mapEquiv rhs J R gamma y = ∑ s, pointEquiv rhs J y s • gamma s := by
  rw [mapEquiv, Module.Basis.constr_apply_fintype]
  simp only [partnerBasis, Module.Basis.equivFun_ofEquivFun]

end

end DFVSGames.Soundness.PartnerMapCoordinates
end

namespace DFVSGames.Soundness.ConcreteExtraction

open PartnerProjection IncidenceExtraction

def slotIndex : PartnerProjection.Slot → Fin 3
  | .first => 0
  | .second => 1
  | .third => 2

def tripleCoordinates (x : PartnerProjection.Triple) : IncidenceExtraction.Triple :=
  fun i => if i = 0 then x.first else if i = 1 then x.second else x.third

end DFVSGames.Soundness.ConcreteExtraction

namespace DFVSGames.Reduction.ActualHomogeneous

open Integration.BinaryLinear
open scoped BigOperators

variable {k : Nat}

theorem finrank_E (k : Nat) : Module.finrank F2 (E k) = 1 + 2 * k := by
  simp [E, Module.finrank_prod, Module.finrank_pi_fintype, Nat.mul_comm]

end DFVSGames.Reduction.ActualHomogeneous

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ActualCanonical
attribute [-instance] _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.ConditionalSimulation.firstInputFintype _root_.OAI.DFVSGames.Soundness.ConditionalSimulation.secondInputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Reduction.ActualCanonical

open Integration.BinaryLinear ActualHomogeneous
open scoped BigOperators

universe u v w
variable {k : Nat}
variable {Name : Type u} {Id : Type v} {R : Type w}
variable [AddCommGroup R] [Module F2 R] [DecidableEq R]

omit [DecidableEq R] in
theorem add_self (x : R) : x + x = 0 := by
  calc
    x + x = (1 + 1 : F2) • x := by simp [add_smul]
    _ = 0 := by rw [show (1 + 1 : F2) = 0 by decide, zero_smul]

end DFVSGames.Reduction.ActualCanonical

namespace DFVSGames.Soundness.RawPartnerTarget
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open PartnerProjection PartnerMapCoordinates ConditionalIncidences

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : Nat} {R : Type} [AddCommGroup R] [Module F2 R]

def rawProjection (rhsB : Fin k → Bool) (J : Finset (Fin k))
    (slot : Fin k → Slot) : ActualHomogeneous.E k →ₗ[F2] RawPoint J :=
  (pointEquiv rhsB J).toLinearMap.comp
    ((PartnerLinear.projection rhsB (activeOf J) slot).comp
      (PartnerLinear.sourceLinearEquiv rhsB).symm.toLinearMap)

def gammaOfRawMap (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] R) :
    RawCoefficients J R := fun s => Y (Pi.single s 1)

theorem rawPoint_decomposition (J : Finset (Fin k)) (v : RawPoint J) :
    (∑ s, v s • Pi.single s (1 : F2)) = v := by
  funext t
  simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul, mul_ite]

theorem rawMap_expansion (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] R)
    (v : RawPoint J) : Y v = ∑ s, v s • gammaOfRawMap J Y s := by
  calc
    Y v = Y (∑ s, v s • Pi.single s (1 : F2)) :=
      congrArg Y (rawPoint_decomposition J v).symm
    _ = _ := by simp [gammaOfRawMap]

theorem rawMap_on_partner (rhsB : Fin k → Bool) (J : Finset (Fin k))
    (Y : RawPoint J →ₗ[F2] R) (y : PartnerPoint rhsB (activeOf J)) :
    Y (pointEquiv rhsB J y) = mapEquiv rhsB J R (gammaOfRawMap J Y) y := by
  rw [mapEquiv_apply]
  exact rawMap_expansion J Y (pointEquiv rhsB J y)

end
end DFVSGames.Soundness.RawPartnerTarget

namespace DFVSGames.Soundness.ConditionalIncidences

noncomputable section

def fullCoefficient {P R : Type} [DecidableEq P] (J : Finset P)
    (gamma : RawCoefficients J (ZeroInformation.Bits R)) (i : Fin 2) :
    P → ZeroInformation.Bits R :=
  fun j => if hj : j ∉ J then gamma (some (.inl (⟨j, hj⟩, i))) else ZeroInformation.zero

def singleCoefficient {P R : Type} [DecidableEq P] (J : Finset P)
    (gamma : RawCoefficients J (ZeroInformation.Bits R)) : P → ZeroInformation.Bits R :=
  fun j => if hj : j ∈ J then gamma (some (.inr ⟨j, hj⟩)) else ZeroInformation.zero

variable {P R O N : Type}
  [Fintype P]
  [DecidableEq P]
  [Fintype R]
  [DecidableEq R]
  (J : Finset P)
  (name : O → Fin 3 → N)
  (gamma : RawCoefficients J (ZeroInformation.Bits R))

def actualFirst (sample : Draw P O) : ZeroInformation.FirstInput P R O :=
  ZeroInformation.firstInput Finset.univ.toList (membershipBool J) (gamma none)
    (fullCoefficient J gamma 0) (fullCoefficient J gamma 1) (singleCoefficient J gamma)
    (fun j => (sample j).1) (fun j => (sample j).2)

def actualSecond (sample : Draw P O) : ZeroInformation.SecondInput P R O N :=
  ZeroInformation.secondInput Finset.univ.toList (membershipBool J) (gamma none)
    (fullCoefficient J gamma 0) (fullCoefficient J gamma 1) (singleCoefficient J gamma)
    (fun j => (sample j).1) (fun j => name (sample j).1 (sample j).2)

end

end DFVSGames.Soundness.ConditionalIncidences

namespace DFVSGames.Soundness.BinaryRowTransport
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear
open ConditionalIncidences PartnerMapCoordinates

noncomputable section
attribute [local instance] Classical.propDecidable
variable {Q : Type}

def rowBits (v : Q → F2) : ZeroInformation.Bits Q := fun q => toBit (v q)

def rowBitsEquiv : (Q → F2) ≃ ZeroInformation.Bits Q where
  toFun := rowBits
  invFun v := fun q => ofBit (v q)
  left_inv v := by funext q; exact ofBit_toBit _
  right_inv v := by funext q; exact toBit_ofBit _

def rowCoefficients {P : Type} (J : Finset P) (gamma : RawCoefficients J (Q → F2)) :
    RawCoefficients J (ZeroInformation.Bits Q) := fun slot => rowBits (gamma slot)

end
end DFVSGames.Soundness.BinaryRowTransport

namespace DFVSGames.Soundness.RawMapLaw
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear
open ConditionalIncidences PartnerMapCoordinates RawPartnerTarget BinaryRowTransport

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : Nat} (J : Finset (Fin k)) (R : Type) [AddCommGroup R] [Module F2 R]

def rawMap (gamma : RawCoefficients J R) : RawPoint J →ₗ[F2] R :=
  (mapEquiv (fun _ : Fin k => false) J R gamma).comp
    (pointEquiv (fun _ : Fin k => false) J).symm.toLinearMap

theorem coefficients_rawMap (gamma : RawCoefficients J R) :
    gammaOfRawMap J (rawMap J R gamma) = gamma := by
  apply (mapEquiv (fun _ : Fin k => false) J R).injective
  apply LinearMap.ext
  intro y
  rw [← rawMap_on_partner]
  change mapEquiv (fun _ : Fin k => false) J R gamma
    ((pointEquiv (fun _ : Fin k => false) J).symm
      (pointEquiv (fun _ : Fin k => false) J y)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem rawMap_coefficients (Y : RawPoint J →ₗ[F2] R) :
    rawMap J R (gammaOfRawMap J Y) = Y := by
  apply LinearMap.ext
  intro v
  have h := rawMap_on_partner (fun _ : Fin k => false) J Y
    ((pointEquiv (fun _ : Fin k => false) J).symm v)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

def rawMapEquiv : RawCoefficients J R ≃ (RawPoint J →ₗ[F2] R) where
  toFun := rawMap J R
  invFun := gammaOfRawMap J
  left_inv := coefficients_rawMap J R
  right_inv := rawMap_coefficients J R

instance rawMapsFintype [Fintype R] : Fintype (RawPoint J →ₗ[F2] R) := by
  classical
  exact Fintype.ofEquiv (RawCoefficients J R) (rawMapEquiv J R)

end
end DFVSGames.Soundness.RawMapLaw

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Explicit
attribute [-instance] _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Reduction.ActualEnumeration

open Integration.BinaryLinear
open ActualHomogeneous
open _root_.OAI.DFVSGames.Reduction.Explicit
open scoped BigOperators

variable {α β N : Type*} {n m k s d noiseCount : Nat}

theorem nodup_pairs {xs : List α} {ys : List β} (hx : xs.Nodup) (hy : ys.Nodup) :
    (pairs xs ys).Nodup := hx.product hy

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

theorem nodup_allLinearMaps {values : List R} (distinct : values.Nodup) :
    (allLinearMaps k R values).Nodup :=
  (nodup_pairs distinct (nodup_functions (nodup_pairs distinct distinct) k)).map
    (coefficientEquiv k R).injective

end Coefficients

theorem nodup_vectors (s : Nat) : (vectors s).Nodup :=
  (List.nodup_finRange _).map (Encoding.alphabetEquiv s).symm.injective

theorem nodup_ambientVectors (s d : Nat) : (ambientVectors s d).Nodup :=
  nodup_pairs (nodup_vectors s) (nodup_vectors d)

theorem nodup_queries (m k s d : Nat) : (queries m k s d).Nodup :=
  nodup_pairs (nodup_functions (List.nodup_finRange _) _)
    (nodup_allLinearMaps k _ (nodup_ambientVectors s d))

theorem nodup_indexedOutcomes {indices : List N} (distinct : indices.Nodup)
    (m k s d : Nat) : (indexedOutcomes m k s d indices).Nodup :=
  nodup_pairs (nodup_queries m k s d)
    (nodup_pairs distinct (nodup_allLinearMaps k F2 (by simp)))

end DFVSGames.Reduction.ActualEnumeration


namespace DFVSGames.Decoder.PaddedLaw

open scoped BigOperators
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open DFVSGames.Soundness
open ConditionalIncidences PartnerProjection RawPartnerTarget RawMapLaw
open SparseLaw

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : ℕ} {V : Type} [AddCommGroup V] [Module F2 V]

def decodeSlot (i : Fin 3) : Slot :=
  if i = 0 then .first else if i = 1 then .second else .third

def blockThird (d : BlockDraw V) : V := blockAmbient d 2

def singletonPositions (d : Fin k → BlockDraw V) : Finset (Fin k) :=
  Finset.univ.filter fun j => (d j).isRight

def drawSlots (d : Fin k → BlockDraw V) (j : Fin k) : Slot :=
  match d j with
  | .inl _ => .first
  | .inr ia => decodeSlot ia.1

def drawCoefficients (d : Fin k → BlockDraw V) (z : V) :
    RawCoefficients (singletonPositions d) V
  | none => z
  | some (.inl (j, i)) =>
      match d j.val with
      | .inl ab => if i = 0 then ab.1 else ab.2
      | .inr _ => 0
  | some (.inr j) =>
      match d j.val with
      | .inl _ => 0
      | .inr ia => ia.2

def paddedMap (rhs : Fin k → Bool) (d : Fin k → BlockDraw V) (z : V) :
    ActualHomogeneous.E k →ₗ[F2] V :=
  (rawMap (singletonPositions d) V (drawCoefficients d z)).comp
    (rawProjection rhs (singletonPositions d) (drawSlots d))


variable [Fintype V]

def blockWeights (β : ℝ) : BlockDraw V → ℝ
  | .inl ab => (1 - β) * uniformWeights (V × V) ab
  | .inr ia => (β / 3) * uniformWeights V ia.2

omit [Module F2 V] in
theorem blockWeights_isProbability (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    DFVSGames.Foundations.Information.IsProbability (blockWeights (V := V) β) := by
  constructor
  · intro d
    cases d with
    | inl ab => exact mul_nonneg (sub_nonneg.mpr hβ') (uniformWeights_pos ab).le
    | inr ia => exact mul_nonneg (div_nonneg hβ (by norm_num)) (uniformWeights_pos ia.2).le
  · rw [Fintype.sum_sum_type]
    simp only [blockWeights, ← Finset.mul_sum,
      (uniformWeights_isProbability (α := V × V)).2, mul_one, Fintype.sum_prod_type,
      (uniformWeights_isProbability (α := V)).2]
    simp

def drawWeights (β : ℝ) (k : ℕ) : ((Fin k → BlockDraw V) × V) → ℝ :=
  fun dz => independentWeights (blockWeights β) k dz.1 * uniformWeights V dz.2

def choiceWeight (β : ℝ) : ProjectionChoice → ℝ
  | none => 1 - β
  | some _ => β / 3

theorem choiceWeight_isProbability (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    DFVSGames.Foundations.Information.IsProbability (choiceWeight β) := by
  constructor
  · intro c
    cases c with
    | none => exact sub_nonneg.mpr hβ'
    | some i => exact div_nonneg hβ (by norm_num)
  · rw [Fintype.sum_option]
    simp [choiceWeight]
    ring

def choiceTupleWeight (β : ℝ) (c : Fin k → ProjectionChoice) : ℝ :=
  ∏ j, choiceWeight β (c j)

theorem choiceTupleWeight_isProbability (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    DFVSGames.Foundations.Information.IsProbability (choiceTupleWeight (k := k) β) := by
  exact independentWeights_isProbability (choiceWeight β)
    (choiceWeight_isProbability β hβ hβ') k

def choiceSlot : ProjectionChoice → Slot
  | none => .first
  | some i => decodeSlot i

def choiceSlots (c : Fin k → ProjectionChoice) (j : Fin k) : Slot :=
  choiceSlot (c j)


end
end DFVSGames.Decoder.PaddedLaw

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_RawPrivateTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Soundness.RawPrivateTable
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open PartnerProjection RawPartnerTarget

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : Nat} {Id Name : Type}

abbrev Extension (k : Nat) (Id : Type) := (Fin k → Id) × (Fin k → Slot)

def displayed (J : Finset (Fin k)) (names : Id → Fin 3 → Name)
    (occ : Fin k → Id) (slot : Fin k → Slot) : Fin k → Sum Id Name :=
  fun j => if j ∈ J then
    Sum.inr (names (occ j) (ConcreteExtraction.slotIndex (slot j)))
  else Sum.inl (occ j)

def SupportedV (J : Finset (Fin k)) (names : Id → Fin 3 → Name) : Type :=
  { V : Fin k → Sum Id Name //
      V ∈ Set.range (fun e : Extension k Id => displayed J names e.1 e.2) }

def representative {J : Finset (Fin k)} {names : Id → Fin 3 → Name}
    (V : SupportedV J names) : Extension k Id := Classical.choose V.property

def supported (J : Finset (Fin k)) (names : Id → Fin 3 → Name)
    (occ : Fin k → Id) (slot : Fin k → Slot) : SupportedV J names :=
  ⟨displayed J names occ slot, ⟨(occ, slot), rfl⟩⟩

variable (J : Finset (Fin k)) (names : Id → Fin 3 → Name) (rhs : Id → F2)
  {R D C Label : Type} [AddCommGroup R] [Module F2 R] [DecidableEq R]
  [AddCommGroup D] [Module F2 D] [AddCommGroup C] [Module F2 C]
  [DecidableEq Id] [DecidableEq Name]

def projection (occ : Fin k → Id) (slot : Fin k → Slot) :
    ActualHomogeneous.E k →ₗ[F2] RawPoint J :=
  rawProjection (fun j => toBit (rhs (occ j))) J slot

end
end DFVSGames.Soundness.RawPrivateTable


namespace DFVSGames.Decoder.TableKeys

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open DFVSGames.Soundness
open scoped BigOperators

universe u v w


variable {Name Id R : Type} [AddCommGroup R] [Module F2 R] [DecidableEq R]
variable {k : Nat}

abbrev Key (k : Nat) (Name Id R : Type) := ActualCanonical.Data k Name Id R

def key (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (P : ActualHomogeneous.E k →ₗ[F2] R) : Key k Name Id R :=
  ActualCanonical.canonical occ names rhs P

variable [DecidableEq Name] [DecidableEq Id]

noncomputable def projectedKey (J : Finset (Fin k)) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (Q : RawPrivateTable.SupportedV J names) (Y : RawPartnerTarget.RawPoint J →ₗ[F2] R) :
    Key k Name Id R :=
  key (RawPrivateTable.representative Q).1 names rhs
    (Y.comp (RawPrivateTable.projection J rhs (RawPrivateTable.representative Q).1
      (RawPrivateTable.representative Q).2))


end DFVSGames.Decoder.TableKeys


namespace DFVSGames.Decoder.TableKeys

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open DFVSGames.Soundness

variable {Name Id R : Type} [AddCommGroup R] [Module F2 R]
variable {k : Nat}

def visibleTau (J : Finset (Fin k)) : RawPartnerTarget.RawPoint J →ₗ[F2] F2 :=
  LinearMap.proj none

end DFVSGames.Decoder.TableKeys


namespace DFVSGames.Decoder.AdviceExperiment

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open DFVSGames.Soundness

noncomputable section

variable (k : Nat) (Id K W R : Type)
variable [AddCommGroup K] [Module F2 K]
variable [AddCommGroup W] [Module F2 W]
variable [AddCommGroup R] [Module F2 R]

structure FullAdvice where
  occurrences : Fin k → Id
  rowMap : K →ₗ[F2] R
  complement : ActualHomogeneous.E k →ₗ[F2] W
  rows : ActualHomogeneous.E k →ₗ[F2] R

structure Draw where
  singletons : Finset (Fin k)
  occurrences : Fin k → Id
  positions : Fin k → PartnerProjection.Slot
  rowMap : K →ₗ[F2] R
  hiddenMatrix : RawPartnerTarget.RawPoint singletons →ₗ[F2] K
  complement : RawPartnerTarget.RawPoint singletons →ₗ[F2] W

variable {k Id K W R}

variable {Name : Type} (names : Id → Fin 3 → Name)

structure ProjectedAdvice (J : Finset (Fin k)) where
  question : RawPrivateTable.SupportedV J names
  rowMap : K →ₗ[F2] R
  complement : RawPartnerTarget.RawPoint J →ₗ[F2] W
  rows : RawPartnerTarget.RawPoint J →ₗ[F2] R

variable (rhs : Id → F2)

def projection (d : Draw k Id K W R) :
    ActualHomogeneous.E k →ₗ[F2] RawPartnerTarget.RawPoint d.singletons :=
  RawPrivateTable.projection d.singletons rhs d.occurrences d.positions

def leftObservation (d : Draw k Id K W R) : FullAdvice k Id K W R where
  occurrences := d.occurrences
  rowMap := d.rowMap
  complement := d.complement.comp (projection rhs d)
  rows := (d.rowMap.comp d.hiddenMatrix).comp (projection rhs d)

def rightObservation (d : Draw k Id K W R) :
    (J : Finset (Fin k)) × ProjectedAdvice (K := K) (W := W) (R := R) names J :=
  ⟨d.singletons, {
    question := RawPrivateTable.supported d.singletons names d.occurrences d.positions
    rowMap := d.rowMap
    complement := d.complement
    rows := d.rowMap.comp d.hiddenMatrix }⟩

def paddedMatrix (d : Draw k Id K W R) : ActualHomogeneous.E k →ₗ[F2] K :=
  d.hiddenMatrix.comp (projection rhs d)

end
end DFVSGames.Decoder.AdviceExperiment


namespace DFVSGames.Clean.AdviceImageLaw

open scoped BigOperators
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Soundness.ConditionalIncidences
open DFVSGames.Soundness.PartnerMapCoordinates
open DFVSGames.Foundations.Games

noncomputable section

attribute [local instance] Classical.propDecidable

variable {K S W : Type} [AddCommGroup K] [Module F2 K]
  [AddCommGroup S] [Module F2 S]

def rangePoint (A : K →ₗ[F2] S) (m : K) : A.range :=
  ⟨A m, ⟨m, rfl⟩⟩

def selectedLift (A : K →ₗ[F2] S) (z : A.range) : K :=
  Classical.choose z.property

theorem selectedLift_spec (A : K →ₗ[F2] S) (z : A.range) :
    A (selectedLift A z) = (z : S) :=
  Classical.choose_spec z.property

theorem rangePoint_lift_add_kernel (A : K →ₗ[F2] S) (z : A.range) (k : A.ker) :
    rangePoint A (selectedLift A z + (k : K)) = z := by
  apply Subtype.ext
  change A (selectedLift A z + (k : K)) = (z : S)
  rw [map_add, selectedLift_spec, k.property, add_zero]

def imageKernelEquiv (A : K →ₗ[F2] S) : K ≃ A.range × A.ker where
  toFun m := (rangePoint A m,
    ⟨m - selectedLift A (rangePoint A m), by
      change A (m - selectedLift A (rangePoint A m)) = 0
      rw [map_sub, selectedLift_spec]
      exact sub_self _⟩)
  invFun p := selectedLift A p.1 + (p.2 : K)
  left_inv m := by
    change selectedLift A (rangePoint A m) + (m - selectedLift A (rangePoint A m)) = m
    rw [add_comm, sub_add_cancel]
  right_inv p := by
    apply Prod.ext
    · exact rangePoint_lift_add_kernel A p.1 p.2
    · apply Subtype.ext
      change selectedLift A p.1 + (p.2 : K) -
        selectedLift A (rangePoint A (selectedLift A p.1 + (p.2 : K))) = (p.2 : K)
      rw [rangePoint_lift_add_kernel]
      exact add_sub_cancel_left _ _

def columnImage (A : K →ₗ[F2] S) (column : W × K) : W × A.range :=
  (column.1, rangePoint A column.2)

def columnSplitEquiv (A : K →ₗ[F2] S) : (W × K) ≃ (W × A.range) × A.ker :=
  (Equiv.prodCongr (Equiv.refl W) (imageKernelEquiv A)).trans
    (Equiv.prodAssoc W A.range A.ker).symm

def visibleCoefficients {I : Type} (A : K →ₗ[F2] S)
    (columns : I → W × K) : I → W × A.range :=
  fun i => columnImage A (columns i)

def coefficientsSplitEquiv (I : Type) (A : K →ₗ[F2] S) :
    (I → W × K) ≃ (I → W × A.range) × (I → A.ker) :=
  (Equiv.piCongrRight fun _ : I => columnSplitEquiv (W := W) A).trans
    (Equiv.arrowProdEquivProdArrow I (fun _ => W × A.range) (fun _ => A.ker))

instance rangeFintype [Fintype S] (A : K →ₗ[F2] S) : Fintype A.range :=
  Fintype.ofFinite _

instance kernelFintype [Fintype K] (A : K →ₗ[F2] S) : Fintype A.ker :=
  Fintype.ofFinite _


end

end DFVSGames.Clean.AdviceImageLaw

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_RepeatedGameBounds
attribute [-instance] _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.ConditionalSimulation.firstInputFintype _root_.OAI.DFVSGames.Soundness.ConditionalSimulation.secondInputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Soundness.RepeatedGameBounds

open scoped BigOperators

noncomputable section

open Foundations.Games

namespace Simulation

variable {QA QB A B OA OB X Y : Type}
  [Fintype QA] [Fintype QB] [Fintype A] [Fintype B]
  [Fintype OA] [Fintype OB] [Fintype X] [Fintype Y]

def weightedGame (G : PredicateGame QA QB A B)
    (questions : FiniteDistribution (QA × QB)) : Game QA QB A B := by
  classical
  exact ⟨questions, fun qa qb a b => decide (G.accepts qa qb a b)⟩

end Simulation

namespace ActualProjection

open IncidenceExtraction

abbrev FirstAnswer (P : Type) := Bool × (P → Triple)
abbrev SecondAnswer (P : Type) := Bool × (P → Triple) × (P → Bool)

def project {P : Type} (single : P → Bool) (indices : P → Fin 3)
    (answer : FirstAnswer P) : SecondAnswer P :=
  (answer.1, ZeroInformation.projectFull single answer.2,
    ZeroInformation.projectSingles single indices answer.2)

def accepts {P R O N : Type} (g : Incidence O N) (single : P → Bool)
    (qa : ZeroInformation.FirstInput P R O)
    (qb : ZeroInformation.SecondInput P R O N)
    (answerA : FirstAnswer P) (answerB : SecondAnswer P) : Prop :=
  (∀ j, xorTriple (answerA.2 j) = (g.rhs (qa.question j) && answerA.1)) ∧
  answerA.1 = true ∧ ∃ indices : P → Fin 3,
    qb.question = ZeroInformation.partnerQuestion single qa.question
      (fun j => g.name (qa.question j) (indices j)) ∧
    answerB = project single indices answerA

def predicateGame {P R O N : Type} (g : Incidence O N) (single : P → Bool) :
    IncidenceExtraction.Game
      (ZeroInformation.FirstInput P R O) (ZeroInformation.SecondInput P R O N)
      (FirstAnswer P) (SecondAnswer P) :=
  ⟨accepts g single⟩

end ActualProjection

end
end DFVSGames.Soundness.RepeatedGameBounds

namespace DFVSGames.Soundness.ActualPointAnswers
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open PartnerProjection PartnerMapCoordinates RawPartnerTarget
open RepeatedGameBounds

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : Nat}

def firstAnswer (rhs : Fin k → Bool) (x : ActualHomogeneous.E k) :
    ActualProjection.FirstAnswer (Fin k) :=
  let p := (PartnerLinear.sourceLinearEquiv rhs).symm x
  (p.homogeneous, fun j => ConcreteExtraction.tripleCoordinates (p.coordinates j))

def secondAnswer (rhs : Fin k → Bool) (J : Finset (Fin k)) (v : RawPoint J) :
    ActualProjection.SecondAnswer (Fin k) :=
  let y := (pointEquiv rhs J).symm v
  (y.homogeneous, (fun j => ConcreteExtraction.tripleCoordinates (y.full j)), y.single)

end
end DFVSGames.Soundness.ActualPointAnswers

namespace DFVSGames.Soundness.ActualInputRows
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open ConditionalIncidences PartnerMapCoordinates RawPartnerTarget BinaryRowTransport

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : Nat} {Q Id Name : Type}

def restrictedFirst (rhs : Id → Bool)
    (qa : ZeroInformation.FirstInput (Fin k) Q Id) (x : ActualHomogeneous.E k) : Q → F2 :=
  let p := (PartnerLinear.sourceLinearEquiv (fun j => rhs (qa.question j))).symm x
  fun q => ofBit (qa.row p.homogeneous
    (fun j => ConcreteExtraction.tripleCoordinates (p.coordinates j)) q)

def firstMap (rhs : Id → Bool) (qa : ZeroInformation.FirstInput (Fin k) Q Id) :
    ActualHomogeneous.E k →ₗ[F2] (Q → F2) :=
  if h : ∃ Z : ActualHomogeneous.E k →ₗ[F2] (Q → F2),
    ∀ x, Z x = restrictedFirst rhs qa x then Classical.choose h else 0

def restrictedSecond (J : Finset (Fin k))
    (qb : ZeroInformation.SecondInput (Fin k) Q Id Name) (v : RawPoint J) : Q → F2 :=
  let y := (pointEquiv (fun _ : Fin k => false) J).symm v
  fun q => ofBit (qb.row y.homogeneous
    (fun j => ConcreteExtraction.tripleCoordinates (y.full j)) y.single q)

def secondMap (J : Finset (Fin k))
    (qb : ZeroInformation.SecondInput (Fin k) Q Id Name) : RawPoint J →ₗ[F2] (Q → F2) :=
  if h : ∃ Y : RawPoint J →ₗ[F2] (Q → F2),
    ∀ v, Y v = restrictedSecond J qb v then Classical.choose h else 0

end
end DFVSGames.Soundness.ActualInputRows

namespace DFVSGames.Clean.AnswerBridge

open Integration.BinaryLinear
open Reduction
open Soundness
open Soundness.RepeatedGameBounds
open Soundness.RawPartnerTarget

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : ℕ} {Q Id Name : Type}

abbrev SourceAnswer (k : ℕ) := {x : ActualHomogeneous.E k // ActualHomogeneous.tau x = 1}
abbrev TargetAnswer (J : Finset (Fin k)) := {v : RawPoint J // v none = 1}

open Soundness.ConditionalIncidences Soundness.BinaryRowTransport
open scoped BigOperators

variable {D : Type} [AddCommGroup D] [Module F2 D]

def finiteCoordinates [FiniteDimensional F2 D] :
    D ≃ₗ[F2] (Fin (Module.finrank F2 D) → F2) :=
  (Module.finBasis F2 D).equivFun

def bitsCoordinatesEquiv (coordinates : D ≃ₗ[F2] (Q → F2)) :
    D ≃ ZeroInformation.Bits Q :=
  coordinates.toEquiv.trans rowBitsEquiv

def coefficientsEquiv (coordinates : D ≃ₗ[F2] (Q → F2)) (J : Finset (Fin k)) :
    RawCoefficients J D ≃ RawCoefficients J (ZeroInformation.Bits Q) :=
  Equiv.piCongrRight (fun _ => bitsCoordinatesEquiv coordinates)

def defaultTargetAnswer (J : Finset (Fin k)) : TargetAnswer J :=
  ⟨Pi.single none 1, by simp⟩

end
end DFVSGames.Clean.AnswerBridge

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ProductLaw
attribute [-instance] _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Clean.ProductLaw

open scoped BigOperators
open Foundations.Games
open Soundness.ConditionalIncidences

noncomputable section
attribute [local instance] Classical.propDecidable

variable {P Q S : Type} [Fintype P] [DecidableEq P] [Fintype Q] [Fintype S]

def splitCoordinates (K : Finset P) :
    (P → Q) ≃ (PositionInside K → Q) × (PositionOutside K → Q) :=
  Equiv.piEquivPiSubtypeProd (fun i => i ∈ K) (fun _ => Q)

end
end DFVSGames.Clean.ProductLaw

namespace DFVSGames.Soundness.ConditionalGameLaw
open scoped BigOperators
open Foundations.Games
open ConditionalIncidences ConditionalSimulation IncidenceExtraction RepeatedGameBounds

noncomputable section
attribute [local instance] Classical.propDecidable

variable {P R O N : Type}
  [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

abbrev OuterStrategy := IncidenceExtraction.Strategies
  (ZeroInformation.FirstInput P R O) (ZeroInformation.SecondInput P R O N)
  (ActualProjection.FirstAnswer P) (ActualProjection.SecondAnswer P)

def actualWin (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N)) (draw : Draw P O) : Prop :=
  strategy.wins (ActualProjection.predicateGame (R := R) g (membershipBool J))
    (actualFirst J gamma draw) (actualSecond J g.name gamma draw)

end
end DFVSGames.Soundness.ConditionalGameLaw

namespace DFVSGames.Clean.UpperBound

open scoped BigOperators
open Foundations.Games
open Soundness
open Soundness.ConditionalIncidences Soundness.ConditionalSimulation
open Soundness.ConditionalGameLaw Soundness.RepeatedGameBounds

noncomputable section
attribute [local instance] Classical.propDecidable

variable {P R O N : Type}
  [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

def fixedAdviceSuccess (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (g : IncidenceExtraction.Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N)) : ℝ :=
  (FiniteDistribution.table (fun _ : P => μ)).probability
    (fun draw => decide (actualWin J g gamma strategy draw))

end
end DFVSGames.Clean.UpperBound

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_Mixture
attribute [-instance] _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Clean

open Foundations.Games
open scoped BigOperators

noncomputable section

def bernoulli (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    FiniteDistribution Bool where
  weight b := if b then p else 1 - p
  nonnegative b := by cases b <;> simp [hp₀, sub_nonneg.mpr hp₁]
  normalized := by simp []

variable {E : Type*} [Fintype E] [Nonempty E]

def singletonSlopeLaw (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    FiniteDistribution (Bool × E) :=
  (bernoulli β hβ₀ hβ₁).product (FiniteDistribution.uniform E)

end
end DFVSGames.Clean

namespace DFVSGames.Clean.Experiment

open scoped BigOperators
open Foundations.Games
open Soundness
open Soundness.ConditionalIncidences Soundness.ConditionalSimulation
open Soundness.ConditionalGameLaw

noncomputable section

variable {R O N : Type} [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

def coefficients {k : ℕ} (extra : Additional k R) (seed : SparseSeed k R) :
    RawCoefficients (singletonSet seed) (Coefficient R) :=
  fun slot => match slot with
  | none => extra.1
  | some (.inl (i, j)) => if j = 0 then (extra.2 i.val).1 else (extra.2 i.val).2
  | some (.inr i) => (seed i.val).2

abbrev LocalStrategies (k : ℕ) (R O N : Type) :=
  OuterStrategy (P := Fin k) (R := R) (O := O) (N := N)

def success (k : ℕ) (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N)
    (extraLaw : FiniteDistribution (Additional k R))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (strategy : Additional k R → SparseSeed k R → LocalStrategies k R O N) : ℝ :=
  extraLaw.expectation fun extra =>
    ((singletonSlopeLaw (E := Coefficient R) β hβ₀ hβ₁).iid k).expectation fun seed =>
      UpperBound.fixedAdviceSuccess μ (singletonSet seed) g (coefficients extra seed)
        (strategy extra seed)

end
end DFVSGames.Clean.Experiment

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_PartnerFullSampling
attribute [-instance] _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Clean.CoefficientSampling

open Foundations.Games
open Soundness.ConditionalIncidences
open scoped BigOperators

noncomputable section

variable {P C : Type} [Fintype P] [DecidableEq P] [Fintype C] [Nonempty C]

def selectCoefficients (J : Finset P) (extra : C × (P → C × C)) (single : P → C) :
    RawCoefficients J C :=
  fun slot => match slot with
  | none => extra.1
  | some (.inl (i, j)) => if j = 0 then (extra.2 i.val).1 else (extra.2 i.val).2
  | some (.inr i) => single i.val

def coefficientProductEquiv (J : Finset P) :
    RawCoefficients J C ≃ C × ((PositionOutside J → C × C) × (PositionInside J → C)) where
  toFun gamma := (gamma none,
    ((fun i => (gamma (some (.inl (i, 0))), gamma (some (.inl (i, 1))))),
      fun i => gamma (some (.inr i))))
  invFun parts := fun slot => match slot with
    | none => parts.1
    | some (.inl (i, j)) => if j = 0 then (parts.2.1 i).1 else (parts.2.1 i).2
    | some (.inr i) => parts.2.2 i
  left_inv gamma := by
    funext slot
    cases slot with
    | none => rfl
    | some slot =>
      cases slot with
      | inl pair => rcases pair with ⟨i, j⟩; fin_cases j <;> rfl
      | inr i => rfl
  right_inv parts := by
    rcases parts with ⟨intercept, full, single⟩
    rfl

end
end DFVSGames.Clean.CoefficientSampling


namespace DFVSGames.Clean.NativeExperiment

open Foundations.Games
open Soundness
open Soundness.ConditionalIncidences Soundness.ConditionalGameLaw
open Experiment
open scoped BigOperators

noncomputable section

variable {R O N : Type} [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

abbrev MaskStrategy (k : ℕ) (R O N : Type) :=
  (mask : Fin k → Bool) → RawCoefficients (maskSet mask) (Coefficient R) →
    LocalStrategies k R O N

def liftStrategy {k : ℕ} (strategy : MaskStrategy k R O N)
    (extra : Additional k R) (seed : SparseSeed k R) : LocalStrategies k R O N :=
  strategy (fun i => (seed i).1) (coefficients extra seed)

def success (k : ℕ) (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (strategy : MaskStrategy k R O N) : ℝ :=
  ((bernoulli β hβ₀ hβ₁).iid k).expectation fun mask =>
    (FiniteDistribution.uniform (RawCoefficients (maskSet mask) (Coefficient R))).expectation
      fun gamma => UpperBound.fixedAdviceSuccess μ (maskSet mask) g gamma (strategy mask gamma)

end
end DFVSGames.Clean.NativeExperiment


namespace DFVSGames.Clean.ActualAdviceBridge

open scoped BigOperators
open Foundations.Games Integration.BinaryLinear Reduction
open Soundness Soundness.ConditionalIncidences Soundness.ConditionalGameLaw
open Soundness.RawPartnerTarget Soundness.BinaryRowTransport
open AnswerBridge

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : ℕ} {D Q O N : Type} [AddCommGroup D] [Module F2 D]

def indexSlot (i : Fin 3) : PartnerProjection.Slot :=
  if i = 0 then .first else if i = 1 then .second else .third

@[simp] theorem slotIndex_indexSlot (i : Fin 3) :
    ConcreteExtraction.slotIndex (indexSlot i) = i := by
  fin_cases i <;> rfl

def projection (g : IncidenceExtraction.Incidence O N)
    (J : Finset (Fin k)) (draw : Draw (Fin k) O) :
    ActualHomogeneous.E k →ₗ[F2] RawPoint J :=
  rawProjection (fun j => g.rhs (draw j).1) J (fun j => indexSlot (draw j).2)

def displayedQuestion (g : IncidenceExtraction.Incidence O N)
    (J : Finset (Fin k)) (draw : Draw (Fin k) O) : RawPrivateTable.SupportedV J g.name :=
  RawPrivateTable.supported J g.name (fun j => (draw j).1) (fun j => indexSlot (draw j).2)

def encodedMapCoefficients (coordinates : D ≃ₗ[F2] (Q → F2))
    (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] D) :
    RawCoefficients J (ZeroInformation.Bits Q) :=
  rowCoefficients J (gammaOfRawMap J (coordinates.toLinearMap.comp Y))

variable [Fintype Q] [DecidableEq Q] [Fintype O] [DecidableEq O]
  [Fintype N] [DecidableEq N] [Fintype D]

def mapBitsEquiv (coordinates : D ≃ₗ[F2] (Q → F2)) (J : Finset (Fin k)) :
    (RawPoint J →ₗ[F2] D) ≃ RawCoefficients J (ZeroInformation.Bits Q) :=
  (RawMapLaw.rawMapEquiv J D).symm.trans (coefficientsEquiv coordinates J)

end
end DFVSGames.Clean.ActualAdviceBridge


namespace DFVSGames.Clean.StochasticBound

open Foundations.Games
open Soundness
open Soundness.ConditionalIncidences Soundness.ConditionalSimulation
open Soundness.ConditionalGameLaw Soundness.RepeatedGameBounds
open scoped BigOperators

noncomputable section

variable {P R O N : Type}
  [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

def actualGame (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (g : IncidenceExtraction.Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R)) :
    Game (ZeroInformation.FirstInput P R O) (ZeroInformation.SecondInput P R O N)
      (ActualProjection.FirstAnswer P) (ActualProjection.SecondAnswer P) :=
  Simulation.weightedGame (ActualProjection.predicateGame (R := R) g (membershipBool J))
    ((FiniteDistribution.table (fun _ : P => μ)).pushforward fun draw =>
      (actualFirst J gamma draw, actualSecond J g.name gamma draw))

abbrev Responses (P R O N : Type) [Fintype P] [DecidableEq P] :=
  (ZeroInformation.FirstInput P R O → FiniteDistribution (ActualProjection.FirstAnswer P)) ×
  (ZeroInformation.SecondInput P R O N → FiniteDistribution (ActualProjection.SecondAnswer P))

def nativeStochasticSuccess (k : ℕ) (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (responses : (mask : Fin k → Bool) →
      RawCoefficients (NativeExperiment.maskSet mask) (ZeroInformation.Bits R) →
      Responses (Fin k) R O N) : ℝ :=
  ((bernoulli β hβ₀ hβ₁).iid k).expectation fun mask =>
    (FiniteDistribution.uniform
      (RawCoefficients (NativeExperiment.maskSet mask) (ZeroInformation.Bits R))).expectation
      fun gamma => (actualGame μ (NativeExperiment.maskSet mask) g gamma).stochasticSuccess
        (responses mask gamma).1 (responses mask gamma).2

end
end DFVSGames.Clean.StochasticBound

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ActualAdviceStochasticBridge
attribute [-instance] _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Clean.ActualAdviceStochasticBridge

open Foundations.Games Integration.BinaryLinear Reduction
open Soundness Soundness.ConditionalIncidences Soundness.RawPartnerTarget
open Soundness.RepeatedGameBounds
open AnswerBridge ActualAdviceBridge

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : ℕ} {D Q O N : Type} [AddCommGroup D] [Module F2 D]
  [Fintype Q] [DecidableEq Q] [Fintype O] [DecidableEq O]
  [Fintype N] [DecidableEq N] [Fintype D]

instance sourceAnswerNonempty : Nonempty (SourceAnswer k) := ⟨⟨(1, 0), rfl⟩⟩
instance targetAnswerNonempty (J : Finset (Fin k)) : Nonempty (TargetAnswer J) :=
  ⟨defaultTargetAnswer J⟩

structure Policies (k : ℕ) (g : IncidenceExtraction.Incidence O N) (D : Type)
    [AddCommGroup D] [Module F2 D] where
  first : (J : Finset (Fin k)) → (Fin k → O) →
    (ActualHomogeneous.E k →ₗ[F2] D) → FiniteDistribution (SourceAnswer k)
  second : (J : Finset (Fin k)) → RawPrivateTable.SupportedV J g.name →
    (RawPoint J →ₗ[F2] D) → FiniteDistribution (TargetAnswer J)

def extendTargetKernel (J : Finset (Fin k)) (names : O → Fin 3 → N)
    (kernel : RawPrivateTable.SupportedV J names → (RawPoint J →ₗ[F2] D) →
      FiniteDistribution (TargetAnswer J))
    (question : Fin k → Sum O N) (Y : RawPoint J →ₗ[F2] D) :
    FiniteDistribution (TargetAnswer J) :=
  if h : question ∈ Set.range
      (fun e : RawPrivateTable.Extension k O => RawPrivateTable.displayed J names e.1 e.2)
  then kernel ⟨question, h⟩ Y else FiniteDistribution.uniform (TargetAnswer J)

def firstResponse (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (J : Finset (Fin k)) (qa : ZeroInformation.FirstInput (Fin k) Q O) :
    FiniteDistribution (ActualProjection.FirstAnswer (Fin k)) :=
  (policy.first J qa.question
    (coordinates.symm.toLinearMap.comp (ActualInputRows.firstMap g.rhs qa))).pushforward
      (fun x => ActualPointAnswers.firstAnswer (fun j => g.rhs (qa.question j)) x.val)

def secondResponse (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (J : Finset (Fin k)) (qb : ZeroInformation.SecondInput (Fin k) Q O N) :
    FiniteDistribution (ActualProjection.SecondAnswer (Fin k)) :=
  (extendTargetKernel J g.name (policy.second J) qb.question
    (coordinates.symm.toLinearMap.comp (ActualInputRows.secondMap J qb))).pushforward
      (fun v => ActualPointAnswers.secondAnswer
        (ActualPointAnswers.displayedRhs g.rhs qb.question) J v.val)

def fixedMapSuccess (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] D) : ℝ :=
  (FiniteDistribution.table (fun _ : Fin k => μ)).expectation fun draw =>
    (policy.first J (fun j => (draw j).1) (Y.comp (projection g J draw))).expectation fun x =>
      (policy.second J (displayedQuestion g J draw) Y).expectation fun v =>
        if projection g J draw x.val = v.val then 1 else 0

def responses (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (mask : Fin k → Bool)
    (_ : RawCoefficients (NativeExperiment.maskSet mask) (ZeroInformation.Bits Q)) :
    StochasticBound.Responses (Fin k) Q O N :=
  (firstResponse coordinates g policy (NativeExperiment.maskSet mask),
   secondResponse coordinates g policy (NativeExperiment.maskSet mask))

def success (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) : ℝ :=
  ((bernoulli β hβ₀ hβ₁).iid k).expectation fun mask =>
    (FiniteDistribution.uniform (RawPoint (NativeExperiment.maskSet mask) →ₗ[F2] D)).expectation
      (fun Y => fixedMapSuccess μ g policy (NativeExperiment.maskSet mask) Y)

end
end DFVSGames.Clean.ActualAdviceStochasticBridge

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_FinalParameters
attribute [-instance] _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Reduction.ActualSource

open DFVSGames.Integration.BinaryLinear

def Source.satisfied (S : Source) (A : Fin S.«variables» → Bool)
    (i : Fin S.occurrences) : Bool := CloneGap.satisfied (S.equation i) A

def Source.failure (S : Source) (A : Fin S.«variables» → Bool) : ℚ :=
  Finset.univ.expect (fun i => if S.satisfied A i then (0 : ℚ) else 1)

def Source.DistinctNames (S : Source) : Prop :=
  ∀ i, (S.equation i).first ≠ (S.equation i).second ∧
    (S.equation i).first ≠ (S.equation i).third ∧
    (S.equation i).second ≠ (S.equation i).third

attribute [instance] SplitGadget.noiseFintype SplitGadget.noiseNonempty

def SplitGadget.stabilityError {s d : Nat} (g : SplitGadget s d) : ℚ :=
  Finset.univ.expect (fun xv : Ambient s d × g.NoiseIndex =>
    if g.f (xv.1 + g.noise xv.2) = g.f xv.1 then (0 : ℚ) else 1)

end DFVSGames.Reduction.ActualSource

namespace DFVSGames.Integration.SplitGadget

open BinaryLinear

variable {R : Type} [AddCommGroup R] [Module F2 R] [FiniteDimensional F2 R]

open DFVSGames.Reduction.ActualSource

noncomputable def kernelProbability {s d : Nat} (g : SplitGadget s d)
    {P : Type} [AddCommGroup P] [Module F2 P]
    (S : Ambient s d →ₗ[F2] P) : ℚ := by
  classical
  exact Finset.univ.expect (fun i => if S (g.noise i) = 0 then (1 : ℚ) else 0)

end DFVSGames.Integration.SplitGadget

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Analysis_NoiseEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Reduction.ActualGame

open DFVSGames.Integration.BinaryLinear
open ActualSource
open Foundations.Target
open scoped BigOperators

noncomputable def edge (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (ω : Outcome S k g) : Constraint (vertexCount S k s d) (2^s) where
  source := vertexEncoding S k s d (false, vertex S k s d (leftQuery S k g ω))
  target := vertexEncoding S k s d (true, vertex S k s d (rightQuery S k g ω))
  permutation := Encoding.translationTable
    (offset S k s d (leftQuery S k g ω)) (offset S k s d (rightQuery S k g ω))

theorem outcomes_nodup (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) :
    (outcomes S k g).Nodup := Finset.nodup_toList _

noncomputable def unfolded (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) (side : Bool)
    (q : Query S k s d) : Alphabet s :=
  ActualOrbit.unfold (canonical S k s d) (sideLabel S k s d labeling side) q

theorem edge_satisfied_iff (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) (ω : Outcome S k g) :
    (edge S k g ω).satisfied labeling = true ↔
      unfolded S k s d labeling false (leftQuery S k g ω) =
      unfolded S k s d labeling true (rightQuery S k g ω) := by
  rw [Constraint.satisfied, decide_eq_true_eq]
  have h := Encoding.translationTable_satisfied_iff
    (offset S k s d (leftQuery S k g ω)) (offset S k s d (rightQuery S k g ω))
    (sideLabel S k s d labeling false (vertex S k s d (leftQuery S k g ω)))
    (sideLabel S k s d labeling true (vertex S k s d (rightQuery S k g ω)))
  simp only [sideLabel, Encoding.alphabetEquiv_apply_symm_apply] at h
  exact h.trans (ActualOrbit.constraint_iff_unfolded (canonical S k s d)
    (sideLabel S k s d labeling false) (sideLabel S k s d labeling true) _ _)

noncomputable def acceptanceProbability (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) : ℚ :=
  Finset.univ.expect (fun ω : Outcome S k g =>
    if (edge S k g ω).satisfied labeling then (1 : ℚ) else 0)

theorem acceptanceProbability_eq_test (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    acceptanceProbability S k g labeling =
      Finset.univ.expect (fun ω : Outcome S k g =>
        if unfolded S k s d labeling false (leftQuery S k g ω) =
            unfolded S k s d labeling true (rightQuery S k g ω)
        then (1 : ℚ) else 0) := by
  unfold acceptanceProbability
  apply Finset.expect_congr rfl
  intro ω _
  simp only [edge_satisfied_iff]

theorem explicitOutcomes_nodup (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (explicitOutcomes S k g en).Nodup :=
  ActualEnumeration.nodup_indexedOutcomes en.nodup _ _ _ _

theorem explicitOutcomes_perm_outcomes (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (explicitOutcomes S k g en).Perm (outcomes S k g) := by
  apply (List.perm_ext_iff_of_nodup (explicitOutcomes_nodup S k g en)
    (outcomes_nodup S k g)).2
  intro ω
  simp

end DFVSGames.Reduction.ActualGame

namespace DFVSGames.Decoder.TableKeysGame

open DFVSGames.Integration.BinaryLinear DFVSGames.Reduction
open ActualSource Foundations.Target
open scoped BigOperators

abbrev Question (S : Source) (k : Nat) := ActualGame.Question S k
abbrev shiftQuery (S : Source) (k s d : Nat) := ActualGame.shiftQuery S k s d

noncomputable def unfolded (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s))
    (q : Query S k s d) : Alphabet s :=
  ActualOrbit.unfold (canonical S k s d) (vertexLabel S k s d labeling) q

theorem unfolded_equivariant (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s))
    (q : Query S k s d) (c : Alphabet s) :
    unfolded S k s d labeling (shiftQuery S k s d c q) =
      unfolded S k s d labeling q + c := by
  change vertexLabel S k s d labeling
      (ActualGame.vertex S k s d (ActualGame.shiftQuery S k s d c q)) +
    ActualGame.offset S k s d (ActualGame.shiftQuery S k s d c q) = _
  rw [ActualGame.vertex_shiftQuery, ActualGame.offset_shiftQuery]
  exact (add_assoc _ _ _).symm

theorem edge_satisfied_iff (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) (ω : Outcome S k g) :
    (edge S k g ω).satisfied labeling = true ↔
      unfolded S k s d labeling (leftQuery S k g ω) =
        unfolded S k s d labeling (rightQuery S k g ω) := by
  rw [Constraint.satisfied, decide_eq_true_eq]
  have h := Encoding.translationTable_satisfied_iff
    (offset S k s d (leftQuery S k g ω)) (offset S k s d (rightQuery S k g ω))
    (vertexLabel S k s d labeling (vertex S k s d (leftQuery S k g ω)))
    (vertexLabel S k s d labeling (vertex S k s d (rightQuery S k g ω)))
  simp only [vertexLabel, Encoding.alphabetEquiv_apply_symm_apply] at h
  exact h.trans (ActualOrbit.constraint_iff_unfolded (canonical S k s d)
    (vertexLabel S k s d labeling) (vertexLabel S k s d labeling) _ _)

noncomputable def acceptanceProbability (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (labeling : Fin (vertexCount S k s d) → Fin (2^s)) : ℚ :=
  𝔼 ω : Outcome S k g, if (edge S k g ω).satisfied labeling then (1 : ℚ) else 0

theorem acceptanceProbability_eq_test (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    acceptanceProbability S k g labeling =
      𝔼 ω : Outcome S k g,
        if unfolded S k s d labeling (leftQuery S k g ω) =
            unfolded S k s d labeling (rightQuery S k g ω)
        then (1 : ℚ) else 0 := by
  unfold acceptanceProbability
  apply Finset.expect_congr rfl
  intro ω _
  simp only [edge_satisfied_iff]

theorem countSatisfied_map_inline_TableKeysGame {n q : Nat} {I : Type*}
    (labeling : Fin n → Fin q) (edges : I → Constraint n q) (xs : List I) :
    countSatisfied labeling (xs.map edges) =
      (xs.map (fun x => if (edges x).satisfied labeling then 1 else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, countSatisfied, List.sum_cons, ih]

theorem countSatisfied_eq_sum (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    countSatisfied labeling (outputInstance S k g).constraints =
      ∑ ω : Outcome S k g, if (edge S k g ω).satisfied labeling then 1 else 0 := by
  change countSatisfied labeling ((outcomes S k g).map (edge S k g)) = _
  rw [countSatisfied_map_inline_TableKeysGame]
  exact Finset.sum_map_toList _ _

theorem acceptanceProbability_eq_count (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    acceptanceProbability S k g labeling =
      (countSatisfied labeling (outputInstance S k g).constraints : ℚ) /
        (outputInstance S k g).constraints.length := by
  rw [acceptanceProbability, Fintype.expect_eq_sum_div_card,
    outputInstance_constraints_length, countSatisfied_eq_sum]
  congr 1
  simp

theorem explicitEdge_eq_rename (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (ω : Outcome S k g) :
    explicitEdge S k g ω = Integration.InstanceEquivalences.renameConstraint
      (semanticToExplicitVertices S k s d) (edge S k g ω) := by
  simp only [explicitEdge, Integration.InstanceEquivalences.renameConstraint, edge,
    semanticToExplicitVertices_apply]

theorem explicitConstraints_perm_renamed (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (outputInstanceWithEnumeration S k g en).constraints.Perm
      ((outputInstance S k g).constraints.map
        (Integration.InstanceEquivalences.renameConstraint (semanticToExplicitVertices S k s d))) := by
  simpa only [outputInstanceWithEnumeration, outputInstance, List.map_map,
    Function.comp_def, ← explicitEdge_eq_rename, outcomes] using
    (ActualGame.explicitOutcomes_perm_outcomes S k g en).map (explicitEdge S k g)

end DFVSGames.Decoder.TableKeysGame

namespace DFVSGames.Decoder.TableKeysRestoration

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open DFVSGames.Soundness
open ActualSource

noncomputable section
attribute [local instance] Classical.propDecidable

section OrbitExtension

variable {Q T : Type} {s d : Nat}

def extendedLabel (can : Q → Ambient s d × T)
    (label : ActualOrbit.Vertex can → Alphabet s) (body : Vector d × T) : Alphabet s :=
  if h : ∃ q, ActualOrbit.body can q = body then label ⟨body, h⟩ else 0

def restoredData (can : Q → Ambient s d × T)
    (label : ActualOrbit.Vertex can → Alphabet s) (D : Ambient s d × T) : Alphabet s :=
  extendedLabel can label (D.1.2, D.2) + D.1.1

end OrbitExtension

def keyAnswer (S : Source) (k s d : Nat)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (D : TableKeys.Key k (Fin S.«variables») (Fin S.occurrences) (Ambient s d)) : Alphabet s :=
  restoredData (TableKeysGame.canonical S k s d)
    (TableKeysGame.vertexLabel S k s d labeling) D

def projectedAnswer (S : Source) (k s d : Nat)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (J : Finset (Fin k))
    (O : RawPrivateTable.SupportedV J (ActualGame.names S))
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] Ambient s d) : Alphabet s :=
  keyAnswer S k s d labeling
    (TableKeys.projectedKey J (ActualGame.names S) (ActualGame.rhs S) O Y)

end

end DFVSGames.Decoder.TableKeysRestoration

namespace DFVSGames.Decoder.TableKeysPrivateRow

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open DFVSGames.Soundness
open ActualSource

noncomputable section

variable {R : Type} [AddCommGroup R] [Module F2 R]
variable {k s d : Nat}

def rowAnswer (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (J : Finset (Fin k))
    (Q : RawPrivateTable.SupportedV J (ActualGame.names S))
    (A : Alphabet s →ₗ[F2] R)
    (rows : AdviceFibers.ObservedRow (E := RawPartnerTarget.RawPoint J) A)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (N : RawPartnerTarget.RawPoint J →ₗ[F2] A.ker) : Alphabet s :=
  TableKeysRestoration.projectedAnswer S k s d labeling J Q
    ((AdviceFibers.assemble A (AdviceFibers.observedBase A rows) N).prod T)

end

end DFVSGames.Decoder.TableKeysPrivateRow

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Analysis_PrivateFourier
attribute [-instance] _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace DFVSGames.Decoder.PrivateFourier

open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixFourier
open scoped BigOperators Classical

section Signs

def sign (a : F2) : ℝ := (binarySign a).re

@[simp] theorem sign_zero : sign 0 = 1 := by simp [sign]
@[simp] theorem sign_one : sign 1 = -1 := by simp [sign]

theorem sign_sq (a : F2) : sign a ^ 2 = 1 := by
  rcases Integration.BinaryLinear.scalar_cases a with rfl | rfl <;> simp

@[simp] theorem sign_abs (a : F2) : |sign a| = 1 := by
  rcases Integration.BinaryLinear.scalar_cases a with rfl | rfl <;> simp

end Signs

section ActualFourier

variable {E H K : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup H] [Module F2 H]
variable [AddCommGroup K] [Module F2 K]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]

def tableSign (F : (E →ₗ[F2] H) → K) (σ : K →ₗ[F2] F2)
    (N : E →ₗ[F2] H) : ℝ := sign (σ (F N))

def frequencyWeight (f : (E →ₗ[F2] H) → ℝ) (Φ : H →ₗ[F2] E) : ℝ :=
  linearCoeff f Φ ^ 2

omit [FiniteDimensional F2 E] [FiniteDimensional F2 H] [Fintype (H →ₗ[F2] E)] in
theorem frequencyWeight_nonneg (f : (E →ₗ[F2] H) → ℝ) (Φ : H →ₗ[F2] E) :
    0 ≤ frequencyWeight f Φ := sq_nonneg _

theorem tableSign_frequencyWeight_sum (F : (E →ₗ[F2] H) → K)
    (σ : K →ₗ[F2] F2) :
    ∑ Φ : H →ₗ[F2] E, frequencyWeight (tableSign F σ) Φ = 1 := by
  simp only [frequencyWeight, linear_parseval, tableSign, sign_sq]
  exact Fintype.expect_const 1

end ActualFourier


end DFVSGames.Decoder.PrivateFourier
end


noncomputable section

namespace DFVSGames.Decoder.PrivateStrategy

attribute [local instance] Classical.propDecidable

open PrivateFourier
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Foundations.Games
open scoped BigOperators Classical

section Candidates

variable {E E' : Type*} [AddCommGroup E] [Module F2 E]
    [AddCommGroup E'] [Module F2 E'] [Fintype E]

def candidates (Z : Submodule F2 E) (z : E) (τ : E →ₗ[F2] F2) : Finset E :=
  Finset.univ.filter fun v => v - z ∈ Z ∧ τ v = 1

theorem mem_candidates (Z : Submodule F2 E) (z v : E) (τ : E →ₗ[F2] F2) :
    v ∈ candidates Z z τ ↔ v - z ∈ Z ∧ τ v = 1 := by simp [candidates]

end Candidates

section RightRule

variable {E H K : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup H] [Module F2 H]
variable [AddCommGroup K] [Module F2 K]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]
variable [Fintype (K →ₗ[F2] F2)]

omit [FiniteDimensional F2 H] in
theorem exists_unit (σ : H →ₗ[F2] F2) (hne : σ ≠ 0) : ∃ h, σ h = 1 := by
  have hn : ∃ h, σ h ≠ 0 := by
    by_contra hh
    apply hne
    ext h
    by_contra hh'
    exact hh ⟨h, hh'⟩
  obtain ⟨h, hh⟩ := hn
  exact ⟨h, (DFVSGames.Integration.BinaryLinear.scalar_cases _).resolve_left hh⟩

def chooseUnit (σ : H →ₗ[F2] F2) (hne : σ ≠ 0) : H :=
  Classical.choose (exists_unit σ hne)

abbrev ActualAnswer (τ : E →ₗ[F2] F2) := {v : E // τ v = 1}

def privateSeedLaw (F : (E →ₗ[F2] H) → K) :
    FiniteDistribution ((K →ₗ[F2] F2) × (H →ₗ[F2] E)) where
  weight p := frequencyWeight (tableSign F p.1) p.2 /
    (Fintype.card (K →ₗ[F2] F2) : ℝ)
  nonnegative p := div_nonneg (frequencyWeight_nonneg _ _) (Nat.cast_nonneg _)
  normalized := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.sum_div, tableSign_frequencyWeight_sum]
    simp [Fintype.card_ne_zero]

def privateOutput (ι : H →ₗ[F2] K) (τ : E →ₗ[F2] F2)
    (fallback : ActualAnswer τ) (p : (K →ₗ[F2] F2) × (H →ₗ[F2] E)) :
    ActualAnswer τ :=
  if hn : p.1.comp ι = 0 then fallback else
    let v := p.2 (chooseUnit (p.1.comp ι) hn)
    if hv : τ v = 1 then ⟨v, hv⟩ else fallback

def privateLaw [Fintype E] (F : (E →ₗ[F2] H) → K)
    (ι : H →ₗ[F2] K) (τ : E →ₗ[F2] F2) (fallback : ActualAnswer τ) :
    FiniteDistribution (ActualAnswer τ) :=
  (privateSeedLaw F).pushforward (privateOutput ι τ fallback)

end RightRule

section LeftRule

variable {E : Type*} [AddCommGroup E] [Module F2 E] [Fintype E]

def candidateLaw (Z : Submodule F2 E) (z : E) (τ : E →ₗ[F2] F2)
    (hz : τ z = 1) : FiniteDistribution (ActualAnswer τ) := by
  letI : Nonempty {v // v ∈ candidates Z z τ} :=
    ⟨⟨z, (mem_candidates Z z z τ).2 ⟨by simp, hz⟩⟩⟩
  exact (FiniteDistribution.uniform {v // v ∈ candidates Z z τ}).pushforward
    (fun v => ⟨v.1, ((mem_candidates Z z v.1 τ).1 v.2).2⟩)

end LeftRule


end DFVSGames.Decoder.PrivateStrategy
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_AdviceLaw
attribute [-instance] _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section

section

namespace DFVSGames.Decoder.AdviceLaw

open scoped BigOperators
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction DFVSGames.Soundness
open ConditionalIncidences RawPartnerTarget RawMapLaw
open DFVSGames.Foundations.Games
open DFVSGames.Clean

noncomputable section
attribute [local instance] Classical.propDecidable

section VisibleMap

variable {k : ℕ} {K W R : Type}
  [AddCommGroup K] [Module F2 K] [Fintype K]
  [AddCommGroup W] [Module F2 W] [Fintype W]
  [AddCommGroup R] [Module F2 R] [Fintype R]

def visibleMap (A : K →ₗ[F2] R) {J : Finset (Fin k)}
    (T : RawPoint J →ₗ[F2] W) (M : RawPoint J →ₗ[F2] K) :
    RawPoint J →ₗ[F2] (W × A.range) :=
  T.prod (A.rangeRestrict.comp M)

def rawMapPairCoefficientsEquiv (J : Finset (Fin k)) :
    ((RawPoint J →ₗ[F2] W) × (RawPoint J →ₗ[F2] K)) ≃
      (RawSlot J → W × K) :=
  (Equiv.prodCongr (rawMapEquiv J W).symm (rawMapEquiv J K).symm).trans
    (Equiv.arrowProdEquivProdArrow (RawSlot J) (fun _ => W) (fun _ => K)).symm

variable {O N : Type} [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

def actualSuccess (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (A : K →ₗ[F2] R)
    (policy : ActualAdviceStochasticBridge.Policies k g (W × A.range))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) : ℝ :=
  ((Clean.bernoulli β hβ₀ hβ₁).iid k).expectation fun mask =>
    (FiniteDistribution.uniform
      ((RawPoint (NativeExperiment.maskSet mask) →ₗ[F2] W) ×
        (RawPoint (NativeExperiment.maskSet mask) →ₗ[F2] K))).expectation fun TM =>
      ActualAdviceStochasticBridge.fixedMapSuccess μ g policy
        (NativeExperiment.maskSet mask) (visibleMap A TM.1 TM.2)

end VisibleMap

section WholeTable

variable {k : ℕ} {V : Type} [AddCommGroup V] [Module F2 V] [Fintype V]
  [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]

def drawDistribution (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution ((Fin k → PaddedLaw.BlockDraw V) × V) where
  weight := PaddedLaw.drawWeights β k
  nonnegative dz := mul_nonneg
    ((SparseLaw.independentWeights_isProbability _
      (PaddedLaw.blockWeights_isProbability β hβ hβ') k).1 dz.1)
    (SparseLaw.uniformWeights_pos dz.2).le
  normalized := by
    rw [Fintype.sum_prod_type]
    simp only [PaddedLaw.drawWeights, ← Finset.mul_sum,
      (SparseLaw.uniformWeights_isProbability (α := V)).2, mul_one]
    exact (SparseLaw.independentWeights_isProbability _
      (PaddedLaw.blockWeights_isProbability β hβ hβ') k).2

def paddedDistribution (rhs : Fin k → Bool) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution (ActualHomogeneous.E k →ₗ[F2] V) :=
  (drawDistribution β hβ hβ').pushforward (fun dz => PaddedLaw.paddedMap rhs dz.1 dz.2)

end WholeTable

section CommonLaw

variable {Ω Y : Type*} [Fintype Ω] [Fintype Y]

def withKernel (μ : FiniteDistribution Ω) (p : Ω → FiniteDistribution Y) :
    FiniteDistribution (Ω × Y) where
  weight xy := μ.weight xy.1 * (p xy.1).weight xy.2
  nonnegative xy := mul_nonneg (μ.nonnegative _) ((p _).nonnegative _)
  normalized := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, FiniteDistribution.normalized, mul_one]
    exact μ.normalized

end CommonLaw

section HiddenRows

variable {k : ℕ} {K R : Type}
  [AddCommGroup K] [Module F2 K] [Fintype K]
  [AddCommGroup R] [Module F2 R] [Fintype R]

instance observedRowsFintype (J : Finset (Fin k)) (A : K →ₗ[F2] R) :
    Fintype (AdviceFibers.ObservedRow (E := RawPoint J) A) := Fintype.ofFinite _

end HiddenRows

section ProjectionSeeds

variable {k : ℕ} {V : Type} [AddCommGroup V] [Module F2 V] [Fintype V]

def projectionSeedDistribution (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution (ProjectionSeed k V) where
  weight s := PaddedLaw.choiceTupleWeight β s.1 * SparseLaw.uniformWeights _ s.2
  nonnegative s := mul_nonneg
    ((PaddedLaw.choiceTupleWeight_isProbability β hβ hβ').1 s.1)
    (SparseLaw.uniformWeights_pos s.2).le
  normalized := by
    rw [Fintype.sum_sigma]
    simp_rw [← Finset.mul_sum, (SparseLaw.uniformWeights_isProbability).2, mul_one]
    exact (PaddedLaw.choiceTupleWeight_isProbability β hβ hβ').2

def projectSeedMap (rhs : Fin k → Bool) (s : ProjectionSeed k V) :
    ActualHomogeneous.E k →ₗ[F2] V :=
  s.2.comp (rawProjection rhs (PaddedLaw.choiceMask s.1) (PaddedLaw.choiceSlots s.1))

end ProjectionSeeds

section ActualDraw

variable {k : ℕ} {Id K W R : Type}
  [AddCommGroup K] [Module F2 K] [AddCommGroup W] [Module F2 W]
  [AddCommGroup R] [Module F2 R]

def seedToActualDraw (occ : Fin k → Id) (A : K →ₗ[F2] R)
    (s : ProjectionSeed k (K × W)) : AdviceExperiment.Draw k Id K W R where
  singletons := PaddedLaw.choiceMask s.1
  occurrences := occ
  positions := PaddedLaw.choiceSlots s.1
  rowMap := A
  hiddenMatrix := (LinearMap.fst F2 K W).comp s.2
  complement := (LinearMap.snd F2 K W).comp s.2

end ActualDraw

section MaskSlots

def choiceDistribution (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution PaddedLaw.ProjectionChoice where
  weight := PaddedLaw.choiceWeight β
  nonnegative := (PaddedLaw.choiceWeight_isProbability β hβ hβ').1
  normalized := (PaddedLaw.choiceWeight_isProbability β hβ hβ').2

def maskSlotChoice (p : Bool × Fin 3) : PaddedLaw.ProjectionChoice :=
  if p.1 then some p.2 else none

def choicesOfMaskSlots {k : ℕ} (mask : Fin k → Bool) (slots : Fin k → Fin 3) :
    Fin k → PaddedLaw.ProjectionChoice :=
  fun j => maskSlotChoice (mask j, slots j)

end MaskSlots

def fullSeedLaw {k : ℕ} {Id A V : Type} [Fintype Id] [Fintype A]
    [AddCommGroup V] [Module F2 V] [Fintype V]
    (occurrences : FiniteDistribution (Fin k → Id)) (publicLaw : FiniteDistribution A)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :=
  (occurrences.product publicLaw).product (projectionSeedDistribution (k := k) (V := V) β hβ hβ')

def fullSeedPad {k : ℕ} {Id A V : Type} [AddCommGroup V] [Module F2 V]
    (rhs : Id → Bool) (s : ((Fin k → Id) × A) × ProjectionSeed k V) :
    ((Fin k → Id) × A) × (ActualHomogeneous.E k →ₗ[F2] V) :=
  (s.1, projectSeedMap (fun j => rhs (s.1.1 j)) s.2)

section CompleteData

variable {k : ℕ} {Id K W R : Type}
  [AddCommGroup K] [Module F2 K] [AddCommGroup W] [Module F2 W]
  [AddCommGroup R] [Module F2 R]

def completeDraw (d : CompleteData k Id K W R) (N : PrivateMap d) :
    AdviceExperiment.Draw k Id K W R where
  singletons := PaddedLaw.choiceMask d.2.1
  occurrences := d.1.1
  positions := PaddedLaw.choiceSlots d.2.1
  rowMap := d.1.2
  hiddenMatrix := AdviceFibers.assemble d.1.2 (AdviceFibers.observedBase d.1.2 d.2.2.2) N
  complement := d.2.2.1

theorem completeDraw_rows (d : CompleteData k Id K W R) (N : PrivateMap d) :
    (completeDraw d N).rowMap.comp (completeDraw d N).hiddenMatrix = d.2.2.2.val := by
  exact (AdviceFibers.observed_assemble _ _ N).trans
    (AdviceFibers.observedBase_property _ _)

theorem completeDraw_left (rhs : Id → F2) (d : CompleteData k Id K W R)
    (N : PrivateMap d) :
    AdviceExperiment.leftObservation rhs (completeDraw d N) = {
      occurrences := d.1.1, rowMap := d.1.2,
      complement := d.2.2.1.comp (rawProjection (fun j => toBit (rhs (d.1.1 j)))
        (PaddedLaw.choiceMask d.2.1) (PaddedLaw.choiceSlots d.2.1)),
      rows := d.2.2.2.val.comp (rawProjection (fun j => toBit (rhs (d.1.1 j)))
        (PaddedLaw.choiceMask d.2.1) (PaddedLaw.choiceSlots d.2.1)) } := by
  simp only [AdviceExperiment.leftObservation, completeDraw_rows] ; rfl

variable [Fintype Id] [Fintype K] [Fintype W] [Fintype R] [Fintype (K →ₗ[F2] R)]

def completeWeight (occurrences : FiniteDistribution (Fin k → Id))
    (publicLaw : FiniteDistribution (K →ₗ[F2] R)) (β : ℝ)
    (d : CompleteData k Id K W R) : ℝ :=
  (occurrences.weight d.1.1 * publicLaw.weight d.1.2) *
    (PaddedLaw.choiceTupleWeight β d.2.1 *
      (1 / (Fintype.card (RawPoint (PaddedLaw.choiceMask d.2.1) →ₗ[F2] (K × W)) : ℝ)))

end CompleteData

end
end DFVSGames.Decoder.AdviceLaw

end

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_RowErasureSliceQuotient
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace DFVSGames.Decoder.TransferredDecoding

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open DFVSGames.Soundness
open ActualSource
open PrivateFourier PrivateStrategy
open scoped BigOperators Classical

open DFVSGames.Inverse

attribute [local instance] Fintype.ofFinite

variable {R : Type} [AddCommGroup R] [Module F2 R]
variable {k s d : Nat}

local instance homFintype_ra49947_1 {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective
def visibleFallback (J : Finset (Fin k)) : ActualAnswer (TableKeys.visibleTau J) :=
  ⟨Pi.single none 1, by simp [TableKeys.visibleTau]⟩

end DFVSGames.Decoder.TransferredDecoding
end

noncomputable section

namespace DFVSGames.Decoder.VisiblePolicies

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open DFVSGames.Soundness
open DFVSGames.Foundations.Games
open ActualSource PrivateStrategy
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

structure ResponseWitness (k : ℕ) where
  columns : Submodule F2 (ActualHomogeneous.E k)
  coefficient : ActualHomogeneous.E k
  firstBit : ActualHomogeneous.tau coefficient = 1

def defaultWitness (k : ℕ) : ResponseWitness k :=
  ⟨⊥, ActualHomogeneous.hBasis k, ActualHomogeneous.tau_hBasis⟩

variable {k s d : ℕ} {R : Type} [AddCommGroup R] [Module F2 R]

abbrev LeftInput (S : Source) (k s d : ℕ) (R : Type)
    [AddCommGroup R] [Module F2 R] :=
  AdviceExperiment.FullAdvice k (Fin S.occurrences) (Alphabet s) (Vector d) R

abbrev RightInput (S : Source) (J : Finset (Fin k)) (s d : ℕ) (R : Type)
    [AddCommGroup R] [Module F2 R] :=
  AdviceExperiment.ProjectedAdvice (K := Alphabet s) (W := Vector d) (R := R)
    (ActualGame.names S) J

def chosenWitness {S : Source}
    (good : LeftInput S k s d R → ResponseWitness k → Prop)
    (q : LeftInput S k s d R) : ResponseWitness k :=
  if h : ∃ w, good q w then Classical.choose h else defaultWitness k

def leftPolicy {S : Source}
    (good : LeftInput S k s d R → ResponseWitness k → Prop)
    (q : LeftInput S k s d R) : FiniteDistribution (ActualAnswer (ActualHomogeneous.tau (k := k))) :=
  let w := chosenWitness good q
  candidateLaw w.columns w.coefficient ActualHomogeneous.tau w.firstBit

def pointLaw {X : Type*} [Fintype X] (x : X) : FiniteDistribution X where
  weight y := if y = x then 1 else 0
  nonnegative y := by split <;> norm_num
  normalized := by simp

def rightPolicy (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (J : Finset (Fin k)) (q : RightInput S J s d R) :
    FiniteDistribution (ActualAnswer (TableKeys.visibleTau J)) :=
  if h : ∃ M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s,
      q.rowMap.comp M = q.rows then
    privateLaw
      (TableKeysPrivateRow.rowAnswer S labeling J q.question q.rowMap ⟨q.rows, h⟩ q.complement)
      q.rowMap.ker.subtype (TableKeys.visibleTau J) (TransferredDecoding.visibleFallback J)
  else pointLaw (TransferredDecoding.visibleFallback J)

def observedAgreement (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : LeftInput S k s d R → ResponseWitness k → Prop)
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) R) : ℝ :=
  ((leftPolicy good (AdviceExperiment.leftObservation (ActualGame.rhs S) draw)).product
    (rightPolicy S labeling draw.singletons
      (AdviceExperiment.rightObservation (ActualGame.names S) draw).2)).probability
    (fun answers => decide
      (AdviceExperiment.projection (ActualGame.rhs S) draw answers.1.1 = answers.2.1))

end DFVSGames.Decoder.VisiblePolicies
end

namespace DFVSGames.Clean.IncidenceGap

open DFVSGames.Foundations.Games
open DFVSGames.Soundness.IncidenceExtraction (Incidence Triple xorTriple)
open scoped BigOperators

noncomputable section

variable {O N : Type} [Fintype O] [Fintype N]

local instance accepts_decidable (g : Incidence O N) (o : O) (i : Fin 3)
    (a : Triple) (b : Bool) : Decidable (g.accepts o i a b) :=
  inferInstanceAs (Decidable (xorTriple a = g.rhs o ∧ a i = b))

def paritySuccess (g : Incidence O N) (ω : FiniteDistribution O) (b : N → Bool) : ℝ :=
  ω.probability (fun o => decide (xorTriple (fun i => b (g.name o i)) = g.rhs o))

def parityValue (g : Incidence O N) (ω : FiniteDistribution O) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty (paritySuccess g ω)

end
end DFVSGames.Clean.IncidenceGap

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ActualAdviceUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Decoder.ActualAdviceUpper

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open DFVSGames.Soundness
open DFVSGames.Foundations.Games
open ActualSource
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d rs : Nat}

instance publicMapFintype (s rs : Nat) : Fintype (Alphabet s →ₗ[F2] Vector rs) :=
  Fintype.ofInjective (fun A : Alphabet s →ₗ[F2] Vector rs => (A : Alphabet s → Vector rs))
    DFunLike.coe_injective

def sourceIncidence (S : Source) :
    IncidenceExtraction.Incidence (Fin S.occurrences) (Fin S.«variables») where
  name := ActualGame.names S
  rhs e := (S.equation e).rhs

abbrev Visible (d : Nat) (A : Alphabet s →ₗ[F2] Vector rs) := Vector d × A.range

def complementMap {E : Type} [AddCommGroup E] [Module F2 E]
    (A : Alphabet s →ₗ[F2] Vector rs) (Y : E →ₗ[F2] Visible d A) :
    E →ₗ[F2] Vector d :=
  (LinearMap.fst F2 (Vector d) A.range).comp Y

def rowMap {E : Type} [AddCommGroup E] [Module F2 E]
    (A : Alphabet s →ₗ[F2] Vector rs) (Y : E →ₗ[F2] Visible d A) :
    E →ₗ[F2] Vector rs :=
  A.range.subtype.comp ((LinearMap.snd F2 (Vector d) A.range).comp Y)

def fullInput (S : Source) (A : Alphabet s →ₗ[F2] Vector rs)
    (occ : Fin k → Fin S.occurrences)
    (Y : ActualHomogeneous.E k →ₗ[F2] Visible d A) :
    VisiblePolicies.LeftInput S k s d (Vector rs) where
  occurrences := occ
  rowMap := A
  complement := complementMap A Y
  rows := rowMap A Y

def projectedInput (S : Source) (A : Alphabet s →ₗ[F2] Vector rs)
    (J : Finset (Fin k)) (O : RawPrivateTable.SupportedV J (ActualGame.names S))
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] Visible d A) :
    VisiblePolicies.RightInput S J s d (Vector rs) where
  question := O
  rowMap := A
  complement := complementMap A Y
  rows := rowMap A Y

def policies (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (A : Alphabet s →ₗ[F2] Vector rs) :
    Clean.ActualAdviceStochasticBridge.Policies k (sourceIncidence S) (Visible d A) where
  first _ occ Y := VisiblePolicies.leftPolicy good (fullInput S A occ Y)
  second J O Y := VisiblePolicies.rightPolicy S labeling J (projectedInput S A J O Y)

def actualDraw (S : Source) (A : Alphabet s →ₗ[F2] Vector rs)
    (J : Finset (Fin k)) (occ : Fin k → Fin S.occurrences)
    (slot : Fin k → PartnerProjection.Slot)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s) :
    AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector rs) where
  singletons := J
  occurrences := occ
  positions := slot
  rowMap := A
  hiddenMatrix := M
  complement := T

end

end DFVSGames.Decoder.ActualAdviceUpper
end

section

namespace DFVSGames.Reduction.ActualCompleteness

open DFVSGames.Integration.BinaryLinear
open scoped BigOperators

section Evaluation
variable {E R : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup R] [Module F2 R] [Fintype R] [Fintype (E →ₗ[F2] R)]

theorem expect_linear_eval (τ : E →ₗ[F2] F2) (x : E) (hx : τ x = 1)
    (g : R → ℚ) :
    (𝔼 X : E →ₗ[F2] R, g (X x)) = 𝔼 r : R, g r := by
  classical
  have hinv (r : R) : (𝔼 X : E →ₗ[F2] R, g (X x + r)) =
      𝔼 X : E →ₗ[F2] R, g (X x) := by
    let e : (E →ₗ[F2] R) ≃ (E →ₗ[F2] R) := Equiv.addRight (τ.smulRight r)
    apply Fintype.expect_equiv e
    intro X
    simp [e, hx]
  calc
    (𝔼 X : E →ₗ[F2] R, g (X x)) =
        𝔼 r : R, 𝔼 X : E →ₗ[F2] R, g (X x + r) := by simp only [hinv, Fintype.expect_const]
    _ = 𝔼 X : E →ₗ[F2] R, 𝔼 r : R, g (X x + r) := Finset.expect_comm _ _ _
    _ = 𝔼 r : R, g r := by
      have hshift (a : R) : (𝔼 r : R, g (a + r)) = 𝔼 r : R, g r := by
        apply Fintype.expect_equiv (Equiv.addLeft a)
        intro r
        rfl
      simp only [hshift, Fintype.expect_const]

end Evaluation

open ActualSource

section Noise
variable {E : Type*} [AddCommGroup E] [Module F2 E] {s d : Nat}
  [Fintype (E →ₗ[F2] Ambient s d)] [Fintype (E →ₗ[F2] F2)]

noncomputable def localNoiseFailure (g : SplitGadget s d) (x : E) : ℚ :=
  𝔼 X : E →ₗ[F2] Ambient s d, 𝔼 i : g.NoiseIndex, 𝔼 ell : E →ₗ[F2] F2,
    if g.f (X x + ell x • g.noise i) = g.f (X x) then 0 else 1

theorem localNoiseFailure_eq_half (g : SplitGadget s d)
    (τ : E →ₗ[F2] F2) (x : E) (hx : τ x = 1) :
    localNoiseFailure g x = g.stabilityError / 2 := by
  classical
  have hbit (r v : Ambient s d) :
      (𝔼 b : F2, if g.f (r + b • v) = g.f r then (0 : ℚ) else 1) =
        (if g.f (r + v) = g.f r then (0 : ℚ) else 1) / 2 := by
    have huniv : (Finset.univ : Finset F2) = {0, 1} := by decide
    by_cases h : g.f (r + v) = g.f r <;> simp [Finset.expect, huniv, h]
  have hinner (X : E →ₗ[F2] Ambient s d) (i : g.NoiseIndex) :
      (𝔼 ell : E →ₗ[F2] F2,
        if g.f (X x + ell x • g.noise i) = g.f (X x) then (0 : ℚ) else 1) =
      (if g.f (X x + g.noise i) = g.f (X x) then (0 : ℚ) else 1) / 2 := by
    exact (expect_linear_eval τ x hx
      (fun b => if g.f (X x + b • g.noise i) = g.f (X x) then (0 : ℚ) else 1)).trans
      (hbit (X x) (g.noise i))
  unfold localNoiseFailure
  simp_rw [hinner]
  rw [expect_linear_eval τ x hx (fun r => 𝔼 i : g.NoiseIndex,
    (if g.f (r + g.noise i) = g.f r then (0 : ℚ) else 1) / 2)]
  have hstab : g.stabilityError = 𝔼 r : Ambient s d, 𝔼 i : g.NoiseIndex,
      if g.f (r + g.noise i) = g.f r then (0 : ℚ) else 1 := by
    exact (Finset.expect_product Finset.univ Finset.univ
      (fun ri : Ambient s d × g.NoiseIndex =>
        if g.f (ri.1 + g.noise ri.2) = g.f ri.1 then (0 : ℚ) else 1))
  rw [hstab]
  simp only [div_eq_mul_inv]
  simp_rw [Finset.expect_mul]

end Noise

section Source

noncomputable def tupleFailure (S : Source) (A : Fin S.«variables» → Bool) (k : Nat) : ℚ :=
  𝔼 U : Fin k → Fin S.occurrences,
    if ∀ j, S.satisfied A (U j) = true then 0 else 1

theorem tupleFailure_le (S : Source) (A : Fin S.«variables» → Bool) (k : Nat) :
    tupleFailure S A k ≤ k * S.failure A := by
  classical
  have hpoint (U : Fin k → Fin S.occurrences) :
      (if ∀ j, S.satisfied A (U j) = true then (0 : ℚ) else 1) ≤
        ∑ j : Fin k, if S.satisfied A (U j) then (0 : ℚ) else 1 := by
    by_cases hgood : ∀ j, S.satisfied A (U j) = true
    · simp [hgood]
    · have hex : ∃ j, S.satisfied A (U j) ≠ true := not_forall.mp hgood
      obtain ⟨j, hj⟩ := hex
      have hsum := Finset.single_le_sum
        (f := fun j : Fin k => if S.satisfied A (U j) then (0 : ℚ) else 1)
        (s := Finset.univ) (a := j) (by intro i _; split <;> norm_num)
        (Finset.mem_univ j)
      simpa [hgood, hj] using hsum
  calc
    tupleFailure S A k ≤ 𝔼 U : Fin k → Fin S.occurrences,
        ∑ j : Fin k, if S.satisfied A (U j) then (0 : ℚ) else 1 :=
      Finset.expect_le_expect (fun U _ => hpoint U)
    _ = ∑ j : Fin k, 𝔼 U : Fin k → Fin S.occurrences,
        if S.satisfied A (U j) then (0 : ℚ) else 1 := Finset.expect_sum_comm _ _ _
    _ = k * S.failure A := by
      have hcoord (j : Fin k) :
          (𝔼 U : Fin k → Fin S.occurrences,
            if S.satisfied A (U j) then (0 : ℚ) else 1) = S.failure A :=
        expect_function_apply j (fun e => if S.satisfied A e then (0 : ℚ) else 1)
      simp_rw [hcoord]
      simp

end Source

section HonestEvaluation
open ActualCanonical ActualHomogeneous
variable {Name Id R : Type*} [AddCommGroup R] [Module F2 R] [DecidableEq R] {k : Nat}

def evalTriple (names : Id → Fin 3 → Name) (A : Name → F2) (e : Id)
    (a : Fin 3 → R) : R := ∑ i, A (names e i) • a i

def evalRecord (names : Id → Fin 3 → Name) (A : Name → F2) : Record Name Id R → R
  | .blank => 0
  | .single n c => A n • c
  | .full e a => evalTriple names A e a

def evaluate (names : Id → Fin 3 → Name) (A : Name → F2)
    (d : Data k Name Id R) : R := d.1 + ∑ j, evalRecord names A (d.2 j)

theorem record_eval_normalized (names : Id → Fin 3 → Name) (A : Name → F2)
    (e : Id) (a : Fin 3 → R) :
    evalRecord names A (record names e a) = evalTriple names A e (ActualCanonical.normalize a) := by
  classical
  by_cases h01 : a 0 = a 1
  · by_cases h02 : a 0 = a 2
    · simp_all [record, evalRecord, evalTriple, ActualCanonical.normalize, ActualCanonical.translate, pivot,
        Fin.sum_univ_three, ActualCanonical.add_self]
    · simp_all [record, evalRecord, evalTriple, ActualCanonical.normalize, ActualCanonical.translate, pivot,
        Fin.sum_univ_three, ActualCanonical.add_self]
  · by_cases h02 : a 0 = a 2
    · simp_all [record, evalRecord, evalTriple, ActualCanonical.normalize, ActualCanonical.translate, pivot,
        Fin.sum_univ_three, ActualCanonical.add_self]
    · by_cases h12 : a 1 = a 2
      · simp_all [record, evalRecord, evalTriple, ActualCanonical.normalize, ActualCanonical.translate, pivot,
          Fin.sum_univ_three, ActualCanonical.add_self]
      · simp [record, h01, h02, h12, evalRecord]

theorem record_eval_adjustment (names : Id → Fin 3 → Name) (A : Name → F2)
    (rhs : Id → F2) (e : Id) (a : Fin 3 → R)
    (hvalid : ∑ i, A (names e i) = rhs e) :
    rhs e • pivot a + evalRecord names A (record names e a) = evalTriple names A e a := by
  rw [record_eval_normalized]
  simp only [evalTriple, ActualCanonical.normalize, ActualCanonical.translate, smul_add, Finset.sum_add_distrib,
    ← Finset.sum_smul, hvalid]
  calc
    _ = (∑ i, A (names e i) • a i) + (rhs e • pivot a + rhs e • pivot a) := by abel
    _ = _ := by rw [ActualCanonical.add_self, add_zero]

theorem evaluate_data (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (A : Name → F2) (z : R) (a : Fin k → Fin 3 → R)
    (hvalid : ∀ j, ∑ i, A (names (occ j) i) = rhs (occ j)) :
    evaluate names A (data occ names rhs z a) =
      z + ∑ j, evalTriple names A (occ j) (a j) := by
  simp only [evaluate, data]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => record_eval_adjustment names A rhs (occ j) (a j) (hvalid j))

theorem canonical_evaluate (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (A : Name → F2) (X : E k →ₗ[F2] R)
    (hvalid : ∀ j, ∑ i, A (names (occ j) i) = rhs (occ j)) :
    evaluate names A (canonical occ names rhs X) = X (honestPoint occ names A) := by
  rw [canonical, evaluate_data occ names rhs A _ _ hvalid]
  conv_rhs => rw [ActualHomogeneous.linearMap_expansion]
  simp [honestPoint, evalTriple, standardTriple, Fin.sum_univ_three]

end HonestEvaluation

section ActualLabeling
noncomputable section

def honestVertexLabel (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (A : Fin S.«variables» → Bool) (v : ActualGame.Vertex S k s d) : Alphabet s :=
  g.f ((0, v.val.1) + ∑ j, evalRecord (ActualGame.names S)
    (fun n => ofBit (A n)) (v.val.2 j))

def honestLabeling (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (A : Fin S.«variables» → Bool) :
    Fin (ActualGame.vertexCount S k s d) → Fin (2^s) :=
  ActualGame.labelingOf S k s d (fun _ => honestVertexLabel S k g A)

theorem honest_unfolded (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (A : Fin S.«variables» → Bool) (side : Bool) (q : ActualGame.Query S k s d) :
    ActualGame.unfolded S k s d (honestLabeling S k g A) side q =
      g.f (evaluate (ActualGame.names S) (fun n => ofBit (A n))
        (ActualGame.canonical S k s d q)) := by
  simp only [honestLabeling, ActualGame.unfolded, ActualGame.sideLabel_labelingOf,
    ActualOrbit.unfold]
  let z := (ActualGame.canonical S k s d q).1
  let r := ∑ j, evalRecord (ActualGame.names S) (fun n => ofBit (A n))
    ((ActualGame.canonical S k s d q).2 j)
  change g.f ((0, z.2) + r) + z.1 = g.f (z + r)
  have hsplit : ((0, z.2) + r) + (z.1, 0) = z + r := by
    apply Prod.ext <;> simp [add_comm]
  have h := g.equivariant ((0, z.2) + r) z.1
  rw [hsplit] at h
  exact h.symm

theorem satisfied_parity (S : Source) (A : Fin S.«variables» → Bool)
    (e : Fin S.occurrences) (h : S.satisfied A e = true) :
    ∑ i : Fin 3, ofBit (A (ActualGame.names S e i)) = ActualGame.rhs S e := by
  have hb : ((A (S.equation e).first ^^ A (S.equation e).second) ^^
      A (S.equation e).third) = (S.equation e).rhs := by
    simpa [Source.satisfied, CloneGap.satisfied] using h
  have hf := congrArg ofBit hb
  simpa [Fin.sum_univ_three, ActualGame.names, ActualGame.rhs, ofBit_xor, add_assoc]
    using hf

theorem honest_unfolded_valid (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (A : Fin S.«variables» → Bool) (side : Bool) (q : ActualGame.Query S k s d)
    (hgood : ∀ j, S.satisfied A (q.1 j) = true) :
    ActualGame.unfolded S k s d (honestLabeling S k g A) side q =
      g.f (q.2 (sourcePoint S k A q.1)) := by
  rw [honest_unfolded]
  apply congrArg g.f
  exact canonical_evaluate q.1 (ActualGame.names S) (ActualGame.rhs S)
    (fun n => ofBit (A n)) q.2 (fun j => satisfied_parity S A (q.1 j) (hgood j))

theorem honest_acceptance_bound (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.«variables» → Bool) :
    1 - (k : ℚ) * S.failure A - g.stabilityError / 2 ≤
      ActualGame.acceptanceProbability S k g (honestLabeling S k g A) := by
  classical
  let P (ω : ActualGame.Outcome S k g) : Prop :=
    ActualGame.unfolded S k s d (honestLabeling S k g A) false
        (ActualGame.leftQuery S k g ω) =
      ActualGame.unfolded S k s d (honestLabeling S k g A) true
        (ActualGame.rightQuery S k g ω)
  let bad (ω : ActualGame.Outcome S k g) : ℚ :=
    if ∀ j, S.satisfied A (ω.1.1 j) = true then 0 else 1
  let noiseBad (ω : ActualGame.Outcome S k g) : ℚ :=
    if g.f (ω.1.2 (sourcePoint S k A ω.1.1) +
        ω.2.2 (sourcePoint S k A ω.1.1) • g.noise ω.2.1) =
      g.f (ω.1.2 (sourcePoint S k A ω.1.1)) then 0 else 1
  have hpoint (ω : ActualGame.Outcome S k g) :
      (if P ω then (0 : ℚ) else 1) ≤ bad ω + noiseBad ω := by
    by_cases hgood : ∀ j, S.satisfied A (ω.1.1 j) = true
    · have hL := honest_unfolded_valid S k g A false (ActualGame.leftQuery S k g ω) hgood
      have hR := honest_unfolded_valid S k g A true (ActualGame.rightQuery S k g ω) hgood
      simp only [P, hL, hR, bad, ite_eq_left hgood, zero_add]
      simp [noiseBad, ActualGame.leftQuery, ActualGame.rightQuery,
        LinearMap.add_apply, LinearMap.smulRight_apply, eq_comm]
      exact le_rfl
    · have hn : 0 ≤ noiseBad ω := by dsimp [noiseBad]; split <;> norm_num
      have hf : (if P ω then (0 : ℚ) else 1) ≤ 1 := by split <;> norm_num
      simpa only [bad, ite_eq_right hgood] using hf.trans (le_add_of_nonneg_right hn)
  have hbad : (𝔼 ω : ActualGame.Outcome S k g, bad ω) = tupleFailure S A k := by
    simp only [expect_pair_inline_ActualCompleteness, bad]
    change (𝔼 U : ActualGame.Question S k, 𝔼 _X : ActualGame.Map k s d,
      𝔼 _i : g.NoiseIndex, 𝔼 _ell : ActualGame.Dual k,
      if ∀ j, S.satisfied A (U j) = true then (0 : ℚ) else 1) = _
    simp_rw [Fintype.expect_const]
    rfl
  have hnoise : (𝔼 ω : ActualGame.Outcome S k g, noiseBad ω) = g.stabilityError / 2 := by
    simp only [expect_pair_inline_ActualCompleteness]
    change (𝔼 U : ActualGame.Question S k, localNoiseFailure g (sourcePoint S k A U)) = _
    have hu (U : ActualGame.Question S k) := localNoiseFailure_eq_half g
      ActualHomogeneous.tau (sourcePoint S k A U) (sourcePoint_tau S k A U)
    simp only [hu, Fintype.expect_const]
  have hfailure : (𝔼 ω : ActualGame.Outcome S k g, if P ω then (0 : ℚ) else 1) ≤
      tupleFailure S A k + g.stabilityError / 2 := by
    calc
      _ ≤ 𝔼 ω : ActualGame.Outcome S k g, (bad ω + noiseBad ω) :=
        Finset.expect_le_expect (fun ω _ => hpoint ω)
      _ = _ := by rw [Finset.expect_add_distrib, hbad, hnoise]
  have hsum : ActualGame.acceptanceProbability S k g (honestLabeling S k g A) +
      (𝔼 ω : ActualGame.Outcome S k g, if P ω then (0 : ℚ) else 1) = 1 := by
    rw [ActualGame.acceptanceProbability_eq_test]
    change (𝔼 ω : ActualGame.Outcome S k g, if P ω then (1 : ℚ) else 0) + _ = _
    rw [← Finset.expect_add_distrib]
    have hp (ω : ActualGame.Outcome S k g) :
        (if P ω then (1 : ℚ) else 0) + (if P ω then (0 : ℚ) else 1) = 1 := by
      split <;> norm_num
    simp only [hp, Fintype.expect_const]
  have htuple := tupleFailure_le S A k
  linarith

end
end ActualLabeling

end DFVSGames.Reduction.ActualCompleteness
end

section

namespace DFVSGames.Decoder.TableKeysCompleteness

open DFVSGames.Integration.BinaryLinear DFVSGames.Reduction
open ActualSource Foundations.Target
open TableKeysGame
open scoped BigOperators

noncomputable section

def diagonalLabeling (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    Fin (ActualGame.vertexCount S k s d) → Fin (2^s) :=
  ActualGame.labelingOf S k s d (fun _ => vertexLabel S k s d labeling)

theorem diagonal_unfolded (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s))
    (side : Bool) (q : Query S k s d) :
    ActualGame.unfolded S k s d (diagonalLabeling S k s d labeling) side q =
      unfolded S k s d labeling q := by
  simp only [diagonalLabeling, ActualGame.unfolded,
    ActualGame.sideLabel_labelingOf, unfolded, canonical]

theorem acceptanceProbability_eq_diagonal (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    acceptanceProbability S k g labeling =
      ActualGame.acceptanceProbability S k g (diagonalLabeling S k s d labeling) := by
  rw [acceptanceProbability_eq_test, ActualGame.acceptanceProbability_eq_test]
  simp only [diagonal_unfolded, leftQuery, rightQuery]

def honestLabeling (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (A : Fin S.«variables» → Bool) : Fin (vertexCount S k s d) → Fin (2^s) :=
  labelingOf S k s d (ActualCompleteness.honestVertexLabel S k g A)

theorem diagonal_honestLabeling (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.«variables» → Bool) :
    diagonalLabeling S k s d (honestLabeling S k g A) =
      ActualCompleteness.honestLabeling S k g A := by
  simp only [diagonalLabeling, honestLabeling, vertexLabel_labelingOf,
    ActualCompleteness.honestLabeling]

theorem honest_acceptance_bound (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.«variables» → Bool) :
    1 - (k : ℚ) * S.failure A - g.stabilityError / 2 ≤
      acceptanceProbability S k g (honestLabeling S k g A) := by
  rw [acceptanceProbability_eq_diagonal, diagonal_honestLabeling]
  exact ActualCompleteness.honest_acceptance_bound S k g A

theorem honest_acceptance_of_bounds (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.«variables» → Bool) (ξ p ε : ℚ)
    (hsource : S.failure A ≤ ξ) (hstable : g.stabilityError ≤ p)
    (hbudget : (k : ℚ) * ξ + p / 2 ≤ ε) :
    1 - ε ≤ acceptanceProbability S k g (honestLabeling S k g A) := by
  have hm := mul_le_mul_of_nonneg_left hsource (show (0 : ℚ) ≤ k by positivity)
  have hactual := honest_acceptance_bound S k g A
  linarith

end

end DFVSGames.Decoder.TableKeysCompleteness
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_CanonicalAddress
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Reduction.CanonicalAddress

open CanonicalEncoding

theorem radix_injective_of_length_eq {B : Nat} (hB : 1 < B)
    {xs ys : List Nat} (sameLength : xs.length = ys.length)
    (xsBounded : ∀ w ∈ xs, w < B) (ysBounded : ∀ w ∈ ys, w < B)
    (sameAddress : radix B xs = radix B ys) : xs = ys := by
  have reversed : xs.reverse = ys.reverse :=
    Nat.ofDigits_inj_of_len_eq hB (by simpa only [List.length_reverse] using sameLength)
      (fun w hw => xsBounded w (List.mem_reverse.mp hw))
      (fun w hw => ysBounded w (List.mem_reverse.mp hw)) sameAddress
  have h := congrArg List.reverse reversed
  simpa only [List.reverse_reverse] using h

theorem bodyAddress_injective {n m k s d : Nat} :
    Function.Injective (bodyAddress (n := n) (m := m) (k := k) (s := s) (d := d)) := by
  intro x y h
  apply bodyWords_injective
  exact radix_injective_of_length_eq (one_lt_base n m s d)
    (by simp only [bodyWords_length]) (bodyWords_lt_base x) (bodyWords_lt_base y)
    (congrArg Fin.val h)

@[simp] theorem bodyAddress_eq_iff {n m k s d : Nat} (x y : Body n m k s d) :
    bodyAddress x = bodyAddress y ↔ x = y := bodyAddress_injective.eq_iff

end DFVSGames.Reduction.CanonicalAddress
end

section

namespace DFVSGames.Integration.NoiseTables

open BinaryLinear DFVSGames.Reduction.ActualSource

variable {s d : Nat}

namespace Table

def gadget (T : Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c) : SplitGadget s d where
  f := f
  equivariant := hf
  NoiseIndex := Fin T.vectors.length
  noiseFintype := inferInstance
  noiseNonempty := ⟨⟨0, List.length_pos_iff.mpr T.nonempty⟩⟩
  noise := T.vectors.get

end Table
end DFVSGames.Integration.NoiseTables
end

section

namespace DFVSGames.Integration.TableReduction

open BinaryLinear NoiseTables DFVSGames.Reduction.ActualSource
open DFVSGames.Reduction.ActualGame DFVSGames.Foundations.Target

variable {s d : Nat}

def tableEnumeration (T : Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c) : NoiseEnumeration (T.gadget f hf) where
  indices := List.finRange T.vectors.length
  nodup := List.nodup_finRange _
  complete i := List.mem_finRange i

def tableSkeleton (T : Table s d) : SplitGadget s d :=
  T.gadget Prod.fst (fun _ _ => rfl)

end DFVSGames.Integration.TableReduction
end

section

namespace DFVSGames.Integration.VertexEmbedding

open DFVSGames.Foundations.Target
open GapSemantics TranslationTarget

def embedConstraint {n m q : Nat} (f : Fin n → Fin m) (c : Constraint n q) :
    Constraint m q where
  source := f c.source
  target := f c.target
  permutation := c.permutation

@[simp] theorem embedConstraint_satisfied {n m q : Nat} (f : Fin n → Fin m)
    (c : Constraint n q) (labeling : Fin m → Fin q) :
    (embedConstraint f c).satisfied labeling = c.satisfied (labeling ∘ f) := rfl

@[simp] theorem embedConstraint_permutation {n m q : Nat} (f : Fin n → Fin m)
    (c : Constraint n q) : (embedConstraint f c).permutation = c.permutation := rfl

theorem count_map {n m q : Nat} (f : Fin n → Fin m)
    (constraints : List (Constraint n q)) (labeling : Fin m → Fin q) :
    countSatisfied labeling (constraints.map (embedConstraint f)) =
      countSatisfied (labeling ∘ f) constraints := by
  induction constraints with
  | nil => rfl
  | cons c cs ih =>
      by_cases hc : c.satisfied (labeling ∘ f) = true <;> simp [countSatisfied, ih, hc]

def embedInstance {q m : Nat} (g : Instance q) (f : Fin g.vertices → Fin m)
    (_hf : Function.Injective f) : Instance q where
  vertices := m
  constraints := g.constraints.map (embedConstraint f)
  nonempty h := g.nonempty (List.map_eq_nil_iff.mp h)

@[simp] theorem embedInstance_vertices {q m : Nat} (g : Instance q)
    (f : Fin g.vertices → Fin m) (hf : Function.Injective f) :
    (embedInstance g f hf).vertices = m := rfl

@[simp] theorem embedInstance_length {q m : Nat} (g : Instance q)
    (f : Fin g.vertices → Fin m) (hf : Function.Injective f) :
    (embedInstance g f hf).constraints.length = g.constraints.length := List.length_map _

@[simp] theorem extendLabeling_apply {n m q : Nat} (f : Fin n → Fin m)
    (hf : Function.Injective f) (labeling : Fin n → Fin q)
    (defaultLabel : Fin q) (v : Fin n) :
    extendLabeling f labeling defaultLabel (f v) = labeling v := by
  classical
  have hx : ∃ u, f u = f v := ⟨v, rfl⟩
  rw [extendLabeling, dite_eq_left hx]
  exact congrArg labeling (hf (Classical.choose_spec hx))

theorem extendLabeling_comp {n m q : Nat} (f : Fin n → Fin m)
    (hf : Function.Injective f) (labeling : Fin n → Fin q) (defaultLabel : Fin q) :
    extendLabeling f labeling defaultLabel ∘ f = labeling := by
  funext v
  exact extendLabeling_apply f hf labeling defaultLabel v

end DFVSGames.Integration.VertexEmbedding
end

section

namespace DFVSGames.Decoder.TableKeysAddressGame

open DFVSGames.Reduction
open ActualSource Foundations.Target
open Integration.VertexEmbedding

abbrev vertexCount (S : Source) (k s d : Nat) : Nat :=
  CanonicalAddress.capacity S.«variables» S.occurrences k s d

def vertexAddress (S : Source) (k s d : Nat) (v : TableKeysGame.Vertex S k s d) :
    Fin (vertexCount S k s d) := CanonicalAddress.bodyAddress v.val

theorem vertexAddress_injective (S : Source) (k s d : Nat) :
    Function.Injective (vertexAddress S k s d) := by
  intro v w h
  apply Subtype.ext
  exact CanonicalAddress.bodyAddress_injective h

def queryAddress (S : Source) (k s d : Nat) (q : TableKeysGame.Query S k s d) :
    Fin (vertexCount S k s d) :=
  CanonicalAddress.bodyAddress (ActualOrbit.body (TableKeysGame.canonical S k s d) q)

@[simp] theorem vertexAddress_query (S : Source) (k s d : Nat)
    (q : TableKeysGame.Query S k s d) :
    vertexAddress S k s d (TableKeysGame.vertex S k s d q) =
      queryAddress S k s d q := rfl

def explicitToAddress (S : Source) (k s d : Nat) :
    Fin (TableKeysGame.explicitVertexCount S k s d) → Fin (vertexCount S k s d) :=
  fun i => vertexAddress S k s d ((TableKeysGame.explicitVertexEncoding S k s d).symm i)

theorem explicitToAddress_injective (S : Source) (k s d : Nat) :
    Function.Injective (explicitToAddress S k s d) :=
  (vertexAddress_injective S k s d).comp
    (TableKeysGame.explicitVertexEncoding S k s d).symm.injective

@[simp] theorem explicitToAddress_apply (S : Source) (k s d : Nat)
    (v : TableKeysGame.Vertex S k s d) :
    explicitToAddress S k s d (TableKeysGame.explicitVertexEncoding S k s d v) =
      vertexAddress S k s d v := by
  simp only [explicitToAddress, Equiv.symm_apply_apply]

def addressEdge (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (ω : TableKeysGame.Outcome S k g) : Constraint (vertexCount S k s d) (2^s) where
  source := queryAddress S k s d (TableKeysGame.leftQuery S k g ω)
  target := queryAddress S k s d (TableKeysGame.rightQuery S k g ω)
  permutation := Encoding.translationTable
    (TableKeysGame.offset S k s d (TableKeysGame.leftQuery S k g ω))
    (TableKeysGame.offset S k s d (TableKeysGame.rightQuery S k g ω))

theorem addressEdge_eq_embed (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (ω : TableKeysGame.Outcome S k g) :
    addressEdge S k g ω = embedConstraint (explicitToAddress S k s d)
      (TableKeysGame.explicitEdge S k g ω) := by
  simp only [addressEdge, embedConstraint, TableKeysGame.explicitEdge,
    explicitToAddress_apply, vertexAddress_query]

def outputInstance (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (en : NoiseEnumeration g) : Instance (2^s) where
  vertices := vertexCount S k s d
  constraints := (ActualGame.explicitOutcomes S k g en).map (addressEdge S k g)
  nonempty h := by
    have hempty := List.map_eq_nil_iff.mp h
    apply (TableKeysGame.outputInstanceWithEnumeration S k g en).nonempty
    change (ActualGame.explicitOutcomes S k g en).map (TableKeysGame.explicitEdge S k g) = []
    rw [hempty]
    rfl

@[simp] theorem outputInstance_length (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (outputInstance S k g en).constraints.length =
      Explicit.edgeCount S.occurrences k (s+d) en.indices.length := by
  simp only [outputInstance, List.length_map, ActualGame.explicitOutcomes,
    ActualEnumeration.length_indexedOutcomes]

theorem outputInstance_count (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    countSatisfied labeling (outputInstance S k g en).constraints =
      countSatisfied (labeling ∘ explicitToAddress S k s d)
        (TableKeysGame.outputInstanceWithEnumeration S k g en).constraints := by
  simpa only [outputInstance, TableKeysGame.outputInstanceWithEnumeration, List.map_map,
    Function.comp_def, ← addressEdge_eq_embed] using
    count_map (explicitToAddress S k s d)
      ((ActualGame.explicitOutcomes S k g en).map (TableKeysGame.explicitEdge S k g)) labeling

theorem outputInstance_translations (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    Integration.TranslationTarget.IsTranslationInstance (Encoding.alphabetEquiv s).symm
      (outputInstance S k g en) := by
  intro constraint hconstraint
  obtain ⟨ω, _, rfl⟩ := List.mem_map.mp hconstraint
  refine ⟨TableKeysGame.offset S k s d (TableKeysGame.leftQuery S k g ω) +
    TableKeysGame.offset S k s d (TableKeysGame.rightQuery S k g ω), ?_⟩
  intro label
  have h := Encoding.translationTable_images
    (TableKeysGame.offset S k s d (TableKeysGame.leftQuery S k g ω))
    (TableKeysGame.offset S k s d (TableKeysGame.rightQuery S k g ω))
    ((Encoding.alphabetEquiv s).symm label)
  simpa only [addressEdge, Encoding.alphabetEquiv_apply_symm_apply,
    Encoding.alphabetEquiv_symm_apply_apply, add_assoc] using
    congrArg (Encoding.alphabetEquiv s).symm h

def tableOutput (S : Source) (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d) :
    Instance (2^s) :=
  outputInstance S k (Integration.TableReduction.tableSkeleton T)
    (Integration.TableReduction.tableEnumeration T Prod.fst (fun _ _ => rfl))

theorem tableOutput_eq_with_witness (S : Source) (k : Nat) {s d : Nat}
    (T : Integration.NoiseTables.Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c) :
    tableOutput S k T = outputInstance S k (T.gadget f hf)
      (Integration.TableReduction.tableEnumeration T f hf) := by
  rfl

theorem tableOutput_translations (S : Source) (k : Nat) {s d : Nat}
    (T : Integration.NoiseTables.Table s d) :
    Integration.TranslationTarget.IsTranslationInstance (Encoding.alphabetEquiv s).symm
      (tableOutput S k T) := outputInstance_translations S k _ _

end DFVSGames.Decoder.TableKeysAddressGame
end

section

namespace DFVSGames.Decoder.MatrixGap

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction DFVSGames.Foundations.Target
open DFVSGames.Integration
open ActualSource

noncomputable section

theorem address_rate_eq_semantic_acceptance (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g)
    (labeling : Fin (TableKeysAddressGame.vertexCount S k s d) → Fin (2 ^ s)) :
    GapSemantics.satisfactionRate (TableKeysAddressGame.outputInstance S k g en) labeling =
      TableKeysGame.acceptanceProbability S k g
        ((labeling ∘ TableKeysAddressGame.explicitToAddress S k s d) ∘
          TableKeysGame.semanticToExplicitVertices S k s d) := by
  calc
    _ = GapSemantics.satisfactionRate
        (TableKeysGame.outputInstanceWithEnumeration S k g en)
        (labeling ∘ TableKeysAddressGame.explicitToAddress S k s d) := by
      unfold GapSemantics.satisfactionRate
      exact congrArg₂ (fun a b : Nat => (a : ℚ) / b)
        (TableKeysAddressGame.outputInstance_count S k g en labeling)
        (by simp only [TableKeysAddressGame.outputInstance,
          TableKeysGame.outputInstanceWithEnumeration, List.length_map])
    _ = GapSemantics.satisfactionRate (TableKeysGame.outputInstance S k g)
        ((labeling ∘ TableKeysAddressGame.explicitToAddress S k s d) ∘
          TableKeysGame.semanticToExplicitVertices S k s d) :=
      InstanceEquivalences.satisfactionRate_eq_of_rename_perm
        (TableKeysGame.outputInstance S k g)
        (TableKeysGame.outputInstanceWithEnumeration S k g en)
        (TableKeysGame.semanticToExplicitVertices S k s d)
        (TableKeysGame.explicitConstraints_perm_renamed S k g en) _
    _ = _ := (TableKeysGame.acceptanceProbability_eq_count S k g _).symm

end

end DFVSGames.Decoder.MatrixGap
end

section

namespace DFVSGames.Decoder.MatrixGap

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction DFVSGames.Foundations.Target
open DFVSGames.Integration
open ActualSource

noncomputable section

theorem semantic_acceptance_le_address_value (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) :
    (TableKeysGame.acceptanceProbability S k g labeling : ℝ) ≤
      InstanceValue.value (TableKeysAddressGame.outputInstance S k g en) := by
  let e := TableKeysGame.semanticToExplicitVertices S k s d
  let addressLabel := VertexEmbedding.extendLabeling
    (TableKeysAddressGame.explicitToAddress S k s d) (labeling ∘ e.symm)
      (⟨0, by positivity⟩ : Fin (2 ^ s))
  have hrestrict : addressLabel ∘ TableKeysAddressGame.explicitToAddress S k s d =
      labeling ∘ e.symm :=
    VertexEmbedding.extendLabeling_comp _
      (TableKeysAddressGame.explicitToAddress_injective S k s d) _ _
  have hpullback : (addressLabel ∘ TableKeysAddressGame.explicitToAddress S k s d) ∘
      TableKeysGame.semanticToExplicitVertices S k s d = labeling := by
    rw [hrestrict]
    funext v
    exact congrArg labeling (e.symm_apply_apply v)
  have hrate := address_rate_eq_semantic_acceptance S k g en addressLabel
  rw [hpullback] at hrate
  have hvalue := InstanceValue.satisfactionRate_le_value
    (TableKeysAddressGame.outputInstance S k g en) addressLabel
  rw [hrate] at hvalue
  exact hvalue

theorem address_value_ge_of_near_assignment (S : Source) (k : Nat) {s d : Nat}
    (T : NoiseTables.Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c)
    (assignment : Fin S.«variables» → Bool) (ξ p : ℚ)
    (hfailure : S.failure assignment ≤ ξ)
    (hstable : (T.gadget f hf).stabilityError ≤ p) :
    (1 : ℝ) - ((k : ℝ) * (ξ : ℝ) + (p : ℝ) / 2) ≤
      InstanceValue.value (TableKeysAddressGame.tableOutput S k T) := by
  let g := T.gadget f hf
  have hrat := TableKeysCompleteness.honest_acceptance_of_bounds S k g assignment
    ξ p ((k : ℚ) * ξ + p / 2) hfailure hstable (le_refl _)
  have hreal : (1 : ℝ) - ((k : ℝ) * (ξ : ℝ) + (p : ℝ) / 2) ≤
      (TableKeysGame.acceptanceProbability S k g
        (TableKeysCompleteness.honestLabeling S k g assignment) : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).2 hrat
    simpa only [Rat.cast_sub, Rat.cast_one, Rat.cast_add, Rat.cast_mul,
      Rat.cast_natCast, Rat.cast_div, Rat.cast_ofNat] using h
  rw [TableKeysAddressGame.tableOutput_eq_with_witness S k T f hf]
  exact hreal.trans (semantic_acceptance_le_address_value S k g
    (TableReduction.tableEnumeration T f hf)
    (TableKeysCompleteness.honestLabeling S k g assignment))

end
end DFVSGames.Decoder.MatrixGap

end

section

namespace DFVSGames.Decoder.MatrixGap

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction DFVSGames.Foundations.Target
open DFVSGames.Foundations.Games
open DFVSGames.Integration
open ActualSource

noncomputable section
attribute [local instance] Classical.propDecidable

structure Parameters (p : ℚ) where
  k : Nat
  s : Nat
  d : Nat
  k_pos : 1 ≤ k
  s_pos : 1 ≤ s
  T : NoiseTables.Table s d
  f : Ambient s d → Alphabet s
  equivariant : ∀ x c, f (x + (c, 0)) = f x + c
  stability : (T.gadget f equivariant).stabilityError ≤ p
  sound : ∀ S : Source, S.DistinctNames →
    Clean.IncidenceGap.parityValue (ActualAdviceUpper.sourceIncidence S)
      (FiniteDistribution.uniform (Fin S.occurrences)) ≤ (4 : ℝ) / 5 →
    InstanceValue.value (TableKeysAddressGame.tableOutput S k T) ≤ (99 : ℝ) / 100

namespace Parameters

variable {p : ℚ}

def output (P : Parameters p) (S : Source) : Instance (2 ^ P.s) :=
  TableKeysAddressGame.tableOutput S P.k P.T

theorem completeness (P : Parameters p) (S : Source)
    (assignment : Fin S.«variables» → Bool) (ξ : ℚ)
    (hfailure : S.failure assignment ≤ ξ) :
    (1 : ℝ) - ((P.k : ℝ) * (ξ : ℝ) + (p : ℝ) / 2) ≤
      InstanceValue.value (TableKeysAddressGame.tableOutput S P.k P.T) :=
  address_value_ge_of_near_assignment S P.k P.T P.f P.equivariant assignment
    ξ p hfailure P.stability

theorem output_translations (P : Parameters p) (S : Source) :
    TranslationTarget.IsTranslationInstance (Encoding.alphabetEquiv P.s).symm
      (P.output S) :=
  TableKeysAddressGame.tableOutput_translations S P.k P.T

end Parameters

end

end DFVSGames.Decoder.MatrixGap
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ProfileCorrection
attribute [-instance] _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def revealLaw (μ : FiniteDistribution (X × Y)) :
    FiniteDistribution ((X × Y) × (X ⊕ Y)) :=
  (μ.product (FiniteDistribution.uniform Bool)).pushforward
    (fun z => (z.1, revealEndpoint z.1 z.2))

def revealFirstLaw (μ : FiniteDistribution (X × Y)) :
    FiniteDistribution ((X ⊕ Y) × (X × Y)) :=
  (revealLaw μ).transport (Equiv.prodComm _ _)

omit [DecidableEq X] [DecidableEq Y] in
@[simp] theorem revealFirstLaw_weight (μ : FiniteDistribution (X × Y))
    (r : X ⊕ Y) (q : X × Y) :
    (revealFirstLaw μ).weight (r,q) = (revealLaw μ).weight (q,r) := rfl

end
end DFVSGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_Bounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineFieldProfile

open Turing

section Transport
variable {K Λ σ τ : Type} [DecidableEq K]

def normalState (ambient : σ) : MachineCompare.State σ := (ambient, false, none, none)

end Transport


end DFVSGames.Foundations.Complexity.MachineFieldProfile


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_SignaturePrepare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceSignaturePrepare

open Turing
open Target PCP SourceContexts SourceOccurrences SourceLocalSignature
open DFVSGames.Foundations.Complexity

abbrev Arena (u : ℕ) (Extra : Type) := SourceContextLoad.Tape u Extra

end DFVSGames.Foundations.Hastad.SourceSignaturePrepare


namespace DFVSGames.Foundations.Complexity.MachineStateFrame

open Turing

variable {K Λ Λ' σ τ : Type} {Γ : K → Type}

variable [DecidableEq K]

theorem frame_advance (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    (c : Option (TM2.Cfg Γ Λ σ)) :
    MachineComposition.advance (TM2.step (frameProgram source))
        (c.map (frameConfiguration ambient)) =
      (MachineComposition.advance (TM2.step source) c).map (frameConfiguration ambient) := by
  cases c with
  | none => rfl
  | some c => exact frame_step source ambient c

theorem frame_iterate (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    (steps : ℕ) (c : Option (TM2.Cfg Γ Λ σ)) :
    (MachineComposition.advance (TM2.step (frameProgram source)))^[steps]
        (c.map (frameConfiguration ambient)) =
      ((MachineComposition.advance (TM2.step source))^[steps] c).map
        (frameConfiguration ambient) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact frame_advance source ambient _

def frameExecution (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    {start : TM2.Cfg Γ Λ σ} {finish : Option (TM2.Cfg Γ Λ σ)} {budget : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step source) start finish budget) :
    StateTransition.EvalsToInTime (TM2.step (frameProgram source))
      (frameConfiguration ambient start) (finish.map (frameConfiguration ambient)) budget where
  steps := run.steps
  evals_in_steps := by
    have h := run.evals_in_steps
    change (MachineComposition.advance (TM2.step source))^[run.steps] (some start) = finish at h
    change (MachineComposition.advance (TM2.step (frameProgram source)))^[run.steps]
      ((some start).map (frameConfiguration ambient)) = finish.map (frameConfiguration ambient)
    rw [frame_iterate, h]
  steps_le_m := run.steps_le_m

@[simp] theorem frameExecution_steps (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    {start : TM2.Cfg Γ Λ σ} {finish : Option (TM2.Cfg Γ Λ σ)} {budget : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step source) start finish budget) :
    (frameExecution source ambient run).steps = run.steps := rfl

end DFVSGames.Foundations.Complexity.MachineStateFrame


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ExpanderFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.PCP.ExpanderTables

open PoweringWalks SpectralReturn

theorem rowIndex_val (v d : Nat) (x : Fin v × Fin d) :
    (rowIndex v d x).val = x.2.val + d * x.1.val := rfl

def vertexIndex (v q : Nat) : Fin v × (Fin q × Fin q) ≃ Fin (v * (q * q)) :=
  (Equiv.prodCongr (Equiv.refl _) (rowIndex q q)).trans (rowIndex v (q * q))

end DFVSGames.Foundations.PCP.ExpanderTables


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineCloudCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.Complexity.MachineCloudCount

open Turing
open MachineComposition

abbrev Alphabet (_ : Tape) := Bool

open DFVSGames.Foundations.PCP

end DFVSGames.Foundations.Complexity.MachineCloudCount

namespace DFVSGames.Foundations.Complexity.MachineCeilingPower

open Turing
open MachineComposition
open DFVSGames.Foundations.PCP

abbrev Alphabet (_ : Tape) := Bool

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

def scaleLoop (g : Nat) : TM2.Stmt Alphabet Label (State σ) :=
  .pop .power (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (Reduction.MachineSubstitution.pushWord .product (List.replicate g true)
        (.goto fun _ => .scale))
      (.push .power (fun _ => false)
        (.push .level (fun _ => true)
          (.load (fun state => (state.1, none)) (.goto fun _ => .transfer)))))

end DFVSGames.Foundations.Complexity.MachineCeilingPower

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineCloudPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.Complexity.MachineCloudPadding

open Turing
open MachineComposition
open DFVSGames.Foundations.PCP

namespace Placement

variable {K K' Λ Λ' σ : Type}

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

end Placement

end DFVSGames.Foundations.Complexity.MachineCloudPadding

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_VerifierCNF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.VerifierToCNF

open Target

def liftLiteral {q : Nat} (V : FiniteVerifier q) (l : Literal V.«variables») :
    Literal (outputVariables V) := ⟨oldIndex V l.variableIndex, l.positive⟩

def forbiddenLiteral {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) (i : Fin q) : Literal V.«variables» :=
  ⟨V.query e i, !(patternAt q p i)⟩

def forbiddenClause {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) : List (Literal (outputVariables V)) :=
  List.ofFn (fun i => liftLiteral V (forbiddenLiteral V e p i))

def mismatchBits {q : Nat} (V : FiniteVerifier q) (A : Fin V.«variables» → Bool)
    (e : Fin V.events) (p : PatternIndex q) : List Bool :=
  List.ofFn (fun i => (forbiddenLiteral V e p i).eval A)

@[simp] theorem mismatchBits_length {q : Nat} (V : FiniteVerifier q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (mismatchBits V A e p).length = q := by simp [mismatchBits]

theorem mismatchFill_length {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (fillBits (mismatchBits V A e p)).length = q - 3 := by
  have h := fillBits_length (mismatchBits V A e p) (by simpa using hq)
  rw [mismatchBits_length] at h
  omega

def mismatchFill {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q)
    (j : Fin (q - 3)) : Bool :=
  (fillBits (mismatchBits V A e p))[j.val]'(by
    rw [mismatchFill_length V hq A e p]
    exact j.isLt)

def extendAssignment {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) : Fin (outputVariables V) → Bool :=
  Fin.addCases A (fun k : Fin (auxiliaryCount V) =>
    let pair : Fin (V.events * (patterns q).length) × Fin (q - 3) := finProdFinEquiv.symm k
    let ep : Fin V.events × PatternIndex q := finProdFinEquiv.symm pair.1
    mismatchFill V hq A ep.1 ep.2 pair.2)

@[simp] theorem extend_old {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (v : Fin V.«variables») :
    extendAssignment V hq A (oldIndex V v) = A v := by
  simp [extendAssignment, oldIndex]

@[simp] theorem extend_fresh {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q)
    (j : Fin (q - 3)) :
    extendAssignment V hq A (freshIndex V e p j) = mismatchFill V hq A e p j := by
  unfold extendAssignment freshIndex auxiliaryCount
  rw [Fin.addCases_right]
  simp only [Equiv.symm_apply_apply]

@[simp] theorem restrict_extend {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) : restrictAssignment V (extendAssignment V hq A) = A := by
  funext v
  exact extend_old V hq A v

end DFVSGames.Foundations.PCP.VerifierToCNF

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_InitialGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.RawInitialTables

open Target GraphTables

def binaryOrder (n : Nat) : (Fin n → Bool) ≃ Fin (2 ^ n) where
  toFun bits := (DFVSGames.Integration.BinaryCoordinates.pack bits).toFin
  invFun index := DFVSGames.Integration.BinaryCoordinates.unpack (BitVec.ofFin index)
  left_inv bits := DFVSGames.Integration.BinaryCoordinates.unpack_pack bits
  right_inv index := by
    change (DFVSGames.Integration.BinaryCoordinates.pack
      (DFVSGames.Integration.BinaryCoordinates.unpack (BitVec.ofFin index))).toFin = index
    rw [DFVSGames.Integration.BinaryCoordinates.pack_unpack]

end DFVSGames.Foundations.PCP.RawInitialTables

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineStateEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.Complexity.MachineStateEquiv

open Turing.TM2

variable {K Λ σ τ : Type} {Γ : K → Type}

variable [DecidableEq K]

theorem advance_transport (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    (c : Option (Cfg Γ Λ σ)) :
    MachineComposition.advance (step (program e source)) (c.map (configuration e)) =
      (MachineComposition.advance (step source) c).map (configuration e) := by
  cases c with
  | none => rfl
  | some c => exact step_transport e source c

theorem iterate_transport (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) (n : Nat)
    (c : Option (Cfg Γ Λ σ)) :
    (MachineComposition.advance (step (program e source)))^[n]
        (c.map (configuration e)) =
      ((MachineComposition.advance (step source))^[n] c).map (configuration e) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, advance_transport,
        Function.iterate_succ_apply']

theorem trace_iff (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) (n : Nat)
    (a b : Cfg Γ Λ σ) :
    (MachineComposition.advance (step (program e source)))^[n]
        (some (configuration e a)) = some (configuration e b) ↔
      (MachineComposition.advance (step source))^[n] (some a) = some b := by
  change (MachineComposition.advance (step (program e source)))^[n]
      ((some a).map (configuration e)) = (some b).map (configuration e) ↔ _
  rw [iterate_transport]
  constructor
  · intro h
    apply Option.map_injective (configurationEquiv e).injective
    change ((MachineComposition.advance (step source))^[n] (some a)).map (configuration e) =
      (some b).map (configuration e)
    exact h
  · exact congrArg (Option.map (configuration e))

theorem trace (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) (n : Nat)
    (a b : Cfg Γ Λ σ)
    (run : (MachineComposition.advance (step source))^[n] (some a) = some b) :
    (MachineComposition.advance (step (program e source)))^[n]
      (some (configuration e a)) = some (configuration e b) :=
  (trace_iff e source n a b).2 run

def execution (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (run : StateTransition.EvalsToInTime (step source) start finish budget) :
    StateTransition.EvalsToInTime (step (program e source))
      (configuration e start) (finish.map (configuration e)) budget where
  steps := run.steps
  evals_in_steps := by
    have h := run.evals_in_steps
    change (MachineComposition.advance (step source))^[run.steps] (some start) = finish at h
    change (MachineComposition.advance (step (program e source)))^[run.steps]
      ((some start).map (configuration e)) = finish.map (configuration e)
    rw [iterate_transport, h]
  steps_le_m := run.steps_le_m

@[simp] theorem execution_steps (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (run : StateTransition.EvalsToInTime (step source) start finish budget) :
    (execution e source run).steps = run.steps := rfl

def execution_reflect (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (run : StateTransition.EvalsToInTime (step (program e source))
      (configuration e start) (finish.map (configuration e)) budget) :
    StateTransition.EvalsToInTime (step source) start finish budget where
  steps := run.steps
  evals_in_steps := by
    change (MachineComposition.advance (step source))^[run.steps] (some start) = finish
    apply Option.map_injective (configurationEquiv e).injective
    change ((MachineComposition.advance (step source))^[run.steps] (some start)).map
      (configuration e) = finish.map (configuration e)
    rw [← iterate_transport]
    exact run.evals_in_steps
  steps_le_m := run.steps_le_m

@[simp] theorem execution_reflect_steps (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (run : StateTransition.EvalsToInTime (step (program e source))
      (configuration e start) (finish.map (configuration e)) budget) :
    (execution_reflect e source run).steps = run.steps := rfl

end DFVSGames.Foundations.Complexity.MachineStateEquiv

namespace DFVSGames.Foundations.Complexity.MachineUnaryEqualityBit

open Turing
open MachineComposition

variable {K Λ A : Type} [DecidableEq K]

instance instFintypeLabel : Fintype Label where
  elems := {.seedLeft, .scanLeft, .restoreLeft, .seedRight, .scanRight,
    .restoreRight, .compare, .equal, .different}
  complete label := by cases label <;> simp

end DFVSGames.Foundations.Complexity.MachineUnaryEqualityBit

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachinePreservingLookupClean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineCloudRank

open Turing MachineComposition MachineCloudCount

variable {σ : Type}

@[simp] theorem update_memory_spare (a b c d e f x : List Bool) :
    Function.update (memory a b c d e f) .spare x = memory a b c d e x := by
  funext k
  cases k <;> rfl

open DFVSGames.Foundations.PCP

end DFVSGames.Foundations.Complexity.MachineCloudRank

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineCloudSelect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineCloudSelect

open Turing MachineComposition

abbrev BaseTape := MachineCloudCount.Tape
abbrev BaseAlphabet := MachineCloudCount.Alphabet

variable {σ : Type}

abbrev Tape := BaseTape ⊕ Unit
abbrev Alphabet : Tape → Type := MachineEmbedding.Alphabet BaseAlphabet (fun _ : Unit => Bool)

def memory (original work target scratch hit rank position : List Bool) :
    ∀ k, List (Alphabet k) :=
  MachineEmbedding.tapes (MachineCloudCount.memory original work target scratch hit rank)
    (fun _ : Unit => position)

@[simp] theorem memory_inl (a b c d e f g : List Bool) (k : BaseTape) :
    memory a b c d e f g (.inl k) = MachineCloudCount.memory a b c d e f k := rfl
@[simp] theorem memory_position (a b c d e f g : List Bool) :
    memory a b c d e f g (.inr ()) = g := rfl

open DFVSGames.Foundations.PCP

end DFVSGames.Foundations.Complexity.MachineCloudSelect


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineRegularMetadata
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.PCP.ExpanderRowControl

open ExpanderTables

def outputPort {d : Nat} (s : Control d) : Fin (degree d) :=
  rowIndex d d (s.lastH.2,s.firstH.2)

def firstAddress {d : Nat} (vertex : Nat) (s : Control d) : Nat :=
  degree d * vertex + (firstOffset s).val

def secondAddress {d : Nat} (vertex : Nat) (s : Control d) : Nat :=
  degree d * vertex + (secondOffset s).val

end DFVSGames.Foundations.PCP.ExpanderRowControl
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_ExpanderTableWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineFixedDivMod

open Turing
open Reduction.MachineSubstitution (pushWord stepAux_pushWord )

variable {K Λ σ : Type} [DecidableEq K]

def emitterWithFinish [Fintype σ] (d : Nat) (positive : 0 < d) (remainder : K)
    (exit : Option Λ) (finish : σ → Fin d → σ) (r : Fin d) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ d) :=
  pushWord remainder (List.replicate r.val true)
    (.load (fun state => ((finish state.1.1 r, residue d positive 0), none))
      (Reduction.MachineTransfer.exitAt remainder exit))

end DFVSGames.Foundations.Complexity.MachineFixedDivMod

end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

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

end DFVSGames.Foundations.Complexity.MachineExpanderRow
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_RawInitialMachineFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine

open Turing
open PCP

namespace Program

open PCP.AlphabetTable

def headRoles : Fin 6 → Tape :=
  Fin.cases .archive (Fin.cases .reverseIndex (Fin.cases .scanWork
    (Fin.cases .indexWork (Fin.cases .head (fun _ => .scratch)))))

end Program

end DFVSGames.Foundations.Complexity.FinalCNFMachine
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_PoweringMachineWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineInitialize

open Turing
open PoweringMachineLoop

theorem boolAlphabet_eq_inline_PoweringMachineInitialize (max : Nat) :
    MachineEmbedding.Alphabet HeaderAlphabet (fun _ : ExtraTape max => Bool) =
      (fun _ : GlobalTape max => Bool) := by
  funext tape
  cases tape <;> rfl

end DFVSGames.Foundations.Complexity.PoweringMachineInitialize
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_Clone100Counting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Explicit.MachineClone100Model

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad

def contextScale {D : Nat} : Context D → Nat
  | .inl j => if j.val = 0 then 100 else D
  | .inr p => if p.2.val < 3 then 100 else 1

def contextOffset (triples : List (Nat × Nat × Nat)) : Context triples.length → Nat
  | .inl _ => 0
  | .inr p => tripleField (triples.get p.1) p.2

end DFVSGames.Explicit.MachineClone100Model
end

section

namespace DFVSGames.Explicit.MachineClone100Context

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity
open MachineClone100Model

theorem contextSource_ne_reversed {D : Nat} (context : Context D) :
    contextSource context ≠ Tape.reversed := by
  cases context with
  | inl slot =>
    simp only [contextSource, headerTape]
    split <;> simp
  | inr pair => simp [contextSource]

end DFVSGames.Explicit.MachineClone100Context
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_MachineClone100Finish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.BinaryValidatorMachine

open BinaryEncoding BinaryFormula

theorem finalDigit_true_iff_inline_MachineBinaryValidatorMachine (bits : List Bool) :
    BinaryNameMachine.finalDigit bits (some true) = some true ↔
      BinaryNameMachine.canonical bits = true := by
  cases bits with
  | nil => simp [BinaryNameMachine.finalDigit, BinaryNameMachine.canonical]
  | cons bit bits =>
      simp only [BinaryNameMachine.finalDigit, BinaryNameMachine.canonical]
      have hsome : ∀ (ds : List Bool) (b : Bool),
          ∃ last, BinaryNameMachine.finalDigit ds (some b) = some last := by
        intro ds
        induction ds with
        | nil => intro b; exact ⟨b, rfl⟩
        | cons d ds ih => intro b; exact ih d
      obtain ⟨last, hlast⟩ := hsome bits bit
      rw [hlast]
      simp

theorem run_frame (slot : Fin 3) (bits rest : List Bool) (last : Bool)
    (valid : BinaryNameMachine.finalDigit bits (some last) = some true) :
    run (.name slot last) (frame bits ++ rest) = run (afterName slot) rest := by
  induction bits generalizing last with
  | nil =>
      have hlast : last = true := by simpa [BinaryNameMachine.finalDigit] using valid
      subst last
      simp [frame, run, nextMode]
  | cons bit bits ih =>
      have hvalid : BinaryNameMachine.finalDigit bits (some bit) = some true := valid
      simpa only [frame, List.cons_append, run, nextMode] using ih bit hvalid

theorem run_name (slot : Fin 3) (name : Nat) (rest : List Bool) :
    run (.name slot true) (nameBits name ++ rest) = run (afterName slot) rest := by
  apply run_frame
  exact (finalDigit_true_iff_inline_MachineBinaryValidatorMachine name.bits).mpr (BinaryParsing.canonical_nat_bits name)

theorem run_literal (slot : Fin 3) (literal : Literal) (rest : List Bool) :
    run (.sign slot) (literalBits literal ++ rest) = run (afterName slot) rest := by
  simpa only [literalBits, List.cons_append, run, nextMode] using
    run_name slot literal.name rest

theorem run_clause (clause : Clause) (rest : List Bool) :
    run (.sign 0) (clauseBits clause ++ rest) = run .clause rest := by
  simp [clauseBits, List.append_assoc, run_literal, afterName]

theorem run_clauses (clauses : List Clause) : run .clause (clausesBits clauses) = .done := by
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      change run (.sign 0) (clauseBits clause ++ clausesBits clauses) = .done
      rw [run_clause, ih]

theorem run_formula (formula : Formula) : run .clause (formulaBits formula) = .done :=
  run_clauses formula.clauses

theorem frame_inverse (slot : Fin 3) (last : Bool) (input : List Bool)
    (accepted : run (.name slot last) input = .done) :
    ∃ bits rest, input = frame bits ++ rest ∧
      BinaryNameMachine.finalDigit bits (some last) = some true ∧
      run (afterName slot) rest = .done := by
  induction input using List.twoStepInduction generalizing last with
  | nil => simp [run] at accepted
  | singleton flag =>
      cases flag with
      | false =>
          cases last with
          | false => simp [run, nextMode] at accepted
          | true =>
              exact ⟨[], [], rfl, rfl, by simpa [run, nextMode] using accepted⟩
      | true => simp [run, nextMode] at accepted
  | cons_cons flag bit input ih _ =>
      cases flag with
      | false =>
          cases last with
          | false => simp [run, nextMode] at accepted
          | true =>
              exact ⟨[], bit :: input, rfl, rfl,
                by simpa [run, nextMode] using accepted⟩
      | true =>
          have haccepted : run (.name slot bit) input = .done := by
            simpa only [run, nextMode] using accepted
          obtain ⟨bits, rest, hinput, hvalid, hrest⟩ := ih bit haccepted
          refine ⟨bit :: bits, rest, ?_, hvalid, hrest⟩
          simp [frame, hinput]

theorem name_inverse (slot : Fin 3) (input : List Bool)
    (accepted : run (.name slot true) input = .done) :
    ∃ name rest, input = nameBits name ++ rest ∧ run (afterName slot) rest = .done := by
  obtain ⟨bits, rest, hinput, hvalid, hrest⟩ := frame_inverse slot true input accepted
  have hcanonical := (finalDigit_true_iff_inline_MachineBinaryValidatorMachine bits).mp hvalid
  have hbits := (BinaryParsing.canonical_iff bits).mp hcanonical
  refine ⟨bitsValue bits, rest, ?_, hrest⟩
  simpa only [nameBits, hbits] using hinput

theorem literal_inverse (slot : Fin 3) (input : List Bool)
    (accepted : run (.sign slot) input = .done) :
    ∃ literal rest, input = literalBits literal ++ rest ∧ run (afterName slot) rest = .done := by
  cases input with
  | nil => simp [run] at accepted
  | cons sign input =>
      have haccepted : run (.name slot true) input = .done := accepted
      obtain ⟨name, rest, hinput, hrest⟩ := name_inverse slot input haccepted
      refine ⟨⟨name, sign⟩, rest, ?_, hrest⟩
      simp [literalBits, hinput]

theorem clause_inverse (input : List Bool) (accepted : run (.sign 0) input = .done) :
    ∃ clause rest, input = clauseBits clause ++ rest ∧ run .clause rest = .done := by
  obtain ⟨a, afterA, hA, acceptedA⟩ := literal_inverse 0 input accepted
  have hacceptedA : run (.sign 1) afterA = .done := by
    simpa [afterName] using acceptedA
  obtain ⟨b, afterB, hB, acceptedB⟩ := literal_inverse 1 afterA hacceptedA
  have hacceptedB : run (.sign 2) afterB = .done := by
    simpa [afterName] using acceptedB
  obtain ⟨c, rest, hC, acceptedC⟩ := literal_inverse 2 afterB hacceptedB
  have hrest : run .clause rest = .done := by simpa [afterName] using acceptedC
  refine ⟨#v[a, b, c], rest, ?_, hrest⟩
  simp [clauseBits, hA, hB, hC, List.append_assoc]

theorem clauses_inverse_aux_inline_MachineBinaryValidatorMachine (fuel : Nat) (input : List Bool)
    (enough : input.length < fuel) (accepted : run .clause input = .done) :
    ∃ clauses, input = clausesBits clauses := by
  induction fuel generalizing input with
  | zero => omega
  | succ fuel ih =>
      cases input with
      | nil => simp [run] at accepted
      | cons flag input =>
          cases flag with
          | false =>
              have hdone : run .done input = .done := accepted
              have hempty := (run_done_iff input).mp hdone
              subst input
              exact ⟨[], rfl⟩
          | true =>
              have haccepted : run (.sign 0) input = .done := accepted
              obtain ⟨clause, rest, hinput, hrest⟩ := clause_inverse input haccepted
              have hlength := congrArg List.length hinput
              simp only [List.length_append] at hlength
              have henough : rest.length < fuel := by
                simp only [List.length_cons] at enough
                omega
              obtain ⟨clauses, hclauses⟩ := ih rest henough hrest
              refine ⟨clause :: clauses, ?_⟩
              simp [clausesBits, hinput, hclauses]

theorem run_clause_iff (input : List Bool) :
    run .clause input = .done ↔ ∃ formula, input = formulaBits formula := by
  constructor
  · intro accepted
    obtain ⟨clauses, hclauses⟩ :=
      clauses_inverse_aux_inline_MachineBinaryValidatorMachine (input.length + 1) input (by omega) accepted
    exact ⟨⟨clauses⟩, hclauses⟩
  · rintro ⟨formula, rfl⟩
    exact run_formula formula

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition

end DFVSGames.BinaryValidatorMachine

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineBinaryTotalInputMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.BinaryTotalInputMachine

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition
open DFVSGames.Reduction.MachineTransfer
open DFVSGames.Reduction.MachineSubstitution
open BinaryValidatorMachine (Mode nextMode run)

def rejectedWord : List Bool := BinaryEncoding.formulaBits BinaryLanguage.rejectBinary

end DFVSGames.BinaryTotalInputMachine

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineBinaryTokenMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.BinaryTokenMachine

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition
open DFVSGames.Reduction.MachineTransfer
open BinaryFormula BinaryEncoding

def tokens (clauses : List Clause) : List Bool := clauses.flatMap clauseBits

@[simp] theorem tokens_nil : tokens [] = [] := rfl

@[simp] theorem tokens_cons (clause : Clause) (clauses : List Clause) :
    tokens (clause :: clauses) = clauseBits clause ++ tokens clauses := by
  simp [tokens]

@[simp] theorem tokens_length (clauses : List Clause) :
    (tokens clauses).length = 6 * clauses.length + 2 * namesBitSize clauses := by
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      simp only [tokens_cons, List.length_append, clauseBits_length, ih,
        List.length_cons, namesBitSize_cons]
      omega

theorem tokenSteps_le (formula : Formula) :
    13 * formula.clauses.length + 3 * namesBitSize formula.clauses + 3 ≤
      3 * (formulaBits formula).length + 3 := by
  rw [BinaryEncoding.formulaBits_length]
  omega

end DFVSGames.BinaryTokenMachine

end

section

namespace DFVSGames.BinaryRenameWords

open BinaryFormula DFVSGames.Foundations

def clauseLiterals (c : Clause) : List Literal := [(c)[0], (c)[1], (c)[2]]

def literals (clauses : List Clause) : List Literal := clauses.flatMap clauseLiterals

def token (literal : Literal) : BinaryNameSearch.Token :=
  (literal.positive, literal.name.bits)

def tokens (clauses : List Clause) : List BinaryNameSearch.Token :=
  (literals clauses).map token

@[simp] theorem literals_nil : literals [] = [] := rfl

@[simp] theorem literals_cons (c : Clause) (cs : List Clause) :
    literals (c :: cs) = (c)[0] :: (c)[1] :: (c)[2] :: literals cs := rfl

@[simp] theorem literals_length (cs : List Clause) :
    (literals cs).length = 3 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [literals_cons, List.length_cons, ih]; omega

@[simp] theorem tokens_length (cs : List Clause) :
    (tokens cs).length = 3 * cs.length := by simp [tokens]

theorem literals_names (F : Formula) :
    (literals F.clauses).map Literal.name = sourceNames F := by
  simp only [literals, sourceNames, List.map_flatMap]
  rfl

theorem tokens_payloads (F : Formula) :
    BinaryNameSearch.payloads (tokens F.clauses) = (sourceNames F).map Nat.bits := by
  rw [← literals_names]
  simp only [BinaryNameSearch.payloads, tokens, List.map_map, token, Function.comp_def]

theorem token_bits (literal : Literal) :
    BinaryNameSearch.tokenBits (token literal) = BinaryEncoding.literalBits literal := by
  simp only [BinaryNameSearch.tokenBits, token, BinaryEncoding.literalBits,
    BinaryEncoding.nameBits, BinaryParsing.frame_eq]

theorem tokens_stream (cs : List Clause) :
    BinaryNameSearch.stream (tokens cs) = BinaryTokenMachine.tokens cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [tokens, literals_cons, List.map_cons, BinaryNameSearch.stream_cons,
        token_bits, BinaryTokenMachine.tokens_cons, BinaryEncoding.clauseBits]
      simpa only [tokens, List.append_assoc] using
        congrArg (fun tail => BinaryEncoding.literalBits (c)[0] ++
          BinaryEncoding.literalBits (c)[1] ++ BinaryEncoding.literalBits (c)[2] ++ tail) ih

theorem tokens_canonical (cs : List Clause) :
    ∀ t ∈ tokens cs, BinaryNameMachine.canonical t.2 = true := by
  intro t mem
  obtain ⟨literal, _, rfl⟩ := List.mem_map.mp mem
  exact BinaryParsing.canonical_nat_bits literal.name

theorem payload_index (F : Formula) (name : Nat) :
    (BinaryNameSearch.payloads (tokens F.clauses)).idxOf name.bits =
      (sourceNames F).idxOf name := by
  rw [tokens_payloads, BinaryOccurrenceRename.idxOf_binary_payloads]

end DFVSGames.BinaryRenameWords

end

section

namespace DFVSGames.BinaryHeaderMachine

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition
open DFVSGames.Reduction.MachineTransfer

section Placement

variable {K Λ A : Type} [DecidableEq K]

@[simp] theorem tapes_variables (variableTape clauses destination : K)
    (vc : variableTape ≠ clauses) (vd : variableTape ≠ destination) (base : K → List Bool)
    (variableCounter clauseCounter output : List Bool) :
    tapes variableTape clauses destination base variableCounter clauseCounter output variableTape =
      variableCounter := by
  simp [tapes, vc, vd]

@[simp] theorem tapes_clauses (variableTape clauses destination : K)
    (cd : clauses ≠ destination) (base : K → List Bool)
    (variableCounter clauseCounter output : List Bool) :
    tapes variableTape clauses destination base variableCounter clauseCounter output clauses =
      clauseCounter := by
  simp [tapes, cd]

@[simp] theorem tapes_destination (variableTape clauses destination : K) (base : K → List Bool)
    (variableCounter clauseCounter output : List Bool) :
    tapes variableTape clauses destination base variableCounter clauseCounter output destination =
      output := by
  simp [tapes]

theorem update_variables_inline_MachineBinaryHeaderMachine (variableTape clauses destination : K)
    (vc : variableTape ≠ clauses) (vd : variableTape ≠ destination) (base : K → List Bool)
    (variableCounter clauseCounter output replacement : List Bool) :
    Function.update (tapes variableTape clauses destination base variableCounter clauseCounter output)
      variableTape replacement = tapes variableTape clauses destination base replacement clauseCounter output := by
  funext k
  by_cases hv : k = variableTape
  · subst k
    simp [tapes, vc, vd]
  · by_cases hd : k = destination
    · subst k
      simp [tapes, hv]
    · by_cases hc : k = clauses
      · subst k
        simp [tapes, hv, hd]
      · simp [tapes, hv, hc, hd]

theorem update_clauses_inline_MachineBinaryHeaderMachine (variableTape clauses destination : K)
    (cd : clauses ≠ destination) (base : K → List Bool)
    (variableCounter clauseCounter output replacement : List Bool) :
    Function.update (tapes variableTape clauses destination base variableCounter clauseCounter output)
      clauses replacement = tapes variableTape clauses destination base variableCounter replacement output := by
  funext k
  by_cases hc : k = clauses
  · subst k
    simp [tapes, cd]
  · by_cases hd : k = destination
    · subst k
      simp [tapes, hc]
    · simp [tapes, hc, hd]

theorem update_destination_inline_MachineBinaryHeaderMachine (variableTape clauses destination : K) (base : K → List Bool)
    (variableCounter clauseCounter output replacement : List Bool) :
    Function.update (tapes variableTape clauses destination base variableCounter clauseCounter output)
      destination replacement = tapes variableTape clauses destination base variableCounter clauseCounter replacement := by
  simp [tapes]

variable (variableTape clauses destination : K)
variable (vc : variableTape ≠ clauses) (vd : variableTape ≠ destination) (cd : clauses ≠ destination)
variable (clauseStart clauseLoop variableStart variableLoop : Λ) (exit : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atClauseStart : program clauseStart = delimiter destination clauseLoop)
variable (atVariableStart : program variableStart = delimiter destination variableLoop)
variable (base : K → List Bool) (ambient : A)

include atClauseStart in
theorem clauseDelimiterStep (variableCounter clauseCounter output : List Bool)
    (register : Option Bool) :
    TM2.step program
      ⟨some clauseStart, (ambient, register),
        tapes variableTape clauses destination base variableCounter clauseCounter output⟩ =
      some ⟨some clauseLoop, (ambient, none),
        tapes variableTape clauses destination base variableCounter clauseCounter (false :: output)⟩ := by
  change some (TM2.stepAux (program clauseStart) _ _) = _
  rw [atClauseStart]
  simp [delimiter, TM2.stepAux, update_destination_inline_MachineBinaryHeaderMachine]

include atVariableStart in
theorem variableDelimiterStep (variableCounter clauseCounter output : List Bool)
    (register : Option Bool) :
    TM2.step program
      ⟨some variableStart, (ambient, register),
        tapes variableTape clauses destination base variableCounter clauseCounter output⟩ =
      some ⟨some variableLoop, (ambient, none),
        tapes variableTape clauses destination base variableCounter clauseCounter (false :: output)⟩ := by
  change some (TM2.stepAux (program variableStart) _ _) = _
  rw [atVariableStart]
  simp [delimiter, TM2.stepAux, update_destination_inline_MachineBinaryHeaderMachine]

end Placement

end DFVSGames.BinaryHeaderMachine

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineBinaryRenameMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.BinaryRenameMachine

open Turing DFVSGames.Foundations
open Complexity Complexity.MachineComposition
open DFVSGames.Reduction.MachineTransfer

theorem clause_count_le_stream (formula : BinaryFormula.Formula) :
    formula.clauses.length ≤ (BinaryTokenMachine.tokens formula.clauses).length := by
  rw [BinaryTokenMachine.tokens_length]
  omega

end DFVSGames.BinaryRenameMachine

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineSingleOrbitCodec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Explicit.MachineSingleOrbitCodec

open DFVSGames.Foundations.Target DFVSGames.Foundations.Complexity

def doubleConstraint {n q : Nat} (c : Constraint n q) : Constraint (2 * n) q where
  source := ⟨c.source.val, by have := c.source.isLt; omega⟩
  target := ⟨n + c.target.val, by have := c.target.isLt; omega⟩
  permutation := c.permutation

end DFVSGames.Explicit.MachineSingleOrbitCodec
end

section

namespace DFVSGames.Reduction.SourceEquationLookup

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineComposition SourceMachine SourceEncoding
variable {σ : Type}

def scanTapes (base : Tape → List Bool) (index : Nat)
    (indexSuffix input : List Bool) : Tape → List Bool :=
  MachineUnaryCounter.counterTapes .index (Function.update base .work input) index indexSuffix

end DFVSGames.Reduction.SourceEquationLookup
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineTemplateAddress
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Reduction.MachineTemplateAddress

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad

variable {q width : Nat} {K Λ σ : Type} [DecidableEq K]

def hornerLayout : MachineHorner.Layout width ↪ Tape q width where
  toFun
    | .inl 0 => .radix
    | .inl 1 => .accA
    | .inl 2 => .accB
    | .inl 3 => .output
    | .inl 4 => .counter
    | .inl 5 => .hornerScratch
    | .inr i => .digit i
  inj' := by
    rintro (a | a) (b | b) h
    · fin_cases a <;> fin_cases b <;> simp_all
    · fin_cases a <;> simp_all
    · fin_cases b <;> simp_all
    · exact congrArg Sum.inr (Tape.digit.inj h)

def hornerSlots (slots : Tape q width ↪ K) : MachineHorner.Layout width ↪ K :=
  hornerLayout.trans slots

def resultTapes (slots : Tape q width ↪ K) (base : K → List Bool) (value : Nat) :
    K → List Bool := Function.update base (slots .output) (encodeWord value ++ base (slots .output))

@[simp] theorem resultTapes_output (slots : Tape q width ↪ K) (base : K → List Bool) (value : Nat) :
    resultTapes slots base value (slots .output) = encodeWord value ++ base (slots .output) := by
  simp [resultTapes]

end DFVSGames.Reduction.MachineTemplateAddress
end

section

namespace DFVSGames.Reduction.MachineAddressEdge

open Turing
open DFVSGames.Foundations.Complexity
open MachineSubstitution (pushWord stepAux_pushWord)

abbrev Tape (q width : Nat) := MachineTemplateAddress.Tape q width ⊕ Fin 2

variable {q width : Nat} {K Λ σ : Type} [DecidableEq K]

def addressSlots (slots : Tape q width ↪ K) : MachineTemplateAddress.Tape q width ↪ K where
  toFun tape := slots (.inl tape)
  inj' := by intro a b h; exact Sum.inl.inj (slots.injective h)

def capacityTape (slots : Tape q width ↪ K) : K := slots (.inr 0)
def outputTape (slots : Tape q width ↪ K) : K := slots (.inr 1)
def workTape (slots : Tape q width ↪ K) : K := addressSlots slots .output
def tempTape (slots : Tape q width ↪ K) : K := addressSlots slots .forward
def scratchTape (slots : Tape q width ↪ K) : K := addressSlots slots .copyScratch

omit [DecidableEq K] in
theorem address_ne_output (slots : Tape q width ↪ K) (tape : MachineTemplateAddress.Tape q width) :
    addressSlots slots tape ≠ outputTape slots := slots.injective.ne (by simp)

omit [DecidableEq K] in
theorem capacity_ne_output (slots : Tape q width ↪ K) :
    capacityTape slots ≠ outputTape slots := slots.injective.ne (by simp)

def appended (slots : Tape q width ↪ K) (base : K → List Bool) (bits : List Bool) :
    K → List Bool := MachineFieldTemplate.outputTapes base (outputTape slots) bits

@[simp] theorem appended_address (slots : Tape q width ↪ K) (base : K → List Bool)
    (bits : List Bool) (tape : MachineTemplateAddress.Tape q width) :
    appended slots base bits (addressSlots slots tape) = base (addressSlots slots tape) :=
  MachineFieldTemplate.outputTapes_other base (outputTape slots) bits _
    (address_ne_output slots tape)

@[simp] theorem appended_capacity (slots : Tape q width ↪ K) (base : K → List Bool)
    (bits : List Bool) : appended slots base bits (capacityTape slots) = base (capacityTape slots) :=
  MachineFieldTemplate.outputTapes_other base (outputTape slots) bits _ (capacity_ne_output slots)

@[simp] theorem appended_output (slots : Tape q width ↪ K) (base : K → List Bool)
    (bits : List Bool) :
    appended slots base bits (outputTape slots) = bits.reverse ++ base (outputTape slots) := by
  exact MachineFieldTemplate.outputTapes_output _ _ _

end DFVSGames.Reduction.MachineAddressEdge
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_CanonicalWordTemplate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Reduction.CanonicalWordTemplate

open Foundations.Complexity CanonicalEncoding

def singleTemplate {s d : Nat} (index : Fin 3) (coefficient : Ambient s d) : List Token :=
  [.literal 1, .name index, .literal 0,
    .literal (vectorWord coefficient.1), .literal (vectorWord coefficient.2),
    .literal 0, .literal 0, .literal 0, .literal 0]

def fullTemplate {s d : Nat} (coefficients : Fin 3 → Ambient s d) : List Token :=
  [.literal 2, .literal 0, .occurrence,
    .literal (vectorWord (coefficients 0).1), .literal (vectorWord (coefficients 0).2),
    .literal (vectorWord (coefficients 1).1), .literal (vectorWord (coefficients 1).2),
    .literal (vectorWord (coefficients 2).1), .literal (vectorWord (coefficients 2).2)]

def template {s d : Nat} (a : Fin 3 → Ambient s d) : List Token :=
  if a 0 = a 1 then
    if a 0 = a 2 then blankTemplate else singleTemplate 2 (a 2 + a 0)
  else if a 0 = a 2 then singleTemplate 1 (a 1 + a 0)
  else if a 1 = a 2 then singleTemplate 0 (a 0 + a 2)
  else fullTemplate (ActualCanonical.normalize a)

@[simp] theorem singleTemplate_length {s d : Nat} (index : Fin 3)
    (coefficient : Ambient s d) : (singleTemplate index coefficient).length = 9 := rfl

@[simp] theorem fullTemplate_length {s d : Nat} (coefficients : Fin 3 → Ambient s d) :
    (fullTemplate coefficients).length = 9 := rfl

@[simp] theorem template_length {s d : Nat} (a : Fin 3 → Ambient s d) :
    (template a).length = 9 := by
  unfold template
  split_ifs <;> rfl

@[simp] theorem evalTemplate_length (names : Fin 3 → Nat) (occurrence : Nat)
    (tokens : List Token) : (evalTemplate names occurrence tokens).length = tokens.length :=
  List.length_map _

@[simp] theorem variableTokens_blankTemplate : variableTokens blankTemplate = [] := rfl

@[simp] theorem variableTokens_singleTemplate {s d : Nat} (index : Fin 3)
    (coefficient : Ambient s d) :
    variableTokens (singleTemplate index coefficient) = [.name index] := rfl

@[simp] theorem variableTokens_fullTemplate {s d : Nat}
    (coefficients : Fin 3 → Ambient s d) :
    variableTokens (fullTemplate coefficients) = [.occurrence] := rfl

end DFVSGames.Reduction.CanonicalWordTemplate
end

section

namespace DFVSGames.Reduction.CanonicalBodyTemplate

open Integration.BinaryLinear Foundations.Complexity CanonicalEncoding
open scoped BigOperators

variable {k : Nat}

@[simp] theorem recordFields_name (names : Fin 3 → Nat) (occurrence : Nat) (j : Fin 3) :
    recordFields names occurrence (nameField j) = names j := by
  simp [recordFields, nameField, j.isLt]

def liftToken (j : Fin k) : CanonicalWordTemplate.Token → Token k
  | .literal value => .literal value
  | .name index => .field j (nameField index)
  | .occurrence => .field j 3

def liftRecord (j : Fin k) (tokens : List CanonicalWordTemplate.Token) : List (Token k) :=
  tokens.map (liftToken j)

@[simp] theorem liftRecord_length (j : Fin k) (tokens : List CanonicalWordTemplate.Token) :
    (liftRecord j tokens).length = tokens.length := List.length_map _

def recordsList {k s d : Nat} (a : Fin k → Fin 3 → Ambient s d)
    (positions : List (Fin k)) : List (Token k) :=
  positions.flatMap (fun j => liftRecord j (CanonicalWordTemplate.template (a j)))

theorem recordsList_length {k s d : Nat} (a : Fin k → Fin 3 → Ambient s d)
    (positions : List (Fin k)) : (recordsList a positions).length = 9 * positions.length := by
  induction positions with
  | nil => rfl
  | cons j positions ih =>
    change (liftRecord j (CanonicalWordTemplate.template (a j)) ++
      recordsList a positions).length = 9 * (positions.length + 1)
    rw [List.length_append, liftRecord_length, CanonicalWordTemplate.template_length, ih]
    omega

def ambientShift {k s d : Nat} (z : Ambient s d)
    (a : Fin k → Fin 3 → Ambient s d) (b : Fin k → F2) : Ambient s d :=
  z + ∑ j, b j • ActualCanonical.pivot (a j)

def alphabetOffset {k s d : Nat} (z : Ambient s d)
    (a : Fin k → Fin 3 → Ambient s d) (b : Fin k → F2) : Vector s :=
  (ambientShift z a b).1

def template {k s d : Nat} (z : Ambient s d)
    (a : Fin k → Fin 3 → Ambient s d) (b : Fin k → F2) : List (Token k) :=
  .literal (vectorWord (ambientShift z a b).2) :: recordsList a (List.ofFn id)

@[simp] theorem template_length {k s d : Nat} (z : Ambient s d)
    (a : Fin k → Fin 3 → Ambient s d) (b : Fin k → F2) :
    (template z a b).length = 1 + 9*k := by
  simp [template, recordsList_length, Nat.add_comm]

end DFVSGames.Reduction.CanonicalBodyTemplate
end

section

namespace DFVSGames.Reduction.CanonicalBodyMachine

open Integration.BinaryLinear Foundations.Complexity CanonicalEncoding

variable {k : Nat}

@[simp] theorem fieldIndex_val (position : Fin k) (field : Fin 4) :
    (fieldIndex position field).val = field.val + 4 * position.val := rfl

end DFVSGames.Reduction.CanonicalBodyMachine
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_UniformReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Reduction.AddressGame

open ActualSource
open Foundations.Target
open Integration.VertexEmbedding

abbrev bodyCapacity (S : Source) (k s d : Nat) : Nat :=
  CanonicalAddress.capacity S.«variables» S.occurrences k s d

def vertexCount (S : Source) (k s d : Nat) : Nat := 2 * bodyCapacity S k s d

def vertexAddress (S : Source) (k s d : Nat) (v : ActualGame.TwoSidedVertex S k s d) :
    Fin (vertexCount S k s d) :=
  Encoding.sideEquiv (bodyCapacity S k s d) (v.1, CanonicalAddress.bodyAddress v.2.val)

def queryAddress (S : Source) (k s d : Nat) (side : Bool) (q : ActualGame.Query S k s d) :
    Fin (vertexCount S k s d) :=
  Encoding.sideEquiv (bodyCapacity S k s d)
    (side, CanonicalAddress.bodyAddress (ActualOrbit.body (ActualGame.canonical S k s d) q))

@[simp] theorem vertexAddress_query (S : Source) (k s d : Nat) (side : Bool)
    (q : ActualGame.Query S k s d) :
    vertexAddress S k s d (side, ActualGame.vertex S k s d q) =
      queryAddress S k s d side q := rfl

end DFVSGames.Reduction.AddressGame
end

section

namespace DFVSGames.Reduction.FixedOutcomes

open Integration.BinaryLinear ActualHomogeneous ActualSource
open ActualEnumeration _root_.OAI.DFVSGames.Reduction.Explicit

variable {N : Type*}

def occurrenceTuples (m k : Nat) : List (Fin k → Fin m) :=
  functions (List.finRange m) k

end DFVSGames.Reduction.FixedOutcomes
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_AddressTupleBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Reduction.AddressOdometerSchedule

open Turing
open DFVSGames.Foundations.Complexity MachineTupleOdometer
open DFVSGames.Foundations.Hastad
open MachineTransfer

noncomputable section

variable {k s d noiseCount m : ℕ} {Λ σ : Type}

def allBits {q : ℕ} (bits : (Fin q → Fin m) → List Bool) : List Bool :=
  (tupleOrder m q).flatMap bits

end
end DFVSGames.Reduction.AddressOdometerSchedule
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_ActualGoodRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.RowErasure

noncomputable section

variable {X Y A S D : Type*}

theorem SliceFamily.selectedDescription_of_good (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) :
    F.selectedDescription f α a s = some (F.chosenDescription f α a s hgood) := by
  simp only [SliceFamily.selectedDescription, dite_eq_left hgood]

theorem SliceFamily.selectedEvent_iff_of_advice (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) (x : X) (hx : F.advice a x = s) :
    F.selectedEvent f α a x ↔ x ∈ F.points (F.chosenDescription f α a s hgood) := by
  unfold SliceFamily.selectedEvent
  rw [hx, F.selectedDescription_of_good f α a s hgood]
  constructor
  · rintro ⟨d, hd, hmem⟩
    have he := Option.some.inj hd
    simpa only [he] using hmem
  · intro hmem
    exact ⟨_, rfl, hmem⟩

end
end DFVSGames.Inverse.RowErasure

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_StageData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace DFVSGames.Appendix.Restriction

open scoped BigOperators
open DFVSGames.Fourier.MatrixCharacters DFVSGames.Fourier.MatrixFourier
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

def compressFrequency (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) : B →ₗ[F2] (E ⧸ A) :=
  A.mkQ.comp (Y.comp B.subtype)

end DFVSGames.Appendix.Restriction
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Derivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace DFVSGames.Appendix.Derivatives
open scoped BigOperators
open DFVSGames.Fourier.MatrixCharacters DFVSGames.Fourier.MatrixFourier
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

def spectralProjector (P : (F →ₗ[F2] E) → Prop) (f : (E →ₗ[F2] F) → ℝ) :
    (E →ₗ[F2] F) → ℝ :=
  ∑ Y with P Y, linearCoeff f Y • (fun X => (linearTraceCharacter Y X).re)

def hybridProjector (A : Submodule F2 E) (B : Submodule F2 F)
    (f : (E →ₗ[F2] F) → ℝ) : (E →ₗ[F2] F) → ℝ :=
  spectralProjector (fun Y => LinearIdentities.Hybrid Y A B) f

def hybridDerivative (A : Submodule F2 E) (B : Submodule F2 F)
    (T : E →ₗ[F2] F) (f : (E →ₗ[F2] F) → ℝ) :
    DFVSGames.Fourier.MatrixRestrictions.Parameter A B → ℝ :=
  DFVSGames.Fourier.MatrixRestrictions.restrict (hybridProjector A B f) A B T

def rankProjector (X : F →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ) :
    (E →ₗ[F2] F) → ℝ :=
  spectralProjector (fun Y => RankAdditivity.RankBelow X Y) f

def selectorMultiplicity {I : Type*} [Fintype I]
    (P : I → (F →ₗ[F2] E) → Prop) (Y : F →ₗ[F2] E) : ℕ :=
  (Finset.univ.filter (fun i : I => P i Y)).card

variable [Finite E] [Finite F]

def HybridIndex (d : ℕ) :=
  {p : Submodule F2 E × Submodule F2 F //
    DFVSGames.Fourier.MatrixRestrictions.order p.1 p.2 ≤ d}

noncomputable instance hybridIndexFintype (d : ℕ) :
    Fintype (HybridIndex (E := E) (F := F) d) := by
  letI : Finite (Submodule F2 E) :=
    Finite.of_injective (fun A : Submodule F2 E => (A : Set E)) SetLike.coe_injective
  letI : Finite (Submodule F2 F) :=
    Finite.of_injective (fun B : Submodule F2 F => (B : Set F)) SetLike.coe_injective
  unfold HybridIndex
  exact Fintype.ofFinite _

def hybridMomentSum (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ s : HybridIndex (E := E) (F := F) d,
    𝔼 T, (𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2) ^ 2

def hybridSelectorEnergy (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ s : HybridIndex (E := E) (F := F) d,
    𝔼 X, hybridProjector s.val.1 s.val.2 f X ^ 2

end DFVSGames.Appendix.Derivatives
end

noncomputable section

namespace DFVSGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters DFVSGames.Fourier.MatrixFourier
open DFVSGames.Appendix DFVSGames.Appendix.Derivatives

variable {A U B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C]

omit [FiniteDimensional F2 A] [FiniteDimensional F2 U] [FiniteDimensional F2 B] [FiniteDimensional F2 C] in

@[simp] theorem productFrequencyEquiv_compressFrequency
    (S : (B × C) →ₗ[F2] (A × U)) :
    productFrequencyEquiv (Restriction.compressFrequency
      (LinearMap.range (LinearMap.inl F2 A U))
      (LinearMap.range (LinearMap.inl F2 B C)) S) =
      (LinearMap.snd F2 A U).comp (S.comp (LinearMap.inl F2 B C)) := by
  apply LinearMap.ext
  intro b
  rfl

end DFVSGames.Inverse.KMSAnalyticHybridEnergy

end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSAnalyticHybridEnergyFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSAnalytic

noncomputable section
open scoped Classical
open DFVSGames.Fourier.MatrixCharacters

variable {E F J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup J] [Module F2 J]

def pointAppend (X : E →ₗ[F2] F) (a : F) : (E × F2) →ₗ[F2] F :=
  X.coprod (LinearMap.toSpanSingleton F2 F a)

@[simp] theorem pointAppend_apply (X : E →ₗ[F2] F) (a : F) (x : E) (c : F2) :
    pointAppend X a (x, c) = X x + c • a := rfl

end
end DFVSGames.Inverse.KMSAnalytic

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_NaturalTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace DFVSGames.Appendix.NaturalTransport
open scoped BigOperators
open DFVSGames.Fourier.MatrixCharacters DFVSGames.Fourier.MatrixFourier
open DFVSGames.Fourier.MatrixRestrictions
open DFVSGames.Appendix.Derivatives DFVSGames.Appendix.RankAdditivity
attribute [local instance] Classical.propDecidable

local instance naturalTransportQuotientFinite
    {V : Type*} [AddCommGroup V] [Module F2 V] [Finite V]
    (P : Submodule F2 V) : Finite (V ⧸ P) :=
  Finite.of_surjective P.mkQ P.mkQ_surjective

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

def quotientFactor (A : Submodule F2 E) (C : Submodule F2 (E ⧸ A)) :
    (E ⧸ C.comap A.mkQ) ≃ₗ[F2] ((E ⧸ A) ⧸ C) :=
  (Submodule.quotEquivOfEq (C.comap A.mkQ) (C.mkQ.comp A.mkQ).ker
    (by rw [LinearMap.ker_comp, Submodule.ker_mkQ])).trans
      ((C.mkQ.comp A.mkQ).quotKerEquivOfSurjective
        (C.mkQ_surjective.comp A.mkQ_surjective))

omit [FiniteDimensional F2 E] [Finite E] in
@[simp] theorem quotientFactor_mkQ (A : Submodule F2 E)
    (C : Submodule F2 (E ⧸ A)) (x : E) :
    quotientFactor A C ((C.comap A.mkQ).mkQ x) = C.mkQ (A.mkQ x) := by
  simp [quotientFactor]

def outputFactor (B : Submodule F2 F) (D : Submodule F2 B) :
    D ≃ₗ[F2] (D.map B.subtype) :=
  Submodule.equivMapOfInjective B.subtype Subtype.val_injective D

omit [FiniteDimensional F2 F] [Finite F] in
@[simp] theorem outputFactor_val (B : Submodule F2 F) (D : Submodule F2 B) (x : D) :
    ((outputFactor B D x : D.map B.subtype) : F) = ((x : B) : F) := rfl

def dualFactor (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) :
    (D →ₗ[F2] ((E ⧸ A) ⧸ C)) ≃ₗ[F2]
      ((D.map B.subtype) →ₗ[F2] (E ⧸ C.comap A.mkQ)) :=
  LinearEquiv.arrowCongr (outputFactor B D) (quotientFactor A C).symm

end DFVSGames.Appendix.NaturalTransport
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_KMSFourthMomentMixedRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSFourthMoment

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters

variable {A I F : Type*}
  [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup F] [Module F2 F]

def partialRestrict (f : ((A × I) →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F) :
    (I →ₗ[F2] F) → ℝ := fun X => f (a.coprod X)

@[simp] theorem partialRestrict_apply
    (f : ((A × I) →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F)
    (X : I →ₗ[F2] F) : partialRestrict f a X = f (a.coprod X) := rfl

end
end DFVSGames.Inverse.KMSFourthMoment

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_KMSFourthMomentZoomTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSFourthMoment

noncomputable section
open scoped Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Inverse.KMSAnalytic

variable {A0 A I F : Type*}
  [AddCommGroup A0] [Module F2 A0]
  [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup F] [Module F2 F]

def pointShuffle (e : (A0 × F2) ≃ₗ[F2] A) :
    ((A0 × I) × F2) ≃ₗ[F2] (A × I) where
  toFun p := (e (p.1.1, p.2), p.1.2)
  invFun p := (((e.symm p.1).1, p.2), (e.symm p.1).2)
  left_inv p := by
    rcases p with ⟨⟨u, v⟩, c⟩
    simp
  right_inv p := by
    rcases p with ⟨u, v⟩
    simp
  map_add' p q := by
    apply Prod.ext
    · change e (p.1.1 + q.1.1, p.2 + q.2) =
        e (p.1.1, p.2) + e (q.1.1, q.2)
      exact map_add e (p.1.1, p.2) (q.1.1, q.2)
    · rfl
  map_smul' c p := by
    apply Prod.ext
    · change e (c • p.1.1, c • p.2) = c • e (p.1.1, p.2)
      exact map_smul e c (p.1.1, p.2)
    · rfl

@[simp] theorem pointShuffle_apply (e : (A0 × F2) ≃ₗ[F2] A)
    (u : A0) (v : I) (c : F2) :
    pointShuffle (I := I) e ((u, v), c) = (e (u, c), v) := rfl

@[simp] theorem pointShuffle_symm_apply (e : (A0 × F2) ≃ₗ[F2] A)
    (u : A) (v : I) :
    (pointShuffle (I := I) e).symm (u, v) =
      (((e.symm u).1, v), (e.symm u).2) := rfl

end
end DFVSGames.Inverse.KMSFourthMoment

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSAnalyticSmallTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixFourier
open DFVSGames.Inverse.KMSAnalytic

variable {A I : Type*} [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I] [Subsingleton A]

def zeroFixedEquiv : I ≃ₗ[F2] (A × I) :=
  { LinearMap.inr F2 A I with
    invFun := Prod.snd
    left_inv := fun _ => rfl
    right_inv := by
      rintro ⟨a, x⟩
      exact Prod.ext (Subsingleton.elim _ _) rfl }

end
end DFVSGames.Inverse.KMSFourthMoment

end OAI
end


