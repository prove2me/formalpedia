-- Prove2me | Definitions.Def_OAIQ085D000
-- name    : OAIQ085D000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T15:52:30.970144+00:00
-- url     : https://prove2.me/theorems/ccf78be9-4873-45eb-bb40-1c80971f99b1
-- title:
--   Definitions bundle OAIQ085D000 of the split of OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 933 declarations of OpenAI's Lean: 482 definitions, 41 inductive types or structures, 14 instances and 396 theorems. The definitions and types are `OAI.DFVSGames.BinaryEncoding.bitsValue`, `OAI.DFVSGames.BinaryEncoding.clauseBits`, `OAI.DFVSGames.BinaryEncoding.clauseNameSize`, `OAI.DFVSGames.BinaryEncoding.clausesBits`, `OAI.DFVSGames.BinaryEncoding.decodeFormula`, `OAI.DFVSGames.BinaryEncoding.formulaBits`, `OAI.DFVSGames.BinaryEncoding.frame`, `OAI.DFVSGames.BinaryEncoding.literalBits`, `OAI.DFVSGames.BinaryEncoding.nameBits`, `OAI.DFVSGames.BinaryEncoding.namesBitSize`, `OAI.DFVSGames.BinaryEncoding.parseClause`, `OAI.DFVSGames.BinaryEncoding.parseClauses`, `OAI.DFVSGames.BinaryEncoding.parseFrame`, `OAI.DFVSGames.BinaryEncoding.parseLiteral`, `OAI.DFVSGames.BinaryEncoding.parseName`, `OAI.DFVSGames.BinaryFormula.Clause`, `OAI.DFVSGames.BinaryFormula.Clause.eval`, `OAI.DFVSGames.BinaryFormula.Formula`, `OAI.DFVSGames.BinaryFormula.Literal`, `OAI.DFVSGames.BinaryFormula.Literal.eval`, `OAI.DFVSGames.BinaryFormula.activeNames`, `OAI.DFVSGames.BinaryFormula.clauseNames`, `OAI.DFVSGames.BinaryFormula.compactIndex`, `OAI.DFVSGames.BinaryFormula.compactLiteral`, `OAI.DFVSGames.BinaryFormula.sourceNames`, `OAI.DFVSGames.BinaryOccurrenceRename.clause`, `OAI.DFVSGames.BinaryOccurrenceRename.extendAssignment`, `OAI.DFVSGames.BinaryOccurrenceRename.literal`, `OAI.DFVSGames.BinaryOccurrenceRename.nameIndex`, `OAI.DFVSGames.BinaryOccurrenceRename.renamed`, `OAI.DFVSGames.BinaryOccurrenceRename.restrictAssignment`, `OAI.DFVSGames.Clean.IncidenceGap.game`, `OAI.DFVSGames.Clean.IncidenceGap.incidenceLaw`, `OAI.DFVSGames.Clean.IncidenceGap.slotLaw`, `OAI.DFVSGames.Decoder.AdviceFibers.ObservedRow`, `OAI.DFVSGames.Decoder.AdviceFibers.RowFiber`, `OAI.DFVSGames.Decoder.AdviceFibers.assemble`, `OAI.DFVSGames.Decoder.AdviceFibers.hiddenCoordinate`, `OAI.DFVSGames.Decoder.AdviceFibers.kernelDifference`, `OAI.DFVSGames.Decoder.AdviceFibers.observationEquiv` and 483 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `DirectedFeedback_Analysis_Deletion`, `DirectedFeedback_Analysis_MatrixCharacters`, `DirectedFeedback_Analysis_MatrixNoise`, `DirectedFeedback_Analysis_NoiseEnumeration`, `DirectedFeedback_Encoding_ExpanderTableWords`, `DirectedFeedback_Encoding_FormulaEncoding`, `DirectedFeedback_Encoding_InstanceEquivalences`, `DirectedFeedback_Encoding_NameCompaction`, `DirectedFeedback_Encoding_Occurrences`, `DirectedFeedback_Encoding_ProductTarget`, `DirectedFeedback_Encoding_RawPrivateTable`, `DirectedFeedback_Games_ActualAdviceUpper`, `DirectedFeedback_Games_ActualCanonical`, `DirectedFeedback_Games_AdviceLaw`, `DirectedFeedback_Games_CanonicalAddress`, `DirectedFeedback_Games_ChainRule`, `DirectedFeedback_Games_Collision`, `DirectedFeedback_Games_ConditionalIncidences`, `DirectedFeedback_Games_ExpanderFamily`, `DirectedFeedback_Games_Explicit`, `DirectedFeedback_Games_FieldArray`, `DirectedFeedback_Games_FinalParameters`, `DirectedFeedback_Games_FinishReduction`, `DirectedFeedback_Games_Generator`, `DirectedFeedback_Games_KernelCardinality`, `DirectedFeedback_Games_Product`, `DirectedFeedback_Games_RowErasureSliceQuotient`, `DirectedFeedback_Games_Target`, `DirectedFeedback_Games_TensorDomination`, `DirectedFeedback_Games_TestEmit`, `DirectedFeedback_Machines_ContextLoad`, `DirectedFeedback_Machines_FinalCNFHeader`, `DirectedFeedback_Machines_MachineAffineLookup`, `DirectedFeedback_Machines_MachineBinaryNameMachine`, `DirectedFeedback_Machines_MachineCloudCount`, `DirectedFeedback_Machines_MachineCloudPadding`, `DirectedFeedback_Machines_MachineEmbedding`, `DirectedFeedback_Machines_MachineLookupSpec`, `DirectedFeedback_Machines_MachineProductField`, `DirectedFeedback_Machines_MachineProductPower`, `DirectedFeedback_Machines_MachineProductProgram`, `DirectedFeedback_Machines_MachineRegularMetadata`, `DirectedFeedback_Machines_MachineSubdivisionInit`, `DirectedFeedback_Machines_MachineSubdivisionLoop`, `DirectedFeedback_Machines_MachineSubdivisionRows`, `DirectedFeedback_Machines_MachineTransducer`, `DirectedFeedback_Machines_MachineUnaryAdd`, `DirectedFeedback_Machines_RawInitialMachineFinish`, `DirectedFeedback_Machines_Tape`, `DirectedFeedback_Machines_TupleOrder`, `DirectedFeedback_Probability_Basic`, `DirectedFeedback_RankGraph_Clone100Counting`, `DirectedFeedback_RankGraph_CloneGap`, `DirectedFeedback_RankGraph_SumBox`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ085D006`, `OAIQ085D007`, `OAIQ085D008`, `OAIQ085D009`, `OAIQ085D010` and `OAIQ085D011`.
-- source:
--   OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ085_DF.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

end OAI
end

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

abbrev Alphabet (Γ : K → Type) (Δ : E → Type) : K ⊕ E → Type
  | .inl k => Γ k
  | .inr e => Δ e

def tapes (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e)) :
    ∀ j, List (Alphabet Γ Δ j)
  | .inl k => source k
  | .inr e => extra e

@[simp] theorem tapes_inl (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e))
    (k : K) : tapes source extra (.inl k) = source k := rfl

@[simp] theorem tapes_inr (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e))
    (e : E) : tapes source extra (.inr e) = extra e := rfl

def label (haltTarget : Option (Λ ⊕ Λextra)) : Option Λ → Option (Λ ⊕ Λextra)
  | none => haltTarget
  | some l => some (.inl l)

end DFVSGames.Foundations.Complexity.MachineEmbedding


namespace DFVSGames.Foundations.Complexity.MachineComposition

def advance {σ : Type} (step : σ → Option σ) (state : Option σ) : Option σ :=
  state.bind step

@[simp] theorem advance_none {σ : Type} (step : σ → Option σ) :
    advance step none = none := rfl

@[simp] theorem advance_some {σ : Type} (step : σ → Option σ) (state : σ) :
    advance step (some state) = step state := rfl

@[simp] theorem advance_iterate_none {σ : Type} (step : σ → Option σ) (n : Nat) :
    (advance step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, advance_none]

theorem liftSuccessfulTrace {σ τ : Type} (source : σ → Option σ)
    (target : τ → Option τ) (embed : σ → τ)
    (simulation : ∀ a b, source a = some b → target (embed a) = some (embed b))
    (n : Nat) (start finish : σ)
    (trace : (advance source)^[n] (some start) = some finish) :
    (advance target)^[n] (some (embed start)) = some (embed finish) := by
  induction n generalizing start with
  | zero =>
      have same := Option.some.inj trace
      cases same
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply] at trace ⊢
      change (advance source)^[n] (source start) = some finish at trace
      change (advance target)^[n] (target (embed start)) = some (embed finish)
      cases firstStep : source start with
      | none =>
          rw [firstStep, advance_iterate_none] at trace
          contradiction
      | some intermediate =>
          rw [firstStep] at trace
          rw [simulation start intermediate firstStep]
          exact ih intermediate trace

def liftExecutionInTime {σ τ : Type} (source : σ → Option σ)
    (target : τ → Option τ) (embed : σ → τ)
    (simulation : ∀ a b, source a = some b → target (embed a) = some (embed b))
    {start finish : σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime source start (some finish) budget) :
    StateTransition.EvalsToInTime target (embed start) (some (embed finish)) budget where
  steps := execution.steps
  evals_in_steps := by
    have sourceTrace := execution.evals_in_steps
    change (advance source)^[execution.steps] (some start) = some finish at sourceTrace
    change (advance target)^[execution.steps] (some (embed start)) = some (embed finish)
    exact liftSuccessfulTrace source target embed simulation execution.steps start finish sourceTrace
  steps_le_m := execution.steps_le_m

@[simp] theorem liftExecutionInTime_steps {σ τ : Type} (source : σ → Option σ)
    (target : τ → Option τ) (embed : σ → τ)
    (simulation : ∀ a b, source a = some b → target (embed a) = some (embed b))
    {start finish : σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime source start (some finish) budget) :
    (liftExecutionInTime source target embed simulation execution).steps = execution.steps := rfl

end DFVSGames.Foundations.Complexity.MachineComposition


namespace DFVSGames.Reduction.MachineTransfer

open Turing

abbrev alphabet (α β : Type) : Bool → Type
  | false => α
  | true => β

variable {α β : Type} [Fintype α] [Fintype β]

def loop (f : α → β) (fallback : β) :
    TM2.Stmt (alphabet α β) Unit (Option β) :=
  .pop false (fun _ head => head.map f)
    (.branch Option.isSome
      (.push true (fun state => state.getD fallback) (.goto fun _ => ()))
      .halt)

def machine (f : α → β) (fallback : β) : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := alphabet α β
  Λ := Unit
  main := ()
  σ := Option β
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype α)
  m _ := loop f fallback

def tapeStacks (input : List α) (output : List β) :
    (side : Bool) → List (alphabet α β side)
  | false => input
  | true => output

def running (f : α → β) (fallback : β) (input : List α) (output : List β)
    (state : Option β) : (machine f fallback).Cfg :=
  ⟨some (), state, tapeStacks input output⟩

def halted (f : α → β) (fallback : β) (output : List β) : (machine f fallback).Cfg :=
  ⟨none, none, tapeStacks (α := α) [] output⟩

omit [Fintype α] [Fintype β] in
theorem update_input_inline_MachineTransfer (input replacement : List α) (output : List β) :
    Function.update (tapeStacks input output) false replacement = tapeStacks replacement output := by
  funext side
  cases side <;> rfl

omit [Fintype α] [Fintype β] in
theorem update_output_inline_MachineTransfer (input : List α) (output replacement : List β) :
    Function.update (tapeStacks input output) true replacement = tapeStacks input replacement := by
  funext side
  cases side <;> rfl

theorem step_empty (f : α → β) (fallback : β) (output : List β) (state : Option β) :
    (machine f fallback).step (running f fallback [] output state) =
      some (halted f fallback output) := by
  change some (TM2.stepAux (loop f fallback) state (tapeStacks (α := α) [] output)) = _
  simp [loop, TM2.stepAux, tapeStacks, halted, Function.update]
  rw [update_input_inline_MachineTransfer]
  rfl

theorem step_cons (f : α → β) (fallback : β) (head : α) (input : List α)
    (output : List β) (state : Option β) :
    (machine f fallback).step (running f fallback (head :: input) output state) =
      some (running f fallback input (f head :: output) (some (f head))) := by
  change some (TM2.stepAux (loop f fallback) state (tapeStacks (head :: input) output)) = _
  simp [loop, TM2.stepAux, tapeStacks, running, Function.update]
  rw [update_input_inline_MachineTransfer, update_output_inline_MachineTransfer]
  rfl

def next (f : α → β) (fallback : β) (configuration : Option (machine f fallback).Cfg) :
    Option (machine f fallback).Cfg := configuration.bind (machine f fallback).step

theorem transfer_steps (f : α → β) (fallback : β) (input : List α) (output : List β)
    (state : Option β) :
    (next f fallback)^[input.length + 1] (some (running f fallback input output state)) =
      some (halted f fallback (input.reverse.map f ++ output)) := by
  induction input generalizing output state with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, next,
      Option.bind_some, List.reverse_nil, List.map_nil, List.nil_append]
      using step_empty f fallback output state
  | cons head input ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (next f fallback)^[input.length + 1]
      ((machine f fallback).step (running f fallback (head :: input) output state)) = _
    rw [step_cons, ih]
    simp only [List.reverse_cons, List.map_append, List.map_singleton,
      List.append_assoc, List.singleton_append]

theorem initList_eq (f : α → β) (fallback : β) (input : List α) :
    initList (machine f fallback) input = running f fallback input [] none := by
  unfold initList running
  congr 1
  funext side
  cases side <;> rfl

theorem haltList_eq (f : α → β) (fallback : β) (output : List β) :
    haltList (machine f fallback) output = halted f fallback output := by
  unfold haltList halted
  congr 1
  funext side
  cases side <;> rfl

theorem transfer_init_steps (f : α → β) (fallback : β) (input : List α) :
    (next f fallback)^[input.length + 1] (some (initList (machine f fallback) input)) =
      some (haltList (machine f fallback) (input.reverse.map f)) := by
  calc
    _ = (next f fallback)^[input.length + 1]
        (some (running f fallback input [] none)) :=
      congrArg _ (congrArg some (initList_eq f fallback input))
    _ = some (halted f fallback (input.reverse.map f)) := by
      simpa only [List.append_nil] using transfer_steps f fallback input [] none
    _ = _ := congrArg some (haltList_eq f fallback (input.reverse.map f)).symm

def outputsInTime (f : α → β) (fallback : β) (input : List α) :
    TM2OutputsInTime (machine f fallback) input (some (input.reverse.map f))
      (input.length + 1) where
  steps := input.length + 1
  evals_in_steps := transfer_init_steps f fallback input
  steps_le_m := Nat.le_refl _

@[simp] theorem outputsInTime_steps (f : α → β) (fallback : β) (input : List α) :
    (outputsInTime f fallback input).steps = input.length + 1 := rfl


variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

def exitAt (dst : K) (exit : Option Λ) : TM2.Stmt Γ Λ (σ × Option (Γ dst)) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def tapesAt (src dst : K) (base : (k : K) → List (Γ k))
    (input : List (Γ src)) (output : List (Γ dst)) : (k : K) → List (Γ k) :=
  Function.update (Function.update base src input) dst output

@[simp] theorem tapesAt_src (src dst : K) (distinct : src ≠ dst)
    (base : (k : K) → List (Γ k)) (input : List (Γ src)) (output : List (Γ dst)) :
    tapesAt src dst base input output src = input := by
  simp [tapesAt, distinct]

@[simp] theorem tapesAt_dst (src dst : K)
    (base : (k : K) → List (Γ k)) (input : List (Γ src)) (output : List (Γ dst)) :
    tapesAt src dst base input output dst = output := by
  simp [tapesAt]

@[simp] theorem tapesAt_self (src dst : K) (base : (k : K) → List (Γ k)) :
    tapesAt src dst base (base src) (base dst) = base := by
  simp [tapesAt]


end DFVSGames.Reduction.MachineTransfer


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

structure Literal («variables» : Nat) where
  variableIndex : Fin «variables»
  positive : Bool
  deriving DecidableEq

def Literal.eval {n : Nat} (literal : Literal n) (assignment : Fin n → Bool) : Bool :=
  if literal.positive then assignment literal.variableIndex else !(assignment literal.variableIndex)

abbrev Clause («variables» : Nat) := Vector (Literal «variables») 3

def Clause.eval {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) : Bool :=
  (clause[0].eval assignment || clause[1].eval assignment) || clause[2].eval assignment

structure Formula where
  «variables» : Nat
  clauses : List (Clause «variables»)

structure PermutationTable (alphabet : Nat) where
  images : Vector (Fin alphabet) alphabet
  inverseImages : Vector (Fin alphabet) alphabet
  leftInverse : ∀ label : Fin alphabet, inverseImages[images[label]] = label
  rightInverse : ∀ label : Fin alphabet, images[inverseImages[label]] = label

structure Constraint (vertices alphabet : Nat) where
  source : Fin vertices
  target : Fin vertices
  permutation : PermutationTable alphabet

def Constraint.satisfied {n q : Nat} (constraint : Constraint n q)
    (labeling : Fin n → Fin q) : Bool :=
  decide (constraint.permutation.images[labeling constraint.source] = labeling constraint.target)

structure Instance (alphabet : Nat) where
  vertices : Nat
  constraints : List (Constraint vertices alphabet)
  nonempty : constraints ≠ []

theorem Instance.constraintCount_positive {q : Nat} (game : Instance q) :
    0 < game.constraints.length := by
  cases h : game.constraints with
  | nil => exact False.elim (game.nonempty h)
  | cons constraint rest => simp

end DFVSGames.Foundations.Target


namespace DFVSGames.Foundations.Complexity

def encodeWord (n : Nat) : List Bool := List.replicate n true ++ [false]

def encodeWords : List Nat → List Bool
  | [] => []
  | n :: ns => encodeWord n ++ encodeWords ns

def decodeWordsAux : List Bool → Nat → Option (List Nat)
  | [], 0 => some []
  | [], _ + 1 => none
  | true :: bs, n => decodeWordsAux bs (n + 1)
  | false :: bs, n => (decodeWordsAux bs 0).map (n :: ·)

def decodeWords (bs : List Bool) : Option (List Nat) := decodeWordsAux bs 0

theorem decodeWordsAux_word (n k : Nat) (bs : List Bool) :
    decodeWordsAux (encodeWord n ++ bs) k =
      (decodeWordsAux bs 0).map ((k + n) :: ·) := by
  induction n generalizing k with
  | zero => simp [encodeWord, decodeWordsAux]
  | succ n ih =>
      simp only [encodeWord, List.replicate_succ, List.cons_append, List.append_assoc,
        decodeWordsAux]
      simpa [encodeWord, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1)

@[simp] theorem decodeWords_encodeWords (ns : List Nat) :
    decodeWords (encodeWords ns) = some ns := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
      simp only [decodeWords, encodeWords, decodeWordsAux_word, Nat.zero_add]
      simpa [decodeWords] using congrArg (Option.map (n :: ·)) ih

@[simp] theorem encodeWord_length (n : Nat) : (encodeWord n).length = n + 1 := by
  simp [encodeWord]

@[simp] theorem encodeWords_append (xs ys : List Nat) :
    encodeWords (xs ++ ys) = encodeWords xs ++ encodeWords ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeWords, ih, List.append_assoc]

@[simp] theorem encodeWords_length (ns : List Nat) :
    (encodeWords ns).length = ns.sum + ns.length := by
  induction ns with
  | nil => rfl
  | cons n ns ih => simp [encodeWords, ih]; omega

open Target

def literalWords {n : Nat} (literal : Literal n) : List Nat :=
  [literal.variableIndex.val, if literal.positive then 1 else 0]

def clauseWords {n : Nat} (clause : Clause n) : List Nat :=
  literalWords clause[0] ++ literalWords clause[1] ++ literalWords clause[2]

def formulaWords (formula : Formula) : List Nat :=
  [formula.«variables», formula.clauses.length] ++ formula.clauses.flatMap clauseWords

def formulaBits (formula : Formula) : List Bool := encodeWords (formulaWords formula)

@[simp] theorem literalWords_length {n : Nat} (literal : Literal n) :
    (literalWords literal).length = 2 := by simp [literalWords]

@[simp] theorem clauseWords_length {n : Nat} (clause : Clause n) :
    (clauseWords clause).length = 6 := by simp [clauseWords]

theorem clausesWords_length {n : Nat} (clauses : List (Clause n)) :
    (clauses.flatMap clauseWords).length = 6 * clauses.length := by
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      simp only [List.flatMap_cons, List.length_append, clauseWords_length,
        List.length_cons, ih, Nat.mul_add, Nat.mul_one]
      omega

@[simp] theorem formulaWords_length (formula : Formula) :
    (formulaWords formula).length = 2 + 6 * formula.clauses.length := by
  simp only [formulaWords, List.length_append, List.length_cons, List.length_nil,
    clausesWords_length]

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

structure Literal where
  name : Nat
  positive : Bool
  deriving DecidableEq

def Literal.eval (literal : Literal) (assignment : Nat → Bool) : Bool :=
  if literal.positive then assignment literal.name else !(assignment literal.name)

abbrev Clause := Vector Literal 3

def Clause.eval (clause : Clause) (assignment : Nat → Bool) : Bool :=
  (clause[0].eval assignment || clause[1].eval assignment) || clause[2].eval assignment

structure Formula where
  clauses : List Clause

def clauseNames (clause : Clause) : List Nat :=
  [clause[0].name, clause[1].name, clause[2].name]

end DFVSGames.BinaryFormula

namespace DFVSGames.BinaryEncoding

open BinaryFormula

def bitsValue : List Bool → Nat
  | [] => 0
  | b :: bits => Nat.bit b (bitsValue bits)

@[simp] theorem bitsValue_bits (n : Nat) : bitsValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bitsValue]
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      simp only [bitsValue, ih]

def frame : List Bool → List Bool
  | [] => [false]
  | b :: bits => true :: b :: frame bits

def parseFrame : List Bool → Option (List Bool × List Bool)
  | false :: rest => some ([], rest)
  | true :: b :: rest => do
      let (bits, trailing) ← parseFrame rest
      return (b :: bits, trailing)
  | _ => none

@[simp] theorem parseFrame_encoded (bits trailing : List Bool) :
    parseFrame (frame bits ++ trailing) = some (bits, trailing) := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [frame, parseFrame, ih]

@[simp] theorem frame_length (bits : List Bool) :
    (frame bits).length = 2 * bits.length + 1 := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [frame, ih]; omega

def nameBits (name : Nat) : List Bool := frame name.bits

def parseName (input : List Bool) : Option (Nat × List Bool) := do
  let (digits, rest) ← parseFrame input
  let name := bitsValue digits
  if digits = name.bits then some (name, rest) else none

@[simp] theorem parseName_encoded (name : Nat) (rest : List Bool) :
    parseName (nameBits name ++ rest) = some (name, rest) := by
  simp [parseName, nameBits]

@[simp] theorem nameBits_length (name : Nat) :
    (nameBits name).length = 2 * name.size + 1 := by
  simp [nameBits, Nat.size_eq_bits_len]

def literalBits (literal : Literal) : List Bool :=
  literal.positive :: nameBits literal.name

def parseLiteral : List Bool → Option (Literal × List Bool)
  | sign :: input => do
      let (name, rest) ← parseName input
      return (⟨name, sign⟩, rest)
  | [] => none

@[simp] theorem parseLiteral_encoded (literal : Literal) (rest : List Bool) :
    parseLiteral (literalBits literal ++ rest) = some (literal, rest) := by
  cases literal with
  | mk name sign => simp [literalBits, parseLiteral]

@[simp] theorem literalBits_length (literal : Literal) :
    (literalBits literal).length = 2 * literal.name.size + 2 := by
  simp [literalBits]

def clauseBits (clause : Clause) : List Bool :=
  literalBits clause[0] ++ literalBits clause[1] ++ literalBits clause[2]

def parseClause (input : List Bool) : Option (Clause × List Bool) := do
  let (a, input) ← parseLiteral input
  let (b, input) ← parseLiteral input
  let (c, rest) ← parseLiteral input
  return (#v[a, b, c], rest)

theorem clause_three_entries (clause : Clause) : #v[clause[0], clause[1], clause[2]] = clause := by
  apply Vector.ext
  intro i hi
  have cases_i : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases_i with rfl | rfl | rfl <;> rfl

@[simp] theorem parseClause_encoded (clause : Clause) (rest : List Bool) :
    parseClause (clauseBits clause ++ rest) = some (clause, rest) := by
  simp [clauseBits, List.append_assoc, parseClause, clause_three_entries]

def clauseNameSize (clause : Clause) : Nat :=
  ((clauseNames clause).map Nat.size).sum

@[simp] theorem clauseBits_length (clause : Clause) :
    (clauseBits clause).length = 2 * clauseNameSize clause + 6 := by
  simp [clauseBits, clauseNameSize, clauseNames]
  omega

def clausesBits : List Clause → List Bool
  | [] => [false]
  | clause :: clauses => true :: (clauseBits clause ++ clausesBits clauses)

def formulaBits (formula : Formula) : List Bool := clausesBits formula.clauses

def namesBitSize (clauses : List Clause) : Nat :=
  ((clauses.flatMap clauseNames).map Nat.size).sum

@[simp] theorem namesBitSize_nil : namesBitSize [] = 0 := rfl

@[simp] theorem namesBitSize_cons (clause : Clause) (clauses : List Clause) :
    namesBitSize (clause :: clauses) = clauseNameSize clause + namesBitSize clauses := by
  simp [namesBitSize, clauseNameSize]

theorem clausesBits_length (clauses : List Clause) :
    (clausesBits clauses).length = 7 * clauses.length + 2 * namesBitSize clauses + 1 := by
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      simp only [clausesBits, List.length_cons, List.length_append, clauseBits_length,
        namesBitSize_cons, ih]
      omega

theorem clauses_length_lt_bits (clauses : List Clause) :
    clauses.length < (clausesBits clauses).length := by
  rw [clausesBits_length]
  omega

def parseClauses : Nat → List Bool → Option (List Clause × List Bool)
  | 0, _ => none
  | _ + 1, false :: rest => some ([], rest)
  | fuel + 1, true :: input => do
      let (clause, input) ← parseClause input
      let (clauses, rest) ← parseClauses fuel input
      return (clause :: clauses, rest)
  | _ + 1, [] => none

@[simp] theorem parseClauses_encoded (clauses : List Clause) (rest : List Bool)
    (fuel : Nat) (enough : clauses.length < fuel) :
    parseClauses fuel (clausesBits clauses ++ rest) = some (clauses, rest) := by
  induction clauses generalizing fuel with
  | nil =>
      cases fuel with
      | zero => omega
      | succ fuel => simp [clausesBits, parseClauses]
  | cons clause clauses ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hrest : clauses.length < fuel := by simp only [List.length_cons] at enough; omega
          simp [clausesBits, parseClauses, List.append_assoc, ih fuel hrest]

def decodeFormula (input : List Bool) : Option Formula := do
  let (clauses, rest) ← parseClauses (input.length + 1) input
  if rest = [] then some ⟨clauses⟩ else none

@[simp] theorem decodeFormula_encoded (formula : Formula) :
    decodeFormula (formulaBits formula) = some formula := by
  cases formula with
  | mk clauses =>
      have hlen := clauses_length_lt_bits clauses
      have parsed := parseClauses_encoded clauses [] ((clausesBits clauses).length + 1) (by omega)
      simp only [List.append_nil] at parsed
      simp [formulaBits, decodeFormula, parsed]

end DFVSGames.BinaryEncoding

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

inductive Token (q : Nat)
  | literal (bits : List Bool)
  | copy (field : Fin q)
  deriving DecidableEq

end DFVSGames.Reduction.MachineFieldTemplate

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

def renameConstraint {n m q : Nat} (e : Fin n ≃ Fin m) (c : Constraint n q) :
    Constraint m q where
  source := e c.source
  target := e c.target
  permutation := c.permutation

@[simp] theorem renameConstraint_satisfied {n m q : Nat} (e : Fin n ≃ Fin m)
    (c : Constraint n q) (labeling : Fin m → Fin q) :
    (renameConstraint e c).satisfied labeling = c.satisfied (labeling ∘ e) := rfl

end DFVSGames.Integration.InstanceEquivalences


namespace DFVSGames.MachineUniformCopyOrder

def copyMajor {α : Type*} (C : Nat) (edges : List α) : List α :=
  (List.replicate C edges).flatten

open DFVSGames.Foundations.Target

end DFVSGames.MachineUniformCopyOrder


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_FormulaEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity

open Target

def parseLiteral («variables» : Nat) : List Nat → Option (Literal «variables» × List Nat)
  | index :: sign :: rest =>
      if bounded : index < «variables» then
        if sign = 0 then some (⟨⟨index, bounded⟩, false⟩, rest)
        else if sign = 1 then some (⟨⟨index, bounded⟩, true⟩, rest)
        else none
      else none
  | _ => none

@[simp] theorem parseLiteral_encoded {n : Nat} (literal : Literal n) (rest : List Nat) :
    parseLiteral n (literalWords literal ++ rest) = some (literal, rest) := by
  cases literal with
  | mk index positive =>
      cases positive <;> simp [literalWords, parseLiteral, index.isLt]

def parseClause («variables» : Nat) (words : List Nat) : Option (Clause «variables» × List Nat) := do
  let (a, words) ← parseLiteral «variables» words
  let (b, words) ← parseLiteral «variables» words
  let (c, words) ← parseLiteral «variables» words
  return (⟨#[a, b, c], rfl⟩, words)

theorem clause_three_entries {n : Nat} (clause : Clause n) :
    (⟨#[clause[0], clause[1], clause[2]], rfl⟩ : Clause n) = clause := by
  apply Vector.ext
  intro i hi
  have cases_i : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases_i with rfl | rfl | rfl <;> rfl

@[simp] theorem parseClause_encoded {n : Nat} (clause : Clause n) (rest : List Nat) :
    parseClause n (clauseWords clause ++ rest) = some (clause, rest) := by
  simp [clauseWords, List.append_assoc, parseClause, parseLiteral_encoded,
    clause_three_entries]

def parseClauses («variables» : Nat) : Nat → List Nat → Option (List (Clause «variables») × List Nat)
  | 0, words => some ([], words)
  | count + 1, words => do
      let (clause, words) ← parseClause «variables» words
      let (clauses, words) ← parseClauses «variables» count words
      return (clause :: clauses, words)

@[simp] theorem parseClauses_encoded {n : Nat} (clauses : List (Clause n)) (rest : List Nat) :
    parseClauses n clauses.length (clauses.flatMap clauseWords ++ rest) = some (clauses, rest) := by
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      simp [List.append_assoc, parseClauses, parseClause_encoded, ih]

def decodeFormulaWords : List Nat → Option Formula
  | «variables» :: count :: words => do
      let (clauses, trailing) ← parseClauses «variables» count words
      if trailing = [] then some ⟨«variables», clauses⟩ else none
  | _ => none

@[simp] theorem decodeFormulaWords_encoded (formula : Formula) :
    decodeFormulaWords (formulaWords formula) = some formula := by
  cases formula with
  | mk «variables» clauses =>
      have parsed := parseClauses_encoded clauses []
      simp only [List.append_nil] at parsed
      simp [decodeFormulaWords, formulaWords, parsed]

def decodeFormulaBits (bits : List Bool) : Option Formula :=
  decodeWords bits >>= decodeFormulaWords

@[simp] theorem decodeFormulaBits_encoded (formula : Formula) :
    decodeFormulaBits (formulaBits formula) = some formula := by
  simp [decodeFormulaBits, formulaBits]

end DFVSGames.Foundations.Complexity


namespace DFVSGames.Foundations.Complexity

open Target

def tableWords {q : Nat} (table : PermutationTable q) : List Nat :=
  table.images.toList.map Fin.val

@[simp] theorem tableWords_length {q : Nat} (table : PermutationTable q) :
    (tableWords table).length = q := by simp [tableWords]

def constraintWords {n q : Nat} (constraint : Constraint n q) : List Nat :=
  [constraint.source.val, constraint.target.val] ++ tableWords constraint.permutation

@[simp] theorem constraintWords_length {n q : Nat} (constraint : Constraint n q) :
    (constraintWords constraint).length = q + 2 := by simp [constraintWords]

end DFVSGames.Foundations.Complexity


namespace DFVSGames.Integration.BinaryCoordinates

abbrev Coordinates (n : Nat) := Fin n → Bool

def pack : {n : Nat} → Coordinates n → BitVec n
  | 0, _ => 0
  | _ + 1, f => BitVec.concat (pack (fun i => f i.succ)) (f 0)

def unpack {n : Nat} (v : BitVec n) : Coordinates n :=
  fun i => v.getLsbD i.val

theorem pack_get {n : Nat} (f : Coordinates n) (i : Fin n) :
    (pack f).getLsbD i.val = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact BitVec.getLsbD_concat_zero
    · exact (BitVec.getLsbD_concat_succ).trans (ih (fun j => f j.succ) j)

theorem unpack_pack {n : Nat} (f : Coordinates n) : unpack (pack f) = f := by
  funext i
  exact pack_get f i

theorem pack_unpack {n : Nat} (v : BitVec n) : pack (unpack v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact pack_get (unpack v) ⟨i, hi⟩

end DFVSGames.Integration.BinaryCoordinates


namespace DFVSGames.Integration.BinaryLinear

open BinaryCoordinates

abbrev F2 := ZMod 2
abbrev Vector (n : Nat) := Fin n → F2

def ofBit (b : Bool) : F2 := if b then 1 else 0
def toBit (a : F2) : Bool := decide (a = 1)

theorem scalar_cases : ∀ a : F2, a = 0 ∨ a = 1 := by decide
theorem ofBit_toBit : ∀ a : F2, ofBit (toBit a) = a := by decide
theorem toBit_ofBit : ∀ b : Bool, toBit (ofBit b) = b := by decide

def toVector {n : Nat} (v : BitVec n) : Vector n := fun i => ofBit (unpack v i)
def fromVector {n : Nat} (v : Vector n) : BitVec n := pack (fun i => toBit (v i))

theorem toVector_fromVector {n : Nat} (v : Vector n) : toVector (fromVector v) = v := by
  funext i
  simp only [toVector, fromVector, unpack_pack, ofBit_toBit]

theorem fromVector_toVector {n : Nat} (v : BitVec n) : fromVector (toVector v) = v := by
  simp only [fromVector, toVector, toBit_ofBit]
  exact pack_unpack v

def coordinatesEquiv (n : Nat) : BitVec n ≃ Vector n where
  toFun := toVector
  invFun := fromVector
  left_inv := fromVector_toVector
  right_inv := toVector_fromVector

end DFVSGames.Integration.BinaryLinear


namespace DFVSGames.Explicit.UniformTarget

open DFVSGames.Foundations Target Complexity
open DFVSGames.Integration
open MachineUniformCopyOrder

theorem copy_length {α : Type*} (C : Nat) (xs : List α) :
    (copyMajor C xs).length = C * xs.length := by
  induction C with
  | zero => simp [copyMajor]
  | succ C ih =>
    simp [copyMajor, List.replicate_succ, List.flatten_cons, Nat.add_mul,
      Nat.add_comm]

def construct {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) : Instance q where
  vertices := g.vertices
  constraints := copyMajor C g.constraints
  nonempty := by
    apply List.length_pos_iff.mp
    rw [copy_length]
    exact Nat.mul_pos hC g.constraintCount_positive

@[simp] theorem vertices {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) :
    (construct C hC g).vertices = g.vertices := rfl

@[simp] theorem edge_count {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) :
    (construct C hC g).constraints.length = C * g.constraints.length :=
  copy_length C g.constraints

end DFVSGames.Explicit.UniformTarget

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineSubdivisionRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit.MachineSubdivisionRows

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Target
open DFVSGames.Foundations.Complexity
open DFVSGames.Reduction

def identityTable (q : Nat) : PermutationTable q where
  images := Vector.ofFn id
  inverseImages := Vector.ofFn id
  leftInverse _ := by simp
  rightInverse _ := by simp

def inverseTable {q : Nat} (p : PermutationTable q) : PermutationTable q where
  images := p.inverseImages
  inverseImages := p.images
  leftInverse := p.rightInverse
  rightInverse := p.leftInverse

def rows {n q : Nat} (vertices : Fin 5 → Fin n) (p : PermutationTable q) :
    List (Constraint n q) :=
  [⟨vertices 0, vertices 1, identityTable q⟩,
   ⟨vertices 2, vertices 1, identityTable q⟩,
   ⟨vertices 2, vertices 3, identityTable q⟩,
   ⟨vertices 4, vertices 3, inverseTable p⟩]

@[simp] theorem rows_length {n q : Nat}
    (vertices : Fin 5 → Fin n) (p : PermutationTable q) :
    (rows vertices p).length = 4 := rfl

def tokens (identity inverse : List Bool) : List (MachineFieldTemplate.Token 5) :=
  [.copy 0, .copy 1, .literal identity,
   .copy 2, .copy 1, .literal identity,
   .copy 2, .copy 3, .literal identity,
   .copy 4, .copy 3, .literal inverse]

@[simp] theorem tokens_length (identity inverse : List Bool) :
    (tokens identity inverse).length = 12 := rfl

end DFVSGames.Explicit.MachineSubdivisionRows


namespace DFVSGames.Reduction.Encoding

open Integration.BinaryLinear
open Foundations.Target

def sideEquiv (n : Nat) : Bool × Fin n ≃ Fin (2*n) :=
  (finTwoEquiv.symm.prodCongr (Equiv.refl (Fin n))).trans finProdFinEquiv

@[simp] theorem sideEquiv_false_val {n : Nat} (i : Fin n) : (sideEquiv n (false, i)).val = i.val := by
  simp [sideEquiv, finProdFinEquiv, finTwoEquiv]

@[simp] theorem sideEquiv_true_val {n : Nat} (i : Fin n) : (sideEquiv n (true, i)).val = n + i.val := by
  simp [sideEquiv, finProdFinEquiv, finTwoEquiv, Nat.add_comm]

def alphabetEquiv (s : Nat) : Integration.BinaryLinear.Vector s ≃ Fin (2^s) :=
  (coordinatesEquiv s).symm.trans
    { toFun := BitVec.toFin
      invFun := BitVec.ofFin
      left_inv := BitVec.ofFin_toFin
      right_inv := BitVec.toFin_ofFin }

@[simp] theorem alphabetEquiv_symm_apply_apply (s : Nat)
    (c : Integration.BinaryLinear.Vector s) :
    (alphabetEquiv s).symm (alphabetEquiv s c) = c :=
  (alphabetEquiv s).symm_apply_apply c

@[simp] theorem alphabetEquiv_apply_symm_apply (s : Nat) (c : Fin (2^s)) :
    alphabetEquiv s ((alphabetEquiv s).symm c) = c :=
  (alphabetEquiv s).apply_symm_apply c

def translate {s : Nat} (a b : Integration.BinaryLinear.Vector s)
    (c : Fin (2^s)) : Fin (2^s) :=
  alphabetEquiv s ((alphabetEquiv s).symm c + a + b)

theorem translate_involutive {s : Nat} (a b : Integration.BinaryLinear.Vector s) :
    Function.Involutive (translate a b) := by
  intro c
  simp only [translate, alphabetEquiv_symm_apply_apply]
  have h : (alphabetEquiv s).symm c + a + b + a + b = (alphabetEquiv s).symm c := by
    ext i
    simp only [Pi.add_apply]
    rw [show (alphabetEquiv s).symm c i + a i + b i + a i + b i =
      (alphabetEquiv s).symm c i + (a i + a i) + (b i + b i) by abel]
    simp [CharTwo.add_self_eq_zero]
  rw [h, alphabetEquiv_apply_symm_apply]

def translationTable {s : Nat} (a b : Integration.BinaryLinear.Vector s) :
    PermutationTable (2^s) where
  images := _root_.Vector.ofFn (translate a b)
  inverseImages := _root_.Vector.ofFn (translate a b)
  leftInverse c := by simpa using translate_involutive a b c
  rightInverse c := by simpa using translate_involutive a b c

@[simp] theorem translationTable_images {s : Nat}
    (a b c : Integration.BinaryLinear.Vector s) :
    (translationTable a b).images[alphabetEquiv s c] = alphabetEquiv s (c + a + b) := by
  simp [translationTable, translate]

@[simp] theorem translationTable_inverseImages {s : Nat}
    (a b c : Integration.BinaryLinear.Vector s) :
    (translationTable a b).inverseImages[alphabetEquiv s c] =
      alphabetEquiv s (c + a + b) := by
  simp [translationTable, translate]


variable {Q V : Type*} [DecidableEq V]

def imageVertices (queries : List Q) (body : Q → V) : List V :=
  (queries.map body).dedup

theorem mem_imageVertices {queries : List Q} {body : Q → V} {v : V} :
    v ∈ imageVertices queries body ↔ ∃ q ∈ queries, body q = v := by
  simp [imageVertices]

theorem imageVertices_nodup (queries : List Q) (body : Q → V) :
    (imageVertices queries body).Nodup := List.nodup_dedup _

abbrev ImageVertex (queries : List Q) (body : Q → V) :=
  {v : V // v ∈ imageVertices queries body}

def imageEquiv (queries : List Q) (body : Q → V) :
    ImageVertex queries body ≃ Fin (imageVertices queries body).length :=
  (List.Nodup.getEquiv _ (imageVertices_nodup queries body)).symm

theorem imageVertices_range (queries : List Q) (body : Q → V)
    (full : ∀ q, q ∈ queries) (v : V) :
    v ∈ imageVertices queries body ↔ v ∈ Set.range body := by
  simp [mem_imageVertices, full, Set.mem_range]


end DFVSGames.Reduction.Encoding


namespace DFVSGames.Explicit.MachineSubdivisionDynamicRows

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Target
open DFVSGames.Foundations.Complexity
open DFVSGames.Reduction
open MachineSubdivisionRows (identityTable inverseTable)

def tokens (identity : List Bool) : List (MachineFieldTemplate.Token 6) :=
  [.copy 0, .copy 1, .literal identity,
   .copy 2, .copy 1, .literal identity,
   .copy 2, .copy 3, .literal identity,
   .copy 4, .copy 3, .copy 5]

@[simp] theorem tokens_length (identity : List Bool) :
    (tokens identity).length = 12 := rfl

end DFVSGames.Explicit.MachineSubdivisionDynamicRows


namespace DFVSGames.Foundations.Complexity.MachineUnaryCounter

open Turing

variable {K Λ σ : Type} [DecidableEq K]

def counterTapes (counter : K) (base : K → List Bool) (n : Nat)
    (suffix : List Bool) : K → List Bool :=
  Function.update base counter (encodeWord n ++ suffix)

@[simp] theorem counterTapes_counter (counter : K) (base : K → List Bool)
    (n : Nat) (suffix : List Bool) :
    counterTapes counter base n suffix counter = encodeWord n ++ suffix := by
  simp [counterTapes]

end DFVSGames.Foundations.Complexity.MachineUnaryCounter


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Analysis_Deletion
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

abbrev Parameter (W : Submodule F2 E)
    (C' : Submodule F2 C) := (E ⧸ W) →ₗ[F2] C'

def embed (W : Submodule F2 E)
    (C' : Submodule F2 C) (A : Parameter W C') : (E →ₗ[F2] C) :=
  C'.subtype.comp (A.comp W.mkQ)

@[simp] theorem embed_apply (W : Submodule F2 E)
    (C' : Submodule F2 C) (A : Parameter W C') (x : E) :
    embed W C' A x = (A (W.mkQ x) : C) := rfl

end DFVSGames.Fourier.MatrixRestrictions


noncomputable section
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear

namespace DFVSGames.Decoder.AdviceFibers

variable {E K R : Type*}
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup K] [Module F2 K]
  [AddCommGroup R] [Module F2 R]

abbrev RowFiber (A : K →ₗ[F2] R) (S : E →ₗ[F2] R) :=
  {M : E →ₗ[F2] K // A.comp M = S}

def kernelDifference (A : K →ₗ[F2] R) (S : E →ₗ[F2] R)
    (M₀ : E →ₗ[F2] K) (h₀ : A.comp M₀ = S) (M : RowFiber A S) :
    E →ₗ[F2] A.ker :=
  (M.val - M₀).codRestrict A.ker (by
    intro x
    change A (M.val x - M₀ x) = 0
    rw [map_sub]
    have hM := LinearMap.congr_fun M.property x
    have hbase := LinearMap.congr_fun h₀ x
    change A (M.val x) = S x at hM
    change A (M₀ x) = S x at hbase
    rw [hM, hbase, sub_self])

@[simp] theorem kernelDifference_apply (A : K →ₗ[F2] R) (S : E →ₗ[F2] R)
    (M₀ : E →ₗ[F2] K) (h₀ : A.comp M₀ = S) (M : RowFiber A S) (x : E) :
    (kernelDifference A S M₀ h₀ M x : K) = M.val x - M₀ x := rfl

def assemble (A : K →ₗ[F2] R) (M₀ : E →ₗ[F2] K)
    (N : E →ₗ[F2] A.ker) : E →ₗ[F2] K :=
  M₀ + A.ker.subtype.comp N

@[simp] theorem assemble_apply (A : K →ₗ[F2] R) (M₀ : E →ₗ[F2] K)
    (N : E →ₗ[F2] A.ker) (x : E) :
    assemble A M₀ N x = M₀ x + (N x : K) := rfl

theorem observed_assemble (A : K →ₗ[F2] R) (M₀ : E →ₗ[F2] K)
    (N : E →ₗ[F2] A.ker) : A.comp (assemble A M₀ N) = A.comp M₀ := by
  ext x
  have hN : A (N x : K) = 0 := (N x).property
  simp only [LinearMap.comp_apply, assemble_apply, map_add, hN, add_zero]

def rowFiberEquiv (A : K →ₗ[F2] R) (S : E →ₗ[F2] R)
    (M₀ : E →ₗ[F2] K) (h₀ : A.comp M₀ = S) :
    (E →ₗ[F2] A.ker) ≃ RowFiber A S where
  toFun N := ⟨assemble A M₀ N, (observed_assemble A M₀ N).trans h₀⟩
  invFun := kernelDifference A S M₀ h₀
  left_inv N := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change M₀ x + (N x : K) - M₀ x = (N x : K)
    exact add_sub_cancel_left _ _
  right_inv M := by
    apply Subtype.ext
    ext x
    change M₀ x + (M.val x - M₀ x) = M.val x
    simpa only [← add_sub_assoc] using add_sub_cancel_left (M₀ x) (M.val x)

@[simp] theorem rowFiberEquiv_coe (A : K →ₗ[F2] R) (S : E →ₗ[F2] R)
    (M₀ : E →ₗ[F2] K) (h₀ : A.comp M₀ = S) (N : E →ₗ[F2] A.ker) :
    (rowFiberEquiv A S M₀ h₀ N).val = assemble A M₀ N := rfl

@[simp] theorem rowFiberEquiv_symm (A : K →ₗ[F2] R) (S : E →ₗ[F2] R)
    (M₀ : E →ₗ[F2] K) (h₀ : A.comp M₀ = S) (M : RowFiber A S) :
    (rowFiberEquiv A S M₀ h₀).symm M = kernelDifference A S M₀ h₀ M := rfl

abbrev ObservedRow (A : K →ₗ[F2] R) :=
  {S : E →ₗ[F2] R // ∃ M : E →ₗ[F2] K, A.comp M = S}

def observe (A : K →ₗ[F2] R) (M : E →ₗ[F2] K) : ObservedRow (E := E) A :=
  ⟨A.comp M, M, rfl⟩

def observedBase (A : K →ₗ[F2] R) (S : ObservedRow (E := E) A) : E →ₗ[F2] K :=
  Classical.choose S.property

theorem observedBase_property (A : K →ₗ[F2] R) (S : ObservedRow (E := E) A) :
    A.comp (observedBase A S) = S.val := Classical.choose_spec S.property

def hiddenCoordinate (A : K →ₗ[F2] R) (M : E →ₗ[F2] K) :
    E →ₗ[F2] A.ker :=
  (rowFiberEquiv A (observe A M).val (observedBase A (observe A M))
    (observedBase_property A (observe A M))).symm ⟨M, rfl⟩

theorem observe_assemble_base (A : K →ₗ[F2] R) (S : ObservedRow (E := E) A)
    (N : E →ₗ[F2] A.ker) : observe A (assemble A (observedBase A S) N) = S := by
  apply Subtype.ext
  exact (observed_assemble A (observedBase A S) N).trans (observedBase_property A S)

def observationEquiv (A : K →ₗ[F2] R) :
    (E →ₗ[F2] K) ≃ ObservedRow (E := E) A × (E →ₗ[F2] A.ker) where
  toFun M := (observe A M, hiddenCoordinate A M)
  invFun p := assemble A (observedBase A p.1) p.2
  left_inv M := by
    exact congrArg Subtype.val
      ((rowFiberEquiv A (observe A M).val (observedBase A (observe A M))
        (observedBase_property A (observe A M))).apply_symm_apply ⟨M, rfl⟩)
  right_inv p := by
    apply Prod.ext
    · exact observe_assemble_base A p.1 p.2
    · apply LinearMap.ext
      intro x
      apply Subtype.ext
      change assemble A (observedBase A p.1) p.2 x -
        observedBase A (observe A (assemble A (observedBase A p.1) p.2)) x =
          (p.2 x : K)
      rw [observe_assemble_base, assemble_apply]
      exact add_sub_cancel_left _ _

@[simp] theorem observationEquiv_apply (A : K →ₗ[F2] R) (M : E →ₗ[F2] K) :
    observationEquiv A M = (observe A M, hiddenCoordinate A M) := rfl


end DFVSGames.Decoder.AdviceFibers
end


namespace DFVSGames.Reduction.ActualOrbit

open DFVSGames.Integration.BinaryLinear

universe u v

variable {Q : Type u} {T : Type v} {s d : Nat}

abbrev Ambient (s d : Nat) := Vector s × Vector d

def body (can : Q → Ambient s d × T) (q : Q) : Vector d × T :=
  ((can q).1.2, (can q).2)

def offset (can : Q → Ambient s d × T) (q : Q) : Vector s := (can q).1.1

def Vertex (can : Q → Ambient s d × T) := {o : Vector d × T // ∃ q, body can q = o}

def vertex (can : Q → Ambient s d × T) (q : Q) : Vertex can :=
  ⟨body can q, q, rfl⟩

theorem vertex_surjective (can : Q → Ambient s d × T) :
    Function.Surjective (vertex can) := by
  rintro ⟨o, q, hq⟩
  exact ⟨q, Subtype.ext hq⟩

noncomputable instance vertexFintype [Fintype Q] (can : Q → Ambient s d × T) :
    Fintype (Vertex can) := by
  classical
  exact Fintype.ofSurjective (vertex can) (vertex_surjective can)

theorem vertex_eq_iff (can : Q → Ambient s d × T) (q r : Q) :
    vertex can q = vertex can r ↔ body can q = body can r := by
  constructor
  · exact congrArg Subtype.val
  · intro h
    exact Subtype.ext h

abbrev TwoSidedVertex (can : Q → Ambient s d × T) := Bool × Vertex can

noncomputable def vertexEquiv [Fintype Q] (can : Q → Ambient s d × T) :
    TwoSidedVertex can ≃ Fin (Fintype.card (TwoSidedVertex can)) :=
  Fintype.equivFin _

def explicitVertexEquiv [DecidableEq (Vector d × T)]
    (can : Q → Ambient s d × T) (queries : List Q) (full : ∀ q, q ∈ queries) :
    Vertex can ≃ Fin (Encoding.imageVertices queries (body can)).length :=
  let e : Vertex can ≃ Encoding.ImageVertex queries (body can) :=
    { toFun v := ⟨v.val, (Encoding.imageVertices_range queries (body can) full v.val).mpr
        v.property⟩
      invFun v := ⟨v.val, (Encoding.imageVertices_range queries (body can) full v.val).mp
        v.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  e.trans (Encoding.imageEquiv queries (body can))

end DFVSGames.Reduction.ActualOrbit

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Analysis_MatrixCharacters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace DFVSGames.Fourier.MatrixCharacters

open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear

abbrev F2 := DFVSGames.Integration.BinaryLinear.F2

def tracePair {n m : Nat} (X : Matrix (Fin n) (Fin m) F2)
    (S : Matrix (Fin m) (Fin n) F2) : F2 := Matrix.trace (X * S)

@[simp] theorem tracePair_zero_left {n m : Nat} (S : Matrix (Fin m) (Fin n) F2) :
    tracePair (0 : Matrix (Fin n) (Fin m) F2) S = 0 := by simp [tracePair]

@[simp] theorem tracePair_zero_right {n m : Nat} (X : Matrix (Fin n) (Fin m) F2) :
    tracePair X (0 : Matrix (Fin m) (Fin n) F2) = 0 := by simp [tracePair]

theorem tracePair_add_left {n m : Nat} (X Y : Matrix (Fin n) (Fin m) F2)
    (S : Matrix (Fin m) (Fin n) F2) :
    tracePair (X + Y) S = tracePair X S + tracePair Y S := by
  simp [tracePair, Matrix.add_mul]

def binarySign (a : F2) : ℂ := if a = 0 then 1 else -1

@[simp] theorem binarySign_zero : binarySign 0 = 1 := by simp [binarySign]
@[simp] theorem binarySign_one : binarySign 1 = -1 := by simp [binarySign]

theorem binarySign_add (a b : F2) : binarySign (a + b) = binarySign a * binarySign b := by
  have htwo : (1 : F2) + 1 = 0 := by decide
  rcases scalar_cases a with rfl | rfl <;>
    rcases scalar_cases b with rfl | rfl <;> simp [htwo]

@[simp] theorem binarySign_im (a : F2) : (binarySign a).im = 0 := by
  unfold binarySign
  split <;> simp

@[simp] theorem binarySign_mul_self (a : F2) : binarySign a * binarySign a = 1 := by
  unfold binarySign
  split <;> simp

section LinearFunctionals

variable {E : Type*} [AddCommGroup E] [Module F2 E]

def linearFunctionalCharacter (φ : E →ₗ[F2] F2) : AddChar E ℂ where
  toFun x := binarySign (φ x)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by rw [map_add, binarySign_add]

@[simp] theorem linearFunctionalCharacter_apply (φ : E →ₗ[F2] F2) (x : E) :
    linearFunctionalCharacter φ x = binarySign (φ x) := rfl

@[simp] theorem linearFunctionalCharacter_zero :
    linearFunctionalCharacter (0 : E →ₗ[F2] F2) = 0 := by
  ext x
  simp

end LinearFunctionals

def traceCharacter {n m : Nat} (S : Matrix (Fin m) (Fin n) F2) :
    AddChar (Matrix (Fin n) (Fin m) F2) ℂ where
  toFun X := binarySign (tracePair X S)
  map_zero_eq_one' := by simp
  map_add_eq_mul' X Y := by rw [tracePair_add_left, binarySign_add]

@[simp] theorem traceCharacter_apply {n m : Nat} (S : Matrix (Fin m) (Fin n) F2)
    (X : Matrix (Fin n) (Fin m) F2) :
    traceCharacter S X = binarySign (tracePair X S) := rfl

@[simp] theorem traceCharacter_zero {n m : Nat} :
    traceCharacter (0 : Matrix (Fin m) (Fin n) F2) = 0 := by
  ext X
  simp

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

def linearTracePair (X : E →ₗ[F2] F) (S : F →ₗ[F2] E) : F2 :=
  LinearMap.trace F2 F (X.comp S)

@[simp] theorem linearTracePair_zero_left (S : F →ₗ[F2] E) :
    linearTracePair (0 : E →ₗ[F2] F) S = 0 := by simp [linearTracePair]

@[simp] theorem linearTracePair_zero_right (X : E →ₗ[F2] F) :
    linearTracePair X (0 : F →ₗ[F2] E) = 0 := by simp [linearTracePair]

theorem linearTracePair_add_left (X Y : E →ₗ[F2] F) (S : F →ₗ[F2] E) :
    linearTracePair (X + Y) S = linearTracePair X S + linearTracePair Y S := by
  simp [linearTracePair, LinearMap.add_comp]

def linearTraceCharacter (S : F →ₗ[F2] E) : AddChar (E →ₗ[F2] F) ℂ where
  toFun X := binarySign (linearTracePair X S)
  map_zero_eq_one' := by simp
  map_add_eq_mul' X Y := by rw [linearTracePair_add_left, binarySign_add]

@[simp] theorem linearTraceCharacter_apply (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    linearTraceCharacter S X = binarySign (linearTracePair X S) := rfl

@[simp] theorem linearTraceCharacter_zero :
    linearTraceCharacter (0 : F →ₗ[F2] E) = 0 := by
  ext X
  simp

end DFVSGames.Fourier.MatrixCharacters
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

def dotCharacter {m : Nat} (w : Vector m) : AddChar (Vector m) ℂ where
  toFun ℓ := binarySign (ℓ ⬝ᵥ w)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by rw [add_dotProduct, binarySign_add]

@[simp] theorem dotCharacter_apply {m : Nat} (w ℓ : Vector m) :
    dotCharacter w ℓ = binarySign (ℓ ⬝ᵥ w) := rfl

end DFVSGames.Fourier.MatrixNoise
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineSubdivisionInit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit.MachineSubdivisionLoopFrame

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Target
open DFVSGames.Foundations.Complexity
open DFVSGames.Reduction

def bodyBits {n q : Nat} (edges : List (Constraint n q)) : List Bool :=
  encodeWords (edges.flatMap constraintWords)

@[simp] theorem bodyBits_nil {n q : Nat} : bodyBits ([] : List (Constraint n q)) = [] := rfl

end DFVSGames.Explicit.MachineSubdivisionLoopFrame


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineSubdivisionLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit

structure OccurrenceGame (V E A : Type*) where
  source : E → V
  target : E → V
  permutation : E → Equiv.Perm A

structure BipartiteGame (L R E A : Type*) where
  left : E → L
  right : E → R
  permutation : E → Equiv.Perm A
  simple : Function.Injective (fun e => (left e, right e))


open scoped BigOperators

namespace Subdivision

variable {V E A : Type*}

abbrev Left (V E : Type*) := V ⊕ E

abbrev Right (E : Type*) := E × Bool

abbrev Edge (E : Type*) := E × Fin 4

def left (g : OccurrenceGame V E A) (ei : Edge E) : Left V E :=
  if ei.2 = 0 then Sum.inl (g.source ei.1)
  else if ei.2 = 3 then Sum.inl (g.target ei.1)
  else Sum.inr ei.1

def right (ei : Edge E) : Right E := (ei.1, decide (2 ≤ ei.2.val))

def permutation (g : OccurrenceGame V E A) (ei : Edge E) : Equiv.Perm A :=
  if ei.2 = 3 then (g.permutation ei.1).symm else Equiv.refl A

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

def restrict (a : Left V E → A) : V → A := fun v => a (Sum.inl v)

def extendLeft (g : OccurrenceGame V E A) (a : V → A) : Left V E → A :=
  Sum.elim a (fun e => a (g.source e))

@[simp] theorem restrict_extendLeft (g : OccurrenceGame V E A) (a : V → A) :
    restrict (extendLeft g a) = a := rfl

variable [DecidableEq A]

variable [Fintype E]

@[simp] theorem edge_count : Fintype.card (Edge E) = 4 * Fintype.card E := by
  simp [Edge, Nat.mul_comm]

@[simp] theorem left_count [Fintype V] :
    Fintype.card (Left V E) = Fintype.card V + Fintype.card E := by
  simp [Left]

@[simp] theorem right_count : Fintype.card (Right E) = 2 * Fintype.card E := by
  simp [Right, Nat.mul_comm]

end Subdivision

end DFVSGames.Explicit


namespace DFVSGames.Foundations.PCP

open Target

structure ClauseAnswer where
  first : Bool
  second : Bool
  third : Bool
  deriving DecidableEq

inductive Slot where
  | first
  | second
  | third
  deriving DecidableEq

def answerAt (answer : ClauseAnswer) : Slot → Bool
  | .first => answer.first
  | .second => answer.second
  | .third => answer.third

def nameAt {n : Nat} (clause : Clause n) : Slot → Fin n
  | .first => clause[0].variableIndex
  | .second => clause[1].variableIndex
  | .third => clause[2].variableIndex

def literalValue (positive value : Bool) : Bool :=
  if positive then value else !value

def localSatisfies {n : Nat} (clause : Clause n) (answer : ClauseAnswer) : Bool :=
  (literalValue clause[0].positive answer.first ||
   literalValue clause[1].positive answer.second) ||
   literalValue clause[2].positive answer.third

def clauseAt (formula : Formula) (index : Fin formula.clauses.length) :
    Clause formula.«variables» := formula.clauses[index.val]

end DFVSGames.Foundations.PCP

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_NameCompaction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.BinaryFormula

open DFVSGames.Foundations

def sourceNames (F : Formula) : List Nat :=
  F.clauses.flatMap clauseNames

def activeNames (F : Formula) : List Nat :=
  (sourceNames F).eraseDups

def compactIndex (F : Formula) (v : Nat)
    (hv : v ∈ activeNames F) : Fin (activeNames F).length :=
  ⟨(activeNames F).idxOf v, List.idxOf_lt_length_iff.mpr hv⟩

def compactLiteral (F : Formula) (l : Literal)
    (hl : l.name ∈ activeNames F) : Target.Literal (activeNames F).length :=
  ⟨compactIndex F l.name hl, l.positive⟩

@[simp] theorem compactLiteral_positive (F : Formula) (l : Literal)
    (hl : l.name ∈ activeNames F) : (compactLiteral F l hl).positive = l.positive := rfl

theorem clauseNames_flat_length (cs : List Clause) :
    (cs.flatMap clauseNames).length = 3 * cs.length := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, clauseNames,
      List.length_cons, List.length_nil, ih]
    omega

end DFVSGames.BinaryFormula


namespace DFVSGames.Foundations.Complexity.MachineCompare

open Turing
open DFVSGames.Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (K : Type) : K → Type := fun _ => Bool
abbrev State (σ : Type) := σ × Bool × Option Bool × Option Bool

def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet K) Λ (State σ) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def finish (exit : Option Λ) : TM2.Stmt (Alphabet K) Λ (State σ) :=
  .load (fun state => (state.1, false, none, none)) (exitAt exit)

def loop (left right : K) (loopLabel : Λ) (equalExit differentExit : Option Λ) :
    TM2.Stmt (Alphabet K) Λ (State σ) :=
  .pop left (fun state head => (state.1, state.2.1, head, state.2.2.2))
    (.pop right (fun state head => (state.1, state.2.1, state.2.2.1, head))
      (.branch (fun state => state.2.2.1.isNone && state.2.2.2.isNone)
        (.branch (fun state => state.2.1) (finish differentExit) (finish equalExit))
        (.load (fun state =>
          (state.1, state.2.1 || decide (state.2.2.1 ≠ state.2.2.2), none, none))
          (.goto fun _ => loopLabel))))

def mismatch (flag : Bool) (leftWord rightWord : List Bool) : Bool :=
  flag || decide (leftWord ≠ rightWord)

@[simp] theorem mismatch_nil_nil (flag : Bool) : mismatch flag [] [] = flag := by
  simp [mismatch]

@[simp] theorem mismatch_nil_cons (flag head : Bool) (tail : List Bool) :
    mismatch flag [] (head :: tail) = true := by simp [mismatch]

@[simp] theorem mismatch_cons_nil (flag head : Bool) (tail : List Bool) :
    mismatch flag (head :: tail) [] = true := by simp [mismatch]

@[simp] theorem mismatch_true (leftWord rightWord : List Bool) :
    mismatch true leftWord rightWord = true := by simp [mismatch]

theorem mismatch_cons (flag leftHead rightHead : Bool) (leftTail rightTail : List Bool) :
    mismatch (flag || decide (leftHead ≠ rightHead)) leftTail rightTail =
      mismatch flag (leftHead :: leftTail) (rightHead :: rightTail) := by
  cases flag <;> cases leftHead <;> cases rightHead <;> simp [mismatch]

@[simp] theorem stepAux_exitAt (exit : Option Λ) (state : State σ)
    (tapes : K → List Bool) :
    TM2.stepAux (exitAt exit) state tapes = ⟨exit, state, tapes⟩ := by
  cases exit <;> rfl

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State σ)
    (tapes : K → List Bool) :
    TM2.stepAux (finish exit) state tapes =
      ⟨exit, (state.1, false, none, none), tapes⟩ := by
  simp [finish, TM2.stepAux]

theorem update_left_inline_MachineCompare (left right : K) (distinct : left ≠ right)
    (base : K → List Bool) (leftWord rightWord replacement : List Bool) :
    Function.update (tapesAt left right base leftWord rightWord) left replacement =
      tapesAt left right base replacement rightWord := by
  funext k
  by_cases hl : k = left
  · subst k
    simp [tapesAt, distinct]
  · by_cases hr : k = right
    · subst k
      simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hl, hr]

theorem update_right_inline_MachineCompare (left right : K) (base : K → List Bool)
    (leftWord rightWord replacement : List Bool) :
    Function.update (tapesAt left right base leftWord rightWord) right replacement =
      tapesAt left right base leftWord replacement := by
  simp [tapesAt]

theorem step_empty (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] []⟩ =
      some ⟨if flag then differentExit else equalExit, (ambient, false, none, none),
        tapesAt left right base [] []⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base [] [])) = _
  rw [atLoop]
  cases flag <;>
    simp [loop, TM2.stepAux, distinct, update_left_inline_MachineCompare, update_right_inline_MachineCompare]

theorem step_nil_cons (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (head : Bool) (tail : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] (head :: tail)⟩ =
      some ⟨some loopLabel, (ambient, true, none, none), tapesAt left right base [] tail⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base [] (head :: tail))) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left_inline_MachineCompare, update_right_inline_MachineCompare]

theorem step_cons_nil (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (head : Bool) (tail : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base (head :: tail) []⟩ =
      some ⟨some loopLabel, (ambient, true, none, none), tapesAt left right base tail []⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base (head :: tail) [])) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left_inline_MachineCompare, update_right_inline_MachineCompare]

theorem step_cons_cons (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (leftHead rightHead : Bool) (leftTail rightTail : List Bool)
    (ambient : σ) (flag : Bool) (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base (leftHead :: leftTail) (rightHead :: rightTail)⟩ =
      some ⟨some loopLabel,
        (ambient, flag || decide (leftHead ≠ rightHead), none, none),
        tapesAt left right base leftTail rightTail⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base (leftHead :: leftTail) (rightHead :: rightTail))) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left_inline_MachineCompare, update_right_inline_MachineCompare]

theorem trace_left_empty_inline_MachineCompare (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (rightWord : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[rightWord.length + 1]
      (some ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] rightWord⟩) =
      some ⟨if mismatch flag [] rightWord then differentExit else equalExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  induction rightWord generalizing flag leftRegister rightRegister with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
      MachineComposition.advance_some, mismatch_nil_nil] using
      step_empty left right distinct loopLabel equalExit differentExit program atLoop base
        ambient flag leftRegister rightRegister
  | cons head tail ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[tail.length + 1]
      (TM2.step program ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] (head :: tail)⟩) = _
    rw [step_nil_cons left right distinct loopLabel equalExit differentExit program atLoop]
    simpa only [mismatch_true, mismatch_nil_cons] using ih true none none

theorem compareTrace_flag (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (leftWord rightWord : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[max leftWord.length rightWord.length + 1]
      (some ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base leftWord rightWord⟩) =
      some ⟨if mismatch flag leftWord rightWord then differentExit else equalExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  induction leftWord generalizing rightWord flag leftRegister rightRegister with
  | nil =>
    simpa only [List.length_nil, Nat.zero_max] using
      trace_left_empty_inline_MachineCompare left right distinct loopLabel equalExit differentExit program atLoop
        base rightWord ambient flag leftRegister rightRegister
  | cons head tail ih =>
    cases rightWord with
    | nil =>
      rw [List.length_cons, List.length_nil, Nat.max_zero, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[tail.length + 1]
        (TM2.step program ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
          tapesAt left right base (head :: tail) []⟩) = _
      rw [step_cons_nil left right distinct loopLabel equalExit differentExit program atLoop]
      simpa only [List.length_nil, Nat.max_zero, mismatch_true, mismatch_cons_nil] using
        ih [] true none none
    | cons rightHead rightTail =>
      rw [List.length_cons, List.length_cons, Nat.succ_max_succ, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[max tail.length rightTail.length + 1]
        (TM2.step program ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
          tapesAt left right base (head :: tail) (rightHead :: rightTail)⟩) = _
      rw [step_cons_cons left right distinct loopLabel equalExit differentExit program atLoop]
      simpa only [mismatch_cons] using
        ih rightTail (flag || decide (head ≠ rightHead)) none none

theorem compareTrace (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (leftWord rightWord : List Bool) (ambient : σ)
    (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[max leftWord.length rightWord.length + 1]
      (some ⟨some loopLabel, (ambient, false, leftRegister, rightRegister),
        tapesAt left right base leftWord rightWord⟩) =
      some ⟨if leftWord = rightWord then equalExit else differentExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  have h := compareTrace_flag left right distinct loopLabel equalExit differentExit program
    atLoop base leftWord rightWord ambient false leftRegister rightRegister
  by_cases heq : leftWord = rightWord <;> simpa [mismatch, heq] using h

theorem compareTrace_fromTapes (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[max (base left).length (base right).length + 1]
      (some ⟨some loopLabel, (ambient, false, leftRegister, rightRegister), base⟩) =
      some ⟨if base left = base right then equalExit else differentExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  simpa only [tapesAt_self] using
    compareTrace left right distinct loopLabel equalExit differentExit program atLoop base
      (base left) (base right) ambient leftRegister rightRegister

def compareInTime (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (leftRegister rightRegister : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some loopLabel, (ambient, false, leftRegister, rightRegister), base⟩
      (some ⟨if base left = base right then equalExit else differentExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩)
      (max (base left).length (base right).length + 1) where
  steps := max (base left).length (base right).length + 1
  evals_in_steps := compareTrace_fromTapes left right distinct loopLabel equalExit differentExit
    program atLoop base ambient leftRegister rightRegister
  steps_le_m := Nat.le_refl _

@[simp] theorem compareInTime_steps (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (leftRegister rightRegister : Option Bool) :
    (compareInTime left right distinct loopLabel equalExit differentExit program atLoop base
      ambient leftRegister rightRegister).steps =
        max (base left).length (base right).length + 1 := rfl

end DFVSGames.Foundations.Complexity.MachineCompare

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineBinaryNameMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.BinaryOccurrenceRename

open BinaryFormula DFVSGames.Foundations

theorem literal_mem_names (F : Formula) (c : Clause) (hc : c ∈ F.clauses)
    (i : Fin 3) : (c)[i].name ∈ sourceNames F := by
  apply List.mem_flatMap.mpr
  refine ⟨c, hc, ?_⟩
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> simp [clauseNames]

def nameIndex (F : Formula) (name : Nat) (mem : name ∈ sourceNames F) :
    Fin (sourceNames F).length :=
  ⟨(sourceNames F).idxOf name, List.idxOf_lt_length_of_mem mem⟩

def literal (F : Formula) (l : Literal) (mem : l.name ∈ sourceNames F) :
    Target.Literal (sourceNames F).length :=
  ⟨nameIndex F l.name mem, l.positive⟩

def clause (F : Formula) (c : Clause) (mem : c ∈ F.clauses) :
    Target.Clause (sourceNames F).length :=
  #v[literal F (c)[0] (literal_mem_names F c mem 0),
    literal F (c)[1] (literal_mem_names F c mem 1),
    literal F (c)[2] (literal_mem_names F c mem 2)]

def renamed (F : Formula) : Target.Formula where
  «variables» := (sourceNames F).length
  clauses := F.clauses.attach.map (fun c => clause F c.val c.property)

def restrictAssignment (F : Formula) (A : Nat → Bool) :
    Fin (sourceNames F).length → Bool :=
  fun i => A (sourceNames F)[i.val]

def extendAssignment (F : Formula) (A : Fin (sourceNames F).length → Bool) : Nat → Bool :=
  fun name => if mem : name ∈ sourceNames F then A (nameIndex F name mem) else false

@[simp] theorem nameIndex_reads_name (F : Formula) (name : Nat)
    (mem : name ∈ sourceNames F) : (sourceNames F)[(nameIndex F name mem).val] = name :=
  List.getElem_idxOf _

@[simp] theorem clause_eval_restrict (F : Formula) (c : Clause) (mem : c ∈ F.clauses)
    (A : Nat → Bool) : (clause F c mem).eval (restrictAssignment F A) = c.eval A := by
  simp [clause, literal, Target.Clause.eval, Target.Literal.eval,
    BinaryFormula.Clause.eval, BinaryFormula.Literal.eval, restrictAssignment]

@[simp] theorem clause_eval_extend (F : Formula) (c : Clause) (mem : c ∈ F.clauses)
    (A : Fin (sourceNames F).length → Bool) :
    (clause F c mem).eval A = c.eval (extendAssignment F A) := by
  have evalLiteral (l : Literal) (hl : l.name ∈ sourceNames F) :
      (literal F l hl).eval A = l.eval (extendAssignment F A) := by
    simp only [literal, Target.Literal.eval, BinaryFormula.Literal.eval,
      extendAssignment, dite_eq_left hl]
    rfl
  simp [clause, Target.Clause.eval, BinaryFormula.Clause.eval, evalLiteral]

@[simp] theorem renamed_clause_count (F : Formula) :
    (renamed F).clauses.length = F.clauses.length := by simp [renamed]

@[simp] theorem renamed_variable_count (F : Formula) :
    (renamed F).«variables» = 3 * F.clauses.length := by
  exact clauseNames_flat_length F.clauses

end DFVSGames.BinaryOccurrenceRename


namespace DFVSGames.Explicit.MachineOutputContract

open DFVSGames.Foundations
open Target
open scoped BigOperators

structure SimpleBipartite {q : Nat} (game : Instance q) where
  side : Fin game.vertices → Bool
  sourceSide : ∀ i : Fin game.constraints.length,
    side game.constraints[i].source = false
  targetSide : ∀ i : Fin game.constraints.length,
    side game.constraints[i].target = true
  endpoints_injective : Function.Injective (fun i : Fin game.constraints.length =>
    (game.constraints[i].source, game.constraints[i].target))

def permutationEquiv {q : Nat} (table : PermutationTable q) : Equiv.Perm (Fin q) where
  toFun label := table.images[label]
  invFun label := table.inverseImages[label]
  left_inv := table.leftInverse
  right_inv := table.rightInverse

namespace SimpleBipartite

variable {q : Nat} {game : Instance q} (presentation : SimpleBipartite game)

def toBipartiteGame : BipartiteGame
    {v : Fin game.vertices // presentation.side v = false}
    {v : Fin game.vertices // presentation.side v = true}
    (Fin game.constraints.length) (Fin q) where
  left i := ⟨game.constraints[i].source, presentation.sourceSide i⟩
  right i := ⟨game.constraints[i].target, presentation.targetSide i⟩
  permutation i := permutationEquiv game.constraints[i].permutation
  simple := by
    intro i j same
    apply presentation.endpoints_injective
    apply Prod.ext
    · exact congrArg Subtype.val (congrArg Prod.fst same)
    · exact congrArg Subtype.val (congrArg Prod.snd same)

def mergeLabelings
    (left : {v : Fin game.vertices // presentation.side v = false} → Fin q)
    (right : {v : Fin game.vertices // presentation.side v = true} → Fin q) :
    Fin game.vertices → Fin q := fun v =>
  if h : presentation.side v = false then left ⟨v, h⟩
  else right ⟨v, by cases hs : presentation.side v <;> simp_all⟩

@[simp] theorem mergeLabelings_left
    (left : {v : Fin game.vertices // presentation.side v = false} → Fin q)
    (right : {v : Fin game.vertices // presentation.side v = true} → Fin q)
    (v : {v : Fin game.vertices // presentation.side v = false}) :
    presentation.mergeLabelings left right v.val = left v := by
  simp [mergeLabelings, v.property]

@[simp] theorem mergeLabelings_right
    (left : {v : Fin game.vertices // presentation.side v = false} → Fin q)
    (right : {v : Fin game.vertices // presentation.side v = true} → Fin q)
    (v : {v : Fin game.vertices // presentation.side v = true}) :
    presentation.mergeLabelings left right v.val = right v := by
  simp [mergeLabelings, v.property]

end SimpleBipartite

end DFVSGames.Explicit.MachineOutputContract

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_ProductTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit.ProductTarget

open DFVSGames.Foundations
open Target
open MachineOutputContract
open scoped BigOperators

variable {L R E : Type*} {q N M : ℕ}

def fullTable (p : Equiv.Perm (Fin q)) : PermutationTable q where
  images := Vector.ofFn p
  inverseImages := Vector.ofFn p.symm
  leftInverse a := by simp
  rightInverse a := by simp

@[simp] theorem fullTable_images (p : Equiv.Perm (Fin q)) (a : Fin q) :
    (fullTable p).images[a] = p a := by simp [fullTable]

@[simp] theorem permutationEquiv_fullTable (p : Equiv.Perm (Fin q)) :
    permutationEquiv (fullTable p) = p := by
  ext a
  simp [permutationEquiv, fullTable]

def row (G : BipartiteGame L R E (Fin q)) (vertices : (L ⊕ R) ≃ Fin N)
    (edges : Fin M ≃ E) (tables : E → PermutationTable q) (i : Fin M) :
    Constraint N q where
  source := vertices (Sum.inl (G.left (edges i)))
  target := vertices (Sum.inr (G.right (edges i)))
  permutation := tables (edges i)

def render (G : BipartiteGame L R E (Fin q)) (vertices : (L ⊕ R) ≃ Fin N)
    (edges : Fin M ≃ E) (tables : E → PermutationTable q) (hM : 0 < M) :
    Instance q where
  vertices := N
  constraints := List.ofFn (row G vertices edges tables)
  nonempty := by
    intro hempty
    have hlength := congrArg List.length hempty
    simp only [List.length_ofFn, List.length_nil] at hlength
    omega

@[simp] theorem render_length (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M) :
    (render G vertices edges tables hM).constraints.length = M := by
  simp [render]

end DFVSGames.Explicit.ProductTarget


namespace DFVSGames.Explicit.SubdivisionTarget

open DFVSGames.Foundations Target
open MachineOutputContract
open scoped BigOperators

def ofInstance {q : Nat} (H : Instance q) :
    OccurrenceGame (Fin H.vertices) (Fin H.constraints.length) (Fin q) where
  source e := H.constraints[e].source
  target e := H.constraints[e].target
  permutation e := permutationEquiv H.constraints[e].permutation

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

def numericEdgeEquiv (Q : Nat) : Fin (4 * Q) ≃ Fin Q × Fin 4 :=
  (finCongr (Nat.mul_comm 4 Q)).trans finProdFinEquiv.symm

@[simp] theorem numericEdgeEquiv_symm_val (Q : Nat) (e : Fin Q) (i : Fin 4) :
    ((numericEdgeEquiv Q).symm (e, i)).val = 4 * e.val + i.val := by
  change i.val + 4 * e.val = 4 * e.val + i.val
  exact Nat.add_comm _ _

def tables {q : Nat} (H : Instance q) (ei : Fin H.constraints.length × Fin 4) :
    PermutationTable q :=
  if ei.2 = 3 then MachineSubdivisionRows.inverseTable H.constraints[ei.1].permutation
  else MachineSubdivisionRows.identityTable q

def subdivide {q : Nat} (H : Instance q) : Instance q :=
  ProductTarget.render (Subdivision.game (ofInstance H))
    (numericVertexEquiv H.vertices H.constraints.length)
    (numericEdgeEquiv H.constraints.length) (tables H)
    (by have h := H.constraintCount_positive; omega)

@[simp] theorem subdivide_vertices {q : Nat} (H : Instance q) :
    (subdivide H).vertices = H.vertices + 3 * H.constraints.length := rfl

@[simp] theorem subdivide_length {q : Nat} (H : Instance q) :
    (subdivide H).constraints.length = 4 * H.constraints.length := by
  apply ProductTarget.render_length

end DFVSGames.Explicit.SubdivisionTarget


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Games

open scoped BigOperators

noncomputable section

structure FiniteDistribution (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonnegative : ∀ x, 0 ≤ weight x
  normalized : ∑ x, weight x = 1

namespace FiniteDistribution

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

def probability (μ : FiniteDistribution Ω) (event : Ω → Bool) : ℝ :=
  ∑ x, if event x then μ.weight x else 0

@[simp] theorem probability_true (μ : FiniteDistribution Ω) :
    μ.probability (fun _ => true) = 1 := by
  simpa [probability] using μ.normalized

@[simp] theorem probability_false (μ : FiniteDistribution Ω) :
    μ.probability (fun _ => false) = 0 := by
  simp [probability]

def pushforward (μ : FiniteDistribution Ω) (f : Ω → Γ) : FiniteDistribution Γ := by
  classical
  exact
    { weight := fun y => ∑ x, if f x = y then μ.weight x else 0
      nonnegative := fun y => Finset.sum_nonneg fun x _ => by
        split
        · exact μ.nonnegative x
        · exact le_rfl
      normalized := by
        rw [Finset.sum_comm]
        simpa using μ.normalized }

def transport (μ : FiniteDistribution Ω) (equiv : Ω ≃ Γ) : FiniteDistribution Γ where
  weight y := μ.weight (equiv.symm y)
  nonnegative y := μ.nonnegative (equiv.symm y)
  normalized := by rw [equiv.symm.sum_comp, μ.normalized]

def iid (μ : FiniteDistribution Ω) (n : Nat) : FiniteDistribution (Fin n → Ω) where
  weight x := ∏ i, μ.weight (x i)
  nonnegative x := Finset.prod_nonneg fun i _ => μ.nonnegative (x i)
  normalized := by rw [← Fintype.sum_pow, μ.normalized, one_pow]

end FiniteDistribution

abbrev Strategy (Q₁ Q₂ A₁ A₂ : Type*) := (Q₁ → A₁) × (Q₂ → A₂)

structure Game (Q₁ Q₂ A₁ A₂ : Type*) [Fintype Q₁] [Fintype Q₂]
    [Fintype A₁] [Fintype A₂] where
  questions : FiniteDistribution (Q₁ × Q₂)
  accepts : Q₁ → Q₂ → A₁ → A₂ → Bool

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

def wins (G : Game Q₁ Q₂ A₁ A₂) (strategy : Strategy Q₁ Q₂ A₁ A₂)
    (questions : Q₁ × Q₂) : Bool :=
  G.accepts questions.1 questions.2 (strategy.1 questions.1) (strategy.2 questions.2)

def success (G : Game Q₁ Q₂ A₁ A₂) (strategy : Strategy Q₁ Q₂ A₁ A₂) : ℝ :=
  G.questions.probability (G.wins strategy)

def tupleQuestionEquiv (n : Nat) :
    (Fin n → Q₁ × Q₂) ≃ (Fin n → Q₁) × (Fin n → Q₂) where
  toFun questions := (fun i => (questions i).1, fun i => (questions i).2)
  invFun questions := fun i => (questions.1 i, questions.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

def repetition (G : Game Q₁ Q₂ A₁ A₂) (n : Nat) :
    Game (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂) := by
  classical
  exact
    { questions := (G.questions.iid n).transport (tupleQuestionEquiv n)
      accepts := fun x y a b => decide (∀ i, G.accepts (x i) (y i) (a i) (b i) = true) }

@[simp] theorem repetition_question_weight (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (questions : (Fin n → Q₁) × (Fin n → Q₂)) :
    (G.repetition n).questions.weight questions =
      ∏ i, G.questions.weight (questions.1 i, questions.2 i) := rfl

@[simp] theorem repetition_accepts_iff (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (x : Fin n → Q₁) (y : Fin n → Q₂) (a : Fin n → A₁) (b : Fin n → A₂) :
    (G.repetition n).accepts x y a b = true ↔
      ∀ i, G.accepts (x i) (y i) (a i) (b i) = true := by
  classical
  simp [repetition]

def coordinateWin (G : Game Q₁ Q₂ A₁ A₂) {n : Nat}
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (coordinate : Fin n) (questions : (Fin n → Q₁) × (Fin n → Q₂)) : Bool :=
  G.accepts (questions.1 coordinate) (questions.2 coordinate)
    (strategy.1 questions.1 coordinate) (strategy.2 questions.2 coordinate)

def selectedWins (G : Game Q₁ Q₂ A₁ A₂) {n : Nat}
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (questions : (Fin n → Q₁) × (Fin n → Q₂)) : Bool := by
  classical
  exact decide (∀ i ∈ selected, G.coordinateWin strategy i questions = true)

@[simp] theorem selectedWins_empty (G : Game Q₁ Q₂ A₁ A₂) {n : Nat}
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (questions : (Fin n → Q₁) × (Fin n → Q₂)) :
    G.selectedWins strategy ∅ questions = true := by
  simp [selectedWins]

end Game

end

end DFVSGames.Foundations.Games


namespace DFVSGames.Foundations.Games

open scoped BigOperators

noncomputable section

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]

def value (G : Game Q₁ Q₂ A₁ A₂) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty G.success

end Game

end

end DFVSGames.Foundations.Games


namespace DFVSGames.Foundations.Games
open scoped BigOperators
noncomputable section

namespace FiniteDistribution
variable {Ω Γ Q A : Type*} [Fintype Ω] [Fintype Γ] [Fintype Q] [Fintype A]

theorem eq_of_weight_eq {μ ν : FiniteDistribution Ω}
    (h : ∀ x, μ.weight x = ν.weight x) : μ = ν := by
  cases μ with
  | mk w hw hs =>
    cases ν with
    | mk w' hw' hs' =>
      have he : w = w' := funext h
      cases he
      rfl

def table [DecidableEq Q] (responses : Q → FiniteDistribution A) :
    FiniteDistribution (Q → A) := by
  classical
  exact
    { weight := fun answers => ∏ q, (responses q).weight (answers q)
      nonnegative := fun answers => Finset.prod_nonneg fun q _ =>
        (responses q).nonnegative (answers q)
      normalized := by
        rw [← Fintype.prod_sum]
        simp only [FiniteDistribution.normalized, Finset.prod_const_one] }

def product (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ) :
    FiniteDistribution (Ω × Γ) where
  weight x := μ.weight x.1 * ν.weight x.2
  nonnegative x := mul_nonneg (μ.nonnegative _) (ν.nonnegative _)
  normalized := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ν.normalized, mul_one]
    exact μ.normalized

end FiniteDistribution

end
end DFVSGames.Foundations.Games


namespace DFVSGames.Foundations.Games.FiniteDistribution
open scoped BigOperators
noncomputable section

def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteDistribution Ω where
  weight _ := 1 / (Fintype.card Ω : ℝ)
  nonnegative _ := div_nonneg zero_le_one (Nat.cast_nonneg _)
  normalized := by
    have hn : (Fintype.card Ω : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_div]
    exact mul_inv_cancel₀ hn

end
end DFVSGames.Foundations.Games.FiniteDistribution


namespace DFVSGames.Repetition

open DFVSGames.Foundations.Games
open scoped BigOperators

noncomputable section

variable {Q₁ Q₂ A₁ A₂ R₁ R₂ B₁ B₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂]

def IsProjection (G : Game Q₁ Q₂ A₁ A₂) : Prop :=
  ∀ x y a b b', G.accepts x y a b = true →
    G.accepts x y a b' = true → b = b'

end
end DFVSGames.Repetition

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Product
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit

open DFVSGames.Foundations.Games
open scoped BigOperators

namespace BipartiteGame

variable {L R E A : Type*}

def product (G : BipartiteGame L R E A) (t : ℕ) :
    BipartiteGame (Fin t → L) (Fin t → R) (Fin t → E) (Fin t → A) where
  left e i := G.left (e i)
  right e i := G.right (e i)
  permutation e :=
    { toFun := fun a i => G.permutation (e i) (a i)
      invFun := fun a i => (G.permutation (e i)).symm (a i)
      left_inv := fun a => by funext i; exact (G.permutation (e i)).left_inv (a i)
      right_inv := fun a => by funext i; exact (G.permutation (e i)).right_inv (a i) }
  simple := by
    intro e f h
    funext i
    apply G.simple
    exact Prod.ext (congrFun (congrArg Prod.fst h) i)
      (congrFun (congrArg Prod.snd h) i)

@[simp] theorem product_left (G : BipartiteGame L R E A) (t : ℕ)
    (e : Fin t → E) (i : Fin t) : (G.product t).left e i = G.left (e i) := rfl

@[simp] theorem product_right (G : BipartiteGame L R E A) (t : ℕ)
    (e : Fin t → E) (i : Fin t) : (G.product t).right e i = G.right (e i) := rfl

@[simp] theorem product_permutation (G : BipartiteGame L R E A) (t : ℕ)
    (e : Fin t → E) (a : Fin t → A) (i : Fin t) :
    (G.product t).permutation e a i = G.permutation (e i) (a i) := rfl

noncomputable section

variable [Fintype L] [Fintype R] [Fintype E] [Fintype A] [Nonempty E]

def toGame (G : BipartiteGame L R E A) : Game L R A A := by
  classical
  exact
    { questions := (FiniteDistribution.uniform E).pushforward
        (fun e => (G.left e, G.right e))
      accepts := fun x y a b => decide
        (∃ e, G.left e = x ∧ G.right e = y ∧ b = G.permutation e a) }

@[simp] theorem toGame_accepts_on_edge (G : BipartiteGame L R E A)
    (e : E) (a b : A) :
    G.toGame.accepts (G.left e) (G.right e) a b = true ↔
      b = G.permutation e a := by
  classical
  simp only [toGame, decide_eq_true_eq]
  constructor
  · rintro ⟨f, hleft, hright, h⟩
    have hf : f = e := G.simple (Prod.ext hleft hright)
    simpa [hf] using h
  · intro h
    exact ⟨e, rfl, rfl, h⟩

end

def relabel {B : Type*} (G : BipartiteGame L R E A) (e : A ≃ B) :
    BipartiteGame L R E B where
  left := G.left
  right := G.right
  permutation f := e.symm.trans ((G.permutation f).trans e)
  simple := G.simple

end BipartiteGame

end DFVSGames.Explicit


namespace DFVSGames.Explicit.ProductPaddedOutput

open DFVSGames.Foundations
open Target
open MachineOutputContract
open ProductTarget
open scoped BigOperators

namespace Embedded

variable {L R E : Type*} {q N M : ℕ}

def row (G : BipartiteGame L R E (Fin q)) (vertices : (L ⊕ R) ↪ Fin N)
    (edges : Fin M ≃ E) (i : Fin M) : Constraint N q where
  source := vertices (Sum.inl (G.left (edges i)))
  target := vertices (Sum.inr (G.right (edges i)))
  permutation := fullTable (G.permutation (edges i))

def render (G : BipartiteGame L R E (Fin q)) (vertices : (L ⊕ R) ↪ Fin N)
    (edges : Fin M ≃ E) (hM : 0 < M) : Instance q where
  vertices := N
  constraints := List.ofFn (row G vertices edges)
  nonempty := by
    intro h
    have hlen := congrArg List.length h
    simp only [List.length_ofFn, List.length_nil] at hlen
    omega

@[simp] theorem render_length (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ↪ Fin N) (edges : Fin M ≃ E) (hM : 0 < M) :
    (render G vertices edges hM).constraints.length = M := by simp [render]

end Embedded

variable {q : ℕ} (H : Instance q) (presentation : SimpleBipartite H)

local instance productConstraintIndicesNonempty_rf85d43_1 : Nonempty (Fin H.constraints.length) :=
  ⟨⟨0, H.constraintCount_positive⟩⟩
abbrev Left := {v : Fin H.vertices // presentation.side v = false}
abbrev Right := {v : Fin H.vertices // presentation.side v = true}

def graph (t : ℕ) : BipartiteGame
    (Fin t → Left H presentation) (Fin t → Right H presentation)
    (Fin t → Fin H.constraints.length) (Fin (q ^ t)) :=
  (presentation.toBipartiteGame.product t).relabel finFunctionFinEquiv

def vertices (t : ℕ) (ht : 0 < t) :
    ((Fin t → Left H presentation) ⊕ (Fin t → Right H presentation)) ↪
      Fin (H.vertices ^ t) where
  toFun := Sum.elim
    (fun x => finFunctionFinEquiv (fun i => (x i).val))
    (fun y => finFunctionFinEquiv (fun i => (y i).val))
  inj' := by
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        apply congrArg Sum.inl
        funext i
        exact Subtype.ext (congrFun (finFunctionFinEquiv.injective h) i)
      | inr y =>
        have hfirst := congrFun (finFunctionFinEquiv.injective h) ⟨0, ht⟩
        have hs := congrArg presentation.side hfirst
        rw [(x ⟨0, ht⟩).property, (y ⟨0, ht⟩).property] at hs
        cases hs
    | inr x =>
      cases y with
      | inl y =>
        have hfirst := congrFun (finFunctionFinEquiv.injective h) ⟨0, ht⟩
        have hs := congrArg presentation.side hfirst
        rw [(x ⟨0, ht⟩).property, (y ⟨0, ht⟩).property] at hs
        cases hs
      | inr y =>
        apply congrArg Sum.inr
        funext i
        exact Subtype.ext (congrFun (finFunctionFinEquiv.injective h) i)

def outputRow (t : ℕ) (ht : 0 < t) (i : Fin (H.constraints.length ^ t)) :
    Constraint (H.vertices ^ t) (q ^ t) :=
  Embedded.row (graph H presentation t) (vertices H presentation t ht)
    finFunctionFinEquiv.symm i

def output (t : ℕ) (ht : 0 < t) : Instance (q ^ t) :=
  Embedded.render (graph H presentation t) (vertices H presentation t ht)
    finFunctionFinEquiv.symm (pow_pos H.constraintCount_positive t)

@[simp] theorem output_vertices (t : ℕ) (ht : 0 < t) :
    (output H presentation t ht).vertices = H.vertices ^ t := rfl

@[simp] theorem output_constraints (t : ℕ) (ht : 0 < t) :
    (output H presentation t ht).constraints = List.ofFn (outputRow H presentation t ht) := rfl

@[simp] theorem output_length (t : ℕ) (ht : 0 < t) :
    (output H presentation t ht).constraints.length = H.constraints.length ^ t := by simp

end DFVSGames.Explicit.ProductPaddedOutput


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineLookupSpec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineLookupSpec

@[simp] theorem decodeWords_encodeWord (i : Nat) :
    decodeWords (encodeWord i) = some [i] := by
  simpa [encodeWords] using decodeWords_encodeWords [i]

end DFVSGames.Foundations.Complexity.MachineLookupSpec


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineAffineLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineUnaryMultiply

open Turing
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

def resultTapes (slots : Fin 5 ↪ K) (base : K → List Bool) (product : ℕ) : K → List Bool :=
  Function.update base (slots 2) (encodeWord product ++ base (slots 2))

@[simp] theorem resultTapes_output (slots : Fin 5 ↪ K) (base : K → List Bool) (p : ℕ) :
    resultTapes slots base p (slots 2) = encodeWord p ++ base (slots 2) := by
  simp [resultTapes]

end DFVSGames.Foundations.Complexity.MachineUnaryMultiply

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineUnaryAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineUnaryAddAt

open Turing
open Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def finish (destination : K) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .load (fun state => (state.1, none)) (exitAt destination exit)

def loop (source destination : K) (loopLabel : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.push destination (fun _ => true) (.goto fun _ => loopLabel))
      (.branch (fun state => state.2.isSome)
        (.push source (fun _ => false) (finish destination exit))
        (finish destination exit)))

def unaryTapes (source destination : K) (base : K → List Bool) (a b : Nat)
    (sourceSuffix destinationSuffix : List Bool) : K → List Bool :=
  tapesAt source destination base (encodeWord a ++ sourceSuffix)
    (encodeWord b ++ destinationSuffix)

@[simp] theorem unaryTapes_source (source destination : K) (distinct : source ≠ destination)
    (base : K → List Bool) (a b : Nat) (sourceSuffix destinationSuffix : List Bool) :
    unaryTapes source destination base a b sourceSuffix destinationSuffix source =
      encodeWord a ++ sourceSuffix := by
  simp [unaryTapes, distinct]

@[simp] theorem unaryTapes_destination (source destination : K)
    (base : K → List Bool) (a b : Nat) (sourceSuffix destinationSuffix : List Bool) :
    unaryTapes source destination base a b sourceSuffix destinationSuffix destination =
      encodeWord b ++ destinationSuffix := by
  simp [unaryTapes]

theorem update_source_inline_MachineUnaryAddAt (source destination : K) (distinct : source ≠ destination)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt source destination base input output) source replacement =
      tapesAt source destination base replacement output := by
  funext k
  by_cases hs : k = source
  · subst k
    simp [tapesAt, distinct]
  · by_cases hd : k = destination
    · subst k
      simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hs, hd]

theorem update_destination_inline_MachineUnaryAddAt (source destination : K)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt source destination base input output) destination replacement =
      tapesAt source destination base input replacement := by
  funext k
  by_cases hd : k = destination
  · subst k
    simp [tapesAt]
  · simp [tapesAt, hd]

theorem stepAux_true (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ) (base : K → List Bool)
    (input output : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (loop source destination loopLabel exit) (ambient, register)
      (tapesAt source destination base (true :: input) output) =
      ⟨some loopLabel, (ambient, some true),
        tapesAt source destination base input (true :: output)⟩ := by
  simp [loop, TM2.stepAux, distinct, update_source_inline_MachineUnaryAddAt, update_destination_inline_MachineUnaryAddAt]

theorem stepAux_false (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ) (base : K → List Bool)
    (input output : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (loop source destination loopLabel exit) (ambient, register)
      (tapesAt source destination base (false :: input) output) =
      ⟨exit, (ambient, none), tapesAt source destination base (false :: input) output⟩ := by
  cases exit <;> simp [loop, finish, exitAt, TM2.stepAux, distinct, update_source_inline_MachineUnaryAddAt]

theorem stepAux_succ (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ) (base : K → List Bool) (a b : Nat)
    (sourceSuffix destinationSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (loop source destination loopLabel exit) (ambient, register)
      (unaryTapes source destination base (a + 1) b sourceSuffix destinationSuffix) =
      ⟨some loopLabel, (ambient, some true),
        unaryTapes source destination base a (b + 1) sourceSuffix destinationSuffix⟩ := by
  simpa only [unaryTapes, encodeWord, List.replicate_succ, List.cons_append] using
    stepAux_true source destination distinct loopLabel exit base
      (encodeWord a ++ sourceSuffix) (encodeWord b ++ destinationSuffix) ambient register

theorem stepAux_zero (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ) (base : K → List Bool) (b : Nat)
    (sourceSuffix destinationSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (loop source destination loopLabel exit) (ambient, register)
      (unaryTapes source destination base 0 b sourceSuffix destinationSuffix) =
      ⟨exit, (ambient, none),
        unaryTapes source destination base 0 b sourceSuffix destinationSuffix⟩ := by
  simpa only [unaryTapes, encodeWord, List.replicate_zero, List.nil_append,
    List.singleton_append] using
    stepAux_false source destination distinct loopLabel exit base sourceSuffix
      (encodeWord b ++ destinationSuffix) ambient register

theorem step_succ (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = loop source destination loopLabel exit)
    (base : K → List Bool) (a b : Nat) (sourceSuffix destinationSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some loopLabel, (ambient, register),
      unaryTapes source destination base (a + 1) b sourceSuffix destinationSuffix⟩ =
      some ⟨some loopLabel, (ambient, some true),
        unaryTapes source destination base a (b + 1) sourceSuffix destinationSuffix⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (unaryTapes source destination base (a + 1) b sourceSuffix destinationSuffix)) = _
  rw [atLoop, stepAux_succ source destination distinct]

theorem step_zero (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = loop source destination loopLabel exit)
    (base : K → List Bool) (b : Nat) (sourceSuffix destinationSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some loopLabel, (ambient, register),
      unaryTapes source destination base 0 b sourceSuffix destinationSuffix⟩ =
      some ⟨exit, (ambient, none),
        unaryTapes source destination base 0 b sourceSuffix destinationSuffix⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (unaryTapes source destination base 0 b sourceSuffix destinationSuffix)) = _
  rw [atLoop, stepAux_zero source destination distinct]

theorem addTrace (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = loop source destination loopLabel exit)
    (base : K → List Bool) (a b : Nat) (sourceSuffix destinationSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[a + 1]
      (some ⟨some loopLabel, (ambient, register),
        unaryTapes source destination base a b sourceSuffix destinationSuffix⟩) =
      some ⟨exit, (ambient, none),
        unaryTapes source destination base 0 (a + b) sourceSuffix destinationSuffix⟩ := by
  induction a generalizing b register with
  | zero =>
    simpa only [Nat.zero_add, Function.iterate_one, MachineComposition.advance_some] using
      step_zero source destination distinct loopLabel exit program atLoop
        base b sourceSuffix destinationSuffix ambient register
  | succ a ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[a + 1]
      (TM2.step program ⟨some loopLabel, (ambient, register),
        unaryTapes source destination base (a + 1) b sourceSuffix destinationSuffix⟩) = _
    rw [step_succ source destination distinct loopLabel exit program atLoop]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (b + 1) (some true)

theorem addFromTapes (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = loop source destination loopLabel exit)
    (base : K → List Bool) (a b : Nat) (sourceSuffix destinationSuffix : List Bool)
    (sourceInput : base source = encodeWord a ++ sourceSuffix)
    (destinationInput : base destination = encodeWord b ++ destinationSuffix)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[a + 1]
      (some ⟨some loopLabel, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        unaryTapes source destination base 0 (a + b) sourceSuffix destinationSuffix⟩ := by
  have hbase : unaryTapes source destination base a b sourceSuffix destinationSuffix =
      base := by
    simp only [unaryTapes, ← sourceInput, ← destinationInput, tapesAt_self]
  have h := addTrace source destination distinct loopLabel exit program atLoop
    base a b sourceSuffix destinationSuffix ambient register
  rw [hbase] at h
  exact h

def addInTime (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = loop source destination loopLabel exit)
    (base : K → List Bool) (a b : Nat) (sourceSuffix destinationSuffix : List Bool)
    (sourceInput : base source = encodeWord a ++ sourceSuffix)
    (destinationInput : base destination = encodeWord b ++ destinationSuffix)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some loopLabel, (ambient, register), base⟩
      (some ⟨exit, (ambient, none),
        unaryTapes source destination base 0 (a + b) sourceSuffix destinationSuffix⟩)
      (a + 1) where
  steps := a + 1
  evals_in_steps := addFromTapes source destination distinct loopLabel exit program atLoop
    base a b sourceSuffix destinationSuffix sourceInput destinationInput ambient register
  steps_le_m := Nat.le_refl _

@[simp] theorem addInTime_steps (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = loop source destination loopLabel exit)
    (base : K → List Bool) (a b : Nat) (sourceSuffix destinationSuffix : List Bool)
    (sourceInput : base source = encodeWord a ++ sourceSuffix)
    (destinationInput : base destination = encodeWord b ++ destinationSuffix)
    (ambient : σ) (register : Option Bool) :
    (addInTime source destination distinct loopLabel exit program atLoop base a b
      sourceSuffix destinationSuffix sourceInput destinationInput ambient register).steps =
      a + 1 := rfl

end DFVSGames.Foundations.Complexity.MachineUnaryAddAt


namespace DFVSGames.Foundations.Complexity.MachineRadixStep

open Turing

variable {K Λ σ : Type}

def multiplySlots (slots : Fin 6 ↪ K) : Fin 5 ↪ K :=
  (Fin.succAboveEmb (2 : Fin 6)).trans slots

@[simp] theorem multiplySlots_zero (slots : Fin 6 ↪ K) : multiplySlots slots 0 = slots 0 := rfl
@[simp] theorem multiplySlots_one (slots : Fin 6 ↪ K) : multiplySlots slots 1 = slots 1 := rfl
@[simp] theorem multiplySlots_two (slots : Fin 6 ↪ K) : multiplySlots slots 2 = slots 3 := rfl
@[simp] theorem multiplySlots_three (slots : Fin 6 ↪ K) : multiplySlots slots 3 = slots 4 := rfl
@[simp] theorem multiplySlots_four (slots : Fin 6 ↪ K) : multiplySlots slots 4 = slots 5 := rfl

variable [DecidableEq K]

def resultTapes (slots : Fin 6 ↪ K) (base : K → List Bool) (value : ℕ) : K → List Bool :=
  Function.update base (slots 3) (encodeWord value ++ base (slots 3))

@[simp] theorem resultTapes_output (slots : Fin 6 ↪ K) (base : K → List Bool) (value : ℕ) :
    resultTapes slots base value (slots 3) = encodeWord value ++ base (slots 3) := by
  simp [resultTapes]

end DFVSGames.Foundations.Complexity.MachineRadixStep


namespace DFVSGames.Foundations.Complexity.MachineHorner

open Turing

variable {K Λ σ : Type} {width : Nat}

abbrev Layout (width : Nat) := Fin 6 ⊕ Fin width

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

variable [DecidableEq K]

def resultTapes (slots : Layout width ↪ K) (base : K → List Bool) (acc : Nat) : K → List Bool :=
  Function.update base (slots (.inl 3)) (encodeWord acc ++ base (slots (.inl 3)))

open scoped BigOperators

@[simp] theorem resultTapes_output (slots : Layout width ↪ K) (base : K → List Bool) (acc : Nat) :
    resultTapes slots base acc (slots (.inl 3)) = encodeWord acc ++ base (slots (.inl 3)) := by
  simp [resultTapes]

end DFVSGames.Foundations.Complexity.MachineHorner

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineProductField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit.ProductMachineSemantics

open DFVSGames.Foundations
open Target
open Complexity
open MachineOutputContract

variable {n q t : ℕ}

def inputTable (H : Instance q) : List ℕ := H.constraints.flatMap constraintWords

end DFVSGames.Explicit.ProductMachineSemantics

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineProductPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit.MachineProductPower

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition
open DFVSGames.Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K] {exponent : Nat}

def digits (i : Nat) : Nat := if i = 0 then 1 else 0

end DFVSGames.Explicit.MachineProductPower


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_FieldArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceClauseLookup

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition

inductive Tape
  | formula | index | work | scratch | field (slot : Fin 6)
  deriving DecidableEq, Fintype

def scanTapes (base : Tape → List Bool) (index : Nat)
    (indexSuffix input : List Bool) : Tape → List Bool :=
  MachineUnaryCounter.counterTapes .index (Function.update base .work input) index indexSuffix

@[simp] theorem scanTapes_work (base : Tape → List Bool) (i : Nat)
    (indexSuffix input : List Bool) : scanTapes base i indexSuffix input .work = input := by
  simp [scanTapes, MachineUnaryCounter.counterTapes]

@[simp] theorem scanTapes_index (base : Tape → List Bool) (i : Nat)
    (indexSuffix input : List Bool) :
    scanTapes base i indexSuffix input .index = encodeWord i ++ indexSuffix := by
  simp [scanTapes, MachineUnaryCounter.counterTapes]

end DFVSGames.Foundations.Hastad.SourceClauseLookup

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

inductive Tape (u : Nat) (Extra : Type)
  | formula | index | work | scratch | copyScratch
  | current (coordinate : Fin u) | remaining (coordinate : Fin u)
  | field (coordinate : Fin u) (slot : Fin 6)
  | extra (value : Extra)
  deriving DecidableEq, Fintype

variable {u : Nat} {Extra : Type}

def place (j : Fin u) : SourceClauseLookup.Tape → Tape u Extra
  | .formula => .formula | .index => .index | .work => .work | .scratch => .scratch
  | .field s => .field j s

def fill (j : Fin u) (base : Tape u Extra → List Bool)
    (localTapes : SourceClauseLookup.Tape → List Bool) : Tape u Extra → List Bool
  | .formula => localTapes .formula | .index => localTapes .index
  | .work => localTapes .work | .scratch => localTapes .scratch
  | .field i s => if i = j then localTapes (.field s) else base (.field i s)
  | p => base p

@[simp] theorem fill_place (j : Fin u) (base : Tape u Extra → List Bool)
    (localTapes : SourceClauseLookup.Tape → List Bool) (p : SourceClauseLookup.Tape) :
    fill j base localTapes (place j p) = localTapes p := by
  cases p <;> simp [fill, place]

@[simp] theorem fill_self (j : Fin u) (base : Tape u Extra → List Bool) :
    fill j base (base ∘ place j) = base := by
  funext p
  cases p <;> simp [fill, place]
  intro h
  subst h
  rfl

variable [DecidableEq Extra]

def coordinateOutput {n : Nat} (j : Fin u) (clause : Target.Clause n)
    (base : Tape u Extra → List Bool) : Tape u Extra → List Bool
  | .index | .work => []
  | .field k s => if k = j then
      encodeWord ((clauseWords clause)[s.val]'(by simp)) ++ base (.field k s)
    else base (.field k s)
  | p => base p

omit [DecidableEq Extra] in
@[simp] theorem coordinateOutput_current {n : Nat} (j k : Fin u) (clause : Target.Clause n)
    (base : Tape u Extra → List Bool) :
    coordinateOutput j clause base (.current k) = base (.current k) := rfl

omit [DecidableEq Extra] in
@[simp] theorem coordinateOutput_remaining {n : Nat} (j k : Fin u) (clause : Target.Clause n)
    (base : Tape u Extra → List Bool) :
    coordinateOutput j clause base (.remaining k) = base (.remaining k) := rfl

omit [DecidableEq Extra] in
@[simp] theorem coordinateOutput_field {n : Nat} (j : Fin u) (s : Fin 6)
    (clause : Target.Clause n) (base : Tape u Extra → List Bool) :
    coordinateOutput j clause base (.field j s) =
      encodeWord ((clauseWords clause)[s.val]'(by simp)) ++ base (.field j s) := by
  simp [coordinateOutput]

end DFVSGames.Foundations.Hastad.SourceContextLoad


noncomputable section

namespace DFVSGames.Foundations.Hastad

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

end DFVSGames.Foundations.Hastad
end


noncomputable section

namespace DFVSGames.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def thirdQuery (π : J → I) (f : Cube I) (g μ : Cube J) : Cube J :=
  cubeXor g (cubeXor (fun y => f (π y)) μ)

end DFVSGames.Foundations.Hastad
end


noncomputable section

namespace DFVSGames.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

def cubeFlip (f : Cube I) : Cube I := fun i => !(f i)

omit [Fintype I] [DecidableEq I] in
@[simp] theorem cubeFlip_cubeFlip (f : Cube I) : cubeFlip (cubeFlip f) = f := by
  funext i
  simp [cubeFlip]

def representative (i₀ : I) (f : Cube I) : Cube I :=
  if f i₀ then cubeFlip f else f

omit [Fintype I] [DecidableEq I] in
theorem representative_at (i₀ : I) (f : Cube I) :
    representative i₀ f i₀ = false := by
  cases hf : f i₀ <;> simp [representative, cubeFlip, hf]

abbrev HalfCube (i₀ : I) := {f : Cube I // f i₀ = false}

def canonicalInput (i₀ : I) (f : Cube I) : HalfCube i₀ :=
  ⟨representative i₀ f, representative_at i₀ f⟩

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

end DFVSGames.Foundations.Hastad
end

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

structure Equation (Name : Type) where
  first : Name
  second : Name
  third : Name
  rhs : Bool

end DFVSGames.Reduction.CloneGap


namespace DFVSGames.Foundations.Hastad.FoldedEquation

open DFVSGames.Reduction.CloneGap
open scoped BigOperators

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

abbrev Address (i₀ : I) (j₀ : J) := HalfCube i₀ ⊕ HalfCube j₀

def rhsCorrection (π : J → I) (i₀ : I) (j₀ : J)
    (f : Cube I) (μ : Cube J) : Bool := f i₀ ^^ f (π j₀) ^^ μ j₀

def equation (π : J → I) (i₀ : I) (j₀ : J)
    (f : Cube I) (g μ : Cube J) : Equation (Address i₀ j₀) where
  first := .inl (canonicalInput i₀ f)
  second := .inr (canonicalInput j₀ g)
  third := .inr (canonicalInput j₀ (thirdQuery π f g μ))
  rhs := rhsCorrection π i₀ j₀ f μ

def conditionedEquation (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true})
    (f : Cube I) (g μ : Cube J) : Equation (Address i₀ j₀) :=
  equation (fun j => π j.val) i₀ j₀ f (restrictQuery valid g) (restrictQuery valid μ)

end DFVSGames.Foundations.Hastad.FoldedEquation


namespace DFVSGames.Foundations.Hastad

open DFVSGames.Reduction.CloneGap
open scoped BigOperators

def mapEquation {Name Name' : Type} (rename : Name → Name')
    (e : Equation Name) : Equation Name' where
  first := rename e.first
  second := rename e.second
  third := rename e.third
  rhs := e.rhs

namespace EmptyContext

variable {I : Type} [Fintype I] [DecidableEq I]

abbrev Address (i₀ : I) := HalfCube i₀ ⊕ Unit

def equation (i₀ : I) (f : Cube I) : Equation (Address i₀) where
  first := .inl (canonicalInput i₀ f)
  second := .inr ()
  third := .inr ()
  rhs := f i₀

omit [Fintype I] [DecidableEq I] in
@[simp] theorem equation_second_eq_third (i₀ : I) (f : Cube I) :
    (equation i₀ f).second = (equation i₀ f).third := rfl

def pairedEquations (i₀ : I) (f : Cube I) : List (Equation (Address i₀)) :=
  [equation i₀ f, equation i₀ (cubeFlip f)]

omit [Fintype I] [DecidableEq I] in
@[simp] theorem pairedEquations_length (i₀ : I) (f : Cube I) :
    (pairedEquations i₀ f).length = 2 := rfl

end EmptyContext
end DFVSGames.Foundations.Hastad


namespace DFVSGames.Reduction.FiniteNoise

open scoped BigOperators

def realizedBit {D : Nat} (z : Fin D) : Bool := decide (z.val = 0)

def realizedNoise {A : Type*} {D : Nat} (z : A → Fin D) : A → Bool :=
  fun a => realizedBit (z a)

end DFVSGames.Reduction.FiniteNoise


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_Tape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace DFVSGames.Foundations.Hastad.SourceTape

open scoped BigOperators
open DFVSGames.Reduction.FiniteNoise

abbrev TestTape (I J : Type*) (D : ℕ) :=
  Cube I × ((J → Fin D) × Cube J)


end DFVSGames.Foundations.Hastad.SourceTape

end


namespace DFVSGames.Foundations.Hastad.SourceContexts

open Target PCP

def clauseAnswerEquiv : ClauseAnswer ≃ Bool × Bool × Bool where
  toFun a := (a.first, a.second, a.third)
  invFun a := ⟨a.1, a.2.1, a.2.2⟩
  left_inv a := by cases a; rfl
  right_inv a := by rcases a with ⟨a, b, c⟩; rfl

def clauseAnswerFinEquiv : ClauseAnswer ≃ Fin 8 :=
  clauseAnswerEquiv.trans
    ((Equiv.prodCongr finTwoEquiv.symm
      (Equiv.prodCongr finTwoEquiv.symm finTwoEquiv.symm)).trans
      ((Equiv.prodCongr (Equiv.refl (Fin 2)) finProdFinEquiv).trans finProdFinEquiv))

instance clauseAnswerFintype : Fintype ClauseAnswer :=
  Fintype.ofEquiv (Bool × Bool × Bool) clauseAnswerEquiv.symm

instance slotFintype : Fintype Slot where
  elems := {.first, .second, .third}
  complete s := by cases s <;> simp

@[simp] theorem card_clauseAnswer : Fintype.card ClauseAnswer = 8 := by
  rw [Fintype.card_congr clauseAnswerFinEquiv]
  rfl

@[simp] theorem card_slot : Fintype.card Slot = 3 := by decide

abbrev I (u : ℕ) := Fin u → Bool
abbrev J (u : ℕ) := Fin u → ClauseAnswer
abbrev ClauseContext (F : Formula) (u : ℕ) := Fin u → Fin F.clauses.length
abbrev VariableContext (F : Formula) (u : ℕ) := Fin u → Fin F.«variables»
abbrev SlotContext (u : ℕ) := Fin u → Slot

@[simp] theorem card_I (u : ℕ) : Fintype.card (I u) = 2 ^ u := by simp [I]
@[simp] theorem card_J (u : ℕ) : Fintype.card (J u) = 8 ^ u := by simp [J]
@[simp] theorem card_ClauseContext (F : Formula) (u : ℕ) :
    Fintype.card (ClauseContext F u) = F.clauses.length ^ u := by simp [ClauseContext]
@[simp] theorem card_VariableContext (F : Formula) (u : ℕ) :
    Fintype.card (VariableContext F u) = F.«variables» ^ u := by simp [VariableContext]
@[simp] theorem card_SlotContext (u : ℕ) :
    Fintype.card (SlotContext u) = 3 ^ u := by simp [SlotContext]

def localConsistent {n : ℕ} (clause : Clause n) (answer : ClauseAnswer) : Bool :=
  decide (∀ s s' : Slot, nameAt clause s = nameAt clause s' →
    answerAt answer s = answerAt answer s')

@[simp] theorem localConsistent_eq_true_iff {n : ℕ}
    (clause : Clause n) (answer : ClauseAnswer) :
    localConsistent clause answer = true ↔
      ∀ s s' : Slot, nameAt clause s = nameAt clause s' →
        answerAt answer s = answerAt answer s' := by
  simp [localConsistent]

def validJ (F : Formula) {u : ℕ} (c : ClauseContext F u) (j : J u) : Bool :=
  decide ((∀ t, localSatisfies (clauseAt F (c t)) (j t) = true) ∧
    ∀ t t' s s', nameAt (clauseAt F (c t)) s = nameAt (clauseAt F (c t')) s' →
      answerAt (j t) s = answerAt (j t') s')

@[simp] theorem validJ_eq_true_iff (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (j : J u) :
    validJ F c j = true ↔
      (∀ t, localSatisfies (clauseAt F (c t)) (j t) = true) ∧
      ∀ t t' s s', nameAt (clauseAt F (c t)) s = nameAt (clauseAt F (c t')) s' →
        answerAt (j t) s = answerAt (j t') s' := by
  simp [validJ]

def canonicalSlot {n : ℕ} (clause : Clause n) (v : Fin n) : Slot :=
  if nameAt clause .first = v then .first
  else if nameAt clause .second = v then .second else .third

def pi (F : Formula) {u : ℕ} (c : ClauseContext F u) (v : VariableContext F u)
    (j : J u) : I u :=
  fun t => answerAt (j t) (canonicalSlot (clauseAt F (c t)) (v t))

def sampledVariables (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) : VariableContext F u :=
  fun t => nameAt (clauseAt F (c t)) (s t)

def baseAccepts (F : Formula) (v : Fin F.«variables») (c : Fin F.clauses.length)
    (i : Bool) (j : ClauseAnswer) : Bool :=
  decide (localSatisfies (clauseAt F c) j = true ∧
    localConsistent (clauseAt F c) j = true ∧
    answerAt j (canonicalSlot (clauseAt F c) v) = i)

@[simp] theorem baseAccepts_eq_true_iff (F : Formula) (v : Fin F.«variables»)
    (c : Fin F.clauses.length) (i : Bool) (j : ClauseAnswer) :
    baseAccepts F v c i j = true ↔
      localSatisfies (clauseAt F c) j = true ∧
      localConsistent (clauseAt F c) j = true ∧
      answerAt j (canonicalSlot (clauseAt F c) v) = i := by
  simp [baseAccepts]

end DFVSGames.Foundations.Hastad.SourceContexts


namespace DFVSGames.Reduction.SourceEncoding

open DFVSGames.Foundations.Complexity

structure Input where
  «variables» : Nat
  equations : List (CloneGap.Equation (Fin «variables»))
  nonempty : equations ≠ []

def equationWords {n : Nat} (e : CloneGap.Equation (Fin n)) : List Nat :=
  [e.first.val, e.second.val, e.third.val, if e.rhs then 1 else 0]

def inputWords (input : Input) : List Nat :=
  [input.«variables», input.equations.length] ++ input.equations.flatMap equationWords

@[simp] theorem equationWords_length {n : Nat} (e : CloneGap.Equation (Fin n)) :
    (equationWords e).length = 4 := by simp [equationWords]

theorem equationsWords_length {n : Nat} (equations : List (CloneGap.Equation (Fin n))) :
    (equations.flatMap equationWords).length = 4 * equations.length := by
  induction equations with
  | nil => rfl
  | cons e equations ih =>
      simp only [List.flatMap_cons, List.length_append, equationWords_length,
        List.length_cons, ih, Nat.mul_add, Nat.mul_one]
      omega

@[simp] theorem inputWords_length (input : Input) :
    (inputWords input).length = 2 + 4 * input.equations.length := by
  simp only [inputWords, List.length_append, List.length_cons, List.length_nil,
    equationsWords_length]

end DFVSGames.Reduction.SourceEncoding

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_Occurrences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceOccurrences

open DFVSGames.Reduction.CloneGap
open scoped BigOperators

structure Encoding (α : Type) where
  size : ℕ
  code : α ≃ Fin size

namespace Encoding

def fin (n : ℕ) : Encoding (Fin n) := ⟨n, Equiv.refl _⟩
def bool : Encoding Bool := ⟨2, finTwoEquiv.symm⟩
def unit : Encoding Unit := ⟨1, finOneEquiv.symm⟩

def prod {α β : Type} (a : Encoding α) (b : Encoding β) : Encoding (α × β) :=
  ⟨a.size * b.size, (Equiv.prodCongr a.code b.code).trans finProdFinEquiv⟩

def sum {α β : Type} (a : Encoding α) (b : Encoding β) : Encoding (α ⊕ β) :=
  ⟨a.size + b.size, (Equiv.sumCongr a.code b.code).trans finSumFinEquiv⟩

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

end Encoding

abbrev GlobalKey (V C I J : Type) := (V × Cube I) ⊕ ((C × Cube J) ⊕ Unit)

def globalEncoding {V C I J : Type}
    (v : Encoding V) (c : Encoding C) (i : Encoding I) (j : Encoding J) :
    Encoding (GlobalKey V C I J) :=
  (v.prod (i.function Encoding.bool)).sum
    ((c.prod (j.function Encoding.bool)).sum Encoding.unit)

@[simp] theorem globalEncoding_size {V C I J : Type}
    (v : Encoding V) (c : Encoding C) (i : Encoding I) (j : Encoding J) :
    (globalEncoding v c i j).size =
      v.size * 2 ^ i.size + (c.size * 2 ^ j.size + 1) := rfl

def extendRestricted {J : Type} (valid : J → Bool)
    (f : Cube {j : J // valid j = true}) : Cube J :=
  fun j => if h : valid j = true then f ⟨j, h⟩ else false

@[simp] theorem extendRestricted_valid {J : Type} (valid : J → Bool)
    (f : Cube {j : J // valid j = true}) (j : {j : J // valid j = true}) :
    extendRestricted valid f j.val = f j := by simp [extendRestricted, j.property]

@[simp] theorem restrictQuery_extendRestricted {J : Type} (valid : J → Bool)
    (f : Cube {j : J // valid j = true}) :
    restrictQuery valid (extendRestricted valid f) = f := by
  funext j
  exact extendRestricted_valid valid f j

@[simp] theorem canonicalInput_half {I : Type} [Fintype I] [DecidableEq I]
    (i₀ : I) (f : HalfCube i₀) :
    canonicalInput i₀ f.val = f := by
  apply Subtype.ext
  simp [canonicalInput, representative, f.property]

def assignmentOfKey {V C I J : Type}
    (v : Encoding V) (c : Encoding C) (i : Encoding I) (j : Encoding J)
    (bits : GlobalKey V C I J → Bool) : Fin (globalEncoding v c i j).size → Bool :=
  fun q => bits ((globalEncoding v c i j).code.symm q)

@[simp] theorem assignmentOfKey_code {V C I J : Type}
    (v : Encoding V) (c : Encoding C) (i : Encoding I) (j : Encoding J)
    (bits : GlobalKey V C I J → Bool) (key : GlobalKey V C I J) :
    assignmentOfKey v c i j bits ((globalEncoding v c i j).code key) = bits key := by
  exact congrArg bits ((globalEncoding v c i j).code.symm_apply_apply key)

section LocalEquations

variable {V C I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def localAddress (vE : Encoding V) (cE : Encoding C) (iE : Encoding I) (jE : Encoding J)
    (v : V) (c : C) (valid : J → Bool) (i₀ : I) (j₀ : {j : J // valid j = true}) :
    FoldedEquation.Address i₀ j₀ → Fin (globalEncoding vE cE iE jE).size
  | .inl f => (globalEncoding vE cE iE jE).code (.inl (v, f.val))
  | .inr g => (globalEncoding vE cE iE jE).code (.inr (.inl (c, extendRestricted valid g.val)))

def conditionedOccurrence
    (vE : Encoding V) (cE : Encoding C) (iE : Encoding I) (jE : Encoding J)
    (v : V) (c : C) (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true}) (f : Cube I) (g μ : Cube J) :
    Equation (Fin (globalEncoding vE cE iE jE).size) :=
  mapEquation (localAddress vE cE iE jE v c valid i₀ j₀)
    (FoldedEquation.conditionedEquation valid π i₀ j₀ f g μ)

end LocalEquations

def findValid {J : Type} (valid : J → Bool) : List J → Option {j : J // valid j = true}
  | [] => none
  | j :: rest => if h : valid j = true then some ⟨j, h⟩ else findValid valid rest

def firstValid {J : Type} (e : Encoding J) (valid : J → Bool) :
    Option {j : J // valid j = true} := findValid valid e.enumerate

def occurrenceList {Tape Name : Type} (tape : Encoding Tape)
    (emit : Tape → Equation Name) : List (Equation Name) := tape.enumerate.map emit

@[simp] theorem occurrenceList_length {Tape Name : Type} (tape : Encoding Tape)
    (emit : Tape → Equation Name) : (occurrenceList tape emit).length = tape.size := by
  simp [occurrenceList]


open SourceContexts
open DFVSGames.Reduction.FiniteNoise

def clauseAnswerEncoding : Encoding PCP.ClauseAnswer := ⟨8, clauseAnswerFinEquiv⟩

def slotEncoding : Encoding PCP.Slot where
  size := 3
  code :=
    { toFun := fun s => match s with | .first => 0 | .second => 1 | .third => 2
      invFun := fun i => if i.val = 0 then .first else if i.val = 1 then .second else .third
      left_inv := by intro s; cases s <;> rfl
      right_inv := by decide }

def iEncoding (u : ℕ) : Encoding (I u) := (Encoding.fin u).function Encoding.bool
def jEncoding (u : ℕ) : Encoding (J u) := (Encoding.fin u).function clauseAnswerEncoding
def variableEncoding (F : Target.Formula) (u : ℕ) : Encoding (VariableContext F u) :=
  (Encoding.fin u).function (Encoding.fin F.«variables»)
def clauseEncoding (F : Target.Formula) (u : ℕ) : Encoding (ClauseContext F u) :=
  (Encoding.fin u).function (Encoding.fin F.clauses.length)
def slotContextEncoding (u : ℕ) : Encoding (SlotContext u) :=
  (Encoding.fin u).function slotEncoding

def proofEncoding (F : Target.Formula) (u : ℕ) :
    Encoding (GlobalKey (VariableContext F u) (ClauseContext F u) (I u) (J u)) :=
  globalEncoding (variableEncoding F u) (clauseEncoding F u) (iEncoding u) (jEncoding u)

def nBits (F : Target.Formula) (u : ℕ) : ℕ := (proofEncoding F u).size

@[simp] theorem nBits_eq (F : Target.Formula) (u : ℕ) :
    nBits F u = F.«variables» ^ u * 2 ^ (2 ^ u) +
      (F.clauses.length ^ u * 2 ^ (8 ^ u) + 1) := rfl

def dummyIndex (F : Target.Formula) (u : ℕ) : Fin (nBits F u) :=
  (proofEncoding F u).code (.inr (.inr ()))

def leftAnchor (u : ℕ) : I u := fun _ => false

def rightAnchor (F : Target.Formula) {u : ℕ} (c : ClauseContext F u) :
    Option {j : J u // validJ F c j = true} := firstValid (jEncoding u) (validJ F c)

def halfTableKeyAssignment (F : Target.Formula) (u : ℕ)
    (a : VariableContext F u → HalfCube (leftAnchor u) → Bool)
    (b : ∀ c : ClauseContext F u, ∀ j₀ : {j : J u // validJ F c j = true},
      HalfCube j₀ → Bool) :
    GlobalKey (VariableContext F u) (ClauseContext F u) (I u) (J u) → Bool
  | .inl (v, f) => a v (canonicalInput (leftAnchor u) f)
  | .inr (.inl (c, g)) =>
    match rightAnchor F c with
    | none => false
    | some j₀ => b c j₀ (canonicalInput j₀ (restrictQuery (validJ F c) g))
  | .inr (.inr _) => false

def emptyAddress (F : Target.Formula) (u : ℕ) (v : VariableContext F u) :
    EmptyContext.Address (leftAnchor u) → Fin (nBits F u)
  | .inl h => (proofEncoding F u).code (.inl (v, h.val))
  | .inr _ => dummyIndex F u

def contextEquation (F : Target.Formula) (u D : ℕ)
    (c : ClauseContext F u) (v : VariableContext F u)
    (t : SourceTape.TestTape (I u) (J u) D) : Equation (Fin (nBits F u)) :=
  match rightAnchor F c with
  | none => mapEquation (emptyAddress F u v) (EmptyContext.equation (leftAnchor u) t.1)
  | some j₀ => conditionedOccurrence (variableEncoding F u) (clauseEncoding F u)
      (iEncoding u) (jEncoding u) v c (validJ F c) (pi F c v) (leftAnchor u) j₀
      t.1 t.2.2 (realizedNoise t.2.1)

def testTapeEncoding (u D : ℕ) : Encoding (SourceTape.TestTape (I u) (J u) D) :=
  ((iEncoding u).function Encoding.bool).prod
    (((jEncoding u).function (Encoding.fin D)).prod ((jEncoding u).function Encoding.bool))

abbrev SourceIndex (F : Target.Formula) (u D : ℕ) :=
  (ClauseContext F u × SlotContext u) × SourceTape.TestTape (I u) (J u) D

def sourceIndexEncoding (F : Target.Formula) (u D : ℕ) : Encoding (SourceIndex F u D) :=
  ((clauseEncoding F u).prod (slotContextEncoding u)).prod (testTapeEncoding u D)

def sourceEquation (F : Target.Formula) (u D : ℕ) (p : SourceIndex F u D) :
    Equation (Fin (nBits F u)) :=
  contextEquation F u D p.1.1 (sampledVariables F p.1.1 p.1.2) p.2

def rawSourceList (F : Target.Formula) (u D : ℕ) : List (Equation (Fin (nBits F u))) :=
  occurrenceList (sourceIndexEncoding F u D) (sourceEquation F u D)

@[simp] theorem rawSourceList_length (F : Target.Formula) (u D : ℕ) :
    (rawSourceList F u D).length =
      (F.clauses.length ^ u * 3 ^ u) *
        (2 ^ (2 ^ u) * (D ^ (8 ^ u) * 2 ^ (8 ^ u))) := by
  rw [rawSourceList, occurrenceList_length]
  rfl


end DFVSGames.Foundations.Hastad.SourceOccurrences


namespace DFVSGames.Foundations.Hastad.SourceLocalSignature

open Target PCP SourceContexts

abbrev Position (u : ℕ) := Fin u × Slot
abbrev NameProfile (u : ℕ) := Position u → Position u → Bool

@[simp] theorem card_position (u : ℕ) : Fintype.card (Position u) = 3 * u := by
  simp [Position, Nat.mul_comm]

end DFVSGames.Foundations.Hastad.SourceLocalSignature

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

abbrev Alphabet (_ : K) := Bool

abbrev digitTapes (current remaining : K) (base : K → List Bool) (d r : ℕ)
    (currentSuffix remainingSuffix : List Bool) : K → List Bool :=
  MachineUnaryAddAt.unaryTapes current remaining base d r currentSuffix remainingSuffix

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

def tupleOrder (n q : ℕ) : List (Fin q → Fin n) :=
  List.ofFn (finFunctionFinEquiv (m := n) (n := q)).symm

end Order

section Nested

open scoped BigOperators

abbrev Configuration (K Λ σ : Type) :=
  TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool)

end Nested


end DFVSGames.Foundations.Complexity.MachineTupleOdometer


namespace DFVSGames.Foundations.Hastad.SourceOdometerSchedule

open Turing Complexity MachineTupleOdometer
open Reduction.MachineTransfer

abbrev Tape := SourceContextLoad.Tape

variable {u m : ℕ} {Extra Λ σ : Type} [DecidableEq Extra]

def setDigits (m : ℕ) {q : ℕ} (digits : Fin q → ℕ)
    (base : Tape u Extra → List Bool) : Tape u Extra → List Bool
  | .current i => if h : i.val < q then encodeWord (digits ⟨i.val, h⟩)
      else base (.current i)
  | .remaining i => if h : i.val < q then encodeWord (m - 1 - digits ⟨i.val, h⟩)
      else base (.remaining i)
  | k => base k

def setAcc (accumulator : Extra) (base : Tape u Extra → List Bool) (bits : List Bool) :
    Tape u Extra → List Bool := Function.update base (.extra accumulator) bits

def putDigit (i : Fin u) (base : Tape u Extra → List Bool) (d r : ℕ) :
    Tape u Extra → List Bool := digitTapes (.current i) (.remaining i) base d r [] []

omit [DecidableEq Extra] in
@[simp] theorem setDigits_zero (m : ℕ) (digits : Fin 0 → ℕ)
    (base : Tape u Extra → List Bool) : setDigits m digits base = base := by
  funext k
  cases k <;> simp [setDigits]

omit [DecidableEq Extra] in
@[simp] theorem setDigits_extra (m : ℕ) {q : ℕ} (digits : Fin q → ℕ)
    (base : Tape u Extra → List Bool) (a : Extra) :
    setDigits m digits base (.extra a) = base (.extra a) := rfl

@[simp] theorem setAcc_self (a : Extra) (base : Tape u Extra → List Bool) :
    setAcc a base (base (.extra a)) = base := by
  simp [setAcc]

@[simp] theorem setAcc_setAcc (a : Extra) (base : Tape u Extra → List Bool)
    (first second : List Bool) : setAcc a (setAcc a base first) second = setAcc a base second := by
  simp [setAcc]

@[simp] theorem setAcc_apply (a : Extra) (base : Tape u Extra → List Bool) (bits : List Bool) :
    setAcc a base bits (.extra a) = bits := by simp [setAcc]

@[simp] theorem putDigit_extra (i : Fin u) (base : Tape u Extra → List Bool)
    (d r : ℕ) (a : Extra) : putDigit i base d r (.extra a) = base (.extra a) := by
  simp [putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt]

def allBits {q : ℕ} (bits : (Fin q → Fin m) → List Bool) : List Bool :=
  (tupleOrder m q).flatMap bits

def configuration (label : Λ) (canonical : σ) (tapes : Tape u Extra → List Bool) :
    Configuration (Tape u Extra) Λ σ := ⟨some label, (canonical, none), tapes⟩

def initialConfiguration (q : ℕ) (bodyLabel : Λ) (canonical : σ)
    (base : Tape u Extra → List Bool) : Configuration (Tape u Extra) Λ σ :=
  configuration bodyLabel canonical (setDigits m (fun _ : Fin q => 0) base)

def finalConfiguration {q : ℕ} (exitLabel : Λ) (canonical : σ) (accumulator : Extra)
    (base : Tape u Extra → List Bool) (bits : (Fin q → Fin m) → List Bool) :
    Configuration (Tape u Extra) Λ σ :=
  configuration exitLabel canonical (setDigits m (fun _ : Fin q => 0)
    (setAcc accumulator base ((allBits bits).reverse ++ base (.extra accumulator))))

omit [DecidableEq Extra] in
@[simp] theorem initial_current (base : Tape u Extra → List Bool)
    (bodyLabel : Λ) (canonical : σ) (i : Fin u) :
    (initialConfiguration (m := m) u bodyLabel canonical base).stk (.current i) =
      encodeWord 0 := by simp [initialConfiguration, configuration, setDigits]

omit [DecidableEq Extra] in
@[simp] theorem initial_remaining (base : Tape u Extra → List Bool)
    (bodyLabel : Λ) (canonical : σ) (i : Fin u) :
    (initialConfiguration (m := m) u bodyLabel canonical base).stk (.remaining i) =
      encodeWord (m - 1) := by simp [initialConfiguration, configuration, setDigits]

@[simp] theorem final_current (base : Tape u Extra → List Bool)
    (exitLabel : Λ) (canonical : σ) (accumulator : Extra)
    (bits : (Fin u → Fin m) → List Bool) (i : Fin u) :
    (finalConfiguration exitLabel canonical accumulator base bits).stk (.current i) =
      encodeWord 0 := by simp [finalConfiguration, configuration, setDigits]

@[simp] theorem final_remaining (base : Tape u Extra → List Bool)
    (exitLabel : Λ) (canonical : σ) (accumulator : Extra)
    (bits : (Fin u → Fin m) → List Bool) (i : Fin u) :
    (finalConfiguration exitLabel canonical accumulator base bits).stk (.remaining i) =
      encodeWord (m - 1) := by simp [finalConfiguration, configuration, setDigits]

@[simp] theorem final_accumulator (base : Tape u Extra → List Bool)
    (exitLabel : Λ) (canonical : σ) (accumulator : Extra)
    (bits : (Fin u → Fin m) → List Bool) :
    (finalConfiguration exitLabel canonical accumulator base bits).stk (.extra accumulator) =
      ((tupleOrder m u).flatMap bits).reverse ++ base (.extra accumulator) := by
  simp [finalConfiguration, configuration, allBits]

end DFVSGames.Foundations.Hastad.SourceOdometerSchedule

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineProductProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit.MachineProductProgram

open Turing
open DFVSGames.Foundations
open Complexity Hastad
open DFVSGames.Reduction.MachineTransfer

abbrev Extra (t : Nat) := Fin 10 ⊕ Fin (t + 1)
abbrev Tape (t : Nat) := SourceContextLoad.Tape t (Extra t)

def auxiliary (t : Nat) (i : Fin 10) : Tape t := .extra (.inl i)
def constantDigit (t : Nat) (i : Fin (t + 1)) : Tape t := .extra (.inr i)
def accumulator (t : Nat) : Tape t := auxiliary t 6
def output (t : Nat) : Tape t := auxiliary t 9

def powerRole (t : Nat) (edgeCount : Bool) : MachineHorner.Layout (t + 1) → Tape t
  | .inl 0 => auxiliary t (if edgeCount then 8 else 0)
  | .inl 1 => auxiliary t 1
  | .inl 2 => auxiliary t 2
  | .inl 3 => auxiliary t 5
  | .inl 4 => auxiliary t 3
  | .inl 5 => auxiliary t 4
  | .inr i => constantDigit t i

theorem powerRole_injective (t : Nat) (edgeCount : Bool) : Function.Injective (powerRole t edgeCount) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => fin_cases a <;> fin_cases b <;> cases edgeCount <;> simp_all [powerRole, auxiliary]
    | inr b => fin_cases a <;> cases edgeCount <;> simp [powerRole, auxiliary, constantDigit] at h
  | inr a =>
    cases b with
    | inl b => fin_cases b <;> cases edgeCount <;> simp [powerRole, auxiliary, constantDigit] at h
    | inr b => simpa [powerRole, constantDigit] using h

def powerSlots (t : Nat) (edgeCount : Bool) : MachineHorner.Layout (t + 1) ↪ Tape t :=
  ⟨powerRole t edgeCount, powerRole_injective t edgeCount⟩

noncomputable def clearKeys (t : Nat) : List (Tape t) :=
  Finset.univ.toList.filter (fun k => decide (k ≠ accumulator t ∧ k ≠ output t))

@[simp] theorem mem_clearKeys (t : Nat) (k : Tape t) :
    k ∈ clearKeys t ↔ k ≠ accumulator t ∧ k ≠ output t := by
  simp [clearKeys]

end DFVSGames.Explicit.MachineProductProgram


namespace DFVSGames.Explicit.MachineProductHeaders

open Turing
open DFVSGames.Foundations Target Complexity Hastad
open MachineProductProgram

def frame {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool) : Tape t → List Bool
  | .formula => encodeWords (ProductMachineSemantics.inputTable H)
  | .extra (.inl i) =>
      if i = 0 then encodeWord H.vertices
      else if i = 7 then encodeWord q
      else if i = 8 then encodeWord H.constraints.length
      else if i = 6 then emitted.reverse else []
  | .extra (.inr i) => encodeWord (MachineProductPower.digits i.val)
  | _ => []

@[simp] theorem frame_accumulator {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool) :
    frame H t emitted (accumulator t) = emitted.reverse := by simp [frame, accumulator, auxiliary]

@[simp] theorem frame_output {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool) :
    frame H t emitted (output t) = [] := by simp [frame, output, auxiliary]

@[simp] theorem frame_radix {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool)
    (edgeCount : Bool) :
    frame H t emitted (powerSlots t edgeCount (.inl 0)) =
      encodeWord (if edgeCount then H.constraints.length else H.vertices) := by
  cases edgeCount <;> simp [frame, powerSlots, powerRole, auxiliary]

@[simp] theorem frame_digit {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool)
    (edgeCount : Bool) (i : Fin (t + 1)) :
    frame H t emitted (powerSlots t edgeCount (.inr i)) =
      encodeWord (MachineProductPower.digits i.val) := rfl

@[simp] theorem frame_power_output {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool)
    (edgeCount : Bool) : frame H t emitted (powerSlots t edgeCount (.inl 3)) = [] := by
  simp [frame, powerSlots, powerRole, auxiliary]

end DFVSGames.Explicit.MachineProductHeaders


namespace DFVSGames.Explicit.MachineProductLoop

open Turing
open DFVSGames.Foundations
open Complexity Hastad
open MachineComposition
open MachineProductProgram

variable {q t : Nat}

noncomputable section

def tupleTapes (H : Target.Instance q) (base : Tape t → List Bool)
    (edges : Fin t → Fin H.constraints.length) (out : List Bool) : Tape t → List Bool :=
  SourceOdometerSchedule.setDigits H.constraints.length (fun i => (edges i).val)
    (SourceOdometerSchedule.setAcc (Sum.inl (6 : Fin 10)) base out)

@[simp] theorem tupleTapes_current (H : Target.Instance q) (base : Tape t → List Bool)
    (edges : Fin t → Fin H.constraints.length) (out : List Bool) (i : Fin t) :
    tupleTapes H base edges out (.current i) = encodeWord (edges i).val := by
  simp [tupleTapes, SourceOdometerSchedule.setDigits, i.isLt]

@[simp] theorem tupleTapes_accumulator (H : Target.Instance q) (base : Tape t → List Bool)
    (edges : Fin t → Fin H.constraints.length) (out : List Bool) :
    tupleTapes H base edges out (accumulator t) = out := by
  simp [tupleTapes, accumulator, auxiliary, SourceOdometerSchedule.setDigits, SourceOdometerSchedule.setAcc]

end

end DFVSGames.Explicit.MachineProductLoop

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ChainRule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Games

open scoped BigOperators

noncomputable section

namespace FiniteDistribution

variable {Ω : Type*} [Fintype Ω]

def condition (μ : FiniteDistribution Ω) (given : Ω → Bool)
    (positive : 0 < μ.probability given) : FiniteDistribution Ω where
  weight x := if given x then μ.weight x / μ.probability given else 0
  nonnegative x := by
    split
    · exact div_nonneg (μ.nonnegative x) positive.le
    · exact le_rfl
  normalized := by
    calc
      _ = (∑ x, if given x then μ.weight x else 0) / μ.probability given := by
        simp only [div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : given x = true <;> simp [hx]
      _ = 1 := div_self (ne_of_gt positive)

theorem probability_condition (μ : FiniteDistribution Ω) (given event : Ω → Bool)
    (positive : 0 < μ.probability given) :
    (μ.condition given positive).probability event =
      μ.probability (fun x => given x && event x) / μ.probability given := by
  simp only [probability, condition, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hg : given x = true <;> by_cases he : event x = true <;> simp [hg, he]

@[simp] theorem probability_condition_given (μ : FiniteDistribution Ω)
    (given : Ω → Bool) (positive : 0 < μ.probability given) :
    (μ.condition given positive).probability given = 1 := by
  rw [μ.probability_condition]
  simpa only [Bool.and_self] using div_self (ne_of_gt positive)

end FiniteDistribution

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  {n : Nat}

def selectedSuccess (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) : ℝ :=
  (G.repetition n).questions.probability (G.selectedWins strategy selected)

@[simp] theorem selectedSuccess_empty (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    G.selectedSuccess strategy ∅ = 1 := by
  have h : G.selectedWins strategy ∅ = fun _ => true :=
    funext (G.selectedWins_empty strategy)
  rw [selectedSuccess, h, FiniteDistribution.probability_true]

end Game

end

end DFVSGames.Foundations.Games


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Collision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Repetition
open DFVSGames.Foundations.Games
open scoped BigOperators
noncomputable section

structure ProjectionKernel (Q₁ Q₂ A₁ A₂ : Type*)
    [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] where
  outer : FiniteDistribution Q₂
  inner : Q₂ → FiniteDistribution Q₁
  accepts : Q₁ → Q₂ → A₁ → A₂ → Bool
  projection : ∀ x y a b b', accepts x y a b = true →
    accepts x y a b' = true → b = b'

namespace ProjectionKernel
variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

def toGame (K : ProjectionKernel Q₁ Q₂ A₁ A₂) : Game Q₁ Q₂ A₁ A₂ where
  questions :=
    { weight := fun q => K.outer.weight q.2 * (K.inner q.2).weight q.1
      nonnegative := fun q => mul_nonneg (K.outer.nonnegative _) ((K.inner _).nonnegative _)
      normalized := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        simp_rw [← Finset.mul_sum, FiniteDistribution.normalized, mul_one]
        exact K.outer.normalized }
  accepts := K.accepts

def apply (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Q₁ → A₁ → ℝ) (y : Q₂) (b : A₂) : ℝ :=
  ∑ x, (K.inner y).weight x * ∑ a, if K.accepts x y a b then f x a else 0

def assignment (labels : Q₁ → A₁) (x : Q₁) (a : A₁) : ℝ := by
  classical
  exact if labels x = a then 1 else 0

@[simp] theorem apply_assignment (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (labels : Q₁ → A₁) (y : Q₂) (b : A₂) :
    K.apply (assignment labels) y b =
      ∑ x, if K.accepts x y (labels x) b then (K.inner y).weight x else 0 := by
  classical
  unfold apply assignment
  apply Finset.sum_congr rfl
  intro x _
  have hsum : (∑ a, if K.accepts x y a b then
      (if labels x = a then (1 : ℝ) else 0) else 0) =
      if K.accepts x y (labels x) b then (1 : ℝ) else 0 := by
    have hpoint (a : A₁) :
        (if K.accepts x y a b then (if labels x = a then (1 : ℝ) else 0) else 0) =
        (if a = labels x then (if K.accepts x y a b then (1 : ℝ) else 0) else 0) := by
      by_cases h : a = labels x
      · subst a
        simp
      · simp [h, Ne.symm h]
    simp_rw [hpoint]
    simp
  rw [hsum]
  by_cases h : K.accepts x y (labels x) b = true <;> simp [h]

end ProjectionKernel
end
end DFVSGames.Repetition


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_TensorDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Repetition.ProjectionKernel

open DFVSGames.Foundations.Games
open scoped BigOperators

noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

def repetition (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (n : Nat) :
    ProjectionKernel (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂) := by
  classical
  exact
    { outer := K.outer.iid n
      inner := fun y => FiniteDistribution.table (fun i : Fin n => K.inner (y i))
      accepts := fun x y a b => decide (∀ i, K.accepts (x i) (y i) (a i) (b i) = true)
      projection := by
        intro x y a b b' hb hb'
        simp only [decide_eq_true_eq] at hb hb'
        funext i
        exact K.projection _ _ _ _ _ (hb i) (hb' i) }

@[simp] theorem repetition_accepts_iff (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (n : Nat)
    (x : Fin n → Q₁) (y : Fin n → Q₂) (a : Fin n → A₁) (b : Fin n → A₂) :
    (K.repetition n).accepts x y a b = true ↔
      ∀ i, K.accepts (x i) (y i) (a i) (b i) = true := by
  classical
  simp [repetition]

@[simp] theorem toGame_repetition (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (n : Nat) :
    (K.repetition n).toGame = K.toGame.repetition n := by
  classical
  have hq : (K.repetition n).toGame.questions = (K.toGame.repetition n).questions := by
    apply FiniteDistribution.eq_of_weight_eq
    intro q
    change ((∏ i, K.outer.weight (q.2 i)) *
        (∏ i, (K.inner (q.2 i)).weight (q.1 i))) =
      ∏ i, K.outer.weight (q.2 i) * (K.inner (q.2 i)).weight (q.1 i)
    exact Finset.prod_mul_distrib.symm
  change Game.mk (K.repetition n).toGame.questions
      (fun (x : Fin n → Q₁) (y : Fin n → Q₂) (a : Fin n → A₁) (b : Fin n → A₂) =>
        decide (∀ i, K.accepts (x i) (y i) (a i) (b i) = true)) =
    Game.mk (K.toGame.repetition n).questions
      (fun (x : Fin n → Q₁) (y : Fin n → Q₂) (a : Fin n → A₁) (b : Fin n → A₂) =>
        decide (∀ i, K.accepts (x i) (y i) (a i) (b i) = true))
  rw [hq]

end
end DFVSGames.Repetition.ProjectionKernel


namespace DFVSGames.Foundations.Repetition

open scoped BigOperators

noncomputable section

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

end

end DFVSGames.Foundations.Repetition


namespace DFVSGames.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y]

def normalizeOr (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (fallback : FiniteDistribution X) : FiniteDistribution X :=
  if h : 0 < ∑ x, w x then
    { weight := normalizedWeight w
      nonnegative := (normalizedWeight_isProbability w hw h).1
      normalized := (normalizedWeight_isProbability w hw h).2 }
  else fallback

theorem sum_mul_normalizeOr (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (fallback : FiniteDistribution X) (x : X) :
    (∑ z, w z) * (normalizeOr w hw fallback).weight x = w x := by
  classical
  have hs : 0 ≤ ∑ z, w z := Finset.sum_nonneg (fun z _ => hw z)
  by_cases h : 0 < ∑ z, w z
  · simp only [normalizeOr, dite_eq_left h, normalizedWeight]
    field_simp
  · have hz : ∑ z, w z = 0 := le_antisymm (le_of_not_gt h) hs
    have hx : w x = 0 := by
      apply le_antisymm _ (hw x)
      have hl := Finset.single_le_sum (fun z _ => hw z) (Finset.mem_univ x)
      simpa only [hz] using hl
    simp [normalizeOr, hz, hx]

end
end DFVSGames.Foundations.Repetition


namespace DFVSGames.Repetition

open DFVSGames.Foundations.Games
open scoped BigOperators

noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

def leftQuestionMarginal (G : Game Q₁ Q₂ A₁ A₂) : FiniteDistribution Q₁ where
  weight x := ∑ y, G.questions.weight (x, y)
  nonnegative x := Finset.sum_nonneg fun y _ => G.questions.nonnegative (x, y)
  normalized := by
    rw [← Fintype.sum_prod_type]
    exact G.questions.normalized

def rightQuestionMarginal (G : Game Q₁ Q₂ A₁ A₂) : FiniteDistribution Q₂ where
  weight y := ∑ x, G.questions.weight (x, y)
  nonnegative y := Finset.sum_nonneg fun x _ => G.questions.nonnegative (x, y)
  normalized := by
    rw [Finset.sum_comm, ← Fintype.sum_prod_type]
    exact G.questions.normalized

def leftGivenRight (G : Game Q₁ Q₂ A₁ A₂) (y : Q₂) : FiniteDistribution Q₁ :=
  DFVSGames.Foundations.Repetition.normalizeOr
    (fun x => G.questions.weight (x, y))
    (fun x => G.questions.nonnegative (x, y)) (leftQuestionMarginal G)

theorem rightQuestionMarginal_mul_leftGivenRight
    (G : Game Q₁ Q₂ A₁ A₂) (x : Q₁) (y : Q₂) :
    (rightQuestionMarginal G).weight y * (leftGivenRight G y).weight x =
      G.questions.weight (x, y) :=
  DFVSGames.Foundations.Repetition.sum_mul_normalizeOr
    (fun x => G.questions.weight (x, y))
    (fun x => G.questions.nonnegative (x, y)) (leftQuestionMarginal G) x

def kernelOfGame (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G) :
    ProjectionKernel Q₁ Q₂ A₁ A₂ where
  outer := rightQuestionMarginal G
  inner := leftGivenRight G
  accepts := G.accepts
  projection := hG

@[simp] theorem kernelOfGame_question_weight
    (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G) (q : Q₁ × Q₂) :
    (kernelOfGame G hG).toGame.questions.weight q = G.questions.weight q :=
  rightQuestionMarginal_mul_leftGivenRight G q.1 q.2

@[simp] theorem toGame_kernelOfGame
    (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G) :
    (kernelOfGame G hG).toGame = G := by
  have hq : (kernelOfGame G hG).toGame.questions = G.questions :=
    FiniteDistribution.eq_of_weight_eq (kernelOfGame_question_weight G hG)
  calc
    _ = { questions := G.questions, accepts := G.accepts } := by
      change Game.mk (kernelOfGame G hG).toGame.questions G.accepts =
        Game.mk G.questions G.accepts
      rw [hq]
    _ = G := by cases G; rfl

@[simp] theorem kernelOfGame_success
    (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) :
    (kernelOfGame G hG).toGame.success strategy = G.success strategy := by
  rw [toGame_kernelOfGame]

@[simp] theorem kernelOfGame_value [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G) :
    (kernelOfGame G hG).toGame.value = G.value := by
  rw [toGame_kernelOfGame]

end
end DFVSGames.Repetition


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_FinishReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Soundness.PartnerProjection

inductive Slot where
  | first | second | third
  deriving DecidableEq, Repr

structure Triple where
  first : Bool
  second : Bool
  third : Bool
  deriving DecidableEq, Repr

def zeroTriple : Triple := ⟨false, false, false⟩

def parity (x : Triple) : Bool := (x.first.xor x.second).xor x.third

def retained (s : Slot) (x : Triple) : Bool :=
  match s with
  | .first => x.first
  | .second => x.second
  | .third => x.third

def freeBit (s : Slot) (x : Triple) : Bool :=
  match s with
  | .first => x.second
  | .second => x.first
  | .third => x.first

def complete (s : Slot) (p r f : Bool) : Triple :=
  match s with
  | .first => ⟨r, f, (p.xor r).xor f⟩
  | .second => ⟨f, r, (p.xor r).xor f⟩
  | .third => ⟨f, (p.xor r).xor f, r⟩

theorem parity_complete (s : Slot) (p r f : Bool) :
    parity (complete s p r f) = p := by
  cases s <;> cases p <;> cases r <;> cases f <;> decide

theorem complete_coordinates (s : Slot) (x : Triple) :
    complete s (parity x) (retained s x) (freeBit s x) = x := by
  rcases x with ⟨a, b, c⟩
  cases s <;> cases a <;> cases b <;> cases c <;> decide

variable {Position : Type} (rhs active : Position → Bool) (slot : Position → Slot)

structure PartnerPoint where
  homogeneous : Bool
  full : Position → Triple
  single : Position → Bool
  full_zero : ∀ j, active j = true → full j = zeroTriple
  full_valid : ∀ j, active j = false → parity (full j) = (rhs j && homogeneous)
  single_zero : ∀ j, active j = false → single j = false

theorem partner_ext {x y : PartnerPoint rhs active}
    (hh : x.homogeneous = y.homogeneous) (hf : x.full = y.full)
    (hs : x.single = y.single) : x = y := by
  cases x
  cases y
  cases hh
  cases hf
  cases hs
  rfl

end DFVSGames.Soundness.PartnerProjection

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KernelCardinality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Soundness.PartnerLinear

open PartnerProjection
open DFVSGames.Integration.BinaryLinear (F2 ofBit toBit scalar_cases ofBit_toBit
  toBit_ofBit )

variable {P : Type} (rhs active : P → Bool) (slot : P → Slot)

abbrev Active := {j : P // active j = true}
abbrev Inactive := {j : P // active j = false}
abbrev PartnerCoordinates := F2 × ((Inactive active → F2 × F2) × (Active active → F2))

def partnerCoordinates (y : PartnerPoint rhs active) : PartnerCoordinates active :=
  (ofBit y.homogeneous,
    (fun j => (ofBit (y.full j.val).first, ofBit (y.full j.val).second),
      fun j => ofBit (y.single j.val)))

def partnerFromCoordinates (v : PartnerCoordinates active) : PartnerPoint rhs active where
  homogeneous := toBit v.1
  full := fun j => if hj : active j = false then
    complete .first (rhs j && toBit v.1)
      (toBit (v.2.1 ⟨j, hj⟩).1) (toBit (v.2.1 ⟨j, hj⟩).2)
    else zeroTriple
  single := fun j => if hj : active j = true then toBit (v.2.2 ⟨j, hj⟩) else false
  full_zero := by intro j hj; simp [hj]
  full_valid := by intro j hj; simp only [dite_eq_left hj]; exact parity_complete _ _ _ _
  single_zero := by intro j hj; simp [hj]

def partnerEquiv : PartnerPoint rhs active ≃ PartnerCoordinates active where
  toFun := partnerCoordinates rhs active
  invFun := partnerFromCoordinates rhs active
  left_inv y := by
    apply partner_ext rhs active
    · exact toBit_ofBit _
    · funext j
      cases hj : active j with
      | false =>
        change (if hj' : active j = false then
          complete .first (rhs j && toBit (ofBit y.homogeneous))
            (toBit (ofBit (y.full j).first)) (toBit (ofBit (y.full j).second))
          else zeroTriple) = y.full j
        simp only [dite_eq_left hj, toBit_ofBit, ← y.full_valid j hj]
        exact complete_coordinates .first (y.full j)
      | true => simpa [partnerFromCoordinates, hj] using (y.full_zero j hj).symm
    · funext j
      cases hj : active j with
      | false => simpa [partnerFromCoordinates, hj] using (y.single_zero j hj).symm
      | true => simp [partnerFromCoordinates, partnerCoordinates, hj, toBit_ofBit]
  right_inv v := by
    apply Prod.ext
    · exact ofBit_toBit _
    · apply Prod.ext
      · funext j
        simp [partnerCoordinates, partnerFromCoordinates, j.property, complete, ofBit_toBit]
      · funext j
        simp [partnerCoordinates, partnerFromCoordinates, j.property, ofBit_toBit]

noncomputable instance partnerAddCommGroup : AddCommGroup (PartnerPoint rhs active) :=
  (partnerEquiv rhs active).addCommGroup

noncomputable instance partnerModule : Module F2 (PartnerPoint rhs active) :=
  (partnerEquiv rhs active).addEquiv.module F2

noncomputable def partnerLinearEquiv : PartnerPoint rhs active ≃ₗ[F2] PartnerCoordinates active :=
  (partnerEquiv rhs active).addEquiv.linearEquiv F2

end DFVSGames.Soundness.PartnerLinear


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ConditionalIncidences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped BigOperators

namespace DFVSGames.Soundness.ConditionalIncidences

noncomputable section

abbrev PositionInside {P : Type} (K : Finset P) := {j : P // j ∈ K}
abbrev PositionOutside {P : Type} (K : Finset P) := {j : P // j ∉ K}

abbrev RawSlot {P : Type} (J : Finset P) :=
  Option ((PositionOutside J × Fin 2) ⊕ PositionInside J)

end

end DFVSGames.Soundness.ConditionalIncidences
end

section

open scoped BigOperators

namespace DFVSGames.Soundness.PartnerMapCoordinates

open PartnerProjection
open ConditionalIncidences (PositionInside PositionOutside RawSlot )
open DFVSGames.Integration.BinaryLinear (F2 ofBit toBit)

noncomputable section

variable {P : Type} [DecidableEq P] (rhs : P → Bool) (J : Finset P)

def activeOf (J : Finset P) (j : P) : Bool := decide (j ∈ J)

def inactiveOfOutside (j : PositionOutside J) : PartnerLinear.Inactive (activeOf J) :=
  ⟨j.val, by simp [activeOf, j.property]⟩

def activeOfInside (j : PositionInside J) : PartnerLinear.Active (activeOf J) :=
  ⟨j.val, by simp [activeOf, j.property]⟩

def outsideOfInactive (j : PartnerLinear.Inactive (activeOf J)) : PositionOutside J :=
  ⟨j.val, by simpa [activeOf] using j.property⟩

def insideOfActive (j : PartnerLinear.Active (activeOf J)) : PositionInside J :=
  ⟨j.val, by simpa [activeOf] using j.property⟩

def tupleToRaw (v : PartnerLinear.PartnerCoordinates (activeOf J)) : RawSlot J → F2
  | none => v.1
  | some (.inl (j, i)) =>
      if i = 0 then (v.2.1 (inactiveOfOutside J j)).1
      else (v.2.1 (inactiveOfOutside J j)).2
  | some (.inr j) => v.2.2 (activeOfInside J j)

def tupleFromRaw (f : RawSlot J → F2) : PartnerLinear.PartnerCoordinates (activeOf J) :=
  (f none,
    (fun j => (f (some (.inl (outsideOfInactive J j, 0))),
      f (some (.inl (outsideOfInactive J j, 1)))),
      fun j => f (some (.inr (insideOfActive J j)))))

def tupleRawEquiv : PartnerLinear.PartnerCoordinates (activeOf J) ≃ₗ[F2] (RawSlot J → F2) where
  toFun := tupleToRaw J
  invFun := tupleFromRaw J
  left_inv v := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext j
        apply Prod.ext <;> rfl
      · funext j
        rfl
  right_inv f := by
    funext s
    rcases s with _ | (⟨j, i⟩ | j)
    · rfl
    · fin_cases i <;> rfl
    · rfl
  map_add' x y := by
    funext s
    rcases s with _ | (⟨j, i⟩ | j)
    · rfl
    · fin_cases i <;> rfl
    · rfl
  map_smul' c x := by
    funext s
    rcases s with _ | (⟨j, i⟩ | j)
    · rfl
    · fin_cases i <;> rfl
    · rfl

def pointEquiv : PartnerPoint rhs (activeOf J) ≃ₗ[F2] (RawSlot J → F2) :=
  (PartnerLinear.partnerLinearEquiv rhs (activeOf J)).trans (tupleRawEquiv J)

@[simp] theorem pointEquiv_none (y : PartnerPoint rhs (activeOf J)) :
    pointEquiv rhs J y none = ofBit y.homogeneous := rfl

@[simp] theorem pointEquiv_full_first (y : PartnerPoint rhs (activeOf J))
    (j : PositionOutside J) :
    pointEquiv rhs J y (some (.inl (j, 0))) = ofBit (y.full j.val).first := rfl

@[simp] theorem pointEquiv_full_second (y : PartnerPoint rhs (activeOf J))
    (j : PositionOutside J) :
    pointEquiv rhs J y (some (.inl (j, 1))) = ofBit (y.full j.val).second := rfl

@[simp] theorem pointEquiv_single (y : PartnerPoint rhs (activeOf J))
    (j : PositionInside J) :
    pointEquiv rhs J y (some (.inr j)) = ofBit (y.single j.val) := rfl

end

end DFVSGames.Soundness.PartnerMapCoordinates
end

namespace DFVSGames.Soundness.IncidenceExtraction

abbrev Triple := Fin 3 → Bool

def xorTriple (x : Triple) : Bool := (x 0 ^^ x 1) ^^ x 2

structure Incidence (Occurrence Name : Type) where
  name : Occurrence → Fin 3 → Name
  rhs : Occurrence → Bool

def Incidence.accepts {Occurrence Name : Type}
    (g : Incidence Occurrence Name) (o : Occurrence) (i : Fin 3)
    (a : Triple) (b : Bool) : Prop :=
  xorTriple a = g.rhs o ∧ a i = b

def Incidence.namedAccepts {Occurrence Name : Type}
    (g : Incidence Occurrence Name) (o : Occurrence) (n : Name)
    (a : Triple) (b : Bool) : Prop :=
  ∃ i, g.name o i = n ∧ g.accepts o i a b

end DFVSGames.Soundness.IncidenceExtraction

namespace DFVSGames.Reduction.ActualHomogeneous

open Integration.BinaryLinear
open scoped BigOperators

abbrev E (k : Nat) := F2 × (Fin k → F2 × F2)

variable {k : Nat}

def tau : E k →ₗ[F2] F2 := LinearMap.fst F2 _ _
def hBasis (k : Nat) : E k := (1, 0)
def firstBasis (j : Fin k) : E k := (0, Pi.single j (1, 0))
def secondBasis (j : Fin k) : E k := (0, Pi.single j (0, 1))

@[simp] theorem tau_hBasis : tau (hBasis k) = 1 := rfl
@[simp] theorem tau_firstBasis (j : Fin k) : tau (firstBasis j) = 0 := rfl
@[simp] theorem tau_secondBasis (j : Fin k) : tau (secondBasis j) = 0 := rfl

theorem pair_fst_ite (p : Prop) [Decidable p] (a b : F2 × F2) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split_ifs <;> rfl
theorem pair_snd_ite (p : Prop) [Decidable p] (a b : F2 × F2) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split_ifs <;> rfl

theorem coordinate_decomposition (x : E k) :
    x = x.1 • hBasis k + ∑ j : Fin k,
      ((x.2 j).1 • firstBasis j + (x.2 j).2 • secondBasis j) := by
  apply Prod.ext
  · simp [hBasis, firstBasis, secondBasis, Prod.fst_sum]
  · funext j
    apply Prod.ext <;>
      simp [hBasis, firstBasis, secondBasis, Pi.single_apply,
        Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, pair_fst_ite, pair_snd_ite]

theorem linearMap_expansion {R : Type*} [AddCommGroup R] [Module F2 R]
    (X : E k →ₗ[F2] R) (x : E k) :
    X x = x.1 • X (hBasis k) + ∑ j : Fin k,
      ((x.2 j).1 • X (firstBasis j) + (x.2 j).2 • X (secondBasis j)) := by
  conv_lhs => rw [coordinate_decomposition x]
  simp

end DFVSGames.Reduction.ActualHomogeneous

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ActualCanonical
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

inductive Record (Name : Type u) (Id : Type v) (R : Type w)
  | blank
  | single (name : Name) (coefficient : R)
  | full (occurrence : Id) (coefficients : Fin 3 → R)
  deriving DecidableEq

abbrev Data (k : Nat) (Name : Type u) (Id : Type v) (R : Type w) :=
  R × (Fin k → Record Name Id R)

def pivot (a : Fin 3 → R) : R :=
  if a 0 = a 1 then a 0 else if a 0 = a 2 then a 0 else a 2

def translate (a : Fin 3 → R) (t : R) : Fin 3 → R := fun i => a i + t
def normalize (a : Fin 3 → R) : Fin 3 → R := translate a (pivot a)

def record (names : Id → Fin 3 → Name) (e : Id) (a : Fin 3 → R) :
    Record Name Id R :=
  if a 0 = a 1 then
      if a 0 = a 2 then .blank else .single (names e 2) (a 2 + a 0)
    else if a 0 = a 2 then .single (names e 1) (a 1 + a 0)
    else if a 1 = a 2 then .single (names e 0) (a 0 + a 2)
    else .full e (normalize a)

def data (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (z : R) (a : Fin k → Fin 3 → R) : Data k Name Id R :=
  (z + ∑ j, rhs (occ j) • pivot (a j), fun j => record names (occ j) (a j))

def standardTriple (X : E k →ₗ[F2] R) (j : Fin k) : Fin 3 → R :=
  ![X (firstBasis j), X (secondBasis j), 0]

def canonical (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (X : E k →ₗ[F2] R) : Data k Name Id R :=
  data occ names rhs (X (hBasis k)) (standardTriple X)

def ambientEval (b : Fin k → F2) (z : R) (a : Fin k → Fin 3 → R) (x : E k) : R :=
  x.1 • z + ∑ j, ((x.2 j).1 • a j 0 + (x.2 j).2 • a j 1 +
    (b j * x.1 + (x.2 j).1 + (x.2 j).2) • a j 2)

theorem data_global_shift (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (z c : R) (a : Fin k → Fin 3 → R) :
    data occ names rhs (z + c) a =
      ((data occ names rhs z a).1 + c, (data occ names rhs z a).2) := by
  apply Prod.ext
  · dsimp [data]; abel
  · rfl

theorem canonical_shift (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (X : E k →ₗ[F2] R) (c : R) :
    canonical occ names rhs (X + tau.smulRight c) =
      ((canonical occ names rhs X).1 + c, (canonical occ names rhs X).2) := by
  have ht : standardTriple (X + tau.smulRight c) = standardTriple X := by
    funext j i
    fin_cases i <;> simp [standardTriple, tau, firstBasis, secondBasis]
  simp only [canonical, ht]
  have hg : (X + tau.smulRight c : E k →ₗ[F2] R) (hBasis k) = X (hBasis k) + c := by
    simp [hBasis, tau]
  rw [hg]
  exact data_global_shift occ names rhs _ c _

omit [DecidableEq R] in
@[simp] theorem ambientEval_hBasis (b : Fin k → F2) (z : R) (a : Fin k → Fin 3 → R) :
    ambientEval b z a (hBasis k) = z + ∑ j, b j • a j 2 := by
  simp [ambientEval, hBasis]

omit [DecidableEq R] in
@[simp] theorem ambientEval_firstBasis (b : Fin k → F2) (z : R)
    (a : Fin k → Fin 3 → R) (j : Fin k) :
    ambientEval b z a (firstBasis j) = a j 0 + a j 2 := by
  classical
  simp only [ambientEval, firstBasis, zero_smul, zero_add, mul_zero]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    simp [hij]
  · simp

omit [DecidableEq R] in
@[simp] theorem ambientEval_secondBasis (b : Fin k → F2) (z : R)
    (a : Fin k → Fin 3 → R) (j : Fin k) :
    ambientEval b z a (secondBasis j) = a j 1 + a j 2 := by
  classical
  simp only [ambientEval, secondBasis, zero_smul, zero_add, mul_zero]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    simp [hij]
  · simp

end DFVSGames.Reduction.ActualCanonical

namespace DFVSGames.Soundness.RawPartnerTarget
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open PartnerProjection PartnerMapCoordinates ConditionalIncidences

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev RawPoint {k : Nat} (J : Finset (Fin k)) := RawSlot J → F2

end
end DFVSGames.Soundness.RawPartnerTarget

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Explicit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Reduction.Explicit

variable {α β : Type*}

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

def words (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | k + 1 => (pairs alphabet (words alphabet k)).map fun p => p.1 :: p.2

def edgeCount (m k dimR noiseCount : Nat) : Nat :=
  m^k * 2^((2*k + 1)*(dimR + 1)) * noiseCount

end DFVSGames.Reduction.Explicit


namespace DFVSGames.Reduction.ActualEnumeration

open Integration.BinaryLinear
open ActualHomogeneous
open _root_.OAI.DFVSGames.Reduction.Explicit
open scoped BigOperators

variable {α β N : Type*} {n m k s d noiseCount : Nat}

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

section Coefficients

variable (k : Nat) (R : Type*) [AddCommGroup R] [Module F2 R]

abbrev Coefficients := R × (Fin k → R × R)

def fromCoefficients (a : Coefficients k R) : E k →ₗ[F2] R where
  toFun x := x.1 • a.1 + ∑ j : Fin k,
    ((x.2 j).1 • (a.2 j).1 + (x.2 j).2 • (a.2 j).2)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul]
    simp only [add_add_add_comm, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
      mul_smul, smul_add, Finset.smul_sum, RingHom.id_apply]

def toCoefficients (X : E k →ₗ[F2] R) : Coefficients k R :=
  (X (hBasis k), fun j => (X (firstBasis j), X (secondBasis j)))

theorem to_fromCoefficients (a : Coefficients k R) :
    toCoefficients k R (fromCoefficients k R a) = a := by
  apply Prod.ext
  · simp [toCoefficients, fromCoefficients, hBasis]
  · funext j
    apply Prod.ext <;>
      simp [toCoefficients, fromCoefficients, firstBasis, secondBasis, Pi.single_apply,
        apply_ite]

theorem from_toCoefficients (X : E k →ₗ[F2] R) :
    fromCoefficients k R (toCoefficients k R X) = X := by
  apply LinearMap.ext
  intro x
  exact (linearMap_expansion X x).symm

def coefficientEquiv : Coefficients k R ≃ (E k →ₗ[F2] R) where
  toFun := fromCoefficients k R
  invFun := toCoefficients k R
  left_inv := to_fromCoefficients k R
  right_inv := from_toCoefficients k R

def allLinearMaps (values : List R) : List (E k →ₗ[F2] R) :=
  (pairs values (functions (pairs values values) k)).map (coefficientEquiv k R)

theorem length_allLinearMaps (values : List R) :
    (allLinearMaps k R values).length = values.length^(2*k+1) := by
  simp only [allLinearMaps, List.length_map, length_pairs, length_functions]
  rw [show values.length * values.length = values.length^2 by simp [pow_two],
    ← pow_mul, pow_succ]
  exact Nat.mul_comm _ _

theorem mem_allLinearMaps {values : List R} (full : ∀ a, a ∈ values)
    (X : E k →ₗ[F2] R) : X ∈ allLinearMaps k R values := by
  apply List.mem_map.mpr
  refine ⟨toCoefficients k R X, ?_, from_toCoefficients k R X⟩
  apply mem_pairs.mpr
  exact ⟨full _, mem_functions (fun a => mem_pairs.mpr ⟨full _, full _⟩) _⟩

end Coefficients

def vectors (s : Nat) : List (Integration.BinaryLinear.Vector s) :=
  (List.finRange (2^s)).map (Encoding.alphabetEquiv s).symm

theorem length_vectors (s : Nat) : (vectors s).length = 2^s := by
  simp [vectors]

theorem mem_vectors (v : Integration.BinaryLinear.Vector s) : v ∈ vectors s := by
  exact List.mem_map.mpr ⟨Encoding.alphabetEquiv s v, List.mem_finRange _,
    (Encoding.alphabetEquiv s).symm_apply_apply v⟩

abbrev Ambient (s d : Nat) :=
  Integration.BinaryLinear.Vector s × Integration.BinaryLinear.Vector d

def ambientVectors (s d : Nat) : List (Ambient s d) := pairs (vectors s) (vectors d)

theorem length_ambientVectors (s d : Nat) : (ambientVectors s d).length = 2^(s+d) := by
  simp [ambientVectors, length_pairs, length_vectors, pow_add]

theorem mem_ambientVectors (v : Ambient s d) : v ∈ ambientVectors s d :=
  mem_pairs.mpr ⟨mem_vectors v.1, mem_vectors v.2⟩

abbrev Query (m k s d : Nat) := (Fin k → Fin m) × (E k →ₗ[F2] Ambient s d)

def queries (m k s d : Nat) : List (Query m k s d) :=
  pairs (functions (List.finRange m) k) (allLinearMaps k _ (ambientVectors s d))

theorem mem_queries (q : Query m k s d) : q ∈ queries m k s d :=
  mem_pairs.mpr ⟨mem_functions (fun i => List.mem_finRange i) _,
    mem_allLinearMaps k _ mem_ambientVectors _⟩

abbrev Outcome (m k s d noiseCount : Nat) :=
  Query m k s d ×
    (Fin noiseCount × (E k →ₗ[F2] F2))

def outcomes (m k s d noiseCount : Nat) : List (Outcome m k s d noiseCount) :=
  pairs
    (queries m k s d)
    (pairs (List.finRange noiseCount) (allLinearMaps k F2 [0, 1]))

theorem length_outcomes (m k s d noiseCount : Nat) :
    (outcomes m k s d noiseCount).length = edgeCount m k (s+d) noiseCount := by
  simp only [outcomes, queries, length_pairs, length_functions, List.length_finRange,
    length_allLinearMaps, length_ambientVectors, List.length_cons, List.length_nil,
    edgeCount, ← pow_mul]
  change m^k * 2^((s+d)*(2*k+1)) * (noiseCount * 2^(2*k+1)) =
    m^k * 2^((2*k+1)*(s+d+1)) * noiseCount
  rw [show (2*k+1)*(s+d+1) = (s+d)*(2*k+1)+(2*k+1) by ring, pow_add]
  ring

def indexedOutcomes (m k s d : Nat) (indices : List N) :
    List (Query m k s d × (N × (E k →ₗ[F2] F2))) :=
  pairs (queries m k s d) (pairs indices (allLinearMaps k F2 [0, 1]))

theorem length_indexedOutcomes (m k s d : Nat) (indices : List N) :
    (indexedOutcomes m k s d indices).length = edgeCount m k (s+d) indices.length := by
  rw [← length_outcomes m k s d indices.length]
  simp only [indexedOutcomes, outcomes, length_pairs, List.length_finRange]

theorem mem_indexedOutcomes {indices : List N} (full : ∀ i, i ∈ indices)
    (ω : Query m k s d × (N × (E k →ₗ[F2] F2))) :
    ω ∈ indexedOutcomes m k s d indices := by
  apply mem_pairs.mpr
  exact ⟨mem_queries _, mem_pairs.mpr ⟨full _, mem_allLinearMaps k F2
    (fun a => by rcases scalar_cases a with rfl | rfl <;> simp) _⟩⟩

end DFVSGames.Reduction.ActualEnumeration


namespace DFVSGames.Decoder.PaddedLaw

open scoped BigOperators
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open DFVSGames.Soundness
open ConditionalIncidences PartnerProjection RawPartnerTarget

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : ℕ} {V : Type} [AddCommGroup V] [Module F2 V]

abbrev BlockDraw (V : Type) := (V × V) ⊕ (Fin 3 × V)

def blockAmbient : BlockDraw V → Fin 3 → V
  | .inl ab => ![ab.1, ab.2, 0]
  | .inr ia => Pi.single ia.1 ia.2

def blockSlopes (d : BlockDraw V) : V × V :=
  (blockAmbient d 0 + blockAmbient d 2, blockAmbient d 1 + blockAmbient d 2)

omit [Module F2 V] in
@[simp] theorem blockSlopes_full (ab : V × V) : blockSlopes (.inl ab) = ab := by
  simp [blockSlopes, blockAmbient]

omit [Module F2 V] in
@[simp] theorem blockSlopes_first (a : V) :
    blockSlopes (.inr ((0 : Fin 3), a)) = (a, 0) := by
  simp [blockSlopes, blockAmbient]

omit [Module F2 V] in
@[simp] theorem blockSlopes_second (a : V) :
    blockSlopes (.inr ((1 : Fin 3), a)) = (0, a) := by
  simp [blockSlopes, blockAmbient]

omit [Module F2 V] in
@[simp] theorem blockSlopes_third (a : V) :
    blockSlopes (.inr ((2 : Fin 3), a)) = (a, a) := by
  simp [blockSlopes, blockAmbient]


variable [Fintype V]

abbrev ProjectionChoice := Option (Fin 3)

def choiceMask (c : Fin k → ProjectionChoice) : Finset (Fin k) :=
  Finset.univ.filter fun j => (c j).isSome


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


namespace DFVSGames.Decoder.TableKeys

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open DFVSGames.Soundness
open scoped BigOperators

universe u v w

section BlockReduction

variable {Name : Type u} {Id : Type v} {R : Type w}
variable [AddCommGroup R] [Module F2 R] [DecidableEq R]

def slope (a d : R) : (F2 × F2) →ₗ[F2] R :=
  (LinearMap.fst F2 F2 F2).smulRight a +
    (LinearMap.snd F2 F2 F2).smulRight d

omit [DecidableEq R] in
@[simp] theorem slope_apply (a d : R) (x y : F2) :
    slope a d (x, y) = x • a + y • d := rfl

end BlockReduction


end DFVSGames.Decoder.TableKeys


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_FinalParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Reduction.ActualSource

open DFVSGames.Integration.BinaryLinear

structure Source where
  «variables» : Nat
  occurrences : Nat
  nonempty : 0 < occurrences
  equation : Fin occurrences → CloneGap.Equation (Fin «variables»)

def Source.sourceList (S : Source) : List (CloneGap.Equation (Fin S.«variables»)) :=
  List.ofFn S.equation

def Source.ofList {n : Nat} (es : List (CloneGap.Equation (Fin n)))
    (hne : es ≠ []) : Source where
  «variables» := n
  occurrences := es.length
  nonempty := List.length_pos_iff.mpr hne
  equation := es.get

@[simp] theorem Source.sourceList_ofList {n : Nat}
    (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ []) :
    (Source.ofList es hne).sourceList = es := by
  exact List.ofFn_getElem

@[simp] theorem Source.sourceList_length (S : Source) :
    S.sourceList.length = S.occurrences := by simp [Source.sourceList]

instance sourceIndexNonempty (S : Source) : Nonempty (Fin S.occurrences) :=
  ⟨⟨0, S.nonempty⟩⟩

abbrev Alphabet (s : Nat) := DFVSGames.Integration.BinaryLinear.Vector s
abbrev Ambient (s d : Nat) := Alphabet s × DFVSGames.Integration.BinaryLinear.Vector d

def alphabetEmbedding (s d : Nat) : Alphabet s →ₗ[F2] Ambient s d :=
  LinearMap.inl F2 (Alphabet s) (DFVSGames.Integration.BinaryLinear.Vector d)

@[simp] theorem alphabetEmbedding_apply (s d : Nat) (c : Alphabet s) :
    alphabetEmbedding s d c = (c, 0) := rfl

structure SplitGadget (s d : Nat) where
  f : Ambient s d → Alphabet s
  equivariant : ∀ (x : Ambient s d) (c : Alphabet s), f (x + (c, 0)) = f x + c
  NoiseIndex : Type
  noiseFintype : Fintype NoiseIndex
  noiseNonempty : Nonempty NoiseIndex
  noise : NoiseIndex → Ambient s d

attribute [instance] SplitGadget.noiseFintype SplitGadget.noiseNonempty

end DFVSGames.Reduction.ActualSource

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Analysis_NoiseEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Reduction.ActualSource

open scoped BigOperators

structure NoiseEnumeration {s d : Nat} (g : SplitGadget s d) where
  indices : List g.NoiseIndex
  nodup : indices.Nodup
  complete : ∀ i, i ∈ indices

namespace NoiseEnumeration

variable {s d : Nat} {g : SplitGadget s d}

theorem nonempty (e : NoiseEnumeration g) : e.indices ≠ [] := by
  intro h
  obtain ⟨i⟩ := g.noiseNonempty
  have hi := e.complete i
  simp only [h, List.not_mem_nil] at hi

end NoiseEnumeration
end DFVSGames.Reduction.ActualSource

namespace DFVSGames.Reduction.ActualGame

open DFVSGames.Integration.BinaryLinear
open ActualSource
open Foundations.Target
open scoped BigOperators

def names (S : Source) (i : Fin S.occurrences) (j : Fin 3) : Fin S.«variables» :=
  if j = 0 then (S.equation i).first
  else if j = 1 then (S.equation i).second else (S.equation i).third

def rhs (S : Source) (i : Fin S.occurrences) : F2 := ofBit (S.equation i).rhs

abbrev Question (S : Source) (k : Nat) := Fin k → Fin S.occurrences
abbrev Map (k s d : Nat) := ActualHomogeneous.E k →ₗ[F2] ActualSource.Ambient s d
abbrev Dual (k : Nat) := ActualHomogeneous.E k →ₗ[F2] F2
abbrev Query (S : Source) (k s d : Nat) := Question S k × Map k s d

noncomputable instance mapFintype (k s d : Nat) : Fintype (Map k s d) :=
  Fintype.ofInjective (fun X : Map k s d => (X : ActualHomogeneous.E k →
    ActualSource.Ambient s d)) DFunLike.coe_injective

noncomputable instance dualFintype (k : Nat) : Fintype (Dual k) :=
  Fintype.ofInjective (fun X : Dual k => (X : ActualHomogeneous.E k → F2))
    DFunLike.coe_injective

def canonical (S : Source) (k s d : Nat) (q : Query S k s d) :=
  ActualCanonical.canonical q.1 (names S) (rhs S) q.2

abbrev Vertex (S : Source) (k s d : Nat) := ActualOrbit.Vertex (canonical S k s d)
abbrev TwoSidedVertex (S : Source) (k s d : Nat) := Bool × Vertex S k s d

def vertex (S : Source) (k s d : Nat) (q : Query S k s d) : Vertex S k s d :=
  ActualOrbit.vertex (canonical S k s d) q

def offset (S : Source) (k s d : Nat) (q : Query S k s d) : Alphabet s :=
  ActualOrbit.offset (canonical S k s d) q

def shiftQuery (S : Source) (k s d : Nat) (c : Alphabet s)
    (q : Query S k s d) : Query S k s d :=
  (q.1, q.2 + ActualHomogeneous.tau.smulRight (c, (0 : Vector d)))

theorem canonical_shiftQuery (S : Source) (k s d : Nat) (c : Alphabet s)
    (q : Query S k s d) :
    canonical S k s d (shiftQuery S k s d c q) =
      ((canonical S k s d q).1 + (c, 0), (canonical S k s d q).2) :=
  ActualCanonical.canonical_shift _ _ _ _ _

@[simp] theorem vertex_shiftQuery (S : Source) (k s d : Nat) (c : Alphabet s)
    (q : Query S k s d) :
    vertex S k s d (shiftQuery S k s d c q) = vertex S k s d q := by
  apply (ActualOrbit.vertex_eq_iff _ _ _).2
  simp only [ActualOrbit.body, canonical_shiftQuery, Prod.snd_add, add_zero]

@[simp] theorem offset_shiftQuery (S : Source) (k s d : Nat) (c : Alphabet s)
    (q : Query S k s d) :
    offset S k s d (shiftQuery S k s d c q) = offset S k s d q + c := by
  simp only [offset, ActualOrbit.offset, canonical_shiftQuery, Prod.fst_add]

noncomputable def vertexCount (S : Source) (k s d : Nat) : Nat :=
  Fintype.card (TwoSidedVertex S k s d)

noncomputable def vertexEncoding (S : Source) (k s d : Nat) :
    TwoSidedVertex S k s d ≃ Fin (vertexCount S k s d) :=
  ActualOrbit.vertexEquiv (canonical S k s d)

abbrev Outcome (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) :=
  Query S k s d × g.NoiseIndex × Dual k

def leftQuery (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (ω : Outcome S k g) : Query S k s d := ω.1

def rightQuery (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (ω : Outcome S k g) : Query S k s d :=
  (ω.1.1, ω.1.2 + ω.2.2.smulRight (g.noise ω.2.1))

noncomputable def outcomes (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) :
    List (Outcome S k g) := Finset.univ.toList

@[simp] theorem mem_outcomes (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (ω : Outcome S k g) : ω ∈ outcomes S k g := by
  simp [outcomes]

@[simp] theorem outcomes_length (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) : (outcomes S k g).length = Fintype.card (Outcome S k g) := by
  simp [outcomes]

noncomputable def sideLabel (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) (side : Bool) :
    Vertex S k s d → Alphabet s := fun v =>
  (Encoding.alphabetEquiv s).symm (labeling (vertexEncoding S k s d (side, v)))

noncomputable def labelingOf (S : Source) (k s d : Nat)
    (labels : Bool → Vertex S k s d → Alphabet s) :
    Fin (vertexCount S k s d) → Fin (2^s) := fun i =>
  let v := (vertexEncoding S k s d).symm i
  Encoding.alphabetEquiv s (labels v.1 v.2)

@[simp] theorem sideLabel_labelingOf (S : Source) (k s d : Nat)
    (labels : Bool → Vertex S k s d → Alphabet s) (side : Bool) :
    sideLabel S k s d (labelingOf S k s d labels) side = labels side := by
  funext v
  simp [sideLabel, labelingOf]

def orbitBodyDecidableEq (S : Source) (k s d : Nat) :
    DecidableEq (Vector d × (Fin k → ActualCanonical.Record
      (Fin S.«variables») (Fin S.occurrences) (ActualSource.Ambient s d))) :=
  @instDecidableEqProd _ _ inferInstance inferInstance

def explicitBodies (S : Source) (k s d : Nat) := by
  letI := orbitBodyDecidableEq S k s d
  exact Encoding.imageVertices (ActualEnumeration.queries S.occurrences k s d)
    (ActualOrbit.body (canonical S k s d))

def explicitVertexCount (S : Source) (k s d : Nat) : Nat :=
  2 * (explicitBodies S k s d).length

def explicitVertexEncoding (S : Source) (k s d : Nat) :
    TwoSidedVertex S k s d ≃ Fin (explicitVertexCount S k s d) := by
  letI := orbitBodyDecidableEq S k s d
  exact (Equiv.prodCongr (Equiv.refl Bool)
    (ActualOrbit.explicitVertexEquiv (canonical S k s d)
      (ActualEnumeration.queries S.occurrences k s d) ActualEnumeration.mem_queries)).trans
    (Encoding.sideEquiv _)

def explicitEdge (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (ω : Outcome S k g) : Constraint (explicitVertexCount S k s d) (2^s) where
  source := explicitVertexEncoding S k s d (false, vertex S k s d (leftQuery S k g ω))
  target := explicitVertexEncoding S k s d (true, vertex S k s d (rightQuery S k g ω))
  permutation := Encoding.translationTable
    (offset S k s d (leftQuery S k g ω)) (offset S k s d (rightQuery S k g ω))

def explicitOutcomes (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (en : NoiseEnumeration g) : List (Outcome S k g) :=
  ActualEnumeration.indexedOutcomes S.occurrences k s d en.indices

@[simp] theorem mem_explicitOutcomes (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) (ω : Outcome S k g) :
    ω ∈ explicitOutcomes S k g en :=
  ActualEnumeration.mem_indexedOutcomes en.complete ω

def outputInstanceWithEnumeration (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) : Foundations.Target.Instance (2^s) where
  vertices := explicitVertexCount S k s d
  constraints := (explicitOutcomes S k g en).map (explicitEdge S k g)
  nonempty := by
    intro h
    let ω : Outcome S k g := Classical.choice inferInstance
    have hm : explicitEdge S k g ω ∈
        (explicitOutcomes S k g en).map (explicitEdge S k g) :=
      List.mem_map.mpr ⟨ω, mem_explicitOutcomes S k g en ω, rfl⟩
    rw [h] at hm
    exact List.not_mem_nil hm

@[simp] theorem outputInstanceWithEnumeration_length (S : Source) (k : Nat)
    {s d : Nat} (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (outputInstanceWithEnumeration S k g en).constraints.length =
      Explicit.edgeCount S.occurrences k (s+d) en.indices.length := by
  simp only [outputInstanceWithEnumeration, List.length_map, explicitOutcomes,
    ActualEnumeration.length_indexedOutcomes]

end DFVSGames.Reduction.ActualGame

namespace DFVSGames.Decoder.TableKeysGame

open DFVSGames.Integration.BinaryLinear DFVSGames.Reduction
open ActualSource Foundations.Target
open scoped BigOperators

abbrev Dual (k : Nat) := ActualGame.Dual k
abbrev Query (S : Source) (k s d : Nat) := ActualGame.Query S k s d
abbrev canonical (S : Source) (k s d : Nat) := ActualGame.canonical S k s d

abbrev Vertex (S : Source) (k s d : Nat) := ActualGame.Vertex S k s d
abbrev vertex (S : Source) (k s d : Nat) := ActualGame.vertex S k s d
abbrev offset (S : Source) (k s d : Nat) := ActualGame.offset S k s d

noncomputable def vertexCount (S : Source) (k s d : Nat) : Nat :=
  Fintype.card (Vertex S k s d)

noncomputable def vertexEncoding (S : Source) (k s d : Nat) :
    Vertex S k s d ≃ Fin (vertexCount S k s d) := Fintype.equivFin _

abbrev Outcome (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) :=
  Query S k s d × g.NoiseIndex × Dual k

abbrev leftQuery (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) :=
  ActualGame.leftQuery S k g
abbrev rightQuery (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) :=
  ActualGame.rightQuery S k g

noncomputable def edge (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (ω : Outcome S k g) : Constraint (vertexCount S k s d) (2^s) where
  source := vertexEncoding S k s d (vertex S k s d (leftQuery S k g ω))
  target := vertexEncoding S k s d (vertex S k s d (rightQuery S k g ω))
  permutation := Encoding.translationTable
    (offset S k s d (leftQuery S k g ω)) (offset S k s d (rightQuery S k g ω))

noncomputable def outcomes (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) :=
  ActualGame.outcomes S k g

noncomputable def outputInstance (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) :
    Instance (2^s) where
  vertices := vertexCount S k s d
  constraints := (outcomes S k g).map (edge S k g)
  nonempty := by
    intro h
    let ω : Outcome S k g := Classical.choice inferInstance
    have hm : edge S k g ω ∈ (outcomes S k g).map (edge S k g) :=
      List.mem_map.mpr ⟨ω, ActualGame.mem_outcomes S k g ω, rfl⟩
    rw [h] at hm
    exact List.not_mem_nil hm

@[simp] theorem outputInstance_constraints_length (S : Source) (k : Nat)
    {s d : Nat} (g : SplitGadget s d) :
    (outputInstance S k g).constraints.length = Fintype.card (Outcome S k g) := by
  simp [outputInstance, outcomes]

noncomputable def vertexLabel (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    Vertex S k s d → Alphabet s := fun v =>
  (Encoding.alphabetEquiv s).symm (labeling (vertexEncoding S k s d v))

noncomputable def labelingOf (S : Source) (k s d : Nat)
    (labels : Vertex S k s d → Alphabet s) :
    Fin (vertexCount S k s d) → Fin (2^s) := fun i =>
  Encoding.alphabetEquiv s (labels ((vertexEncoding S k s d).symm i))

@[simp] theorem vertexLabel_labelingOf (S : Source) (k s d : Nat)
    (labels : Vertex S k s d → Alphabet s) :
    vertexLabel S k s d (labelingOf S k s d labels) = labels := by
  funext v
  simp [vertexLabel, labelingOf]

def explicitVertexCount (S : Source) (k s d : Nat) : Nat :=
  (ActualGame.explicitBodies S k s d).length

def explicitVertexEncoding (S : Source) (k s d : Nat) :
    Vertex S k s d ≃ Fin (explicitVertexCount S k s d) := by
  letI := ActualGame.orbitBodyDecidableEq S k s d
  exact ActualOrbit.explicitVertexEquiv (canonical S k s d)
    (ActualEnumeration.queries S.occurrences k s d) ActualEnumeration.mem_queries

noncomputable def semanticToExplicitVertices (S : Source) (k s d : Nat) :
    Fin (vertexCount S k s d) ≃ Fin (explicitVertexCount S k s d) :=
  (vertexEncoding S k s d).symm.trans (explicitVertexEncoding S k s d)

@[simp] theorem semanticToExplicitVertices_apply (S : Source) (k s d : Nat)
    (v : Vertex S k s d) :
    semanticToExplicitVertices S k s d (vertexEncoding S k s d v) =
      explicitVertexEncoding S k s d v := by
  simp [semanticToExplicitVertices]

def explicitEdge (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (ω : Outcome S k g) : Constraint (explicitVertexCount S k s d) (2^s) where
  source := explicitVertexEncoding S k s d (vertex S k s d (leftQuery S k g ω))
  target := explicitVertexEncoding S k s d (vertex S k s d (rightQuery S k g ω))
  permutation := Encoding.translationTable
    (offset S k s d (leftQuery S k g ω)) (offset S k s d (rightQuery S k g ω))

def outputInstanceWithEnumeration (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) : Instance (2^s) where
  vertices := explicitVertexCount S k s d
  constraints := (ActualGame.explicitOutcomes S k g en).map (explicitEdge S k g)
  nonempty := by
    intro h
    let ω : Outcome S k g := Classical.choice inferInstance
    have hm : explicitEdge S k g ω ∈
        (ActualGame.explicitOutcomes S k g en).map (explicitEdge S k g) :=
      List.mem_map.mpr ⟨ω, ActualGame.mem_explicitOutcomes S k g en ω, rfl⟩
    rw [h] at hm
    exact List.not_mem_nil hm

@[simp] theorem outputInstanceWithEnumeration_length (S : Source) (k : Nat)
    {s d : Nat} (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (outputInstanceWithEnumeration S k g en).constraints.length =
      Explicit.edgeCount S.occurrences k (s+d) en.indices.length := by
  simp only [outputInstanceWithEnumeration, List.length_map,
    ActualGame.explicitOutcomes, ActualEnumeration.length_indexedOutcomes]

end DFVSGames.Decoder.TableKeysGame

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_RowErasureSliceQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.RowErasureSliceQuotient

noncomputable section

variable {R E K L : Type*} [Field R]
  [AddCommGroup E] [AddCommGroup K] [AddCommGroup L]
  [Module R E] [Module R K] [Module R L]

def direction (A : K →ₗ[R] L) (Q : Submodule R E)
    (N : (E ⧸ Q) →ₗ[R] A.ker) : E →ₗ[R] K :=
  A.ker.subtype.comp (N.comp Q.mkQ)

@[simp] theorem direction_apply (A : K →ₗ[R] L) (Q : Submodule R E)
    (N : (E ⧸ Q) →ₗ[R] A.ker) (x : E) :
    direction A Q N x = (N (Q.mkQ x) : K) := rfl

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

def equiv (A : K →ₗ[R] L) (Q : Submodule R E) (M₀ : E →ₗ[R] K) :
    ((E ⧸ Q) →ₗ[R] A.ker) ≃ AffineSlice A Q M₀ :=
  Equiv.ofBijective (ofQuotient A Q M₀) (ofQuotient_bijective A Q M₀)

@[simp] theorem equiv_apply (A : K →ₗ[R] L) (Q : Submodule R E)
    (M₀ : E →ₗ[R] K) (N : (E ⧸ Q) →ₗ[R] A.ker) :
    equiv A Q M₀ N = ofQuotient A Q M₀ N := rfl

end
end DFVSGames.Inverse.RowErasureSliceQuotient

namespace DFVSGames.Clean.IncidenceGap

open DFVSGames.Foundations.Games
open DFVSGames.Soundness.IncidenceExtraction (Incidence Triple xorTriple)
open scoped BigOperators

noncomputable section

variable {O N : Type} [Fintype O] [Fintype N]

local instance accepts_decidable_rf85d43_1 (g : Incidence O N) (o : O) (i : Fin 3)
    (a : Triple) (b : Bool) : Decidable (g.accepts o i a b) :=
  inferInstanceAs (Decidable (xorTriple a = g.rhs o ∧ a i = b))
def slotLaw (ω : FiniteDistribution O) : FiniteDistribution (O × Fin 3) :=
  ω.product (FiniteDistribution.uniform (Fin 3))

@[simp] theorem slotLaw_weight (ω : FiniteDistribution O) (o : O) (i : Fin 3) :
    (slotLaw ω).weight (o, i) = ω.weight o / 3 := by
  simp [slotLaw, FiniteDistribution.product, FiniteDistribution.uniform, div_eq_mul_inv]

def incidenceLaw (g : Incidence O N) (ω : FiniteDistribution O) :
    FiniteDistribution (O × N) :=
  (slotLaw ω).pushforward (fun q => (q.1, g.name q.1 q.2))

def game (g : Incidence O N) (ω : FiniteDistribution O) : Game O N Triple Bool := by
  classical
  exact { questions := incidenceLaw g ω
          accepts := fun o n a b => decide (g.namedAccepts o n a b) }

@[simp] theorem game_accepts_iff (g : Incidence O N) (ω : FiniteDistribution O)
    (o : O) (n : N) (a : Triple) (b : Bool) :
    (game g ω).accepts o n a b = true ↔ g.namedAccepts o n a b := by
  classical
  simp [game]

end
end DFVSGames.Clean.IncidenceGap

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.GraphTables

open DFVSGames.Foundations.Complexity

abbrev Label := Fin 64
abbrev RelationTable := Vector Bool 4096

end DFVSGames.Foundations.PCP.GraphTables

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

def rowIndex (v d : Nat) : Fin v × Fin d ≃ Fin (v * d) := finProdFinEquiv

structure Table (v d : Nat) where
  rows : Vector (Fin (v * d)) (v * d)
  involutive : Function.Involutive (fun i : Fin (v * d) => rows[i])

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

inductive Tape
  | original | work | target | scratch | count | spare
  deriving DecidableEq

instance instFintypeTape : Fintype Tape := derive_fintype% Tape

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

open DFVSGames.Foundations.PCP

end DFVSGames.Foundations.Complexity.MachineCloudCount

namespace DFVSGames.Foundations.Complexity.MachineCeilingPower

open Turing
open MachineComposition
open DFVSGames.Foundations.PCP

inductive Tape
  | input | work | power | saved | level | fuel | spare | product
  deriving DecidableEq

instance instFintypeTape : Fintype Tape := derive_fintype% Tape

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

def tapes (view : K' → Option K) (source : K → List Bool)
    (extra : K' → List Bool) : K' → List Bool :=
  fun j => match view j with
    | some k => source k
    | none => extra j

end Placement

inductive Tape
  | table | query | count | work | scratch | spare | power | level | fuel | product
  deriving DecidableEq

instance instFintypeTape : Fintype Tape := derive_fintype% Tape

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

def countView : Tape → Option MachineCloudCount.Tape
  | .table => some .original
  | .query => some .target
  | .count => some .count
  | .work => some .work
  | .scratch => some .scratch
  | .spare => some .spare
  | _ => none

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

@[simp] theorem countMemory (a b c d e f g h i j : List Bool) :
    Placement.tapes countView (MachineCloudCount.memory a d b e c f)
      (memory a b c d e f g h i j) = memory a b c d e f g h i j := by
  funext k; cases k <;> rfl

@[simp] theorem powerMemory (a b c d e f g h i j : List Bool) :
    Placement.tapes powerView (MachineCeilingPower.memory c d g e h i f j)
      (memory a b c d e f g h i j) = memory a b c d e f g h i j := by
  funext k; cases k <;> rfl

end DFVSGames.Foundations.Complexity.MachineCloudPadding

namespace DFVSGames.Foundations.Complexity.MachineCloudPrefix

open Turing MachineComposition
open DFVSGames.Foundations.PCP
open scoped BigOperators

inductive Tape
  | inner (k : MachineCloudPadding.Tape)
  | bound | remaining | total
  deriving DecidableEq, Fintype

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

end DFVSGames.Foundations.Complexity.MachineCloudPrefix

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

namespace DFVSGames.Foundations.Complexity.MachineRegularMetadata

open Turing MachineComposition
open DFVSGames.Foundations.PCP

inductive Extra | padding | level
  deriving DecidableEq

instance instFintypeExtra : Fintype Extra := derive_fintype% Extra

abbrev Tape := Fin 27 ⊕ Extra

variable {σ : Type}

def cloudView : Tape → Option MachineCloudPadding.Tape
  | .inl i => match i.val with
    | 0 => some .table
    | 2 => some .query
    | 4 => some .count
    | 9 => some .work
    | 10 => some .scratch
    | 11 => some .spare
    | 12 => some .fuel
    | 13 => some .product
    | _ => none
  | .inr .padding => some .power
  | .inr .level => some .level

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

def frame (data : Data) : Tape → List Bool
  | .inl i => match i.val with
    | 0 => data.table
    | 1 => data.globalIndex
    | 2 => data.owner
    | 3 => data.localRank
    | 4 => data.count
    | 5 => data.offset
    | 6 => data.darts
    | 7 => data.rotor
    | 8 => data.output
    | _ => []
  | .inr .padding => data.padding
  | .inr .level => data.level

@[simp] theorem frame_index (data : Data) :
    frame data (.inl 1) = data.globalIndex := rfl

@[simp] theorem frame_query_empty (data : Data) :
    frame data (.inl 9) = [] := rfl

end DFVSGames.Foundations.Complexity.MachineRegularMetadata
end

section

namespace DFVSGames.Foundations.PCP.ExpanderRowControl

open ExpanderTables

abbrev degree (d : Nat) : Nat := d * d
abbrev cloudSize (d : Nat) : Nat := degree d * degree d

structure Control (d : Nat) where
  firstH : Fin (cloudSize d) × Fin d
  lastInput : Fin d
  firstG : Fin (degree d)
  secondG : Fin (degree d)
  lastH : Fin (cloudSize d) × Fin d
  deriving DecidableEq, Fintype

def squarePorts {d : Nat} (s : Control d) : Fin (degree d) × Fin (degree d) :=
  (rowIndex (degree d) (degree d)).symm s.firstH.1

def receiveFirst {d : Nat} (s : Control d) (returnedPort : Fin (degree d)) : Control d :=
  { s with firstG := returnedPort }

def firstOffset {d : Nat} (s : Control d) : Fin (degree d) := (squarePorts s).1
def secondOffset {d : Nat} (s : Control d) : Fin (degree d) := (squarePorts s).2

@[simp] theorem firstOffset_receiveFirst {d : Nat} (s : Control d) (r : Fin (degree d)) :
    firstOffset (receiveFirst s r) = firstOffset s := rfl

@[simp] theorem secondOffset_receiveFirst {d : Nat} (s : Control d) (r : Fin (degree d)) :
    secondOffset (receiveFirst s r) = secondOffset s := rfl

@[simp] theorem receiveFirst_port {d : Nat} (s : Control d) (r : Fin (degree d)) :
    (receiveFirst s r).firstG = r := rfl

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

namespace DFVSGames.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

inductive Tape
  | inputVertex | table | output
  | emitScratch | queryReverse | queryIndex
  | lookupOutput | lookupWork | lookupRestore
  | quotientFirst | quotientSecond | remainderFirst | remainderSecond
  deriving DecidableEq

instance instFintypeTape : Fintype Tape := derive_fintype% Tape

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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_AdviceLaw
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
open ConditionalIncidences RawPartnerTarget
open DFVSGames.Foundations.Games
open DFVSGames.Clean

noncomputable section
attribute [local instance] Classical.propDecidable

section ProjectionSeeds

variable {k : ℕ} {V : Type} [AddCommGroup V] [Module F2 V] [Fintype V]

abbrev ProjectionSeed (k : ℕ) (V : Type) [AddCommGroup V] [Module F2 V] :=
  Σ c : Fin k → PaddedLaw.ProjectionChoice,
    RawPoint (PaddedLaw.choiceMask c) →ₗ[F2] V

end ProjectionSeeds

section CompleteData

variable {k : ℕ} {Id K W R : Type}
  [AddCommGroup K] [Module F2 K] [AddCommGroup W] [Module F2 W]
  [AddCommGroup R] [Module F2 R]

abbrev FullSeed (k : ℕ) (Id K W R : Type)
    [AddCommGroup K] [Module F2 K] [AddCommGroup W] [Module F2 W]
    [AddCommGroup R] [Module F2 R] :=
  ((Fin k → Id) × (K →ₗ[F2] R)) × ProjectionSeed k (K × W)

abbrev CompleteData (k : ℕ) (Id K W R : Type)
    [AddCommGroup K] [Module F2 K] [AddCommGroup W] [Module F2 W]
    [AddCommGroup R] [Module F2 R] :=
  Σ ua : (Fin k → Id) × (K →ₗ[F2] R),
    Σ c : Fin k → PaddedLaw.ProjectionChoice,
      (RawPoint (PaddedLaw.choiceMask c) →ₗ[F2] W) ×
        AdviceFibers.ObservedRow (E := RawPoint (PaddedLaw.choiceMask c)) ua.2

abbrev PrivateMap (d : CompleteData k Id K W R) :=
  RawPoint (PaddedLaw.choiceMask d.2.1) →ₗ[F2] d.1.2.ker

def targetObservationEquiv (J : Finset (Fin k)) (A : K →ₗ[F2] R) :
    (RawPoint J →ₗ[F2] (K × W)) ≃
      ((RawPoint J →ₗ[F2] W) × AdviceFibers.ObservedRow (E := RawPoint J) A) ×
        (RawPoint J →ₗ[F2] A.ker) :=
  (LinearMap.prodEquiv F2).toEquiv.symm |>.trans
    (Equiv.prodComm _ _) |>.trans
    (Equiv.prodCongr (Equiv.refl _) (AdviceFibers.observationEquiv A)) |>.trans
    (Equiv.prodAssoc _ _ _).symm

def fullSeedCoordinatesEquiv :
    FullSeed k Id K W R ≃ Σ d : CompleteData k Id K W R, PrivateMap d :=
  ((Equiv.sigmaEquivProd ((Fin k → Id) × (K →ₗ[F2] R))
      (ProjectionSeed k (K × W))).symm.trans
    (Equiv.sigmaCongrRight fun (ua : (Fin k → Id) × (K →ₗ[F2] R)) =>
      Equiv.sigmaCongrRight fun c => targetObservationEquiv (PaddedLaw.choiceMask c) ua.2)).trans
    { toFun := fun p => ⟨⟨p.1, p.2.1, p.2.2.1⟩, p.2.2.2⟩
      invFun := fun p => ⟨p.1.1, p.1.2.1, p.1.2.2, p.2⟩
      left_inv := fun p => by rcases p with ⟨ua, c, ⟨T, S⟩, N⟩; rfl
      right_inv := fun p => by rcases p with ⟨⟨ua, c, T, S⟩, N⟩; rfl }

def completeObserve (s : FullSeed k Id K W R) : CompleteData k Id K W R :=
  (fullSeedCoordinatesEquiv s).1

def completeAssemble (d : CompleteData k Id K W R) (N : PrivateMap d) :
    FullSeed k Id K W R :=
  fullSeedCoordinatesEquiv.symm ⟨d, N⟩

@[simp] theorem completeObserve_assemble (d : CompleteData k Id K W R)
    (N : PrivateMap d) : completeObserve (completeAssemble d N) = d :=
  congrArg Sigma.fst (fullSeedCoordinatesEquiv.apply_symm_apply ⟨d, N⟩)

def completeFiberEquiv (d : CompleteData k Id K W R) :
    PrivateMap d ≃ {s : FullSeed k Id K W R // completeObserve s = d} :=
  ((Equiv.subtypeEquiv fullSeedCoordinatesEquiv (fun _ => Iff.rfl)).trans
    (Equiv.sigmaSubtype d)).symm

@[simp] theorem completeFiberEquiv_val (d : CompleteData k Id K W R) (N : PrivateMap d) :
    (completeFiberEquiv d N).val = completeAssemble d N := rfl

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

namespace DFVSGames.Reduction.ActualCompleteness

open DFVSGames.Integration.BinaryLinear
open scoped BigOperators

open ActualSource

section HonestEvaluation
open ActualCanonical ActualHomogeneous
variable {Name Id R : Type*} [AddCommGroup R] [Module F2 R] [DecidableEq R] {k : Nat}

def honestPoint (occ : Fin k → Id) (names : Id → Fin 3 → Name) (A : Name → F2) : E k :=
  (1, fun j => (A (names (occ j) 0), A (names (occ j) 1)))

@[simp] theorem honestPoint_tau (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (A : Name → F2) : tau (honestPoint occ names A) = 1 := rfl

end HonestEvaluation

section ActualLabeling
noncomputable section

def sourcePoint (S : Source) (k : Nat) (A : Fin S.«variables» → Bool)
    (U : ActualGame.Question S k) : ActualHomogeneous.E k :=
  honestPoint U (ActualGame.names S) (fun n => ofBit (A n))

@[simp] theorem sourcePoint_tau (S : Source) (k : Nat) (A : Fin S.«variables» → Bool)
    (U : ActualGame.Question S k) : ActualHomogeneous.tau (sourcePoint S k A U) = 1 := rfl

end
end ActualLabeling

end DFVSGames.Reduction.ActualCompleteness
end

section

namespace DFVSGames.Reduction.CanonicalEncoding

open Integration.BinaryLinear
open Foundations.Complexity

abbrev Ambient (s d : Nat) := Integration.BinaryLinear.Vector s × Integration.BinaryLinear.Vector d
abbrev Record (n m s d : Nat) := ActualCanonical.Record (Fin n) (Fin m) (Ambient s d)
abbrev Body (n m k s d : Nat) := Integration.BinaryLinear.Vector d × (Fin k → Record n m s d)

def vectorWord {s : Nat} (v : Integration.BinaryLinear.Vector s) : Nat :=
  (Encoding.alphabetEquiv s v).val

theorem vectorWord_lt {s : Nat} (v : Integration.BinaryLinear.Vector s) :
    vectorWord v < 2^s := (Encoding.alphabetEquiv s v).isLt

theorem vectorWord_injective {s : Nat} :
    Function.Injective (vectorWord (s := s)) := by
  intro x y h
  apply (Encoding.alphabetEquiv s).injective
  exact Fin.ext h

@[simp] theorem vectorWord_eq_iff {s : Nat} (x y : Integration.BinaryLinear.Vector s) :
    vectorWord x = vectorWord y ↔ x = y := vectorWord_injective.eq_iff

def recordWords {n m s d : Nat} : Record n m s d → List Nat
  | .blank => [0, 0, 0, 0, 0, 0, 0, 0, 0]
  | .single name coefficient =>
      [1, name.val, 0, vectorWord coefficient.1, vectorWord coefficient.2, 0, 0, 0, 0]
  | .full occurrence coefficients =>
      [2, 0, occurrence.val,
        vectorWord (coefficients 0).1, vectorWord (coefficients 0).2,
        vectorWord (coefficients 1).1, vectorWord (coefficients 1).2,
        vectorWord (coefficients 2).1, vectorWord (coefficients 2).2]

@[simp] theorem recordWords_length {n m s d : Nat} (r : Record n m s d) :
    (recordWords r).length = 9 := by
  cases r <;> rfl

theorem recordWords_injective {n m s d : Nat} :
    Function.Injective (recordWords (n := n) (m := m) (s := s) (d := d)) := by
  intro r t h
  cases r with
  | blank => cases t <;> simp_all [recordWords]
  | single name coefficient =>
    cases t with
    | blank => simp [recordWords] at h
    | single name' coefficient' =>
      simp [recordWords] at h
      rcases h with ⟨hn, hc, hd⟩
      have hp : coefficient = coefficient' := Prod.ext hc hd
      have hn' : name = name' := Fin.ext hn
      cases hn'
      cases hp
      rfl
    | full occurrence coefficients => simp [recordWords] at h
  | full occurrence coefficients =>
    cases t with
    | blank => simp [recordWords] at h
    | single name coefficient => simp [recordWords] at h
    | full occurrence' coefficients' =>
      simp [recordWords] at h
      rcases h with ⟨hi, h0c, h0d, h1c, h1d, h2c, h2d⟩
      have hp : coefficients = coefficients' := by
        funext i
        fin_cases i
        · exact Prod.ext h0c h0d
        · exact Prod.ext h1c h1d
        · exact Prod.ext h2c h2d
      have hi' : occurrence = occurrence' := Fin.ext hi
      cases hi'
      cases hp
      rfl

def recordsWords {n m s d : Nat} (rs : List (Record n m s d)) : List Nat :=
  rs.flatMap recordWords

@[simp] theorem recordsWords_nil {n m s d : Nat} :
    recordsWords ([] : List (Record n m s d)) = [] := rfl

@[simp] theorem recordsWords_cons {n m s d : Nat} (r : Record n m s d)
    (rs : List (Record n m s d)) :
    recordsWords (r :: rs) = recordWords r ++ recordsWords rs := rfl

@[simp] theorem recordsWords_length {n m s d : Nat} (rs : List (Record n m s d)) :
    (recordsWords rs).length = 9 * rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [ih, Nat.mul_add, Nat.add_comm]

theorem recordsWords_take_head {n m s d : Nat} (r : Record n m s d)
    (rs : List (Record n m s d)) :
    (recordsWords (r :: rs)).take 9 = recordWords r := by
  change (recordWords r ++ recordsWords rs).take 9 = recordWords r
  simpa only [recordWords_length] using
    (List.take_append_length (l₁ := recordWords r) (l₂ := recordsWords rs))

theorem recordsWords_injective {n m s d : Nat} :
    Function.Injective (recordsWords (n := n) (m := m) (s := s) (d := d)) := by
  intro rs
  induction rs with
  | nil =>
    intro ts h
    cases ts with
    | nil => rfl
    | cons t ts =>
      have hl := congrArg List.length h
      simp only [recordsWords_length, List.length_nil, List.length_cons] at hl
      omega
  | cons r rs ih =>
    intro ts h
    cases ts with
    | nil =>
      have hl := congrArg List.length h
      simp only [recordsWords_length, List.length_nil, List.length_cons] at hl
      omega
    | cons t ts =>
      have hh := congrArg (List.take 9) h
      simp only [recordsWords_take_head] at hh
      have hr := recordWords_injective hh
      subst t
      apply congrArg (List.cons r)
      apply ih
      exact List.append_cancel_left (by simpa only [recordsWords_cons] using h)

def bodyWords {n m k s d : Nat} (body : Body n m k s d) : List Nat :=
  vectorWord body.1 :: recordsWords (List.ofFn body.2)

@[simp] theorem bodyWords_length {n m k s d : Nat} (body : Body n m k s d) :
    (bodyWords body).length = 1 + 9*k := by
  simp [bodyWords, Nat.add_comm]

theorem bodyWords_injective {n m k s d : Nat} :
    Function.Injective (bodyWords (n := n) (m := m) (k := k) (s := s) (d := d)) := by
  intro x y h
  have hh := List.cons.inj h
  apply Prod.ext
  · exact vectorWord_injective hh.1
  · exact List.ofFn_injective (recordsWords_injective hh.2)

@[simp] theorem bodyWords_eq_iff {n m k s d : Nat} (x y : Body n m k s d) :
    bodyWords x = bodyWords y ↔ x = y := bodyWords_injective.eq_iff

def wordBound (n m s d : Nat) : Nat := n + m + 2^s + 2^d + 3

theorem recordWords_bounded {n m s d : Nat} (r : Record n m s d)
    (w : Nat) (hw : w ∈ recordWords r) : w ≤ wordBound n m s d := by
  unfold wordBound
  cases r with
  | blank =>
    simp [recordWords] at hw
    subst w
    exact Nat.zero_le _
  | single name coefficient =>
    have hn := name.isLt
    have hc := vectorWord_lt coefficient.1
    have hd := vectorWord_lt coefficient.2
    simp only [recordWords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h | h | h | h | h | h | h <;> omega
  | full occurrence coefficients =>
    have hi := occurrence.isLt
    have h0c := vectorWord_lt (coefficients 0).1
    have h0d := vectorWord_lt (coefficients 0).2
    have h1c := vectorWord_lt (coefficients 1).1
    have h1d := vectorWord_lt (coefficients 1).2
    have h2c := vectorWord_lt (coefficients 2).1
    have h2d := vectorWord_lt (coefficients 2).2
    simp only [recordWords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h | h | h | h | h | h | h <;> omega

theorem bodyWords_bounded {n m k s d : Nat} (body : Body n m k s d)
    (w : Nat) (hw : w ∈ bodyWords body) : w ≤ wordBound n m s d := by
  rcases List.mem_cons.mp hw with h | h
  · subst w
    have hv := vectorWord_lt body.1
    have hs : 0 < (2 : Nat)^s := pow_pos (by decide) _
    unfold wordBound
    omega
  · obtain ⟨r, _, hr⟩ := List.mem_flatMap.mp h
    exact recordWords_bounded r w hr

end DFVSGames.Reduction.CanonicalEncoding
end

end
end
end
end
end
end
end
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

def radix (B : Nat) (words : List Nat) : Nat := Nat.ofDigits B words.reverse

@[simp] theorem radix_nil (B : Nat) : radix B [] = 0 := rfl

theorem radix_lt_pow_length {B : Nat} (hB : 1 < B) (words : List Nat)
    (bounded : ∀ w ∈ words, w < B) : radix B words < B ^ words.length := by
  unfold radix
  simpa only [List.length_reverse] using
    Nat.ofDigits_lt_base_pow_length hB
      (fun w hw => bounded w (List.mem_reverse.mp hw))

def base (n m s d : Nat) : Nat := wordBound n m s d + 1

@[simp] theorem base_eq (n m s d : Nat) :
    base n m s d = n + m + 2^s + 2^d + 4 := by
  simp [base, wordBound, Nat.add_assoc]

theorem one_lt_base (n m s d : Nat) : 1 < base n m s d := by
  have h : 3 ≤ wordBound n m s d := by
    unfold wordBound
    exact Nat.le_add_left 3 _
  unfold base
  omega

theorem bodyWords_lt_base {n m k s d : Nat} (body : Body n m k s d)
    (w : Nat) (hw : w ∈ bodyWords body) : w < base n m s d :=
  Nat.lt_succ_of_le (bodyWords_bounded body w hw)

def capacity (n m k s d : Nat) : Nat := (base n m s d) ^ (1 + 9*k)

def bodyAddress {n m k s d : Nat} (body : Body n m k s d) :
    Fin (capacity n m k s d) :=
  ⟨radix (base n m s d) (bodyWords body), by
    simpa only [capacity, bodyWords_length] using
      radix_lt_pow_length (one_lt_base n m s d) (bodyWords body) (bodyWords_lt_base body)⟩

@[simp] theorem bodyAddress_val {n m k s d : Nat} (body : Body n m k s d) :
    (bodyAddress body).val = radix (base n m s d) (bodyWords body) := rfl

end DFVSGames.Reduction.CanonicalAddress
end

section

namespace DFVSGames.Integration.NoiseTables

open BinaryLinear DFVSGames.Reduction.ActualSource

variable {s d : Nat}

structure Table (s d : Nat) where
  vectors : List (Ambient s d)
  nonempty : vectors ≠ []

namespace Table

def ofEnumeration (g : SplitGadget s d) (en : NoiseEnumeration g) : Table s d where
  vectors := en.indices.map g.noise
  nonempty := by simpa using en.nonempty

@[simp] theorem ofEnumeration_length (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (ofEnumeration g en).vectors.length = en.indices.length := by
  simp [ofEnumeration]

end Table
end DFVSGames.Integration.NoiseTables
end

end
end
end
end
end
end
end
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

inductive Tape
  | input | output | accumulator | scratch | vertices | darts | tail | head | rowIndex
  | archive | reverseIndex | scanWork | indexWork
  deriving DecidableEq

instance instFintypeTape : Fintype Tape := derive_fintype% Tape

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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_FinalCNFHeader
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

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing

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

end DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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

inductive Tape
  | input | header | counter | field (slot : Fin 4) | scratch | reversed | output
  deriving DecidableEq, Fintype

abbrev Context (D : Nat) := Fin 2 ⊕ (Fin D × Fin 4)

def headerTape (j : Fin 2) : Tape := if j.val = 0 then .header else .counter

def contextSource {D : Nat} : Context D → Tape
  | .inl j => headerTape j
  | .inr p => .field p.2

end DFVSGames.Explicit.MachineClone100Model
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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


