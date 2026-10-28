-- Prove2me | Definitions.Def_OAIQ087A000
-- name    : OAIQ087A000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:17:26.740241+00:00
-- url     : https://prove2.me/theorems/86e801ad-9cf7-427f-9550-3692277e7d22
-- title:
--   Definitions bundle OAIQ087A000 of the split of OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 659 declarations of OpenAI's Lean: 354 definitions, 13 inductive types or structures, 5 instances and 287 theorems. The definitions and types are `OAI.MaxCutGames.Appendix.A13Index.BoundedPositiveTriple`, `OAI.MaxCutGames.Appendix.A13Index.PositiveTriple`, `OAI.MaxCutGames.Appendix.A13Index.PositiveWitness`, `OAI.MaxCutGames.Appendix.A13Index.Triple`, `OAI.MaxCutGames.Appendix.A13Index.WeakPositive`, `OAI.MaxCutGames.Appendix.A13Index.boundedPositiveTripleFintype`, `OAI.MaxCutGames.Appendix.A13Index.geometricIndexFintype`, `OAI.MaxCutGames.Appendix.A13Index.positiveEquiv`, `OAI.MaxCutGames.Appendix.A13Index.positiveInverse`, `OAI.MaxCutGames.Appendix.A13Index.positiveMap`, `OAI.MaxCutGames.Appendix.A13Index.positiveTripleFintype`, `OAI.MaxCutGames.Appendix.A13Index.positiveWitnessFintype`, `OAI.MaxCutGames.Appendix.A13Index.size`, `OAI.MaxCutGames.Appendix.A13Index.tripleFintype`, `OAI.MaxCutGames.Appendix.A13Index.weakA`, `OAI.MaxCutGames.Appendix.A13Index.weakB`, `OAI.MaxCutGames.Appendix.A13Index.weakPositiveFintype`, `OAI.MaxCutGames.Appendix.A13Reduction.boundedPositiveTripleSum`, `OAI.MaxCutGames.Appendix.A13Reduction.positiveTripleSum`, `OAI.MaxCutGames.Appendix.A13Reduction.tripleMoment`, `OAI.MaxCutGames.Appendix.A13Reduction.tripleTerm`, `OAI.MaxCutGames.Appendix.A1Reduction.weakFourthSum`, `OAI.MaxCutGames.Appendix.A4IndexCount.Index`, `OAI.MaxCutGames.Appendix.A4IndexCount.Valid`, `OAI.MaxCutGames.Appendix.A4IndexCount.aToRange`, `OAI.MaxCutGames.Appendix.A4IndexCount.encode`, `OAI.MaxCutGames.Appendix.A4IndexCount.encodeFixed`, `OAI.MaxCutGames.Appendix.A4IndexCount.factorViaRange`, `OAI.MaxCutGames.Appendix.A4IndexCount.quotientRestriction`, `OAI.MaxCutGames.Appendix.A5ForwardIndex.Fiber`, `OAI.MaxCutGames.Appendix.A5ForwardIndex.Index`, `OAI.MaxCutGames.Appendix.A5ForwardIndex.descendant`, `OAI.MaxCutGames.Appendix.A5ForwardIndex.earlierTriple`, `OAI.MaxCutGames.Appendix.A5ForwardIndex.encode`, `OAI.MaxCutGames.Appendix.A5ForwardIndex.indexFintype`, `OAI.MaxCutGames.Appendix.A5ForwardIndex.sourceI`, `OAI.MaxCutGames.Appendix.A5ForwardIndex.sourceJ`, `OAI.MaxCutGames.Appendix.A5ForwardIndex.targetRank`, `OAI.MaxCutGames.Appendix.A5IndexCount.encode`, `OAI.MaxCutGames.Appendix.A5IndexCount.fullRange` and 327 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MaxCut_Encoding_BinaryCoordinates`, `MaxCut_Encoding_Encoding2`, `MaxCut_Encoding_FormulaEncoding`, `MaxCut_Encoding_InputEncoding`, `MaxCut_Encoding_Serialization`, `MaxCut_Encoding_ThreeBitTest`, `MaxCut_Games_A1Reduction`, `MaxCut_Games_A4IndexCount`, `MaxCut_Games_A5Induction`, `MaxCut_Games_A5ReverseIndex`, `MaxCut_Games_A5Scalar`, `MaxCut_Games_CoordinateTransport`, `MaxCut_Games_Deletion`, `MaxCut_Games_Derivatives`, `MaxCut_Games_Identities`, `MaxCut_Games_LevelInequality`, `MaxCut_Games_MatrixCharacters`, `MaxCut_Games_MatrixFourier`, `MaxCut_Games_OperatorNorm`, `MaxCut_Games_RankAdditivity`, `MaxCut_Games_Restriction`, `MaxCut_Games_SubmoduleInterval`, `MaxCut_Games_Target`, `MaxCut_Games_UpperMobius`, `MaxCut_Machines_MachineBinaryFormula`, `MaxCut_Machines_MachineBinaryNameCompare`, `MaxCut_Machines_MachineBinaryParsing`, `MaxCut_Machines_MachineBinaryRenameWords`, `MaxCut_Machines_MachineFieldTemplate`, `MaxCut_Machines_MachineHorner`, `MaxCut_Machines_MachineLookupCore`, `MaxCut_Machines_MachineSubdivisionDynamicRows`, `MaxCut_Machines_MachineUnaryMultiply`, `MaxCut_Machines_Runtime`, `MaxCut_Machines_RuntimeModel`, `MaxCut_PCP_ClauseVerifier`, `MaxCut_PCP_ContextLoad`, `MaxCut_PCP_ContextPrepare`, `MaxCut_PCP_FieldArray`, `MaxCut_PCP_Folding`, `MaxCut_PCP_HeaderAccumulate`, `MaxCut_PCP_HonestTest`, `MaxCut_PCP_Occurrences`.
--
--   **Imports.** It imports the published bundle `Def_OptimalMaxCut`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ087A007`, `OAIQ087A008`, `OAIQ087A009`, `OAIQ087A010`, `OAIQ087A011`, `OAIQ087A012` and `OAIQ087A013`; the statement `OAI.MaxCutGames.Appendix.A13Reduction.degree_reduction_truncated`.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Definitions.Def_OptimalMaxCut

section
-- module Solutions.OAIQ087_MC.Compat
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
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_BinaryCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Dimension-independent transport between the compact bit-vector coordinates of
the finite motif and the coordinate functions used by the later constructions.
The vector-space addition involved here is XOR, not modular integer addition.
-/

/-! Exact transport from XOR bit vectors to vector spaces over `ZMod 2`. -/
namespace MaxCutGames.Integration.BinaryLinear

abbrev F2 := ZMod 2

theorem scalar_cases : ∀ a : F2, a = 0 ∨ a = 1 := by decide

end MaxCutGames.Integration.BinaryLinear

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Target
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Target

structure Literal («variables» : Nat) where
  variableIndex : Fin «variables»
  positive : Bool
  deriving DecidableEq

def Literal.eval {n : Nat} (literal : Literal n) (assignment : Fin n → Bool) : Bool :=
  if literal.positive then assignment literal.variableIndex else !(assignment literal.variableIndex)

abbrev Clause («variables» : Nat) := Vector (Literal «variables») 3

def Clause.eval {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) : Bool :=
  (clause[0].eval assignment || clause[1].eval assignment) || clause[2].eval assignment

/-- A finite conjunction of clauses with exactly three literal slots each.
Repeated «variables» and repeated literals are allowed. -/
structure Formula where
  «variables» : Nat
  clauses : List (Clause «variables»)

end MaxCutGames.Foundations.Target

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_Serialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Concrete finite-alphabet serialization primitives. A natural word `n` is `n`
one-bits followed by a zero delimiter. These are size and decoding theorems, not
running-time certificates. In particular, output length is never called runtime.
-/

namespace MaxCutGames.Foundations.Complexity

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

end MaxCutGames.Foundations.Complexity

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_FormulaEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A checked parser for the concrete 3CNF serialization, including finite-index
bounds, Boolean signs, clause count, and absence of trailing garbage. -/

namespace MaxCutGames.Foundations.Complexity

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

/-! Concrete forward-table serialization of unique games. The parser reconstructs
an inverse by finite search and checks both inverse laws. Constraint occurrences,
including repeated parallel edges, are preserved in their original list order. -/

end MaxCutGames.Foundations.Complexity

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Runtime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Stack-length bounds derived from actual machine transitions. A finite program
has a maximum number of pushes in any one statement. Iterating its transitions
therefore bounds output length by input length plus that constant times elapsed
steps. This proves a consequence of a runtime certificate, not its converse.
-/

/-! Exact embedding of a finite-stack program into disjoint stacks and labels.
An original halt can either halt or enter an explicit continuation label.
The simulation preserves all extra stacks and the second state component. -/

namespace MaxCutGames.Foundations.Complexity.MachineEmbedding

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

end MaxCutGames.Foundations.Complexity.MachineEmbedding

/-!
Execution transport and polynomial budget arithmetic for genuine TM2 sequential
composition. These lemmas preserve actual transition witnesses. The four-phase
lemma requires all phases to be executions of the same combined program; it is
not a replacement for constructing that program and proving its tape handoffs.
-/

namespace MaxCutGames.Foundations.Complexity.MachineComposition

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

end MaxCutGames.Foundations.Complexity.MachineComposition

/-!
# Certified reversal and relabeling between finite alphabets

The actual TM2 machine transfers a list over a finite alphabet `α` to a second
stack over `β`, reverses its order, and applies a fixed map `f : α → β` to each
symbol. The trace has exactly `input.length + 1` transitions. An explicit
fallback symbol makes the push expression total, including the unused branch
where the internal register is empty.

This primitive supports machine composition when intermediate stack alphabets
differ. It does not yet implement the Unique Games reduction.
-/

namespace MaxCutGames.Reduction.MachineTransfer

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

/-- Exact actual-machine trace, for any accumulator and internal register. -/
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
  erw [initList_eq, haltList_eq]
  simpa only [List.append_nil] using! transfer_steps f fallback input [] none

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

def loopAt (src dst : K) (f : Γ src → Γ dst) (fallback : Γ dst)
    (loopLabel : Λ) (exit : Option Λ) : TM2.Stmt Γ Λ (σ × Option (Γ dst)) :=
  .pop src (fun state head => (state.1, head.map f))
    (.branch (fun state => state.2.isSome)
      (.push dst (fun state => state.2.getD fallback) (.goto fun _ => loopLabel))
      (exitAt dst exit))

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

end MaxCutGames.Reduction.MachineTransfer

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineFieldTemplate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.MachineFieldTemplate

open Turing
open MaxCutGames.Foundations.Complexity

variable {q : Nat} {K Λ σ : Type}

inductive Token (q : Nat)
  | literal (bits : List Bool)
  | copy (field : Fin q)
  deriving DecidableEq

end MaxCutGames.Reduction.MachineFieldTemplate

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineSubdivisionDynamicRows
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

namespace MaxCutGames.Explicit.MachineSubdivisionDynamicRows

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Target
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Reduction

def tokens (identity : List Bool) : List (MachineFieldTemplate.Token 6) :=
  [.copy 0, .copy 1, .literal identity,
   .copy 2, .copy 1, .literal identity,
   .copy 2, .copy 3, .literal identity,
   .copy 4, .copy 3, .copy 5]

@[simp] theorem tokens_length (identity : List Bool) :
    (tokens identity).length = 12 := rfl

end MaxCutGames.Explicit.MachineSubdivisionDynamicRows

/-!
One actual TM2 transition tests and decrements a zero-delimited unary counter.
The guard peeks before branching: a true bit is popped, while a false delimiter
is retained. Both branches clear the one-bit register and preserve the ambient
state. There is no assumed execution trace or input-dependent finite program.
-/

namespace MaxCutGames.Foundations.Complexity.MachineUnaryCounter

open Turing

variable {K Λ σ : Type} [DecidableEq K]

/-- An arbitrary caller frame with one tape holding the unary counter and
its unread suffix. Only this tape depends on the counter value. -/
def counterTapes (counter : K) (base : K → List Bool) (n : Nat)
    (suffix : List Bool) : K → List Bool :=
  Function.update base counter (encodeWord n ++ suffix)

@[simp] theorem counterTapes_counter (counter : K) (base : K → List Bool)
    (n : Nat) (suffix : List Bool) :
    counterTapes counter base n suffix counter = encodeWord n ++ suffix := by
  simp [counterTapes]

end MaxCutGames.Foundations.Complexity.MachineUnaryCounter

/-! Exact execution of the three input-header reads of subdivision. -/

/-! Physical header arithmetic and private-vertex initialization. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineLookupCore
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

/-!
Pure list specification for destructive zero-based unary table lookup.
These are serialization identities and bit-count bounds, not TM2 runtime
certificates. The connection to actual transitions is in `MachineLookup`.
-/
namespace MaxCutGames.Foundations.Complexity.MachineLookupSpec

@[simp] theorem decodeWords_encodeWord (i : Nat) :
    decodeWords (encodeWord i) = some [i] := by
  simpa [encodeWords] using decodeWords_encodeWords [i]

/-! Bounds on the proposed lookup recurrence. A separate machine proof must
identify these counts with actual transition traces. -/

end MaxCutGames.Foundations.Complexity.MachineLookupSpec

/-!
Execution of the destructive field-discard loop in an arbitrary ambient TM2
program. The scanner consumes a unary payload and its delimiter, preserves the
ambient state and other tapes, and clears its head register on return. At EOF it
returns immediately, leaving the tapes unchanged.
-/

/-!
Actual traces for the fixed unary lookup machine. Successful lookup preserves
an arbitrary unread table suffix. Rejection relative to a list's end is stated
only for its complete, unframed encoding, so no hidden endpoint is assumed.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_FieldArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceClauseLookup

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition

inductive Tape
  | formula | index | work | scratch | field (slot : Fin 6)
  deriving DecidableEq, Fintype

/-- Normal form for the changing counter and consumed work-copy prefix. -/
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

end MaxCutGames.Foundations.Hastad.SourceClauseLookup

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ContextLoad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A shared-arena context loader. Its finite program copies each selected
clause index, executes the checked lookup, and clears consumed scratch tapes.
Tuple digits and arbitrary extra tapes are protected throughout. -/

namespace MaxCutGames.Foundations.Hastad.SourceContextLoad

open Turing MaxCutGames.Foundations.Complexity
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

end MaxCutGames.Foundations.Hastad.SourceContextLoad

/-! Real Walsh analysis on finite Boolean cubes. The basis and inversion
identities are proved from the explicit coordinate characters. -/

noncomputable section

namespace MaxCutGames.Foundations.Hastad

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

end MaxCutGames.Foundations.Hastad
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_ThreeBitTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MaxCutGames.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- The third queried Boolean table is `g * (f ∘ π) * μ` in sign notation. -/
def thirdQuery (π : J → I) (f : Cube I) (g μ : Cube J) : Cube J :=
  cubeXor g (cubeXor (fun y => f (π y)) μ)

end MaxCutGames.Foundations.Hastad
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_Folding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit half-table storage, odd folding, and conditioning on the finite
set of satisfying local assignments for Håstad's test. -/

noncomputable section

namespace MaxCutGames.Foundations.Hastad

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

end MaxCutGames.Foundations.Hastad
end

namespace MaxCutGames.Reduction.CloneGap

variable {α β : Type*}

structure Equation (Name : Type) where
  first : Name
  second : Name
  third : Name
  rhs : Bool

end MaxCutGames.Reduction.CloneGap

namespace MaxCutGames.Foundations.Hastad.FoldedEquation

open MaxCutGames.Reduction.CloneGap
open scoped BigOperators

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Left and right stored tables have disjoint variable names. -/
abbrev Address (i₀ : I) (j₀ : J) := HalfCube i₀ ⊕ HalfCube j₀

/-- Cancellation of the two copies of `g j₀` leaves this explicit RHS. -/
def rhsCorrection (π : J → I) (i₀ : I) (j₀ : J)
    (f : Cube I) (μ : Cube J) : Bool := f i₀ ^^ f (π j₀) ^^ μ j₀

/-- One sampled test becomes exactly one three-occurrence equation. -/
def equation (π : J → I) (i₀ : I) (j₀ : J)
    (f : Cube I) (g μ : Cube J) : Equation (Address i₀ j₀) where
  first := .inl (canonicalInput i₀ f)
  second := .inr (canonicalInput j₀ g)
  third := .inr (canonicalInput j₀ (thirdQuery π f g μ))
  rhs := rhsCorrection π i₀ j₀ f μ

end MaxCutGames.Foundations.Hastad.FoldedEquation

/-!
Actual equations for clause contexts having no valid local assignment. The
right answer is the constant false bit, represented by two occurrences of one
dummy variable. Those occurrences cancel for every assignment. The remaining
left answer is folded, so its uniform bias is exactly zero.
-/

namespace MaxCutGames.Foundations.Hastad

open MaxCutGames.Reduction.CloneGap
open scoped BigOperators

namespace EmptyContext

variable {I : Type} [Fintype I] [DecidableEq I]

/-- A left half-table address or the one dummy address. -/
abbrev Address (i₀ : I) := HalfCube i₀ ⊕ Unit

/-- The dummy appears twice. Its assigned bit cancels in the equation. -/
def equation (i₀ : I) (f : Cube I) : Equation (Address i₀) where
  first := .inl (canonicalInput i₀ f)
  second := .inr ()
  third := .inr ()
  rhs := f i₀

omit [Fintype I] [DecidableEq I] in
@[simp] theorem equation_second_eq_third (i₀ : I) (f : Cube I) :
    (equation i₀ f).second = (equation i₀ f).third := rfl

end EmptyContext
end MaxCutGames.Foundations.Hastad

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_Encoding2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An occurrence-preserving E3LIN table codec. The word stream contains its
declared variable count and equation count, followed by four words per equation.
Parsing checks all three indices, the Boolean right-hand side, the exact count,
absence of trailing words, and nonemptiness. Length theorems below concern the
actual serialized output; they make no running-time claim. -/

namespace MaxCutGames.Reduction.SourceEncoding

open MaxCutGames.Foundations.Complexity

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

end MaxCutGames.Reduction.SourceEncoding

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_InputEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.BinaryFormula

/-- An ordinary conjunction of three-slot clauses with sparse variable names.
Repeated names and repeated literals are permitted in every clause. -/

def clauseNames (clause : Clause) : List Nat :=
  [clause[0].name, clause[1].name, clause[2].name]

end MaxCutGames.BinaryFormula

namespace MaxCutGames.BinaryEncoding

open BinaryFormula

@[simp] theorem bitsValue_bits (n : Nat) : bitsValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bitsValue]
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      simp only [bitsValue, ih]

/-- Prefix-free framing on the two-symbol input alphabet. -/

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

/-- Equality with the canonical digits rejects alternate padded encodings. -/

@[simp] theorem parseName_encoded (name : Nat) (rest : List Bool) :
    parseName (nameBits name ++ rest) = some (name, rest) := by
  simp [parseName, nameBits]

@[simp] theorem nameBits_length (name : Nat) :
    (nameBits name).length = 2 * name.size + 1 := by
  simp [nameBits, Nat.size_eq_bits_len]

def literalBits (literal : Literal) : List Bool :=
  literal.positive :: nameBits literal.name

@[simp] theorem parseLiteral_encoded (literal : Literal) (rest : List Bool) :
    parseLiteral (literalBits literal ++ rest) = some (literal, rest) := by
  cases literal with
  | mk name sign => simp [literalBits, parseLiteral]

@[simp] theorem literalBits_length (literal : Literal) :
    (literalBits literal).length = 2 * literal.name.size + 2 := by
  simp [literalBits]

def clauseBits (clause : Clause) : List Bool :=
  literalBits clause[0] ++ literalBits clause[1] ++ literalBits clause[2]

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

theorem formulaBits_length (formula : Formula) :
    (formulaBits formula).length =
      7 * formula.clauses.length + 2 * namesBitSize formula.clauses + 1 :=
  clausesBits_length formula.clauses

theorem clauses_length_lt_bits (clauses : List Clause) :
    clauses.length < (clausesBits clauses).length := by
  rw [clausesBits_length]
  omega

/-- Fuel bounds the number of clause iterations, not the size of any name. -/

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

@[simp] theorem decodeFormula_encoded (formula : Formula) :
    decodeFormula (formulaBits formula) = some formula := by
  cases formula with
  | mk clauses =>
      have hlen := clauses_length_lt_bits clauses
      have parsed := parseClauses_encoded clauses [] ((clausesBits clauses).length + 1) (by omega)
      simp only [List.append_nil] at parsed
      simp [formulaBits, decodeFormula, parsed]

end MaxCutGames.BinaryEncoding

/- The ordinary binary 3SAT language, including rejection of malformed words,
is exactly `MaxCutGames.BinaryLanguage.language`. -/

/- A finite simple unweighted graph with its full Boolean adjacency table.
Symmetry and the zero diagonal forbid directed edges, loops and repetitions.
No real/rational edge weights occur. -/

/- Each unordered distinct edge crossing the cut is counted exactly once. -/

/- An actual finite maximum, not a supremum over a relaxed cut domain. -/

/- A full binary output encoding: canonical delimited binary size, canonical
delimited binary Q, followed by the complete n-by-n Boolean adjacency table,
in lexicographic order. Thus neither Q nor adjacency is an oracle. -/

/- The target asserts a reduction, rather than a conditional implication from
an assumed reduction. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Fourier.MatrixRestrictions

open MaxCutGames.Integration.BinaryLinear
open scoped BigOperators

variable {E C : Type*} [AddCommGroup E] [Module F2 E]
    [AddCommGroup C] [Module F2 C]

abbrev Parameter (W : Submodule F2 E)
    (C' : Submodule F2 C) := (E ⧸ W) →ₗ[F2] C'

/-- The canonical inclusion of `L(E/W,C')` into `L(E,C)`. -/
def embed (W : Submodule F2 E)
    (C' : Submodule F2 C) (A : Parameter W C') : (E →ₗ[F2] C) :=
  C'.subtype.comp (A.comp W.mkQ)

@[simp] theorem embed_apply (W : Submodule F2 E)
    (C' : Submodule F2 C) (A : Parameter W C') (x : E) :
    embed W C' A x = (A (W.mkQ x) : C) := rfl

def translate (W : Submodule F2 E)
    (C' : Submodule F2 C) (X : (E →ₗ[F2] C))
    (A : Parameter W C') : (E →ₗ[F2] C) := X + embed W C' A

/-- The perturbation inclusion is itself a binary linear map. -/
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

/-- Restrict a real observable to the actual affine quotient-map domain. -/
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

end MaxCutGames.Fourier.MatrixRestrictions

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_MatrixCharacters
attribute [-instance] _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace characters on actual finite binary matrix spaces. -/

noncomputable section

namespace MaxCutGames.Fourier.MatrixCharacters

open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear

abbrev F2 := MaxCutGames.Integration.BinaryLinear.F2

/-- The binary trace pairing between oppositely oriented matrices. -/
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

/-- The unique nontrivial complex-valued character of the binary field. -/
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

/-- A binary linear functional determines a complex additive character. -/
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

/-- The basis-independent trace pairing in the statement of Lemma 2.1. -/
def linearTracePair (X : E →ₗ[F2] F) (S : F →ₗ[F2] E) : F2 :=
  LinearMap.trace F2 F (X.comp S)

@[simp] theorem linearTracePair_zero_left (S : F →ₗ[F2] E) :
    linearTracePair (0 : E →ₗ[F2] F) S = 0 := by simp [linearTracePair]

@[simp] theorem linearTracePair_zero_right (X : E →ₗ[F2] F) :
    linearTracePair X (0 : F →ₗ[F2] E) = 0 := by simp [linearTracePair]

theorem linearTracePair_add_left (X Y : E →ₗ[F2] F) (S : F →ₗ[F2] E) :
    linearTracePair (X + Y) S = linearTracePair X S + linearTracePair Y S := by
  simp [linearTracePair, LinearMap.add_comp]

/-- The trace character on actual linear maps, with no choice of basis. -/
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

end MaxCutGames.Fourier.MatrixCharacters
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_MatrixFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalized Fourier analysis of finite binary linear-map spaces

The coefficient normalization is uniform expectation on the primal space. The
Parseval sum over frequencies is an unnormalized sum. The underlying complex
Fourier system is the actual trace-character family on the finite additive group.
Completeness is proved directly from character cancellation and finite sums.
-/

noncomputable section

namespace MaxCutGames.Fourier.MatrixFourier

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate
open Finset
open MaxCutGames.Fourier.MatrixCharacters

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- Real coefficient on the actual space of binary linear maps. -/
def linearCoeff (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) : ℝ :=
  𝔼 X, f X * (linearTraceCharacter S X).re

end MaxCutGames.Fourier.MatrixFourier
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_RankAdditivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rank-additive pairs of linear maps

The rank-additive selector in Appendix A.1 has a concrete geometric meaning:
the two image spaces are disjoint and the two kernels span the domain. These
lemmas apply over any field and arbitrary finite dimensions, in particular
over `ZMod 2` with the second map equal to `Y + X`.
-/

namespace MaxCutGames.Appendix.RankAdditivity

open Module LinearMap

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V]

/-- Disjoint images prevent cancellation between the two map values. -/
theorem ker_add_of_disjoint (f g : W →ₗ[K] V)
    (h : Disjoint (LinearMap.range f) (LinearMap.range g)) :
    LinearMap.ker (f + g) = LinearMap.ker f ⊓ LinearMap.ker g := by
  ext w
  constructor
  · intro hw
    have hsum : f w + g w = 0 := hw
    have hf : f w = 0 := by
      apply Submodule.disjoint_def.mp h (f w)
      · exact ⟨w, rfl⟩
      · exact ⟨-w, by simpa only [map_neg] using (eq_neg_of_add_eq_zero_left hsum).symm⟩
    have hg : g w = 0 := by simpa only [hf, zero_add] using hsum
    exact ⟨hf, hg⟩
  · rintro ⟨hf, hg⟩
    change f w + g w = 0
    change f w = 0 at hf
    change g w = 0 at hg
    rw [hf, hg, add_zero]

variable [FiniteDimensional K W] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
/-- The exact rank-additivity criterion used to define `X ⪯ Y` in Appendix A.1. -/
theorem finrank_add_eq_iff (f g : W →ₗ[K] V) :
    finrank K (LinearMap.range (f + g)) =
        finrank K (LinearMap.range f) + finrank K (LinearMap.range g) ↔
      Disjoint (LinearMap.range f) (LinearMap.range g) ∧
        LinearMap.ker f ⊔ LinearMap.ker g = ⊤ := by
  have hf := f.finrank_range_add_finrank_ker
  have hg := g.finrank_range_add_finrank_ker
  have hfg := (f + g).finrank_range_add_finrank_ker
  have hker := (LinearMap.ker f).finrank_sup_add_finrank_inf_eq (LinearMap.ker g)
  constructor
  · intro hrank
    have hle := Submodule.finrank_mono (LinearMap.range_add_le f g)
    have himage := (LinearMap.range f).finrank_sup_add_finrank_inf_eq (LinearMap.range g)
    have hinf : finrank K (LinearMap.range f ⊓ LinearMap.range g : Submodule K V) = 0 := by
      omega
    have hd : Disjoint (LinearMap.range f) (LinearMap.range g) := by
      exact disjoint_iff.mpr (Submodule.finrank_eq_zero.mp hinf)
    refine ⟨hd, ?_⟩
    have heq := ker_add_of_disjoint f g hd
    rw [heq] at hfg
    apply Submodule.eq_top_of_finrank_eq
    omega
  · rintro ⟨hd, htop⟩
    rw [ker_add_of_disjoint f g hd] at hfg
    rw [htop, finrank_top] at hker
    omega

omit [FiniteDimensional K V] in
/-- The left image is contained in the total image for a rank-additive pair. -/
theorem range_left_le_range_add (f g : W →ₗ[K] V)
    (h : finrank K (LinearMap.range (f + g)) =
      finrank K (LinearMap.range f) + finrank K (LinearMap.range g)) :
    LinearMap.range f ≤ LinearMap.range (f + g) := by
  have hk := ((finrank_add_eq_iff f g).mp h).2
  intro v hv
  have hp : (v, (0 : V)) ∈ (LinearMap.range f).prod (LinearMap.range g) :=
    ⟨hv, Submodule.zero_mem _⟩
  rw [← LinearMap.range_prod_eq hk] at hp
  rcases hp with ⟨w, hw⟩
  have hwf : f w = v := congrArg Prod.fst hw
  have hwg : g w = 0 := congrArg Prod.snd hw
  refine ⟨w, ?_⟩
  change f w + g w = v
  rw [hwf, hwg, add_zero]

omit [FiniteDimensional K V] in
/-- The total kernel is contained in the left kernel for a rank-additive pair. -/
theorem ker_add_le_ker_left (f g : W →ₗ[K] V)
    (h : finrank K (LinearMap.range (f + g)) =
      finrank K (LinearMap.range f) + finrank K (LinearMap.range g)) :
    LinearMap.ker (f + g) ≤ LinearMap.ker f := by
  rw [ker_add_of_disjoint f g ((finrank_add_eq_iff f g).mp h).1]
  exact inf_le_left

def RankBelow (X Y : W →ₗ[K] V) : Prop :=
  finrank K (LinearMap.range Y) =
    finrank K (LinearMap.range X) + finrank K (LinearMap.range (Y - X))

omit [FiniteDimensional K W] [FiniteDimensional K V] in
theorem add_remainder (X Y : W →ₗ[K] V) : X + (Y - X) = Y := by
  rw [add_comm X, sub_add_cancel]

omit [FiniteDimensional K V] in
theorem range_le_of_rankBelow (X Y : W →ₗ[K] V) (h : RankBelow X Y) :
    LinearMap.range X ≤ LinearMap.range Y := by
  have h' : finrank K (LinearMap.range (X + (Y - X))) =
      finrank K (LinearMap.range X) + finrank K (LinearMap.range (Y - X)) := by
    rw [add_remainder]
    exact h
  simpa only [add_remainder] using range_left_le_range_add X (Y - X) h'

omit [FiniteDimensional K V] in
theorem ker_le_of_rankBelow (X Y : W →ₗ[K] V) (h : RankBelow X Y) :
    LinearMap.ker Y ≤ LinearMap.ker X := by
  have h' : finrank K (LinearMap.range (X + (Y - X))) =
      finrank K (LinearMap.range X) + finrank K (LinearMap.range (Y - X)) := by
    rw [add_remainder]
    exact h
  simpa only [add_remainder] using ker_add_le_ker_left X (Y - X) h'

end MaxCutGames.Appendix.RankAdditivity

namespace MaxCutGames.Appendix.CompressionCount

open Module
open MaxCutGames.Integration.BinaryLinear (F2)

universe u v w

variable (U : Type u) (K : Type v) (C : Type w)
variable [AddCommGroup U] [Module F2 U]
variable [AddCommGroup K] [Module F2 K]
variable [AddCommGroup C] [Module F2 C]

/-- Canonical rank-`dim U` map. -/
def base : (U × K) →ₗ[F2] (U × C) :=
  (LinearMap.inl F2 U C).comp (LinearMap.fst F2 U K)

@[simp] theorem base_apply (p : U × K) : base U K C p = (p.1, 0) := rfl

variable {U K C}

/-- Compress by restricting to the second domain factor and taking the second
codomain coordinate. -/
def compress (Y : (U × K) →ₗ[F2] (U × C)) : K →ₗ[F2] C :=
  (LinearMap.snd F2 U C).comp (Y.comp (LinearMap.inr F2 U K))

@[simp] theorem compress_apply (Y : (U × K) →ₗ[F2] (U × C)) (k : K) :
    compress Y k = (Y (0, k)).2 := rfl

/-- The actual rank-order compression fiber; subtraction agrees with addition
over the binary field. -/
def Fiber (Z : K →ₗ[F2] C) :=
  {Y : (U × K) →ₗ[F2] (U × C) //
    finrank F2 Y.range = finrank F2 U + finrank F2 (Y - base U K C).range ∧
      compress Y = Z}

abbrev Parameters (Z : K →ₗ[F2] C) :=
  (Z.range →ₗ[F2] U) × (U →ₗ[F2] Z.range)

def graph (Z : K →ₗ[F2] C) (F : Z.range →ₗ[F2] U) :
    Z.range →ₗ[F2] (U × C) := F.prod Z.range.subtype

def inclusion (Z : K →ₗ[F2] C) : (U × Z.range) →ₗ[F2] (U × C) :=
  (LinearMap.id : U →ₗ[F2] U).prodMap Z.range.subtype

def lower (Z : K →ₗ[F2] C) (H : U →ₗ[F2] Z.range) :
    (U × K) →ₗ[F2] Z.range := H.coprod Z.rangeRestrict

/-- The block matrix `[I+FH,FZ;H,Z]`. -/
def lift (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) :
    (U × K) →ₗ[F2] (U × C) :=
  base U K C + (graph Z P.1).comp (lower Z P.2)

@[simp] theorem lift_apply (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z)
    (p : U × K) :
    lift Z P p = (p.1 + P.1 (P.2 p.1 + Z.rangeRestrict p.2),
      ((P.2 p.1 : Z.range) : C) + Z p.2) := by
  simp [lift, graph, lower]

@[simp] theorem compress_lift (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) :
    compress (lift Z P) = Z := by
  ext k
  simp

theorem graph_injective (Z : K →ₗ[F2] C) (F : Z.range →ₗ[F2] U) :
    Function.Injective (graph Z F) := by
  intro a b h
  exact Subtype.ext (congrArg Prod.snd h)

theorem inclusion_injective (Z : K →ₗ[F2] C) :
    Function.Injective (inclusion (U := U) Z) := by
  intro a b h
  exact Prod.ext (by simpa [inclusion] using congrArg Prod.fst h)
    (Subtype.ext (by simpa [inclusion] using congrArg Prod.snd h))

theorem lower_surjective (Z : K →ₗ[F2] C) (H : U →ₗ[F2] Z.range) :
    Function.Surjective (lower Z H) := by
  intro c
  obtain ⟨k, hk⟩ := Z.surjective_rangeRestrict c
  refine ⟨(0, k), ?_⟩
  simpa [lower] using hk

theorem range_lift_sub_base (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) :
    (lift Z P - base U K C).range = (graph Z P.1).range := by
  rw [lift, add_sub_cancel_left]
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (lower_surjective Z P.2))

theorem range_lift (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) :
    (lift Z P).range = (inclusion (U := U) Z).range := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    refine ⟨(p.1 + P.1 (P.2 p.1 + Z.rangeRestrict p.2),
      P.2 p.1 + Z.rangeRestrict p.2), ?_⟩
    simp [inclusion]
  · rintro _ ⟨⟨u, c⟩, rfl⟩
    obtain ⟨k, hk⟩ := Z.surjective_rangeRestrict (c - P.2 (u - P.1 c))
    refine ⟨(u - P.1 c, k), ?_⟩
    have hc : P.2 (u - P.1 c) + Z.rangeRestrict k = c := by rw [hk]; abel
    apply Prod.ext
    · change u - P.1 c + P.1 (P.2 (u - P.1 c) + Z.rangeRestrict k) = u
      rw [hc]
      abel
    · simpa [inclusion] using congrArg Subtype.val hc

variable [FiniteDimensional F2 U] [FiniteDimensional F2 K] [FiniteDimensional F2 C]

omit [FiniteDimensional F2 U] [FiniteDimensional F2 K] [FiniteDimensional F2 C] in
theorem finrank_base : finrank F2 (base U K C).range = finrank F2 U := by
  rw [base, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr LinearMap.fst_surjective)]
  exact LinearMap.finrank_range_of_inj LinearMap.inl_injective

omit [FiniteDimensional F2 C] in
theorem lift_rank_order (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) :
    finrank F2 (lift Z P).range =
      finrank F2 U + finrank F2 (lift Z P - base U K C).range := by
  rw [range_lift, range_lift_sub_base,
    LinearMap.finrank_range_of_inj (inclusion_injective (U := U) Z),
    LinearMap.finrank_range_of_inj (graph_injective Z P.1), Module.finrank_prod]

def toFiber (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) : Fiber (U := U) Z :=
  ⟨lift Z P, lift_rank_order Z P, compress_lift Z P⟩

omit [FiniteDimensional F2 U] [FiniteDimensional F2 K] [FiniteDimensional F2 C] in
theorem lift_injective (Z : K →ₗ[F2] C) :
    Function.Injective (lift (U := U) Z) := by
  rintro ⟨F, H⟩ ⟨G, J⟩ h
  have hH : H = J := by
    ext u
    have he := congrArg (fun f => (f (u, 0)).2) h
    simpa using he
  have hF : F = G := by
    ext c
    obtain ⟨k, hk⟩ := Z.surjective_rangeRestrict c
    have he := congrArg (fun f => (f (0, k)).1) h
    simpa [hk] using he
  exact Prod.ext hF hH

omit [FiniteDimensional F2 C] in
/-- Rank additivity supplies exactly the image/kernel hypotheses used by the
block argument. -/
theorem fiber_geometry (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    Disjoint (base U K C).range (Y.val - base U K C).range ∧
      (base U K C).ker ⊔ (Y.val - base U K C).ker = ⊤ := by
  apply (RankAdditivity.finrank_add_eq_iff (base U K C) (Y.val - base U K C)).mp
  have heq : base U K C + (Y.val - base U K C) = Y.val := by abel
  rw [heq, finrank_base]
  exact Y.property.1

omit [FiniteDimensional F2 C] in
/-- Every lower coordinate of a map in the fiber lies in the compressed image.
This is the step that permits taking `H : U → range Z`. -/
theorem snd_mem_range (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) (p : U × K) :
    (Y.val p).2 ∈ Z.range := by
  have hp : p ∈ (base U K C).ker ⊔ (Y.val - base U K C).ker := by
    rw [(fiber_geometry Z Y).2]
    trivial
  rcases Submodule.mem_sup.mp hp with ⟨a, ha, b, hb, hab⟩
  have ha0 : a.1 = 0 := congrArg Prod.fst ha
  have haeq : a = (0, a.2) := Prod.ext ha0 rfl
  have hDb : Y.val b = base U K C b := sub_eq_zero.mp hb
  refine ⟨a.2, ?_⟩
  have hcomp := LinearMap.congr_fun Y.property.2 a.2
  calc
    Z a.2 = (Y.val (0, a.2)).2 := hcomp.symm
    _ = (Y.val a).2 := congrArg (fun q => (Y.val q).2) haeq.symm
    _ = (Y.val (a + b)).2 := by simp [map_add, hDb]
    _ = (Y.val p).2 := congrArg (fun q => (Y.val q).2) hab

/-- Choose a linear section of the map onto its image. -/
noncomputable def linearSection (Z : K →ₗ[F2] C) : Z.range →ₗ[F2] K :=
  Classical.choose
    (Z.rangeRestrict.exists_rightInverse_of_surjective Z.range_rangeRestrict)

omit [FiniteDimensional F2 C] in
theorem section_spec (Z : K →ₗ[F2] C) (c : Z.range) :
    Z.rangeRestrict (linearSection Z c) = c :=
  LinearMap.congr_fun (Classical.choose_spec
    (Z.rangeRestrict.exists_rightInverse_of_surjective Z.range_rangeRestrict)) c

noncomputable def extractedF (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    Z.range →ₗ[F2] U :=
  (LinearMap.fst F2 U C).comp
    (Y.val.comp ((LinearMap.inr F2 U K).comp (linearSection Z)))

def extractedH (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    U →ₗ[F2] Z.range :=
  ((LinearMap.snd F2 U C).comp (Y.val.comp (LinearMap.inl F2 U K))).codRestrict
    Z.range (fun u => snd_mem_range Z Y (u, 0))

omit [FiniteDimensional F2 C] in
theorem extracted_lower (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) (p : U × K) :
    extractedH Z Y p.1 + Z.rangeRestrict p.2 =
      ⟨(Y.val p).2, snd_mem_range Z Y p⟩ := by
  apply Subtype.ext
  change (Y.val (p.1, 0)).2 + Z p.2 = (Y.val p).2
  rw [← LinearMap.congr_fun Y.property.2 p.2]
  change (Y.val (p.1, 0)).2 + (Y.val (0, p.2)).2 = (Y.val p).2
  rw [← Prod.snd_add, ← map_add]
  simp

omit [FiniteDimensional F2 C] in
/-- On the difference image, the lower coordinate uniquely determines the
upper coordinate. -/
theorem difference_ext_snd (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z)
    (p q : U × K) (h : (Y.val p).2 = (Y.val q).2) :
    (Y.val - base U K C) p = (Y.val - base U K C) q := by
  let D := Y.val - base U K C
  have hbottom : (D (p - q)).2 = 0 := by
    change ((Y.val - base U K C) (p - q)).2 = 0
    simp only [LinearMap.sub_apply, map_sub, Prod.snd_sub, base_apply]
    simpa using sub_eq_zero.mpr h
  have hzero : D (p - q) = 0 := by
    apply Submodule.disjoint_def.mp (fiber_geometry Z Y).1 (D (p - q))
    · refine ⟨((D (p - q)).1, 0), ?_⟩
      exact Prod.ext rfl hbottom.symm
    · exact ⟨p - q, rfl⟩
  exact sub_eq_zero.mp (by simpa only [map_sub] using hzero)

omit [FiniteDimensional F2 C] in
theorem lift_extracted (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    lift Z (extractedF Z Y, extractedH Z Y) = Y.val := by
  apply LinearMap.ext
  intro p
  let c : Z.range := ⟨(Y.val p).2, snd_mem_range Z Y p⟩
  have hq : (Y.val (0, linearSection Z c)).2 = (Y.val p).2 := by
    calc
      (Y.val (0, linearSection Z c)).2 = Z (linearSection Z c) :=
        LinearMap.congr_fun Y.property.2 (linearSection Z c)
      _ = (c : C) := congrArg Subtype.val (section_spec Z c)
      _ = (Y.val p).2 := rfl
  have hd := congrArg Prod.fst (difference_ext_snd Z Y p (0, linearSection Z c) hq.symm)
  change (Y.val p).1 - p.1 = (Y.val (0, linearSection Z c)).1 - 0 at hd
  apply Prod.ext
  · change p.1 + extractedF Z Y
      (extractedH Z Y p.1 + Z.rangeRestrict p.2) = (Y.val p).1
    rw [extracted_lower]
    change p.1 + (Y.val (0, linearSection Z c)).1 = (Y.val p).1
    rw [sub_zero] at hd
    rw [← hd]
    abel
  · simpa using congrArg Subtype.val (extracted_lower Z Y p)

omit [FiniteDimensional F2 C] in
theorem toFiber_bijective (Z : K →ₗ[F2] C) :
    Function.Bijective (toFiber (U := U) Z) := by
  constructor
  · intro P Q h
    exact lift_injective Z (congrArg Subtype.val h)
  · intro Y
    exact ⟨(extractedF Z Y, extractedH Z Y), Subtype.ext (lift_extracted Z Y)⟩

/-- The exact compression fiber is in bijection with two independent spaces of
linear maps. No rank or cardinality claim is an assumption of this equivalence. -/
noncomputable def fiberEquiv (Z : K →ₗ[F2] C) :
    Parameters (U := U) Z ≃ Fiber (U := U) Z :=
  Equiv.ofBijective (toFiber Z) (toFiber_bijective Z)

end MaxCutGames.Appendix.CompressionCount

/-! Actual subspace cardinality bounds used in (5.12)--(5.13).

Every subspace is the image of a projection endomorphism. Thus the set of all
subspaces is a quotient of the endomorphism space. The exact finite-field
linear-map count is reused from `Appendix.CompressionCount`.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Restriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MaxCutGames.Appendix.Restriction

open scoped BigOperators
open MaxCutGames.Fourier.MatrixCharacters MaxCutGames.Fourier.MatrixFourier
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

/-- The actual quotient-and-restriction map on Fourier indices in (A.1). -/
def compressFrequency (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) : B →ₗ[F2] (E ⧸ A) :=
  A.mkQ.comp (Y.comp B.subtype)

end MaxCutGames.Appendix.Restriction
end

section

namespace MaxCutGames.Appendix.Level.LinearRank

open Module LinearMap
attribute [local instance] Classical.propDecidable

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V] [FiniteDimensional K W] [FiniteDimensional K V]

/-- Restriction in the domain and quotient in the codomain, as actual
linear maps. This is the Fourier-frequency map of an affine restriction. -/
def compress (A : Submodule K V) (B : Submodule K W) (Y : W →ₗ[K] V) :
    B →ₗ[K] V ⧸ A := A.mkQ.comp (Y.comp B.subtype)

end MaxCutGames.Appendix.Level.LinearRank
end

/-! The arbitrary-dimensional linear-algebra cover in Appendix A.1. -/
namespace MaxCutGames.Appendix.DegreeCover

abbrev F2 := ZMod 2
variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V]

@[simp] theorem binary_add_self (v : V) : v + v = 0 := by
  have h : (1 + 1 : F2) = 0 := by decide
  simpa only [add_smul, one_smul, zero_smul] using congrArg (fun c : F2 => c • v) h

@[simp] theorem binary_neg (v : V) : -v = v := by
  apply neg_eq_iff_add_eq_zero.mpr
  exact binary_add_self v

end MaxCutGames.Appendix.DegreeCover

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Identities
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Appendix.LinearIdentities

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V]

/-- The actual hybrid selector from Appendix A.1, for genuine linear maps. -/
def Hybrid (Y : W →ₗ[K] V) (A : Submodule K V) (B : Submodule K W) : Prop :=
  A ≤ LinearMap.range Y ∧ A.comap Y ≤ B

/-- The compressed dual frequency `Q_A Y|_B`. -/
def compress (Y : W →ₗ[K] V) (A : Submodule K V) (B : Submodule K W) :
    B →ₗ[K] (V ⧸ A) := A.mkQ.comp (Y.domRestrict B)

@[simp] theorem compress_apply (Y : W →ₗ[K] V) (A : Submodule K V)
    (B : Submodule K W) (b : B) : compress Y A B b = A.mkQ (Y b) := rfl

variable [FiniteDimensional K W] [FiniteDimensional K V]

/-- The precise right-hand pair selector of (A.5). -/
def A5PairSurvives (X Y : W →ₗ[K] V) (A : Submodule K V) (B : Submodule K W)
    (p : Submodule K V × Submodule K W) : Prop :=
  Hybrid Y p.1 p.2 ∧ Disjoint p.1 (LinearMap.range X) ∧
  p.1 ⊔ LinearMap.range X = A ∧ p.2 ⊔ LinearMap.ker X = ⊤ ∧
  p.2 ⊓ LinearMap.ker X = B ∧
  RankAdditivity.RankBelow (compress X p.1 p.2) (compress Y p.1 p.2)

/-! ## The unique selector in (A.4) -/

abbrev A4Index := Σ A₀ : Submodule K V, Σ B₀ : Submodule K W, B₀ →ₗ[K] (V ⧸ A₀)

/-- The full index and selectors of a right-hand summand of (A.4). -/
def A4Survives (Y : W →ₗ[K] V) (A : Submodule K V) (B : Submodule K W)
    (p : A4Index (K := K) (W := W) (V := V)) : Prop :=
  p.1 ≤ A ∧ B ≤ p.2.1 ∧ Hybrid Y p.1 p.2.1 ∧
    LinearMap.ker p.2.2 = B.comap p.2.1.subtype ∧
    LinearMap.range p.2.2 = A.map p.1.mkQ ∧
    RankAdditivity.RankBelow p.2.2 (compress Y p.1 p.2.1)

end MaxCutGames.Appendix.LinearIdentities

namespace MaxCutGames.Appendix.BinaryA4

open LinearIdentities

abbrev F2 := DegreeCover.F2

end MaxCutGames.Appendix.BinaryA4

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_CoordinateTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MaxCutGames.Appendix.CoordinateTransport

variable {𝕜 E F : Type*} [Field 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/-- A complement to the kernel maps isomorphically onto the range. -/
def complementRangeEquiv (X : E →ₗ[𝕜] F) (P : Submodule 𝕜 E)
    (hP : IsCompl X.ker P) : P ≃ₗ[𝕜] X.range :=
  (X.ker.quotientEquivOfIsCompl P hP).symm.trans X.quotKerEquivRange

@[simp] theorem complementRangeEquiv_apply (X : E →ₗ[𝕜] F)
    (P : Submodule 𝕜 E) (hP : IsCompl X.ker P) (p : P) :
    (complementRangeEquiv X P hP p : F) = X p := by
  rfl

/-- Domain coordinates, with the first coordinate literally in `range X`. -/
def domainEquiv (X : E →ₗ[𝕜] F) (P : Submodule 𝕜 E)
    (hP : IsCompl X.ker P) : (X.range × X.ker) ≃ₗ[𝕜] E :=
  (LinearEquiv.prodCongr (complementRangeEquiv X P hP).symm
    (LinearEquiv.refl 𝕜 X.ker)).trans (P.prodEquivOfIsCompl X.ker hP.symm)

/-- The domain equivalence exhibits precisely the image coordinate of X. -/
@[simp] theorem apply_domainEquiv (X : E →ₗ[𝕜] F)
    (P : Submodule 𝕜 E) (hP : IsCompl X.ker P) (u : X.range) (k : X.ker) :
    X (domainEquiv X P hP (u, k)) = (u : F) := by
  change X ((complementRangeEquiv X P hP).symm u + (k : E)) = (u : F)
  rw [map_add, show X (k : E) = 0 from k.property, add_zero]
  have h := congrArg (fun v : X.range => (v : F))
    ((complementRangeEquiv X P hP).apply_symm_apply u)
  simpa only [complementRangeEquiv_apply] using h

/-- Codomain coordinates split the range off from a chosen complement. -/
def codomainEquiv (X : E →ₗ[𝕜] F) (C : Submodule 𝕜 F)
    (hC : IsCompl X.range C) : (X.range × C) ≃ₗ[𝕜] F :=
  X.range.prodEquivOfIsCompl C hC

/-- An arbitrary map has the canonical compression-fiber block form. -/
theorem canonical_block (X : E →ₗ[𝕜] F) (P : Submodule 𝕜 E)
    (hP : IsCompl X.ker P) (C : Submodule 𝕜 F)
    (hC : IsCompl X.range C) (u : X.range) (k : X.ker) :
    (codomainEquiv X C hC).symm (X (domainEquiv X P hP (u, k))) = (u, 0) := by
  rw [apply_domainEquiv]
  exact Submodule.prodEquivOfIsCompl_symm_apply_left X.range C hC u

@[simp] theorem domainEquiv_zero_left (X : E →ₗ[𝕜] F)
    (P : Submodule 𝕜 E) (hP : IsCompl X.ker P) (k : X.ker) :
    domainEquiv X P hP (0, k) = (k : E) := by
  change ((complementRangeEquiv X P hP).symm 0 : E) + (k : E) = (k : E)
  simp

theorem quotient_coordinates (X : E →ₗ[𝕜] F) (C : Submodule 𝕜 F)
    (hC : IsCompl X.range C) (v : F) :
    X.range.quotientEquivOfIsCompl C hC (X.range.mkQ v) =
      ((codomainEquiv X C hC).symm v).2 := by
  simp [codomainEquiv, Submodule.prodEquivOfIsCompl_symm_apply]

/-- Re-express all maps in the chosen domain/codomain coordinates at once. -/
def toBlocks (X : E →ₗ[𝕜] F) (P : Submodule 𝕜 E)
    (hP : IsCompl X.ker P) (C : Submodule 𝕜 F) (hC : IsCompl X.range C) :
    (E →ₗ[𝕜] F) ≃ₗ[𝕜] ((X.range × X.ker) →ₗ[𝕜] (X.range × C)) :=
  LinearEquiv.arrowCongr (domainEquiv X P hP).symm (codomainEquiv X C hC).symm

@[simp] theorem toBlocks_apply (X Y : E →ₗ[𝕜] F) (P : Submodule 𝕜 E)
    (hP : IsCompl X.ker P) (C : Submodule 𝕜 F) (hC : IsCompl X.range C)
    (u : X.range) (k : X.ker) :
    toBlocks X P hP C hC Y (u, k) =
      (codomainEquiv X C hC).symm (Y (domainEquiv X P hP (u, k))) := by
  rfl

/-- The lower-right block is exactly the original quotient restriction,
transported through the quotient/complement equivalence. -/
theorem compressed_toBlocks (X Y : E →ₗ[𝕜] F) (P : Submodule 𝕜 E)
    (hP : IsCompl X.ker P) (C : Submodule 𝕜 F) (hC : IsCompl X.range C)
    (k : X.ker) :
    (toBlocks X P hP C hC Y (0, k)).2 =
      X.range.quotientEquivOfIsCompl C hC (X.range.mkQ (Y k)) := by
  rw [toBlocks_apply, domainEquiv_zero_left, quotient_coordinates]

theorem toBlocks_base (X : E →ₗ[𝕜] F) (P : Submodule 𝕜 E)
    (hP : IsCompl X.ker P) (C : Submodule 𝕜 F) (hC : IsCompl X.range C) :
    toBlocks X P hP C hC X =
      (LinearMap.inl 𝕜 X.range C).comp (LinearMap.fst 𝕜 X.range X.ker) := by
  apply LinearMap.ext
  intro p
  exact canonical_block X P hP C hC p.1 p.2

section RankTransport

variable {U V : Type*} [AddCommGroup U] [Module 𝕜 U]
  [AddCommGroup V] [Module 𝕜 V]

/-- Changing coordinates induces a genuine linear equivalence on ranges. -/
def rangeTransport (e : E ≃ₗ[𝕜] U) (f : F ≃ₗ[𝕜] V) (Y : E →ₗ[𝕜] F) :
    Y.range ≃ₗ[𝕜] (LinearEquiv.arrowCongr e f Y).range where
  toFun y := ⟨f y, by
    obtain ⟨w, hw⟩ := y.property
    exact ⟨e w, by simp [LinearEquiv.arrowCongr_apply, hw]⟩⟩
  invFun z := ⟨f.symm z, by
    obtain ⟨u, hu⟩ := z.property
    refine ⟨e.symm u, ?_⟩
    have h := congrArg f.symm hu
    simpa only [LinearEquiv.arrowCongr_apply, LinearEquiv.symm_apply_apply] using h⟩
  left_inv y := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp
  map_add' y z := by apply Subtype.ext; simp
  map_smul' c y := by apply Subtype.ext; simp

theorem finrank_range_transport (e : E ≃ₗ[𝕜] U) (f : F ≃ₗ[𝕜] V)
    (Y : E →ₗ[𝕜] F) :
    Module.finrank 𝕜 (LinearEquiv.arrowCongr e f Y).range =
      Module.finrank 𝕜 Y.range :=
  (rangeTransport e f Y).finrank_eq.symm

end RankTransport

theorem finrank_toBlocks (X Y : E →ₗ[𝕜] F) (P : Submodule 𝕜 E)
    (hP : IsCompl X.ker P) (C : Submodule 𝕜 F) (hC : IsCompl X.range C) :
    Module.finrank 𝕜 (toBlocks X P hP C hC Y).range =
      Module.finrank 𝕜 Y.range :=
  finrank_range_transport (domainEquiv X P hP).symm (codomainEquiv X C hC).symm Y

end MaxCutGames.Appendix.CoordinateTransport

/-!
# Exact compression fibers for arbitrary binary linear maps

This is the general cardinality assertion in Lemma A.2, with the actual kernel
restriction and range quotient. The map X is arbitrary; no chosen-coordinate
or fixed-dimension hypothesis occurs in `card_fiber`.
-/

namespace MaxCutGames.Appendix.FullCompression

open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Appendix.CoordinateTransport
open Module

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]

/-- Restrict a dual map to `ker X` and then quotient by `range X`. -/
def compression (X Y : E →ₗ[F2] F) : X.ker →ₗ[F2] (F ⧸ X.range) :=
  X.range.mkQ.comp (Y.comp X.ker.subtype)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
@[simp] theorem compression_apply (X Y : E →ₗ[F2] F) (k : X.ker) :
    compression X Y k = X.range.mkQ (Y k) := rfl

/-- The genuine rank-additive compression fiber. In characteristic two,
`Y - X` and `Y + X` are equal. -/
def Fiber (X : E →ₗ[F2] F) (Z : X.ker →ₗ[F2] (F ⧸ X.range)) :=
  {Y : E →ₗ[F2] F // finrank F2 Y.range =
      finrank F2 X.range + finrank F2 (Y - X).range ∧ compression X Y = Z}

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem fiber_condition_iff (X Y : E →ₗ[F2] F)
    (Z : X.ker →ₗ[F2] (F ⧸ X.range))
    (P : Submodule F2 E) (hP : IsCompl X.ker P)
    (C : Submodule F2 F) (hC : IsCompl X.range C) :
    (finrank F2 Y.range = finrank F2 X.range + finrank F2 (Y - X).range ∧
      compression X Y = Z) ↔
    (finrank F2 (toBlocks X P hP C hC Y).range = finrank F2 X.range +
      finrank F2 (toBlocks X P hP C hC Y - CompressionCount.base X.range X.ker C).range ∧
      CompressionCount.compress (toBlocks X P hP C hC Y) =
        (X.range.quotientEquivOfIsCompl C hC).toLinearMap.comp Z) := by
  have hy := finrank_toBlocks X Y P hP C hC
  have hd := finrank_toBlocks X (Y - X) P hP C hC
  rw [map_sub, toBlocks_base] at hd
  change finrank F2 (toBlocks X P hP C hC Y - CompressionCount.base X.range X.ker C).range =
    finrank F2 (Y - X).range at hd
  rw [hy, hd]
  refine and_congr_right (fun _ => ?_)
  constructor
  · intro hz
    apply LinearMap.ext
    intro k
    change (toBlocks X P hP C hC Y (0, k)).2 =
      X.range.quotientEquivOfIsCompl C hC (Z k)
    rw [compressed_toBlocks]
    exact congrArg (X.range.quotientEquivOfIsCompl C hC)
      (DFunLike.congr_fun hz k)
  · intro hz
    apply LinearMap.ext
    intro k
    apply (X.range.quotientEquivOfIsCompl C hC).injective
    have h := DFunLike.congr_fun hz k
    change (toBlocks X P hP C hC Y (0, k)).2 =
      X.range.quotientEquivOfIsCompl C hC (Z k) at h
    rw [compressed_toBlocks] at h
    exact h

/-- Coordinate transport is a bijection on the complete rank-additive fibers. -/
def fiberEquiv (X : E →ₗ[F2] F) (Z : X.ker →ₗ[F2] (F ⧸ X.range))
    (P : Submodule F2 E) (hP : IsCompl X.ker P)
    (C : Submodule F2 F) (hC : IsCompl X.range C) :
    Fiber X Z ≃ CompressionCount.Fiber (U := X.range)
      ((X.range.quotientEquivOfIsCompl C hC).toLinearMap.comp Z) :=
  (toBlocks X P hP C hC).toEquiv.subtypeEquiv
    (fun Y => fiber_condition_iff X Y Z P hP C hC)

end MaxCutGames.Appendix.FullCompression

/-!
# Energy after merging a bounded number of frequencies

This finite ordered-ring theorem supplies the Cauchy–Schwarz step in (A.10).
Its fiber-cardinality hypothesis is explicit and remains to be instantiated by
the general rank-additive compression count of Lemma A.2.
-/

/-! Exact coefficient-energy estimate underlying (A.10), with genuine
binary linear maps, their rank-additive order and quotient compression. -/

/-!
Finite-field subspace cardinality bounds used in Appendix A.4. The objects
counted here are actual mathlib submodules, not encoded cardinality assumptions.
-/

namespace MaxCutGames.Appendix.SubspaceCounting

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V]

noncomputable def generators (S : Submodule K V) (k : ℕ)
    (h : finrank K S = k) : Fin k → V :=
  fun i => (Module.finBasisOfFinrankEq K S h i : V)

variable {U : Type*} [AddCommGroup U] [Module K U] [Module.Finite K U]

/-- Factor a map whose kernel contains `ker Y` and whose image lies in `range Y`
through the effective domain and codomain. -/
def quotientImageMap (Y X : U →ₗ[K] V)
    (hker : LinearMap.ker Y ≤ LinearMap.ker X)
    (himage : LinearMap.range X ≤ LinearMap.range Y) :
    (U ⧸ LinearMap.ker Y) →ₗ[K] LinearMap.range Y :=
  let f := (LinearMap.ker Y).liftQ X hker
  f.codRestrict (LinearMap.range Y) (fun q => himage (by
    rw [← Submodule.range_liftQ (LinearMap.ker Y) X hker]
    exact LinearMap.mem_range_self f q))

omit [Module.Finite K V] [Module.Finite K U] in
@[simp] theorem quotientImageMap_mk (Y X : U →ₗ[K] V)
    (hker : LinearMap.ker Y ≤ LinearMap.ker X)
    (himage : LinearMap.range X ≤ LinearMap.range Y) (u : U) :
    (quotientImageMap Y X hker himage ((LinearMap.ker Y).mkQ u) : V) = X u := rfl

end MaxCutGames.Appendix.SubspaceCounting

/-!
The corrected weighted fourth coefficient-energy estimate of Appendix A.4.
The proof uses the actual compression-fiber energy theorem and the actual
rank-additive predecessor count, not hypotheses replacing either result.
The remaining Fourier interpretation is separate: `energy a X` is the sum of
squares of coefficients after the actual derivative compression.
-/

namespace MaxCutGames.Appendix.WeightedFourthMoment

open Module
open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Appendix.RankAdditivity (RankBelow)
attribute [local instance] Classical.propDecidable

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)]

abbrev rank (X : E →ₗ[F2] F) : ℕ := finrank F2 X.range

@[instance_reducible] def vectorFintype (V : Type*) [AddCommGroup V] [Module F2 V]
    [FiniteDimensional F2 V] : Fintype V :=
  Fintype.ofEquiv (Fin (finrank F2 V) → F2) (Module.finBasis F2 V).equivFun.symm.toEquiv

@[instance_reducible] def compressedFintype (X : E →ₗ[F2] F) : Fintype (X.ker →ₗ[F2] (F ⧸ X.range)) := by
  classical
  letI := vectorFintype X.ker
  letI := vectorFintype (F ⧸ X.range)
  exact Fintype.ofInjective DFunLike.coe DFunLike.coe_injective

/-- Energy of the actual merged derivative coefficients. -/
def energy (a : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) : ℝ := by
  classical
  letI := compressedFintype X
  exact ∑ Z, (∑ Y, if RankBelow X Y ∧ FullCompression.compression X Y = Z
    then a Y else 0)^2

end MaxCutGames.Appendix.WeightedFourthMoment

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Derivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MaxCutGames.Appendix.Derivatives
open scoped BigOperators
open MaxCutGames.Fourier.MatrixCharacters MaxCutGames.Fourier.MatrixFourier
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- Actual normalized Fourier projector onto the indices satisfying `P`. -/
def spectralProjector (P : (F →ₗ[F2] E) → Prop) (f : (E →ₗ[F2] F) → ℝ) :
    (E →ₗ[F2] F) → ℝ :=
  ∑ Y with P Y, linearCoeff f Y • (fun X => (linearTraceCharacter Y X).re)

def hybridProjector (A : Submodule F2 E) (B : Submodule F2 F)
    (f : (E →ₗ[F2] F) → ℝ) : (E →ₗ[F2] F) → ℝ :=
  spectralProjector (fun Y => LinearIdentities.Hybrid Y A B) f

def hybridDerivative (A : Submodule F2 E) (B : Submodule F2 F)
    (T : E →ₗ[F2] F) (f : (E →ₗ[F2] F) → ℝ) :
    MaxCutGames.Fourier.MatrixRestrictions.Parameter A B → ℝ :=
  MaxCutGames.Fourier.MatrixRestrictions.restrict (hybridProjector A B f) A B T

def rankProjector (X : F →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ) :
    (E →ₗ[F2] F) → ℝ :=
  spectralProjector (fun Y => RankAdditivity.RankBelow X Y) f

def mapDerivative (X : F →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ) :
    MaxCutGames.Fourier.MatrixRestrictions.Parameter X.range X.ker → ℝ :=
  MaxCutGames.Fourier.MatrixRestrictions.restrict (rankProjector X f) X.range X.ker 0

def selectorMultiplicity {I : Type*} [Fintype I]
    (P : I → (F →ₗ[F2] E) → Prop) (Y : F →ₗ[F2] E) : ℕ :=
  (Finset.univ.filter (fun i : I => P i Y)).card

variable [Finite E] [Finite F]

def HybridIndex (d : ℕ) :=
  {p : Submodule F2 E × Submodule F2 F //
    MaxCutGames.Fourier.MatrixRestrictions.order p.1 p.2 ≤ d}

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

end MaxCutGames.Appendix.Derivatives

/-!
# Actual Hybrid derivative energy in product coordinates

Parseval and affine restriction merge the selected Fourier coefficients over
each actual compressed frequency. For a product splitting, explicit linear
equivalences identify the quotient by the first factor with the second factor,
and the first-factor subspace with its original space. Reindexing the frequency
sum therefore introduces no multiplicity or normalization factor.
-/

namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open MaxCutGames.Fourier.MatrixCharacters MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Appendix MaxCutGames.Appendix.Derivatives

section ProductEquivalences

variable {R A U B C : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup U] [Module R U]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]

/-- The first factor, regarded as its actual coordinate subspace. -/
def leftRangeEquiv : B ≃ₗ[R] LinearMap.range (LinearMap.inl R B C) where
  toFun b := ⟨(b, 0), ⟨b, rfl⟩⟩
  invFun x := x.val.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨x, hx⟩
    obtain ⟨b, rfl⟩ := hx
    rfl
  map_add' _ _ := by apply Subtype.ext; simp
  map_smul' _ _ := by apply Subtype.ext; simp

@[simp] theorem leftRangeEquiv_coe (b : B) :
    (leftRangeEquiv (R := R) (C := C) b : B × C) = (b, 0) := rfl

/-- The second projection descends through the first-factor quotient. -/
def quotientRightMap :
    ((A × U) ⧸ LinearMap.range (LinearMap.inl R A U)) →ₗ[R] U :=
  (LinearMap.range (LinearMap.inl R A U)).liftQ (LinearMap.snd R A U) (by
    rintro x ⟨a, rfl⟩
    rfl)

@[simp] theorem quotientRightMap_mkQ (x : A × U) :
    quotientRightMap (R := R)
      ((LinearMap.range (LinearMap.inl R A U)).mkQ x) = x.2 := rfl

/-- The quotient by the first coordinate has the second coordinate as a
canonical linear presentation. -/
def quotientRightEquiv :
    ((A × U) ⧸ LinearMap.range (LinearMap.inl R A U)) ≃ₗ[R] U where
  toLinearMap := quotientRightMap
  invFun u := (LinearMap.range (LinearMap.inl R A U)).mkQ (0, u)
  left_inv := by
    intro q
    obtain ⟨⟨a, u⟩, rfl⟩ := (LinearMap.range (LinearMap.inl R A U)).mkQ_surjective q
    change (LinearMap.range (LinearMap.inl R A U)).mkQ (0, u) =
      (LinearMap.range (LinearMap.inl R A U)).mkQ (a, u)
    have hz : (LinearMap.range (LinearMap.inl R A U)).mkQ (a, 0) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨a, rfl⟩
    calc
      _ = (LinearMap.range (LinearMap.inl R A U)).mkQ (a, 0) +
          (LinearMap.range (LinearMap.inl R A U)).mkQ (0, u) := by rw [hz, zero_add]
      _ = (LinearMap.range (LinearMap.inl R A U)).mkQ ((a, 0) + (0, u)) :=
        (map_add _ _ _).symm
      _ = _ := by simp
  right_inv _ := rfl

@[simp] theorem quotientRightEquiv_mkQ (x : A × U) :
    quotientRightEquiv (R := R)
      ((LinearMap.range (LinearMap.inl R A U)).mkQ x) = x.2 := rfl

/-- The exact change of frequency coordinates for a product restriction. -/
def productFrequencyEquiv :
    ((LinearMap.range (LinearMap.inl R B C)) →ₗ[R]
      ((A × U) ⧸ LinearMap.range (LinearMap.inl R A U))) ≃ (B →ₗ[R] U) where
  toFun Z := (quotientRightEquiv (R := R) (A := A) (U := U)).toLinearMap.comp
    (Z.comp (leftRangeEquiv (R := R) (B := B) (C := C)).toLinearMap)
  invFun Z := (quotientRightEquiv (R := R) (A := A) (U := U)).symm.toLinearMap.comp
    (Z.comp (leftRangeEquiv (R := R) (B := B) (C := C)).symm.toLinearMap)
  left_inv Z := by
    apply LinearMap.ext
    intro b
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  right_inv Z := by
    apply LinearMap.ext
    intro b
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]

end ProductEquivalences

variable {A U B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C]

omit [FiniteDimensional F2 A] [FiniteDimensional F2 U] [FiniteDimensional F2 B] [FiniteDimensional F2 C] in
/-- Actual quotient compression becomes the block compression. -/
@[simp] theorem productFrequencyEquiv_compressFrequency
    (S : (B × C) →ₗ[F2] (A × U)) :
    productFrequencyEquiv (Restriction.compressFrequency
      (LinearMap.range (LinearMap.inl F2 A U))
      (LinearMap.range (LinearMap.inl F2 B C)) S) =
      (LinearMap.snd F2 A U).comp (S.comp (LinearMap.inl F2 B C)) := by
  apply LinearMap.ext
  intro b
  rfl

end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

/-!
# Actual Fourier components for the KMS analytic argument

All coefficients use normalized expectation on the primal matrix space; sums
over frequencies are unnormalized. These identities use only the common
trace-character Fourier identities.
-/

/-!
# Exact rank support of actual hybrid derivatives

The actual Hybrid selector loses exactly `dim A + codim B` in rank.
Consequently a pure rank component has derivative coefficients supported at
that exact remaining rank. Orders above the original rank give zero.
-/

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_A4IndexCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Appendix A.4 index encoding. Its kernel and range recover the
two subspaces, and its quotient relation recovers the linear map. The final
count follows from this injection into a genuine binary linear-map space. -/

noncomputable section

namespace MaxCutGames.Appendix.A4IndexCount

section Generic

variable {K : Type*} [Field K]

def factorViaRange {U L T : Type*}
    [AddCommGroup U] [Module K U] [AddCommGroup L] [Module K L]
    [AddCommGroup T] [Module K T]
    (X : U →ₗ[K] L) (P : U →ₗ[K] T) (hker : X.ker ≤ P.ker) :
    X.range →ₗ[K] T :=
  (X.ker.liftQ P hker).comp X.quotKerEquivRange.symm.toLinearMap

variable {V W : Type*}
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def quotientRestriction (B B0 : Submodule K W) : B0 →ₗ[K] (W ⧸ B) :=
  B.mkQ.comp B0.subtype

theorem ker_quotientRestriction (B B0 : Submodule K W) :
    (quotientRestriction B B0).ker = B.comap B0.subtype := by
  ext b
  change B.mkQ (b : W) = 0 ↔ (b : W) ∈ B
  exact Submodule.Quotient.mk_eq_zero B

def aToRange (A A0 : Submodule K V) (B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hR : X.range = A.map A0.mkQ) : A →ₗ[K] X.range :=
  (A0.mkQ.comp A.subtype).codRestrict X.range (by
    intro a
    rw [hR]
    exact Submodule.mem_map.mpr ⟨a.val, a.property, rfl⟩)

def encodeFixed (A A0 : Submodule K V) (B B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hK : X.ker = B.comap B0.subtype)
    (hR : X.range = A.map A0.mkQ) : A →ₗ[K] (W ⧸ B) :=
  (factorViaRange X (quotientRestriction B B0)
    (hK.trans (ker_quotientRestriction B B0).symm).le).comp
      (aToRange A A0 B0 X hR)

def Valid (A : Submodule K V) (B : Submodule K W)
    (p : LinearIdentities.A4Index (K := K) (W := W) (V := V)) : Prop :=
  p.1 ≤ A ∧ B ≤ p.2.1 ∧ p.2.2.ker = B.comap p.2.1.subtype ∧
    p.2.2.range = A.map p.1.mkQ

abbrev Index (A : Submodule K V) (B : Submodule K W) :=
  {p : LinearIdentities.A4Index (K := K) (W := W) (V := V) // Valid A B p}

def encode (A : Submodule K V) (B : Submodule K W)
    (p : Index A B) : A →ₗ[K] (W ⧸ B) :=
  encodeFixed A p.val.1 B p.val.2.1 p.val.2.2
    p.property.2.2.1 p.property.2.2.2

end Generic

open Integration.BinaryLinear

end MaxCutGames.Appendix.A4IndexCount

/-!
# Actual Fourier-projector partitions for Appendix A.4 and A.5

The partitions use the proved unique geometric selectors on each actual
Fourier index. Their finite index types are the canonical counting types.
-/

open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Appendix.Derivatives

namespace MaxCutGames.Appendix.OperatorPartitions

attribute [local instance] Classical.propDecidable

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

variable [Finite E] [Finite F]

open MaxCutGames.Appendix.LinearIdentities
open MaxCutGames.Appendix.RankAdditivity

abbrev A4GeometricIndex (A : Submodule F2 E) (B : Submodule F2 F) :=
  A4IndexCount.Index A B

def a4Mask (A : Submodule F2 E) (B : Submodule F2 F)
    (i : A4GeometricIndex A B) (Y : F →ₗ[F2] E) : Prop :=
  Hybrid Y i.val.1 i.val.2.1 ∧
    RankBelow i.val.2.2 (compress Y i.val.1 i.val.2.1)

def A5Geometry (X : F →ₗ[F2] E) (A : Submodule F2 E) (B : Submodule F2 F)
    (p : Submodule F2 E × Submodule F2 F) : Prop :=
  Disjoint p.1 X.range ∧ p.1 ⊔ X.range = A ∧
    p.2 ⊔ X.ker = ⊤ ∧ p.2 ⊓ X.ker = B

abbrev A5GeometricIndex (X : F →ₗ[F2] E)
    (A : Submodule F2 E) (B : Submodule F2 F) :=
  {p : Submodule F2 E × Submodule F2 F // A5Geometry X A B p}

def a5Mask (X : F →ₗ[F2] E) (A : Submodule F2 E) (B : Submodule F2 F)
    (i : A5GeometricIndex X A B) (Y : F →ₗ[F2] E) : Prop :=
  Hybrid Y i.val.1 i.val.2 ∧
    RankBelow (compress X i.val.1 i.val.2) (compress Y i.val.1 i.val.2)

def a5OuterMask (X : F →ₗ[F2] E) (A : Submodule F2 E)
    (B : Submodule F2 F) (Y : F →ₗ[F2] E) : Prop :=
  RankBelow X Y ∧ Hybrid (compress Y X.range X.ker)
    (A.map X.range.mkQ) (B.comap X.ker.subtype)

end MaxCutGames.Appendix.OperatorPartitions
end

/-!
# Exact transport of nested affine restrictions

The nested quotient-domain/range inclusion has exactly the effective
annihilator and target obtained by comap and map. Its parameterization is
linearly equivalent to the direct effective restriction, independently of
any Fourier frequency. Thus normalized second moments and the outer average
of their squares agree while retaining the full affine translate.
-/

noncomputable section

namespace MaxCutGames.Appendix.RestrictionTransport

open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixRestrictions

section Nested

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

/-- Compose the two actual quotient-domain and target-subspace embeddings. -/
def nestedEmbedding (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) :
    Parameter C D →ₗ[F2] (E →ₗ[F2] F) :=
  (embedding A B).comp (embedding C D)

end Nested

section SameRange

variable {K : Type*} {G : Type*} {P : Type*} {Q : Type*} [Field K]
  [AddCommGroup G] [Module K G] [AddCommGroup P] [Module K P]
  [AddCommGroup Q] [Module K Q]

theorem exists_range_preimage_inline_RestrictionTransport (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (h : f.range ≤ g.range) (x : P) : ∃ y : Q, g y = f x := h ⟨x, rfl⟩

/-- The actual linear change of parameters between two injective presentations. -/
def sameRangeEquiv (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) : P ≃ₗ[K] Q := by
  let fw (x : P) := Classical.choose (exists_range_preimage_inline_RestrictionTransport f g (le_of_eq h) x)
  let bw (y : Q) := Classical.choose (exists_range_preimage_inline_RestrictionTransport g f (le_of_eq h.symm) y)
  have hfw (x : P) : g (fw x) = f x :=
    Classical.choose_spec (exists_range_preimage_inline_RestrictionTransport f g (le_of_eq h) x)
  have hbw (y : Q) : f (bw y) = g y :=
    Classical.choose_spec (exists_range_preimage_inline_RestrictionTransport g f (le_of_eq h.symm) y)
  exact
    { toFun := fw
      invFun := bw
      left_inv := by
        intro x
        apply hf
        rw [hbw, hfw]
      right_inv := by
        intro y
        apply hg
        rw [hfw, hbw]
      map_add' := by
        intro x y
        apply hg
        simp only [map_add, hfw]
      map_smul' := by
        intro c x
        change fw (c • x) = c • fw x
        apply hg
        simp only [map_smul, hfw] }

end SameRange

end MaxCutGames.Appendix.RestrictionTransport

/-! Genuine hybrid derivative composition: the effective subspaces have
additive order, and the full translate average preserves the square of the
second moment. Transport of an additional map derivative is a separate step. -/

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_LevelInequality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The real-valued finite-probability steps at the end of Appendix A.5.

The results here prove normalized Cauchy--Schwarz/Hölder consequences and
Boolean moment identities. They do not introduce Proposition A.5 or Lemma A.6
as axioms, and do not identify a conditional estimate with Theorem 2.3.
-/

noncomputable section

namespace MaxCutGames.Appendix.LevelInequality

open scoped BigOperators
open MaxCutGames.Fourier.MatrixCharacters MaxCutGames.Fourier.MatrixFourier

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- The actual rank of a Fourier index `S : F → E`. -/
def frequencyRank (S : F →ₗ[F2] E) : ℕ := Module.finrank F2 (LinearMap.range S)

end MaxCutGames.Appendix.LevelInequality

/-! Actual Fourier degree loss for both derivative operators. The support
cutoffs apply to genuine binary linear maps, including the case where the
total derivative order is larger than the original degree. -/

namespace MaxCutGames.Appendix.DerivativeDegree

open scoped BigOperators
open MaxCutGames.Fourier.MatrixCharacters MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Fourier.MatrixRestrictions
open MaxCutGames.Appendix.Derivatives
open MaxCutGames.Appendix.LevelInequality (frequencyRank)
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- Fourier support is restricted to maps of rank at most `d`. -/
def DegreeAtMost (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : Prop :=
  ∀ Y, d < frequencyRank Y → linearCoeff f Y = 0

variable [Finite E] [Finite F]

local instance quotientFinite (A : Submodule F2 E) : Finite (E ⧸ A) :=
  Finite.of_surjective A.mkQ A.mkQ_surjective

local instance compressedDualFintype (A : Submodule F2 E) (B : Submodule F2 F) :
    Fintype (B →ₗ[F2] (E ⧸ A)) := by
  classical
  letI : Fintype B := Fintype.ofFinite _
  letI : Fintype (E ⧸ A) := Fintype.ofFinite _
  exact Fintype.ofInjective (fun L : B →ₗ[F2] (E ⧸ A) => (L : B → E ⧸ A))
    DFunLike.coe_injective

end MaxCutGames.Appendix.DerivativeDegree

/-! The degree-zero base case in the actual finite binary Fourier model. -/

/-! The actual forward Appendix A.5 index injects into two spaces of linear
maps. The first map recovers the image complement, the second its kernel
complement. No index-cardinality inequality is assumed. -/

namespace MaxCutGames.Appendix.A5IndexCount

open MaxCutGames.Integration.BinaryLinear (F2)

variable {V W : Type*}
  [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]

def insideEquiv (A I : Submodule F2 V) (hIA : I ≤ A) :
    (I.comap A.subtype) ≃ₗ[F2] I where
  toFun i := ⟨i.val.val, i.property⟩
  invFun i := ⟨⟨i.val, hIA i.property⟩, i.property⟩
  left_inv _i := Subtype.ext (Subtype.ext rfl)
  right_inv _i := Subtype.ext rfl
  map_add' _i _j := Subtype.ext rfl
  map_smul' _c _i := Subtype.ext rfl

theorem internal_isCompl (A I A0 : Submodule F2 V) (hIA : I ≤ A)
    (hd : Disjoint A0 I) (hj : A0 ⊔ I = A) :
    IsCompl (I.comap A.subtype) (A0.comap A.subtype) := by
  have hA0 : A0 ≤ A := le_sup_left.trans hj.le
  refine ⟨Submodule.disjoint_def.mpr ?_, codisjoint_iff.mpr ?_⟩
  · intro a hi h0
    exact Subtype.ext (Submodule.disjoint_def.mp hd a.val h0 hi)
  · apply eq_top_iff.mpr
    intro a _
    have ha : a.val ∈ A0 ⊔ I := by rw [hj]; exact a.property
    rcases Submodule.mem_sup.mp ha with ⟨v, hv, i, hi, hvi⟩
    refine Submodule.mem_sup.mpr ⟨⟨i, hIA hi⟩, hi, ⟨v, hA0 hv⟩, hv, ?_⟩
    apply Subtype.ext
    change i + v = a.val
    rw [add_comm]
    exact hvi

def projectionA0 (A I A0 : Submodule F2 V) (hIA : I ≤ A)
    (hd : Disjoint A0 I) (hj : A0 ⊔ I = A) : A →ₗ[F2] I :=
  (insideEquiv A I hIA).toLinearMap.comp
    (((I.comap A.subtype).isComplEquivProj
      ⟨A0.comap A.subtype, internal_isCompl A I A0 hIA hd hj⟩).val)

def fullRange {U L : Type*} [AddCommGroup U] [Module F2 U]
    [AddCommGroup L] [Module F2 L] (S : U →ₗ[F2] L) (hS : S.range = ⊤) :
    L →ₗ[F2] S.range :=
  (LinearMap.id : L →ₗ[F2] L).codRestrict S.range (fun x => by rw [hS]; trivial)

theorem quotientRestriction_surjective (J B0 : Submodule F2 W) (hc : B0 ⊔ J = ⊤) :
    Function.Surjective (A4IndexCount.quotientRestriction J B0) := by
  intro z
  obtain ⟨w, rfl⟩ := J.mkQ_surjective z
  have hw : w ∈ B0 ⊔ J := by rw [hc]; trivial
  rcases Submodule.mem_sup.mp hw with ⟨b, hb, j, hj, hbj⟩
  refine ⟨⟨b, hb⟩, ?_⟩
  change J.mkQ b = J.mkQ w
  have hz : J.mkQ j = 0 := (Submodule.Quotient.mk_eq_zero J).mpr hj
  rw [← hbj, map_add, hz, add_zero]

theorem quotientRestriction_same_kernel (B J B0 : Submodule F2 W)
    (hm : B0 ⊓ J = B) :
    (A4IndexCount.quotientRestriction J B0).ker =
      (A4IndexCount.quotientRestriction B B0).ker := by
  rw [A4IndexCount.ker_quotientRestriction, A4IndexCount.ker_quotientRestriction]
  ext b
  change (b : W) ∈ J ↔ (b : W) ∈ B
  constructor
  · intro hj
    have hb : (b : W) ∈ B0 ⊓ J := ⟨b.property, hj⟩
    rwa [hm] at hb
  · intro hb
    exact (hm.symm.le.trans inf_le_right) hb

def sectionB0 (B J B0 : Submodule F2 W)
    (hc : B0 ⊔ J = ⊤) (hm : B0 ⊓ J = B) : (W ⧸ J) →ₗ[F2] (W ⧸ B) :=
  (A4IndexCount.factorViaRange (A4IndexCount.quotientRestriction J B0)
    (A4IndexCount.quotientRestriction B B0)
    (quotientRestriction_same_kernel B J B0 hm).le).comp
      (fullRange (A4IndexCount.quotientRestriction J B0)
        (LinearMap.range_eq_top.mpr (quotientRestriction_surjective J B0 hc)))

def encode (X : W →ₗ[F2] V) (A : Submodule F2 V) (B : Submodule F2 W)
    (hIA : X.range ≤ A) (p : OperatorPartitions.A5GeometricIndex X A B) :
    (A →ₗ[F2] X.range) × ((W ⧸ X.ker) →ₗ[F2] (W ⧸ B)) :=
  (projectionA0 A X.range p.val.1 hIA p.property.1 p.property.2.1,
    sectionB0 B X.ker p.val.2 p.property.2.2.1 p.property.2.2.2)

end MaxCutGames.Appendix.A5IndexCount
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_OperatorNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Native derivative norm decompositions for Appendix A.4 and A.5

The finite projector partitions and exact affine restriction transport yield
norm bounds for the actual derivative operators. The cardinality factors are
explicit: numerical estimates on the geometric index sets are separate lemmas.
-/

noncomputable section
open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier
open MaxCutGames.Appendix.Derivatives
open MaxCutGames.Appendix.OperatorPartitions
open MaxCutGames.Appendix.LinearIdentities
open MaxCutGames.Appendix.RankAdditivity

namespace MaxCutGames.Appendix.OperatorNorm

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F]

local instance quotientFinite (A : Submodule F2 E) : Finite (E ⧸ A) :=
  Finite.of_surjective A.mkQ A.mkQ_surjective

local instance compressedDualFintype (A : Submodule F2 E) (B : Submodule F2 F) :
    Fintype (B →ₗ[F2] (E ⧸ A)) := by
  classical
  letI : Fintype B := Fintype.ofFinite _
  letI : Fintype (E ⧸ A) := Fintype.ofFinite _
  exact Fintype.ofInjective (fun L : B →ₗ[F2] (E ⧸ A) => (L : B → E ⧸ A))
    DFunLike.coe_injective

end MaxCutGames.Appendix.OperatorNorm
end

/-! Natural changes of domain and codomain preserve rank, Fourier projectors,
and map-derivative energies. The quotient/subtype specialization transports
the actual labels occurring in nested hybrid derivatives. -/

noncomputable section
namespace MaxCutGames.Appendix.NaturalTransport
open scoped BigOperators
open MaxCutGames.Fourier.MatrixCharacters MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Fourier.MatrixRestrictions
open MaxCutGames.Appendix.Derivatives MaxCutGames.Appendix.RankAdditivity
attribute [local instance] Classical.propDecidable

local instance instFiniteQuotientSubmoduleF2 {V : Type*} [AddCommGroup V] [Module F2 V] [Finite V]
    (P : Submodule F2 V) : Finite (V ⧸ P) :=
  Finite.of_surjective P.mkQ P.mkQ_surjective

local instance instFintypeLinearMapF2IdSubtypeMemSubmoduleQuotientOfFinite {U V : Type*} [AddCommGroup U] [Module F2 U]
    [AddCommGroup V] [Module F2 V] [Finite U] [Finite V]
    (A : Submodule F2 U) (B : Submodule F2 V) : Fintype (B →ₗ[F2] (U ⧸ A)) :=
  OperatorNorm.compressedDualFintype A B

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

def parameterFactor (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) :
    Parameter C D ≃ₗ[F2] Parameter (C.comap A.mkQ) (D.map B.subtype) :=
  LinearEquiv.arrowCongr (quotientFactor A C).symm (outputFactor B D)

def dualFactor (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) :
    (D →ₗ[F2] ((E ⧸ A) ⧸ C)) ≃ₗ[F2]
      ((D.map B.subtype) →ₗ[F2] (E ⧸ C.comap A.mkQ)) :=
  LinearEquiv.arrowCongr (outputFactor B D) (quotientFactor A C).symm

end MaxCutGames.Appendix.NaturalTransport

/-!
# Exact coordinate transport of hybrid derivative energy

Both ambient spaces, both selector subspaces, and the affine MaxCutGames.Fourier.MatrixRestrictions.translate are
transported together. The actual Fourier selector and the actual affine
restriction then have the same normalized squared norm.
-/

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_A5Scalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite scalar estimates in the Appendix A.5 induction

The geometric estimate retains the original positive-order condition
`1 ≤ i + j + k`; deleting the origin is essential when `k = 0`.
-/

noncomputable section
open scoped BigOperators

namespace MaxCutGames.Appendix.A5Scalar

def positiveSum (q : ℝ) (n m k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
    if 1 ≤ i + j + k then q ^ (i + j + k) else 0

end MaxCutGames.Appendix.A5Scalar
end

/-! Canonical indices for the Appendix A.5 induction passage. The outer
hybrid index is recovered from its actual geometric pair, so forgetting it
does not increase multiplicity. -/

noncomputable section

namespace MaxCutGames.Appendix.A5Passage

open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Appendix.Derivatives
attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

abbrev OuterIndex (X : F →ₗ[F2] E) (e : Nat) :=
  HybridIndex (E := E ⧸ X.range) (F := X.ker) e

def LiftedA (X : F →ₗ[F2] E) {e : Nat} (s : OuterIndex X e) : Submodule F2 E :=
  s.val.1.comap X.range.mkQ

def LiftedB (X : F →ₗ[F2] E) {e : Nat} (s : OuterIndex X e) : Submodule F2 F :=
  s.val.2.map X.ker.subtype

abbrev Pair (X : F →ₗ[F2] E) {e : Nat} (s : OuterIndex X e) :=
  OperatorPartitions.A5GeometricIndex X (LiftedA X s) (LiftedB X s)

abbrev Passage (X : F →ₗ[F2] E) (e : Nat) :=
  Σ s : OuterIndex X e, Pair X s

def forget (X : F →ₗ[F2] E) (e : Nat) (q : Passage X e) :
    Submodule F2 E × Submodule F2 F := q.2.val

@[simp] theorem forget_val (X : F →ₗ[F2] E) (e : Nat) (q : Passage X e) :
    forget X e q = q.2.val := rfl

variable [Finite E] [Finite F]

instance pairFintype (X : F →ₗ[F2] E) {e : Nat} (s : OuterIndex X e) :
    Fintype (Pair X s) := by
  letI : Finite (Submodule F2 E) :=
    Finite.of_injective (fun A : Submodule F2 E => (A : Set E)) SetLike.coe_injective
  letI : Finite (Submodule F2 F) :=
    Finite.of_injective (fun B : Submodule F2 F => (B : Set F)) SetLike.coe_injective
  exact Fintype.ofFinite _

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

def descendantSum (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) (e : Nat) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ q : Passage X e,
    𝔼 U, (𝔼 N, mapDerivative
      (NaturalTransport.dualFactor A B q.2.val.1 q.2.val.2
        (LinearIdentities.compress X q.2.val.1 q.2.val.2))
      (hybridDerivative (q.2.val.1.comap A.mkQ) (q.2.val.2.map B.subtype) U f) N ^ 2) ^ 2

end MaxCutGames.Appendix.A5Passage
end

/-! Finite Gram-energy estimates used in Lemma A.1. The witness relation and
frequency-count instantiations are separate obligations. -/

/-! Subspace classification by one additional coordinate and the finite-field
subspace Möbius identity. All spaces, quotients and dimensions are genuine. -/
namespace MaxCutGames.Appendix.SubspaceExtensions
open scoped BigOperators
open LinearMap Submodule
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def horizontal (B : Submodule K V) : Submodule K (V × K) := B.prod ⊥
def hKernel (S : Submodule K (V × K)) : Submodule K V := S.comap (LinearMap.inl K V K)

def scalarMap {Q : Type*} [AddCommGroup Q] [Module K Q] (q : Q) : K →ₗ[K] Q where
  toFun t := t • q
  map_add' a b := add_smul a b q
  map_smul' a b := by change (a*b) • q = a • (b • q); exact mul_smul a b q

def extension (B : Submodule K V) (q : V ⧸ B) : Submodule K (V × K) :=
  LinearMap.ker (B.mkQ.comp (LinearMap.fst K V K) -
    (scalarMap q).comp (LinearMap.snd K V K))

theorem extension_mem (B : Submodule K V) (q : V ⧸ B) (x : V) (t : K) :
    (x,t) ∈ extension B q ↔ B.mkQ x = t • q := by
  change B.mkQ x - t • q = 0 ↔ _
  exact sub_eq_zero

theorem mkQ_eq_smul_iff (B : Submodule K V) (x v : V) (t : K) :
    B.mkQ x = t • B.mkQ v ↔ x - t • v ∈ B := by
  have he : B.mkQ (x-t•v) = B.mkQ x - t•B.mkQ v := by simp only [map_sub, map_smul]
  rw [← sub_eq_zero, ← he]
  change (x-t•v ∈ LinearMap.ker B.mkQ) ↔ _
  rw [Submodule.ker_mkQ]

@[simp] theorem hKernel_horizontal (B : Submodule K V) : hKernel (horizontal B) = B := by
  ext x
  change (x ∈ B ∧ (0:K) = 0) ↔ x ∈ B
  simp

@[simp] theorem hKernel_extension (B : Submodule K V) (q : V ⧸ B) : hKernel (extension B q) = B := by
  ext x
  change (x,0) ∈ extension B q ↔ x ∈ B
  rw [extension_mem, zero_smul]
  change (x ∈ LinearMap.ker B.mkQ) ↔ x ∈ B
  rw [Submodule.ker_mkQ]

theorem exists_one_extension (B : Submodule K V) (q : V ⧸ B) : ∃ v, (v,1) ∈ extension B q := by
  obtain ⟨v,hv⟩ := B.mkQ_surjective q
  exact ⟨v, (extension_mem B q v 1).mpr (by simpa only [one_smul] using hv)⟩

theorem eq_extension_of_one_mem (S : Submodule K (V × K)) (v : V)
    (hv : (v,1) ∈ S) : S = extension (hKernel S) ((hKernel S).mkQ v) := by
  ext p
  rcases p with ⟨x,t⟩
  rw [extension_mem, mkQ_eq_smul_iff]
  change (x,t) ∈ S ↔ (x-t•v,0) ∈ S
  have hz : (x-t•v,0) = (x,t)-t•(v,1) := by ext <;> simp
  rw [hz]
  constructor
  · intro hx; exact S.sub_mem hx (S.smul_mem t hv)
  · intro hx
    have h := S.add_mem hx (S.smul_mem t hv)
    simpa only [sub_add_cancel] using h

theorem eq_horizontal_of_no_one (S : Submodule K (V × K))
    (hn : ¬ ∃ v, (v,1) ∈ S) : S = horizontal (hKernel S) := by
  have last_zero : ∀ x t, (x,t) ∈ S → t = 0 := by
    intro x t hxt
    by_contra ht
    have h := S.smul_mem t⁻¹ hxt
    have h' : (t⁻¹ • x,1) ∈ S := by simpa [smul_eq_mul, ht] using h
    exact hn ⟨_,h'⟩
  ext p
  rcases p with ⟨x,t⟩
  change (x,t) ∈ S ↔ (x ∈ hKernel S ∧ t = 0)
  constructor
  · intro hp
    have ht := last_zero x t hp
    subst t
    exact ⟨hp,rfl⟩
  · rintro ⟨hx,rfl⟩
    exact hx

theorem horizontal_ne_extension (A B : Submodule K V) (q : V ⧸ B) : horizontal A ≠ extension B q := by
  intro h
  obtain ⟨v,hv⟩ := exists_one_extension B q
  have hv' : (v,1) ∈ horizontal A := h.symm ▸ hv
  change v ∈ A ∧ (1:K) = 0 at hv'
  exact one_ne_zero hv'.2

theorem extension_injective (B : Submodule K V) : Function.Injective (extension B) := by
  intro q r h
  obtain ⟨v,hv⟩ := B.mkQ_surjective q
  have hp : (v,1) ∈ extension B q := (extension_mem B q v 1).mpr (by simpa using hv)
  have hp' : (v,1) ∈ extension B r := h ▸ hp
  have hr := (extension_mem B r v 1).mp hp'
  simpa only [one_smul, hv] using hr

def encode : (Submodule K V) ⊕ (Σ B : Submodule K V, V ⧸ B) → Submodule K (V × K)
  | .inl B => horizontal B
  | .inr ⟨B,q⟩ => extension B q

theorem encode_injective : Function.Injective (encode (K:=K) (V:=V)) := by
  intro a b h
  cases a with
  | inl A =>
    cases b with
    | inl B =>
      have hAB : A = B := by simpa only [encode,hKernel_horizontal] using congrArg hKernel h
      subst B
      rfl
    | inr b =>
      rcases b with ⟨B,q⟩
      exact False.elim (horizontal_ne_extension A B q h)
  | inr a =>
    rcases a with ⟨A,q⟩
    cases b with
    | inl B => exact False.elim (horizontal_ne_extension B A q h.symm)
    | inr b =>
      rcases b with ⟨B,r⟩
      have hAB : A = B := by simpa only [encode,hKernel_extension] using congrArg hKernel h
      cases hAB
      have hqr : q = r := extension_injective A h
      cases hqr
      rfl

theorem encode_surjective : Function.Surjective (encode (K:=K) (V:=V)) := by
  intro S
  by_cases h : ∃ v, (v,1) ∈ S
  · obtain ⟨v,hv⟩ := h
    exact ⟨.inr ⟨hKernel S,(hKernel S).mkQ v⟩, (eq_extension_of_one_mem S v hv).symm⟩
  · exact ⟨.inl (hKernel S), (eq_horizontal_of_no_one S h).symm⟩

def splitEquiv : Submodule K (V × K) ≃ (Submodule K V) ⊕ (Σ B : Submodule K V, V ⧸ B) :=
  (Equiv.ofBijective encode ⟨encode_injective,encode_surjective⟩).symm

def horizontalEquiv (B : Submodule K V) : B ≃ₗ[K] horizontal B where
  toFun b := ⟨((b:V),0),⟨b.property,rfl⟩⟩
  invFun p := ⟨p.val.1,p.property.1⟩
  left_inv b := by apply Subtype.ext; rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hp : p.val.2 = 0 := p.property.2
      exact hp.symm
  map_add' a b := by apply Subtype.ext; simp
  map_smul' c b := by apply Subtype.ext; simp

def extensionEquiv (B : Submodule K V) (q : V ⧸ B) (v : V) (hv : B.mkQ v = q) :
    (B × K) ≃ₗ[K] extension B q where
  toFun p := ⟨((p.1:V)+p.2•v,p.2), by
    apply (extension_mem B q _ _).mpr
    have hb : B.mkQ (p.1:V) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [Submodule.ker_mkQ]
      exact p.1.property
    simp only [map_add,map_smul,hb,hv,zero_add]⟩
  invFun p := (⟨p.val.1-p.val.2•v, by
    apply (mkQ_eq_smul_iff B _ v _).mp
    rw [hv]
    exact (extension_mem B q _ _).mp p.property⟩,p.val.2)
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      change ((p.1:V)+p.2•v)-p.2•v = (p.1:V)
      exact add_sub_cancel_right _ _
    · rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · change (p.val.1-p.val.2•v)+p.val.2•v = p.val.1
      exact sub_add_cancel _ _
    · rfl
  map_add' p r := by
    apply Subtype.ext
    apply Prod.ext
    · change ((p.1:V)+(r.1:V))+(p.2+r.2)•v =
        ((p.1:V)+p.2•v)+((r.1:V)+r.2•v)
      rw [add_smul]
      abel
    · rfl
  map_smul' c p := by
    apply Subtype.ext
    apply Prod.ext
    · change c•(p.1:V)+(c*p.2)•v = c•((p.1:V)+p.2•v)
      rw [smul_add,mul_smul]
    · rfl

local instance subspaceFintype [Finite V] : Fintype (Submodule K V) := by
  classical
  letI := Fintype.ofFinite V
  exact Fintype.ofInjective (fun B : Submodule K V => (B : Set V)) SetLike.coe_injective
local instance quotientFintype [Finite V] (B : Submodule K V) : Fintype (V ⧸ B) := by
  letI : Finite (V ⧸ B) := Finite.of_surjective B.mkQ B.mkQ_surjective
  exact Fintype.ofFinite _

def weightedTotal [Finite V] (w : Nat → ℤ) : ℤ := ∑ B : Submodule K V, w (Module.finrank K B)

def mobiusWeight (q : Nat) : Nat → ℤ
  | 0 => 1
  | n+1 => -(q:ℤ)^n * mobiusWeight q n

def mobiusTotal [Finite K] [Finite V] : ℤ :=
  weightedTotal (K:=K) (V:=V) (mobiusWeight (Nat.card K))

variable {W : Type*} [AddCommGroup W] [Module K W]

theorem map_inverse (e : V ≃ₗ[K] W) (B : Submodule K V) :
    (B.map e.toLinearMap).map e.symm.toLinearMap = B := by
  have hc : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by ext x; simp
  rw [← Submodule.map_comp,hc,Submodule.map_id]

def subspaceEquiv (e : V ≃ₗ[K] W) : Submodule K V ≃ Submodule K W where
  toFun B := B.map e.toLinearMap
  invFun C := C.map e.symm.toLinearMap
  left_inv := map_inverse e
  right_inv := map_inverse e.symm

def subspaceMapEquiv (e : V ≃ₗ[K] W) (B : Submodule K V) : B ≃ₗ[K] B.map e.toLinearMap where
  toFun b := ⟨e b,Submodule.mem_map.mpr ⟨b,b.property,rfl⟩⟩
  invFun c := ⟨e.symm c,by
    rcases Submodule.mem_map.mp c.property with ⟨b,hb,hbc⟩

    rw [← hbc]
    simpa using hb⟩
  left_inv b := by apply Subtype.ext; simp
  right_inv c := by apply Subtype.ext; simp
  map_add' a b := by apply Subtype.ext; simp
  map_smul' c b := by apply Subtype.ext; simp

def coordinateSplit (n : Nat) :
    (Fin (n+1) → K) ≃ₗ[K] ((Fin n → K) × K) where
  toFun f := (fun i => f i.castSucc, f (Fin.last n))
  invFun p := Fin.lastCases p.2 p.1
  left_inv f := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv p := by
    apply Prod.ext
    · funext i; simp
    · simp
  map_add' f g := rfl
  map_smul' c f := rfl

end
end MaxCutGames.Appendix.SubspaceExtensions

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_SubmoduleInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Appendix.SubmoduleInterval
open Module
variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

def lowerIntervalEquiv (I : Submodule 𝕜 V) :
    {A : Submodule 𝕜 V // A ≤ I} ≃ Submodule 𝕜 I where
  toFun A := A.val.comap I.subtype
  invFun B := ⟨B.map I.subtype, by
    intro x hx
    rcases Submodule.mem_map.mp hx with ⟨b, hb, rfl⟩
    exact b.property⟩
  left_inv A := by
    apply Subtype.ext
    change (A.val.comap I.subtype).map I.subtype = A.val
    ext x
    constructor
    · intro hx
      rcases Submodule.mem_map.mp hx with ⟨b, hb, rfl⟩
      exact hb
    · intro hx
      exact Submodule.mem_map.mpr ⟨⟨x, A.property hx⟩, hx, rfl⟩
  right_inv B := by
    change (B.map I.subtype).comap I.subtype = B
    ext b
    constructor
    · intro hb
      change (b : V) ∈ B.map I.subtype at hb
      rcases Submodule.mem_map.mp hb with ⟨c, hc, hcb⟩
      have h : c = b := Subtype.ext hcb
      simpa only [h] using hc
    · intro hb
      exact Submodule.mem_map.mpr ⟨b, hb, rfl⟩

def lowerIntervalSpaceEquiv (I : Submodule 𝕜 V)
    (A : {A : Submodule 𝕜 V // A ≤ I}) :
    A.val ≃ₗ[𝕜] A.val.comap I.subtype where
  toFun a := ⟨⟨a.val, A.property a.property⟩, a.property⟩
  invFun b := ⟨b.val.val, b.property⟩
  left_inv _a := Subtype.ext rfl
  right_inv _b := Subtype.ext (Subtype.ext rfl)
  map_add' _a _b := Subtype.ext (Subtype.ext rfl)
  map_smul' _c _a := Subtype.ext (Subtype.ext rfl)

open scoped BigOperators
attribute [local instance] Classical.propDecidable

local instance submoduleFinite [Finite V] : Finite (Submodule 𝕜 V) :=
  Finite.of_injective (fun S : Submodule 𝕜 V => (S : Set V)) SetLike.coe_injective

noncomputable def lowerWeightedTotal [Finite V] (I : Submodule 𝕜 V) (w : Nat → ℤ) : ℤ := by
  classical
  letI := Fintype.ofFinite {A : Submodule 𝕜 V // A ≤ I}
  exact ∑ A : {A : Submodule 𝕜 V // A ≤ I}, w (finrank 𝕜 A.val)

end MaxCutGames.Appendix.SubmoduleInterval

/-! Actual reindexing of Appendix A.4 geometric witnesses by their raw triples.
The original nonzero weak-pair condition is equivalent to positive total
restriction order plus frequency rank. -/

noncomputable section

namespace MaxCutGames.Appendix.A13Index

open Module
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixRestrictions (order)

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

abbrev Triple := LinearIdentities.A4Index (K := F2) (W := F) (V := E)

def weakA (q : Triple (E := E) (F := F)) : Submodule F2 E :=
  q.2.2.range.comap q.1.mkQ

def weakB (q : Triple (E := E) (F := F)) : Submodule F2 F :=
  q.2.2.ker.map q.2.1.subtype

theorem recover_weakA {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) : weakA p.val = A := by
  rcases p with ⟨⟨A0, B0, X⟩, hA, hB, hK, hR⟩
  change X.range.comap A0.mkQ = A
  rw [hR]
  ext a
  change A0.mkQ a ∈ A.map A0.mkQ ↔ a ∈ A
  constructor
  · intro ha
    rcases Submodule.mem_map.mp ha with ⟨v, hv, he⟩
    have hm : a - v ∈ A0 := by
      apply (Submodule.Quotient.mk_eq_zero A0).mp
      change A0.mkQ (a - v) = 0
      rw [map_sub, he, sub_self]
    simpa only [sub_add_cancel] using A.add_mem (hA hm) hv
  · intro ha
    exact Submodule.mem_map.mpr ⟨a, ha, rfl⟩

theorem recover_weakB {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) : weakB p.val = B := by
  rcases p with ⟨⟨A0, B0, X⟩, hA, hB, hK, hR⟩
  change X.ker.map B0.subtype = B
  rw [hK]
  ext b
  constructor
  · intro hb
    rcases Submodule.mem_map.mp hb with ⟨v, hv, rfl⟩
    exact hv
  · intro hb
    exact Submodule.mem_map.mpr ⟨⟨b, hB hb⟩, hb, rfl⟩

theorem canonicalValid (q : Triple (E := E) (F := F)) :
    A4IndexCount.Valid (weakA q) (weakB q) q := by
  rcases q with ⟨A0, B0, X⟩
  change A0 ≤ X.range.comap A0.mkQ ∧ X.ker.map B0.subtype ≤ B0 ∧
    X.ker = (X.ker.map B0.subtype).comap B0.subtype ∧
    X.range = (X.range.comap A0.mkQ).map A0.mkQ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    change A0.mkQ a ∈ X.range
    have hz : A0.mkQ a = 0 := (Submodule.Quotient.mk_eq_zero A0).mpr ha
    rw [hz]
    exact X.range.zero_mem
  · intro b hb
    rcases Submodule.mem_map.mp hb with ⟨v, hv, rfl⟩
    exact v.property
  · ext b
    constructor
    · intro hb
      exact Submodule.mem_map.mpr ⟨b, hb, rfl⟩
    · intro hb
      change (b : F) ∈ X.ker.map B0.subtype at hb
      rcases Submodule.mem_map.mp hb with ⟨v, hv, he⟩
      have h : v = b := Subtype.ext he
      simpa only [h] using hv
  · ext z
    constructor
    · intro hz
      obtain ⟨v, rfl⟩ := A0.mkQ_surjective z
      exact Submodule.mem_map.mpr ⟨v, hz, rfl⟩
    · intro hz
      rcases Submodule.mem_map.mp hz with ⟨v, hv, rfl⟩
      exact hv

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 F] in
theorem dim_weakA {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) :
    finrank F2 A = finrank F2 p.val.1 + finrank F2 p.val.2.2.range := by
  rcases p with ⟨⟨A0, B0, X⟩, hA, hB, hK, hR⟩
  change finrank F2 A = finrank F2 A0 + finrank F2 X.range
  let Q := A4IndexCount.quotientRestriction A0 A
  have hQR : Q.range = X.range := by
    rw [hR]
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact Submodule.mem_map.mpr ⟨a.val, a.property, rfl⟩
    · intro hz
      rcases Submodule.mem_map.mp hz with ⟨a, ha, he⟩
      exact ⟨⟨a, ha⟩, he⟩
  have hQK : finrank F2 Q.ker = finrank F2 A0 := by
    rw [A4IndexCount.ker_quotientRestriction]
    exact (SubmoduleInterval.lowerIntervalSpaceEquiv A ⟨A0, hA⟩).finrank_eq.symm
  have h := Q.finrank_range_add_finrank_ker
  rw [hQR, hQK] at h
  omega

omit [FiniteDimensional F2 E] in
theorem codim_weakB {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) :
    finrank F2 (F ⧸ B) =
      finrank F2 (F ⧸ p.val.2.1) + finrank F2 p.val.2.2.range := by
  rcases p with ⟨⟨A0, B0, X⟩, hA, hB, hK, hR⟩
  change finrank F2 (F ⧸ B) = finrank F2 (F ⧸ B0) + finrank F2 X.range
  have hKB : finrank F2 X.ker = finrank F2 B := by
    rw [hK]
    exact (SubmoduleInterval.lowerIntervalSpaceEquiv B0 ⟨B, hB⟩).finrank_eq.symm
  have h := X.finrank_range_add_finrank_ker
  rw [hKB] at h
  have hBdim := B.finrank_quotient_add_finrank
  have hB0dim := B0.finrank_quotient_add_finrank
  omega

def size (q : Triple (E := E) (F := F)) : Nat :=
  order q.1 q.2.1 + finrank F2 q.2.2.range

theorem weak_order {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) :
    order A B = order p.val.1 p.val.2.1 + 2 * finrank F2 p.val.2.2.range := by
  have ha := dim_weakA p
  have hb := codim_weakB p
  dsimp only [order]
  omega

theorem order_eq_zero_iff (A : Submodule F2 E) (B : Submodule F2 F) :
    order A B = 0 ↔ A = ⊥ ∧ B = ⊤ := by
  constructor
  · intro h
    change finrank F2 A + finrank F2 (F ⧸ B) = 0 at h
    have ha : finrank F2 A = 0 := by omega
    have hb : finrank F2 (F ⧸ B) = 0 := by omega
    refine ⟨Submodule.finrank_eq_zero.mp ha, ?_⟩
    apply Submodule.eq_top_iff_finrank_eq.mpr
    have hq := B.finrank_quotient_add_finrank
    omega
  · rintro ⟨rfl, rfl⟩
    simpa [order] using
      (Module.finrank_eq_zero_of_subsingleton F2 (F ⧸ (⊤ : Submodule F2 F)))

theorem valid_positive_iff {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) :
    (A, B) ≠ (⊥, ⊤) ↔ 0 < size p.val := by
  have h := weak_order p
  constructor
  · intro hp
    by_contra ht
    have hz : order A B = 0 := by
      dsimp only [size] at ht
      omega
    rcases (order_eq_zero_iff A B).mp hz with ⟨hA, hB⟩
    exact hp (Prod.ext hA hB)
  · intro ht hp
    have hAB : A = ⊥ ∧ B = ⊤ := Prod.mk.inj hp
    have hz := (order_eq_zero_iff A B).mpr hAB
    dsimp only [size] at ht
    omega

abbrev WeakPositive :=
  {p : Submodule F2 E × Submodule F2 F // p ≠ (⊥, ⊤)}

abbrev PositiveWitness :=
  Σ p : WeakPositive (E := E) (F := F), A4IndexCount.Index p.val.1 p.val.2

abbrev PositiveTriple := {q : Triple (E := E) (F := F) // 0 < size q}

abbrev BoundedPositiveTriple (d : Nat) :=
  {q : Triple (E := E) (F := F) // 0 < size q ∧ size q ≤ d}

def positiveMap (p : PositiveWitness (E := E) (F := F)) :
    PositiveTriple (E := E) (F := F) :=
  ⟨p.2.val, (valid_positive_iff p.2).mp p.1.property⟩

theorem positiveMap_injective :
    Function.Injective (positiveMap (E := E) (F := F)) := by
  rintro ⟨⟨⟨A, B⟩, hp⟩, p⟩ ⟨⟨⟨A', B'⟩, hp'⟩, p'⟩ he
  have hraw : p.val = p'.val := congrArg Subtype.val he
  have hA : A = A' := by
    calc
      A = weakA p.val := (recover_weakA p).symm
      _ = weakA p'.val := congrArg weakA hraw
      _ = A' := recover_weakA p'
  have hB : B = B' := by
    calc
      B = weakB p.val := (recover_weakB p).symm
      _ = weakB p'.val := congrArg weakB hraw
      _ = B' := recover_weakB p'
  cases hA
  cases hB
  have hpp : p = p' := Subtype.ext hraw
  cases hpp
  rfl

def positiveInverse (q : PositiveTriple (E := E) (F := F)) :
    PositiveWitness (E := E) (F := F) :=
  ⟨⟨(weakA q.val, weakB q.val),
      (valid_positive_iff ⟨q.val, canonicalValid q.val⟩).mpr q.property⟩,
    ⟨q.val, canonicalValid q.val⟩⟩

def positiveEquiv : PositiveWitness (E := E) (F := F) ≃
    PositiveTriple (E := E) (F := F) :=
  Equiv.ofBijective positiveMap ⟨positiveMap_injective, by
    intro q
    refine ⟨positiveInverse q, ?_⟩
    exact Subtype.ext rfl⟩

@[simp] theorem positiveMap_val (p : PositiveWitness (E := E) (F := F)) :
    (positiveMap p).val = p.2.val := rfl

@[simp] theorem positiveEquiv_val (p : PositiveWitness (E := E) (F := F)) :
    (positiveEquiv p).val = p.2.val := rfl

@[instance_reducible]
def tripleFintype [Finite E] [Finite F] :
    Fintype (Triple (E := E) (F := F)) := by
  classical
  letI : Fintype (Submodule F2 E) := SubspaceExtensions.subspaceFintype
  letI : Fintype (Submodule F2 F) := SubspaceExtensions.subspaceFintype
  letI (A : Submodule F2 E) : Finite (E ⧸ A) :=
    Finite.of_surjective A.mkQ A.mkQ_surjective
  letI (A : Submodule F2 E) (B : Submodule F2 F) :
      Fintype (B →ₗ[F2] (E ⧸ A)) := by
    letI : Fintype B := Fintype.ofFinite _
    letI : Fintype (E ⧸ A) := Fintype.ofFinite _
    exact Fintype.ofInjective (fun L : B →ₗ[F2] (E ⧸ A) =>
      (L : B → E ⧸ A)) DFunLike.coe_injective
  exact inferInstance

@[instance_reducible]
def weakPositiveFintype [Finite E] [Finite F] :
    Fintype (WeakPositive (E := E) (F := F)) := by
  classical
  letI : Fintype (Submodule F2 E) := SubspaceExtensions.subspaceFintype
  letI : Fintype (Submodule F2 F) := SubspaceExtensions.subspaceFintype
  exact inferInstance

@[instance_reducible]
def geometricIndexFintype [Finite E] [Finite F]
    (A : Submodule F2 E) (B : Submodule F2 F) :
    Fintype (A4IndexCount.Index A B) := by
  classical
  letI := tripleFintype (E := E) (F := F)
  exact inferInstance

@[instance_reducible]
def positiveWitnessFintype [Finite E] [Finite F] :
    Fintype (PositiveWitness (E := E) (F := F)) := by
  classical
  letI := weakPositiveFintype (E := E) (F := F)
  letI (A : Submodule F2 E) (B : Submodule F2 F) := geometricIndexFintype A B
  exact inferInstance

@[instance_reducible]
def positiveTripleFintype [Finite E] [Finite F] :
    Fintype (PositiveTriple (E := E) (F := F)) := by
  classical
  letI := tripleFintype (E := E) (F := F)
  exact inferInstance

@[instance_reducible]
def boundedPositiveTripleFintype [Finite E] [Finite F] (d : Nat) :
    Fintype (BoundedPositiveTriple (E := E) (F := F) d) := by
  classical
  letI := tripleFintype (E := E) (F := F)
  exact inferInstance

end MaxCutGames.Appendix.A13Index
end

namespace MaxCutGames.Appendix.TotalPredecessorCount
open Module
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Appendix.RankAdditivity
variable {E F : Type*} [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

noncomputable def predecessorEnd (Y : E →ₗ[F2] F)
    (R : {R : E →ₗ[F2] F // RankBelow R Y}) : Y.range →ₗ[F2] Y.range :=
  let R' : E →ₗ[F2] Y.range := R.val.codRestrict Y.range
    (fun x => range_le_of_rankBelow R.val Y R.property ⟨x,rfl⟩)
  let hker : Y.ker ≤ R'.ker := by
    intro x hx
    exact Subtype.ext (ker_le_of_rankBelow R.val Y R.property hx)
  (Y.ker.liftQ R' hker).comp Y.quotKerEquivRange.symm.toLinearMap

end MaxCutGames.Appendix.TotalPredecessorCount

/-! Products and the fourth moment for the actual binary trace Fourier model. -/

noncomputable section

/-! The actual F1 witness bound in Lemma A.1. Coefficients remain signed;
absolute values occur only in the majorant. The two predecessor counts and
Cauchy–Schwarz give the factor `2^(6*d^2)`. -/
namespace MaxCutGames.Appendix.F1Energy
open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Appendix.RankAdditivity
variable {E F : Type*} [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
local notation "G" => (E →ₗ[F2] F)
attribute [local instance] Classical.propDecidable

def rank (Y : G) : ℕ := Module.finrank F2 Y.range

def Good (X Y : G) : Prop :=
  ∃ R : G, RankBelow R X ∧ RankBelow R Y ∧ RankBelow (X + R) (X + Y)

abbrev BoundedSplit (d : ℕ) (X : G) :=
  {R : G // RankBelow R X ∧ rank R ≤ d ∧ rank (X + R) ≤ d}

theorem add_self_cancel (X R : G) : (X + R) + R = X := by
  rw [add_assoc, DegreeCover.binary_add_self, add_zero]

def translate (R : G) : G ≃ G where
  toFun X := X + R
  invFun X := X + R
  left_inv X := add_self_cancel X R
  right_inv X := add_self_cancel X R

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

variable [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)]

def predecessorCoefficient (a : G → ℝ) (R C : G) : ℝ :=
  if RankBelow R (R+C) then |a (R+C)| else 0

def gram (a : G → ℝ) (R S : G) : ℝ :=
  ∑ C, predecessorCoefficient a R C * predecessorCoefficient a S C

def predecessorEnergy (a : G → ℝ) : ℝ :=
  ∑ R, ∑ C, predecessorCoefficient a R C ^ 2

def goodConvolution (a : G → ℝ) (X : G) : ℝ :=
  ∑ Y, if Good X Y then |a Y| * |a (X+Y)| else 0

open MaxCutGames.Fourier.MatrixFourier

end MaxCutGames.Appendix.F1Energy
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_UpperMobius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MaxCutGames.Appendix.UpperMobius
open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear
attribute [local instance] Classical.propDecidable
variable {W : Type*} [AddCommGroup W] [Module F2 W]
  [FiniteDimensional F2 W] [Finite W]

local instance quotientFinite (K : Submodule F2 W) : Finite (W ⧸ K) :=
  Finite.of_surjective K.mkQ K.mkQ_surjective

local instance dualFinite {V : Type*} [AddCommGroup V] [Module F2 V] [Finite V] :
    Finite (Module.Dual F2 V) :=
  Finite.of_injective (fun f : Module.Dual F2 V => (f : V → F2)) DFunLike.coe_injective

local instance submoduleFinite {V : Type*} [AddCommGroup V] [Module F2 V] [Finite V] :
    Finite (Submodule F2 V) :=
  Finite.of_injective (fun S : Submodule F2 V => (S : Set V)) SetLike.coe_injective

noncomputable def upperQuotientEquiv (K : Submodule F2 W) :
    {B : Submodule F2 W // K ≤ B} ≃ Submodule F2 (W ⧸ K) :=
  (Submodule.comapMkQRelIso K).symm.toEquiv

noncomputable def dualSubspaceEquiv (V : Type*) [AddCommGroup V]
    [Module F2 V] [FiniteDimensional F2 V] :
    Submodule F2 V ≃ Submodule F2 (Module.Dual F2 V) :=
  (Subspace.orderIsoFiniteDimensional (K := F2) (V := V)).toEquiv

noncomputable def upperDualSubspaceEquiv (K : Submodule F2 W) :
    {B : Submodule F2 W // K ≤ B} ≃
      Submodule F2 (Module.Dual F2 (W ⧸ K)) :=
  (upperQuotientEquiv K).trans (dualSubspaceEquiv (W ⧸ K))

noncomputable def upperWeightedTotal (K : Submodule F2 W) (w : ℕ → ℤ) : ℤ := by
  classical
  letI := Fintype.ofFinite {B : Submodule F2 W // K ≤ B}
  exact ∑ B : {B : Submodule F2 W // K ≤ B}, w (Module.finrank F2 (W ⧸ B.val))

end MaxCutGames.Appendix.UpperMobius

open scoped BigOperators

namespace MaxCutGames.Appendix.DyadicError

def quarterSum (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, (1/4 : ℝ)^i

def quarterError (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
    if i=0 ∧ j=0 then 0 else (1/4 : ℝ)^(i+j)

def dyadicError (d : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (d+1), ∑ j ∈ Finset.range (d+1),
    if i=0 ∧ j=0 then 0 else (1/2 : ℝ)^(3*d*(i+j))

end MaxCutGames.Appendix.DyadicError
end

/-! The signed bad-convolution term of Appendix A.1.  The selector here is
the weak image/kernel selector, prior to its separate A.4 decomposition. -/
noncomputable section
namespace MaxCutGames.Appendix.BadConvolution
open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear (F2)
open Module (finrank)
attribute [local instance] Classical.propDecidable

variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V]

def Incidence (A : Submodule F2 V) (B : Submodule F2 W) (Y : W →ₗ[F2] V) : Prop :=
  A ≤ Y.range ∧ Y.ker ≤ B

def Bad (X Y : W →ₗ[F2] V) : Prop :=
  (X.range ⊓ Y.range) ⊓ (X+Y).range ≠ ⊥ ∨
    (X.ker ⊔ Y.ker) ⊔ (X+Y).ker ≠ ⊤

def filteredCoefficient (A : Submodule F2 V) (B : Submodule F2 W)
    (a : (W →ₗ[F2] V) → ℝ) (Y : W →ₗ[F2] V) : ℝ :=
  if Incidence A B Y then a Y else 0

def mobius (i : ℕ) : ℝ := (-1:ℝ)^i * 2^(i.choose 2)

def pairDimension (p : Submodule F2 V × Submodule F2 W) : ℕ :=
  finrank F2 p.1 + finrank F2 (W ⧸ p.2)

def pairWeight (p : Submodule F2 V × Submodule F2 W) : ℝ :=
  mobius (finrank F2 p.1) * mobius (finrank F2 (W ⧸ p.2))

def signedWeight (p : Submodule F2 V × Submodule F2 W) : ℝ :=
  if p = (⊥,⊤) then 0 else -pairWeight p

section FiniteSums
variable [Fintype (W →ₗ[F2] V)]

def pieceConvolution (A : Submodule F2 V) (B : Submodule F2 W)
    (a : (W →ₗ[F2] V) → ℝ) (X : W →ₗ[F2] V) : ℝ :=
  ∑ Y, filteredCoefficient A B a Y * filteredCoefficient A B a (X+Y)

def badConvolution (a : (W →ₗ[F2] V) → ℝ) (X : W →ₗ[F2] V) : ℝ :=
  ∑ Y, if Bad X Y then a Y * a (X+Y) else 0
end FiniteSums

end MaxCutGames.Appendix.BadConvolution
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_A1Reduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MaxCutGames.Appendix.A1Reduction
open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Appendix.Derivatives
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)]

def weakFourthSum (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ p : Submodule F2 E × Submodule F2 F,
    if p ≠ (⊥, ⊤) then
      (2:ℝ)^(7*d*(Module.finrank F2 p.1 + Module.finrank F2 (F ⧸ p.2))) *
        (𝔼 M, spectralProjector (fun Y => p.1 ≤ Y.range ∧ Y.ker ≤ p.2) f M^4)
    else 0

end MaxCutGames.Appendix.A1Reduction

open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Fourier
open MaxCutGames.Appendix.Derivatives
open MaxCutGames.Appendix.OperatorPartitions
open MaxCutGames.Appendix.LinearIdentities

namespace MaxCutGames.Appendix.A13Reduction

attribute [local instance] Classical.propDecidable

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F]

attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype

/-- The actual averaged fourth moment attached to a raw derivative triple. -/
def tripleMoment (p : A4Index (K := F2) (W := F) (V := E))
    (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  𝔼 T, 𝔼 N, mapDerivative p.2.2 (hybridDerivative p.1 p.2.1 T f) N ^ 4

/-- The weight after relabeling the actual raw derivative triple. -/
def tripleTerm (d : ℕ) (p : A13Index.Triple (E := E) (F := F))
    (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  (2 : ℝ) ^ (24 * d * A13Index.size p) * tripleMoment p f

variable [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)]

/-- The displayed A.13 sum: its original positive total order is retained. -/
def positiveTripleSum (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ p : A13Index.PositiveTriple (E := E) (F := F), tripleTerm d p.val f

/-- The same sum after the genuine degree-support cutoff. -/
def boundedPositiveTripleSum (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ p : A13Index.BoundedPositiveTriple (E := E) (F := F) d, tripleTerm d p.val f

end MaxCutGames.Appendix.A13Reduction
end

namespace MaxCutGames.Appendix.DerivativeInduction

open MaxCutGames.Integration.BinaryLinear
open LinearMap

variable {B U A C : Type*}
variable [AddCommGroup B] [Module F2 B] [AddCommGroup U] [Module F2 U]
variable [AddCommGroup A] [Module F2 A] [AddCommGroup C] [Module F2 C]

/-- The actual complement conditions after choosing domain/codomain splittings. -/
def IsAntecedent (Z : B →ₗ[F2] C) (X : (B × U) →ₗ[F2] (A × C)) : Prop :=
  (∀ b, (X (b, 0)).2 = Z b) ∧
  Disjoint X.range (LinearMap.inl F2 A C).range ∧
  (LinearMap.inl F2 B U).range ⊔ X.ker = ⊤

abbrev Antecedent (Z : B →ₗ[F2] C) :=
  { X : (B × U) →ₗ[F2] (A × C) // IsAntecedent Z X }

theorem antecedent_image_from_left (Z : B →ₗ[F2] C)
    (X : (B × U) →ₗ[F2] (A × C)) (hX : IsAntecedent Z X) (p : B × U) :
    ∃ b : B, X p = X (b, 0) := by
  have hp : p ∈ (LinearMap.inl F2 B U).range ⊔ X.ker := by
    rw [hX.2.2]
    trivial
  obtain ⟨q, hq, r, hr, he⟩ := Submodule.mem_sup.mp hp
  obtain ⟨b, rfl⟩ := hq
  refine ⟨b, ?_⟩
  rw [← he, map_add]
  have hz : X r = 0 := hr
  simp only [hz, add_zero, LinearMap.inl_apply]

theorem antecedent_bottom_mem_range (Z : B →ₗ[F2] C)
    (X : (B × U) →ₗ[F2] (A × C)) (hX : IsAntecedent Z X) (p : B × U) :
    (X p).2 ∈ Z.range := by
  obtain ⟨b, hb⟩ := antecedent_image_from_left Z X hX p
  exact ⟨b, (hX.1 b).symm.trans (congrArg Prod.snd hb).symm⟩

theorem antecedent_vertical_zero (Z : B →ₗ[F2] C)
    (X : (B × U) →ₗ[F2] (A × C)) (hX : IsAntecedent Z X)
    (p : B × U) (hp : (X p).2 = 0) : X p = 0 := by
  apply Submodule.disjoint_def.mp hX.2.1 (X p) (LinearMap.mem_range_self X p)
  exact ⟨(X p).1, Prod.ext rfl hp.symm⟩

theorem antecedent_kernel_le_inline_DerivativeInduction (Z : B →ₗ[F2] C)
    (X : (B × U) →ₗ[F2] (A × C)) (hX : IsAntecedent Z X) :
    Z.ker ≤ ((LinearMap.fst F2 A C).comp (X.comp (LinearMap.inl F2 B U))).ker := by
  intro b hb
  have hz : Z b = 0 := hb
  have hx := antecedent_vertical_zero Z X hX (b, 0) ((hX.1 b).trans hz)
  exact congrArg Prod.fst hx

/-- The graph map from the fixed compressed image into the removed summand. -/
noncomputable def graphParameter (Z : B →ₗ[F2] C)
    (X : Antecedent (U := U) (A := A) Z) : Z.range →ₗ[F2] A :=
  (Z.ker.liftQ ((LinearMap.fst F2 A C).comp
    (X.val.comp (LinearMap.inl F2 B U))) (antecedent_kernel_le_inline_DerivativeInduction Z X.val X.property)).comp
    Z.quotKerEquivRange.symm.toLinearMap

theorem graphParameter_apply (Z : B →ₗ[F2] C)
    (X : Antecedent (U := U) (A := A) Z) (b : B) :
    graphParameter Z X (Z.rangeRestrict b) = (X.val (b, 0)).1 := by
  rw [show Z.rangeRestrict b = ⟨Z b, LinearMap.mem_range_self Z b⟩ from rfl]
  simp [graphParameter, LinearMap.quotKerEquivRange_symm_apply_image]

/-- Values on the omitted domain complement, compressed into `range Z`. -/
noncomputable def complementParameter (Z : B →ₗ[F2] C)
    (X : Antecedent (U := U) (A := A) Z) : U →ₗ[F2] Z.range :=
  ((LinearMap.snd F2 A C).comp (X.val.comp (LinearMap.inr F2 B U))).codRestrict
    Z.range (fun u => antecedent_bottom_mem_range Z X.val X.property (0, u))

@[simp] theorem complementParameter_val (Z : B →ₗ[F2] C)
    (X : Antecedent (U := U) (A := A) Z) (u : U) :
    (complementParameter Z X u : C) = (X.val (0, u)).2 := rfl

/-- The block matrix `[F Z, F H; Z, H]`. -/
def lift (Z : B →ₗ[F2] C) (F : Z.range →ₗ[F2] A) (H : U →ₗ[F2] Z.range) :
    (B × U) →ₗ[F2] (A × C) :=
  (F.comp (Z.rangeRestrict.coprod H)).prod
    (Z.range.subtype.comp (Z.rangeRestrict.coprod H))

@[simp] theorem lift_apply (Z : B →ₗ[F2] C)
    (F : Z.range →ₗ[F2] A) (H : U →ₗ[F2] Z.range) (p : B × U) :
    lift Z F H p = (F (Z.rangeRestrict p.1 + H p.2),
      ((Z.rangeRestrict p.1 + H p.2 : Z.range) : C)) := rfl

theorem lift_isAntecedent (Z : B →ₗ[F2] C)
    (F : Z.range →ₗ[F2] A) (H : U →ₗ[F2] Z.range) :
    IsAntecedent Z (lift Z F H) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b
    simp
  · apply Submodule.disjoint_def.mpr
    intro v hv hw
    obtain ⟨p, rfl⟩ := hv
    obtain ⟨a, ha⟩ := hw
    have hz : Z.rangeRestrict p.1 + H p.2 = 0 := by
      apply Subtype.ext
      exact (congrArg Prod.snd ha).symm
    simp [hz]
  · apply top_unique
    intro p _
    obtain ⟨b, hb⟩ := Z.surjective_rangeRestrict (Z.rangeRestrict p.1 + H p.2)
    have he : lift Z F H p = lift Z F H (b, 0) := by
      simp [hb]
    apply Submodule.mem_sup.mpr
    refine ⟨(b, 0), ⟨b, rfl⟩, p - (b, 0), ?_, ?_⟩
    · change lift Z F H (p - (b, 0)) = 0
      rw [map_sub, he, sub_self]
    · simpa only [← add_sub_assoc] using add_sub_cancel_left (b, 0) p

def intoAntecedent (Z : B →ₗ[F2] C)
    (p : (Z.range →ₗ[F2] A) × (U →ₗ[F2] Z.range)) :
    Antecedent (U := U) (A := A) Z :=
  ⟨lift Z p.1 p.2, lift_isAntecedent Z p.1 p.2⟩

theorem graphParameter_lift (Z : B →ₗ[F2] C)
    (F : Z.range →ₗ[F2] A) (H : U →ₗ[F2] Z.range) :
    graphParameter Z (intoAntecedent Z (F, H)) = F := by
  ext c
  obtain ⟨b, rfl⟩ := Z.surjective_rangeRestrict c
  rw [graphParameter_apply]
  simp [intoAntecedent]

theorem complementParameter_lift (Z : B →ₗ[F2] C)
    (F : Z.range →ₗ[F2] A) (H : U →ₗ[F2] Z.range) :
    complementParameter Z (intoAntecedent Z (F, H)) = H := by
  ext u
  simp [intoAntecedent]

theorem lift_parameters (Z : B →ₗ[F2] C)
    (X : Antecedent (U := U) (A := A) Z) :
    lift Z (graphParameter Z X) (complementParameter Z X) = X.val := by
  apply LinearMap.ext
  intro p
  have hb : (Z.rangeRestrict p.1 + complementParameter Z X p.2 : C) = (X.val p).2 := by
    have hp : p = (p.1, 0) + (0, p.2) := by simp
    conv_rhs => rw [hp, map_add]
    simp [X.property.1]
  obtain ⟨b, he⟩ := antecedent_image_from_left Z X.val X.property p
  have hr : Z.rangeRestrict p.1 + complementParameter Z X p.2 = Z.rangeRestrict b := by
    apply Subtype.ext
    exact hb.trans ((congrArg Prod.snd he).trans (X.property.1 b))
  apply Prod.ext
  · change graphParameter Z X (Z.rangeRestrict p.1 + complementParameter Z X p.2) = _
    rw [hr, graphParameter_apply]
    exact (congrArg Prod.fst he).symm
  · exact hb

/-- Exact antecedent bijection; neither direction assumes the desired count. -/
noncomputable def antecedentEquiv (Z : B →ₗ[F2] C) :
    Antecedent (U := U) (A := A) Z ≃
      (Z.range →ₗ[F2] A) × (U →ₗ[F2] Z.range) where
  toFun X := (graphParameter Z X, complementParameter Z X)
  invFun := intoAntecedent Z
  left_inv X := Subtype.ext (lift_parameters Z X)
  right_inv p := Prod.ext (graphParameter_lift Z p.1 p.2)
    (complementParameter_lift Z p.1 p.2)

theorem isAntecedent_iff_pointwise (Z : B →ₗ[F2] C)
    (X : (B × U) →ₗ[F2] (A × C)) :
    IsAntecedent Z X ↔
      (∀ b, (X (b, 0)).2 = Z b) ∧
      (∀ p, (X p).2 = 0 → X p = 0) ∧
      (∀ p, ∃ b, X p = X (b, 0)) := by
  constructor
  · intro h
    exact ⟨h.1, antecedent_vertical_zero Z X h, antecedent_image_from_left Z X h⟩
  · rintro ⟨hc, hv, hs⟩
    refine ⟨hc, Submodule.disjoint_def.mpr ?_, top_unique ?_⟩
    · rintro v ⟨p, rfl⟩ ⟨a, ha⟩
      exact hv p (congrArg Prod.snd ha).symm
    · intro p _
      obtain ⟨b, hb⟩ := hs p
      apply Submodule.mem_sup.mpr
      refine ⟨(b, 0), ⟨b, rfl⟩, p - (b, 0), ?_, ?_⟩
      · change X (p - (b, 0)) = 0
        rw [map_sub, hb, sub_self]
      · simpa only [← add_sub_assoc] using add_sub_cancel_left (b, 0) p

variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V]

theorem disjoint_range_iff_zero (X : W →ₗ[F2] V) (Q : Submodule F2 V) :
    Disjoint X.range Q ↔ ∀ w, X w ∈ Q → X w = 0 := by
  constructor
  · intro h w hw
    exact Submodule.disjoint_def.mp h (X w) (LinearMap.mem_range_self X w) hw
  · intro h
    apply Submodule.disjoint_def.mpr
    rintro v ⟨w, rfl⟩ hw
    exact h w hw

theorem sup_kernel_iff_image (X : W →ₗ[F2] V) (P : Submodule F2 W) :
    P ⊔ X.ker = ⊤ ↔ ∀ w, ∃ p : P, X w = X p := by
  constructor
  · intro h w
    have hw : w ∈ P ⊔ X.ker := by rw [h]; trivial
    obtain ⟨p, hp, r, hr, he⟩ := Submodule.mem_sup.mp hw
    refine ⟨⟨p, hp⟩, ?_⟩
    rw [← he, map_add]
    have hz : X r = 0 := hr
    simp [hz]
  · intro h
    apply top_unique
    intro w _
    obtain ⟨p, hp⟩ := h w
    apply Submodule.mem_sup.mpr
    refine ⟨p, p.property, w - p, ?_, ?_⟩
    · change X (w - p) = 0
      rw [map_sub, hp, sub_self]
    · simpa only [← add_sub_assoc] using add_sub_cancel_left (p : W) w

/-- Antecedents on arbitrary subspaces. Projection onto the chosen complement
is the quotient compression expressed through `quotientEquivOfIsCompl`. -/
def IsSubspaceAntecedent (P : Submodule F2 W) (Q D : Submodule F2 V)
    (hQ : IsCompl Q D) (Z : P →ₗ[F2] D) (X : W →ₗ[F2] V) : Prop :=
  (∀ p : P, D.projectionOnto Q hQ.symm (X p) = Z p) ∧
  Disjoint X.range Q ∧ P ⊔ X.ker = ⊤

abbrev SubspaceAntecedent (P : Submodule F2 W) (Q D : Submodule F2 V)
    (hQ : IsCompl Q D) (Z : P →ₗ[F2] D) :=
  { X : W →ₗ[F2] V // IsSubspaceAntecedent P Q D hQ Z X }

noncomputable def coordinateEquiv (P E : Submodule F2 W) (Q D : Submodule F2 V)
    (hP : IsCompl P E) (hQ : IsCompl Q D) :
    (W →ₗ[F2] V) ≃ₗ[F2] ((P × E) →ₗ[F2] (Q × D)) :=
  LinearEquiv.arrowCongr (P.prodEquivOfIsCompl E hP).symm
    (Q.prodEquivOfIsCompl D hQ).symm

@[simp] theorem coordinateEquiv_apply (P E : Submodule F2 W)
    (Q D : Submodule F2 V) (hP : IsCompl P E) (hQ : IsCompl Q D)
    (X : W →ₗ[F2] V) (p : P × E) :
    coordinateEquiv P E Q D hP hQ X p =
      (Q.prodEquivOfIsCompl D hQ).symm (X ((p.1 : W) + p.2)) := rfl

theorem coordinate_antecedent_iff (P E : Submodule F2 W)
    (Q D : Submodule F2 V) (hP : IsCompl P E) (hQ : IsCompl Q D)
    (Z : P →ₗ[F2] D) (X : W →ₗ[F2] V) :
    IsAntecedent Z (coordinateEquiv P E Q D hP hQ X) ↔
      IsSubspaceAntecedent P Q D hQ Z X := by
  rw [isAntecedent_iff_pointwise]
  unfold IsSubspaceAntecedent
  rw [disjoint_range_iff_zero, sup_kernel_iff_image]
  constructor
  · rintro ⟨hc, hv, hs⟩
    refine ⟨?_, ?_, ?_⟩
    · intro p
      simpa using hc p
    · intro w hw
      let p := (P.prodEquivOfIsCompl E hP).symm w
      have hp : (p.1 : W) + p.2 = w :=
        (P.prodEquivOfIsCompl E hP).apply_symm_apply w
      have hz : (coordinateEquiv P E Q D hP hQ X p).2 = 0 := by
        rw [coordinateEquiv_apply, hp]
        exact (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero Q D hQ).mpr hw
      have hh := congrArg (Q.prodEquivOfIsCompl D hQ) (hv p hz)
      simpa only [coordinateEquiv_apply, hp, LinearEquiv.apply_symm_apply, map_zero] using hh
    · intro w
      let p := (P.prodEquivOfIsCompl E hP).symm w
      have hp : (p.1 : W) + p.2 = w :=
        (P.prodEquivOfIsCompl E hP).apply_symm_apply w
      obtain ⟨b, hb⟩ := hs p
      refine ⟨b, ?_⟩
      have hh := congrArg (Q.prodEquivOfIsCompl D hQ) hb
      simpa only [coordinateEquiv_apply, hp, Submodule.coe_zero, add_zero,
        LinearEquiv.apply_symm_apply] using hh
  · rintro ⟨hc, hv, hs⟩
    refine ⟨?_, ?_, ?_⟩
    · intro p
      simpa using hc p
    · intro p hp
      have hm : X ((p.1 : W) + p.2) ∈ Q :=
        (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero Q D hQ).mp hp
      have hz := hv ((p.1 : W) + p.2) hm
      simp [hz]
    · intro p
      obtain ⟨b, hb⟩ := hs ((p.1 : W) + p.2)
      refine ⟨b, ?_⟩
      simpa only [coordinateEquiv_apply, Submodule.coe_zero, add_zero] using
        congrArg (Q.prodEquivOfIsCompl D hQ).symm hb

/-- Transport the canonical antecedent count to arbitrary complementary subspaces. -/
noncomputable def subspaceAntecedentEquiv (P E : Submodule F2 W)
    (Q D : Submodule F2 V) (hP : IsCompl P E) (hQ : IsCompl Q D)
    (Z : P →ₗ[F2] D) :
    SubspaceAntecedent P Q D hQ Z ≃
      (Z.range →ₗ[F2] Q) × (E →ₗ[F2] Z.range) :=
  (Equiv.subtypeEquiv (coordinateEquiv P E Q D hP hQ).toEquiv
    (fun X => (coordinate_antecedent_iff P E Q D hP hQ Z X).symm)).trans
    (antecedentEquiv Z)

end MaxCutGames.Appendix.DerivativeInduction

/-!
# Exact antecedents of quotient compression

This is the reverse-map count used in Proposition A.5. The compressed map is
fixed, together with the two removed subspaces; neither a prescribed rank nor
an assumed cardinality is part of the antecedent predicate.
-/

namespace MaxCutGames.Appendix.AntecedentCount

open MaxCutGames.Integration.BinaryLinear
open LinearIdentities
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V]

/-- Actual quotient-compression antecedents with the complement conditions
in the passage from (A.15) to (A.16). -/
def IsAntecedent (P : Submodule F2 W) (Q : Submodule F2 V)
    (Y : P →ₗ[F2] (V ⧸ Q)) (X : W →ₗ[F2] V) : Prop :=
  compress X Q P = Y ∧ Disjoint X.range Q ∧ P ⊔ X.ker = ⊤

abbrev Antecedent (P : Submodule F2 W) (Q : Submodule F2 V)
    (Y : P →ₗ[F2] (V ⧸ Q)) :=
  {X : W →ₗ[F2] V // IsAntecedent P Q Y X}

/-- Choosing a codomain complement only changes the coordinates of the fixed
compressed output. -/
theorem isAntecedent_iff_subspace (P : Submodule F2 W)
    (Q D : Submodule F2 V) (hQ : IsCompl Q D)
    (Y : P →ₗ[F2] (V ⧸ Q)) (X : W →ₗ[F2] V) :
    IsAntecedent P Q Y X ↔
      DerivativeInduction.IsSubspaceAntecedent P Q D hQ
        ((Q.quotientEquivOfIsCompl D hQ).toLinearMap.comp Y) X := by
  constructor
  · rintro ⟨hXY, hd, hk⟩
    refine ⟨?_, hd, hk⟩
    intro p
    have h := LinearMap.congr_fun hXY p
    exact congrArg (Q.quotientEquivOfIsCompl D hQ) h
  · rintro ⟨hXY, hd, hk⟩
    refine ⟨?_, hd, hk⟩
    ext p
    apply (Q.quotientEquivOfIsCompl D hQ).injective
    exact hXY p

/-- The quotient antecedents and the graph-coordinate antecedents are the
same maps, with equivalent predicates. -/
def subspaceEquiv (P : Submodule F2 W) (Q D : Submodule F2 V)
    (hQ : IsCompl Q D) (Y : P →ₗ[F2] (V ⧸ Q)) :
    Antecedent P Q Y ≃ DerivativeInduction.SubspaceAntecedent P Q D hQ
      ((Q.quotientEquivOfIsCompl D hQ).toLinearMap.comp Y) where
  toFun X := ⟨X.val, (isAntecedent_iff_subspace P Q D hQ Y X.val).mp X.property⟩
  invFun X := ⟨X.val, (isAntecedent_iff_subspace P Q D hQ Y X.val).mpr X.property⟩
  left_inv _X := rfl
  right_inv _X := rfl

end

end MaxCutGames.Appendix.AntecedentCount

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_A5ReverseIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Appendix.A5ReverseIndex

open MaxCutGames.Integration.BinaryLinear
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V W : Type*} [AddCommGroup V] [Module F2 V]
  [AddCommGroup W] [Module F2 W]

/-- Earlier codomain constraints inside the final codomain constraint. -/
abbrev EarlierA (A' : Submodule F2 V) (i : ℕ) :=
  {A : Submodule F2 V // A ≤ A' ∧ Module.finrank F2 A = i}

/-- Earlier retained domains containing the final retained domain. -/
abbrev EarlierB (B' : Submodule F2 W) (j : ℕ) :=
  {B : Submodule F2 W // B' ≤ B ∧ Module.finrank F2 (W ⧸ B) = j}

/-- Natural frequency coordinates for an earlier pair inside a fixed final
pair. This is a change of domain and codomain separately. -/
def frequencyEquiv (A A' : Submodule F2 V) (B' B : Submodule F2 W)
    (hA : A ≤ A') (hB : B' ≤ B) :
    (B' →ₗ[F2] (V ⧸ A')) ≃ₗ[F2]
      ((B'.comap B.subtype) →ₗ[F2] ((V ⧸ A) ⧸ A'.map A.mkQ)) :=
  LinearEquiv.arrowCongr
    (SubmoduleInterval.lowerIntervalSpaceEquiv B ⟨B', hB⟩)
    (Submodule.quotientQuotientEquivQuotient A A' hA).symm

def relativeFrequency (A A' : Submodule F2 V) (B' B : Submodule F2 W)
    (hA : A ≤ A') (hB : B' ≤ B) (Y : B' →ₗ[F2] (V ⧸ A')) :=
  frequencyEquiv A A' B' B hA hB Y

/-- The exact reverse fiber after the earlier dimensions are fixed. -/
abbrev Ancestor (A' : Submodule F2 V) (B' : Submodule F2 W)
    (Y : B' →ₗ[F2] (V ⧸ A')) (i j : ℕ) :=
  Σ A : EarlierA A' i, Σ B : EarlierB B' j,
    AntecedentCount.Antecedent (B'.comap B.val.subtype) (A'.map A.val.mkQ)
      (relativeFrequency A.val A' B' B.val A.property.1 B.property.1 Y)

end

end MaxCutGames.Appendix.A5ReverseIndex

/-! Pointwise identification of the natural frequency transport with the
relative frequency used by the actual reverse compression fibers. -/

noncomputable section
namespace MaxCutGames.Appendix.A5FrequencyTransport

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Appendix.LinearIdentities
open MaxCutGames.Appendix.NaturalTransport

variable {V W : Type*} [AddCommGroup V] [Module F2 V]
  [AddCommGroup W] [Module F2 W]

theorem quotient_relativeFrequency_apply
    (A A' : Submodule F2 V) (B' B : Submodule F2 W)
    (hA : A ≤ A') (hB : B' ≤ B)
    (Y : B' →ₗ[F2] (V ⧸ A')) (b : B'.comap B.subtype) :
    Submodule.quotientQuotientEquivQuotient A A' hA
      (A5ReverseIndex.relativeFrequency A A' B' B hA hB Y b) =
    Y ((SubmoduleInterval.lowerIntervalSpaceEquiv B ⟨B', hB⟩).symm b) := by
  change Submodule.quotientQuotientEquivQuotient A A' hA
      ((Submodule.quotientQuotientEquivQuotient A A' hA).symm
        (Y ((SubmoduleInterval.lowerIntervalSpaceEquiv B ⟨B', hB⟩).symm b))) = _
  exact (Submodule.quotientQuotientEquivQuotient A A' hA).apply_symm_apply _

theorem quotient_compress_apply
    (A A' : Submodule F2 V) (B' B : Submodule F2 W)
    (hA : A ≤ A') (X : B →ₗ[F2] (V ⧸ A)) (b : B'.comap B.subtype) :
    Submodule.quotientQuotientEquivQuotient A A' hA
      (compress X (A'.map A.mkQ) (B'.comap B.subtype) b) =
    Submodule.mapQ A A' LinearMap.id hA (X b.val) := rfl

/-- The relative compression equation follows from the concrete map to the
direct quotient on each element of the retained subspace. -/
theorem compression_eq_relativeFrequency_of_pointwise
    (A A' : Submodule F2 V) (B' B : Submodule F2 W)
    (hA : A ≤ A') (hB : B' ≤ B)
    (X : B →ₗ[F2] (V ⧸ A)) (Y : B' →ₗ[F2] (V ⧸ A'))
    (hY : ∀ b : B', Submodule.mapQ A A' LinearMap.id hA
      (X ⟨b.val, hB b.property⟩) = Y b) :
    compress X (A'.map A.mkQ) (B'.comap B.subtype) =
      A5ReverseIndex.relativeFrequency A A' B' B hA hB Y := by
  ext b
  apply (Submodule.quotientQuotientEquivQuotient A A' hA).injective
  rw [quotient_compress_apply, quotient_relativeFrequency_apply]
  exact hY ((SubmoduleInterval.lowerIntervalSpaceEquiv B ⟨B', hB⟩).symm b)

variable [FiniteDimensional F2 V] [FiniteDimensional F2 W]
  [Finite V] [Finite W]

omit [FiniteDimensional F2 V] [Finite V] in
theorem quotientFactor_mapQ
    (A : Submodule F2 V) (C : Submodule F2 (V ⧸ A))
    (hA : A ≤ C.comap A.mkQ) (u : V ⧸ A) :
    quotientFactor A C
      (Submodule.mapQ A (C.comap A.mkQ) LinearMap.id hA u) = C.mkQ u := by
  obtain ⟨x, rfl⟩ := A.mkQ_surjective u
  change quotientFactor A C ((C.comap A.mkQ).mkQ x) = C.mkQ (A.mkQ x)
  exact quotientFactor_mkQ A C x

omit [FiniteDimensional F2 V] [FiniteDimensional F2 W] [Finite V] [Finite W] in
theorem dualFactor_quotient
    (A : Submodule F2 V) (B : Submodule F2 W)
    (C : Submodule F2 (V ⧸ A)) (D : Submodule F2 B)
    (Z : D →ₗ[F2] ((V ⧸ A) ⧸ C)) (b : D.map B.subtype) :
    quotientFactor A C (dualFactor A B C D Z b) =
      Z ((outputFactor B D).symm b) := by
  change quotientFactor A C ((quotientFactor A C).symm
    (Z ((outputFactor B D).symm b))) = _
  exact (quotientFactor A C).apply_symm_apply _

omit [FiniteDimensional F2 W] [Finite W] in
theorem outputFactor_symm_as_inclusion
    (B : Submodule F2 W) (D : Submodule F2 B)
    (hB : D.map B.subtype ≤ B) (b : D.map B.subtype) :
    (((outputFactor B D).symm b : D) : B) = ⟨b.val, hB b.property⟩ := by
  apply Subtype.ext
  have hh := outputFactor_val B D ((outputFactor B D).symm b)
  rw [LinearEquiv.apply_symm_apply] at hh
  exact hh.symm

omit [FiniteDimensional F2 V] [FiniteDimensional F2 W] [Finite V] [Finite W] in
/-- The naturally transported local compression belongs to the precise
relative-frequency fiber used in `A5ReverseIndex.Ancestor`. -/
theorem compression_eq_relativeFrequency_dualFactor
    (A : Submodule F2 V) (B : Submodule F2 W)
    (C : Submodule F2 (V ⧸ A)) (D : Submodule F2 B)
    (hA : A ≤ C.comap A.mkQ) (hB : D.map B.subtype ≤ B)
    (X : B →ₗ[F2] (V ⧸ A)) :
    compress X ((C.comap A.mkQ).map A.mkQ) ((D.map B.subtype).comap B.subtype) =
      A5ReverseIndex.relativeFrequency A (C.comap A.mkQ) (D.map B.subtype) B hA hB
        (dualFactor A B C D (compress X C D)) := by
  apply compression_eq_relativeFrequency_of_pointwise
  intro b
  apply (quotientFactor A C).injective
  rw [quotientFactor_mapQ, dualFactor_quotient]
  change C.mkQ (X ⟨b.val, hB b.property⟩) =
    C.mkQ (X (((outputFactor B D).symm b : D) : B))
  rw [outputFactor_symm_as_inclusion B D hB b]

omit [FiniteDimensional F2 V] [FiniteDimensional F2 W] [Finite V] [Finite W] in
/-- Package the actual naturally transported label into its counted
antecedent fiber, retaining the original map as the witness. -/
theorem isAntecedent_relativeFrequency_dualFactor
    (A : Submodule F2 V) (B : Submodule F2 W)
    (C : Submodule F2 (V ⧸ A)) (D : Submodule F2 B)
    (hA : A ≤ C.comap A.mkQ) (hB : D.map B.subtype ≤ B)
    (X : B →ₗ[F2] (V ⧸ A))
    (hdis : Disjoint X.range C) (hcover : D ⊔ X.ker = ⊤) :
    AntecedentCount.IsAntecedent ((D.map B.subtype).comap B.subtype)
      ((C.comap A.mkQ).map A.mkQ)
      (A5ReverseIndex.relativeFrequency A (C.comap A.mkQ) (D.map B.subtype) B hA hB
        (dualFactor A B C D (compress X C D))) X := by
  refine ⟨compression_eq_relativeFrequency_dualFactor A B C D hA hB X, ?_, ?_⟩
  · rw [Submodule.map_comap_eq_of_surjective A.mkQ_surjective C]
    exact hdis
  · rw [Submodule.comap_map_eq_of_injective (f := B.subtype) Subtype.val_injective D]
    exact hcover

end MaxCutGames.Appendix.A5FrequencyTransport

namespace MaxCutGames.Appendix.A5ForwardIndex

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Fourier.MatrixRestrictions (order)
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

abbrev Index (d : ℕ) :=
  Σ r : A13Index.BoundedPositiveTriple (E := E) (F := F) d,
    A5Passage.Passage r.val.2.2 (d - A13Index.size r.val)

def descendant {d : ℕ} (a : Index (E := E) (F := F) d) :
    A13Index.Triple (E := E) (F := F) :=
  ⟨a.2.2.val.1.comap a.1.val.1.mkQ, a.2.2.val.2.map a.1.val.2.1.subtype,
    NaturalTransport.dualFactor a.1.val.1 a.1.val.2.1 a.2.2.val.1 a.2.2.val.2
      (LinearIdentities.compress a.1.val.2.2 a.2.2.val.1 a.2.2.val.2)⟩

def sourceI {d : ℕ} (a : Index (E := E) (F := F) d) : ℕ :=
  Module.finrank F2 a.1.val.1

def sourceJ {d : ℕ} (a : Index (E := E) (F := F) d) : ℕ :=
  Module.finrank F2 (F ⧸ a.1.val.2.1)

def targetRank (r : A13Index.Triple (E := E) (F := F)) : ℕ :=
  Module.finrank F2 r.2.2.range

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem earlierA_le {d : ℕ} (a : Index (E := E) (F := F) d) :
    a.1.val.1 ≤ (descendant a).1 := by
  intro x hx
  change a.1.val.1.mkQ x ∈ a.2.2.val.1
  rw [show a.1.val.1.mkQ x = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hx]
  exact a.2.2.val.1.zero_mem

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem earlierB_le {d : ℕ} (a : Index (E := E) (F := F) d) :
    (descendant a).2.1 ≤ a.1.val.2.1 := by
  rintro x ⟨b, hb, rfl⟩
  exact b.property

abbrev Fiber (d : ℕ) (r : A13Index.Triple (E := E) (F := F)) (i j : ℕ) :=
  {a : Index (E := E) (F := F) d //
    descendant a = r ∧ sourceI a = i ∧ sourceJ a = j}

/-- The encoder keeps the actual earlier pair and actual earlier map. -/
def encode (d : ℕ) (r : A13Index.Triple (E := E) (F := F)) (i j : ℕ)
    (a : Fiber d r i j) : A5ReverseIndex.Ancestor r.1 r.2.1 r.2.2 i j := by
  rcases a with ⟨a, hr, hi, hj⟩
  cases hr
  refine ⟨⟨a.1.val.1, earlierA_le a, hi⟩,
    ⟨a.1.val.2.1, earlierB_le a, hj⟩, ⟨a.1.val.2.2, ?_⟩⟩
  exact A5FrequencyTransport.isAntecedent_relativeFrequency_dualFactor
    a.1.val.1 a.1.val.2.1 a.2.2.val.1 a.2.2.val.2
    (earlierA_le a) (earlierB_le a) a.1.val.2.2
    a.2.2.property.1.symm a.2.2.property.2.2.1

def earlierTriple {A' : Submodule F2 E} {B' : Submodule F2 F}
    {Y : B' →ₗ[F2] (E ⧸ A')} {i j : ℕ}
    (a : A5ReverseIndex.Ancestor A' B' Y i j) : A13Index.Triple (E := E) (F := F) :=
  ⟨a.1.val, a.2.1.val, a.2.2.val⟩

local instance indexFintype (d : ℕ) : Fintype (Index (E := E) (F := F) d) := by
  letI := A13Index.boundedPositiveTripleFintype (E := E) (F := F) d
  exact inferInstance

end MaxCutGames.Appendix.A5ForwardIndex

open scoped BigOperators

namespace MaxCutGames.Appendix.A5WeightedReindex

attribute [local instance] Classical.propDecidable

variable {α β : Type*} [Fintype α] [Fintype β]

def fiber (result : α → β) (i j : α → ℕ) (b : β) (r s : ℕ) : Finset α :=
  Finset.univ.filter (fun a => result a = b ∧ i a = r ∧ j a = s)

end MaxCutGames.Appendix.A5WeightedReindex
end

/-!
# The actual weighted reversal in Appendix A.5

The forward index records an original positive triple and an actual A.5
passage. Its checked reverse-fiber bound permits finite weighted grouping.
The resulting weights are the moments of the actual transported derivatives.
No degree hypothesis or analytic induction hypothesis is used here.
-/

noncomputable section
namespace MaxCutGames.Appendix.A5ReverseSum

open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Fourier.MatrixRestrictions (order)
open Derivatives
open A5ForwardIndex

attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype
attribute [local instance] SubspaceExtensions.subspaceFintype

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

def actualMoment (f : (E →ₗ[F2] F) → ℝ)
    (r : A13Index.Triple (E := E) (F := F)) : ℝ :=
  𝔼 T, (𝔼 N, mapDerivative r.2.2 (hybridDerivative r.1 r.2.1 T f) N ^ 2) ^ 2

def targetWeight (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (r : A13Index.Triple (E := E) (F := F)) : ℝ :=
  if order r.1 r.2.1 ≤ d then actualMoment f r else 0

end MaxCutGames.Appendix.A5ReverseSum
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_A5Induction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual norm and induction steps for Proposition A.5. The universal degree
property below is the motive for strong induction on the degree; defining
that property does not assert its truth. -/

noncomputable section
namespace MaxCutGames.Appendix.A5Induction

open scoped BigOperators
open MaxCutGames.Fourier.MatrixCharacters MaxCutGames.Fourier.MatrixFourier
open MaxCutGames.Fourier.MatrixRestrictions
open MaxCutGames.Appendix.Derivatives MaxCutGames.Appendix.DerivativeDegree
open MaxCutGames.Appendix.LevelInequality (frequencyRank)
attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype
attribute [local instance] SubspaceExtensions.subspaceFintype

universe u v

/-- The strong-induction motive quantifies over the actual changing domains.
Quotients and subspaces preserve the fixed universe levels. -/
def BoundAtDegree (d : ℕ) : Prop :=
  ∀ {E : Type u} {F : Type v}
    [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
    [FiniteDimensional F2 E] [FiniteDimensional F2 F]
    [Finite E] [Finite F]
    [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
    (f : (E →ₗ[F2] F) → ℝ),
    DegreeAtMost d f →
      (𝔼 M, f M ^ 4) ≤ (2 : ℝ) ^ (100 * d * d) * hybridMomentSum d f

variable {E : Type u} {F : Type v}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Finite E] [Finite F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- The actual weighted map-derivative sum left by the finite reindexing. -/
def dampedMapMoment (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ X : F →ₗ[F2] E,
    (1 / 2 : ℝ) ^ (31 * d * (frequencyRank X + 1) + 4 * d * frequencyRank X) *
      (𝔼 N, mapDerivative X f N ^ 2) ^ 2

def dampedHybridMoment (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ s : HybridIndex (E := E) (F := F) d,
    𝔼 T, dampedMapMoment d (hybridDerivative s.val.1 s.val.2 T f)

/-- Actual A.5 descendants before recombining the first hybrid restriction. -/
def postA5Sum (X : F →ₗ[F2] E) (e : ℕ) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ q : A5Passage.Passage X e, 𝔼 S : Parameter X.range X.ker,
    (𝔼 N, mapDerivative (LinearIdentities.compress X q.2.val.1 q.2.val.2)
      (hybridDerivative q.2.val.1 q.2.val.2 (embed X.range X.ker S) f) N ^ 2)^2

end MaxCutGames.Appendix.A5Induction
end

/-! Frequency-conditioned counts of actual Hybrid pairs and derivative indices. -/

/-! The analytic synthesis and the direct basis-invariant projection are the
same actual function. This identity fixes the interface for both moment and
spectral estimates. -/

/-!
The exact rank component meets the generic derivative inequality's degree
contract by its literal Fourier coefficient filter. This specializes the
checked aggregation to the same actual component used by the KMS spectral
argument; the separate basis-specific proof supplies its hybrid energy.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ClauseVerifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.PCP

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

end MaxCutGames.Foundations.PCP

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineBinaryFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.BinaryFormula

open MaxCutGames.Foundations

def sourceNames (F : Formula) : List Nat :=
  F.clauses.flatMap clauseNames

/-- Explicit list of occurring names, with duplicates removed. The list lengths
depend only on occurrences; no interval of natural-number names is enumerated. -/
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

end MaxCutGames.BinaryFormula

/-!
An explicit ordinary-binary codec for sparse-name three-literal CNF.

A natural name uses its canonical little-endian binary digits. Each payload
digit b is represented by the pair `true,b`; `false` terminates the name.
Zero has the empty payload and therefore the one-bit encoding `[false]`.
A literal is its sign bit followed by its name. A clause contains three literal
encodings. A formula contains `true` followed by each clause, then one final
`false`. There is no unary expansion of a variable name, declared variable
universe, or deduplication of literal or clause occurrences.

The parser rejects noncanonical name payloads, incomplete literals/clauses, and
trailing input. The input length is within a fixed factor of the total ordinary
binary name lengths plus signs and clause framing. Machine correspondence and
runtime are proved separately; these output-size bounds are not time bounds.
-/

/-!
# A destructive equality test on two actual Bool stacks

Each loop transition pops both stacks and compares only the two finite head
registers. A sticky mismatch flag makes the loop continue after disagreement.
The final empty/empty test selects an equal or different continuation and resets
all comparison registers. The ambient state and every other tape are preserved.
-/

namespace MaxCutGames.Foundations.Complexity.MachineCompare

open Turing
open MaxCutGames.Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (K : Type) : K → Type := fun _ => Bool
abbrev State (σ : Type) := σ × Bool × Option Bool × Option Bool

/-- An optional continuation, without reading or writing any tape. -/
def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet K) Λ (State σ) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

/-- Clear both head registers and the mismatch flag after choosing the exit. -/
def finish (exit : Option Λ) : TM2.Stmt (Alphabet K) Λ (State σ) :=
  .load (fun state => (state.1, false, none, none)) (exitAt exit)

/-- The only comparison performed by the program is on two `Option Bool` heads.
In particular, no statement is given a whole-list equality oracle. -/
def loop (left right : K) (loopLabel : Λ) (equalExit differentExit : Option Λ) :
    TM2.Stmt (Alphabet K) Λ (State σ) :=
  .pop left (fun state head => (state.1, state.2.1, head, state.2.2.2))
    (.pop right (fun state head => (state.1, state.2.1, state.2.2.1, head))
      (.branch (fun state => state.2.2.1.isNone && state.2.2.2.isNone)
        (.branch (fun state => state.2.1) (finish differentExit) (finish equalExit))
        (.load (fun state =>
          (state.1, state.2.1 || decide (state.2.2.1 ≠ state.2.2.2), none, none))
          (.goto fun _ => loopLabel))))

/-- Specification-only outcome, also recording an earlier mismatch. -/
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

/-- The exact trace with a possibly pre-existing mismatch. Every input symbol
is consumed even when disagreement has already been detected. -/
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

/-- With a clear initial flag, the final continuation tests equality of the
two complete original words. Both tapes and all comparison registers are empty. -/
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

/-- An actual timed execution witness, with the exact stored transition count. -/
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

end MaxCutGames.Foundations.Complexity.MachineCompare

namespace MaxCutGames.BinaryNameMachine

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition
open MaxCutGames.Reduction.MachineTransfer

def frame : List Bool → List Bool
  | [] => [false]
  | bit :: bits => true :: bit :: frame bits

def steps : List Bool → Nat
  | true :: _ :: rest => steps rest + 1
  | _ => 1

@[simp] theorem frame_length (bits : List Bool) :
    (frame bits).length = 2 * bits.length + 1 := by
  induction bits with
  | nil => simp [frame]
  | cons bit bits ih => simp only [frame, List.length_cons, ih]; omega

@[simp] theorem steps_frame (bits suffix : List Bool) :
    steps (frame bits ++ suffix) = bits.length + 1 := by
  induction bits with
  | nil => simp [frame, steps]
  | cons bit bits ih => simp [frame, steps, ih]

end MaxCutGames.BinaryNameMachine

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_HonestTest
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Honest completeness of the actual three-query test. Compatible coordinate
dictators cancel the two uniform query tables, leaving exactly one noise bit.
The finite-tape form uses the proved product-noise pushforward law. -/

noncomputable section

namespace MaxCutGames.Foundations.Hastad.SourceTape

open scoped BigOperators

/-- Two full Boolean query tables and one finite noise entry per right index. -/
abbrev TestTape (I J : Type*) (D : ℕ) :=
  Cube I × ((J → Fin D) × Cube J)

end MaxCutGames.Foundations.Hastad.SourceTape

end

namespace MaxCutGames.Foundations.Hastad.SourceContexts

open Target PCP

/-- Executable tuple encoding of the eight clause answers. -/
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

/-- Satisfaction and consistency over all `3*u` occurrence slots. -/
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

/-- First matching visible occurrence, with the third slot as an off-support
default. Its inputs contain no hidden incidence choice. -/
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

end MaxCutGames.Foundations.Hastad.SourceContexts

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_Occurrences
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Executable radix numbering of padded global long-code tables and an ordered
equation occurrence list. The code enumerates random tapes, not distinct
equations: coinciding equations and repeated variable occurrences are retained.
-/

namespace MaxCutGames.Foundations.Hastad.SourceOccurrences

open MaxCutGames.Reduction.CloneGap
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

end Encoding

/-- Distinct table vertices and the three side tags never share storage.
Unused ambient query positions are harmless explicit padding. -/
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

/-- Extending by false gives a unique padded address to a restricted query. -/
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

/-- The global index map is an explicit equivalence, including all padding. -/
def assignmentOfKey {V C I J : Type}
    (v : Encoding V) (c : Encoding C) (i : Encoding I) (j : Encoding J)
    (bits : GlobalKey V C I J → Bool) : Fin (globalEncoding v c i j).size → Bool :=
  fun q => bits ((globalEncoding v c i j).code.symm q)

@[simp] theorem assignmentOfKey_code {V C I J : Type}
    (v : Encoding V) (c : Encoding C) (i : Encoding I) (j : Encoding J)
    (bits : GlobalKey V C I J → Bool) (key : GlobalKey V C I J) :
    assignmentOfKey v c i j bits ((globalEncoding v c i j).code key) = bits key := by
  exact congrArg bits ((globalEncoding v c i j).code.symm_apply_apply key)

/-- Mapping the ordered enumeration preserves all sampled occurrences. -/
def occurrenceList {Tape Name : Type} (tape : Encoding Tape)
    (emit : Tape → Equation Name) : List (Equation Name) := tape.enumerate.map emit

@[simp] theorem occurrenceList_length {Tape Name : Type} (tape : Encoding Tape)
    (emit : Tape → Equation Name) : (occurrenceList tape emit).length = tape.size := by
  simp [occurrenceList]

open SourceContexts

def clauseAnswerEncoding : Encoding PCP.ClauseAnswer := ⟨8, clauseAnswerFinEquiv⟩

def iEncoding (u : ℕ) : Encoding (I u) := (Encoding.fin u).function Encoding.bool
def jEncoding (u : ℕ) : Encoding (J u) := (Encoding.fin u).function clauseAnswerEncoding
def variableEncoding (F : Target.Formula) (u : ℕ) : Encoding (VariableContext F u) :=
  (Encoding.fin u).function (Encoding.fin F.«variables»)
def clauseEncoding (F : Target.Formula) (u : ℕ) : Encoding (ClauseContext F u) :=
  (Encoding.fin u).function (Encoding.fin F.clauses.length)

def proofEncoding (F : Target.Formula) (u : ℕ) :
    Encoding (GlobalKey (VariableContext F u) (ClauseContext F u) (I u) (J u)) :=
  globalEncoding (variableEncoding F u) (clauseEncoding F u) (iEncoding u) (jEncoding u)

def nBits (F : Target.Formula) (u : ℕ) : ℕ := (proofEncoding F u).size

@[simp] theorem nBits_eq (F : Target.Formula) (u : ℕ) :
    nBits F u = F.«variables» ^ u * 2 ^ (2 ^ u) +
      (F.clauses.length ^ u * 2 ^ (8 ^ u) + 1) := rfl

abbrev SourceIndex (F : Target.Formula) (u D : ℕ) :=
  (ClauseContext F u × SlotContext u) × SourceTape.TestTape (I u) (J u) D

end MaxCutGames.Foundations.Hastad.SourceOccurrences

namespace MaxCutGames.Foundations.Hastad.SourceLocalSignature

open Target PCP SourceContexts

abbrev Position (u : ℕ) := Fin u × Slot
abbrev NameProfile (u : ℕ) := Position u → Position u → Bool

/-- All local control data have sizes determined solely by the repetition
parameter. Global variable and clause indices are absent. -/
structure Signature (u : ℕ) where
  signs : Position u → Bool
  sameName : NameProfile u
  selected : SlotContext u
  deriving DecidableEq

@[simp] theorem card_position (u : ℕ) : Fintype.card (Position u) = 3 * u := by
  simp [Position, Nat.mul_comm]

end MaxCutGames.Foundations.Hastad.SourceLocalSignature

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineUnaryMultiply
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

namespace MaxCutGames.Foundations.Complexity.MachineUnaryMultiply

open Turing
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

def resultTapes (slots : Fin 5 ↪ K) (base : K → List Bool) (product : ℕ) : K → List Bool :=
  Function.update base (slots 2) (encodeWord product ++ base (slots 2))

@[simp] theorem resultTapes_output (slots : Fin 5 ↪ K) (base : K → List Bool) (p : ℕ) :
    resultTapes slots base p (slots 2) = encodeWord p ++ base (slots 2) := by
  simp [resultTapes]

end MaxCutGames.Foundations.Complexity.MachineUnaryMultiply

namespace MaxCutGames.Foundations.Complexity.MachineUnaryAddAt

open Turing
open Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def finish (destination : K) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .load (fun state => (state.1, none)) (exitAt destination exit)

/-- A fixed finite statement; arithmetic is performed by the physical unary tapes. -/
def loop (source destination : K) (loopLabel : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.push destination (fun _ => true) (.goto fun _ => loopLabel))
      (.branch (fun state => state.2.isSome)
        (.push source (fun _ => false) (finish destination exit))
        (finish destination exit)))

/-- A caller's tape frame with the two unary prefixes and their unread suffixes. -/
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

/-- The zero branch restores the delimiter, clears the register, and exits. -/
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

/-- Exactly `a` positive-bit transitions followed by the delimiter transition. -/
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

/-- The same actual execution from a caller's supplied tape configuration. -/
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

/-- A composable time witness whose stored transition count is exactly `a + 1`. -/
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

end MaxCutGames.Foundations.Complexity.MachineUnaryAddAt

/-!
One actual Horner step on unary field stacks. Multiplication and addition are
executions of the same finite program. All three operands are preserved; only
the output stack receives a new field and both work stacks return empty.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRadixStep

open Turing

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

def resultTapes (slots : Fin 6 ↪ K) (base : K → List Bool) (value : ℕ) : K → List Bool :=
  Function.update base (slots 3) (encodeWord value ++ base (slots 3))

@[simp] theorem resultTapes_output (slots : Fin 6 ↪ K) (base : K → List Bool) (value : ℕ) :
    resultTapes slots base value (slots 3) = encodeWord value ++ base (slots 3) := by
  simp [resultTapes]

end MaxCutGames.Foundations.Complexity.MachineRadixStep

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineHorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Fixed-width Horner traversal by actual radix steps. Two accumulators alternate:
a radix step writes into the empty alternate, then the previous accumulator is
consumed. The base, digit fields, and arbitrary external tapes are preserved.
-/

namespace MaxCutGames.Foundations.Complexity.MachineHorner

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

end MaxCutGames.Foundations.Complexity.MachineHorner

/-! One actual product-output field: gather the fixed number of coordinate
values from the input table, evaluate their common-radix code by Horner, move
the resulting word into the reversed output accumulator, and clear the gather
work. All input fields and the input table are preserved. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ContextPrepare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceLoopInit

open Turing MaxCutGames.Foundations.Complexity
open MachineComposition

inductive HeaderTape | variableCount | clauseCount
  deriving DecidableEq

abbrev Tape (u : Nat) (Extra : Type) := SourceContextLoad.Tape u (HeaderTape ⊕ Extra)

end MaxCutGames.Foundations.Hastad.SourceLoopInit

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_RuntimeModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed natural polynomials are represented by literal Horner coefficients.
The coefficient representation is independent of the machine input. The actual
machine wrapper is built from the shared physical unary Horner subroutine. -/

namespace MaxCutGames.Foundations.Complexity.CookLevin.PolynomialMachine

noncomputable def coefficientPolynomial : List Nat → Polynomial Nat
  | [] => 0
  | a :: rest => coefficientPolynomial rest * Polynomial.X + Polynomial.C a

end MaxCutGames.Foundations.Complexity.CookLevin.PolynomialMachine

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_HeaderAccumulate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceHeaderAccumulate

open Turing MaxCutGames.Foundations.Complexity
open MachineComposition
open MaxCutGames.Reduction.MachineTransfer

structure Layout (K : Type) where
  bits : K
  count : K
  accumulator : K
  bits_count : bits ≠ count
  bits_accumulator : bits ≠ accumulator
  count_accumulator : count ≠ accumulator

variable {K Λ σ : Type} [DecidableEq K]

def statement (layout : Layout K) (labels : Bool → Λ) (exit : Option Λ) :
    Bool → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | false => loopAt layout.bits layout.accumulator id false (labels false) (some (labels true))
  | true => loopAt layout.count layout.accumulator id false (labels true) exit

def resultTapes (layout : Layout K) (base : K → List Bool) (nBits count : Nat) : K → List Bool :=
  Function.update (Function.update (Function.update base layout.bits []) layout.count [])
    layout.accumulator ((encodeWords [nBits, count]).reverse ++ base layout.accumulator)

@[simp] theorem result_bits (layout : Layout K) (base : K → List Bool) (nBits count : Nat) :
    resultTapes layout base nBits count layout.bits = [] := by
  simp [resultTapes, layout.bits_count, layout.bits_accumulator]

@[simp] theorem result_count (layout : Layout K) (base : K → List Bool) (nBits count : Nat) :
    resultTapes layout base nBits count layout.count = [] := by
  simp [resultTapes, layout.count_accumulator]

@[simp] theorem result_accumulator (layout : Layout K) (base : K → List Bool) (nBits count : Nat) :
    resultTapes layout base nBits count layout.accumulator =
      (encodeWords [nBits, count]).reverse ++ base layout.accumulator := by
  simp [resultTapes]

end MaxCutGames.Foundations.Hastad.SourceHeaderAccumulate

/-! Actual fixed-coefficient affine address construction. A finite literal phase
loads the coefficient, the checked width-two Horner machine reads coefficient
and preserved offset with the rank as its radix, then the literal field is
actually consumed. All operands and work stacks are restored. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineBinaryNameCompare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Compare one framed binary name with an already extracted reversed key.
The candidate stream loses precisely that name frame. The key and every other
non-work stack are preserved; the three work stacks are empty again on exit.
The scanner, copy loops, and head-by-head comparison all execute actual TM2
instructions. Whole words occur only in the correctness specification.
-/

/-!
First-occurrence search over signed, framed binary names. The stream has no
clause markers. Every iteration discards one sign, scans and compares the
actual candidate payload, and increments a Boolean unary counter only after a
mismatch. The preserved key is a reversed payload, never a unary name.

The six explicitly distinct tapes are: stream, preserved key, candidate,
copied key, copy scratch, and unary occurrence counter. Successful search
consumes precisely the prefix through the first matching name, preserves the
unread suffix and all ambient tapes, and returns the three work tapes empty.
The time theorem follows from literal instruction equations and checked
comparison executions, with no supplied loop-body trace premise.
-/

namespace MaxCutGames.BinaryNameSearch

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition
open MaxCutGames.Reduction.MachineTransfer

abbrev Token := Bool × List Bool

def tokenBits (token : Token) : List Bool :=
  token.1 :: BinaryNameMachine.frame token.2

def stream : List Token → List Bool
  | [] => []
  | token :: tokens => tokenBits token ++ stream tokens

def payloads (tokens : List Token) : List (List Bool) := tokens.map Prod.snd

def payloadSize (tokens : List Token) : Nat := (payloads tokens |>.map List.length).sum

@[simp] theorem stream_nil : stream [] = [] := rfl

@[simp] theorem stream_cons (token : Token) (tokens : List Token) :
    stream (token :: tokens) = tokenBits token ++ stream tokens := rfl

@[simp] theorem payloads_nil : payloads [] = [] := rfl

@[simp] theorem payloads_cons (token : Token) (tokens : List Token) :
    payloads (token :: tokens) = token.2 :: payloads tokens := rfl

@[simp] theorem payloadSize_nil : payloadSize [] = 0 := rfl

@[simp] theorem payloadSize_cons (token : Token) (tokens : List Token) :
    payloadSize (token :: tokens) = token.2.length + payloadSize tokens := rfl

@[simp] theorem stream_length (tokens : List Token) :
    (stream tokens).length = 2 * payloadSize tokens + 2 * tokens.length := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
      simp only [stream_cons, List.length_append, tokenBits, List.length_cons,
        BinaryNameMachine.frame_length, ih, payloadSize_cons]
      omega

end MaxCutGames.BinaryNameSearch

namespace MaxCutGames.BinaryLiteralMachine

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition
open MaxCutGames.Reduction.MachineTransfer

variable {K Λ A : Type} [DecidableEq K]

def index (tokens : List BinaryNameSearch.Token) (bits : List Bool) : Nat :=
  (BinaryNameSearch.payloads tokens).idxOf bits

end MaxCutGames.BinaryLiteralMachine

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineBinaryParsing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Soundness of the ordinary-binary parser and its concrete name-scanning machine.
Every successful parse consumes exactly a canonical encoding and leaves its
stated suffix. Thus malformed or noncanonical bitstrings cannot name an extra
formula. The finite scanner's final-digit test is proved equivalent to the
codec's arithmetic canonicality test.
-/

/-!
Occurrence-index renaming for the ordinary-binary input machine. Every name is
replaced by the position of its first occurrence in the complete literal-name
list. The output declares three «variables» per clause; some IDs can be unused.
This avoids constructing a duplicate-free dictionary while keeping all IDs
bounded by the literal occurrence count. Equality tests may compare the actual
canonical binary payloads, without converting a name to unary.

These are the correspondence facts for the scan/compare machine.
They do not by themselves assert that the renaming runs in polynomial time.
-/

namespace MaxCutGames.BinaryOccurrenceRename

open BinaryFormula MaxCutGames.Foundations

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

end MaxCutGames.BinaryOccurrenceRename

/-!
The ordinary binary 3SAT language includes exactly the successfully decoded
satisfiable formulas. A total semantic extension of occurrence-index renaming
maps malformed bitstrings to a fixed contradictory formula. Its runtime is a
separate machine-composition obligation; the size theorem below is only size.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineBinaryRenameWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The word-level correspondence used by the ordinary-binary renaming machine.
Literal occurrences stay in clause order, and equality is tested on canonical
binary payloads. The output body consists of the first occurrence index and
the sign of every literal, in the inherited dense formula codec.
-/

/-!
An actual finite Boolean-stack routine prepending two unary header words to an
already restored serialized body. It consumes counters containing `n` and `m`
true bits, respectively, in exactly `n + m + 4` transitions. All ambient stacks
and the finite ambient state are preserved. The input counters need no separate
counting pass: a caller can accumulate them while constructing the body.

The generic placement theorem uses only four displayed instruction equations.
The concrete machine below has three Boolean stacks and four control labels;
its final transfer halts directly. This is a staged configuration computation,
not a single-input `initList` assertion that silently assumes two extra inputs.
-/

namespace MaxCutGames.BinaryHeaderMachine

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition
open MaxCutGames.Reduction.MachineTransfer

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool

section Placement

variable {K Λ A : Type} [DecidableEq K]

def tapes (variableTape clauses destination : K) (base : K → List Bool)
    (variableCounter clauseCounter output : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base variableTape variableCounter)
    clauses clauseCounter) destination output

end Placement

end MaxCutGames.BinaryHeaderMachine

/-!
The finite Boolean-stack driver for first-occurrence renaming. Its permanent
input is copied to a cursor, each literal is translated by the checked search
loop, and the physical output is restored, prefixed with its count headers,
and cleaned up. Every tape uses Bool and every control component is finite.
-/

end OAI
end


