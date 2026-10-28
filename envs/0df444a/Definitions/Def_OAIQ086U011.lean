-- Prove2me | Definitions.Def_OAIQ086U011
-- name    : OAIQ086U011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T16:44:20.371043+00:00
-- url     : https://prove2.me/theorems/27ba1a03-9616-4a58-b0cf-52e25f6a0945
-- title:
--   Definitions bundle OAIQ086U011 of the split of OpenAI, The Unique Games Theorem
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniqueGamesTheorem.theorem11`, carved from OpenAI's openai/math development (OpenAI, *The Unique Games Theorem*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 200 declarations of OpenAI's Lean: 76 definitions, 8 inductive types or structures, 2 instances and 114 theorems. The definitions and types are `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextPrepare.stateSwap`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorModel.coefficientKeys`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderCounts.Clean`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderCounts.Label`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderCounts.WorkClean`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderCounts.afterEval`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderCounts.evalStart`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderCounts.inTime`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderCounts.statement`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderCounts.steps`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderCounts.timePolynomial`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHonest.honestValidJ`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLocalEquation.localInputEncoding`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLoopInit.headerInTime`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLoopInit.initializeInTime`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLoopInit.readOutput`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLoopOrder.rankedQuery`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceProfileBridge.reindexProfile`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceQueryLoop.Label`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceQueryLoop.prefixSteps`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceQueryOrder.occurrenceBits`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceQueryOrder.slotBits`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceQueryOrder.tupleBits`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceRankPhase.clauseRankInTime`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceRankPhase.variableRankInTime`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceRuntimeModel.rankControls`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceSignaturePrepare.polarityField`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceSignaturePrepare.signStateEquiv`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ArithmeticLabel`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.Label`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.arithmeticEntry`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.timePolynomial`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceTestAppend.Label`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceTestAppend.bodyLabel`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceTestAppend.steps`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceTestEmit.Label`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceTestEmit.bodyLabel`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceTupleBody.QueryCount`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceTupleBound.preparePolynomial`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceTupleBound.setupPolynomial` and 44 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `UniqueGames_Inverse_RowErasureMatrixLemmas`, `UniqueGames_PCP_AlphabetTableBoundsLemmas`, `UniqueGames_PCP_Body`, `UniqueGames_PCP_DriverLemmas`, `UniqueGames_PCP_EmitRows`, `UniqueGames_PCP_FinalBooleanVerifier`, `UniqueGames_PCP_InitialGraphLemmas`, `UniqueGames_PCP_Initialization`, `UniqueGames_PCP_LoopInitializationLemmas`, `UniqueGames_PCP_PreprocessingTableSpectral`, `UniqueGames_PCP_PreprocessingTablesLemmas`, `UniqueGames_PCP_RawInitialTablesLemmas`, `UniqueGames_PCP_SourceContextLoad`, `UniqueGames_PCP_SourceDescriptorEmissionLemmas`, `UniqueGames_PCP_SourceFieldArrayLemmas`, `UniqueGames_PCP_SourceHeaderCounts`, `UniqueGames_PCP_SourceHonestLemmas`, `UniqueGames_PCP_SourceLoopInitLemmas`, `UniqueGames_PCP_SourceOccurrences`, `UniqueGames_PCP_SourceQueryLoopLemmas`, `UniqueGames_PCP_SourceQueryOrderLemmas`, `UniqueGames_PCP_SourceSignaturePrepareLemmas`, `UniqueGames_PCP_SourceTupleBody`, `UniqueGames_PCP_SourceTupleBound`, `UniqueGames_PCP_TableIteration`.
--
--   **Imports.** It imports the published bundle `Def_UniqueGamesTheorem`; the bundles `OAIQ086U006`, `OAIQ086U007`, `OAIQ086U008` and `OAIQ086U009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ086U012` and `OAIQ086U014`.
-- source:
--   OpenAI, The Unique Games Theorem, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Unique-Games-Theorem-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_UniqueGamesTheorem
import Definitions.Def_OAIQ086U006
import Definitions.Def_OAIQ086U007
import Definitions.Def_OAIQ086U008
import Definitions.Def_OAIQ086U009

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

def left {ell m : ℕ} (e : Samples ell m) : Mat ell m := e.1

def right {ell m : ℕ} (e : Samples ell m) : Mat ell m :=
  e.1 + rankOne e.2.1 e.2.2

/-- Translation of the sampled matrix is a permutation while the two sampled
factors remain fixed; this also covers either factor being zero. -/
def stepEquiv (ell m : ℕ) : Samples ell m ≃ Samples ell m where
  toFun e := (right e, e.2)
  invFun e := (e.1 - rankOne e.2.1 e.2.2, e.2)
  left_inv e := by
    apply Prod.ext
    · exact add_sub_cancel_right e.1 (rankOne e.2.1 e.2.2)
    · rfl
  right_inv e := by
    apply Prod.ext
    · exact sub_add_cancel e.1 (rankOne e.2.1 e.2.2)
    · rfl

end
end UniqueGamesTheorem.Inverse.RowErasureMatrix

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

theorem incidenceAccept_true (F : Formula) (event : RandomEvent F) (a b : Label)
    (h : incidenceAccept F event a b = true) :
    localSatisfies (clauseAt F event.1) (toClauseAnswer a) = true ∧
      answerAt (toClauseAnswer a) event.2 = b.1 := by
  simp only [incidenceAccept, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem incidence_honest (F : Formula) (A : Fin F.variables → Bool)
    (sat : ∀ c ∈ F.clauses, c.eval A = true) (event : RandomEvent F) :
    incidenceAccept F event (honestLabeling F A (clauseVertex F event.1))
      (honestLabeling F A (variableVertex F (nameAt (clauseAt F event.1) event.2))) = true := by
  have hc : (clauseAt F event.1).eval A = true := sat _ (List.getElem_mem _)
  simp [incidenceAccept, honestLabeling, clauseVertex, variableVertex, variableLabel,
    variableValid, honest_satisfies, honest_answerAt, hc]

theorem raw_completeness (F : Formula) (sat : F.Satisfiable) : (raw F).Satisfiable := by
  rcases sat with ⟨A, hA⟩
  refine ⟨honestLabeling F A, fun d => ?_⟩
  cases d with
  | inl pair =>
    rcases pair with ⟨event, orientation⟩
    cases orientation <;> exact incidence_honest F A hA event
  | inr u => rfl

theorem raw_reflects (F : Formula) (sat : (raw F).Satisfiable) : F.Satisfiable := by
  rcases sat with ⟨labeling, hlabeling⟩
  let A : Fin F.variables → Bool := fun v => (labeling (variableVertex F v)).1
  have slot_correct (i : Fin F.clauses.length) (s : Slot) :
      localSatisfies (clauseAt F i) (toClauseAnswer (labeling (clauseVertex F i))) = true ∧
        answerAt (toClauseAnswer (labeling (clauseVertex F i))) s =
          A (nameAt (clauseAt F i) s) := by
    exact incidenceAccept_true F (i, s) _ _ (hlabeling (.inl ((i, s), false)))
  have clause_correct (i : Fin F.clauses.length) : (clauseAt F i).eval A = true := by
    have equal : toClauseAnswer (labeling (clauseVertex F i)) = honestAnswer (clauseAt F i) A :=
      clauseAnswer_eq_of_slots _ _ (fun s => by
        simpa only [honest_answerAt] using (slot_correct i s).2)
    have satisfied := (slot_correct i .first).1
    rw [equal, honest_satisfies] at satisfied
    exact satisfied
  refine ⟨A, fun c hc => ?_⟩
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hc
  simpa only [clauseAt, heq] using clause_correct ⟨i, hi⟩

theorem raw_satisfiable_iff (F : Formula) : (raw F).Satisfiable ↔ F.Satisfiable :=
  ⟨raw_reflects F, raw_completeness F⟩

end UniqueGamesTheorem.Foundations.PCP.InitialGraph

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_AlphabetTableBoundsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.VerifierToCNF

open Target

def clauseFailures {n : Nat} (clauses : List (Clause n)) (A : Fin n → Bool) : Nat :=
  (clauses.map (fun c => c.eval A)).count false

theorem tautology_satisfied {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (e : Fin V.events) (B : Fin (outputVariables V) → Bool) :
    (tautology V hq e).eval B = true := by
  simp [tautology, Clause.eval, Literal.eval]

theorem block_honest {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.variables → Bool) (e : Fin V.events) (p : PatternIndex q)
    (honest : eventValue V A e = true) :
    (block V hq e p).all (fun c => c.eval (extendAssignment V hq A)) = true := by
  cases accepted : V.accepts e (patternAt q p) with
  | true => simp [block, accepted, tautology_satisfied]
  | false =>
    have good := (fillBits_correct (mismatchBits V A e p) (by simpa using hq)).mpr
      (mismatchBits_true V A e p honest accepted)
    have values := splitLong_values (forbiddenClause V e p) (auxiliaryNames V e p)
      (extendAssignment V hq A)
    rw [forbiddenClause_values, restrict_extend, extended_auxiliary_values] at values
    have all := congrArg (fun bs : List Bool => bs.all id) values
    simp only [List.all_map, Function.comp_def, id_eq] at all
    simpa only [block, accepted, Bool.false_eq_true, ↓reduceIte] using all.trans good

theorem convert_nonempty {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (eventsPositive : 0 < V.events) : (convert V hq).clauses ≠ [] := by
  have p : 0 < (convert V hq).clauses.length := by
    rw [convert_clause_count]
    exact Nat.mul_pos eventsPositive (Nat.mul_pos (Nat.pow_pos (by decide)) (by omega))
  intro empty
  simp only [empty, List.length_nil] at p
  omega

theorem convert_completeness {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.variables → Bool) (honest : ∀ e, eventValue V A e = true) :
    (convert V hq).Satisfiable := by
  refine ⟨extendAssignment V hq A, fun c hc => ?_⟩
  obtain ⟨e, _, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨p, _, hc⟩ := List.mem_flatMap.mp hc
  exact List.all_eq_true.mp (block_honest V hq A e p (honest e)) c hc

theorem clauseFailures_append {n : Nat} (xs ys : List (Clause n)) (A : Fin n → Bool) :
    clauseFailures (xs ++ ys) A = clauseFailures xs A + clauseFailures ys A := by
  simp [clauseFailures, List.map_append, List.count_append]

theorem clauseFailures_le_flatMap {α : Type*} {n : Nat} (xs : List α)
    (f : α → List (Clause n)) (A : Fin n → Bool) (x : α) (hx : x ∈ xs) :
    clauseFailures (f x) A ≤ clauseFailures (xs.flatMap f) A := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp only [List.flatMap_cons, clauseFailures_append]
      omega
    · have h := ih hx
      simp only [List.flatMap_cons, clauseFailures_append]
      omega

/-- The actual answer pattern forces a failed chain, even when queried names
repeat and regardless of the labels on all allocated auxiliary variables. -/
theorem block_failed {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (B : Fin (outputVariables V) → Bool) (e : Fin V.events) (p : PatternIndex q)
    (rejected : V.accepts e (patternAt q p) = false)
    (actual : ∀ i, restrictAssignment V B (V.query e i) = patternAt q p i) :
    1 ≤ clauseFailures (block V hq e p) B := by
  have bitsFalse := mismatchBits_false V (restrictAssignment V B) e p actual
  have size : ((forbiddenClause V e p).map (fun l => l.eval B)).length =
      ((auxiliaryNames V e p).map B).length + 3 := by
    simp only [List.length_map, forbiddenClause, auxiliaryNames, List.length_ofFn]
    omega
  have failed := chainView_failed ((forbiddenClause V e p).map (fun l => l.eval B))
    ((auxiliaryNames V e p).map B) size (by
      rw [forbiddenClause_values]
      exact bitsFalse)
  simpa only [block, rejected, Bool.false_eq_true, ↓reduceIte, clauseFailures,
    splitLong_values] using failed

theorem eventBlock_failed {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (B : Fin (outputVariables V) → Bool) (e : Fin V.events)
    (rejected : eventValue V (restrictAssignment V B) e = false) :
    1 ≤ clauseFailures (eventBlock V hq e) B := by
  obtain ⟨p, hp⟩ := patternAt_surjective q (fun i => restrictAssignment V B (V.query e i))
  have rejectedPattern : V.accepts e (patternAt q p) = false := by
    rw [hp]
    exact rejected
  have failed := block_failed V hq B e p rejectedPattern (fun i => (congrFun hp i).symm)
  exact failed.trans (clauseFailures_le_flatMap (List.finRange (patterns q).length)
    (block V hq e) B p (by simp))

theorem clauseFailures_flatMap {α : Type*} {n : Nat} (xs : List α)
    (f : α → List (Clause n)) (A : Fin n → Bool) :
    clauseFailures (xs.flatMap f) A = (xs.map (fun x => clauseFailures (f x) A)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, clauseFailures_append, List.map_cons, List.sum_cons, ih]

theorem convert_count_bridge {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (B : Fin (outputVariables V) → Bool) :
    rejectedEventCount V (restrictAssignment V B) ≤ NameCompaction.failedCount (convert V hq) B := by
  change ((List.finRange V.events).map (eventValue V (restrictAssignment V B))).count false ≤
    clauseFailures ((List.finRange V.events).flatMap (eventBlock V hq)) B
  rw [count_false_map_sum, clauseFailures_flatMap]
  apply nat_sum_map_le
  intro e _
  cases rejected : eventValue V (restrictAssignment V B) e with
  | false => simpa only [rejected, Bool.false_eq_true, ↓reduceIte] using
      eventBlock_failed V hq B e rejected
  | true => simp only [↓reduceIte, Nat.zero_le]

theorem convert_gap {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (a b : Nat)
    (gap : ∀ A, a * V.events ≤ b * rejectedEventCount V A)
    (B : Fin (outputVariables V) → Bool) :
    a * (convert V hq).clauses.length ≤
      (b * (2 ^ q * (q - 2))) * NameCompaction.failedCount (convert V hq) B := by
  have eventGap := gap (restrictAssignment V B)
  have countBound := Nat.mul_le_mul_left b (convert_count_bridge V hq B)
  rw [convert_clause_count]
  calc
    a * (V.events * (2 ^ q * (q - 2))) = (a * V.events) * (2 ^ q * (q - 2)) := by
      rw [Nat.mul_assoc]
    _ ≤ (b * NameCompaction.failedCount (convert V hq) B) * (2 ^ q * (q - 2)) :=
      Nat.mul_le_mul_right _ (eventGap.trans countBound)
    _ = (b * (2 ^ q * (q - 2))) * NameCompaction.failedCount (convert V hq) B := by ac_rfl

end UniqueGamesTheorem.Foundations.PCP.VerifierToCNF

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

def headerInTime {K Λ σ : Type} [DecidableEq K] (q n m : Nat)
    (sources : Fin 2 → K) (scratch output : K)
    (sourceScratch : ∀ i, sources i ≠ scratch)
    (sourceOutput : ∀ i, sources i ≠ output) (scratchOutput : scratch ≠ output)
    (labels : Label (headerCommands q σ).length (Addresses.fieldBound q) → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement (listCommands (headerCommands q σ))
      sources scratch output labels exit label)
    (base : K → List Bool) (operands : ∀ i, base (sources i) = encodeWord (![n, m] i))
    (scratchEmpty : base scratch = []) (ambient : σ) (N : Nat) (hn : n ≤ N) (hm : m ≤ N) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (labelAt (headerCommands q σ).length (Addresses.fieldBound q) 0 .entry)),
        ((ambient, ()), none), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes output base
        (encodeWords [Enumeration.vertexCount n m q, Enumeration.dartCount m q])⟩)
      (7 * (3 * (N + 1) + 3) + 1) := by
  have bounded : ∀ i : Fin 2, ![n, m] i ≤ N := by
    intro i
    fin_cases i <;> simp [hn, hm]
  have run := planInTime (listCommands (headerCommands q σ)) sources scratch output
    sourceScratch sourceOutput scratchOutput labels exit p atLabels ![n, m] base operands
    scratchEmpty ambient N bounded
  rw [bits_listCommands, headerCommands_bits] at run
  simpa only [headerCommands_length] using run

def blockInTimeAmbient {K Λ σ : Type} [DecidableEq K] {q : Nat}
    (input : GenericGraphTables.Table q) (edge : Fin input.darts)
    (context : σ → Context q) (ambient : σ) (hcontext : context ambient = rowContext input edge)
    (sources : Fin 5 → K) (scratch output : K)
    (sourceScratch : ∀ i, sources i ≠ scratch)
    (sourceOutput : ∀ i, sources i ≠ output) (scratchOutput : scratch ≠ output)
    (labels : Label (blockCommandsIn q context).length (Addresses.fieldBound q) → Λ)
    (exit : Option Λ) (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement (listCommands (blockCommandsIn q context))
      sources scratch output labels exit label)
    (base : K → List Bool)
    (operands : ∀ i, base (sources i) = encodeWord (rowValues input edge i))
    (scratchEmpty : base scratch = []) (N : Nat)
    (bounded : ∀ i, rowValues input edge i ≤ N) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (labelAt (blockCommandsIn q context).length (Addresses.fieldBound q) 0 .entry)),
        ((ambient, ()), none), base⟩
      (some ⟨exit, ((ambient, ()), none),
        resultTapes output base (encodeWords (blockWords input edge))⟩)
      (Enumeration.localCount q * (6 * (2 * 4104)) * (3 * (N + 1) + 3) + 1) := by
  have run := planInTime (listCommands (blockCommandsIn q context)) sources scratch output
    sourceScratch sourceOutput scratchOutput labels exit p atLabels (rowValues input edge)
    base operands scratchEmpty ambient N bounded
  rw [bits_listCommands, blockCommandsIn_bits input edge context ambient hcontext] at run
  have lengthBound : (blockCommandsIn q context).length ≤
      Enumeration.localCount q * (6 * (2 * 4104)) := by
    simpa only [blockCommandsIn, List.length_map] using blockCommands_length_le q
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  exact run.steps_le_m.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ lengthBound) 1)

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.EmitRows

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_DriverLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
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

def program (q : Nat) : Label q → TM2.Stmt Alphabet (Label q) (State q)
  | .setup label => Setup.statement setupPorts Label.setup (some (headerEntry q)) label
  | .header label => emitterStatement
      (Emitter.statement (Emitter.listCommands (headerPlan q)) headerSources .scratch .reversed
        Label.header (some .guard) label)
  | .guard => MachineUnaryCounter.guard .counter .tailStart .reverseOutput
  | .tailStart => SourceMachine.fieldStart .tail .tailLoop
  | .tailLoop => SourceMachine.fieldLoop .cursor .tail .tailLoop (some .reverseStart)
  | .reverseStart => SourceMachine.fieldStart .reverseIndex .reverseLoop
  | .reverseLoop => SourceMachine.fieldLoop .cursor .reverseIndex .reverseLoop (some .readPredicate)
  | .readPredicate => ReadRelation.parser .cursor .headCopyFirst
  | .headCopyFirst => Reduction.MachineTransfer.loopAt .original .scratch id false
      .headCopyFirst (some .headCopySecond)
  | .headCopySecond => MachineCopy.forkLoop .scratch .original .scan false
      .headCopySecond (some .indexCopyFirst)
  | .indexCopyFirst => Reduction.MachineTransfer.loopAt .reverseIndex .scratch id false
      .indexCopyFirst (some .indexCopySecond)
  | .indexCopySecond => MachineCopy.forkLoop .scratch .reverseIndex .indexScan false
      .indexCopySecond (some .headVertices)
  | .headVertices => MachineLookup.discard .scan .headVertices .headDarts
  | .headDarts => MachineLookup.discard .scan .headDarts (.headLookup .guard)
  | .headLookup label => Lookup.statement q .indexScan .scan .head Label.headLookup
      (some (.compare .leftFirst)) label
  | .compare label => CompareLoop.statement Label.compare (rowEntry q) label
  | .emit label => emitterStatement
      (Emitter.statement (Emitter.listCommands (rowPlan q)) rowSources .scratch .reversed
        Label.emit (some (.clearField 0)) label)
  | .clearField slot => MachineDrain.drain (fieldPorts slot) (.clearField slot)
      (some (clearNext slot))
  | .increment => nextRow .guard
  | .reverseOutput => Reduction.MachineTransfer.loopAt .reversed .output id false
      .reverseOutput (some (.cleanup 0))
  | .cleanup slot => Cleanup.instruction cleanupPorts Label.cleanup (initial q).1 none slot

/-- Every state component is finite; the q-dependent relation register is
enumerated by the explicit vector/function equivalence of the parser. -/
def machine (q : Nat) : FinTM2 := by
  letI := ReadRelation.stateFintype Flags q
  exact {
    K := Tape
    k₀ := .original
    k₁ := .output
    Γ := Alphabet
    Λ := Label q
    main := .setup .copyFirst
    σ := State q
    initialState := initial q
    m := program q }

@[simp] theorem program_setup (q : Nat) (label : Setup.Label) :
    program q (.setup label) =
      Setup.statement setupPorts Label.setup (some (headerEntry q)) label := rfl

@[simp] theorem program_guard (q : Nat) : program q .guard =
    MachineUnaryCounter.guard .counter .tailStart .reverseOutput := rfl

@[simp] theorem program_headLookup (q : Nat) (label : Lookup.Label) :
    program q (.headLookup label) = Lookup.statement q .indexScan .scan .head
      Label.headLookup (some (.compare .leftFirst)) label := rfl

@[simp] theorem program_compare (q : Nat) (label : CompareLoop.Label) :
    program q (.compare label) = CompareLoop.statement Label.compare (rowEntry q) label := rfl

@[simp] theorem program_increment (q : Nat) : program q .increment = nextRow .guard := rfl

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Driver

/-! The actual final driver phases: reverse the accumulated output, drain all
fifteen nonoutput stacks, reset the finite state, and reach `haltList`.
Polynomial resource bounds below require an actual preceding execution. -/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Finish

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open RuntimeModel
open scoped BigOperators

def afterReversal (base : Tape → List Bool) (word : List Bool) : Tape → List Bool :=
  Reduction.MachineTransfer.tapesAt .reversed .output base [] word

@[simp] theorem afterReversal_output (base : Tape → List Bool) (word : List Bool) :
    afterReversal base word .output = word := by
  simp [afterReversal, Reduction.MachineTransfer.tapesAt]

@[simp] theorem afterReversal_reversed (base : Tape → List Bool) (word : List Bool) :
    afterReversal base word .reversed = [] := by
  simp [afterReversal, Reduction.MachineTransfer.tapesAt]

def finishBudget (base : Tape → List Bool) (word : List Bool) : Nat :=
  word.length + 1 + (∑ i : Fin 15, (afterReversal base word (cleanupPorts i)).length) + 16

/-- The actual driver's reversal loop enters its first cleanup label. -/
def reverseInTime (q : Nat) (base : Tape → List Bool) (word : List Bool)
    (state : State q) (hreversed : base .reversed = word.reverse)
    (houtput : base .output = []) :
    StateTransition.EvalsToInTime (Driver.machine q).step
      ⟨some .reverseOutput, state, base⟩
      (some ⟨some (.cleanup 0), (state.1, none), afterReversal base word⟩)
      (word.length + 1) := by
  have run := Reduction.MachineTransfer.transferAtInTime
    (σ := Ambient q) Tape.reversed Tape.output (by decide) id false
    Driver.Label.reverseOutput (some (.cleanup 0)) (Driver.program q) rfl
    base state.1 state.2
  simpa only [hreversed, houtput, List.length_reverse, List.reverse_reverse,
    List.map_id, List.append_nil, afterReversal, Driver.machine, FinTM2.step] using! run

theorem cleared_eq_haltList (q : Nat) (base : Tape → List Bool) :
    (⟨none, initial q, Cleanup.clearTapes cleanupPorts base⟩ : (Driver.machine q).Cfg) =
      haltList (Driver.machine q) (base .output) := by
  have tapes := Cleanup.clearTapes_outputOnly cleanupPorts Tape.output base
    cleanupPorts_ne_output cleanupPorts_cover
  congr 1

/-- All remaining driver stacks are actually popped, and the exact initial
finite state is restored before the halting configuration is reached. -/
def cleanupInTime (q : Nat) (base : Tape → List Bool) (state : State q) :
    StateTransition.EvalsToInTime (Driver.machine q).step
      ⟨some (.cleanup 0), state, base⟩
      (some (haltList (Driver.machine q) (base .output)))
      ((∑ i : Fin 15, (base (cleanupPorts i)).length) + 16) := by
  have run := Cleanup.cleanupInTime cleanupPorts Driver.Label.cleanup (initial q).1 none
    (Driver.program q)
    (fun i => by simp only [Driver.program, Cleanup.instruction_drain])
    (by simp only [Driver.program, Cleanup.instruction_finish]) base state.1 state.2
  change StateTransition.EvalsToInTime (Driver.machine q).step
    ⟨some (.cleanup 0), state, base⟩
    (some ⟨none, initial q, Cleanup.clearTapes cleanupPorts base⟩)
    ((∑ i : Fin 15, (base (cleanupPorts i)).length) + 15 + 1) at run
  rw [cleared_eq_haltList] at run
  simpa only [Nat.add_assoc] using run

def finishInTime (q : Nat) (base : Tape → List Bool) (word : List Bool)
    (state : State q) (hreversed : base .reversed = word.reverse)
    (houtput : base .output = []) :
    StateTransition.EvalsToInTime (Driver.machine q).step
      ⟨some .reverseOutput, state, base⟩
      (some (haltList (Driver.machine q) word)) (finishBudget base word) := by
  have first := reverseInTime q base word state hreversed houtput
  have last := cleanupInTime q (afterReversal base word) (state.1, none)
  rw [afterReversal_output] at last
  have run := StateTransition.EvalsToInTime.trans (Driver.machine q).step _ _
    ⟨some .reverseOutput, state, base⟩
    ⟨some (.cleanup 0), (state.1, none), afterReversal base word⟩
    (some (haltList (Driver.machine q) word)) first last
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have budgetEq : ((∑ i : Fin 15, (afterReversal base word (cleanupPorts i)).length) + 16) +
      (word.length + 1) =
      finishBudget base word := by
    dsimp only [finishBudget]
    omega
  exact run.steps_le_m.trans (Nat.le_of_eq budgetEq)

theorem afterReversal_selected_length_le (base : Tape → List Bool) (word : List Bool)
    (i : Fin 15) :
    (afterReversal base word (cleanupPorts i)).length ≤ (base (cleanupPorts i)).length := by
  have ho := cleanupPorts_ne_output i
  by_cases hr : cleanupPorts i = .reversed <;>
    simp [afterReversal, Reduction.MachineTransfer.tapesAt, ho, hr]

/-- Every stack bound here is derived from the actual preceding driver trace. -/
theorem stackLength_after_prefix (q : Nat) (input : List Bool)
    (base : Tape → List Bool) (state : State q) (budget : Nat)
    (prefixRun : StateTransition.EvalsToInTime (Driver.machine q).step
      (initList (Driver.machine q) input) (some ⟨some .reverseOutput, state, base⟩) budget)
    (k : Tape) :
    (base k).length ≤ input.length + budget * Runtime.programPushBound (Driver.machine q) := by
  have bound := Runtime.executionSizeBound (Driver.machine q).step
    (fun cfg => (cfg.stk k).length) (Runtime.programPushBound (Driver.machine q))
    (Runtime.stepStackLength (Driver.machine q) k) prefixRun
  exact bound.trans (Nat.add_le_add_right
    (Runtime.initialStackLength (Driver.machine q) input k) _)

theorem finishBudget_le_of_prefix (q : Nat) (input : List Bool)
    (base : Tape → List Bool) (word : List Bool) (state : State q) (budget : Nat)
    (prefixRun : StateTransition.EvalsToInTime (Driver.machine q).step
      (initList (Driver.machine q) input) (some ⟨some .reverseOutput, state, base⟩) budget)
    (hreversed : base .reversed = word.reverse) :
    finishBudget base word ≤
      16 * (input.length + budget * Runtime.programPushBound (Driver.machine q)) + 17 := by
  let B := input.length + budget * Runtime.programPushBound (Driver.machine q)
  have wordBound : word.length ≤ B := by
    simpa only [hreversed, List.length_reverse] using
      stackLength_after_prefix q input base state budget prefixRun .reversed
  have sumBound : (∑ i : Fin 15, (afterReversal base word (cleanupPorts i)).length) ≤ 15 * B := by
    calc
      _ ≤ ∑ _i : Fin 15, B := by
        apply Finset.sum_le_sum
        intro i _
        exact (afterReversal_selected_length_le base word i).trans
          (stackLength_after_prefix q input base state budget prefixRun (cleanupPorts i))
      _ = 15 * B := by simp
  dsimp only [finishBudget]
  omega

/-- A polynomial time allowance for the whole prefixRun followed by actual
reversal and cleanup. The fixed push bound belongs to the concrete driver. -/
noncomputable def completedPolynomial (q : Nat) (prefixTime : Polynomial Nat) : Polynomial Nat :=
  prefixTime + Polynomial.C 16 *
    (Polynomial.X + Polynomial.C (Runtime.programPushBound (Driver.machine q)) * prefixTime) +
    Polynomial.C 17

def finishAfterPrefix (q : Nat) (input : List Bool) (base : Tape → List Bool)
    (word : List Bool) (state : State q) (budget : Nat)
    (prefixRun : StateTransition.EvalsToInTime (Driver.machine q).step
      (initList (Driver.machine q) input) (some ⟨some .reverseOutput, state, base⟩) budget)
    (hreversed : base .reversed = word.reverse) (houtput : base .output = []) :
    TM2OutputsInTime (Driver.machine q) input (some word)
      (budget + 16 * (input.length + budget * Runtime.programPushBound (Driver.machine q)) + 17) := by
  have last := finishInTime q base word state hreversed houtput
  let run := StateTransition.EvalsToInTime.trans (Driver.machine q).step _ _
    (initList (Driver.machine q) input) ⟨some .reverseOutput, state, base⟩
    (some (haltList (Driver.machine q) word)) prefixRun last
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have finishBound := finishBudget_le_of_prefix q input base word state budget prefixRun hreversed
  have allBound := run.steps_le_m
  omega

def finishAfterPolynomialPrefix (q : Nat) (input : List Bool) (base : Tape → List Bool)
    (word : List Bool) (state : State q) (prefixTime : Polynomial Nat)
    (prefixRun : StateTransition.EvalsToInTime (Driver.machine q).step
      (initList (Driver.machine q) input) (some ⟨some .reverseOutput, state, base⟩)
      (prefixTime.eval input.length))
    (hreversed : base .reversed = word.reverse) (houtput : base .output = []) :
    TM2OutputsInTime (Driver.machine q) input (some word)
      ((completedPolynomial q prefixTime).eval input.length) := by
  have run := finishAfterPrefix q input base word state (prefixTime.eval input.length)
    prefixRun hreversed houtput
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  simpa only [completedPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Nat.mul_comm] using run.steps_le_m

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Finish

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_Body
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

/-- An execution witness, with the exact invariant needed by the next guard. -/
structure RowStepResult (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) (oldRelation : GenericGraphTables.RelationTable q)
    (oldFlag : Bool) where
  tapes : Tape → List Bool
  ready : LoopState.Ready input (e.val + 1) tapes
  run : StateTransition.EvalsToInTime (TM2.step (Driver.program q))
    ⟨some .guard, normal oldRelation oldFlag, base⟩
    (some ⟨some .guard, CompareLoop.rowState input e, tapes⟩)
    (bodyTime q (LoopState.inputBits input).length)

def guardTapes (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) : Tape → List Bool :=
  Function.update base .counter (encodeWord (input.darts - (e.val + 1)))

def parsedTapes (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) : Tape → List Bool :=
  Lookup.readRowTapes .cursor .tail .reverseIndex (guardTapes input e base)
    input.rows[e] (LoopState.cursorBits input (e.val + 1))

def workingTapes (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) : Tape → List Bool :=
  Lookup.headLookupTapes headPorts (parsedTapes input e base) input e

def emittedTapes (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) : Tape → List Bool :=
  Emitter.resultTapes .reversed (workingTapes input e base)
    (encodeWords (EmitRows.blockWords input e))

def clearFieldsTapes (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (Function.update (Function.update base .tail []) .reverseIndex []) .head []

/-- Exact final tapes, including the lookup's retained scan suffixes. -/
def resultTapes (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (clearFieldsTapes (emittedTapes input e base)) .edge
    (encodeWord (e.val + 1))

theorem workingTapes_other (input : GenericGraphTables.Table q)
    (e : Fin input.darts) (base : Tape → List Bool) (other : Tape)
    (hcounter : other ≠ .counter) (hcursor : other ≠ .cursor)
    (htail : other ≠ .tail) (hreverse : other ≠ .reverseIndex)
    (hscan : other ≠ .scan) (hindex : other ≠ .indexScan) (hhead : other ≠ .head) :
    workingTapes input e base other = base other := by
  simp [workingTapes, Lookup.headLookupTapes, MachineLookup.tapes, headPorts,
    parsedTapes, Lookup.readRowTapes, guardTapes, hcounter, hcursor, htail,
    hreverse, hscan, hindex, hhead]

theorem workingTapes_tail (input : GenericGraphTables.Table q)
    (e : Fin input.darts) (base : Tape → List Bool) :
    workingTapes input e base .tail = encodeWord input.rows[e].tail.val := by
  simp [workingTapes, Lookup.headLookupTapes, MachineLookup.tapes, headPorts,
    parsedTapes, Lookup.readRowTapes]

theorem workingTapes_reverse (input : GenericGraphTables.Table q)
    (e : Fin input.darts) (base : Tape → List Bool) :
    workingTapes input e base .reverseIndex = encodeWord input.rows[e].reverseIndex.val := by
  simp [workingTapes, Lookup.headLookupTapes, MachineLookup.tapes, headPorts,
    parsedTapes, Lookup.readRowTapes]

theorem workingTapes_head (input : GenericGraphTables.Table q)
    (e : Fin input.darts) (base : Tape → List Bool) :
    workingTapes input e base .head =
      encodeWord input.rows[input.rows[e].reverseIndex].tail.val := by
  simp [workingTapes, Lookup.headLookupTapes, MachineLookup.tapes, headPorts,
    Lookup.headValue, Lookup.headIndex]

/-- The three cleanup phases are actual drains in the concrete program. -/
def clearFieldsInTime (base : Tape → List Bool) (ambient : Ambient q) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some (.clearField 0), (ambient, none), base⟩
      (some ⟨some .increment, (ambient, none), clearFieldsTapes base⟩)
      ((base .tail).length + (base .reverseIndex).length + (base .head).length + 3) := by
  let first := MachineDrain.drainInTime Tape.tail (Driver.Label.clearField 0)
    (some (.clearField 1)) (Driver.program q) (by rfl) base ambient none
  let second := MachineDrain.drainInTime Tape.reverseIndex (Driver.Label.clearField 1)
    (some (.clearField 2)) (Driver.program q) (by rfl)
    (Function.update base .tail []) ambient none
  let third := MachineDrain.drainInTime Tape.head (Driver.Label.clearField 2)
    (some .increment) (Driver.program q) (by rfl)
    (Function.update (Function.update base .tail []) .reverseIndex []) ambient none
  let firstTwo := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ firstTwo third
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have h := run.steps_le_m
  simp only [Function.update_of_ne (by decide : Tape.reverseIndex ≠ .tail),
    Function.update_of_ne (by decide : Tape.head ≠ .reverseIndex),
    Function.update_of_ne (by decide : Tape.head ≠ .tail)] at h
  omega

def incrementInTime (base : Tape → List Bool) (ambient : Ambient q)
    (e : Nat) (he : base .edge = encodeWord e) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some .increment, (ambient, none), base⟩
      (some ⟨some .guard, (ambient, none), Function.update base .edge (encodeWord (e + 1))⟩)
      1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (nextRow (Driver.Label.guard : Driver.Label q))
      (ambient, none) base) = _
    simpa only [List.append_nil] using congrArg some
      (stepAux_nextRow (Driver.Label.guard : Driver.Label q) (ambient, none) base e []
        (by simpa only [List.append_nil] using he))
  steps_le_m := Nat.le_refl _

theorem emitterView_at (label :
    Emitter.Label (Driver.rowPlan q).length (Addresses.fieldBound q)) :
    (MachineControl.program (Equiv.refl (Driver.Label q)) (emitterEquiv q).symm
      (Driver.program q)) (.emit label) =
      Emitter.statement (Emitter.listCommands (Driver.rowPlan q)) rowSources
        Tape.scratch Tape.reversed Driver.Label.emit (some (.clearField 0)) label := by
  change MachineControl.statement id (emitterEquiv q).symm
    (MachineControl.statement id (emitterEquiv q) _) = _
  exact MachineFieldProfile.statement_roundtrip (emitterEquiv q).symm _

theorem context_rowState (input : GenericGraphTables.Table q)
    (e : Fin input.darts) :
    context (CompareLoop.rowState input e).1 = EmitRows.rowContext input e := by
  change (input.rows[e].relation,
    decide (input.rows[e].tail.val = input.rows[input.rows[e].reverseIndex].tail.val)) =
      (input.rows[e].relation,
        decide (input.rows[e].tail = input.rows[input.rows[e].reverseIndex].tail))
  simp only [Fin.val_inj]

/-- Execute the actual emitted row block through the finite register equivalence. -/
def emitInTime (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool)
    (operands : ∀ i, base (rowSources i) = encodeWord (EmitRows.rowValues input e i))
    (scratchEmpty : base .scratch = []) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some (Driver.rowEntry q), CompareLoop.rowState input e, base⟩
      (some ⟨some (.clearField 0), CompareLoop.rowState input e,
        Emitter.resultTapes .reversed base (encodeWords (EmitRows.blockWords input e))⟩)
      (Enumeration.localCount q * (6 * (2 * 4104)) *
        (3 * ((LoopState.inputBits input).length + 1) + 3) + 1) := by
  let view := MachineControl.program (Equiv.refl (Driver.Label q)) (emitterEquiv q).symm
    (Driver.program q)
  have sourceScratch : ∀ i : Fin 5, rowSources i ≠ Tape.scratch := by
    intro i; fin_cases i <;> decide
  have sourceOutput : ∀ i : Fin 5, rowSources i ≠ Tape.reversed := by
    intro i; fin_cases i <;> decide
  have bounded : ∀ i, EmitRows.rowValues input e i ≤ (LoopState.inputBits input).length := by
    have hn := GenericGraphTables.vertices_le_tableBits_length input
    have hm := GenericGraphTables.darts_le_tableBits_length input
    have he := e.isLt
    have ht := input.rows[e].tail.isLt
    have hh := input.rows[input.rows[e].reverseIndex].tail.isLt
    intro i
    fin_cases i <;> simp [EmitRows.rowValues, Addresses.values, LoopState.inputBits] <;> omega
  have run := EmitRows.blockInTimeAmbient input e (@context q)
    (CompareLoop.rowState input e).1 (context_rowState input e)
    rowSources Tape.scratch Tape.reversed sourceScratch sourceOutput (by decide)
    Driver.Label.emit (some (.clearField 0)) view emitterView_at base operands
    scratchEmpty (LoopState.inputBits input).length bounded
  have restored : MachineControl.program (Equiv.refl (Driver.Label q)) (emitterEquiv q) view =
      Driver.program q := by
    funext label
    exact MachineFieldProfile.statement_roundtrip (emitterEquiv q) (Driver.program q label)
  have transported := transportInTime (emitterEquiv q) view run
  rw [restored] at transported
  simpa [MachineControl.configuration, emitterEquiv, Option.map_some, id_eq,
    Driver.rowEntry, Driver.rowPlan, CompareLoop.rowState, normal] using transported

theorem result_ready (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) (ready : LoopState.Ready input e.val base) :
    LoopState.Ready input (e.val + 1) (resultTapes input e base) := by
  constructor
  · exact Nat.succ_le_of_lt e.isLt
  all_goals simp [resultTapes, clearFieldsTapes, emittedTapes, Emitter.resultTapes,
    workingTapes, Lookup.headLookupTapes, MachineLookup.tapes, headPorts,
    parsedTapes, Lookup.readRowTapes, guardTapes, ready.original, ready.vertices,
    ready.darts, ready.scratch, ready.compareLeft, ready.compareRight, ready.output,
    ready.reversed, LoopState.prefixBits_reverse_succ input e.val e.isLt]

theorem workingOperands (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) (ready : LoopState.Ready input e.val base) :
    ∀ i, workingTapes input e base (rowSources i) =
      encodeWord (EmitRows.rowValues input e i) := by
  intro i
  fin_cases i <;> simp [rowSources, EmitRows.rowValues, Addresses.values,
    workingTapes, Lookup.headLookupTapes, MachineLookup.tapes, headPorts,
    parsedTapes, Lookup.readRowTapes, guardTapes, Lookup.headValue, Lookup.headIndex,
    ready.vertices, ready.darts, ready.edge]

/-- Execute a whole row iteration from the exact guard invariant. Every run
below is obtained from the concrete code at its component labels. -/
def rowStep (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) (ready : LoopState.Ready input e.val base)
    (oldRelation : GenericGraphTables.RelationTable q) (oldFlag : Bool) :
    RowStepResult input e base oldRelation oldFlag := by
  let N := (LoopState.inputBits input).length
  have guarded : StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some .guard, normal oldRelation oldFlag, base⟩
      (some ⟨some .tailStart, normal oldRelation oldFlag, guardTapes input e base⟩) 1 := by
    have hbase : MachineUnaryCounter.counterTapes .counter base
        (input.darts - (e.val + 1) + 1) [] = base := by
      simp only [MachineUnaryCounter.counterTapes, List.append_nil,
        ← ready.counter_succ e.isLt, Function.update_eq_self]
    have run := MachineUnaryCounter.guardInTime_succ Tape.counter Driver.Label.guard
      .tailStart .reverseOutput (Driver.program q) (by rfl) base
      (input.darts - (e.val + 1)) [] (normal oldRelation oldFlag).1 none
    rw [hbase] at run
    simpa only [MachineUnaryCounter.counterTapes, List.append_nil, guardTapes,
      normal] using run
  have parsed : StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some .tailStart, normal oldRelation oldFlag, guardTapes input e base⟩
      (some ⟨some .headCopyFirst, normal input.rows[e].relation oldFlag,
        parsedTapes input e base⟩) (Lookup.readRowCost input.rows[e]) := by
    have hcursor : guardTapes input e base .cursor = Lookup.rowBits input.rows[e] ++
        LoopState.cursorBits input (e.val + 1) := by
      simpa only [guardTapes, Function.update_of_ne (by decide : Tape.cursor ≠ .counter),
        Lookup.rowBits] using ready.cursor.trans (LoopState.cursorBits_succ input e.val e.isLt)
    have htail : guardTapes input e base .tail = [] := by simp [guardTapes, ready.tail]
    have hreverse : guardTapes input e base .reverseIndex = [] := by
      simp [guardTapes, ready.reverseIndex]
    simpa only [normal, parsedTapes] using
      Lookup.readRowInTime Tape.cursor Tape.tail Tape.reverseIndex
        (by decide) (by decide) (by decide) Driver.Label.tailStart .tailLoop
        .reverseStart .reverseLoop .readPredicate .headCopyFirst (Driver.program q)
        (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
        (guardTapes input e base) input.rows[e] (LoopState.cursorBits input (e.val + 1))
        hcursor htail hreverse (oldFlag, false, none) oldRelation none
  have looked : StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some .headCopyFirst, normal input.rows[e].relation oldFlag, parsedTapes input e base⟩
      (some ⟨some (.compare .leftFirst), normal input.rows[e].relation oldFlag,
        workingTapes input e base⟩) (7 * N + 5) := by
    have htable : parsedTapes input e base (headPorts 0) = GenericGraphTables.tableBits input := by
      simpa [headPorts, parsedTapes, Lookup.readRowTapes, guardTapes,
        LoopState.inputBits] using ready.original
    have hreverse : parsedTapes input e base (headPorts 1) =
        encodeWord (Lookup.headIndex input e).val := by
      simp [headPorts, parsedTapes, Lookup.readRowTapes, Lookup.headIndex]
    have hhead : parsedTapes input e base (headPorts 4) = [] := by
      simp [headPorts, parsedTapes, Lookup.readRowTapes, guardTapes, ready.head]
    have hscratch : parsedTapes input e base (headPorts 5) = [] := by
      simp [headPorts, parsedTapes, Lookup.readRowTapes, guardTapes, ready.scratch]
    have run := Lookup.headLookupInTime headPorts headPorts_injective
      Driver.Label.headCopyFirst .headCopySecond .indexCopyFirst .indexCopySecond
      .headVertices .headDarts Driver.Label.headLookup (some (.compare .leftFirst))
      (Driver.program q) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (fun _ => rfl) (parsedTapes input e base) input e htable hreverse hhead hscratch
      (normal input.rows[e].relation oldFlag).1 none
    simpa only [workingTapes, normal, N, LoopState.inputBits, Lookup.headTimePolynomial,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] using run
  have hleft : workingTapes input e base .compareLeft = [] :=
    (workingTapes_other input e base .compareLeft (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans ready.compareLeft
  have hright : workingTapes input e base .compareRight = [] :=
    (workingTapes_other input e base .compareRight (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans ready.compareRight
  have hscratch : workingTapes input e base .scratch = [] :=
    (workingTapes_other input e base .scratch (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans ready.scratch
  let compared := CompareLoop.compareRowInTime Driver.Label.compare (Driver.rowEntry q)
    (Driver.program q) (fun _ => rfl) input e (workingTapes input e base)
    (workingTapes_tail input e base) (workingTapes_head input e base)
    hleft hright hscratch oldFlag
  let emitted := emitInTime input e (workingTapes input e base)
    (workingOperands input e base ready) hscratch
  let cleared := clearFieldsInTime (emittedTapes input e base) (CompareLoop.rowState input e).1
  have hedge : clearFieldsTapes (emittedTapes input e base) .edge = encodeWord e.val := by
    simp [clearFieldsTapes, emittedTapes, Emitter.resultTapes, workingTapes,
      Lookup.headLookupTapes, MachineLookup.tapes, headPorts, parsedTapes,
      Lookup.readRowTapes, guardTapes, ready.edge]
  let incremented := incrementInTime (clearFieldsTapes (emittedTapes input e base))
    (CompareLoop.rowState input e).1 e.val hedge
  let run₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ guarded parsed
  let run₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ looked
  let run₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₂ compared
  let run₄ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₃ emitted
  let run₅ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₄ cleared
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₅ incremented
  refine {
    tapes := resultTapes input e base
    ready := result_ready input e base ready
    run := { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  }
  have hn : input.vertices ≤ N := GenericGraphTables.vertices_le_tableBits_length input
  have hm : input.darts ≤ N := GenericGraphTables.darts_le_tableBits_length input
  have hr : Lookup.readRowCost input.rows[e] ≤ 2 * N + 5 :=
    Lookup.readRowCost_table_le input e
  have ht : (emittedTapes input e base .tail).length ≤ N := by
    simp only [emittedTapes, Emitter.resultTapes,
      Function.update_of_ne (by decide : Tape.tail ≠ .reversed), workingTapes_tail,
      encodeWord_length]
    exact (Nat.succ_le_of_lt input.rows[e].tail.isLt).trans hn
  have hv : (emittedTapes input e base .reverseIndex).length ≤ N := by
    simp only [emittedTapes, Emitter.resultTapes,
      Function.update_of_ne (by decide : Tape.reverseIndex ≠ .reversed), workingTapes_reverse,
      encodeWord_length]
    exact (Nat.succ_le_of_lt input.rows[e].reverseIndex.isLt).trans hm
  have hh : (emittedTapes input e base .head).length ≤ N := by
    simp only [emittedTapes, Emitter.resultTapes,
      Function.update_of_ne (by decide : Tape.head ≠ .reversed), workingTapes_head,
      encodeWord_length]
    exact (Nat.succ_le_of_lt input.rows[input.rows[e].reverseIndex].tail.isLt).trans hn
  have budget := run.steps_le_m
  change run.steps ≤ (32 + 8 * (Enumeration.localCount q * (6 * (2 * 4104)))) * (N + 1)
  nlinarith

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Body

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_FinalBooleanVerifier
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.FinalBooleanVerifier

open Target

variable {V E : Type*} {n m : Nat}

theorem cnf_completeness (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (sat : G.Satisfiable) : (cnf G vertices edges).Satisfiable := by
  obtain ⟨labeling, satisfied⟩ := sat
  exact VerifierToCNF.convert_completeness (verifier G vertices edges) (by decide)
    (bitsOfLabels vertices labeling) (verifier_completeness G vertices edges labeling satisfied)

theorem cnf_count_bridge [Fintype E] (G : ConstraintGraph V E Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) (assignment : OutputAssignment G vertices edges) :
    G.rejectionCount (extractLabeling G vertices edges assignment) ≤
      NameCompaction.failedCount (cnf G vertices edges) assignment := by
  have h := VerifierToCNF.convert_count_bridge (verifier G vertices edges) (by decide) assignment
  rw [rejection_count_eq] at h
  exact h

theorem failedCount_zero_of_satisfied (F : Formula) (assignment : Fin F.variables → Bool)
    (satisfied : ∀ c ∈ F.clauses, c.eval assignment = true) :
    NameCompaction.failedCount F assignment = 0 := by
  apply (VerifierToCNF.zero_false_count_iff_all _).mpr
  have h := List.all_eq_true.mpr satisfied
  simpa only [NameCompaction.evaluationList, List.all_map, Function.comp_def, id_eq] using h

theorem cnf_reflects [Fintype E] (G : ConstraintGraph V E Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) (sat : (cnf G vertices edges).Satisfiable) :
    G.Satisfiable := by
  obtain ⟨assignment, satisfied⟩ := sat
  have zero := failedCount_zero_of_satisfied (cnf G vertices edges) assignment satisfied
  have bound := cnf_count_bridge G vertices edges assignment
  have graphZero : G.rejectionCount (extractLabeling G vertices edges assignment) = 0 := by omega
  exact ⟨extractLabeling G vertices edges assignment,
    all_satisfied_of_rejectionCount_zero G _ graphZero⟩

theorem cnf_satisfiable_iff [Fintype E] (G : ConstraintGraph V E Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) :
    (cnf G vertices edges).Satisfiable ↔ G.Satisfiable :=
  ⟨cnf_reflects G vertices edges, cnf_completeness G vertices edges⟩

theorem cnf_nonempty (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (nonempty : 0 < m) : (cnf G vertices edges).clauses ≠ [] :=
  VerifierToCNF.convert_nonempty (verifier G vertices edges) (by decide) nonempty

theorem cnf_gap [Fintype E] (G : ConstraintGraph V E Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) (a b : Nat)
    (source : ∀ labeling : V → Label, a * Fintype.card E ≤ b * G.rejectionCount labeling)
    (assignment : OutputAssignment G vertices edges) :
    a * (cnf G vertices edges).clauses.length ≤
      (b * 40960) * NameCompaction.failedCount (cnf G vertices edges) assignment := by
  have cardEdges : Fintype.card E = m := by simpa using Fintype.card_congr edges
  have testGap (bits : Fin (n * 6) → Bool) :
      a * m ≤ b * VerifierToCNF.rejectedEventCount (verifier G vertices edges) bits := by
    rw [rejection_count_eq]
    simpa only [cardEdges] using source (labelsOfBits vertices bits)
  simpa only [cnf, VerifierToCNF.twelve_query_factor] using
    VerifierToCNF.convert_gap (verifier G vertices edges) (by decide) a b testGap assignment

end UniqueGamesTheorem.Foundations.PCP.FinalBooleanVerifier

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_Initialization
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
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

def inputTapes (input : GenericGraphTables.Table q) : Tape → List Bool
  | .original => GenericGraphTables.tableBits input
  | _ => []

def setupTapes (input : GenericGraphTables.Table q) : Tape → List Bool
  | .original => GenericGraphTables.tableBits input
  | .cursor => rowsBits input
  | .vertices => encodeWord input.vertices
  | .darts | .counter => encodeWord input.darts
  | .edge => encodeWord 0
  | _ => []

/-- Complete initial loop state. Every auxiliary tape not listed here is empty. -/
def loopTapes (input : GenericGraphTables.Table q) : Tape → List Bool
  | .original => GenericGraphTables.tableBits input
  | .cursor => rowsBits input
  | .vertices => encodeWord input.vertices
  | .darts | .counter => encodeWord input.darts
  | .edge => encodeWord 0
  | .reversed => (headerBits input).reverse
  | _ => []

def loopStart (input : GenericGraphTables.Table q) :
    TM2.Cfg Alphabet (Driver.Label q) (State q) :=
  ⟨some .guard, initial q, loopTapes input⟩

theorem setupResult_eq (input : GenericGraphTables.Table q) :
    Setup.resultTapes setupPorts (inputTapes input) input.vertices input.darts (rowsBits input) =
      setupTapes input := by
  funext tape
  cases tape <;> simp [Setup.resultTapes, setupPorts, inputTapes, setupTapes]

theorem headerResult_eq (input : GenericGraphTables.Table q) :
    Emitter.resultTapes Tape.reversed (setupTapes input) (headerBits input) = loopTapes input := by
  funext tape
  cases tape <;> simp [Emitter.resultTapes, setupTapes, loopTapes]

theorem machineInitial_eq (input : GenericGraphTables.Table q) :
    initList (Driver.machine q) (GenericGraphTables.tableBits input) =
      (⟨some (.setup .copyFirst), initial q, inputTapes input⟩ :
        TM2.Cfg Alphabet (Driver.Label q) (State q)) := by
  change (⟨some (.setup .copyFirst), initial q, _⟩ :
    TM2.Cfg Alphabet (Driver.Label q) (State q)) = _
  congr 1
  funext tape
  cases tape <;> rfl

/-- The driver executes its actual setup statements from its actual input configuration. -/
def setupInTime (input : GenericGraphTables.Table q) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      (initList (Driver.machine q) (GenericGraphTables.tableBits input))
      (some ⟨some (Driver.headerEntry q), initial q, setupTapes input⟩)
      (6 * (GenericGraphTables.tableBits input).length + 11) := by
  have initialized : ∀ i : Fin 7, inputTapes input (setupPorts i) =
      if i = 0 then GenericGraphTables.tableBits input else [] := by
    intro i
    fin_cases i <;> rfl
  have run := Setup.tableSetupInTime setupPorts setupPorts_injective Driver.Label.setup
    (some (Driver.headerEntry q)) (Driver.program q) (Driver.program_setup q)
    (inputTapes input) input initialized (initial q).1 none
  have initialState : ((initial q).1, (none : Option Bool)) = initial q := rfl
  have result := setupResult_eq input
  unfold rowsBits at result
  rw [initialState, result] at run
  rw [machineInitial_eq]
  exact run

theorem headerView_at (label : Emitter.Label (Driver.headerPlan q).length
    (Addresses.fieldBound q)) :
    (MachineControl.program (Equiv.refl (Driver.Label q)) (emitterEquiv q).symm
      (Driver.program q)) (.header label) =
      Emitter.statement (Emitter.listCommands (Driver.headerPlan q)) headerSources
        Tape.scratch Tape.reversed Driver.Label.header (some .guard) label := by
  change MachineControl.statement id (emitterEquiv q).symm
    (MachineControl.statement id (emitterEquiv q) _) = _
  exact MachineFieldProfile.statement_roundtrip (emitterEquiv q).symm _

/-- No header execution is assumed: the checked template is instantiated at
the concrete driver labels and transported through the finite state layout. -/
def headerInTime (input : GenericGraphTables.Table q) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some (Driver.headerEntry q), initial q, setupTapes input⟩
      (some (loopStart input))
      (7 * (3 * ((GenericGraphTables.tableBits input).length + 1) + 3) + 1) := by
  let view := MachineControl.program (Equiv.refl (Driver.Label q)) (emitterEquiv q).symm
    (Driver.program q)
  have sourceScratch : ∀ i : Fin 2, headerSources i ≠ Tape.scratch := by
    intro i
    fin_cases i <;> decide
  have sourceOutput : ∀ i : Fin 2, headerSources i ≠ Tape.reversed := by
    intro i
    fin_cases i <;> decide
  have operands : ∀ i : Fin 2, setupTapes input (headerSources i) =
      encodeWord (![input.vertices, input.darts] i) := by
    intro i
    fin_cases i <;> rfl
  have run := EmitRows.headerInTime q input.vertices input.darts headerSources
    Tape.scratch Tape.reversed sourceScratch sourceOutput (by decide)
    Driver.Label.header (some .guard) view headerView_at
    (setupTapes input) operands (by rfl) (initial q).1
    (GenericGraphTables.tableBits input).length
    (GenericGraphTables.vertices_le_tableBits_length input)
    (GenericGraphTables.darts_le_tableBits_length input)
  have restored : MachineControl.program (Equiv.refl (Driver.Label q)) (emitterEquiv q) view =
      Driver.program q := by
    funext label
    exact MachineFieldProfile.statement_roundtrip (emitterEquiv q) (Driver.program q label)
  have transported := transportInTime (emitterEquiv q) view run
  rw [restored] at transported
  change StateTransition.EvalsToInTime (TM2.step (Driver.program q))
    ⟨some (Driver.headerEntry q), initial q, setupTapes input⟩
    (some ⟨some .guard, initial q,
      Emitter.resultTapes Tape.reversed (setupTapes input) (headerBits input)⟩)
    (7 * (3 * ((GenericGraphTables.tableBits input).length + 1) + 3) + 1) at transported
  rw [headerResult_eq] at transported
  exact transported

/-- Actual initialization of the complete finite driver, ending at its first
guard with the exact input, counter, cursor, index, and reversed headers. -/
def initializeInTime (input : GenericGraphTables.Table q) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      (initList (Driver.machine q) (GenericGraphTables.tableBits input))
      (some (loopStart input)) (time (GenericGraphTables.tableBits input).length) := by
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (setupInTime input) (headerInTime input)
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have bound := run.steps_le_m
  unfold time
  omega

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Initialization

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PreprocessingTableSpectral
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
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

/-- The stored overlaid graph is the actual semantic overlay in numbered
port coordinates. This is equality of reversible port graphs. -/
theorem overlay_portGraph {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) :
    PortTables.portGraph (PreprocessingOverlayTables.overlay G H) =
      GraphTransport.reindex
        (Overlay.portGraph (PortTables.portGraph G) (ExpanderTables.graph H))
        (Equiv.refl _) (PreprocessingOverlayTables.overlayPorts d e) := by
  unfold PreprocessingOverlayTables.overlay
  rw [materialize_portGraph]
  rfl

/-- An actual half-spectral expander overlay gives a `7/8` certificate for
the stored table. The original table needs no spectral certificate.
The degree hypothesis supplies nonempty old and expander port types. -/
theorem overlay_certificate_seven_eighths {n d e : Nat}
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (hn : 0 < n) (hdegree : d = e + 1) (he : 8 ≤ e)
    (hH : SpectralCertificate (ExpanderTables.graph H) (1 / 2 : ℝ)) :
    SpectralCertificate (PortTables.portGraph (PreprocessingOverlayTables.overlay G H))
      (7 / 8 : ℝ) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [overlay_portGraph]
  apply GraphTransport.reindex_spectralCertificate
  apply Overlay.spectralCertificate_seven_eighths
    (PortTables.portGraph G) (ExpanderTables.graph H)
  · simpa only [Fintype.card_fin] using hdegree
  · simp only [Fintype.card_fin]
    omega
  · exact hH

end UniqueGamesTheorem.Foundations.PCP.PreprocessingTableSpectral

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PreprocessingTablesLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

theorem overlayFamily_certificate (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) :
    SpectralCertificate (ExpanderTables.graph (overlayFamily H t)) (1 / 2 : ℝ) := by
  let : NeZero Expanders.baseDegree := ⟨PreprocessingRegularSoundness.baseDegree_ne_zero⟩
  apply PreprocessingRegularSoundness.resizeTable_certificate
  exact ExpanderTables.family_certificate H certificate _

theorem overlay_certificate (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) :
    SpectralCertificate (PortTables.portGraph
      (PreprocessingOverlayTables.overlay (padded H t) (overlayFamily H t))) (7 / 8 : ℝ) :=
  PreprocessingTableSpectral.overlay_certificate_seven_eighths _ _
    (vertices_positive t) rfl PreprocessingRegularSoundness.internalDegree_ge_eight
    (overlayFamily_certificate H certificate t)

theorem soundness (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) (labels : Fin (vertices t) → GraphTables.Label) :
    (GraphTables.semantics t).rejectionCount (roundLabels t labels) ≤
      (PortTables.baseGraph (preprocess H t)).rejectionCount labels := by
  rw [rejectionCount_eq_regularized]
  exact PreprocessingRegularSoundness.soundness H certificate t (restrictedLabel t labels)

theorem gap_transfer_real (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) (ht : 0 < t.darts)
    (epsilon : ℝ) (he : 0 ≤ epsilon)
    (lower : ∀ labels : Fin t.vertices → GraphTables.Label,
      epsilon * t.darts ≤ ((GraphTables.semantics t).rejectionCount labels : ℝ))
    (labels : Fin (vertices t) → GraphTables.Label) :
    (epsilon / Preprocessing.sizeFactor) *
        Fintype.card (Fin (vertices t) × Fin PreprocessingTables.degree) ≤
      ((PortTables.baseGraph (preprocess H t)).rejectionCount labels : ℝ) := by
  have hs : (0 : ℝ) < Preprocessing.sizeFactor :=
    Nat.cast_pos.mpr Preprocessing.sizeFactor_positive
  have hcount : Fintype.card (Fin (vertices t) × Fin PreprocessingTables.degree) ≤
      Preprocessing.sizeFactor * t.darts := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    calc
      _ ≤ (ExpanderFamily.growth ^ 2 * t.darts) * PreprocessingTables.degree :=
        Nat.mul_le_mul_right _ (vertices_le_of_positive t ht)
      _ = _ := by rw [PreprocessingTables.degree_eq]; unfold Preprocessing.sizeFactor; ring
  have hcountR : (Fintype.card (Fin (vertices t) × Fin PreprocessingTables.degree) : ℝ) ≤
      (Preprocessing.sizeFactor : ℝ) * t.darts := by exact_mod_cast hcount
  calc
    _ ≤ (epsilon / Preprocessing.sizeFactor) *
        ((Preprocessing.sizeFactor : ℝ) * t.darts) :=
      mul_le_mul_of_nonneg_left hcountR (div_nonneg he hs.le)
    _ = epsilon * t.darts := by field_simp
    _ ≤ ((GraphTables.semantics t).rejectionCount (roundLabels t labels) : ℝ) := lower _
    _ ≤ _ := Nat.cast_le.mpr (soundness H certificate t labels)

end UniqueGamesTheorem.Foundations.PCP.PreprocessingGuarantees

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_RawInitialTablesLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.sourceIndexNonempty _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

theorem raw64_satisfiable_iff (F : Formula) : (raw64 F).Satisfiable ↔ F.Satisfiable :=
  (AlphabetRetraction.satisfiable_pullback_iff (InitialGraph.raw F)
    AlphabetRetraction.decode64 AlphabetRetraction.encode64
      AlphabetRetraction.decode_encode64).trans (InitialGraph.raw_satisfiable_iff F)

theorem table_semantics (F : Formula) :
    GraphTables.semantics (table F) =
      (raw64 F).reindex (vertexOrder F) (dartOrder F) labelOrder := by
  change GraphTables.semantics (GraphTables.ofGraph
    (GraphTables.enumeratedGraph (raw64 F) (vertexOrder F) (dartOrder F) labelOrder)) = _
  rw [GraphTables.semantics_ofGraph]
  rfl

theorem table_satisfiable_iff (F : Formula) :
    (GraphTables.semantics (table F)).Satisfiable ↔ F.Satisfiable := by
  rw [table_semantics]
  exact ((raw64 F).satisfiable_reindex (vertexOrder F) (dartOrder F) labelOrder).trans
    (raw64_satisfiable_iff F)

end UniqueGamesTheorem.Foundations.PCP.RawInitialTables

/-! Polynomial arithmetic for the actual initial-machine phase counts. The
separate execution theorem must connect these counts to the concrete program. -/

/-! Explicit finite predicates and numeric row words of the initial incidence table.
Every relation retains all 4096 entries, including repetitions. -/

/-! The concrete numbered amplification round, with one fixed base expander.
Every intermediate is an actual stored table, with explicit finite coordinates.
The running-time certificate is a separate theorem about these same functions. -/

namespace UniqueGamesTheorem.Foundations.PCP.RoundTables

theorem build_completeness (H : BaseTable) (table : GraphTables.Table)
    (sat : (GraphTables.semantics table).Satisfiable) :
    (GraphTables.semantics (build H table)).Satisfiable := by
  let : Nonempty (Fin alphabet) := ⟨⟨0, alphabet_positive⟩⟩
  exact AlphabetTable.Table.perfect_completeness (powered H table)
    (PoweringTableSemantics.preserves_satisfiability
      (PreprocessingTables.preprocess H table) walkParameter
      (PreprocessingGuarantees.completeness H table sat))

instance instNonemptyFinDartsValTableLtNatOfNat (input : Input) : Nonempty (Fin input.val.darts) := ⟨⟨0, input.property⟩⟩

def Satisfiable (input : Input) : Prop := (GraphTables.semantics input.val).Satisfiable

noncomputable def gap (input : Input) : ℝ := (GraphTables.semantics input.val).gap

theorem gap_nonnegative (input : Input) : 0 ≤ gap input :=
  (GraphTables.semantics input.val).gap_nonnegative

theorem one_le_size_mul_gap (input : Input) (unsat : ¬ Satisfiable input) :
    1 ≤ (size input : ℝ) * gap input := by
  have h := (GraphTables.semantics input.val).inverse_card_le_gap_of_unsatisfiable unsat
  have hp : (0 : ℝ) < input.val.darts := Nat.cast_pos.mpr input.property
  simp only [Fintype.card_fin] at h
  have hd := (div_le_iff₀ hp).mp h
  have hsize : (input.val.darts : ℝ) ≤ (size input : ℝ) := by
    exact_mod_cast (Nat.le_add_left input.val.darts input.val.vertices)
  exact (show 1 ≤ (input.val.darts : ℝ) * gap input by
    simpa only [gap, mul_comm] using hd).trans
    (mul_le_mul_of_nonneg_right hsize (gap_nonnegative input))

theorem step_completeness (H : BaseTable) (input : Input) :
    Satisfiable input → Satisfiable (step H input) := build_completeness H input.val

end UniqueGamesTheorem.Foundations.PCP.RoundTables

/-! Gap amplification for the actual numbered table round. The fixed base
expander is the only supplied construction datum with a spectral certificate. -/

namespace UniqueGamesTheorem.Foundations.PCP.RoundTableGap

open RoundTables
open PoweringWalks SpectralReturn

variable (H : BaseTable)
  (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))

include certificate

theorem powered_count_gap (input : Input)
    (labeling : Fin (powered H input.val).vertices → Fin alphabet) :
    RoundGap.poweredLower (gap input) * ((powered H input.val).darts : ℝ) ≤
      ((GenericGraphTables.semantics (powered H input.val)).rejectionCount labeling : ℝ) := by
  let old := PreprocessingOverlayTables.overlay
    (PreprocessingTables.padded H input.val) (PreprocessingTables.overlayFamily H input.val)
  have hd : 0 < (PreprocessingRegularTables.internalDegree + 1) +
      PreprocessingRegularTables.internalDegree := by omega
  let : Nonempty (Fin ((PreprocessingRegularTables.internalDegree + 1) +
      PreprocessingRegularTables.internalDegree)) := ⟨⟨0, hd⟩⟩
  have spectral : SpectralCertificate (lazyGraph (PortTables.portGraph old)) (31 / 32 : ℝ) :=
    LazySpectral.lazy_certificate_31_32 (PortTables.portGraph old)
      (PreprocessingGuarantees.overlay_certificate H certificate input.val)
  have lower := PreprocessingGuarantees.gap_transfer_real H certificate input.val input.property
    (gap input) (gap_nonnegative input)
    (by simpa only [Fintype.card_fin] using
      ((GraphTables.semantics input.val).le_gap_iff (gap input)).mp le_rfl)
  have hs : (0 : ℝ) < Preprocessing.sizeFactor := Nat.cast_pos.mpr Preprocessing.sizeFactor_positive
  have hn : walkParameter = 2 * PoweringSoundness.center 64 FinalConstants.windowHalf :=
    walkParameter_eq
  have bound := PoweringPortReindex.lazy_table_uniform_count_gap_at old
    (PreprocessingTables.vertices_positive input.val) hd (31 / 32) spectral
    FinalConstants.windowHalf FinalConstants.windowHalf_positive walkParameter hn
    (gap input / Preprocessing.sizeFactor) (div_nonneg (gap_nonnegative input) hs.le)
    lower labeling
  have hw : walkParameter + 1 = FinalConstants.walkLength := by
    rw [walkParameter_eq]
    rfl
  simpa only [RoundGap.poweredLower, PoweringFinalConstants.card_alphabet,
    hw, FinalConstants.cap, powered, PreprocessingTables.preprocess, old] using! bound

theorem build_count_gap (input : Input)
    (labeling : Fin (build H input.val).vertices → GraphTables.Label) :
    min (2 * gap input) FinalConstants.cap * ((build H input.val).darts : ℝ) ≤
      ((GraphTables.semantics (build H input.val)).rejectionCount labeling : ℝ) := by
  have h := AlphabetTableBounds.gap_transfer_real alphabet_positive (powered H input.val)
    (RoundGap.poweredLower (gap input))
    (RoundGap.poweredLower_nonnegative (gap input) (gap_nonnegative input))
    (powered_count_gap H certificate input) labeling
  have scalar : min (2 * gap input) FinalConstants.cap ≤
      RoundGap.poweredLower (gap input) / 12288 := by
    simpa only [RoundGap.poweredLower, FinalConstants.cap, FinalConstants.walkLength,
      PoweringFinalConstants.center_eq] using
      PoweringFinalConstants.composed_scaled_gap (gap input) (gap_nonnegative input)
  exact (mul_le_mul_of_nonneg_right scalar (Nat.cast_nonneg _)).trans h

theorem step_gap (input : Input) :
    min (2 * gap input) FinalConstants.cap ≤ gap (step H input) := by
  apply ((GraphTables.semantics (step H input).val).le_gap_iff _).mpr
  simp only [step]
  intro labeling
  erw [Fintype.card_fin]
  exact build_count_gap H certificate input labeling

end UniqueGamesTheorem.Foundations.PCP.RoundTableGap

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_LoopInitializationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
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

/-- Concrete final configuration and full remaining-loop execution. -/
structure LoopResult (input : GenericGraphTables.Table q) (e remaining : Nat)
    (base : Tape → List Bool) (oldRelation : GenericGraphTables.RelationTable q)
    (oldFlag : Bool) where
  tapes : Tape → List Bool
  relation : GenericGraphTables.RelationTable q
  flag : Bool
  ready : LoopState.Ready input input.darts tapes
  run : StateTransition.EvalsToInTime (TM2.step (Driver.program q))
    ⟨some .guard, normal oldRelation oldFlag, base⟩
    (some ⟨some .reverseOutput, normal relation flag, tapes⟩)
    (remaining * Body.bodyTime q (LoopState.inputBits input).length + 1)

-- Preserve the concrete run-size contribution in the derived PrefixResult instance.
noncomputable local instance prefixRunSizeOf (input : GenericGraphTables.Table q)
    (tapes : Tape → List Bool) (relation : GenericGraphTables.RelationTable q) (flag : Bool) :
    SizeOf (StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      (initList (Driver.machine q) (GenericGraphTables.tableBits input))
      (some ⟨some .reverseOutput, normal relation flag, tapes⟩)
      (prefixTime q (LoopState.inputBits input).length)) :=
  @StateTransition.EvalsToInTime._sizeOf_inst
    (TM2.Cfg Alphabet (Driver.Label q) (State q))
    (TM2.step (Driver.program q))
    (initList (Driver.machine q) (GenericGraphTables.tableBits input))
    (some ⟨some .reverseOutput, normal relation flag, tapes⟩)
    (prefixTime q (LoopState.inputBits input).length) inferInstance

/-- Actual initialization followed by every row, ending just before reversal. -/
structure PrefixResult (input : GenericGraphTables.Table q) where
  tapes : Tape → List Bool
  relation : GenericGraphTables.RelationTable q
  flag : Bool
  ready : LoopState.Ready input input.darts tapes
  run : StateTransition.EvalsToInTime (TM2.step (Driver.program q))
    (initList (Driver.machine q) (GenericGraphTables.tableBits input))
    (some ⟨some .reverseOutput, normal relation flag, tapes⟩)
    (prefixTime q (LoopState.inputBits input).length)

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Loop



namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Runtime

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open RuntimeModel


noncomputable def time (q : Nat) : Polynomial Nat :=
  Finish.completedPolynomial q (prefixPolynomial q)

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Runtime



/-! Every work tape of the actual alphabet-table machine stores Bool symbols.
This checks the work alphabets separately from the finite-machine structure's
input-alphabet condition, without changing the runtime certificate. -/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable

open UniqueGamesTheorem.Foundations.Complexity

theorem Driver.finiteAlphabet (q : Nat) :
    MachineFiniteAlphabet.FiniteAlphabet (Driver.machine q) := by
  intro k
  change Finite Bool
  infer_instance

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable



/-! The actual padding, expander overlay, and lazy-loop stages composed into
one polynomial-time finite machine. The initial degree-replacement stage is
assembled separately. -/



/-! The complete actual preprocessing machine, including degree replacement,
vertex padding, explicit expander construction, overlay, and lazy edges. -/



/-!
Actual sequential finite-machine composition for the concrete numbered round.
The initial composition lemma isolates the preprocessing and powering execution
certificates with their shared bit codecs. The final endpoint supplies the
checked powering and alphabet machines, leaving only preprocessing explicit.
-/

namespace UniqueGamesTheorem.Foundations.PCP.RoundComputation

open Turing
open UniqueGamesTheorem.Foundations.Complexity


/-- The exact pending preprocessing interface, including its output encoding. -/
abbrev PreprocessingCertificate (H : RoundTables.BaseTable) :=
  TM2ComputableInPolyTime GraphTables.tableBits
    (PortTables.inputBits (ports := PreprocessingTables.degree))
    (PreprocessingTables.output H)

/-- The exact powering interface at the fixed parameters of the round. -/
abbrev PoweringCertificate :=
  TM2ComputableInPolyTime
    (PortTables.inputBits (ports := PreprocessingTables.degree))
    (GenericGraphTables.tableBits (q := RoundTables.alphabet))
    (PoweringTables.transform PreprocessingTables.degree RoundTables.walkParameter)

/-- Both actual transfer loops between the machines are included by
`MachineSequential.composeBits`; their work contributes to its polynomial. -/
noncomputable def poweredPolynomialTimeOfCertificates (H : RoundTables.BaseTable)
    (preprocessing : PreprocessingCertificate H) (powering : PoweringCertificate) :
    TM2ComputableInPolyTime GraphTables.tableBits
      (GenericGraphTables.tableBits (q := RoundTables.alphabet))
      (RoundTables.powered H) := by
  change TM2ComputableInPolyTime GraphTables.tableBits _
    (fun table => PoweringTables.transform PreprocessingTables.degree
      RoundTables.walkParameter (PreprocessingTables.output H table))
  exact MachineSequential.composeBits preprocessing powering

/-- All intermediate work alphabets stay finite under the actual sequential
composition, provided that they are finite in the two supplied machines. -/
theorem powered_finiteAlphabet (H : RoundTables.BaseTable)
    (preprocessing : PreprocessingCertificate H) (powering : PoweringCertificate)
    (hpreprocessing : MachineFiniteAlphabet.FiniteAlphabet preprocessing.tm)
    (hpowering : MachineFiniteAlphabet.FiniteAlphabet powering.tm) :
    MachineFiniteAlphabet.FiniteAlphabet
      (poweredPolynomialTimeOfCertificates H preprocessing powering).tm :=
  MachineFiniteAlphabet.composeBits preprocessing powering hpreprocessing hpowering

end UniqueGamesTheorem.Foundations.PCP.RoundComputation

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceFieldArrayLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceClauseLookup

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition SourceMachine

/-- The two header fields are physically consumed from the work copy. -/
theorem discardHeadersTrace (base : Tape → List Bool) (variableCount clauses : Nat)
    (suffix : List Bool) (hinput : base .work = encodeWords [variableCount, clauses] ++ suffix) :
    (advance (TM2.step program))^[variableCount + clauses + 2]
      (some ⟨some .headerFirst, ((), none), base⟩) =
      some ⟨some .guard, ((), none), Function.update base .work suffix⟩ := by
  have ht := discardFieldsTrace .work headerLabel program base 0 [variableCount, clauses]
    suffix (by
      intro r hr
      have he : r = 0 ∨ r = 1 := by simp at hr; omega
      rcases he with rfl | rfl <;> rfl) hinput ()
  simpa [encodeWords_length, headerLabel] using ht

/-- The fixed skip body consumes six complete unary fields and returns to the
same counter guard, preserving the counter and every other tape. -/
theorem discardSixTrace (base : Tape → List Bool) (values : List Nat)
    (hlen : values.length = 6) (suffix : List Bool)
    (hinput : base .work = encodeWords values ++ suffix) :
    (advance (TM2.step program))^[(encodeWords values).length]
      (some ⟨some (skipLabel 0), ((), none), base⟩) =
      some ⟨some .guard, ((), none), Function.update base .work suffix⟩ := by
  have ht := discardFieldsTrace .work skipLabel program base 0 values suffix
    (by intro r hr; simpa only [Nat.zero_add] using atSkip r (by omega)) hinput ()
  simpa [hlen, skipLabel] using ht

/-- Read the selected six fields using the already checked scanner. -/
theorem readSixTrace (base : Tape → List Bool) (values : List Nat)
    (hlen : values.length = 6) (suffix : List Bool)
    (hinput : base .work = encodeWords values ++ suffix) :
    (advance (TM2.step program))^[(encodeWords values).length + 7]
      (some ⟨some (readStart 0), ((), none), base⟩) =
      some ⟨none, ((), none),
        SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix⟩ := by
  have ht := SourceFieldArray.sequenceTrace .work fieldDestination readStart readLoop none
    program base 0 values suffix (by intro r hr; simp [fieldDestination])
    (by intro r hr; simpa only [Nat.zero_add] using atReadStart r (by omega))
    (by intro r hr; simpa only [Nat.zero_add] using atReadLoop r (by omega))
    (by simpa [hlen] using atReadDone) hinput () none
  have htime : values.sum + 2 * values.length + 1 = (encodeWords values).length + 7 := by
    rw [encodeWords_length, hlen]
  simpa only [Nat.zero_add, htime] using ht

/-- Each clause-index bit causes one genuine guard transition and exactly six
field-discard loops. The final zero guard enters the field reader. -/
theorem skipClausesTrace {n : Nat} (base : Tape → List Bool)
    (prior : List (Target.Clause n)) (indexSuffix suffix : List Bool)
    (register : Option Bool) :
    (advance (TM2.step program))^[(encodeWords (prior.flatMap clauseWords)).length + prior.length + 1]
      (some ⟨some .guard, ((), register), scanTapes base prior.length indexSuffix
        (encodeWords (prior.flatMap clauseWords) ++ suffix)⟩) =
      some ⟨some (readStart 0), ((), none), scanTapes base 0 indexSuffix suffix⟩ := by
  induction prior generalizing register with
  | nil =>
    simpa only [List.flatMap_nil, List.length_nil, encodeWords, List.nil_append,
      Nat.zero_add, Function.iterate_one, advance_some, scanTapes] using
      MachineUnaryCounter.guardStep_zero .index .guard (skipLabel 0) (readStart 0)
        program rfl (Function.update base .work suffix) indexSuffix () register
  | cons clause prior ih =>
    have hencoding : encodeWords ((clause :: prior).flatMap clauseWords) ++ suffix =
        encodeWords (clauseWords clause) ++ (encodeWords (prior.flatMap clauseWords) ++ suffix) := by
      simp only [List.flatMap_cons, encodeWords_append, List.append_assoc]
    have htime : (encodeWords ((clause :: prior).flatMap clauseWords)).length +
        (clause :: prior).length + 1 =
        ((encodeWords (prior.flatMap clauseWords)).length + prior.length + 1 +
          (encodeWords (clauseWords clause)).length) + 1 := by
      simp only [List.flatMap_cons, encodeWords_append, List.length_append, List.length_cons]
      omega
    rw [htime, Function.iterate_succ_apply]
    change (advance (TM2.step program))^[
      (encodeWords (prior.flatMap clauseWords)).length + prior.length + 1 +
        (encodeWords (clauseWords clause)).length]
      (TM2.step program ⟨some .guard, ((), register),
        MachineUnaryCounter.counterTapes .index
          (Function.update base .work (encodeWords ((clause :: prior).flatMap clauseWords) ++ suffix))
          (prior.length + 1) indexSuffix⟩) = _
    rw [MachineUnaryCounter.guardStep_succ .index .guard (skipLabel 0) (readStart 0)
      program rfl]
    rw [Function.iterate_add_apply]
    have hd := discardSixTrace
      (scanTapes base prior.length indexSuffix
        (encodeWords ((clause :: prior).flatMap clauseWords) ++ suffix))
      (clauseWords clause) (clauseWords_length clause)
      (encodeWords (prior.flatMap clauseWords) ++ suffix) (by
        rw [scanTapes_work, hencoding])
    change (advance (TM2.step program))^[
      (encodeWords (prior.flatMap clauseWords)).length + prior.length + 1]
      ((advance (TM2.step program))^[(encodeWords (clauseWords clause)).length]
        (some ⟨some (skipLabel 0), ((), none), scanTapes base prior.length indexSuffix
          (encodeWords ((clause :: prior).flatMap clauseWords) ++ suffix)⟩)) = _
    rw [hd, update_scanTapes_work]
    exact ih none

/-- Each field stack receives exactly its own unary value, in formula order. -/
theorem readSix_output_field (base : Tape → List Bool) (values : List Nat)
    (hlen : values.length = 6) (suffix : List Bool) (j : Fin 6) :
    SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix (.field j) =
      encodeWord (values[j.val]'(by omega)) ++ base (.field j) := by
  have ht := SourceFieldArray.sequenceTapes_selected .work fieldDestination base 0 values
    suffix j.val (by omega) (by intro r hr; simp [fieldDestination])
    (by
      intro r s hr hs he
      apply fieldDestination_injective_below r s (by omega) (by omega)
      simpa only [Nat.zero_add] using he)
  simpa only [Nat.zero_add, fieldDestination_eq] using ht

theorem readSix_output_work (base : Tape → List Bool) (values : List Nat)
    (_hlen : values.length = 6) (suffix : List Bool)
    (hinput : base .work = encodeWords values ++ suffix) :
    SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix .work = suffix := by
  apply SourceFieldArray.sequenceTapes_source _ _ _ _ _ _ _ hinput
  intro r hr
  simp [fieldDestination]

theorem readSix_output_frame (base : Tape → List Bool) (values : List Nat)
    (suffix : List Bool) (p : Tape) (hwork : p ≠ .work)
    (hfield : ∀ j : Fin 6, p ≠ .field j) :
    SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix p = base p := by
  apply SourceFieldArray.sequenceTapes_other _ _ _ hwork
  intro r hr
  exact hfield _

end UniqueGamesTheorem.Foundations.Hastad.SourceClauseLookup

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceContextLoad
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
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

omit [DecidableEq Extra] in
theorem stageTapes_clean (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (r : Nat) (hi : base .index = []) (hw : base .work = []) :
    stageTapes F tuple base r .index = [] ∧ stageTapes F tuple base r .work = [] := by
  induction r with
  | zero => exact ⟨hi, hw⟩
  | succ r ih =>
    simp only [stageTapes]
    split
    · exact ⟨rfl, rfl⟩
    · exact ih

omit [DecidableEq Extra] in
theorem stageTapes_field (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (r : Nat) (j : Fin u) (s : Fin 6) :
    stageTapes F tuple base r (.field j s) = if j.val < r then
      encodeWord ((clauseWords F.clauses[(tuple j).val])[s.val]'(by simp)) ++ base (.field j s)
      else base (.field j s) := by
  induction r with
  | zero => simp [stageTapes]
  | succ r ih =>
    simp only [stageTapes]
    split
    next hr =>
      by_cases hj : j = (⟨r, hr⟩ : Fin u)
      · subst j
        simp only [coordinateOutput_field, ih]
        simp
      · rw [coordinateOutput_other_field _ _ _ _ _ hj, ih]
        have hval : j.val ≠ r := by intro h; apply hj; exact Fin.ext h
        have he : j.val < r + 1 ↔ j.val < r := by omega
        simp only [he]
    next hr =>
      rw [ih]
      have hjr : j.val < r := by omega
      have hjr' : j.val < r + 1 := by omega
      simp only [hjr, hjr', ite_true, if_true]

omit [DecidableEq Extra] in
theorem output_variable (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (j : Fin u) (s : Fin 3) :
    stageTapes F tuple base u (variableField j s) =
      encodeWord (F.clauses[(tuple j).val][s.val].variableIndex.val) ++ base (variableField j s) := by
  rw [variableField, stageTapes_field, ite_eq_left j.isLt, clauseWords_variable]

omit [DecidableEq Extra] in
theorem output_polarity (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (j : Fin u) (s : Fin 3) :
    stageTapes F tuple base u (polarityField j s) =
      encodeWord (if F.clauses[(tuple j).val][s.val].positive then 1 else 0) ++
        base (polarityField j s) := by
  rw [polarityField, stageTapes_field, ite_eq_left j.isLt, clauseWords_polarity]

end UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceOccurrences
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.slotFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

section ConcreteSource

open SourceContexts
open UniqueGamesTheorem.Reduction.FiniteNoise

theorem contextEquation_satisfied (F : Target.Formula) (u D : ℕ)
    (c : ClauseContext F u) (v : VariableContext F u)
    (t : SourceTape.TestTape (I u) (J u) D) (bits : Fin (nBits F u) → Bool) :
    satisfied (contextEquation F u D c v t) bits =
      !(leftResponse F u bits v t.1 ^^ rightResponse F u bits c t.2.2 ^^
        rightResponse F u bits c (thirdQuery (pi F c v) t.1 t.2.2 (realizedNoise t.2.1))) := by
  cases ha : rightAnchor F c with
  | none =>
    simp only [contextEquation, ha, satisfied_mapEquation, EmptyContext.equation_satisfied,
      rightResponse, Bool.xor_false]
    rfl
  | some j₀ =>
    simp only [contextEquation, ha, rightResponse]
    exact conditionedOccurrence_satisfied (variableEncoding F u) (clauseEncoding F u)
      (iEncoding u) (jEncoding u) v c (validJ F c) (pi F c v) (leftAnchor u) j₀
      bits t.1 t.2.2 (realizedNoise t.2.1)

theorem rawSourceList_acceptance (F : Target.Formula) (u D : ℕ)
    (hD : 0 < D) (bits : Fin (nBits F u) → Bool) :
    ((rawSourceList F u D).countP (fun e => satisfied e bits) : ℝ) /
        (rawSourceList F u D).length =
      𝔼 c : ClauseContext F u, 𝔼 s : SlotContext u,
        testAcceptance ((D : ℝ)⁻¹) (pi F c (sampledVariables F c s))
          (leftResponse F u bits (sampledVariables F c s)) (rightResponse F u bits c) := by
  rw [rawSourceList, occurrenceList_acceptance, SourceTape.expect_prod]
  rw [SourceTape.expect_prod]
  apply Finset.expect_congr rfl
  intro c _
  apply Finset.expect_congr rfl
  intro s _
  rw [← SourceTape.tapeAcceptance_eq_testAcceptance hD]
  unfold SourceTape.tapeAcceptance
  apply Finset.expect_congr rfl
  intro t _
  rw [sourceEquation, contextEquation_satisfied]
  cases h : leftResponse F u bits (sampledVariables F c s) t.1 ^^
    rightResponse F u bits c t.2.2 ^^
      rightResponse F u bits c
        (thirdQuery (pi F c (sampledVariables F c s)) t.1 t.2.2 (realizedNoise t.2.1)) <;> rfl

theorem emptyFormulaEquation_satisfied (F : Target.Formula) (u : ℕ)
    (bits : Fin (nBits F u) → Bool) :
    satisfied (emptyFormulaEquation F u) bits = !(bits (dummyIndex F u)) := by
  cases h : bits (dummyIndex F u) <;> simp [emptyFormulaEquation, satisfied, h]

end ConcreteSource

end UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceHonestLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.slotFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceHonest

open UniqueGamesTheorem.Reduction.CloneGap
open UniqueGamesTheorem.Reduction.FiniteNoise
open scoped BigOperators

open SourceContexts
open SourceOccurrences

/-- Satisfiability supplies one consistent valid right coordinate in every
clause tuple, including tuples with repeated clauses or variable names. -/
def honestValidJ (F : Target.Formula) {u : ℕ} (c : ClauseContext F u)
    (assignment : Fin F.variables → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    {j : J u // validJ F c j = true} :=
  ⟨honestJ F c assignment, honestJ_valid F c assignment hs⟩

theorem leftResponse_honest (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.variables → Bool) (v : VariableContext F u) :
    leftResponse F u (honestBits F u assignment) v =
      fun f => f (honestI F v assignment) := by
  funext f
  simp only [leftResponse, honestBits_code, honestGlobal, taggedAssignment,
    foldedAnswer_dictator]

theorem rightResponse_honest (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.variables → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true)
    (c : ClauseContext F u) :
    rightResponse F u (honestBits F u assignment) c =
      fun g => g (honestJ F c assignment) := by
  funext g
  cases ha : rightAnchor F c with
  | none =>
    have hf := (rightAnchor_none_iff F c).mp ha (honestJ F c assignment)
    rw [honestJ_valid F c assignment hs] at hf
    cases hf
  | some j₀ =>
    simp only [rightResponse, ha, honestBits_code, honestGlobal, taggedAssignment]
    have ht : (fun h : HalfCube j₀ =>
        extendRestricted (validJ F c) h.val (honestJ F c assignment)) =
        fun h => h.val (honestValidJ F c assignment hs) := by
      funext h
      exact extendRestricted_valid (validJ F c) h.val (honestValidJ F c assignment hs)
    rw [ht]
    exact conditionedFoldedAnswer_dictator (validJ F c) j₀
      (honestValidJ F c assignment hs) g

/-- Every actual occurrence is counted, even when its visible context,
equation, or one of its three addresses repeats. -/
theorem rawSourceList_honest_acceptance (F : Target.Formula) (u D : ℕ)
    (hD : 0 < D) (hF : F.clauses ≠ [])
    (assignment : Fin F.variables → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    ((rawSourceList F u D).countP
      (fun e => satisfied e (honestBits F u assignment)) : ℝ) /
        (rawSourceList F u D).length = 1 - (D : ℝ)⁻¹ := by
  have hc : 0 < F.clauses.length := List.length_pos_iff.mpr hF
  let : Nonempty (Fin F.clauses.length) := ⟨⟨0, hc⟩⟩
  rw [rawSourceList_acceptance F u D hD]
  have heq (c : ClauseContext F u) (s : SlotContext u) :
      testAcceptance ((D : ℝ)⁻¹) (pi F c (sampledVariables F c s))
        (leftResponse F u (honestBits F u assignment) (sampledVariables F c s))
        (rightResponse F u (honestBits F u assignment) c) = 1 - (D : ℝ)⁻¹ := by
    rw [leftResponse_honest, rightResponse_honest F u assignment hs]
    exact testAcceptance_dictator _ _ _ _ (pi_honest_sampled F c s assignment)
  simp_rw [heq]
  simp only [Fintype.expect_const]

theorem sourceList_honest_acceptance_nonempty (F : Target.Formula) (u D : ℕ)
    (hD : 0 < D) (hF : F.clauses ≠ [])
    (assignment : Fin F.variables → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    ((sourceList F u D).countP
      (fun e => satisfied e (honestBits F u assignment)) : ℝ) /
        (sourceList F u D).length = 1 - (D : ℝ)⁻¹ := by
  rw [sourceList_nonempty F u D hF]
  exact rawSourceList_honest_acceptance F u D hD hF assignment hs

theorem sourceList_honest_acceptance (F : Target.Formula) (u D : ℕ)
    (hD : 0 < D) (assignment : Fin F.variables → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    1 - (D : ℝ)⁻¹ ≤ ((sourceList F u D).countP
      (fun e => satisfied e (honestBits F u assignment)) : ℝ) /
        (sourceList F u D).length := by
  by_cases hF : F.clauses = []
  · rw [sourceList_empty F u D hF]
    simp only [List.countP_cons, List.countP_nil, emptyFormulaEquation_satisfied,
      honestBits_dummy, Bool.not_false, ↓reduceIte,
      Nat.zero_add, Nat.cast_one, List.length_cons, List.length_nil, div_one]
    exact sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg D))
  · exact (sourceList_honest_acceptance_nonempty F u D hD hF assignment hs).ge

/-- Rational acceptance form used by the finite reduction interface. -/
theorem sourceList_honest_acceptance_rat (F : Target.Formula) (u D : ℕ)
    (hD : 0 < D) (assignment : Fin F.variables → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    1 - (D : ℚ)⁻¹ ≤ ((sourceList F u D).countP
      (fun e => satisfied e (honestBits F u assignment)) : ℚ) /
        (sourceList F u D).length := by
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_sub, Rat.cast_one, Rat.cast_inv, Rat.cast_natCast, Rat.cast_div] using
    sourceList_honest_acceptance F u D hD assignment hs

end UniqueGamesTheorem.Foundations.Hastad.SourceHonest

namespace UniqueGamesTheorem.Foundations.Hastad.SourceLocalEquation

open Target SourceContexts SourceOccurrences SourceLocalSignature
open UniqueGamesTheorem.Reduction.CloneGap
open UniqueGamesTheorem.Reduction.FiniteNoise

def localInputEncoding (u D : ℕ) : Encoding (LocalInput u D) :=
  (signatureEncoding u).prod (testTapeEncoding u D)

end UniqueGamesTheorem.Foundations.Hastad.SourceLocalEquation

/-! The actual global addresses use three input-dependent base registers.
Every local query contributes only a fixed finite selector and fixed offset,
so a finite control table can select a base and emit its unary offset. -/

/-! Actual fixed-coefficient affine address construction. A finite literal phase
loads the coefficient, the checked width-two Horner machine reads coefficient
and preserved offset with the rank as its radix, then the literal field is
actually consumed. All operands and work stacks are restored. -/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceDescriptorEmissionLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.slotFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission

open Turing
open Target SourceContexts SourceOccurrences SourceLocalSignature SourceLocalEquation
open UniqueGamesTheorem.Reduction.CloneGap
open UniqueGamesTheorem.Foundations.Complexity

variable {K Λ : Type} [DecidableEq K]

/-- Executable state equality is obtained from the explicit radix code. -/
instance localInputDecidableEq (u D : ℕ) : DecidableEq (LocalInput u D) :=
  fun x y =>
    if h : (localInputEncoding u D).code x = (localInputEncoding u D).code y then
      isTrue ((localInputEncoding u D).code.injective h)
    else isFalse (fun hxy => h (congrArg (localInputEncoding u D).code hxy))

end UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission

/-! Emit one fixed descriptor equation from three preserved unary base registers.
The output order is first address, second address, third address, RHS. The actual
stack program emits those fields in reverse order. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceEquationEmit

open Turing Complexity
open SourceAddressDescriptors
open UniqueGamesTheorem.Reduction.CloneGap
open UniqueGamesTheorem.Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

theorem equationTrace (sources : Fin 3 → K) (destination scratch : K)
    (sourceDestination : ∀ side, sources side ≠ destination)
    (sourceScratch : ∀ side, sources side ≠ scratch)
    (destinationScratch : destination ≠ scratch) (e : Equation Descriptor)
    (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement sources destination scratch e labels exit label)
    (base : K → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (sources side) = encodeWord (values side))
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps values e]
      (some ⟨some (labels .seed), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), prefixTapes destination base (words values e)⟩ := by
  have hw (written : List Nat) (side : Fin 3) :
      prefixTapes destination base written (sources side) = encodeWord (values side) := by
    rw [prefixTapes_other _ _ _ _ (sourceDestination side), sourceWords side]
  have hs (written : List Nat) : prefixTapes destination base written scratch = [] := by
    rw [prefixTapes_other _ _ _ _ (Ne.symm destinationScratch), scratchEmpty]
  have hseed : (MachineComposition.advance (TM2.step p))^[1]
      (some ⟨some (labels .seed), (ambient, register), base⟩) =
      some ⟨some (labels .thirdDrain), (ambient, register),
        prefixTapes destination base [rhsBit e]⟩ := by
    change some (TM2.stepAux (p (labels .seed)) (ambient, register) base) = _
    rw [atLabels .seed]
    simp only [statement, stepAux_pushWord, List.reverse_reverse, TM2.stepAux,
      prefixTapes, encodeWords, List.append_nil]
  have hthird : (MachineComposition.advance (TM2.step p))^[2 * values e.third.1 + 5]
      (some ⟨some (labels .thirdDrain), (ambient, register),
        prefixTapes destination base [rhsBit e]⟩) =
      some ⟨some (labels .secondDrain), (ambient, none),
        prefixTapes destination base [realize values e.third, rhsBit e]⟩ := by
    have h := MachineRegisterEmit.registerEmitTrace (sources e.third.1) destination scratch
      (sourceDestination _) (sourceScratch _) destinationScratch e.third.2
      (labels .thirdDrain) (labels .thirdFork) (labels .thirdEmit) (some (labels .secondDrain))
      p (atLabels .thirdDrain) (atLabels .thirdFork) (atLabels .thirdEmit)
      (prefixTapes destination base [rhsBit e]) (values e.third.1)
      (hw _ _) (hs _) ambient register
    simpa only [prefixTapes, Function.update_self, Function.update_idem, realize,
      encodeWords, List.append_nil, List.append_assoc] using h
  have hsecond : (MachineComposition.advance (TM2.step p))^[2 * values e.second.1 + 5]
      (some ⟨some (labels .secondDrain), (ambient, none),
        prefixTapes destination base [realize values e.third, rhsBit e]⟩) =
      some ⟨some (labels .firstDrain), (ambient, none),
        prefixTapes destination base [realize values e.second, realize values e.third, rhsBit e]⟩ := by
    have h := MachineRegisterEmit.registerEmitTrace (sources e.second.1) destination scratch
      (sourceDestination _) (sourceScratch _) destinationScratch e.second.2
      (labels .secondDrain) (labels .secondFork) (labels .secondEmit) (some (labels .firstDrain))
      p (atLabels .secondDrain) (atLabels .secondFork) (atLabels .secondEmit)
      (prefixTapes destination base [realize values e.third, rhsBit e]) (values e.second.1)
      (hw _ _) (hs _) ambient none
    simpa only [prefixTapes, Function.update_self, Function.update_idem, realize,
      encodeWords, List.append_nil, List.append_assoc] using h
  have hfirst : (MachineComposition.advance (TM2.step p))^[2 * values e.first.1 + 5]
      (some ⟨some (labels .firstDrain), (ambient, none),
        prefixTapes destination base [realize values e.second, realize values e.third, rhsBit e]⟩) =
      some ⟨exit, (ambient, none), prefixTapes destination base (words values e)⟩ := by
    have h := MachineRegisterEmit.registerEmitTrace (sources e.first.1) destination scratch
      (sourceDestination _) (sourceScratch _) destinationScratch e.first.2
      (labels .firstDrain) (labels .firstFork) (labels .firstEmit) exit
      p (atLabels .firstDrain) (atLabels .firstFork) (atLabels .firstEmit)
      (prefixTapes destination base [realize values e.second, realize values e.third, rhsBit e])
      (values e.first.1) (hw _ _) (hs _) ambient none
    simpa only [prefixTapes, Function.update_self, Function.update_idem, words, rhsBit, realize,
      encodeWords, List.append_nil, List.append_assoc] using h
  rw [show steps values e = (2 * values e.first.1 + 5) +
      ((2 * values e.second.1 + 5) + ((2 * values e.third.1 + 5) + 1)) by
        unfold steps; omega]
  rw [Function.iterate_add_apply _ (2 * values e.first.1 + 5),
    Function.iterate_add_apply _ (2 * values e.second.1 + 5),
    Function.iterate_add_apply _ (2 * values e.third.1 + 5), hseed, hthird, hsecond, hfirst]

end UniqueGamesTheorem.Foundations.Hastad.SourceEquationEmit

namespace UniqueGamesTheorem.Foundations.Hastad.SourceProfileBridge

open Target SourceContexts SourceOccurrences SourceLocalSignature
open Complexity

def reindexProfile (u : ℕ) (profile : MachineFieldProfile.Profile (positionEncoding u).size) :
    NameProfile u :=
  fun p q => profile ((positionEncoding u).code p) ((positionEncoding u).code q)

end UniqueGamesTheorem.Foundations.Hastad.SourceProfileBridge

namespace UniqueGamesTheorem.Foundations.Hastad.SourceRankPhase

open Turing Complexity
open scoped BigOperators
open Target SourceContexts SourceOccurrences SourceAddressArithmetic

variable {K Λ σ : Type} {width : Nat}

variable [DecidableEq K]

def variableRankInTime (F : Formula) (u : Nat) (v : VariableContext F u)
    (slots : MachineHorner.Layout u ↪ K) (labels : MachineHorner.Label u → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (operandRadix : base (slots (.inl 0)) = encodeWord F.variables)
    (operandDigits : ∀ i, base (slots (.inr i)) = encodeWord (v i).val)
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .start), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none),
        MachineHorner.resultTapes slots base (((variableEncoding F u).code v).val)⟩)
      ((MachineHorner.timePolynomial u).eval F.variables) := by
  have h := rankInPolynomialTime slots labels exit p atLabels base F.variables (fun i => (v i).val)
    operandRadix operandDigits clean ambient register F.variables (Nat.le_refl _) (fun i => (v i).isLt.le)
  simpa only [rank, ← variable_rank F u v] using h

def clauseRankInTime (F : Formula) (u : Nat) (c : ClauseContext F u)
    (slots : MachineHorner.Layout u ↪ K) (labels : MachineHorner.Label u → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (operandRadix : base (slots (.inl 0)) = encodeWord F.clauses.length)
    (operandDigits : ∀ i, base (slots (.inr i)) = encodeWord (c i).val)
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .start), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none),
        MachineHorner.resultTapes slots base (((clauseEncoding F u).code c).val)⟩)
      ((MachineHorner.timePolynomial u).eval F.clauses.length) := by
  have h := rankInPolynomialTime slots labels exit p atLabels base F.clauses.length (fun i => (c i).val)
    operandRadix operandDigits clean ambient register F.clauses.length (Nat.le_refl _) (fun i => (c i).isLt.le)
  simpa only [rank, ← clause_rank F u c] using h

variable {u : Nat} {Extra : Type}

theorem selectedDigits_loaded (F : Formula) (c : ClauseContext F u) (selected : SlotContext u)
    (controls : Fin 6 ↪ Extra) (base : SourceContextLoad.Tape u Extra → List Bool)
    (empty : ∀ i, base (SourceContextLoad.variableField i (slotEncoding.code (selected i))) = [])
    (i : Fin u) :
    SourceContextLoad.stageTapes F c base u (variableSlots controls selected (.inr i)) =
      encodeWord (sampledVariables F c selected i).val := by
  rw [variableSlots_digit]
  erw [SourceContextLoad.output_variable, empty i, List.append_nil]
  congr 1
  cases hs : selected i <;> simp [sampledVariables, PCP.nameAt, PCP.clauseAt, slotEncoding, hs] <;> rfl

end UniqueGamesTheorem.Foundations.Hastad.SourceRankPhase

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceLoopInitLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceLoopInit

open Turing UniqueGamesTheorem.Foundations.Complexity
open MachineComposition SourceMachine

variable {u : Nat} {Extra : Type}

variable [DecidableEq Extra]

def readOutput (F : Target.Formula) (base : Tape u Extra → List Bool) : Tape u Extra → List Bool :=
  SourceFieldArray.sequenceTapes .work headerDestination (copiedInput base) 0
    [F.variables, F.clauses.length] (encodeWords (F.clauses.flatMap clauseWords))

theorem clear_readOutput (F : Target.Formula) (base : Tape u Extra → List Bool) :
    Function.update (readOutput F base) .work [] = headerOutput F base := by
  funext p
  cases p <;> simp [readOutput, headerOutput, SourceFieldArray.sequenceTapes,
    afterField, fieldTapes, copiedInput, headerDestination, variableHeader, clauseHeader]
  rename_i e
  cases e with
  | inl h => cases h <;> simp
  | inr e => simp

theorem readOutput_work (F : Target.Formula) (base : Tape u Extra → List Bool) :
    readOutput F base .work = encodeWords (F.clauses.flatMap clauseWords) := by
  simp [readOutput, SourceFieldArray.sequenceTapes, afterField, fieldTapes,
    headerDestination, variableHeader, clauseHeader, encodeWords]

def headerInTime (F : Target.Formula) (base : Tape u Extra → List Bool)
    (hformula : base .formula = formulaBits F) (hwork : base .work = [])
    (hscratch : base .scratch = []) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .inputCopyOut, ((), register), base⟩
      (some ⟨some (labelAt 0), ((), none), headerOutput F base⟩)
      (3 * (formulaBits F).length + 6) := by
  have copying := MachineCopy.copyInTime .formula .work .scratch
    (by simp) (by simp) (by simp) false .inputCopyOut .inputCopyBack (some (readStart 0))
    program rfl rfl base hscratch () register
  have hc : Function.update base .work (base .formula ++ base .work) = copiedInput base := by
    simp [copiedInput, hwork]
  rw [hc] at copying
  have reading := SourceFieldArray.sequenceInTime .work headerDestination readStart readLoop
    (some .clearWork) program (copiedInput base) 0 [F.variables, F.clauses.length]
    (encodeWords (F.clauses.flatMap clauseWords))
    (by intro r hr; simp [headerDestination, variableHeader, clauseHeader]; split <;> simp)
    (by intro r hr; simpa only [Nat.zero_add] using atReadStart (u := u) (Extra := Extra) r (by simpa using hr))
    (by intro r hr; simpa only [Nat.zero_add] using atReadLoop (u := u) (Extra := Extra) r (by simpa using hr))
    (by simpa using (atReadDone (u := u) (Extra := Extra)))
    (by simp [copiedInput, hformula, formulaBits, formulaWords, encodeWords, List.append_assoc]) () none
  have draining := MachineDrain.drainInTime .work .clearWork (some (labelAt 0))
    program rfl (readOutput F base) () none
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ copying reading) draining
  refine { steps := joined.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · simpa only [clear_readOutput] using joined.evals_in_steps
  · apply Nat.le_trans joined.steps_le_m
    rw [readOutput_work, hformula]
    have he : (formulaBits F).length = F.variables + F.clauses.length + 2 +
        (encodeWords (F.clauses.flatMap clauseWords)).length := by
      simp [formulaBits, formulaWords, encodeWords, Nat.add_assoc]
      omega
    simp only [List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
    omega

def initializeInTime (F : Target.Formula) (hm : 0 < F.clauses.length)
    (base : Tape u Extra → List Bool) (hformula : base .formula = formulaBits F)
    (hwork : base .work = []) (hscratch : base .scratch = []) (hcopy : base .copyScratch = [])
    (hclauseHeader : base clauseHeader = [])
    (hcurrent : ∀ j, base (.current j) = []) (hremaining : ∀ j, base (.remaining j) = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .inputCopyOut, ((), none), base⟩
      (some ⟨none, ((), none), outputTapes F base⟩)
      ((2 * u + 3) * (formulaBits F).length + 6 * u + 7) := by
  have firstRun := headerInTime F base hformula hwork hscratch none
  have hcount : headerOutput F base clauseHeader = encodeWord F.clauses.length := by
    simp [headerOutput, hclauseHeader]
  have secondRun := digitsInTime F.clauses.length hm (headerOutput F base) hcount
    (by intro j; rw [headerOutput_frame _ _ _ (by simp) (by simp [variableHeader])
      (by simp [clauseHeader])]; exact hcurrent j)
    (by intro j; rw [headerOutput_frame _ _ _ (by simp) (by simp [variableHeader])
      (by simp [clauseHeader])]; exact hremaining j)
    (by rw [headerOutput_frame _ _ _ (by simp) (by simp [variableHeader])
      (by simp [clauseHeader])]; exact hcopy)
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ firstRun secondRun
  refine { steps := joined.steps, evals_in_steps := joined.evals_in_steps, steps_le_m := ?_ }
  apply Nat.le_trans joined.steps_le_m
  have hL := SourceContextLoad.clauses_length_le_input F
  have hb : u * (2 * F.clauses.length + 6) ≤ u * (2 * (formulaBits F).length + 6) :=
    Nat.mul_le_mul_left u (by omega)
  have he : (2 * u + 3) * (formulaBits F).length + 6 * u + 7 =
      u * (2 * (formulaBits F).length + 6) + 3 * (formulaBits F).length + 7 := by
    simp [Nat.add_mul, Nat.mul_add, Nat.mul_comm, Nat.mul_assoc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [he]
  omega

end UniqueGamesTheorem.Foundations.Hastad.SourceLoopInit

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceHeaderCounts
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceHeaderCounts

open Turing Complexity
open MachineComposition

noncomputable section

theorem bitValue_eq_nBits (F : Target.Formula) (u : Nat) :
    bitValue u F.variables F.clauses.length = SourceOccurrences.nBits F u := by
  rw [SourceOccurrences.nBits_eq]
  simp [bitValue, dummyValue, leftValue, rightValue, Nat.mul_comm, Nat.add_assoc]

theorem occurrenceValue_eq_length (F : Target.Formula) (u D : Nat)
    (hm : 0 < F.clauses.length) :
    occurrenceValue u D F.clauses.length = (SourceOccurrences.sourceList F u D).length := by
  have hne : F.clauses ≠ [] := by intro h; simp [h] at hm
  have hfalse : ¬ F.clauses.isEmpty = true := by simpa using hne
  simp only [SourceOccurrences.sourceList, ite_eq_right hfalse]
  rw [SourceOccurrences.rawSourceList_length]
  unfold occurrenceValue
  rw [SourceBounds.testTapeEncoding_size]
  ac_rfl

variable {u D : Nat} {K Λ σ : Type}

structure Clean (slots : Layout u D ↪ K) (base : K → List Bool) : Prop where
  left : base (control slots .leftBlockSize) = []
  right : base (control slots .rightTemporary) = []
  dummy : base (control slots .dummyIndex) = []
  bits : base (control slots .bitCount) = []
  occurrences : base (control slots .occurrenceCount) = []
  accA : base (control slots .accA) = []
  accB : base (control slots .accB) = []
  counter : base (control slots .counter) = []
  scratch : base (control slots .scratch) = []
  coefficients : ∀ i : Coefficients u D, base (slots (.inr i)) = []

inductive Label (u D : Nat)
  | evaluate (kind : Kind) (localLabel : Eval.Label (polynomial u D kind))
  | copyLeftOut | copyLeftBack | addRight | clearTemporary
  | copyDummyOut | copyDummyBack | incrementBits
  deriving DecidableEq, Fintype

def evalStart (kind : Kind) : Label u D := .evaluate kind (Eval.start (polynomial u D kind))

def afterEval : Kind → Label u D
  | .left => evalStart .right | .right => evalStart .occurrences | .occurrences => .copyLeftOut

variable [DecidableEq K]

def statement (slots : Layout u D ↪ K) (labels : Label u D → Λ) (exit : Option Λ) :
    Label u D → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .evaluate kind l => Eval.statement (polynomial u D kind) (evalSlots slots kind)
      (fun l => labels (.evaluate kind l)) (some (labels (afterEval kind))) l
  | .copyLeftOut => Reduction.MachineTransfer.loopAt (control slots .leftBlockSize)
      (control slots .scratch) id false (labels .copyLeftOut) (some (labels .copyLeftBack))
  | .copyLeftBack => MachineCopy.forkLoop (control slots .scratch)
      (control slots .leftBlockSize) (control slots .dummyIndex) false
      (labels .copyLeftBack) (some (labels .addRight))
  | .addRight => MachineUnaryAddAt.loop (control slots .rightTemporary)
      (control slots .dummyIndex) (labels .addRight) (some (labels .clearTemporary))
  | .clearTemporary => .pop (control slots .rightTemporary) (fun state _ => state)
      (.goto fun _ => labels .copyDummyOut)
  | .copyDummyOut => Reduction.MachineTransfer.loopAt (control slots .dummyIndex)
      (control slots .scratch) id false (labels .copyDummyOut) (some (labels .copyDummyBack))
  | .copyDummyBack => MachineCopy.forkLoop (control slots .scratch)
      (control slots .dummyIndex) (control slots .bitCount) false
      (labels .copyDummyBack) (some (labels .incrementBits))
  | .incrementBits => .push (control slots .bitCount) (fun _ => true)
      (Reduction.MachineTransfer.exitAt (control slots .bitCount) exit)

def steps (u D n m : Nat) : Nat :=
  Eval.steps (polynomial u D .left) n + Eval.steps (polynomial u D .right) m +
    Eval.steps (polynomial u D .occurrences) m +
    2 * leftValue u n + rightValue u m + 2 * dummyValue u n m + 11

structure WorkClean (slots : Layout u D ↪ K) (base : K → List Bool) : Prop where
  accA : base (control slots .accA) = []
  accB : base (control slots .accB) = []
  counter : base (control slots .counter) = []
  scratch : base (control slots .scratch) = []
  coefficients : ∀ i : Coefficients u D, base (slots (.inr i)) = []

omit [DecidableEq K] in
theorem Clean.work {slots : Layout u D ↪ K} {base : K → List Bool} (clean : Clean slots base) :
    WorkClean slots base :=
  ⟨clean.accA, clean.accB, clean.counter, clean.scratch, clean.coefficients⟩

theorem WorkClean.update_output {slots : Layout u D ↪ K} {base : K → List Bool}
    (clean : WorkClean slots base) (kind : Kind) (value : List Bool) :
    WorkClean slots (Function.update base (control slots (outputControl kind)) value) := by
  cases kind <;> constructor
  all_goals try { simpa [outputControl] using clean.accA }
  all_goals try { simpa [outputControl] using clean.accB }
  all_goals try { simpa [outputControl] using clean.counter }
  all_goals try { simpa [outputControl] using clean.scratch }
  all_goals intro i; simpa [control, slots.injective.eq_iff] using clean.coefficients i

theorem evalPhaseTrace (slots : Layout u D ↪ K) (labels : Label u D → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (kind : Kind) (base : K → List Bool) (n : Nat)
    (hinput : base (control slots (inputControl kind)) = encodeWord n)
    (hdest : base (control slots (outputControl kind)) = [])
    (clean : WorkClean slots base) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[Eval.steps (polynomial u D kind) n]
      (some ⟨some (labels (evalStart kind)), ((ambient, ()), register), base⟩) =
      some ⟨some (labels (afterEval kind)), ((ambient, ()), none),
        Function.update base (control slots (outputControl kind))
          (encodeWord ((polynomial u D kind).eval n))⟩ := by
  have h := Eval.trace (polynomial u D kind) (evalSlots slots kind)
    (fun l => labels (.evaluate kind l)) (some (labels (afterEval kind))) program
    (fun l => atLabels (.evaluate kind l)) base n (by simpa using hinput)
    (fun i => by simpa using clean.coefficients (coefficientBlock u D kind i))
    ⟨by simpa using clean.accA, by simpa using clean.accB,
      by simpa using clean.counter, by simpa using clean.scratch⟩ ambient register
  simpa only [evalStart, MachineHorner.resultTapes, evalSlots_destination,
    hdest, List.append_nil] using h

/-- The actual header program preserves its two operands and every caller frame.
The four retained outputs are left-block size, dummy index, bit count, and
occurrence count. The temporary and all coefficient/work tapes are restored. -/
theorem trace (slots : Layout u D ↪ K) (labels : Label u D → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (n m : Nat)
    (hn : base (control slots .variableCount) = encodeWord n)
    (hm : base (control slots .clauseCount) = encodeWord m)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps u D n m]
      (some ⟨some (labels (evalStart .left)), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base n m⟩ := by
  let t1 := Function.update base (control slots .leftBlockSize) (encodeWord (leftValue u n))
  let t2 := Function.update t1 (control slots .rightTemporary) (encodeWord (rightValue u m))
  let t3 := Function.update t2 (control slots .occurrenceCount) (encodeWord (occurrenceValue u D m))
  let t4 := Function.update t3 (control slots .dummyIndex) (encodeWord (leftValue u n))
  let t5 := Function.update (Function.update t4 (control slots .rightTemporary) [false])
    (control slots .dummyIndex) (encodeWord (dummyValue u n m))
  let t6 := Function.update t5 (control slots .rightTemporary) []
  let t7 := Function.update t6 (control slots .bitCount) (encodeWord (dummyValue u n m))
  have h1 := evalPhaseTrace slots labels exit program atLabels .left base n hn clean.left
    clean.work ambient register
  change (advance (TM2.step program))^[Eval.steps (polynomial u D .left) n]
      (some ⟨some (labels (evalStart .left)), ((ambient, ()), register), base⟩) =
      some ⟨some (labels (evalStart .right)), ((ambient, ()), none), _⟩ at h1
  simp only [polynomial_left_eval] at h1
  have cw1 : WorkClean slots t1 := clean.work.update_output .left _
  have h2 := evalPhaseTrace slots labels exit program atLabels .right t1 m
    (by simpa [t1, inputControl] using hm)
    (by simpa [t1, outputControl] using clean.right) cw1 ambient none
  change (advance (TM2.step program))^[Eval.steps (polynomial u D .right) m]
      (some ⟨some (labels (evalStart .right)), ((ambient, ()), none), t1⟩) =
      some ⟨some (labels (evalStart .occurrences)), ((ambient, ()), none), _⟩ at h2
  simp only [polynomial_right_eval] at h2
  have cw2 : WorkClean slots t2 := cw1.update_output .right _
  have h3 := evalPhaseTrace slots labels exit program atLabels .occurrences t2 m
    (by simpa [t2, t1, inputControl] using hm)
    (by simpa [t2, t1, outputControl] using clean.occurrences) cw2 ambient none
  change (advance (TM2.step program))^[Eval.steps (polynomial u D .occurrences) m]
      (some ⟨some (labels (evalStart .occurrences)), ((ambient, ()), none), t2⟩) =
      some ⟨some (labels .copyLeftOut), ((ambient, ()), none), _⟩ at h3
  simp only [polynomial_occurrences_eval] at h3
  have cw3 : WorkClean slots t3 := cw2.update_output .occurrences _
  have copyingLeft := MachineCopy.copyTrace (control slots .leftBlockSize)
    (control slots .dummyIndex) (control slots .scratch)
    (by simp) (by simp) (by simp) false (labels .copyLeftOut) (labels .copyLeftBack)
    (some (labels .addRight)) program (atLabels .copyLeftOut) (atLabels .copyLeftBack)
    t3 cw3.scratch (ambient, ()) none
  have hleft : t3 (control slots .leftBlockSize) = encodeWord (leftValue u n) := by
    simp [t3, t2, t1]
  have hdummy : t3 (control slots .dummyIndex) = [] := by
    simpa [t3, t2, t1] using clean.dummy
  rw [hleft, hdummy, List.append_nil, encodeWord_length] at copyingLeft
  have adding := MachineUnaryAddAt.addFromTapes (control slots .rightTemporary)
    (control slots .dummyIndex) (by simp) (labels .addRight) (some (labels .clearTemporary))
    program (atLabels .addRight) t4 (rightValue u m) (leftValue u n) [] []
    (by simp [t4, t3, t2]) (by simp [t4]) (ambient, ()) none
  have ha : MachineUnaryAddAt.unaryTapes (control slots .rightTemporary)
      (control slots .dummyIndex) t4 0 (rightValue u m + leftValue u n) [] [] = t5 := by
    simp [MachineUnaryAddAt.unaryTapes, Reduction.MachineTransfer.tapesAt, t5,
      encodeWord, dummyValue, Nat.add_comm]
  rw [ha] at adding
  have clearing : (advance (TM2.step program))^[1]
      (some ⟨some (labels .clearTemporary), ((ambient, ()), none), t5⟩) =
      some ⟨some (labels .copyDummyOut), ((ambient, ()), none), t6⟩ := by
    change some (TM2.stepAux (program (labels .clearTemporary)) _ _) = _
    rw [atLabels]
    simp [statement, TM2.stepAux, t6, t5]
  have copyingDummy := MachineCopy.copyTrace (control slots .dummyIndex)
    (control slots .bitCount) (control slots .scratch)
    (by simp) (by simp) (by simp) false (labels .copyDummyOut) (labels .copyDummyBack)
    (some (labels .incrementBits)) program (atLabels .copyDummyOut) (atLabels .copyDummyBack)
    t6 (by simpa [t6, t5, t4] using cw3.scratch) (ambient, ()) none
  have hdi : t6 (control slots .dummyIndex) = encodeWord (dummyValue u n m) := by
    simp [t6, t5]
  have hbi : t6 (control slots .bitCount) = [] := by
    simpa [t6, t5, t4, t3, t2, t1] using clean.bits
  rw [hdi, hbi, List.append_nil, encodeWord_length] at copyingDummy
  have increment : (advance (TM2.step program))^[1]
      (some ⟨some (labels .incrementBits), ((ambient, ()), none), t7⟩) =
      some ⟨exit, ((ambient, ()), none),
        Function.update t7 (control slots .bitCount) (encodeWord (bitValue u n m))⟩ := by
    change some (TM2.stepAux (program (labels .incrementBits)) _ _) = _
    rw [atLabels]
    cases exit <;> simp [statement, TM2.stepAux, Reduction.MachineTransfer.exitAt,
      t7, bitValue, encodeWord, List.replicate_succ]
  have total := trace_trans _ (trace_trans _ (trace_trans _ (trace_trans _
    (trace_trans _ (trace_trans _ (trace_trans _ h1 h2) h3) copyingLeft) adding) clearing)
      copyingDummy) increment
  have htime :
      Eval.steps (polynomial u D .left) n + Eval.steps (polynomial u D .right) m +
        Eval.steps (polynomial u D .occurrences) m + 2 * (leftValue u n + 1 + 1) +
        (rightValue u m + 1) + 1 + 2 * (dummyValue u n m + 1 + 1) + 1 =
      steps u D n m := by unfold steps; omega
  rw [htime] at total
  have frame : Function.update t7 (control slots .bitCount) (encodeWord (bitValue u n m)) =
      resultTapes slots base n m := by
    funext k
    by_cases hr : k = control slots .rightTemporary
    · subst k
      simp [t7, t6, t5, t4, t3, t2, t1, resultTapes, clean.right]
    · simp [t7, t6, t5, t4, t3, t2, t1, resultTapes, Function.update_apply, hr]
      split_ifs <;> rfl
  rw [frame] at total
  exact total

def timePolynomial (u D : Nat) : Polynomial Nat :=
  CookLevin.PolynomialMachine.timePolynomial (polynomial u D .left) +
    CookLevin.PolynomialMachine.timePolynomial (polynomial u D .right) +
    CookLevin.PolynomialMachine.timePolynomial (polynomial u D .occurrences) +
    Polynomial.C 2 * polynomial u D .left + polynomial u D .right +
    Polynomial.C 2 * (polynomial u D .left + polynomial u D .right) + Polynomial.C 11

theorem steps_le_timePolynomial (u D n m L : Nat) (hn : n ≤ L) (hm : m ≤ L) :
    steps u D n m ≤ (timePolynomial u D).eval L := by
  have hEval (p : Polynomial Nat) (a : Nat) (ha : a ≤ L) :
      Eval.steps p a ≤ (CookLevin.PolynomialMachine.timePolynomial p).eval L := by
    apply Nat.le_trans (m := (CookLevin.PolynomialMachine.timePolynomial p).eval a)
    · rw [CookLevin.PolynomialMachine.timePolynomial_eval]
      unfold Eval.steps
      omega
    · exact natPolynomial_eval_mono _ ha
  have h1 := hEval (polynomial u D .left) n hn
  have h2 := hEval (polynomial u D .right) m hm
  have h3 := hEval (polynomial u D .occurrences) m hm
  have hl : leftValue u n ≤ leftValue u L :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn u)
  have hr : rightValue u m ≤ rightValue u L :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm u)
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    polynomial_left_eval, polynomial_right_eval]
  unfold steps dummyValue
  omega

def inTime (slots : Layout u D ↪ K) (labels : Label u D → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (n m : Nat)
    (hn : base (control slots .variableCount) = encodeWord n)
    (hm : base (control slots .clauseCount) = encodeWord m)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (evalStart .left)), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes slots base n m⟩)
      (steps u D n m) where
  steps := steps u D n m
  evals_in_steps := trace slots labels exit program atLabels base n m hn hm clean ambient register
  steps_le_m := Nat.le_refl _

@[simp] theorem result_variableCount (slots : Layout u D ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (control slots .variableCount) = base (control slots .variableCount) := by
  simp [resultTapes]
@[simp] theorem result_clauseCount (slots : Layout u D ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (control slots .clauseCount) = base (control slots .clauseCount) := by
  simp [resultTapes]

end

end UniqueGamesTheorem.Foundations.Hastad.SourceHeaderCounts

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceSignaturePrepareLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.slotFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceSignaturePrepare

open Turing
open Target PCP SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge
open UniqueGamesTheorem.Foundations.Complexity

variable {u : ℕ} {Extra τ : Type}

def polarityField (p : Position u) : Arena u Extra :=
  SourceContextLoad.polarityField p.1 (slotEncoding.code p.2)

theorem place_injective : Function.Injective (place (u := u) (Extra := Extra)) := by
  intro a b h
  have h' := congrArg unplace h
  simpa only [unplace_place, Option.some.injEq] using h'

variable [DecidableEq Extra]

theorem fill_update (base : Arena u Extra → List Bool)
    (localTapes : MachineFieldProfile.Tape (Width u) → List Bool)
    (k : MachineFieldProfile.Tape (Width u)) (value : List Bool) :
    fill base (Function.update localTapes k value) =
      Function.update (fill base localTapes) (place k) value := by
  funext a
  cases hu : unplace a with
  | none =>
    have hne : a ≠ place k := by
      intro h
      rw [h, unplace_place] at hu
      contradiction
    simp only [fill, hu, Function.update_of_ne hne]
  | some j =>
    have ha := place_unplace a j hu
    rw [← ha]
    by_cases h : j = k
    · subst j
      simp only [fill_place]
      simp [Function.update]
    · have hne : place (Extra := Extra) j ≠ place k := fun h' => h (place_injective h')
      simp only [fill_place, Function.update_of_ne h, Function.update_of_ne hne]

/-- Reassociate finite registers without adding a transition. -/
def signStateEquiv (u : ℕ) (τ : Type) :
    SourceSignLoad.State u (ProfileState u × τ) ≃ State u τ where
  toFun x := (x.2.1, (x.1, x.2.2))
  invFun x := (x.2.1, (x.1, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq Extra] in
/-- Unary sign fields may retain arbitrary old suffixes: only the leading
sign bit is read. -/
theorem loaded_sign_field (F : Formula) (c : ClauseContext F u)
    (base : Arena u Extra → List Bool) (p : Position u) :
    SourceContextLoad.stageTapes F c base u (polarityField p) =
      encodeWord (if positiveAt (clauseAt F (c p.1)) p.2 then 1 else 0) ++
        base (polarityField p) := by
  have ho := SourceContextLoad.output_polarity F c base p.1 (slotEncoding.code p.2)
  change SourceContextLoad.stageTapes F c base u (polarityField p) =
    encodeWord (if F.clauses[(c p.1).val][(slotEncoding.code p.2).val].positive then 1 else 0) ++
      base (polarityField p) at ho
  rw [ho]
  rcases p with ⟨t, s⟩
  cases s <;> rfl

end UniqueGamesTheorem.Foundations.Hastad.SourceSignaturePrepare

namespace UniqueGamesTheorem.Foundations.Hastad.SourceContextPrepare

open Turing UniqueGamesTheorem.Foundations.Complexity
open Target PCP SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge

variable {u : Nat} {Extra τ : Type}

def stateSwap (u : Nat) (τ : Type) : PrepareState u τ × LoadState ≃ State u τ :=
  Equiv.prodComm _ _

end UniqueGamesTheorem.Foundations.Hastad.SourceContextPrepare

/-! The actual numbered equation list has exactly the acceptance bounded by
the private Fourier decoder. Only the repeated base-game value is an input
here; list semantics and all finite sampling laws are supplied. -/
noncomputable section
namespace UniqueGamesTheorem.Foundations.Hastad.SourceSoundness

open scoped BigOperators
open Target SourceContexts SourceOccurrences SourceGame

/-- Exact finite occurrence-list soundness, including arbitrary assignments
to unused padded proof bits and to the dummy bit. -/
theorem sourceList_sound (F : Formula) (hne : F.clauses ≠ []) (u D : ℕ)
    (hD : 0 < D) (hDtwo : 2 ≤ D) (δ : ℝ) (hδ : 0 ≤ δ)
    (hvalue : ((baseGame F hne).repetition u).value ≤
      4 * (D : ℝ)⁻¹ * δ ^ 2)
    (bits : Fin (nBits F u) → Bool) :
    ((sourceList F u D).countP (fun e => UniqueGamesTheorem.Reduction.CloneGap.satisfied e bits) : ℝ) /
      (sourceList F u D).length ≤ (1 + δ) / 2 := by
  rw [sourceList_nonempty F u D hne, rawSourceList_acceptance F u D hD]
  have hε : (0 : ℝ) < (D : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hD)
  have hε' : (D : ℝ)⁻¹ ≤ (1 : ℝ) / 2 := by
    have hd : (2 : ℝ) ≤ D := by exact_mod_cast hDtwo
    simpa only [one_div] using
      (inv_le_inv₀ (Nat.cast_pos.mpr hD) (by norm_num : (0 : ℝ) < 2)).mpr hd
  have h := source_acceptance_le_split F hne u ((D : ℝ)⁻¹) δ
    (fun _ => leftAnchor u) (leftTable F u bits) (rightOracle F u bits)
    hε hε' hδ hvalue
  simpa only [leftTable_answer, rightOracle_answer] using h

/-- The direct uniform reduction consumes rational occurrence fractions. -/
theorem sourceList_sound_rat (F : Formula) (hne : F.clauses ≠ []) (u D : ℕ)
    (hD : 0 < D) (hDtwo : 2 ≤ D) (δ : ℚ) (hδ : 0 ≤ δ)
    (hvalue : ((baseGame F hne).repetition u).value ≤
      4 * (D : ℝ)⁻¹ * (δ : ℝ) ^ 2)
    (bits : Fin (nBits F u) → Bool) :
    ((sourceList F u D).countP (fun e => UniqueGamesTheorem.Reduction.CloneGap.satisfied e bits) : ℚ) /
      (sourceList F u D).length ≤ (1 + δ) / 2 := by
  have h := sourceList_sound F hne u D hD hDtwo (δ : ℝ)
    (by exact_mod_cast hδ) hvalue bits
  apply (Rat.cast_le (K := ℝ)).mp
  push_cast
  exact h

end UniqueGamesTheorem.Foundations.Hastad.SourceSoundness

end

namespace UniqueGamesTheorem.Foundations.Hastad.SourceTestEmit

open Turing
open Target SourceContexts SourceOccurrences SourceLocalSignature SourceLocalEquation
open SourceAddressDescriptors SourceEquationEmit
open UniqueGamesTheorem.Reduction.CloneGap
open Complexity

abbrev Label (u D : ℕ) := Unit ⊕ (LocalInput u D × SourceEquationEmit.Label)

def bodyLabel (u D : ℕ) (state : LocalInput u D) (label : SourceEquationEmit.Label) :
    Label u D := .inr (state, label)

end UniqueGamesTheorem.Foundations.Hastad.SourceTestEmit

namespace UniqueGamesTheorem.Foundations.Hastad.SourceTestAppend

open Turing Complexity
open Target SourceContexts SourceOccurrences SourceLocalSignature SourceLocalEquation
open SourceAddressDescriptors SourceEquationEmit SourceTestEmit

inductive Label (u D : Nat)
  | test (label : SourceTestEmit.Label u D)
  | append
  deriving DecidableEq, Fintype

def steps (u D : Nat) (values : Fin 3 → Nat) (state : LocalInput u D) : Nat :=
  SourceEquationEmit.steps values (localEquation u D state) + 1 +
    (equationBits u D values state).length + 1

variable {K Λ : Type} [DecidableEq K]

def bodyLabel (u D : Nat) (labels : Label u D → Λ) (state : LocalInput u D)
    (label : SourceEquationEmit.Label) : Λ :=
  labels (.test (SourceTestEmit.bodyLabel u D state label))

theorem resultTapes_other (layout : Layout K) (base : K → List Bool) (bits : List Bool)
    (k : K) (hk : k ≠ layout.accumulator) : resultTapes layout base bits k = base k := by
  simp [resultTapes, hk]

theorem resultTapes_source (layout : Layout K) (base : K → List Bool) (bits : List Bool)
    (side : Fin 3) : resultTapes layout base bits (layout.sources side) = base (layout.sources side) :=
  resultTapes_other layout base bits _ (layout.sourceAccumulator side)

theorem resultTapes_temporary (layout : Layout K) (base : K → List Bool) (bits : List Bool) :
    resultTapes layout base bits layout.temporary = base layout.temporary :=
  resultTapes_other layout base bits _ layout.temporaryAccumulator

theorem resultTapes_scratch (layout : Layout K) (base : K → List Bool) (bits : List Bool) :
    resultTapes layout base bits layout.scratch = base layout.scratch :=
  resultTapes_other layout base bits _ layout.scratchAccumulator

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

open Turing Complexity Target SourceContexts SourceOccurrences
open SourceLocalSignature SourceLocalEquation

inductive Label (u D n : Nat)
  | load (index : Fin (n + 1))
  | emit (index : Fin n) (label : SourceTestAppend.Label u D)
  deriving DecidableEq, Fintype

variable {K Λ : Type} [DecidableEq K]

def prefixSteps (u D : Nat) (queries : Nat → Query u D)
    (values : Fin 3 → Nat) (signature : Signature u) : Nat → Nat
  | 0 => 0
  | n + 1 => prefixSteps u D queries values signature n +
      (SourceTestAppend.steps u D values (signature, queries n) + 1)

theorem prefixSteps_le (u D n B : Nat) (queries : Nat → Query u D)
    (values : Fin 3 → Nat) (signature : Signature u)
    (hbound : ∀ i, i < n → SourceTestAppend.steps u D values (signature, queries i) ≤ B) :
    prefixSteps u D queries values signature n ≤ n * (B + 1) := by
  induction n with
  | zero => simp [prefixSteps]
  | succ n ih =>
    have hp := ih (fun i hi => hbound i (by omega))
    have hb := hbound n (by omega)
    rw [prefixSteps, Nat.succ_mul]
    omega

end UniqueGamesTheorem.Foundations.Hastad.SourceQueryLoop

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceLoopOrder

open Complexity Complexity.MachineTupleOdometer
open Target SourceContexts SourceOccurrences
open UniqueGamesTheorem.Reduction

/-- Total extension of the declared tape decoder, for the query loop's natural
index register. Out-of-range values are never visited by that loop. -/
def rankedQuery (u D : ℕ) (fallback : SourceQueryLoop.Query u D)
    (i : ℕ) : SourceQueryLoop.Query u D :=
  if h : i < (testTapeEncoding u D).size then
    (testTapeEncoding u D).code.symm ⟨i, h⟩
  else fallback

theorem rankedQuery_at (u D : ℕ) (fallback : SourceQueryLoop.Query u D)
    (i : Fin (testTapeEncoding u D).size) :
    rankedQuery u D fallback i.val = (testTapeEncoding u D).code.symm i := by
  simp only [rankedQuery, i.isLt, ↓reduceDIte]

theorem query_prefixBits_eq_ofFn (u D n : ℕ) (queries : ℕ → SourceQueryLoop.Query u D)
    (values : Fin 3 → ℕ) (signature : SourceLocalSignature.Signature u) :
    SourceQueryLoop.prefixBits u D queries values signature n =
      (List.ofFn (fun i : Fin n => queries i.val)).flatMap
        (fun query => SourceTestAppend.equationBits u D values (signature, query)) := by
  induction n with
  | zero => simp [SourceQueryLoop.prefixBits]
  | succ n ih =>
    rw [SourceQueryLoop.prefixBits, List.ofFn_succ', List.concat_eq_append,
      List.flatMap_append]
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      Fin.val_castSucc, Fin.val_last] using
      congrArg (fun bits => bits ++
        SourceTestAppend.equationBits u D values (signature, queries n)) ih

theorem query_prefixBits_eq_enumerate (u D : ℕ) (fallback : SourceQueryLoop.Query u D)
    (values : Fin 3 → ℕ) (signature : SourceLocalSignature.Signature u) :
    SourceQueryLoop.prefixBits u D (rankedQuery u D fallback) values signature
        (testTapeEncoding u D).size =
      (testTapeEncoding u D).enumerate.flatMap
        (fun query => SourceTestAppend.equationBits u D values (signature, query)) := by
  rw [query_prefixBits_eq_ofFn]
  have hlist : List.ofFn (fun i : Fin (testTapeEncoding u D).size =>
      rankedQuery u D fallback i.val) = (testTapeEncoding u D).enumerate := by
    apply congrArg List.ofFn
    funext i
    exact rankedQuery_at u D fallback i
  rw [hlist]

end UniqueGamesTheorem.Foundations.Hastad.SourceLoopOrder

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceQueryOrderLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Foundations.Hastad.SourceQueryOrder

open Turing Complexity Target SourceContexts SourceOccurrences
open SourceLocalSignature SourceAddressDescriptors SourceLoopOrder


def occurrenceBits (F : Formula) (u D : Nat) (p : SourceIndex F u D) : List Bool :=
  encodeWords (UniqueGamesTheorem.Reduction.SourceEncoding.equationWords (sourceEquation F u D p))

def slotBits (F : Formula) (u D : Nat) (c : ClauseContext F u) (s : SlotContext u) :
    List Bool :=
  (testTapeEncoding u D).enumerate.flatMap (fun t => occurrenceBits F u D ((c, s), t))

def tupleBits (F : Formula) (u D : Nat) (c : ClauseContext F u) : List Bool :=
  (slotContextEncoding u).enumerate.flatMap (slotBits F u D c)

end UniqueGamesTheorem.Foundations.Hastad.SourceQueryOrder



namespace UniqueGamesTheorem.Foundations.Hastad.SourceRuntimeModel

open Turing Complexity SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge


variable {u D : Nat} {Extra : Type}

def rankControls (header : SourceLoopInit.HeaderTape) : Fin 6 ↪ BodyExtra Extra where
  toFun
    | 0 => .inl header
    | 1 => .inr .accA
    | 2 => .inr .accB
    | 3 => .inr .rank
    | 4 => .inr .counter
    | 5 => .inr .arithScratch
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

end UniqueGamesTheorem.Foundations.Hastad.SourceRuntimeModel



namespace UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorModel

open Turing Complexity SourceRuntimeModel


noncomputable def coefficientKeys (u D : Nat) : List (SourceHeaderCounts.Coefficients u D) :=
  (List.finRange (CookLevin.PolynomialMachine.width
    (SourceHeaderCounts.polynomial u D .left))).map Sum.inl ++
  (List.finRange (CookLevin.PolynomialMachine.width
    (SourceHeaderCounts.polynomial u D .right))).map (fun i => Sum.inr (Sum.inl i)) ++
  (List.finRange (CookLevin.PolynomialMachine.width
    (SourceHeaderCounts.polynomial u D .occurrences))).map (fun i => Sum.inr (Sum.inr i))

end UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorModel



namespace UniqueGamesTheorem.Foundations.Hastad.SourceStartup

open Turing Complexity SourceRuntimeModel SourceGeneratorModel
open MachineComposition


noncomputable section

variable {u D : Nat}

abbrev ArithmeticLabel (u D : Nat) := SourceHeaderCounts.Label u D ⊕ Bool
abbrev Label (u D : Nat) := SourceLoopInit.Label u ⊕ ArithmeticLabel u D

def arithmeticEntry (u D : Nat) : ArithmeticLabel u D :=
  .inl (SourceHeaderCounts.evalStart .left)

local instance instDecidableEqExtra_rc4b462_1 (u D : Nat) : DecidableEq (SourceGeneratorModel.Extra u D) := Classical.decEq _
def timePolynomial (u D : Nat) : Polynomial Nat :=
  SourceLoopInit.timePolynomial u + SourceHeaderCounts.timePolynomial u D +
    SourceHeaderCounts.polynomial u D .left + SourceHeaderCounts.polynomial u D .right +
    SourceHeaderCounts.polynomial u D .occurrences + Polynomial.C 5

end

end UniqueGamesTheorem.Foundations.Hastad.SourceStartup



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


abbrev QueryCount (u D : Nat) := (testTapeEncoding u D).size

end UniqueGamesTheorem.Foundations.Hastad.SourceTupleBody

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

open Complexity SourceContexts SourceOccurrences SourceTupleBody
open Complexity.MachineComposition

variable {u D : Nat}

noncomputable def slotPolynomial (u D : Nat) : Polynomial Nat :=
  Polynomial.C 1 + MachineHorner.timePolynomial u +
    (SourceBasePhase.timePolynomial (2 ^ (2 ^ u))).comp (rankPolynomial u + Polynomial.C 2) +
    (Polynomial.C (QueryCount u D) * (Polynomial.C 9 * numberPolynomial u + Polynomial.C 21) +
      Polynomial.C 1) +
    (rankPolynomial u + Polynomial.C 2) + (numberPolynomial u + Polynomial.C 2)

theorem slotPolynomial_eval (u D L : Nat) :
    (slotPolynomial u D).eval L =
      1 + (MachineHorner.timePolynomial u).eval L +
        (SourceBasePhase.timePolynomial (2 ^ (2 ^ u))).eval (L ^ u + 2) +
        (QueryCount u D * (9 * (SourceBounds.bitCoefficient u * L ^ u) + 21) + 1) +
        (L ^ u + 2) + (SourceBounds.bitCoefficient u * L ^ u + 2) := by
  simp only [slotPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_comp, rankPolynomial_eval, numberPolynomial_eval]

noncomputable def preparePolynomial (u : Nat) : Polynomial Nat :=
  Polynomial.C u * (Polynomial.C 10 * Polynomial.X + Polynomial.C 20) + Polynomial.C 1 +
    (Polynomial.C (SourceSignaturePrepare.Width u * SourceSignaturePrepare.Width u) *
      (Polynomial.C 5 * Polynomial.X + Polynomial.C 6) + Polynomial.C 2)

theorem preparePolynomial_eval (u L : Nat) :
    (preparePolynomial u).eval L =
      (u * (10 * L + 20) + 1) +
        (SourceSignaturePrepare.Width u * SourceSignaturePrepare.Width u * (5 * L + 6) + 2) := by
  simp only [preparePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]

noncomputable def setupPolynomial (u : Nat) : Polynomial Nat :=
  preparePolynomial u + Polynomial.C 1 + MachineHorner.timePolynomial u +
    (SourceBasePhase.timePolynomial (2 ^ (8 ^ u))).comp
      (rankPolynomial u + numberPolynomial u + Polynomial.C 2) +
    (rankPolynomial u + Polynomial.C 2)

theorem setupPolynomial_eval (u L : Nat) :
    (setupPolynomial u).eval L =
      (preparePolynomial u).eval L + 1 + (MachineHorner.timePolynomial u).eval L +
        (SourceBasePhase.timePolynomial (2 ^ (8 ^ u))).eval
          (L ^ u + SourceBounds.bitCoefficient u * L ^ u + 2) + (L ^ u + 2) := by
  simp only [setupPolynomial, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_comp, rankPolynomial_eval, numberPolynomial_eval]

end UniqueGamesTheorem.Foundations.Hastad.SourceTupleBound

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_TableIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Iteration of the concrete stored-table round, with the original formula's
actual initial graph size controlling the number of rounds. -/

namespace UniqueGamesTheorem.Foundations.PCP.TableIteration

open RoundTables
open Target Complexity

theorem run_completeness (H : BaseTable) (n : Nat) (input : Input)
    (sat : Satisfiable input) : Satisfiable (run H n input) :=
  AmplificationIteration.run_preserves (step H) Satisfiable (step_completeness H) n input sat

end UniqueGamesTheorem.Foundations.PCP.TableIteration

end

end OAI
end


