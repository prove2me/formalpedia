-- Prove2me | Definitions.Def_OAIQ087A025
-- name    : OAIQ087A025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:38:58.983184+00:00
-- url     : https://prove2.me/theorems/02b2d4c1-d4a1-46f2-b113-f0183938b43b
-- title:
--   Definitions bundle OAIQ087A025 of the split of OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 334 declarations of OpenAI's Lean: 169 definitions, 5 inductive types or structures, 1 instance and 159 theorems. The definitions and types are `OAI.MaxCutGames.Foundations.Complexity.MachineRegularMetadata.originalMember`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularMetadata.ownerData`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularMetadata.ownerRemainder`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularMetadata.ownerSteps`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularMetadata.rankData`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularMetadata.rankRemainder`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularMetadata.rankSteps`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularOriginalBody.FamilyState`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularOriginalBody.State`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularOriginalBody.familyStates`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularOriginalBody.metadataStates`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularOriginalBody.readyState`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularOriginalBody.vertexStates`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularOriginalClean.Input`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularOriginalClean.steps`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularOriginalRow.Input`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularOriginalRow.affined`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularOriginalRow.copied`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularOriginalRow.emittedWords`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularOriginalRow.finalTapes`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularOriginalRow.looked`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularOriginalRow.prefixWords`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularOriginalRow.rowSteps`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularOriginalRow.steps`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularOriginalRow.suffixWords`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.FamilyState`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.State`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.familyStates`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.metadataStates`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.readyState`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.vertexStates`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.State`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Header.Label`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Header.copyExit`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Header.fieldExit`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.State`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.headerStates`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.readyState`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularVertexBlock.originalMemory`, `OAI.MaxCutGames.Foundations.Complexity.MachineRepeat.bodyReturn` and 134 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MaxCut_Estimates_Basic`, `MaxCut_Games_PoweringMasterState`, `MaxCut_Games_PoweringPlanBudget`, `MaxCut_Machines_Alphabet`, `MaxCut_Machines_EmitRows`, `MaxCut_Machines_MachineRegularLift`, `MaxCut_Machines_MachineRegularMetadata`, `MaxCut_Machines_MachineRegularOriginalBody`, `MaxCut_Machines_MachineRegularOwnerProgram`, `MaxCut_Machines_MachineRegularVertexBlock`, `MaxCut_Machines_PoweringMachineField`, `MaxCut_Machines_PoweringMachineGlobal`, `MaxCut_Machines_PoweringMachineRelation`, `MaxCut_Machines_PoweringMachineRotor`, `MaxCut_Machines_PoweringMachineRowHeaders`, `MaxCut_Machines_PoweringMachineVertex`, `MaxCut_Machines_RawInitialMachineBudget`, `MaxCut_Machines_Runtime2`, `MaxCut_Machines_RuntimeSpace`, `MaxCut_Machines_SelectorMachine`, `MaxCut_PCP_ContextPrepare`, `MaxCut_PCP_PortTableLookup`, `MaxCut_PCP_PoweringOpinionTables`, `MaxCut_PCP_PoweringRowData`, `MaxCut_PCP_PoweringRowHeaderSemantics`, `MaxCut_PCP_PoweringTableLayout`, `MaxCut_PCP_PreprocessingFamilyBridge`, `MaxCut_PCP_PreprocessingPaddingWords`, `MaxCut_PCP_RawInitialTables`.
--
--   **Imports.** It imports the bundles `OAIQ087A014`, `OAIQ087A015`, `OAIQ087A016`, `OAIQ087A017` and `OAIQ087A018` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ087A030`, `OAIQ087A031` and `OAIQ087A032`.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ087A014
import Definitions.Def_OAIQ087A015
import Definitions.Def_OAIQ087A016
import Definitions.Def_OAIQ087A017
import Definitions.Def_OAIQ087A018

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_RuntimeSpace
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intermediate tape-space bounds derived from actual successful machine
prefixes, and their use in the separately checked physical finalizer. -/

/-! A fixed finite TM2 interpreter for a unary number of runs of a fixed
certified machine. The counter is data on a separate tape. Every body run is
lifted from an actual `TM2OutputsInTime` witness, and all transfers are executed
by the checked finite transfer loops. -/

namespace MaxCutGames.Foundations.Complexity.MachineRepeat
open Turing

variable (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool) (output : M.Γ M.k₁ ≃ Bool)

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
  rw [hs,hd,List.append_nil,bodyToTemp_tapes_inline_MachineRepeat] at run
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
        inputTapes M word.reverse counter from tempToBody_tapes_inline_MachineRepeat M word counter] at run
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
  rw [inputTapes_input,hd,List.map_id,List.append_nil,finalToTemp_tapes_inline_MachineRepeat] at run
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
  rw [hs,hd,List.map_id,List.append_nil,tempToOutput_tapes_inline_MachineRepeat] at run
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
  have guard := oneStep_inline_MachineRepeat _ _ _ (guardStep_none M input output word)
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
    have guard := oneStep_inline_MachineRepeat _ _ _ (guardStep_some M input output ((words 0).map input.symm)
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
  rw [inputConfig_init_inline_MachineRepeat M input output] at full
  have input_append := @List.map_append Bool
    ((machine M input output).Γ (machine M input output).k₀) input.symm
    (encodeWord count) (words 0)
  simpa only [TM2OutputsInTime, Option.map_some, input_append, Nat.add_comm] using! full

end MaxCutGames.Foundations.Complexity.MachineRepeat

/-!
Finiteness of every alphabet of the actual machines used by the reduction.
`FinTM2` already bundles finitely many tapes, control labels and register states,
but its alphabet field only requires the input tape alphabet to be finite.
This additional property is preserved by the actual sequential and repetition
constructors; it does not replace or alter their execution certificates.
-/

/-! Whole-instance uniform copying: exact physical header arithmetic, repeated
body emission, actual cleanup, and a polynomial bound in the input codec length. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ContextPrepare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceContextPrepare

open Turing MaxCutGames.Foundations.Complexity
open Target PCP SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge

variable {u : Nat} {Extra τ : Type}

def stateSwap (u : Nat) (τ : Type) : PrepareState u τ × LoadState ≃ State u τ :=
  Equiv.prodComm _ _

end MaxCutGames.Foundations.Hastad.SourceContextPrepare

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PoweringOpinionTables
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

namespace MaxCutGames.Foundations.PCP.PoweringOpinionTables

open PoweringWalks PoweringLabels PoweringAddresses PoweringReach
open scoped BigOperators

variable {X A : Type*}

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

end MaxCutGames.Foundations.PCP.PoweringOpinionTables

/-!
# Executable directed graph tables over a fixed finite alphabet

The alphabet size `q` is fixed by the encoding, not encoded as a variable input
field. The header stores vertex and directed-dart counts. Each ordered dart row
stores its tail, reverse index, and every `q*q` predicate bit in order `b+q*a`.
All fields use the existing unary natural-word codec. Decoding validates graph
laws and preserves loops and repeated darts. Size bounds count the complete
serialized table and make no running-time assertion.
-/

/-!
# Executable tables of the actual powering graph

The input rotor and every base predicate are stored finite vectors. The output
has one row for each start vertex, bounded port word, and orientation, with the
two orientations adjacent. Every complete predicate table is generated from the
bounded first-address lookup test. Degree and walk length fix the output alphabet;
neither the alphabet nor an address list depends on the input vertex count.
-/

namespace MaxCutGames.Foundations.PCP.PoweringTables

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

end MaxCutGames.Foundations.PCP.PoweringTables

/-!
# Actual rejection counts and sizes for the powering construction

Normalized rejection averages are the cardinal ratios of the corresponding
rejected-dart sets. These identities include empty finite types. Positivity
of the dart cardinality is required only when translating inequalities by
division. The powered dart count and common alphabet size are computed from
their actual product and function types.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_EmitRows
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

/-! Actual finite-stack cleanup. Each selected stack is drained using the
checked pop loop, followed by one transition resetting the finite state.
Repeated selections are allowed; they only reduce the cost upper bound. -/

/-!
Exact tape invariant for the old-dart loop. The cursor stores the remaining
input rows, while the reversed tape stores precisely the output headers and
the blocks already emitted. The scan and index-scan tapes are unconstrained:
the next lookup prefixes fresh copies and retains old residues as suffixes.
Finite control state is specified by the actual execution theorems using this
tape invariant.
-/

namespace MaxCutGames.Foundations.PCP.AlphabetTable.LoopState

open MaxCutGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

@[simp] theorem cursorBits_full (input : GenericGraphTables.Table q) :
    cursorBits input input.darts = [] := by
  have finished := List.drop_length (l := GenericGraphTables.rowList input)
  rw [GenericGraphTables.rowList_length] at finished
  unfold cursorBits cursorWords
  rw [finished]
  rfl

end MaxCutGames.Foundations.PCP.AlphabetTable.LoopState

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Runtime2
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every work tape of the actual alphabet-table machine stores Bool symbols.
This checks the work alphabets separately from the finite-machine structure's
input-alphabet condition, without changing the runtime certificate. -/

/-!
# Exact register-equivalence transport for finite-stack programs

The instruction translation reuses `MachineControl.statement` with unchanged
labels. An explicit register equivalence changes neither tapes nor labels.
The transition function, every iterated trace, and runtime witnesses are
transported in exactly the same number of transitions, including failed or
halted traces. No simulation premise is assumed.
-/

namespace MaxCutGames.Foundations.Complexity.MachineUnaryEqualityBit

open Turing
open MachineComposition

variable {K Λ A : Type} [DecidableEq K]

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
  have copied := joinTrace_inline_MachineUnaryEqualityBit leftRun rightRun
  have compared := joinTrace_inline_MachineUnaryEqualityBit copied compareRun
  rw [steps, Function.iterate_succ_apply', compared, advance_some]
  exact emitRun

end MaxCutGames.Foundations.Complexity.MachineUnaryEqualityBit

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

namespace MaxCutGames.Foundations.Complexity.PoweringMachineRow

open Turing
open MachineFixedBlockMap
open MaxCutGames.Foundations.PCP

/-! ## Fixed finite relation calculation -/

theorem rowAccept_eq_true {t S q : Nat}
    (labelAt : Fin q → Fin S → GraphTables.Label)
    (bits : Buffer (inputSize t S)) (a b : Fin q) :
    rowAccept labelAt bits a b = true ↔ ∀ k, edgeAccept labelAt bits k a b = true := by
  simp [rowAccept, List.all_eq_true, List.mem_ofFn]

/-! ## Actual unary Boolean field instructions -/

/-! ## Concrete row machine and its actual one-step execution -/

end MaxCutGames.Foundations.Complexity.PoweringMachineRow

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularLift
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
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

namespace MaxCutGames.Foundations.Complexity.MachineRegularOriginalRow

open Turing MachineComposition
open PCP PCP.GraphTables PCP.PreprocessingRegularTables

def prefixWords (t : Table) (e : Fin t.darts) : List Nat :=
  [t.vertices, t.darts] ++ ((rowList t).take e.val).flatMap rowWords

def suffixWords (t : Table) (e : Fin t.darts) : List Nat :=
  ((rowList t).drop (e.val + 1)).flatMap rowWords

theorem prefixWords_length (t : Table) (e : Fin t.darts) :
    (prefixWords t e).length = 2 + 4098 * e.val := by
  simp only [prefixWords, List.length_append, List.length_cons, List.length_nil,
    rowsWords_length, List.length_take, rowList_length, Nat.min_eq_left e.isLt.le]

theorem tableWords_at_row (t : Table) (e : Fin t.darts) :
    GraphTables.tableWords t = prefixWords t e ++ (rowWords t.rows[e] ++ suffixWords t e) := by
  have he : e.val < (rowList t).length := by simpa only [rowList_length] using e.isLt
  have hs : (rowList t).take e.val ++ (rowList t)[e.val] ::
      (rowList t).drop (e.val + 1) = rowList t := by
    rw [List.getElem_cons_drop he, List.take_append_drop]
  have hw := congrArg (fun rs : List (DartRow t.vertices t.darts) => rs.flatMap rowWords) hs
  simp only [List.flatMap_append, List.flatMap_cons, rowList, Vector.getElem_toList] at hw
  unfold GraphTables.tableWords prefixWords suffixWords rowList
  rw [← hw]
  simp only [List.append_assoc, Fin.getElem_fin]

theorem tableWords_drop_row (t : Table) (e : Fin t.darts) :
    (GraphTables.tableWords t).drop (2 + 4098 * e.val) = rowWords t.rows[e] ++ suffixWords t e := by
  rw [tableWords_at_row]
  exact List.drop_left' (l₂ := rowWords t.rows[e] ++ suffixWords t e)
    (prefixWords_length t e)

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

def emittedWords (q : Nat) (t : Table) (e : Fin t.darts) : List Nat :=
  e.val :: ((q + 1) * t.rows[e].reverseIndex.val + q) :: relationWords t.rows[e].relation

theorem affined_fields (q : Nat) (t : Table) (e : Fin t.darts)
    (base : Tape → List Bool) (input : Input t e base) :
    MachineTableRows.fieldBits fields (affined q t e base) = encodeWords (emittedWords q t e) := by
  have htail := affined_other q t e base 0 (by decide) (by decide) (by decide)
    (by decide) (by decide)
  simp only [MachineTableRows.fieldBits, fields_zero, fields_one, fields_two,
    htail, input.indexWord, affined_reverse, input.computedEmpty,
    affined_relation, input.relationEmpty, List.append_nil,
    emittedWords, encodeWords, List.append_assoc]

def rowSteps (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) : Nat :=
  4 * (encodeWords (emittedWords q t e)).length + 2 * (base 9).length + 9

def steps (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) : Nat :=
  MachineAffineLookup.steps (GraphTables.tableWords t) e.val 4098 3 + 1 +
    (2 * (t.rows[e].reverseIndex.val + 1) + 1) + rowSteps q t e base

def finalTapes (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    Tape → List Bool :=
  Function.update (affined q t e base) 9 (base 9 ++ encodeWords (emittedWords q t e))

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

end MaxCutGames.Foundations.Complexity.MachineRegularOriginalRow

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularMetadata
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual metadata preparation for an original regularized vertex. The
shared 27-tape row interface is preserved, with two explicit extra outputs
for padding count and geometric level. Family generation is a subsequent
stage and owns the rotor tape. -/

namespace MaxCutGames.Foundations.Complexity.MachineRegularMetadata

open Turing MachineComposition
open MaxCutGames.Foundations.PCP

variable {σ : Type}

theorem selected_owner (t : GraphTables.Table) (e : Fin t.darts) :
    (GraphTables.tableWords t)[4098 * e.val + 2]? = some t.rows[e].tail.val := by
  have h := congrArg (fun words : List Nat => words[0]?)
    (MachineRegularOriginalRow.tableWords_drop_row t e)
  simp only [List.getElem?_drop, Nat.add_zero] at h
  rw [show 2 + 4098 * e.val = 4098 * e.val + 2 by omega] at h
  simpa [GraphTables.rowWords] using h

def ownerData (t : GraphTables.Table) (e : Fin t.darts) (data : Data) : Data :=
  { data with owner := encodeWord t.rows[e].tail.val }

def ownerRemainder (t : GraphTables.Table) (e : Fin t.darts) : List Bool :=
  encodeWords ((GraphTables.tableWords t).drop (4098 * e.val + 2 + 1))

def ownerSteps (t : GraphTables.Table) (e : Fin t.darts) : Nat :=
  MachineAffineLookup.steps (GraphTables.tableWords t) e.val 4098 2 + 2 +
    ((ownerRemainder t e).length + 1)

def rankData (t : GraphTables.Table) (v : Fin t.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics t) v) (data : Data) : Data :=
  { data with localRank := encodeWord (PreprocessingCloudIndex.cloudRank t v e).val }

def rankRemainder (t : GraphTables.Table)
    (v : Fin t.vertices) (e : DegreeReplacement.Cloud (GraphTables.semantics t) v) : List Bool :=
  encodeWords (((MachineCloudCount.tableRows t).drop e.val.val).flatMap MachineCloudCount.rowWords)

def rankSteps (t : GraphTables.Table) (v : Fin t.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics t) v) : Nat :=
  querySteps v.val e.val.val +
    MachineCloudRank.rankSteps t.vertices t.darts v.val e.val.val (MachineCloudCount.tableRows t) [] +
    ((rankQuery v.val e.val.val).length + 1) + ((rankRemainder t v e).length + 1) + 2

/-- Membership is a statement about the actual stored tail, used only to
identify the numeric answer of the physical rank routine. -/
def originalMember (t : GraphTables.Table) (e : Fin t.darts) :
    DegreeReplacement.Cloud (GraphTables.semantics t) t.rows[e].tail := ⟨e, rfl⟩

theorem encodeWords_drop_length_le_inline_MachineRegularMetadata (values : List Nat) (n : Nat) :
    (encodeWords (values.drop n)).length ≤ (encodeWords values).length := by
  have h := congrArg (fun words : List Nat => (encodeWords words).length)
    (List.take_append_drop n values)
  simp only [encodeWords_append, List.length_append] at h
  omega

theorem ownerRemainder_length_le (t : GraphTables.Table) (e : Fin t.darts) :
    (ownerRemainder t e).length ≤ (GraphTables.tableBits t).length :=
  encodeWords_drop_length_le_inline_MachineRegularMetadata _ _

end MaxCutGames.Foundations.Complexity.MachineRegularMetadata

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Alphabet
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

namespace MaxCutGames.Foundations.Complexity.MachineRegularInternalRow

open Turing MachineComposition
open PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ : Type} [DecidableEq K]

theorem alphabet_tapes_apply_inline_MachineRegularInternalRow {K : Type} {Γ Δ : K → Type}
    (h : Γ = Δ) (base : ∀ k, List (Γ k)) (k : K) :
    MachineAlphabetTransport.tapes h base k =
      Eq.mp (congrArg (fun alphabet => List (alphabet k)) h) (base k) := by
  cases h
  rfl

theorem selectToBoolTapes_eq (base : ∀ k, List (RawSelectAlphabet k)) :
    selectToBoolTapes base = MachineAlphabetTransport.tapes selectAlphabet_eq base := by
  funext k
  rw [alphabet_tapes_apply_inline_MachineRegularInternalRow]
  cases k with
  | inl k => cases k <;> rfl
  | inr k => rfl

end MaxCutGames.Foundations.Complexity.MachineRegularInternalRow

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_SelectorMachine
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineRegularInternalRow
open Turing MachineComposition
open PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)
variable {K Λ σ : Type} [DecidableEq K]

/-- A selected original dart is below the original dart count; a dummy
target is the old-dart count plus its physical prefix and local remainder. -/
theorem selectedIndex_le (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (PreprocessingCloudIndex.cloudSize t v + padding v)) :
    PreprocessingInternalRows.selectedIndex t padding v i ≤
      t.darts + PreprocessingPaddingOffsets.offset padding v.val + i.val := by
  unfold PreprocessingInternalRows.selectedIndex
  split
  · rename_i hi
    have h := (PreprocessingCloudIndex.cloudSelect t v ⟨i.val, hi⟩).val.isLt
    omega
  · omega

theorem encodedDrop_length_le (values : List Nat) (n : Nat) :
    (encodeWords (values.drop n)).length ≤ (encodeWords values).length := by
  have h : (encodeWords (values.take n)).length + (encodeWords (values.drop n)).length =
      (encodeWords values).length := by
    rw [← List.length_append, ← encodeWords_append, List.take_append_drop]
  omega

/-- Every rotor entry occupies at least its delimiter on the physical tape. -/
theorem rotorSize_le_encodedLength {n q : Nat} (positive : 0 < q)
    (table : ExpanderTables.Table n q) :
    n ≤ (encodeWords (ExpanderTableWords.rotationWords table)).length := by
  have h : n * q ≤ (encodeWords (ExpanderTableWords.rotationWords table)).length := by
    rw [encodeWords_length, ExpanderTableWords.rotationWords_length]
    omega
  exact (Nat.le_mul_of_pos_right n positive).trans h

end MaxCutGames.Foundations.Complexity.MachineRegularInternalRow

/-!
# Reusable inherited-row execution with actual cleanup

Five concrete drain loops remove the query delimiter, unread scan suffix,
raw reverse field, computed reverse field, and copied relation. With initially
empty work tapes, the only final tape change is the appended output row. The
index on tape zero and input table on tape one are both preserved.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularOriginalClean

open Turing MachineComposition PCP PCP.GraphTables PCP.PreprocessingRegularTables

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

end MaxCutGames.Foundations.Complexity.MachineRegularOriginalClean

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingPaddingWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact serialization of whole-vertex padding

The original dart rows remain in their original order, with every old tail,
reverse index, and relation bit unchanged. The suffix is exactly the bit stream
emitted by the checked dummy-vertex machine, starting at vertex `n` and dart
`n*d`. This is an equality for the actual table codec, with no runtime premise.
-/

/-!
# Complete serialization of the actual regularized table

Each global vertex emits its internal ports in increasing order, then its
inherited port. Original darts are the first global vertices. Dummy vertices
follow in increasing owner and local-dummy order. These are identities for the
actual stored rows and existing codec, with arbitrary actual cloud tables.
-/

namespace MaxCutGames.Foundations.PCP.PreprocessingRegularWords

open DegreeReplacement PreprocessingCloudIndex PreprocessingRegularTables Complexity
open scoped BigOperators

variable (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
variable (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)

theorem encodeWords_flatMap_inline_PreprocessingRegularWords {α : Type*} (xs : List α) (words : α → List Nat) :
    encodeWords (xs.flatMap words) = xs.flatMap (fun x => encodeWords (words x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

end MaxCutGames.Foundations.PCP.PreprocessingRegularWords

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularVertexBlock
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
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

namespace MaxCutGames.Foundations.Complexity.MachineRegularVertexBlock

open Turing MachineComposition PCP MachineRegularInternalRow
open PreprocessingCloudIndex PreprocessingRegularTables

variable {σ Λ : Type}

def originalMemory (graph : List Bool) (x : Nat) (output : List Bool) :
    MachineRegularOriginalClean.Tape → List Bool :=
  ![encodeWord x, graph, [], [], [], [], [], [], [], output]

theorem originalMemory_update (graph : List Bool) (x : Nat) (output output' : List Bool) :
    Function.update (originalMemory graph x output) (9 : MachineRegularOriginalClean.Tape) output' =
      originalMemory graph x output' := by funext j; fin_cases j <;> rfl

theorem encodeWords_flatMap_inline_MachineRegularVertexBlock {A : Type*} (xs : List A) (words : A → List Nat) :
    encodeWords (xs.flatMap words) = xs.flatMap (fun x => encodeWords (words x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem encodeWords_pair_inline_MachineRegularVertexBlock (a b : Nat) (rest : List Nat) :
    encodeWords ([a, b] ++ rest) = encodeWord a ++ (encodeWord b ++ encodeWords rest) := rfl

end MaxCutGames.Foundations.Complexity.MachineRegularVertexBlock

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingFamilyBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact serialized family tables at actual regularization vertices

The geometric family maps request zero to a one-vertex table. Empty clouds in
regularization instead remain empty. The bridge therefore requires positive
cloud size, derived here from each actual original or dummy vertex.
-/

namespace MaxCutGames.Foundations.PCP.PreprocessingFamilyBridge

open PreprocessingCloudIndex PreprocessingRegularTables ExpanderTableWords
open MaxCutGames.Foundations.Complexity (encodeWords)

/-- Transporting only the size equality leaves every serialized rotor entry
unchanged; no relabeling or alternative numbering is introduced. -/
theorem rotationWords_resizeTable {n m q : Nat} (h : n = m)
    (table : ExpanderTables.Table n q) :
    rotationWords (resizeTable h table) = rotationWords table := by
  cases h
  rfl

/-- An actual original dart supplies a member of its owner's cloud. -/
theorem cloudSize_pos_of_dart (t : GraphTables.Table) (e : Fin t.darts) :
    0 < cloudSize t t.rows[e].tail := by
  have h := (oldCloudIndex t e).isLt
  omega

end MaxCutGames.Foundations.PCP.PreprocessingFamilyBridge

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularOriginalBody
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

namespace MaxCutGames.Foundations.Complexity.MachineRegularOriginalBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable

abbrev FamilyState := MachineRegularFamily.State
abbrev State := (CoreState × MetaState) × FamilyState

theorem degree_positive : 0 < internalDegree :=
  Nat.mul_pos MachineExpanderFamily.baseDegree_positive MachineExpanderFamily.baseDegree_positive

def readyState (H : BaseTable) : State :=
  ((MachineRegularInternalRow.coreInitialState internalDegree degree_positive (),
    (((), false), none)), MachineRegularFamily.readyState H)

def metadataStates : (MetaState × (CoreState × FamilyState)) ≃ State where
  toFun p := ((p.2.1, p.1), p.2.2)
  invFun p := (p.1.2, (p.1.1, p.2))
  left_inv _ := rfl
  right_inv _ := rfl

def familyStates : (FamilyState × (CoreState × MetaState)) ≃ State := Equiv.prodComm _ _
def vertexStates : (CoreState × (MetaState × FamilyState)) ≃ State :=
  (Equiv.prodAssoc _ _ _).symm

end MaxCutGames.Foundations.Complexity.MachineRegularOriginalBody

namespace MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup

open Turing MachineComposition

variable {Λ : Type}

abbrev State := MachineRegularOriginalBody.State × Option Bool

end MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularOwnerProgram
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

namespace MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable
open PreprocessingRegularLoopWords

abbrev State := MachineRegularOriginalBody.State × Option Bool
abbrev FamilyState := MachineRegularOriginalBody.FamilyState

def readyState (H : BaseTable) : State := (MachineRegularOriginalBody.readyState H, none)

def metadataStates : (MetaState × ((CoreState × FamilyState) × Option Bool)) ≃ State where
  toFun p := (((p.2.1.1, p.1), p.2.1.2), p.2.2)
  invFun p := (p.1.1.2, ((p.1.1.1, p.1.2), p.2))
  left_inv _ := rfl
  right_inv _ := rfl

def familyStates : (FamilyState × ((CoreState × MetaState) × Option Bool)) ≃ State where
  toFun p := ((p.2.1, p.1), p.2.2)
  invFun p := (p.1.2, (p.1.1, p.2))
  left_inv _ := rfl
  right_inv _ := rfl

def vertexStates : (CoreState × ((MetaState × FamilyState) × Option Bool)) ≃ State where
  toFun p := (((p.1, p.2.1.1), p.2.1.2), p.2.2)
  invFun p := (p.1.1.1, ((p.1.1.2, p.1.2), p.2))
  left_inv _ := rfl
  right_inv _ := rfl

end MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody

/-! Actual execution and exact runtime of the fixed dummy-owner program. -/

/-! Bounds on actual metadata, stored rotor words, and emitted prefixes. These
are size estimates used inside separately proved machine executions. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Basic
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

namespace MaxCutGames.Foundations.Complexity.MachineRegularTable

open Turing MachineComposition
open MaxCutGames.Foundations.PCP

namespace Header

inductive Label
  | init | seedM | clearIndex
  | lookup (field : Field) (label : MachinePreservingLookupClean.Label)
  | prefix (label : MachineCloudPrefix.Label)
  | copyFirst (phase : CopyPhase) | copySecond (phase : CopyPhase)
  | add | scaleSeed | scaleScan | scaleRestore
  | appendFirst | appendSecond | appendThird
  | cleanupZeros | clearQuery | done
  deriving DecidableEq, Fintype

def fieldExit : Field → Label
  | .vertices => .seedM
  | .darts => .clearIndex

def copyExit : CopyPhase → Label
  | .count => .add
  | .rEmit => .copyFirst .nEmit
  | .nEmit => .appendFirst

end Header

namespace Top

abbrev State := MachineRegularOriginalBody.State × Option Bool

def headerStates :
    (Header.State Unit × (MachineRegularOriginalBody.CoreState ×
      (MachineRegularOriginalBody.FamilyState × Option Bool))) ≃ State where
  toFun p := (((p.2.1, p.1), p.2.2.1), p.2.2.2)
  invFun p := (p.1.1.2, (p.1.1.1, (p.1.2, p.2)))
  left_inv _ := rfl
  right_inv _ := rfl

def readyState (H : BaseTable) : State := (MachineRegularOriginalBody.readyState H, none)

end Top
end MaxCutGames.Foundations.Complexity.MachineRegularTable

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_PoweringMasterState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit common-register layout for the powering machine. The header,
word and affine routines use the trailing optional-bit register directly.
Comparison reassociates the finite registers; row evaluation moves the fixed
buffer to the final component. The row adapter below proves an actual step
of the caller's mixed program, rather than requiring that the entire program
be a translated copy of the row routine. -/

namespace MaxCutGames.Foundations.Complexity.PoweringMasterState

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

def rowAt {t S q : Nat} (src dst : K)
    (labelAt : Fin q → Fin S → PCP.GraphTables.Label) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (Master (PoweringMachineRow.inputSize t S)) :=
  encodedBlockAt src dst (PoweringMachineRow.rowBlock labelAt) exit

end Row

end MaxCutGames.Foundations.Complexity.PoweringMasterState

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PortTableLookup
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact word offsets in executable port tables

These are optional list-lookup equalities for the unary-word stream consumed by
the lookup machine. They expose the stored tail, reverse index, and predicate
bit at their actual positions in the existing graph-table serialization.
-/

namespace MaxCutGames.Foundations.PCP.PortTableLookup

variable {n d : Nat}

theorem row_word_inline_PortTableLookup (table : PortTables.Table n d) (i : Fin (n * d))
    (j : Nat) (hj : j < 4098) :
    (PortTables.tableWords table)[2 + 4098 * i.val + j]? =
      (GraphTables.rowWords (PortTables.flatRows table)[i])[j]? := by
  rw [PortTables.tableWords_eq]
  change (n :: n * d :: (PortTables.flatRows table).toList.flatMap
    GraphTables.rowWords)[2 + 4098 * i.val + j]? = _
  rw [show 2 + 4098 * i.val + j = (4098 * i.val + j + 1) + 1 by omega,
    List.getElem?_cons_succ, List.getElem?_cons_succ]
  apply flatMap_word_inline_PortTableLookup GraphTables.rowWords 4098 j hj
    (PortTables.flatRows table).toList
    (fun row _ => GraphTables.rowWords_length row) i.val
    ((PortTables.flatRows table)[i])
  simp only [Vector.getElem?_toList, Vector.getElem?_eq_getElem i.isLt,
    Fin.getElem_fin]

/-- The first word of row `i` records the tail vertex. -/
theorem tail_word (table : PortTables.Table n d) (i : Fin (n * d)) :
    (PortTables.tableWords table)[2 + 4098 * i.val]? =
      some (((PortTables.rowIndex n d).symm i).1.val) := by
  have h := row_word_inline_PortTableLookup table i 0 (by decide)
  simpa only [Nat.add_zero, GraphTables.rowWords, PortTables.flatRows,
    Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, List.cons_append,
    List.nil_append, List.getElem?_cons_zero] using h

/-- The second word of row `i` is the actual stored reverse index. -/
theorem reverse_word (table : PortTables.Table n d) (i : Fin (n * d)) :
    (PortTables.tableWords table)[3 + 4098 * i.val]? =
      some (table.reverseIndex[i].val) := by
  have h := row_word_inline_PortTableLookup table i 1 (by decide)
  rw [show 2 + 4098 * i.val + 1 = 3 + 4098 * i.val by omega] at h
  simpa only [GraphTables.rowWords, PortTables.flatRows, Fin.getElem_fin,
    Vector.getElem_ofFn, Fin.eta, List.cons_append, List.nil_append,
    List.getElem?_cons_succ, List.getElem?_cons_zero] using h

/-- Relation position `j` is a stored Boolean, encoded as its zero-or-one word. -/
theorem relation_word (table : PortTables.Table n d) (i : Fin (n * d))
    (j : Fin 4096) :
    (PortTables.tableWords table)[4 + 4098 * i.val + j.val]? =
      some (GraphTables.bitWord table.relations[i][j]) := by
  have h := row_word_inline_PortTableLookup table i (j.val + 2) (by omega)
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

end MaxCutGames.Foundations.PCP.PortTableLookup

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_PoweringMachineRotor
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rotor step on the live unary port-table encoding. First read the reverse
dart identifier; then read that dart's tail vertex. This uses no division or
runtime graph data in finite control. Both positional selections are proved
from the actual serialization. -/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineRotor

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

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

theorem steps_le (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d) :
    steps table vertex port ≤ 14 * (PortTables.tableBits table).length + 12 := by
  have hvertex : vertex.val ≤ (encodeWords (PortTables.tableWords table)).length :=
    Nat.le_trans (Nat.le_of_lt vertex.isLt) (PortTables.vertices_le_tableBits_length table)
  have hreverse := MachineLookupSpec.output_length_le (PortTables.tableWords table)
    (reverseAddress vertex port) (reverseId table vertex port) (reverse_selected table vertex port)
  rw [encodeWord_length] at hreverse
  have hr := MachineAffineLookup.steps_le_table (PortTables.tableWords table)
    vertex.val (4098 * d) (4098 * port.val + 3) (reverseId table vertex port)
    (reverse_selected table vertex port) hvertex
  have he := MachineAffineLookup.steps_le_table (PortTables.tableWords table)
    (reverseId table vertex port) 4098 2 ((PortTables.rotation table (vertex, port)).1.val)
    (endpoint_selected table vertex port) (by omega)
  change _ ≤ 14 * (encodeWords (PortTables.tableWords table)).length + 12
  unfold steps
  omega

end MaxCutGames.Foundations.Complexity.PoweringMachineRotor

/-! Fixed port words are executed by a finite chain of actual rotor programs.
The six shared tapes hold table, query, scan, reverse identifier, scratch and
output. Each walk position has a separate physical vertex tape. The final
unary copy also handles the empty word and preserves the starting vertex. -/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineWord

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

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

theorem steps_le (table : PortTables.Table n d) (t : Nat)
    (vertex : Fin n) (ports : Fin t → Fin d) :
    steps table t vertex ports ≤ (14 * t + 2) * (PortTables.tableBits table).length + 12 * t + 3 := by
  induction t generalizing vertex with
  | zero =>
      have h := Nat.le_trans (Nat.le_of_lt vertex.isLt) (PortTables.vertices_le_tableBits_length table)
      simp only [steps, Nat.mul_zero, Nat.zero_add]
      omega
  | succ t ih =>
      have hr := PoweringMachineRotor.steps_le table vertex (ports 0)
      have ht := ih (PortTables.rotation table (vertex, ports 0)).1 (fun j => ports j.succ)
      simp only [steps, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_assoc] at ht ⊢
      omega

end MaxCutGames.Foundations.Complexity.PoweringMachineWord

/-! A fixed shared tape layout for the actual powering field subroutines.
The vertex identifiers live on physical tapes. The trajectory capacity is
fixed by `max`; each bounded word uses its first `t` trajectory tapes. -/

/-! Actual powering initialization on the common finite tape set. The first
unary input field is copied by the affine machine and consumed by the checked
header program. The original input and every unrelated tape are preserved.
No runtime graph or vertex count is captured by the finite program. -/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineInitialize

open Turing
open PoweringMachineLoop PoweringMasterState

def dropUnit_inline_PoweringMachineInitialize (N : Nat) : (Master N × Unit) ≃ Master N where
  toFun := Prod.fst
  invFun state := (state, ())
  left_inv := by rintro ⟨state, ⟨⟩⟩; rfl
  right_inv := by intro state; rfl

/-- The native checked header statement is embedded and its inert extra
register removed. All four native header tapes keep their identities. -/
def headerStatement (max N B : Nat) (label : HeaderLabel) :
    TM2.Stmt (fun _ : GlobalTape max => Bool) Label (Master N) :=
  MachineStateEquiv.statement (dropUnit_inline_PoweringMachineInitialize N)
    (castStatement_inline_PoweringMachineInitialize (boolAlphabet_eq_inline_PoweringMachineInitialize max)
      (MachineEmbedding.statement (Λextra := MachineUnaryAffineAt.Label)
        (τ := Unit) none (headerProgram (σ := OtherRegisters N) B label)))

def headerConfiguration {max N : Nat} (extra : ExtraTape max → List Bool)
    (c : TM2.Cfg HeaderAlphabet HeaderLabel (Master N)) :
    TM2.Cfg (fun _ : GlobalTape max => Bool) Label (Master N) :=
  ⟨c.l.map Sum.inl, c.var, mergeTapes c.stk extra⟩

theorem headerConfiguration_eq_inline_PoweringMachineInitialize {max N : Nat} (extra : ExtraTape max → List Bool)
    (c : TM2.Cfg HeaderAlphabet HeaderLabel (Master N)) :
    headerConfiguration extra c =
      MachineStateEquiv.configuration (dropUnit_inline_PoweringMachineInitialize N)
        (castConfiguration_inline_PoweringMachineInitialize (boolAlphabet_eq_inline_PoweringMachineInitialize max)
          (MachineEmbedding.configuration (Λextra := MachineUnaryAffineAt.Label)
            none () extra c)) := by
  cases c with
  | mk label state tapes =>
    simp only [MachineEmbedding.configuration, castConfiguration_mk_inline_PoweringMachineInitialize,
      MachineStateEquiv.configuration, castTapes_embedding_inline_PoweringMachineInitialize, dropUnit_inline_PoweringMachineInitialize,
      Equiv.coe_fn_mk, headerConfiguration]
    cases label <;> rfl

theorem stepAux_headerStatement (max N B : Nat) (label : HeaderLabel)
    (state : Master N) (header : HeaderTape → List Bool)
    (extra : ExtraTape max → List Bool) :
    TM2.stepAux (headerStatement max N B label) state (mergeTapes header extra) =
      headerConfiguration extra (TM2.stepAux (headerProgram B label) state header) := by
  rw [headerStatement, MachineStateEquiv.stepAux_transport_symm]
  change MachineStateEquiv.configuration (dropUnit_inline_PoweringMachineInitialize N)
    (TM2.stepAux (castStatement_inline_PoweringMachineInitialize (boolAlphabet_eq_inline_PoweringMachineInitialize max)
      (MachineEmbedding.statement none (headerProgram B label))) (state, ())
      (mergeTapes header extra)) = _
  rw [← castTapes_embedding_inline_PoweringMachineInitialize, stepAux_cast_inline_PoweringMachineInitialize, MachineEmbedding.stepAux_simulation]
  exact (headerConfiguration_eq_inline_PoweringMachineInitialize extra _).symm

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

end MaxCutGames.Foundations.Complexity.PoweringMachineInitialize

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_PoweringMachineRelation
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.PoweringMachineRelation

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

theorem steps_le (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d)
    (position : Fin 4096) :
    MachineAffineLookup.steps (PortTables.tableWords table) vertex.val
      (4098 * d) (4098 * port.val + 4 + position.val) ≤
      7 * (PortTables.tableBits table).length + 6 :=
  MachineAffineLookup.steps_le_table (PortTables.tableWords table) vertex.val
    (4098 * d) (4098 * port.val + 4 + position.val) (value table vertex port position)
    (selected table vertex port position)
    (Nat.le_trans (Nat.le_of_lt vertex.isLt) (PortTables.vertices_le_tableBits_length table))

end MaxCutGames.Foundations.Complexity.PoweringMachineRelation

/-! A concrete relation-field producer: execute a fixed word from the live
start vertex, then read the predicate at the reached vertex and fixed port.
All instructions use the shared tape layout and preserve the finite row
buffer. No execution premise is supplied by the caller. -/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineRelationField

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

end MaxCutGames.Foundations.Complexity.PoweringMachineRelationField

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

namespace MaxCutGames.Foundations.Complexity.PoweringMachineEqualityField

open Turing
open MachineComposition
open PCP

variable {K Λ A : Type} [DecidableEq K]
variable {max l r n d : Nat}

abbrev State := MachineUnaryEqualityBit.State

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

theorem steps_le (graph : PortTables.Table n d) (vertex : Fin n)
    (left : Fin l → Fin d) (right : Fin r → Fin d) :
    steps graph vertex left right ≤
      (14 * (l + r) + 10) * (PortTables.tableBits graph).length + 12 * (l + r) + 15 := by
  have hl := PoweringMachineWord.steps_le graph l vertex left
  have hr := PoweringMachineWord.steps_le graph r vertex right
  have he := MachineUnaryEqualityBit.steps_le
    (endpoint graph vertex left).val (endpoint graph vertex right).val
  have hleft := Nat.le_trans (Nat.le_of_lt (endpoint graph vertex left).isLt)
    (PortTables.vertices_le_tableBits_length graph)
  have hright := Nat.le_trans (Nat.le_of_lt (endpoint graph vertex right).isLt)
    (PortTables.vertices_le_tableBits_length graph)
  unfold steps
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc] at hl hr ⊢
  omega

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

end MaxCutGames.Foundations.Complexity.PoweringMachineEqualityField

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PoweringRowData
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineField.labelDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineField.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

namespace MaxCutGames.Foundations.PCP.PoweringRowData

open MaxCutGames.Foundations.Complexity
open Turing
open PoweringMachineRow MachineFixedBlockMap
open PoweringWalks PoweringLabels PoweringAddresses PoweringReach
open PoweringOpinionTables PoweringEnumeration

variable {vertices d : Nat}

/-- An actual endpoint comparison; it has no reachability oracle input. -/
def endpointMask (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center target : Fin vertices) (i : AddressIndex d t) : Bool :=
  decide ((wordToBall G t center ((allAddresses d t).get i)).val = target)

theorem firstMatch_endpointMask (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) :
    firstMatch (endpointMask G t center u.val) = some (addressIndex G t center u) := by
  unfold endpointMask addressIndex
  exact firstMatch_firstIndex
    (fun w : PortWords (Fin d) t => (wordToBall G t center w).val = u.val)
    (allAddresses d t) (by
      obtain ⟨w, hw⟩ := wordToBall_surjective G t center u
      exact ⟨w, mem_allAddresses d t w, congrArg Subtype.val hw⟩)

def slotCount (d n : Nat) : Nat := (allAddresses d (n + 1)).length

abbrev RowBuffer (d n : Nat) := Buffer (inputSize (n + 1) (slotCount d n))

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

/-- For each actual path edge, store its complete base relation, then the
start-to-tail mask, then the end-to-head mask. Every bit is computed. -/
def walkData (input : PortTables.Table vertices d) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1))
    (k : Fin (n + 1)) : Field (slotCount d n) → Bool
  | .inl (a, b) => PortTables.accepts input (edgeAt (PortTables.portGraph input) n w k) a b
  | .inr (.inl i) => endpointMask (PortTables.portGraph input) (n + 1) w.1
      (edgeAt (PortTables.portGraph input) n w k).1 i
  | .inr (.inr i) => endpointMask (PortTables.portGraph input) (n + 1)
      (endpoint (PortTables.portGraph input) w)
      ((PortTables.portGraph input).rot (edgeAt (PortTables.portGraph input) n w k)).1 i

def walkBits (input : PortTables.Table vertices d) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) : RowBuffer d n :=
  packData (walkData input n w)

@[simp] theorem basePredicate_walkBits (input : PortTables.Table vertices d) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1))
    (a b : GraphTables.Label) :
    basePredicate (walkBits input n w) k a b =
      PortTables.accepts input (edgeAt (PortTables.portGraph input) n w k) a b := by
  simp [basePredicate, walkBits, walkData]

@[simp] theorem leftMatches_walkBits (input : PortTables.Table vertices d) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1)) :
    leftMatches (walkBits input n w) k = endpointMask (PortTables.portGraph input)
      (n + 1) w.1 (edgeAt (PortTables.portGraph input) n w k).1 := by
  funext i
  simp [leftMatches, walkBits, walkData]

@[simp] theorem rightMatches_walkBits (input : PortTables.Table vertices d) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1)) :
    rightMatches (walkBits input n w) k = endpointMask (PortTables.portGraph input)
      (n + 1) (endpoint (PortTables.portGraph input) w)
      ((PortTables.portGraph input).rot (edgeAt (PortTables.portGraph input) n w k)).1 := by
  funext i
  simp [rightMatches, walkBits, walkData]

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

/-- Reverse orientation exchanges the two mask fields and label arguments. -/
def transposeField {S : Nat} : Field S → Field S
  | .inl (a, b) => .inl (b, a)
  | .inr (.inl i) => .inr (.inr i)
  | .inr (.inr i) => .inr (.inl i)

def transposeBits {t S : Nat} (bits : Buffer (inputSize t S)) : Buffer (inputSize t S) :=
  packData fun k field => bits (inputEquiv t S (k, transposeField field))

@[simp] theorem basePredicate_transposeBits {t S : Nat}
    (bits : Buffer (inputSize t S)) (k : Fin t) (a b : GraphTables.Label) :
    basePredicate (transposeBits bits) k a b = basePredicate bits k b a := by
  simp [basePredicate, transposeBits, transposeField]

@[simp] theorem leftMatches_transposeBits {t S : Nat}
    (bits : Buffer (inputSize t S)) (k : Fin t) :
    leftMatches (transposeBits bits) k = rightMatches bits k := by
  funext i
  simp [leftMatches, rightMatches, transposeBits, transposeField]

@[simp] theorem rightMatches_transposeBits {t S : Nat}
    (bits : Buffer (inputSize t S)) (k : Fin t) :
    rightMatches (transposeBits bits) k = leftMatches bits k := by
  funext i
  simp [leftMatches, rightMatches, transposeBits, transposeField]

theorem edgeAccept_transposeBits {t S q : Nat}
    (labelAt : Fin q → Fin S → GraphTables.Label)
    (bits : Buffer (inputSize t S)) (k : Fin t) (a b : Fin q) :
    edgeAccept labelAt (transposeBits bits) k a b = edgeAccept labelAt bits k b a := by
  simp only [edgeAccept, leftMatches_transposeBits, rightMatches_transposeBits]
  cases hl : firstMatch (leftMatches bits k) <;>
    cases hr : firstMatch (rightMatches bits k) <;>
    simp []

theorem rowAccept_transposeBits {t S q : Nat}
    (labelAt : Fin q → Fin S → GraphTables.Label)
    (bits : Buffer (inputSize t S)) (a b : Fin q) :
    rowAccept labelAt (transposeBits bits) a b = rowAccept labelAt bits b a := by
  apply Bool.eq_iff_iff.mpr
  simp only [rowAccept_eq_true, edgeAccept_transposeBits]

/-- The fully specified data block for either directed occurrence. -/
def rowBits (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) : RowBuffer d n :=
  if e.1 then transposeBits (walkBits input n e.2) else walkBits input n e.2

def rowData (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n)
    (k : Fin (n + 1)) (field : Field (slotCount d n)) : Bool :=
  walkData input n e.2 k (if e.1 then transposeField field else field)

theorem rowBits_packData (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) :
    rowBits input n e = packData (rowData input n e) := by
  rcases e with ⟨direction, w⟩
  cases direction <;> funext i <;>
    simp [rowBits, rowData, transposeBits, walkBits, packData]

@[simp] theorem rowBits_field (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n)
    (k : Fin (n + 1)) (field : Field (slotCount d n)) :
    rowBits input n e (inputEquiv (n + 1) (slotCount d n) (k, field)) =
      rowData input n e k field := by
  rw [rowBits_packData, packData_inputEquiv]

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

/-! ## Exact field and emitted-relation serialization -/

def dataWords (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) : List Nat :=
  (List.ofFn (rowBits input n e)).map GraphTables.bitWord

def dataTape (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) : List Bool :=
  encodeWords (dataWords input n e)

def emittedRelation (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) :
    GenericGraphTables.RelationTable (PoweringTables.labelCount d n) :=
  Vector.ofFn (rowBlock (fixedLabelAt d n) (rowBits input n e))

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

end MaxCutGames.Foundations.PCP.PoweringRowData

/-! A fixed powered-row data block is reduced to two concrete instruction
forms: follow a fixed port word and read one stored predicate entry, or follow
two fixed words and compare their endpoint identifiers. The plan depends only
on the fixed degree, radius, word and orientation. Its interpretation is exactly
the data block consumed by the checked row transducer. -/

namespace MaxCutGames.Foundations.PCP.PoweringFieldPlan

open PoweringWalks PoweringLabels PoweringAddresses PoweringReach PoweringRowData
open MaxCutGames.Foundations.Complexity PoweringMachineRow

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

def addressPorts {d t : Nat} (i : PoweringOpinionTables.AddressIndex d t) : List (Fin d) :=
  List.ofFn ((allAddresses d t).get i).2

theorem walkEnd_addressPorts {d t : Nat} (G : PortGraph V (Fin d)) (v : V)
    (i : PoweringOpinionTables.AddressIndex d t) :
    walkEnd G v (addressPorts i) = (wordToBall G t v ((allAddresses d t).get i)).val :=
  (wordEnd_eq_walkEnd_ofFn G _ _ _).symm

theorem addressPorts_length_le {d t : Nat} (i : PoweringOpinionTables.AddressIndex d t) :
    (addressPorts i).length ≤ t := by
  simp only [addressPorts, List.length_ofFn]
  exact Nat.le_of_lt_succ ((allAddresses d t).get i).1.isLt

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

end MaxCutGames.Foundations.PCP.PoweringFieldPlan

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_PoweringMachineField
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.PoweringMachineField

open Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {n d max : Nat}

abbrev State := MachineUnaryEqualityBit.State

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

end MaxCutGames.Foundations.Complexity.PoweringMachineField

/-! The concrete finite program that produces an entire powered-row input
block. Its static control executes the field plan backwards, so prepending each
computed unary Boolean field leaves the canonical serialized block in order. -/

namespace MaxCutGames.Foundations.Complexity.PoweringMachinePlan

open Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {vertices d max : Nat}

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

end MaxCutGames.Foundations.Complexity.PoweringMachinePlan

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_PoweringPlanBudget
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

namespace MaxCutGames.Foundations.Complexity.PoweringPlanBudget

open Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {vertices d max : Nat}

/-- This is the actual static instruction list's length, not a supplied bound. -/
@[simp] theorem boundedRowPlan_length (n : Nat)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    (PoweringMachinePlan.boundedRowPlan n ports direction).length =
      PoweringMachineRow.inputSize (n + 1) (PoweringRowData.slotCount d n) := by
  simp only [PoweringMachinePlan.boundedRowPlan, List.length_ofFn]

end MaxCutGames.Foundations.Complexity.PoweringPlanBudget

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PoweringRowHeaderSemantics
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact tail and reverse-index fields of the actual powering-table rows.
The reverse address is affine in the live starting vertex; the coefficient
and offset depend only on the fixed degree, word, and orientation. -/

namespace MaxCutGames.Foundations.PCP.PoweringRowHeaderSemantics

open PoweringWalks PoweringEnumeration
open MaxCutGames.Foundations.Complexity

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

end MaxCutGames.Foundations.PCP.PoweringRowHeaderSemantics

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_PoweringMachineRowHeaders
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.PoweringMachineRowHeaders

open Turing MachineComposition
open PCP PoweringRowHeaderSemantics
open PoweringMachineTapes

variable {K Λ σ : Type} [DecidableEq K]
variable {vertices d max : Nat}

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

end MaxCutGames.Foundations.Complexity.PoweringMachineRowHeaders

namespace MaxCutGames.Foundations.Complexity.PoweringMachineRowBody

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

theorem plan_other_inline_PoweringMachineRowBody {max : Nat} (graph : PortTables.Table vertices d)
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
    _ = base k := plan_other_inline_PoweringMachineRowBody graph placement vertex _ base k outside

end MaxCutGames.Foundations.Complexity.PoweringMachineRowBody

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PoweringTableLayout
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

namespace MaxCutGames.Foundations.PCP.PoweringTableLayout

open MaxCutGames.Foundations.Complexity
open PoweringTables PoweringEnumeration

theorem dartCount_eq_vertex_blocks (vertices d n : Nat) :
    dartCount vertices d n = vertices * blockSize d n := by
  unfold dartCount
  simp only [blockSize]
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

end MaxCutGames.Foundations.PCP.PoweringTableLayout

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_PoweringMachineVertex
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.PoweringMachineVertex

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

theorem encodeWords_flatMap_inline_PoweringMachineVertex {X : Type*} (xs : List X) (f : X → List Nat) :
    encodeWords (xs.flatMap f) = xs.flatMap (fun x => encodeWords (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

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
      rw [encodeWords_flatMap_inline_PoweringMachineVertex]
      erw [← hrows, List.flatMap_map]
      rfl

end MaxCutGames.Foundations.Complexity.PoweringMachineVertex

/-! Actual variable-size vertex enumeration. The finite guard decrements the
live unary counter, a one-step bridge enters the fixed vertex producer, and the
producer returns to the guard. Work tapes may change after every vertex. -/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineOuterLoop

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

end MaxCutGames.Foundations.Complexity.PoweringMachineOuterLoop

/-!
# Physical output headers followed by complete work-tape cleanup

The finite program first copies the dart-count word onto the existing row
output, then copies the vertex-count word, and finally drains every tape except
the output. Both unary header values are read from physical tapes; they do not
parameterize the program. Header sources and their unread suffixes are restored
by the two copies before cleanup. The final configuration contains the full
encoded header and rows on the output tape and empty words on every other tape.
-/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineFinish

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K] {N : Nat}

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

end MaxCutGames.Foundations.Complexity.PoweringMachineFinish

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_PoweringMachineGlobal
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The fixed global powering machine

For fixed degree `d` and radius parameter `n`, this is one concrete finite
machine: initialization, unary vertex guard, the fixed vertex-row producer,
and output-header/cleanup instructions are connected by explicit labels.
Its definition takes no input graph, vertex count, or program callback.

The code equations below expose each actual branch for the separate runtime
proof. The variable-size input graph and counters reside on physical tapes.
-/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineGlobal

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

end MaxCutGames.Foundations.Complexity.PoweringMachineGlobal

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_RawInitialTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit structural numberings of the raw 3SAT incidence graph. Unused
declared variable names are retained; their unary input header pays for them.
The graph has one dummy vertex and one tautological loop, even for an empty
formula. No input-dependent choice of a finite enumeration is made. -/

namespace MaxCutGames.Foundations.PCP.RawInitialTables

open Target GraphTables

theorem table_darts_positive (F : Formula) : 0 < (table F).darts := by
  rw [table_darts]; omega

theorem initial_size (F : Formula) :
    (table F).vertices + (table F).darts = F.«variables» + 7 * F.clauses.length + 2 := by
  rw [table_vertices, table_darts]
  omega

end MaxCutGames.Foundations.PCP.RawInitialTables

/-!
A stable type of finite graphs over one fixed alphabet. Vertex and dart types,
their finite enumeration and equality data, and the actual constraint graph
are stored together. The gap is computed from that graph's actual finite
labeling minimum. This mathematical bundle is not a serialized machine input;
no finite numbering is chosen here.
-/

/-! The concrete numbered amplification round, with one fixed base expander.
Every intermediate is an actual stored table, with explicit finite coordinates.
The running-time certificate is a separate theorem about these same functions. -/

/-!
The finite iteration and size arithmetic for an amplification transformation.
The transformation itself must be supplied by the actual graph construction;
these theorems do not assert that such a transformation exists.  In particular,
the polynomial size estimate below is not a machine runtime certificate.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_RawInitialMachineBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial arithmetic for the actual initial-machine phase counts. The
separate execution theorem must connect these counts to the concrete program. -/

namespace MaxCutGames.Foundations.PCP.RawInitialMachineBudget

open Target Complexity

def nameSum {n : Nat} (c : Clause n) : Nat :=
  (c)[0].variableIndex.val + (c)[1].variableIndex.val + (c)[2].variableIndex.val

def bodyTime {n : Nat} (i : Nat) (c : Clause n) : Nat :=
  6 * n + 18 * i + 2 * nameSum c +
    2 * (encodeWords (Complexity.clauseWords c)).length + 63

def loopTime {n : Nat} (i : Nat) : List (Clause n) → Nat
  | [] => 1
  | c :: cs => bodyTime i c + loopTime (i + 1) cs

theorem nameSum_le {n : Nat} (c : Clause n) : nameSum c ≤ 3 * n := by
  have h0 := (c)[0].variableIndex.isLt
  have h1 := (c)[1].variableIndex.isLt
  have h2 := (c)[2].variableIndex.isLt
  unfold nameSum
  omega

theorem bodyTime_le {n : Nat} (i : Nat) (c : Clause n) :
    bodyTime i c ≤ 18 * n + 18 * i + 81 := by
  have hn := nameSum_le c
  have hb := clauseBits_length_le c
  unfold bodyTime
  omega

theorem loopTime_le {n : Nat} (i : Nat) (cs : List (Clause n)) :
    loopTime i cs ≤ cs.length * (18 * n + 18 * (i + cs.length) + 81) + 1 := by
  induction cs generalizing i with
  | nil => simp [loopTime]
  | cons c cs ih =>
      have hc := bodyTime_le i c
      have ht := ih (i + 1)
      have hbound : bodyTime i c ≤ 18 * n + 18 * (i + (c :: cs).length) + 81 := by
        simp only [List.length_cons]
        omega
      have hsame : 18 * n + 18 * (i + 1 + cs.length) + 81 =
          18 * n + 18 * (i + (c :: cs).length) + 81 := by
        simp only [List.length_cons]
        omega
      rw [hsame] at ht
      rw [loopTime]
      calc
        _ ≤ (18 * n + 18 * (i + (c :: cs).length) + 81) +
            (cs.length * (18 * n + 18 * (i + (c :: cs).length) + 81) + 1) :=
          Nat.add_le_add hbound ht
        _ = _ := by rw [List.length_cons]; ring

theorem input_header_bound (F : Formula) :
    F.«variables» + F.clauses.length + 2 ≤ (formulaBits F).length := by
  simp only [formulaBits, formulaWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

theorem graph_size_bound (F : Formula) :
    (RawInitialTables.table F).vertices + (RawInitialTables.table F).darts ≤
      7 * (formulaBits F).length := by
  rw [RawInitialTables.initial_size]
  have h := input_header_bound F
  omega

def fullBudget (F : Formula) : Nat :=
  6 * F.«variables» + 10 * F.clauses.length + 30 + loopTime 0 F.clauses +
    (GraphTables.tableBits (RawInitialTables.table F)).length

end MaxCutGames.Foundations.PCP.RawInitialMachineBudget

end OAI
end


