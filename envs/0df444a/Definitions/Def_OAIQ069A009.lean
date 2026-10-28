-- Prove2me | Definitions.Def_OAIQ069A009
-- name    : OAIQ069A009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:00:42.233389+00:00
-- url     : https://prove2.me/theorems/e14a7063-66e6-42f2-a3d3-a56876aec38c
-- title:
--   Definitions bundle OAIQ069A009 of the split of OpenAI, Hardness of finding large independent sets in three-colorable graphs (result family 106)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LargeIndependentSets.mainTheoremReal`, carved from OpenAI's openai/math development (OpenAI, *Hardness of finding large independent sets in three-colorable graphs (result family 106)*, OpenAI Math Release, September 24, 2026, result family 106, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 153 declarations of OpenAI's Lean: 63 definitions, 4 inductive types or structures and 86 theorems. The definitions and types are `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Addresses.eventVertexField`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Addresses.fieldForDartTail`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Addresses.fieldForQueryEvent`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Addresses.headerDarts`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Addresses.headerVertices`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Addresses.rawQueryField`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Body.RowStepResult`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Body.clearFieldsInTime`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Body.clearFieldsTapes`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Body.emitInTime`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Body.emittedTapes`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Body.guardTapes`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Body.incrementInTime`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Body.parsedTapes`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Body.resultTapes`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Body.workingTapes`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.CompareLoop.compareInTime`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.CompareLoop.compareRowInTime`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.CompareLoop.compareWordsInTime`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Driver.machine`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.EmitRows.blockInTimeAmbient`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.EmitRows.headerInTime`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Finish.afterReversal`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Finish.cleanupInTime`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Finish.completedPolynomial`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Finish.finishAfterPolynomialPrefix`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Finish.finishAfterPrefix`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Finish.finishBudget`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Finish.finishInTime`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Finish.reverseInTime`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Initialization.headerInTime`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Initialization.initializeInTime`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Initialization.inputTapes`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Initialization.loopStart`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Initialization.loopTapes`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Initialization.setupInTime`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Initialization.setupTapes`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Loop.LoopResult`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Loop.PrefixResult`, `OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Loop.zeroGuardInTime` and 27 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `IndependentSets_Encoding_TargetLCExpr`, `IndependentSets_Expansion_PoweringFieldPlan`, `IndependentSets_Expansion_PoweringRowData`, `IndependentSets_Expansion_PoweringTables`, `IndependentSets_Expansion_PreprocessingTables`, `IndependentSets_Expansion_RoundComputation`, `IndependentSets_Machines_Initialization`, `IndependentSets_Machines_MachineControl`, `IndependentSets_Machines_Runtime`, `IndependentSets_Machines_TargetLCMachine`, `IndependentSets_Main`, `IndependentSets_PCP_Addresses`, `IndependentSets_PCP_Body`, `IndependentSets_PCP_CompareLoop`, `IndependentSets_PCP_Driver`, `IndependentSets_PCP_EmitRows`, `IndependentSets_PCP_Finish`, `IndependentSets_PCP_LoopInitialization`, `IndependentSets_Reduction_TargetRead`.
--
--   **Imports.** It imports the published bundle `Def_IndependentSets`; the bundles `OAIQ069A006` and `OAIQ069A007` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ069A010`.
-- source:
--   OpenAI, Hardness of finding large independent sets in three-colorable graphs (result family 106), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 106; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Hardness-of-finding-large-independent-sets-in-three-colorable-graphs-September-24-2026/Hardness-of-finding-large-independent-sets-in-three-colorable-graphs-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 1581d4c

import Mathlib
import Definitions.Def_IndependentSets
import Definitions.Def_OAIQ069A006
import Definitions.Def_OAIQ069A007

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_PoweringTables
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PoweringTables

open PoweringWalks PoweringLabels PoweringAddresses PoweringEnumeration

def transform (d n : Nat) (input : PortTables.Input d) : GenericGraphTables.Table (labelCount d n) :=
  table input.2 n

end IndependentSetsGames.Foundations.PCP.PoweringTables

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_PreprocessingTables
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PreprocessingTables

open PreprocessingRegularTables

def output (H : BaseTable) (t : GraphTables.Table) : PortTables.Input degree :=
  ⟨vertices t, preprocess H t⟩

end IndependentSetsGames.Foundations.PCP.PreprocessingTables

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_MachineControl
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.RuntimeModel

open Turing
open IndependentSetsGames.Foundations.Complexity

variable {Λ : Type} {q : Nat}

theorem stepAux_storeLoop (value : Bool) (next : Λ) (state : State q)
    (base : Tape → List Bool) :
    TM2.stepAux (storeLoop value next) state base =
      ⟨some next, normal state.1.2 value, base⟩ := rfl

theorem stepAux_nextRow (next : Λ) (state : State q)
    (base : Tape → List Bool) (edge : Nat) (suffix : List Bool)
    (he : base .edge = encodeWord edge ++ suffix) :
    TM2.stepAux (nextRow next) state base =
      ⟨some next, (state.1, none),
        Function.update base .edge (encodeWord (edge + 1) ++ suffix)⟩ := by
  simp [nextRow, TM2.stepAux, he, encodeWord, List.replicate_succ]

end IndependentSetsGames.Foundations.PCP.AlphabetTable.RuntimeModel

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_PoweringRowData
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PoweringRowData

open IndependentSetsGames.Foundations.Complexity
open Turing
open PoweringMachineRow MachineFixedBlockMap
open PoweringWalks PoweringLabels PoweringAddresses PoweringReach
open PoweringOpinionTables PoweringEnumeration

variable {vertices d : Nat}

theorem firstMatch_endpointMask (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) :
    firstMatch (endpointMask G t center u.val) = some (addressIndex G t center u) := by
  unfold endpointMask addressIndex
  exact firstMatch_firstIndex
    (fun w : PortWords (Fin d) t => (wordToBall G t center w).val = u.val)
    (allAddresses d t) (by
      obtain ⟨w, hw⟩ := wordToBall_surjective G t center u
      exact ⟨w, mem_allAddresses d t w, congrArg Subtype.val hw⟩)

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

theorem edgeAccept_transposeBits {t S q : Nat}
    (labelAt : Fin q → Fin S → GraphTables.Label)
    (bits : Buffer (inputSize t S)) (k : Fin t) (a b : Fin q) :
    edgeAccept labelAt (transposeBits bits) k a b = edgeAccept labelAt bits k b a := by
  simp only [edgeAccept, leftMatches_transposeBits, rightMatches_transposeBits]
  cases firstMatch (leftMatches bits k) <;>
    cases firstMatch (rightMatches bits k) <;>
    simp

theorem rowAccept_transposeBits {t S q : Nat}
    (labelAt : Fin q → Fin S → GraphTables.Label)
    (bits : Buffer (inputSize t S)) (a b : Fin q) :
    rowAccept labelAt (transposeBits bits) a b = rowAccept labelAt bits b a := by
  apply Bool.eq_iff_iff.mpr
  simp only [rowAccept_eq_true, edgeAccept_transposeBits]

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

end IndependentSetsGames.Foundations.PCP.PoweringRowData

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_PoweringFieldPlan
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PoweringFieldPlan

open PoweringWalks PoweringLabels PoweringAddresses PoweringReach PoweringRowData
open IndependentSetsGames.Foundations.Complexity PoweringMachineRow

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

end IndependentSetsGames.Foundations.PCP.PoweringFieldPlan

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_CompareLoop
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.CompareLoop

open Turing
open IndependentSetsGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat} {Λ : Type}

theorem compareProgram_at
    (program : Λ → TM2.Stmt Alphabet Λ (State q)) (label : Λ)
    (stmt : TM2.Stmt Alphabet Λ
      (MachineCompare.State (GenericGraphTables.RelationTable q × Bool)))
    (atLabel : program label = compareStatement stmt) :
    (MachineControl.program (Equiv.refl Λ) (compareEquiv q) program) label = stmt := by
  change MachineControl.statement id (compareEquiv q) (program label) = stmt
  rw [atLabel]
  exact MachineFieldProfile.statement_roundtrip (compareEquiv q) stmt

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

end IndependentSetsGames.Foundations.PCP.AlphabetTable.CompareLoop

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_Addresses
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Addresses

open IndependentSetsGames.Foundations.Hastad
open Enumeration

def headerVertices (q : Nat) : Field (fieldBound q) :=
  ⟨[(0, tapeCount q), (1, localCount q + pairTapeCount q)], zeroOffset q⟩

def headerDarts (q : Nat) : Field (fieldBound q) :=
  ⟨[(1, 12 * localCount q)], zeroOffset q⟩

def eventVertexField (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q)) :
    Field (fieldBound q) :=
  ⟨[(2, localCount q)], eventOffset q event⟩

def rawQueryField (q : Nat) (query : Queries.RawQuery q) : Field (fieldBound q) :=
  ⟨rawQueryTerms q query, rawQueryOffset q query⟩

theorem headerVertices_eval (q n m edge tail head : Nat) :
    eval (headerVertices q) (values n m edge tail head) = vertexCount n m q := by
  simp [eval, headerVertices, values, zeroOffset, Emitter.affineValue,
    vertexCount, eventCount, addressCount, Nat.mul_add,
    Nat.mul_comm, Nat.add_comm, Nat.add_assoc]

theorem headerDarts_eval (q n m edge tail head : Nat) :
    eval (headerDarts q) (values n m edge tail head) = dartCount m q := by
  simp [eval, headerDarts, values, zeroOffset, Emitter.affineValue,
    dartCount, eventCount, Nat.mul_comm, Nat.mul_assoc]

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

theorem rawQueryTerms_query (q : Nat) (P : Fin q → Fin q → Bool)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) :
    rawQueryTerms q (Queries.query P event slot) = queryEventTerms q event slot := by
  rcases event with ⟨kind, ⟨side, tape⟩, f, g, r₀, r₁, r₂⟩
  by_cases hk₀ : kind = 0 <;> by_cases hk₁ : kind = 1 <;> by_cases hk₂ : kind = 2 <;>
    simp only [queryEventTerms, Queries.query, hk₀, hk₁, hk₂, ite_true, ite_false]
  all_goals split_ifs <;> rfl

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

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Addresses

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_EmitRows
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.EmitRows

open Turing
open IndependentSetsGames.Foundations.Complexity
open Emitter

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

theorem blockCommandsIn_bits {σ : Type} {q : Nat}
    (input : GenericGraphTables.Table q) (edge : Fin input.darts)
    (context : σ → Context q) (ambient : σ) (hcontext : context ambient = rowContext input edge) :
    (blockCommandsIn q context).flatMap (commandBits (rowValues input edge) ambient) =
      encodeWords (blockWords input edge) := by
  simp only [blockCommandsIn, List.flatMap_map, commandBits_mapAmbient]
  rw [hcontext]
  exact blockCommands_bits input edge

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

end IndependentSetsGames.Foundations.PCP.AlphabetTable.EmitRows

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_Driver
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Driver

open Turing
open IndependentSetsGames.Foundations.Complexity
open IndependentSetsGames.Foundations.Hastad
open RuntimeModel

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

@[simp] theorem program_headLookup (q : Nat) (label : Lookup.Label) :
    program q (.headLookup label) = Lookup.statement q .indexScan .scan .head
      Label.headLookup (some (.compare .leftFirst)) label := rfl

@[simp] theorem program_compare (q : Nat) (label : CompareLoop.Label) :
    program q (.compare label) = CompareLoop.statement Label.compare (rowEntry q) label := rfl

@[simp] theorem program_increment (q : Nat) : program q .increment = nextRow .guard := rfl

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Driver
namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.LoopState

open IndependentSetsGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

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

end IndependentSetsGames.Foundations.PCP.AlphabetTable.LoopState

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_Finish
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Finish

open Turing
open IndependentSetsGames.Foundations.Complexity
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

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Finish

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_Initialization
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Initialization

open Turing
open IndependentSetsGames.Foundations.Complexity
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

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Initialization

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_Body
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Body

open Turing
open IndependentSetsGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

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

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Body

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_LoopInitialization
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.LoopInitialization

open IndependentSetsGames.Foundations.Complexity
open RuntimeModel LoopState

theorem initialization_ready {q : Nat} (input : GenericGraphTables.Table q) :
    Ready input 0 (Initialization.loopTapes input) where
  le_darts := Nat.zero_le _
  original := rfl
  cursor := by
    change Initialization.rowsBits input = cursorBits input 0
    rw [cursorBits_zero]
    rfl
  vertices := rfl
  darts := rfl
  counter := by simp [Initialization.loopTapes]
  edge := rfl
  tail := rfl
  reverseIndex := rfl
  head := rfl
  scratch := rfl
  compareLeft := rfl
  compareRight := rfl
  output := rfl
  reversed := by
    change (Initialization.headerBits input).reverse = (prefixBits input 0).reverse
    rw [prefixBits_zero]
    rfl

end IndependentSetsGames.Foundations.PCP.AlphabetTable.LoopInitialization
namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Loop

open Turing
open IndependentSetsGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

def zeroGuardInTime (input : GenericGraphTables.Table q) (base : Tape → List Bool)
    (ready : LoopState.Ready input input.darts base)
    (relation : GenericGraphTables.RelationTable q) (flag : Bool) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some .guard, normal relation flag, base⟩
      (some ⟨some .reverseOutput, normal relation flag, base⟩) 1 := by
  have counterSelf : MachineUnaryCounter.counterTapes Tape.counter base 0 [] = base := by
    simp only [MachineUnaryCounter.counterTapes, List.append_nil,
      ← ready.counter_at_end, Function.update_eq_self]
  have run := MachineUnaryCounter.guardInTime_zero Tape.counter
    (Driver.Label.guard : Driver.Label q) .tailStart .reverseOutput
    (Driver.program q) (Driver.program_guard q) base [] (normal relation flag).1 none
  simpa only [counterSelf, normal] using run

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

structure PrefixResult (input : GenericGraphTables.Table q) where
  tapes : Tape → List Bool
  relation : GenericGraphTables.RelationTable q
  flag : Bool
  ready : LoopState.Ready input input.darts tapes
  run : StateTransition.EvalsToInTime (TM2.step (Driver.program q))
    (initList (Driver.machine q) (GenericGraphTables.tableBits input))
    (some ⟨some .reverseOutput, normal relation flag, tapes⟩)
    (prefixTime q (LoopState.inputBits input).length)

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Loop

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_Runtime
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Runtime

open Turing
open IndependentSetsGames.Foundations.Complexity
open RuntimeModel

noncomputable def time (q : Nat) : Polynomial Nat :=
  Finish.completedPolynomial q (prefixPolynomial q)

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Runtime

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_TargetRead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace LargeIndependentSets.TargetRead
open IndependentSetsGames.Foundations IndependentSetsGames.Foundations.Complexity
open IndependentSetsCut.CounterMachine
open Target PCP Hastad.SourceContexts Hastad.SourceGame
open scoped Classical BigOperators

lemma encodeWords_eq (xs : List ℕ) : encodeWords xs=Expr.unaryWords xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeWords,encodeWord,Expr.unaryWords,ih]

lemma read (F : Target.Formula) (w : ℕ) :
    Expr.wordValue (Complexity.formulaBits F) w=((formulaWords F)[w]?).getD 0 := by
  rw [Complexity.formulaBits,encodeWords_eq,Expr.wordValue_encoded]

lemma read_vars (F : Target.Formula) : Expr.wordValue (Complexity.formulaBits F) 0=F.«variables» := by
  rw [read]; simp [formulaWords]
lemma read_clauses (F : Target.Formula) : Expr.wordValue (Complexity.formulaBits F) 1=F.clauses.length := by
  rw [read]; simp [formulaWords]

lemma read_clause (F : Target.Formula) (c : Fin F.clauses.length) (j : Fin 6) :
    Expr.wordValue (Complexity.formulaBits F) (2+6*c.val+j.val)=
      ((clauseWords (clauseAt F c))[j.val]?).getD 0 := by
  rw [read,formulaWords,List.getElem?_append_right (by simp; omega)]
  simp only [List.length_cons,List.length_nil]
  rw [show 2+6*c.val+j.val-2=6*c.val+j.val by omega]
  exact block_get 0 clauseWords 6 clauseWords_length F.clauses c j.val j.isLt

lemma read_name (F : Target.Formula) (c : Fin F.clauses.length) (s : Slot) :
    Expr.wordValue (Complexity.formulaBits F) (2+6*c.val+2*(RawInitialTables.slotOrder s).val)=
      (nameAt (clauseAt F c) s).val := by
  have h := read_clause F c ⟨2*(RawInitialTables.slotOrder s).val,by have := (RawInitialTables.slotOrder s).isLt; omega⟩
  cases s <;> simpa [RawInitialTables.slotOrder,clauseWords,literalWords,nameAt] using h

lemma read_sign (F : Target.Formula) (c : Fin F.clauses.length) (s : Slot) :
    Expr.wordValue (Complexity.formulaBits F) (2+6*c.val+(2*(RawInitialTables.slotOrder s).val+1))=
      (if signAt (clauseAt F c) s then 1 else 0) := by
  have h := read_clause F c ⟨2*(RawInitialTables.slotOrder s).val+1,by have := (RawInitialTables.slotOrder s).isLt; omega⟩
  cases s <;> convert h using 1 <;> simp [RawInitialTables.slotOrder,clauseWords,literalWords,signAt] <;> rfl

@[simp] lemma varsExpr_eval (F : Target.Formula) (a : ℕ → ℕ) :
    varsExpr.eval (Complexity.formulaBits F) a=F.«variables» := by simp [varsExpr,Expr.eval,read_vars]
@[simp] lemma clausesExpr_eval (F : Target.Formula) (a : ℕ → ℕ) :
    clausesExpr.eval (Complexity.formulaBits F) a=F.clauses.length := by simp [clausesExpr,Expr.eval,read_clauses]
lemma nameExpr_eval (F : Target.Formula) (c : Expr) (a : ℕ → ℕ) (i : Fin F.clauses.length)
    (hi : c.eval (Complexity.formulaBits F) a=i.val) (s : Slot) :
    (nameExpr c s).eval (Complexity.formulaBits F) a=(nameAt (clauseAt F i) s).val := by
  simp only [nameExpr,Expr.word_eval,Expr.eval,hi,read_name]
lemma signExpr_eval (F : Target.Formula) (c : Expr) (a : ℕ → ℕ) (i : Fin F.clauses.length)
    (hi : c.eval (Complexity.formulaBits F) a=i.val) (s : Slot) :
    (signExpr c s).eval (Complexity.formulaBits F) a=if signAt (clauseAt F i) s then 1 else 0 := by
  simp only [signExpr,Expr.word_eval,Expr.eval,hi,read_sign]

end LargeIndependentSets.TargetRead
namespace LargeIndependentSets.TargetRepair
open IndependentSetsGames.Foundations IndependentSetsGames.Foundations.Complexity
open IndependentSetsCut.CounterMachine
open Target PCP Hastad.SourceContexts Hastad.SourceGame
open TargetRead
open scoped Classical BigOperators

def shape {n : ℕ} (cl : Target.Clause n) : Shape :=
  (signAt cl,fun s t => decide (nameAt cl s=nameAt cl t))

lemma shapeSat_exact {n : ℕ} (cl : Target.Clause n) (j : ClauseAnswer) :
    shapeSat (shape cl) j=localSatisfies cl j := rfl
lemma shapeCons_exact {n : ℕ} (cl : Target.Clause n) (j : ClauseAnswer) :
    shapeCons (shape cl) j=localConsistent cl j := by
  simp only [shapeCons,shape,localConsistent,decide_eq_true_eq]
lemma repairedBit_exact {n : ℕ} (cl : Target.Clause n) (j : ClauseAnswer) (s : Slot) :
    repairedBit (shape cl) j s=answerAt (LCInput.repair cl j) s := by
  simp only [repairedBit,shapeSat_exact,shapeCons_exact,LCInput.repair]
  by_cases h : localSatisfies cl j=true ∧ localConsistent cl j=true
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h]
    rw [LCInput.fallback,honest_answerAt]
    change (if decide (nameAt cl s=cl[0].variableIndex) then cl[0].positive else false)=_
    by_cases hn : nameAt cl s=cl[0].variableIndex
    · rw [ite_eq_left (by simpa only [decide_eq_true_eq] using hn),ite_eq_left hn]
    · rw [ite_eq_right (by simpa only [decide_eq_true_eq] using hn),ite_eq_right hn]

lemma shapeTest_nonzero (F : Target.Formula) (c : Expr) (a : ℕ → ℕ) (i : Fin F.clauses.length)
    (hi : c.eval (Complexity.formulaBits F) a=i.val) (sh : Shape) :
    (shapeTest c sh).eval (Complexity.formulaBits F) a≠0 ↔ sh=shape (clauseAt F i) := by
  have hs (s : Slot) := signExpr_eval F c a i hi s
  have hn (s : Slot) := nameExpr_eval F c a i hi s
  simp only [shapeTest,Expr.eval,Expr.listAll_eval,Expr.equal_eval,hs,hn,List.mem_finRange,
    forall_true_left,Nat.mul_ne_zero_iff,indicator_ne,Fin.val_inj]
  simp only [← bit_decide,bit_eq,Bool.decide_coe]
  constructor
  · rintro ⟨hs,hn⟩
    apply Prod.ext
    · funext s
      change sh.1 s=signAt (clauseAt F i) s
      simpa using (hs (RawInitialTables.slotOrder s)).symm
    · funext s t
      simpa [shape] using (hn (RawInitialTables.slotOrder s) (RawInitialTables.slotOrder t)).symm
  · rintro rfl
    exact ⟨fun _ => rfl,fun _ _ => rfl⟩

lemma shapeExpr_eval (F : Target.Formula) (c : Expr) (a : ℕ → ℕ) (i : Fin F.clauses.length)
    (hi : c.eval (Complexity.formulaBits F) a=i.val) :
    (shapeExpr c).eval (Complexity.formulaBits F) a=(Fintype.equivFin Shape (shape (clauseAt F i))).val := by
  apply Expr.pick_eval
  exact shapeTest_nonzero F c a i hi

lemma repairExpr_eval (F : Target.Formula) (c : Expr) (a : ℕ → ℕ) (i : Fin F.clauses.length)
    (hi : c.eval (Complexity.formulaBits F) a=i.val) (j : ClauseAnswer) (s : Slot) :
    (repairExpr c j s).eval (Complexity.formulaBits F) a=bit (answerAt (LCInput.repair (clauseAt F i) j) s) := by
  rw [repairExpr,Expr.staticLookup_eval _ _ _ _ _ (shapeExpr_eval F c a i hi),repairedBit_exact]

lemma selectSlot_eval (x : Expr) (f : Slot → Expr) (str : List Bool) (a : ℕ → ℕ) (s : Slot)
    (hs : x.eval str a=(RawInitialTables.slotOrder s).val) :
    (selectSlot x f).eval str a=(f s).eval str a := by
  simp only [selectSlot,Expr.listSum_eval,Expr.eval,Expr.equal_eval,hs,ite_mul,one_mul,zero_mul]
  rw [← List.ofFn_eq_map,List.sum_ofFn]
  simp [Fin.val_inj]

end LargeIndependentSets.TargetRepair

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Encoding_TargetLCExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.TargetLC
open IndependentSetsGames.Foundations IndependentSetsGames.Foundations.Complexity
open IndependentSetsCut.CounterMachine
open Target PCP Hastad.SourceContexts Hastad.SourceGame UniformLC
open TargetRead TargetRepair
open scoped Classical BigOperators
noncomputable section
variable (u : ℕ)

def eventExpr (x : Expr) (k : Fin u) : Expr :=
  Expr.remainder (Expr.quotient x (Expr.power (.mul clausesExpr (.const 3)) k.val))
    (.mul clausesExpr (.const 3))
def clauseExpr (x : Expr) (k : Fin u) : Expr := Expr.quotient (eventExpr u x k) (.const 3)
def slotExpr (x : Expr) (k : Fin u) : Expr := Expr.remainder (eventExpr u x k) (.const 3)

lemma clauseExpr_eval (F : Input) (x : Expr) (a : ℕ → ℕ) (i : Fin (table u F).ne)
    (hi : x.eval (Complexity.formulaBits F.val) a=i.val) (k : Fin u) :
    (clauseExpr u x k).eval (Complexity.formulaBits F.val) a=
      (((eventEquiv u F.val).symm i k).1).val := by
  simp only [clauseExpr,eventExpr,Expr.remainder_eval,Expr.quotient_eval,Expr.power_eval,
    Expr.eval,clausesExpr_eval,hi]
  rfl

lemma slotExpr_eval (F : Input) (x : Expr) (a : ℕ → ℕ) (i : Fin (table u F).ne)
    (hi : x.eval (Complexity.formulaBits F.val) a=i.val) (k : Fin u) :
    (slotExpr u x k).eval (Complexity.formulaBits F.val) a=
      (RawInitialTables.slotOrder (((eventEquiv u F.val).symm i k).2)).val := by
  simp only [slotExpr,eventExpr,Expr.remainder_eval,Expr.quotient_eval,Expr.power_eval,
    Expr.eval,clausesExpr_eval,hi]
  change _=(RawInitialTables.slotOrder (RawInitialTables.slotOrder.symm _)).val
  rw [Equiv.apply_symm_apply]
  rfl

def sampledNameExpr (x : Expr) (k : Fin u) : Expr :=
  selectSlot (slotExpr u x k) (nameExpr (clauseExpr u x k))
def projectedBitExpr (x : Expr) (j : J u) (k : Fin u) : Expr :=
  selectSlot (slotExpr u x k) (repairExpr (clauseExpr u x k) (j k))

lemma sampledNameExpr_eval (F : Input) (x : Expr) (a : ℕ → ℕ) (i : Fin (table u F).ne)
    (hi : x.eval (Complexity.formulaBits F.val) a=i.val) (k : Fin u) :
    (sampledNameExpr u x k).eval (Complexity.formulaBits F.val) a=
      (nameAt (clauseAt F.val (((eventEquiv u F.val).symm i k).1))
        (((eventEquiv u F.val).symm i k).2)).val := by
  rw [sampledNameExpr,selectSlot_eval _ _ _ _ _ (slotExpr_eval u F x a i hi k)]
  exact nameExpr_eval F.val _ a _ (clauseExpr_eval u F x a i hi k) _

lemma projectedBitExpr_eval (F : Input) (x : Expr) (a : ℕ → ℕ) (i : Fin (table u F).ne)
    (hi : x.eval (Complexity.formulaBits F.val) a=i.val) (j : J u) (k : Fin u) :
    (projectedBitExpr u x j k).eval (Complexity.formulaBits F.val) a=
      bit ((table u F).project i j k) := by
  rw [projectedBitExpr,selectSlot_eval _ _ _ _ _ (slotExpr_eval u F x a i hi k)]
  rw [repairExpr_eval _ _ _ _ (clauseExpr_eval u F x a i hi k)]
  congr 1
  exact (project_apply u F.val _ j k).symm

lemma rankExpr_eval (s : List Bool) (a : ℕ → ℕ) (base : Expr) (f : Fin u → Expr)
    {m : ℕ} (v : Fin u → Fin m) (hb : base.eval s a=m) (hf : ∀ k, (f k).eval s a=(v k).val) :
    (rankExpr u base f).eval s a=(finFunctionFinEquiv v).val := by
  simp only [rankExpr,Expr.listSum_eval,Expr.eval,Expr.power_eval,hb,hf,finFunctionFinEquiv_apply]
  rw [← List.ofFn_eq_map,List.sum_ofFn]

def leftExpr (x : Expr) : Expr := rankExpr u clausesExpr (clauseExpr u x)
def rightExpr (x : Expr) : Expr := rankExpr u varsExpr (sampledNameExpr u x)
lemma leftExpr_eval (F : Input) (x : Expr) (a : ℕ → ℕ) (i : Fin (table u F).ne)
    (hi : x.eval (Complexity.formulaBits F.val) a=i.val) :
    (leftExpr u x).eval (Complexity.formulaBits F.val) a=((table u F).left i).val := by
  exact rankExpr_eval u _ _ _ _ _ (clausesExpr_eval F.val a) (clauseExpr_eval u F x a i hi)
lemma rightExpr_eval (F : Input) (x : Expr) (a : ℕ → ℕ) (i : Fin (table u F).ne)
    (hi : x.eval (Complexity.formulaBits F.val) a=i.val) :
    (rightExpr u x).eval (Complexity.formulaBits F.val) a=((table u F).right i).val := by
  exact rankExpr_eval u _ _ _ _ _ (varsExpr_eval F.val a) (sampledNameExpr_eval u F x a i hi)

def projectionTest (x : Expr) (f : J u → I u) : Expr :=
  Expr.listAll (List.finRange (Fintype.card (J u))) fun i =>
    Expr.listAll (List.finRange u) fun k =>
      Expr.equal (projectedBitExpr u x ((Fintype.equivFin (J u)).symm i) k)
        (.const (bit (f ((Fintype.equivFin (J u)).symm i) k)))
lemma projectionTest_nonzero (F : Input) (x : Expr) (a : ℕ → ℕ) (i : Fin (table u F).ne)
    (hi : x.eval (Complexity.formulaBits F.val) a=i.val) (f : J u → I u) :
    (projectionTest u x f).eval (Complexity.formulaBits F.val) a≠0 ↔ f=(table u F).project i := by
  simp only [projectionTest,Expr.listAll_eval,List.mem_finRange,forall_true_left,
    Expr.equal_eval,projectedBitExpr_eval u F x a i hi,Expr.eval,indicator_ne,bit_eq]
  constructor
  · intro h
    funext j k
    simpa using (h (Fintype.equivFin (J u) j) k).symm
  · rintro rfl
    exact fun _ _ => rfl

def projectExpr (x : Expr) : Expr := Expr.pick projectCode (projectionTest u x)
lemma projectExpr_eval (F : Input) (x : Expr) (a : ℕ → ℕ) (i : Fin (table u F).ne)
    (hi : x.eval (Complexity.formulaBits F.val) a=i.val) :
    (projectExpr u x).eval (Complexity.formulaBits F.val) a=projectCode ((table u F).project i) := by
  apply Expr.pick_eval
  exact projectionTest_nonzero u F x a i hi

end
end LargeIndependentSets.TargetLC

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_RoundComputation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.RoundComputation

open Turing
open IndependentSetsGames.Foundations.Complexity

abbrev PreprocessingCertificate (H : RoundTables.BaseTable) :=
  TM2ComputableInPolyTime GraphTables.tableBits
    (PortTables.inputBits (ports := PreprocessingTables.degree))
    (PreprocessingTables.output H)

abbrev PoweringCertificate :=
  TM2ComputableInPolyTime
    (PortTables.inputBits (ports := PreprocessingTables.degree))
    (GenericGraphTables.tableBits (q := RoundTables.alphabet))
    (PoweringTables.transform PreprocessingTables.degree RoundTables.walkParameter)

noncomputable def poweredPolynomialTimeOfCertificates (H : RoundTables.BaseTable)
    (preprocessing : PreprocessingCertificate H) (powering : PoweringCertificate) :
    TM2ComputableInPolyTime GraphTables.tableBits
      (GenericGraphTables.tableBits (q := RoundTables.alphabet))
      (RoundTables.powered H) := by
  change TM2ComputableInPolyTime GraphTables.tableBits _
    (fun table => PoweringTables.transform PreprocessingTables.degree
      RoundTables.walkParameter (PreprocessingTables.output H table))
  exact MachineSequential.composeBits preprocessing powering

end IndependentSetsGames.Foundations.PCP.RoundComputation

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_TargetLCMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.TargetLC
open IndependentSetsGames.Foundations IndependentSetsGames.Foundations.Complexity
open IndependentSetsCut.CounterMachine
open Target PCP Hastad.SourceContexts Hastad.SourceGame UniformLC
open TargetRead TargetRepair
open scoped Classical BigOperators
noncomputable section
variable (u : ℕ)

def edgesExpr : Expr := Expr.power (.mul clausesExpr (.const 3)) u
def countExpr : Expr := .add (.const 3) (.mul (.const 3) (edgesExpr u))
def valueExpr : Expr :=
  let x := Expr.quotient (.sub (.arg 0) (.const 3)) (.const 3)
  let j := Expr.remainder (.sub (.arg 0) (.const 3)) (.const 3)
  Expr.cond (Expr.equal (.arg 0) (.const 0)) (Expr.power clausesExpr u)
    (Expr.cond (Expr.equal (.arg 0) (.const 1)) (Expr.power varsExpr u)
      (Expr.cond (Expr.equal (.arg 0) (.const 2)) (edgesExpr u)
        (Expr.cond (Expr.lt x (edgesExpr u))
          (Expr.cond (Expr.equal j (.const 0)) (leftExpr u x)
            (Expr.cond (Expr.equal j (.const 1)) (rightExpr u x) (projectExpr u x))) (.const 0))))

@[simp] lemma edgesExpr_eval (F : Input) (a : ℕ → ℕ) :
    (edgesExpr u).eval (Complexity.formulaBits F.val) a=(table u F).ne := by
  simp only [edgesExpr,Expr.power_eval,Expr.eval,clausesExpr_eval]
  rfl
@[simp] lemma countExpr_eval (F : Input) (a : ℕ → ℕ) :
    (countExpr u).eval (Complexity.formulaBits F.val) a=3+3*(table u F).ne := by
  simp only [countExpr,Expr.eval,edgesExpr_eval]

lemma valueExpr_eval (F : Input) (w : ℕ) :
    (valueExpr u).eval (Complexity.formulaBits F.val) (fun _ => w)=(table u F).value w := by
  let x := Expr.quotient (.sub (.arg 0) (.const 3)) (.const 3)
  have hx : x.eval (Complexity.formulaBits F.val) (fun _ => w)=(w-3)/3 := by
    simp [x,Expr.quotient_eval,Expr.eval]
  simp only [valueExpr,Expr.cond_eval,Expr.equal_eval,Expr.eval,Expr.power_eval,
    clausesExpr_eval,varsExpr_eval,edgesExpr_eval,Table.value]
  by_cases h0 : w=0
  · simp only [h0]; rfl
  by_cases h1 : w=1
  · simp only [h1]; rfl
  by_cases h2 : w=2
  · simp [h2]
  simp only [h0,h1,h2]
  simp only [Expr.lt_eval,Expr.quotient_eval,Expr.remainder_eval,Expr.eval,edgesExpr_eval,indicator_ne]
  by_cases he : (w-3)/3 < (table u F).ne
  · simp only [he,ite_eq_left,dite_eq_left]
    have hl := leftExpr_eval u F x (fun _ => w) ⟨(w-3)/3,he⟩ hx
    have hr := rightExpr_eval u F x (fun _ => w) ⟨(w-3)/3,he⟩ hx
    have hp := projectExpr_eval u F x (fun _ => w) ⟨(w-3)/3,he⟩ hx
    rw [hl,hr,hp]
    rfl
  · simp only [he]
    rfl

lemma serializer_spec (F : Input) :
    UnaryTables.words (fun w => (valueExpr u).eval (Complexity.formulaBits F.val) (fun _ => w))
      ((countExpr u).eval (Complexity.formulaBits F.val) (fun _ => 0))=(table u F).bits := by
  rw [countExpr_eval,Table.bits]
  exact UnaryTables.words_congr (fun w _ => valueExpr_eval u F w)

def certificate : Turing.TM2ComputableInPolyTime (fun F : Input => Complexity.formulaBits F.val)
    Table.bits (table u) :=
  UnaryTables.encodedComputer _ _ _ (countExpr u) (valueExpr u) (serializer_spec u)

end
end LargeIndependentSets.TargetLC

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open IndependentSetsGames.Foundations
open scoped Classical
noncomputable section

namespace CompleteReduction
open PCP Hastad.SourceContexts Hastad.SourceGame
open Complexity

def gapInput (H : RoundTables.BaseTable) (b : List Bool) : TargetLC.Input :=
  ⟨TableIteration.gapMap H (BinaryNormalize.normalize b),TableIteration.gapMap_nonempty H _⟩

def reduce (H : RoundTables.BaseTable) (p : SamplerParameters) (u q : ℕ) (hq : 0<q)
    (b : List Bool) : Graph := GeometryNames.output (J u) (I u) p q hq (TargetLC.table u (gapInput H b))

def vertexPolynomial (p : SamplerParameters) (u q : ℕ) : Polynomial ℕ :=
  Polynomial.C q + (Polynomial.C 3*clausePolynomial)^(u*p.n) *
    Polynomial.C (GeometryNames.outcomeCount (J u) (I u) p)

def outputPolynomial (p : SamplerParameters) (u q : ℕ) : Polynomial ℕ :=
  Polynomial.C 4*(vertexPolynomial p u q+Polynomial.C 1)^2

end CompleteReduction

end
end LargeIndependentSets

end OAI
end


