-- Prove2me | Definitions.Def_OAIQ082C018
-- name    : OAIQ082C018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T13:39:09.591622+00:00
-- url     : https://prove2.me/theorems/158ea000-daf7-4e5a-8bce-47b547da66a2
-- title:
--   Definitions bundle OAIQ082C018 of the split of OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.BinPackingGap.main_results`, carved from OpenAI's openai/math development (OpenAI, *Additive hardness and unbounded configuration gaps in bin packing (result family 118)*, OpenAI Math Release, September 24, 2026, result family 118, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 195 declarations of OpenAI's Lean: 75 definitions, 3 inductive types or structures and 117 theorems. The definitions and types are `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TermMachine.RootsValid`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TermMachine.lookupSteps`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TermMachine.lookupTapes`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TermMachine.testPredicate`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFCleanup.cleanupExecution`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFCleanup.outputsInTime`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.LoopInvariant`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.LoopRun`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.RawRun`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.auxiliaryFlag`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.computableInPolyTime`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.emitInTime`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.emittedBytes`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.endpointsInTime`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.finalTimePolynomial`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.finishInTime`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.formulaHeader`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.guardEndInTime`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.guardRowInTime`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.headFlag`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.headPhaseInTime`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.headerInTime`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.headerPlan`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.initializedTableHeaderInTime`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.literalPlan`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.loopInTime`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.patternLiteral`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.patternPlan`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.phaseTimePolynomial`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.rawBudget`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.rawRun`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.referenceOffset`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.referenceValue`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.relationInTime`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.rowInTime`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.rowPlan`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.rowTime`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.tableHeaderInTime`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.tableRowsBits`, `OAI.BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program.tailFlag` and 38 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `BinPacking_Computation_FinalCNFCleanup`, `BinPacking_Computation_FinalCNFRowPlan`, `BinPacking_Computation_FinalCNFRowTrace`, `BinPacking_Computation_GraphCounterStart`, `BinPacking_Computation_GraphIterationBounds`, `BinPacking_Computation_MachineUnaryEqualityBit`, `BinPacking_Computation_TableIterationFiniteAlphabet`, `BinPacking_CookLevin_TermMachine`, `BinPacking_PCP_CompareLoop`, `BinPacking_PCP_FinalBooleanVerifier`, `BinPacking_PCP_Initialization`, `BinPacking_PCP_Lookup`, `BinPacking_PCP_PCPSource`, `BinPacking_PCP_PCPSourceHardness`, `BinPacking_PCP_PreprocessingGuarantees`, `BinPacking_PCP_RawInitialMachineBody`, `BinPacking_PCP_RawInitialMachineBudget`, `BinPacking_PCP_RawInitialMachineCleanup`, `BinPacking_PCP_RawInitialMachineFinish`, `BinPacking_PCP_RawInitialMachineLoopData`, `BinPacking_PCP_RawInitialMachineReadClause`, `BinPacking_PCP_RoundTableGap`.
--
--   **Imports.** It imports the published bundle `Def_BinPackingGap`; the bundles `OAIQ082C010`, `OAIQ082C011` and `OAIQ082C012` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ082C024`.
-- source:
--   OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 118; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_BinPackingGap
import Definitions.Def_OAIQ082C010
import Definitions.Def_OAIQ082C011
import Definitions.Def_OAIQ082C012

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_FinalBooleanVerifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.FinalBooleanVerifier

open Target

variable {V E : Type*} {n m : Nat}

theorem query_tail (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (e : Fin m) (j : Fin 6) :
    (verifier G vertices edges).query e (Fin.castAdd 6 j) =
      bitIndex vertices (G.tail (edges.symm e)) j := by
  simp only [verifier, Fin.addCases_left]

theorem query_head (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (e : Fin m) (j : Fin 6) :
    (verifier G vertices edges).query e (Fin.natAdd 6 j) =
      bitIndex vertices (G.head (edges.symm e)) j := by
  simp only [verifier, Fin.addCases_right]

end BinPackingGames.Foundations.PCP.FinalBooleanVerifier

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RawInitialMachineBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.GenericGraphTables

open BinPackingGames.Foundations.Complexity

variable {q : Nat}

theorem vertices_le_tableBits_length (table : (Table q)) :
    table.vertices ≤ (tableBits table).length := by
  simp only [tableBits, tableWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

theorem darts_le_tableBits_length (table : (Table q)) :
    table.darts ≤ (tableBits table).length := by
  simp only [tableBits, tableWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

end BinPackingGames.Foundations.PCP.GenericGraphTables

namespace BinPackingGames.Foundations.PCP.AlphabetTable.Input

open BinPackingGames.Foundations.Complexity

export GenericGraphTables (Label RelationTable DartRow Rows Valid Table
  relationIndex relationAt relationOf relationAt_relationOf
  reverseAt acceptsAt rowList rowList_length semantics semantics_reverse
  semantics_tail semantics_accepts ofGraph semantics_ofGraph ofEnumeratedGraph
  bitWord relationWords relationWords_length rowWords rowWords_length
  tableWords tableBits vertices_le_tableBits_length darts_le_tableBits_length)

variable {q n m : Nat}

theorem tableBits_header (table : Table q) :
    tableBits table = encodeWord table.vertices ++
      (encodeWord table.darts ++ encodeWords ((rowList table).flatMap rowWords)) := by
  simp [tableBits, tableWords, encodeWords]

end BinPackingGames.Foundations.PCP.AlphabetTable.Input

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineUnaryEqualityBit
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineFieldProfile

open Turing

section Transport
variable {K Λ σ τ : Type} [DecidableEq K]

def copyInCompareState (source destination scratch : K)
    (hSD : source ≠ destination) (hST : source ≠ scratch) (hDT : destination ≠ scratch)
    (firstLabel secondLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineCompare.State σ))
    (atFirst : program firstLabel = copyStatement
      (Reduction.MachineTransfer.loopAt source scratch id false firstLabel (some secondLabel)))
    (atSecond : program secondLabel = copyStatement
      (MachineCopy.forkLoop scratch source destination false secondLabel exit))
    (base : K → List Bool) (hScratch : base scratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some firstLabel, normalState ambient, base⟩
      (some ⟨exit, normalState ambient,
        Function.update base destination (base source ++ base destination)⟩)
      (2 * ((base source).length + 1)) := by
  let e := copyStateEquiv σ
  let view := MachineControl.program (Equiv.refl Λ) e.symm program
  have hfirst : view firstLabel =
      Reduction.MachineTransfer.loopAt source scratch id false firstLabel (some secondLabel) := by
    dsimp [view, MachineControl.program]
    rw [atFirst]
    exact statement_roundtrip e.symm _
  have hsecond : view secondLabel =
      MachineCopy.forkLoop scratch source destination false secondLabel exit := by
    dsimp [view, MachineControl.program]
    rw [atSecond]
    exact statement_roundtrip e.symm _
  let run := MachineCopy.copyInTime source destination scratch hSD hST hDT false
    firstLabel secondLabel exit view hfirst hsecond base hScratch (ambient, false, none) none
  have hprogram : MachineControl.program (Equiv.refl Λ) e view = program := by
    funext label
    exact statement_roundtrip e (program label)
  have hsim (a b : TM2.Cfg (fun _ : K => Bool) Λ ((σ × Bool × Option Bool) × Option Bool))
      (hab : TM2.step view a = some b) :
      TM2.step program (MachineControl.configuration id e a) =
        some (MachineControl.configuration id e b) := by
    have hh := MachineControl.step_simulation (Equiv.refl Λ) e view a
    rw [hprogram, hab] at hh
    exact hh
  have lifted := MachineComposition.liftExecutionInTime (TM2.step view) (TM2.step program)
    (MachineControl.configuration id e) hsim run
  simpa [MachineControl.configuration, copyStateEquiv, normalState, e] using lifted

end Transport

section PreservedComparison
variable {K Λ σ : Type} [DecidableEq K]

def nonDestructiveCompareInTime (left right workLeft workRight scratch : K)
    (hleft : left ≠ workLeft ∧ left ≠ workRight ∧ left ≠ scratch)
    (hright : right ≠ workLeft ∧ right ≠ workRight ∧ right ≠ scratch)
    (hwork : workLeft ≠ workRight ∧ workLeft ≠ scratch ∧ workRight ≠ scratch)
    (leftFirst leftSecond rightFirst rightSecond compareLabel : Λ)
    (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineCompare.State σ))
    (atLeftFirst : program leftFirst = copyStatement
      (Reduction.MachineTransfer.loopAt left scratch id false leftFirst (some leftSecond)))
    (atLeftSecond : program leftSecond = copyStatement
      (MachineCopy.forkLoop scratch left workLeft false leftSecond (some rightFirst)))
    (atRightFirst : program rightFirst = copyStatement
      (Reduction.MachineTransfer.loopAt right scratch id false rightFirst (some rightSecond)))
    (atRightSecond : program rightSecond = copyStatement
      (MachineCopy.forkLoop scratch right workRight false rightSecond (some compareLabel)))
    (atCompare : program compareLabel =
      MachineCompare.loop workLeft workRight compareLabel equalExit differentExit)
    (base : K → List Bool) (hWL : base workLeft = []) (hWR : base workRight = [])
    (hScratch : base scratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some leftFirst, normalState ambient, base⟩
      (some ⟨if base left = base right then equalExit else differentExit,
        normalState ambient, base⟩)
      (2 * ((base left).length + 1) + 2 * ((base right).length + 1) +
        max (base left).length (base right).length + 1) := by
  let t₁ := Function.update base workLeft (base left)
  let t₂ := Function.update t₁ workRight (base right)
  have h₁ := copyInCompareState left workLeft scratch hleft.1 hleft.2.2 hwork.2.1
    leftFirst leftSecond (some rightFirst) program atLeftFirst atLeftSecond base hScratch ambient
  simp only [hWL, List.append_nil] at h₁
  have hSR : t₁ right = base right := by simp [t₁, hright.1]
  have hDR : t₁ workRight = [] := by simp [t₁, Ne.symm hwork.1, hWR]
  have hTR : t₁ scratch = [] := by simp [t₁, Ne.symm hwork.2.1, hScratch]
  have h₂ := copyInCompareState right workRight scratch hright.2.1 hright.2.2 hwork.2.2
    rightFirst rightSecond (some compareLabel) program atRightFirst atRightSecond t₁ hTR ambient
  rw [hSR, hDR] at h₂
  simp only [List.append_nil] at h₂
  have hL : t₂ workLeft = base left := by simp [t₂, t₁, hwork.1]
  have hR : t₂ workRight = base right := by simp [t₂]
  have hrestore : Reduction.MachineTransfer.tapesAt workLeft workRight t₂ [] [] = base := by
    funext p
    by_cases hl : p = workLeft
    · subst p
      simp [Reduction.MachineTransfer.tapesAt, hwork.1, hWL]
    · by_cases hr : p = workRight
      · subst p
        simp [Reduction.MachineTransfer.tapesAt, hWR]
      · simp [Reduction.MachineTransfer.tapesAt, t₂, t₁, hl, hr]
  have h₃ := MachineCompare.compareInTime workLeft workRight hwork.1 compareLabel
    equalExit differentExit program atCompare t₂ ambient none none
  rw [hL, hR, hrestore] at h₃
  let h₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ h₁ h₂
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ h₁₂ h₃
  exact { toEvalsTo := run.toEvalsTo, steps_le_m := by have h := run.steps_le_m; omega }

end PreservedComparison

end BinPackingGames.Foundations.Complexity.MachineFieldProfile

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_PreprocessingGuarantees
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.PreprocessingTables

open PreprocessingRegularTables

theorem regularVertices_ge_darts (t : GraphTables.Table) : t.darts ≤ regularVertices t := by
  change t.darts ≤ t.darts + _
  omega

end BinPackingGames.Foundations.PCP.PreprocessingTables

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_Lookup
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.AlphabetTable.ReadRelation

open Turing
open BinPackingGames.Foundations.Complexity
open GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K] {q : Nat}

theorem stepAux_readSlot (source : K) (i : Fin (q * q)) (bit : Bool)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q))
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (initial : RelationTable q) (register : Option Bool) :
    TM2.stepAux (readSlot source i next) ((ambient, initial), register)
      (Function.update base source (encodeWord (bitWord bit) ++ suffix)) =
      TM2.stepAux next ((ambient, initial.set i.val bit i.isLt), none)
        (Function.update base source suffix) := by
  cases bit <;> simp [readSlot, TM2.stepAux, bitWord, encodeWord]

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

end BinPackingGames.Foundations.PCP.AlphabetTable.ReadRelation

namespace BinPackingGames.Foundations.PCP.AlphabetTable.Lookup

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K]

section Ambient

variable {q n m : Nat} (counter source destination : K) (labels : Label → Λ)
  (exit : Option Λ)
  (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
  (atStatement : ∀ label, P (labels label) = statement q counter source destination labels exit label)

include atStatement

theorem skipRowTrace (base : K → List Bool) (row : DartRow q n m) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[row.tail.val + row.reverseIndex.val + 3]
      (some ⟨some (labels .skipTail), (ambient, register),
        Function.update base source (rowBits row ++ suffix)⟩) =
      some ⟨some (labels .guard), (ambient, none), Function.update base source suffix⟩ := by
  have ht := MachineLookup.discardTrace_update source (labels .skipTail) (labels .skipReverse)
    P (atStatement .skipTail) base row.tail.val
    (encodeWord row.reverseIndex.val ++ (encodeWords (relationWords row.relation) ++ suffix))
    ambient register
  have hr := MachineLookup.discardTrace_update source (labels .skipReverse) (labels .skipPredicate)
    P (atStatement .skipReverse) base row.reverseIndex.val
    (encodeWords (relationWords row.relation) ++ suffix) ambient none
  have hp : TM2.step P
      ⟨some (labels .skipPredicate), (ambient, none), Function.update base source
        (encodeWords (relationWords row.relation) ++ suffix)⟩ =
      some ⟨some (labels .guard), (ambient, none), Function.update base source suffix⟩ := by
    change some (TM2.stepAux (P (labels .skipPredicate)) _ _) = _
    rw [atStatement .skipPredicate]
    have h := congrArg some (stepAux_skipBits source row.relation.toList
      (.goto fun _ => labels .guard) base suffix ambient none)
    simpa only [statement, Vector.length_toList, relationWords, TM2.stepAux] using h
  rw [rowBits_eq]
  simp only [List.append_assoc]
  rw [show row.tail.val + row.reverseIndex.val + 3 =
    1 + ((row.reverseIndex.val + 1) + (row.tail.val + 1)) by omega,
    Function.iterate_add_apply, Function.iterate_add_apply, ht, hr,
    Function.iterate_one, advance_some, hp]

theorem skipRowTrace_fromTapes (base : K → List Bool) (row : DartRow q n m)
    (suffix : List Bool) (hinput : base source = rowBits row ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[row.tail.val + row.reverseIndex.val + 3]
      (some ⟨some (labels .skipTail), (ambient, register), base⟩) =
      some ⟨some (labels .guard), (ambient, none), Function.update base source suffix⟩ := by
  have h := skipRowTrace counter source destination labels exit P atStatement
    base row suffix ambient register
  have hb : Function.update base source (rowBits row ++ suffix) = base := by
    rw [← hinput]
    exact Function.update_eq_self source base
  rw [hb] at h
  exact h

theorem selectTrace (hsd : source ≠ destination) (base : K → List Bool)
    (row : DartRow q n m) (suffix : List Bool)
    (hinput : base source = rowBits row ++ suffix) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[row.tail.val + 2]
      (some ⟨some (labels .select), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), Hastad.SourceMachine.fieldTapes source destination base
        (encodeWord row.reverseIndex.val ++ (encodeWords (relationWords row.relation) ++ suffix))
        (encodeWord row.tail.val ++ base destination)⟩ := by
  let ht := Hastad.SourceMachine.fieldInTime source destination hsd
    (labels .select) (labels .copy) exit P (atStatement .select) (atStatement .copy)
    base row.tail.val
    (encodeWord row.reverseIndex.val ++ (encodeWords (relationWords row.relation) ++ suffix))
    (by simpa only [rowBits_eq, List.append_assoc] using hinput) ambient register
  have hsteps : ht.steps = row.tail.val + 2 := rfl
  have htrace := ht.evals_in_steps
  rw [hsteps] at htrace
  exact htrace

theorem lookupTailTrace
    (hcs : counter ≠ source) (hcd : counter ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (prior : List (DartRow q n m)) (row : DartRow q n m)
    (counterSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[lookupCost prior row]
      (some ⟨some (labels .guard), (ambient, register),
        MachineLookup.tapes counter source destination base
          (encodeWord prior.length ++ counterSuffix)
          (rowsBits prior ++ (rowBits row ++ suffix)) output⟩) =
      some ⟨exit, (ambient, none),
        MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix)
          (encodeWord row.reverseIndex.val ++ (encodeWords (relationWords row.relation) ++ suffix))
          (encodeWord row.tail.val ++ output)⟩ := by
  induction prior generalizing register with
  | nil =>
    simp only [lookupCost, prefixCost, List.map_nil, List.sum_nil, Nat.zero_add,
      List.length_nil, rowsBits_nil, List.nil_append]
    rw [show row.tail.val + 3 = (row.tail.val + 2) + 1 by omega,
      Function.iterate_succ_apply]
    have hg := MachineUnaryCounter.guardStep_zero counter (labels .guard)
      (labels .skipTail) (labels .select) P (atStatement .guard)
      (MachineLookup.tapes counter source destination base
        (encodeWord 0 ++ counterSuffix) (rowBits row ++ suffix) output)
      counterSuffix ambient register
    have hcounter : MachineUnaryCounter.counterTapes counter
        (MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix) (rowBits row ++ suffix) output) 0 counterSuffix =
        MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix) (rowBits row ++ suffix) output := by
      simp only [MachineUnaryCounter.counterTapes, MachineLookup.update_index _ _ _ hcs hcd]
    rw [hcounter] at hg
    simp only [advance_some]
    rw [hg]
    have hs := selectTrace counter source destination labels exit P atStatement hsd
      (MachineLookup.tapes counter source destination base
        (encodeWord 0 ++ counterSuffix) (rowBits row ++ suffix) output)
      row suffix (by simp [hsd]) ambient none
    simpa only [MachineLookup.tapes_destination,
      MachineLookup.fieldTapes_eq _ _ _ hsd] using hs
  | cons first prior ih =>
    simp only [lookupCost, prefixCost, List.map_cons, List.sum_cons, List.length_cons,
      rowsBits_cons, List.append_assoc]
    rw [show skipCost first + (prior.map skipCost).sum + row.tail.val + 3 =
      ((prior.map skipCost).sum + row.tail.val + 3) +
        (first.tail.val + first.reverseIndex.val + 3) + 1 by simp only [skipCost]; omega,
      Function.iterate_succ_apply]
    have hg := MachineUnaryCounter.guardStep_succ counter (labels .guard)
      (labels .skipTail) (labels .select) P (atStatement .guard)
      (MachineLookup.tapes counter source destination base
        (encodeWord prior.length ++ counterSuffix)
        (rowBits first ++ (rowsBits prior ++ (rowBits row ++ suffix))) output)
      prior.length counterSuffix ambient register
    simp only [MachineUnaryCounter.counterTapes,
      MachineLookup.update_index _ _ _ hcs hcd] at hg
    simp only [advance_some]
    rw [hg, Function.iterate_add_apply]
    have hs := skipRowTrace_fromTapes counter source destination labels exit P atStatement
      (MachineLookup.tapes counter source destination base
        (encodeWord prior.length ++ counterSuffix)
        (rowBits first ++ (rowsBits prior ++ (rowBits row ++ suffix))) output)
      first (rowsBits prior ++ (rowBits row ++ suffix)) (by simp [hsd]) ambient none
    rw [hs]
    simp only [MachineLookup.update_source _ _ _ hsd]
    exact ih none

end Ambient

theorem tableTailTrace {q : Nat}
    (counter source destination : K) (labels : Label → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStatement : ∀ label, P (labels label) = statement q counter source destination labels exit label)
    (hcs : counter ≠ source) (hcd : counter ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (table : Table q) (e : Fin table.darts)
    (counterSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[lookupCost ((rowList table).take e.val) table.rows[e]]
      (some ⟨some (labels .guard), (ambient, register),
        MachineLookup.tapes counter source destination base
          (encodeWord e.val ++ counterSuffix) (rowsBits (rowList table) ++ suffix) output⟩) =
      some ⟨exit, (ambient, none),
        MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix)
          (encodeWord table.rows[e].reverseIndex.val ++
            (encodeWords (relationWords table.rows[e].relation) ++
              (rowsBits ((rowList table).drop (e.val + 1)) ++ suffix)))
          (encodeWord table.rows[e].tail.val ++ output)⟩ := by
  have h := lookupTailTrace counter source destination labels exit P atStatement
    hcs hcd hsd base ((rowList table).take e.val) table.rows[e] counterSuffix
    (rowsBits ((rowList table).drop (e.val + 1)) ++ suffix) output ambient register
  have hlength : ((rowList table).take e.val).length = e.val := by
    simp only [List.length_take, rowList_length, Nat.min_eq_left (Nat.le_of_lt e.isLt)]
  have hsplit : rowsBits (rowList table) ++ suffix =
      rowsBits ((rowList table).take e.val) ++
        (rowBits table.rows[e] ++ (rowsBits ((rowList table).drop (e.val + 1)) ++ suffix)) := by
    have hrow : table.rows[e.val] = table.rows[e] := rfl
    simpa only [rowsBits, rowBits, rowList, Vector.getElem_toList, hrow] using
      Input.rowsBits_append_split (rowList table) e.val (by simp) suffix
  rw [hlength, ← hsplit] at h
  exact h

theorem fullTableTailTrace {q : Nat}
    (counter source destination : K) (labels : Label → Λ) (exit : Option Λ)
    (headerVertices headerDarts : Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStatement : ∀ label, P (labels label) = statement q counter source destination labels exit label)
    (atVertices : P headerVertices = MachineLookup.discard source headerVertices headerDarts)
    (atDarts : P headerDarts = MachineLookup.discard source headerDarts (labels .guard))
    (hcs : counter ≠ source) (hcd : counter ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (table : Table q) (e : Fin table.darts)
    (counterSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[lookupCost ((rowList table).take e.val) table.rows[e] +
        (table.darts + 1) + (table.vertices + 1)]
      (some ⟨some headerVertices, (ambient, register),
        MachineLookup.tapes counter source destination base
          (encodeWord e.val ++ counterSuffix) (tableBits table ++ suffix) output⟩) =
      some ⟨exit, (ambient, none),
        MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix)
          (encodeWord table.rows[e].reverseIndex.val ++
            (encodeWords (relationWords table.rows[e].relation) ++
              (rowsBits ((rowList table).drop (e.val + 1)) ++ suffix)))
          (encodeWord table.rows[e].tail.val ++ output)⟩ := by
  have hv := MachineLookup.discardTrace source headerVertices headerDarts P atVertices
    (MachineLookup.tapes counter source destination base
      (encodeWord e.val ++ counterSuffix) (tableBits table ++ suffix) output)
    table.vertices (encodeWord table.darts ++ (rowsBits (rowList table) ++ suffix))
    (by simp only [MachineLookup.tapes_source _ _ _ hsd, Input.tableBits_header,
      rowsBits, List.append_assoc]) ambient register
  rw [Function.iterate_add_apply, hv]
  simp only [MachineLookup.update_source _ _ _ hsd]
  have hd := MachineLookup.discardTrace source headerDarts (labels .guard) P atDarts
    (MachineLookup.tapes counter source destination base
      (encodeWord e.val ++ counterSuffix)
      (encodeWord table.darts ++ (rowsBits (rowList table) ++ suffix)) output)
    table.darts (rowsBits (rowList table) ++ suffix) (by simp [hsd]) ambient none
  rw [Function.iterate_add_apply, hd]
  simp only [MachineLookup.update_source _ _ _ hsd]
  exact tableTailTrace counter source destination labels exit P atStatement hcs hcd hsd
    base table e counterSuffix suffix output ambient none

theorem tableTailCost_le {q : Nat} (table : Table q) (e : Fin table.darts) :
    tableTailCost table e ≤ (tableBits table).length + 2 * (encodeWord e.val).length + 1 := by
  have htake : ((rowList table).take e.val).length = e.val := by
    simp only [List.length_take, rowList_length, Nat.min_eq_left (Nat.le_of_lt e.isLt)]
  have hrow : table.rows[e.val] = table.rows[e] := rfl
  have hsplit : rowsBits (rowList table) = rowsBits ((rowList table).take e.val) ++
      (rowBits table.rows[e] ++ rowsBits ((rowList table).drop (e.val + 1))) := by
    simpa only [rowsBits, rowBits, rowList, Vector.getElem_toList, hrow] using
      Input.rowsBits_split (rowList table) e.val (by simp)
  have hp : (rowsBits ((rowList table).take e.val) ++ rowBits table.rows[e]).length ≤
      (rowsBits (rowList table)).length := by
    rw [hsplit]
    simp only [List.length_append]
    omega
  have hb := lookupCost_le ((rowList table).take e.val) table.rows[e]
  rw [htake] at hb
  have hh := congrArg List.length (Input.tableBits_header table)
  change (tableBits table).length =
    (encodeWord table.vertices ++ (encodeWord table.darts ++ rowsBits (rowList table))).length at hh
  simp only [List.length_append, encodeWord_length] at hh
  unfold tableTailCost
  omega

def headLookupCost {q : Nat} (table : Table q) (e : Fin table.darts) : Nat :=
  2 * ((tableBits table).length + 1) +
    2 * ((encodeWord (headIndex table e).val).length + 1) + tableTailCost table (headIndex table e)

theorem headLookupCost_le {q : Nat} (table : Table q) (e : Fin table.darts) :
    headLookupCost table e ≤ 7 * (tableBits table).length + 5 := by
  have hi : (encodeWord (headIndex table e).val).length ≤ (tableBits table).length := by
    rw [encodeWord_length]
    exact (Nat.succ_le_of_lt (headIndex table e).isLt).trans (darts_le_tableBits_length table)
  have hl := tableTailCost_le table (headIndex table e)
  unfold headLookupCost
  omega

def headLookupInTime {q : Nat}
    (tape : HeadTapes K) (hinj : Function.Injective tape)
    (tableFirst tableSecond indexFirst indexSecond headerVertices headerDarts : Λ)
    (labels : Label → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atTableFirst : P tableFirst = Reduction.MachineTransfer.loopAt
      (tape 0) (tape 5) id false tableFirst (some tableSecond))
    (atTableSecond : P tableSecond = MachineCopy.forkLoop
      (tape 5) (tape 0) (tape 2) false tableSecond (some indexFirst))
    (atIndexFirst : P indexFirst = Reduction.MachineTransfer.loopAt
      (tape 1) (tape 5) id false indexFirst (some indexSecond))
    (atIndexSecond : P indexSecond = MachineCopy.forkLoop
      (tape 5) (tape 1) (tape 3) false indexSecond (some headerVertices))
    (atVertices : P headerVertices = MachineLookup.discard (tape 2) headerVertices headerDarts)
    (atDarts : P headerDarts = MachineLookup.discard (tape 2) headerDarts (labels .guard))
    (atStatement : ∀ label,
      P (labels label) = statement q (tape 3) (tape 2) (tape 4) labels exit label)
    (base : K → List Bool) (table : Table q) (e : Fin table.darts)
    (hTable : base (tape 0) = tableBits table)
    (hReverse : base (tape 1) = encodeWord (headIndex table e).val)
    (hHead : base (tape 4) = []) (hScratch : base (tape 5) = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some tableFirst, (ambient, register), base⟩
      (some ⟨exit, (ambient, none), headLookupTapes tape base table e⟩)
      (headTimePolynomial.eval (tableBits table).length) := by
  have hne (i j : Fin 6) (h : i ≠ j) : tape i ≠ tape j := fun heq => h (hinj heq)
  let t₁ := Function.update base (tape 2) (tableBits table ++ base (tape 2))
  let t₂ := Function.update t₁ (tape 3) (encodeWord (headIndex table e).val ++ base (tape 3))
  have run₁ : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some tableFirst, (ambient, register), base⟩
      (some ⟨some indexFirst, (ambient, none), t₁⟩)
      (2 * ((tableBits table).length + 1)) := by
    simpa only [hTable, t₁] using MachineCopy.copyInTime (tape 0) (tape 2) (tape 5)
      (hne 0 2 (by decide)) (hne 0 5 (by decide)) (hne 2 5 (by decide)) false
      tableFirst tableSecond (some indexFirst) P atTableFirst atTableSecond
      base hScratch ambient register
  have hsrc : t₁ (tape 1) = encodeWord (headIndex table e).val := by
    simp only [t₁, Function.update_of_ne (hne 1 2 (by decide)), hReverse]
  have hdst : t₁ (tape 3) = base (tape 3) := by
    simp only [t₁, Function.update_of_ne (hne 3 2 (by decide))]
  have hscratch₁ : t₁ (tape 5) = [] := by
    simp only [t₁, Function.update_of_ne (hne 5 2 (by decide)), hScratch]
  have run₂ : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some indexFirst, (ambient, none), t₁⟩
      (some ⟨some headerVertices, (ambient, none), t₂⟩)
      (2 * ((encodeWord (headIndex table e).val).length + 1)) := by
    simpa only [hsrc, hdst, t₂] using MachineCopy.copyInTime (tape 1) (tape 3) (tape 5)
      (hne 1 3 (by decide)) (hne 1 5 (by decide)) (hne 3 5 (by decide)) false
      indexFirst indexSecond (some headerVertices) P atIndexFirst atIndexSecond
      t₁ hscratch₁ ambient none
  have ht₂ : t₂ = MachineLookup.tapes (tape 3) (tape 2) (tape 4) base
      (encodeWord (headIndex table e).val ++ base (tape 3))
      (tableBits table ++ base (tape 2)) [] := by
    funext k
    by_cases hi : k = tape 3
    · subst k
      simp [t₂, MachineLookup.tapes, hne 3 2 (by decide), hne 3 4 (by decide)]
    · by_cases hs : k = tape 2
      · subst k
        simp [t₂, t₁, MachineLookup.tapes, hne 2 3 (by decide), hne 2 4 (by decide)]
      · by_cases hh : k = tape 4
        · subst k
          simp [t₂, t₁, MachineLookup.tapes, hne 4 3 (by decide),
            hne 4 2 (by decide), hHead]
        · simp [t₂, t₁, MachineLookup.tapes, hi, hs, hh]
  let run₃ : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some headerVertices, (ambient, none), t₂⟩
      (some ⟨exit, (ambient, none), headLookupTapes tape base table e⟩)
      (tableTailCost table (headIndex table e)) := {
    steps := tableTailCost table (headIndex table e)
    evals_in_steps := by
      change (advance (TM2.step P))^[tableTailCost table (headIndex table e)]
        (some ⟨some headerVertices, (ambient, none), t₂⟩) =
          some ⟨exit, (ambient, none), headLookupTapes tape base table e⟩
      rw [ht₂]
      simpa only [headLookupTapes, headValue, tableTailCost, List.append_nil] using
        fullTableTailTrace (tape 3) (tape 2) (tape 4) labels exit
          headerVertices headerDarts P atStatement atVertices atDarts
          (hne 3 2 (by decide)) (hne 3 4 (by decide)) (hne 2 4 (by decide))
          base table (headIndex table e) (base (tape 3)) (base (tape 2)) [] ambient none
    steps_le_m := Nat.le_refl _ }
  let run₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ run₂
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁₂ run₃
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have ht := run.steps_le_m
  have hb := headLookupCost_le table e
  simp only [headTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  unfold headLookupCost at hb
  omega

theorem readRowCost_table_le {q : Nat} (table : Table q) (e : Fin table.darts) :
    readRowCost table.rows[e] ≤ 2 * (tableBits table).length + 5 := by
  have ht := (Nat.le_of_lt table.rows[e].tail.isLt).trans
    (vertices_le_tableBits_length table)
  have hr := (Nat.le_of_lt table.rows[e].reverseIndex.isLt).trans
    (darts_le_tableBits_length table)
  unfold readRowCost
  omega

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

end BinPackingGames.Foundations.PCP.AlphabetTable.Lookup

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_FinalCNFRowTrace
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.FinalCNFMachine

open Turing
open PCP

section RelationReader

variable {K Λ σ : Type} {N : Nat}

def unaryBits (slots : List (Fin N)) (bits : Buffer N) : List Bool :=
  slots.flatMap fun i => encodeWord (GraphTables.bitWord (bits i))

theorem unaryBits_eq_encodeWords (slots : List (Fin N)) (bits : Buffer N) :
    unaryBits slots bits = encodeWords (slots.map fun i => GraphTables.bitWord (bits i)) := by
  induction slots with
  | nil => rfl
  | cons i slots ih => simpa only [unaryBits, List.flatMap_cons, List.map_cons,
      encodeWords] using congrArg (encodeWord (GraphTables.bitWord (bits i)) ++ ·) ih

variable [DecidableEq K]

theorem stepAux_readUnarySlots (source : K) (slots : List (Fin N))
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (ambient : σ) (bits buffer : Buffer N) (tapes : K → List Bool)
    (suffix : List Bool) :
    TM2.stepAux (readUnarySlots source slots next) (ambient, buffer)
        (Function.update tapes source (unaryBits slots bits ++ suffix)) =
      TM2.stepAux next (ambient, MachineFixedBlockMap.fill slots bits buffer)
        (Function.update tapes source suffix) := by
  induction slots generalizing buffer tapes with
  | nil => simp [readUnarySlots, unaryBits, MachineFixedBlockMap.fill]
  | cons i slots ih =>
      cases hi : bits i <;>
        simp only [readUnarySlots, unaryBits, List.flatMap_cons, hi,
          GraphTables.bitWord, Bool.false_eq_true, ite_false, ite_true, if_true, encodeWord,
          List.replicate_zero, List.replicate_succ, List.nil_append,
          List.cons_append,
          TM2.stepAux, Function.update_self, List.head?_cons, Option.getD_some,
          List.tail_cons, Function.update_idem, MachineFixedBlockMap.fill,
          List.foldl_cons]
      · simpa [unaryBits, MachineFixedBlockMap.fill, hi, encodeWord, GraphTables.bitWord] using
          ih (Function.update buffer i false) tapes
      · simpa [unaryBits, MachineFixedBlockMap.fill, hi, encodeWord, GraphTables.bitWord] using
          ih (Function.update buffer i true) tapes

theorem stepAux_readUnaryAll (source : K)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (state : σ × Buffer N) (bits : Buffer N) (tapes : K → List Bool)
    (suffix : List Bool)
    (hinput : tapes source = unaryBits (List.ofFn id) bits ++ suffix) :
    TM2.stepAux (readUnarySlots source (List.ofFn id) next) state tapes =
      TM2.stepAux next (state.1, bits) (Function.update tapes source suffix) := by
  have h := stepAux_readUnarySlots source (List.ofFn id) next state.1 bits state.2 tapes suffix
  have hin : Function.update tapes source (unaryBits (List.ofFn id) bits ++ suffix) = tapes := by
    simpa only [← hinput] using Function.update_eq_self source tapes
  rw [hin, MachineFixedBlockMap.fill_all] at h
  exact h

end RelationReader

theorem unaryBits_relation (relation : GraphTables.RelationTable) :
    unaryBits (List.ofFn id) (fun i => relation[i]) =
      encodeWords (GraphTables.relationWords relation) := by
  have h : List.ofFn (fun i : Fin 4096 => relation[i]) = relation.toList := by
    change List.ofFn (fun i : Fin 4096 => relation[i.val]) = relation.toList
    rw [← Vector.toList_ofFn, Vector.ofFn_getElem]
  rw [unaryBits_eq_encodeWords]
  unfold GraphTables.relationWords
  rw [← h]
  simp only [List.map_ofFn, Function.comp_def, id_eq]

section AmbientRelation

variable {K Λ σ : Type} [DecidableEq K]

theorem stepAux_readRelationAt (source : K) (exit : Λ) (ambient : σ)
    (buffer : Buffer 4096) (unitState : Unit) (register : Option Bool)
    (relation : GraphTables.RelationTable) (tapes : K → List Bool) (suffix : List Bool)
    (hinput : tapes source = encodeWords (GraphTables.relationWords relation) ++ suffix) :
    TM2.stepAux (readRelationAt source exit) (((ambient, buffer), unitState), register) tapes =
      ⟨some exit, (((ambient, fun i => relation[i]), unitState), register),
        Function.update tapes source suffix⟩ := by
  change TM2.stepAux (MachineControl.statement id (readerStateEquiv σ 4096)
    (readUnarySlots source (List.ofFn id) (.goto fun _ => exit)))
    ((readerStateEquiv σ 4096) (((ambient, unitState), register), buffer)) tapes = _
  rw [MachineControl.stepAux_simulation]
  rw [stepAux_readUnaryAll source _ _ (fun i => relation[i]) tapes suffix
    (by simpa only [unaryBits_relation] using hinput)]
  rfl

end AmbientRelation

namespace Program

open PCP.AlphabetTable

def headerPlan : Plan :=
  Emitter.affineCommands [(0, 6), (1, 36864)] (fun _ => 0) ++
    Emitter.affineCommands [(1, 40960)] (fun _ => 0)

theorem headerPlan_length : headerPlan.length = 7 := by
  simp [headerPlan]

theorem headerPlan_bits (vertices darts tail head row : Nat) (ambient : Ambient) :
    headerPlan.flatMap (Emitter.commandBits (values vertices darts tail head row) ambient) =
      encodeWords [6 * vertices + 36864 * darts, 40960 * darts] := by
  rw [headerPlan, List.flatMap_append, Emitter.affineCommands_bits,
    Emitter.affineCommands_bits]
  simp [Emitter.affineValue, values, encodeWords]
  rfl

def headPhaseInTime (headerPlan rowPlan : Plan) (base : Tape → List Bool)
    (table : GenericGraphTables.Table 64) (e : Fin table.darts)
    (hTable : base .archive = GenericGraphTables.tableBits table)
    (hReverse : base .reverseIndex = encodeWord (Lookup.headIndex table e).val)
    (hHead : base .head = []) (hScratch : base .scratch = []) (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .headTableFirst, ((ambient, ()), none), base⟩
      (some ⟨some .readRelation, ((ambient, ()), none),
        Lookup.headLookupTapes headRoles base table e⟩)
      (Lookup.headTimePolynomial.eval (GenericGraphTables.tableBits table).length) :=
  Lookup.headLookupInTime headRoles headRoles_injective
    .headTableFirst .headTableSecond .headIndexFirst .headIndexSecond
    .headHeaderVertices .headHeaderDarts Label.headLookup (some .readRelation)
    (program headerPlan rowPlan) rfl rfl rfl rfl rfl rfl (fun _ => rfl)
    base table e hTable hReverse hHead hScratch (ambient, ()) none

end Program

end BinPackingGames.Foundations.Complexity.FinalCNFMachine

namespace BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program

section

open Turing
open PCP.AlphabetTable

@[simp] theorem headerTimePolynomial_eval (length : Nat) :
    headerTimePolynomial.eval length = 25 * length + 52 := by
  simp [headerTimePolynomial]

def headerInTime (rowPlan : Plan) (n m : Nat) (rowsBits : List Bool) (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .copyFirst, ((ambient, ()), none),
        headerInputTapes (encodeWords [n, m] ++ rowsBits)⟩
      (some ⟨some .guard, ((ambient, ()), none), headerResultTapes n m rowsBits⟩)
      (headerTimePolynomial.eval (encodeWords [n, m] ++ rowsBits).length) := by
  let word := encodeWords [n, m] ++ rowsBits
  let bits := encodeWords [6 * n + 36864 * m, 40960 * m]
  let b₀ := headerInputTapes word
  let b₁ := headerFrame word word [] [] [] [] [] []
  let b₂ := headerFrame (encodeWord m ++ rowsBits) word (encodeWord n) [] [] [] [] []
  let b₃ := headerFrame rowsBits word (encodeWord n) (encodeWord m) [] [] [] []
  let b₄ := headerFrame rowsBits word (encodeWord n) (encodeWord m)
    (encodeWord 0) (encodeWord 0) (encodeWord 0) []
  let b₅ := headerFrame rowsBits word (encodeWord n) (encodeWord m)
    (encodeWord 0) (encodeWord 0) (encodeWord 0) bits.reverse
  let b₆ := headerFrame rowsBits word (encodeWord n) (encodeWord m)
    (encodeWord 0) [] (encodeWord 0) bits.reverse
  let b₇ := headerResultTapes n m rowsBits
  have h₀ : Function.update b₀ Tape.archive (b₀ .input ++ b₀ .archive) = b₁ := by
    funext tape; cases tape <;> simp [b₀, b₁, headerInputTapes, headerFrame]
  have h₁ : Hastad.SourceMachine.fieldTapes Tape.input Tape.vertices b₁
      (encodeWord m ++ rowsBits) (encodeWord n ++ b₁ .vertices) = b₂ := by
    funext tape; cases tape <;> simp [Hastad.SourceMachine.fieldTapes, b₁, b₂, headerFrame]
  have h₂ : Hastad.SourceMachine.fieldTapes Tape.input Tape.darts b₂
      rowsBits (encodeWord m ++ b₂ .darts) = b₃ := by
    funext tape; cases tape <;> simp [Hastad.SourceMachine.fieldTapes, b₂, b₃, headerFrame]
  have h₄ : Emitter.resultTapes Tape.accumulator b₄
      (Emitter.prefixBits (Emitter.listCommands headerPlan) (values n m 0 0 0)
        ambient headerPlan.length) = b₅ := by
    rw [Emitter.bits_listCommands, headerPlan_bits]
    funext tape; cases tape <;> simp [Emitter.resultTapes, b₄, b₅, bits, headerFrame]
  have h₅ : Function.update b₅ Tape.tail [] = b₆ := by
    funext tape; cases tape <;> simp [b₅, b₆, headerFrame]
  have h₆ : Function.update b₆ Tape.head [] = b₇ := by
    funext tape; cases tape <;> simp [b₆, b₇, headerResultTapes, bits, word, headerFrame]
  have hn : n ≤ word.length := by
    simp only [word, List.length_append, encodeWords_length, List.sum_cons,
      List.sum_nil, List.length_cons, List.length_nil] ; omega
  have hm : m ≤ word.length := by
    simp only [word, List.length_append, encodeWords_length, List.sum_cons,
      List.sum_nil, List.length_cons, List.length_nil] ; omega
  let p₀ := MachineCopy.copyInTime Tape.input Tape.archive Tape.scratch
    (by decide) (by decide) (by decide) false .copyFirst .copySecond (some .startVertices)
    (program headerPlan rowPlan) rfl rfl b₀ (by rfl) (ambient, ()) none
  have p₀' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .copyFirst, ((ambient, ()), none), b₀⟩
      (some ⟨some .startVertices, ((ambient, ()), none), b₁⟩) (2 * (word.length + 1)) := by
    have h := p₀
    rw [h₀] at h
    simpa only [show b₀ .input = word from rfl] using h
  let p₁ := Hastad.SourceMachine.fieldInTime Tape.input Tape.vertices (by decide)
    .startVertices .readVertices (some .startDarts) (program headerPlan rowPlan)
    rfl rfl b₁ n (encodeWord m ++ rowsBits)
    (by simp [b₁, headerFrame, word, encodeWords, List.append_assoc]) (ambient, ()) none
  have p₁' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .startVertices, ((ambient, ()), none), b₁⟩
      (some ⟨some .startDarts, ((ambient, ()), none), b₂⟩) (n + 2) := by
    simpa only [h₁] using p₁
  let p₂ := Hastad.SourceMachine.fieldInTime Tape.input Tape.darts (by decide)
    .startDarts .readDarts (some .seedIndex) (program headerPlan rowPlan)
    rfl rfl b₂ m rowsBits rfl (ambient, ()) none
  have p₂' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .startDarts, ((ambient, ()), none), b₂⟩
      (some ⟨some .seedIndex, ((ambient, ()), none), b₃⟩) (m + 2) := by
    simpa only [h₂] using p₂
  let p₃ : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .seedIndex, ((ambient, ()), none), b₃⟩
      (some ⟨some (.header (Emitter.labelAt headerPlan.length 36864 0 .entry)),
        ((ambient, ()), none), b₄⟩) 1 := {
    steps := 1
    evals_in_steps := by
      simp only [Function.iterate_one]
      change TM2.step (program headerPlan rowPlan)
        ⟨some .seedIndex, ((ambient, ()), none), b₃⟩ = _
      have ht : Function.update (Function.update (Function.update b₃ Tape.rowIndex [false])
          Tape.tail [false]) Tape.head [false] = b₄ := by
        funext tape; cases tape <;> simp [b₃, b₄, headerFrame, encodeWord]
      simp only [TM2.step, program, TM2.stepAux]
      apply congrArg some
      exact congrArg (TM2.Cfg.mk _ _) ht
    steps_le_m := Nat.le_refl _ }
  let p₄ := Emitter.planInTime (Emitter.listCommands headerPlan) source Tape.scratch
    Tape.accumulator source_ne_scratch source_ne_accumulator (by decide)
    Label.header (some .headerClearTail) (program headerPlan rowPlan) (fun _ => rfl)
    (values n m 0 0 0) b₄
    (by intro i; fin_cases i <;> rfl) rfl ambient word.length
    (by
      intro i
      fin_cases i
      · exact hn
      · exact hm
      · exact Nat.zero_le _
      · exact Nat.zero_le _
      · exact Nat.zero_le _)
  have p₄' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some (.header (Emitter.labelAt headerPlan.length 36864 0 .entry)),
        ((ambient, ()), none), b₄⟩
      (some ⟨some .headerClearTail, ((ambient, ()), none), b₅⟩)
      (7 * (3 * (word.length + 1) + 3) + 1) := by
    have h := p₄
    rw [h₄] at h
    simpa only [headerPlan_length] using h
  let p₅ := MachineLookup.discardInTime Tape.tail .headerClearTail .headerClearHead
    (program headerPlan rowPlan) rfl b₅ 0 [] (by simp [b₅, headerFrame]) (ambient, ()) none
  have p₅' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .headerClearTail, ((ambient, ()), none), b₅⟩
      (some ⟨some .headerClearHead, ((ambient, ()), none), b₆⟩) 1 := by
    simpa only [h₅] using p₅
  let p₆ := MachineLookup.discardInTime Tape.head .headerClearHead .guard
    (program headerPlan rowPlan) rfl b₆ 0 [] (by simp [b₆, headerFrame]) (ambient, ()) none
  have p₆' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .headerClearHead, ((ambient, ()), none), b₆⟩
      (some ⟨some .guard, ((ambient, ()), none), b₇⟩) 1 := by
    simpa only [h₆] using p₆
  let p₀₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀' p₁'
  let p₀₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁ p₂'
  let p₀₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂ p₃
  let p₀₁₂₃₄ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃ p₄'
  let p₀₁₂₃₄₅ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃₄ p₅'
  let p := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃₄₅ p₆'
  exact {
    toEvalsTo := p.toEvalsTo
    steps_le_m := by
      have h := p.steps_le_m
      change _ ≤ headerTimePolynomial.eval word.length
      rw [headerTimePolynomial_eval]
      omega }

def tableRowsBits (table : PCP.GenericGraphTables.Table 64) : List Bool :=
  encodeWords ((PCP.GenericGraphTables.rowList table).flatMap PCP.GenericGraphTables.rowWords)

theorem tableBits_header_rows (table : PCP.GenericGraphTables.Table 64) :
    PCP.GenericGraphTables.tableBits table =
      encodeWords [table.vertices, table.darts] ++ tableRowsBits table := by
  simp only [PCP.GenericGraphTables.tableBits, PCP.GenericGraphTables.tableWords,
    encodeWords_append, tableRowsBits]

def tableHeaderInTime (rowPlan : Plan) (table : PCP.GenericGraphTables.Table 64)
    (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .copyFirst, ((ambient, ()), none),
        headerInputTapes (PCP.GenericGraphTables.tableBits table)⟩
      (some ⟨some .guard, ((ambient, ()), none),
        headerResultTapes table.vertices table.darts (tableRowsBits table)⟩)
      (headerTimePolynomial.eval (PCP.GenericGraphTables.tableBits table).length) := by
  rw [tableBits_header_rows]
  exact headerInTime rowPlan table.vertices table.darts (tableRowsBits table) ambient

theorem headerInput_configuration (rowPlan : Plan) (input : List Bool) :
    initList (machine headerPlan rowPlan) input =
      ⟨some .copyFirst, ((((), fun _ => false), ()), none), headerInputTapes input⟩ := by
  have ht : (initList (machine headerPlan rowPlan) input).stk = headerInputTapes input := by
    funext tape
    (cases tape <;> simp [initList, machine, headerInputTapes, headerFrame]); rfl
  exact congrArg (TM2.Cfg.mk _ _) ht

def initializedTableHeaderInTime (rowPlan : Plan) (table : PCP.GenericGraphTables.Table 64) :
    StateTransition.EvalsToInTime (machine headerPlan rowPlan).step
      (initList (machine headerPlan rowPlan) (PCP.GenericGraphTables.tableBits table))
      (some ⟨some .guard, ((((), fun _ => false), ()), none),
        headerResultTapes table.vertices table.darts (tableRowsBits table)⟩)
      (headerTimePolynomial.eval (PCP.GenericGraphTables.tableBits table).length) := by
  rw [headerInput_configuration]
  exact tableHeaderInTime rowPlan table ((), fun _ => false)

end

open Turing PCP PCP.AlphabetTable

def endpointsInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (tail reverse : Nat) (rest : List Bool)
    (hinput : base .input = encodeWord tail ++ encodeWord reverse ++ rest)
    (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .startTail, ((ambient, ()), none), base⟩
      (some ⟨some .headTableFirst, ((ambient, ()), none),
        endpointTapes base tail reverse rest⟩) (tail + reverse + 4) := by
  let first := Hastad.SourceMachine.fieldTapes Tape.input Tape.tail base
    (encodeWord reverse ++ rest) (encodeWord tail ++ base .tail)
  let run₁ := Hastad.SourceMachine.fieldInTime Tape.input Tape.tail (by decide)
    .startTail .readTail (some .startReverse) (program headerPlan plan) rfl rfl
    base tail (encodeWord reverse ++ rest) (by simpa only [List.append_assoc] using hinput)
    (ambient, ()) none
  have input₁ : first .input = encodeWord reverse ++ rest := by
    simp [first, Hastad.SourceMachine.fieldTapes]
  have reverse₁ : first .reverseIndex = base .reverseIndex := by
    simp [first, Hastad.SourceMachine.fieldTapes]
  let run₂ := Hastad.SourceMachine.fieldInTime Tape.input Tape.reverseIndex (by decide)
    .startReverse .readReverse (some .headTableFirst) (program headerPlan plan) rfl rfl
    first reverse rest input₁ (ambient, ()) none
  have joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ run₂
  simpa only [first, reverse₁, endpointTapes, Nat.add_assoc,
    Nat.add_left_comm, Nat.add_comm] using joined

def relationInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (relation : GraphTables.RelationTable) (rest : List Bool)
    (hinput : base .input = encodeWords (GraphTables.relationWords relation) ++ rest)
    (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .readRelation, ((ambient, ()), none), base⟩
      (some ⟨some (.row (Emitter.labelAt plan.length 36864 0 .entry)),
        ((((), fun i => relation[i]), ()), none), Function.update base .input rest⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program headerPlan plan .readRelation) _ _) = _
    rw [program, stepAux_readRelationAt _ _ _ _ _ _ _ _ _ hinput]
  steps_le_m := Nat.le_refl _

def emitInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (operands : Fin 5 → Nat) (hoperands : ∀ i, base (source i) = encodeWord (operands i))
    (hscratch : base .scratch = []) (ambient : Ambient)
    (N : Nat) (hbounded : ∀ i, operands i ≤ N) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some (.row (Emitter.labelAt plan.length 36864 0 .entry)),
        ((ambient, ()), none), base⟩
      (some ⟨some .clearTail, ((ambient, ()), none),
        Function.update base .accumulator
          ((plan.flatMap (Emitter.commandBits operands ambient)).reverse ++ base .accumulator)⟩)
      (plan.length * (3 * (N + 1) + 3) + 1) := by
  have run := Emitter.planInTime (Emitter.listCommands plan)
    source Tape.scratch Tape.accumulator source_ne_scratch source_ne_accumulator (by decide)
    Label.row (some .clearTail) (program headerPlan plan) (fun _ => rfl)
    operands base hoperands hscratch ambient N hbounded
  simpa only [Emitter.bits_listCommands, Emitter.resultTapes] using run

def finishInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (tail head reverse row : Nat)
    (htail : base .tail = encodeWord tail) (hhead : base .head = encodeWord head)
    (hreverse : base .reverseIndex = encodeWord reverse)
    (hrow : base .rowIndex = encodeWord row) (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .clearTail, ((ambient, ()), none), base⟩
      (some ⟨some .guard, ((ambient, ()), none), finishTapes base row⟩)
      (tail + head + reverse + 4) := by
  let t₁ := Function.update base Tape.tail []
  let t₂ := Function.update t₁ Tape.head []
  let t₃ := Function.update t₂ Tape.reverseIndex []
  let run₁ := MachineLookup.discardInTime Tape.tail .clearTail .clearHead
    (program headerPlan plan) rfl base tail [] (by simpa using htail) (ambient, ()) none
  have hhead₁ : t₁ .head = encodeWord head := by simp [t₁, hhead]
  let run₂ := MachineLookup.discardInTime Tape.head .clearHead .clearReverse
    (program headerPlan plan) rfl t₁ head [] (by simpa using hhead₁) (ambient, ()) none
  have hreverse₂ : t₂ .reverseIndex = encodeWord reverse := by simp [t₂, t₁, hreverse]
  let run₃ := MachineLookup.discardInTime Tape.reverseIndex .clearReverse .nextRow
    (program headerPlan plan) rfl t₂ reverse [] (by simpa using hreverse₂) (ambient, ()) none
  let run₄ : StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .nextRow, ((ambient, ()), none), t₃⟩
      (some ⟨some .guard, ((ambient, ()), none), finishTapes base row⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change some (TM2.stepAux (program headerPlan plan .nextRow) _ _) = _
      simp only [program, TM2.stepAux]
      congr 2
      simp [t₃, t₂, t₁, finishTapes, hrow, encodeWord, List.replicate_succ]
    steps_le_m := Nat.le_refl _ }
  let r₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ run₂
  let r₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂ run₃
  have run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂₃ run₄
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using run

end BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_FinalCNFCleanup
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.FinalCNFCleanup

open Turing MachineComposition
open FinalCNFMachine (State)
open FinalCNFMachine.Program (Tape Plan)

theorem step_simulation (headerPlan rowPlan : Plan)
    (a b : (FinalCNFMachine.Program.machine headerPlan rowPlan).Cfg)
    (step : (FinalCNFMachine.Program.machine headerPlan rowPlan).step a = some b) :
    (completedMachine headerPlan rowPlan).step (embeddedCfg headerPlan rowPlan a) =
      some (embeddedCfg headerPlan rowPlan b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => simp [FinTM2.step, TM2.step] at step
    | some label =>
      have hb : TM2.stepAux (FinalCNFMachine.Program.program headerPlan rowPlan label)
          state tapes = b := Option.some.inj step
      rw [← hb]
      change some (TM2.stepAux
        (redirectStmt Sum.inl (cleanupEntry headerPlan rowPlan)
          (FinalCNFMachine.Program.program headerPlan rowPlan label)) state tapes) = _
      erw [stepAux_redirect]
      rfl

theorem finalTapes_eq (base : Tape → List Bool) :
    MachineDrainMany.finalTapes chosen base = MachineDrainMany.haltTapes .output (base .output) := by
  funext tape
  rw [MachineDrainMany.finalTapes_apply]
  simp only [mem_chosen]
  by_cases h : tape = .output
  · subst tape
    simp [MachineDrainMany.haltTapes]
  · simp [MachineDrainMany.haltTapes, h]

theorem haltList_eq (headerPlan rowPlan : Plan) (output : List Bool) :
    haltList (completedMachine headerPlan rowPlan) output =
      ⟨none, (FinalCNFMachine.Program.machine headerPlan rowPlan).initialState,
        MachineDrainMany.haltTapes .output output⟩ := by
  congr 1

def cleanupExecution (headerPlan rowPlan : Plan) (state : State Unit) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (completedMachine headerPlan rowPlan).step
      ⟨cleanupEntry headerPlan rowPlan, state, base⟩
      (some (haltList (completedMachine headerPlan rowPlan) (base .output)))
      (MachineDrainMany.steps chosen base + 1) := by
  let after : (completedMachine headerPlan rowPlan).Cfg :=
    ⟨some (resetLabel headerPlan rowPlan),
      (state.1, MachineDrainMany.finalRegister chosen state.2),
      MachineDrainMany.finalTapes chosen base⟩
  have drains : StateTransition.EvalsToInTime (completedMachine headerPlan rowPlan).step
      ⟨cleanupEntry headerPlan rowPlan, state, base⟩ (some after)
      (MachineDrainMany.steps chosen base) := {
    steps := MachineDrainMany.steps chosen base
    evals_in_steps := MachineDrainMany.trace chosen (cleanupLabel headerPlan rowPlan)
      (some (resetLabel headerPlan rowPlan)) (completedProgram headerPlan rowPlan)
      (fun _ => rfl) base state.1 state.2
    steps_le_m := le_rfl }
  have reset : StateTransition.EvalsToInTime (completedMachine headerPlan rowPlan).step
      after (some (haltList (completedMachine headerPlan rowPlan) (base .output))) 1 := {
    steps := 1
    evals_in_steps := by
      change some (⟨none, (FinalCNFMachine.Program.machine headerPlan rowPlan).initialState,
        MachineDrainMany.finalTapes chosen base⟩ : (completedMachine headerPlan rowPlan).Cfg) =
          some (haltList (completedMachine headerPlan rowPlan) (base .output))
      erw [finalTapes_eq, haltList_eq]
      rfl
    steps_le_m := le_rfl }
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans _ (MachineDrainMany.steps chosen base) 1
      _ after _ drains reset

def outputsInTime (headerPlan rowPlan : Plan) (input output : List Bool)
    (state : State Unit) (base : Tape → List Bool) (budget : Nat)
    (raw : StateTransition.EvalsToInTime
      (FinalCNFMachine.Program.machine headerPlan rowPlan).step
      (initList (FinalCNFMachine.Program.machine headerPlan rowPlan) input)
      (some ⟨none, state, base⟩) budget)
    (correctOutput : base .output = output) :
    TM2OutputsInTime (completedMachine headerPlan rowPlan) input (some output)
      (budget + 12 * (input.length + budget *
        Runtime.programPushBound (FinalCNFMachine.Program.machine headerPlan rowPlan) + 1) + 1) := by
  let lifted := liftExecutionInTime
    (FinalCNFMachine.Program.machine headerPlan rowPlan).step
    (completedMachine headerPlan rowPlan).step (embeddedCfg headerPlan rowPlan)
    (step_simulation headerPlan rowPlan) raw
  have joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ lifted
    (cleanupExecution headerPlan rowPlan state base)
  have stackBound : ∀ tape, (base tape).length ≤ input.length + budget *
      Runtime.programPushBound (FinalCNFMachine.Program.machine headerPlan rowPlan) := by
    intro tape
    have h := Runtime.executionSizeBound
      (FinalCNFMachine.Program.machine headerPlan rowPlan).step
      (fun cfg => (cfg.stk tape).length)
      (Runtime.programPushBound (FinalCNFMachine.Program.machine headerPlan rowPlan))
      (Runtime.stepStackLength (FinalCNFMachine.Program.machine headerPlan rowPlan) tape) raw
    exact h.trans (Nat.add_le_add_right
      (Runtime.initialStackLength (FinalCNFMachine.Program.machine headerPlan rowPlan) input tape) _)
  have cleanupBound := MachineDrainMany.steps_le_uniform chosen base _ stackBound
  rw [chosen_length] at cleanupBound
  rw [embedded_init, correctOutput] at joined
  exact { toEvalsTo := joined.toEvalsTo
          steps_le_m := joined.steps_le_m.trans (by omega) }

end BinPackingGames.Foundations.Complexity.FinalCNFCleanup

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RoundTableGap
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.AlphabetTable.Addresses

open BinPackingGames.Foundations.Hastad
open Enumeration

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

theorem fieldForQueryEvent_eval (n m q : Nat) (edge : Fin m) (tail head : Fin n)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6)
    (P : Fin q → Fin q → Bool) :
    eval (fieldForQueryEvent q event slot P) (values n m edge.val tail.val head.val) =
      (vertexEquiv n m q
        (.inr (Queries.globalize tail head edge (Queries.query P event slot)))).val := by
  rw [fieldForQueryEvent_eq_rawQueryField]
  exact rawQueryField_eval n m q edge tail head _

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

end BinPackingGames.Foundations.PCP.AlphabetTable.Addresses

namespace BinPackingGames.Foundations.PCP.AlphabetTableBounds

open AlphabetTable

variable {q : Nat}

theorem build_total (input : GenericGraphTables.Table q) :
    (Table.build input).vertices + (Table.build input).darts =
      input.vertices * 2 ^ q + input.darts *
        (AlphabetGraphBounds.vertexFactor q + AlphabetGraphBounds.dartFactor q) := by
  rw [build_vertices, build_darts]
  ring

theorem build_total_le (input : GenericGraphTables.Table q) :
    (Table.build input).vertices + (Table.build input).darts ≤
      AlphabetGraphBounds.sizeFactor q * (input.vertices + input.darts) := by
  rw [build_total]
  have hv : 2 ^ q ≤ AlphabetGraphBounds.sizeFactor q := by
    unfold AlphabetGraphBounds.sizeFactor
    omega
  have he : AlphabetGraphBounds.vertexFactor q + AlphabetGraphBounds.dartFactor q ≤
      AlphabetGraphBounds.sizeFactor q := by
    unfold AlphabetGraphBounds.sizeFactor
    exact Nat.add_le_add_right (Nat.le_add_left _ _) _
  calc
    _ ≤ input.vertices * AlphabetGraphBounds.sizeFactor q +
        input.darts * AlphabetGraphBounds.sizeFactor q :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hv) (Nat.mul_le_mul_left _ he)
    _ = _ := by ring

end BinPackingGames.Foundations.PCP.AlphabetTableBounds

namespace BinPackingGames.Foundations.PCP.RoundTables

def sizeFactor : Nat := AlphabetGraphBounds.sizeFactor alphabet *
  (ExpanderFamily.growth ^ 2 * (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1)))

theorem sizeFactor_positive : 0 < sizeFactor := by
  unfold sizeFactor
  apply Nat.mul_pos (AlphabetGraphBounds.sizeFactor_positive alphabet)
  apply Nat.mul_pos
  · exact Nat.pow_pos (Nat.zero_lt_one.trans ExpanderFamily.growth_gt_one)
  · omega

theorem powered_vertices (H : BaseTable) (table : GraphTables.Table) :
    (powered H table).vertices = PreprocessingTables.vertices table := rfl

end BinPackingGames.Foundations.PCP.RoundTables

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_FinalCNFRowPlan
attribute [-instance] _root_.OAI.BinPackingCompleteness.PCPSource.clauseCount_neZero _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.FinalCNFTemplate

open Target PCP

variable (V : VerifierToCNF.FiniteVerifier 12) (e : Fin V.events)
  (p : VerifierToCNF.PatternIndex 12)

def resolve : Reference → Fin (VerifierToCNF.outputVariables V)
  | .query i => VerifierToCNF.oldIndex V (V.query e i)
  | .auxiliary j => VerifierToCNF.freshIndex V e p j

theorem resolve_query_value (i : Fin 12) :
    (resolve V e p (.query i)).val = (V.query e i).val := by
  simp only [resolve, VerifierToCNF.oldIndex, Fin.val_castAdd]

theorem resolve_auxiliary_value (j : Fin 9) :
    (resolve V e p (.auxiliary j)).val =
      V.variables + ((e.val * 4096 + p.val) * 9 + j.val) := by
  change (VerifierToCNF.freshIndex V e p j).val = _
  exact (VerifierToCNF.freshIndex_value V e p j).trans
    (congrArg (fun k : Nat => V.variables + ((e.val * k + p.val) * 9 + j.val))
      (show (VerifierToCNF.patterns 12).length = 4096 from VerifierToCNF.patterns_length 12))

def instantiateLiteral (literal : LiteralTemplate) : Literal (VerifierToCNF.outputVariables V) :=
  ⟨resolve V e p literal.reference, literal.positive⟩

def instantiateClause (clause : ClauseTemplate) : Clause (VerifierToCNF.outputVariables V) :=
  #v[instantiateLiteral V e p clause[0], instantiateLiteral V e p clause[1],
    instantiateLiteral V e p clause[2]]

theorem instantiate_templates :
    (templates (V.accepts e (VerifierToCNF.patternAt 12 p))
      (VerifierToCNF.patternAt 12 p)).map (instantiateClause V e p) =
        VerifierToCNF.block V (by decide) e p := by
  cases h : V.accepts e (VerifierToCNF.patternAt 12 p) with
  | false =>
      simp only [h, templates_false, VerifierToCNF.block, Bool.false_eq_true, ↓reduceIte,
        VerifierToCNF.forbiddenClause, VerifierToCNF.auxiliaryNames]
      rw [splitLong_twelve]
      rfl
  | true =>
      simp only [h, templates_true, VerifierToCNF.block, ↓reduceIte, List.map_replicate]
      rfl

theorem instantiateClause_words (clause : ClauseTemplate) :
    Complexity.clauseWords (instantiateClause V e p clause) =
      clauseWords (fun r => (resolve V e p r).val) clause := rfl

theorem words_eq_block :
    words (V.accepts e (VerifierToCNF.patternAt 12 p)) (VerifierToCNF.patternAt 12 p)
      (fun r => (resolve V e p r).val) =
        (VerifierToCNF.block V (by decide) e p).flatMap Complexity.clauseWords := by
  rw [← instantiate_templates V e p]
  simp only [List.flatMap_map, instantiateClause_words]
  rfl

end BinPackingGames.Foundations.Complexity.FinalCNFTemplate

namespace BinPackingGames.Foundations.Complexity.FinalCNFPattern

open PCP
open scoped BigOperators

abbrev tableVerifier (table : GraphTables.Table) : VerifierToCNF.FiniteVerifier 12 :=
  FinalBooleanVerifier.verifier (tableGraph table) (Equiv.refl _) (Equiv.refl _)

theorem pattern_lookup_eq_verifier_accepts (table : GraphTables.Table)
    (e : Fin table.darts) (p : VerifierToCNF.PatternIndex 12) :
    table.rows[e].relation[patternRelationIndex p] =
      (tableVerifier table).accepts e (VerifierToCNF.patternAt 12 p) := rfl

end BinPackingGames.Foundations.Complexity.FinalCNFPattern

namespace BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program

open PCP PCP.AlphabetTable FinalCNFTemplate

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

def referenceOffset (p : VerifierToCNF.PatternIndex 12) : Reference → Fin 36864
  | .query i => ⟨if i.val < 6 then i.val else i.val - 6, by split <;> omega⟩
  | .auxiliary j => ⟨9 * p.val + j.val, by have hp := pattern_lt p; omega⟩

def literalPlan (p : VerifierToCNF.PatternIndex 12) (literal : Ambient → LiteralTemplate) : Plan :=
  [.scaledIf 0 6 (fun state => auxiliaryFlag (literal state).reference),
   .scaledIf 2 6 (fun state => tailFlag (literal state).reference),
   .scaledIf 3 6 (fun state => headFlag (literal state).reference),
   .scaledIf 4 36864 (fun state => auxiliaryFlag (literal state).reference),
   .bounded (fun state => referenceOffset p (literal state).reference),
   .literal [false],
   .bit (fun state => (literal state).positive)]

theorem literalPlan_length (p : VerifierToCNF.PatternIndex 12)
    (literal : Ambient → LiteralTemplate) : (literalPlan p literal).length = 7 := rfl

theorem literalPlan_bits (p : VerifierToCNF.PatternIndex 12)
    (literal : Ambient → LiteralTemplate) (vertices darts tail head row : Nat)
    (ambient : Ambient) :
    (literalPlan p literal).flatMap
      (Emitter.commandBits (values vertices darts tail head row) ambient) =
      encodeWords (FinalCNFTemplate.literalWords
        (referenceValue vertices tail head row p.val) (literal ambient)) := by
  rcases h : literal ambient with ⟨reference, positive⟩
  cases reference with
  | query i =>
      by_cases hi : i.val < 6
      · simp [literalPlan, Emitter.commandBits, h, auxiliaryFlag, tailFlag, headFlag,
          referenceOffset, referenceValue, FinalCNFTemplate.literalWords, values,
          hi, show ¬ 6 ≤ i.val by omega, encodeWords, encodeWord, List.replicate_add,
          List.append_assoc, -List.replicate_append_replicate]
        rfl
      · simp [literalPlan, Emitter.commandBits, h, auxiliaryFlag, tailFlag, headFlag,
          referenceOffset, referenceValue, FinalCNFTemplate.literalWords, values,
          hi, show 6 ≤ i.val by omega, encodeWords, encodeWord, List.replicate_add,
          List.append_assoc, -List.replicate_append_replicate]
        rfl
  | auxiliary j =>
      simp [literalPlan, Emitter.commandBits, h, auxiliaryFlag, tailFlag, headFlag,
        referenceOffset, referenceValue, FinalCNFTemplate.literalWords, values,
        encodeWords, encodeWord, List.replicate_add, List.append_assoc,
        -List.replicate_append_replicate]
      rfl

def patternLiteral (p : VerifierToCNF.PatternIndex 12) (clause : Fin 10) (slot : Fin 3)
    (ambient : Ambient) : LiteralTemplate :=
  literalAt (ambient.2 (FinalCNFPattern.patternRelationIndex p))
    (VerifierToCNF.patternAt 12 p) clause slot

def patternPlan (p : VerifierToCNF.PatternIndex 12) : Plan :=
  (List.finRange 10).flatMap fun clause =>
    (List.finRange 3).flatMap fun slot => literalPlan p (patternLiteral p clause slot)

def rowPlan : Plan :=
  (List.finRange (VerifierToCNF.patterns 12).length).flatMap patternPlan

theorem patternPlan_length (p : VerifierToCNF.PatternIndex 12) :
    (patternPlan p).length = 210 := by
  unfold patternPlan
  rw [VerifierToCNF.length_flatMap_constant _ _ 21]
  · simp
  · intro clause hclause
    rw [VerifierToCNF.length_flatMap_constant _ _ 7]
    · simp
    · intro slot hslot
      exact literalPlan_length _ _

theorem rowPlan_length : rowPlan.length = 860160 := by
  unfold rowPlan
  rw [VerifierToCNF.length_flatMap_constant _ _ 210]
  · rw [List.length_finRange, VerifierToCNF.patterns_length]
    norm_num
  · intro p hp
    exact patternPlan_length p

theorem encodeWords_flatMap {α : Type*} (xs : List α) (words : α → List Nat) :
    encodeWords (xs.flatMap words) = xs.flatMap (fun x => encodeWords (words x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem patternPlan_bits (p : VerifierToCNF.PatternIndex 12)
    (vertices darts tail head row : Nat) (ambient : Ambient) :
    (patternPlan p).flatMap
      (Emitter.commandBits (values vertices darts tail head row) ambient) =
      encodeWords (FinalCNFTemplate.words
        (ambient.2 (FinalCNFPattern.patternRelationIndex p))
        (VerifierToCNF.patternAt 12 p) (referenceValue vertices tail head row p.val)) := by
  unfold patternPlan
  simp only [List.flatMap_assoc]
  simp_rw [literalPlan_bits]
  have hclauses :
      (List.finRange 10).map
        (fun c => (blockTemplates (ambient.2 (FinalCNFPattern.patternRelationIndex p))
          (VerifierToCNF.patternAt 12 p))[c]) =
      templates (ambient.2 (FinalCNFPattern.patternRelationIndex p))
        (VerifierToCNF.patternAt 12 p) := by
    rw [← List.ofFn_eq_map]
    change List.ofFn (fun c : Fin 10 =>
      (blockTemplates (ambient.2 (FinalCNFPattern.patternRelationIndex p))
        (VerifierToCNF.patternAt 12 p))[c.val]) = _
    rw [← Vector.toList_ofFn, Vector.ofFn_getElem]
    rfl
  unfold FinalCNFTemplate.words
  rw [← hclauses, List.flatMap_map, encodeWords_flatMap]
  apply List.flatMap_congr
  intro clause hclause
  simp only [List.finRange, List.ofFn_succ, List.ofFn_zero, List.flatMap_cons,
    List.flatMap_nil, patternLiteral, literalAt, FinalCNFTemplate.clauseWords,
    encodeWords_append, List.append_nil, List.append_assoc]
  rfl

theorem referenceValue_eq_resolve (table : GraphTables.Table) (e : Fin table.darts)
    (p : VerifierToCNF.PatternIndex 12) (reference : Reference) :
    referenceValue table.vertices table.rows[e].tail.val
      table.rows[table.rows[e].reverseIndex].tail.val e.val p.val reference =
      (resolve (FinalCNFPattern.tableVerifier table) e p reference).val := by
  cases reference with
  | query i =>
      rw [resolve_query_value]
      refine Fin.addCases (m := 6) (n := 6) (fun j => ?_) (fun j => ?_) i
      · rw [FinalBooleanVerifier.query_tail]
        simp only [referenceValue, Fin.val_castAdd, j.isLt, ite_true, if_true]
        change 6 * table.rows[e].tail.val + j.val = j.val + 6 * table.rows[e].tail.val
        omega
      · rw [FinalBooleanVerifier.query_head]
        simp only [referenceValue, Fin.val_natAdd]
        split
        · omega
        · change 6 * table.rows[table.rows[e].reverseIndex].tail.val +
              (6 + j.val - 6) = j.val + 6 * table.rows[table.rows[e].reverseIndex].tail.val
          omega
  | auxiliary j =>
      rw [resolve_auxiliary_value]
      change 6 * table.vertices + 36864 * e.val + (9 * p.val + j.val) =
        table.vertices * 6 + ((e.val * 4096 + p.val) * 9 + j.val)
      omega

theorem rowPlan_bits (table : GraphTables.Table) (e : Fin table.darts) :
    rowPlan.flatMap (Emitter.commandBits
      (values table.vertices table.darts table.rows[e].tail.val
        table.rows[table.rows[e].reverseIndex].tail.val e.val)
      ((), fun i => table.rows[e].relation[i])) =
      encodeWords ((VerifierToCNF.eventBlock (FinalCNFPattern.tableVerifier table)
        (by decide) e).flatMap Complexity.clauseWords) := by
  unfold rowPlan VerifierToCNF.eventBlock
  simp only [List.flatMap_assoc]
  rw [encodeWords_flatMap]
  apply List.flatMap_congr
  intro p hp
  rw [patternPlan_bits]
  dsimp only
  rw [FinalCNFPattern.pattern_lookup_eq_verifier_accepts]
  have href := funext (referenceValue_eq_resolve table e p)
  rw [href]
  exact congrArg encodeWords (words_eq_block (FinalCNFPattern.tableVerifier table) e p)

end BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_GraphCounterStart
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.GraphCounterModel

open Turing

def startInTime (n m : Nat) (rest : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (initList machine (encodeWords [n, m] ++ rest))
      (some (clockConfiguration (startExtra rest (encodeWords [n, m] ++ rest)) none
        (initList MachineLogCounter.machine (encodeWord (n + m)))))
      (2 * ((encodeWords [n, m] ++ rest).length + 1) + 1 + (n + 1) + (m + 1)) := by
  let word := encodeWords [n, m] ++ rest
  let b₀ := startMemory word [] []
  let b₁ := startMemory word word []
  let b₂ := startMemory word word (encodeWord 0)
  have hc : Function.update b₀ (.inr .archive) (b₀ (.inr .input) ++ b₀ (.inr .archive)) = b₁ := by
    funext tape
    cases tape with
    | inl k => simp [b₀, b₁, startMemory]
    | inr k => cases k <;> simp [b₀, b₁, startMemory, startExtra]
  let copy := MachineCopy.copyInTime (.inr ExtraTape.input) (.inr ExtraTape.archive)
    (.inr ExtraTape.scratch) (by decide) (by decide) (by decide) false
    (.inr ExtraLabel.copyFirst) (.inr ExtraLabel.copySecond) (some (.inr ExtraLabel.seed))
    program rfl rfl b₀ rfl MachineLogCounter.initialState none
  have copy' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr .copyFirst), initialState, b₀⟩
      (some ⟨some (.inr .seed), initialState, b₁⟩) (2 * (word.length + 1)) := by
    have h := copy
    rw [hc] at h
    simpa only [initialState, show b₀ (.inr .input) = word from rfl] using h
  have seed : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr .seed), initialState, b₁⟩
      (some ⟨some (.inr .headerFirst), initialState, b₂⟩) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change some (TM2.stepAux (program (.inr .seed)) initialState b₁) = _
    simp only [program, TM2.stepAux, b₁, startMemory]
    rw [startMemory_sum_update]
    rfl
  have first := headerInTime (.inr .headerFirst) (.inr .headerSecond) rfl
    n 0 (encodeWord m ++ rest) word MachineLogCounter.initialState none
  have first' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr .headerFirst), initialState, b₂⟩
      (some ⟨some (.inr .headerSecond), initialState,
        startMemory (encodeWord m ++ rest) word (encodeWord n)⟩) (n + 1) := by
    simpa only [b₂, initialState, word, encodeWords, List.append_nil, List.append_assoc,
      Nat.add_zero] using first
  have second := headerInTime (.inr .headerSecond) (.inl 0) rfl
    m n rest word MachineLogCounter.initialState none
  have second' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr .headerSecond), initialState,
        startMemory (encodeWord m ++ rest) word (encodeWord n)⟩
      (some ⟨some (.inl 0), initialState, startMemory rest word (encodeWord (n + m))⟩)
      (m + 1) := by simpa only [initialState, Nat.add_comm m n] using second
  let p₀ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ copy' seed
  let p₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀ first'
  let p := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₁ second'
  rw [initialMemory, clockInitialMemory]
  exact {
    toEvalsTo := p.toEvalsTo
    steps_le_m := by
      have h := p.steps_le_m
      change p.steps ≤ 2 * (word.length + 1) + 1 + (n + 1) + (m + 1)
      omega
  }

end BinPackingGames.Foundations.Complexity.GraphCounterModel

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_PCPSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.FinalTableFormula

open Target Complexity

theorem formulaBits_length_le_polynomial (table : GraphTables.Table) :
    (formulaBits (output table)).length ≤
      sizePolynomial.eval (GraphTables.tableBits table).length := by
  have hinput := GraphTableComplexity.size_add_two_le_bits table
  have hv : (output table).variables ≤ 36864 * (GraphTables.tableBits table).length := by
    rw [variable_count]
    omega
  have hc : (output table).clauses.length ≤ 40960 * (GraphTables.tableBits table).length := by
    rw [clause_count]
    omega
  have hsum : (output table).variables + (output table).clauses.length + 2 ≤
      77824 * (GraphTables.tableBits table).length + 2 := by omega
  have hproduct := Nat.mul_le_mul hc (Nat.mul_le_mul_left 3 (Nat.add_le_add_right hv 2))
  rw [sizePolynomial_eval]
  exact (formulaBits_length_le (output table)).trans (Nat.add_le_add hsum hproduct)

end BinPackingGames.Foundations.PCP.FinalTableFormula

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_GraphIterationBounds
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.GraphCounterFinish

open Turing GraphCounterModel

theorem drainTrace (rest original counter : List Bool) :
    (MachineComposition.advance (TM2.step program))^[rest.length + 1]
      (some ⟨some (.inr .clearInput), initialState, frame rest original counter [] []⟩) =
      some ⟨some (.inr .clockCopy), initialState, frame [] original counter [] []⟩ := by
  have h := (MachineDrain.drainInTime (Sum.inr ExtraTape.input) (Sum.inr ExtraLabel.clearInput)
    (some (.inr .clockCopy)) program rfl (frame rest original counter [] [])
    MachineLogCounter.initialState none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[rest.length + 1]
    (some ⟨some (.inr .clearInput), initialState, frame rest original counter [] []⟩) = _ at h
  have update : Function.update (frame rest original counter [] []) (.inr .input) [] =
      frame [] original counter [] [] := by
    funext tape
    cases tape with
    | inl i => simp [frame]
    | inr k => cases k <;> simp [frame]
  simpa only [update, initialState] using h

theorem finishTrace (counter rest original : List Bool) :
    (MachineComposition.advance (TM2.step program))^[
        rest.length + 2 * counter.length + 2 * original.length + 4]
      (some (clockConfiguration (extraTapes rest original) none
        (haltList MachineLogCounter.machine counter))) =
      some (haltList machine (counter ++ original)) := by
  rw [start_eq]
  have total := trace_trans _
    (trace_trans _ (trace_trans _ (drainTrace rest original counter)
      (clockCopyTrace original counter)) (archiveCopyTrace original counter))
    (reverseTrace original counter)
  simpa only [show rest.length + 1 + (counter.length + 1) + (original.length + 1) +
      (original.length + counter.length + 1) =
      rest.length + 2 * counter.length + 2 * original.length + 4 by omega] using total

def finishInTime (counter rest original : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      (clockConfiguration (extraTapes rest original) none (haltList MachineLogCounter.machine counter))
      (some (haltList machine (counter ++ original)))
      (rest.length + 2 * counter.length + 2 * original.length + 4) where
  steps := rest.length + 2 * counter.length + 2 * original.length + 4
  evals_in_steps := finishTrace counter rest original
  steps_le_m := le_rfl

end BinPackingGames.Foundations.Complexity.GraphCounterFinish

namespace BinPackingGames.Foundations.Complexity.GraphCounterPrefix

open Turing PCP GraphCounterModel GraphCounterFinish

def rawOutput (n m : Nat) (rest : List Bool) : List Bool :=
  encodeWord ((n + m).log2 + 1) ++ (encodeWords [n, m] ++ rest)

def rawInTime (n m : Nat) (rest : List Bool) :
    TM2OutputsInTime machine (encodeWords [n, m] ++ rest) (some (rawOutput n m rest))
      (20 * (encodeWords [n, m] ++ rest).length + 30) := by
  let original := encodeWords [n, m] ++ rest
  let start := startInTime n m rest
  let clock := clockInTime (extraTapes rest original) none (n + m)
  let finish := finishInTime (encodeWord ((n + m).log2 + 1)) rest original
  have start' : StateTransition.EvalsToInTime (TM2.step program)
      (initList machine original)
      (some (clockConfiguration (extraTapes rest original) none
        (initList MachineLogCounter.machine (encodeWord (n + m)))))
      (2 * (original.length + 1) + 1 + (n + 1) + (m + 1)) := start
  let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ start' clock
  let total := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first finish
  refine { toEvalsTo := total.toEvalsTo, steps_le_m := ?_ }
  have bound := total.steps_le_m
  have hlog := Nat.log2_le_self (n + m)
  have hlength : original.length = n + m + 2 + rest.length := by
    simp only [original, List.length_append, encodeWords, encodeWord_length, List.length_nil]
    omega
  simp only [encodeWord_length] at bound
  change total.steps ≤ 20 * original.length + 30
  omega

def count (table : GraphTables.Table) : Nat := (table.vertices + table.darts).log2 + 1

def output (table : GraphTables.Table) : List Bool :=
  encodeWord (count table) ++ GraphTables.tableBits table

def rowsBits (table : GraphTables.Table) : List Bool :=
  encodeWords ((GraphTables.rowList table).flatMap GraphTables.rowWords)

theorem tableBits_decomposition (table : GraphTables.Table) :
    GraphTables.tableBits table = encodeWords [table.vertices, table.darts] ++ rowsBits table :=
  encodeWords_append _ _

def outputsInTime (table : GraphTables.Table) :
    TM2OutputsInTime machine (GraphTables.tableBits table) (some (output table))
      (20 * (GraphTables.tableBits table).length + 30) := by
  have run := rawInTime table.vertices table.darts (rowsBits table)
  simpa only [rawOutput, output, count, tableBits_decomposition] using run

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime GraphTables.tableBits id output where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 20 * Polynomial.X + 30
  outputsFun table := by
    change TM2OutputsInTime machine ((GraphTables.tableBits table).map id)
      (some ((output table).map id))
      ((20 * Polynomial.X + 30 : Polynomial Nat).eval (GraphTables.tableBits table).length)
    erw [List.map_id, List.map_id]
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X] using outputsInTime table

end BinPackingGames.Foundations.Complexity.GraphCounterPrefix

namespace BinPackingGames.Foundations.Complexity.GraphIterationBounds

open PCP RoundTables

def inputBits (input : Input) : List Bool := GraphTables.tableBits input.val

def countedBits (input : Input) : List Bool := GraphCounterPrefix.output input.val

def words (H : BaseTable) (input : Input) (i : Nat) : List Bool :=
  GraphTables.tableBits (TableIteration.runTables H i input.val)

def count (input : Input) : Nat := GraphCounterPrefix.count input.val

noncomputable def lengthPolynomial : Polynomial Nat :=
  (GraphTableComplexity.encodingPolynomial 64).comp (PCPIterationMachine.sizePolynomial sizeFactor)

theorem inputBits_le_countedBits (input : Input) : (inputBits input).length ≤ (countedBits input).length := by
  simp only [inputBits, countedBits, GraphCounterPrefix.output, List.length_append]
  omega

theorem size_le_inputBits (input : Input) : size input ≤ (inputBits input).length := by
  have h := GraphTableComplexity.size_add_two_le_bits input.val
  unfold size inputBits
  omega

theorem count_le (input : Input) : count input ≤ (countedBits input).length + 1 :=
  (PCPIterationMachine.rounds_le (size input)).trans
    (Nat.add_le_add_right ((size_le_inputBits input).trans (inputBits_le_countedBits input)) 1)

noncomputable def runtimePolynomial (bodyTime : Polynomial Nat) : Polynomial Nat :=
  (Polynomial.X + 1) * (bodyTime.comp lengthPolynomial + 2 * lengthPolynomial + 4) +
    2 * lengthPolynomial + 4

theorem runtimePolynomial_eval (bodyTime : Polynomial Nat) (N : Nat) :
    (runtimePolynomial bodyTime).eval N =
      (N + 1) * (bodyTime.eval (lengthPolynomial.eval N) + 2 * lengthPolynomial.eval N + 4) +
        2 * lengthPolynomial.eval N + 4 := by
  simp only [runtimePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_ofNat, Polynomial.eval_comp]

end BinPackingGames.Foundations.Complexity.GraphIterationBounds

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RawInitialMachineLoopData
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.RawInitialMachineStart

open Turing Complexity Hastad RawInitialMachineModel

theorem readCountersTrace (n m : ℕ) (clauseBits : List Bool) :
    (MachineComposition.advance (TM2.step program))^[n + m + 4]
      (some (initList machine (encodeWords [n, m] ++ clauseBits))) =
      some ⟨some .scanN, initialState, counterTapes n m clauseBits⟩ := by
  let t0 := inputTapes (encodeWords [n, m] ++ clauseBits)
  have first := (SourceMachine.fieldInTime .input .variables (by decide)
    (.headerStart 0) (.headerLoop 0) (some (.headerStart 1)) program rfl rfl
    t0 n (encodeWord m ++ clauseBits)
    (by simp [t0, inputTapes, encodeWords, List.append_assoc])
    (false, false, false) none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[n + 2]
    (some ⟨some (.headerStart 0), initialState, t0⟩) = _ at first
  have firstFrame : SourceMachine.fieldTapes .input .variables t0
      (encodeWord m ++ clauseBits) (encodeWord n ++ t0 .variables) =
      firstTapes n m clauseBits := by
    funext k
    cases k <;> simp [SourceMachine.fieldTapes, t0, inputTapes, firstTapes]
  rw [firstFrame] at first
  have second := (SourceMachine.fieldInTime .input .counter (by decide)
    (.headerStart 1) (.headerLoop 1) (some .scanN) program rfl rfl
    (firstTapes n m clauseBits) m clauseBits rfl (false, false, false) none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[m + 2]
    (some ⟨some (.headerStart 1), initialState, firstTapes n m clauseBits⟩) = _ at second
  have secondFrame : SourceMachine.fieldTapes .input .counter (firstTapes n m clauseBits)
      clauseBits (encodeWord m ++ firstTapes n m clauseBits .counter) =
      counterTapes n m clauseBits := by
    funext k
    cases k <;> simp [SourceMachine.fieldTapes, firstTapes, counterTapes]
  rw [secondFrame] at second
  have total := trace_trans _ first second
  rw [show (n + 2) + (m + 2) = n + m + 4 by omega] at total
  simpa only [initList_eq, t0, initialState] using! total

theorem startTrace (n m : ℕ) (clauseBits : List Bool) :
    (MachineComposition.advance (TM2.step program))^[3 * n + 5 * m + 13]
      (some (initList machine (encodeWords [n, m] ++ clauseBits))) =
      some ⟨some .guard, initialState, startTapes n m clauseBits⟩ := by
  have total := trace_trans _
    (trace_trans _ (readCountersTrace n m clauseBits) (headersTrace n m clauseBits))
    (initializeIndexTrace n m clauseBits)
  simpa only [show (n + m + 4) + (2 * n + 4 * m + 8) + 1 =
    3 * n + 5 * m + 13 by omega] using total

end BinPackingGames.Foundations.PCP.RawInitialMachineStart

namespace BinPackingGames.Foundations.PCP.RawInitialMachinePhases

open Turing Complexity RawInitialMachineModel

def cleanupFieldInTime (slot : Fin 6) (base : Tape → List Bool) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.cleanupField slot), state, base⟩
      (some ⟨some (if h : slot.val + 1 < 6 then .cleanupField ⟨slot.val + 1, h⟩
        else .incrementIndex), (state.1, none), Function.update base (.field slot) []⟩)
      ((base (.field slot)).length + 1) :=
  MachineDrain.drainInTime (.field slot) (.cleanupField slot) _ program rfl base state.1 state.2

def cleanupFinalInTime (slot : Fin 3) (base : Tape → List Bool) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.cleanupFinal slot), state, base⟩
      (some ⟨some (if h : slot.val + 1 < 3 then .cleanupFinal ⟨slot.val + 1, h⟩
        else .reset), (state.1, none), Function.update base (finalTape slot) []⟩)
      ((base (finalTape slot)).length + 1) :=
  MachineDrain.drainInTime (finalTape slot) (.cleanupFinal slot) _ program rfl base state.1 state.2

end BinPackingGames.Foundations.PCP.RawInitialMachinePhases

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RawInitialMachineReadClause
attribute [-instance] _root_.OAI.BinPackingCompleteness.PCPSource.clauseCount_neZero _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.RawInitialMachineReadClause

open Turing Complexity Hastad RawInitialMachineModel

theorem fieldsTrace {n : ℕ} (base : Tape → List Bool) (c : Target.Clause n)
    (suffix : List Bool)
    (hinput : base .input = encodeWords (Complexity.clauseWords c) ++ suffix)
    (hempty : ∀ j, base (.field j) = []) (state : State) :
    (MachineComposition.advance (TM2.step program))^[
        (encodeWords (Complexity.clauseWords c)).length + 6]
      (some ⟨some (.fieldStart 0), state, base⟩) =
      some ⟨some .loadSigns, (state.1, none), recordTapes base c suffix⟩ := by
  let a := fieldValue c 0
  let b := fieldValue c 1
  let d := fieldValue c 2
  let e := fieldValue c 3
  let f := fieldValue c 4
  let g := fieldValue c 5
  have hwords : Complexity.clauseWords c = [a, b, d, e, f, g] := rfl
  have hin : base .input = encodeWord a ++ (encodeWords [b, d, e, f, g] ++ suffix) := by
    rw [hinput, hwords]
    simp only [encodeWords, List.append_assoc]
  let t1 := SourceMachine.afterField .input (.field 0) base a
    (encodeWords [b, d, e, f, g] ++ suffix)
  let t2 := SourceMachine.afterField .input (.field 1) t1 b
    (encodeWords [d, e, f, g] ++ suffix)
  let t3 := SourceMachine.afterField .input (.field 2) t2 d
    (encodeWords [e, f, g] ++ suffix)
  let t4 := SourceMachine.afterField .input (.field 3) t3 e
    (encodeWords [f, g] ++ suffix)
  let t5 := SourceMachine.afterField .input (.field 4) t4 f
    (encodeWords [g] ++ suffix)
  let t6 := SourceMachine.afterField .input (.field 5) t5 g suffix
  have h1 := (SourceMachine.fieldInTime .input (.field 0) (by decide)
    (.fieldStart 0) (.fieldLoop 0) (some (.fieldStart 1)) program rfl rfl
    base a (encodeWords [b, d, e, f, g] ++ suffix) hin state.1 state.2).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[a + 2]
    (some ⟨some (.fieldStart 0), state, base⟩) =
    some ⟨some (.fieldStart 1), (state.1, none), t1⟩ at h1
  have h2 := (SourceMachine.fieldInTime .input (.field 1) (by decide)
    (.fieldStart 1) (.fieldLoop 1) (some (.fieldStart 2)) program rfl rfl
    t1 b (encodeWords [d, e, f, g] ++ suffix)
    (by simp [t1, SourceMachine.afterField, encodeWords, List.append_assoc])
    state.1 none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[b + 2]
    (some ⟨some (.fieldStart 1), (state.1, none), t1⟩) =
    some ⟨some (.fieldStart 2), (state.1, none), t2⟩ at h2
  have h3 := (SourceMachine.fieldInTime .input (.field 2) (by decide)
    (.fieldStart 2) (.fieldLoop 2) (some (.fieldStart 3)) program rfl rfl
    t2 d (encodeWords [e, f, g] ++ suffix)
    (by simp [t2, SourceMachine.afterField, encodeWords, List.append_assoc])
    state.1 none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[d + 2]
    (some ⟨some (.fieldStart 2), (state.1, none), t2⟩) =
    some ⟨some (.fieldStart 3), (state.1, none), t3⟩ at h3
  have h4 := (SourceMachine.fieldInTime .input (.field 3) (by decide)
    (.fieldStart 3) (.fieldLoop 3) (some (.fieldStart 4)) program rfl rfl
    t3 e (encodeWords [f, g] ++ suffix)
    (by simp [t3, SourceMachine.afterField, encodeWords, List.append_assoc])
    state.1 none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[e + 2]
    (some ⟨some (.fieldStart 3), (state.1, none), t3⟩) =
    some ⟨some (.fieldStart 4), (state.1, none), t4⟩ at h4
  have h5 := (SourceMachine.fieldInTime .input (.field 4) (by decide)
    (.fieldStart 4) (.fieldLoop 4) (some (.fieldStart 5)) program rfl rfl
    t4 f (encodeWords [g] ++ suffix)
    (by simp [t4, SourceMachine.afterField, encodeWords, List.append_assoc])
    state.1 none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[f + 2]
    (some ⟨some (.fieldStart 4), (state.1, none), t4⟩) =
    some ⟨some (.fieldStart 5), (state.1, none), t5⟩ at h5
  have h6 := (SourceMachine.fieldInTime .input (.field 5) (by decide)
    (.fieldStart 5) (.fieldLoop 5) (some .loadSigns) program rfl rfl
    t5 g suffix
    (by simp [t5, SourceMachine.afterField, encodeWords])
    state.1 none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[g + 2]
    (some ⟨some (.fieldStart 5), (state.1, none), t5⟩) =
    some ⟨some .loadSigns, (state.1, none), t6⟩ at h6
  have total := trace_trans _ (trace_trans _ (trace_trans _
    (trace_trans _ (trace_trans _ h1 h2) h3) h4) h5) h6
  have htime : (((((a + 2) + (b + 2)) + (d + 2)) + (e + 2)) + (f + 2)) + (g + 2) =
      (encodeWords (Complexity.clauseWords c)).length + 6 := by
    rw [hwords, encodeWords_length]
    simp
    omega
  rw [htime] at total
  have frame : t6 = recordTapes base c suffix := by
    funext k
    cases k with
    | field j =>
      fin_cases j <;>
        simp [t6, t5, t4, t3, t2, t1, SourceMachine.afterField, SourceMachine.fieldTapes,
          recordTapes, hempty, a, b, d, e, f, g]
    | _ =>
      simp [t6, t5, t4, t3, t2, t1, SourceMachine.afterField, SourceMachine.fieldTapes,
        recordTapes]
  rw [frame] at total
  exact total

theorem readClauseTrace {n : ℕ} (base : Tape → List Bool) (c : Target.Clause n)
    (suffix : List Bool)
    (hinput : base .input = encodeWords (Complexity.clauseWords c) ++ suffix)
    (hempty : ∀ j, base (.field j) = []) (state : State) :
    (MachineComposition.advance (TM2.step program))^[
        (encodeWords (Complexity.clauseWords c)).length + 7]
      (some ⟨some (.fieldStart 0), state, base⟩) =
      some ⟨some (.scan (.tailVariables 0)), (RawInitialRows.clauseSigns c, none),
        recordTapes base c suffix⟩ := by
  have first := fieldsTrace base c suffix hinput hempty state
  have last := RawInitialMachinePhases.loadSigns_step (recordTapes base c suffix)
    (c)[0].positive (c)[1].positive (c)[2].positive rfl rfl rfl (state.1, none)
  have lastTrace : (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .loadSigns, (state.1, none), recordTapes base c suffix⟩) =
      some ⟨some (.scan (.tailVariables 0)), (RawInitialRows.clauseSigns c, none),
        recordTapes base c suffix⟩ := last
  have total := trace_trans _ first lastTrace
  simpa only [show (encodeWords (Complexity.clauseWords c)).length + 6 + 1 =
    (encodeWords (Complexity.clauseWords c)).length + 7 by omega] using total

end BinPackingGames.Foundations.PCP.RawInitialMachineReadClause

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RawInitialMachineCleanup
attribute [-instance] _root_.OAI.BinPackingCompleteness.PCPSource.clauseCount_neZero _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.RawInitialMachineCleanup

open Turing Complexity RawInitialMachineModel RawInitialMachineReadClause

theorem cleanupTrace {n : ℕ} (base : Tape → List Bool) (c : Target.Clause n)
    (suffix : List Bool) (i : ℕ)
    (hempty : ∀ j, base (.field j) = []) (hindex : base .index = encodeWord i)
    (incoming : State) :
    (MachineComposition.advance (TM2.step program))^[
        (encodeWords (Complexity.clauseWords c)).length + 7]
      (some ⟨some (.cleanupField 0), incoming, recordTapes base c suffix⟩) =
      some ⟨some .guard, (incoming.1, none),
        Function.update (Function.update base .input suffix) .index (encodeWord (i + 1))⟩ := by
  let r := recordTapes base c suffix
  let t1 := Function.update r (.field 0) []
  let t2 := Function.update t1 (.field 1) []
  let t3 := Function.update t2 (.field 2) []
  let t4 := Function.update t3 (.field 3) []
  let t5 := Function.update t4 (.field 4) []
  let t6 := Function.update t5 (.field 5) []
  have h1 := (RawInitialMachinePhases.cleanupFieldInTime 0 r incoming).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[
      (encodeWord (fieldValue c 0)).length + 1]
    (some ⟨some (.cleanupField 0), incoming, r⟩) =
    some ⟨some (.cleanupField 1), (incoming.1, none), t1⟩ at h1
  have h2 := (RawInitialMachinePhases.cleanupFieldInTime 1 t1 (incoming.1, none)).evals_in_steps
  have hf2 : t1 (.field 1) = encodeWord (fieldValue c 1) := by
    simp [t1, r]
  change (MachineComposition.advance (TM2.step program))^[(t1 (.field 1)).length + 1]
    (some ⟨some (.cleanupField 1), (incoming.1, none), t1⟩) =
    some ⟨some (.cleanupField 2), (incoming.1, none), t2⟩ at h2
  rw [hf2] at h2
  have h3 := (RawInitialMachinePhases.cleanupFieldInTime 2 t2 (incoming.1, none)).evals_in_steps
  have hf3 : t2 (.field 2) = encodeWord (fieldValue c 2) := by
    simp [t2, t1, r]
  change (MachineComposition.advance (TM2.step program))^[(t2 (.field 2)).length + 1]
    (some ⟨some (.cleanupField 2), (incoming.1, none), t2⟩) =
    some ⟨some (.cleanupField 3), (incoming.1, none), t3⟩ at h3
  rw [hf3] at h3
  have h4 := (RawInitialMachinePhases.cleanupFieldInTime 3 t3 (incoming.1, none)).evals_in_steps
  have hf4 : t3 (.field 3) = encodeWord (fieldValue c 3) := by
    simp [t3, t2, t1, r]
  change (MachineComposition.advance (TM2.step program))^[(t3 (.field 3)).length + 1]
    (some ⟨some (.cleanupField 3), (incoming.1, none), t3⟩) =
    some ⟨some (.cleanupField 4), (incoming.1, none), t4⟩ at h4
  rw [hf4] at h4
  have h5 := (RawInitialMachinePhases.cleanupFieldInTime 4 t4 (incoming.1, none)).evals_in_steps
  have hf5 : t4 (.field 4) = encodeWord (fieldValue c 4) := by
    simp [t4, t3, t2, t1, r]
  change (MachineComposition.advance (TM2.step program))^[(t4 (.field 4)).length + 1]
    (some ⟨some (.cleanupField 4), (incoming.1, none), t4⟩) =
    some ⟨some (.cleanupField 5), (incoming.1, none), t5⟩ at h5
  rw [hf5] at h5
  have h6 := (RawInitialMachinePhases.cleanupFieldInTime 5 t5 (incoming.1, none)).evals_in_steps
  have hf6 : t5 (.field 5) = encodeWord (fieldValue c 5) := by
    simp [t5, t4, t3, t2, t1, r]
  change (MachineComposition.advance (TM2.step program))^[(t5 (.field 5)).length + 1]
    (some ⟨some (.cleanupField 5), (incoming.1, none), t5⟩) =
    some ⟨some .incrementIndex, (incoming.1, none), t6⟩ at h6
  rw [hf6] at h6
  have last := incrementIndexTrace t6 (incoming.1, none)
  have total := trace_trans _ (trace_trans _ (trace_trans _ (trace_trans _
    (trace_trans _ (trace_trans _ h1 h2) h3) h4) h5) h6) last
  have htime :
      ((((((encodeWord (fieldValue c 0)).length + 1 +
        ((encodeWord (fieldValue c 1)).length + 1)) +
        ((encodeWord (fieldValue c 2)).length + 1)) +
        ((encodeWord (fieldValue c 3)).length + 1)) +
        ((encodeWord (fieldValue c 4)).length + 1)) +
        ((encodeWord (fieldValue c 5)).length + 1)) + 1 =
      (encodeWords (Complexity.clauseWords c)).length + 7 := by
    simp [fieldValue, Complexity.clauseWords, Complexity.literalWords, encodeWords]
    omega
  rw [htime] at total
  have frame : Function.update t6 .index (true :: t6 .index) =
      Function.update (Function.update base .input suffix) .index (encodeWord (i + 1)) := by
    funext k
    cases k with
    | field j =>
      fin_cases j <;> simp [t6, t5, t4, t3, t2, t1, r, recordTapes, hempty]
    | index =>
      simp [t6, t5, t4, t3, t2, t1, r, recordTapes, hindex,
        encodeWord, List.replicate_succ]
    | _ => simp [t6, t5, t4, t3, t2, t1, r, recordTapes]
  rw [frame] at total
  exact total

end BinPackingGames.Foundations.PCP.RawInitialMachineCleanup

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RawInitialMachineBody
attribute [-instance] _root_.OAI.BinPackingCompleteness.PCPSource.clauseCount_neZero _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.RawInitialMachineBody

open Turing Target Complexity RawInitialMachineModel RawInitialMachineLoopData
open RawInitialMachineReadClause RawInitialMachineRows RawInitialMachineBudget

theorem bodyTrace {n : Nat} (i remaining : Nat) (c : Clause n)
    (suffix reversed : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[bodyTime i c]
      (some ⟨some .guard, state,
        loopTapes n i (remaining + 1)
          (encodeWords (Complexity.clauseWords c) ++ suffix) reversed⟩) =
      some ⟨some .guard, (RawInitialRows.clauseSigns c, none),
        loopTapes n (i + 1) remaining suffix
          ((encodeWords (RawInitialRows.clauseWords n i
            (RawInitialRows.clauseNames c) (RawInitialRows.clauseSigns c))).reverse ++ reversed)⟩ := by
  let input := encodeWords (Complexity.clauseWords c) ++ suffix
  let base := loopTapes n i remaining input reversed
  let chunk := (encodeWords (RawInitialRows.clauseWords n i
    (RawInitialRows.clauseNames c) (RawInitialRows.clauseSigns c))).reverse
  let emitted := loopTapes n i remaining input (chunk ++ reversed)
  have first := guardTrace_succ n i remaining input reversed state
  have read := readClauseTrace base c suffix rfl (fun _ => rfl) (state.1, none)
  have rows := rowsTrace (recordTapes base c suffix) n i
    (RawInitialRows.clauseNames c) (RawInitialRows.clauseSigns c)
    rfl rfl rfl rfl rfl rfl
  have frame : outputTapes (recordTapes base c suffix) chunk =
      recordTapes emitted c suffix := by
    funext tape
    cases tape <;> simp [outputTapes, recordTapes, emitted, base, loopTapes]
  change (MachineComposition.advance (TM2.step program))^[6 * n + 18 * i +
      2 * nameSum c + 48]
    (some ⟨some (.scan (.tailVariables 0)), (RawInitialRows.clauseSigns c, none),
      recordTapes base c suffix⟩) =
    some ⟨some (.cleanupField 0), (RawInitialRows.clauseSigns c, none),
    outputTapes (recordTapes base c suffix) chunk⟩ at rows
  rw [frame] at rows
  have cleanup := RawInitialMachineCleanup.cleanupTrace emitted c suffix i
    (fun _ => rfl) rfl (RawInitialRows.clauseSigns c, none)
  have finalFrame : Function.update (Function.update emitted .input suffix)
      .index (encodeWord (i + 1)) =
      loopTapes n (i + 1) remaining suffix (chunk ++ reversed) := by
    funext tape
    cases tape <;> simp [emitted, loopTapes]
  rw [finalFrame] at cleanup
  have total := trace_trans _ (trace_trans _ (trace_trans _ first read) rows) cleanup
  have time : 1 + ((encodeWords (Complexity.clauseWords c)).length + 7) +
      (6 * n + 18 * i + 2 * nameSum c + 48) +
      ((encodeWords (Complexity.clauseWords c)).length + 7) = bodyTime i c := by
    simp only [bodyTime, nameSum]
    omega
  simpa only [time] using total

end BinPackingGames.Foundations.PCP.RawInitialMachineBody

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RawInitialMachineFinish
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.RawInitialMachineFinish

open Turing Complexity RawInitialMachineModel RawInitialMachinePhases

theorem cleanupTrace (n m : Nat) (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[n + m + 6]
      (some ⟨some (.cleanupFinal 0), state, finishTapes n m rev⟩) =
      some ⟨some .reset, (state.1, none), tapes [] [] [] rev []⟩ := by
  have h0 := (cleanupFinalInTime 0 (finishTapes n m rev) state).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[(encodeWord n).length + 1]
    (some ⟨some (.cleanupFinal 0), state, finishTapes n m rev⟩) = _ at h0
  rw [encodeWord_length] at h0
  have f0 : Function.update (finishTapes n m rev) .variables [] =
      tapes [] [false] (encodeWord m) rev [] := by
    funext k
    cases k <;> simp [finishTapes, tapes]
  change (MachineComposition.advance (TM2.step program))^[n + 2]
    (some ⟨some (.cleanupFinal 0), state, finishTapes n m rev⟩) =
    some ⟨some (.cleanupFinal 1), (state.1, none),
      Function.update (finishTapes n m rev) .variables []⟩ at h0
  rw [f0] at h0
  have h1 := (cleanupFinalInTime 1 (tapes [] [false] (encodeWord m) rev [])
    (state.1, none)).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[2]
    (some ⟨some (.cleanupFinal 1), (state.1, none),
      tapes [] [false] (encodeWord m) rev []⟩) = _ at h1
  have f1 : Function.update (tapes [] [false] (encodeWord m) rev []) .counter [] =
      tapes [] [] (encodeWord m) rev [] := by
    funext k
    cases k <;> simp [tapes]
  change (MachineComposition.advance (TM2.step program))^[2]
    (some ⟨some (.cleanupFinal 1), (state.1, none), tapes [] [false] (encodeWord m) rev []⟩) =
    some ⟨some (.cleanupFinal 2), (state.1, none),
      Function.update (tapes [] [false] (encodeWord m) rev []) .counter []⟩ at h1
  rw [f1] at h1
  have h2 := (cleanupFinalInTime 2 (tapes [] [] (encodeWord m) rev [])
    (state.1, none)).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[(encodeWord m).length + 1]
    (some ⟨some (.cleanupFinal 2), (state.1, none),
      tapes [] [] (encodeWord m) rev []⟩) = _ at h2
  rw [encodeWord_length] at h2
  have f2 : Function.update (tapes [] [] (encodeWord m) rev []) .index [] =
      tapes [] [] [] rev [] := by
    funext k
    cases k <;> simp [tapes]
  change (MachineComposition.advance (TM2.step program))^[m + 2]
    (some ⟨some (.cleanupFinal 2), (state.1, none), tapes [] [] (encodeWord m) rev []⟩) =
    some ⟨some .reset, (state.1, none),
      Function.update (tapes [] [] (encodeWord m) rev []) .index []⟩ at h2
  rw [f2] at h2
  have total := trace_trans _ (trace_trans _ h0 h1) h2
  simpa only [show (n + 2) + 2 + (m + 2) = n + m + 6 by omega] using total

theorem finishTrace (n m : Nat) (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[
        3 * n + 5 * m + 17 + (encodeWords (RawInitialRows.dummyWords n m)).length + rev.length]
      (some ⟨some (.scan .dummyVariables), state, finishTapes n m rev⟩) =
      some (haltList machine (rev.reverse ++ encodeWords (RawInitialRows.dummyWords n m))) := by
  let emitted := (encodeWords (RawInitialRows.dummyWords n m)).reverse ++ rev
  have total := trace_trans _ (trace_trans _ (dummyTrace n m rev state)
    (cleanupTrace n m emitted (state.1, none)))
    (resetReverseTrace emitted (state.1, none))
  have hout : emitted.reverse = rev.reverse ++ encodeWords (RawInitialRows.dummyWords n m) := by
    simp only [emitted, List.reverse_append, List.reverse_reverse]
  rw [hout] at total
  have htime : (2 * n + 4 * m + 9) + (n + m + 6) + (emitted.length + 2) =
      3 * n + 5 * m + 17 + (encodeWords (RawInitialRows.dummyWords n m)).length + rev.length := by
    simp only [emitted, List.length_append, List.length_reverse]
    omega
  rwa [htime] at total

end BinPackingGames.Foundations.PCP.RawInitialMachineFinish

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_TableIterationFiniteAlphabet
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program

section

open Turing PCP PCP.AlphabetTable FinalCNFTableAdapter

theorem prepared_input (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) :
    preparedTapes base table e rest .input = rowRest table e rest := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes, endpointTapes,
    Hastad.SourceMachine.fieldTapes]

theorem prepared_head (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) :
    preparedTapes base table e rest .head =
      encodeWord table.rows[table.rows[e].reverseIndex].tail.val := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes,
    genericTable_headValue, GraphTables.semantics, ConstraintGraph.head,
    GraphTables.reverseAt]

theorem prepared_tail (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) :
    preparedTapes base table e rest .tail = encodeWord table.rows[e].tail.val ++ base .tail := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes, endpointTapes,
    Hastad.SourceMachine.fieldTapes]

theorem prepared_reverse (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) :
    preparedTapes base table e rest .reverseIndex =
      encodeWord table.rows[e].reverseIndex.val ++ base .reverseIndex := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes, endpointTapes,
    Hastad.SourceMachine.fieldTapes]

theorem prepared_frame (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) (tape : Tape)
    (hi : tape ≠ .input) (ht : tape ≠ .tail) (hr : tape ≠ .reverseIndex)
    (hh : tape ≠ .head) (hs : tape ≠ .scanWork) (hx : tape ≠ .indexWork) :
    preparedTapes base table e rest tape = base tape := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes, endpointTapes,
    Hastad.SourceMachine.fieldTapes, hi, ht, hr, hh, hs, hx]

theorem rowResult_frame (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) (tape : Tape)
    (hi : tape ≠ .input) (ht : tape ≠ .tail) (hr : tape ≠ .reverseIndex)
    (hh : tape ≠ .head) (hs : tape ≠ .scanWork) (hx : tape ≠ .indexWork)
    (ha : tape ≠ .accumulator) (hc : tape ≠ .rowIndex) :
    rowResultTapes plan base table e rest tape = base tape := by
  simp only [rowResultTapes, finishTapes, emittedTapes, Function.update_of_ne hi,
    Function.update_of_ne ht, Function.update_of_ne hr, Function.update_of_ne hh,
    Function.update_of_ne ha, Function.update_of_ne hc]
  exact prepared_frame base table e rest tape hi ht hr hh hs hx

def guardRowInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (ambient : Ambient) (hinput : base .input ≠ []) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .guard, ((ambient, ()), none), base⟩
      (some ⟨some .startTail, ((ambient, ()), none), base⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program headerPlan plan .guard) _ _) = _
    cases hb : base .input with
    | nil => exact False.elim (hinput hb)
    | cons b bs => simp [program, guard, TM2.stepAux, hb]
  steps_le_m := Nat.le_refl _

def guardEndInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (ambient : Ambient) (hinput : base .input = []) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .guard, ((ambient, ()), none), base⟩
      (some ⟨some .reverseOutput, ((ambient, ()), none), base⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program headerPlan plan .guard) _ _) = _
    simp [program, guard, TM2.stepAux, hinput]
  steps_le_m := Nat.le_refl _

theorem prepared_operands (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool)
    (hn : base .vertices = encodeWord table.vertices)
    (hm : base .darts = encodeWord table.darts)
    (hr : base .rowIndex = encodeWord e.val)
    (ht : base .tail = []) :
    ∀ i, (Function.update (preparedTapes base table e rest) Tape.input rest) (source i) =
      encodeWord (rowOperands table e i) := by
  intro i
  fin_cases i
  · simpa [source, rowOperands, values] using
      prepared_frame base table e rest .vertices (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) |>.trans hn
  · change (Function.update (preparedTapes base table e rest) Tape.input rest) Tape.darts = _
    simp only [Function.update_of_ne (show Tape.darts ≠ Tape.input by decide)]
    exact (prepared_frame base table e rest .darts (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hm
  · change (Function.update (preparedTapes base table e rest) Tape.input rest) Tape.tail = _
    simp only [Function.update_of_ne (show Tape.tail ≠ Tape.input by decide), prepared_tail,
      ht, List.append_nil]
    rfl
  · change (Function.update (preparedTapes base table e rest) Tape.input rest) Tape.head = _
    simp only [Function.update_of_ne (show Tape.head ≠ Tape.input by decide), prepared_head]
    rfl
  · change (Function.update (preparedTapes base table e rest) Tape.input rest) Tape.rowIndex = _
    simp only [Function.update_of_ne (show Tape.rowIndex ≠ Tape.input by decide)]
    exact (prepared_frame base table e rest .rowIndex (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hr

theorem rowOperands_bounded (table : GraphTables.Table) (e : Fin table.darts) :
    ∀ i, rowOperands table e i ≤ (GraphTables.tableBits table).length := by
  intro i
  fin_cases i
  · exact GraphTables.vertices_le_tableBits_length table
  · exact GraphTables.darts_le_tableBits_length table
  · exact table.rows[e].tail.isLt.le.trans (GraphTables.vertices_le_tableBits_length table)
  · exact table.rows[table.rows[e].reverseIndex].tail.isLt.le.trans
      (GraphTables.vertices_le_tableBits_length table)
  · exact e.isLt.le.trans (GraphTables.darts_le_tableBits_length table)

def rowTime (plan : Plan) (N : Nat) : Nat :=
  plan.length * (3 * (N + 1) + 3) + 12 * N + 15

noncomputable def rowInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool)
    (hinput : base .input = encodeWords (GraphTables.rowWords table.rows[e]) ++ rest)
    (harchive : base .archive = GraphTables.tableBits table)
    (hn : base .vertices = encodeWord table.vertices)
    (hm : base .darts = encodeWord table.darts)
    (hrow : base .rowIndex = encodeWord e.val)
    (ht : base .tail = []) (hh : base .head = []) (hr : base .reverseIndex = [])
    (hscratch : base .scratch = []) (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .startTail, ((ambient, ()), none), base⟩
      (some ⟨some .guard, ((rowRelation table e, ()), none),
        rowResultTapes plan base table e rest⟩)
      (rowTime plan (GraphTables.tableBits table).length) := by
  let parsed := endpointTapes base table.rows[e].tail.val table.rows[e].reverseIndex.val
    (rowRest table e rest)
  let ready := preparedTapes base table e rest
  let read := Function.update ready Tape.input rest
  let output := emittedTapes plan base table e rest
  let run₁ := endpointsInTime headerPlan plan base table.rows[e].tail.val
    table.rows[e].reverseIndex.val (rowRest table e rest)
    (by simpa [GraphTables.rowWords, encodeWords, List.append_assoc, rowRest] using hinput) ambient
  have parsed_archive : parsed .archive = GenericGraphTables.tableBits (genericTable table) := by
    simpa [parsed, endpointTapes, Hastad.SourceMachine.fieldTapes] using harchive
  have parsed_reverse : parsed .reverseIndex =
      encodeWord (Lookup.headIndex (genericTable table) e).val := by
    simp [parsed, endpointTapes, Hastad.SourceMachine.fieldTapes, hr]
  have parsed_head : parsed .head = [] := by
    simp [parsed, endpointTapes, Hastad.SourceMachine.fieldTapes, hh]
  have parsed_scratch : parsed .scratch = [] := by
    simp [parsed, endpointTapes, Hastad.SourceMachine.fieldTapes, hscratch]
  let run₂ := headPhaseInTime headerPlan plan parsed (genericTable table) e
    parsed_archive parsed_reverse parsed_head parsed_scratch ambient
  let run₃ := relationInTime headerPlan plan ready table.rows[e].relation rest
    (prepared_input base table e rest) ambient
  have read_operands : ∀ i, read (source i) = encodeWord (rowOperands table e i) :=
    prepared_operands base table e rest hn hm hrow ht
  have read_scratch : read .scratch = [] := by
    simp only [read, Function.update_of_ne (show Tape.scratch ≠ Tape.input by decide)]
    exact (prepared_frame base table e rest .scratch (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hscratch
  have read_acc : read .accumulator = base .accumulator := by
    simp only [read, Function.update_of_ne (show Tape.accumulator ≠ Tape.input by decide)]
    exact prepared_frame base table e rest .accumulator (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have run₄ : StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some (.row (Emitter.labelAt plan.length 36864 0 .entry)),
        ((rowRelation table e, ()), none), read⟩
      (some ⟨some .clearTail, ((rowRelation table e, ()), none), output⟩)
      (plan.length * (3 * ((GraphTables.tableBits table).length + 1) + 3) + 1) := by
    simpa only [read_acc, output, emittedTapes, read, ready] using
      emitInTime headerPlan plan read (rowOperands table e) read_operands read_scratch
        (rowRelation table e) (GraphTables.tableBits table).length (rowOperands_bounded table e)
  have output_tail : output .tail = encodeWord table.rows[e].tail.val := by
    simp [output, emittedTapes, prepared_tail, ht]
  have output_head : output .head = encodeWord table.rows[table.rows[e].reverseIndex].tail.val := by
    simp [output, emittedTapes, prepared_head]
  have output_reverse : output .reverseIndex = encodeWord table.rows[e].reverseIndex.val := by
    simp [output, emittedTapes, prepared_reverse, hr]
  have output_row : output .rowIndex = encodeWord e.val := by
    simp only [output, emittedTapes,
      Function.update_of_ne (show Tape.rowIndex ≠ Tape.accumulator by decide),
      Function.update_of_ne (show Tape.rowIndex ≠ Tape.input by decide)]
    exact (prepared_frame base table e rest .rowIndex (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hrow
  let run₅ := finishInTime headerPlan plan output table.rows[e].tail.val
    table.rows[table.rows[e].reverseIndex].tail.val table.rows[e].reverseIndex.val e.val
    output_tail output_head output_reverse output_row (rowRelation table e)
  let r₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ run₂
  let r₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂ run₃
  let r₁₂₃₄ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂₃ run₄
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂₃₄ run₅
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have hb := run.steps_le_m
  have htbound := rowOperands_bounded table e 2
  have hhbound := rowOperands_bounded table e 3
  have hrbound := table.rows[e].reverseIndex.isLt.le.trans (GraphTables.darts_le_tableBits_length table)
  change table.rows[e].tail.val ≤ _ at htbound
  change table.rows[table.rows[e].reverseIndex].tail.val ≤ _ at hhbound
  simp only [Lookup.headTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, genericTable_tableBits] at hb
  unfold rowTime
  omega

end

section

open PCP PCP.AlphabetTable FinalCNFTableAdapter

theorem remainingEvents_cons (table : GraphTables.Table) (r : Nat) (h : r < table.darts) :
    remainingEvents table r = ⟨r, h⟩ :: remainingEvents table (r + 1) := by
  unfold remainingEvents
  rw [List.drop_eq_getElem_cons (l := List.finRange table.darts) (i := r)
    (by simpa using h)]
  simp

theorem inputStream_remaining_cons (table : GraphTables.Table) (r : Nat)
    (h : r < table.darts) :
    inputStream table (remainingEvents table r) =
      encodeWords (GraphTables.rowWords table.rows[(⟨r, h⟩ : Fin table.darts)]) ++
        inputStream table (remainingEvents table (r + 1)) := by
  rw [remainingEvents_cons table r h, inputStream_cons]

theorem outputStream_remaining_cons (plan : Plan) (table : GraphTables.Table) (r : Nat)
    (h : r < table.darts) :
    outputStream plan table (remainingEvents table r) =
      plan.flatMap (Emitter.commandBits (rowOperands table ⟨r, h⟩)
        (rowRelation table ⟨r, h⟩)) ++
          outputStream plan table (remainingEvents table (r + 1)) := by
  rw [remainingEvents_cons table r h, outputStream_cons]

theorem encodeWords_flatMap_rows {α : Type} (rows : List α) (words : α → List Nat) :
    encodeWords (rows.flatMap words) = rows.flatMap (fun row => encodeWords (words row)) := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem rowList_eq_finRange_map (table : GraphTables.Table) :
    GraphTables.rowList table = (List.finRange table.darts).map (fun e => table.rows[e]) := by
  rw [← List.ofFn_eq_map, ← Vector.toList_ofFn]
  change table.rows.toList = (Vector.ofFn (fun i => table.rows[i.val])).toList
  rw [Vector.ofFn_getElem]

theorem inputStream_all (table : GraphTables.Table) :
    inputStream table (List.finRange table.darts) = tableRowsBits (genericTable table) := by
  rw [tableRowsBits, genericTable_rowList]
  erw [List.flatMap_map]
  change inputStream table (List.finRange table.darts) =
    encodeWords ((GraphTables.rowList table).flatMap GraphTables.rowWords)
  rw [rowList_eq_finRange_map, List.flatMap_map, encodeWords_flatMap_rows]
  rfl

theorem inputStream_remaining_zero (table : GraphTables.Table) :
    inputStream table (remainingEvents table 0) = tableRowsBits (genericTable table) := by
  rw [remainingEvents_zero, inputStream_all]

end

section

open Turing PCP PCP.AlphabetTable

structure LoopInvariant (table : GraphTables.Table) (r : Nat) (base : Tape → List Bool) : Prop where
  input : base .input = inputStream table (remainingEvents table r)
  archive : base .archive = GraphTables.tableBits table
  vertices : base .vertices = encodeWord table.vertices
  darts : base .darts = encodeWord table.darts
  index : base .rowIndex = encodeWord r
  tail : base .tail = []
  head : base .head = []
  reverse : base .reverseIndex = []
  scratch : base .scratch = []

structure LoopRun (headerPlan plan : Plan) (table : GraphTables.Table) (r remaining : Nat)
    (base : Tape → List Bool) (ambient : Ambient) where
  finalAmbient : Ambient
  finalTapes : Tape → List Bool
  execution : StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
    ⟨some .guard, ((ambient, ()), none), base⟩
    (some ⟨some .reverseOutput, ((finalAmbient, ()), none), finalTapes⟩)
    (remaining * (rowTime plan (GraphTables.tableBits table).length + 1) + 1)
  accumulator : finalTapes .accumulator =
    (outputStream plan table (remainingEvents table r)).reverse ++ base .accumulator
  output : finalTapes .output = base .output

theorem rowInvariant_succ (plan : Plan) (table : GraphTables.Table) (r : Nat)
    (hr : r < table.darts) (base : Tape → List Bool) (invariant : LoopInvariant table r base) :
    LoopInvariant table (r + 1)
      (rowResultTapes plan base table ⟨r, hr⟩
        (inputStream table (remainingEvents table (r + 1)))) := by
  constructor
  · exact rowResult_input _ _ _ _ _
  · exact (rowResult_frame _ _ _ _ _ .archive (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans invariant.archive
  · exact (rowResult_frame _ _ _ _ _ .vertices (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans invariant.vertices
  · exact (rowResult_frame _ _ _ _ _ .darts (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans invariant.darts
  · exact rowResult_index _ _ _ _ _
  · exact rowResult_tail _ _ _ _ _
  · exact rowResult_head _ _ _ _ _
  · exact rowResult_reverse _ _ _ _ _
  · exact (rowResult_frame _ _ _ _ _ .scratch (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans invariant.scratch

theorem rowWords_nonempty (table : GraphTables.Table) (e : Fin table.darts) :
    encodeWords (GraphTables.rowWords table.rows[e]) ≠ [] := by
  simp [GraphTables.rowWords, encodeWords, encodeWord]

noncomputable def loopInTime (headerPlan plan : Plan) (table : GraphTables.Table)
    (remaining : Nat) :
    ∀ (r : Nat) (_hcount : r + remaining = table.darts) (base : Tape → List Bool)
      (ambient : Ambient), LoopInvariant table r base →
        LoopRun headerPlan plan table r remaining base ambient := by
  induction remaining with
  | zero =>
      intro r hcount base ambient invariant
      have hr : r = table.darts := by omega
      have hinput : base .input = [] := by
        simpa only [hr, remainingEvents_done, inputStream_nil] using invariant.input
      refine {
        finalAmbient := ambient
        finalTapes := base
        execution := ?_
        accumulator := ?_
        output := rfl }
      · simpa only [Nat.zero_mul, Nat.zero_add] using
          guardEndInTime headerPlan plan base ambient hinput
      · simp only [hr, remainingEvents_done, outputStream_nil, List.reverse_nil, List.nil_append]
  | succ remaining ih =>
      intro r hcount base ambient invariant
      have hr : r < table.darts := by omega
      let e : Fin table.darts := ⟨r, hr⟩
      let rest := inputStream table (remainingEvents table (r + 1))
      let next := rowResultTapes plan base table e rest
      have hinput : base .input = encodeWords (GraphTables.rowWords table.rows[e]) ++ rest := by
        rw [invariant.input, inputStream_remaining_cons table r hr]
      have hnonempty : base .input ≠ [] := by
        rw [hinput]
        exact List.append_ne_nil_of_left_ne_nil (rowWords_nonempty table e) rest
      let guardRun := guardRowInTime headerPlan plan base ambient hnonempty
      let rowRun := rowInTime headerPlan plan base table e rest hinput invariant.archive
        invariant.vertices invariant.darts invariant.index invariant.tail invariant.head
        invariant.reverse invariant.scratch ambient
      let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ guardRun rowRun
      let later := ih (r + 1) (by omega) next (rowRelation table e)
        (rowInvariant_succ plan table r hr base invariant)
      let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first later.execution
      refine {
        finalAmbient := later.finalAmbient
        finalTapes := later.finalTapes
        execution := { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
        accumulator := ?_
        output := ?_ }
      · have hb := run.steps_le_m
        rw [Nat.succ_mul]
        omega
      · rw [later.accumulator, outputStream_remaining_cons plan table r hr]
        simp only [next, rowResult_accumulator, List.reverse_append, List.append_assoc]
        rfl
      · rw [later.output]
        exact rowResult_frame _ _ _ _ _ .output (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)

end

section

open Turing PCP PCP.AlphabetTable FinalCNFTableAdapter

def emittedBytes (plan : Plan) (table : GraphTables.Table) : List Bool :=
  encodeWords [6 * table.vertices + 36864 * table.darts, 40960 * table.darts] ++
    outputStream plan table (List.finRange table.darts)

noncomputable def rawBudget (plan : Plan) (table : GraphTables.Table) : Nat :=
  headerTimePolynomial.eval (GraphTables.tableBits table).length +
    table.darts * (rowTime plan (GraphTables.tableBits table).length + 1) + 1 +
      (emittedBytes plan table).length + 1

structure RawRun (plan : Plan) (table : GraphTables.Table) where
  finalAmbient : Ambient
  finalTapes : Tape → List Bool
  execution : StateTransition.EvalsToInTime (machine headerPlan plan).step
    (initList (machine headerPlan plan) (GraphTables.tableBits table))
    (some ⟨none, ((finalAmbient, ()), none), finalTapes⟩) (rawBudget plan table)
  output : finalTapes .output = emittedBytes plan table

theorem header_loopInvariant (_plan : Plan) (table : GraphTables.Table) :
    LoopInvariant table 0 (headerResultTapes table.vertices table.darts
      (tableRowsBits (genericTable table))) := by
  constructor
  · rw [headerResultTapes_input, inputStream_remaining_zero]
  · rw [headerResultTapes_archive]
    exact (tableBits_header_rows (genericTable table)).symm.trans (genericTable_tableBits table)
  · rfl
  · rfl
  · exact headerResultTapes_rowIndex _ _ _
  · rfl
  · rfl
  · rfl
  · rfl

noncomputable def rawRun (plan : Plan) (table : GraphTables.Table) : RawRun plan table := by
  let base := headerResultTapes table.vertices table.darts (tableRowsBits (genericTable table))
  let ambient : Ambient := ((), fun _ => false)
  have headerRun : StateTransition.EvalsToInTime (machine headerPlan plan).step
      (initList (machine headerPlan plan) (GraphTables.tableBits table))
      (some ⟨some .guard, ((ambient, ()), none), base⟩)
      (headerTimePolynomial.eval (GraphTables.tableBits table).length) := by
    simpa only [genericTable_tableBits, genericTable_vertices, genericTable_darts, base, ambient]
      using initializedTableHeaderInTime plan (genericTable table)
  let loop := loopInTime headerPlan plan table table.darts 0 (by omega)
    base ambient (header_loopInvariant plan table)
  have acc : loop.finalTapes .accumulator = (emittedBytes plan table).reverse := by
    rw [loop.accumulator]
    simp only [remainingEvents_zero, base, headerResultTapes_accumulator, emittedBytes,
      List.reverse_append]
  have out : loop.finalTapes .output = [] := by
    rw [loop.output]
    rfl
  let finalTapes := Reduction.MachineTransfer.tapesAt Tape.accumulator Tape.output
    loop.finalTapes [] (emittedBytes plan table)
  have finish : StateTransition.EvalsToInTime (machine headerPlan plan).step
      ⟨some .reverseOutput, ((loop.finalAmbient, ()), none), loop.finalTapes⟩
      (some ⟨none, ((loop.finalAmbient, ()), none), finalTapes⟩)
      ((emittedBytes plan table).length + 1) := by
    have run := Reduction.MachineTransfer.transferAtInTime Tape.accumulator Tape.output
      (by decide) id false .reverseOutput none (program headerPlan plan) rfl
      loop.finalTapes (loop.finalAmbient, ()) none
    simpa only [acc, out, List.reverse_reverse, List.length_reverse, List.map_id,
      List.append_nil, finalTapes, machine, FinTM2.step] using! run
  let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ headerRun loop.execution
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first finish
  exact {
    finalAmbient := loop.finalAmbient
    finalTapes := finalTapes
    execution := {
      toEvalsTo := run.toEvalsTo
      steps_le_m := by
        have hb := run.steps_le_m
        unfold rawBudget
        omega }
    output := by simp [finalTapes, Reduction.MachineTransfer.tapesAt] }

end

section

open PCP PCP.AlphabetTable

def formulaHeader (table : GraphTables.Table) : List Bool :=
  encodeWords [6 * table.vertices + 36864 * table.darts, 40960 * table.darts]

theorem formulaHeader_eq (table : GraphTables.Table) :
    formulaHeader table = encodeWords [(FinalTableFormula.output table).variables,
      (FinalTableFormula.output table).clauses.length] := by
  simp only [formulaHeader, FinalTableFormula.variable_count, FinalTableFormula.clause_count,
    Nat.mul_comm]

theorem outputStream_eq_clauseBits (table : GraphTables.Table) :
    outputStream rowPlan table (List.finRange table.darts) =
      encodeWords ((FinalTableFormula.output table).clauses.flatMap Complexity.clauseWords) := by
  calc
    _ = (List.finRange table.darts).flatMap (fun e =>
          encodeWords ((VerifierToCNF.eventBlock (FinalCNFPattern.tableVerifier table)
            (by decide) e).flatMap Complexity.clauseWords)) := by
      apply List.flatMap_congr
      intro e he
      exact rowPlan_bits table e
    _ = encodeWords ((List.finRange table.darts).flatMap (fun e =>
          (VerifierToCNF.eventBlock (FinalCNFPattern.tableVerifier table)
            (by decide) e).flatMap Complexity.clauseWords)) :=
      (encodeWords_flatMap _ _).symm
    _ = _ := by
      congr 1
      rw [← List.flatMap_assoc]
      rfl

theorem header_append_outputStream (table : GraphTables.Table) :
    formulaHeader table ++ outputStream rowPlan table (List.finRange table.darts) =
      formulaBits (FinalTableFormula.output table) := by
  rw [formulaHeader_eq, outputStream_eq_clauseBits]
  exact (encodeWords_append _ _).symm

end

section

open PCP

theorem rowTimePolynomial_eval (N : Nat) :
    rowTimePolynomial.eval N = rowTime rowPlan N := by
  simp only [rowTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, rowTime, rowPlan_length]

noncomputable def phaseTimePolynomial : Polynomial Nat :=
  headerTimePolynomial +
    (Polynomial.X * (rowTimePolynomial + Polynomial.C 1) + Polynomial.C 1) +
    (FinalTableFormula.sizePolynomial + Polynomial.C 1)

theorem phaseTimePolynomial_eval (N : Nat) :
    phaseTimePolynomial.eval N =
      headerTimePolynomial.eval N + (N * (rowTime rowPlan N + 1) + 1) +
        (FinalTableFormula.sizePolynomial.eval N + 1) := by
  simp only [phaseTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, rowTimePolynomial_eval]

theorem phaseTime_le {N rows outputLength : Nat} (rowBound : rows ≤ N)
    (outputBound : outputLength ≤ FinalTableFormula.sizePolynomial.eval N) :
    headerTimePolynomial.eval N + (rows * (rowTime rowPlan N + 1) + 1) +
      (outputLength + 1) ≤ phaseTimePolynomial.eval N := by
  have hrows := Nat.mul_le_mul_right (rowTime rowPlan N + 1) rowBound
  rw [phaseTimePolynomial_eval]
  omega

theorem table_phaseTime_le (table : GraphTables.Table) :
    headerTimePolynomial.eval (GraphTables.tableBits table).length +
      (table.darts * (rowTime rowPlan (GraphTables.tableBits table).length + 1) + 1) +
      ((formulaBits (FinalTableFormula.output table)).length + 1) ≤
        phaseTimePolynomial.eval (GraphTables.tableBits table).length :=
  phaseTime_le (GraphTables.darts_le_tableBits_length table)
    (FinalTableFormula.formulaBits_length_le_polynomial table)

noncomputable def finalTimePolynomial (C : Nat) : Polynomial Nat :=
  phaseTimePolynomial + Polynomial.C 12 *
    (Polynomial.X + phaseTimePolynomial * Polynomial.C C + Polynomial.C 1) + Polynomial.C 1

theorem finalTimePolynomial_eval (C N : Nat) :
    (finalTimePolynomial C).eval N = phaseTimePolynomial.eval N +
      12 * (N + phaseTimePolynomial.eval N * C + 1) + 1 := by
  simp only [finalTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]

end

open Turing PCP

theorem emittedBytes_eq_formulaBits (table : GraphTables.Table) :
    emittedBytes rowPlan table = formulaBits (FinalTableFormula.output table) :=
  header_append_outputStream table

theorem rawBudget_le_phaseTime (table : GraphTables.Table) :
    rawBudget rowPlan table ≤ phaseTimePolynomial.eval (GraphTables.tableBits table).length := by
  unfold rawBudget
  rw [emittedBytes_eq_formulaBits]
  simpa only [Nat.add_assoc] using table_phaseTime_le table

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime GraphTables.tableBits formulaBits FinalTableFormula.output where
  tm := FinalCNFCleanup.completedMachine headerPlan rowPlan
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := finalTimePolynomial (Runtime.programPushBound (machine headerPlan rowPlan))
  outputsFun table := by
    let tm := FinalCNFCleanup.completedMachine headerPlan rowPlan
    let input : List (tm.Γ tm.k₀) := GraphTables.tableBits table
    let output : List (tm.Γ tm.k₁) := formulaBits (FinalTableFormula.output table)
    change TM2OutputsInTime tm (input.map id) (some (output.map id))
      ((finalTimePolynomial (Runtime.programPushBound (machine headerPlan rowPlan))).eval
        (GraphTables.tableBits table).length)
    rw [List.map_id, List.map_id]
    rw [finalTimePolynomial_eval]
    let raw := rawRun rowPlan table
    let bounded : StateTransition.EvalsToInTime (machine headerPlan rowPlan).step
        (initList (machine headerPlan rowPlan) (GraphTables.tableBits table))
        (some ⟨none, ((raw.finalAmbient, ()), none), raw.finalTapes⟩)
        (phaseTimePolynomial.eval (GraphTables.tableBits table).length) := {
      toEvalsTo := raw.execution.toEvalsTo
      steps_le_m := raw.execution.steps_le_m.trans (rawBudget_le_phaseTime table) }
    have correct : raw.finalTapes .output = formulaBits (FinalTableFormula.output table) :=
      raw.output.trans (emittedBytes_eq_formulaBits table)
    have run := FinalCNFCleanup.outputsInTime headerPlan rowPlan
      (GraphTables.tableBits table) (formulaBits (FinalTableFormula.output table))
      ((raw.finalAmbient, ()), none) raw.finalTapes
      (phaseTimePolynomial.eval (GraphTables.tableBits table).length) bounded correct
    exact run

end BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program

namespace BinPackingGames.Foundations.Complexity.MachineTableIteration

open Turing PCP RoundTables GraphIterationBounds

def finalTable (H : BaseTable) (input : Input) : GraphTables.Table :=
  TableIteration.runTables H (count input) input.val

noncomputable def counterCertificate : TM2ComputableInPolyTime inputBits countedBits (id : Input → Input) where
  toTM2ComputableAux := GraphCounterPrefix.computableInPolyTime.toTM2ComputableAux
  time := GraphCounterPrefix.computableInPolyTime.time
  outputsFun input := GraphCounterPrefix.computableInPolyTime.outputsFun input.val

end BinPackingGames.Foundations.Complexity.MachineTableIteration

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_TermMachine
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.TermMachine

open Turing MachineComposition TransitionTemplate PostfixModel

attribute [instance] Emitter.finite

def lookupTapes : Fin 5 → Tape
  | 0 => .roots
  | 1 => .address
  | 2 => .copy
  | 3 => .value
  | 4 => .scratch

def lookupSteps (input : Input) (address : Nat) : Nat :=
  MachinePreservingLookupClean.steps input.roots address +
    (rootLookup input.roots address) + 5

attribute [instance] Selector.finite

def testPredicate (within : Bool) (p : Position) (input : Input) : Bool :=
  if within then decide (p.eval input.cursor < input.capacity)
  else decide (p.eval input.cursor = 0)

variable {K Λ σ : Type} {Γ : K → Type} [∀ k, DecidableEq (Γ k)]
variable [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, Fintype (Γ k)] [DecidableEq Λ] [Fintype Λ]

def RootsValid (indexing : ConfigIndex.Indexing Γ Λ σ) (input : Input) : Prop :=
  indexing.width input.capacity ≤ input.roots.length

end BinPackingGames.Foundations.Complexity.CookLevin.TermMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_CompareLoop
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.AlphabetTable.RuntimeModel

open Turing
open BinPackingGames.Foundations.Complexity

theorem headPorts_injective : Function.Injective headPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [headPorts]

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

end BinPackingGames.Foundations.PCP.AlphabetTable.RuntimeModel

namespace BinPackingGames.Foundations.PCP.AlphabetTable.CompareLoop

open Turing
open BinPackingGames.Foundations.Complexity
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

theorem encodeWord_eq_iff (left right : Nat) :
    encodeWord left = encodeWord right ↔ left = right := by
  constructor
  · intro h
    have hh := congrArg List.length h
    simpa only [encodeWord_length, Nat.add_right_cancel_iff] using hh
  · rintro rfl
    rfl

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

end BinPackingGames.Foundations.PCP.AlphabetTable.CompareLoop

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_Initialization
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.AlphabetTable.Setup

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Foundations.Hastad

variable {K Λ σ : Type} [DecidableEq K]

def resultTapes (ports : Ports K) (base : K → List Bool)
    (n m : Nat) (rows : List Bool) : K → List Bool :=
  Function.update
    (Function.update
      (Function.update
        (Function.update (Function.update base (ports 1) rows)
          (ports 2) (encodeWord n)) (ports 3) (encodeWord m))
      (ports 4) (encodeWord m)) (ports 6) (encodeWord 0)

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

end BinPackingGames.Foundations.PCP.AlphabetTable.Setup

namespace BinPackingGames.Foundations.PCP.AlphabetTable.EmitRows

open Turing
open BinPackingGames.Foundations.Complexity
open Emitter

theorem relationBits_values (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) (context : Context q) :
    (relationBits q event slot orientation).map (fun bit => if bit context then 1 else 0) =
      GraphTables.relationWords
        (Relations.relationFromTable context.1 context.2 event slot orientation) := by
  exact bitValues_ofFn (fun state : Context q =>
    Relations.relationFromTable state.1 state.2 event slot orientation) context

theorem encodedRow {n m : Nat} (row : GraphTables.DartRow n m) :
    encodeWords (GraphTables.rowWords row) =
      encodeWord row.tail.val ++ (encodeWord row.reverseIndex.val ++
        encodeWords (GraphTables.relationWords row.relation)) := by
  simp only [GraphTables.rowWords, List.cons_append, List.nil_append, encodeWords]

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

end BinPackingGames.Foundations.PCP.AlphabetTable.EmitRows

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_PCPSourceHardness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.PCP.AlphabetTable.Runtime

open Turing
open BinPackingGames.Foundations.Complexity
open RuntimeModel

theorem prefixPolynomial_eval (q N : Nat) :
    (prefixPolynomial q).eval N = Loop.prefixTime q N := by
  simp only [prefixPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Loop.prefixTime,
    Initialization.time, Body.bodyTime]
  ring

end BinPackingGames.Foundations.PCP.AlphabetTable.Runtime

end

end OAI
end


