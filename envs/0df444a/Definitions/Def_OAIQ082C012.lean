-- Prove2me | Definitions.Def_OAIQ082C012
-- name    : OAIQ082C012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T13:30:50.635852+00:00
-- url     : https://prove2.me/theorems/f3e565f7-df01-40d2-bbf4-b981d7811fdb
-- title:
--   Definitions bundle OAIQ082C012 of the split of OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.BinPackingGap.main_results`, carved from OpenAI's openai/math development (OpenAI, *Additive hardness and unbounded configuration gaps in bin packing (result family 118)*, OpenAI Math Release, September 24, 2026, result family 118, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 328 declarations of OpenAI's Lean: 98 definitions, 1 inductive type or structure and 229 theorems. The definitions and types are `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CellsMachine.frame`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CellsPrefixStage.Agrees`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CellsPrefixStage.capacityPorts`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CellsPrefixStage.statement`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish.program`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerModel.machine`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerModel.program`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine.literal`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ForestStage.afterRecords`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ForestStage.coreBase`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ForestStage.coreInitial`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ForestStage.framedCfg`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ForestStage.framedProgram`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ForestStage.framedStatement`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ForestStage.initialLocal`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ForestStage.program`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ForestStage.statement`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ForestStage.steps`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationControl.cells`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationControl.instDecidableEqΓTmBoolComputation`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationControl.literalStatement`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationMachine.termTokens`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationMachineAt.Agrees`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationMachineAt.closurePorts`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationMachineAt.contents`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationMachineAt.statement`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationMachineAt.tapes`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationStage.Ports`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationTemplate.initialCellTokens`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationTemplate.inputCellTokens`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationTemplate.presenceTokens`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationTemplate.selectorLoopTokens`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InputCellsCapacity.Agrees`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InputCellsCapacity.statement`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InputCellsMachine.EmitAgrees`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InputCellsMachine.alphabetDecidable`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InputCellsMachine.prefixTruth`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InputCellsMachine.statement`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InputCellsMachine.symbolTruth`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.PaddingCellsMachine.cellsInterval` and 59 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `BinPacking_Computation_FinalCNFRowPlan`, `BinPacking_Computation_GraphCounterStart`, `BinPacking_Computation_GraphIterationBounds`, `BinPacking_Computation_MachineInitialHeaders`, `BinPacking_CookLevin_BoundedExecution`, `BinPacking_CookLevin_CellsTokensAlignment`, `BinPacking_CookLevin_CircuitEncodingBridge`, `BinPacking_CookLevin_CircuitFinish`, `BinPacking_CookLevin_CircuitProducer`, `BinPacking_CookLevin_ClashMachine`, `BinPacking_CookLevin_Completeness`, `BinPacking_CookLevin_ConfigIndex`, `BinPacking_CookLevin_ForestStage`, `BinPacking_CookLevin_InitializationMachine`, `BinPacking_CookLevin_InitializationMachineAt`, `BinPacking_CookLevin_MachineCircuit`, `BinPacking_CookLevin_OutputOrder`, `BinPacking_CookLevin_PaddingCellsMachine`, `BinPacking_CookLevin_PayloadPresenceMachine`, `BinPacking_CookLevin_PostfixBounds`, `BinPacking_CookLevin_ProducerFrontStage`, `BinPacking_CookLevin_TransitionArena`, `BinPacking_CookLevin_ValidityMachine`, `BinPacking_CookLevin_VerifierCircuit`, `BinPacking_PCP_Initialization`, `BinPacking_PCP_Lookup`, `BinPacking_PCP_MachineRawInitialTable`, `BinPacking_PCP_PCPSourceHardness`, `BinPacking_PCP_RawInitialMachineBody`, `BinPacking_PCP_RawInitialMachineBudget`, `BinPacking_PCP_RawInitialMachineCleanup`, `BinPacking_PCP_RawInitialMachineFinish`, `BinPacking_PCP_RawInitialMachineLoopData`, `BinPacking_PCP_RawInitialMachineRows`, `BinPacking_PCP_RoundTableGap`.
--
--   **Imports.** It imports the published bundle `Def_BinPackingGap`; the bundles `OAIQ082C005`, `OAIQ082C006` and `OAIQ082C007` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ082C018`, `OAIQ082C019` and `OAIQ082C020`.
-- source:
--   OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 118; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_BinPackingGap
import Definitions.Def_OAIQ082C005
import Definitions.Def_OAIQ082C006
import Definitions.Def_OAIQ082C007

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RawInitialMachineBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.GraphTableComplexity

open BinPackingGames.Foundations.Complexity
open Polynomial

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

theorem bits_le_polynomial (table : GraphTables.Table) :
    (GraphTables.tableBits table).length ≤
      (encodingPolynomial 64).eval (table.vertices + table.darts) :=
  (GraphTables.tableBits_length_le table).trans
    (rowBound_le_polynomial 64 table.vertices table.darts)

theorem bits_le_of_size_le {N : Nat} (table : GraphTables.Table)
    (hsize : table.vertices + table.darts ≤ N) :
    (GraphTables.tableBits table).length ≤ (encodingPolynomial 64).eval N :=
  (bits_le_polynomial table).trans (encodingPolynomial_mono 64 hsize)

end BinPackingGames.Foundations.PCP.GraphTableComplexity

namespace BinPackingGames.Foundations.PCP.AlphabetTable.Input

open BinPackingGames.Foundations.Complexity

export GenericGraphTables (Label RelationTable DartRow Rows Valid Table
  relationIndex relationAt relationOf relationAt_relationOf
  reverseAt acceptsAt rowList rowList_length semantics semantics_reverse
  semantics_tail semantics_accepts ofGraph semantics_ofGraph ofEnumeratedGraph
  bitWord relationWords relationWords_length rowWords rowWords_length
  )

variable {q n m : Nat}

theorem rowsWords_split (rows : List (DartRow q n m)) (e : Nat)
    (he : e < rows.length) :
    rows.flatMap rowWords = (rows.take e).flatMap rowWords ++
      (rowWords rows[e] ++ (rows.drop (e + 1)).flatMap rowWords) := by
  have hs : rows.take e ++ rows[e] :: rows.drop (e + 1) = rows := by
    rw [List.getElem_cons_drop he, List.take_append_drop]
  have hw := congrArg (fun rs : List (DartRow q n m) => rs.flatMap rowWords) hs
  simpa only [List.flatMap_append, List.flatMap_cons, List.append_assoc] using hw.symm

theorem rowsBits_split (rows : List (DartRow q n m)) (e : Nat)
    (he : e < rows.length) :
    encodeWords (rows.flatMap rowWords) =
      encodeWords ((rows.take e).flatMap rowWords) ++
        (encodeWords (rowWords rows[e]) ++
          encodeWords ((rows.drop (e + 1)).flatMap rowWords)) := by
  rw [rowsWords_split rows e he]
  simp only [encodeWords_append]

theorem rowsBits_append_split (rows : List (DartRow q n m)) (e : Nat)
    (he : e < rows.length) (suffix : List Bool) :
    encodeWords (rows.flatMap rowWords) ++ suffix =
      encodeWords ((rows.take e).flatMap rowWords) ++
        (encodeWords (rowWords rows[e]) ++
          (encodeWords ((rows.drop (e + 1)).flatMap rowWords) ++ suffix)) := by
  rw [rowsBits_split rows e he]
  simp only [List.append_assoc]

end BinPackingGames.Foundations.PCP.AlphabetTable.Input

namespace BinPackingGames.Foundations.PCP.RawInitialMachineBudget

open Target Complexity

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

theorem timePolynomial_eval (N : Nat) :
    timePolynomial.eval N = 100 * N ^ 2 + 60000 * N + 100 := by
  simp [timePolynomial]

theorem fullBudget_le (F : Formula) :
    fullBudget F ≤ timePolynomial.eval (formulaBits F).length := by
  have hinput := input_header_bound F
  have hloop := loopTime_le 0 F.clauses
  have hout := GraphTableComplexity.bits_le_of_size_le (RawInitialTables.table F)
    (graph_size_bound F)
  rw [GraphTableComplexity.encodingPolynomial_eval] at hout
  simp only [Nat.zero_add] at hloop
  have hm : F.clauses.length ≤ (formulaBits F).length := by omega
  have hcoefficient : 18 * F.variables + 18 * F.clauses.length + 81 ≤
      18 * (formulaBits F).length + 81 := by omega
  have hproduct := Nat.mul_le_mul hm hcoefficient
  rw [timePolynomial_eval]
  unfold fullBudget
  nlinarith

end BinPackingGames.Foundations.PCP.RawInitialMachineBudget

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_Lookup
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

end BinPackingGames.Foundations.PCP.AlphabetTable.ReadRelation

namespace BinPackingGames.Foundations.PCP.AlphabetTable.Lookup

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K]

theorem stepAux_skipBits (source : K) (bits : List Bool)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (base : K → List Bool) (suffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (skipBits source bits.length next) (ambient, register)
        (Function.update base source (encodeWords (bits.map bitWord) ++ suffix)) =
      TM2.stepAux next (ambient, none) (Function.update base source suffix) := by
  induction bits generalizing register with
  | nil => simp [skipBits, encodeWords, TM2.stepAux]
  | cons bit bits ih =>
    cases bit <;>
      simpa only [List.length_cons, skipBits, List.map_cons, bitWord, Bool.false_eq_true,
        ite_false, ite_true, if_true, encodeWords, encodeWord, List.replicate_zero,
        List.replicate_succ, List.nil_append, List.cons_append, List.singleton_append,
        TM2.stepAux, Function.update_self, List.head?_cons, List.tail_cons,
        Option.getD_some, Bool.cond_false, Bool.cond_true, Function.update_idem] using
          ih none

theorem rowBits_eq {q n m : Nat} (row : DartRow q n m) :
    rowBits row = encodeWord row.tail.val ++
      (encodeWord row.reverseIndex.val ++ encodeWords (relationWords row.relation)) := by
  simp [rowBits, rowWords, encodeWords]

def skipCost {q n m : Nat} (row : DartRow q n m) : Nat :=
  row.tail.val + row.reverseIndex.val + 4

def prefixCost {q n m : Nat} (rows : List (DartRow q n m)) : Nat :=
  (rows.map skipCost).sum

def lookupCost {q n m : Nat} (prior : List (DartRow q n m)) (row : DartRow q n m) : Nat :=
  prefixCost prior + row.tail.val + 3

theorem lookupCost_le {q n m : Nat} (prior : List (DartRow q n m)) (row : DartRow q n m) :
    lookupCost prior row ≤ (rowsBits prior ++ rowBits row).length +
      2 * (encodeWord prior.length).length + 1 := by
  have hp : prefixCost prior ≤ (rowsBits prior).length + 2 * prior.length := by
    induction prior with
    | nil => simp [prefixCost]
    | cons first prior ih =>
      have hb : skipCost first ≤ (rowBits first).length + 2 := by
        simp only [skipCost, rowBits_eq, List.length_append, encodeWord_length]
        omega
      simp only [prefixCost, List.map_cons, List.sum_cons, rowsBits_cons,
        List.length_append, List.length_cons] at *
      omega
  have hr : row.tail.val + 1 ≤ (rowBits row).length := by
    simp only [rowBits_eq, List.length_append, encodeWord_length]
    omega
  simp only [lookupCost, List.length_append, encodeWord_length]
  omega

def tableTailCost {q : Nat} (table : Table q) (e : Fin table.darts) : Nat :=
  lookupCost ((rowList table).take e.val) table.rows[e] +
    (table.darts + 1) + (table.vertices + 1)

def readRowTapes {q n m : Nat} (source tail reverse : K) (base : K → List Bool)
    (row : DartRow q n m) (suffix : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base source suffix)
    tail (encodeWord row.tail.val)) reverse (encodeWord row.reverseIndex.val)

def readRowCost {q n m : Nat} (row : DartRow q n m) : Nat :=
  row.tail.val + row.reverseIndex.val + 5

end BinPackingGames.Foundations.PCP.AlphabetTable.Lookup

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RoundTableGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.AlphabetTable.Enumeration

open BinPackingGames.Foundations.Hastad
open scoped BigOperators

theorem ordered_trans_finCongr {A : Type*} {a b : Nat}
    (order : A ≃ Fin a) (sameCount : a = b) :
    ordered (order.trans (finCongr sameCount)) = ordered order := by
  cases sameCount
  rfl

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

theorem ordered_dart (m q : Nat) :
    ordered (dartEquiv m q) =
      (List.finRange m).flatMap (fun edge =>
        (localEvents q).flatMap (fun event =>
          (List.finRange 6).flatMap (fun slot =>
            [(((edge, event), slot), false), (((edge, event), slot), true)]))) := by
  erw [dartEquiv, ordered_trans_finCongr, ordered_product, ordered_product, ordered_event]
  simp only [ordered_refl, ordered_bool, List.flatMap_assoc, List.flatMap_map,
    List.map_cons, List.map_nil]

end BinPackingGames.Foundations.PCP.AlphabetTable.Enumeration

namespace BinPackingGames.Foundations.PCP.AlphabetTable.Table

variable {q : Nat}

theorem rowList_eq_ordered (input : GenericGraphTables.Table q) :
    GraphTables.rowList (build input) =
      (Enumeration.ordered (Enumeration.dartEquiv input.darts q)).map
        (rowFromDart input) := by
  change (Vector.ofFn (fun index => rowFromDart input
      ((Enumeration.dartEquiv input.darts q).symm index))).toList =
    (List.ofFn (Enumeration.dartEquiv input.darts q).symm).map (rowFromDart input)
  simp only [Vector.toList_ofFn, List.map_ofFn, Function.comp_def]

theorem tableWords_eq_ordered (input : GenericGraphTables.Table q) :
    GraphTables.tableWords (build input) =
      [Enumeration.vertexCount input.vertices input.darts q,
        Enumeration.dartCount input.darts q] ++
        (Enumeration.ordered (Enumeration.dartEquiv input.darts q)).flatMap
          (fun dart => GraphTables.rowWords (rowFromDart input dart)) := by
  simp only [GraphTables.tableWords, rowList_eq_ordered, build_vertices, build_darts,
    List.flatMap_map]

end BinPackingGames.Foundations.PCP.AlphabetTable.Table

namespace BinPackingGames.Foundations.PCP.AlphabetTableBounds

open AlphabetTable

variable {q : Nat}

theorem build_vertices (input : GenericGraphTables.Table q) :
    (Table.build input).vertices = input.vertices * 2 ^ q +
      input.darts * AlphabetGraphBounds.vertexFactor q := by
  rw [Table.build_vertices]
  simp only [Enumeration.vertexCount, Enumeration.eventCount, Enumeration.addressCount,
    Enumeration.localCount, Enumeration.tapeCount, Enumeration.pairTapeCount,
    Enumeration.fiveTapeCount, AlphabetGraphBounds.vertexFactor,
    AlphabetGraphBounds.localEventFactor]
  ring

end BinPackingGames.Foundations.PCP.AlphabetTableBounds

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_FinalCNFRowPlan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.FinalCNFTemplate

open Target PCP

variable (V : VerifierToCNF.FiniteVerifier 12) (e : Fin V.events)
  (p : VerifierToCNF.PatternIndex 12)

theorem splitLong_twelve {n : Nat} (ls : Fin 12 → Literal n) (ys : Fin 9 → Fin n) :
    VerifierToCNF.splitLong (List.ofFn ls) (List.ofFn ys) =
      [#v[ls 0, ls 1, ⟨ys 0, true⟩],
       #v[⟨ys 0, false⟩, ls 2, ⟨ys 1, true⟩],
       #v[⟨ys 1, false⟩, ls 3, ⟨ys 2, true⟩],
       #v[⟨ys 2, false⟩, ls 4, ⟨ys 3, true⟩],
       #v[⟨ys 3, false⟩, ls 5, ⟨ys 4, true⟩],
       #v[⟨ys 4, false⟩, ls 6, ⟨ys 5, true⟩],
       #v[⟨ys 5, false⟩, ls 7, ⟨ys 6, true⟩],
       #v[⟨ys 6, false⟩, ls 8, ⟨ys 7, true⟩],
       #v[⟨ys 7, false⟩, ls 9, ⟨ys 8, true⟩],
       #v[⟨ys 8, false⟩, ls 10, ls 11]] := by
  simp only [List.ofFn_succ, List.ofFn_zero, VerifierToCNF.splitLong]
  rfl

end BinPackingGames.Foundations.Complexity.FinalCNFTemplate

namespace BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program

open PCP PCP.AlphabetTable FinalCNFTemplate

theorem pattern_lt (p : VerifierToCNF.PatternIndex 12) : p.val < 4096 := by
  have hlen : (VerifierToCNF.patterns 12).length = 4096 := VerifierToCNF.patterns_length 12
  exact lt_of_lt_of_eq p.isLt hlen

end BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_GraphCounterStart
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.GraphCounterModel

open Turing

def program : Label → TM2.Stmt Alphabet Label State
  | .inl l => clockStatement (MachineLogCounter.program l)
  | .inr .copyFirst => Reduction.MachineTransfer.loopAt (.inr .input) (.inr .scratch)
      id false (.inr .copyFirst) (some (.inr .copySecond))
  | .inr .copySecond => MachineCopy.forkLoop (.inr .scratch) (.inr .input) (.inr .archive)
      false (.inr .copySecond) (some (.inr .seed))
  | .inr .seed => .push (.inl 0) (fun _ => false) (.goto fun _ => .inr .headerFirst)
  | .inr .headerFirst => readHeader (.inr .headerFirst) (.inr .headerSecond)
  | .inr .headerSecond => readHeader (.inr .headerSecond) (.inl 0)
  | .inr .clearInput => MachineDrain.drain (.inr .input) (.inr .clearInput)
      (some (.inr .clockCopy))
  | .inr .clockCopy => Reduction.MachineTransfer.loopAt (.inl 2) (.inr .scratch)
      id false (.inr .clockCopy) (some (.inr .archiveCopy))
  | .inr .archiveCopy => Reduction.MachineTransfer.loopAt (.inr .archive) (.inr .scratch)
      id false (.inr .archiveCopy) (some (.inr .finalReverse))
  | .inr .finalReverse => Reduction.MachineTransfer.loopAt (.inr .scratch) (.inr .output)
      id false (.inr .finalReverse) none

def machine : FinTM2 where
  K := Tape
  k₀ := .inr .input
  k₁ := .inr .output
  Γ := Alphabet
  Λ := Label
  main := .inr .copyFirst
  σ := State
  initialState := initialState
  m := program

theorem clockStep (extra : ExtraTape → List Bool) (register : Option Bool)
    (a b : MachineLogCounter.machine.Cfg)
    (h : MachineLogCounter.machine.step a = some b) :
    TM2.step program (clockConfiguration extra register a) =
      some (clockConfiguration extra register b) := by
  cases a with
  | mk label state tapes =>
      cases label with
      | none => cases h
      | some label =>
          have hb := Option.some.inj h
          subst b
          exact congrArg some (clockStatement_simulation extra register
            (MachineLogCounter.program label) state tapes)

def clockInTime (extra : ExtraTape → List Bool) (register : Option Bool) (n : Nat) :
    StateTransition.EvalsToInTime (TM2.step program)
      (clockConfiguration extra register (initList MachineLogCounter.machine (encodeWord n)))
      (some (clockConfiguration extra register
        (haltList MachineLogCounter.machine (encodeWord (n.log2 + 1))))) (8 * n + 4) :=
  MachineComposition.liftExecutionInTime _ _ (clockConfiguration extra register)
    (clockStep extra register) (MachineLogCounter.outputsInTime n)

end BinPackingGames.Foundations.Complexity.GraphCounterModel

namespace BinPackingGames.Foundations.Complexity.GraphCounterModel

open Turing

theorem headerStep_zero (again next : Label)
    (atHeader : program again = readHeader again next)
    (suffix archive : List Bool) (sum : Nat)
    (state : MachineLogCounter.State) (register : Option Bool) :
    TM2.step program
      ⟨some again, (state, register), startMemory (encodeWord 0 ++ suffix) archive (encodeWord sum)⟩ =
      some ⟨some next, (state, none), startMemory suffix archive (encodeWord sum)⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atHeader]
  simp only [readHeader, TM2.stepAux, startMemory, startExtra, encodeWord,
    List.replicate_zero, List.nil_append, List.singleton_append, List.head?_cons,
    List.tail_cons, Option.getD_some, Bool.cond_false]
  rw [startMemory_input_update]

theorem headerStep_succ (again next : Label)
    (atHeader : program again = readHeader again next)
    (n sum : Nat) (suffix archive : List Bool)
    (state : MachineLogCounter.State) (register : Option Bool) :
    TM2.step program
      ⟨some again, (state, register),
        startMemory (encodeWord (n + 1) ++ suffix) archive (encodeWord sum)⟩ =
      some ⟨some again, (state, some true),
        startMemory (encodeWord n ++ suffix) archive (encodeWord (sum + 1))⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atHeader]
  simp only [readHeader, TM2.stepAux, startMemory, startExtra, encodeWord,
    List.replicate_succ, List.cons_append, List.head?_cons, List.tail_cons,
    Option.getD_some, Bool.cond_true]
  rw [startMemory_input_update, startMemory_sum_update]
  rfl

theorem headerTrace (again next : Label)
    (atHeader : program again = readHeader again next)
    (n sum : Nat) (suffix archive : List Bool)
    (state : MachineLogCounter.State) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some again, (state, register),
        startMemory (encodeWord n ++ suffix) archive (encodeWord sum)⟩) =
      some ⟨some next, (state, none), startMemory suffix archive (encodeWord (n + sum))⟩ := by
  induction n generalizing sum register with
  | zero =>
      simpa only [Nat.zero_add, Function.iterate_one, MachineComposition.advance_some] using
        headerStep_zero again next atHeader suffix archive sum state register
  | succ n ih =>
      rw [Function.iterate_succ_apply, MachineComposition.advance_some]
      rw [headerStep_succ again next atHeader n sum suffix archive state register]
      simpa only [Nat.add_assoc, Nat.add_comm 1 sum] using ih (sum + 1) (some true)

def headerInTime (again next : Label)
    (atHeader : program again = readHeader again next)
    (n sum : Nat) (suffix archive : List Bool)
    (state : MachineLogCounter.State) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, (state, register), startMemory (encodeWord n ++ suffix) archive (encodeWord sum)⟩
      (some ⟨some next, (state, none), startMemory suffix archive (encodeWord (n + sum))⟩)
      (n + 1) where
  steps := n + 1
  evals_in_steps := headerTrace again next atHeader n sum suffix archive state register
  steps_le_m := le_rfl

theorem initialMemory (word : List Bool) :
    initList machine word =
      ⟨some (.inr .copyFirst), initialState, startMemory word [] []⟩ := by
  have ht : (initList machine word).stk = startMemory word [] [] := by
    funext tape
    cases tape with
    | inl k => simp [initList, machine, startMemory]
    | inr k => (cases k <;> simp [initList, machine, startMemory, startExtra]); rfl
  exact congrArg (TM2.Cfg.mk _ _) ht

end BinPackingGames.Foundations.Complexity.GraphCounterModel

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_GraphIterationBounds
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.GraphCounterFinish

open Turing GraphCounterModel

theorem finish_eq (word : List Bool) :
    (⟨none, initialState, frame [] [] [] [] word⟩ : TM2.Cfg Alphabet Label State) =
      haltList machine word := by
  unfold haltList
  congr 1
  funext tape
  cases tape with
  | inl i => simp [machine, frame]
  | inr k => (cases k <;> simp [machine, frame]); rfl

theorem clockCopyTrace (original counter : List Bool) :
    (MachineComposition.advance (TM2.step program))^[counter.length + 1]
      (some ⟨some (.inr .clockCopy), initialState, frame [] original counter [] []⟩) =
      some ⟨some (.inr .archiveCopy), initialState, frame [] original [] counter.reverse []⟩ := by
  have h := (Reduction.MachineTransfer.transferAtInTime (Sum.inl (2 : Fin 3))
    (Sum.inr ExtraTape.scratch) (by decide) id false (.inr .clockCopy)
    (some (.inr .archiveCopy)) program rfl (frame [] original counter [] [])
    MachineLogCounter.initialState none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[counter.length + 1]
    (some ⟨some (.inr .clockCopy), initialState, frame [] original counter [] []⟩) = _ at h
  have update : Reduction.MachineTransfer.tapesAt (Sum.inl (2 : Fin 3))
      (Sum.inr ExtraTape.scratch) (frame [] original counter [] []) []
        ((frame [] original counter [] [] (.inl 2)).reverse.map id ++
          frame [] original counter [] [] (.inr .scratch)) =
      frame [] original [] counter.reverse [] := by
    funext tape
    cases tape with
    | inl i => fin_cases i <;> simp [Reduction.MachineTransfer.tapesAt, frame]
    | inr k => cases k <;> simp [Reduction.MachineTransfer.tapesAt, frame]
  simpa only [update, initialState] using h

theorem archiveCopyTrace (original counter : List Bool) :
    (MachineComposition.advance (TM2.step program))^[original.length + 1]
      (some ⟨some (.inr .archiveCopy), initialState, frame [] original [] counter.reverse []⟩) =
      some ⟨some (.inr .finalReverse), initialState,
        frame [] [] [] (original.reverse ++ counter.reverse) []⟩ := by
  have h := (Reduction.MachineTransfer.transferAtInTime (Sum.inr ExtraTape.archive)
    (Sum.inr ExtraTape.scratch) (by decide) id false (.inr .archiveCopy)
    (some (.inr .finalReverse)) program rfl (frame [] original [] counter.reverse [])
    MachineLogCounter.initialState none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[original.length + 1]
    (some ⟨some (.inr .archiveCopy), initialState, frame [] original [] counter.reverse []⟩) = _ at h
  have update : Reduction.MachineTransfer.tapesAt (Sum.inr ExtraTape.archive)
      (Sum.inr ExtraTape.scratch) (frame [] original [] counter.reverse []) []
        ((frame [] original [] counter.reverse [] (.inr .archive)).reverse.map id ++
          frame [] original [] counter.reverse [] (.inr .scratch)) =
      frame [] [] [] (original.reverse ++ counter.reverse) [] := by
    funext tape
    cases tape with
    | inl i => simp [Reduction.MachineTransfer.tapesAt, frame]
    | inr k => cases k <;> simp [Reduction.MachineTransfer.tapesAt, frame]
  simpa only [update, initialState] using h

theorem reverseTrace (original counter : List Bool) :
    (MachineComposition.advance (TM2.step program))^[original.length + counter.length + 1]
      (some ⟨some (.inr .finalReverse), initialState,
        frame [] [] [] (original.reverse ++ counter.reverse) []⟩) =
      some (haltList machine (counter ++ original)) := by
  have h := (Reduction.MachineTransfer.transferAtInTime (Sum.inr ExtraTape.scratch)
    (Sum.inr ExtraTape.output) (by decide) id false (.inr .finalReverse) none program rfl
    (frame [] [] [] (original.reverse ++ counter.reverse) []) MachineLogCounter.initialState none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[
    (original.reverse ++ counter.reverse).length + 1]
    (some ⟨some (.inr .finalReverse), initialState,
      frame [] [] [] (original.reverse ++ counter.reverse) []⟩) = _ at h
  have update : Reduction.MachineTransfer.tapesAt (Sum.inr ExtraTape.scratch)
      (Sum.inr ExtraTape.output) (frame [] [] [] (original.reverse ++ counter.reverse) []) []
        ((frame [] [] [] (original.reverse ++ counter.reverse) [] (.inr .scratch)).reverse.map id ++
          frame [] [] [] (original.reverse ++ counter.reverse) [] (.inr .output)) =
      frame [] [] [] [] (counter ++ original) := by
    funext tape
    cases tape with
    | inl i => simp [Reduction.MachineTransfer.tapesAt, frame]
    | inr k => cases k <;> simp [Reduction.MachineTransfer.tapesAt, frame]
  rw [update] at h
  rw [← finish_eq]
  simpa only [List.length_append, List.length_reverse, initialState] using! h

end BinPackingGames.Foundations.Complexity.GraphCounterFinish

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineInitialHeaders
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineInitialHeaders

open Turing
open Reduction.MachineTransfer
open Reduction.MachineSubstitution
open MachineCopy

variable {K Λ σ : Type} [DecidableEq K]

theorem update_source (source scratch output : K)
    (hst : source ≠ scratch) (hso : source ≠ output) (hto : scratch ≠ output)
    (base : K → List Bool) (input saved emitted replacement : List Bool) :
    Function.update (forkTapes source scratch output base input saved emitted)
      source replacement = forkTapes source scratch output base replacement saved emitted := by
  funext k
  by_cases hs : k = source
  · subst k; simp [forkTapes, hst, hso]
  · by_cases ht : k = scratch
    · subst k; simp [forkTapes, Ne.symm hst, hto]
    · by_cases ho : k = output
      · subst k; simp [forkTapes, Ne.symm hso]
      · simp [forkTapes, hs, ht, ho]

theorem update_scratch (source scratch output : K) (hto : scratch ≠ output)
    (base : K → List Bool) (input saved emitted replacement : List Bool) :
    Function.update (forkTapes source scratch output base input saved emitted)
      scratch replacement = forkTapes source scratch output base input replacement emitted := by
  funext k
  by_cases ht : k = scratch
  · subst k; simp [forkTapes, hto]
  · by_cases ho : k = output
    · subst k; simp [forkTapes, Ne.symm hto]
    · simp [forkTapes, ht, ho]

theorem update_output (source scratch output : K)
    (base : K → List Bool) (input saved emitted replacement : List Bool) :
    Function.update (forkTapes source scratch output base input saved emitted)
      output replacement = forkTapes source scratch output base input saved replacement := by
  simp [forkTapes]

theorem prefixStep_true (source scratch output : K)
    (hst : source ≠ scratch) (hso : source ≠ output) (hto : scratch ≠ output)
    (scale : ℕ) (again restore : Λ) (base : K → List Bool)
    (input saved emitted : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (prefixScan source scratch output scale again restore)
      (ambient, register) (forkTapes source scratch output base (true :: input) saved emitted) =
      ⟨some again, (ambient, some true), forkTapes source scratch output base input
        (true :: saved) (List.replicate scale true ++ emitted)⟩ := by
  simp [prefixScan, TM2.stepAux, hst, hso, hto, update_source, update_scratch,
    stepAux_pushWord, update_output]

theorem prefixStep_false (source scratch output : K)
    (hst : source ≠ scratch) (hso : source ≠ output) (hto : scratch ≠ output)
    (scale : ℕ) (again restore : Λ) (base : K → List Bool)
    (suffix saved emitted : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (prefixScan source scratch output scale again restore)
      (ambient, register) (forkTapes source scratch output base (false :: suffix) saved emitted) =
      ⟨some restore, (ambient, none),
        forkTapes source scratch output base (false :: suffix) saved emitted⟩ := by
  simp [prefixScan, TM2.stepAux, hst, hso, hto, update_source]

theorem prefixScanTrace (source scratch output : K)
    (hst : source ≠ scratch) (hso : source ≠ output) (hto : scratch ≠ output)
    (scale : ℕ) (again restore : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program again = prefixScan source scratch output scale again restore)
    (base : K → List Bool) (n : ℕ) (suffix saved emitted : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some again, (ambient, register),
        forkTapes source scratch output base (encodeWord n ++ suffix) saved emitted⟩) =
      some ⟨some restore, (ambient, none),
        forkTapes source scratch output base (false :: suffix)
          (List.replicate n true ++ saved) (List.replicate (scale * n) true ++ emitted)⟩ := by
  induction n generalizing saved emitted register with
  | zero =>
    simp only [Nat.zero_add, Function.iterate_one, MachineComposition.advance_some,
      encodeWord, List.replicate_zero, List.nil_append, List.singleton_append,
      Nat.mul_zero]
    change some (TM2.stepAux (program again) _ _) = _
    rw [atScan, prefixStep_false source scratch output hst hso hto]
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[n + 1]
      (some (TM2.stepAux (program again) _ _)) = _
    rw [atScan]
    simp only [encodeWord, List.replicate_succ, List.cons_append]
    rw [prefixStep_true source scratch output hst hso hto]
    change (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some again, (ambient, some true),
        forkTapes source scratch output base (encodeWord n ++ suffix)
          (true :: saved) (List.replicate scale true ++ emitted)⟩) = _
    rw [ih]
    have hs : List.replicate n true ++ true :: saved =
        true :: (List.replicate n true ++ saved) := by
      rw [replicate_append_cons, List.replicate_succ, List.cons_append]
    simp only [hs, Nat.mul_succ, List.replicate_add, List.append_assoc]

theorem prefixTrace (source scratch output : K)
    (hst : source ≠ scratch) (hso : source ≠ output) (hto : scratch ≠ output)
    (scale : ℕ) (again restore : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program again = prefixScan source scratch output scale again restore)
    (atRestore : program restore = loopAt scratch source id false restore exit)
    (base : K → List Bool) (n : ℕ) (suffix : List Bool)
    (hsource : base source = encodeWord n ++ suffix) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * n + 2]
      (some ⟨some again, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), Function.update base output
        (List.replicate (scale * n) true ++ base output)⟩ := by
  have scan := prefixScanTrace source scratch output hst hso hto scale again restore
    program atScan base n suffix [] (base output) ambient register
  have hstart : forkTapes source scratch output base (encodeWord n ++ suffix) []
      (base output) = base := by
    rw [← hsource, ← scratchEmpty]
    exact forkTapes_self source scratch output base
  rw [hstart] at scan
  simp only [List.append_nil] at scan
  let emitted := List.replicate (scale * n) true ++ base output
  let scanned := forkTapes source scratch output base (false :: suffix)
    (List.replicate n true) emitted
  have restoreTrace := transferAt_fromTapes scratch source (Ne.symm hst) id false
    restore exit program atRestore scanned ambient none
  change (MachineComposition.advance (TM2.step program))^[(scanned scratch).length + 1]
    (some ⟨some restore, (ambient, none), scanned⟩) = _ at restoreTrace
  have hs : scanned scratch = List.replicate n true := by simp [scanned, hto]
  have hi : scanned source = false :: suffix := by simp [scanned, hst, hso]
  rw [hs, hi] at restoreTrace
  simp only [List.length_replicate, List.reverse_replicate, List.map_id] at restoreTrace
  have hrestored : tapesAt scratch source scanned []
      (List.replicate n true ++ false :: suffix) = Function.update base output emitted := by
    funext k
    by_cases hks : k = source
    · subst k
      simp [tapesAt, hso, hsource, encodeWord]
    · by_cases hkt : k = scratch
      · subst k
        simp [tapesAt, Ne.symm hst, hto, scratchEmpty]
      · by_cases hko : k = output
        · subst k
          simp [tapesAt, scanned, forkTapes, Ne.symm hso, Ne.symm hto]
        · simp [tapesAt, scanned, forkTapes, hks, hkt, hko]
  rw [hrestored] at restoreTrace
  rw [show 2 * n + 2 = (n + 1) + (n + 1) by omega,
    Function.iterate_add_apply, scan]
  exact restoreTrace

def prefixInTime (source scratch output : K)
    (hst : source ≠ scratch) (hso : source ≠ output) (hto : scratch ≠ output)
    (scale : ℕ) (again restore : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program again = prefixScan source scratch output scale again restore)
    (atRestore : program restore = loopAt scratch source id false restore exit)
    (base : K → List Bool) (n : ℕ) (suffix : List Bool)
    (hsource : base source = encodeWord n ++ suffix) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, (ambient, register), base⟩
      (some ⟨exit, (ambient, none), Function.update base output
        (List.replicate (scale * n) true ++ base output)⟩) (2 * n + 2) where
  steps := 2 * n + 2
  evals_in_steps := prefixTrace source scratch output hst hso hto scale again restore exit
    program atScan atRestore base n suffix hsource scratchEmpty ambient register
  steps_le_m := Nat.le_refl _

theorem headerTrace (nTape mTape scratch output : K)
    (_hnm : nTape ≠ mTape) (hnt : nTape ≠ scratch) (hno : nTape ≠ output)
    (hmt : mTape ≠ scratch) (hmo : mTape ≠ output) (hto : scratch ≠ output)
    (scanN restoreN scanM1 restoreM1 closeFirst scanM6 restoreM6 closeSecond : Λ)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScanN : program scanN = prefixScan nTape scratch output 1 scanN restoreN)
    (atRestoreN : program restoreN = loopAt scratch nTape id false restoreN (some scanM1))
    (atScanM1 : program scanM1 = prefixScan mTape scratch output 1 scanM1 restoreM1)
    (atRestoreM1 : program restoreM1 = loopAt scratch mTape id false restoreM1 (some closeFirst))
    (atCloseFirst : program closeFirst = pushWord output [true, false]
      (exitAt output (some scanM6)))
    (atScanM6 : program scanM6 = prefixScan mTape scratch output 6 scanM6 restoreM6)
    (atRestoreM6 : program restoreM6 = loopAt scratch mTape id false restoreM6 (some closeSecond))
    (atCloseSecond : program closeSecond = pushWord output [true, false] (exitAt output exit))
    (base : K → List Bool) (n m : ℕ) (nSuffix mSuffix : List Bool)
    (hn : base nTape = encodeWord n ++ nSuffix)
    (hm : base mTape = encodeWord m ++ mSuffix) (ht : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * n + 4 * m + 8]
      (some ⟨some scanN, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), Function.update base output
        ((encodeWords [n + m + 1, 6 * m + 1]).reverse ++ base output)⟩ := by
  let out1 := List.replicate n true ++ base output
  let out2 := List.replicate m true ++ out1
  let out3 := [false, true] ++ out2
  let out4 := List.replicate (6 * m) true ++ out3
  let out5 := [false, true] ++ out4
  let b1 := Function.update base output out1
  let b2 := Function.update base output out2
  let b3 := Function.update base output out3
  let b4 := Function.update base output out4
  let b5 := Function.update base output out5
  have first := prefixTrace nTape scratch output hnt hno hto 1 scanN restoreN
    (some scanM1) program atScanN atRestoreN base n nSuffix hn ht ambient register
  simp only [Nat.one_mul] at first
  change (MachineComposition.advance (TM2.step program))^[2 * n + 2]
    (some ⟨some scanN, (ambient, register), base⟩) =
    some ⟨some scanM1, (ambient, none), b1⟩ at first
  have second := prefixTrace mTape scratch output hmt hmo hto 1 scanM1 restoreM1
    (some closeFirst) program atScanM1 atRestoreM1 b1 m mSuffix
    (by simp [b1, hmo, hm]) (by simp [b1, hto, ht]) ambient none
  simp only [Nat.one_mul, b1, Function.update_self, Function.update_idem] at second
  change (MachineComposition.advance (TM2.step program))^[2 * m + 2]
    (some ⟨some scanM1, (ambient, none), b1⟩) =
    some ⟨some closeFirst, (ambient, none), b2⟩ at second
  have third := literalTrace output [true, false] closeFirst (some scanM6)
    program atCloseFirst b2 ambient none
  simp only [b2, Function.update_self, Function.update_idem] at third
  change (MachineComposition.advance (TM2.step program))^[1]
    (some ⟨some closeFirst, (ambient, none), b2⟩) =
    some ⟨some scanM6, (ambient, none), b3⟩ at third
  have fourth := prefixTrace mTape scratch output hmt hmo hto 6 scanM6 restoreM6
    (some closeSecond) program atScanM6 atRestoreM6 b3 m mSuffix
    (by simp [b3, hmo, hm]) (by simp [b3, hto, ht]) ambient none
  simp only [b3, Function.update_self, Function.update_idem] at fourth
  change (MachineComposition.advance (TM2.step program))^[2 * m + 2]
    (some ⟨some scanM6, (ambient, none), b3⟩) =
    some ⟨some closeSecond, (ambient, none), b4⟩ at fourth
  have fifth := literalTrace output [true, false] closeSecond exit
    program atCloseSecond b4 ambient none
  simp only [b4, Function.update_self, Function.update_idem] at fifth
  change (MachineComposition.advance (TM2.step program))^[1]
    (some ⟨some closeSecond, (ambient, none), b4⟩) =
    some ⟨exit, (ambient, none), b5⟩ at fifth
  have total := trace_trans _ (trace_trans _ (trace_trans _ (trace_trans _ first second)
    third) fourth) fifth
  have hsteps : (((2 * n + 2) + (2 * m + 2)) + 1 + (2 * m + 2)) + 1 =
      2 * n + 4 * m + 8 := by omega
  rw [hsteps] at total
  have hout : out5 = (encodeWords [n + m + 1, 6 * m + 1]).reverse ++ base output := by
    simp only [out5, out4, out3, out2, out1, encodeWords, encodeWord,
      List.reverse_append, List.reverse_replicate, List.reverse_cons, List.reverse_nil,
      List.append_nil, List.nil_append, List.append_assoc, List.singleton_append]
    rw [show n + m + 1 = 1 + m + n by omega,
      show 6 * m + 1 = 1 + 6 * m by omega]
    simp only [List.replicate_add, List.replicate_one, List.cons_append,
      List.nil_append, List.append_assoc]
  simpa only [b5, hout] using total

end BinPackingGames.Foundations.Complexity.MachineInitialHeaders

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_BoundedExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.BoundedExecution

theorem run_stack_bound (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀))
    (n : Nat) (k : tm.K) :
    ((run tm input n).stk k).length ≤ input.length + n * Runtime.programPushBound tm := by
  have h := Runtime.executionSizeBound tm.step (fun c => (c.stk k).length)
    (Runtime.programPushBound tm) (Runtime.stepStackLength tm k)
    (executionToAbsorbing tm.step (Turing.initList tm input) n)
  exact h.trans (Nat.add_le_add_right (Runtime.initialStackLength tm input k) _)

theorem run_stack_le (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀))
    (T n : Nat) (hn : n ≤ T) (k : tm.K) :
    ((run tm input n).stk k).length ≤ stackCapacity tm input T :=
  (run_stack_bound tm input n k).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_right (Runtime.programPushBound tm) hn) _)

theorem statement_budget (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀))
    (T n : Nat) (hn : n < T) (label : tm.Λ) (k : tm.K) :
    ((run tm input n).stk k).length + Runtime.statementPushBound (tm.m label) ≤
      stackCapacity tm input T := by
  have hlen := run_stack_bound tm input n k
  have hstmt := Runtime.statement_le_programPushBound tm label
  have htime := Nat.mul_le_mul_right (Runtime.programPushBound tm) (show n + 1 ≤ T by omega)
  rw [Nat.add_mul, Nat.one_mul] at htime
  unfold stackCapacity
  omega

end BinPackingGames.Foundations.Complexity.CookLevin.BoundedExecution

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ConfigIndex
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin

open Target

theorem Circuit.toFormula_satisfiable_iff_eval (C : Circuit) :
    C.toFormula.Satisfiable ↔ ∃ input : Fin C.inputs → Bool, C.eval input = true := by
  constructor
  · rintro ⟨A, hA⟩
    rcases (C.toFormula_satisfied_iff A).mp hA with ⟨hc, ho⟩
    refine ⟨C.restrictAssignment A, ?_⟩
    have hinput : ∀ j, j < C.inputs →
        inputEnv (C.restrictAssignment A) j = inputEnv A j := by
      intro j hj
      have ht : j < C.wires := by simp only [Circuit.wires]; omega
      simp [inputEnv, hj, ht, Circuit.restrictAssignment]
    have hu := run_unique C.inputs C.gates (inputEnv (C.restrictAssignment A))
      (inputEnv A) C.ordered hc hinput C.output.val C.output.isLt
    have heval : C.eval (C.restrictAssignment A) = A C.output := by
      have hout : C.output.val < C.wires := C.output.isLt
      simpa [Circuit.eval, Circuit.evalWires, inputEnv, hout] using hu
    exact heval.trans ho
  · rintro ⟨input, hinput⟩
    let A : Fin C.wires → Bool := fun j => C.evalWires input j.val
    refine ⟨A, (C.toFormula_satisfied_iff A).mpr ⟨?_, hinput⟩⟩
    apply Consistent.congr (C.evalWires_consistent input) C.ordered
    intro j hj
    have ht : j < C.wires := hj
    simp [inputEnv, ht, A]

end BinPackingGames.Foundations.Complexity.CookLevin

namespace BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit

open Turing
open StackEncoding BoundedExecution

variable {K : Type} {Γ : K → Type} {Λ σ ι : Type}
variable [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)] [DecidableEq Λ]

def DataBits.Bounded {S : Nat} (bits : DataBits ι Γ σ S) (C : Nat) : Prop :=
  (∀ v, (bits.state v).size ≤ C) ∧ ∀ k i a, (bits.cells k i a).size ≤ C

def ResultBits.Bounded {S : Nat} (bits : ResultBits ι Γ Λ σ S) (C : Nat) : Prop :=
  bits.toDataBits.Bounded C ∧ ∀ l, (bits.label l).size ≤ C

theorem size_readBits_le {A : Type} [DecidableEq A] {S : Nat}
    (bits : Fin S → Option A → Expr ι) (C : Nat) (hC : 1 ≤ C)
    (h : ∀ i a, (bits i a).size ≤ C) (n : Nat) (a : Option A) :
    (readBits bits n a).size ≤ C := by
  unfold readBits
  split
  · exact h _ _
  · exact hC

omit [DecidableEq σ] [∀ stack, Fintype (Γ stack)] in
theorem pushBits_bounded {S : Nat} (bits : DataBits ι Γ σ S) (C : Nat)
    (h : bits.Bounded C) (k : K) (f : σ → Γ k) :
    (pushBits bits k f).Bounded (max C (unaryCost σ C)) := by
  refine ⟨fun v => (h.1 v).trans (Nat.le_max_left _ _), ?_⟩
  intro j i a
  by_cases hj : j = k
  · subst j
    simp only [pushBits, Function.update_self]
    split
    · exact (size_table_le _ _ _ C h.1).trans (Nat.le_max_right _ _)
    · exact (h.2 _ _ _).trans (Nat.le_max_left _ _)
  · simpa only [pushBits, Function.update_of_ne hj] using
      (h.2 j i a).trans (Nat.le_max_left C (unaryCost σ C))

omit [DecidableEq K] in
theorem peekBits_bounded {S : Nat} (bits : DataBits ι Γ σ S) (C : Nat) (hC : 1 ≤ C)
    (h : bits.Bounded C) (k : K) (f : σ → Option (Γ k) → σ) :
    (peekBits bits k f).Bounded (max C (headCost σ (Γ k) C)) := by
  refine ⟨?_, fun j i a => (h.2 j i a).trans (Nat.le_max_left _ _)⟩
  intro v
  exact (size_table₂_le _ _ _ v C h.1
    (fun a => size_readBits_le _ C hC (h.2 k) 0 a)).trans (Nat.le_max_right _ _)

theorem popBits_bounded {S : Nat} (bits : DataBits ι Γ σ S) (C : Nat) (hC : 1 ≤ C)
    (h : bits.Bounded C) (k : K) (f : σ → Option (Γ k) → σ) :
    (popBits bits k f).Bounded (max C (headCost σ (Γ k) C)) := by
  refine ⟨(peekBits_bounded bits C hC h k f).1, ?_⟩
  intro j i a
  by_cases hj : j = k
  · subst j
    simpa only [popBits, Function.update_self] using
      (size_readBits_le _ C hC (h.2 k) (i.val + 1) a).trans
        (Nat.le_max_left C (headCost σ (Γ k) C))
  · simpa only [popBits, Function.update_of_ne hj] using
      (h.2 j i a).trans (Nat.le_max_left C (headCost σ (Γ k) C))

omit [DecidableEq K] [∀ stack, Fintype (Γ stack)] [∀ stack, DecidableEq (Γ stack)] in
theorem loadBits_bounded {S : Nat} (bits : DataBits ι Γ σ S) (C : Nat)
    (h : bits.Bounded C) (f : σ → σ) :
    (loadBits bits f).Bounded (max C (unaryCost σ C)) := by
  exact ⟨fun v => (size_table_le f bits.state v C h.1).trans (Nat.le_max_right _ _),
    fun k i a => (h.2 k i a).trans (Nat.le_max_left _ _)⟩

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [∀ stack, Fintype (Γ stack)]
  [∀ stack, DecidableEq (Γ stack)] [DecidableEq Λ] in
theorem muxResult_bounded {S : Nat} (condition : Expr ι) (yes no : ResultBits ι Γ Λ σ S)
    (G Y N : Nat) (hc : condition.size ≤ G) (hy : yes.Bounded Y) (hn : no.Bounded N) :
    (muxResult condition yes no).Bounded (2 * G + Y + N + 4) := by
  have hm (x y : Expr ι) (hx : x.size ≤ Y) (hy : y.size ≤ N) :
      (Expr.mux condition x y).size ≤ 2 * G + Y + N + 4 := by
    simp only [Expr.mux, Expr.size]
    omega
  exact ⟨⟨fun v => hm _ _ (hy.1.1 v) (hn.1.1 v),
    fun k i a => hm _ _ (hy.1.2 k i a) (hn.1.2 k i a)⟩,
    fun l => hm _ _ (hy.2 l) (hn.2 l)⟩

theorem compileAux_bounded {S : Nat} (stmt : TM2.Stmt Γ Λ σ)
    (bits : DataBits ι Γ σ S) (C : Nat) (hC : 1 ≤ C) (h : bits.Bounded C) :
    (compileAux stmt bits).Bounded (statementCost stmt C) := by
  induction stmt generalizing bits C with
  | push k f next ih =>
    exact ih _ _ (hC.trans (Nat.le_max_left _ _)) (pushBits_bounded bits C h k f)
  | peek k f next ih =>
    exact ih _ _ (hC.trans (Nat.le_max_left _ _)) (peekBits_bounded bits C hC h k f)
  | pop k f next ih =>
    exact ih _ _ (hC.trans (Nat.le_max_left _ _)) (popBits_bounded bits C hC h k f)
  | load f next ih =>
    exact ih _ _ (hC.trans (Nat.le_max_left _ _)) (loadBits_bounded bits C h f)
  | branch guard yes no ihy ihn =>
    exact muxResult_bounded _ _ _ _ _ _ (size_table_le guard bits.state true C h.1)
      (ihy bits C hC h) (ihn bits C hC h)
  | goto label =>
    exact ⟨⟨fun v => (h.1 v).trans (Nat.le_max_left _ _),
      fun k i a => (h.2 k i a).trans (Nat.le_max_left _ _)⟩,
      fun l => (size_table_le _ _ l C h.1).trans (Nat.le_max_right _ _)⟩
  | halt =>
    exact ⟨⟨fun v => (h.1 v).trans (Nat.le_max_left _ _),
      fun k i a => (h.2 k i a).trans (Nat.le_max_left _ _)⟩,
      fun _ => Nat.le_max_right _ _⟩

theorem transitionExpr_size_le (S : Nat) (stmt : TM2.Stmt Γ Λ σ)
    (bit : ConfigBit Γ Λ σ S) :
    (transitionExpr S stmt bit).size ≤ statementCost stmt 1 := by
  have h := compileAux_bounded stmt (inputBits S) 1 (by decide)
    ⟨fun _ => Nat.le_refl _, fun _ _ _ => Nat.le_refl _⟩
  rcases bit with label | (v | ⟨k, i, a⟩)
  · exact h.2 label
  · exact h.1.1 v
  · exact h.1.2 k i a

end BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_CircuitEncodingBridge
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerModel

open Turing
open BinPackingGames.Foundations.Hastad
open BinPackingGames.Reduction

def program : Label → TM2.Stmt Alphabet Label State
  | .headerStart j => SourceMachine.fieldStart (headerTape j) (.headerLoop j)
  | .headerLoop j => SourceMachine.fieldLoop .input (headerTape j) (.headerLoop j)
      (headerNext j)
  | .setup c => .load (fun _ => (((), c), none)) (.goto fun _ => .scan c)
  | .scan c => MachineTransducerCopy.scanLoop (contextSource c) .scratch
      defaultControl (fun q b => .emit c q b) (.restore c)
  | .emit c q b => MachineTransducerCopy.emitter .reversed (fun q _ => q)
      emission (.scan c) q b
  | .restore c => MachineTransfer.loopAt .scratch (contextSource c) id false
      (.restore c) (contextNext c)
  | .clearHeader => drain .header .clearHeader .guard
  | .guard => MachineUnaryCounter.guard .counter (.fieldStart 0) (.setup (.output 0))
  | .fieldStart j => SourceMachine.fieldStart (.field j) (.fieldLoop j)
  | .fieldLoop j => SourceMachine.fieldLoop .input (.field j) (.fieldLoop j)
      (SourceMachine.fieldNext Label.fieldStart (some .decodeTag) j)
  | .decodeTag => tagDecoder 4 0
  | .cleanup j => drain (.field j) (.cleanup j) (cleanupNext j)
  | .finalCounter => .pop .counter (fun state _ => (state.1, none))
      (.goto fun _ => .clearSelected)
  | .clearSelected => drain .selected .clearSelected .finalReverse
  | .finalReverse => MachineTransfer.loopAt .reversed .output id false .finalReverse none

def machine : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .headerStart 0
  σ := State
  initialState := initialState
  m := program

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerModel

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitEmission

open Turing
open BinPackingGames.Reduction
open CircuitProducerModel

theorem setupStep (context : Context) (base : Tape → List Bool) (state : State) :
    TM2.step program ⟨some (.setup context), state, base⟩ =
      some ⟨some (.scan context), (((), context), none), base⟩ := rfl

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitEmission

namespace BinPackingGames.Foundations.Complexity.CookLevin.PostfixModel

namespace Token

def bits (token : Token) : List Bool := encodeWords token.words

end Token

end BinPackingGames.Foundations.Complexity.CookLevin.PostfixModel

namespace BinPackingGames.Foundations.Complexity.CookLevin

open Target CircuitProducerModel

theorem gateClauses_words {n : Nat} (output : Fin n) (g : Gate) (h : g.Bounded n) :
    (gateClauses output g h).flatMap clauseWords = (gateRecord output.val g).outputWords := by
  cases g with
  | const b => cases b <;> rfl
  | not x => rfl
  | and x y => rfl
  | or x y => rfl

theorem Circuit.gateBlocks_words (C : Circuit) :
    ((List.finRange C.gates.length).flatMap C.gateBlock).flatMap clauseWords =
      C.records.flatMap Record.outputWords := by
  rw [List.flatMap_assoc]
  calc
    _ = (List.finRange C.gates.length).flatMap
        (fun i => (gateRecord (C.inputs + i.val) C.gates[i.val]).outputWords) := by
      apply List.flatMap_congr
      intro i _
      exact gateClauses_words (C.gateOutput i) (C.gateAt i) (C.gateBounded i)
    _ = C.records.flatMap Record.outputWords := gateRecords_outputWords C.inputs C.gates

theorem Circuit.formulaWords_eq_records (C : Circuit) :
    formulaWords C.toFormula =
      [C.wires, 3 * C.gates.length + 1] ++
        C.records.flatMap Record.outputWords ++ outputWords C.output.val := by
  unfold formulaWords
  change [C.wires, C.toFormula.clauses.length] ++ C.toFormula.clauses.flatMap clauseWords = _
  rw [C.toFormula_clause_count]
  change [C.wires, 3 * C.gates.length + 1] ++
      (((List.finRange C.gates.length).flatMap C.gateBlock ++
        [unitClause C.output true]).flatMap clauseWords) = _
  rw [List.flatMap_append, C.gateBlocks_words]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, unitClause_words,
    List.append_assoc]

end BinPackingGames.Foundations.Complexity.CookLevin

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_MachineCircuit
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.MachineCircuit

open Turing StatementCircuit BoundedExecution
open scoped BigOperators

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [DecidableEq K] [Fintype Λ] [DecidableEq Λ]
variable [Fintype σ] [DecidableEq σ]
variable [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)]

theorem stickyExpr_size_le (S : Nat) (program : Λ → TM2.Stmt Γ Λ σ)
    (bit : ConfigBit Γ Λ σ S) :
    (stickyExpr S program bit).size ≤ expressionCost program := by
  have hc : ∀ e ∈ Finset.univ.toList.map (liveCase S program bit),
      e.size ≤ programCost program + 2 := by
    intro e he
    rcases List.mem_map.mp he with ⟨label, _, rfl⟩
    have h := (transitionExpr_size_le S (program label) bit).trans
      (statementCost_le_programCost program label)
    simp only [liveCase, Expr.size, Expr.size_rename]
    omega
  have hd := Expr.size_disjoin_le
    (Finset.univ.toList.map (liveCase S program bit)) (programCost program + 2) hc
  simp only [List.length_map, Finset.length_toList, Finset.card_univ] at hd
  simp only [Nat.add_assoc] at hd
  rw [show (2 : Nat) + 1 = 3 by decide] at hd
  simp only [stickyExpr, Expr.size, expressionCost]
  omega

end BinPackingGames.Foundations.Complexity.CookLevin.MachineCircuit

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_OutputOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitBatch

open StatementCircuit

namespace Frame

variable {inputs width oldWidth newWidth : Nat}

theorem repeat_gate_count (f : Frame inputs width) (es : Fin width → Expr (Fin width))
    (T : Nat) :
    (f.repeat es T).fragment.gates.length =
      f.fragment.gates.length + T * Batch.cost (List.ofFn es) := by
  induction T with
  | zero => simp [«repeat»]
  | succ T ih =>
    rw [«repeat», step_gate_count, ih, Nat.succ_mul]
    omega

end Frame

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitBatch

namespace BinPackingGames.Foundations.Complexity.CookLevin.PostfixAlignment

open StatementCircuit CircuitBatch PostfixModel

variable {ι : Type*}

theorem tokenWords_length_le (tokens : List Token) :
    (tokenWords tokens).length ≤ 2 * tokens.length := by
  induction tokens with
  | nil => simp [tokenWords]
  | cons t ts ih =>
    have ht : t.words.length ≤ 2 := by
      cases t with
      | const b => cases b <;> decide
      | not => decide
      | and => decide
      | or => decide
      | input w => simp [Token.words]
    simp only [tokenWords, List.flatMap_cons, List.length_append] at ih ⊢
    simp only [List.length_cons]
    omega

theorem expr_tokenWords_bounded (wire : ι → Nat) (e : Expr ι) (start : Nat)
    (hw : ∀ i, wire i < start) (word : Nat) (h : word ∈ tokenWords (exprTokens wire e)) :
    word ≤ max 5 start := by
  obtain ⟨t, ht, hword⟩ := List.mem_flatMap.mp h
  rcases exprTokens_member wire e t ht with ⟨b, rfl⟩ | rfl | rfl | rfl | ⟨i, rfl⟩
  · cases b <;> simp only [Token.words, List.mem_singleton] at hword <;> omega
  · simp only [Token.words, List.mem_singleton] at hword; omega
  · simp only [Token.words, List.mem_singleton] at hword; omega
  · simp only [Token.words, List.mem_singleton] at hword; omega
  · simp only [Token.words, List.mem_cons, List.not_mem_nil, or_false] at hword
    have hi := hw i
    rcases hword with rfl | rfl <;> omega

theorem forest_tokenWords_bounded (wire : ι → Nat) (es : List (Expr ι)) (start : Nat)
    (hw : ∀ i, wire i < start) (word : Nat) (h : word ∈ tokenWords (forestTokens wire es)) :
    word ≤ max 5 start := by
  obtain ⟨t, ht, hword⟩ := List.mem_flatMap.mp h
  obtain ⟨e, he, htoken⟩ := List.mem_flatMap.mp ht
  exact expr_tokenWords_bounded wire e start hw word
    (List.mem_flatMap.mpr ⟨t, htoken, hword⟩)

theorem forest_tokenBits_length_le (wire : ι → Nat) (es : List (Expr ι)) (start : Nat)
    (hw : ∀ i, wire i < start) :
    (tokenBits (forestTokens wire es)).length ≤
      2 * Batch.cost es * (max 5 start + 1) := by
  have hb := encodeWords_length_le (tokenWords (forestTokens wire es)) (max 5 start)
    (forest_tokenWords_bounded wire es start hw)
  have hc : (tokenWords (forestTokens wire es)).length ≤ 2 * Batch.cost es := by
    simpa only [forestTokens_length] using tokenWords_length_le (forestTokens wire es)
  exact hb.trans (Nat.mul_le_mul_right _ hc)

end BinPackingGames.Foundations.Complexity.CookLevin.PostfixAlignment

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_VerifierCircuit
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.WitnessCircuit

open StatementCircuit WitnessEncoding

section Size

theorem size_nonemptyExpr_le (q : Nat) :
    (nonemptyExpr q).size ≤ 2 * (q + 1) + 1 := by
  have h := Expr.size_disjoin_le (List.ofFn (selectorExpr q)) 1 (by
    intro e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    simp)
  simpa [nonemptyExpr, Nat.mul_comm] using h

theorem size_clashPairExpr_le (q : Nat) (i j : Fin (q + 1)) :
    (clashPairExpr q i j).size ≤ 3 := by
  by_cases h : i = j <;> simp [clashPairExpr, h, Expr.size, selectorExpr]

theorem size_clashExpr_le (q : Nat) :
    (clashExpr q).size ≤ (q + 1) * (4 * (q + 1) + 2) + 1 := by
  have hi (i : Fin (q + 1)) :
      (Expr.disjoin (List.ofFn (clashPairExpr q i))).size ≤ 4 * (q + 1) + 1 := by
    have h := Expr.size_disjoin_le (List.ofFn (clashPairExpr q i)) 3 (by
      intro e he
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp he
      exact size_clashPairExpr_le q i j)
    simpa [Nat.mul_comm] using h
  have h := Expr.size_disjoin_le
    (List.ofFn fun i => Expr.disjoin (List.ofFn (clashPairExpr q i)))
    (4 * (q + 1) + 1) (by
      intro e he
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
      exact hi i)
  simpa [clashExpr, Nat.add_assoc] using h

theorem size_validityExpr_le (q : Nat) : (validityExpr q).size ≤ 12 * (q + 1) ^ 2 := by
  have hn := size_nonemptyExpr_le q
  have hc := size_clashExpr_le q
  simp only [validityExpr, Expr.size]
  nlinarith

theorem size_presenceExpr_le (q n : Nat) : (presenceExpr q n).size ≤ 4 * (q + 1) + 1 := by
  have h := Expr.size_disjoin_le
    (List.ofFn fun length : Fin (q + 1) =>
      Expr.and (selectorExpr q length) (.const (decide (n < length.val)))) 3 (by
        intro e he
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
        simp [Expr.size])
  simpa [presenceExpr, Nat.mul_comm] using h

theorem size_payloadSymbolExpr {A : Type*} [DecidableEq A]
    (q : Nat) (f : Bool → A) (i : Fin q) (a : Option A) :
    (payloadSymbolExpr q f i a).size = 8 := by
  simp [payloadSymbolExpr, size_mux, Expr.size]

theorem size_inputCellExpr_le {A : Type*} [DecidableEq A]
    (q : Nat) (input : List Bool) (f : Bool → A) (n : Nat) (a : Option A) :
    (inputCellExpr q input f n a).size ≤ 8 * (q + 1) + 15 := by
  unfold inputCellExpr
  split
  · simp [Expr.size]
  · split
    · rw [size_mux, size_payloadSymbolExpr]
      have h := size_presenceExpr_le q (n - (inputPrefix input).length)
      simp only [Expr.size]
      omega
    · simp [Expr.size]

end Size

section Initial

variable (verifier : NPVerifier)
variable [DecidableEq verifier.computation.tm.Λ]
variable [DecidableEq verifier.computation.tm.σ]
variable [∀ k, DecidableEq (verifier.computation.tm.Γ k)]

omit [DecidableEq verifier.computation.tm.Λ] [DecidableEq verifier.computation.tm.σ] in
theorem size_initialCellExpr_le (input : List Bool) (S : Nat)
    (k : verifier.computation.tm.K) (i : Fin S) (a : Option (verifier.computation.tm.Γ k)) :
    (initialCellExpr verifier input S k i a).size ≤
      8 * (verifier.witnessBound.eval input.length + 1) + 15 := by
  by_cases hk : k = verifier.computation.tm.k₀
  · subst k
    simpa [initialCellExpr] using
      size_inputCellExpr_le (verifier.witnessBound.eval input.length) input
        verifier.computation.inputAlphabet.invFun i.val a
  · simp [initialCellExpr, hk, Expr.size]

theorem size_initExpr_le (input : List Bool) (S : Nat)
    (bit : ConfigBit verifier.computation.tm.Γ verifier.computation.tm.Λ
      verifier.computation.tm.σ S) :
    (initExpr verifier input S bit).size ≤
      8 * (verifier.witnessBound.eval input.length + 1) + 15 := by
  rcases bit with label | (state | ⟨k, i, a⟩)
  · simp [initExpr, Expr.size]
  · simp [initExpr, Expr.size]
  · exact size_initialCellExpr_le verifier input S k i a

end Initial

end BinPackingGames.Foundations.Complexity.CookLevin.WitnessCircuit

namespace BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit

open Turing StatementCircuit CircuitBatch
open scoped BigOperators

attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit.alphabetFinite
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit.labelFinite
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit.stateFinite
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit.labelDecidable
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit.stateDecidable
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit.alphabetDecidable
theorem mismatchExpr_size_le (V : NPVerifier) (input : List Bool) (j : Fin (width V input)) :
    (mismatchExpr V input j).size ≤ 2 := by
  unfold mismatchExpr
  split <;> simp [Expr.size]

theorem acceptanceExpr_size_le (V : NPVerifier) (input : List Bool) :
    (acceptanceExpr V input).size ≤ 3 * width V input + 4 := by
  have h := Expr.size_disjoin_le (List.ofFn (mismatchExpr V input)) 2 (by
    intro e he
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp he
    exact mismatchExpr_size_le V input j)
  simp only [List.length_ofFn] at h
  simp only [acceptanceExpr, Expr.size]
  omega

theorem stepExpressions_size_le (V : NPVerifier) (input : List Bool)
    (j : Fin (width V input + 1)) :
    (stepExpressions V input j).size ≤ MachineCircuit.expressionCost V.computation.tm.m := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [stepExpressions, Fin.lastCases_last, Expr.size, MachineCircuit.expressionCost]
    omega
  · simpa [stepExpressions] using MachineCircuit.stickyExpr_size_le
      (capacity V input.length) V.computation.tm.m ((bitEquiv V input).symm i)

theorem initialExpressions_cost_le (V : NPVerifier) (input : List Bool) :
    Batch.cost (List.ofFn (initialExpressions V input)) ≤
      width V input * (8 * (V.witnessBound.eval input.length + 1) + 15) +
      12 * (V.witnessBound.eval input.length + 1) ^ 2 := by
  rw [Batch.cost_ofFn, Fin.sum_univ_castSucc]
  simp only [initialExpressions, Fin.lastCases_castSucc, Fin.lastCases_last]
  apply Nat.add_le_add
  · calc
      _ ≤ ∑ _ : Fin (width V input), (8 * (V.witnessBound.eval input.length + 1) + 15) := by
        apply Finset.sum_le_sum
        intro i _
        exact WitnessCircuit.size_initExpr_le V input (capacity V input.length)
          ((bitEquiv V input).symm i)
      _ = _ := by simp
  · exact WitnessCircuit.size_validityExpr_le _

theorem circuitOfVerifier_gate_count (V : NPVerifier) (input : List Bool) :
    (circuitOfVerifier V input).gates.length =
      Batch.cost (List.ofFn (initialExpressions V input)) +
      V.horizon input.length * Batch.cost (List.ofFn (stepExpressions V input)) +
      (acceptanceExpr V input).size := by
  change ((timeFrame V input (V.horizon input.length)).step
    (fun _ : Fin 1 => acceptanceExpr V input)).fragment.gates.length = _
  rw [Frame.step_gate_count]
  simp only [timeFrame, Frame.repeat_gate_count, initialFrame, Frame.step_gate_count,
    Frame.initial, Fragment.empty, List.length_nil, Nat.zero_add]
  have hsingle : Batch.cost (List.ofFn (fun _ : Fin 1 => acceptanceExpr V input)) =
      (acceptanceExpr V input).size := by simp [Batch.cost]
  rw [hsingle]

theorem circuitOfVerifier_gates_le (V : NPVerifier) (input : List Bool) :
    (circuitOfVerifier V input).gates.length ≤
      width V input * (8 * (V.witnessBound.eval input.length + 1) + 15) +
      12 * (V.witnessBound.eval input.length + 1) ^ 2 +
      V.horizon input.length * ((width V input + 1) *
        MachineCircuit.expressionCost V.computation.tm.m) + (3 * width V input + 4) := by
  rw [circuitOfVerifier_gate_count]
  exact Nat.add_le_add
    (Nat.add_le_add (initialExpressions_cost_le V input)
      (Nat.mul_le_mul_left _ (Batch.cost_ofFn_le _ _ (stepExpressions_size_le V input))))
    (acceptanceExpr_size_le V input)

theorem widthPolynomial_eval (V : NPVerifier) (input : List Bool) :
    (widthPolynomial V).eval input.length = width V input := by
  simp [widthPolynomial, width, ConfigIndex.Indexing.width, capacity,
    NPVerifier.horizon, Nat.mul_comm]

def gatePolynomial (V : NPVerifier) : Polynomial Nat :=
  VerifierBounds.machineGatesPolynomial V.computation.time V.witnessBound
    (Runtime.programPushBound V.computation.tm)
    ((indexing V).labelCount + (indexing V).stateCount) (indexing V).symbolCount
    (MachineCircuit.expressionCost V.computation.tm.m)

theorem circuitOfVerifier_gates_le_polynomial (V : NPVerifier) (input : List Bool) :
    (circuitOfVerifier V input).gates.length ≤ (gatePolynomial V).eval input.length := by
  have hw := widthPolynomial_eval V input
  unfold widthPolynomial at hw
  simpa only [gatePolynomial, VerifierBounds.machineGatesPolynomial_eval, hw,
    Bounds.horizonPolynomial_eval, NPVerifier.horizon] using
      circuitOfVerifier_gates_le V input

end BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ClashMachine
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.InitializationTemplate

section

open PostfixModel

theorem forTokens_eq_flatMap_range (count : Nat) (body : Nat → List Token) :
    forTokens count body = (List.range count).flatMap body := by
  induction count with
  | zero => rfl
  | succ count ih => simp [forTokens, List.range_succ, ih]

theorem forTokens_eq_ofFn (count : Nat) (body : Nat → List Token) :
    forTokens count body = (List.ofFn fun i : Fin count => body i.val).flatten := by
  induction count with
  | zero => simp [forTokens]
  | succ count ih =>
    rw [forTokens, ih, List.ofFn_succ']
    simp [List.concat_eq_append]

theorem forTokens_succ_first (count : Nat) (body : Nat → List Token) :
    forTokens (count + 1) body = body 0 ++ forTokens count (fun j => body (j + 1)) := by
  simp [forTokens_eq_flatMap_range, List.range_succ_eq_map, List.flatMap_map]

theorem forTokens_congr (count : Nat) (first second : Nat → List Token)
    (h : ∀ i, i < count → first i = second i) :
    forTokens count first = forTokens count second := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [forTokens, forTokens, ih (fun i hi => h i (by omega)), h count (by omega)]

def presenceTokens (q n : Nat) : List Token :=
  forTokens (q + 1) (fun length => [.input length, .const (decide (n < length)), .and]) ++
    closeOr (q + 1)

def selectorLoopTokens (count start threshold : Nat) : List Token :=
  forTokens count (fun j => [.input (start + j), .const (decide (threshold ≤ j)), .and])

theorem selectorLoopTokens_length (count start threshold : Nat) :
    (selectorLoopTokens count start threshold).length = 3 * count := by
  simpa only [selectorLoopTokens, Nat.mul_comm] using
    forTokens_length_eq count
      (fun j => [.input (start + j), .const (decide (threshold ≤ j)), .and]) 3
      (fun _ _ => rfl)

theorem selectorLoopTokens_succ (count start threshold : Nat) :
    selectorLoopTokens (count + 1) start threshold =
      [.input start, .const (decide (threshold = 0)), .and] ++
        selectorLoopTokens count (start + 1) (threshold - 1) := by
  rw [selectorLoopTokens, forTokens_succ_first]
  simp only [Nat.add_zero, Nat.le_zero]
  apply congrArg (List.append [Token.input start, Token.const (decide (threshold = 0)), Token.and])
  apply forTokens_congr
  intro j _
  have ha : start + (j + 1) = start + 1 + j := by omega
  have ht : (threshold ≤ j + 1) = (threshold - 1 ≤ j) := propext (by omega)
  simp only [ha, ht]

theorem selectorLoopTokens_presence (q n : Nat) :
    selectorLoopTokens (q + 1) 0 (n + 1) ++ closeOr (q + 1) = presenceTokens q n := by
  simp only [selectorLoopTokens, presenceTokens]
  apply congrArg (fun xs : List Token => xs ++ closeOr (q + 1))
  apply forTokens_congr
  intro j _
  simp only [Nat.zero_add, Nat.succ_le_iff]

theorem presenceTokens_length (q n : Nat) : (presenceTokens q n).length = 4 * (q + 1) + 1 := by
  rw [← selectorLoopTokens_presence q n, List.length_append, selectorLoopTokens_length]
  simp only [closeOr, List.length_append, List.length_cons, List.length_nil, List.length_replicate]
  omega

end

open StatementCircuit WitnessCircuit WitnessEncoding PostfixModel PostfixAlignment CircuitBatch

theorem exprTokens_disjoin {ι : Type*} (wire : ι → Nat) (es : List (Expr ι)) :
    exprTokens wire (Expr.disjoin es) = forestTokens wire es ++ closeOr es.length := by
  induction es with
  | nil => simp [Expr.disjoin, exprTokens, forestTokens, closeOr]
  | cons e es ih =>
    simp [Expr.disjoin, exprTokens, forestTokens_cons, ih, closeOr,
      List.replicate_succ', List.append_assoc]

section Symbols

variable {A : Type*} [DecidableEq A]

def inputCellTokens (q : Nat) (input : List Bool) (f : Bool → A) (n : Nat) (a : Option A) :
    List Token :=
  if n < (inputPrefix input).length then [.const (decide (((inputPrefix input)[n]?).map f = a))]
  else if n - (inputPrefix input).length < q then
    muxTokens (presenceTokens q (n - (inputPrefix input).length))
      (payloadSymbolTokens q f (n - (inputPrefix input).length) a)
      [.const (decide ((none : Option A) = a))]
  else [.const (decide ((none : Option A) = a))]

end Symbols

section Initial

variable (V : NPVerifier)
variable [DecidableEq V.computation.tm.Λ] [DecidableEq V.computation.tm.σ]
variable [∀ k, DecidableEq (V.computation.tm.Γ k)]

def initialCellTokens (input : List Bool) (S : Nat) (k : V.computation.tm.K)
    (i : Fin S) (a : Option (V.computation.tm.Γ k)) : List Token :=
  if h : k = V.computation.tm.k₀ then by
    subst k
    exact inputCellTokens (V.witnessBound.eval input.length) input
      V.computation.inputAlphabet.invFun i.val a
  else [.const (decide ((none : Option (V.computation.tm.Γ k)) = a))]

end Initial

end BinPackingGames.Foundations.Complexity.CookLevin.InitializationTemplate

namespace BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine

open Turing MachineComposition PostfixModel InitializationTemplate
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ : Type} [DecidableEq K]

theorem tokenBits_append (first second : List Token) :
    tokenBits (first ++ second) = tokenBits first ++ tokenBits second := by
  simp [tokenBits, tokenWords]

theorem emitted_append (output count : K) (hne : output ≠ count)
    (base : K → List Bool) (first second : List Token) :
    emitted output count (emitted output count base first) second =
      emitted output count base (first ++ second) := by
  funext k
  by_cases ho : k = output
  · subst k
    simp [emitted, hne, tokenBits_append, List.reverse_append, List.append_assoc]
  · by_cases hc : k = count
    · subst k
      have hr : List.replicate second.length true ++ List.replicate first.length true =
          List.replicate (first.length + second.length) true := by
        rw [← List.replicate_add, Nat.add_comm]
      simp only [emitted_count, List.length_append, ← List.append_assoc, hr]
    · simp [emitted, ho, hc]

def literal (output count : K) (tokens : List Token)
    (continuation : TM2.Stmt (Alphabet (K := K)) Λ (State σ)) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  pushWord output (tokenBits tokens)
    (pushWord count (List.replicate tokens.length true) continuation)

theorem stepAux_literal (output count : K) (hne : output ≠ count)
    (tokens : List Token) (continuation : TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (state : State σ) (base : K → List Bool) :
    TM2.stepAux (literal output count tokens continuation) state base =
      TM2.stepAux continuation state (emitted output count base tokens) := by
  simp [literal, stepAux_pushWord, emitted, Ne.symm hne]

end BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ValidityMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.ValidityMachine

open Turing MachineComposition PostfixModel InitializationTemplate
open ClashMachine (State clean emitted emitted_append emitted_nil)

variable {K Λ σ : Type} [DecidableEq K]

namespace Nonempty

def copyStatement (source scratch destination : K)
    (labels : MachineUnaryAffineAt.Label → Λ) (exit : Option Λ) :
    MachineUnaryAffineAt.Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .seed => MachineUnaryAffineAt.seed destination 1 (labels .scan)
  | .scan => MachineUnaryAffineAt.scan source scratch destination 1 (labels .scan) (labels .restore)
  | .restore => Reduction.MachineTransfer.loopAt scratch source id false (labels .restore) exit

end Nonempty

end BinPackingGames.Foundations.Complexity.CookLevin.ValidityMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_PaddingCellsMachine
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.InputCellsMachine

open Turing PostfixModel InitializationTemplate
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ : Type} [DecidableEq K] {A : Nat}

theorem rowFrom_succ (table : TruthTable A) (bit : Bool) (start count : Nat) :
    rowFrom table bit start (count + 1) =
      .const (tableAt table bit start) :: rowFrom table bit (start + 1) count := by
  simp only [rowFrom, forTokens_succ_first, Nat.add_zero, List.singleton_append]
  congr 1
  apply forTokens_congr
  intro j _
  simp only [Nat.add_assoc, Nat.add_comm 1 j]

theorem streamTokens_eq_rows (table : TruthTable A) (input : List Bool) :
    streamTokens table input =
      (List.ofFn fun i : Fin input.length => rowTokens table input[i.val]).flatten := by
  rw [List.ofFn_getElem_eq_map]
  rfl

theorem tokenBits_cons (token : Token) (tokens : List Token) :
    tokenBits (token :: tokens) = token.bits ++ tokenBits tokens := by
  simp [tokenBits, tokenWords, Token.bits]

theorem tokenBits_append (first second : List Token) :
    tokenBits (first ++ second) = tokenBits first ++ tokenBits second := by
  simp [tokenBits, tokenWords]

def statement (p : Ports K) (label : Label A ↪ Λ) (exit : Option Λ)
    (table : TruthTable A) : Label A → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .scan =>
      .pop (p 0) (fun state head => (state.1, head))
        (.branch (fun state => state.2.isSome)
          (.goto fun state => label (.emit (state.2.getD false) 0))
          (.load (fun state => (state.1, none))
            (Reduction.MachineTransfer.exitAt (p 0) exit)))
  | .emit bit i =>
      if hi : i.val < A then
        pushWord (p 1) (Token.bits (.const (table bit ⟨i.val, hi⟩)))
          (.push (p 2) (fun _ => true)
            (.goto fun _ => label (.emit bit ⟨i.val + 1, by omega⟩)))
      else .load (fun state => (state.1, none)) (.goto fun _ => label .scan)

def EmitAgrees (p : Ports K) (label : Label A ↪ Λ) (exit : Option Λ) (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)) : Prop :=
  ∀ bit i, program (label (.emit bit i)) = statement p label exit table (.emit bit i)

theorem emitStep (p : Ports K) (label : Label A ↪ Λ) (exit : Option Λ) (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (ha : EmitAgrees p label exit table program) (base : K → List Bool)
    (bit : Bool) (i : Nat) (hi : i < A) (input output count : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some (label (.emit bit ⟨i, by omega⟩)), (ambient, register), tapes p base input output count⟩ =
      some ⟨some (label (.emit bit ⟨i + 1, by omega⟩)), (ambient, register),
        tapes p base input ((Token.bits (.const (tableAt table bit i))).reverse ++ output)
          (true :: count)⟩ := by
  change some (TM2.stepAux (program (label (.emit bit ⟨i, by omega⟩))) _ _) = _
  rw [ha bit ⟨i, by omega⟩]
  simp only [statement, dite_eq_left hi, stepAux_pushWord, TM2.stepAux,
    tapes_output, update_output, tapes_count, update_count, tableAt]

theorem finishRowStep (p : Ports K) (label : Label A ↪ Λ) (exit : Option Λ) (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (ha : EmitAgrees p label exit table program) (base : K → List Bool)
    (bit : Bool) (input output count : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some (label (.emit bit ⟨A, by omega⟩)), (ambient, register), tapes p base input output count⟩ =
      some ⟨some (label .scan), (ambient, none), tapes p base input output count⟩ := by
  change some (TM2.stepAux (program (label (.emit bit ⟨A, by omega⟩))) _ _) = _
  rw [ha bit ⟨A, by omega⟩]
  simp [statement, TM2.stepAux]

theorem rowTrace (p : Ports K) (label : Label A ↪ Λ) (exit : Option Λ) (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (ha : EmitAgrees p label exit table program) (base : K → List Bool)
    (bit : Bool) (start remaining : Nat) (hr : start + remaining = A)
    (input output count : List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[remaining + 1]
      (some ⟨some (label (.emit bit ⟨start, by omega⟩)), (ambient, register),
        tapes p base input output count⟩) =
      some ⟨some (label .scan), (ambient, none), tapes p base input
        ((tokenBits (rowFrom table bit start remaining)).reverse ++ output)
        (List.replicate remaining true ++ count)⟩ := by
  induction remaining generalizing start output count register with
  | zero =>
    have hs : start = A := by omega
    subst start
    simpa only [Nat.zero_add, Function.iterate_one, MachineComposition.advance_some,
      rowFrom, forTokens, tokenBits, tokenWords, List.flatMap_nil, encodeWords,
      List.reverse_nil, List.replicate_zero, List.nil_append] using
      finishRowStep p label exit table program ha base bit input output count ambient register
  | succ remaining ih =>
    have hs : start < A := by omega
    rw [Function.iterate_succ_apply]
    simp only [MachineComposition.advance_some]
    rw [emitStep p label exit table program ha base bit start hs]
    rw [ih (start + 1) (by omega)]
    rw [rowFrom_succ, tokenBits_cons, List.reverse_append]
    simp only [List.append_assoc, List.replicate_succ', List.singleton_append]

open VerifierCircuit WitnessEncoding

local instance alphabetDecidable (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

def symbolTruth (V : NPVerifier) (bit : Bool) :
    (Σ k, Option (V.computation.tm.Γ k)) → Bool
  | ⟨k, a⟩ => if h : k = V.computation.tm.k₀ then by
    subst k
    exact decide (some (V.computation.inputAlphabet.invFun bit) = a)
  else decide ((none : Option (V.computation.tm.Γ k)) = a)

def prefixTruth (V : NPVerifier) : TruthTable (indexing V).symbolCount := fun bit j =>
  symbolTruth V bit ((indexing V).symbols.symm j)

theorem symbolTruth_eq_initialCellTokens (V : NPVerifier) (input : List Bool) (S : Nat)
    (i : Fin S) (bit : Bool) (hi : i.val < (inputPrefix input).length)
    (hbit : (inputPrefix input)[i.val]? = some bit)
    (symbol : Σ k, Option (V.computation.tm.Γ k)) :
    [.const (symbolTruth V bit symbol)] = initialCellTokens V input S symbol.1 i symbol.2 := by
  obtain ⟨k, a⟩ := symbol
  by_cases hk : k = V.computation.tm.k₀
  · subst k
    simp only [symbolTruth, initialCellTokens, dite_true]
    simp only [inputCellTokens, ite_eq_left hi, hbit, Option.map_some]
  · simp [symbolTruth, initialCellTokens, hk]

theorem prefixTruth_eq_initialCellTokens (V : NPVerifier) (input : List Bool) (S : Nat)
    (i : Fin S) (bit : Bool) (hi : i.val < (inputPrefix input).length)
    (hbit : (inputPrefix input)[i.val]? = some bit) (j : Fin (indexing V).symbolCount) :
    [.const (prefixTruth V bit j)] =
      initialCellTokens V input S ((indexing V).symbols.symm j).1 i
        ((indexing V).symbols.symm j).2 :=
  symbolTruth_eq_initialCellTokens V input S i bit hi hbit ((indexing V).symbols.symm j)

theorem prefixRow_eq_initialCellTokens (V : NPVerifier) (input : List Bool) (S : Nat)
    (i : Fin S) (bit : Bool) (hi : i.val < (inputPrefix input).length)
    (hbit : (inputPrefix input)[i.val]? = some bit) :
    rowTokens (prefixTruth V) bit =
      (List.ofFn fun j : Fin (indexing V).symbolCount =>
        initialCellTokens V input S ((indexing V).symbols.symm j).1 i
          ((indexing V).symbols.symm j).2).flatten := by
  rw [rowTokens, rowFrom, forTokens_eq_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext j
  simp only [Nat.zero_add, tableAt, dite_eq_left j.isLt]
  exact prefixTruth_eq_initialCellTokens V input S i bit hi hbit j

theorem prefixStream_eq_initialCells (V : NPVerifier) (input : List Bool) (S : Nat)
    (hS : (inputPrefix input).length ≤ S) :
    streamTokens (prefixTruth V) (inputPrefix input) =
      (List.ofFn fun i : Fin (inputPrefix input).length =>
        (List.ofFn fun j : Fin (indexing V).symbolCount =>
          initialCellTokens V input S ((indexing V).symbols.symm j).1
            ⟨i.val, Nat.lt_of_lt_of_le i.isLt hS⟩
            ((indexing V).symbols.symm j).2).flatten).flatten := by
  rw [streamTokens_eq_rows]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  exact prefixRow_eq_initialCellTokens V input S ⟨i.val, Nat.lt_of_lt_of_le i.isLt hS⟩
    (inputPrefix input)[i.val] i.isLt (List.getElem?_eq_getElem i.isLt)

end BinPackingGames.Foundations.Complexity.CookLevin.InputCellsMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.InitializationControl

open Turing PostfixModel VerifierCircuit InitializationTemplate
open Reduction.MachineSubstitution

attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationControl.instDecidableEqΛTmBoolComputation
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationControl.instDecidableEqσTmBoolComputation
local instance instDecidableEqΓTmBoolComputation (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

def cells (V : NPVerifier) (input : List Bool) (S : Nat) : List Token :=
  (List.finRange S).flatMap fun i =>
    (List.finRange (indexing V).symbolCount).flatMap fun j =>
      let symbol := (indexing V).symbols.symm j
      initialCellTokens V input S symbol.1 i symbol.2

variable {K Λ σ : Type} [DecidableEq K]

def literalStatement (p : Ports K) (ts : List Token) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ σ :=
  pushWord p.reversed (tokenBits ts)
    (pushWord p.count (List.replicate ts.length true) (exitStatement exit))

theorem literalStep (p : Ports K) (ts : List Token) (exit : Option Λ)
    (base : K → List Bool) (state : σ) :
    TM2.stepAux (literalStatement p ts exit) state base =
      ⟨exit, state, emitted p base ts⟩ := by
  rw [literalStatement, stepAux_pushWord, stepAux_pushWord]
  cases exit <;>
    simp [exitStatement, TM2.stepAux, emitted, p.distinct.symm]

end BinPackingGames.Foundations.Complexity.CookLevin.InitializationControl

namespace BinPackingGames.Foundations.Complexity.CookLevin.InputCellsCapacity

open Turing PostfixModel InputCellsMachine

variable {K Λ σ : Type} [DecidableEq K] {A : Nat}

theorem tapes_other (p : Ports K) (base : K → List Bool) (remaining : Nat)
    (input output count : List Bool) (k : K) (hk : ∀ j, k ≠ p j) :
    tapes p base remaining input output count k = base k := by
  rw [tapes, InputCellsMachine.tapes_other _ _ _ _ _ _ (fun j => hk j.castSucc)]
  simp [hk]

theorem update_input (p : Ports K) (base : K → List Bool) (remaining : Nat)
    (input output count replacement : List Bool) :
    Function.update (tapes p base remaining input output count) (p 0) replacement =
      tapes p base remaining replacement output count :=
  InputCellsMachine.update_input (corePorts p) _ _ _ _ _

theorem update_capacity (p : Ports K) (base : K → List Bool) (remaining replacement : Nat)
    (input output count : List Bool) :
    Function.update (tapes p base remaining input output count) (p 3) (encodeWord replacement) =
      tapes p base replacement input output count := by
  funext k
  by_cases hk : ∃ j, p j = k
  · obtain ⟨j, rfl⟩ := hk
    fin_cases j <;> simp [p.injective.eq_iff]
  · have hn : ∀ j, k ≠ p j := fun j h => hk ⟨j, h.symm⟩
    simp only [Function.update_of_ne (hn 3),
      tapes_other p base remaining input output count k hn,
      tapes_other p base replacement input output count k hn]

def statement (p : Ports K) (label : InputCellsMachine.Label A ↪ Λ) (exit : Option Λ)
    (table : TruthTable A) :
    InputCellsMachine.Label A → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .scan =>
      .pop (p 0) (fun state head => (state.1, head))
        (.branch (fun state => state.2.isSome)
          (.pop (p 3) (fun state _ => state)
            (.goto fun state => label (.emit (state.2.getD false) 0)))
          (.load (fun state => (state.1, none))
            (Reduction.MachineTransfer.exitAt (p 0) exit)))
  | .emit bit i => InputCellsMachine.statement (corePorts p) label exit table (.emit bit i)

def Agrees (p : Ports K) (label : InputCellsMachine.Label A ↪ Λ) (exit : Option Λ)
    (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)) : Prop :=
  ∀ l, program (label l) = statement p label exit table l

omit [DecidableEq K] in
theorem emitAgrees (p : Ports K) (label : InputCellsMachine.Label A ↪ Λ) (exit : Option Λ)
    (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (ha : Agrees p label exit table program) :
    InputCellsMachine.EmitAgrees (corePorts p) label exit table program := by
  intro bit i
  exact ha (.emit bit i)

theorem scanStep_nil (p : Ports K) (label : InputCellsMachine.Label A ↪ Λ)
    (exit : Option Λ) (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (ha : Agrees p label exit table program) (base : K → List Bool) (remaining : Nat)
    (output count : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some (label .scan), (ambient, register), tapes p base remaining [] output count⟩ =
      some ⟨exit, (ambient, none), tapes p base remaining [] output count⟩ := by
  change some (TM2.stepAux (program (label .scan)) _ _) = _
  rw [ha .scan]
  cases exit <;> simp [statement, TM2.stepAux, Reduction.MachineTransfer.exitAt, update_input]

theorem scanStep_cons (p : Ports K) (label : InputCellsMachine.Label A ↪ Λ)
    (exit : Option Λ) (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (ha : Agrees p label exit table program) (base : K → List Bool) (remaining : Nat)
    (bit : Bool) (input output count : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some (label .scan), (ambient, register), tapes p base (remaining + 1) (bit :: input) output count⟩ =
      some ⟨some (label (.emit bit 0)), (ambient, some bit),
        tapes p base remaining input output count⟩ := by
  change some (TM2.stepAux (program (label .scan)) _ _) = _
  rw [ha .scan]
  simp [statement, TM2.stepAux, update_input, encodeWord, List.replicate_succ]
  exact update_capacity p base (remaining + 1) remaining input output count

theorem streamTrace_add (p : Ports K) (label : InputCellsMachine.Label A ↪ Λ)
    (exit : Option Λ) (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (ha : Agrees p label exit table program) (base : K → List Bool) (remaining : Nat)
    (input output count : List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[(A + 2) * input.length + 1]
      (some ⟨some (label .scan), (ambient, register),
        tapes p base (input.length + remaining) input output count⟩) =
      some ⟨exit, (ambient, none), tapes p base remaining []
        ((tokenBits (streamTokens table input)).reverse ++ output)
        (List.replicate (A * input.length) true ++ count)⟩ := by
  induction input generalizing output count register with
  | nil =>
    simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, Function.iterate_one,
      MachineComposition.advance_some, streamTokens, List.flatMap_nil, tokenBits,
      tokenWords, encodeWords, List.reverse_nil, List.replicate_zero, List.nil_append] using
      scanStep_nil p label exit table program ha base remaining output count ambient register
  | cons bit input ih =>
    have hround :
        (MachineComposition.advance (TM2.step program))^[A + 2]
          (some ⟨some (label .scan), (ambient, register),
            tapes p base ((bit :: input).length + remaining) (bit :: input) output count⟩) =
          some ⟨some (label .scan), (ambient, none),
            tapes p base (input.length + remaining) input
              ((tokenBits (rowTokens table bit)).reverse ++ output)
              (List.replicate A true ++ count)⟩ := by
      have hn : (bit :: input).length + remaining = (input.length + remaining) + 1 := by
        simp only [List.length_cons]
        omega
      rw [hn]
      change (MachineComposition.advance (TM2.step program))^[(A + 1) + 1] _ = _
      rw [Function.iterate_succ_apply]
      simp only [MachineComposition.advance_some]
      rw [scanStep_cons p label exit table program ha base]
      exact rowTrace (corePorts p) label exit table program
        (emitAgrees p label exit table program ha)
        (Function.update base (p 3) (encodeWord (input.length + remaining))) bit 0 A (by omega)
        input output count ambient (some bit)
    have htime : (A + 2) * (bit :: input).length + 1 =
        ((A + 2) * input.length + 1) + (A + 2) := by
      rw [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega
    rw [htime, Function.iterate_add_apply, hround, ih]
    simp only [streamTokens, List.flatMap_cons, tokenBits_append, List.reverse_append,
      List.append_assoc, List.length_cons, Nat.mul_add, Nat.mul_one]
    rw [List.replicate_add]
    simp only [List.append_assoc]

theorem streamTrace (p : Ports K) (label : InputCellsMachine.Label A ↪ Λ)
    (exit : Option Λ) (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (ha : Agrees p label exit table program) (base : K → List Bool) (S : Nat)
    (input output count : List Bool) (hS : input.length ≤ S)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[(A + 2) * input.length + 1]
      (some ⟨some (label .scan), (ambient, register), tapes p base S input output count⟩) =
      some ⟨exit, (ambient, none), tapes p base (S - input.length) []
        ((tokenBits (streamTokens table input)).reverse ++ output)
        (List.replicate (A * input.length) true ++ count)⟩ := by
  have h := streamTrace_add p label exit table program ha base (S - input.length)
    input output count ambient register
  rw [Nat.add_sub_of_le hS] at h
  exact h

theorem copyAndStreamTrace (p : Ports K) (label : InputCellsMachine.Label A ↪ Λ)
    (exit : Option Λ) (table : TruthTable A) (saved scratch : K)
    (hSaved : ∀ j, saved ≠ p j) (hScratch : ∀ j, scratch ≠ p j)
    (hSep : saved ≠ scratch) (copyFirst copySecond : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (ha : Agrees p label exit table program)
    (atFirst : program copyFirst = Reduction.MachineTransfer.loopAt saved scratch
      id false copyFirst (some copySecond))
    (atSecond : program copySecond = MachineCopy.forkLoop scratch saved (p 0)
      false copySecond (some (label .scan)))
    (base : K → List Bool) (S : Nat) (input output count : List Bool)
    (hS : input.length ≤ S) (hinput : base saved = input) (hEmpty : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[(A + 4) * input.length + 3]
      (some ⟨some copyFirst, (ambient, register), tapes p base S [] output count⟩) =
      some ⟨exit, (ambient, none), tapes p base (S - input.length) []
        ((tokenBits (streamTokens table input)).reverse ++ output)
        (List.replicate (A * input.length) true ++ count)⟩ := by
  have hsource : tapes p base S [] output count saved = input := by
    rw [tapes_other p base S [] output count saved hSaved, hinput]
  have hscratch : tapes p base S [] output count scratch = [] := by
    rw [tapes_other p base S [] output count scratch hScratch, hEmpty]
  have hc := MachineCopy.copyTrace saved (p 0) scratch (hSaved 0) hSep
    (hScratch 0).symm false copyFirst copySecond (some (label .scan)) program
    atFirst atSecond (tapes p base S [] output count) hscratch ambient register
  rw [hsource, tapes_input, List.append_nil, update_input] at hc
  have htime : (A + 4) * input.length + 3 =
      ((A + 2) * input.length + 1) + 2 * (input.length + 1) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
    omega
  rw [htime, Function.iterate_add_apply, hc]
  exact streamTrace p label exit table program ha base S input output count hS ambient none

end BinPackingGames.Foundations.Complexity.CookLevin.InputCellsCapacity

namespace BinPackingGames.Foundations.Complexity.CookLevin.CellsPrefixStage

open Turing PostfixModel InputCellsMachine

variable {K Λ σ : Type} [DecidableEq K] {A : Nat}

def capacityPorts (p : Ports K) : InputCellsCapacity.Ports K where
  toFun j := p (![4, 2, 3, 5] j)
  inj' := by
    intro i j h
    have hmap : Function.Injective (fun j : Fin 4 => (![4, 2, 3, 5] j : Fin 7)) := by decide
    exact hmap (p.injective h)

omit [DecidableEq K] in
theorem saved_distinct (p : Ports K) (j : Fin 4) : p 0 ≠ capacityPorts p j := by
  change p 0 ≠ p (![4, 2, 3, 5] j)
  fin_cases j <;> simp [p.injective.eq_iff]

omit [DecidableEq K] in
theorem scratch_distinct (p : Ports K) (j : Fin 4) : p 6 ≠ capacityPorts p j := by
  change p 6 ≠ p (![4, 2, 3, 5] j)
  fin_cases j <;> simp [p.injective.eq_iff]

theorem prepared_eq (p : Ports K) (base : K → List Bool) (S : Nat)
    (hwork : base (p 4) = []) :
    InputCellsCapacity.tapes (capacityPorts p) base S [] (base (p 2)) (base (p 3)) =
      Function.update base (p 5) (encodeWord S) := by
  change Function.update (Function.update (Function.update
    (Function.update base (p 5) (encodeWord S)) (p 4) [])
      (p 2) (base (p 2))) (p 3) (base (p 3)) = _
  funext k
  by_cases hk : ∃ j, p j = k
  · obtain ⟨j, rfl⟩ := hk
    fin_cases j <;> simp [p.injective.eq_iff, hwork]
  · have hn : ∀ j, k ≠ p j := fun j h => hk ⟨j, h.symm⟩
    simp [hn]

def statement (p : Ports K) (label : Label A ↪ Λ) (exit : Option Λ)
    (table : TruthTable A) : Label A → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .capacityFirst => Reduction.MachineTransfer.loopAt (p 1) (p 6) id false
      (label .capacityFirst) (some (label .capacitySecond))
  | .capacitySecond => MachineCopy.forkLoop (p 6) (p 1) (p 5) false
      (label .capacitySecond) (some (label .prefixFirst))
  | .prefixFirst => Reduction.MachineTransfer.loopAt (p 0) (p 6) id false
      (label .prefixFirst) (some (label .prefixSecond))
  | .prefixSecond => MachineCopy.forkLoop (p 6) (p 0) (p 4) false
      (label .prefixSecond) (some (label (.stream .scan)))
  | .stream entry => InputCellsCapacity.statement (capacityPorts p) (streamLabels label)
      exit table entry

def Agrees (p : Ports K) (label : Label A ↪ Λ) (exit : Option Λ) (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)) : Prop :=
  ∀ entry, program (label entry) = statement p label exit table entry

omit [DecidableEq K] in
theorem stream_agrees (p : Ports K) (label : Label A ↪ Λ) (exit : Option Λ)
    (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (ha : Agrees p label exit table program) :
    InputCellsCapacity.Agrees (capacityPorts p) (streamLabels label) exit table program := by
  intro entry
  exact ha (.stream entry)

theorem trace (p : Ports K) (label : Label A ↪ Λ) (exit : Option Λ)
    (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (ha : Agrees p label exit table program) (base : K → List Bool)
    (input : List Bool) (S : Nat) (hS : input.length ≤ S)
    (hinput : base (p 0) = input) (hcached : base (p 1) = encodeWord S)
    (hwork : base (p 4) = []) (hcapacity : base (p 5) = []) (hscratch : base (p 6) = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * (S + 2) + ((A + 4) * input.length + 3)]
      (some ⟨some (label .capacityFirst), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), InputCellsCapacity.tapes (capacityPorts p) base
        (S - input.length) []
        ((tokenBits (streamTokens table input)).reverse ++ base (p 2))
        (List.replicate (A * input.length) true ++ base (p 3))⟩ := by
  have hc := MachineCopy.copyTrace (p 1) (p 5) (p 6)
    (p.injective.ne (by decide)) (p.injective.ne (by decide)) (p.injective.ne (by decide))
    false (label .capacityFirst) (label .capacitySecond) (some (label .prefixFirst))
    program (ha .capacityFirst) (ha .capacitySecond) base hscratch ambient register
  rw [hcached, hcapacity, List.append_nil, encodeWord_length] at hc
  have hp := InputCellsCapacity.copyAndStreamTrace (capacityPorts p) (streamLabels label)
    exit table (p 0) (p 6) (saved_distinct p) (scratch_distinct p)
    (p.injective.ne (by decide)) (label .prefixFirst) (label .prefixSecond) program
    (stream_agrees p label exit table program ha) (ha .prefixFirst) (ha .prefixSecond)
    base S input (base (p 2)) (base (p 3)) hS hinput hscratch ambient none
  rw [prepared_eq p base S hwork] at hp
  rw [Nat.add_comm (2 * (S + 2)), Function.iterate_add_apply, hc]
  exact hp

end BinPackingGames.Foundations.Complexity.CookLevin.CellsPrefixStage

namespace BinPackingGames.Foundations.Complexity.CookLevin.PaddingCellsMachine

open Turing PostfixModel InitializationTemplate VerifierCircuit WitnessEncoding

variable {K Λ σ : Type} [DecidableEq K]

def statement (p : Ports K) (row : List Token) (again : Λ) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool) :=
  .pop (p 3) (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.load (fun state => (state.1, none))
        (InitializationControl.literalStatement (literalPorts p) row (some again)))
      (.push (p 3) (fun _ => false)
        (.load (fun state => (state.1, none))
          (InitializationControl.exitStatement exit))))

theorem step_zero (p : Ports K) (row : List Token) (again : Λ) (exit : Option Λ)
    (base : K → List Bool) (suffix output count : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.stepAux (statement p row again exit) (ambient, register)
      (frame p base (encodeWord 0 ++ suffix) output count) =
      ⟨exit, (ambient, none), frame p base (encodeWord 0 ++ suffix) output count⟩ := by
  cases exit <;>
    simp [statement, TM2.stepAux, encodeWord, InitializationControl.exitStatement]

theorem step_succ (p : Ports K) (row : List Token) (again : Λ) (exit : Option Λ)
    (base : K → List Bool) (n : Nat) (suffix output count : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.stepAux (statement p row again exit) (ambient, register)
      (frame p base (encodeWord (n + 1) ++ suffix) output count) =
      ⟨some again, (ambient, none), frame p base (encodeWord n ++ suffix)
        ((tokenBits row).reverse ++ output) (List.replicate row.length true ++ count)⟩ := by
  simp [statement, TM2.stepAux, encodeWord, List.replicate_succ,
    InitializationControl.literalStep]

theorem trace (p : Ports K) (row : List Token) (again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (code : program again = statement p row again exit)
    (base : K → List Bool) (n : Nat) (suffix output count : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some again, (ambient, register),
        frame p base (encodeWord n ++ suffix) output count⟩) =
      some ⟨exit, (ambient, none), frame p base (encodeWord 0 ++ suffix)
        ((tokenBits (repeatedRows row n)).reverse ++ output)
        (List.replicate (n * row.length) true ++ count)⟩ := by
  induction n generalizing output count register with
  | zero =>
      change some (TM2.stepAux (program again) (ambient, register)
        (frame p base (encodeWord 0 ++ suffix) output count)) = _
      rw [code, step_zero]
      simp [tokenBits, tokenWords, encodeWords]
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[n + 1]
        (some (TM2.stepAux (program again) (ambient, register)
          (frame p base (encodeWord (n + 1) ++ suffix) output count))) = _
      rw [code, step_succ, ih]
      simp only [repeatedRows_succ, OrClosure.tokenBits_append, List.reverse_append,
        List.append_assoc]
      have hc : List.replicate (n * row.length) true ++
          (List.replicate row.length true ++ count) =
          List.replicate ((n + 1) * row.length) true ++ count := by
        rw [← List.append_assoc, List.replicate_append_replicate, Nat.succ_mul]
      rw [hc]

section FixedVerifier

local instance instDecidableEqΛTmBoolComputation_r1a2749_1 (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance instDecidableEqσTmBoolComputation_r1a2749_1 (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance instDecidableEqΓTmBoolComputation (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

theorem initialCellTokens_padding (V : NPVerifier) (input : List Bool) (S : Nat)
    (k : V.computation.tm.K) (i : Fin S) (a : Option (V.computation.tm.Γ k))
    (padding : (inputPrefix input).length + V.witnessBound.eval input.length ≤ i.val) :
    initialCellTokens V input S k i a = [.const (decide ((none : Option _) = a))] := by
  have hp : ¬ i.val < (inputPrefix input).length := by omega
  have hq : ¬ i.val - (inputPrefix input).length < V.witnessBound.eval input.length := by omega
  by_cases hk : k = V.computation.tm.k₀
  · subst k
    simp only [initialCellTokens, inputCellTokens, ite_eq_right hp, ite_eq_right hq, dite_eq_ite, ite_self]
  · simp [initialCellTokens, hk]

theorem cellRow_padding (V : NPVerifier) (input : List Bool) (S : Nat) (i : Fin S)
    (padding : (inputPrefix input).length + V.witnessBound.eval input.length ≤ i.val) :
    ((List.finRange (indexing V).symbolCount).flatMap fun j =>
      let symbol := (indexing V).symbols.symm j
      initialCellTokens V input S symbol.1 i symbol.2) = blankRow V := by
  simp only [initialCellTokens_padding V input S _ i _ padding]
  exact List.map_eq_flatMap.symm

def cellsInterval (V : NPVerifier) (input : List Bool) (S start n : Nat)
    (within : start + n ≤ S) : List Token :=
  (List.finRange n).flatMap fun i =>
    (List.finRange (indexing V).symbolCount).flatMap fun j =>
      let symbol := (indexing V).symbols.symm j
      initialCellTokens V input S symbol.1 ⟨start + i.val, by omega⟩ symbol.2

theorem cellsInterval_padding (V : NPVerifier) (input : List Bool) (S start n : Nat)
    (within : start + n ≤ S)
    (padding : (inputPrefix input).length + V.witnessBound.eval input.length ≤ start) :
    cellsInterval V input S start n within = repeatedRows (blankRow V) n := by
  unfold cellsInterval
  have hrow (i : Fin n) :
      ((List.finRange (indexing V).symbolCount).flatMap fun j =>
        let symbol := (indexing V).symbols.symm j
        initialCellTokens V input S symbol.1 ⟨start + i.val, by omega⟩ symbol.2) =
      blankRow V := cellRow_padding V input S _ (by
        change (inputPrefix input).length + V.witnessBound.eval input.length ≤ start + i.val
        omega)
  simp_rw [hrow]
  simp [List.flatMap_def, repeatedRows]

end FixedVerifier

end BinPackingGames.Foundations.Complexity.CookLevin.PaddingCellsMachine

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_InitializationMachine
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.InitializationMachine

open Turing
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)
open PostfixModel

@[simp] theorem tapes_reversed (base : Tape → List Bool) (m i d : Nat) (output : List Bool) :
    tapes base m i d output .reversed = output := rfl

def termTokens (i d : Nat) : List Token :=
  [.input i, .const (decide (d = 0)), .and]

theorem termTokens_bits (i d : Nat) :
    tokenBits (termTokens i d) = encodeWord 5 ++ encodeWord i ++
      encodeWords [if decide (d = 0) then 1 else 0, 3] := by
  by_cases hd : d = 0 <;>
    simp [termTokens, tokenBits, tokenWords, Token.words, hd, encodeWords, List.append_assoc]

theorem tokens_append_bits (xs ys : List Token) :
    tokenBits (xs ++ ys) = tokenBits xs ++ tokenBits ys := by
  simp [tokenBits, tokenWords, List.flatMap_append]

theorem selectorSteps_le (i m : Nat) :
    selectorSteps i m ≤ m * (3 * (i + m) + 6) + 1 := by
  induction m generalizing i with
  | zero => simp [selectorSteps]
  | succ m ih =>
    let B := 3 * (i + (m + 1)) + 6
    have hbody : 1 + bodySteps i ≤ B := by unfold bodySteps B; omega
    have hrest : selectorSteps (i + 1) m ≤ m * B + 1 := by
      simpa only [B, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (i + 1)
    calc
      selectorSteps i (m + 1) = (1 + bodySteps i) + selectorSteps (i + 1) m := rfl
      _ ≤ B + (m * B + 1) := Nat.add_le_add hbody hrest
      _ = (m + 1) * B + 1 := by rw [Nat.succ_mul]; omega

end BinPackingGames.Foundations.Complexity.CookLevin.InitializationMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_InitializationMachineAt
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.InitializationMachineAt

open Turing PostfixModel
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)
open InitializationMachine (Label termTokens bodySteps selectorSteps)

variable {K Λ σ : Type} [DecidableEq K]

def contents (m i d : Nat) (output count : List Bool) (j : Fin 6) : List Bool :=
  match j.val with
  | 0 => encodeWord m
  | 1 => encodeWord i
  | 2 => encodeWord d
  | 3 => []
  | 4 => output
  | _ => count

def tapes (p : Ports K) (base : K → List Bool) (m i d : Nat)
    (output count : List Bool) : K → List Bool := frame p base (contents m i d output count)

@[simp] theorem tapes_at (p : Ports K) (base : K → List Bool) (m i d : Nat)
    (output count : List Bool) (j : Fin 6) :
    tapes p base m i d output count (p j) = contents m i d output count j := by
  exact frame_at p base _ j

theorem tapes_other (p : Ports K) (base : K → List Bool) (m i d : Nat)
    (output count : List Bool) (k : K) (hk : ∀ j, k ≠ p j) :
    tapes p base m i d output count k = base k := frame_other p base _ k hk

theorem update_remaining (p : Ports K) (base : K → List Bool) (m i d r : Nat)
    (output count : List Bool) :
    Function.update (tapes p base m i d output count) (p 0) (encodeWord r) =
      tapes p base r i d output count := by
  rw [tapes, update_frame]
  congr 1
  funext j
  fin_cases j <;> simp [contents]

theorem update_current (p : Ports K) (base : K → List Bool) (m i d r : Nat)
    (output count : List Bool) :
    Function.update (tapes p base m i d output count) (p 1) (encodeWord r) =
      tapes p base m r d output count := by
  rw [tapes, update_frame]
  congr 1
  funext j
  fin_cases j <;> simp [contents]

theorem update_threshold (p : Ports K) (base : K → List Bool) (m i d r : Nat)
    (output count : List Bool) :
    Function.update (tapes p base m i d output count) (p 2) (encodeWord r) =
      tapes p base m i r output count := by
  rw [tapes, update_frame]
  congr 1
  funext j
  fin_cases j <;> simp [contents]

theorem update_reversed (p : Ports K) (base : K → List Bool) (m i d : Nat)
    (output count replacement : List Bool) :
    Function.update (tapes p base m i d output count) (p 4) replacement =
      tapes p base m i d replacement count := by
  rw [tapes, update_frame]
  congr 1
  funext j
  fin_cases j <;> simp [contents]

theorem update_count (p : Ports K) (base : K → List Bool) (m i d : Nat)
    (output count replacement : List Bool) :
    Function.update (tapes p base m i d output count) (p 5) replacement =
      tapes p base m i d output replacement := by
  rw [tapes, update_frame]
  congr 1
  funext j
  fin_cases j <;> simp [contents]

theorem push_current (p : Ports K) (base : K → List Bool) (m i d : Nat)
    (output count : List Bool) :
    Function.update (tapes p base m i d output count) (p 1) (true :: encodeWord i) =
      tapes p base m (i + 1) d output count := by
  rw [show true :: encodeWord i = encodeWord (i + 1) by
    simp [encodeWord, List.replicate_succ]]
  exact update_current p base m i d (i + 1) output count

def statement (p : Ports K) (label : Label ↪ Λ) : Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .guard => MachineUnaryCounter.guard (p 0) (label .inputTag) (label .done)
  | .inputTag => pushWord (p 4) (encodeWord 5) (.goto fun _ => label .scan)
  | .scan => MachineTransducerCopy.scanLoop (p 1) (p 3) false
      (fun _ b => label (.emit b)) (label .restore)
  | .emit b => MachineTransducerCopy.emitter (p 4) (fun _ _ => false)
      (fun _ symbol => [symbol]) (label .scan) false b
  | .restore => Reduction.MachineTransfer.loopAt (p 3) (p 1) id false
      (label .restore) (some (label .test))
  | .test => MachineUnaryCounter.guard (p 2) (label (.result false)) (label (.result true))
  | .result b => pushWord (p 4) (encodeWords [if b then 1 else 0, 3])
      (.push (p 5) (fun _ => true) (.push (p 5) (fun _ => true)
        (.push (p 5) (fun _ => true)
          (.push (p 1) (fun _ => true) (.goto fun _ => label .guard)))))
  | .done => .halt

def Agrees (p : Ports K) (label : Label ↪ Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ)) : Prop :=
  ∀ l, l ≠ .done → program (label l) = statement p label l

theorem inputTagStep (p : Ports K) (label : Label ↪ Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ)) (ha : Agrees p label program)
    (base : K → List Bool) (m i d : Nat) (output count : List Bool) (ambient : σ) :
    TM2.step program ⟨some (label .inputTag), initialState ambient, tapes p base m i d output count⟩ =
      some ⟨some (label .scan), initialState ambient,
        tapes p base m i d ((encodeWord 5).reverse ++ output) count⟩ := by
  change some (TM2.stepAux (program (label .inputTag)) _ _) = _
  rw [ha .inputTag (by decide), statement, stepAux_pushWord]
  simp [TM2.stepAux, contents, update_reversed]

theorem thresholdStep (p : Ports K) (label : Label ↪ Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ)) (ha : Agrees p label program)
    (base : K → List Bool) (m i d : Nat) (output count : List Bool) (ambient : σ) :
    TM2.step program ⟨some (label .test), initialState ambient, tapes p base m i d output count⟩ =
      some ⟨some (label (.result (decide (d = 0)))), initialState ambient,
        tapes p base m i (d - 1) output count⟩ := by
  change some (TM2.stepAux (program (label .test)) _ _) = _
  rw [ha .test (by decide)]
  cases d with
  | zero => simp [statement, MachineUnaryCounter.guard, TM2.stepAux, contents, initialState, encodeWord]
  | succ d =>
    simp only [statement, MachineUnaryCounter.guard, TM2.stepAux, initialState,
      tapes_at, contents, encodeWord, List.replicate_succ, List.cons_append]
    change some (⟨some (label (.result false)), initialState ambient,
      Function.update (tapes p base m i (d + 1) output count) (p 2) (encodeWord d)⟩ :
      TM2.Cfg (Alphabet (K := K)) Λ (State σ)) = _
    rw [update_threshold]
    simp [initialState]

theorem resultStep (p : Ports K) (label : Label ↪ Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ)) (ha : Agrees p label program)
    (base : K → List Bool) (m i d : Nat) (output count : List Bool) (ambient : σ) (b : Bool) :
    TM2.step program ⟨some (label (.result b)), initialState ambient, tapes p base m i d output count⟩ =
      some ⟨some (label .guard), initialState ambient, tapes p base m (i + 1) d
        ((encodeWords [if b then 1 else 0, 3]).reverse ++ output) (true :: true :: true :: count)⟩ := by
  change some (TM2.stepAux (program (label (.result b))) _ _) = _
  rw [ha (.result b) (by intro h; cases h), statement, stepAux_pushWord]
  simp [TM2.stepAux, contents, update_reversed, update_count, push_current]

theorem guardStep_zero (p : Ports K) (label : Label ↪ Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ)) (ha : Agrees p label program)
    (base : K → List Bool) (i d : Nat) (output count : List Bool) (ambient : σ) :
    TM2.step program ⟨some (label .guard), initialState ambient, tapes p base 0 i d output count⟩ =
      some ⟨some (label .done), initialState ambient, tapes p base 0 i d output count⟩ := by
  change some (TM2.stepAux (program (label .guard)) _ _) = _
  rw [ha .guard (by decide)]
  simp [statement, MachineUnaryCounter.guard, TM2.stepAux, contents, initialState, encodeWord]

theorem guardStep_succ (p : Ports K) (label : Label ↪ Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ)) (ha : Agrees p label program)
    (base : K → List Bool) (m i d : Nat) (output count : List Bool) (ambient : σ) :
    TM2.step program ⟨some (label .guard), initialState ambient, tapes p base (m + 1) i d output count⟩ =
      some ⟨some (label .inputTag), initialState ambient, tapes p base m i d output count⟩ := by
  change some (TM2.stepAux (program (label .guard)) _ _) = _
  rw [ha .guard (by decide)]
  simp only [statement, MachineUnaryCounter.guard, TM2.stepAux, initialState,
    tapes_at, contents, encodeWord, List.replicate_succ, List.cons_append]
  change some (⟨some (label .inputTag), initialState ambient,
    Function.update (tapes p base (m + 1) i d output count) (p 0) (encodeWord m)⟩ :
    TM2.Cfg (Alphabet (K := K)) Λ (State σ)) = _
  rw [update_remaining]
  rfl

def closurePorts (p : Ports K) (closing : K) (hc : ∀ j, closing ≠ p j) : OrClosure.Ports K where
  remaining := closing
  reversed := p 4
  count := p 5
  remaining_ne_reversed := hc 4
  remaining_ne_count := hc 5
  reversed_ne_count := p.injective.ne (by decide)

theorem presenceSteps_le (q : Nat) :
    selectorSteps 0 (q + 1) + (q + 1 + 2) ≤
      (q + 1) * (3 * (q + 1) + 7) + 3 := by
  have h := InitializationMachine.selectorSteps_le 0 (q + 1)
  simp only [Nat.zero_add] at h
  rw [show 3 * (q + 1) + 7 = (3 * (q + 1) + 6) + 1 by omega,
    Nat.mul_add, Nat.mul_one]
  omega

end BinPackingGames.Foundations.Complexity.CookLevin.InitializationMachineAt

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_PayloadPresenceMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.PayloadPresenceMachine

open Turing MachineComposition PostfixModel InitializationTemplate
open ClashMachine (State clean emitted)

variable {K Λ σ : Type} [DecidableEq K]

def closurePorts (slots : Ports K) : OrClosure.Ports K :=
  InitializationMachineAt.closurePorts (presenceMap.trans slots) (slots 6) (closing_distinct slots)

def statement (slots : Ports K) (labels : Label ↪ Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .initialize_ => .push (slots 3) (fun _ => false) (.goto fun _ => labels (.copy .remaining .seed))
  | .copy context l => ValidityMachine.Nonempty.copyStatement (copySource slots context) (slots 5)
      (copyTarget slots context) (fun l => labels (.copy context l)) (some (copyExit labels context)) l
  | .presence .done => OrClosure.seed (closurePorts slots) (labels .orLoop)
  | .presence l => InitializationMachineAt.statement (presenceMap.trans slots)
      (presenceLabels.trans labels) l
  | .orLoop => OrClosure.loop (closurePorts slots) (labels .orLoop) (some (labels .cleanup))
  | .cleanup => .pop (slots 2) (fun s _ => s)
      (.pop (slots 4) (fun s _ => s) (.pop (slots 6) (fun s _ => s) (.goto fun _ => labels .drain)))
  | .drain => MachineDrain.drain (slots 3) (labels .drain) exit

structure Ready (slots : Ports K) (base : K → List Bool) (q i : Nat) : Prop where
  boundWord : base (slots 0) = encodeWord q
  indexWord : base (slots 1) = encodeWord i
  empty : ∀ j : Fin 9, j ≠ 0 → j ≠ 1 → j ≠ 7 → j ≠ 8 → base (slots j) = []

theorem Ready.emitted {slots : Ports K} {base : K → List Bool} {q i : Nat}
    (h : Ready slots base q i) (tokens : List Token) :
    Ready slots (emitted (slots 7) (slots 8) base tokens) q i := by
  constructor
  · simpa [ClashMachine.emitted, slots.injective.eq_iff] using h.boundWord
  · simpa [ClashMachine.emitted, slots.injective.eq_iff] using h.indexWord
  · intro j h₀ h₁ h₇ h₈
    simpa [ClashMachine.emitted, slots.injective.eq_iff, h₇, h₈] using h.empty j h₀ h₁ h₇ h₈

def working (slots : Ports K) (base : K → List Bool) (r j d c : Nat) : K → List Bool :=
  Function.update (Function.update (Function.update (Function.update base
    (slots 2) (encodeWord r)) (slots 3) (encodeWord j)) (slots 4) (encodeWord d))
      (slots 6) (encodeWord c)

theorem steps_le (q i : Nat) (hi : i < q) : steps q i ≤ 30 * (q + 2) ^ 2 := by
  have h := InitializationMachineAt.presenceSteps_le q
  unfold steps
  nlinarith

end BinPackingGames.Foundations.Complexity.CookLevin.PayloadPresenceMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_CellsTokensAlignment
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.PayloadCellsMachine

open Turing MachineComposition PostfixModel InitializationTemplate
open ClashMachine (State clean emitted)
open PayloadPresenceMachine (Ports Ready)

variable {K Λ σ : Type} [DecidableEq K]

def payloadTokens (address : Nat) (yes no : Bool) : List Token :=
  [.input address, .const yes, .and, .input address, .not, .const no, .and, .or]

def symbolTokens (spec : SymbolSpec) (q i : Nat) : List Token :=
  if spec.isInput then
    muxTokens (presenceTokens q i) (payloadTokens (q + 1 + i) spec.trueValue spec.falseValue)
      [.const spec.absentValue]
  else [.const spec.absentValue]

namespace Payload

def statement (slots : Ports K) (labels : Label → Λ) (exit : Option Λ) (yes no : Bool) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .seed => MachineUnaryAffineAt.seed (slots 3) 1 (labels .scanQ)
  | .scanQ => MachineUnaryAffineAt.scan (slots 0) (slots 5) (slots 3) 1
      (labels .scanQ) (labels .restoreQ)
  | .restoreQ => Reduction.MachineTransfer.loopAt (slots 5) (slots 0) id false
      (labels .restoreQ) (some (labels .scanI))
  | .scanI => MachineUnaryAffineAt.scan (slots 1) (slots 5) (slots 3) 1
      (labels .scanI) (labels .restoreI)
  | .restoreI => Reduction.MachineTransfer.loopAt (slots 5) (slots 1) id false
      (labels .restoreI) (some (labels (.inputTrue .tag)))
  | .inputTrue l => ClashMachine.Input.statement (inputMap.trans slots)
      (fun l => labels (.inputTrue l)) (some (labels .middle)) l
  | .middle => ClashMachine.literal (slots 7) (slots 8) [.const yes, .and]
      (.goto fun _ => labels (.inputFalse .tag))
  | .inputFalse l => ClashMachine.Input.statement (inputMap.trans slots)
      (fun l => labels (.inputFalse l)) (some (labels .suffix)) l
  | .suffix => ClashMachine.literal (slots 7) (slots 8) [.not, .const no, .and, .or]
      (.goto fun _ => labels .drain)
  | .drain => MachineDrain.drain (slots 3) (labels .drain) exit

end Payload

namespace Symbol

def statement (slots : Ports K) (labels : Label ↪ Λ) (exit : Option Λ) (spec : SymbolSpec) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .start => if spec.isInput then .goto fun _ => labels (.first .initialize_)
      else ClashMachine.literal (slots 7) (slots 8) [.const spec.absentValue]
        (Reduction.MachineTransfer.exitAt (slots 7) exit)
  | .first l => PayloadPresenceMachine.statement slots (firstLabels.trans labels)
      (some (labels (.payload .seed))) l
  | .payload l => Payload.statement slots (fun l => labels (.payload l))
      (some (labels .conjunction)) spec.trueValue spec.falseValue l
  | .conjunction => ClashMachine.literal (slots 7) (slots 8) [.and]
      (.goto fun _ => labels (.second .initialize_))
  | .second l => PayloadPresenceMachine.statement slots (secondLabels.trans labels)
      (some (labels .suffix)) l
  | .suffix => ClashMachine.literal (slots 7) (slots 8) [.not, .const spec.absentValue, .and, .or]
      (Reduction.MachineTransfer.exitAt (slots 7) exit)

theorem steps_le (spec : SymbolSpec) (q i : Nat) (hi : i < q) :
    steps spec q i ≤ 120 * (q + 2) ^ 2 := by
  have hq : q + 2 ≤ (q + 2) ^ 2 := by nlinarith
  have hp := Payload.steps_le q i hi
  have hc := PayloadPresenceMachine.steps_le q i hi
  unfold steps
  split <;> omega

end Symbol

namespace Row

variable {A : Nat}

def tokensFrom (table : Fin A → SymbolSpec) (q i start count : Nat) : List Token :=
  forTokens count (fun j => symbolTokens (tableAt table (start + j)) q i)

def tokens (table : Fin A → SymbolSpec) (q i : Nat) : List Token := tokensFrom table q i 0 A

theorem tokensFrom_succ (table : Fin A → SymbolSpec) (q i start count : Nat) :
    tokensFrom table q i start (count + 1) =
      symbolTokens (tableAt table start) q i ++ tokensFrom table q i (start + 1) count := by
  rw [tokensFrom, forTokens_succ_first]
  simp only [Nat.add_zero]
  apply congrArg (List.append (symbolTokens (tableAt table start) q i))
  apply forTokens_congr
  intro j _
  rw [show start + (j + 1) = start + 1 + j by omega]

theorem tokens_eq_ofFn (table : Fin A → SymbolSpec) (q i : Nat) :
    tokens table q i = (List.ofFn fun j : Fin A => symbolTokens (table j) q i).flatten := by
  rw [tokens, tokensFrom, forTokens_eq_ofFn]
  congr 1
  congr 1
  funext j
  simp [tableAt, j.isLt]

def statement (slots : Ports K) (labels : Label A ↪ Λ) (exit : Option Λ)
    (table : Fin A → SymbolSpec) : Label A → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .visit j => if hj : j.val < A then .goto fun _ => labels (.symbol ⟨j.val, hj⟩ .start)
      else Reduction.MachineTransfer.exitAt (slots 7) exit
  | .symbol j l => Symbol.statement slots ((symbolLabels j).trans labels)
      (some (labels (.visit ⟨j.val + 1, by omega⟩))) (table j) l

theorem stepsFrom_le (table : Fin A → SymbolSpec) (q i start count : Nat) (hi : i < q) :
    stepsFrom table q i start count ≤ count * (120 * (q + 2) ^ 2 + 1) + 1 := by
  induction count generalizing start with
  | zero => simp [stepsFrom]
  | succ count ih =>
    have hs := Symbol.steps_le (tableAt table start) q i hi
    have hr := ih (start + 1)
    rw [stepsFrom, Nat.succ_mul]
    omega

theorem steps_le (table : Fin A → SymbolSpec) (q i : Nat) (hi : i < q) :
    steps table q i ≤ A * (120 * (q + 2) ^ 2 + 1) + 1 := stepsFrom_le table q i 0 A hi

end Row

end BinPackingGames.Foundations.Complexity.CookLevin.PayloadCellsMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.PayloadRowsLoop

open Turing MachineComposition PostfixModel InitializationTemplate
open ClashMachine (State clean emitted emitted_append)
open PayloadCellsMachine (SymbolSpec)

variable {K Λ σ : Type} [DecidableEq K] {A : Nat}

theorem ext_ports (p : Ports K) {f g : K → List Bool}
    (atPorts : ∀ j, f (p j) = g (p j))
    (outside : ∀ k, (∀ j, k ≠ p j) → f k = g k) : f = g := by
  funext k
  by_cases hk : ∃ j, p j = k
  · obtain ⟨j, rfl⟩ := hk
    exact atPorts j
  · exact outside k (fun j h => hk ⟨j, h.symm⟩)

theorem update_remaining (p : Ports K) (base : K → List Bool) (m i c r : Nat) :
    Function.update (frame p base m i c) (p 9) (encodeWord r) = frame p base r i c := by
  apply ext_ports p
  · intro j
    fin_cases j <;> simp [frame, p.injective.eq_iff]
  · intro k hk
    simp [frame, hk]

theorem update_index (p : Ports K) (base : K → List Bool) (m i c r : Nat) :
    Function.update (frame p base m i c) (p 1) (encodeWord r) = frame p base m r c := by
  apply ext_ports p
  · intro j
    fin_cases j <;> simp [frame, p.injective.eq_iff]
  · intro k hk
    simp [frame, hk]

theorem update_capacity (p : Ports K) (base : K → List Bool) (m i c r : Nat) :
    Function.update (frame p base m i c) (p 10) (encodeWord r) = frame p base m i r := by
  simp [frame]

theorem frame_emitted (p : Ports K) (base : K → List Bool) (m i c : Nat) (tokens : List Token) :
    emitted (p 7) (p 8) (frame p base m i c) tokens =
      frame p (emitted (p 7) (p 8) base tokens) m i c := by
  apply ext_ports p
  · intro j
    fin_cases j <;> simp [frame, emitted, p.injective.eq_iff]
  · intro k hk
    simp [frame, emitted, hk]

theorem frame_ready (p : Ports K) (base : K → List Bool) (q m i c : Nat)
    (ready : PayloadPresenceMachine.Ready (rowPorts p) base q 0) :
    PayloadPresenceMachine.Ready (rowPorts p) (frame p base m i c) q i := by
  constructor
  · change frame p base m i c (p 0) = encodeWord q
    have boundWord : base (p 0) = encodeWord q := ready.boundWord
    simpa [frame, p.injective.eq_iff] using boundWord
  · exact frame_index p base m i c
  · intro j h₀ h₁ h₇ h₈
    have h1 : rowMap j ≠ (1 : Fin 11) := by
      intro h
      apply h₁
      exact Fin.ext (congrArg (fun x : Fin 11 => x.val) h)
    have h9 : rowMap j ≠ (9 : Fin 11) := by
      intro h
      have hv := congrArg (fun x : Fin 11 => x.val) h
      change j.val = 9 at hv
      omega
    have h10 : rowMap j ≠ (10 : Fin 11) := by
      intro h
      have hv := congrArg (fun x : Fin 11 => x.val) h
      change j.val = 10 at hv
      omega
    simpa only [rowPorts, Function.Embedding.trans_apply, frame,
      Function.update_of_ne (p.injective.ne h10), Function.update_of_ne (p.injective.ne h9),
      Function.update_of_ne (p.injective.ne h1)] using ready.empty j h₀ h₁ h₇ h₈

def statement (p : Ports K) (label : Label A ↪ Λ) (exit : Λ)
    (table : Fin A → SymbolSpec) : Label A → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .guard => MachineUnaryCounter.guard (p 9) (label (.row (.visit 0))) exit
  | .next => .pop (p 10) (fun state _ => state)
      (.push (p 1) (fun _ => true) (.goto fun _ => label .guard))
  | .row entry => PayloadCellsMachine.Row.statement (rowPorts p) (rowLabels label)
      (some (label .next)) table entry

def Agrees (p : Ports K) (label : Label A ↪ Λ) (exit : Λ) (table : Fin A → SymbolSpec)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ)) : Prop :=
  ∀ entry, program (label entry) = statement p label exit table entry

theorem guardStep_zero (p : Ports K) (label : Label A ↪ Λ) (exit : Λ)
    (table : Fin A → SymbolSpec) (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (ha : Agrees p label exit table program) (base : K → List Bool) (i c : Nat) (ambient : σ) :
    TM2.step program ⟨some (label .guard), clean ambient, frame p base 0 i c⟩ =
      some ⟨some exit, clean ambient, frame p base 0 i c⟩ := by
  change some (TM2.stepAux (program (label .guard)) _ _) = _
  rw [ha .guard]
  simp [statement, MachineUnaryCounter.guard, TM2.stepAux, clean, encodeWord]

theorem guardStep_succ (p : Ports K) (label : Label A ↪ Λ) (exit : Λ)
    (table : Fin A → SymbolSpec) (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (ha : Agrees p label exit table program) (base : K → List Bool) (m i c : Nat) (ambient : σ) :
    TM2.step program ⟨some (label .guard), clean ambient, frame p base (m + 1) i c⟩ =
      some ⟨some (label (.row (.visit 0))), clean ambient, frame p base m i c⟩ := by
  change some (TM2.stepAux (program (label .guard)) _ _) = _
  rw [ha .guard]
  simp [statement, MachineUnaryCounter.guard, TM2.stepAux, clean, encodeWord, List.replicate_succ]
  exact update_remaining p base (m + 1) i c m

theorem nextStep (p : Ports K) (label : Label A ↪ Λ) (exit : Λ)
    (table : Fin A → SymbolSpec) (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (ha : Agrees p label exit table program) (base : K → List Bool) (m i c : Nat) (ambient : σ) :
    TM2.step program ⟨some (label .next), clean ambient, frame p base m i (c + 1)⟩ =
      some ⟨some (label .guard), clean ambient, frame p base m (i + 1) c⟩ := by
  change some (TM2.stepAux (program (label .next)) _ _) = _
  rw [ha .next]
  simp only [statement, TM2.stepAux, frame_capacity, encodeWord, List.replicate_succ,
    List.cons_append, List.tail_cons]
  rw [Function.update_of_ne (p.injective.ne (by decide : (1 : Fin 11) ≠ 10))]
  change some (⟨some (label .guard), clean ambient,
    Function.update (Function.update (frame p base m i (c + 1)) (p 10) (encodeWord c))
      (p 1) (true :: frame p base m i (c + 1) (p 1))⟩ : TM2.Cfg (Alphabet (K := K)) Λ (State σ)) = _
  rw [update_capacity, frame_index]
  rw [show true :: encodeWord i = encodeWord (i + 1) by simp [encodeWord, List.replicate_succ]]
  rw [update_index]

def tokens (table : Fin A → SymbolSpec) (q : Nat) : Nat → Nat → List Token
  | _, 0 => []
  | i, m + 1 => PayloadCellsMachine.Row.tokens table q i ++ tokens table q (i + 1) m

theorem steps_le (table : Fin A → SymbolSpec) (q i m : Nat) (hbound : i + m ≤ q) :
    steps table q i m ≤ m * (A * (120 * (q + 2) ^ 2 + 1) + 3) + 1 := by
  induction m generalizing i with
  | zero => simp [steps]
  | succ m ih =>
    have ht := ih (i + 1) (by omega)
    have hr := PayloadCellsMachine.Row.steps_le table q i (by omega)
    rw [steps, Nat.succ_mul]
    omega

theorem tokens_eq_forTokens (table : Fin A → SymbolSpec) (q i m : Nat) :
    tokens table q i m = forTokens m (fun j => PayloadCellsMachine.Row.tokens table q (i + j)) := by
  induction m generalizing i with
  | zero => rfl
  | succ m ih =>
    rw [tokens, forTokens_succ_first, Nat.add_zero, ih]
    apply congrArg (List.append (PayloadCellsMachine.Row.tokens table q i))
    apply forTokens_congr
    intro j _
    rw [show i + 1 + j = i + (j + 1) by omega]

end BinPackingGames.Foundations.Complexity.CookLevin.PayloadRowsLoop

namespace BinPackingGames.Foundations.Complexity.CookLevin.PayloadCellsMachine

open InitializationTemplate WitnessEncoding

local instance alphabetDecidable (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

def symbolSpec (V : NPVerifier) (k : V.computation.tm.K)
    (a : Option (V.computation.tm.Γ k)) : SymbolSpec :=
  if h : k = V.computation.tm.k₀ then by
    subst k
    exact ⟨true, decide (some (V.computation.inputAlphabet.invFun true) = a),
      decide (some (V.computation.inputAlphabet.invFun false) = a), decide (none = a)⟩
  else ⟨false, false, false, decide (none = a)⟩

def symbolTable (V : NPVerifier) : Fin (VerifierCircuit.indexing V).symbolCount → SymbolSpec :=
  fun j => let symbol := (VerifierCircuit.indexing V).symbols.symm j
    symbolSpec V symbol.1 symbol.2

def payloadRowTokens (V : NPVerifier) (q i : Nat) : List PostfixModel.Token :=
  Row.tokens (symbolTable V) q i

theorem symbolTokens_eq_initialCellTokens (V : NPVerifier) (input : List Bool) (S i : Nat)
    (hi : i < V.witnessBound.eval input.length)
    (hS : (inputPrefix input).length + i < S) (k : V.computation.tm.K)
    (a : Option (V.computation.tm.Γ k)) :
    symbolTokens (symbolSpec V k a) (V.witnessBound.eval input.length) i =
      initialCellTokens V input S k ⟨(inputPrefix input).length + i, hS⟩ a := by
  by_cases hk : k = V.computation.tm.k₀
  · subst k
    have hp : ¬ (inputPrefix input).length + i < (inputPrefix input).length := by omega
    have hn : (inputPrefix input).length + i - (inputPrefix input).length = i := by omega
    have hcell : inputCellTokens (V.witnessBound.eval input.length) input
        V.computation.inputAlphabet.invFun ((inputPrefix input).length + i) a =
        muxTokens (presenceTokens (V.witnessBound.eval input.length) i)
          (payloadSymbolTokens (V.witnessBound.eval input.length)
            V.computation.inputAlphabet.invFun i a) [.const (decide (none = a))] := by
      simp only [inputCellTokens, ite_eq_right hp, hn, ite_eq_left hi]
    simpa [symbolTokens, symbolSpec, initialCellTokens, payloadTokens, payloadSymbolTokens] using hcell.symm
  · simp [symbolSpec, symbolTokens, initialCellTokens, hk]

theorem payloadRowTokens_eq (V : NPVerifier) (input : List Bool) (S i : Nat)
    (hi : i < V.witnessBound.eval input.length) (hS : (inputPrefix input).length + i < S) :
    payloadRowTokens V (V.witnessBound.eval input.length) i =
      (List.ofFn fun j : Fin (VerifierCircuit.indexing V).symbolCount =>
        let symbol := (VerifierCircuit.indexing V).symbols.symm j
        initialCellTokens V input S symbol.1 ⟨(inputPrefix input).length + i, hS⟩ symbol.2).flatten := by
  rw [payloadRowTokens, Row.tokens_eq_ofFn]
  congr 1
  congr 1
  funext j
  exact symbolTokens_eq_initialCellTokens V input S i hi hS _ _

end BinPackingGames.Foundations.Complexity.CookLevin.PayloadCellsMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.CellsTokensAlignment

open WitnessEncoding InitializationTemplate PaddingCellsMachine

local instance instDecidableEqΛTmBoolComputation_r1a2749_2 (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance instDecidableEqσTmBoolComputation_r1a2749_2 (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance instDecidableEqΓTmBoolComputation_r1a2749_1 (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _
theorem cellsInterval_append (V : NPVerifier) (input : List Bool) (S start m n : Nat)
    (within : start + (m + n) ≤ S) :
    cellsInterval V input S start (m + n) within =
      cellsInterval V input S start m (by omega) ++
        cellsInterval V input S (start + m) n (by omega) := by
  simp only [cellsInterval, List.flatMap_def, ← List.ofFn_eq_map]
  rw [List.ofFn_add, List.flatten_append]
  simp only [Fin.val_castLE, Fin.val_natAdd, Nat.add_assoc]

theorem cellsInterval_full (V : NPVerifier) (input : List Bool) (S : Nat) :
    cellsInterval V input S 0 S (by omega) = InitializationControl.cells V input S := by
  simp only [cellsInterval, InitializationControl.cells, Nat.zero_add]

theorem prefix_eq_interval (V : NPVerifier) (input : List Bool) (S : Nat)
    (within : (inputPrefix input).length ≤ S) :
    InputCellsMachine.streamTokens (InputCellsMachine.prefixTruth V) (inputPrefix input) =
      cellsInterval V input S 0 (inputPrefix input).length (by omega) := by
  simpa only [cellsInterval, List.flatMap_def, ← List.ofFn_eq_map, Nat.zero_add] using
    InputCellsMachine.prefixStream_eq_initialCells V input S within

theorem payload_eq_interval (V : NPVerifier) (input : List Bool) (S : Nat)
    (within : (inputPrefix input).length + V.witnessBound.eval input.length ≤ S) :
    PayloadRowsLoop.tokens (PayloadCellsMachine.symbolTable V)
      (V.witnessBound.eval input.length) 0 (V.witnessBound.eval input.length) =
      cellsInterval V input S (inputPrefix input).length (V.witnessBound.eval input.length) within := by
  rw [PayloadRowsLoop.tokens_eq_forTokens, forTokens_eq_ofFn]
  simp only [cellsInterval, List.flatMap_def, ← List.ofFn_eq_map, Nat.zero_add]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  exact PayloadCellsMachine.payloadRowTokens_eq V input S i.val i.isLt (by omega)

theorem cells_eq_streams (V : NPVerifier) (input : List Bool) (S : Nat)
    (within : (inputPrefix input).length + V.witnessBound.eval input.length ≤ S) :
    InputCellsMachine.streamTokens (InputCellsMachine.prefixTruth V) (inputPrefix input) ++
      PayloadRowsLoop.tokens (PayloadCellsMachine.symbolTable V)
        (V.witnessBound.eval input.length) 0 (V.witnessBound.eval input.length) ++
      repeatedRows (blankRow V)
        (S - (inputPrefix input).length - V.witnessBound.eval input.length) =
      InitializationControl.cells V input S := by
  let P := (inputPrefix input).length
  let q := V.witnessBound.eval input.length
  let r := S - P - q
  have hpq : P + q ≤ S := within
  have total : (P + q) + r = S := by dsimp only [r]; omega
  have hpre := prefix_eq_interval V input S (by omega)
  have hpay := payload_eq_interval V input S within
  have hpad := cellsInterval_padding V input S (P + q) r (by omega) (by exact le_rfl)
  rw [hpre, hpay, ← hpad]
  have first := cellsInterval_append V input S 0 P q (by omega)
  have second := cellsInterval_append V input S 0 (P + q) r (by omega)
  simp only [Nat.zero_add] at first second
  rw [← first, ← second]
  simpa only [total] using cellsInterval_full V input S

end BinPackingGames.Foundations.Complexity.CookLevin.CellsTokensAlignment

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_CircuitFinish
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish

open Turing MachineComposition
open MachineCloudPadding

variable {σ : Type}

def program : Label → TM2.Stmt Alphabet Label (State σ)
  | .copyOut => Reduction.MachineTransfer.loopAt .current .scratch id false
      .copyOut (some .copyBack)
  | .copyBack => MachineCopy.forkLoop .scratch .current .gateCount false
      .copyBack (some .cancel)
  | .cancel => cancelLoop
  | .records => Reduction.MachineTransfer.loopAt .reversedRecords .output id false
      .records (some .rootOut)
  | .rootOut => Reduction.MachineTransfer.loopAt .root .scratch id false
      .rootOut (some .rootBack)
  | .rootBack => Reduction.MachineTransfer.loopAt .scratch .output id false
      .rootBack (some .countOut)
  | .countOut => Reduction.MachineTransfer.loopAt .gateCount .scratch id false
      .countOut (some .countBack)
  | .countBack => Reduction.MachineTransfer.loopAt .scratch .output id false
      .countBack (some .currentOut)
  | .currentOut => Reduction.MachineTransfer.loopAt .current .scratch id false
      .currentOut (some .currentBack)
  | .currentBack => Reduction.MachineTransfer.loopAt .scratch .output id false
      .currentBack none

theorem cancelStep_zero (current root reversedRecords output scratch : List Bool)
    (g : Nat) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some .cancel, (ambient, register),
        memory current (encodeWord 0) root reversedRecords output (encodeWord g) scratch⟩ =
      some ⟨some .records, (ambient, none),
        memory current [] root reversedRecords output (encodeWord g) scratch⟩ := by
  change some (TM2.stepAux cancelLoop _ _) = _
  simp [cancelLoop, TM2.stepAux, memory, encodeWord]

theorem cancelStep_succ (current root reversedRecords output scratch : List Bool)
    (f g : Nat) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some .cancel, (ambient, register),
        memory current (encodeWord (f + 1)) root reversedRecords output
          (encodeWord (g + 1)) scratch⟩ =
      some ⟨some .cancel, (ambient, none),
        memory current (encodeWord f) root reversedRecords output (encodeWord g) scratch⟩ := by
  change some (TM2.stepAux cancelLoop _ _) = _
  simp [cancelLoop, TM2.stepAux, memory, encodeWord, List.replicate_succ]

theorem cancelTrace (current root reversedRecords output scratch : List Bool)
    (f g : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[f + 1]
      (some ⟨some .cancel, (ambient, register),
        memory current (encodeWord f) root reversedRecords output
          (encodeWord (f + g)) scratch⟩) =
      some ⟨some .records, (ambient, none),
        memory current [] root reversedRecords output (encodeWord g) scratch⟩ := by
  induction f generalizing register with
  | zero =>
    simpa only [Nat.zero_add, Function.iterate_one, advance_some] using
      cancelStep_zero current root reversedRecords output scratch g ambient register
  | succ f ih =>
    rw [Function.iterate_succ_apply]
    simp only [Nat.succ_add]
    change (advance (TM2.step program))^[f + 1]
      (TM2.step program
        ⟨some .cancel, (ambient, register),
          memory current (encodeWord (f + 1)) root reversedRecords output
            (encodeWord ((f + g) + 1)) scratch⟩) = _
    rw [cancelStep_succ]
    exact ih none

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_CircuitProducer
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerStages

open Turing
open BinPackingGames.Reduction
open CircuitProducerModel

theorem counterStep (base : Tape → List Bool) (hcounter : base .counter = [false]) :
    TM2.step program ⟨some .finalCounter, initialState, base⟩ =
      some ⟨some .clearSelected, initialState, Function.update base .counter []⟩ := by
  simp [TM2.step, TM2.stepAux, program, initialState, hcounter]

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerStages

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerHeaders

open Turing
open BinPackingGames.Foundations.Hastad
open CircuitProducerModel CircuitEmission CircuitProducerStages

theorem parsedTapes_eq (base : Tape → List Bool) (n m output : Nat) (suffix : List Bool)
    (hn : base .header = []) (hm : base .counter = []) (ho : base .selected = []) :
    SourceMachine.afterField .input .selected
      (SourceMachine.afterField .input .counter
        (SourceMachine.afterField .input .header base n
          (encodeWords [m, output] ++ suffix)) m (encodeWord output ++ suffix))
      output suffix = parsedTapes base n m output suffix := by
  funext tape
  cases tape <;>
    simp [SourceMachine.afterField, SourceMachine.fieldTapes, parsedTapes, hn, hm, ho]

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerHeaders

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducer

open Turing
open CircuitProducerModel

theorem producedBits_asInput (C : Circuit) :
    CircuitProducerRuntime.producedBits (asInput C) = formulaBits C.toFormula := by
  rw [formulaBits, C.formulaWords_eq_records]
  simp only [CircuitProducerRuntime.producedBits, CircuitProducerRuntime.outputHeaders,
    asInput, Circuit.records_length, recordsOutput_eq, encodeWords_append]

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducer

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_PostfixBounds
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.PostfixMachine

open Turing PostfixModel Hastad

def resetGoto (label : Label) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => initialState) (.goto fun _ => label)

def tagDecoder : Nat → Fin 6 → TM2.Stmt Alphabet Label State
  | 0, tag => .pop .input (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false) (.halt) (resetGoto (prepare tag)))
  | fuel + 1, tag => .pop .input (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (tagDecoder fuel ⟨min (tag.val + 1) 5, by omega⟩) (resetGoto (prepare tag)))

def program : Label → TM2.Stmt Alphabet Label State
  | .headerStart slot => SourceMachine.fieldStart (headerTape slot) (.headerLoop slot)
  | .headerLoop slot => SourceMachine.fieldLoop .input (headerTape slot) (.headerLoop slot)
      (some (if slot.val = 0 then .headerStart 1 else .guard))
  | .guard => MachineUnaryCounter.guard .remaining .decode .finish
  | .decode => tagDecoder 5 0
  | .readStart tag pass => SourceMachine.fieldStart (readDestination tag pass) (.readLoop tag pass)
  | .readLoop tag pass => SourceMachine.fieldLoop (readSource tag) (readDestination tag pass)
      (.readLoop tag pass) (some (readNext tag pass))
  | .emitTag tag => Reduction.MachineSubstitution.pushWord .reversed (encodeWord (gateTag tag))
      (.goto fun _ => .field tag 0)
  | .field tag slot =>
      if fieldUnused tag slot then
        .push .reversed (fun _ => false) (.goto fun _ => fieldNext tag slot)
      else MachineInitialHeaders.prefixScan (fieldSource tag slot) .scratch .reversed 1
        (.field tag slot) (.restore tag slot)
  | .restore tag slot => Reduction.MachineTransfer.loopAt .scratch (fieldSource tag slot)
      id false (.restore tag slot) (some (.closeField tag slot))
  | .closeField tag slot => .push .reversed (fun _ => false) (.goto fun _ => fieldNext tag slot)
  | .rootDrain => Reduction.MachineTransfer.loopAt .current .scratch id false
      .rootDrain (some .rootFork)
  | .rootFork => MachineCopy.forkLoop .scratch .current .roots false .rootFork (some .increment)
  | .increment => .push .current (fun _ => true) (.goto fun _ => .clearLeft)
  | .clearLeft => MachineDrain.drain .left .clearLeft (some .clearRight)
  | .clearRight => MachineDrain.drain .right .clearRight (some .guard)
  | .finish => .pop .remaining (fun _ _ => initialState) (.goto fun _ => .finalReverse)
  | .finalReverse => Reduction.MachineTransfer.loopAt .reversed .output id false .finalReverse none

def machine : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .headerStart 0
  σ := State
  initialState := initialState
  m := program

abbrev advance := MachineComposition.advance (TM2.step program)

theorem decodeTrace (tag : Fin 6) (base : Tape → List Bool) (suffix : List Bool)
    (hinput : base .input = encodeWord tag.val ++ suffix) :
    advance^[1] (some ⟨some .decode, initialState, base⟩) =
      some ⟨some (prepare tag), initialState, Function.update base .input suffix⟩ := by
  change some (TM2.stepAux (program .decode) initialState base) = _
  fin_cases tag <;>
    simp [program, tagDecoder, TM2.stepAux, hinput, encodeWord, resetGoto, initialState]

theorem emitTagTrace (tag : Fin 6) (base : Tape → List Bool) :
    advance^[1] (some ⟨some (.emitTag tag), initialState, base⟩) =
      some ⟨some (.field tag 0), initialState,
        outputTapes base (encodeWord (gateTag tag)).reverse⟩ :=
  MachineInitialHeaders.literalTrace .reversed (encodeWord (gateTag tag))
    (.emitTag tag) (some (.field tag 0)) program rfl base () none

theorem fieldTrace (tag : Fin 6) (slot : Fin 3) (base : Tape → List Bool)
    (value : Nat) (ready : FieldReady tag slot base value) (hscratch : base .scratch = []) :
    advance^[fieldSteps tag slot value]
      (some ⟨some (.field tag slot), initialState, base⟩) =
      some ⟨some (fieldNext tag slot), initialState,
        outputTapes base (encodeWord value).reverse⟩ := by
  cases hu : fieldUnused tag slot with
  | true =>
      have hz := ready.1 hu
      subst value
      simp only [fieldSteps, hu, ↓reduceIte]
      change some (TM2.stepAux (program (.field tag slot)) initialState base) = _
      simp only [program, hu, ↓reduceIte, TM2.stepAux, encodeWord, List.replicate_zero,
        List.nil_append, List.reverse_singleton, outputTapes, List.singleton_append]
  | false =>
      have hcopy := (MachineInitialHeaders.prefixInTime (fieldSource tag slot) .scratch .reversed
        (fieldSource_ne_scratch tag slot) (fieldSource_ne_reversed tag slot) (by decide)
        1 (.field tag slot) (.restore tag slot) (some (.closeField tag slot)) program
        (by simp only [program, hu, Bool.false_eq_true, ↓reduceIte]) rfl base value []
        (by simpa using ready.2 hu) hscratch () none).evals_in_steps
      let copied := outputTapes base (List.replicate value true)
      change advance^[2 * value + 2]
        (some ⟨some (.field tag slot), initialState, base⟩) =
        some ⟨some (.closeField tag slot), initialState,
          outputTapes base (List.replicate (1 * value) true)⟩ at hcopy
      simp only [Nat.one_mul] at hcopy
      have hclose : advance^[1]
          (some ⟨some (.closeField tag slot), initialState, copied⟩) =
          some ⟨some (fieldNext tag slot), initialState, outputTapes copied [false]⟩ := by
        change some (TM2.stepAux (program (.closeField tag slot)) initialState copied) = _
        rfl
      have total := trace_trans _ hcopy hclose
      simpa only [fieldSteps, hu, Bool.false_eq_true, ↓reduceIte, copied, outputTapes_twice,
        encodeWord, List.reverse_append, List.reverse_singleton, List.reverse_replicate,
        show 2 * value + 2 + 1 = 2 * value + 3 by omega] using total

theorem rootPushTrace (base : Tape → List Bool) (current : Nat)
    (hcurrent : base .current = encodeWord current) (hscratch : base .scratch = []) :
    advance^[2 * current + 4]
      (some ⟨some .rootDrain, initialState, base⟩) =
      some ⟨some .increment, initialState,
        Function.update base .roots (encodeWord current ++ base .roots)⟩ := by
  have h := MachineCopy.copyTrace Tape.current Tape.roots Tape.scratch
    (by decide) (by decide) (by decide) false .rootDrain .rootFork (some .increment)
    program rfl rfl base hscratch () none
  simpa only [hcurrent, encodeWord_length, advance, initialState,
    show 2 * (current + 1 + 1) = 2 * current + 4 by omega] using h

theorem incrementTrace (base : Tape → List Bool) (current : Nat)
    (hcurrent : base .current = encodeWord current) :
    advance^[1] (some ⟨some .increment, initialState, base⟩) =
      some ⟨some .clearLeft, initialState,
        Function.update base .current (encodeWord (current + 1))⟩ := by
  change some (TM2.stepAux (program .increment) initialState base) = _
  simp only [program, TM2.stepAux, hcurrent, encodeWord, List.replicate_succ,
    List.cons_append]

theorem recordTrace (tag : Fin 6) (base : Tape → List Bool) (values : Fin 3 → Nat)
    (ready : ∀ slot, FieldReady tag slot base (values slot)) (hscratch : base .scratch = []) :
    advance^[recordSteps tag values]
      (some ⟨some (.emitTag tag), initialState, base⟩) =
      some ⟨some .rootDrain, initialState,
        outputTapes base (encodeWords [gateTag tag, values 0, values 1, values 2]).reverse⟩ := by
  let first := outputTapes base (encodeWord (gateTag tag)).reverse
  let second := outputTapes first (encodeWord (values 0)).reverse
  let third := outputTapes second (encodeWord (values 1)).reverse
  have readyFirst : ∀ slot, FieldReady tag slot first (values slot) :=
    fun slot => FieldReady.output tag slot base (values slot) (ready slot)
      (encodeWord (gateTag tag)).reverse
  have readySecond : ∀ slot, FieldReady tag slot second (values slot) :=
    fun slot => FieldReady.output tag slot first (values slot) (readyFirst slot)
      (encodeWord (values 0)).reverse
  have readyThird : ∀ slot, FieldReady tag slot third (values slot) :=
    fun slot => FieldReady.output tag slot second (values slot) (readySecond slot)
      (encodeWord (values 1)).reverse
  have ht := emitTagTrace tag base
  have h0 := fieldTrace tag 0 first (values 0) (readyFirst 0)
    (by simpa [first, outputTapes] using hscratch)
  have h1 := fieldTrace tag 1 second (values 1) (readySecond 1)
    (by simpa [second, first, outputTapes] using hscratch)
  have h2 := fieldTrace tag 2 third (values 2) (readyThird 2)
    (by simpa [third, second, first, outputTapes] using hscratch)
  change advance^[fieldSteps tag 0 (values 0)]
    (some ⟨some (.field tag 0), initialState, first⟩) =
    some ⟨some (.field tag 1), initialState, second⟩ at h0
  change advance^[fieldSteps tag 1 (values 1)]
    (some ⟨some (.field tag 1), initialState, second⟩) =
    some ⟨some (.field tag 2), initialState, third⟩ at h1
  change advance^[fieldSteps tag 2 (values 2)]
    (some ⟨some (.field tag 2), initialState, third⟩) =
    some ⟨some .rootDrain, initialState,
      outputTapes third (encodeWord (values 2)).reverse⟩ at h2
  have total := trace_trans _ (trace_trans _ (trace_trans _ ht h0) h1) h2
  simpa only [recordSteps, third, second, first, outputTapes_twice, encodeWords,
    List.append_nil, List.reverse_append, List.append_assoc] using total

def tokenSteps (current : Nat) (token : Token) (gate : Gate) : Nat :=
  1 + operandSteps token gate + recordSteps token.tag (gateRecord current gate).slot +
    (2 * current + (operandFields token gate).1.length +
      (operandFields token gate).2.length + 7)

def tokensSteps (current : Nat) (roots : List Nat) : List Token → Nat
  | [] => 0
  | token :: tokens => match token.takeGate roots with
      | none => 0
      | some (gate, rest) =>
          1 + tokenSteps current token gate + tokensSteps (current + 1) (current :: rest) tokens

theorem token_bits (token : Token) : token.bits = encodeWord token.tag.val ++ argumentBits token := by
  cases token with
  | const value => cases value <;> simp [Token.bits, Token.words, Token.tag, argumentBits, encodeWords]
  | not | and | or | input _ => simp [Token.bits, Token.words, Token.tag, argumentBits, encodeWords]

theorem preparedReady (base : Tape → List Bool) (current : Nat) (token : Token)
    (roots rest : List Nat) (gate : Gate) (suffix : List Bool)
    (htake : token.takeGate roots = some (gate, rest)) :
    gateTag token.tag = (gateRecord current gate).tag.val ∧
      ∀ slot, FieldReady token.tag slot
        (preparedTapes base current rest suffix
          (operandFields token gate).1 (operandFields token gate).2)
        ((gateRecord current gate).slot slot) := by
  cases token with
  | const value =>
      simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
      rcases htake with ⟨rfl, rfl⟩
      cases value <;> refine ⟨rfl, ?_⟩ <;> intro slot <;> fin_cases slot <;>
        simp [FieldReady, Token.tag, fieldUnused, fieldSource, preparedTapes, operandFields,
          gateRecord, CircuitProducerModel.Record.slot]
  | input wire =>
      simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
      rcases htake with ⟨rfl, rfl⟩
      refine ⟨rfl, ?_⟩
      intro slot
      fin_cases slot <;> simp [FieldReady, Token.tag, fieldUnused, fieldSource, preparedTapes,
        operandFields, gateRecord, CircuitProducerModel.Record.slot]
  | not =>
      cases roots with
      | nil => simp [Token.takeGate] at htake
      | cons arg roots =>
          simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
          rcases htake with ⟨rfl, rfl⟩
          refine ⟨rfl, ?_⟩
          intro slot
          fin_cases slot <;> simp [FieldReady, Token.tag, fieldUnused, fieldSource, preparedTapes,
            operandFields, gateRecord, CircuitProducerModel.Record.slot]
  | and =>
      cases roots with
      | nil => simp [Token.takeGate] at htake
      | cons right roots =>
          cases roots with
          | nil => simp [Token.takeGate] at htake
          | cons left roots =>
              simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
              rcases htake with ⟨rfl, rfl⟩
              refine ⟨rfl, ?_⟩
              intro slot
              fin_cases slot <;> simp [FieldReady, Token.tag, fieldUnused, fieldSource, preparedTapes,
                operandFields, gateRecord, CircuitProducerModel.Record.slot]
  | or =>
      cases roots with
      | nil => simp [Token.takeGate] at htake
      | cons right roots =>
          cases roots with
          | nil => simp [Token.takeGate] at htake
          | cons left roots =>
              simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
              rcases htake with ⟨rfl, rfl⟩
              refine ⟨rfl, ?_⟩
              intro slot
              fin_cases slot <;> simp [FieldReady, Token.tag, fieldUnused, fieldSource, preparedTapes,
                operandFields, gateRecord, CircuitProducerModel.Record.slot]

theorem tokenBits_cons (token : Token) (tokens : List Token) :
    tokenBits (token :: tokens) = token.bits ++ tokenBits tokens := by
  simp [tokenBits, tokenWords, Token.bits]

theorem guardPositiveTrace (base : Tape → List Bool) (count : Nat)
    (hcount : base .remaining = encodeWord (count + 1)) :
    advance^[1] (some ⟨some .guard, initialState, base⟩) =
      some ⟨some .decode, initialState, Function.update base .remaining (encodeWord count)⟩ := by
  change some (TM2.stepAux (program .guard) initialState base) = _
  simp [program, MachineUnaryCounter.guard, TM2.stepAux, hcount, encodeWord,
    List.replicate_succ, initialState]

theorem reverseTrace (base : Tape → List Bool) (bits : List Bool)
    (hzero : base .remaining = encodeWord 0) (hbits : base .reversed = bits.reverse) :
    advance^[bits.length + 3] (some ⟨some .guard, initialState, base⟩) =
      some ⟨none, initialState, reversedTapes base bits⟩ := by
  have hguard : advance^[1] (some ⟨some .guard, initialState, base⟩) =
      some ⟨some .finish, initialState, base⟩ := by
    change some (TM2.stepAux (program .guard) initialState base) = _
    simp [program, MachineUnaryCounter.guard, TM2.stepAux, hzero, encodeWord, initialState]
  let cleared := Function.update base .remaining []
  have hclear : advance^[1] (some ⟨some .finish, initialState, base⟩) =
      some ⟨some .finalReverse, initialState, cleared⟩ := by
    change some (TM2.stepAux (program .finish) initialState base) = _
    simp [program, TM2.stepAux, hzero, encodeWord, cleared, initialState]
  have htransfer := (Reduction.MachineTransfer.transferAtInTime
    Tape.reversed Tape.output (by decide) id false .finalReverse none program rfl
    cleared () none).evals_in_steps
  change advance^[(cleared .reversed).length + 1]
    (some ⟨some .finalReverse, initialState, cleared⟩) =
    some ⟨none, initialState,
      Reduction.MachineTransfer.tapesAt .reversed .output cleared []
        ((cleared .reversed).reverse.map id ++ cleared .output)⟩ at htransfer
  have hlength : (cleared .reversed).length = bits.length := by
    simp [cleared, hbits]
  have frame : Reduction.MachineTransfer.tapesAt Tape.reversed Tape.output cleared []
      ((cleared .reversed).reverse.map id ++ cleared .output) = reversedTapes base bits := by
    simp [Reduction.MachineTransfer.tapesAt, cleared, reversedTapes, hbits]
  rw [hlength, frame] at htransfer
  have total := trace_trans _ (trace_trans _ hguard hclear) htransfer
  simpa only [show 1 + 1 + (bits.length + 1) = bits.length + 3 by omega] using total

end BinPackingGames.Foundations.Complexity.CookLevin.PostfixMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.PostfixBounds

open StatementCircuit CircuitBatch PostfixModel PostfixMachine PostfixAlignment
open CircuitProducerModel

theorem tokenSteps_le (current R : Nat) (token : Token) (gate : Gate)
    (hq : current ≤ R) (ht : TokenBounded R token) (hg : gate.Bounded (R + 1)) :
    tokenSteps current token gate ≤ 12 * R + 24 := by
  have ho := operandSteps_le token gate R ht hg
  have hf := operandFields_length_le token gate R ht hg
  have hr := recordSteps_le token.tag (gateRecord current gate).slot R
    (gateRecord_slot_le current R gate hq hg)
  unfold tokenSteps
  omega

theorem tokensSteps_le (tokens : List Token) (current : Nat) (roots : List Nat) (R : Nat)
    (hq : current + tokens.length ≤ R) (hr : RootsBounded R roots)
    (ht : ∀ token ∈ tokens, TokenBounded R token) :
    tokensSteps current roots tokens ≤ tokens.length * (12 * R + 25) := by
  induction tokens generalizing current roots with
  | nil => simp [tokensSteps]
  | cons token tokens ih =>
    cases htake : token.takeGate roots with
    | none => simp [tokensSteps, htake]
    | some pair =>
      rcases pair with ⟨gate, rest⟩
      have hc : current ≤ R := by simp only [List.length_cons] at hq; omega
      have hb := takeGate_bounds token roots gate rest R (ht token (by simp)) hr htake
      have hs := tokenSteps_le current R token gate hc (ht token (by simp)) hb.1
      have hroots : RootsBounded R (current :: rest) := by
        intro r h
        rcases List.mem_cons.mp h with rfl | h
        · exact hc
        · exact hb.2 r h
      have hi := ih (current + 1) (current :: rest) (by
        simp only [List.length_cons] at hq
        omega) hroots (fun t h => ht t (by simp [h]))
      simp only [tokensSteps, htake, List.length_cons]
      calc
        _ ≤ (1 + (12 * R + 24)) + tokens.length * (12 * R + 25) :=
          Nat.add_le_add (Nat.add_le_add_left hs 1) hi
        _ = _ := by ring

theorem forest_tokensSteps_le {ι : Type*} (wire : ι → Nat) (es : List (Expr ι))
    (start : Nat) (roots : List Nat) (hw : ∀ i, wire i < start)
    (hr : RootsBounded (start + Batch.cost es) roots) :
    tokensSteps start roots (forestTokens wire es) ≤
      Batch.cost es * (12 * (start + Batch.cost es) + 25) := by
  have h := tokensSteps_le (forestTokens wire es) start roots (start + Batch.cost es)
    (by simpa only [forestTokens_length] using Nat.le_refl (start + Batch.cost es)) hr
    (forestTokens_bounded wire es _ (fun i => by have := hw i; omega))
  simpa only [forestTokens_length] using h

theorem forest_recordsBits_length_le {ι : Type*} (wire : ι → Nat) (es : List (Expr ι))
    (start : Nat) (hw : ∀ i, wire i < start) :
    (recordsBits (gateRecords start (Batch.gates wire start es))).length ≤
      4 * Batch.cost es * (start + Batch.cost es + 5) := by
  have h := encodeWords_length_le
    (recordsWords (gateRecords start (Batch.gates wire start es)))
    (start + (Batch.gates wire start es).length + 4)
    (gateRecords_fields_le start _ (Batch.gates_ordered wire start es hw))
  simpa only [recordsBits, recordsWords_length, gateRecords_length, Batch.gates_length,
    Nat.add_assoc] using h

end BinPackingGames.Foundations.Complexity.CookLevin.PostfixBounds

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ForestStage
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.ForestStage

open Turing MachineComposition StatementCircuit CircuitBatch CircuitProducerModel
open PostfixModel PostfixAlignment

def initialLocal (start : Nat) (tokens : List Token)
    (oldRecords oldRoots : List Bool) : Tape → List Bool
  | .lower .current => encodeWord start
  | .lower .remaining => encodeWord tokens.length
  | .tokens => (tokenBits tokens).reverse
  | .records => oldRecords
  | .rootTable => oldRoots
  | _ => []

def coreBase (tokens : List Token) : PostfixMachine.Tape → List Bool
  | .remaining => encodeWord tokens.length
  | _ => []

def coreInitial (start : Nat) (tokens : List Token) : PostfixMachine.Tape → List Bool :=
  PostfixMachine.boundaryTapes (coreBase tokens) start [] (tokenBits tokens)

def framedStatement {σ : Type}
    (stmt : TM2.Stmt PostfixMachine.Alphabet PostfixMachine.Label PostfixMachine.State) :
    TM2.Stmt PostfixMachine.Alphabet PostfixMachine.Label (State σ) :=
  MachineControl.statement id (stateEquiv σ) (MachineStateFrame.frameStatement stmt)

def framedProgram {σ : Type} :
    PostfixMachine.Label → TM2.Stmt PostfixMachine.Alphabet PostfixMachine.Label (State σ) :=
  fun label => framedStatement (PostfixMachine.program label)

def framedCfg {σ : Type} (ambient : σ × Bool) (cfg : PostfixMachine.machine.Cfg) :
    TM2.Cfg PostfixMachine.Alphabet PostfixMachine.Label (State σ) :=
  MachineControl.configuration id (stateEquiv σ)
    (MachineStateFrame.frameConfiguration ambient cfg)

theorem framed_step {σ : Type} (ambient : σ × Bool)
    (a b : PostfixMachine.machine.Cfg) (h : PostfixMachine.machine.step a = some b) :
    TM2.step framedProgram (framedCfg ambient a) = some (framedCfg ambient b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => simp [FinTM2.step, TM2.step] at h
    | some label =>
      have hb : TM2.stepAux (PostfixMachine.program label) state tapes = b := Option.some.inj h
      rw [← hb]
      change some (TM2.stepAux
        (MachineControl.statement id (stateEquiv σ)
          (MachineStateFrame.frameStatement (PostfixMachine.program label)))
        (stateEquiv σ (state, ambient)) tapes) = _
      erw [MachineControl.stepAux_simulation, MachineStateFrame.frame_stepAux]
      rfl

def steps (tokens : List Token) (start : Nat) (roots : List Nat) (gates : List Gate)
    (oldRoots : List Bool) : Nat :=
  (tokenBits tokens).length + PostfixMachine.tokensSteps start [] tokens +
    2 * (recordsBits (gateRecords start gates)).length + oldRoots.length +
    RootRefresh.steps roots + 7

theorem forest_rootsBits_length_le {ι : Type*}
    (es : List (Expr ι)) (start : Nat) :
    (encodeWords (Batch.roots start es).reverse).length ≤
      Batch.cost es * (start + Batch.cost es + 1) := by
  have h := encodeWords_length_le (Batch.roots start es).reverse
    (start + Batch.cost es) (by
      intro r hr
      exact (Batch.roots_bounds start es r (List.mem_reverse.mp hr)).2.le)
  have h' : (encodeWords (Batch.roots start es).reverse).length ≤
      es.length * (start + Batch.cost es + 1) := by
    simpa only [List.length_reverse, Batch.roots_length] using h
  exact h'.trans (Nat.mul_le_mul_right _ (forest_length_le_cost es))

theorem forest_rootRefresh_le {ι : Type*} (es : List (Expr ι)) (start : Nat) :
    RootRefresh.steps (Batch.roots start es).reverse ≤
      3 * (Batch.cost es * (start + Batch.cost es + 1)) + 1 :=
  (RootRefresh.steps_le_length _).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 3 (forest_rootsBits_length_le es start)) 1)

theorem forest_steps_le {ι : Type*} (wire : ι → Nat) (es : List (Expr ι))
    (start : Nat) (oldRoots : List Bool) (hw : ∀ i, wire i < start) :
    steps (forestTokens wire es) start (Batch.roots start es).reverse
        (Batch.gates wire start es) oldRoots ≤
      timePolynomial.eval (start + Batch.cost es + (tokenBits (forestTokens wire es)).length +
        oldRoots.length + 1) := by
  simp only [steps, timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  exact forest_cost_quadratic start (Batch.cost es)
    (tokenBits (forestTokens wire es)).length oldRoots.length
    (PostfixMachine.tokensSteps start [] (forestTokens wire es))
    (recordsBits (gateRecords start (Batch.gates wire start es))).length
    (RootRefresh.steps (Batch.roots start es).reverse)
    (PostfixBounds.forest_tokensSteps_le wire es start [] hw (by intro r hr; simp at hr))
    (PostfixBounds.forest_recordsBits_length_le wire es start hw)
    (forest_rootRefresh_le es start)

def program {σ : Type} : Label → TM2.Stmt (Alphabet (K := Tape)) Label (State σ)
  | .reverseTokens => Reduction.MachineTransfer.loopAt .tokens (.lower .input) id false
      .reverseTokens (some (.lower .guard))
  | .lower label => ForestPlacement.statement localLowerPorts Label.lower
      (some .reverseRecords) (framedProgram label)
  | .reverseRecords => Reduction.MachineTransfer.loopAt (.lower .output) .records id false
      .reverseRecords (some .drainRoots)
  | .drainRoots => MachineDrain.drain .rootTable .drainRoots (some .rootGuard)
  | .rootGuard => RootRefresh.guard (.lower .roots) .rootStart (some .finish)
  | .rootStart => Hastad.SourceMachine.fieldStart .rootTable .rootLoop
  | .rootLoop => Hastad.SourceMachine.fieldLoop (.lower .roots) .rootTable .rootLoop
      (some .rootGuard)
  | .finish => .push (.lower .remaining) (fun _ => false)
      (.load (fun state => (state.1, none)) .halt)

def afterRecords (next : Nat) (roots : List Nat) (records oldRoots : List Bool) :
    Tape → List Bool
  | .lower .current => encodeWord next
  | .lower .roots => encodeWords roots
  | .records => records
  | .rootTable => oldRoots
  | _ => []

section Caller

variable {K Λ σ : Type} [DecidableEq K]

def statement (ports : Ports K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  fun label => ForestPlacement.statement ports labels exit (program label)

end Caller

end BinPackingGames.Foundations.Complexity.CookLevin.ForestStage

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_TransitionArena
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerInvariant

open StatementCircuit CircuitBatch PostfixModel PostfixAlignment

variable {inputs oldWidth newWidth width : Nat}

def finalFrame (V : NPVerifier) (input : List Bool) :
    Frame (2 * V.witnessBound.eval input.length + 1) 1 :=
  (VerifierCircuit.timeFrame V input (V.horizon input.length)).step
    (fun _ : Fin 1 => VerifierCircuit.acceptanceExpr V input)

def budgetPolynomial (V : NPVerifier) : Polynomial Nat :=
  WitnessEncoding.freeInputPolynomial V.witnessBound + VerifierCircuit.gatePolynomial V +
    VerifierCircuit.widthPolynomial V + 1

def tapePolynomial (V : NPVerifier) : Polynomial Nat :=
  4 * (budgetPolynomial V + 6)^2

theorem budgetPolynomial_eval (V : NPVerifier) (input : List Bool) :
    (budgetPolynomial V).eval input.length =
      (2 * V.witnessBound.eval input.length + 1) +
      (VerifierCircuit.gatePolynomial V).eval input.length +
      VerifierCircuit.width V input + 1 := by
  simp only [budgetPolynomial, Polynomial.eval_add, Polynomial.eval_one,
    WitnessEncoding.freeInputPolynomial_eval, VerifierCircuit.widthPolynomial_eval]

theorem tapePolynomial_eval (V : NPVerifier) (n : Nat) :
    (tapePolynomial V).eval n = 4 * ((budgetPolynomial V).eval n + 6)^2 := by
  simp [tapePolynomial]

def stageEnvelopePolynomial (V : NPVerifier) : Polynomial Nat :=
  Bounds.capacityPolynomial V.computation.time V.witnessBound
    (Runtime.programPushBound V.computation.tm) + budgetPolynomial V + tapePolynomial V + 1

theorem stageEnvelopePolynomial_eval (V : NPVerifier) (input : List Bool) :
    (stageEnvelopePolynomial V).eval input.length =
      VerifierCircuit.capacity V input.length + (budgetPolynomial V).eval input.length +
      (tapePolynomial V).eval input.length + 1 := by
  simp [stageEnvelopePolynomial, VerifierCircuit.capacity, NPVerifier.horizon, Nat.mul_comm]

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerInvariant

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ProducerFrontStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.CellsMachine

open Turing MachineComposition PostfixModel
open ClashMachine (State clean emitted emitted_append chain)
open PayloadCellsMachine (SymbolSpec)

variable {K Λ σ : Type} [DecidableEq K] {A : Nat}

abbrev frame (p : Ports K) (base : K → List Bool) (m i c : Nat) :=
  PayloadRowsLoop.frame (loopPorts p) base m i c

variable (p : Ports K)
  (labels : Label A ↪ Λ)
  (exit : Option Λ)
  (prefixTable : InputCellsMachine.TruthTable A)
  (payload : Fin A → SymbolSpec)
  (blank : List Token)
  (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))

theorem steps_le (payload : Fin A → SymbolSpec) (inputLength q S : Nat) :
    steps payload inputLength q S ≤
      (2 * (S + 2) + ((A + 4) * inputLength + 3)) + (2 * (q + 2) + 1) +
      (q * (A * (120 * (q + 2) ^ 2 + 1) + 3) + 1) + (S + 1) + (q + 3) := by
  have h := PayloadRowsLoop.steps_le payload q 0 q (by omega)
  unfold steps
  omega

end BinPackingGames.Foundations.Complexity.CookLevin.CellsMachine

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_Completeness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.InitializationStage

open Turing MachineComposition StatementCircuit CircuitBatch PostfixModel PostfixAlignment

abbrev Ports (K : Type) := ForestStage.Ports K

end BinPackingGames.Foundations.Complexity.CookLevin.InitializationStage

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_Initialization
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.AlphabetTable.EmitRows

open Turing
open BinPackingGames.Foundations.Complexity
open Emitter

def rowContext {q : Nat} (input : GenericGraphTables.Table q) (edge : Fin input.darts) : Context q :=
  let old := input.rows[edge]
  (old.relation, decide (old.tail = input.rows[old.reverseIndex].tail))

def rowValues {q : Nat} (input : GenericGraphTables.Table q)
    (edge : Fin input.darts) : Fin 5 → Nat :=
  let old := input.rows[edge]
  Addresses.values input.vertices input.darts edge.val old.tail.val
    input.rows[old.reverseIndex].tail.val

theorem encodeWords_flatMap {α : Type} (items : List α) (words : α → List Nat) :
    encodeWords (items.flatMap words) = items.flatMap (fun item => encodeWords (words item)) := by
  induction items with
  | nil => rfl
  | cons item items ih => simp [encodeWords_append, ih]

end BinPackingGames.Foundations.PCP.AlphabetTable.EmitRows

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RawInitialMachineLoopData
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Hastad.SourceContexts.slotFintype _root_.OAI.BinPackingGames.Foundations.Hastad.SourceContexts.slotInhabited _root_.OAI.BinPackingGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.RawInitialRows

open Target GraphTables RawInitialTables

def rowFor (F : Formula) (d : InitialGraph.Dart F) :
    DartRow (F.variables + F.clauses.length + 1) (6 * F.clauses.length + 1) where
  tail := vertexOrder F (InitialGraph.tail F d)
  reverseIndex := dartOrder F (InitialGraph.reverse F d)
  relation := relationOf (fun a b => InitialGraph.predicate F d (decodedLabel a) (decodedLabel b))

theorem rowList_table (F : Formula) :
    rowList (table F) = (orderedList (dartOrder F)).map (rowFor F) := by
  simp only [rowList, table, ofEnumeratedGraph, ofGraph, graphRows, Vector.toList_ofFn,
    orderedList, List.map_ofFn]
  rfl

theorem rowWords_incidence (F : Formula) (i : Fin F.clauses.length)
    (slot : Slot) (orientation : Bool) :
    rowWords (rowFor F (.inl ((i, slot), orientation))) =
      incidenceWords F.variables i.val (clauseNames (clauseAt F i))
        (clauseSigns (clauseAt F i)) slot orientation := by
  have ht : (rowFor F (.inl ((i, slot), orientation))).tail.val =
      if orientation then nameWord (clauseNames (clauseAt F i)) slot else F.variables + i.val := by
    cases orientation <;> cases slot <;> rfl
  have hr : (rowFor F (.inl ((i, slot), orientation))).reverseIndex.val =
      6 * i.val + 2 * (slotOrder slot).val + (if orientation then 0 else 1) := by
    cases orientation <;> cases slot <;>
      simp [rowFor, InitialGraph.reverse, dartOrder, eventOrder, slotOrder, unitOrder,
        finProdFinEquiv, finSumFinEquiv, finTwoEquiv, Nat.mul_add,
        Nat.mul_comm, Nat.mul_left_comm, Nat.add_comm]
  have hp : (rowFor F (.inl ((i, slot), orientation))).relation =
      relationOf (relationPredicate (clauseSigns (clauseAt F i)) slot orientation) := by
    cases orientation <;> rfl
  unfold rowWords incidenceWords relationWordsFor
  rw [ht, hr, hp]

theorem rowWords_dummy (F : Formula) :
    rowWords (rowFor F (.inr ())) = dummyWords F.variables F.clauses.length := by
  have ht : (rowFor F (.inr ())).tail.val = F.variables + F.clauses.length := rfl
  have hr : (rowFor F (.inr ())).reverseIndex.val = 6 * F.clauses.length := by
    simp [rowFor, InitialGraph.reverse, dartOrder, unitOrder, finSumFinEquiv]
  have hp : (rowFor F (.inr ())).relation = relationOf (fun _ _ => true) := rfl
  have hw : relationWords (relationOf (fun _ _ => true)) = List.replicate 4096 1 := by
    unfold relationWords
    rw [relationOf, Vector.toList_ofFn, List.map_ofFn]
    exact List.ofFn_const 4096 1
  unfold rowWords dummyWords
  rw [ht, hr, hp, hw]

theorem clauseDarts_rowWords (F : Formula) (i : Fin F.clauses.length) :
    (clauseDarts F i).flatMap (fun d => rowWords (rowFor F d)) =
      clauseWords F.variables i.val (clauseNames (clauseAt F i))
        (clauseSigns (clauseAt F i)) := by
  simp [clauseDarts, rowWords_incidence, clauseWords, List.append_assoc]

theorem tableWords_eq (F : Formula) :
    tableWords (table F) =
      [F.variables + F.clauses.length + 1, 6 * F.clauses.length + 1] ++
      (List.finRange F.clauses.length).flatMap (fun i =>
        clauseWords F.variables i.val (clauseNames (clauseAt F i))
          (clauseSigns (clauseAt F i))) ++ dummyWords F.variables F.clauses.length := by
  rw [tableWords, rowList_table, orderedList_dartOrder]
  simp [List.flatMap_map, List.flatMap_append, List.flatMap_assoc, clauseDarts_rowWords,
    rowWords_dummy]

end BinPackingGames.Foundations.PCP.RawInitialRows

namespace BinPackingGames.Foundations.PCP.RawInitialMachineModel

open Turing Complexity Hastad

def drain (tape : Tape) (again next : Label) : TM2.Stmt Alphabet Label State :=
  MachineDrain.drain tape again (some next)

def program : Label → TM2.Stmt Alphabet Label State
  | .headerStart slot => SourceMachine.fieldStart (headerTape slot) (.headerLoop slot)
  | .headerLoop slot => SourceMachine.fieldLoop .input (headerTape slot) (.headerLoop slot)
      (if slot.val = 0 then some (.headerStart 1) else some .scanN)
  | .scanN => MachineInitialHeaders.prefixScan .variables .scratch .reversed 1 .scanN .restoreN
  | .restoreN => Reduction.MachineTransfer.loopAt .scratch .variables id false .restoreN (some .scanM1)
  | .scanM1 => MachineInitialHeaders.prefixScan .counter .scratch .reversed 1 .scanM1 .restoreM1
  | .restoreM1 => Reduction.MachineTransfer.loopAt .scratch .counter id false .restoreM1 (some .closeFirst)
  | .closeFirst => Reduction.MachineSubstitution.pushWord .reversed [true, false]
      (.goto fun _ => .scanM6)
  | .scanM6 => MachineInitialHeaders.prefixScan .counter .scratch .reversed 6 .scanM6 .restoreM6
  | .restoreM6 => Reduction.MachineTransfer.loopAt .scratch .counter id false .restoreM6 (some .closeSecond)
  | .closeSecond => Reduction.MachineSubstitution.pushWord .reversed [true, false]
      (.goto fun _ => .initializeIndex)
  | .initializeIndex => .push .index (fun _ => false) (.goto fun _ => .guard)
  | .guard => MachineUnaryCounter.guard .counter (.fieldStart 0) (.scan .dummyVariables)
  | .fieldStart slot => SourceMachine.fieldStart (.field slot) (.fieldLoop slot)
  | .fieldLoop slot => SourceMachine.fieldLoop .input (.field slot) (.fieldLoop slot)
      (if h : slot.val + 1 < 6 then some (.fieldStart ⟨slot.val + 1, h⟩)
        else some .loadSigns)
  | .loadSigns =>
      .peek (.field 1) (fun state head => ((head.getD false, state.1.2), state.2))
        (.peek (.field 3) (fun state head => ((state.1.1, head.getD false, state.1.2.2), state.2))
          (.peek (.field 5) (fun state head => ((state.1.1, state.1.2.1, head.getD false), state.2))
            (.load (fun state => (state.1, none)) (.goto fun _ => .scan (.tailVariables 0)))))
  | .scan phase => MachineInitialHeaders.prefixScan (copySource phase) .scratch .reversed
      (copyScale phase) (.scan phase) (.restore phase)
  | .restore phase => Reduction.MachineTransfer.loopAt .scratch (copySource phase) id false
      (.restore phase) (some (copyNext phase))
  | .closeTail slot orientation => .push .reversed (fun _ => false)
      (.goto fun _ => .scan (.reverseIndex slot orientation))
  | .closeReverse slot orientation => Reduction.MachineSubstitution.pushWord .reversed
      (encodeWord (2 * slot.val + if orientation then 0 else 1))
        (.goto fun _ => .relation slot orientation)
  | .relation slot orientation => MachineFiniteTable.emit .reversed
      (relationOutput slot orientation)
      stateKeys (.goto fun _ => relationNext slot orientation)
  | .cleanupField slot => drain (.field slot) (.cleanupField slot)
      (if h : slot.val + 1 < 6 then .cleanupField ⟨slot.val + 1, h⟩ else .incrementIndex)
  | .incrementIndex => .push .index (fun _ => true) (.goto fun _ => .guard)
  | .closeDummyTail => .push .reversed (fun _ => false) (.goto fun _ => .scan .dummyReverse)
  | .closeDummyReverse => .push .reversed (fun _ => false) (.goto fun _ => .dummyRelation)
  | .dummyRelation => Reduction.MachineSubstitution.pushWord .reversed
      (encodeWords (GraphTables.relationWords (GraphTables.relationOf (fun _ _ => true))))
        (.goto fun _ => .cleanupFinal 0)
  | .cleanupFinal slot => drain (finalTape slot) (.cleanupFinal slot)
      (if h : slot.val + 1 < 3 then .cleanupFinal ⟨slot.val + 1, h⟩ else .reset)
  | .reset => .load (fun _ => initialState) (.goto fun _ => .finalReverse)
  | .finalReverse => Reduction.MachineTransfer.loopAt .reversed .output id false .finalReverse none

def machine : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .headerStart 0
  σ := State
  initialState := initialState
  m := program

end BinPackingGames.Foundations.PCP.RawInitialMachineModel

namespace BinPackingGames.Foundations.PCP.RawInitialMachineStart

open Turing Complexity Hastad RawInitialMachineModel

theorem initList_eq (bits : List Bool) :
    initList machine bits =
      ⟨some (.headerStart 0), initialState, inputTapes bits⟩ := by
  unfold initList
  congr 1
  funext k
  change Tape at k
  cases k <;> rfl

theorem headersTrace (n m : ℕ) (clauseBits : List Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * n + 4 * m + 8]
      (some ⟨some .scanN, initialState, counterTapes n m clauseBits⟩) =
      some ⟨some .initializeIndex, initialState, headerTapes n m clauseBits⟩ := by
  have h := MachineInitialHeaders.headerTrace .variables .counter .scratch .reversed
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    .scanN .restoreN .scanM1 .restoreM1 .closeFirst .scanM6 .restoreM6 .closeSecond
    (some .initializeIndex) program rfl rfl rfl rfl rfl rfl rfl rfl
    (counterTapes n m clauseBits) n m [] []
    (by simp [counterTapes]) (by simp [counterTapes]) rfl
    (false, false, false) none
  have frame : Function.update (counterTapes n m clauseBits) .reversed
      ((encodeWords [n + m + 1, 6 * m + 1]).reverse ++
        counterTapes n m clauseBits .reversed) = headerTapes n m clauseBits := by
    funext k
    cases k <;> simp [counterTapes, headerTapes]
  rw [frame] at h
  exact h

theorem initializeIndexTrace (n m : ℕ) (clauseBits : List Bool) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .initializeIndex, initialState, headerTapes n m clauseBits⟩) =
      some ⟨some .guard, initialState, startTapes n m clauseBits⟩ := by
  simp only [Function.iterate_one, MachineComposition.advance_some]
  change some (TM2.stepAux (program .initializeIndex) initialState
    (headerTapes n m clauseBits)) = _
  simp only [program, TM2.stepAux]
  congr 2
  funext k
  cases k <;> simp [headerTapes, startTapes]

end BinPackingGames.Foundations.PCP.RawInitialMachineStart

namespace BinPackingGames.Foundations.PCP.RawInitialMachinePhases

open Turing Complexity RawInitialMachineModel

def copyInTime (phase : CopyPhase) (base : Tape → List Bool)
    (n : Nat) (suffix : List Bool)
    (hsource : base (copySource phase) = encodeWord n ++ suffix)
    (hscratch : base .scratch = []) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.scan phase), state, base⟩
      (some ⟨some (copyNext phase), (state.1, none),
        Function.update base .reversed
          (List.replicate (copyScale phase * n) true ++ base .reversed)⟩)
      (2 * n + 2) :=
  MachineInitialHeaders.prefixInTime (copySource phase) Tape.scratch Tape.reversed
    (copySource_ne_scratch phase) (copySource_ne_reversed phase) (by decide)
    (copyScale phase) (.scan phase) (.restore phase) (some (copyNext phase))
    program rfl rfl base n suffix hsource hscratch state.1 state.2

def relationInTime (slot : Fin 3) (orientation : Bool)
    (base : Tape → List Bool) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.relation slot orientation), state, base⟩
      (some ⟨some (relationNext slot orientation), state,
        Function.update base .reversed
          (relationOutput slot orientation state ++ base .reversed)⟩) 1 :=
  MachineFiniteTable.emitInTime (K := Tape) (Λ := Label) (σ := State) (Γ := Alphabet)
    Tape.reversed
    (relationOutput slot orientation)
    stateKeys stateKeys_complete program (.relation slot orientation)
    (relationNext slot orientation) rfl state base

theorem loadSigns_step (base : Tape → List Bool) (a b c : Bool)
    (ha : base (.field 1) = encodeWord (if a then 1 else 0))
    (hb : base (.field 3) = encodeWord (if b then 1 else 0))
    (hc : base (.field 5) = encodeWord (if c then 1 else 0)) (state : State) :
    (TM2.step program) ⟨some .loadSigns, state, base⟩ =
      some ⟨some (.scan (.tailVariables 0)), ((a, b, c), none), base⟩ := by
  change some (TM2.stepAux (program .loadSigns) state base) = _
  simp only [program, TM2.stepAux, ha, hb, hc, bitWord_head, Option.getD_some]

end BinPackingGames.Foundations.PCP.RawInitialMachinePhases

namespace BinPackingGames.Foundations.PCP.RawInitialMachineLoopData

open Target Complexity RawInitialMachineModel

theorem tableWords_decomposition (F : Formula) :
    GraphTables.tableWords (RawInitialTables.table F) =
      [F.variables + F.clauses.length + 1, 6 * F.clauses.length + 1] ++
        clauseOutput F.variables 0 F.clauses ++
          RawInitialRows.dummyWords F.variables F.clauses.length := by
  rw [RawInitialRows.tableWords_eq, clauseOutput_numbered]

end BinPackingGames.Foundations.PCP.RawInitialMachineLoopData

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RawInitialMachineCleanup
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.RawInitialMachineCleanup

open Turing Complexity RawInitialMachineModel RawInitialMachineReadClause

theorem incrementIndexTrace (base : Tape → List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .incrementIndex, state, base⟩) =
      some ⟨some .guard, state, Function.update base .index (true :: base .index)⟩ := by
  rfl

end BinPackingGames.Foundations.PCP.RawInitialMachineCleanup

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RawInitialMachineRows
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Hastad.SourceContexts.slotFintype _root_.OAI.BinPackingGames.Foundations.Hastad.SourceContexts.slotInhabited _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.RawInitialMachineRows

open Turing Complexity RawInitialMachineModel RawInitialMachinePhases

attribute [local irreducible] relationOutput RawInitialRows.relationWordsFor

abbrev advance := MachineComposition.advance (TM2.step program)

theorem copyTrace (phase : CopyPhase) (base : Tape → List Bool)
    (n : ℕ) (hsource : base (copySource phase) = encodeWord n)
    (hscratch : base .scratch = []) (signs : Signs) :
    advance^[2 * n + 2] (some ⟨some (.scan phase), (signs, none), base⟩) =
      some ⟨some (copyNext phase), (signs, none),
        outputTapes base (List.replicate (copyScale phase * n) true)⟩ :=
  (copyInTime phase base n [] (by simpa using hsource) hscratch (signs, none)).evals_in_steps

theorem closeTailTrace (slot : Fin 3) (orientation : Bool)
    (base : Tape → List Bool) (signs : Signs) :
    advance^[1] (some ⟨some (.closeTail slot orientation), (signs, none), base⟩) =
      some ⟨some (.scan (.reverseIndex slot orientation)), (signs, none),
        outputTapes base [false]⟩ := by
  change some (TM2.stepAux (program (.closeTail slot orientation)) (signs, none) base) = _
  rfl

theorem closeReverseTrace (slot : Fin 3) (orientation : Bool)
    (base : Tape → List Bool) (signs : Signs) :
    advance^[1] (some ⟨some (.closeReverse slot orientation), (signs, none), base⟩) =
      some ⟨some (.relation slot orientation), (signs, none),
        outputTapes base (encodeWord (2 * slot.val + if orientation then 0 else 1)).reverse⟩ :=
  MachineInitialHeaders.literalTrace .reversed
    (encodeWord (2 * slot.val + if orientation then 0 else 1))
    (.closeReverse slot orientation) (some (.relation slot orientation))
    program rfl base signs none

theorem rowEndTrace (slot : Fin 3) (orientation : Bool) (base : Tape → List Bool)
    (i : ℕ) (hindex : base .index = encodeWord i) (hscratch : base .scratch = [])
    (signs : Signs) :
    advance^[2 * i + 5] (some ⟨some (.closeTail slot orientation), (signs, none), base⟩) =
      some ⟨some (relationNext slot orientation), (signs, none),
        outputTapes base (rowEndBits slot orientation i signs)⟩ := by
  let first := outputTapes base [false]
  let second := outputTapes first (List.replicate (6 * i) true)
  let third := outputTapes second
    (encodeWord (2 * slot.val + if orientation then 0 else 1)).reverse
  have h1 := closeTailTrace slot orientation base signs
  have h2 := copyTrace (.reverseIndex slot orientation) first i
    (by simpa [first, outputTapes, copySource] using hindex)
    (by simpa [first, outputTapes] using hscratch) signs
  change advance^[2 * i + 2]
    (some ⟨some (.scan (.reverseIndex slot orientation)), (signs, none), first⟩) =
    some ⟨some (.closeReverse slot orientation), (signs, none), second⟩ at h2
  have h3 := closeReverseTrace slot orientation second signs
  have h4 := (relationInTime slot orientation third (signs, none)).evals_in_steps
  change advance^[1] (some ⟨some (.relation slot orientation), (signs, none), third⟩) =
    some ⟨some (relationNext slot orientation), (signs, none),
      outputTapes third (relationOutput slot orientation (signs, none))⟩ at h4
  have total := trace_trans _ (trace_trans _ (trace_trans _ h1 h2) h3) h4
  have hout : outputTapes third (relationOutput slot orientation (signs, none)) =
      outputTapes base (rowEndBits slot orientation i signs) := by
    simp only [third, second, first, outputTapes_twice]
    apply congrArg (outputTapes base)
    rw [reverse_encodeWord_add]
    simp only [rowEndBits, Nat.add_assoc, List.append_assoc]
  rw [hout] at total
  simpa only [show 1 + (2 * i + 2) + 1 + 1 = 2 * i + 5 by omega] using total

theorem falseRowTrace (slot : Fin 3) (base : Tape → List Bool) (n i : ℕ)
    (names : RawInitialRows.Names) (signs : Signs)
    (hvariables : base .variables = encodeWord n) (hindex : base .index = encodeWord i)
    (hscratch : base .scratch = []) :
    advance^[2 * n + 4 * i + 9]
      (some ⟨some (.scan (.tailVariables slot)), (signs, none), base⟩) =
      some ⟨some (.scan (.variableName slot)), (signs, none),
        outputTapes base (encodeWords (RawInitialRows.incidenceWords n i names signs
          (RawInitialTables.slotOrder.symm slot) false)).reverse⟩ := by
  let first := outputTapes base (List.replicate n true)
  let second := outputTapes first (List.replicate i true)
  have h1 := copyTrace (.tailVariables slot) base n hvariables hscratch signs
  have h2 := copyTrace (.tailIndex slot) first i
    (by simpa [first, outputTapes, copySource] using hindex)
    (by simpa [first, outputTapes] using hscratch) signs
  simp only [copyScale, Nat.one_mul, copyNext] at h1 h2
  change advance^[2 * n + 2]
    (some ⟨some (.scan (.tailVariables slot)), (signs, none), base⟩) =
    some ⟨some (.scan (.tailIndex slot)), (signs, none), first⟩ at h1
  change advance^[2 * i + 2]
    (some ⟨some (.scan (.tailIndex slot)), (signs, none), first⟩) =
    some ⟨some (.closeTail slot false), (signs, none), second⟩ at h2
  have h3 := rowEndTrace slot false second i
    (by simpa [second, first, outputTapes] using hindex)
    (by simpa [second, first, outputTapes] using hscratch) signs
  have total := trace_trans _ (trace_trans _ h1 h2) h3
  have hout : outputTapes second (rowEndBits slot false i signs) =
      outputTapes base (encodeWords (RawInitialRows.incidenceWords n i names signs
        (RawInitialTables.slotOrder.symm slot) false)).reverse := by
    simp only [second, first, outputTapes_twice]
    apply congrArg (outputTapes base)
    rw [← List.replicate_add, Nat.add_comm i n, rowEndBits_append]
    simp only [RawInitialRows.incidenceWords, Bool.false_eq_true, ↓reduceIte,
      Equiv.apply_symm_apply]
  rw [hout] at total
  simpa only [relationNext, Bool.false_eq_true, ↓reduceIte,
    show (2 * n + 2) + (2 * i + 2) + (2 * i + 5) = 2 * n + 4 * i + 9 by omega] using total

theorem trueRowTrace (slot : Fin 3) (base : Tape → List Bool) (n i : ℕ)
    (names : RawInitialRows.Names) (signs : Signs)
    (hname : base (.field (nameField slot)) =
      encodeWord (RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot)))
    (hindex : base .index = encodeWord i) (hscratch : base .scratch = []) :
    advance^[2 * RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot) + 2 * i + 7]
      (some ⟨some (.scan (.variableName slot)), (signs, none), base⟩) =
      some ⟨some (relationNext slot true), (signs, none),
        outputTapes base (encodeWords (RawInitialRows.incidenceWords n i names signs
          (RawInitialTables.slotOrder.symm slot) true)).reverse⟩ := by
  let value := RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot)
  let first := outputTapes base (List.replicate value true)
  have h1 := copyTrace (.variableName slot) base value hname hscratch signs
  simp only [copyScale, Nat.one_mul, copyNext] at h1
  change advance^[2 * value + 2]
    (some ⟨some (.scan (.variableName slot)), (signs, none), base⟩) =
    some ⟨some (.closeTail slot true), (signs, none), first⟩ at h1
  have h2 := rowEndTrace slot true first i
    (by simpa [first, outputTapes] using hindex)
    (by simpa [first, outputTapes] using hscratch) signs
  have total := trace_trans _ h1 h2
  have hout : outputTapes first (rowEndBits slot true i signs) =
      outputTapes base (encodeWords (RawInitialRows.incidenceWords n i names signs
        (RawInitialTables.slotOrder.symm slot) true)).reverse := by
    simp only [first, outputTapes_twice, rowEndBits_append, value,
      RawInitialRows.incidenceWords, ↓reduceIte, Equiv.apply_symm_apply]
  rw [hout] at total
  simpa only [value, show (2 * value + 2) + (2 * i + 5) = 2 * value + 2 * i + 7 by omega] using total

theorem pairTrace (slot : Fin 3) (base : Tape → List Bool) (n i : ℕ)
    (names : RawInitialRows.Names) (signs : Signs)
    (hvariables : base .variables = encodeWord n) (hindex : base .index = encodeWord i)
    (hname : base (.field (nameField slot)) =
      encodeWord (RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot)))
    (hscratch : base .scratch = []) :
    advance^[2 * n + 6 * i +
      2 * RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot) + 16]
      (some ⟨some (.scan (.tailVariables slot)), (signs, none), base⟩) =
      some ⟨some (relationNext slot true), (signs, none),
        outputTapes base (encodeWords (pairWords slot n i names signs)).reverse⟩ := by
  let first := outputTapes base (encodeWords (RawInitialRows.incidenceWords n i names signs
    (RawInitialTables.slotOrder.symm slot) false)).reverse
  have h1 := falseRowTrace slot base n i names signs hvariables hindex hscratch
  have h2 := trueRowTrace slot first n i names signs
    (by simpa [first, outputTapes] using hname)
    (by simpa [first, outputTapes] using hindex)
    (by simpa [first, outputTapes] using hscratch)
  have total := trace_trans _ h1 h2
  simpa only [first, outputTapes_twice, pairWords, encodeWords_append, List.reverse_append,
    show (2 * n + 4 * i + 9) +
      (2 * RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot) + 2 * i + 7) =
      2 * n + 6 * i +
        2 * RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot) + 16 by omega]
    using total

theorem rowsTrace (base : Tape → List Bool) (n i : ℕ)
    (names : RawInitialRows.Names) (signs : Signs)
    (hvariables : base .variables = encodeWord n) (hindex : base .index = encodeWord i)
    (hname0 : base (.field 0) = encodeWord names.1)
    (hname2 : base (.field 2) = encodeWord names.2.1)
    (hname4 : base (.field 4) = encodeWord names.2.2)
    (hscratch : base .scratch = []) :
    advance^[6 * n + 18 * i + 2 * (names.1 + names.2.1 + names.2.2) + 48]
      (some ⟨some (.scan (.tailVariables 0)), (signs, none), base⟩) =
      some ⟨some (.cleanupField 0), (signs, none),
        outputTapes base (encodeWords (RawInitialRows.clauseWords n i names signs)).reverse⟩ := by
  let first := outputTapes base (encodeWords (pairWords 0 n i names signs)).reverse
  let second := outputTapes first (encodeWords (pairWords 1 n i names signs)).reverse
  have h0 := pairTrace 0 base n i names signs hvariables hindex hname0 hscratch
  have h1 := pairTrace 1 first n i names signs
    (by simpa [first, outputTapes] using hvariables)
    (by simpa [first, outputTapes] using hindex)
    (by simpa [first, outputTapes, nameField, RawInitialRows.nameWord,
      RawInitialTables.slotOrder] using hname2)
    (by simpa [first, outputTapes] using hscratch)
  have h2 := pairTrace 2 second n i names signs
    (by simpa [second, first, outputTapes] using hvariables)
    (by simpa [second, first, outputTapes] using hindex)
    (by simpa [second, first, outputTapes, nameField, RawInitialRows.nameWord,
      RawInitialTables.slotOrder] using hname4)
    (by simpa [second, first, outputTapes] using hscratch)
  change advance^[2 * n + 6 * i + 2 * names.1 + 16]
    (some ⟨some (.scan (.tailVariables 0)), (signs, none), base⟩) =
    some ⟨some (.scan (.tailVariables 1)), (signs, none), first⟩ at h0
  change advance^[2 * n + 6 * i + 2 * names.2.1 + 16]
    (some ⟨some (.scan (.tailVariables 1)), (signs, none), first⟩) =
    some ⟨some (.scan (.tailVariables 2)), (signs, none), second⟩ at h1
  change advance^[2 * n + 6 * i + 2 * names.2.2 + 16]
    (some ⟨some (.scan (.tailVariables 2)), (signs, none), second⟩) =
    some ⟨some (.cleanupField 0), (signs, none),
      outputTapes second (encodeWords (pairWords 2 n i names signs)).reverse⟩ at h2
  have total := trace_trans _ (trace_trans _ h0 h1) h2
  have hout : outputTapes second (encodeWords (pairWords 2 n i names signs)).reverse =
      outputTapes base (encodeWords (RawInitialRows.clauseWords n i names signs)).reverse := by
    simp only [second, first, outputTapes_twice, RawInitialRows.clauseWords,
      encodeWords_append, List.reverse_append, pairWords, List.append_assoc]
    rfl
  rw [hout] at total
  simpa only [show (2 * n + 6 * i + 2 * names.1 + 16) +
    (2 * n + 6 * i + 2 * names.2.1 + 16) + (2 * n + 6 * i + 2 * names.2.2 + 16) =
      6 * n + 18 * i + 2 * (names.1 + names.2.1 + names.2.2) + 48 by omega] using total

end BinPackingGames.Foundations.PCP.RawInitialMachineRows

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RawInitialMachineBody
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.RawInitialMachineBody

open Turing Target Complexity RawInitialMachineModel RawInitialMachineLoopData
open RawInitialMachineReadClause RawInitialMachineRows RawInitialMachineBudget

theorem guardTrace_succ (n i remaining : Nat) (input reversed : List Bool)
    (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .guard, state, loopTapes n i (remaining + 1) input reversed⟩) =
      some ⟨some (.fieldStart 0), (state.1, none),
        loopTapes n i remaining input reversed⟩ := by
  have h := MachineUnaryCounter.guardTrace_succ Tape.counter Label.guard
    (.fieldStart 0) (.scan .dummyVariables) program rfl
    (loopTapes n i remaining input reversed) remaining [] state.1 state.2
  have heq (r : Nat) : MachineUnaryCounter.counterTapes Tape.counter
      (loopTapes n i remaining input reversed) r [] = loopTapes n i r input reversed := by
    funext tape
    cases tape <;> simp [MachineUnaryCounter.counterTapes, loopTapes]
  simpa only [heq, Prod.mk.eta] using h

theorem guardTrace_zero (n i : Nat) (input reversed : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .guard, state, loopTapes n i 0 input reversed⟩) =
      some ⟨some (.scan .dummyVariables), (state.1, none),
        loopTapes n i 0 input reversed⟩ := by
  have h := MachineUnaryCounter.guardTrace_zero Tape.counter Label.guard
    (.fieldStart 0) (.scan .dummyVariables) program rfl
    (loopTapes n i 0 input reversed) [] state.1 state.2
  have heq : MachineUnaryCounter.counterTapes Tape.counter
      (loopTapes n i 0 input reversed) 0 [] = loopTapes n i 0 input reversed := by
    funext tape
    cases tape <;> simp [MachineUnaryCounter.counterTapes, loopTapes]
  simpa only [heq, Prod.mk.eta] using h

end BinPackingGames.Foundations.PCP.RawInitialMachineBody

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RawInitialMachineFinish
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.RawInitialMachineFinish

open Turing Complexity RawInitialMachineModel RawInitialMachinePhases

theorem trueRelationWords :
    GraphTables.relationWords (GraphTables.relationOf (fun _ _ => true)) =
      List.replicate 4096 1 := by
  unfold GraphTables.relationWords
  rw [GraphTables.relationOf, Vector.toList_ofFn, List.map_ofFn]
  exact List.ofFn_const 4096 1

theorem resetReverseTrace (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[rev.length + 2]
      (some ⟨some .reset, state, tapes [] [] [] rev []⟩) =
      some (haltList machine rev.reverse) := by
  have reset : (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .reset, state, tapes [] [] [] rev []⟩) =
      some ⟨some .finalReverse, initialState, tapes [] [] [] rev []⟩ := rfl
  have transfer := (Reduction.MachineTransfer.transferAtInTime
    .reversed .output (by decide) id false .finalReverse none program rfl
    (tapes [] [] [] rev []) (false, false, false) none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[rev.length + 1]
    (some ⟨some .finalReverse, initialState, tapes [] [] [] rev []⟩) = _ at transfer
  have frame : Reduction.MachineTransfer.tapesAt .reversed .output
      (tapes [] [] [] rev []) [] (rev.reverse.map id ++ []) =
      (haltList machine rev.reverse).stk := by
    funext k
    change Tape at k
    cases k <;> simp [Reduction.MachineTransfer.tapesAt, tapes, haltList, machine]
    rfl
  change (MachineComposition.advance (TM2.step program))^[rev.length + 1]
    (some ⟨some .finalReverse, initialState, tapes [] [] [] rev []⟩) =
    some ⟨none, initialState, Reduction.MachineTransfer.tapesAt .reversed .output
      (tapes [] [] [] rev []) [] (rev.reverse.map id ++ [])⟩ at transfer
  rw [frame] at transfer
  have total := trace_trans _ reset transfer
  rw [show 1 + (rev.length + 1) = rev.length + 2 by omega] at total
  change (MachineComposition.advance (TM2.step program))^[rev.length + 2]
    (some ⟨some .reset, state, tapes [] [] [] rev []⟩) =
    some ⟨none, initialState, (haltList machine rev.reverse).stk⟩
  exact total

theorem copyFinishTrace (n m r : Nat) (rev : List Bool) (phase : CopyPhase)
    (hsource : finishTapes n m rev (copySource phase) = encodeWord r) (state : State) :
    (MachineComposition.advance (TM2.step program))^[2 * r + 2]
      (some ⟨some (.scan phase), state, finishTapes n m rev⟩) =
      some ⟨some (copyNext phase), (state.1, none),
        finishTapes n m (List.replicate (copyScale phase * r) true ++ rev)⟩ := by
  have h := (copyInTime phase (finishTapes n m rev) r []
    (by simpa only [List.append_nil] using hsource) rfl state).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[2 * r + 2]
    (some ⟨some (.scan phase), state, finishTapes n m rev⟩) =
    some ⟨some (copyNext phase), (state.1, none),
      Function.update (finishTapes n m rev) .reversed
        (List.replicate (copyScale phase * r) true ++ rev)⟩ at h
  rw [update_finish] at h
  exact h

theorem closeDummyTailTrace (n m : Nat) (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .closeDummyTail, state, finishTapes n m rev⟩) =
      some ⟨some (.scan .dummyReverse), state, finishTapes n m (false :: rev)⟩ := by
  change some (TM2.stepAux (program .closeDummyTail) state (finishTapes n m rev)) = _
  simp only [program, TM2.stepAux]
  congr 2
  exact update_finish _ _ _ _

theorem closeDummyReverseTrace (n m : Nat) (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .closeDummyReverse, state, finishTapes n m rev⟩) =
      some ⟨some .dummyRelation, state, finishTapes n m (false :: rev)⟩ := by
  change some (TM2.stepAux (program .closeDummyReverse) state (finishTapes n m rev)) = _
  simp only [program, TM2.stepAux]
  congr 2
  exact update_finish _ _ _ _

theorem dummyRelationTrace (n m : Nat) (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .dummyRelation, state, finishTapes n m rev⟩) =
      some ⟨some (.cleanupFinal 0), state,
        finishTapes n m ((encodeWords (List.replicate 4096 1)).reverse ++ rev)⟩ := by
  change some (TM2.stepAux (program .dummyRelation) state (finishTapes n m rev)) = _
  rw [program, Reduction.MachineSubstitution.stepAux_pushWord, trueRelationWords]
  simp only [TM2.stepAux]
  congr 2
  exact update_finish _ _ _ _

theorem dummyTrace (n m : Nat) (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[2 * n + 4 * m + 9]
      (some ⟨some (.scan .dummyVariables), state, finishTapes n m rev⟩) =
      some ⟨some (.cleanupFinal 0), (state.1, none),
        finishTapes n m ((encodeWords (RawInitialRows.dummyWords n m)).reverse ++ rev)⟩ := by
  let a := List.replicate n true ++ rev
  let b := List.replicate m true ++ a
  let c := false :: b
  let d := List.replicate (6 * m) true ++ c
  let e := false :: d
  have h0 := copyFinishTrace n m n rev .dummyVariables rfl state
  simp only [copyScale, copyNext, Nat.one_mul] at h0
  have h1 := copyFinishTrace n m m a .dummyIndex rfl (state.1, none)
  simp only [copyScale, copyNext, Nat.one_mul] at h1
  have h2 := closeDummyTailTrace n m b (state.1, none)
  have h3 := copyFinishTrace n m m c .dummyReverse rfl (state.1, none)
  simp only [copyScale, copyNext] at h3
  have h4 := closeDummyReverseTrace n m d (state.1, none)
  have h5 := dummyRelationTrace n m e (state.1, none)
  have total := trace_trans _ (trace_trans _ (trace_trans _
    (trace_trans _ (trace_trans _ h0 h1) h2) h3) h4) h5
  have output : (encodeWords (List.replicate 4096 1)).reverse ++ e =
      (encodeWords (RawInitialRows.dummyWords n m)).reverse ++ rev := by
    have rep : List.replicate m true ++ (List.replicate n true ++ rev) =
        List.replicate (n + m) true ++ rev := by
      rw [← List.append_assoc, ← List.replicate_add, Nat.add_comm m n]
    simp only [RawInitialRows.dummyWords, encodeWords_append, encodeWords,
      List.append_nil, List.reverse_append,
      encodeWord, List.reverse_cons,
      List.reverse_replicate, List.append_assoc, List.singleton_append,
      a, b, c, d, e]
    rw [rep]
    simp only [List.reverse_nil, List.nil_append, List.cons_append]
  rw [output] at total
  simpa only [show (((((2 * n + 2) + (2 * m + 2)) + 1) + (2 * m + 2)) + 1) + 1 =
    2 * n + 4 * m + 9 by omega] using total

end BinPackingGames.Foundations.PCP.RawInitialMachineFinish

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_MachineRawInitialTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.MachineRawInitialTable

open Turing Target Complexity RawInitialMachineModel RawInitialMachineLoopData
open RawInitialMachineBudget RawInitialMachineLoop

theorem outputBits (F : Formula) :
    GraphTables.tableBits (RawInitialTables.table F) = prefixBits F ++
      encodeWords (RawInitialRows.dummyWords F.variables F.clauses.length) := by
  change encodeWords (GraphTables.tableWords (RawInitialTables.table F)) = _
  rw [tableWords_decomposition, encodeWords_append]
  rfl

end BinPackingGames.Foundations.PCP.MachineRawInitialTable

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

noncomputable def prefixPolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C 27 * Polynomial.X + Polynomial.C 54 +
    Polynomial.X *
      (Polynomial.C (32 + 8 * (Enumeration.localCount q * (6 * (2 * 4104)))) *
        (Polynomial.X + Polynomial.C 1)) + Polynomial.C 1

end BinPackingGames.Foundations.PCP.AlphabetTable.Runtime

end

end OAI
end


