-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdLayout
-- name    : QMAPerfectCompleteness_Proof_ThresholdLayout
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:00:11.851622+00:00
-- url     : https://prove2.me/theorems/93afd5bd-8a2e-4f02-a4ad-533aaec2c0c8
-- title:
--   Physical adders for certificate thresholds
-- statement:
--   Constructs the two concrete adder layouts from the disjoint certificate arithmetic slots. The wire identities identify each adder input, carry bank, output and temporary bit with its intended physical register.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/ThresholdLayout.lean, retained declaration span lines 8–85.

/- Generated from Solutions.ThresholdLayout by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanFraming
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_RegisterCopies
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdPreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableAddition



/-! Construct the two concrete adders from the certificate arithmetic slot injection. -/
namespace QMAPerfectCompleteness.Main.ThresholdPreparation
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-- The local adder order is A,B,carry,output,temp. -/
def adderSlot {k : ℕ} (ids : Fin 3 ↪ Fin 6) (i : Fin (4*(k+2)+2)) : Slot k :=
  if h0 : i.val < k+2 then .word (ids 0) ⟨i.val,h0⟩ else
  if h1 : i.val < 2*(k+2) then .word (ids 1) ⟨i.val-(k+2),by omega⟩ else
  if h2 : i.val < 3*(k+2)+1 then .carry ⟨i.val-2*(k+2),by omega⟩ else
  if h3 : i.val < 4*(k+2)+1 then .word (ids 2) ⟨i.val-(3*(k+2)+1),by omega⟩ else .temp

lemma adderSlot_injective {k : ℕ} (ids : Fin 3 ↪ Fin 6) : Function.Injective (adderSlot (k := k) ids) := by
  intro i j h
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  unfold adderSlot at h
  split_ifs at h <;>
    simp_all [Slot.word.injEq,Slot.carry.injEq,ids.injective.eq_iff,Fin.mk.injEq] <;> omega

def adder {k n : ℕ} (wire : Slot k ↪ Fin n) (ids : Fin 3 ↪ Fin 6) :
    VariableAddition.Layout (k+2) n :=
  ⟨(⟨adderSlot ids,adderSlot_injective ids⟩ : Fin (4*(k+2)+2) ↪ Slot k).trans wire⟩

lemma adder_left {k n : ℕ} (wire : Slot k ↪ Fin n) (ids : Fin 3 ↪ Fin 6) (j : Fin (k+2)) :
    (adder wire ids).left j = wire (.word (ids 0) j) := by
  change wire (adderSlot ids ⟨j.val,by omega⟩) = _
  simp [adderSlot,j.isLt]

lemma adder_right {k n : ℕ} (wire : Slot k ↪ Fin n) (ids : Fin 3 ↪ Fin 6) (j : Fin (k+2)) :
    (adder wire ids).right j = wire (.word (ids 1) j) := by
  have hj := j.isLt
  change wire (adderSlot ids ⟨k+2+j.val,by omega⟩) = _
  have h0 : ¬ k+2+j.val < k+2 := by omega
  have h1 : k+2+j.val < 2*(k+2) := by omega
  simp [adderSlot,h0,h1]

lemma adder_carry {k n : ℕ} (wire : Slot k ↪ Fin n) (ids : Fin 3 ↪ Fin 6) (j : Fin (k+3)) :
    (adder wire ids).carry j = wire (.carry j) := by
  have hj := j.isLt
  change wire (adderSlot ids ⟨2*(k+2)+j.val,by omega⟩) = _
  have h0 : ¬ 2*(k+2)+j.val < k+2 := by omega
  have h1 : ¬ 2*(k+2)+j.val < 2*(k+2) := by omega
  have h2 : 2*(k+2)+j.val < 3*(k+2)+1 := by omega
  simp [adderSlot,h0,h1,h2]

lemma adder_output {k n : ℕ} (wire : Slot k ↪ Fin n) (ids : Fin 3 ↪ Fin 6) (j : Fin (k+2)) :
    (adder wire ids).output j = wire (.word (ids 2) j) := by
  have hj := j.isLt
  change wire (adderSlot ids ⟨3*(k+2)+1+j.val,by omega⟩) = _
  have h0 : ¬ 3*(k+2)+1+j.val < k+2 := by omega
  have h1 : ¬ 3*(k+2)+1+j.val < 2*(k+2) := by omega
  have h2 : ¬ 3*(k+2)+1+j.val < 3*(k+2)+1 := by omega
  have h3 : 3*(k+2)+1+j.val < 4*(k+2)+1 := by omega
  simp [adderSlot,h0,h1,h2,h3]

lemma adder_temp {k n : ℕ} (wire : Slot k ↪ Fin n) (ids : Fin 3 ↪ Fin 6) :
    (adder wire ids).temp = wire .temp := by
  change wire (adderSlot ids ⟨4*(k+2)+1,by omega⟩) = _
  have h0 : ¬ 4*(k+2)+1 < k+2 := by omega
  have h1 : ¬ 4*(k+2)+1 < 2*(k+2) := by omega
  have h2 : ¬ 4*(k+2)+1 < 3*(k+2)+1 := by omega
  simp [adderSlot,h0,h1,h2]

def threeIds : Fin 3 ↪ Fin 6 := ⟨![0,1,4],by decide⟩
def upperIds : Fin 3 ↪ Fin 6 := ⟨![4,2,5],by decide⟩

/-- No extra layout assumptions are required beyond disjoint physical slots. -/
def ofWire {k n : ℕ} (wire : Slot k ↪ Fin n) : Layout k n where
  wire := wire
  three := adder wire threeIds
  upper := adder wire upperIds
  three_left := adder_left wire threeIds
  three_right := adder_right wire threeIds
  three_output := adder_output wire threeIds
  upper_left := adder_left wire upperIds
  upper_right := adder_right wire upperIds
  upper_output := adder_output wire upperIds
  three_carry := adder_carry wire threeIds
  upper_carry := adder_carry wire upperIds
  three_temp := adder_temp wire threeIds
  upper_temp := adder_temp wire upperIds

end QMAPerfectCompleteness.Main.ThresholdPreparation


