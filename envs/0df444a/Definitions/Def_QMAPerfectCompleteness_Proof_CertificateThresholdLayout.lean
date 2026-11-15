-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CertificateThresholdLayout
-- name    : QMAPerfectCompleteness_Proof_CertificateThresholdLayout
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:10:58.288022+00:00
-- url     : https://prove2.me/theorems/9e7862bf-0202-4d21-bb00-6da73b94f879
-- title:
--   Physical placement of certificate arithmetic slots
-- statement:
--   Maps the general threshold-preparation slots to the actual certificate bits, six padded work words, carry bank and temporary bit of the master layout. Injectivity certifies that the selected sources and arithmetic workspace are genuinely distinct and supplies the placement used by the concrete adders.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CertificateThresholdLayout.lean, lines 8–68.

/- Generated from Solutions.CertificateThresholdLayout by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanFraming
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMixture
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateVerifierLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentCertificate
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_Dyadic
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_PointwiseSetup
import Definitions.Def_QMAPerfectCompleteness_Proof_RegisterCopies
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdPreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableAddition
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableComparison
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableHistoryEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierAnalysis

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.Certificate
end QMAPerfectCompleteness.Main.Certificate
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof



/-! The actual master-layout placement of the coherent binary threshold preparation. -/
namespace QMAPerfectCompleteness.Main.CertificateMasterLayout
open ThresholdPreparation

lemma bank_disjoint (V : Verifier gatesG2) (a l b m : ℕ)
    (ha : a+l≤work V) (hb : b+m≤work V) (hab : a+l≤b) (i : Fin l) (j : Fin m) :
    bank V a l ha i ≠ bank V b m hb j := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  have hj := j.isLt
  simp only [bank_val] at hv
  omega

lemma certAB_ne_bank (V : Verifier gatesG2) (a l : ℕ) (ha : a+l≤work V)
    (i : Fin (2*k V)) (j : Fin l) : certAB V i ≠ bank V a l ha j := by
  intro h
  have hv := congrArg Fin.val h
  have hj := j.isLt
  simp only [certAB_val,bank_val] at hv
  omega

def thresholdWireFun (V : Verifier gatesG2) : Slot (k V) → Fin (total V)
  | .certificate s j => certificate V s j
  | .word d j => prepWord V d j
  | .carry j => prepCarry V j
  | .temp => prepTemp V

/-- All arithmetic sources and workspace occupy genuinely distinct physical wires. -/
def thresholdWire (V : Verifier gatesG2) : Slot (k V) ↪ Fin (total V) :=
  ⟨thresholdWireFun V,by
    intro s t h
    cases s with
    | certificate a i =>
      cases t with
      | certificate b j =>
        have hp := (certAB V).injective h
        have he := finProdFinEquiv.injective hp
        cases he
        rfl
      | word d j => exact (certAB_ne_bank V _ _ _ _ _ h).elim
      | carry j => exact (certAB_ne_bank V _ _ _ _ _ h).elim
      | temp => exact (certAB_ne_bank V _ _ _ _ _ h).elim
    | word d i =>
      cases t with
      | certificate a j => exact (certAB_ne_bank V _ _ _ _ _ h.symm).elim
      | word e j =>
        have hp := (prepWordBank V).injective h
        have he := finProdFinEquiv.injective hp
        cases he
        rfl
      | carry j => exact (bank_disjoint V _ _ _ _ _ _ (by omega) _ _ h).elim
      | temp => exact (bank_disjoint V _ _ _ _ _ _ (by omega) _ _ h).elim
    | carry i =>
      cases t with
      | certificate a j => exact (certAB_ne_bank V _ _ _ _ _ h.symm).elim
      | word d j => exact (bank_disjoint V _ _ _ _ _ _ (by omega) _ _ h.symm).elim
      | carry j => exact congrArg Slot.carry ((prepCarry V).injective h)
      | temp => exact (bank_disjoint V _ _ _ _ _ _ (by omega) _ _ h).elim
    | temp =>
      cases t with
      | certificate a j => exact (certAB_ne_bank V _ _ _ _ _ h.symm).elim
      | word d j => exact (bank_disjoint V _ _ _ _ _ _ (by omega) _ _ h.symm).elim
      | carry j => exact (bank_disjoint V _ _ _ _ _ _ (by omega) _ _ h.symm).elim
      | temp => rfl⟩






end QMAPerfectCompleteness.Main.CertificateMasterLayout


