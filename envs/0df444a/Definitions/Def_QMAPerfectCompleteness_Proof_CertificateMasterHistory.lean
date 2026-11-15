-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterHistory
-- name    : QMAPerfectCompleteness_Proof_CertificateMasterHistory
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:09:45.655662+00:00
-- url     : https://prove2.me/theorems/1f3205b3-fb43-4ae1-97ad-dc67ecc36a84
-- title:
--   Variable history equality on the master layout
-- statement:
--   Selects the original proof bits, certificate word $z$, shared borrow storage and clock-test flags inside the master register layout. The resulting history-test layout compares the two proof words and tests the final clock value with disjoint target and scratch wires.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CertificateMasterHistory.lean, lines 9–83.

/- Generated from Solutions.CertificateMasterHistory by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableComparison
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableHistoryEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierAnalysis

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.Certificate
end QMAPerfectCompleteness.Main.Certificate
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof



/-! Variable-z last-clock equality on the actual master register layout. -/
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CertificateMasterLayout
open BlockCircuit BlockCompiler VariableHistoryEquality
variable (V : Verifier gatesG2)

lemma oldWork_ge_fifteen : 15 ≤ oldWork V := by
  change 15 ≤ indexQubits V+clockWires V+V.proofQubits+15
  omega
lemma work_ge_fifteen : 15 ≤ work V := by
  have h := oldWork_ge_fifteen V
  dsimp only [work]
  omega

def historyEquality : Fin (3*V.proofQubits+2) ↪ Fin (total V) :=
  ⟨fun j => ⟨if j.val<V.proofQubits then indexQubits V+clockWires V+j.val else
      if j.val<2*V.proofQubits then bodyWires V+work V+(j.val-V.proofQubits) else
      if j.val<3*V.proofQubits+1 then bodyWires V+11+(j.val-2*V.proofQubits) else bodyWires V+10,by
      have hj := j.isLt
      have hwork : V.proofQubits+15 ≤ work V := by
        have ho : V.proofQubits+15 ≤ oldWork V := by
          change V.proofQubits+15 ≤ indexQubits V+clockWires V+V.proofQubits+15
          omega
        dsimp only [work]
        omega
      dsimp only [total,CertificateCoordinates.claimQubits,bodyWires]
      split_ifs <;> omega⟩,
    by
      intro i j h
      have hv := congrArg Fin.val h
      change (if i.val<V.proofQubits then indexQubits V+clockWires V+i.val else
        if i.val<2*V.proofQubits then bodyWires V+work V+(i.val-V.proofQubits) else
        if i.val<3*V.proofQubits+1 then bodyWires V+11+(i.val-2*V.proofQubits) else bodyWires V+10) =
        (if j.val<V.proofQubits then indexQubits V+clockWires V+j.val else
        if j.val<2*V.proofQubits then bodyWires V+work V+(j.val-V.proofQubits) else
        if j.val<3*V.proofQubits+1 then bodyWires V+11+(j.val-2*V.proofQubits) else bodyWires V+10) at hv
      have hi := i.isLt
      have hj := j.isLt
      have hwork : V.proofQubits+15 ≤ work V := by
        have ho : V.proofQubits+15 ≤ oldWork V := by
          change V.proofQubits+15 ≤ indexQubits V+clockWires V+V.proofQubits+15
          omega
        dsimp only [work]
        omega
      apply Fin.ext
      dsimp only [bodyWires] at hv
      split_ifs at hv <;> omega⟩

def oldTags : Fin 11 ↪ Fin (total V) :=
  (⟨(layoutOf V).tagWire,(layoutOf V).tagWire_injective⟩ : Fin 11 ↪ Fin (layoutOf V).total).trans (oldEmbedding V)

def historyTagChoice : Fin 3 ↪ Fin 11 := ⟨![8,6,7],by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩
def historyTags : Fin 3 ↪ Fin (total V) := historyTagChoice.trans (oldTags V)

lemma oldTags_val (j : Fin 11) : (oldTags V j).val=bodyWires V+j.val := rfl

lemma history_no_small_tag (t : Fin 11) (ht : t.val<10) (j : Fin (3*V.proofQubits+2)) :
    oldTags V t ≠ historyEquality V j := by
  intro h
  have hv := congrArg Fin.val h
  change bodyWires V+t.val = (if j.val<V.proofQubits then indexQubits V+clockWires V+j.val else
    if j.val<2*V.proofQubits then bodyWires V+work V+(j.val-V.proofQubits) else
    if j.val<3*V.proofQubits+1 then bodyWires V+11+(j.val-2*V.proofQubits) else bodyWires V+10) at hv
  have hw := work_ge_fifteen V
  dsimp only [bodyWires] at hv
  split_ifs at hv <;> omega

def historyClock : ControlCircuits.AndLayout (clockWires V) (total V) where
  controls := (layoutOf V).clockLayout.controls.trans (oldEmbedding V)
  flags := (layoutOf V).clockLayout.flags.trans (oldEmbedding V)
  disjoint i j h := (layoutOf V).clockLayout.disjoint i j ((oldEmbedding V).injective h)

def historyLayout : VariableHistoryEquality.Layout V.proofQubits (clockWires V) (total V) where
  equality := historyEquality V
  clock := historyClock V
  tags := historyTags V
  eq_disjoint i j := history_no_small_tag V (historyTagChoice i) (by fin_cases i <;> decide) j
  clock_disjoint i j h :=
    ((layoutOf V).clock_ne_tag j (historyTagChoice i)).symm ((oldEmbedding V).injective h)
  flags_disjoint i j h :=
    (layoutOf V).tag_ne_scratch (historyTagChoice i) _ ((oldEmbedding V).injective h)





end QMAPerfectCompleteness.Main.CertificateMasterLayout


