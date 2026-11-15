-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterLayout
-- name    : QMAPerfectCompleteness_Proof_CertificateMasterLayout
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:08:16.630455+00:00
-- url     : https://prove2.me/theorems/5a79781d-52b7-4282-a801-ae5108da3334
-- title:
--   Master register layout for the coherent certificate verifier
-- statement:
--   Allocates one physical register containing the original block circuit, six padded arithmetic words, shared carry storage, validity tags, zero-test work and the appended certificate. The original block wires retain their addresses, and two independent zero-padding wires extend the index to the width required by certificate arithmetic; the additional space is linear in the register widths.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CertificateMasterLayout.lean, lines 11–83.

/- Generated from Solutions.CertificateMasterLayout by authoritative Stage-2 skeleton subtraction.
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



/-! One polynomial physical workspace for the coherent certificate verifier. -/
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CertificateMasterLayout
open BlockCircuit BlockCompiler CertificateCoordinates

variable (V : Verifier gatesG2)
abbrev k := indexQubits V
abbrev r := indexQubits V+2
abbrev oldWork := (layoutOf V).work
abbrev prepWork := 6*(indexQubits V+2)+(indexQubits V+3)+1
abbrev readoutWork := indexQubits V+V.ancillaQubits+2
abbrev work := oldWork V+prepWork V+2+6+readoutWork V+2
abbrev total := (bodyWires V+work V)+claimQubits V

/-- Prefix placement retains every published block-compiler wire address. -/
def oldEmbedding : Fin (layoutOf V).total ↪ Fin (total V) :=
  Fin.castLEEmb (by
    change bodyWires V+oldWork V ≤ (bodyWires V+work V)+claimQubits V
    have hw : oldWork V ≤ work V := by dsimp only [work]; omega
    omega)

def bank (start len : ℕ) (h : start+len ≤ work V) : Fin len ↪ Fin (total V) :=
  ⟨fun j => ⟨bodyWires V+start+j.val,by have := j.isLt; dsimp [total]; omega⟩,
    by intro i j hij; apply Fin.ext; have hv := congrArg Fin.val hij; dsimp at hv; omega⟩

def prepWordBank : Fin (6*r V) ↪ Fin (total V) :=
  bank V (oldWork V) (6*r V) (by dsimp [work,prepWork,r]; omega)
def prepCarry : Fin (k V+3) ↪ Fin (total V) :=
  bank V (oldWork V+6*r V) (k V+3) (by dsimp [work,prepWork,r,k]; omega)
def prepTemp : Fin (total V) :=
  bank V (oldWork V+6*r V+(k V+3)) 1 (by dsimp [work,prepWork,r,k]; omega) 0

def prepWord (d : Fin 6) (j : Fin (r V)) : Fin (total V) := prepWordBank V (finProdFinEquiv (d,j))

def padding : Fin 2 ↪ Fin (total V) :=
  bank V (oldWork V+prepWork V) 2 (by dsimp [work]; omega)
def validity : Fin 6 ↪ Fin (total V) :=
  bank V (oldWork V+prepWork V+2) 6 (by dsimp [work]; omega)
def readoutFlags : Fin (readoutWork V) ↪ Fin (total V) :=
  bank V (oldWork V+prepWork V+2+6) (readoutWork V) (by dsimp [work]; omega)
def readoutTags : Fin 2 ↪ Fin (total V) :=
  bank V (oldWork V+prepWork V+2+6+readoutWork V) 2 (by dsimp [work]; omega)

/-- Certificate z lies after the whole computational body and workspace. -/
def certZ : Fin V.proofQubits ↪ Fin (total V) :=
  ⟨fun j => ⟨bodyWires V+work V+j.val,by have := j.isLt; dsimp [total,claimQubits]; omega⟩,
    by intro i j hij; apply Fin.ext; have hv := congrArg Fin.val hij; dsimp at hv; omega⟩
def certAB : Fin (2*k V) ↪ Fin (total V) :=
  ⟨fun j => ⟨bodyWires V+work V+V.proofQubits+j.val,by
      have hj : j.val < 2*indexQubits V := j.isLt
      dsimp only [total,claimQubits]; omega⟩,
    by intro i j hij; apply Fin.ext; have hv := congrArg Fin.val hij; dsimp at hv; omega⟩
def certificate (s : Fin 2) (j : Fin (k V)) : Fin (total V) := certAB V (finProdFinEquiv (s,j))


@[simp] lemma bank_val (start len : ℕ) (h : start+len≤work V) (j : Fin len) :
    (bank V start len h j).val=bodyWires V+start+j.val := rfl

@[simp] lemma certAB_val (j : Fin (2*k V)) :
    (certAB V j).val=bodyWires V+work V+V.proofQubits+j.val := rfl

/-- Published block index, padded by two independent zero wires for k+2-bit arithmetic. -/
def paddedIndex : Fin (r V) ↪ Fin (total V) :=
  ⟨fun j => ⟨if j.val<k V then j.val else bodyWires V+oldWork V+prepWork V+(j.val-k V),by
      have hj : j.val<k V+2 := j.isLt
      have hb : k V ≤ bodyWires V := by dsimp only [k,bodyWires]; omega
      have hw : oldWork V+prepWork V+2 ≤ work V := by dsimp only [work]; omega
      change (if j.val<k V then j.val else bodyWires V+oldWork V+prepWork V+(j.val-k V)) <
        (bodyWires V+work V)+claimQubits V
      split_ifs <;> omega⟩,
    by
      intro i j h
      have hv := congrArg Fin.val h
      change (if i.val<k V then i.val else bodyWires V+oldWork V+prepWork V+(i.val-k V)) =
        (if j.val<k V then j.val else bodyWires V+oldWork V+prepWork V+(j.val-k V)) at hv
      have hb : k V ≤ bodyWires V := by dsimp only [k,bodyWires]; omega
      apply Fin.ext
      split_ifs at hv <;> omega⟩

end QMAPerfectCompleteness.Main.CertificateMasterLayout


