-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CertificateCoordinates
-- name    : QMAPerfectCompleteness_Proof_CertificateCoordinates
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:05:15.697573+00:00
-- url     : https://prove2.me/theorems/d6cfa95a-97e4-4b50-924c-3f5884000f07
-- title:
--   Binary coordinates for history and certificate registers
-- statement:
--   Constructs equivalences between contiguous qubit registers and the history together with a certificate $(z,a,b)$, where $a$ and $b$ are $k$-bit integers. A further equivalence reads the logical block body and certificate from the physical computation while retaining every workspace bit.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CertificateCoordinates.lean, lines 8–49.

/- Generated from Solutions.CertificateCoordinates by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMixture
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
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierAnalysis

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.Certificate
end QMAPerfectCompleteness.Main.Certificate
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof



/-! Concrete qubit coordinates for a coherent binary certificate and its history proof. -/
namespace QMAPerfectCompleteness.Main.CertificateCoordinates
open BlockCircuit BlockCoordinates IndexHadamards CertificateMixture

def splitBasis (a b : ℕ) : Basis (a+b) ≃ Basis a × Basis b where
  toFun x := (fun i => x (Fin.castAdd b i),fun i => x (Fin.natAdd a i))
  invFun p := Fin.append p.1 p.2
  left_inv x := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · exact Fin.append_left _ _ _
    · exact Fin.append_right _ _ _
  right_inv p := by
    apply Prod.ext
    · funext i; exact Fin.append_left _ _ _
    · funext i; exact Fin.append_right _ _ _

abbrev claimQubits (V : Verifier gatesG2) : ℕ := V.proofQubits + (indexQubits V+indexQubits V)
abbrev proofQubits (V : Verifier gatesG2) : ℕ :=
  (clockWires V+V.proofQubits) + claimQubits V

def claimEquiv (V : Verifier gatesG2) : Basis (claimQubits V) ≃ Claim V :=
  (splitBasis V.proofQubits (indexQubits V+indexQubits V)).trans
    (Equiv.prodCongr (Equiv.refl _)
      ((splitBasis (indexQubits V) (indexQubits V)).trans
        (Equiv.prodCongr (bitsEquiv _) (bitsEquiv _))))

def historyEquiv (V : Verifier gatesG2) : Basis (clockWires V+V.proofQubits) ≃ History V :=
  (splitBasis (clockWires V) V.proofQubits).trans
    (Equiv.prodCongr (clockEquiv V) (Equiv.refl _))

/-- The physical proof contains the history, z, a and b in contiguous binary registers. -/
def proofEquiv (V : Verifier gatesG2) : Basis (proofQubits V) ≃ CoherentCertificate.ProofReg V :=
  (splitBasis (clockWires V+V.proofQubits) (claimQubits V)).trans
    (Equiv.prodCongr (historyEquiv V) (claimEquiv V))

/-- A circuit may use the original published block layout followed by certificate wires.
This equivalence reads its logical body and certificate while retaining all workspace bits. -/
def computationEquiv (V : Verifier gatesG2) (w : ℕ) :
    Basis ((bodyWires V+w)+claimQubits V) ≃ CoherentCertificate.ComputationReg V × Basis w :=
  ((splitBasis (bodyWires V+w) (claimQubits V)).trans
    (Equiv.prodCongr (coordinates V w) (claimEquiv V))).trans
    { toFun := fun p => ((p.1.1,p.2),p.1.2)
      invFun := fun p => ((p.1.1,p.2),p.1.2)
      left_inv := by rintro ⟨⟨p,w⟩,c⟩; rfl
      right_inv := by rintro ⟨⟨p,c⟩,w⟩; rfl }







end QMAPerfectCompleteness.Main.CertificateCoordinates


