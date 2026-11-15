-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CoherentReadout
-- name    : QMAPerfectCompleteness_Proof_CoherentReadout
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:06:03.953902+00:00
-- url     : https://prove2.me/theorems/513f550d-4b03-4b0b-a6a4-d7f9db27cbc3
-- title:
--   Basis inclusions and the selected zero-block support
-- statement:
--   Defines the inclusion matrix of a basis map and the predicate selecting the all-zero auxiliary block with outgoing flag zero. These auxiliary objects connect the final Boolean readout of the physical circuit to the logical projector used in the cyclic rejection test.
-- source:
--   Auxiliary construction in the formalization of Grewal–Rudolph, QMA has perfect completeness (paper manuscript ~/research/qma1z/main.tex). Source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CoherentReadout.lean, lines 10–77.

/- Generated from Solutions.CoherentReadout by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMixture
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentAcceptance
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentCertificate
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_Dyadic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_PointwiseSetup
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierAnalysis

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.Certificate
end QMAPerfectCompleteness.Main.Certificate
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof



/-! Exact matrix compression of a final Boolean readout flag and the all-zero Z projector. -/
open Matrix
open scoped Classical
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CoherentCertificate
open CertificateMixture

noncomputable def basisMatrix {α β : Type*} (e : α → β) : Matrix β α ℂ :=
  Matrix.of fun y x => if y=e x then 1 else 0







/-- The support of |0⟩_Z⊗I on the logical block register. -/
def zeroZ (V : Verifier gatesG2) (p : V.BlockReg (indexQubits V)) : Prop :=
  ∃h : History V,p=(0,BlockProof.bodyInitial V false h)







end QMAPerfectCompleteness.Main.CoherentCertificate


