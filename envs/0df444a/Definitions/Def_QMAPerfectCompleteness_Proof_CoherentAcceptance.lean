-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CoherentAcceptance
-- name    : QMAPerfectCompleteness_Proof_CoherentAcceptance
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:04:44.779144+00:00
-- url     : https://prove2.me/theorems/a147e019-26a5-4e21-9043-4a8106169e96
-- title:
--   Decidable equality for coherent computation registers
-- statement:
--   Supplies classical decidable equality on the finite computation-register basis used by the coherent certificate verifier. This auxiliary instance allows the subsequent acceptance algebra to form identity matrices and compare basis indices on certificate-controlled sectors.
-- source:
--   Auxiliary construction in the formalization of Grewal–Rudolph, QMA has perfect completeness (paper manuscript ~/research/qma1z/main.tex). Source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CoherentAcceptance.lean, lines 8–8.

/- Generated from Solutions.CoherentAcceptance by authoritative Stage-2 skeleton subtraction.
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



/-! Exact acceptance algebra for retained certificate fibers and ignored ancillary garbage. -/
open Matrix
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CoherentCertificate
open CertificateMixture
noncomputable local instance computationDecEq (V : Verifier gatesG2) : DecidableEq (ComputationReg V) := Classical.decEq _









end QMAPerfectCompleteness.Main.CoherentCertificate


