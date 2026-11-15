-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CoherentCertificate
-- name    : QMAPerfectCompleteness_Proof_CoherentCertificate
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:03:46.008512+00:00
-- url     : https://prove2.me/theorems/e2595221-30bb-438b-a91c-d8b20cf453e9
-- title:
--   Coherent certificate initialization and rejection projector
-- statement:
--   Defines proof and computation registers carrying a history and a certificate claim. Initialization prepares the index state and incoming flag independently in every claim sector. The rejection projector tests the selected zero block for valid claims and is the identity on invalid claims, so invalid certificates reject unconditionally.
-- source:
--   Auxiliary construction in the formalization of Grewal–Rudolph, QMA has perfect completeness (paper manuscript ~/research/qma1z/main.tex). Source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CoherentCertificate.lean, lines 12–31.

/- Generated from Solutions.CoherentCertificate by authoritative Stage-2 skeleton subtraction.
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



/-! Coherent certificate control, invalid-claim rejection, and the final acceptance bridge.
This module proves the measurement algebra independently of how the literal dynamic
comparison circuit is synthesized. -/
open Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CoherentCertificate
open CertificateMixture VerifierAnalysis

abbrev ProofReg (V : Verifier gatesG2) := History V × Claim V
abbrev ComputationReg (V : Verifier gatesG2) := V.BlockReg (indexQubits V) × Claim V



/-- Prepare η on every certificate branch. -/
noncomputable def initialIsometry (V : Verifier gatesG2) : Matrix (ComputationReg V) (ProofReg V) ℂ :=
  Matrix.blockDiagonal fun _ : Claim V => V.zEmbed (indexQubits V) true

/-- Rejection checks all of Z for valid claims and rejects invalid claims unconditionally. -/
noncomputable def rejectProjector (V : Verifier gatesG2) :
    Matrix (ComputationReg V) (ComputationReg V) ℂ := by
  classical
  exact Matrix.blockDiagonal fun c : Claim V => if IsValidCertificate V c.2.1 c.2.2 then
    V.zEmbed (indexQubits V) false * (V.zEmbed (indexQubits V) false)ᴴ else 1















end QMAPerfectCompleteness.Main.CoherentCertificate


