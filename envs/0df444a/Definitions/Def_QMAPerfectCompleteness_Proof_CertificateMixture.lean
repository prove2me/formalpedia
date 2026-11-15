-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMixture
-- name    : QMAPerfectCompleteness_Proof_CertificateMixture
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:02:38.769599+00:00
-- url     : https://prove2.me/theorems/8d504a22-3ec4-482d-b611-c05aa49757f3
-- title:
--   Certificate labels and their rejection effects
-- statement:
--   Defines a claim as a proof word $z$ together with two bounded binary integers. A valid claim has rejection effect $B^*B$, where $B$ is its block-test rejection map and $B^*$ denotes the adjoint; an invalid claim has rejection effect the identity. The definite-label embedding attaches a chosen classical claim to a history vector.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CertificateMixture.lean, lines 47–96.

/- Generated from Solutions.CertificateMixture by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
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



open Matrix
open scoped ComplexOrder

namespace QMAPerfectCompleteness.Main.CertificateMixture
open VerifierAnalysis

variable {ι C : Type*} [Fintype ι] [Fintype C] [DecidableEq ι] [DecidableEq C]











/-- The classical certificate is exactly z and two k-bit integers. -/
abbrev Claim (V : Verifier gatesG2) :=
  V.Proof × Fin (2 ^ indexQubits V) × Fin (2 ^ indexQubits V)

/-- Valid claims use the block-test rejection effect; invalid claims are rejected with certainty. -/
noncomputable def claimRejection (V : Verifier gatesG2) (c : Claim V) :
    Matrix (History V) (History V) ℂ := by
  classical
  exact if IsValidCertificate V c.2.1 c.2.2 then
    (ProofSetup.rejectionBlock V c.1 c.2.1 c.2.2)ᴴ *
      ProofSetup.rejectionBlock V c.1 c.2.1 c.2.2
  else 1







/-- Attach a definite classical certificate to a history vector. -/
def attachClaim (c : C) (ψ : ι → ℂ) : ι × C → ℂ := fun x => if x.2 = c then ψ x.1 else 0







end QMAPerfectCompleteness.Main.CertificateMixture


