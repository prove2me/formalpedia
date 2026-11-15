-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_VerifierAnalysis
-- name    : QMAPerfectCompleteness_Proof_VerifierAnalysis
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:01:25.129862+00:00
-- url     : https://prove2.me/theorems/bbc949b3-b3b3-4015-99a1-8e2c468e1d56
-- title:
--   Pure-history rejection probability of the block test
-- statement:
--   Defines the rejection probability for a pure history vector as the square of the Euclidean norm of its image under the selected rejection block. This scalar quantity links the cyclic residual lower bound with the certificate verifier’s rejection effect.
-- source:
--   Auxiliary construction in the formalization of Grewal–Rudolph, QMA has perfect completeness (paper manuscript ~/research/qma1z/main.tex). Source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/VerifierAnalysis.lean, lines 9–12.

/- Generated from Solutions.VerifierAnalysis by authoritative Stage-2 skeleton subtraction.
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

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.Certificate
end QMAPerfectCompleteness.Main.Certificate
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof



open Matrix
open scoped ComplexOrder

namespace QMAPerfectCompleteness.Main.VerifierAnalysis

/-- Rejection probability of the block test on a pure history state. -/
noncomputable def rejectionProbability (V : Verifier gatesG2) (z : V.Proof)
    (a b : ℕ) (ψ : History V → ℂ) : ℝ :=
  euclidNorm (ProofSetup.rejectionBlock V z a b *ᵥ ψ) ^ 2











end QMAPerfectCompleteness.Main.VerifierAnalysis


