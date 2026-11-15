-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_PointwiseSetup
-- name    : QMAPerfectCompleteness_Proof_PointwiseSetup
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:48:06.563204+00:00
-- url     : https://prove2.me/theorems/09a78966-a5be-4f43-85a9-79d622f2328a
-- title:
--   The scaled cyclic rejection block
-- statement:
--   Defines the scaled cyclic-consistency matrix used as the pointwise rejection block. Keeping this operator separate from the class reduction supports the honest-history and mixed-state soundness calculations.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, Section 3.3, the coherent-certificate verifier and controlled block construction. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/PointwiseSetup.lean, retained declaration span lines 30–35.

/- Generated from Solutions.PointwiseSetup by authoritative Stage-2 skeleton subtraction.
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

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.Certificate
end QMAPerfectCompleteness.Main.Certificate
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof



/-!
# Pointwise main-proof lemmas, following §3 of the paper

The certificate, cyclic constraint, and algebraic block identity are proved locally.
Pointwise lemmas are separate from class assembly and contain no proof holes.
Keep platform sources in Definitions/ and Theorems/ verbatim; do proof work in Solutions/.
-/

open Matrix

namespace QMAPerfectCompleteness.Main.ProofSetup



/-- The designated all-zero rejection amplitude, before taking its squared Euclidean norm.
The flag starts at one and is projected onto zero, exactly as in Lemma 3.6. -/
noncomputable def rejectionBlock (V : Verifier gatesG2) (z : V.Proof) (a b : ℕ) :
    Matrix (History V) (History V) ℂ :=
  (V.zEmbed (indexQubits V) false)ᴴ * V.blockUnitary (indexQubits V) z a b *
    V.zEmbed (indexQubits V) true

















end QMAPerfectCompleteness.Main.ProofSetup


