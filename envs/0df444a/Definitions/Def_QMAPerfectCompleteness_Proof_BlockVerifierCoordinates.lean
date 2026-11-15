-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_BlockVerifierCoordinates
-- name    : QMAPerfectCompleteness_Proof_BlockVerifierCoordinates
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:57:47.215415+00:00
-- url     : https://prove2.me/theorems/ace6802e-64d0-4c3b-8651-97ebb89f5536
-- title:
--   Verifier calls in logical block coordinates
-- statement:
--   Places an arbitrary operator on the original verifier wires inside the logical block register, with identity action on the index and the other spectator registers. This is the logical operator corresponding to the literal calls to the verifier and its inverse in SELECT.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/BlockVerifierCoordinates.lean, lines 66–69.

/- Generated from Solutions.BlockVerifierCoordinates by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.BlockComposition
end QMAPerfectCompleteness.Main.BlockComposition



/-! The two literal verifier calls in logical block coordinates, with arbitrary workspace. -/
open Matrix
open scoped Kronecker
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.BlockVerifierCoordinates
open BlockCircuit BlockCoordinates ReversibleGadgets



noncomputable def logicalVerifier (V : Verifier gatesG2)
    (M : Matrix V.Wire V.Wire ℂ) :
    Matrix (V.BlockReg (indexQubits V)) (V.BlockReg (indexQubits V)) ℂ :=
  (1 : Matrix (Fin (2^indexQubits V)) (Fin (2^indexQubits V)) ℂ) ⊗ₖ V.onWires M











end QMAPerfectCompleteness.Main.BlockVerifierCoordinates


