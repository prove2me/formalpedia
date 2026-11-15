-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_BlockStateCoordinates
-- name    : QMAPerfectCompleteness_Proof_BlockStateCoordinates
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:59:07.398265+00:00
-- url     : https://prove2.me/theorems/87b7024c-72b7-4ecf-a3c8-53a41eefc547
-- title:
--   Physical basis type for the block compiler
-- statement:
--   Fixes the verifier-induced block layout and its physical computational-basis type. These abbreviations keep the history-register dimensions and the shared workspace consistent across the subsequent coordinate and transport arguments.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/BlockStateCoordinates.lean, lines 11–12.

/- Generated from Solutions.BlockStateCoordinates by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockClockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCompiler
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



/-! Pure basis-state identities for the concrete block compiler's register layout. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Matrix
namespace QMAPerfectCompleteness.Main.BlockStateCoordinates
open BlockCompiler BlockCoordinates
variable (V : Verifier gatesG2)
abbrev D := layoutOf V
abbrev Physical := Basis (BlockCircuit.bodyWires V+(D V).work)















end QMAPerfectCompleteness.Main.BlockStateCoordinates


