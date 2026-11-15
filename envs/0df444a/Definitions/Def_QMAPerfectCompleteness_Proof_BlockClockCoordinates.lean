-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_BlockClockCoordinates
-- name    : QMAPerfectCompleteness_Proof_BlockClockCoordinates
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:57:40.92537+00:00
-- url     : https://prove2.me/theorems/d6399de9-f0b6-4826-b919-f01852d49afd
-- title:
--   Physical controlled clock increment
-- statement:
--   Names the computational-basis action of the controlled modular clock increment on a block-circuit layout. This physical permutation is the clock operation whose logical-coordinate interpretation is used in the SELECT construction.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/BlockClockCoordinates.lean, lines 10–11.

/- Generated from Solutions.BlockClockCoordinates by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
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



/-! Physical controlled increment in the published logical clock coordinates. -/
set_option backward.isDefEq.respectTransparency false
open Matrix
namespace QMAPerfectCompleteness.Main.BlockClockCoordinates
open BlockCompiler ClockCircuits BlockCoordinates

abbrev increment (D : Layout) : Basis D.total → Basis D.total :=
  controlledIncrementAction D.incrementLayout




























end QMAPerfectCompleteness.Main.BlockClockCoordinates


