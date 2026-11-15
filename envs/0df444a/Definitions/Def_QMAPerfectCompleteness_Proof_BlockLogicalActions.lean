-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_BlockLogicalActions
-- name    : QMAPerfectCompleteness_Proof_BlockLogicalActions
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:02:18.626688+00:00
-- url     : https://prove2.me/theorems/9da68d04-9235-4ed5-86dc-e3bf4dd8fef7
-- title:
--   Signed deterministic basis maps
-- statement:
--   Defines the matrix of a deterministic basis map with a scalar attached to each input column: its $(y,x)$ entry is $s(x)$ when $y=f(x)$ and zero otherwise. This combines classical clock and flag actions with the minus signs required by the cyclic block encoding.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/BlockLogicalActions.lean, lines 10–12.

/- Generated from Solutions.BlockLogicalActions by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockImplements
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockLogicalSelect
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockStateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockVerifierCoordinates
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
namespace QMAPerfectCompleteness.Main.BlockTransport
end QMAPerfectCompleteness.Main.BlockTransport



/-! Deterministic logical matrix entries for flag and clock operations. -/
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.BlockImplements

noncomputable def signedMap {α : Type*} (f : α → α) (s : α → ℂ) : Matrix α α ℂ := by
  classical
  exact fun y x => if y = f x then s x else 0







variable (V : Verifier gatesG2)







end QMAPerfectCompleteness.Main.BlockImplements


