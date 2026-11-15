-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_BlockImplements
-- name    : QMAPerfectCompleteness_Proof_BlockImplements
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:01:05.198591+00:00
-- url     : https://prove2.me/theorems/e58ea0a8-495d-4063-a5c6-550951c1236c
-- title:
--   Basis embeddings and exact circuit transport
-- statement:
--   For a basis encoding $e$, defines an inclusion matrix whose $(y,x)$ entry is one when $y=e(x)$ and zero otherwise. Exact transport from an encoding $e$ to an encoding $f$ by a physical circuit $C$, with logical action $U$, is expressed by $C J_e=J_f U$; this covers clean and predicate-tagged workspace fibers.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/BlockImplements.lean, lines 16–58.

/- Generated from Solutions.BlockImplements by authoritative Stage-2 skeleton subtraction.
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



/-! Exact realization of the literal paper compiler on the published wire layout. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.BlockImplements
open BlockCompiler BlockCoordinates BlockClockCoordinates ReversibleGadgets

/-- Computational-basis inclusion used for clean and predicate-tagged register encodings. -/
noncomputable def basisEmbedding {α β : Type*} (e : α → β) : Matrix β α ℂ :=
  by
    classical
    exact fun y x => if y = e x then 1 else 0

/-- A circuit transports one basis encoding to another, with the stated logical operation. -/
def Transports {α β : Type*} [Fintype α] [Fintype β]
    (e f : α → β) (C : Matrix β β ℂ) (U : Matrix α α ℂ) : Prop :=
  C * basisEmbedding e = basisEmbedding f * U





noncomputable def basisMap {α : Type*} (f : α → α) : Matrix α α ℂ := basisEmbedding f





variable (V : Verifier gatesG2)
abbrev D := layoutOf V
abbrev Physical := Basis (BlockCircuit.bodyWires V+(D V).work)
abbrev Logical := V.BlockReg (indexQubits V)



































end QMAPerfectCompleteness.Main.BlockImplements


