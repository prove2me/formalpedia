-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_BlockLogicalSelect
-- name    : QMAPerfectCompleteness_Proof_BlockLogicalSelect
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:48:13.157556+00:00
-- url     : https://prove2.me/theorems/8d19e51b-d19f-409d-b6e9-2061104071c0
-- title:
--   Logical branches of the indexed SELECT operator
-- statement:
--   Defines index-controlled selection of body operators and the logical middle and post-call factors for a certificate $(z,a,b)$. The intervals cut at $a$, $3a$ and $3a+b$ select the identity, forward-transition and closing branches, including their flag actions and negative phases.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/BlockLogicalSelect.lean, lines 9–55.

/- Generated from Solutions.BlockLogicalSelect by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates



/-! Abstract branch assembly for the literal block compiler. -/
open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.BlockLogicalSelect
variable (V : Verifier gatesG2)
abbrev Logical := V.BlockReg (indexQubits V)

noncomputable def select (F : Fin (2^indexQubits V) → Matrix V.Body V.Body ℂ) :
    Matrix (Logical V) (Logical V) ℂ := by
  classical
  exact fun y x => if y.1 = x.1 then F x.1 y.2 x.2 else 0









noncomputable def midBranch (a : ℕ) (j : Fin (2^indexQubits V)) : Matrix V.Body V.Body ℂ :=
  if j.val < a then 1 else if j.val < 3*a then
    V.flipIf (fun t q => decide (t.val < ell V.proofQubits) && q V.output) else 1

noncomputable def postBranch (z : V.Proof) (a b : ℕ) (j : Fin (2^indexQubits V)) :
    Matrix V.Body V.Body ℂ :=
  if j.val < a then V.flagX else if j.val < 3*a then -V.shift
    else if j.val < 3*a+b then -V.gadgetR z else 1











end QMAPerfectCompleteness.Main.BlockLogicalSelect


