-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_RegisterCopies
-- name    : QMAPerfectCompleteness_Proof_RegisterCopies
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:51:55.950754+00:00
-- url     : https://prove2.me/theorems/d8f49378-5fe6-473f-9fa9-9b00b04bb11d
-- title:
--   Parallel classical register copies
-- statement:
--   Defines a literal list of classical controlled-copy commands with distinct target wires. The commands read the specified source bits without changing their source register.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/RegisterCopies.lean, retained declaration span lines 11–12.

/- Generated from Solutions.RegisterCopies by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanFraming
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets



/-! Parallel classical register copies with distinct targets and unchanged source wires. -/
namespace QMAPerfectCompleteness.Main.RegisterCopies
open BooleanCircuits

variable {ι : Type*} [DecidableEq ι] {n : ℕ}
variable (source : ι → Fin n) (target : ι ↪ Fin n)
variable (hd : ∀ i j, source i ≠ target j)

def commands (js : List ι) : List (Command n) :=
  js.map fun j => .copy (source j) (target j) (hd j j)













end QMAPerfectCompleteness.Main.RegisterCopies


