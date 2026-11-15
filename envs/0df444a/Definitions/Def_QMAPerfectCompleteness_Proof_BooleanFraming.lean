-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_BooleanFraming
-- name    : QMAPerfectCompleteness_Proof_BooleanFraming
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:50:33.654199+00:00
-- url     : https://prove2.me/theorems/d176e57e-a748-4573-8723-e3093d89c466
-- title:
--   Read and write supports of Boolean commands
-- statement:
--   Records the target wire and the set of wires read or written by each reversible Boolean command. These predicates express the support conditions used to show that unrelated registers are unchanged and that compute–uncompute circuits can reuse clean workspace.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/BooleanFraming.lean, lines 6–14.

/- Generated from Solutions.BooleanFraming by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets



/-! Inverses and frame rules for the concrete Boolean straight-line compiler. -/
namespace QMAPerfectCompleteness.Main.BooleanCircuits

def Command.target {n : ℕ} : Command n → Fin n
  | .flip t => t
  | .copy _ t _ => t
  | .conj _ _ t _ _ => t

def Command.Within {n : ℕ} (S : Set (Fin n)) : Command n → Prop
  | .flip t => t ∈ S
  | .copy a t _ => a ∈ S ∧ t ∈ S
  | .conj a b t _ _ => a ∈ S ∧ b ∈ S ∧ t ∈ S

















end QMAPerfectCompleteness.Main.BooleanCircuits


