-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_RealSimulation
-- name    : QMAPerfectCompleteness_Proof_RealSimulation
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:44:56.039055+00:00
-- url     : https://prove2.me/theorems/1ce1b98c-3e9f-4fd8-9558-b65432c77f7c
-- title:
--   Real block representation of a complex matrix
-- statement:
--   For a complex matrix A, defines its real representation on a leading Boolean index by the block matrix with rows (Re A, −Im A) and (Im A, Re A). Boolean false indexes the real block and true the imaginary block. This is the representation used in the exact real simulation of Lemma 3.1.
-- source:
--   Auxiliary construction in the formalization of Grewal–Rudolph, QMA has perfect completeness (paper manuscript ~/research/qma1z/main.tex). Source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/RealSimulation.lean, lines 10–14.

/- Generated from Solutions.RealSimulation by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Gates



open Matrix
open scoped ComplexOrder

namespace QMAPerfectCompleteness.Main.RealSimulation

variable {ι κ τ : Type*}

/-- The real representation used in Lemma 3.1. The new Bool wire comes first;
`false` is the real block and `true` the imaginary block. -/
def realRep (A : Matrix ι κ ℂ) : Matrix (Bool × ι) (Bool × κ) ℝ :=
  fun x y => if x.1 then (if y.1 then (A x.2 y.2).re else (A x.2 y.2).im)
    else (if y.1 then -(A x.2 y.2).im else (A x.2 y.2).re)





























































open scoped Kronecker



end QMAPerfectCompleteness.Main.RealSimulation


