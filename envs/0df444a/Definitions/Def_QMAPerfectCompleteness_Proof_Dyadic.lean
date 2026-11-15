-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_Dyadic
-- name    : QMAPerfectCompleteness_Proof_Dyadic
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:45:30.991195+00:00
-- url     : https://prove2.me/theorems/56114f67-026d-4ced-a3e4-100dd85f45a7
-- title:
--   Integer-valued complex matrices
-- statement:
--   Defines the predicate that every entry of a complex matrix lies in the image of the integer cast. It is the exact integrality notion used in Corollary 3.2 when the G₂ acceptance matrix is multiplied by the prescribed power of two.
-- source:
--   Auxiliary construction in the formalization of Grewal–Rudolph, QMA has perfect completeness (paper manuscript ~/research/qma1z/main.tex). Source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/Dyadic.lean, lines 6–8.

/- Generated from Solutions.Dyadic by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic



open Matrix
namespace QMAPerfectCompleteness.Main.Dyadic

/-- Matrices all of whose entries are rational integers embedded in the complexes. -/
def IntegerEntries {ι κ : Type*} (M : Matrix ι κ ℂ) : Prop :=
  ∀ i j, M i j ∈ (Int.castRingHom ℂ).range





























end QMAPerfectCompleteness.Main.Dyadic


