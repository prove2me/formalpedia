-- Prove2me | Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffWeights
-- name    : PretorsionImageClosed_LinearQuiver_CutoffWeights
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T06:11:27.591988+00:00
-- url     : https://prove2.me/theorems/21d24092-7321-4987-80d2-a0905efb5da6
-- title:
--   Cutoff Weights
-- statement:
--   Definitions and structural lemmas for Cutoff Weights, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffWeights.lean

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffCriterion
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Counting
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed
open CategoryTheory Limits Statement Polynomial Finset
namespace LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
def RowCutoff.rowsReaching (β : RowCutoff n) : ℕ := (univ.filter (fun a : Fin n => β.β a = n)).card
def colCount (β : RowCutoff n) (α : ColCutoff n) (d : Fin n) : ℕ :=
  (univ.filter (fun a : Fin n => a ≤ d ∧ d.val < β.β a ∧ α.α d ≤ a.val)).card
def middleCount (β : RowCutoff n) (α : ColCutoff n) : ℕ := ∑ d, colCount β α d
def cpWeight (p : CutoffPair n) : Rq[X] :=
  X ^ p.1.1.rowsReaching * C (q ^ middleCount p.1.1 p.1.2)
instance : Fintype (CutoffPair n) := Fintype.ofFinite _
instance : Fintype (PretorsionTheory (Statement.LinRep k n)) := Fintype.ofFinite _
end LinearQuiver
end PretorsionImageClosed


