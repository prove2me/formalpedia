-- Prove2me | Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
-- name    : PretorsionImageClosed_Gandhi_ColumnSum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:34:36.585742+00:00
-- url     : https://prove2.me/theorems/899cc3c3-6e1f-479b-8281-f0802c77097b
-- title:
--   Column Sum
-- statement:
--   Definitions and structural lemmas for Column Sum, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Gandhi/ColumnSum.lean

module
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed.Statement
open Polynomial Finset
variable {ι : Type*} [LinearOrder ι]
def psiTerm (R Cont : Finset ι) : Rq[X] :=
  X ^ Cont.card * (C (q ^ Cont.card) +
    ∑ e ∈ Cont.filter (fun e => ∀ a ∈ R, a < e → a ∈ Cont),
      C (q ^ (Cont.filter (fun a => e < a)).card))
def psi (R : Finset ι) : Rq[X] := ∑ Cont ∈ R.powerset, psiTerm R Cont
def admCount (R J : Finset ι) : ℕ :=
  (R.filter (fun c => ∀ j ∈ J, c ≤ j)).card + J.card + (if J = ∅ then 1 else 0)
def thetaTerm (R J : Finset ι) : Rq[X] := C (q ^ J.card) * X ^ admCount R J
def theta (R : Finset ι) : Rq[X] := ∑ J ∈ R.powerset, thetaTerm R J
end PretorsionImageClosed.Statement


