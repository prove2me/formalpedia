-- Prove2me | Definitions.Def_AaronsonAmbainis_DetLow_RowOps
-- name    : AaronsonAmbainis_DetLow_RowOps
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:26:38.997205+00:00
-- url     : https://prove2.me/theorems/21d15af5-669b-489f-a163-01cf871a6eb4
-- title:
--   Row Ops
-- statement:
--   Definitions and structural lemmas for Row Ops, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/RowOps.lean

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
set_option autoImplicit true
namespace AaronsonAmbainis
namespace DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
noncomputable def pairMat (g : Cube ι → Bool) (j : ι) :
    Matrix (Ones g) (Ones g) (MvPolynomial ι ℤ) :=
  fun x y => if x.1 j = true ∧ y.1 = flipSet x.1 {j} then 1 else 0
noncomputable def redMat (g : Cube ι → Bool) (j : ι) :
    Matrix (Ones g) (Ones g) (MvPolynomial ι ℤ) :=
  fun x z => if x ∈ Up g j ∧ z.1 j = x.1 j then 0 else agMon x.1 z.1
noncomputable def diagVec (g : Cube ι → Bool) (j : ι) : Ones g → MvPolynomial ι ℤ :=
  fun x => if x ∈ Up g j then 1 - X j ^ 2 else 1
end DetLow
end AaronsonAmbainis


