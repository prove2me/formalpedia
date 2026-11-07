-- Prove2me | Definitions.Def_AaronsonAmbainis_DetBij_Main
-- name    : AaronsonAmbainis_DetBij_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:31:06.503596+00:00
-- url     : https://prove2.me/theorems/465fd97a-32c2-43d4-90ec-c5c7b840263d
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Main.lean

import Definitions.Def_AaronsonAmbainis_DetBij_Perm
set_option autoImplicit true
namespace AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def extWing (g : Cube ι → Bool) (A : Cube ι → Finset ι) (x : Cube ι) : Finset ι :=
  if x ∈ zone g then A x else ∅
end AaronsonAmbainis.DetBij


