-- Prove2me | Definitions.Def_AaronsonAmbainis_DetLow_Basic
-- name    : AaronsonAmbainis_DetLow_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:19:59.344775+00:00
-- url     : https://prove2.me/theorems/fa35cb51-493c-4d2b-b178-6fc05536ecf0
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Basic.lean

import Definitions.Def_AaronsonAmbainis_DetDefs
set_option autoImplicit true
namespace AaronsonAmbainis
namespace DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def Up (g : Cube ι → Bool) (j : ι) : Finset (Ones g) :=
  univ.filter fun x => x.1 j = true ∧ g (flipSet x.1 {j}) = true
end DetLow
end AaronsonAmbainis


