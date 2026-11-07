-- Prove2me | Definitions.Def_AaronsonAmbainis_DetLow_Count
-- name    : AaronsonAmbainis_DetLow_Count
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:52:51.014207+00:00
-- url     : https://prove2.me/theorems/ece40d2b-3423-4580-a06b-019ee60e80fb
-- title:
--   Count
-- statement:
--   Definitions and structural lemmas for Count, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Count.lean

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
set_option autoImplicit true
namespace AaronsonAmbainis
namespace DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def Dn (g : Cube ι → Bool) (j : ι) : Finset (Ones g) :=
  univ.filter fun x => x.1 j = false ∧ g (flipSet x.1 {j}) = true
def Bd (g : Cube ι → Bool) (j : ι) : Finset (Ones g) :=
  univ.filter fun x => g (flipSet x.1 {j}) = false
end DetLow
end AaronsonAmbainis


