-- Prove2me | Definitions.Def_AaronsonAmbainis_DetBij_Perm
-- name    : AaronsonAmbainis_DetBij_Perm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:29:14.829589+00:00
-- url     : https://prove2.me/theorems/42852c1e-e524-4ab9-a6b4-50ff70c3e2f8
-- title:
--   Perm
-- statement:
--   Definitions and structural lemmas for Perm, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Perm.lean

import Definitions.Def_AaronsonAmbainis_DetBij_Identity
set_option autoImplicit true
namespace AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
end AaronsonAmbainis.DetBij


