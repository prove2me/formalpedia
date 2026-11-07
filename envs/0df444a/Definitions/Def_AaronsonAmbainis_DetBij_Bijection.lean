-- Prove2me | Definitions.Def_AaronsonAmbainis_DetBij_Bijection
-- name    : AaronsonAmbainis_DetBij_Bijection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:42:42.710732+00:00
-- url     : https://prove2.me/theorems/618459ba-087b-4ecf-b6f3-7da6e992e780
-- title:
--   Bijection
-- statement:
--   Definitions and structural lemmas for Bijection, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Bijection.lean

import Definitions.Def_AaronsonAmbainis_DetBij_Perm
set_option autoImplicit true
namespace AaronsonAmbainis.DetBij
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]
end AaronsonAmbainis.DetBij


