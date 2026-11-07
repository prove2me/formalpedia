-- Prove2me | Definitions.Def_AaronsonAmbainis_DetLow_Degree
-- name    : AaronsonAmbainis_DetLow_Degree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:23:09.162205+00:00
-- url     : https://prove2.me/theorems/de0eec5d-3a3c-4b46-b255-6e0882d8028e
-- title:
--   Degree
-- statement:
--   Definitions and structural lemmas for Degree, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Degree.lean

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
set_option autoImplicit true
namespace AaronsonAmbainis
namespace DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
end DetLow
end AaronsonAmbainis


