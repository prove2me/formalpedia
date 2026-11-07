-- Prove2me | Definitions.Def_AaronsonAmbainis_Level_Basic
-- name    : AaronsonAmbainis_Level_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:33:10.248197+00:00
-- url     : https://prove2.me/theorems/115a13e4-1a7b-4fc5-8c64-0b472afda158
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
set_option autoImplicit true
namespace AaronsonAmbainis
namespace Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end Level
end AaronsonAmbainis


