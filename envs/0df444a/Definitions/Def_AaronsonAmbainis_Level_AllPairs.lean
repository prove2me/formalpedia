-- Prove2me | Definitions.Def_AaronsonAmbainis_Level_AllPairs
-- name    : AaronsonAmbainis_Level_AllPairs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:32:43.683519+00:00
-- url     : https://prove2.me/theorems/cb9049b0-3766-4ede-aa11-a1fbe3977f59
-- title:
--   All Pairs
-- statement:
--   Definitions and structural lemmas for All Pairs, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/AllPairs.lean

import Definitions.Def_AaronsonAmbainis_Level_Rows
import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
set_option autoImplicit true
namespace AaronsonAmbainis
namespace Level
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]
end Level
end AaronsonAmbainis


