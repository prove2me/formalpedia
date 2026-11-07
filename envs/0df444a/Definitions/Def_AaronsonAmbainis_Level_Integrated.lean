-- Prove2me | Definitions.Def_AaronsonAmbainis_Level_Integrated
-- name    : AaronsonAmbainis_Level_Integrated
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:34:47.500476+00:00
-- url     : https://prove2.me/theorems/848c029a-8910-4c59-95e6-f32f42b70c1d
-- title:
--   Integrated
-- statement:
--   Definitions and structural lemmas for Integrated, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Integrated.lean

import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Level_Integral
import Definitions.Def_AaronsonAmbainis_Level_AllPairs
set_option autoImplicit true
namespace AaronsonAmbainis
open Finset
namespace Level
variable {ι : Type} [Fintype ι] [DecidableEq ι]
end Level
end AaronsonAmbainis


