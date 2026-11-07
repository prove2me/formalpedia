-- Prove2me | Definitions.Def_AaronsonAmbainis_Average_Iterate
-- name    : AaronsonAmbainis_Average_Iterate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:36:12.648769+00:00
-- url     : https://prove2.me/theorems/2729b7d1-8637-462b-85c7-24f333347d1d
-- title:
--   Iterate
-- statement:
--   Definitions and structural lemmas for Iterate, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Iterate.lean

import Definitions.Def_AaronsonAmbainis_Average_Coordinate
import Definitions.Def_AaronsonAmbainis_Level_Basic
set_option autoImplicit true
namespace AaronsonAmbainis
namespace Average
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]
end Average
end AaronsonAmbainis


