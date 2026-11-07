-- Prove2me | Definitions.Def_AaronsonAmbainis_Dual_Core
-- name    : AaronsonAmbainis_Dual_Core
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:40:23.476102+00:00
-- url     : https://prove2.me/theorems/2b5b62de-8adb-4eb5-a553-b0319940d5dc
-- title:
--   Core
-- statement:
--   Definitions and structural lemmas for Core, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Core.lean

import Definitions.Def_AaronsonAmbainis_RowDefs
set_option autoImplicit true
namespace AaronsonAmbainis
namespace Dual
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end Dual
end AaronsonAmbainis


