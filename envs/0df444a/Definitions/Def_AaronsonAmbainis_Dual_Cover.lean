-- Prove2me | Definitions.Def_AaronsonAmbainis_Dual_Cover
-- name    : AaronsonAmbainis_Dual_Cover
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:41:32.736272+00:00
-- url     : https://prove2.me/theorems/0f987bee-c71b-4956-8d4f-028bd60194cc
-- title:
--   Cover
-- statement:
--   Definitions and structural lemmas for Cover, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Cover.lean

import Definitions.Def_AaronsonAmbainis_Dual_Sets
import Definitions.Def_AaronsonAmbainis_Dual_Functional
import Definitions.Def_AaronsonAmbainis_Dual_Core
set_option autoImplicit true
namespace AaronsonAmbainis
open Finset
namespace Dual
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end Dual
end AaronsonAmbainis


