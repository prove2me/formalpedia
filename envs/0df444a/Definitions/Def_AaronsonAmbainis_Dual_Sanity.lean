-- Prove2me | Definitions.Def_AaronsonAmbainis_Dual_Sanity
-- name    : AaronsonAmbainis_Dual_Sanity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:04:08.803548+00:00
-- url     : https://prove2.me/theorems/ce3a199d-8bc5-485c-95b7-271f39aec8f2
-- title:
--   Sanity
-- statement:
--   Definitions and structural lemmas for Sanity, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sanity.lean

import Definitions.Def_AaronsonAmbainis_Dual_Cover
import Definitions.Def_AaronsonAmbainis_Dual_RowAux
import Definitions.Def_AaronsonAmbainis_MainTheorem
set_option autoImplicit true
namespace AaronsonAmbainis
namespace Dual
open Finset
section Weak
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end Weak
end Dual
end AaronsonAmbainis


