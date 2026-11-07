-- Prove2me | Definitions.Def_AaronsonAmbainis_Dual_Functional
-- name    : AaronsonAmbainis_Dual_Functional
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:40:03.729256+00:00
-- url     : https://prove2.me/theorems/d62f621b-63b0-4cd6-ab45-adaf21774ea5
-- title:
--   Functional
-- statement:
--   Definitions and structural lemmas for Functional, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Functional.lean

import Definitions.Def_AaronsonAmbainis_RowDefs
set_option autoImplicit true
namespace AaronsonAmbainis
namespace Dual
open Finset
variable {β : Type*} [Fintype β] [DecidableEq β]
end Dual
end AaronsonAmbainis


