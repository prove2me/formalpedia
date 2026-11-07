-- Prove2me | Definitions.Def_AaronsonAmbainis_TwoSided_Basic
-- name    : AaronsonAmbainis_TwoSided_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:21:33.707318+00:00
-- url     : https://prove2.me/theorems/e7867c92-dbe5-44bc-b4a9-9d65f6a1bb14
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Basic.lean

import Definitions.Def_AaronsonAmbainis_AllPairsDefs
set_option autoImplicit true
namespace AaronsonAmbainis
open Finset
section NoFintype
variable {ι : Type*} [DecidableEq ι]
end NoFintype
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end AaronsonAmbainis


