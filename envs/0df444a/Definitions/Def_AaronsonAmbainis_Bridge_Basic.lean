-- Prove2me | Definitions.Def_AaronsonAmbainis_Bridge_Basic
-- name    : AaronsonAmbainis_Bridge_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:46:06.384112+00:00
-- url     : https://prove2.me/theorems/45d7ac2b-d3f2-4228-9047-649d2ce5c1a0
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean

import Definitions.Def_AaronsonAmbainis_Statements
set_option autoImplicit true
namespace AaronsonAmbainis.Bridge
open Finset
section NoFintype
variable {ι : Type*} [DecidableEq ι]
end NoFintype
section DictPlain
variable {ι : Type*}
noncomputable def dict (j : ι) : Cube ι → ℝ := fun x => if x j then -1 else 1
end DictPlain
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end AaronsonAmbainis.Bridge


