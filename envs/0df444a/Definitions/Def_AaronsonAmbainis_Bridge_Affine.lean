-- Prove2me | Definitions.Def_AaronsonAmbainis_Bridge_Affine
-- name    : AaronsonAmbainis_Bridge_Affine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:49:44.187365+00:00
-- url     : https://prove2.me/theorems/c574aac8-c2c4-4631-9ab4-fb77514bb2db
-- title:
--   Affine
-- statement:
--   Definitions and structural lemmas for Affine, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Affine.lean

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
set_option autoImplicit true
namespace AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end AaronsonAmbainis.Bridge


