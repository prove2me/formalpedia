-- Prove2me | Definitions.Def_AaronsonAmbainis_Level_Integral
-- name    : AaronsonAmbainis_Level_Integral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:17:35.4452+00:00
-- url     : https://prove2.me/theorems/f75be3c3-4398-4e7d-8c2e-07ab0e23eba8
-- title:
--   Integral
-- statement:
--   Definitions and structural lemmas for Integral, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Integral.lean

import Mathlib
set_option autoImplicit true
namespace AaronsonAmbainis
namespace Level
open Finset
noncomputable def stp (c t : ℝ) : ℝ := if c ≤ t then 1 else 0
end Level
end AaronsonAmbainis


