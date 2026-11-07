-- Prove2me | Definitions.Def_AaronsonAmbainis_Row_Extension
-- name    : AaronsonAmbainis_Row_Extension
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:55:32.138408+00:00
-- url     : https://prove2.me/theorems/26ce5915-0e4a-4260-b702-d25197c72a24
-- title:
--   Extension
-- statement:
--   Definitions and structural lemmas for Extension, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Extension.lean

import Definitions.Def_AaronsonAmbainis_Row_Chi
set_option autoImplicit true
namespace AaronsonAmbainis
namespace Row
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def weight (u : ι → ℝ) (z : Cube ι) : ℝ := ∏ i, (1 + sgn (z i) * u i) / 2
end Row
end AaronsonAmbainis


