-- Prove2me | Definitions.Def_AaronsonAmbainis_Row_Chi
-- name    : AaronsonAmbainis_Row_Chi
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:53:48.795908+00:00
-- url     : https://prove2.me/theorems/3266225e-2883-47d6-ba22-91a05e083db6
-- title:
--   Chi
-- statement:
--   Definitions and structural lemmas for Chi, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Chi.lean

import Definitions.Def_AaronsonAmbainis_RowDefs
set_option autoImplicit true
namespace AaronsonAmbainis
namespace Row
open Finset
noncomputable def sgn (b : Bool) : ℝ := if b then -1 else 1
def zero (β : Type*) : Cube β := fun _ => false
def unit {β : Type*} [DecidableEq β] (b : β) : Cube β := fun b' => decide (b' = b)
variable {ι : Type*}
end Row
end AaronsonAmbainis


