-- Prove2me | Definitions.Def_AaronsonAmbainis_Average_Coordinate
-- name    : AaronsonAmbainis_Average_Coordinate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:34:40.31851+00:00
-- url     : https://prove2.me/theorems/0bee1e96-550c-4b4d-8323-02f440653ea1
-- title:
--   Coordinate
-- statement:
--   Definitions and structural lemmas for Coordinate, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Coordinate.lean

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
set_option autoImplicit true
namespace AaronsonAmbainis
namespace Average
open Finset
section NoFintype
variable {ι : Type*} [DecidableEq ι]
end NoFintype
variable {ι : Type} [Fintype ι] [DecidableEq ι]
noncomputable def avg (j : ι) (f : Cube ι → ℝ) : Cube ι → ℝ :=
  fun x => (f x + f (flipSet x {j})) / 2
end Average
end AaronsonAmbainis


