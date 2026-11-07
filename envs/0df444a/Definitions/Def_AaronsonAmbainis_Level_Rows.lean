-- Prove2me | Definitions.Def_AaronsonAmbainis_Level_Rows
-- name    : AaronsonAmbainis_Level_Rows
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:31:27.64225+00:00
-- url     : https://prove2.me/theorems/cbe14be7-49b3-4011-af88-4ba66eee2912
-- title:
--   Rows
-- statement:
--   Definitions and structural lemmas for Rows, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Rows.lean

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
set_option autoImplicit true
namespace AaronsonAmbainis
namespace Level
open Finset
noncomputable def lev {ι : Type*} (f : Cube ι → ℝ) (t : ℝ) : Cube ι → Bool :=
  fun x => decide (t < f x)
noncomputable def levRow {ι : Type*} (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ) (t : ℝ) :
    Cube ι → ι → ℝ :=
  fun x j => if f x = t then 1 else a x j / |f x - t|
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end Level
end AaronsonAmbainis


