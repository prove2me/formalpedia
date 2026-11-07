-- Prove2me | Definitions.Def_AaronsonAmbainis_TwoSided_AllPairsCore
-- name    : AaronsonAmbainis_TwoSided_AllPairsCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:28:23.174401+00:00
-- url     : https://prove2.me/theorems/2c33d539-3201-444e-b56f-a97539f2c7c4
-- title:
--   All Pairs Core
-- statement:
--   Definitions and structural lemmas for All Pairs Core, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/AllPairsCore.lean

import Definitions.Def_AaronsonAmbainis_TwoSided_Glue
set_option autoImplicit true
namespace AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def allPairsTerm (g : Cube ι → Bool) (w : ι → ℝ) (lam : Cube ι → ι → ℝ)
    (F : Finset ι) (x : Cube ι) : ℝ :=
  if g x = true ∧ g (flipSet x F) = false then
    (∑ j ∈ F, w j * lam x j * lam (flipSet x F) j)⁻¹ else 0
end AaronsonAmbainis


