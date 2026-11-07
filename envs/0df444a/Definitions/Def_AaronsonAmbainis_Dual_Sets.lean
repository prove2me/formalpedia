-- Prove2me | Definitions.Def_AaronsonAmbainis_Dual_Sets
-- name    : AaronsonAmbainis_Dual_Sets
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:40:27.191207+00:00
-- url     : https://prove2.me/theorems/5e827f77-09d8-4d6d-9c2d-c5cfd70d32e3
-- title:
--   Sets
-- statement:
--   Definitions and structural lemmas for Sets, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sets.lean

import Definitions.Def_AaronsonAmbainis_RowDefs
set_option autoImplicit true
namespace AaronsonAmbainis
namespace Dual
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def massSet (ι : Type*) [Fintype ι] (K : ℝ) : Set (ι → ℝ) :=
  {a | (∀ i, 0 ≤ a i) ∧ ∑ i, a i ≤ K}
def slack (t : Finset ι → ℝ) (a : ι → ℝ) : Finset ι → ℝ :=
  fun S => ∑ i ∈ S, a i - t S
def orthant (ι : Type*) : Set (Finset ι → ℝ) := {v | ∀ S, 0 ≤ v S}
end Dual
end AaronsonAmbainis


