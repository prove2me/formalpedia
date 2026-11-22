-- Prove2me | Definitions.Def_Autoconvolutions_Occupancy
-- name    : Autoconvolutions_Occupancy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:47:46.289654+00:00
-- url     : https://prove2.me/theorems/cbb92696-58f2-4b4a-83ae-6b312593ba33
-- title:
--   Occupancy
-- statement:
--   Definitions and structural lemmas for Occupancy, from Vjekoslav Kovač's pinned Sharpness for autoconvolutions development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Occupancy.lean

module
public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Powerset
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace Autoconvolutions.Blocks
variable {ι : Type*} [DecidableEq ι]
def indicatorVector : Finset ι ↪ (ι → ℕ) where
  toFun T i := if i ∈ T then 1 else 0
  inj' := by
    intro T U h
    ext i
    have e := congrFun h i
    by_cases hT : i ∈ T <;> by_cases hU : i ∈ U <;> simp_all
def goodVectors (I : Finset ι) (k : ℕ) : Finset (ι → ℕ) :=
  (I.powersetCard k).map indicatorVector
end Autoconvolutions.Blocks


