-- Prove2me | solution 1 for Auto.aux_orbit_add_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:55:04.602311+00:00
-- url     : https://prove2.me/submissions/6ed818d3-8f93-42f2-bb60-226e61706fca

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_orbit_add
public import Theorems.Thm_Auto_aux_orbit_coordinate

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace Auto
theorem _root_.solution {X : Type*} {n : ℕ}
    (S : Fin n → X → X) (hS : ∀ i j, Function.Commute (S i) (S j))
    (k : Fin n → ℕ) (i : Fin n) (m : ℕ) :
    aux_orbit S (k + aux_coordinate i m) = aux_orbit S k ∘ (S i)^[m] := by
  rw [aux_orbit_add S hS, aux_orbit_coordinate]
end Auto
