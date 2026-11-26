-- Prove2me | solution 1 for Auto.aux_overlapWidth_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:47:37.861623+00:00
-- url     : https://prove2.me/submissions/a1e0562d-2e38-4e5c-8e53-4ced6a5518a4

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_overlapLower_eq_add_overlapLower_zero
public import Theorems.Thm_Auto_aux_overlapUpper_eq_add_overlapUpper_zero

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace Auto
theorem _root_.solution {n : ℕ} (hn : 0 < n)
    (ε δ : ℝ) (u : aux_RVector n) (m : ℕ) :
    aux_overlapUpper hn ε δ u m - aux_overlapLower hn ε u m =
      aux_overlapUpper hn ε δ u 0 - aux_overlapLower hn ε u 0 := by
  rw [aux_overlapUpper_eq_add_overlapUpper_zero,
    aux_overlapLower_eq_add_overlapLower_zero]
  ring
end Auto
