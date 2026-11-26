-- Prove2me | solution 1 for Auto.aux_overlapWidth_eq_translate_width
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:48:36.279723+00:00
-- url     : https://prove2.me/submissions/70c27da5-5424-48ed-99d7-bf27b55d9f24

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_overlapWidth_invariant

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
    aux_overlapWidth hn ε δ u =
      aux_overlapUpper hn ε δ u m - aux_overlapLower hn ε u m := by
  symm
  exact aux_overlapWidth_invariant hn ε δ u m
end Auto
