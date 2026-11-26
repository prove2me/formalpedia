-- Prove2me | Definitions.Def_Tablet_BoundaryZero
-- name    : Tablet_BoundaryZero
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:47:53.274879+00:00
-- url     : https://prove2.me/theorems/0b94c447-9de5-41b9-808e-29cd1479fa48
-- title:
--   Boundary Zero
-- statement:
--   Definitions and structural lemmas for Boundary Zero, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BoundaryZero.lean

import Definitions.Def_Tablet_Form1
set_option autoImplicit false
open scoped NNReal
def BoundaryZero {E : Type*} [MetricSpace E] (T : Form1 E → ℝ) : Prop :=
-- BODY
  ∀ (f : E → ℝ) (b : ℝ≥0) (_hb : ∀ x, |f x| ≤ (b : ℝ)) (L : ℝ≥0) (hL : LipschitzWith L f),
    T ⟨fun _ => (1 : ℝ), 1, fun x => by simp, 0,
        by simp [LipschitzWith.const (α := E) (1 : ℝ)], f, L, hL⟩ = 0


