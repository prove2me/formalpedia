-- Prove2me | Definitions.Def_Tablet_Form1
-- name    : Tablet_Form1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:47:26.831129+00:00
-- url     : https://prove2.me/theorems/8ed514c8-7809-5c8c-91bd-ae99bba0b2e9
-- title:
--   Form1
-- statement:
--   Definitions and structural lemmas for Form1, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/Form1.lean

import Definitions.Def_Tablet_Preamble
set_option autoImplicit false
open scoped NNReal
structure Form1 (E : Type*) [MetricSpace E] where
-- BODY
  f : E → ℝ
  fBound : ℝ≥0
  f_bounded : ∀ x : E, |f x| ≤ (fBound : ℝ)
  fLip : ℝ≥0
  f_lipschitz : LipschitzWith fLip f
  pi : E → ℝ
  piLip : ℝ≥0
  pi_lipschitz : LipschitzWith piLip pi


