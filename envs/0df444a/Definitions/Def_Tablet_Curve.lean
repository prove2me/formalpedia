-- Prove2me | Definitions.Def_Tablet_Curve
-- name    : Tablet_Curve
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:47:27.683449+00:00
-- url     : https://prove2.me/theorems/42ff45e2-69da-54b5-b178-cf1a35eb42c7
-- title:
--   Curve
-- statement:
--   Definitions and structural lemmas for Curve, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/Curve.lean

import Definitions.Def_Tablet_Preamble
set_option autoImplicit false
open MeasureTheory Set
structure Curve (E : Type*) [MetricSpace E] where
-- BODY
  len : ℝ
  len_nonneg : 0 ≤ len
  toFun : ℝ → E
  clamped : ∀ t : ℝ, toFun t = toFun (min len (max 0 t))
  unitSpeed : HasUnitSpeedOn toFun (Set.Icc 0 len)


