-- Prove2me | Definitions.Def_Tablet_IsPiecewiseGeodesicWith
-- name    : Tablet_IsPiecewiseGeodesicWith
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:55:16.65446+00:00
-- url     : https://prove2.me/theorems/f48aeb8f-b9e8-4201-8997-1eaa73957738
-- title:
--   Is Piecewise Geodesic With
-- statement:
--   Definitions and structural lemmas for Is Piecewise Geodesic With, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/IsPiecewiseGeodesicWith.lean

import Definitions.Def_Tablet_IsGeodesicResolution
set_option autoImplicit false
def IsPiecewiseGeodesicWith {E : Type*} [MetricSpace E] (γ : Curve E) (k : ℕ) : Prop :=
-- BODY
  ∃ s : ℕ → ℝ, IsGeodesicResolution γ k s


