-- Prove2me | Definitions.Def_Tablet_IsPiecewiseGeodesic
-- name    : Tablet_IsPiecewiseGeodesic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:55:44.774447+00:00
-- url     : https://prove2.me/theorems/7804ae87-bf78-5ede-b556-e07d7310ebea
-- title:
--   Is Piecewise Geodesic
-- statement:
--   Definitions and structural lemmas for Is Piecewise Geodesic, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/IsPiecewiseGeodesic.lean

import Definitions.Def_Tablet_IsPiecewiseGeodesicWith
set_option autoImplicit false
def IsPiecewiseGeodesic {E : Type*} [MetricSpace E] (γ : Curve E) : Prop :=
-- BODY
  ∃ k : ℕ, IsPiecewiseGeodesicWith γ k


