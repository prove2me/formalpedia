-- Prove2me | Definitions.Def_Tablet_IsGeodesicOn
-- name    : Tablet_IsGeodesicOn
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:47:47.924179+00:00
-- url     : https://prove2.me/theorems/d7c0dcba-304a-4b8c-a419-93cfde540f87
-- title:
--   Is Geodesic On
-- statement:
--   Definitions and structural lemmas for Is Geodesic On, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/IsGeodesicOn.lean

import Definitions.Def_Tablet_Curve
set_option autoImplicit false
open Set
def IsGeodesicOn {E : Type*} [MetricSpace E] (γ : Curve E) (a b : ℝ) : Prop :=
-- BODY
  ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, dist (γ.toFun s) (γ.toFun t) = |s - t|


