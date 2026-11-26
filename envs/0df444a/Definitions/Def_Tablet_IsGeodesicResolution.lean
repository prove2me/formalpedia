-- Prove2me | Definitions.Def_Tablet_IsGeodesicResolution
-- name    : Tablet_IsGeodesicResolution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:48:12.559487+00:00
-- url     : https://prove2.me/theorems/0a984436-8835-5d1f-b366-7aebde27fd9b
-- title:
--   Is Geodesic Resolution
-- statement:
--   Definitions and structural lemmas for Is Geodesic Resolution, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/IsGeodesicResolution.lean

import Definitions.Def_Tablet_IsGeodesicOn
set_option autoImplicit false
open Set
def IsGeodesicResolution {E : Type*} [MetricSpace E] (γ : Curve E) (k : ℕ) (s : ℕ → ℝ) : Prop :=
-- BODY
  MonotoneOn s (Set.Icc 0 k) ∧ s 0 = 0 ∧ s k = γ.len ∧
    ∀ i < k, IsGeodesicOn γ (s i) (s (i + 1))


