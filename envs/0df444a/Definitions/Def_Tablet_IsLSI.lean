-- Prove2me | Definitions.Def_Tablet_IsLSI
-- name    : Tablet_IsLSI
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:00:59.471304+00:00
-- url     : https://prove2.me/theorems/659147d3-67db-4962-ac6f-3902b39e6d1f
-- title:
--   Is LSI
-- statement:
--   Definitions and structural lemmas for Is LSI, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/IsLSI.lean

import Definitions.Def_Tablet_dGamma
import Definitions.Def_Tablet_IsPiecewiseGeodesic
set_option autoImplicit false
open Set
def IsLSI {E : Type*} [MetricSpace E] (γ : Curve E) (δ ε : ℝ) : Prop :=
-- BODY
  IsPiecewiseGeodesic γ ∧
    ∀ s ∈ Set.Icc (0 : ℝ) γ.len, ∀ t ∈ Set.Icc (0 : ℝ) γ.len,
      δ ≤ dGamma γ s t → ε * dGamma γ s t ≤ dist (γ.toFun s) (γ.toFun t)


