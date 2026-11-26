-- Prove2me | Definitions.Def_Tablet_dGamma
-- name    : Tablet_dGamma
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:59:49.318308+00:00
-- url     : https://prove2.me/theorems/71883bdb-3ca3-5aeb-8f0d-3cf99fe21cc1
-- title:
--   d Gamma
-- statement:
--   Definitions and structural lemmas for d Gamma, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/dGamma.lean

import Definitions.Def_Tablet_Curve
import Definitions.Def_Tablet_IsClosedCurve
set_option autoImplicit false
open Classical
noncomputable def dGamma {E : Type*} [MetricSpace E] (γ : Curve E) (t t' : ℝ) : ℝ :=
-- BODY
  if IsClosedCurve γ then min |t - t'| (γ.len - |t - t'|) else |t - t'|


