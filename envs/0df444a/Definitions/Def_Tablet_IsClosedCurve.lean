-- Prove2me | Definitions.Def_Tablet_IsClosedCurve
-- name    : Tablet_IsClosedCurve
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:57:03.480411+00:00
-- url     : https://prove2.me/theorems/fdd40d69-c04f-5165-b079-8bde4f5ee61b
-- title:
--   Is Closed Curve
-- statement:
--   Definitions and structural lemmas for Is Closed Curve, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/IsClosedCurve.lean

import Definitions.Def_Tablet_Curve
set_option autoImplicit false
def IsClosedCurve {E : Type*} [MetricSpace E] (γ : Curve E) : Prop :=
-- BODY
  γ.toFun γ.len = γ.toFun 0


