-- Prove2me | Definitions.Def_Tablet_ThetaL
-- name    : Tablet_ThetaL
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:48:49.549192+00:00
-- url     : https://prove2.me/theorems/b4159375-f855-4681-9c9a-79a93883d6bd
-- title:
--   Theta L
-- statement:
--   Definitions and structural lemmas for Theta L, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ThetaL.lean

import Definitions.Def_Tablet_massOfFunctional
import Definitions.Def_Tablet_curveCurrent
set_option autoImplicit false
open ENNReal
def ThetaL {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E] (l : ℕ) :
    Set (Curve E) :=
-- BODY
  { γ | massOfFunctional (curveCurrent γ) = (l : ℝ≥0∞) }


