-- Prove2me | Definitions.Def_Tablet_CurrentContinuousF
-- name    : Tablet_CurrentContinuousF
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:54:05.621175+00:00
-- url     : https://prove2.me/theorems/c0c1455d-e460-41b2-b82a-93922ad6d4b5
-- title:
--   Current Continuous F
-- statement:
--   Definitions and structural lemmas for Current Continuous F, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurrentContinuousF.lean

import Definitions.Def_Tablet_MetricCurrent1
set_option autoImplicit false
open Set Filter Finset MeasureTheory ENNReal
open scoped NNReal


