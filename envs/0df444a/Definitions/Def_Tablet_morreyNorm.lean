-- Prove2me | Definitions.Def_Tablet_morreyNorm
-- name    : Tablet_morreyNorm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:58:20.208642+00:00
-- url     : https://prove2.me/theorems/7d8e70ee-2eab-59d8-bb90-5e617e20785d
-- title:
--   morrey Norm
-- statement:
--   Definitions and structural lemmas for morrey Norm, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/morreyNorm.lean

import Definitions.Def_Tablet_Preamble
set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable def morreyNorm {E : Type*} [MetricSpace E] [MeasurableSpace E]
    (μ : Measure E) : ℝ≥0∞ :=
-- BODY
  ⨆ x : E, ⨆ r : ℝ, ⨆ _ : 0 < r, μ (Metric.closedBall x r) / ENNReal.ofReal r


