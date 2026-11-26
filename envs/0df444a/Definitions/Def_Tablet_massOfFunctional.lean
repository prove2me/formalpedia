-- Prove2me | Definitions.Def_Tablet_massOfFunctional
-- name    : Tablet_massOfFunctional
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:48:19.118519+00:00
-- url     : https://prove2.me/theorems/6af1b136-55e7-5fbb-b0de-baecd6da42bc
-- title:
--   mass Of Functional
-- statement:
--   Definitions and structural lemmas for mass Of Functional, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/massOfFunctional.lean

import Definitions.Def_Tablet_IsAdmissible
set_option autoImplicit false
open MeasureTheory ENNReal
noncomputable def massOfFunctional {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : Form1 E → ℝ) : ℝ≥0∞ :=
-- BODY
  ⨅ μ : { μ : Measure E // IsAdmissible T μ }, (μ.1 Set.univ)


