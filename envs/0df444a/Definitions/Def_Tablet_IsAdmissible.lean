-- Prove2me | Definitions.Def_Tablet_IsAdmissible
-- name    : Tablet_IsAdmissible
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:47:51.028186+00:00
-- url     : https://prove2.me/theorems/5fcafef9-75d0-4980-a912-2e8b97923797
-- title:
--   Is Admissible
-- statement:
--   Definitions and structural lemmas for Is Admissible, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/IsAdmissible.lean

import Definitions.Def_Tablet_Form1
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
set_option autoImplicit false
open MeasureTheory ENNReal
def IsAdmissible {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : Form1 E → ℝ) (μ : Measure E) : Prop :=
-- BODY
  IsFiniteMeasure μ ∧
    ∀ ω : Form1 E, ENNReal.ofReal |T ω| ≤ (ω.piLip : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal |ω.f x| ∂μ


