-- Prove2me | Definitions.Def_Tablet_MassSupFormula
-- name    : Tablet_MassSupFormula
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:49:22.989394+00:00
-- url     : https://prove2.me/theorems/b924579c-a603-505a-b740-04f5c8542ed3
-- title:
--   Mass Sup Formula
-- statement:
--   Definitions and structural lemmas for Mass Sup Formula, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/MassSupFormula.lean

import Definitions.Def_Tablet_MetricCurrent1
set_option autoImplicit false
open MeasureTheory ENNReal
def MassSupFormulaStatement (E : Type*) [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] : Prop :=
  ∀ (T : MetricCurrent1 E) (c : ℝ), 0 ≤ c →
    (∀ (n : ℕ) (ω : Fin n → Form1 E),
      (∀ p, (ω p).piLip ≤ 1) →
      (∀ x : E, ∑ p, |(ω p).f x| ≤ 1) →
      ∑ p, |T.toFun (ω p)| ≤ c) →
    massOfFunctional T.toFun ≤ ENNReal.ofReal c


