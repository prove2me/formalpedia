-- Prove2me | Definitions.Def_Tablet_PaoliniStepanovExists
-- name    : Tablet_PaoliniStepanovExists
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:50:26.734185+00:00
-- url     : https://prove2.me/theorems/e1697944-4dce-4955-bf19-c1135eb3e363
-- title:
--   Paolini Stepanov Exists
-- statement:
--   Definitions and structural lemmas for Paolini Stepanov Exists, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/PaoliniStepanovExists.lean

import Definitions.Def_Tablet_MetricCurrent1
import Definitions.Def_Tablet_BoundaryZero
import Definitions.Def_Tablet_PSFamily
set_option autoImplicit false
open MeasureTheory ENNReal
def PaoliniStepanovExistsStatement (E : Type*) [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] : Prop :=
  ∀ (T : MetricCurrent1 E), T.toFun ≠ 0 → BoundaryZero T.toFun →
    ∃ F : PSFamily T.toFun, F.massMeasure Set.univ = massOfFunctional T.toFun


