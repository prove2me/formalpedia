-- Prove2me | Definitions.Def_MetricSurgery_Solution
-- name    : MetricSurgery_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:54:10.799343+00:00
-- url     : https://prove2.me/theorems/0f888200-daee-54e2-8278-93ac9531378d
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Solution.lean

import Definitions.Def_Tablet_ApproximationMetric
import Definitions.Def_Tablet_BBAssertion
import Definitions.Def_Tablet_SurgeryEta
import Definitions.Def_Tablet_C1SmallBall
import Definitions.Def_Tablet_EtaRepeats
import Theorems.Thm_ApproximationMetric
import Theorems.Thm_BBAssertion
import Theorems.Thm_C1SmallBall
import Theorems.Thm_EtaRepeats
import Theorems.Thm_SurgeryEta

set_option autoImplicit false
open Set Filter Finset MeasureTheory ENNReal
namespace AtomicDecomposition
end AtomicDecomposition


