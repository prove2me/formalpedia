-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HyperboloidChartMeasureFormula
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_HyperboloidChartMeasureFormula
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T08:45:12.85954+00:00
-- url     : https://prove2.me/theorems/e74827f6-2e43-5914-91f5-8b654927a3b9
-- title:
--   Hyperboloid Chart Measure Formula
-- statement:
--   Definitions and structural lemmas for Hyperboloid Chart Measure Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HyperboloidChartMeasureFormula.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushQ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
namespace GlobalTheory.HypChartPf
open PI.RhsWLim PI.RhsWLim.W
def sgn (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if r ≤ i.val ∧ i.val < r + k then 1 else if i.val = r + k then -1 else 0
end GlobalTheory.HypChartPf


