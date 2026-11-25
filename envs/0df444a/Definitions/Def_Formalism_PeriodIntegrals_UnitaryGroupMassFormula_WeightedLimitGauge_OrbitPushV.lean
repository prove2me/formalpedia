-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushV
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushV
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T09:00:15.915501+00:00
-- url     : https://prove2.me/theorems/62668e1f-1d1a-4277-ac1d-744982edd797
-- title:
--   Orbit Push V
-- statement:
--   Definitions and structural lemmas for Orbit Push V, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushV.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
namespace PI.RhsWLim.W
open PI.RhsWLim
variable {k : ℕ}
def tau (k : ℕ) (T' : ℝ) (p : (Fin k → ℂ) × ℂ) : ℝ := Real.sqrt (-qf k p / T')
def phiR (a T' t : ℝ) : ℝ := Real.sqrt (a + t ^ 2 * T')
end PI.RhsWLim.W


