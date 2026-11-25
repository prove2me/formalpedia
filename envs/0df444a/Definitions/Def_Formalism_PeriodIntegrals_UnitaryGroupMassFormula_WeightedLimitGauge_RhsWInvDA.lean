-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvDA
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvDA
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T08:54:15.067475+00:00
-- url     : https://prove2.me/theorems/17456b12-4689-55a1-aabd-b65a4f56abc7
-- title:
--   Rhs WInv DA
-- statement:
--   Definitions and structural lemmas for Rhs WInv DA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/RhsWInvDA.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvR
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
open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal
namespace PI.RhsWLim.W.RI
section Abstract
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable {X : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
def iotaQ (H : Subgroup G) (p : G → X) (q : G ⧸ H) : X := p q.out
end Abstract
end PI.RhsWLim.W.RI


