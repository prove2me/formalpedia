-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
-- name    : CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T15:13:48.432967+00:00
-- url     : https://prove2.me/theorems/a7ec5dcc-88ec-4aca-b73a-44d76a3960ac
-- title:
--   Ph Meas
-- statement:
--   Definitions and structural lemmas for Ph Meas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/PhMeas.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhMeasCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_ExpIntertwine
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set
noncomputable section
namespace CompanionTheory.D.Upq.Sm
open PI.PhMeasCore
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
end CompanionTheory.D.Upq.Sm
end


