-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialFactorIdentity_ExpMvEq
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialFactorIdentity_ExpMvEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:32.658736+00:00
-- url     : https://prove2.me/theorems/932d680c-af35-49c7-a1c7-e0a3e0caa255
-- title:
--   Exp Mv Eq
-- statement:
--   Definitions and structural lemmas for Exp Mv Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialFactorIdentity/ExpMvEq.lean

import Definitions.Def_Formalism_PeriodIntegrals_PhiCubeOfFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_CoeffSingleLg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.PhiCubeOfFactor.Wk
open PI.PhiCubeOfFactor MvPowerSeries PI.FglShared
variable {p : ℕ} [Fact p.Prime]
def uS (E : PowerSeries ℂ_[p]) (x : MvPowerSeries (Fin 2) ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] :=
  PowerSeries.subst x (logMv E)
end PI.PhiCubeOfFactor.Wk
end


