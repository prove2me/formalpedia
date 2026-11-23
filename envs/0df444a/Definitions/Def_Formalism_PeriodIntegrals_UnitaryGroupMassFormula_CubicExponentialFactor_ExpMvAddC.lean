-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubicExponentialFactor_ExpMvAddC
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubicExponentialFactor_ExpMvAddC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:37.285088+00:00
-- url     : https://prove2.me/theorems/d258d0e3-be30-41bd-90fc-c7570799ffe1
-- title:
--   Exp Mv Add C
-- statement:
--   Definitions and structural lemmas for Exp Mv Add C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubicExponentialFactor/ExpMvAddC.lean

import Definitions.Def_Formalism_PeriodIntegrals_CubicExponentialFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_CoeffSingleLg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubicExponentialFactor_NormAddLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.CubicExponentialFactor.Wk
open PI.CubicExponentialFactor MvPowerSeries PI.FglShared
set_option linter.unusedSimpArgs false
variable {p : ℕ} [Fact p.Prime]
def uS (E : PowerSeries ℂ_[p]) (x : MvPowerSeries (Fin 3) ℂ_[p]) : MvPowerSeries (Fin 3) ℂ_[p] :=
  PowerSeries.subst x (logMv E)
end PI.CubicExponentialFactor.Wk
end


