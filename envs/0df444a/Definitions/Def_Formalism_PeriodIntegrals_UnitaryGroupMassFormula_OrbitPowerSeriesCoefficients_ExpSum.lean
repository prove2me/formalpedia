-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_ExpSum
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_ExpSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:39.020319+00:00
-- url     : https://prove2.me/theorems/dfcca104-07bf-4243-b194-ed3af2871c47
-- title:
--   Exp Sum
-- statement:
--   Definitions and structural lemmas for Exp Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/ExpSum.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
namespace PI.OrbShared.ExpSum
open MvPowerSeries
variable {K : Type*} [Field K] [CharZero K]
abbrev eS {τ : Type*} (f : MvPowerSeries τ K) : MvPowerSeries τ K :=
  PowerSeries.subst f (PowerSeries.exp K)
variable {τ υ : Type*}
end PI.OrbShared.ExpSum
end


