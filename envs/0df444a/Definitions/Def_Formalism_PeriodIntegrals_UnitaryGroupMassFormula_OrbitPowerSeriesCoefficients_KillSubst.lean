-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_KillSubst
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_KillSubst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:50.431606+00:00
-- url     : https://prove2.me/theorems/b13bfdb2-e156-4e8b-a425-691614ef00b2
-- title:
--   Kill Subst
-- statement:
--   Definitions and structural lemmas for Kill Subst, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/KillSubst.lean

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
namespace PI.OrbShared
open MvPowerSeries
open scoped MvPowerSeries.WithPiTopology
variable {σ τ υ R : Type*} [CommRing R]
end PI.OrbShared


