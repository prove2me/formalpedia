-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EvenPowerSeries_WqEven
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EvenPowerSeries_WqEven
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:27:50.33373+00:00
-- url     : https://prove2.me/theorems/ea943949-96f3-4f24-9672-4be526b922cb
-- title:
--   Wq Even
-- statement:
--   Definitions and structural lemmas for Wq Even, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EvenPowerSeries/WqEven.lean

import Definitions.Def_Formalism_PeriodIntegrals_PhEven
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.PhEven.ParB
open PI.AddIntG
section Field
variable {K : Type*} [Field K]
def nu (K : Type*) [Field K] : PowerSeries K →+* PowerSeries K := PowerSeries.rescale (-1 : K)
end Field
variable {p : ℕ} [Fact p.Prime]
end PI.PhEven.ParB
namespace PI.PhEven
end PI.PhEven
end


