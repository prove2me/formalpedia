-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_ExpLog
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_ExpLog
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:43:44.224022+00:00
-- url     : https://prove2.me/theorems/b32636d5-d48d-4f05-bfc3-51f5a980acb0
-- title:
--   Exp Log
-- statement:
--   Definitions and structural lemmas for Exp Log, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupCommon/ExpLog.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.FglShared
open MvPowerSeries
section Field
variable {K : Type} [Field K] [CharZero K]
end Field
section Padic
variable {p : ℕ} [Fact p.Prime]
def logS {σ : Type} (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    if n = 0 then 0 else (-1 : ℂ_[p]) ^ (n + 1) * MvPowerSeries.coeff α ((F - 1) ^ n) / (n : ℂ_[p])
end Padic
end PI.FglShared
end


