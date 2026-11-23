-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_WfRing
-- name    : Formalism_PeriodIntegrals_WfRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:21.220657+00:00
-- url     : https://prove2.me/theorems/bf397913-36a3-4ad3-8e42-336471ef9cf6
-- title:
--   Wf Ring
-- statement:
--   Definitions and structural lemmas for Wf Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/WfRing.lean

import Definitions.Def_Formalism_PeriodIntegrals_ExpIntW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI
def WfRing : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f g : MvPowerSeries σ ℂ_[p]), CoefWf f → CoefWf g →
    CoefWf (f + g) ∧ CoefWf (f - g) ∧ CoefWf (f * g) ∧ ∀ c : ℂ_[p], InWf c → CoefWf (MvPowerSeries.C c * f)
end PI


