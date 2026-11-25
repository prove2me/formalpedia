-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_ContinuousLmulM
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_ContinuousLmulM
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T08:18:19.79304+00:00
-- url     : https://prove2.me/theorems/dc0805f1-4f95-568e-8ed9-a9fab0abbbca
-- title:
--   Continuous Lmul M
-- statement:
--   Definitions and structural lemmas for Continuous Lmul M, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/ContinuousLmulM.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_OfRealCoordsSmulCenterCoord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Filter Topology Set Real
open scoped ENNReal
namespace PI.ExistsGaugeMeasureForEachRank.W
variable {r : ℕ}
instance fact_two_pi : Fact (0 < 2 * π) := ⟨by positivity⟩
def Gm (r : ℕ) (θ : AddCircle (2 * π)) : Mt 0 r :=
  fun i j => dgl r ((AddCircle.toCircle θ : Circle) : ℂ) i j
def μG (r : ℕ) : Measure (Mt 0 r) := Measure.map (Gm r) volume
end PI.ExistsGaugeMeasureForEachRank.W


