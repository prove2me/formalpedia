-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_OfRealCoordsSmulCenterCoord
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_OfRealCoordsSmulCenterCoord
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T08:08:58.579793+00:00
-- url     : https://prove2.me/theorems/111a70e6-75c6-5f26-ad02-ed6683008fcd
-- title:
--   Of Real Coords Smul Center Coord
-- statement:
--   Definitions and structural lemmas for Of Real Coords Smul Center Coord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/OfRealCoordsSmulCenterCoord.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
namespace PI.ExistsGaugeMeasureForEachRank.W
variable {r : ℕ}
def dz (r : ℕ) (z : ℂ) : Mat 0 r := diagonal (Pi.single (cI r) z)
def v0 (r : ℕ) : EuclideanSpace ℝ (Fin (2 * r + 0 + 1) × Fin (2 * r + 0 + 1) × Bool) :=
  EuclideanSpace.single (cI r, cI r, true) 1
end PI.ExistsGaugeMeasureForEachRank.W


