-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T08:00:01.311804+00:00
-- url     : https://prove2.me/theorems/21b2c615-11bf-4df0-a166-334cbebdeffb
-- title:
--   Dgl Apply Off
-- statement:
--   Definitions and structural lemmas for Dgl Apply Off, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/DglApplyOff.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace PI.ExistsGaugeMeasureForEachRank.W
variable {r : ℕ}
def cI (r : ℕ) : Fin (2 * r + 0 + 1) := ⟨r, by omega⟩
def dgl (r : ℕ) (u : ℂ) : Mat 0 r := diagonal (fun i => if i = cI r then u else 1)
end PI.ExistsGaugeMeasureForEachRank.W


