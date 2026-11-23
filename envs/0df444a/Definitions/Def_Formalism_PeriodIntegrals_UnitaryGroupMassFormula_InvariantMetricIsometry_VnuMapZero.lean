-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_VnuMapZero
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_VnuMapZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:45:19.247701+00:00
-- url     : https://prove2.me/theorems/1bfb79de-c879-4bcc-a5bb-34cf1eab6ce6
-- title:
--   Vnu Map Zero
-- statement:
--   Definitions and structural lemmas for Vnu Map Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/VnuMapZero.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_OeEqOfRangeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical
namespace PI.IsoInvMetricW
open PI.IsoInvMetric
section
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {nu : Lt → YoungDiagram}
end
end PI.IsoInvMetricW


