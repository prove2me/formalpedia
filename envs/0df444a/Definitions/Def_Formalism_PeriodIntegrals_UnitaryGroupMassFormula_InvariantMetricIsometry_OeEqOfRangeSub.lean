-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_OeEqOfRangeSub
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_OeEqOfRangeSub
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:43:07.4184+00:00
-- url     : https://prove2.me/theorems/4dc9ab75-6769-457d-9053-3a8bf26a9df5
-- title:
--   Oe Eq Of Range Sub
-- statement:
--   Definitions and structural lemmas for Oe Eq Of Range Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/OeEqOfRangeSub.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_ColChoiceFintype
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
def J0 {Lt : Type} {N : ℕ} (nu : Lt → YoungDiagram) (hle : ∀ z, (nu z).colLen 0 ≤ N) :
    ColChoice N nu :=
  fun s c => Fin.castLEOrderEmb (le_trans ((nu s).colLen_anti 0 c (Nat.zero_le _)) (hle s))
end PI.IsoInvMetricW


