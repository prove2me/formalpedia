-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
-- name    : Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T22:28:07.285802+00:00
-- url     : https://prove2.me/theorems/d449282d-555d-4c75-b273-30d992431052
-- title:
--   Sharper Size Needs Mle KFalse
-- statement:
--   Definitions and structural lemmas for Sharper Size Needs Mle KFalse, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SharperSizeNeedsMleKFalse.lean

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace Formalism.CohomologicalDescent
open Classical
def sums_G (c x0 x : ℝ) : ℝ := if x ≤ x0 then c / x0 * x else c + c * Real.log (x / x0)
end Formalism.CohomologicalDescent


