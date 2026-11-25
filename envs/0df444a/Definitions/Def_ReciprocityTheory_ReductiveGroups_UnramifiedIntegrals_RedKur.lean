-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKur
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKur
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:49:18.850443+00:00
-- url     : https://prove2.me/theorems/5a0787c7-822f-4c42-a5e5-6d725afd3f12
-- title:
--   Red Kur
-- statement:
--   Definitions and structural lemmas for Red Kur, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedKur.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KurComplete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
namespace ReciprocityTheory.ChartRestriction.L1
variable (l : ℕ) [Fact l.Prime]
end ReciprocityTheory.ChartRestriction.L1


