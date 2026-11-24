-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KmuInclDenseRange
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KmuInclDenseRange
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T21:49:32.450344+00:00
-- url     : https://prove2.me/theorems/deefa40f-e8d2-412a-b7fa-877ce37cb9a3
-- title:
--   Kmu Incl Dense Range
-- statement:
--   Definitions and structural lemmas for Kmu Incl Dense Range, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/KmuInclDenseRange.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsExtendEndomorphismFractions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable (l : ℕ) [Fact l.Prime]
def kmuIncl : Kmu l →+* MaximalUnramifiedExtension l := Subfield.inclusion (Subfield.le_topologicalClosure (Kmu l))
end ReciprocityTheory.ChartRestriction.L1


