-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedProjA
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedProjA
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T21:46:21.94549+00:00
-- url     : https://prove2.me/theorems/c41b6602-3497-45ed-9561-05ba89000f00
-- title:
--   Red Proj A
-- statement:
--   Definitions and structural lemmas for Red Proj A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedProjA.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
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
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial
namespace ReciprocityTheory.ChartRestriction.L1
variable {K : Type} [Field K] (U : PowerSeries K)
end ReciprocityTheory.ChartRestriction.L1


