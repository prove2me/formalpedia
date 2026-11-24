-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocD
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocD
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T21:58:23.334626+00:00
-- url     : https://prove2.me/theorems/8f719889-0a2c-4387-ac6d-2fb704d00a4a
-- title:
--   Mod Loc D
-- statement:
--   Definitions and structural lemmas for Mod Loc D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModLocD.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane Pointwise
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
namespace ReciprocityTheory.ChartRestriction.L1
end ReciprocityTheory.ChartRestriction.L1


