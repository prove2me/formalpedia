-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModInertKur
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModInertKur
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T22:08:29.713806+00:00
-- url     : https://prove2.me/theorems/8eec47ca-638a-4e0b-8c4a-27f13ace953d
-- title:
--   Mod Inert Kur
-- statement:
--   Definitions and structural lemmas for Mod Inert Kur, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModInertKur.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
namespace ReciprocityTheory.ChartRestriction.L1
end ReciprocityTheory.ChartRestriction.L1


