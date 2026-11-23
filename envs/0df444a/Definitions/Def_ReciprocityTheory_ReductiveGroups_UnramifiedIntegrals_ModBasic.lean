-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:07.950787+00:00
-- url     : https://prove2.me/theorems/369ad51d-0a97-4f79-85ed-24cf6f3e90d5
-- title:
--   Mod Basic
-- statement:
--   Definitions and structural lemmas for Mod Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModBasic.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
namespace ReciprocityTheory.ChartRestriction.L1
end ReciprocityTheory.ChartRestriction.L1


