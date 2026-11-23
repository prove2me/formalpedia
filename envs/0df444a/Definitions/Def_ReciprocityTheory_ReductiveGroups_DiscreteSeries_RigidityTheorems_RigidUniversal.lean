-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_RigidUniversal
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_RigidUniversal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:28:23.248541+00:00
-- url     : https://prove2.me/theorems/dc89118a-1168-4a49-b8d7-6967153f17aa
-- title:
--   Rigid Universal
-- statement:
--   Definitions and structural lemmas for Rigid Universal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/RigidUniversal.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_RigidOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_DiagSubIsKIrrHW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
end ReciprocityTheory.ChartRestriction.DS


