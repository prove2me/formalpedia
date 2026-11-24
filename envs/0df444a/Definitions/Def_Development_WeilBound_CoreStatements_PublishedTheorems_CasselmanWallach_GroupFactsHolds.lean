-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_GroupFactsHolds
-- name    : Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_GroupFactsHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:03.212808+00:00
-- url     : https://prove2.me/theorems/7472ec9d-d5f1-422f-b846-de508ecb7bf9
-- title:
--   Group Facts Holds
-- statement:
--   Definitions and structural lemmas for Group Facts Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/GroupFactsHolds.lean

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IsInLieAlgebraISmulAddConjTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
namespace PositivityTheory.CW
namespace CompactGroupFacts
variable {n : ℕ}
end CompactGroupFacts
end PositivityTheory.CW
end


