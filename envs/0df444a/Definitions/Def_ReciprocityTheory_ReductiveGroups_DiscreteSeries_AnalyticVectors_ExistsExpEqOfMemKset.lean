-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ExistsExpEqOfMemKset
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ExistsExpEqOfMemKset
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:32:55.9063+00:00
-- url     : https://prove2.me/theorems/97964ea7-70f7-4769-9cae-d7c877dd108f
-- title:
--   Exists Exp Eq Of Mem Kset
-- statement:
--   Definitions and structural lemmas for Exists Exp Eq Of Mem Kset, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/ExistsExpEqOfMemKset.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
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
section L2
open scoped Matrix.Norms.L2Operator
end L2
end ReciprocityTheory.ChartRestriction.DS


