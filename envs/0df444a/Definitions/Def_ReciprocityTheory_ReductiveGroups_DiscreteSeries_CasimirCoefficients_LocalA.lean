-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_LocalA
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_LocalA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:07:21.292333+00:00
-- url     : https://prove2.me/theorems/3956b58c-8410-488c-ae2b-45126f918925
-- title:
--   Local A
-- statement:
--   Definitions and structural lemmas for Local A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/LocalA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section LogL
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
end LogL
end ReciprocityTheory.ChartRestriction.DS.S7


