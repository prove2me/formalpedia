-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:04:01.571343+00:00
-- url     : https://prove2.me/theorems/d837fd05-2926-4c85-b809-8ad0eeaa8528
-- title:
--   Deriv GA
-- statement:
--   Definitions and structural lemmas for Deriv GA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/DerivGA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
section PathL
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
end PathL
end ReciprocityTheory.ChartRestriction.DS.S7


