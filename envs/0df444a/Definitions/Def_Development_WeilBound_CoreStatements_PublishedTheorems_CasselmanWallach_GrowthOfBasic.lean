-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_GrowthOfBasic
-- name    : Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_GrowthOfBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:48.446316+00:00
-- url     : https://prove2.me/theorems/bdf791c8-97f6-40e2-9977-e1b6f69920d6
-- title:
--   Growth Of Basic
-- statement:
--   Definitions and structural lemmas for Growth Of Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/GrowthOfBasic.lean

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
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
namespace GrowthPolynomialOperator
variable {n : ℕ}
end GrowthPolynomialOperator
end PositivityTheory.CW
end


