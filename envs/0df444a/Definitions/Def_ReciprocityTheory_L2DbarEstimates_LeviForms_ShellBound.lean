-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ShellBound
-- name    : ReciprocityTheory_L2DbarEstimates_LeviForms_ShellBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:44:27.2894+00:00
-- url     : https://prove2.me/theorems/ad94798a-1607-4365-8e7f-e5882f917001
-- title:
--   Shell Bound
-- statement:
--   Definitions and structural lemmas for Shell Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ShellBound.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ShellA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
namespace ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff
end ReciprocityTheory.L2DbarEstimates.I


