-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_RLLieD
-- name    : Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_RLLieD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:35.936519+00:00
-- url     : https://prove2.me/theorems/76c2eba2-db8a-49aa-a899-e88c718410c2
-- title:
--   RLLie D
-- statement:
--   Definitions and structural lemmas for RLLie D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/RLLieD.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
namespace PositivityTheory.RL.Delta
open Complex
open scoped Real ContDiff
end PositivityTheory.RL.Delta
end


