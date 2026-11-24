-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffShape
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffShape
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:36:55.166161+00:00
-- url     : https://prove2.me/theorems/8f3f5c75-d092-4b32-bac3-e51f7212c97a
-- title:
--   PCut Off Shape
-- statement:
--   Definitions and structural lemmas for PCut Off Shape, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffShape.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial Filter Topology
open scoped ContDiff
noncomputable section
def cutProfile (k : ℕ) (w : ℝ) : ℝ :=
  if w = 0 then 0 else if 1 ≤ w then 1 else cutStep (Real.log (-Real.log w) / ((k : ℝ) + 1))
end
end GroundTheory.Heights₂.Heights


