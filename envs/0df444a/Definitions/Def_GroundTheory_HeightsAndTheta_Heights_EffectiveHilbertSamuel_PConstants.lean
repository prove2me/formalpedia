-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
-- name    : GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:22.746376+00:00
-- url     : https://prove2.me/theorems/f991f88c-d885-4254-a70b-c8b2c1525122
-- title:
--   PConstants
-- statement:
--   Definitions and structural lemmas for PConstants, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PConstants.lean

import Mathlib
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
open Real
def vanishingOrderBound (T D N : ℝ) : ℝ := T + 2 * D + 4 + N
end GroundTheory.Heights₂.Heights


