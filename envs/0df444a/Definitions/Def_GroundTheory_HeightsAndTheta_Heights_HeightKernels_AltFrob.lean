-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltFrob
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltFrob
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:08.813711+00:00
-- url     : https://prove2.me/theorems/46a0b57c-fe45-4665-8a20-fa031b18a94a
-- title:
--   Alt Frob
-- statement:
--   Definitions and structural lemmas for Alt Frob, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltFrob.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
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
open Finset
namespace KAlt
def frobDelta {r : ℕ} (la : Fin r → ℕ) : ℚ :=
  ∏ a : Fin r, ∏ b : Fin r,
    if a < b then ((la a + (r - 1 - a) : ℕ) : ℚ) - ((la b + (r - 1 - b) : ℕ) : ℚ) else 1
end KAlt
end GroundTheory.Heights₂.Heights


