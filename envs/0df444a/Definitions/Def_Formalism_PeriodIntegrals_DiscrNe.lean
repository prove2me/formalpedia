-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_DiscrNe
-- name    : Formalism_PeriodIntegrals_DiscrNe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:22:42.445054+00:00
-- url     : https://prove2.me/theorems/b96fdf52-f917-44e5-99d6-4b5fc2b36ada
-- title:
--   Discr Ne
-- statement:
--   Definitions and structural lemmas for Discr Ne, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/DiscrNe.lean

import Definitions.Def_Formalism_PeriodIntegrals_LatDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical
namespace PI
def DiscrNe : Prop :=
  ∀ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 → discr (lat2 w₁ w₂) ≠ 0
end PI


