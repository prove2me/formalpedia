-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_SigmaStarEx
-- name    : Formalism_PeriodIntegrals_SigmaStarEx
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:22:51.03213+00:00
-- url     : https://prove2.me/theorems/5b3ba224-5eef-4e20-8e56-6a34f438ad26
-- title:
--   Sigma Star Ex
-- statement:
--   Definitions and structural lemmas for Sigma Star Ex, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/SigmaStarEx.lean

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
def SigmaStarEx : Prop :=
  ∀ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 →
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ deriv G 0 = 1 ∧ (∀ z, G (-z) = -G z) ∧
      ∀ ω ∈ lat2 w₁ w₂, ∀ z, U1 (lat2 w₁ w₂) ω G z = (if ω / 2 ∈ lat2 w₁ w₂ then 1 else -1) * G z
end PI


