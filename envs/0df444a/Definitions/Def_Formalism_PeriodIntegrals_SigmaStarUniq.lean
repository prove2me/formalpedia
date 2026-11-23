-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_SigmaStarUniq
-- name    : Formalism_PeriodIntegrals_SigmaStarUniq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:22:54.06043+00:00
-- url     : https://prove2.me/theorems/91b71d22-892e-45e1-83f4-a32ae66152ef
-- title:
--   Sigma Star Uniq
-- statement:
--   Definitions and structural lemmas for Sigma Star Uniq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/SigmaStarUniq.lean

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
def SigmaStarUniq : Prop :=
  ∀ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 → ∀ G G' : ℂ → ℂ,
    (Differentiable ℂ G ∧ deriv G 0 = 1 ∧ (∀ z, G (-z) = -G z) ∧
      ∀ ω ∈ lat2 w₁ w₂, ∀ z, U1 (lat2 w₁ w₂) ω G z = (if ω / 2 ∈ lat2 w₁ w₂ then 1 else -1) * G z) →
    (Differentiable ℂ G' ∧ deriv G' 0 = 1 ∧ (∀ z, G' (-z) = -G' z) ∧
      ∀ ω ∈ lat2 w₁ w₂, ∀ z, U1 (lat2 w₁ w₂) ω G' z = (if ω / 2 ∈ lat2 w₁ w₂ then 1 else -1) * G' z) →
    G = G'
end PI


