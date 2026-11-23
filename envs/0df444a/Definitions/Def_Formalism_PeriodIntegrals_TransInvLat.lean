-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_TransInvLat
-- name    : Formalism_PeriodIntegrals_TransInvLat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:22:49.833054+00:00
-- url     : https://prove2.me/theorems/1fe59827-de8e-43a2-8352-70d26b9260f2
-- title:
--   Trans Inv Lat
-- statement:
--   Definitions and structural lemmas for Trans Inv Lat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/TransInvLat.lean

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
def TransInvLat : Prop :=
  ∀ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 → ∀ G : ℂ → ℂ,
    (∀ ω ∈ lat2 w₁ w₂, ∀ z, U1 (lat2 w₁ w₂) ω G z = (if ω / 2 ∈ lat2 w₁ w₂ then 1 else -1) * G z) →
    ∀ (x ω : ℂ) (m : ℕ), 0 < m → (m : ℂ) * (x / 2) ∈ lat2 w₁ w₂ → ω ∈ lat2 w₁ w₂ →
      U1 (lat2 w₁ w₂) (x + 2 * (m : ℂ) * ω) G = U1 (lat2 w₁ w₂) x G
end PI


