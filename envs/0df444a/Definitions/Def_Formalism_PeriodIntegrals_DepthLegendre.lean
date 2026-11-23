-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_DepthLegendre
-- name    : Formalism_PeriodIntegrals_DepthLegendre
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:49.264978+00:00
-- url     : https://prove2.me/theorems/863fcba8-fc1c-44bf-8fb1-758a3c9b7d1a
-- title:
--   Depth Legendre
-- statement:
--   Definitions and structural lemmas for Depth Legendre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/DepthLegendre.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI
def DepthLegendre : Prop :=
  (∀ p : ℕ, p.Prime → ∀ c : ℕ, 1 ≤ c → (p - 1) * padicValNat p c.factorial < c) ∧
  (∀ p : ℕ, 2 ≤ p → ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) ≤ 2 * ((p : ℝ) ^ n - 1) / ((p : ℝ) - 1) ∧
      (n : ℝ) - 1 ≤ 2 * ((p : ℝ) ^ (n - 1) - 1) / ((p : ℝ) - 1))
end PI


