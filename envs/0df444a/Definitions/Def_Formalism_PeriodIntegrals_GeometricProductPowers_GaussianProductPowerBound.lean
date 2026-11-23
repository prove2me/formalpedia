-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_GeometricProductPowers_GaussianProductPowerBound
-- name    : Formalism_PeriodIntegrals_GeometricProductPowers_GaussianProductPowerBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:39.03056+00:00
-- url     : https://prove2.me/theorems/2220c973-fba5-4e76-ae31-46267dafe364
-- title:
--   Gaussian Product Power Bound
-- statement:
--   Definitions and structural lemmas for Gaussian Product Power Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/GeometricProductPowers/GaussianProductPowerBound.lean

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
namespace ConditionalKappaBounds.G2
def GaussianProductPowerBound : Prop := ∀ (f k r : ℕ) (b g0 g1 : ℝ), 1 ≤ f → f ≤ k → 2 ≤ b →
  ((k : ℝ) * b) ^ 8 ≤ g0 → ((k : ℝ) * b) ^ 8 ≤ g1 →
  (1 - (((f : ℝ) * k) ^ 3)⁻¹ / 4) * (g0 * g1) ^ (f * (r * (r - 1) / 2)) ≤
    (∏ i ∈ Finset.Ico 1 r, ((g0 ^ i - 1) * (g1 ^ i - 1))) ^ f
end ConditionalKappaBounds.G2


