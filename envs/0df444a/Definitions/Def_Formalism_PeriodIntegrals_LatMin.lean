-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_LatMin
-- name    : Formalism_PeriodIntegrals_LatMin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:58:48.891714+00:00
-- url     : https://prove2.me/theorems/55e980b2-c46c-4c1e-8d42-35894ab0300e
-- title:
--   Lat Min
-- statement:
--   Definitions and structural lemmas for Lat Min, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/LatMin.lean

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
open MvPolynomial
def LatMin : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (B : MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p])
    (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (W : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])),
    p ≠ 2 → FiniteDimensional ℚ_[p] W → (∀ x ∈ L, x ∈ W) → L.FG →
    (∀ (c : ℚ_[p]) u v, B (c • u) v = c * B u v) → (∀ u u' v, B (u + u') v = B u v + B u' v) →
    (∀ u ∈ L, ∀ v ∈ L, B u v = B v u) → (∃ u ∈ L, ∃ v ∈ L, B u v ≠ 0) →
    ∃ x ∈ L, B x x ≠ 0 ∧ ∀ u ∈ L, ∃ c : ℤ_[p], B u x = (c : ℚ_[p]) * B x x
end PI


