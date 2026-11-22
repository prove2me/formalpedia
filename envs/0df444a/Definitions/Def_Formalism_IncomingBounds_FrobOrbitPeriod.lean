-- Prove2me | Definitions.Def_Formalism_IncomingBounds_FrobOrbitPeriod
-- name    : Formalism_IncomingBounds_FrobOrbitPeriod
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:58:16.778921+00:00
-- url     : https://prove2.me/theorems/8806781c-a94d-4b54-a03e-6dbfc53ea0b9
-- title:
--   Frob Orbit Period
-- statement:
--   Definitions and structural lemmas for Frob Orbit Period, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FrobOrbitPeriod.lean

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
open scoped BigOperators
namespace Formalism.IncomingBounds
def FrobOrbitSum : Prop :=
  ∀ (α : Type) [Fintype α] (φ : Equiv.Perm α) (p : ℝ), 1 < p → ∀ k : ℕ, 1 ≤ k → ∀ a : α → ℝ,
    (∑ τ : α, ((∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹ * a ((φ ^ (n + 1)) τ)) - a τ / (p - 1))) =
      (1 / (p ^ k - 1) - 1 / (p - 1)) * ∑ τ : α, a τ
def FrobOrbitPeriod : Prop :=
  ∀ (α : Type) (φ : Equiv.Perm α) (p : ℝ), 1 < p → ∀ k : ℕ, 1 ≤ k → ∀ (a : α → ℝ) (τ : α)
    (f : ℕ), 1 ≤ f → (φ ^ f) τ = τ →
      (∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹ * a ((φ ^ (n + 1)) τ)) =
        (∑ n ∈ Finset.range f, (p ^ ((n + 1) * k))⁻¹ * a ((φ ^ (n + 1)) τ)) /
          (1 - (p ^ (f * k))⁻¹)
end Formalism.IncomingBounds


