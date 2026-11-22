-- Prove2me | Definitions.Def_Formalism_ZetaNonvanishingGeneralWeights
-- name    : Formalism_ZetaNonvanishingGeneralWeights
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:35.0499+00:00
-- url     : https://prove2.me/theorems/d5a46f8e-5b59-490a-8ed2-93d911f8de9e
-- title:
--   Zeta Nonvanishing General Weights
-- statement:
--   Definitions and structural lemmas for Zeta Nonvanishing General Weights, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishingGeneralWeights.lean

import Definitions.Def_Formalism_StatementU
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set
noncomputable section
namespace Formalism
def spreadWeightedAverage (m : ℕ) (x : ℝ) (f : ℝ → ℝ) : ℝ :=
  wavg (fun j : Fin m => x / (1 + ((j : ℕ) + 1 : ℝ) / m)) (fun _ => (1 : ℝ) / m) x f
def ZetaNonvanishingGeneralWeights : Prop :=
  ∀ s₀ : ℝ, (s₀ = 1 ∨ s₀ = -1) → ∀ θ : ℝ, 0 ≤ θ → θ < 1 →
  (∀ ε : ℝ, 0 < ε → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∃ (m : ℕ) (xs ω : Fin m → ℝ), (∀ j, 0 ≤ ω j) ∧ ∑ j, ω j = 1 ∧
      (∀ j, x / 2 ≤ xs j ∧ xs j ≤ x) ∧ (∀ j, |xs j / x - 1| ≤ x ^ (θ - 1 + ε)) ∧
      s₀ * wavg xs ω x Gz ≤ C * x ^ (θ + ε)) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0
def ZetaNonvanishingSpreadWeights : Prop :=
  ∀ s₀ : ℝ, (s₀ = 1 ∨ s₀ = -1) → ∀ θ : ℝ, 0 ≤ θ → θ < 1 →
  (∀ ε : ℝ, 0 < ε → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∃ m : ℕ, 0 < m ∧ x ^ (1 - θ - ε) ≤ m ∧ s₀ * spreadWeightedAverage m x Gz ≤ C * x ^ (θ + ε)) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0
end Formalism


