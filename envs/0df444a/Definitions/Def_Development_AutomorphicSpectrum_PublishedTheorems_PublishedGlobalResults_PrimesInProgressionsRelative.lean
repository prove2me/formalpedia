-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_PublishedTheorems_PublishedGlobalResults_PrimesInProgressionsRelative
-- name    : Development_AutomorphicSpectrum_PublishedTheorems_PublishedGlobalResults_PrimesInProgressionsRelative
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:06:07.067788+00:00
-- url     : https://prove2.me/theorems/44e9632f-2f7e-4820-81f8-62a48c079727
-- title:
--   Primes In Progressions Relative
-- statement:
--   Definitions and structural lemmas for Primes In Progressions Relative, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/PublishedGlobalResults/PrimesInProgressionsRelative.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Classical
open NumberField
noncomputable section
namespace GlobalTheory.CompanionTheory
def PrimesInProgressionsRelative : Prop :=
  ∃ C₀ C c cQ c₁ : ℝ, 0 < C₀ ∧ 0 < C ∧ 0 < c ∧ 0 < cQ ∧ 0 < c₁ ∧ ∀ (N : ℕ) [NeZero N], ∃ (β : ℝ) (θ : ZMod N → ℝ),
    (((∀ a, θ a = 0) ∧ ∀ (χ : DirichletCharacter ℂ N) (b : ℝ), 1 - c₁ / Real.log (4 * N) ≤ b → b < 1 →
        DirichletCharacter.LFunction χ b ≠ 0) ∨
      (∃ χ₁ : DirichletCharacter ℂ N, (∀ a, χ₁ a = (θ a : ℂ)) ∧ 1 / 2 ≤ β ∧ β < 1 ∧
        cQ / ((4 * N : ℝ) ^ 2 * Real.log (4 * N)) ≤ 1 - β ∧ DirichletCharacter.LFunction χ₁ β = 0 ∧
        ∀ (χ : DirichletCharacter ℂ N) (b : ℝ), 1 - c₁ / Real.log (4 * N) ≤ b → b < 1 →
          DirichletCharacter.LFunction χ b = 0 → χ = χ₁ ∧ b = β)) ∧
    ∀ a : ZMod N, IsUnit a → ∀ X : ℝ, (4 * N : ℝ) ^ C₀ ≤ X →
      |(((Finset.Icc 1 ⌊X⌋₊).filter (fun p : ℕ => p.Prime ∧ (p : ZMod N) = a)).card : ℝ) -
          ((∫ t in (2 : ℝ)..X, 1 / Real.log t) - θ a * ∫ t in (2 : ℝ)..X ^ β, 1 / Real.log t) / (Nat.totient N : ℝ)| ≤
        (C * Real.exp (-(c * Real.log X / Real.log (4 * N))) + C * Real.exp (-(c * Real.sqrt (Real.log X)))) *
          (((∫ t in (2 : ℝ)..X, 1 / Real.log t) - θ a * ∫ t in (2 : ℝ)..X ^ β, 1 / Real.log t) / (Nat.totient N : ℝ))
end GlobalTheory.CompanionTheory


