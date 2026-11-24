-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_JetOfMonomialSumStatement
-- name    : GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_JetOfMonomialSumStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:49.770558+00:00
-- url     : https://prove2.me/theorems/0b1277a5-1666-4666-b37a-3c23b3327ee5
-- title:
--   Jet Of Monomial Sum Statement
-- statement:
--   Definitions and structural lemmas for Jet Of Monomial Sum Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/JetOfMonomialSumStatement.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.EffectiveHS
def JetOfMonomialSum.Statement : Prop :=
  ∀ (n p : ℕ) (u : Fin p → (Fin n → ℂ) → ℂ) (h : (Fin p → ℕ) → (Fin n → ℂ) → ℂ)
    (z₀ : Fin n → ℂ) (a : ℕ),
    (∀ i, AnalyticAt ℂ (u i) z₀) → (∀ i, u i z₀ = 0) → (∀ α, AnalyticAt ℂ (h α) z₀) →
    (∀ k < a, iteratedFDeriv ℂ k
        (fun z => ∑ α ∈ Finset.Nat.antidiagonalTuple p a, (∏ i, u i z ^ α i) * h α z) z₀ = 0) ∧
    iteratedFDeriv ℂ a
        (fun z => ∑ α ∈ Finset.Nat.antidiagonalTuple p a, (∏ i, u i z ^ α i) * h α z) z₀ =
      ∑ α ∈ Finset.Nat.antidiagonalTuple p a,
        h α z₀ • iteratedFDeriv ℂ a (fun z => ∏ i, u i z ^ α i) z₀ ∧
    ∀ w : Fin n → ℂ, iteratedFDeriv ℂ a
        (fun z => ∑ α ∈ Finset.Nat.antidiagonalTuple p a, (∏ i, u i z ^ α i) * h α z) z₀
        (fun _ => w) =
      (a.factorial : ℂ) * ∑ α ∈ Finset.Nat.antidiagonalTuple p a,
        (∏ i, (fderiv ℂ (u i) z₀ w) ^ α i) * h α z₀
end GroundTheory.Heights₂.Heights.EffectiveHS


