-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermCanonicalCover
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermCanonicalCover
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:13:04.724695+00:00
-- url     : https://prove2.me/theorems/8e6986e8-6476-4bf0-b5ba-8b401ece0f58
-- title:
--   St Prime Germ Canonical Cover
-- statement:
--   Definitions and structural lemmas for St Prime Germ Canonical Cover, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StPrimeGermCanonicalCover.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermNullstellensatz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter
def PrimeGermCanonicalCover.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (p : Fin k → (σ → ℂ) → ℂ),
    (∀ i, AnalyticAt ℂ (p i) w) → (holGermIdeal w p).IsPrime →
    ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (δ : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ δ (A w) ∧
      (¬ ∃ h : Fin k → (σ → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (h i) w) ∧
          ∀ᶠ z in 𝓝 w, δ (A z) = ∑ i, h i z * p i z) ∧
      (∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g w →
        ∃ (M : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (h : Fin k → (σ → ℂ) → ℂ),
          (∀ j, AnalyticAt ℂ (a j) (A w)) ∧ (∀ i, AnalyticAt ℂ (h i) w) ∧
          ∀ᶠ z in 𝓝 w, δ (A z) ^ M * g z - ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = ∑ i, h i z * p i z) ∧
      ∀ W ∈ 𝓝 w, ∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
        ∃ x : Fin N → σ → ℂ, (∀ j, x j ∈ W ∧ (∀ i, p i (x j) = 0) ∧ A (x j) = y) ∧
          Function.Injective fun j => ℓ (x j)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


