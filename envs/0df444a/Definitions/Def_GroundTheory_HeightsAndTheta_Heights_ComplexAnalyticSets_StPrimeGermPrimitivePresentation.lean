-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermPrimitivePresentation
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermPrimitivePresentation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:53.032975+00:00
-- url     : https://prove2.me/theorems/6bfa97d1-412c-4114-af73-317a1017cb34
-- title:
--   St Prime Germ Primitive Presentation
-- statement:
--   Definitions and structural lemmas for St Prime Germ Primitive Presentation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StPrimeGermPrimitivePresentation.lean

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
def IsGermCombination {σ : Type} [Fintype σ] (w : σ → ℂ) {k : ℕ} (p : Fin k → (σ → ℂ) → ℂ)
    (f : (σ → ℂ) → ℂ) : Prop :=
  ∃ h : Fin k → (σ → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (h i) w) ∧ ∀ᶠ z in 𝓝 w, f z = ∑ i, h i z * p i z
noncomputable def monicOfCoeffs {N : ℕ} (c : Fin N → ℂ) : Polynomial ℂ :=
  Polynomial.X ^ N + ∑ j : Fin N, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)
def IsPrimitivePresentation {σ : Type} [Fintype σ] (w : σ → ℂ) {k : ℕ} (p : Fin k → (σ → ℂ) → ℂ) {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ) {N : ℕ} (c : Fin N → (Fin d → ℂ) → ℂ)
    (δ : (Fin d → ℂ) → ℂ) : Prop :=
  (∀ j, AnalyticAt ℂ (c j) (A w)) ∧ AnalyticAt ℂ δ (A w) ∧
  IsGermCombination w p (fun z => ℓ z ^ N + ∑ j, c j (A z) * ℓ z ^ (j : ℕ)) ∧
  (∀ a : Fin N → (Fin d → ℂ) → ℂ, (∀ j, AnalyticAt ℂ (a j) (A w)) →
    IsGermCombination w p (fun z => ∑ j, a j (A z) * ℓ z ^ (j : ℕ)) →
    ∀ j, ∀ᶠ y in 𝓝 (A w), a j y = 0) ∧
  (∀ᶠ y in 𝓝 (A w), δ y ≠ 0 → (monicOfCoeffs fun j => c j y).Separable) ∧
  (∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g w →
    ∃ (M : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (a j) (A w)) ∧
      IsGermCombination w p (fun z => δ (A z) ^ M * g z - ∑ j, a j (A z) * ℓ z ^ (j : ℕ))) ∧
  (∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g w →
    ∃ (n : ℕ) (b : Fin n → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (b j) (A w)) ∧
      IsGermCombination w p (fun z => g z ^ n + ∑ j, b j (A z) * g z ^ (j : ℕ)) ∧
      ∀ T : ℂ, T ^ n + ∑ j, b j (A w) * T ^ (j : ℕ) = (T - g w) ^ n)
def PrimeGermPrimitivePresentation.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (p : Fin k → (σ → ℂ) → ℂ),
    (∀ i, AnalyticAt ℂ (p i) w) → (holGermIdeal w p).IsPrime →
    ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ)
      (c : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ),
      IsPrimitivePresentation w p A ℓ c δ ∧ ¬ IsGermCombination w p (fun z => δ (A z))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


