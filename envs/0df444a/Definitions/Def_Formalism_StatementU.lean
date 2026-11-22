-- Prove2me | Definitions.Def_Formalism_StatementU
-- name    : Formalism_StatementU
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:51:52.106923+00:00
-- url     : https://prove2.me/theorems/547bf880-292b-48ab-a852-b8ba7ae62380
-- title:
--   Statement U
-- statement:
--   Definitions and structural lemmas for Statement U, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/StatementU.lean

import Definitions.Def_Formalism_StatementOC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace Formalism
def Gzbar (x : ℝ) : ℝ := ∫ u in (1 : ℝ)..2, u * Gz (x / u)
def wavg {m : ℕ} (xs ω : Fin m → ℝ) (x : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ j, ω j * (x / xs j) * f (xs j)
def ZetaLandau : Prop :=
  ∀ s₀ : ℝ, (s₀ = 1 ∨ s₀ = -1) → ∀ θ : ℝ, 0 < θ → θ < 1 →
  (∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → s₀ * Gz x ≤ C * x ^ θ) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0
def ZetaLandauBar : Prop :=
  ∀ s₀ : ℝ, (s₀ = 1 ∨ s₀ = -1) → ∀ θ : ℝ, 0 < θ → θ < 1 →
  (∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → s₀ * Gzbar x ≤ C * x ^ θ) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0
def ZetaLandauEps : Prop :=
  ∀ s₀ : ℝ, (s₀ = 1 ∨ s₀ = -1) → ∀ θ : ℝ, 0 ≤ θ → θ < 1 →
  (∀ ε : ℝ, 0 < ε → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → s₀ * Gz x ≤ C * x ^ (θ + ε)) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0
def ZetaLandauBarEps : Prop :=
  ∀ s₀ : ℝ, (s₀ = 1 ∨ s₀ = -1) → ∀ θ : ℝ, 0 ≤ θ → θ < 1 →
  (∀ ε : ℝ, 0 < ε → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → s₀ * Gzbar x ≤ C * x ^ (θ + ε)) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0
def GzLipschitz : Prop :=
  ∃ K : ℝ, ∀ t t' : ℝ, 1 / 2 ≤ t → 1 / 2 ≤ t' → |Gz t| ≤ K * t ∧ |Gz t - Gz t'| ≤ K * |t - t'|
def SampleAverageApprox : Prop :=
  ∃ K : ℝ, ∀ (m : ℕ) (xs ω : Fin m → ℝ) (x η : ℝ), 1 ≤ x → (∀ j, 0 ≤ ω j) → ∑ j, ω j = 1 →
    (∀ j, x / 2 ≤ xs j ∧ xs j ≤ x) → (∀ j, |xs j / x - 1| ≤ η) →
    |wavg xs ω x Gz - Gz x| ≤ K * η * x
def RiemannSumApprox : Prop :=
  ∃ K : ℝ, ∀ (m : ℕ) (x : ℝ), 0 < m → 1 ≤ x →
    |wavg (fun j : Fin m => x / (1 + ((j : ℕ) + 1 : ℝ) / m)) (fun _ => (1 : ℝ) / m) x Gz - Gzbar x|
      ≤ K * x / m
end Formalism


