-- Prove2me | Definitions.Def_Formalism_LFunctionBounds_ExpSumLowerBound
-- name    : Formalism_LFunctionBounds_ExpSumLowerBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:35:34.201059+00:00
-- url     : https://prove2.me/theorems/f41271e8-5eac-455a-9843-4cd00113b1f5
-- title:
--   Exp Sum Lower Bound
-- statement:
--   Definitions and structural lemmas for Exp Sum Lower Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/ExpSumLowerBound.lean

import Definitions.Def_Formalism_LFunctionBounds_PositivityBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
namespace Formalism.FX
open Classical
def TripleAverageIdentity : Prop :=
  ∀ (l : ℕ) [NeZero l], l.Prime → l ≠ 2 → ∀ ν : ℕ × ℕ × ℕ → ℝ, IsProb l ν → ∀ x : ℝ, 1 ≤ x →
    ∑ S ∈ triples l, ν S * (AS l S x + 2 * Al l x - tripleMainTerm l S x) =
      famComb (fun _ : oddChars l => l) (fun χ => (χ : DirichletCharacter ℂ l)⁻¹)
          (fun χ => cW l ν χ) x
        - (x * Real.log l / ((l : ℝ) - 1) - Al l x)
def LogOm1Bound : Prop :=
  ∃ K : ℝ, ∀ l : ℕ, 2 ≤ l → ∀ S ∈ triples l, |logOm1 l S| ≤ K * (1 + Real.log l)
def gaussK (μ κ y : ℝ) : ℝ :=
  (4 * Real.pi * κ) ^ (-(1 / 2 : ℝ)) * Real.exp (-(y - μ) ^ 2 / (4 * κ))
def GaussLaplace : Prop :=
  ∀ (f : ℝ → ℂ) (a C : ℝ),
    MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Ioi 0)) →
    (∀ y : ℝ, 0 < y → ‖f y‖ ≤ C * Real.exp (a * y)) →
    ∀ c : ℝ, a < c → ∀ μ κ : ℝ, 0 < κ →
      ∫ y in Set.Ioi (0 : ℝ), f y * (gaussK μ κ y : ℂ) =
        (1 / (2 * Real.pi) : ℂ) * ∫ v : ℝ,
          (∫ y in Set.Ioi (0 : ℝ), f y * Complex.exp (-((c : ℂ) + v * I) * y)) *
            Complex.exp (κ * ((c : ℂ) + v * I) ^ 2 + μ * ((c : ℂ) + v * I))
def rectInt (g : ℂ → ℂ) (x0 x1 y0 y1 : ℝ) : ℂ :=
  (∫ x in x0..x1, g (x + y0 * I)) - (∫ x in x0..x1, g (x + y1 * I)) +
    I * (∫ y in y0..y1, g (x1 + y * I)) - I * (∫ y in y0..y1, g (x0 + y * I))
def RectResidue : Prop :=
  ∀ (g G : ℂ → ℂ) (P : Finset ℂ) (b : ℂ → ℂ) (x0 x1 y0 y1 : ℝ), x0 < x1 → y0 < y1 →
    (∀ p ∈ P, x0 < p.re ∧ p.re < x1 ∧ y0 < p.im ∧ p.im < y1) →
    (∃ U : Set ℂ, IsOpen U ∧ (Set.uIcc x0 x1 ×ℂ Set.uIcc y0 y1) ⊆ U ∧ DifferentiableOn ℂ G U) →
    (∀ w : ℂ, w ∉ P → g w = G w + ∑ p ∈ P, b p / (w - p)) →
    rectInt g x0 x1 y0 y1 = 2 * Real.pi * I * ∑ p ∈ P, b p
def LogDerivBound : Prop :=
  ∀ (f : ℂ → ℂ) (z₀ : ℂ) (R M : ℝ), 0 < R → 1 ≤ M →
    DifferentiableOn ℂ f (Metric.closedBall z₀ R) → (∀ z ∈ Metric.closedBall z₀ R, f z ≠ 0) →
    (∀ z ∈ Metric.closedBall z₀ R, ‖f z‖ ≤ M * ‖f z₀‖) →
    ∀ z ∈ Metric.closedBall z₀ (R / 2), ‖deriv f z / f z‖ ≤ 24 * Real.log M / R
def ExpSumLowerBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (z b : ι → ℂ) (i₀ : ι), Function.Injective z → (∀ i, b i ≠ 0) →
    (∀ i, (z i).re ≤ (z i₀).re) →
    ∃ c L₀ μ₀ : ℝ, 0 < c ∧ 0 < L₀ ∧ ∀ μ : ℝ, μ₀ ≤ μ → ∃ μ' ∈ Set.Icc μ (μ + L₀),
      c * Real.exp (μ' * (z i₀).re) ≤ ‖∑ i, b i * Complex.exp (μ' * z i)‖
def LocalLandau : Prop :=
  ∀ θ : ℝ, 1 / 2 ≤ θ → θ < 1 → ∀ ρ₀ : ℂ, θ < ρ₀.re → riemannZeta ρ₀ = 0 →
    ∃ s₀ T : ℝ, 1 / 2 < s₀ ∧ s₀ < 1 ∧ 1 ≤ T ∧ ∀ A : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ L₀ : ℕ, ∀ (l : ℕ) [NeZero l], l.Prime → L₀ ≤ l →
        ∀ (ι : Type) [Fintype ι] (χ : ι → DirichletCharacter ℂ l) (c : ι → ℂ),
          (∀ i, χ i ≠ 1) →
          (∀ x : ℝ, 1 ≤ x → (∑ i, c i * GchiC (χ i) x).im = 0) →
          ∑ i, ‖c i‖ ≤ (l : ℝ) ^ A →
          ‖∑ i, c i * (deriv (DirichletCharacter.LFunction (χ i)) 1 /
              DirichletCharacter.LFunction (χ i) 1)‖ ≤ (l : ℝ) ^ A →
          (∀ i, c i ≠ 0 → ∀ s : ℂ, s₀ ≤ s.re → |s.im| ≤ T →
            DirichletCharacter.LFunction (χ i) s ≠ 0) →
          ¬ (∀ x : ℝ, (l : ℝ) ^ (1 / ε) ≤ x → x ≤ (l : ℝ) ^ (1300 / ε) →
              famComb (fun _ : ι => l) χ c x ≤ x ^ (θ + ε) + 2 * Real.log l + Real.log x)
end Formalism.FX


