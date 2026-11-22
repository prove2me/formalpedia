-- Prove2me | Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
-- name    : Formalism_ZeroFreeRegion_SmallHeightLogDeriv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:39.378647+00:00
-- url     : https://prove2.me/theorems/56efa59e-2bdd-4a47-96a6-b2d5675419e4
-- title:
--   Small Height Log Deriv
-- statement:
--   Definitions and structural lemmas for Small Height Log Deriv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/SmallHeightLogDeriv.lean

import Definitions.Def_Formalism_ZeroFreeRegion_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
namespace Formalism.ZF
def rectInt (g : ℂ → ℂ) (x0 x1 y0 y1 : ℝ) : ℂ :=
  (∫ x in x0..x1, g (x + y0 * I)) - (∫ x in x0..x1, g (x + y1 * I)) +
    I * (∫ y in y0..y1, g (x1 + y * I)) - I * (∫ y in y0..y1, g (x0 + y * I))
def LogDerivBound : Prop :=
  ∀ (f : ℂ → ℂ) (z₀ : ℂ) (R M : ℝ), 0 < R → 1 ≤ M →
    DifferentiableOn ℂ f (Metric.closedBall z₀ R) → (∀ z ∈ Metric.closedBall z₀ R, f z ≠ 0) →
    (∀ z ∈ Metric.closedBall z₀ R, ‖f z‖ ≤ M * ‖f z₀‖) →
    ∀ z ∈ Metric.closedBall z₀ (R / 2), ‖deriv f z / f z‖ ≤ 24 * Real.log M / R
def ThreeFourOne : Prop :=
  ∀ σ t : ℝ, 1 < σ →
    0 ≤ 3 * (-(deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ))).re
      + 4 * (-(deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I))).re
      + (-(deriv riemannZeta ((σ : ℂ) + 2 * t * I) / riemannZeta ((σ : ℂ) + 2 * t * I))).re
def LogDerivRight : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 < s.re →
    ‖deriv riemannZeta s / riemannZeta s‖ ≤ 1 / (s.re - 1) + C
def ZetaGrowth : Prop :=
  ∀ s : ℂ, 0 < s.re → s ≠ 1 → ‖riemannZeta s‖ ≤ 1 + 1 / ‖s - 1‖ + ‖s‖ * (1 + 1 / s.re)
def ZetaInvBound : Prop :=
  ∀ s : ℂ, 1 < s.re → ‖riemannZeta s‖⁻¹ ≤ s.re / (s.re - 1)
def SmallHeight : Prop :=
  ∀ T : ℝ, ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, |s.im| ≤ T → 1 - c ≤ s.re → s ≠ 1 → riemannZeta s ≠ 0
def SmallHeightLogDeriv : Prop :=
  ∀ T : ℝ, ∃ c C : ℝ, 0 < c ∧ ∀ s : ℂ, s ≠ 1 → |s.im| ≤ T → 1 - c ≤ s.re → s.re ≤ 3 →
    ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ C
def ZeroFactor : Prop :=
  ∀ (f : ℂ → ℂ) (z₀ : ℂ) (r R₁ : ℝ), 0 < R₁ → R₁ < r →
    DifferentiableOn ℂ f (Metric.closedBall z₀ r) → f z₀ ≠ 0 →
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ) (h : ℂ → ℂ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall z₀ R₁ ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      DifferentiableOn ℂ h (Metric.closedBall z₀ r) ∧
      (∀ z ∈ Metric.closedBall z₀ R₁, h z ≠ 0) ∧
      ∀ z ∈ Metric.closedBall z₀ r, f z = (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z
def LandauLocal : Prop :=
  ∀ (f : ℂ → ℂ) (z₀ : ℂ) (r M : ℝ), 0 < r → 1 ≤ M →
    DifferentiableOn ℂ f (Metric.closedBall z₀ r) → f z₀ ≠ 0 →
    (∀ z ∈ Metric.closedBall z₀ r, ‖f z‖ ≤ M * ‖f z₀‖) →
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall z₀ (r / 3) ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ Real.log M / Real.log 2 ∧
      ∀ z ∈ Metric.closedBall z₀ (r / 6), f z ≠ 0 →
        ‖deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)‖ ≤ 72 * Real.log M / r
def Fy (y : ℝ) (w : ℂ) : ℂ :=
  -(deriv riemannZeta w / riemannZeta w) * (y : ℂ) ^ w / (w * (w - 1))
def Perron : Prop :=
  ∀ y : ℝ, 1 ≤ y → ∀ σ₀ : ℝ, 1 < σ₀ →
    MeasureTheory.Integrable (fun t : ℝ => Fy y ((σ₀ : ℂ) + t * I)) ∧
    ((Formalism.Sz y : ℝ) : ℂ) = (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Fy y ((σ₀ : ℂ) + t * I)
def RectDoublePole : Prop :=
  ∀ (g G : ℂ → ℂ) (a b p : ℂ) (x0 x1 y0 y1 : ℝ),
    x0 < p.re → p.re < x1 → y0 < p.im → p.im < y1 →
    (∃ U : Set ℂ, IsOpen U ∧ (Set.uIcc x0 x1 ×ℂ Set.uIcc y0 y1) ⊆ U ∧ DifferentiableOn ℂ G U) →
    (∀ w : ℂ, w ≠ p → g w = G w + a / (w - p) ^ 2 + b / (w - p)) →
    rectInt g x0 x1 y0 y1 = 2 * Real.pi * I * b
def LaurentAtOne : Prop :=
  ∀ y : ℝ, 0 < y → ∃ A : ℂ → ℂ, DifferentiableAt ℂ A 1 ∧
    ∀ᶠ w in 𝓝[≠] (1 : ℂ), Fy y w = A w + (y : ℂ) / (w - 1) ^ 2 +
      ((y : ℂ) * Real.log y - (1 + Real.eulerMascheroniConstant) * y) / (w - 1)
def RectShift : Prop :=
  ∀ y : ℝ, 0 < y → ∀ σ₁ σ₀ T : ℝ, 0 < σ₁ → σ₁ < 1 → 1 < σ₀ → 0 < T →
    (∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₀ → |w.im| ≤ T → w ≠ 1 → riemannZeta w ≠ 0) →
    rectInt (Fy y) σ₁ σ₀ (-T) T =
      2 * Real.pi * I * ((y : ℂ) * Real.log y - (1 + Real.eulerMascheroniConstant) * y)
def LandauLocalOf : Prop := ZeroFactor → LogDerivBound → LandauLocal
def ZeroFreeOf : Prop :=
  ThreeFourOne → LogDerivRight → ZetaGrowth → ZetaInvBound → SmallHeight → LandauLocal →
    ZeroFreeRegion
def LogDerivRegionOf : Prop :=
  ZeroFreeRegion → LogDerivRight → ZetaGrowth → ZetaInvBound → SmallHeightLogDeriv →
    LandauLocal → LogDerivRegion
def RectShiftOf : Prop := RectDoublePole → LaurentAtOne → RectShift
def GzPNTOf : Prop :=
  ZeroFreeRegion → LogDerivRegion → LogDerivRight → Perron → RectShift → GzPNT
end Formalism.ZF


