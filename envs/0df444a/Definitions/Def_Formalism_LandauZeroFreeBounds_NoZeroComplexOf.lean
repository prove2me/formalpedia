-- Prove2me | Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
-- name    : Formalism_LandauZeroFreeBounds_NoZeroComplexOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:40.319821+00:00
-- url     : https://prove2.me/theorems/5e699b4b-a1dd-484e-a86e-8382bfa7cf87
-- title:
--   No Zero Complex Of
-- statement:
--   Definitions and structural lemmas for No Zero Complex Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/NoZeroComplexOf.lean

import Definitions.Def_Formalism_LandauZeroFreeBounds_Statement
import Definitions.Def_Formalism_ZeroFreeRegion_Statement
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
namespace Formalism.ZeroFreeDirichlet
def negLD {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  -(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s)
def LandauLocal2 : Prop :=
  ∀ (f : ℂ → ℂ) (z₀ : ℂ) (r M : ℝ), 0 < r → 1 ≤ M →
    DifferentiableOn ℂ f (Metric.closedBall z₀ r) → f z₀ ≠ 0 →
    (∀ z ∈ Metric.closedBall z₀ r, ‖f z‖ ≤ M * ‖f z₀‖) →
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall z₀ (r / 3) ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, deriv f ρ = 0 → 2 ≤ m ρ) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ Real.log M / Real.log 2 ∧
      ∀ z ∈ Metric.closedBall z₀ (r / 6), f z ≠ 0 →
        ‖deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)‖ ≤ 72 * Real.log M / r
def LGrowth : Prop :=
  ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ, 1 / 2 ≤ s.re →
    ‖DirichletCharacter.LFunction χ s‖ ≤ C * q * (1 + ‖s‖)
def LInvBound : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), 1 < s.re →
    ‖DirichletCharacter.LFunction χ s‖⁻¹ ≤ s.re / (s.re - 1)
def LLogDerivRight : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), 1 < s.re →
    ‖negLD χ s‖ ≤ 1 / (s.re - 1) + C
def Positivity : Prop :=
  ∀ (q : ℕ) [NeZero q] (σ : ℝ), 1 < σ →
    (∀ (χ : DirichletCharacter ℂ q) (t : ℝ),
      0 ≤ 3 * (negLD (1 : DirichletCharacter ℂ q) (σ : ℂ)).re + 4 * (negLD χ ((σ : ℂ) + t * I)).re
        + (negLD (χ ^ 2) ((σ : ℂ) + 2 * t * I)).re) ∧
    (∀ χ : DirichletCharacter ℂ q, χ ^ 2 = 1 →
      0 ≤ (negLD (1 : DirichletCharacter ℂ q) (σ : ℂ)).re + (negLD χ (σ : ℂ)).re) ∧
    (∀ χ₁ χ₂ : DirichletCharacter ℂ q, χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 →
      0 ≤ (negLD (1 : DirichletCharacter ℂ q) (σ : ℂ)).re + (negLD χ₁ (σ : ℂ)).re
        + (negLD χ₂ (σ : ℂ)).re + (negLD (χ₁ * χ₂) (σ : ℂ)).re)
def TrivLogDeriv : Prop :=
  ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (σ t : ℝ), 1 < σ → σ ≤ 2 →
    (negLD (1 : DirichletCharacter ℂ q) ((σ : ℂ) + t * I)).re ≤
      (1 / ((σ : ℂ) - 1 + t * I)).re + C * Real.log ((q : ℝ) * (|t| + 2))
def TrivZeros : Prop :=
  ∀ (q : ℕ) [NeZero q] (s : ℂ), 0 < s.re → s ≠ 1 →
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s = 0 → riemannZeta s = 0
def RealConj : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 → χ ≠ 1 → ∀ s : ℂ,
    DirichletCharacter.LFunction χ (starRingEnd ℂ s) = starRingEnd ℂ (DirichletCharacter.LFunction χ s)
def LocalZeros : Prop :=
  ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ t : ℝ,
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔
        (ρ ∈ Metric.closedBall ((11 / 10 : ℂ) + t * I) (1 / 5) ∧ DirichletCharacter.LFunction χ ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, deriv (DirichletCharacter.LFunction χ) ρ = 0 → 2 ≤ m ρ) ∧
      ∀ σ : ℝ, 1 < σ → σ ≤ 6 / 5 →
        (negLD χ ((σ : ℂ) + t * I)).re ≤
          C * Real.log ((q : ℝ) * (|t| + 2)) - ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + t * I - ρ)).re
def NoZeroComplex : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    χ ^ 2 ≠ 1 → InRegion c q s → DirichletCharacter.LFunction χ s ≠ 0
def RealLargeT : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    χ ^ 2 = 1 → χ ≠ 1 → δ / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ |s.im| → InRegion c q s →
      DirichletCharacter.LFunction χ s ≠ 0
def RealSmallT : Prop :=
  ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 → χ ≠ 1 →
    ∀ s s' : ℂ, |s.im| < δ / Real.log ((q : ℝ) * (|s.im| + 2)) →
      |s'.im| < δ / Real.log ((q : ℝ) * (|s'.im| + 2)) →
      InRegion c q s → InRegion c q s' →
      DirichletCharacter.LFunction χ s = 0 → DirichletCharacter.LFunction χ s' = 0 →
      s.im = 0 ∧ deriv (DirichletCharacter.LFunction χ) s ≠ 0 ∧ s' = s
def TwoReal : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q), χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 →
    χ₁ ≠ 1 → χ₂ ≠ 1 → χ₁ ≠ χ₂ → ∀ β₁ β₂ : ℝ, InRegion c q (β₁ : ℂ) → InRegion c q (β₂ : ℂ) →
      DirichletCharacter.LFunction χ₁ (β₁ : ℂ) ≠ 0 ∨ DirichletCharacter.LFunction χ₂ (β₂ : ℂ) ≠ 0
def LocalZerosOf : Prop := LandauLocal2 → LGrowth → LInvBound → LocalZeros
def NoZeroComplexOf : Prop := LocalZeros → LLogDerivRight → Positivity → NoZeroComplex
def RealLargeTOf : Prop := LocalZeros → LLogDerivRight → Positivity → TrivLogDeriv → RealLargeT
def RealSmallTOf : Prop := LocalZeros → LLogDerivRight → Positivity → RealConj → RealSmallT
def TwoRealOf : Prop := LocalZeros → LLogDerivRight → Positivity → TwoReal
def ZFRDirichletOf : Prop :=
  Formalism.ZF.ZeroFreeRegion → TrivZeros → NoZeroComplex → RealLargeT → RealSmallT → TwoReal → ZFRDirichlet
end Formalism.ZeroFreeDirichlet


