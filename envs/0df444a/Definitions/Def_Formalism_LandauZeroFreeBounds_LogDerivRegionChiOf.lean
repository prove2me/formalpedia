-- Prove2me | Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
-- name    : Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:50:53.647794+00:00
-- url     : https://prove2.me/theorems/b062b784-d118-4e12-89a2-f5a2a63864af
-- title:
--   Log Deriv Region Chi Of
-- statement:
--   Definitions and structural lemmas for Log Deriv Region Chi Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/LogDerivRegionChiOf.lean

import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAP
import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset ArithmeticFunction
noncomputable section
namespace Formalism.ZeroFreeDirichlet
def Schi {q : ℕ} (χ : DirichletCharacter ℂ q) (y : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊y⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((y / n - 1 : ℝ) : ℂ)
def Fchi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (y : ℝ) (w : ℂ) : ℂ :=
  negLD χ w * (y : ℂ) ^ w / (w * (w - 1))
def PerronChi : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (y : ℝ), 1 ≤ y → ∀ σ₀ : ℝ, 1 < σ₀ →
    MeasureTheory.Integrable (fun t : ℝ => Fchi χ y ((σ₀ : ℂ) + t * I)) ∧
    Schi χ y = (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Fchi χ y ((σ₀ : ℂ) + t * I)
def LogDerivRegionChi : Prop :=
  ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 20 → ∃ C : ℝ,
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (B : Finset ℝ), χ ≠ 1 → ExcZeros c₁ χ B →
      ∀ s : ℂ, InRegion (c₁ / 2) q s → (∀ β ∈ B, s ≠ (β : ℂ)) →
        ‖negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ C * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2
def RectShiftChi : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ y : ℝ, 0 < y →
    ∀ (σ₁ σ₀ T : ℝ) (B : Finset ℝ), 0 < σ₁ → σ₁ < 1 → 1 < σ₀ → 0 < T →
      (∀ β ∈ B, σ₁ < β ∧ β < σ₀ ∧ deriv (DirichletCharacter.LFunction χ) (β : ℂ) ≠ 0) →
      (∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₀ → |w.im| ≤ T → DirichletCharacter.LFunction χ w = 0 →
        ∃ β ∈ B, w = (β : ℂ)) →
      (∀ β ∈ B, DirichletCharacter.LFunction χ (β : ℂ) = 0) →
      Formalism.ZF.rectInt (Fchi χ y) σ₁ σ₀ (-T) T =
        2 * Real.pi * I * (negLD χ 1 * y - ∑ β ∈ B, (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1)))
def SmoothChi : Prop :=
  ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 20 → ∃ c C : ℝ, 0 < c ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (B : Finset ℝ) (y : ℝ), χ ≠ 1 → ExcZeros c₁ χ B →
      2 ≤ y → (q : ℝ) ≤ Real.exp (c * Real.sqrt (Real.log y)) →
      ‖Schi χ y - negLD χ 1 * y + ∑ β ∈ B, (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1))‖ ≤
        C * y * Real.exp (-c * Real.sqrt (Real.log y))
def LDerivNearOne : Prop :=
  ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ σ : ℝ,
    1 - 1 / Real.log (3 * q) ≤ σ → σ ≤ 1 →
      ‖deriv (DirichletCharacter.LFunction χ) (σ : ℂ)‖ ≤ C * Real.log (3 * q) ^ 2
def ExcBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (β : ℝ),
    χ ^ 2 = 1 → χ ≠ 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 → β ≤ 1 - c * (q : ℝ) ^ (-ε)
def MertensUpper : Prop :=
  ∀ z : ℝ, 2 ≤ z → ∏ p ∈ (range (⌊z⌋₊ + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)) ≤ 1 / Real.log z
def LandauLocal3 : Prop :=
  ∀ (f : ℂ → ℂ) (z₀ : ℂ) (r M : ℝ), 0 < r → 1 ≤ M →
    DifferentiableOn ℂ f (Metric.closedBall z₀ r) → f z₀ ≠ 0 →
    (∀ z ∈ Metric.closedBall z₀ r, ‖f z‖ ≤ M * ‖f z₀‖) →
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall z₀ (r / 3) ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, deriv f ρ = 0 → 2 ≤ m ρ) ∧
      (∀ ρ ∈ Z, deriv f ρ ≠ 0 → m ρ = 1) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ Real.log M / Real.log 2 ∧
      ∀ z ∈ Metric.closedBall z₀ (r / 6), f z ≠ 0 →
        ‖deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)‖ ≤ 72 * Real.log M / r
def LogDerivRegionChiOf : Prop :=
  LandauLocal3 → LGrowth → LInvBound → LLogDerivRight → LogDerivRegionChi
def SmoothChiOf : Prop :=
  PerronChi → RectShiftChi → LogDerivRegionChi → LLogDerivRight → SmoothChi
def PsiChiBoundOf : Prop := SmoothChi → Formalism.ZF.GzPNT → PsiChiBound
def ExcBoundOf : Prop := SiegelLower → LDerivNearOne → ExcBound
def SiegelWalfiszOf : Prop := PsiChiBound → ZFRDirichlet → ExcBound → SiegelWalfisz
def SiegelWalfiszAPOf : Prop := SiegelWalfisz → SiegelWalfiszAP
def PrimeShareSWOf : Prop := SiegelWalfiszAP → MertensUpper → PrimeShareSW
end Formalism.ZeroFreeDirichlet


