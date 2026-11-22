-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
-- name    : Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:10:05.314145+00:00
-- url     : https://prove2.me/theorems/289d764c-91f3-4f3c-9c0c-db830179f22a
-- title:
--   Smoothed Remainder Real Integral Formula
-- statement:
--   Definitions and structural lemmas for Smoothed Remainder Real Integral Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/SmoothedRemainderRealIntegralFormula.lean

import Mathlib
import Definitions.Def_Formalism_LandauZeroFreeBounds_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology ArithmeticFunction
open scoped ENNReal
noncomputable section
namespace Formalism.HermitianLattices.GL2PrimeSums
def psum (a : ℕ → ℂ) (u : ℝ) : ℂ := ∑ n ∈ Icc 1 ⌊u⌋₊, a n
def psumR (a : ℕ → ℝ) (u : ℝ) : ℝ := ∑ n ∈ Icc 1 ⌊u⌋₊, a n
def Gchi (a : ℕ → ℂ) (S : ℂ) (y : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊y⌋₊, a n * ((y / (n : ℝ) - 1 : ℝ) : ℂ) - (y : ℂ) * S
def Gone (a : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊y⌋₊, a n * (y / (n : ℝ) - 1) - y * (Real.log y - 1 - Real.eulerMascheroniConstant)
def SmoothedRemainderIntegralFormula : Prop :=
  ∀ (a : ℕ → ℂ) (S : ℂ),
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, a n / (n : ℂ)) atTop (𝓝 S) →
    ∀ y : ℝ, 1 ≤ y → ∃ I : ℂ,
      Tendsto (fun U : ℝ => ∫ u in y..U, psum a u / (u : ℂ) ^ 2) atTop (𝓝 I) ∧
      Gchi a S y = -(y : ℂ) * I
def SmoothedRemainderRealIntegralFormula : Prop :=
  ∀ a : ℕ → ℝ,
    Tendsto (fun U : ℝ => ∫ u in (1 : ℝ)..U, (psumR a u - u) / u ^ 2) atTop
      (𝓝 (-1 - Real.eulerMascheroniConstant)) →
    ∀ y : ℝ, 1 ≤ y → ∃ I : ℝ,
      Tendsto (fun U : ℝ => ∫ u in y..U, (psumR a u - u) / u ^ 2) atTop (𝓝 I) ∧
      Gone a y = -y * I
def WeightedSumTendsto : Prop :=
  ∀ (a : ℕ → ℂ) (S : ℂ),
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, a n / (n : ℂ)) atTop (𝓝 S) →
    ∀ y : ℝ, 1 ≤ y →
      Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, a n * ((min 1 (y / (n : ℝ)) : ℝ) : ℂ)) atTop
        (𝓝 (-Gchi a S y))
def SmoothedRemainderHasDerivBound : Prop :=
  ∀ CM : ℝ, (∀ y : ℝ, 1 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n / (n : ℝ) ≤ Real.log y + CM) →
    ∀ (a : ℕ → ℂ) (S : ℂ), (∀ n, ‖a n‖ ≤ Λ n) →
    ∀ y : ℝ, 1 ≤ y →
      HasDerivWithinAt (Gchi a S) (∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℂ) - S) (Set.Ici y) y ∧
      ‖∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℂ) - S‖ ≤ Real.log y + CM + ‖S‖
def SmoothedRemainderRealHasDerivBound : Prop :=
  ∀ (CM : ℝ) (a : ℕ → ℝ),
    (∀ y : ℝ, 1 ≤ y → |∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℝ) - Real.log y| ≤ CM) →
    ∀ y : ℝ, 1 ≤ y →
      HasDerivWithinAt (Gone a)
        (∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℝ) - Real.log y + Real.eulerMascheroniConstant) (Set.Ici y) y ∧
      |∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℝ) - Real.log y + Real.eulerMascheroniConstant| ≤
        CM + Real.eulerMascheroniConstant
def SmoothedRemainderScaling : Prop :=
  ∀ (a : ℕ → ℂ) (S : ℂ) (A w : ℝ), 0 < A → 0 < w →
    (w : ℂ) * Gchi a S (A / w) =
      ∑ n ∈ Icc 1 ⌊A / w⌋₊, a n * ((A / (n : ℝ) - w : ℝ) : ℂ) - (A : ℂ) * S
def SmoothedRemainderScaledDiffBound : Prop :=
  ∀ (a : ℕ → ℂ) (S : ℂ), (∀ y : ℝ, 0 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, ‖a n‖ ≤ 2 * y) →
    ∀ A w₁ w₂ : ℝ, 0 < A → 0 < w₁ → w₁ ≤ w₂ →
      ‖(w₂ : ℂ) * Gchi a S (A / w₂) - (w₁ : ℂ) * Gchi a S (A / w₁)‖ ≤ 3 * A * Real.log (w₂ / w₁)
def SmoothedRemainderRealScaledDiffBound : Prop :=
  ∀ a : ℕ → ℝ, (∀ n, 0 ≤ a n) → (∀ y : ℝ, 0 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, a n ≤ 2 * y) →
    ∀ A w₁ w₂ : ℝ, 0 < A → 0 < w₁ → w₁ ≤ w₂ →
      |w₂ * Gone a (A / w₂) - w₁ * Gone a (A / w₁)| ≤ 3 * A * Real.log (w₂ / w₁)
def GoodFor (Q : ℝ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ s : ℂ, 1 - 1 / 400 < s.re → |s.im| ≤ Q → ¬ Formalism.ZeroFreeDirichlet.IsLZero χ s
def ZeroPairs (σ Q : ℝ) : Set ((Σ q : ℕ, DirichletCharacter ℂ (q + 1)) × ℂ) :=
  {p | ((p.1.1 + 1 : ℕ) : ℝ) ≤ Q ∧ p.1.2.IsPrimitive ∧ σ < p.2.re ∧ |p.2.im| ≤ Q ∧
    Formalism.ZeroFreeDirichlet.IsLZero p.1.2 p.2}
def ZeroDensityBound (σ Q : ℝ) : Prop :=
  (((ZeroPairs σ Q).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (10 ^ 88 * (10 ^ 421 * Q ^ 99) ^ (1 - σ))
def BadChars (Q : ℝ) : Set (Σ q : ℕ, DirichletCharacter ℂ (q + 1)) :=
  {c | ((c.1 + 1 : ℕ) : ℝ) ≤ Q ∧ c.2.IsPrimitive ∧ c.2 ^ 2 = 1 ∧ ¬ GoodFor Q c.2}
def ExceptionalCharacterCountBound : Prop :=
  (∀ Q : ℝ, 3 ≤ Q → ZeroDensityBound (1 - 1 / 400) Q) →
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 3 ≤ Q →
      (((BadChars Q).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (C * Q ^ ((1 : ℝ) / 4))
def TailSumBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ C₁ c₁ CM : ℝ, 0 < C₁ → 0 < c₁ → 0 ≤ CM →
    ∃ x₀ C : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ Q : ℝ, 0 < Q → x ^ (ε / 6) ≤ Real.log Q → Real.log Q ≤ x ^ (ε / 4) →
      ∀ (a : ℕ → ℂ) (S : ℂ),
        Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, a n / (n : ℂ)) atTop (𝓝 S) →
        (∀ y : ℝ, 1 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, ‖a n‖ / (n : ℝ) ≤ Real.log y + CM) →
        (∀ u : ℝ, 2 ≤ u → ‖psum a u‖ ≤
          C₁ * (u ^ (1 - (1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + u / Q * Real.log (u * Q) ^ 2)) →
        (∀ u : ℝ, Real.exp (Real.log Q ^ 2) ≤ u →
          ‖psum a u‖ ≤ C₁ * u * Real.exp (-c₁ * Real.sqrt (Real.log u))) →
        ‖(x : ℂ) * (S - ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ))‖ ≤ x ^ ε ∧
        ‖S‖ ≤ C * Real.log x
def Li (X : ℝ) : ℝ := ∫ t in (2 : ℝ)..X, 1 / Real.log t
def Emain (θ : ℤ) (β X : ℝ) : ℝ := Li X - θ * Li (X ^ β)
def rhoErr (C c B X : ℝ) : ℝ :=
  C * Real.exp (-c * Real.log X / Real.log B) + C * Real.exp (-c * Real.sqrt (Real.log X))
def ShortIntervalLowerBound : Prop :=
  ∀ C₀ Cr cr cb : ℝ, 0 < C₀ → 0 < Cr → 0 < cr → 0 < cb →
    ∃ C₀' c : ℝ, C₀ ≤ C₀' ∧ 0 < c ∧
      ∀ (B G β : ℝ) (θ : ℤ) (π₁ π₂ : ℝ → ℕ),
        4 ≤ B → 1 ≤ G → G ≤ B → θ ∈ ({-1, 0, 1} : Set ℤ) →
        (θ ≠ 0 → 1 / 2 ≤ β ∧ β < 1 ∧ cb / (B ^ 2 * Real.log B) ≤ 1 - β) →
        (∀ Y : ℝ, 1 ≤ Y → (π₂ Y : ℝ) ≤ 2 * Real.sqrt Y) →
        (∀ Y : ℝ, B ^ C₀ ≤ Y →
          |G * ((π₁ Y : ℝ) + π₂ Y) - Emain θ β Y| ≤ rhoErr Cr cr B Y * Emain θ β Y) →
        ∀ X : ℝ, B ^ C₀' ≤ X →
          c * B ^ (-5 : ℝ) * X / Real.log X ≤ Emain θ β X ∧
          ∀ h : ℝ, h ≤ 1 → rhoErr Cr cr B X ≤ h / 100 → B ^ (7 : ℝ) ≤ h * X ^ ((1 : ℝ) / 3) →
            c * h * B ^ (-6 : ℝ) * X / Real.log X ≤ (π₁ (X * (1 + h)) : ℝ) - π₁ X
def PrimesAPInterval (C₀ Cr cr c : ℝ) : Prop :=
  ∀ (m a : ℕ), 3 ≤ m → Nat.Coprime a m → ∀ Y h : ℝ, (4 * (m : ℝ)) ^ C₀ ≤ Y → h ≤ 1 →
    rhoErr Cr cr (4 * m) Y ≤ h / 100 → (4 * (m : ℝ)) ^ (7 : ℝ) ≤ h * Y ^ ((1 : ℝ) / 3) →
    c * h * (4 * (m : ℝ)) ^ (-6 : ℝ) * Y / Real.log Y ≤
      (((Ioc ⌊Y⌋₊ ⌊Y * (1 + h)⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD m])).card : ℝ)
def PP (m₀ a₀ : ℕ) (X : ℝ) : Finset ℕ :=
  (Ioc ⌊Real.sqrt X⌋₊ ⌊X⌋₊).filter (fun q => q.Prime ∧ q ≡ a₀ [MOD m₀])
def PrimesInProgressionCountLowerBound : Prop :=
  ∀ C₀ Cr cr c : ℝ, 0 < C₀ → 0 < Cr → 0 < cr → 0 < c → PrimesAPInterval C₀ Cr cr c →
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ m₀ a₀ : ℕ, 3 ≤ m₀ → Nat.Coprime a₀ m₀ →
      ∀ X : ℝ, 0 < X → (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X → x ^ (ε / 6) ≤ Real.log X →
        X ^ ((9 : ℝ) / 10) ≤ ((PP m₀ a₀ X).card : ℝ)
def cn (x : ℝ) (n : ℕ) : ℝ := Λ n * min 1 (x / (n : ℝ))
def outPart (m₀ m : ℕ) : ℕ :=
  ∏ p ∈ m.primeFactors.filter (fun p => ¬ p ∣ m₀ ∧ Odd (m.factorization p)), p
def sqSum (x : ℝ) (κ : ℕ → ℂ) (q : ℕ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, (cn x n : ℂ) * κ n * (jacobiSym (n : ℤ) q : ℂ)
def JacobiTwistedMeanSquareBound : Prop :=
  (∀ y : ℝ, 0 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n ≤ 2 * y) →
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ C' c' : ℝ, 0 < C' → 0 < c' →
    ∃ x₀ C : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ (m₀ : ℕ) (PPs : Finset ℕ) (κ : ℕ → ℂ) (nStar : ℕ),
        8 ∣ m₀ → 0 < m₀ →
        (∀ p : ℕ, p.Prime → p ∣ m₀ → (p : ℝ) ≤ x ^ (ε / 5) ∨ x ^ (400 : ℝ) < p) →
        PPs.Nonempty → (∀ q ∈ PPs, q.Prime ∧ q % 4 = 3 ∧ x ^ (400 : ℝ) < q) →
        κ 1 = 1 → (∀ m n, κ (m * n) = κ m * κ n) → (∀ n, ‖κ n‖ ≤ 1) →
        (∀ n n' : ℕ, n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊ → n' ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊ →
          IsPrimePow n → IsPrimePow n' → outPart m₀ (n * n') ≠ 1 → outPart m₀ (n * n') ≠ nStar →
          |(∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)) / PPs.card| ≤
            C' * Real.exp (-c' * Real.log x ^ 2)) →
        (∑ q ∈ PPs, ‖sqSum x κ q‖ ^ 2) / PPs.card ≤ C * x * Real.log x
end Formalism.HermitianLattices.GL2PrimeSums


