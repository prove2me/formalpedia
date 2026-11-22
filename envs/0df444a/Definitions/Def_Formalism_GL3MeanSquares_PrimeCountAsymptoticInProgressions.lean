-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
-- name    : Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:48:35.746871+00:00
-- url     : https://prove2.me/theorems/1719407b-201c-49a6-b3f6-062177d494c5
-- title:
--   Prime Count Asymptotic In Progressions
-- statement:
--   Definitions and structural lemmas for Prime Count Asymptotic In Progressions, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/PrimeCountAsymptoticInProgressions.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
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
namespace Formalism.HermitianLattices.GL2a2
open Formalism.HermitianLattices.GL2PrimeSums
def LogDerivSeries : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) / (n : ℂ)) atTop
      (𝓝 (-(deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1)))
def PsiZeroConst : Prop :=
  Tendsto (fun U : ℝ => ∫ u in (1 : ℝ)..U, (psumR (fun n => Λ n) u - u) / u ^ 2) atTop
    (𝓝 (-1 - Real.eulerMascheroniConstant))
def SmoothedRemainderLipschitz : Prop :=
  ∀ CM : ℝ, (∀ y : ℝ, 1 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n / (n : ℝ) ≤ Real.log y + CM) →
    ∀ (a : ℕ → ℂ) (S : ℂ), (∀ n, ‖a n‖ ≤ Λ n) →
    ∀ y₁ y₂ : ℝ, 1 ≤ y₁ → y₁ ≤ y₂ →
      ‖Gchi a S y₂ - Gchi a S y₁‖ ≤ (Real.log y₂ + CM + ‖S‖) * (y₂ - y₁)
def SmoothedRemainderRealLipschitz : Prop :=
  ∀ (CM : ℝ) (a : ℕ → ℝ),
    (∀ y : ℝ, 1 ≤ y → |∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℝ) - Real.log y| ≤ CM) →
    ∀ y₁ y₂ : ℝ, 1 ≤ y₁ → y₁ ≤ y₂ →
      |Gone a y₂ - Gone a y₁| ≤ (CM + Real.eulerMascheroniConstant) * (y₂ - y₁)
def ZeroFreeSymmetric : Prop :=
  ∀ (Q : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ^ 2 = 1 → GoodFor Q χ →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| ≤ Q → Formalism.ZeroFreeDirichlet.IsLZero χ s →
      1 / 400 ≤ s.re ∧ s.re ≤ 1 - 1 / 400
def ZeroSumBoundSmall : Prop :=
  ∀ C₂ C₃ : ℝ, 0 < C₂ → 0 < C₃ → ∃ C₁ : ℝ, 0 < C₁ ∧
    ∀ (Q u : ℝ) (Zs : Multiset ℂ) (ψ : ℂ), 3 ≤ Q → 2 ≤ u →
      (∀ ρ ∈ Zs, ρ.re ≤ 1 - 1 / 400) →
      (Zs.map (fun ρ => 1 / ‖ρ‖)).sum ≤ C₂ * Real.log Q ^ 2 →
      ‖ψ + (Zs.map (fun ρ => (u : ℂ) ^ ρ / ρ)).sum‖ ≤
        C₃ * (u / Q * Real.log (u * Q) ^ 2 + Real.log (u * Q) ^ 2) →
      ‖ψ‖ ≤ C₁ * (u ^ (1 - (1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + u / Q * Real.log (u * Q) ^ 2)
def ZeroSumBoundLarge : Prop :=
  ∀ c C₂ : ℝ, 0 < c → 0 < C₂ → ∃ C₁ c₁ : ℝ, 0 < C₁ ∧ 0 < c₁ ∧
    ∀ (Q u : ℝ) (Zs : Multiset ℂ), 3 ≤ Q → Real.exp (Real.log Q ^ 2) ≤ u →
      (∀ ρ ∈ Zs, |ρ.im| ≤ Real.exp (Real.sqrt (Real.log u)) ∧
        ρ.re ≤ 1 - c / Real.log (Q * (|ρ.im| + 3))) →
      (Zs.map (fun ρ => 1 / ‖ρ‖)).sum ≤ C₂ * Real.log (Q * Real.exp (Real.sqrt (Real.log u))) ^ 2 →
      ‖(Zs.map (fun ρ => (u : ℂ) ^ ρ / ρ)).sum‖ ≤ C₁ * u * Real.exp (-c₁ * Real.sqrt (Real.log u))
def PartialSumIntegralBound : Prop :=
  ∀ C₁ c₁ : ℝ, 0 < C₁ → 0 < c₁ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (Q : ℝ) (a : ℕ → ℂ), 3 ≤ Q →
      (∀ u : ℝ, 2 ≤ u → ‖psum a u‖ ≤
        C₁ * (u ^ (1 - (1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + u / Q * Real.log (u * Q) ^ 2)) →
      (∀ u : ℝ, Real.exp (Real.log Q ^ 2) ≤ u →
        ‖psum a u‖ ≤ C₁ * u * Real.exp (-c₁ * Real.sqrt (Real.log u))) →
      ∀ Z U : ℝ, 2 ≤ Z → Z ≤ U →
        ‖psum a Z‖ / Z + (∫ u in Z..U, ‖psum a u‖ / u ^ 2) ≤
          C * (Z ^ (-(1 : ℝ) / 400) * Real.log (Z * Q) ^ 2 + Q ^ (-c))
def PrimeCountAsymptoticInProgressions (C₀ Cr cr cb : ℝ) : Prop :=
  ∀ m a : ℕ, 3 ≤ m → Nat.Coprime a m → ∃ (θ : ℤ) (β : ℝ), θ ∈ ({-1, 0, 1} : Set ℤ) ∧
    (θ ≠ 0 → 1 / 2 ≤ β ∧ β < 1 ∧ cb / ((4 * (m : ℝ)) ^ 2 * Real.log (4 * m)) ≤ 1 - β) ∧
    ∀ Y : ℝ, (4 * (m : ℝ)) ^ C₀ ≤ Y →
      |(m.totient : ℝ) * (((Icc 1 ⌊Y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD m])).card : ℝ) - Emain θ β Y|
        ≤ rhoErr Cr cr (4 * m) Y * Emain θ β Y
def ShortIntervalImpliesProgressions : Prop :=
  ShortIntervalLowerBound → ∀ C₀ Cr cr cb : ℝ, 0 < C₀ → 0 < Cr → 0 < cr → 0 < cb → PrimeCountAsymptoticInProgressions C₀ Cr cr cb →
    ∃ C₀' c : ℝ, 0 < C₀' ∧ 0 < c ∧ PrimesAPInterval C₀' Cr cr c
def KronOdd : Prop :=
  ∀ q n : ℕ, q % 4 = 3 → Odd n → jacobiSym (-(q : ℤ)) n = jacobiSym (n : ℤ) q
def KronTwo : Prop :=
  ∀ q : ℕ, q % 4 = 3 → ZMod.χ₈ ((-(q : ℤ) : ℤ) : ZMod 8) = jacobiSym 2 q
def ClassConst : Prop :=
  ∀ m₀ d q q' : ℕ, 8 ∣ m₀ → d ∣ m₀ → Squarefree d → Odd q → Odd q' → q ≡ q' [MOD m₀] →
    jacobiSym (d : ℤ) q = jacobiSym (d : ℤ) q'
def inPart (m₀ m : ℕ) : ℕ :=
  ∏ p ∈ m.primeFactors.filter (fun p => p ∣ m₀ ∧ Odd (m.factorization p)), p
def JacobiInOut : Prop :=
  ∀ m₀ m q : ℕ, 0 < m → Nat.Coprime m q →
    jacobiSym (m : ℤ) q = jacobiSym (inPart m₀ m : ℤ) q * jacobiSym (outPart m₀ m : ℤ) q
def LamSumZero : Prop :=
  ∀ m₀ s a₀ : ℕ, 0 < m₀ → 1 < s → Odd s → Squarefree s → Nat.Coprime s m₀ →
    ∑ b ∈ (range (m₀ * s)).filter (fun b => b ≡ a₀ [MOD m₀]), jacobiSym (b : ℤ) s = 0
def MuConst : Prop :=
  ∀ (F : Finset ℕ) (lam N η : ℕ → ℝ) (M ρ : ℝ), 0 ≤ M → 0 ≤ ρ → ρ < 1 →
    (∀ b ∈ F, |lam b| ≤ 1) → (∑ b ∈ F, lam b) = 0 → (∀ b ∈ F, |η b| ≤ ρ) →
    (∀ b ∈ F, N b = M * (1 + η b)) →
    |∑ b ∈ F, lam b * N b| / (∑ b ∈ F, N b) ≤ ρ / (1 - ρ)
def MuSmall : Prop :=
  ∀ (F : Finset ℕ) (lam N η θ : ℕ → ℝ) (T t δ ρ : ℝ), 0 ≤ T → 0 ≤ t → t ≤ δ → δ < 1 → 0 ≤ ρ → ρ < 1 →
    (∀ b ∈ F, |lam b| ≤ 1) → (∑ b ∈ F, lam b) = 0 → (∀ b ∈ F, |θ b| ≤ 1) → (∀ b ∈ F, |η b| ≤ ρ) →
    (∀ b ∈ F, N b = T * (1 - θ b * t) * (1 + η b)) →
    |∑ b ∈ F, lam b * N b| / (∑ b ∈ F, N b) ≤ (ρ * (1 + δ) + δ) / ((1 - δ) * (1 - ρ))
def MeanRemove : Prop :=
  ∀ (A A' : Finset ℕ) (f : ℕ → ℝ) (X : ℝ), 0 < X → A' ⊆ A →
    ((A \ A').card : ℝ) ≤ X ^ ((1 : ℝ) / 2) → X ^ ((9 : ℝ) / 10) ≤ (A.card : ℝ) → (∀ q ∈ A, |f q| ≤ 1) →
    |(∑ q ∈ A, f q) / (A.card : ℝ) - (∑ q ∈ A', f q) / (A'.card : ℝ)| ≤ 2 * X ^ (-(2 : ℝ) / 5)
def sP (x : ℝ) (p : ℕ) : ℝ :=
  ∑ i ∈ (Icc 1 ⌊x ^ (400 : ℝ)⌋₊).filter (fun i => p ^ i ≤ ⌊x ^ (400 : ℝ)⌋₊), cn x (p ^ i)
def Rsum (x : ℝ) (m₀ : ℕ) : ℝ :=
  (∑ n ∈ (Icc 1 ⌊x ^ (400 : ℝ)⌋₊).filter (fun n => IsSquare n), cn x n) +
    (∑ p ∈ m₀.primeFactors.filter (fun p => p ≤ ⌊x ^ (400 : ℝ)⌋₊), sP x p)
def SizeSumC : Prop :=
  (∀ y : ℝ, 0 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n ≤ 2 * y) →
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, cn x n ≤ C * x * Real.log x
def SizeSpAll : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ p : ℕ, p.Prime → sP x p ≤ C * Real.log x
def SizeSpLarge : Prop :=
  ∀ x : ℝ, 0 < x → ∀ p : ℕ, p.Prime → x < p → sP x p ≤ 2 * x * Real.log p / p
def SizeR : Prop :=
  (∀ y : ℝ, 0 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n ≤ 2 * y) →
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ x : ℝ, 2 ≤ x → ∀ m₀ : ℕ, 0 < m₀ →
      (∀ p : ℕ, p.Prime → p ∣ m₀ → (p : ℝ) ≤ x ^ (ε / 5) ∨ x ^ (400 : ℝ) < p) →
      Rsum x m₀ ≤ C * (x ^ ((1 : ℝ) / 2) + x ^ (ε / 5) * Real.log x)
def SizeSpSq : Prop :=
  (∀ y : ℝ, 0 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n ≤ 2 * y) →
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      ∑ p ∈ (Icc 1 ⌊x ^ (400 : ℝ)⌋₊).filter (fun p => p.Prime), sP x p ^ 2 ≤ C * x * Real.log x
end Formalism.HermitianLattices.GL2a2


