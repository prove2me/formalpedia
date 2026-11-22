-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
-- name    : Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:32:07.11521+00:00
-- url     : https://prove2.me/theorems/c1e8e67d-8a47-4f66-8be7-a71cc6e29245
-- title:
--   Second Estimate Of Interval Hypothesis
-- statement:
--   Definitions and structural lemmas for Second Estimate Of Interval Hypothesis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/SecondEstimateOfIntervalHypothesis.lean

import Mathlib
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction Classical
noncomputable section
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
def X1 (ε x : ℝ) : ℝ := Real.exp (x ^ (ε / 5))
def X2 (ε x : ℝ) : ℝ := Real.exp (x ^ (ε / 5) * Real.log x ^ 2)
def logDerivLAtOne {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ :=
  deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1
def Gchi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (y : ℝ) : ℂ :=
  (∑ n ∈ Icc 1 ⌊y⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((y / n - 1 : ℝ) : ℂ)) + (y : ℂ) * logDerivLAtOne χ
def G1 (y : ℝ) : ℝ :=
  (∑ n ∈ Icc 1 ⌊y⌋₊, Λ n * (y / n - 1)) - y * (Real.log y - 1 - Real.eulerMascheroniConstant)
def cN (x : ℝ) (n : ℕ) : ℝ := Λ n * min 1 (x / n)
def Sz {q : ℕ} (χ : DirichletCharacter ℂ q) (x z : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊z⌋₊, ((cN x n : ℝ) : ℂ) * χ (n : ZMod q)
def tailL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (z : ℝ) : ℂ :=
  - logDerivLAtOne χ - ∑ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) / (n : ℂ)
def qc (q : ℕ) [Fact q.Prime] : DirichletCharacter ℂ q :=
  (quadraticChar (ZMod q)).ringHomComp (Int.castRingHom ℂ)
def chi8 : DirichletCharacter ℂ 8 := ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)
def one1 : DirichletCharacter ℂ 1 := 1
instance neZeroMulPrime {t q : ℕ} [NeZero t] [Fact q.Prime] : NeZero (t * q) :=
  ⟨Nat.mul_ne_zero (NeZero.ne t) (Fact.out : q.Prime).ne_zero⟩
def tw {t : ℕ} (θ : DirichletCharacter ℂ t) (q : ℕ) [Fact q.Prime] : DirichletCharacter ℂ (t * q) :=
  DirichletCharacter.changeLevel (Dvd.intro q rfl) θ * DirichletCharacter.changeLevel (Dvd.intro_left t rfl) (qc q)
def ZeroFreeBox {N : ℕ} [NeZero N] (Q : ℝ) (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, 1 - 1 / 400 < s.re → |s.im| ≤ Q → DirichletCharacter.LFunction χ s ≠ 0
def GoodFor {N : ℕ} [NeZero N] (Q : ℝ) (χ : DirichletCharacter ℂ N) : Prop :=
  χ.IsPrimitive ∧ χ ^ 2 = 1 ∧ (N : ℝ) ≤ Q ∧ ZeroFreeBox Q χ
def PPset (m₀ a₀ : ℕ) (X : ℝ) : Finset ℕ :=
  (Icc 1 ⌊X⌋₊).filter (fun q => q.Prime ∧ q % m₀ = a₀ % m₀ ∧ X ^ (1 / 2 : ℝ) < (q : ℝ))
def oddM (y : ℝ) (q₁ : ℕ) : ℕ := q₁ * ∏ p ∈ (Icc 3 ⌊y⌋₊).filter Nat.Prime, p
def SplitsIn (d p : ℕ) : Prop :=
  ∃ r s : ZMod p, r ≠ s ∧ r ^ 2 - r + (((d + 1) / 4 : ℕ) : ZMod p) = 0 ∧ s ^ 2 - s + (((d + 1) / 4 : ℕ) : ZMod p) = 0
def IsNormOne (d N p : ℕ) : Prop :=
  ∃ u v : ℤ, (N : ℤ) ∣ u - 1 ∧ (N : ℤ) ∣ v ∧ (p : ℤ) = u ^ 2 + u * v + (((d + 1) / 4 : ℕ) : ℤ) * v ^ 2
def normPrimes (d N : ℕ) (lo hi : ℝ) : Finset ℕ :=
  (Icc 1 ⌊hi⌋₊).filter (fun p => p.Prime ∧ lo < (p : ℝ) ∧ IsNormOne d N p)
def rho (c Cρ B X : ℝ) : ℝ :=
  Cρ * Real.exp (-c * Real.log X / Real.log B) + Cρ * Real.exp (-c * Real.log X ^ (1 / 2 : ℝ))
def BoxCountHyp (C : ℝ) : Prop :=
  ∀ (t : ℕ) [NeZero t] (θ : DirichletCharacter ℂ t) (Q : ℝ) (S : Finset ℕ), θ.IsPrimitive → θ ^ 2 = 1 →
    (∀ q ∈ S, ∃ _ : Fact q.Prime, q % 4 = 3 ∧ q.Coprime t ∧ ((t * q : ℕ) : ℝ) ≤ Q ∧ ¬ ZeroFreeBox Q (tw θ q)) →
    (S.card : ℝ) ≤ C * Q ^ (1 / 4 : ℝ)
def BoxTailHyp (ε C x₀ : ℝ) : Prop :=
  ∀ (x Q : ℝ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), x₀ ≤ x → x ^ (ε / 6) ≤ Real.log Q →
    Real.log Q ≤ x ^ (ε / 4) → χ ≠ 1 → GoodFor Q χ →
    ‖(x : ℂ) * tailL χ (x ^ 400)‖ ≤ x ^ ε ∧ ‖logDerivLAtOne χ‖ ≤ C * Real.log x
def MeanSquareHyp (ε C x₀ : ℝ) : Prop :=
  ∀ (x X : ℝ) (m₀ a₀ : ℕ) (κ : ℕ → ℂ), x₀ ≤ x → 8 ∣ m₀ →
    (∀ p : ℕ, p.Prime → p ∣ m₀ → (p : ℝ) ≤ x ^ (ε / 5) ∨ x ^ 400 < (p : ℝ)) → a₀.Coprime m₀ → a₀ % 4 = 3 →
    (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X → x ^ (ε / 6) ≤ Real.log X →
    (∀ n, ‖κ n‖ ≤ 1) → (∀ a b, κ (a * b) = κ a * κ b) →
    X ^ (9 / 10 : ℝ) ≤ ((PPset m₀ a₀ X).card : ℝ) ∧
    (∑ q ∈ PPset m₀ a₀ X,
        ‖∑ n ∈ Icc 1 ⌊x ^ 400⌋₊, ((cN x n : ℝ) : ℂ) * κ n * ((jacobiSym (n : ℤ) q : ℤ) : ℂ)‖ ^ 2) ≤
      C * x * Real.log x * ((PPset m₀ a₀ X).card : ℝ)
def IntervalHyp (C₀ c Cρ c₃ : ℝ) : Prop :=
  ∀ (d N : ℕ) (X h : ℝ), d.Prime → d % 4 = 3 → 1 ≤ N → (4 * (d : ℝ) * (N : ℝ) ^ 2) ^ C₀ ≤ X →
    rho c Cρ (4 * (d : ℝ) * (N : ℝ) ^ 2) X ≤ h / 100 → 0 < h → h ≤ 1 →
    (4 * (d : ℝ) * (N : ℝ) ^ 2) ^ 7 ≤ h * X ^ (1 / 3 : ℝ) →
    c₃ * h * (4 * (d : ℝ) * (N : ℝ) ^ 2) ^ (-6 : ℝ) * X / Real.log X ≤ ((normPrimes d N X (X * (1 + h))).card : ℝ)
def UptoHyp (C₀ c Cρ c₃ : ℝ) : Prop :=
  ∀ (d N : ℕ) (X : ℝ), d.Prime → d % 4 = 3 → 1 ≤ N → (4 * (d : ℝ) * (N : ℝ) ^ 2) ^ C₀ ≤ X →
    rho c Cρ (4 * (d : ℝ) * (N : ℝ) ^ 2) X ≤ 1 / 2 →
    c₃ * (4 * (d : ℝ) * (N : ℝ) ^ 2) ^ (-6 : ℝ) * X / Real.log X - 2 * X ^ (1 / 2 : ℝ) ≤
      2 * ((normPrimes d N 0 X).card : ℝ)
def WGIdentity : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (a w : ℝ) (M : ℕ), 0 < a → 0 < w → ⌊a / w⌋₊ ≤ M →
    (w : ℂ) * Gchi χ (a / w) =
      (∑ n ∈ Icc 1 M, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((max (a / n - w) 0 : ℝ) : ℂ)) + (a : ℂ) * logDerivLAtOne χ
def WGLipschitz : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (a w w' : ℝ), 0 < a → 0 < w → w ≤ w' →
    ‖(w' : ℂ) * Gchi χ (a / w') - (w : ℂ) * Gchi χ (a / w)‖ ≤ Chebyshev.psi (a / w) * (w' - w)
def WeightedSumLipschitzTrivial : Prop :=
  ∀ (a w w' : ℝ), 0 < a → 0 < w → w ≤ w' →
    |w' * G1 (a / w') - w * G1 (a / w)| ≤ (Chebyshev.psi (a / w) + a / w) * (w' - w)
def CharacterSumLipschitzOfChebyshev : Prop :=
  (∀ y : ℝ, 0 ≤ y → Chebyshev.psi y ≤ 2 * y) →
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (a w w' : ℝ), 0 < a → 0 < w → w ≤ w' →
      ‖(w' : ℂ) * Gchi χ (a / w') - (w : ℂ) * Gchi χ (a / w)‖ ≤ 3 * a / w * (w' - w)) ∧
    (∀ (a w w' : ℝ), 0 < a → 0 < w → w ≤ w' →
      |w' * G1 (a / w') - w * G1 (a / w)| ≤ 3 * a / w * (w' - w))
def GFiniteSplit : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x z : ℝ), 0 < x → x ≤ z →
    Gchi χ x = - Sz χ x z - (x : ℂ) * tailL χ z
def MarkovDiscard : Prop :=
  ∀ (P B : Finset ℕ) (J : ℕ) (S : Fin J → ℕ → ℝ) (V t : ℝ), 0 < t →
    (∀ j, (∑ q ∈ P, S j q ^ 2) ≤ V * (P.card : ℝ)) →
    (J : ℝ) * (V / t ^ 2) * (P.card : ℝ) + (B.card : ℝ) < (P.card : ℝ) →
    ∃ q ∈ P, q ∉ B ∧ ∀ j, |S j q| ≤ t
def UnitModulusIncrementConditions : Prop :=
  ∀ ε C : ℝ, 0 < ε → ε ≤ 1 → 0 < C → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    x ^ 400 < X1 ε x ^ (1 / 2 : ℝ) ∧ 2 ≤ x ^ (ε / 5) ∧
    (1 / 4) * Real.log x ^ 2 * Real.log 8 ≤ Real.log (X1 ε x) ∧
    Real.log x ^ 2 * Real.log (8 * (x ^ 400) ^ 2) ≤ Real.log (X1 ε x) ∧
    x ^ (ε / 6) ≤ Real.log (X1 ε x) ∧
    x ^ (ε / 6) ≤ Real.log (8 * X1 ε x) ∧ Real.log (8 * X1 ε x) ≤ x ^ (ε / 4) ∧
    C * x * Real.log x / (x ^ (1 / 2 + ε) / 2) ^ 2 ≤ x ^ (-ε) ∧ x ^ (-ε) ≤ 1 / 8 ∧
    2 * (C * (8 * X1 ε x) ^ (1 / 4 : ℝ)) ≤ X1 ε x ^ (9 / 10 : ℝ) / 2
def PrimorialBound : Prop :=
  ∀ (y : ℝ) (q₁ : ℕ), 0 ≤ y → (q₁ : ℝ) ≤ Real.exp y → ((oddM y q₁ : ℕ) : ℝ) ≤ Real.exp (3 * y)
def ClassAdmissible : Prop :=
  ∀ (y z : ℝ) (q₁ : ℕ), 2 ≤ y → q₁.Prime → q₁ % 8 = 3 → z < (q₁ : ℝ) →
    ∃ a₀ : ℕ, a₀ % 16 = 7 ∧ oddM y q₁ ∣ a₀ + 1 ∧ a₀.Coprime (16 * oddM y q₁) ∧ a₀ % 4 = 3 ∧ 8 ∣ 16 * oddM y q₁ ∧
      (∀ p : ℕ, p.Prime → p ∣ 16 * oddM y q₁ → (p : ℝ) ≤ y ∨ z < (p : ℝ)) ∧
      ∀ d : ℕ, d % (16 * oddM y q₁) = a₀ % (16 * oddM y q₁) → d % 16 = 7 ∧ oddM y q₁ ∣ d + 1
def ClassSplit : Prop :=
  ∀ (y : ℝ) (q₁ d : ℕ), q₁.Prime → d % 16 = 7 → oddM y q₁ ∣ d + 1 →
    SplitsIn d q₁ ∧ ∀ p : ℕ, p.Prime → (p : ℝ) ≤ y → SplitsIn d p
def IncrementSizeConditions : Prop :=
  ∀ ε C : ℝ, 0 < ε → ε ≤ 1 → 0 < C → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    (∀ m₀ : ℝ, 0 < m₀ → m₀ ≤ 16 * Real.exp (3 * x ^ (ε / 5)) →
      (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log (X2 ε x)) ∧
    x ^ (ε / 6) ≤ Real.log (X2 ε x) ∧
    (8 * X1 ε x * X2 ε x) ^ (1 / 4 : ℝ) ≤ X2 ε x ^ (1 / 3 : ℝ) ∧
    x ^ (ε / 6) ≤ Real.log (8 * X1 ε x * X2 ε x) ∧ Real.log (8 * X1 ε x * X2 ε x) ≤ x ^ (ε / 4) ∧
    4 * (C * (8 * X1 ε x * X2 ε x) ^ (1 / 4 : ℝ)) ≤ X2 ε x ^ (9 / 10 : ℝ) / 2 ∧
    x ^ (1 / 2 + ε) / 2 + x ^ ε ≤ x ^ (1 / 2 + ε)
def TwEval : Prop :=
  ∀ (t : ℕ) (θ : DirichletCharacter ℂ t) (q : ℕ) [Fact q.Prime] (n : ℕ),
    tw θ q (n : ZMod (t * q)) = θ (n : ZMod t) * ((jacobiSym (n : ℤ) q : ℤ) : ℂ)
def TwPrimitive : Prop :=
  (chi8.IsPrimitive ∧ chi8 ^ 2 = 1) ∧
  ∀ (t : ℕ) (θ : DirichletCharacter ℂ t) (q : ℕ) [Fact q.Prime], θ.IsPrimitive → q ≠ 2 → q.Coprime t →
    (tw θ q).IsPrimitive ∧ tw θ q ≠ 1 ∧ (θ ^ 2 = 1 → tw θ q ^ 2 = 1)
def ExistsSplitGoodPrimePair (ε C x : ℝ) : Prop :=
  ∃ (q₁ d : ℕ) (_ : Fact q₁.Prime) (_ : Fact d.Prime),
    q₁ % 8 = 3 ∧ d % 16 = 7 ∧
    X1 ε x ^ (1 / 2 : ℝ) < (q₁ : ℝ) ∧ (q₁ : ℝ) ≤ X1 ε x ∧ X2 ε x ^ (1 / 2 : ℝ) < (d : ℝ) ∧ (d : ℝ) ≤ X2 ε x ∧
    SplitsIn d q₁ ∧ (∀ p : ℕ, p.Prime → (p : ℝ) ≤ x ^ (ε / 5) → SplitsIn d p) ∧
    GoodFor (8 * X1 ε x) (tw one1 q₁) ∧ GoodFor (8 * X1 ε x) (tw chi8 q₁) ∧
    GoodFor (8 * X1 ε x * X2 ε x) (tw one1 d) ∧ GoodFor (8 * X1 ε x * X2 ε x) (tw chi8 d) ∧
    GoodFor (8 * X1 ε x * X2 ε x) (tw (tw one1 q₁) d) ∧ GoodFor (8 * X1 ε x * X2 ε x) (tw (tw chi8 q₁) d) ∧
    (‖Gchi (tw one1 q₁) x‖ ≤ x ^ (1 / 2 + ε) ∧ ‖logDerivLAtOne (tw one1 q₁)‖ ≤ C * Real.log x) ∧
    (‖Gchi (tw one1 d) x‖ ≤ x ^ (1 / 2 + ε) ∧ ‖logDerivLAtOne (tw one1 d)‖ ≤ C * Real.log x) ∧
    (‖Gchi (tw (tw one1 q₁) d) x‖ ≤ x ^ (1 / 2 + ε) ∧ ‖logDerivLAtOne (tw (tw one1 q₁) d)‖ ≤ C * Real.log x)
def PrimePairOfBoxAndMeanSquareHypotheses : Prop :=
  ∀ ε C₂ C₂' x₂ C₄ x₄ : ℝ, 0 < ε → ε ≤ 1 → 0 < C₂ → 0 < C₄ →
    BoxCountHyp C₂ → BoxTailHyp ε C₂' x₂ → MeanSquareHyp ε C₄ x₄ →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ExistsSplitGoodPrimePair ε C₂' x
def LogNE : Prop :=
  ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ n q₁ d : ℕ, 1 ≤ n → (n : ℝ) ≤ x ^ A →
    X1 ε x ^ (1 / 2 : ℝ) < (q₁ : ℝ) → (q₁ : ℝ) ≤ X1 ε x → X2 ε x ^ (1 / 2 : ℝ) < (d : ℝ) → (d : ℝ) ≤ X2 ε x →
    x ^ (ε / 5) / 2 < Real.log q₁ ∧ Real.log q₁ ≤ x ^ (ε / 5) ∧
    x ^ (ε / 5) * Real.log x ^ 2 / 2 < Real.log d ∧ Real.log d ≤ x ^ (ε / 5) * Real.log x ^ 2 ∧
    Real.log ((4 * n * q₁ * d : ℕ) : ℝ) ≤ 2 * x ^ (ε / 5) * Real.log x ^ 2
def ExpSplit : Prop :=
  ∀ c v lam : ℝ, 0 < c → 0 ≤ v → 0 < lam →
    Real.exp (-c * v / (lam + Real.sqrt v)) ≤ Real.exp (-c * v / (2 * lam)) + Real.exp (-c * Real.sqrt v / 2)
def SmoothingSizeBounds : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ y lam : ℝ, Real.exp (x ^ (ε / 3)) / 3 ≤ y → 0 < lam →
    lam ≤ 2 * x ^ (ε / 5) * Real.log x ^ 2 →
    x ^ (ε / 3) / 2 ≤ Real.log y ∧ x ^ (2 * ε / 15) / (4 * Real.log x ^ 2) ≤ Real.log y / lam ∧
    x ^ (ε / 6) / 2 ≤ Real.sqrt (Real.log y)
def ThinIntegral : Prop :=
  ∀ ε c : ℝ, 0 < ε → 0 < c → ∃ c' x₀ : ℝ, 0 < c' ∧ ∀ x : ℝ, x₀ ≤ x → ∀ V lam : ℝ, x ^ (ε / 3) / 2 ≤ V → 1 ≤ lam →
    lam ≤ 2 * x ^ (ε / 5) * Real.log x ^ 2 →
    MeasureTheory.IntegrableOn (fun v : ℝ => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) (Set.Ioi V) ∧
    (∫ v in Set.Ioi V, (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) ≤ Real.exp (-c' * x ^ (ε / 8))
def TailIntegralBoundOfPsiBound : Prop :=
  ∀ ε c C : ℝ, 0 < ε → 0 < c → 0 < C → ∃ c' x₀ : ℝ, 0 < c' ∧ ∀ x : ℝ, x₀ ≤ x → ∀ (y lam : ℝ) (psi0 : ℝ → ℂ),
    Real.exp (x ^ (ε / 3)) / 3 ≤ y → 1 ≤ lam → lam ≤ 2 * x ^ (ε / 5) * Real.log x ^ 2 →
    (∀ u : ℝ, y ≤ u → ‖psi0 u‖ ≤
      C * u * (Real.log u + lam) ^ 2 * Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u)))) →
    ‖(y : ℂ) * ∫ u in Set.Ioi y, psi0 u / (u : ℂ) ^ 2‖ ≤ y * Real.exp (-c' * x ^ (ε / 8))
def CharacterSmoothingEstimate : Prop :=
  ∀ ε c C : ℝ, 0 < ε → 0 < c → 0 < C → ∃ c' x₀ : ℝ, 0 < c' ∧ ∀ x : ℝ, x₀ ≤ x → ∀ y lam : ℝ,
    Real.exp (x ^ (ε / 3)) / 3 ≤ y → 1 ≤ lam → lam ≤ 2 * x ^ (ε / 5) * Real.log x ^ 2 →
    (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      Gchi χ y = -((y : ℂ) * ∫ u in Set.Ioi y, Formalism.ZeroFreeDirichlet.psiChi χ u / (u : ℂ) ^ 2) →
      (∀ u : ℝ, y ≤ u → ‖Formalism.ZeroFreeDirichlet.psiChi χ u‖ ≤
        C * u * (Real.log u + lam) ^ 2 * Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u)))) →
      ‖Gchi χ y‖ ≤ y * Real.exp (-c' * x ^ (ε / 8))) ∧
    (G1 y = -(y * ∫ u in Set.Ioi y, (Chebyshev.psi u - u) / u ^ 2) →
      (∀ u : ℝ, y ≤ u → |Chebyshev.psi u - u| ≤
        C * u * (Real.log u + lam) ^ 2 * Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u)))) →
      |G1 y| ≤ y * Real.exp (-c' * x ^ (ε / 8)))
def NoExcOfBox : Prop :=
  ∀ (c₁ Q : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 0 ≤ Q → c₁ / Real.log (2 * q) < 1 / 400 →
    ZeroFreeBox Q χ → (∀ s : ℂ, Formalism.ZeroFreeDirichlet.InRegion c₁ q s → Formalism.ZeroFreeDirichlet.IsLZero χ s → s.im = 0) →
    Formalism.ZeroFreeDirichlet.ExcZeros c₁ χ ∅
def RealCharCount : Prop :=
  ∀ e : ℕ, 1 ≤ e → (Finset.univ.filter (fun g : ZMod 2 × ZMod 2 × ZMod (2 ^ e) => g + g = 0)).card = 8
def NormOneCongr : Prop :=
  ∀ d N p : ℕ, IsNormOne d N p → ((p : ℤ) ≡ 1 [ZMOD (N : ℤ)]) ∧ ∀ χ : DirichletCharacter ℂ N, χ (p : ZMod N) = 1
def NormOneCongrGeneral : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (N : ℤ) (α : NumberField.RingOfIntegers K),
    Algebra.norm ℤ (1 + (N : NumberField.RingOfIntegers K) * α) ≡ 1 [ZMOD N]
def ExponentialRangeSizeConditions : Prop :=
  ∀ ε C C_B C₀ c Cρ c₃ : ℝ, 0 < ε → 0 < C → 0 < C_B → 0 < C₀ → 0 < c → 0 < Cρ → 0 < c₃ →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ B Y : ℝ, 4 ≤ B → Real.log B ≤ C_B * x ^ (ε / 5) * Real.log x ^ 2 →
      Real.exp (8 * x ^ ε) ≤ Y → Y ≤ Real.exp (C * x ^ ε) →
      B ^ C₀ ≤ Y ∧ rho c Cρ B Y ≤ 1 / 100 ∧ B ^ 7 ≤ 1 * Y ^ (1 / 3 : ℝ) ∧
      Y ^ (9 / 10 : ℝ) ≤ c₃ * 1 * B ^ (-6 : ℝ) * Y / Real.log Y
def PrimeEstimateOfIntervalHyp : Prop :=
  ∀ C₀ c Cρ c₃ : ℝ, 0 < C₀ → 0 < c → 0 < Cρ → 0 < c₃ → IntervalHyp C₀ c Cρ c₃ →
    ∀ ε C : ℝ, 0 < ε → 0 < C → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (d NE : ℕ) (k Y : ℝ), d.Prime → d % 4 = 3 →
      (d : ℝ) ≤ X2 ε x → 1 ≤ NE → Real.log NE ≤ 2 * x ^ (ε / 5) * Real.log x ^ 2 → 1 ≤ k →
      (k * Real.exp (x ^ ε)) ^ 8 ≤ Y → Y ≤ Real.exp (x ^ ε) ^ C →
      Y ^ (9 / 10 : ℝ) ≤ ((normPrimes d NE Y (2 * Y)).card : ℝ)
def ExclusionInequalities : Prop :=
  ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (r : ℕ) (Y : ℝ), (r : ℝ) ≤ x ^ A →
    Real.exp (8 * x ^ ε) ≤ Y →
    (3 * (r : ℝ) + 1) * (4 * (r : ℝ) ^ 2 * Y ^ (3 / 4 : ℝ) + 1) ≤ Y ^ (4 / 5 : ℝ) ∧
    Y ^ (4 / 5 : ℝ) + 1 < Y ^ (9 / 10 : ℝ)
def ChoiceOfTwoPrimes : Prop :=
  ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (r : ℕ) (Y : ℝ) (GG : Finset ℕ) (excl : ℕ → Finset ℕ),
    (r : ℝ) ≤ x ^ A → Real.exp (8 * x ^ ε) ≤ Y → Y ^ (9 / 10 : ℝ) ≤ (GG.card : ℝ) →
    (∀ g ∈ GG, ((excl g).card : ℝ) ≤ (3 * (r : ℝ) + 1) * (4 * (r : ℝ) ^ 2 * Y ^ (3 / 4 : ℝ) + 1)) →
    ∃ g₁ ∈ GG, ∃ g₂ ∈ GG, g₂ ≠ g₁ ∧ g₂ ∉ excl g₁
def ReciprocalWeightSizeConditions : Prop :=
  ∀ ε δ A integralAdeleSpan C_B C₀ c Cρ : ℝ, 0 < ε → 0 < δ → 0 < A → 0 < integralAdeleSpan → 0 < C_B → 0 < C₀ → 0 < c → 0 < Cρ →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ B T m fk : ℝ, 4 ≤ B → Real.log B ≤ C_B * x ^ ε → x ^ δ ≤ m → 1 ≤ fk → fk ≤ x ^ A →
      integralAdeleSpan * m * x ^ ε ≤ Real.log T → 0 < T →
      B ^ C₀ ≤ T ∧ rho c Cρ B T ≤ 1 / fk / 100 ∧ B ^ 7 ≤ 1 / fk * T ^ (1 / 3 : ℝ)
def SecondEstimateOfIntervalHypothesis : Prop :=
  ∀ C₀ c Cρ c₃ : ℝ, 0 < C₀ → 0 < c → 0 < Cρ → 0 < c₃ → IntervalHyp C₀ c Cρ c₃ →
    ∀ ε δ A integralAdeleSpan C_Y : ℝ, 0 < ε → 0 < δ → 0 < A → 0 < integralAdeleSpan → 0 < C_Y → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ (d NE g₁ g₂ : ℕ) (m fk Ts : ℝ), d.Prime → d % 4 = 3 → (d : ℝ) ≤ X2 ε x → 1 ≤ NE →
      Real.log NE ≤ 2 * x ^ (ε / 5) * Real.log x ^ 2 → 1 ≤ g₁ → 1 ≤ g₂ → Real.log g₁ ≤ C_Y * x ^ ε →
      Real.log g₂ ≤ C_Y * x ^ ε → x ^ δ ≤ m → 1 ≤ fk → fk ≤ x ^ A → 0 < Ts → integralAdeleSpan * m * x ^ ε ≤ Real.log Ts →
      ∃ T : ℕ, T.Prime ∧ Ts ≤ (T : ℝ) ∧ (T : ℝ) ≤ Ts * (1 + 1 / fk) ∧ IsNormOne d (NE * (g₁ * g₂) ^ 2) T
def TstarSize : Prop :=
  ∀ ε δ A C : ℝ, 0 < ε → 0 < δ → 0 < A → 0 < C → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ m k n : ℝ, 1 ≤ n → n ≤ x ^ A →
    x ^ δ ≤ m → m ^ 2 * x ^ ε ≤ k →
    m * x ^ ε / 2 ≤
      m * Real.log (x * Real.exp (x ^ ε) / Real.exp (x ^ (ε / 3)) / (x * n)) - C * (x ^ ε + m ^ 2 * x ^ ε / k) ∧
    ∀ Xu Gam fk : ℝ, 0 < Xu → 1 ≤ Gam → 0 < fk → m * x ^ ε / 2 ≤ Real.log Xu → Real.log Gam ≤ fk →
      m * x ^ ε / 4 ≤ Real.log (Xu * Gam ^ (-2 / fk))
def ChoiceOfExponentConstant : Prop :=
  ∀ C C₀ c Cρ c₃ : ℝ, 0 < C → 0 < C₀ → 0 < c → 0 < Cρ → 0 < c₃ → ∃ C₁ : ℝ, C₀ ≤ C₁ ∧ ∀ B : ℝ, 12 ≤ B →
    rho c Cρ B (B ^ C₁) ≤ 1 / 2 ∧
    2 * B ^ C ≤ c₃ * B ^ (-6 : ℝ) * B ^ C₁ / Real.log (B ^ C₁) - 2 * (B ^ C₁) ^ (1 / 2 : ℝ)
def PrimeBoundOfUptoHyp : Prop :=
  ∀ C₀ c Cρ c₃ : ℝ, 0 < C₀ → 0 < c → 0 < Cρ → 0 < c₃ → UptoHyp C₀ c Cρ c₃ →
    ∀ C : ℝ, 0 < C → ∃ C' : ℝ, 0 < C' ∧ ∀ d NE M₀ J : ℕ, d.Prime → d % 4 = 3 → 4 * d ≤ NE → 1 ≤ M₀ →
      (M₀ : ℝ) ≤ (NE : ℝ) ^ C → (J : ℝ) ≤ (NE : ℝ) ^ C →
      ∃ S : Finset ℕ, S.card = J ∧ ∀ p ∈ S, p.Prime ∧ IsNormOne d (M₀ * NE) p ∧ (p : ℝ) ≤ (NE : ℝ) ^ C'
def LogPrimeSizeBound : Prop :=
  ∀ ε C' : ℝ, 0 < ε → 0 < C' → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ NE p : ℝ, 1 ≤ NE → 0 < p →
    Real.log NE ≤ 2 * x ^ (ε / 5) * Real.log x ^ 2 → p ≤ NE ^ C' →
    Real.log p ≤ C' * Real.log NE ∧ C' * Real.log NE ≤ 2 * C' * x ^ (ε / 5) * Real.log x ^ 2 ∧
    2 * C' * x ^ (ε / 5) * Real.log x ^ 2 ≤ x ^ ε
def IsNormOneIff : Prop :=
  ∀ d N p : ℕ, IsNormOne d N p ↔
    ∃ π : QuadraticAlgebra ℤ (-(((d + 1) / 4 : ℕ) : ℤ)) 1,
      (((N : ℤ) : QuadraticAlgebra ℤ (-(((d + 1) / 4 : ℕ) : ℤ)) 1) ∣ π - 1) ∧ QuadraticAlgebra.norm π = (p : ℤ)
def TypeSign : Prop :=
  ∀ q₁ d : ℕ, q₁.Prime → d.Prime → q₁ % 8 = 3 → d % 16 = 7 → q₁ ∣ d + 1 →
    jacobiSym (-(d : ℤ)) q₁ = 1 ∧ jacobiSym (-(q₁ : ℤ)) d = -1
def TypeSignOfSplit : Prop :=
  ∀ q₁ d : ℕ, q₁ % 4 = 3 → d % 4 = 3 → jacobiSym (-(d : ℤ)) q₁ = 1 → jacobiSym (-(q₁ : ℤ)) d = -1
def SplitsIffJacobi : Prop :=
  ∀ d p : ℕ, p.Prime → d % 4 = 3 →
    (p ≠ 2 → (SplitsIn d p ↔ jacobiSym (-(d : ℤ)) p = 1)) ∧ (SplitsIn d 2 ↔ d % 8 = 7)
end Formalism.HermitianLattices.ZeroFreeRegionGL2


