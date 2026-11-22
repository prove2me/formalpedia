-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_SmoothedRemainderRealIntegralFormula
-- name    : Formalism_SizeWindowBrackets_SmoothedRemainderRealIntegralFormula
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:01:51.447039+00:00
-- url     : https://prove2.me/theorems/7e8eb602-f4f4-4b89-b10b-de1c680a9028
-- title:
--   Smoothed Remainder Real Integral Formula
-- statement:
--   Definitions and structural lemmas for Smoothed Remainder Real Integral Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/SmoothedRemainderRealIntegralFormula.lean

import Definitions.Def_Formalism_SizeWindowBrackets_Chain2aCoreNoAnalytic
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAP
import Definitions.Def_Formalism_ZeroFreeRegion_Statement
import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology ArithmeticFunction
noncomputable section
namespace Formalism.LFunctionChainParameters.LBr2
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds
def X1 (ε x : ℝ) : ℝ := Real.exp (x ^ (ε / 5))
def X2 (ε x : ℝ) : ℝ := Real.exp (x ^ (ε / 5) * Real.log x ^ 2)
def logDerivLAtOne {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ :=
  deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1
def Gchi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (y : ℝ) : ℂ :=
  (∑ n ∈ Icc 1 ⌊y⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((y / n - 1 : ℝ) : ℂ)) + (y : ℂ) * logDerivLAtOne χ
def G1 (y : ℝ) : ℝ :=
  (∑ n ∈ Icc 1 ⌊y⌋₊, Λ n * (y / n - 1)) - y * (Real.log y - 1 - Real.eulerMascheroniConstant)
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
def SplitsIn (d p : ℕ) : Prop :=
  ∃ r s : ZMod p, r ≠ s ∧ r ^ 2 - r + (((d + 1) / 4 : ℕ) : ZMod p) = 0 ∧ s ^ 2 - s + (((d + 1) / 4 : ℕ) : ZMod p) = 0
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
def TwPrimitive : Prop :=
  (chi8.IsPrimitive ∧ chi8 ^ 2 = 1) ∧
  ∀ (t : ℕ) (θ : DirichletCharacter ℂ t) (q : ℕ) [Fact q.Prime], θ.IsPrimitive → q ≠ 2 → q.Coprime t →
    (tw θ q).IsPrimitive ∧ tw θ q ≠ 1 ∧ (θ ^ 2 = 1 → tw θ q ^ 2 = 1)
def TwEval : Prop :=
  ∀ (t : ℕ) (θ : DirichletCharacter ℂ t) (q : ℕ) [Fact q.Prime] (n : ℕ),
    tw θ q (n : ZMod (t * q)) = θ (n : ZMod t) * ((jacobiSym (n : ℤ) q : ℤ) : ℂ)
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
def psumA (a : ℕ → ℂ) (u : ℝ) : ℂ := ∑ n ∈ Icc 1 ⌊u⌋₊, a n
def psumRA (a : ℕ → ℝ) (u : ℝ) : ℝ := ∑ n ∈ Icc 1 ⌊u⌋₊, a n
def GchiA (a : ℕ → ℂ) (S : ℂ) (y : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊y⌋₊, a n * ((y / (n : ℝ) - 1 : ℝ) : ℂ) - (y : ℂ) * S
def GoneA (a : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊y⌋₊, a n * (y / (n : ℝ) - 1) - y * (Real.log y - 1 - Real.eulerMascheroniConstant)
def SmoothedRemainderIntegralFormula : Prop :=
  ∀ (a : ℕ → ℂ) (S : ℂ),
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, a n / (n : ℂ)) atTop (𝓝 S) →
    ∀ y : ℝ, 1 ≤ y → ∃ I : ℂ,
      Tendsto (fun U : ℝ => ∫ u in y..U, psumA a u / (u : ℂ) ^ 2) atTop (𝓝 I) ∧
      GchiA a S y = -(y : ℂ) * I
def SmoothedRemainderRealIntegralFormula : Prop :=
  ∀ a : ℕ → ℝ,
    Tendsto (fun U : ℝ => ∫ u in (1 : ℝ)..U, (psumRA a u - u) / u ^ 2) atTop
      (𝓝 (-1 - Real.eulerMascheroniConstant)) →
    ∀ y : ℝ, 1 ≤ y → ∃ I : ℝ,
      Tendsto (fun U : ℝ => ∫ u in y..U, (psumRA a u - u) / u ^ 2) atTop (𝓝 I) ∧
      GoneA a y = -y * I
def LogDerivSeries : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) / (n : ℂ)) atTop
      (𝓝 (-(deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1)))
def PsiZeroConst : Prop :=
  Tendsto (fun U : ℝ => ∫ u in (1 : ℝ)..U, (psumRA (fun n => Λ n) u - u) / u ^ 2) atTop
    (𝓝 (-1 - Real.eulerMascheroniConstant))
instance neZeroHostN (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] : NeZero (hostN e q d) :=
  ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ two_ne_zero) (Fact.out : q.Prime).ne_zero)
    (Fact.out : d.Prime).ne_zero⟩
def condOf (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (ψ : AddChar (E0 × HA e) ℂ) : ℕ :=
  (dirChar (recMap e q d) ψ).conductor
instance neZeroCondOf (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (ψ : AddChar (E0 × HA e) ℂ) :
    NeZero (condOf e q d ψ) :=
  ⟨DirichletCharacter.conductor_ne_zero _⟩
def chiOf (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (ψ : AddChar (E0 × HA e) ℂ) :
    DirichletCharacter ℂ (condOf e q d ψ) :=
  (dirChar (recMap e q d) ψ).primitiveCharacter
def EllIsLD1 : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (ψ : AddChar (E0 × HA e) ℂ),
    hostEll e q d ψ = logDerivLAtOne (chiOf e q d ψ)
def GrowthFunctionEqTrivial : Prop := ∀ y : ℝ, Gz y = G1 y
def GPsiIsGchi : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (ell : AddChar (E0 × HA e) ℂ → ℂ) (ψ : AddChar (E0 × HA e) ℂ),
    ψ ≠ 0 → ell ψ = logDerivLAtOne (chiOf e q d ψ) → ∀ y : ℝ, GPsi (hostData e q d) ell ψ y = Gchi (chiOf e q d ψ) y
def GPsiHost : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime],
    (∀ ψ : AddChar (E0 × HA e) ℂ, ψ ≠ 0 → ∀ y : ℝ,
      GPsi (hostData e q d) (hostEll e q d) ψ y = Gchi (chiOf e q d ψ) y) ∧
    ∀ y : ℝ, GPsi (hostData e q d) (hostEll e q d) 0 y = ((G1 y : ℝ) : ℂ)
def ChiOfFacts : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d → ∀ ψ : AddChar (E0 × HA e) ℂ,
    (chiOf e q d ψ).IsPrimitive ∧
    (∃ h : condOf e q d ψ ∣ hostN e q d,
      DirichletCharacter.changeLevel h (chiOf e q d ψ) = dirChar (recMap e q d) ψ) ∧
    (ψ ≠ 0 → chiOf e q d ψ ≠ 1 ∧ condOf e q d ψ ≠ 1)
def ThinChar (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (X' θ : ℝ) : Prop :=
  (∀ ψ : AddChar (E0 × HA e) ℂ, ψ ≠ 0 → ∀ y : ℝ, X' / 3 ≤ y → ‖Gchi (chiOf e q d ψ) y‖ ≤ y * θ) ∧
  ∀ y : ℝ, X' / 3 ≤ y → |G1 y| ≤ y * θ
def ThinIff : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (X' θ : ℝ),
    ThinScales (hostData e q d) (hostEll e q d) X' θ ↔ ThinChar e q d X' θ
def ThinOfAllCond : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d → ∀ X' θ : ℝ,
    (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), N ∣ 2 ^ (e + 2) * q * d → χ.IsPrimitive → χ ≠ 1 →
      ∀ y : ℝ, X' / 3 ≤ y → ‖Gchi χ y‖ ≤ y * θ) →
    (∀ y : ℝ, X' / 3 ≤ y → |G1 y| ≤ y * θ) →
    ThinScales (hostData e q d) (hostEll e q d) X' θ
def DirichletSmoothingHypotheses (c C lam y : ℝ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Prop :=
  Gchi χ y = -((y : ℂ) * ∫ u in Set.Ioi y, Formalism.ZeroFreeDirichlet.psiChi χ u / (u : ℂ) ^ 2) ∧
  ∀ u : ℝ, y ≤ u → ‖Formalism.ZeroFreeDirichlet.psiChi χ u‖ ≤
    C * u * (Real.log u + lam) ^ 2 * Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u)))
def TrivialSmoothingHypotheses (c C lam y : ℝ) : Prop :=
  G1 y = -(y * ∫ u in Set.Ioi y, (Chebyshev.psi u - u) / u ^ 2) ∧
  ∀ u : ℝ, y ≤ u → |Chebyshev.psi u - u| ≤
    C * u * (Real.log u + lam) ^ 2 * Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u)))
def ThinScalesFromSmoothing : Prop :=
  CharacterSmoothingEstimate → ∀ ε c C : ℝ, 0 < ε → 0 < c → 0 < C → ∃ c' x₀ : ℝ, 0 < c' ∧ ∀ x : ℝ, x₀ ≤ x →
    ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime] (lam : ℝ), 1 ≤ lam → lam ≤ 2 * x ^ (ε / 5) * Real.log x ^ 2 →
    (∀ y : ℝ, Real.exp (x ^ (ε / 3)) / 3 ≤ y →
      (∀ ψ : AddChar (E0 × HA e) ℂ, ψ ≠ 0 → DirichletSmoothingHypotheses c C lam y (chiOf e q d ψ)) ∧ TrivialSmoothingHypotheses c C lam y) →
    ThinScales (hostData e q d) (hostEll e q d) (XpTx x ε) (Real.exp (-c' * x ^ (ε / 8)))
def CharacterSmoothingInstance : Prop :=
  SmoothedRemainderIntegralFormula → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    Tendsto (fun M : ℕ => ∑ n ∈ Icc 1 M, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) / (n : ℂ)) atTop (𝓝 (-logDerivLAtOne χ)) →
    ∀ y : ℝ, 1 ≤ y → MeasureTheory.IntegrableOn (fun u : ℝ => Formalism.ZeroFreeDirichlet.psiChi χ u / (u : ℂ) ^ 2) (Set.Ioi y) →
    Gchi χ y = -((y : ℂ) * ∫ u in Set.Ioi y, Formalism.ZeroFreeDirichlet.psiChi χ u / (u : ℂ) ^ 2)
def TrivialCharacterSmoothing : Prop :=
  SmoothedRemainderRealIntegralFormula → PsiZeroConst → ∀ y : ℝ, 1 ≤ y →
    MeasureTheory.IntegrableOn (fun u : ℝ => (Chebyshev.psi u - u) / u ^ 2) (Set.Ioi y) →
    G1 y = -(y * ∫ u in Set.Ioi y, (Chebyshev.psi u - u) / u ^ 2)
def psiBd (c C lam u : ℝ) : ℝ :=
  C * u * (Real.log u + lam) ^ 2 * Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u)))
def ThinOfPsiBounds : Prop :=
  CharacterSmoothingEstimate → ThinIntegral → SmoothingSizeBounds → SmoothedRemainderIntegralFormula → SmoothedRemainderRealIntegralFormula → LogDerivSeries → PsiZeroConst →
  ∀ ε c C : ℝ, 0 < ε → 0 < c → 0 < C → ∃ c' x₀ : ℝ, 0 < c' ∧ ∀ x : ℝ, x₀ ≤ x →
    ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d →
    ∀ lam : ℝ, 1 ≤ lam → lam ≤ 2 * x ^ (ε / 5) * Real.log x ^ 2 →
    (∀ ψ : AddChar (E0 × HA e) ℂ, ψ ≠ 0 → ∀ u : ℝ, Real.exp (x ^ (ε / 3)) / 3 ≤ u →
      ‖Formalism.ZeroFreeDirichlet.psiChi (chiOf e q d ψ) u‖ ≤ psiBd c C lam u) →
    (∀ u : ℝ, Real.exp (x ^ (ε / 3)) / 3 ≤ u → |Chebyshev.psi u - u| ≤ psiBd c C lam u) →
    ThinScales (hostData e q d) (hostEll e q d) (XpTx x ε) (Real.exp (-c' * x ^ (ε / 8)))
def HostNIs : Prop := ∀ e q d : ℕ, hostN e q d = 4 * 2 ^ e * q * d
def LogNE : Prop :=
  ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ n q₁ d : ℕ, 1 ≤ n → (n : ℝ) ≤ x ^ A →
    X1 ε x ^ (1 / 2 : ℝ) < (q₁ : ℝ) → (q₁ : ℝ) ≤ X1 ε x → X2 ε x ^ (1 / 2 : ℝ) < (d : ℝ) → (d : ℝ) ≤ X2 ε x →
    x ^ (ε / 5) / 2 < Real.log q₁ ∧ Real.log q₁ ≤ x ^ (ε / 5) ∧
    x ^ (ε / 5) * Real.log x ^ 2 / 2 < Real.log d ∧ Real.log d ≤ x ^ (ε / 5) * Real.log x ^ 2 ∧
    Real.log ((4 * n * q₁ * d : ℕ) : ℝ) ≤ 2 * x ^ (ε / 5) * Real.log x ^ 2
def ThinHostNE : Prop :=
  CharacterSmoothingEstimate → ThinIntegral → SmoothingSizeBounds → SmoothedRemainderIntegralFormula → SmoothedRemainderRealIntegralFormula → LogDerivSeries → PsiZeroConst → LogNE →
  ∀ ε A c C : ℝ, 0 < ε → 0 < A → 0 < c → 0 < C → ∃ c' x₀ : ℝ, 0 < c' ∧ ∀ x : ℝ, x₀ ≤ x →
    ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d → ((2 ^ e : ℕ) : ℝ) ≤ x ^ A →
    X1 ε x ^ (1 / 2 : ℝ) < (q : ℝ) → (q : ℝ) ≤ X1 ε x → X2 ε x ^ (1 / 2 : ℝ) < (d : ℝ) → (d : ℝ) ≤ X2 ε x →
    (∀ ψ : AddChar (E0 × HA e) ℂ, ψ ≠ 0 → ∀ u : ℝ, Real.exp (x ^ (ε / 3)) / 3 ≤ u →
      ‖Formalism.ZeroFreeDirichlet.psiChi (chiOf e q d ψ) u‖ ≤ psiBd c C (Real.log (hostN e q d)) u) →
    (∀ u : ℝ, Real.exp (x ^ (ε / 3)) / 3 ≤ u → |Chebyshev.psi u - u| ≤ psiBd c C (Real.log (hostN e q d)) u) →
    ThinScales (hostData e q d) (hostEll e q d) (XpTx x ε) (Real.exp (-c' * x ^ (ε / 8)))
def SameChar {N M : ℕ} (χ : DirichletCharacter ℂ N) (χ' : DirichletCharacter ℂ M) : Prop :=
  N = M ∧ ∀ n : ℕ, χ (n : ZMod N) = χ' (n : ZMod M)
def SameCharG : Prop :=
  ∀ (N M : ℕ) [NeZero N] [NeZero M] (χ : DirichletCharacter ℂ N) (χ' : DirichletCharacter ℂ M), SameChar χ χ' →
    logDerivLAtOne χ = logDerivLAtOne χ' ∧ (∀ y : ℝ, Gchi χ y = Gchi χ' y) ∧ (∀ y : ℝ, Formalism.ZeroFreeDirichlet.psiChi χ y = Formalism.ZeroFreeDirichlet.psiChi χ' y) ∧
    DirichletCharacter.LFunction χ = DirichletCharacter.LFunction χ' ∧ (χ.IsPrimitive ↔ χ'.IsPrimitive)
def HostQuadChars : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d →
    SameChar (chiOf e q d psC) (tw one1 q) ∧ SameChar (chiOf e q d chC) (tw one1 d) ∧
    SameChar (chiOf e q d chpsC) (tw (tw one1 q) d)
def CharacterValueBounds (q₁ d : ℕ) [Fact q₁.Prime] [Fact d.Prime] (x ε C : ℝ) : Prop :=
  (‖Gchi (tw one1 q₁) x‖ ≤ x ^ (1 / 2 + ε) ∧ ‖logDerivLAtOne (tw one1 q₁)‖ ≤ C * Real.log x) ∧
  (‖Gchi (tw one1 d) x‖ ≤ x ^ (1 / 2 + ε) ∧ ‖logDerivLAtOne (tw one1 d)‖ ≤ C * Real.log x) ∧
  (‖Gchi (tw (tw one1 q₁) d) x‖ ≤ x ^ (1 / 2 + ε) ∧ ‖logDerivLAtOne (tw (tw one1 q₁) d)‖ ≤ C * Real.log x)
def ValuesIff : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d → ∀ x ε C : ℝ,
    ValuesAtX (hostData e q d) (hostEll e q d) x ε C ↔ CharacterValueBounds q d x ε C
def PrimeCongruenceHypotheses : Prop :=
  ∀ q d : ℕ, q.Prime → d.Prime → q % 8 = 3 → d % 16 = 7 → SplitsIn d q → FrobeniusOrbits.HostHyp q d
def PrimeWindowValues : Prop :=
  ∀ ε C x : ℝ, ExistsSplitGoodPrimePair ε C x → ∃ (q d : ℕ) (_ : Fact q.Prime) (_ : Fact d.Prime), FrobeniusOrbits.HostHyp q d ∧
    X1 ε x ^ (1 / 2 : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ X1 ε x ∧ X2 ε x ^ (1 / 2 : ℝ) < (d : ℝ) ∧ (d : ℝ) ≤ X2 ε x ∧
    ∀ e : ℕ, ValuesAtX (hostData e q d) (hostEll e q d) x ε C
def HostRealChars : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d → ∀ ψ : AddChar (E0 × HA e) ℂ,
    chiOf e q d ψ ^ 2 = 1 →
    ψ = 0 ∨ SameChar (chiOf e q d ψ) chi8 ∨
    SameChar (chiOf e q d ψ) (tw one1 q) ∨ SameChar (chiOf e q d ψ) (tw chi8 q) ∨
    SameChar (chiOf e q d ψ) (tw one1 d) ∨ SameChar (chiOf e q d ψ) (tw chi8 d) ∨
    SameChar (chiOf e q d ψ) (tw (tw one1 q) d) ∨ SameChar (chiOf e q d ψ) (tw (tw chi8 q) d)
def TwKronecker : Prop :=
  ∀ (q : ℕ) [Fact q.Prime], q % 4 = 3 → ∀ m : ℕ, Odd m →
    tw one1 q (m : ZMod (1 * q)) = ((jacobiSym (-(q : ℤ)) m : ℤ) : ℂ)
def PrimePairSplittingValuesAndRealChars : Prop :=
  ∀ ε C x : ℝ, 0 ≤ x → ExistsSplitGoodPrimePair ε C x → ∃ (q d : ℕ) (_ : Fact q.Prime) (_ : Fact d.Prime), FrobeniusOrbits.HostHyp q d ∧
    X1 ε x ^ (1 / 2 : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ X1 ε x ∧ X2 ε x ^ (1 / 2 : ℝ) < (d : ℝ) ∧ (d : ℝ) ≤ X2 ε x ∧
    (∀ p : ℕ, p.Prime → (p : ℝ) ≤ x ^ (ε / 5) → SplitsIn d p) ∧
    ∀ e : ℕ, ValuesAtX (hostData e q d) (hostEll e q d) x ε C ∧
      ∀ ψ : AddChar (E0 × HA e) ℂ, chiOf e q d ψ ^ 2 = 1 →
        ψ = 0 ∨ SameChar (chiOf e q d ψ) chi8 ∨ ZeroFreeBox (8 * X1 ε x) (chiOf e q d ψ)
def ThinOne : Prop :=
  ∀ ε c' : ℝ, 0 < ε → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ y : ℝ, Real.exp (x ^ (ε / 3)) / 3 ≤ y →
    |G1 y| ≤ y * Real.exp (-c' * x ^ (ε / 8))
def ThinOneOf : Prop := Formalism.ZF.GzPNT → ThinOne
def LogDerivSeriesOf : Prop := Formalism.ZeroFreeDirichlet.SiegelWalfisz → LogDerivSeries
def PsiZeroConstOf : Prop := Formalism.ZF.GzPNT → PsiZeroConst
def ThinOfCharBounds : Prop :=
  Formalism.ZF.GzPNT → Formalism.ZeroFreeDirichlet.SiegelWalfisz → CharacterSmoothingEstimate → ThinIntegral → SmoothingSizeBounds → SmoothedRemainderIntegralFormula → LogNE →
  ∀ ε A c C : ℝ, 0 < ε → 0 < A → 0 < c → 0 < C → ∃ c' x₀ : ℝ, 0 < c' ∧ ∀ x : ℝ, x₀ ≤ x →
    ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d → ((2 ^ e : ℕ) : ℝ) ≤ x ^ A →
    X1 ε x ^ (1 / 2 : ℝ) < (q : ℝ) → (q : ℝ) ≤ X1 ε x → X2 ε x ^ (1 / 2 : ℝ) < (d : ℝ) → (d : ℝ) ≤ X2 ε x →
    (∀ ψ : AddChar (E0 × HA e) ℂ, ψ ≠ 0 → ∀ u : ℝ, Real.exp (x ^ (ε / 3)) / 3 ≤ u →
      ‖Formalism.ZeroFreeDirichlet.psiChi (chiOf e q d ψ) u‖ ≤ psiBd c C (Real.log (hostN e q d)) u) →
    ThinScales (hostData e q d) (hostEll e q d) (XpTx x ε) (Real.exp (-c' * x ^ (ε / 8)))
def NoRealZeroSmall : Prop :=
  (∀ σ : ℝ, 0 < σ → σ < 1 → riemannZeta (σ : ℂ) ≠ 0) ∧
  (∀ σ : ℝ, 0 < σ → σ < 1 → DirichletCharacter.LFunction chi8 (σ : ℂ) ≠ 0)
def SmoothGen : Prop :=
  Formalism.ZeroFreeDirichlet.PerronChi → Formalism.ZeroFreeDirichlet.RectShiftChi → Formalism.ZeroFreeDirichlet.LogDerivRegionChi → Formalism.ZeroFreeDirichlet.LLogDerivRight →
  ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 20 → ∃ A : ℝ, 0 ≤ A ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → Formalism.ZeroFreeDirichlet.ExcZeros c₁ χ ∅ → ∀ y : ℝ, 2 ≤ y →
      ‖Gchi χ y‖ ≤ A * y * (Real.log q + 2 + Real.sqrt (Real.log y) + Real.log y) ^ 3 *
        Real.exp (-(c₁ / 16) * Real.log y / (Real.log q + 2 + Real.sqrt (Real.log y)))
def ThinOfNoExc : Prop :=
  Formalism.ZeroFreeDirichlet.PerronChi → Formalism.ZeroFreeDirichlet.RectShiftChi → Formalism.ZeroFreeDirichlet.LogDerivRegionChi → Formalism.ZeroFreeDirichlet.LLogDerivRight →
  ∀ ε c₁ : ℝ, 0 < ε → 0 < c₁ → c₁ ≤ 1 / 20 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → Formalism.ZeroFreeDirichlet.ExcZeros c₁ χ ∅ →
    Real.log q ≤ 2 * x ^ (ε / 5) * Real.log x ^ 2 → ∀ y : ℝ, Real.exp (x ^ (ε / 3)) / 3 ≤ y →
      ‖Gchi χ y‖ ≤ y * Real.exp (-(c₁ / 256) * x ^ (ε / 8))
def NoExcOfReal : Prop :=
  Formalism.ZeroFreeDirichlet.ZFRDirichlet → ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 20 ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      (χ ^ 2 = 1 → ∀ σ : ℝ, 1 - 1 / 400 < σ → DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0) →
      Formalism.ZeroFreeDirichlet.ExcZeros c₁ χ ∅
def PrimePairBounds (ε C x : ℝ) (q₁ d : ℕ) [Fact q₁.Prime] [Fact d.Prime] : Prop :=
    q₁ % 8 = 3 ∧ d % 16 = 7 ∧
    X1 ε x ^ (1 / 2 : ℝ) < (q₁ : ℝ) ∧ (q₁ : ℝ) ≤ X1 ε x ∧ X2 ε x ^ (1 / 2 : ℝ) < (d : ℝ) ∧ (d : ℝ) ≤ X2 ε x ∧
    SplitsIn d q₁ ∧ (∀ p : ℕ, p.Prime → (p : ℝ) ≤ x ^ (ε / 5) → SplitsIn d p) ∧
    GoodFor (8 * X1 ε x) (tw one1 q₁) ∧ GoodFor (8 * X1 ε x) (tw chi8 q₁) ∧
    GoodFor (8 * X1 ε x * X2 ε x) (tw one1 d) ∧ GoodFor (8 * X1 ε x * X2 ε x) (tw chi8 d) ∧
    GoodFor (8 * X1 ε x * X2 ε x) (tw (tw one1 q₁) d) ∧ GoodFor (8 * X1 ε x * X2 ε x) (tw (tw chi8 q₁) d) ∧
    (‖Gchi (tw one1 q₁) x‖ ≤ x ^ (1 / 2 + ε) ∧ ‖logDerivLAtOne (tw one1 q₁)‖ ≤ C * Real.log x) ∧
    (‖Gchi (tw one1 d) x‖ ≤ x ^ (1 / 2 + ε) ∧ ‖logDerivLAtOne (tw one1 d)‖ ≤ C * Real.log x) ∧
    (‖Gchi (tw (tw one1 q₁) d) x‖ ≤ x ^ (1 / 2 + ε) ∧ ‖logDerivLAtOne (tw (tw one1 q₁) d)‖ ≤ C * Real.log x)
def PrimePairExistsIffConditions : Prop :=
  ∀ ε C x : ℝ, ExistsSplitGoodPrimePair ε C x ↔ ∃ (q₁ d : ℕ) (_ : Fact q₁.Prime) (_ : Fact d.Prime), PrimePairBounds ε C x q₁ d
def HostAnalyticConcl : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (C : ℝ) (q d : ℕ) [Fact q.Prime] [Fact d.Prime], PrimePairBounds ε C x q d →
      FrobeniusOrbits.HostHyp q d ∧ ∀ e : ℕ, ((2 ^ e : ℕ) : ℝ) ≤ x ^ A →
        ThinScales (hostData e q d) (hostEll e q d) (XpTx x ε) (Real.exp (-c' * x ^ (ε / 8))) ∧
        ValuesAtX (hostData e q d) (hostEll e q d) x ε C
def AnalyticInputsFromPNT : Prop :=
  Formalism.ZF.GzPNT → Formalism.ZeroFreeDirichlet.ZFRDirichlet →
  Formalism.ZeroFreeDirichlet.PerronChi → Formalism.ZeroFreeDirichlet.RectShiftChi → Formalism.ZeroFreeDirichlet.LogDerivRegionChi → Formalism.ZeroFreeDirichlet.LLogDerivRight →
  NoRealZeroSmall → LogNE → HostAnalyticConcl
def AnalyticInputsOfNoSmallRealZero : Prop := NoRealZeroSmall → LogNE → HostAnalyticConcl
def Chain3Core (eD eL K cHH eK CL ε x : ℝ) : Prop :=
  ∃ (e q d : ℕ) (_ : Fact q.Prime) (_ : Fact d.Prime)
    (W : HA e → Type) (_ : ∀ u0, Fintype (W u0)) (_ : ∀ u0, Nonempty (W u0)) (m : ℕ)
    (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset (HA e)) (a : HA e → ℝ) (w : HA e → Fin m → E0 × HA e → ℝ)
    (Fm : ∀ u0, Fam (W u0) m) (η θ : ℝ),
    FrobeniusOrbits.HostHyp q d ∧ G.x = x ∧ G.ε = ε ∧ C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ C.cHH ≤ cHH ∧
    ThinChar e q d (Real.exp (x ^ (ε / 3))) θ ∧ CharacterValueBounds q d x ε CL ∧
    (ThinScales (hostData e q d) (hostEll e q d) (XpTx G.x G.ε) θ →
      ValuesAtX (hostData e q d) (hostEll e q d) G.x G.ε CL →
      Inputs2 (hostData e q d) (hostEll e q d) G C cT N TT T2 a w Fm η θ eK K CL)
def Core3ToCore2 : Prop :=
  ∀ eD eL K cHH eK CL ε x : ℝ, Chain3Core eD eL K cHH eK CL ε x → Chain2Core eD eL K cHH eK CL ε x
def Chain3 : Prop :=
  Chain2 → ∀ eD eL ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ K cHH eK CL x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → Chain3Core eD eL K cHH eK CL ε x) →
    RiemannHypothesis
def Chain4Core (A c Cp c' eD eL K cHH eK CL ε x : ℝ) : Prop :=
  ∃ (e q d : ℕ) (_ : Fact q.Prime) (_ : Fact d.Prime)
    (W : HA e → Type) (_ : ∀ u0, Fintype (W u0)) (_ : ∀ u0, Nonempty (W u0)) (m : ℕ)
    (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset (HA e)) (a : HA e → ℝ) (w : HA e → Fin m → E0 × HA e → ℝ)
    (Fm : ∀ u0, Fam (W u0) m) (η : ℝ),
    FrobeniusOrbits.HostHyp q d ∧ G.x = x ∧ G.ε = ε ∧ C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ C.cHH ≤ cHH ∧
    ((2 ^ e : ℕ) : ℝ) ≤ x ^ A ∧
    X1 ε x ^ (1 / 2 : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ X1 ε x ∧ X2 ε x ^ (1 / 2 : ℝ) < (d : ℝ) ∧ (d : ℝ) ≤ X2 ε x ∧
    (∀ ψ : AddChar (E0 × HA e) ℂ, ψ ≠ 0 → ∀ u : ℝ, Real.exp (x ^ (ε / 3)) / 3 ≤ u →
      ‖Formalism.ZeroFreeDirichlet.psiChi (chiOf e q d ψ) u‖ ≤ psiBd c Cp (Real.log (hostN e q d)) u) ∧
    CharacterValueBounds q d x ε CL ∧
    (ThinScales (hostData e q d) (hostEll e q d) (XpTx G.x G.ε) (Real.exp (-c' * x ^ (ε / 8))) →
      ValuesAtX (hostData e q d) (hostEll e q d) G.x G.ε CL →
      Inputs2 (hostData e q d) (hostEll e q d) G C cT N TT T2 a w Fm η (Real.exp (-c' * x ^ (ε / 8))) eK K CL)
def Chain4 : Prop :=
  Formalism.ZF.GzPNT → Formalism.ZeroFreeDirichlet.SiegelWalfisz → CharacterSmoothingEstimate → ThinIntegral → SmoothingSizeBounds → SmoothedRemainderIntegralFormula → LogNE → Chain2 →
  ∀ eD eL ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ → ∃ A c Cp : ℝ, 0 < A ∧ 0 < c ∧ 0 < Cp ∧ ∀ c' : ℝ, 0 < c' →
      ∃ K cHH eK CL x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → Chain4Core A c Cp c' eD eL K cHH eK CL ε x) →
    RiemannHypothesis
def Chain3cCore (Cord eD eL K cHH eK CL eW KW ε x : ℝ) : Prop :=
  ∃ (e q d : ℕ) (_ : Fact q.Prime) (_ : Fact d.Prime) (Ω : Type) (_ : Fintype Ω)
    (W : Ω → HA e → Type) (_ : ∀ o u0, Fintype (W o u0)) (_ : ∀ o u0, Nonempty (W o u0)) (m : ℕ)
    (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset (HA e)) (a : Ω → HA e → ℝ) (w : Ω → HA e → Fin m → E0 × HA e → ℝ)
    (Fm : ∀ o u0, Fam (W o u0) m) (Lp : HA e → Ω → LossP (HA e) m)
    (P : PrimeWindowSizeBounds.Par) (π : Ω → ℝ) (s sB : Finset ℕ) (BAD : ℕ → HA e → Prop) (Sig : ℕ → Ω → ℝ) (η θ : ℝ),
    FrobeniusOrbits.HostHyp q d ∧ G.x = x ∧ G.ε = ε ∧ C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ C.cHH ≤ cHH ∧ P.e₂ = e ∧
    ThinChar e q d (Real.exp (x ^ (ε / 3))) θ ∧ CharacterValueBounds q d x ε CL ∧
    LossHyp (hostData e q d) G C N TT a w Fm Lp P π s sB BAD Sig Cord eW KW ∧
    ∀ o, 0 < π o →
      ThinScales (hostData e q d) (hostEll e q d) (XpTx G.x G.ε) θ →
      ValuesAtX (hostData e q d) (hostEll e q d) G.x G.ε CL →
      InputsB (hostData e q d) (hostEll e q d) G C cT N TT T2 (a o) (w o) (Fm o) η θ eK K CL
def Core3cToCore2c : Prop :=
  ∀ Cord eD eL K cHH eK CL eW KW ε x : ℝ,
    Chain3cCore Cord eD eL K cHH eK CL eW KW ε x → Chain2cCore Cord eD eL K cHH eK CL eW KW ε x
def Chain3c : Prop :=
  Chain2c → ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ K cHH eK CL eW KW x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → Chain3cCore Cord eD eL K cHH eK CL eW KW ε x) →
    RiemannHypothesis
def Chain5Core (A c' eD eL K cHH eK CL ε x : ℝ) : Prop :=
  ∃ (e q d : ℕ) (_ : Fact q.Prime) (_ : Fact d.Prime)
    (W : HA e → Type) (_ : ∀ u0, Fintype (W u0)) (_ : ∀ u0, Nonempty (W u0)) (m : ℕ)
    (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset (HA e)) (a : HA e → ℝ) (w : HA e → Fin m → E0 × HA e → ℝ)
    (Fm : ∀ u0, Fam (W u0) m) (η : ℝ),
    G.x = x ∧ G.ε = ε ∧ C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ C.cHH ≤ cHH ∧
    ((2 ^ e : ℕ) : ℝ) ≤ x ^ A ∧ PrimePairBounds ε CL x q d ∧
    (ThinScales (hostData e q d) (hostEll e q d) (XpTx G.x G.ε) (Real.exp (-c' * x ^ (ε / 8))) →
      ValuesAtX (hostData e q d) (hostEll e q d) G.x G.ε CL →
      Inputs2 (hostData e q d) (hostEll e q d) G C cT N TT T2 a w Fm η (Real.exp (-c' * x ^ (ε / 8))) eK K CL)
def Chain5 : Prop :=
  HostAnalyticConcl → Chain2 → ∀ eD eL ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ → ∃ A : ℝ, 0 < A ∧ ∀ c' : ℝ, 0 < c' →
      ∃ K cHH eK CL x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → Chain5Core A c' eD eL K cHH eK CL ε x) →
    RiemannHypothesis
def Chain5cCore (A c' Cord eD eL K cHH eK CL eW KW ε x : ℝ) : Prop :=
  ∃ (e q d : ℕ) (_ : Fact q.Prime) (_ : Fact d.Prime) (Ω : Type) (_ : Fintype Ω)
    (W : Ω → HA e → Type) (_ : ∀ o u0, Fintype (W o u0)) (_ : ∀ o u0, Nonempty (W o u0)) (m : ℕ)
    (G : Glob) (C : Consts) (cT : ℝ) (N : ℕ)
    (TT T2 : Finset (HA e)) (a : Ω → HA e → ℝ) (w : Ω → HA e → Fin m → E0 × HA e → ℝ)
    (Fm : ∀ o u0, Fam (W o u0) m) (Lp : HA e → Ω → LossP (HA e) m)
    (P : PrimeWindowSizeBounds.Par) (π : Ω → ℝ) (s sB : Finset ℕ) (BAD : ℕ → HA e → Prop) (Sig : ℕ → Ω → ℝ) (η : ℝ),
    G.x = x ∧ G.ε = ε ∧ C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ C.cHH ≤ cHH ∧ P.e₂ = e ∧
    ((2 ^ e : ℕ) : ℝ) ≤ x ^ A ∧ PrimePairBounds ε CL x q d ∧
    LossHyp (hostData e q d) G C N TT a w Fm Lp P π s sB BAD Sig Cord eW KW ∧
    ∀ o, 0 < π o →
      ThinScales (hostData e q d) (hostEll e q d) (XpTx G.x G.ε) (Real.exp (-c' * x ^ (ε / 8))) →
      ValuesAtX (hostData e q d) (hostEll e q d) G.x G.ε CL →
      InputsB (hostData e q d) (hostEll e q d) G C cT N TT T2 (a o) (w o) (Fm o) η (Real.exp (-c' * x ^ (ε / 8))) eK K CL
def Chain5c : Prop :=
  HostAnalyticConcl → Chain2c → ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ → ∃ A : ℝ, 0 < A ∧ ∀ c' : ℝ, 0 < c' →
      ∃ K cHH eK CL eW KW x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → Chain5cCore A c' Cord eD eL K cHH eK CL eW KW ε x) →
    RiemannHypothesis
end Formalism.LFunctionChainParameters.LBr2


