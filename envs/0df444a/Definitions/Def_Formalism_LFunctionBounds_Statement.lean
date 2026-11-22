-- Prove2me | Definitions.Def_Formalism_LFunctionBounds_Statement
-- name    : Formalism_LFunctionBounds_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:28:08.034829+00:00
-- url     : https://prove2.me/theorems/bed36567-0cd2-4b29-9579-41fa63a2432f
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/Statement.lean

import Definitions.Def_Formalism_StatementFL
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
def triples (l : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Icc 1 l ×ˢ Finset.Icc 1 l ×ˢ Finset.Icc 1 l).filter (fun S => S.1 + S.2.1 + S.2.2 = l)
def IsProb (l : ℕ) (ν : ℕ × ℕ × ℕ → ℝ) : Prop :=
  (∀ S ∈ triples l, 0 ≤ ν S) ∧ ∑ S ∈ triples l, ν S = 1
def W (l : ℕ) (ν : ℕ × ℕ × ℕ → ℝ) (x : ℕ) : ℝ :=
  ∑ S ∈ triples l, ν S *
    ((if S.1 = x then 1 else 0) + (if S.2.1 = x then 1 else 0) + (if S.2.2 = x then 1 else 0))
def Snu (l : ℕ) (ν : ℕ × ℕ × ℕ → ℝ) (χ : DirichletCharacter ℂ l) : ℂ :=
  ∑ x ∈ Finset.Ioo 0 l, (W l ν x : ℂ) * (starRingEnd ℂ) (χ (x : ZMod l))
def cW (l : ℕ) [NeZero l] (ν : ℕ × ℕ × ℕ → ℝ) (χ : DirichletCharacter ℂ l) : ℂ :=
  DirichletCharacter.LFunction χ 0 * Snu l ν χ / ((((l : ℝ) - 1) / 2 : ℝ) : ℂ)
def oddChars (l : ℕ) [NeZero l] : Finset (DirichletCharacter ℂ l) :=
  @Finset.filter _ (fun χ => χ.Odd) (Classical.decPred _) (@Finset.univ _ (Fintype.ofFinite _))
def saw (y : ℝ) : ℝ := if Int.fract y = 0 then 0 else Int.fract y - 1 / 2
def sgnS (l : ℕ) (S : ℕ × ℕ × ℕ) (t : ℤ) : ℝ :=
  -2 * (saw ((t : ℝ) * (S.1 : ℝ) / (l : ℝ)) + saw ((t : ℝ) * (S.2.1 : ℝ) / (l : ℝ)) +
    saw ((t : ℝ) * (S.2.2 : ℝ) / (l : ℝ)))
def oNu (l : ℕ) (ν : ℕ × ℕ × ℕ → ℝ) (t : ℤ) : ℝ := ∑ S ∈ triples l, ν S * sgnS l S t
def gam (s : ℝ) : ℝ := Real.Gamma s / Real.Gamma (1 - s)
def logOm1 (l : ℕ) (S : ℕ × ℕ × ℕ) : ℝ :=
  -Real.log l + (Real.log (gam ((S.1 : ℝ) / (l : ℝ))) + Real.log (gam ((S.2.1 : ℝ) / (l : ℝ))) +
    Real.log (gam ((S.2.2 : ℝ) / (l : ℝ))))
def PeriodIdentity : Prop :=
  ∀ (l : ℕ) [NeZero l], l.Prime → l ≠ 2 → ∀ ν : ℕ × ℕ × ℕ → ℝ, IsProb l ν →
    (∀ t : ℤ, ¬ (l : ℤ) ∣ t →
      ((oNu l ν t : ℝ) : ℂ) = ∑ χ ∈ oddChars l, cW l ν χ * (starRingEnd ℂ) (χ (t : ZMod l))) ∧
    (∑ χ ∈ oddChars l, cW l ν χ = 1) ∧
    (∀ χ ∈ oddChars l, cW l ν χ⁻¹ = (starRingEnd ℂ) (cW l ν χ)) ∧
    (((∑ S ∈ triples l, ν S * logOm1 l S : ℝ) : ℂ) =
      (Real.eulerMascheroniConstant : ℂ) + (Real.log (2 * Real.pi / l) : ℂ) -
        ∑ χ ∈ oddChars l, cW l ν χ *
          (deriv (DirichletCharacter.LFunction χ⁻¹) 1 / DirichletCharacter.LFunction χ⁻¹ 1))
def KillingLemma : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ l₀ : ℕ, ∀ (l : ℕ) [NeZero l], l.Prime → l₀ ≤ l →
    ∀ BB : Finset (DirichletCharacter ℂ l), BB ⊆ oddChars l → (∀ χ ∈ BB, χ⁻¹ ∈ BB) →
      (BB.card : ℝ) ≤ (l : ℝ) ^ (1 - ε) →
      ∃ ν : ℕ × ℕ × ℕ → ℝ, IsProb l ν ∧ ∀ χ ∈ BB, cW l ν χ = 0
def zeroChars (l : ℕ) [NeZero l] (θ : ℝ) (Z : Finset ℂ) : Finset (DirichletCharacter ℂ l) :=
  @Finset.filter _ (fun χ => (∃ σ : ℝ, θ ≤ σ ∧ σ ≤ 1 ∧ DirichletCharacter.LFunction χ σ = 0) ∨
      ∃ z ∈ Z, DirichletCharacter.LFunction χ z = 0) (Classical.decPred _)
    (@Finset.univ _ (Fintype.ofFinite _))
def Density : Prop :=
  ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ T : ℝ, 1 ≤ T → ∀ k : ℕ, ∃ C : ℝ,
    ∀ (l : ℕ) [NeZero l], l.Prime → ∀ Z : Finset ℂ, Z.card ≤ k →
      (∀ z ∈ Z, θ ≤ z.re ∧ |z.im| ≤ T) →
      ((zeroChars l θ Z).card : ℝ) ≤ C * (l : ℝ) ^ (1 - δ)
def zeroCharsRect (l : ℕ) [NeZero l] (θ T : ℝ) : Finset (DirichletCharacter ℂ l) :=
  @Finset.filter _ (fun χ => ∃ s : ℂ, θ ≤ s.re ∧ |s.im| ≤ T ∧ DirichletCharacter.LFunction χ s = 0)
    (Classical.decPred _) (@Finset.univ _ (Fintype.ofFinite _))
def DensityRect : Prop :=
  ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ T : ℝ, 1 ≤ T → ∃ C : ℝ,
    ∀ (l : ℕ) [NeZero l], l.Prime → ((zeroCharsRect l θ T).card : ℝ) ≤ C * (l : ℝ) ^ (1 - δ)
def inCM (l : ℕ) (S : ℕ × ℕ × ℕ) (n : ℕ) : Prop :=
  Int.fract ((n * S.1 : ℝ) / l) + Int.fract ((n * S.2.1 : ℝ) / l) < 1
open ArithmeticFunction in

def AS (l : ℕ) (S : ℕ × ℕ × ℕ) (y : ℝ) : ℝ :=
  2 * ∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
    if ¬ l ∣ n ∧ ¬ inCM l S n then Λ n * max 0 (y / (n : ℝ) - 1) else 0
def Al (l : ℕ) (y : ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 ⌊y⌋₊, Real.log l * max 0 (y / (l : ℝ) ^ i - 1)
def logPiV (l : ℕ) : ℝ := Real.log (2 * Real.pi / l) + Real.log l / ((l : ℝ) - 1)
def tripleMainTerm (l : ℕ) (S : ℕ × ℕ × ℕ) (y : ℝ) : ℝ :=
  y * (Real.log y - 1 - logOm1 l S + logPiV l)
def FixedLPointwise : Prop :=
  ∀ θ : ℝ, 1 / 2 ≤ θ → θ < 1 →
  (∀ L₀ : ℕ, ∃ l : ℕ, L₀ ≤ l ∧ l.Prime ∧
    ∀ ε : ℝ, 0 < ε → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ S ∈ triples l,
      AS l S x + 2 * Al l x ≤ tripleMainTerm l S x + C * x ^ (θ + ε)) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0
def FixedLW3 : Prop :=
  ∀ θ : ℝ, 1 / 2 ≤ θ → θ < 1 →
  (∀ L₀ : ℕ, ∃ l : ℕ, L₀ ≤ l ∧ l.Prime ∧
    ∀ ε : ℝ, 0 < ε → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∃ m : ℕ, 0 < m ∧ x ^ (1 - θ - ε) ≤ m ∧
      ∀ S ∈ triples l,
        chebyshevWeightedAverage m x (fun y => AS l S y + 2 * Al l y) ≤ chebyshevWeightedAverage m x (tripleMainTerm l S) + C * x ^ (θ + ε)) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0
example : triples 3 = {(1, 1, 1)} := by decide
example : saw (1 / 2) = 0 := by norm_num [saw]
example (y : ℝ) : saw (y + 1) = saw y := by simp [saw]
def Theorem7 : Prop :=
  ∀ θ : ℝ, 1 / 2 ≤ θ → θ < 1 →
  (∀ ε : ℝ, 0 < ε → ∀ L₀ : ℕ, ∃ l : ℕ, L₀ ≤ l ∧ l.Prime ∧
    ∀ S ∈ triples l, ∀ x : ℝ, (l : ℝ) ^ (1 / ε) ≤ x → x ≤ (l : ℝ) ^ (1300 / ε) →
      AS l S x + 2 * Al l x ≤ tripleMainTerm l S x + x ^ (θ + ε)) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0
def PrimesLL : Prop :=
  ∀ K : ℝ, 0 < K → ∀ L₀ : ℕ, ∃ l : ℕ, L₀ ≤ l ∧ l.Prime ∧ l % 4 = 3 ∧
    ∀ p : ℕ, p.Prime → p ∣ (l - 1) / 2 → K * Real.log l ≤ p
end Formalism.FX


