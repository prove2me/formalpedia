-- Prove2me | Definitions.Def_Formalism_GrowthSums_StatementA
-- name    : Formalism_GrowthSums_StatementA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:21:20.41573+00:00
-- url     : https://prove2.me/theorems/212dce5b-993c-482a-aa89-cdf95bae3665
-- title:
--   Statement A
-- statement:
--   Definitions and structural lemmas for Statement A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GrowthSums/StatementA.lean

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_StatementB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.GrowthSums
def Dichotomy : Prop :=
  ∀ (x P δ A₀ Aᵢ ε : ℝ), 0 ≤ δ → δ ≤ 1 / 6 → 0 < x → 0 < P → 0 < Aᵢ →
    ¬ (x * (1 - 2 * δ) ≤ P ∧ P ≤ x * (1 + 2 * δ)) →
    |ε| ≤ 2 / 3 * δ → A₀ / Aᵢ = x / P * (1 + ε) →
    (Aᵢ * (1 + δ) < A₀ ∧ P < x * (1 - 2 * δ)) ∨ (A₀ < Aᵢ * (1 - δ) ∧ x * (1 + 2 * δ) < P)
def DichotomySharp : Prop :=
  ∀ δ : ℝ, 1 / 6 < δ → ∃ x P A₀ Aᵢ ε : ℝ, 0 < x ∧ 0 < P ∧ 0 < Aᵢ ∧
    ¬ (x * (1 - 2 * δ) ≤ P ∧ P ≤ x * (1 + 2 * δ)) ∧
    |ε| ≤ 2 / 3 * δ ∧ A₀ / Aᵢ = x / P * (1 + ε) ∧
    ¬ (Aᵢ * (1 + δ) < A₀) ∧ ¬ (A₀ < Aᵢ * (1 - δ))
def InitialRun : Prop :=
  ∀ (p x δ : ℝ) (s : ℕ) (d : Fin s → ℕ), 1 < p → 0 ≤ δ → StrictMono d →
    (∀ i j : Fin s, i ≤ j → p ^ d j < x * (1 - 2 * δ) → p ^ d i < x * (1 - 2 * δ)) ∧
    (p < x → ¬ (x * (1 - 2 * δ) ≤ p ∧ p ≤ x * (1 + 2 * δ)) → p < x * (1 - 2 * δ))
def MultinomialVal : Prop :=
  ∀ (p k : ℕ) (f : Fin k → ℕ), p.Prime →
    padicValNat p (Nat.multinomial univ f) ≤ (k - 1) * Nat.log p (∑ i, f i)
def coarseUnit (P n : ℕ) : ℚ :=
  ((P * n).factorial : ℚ) / (((P.factorial : ℚ) ^ n) * (n.factorial : ℚ))
def CoarseUnitProd : Prop :=
  ∀ P n : ℕ, 1 ≤ P →
    coarseUnit P n = ∏ i ∈ range n, ∏ y ∈ Ico 1 P, (1 + (P : ℚ) * i / y)
def FactorialDigit : Prop :=
  ∀ P ρ e' : ℕ, 1 ≤ P → ρ < P →
    (((ρ + P * e').factorial : ℕ) : ℚ) =
      (ρ.factorial : ℚ) * (e'.factorial : ℚ) * (P.factorial : ℚ) ^ e' * coarseUnit P e' *
        ∏ y ∈ Icc 1 ρ, (1 + (P : ℚ) * e' / y)
def HarmonicVal : Prop :=
  ∀ p t s : ℕ, p.Prime →
    (s : ℤ) ≤ padicValRat p (((p ^ (t + 1) : ℕ) : ℚ) ^ s * ∑ y ∈ Ico 1 (p ^ (t + 1)), 1 / (y : ℚ) ^ s)
def PowerSumPoly : Prop :=
  ∀ s : ℕ, ∃ f : Polynomial ℚ, f.natDegree = s + 1 ∧
    ∀ n : ℕ, f.eval (n : ℚ) = ∑ i ∈ range n, (i : ℚ) ^ s
def OrderBound : Prop :=
  ∀ (p : ℝ) (z s₁ : ℕ) (S : Finset ℕ), 2 ≤ p → (∀ i ∈ S, s₁ ≤ i ∧ i ≤ z) →
    ∑ i ∈ S, p ^ (z - i) ≤ 2 * p ^ (z - s₁)
def EdgeCount : Prop :=
  ∀ q k : ℕ, 2 ≤ q → 1 ≤ k → q ^ (k - 1) ≤ (q ^ k - 1) / (q - 1)
def PlaneCountLower : Prop :=
  ∀ q n r : ℕ, r ≤ n → q ^ (r * (n - r)) ≤ Formalism.G0.gaussBinom q n r
def rhoP (p : ℝ) : ℝ := 1 / (p ^ 2 - 1)
def gamP (p : ℝ) : ℝ := p * rhoP p
def GammaIdentity : Prop :=
  ∀ p : ℝ, 1 < p →
    HasSum (fun n : ℕ => (p ^ (2 * n + 1))⁻¹) (gamP p) ∧ gamP p = 1 / (p - 1) - rhoP p
def ExponentIdentityC : Prop :=
  ∀ N r l : ℤ, l * (N - 2 * r + l) + (r - l) * (N - r + l) = r * (N - r)
def HsymmNorm : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (σ : Type) [Fintype σ] [DecidableEq σ]
    (l : ℕ) (x : σ → K) (M : ℝ), 0 ≤ M → (∀ i, ‖x i‖ ≤ M) →
    ‖MvPolynomial.eval x (MvPolynomial.hsymm σ K l)‖ ≤ M ^ l
def Nprime {ι : Type} (Ev Od : Finset ι) (lam : ι → ℕ → ℝ) (wj : ι → ℝ) (i : ℕ) : ℝ :=
  ∑ s ∈ Ev, ∑ a ∈ Icc 1 i, lam s a + (i : ℝ) * ∑ s ∈ Od, wj s
def CoeffIntegral : Prop :=
  ∀ (ι : Type) (Ev Od TTev : Finset ι) (k r l t : ℕ) (n' Nj vh : ℝ)
    (lam : ι → ℕ → ℝ) (w1 wj : ι → ℝ),
    TTev ⊆ Ev → 1 ≤ r → 2 * r ≤ k → l ≤ r → 0 ≤ n' →
    (∀ s ∈ Ev, ∀ i ∈ Icc 1 k, -w1 s ≤ lam s i) →
    (t : ℝ) + 1 ≤ Nj - 2 * r + l →
    (l : ℝ) * (∑ s ∈ Ev, w1 s - ∑ s ∈ Od, wj s) - l * n' * t / 2 ≤ vh →
    let vc := Nprime Ev Od lam wj r - Nprime Ev Od lam wj (r - l) + n' * l * (Nj - 2 * r + l) / 2 + vh
    (∑ s ∈ Ev, (∑ a ∈ Icc (r - l + 1) r, lam s a + l * w1 s)) ≤ vc ∧
    0 ≤ ∑ s ∈ Ev, (∑ a ∈ Icc (r - l + 1) r, lam s a + l * w1 s) ∧
    (l = r → ∑ s ∈ TTev, (lam s 1 - lam s 2) ≤ vc)
def PrExp {ι : Type} (Od : Finset ι) (k r j t : ℕ) (n' : ℝ) (lam : ι → ℕ → ℝ) (wj : ι → ℝ) : ℝ :=
  ∑ s ∈ Od, ((r : ℝ) * wj s + ∑ a ∈ Icc (k - r + 1) k, lam s a) + n' * r * j * (t + 1) / 2
def PrNonneg : Prop :=
  ∀ (ι : Type) (Od : Finset ι) (k r j t : ℕ) (n' : ℝ) (lam : ι → ℕ → ℝ) (w1 wj : ι → ℝ),
    r ≤ k → 0 ≤ n' →
    (∀ s ∈ Od, ∀ a ∈ Icc 1 k, lam s k ≤ lam s a) →
    (∀ s ∈ Od, -lam s k ≤ w1 s) → (∀ s ∈ Od, w1 s ≤ wj s) →
    0 ≤ PrExp Od k r j t n' lam wj
def gainG {n : ℕ} (p : ℝ) (TT TTodd : Finset (ZMod n)) (al cap : ZMod n → ℝ) (de : ℝ) : ℝ :=
  gamP p * ∑ s ∈ TT, al s -
    ∑ s ∈ TTodd, ∑' e : ℕ, min (al s / p ^ (2 * e + 1)) (cap (s + ((2 * e + 1 : ℕ) : ZMod n))) - de
def excessGain {n : ℕ} (p : ℝ) (TT : Finset (ZMod n)) (D : ZMod n → Finset ℕ) (al cap : ZMod n → ℝ)
    (de : ℝ) : ℝ :=
  ∑ s ∈ TT, ∑' e : ℕ,
    (if 2 * e + 1 ∈ D s then 0 else max (al s / p ^ (2 * e + 1) - cap (s + ((2 * e + 1 : ℕ) : ZMod n))) 0)
    - de
def ServiceSize : Prop :=
  ∀ (n m : ℕ) (p : ℝ) (TT TTodd : Finset (ZMod n)) (D : Fin m → ZMod n → Finset ℕ)
    (al : ZMod n → ℝ) (cap : Fin m → ZMod n → ℝ) (de Pr : Fin m → ℝ),
    1 < p → (∀ s, 0 ≤ al s) → (∀ j s, 0 ≤ cap j s) → (∀ j, 0 ≤ Pr j) →
    ∑ j, max (gainG p TT TTodd al (cap j) (de j) - Pr j - excessGain p TT (D j) al (cap j) (de j)) 0 ≤
      m * (gamP p * ∑ s ∈ TT, al s)
end Formalism.GrowthSums


