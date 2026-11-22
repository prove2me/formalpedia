-- Prove2me | Definitions.Def_Formalism_WindowSums_Statement
-- name    : Formalism_WindowSums_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:59:54.969803+00:00
-- url     : https://prove2.me/theorems/a9fccbc2-ab4b-45d0-a62e-410df3b6491f
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WindowSums/Statement.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.WindowSums
open PowerSeries
def IdLQ {O : Type} [CommRing O] (ℓ : ℕ) (s B : ℕ) : Ideal (PowerSeries O) :=
  Ideal.span {PowerSeries.C ((ℓ : O) ^ s), (PowerSeries.X : PowerSeries O) ^ B}
def p1 {O : Type} [CommRing O] (ℓ : ℕ) (ε u : PowerSeries O) : PowerSeries O :=
  PowerSeries.C (ℓ : O) * ε + u * PowerSeries.X ^ ℓ
def R2 : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ℓ : ℕ) [Fact ℓ.Prime],
    Irreducible (ℓ : O) →
    ∀ (f₁ : PowerSeries O) (a A y B s v₁ : ℕ),
      ¬ ((ℓ : O) ^ (v₁ + 1) ∣ PowerSeries.constantCoeff f₁) →
      y + A + a + v₁ + 1 ≤ B →
      PowerSeries.C ((ℓ : O) ^ a) * f₁ * (PowerSeries.X - PowerSeries.C (ℓ : O)) ^ A *
          PowerSeries.X ^ y ∈ IdLQ (O := O) ℓ s B →
      s ≤ a + v₁
def DistinctTerms : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (ϖ : O), ϖ ≠ 0 → ¬ IsUnit ϖ →
    ∀ {ι : Type} (I : Finset ι) (w : ι → PowerSeries O) (e m : ι → ℕ) (B s : ℕ),
      (∀ i ∈ I, IsUnit (w i)) → Set.InjOn e I →
      ((∑ i ∈ I, w i * PowerSeries.X ^ e i * PowerSeries.C (ϖ ^ m i)) ∈
          Ideal.span {(PowerSeries.X : PowerSeries O) ^ B, PowerSeries.C (ϖ ^ s)} ↔
        ∀ i ∈ I, B ≤ e i ∨ s ≤ m i)
def PowMemIdealOfLe : Prop :=
  ∀ (O : Type) [CommRing O] (ℓ : ℕ) [Fact ℓ.Prime] (ε u : PowerSeries O) (y B c : ℕ),
    (c : ℝ) ≤ (y : ℝ) + 1 - (B : ℝ) / (ℓ : ℝ) →
    (p1 ℓ ε u) ^ y ∈ IdLQ (O := O) ℓ c B
def LeOfPowMemIdeal : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ℓ : ℕ) [Fact ℓ.Prime],
    Irreducible (ℓ : O) →
    ∀ (ε u : PowerSeries O), IsUnit ε → IsUnit u →
    ∀ (y B c : ℕ), 1 ≤ B →
      (p1 ℓ ε u) ^ y ∈ IdLQ (O := O) ℓ c B →
      (c : ℝ) ≤ max 0 ((y : ℝ) - (B : ℝ) / (ℓ : ℝ) + 2 + Real.logb ℓ y)
def SemilinearActionOnEigenvectorFamily : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ℓ : ℕ) [Fact ℓ.Prime],
    Irreducible (ℓ : O) →
    ∀ (ε u : PowerSeries O), IsUnit u →
    ∀ (y B : ℕ), ℓ * y < B → (p1 ℓ ε u) ^ y ∉ IdLQ (O := O) ℓ 1 B
def C1 : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ℓ : ℕ) [Fact ℓ.Prime],
    Irreducible (ℓ : O) →
    ∀ (ε u : PowerSeries O), IsUnit ε → IsUnit u →
    ∀ (b y s : ℕ), 1 ≤ y →
      (PowerSeries.X : PowerSeries O) ^ b ∈
          Ideal.span {(p1 ℓ ε u) ^ y, PowerSeries.C ((ℓ : O) ^ s)} →
      (s : ℝ) ≤ max 0 ((b : ℝ) / (ℓ : ℝ) - (y : ℝ) + 2 + Real.logb ℓ b)
def DegCmp : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (ϖ : O), Prime ϖ →
    ∀ (F G : PowerSeries O) (c : O) (k : ℕ),
      PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) G ≠ 0 →
      (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) F).order <
        (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) G).order →
      PowerSeries.C c * F ∈ Ideal.span {PowerSeries.C (ϖ ^ k), G} →
      ϖ ^ k ∣ c
def XPowDecomposition : Prop :=
  ∀ (O : Type) [CommRing O] (ℓ : ℕ) [Fact ℓ.Prime] (u : PowerSeries O) (b s : ℕ),
    s ≤ b / ℓ + 1 →
    let Bq := b / ℓ
    let Z := PowerSeries.X ^ ℓ + PowerSeries.C (ℓ : O) * u
    let α := PowerSeries.X ^ (b % ℓ) * ∑ i ∈ Finset.range s,
      PowerSeries.C ((Bq.choose i : O) * (ℓ : O) ^ (s - 1 - i)) * Z ^ i * (-u) ^ (Bq - i)
    let β := PowerSeries.X ^ (b % ℓ) * ∑ j ∈ Finset.range (Bq + 1 - s),
      PowerSeries.C ((Bq.choose (s + j) : O)) * Z ^ j * (-(PowerSeries.C (ℓ : O) * u)) ^ (Bq - s - j)
    (PowerSeries.X : PowerSeries O) ^ b = α * PowerSeries.C ((ℓ : O) ^ (Bq + 1 - s)) + β * Z ^ s
def QNilp : Prop :=
  ∀ (O : Type) [CommRing O] (ℓ : ℕ) (u : PowerSeries O) (s g : ℕ), 1 ≤ s + g →
    (PowerSeries.X : PowerSeries O) ^ (ℓ * (s + g - 1)) ∈
      Ideal.span {(PowerSeries.X ^ ℓ + PowerSeries.C (ℓ : O) * u) ^ s, PowerSeries.C ((ℓ : O) ^ g)}
def ZpowVal : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ) (s : ℕ), 1 ≤ s → (ℓ = 2 → 2 ≤ s) →
    PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s →
    ∀ j : ℤ, j ≠ 0 →
      (((u ^ j : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 ≠ 0 ∧
        PadicInt.valuation (((u ^ j : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) = s + padicValInt ℓ j)
def ValProd : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ) (s : ℕ), 1 ≤ s → (ℓ = 2 → 2 ≤ s) →
    PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s →
    (∀ M : ℕ, (∏ i ∈ Finset.Icc 1 M, (1 - (u : ℤ_[ℓ]) ^ i)) ≠ 0 ∧
      PadicInt.valuation (∏ i ∈ Finset.Icc 1 M, (1 - (u : ℤ_[ℓ]) ^ i)) =
        M * s + padicValNat ℓ M.factorial) ∧
    (∀ J : Finset ℤ, 0 ∉ J →
      (∏ j ∈ J, (1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))) ≠ 0 ∧
      PadicInt.valuation (∏ j ∈ J, (1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))) =
        J.card * s + ∑ j ∈ J, padicValInt ℓ j)
def PP (ℓ : ℕ) [Fact ℓ.Prime] (c : ℤ_[ℓ]ˣ) (ell : ℕ) (JJ : Finset ℤ) : Polynomial ℤ_[ℓ] :=
  (∏ i ∈ JJ.erase 0,
      (Polynomial.X ^ (ℓ ^ ell) - Polynomial.C ((c ^ (i * (ℓ : ℤ) ^ ell) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))) *
    ∑ k ∈ Finset.range (ℓ ^ ell), Polynomial.X ^ k
def KillerVal : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ∀ (c : ℤ_[ℓ]ˣ), PadicInt.valuation ((c : ℤ_[ℓ]) - 1) = 1 →
    ∀ (ell : ℕ) (JJ : Finset ℤ),
      (PP ℓ c ell JJ).eval 1 ≠ 0 ∧
      PadicInt.valuation ((PP ℓ c ell JJ).eval 1) =
        ∑ i ∈ JJ.erase 0, (1 + ell + padicValInt ℓ i) + ell
def KillerKills : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (c : ℤ_[ℓ]ˣ) (ell : ℕ) (JJ : Finset ℤ)
    (V : Type) [AddCommGroup V] [Module ℤ_[ℓ] V] (T : Module.End ℤ_[ℓ] V),
    (∀ x : V, (∃ i ∈ JJ.erase 0, (T ^ (ℓ ^ ell)) x = ((c ^ (i * (ℓ : ℤ) ^ ell) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • x) →
      Polynomial.aeval T (PP ℓ c ell JJ) x = 0) ∧
    (∀ v : V, (T ^ (ℓ ^ ell)) v = v → Polynomial.aeval T (PP ℓ c ell JJ) (T v - v) = 0)
def WindowSum : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (a : ℤ) (L D : ℕ) (S : Finset ℤ),
    S ⊆ Finset.Ico a (a + L) → 0 ∉ S → (∀ i ∈ S, |i| ≤ D) →
    ((∑ i ∈ S, padicValInt ℓ i : ℕ) : ℝ) ≤ (L : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ D
def RSplit : Prop :=
  ∀ (R : Type) [CommRing R] (P : Polynomial R), ∃ P₁ : Polynomial R,
    P - Polynomial.C (P.eval 1) = (Polynomial.X - 1) * P₁ ∧
    ∀ (V : Type) [AddCommGroup V] [Module R V] (T : Module.End R V) (w : V),
      P.eval 1 • w = Polynomial.aeval T P w - (T (Polynomial.aeval T P₁ w) - Polynomial.aeval T P₁ w)
def Lagrange : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (V : Type) [AddCommGroup V] [Module R V]
    (T : Module.End R V) {ι : Type} [DecidableEq ι] (I S : Finset ι) (γ : ι → R) (d : R) (x : V),
    S ⊆ I → Set.InjOn γ I →
    Polynomial.aeval T (∏ k ∈ S, (Polynomial.X - Polynomial.C (γ k))) x = 0 →
    Polynomial.aeval T (∏ k ∈ I \ S, (Polynomial.X - Polynomial.C (γ k))) x = 0 →
    (∀ k ∈ I, (∏ m ∈ I.erase k, (γ k - γ m)) ∣ d) →
    d • x = 0
def LagrangeCyc : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ) (s : ℕ), 1 ≤ s → (ℓ = 2 → 2 ≤ s) →
    PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s →
    ∀ (V : Type) [AddCommGroup V] [Module ℤ_[ℓ] V] (T : Module.End ℤ_[ℓ] V) (n : ℕ)
      (S : Finset ℕ) (x : V), S ⊆ Finset.range n →
      Polynomial.aeval T (∏ k ∈ S, (Polynomial.X - Polynomial.C ((u : ℤ_[ℓ]) ^ k))) x = 0 →
      Polynomial.aeval T (∏ k ∈ Finset.range n \ S,
        (Polynomial.X - Polynomial.C ((u : ℤ_[ℓ]) ^ k))) x = 0 →
      ((ℓ : ℤ_[ℓ]) ^ ((n - 1) * s + padicValNat ℓ (n - 1).factorial)) • x = 0
def LagrangeInt : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (V : Type) [AddCommGroup V] [Module ℤ_[ℓ] V] (T : Module.End ℤ_[ℓ] V)
    (R₁ R₂ : Finset ℤ) (x : V) (J : ℕ) (a : Fin J → ℤ) (L : Fin J → ℕ) (D E : ℕ),
    Disjoint R₁ R₂ →
    Polynomial.aeval T (∏ r ∈ R₁, (Polynomial.X - Polynomial.C (r : ℤ_[ℓ]))) x = 0 →
    Polynomial.aeval T (∏ r ∈ R₂, (Polynomial.X - Polynomial.C (r : ℤ_[ℓ]))) x = 0 →
    (∀ r ∈ R₁ ∪ R₂, ∃ j, a j ≤ r ∧ r < a j + L j) →
    (∀ r ∈ R₁ ∪ R₂, ∀ r' ∈ R₁ ∪ R₂, |r - r'| ≤ D) →
    (∑ j, ((L j : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ D)) ≤ E →
    ((ℓ : ℤ_[ℓ]) ^ E) • x = 0
def GapD : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (V : Type) [AddCommGroup V] [Module ℤ_[ℓ] V] (T : Module.End ℤ_[ℓ] V)
    (H A' S η' E : ℕ) (R₂ : Finset ℤ) (x : V),
    2 * A' + η' < H →
    R₂ ⊆ Finset.Icc ((H : ℤ) + 1) (H + S + A') ∪ Finset.Icc (1 - (η' : ℤ)) (η' + A') →
    Polynomial.aeval T (∏ i ∈ Finset.range A',
      (Polynomial.X - Polynomial.C (((H : ℤ) - i : ℤ) : ℤ_[ℓ]))) x = 0 →
    Polynomial.aeval T (∏ r ∈ R₂, (Polynomial.X - Polynomial.C (r : ℤ_[ℓ]))) x = 0 →
    ((3 * A' + S + 2 * η' : ℕ) : ℝ) / ((ℓ : ℝ) - 1) + 2 * Real.logb ℓ (H + S + A' + η' : ℕ) ≤ E →
    ((ℓ : ℤ_[ℓ]) ^ E) • x = 0
def FactorialValuationBound : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], 5 ≤ ℓ → ∀ (b S : ℕ),
    let j := (b + S) / (ℓ - 1) + 1
    (b : ℝ) / ℓ ≤ (j + padicValNat ℓ j.factorial : ℕ) ∧
    ((j + padicValNat ℓ j.factorial : ℕ) : ℝ) ≤ (b : ℝ) / ℓ + 3 * (b : ℝ) / (ℓ : ℝ) ^ 2 + 2 * S + 2
def FactorialValuationBoundOfNat : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], 5 ≤ ℓ → ∀ (h : ℕ),
    let j := h / (ℓ - 1) + 1
    (h : ℝ) / ℓ ≤ (j + padicValNat ℓ j.factorial : ℕ) ∧
    ((j + padicValNat ℓ j.factorial : ℕ) : ℝ) ≤ (h : ℝ) / ℓ + 3 * (h : ℝ) / (ℓ : ℝ) ^ 2 + 2
end Formalism.WindowSums


