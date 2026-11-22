-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
-- name    : Formalism_QuotientMetricDivisors_Complement2Normaliser
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:47:36.03702+00:00
-- url     : https://prove2.me/theorems/2a4afacc-5152-4f82-9027-18d147d62716
-- title:
--   Complement2 Normaliser
-- statement:
--   Definitions and structural lemmas for Complement2 Normaliser, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/Complement2Normaliser.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_LogFactorialIndices_StatementSize
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
noncomputable section
namespace Formalism.DivisionValues
def PlOver {K : Type} [Field K] [NumberField K] (g : ℕ) (w : HeightOneSpectrum (𝓞 K)) : Prop :=
  0 < vw w (g : K)
def LwSumOver : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (g : ℕ), 0 < g →
    {w : HeightOneSpectrum (𝓞 K) | PlOver g w}.Finite ∧
    (∀ w : HeightOneSpectrum (𝓞 K), vw (conjPl w) (g : K) = vw w (g : K)) ∧
    (∀ w : HeightOneSpectrum (𝓞 K), PlOver g (conjPl w) ↔ PlOver g w) ∧
    (∀ w : HeightOneSpectrum (𝓞 K), 0 < lw w) ∧
    ∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : PlOver g w), lw w * (vw w (g : K) : ℝ) = Real.log g
def PlOverCoprime : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g g' : ℕ), Nat.Coprime g g' →
    ∀ w : HeightOneSpectrum (𝓞 K), ¬ (PlOver g w ∧ PlOver g' w)
def Complement2Normaliser : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (g : ℕ), 0 < g →
    ∀ pb : K, pb * star pb = (g : K) →
    ∀ (Psi : Type) [Fintype Psi] (p : Psi → K) (ν : Psi → ℕ), (∀ τ, p τ = pb) →
    ∀ w : HeightOneSpectrum (𝓞 K),
      vw w (∏ τ, p τ ^ ν τ) + vw (conjPl w) (∏ τ, p τ ^ ν τ) = ((∑ τ, ν τ : ℕ) : ℤ) * vw w (g : K)
def Complement2Scalar : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K), IsConjAt v0 →
    ∀ cg : K, ‖v0.embedding cg‖ = 1 →
    ∀ w : HeightOneSpectrum (𝓞 K), vw w cg + vw (conjPl w) cg = 0
def Complement2Arith : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (g : ℕ), 0 < g →
    ∀ (E F : HeightOneSpectrum (𝓞 K) → ℝ) (nn cg : K) (m Dpi Dp Dm er : ℝ),
    (∀ w, PlOver g w →
      |E w - (F w + (vw w nn : ℝ) - (vw w cg : ℝ) / m)| ≤ er * (vw w (g : K) : ℝ)) →
    (∀ w, PlOver g w → F w = -((Dp + Dm) / 2) * (vw w (g : K) : ℝ)) →
    (∀ w, PlOver g w → vw w cg + vw (conjPl w) cg = 0) →
    (∀ w, PlOver g w → (vw w nn : ℝ) + (vw (conjPl w) nn : ℝ) = Dpi * (vw w (g : K) : ℝ)) →
      |2 * (∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : PlOver g w), lw w * E w) -
        (Dpi - Dp - Dm) * Real.log g| ≤ 2 * er * Real.log g
def Complement2Degree : Prop :=
  ∀ (Pl : Type) [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
    (aT w nν δν δpm : Pl → ℝ) (k Dpi Dp Dm : ℝ),
    Dpi = ∑ ρ, nν ρ →
    (∀ ρ, nν ρ = (if ρ ∈ TT then aT ρ + (k - 1) * w ρ else k * w ρ) + δν ρ) →
    Dp + Dm = ∑ ρ, ((k - 1) * w ρ + δpm ρ) →
      Dpi - Dp - Dm =
        (∑ t ∈ TT, aT t) + (∑ ρ, if ρ ∈ TT then 0 else w ρ) + ∑ ρ, (δν ρ - δpm ρ)
def Complement2Sum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (g : Fin 2 → ℕ),
    (∀ i, 0 < g i) → Nat.Coprime (g 0) (g 1) →
    ∀ (E F : HeightOneSpectrum (𝓞 K) → ℝ), (Function.support E).Finite →
    ∀ (nn cg : Fin 2 → K) (m Dpi Dp Dm er Eels : ℝ),
    (∀ i w, PlOver (g i) w →
      |E w - (F w + (vw w (nn i) : ℝ) - (vw w (cg i) : ℝ) / m)| ≤ er * (vw w (g i : K) : ℝ)) →
    (∀ i w, PlOver (g i) w → F w = -((Dp + Dm) / 2) * (vw w (g i : K) : ℝ)) →
    (∀ i w, PlOver (g i) w → vw w (cg i) + vw (conjPl w) (cg i) = 0) →
    (∀ i w, PlOver (g i) w →
      (vw w (nn i) : ℝ) + (vw (conjPl w) (nn i) : ℝ) = Dpi * (vw w (g i : K) : ℝ)) →
    (∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : ∀ i, ¬ PlOver (g i) w), lw w * |E w|) ≤ Eels →
    ∀ (Pl : Type) [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
      (aT w nν δν δpm : Pl → ℝ) (k : ℝ),
    Dpi = ∑ ρ, nν ρ →
    (∀ ρ, nν ρ = (if ρ ∈ TT then aT ρ + (k - 1) * w ρ else k * w ρ) + δν ρ) →
    Dp + Dm = ∑ ρ, ((k - 1) * w ρ + δpm ρ) →
      |2 * (∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * E w) -
        (∑ t ∈ TT, aT t) * Real.log ((g 0 : ℝ) * (g 1 : ℝ))| ≤
      ((∑ ρ, if ρ ∈ TT then 0 else |w ρ|) + (∑ ρ, (|δν ρ| + |δpm ρ|)) + 2 * er) *
        Real.log ((g 0 : ℝ) * (g 1 : ℝ)) + 2 * Eels
def Complement2 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (g : Fin 2 → ℕ),
    (∀ i, 0 < g i) → Nat.Coprime (g 0) (g 1) →
    ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
      (E F : J → HeightOneSpectrum (𝓞 K) → ℝ), (∀ j, (Function.support (E j)).Finite) →
    ∀ (nn : J → Fin 2 → K) (cg : Fin 2 → K) (Dpi Dp Dm er Eels : J → ℝ)
      (aT : Pl → ℝ) (w nν δν δpm : J → Pl → ℝ)
      (x eps L b B0 m f k N S tt η w'' b' X'' logd C0 : ℝ),

    (∀ j i w, PlOver (g i) w →
      |E j w - (F j w + (vw w (nn j i) : ℝ) - (vw w (cg i) : ℝ) / m)| ≤
        er j * (vw w (g i : K) : ℝ)) →
    (∀ j i w, PlOver (g i) w → F j w = -((Dp j + Dm j) / 2) * (vw w (g i : K) : ℝ)) →
    (∀ i w, PlOver (g i) w → vw w (cg i) + vw (conjPl w) (cg i) = 0) →
    (∀ j i w, PlOver (g i) w →
      (vw w (nn j i) : ℝ) + (vw (conjPl w) (nn j i) : ℝ) = Dpi j * (vw w (g i : K) : ℝ)) →

    (∀ j, (∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : ∀ i, ¬ PlOver (g i) w), lw w * |E j w|) ≤ Eels j) →

    (∀ j, Dpi j = ∑ ρ, nν j ρ) →
    (∀ j ρ, nν j ρ = (if ρ ∈ TT then aT ρ + (k - 1) * w j ρ else k * w j ρ) + δν j ρ) →
    (∀ j, Dp j + Dm j = ∑ ρ, ((k - 1) * w j ρ + δpm j ρ)) →

    1 ≤ x → 0 < eps → L = x ^ eps → 0 ≤ b → B0 = f * m * b * x ^ eps →

    (Fintype.card J : ℝ) = m → (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f →

    1 ≤ k → 1 ≤ N → 0 ≤ S → 0 ≤ tt → 0 ≤ η → 0 ≤ b' → 0 ≤ logd →

    (∀ j ρ, 0 ≤ w j ρ ∧ w j ρ ≤ 2 * b) →

    k * S ≤ w'' → m * (tt + 1) * η ≤ w'' → N * w'' ≤ b → N * (N + tt) ≤ b → k * b' ≤ b →
    f * k * N * X'' ≤ b → logd ≤ L → Real.log ((g 0 : ℝ) * (g 1 : ℝ)) ≤ C0 * L →

    0 ≤ C0 →
    (∀ j, er j ≤ C0 * (f * (N * (N + tt) + m ^ 2 * η))) →
    (∀ j ρ, |δν j ρ| ≤ C0 * (k * S + m * tt * η + (if ρ ∈ TT then b' / x else 0))) →
    (∀ j ρ, |δpm j ρ| ≤ C0 * (k * S + m * η)) →
    (∀ j, Eels j ≤ C0 * B0 + ((TT.card : ℝ) * (2 * b + 4 * k * b') + 4 * f * k * b') * logd +
      C0 * (f * k * N * X'')) →
      (∀ j, |2 * (∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * E j w) -
        (∑ t ∈ TT, aT t) * Real.log ((g 0 : ℝ) * (g 1 : ℝ))| ≤ (9 * C0 ^ 2 + 6 * C0 + 20) * B0) ∧
      |2 * (∑ j, ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * E j w) -
        m * ((∑ t ∈ TT, aT t) * Real.log ((g 0 : ℝ) * (g 1 : ℝ)))| ≤
        (9 * C0 ^ 2 + 6 * C0 + 20) * (m * B0)
def PhLip : Prop :=
  ∀ y y' A : ℝ, 1 ≤ y → 1 ≤ y' → y ≤ A → y' ≤ A →
    |Formalism.LatticeIndexTer.ph y - Formalism.LatticeIndexTer.ph y'| ≤ |y - y'| * Real.log A
def Complement3 : Prop :=
  ∀ (U J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)] (n : ℕ)

    (hu hP logT : U → ℝ) (hK : U → J → ℝ) (aT nτ : U → Pl → ℝ) (phν nν : U → J → Pl → ℝ)
    (c : U → J → Pl → Fin n → ℝ)

    (mlam logκ cP cT e6 logOm logg : ℝ) (cK : J → ℝ) (w fa pr nr : J → Pl → ℝ)

    (x eps L b a rd La B0 m f k N S Sc tt η w'' b' Δ C0 : ℝ),

    (∀ u, hu u = hP u + ∑ j, hK u j - mlam - logκ) →
    (∀ u, hP u = -(∑ ρ, nτ u ρ) * logT u + cP) →
    (∀ u j, hK u j = ∑ ρ, (phν u j ρ - nν u j ρ * logOm) + cK j + cT * (L + logg + logT u)) →
    mlam = ∑ j, ∑ ρ, fa j ρ - e6 →

    (∀ u j ρ, phν u j ρ = ∑ i, Formalism.LatticeIndexTer.ph (w j ρ + c u j ρ i) +
      (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (aT u ρ + w j ρ) else 0) + pr j ρ) →
    (∀ u j ρ, nν u j ρ = ∑ i, (w j ρ + c u j ρ i) +
      (if ρ ∈ TT then aT u ρ + w j ρ else 0) + nr j ρ) →
    (∀ u j ρ i, 0 ≤ c u j ρ i ∧ c u j ρ i ≤ Sc) → 0 ≤ Sc → Sc ≤ 3 * S → (n : ℝ) ≤ k →
    (∀ u, ∀ ρ ∈ TT, a ≤ aT u ρ ∧ aT u ρ ≤ a + Δ) → m * Δ ≤ a →
    (∀ j ρ, 1 ≤ w j ρ ∧ w j ρ + Sc ≤ a * rd) → (∀ u j, ∀ ρ ∈ TT, aT u ρ + w j ρ ≤ a * rd) →

    (∀ u, 0 ≤ logT u ∧ logT u ≤ C0 * m * L) → 0 ≤ cT → cT ≤ C0 * (f * m ^ 2 * N ^ 2) →
    (∀ u ρ, |nτ u ρ - (if ρ ∈ TT then aT u ρ else 0)| ≤
      C0 * ((if ρ ∈ TT then b' else 0) + S + m * η + N)) →

    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → a = x * b →

    1 ≤ rd → Real.log rd ≤ L → Real.log x ≤ L → La = Real.log (a * rd) →
    B0 = f * m * b * x ^ eps →

    (Fintype.card J : ℝ) = m → (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f →

    1 ≤ k → 1 ≤ N → 0 ≤ S → 0 ≤ tt → 0 ≤ η → 0 ≤ b' → 0 ≤ C0 → |logOm| ≤ La →

    m ^ 3 * N ^ 2 * L ≤ b → k * N ≤ b → k * S ≤ w'' → m * (tt + 1) * η ≤ w'' → N * w'' ≤ b →
    m * k * b' ≤ a →
      ∀ u u', |(hu u + ∑ t ∈ TT, aT u t * logT u) - (hu u' + ∑ t ∈ TT, aT u' t * logT u')| ≤
        (7 * C0 ^ 2 + 18) * ((TT.card : ℝ) * a * La + m * B0)
end Formalism.DivisionValues


