-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_UntwistedChoice
-- name    : Formalism_QuotientMetricDivisors_UntwistedChoice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:09:37.658828+00:00
-- url     : https://prove2.me/theorems/ce6dde5c-0dcf-43d1-b1bc-b5fa3b5bcef3
-- title:
--   Untwisted Choice
-- statement:
--   Definitions and structural lemmas for Untwisted Choice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/UntwistedChoice.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_BoundsChain
import Definitions.Def_Formalism_QuotientMetricDivisors_StatementK
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.DivisionValues
def PrimeSumSq : Prop :=
  (∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) →
    ∑ p ∈ s, 2 * Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 999 / 1000) ∧
  Summable (fun p : Nat.Primes => 2 * Real.log ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2) ∧
  ∑' p : Nat.Primes, 2 * Real.log ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2 < 1
def PlaceSumNat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n →
    (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (vw w (n : K) : ℝ)).Finite ∧
    ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (vw w (n : K) : ℝ) = Real.log (n : ℝ) ∧
    ∀ S : Finset (HeightOneSpectrum (𝓞 K)), ∑ w ∈ S, lw w * (vw w (n : K) : ℝ) ≤ Real.log (n : ℝ)
def PlaceSumOver : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (p : ℕ), 0 < p →
    ∀ S : Finset (HeightOneSpectrum (𝓞 K)), (∀ w ∈ S, (p : 𝓞 K) ∈ w.asIdeal) →
      ∑ w ∈ S, lw w ≤ Real.log (p : ℝ)
def PrimeUnder : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∃ ell : HeightOneSpectrum (𝓞 K) → ℕ,
    ∀ w, (ell w).Prime ∧ ((ell w : ℕ) : 𝓞 K) ∈ w.asIdeal
def PlaceSumSq : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ell : HeightOneSpectrum (𝓞 K) → ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 K))),
    (∀ w ∈ S, (ell w).Prime ∧ ((ell w : ℕ) : 𝓞 K) ∈ w.asIdeal) →
      ∑ w ∈ S, lw w * ((vw w ((ell w : ℕ) : K) : ℝ) * (2 / (ell w : ℝ) ^ 2)) ≤ 999 / 1000
def PlaceSumSqPlain : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ell : HeightOneSpectrum (𝓞 K) → ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 K))),
    (∀ w ∈ S, (ell w).Prime ∧ ((ell w : ℕ) : 𝓞 K) ∈ w.asIdeal) →
      ∑ w ∈ S, lw w * (2 / (ell w : ℝ) ^ 2) ≤ 999 / 1000
def EllReal : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (p : ℕ),
    p.Prime → (p : 𝓞 K) ∈ w.asIdeal →
      1 ≤ vw w (p : K) ∧
      2 / ((p : ℝ) / Real.sqrt (vw w (p : K) : ℝ)) ^ 2 = (vw w (p : K) : ℝ) * (2 / (p : ℝ) ^ 2)
def UntwistedChoice : Prop :=
  ∀ (Pl J : Type) [Fintype J] (S Tw : Finset Pl) (D : ℕ), 0 < D → Tw ⊆ S →
    ∀ (l ell : Pl → ℝ) (I Ic jT F err Jx η : Pl → J → ℝ),
    (∀ w ∈ S, w ∉ Tw → ∀ j, I w j + Ic w j + jT w j = 0) →
    (∀ w ∈ S, w ∉ Tw → ∀ j, F w j = 0) →
    (∀ w ∈ Tw, ∑ j, (I w j + Ic w j) ≤ (∑ j, (2 * F w j + err w j) + 2 / ell w ^ 2) * D) →
    (∀ w ∈ Tw, ∀ j, jT w j ≤ Jx w j * D + η w j) →
    ∃ err' Jx' η' : Pl → J → ℝ,
      (∀ w ∈ Tw, ∀ j, err' w j = err w j ∧ Jx' w j = Jx w j ∧ η' w j = η w j) ∧
      (∀ w ∈ S, ∑ j, (I w j + Ic w j) ≤ (∑ j, (2 * F w j + err' w j) + 2 / ell w ^ 2) * D) ∧
      (∀ w ∈ S, ∀ j, jT w j ≤ Jx' w j * D + η' w j) ∧
      (∀ j, ∑ w ∈ S, l w * (err' w j + Jx' w j) = ∑ w ∈ Tw, l w * (err w j + Jx w j)) ∧
      (∀ j, ∑ w ∈ S, l w * η' w j / D = ∑ w ∈ Tw, l w * η w j / D) ∧
      (∀ j, ∑ w ∈ S, l w * F w j = ∑ w ∈ Tw, l w * F w j)
def AbsorbB : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl]
    (x eps L b B0 Nc xe m f N lam0 logg logDG C0 LG E3 logOm : ℝ)
    (pq Lj E1 E2 : J → ℝ) (w : J → Pl → ℝ),

    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → Real.log x ≤ L →

    B0 = f * m * b * x ^ eps → 0 ≤ Nc → x ^ eps ≤ xe →

    (Fintype.card J : ℝ) = m → 1 ≤ m → 1 ≤ f →

    lam0 ≤ b → N ^ 2 * logg ≤ b → N * Real.log (f * N) ≤ b →

    0 ≤ C0 →
    (∀ j, Lj j ≤ (∑ ρ, pq j * w j ρ * logOm) + C0 * B0 * Real.log (Real.log x)) →
    LG ≤ lam0 + C0 * f * N ^ 2 * logg →
    logDG ≤ C0 * f * N * Real.log (f * N) →
    (∀ j, E1 j ≤ C0 * xe * (B0 + Nc) + logDG + C0 * f * N ^ 2 * logg) →
    (∀ j, E2 j ≤ C0 * xe * (B0 + Nc)) →
    E3 ≤ 1 →
      (∑ j, Lj j) + LG + (∑ j, (E1 j + E2 j)) + E3 ≤
        (∑ j, ∑ ρ, pq j * w j ρ * logOm) + (6 * C0 + 2) * m * xe * (B0 + Nc)
def PropBPrimeSum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (J : Type) [Fintype J]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (D : ℕ) (lcvR logκ : ℝ) (lcvM : J → ℝ)
    (vG : HeightOneSpectrum (𝓞 K) → ℝ) (I Ic jT : HeightOneSpectrum (𝓞 K) → J → ℝ),
    lcvR ≤ (D : ℝ) * logκ + ∑ j, lcvM j +
      ∑ w ∈ S, lw w * (vG w + ∑ j, (I w j + Ic w j + jT w j)) →
    0 < D →

    ∀ (Tw : Finset (HeightOneSpectrum (𝓞 K))), Tw ⊆ S →
    ∀ (ell : HeightOneSpectrum (𝓞 K) → ℕ), (∀ w, (ell w).Prime ∧ ((ell w : ℕ) : 𝓞 K) ∈ w.asIdeal) →
    ∀ (F err Jj η : HeightOneSpectrum (𝓞 K) → J → ℝ),
    (∀ w ∈ S, w ∉ Tw → ∀ j, I w j +
        Ic w j +
        jT w j = 0) →
    (∀ w ∈ S, w ∉ Tw → ∀ j, F w j = 0) →

    ∀ (Pl : Type) [Fintype Pl] (x eps L b B0 Nc xe m f N C0 logOm : ℝ) (G0 g12 DG : ℕ)
      (pq : J → ℝ) (wt : J → Pl → ℝ),
    0 < G0 → 0 < g12 → 0 < DG →
    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → Real.log x ≤ L →
    B0 = f * m * b * x ^ eps → 0 ≤ Nc → x ^ eps ≤ xe →
    (Fintype.card J : ℝ) = m → 1 ≤ m → 1 ≤ f →
    Real.log (G0 : ℝ) ≤ b → N ^ 2 * Real.log (g12 : ℝ) ≤ b → N * Real.log (f * N) ≤ b →
    0 ≤ C0 →
    Real.log (DG : ℝ) ≤ C0 * f * N * Real.log (f * N) →

    (∀ w ∈ S, vG w ≤
      (D : ℝ) * ((vw w (G0 : K) : ℝ) + C0 * f * N ^ 2 * (vw w (g12 : K) : ℝ))) →

    (∀ j, lcvM j / D ≤
      (∑ r, pq j * wt j r * logOm) + C0 * B0 * Real.log (Real.log x)) →

    (∀ w ∈ Tw, ∑ j, (I w j +
        Ic w j) ≤
      (∑ j, (2 * F w j + err w j) +
        (vw w ((ell w : ℕ) : K) : ℝ) * (2 / (ell w : ℝ) ^ 2)) * D) →
    (∀ j, ∑ w ∈ Tw, lw w * (err w j + Jj w j) ≤ C0 * xe * (B0 + Nc)) →

    (∀ w ∈ Tw, ∀ j, jT w j ≤
      (Jj w j + (vw w (DG : K) : ℝ) + C0 * f * N ^ 2 * (vw w (g12 : K) : ℝ)) * D + η w j) →
    (∀ j, ∑ w ∈ Tw, lw w * η w j / D ≤ C0 * xe * (B0 + Nc)) →
      lcvR / D ≤ logκ + (∑ j, ∑ r, pq j * wt j r * logOm) +
        2 * (∑ j, ∑ w ∈ Tw, lw w * F w j) + (6 * C0 + 2) * m * xe * (B0 + Nc)
def PropBPrime : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (D : ℕ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ v, IsUnit (XE v).det) →
    ∀ (Tup : Type) (μ0 : Tup) (μ : HeightOneSpectrum (𝓞 K) → Tup), (∀ w, μ (conjPl w) = μ w) →
    {w | μ w ≠ μ0}.Finite →
    ∀ (XQ : Tup → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ t v, IsUnit (XQ t v).det) →
    ∀ (abelian₂ : Tup → Submodule (𝓞 K) (Fin D → K)), (∀ t, Submodule.IsLattice K (abelian₂ t)) →
    ∀ (ι : Tup → Matrix (Fin D) (Fin D) K), (∀ t, IsUnit (ι t).det) →
    ∀ (J : Type) [Fintype J] (d : J → ℕ)
      (XW : ∀ j, InfinitePlace K → Matrix (Fin (d j)) (Fin (d j)) ℂ), (∀ j v, IsUnit (XW j v).det) →
    ∀ (M : ∀ j, Submodule (𝓞 K) (Fin (d j) → K)), (∀ j, Submodule.IsLattice K (M j)) →
    ∀ (HT : ∀ j, Tup → Matrix (Fin (d j)) (Fin (d j)) K)
      (XT : ∀ j, Tup → InfinitePlace K → Matrix (Fin (d j)) (Fin (d j)) ℂ),
      (∀ j t, IsRatHerm K0 (HT j t) (XT j t)) →
    ∀ (T : ∀ j, Tup → Submodule (𝓞 K) (Fin (d j) → K)), (∀ j t, Submodule.IsLattice K (T j t)) →
    ∀ (θ : ∀ j, Tup → Matrix (Fin (d j)) (Fin (d j)) K), (∀ j t, IsUnit (θ j t).det) →
    ∀ (κ : InfinitePlace K → ℝ), (∀ v, 0 < κ v) →
    ∀ (ρ : Tup → K) (ρr : Tup → ℝ), (∀ t, v0.embedding (ρ t) = (ρr t : ℂ)) → ρ μ0 = 1 →
    (∀ t, 0 < ρr t) → (∀ w, vw w (ρ (μ w)) = 0) →
    (∀ v, detRatio (XQ μ0) XE (ι μ0) v = κ v ^ D * ∏ j, detRatio (XT j μ0) (XW j) (θ j μ0) v) →
    (∀ t, detRatio (XQ t) XE (ι t) v0 =
      (κ v0 * ρr t) ^ D * ∏ j, detRatio (XT j t) (XW j) (θ j t) v0) →
    ∀ (G : Tup → HeightOneSpectrum (𝓞 K) → K)
      (e : Tup → HeightOneSpectrum (𝓞 K) → Fin D → Fin D → K),
    (∀ t w, IsLocBasis (abelian₂ t) w (e t w)) →
    (∀ t w, v0.embedding (G t w) = (gram (XQ t) v0 (e t w)).det) →
    ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ i j, H i j ∈ K0) →
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ P : Matrix (Fin D) (Fin n) K, Function.Surjective P.mulVec → IsQuotMetric P H (XQ μ0) →
    ∀ Mt : Submodule (𝓞 K) (Fin n → K), Submodule.IsLattice K Mt → abelian₂ μ0 = matLat P Mt →
    (∀ w, G μ0 w = gramR (quotGram P H) (e μ0 w)) →
    ∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsLattice K R →
    (∀ w, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι (μ w)) (abelian₂ (μ w)))) →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 K))),
    (∀ w ∉ S, lw w * ((vw w (G (μ w) w) : ℝ) + ∑ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) + (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) + (jw (HT j (μ w)) w (T j (μ w)) : ℝ))) = 0) →
    0 < D →

    ∀ (Tw : Finset (HeightOneSpectrum (𝓞 K))), Tw ⊆ S →
    ∀ (ell : HeightOneSpectrum (𝓞 K) → ℕ), (∀ w, (ell w).Prime ∧ ((ell w : ℕ) : 𝓞 K) ∈ w.asIdeal) →
    ∀ (F err Jj η : HeightOneSpectrum (𝓞 K) → J → ℝ),
    (∀ w ∈ S, w ∉ Tw → ∀ j, (idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
        (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
        (jw (HT j (μ w)) w (T j (μ w)) : ℝ) = 0) →
    (∀ w ∈ S, w ∉ Tw → ∀ j, F w j = 0) →

    ∀ (Pl : Type) [Fintype Pl] (x eps L b B0 Nc xe m f N C0 logOm : ℝ) (G0 g12 DG : ℕ)
      (pq : J → ℝ) (wt : J → Pl → ℝ),
    0 < G0 → 0 < g12 → 0 < DG →
    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → Real.log x ≤ L →
    B0 = f * m * b * x ^ eps → 0 ≤ Nc → x ^ eps ≤ xe →
    (Fintype.card J : ℝ) = m → 1 ≤ m → 1 ≤ f →
    Real.log (G0 : ℝ) ≤ b → N ^ 2 * Real.log (g12 : ℝ) ≤ b → N * Real.log (f * N) ≤ b →
    0 ≤ C0 →
    Real.log (DG : ℝ) ≤ C0 * f * N * Real.log (f * N) →

    (∀ w ∈ S, (vw w (G (μ w) w) : ℝ) ≤
      (D : ℝ) * ((vw w (G0 : K) : ℝ) + C0 * f * N ^ 2 * (vw w (g12 : K) : ℝ))) →

    (∀ j, lcv (XW j) (M j) / D ≤
      (∑ r, pq j * wt j r * logOm) + C0 * B0 * Real.log (Real.log x)) →

    (∀ w ∈ Tw, ∑ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
        (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ)) ≤
      (∑ j, (2 * F w j + err w j) +
        (vw w ((ell w : ℕ) : K) : ℝ) * (2 / (ell w : ℝ) ^ 2)) * D) →
    (∀ j, ∑ w ∈ Tw, lw w * (err w j + Jj w j) ≤ C0 * xe * (B0 + Nc)) →

    (∀ w ∈ Tw, ∀ j, (jw (HT j (μ w)) w (T j (μ w)) : ℝ) ≤
      (Jj w j + (vw w (DG : K) : ℝ) + C0 * f * N ^ 2 * (vw w (g12 : K) : ℝ)) * D + η w j) →
    (∀ j, ∑ w ∈ Tw, lw w * η w j / D ≤ C0 * xe * (B0 + Nc)) →
      lcv XE R / D ≤ meanLog κ + (∑ j, ∑ r, pq j * wt j r * logOm) +
        2 * (∑ j, ∑ w ∈ Tw, lw w * F w j) + (6 * C0 + 2) * m * xe * (B0 + Nc)
def PropBPrimeW : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (D : ℕ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ v, IsUnit (XE v).det) →
    ∀ (Tup : Type) (μ0 : Tup) (μ : HeightOneSpectrum (𝓞 K) → Tup), (∀ w, μ (conjPl w) = μ w) →
    {w | μ w ≠ μ0}.Finite →
    ∀ (XQ : Tup → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ t v, IsUnit (XQ t v).det) →
    ∀ (abelian₂ : Tup → Submodule (𝓞 K) (Fin D → K)), (∀ t, Submodule.IsLattice K (abelian₂ t)) →
    ∀ (ι : Tup → Matrix (Fin D) (Fin D) K), (∀ t, IsUnit (ι t).det) →
    ∀ (J : Type) [Fintype J] (d : J → ℕ)
      (XW : ∀ j, InfinitePlace K → Matrix (Fin (d j)) (Fin (d j)) ℂ), (∀ j v, IsUnit (XW j v).det) →
    ∀ (M : ∀ j, Submodule (𝓞 K) (Fin (d j) → K)), (∀ j, Submodule.IsLattice K (M j)) →
    ∀ (HT : ∀ j, Tup → Matrix (Fin (d j)) (Fin (d j)) K)
      (XT : ∀ j, Tup → InfinitePlace K → Matrix (Fin (d j)) (Fin (d j)) ℂ),
      (∀ j, IsRatHerm K0 (HT j μ0) (XT j μ0)) → (∀ j t, IsHermAt v0 (HT j t) (XT j t)) →
    ∀ (T : ∀ j, Tup → Submodule (𝓞 K) (Fin (d j) → K)), (∀ j t, Submodule.IsLattice K (T j t)) →
    ∀ (θ : ∀ j, Tup → Matrix (Fin (d j)) (Fin (d j)) K), (∀ j t, IsUnit (θ j t).det) →
    ∀ (κ : InfinitePlace K → ℝ), (∀ v, 0 < κ v) →
    ∀ (ρ : Tup → K) (ρr : Tup → ℝ), (∀ t, v0.embedding (ρ t) = (ρr t : ℂ)) → ρ μ0 = 1 →
    (∀ t, 0 < ρr t) → (∀ w, vw w (ρ (μ w)) = 0) →
    (∀ v, detRatio (XQ μ0) XE (ι μ0) v = κ v ^ D * ∏ j, detRatio (XT j μ0) (XW j) (θ j μ0) v) →
    (∀ t, detRatio (XQ t) XE (ι t) v0 =
      (κ v0 * ρr t) ^ D * ∏ j, detRatio (XT j t) (XW j) (θ j t) v0) →
    ∀ (G : Tup → HeightOneSpectrum (𝓞 K) → K)
      (e : Tup → HeightOneSpectrum (𝓞 K) → Fin D → Fin D → K),
    (∀ t w, IsLocBasis (abelian₂ t) w (e t w)) →
    (∀ t w, v0.embedding (G t w) = (gram (XQ t) v0 (e t w)).det) →
    ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ i j, H i j ∈ K0) →
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ P : Matrix (Fin D) (Fin n) K, Function.Surjective P.mulVec → IsQuotMetric P H (XQ μ0) →
    ∀ Mt : Submodule (𝓞 K) (Fin n → K), Submodule.IsLattice K Mt → abelian₂ μ0 = matLat P Mt →
    (∀ w, G μ0 w = gramR (quotGram P H) (e μ0 w)) →
    ∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsLattice K R →
    (∀ w, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι (μ w)) (abelian₂ (μ w)))) →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 K))),
    (∀ w ∉ S, lw w * ((vw w (G (μ w) w) : ℝ) + ∑ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) + (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) + (jw (HT j (μ w)) w (T j (μ w)) : ℝ))) = 0) →
    0 < D →

    ∀ (Tw : Finset (HeightOneSpectrum (𝓞 K))), Tw ⊆ S →
    ∀ (ell : HeightOneSpectrum (𝓞 K) → ℕ), (∀ w, (ell w).Prime ∧ ((ell w : ℕ) : 𝓞 K) ∈ w.asIdeal) →
    ∀ (F err Jj η : HeightOneSpectrum (𝓞 K) → J → ℝ),
    (∀ w ∈ S, w ∉ Tw → ∀ j, (idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
        (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
        (jw (HT j (μ w)) w (T j (μ w)) : ℝ) = 0) →
    (∀ w ∈ S, w ∉ Tw → ∀ j, F w j = 0) →

    ∀ (Pl : Type) [Fintype Pl] (x eps L b B0 Nc xe m f N C0 logOm : ℝ) (G0 g12 DG : ℕ)
      (pq : J → ℝ) (wt : J → Pl → ℝ),
    0 < G0 → 0 < g12 → 0 < DG →
    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → Real.log x ≤ L →
    B0 = f * m * b * x ^ eps → 0 ≤ Nc → x ^ eps ≤ xe →
    (Fintype.card J : ℝ) = m → 1 ≤ m → 1 ≤ f →
    Real.log (G0 : ℝ) ≤ b → N ^ 2 * Real.log (g12 : ℝ) ≤ b → N * Real.log (f * N) ≤ b →
    0 ≤ C0 →
    Real.log (DG : ℝ) ≤ C0 * f * N * Real.log (f * N) →

    (∀ w ∈ S, (vw w (G (μ w) w) : ℝ) ≤
      (D : ℝ) * ((vw w (G0 : K) : ℝ) + C0 * f * N ^ 2 * (vw w (g12 : K) : ℝ))) →

    (∀ j, lcv (XW j) (M j) / D ≤
      (∑ r, pq j * wt j r * logOm) + C0 * B0 * Real.log (Real.log x)) →

    (∀ w ∈ Tw, ∑ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
        (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ)) ≤
      (∑ j, (2 * F w j + err w j) +
        (vw w ((ell w : ℕ) : K) : ℝ) * (2 / (ell w : ℝ) ^ 2)) * D) →
    (∀ j, ∑ w ∈ Tw, lw w * (err w j + Jj w j) ≤ C0 * xe * (B0 + Nc)) →

    (∀ w ∈ Tw, ∀ j, (jw (HT j (μ w)) w (T j (μ w)) : ℝ) ≤
      (Jj w j + (vw w (DG : K) : ℝ) + C0 * f * N ^ 2 * (vw w (g12 : K) : ℝ)) * D + η w j) →
    (∀ j, ∑ w ∈ Tw, lw w * η w j / D ≤ C0 * xe * (B0 + Nc)) →
      lcv XE R / D ≤ meanLog κ + (∑ j, ∑ r, pq j * wt j r * logOm) +
        2 * (∑ j, ∑ w ∈ Tw, lw w * F w j) + (6 * C0 + 2) * m * xe * (B0 + Nc)
def DivIneqWithB : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]

    (muC mu0 Fo hu hP mlam logT : ℝ) (hK : J → ℝ) (aT : Pl → ℝ) (phν nν fa : J → Pl → ℝ)

    (x eps L b a rd La B0 Nc xe m f k N S tt η w'' b' dC lam0 C0 : ℝ)

    (Lpass e6 eP logOm : ℝ) (eK pq : J → ℝ) (w eE δ : J → Pl → ℝ)

    (logg logDG LG E3 : ℝ) (Lj E1 E2 : J → ℝ),

    muC ≤ mu0 + Lpass →
    mu0 ≤ (∑ j, Lj j) + 2 * Fo + LG + (∑ j, (E1 j + E2 j)) + E3 →
    hu = hP + ∑ j, hK j - mlam →
    (∀ j, hK j ≤ ∑ ρ, (phν j ρ - nν j ρ * logOm) + eK j) →
    ∑ j, ∑ ρ, fa j ρ - e6 ≤ mlam →
    hP ≤ -(∑ t ∈ TT, aT t * logT) + eP →
    (∀ j ρ, phν j ρ - fa j ρ ≤ (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (aT ρ) else 0) + eE j ρ) →
    (∀ j ρ, nν j ρ = (if ρ ∈ TT then aT ρ else 0) + k * w j ρ + δ j ρ) →

    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → a = x * b →

    1 ≤ rd → Real.log rd ≤ L → Real.log x ≤ L → La = Real.log (a * rd) →

    B0 = f * m * b * x ^ eps → 0 ≤ Nc → x ^ eps ≤ xe →

    (Fintype.card J : ℝ) = m → (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f →

    1 ≤ k → 1 ≤ N → 0 ≤ S → 0 ≤ tt → 0 ≤ η → 1 ≤ dC → 0 ≤ lam0 → 0 ≤ b' →

    (∀ j ρ, 0 ≤ w j ρ ∧ w j ρ ≤ 2 * b) →

    (∀ j, |pq j - k| ≤ m) → |logOm| ≤ La →

    lam0 ≤ b → N ^ 2 * dC ≤ b → m ^ 3 * N ^ 2 * L ≤ b → m * η * N * L ≤ b → k * N ≤ b →
    k * S ≤ w'' → m * (tt + 1) * η ≤ w'' → N * w'' ≤ b → b' * N ≤ a → m * k * b' ≤ a →
    N ^ 2 * logg ≤ b → N * Real.log (f * N) ≤ b →

    0 ≤ C0 →
    Lpass ≤ 1 + C0 * lam0 →
    (∀ j, Lj j ≤ (∑ ρ, pq j * w j ρ * logOm) + C0 * B0 * Real.log (Real.log x)) →
    LG ≤ lam0 + C0 * f * N ^ 2 * logg →
    logDG ≤ C0 * f * N * Real.log (f * N) →
    (∀ j, E1 j ≤ C0 * xe * (B0 + Nc) + logDG + C0 * f * N ^ 2 * logg) →
    (∀ j, E2 j ≤ C0 * xe * (B0 + Nc)) →
    E3 ≤ 1 →
    (∀ j, eK j ≤ C0 * (f * N ^ 2 * (La + dC) + f * m ^ 3 * N ^ 2 * L)) →
    e6 ≤ C0 * m * f * N ^ 2 * La →
    eP ≤ C0 * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La →
    (∀ j ρ, eE j ρ ≤ C0 * (w j ρ + S + N ^ 2 + m * (tt + 1) * η) * La) →
    (∀ j ρ, |δ j ρ| ≤
      C0 * (w j ρ + k * (N + S) + m * (tt + 1) * η + (if ρ ∈ TT then k * b' else 0))) →
      muC + hu - 2 * Fo ≤
        ∑ t ∈ TT, (m * (Formalism.LatticeIndexTer.ph (aT t) - aT t * logOm) - aT t * logT) +
        (50 * (6 * C0 + 2) + 10) * ((TT.card : ℝ) * a * La + m * (B0 + Nc) * xe)
end Formalism.DivisionValues


