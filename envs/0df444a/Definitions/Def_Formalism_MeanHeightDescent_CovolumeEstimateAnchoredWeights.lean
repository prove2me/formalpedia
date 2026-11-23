-- Prove2me | Definitions.Def_Formalism_MeanHeightDescent_CovolumeEstimateAnchoredWeights
-- name    : Formalism_MeanHeightDescent_CovolumeEstimateAnchoredWeights
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:21:40.529857+00:00
-- url     : https://prove2.me/theorems/0b10784f-f0d8-45ae-b321-9284fabf600d
-- title:
--   Covolume Estimate Anchored Weights
-- statement:
--   Definitions and structural lemmas for Covolume Estimate Anchored Weights, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/CovolumeEstimateAnchoredWeights.lean

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_StatementA
import Definitions.Def_Formalism_MeanHeightDescent_StatementF
import Definitions.Def_Formalism_MeanHeightDescent_StatementJ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module NumberField
noncomputable section
namespace Formalism.ExtensionFiltration
def WShift : Prop :=
  ∀ (Pl : Type) [Fintype Pl] (w w0 : Pl → ℝ) (lcvD pq logOm C3 B0 llx La f m k Δ b xe : ℝ),
    lcvD ≤ (∑ ρ, pq * w ρ * logOm) + C3 * B0 * llx →
    (∀ ρ, |w ρ - w0 ρ| ≤ Δ) → 0 ≤ Δ → |pq - k| ≤ m → |logOm| ≤ La → La ≤ 3 * xe →
    (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ k → k * Δ ≤ 2 * b → B0 = f * m * b * xe → 1 ≤ llx →
    lcvD ≤ (∑ ρ, pq * w0 ρ * logOm) + (C3 + 12) * B0 * llx
def WShiftConst : Prop :=
  ∀ (Pl : Type) [Fintype Pl] (w w0 : Pl → ℝ) (lcvD pq logOm C3 B0 llx La f m k Δ b xe CO : ℝ),
    lcvD ≤ (∑ ρ, pq * w ρ * logOm) + C3 * B0 * llx →
    (∀ ρ, |w ρ - w0 ρ| ≤ Δ) → 0 ≤ Δ → |pq - k| ≤ m → 1 ≤ CO → |logOm| ≤ CO * La → La ≤ 3 * xe →
    (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ k → k * Δ ≤ 2 * b → B0 = f * m * b * xe → 1 ≤ llx →
    lcvD ≤ (∑ ρ, pq * w0 ρ * logOm) + (C3 + 12 * CO) * B0 * llx
def PeriodBound : Prop :=
  ∀ (logOm v rd Lc L x b a : ℝ),
    logOm = Real.eulerMascheroniConstant + Real.log (Real.pi / v) - Lc → 2 * v = rd → 4 ≤ rd →
    |Lc| ≤ L → 1 ≤ x → b = Real.exp L → a = x * b →
    |logOm| ≤ Real.log (a * rd)
def CovolumeEstimateAnchoredWeights : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (d D : ℕ),
    0 < D → d = D →
    ∀ XW : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ, (∀ v, IsUnit (XW v).det) →
    ∀ M : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K M →
    ∀ (Pl : Type) [Fintype Pl] (w w0 c1 ua : Pl → ℝ)
      (muU muA muN muG mmax dA dB dN dg db : ℝ)
      (C1 Cf Cc cfl ε δ Q P Λ G P9 : ℝ)
      (pq q' logOm x eps L b rd Lchi llx LL0 B0 f m k S η a La R CO : ℝ),

    -(2 * (C1 * LL0 * (∑ τ, ua τ) + b / 4)) ≤ muU →

    cfl = (∑ τ, w τ * c1 τ) - Cf * q' * Real.log rd * (∑ τ, w τ) - Cf * L →
    muU + 2 * cfl ≤ muA →

    0 < dA → dA ≤ dB → (1 - ε) * dB ≤ dA → 0 ≤ ε → 0 ≤ P →
    dA * (muA - P) + (dB - dA) * (-Λ) ≤ dB * muN →
    |2 * cfl| ≤ Q → Λ ≤ Q → ε * Q ≤ b / 4 →

    0 < dN → dN = dg + db → 0 ≤ db → db ≤ 3 * δ * dN → 0 ≤ δ → δ ≤ 1 / 12 →
    dN * muN ≤ dg * muG + db * (mmax + G) → |muN| ≤ Q → mmax ≤ Q → G ≤ Q →

    muG - P9 ≤ Formalism.HN.muDef (Pi.basisFun K (Fin d)) XW M →
    P + 12 * δ * Q + P9 ≤ b →

    (∀ τ, |c1 τ + pq * logOm / 2| ≤ Cc * q' * (Real.log rd + Lchi)) →

    (∀ τ, m * w τ / 2 ≤ ua τ ∧ ua τ ≤ 2 * (m * w τ + k * S + k * η)) → 1 ≤ (∑ τ, ua τ) →
    (∀ τ, 0 ≤ w τ ∧ w τ ≤ 2 * b) → k * S ≤ b → k * η ≤ b →
    (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f → 0 ≤ q' → q' ≤ m →

    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → 1 ≤ rd → Real.log rd ≤ L →
    0 ≤ Lchi → Lchi ≤ L → Real.log x ≤ L → 1 ≤ llx →
    LL0 = Real.log (b * rd) * llx + Lchi + Real.log x →
    B0 = f * m * b * x ^ eps → 0 ≤ C1 → 0 ≤ Cf → 0 ≤ Cc →

    (∀ ρ, |w ρ - w0 ρ| ≤ S + R) → 0 ≤ S → 0 ≤ R → k * R ≤ b → 1 ≤ k →
    |pq - k| ≤ m → a = x * b → La = Real.log (a * rd) → 1 ≤ CO → |logOm| ≤ CO * La →
    Formalism.DivisionValues.lcv XW M / D ≤
      (∑ ρ, pq * w0 ρ * logOm) + (64 * (C1 + 3 * Cf) + 8 * Cc + 2 + 12 * CO) * B0 * llx
def CovolumeEstimateOfAverageDegreeWeighted : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (d D : ℕ),
    0 < D → d = D →
    ∀ XW : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ, (∀ v, IsUnit (XW v).det) →
    ∀ M : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K M →
    ∀ (Pl : Type) [Fintype Pl] (w w0 c1 ua : Pl → ℝ)
      (ι : Type) [Fintype ι] [Nonempty ι] (T DY A cs X cc z ρ R1 R2 Bn δ' : ℝ)
      (h sl δc dc degc : ι → ℝ) (Ca Cb PPf e1 e2 : ℝ)
      (muU muA muN muG mmax dA dB dN dg db : ℝ)
      (Cf Cc cfl ε δ Q P Λ G P9 : ℝ)
      (pq q' logOm x eps L b rd Lchi llx LL0 B0 f m k S η a La R CO : ℝ),

    0 ≤ DY → 3 * DY + 5 ≤ T → 0 < A → 0 ≤ cs → 0 ≤ X → 0 ≤ cc → 0 ≤ z → z < 1 → 0 ≤ ρ → ρ < 1 →
    0 ≤ R1 → 0 ≤ R2 → 0 < Bn → 0 < δ' →
    (∀ c, δ' ≤ δc c ∧ δc c ≤ δ' / (1 - ρ)) →
    (∀ c, Bn * δc c ≤ dc c ∧ (1 - z) * dc c ≤ Bn * δc c) →
    (∀ c, 0 ≤ h c + cs) →
    (∀ c, (1 - ρ) * max 0 (sl c + cs) ≤ h c + cs + cc) →
    -X ≤ (∑ c, sl c) / (Fintype.card ι : ℝ) →
    (∀ c, Bn * δc c *
        (T * h c - 3 * (DY + 1) * |h c| - A * Real.log (2 + |h c|) - R1 - 2 * z * R2) ≤ degc c) →
    T * X ≤ Ca * LL0 * (∑ τ, ua τ) + e1 → T * cc ≤ Cb * LL0 * (∑ τ, ua τ) + e2 →
    cs * (6 * DY + 10 + T * (z + 2 * ρ)) + (A * Real.log (max A 1) + 4) + R1 + 2 * z * R2 + PPf
      + e1 + e2 ≤ b / 4 →
    2 * ((∑ c, degc c) / (∑ c, dc c) - PPf) ≤ muU →

    cfl = (∑ τ, w τ * c1 τ) - Cf * q' * Real.log rd * (∑ τ, w τ) - Cf * L →
    muU + 2 * cfl ≤ muA →

    0 < dA → dA ≤ dB → (1 - ε) * dB ≤ dA → 0 ≤ ε → 0 ≤ P →
    dA * (muA - P) + (dB - dA) * (-Λ) ≤ dB * muN →
    |2 * cfl| ≤ Q → Λ ≤ Q → ε * Q ≤ b / 4 →

    0 < dN → dN = dg + db → 0 ≤ db → db ≤ 3 * δ * dN → 0 ≤ δ → δ ≤ 1 / 12 →
    dN * muN ≤ dg * muG + db * (mmax + G) → |muN| ≤ Q → mmax ≤ Q → G ≤ Q →

    muG - P9 ≤ Formalism.HN.muDef (Pi.basisFun K (Fin d)) XW M →
    P + 12 * δ * Q + P9 ≤ b →

    (∀ τ, |c1 τ + pq * logOm / 2| ≤ Cc * q' * (Real.log rd + Lchi)) →

    (∀ τ, m * w τ / 2 ≤ ua τ ∧ ua τ ≤ 2 * (m * w τ + k * S + k * η)) → 1 ≤ (∑ τ, ua τ) →
    (∀ τ, 0 ≤ w τ ∧ w τ ≤ 2 * b) → k * S ≤ b → k * η ≤ b →
    (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f → 0 ≤ q' → q' ≤ m →

    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → 1 ≤ rd → Real.log rd ≤ L →
    0 ≤ Lchi → Lchi ≤ L → Real.log x ≤ L → 1 ≤ llx →
    LL0 = Real.log (b * rd) * llx + Lchi + Real.log x →
    B0 = f * m * b * x ^ eps → 0 ≤ Ca → 0 ≤ Cb → 0 ≤ Cf → 0 ≤ Cc →

    (∀ σ, |w σ - w0 σ| ≤ S + R) → 0 ≤ S → 0 ≤ R → k * R ≤ b → 1 ≤ k →
    |pq - k| ≤ m → a = x * b → La = Real.log (a * rd) → 1 ≤ CO → |logOm| ≤ CO * La →
    Formalism.DivisionValues.lcv XW M / D ≤
      (∑ σ, pq * w0 σ * logOm) + (64 * (Ca + Cb + 3 * Cf) + 8 * Cc + 2 + 12 * CO) * B0 * llx
def PerturbedWeightedSumEstimate : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl]
    (mu0 Fo LG E3 logOm B0 Nc llx xe m C3 Cn La f k Δ b xq : ℝ)
    (Lj E1 E2 pq : J → ℝ) (w w0 : J → Pl → ℝ),
    mu0 ≤ (∑ j, Lj j) + 2 * Fo + LG + (∑ j, (E1 j + E2 j)) + E3 →
    (∀ j, Lj j ≤ (∑ ρ, pq j * w j ρ * logOm) + C3 * B0 * llx) →
    (∀ j ρ, |w j ρ - w0 j ρ| ≤ Δ) → 0 ≤ Δ → (∀ j, |pq j - k| ≤ m) → |logOm| ≤ La → La ≤ 3 * xq →
    (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ k → k * Δ ≤ 2 * b → B0 = f * m * b * xq → 1 ≤ llx →
    LG + (∑ j, (E1 j + E2 j)) + E3 ≤ Cn * m * xe * (B0 + Nc) →
    (Fintype.card J : ℝ) = m → llx ≤ xe → 0 ≤ Nc → 0 ≤ C3 →
    ∃ Eb : ℝ, mu0 ≤ (∑ j, ∑ ρ, pq j * w0 j ρ * logOm) + 2 * Fo + Eb ∧
      Eb ≤ (C3 + 12 + Cn) * m * xe * (B0 + Nc)
def DivisionInequalityWeighted : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]

    (muC mu0 Fo hu hP mlam logT : ℝ) (hK : J → ℝ) (aT : Pl → ℝ) (phν nν fa : J → Pl → ℝ)

    (x eps L b a rd La B0 Nc xe m f k N S tt η w'' b' lam0 C0 : ℝ)

    (Lpass e6 eP logOm : ℝ) (eK pq : J → ℝ) (w eE δ : J → Pl → ℝ)

    (LG E3 llx C3 Cn R : ℝ) (Lj E1 E2 : J → ℝ) (wA : J → Pl → ℝ),

    muC ≤ mu0 + Lpass →
    mu0 ≤ (∑ j, Lj j) + 2 * Fo + LG + (∑ j, (E1 j + E2 j)) + E3 →
    (∀ j, Lj j ≤ (∑ ρ, pq j * wA j ρ * logOm) + C3 * B0 * llx) →
    (∀ j ρ, |wA j ρ - w j ρ| ≤ S + R) → 0 ≤ R → k * R ≤ b → 1 ≤ llx →
    LG + (∑ j, (E1 j + E2 j)) + E3 ≤ Cn * m * xe * (B0 + Nc) →
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

    1 ≤ k → 1 ≤ N → 0 ≤ S → 0 ≤ tt → 0 ≤ η →

    (∀ j ρ, 0 ≤ w j ρ ∧ w j ρ ≤ 2 * b) →

    (∀ j, |pq j - k| ≤ m) → |logOm| ≤ La →

    lam0 ≤ b → N ^ 2 ≤ b → m ^ 3 * N ^ 2 * L ≤ b → m * η * N * L ≤ b → k * N ≤ b →
    k * S ≤ w'' → m * (tt + 1) * η ≤ w'' → N * w'' ≤ b → b' * N ≤ a → m * k * b' ≤ a →

    0 ≤ C0 →
    Lpass ≤ 1 + C0 * lam0 →
    C3 + 12 + Cn ≤ C0 → llx ≤ xe → 0 ≤ C3 →
    (∀ j, eK j ≤ C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L)) →
    e6 ≤ C0 * m * f * N ^ 2 * La →
    eP ≤ C0 * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La →
    (∀ j ρ, eE j ρ ≤ C0 * (w j ρ + S + N ^ 2 + m * (tt + 1) * η) * La) →
    (∀ j ρ, |δ j ρ| ≤
      C0 * (w j ρ + k * (N + S) + m * (tt + 1) * η + (if ρ ∈ TT then k * b' else 0))) →
      muC + hu - 2 * Fo ≤
        ∑ t ∈ TT, (m * (Formalism.LatticeIndexTer.ph (aT t) - aT t * logOm) - aT t * logT) +
        (50 * C0 + 10) * ((TT.card : ℝ) * a * La + m * (B0 + Nc) * xe)
def kapBig (p q i : ℤ) : ℤ := q - p - 1 + 2 * i
def kapSmall (p q i : ℤ) : ℤ := -p - q - 1 + 2 * i
def KapVector : Prop :=
  ∀ (p q : ℕ),
    (∑ i ∈ Finset.Icc 1 p, kapBig p q i) + (∑ i ∈ Finset.Icc 1 q, kapSmall p q i) = 0 ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ p → |kapBig p q i| ≤ (p : ℤ) + q - 1) ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ q → |kapSmall p q i| ≤ (p : ℤ) + q - 1) ∧
    (∀ i : ℤ, kapBig p q i - kapBig p q (i + 1) = -2) ∧
    (∀ i : ℤ, kapSmall p q i - kapSmall p q (i + 1) = -2) ∧
    kapBig p q p - kapSmall p q 1 = 2 * ((p : ℤ) + q) - 2 ∧
    (∀ k j : ℤ, (p : ℤ) = k - 1 + j → kapBig p q (k - 1) = ((p : ℤ) + q) - 1 - 2 * j)
def AnchoredFloor : Prop :=
  ∀ (N A T D : ℕ) (x u1 : ℕ → ℤ), A < N →
    (∀ i, i + 1 < N → 0 ≤ x i - x (i + 1)) →
    (∀ i, i + 1 < N → u1 i - u1 (i + 1) = (x i - x (i + 1)) / ((T : ℤ) + D + 1)) →
    u1 A = 0 →
    ∀ i, i < N → ((T : ℤ) + D + 1) * |u1 i| ≤ |x i - x A|
def AnchoredQuotientTotalBound : Prop :=
  ∀ (Pl : Type) [Fintype Pl] (N T D jj f : ℕ) (c0 : ℤ) (A p : Pl → ℕ) (u x u1 kap : Pl → ℕ → ℤ),
    (∀ τ, A τ < p τ ∧ p τ ≤ N ∧ N ≤ p τ + jj) → 0 ≤ c0 → Fintype.card Pl ≤ f →
    (∀ τ i, i < N → x τ i = u τ i - c0 * (if i < p τ then 0 else -1) - kap τ i) →
    (∀ τ i, i < N → |kap τ i| ≤ 2 * (N : ℤ)) →
    (∀ τ i, i + 1 < N → 0 ≤ x τ i - x τ (i + 1)) →
    (∀ τ i, i + 1 < N → u1 τ i - u1 τ (i + 1) = (x τ i - x τ (i + 1)) / ((T : ℤ) + D + 1)) →
    (∀ τ, u1 τ (A τ) = 0) → (∀ τ, u τ (A τ) = 0) →
    ((T : ℤ) + D + 1) * (∑ τ, ∑ i ∈ Finset.range N, |u1 τ i|) ≤
      (∑ τ, ∑ i ∈ Finset.range N, |u τ i|) + c0 * f * jj + 4 * f * (N : ℤ) ^ 2 ∧
    (T : ℤ) * (∑ τ, ∑ i ∈ Finset.range N, |u1 τ i|) ≤
      (∑ τ, ∑ i ∈ Finset.range N, |u τ i|) + c0 * f * jj + 4 * f * (N : ℤ) ^ 2
def AnchoredQuotientExact : Prop :=
  ∀ (N A T D : ℕ) (um kap u1 rem : ℕ → ℤ), A < N →
    (∀ i, i + 1 < N → u1 i - u1 (i + 1) =
      ((um i - kap i) - (um (i + 1) - kap (i + 1))) / ((T : ℤ) + D + 1)) →
    (∀ i, i + 1 < N → rem i - rem (i + 1) =
      ((um i - kap i) - (um (i + 1) - kap (i + 1))) % ((T : ℤ) + D + 1)) →
    u1 A = 0 → rem A = 0 → um A = 0 →
    ∀ i, i < N → um i = (kap i + (u1 i + rem i) + D * u1 i) + T * u1 i - kap A
def QuotientGapsLowerBound : Prop :=
  ∀ (T D N : ℕ) (h0 c0 g : ℤ),
    (((T : ℤ) + D + 2) * ((T : ℤ) + D + 2 + 2 * N) ≤ g →
      (T : ℤ) + D + 2 + 2 * N ≤ (g + 2) / ((T : ℤ) + D + 1)) ∧
    (4 * D + 4 ≤ T → 0 ≤ c0 → 4 * (c0 + 2 * N + T + D + 1) ≤ h0 → h0 ≤ g →
      h0 ≤ 2 * T * ((g - c0 - (2 * N - 2)) / ((T : ℤ) + D + 1)) ∧
      (24 * (N : ℤ) * T ≤ h0 → h0 ≤ 4 * T * ((g - c0 - (2 * N - 2)) / ((T : ℤ) + D + 1) - 3 * N)))
def SpreadBound : Prop :=
  ∀ (Pl : Type) [Fintype Pl] (N m : ℕ) (T jj : ℝ) (w mx mn : Pl → ℝ) (u' : Pl → ℕ → ℝ)
    (nodes : Pl → Finset ℕ),
    0 < T → 0 ≤ jj → jj ≤ m → (∀ τ, 0 ≤ w τ) →
    (∀ τ, nodes τ ⊆ Finset.range N ∧ (nodes τ).card = m) →
    (∀ τ, mx τ - mn τ ≤ 3 / 2 * w τ / T) →
    (∀ τ, ∀ i ∈ nodes τ, w τ / (4 * T) ≤ |u' τ i|) →
    jj * (∑ τ, (mx τ - mn τ)) ≤ 6 * (∑ τ, ∑ i ∈ Finset.range N, |u' τ i|)
def MKShort : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (B : Submodule (𝓞 K) V), B.FG → Formalism.HN.rkK B = 1 →
      ∃ x ∈ B, x ≠ 0 ∧ ∀ v, 2 * Real.log (Formalism.HermitianLatticesTheory.normAt b X v x) ≤
        -(Formalism.HN.muDef b X B) + Formalism.HN.logDisc K / (Module.finrank ℚ K : ℝ) + Real.log (2 / Real.pi)
def SumSplitClass : Prop :=
  ∀ (Q : Finset ℕ) (e : ℕ → ℝ) (A M : ℝ),
    (∀ p ∈ Q, 2 ≤ p) → 0 ≤ A → (∀ p ∈ Q, e p ≤ A / ((p : ℝ) - 1)) →
    (∑ p ∈ Q, Real.log p / ((p : ℝ) - 1)) ≤ M →
    (∑ p ∈ Q, e p * Real.log p) ≤ A * M
def SumInertSmall : Prop :=
  ∀ (Q : Finset ℕ) (Φ : Type) [Fintype Φ] (e : ℕ → ℝ) (c i : Φ → ℝ) (m j' N sm y0 b S1 S0 : ℝ),
    (∀ p ∈ Q, 3 ≤ p ∧ (p : ℝ) < y0) →
    (∀ φ, 1 ≤ c φ ∧ c φ ≤ b) → (∀ φ, 0 ≤ i φ ∧ i φ ≤ N) → 0 ≤ j' → j' ≤ m → 0 ≤ sm →
    (∀ p ∈ Q, e p ≤ (∑ φ, (c φ * m * p / ((p : ℝ) ^ 2 - 1)
        + c φ * j' * (3 + (1 / 2) * Real.logb p (c φ)) / ((p : ℝ) - 1)
        + (i φ) ^ 2 * (Real.logb p (c φ) + 1))) + sm / ((p : ℝ) - 1)) →
    (∑ p ∈ Q, Real.log p / ((p : ℝ) - 1)) ≤ S1 → (∑ p ∈ Q, 1 / ((p : ℝ) - 1)) ≤ S0 →
    (∑ p ∈ Q, e p * Real.log p) ≤
      (4 * m * (∑ φ, c φ) + sm) * S1 + (1 / 2) * m * (∑ φ, c φ) * Real.log b * S0
        + (Fintype.card Φ : ℝ) * N ^ 2 * (Q.card : ℝ) * (Real.log b + Real.log y0)
def SumAtTwo : Prop :=
  ∀ (e2 C s u1 n x : ℝ), 0 ≤ C → 0 ≤ u1 → e2 ≤ C * (s + 2) * u1 → s ≤ Real.logb 2 (4 * n) → 1 ≤ n →
    Real.log (16 * n) ≤ C * Real.log x → e2 * Real.log 2 ≤ u1 * (C ^ 2 * Real.log x)
def SumRamified : Prop :=
  ∀ (Pe : Finset ℕ) (e : ℕ → ℝ) (T DF C k m U PPd : ℝ), 0 ≤ T → 0 ≤ U → 0 ≤ PPd →
    (∀ p ∈ Pe, 2 ≤ p) → (∀ p ∈ Pe, e p ≤ DF / ((p : ℝ) - 1)) →
    (∀ p ∈ Pe, C * (k / m) * Real.log p ≤ (p : ℝ) - 1) →
    T * DF ≤ C * (k / m) * U + T * PPd →
    T * (∑ p ∈ Pe, e p * Real.log p) ≤ (Pe.card : ℝ) * (U + T * PPd)
def SumTotal : Prop :=
  ∀ (Pl : Type) [Fintype Pl] (ua : Pl → ℝ) (P Pab Pc Pe Pf : Finset ℕ) (Φ : Type) [Fintype Φ]
    (eloc : ℕ → ℝ) (c i : Φ → ℝ)
    (T u1 primePairSetFirst PPc PPd C m j' k N sm y0 DF s n x b rd Lchi llx LL0 : ℝ),
    P ⊆ Pab ∪ Pc ∪ {2} ∪ Pe ∪ Pf → (∀ p, 0 ≤ eloc p) →
    1 ≤ C → 0 ≤ T → 0 ≤ u1 → 0 ≤ primePairSetFirst → 0 ≤ PPd → 0 ≤ (∑ τ, ua τ) → T * u1 ≤ (∑ τ, ua τ) + primePairSetFirst →

    (∀ p ∈ Pab, 2 ≤ p) → (∀ p ∈ Pab, eloc p ≤ C * u1 / ((p : ℝ) - 1)) →
    (∑ p ∈ Pab, Real.log p / ((p : ℝ) - 1)) ≤ C * Real.log DF → Real.log DF ≤ C * Real.log b →

    (∀ p ∈ Pc, 3 ≤ p ∧ (p : ℝ) < y0) →
    (∀ φ, 1 ≤ c φ ∧ c φ ≤ b) → (∀ φ, 0 ≤ i φ ∧ i φ ≤ N) → 0 ≤ j' → j' ≤ m → 0 ≤ sm →
    (∀ p ∈ Pc, eloc p ≤ (∑ φ, (c φ * m * p / ((p : ℝ) ^ 2 - 1)
        + c φ * j' * (3 + (1 / 2) * Real.logb p (c φ)) / ((p : ℝ) - 1)
        + (i φ) ^ 2 * (Real.logb p (c φ) + 1))) + sm / ((p : ℝ) - 1)) →
    (∑ p ∈ Pc, Real.log p / ((p : ℝ) - 1)) ≤ C * Real.log y0 →
    (∑ p ∈ Pc, 1 / ((p : ℝ) - 1)) ≤ Real.log (Real.log y0) + 1 →
    Real.log y0 ≤ C * Real.log x → Real.log (Real.log y0) + 1 ≤ C * llx →
    m * (∑ φ, c φ) ≤ C * u1 → sm ≤ C * u1 →
    (Fintype.card Φ : ℝ) * N ^ 2 * (Pc.card : ℝ) * (Real.log b + Real.log y0) ≤ PPc →

    eloc 2 ≤ C * (s + 2) * u1 → s ≤ Real.logb 2 (4 * n) → 1 ≤ n → Real.log (16 * n) ≤ C * Real.log x →

    (∀ p ∈ Pe, 2 ≤ p) → (∀ p ∈ Pe, eloc p ≤ DF / ((p : ℝ) - 1)) →
    (∀ p ∈ Pe, C * (k / m) * Real.log p ≤ (p : ℝ) - 1) →
    T * DF ≤ C * (k / m) * (∑ τ, ua τ) + T * PPd → Pe.card ≤ 2 →

    (∀ p ∈ Pf, 2 ≤ p) → (∀ p ∈ Pf, eloc p ≤ C * u1 / ((p : ℝ) - 1)) → Pf.card ≤ 4 →

    1 ≤ b → 1 ≤ rd → 0 ≤ Lchi → 1 ≤ Real.log x → 1 ≤ llx →
    LL0 = Real.log (b * rd) * llx + Lchi + Real.log x →
    T * (∑ p ∈ P, eloc p * Real.log p) ≤
      12 * C ^ 3 * LL0 * (∑ τ, ua τ) + (10 * C ^ 3 * LL0 * primePairSetFirst + T * (PPc + 2 * PPd))
def SumTotalAdd : Prop :=
  ∀ (P Bd : Finset ℕ) (e eloc ad : ℕ → ℝ) (T B PPa : ℝ), 0 ≤ T →
    (∀ p ∈ Bd, 0 ≤ ad p) →
    (∀ p ∈ P, e p ≤ eloc p + (if p ∈ Bd then ad p else 0)) →
    T * (∑ p ∈ P, eloc p * Real.log p) ≤ B →
    (∑ p ∈ Bd, ad p * Real.log p) ≤ PPa →
    T * (∑ p ∈ P, e p * Real.log p) ≤ B + T * PPa
def SumUnits : Prop :=
  ∀ (Bd : Finset ℕ) (ad kp : ℕ → ℝ) (CL K : ℝ), Bd.card ≤ 7 → 0 ≤ CL →
    (∀ p ∈ Bd, ad p ≤ kp p + 3) → (∀ p ∈ Bd, Real.log p ≤ CL) →
    (∑ p ∈ Bd, kp p * Real.log p) ≤ K →
    (∑ p ∈ Bd, ad p * Real.log p) ≤ K + 21 * CL
def SumTotalUnits : Prop :=
  ∀ (Pl : Type) [Fintype Pl] (ua : Pl → ℝ) (P Pab Pc Pe Pf Bd : Finset ℕ) (Φ : Type) [Fintype Φ]
    (e eloc ad : ℕ → ℝ) (c i : Φ → ℝ)
    (T u1 primePairSetFirst PPc PPd PPa C m j' k N sm y0 DF s n x b rd Lchi llx LL0 : ℝ),
    P ⊆ Pab ∪ Pc ∪ {2} ∪ Pe ∪ Pf → (∀ p, 0 ≤ eloc p) →
    1 ≤ C → 0 ≤ T → 0 ≤ u1 → 0 ≤ primePairSetFirst → 0 ≤ PPd → 0 ≤ (∑ τ, ua τ) → T * u1 ≤ (∑ τ, ua τ) + primePairSetFirst →

    (∀ p ∈ Pab, 2 ≤ p) → (∀ p ∈ Pab, eloc p ≤ C * u1 / ((p : ℝ) - 1)) →
    (∑ p ∈ Pab, Real.log p / ((p : ℝ) - 1)) ≤ C * Real.log DF → Real.log DF ≤ C * Real.log b →

    (∀ p ∈ Pc, 3 ≤ p ∧ (p : ℝ) < y0) →
    (∀ φ, 1 ≤ c φ ∧ c φ ≤ b) → (∀ φ, 0 ≤ i φ ∧ i φ ≤ N) → 0 ≤ j' → j' ≤ m → 0 ≤ sm →
    (∀ p ∈ Pc, eloc p ≤ (∑ φ, (c φ * m * p / ((p : ℝ) ^ 2 - 1)
        + c φ * j' * (3 + (1 / 2) * Real.logb p (c φ)) / ((p : ℝ) - 1)
        + (i φ) ^ 2 * (Real.logb p (c φ) + 1))) + sm / ((p : ℝ) - 1)) →
    (∑ p ∈ Pc, Real.log p / ((p : ℝ) - 1)) ≤ C * Real.log y0 →
    (∑ p ∈ Pc, 1 / ((p : ℝ) - 1)) ≤ Real.log (Real.log y0) + 1 →
    Real.log y0 ≤ C * Real.log x → Real.log (Real.log y0) + 1 ≤ C * llx →
    m * (∑ φ, c φ) ≤ C * u1 → sm ≤ C * u1 →
    (Fintype.card Φ : ℝ) * N ^ 2 * (Pc.card : ℝ) * (Real.log b + Real.log y0) ≤ PPc →

    eloc 2 ≤ C * (s + 2) * u1 → s ≤ Real.logb 2 (4 * n) → 1 ≤ n → Real.log (16 * n) ≤ C * Real.log x →

    (∀ p ∈ Pe, 2 ≤ p) → (∀ p ∈ Pe, eloc p ≤ DF / ((p : ℝ) - 1)) →
    (∀ p ∈ Pe, C * (k / m) * Real.log p ≤ (p : ℝ) - 1) →
    T * DF ≤ C * (k / m) * (∑ τ, ua τ) + T * PPd → Pe.card ≤ 2 →

    (∀ p ∈ Pf, 2 ≤ p) → (∀ p ∈ Pf, eloc p ≤ C * u1 / ((p : ℝ) - 1)) → Pf.card ≤ 4 →

    1 ≤ b → 1 ≤ rd → 0 ≤ Lchi → 1 ≤ Real.log x → 1 ≤ llx →
    LL0 = Real.log (b * rd) * llx + Lchi + Real.log x →

    (∀ p ∈ Bd, 0 ≤ ad p) → (∀ p ∈ P, e p ≤ eloc p + (if p ∈ Bd then ad p else 0)) →
    (∑ p ∈ Bd, ad p * Real.log p) ≤ PPa →
    T * (∑ p ∈ P, e p * Real.log p) ≤
      12 * C ^ 3 * LL0 * (∑ τ, ua τ) + (10 * C ^ 3 * LL0 * primePairSetFirst + T * (PPc + 2 * PPd + PPa))
def DepthRadius : Prop :=
  ∀ p : ℝ, 1 < p → 1 / (p - 1) - 1 / (p ^ 2 - 1) = p / (p ^ 2 - 1)
def DepthBadCount : Prop :=
  ∀ (p c : ℕ) (j' : ℝ), 2 ≤ p → 1 ≤ c → 0 ≤ j' →
    (((Finset.range c).filter (fun R => p ^ (2 * R + 1) ≤ c)).card : ℝ) ≤ (Real.logb p c + 1) / 2 ∧
    (∀ R : ℕ, p ^ (2 * R + 1) ≤ c → R ∈ Finset.range c) ∧
    j' * (1 + (((Finset.range c).filter (fun R => p ^ (2 * R + 1) ≤ c)).card : ℝ))
      ≤ j' * (3 / 2 + (1 / 2) * Real.logb p c)
def DepthGap : Prop :=
  ∀ (p c i j' N k m cr nuEta nuY : ℝ), 1 < p → 1 ≤ c → 0 ≤ j' →
    i * c * p / (p ^ 2 - 1) - c * cr * p / (p ^ 2 - 1) - i ^ 2 * (Real.logb p c + 1) ≤ nuEta →
    cr ≤ j' * (3 / 2 + (1 / 2) * Real.logb p c) →
    nuY ≤ c * (j' / (p - 1) + (N - 2 * j') * p / (p ^ 2 - 1)) →
    (nuY - nuEta ≤ c * (N - 2 * j' - i) * p / (p ^ 2 - 1)
        + c * j' * (3 + (1 / 2) * Real.logb p c) / (p - 1) + i ^ 2 * (Real.logb p c + 1)) ∧
    (i * c * p / (p ^ 2 - 1) - c * j' * (2 + (1 / 2) * Real.logb p c) / (p - 1)
        - i ^ 2 * (Real.logb p c + 1) ≤ nuEta) ∧
    (k - 1 ≤ i → N = k + m - 1 →
      c * (N - 2 * j' - i) * p / (p ^ 2 - 1) ≤ c * m * p / (p ^ 2 - 1))
end Formalism.ExtensionFiltration


