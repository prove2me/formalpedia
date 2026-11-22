-- Prove2me | Definitions.Def_Formalism_DivisorInequality_StatementObj
-- name    : Formalism_DivisorInequality_StatementObj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:45.264375+00:00
-- url     : https://prove2.me/theorems/5dc4b236-f09b-4ffd-9e3a-8877c83447fd
-- title:
--   Statement Obj
-- statement:
--   Definitions and structural lemmas for Statement Obj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DivisorInequality/StatementObj.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_StatementK
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.DivisorInequality
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.LatticeIndexTer (ph)
def BoundsMu : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (D : ℕ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), 0 < D → (∀ v, IsUnit (XE v).det) →
    ∀ (Tup : Type) (μ0 : Tup) (μ : HeightOneSpectrum (𝓞 K) → Tup), (∀ y, μ (conjPl y) = μ y) →
    {y | μ y ≠ μ0}.Finite →
    ∀ (XQ : Tup → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ t v, IsUnit (XQ t v).det) →
    ∀ (abelian₂ : Tup → Submodule (𝓞 K) (Fin D → K)), (∀ t, Submodule.IsLattice K (abelian₂ t)) →
    ∀ (ι : Tup → Matrix (Fin D) (Fin D) K), (∀ t, IsUnit (ι t).det) →
    ∀ (J : Type) [Fintype J]
      (XW : J → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ j v, IsUnit (XW j v).det) →
    ∀ (M : J → Submodule (𝓞 K) (Fin D → K)), (∀ j, Submodule.IsLattice K (M j)) →
    ∀ (HT : J → Tup → Matrix (Fin D) (Fin D) K)
      (XT : J → Tup → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ),
      (∀ j, IsRatHerm K0 (HT j μ0) (XT j μ0)) → (∀ j t, IsHermAt v0 (HT j t) (XT j t)) →
    ∀ (Tl : J → Tup → Submodule (𝓞 K) (Fin D → K)), (∀ j t, Submodule.IsLattice K (Tl j t)) →
    ∀ (θ : J → Tup → Matrix (Fin D) (Fin D) K), (∀ j t, IsUnit (θ j t).det) →
    ∀ (κ : InfinitePlace K → ℝ), (∀ v, 0 < κ v) →
    ∀ (ρt : Tup → K) (ρr : Tup → ℝ), (∀ t, v0.embedding (ρt t) = (ρr t : ℂ)) → ρt μ0 = 1 →
    (∀ t, 0 < ρr t) → (∀ y, vw y (ρt (μ y)) = 0) →
    (∀ v, detRatio (XQ μ0) XE (ι μ0) v = κ v ^ D * ∏ j, detRatio (XT j μ0) (XW j) (θ j μ0) v) →
    (∀ t, detRatio (XQ t) XE (ι t) v0 =
      (κ v0 * ρr t) ^ D * ∏ j, detRatio (XT j t) (XW j) (θ j t) v0) →
    ∀ (Gm : Tup → HeightOneSpectrum (𝓞 K) → K)
      (eb : Tup → HeightOneSpectrum (𝓞 K) → Fin D → Fin D → K),
    (∀ t y, IsLocBasis (abelian₂ t) y (eb t y)) →
    (∀ t y, v0.embedding (Gm t y) = (gram (XQ t) v0 (eb t y)).det) →
    ∀ (nH : ℕ) (Hm : Matrix (Fin nH) (Fin nH) K), (∀ i j, Hm i j ∈ K0) →
    (∀ v : InfinitePlace K, (Hm.map v.embedding).PosDef) →
    ∀ Pm : Matrix (Fin D) (Fin nH) K, Function.Surjective Pm.mulVec → IsQuotMetric Pm Hm (XQ μ0) →
    ∀ Mt : Submodule (𝓞 K) (Fin nH → K), Submodule.IsLattice K Mt → abelian₂ μ0 = matLat Pm Mt →
    (∀ y, Gm μ0 y = gramR (quotGram Pm Hm) (eb μ0 y)) →
    ∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsLattice K R →
    (∀ y, Formalism.HermitianLatticesTheory.localization₂ y.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ y.asIdeal (matLat (ι (μ y)) (abelian₂ (μ y)))) →

    ∀ (Sy Tw : Finset (HeightOneSpectrum (𝓞 K))), Tw ⊆ Sy →
    (∀ y ∉ Sy, lw y * ((vw y (Gm (μ y) y) : ℝ) + ∑ j, ((idx y (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) +
      (idx (conjPl y) (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) + (jw (HT j (μ y)) y (Tl j (μ y)) : ℝ))) = 0) →
    (∀ y ∈ Sy, y ∉ Tw → ∀ j, (idx y (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) +
      (idx (conjPl y) (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) + (jw (HT j (μ y)) y (Tl j (μ y)) : ℝ) = 0) →
    ∀ (LG E3 : ℝ) (E1 E2 : J → ℝ) (elly gy : HeightOneSpectrum (𝓞 K) → ℝ)
      (Fy erry Jy ηy : HeightOneSpectrum (𝓞 K) → J → ℝ),
    (∀ y ∈ Sy, y ∉ Tw → ∀ j, Fy y j = 0) →

    (∀ y ∈ Sy, (vw y (Gm (μ y) y) : ℝ) ≤ (D : ℝ) * gy y) → ∑ y ∈ Sy, lw y * gy y ≤ LG →

    (∀ y ∈ Tw, ∑ j, ((idx y (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) +
        (idx (conjPl y) (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ)) ≤
      (∑ j, (2 * Fy y j + erry y j) + 2 / elly y ^ 2) * D) →

    (∀ y ∈ Tw, ∀ j, (jw (HT j (μ y)) y (Tl j (μ y)) : ℝ) ≤ Jy y j * D + ηy y j) →

    (∀ j, ∑ y ∈ Tw, lw y * (erry y j + Jy y j) ≤ E1 j) →
    (∀ j, ∑ y ∈ Tw, lw y * ηy y j / D ≤ E2 j) →
    ∑ y ∈ Sy, lw y * (2 / elly y ^ 2) ≤ E3 →
      Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat R) ≤
        meanLog κ + (∑ j, lcv (XW j) (M j) / D) + 2 * (∑ j, ∑ y ∈ Tw, lw y * Fy y j) + LG +
          (∑ j, (E1 j + E2 j)) + E3 ∧
      ∀ j, lcv (XW j) (M j) / D = -Formalism.HN.muDef (Pi.basisFun K (Fin D)) (XW j) (M j)
def BaseLevelBoundsWithCovolume : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (D : ℕ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), 0 < D → (∀ v, IsUnit (XE v).det) →
    ∀ (Tup : Type) (μ0 : Tup) (μ : HeightOneSpectrum (𝓞 K) → Tup), (∀ y, μ (conjPl y) = μ y) →
    {y | μ y ≠ μ0}.Finite →
    ∀ (XQ : Tup → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ t v, IsUnit (XQ t v).det) →
    ∀ (abelian₂ : Tup → Submodule (𝓞 K) (Fin D → K)), (∀ t, Submodule.IsLattice K (abelian₂ t)) →
    ∀ (ι : Tup → Matrix (Fin D) (Fin D) K), (∀ t, IsUnit (ι t).det) →
    ∀ (J : Type) [Fintype J]
      (XW : J → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ j v, IsUnit (XW j v).det) →
    ∀ (M : J → Submodule (𝓞 K) (Fin D → K)), (∀ j, Submodule.IsLattice K (M j)) →
    ∀ (HT : J → Tup → Matrix (Fin D) (Fin D) K)
      (XT : J → Tup → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ),
      (∀ j, IsRatHerm K0 (HT j μ0) (XT j μ0)) → (∀ j t, IsHermAt v0 (HT j t) (XT j t)) →
    ∀ (Tl : J → Tup → Submodule (𝓞 K) (Fin D → K)), (∀ j t, Submodule.IsLattice K (Tl j t)) →
    ∀ (θ : J → Tup → Matrix (Fin D) (Fin D) K), (∀ j t, IsUnit (θ j t).det) →
    ∀ (κ : InfinitePlace K → ℝ), (∀ v, 0 < κ v) →
    ∀ (ρt : Tup → K) (ρr : Tup → ℝ), (∀ t, v0.embedding (ρt t) = (ρr t : ℂ)) → ρt μ0 = 1 →
    (∀ t, 0 < ρr t) → (∀ y, vw y (ρt (μ y)) = 0) →
    (∀ v, detRatio (XQ μ0) XE (ι μ0) v = κ v ^ D * ∏ j, detRatio (XT j μ0) (XW j) (θ j μ0) v) →
    (∀ t, detRatio (XQ t) XE (ι t) v0 =
      (κ v0 * ρr t) ^ D * ∏ j, detRatio (XT j t) (XW j) (θ j t) v0) →
    ∀ (Gm : Tup → HeightOneSpectrum (𝓞 K) → K)
      (eb : Tup → HeightOneSpectrum (𝓞 K) → Fin D → Fin D → K),
    (∀ t y, IsLocBasis (abelian₂ t) y (eb t y)) →
    (∀ t y, v0.embedding (Gm t y) = (gram (XQ t) v0 (eb t y)).det) →
    ∀ (nH : ℕ) (Hm : Matrix (Fin nH) (Fin nH) K), (∀ i j, Hm i j ∈ K0) →
    (∀ v : InfinitePlace K, (Hm.map v.embedding).PosDef) →
    ∀ Pm : Matrix (Fin D) (Fin nH) K, Function.Surjective Pm.mulVec → IsQuotMetric Pm Hm (XQ μ0) →
    ∀ Mt : Submodule (𝓞 K) (Fin nH → K), Submodule.IsLattice K Mt → abelian₂ μ0 = matLat Pm Mt →
    (∀ y, Gm μ0 y = gramR (quotGram Pm Hm) (eb μ0 y)) →
    ∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsLattice K R →
    (∀ y, Formalism.HermitianLatticesTheory.localization₂ y.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ y.asIdeal (matLat (ι (μ y)) (abelian₂ (μ y)))) →

    ∀ (Sy Tw : Finset (HeightOneSpectrum (𝓞 K))), Tw ⊆ Sy →
    (∀ y ∉ Sy, lw y * ((vw y (Gm (μ y) y) : ℝ) + ∑ j, ((idx y (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) +
      (idx (conjPl y) (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) + (jw (HT j (μ y)) y (Tl j (μ y)) : ℝ))) = 0) →
    (∀ y ∈ Sy, y ∉ Tw → ∀ j, (idx y (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) +
      (idx (conjPl y) (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) + (jw (HT j (μ y)) y (Tl j (μ y)) : ℝ) = 0) →
    ∀ (LG E3 : ℝ) (E1 E2 : J → ℝ) (elly gy : HeightOneSpectrum (𝓞 K) → ℝ)
      (Fy erry Jy ηy : HeightOneSpectrum (𝓞 K) → J → ℝ),
    (∀ y ∈ Sy, y ∉ Tw → ∀ j, Fy y j = 0) →

    (∀ y ∈ Sy, (vw y (Gm (μ y) y) : ℝ) ≤ (D : ℝ) * gy y) → ∑ y ∈ Sy, lw y * gy y ≤ LG →

    (∀ y ∈ Tw, ∑ j, ((idx y (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) +
        (idx (conjPl y) (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ)) ≤
      (∑ j, (2 * Fy y j + erry y j) + 2 / elly y ^ 2) * D) →

    (∀ y ∈ Tw, ∀ j, (jw (HT j (μ y)) y (Tl j (μ y)) : ℝ) ≤ Jy y j * D + ηy y j) →

    (∀ j, ∑ y ∈ Tw, lw y * (erry y j + Jy y j) ≤ E1 j) →
    (∀ j, ∑ y ∈ Tw, lw y * ηy y j / D ≤ E2 j) →
    ∑ y ∈ Sy, lw y * (2 / elly y ^ 2) ≤ E3 →
    ∀ (Pl : Type) [Fintype Pl] (pq : J → ℝ) (w : J → Pl → ℝ)
      (logOm x eps L b rd B0 f m k S η : ℝ)

    (q' : J → ℝ) (c1 ua : J → Pl → ℝ)
    (muU muA muN muG mmax dA dB dN dgd dbd cfl εd δd Qd Pd Λd Gd P9 : J → ℝ)
    (C1 Cf Cc Lchi llx LL0 : ℝ),

    (∀ j, -(2 * (C1 * LL0 * (∑ τ, ua j τ) + b / 4)) ≤ muU j) →
    (∀ j, cfl j =
      (∑ τ, w j τ * c1 j τ) - Cf * q' j * Real.log rd * (∑ τ, w j τ) - Cf * L) →
    (∀ j, muU j + 2 * cfl j ≤ muA j) →
    (∀ j, 0 < dA j ∧ dA j ≤ dB j ∧ (1 - εd j) * dB j ≤ dA j ∧ 0 ≤ εd j ∧ 0 ≤ Pd j) →
    (∀ j, dA j * (muA j - Pd j) + (dB j - dA j) * (-Λd j) ≤ dB j * muN j) →
    (∀ j, |2 * cfl j| ≤ Qd j ∧ Λd j ≤ Qd j ∧ εd j * Qd j ≤ b / 4) →
    (∀ j, 0 < dN j ∧ dN j = dgd j + dbd j ∧ 0 ≤ dbd j ∧ dbd j ≤ 3 * δd j * dN j ∧ 0 ≤ δd j ∧
      δd j ≤ 1 / 12) →
    (∀ j, dN j * muN j ≤ dgd j * muG j + dbd j * (mmax j + Gd j)) →
    (∀ j, |muN j| ≤ Qd j ∧ mmax j ≤ Qd j ∧ Gd j ≤ Qd j) →
    (∀ j, muG j - P9 j ≤ Formalism.HN.muDef (Pi.basisFun K (Fin D)) (XW j) (M j)) →
    (∀ j, Pd j + 12 * δd j * Qd j + P9 j ≤ b) →
    (∀ j τ, |c1 j τ + pq j * logOm / 2| ≤ Cc * q' j * (Real.log rd + Lchi)) →
    (∀ j τ, m * w j τ / 2 ≤ ua j τ ∧ ua j τ ≤ 2 * (m * w j τ + k * S + k * η)) →
    (∀ j, 1 ≤ ∑ τ, ua j τ) → (∀ j, 0 ≤ q' j ∧ q' j ≤ m) →
    0 ≤ Lchi → Lchi ≤ L → 1 ≤ llx →
    LL0 = Real.log (b * rd) * llx + Lchi + Real.log x →
    0 ≤ C1 → 0 ≤ Cf → 0 ≤ Cc →

    (∀ j ρ, 0 ≤ w j ρ ∧ w j ρ ≤ 2 * b) → k * S ≤ b → k * η ≤ b →
    (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f →
    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → 1 ≤ rd → Real.log rd ≤ L → Real.log x ≤ L →
    B0 = f * m * b * x ^ eps →
      (∀ j, lcv (XW j) (M j) / D ≤
        (∑ ρ, pq j * w j ρ * logOm) + (64 * (C1 + 3 * Cf) + 8 * Cc + 2) * B0 * llx) ∧
      Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat R) ≤
        meanLog κ + (∑ j, ∑ ρ, pq j * w j ρ * logOm) + 2 * (∑ j, ∑ y ∈ Tw, lw y * Fy y j) +
          ((Fintype.card J : ℝ) * ((64 * (C1 + 3 * Cf) + 8 * Cc + 2) * B0 * llx) + LG +
            (∑ j, (E1 j + E2 j)) + E3)
def BoundsMuOn : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (D : ℕ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), 0 < D → (∀ v, IsUnit (XE v).det) →
    ∀ (Tup : Type) (μ0 : Tup) (μ : HeightOneSpectrum (𝓞 K) → Tup), (∀ y, μ (conjPl y) = μ y) →
    {y | μ y ≠ μ0}.Finite →
    ∀ (XQ : Tup → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ t v, IsUnit (XQ t v).det) →
    ∀ (abelian₂ : Tup → Submodule (𝓞 K) (Fin D → K)), (∀ t, Submodule.IsLattice K (abelian₂ t)) →
    ∀ (ι : Tup → Matrix (Fin D) (Fin D) K), (∀ t, IsUnit (ι t).det) →
    ∀ (J : Type) [Fintype J]
      (XW : J → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ j v, IsUnit (XW j v).det) →
    ∀ (M : J → Submodule (𝓞 K) (Fin D → K)), (∀ j, Submodule.IsLattice K (M j)) →
    ∀ (HT : J → Tup → Matrix (Fin D) (Fin D) K)
      (XT : J → Tup → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ),
      (∀ j, IsRatHerm K0 (HT j μ0) (XT j μ0)) → (∀ j t, IsHermAt v0 (HT j t) (XT j t)) →
    ∀ (Tl : J → Tup → Submodule (𝓞 K) (Fin D → K)), (∀ j t, Submodule.IsLattice K (Tl j t)) →
    ∀ (θ : J → Tup → Matrix (Fin D) (Fin D) K), (∀ j t, IsUnit (θ j t).det) →
    ∀ (κ : InfinitePlace K → ℝ), (∀ v, 0 < κ v) →
    ∀ (ρt : Tup → K) (ρr : Tup → ℝ), (∀ t, v0.embedding (ρt t) = (ρr t : ℂ)) → ρt μ0 = 1 →
    (∀ t, 0 < ρr t) → (∀ y, vw y (ρt (μ y)) = 0) →
    (∀ v, detRatio (XQ μ0) XE (ι μ0) v = κ v ^ D * ∏ j, detRatio (XT j μ0) (XW j) (θ j μ0) v) →
    (∀ t, detRatio (XQ t) XE (ι t) v0 =
      (κ v0 * ρr t) ^ D * ∏ j, detRatio (XT j t) (XW j) (θ j t) v0) →
    ∀ (Gm : Tup → HeightOneSpectrum (𝓞 K) → K)
      (eb : Tup → HeightOneSpectrum (𝓞 K) → Fin D → Fin D → K),
    (∀ t y, IsLocBasis (abelian₂ t) y (eb t y)) →
    (∀ t y, v0.embedding (Gm t y) = (gram (XQ t) v0 (eb t y)).det) →
    ∀ (nH : ℕ) (Hm : Matrix (Fin nH) (Fin nH) K), (∀ i j, Hm i j ∈ K0) →
    (∀ v : InfinitePlace K, (Hm.map v.embedding).PosDef) →
    ∀ Pm : Matrix (Fin D) (Fin nH) K, Function.Surjective Pm.mulVec → IsQuotMetric Pm Hm (XQ μ0) →
    ∀ Mt : Submodule (𝓞 K) (Fin nH → K), Submodule.IsLattice K Mt → abelian₂ μ0 = matLat Pm Mt →
    (∀ y, Gm μ0 y = gramR (quotGram Pm Hm) (eb μ0 y)) →
    ∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsLattice K R →
    (∀ y, Formalism.HermitianLatticesTheory.localization₂ y.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ y.asIdeal (matLat (ι (μ y)) (abelian₂ (μ y)))) →

    ∀ (Sy Tw : Finset (HeightOneSpectrum (𝓞 K))), Tw ⊆ Sy →
    (∀ y ∉ Sy, lw y * ((vw y (Gm (μ y) y) : ℝ) + ∑ j, ((idx y (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) +
      (idx (conjPl y) (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) + (jw (HT j (μ y)) y (Tl j (μ y)) : ℝ))) = 0) →
    (∀ y ∈ Sy, y ∉ Tw → ∀ j, (idx y (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) +
      (idx (conjPl y) (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) + (jw (HT j (μ y)) y (Tl j (μ y)) : ℝ) = 0) →
    ∀ (LG : ℝ) (E2 : J → ℝ) (gy : HeightOneSpectrum (𝓞 K) → ℝ) (Jy ηy : HeightOneSpectrum (𝓞 K) → J → ℝ)
      (e0 r0 ε0 F0 errl : HeightOneSpectrum (𝓞 K) → J → ℝ) (vU0 gq : HeightOneSpectrum (𝓞 K) → ℝ)
      (dK EA Rb EJ : J → ℝ) (δq : ℝ),
    (∀ y ∈ Sy, y ∉ Tw → ∀ j, F0 y j = 0) →

    (∀ y ∈ Sy, (vw y (Gm (μ y) y) : ℝ) ≤ (D : ℝ) * gy y) → ∑ y ∈ Sy, lw y * gy y ≤ LG →

    0 < δq →
    (∀ y ∈ Tw, ∀ j, (idx y (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) ≤
      (ramw y : ℝ) * ((e0 y j + vU0 y) * (D : ℝ) + (r0 y j + dK j * vU0 y) / δq + ε0 y j)) →
    (∀ y ∈ Tw, ∀ j, (idx (conjPl y) (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) ≤
      (ramw (conjPl y) : ℝ) * ((e0 (conjPl y) j + vU0 (conjPl y)) * (D : ℝ) +
        (r0 (conjPl y) j + dK j * vU0 (conjPl y)) / δq + ε0 (conjPl y) j)) →
    (∀ j, dK j / δq ≤ 3 * (D : ℝ)) →
    (∀ y ∈ Tw, 0 ≤ vU0 y ∧ vU0 (conjPl y) = vU0 y ∧ 4 * vU0 y ≤ gq y) →
    (∀ y ∈ Tw, ∀ j, e0 y j + e0 (conjPl y) j - 2 * F0 y j + 2 * gq y ≤ errl y j) →
    (∀ y ∈ Tw, ∑ j, (ε0 y j + ε0 (conjPl y) j) ≤ 2 / (plc y : ℝ) ^ 2) →
    (∀ j, ∑ y ∈ Tw, lw y * ((ramw y : ℝ) * errl y j) ≤ EA j) →
    (∀ j, ∀ S' : Finset (HeightOneSpectrum (𝓞 K)), ∑ y ∈ S', lw y * ((ramw y : ℝ) * r0 y j) ≤ Rb j) →
    (∀ j, ∑ y ∈ Tw, lw y * Jy y j ≤ EJ j) →

    (∀ y ∈ Tw, ∀ j, (jw (HT j (μ y)) y (Tl j (μ y)) : ℝ) ≤ Jy y j * D + ηy y j) →
    (∀ j, ∑ y ∈ Tw, lw y * ηy y j / D ≤ E2 j) →
      Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat R) ≤
        meanLog κ + (∑ j, lcv (XW j) (M j) / D) +
          2 * (∑ j, ∑ y ∈ Tw, lw y * ((ramw y : ℝ) * F0 y j)) + LG +
          (∑ j, ((EA j + 2 * Rb j / (δq * (D : ℝ)) + EJ j) + E2 j)) + 1 ∧
      ∀ j, lcv (XW j) (M j) / D = -Formalism.HN.muDef (Pi.basisFun K (Fin D)) (XW j) (M j)
def DivIneqObj : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (D : ℕ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), 0 < D → (∀ v, IsUnit (XE v).det) →
    ∀ (Tup : Type) (μ0 : Tup) (μ : HeightOneSpectrum (𝓞 K) → Tup), (∀ y, μ (conjPl y) = μ y) →
    {y | μ y ≠ μ0}.Finite →
    ∀ (XQ : Tup → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ t v, IsUnit (XQ t v).det) →
    ∀ (abelian₂ : Tup → Submodule (𝓞 K) (Fin D → K)), (∀ t, Submodule.IsLattice K (abelian₂ t)) →
    ∀ (ι : Tup → Matrix (Fin D) (Fin D) K), (∀ t, IsUnit (ι t).det) →
    ∀ (J : Type) [Fintype J]
      (XW : J → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ j v, IsUnit (XW j v).det) →
    ∀ (M : J → Submodule (𝓞 K) (Fin D → K)), (∀ j, Submodule.IsLattice K (M j)) →
    ∀ (HT : J → Tup → Matrix (Fin D) (Fin D) K)
      (XT : J → Tup → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ),
      (∀ j, IsRatHerm K0 (HT j μ0) (XT j μ0)) → (∀ j t, IsHermAt v0 (HT j t) (XT j t)) →
    ∀ (Tl : J → Tup → Submodule (𝓞 K) (Fin D → K)), (∀ j t, Submodule.IsLattice K (Tl j t)) →
    ∀ (θ : J → Tup → Matrix (Fin D) (Fin D) K), (∀ j t, IsUnit (θ j t).det) →
    ∀ (κ : InfinitePlace K → ℝ), (∀ v, 0 < κ v) →
    ∀ (ρt : Tup → K) (ρr : Tup → ℝ), (∀ t, v0.embedding (ρt t) = (ρr t : ℂ)) → ρt μ0 = 1 →
    (∀ t, 0 < ρr t) → (∀ y, vw y (ρt (μ y)) = 0) →
    (∀ v, detRatio (XQ μ0) XE (ι μ0) v = κ v ^ D * ∏ j, detRatio (XT j μ0) (XW j) (θ j μ0) v) →
    (∀ t, detRatio (XQ t) XE (ι t) v0 =
      (κ v0 * ρr t) ^ D * ∏ j, detRatio (XT j t) (XW j) (θ j t) v0) →
    ∀ (Gm : Tup → HeightOneSpectrum (𝓞 K) → K)
      (eb : Tup → HeightOneSpectrum (𝓞 K) → Fin D → Fin D → K),
    (∀ t y, IsLocBasis (abelian₂ t) y (eb t y)) →
    (∀ t y, v0.embedding (Gm t y) = (gram (XQ t) v0 (eb t y)).det) →
    ∀ (nH : ℕ) (Hm : Matrix (Fin nH) (Fin nH) K), (∀ i j, Hm i j ∈ K0) →
    (∀ v : InfinitePlace K, (Hm.map v.embedding).PosDef) →
    ∀ Pm : Matrix (Fin D) (Fin nH) K, Function.Surjective Pm.mulVec → IsQuotMetric Pm Hm (XQ μ0) →
    ∀ Mt : Submodule (𝓞 K) (Fin nH → K), Submodule.IsLattice K Mt → abelian₂ μ0 = matLat Pm Mt →
    (∀ y, Gm μ0 y = gramR (quotGram Pm Hm) (eb μ0 y)) →
    ∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsLattice K R →
    (∀ y, Formalism.HermitianLatticesTheory.localization₂ y.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ y.asIdeal (matLat (ι (μ y)) (abelian₂ (μ y)))) →

    ∀ (Sy Tw : Finset (HeightOneSpectrum (𝓞 K))), Tw ⊆ Sy →
    (∀ y ∉ Sy, lw y * ((vw y (Gm (μ y) y) : ℝ) + ∑ j, ((idx y (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) +
      (idx (conjPl y) (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) + (jw (HT j (μ y)) y (Tl j (μ y)) : ℝ))) = 0) →
    (∀ y ∈ Sy, y ∉ Tw → ∀ j, (idx y (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) +
      (idx (conjPl y) (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) + (jw (HT j (μ y)) y (Tl j (μ y)) : ℝ) = 0) →
    ∀ (LG : ℝ) (E2 : J → ℝ) (gy : HeightOneSpectrum (𝓞 K) → ℝ) (Jy ηy : HeightOneSpectrum (𝓞 K) → J → ℝ)
      (e0 r0 ε0 F0 errl : HeightOneSpectrum (𝓞 K) → J → ℝ) (vU0 gq : HeightOneSpectrum (𝓞 K) → ℝ)
      (dK EA Rb EJ : J → ℝ) (δq : ℝ),
    (∀ y ∈ Sy, y ∉ Tw → ∀ j, F0 y j = 0) →

    (∀ y ∈ Sy, (vw y (Gm (μ y) y) : ℝ) ≤ (D : ℝ) * gy y) → ∑ y ∈ Sy, lw y * gy y ≤ LG →

    0 < δq →
    (∀ y ∈ Tw, ∀ j, (idx y (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) ≤
      (ramw y : ℝ) * ((e0 y j + vU0 y) * (D : ℝ) + (r0 y j + dK j * vU0 y) / δq + ε0 y j)) →
    (∀ y ∈ Tw, ∀ j, (idx (conjPl y) (M j) (matLat (θ j (μ y)) (Tl j (μ y))) : ℝ) ≤
      (ramw (conjPl y) : ℝ) * ((e0 (conjPl y) j + vU0 (conjPl y)) * (D : ℝ) +
        (r0 (conjPl y) j + dK j * vU0 (conjPl y)) / δq + ε0 (conjPl y) j)) →
    (∀ j, dK j / δq ≤ 3 * (D : ℝ)) →
    (∀ y ∈ Tw, 0 ≤ vU0 y ∧ vU0 (conjPl y) = vU0 y ∧ 4 * vU0 y ≤ gq y) →
    (∀ y ∈ Tw, ∀ j, e0 y j + e0 (conjPl y) j - 2 * F0 y j + 2 * gq y ≤ errl y j) →
    (∀ y ∈ Tw, ∑ j, (ε0 y j + ε0 (conjPl y) j) ≤ 2 / (plc y : ℝ) ^ 2) →
    (∀ j, ∑ y ∈ Tw, lw y * ((ramw y : ℝ) * errl y j) ≤ EA j) →
    (∀ j, ∀ S' : Finset (HeightOneSpectrum (𝓞 K)), ∑ y ∈ S', lw y * ((ramw y : ℝ) * r0 y j) ≤ Rb j) →
    (∀ j, ∑ y ∈ Tw, lw y * Jy y j ≤ EJ j) →

    (∀ y ∈ Tw, ∀ j, (jw (HT j (μ y)) y (Tl j (μ y)) : ℝ) ≤ Jy y j * D + ηy y j) →
    (∀ j, ∑ y ∈ Tw, lw y * ηy y j / D ≤ E2 j) →
    ∀ (Pl Emb Sg : Type) [Fintype Pl] [Fintype Emb] [Nonempty Emb] [Fintype Sg]
    (TT : Finset Pl) [DecidablePred (· ∈ TT)] (nr : ℕ)

    (muC mu0 Fo hu hP mlam logT logκ : ℝ) (hK : J → ℝ) (aT : Pl → ℝ) (fa : J → Pl → ℝ)

    (ν : J → Pl → Fin nr → ℝ)

    (x eps L b a rd La B0 Nc xe m f k N S tt η w'' b' lam0 C0 : ℝ)

    (e6 logOm : ℝ) (pq : J → ℝ) (w eE δ : J → Pl → ℝ)

    (g0 : J → ℝ) (logK MainNotions : J → Emb → ℝ) (logOmτ : Pl → Emb → ℝ) (logth0 : Emb → ℝ)
    (logh logh' : J → ℝ) (v logg C2 Cth C4 c5 c6 CT C8 : ℝ)

    (rk nS dg : Sg → ℝ) (nbar HH0 muP0 muPs r g p2 pF pN : ℝ)

    (ev : ℝ) (bT nτ lam1 D0 D1 logc logxi : Pl → ℝ) (Cev : ℝ)

    (q' : J → ℝ) (c1 ua : J → Pl → ℝ)
    (muU muA muN muG mmax dA dB dN dgd dbd cfl εd δd Qd Pd Λd Gd P9 : J → ℝ)
    (C1 Cf Cc Lchi llx LL0 : ℝ)

    (logDG Cb : ℝ),

    mu0 = Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat R) →
    logκ = meanLog κ →
    Fo = ∑ j, ∑ y ∈ Tw, lw y * ((ramw y : ℝ) * F0 y j) →

    0 < nbar → 0 ≤ lam0 → (∀ s, 0 ≤ rk s) → 0 < ∑ s, rk s → 0 ≤ r →
    (∀ s, (1 - 8 * f * r / g) * nbar ≤ nS s ∧ nS s ≤ (1 + 8 * f * r / g) * nbar) →
    |(-mu0) - muP0| ≤ lam0 → |(-muC) - muPs| ≤ lam0 →
    (∀ s, dg s ≤ rk s * (HH0 + lam0)) →
    (∑ s, nS s * dg s) - 17 / 2 * lam0 * (∑ s, nS s * rk s) ≤ muPs * (∑ s, nS s * rk s) →
    muP0 * (∑ s, rk s) ≤ (∑ s, dg s) + 2 * lam0 * (∑ s, rk s) →

    HH0 ≤ -logκ + p2 * b → Fo ≤ pF * b → Nc ≤ pN * b → (k * b) ^ 8 ≤ g →
    24 * f * r *
      ((2 * m * f * N * La + 2 * pF + C0 * m * xe * (f * m * xe + pN)) + p2 + 4) ≤ (k * b) ^ 7 →
    24 * f * r ≤ (k * b) ^ 8 →

    (∀ j, -(2 * (C1 * LL0 * (∑ τ, ua j τ) + b / 4)) ≤ muU j) →
    (∀ j, cfl j =
      (∑ τ, w j τ * c1 j τ) - Cf * q' j * Real.log rd * (∑ τ, w j τ) - Cf * L) →
    (∀ j, muU j + 2 * cfl j ≤ muA j) →
    (∀ j, 0 < dA j ∧ dA j ≤ dB j ∧ (1 - εd j) * dB j ≤ dA j ∧ 0 ≤ εd j ∧ 0 ≤ Pd j) →
    (∀ j, dA j * (muA j - Pd j) + (dB j - dA j) * (-Λd j) ≤ dB j * muN j) →
    (∀ j, |2 * cfl j| ≤ Qd j ∧ Λd j ≤ Qd j ∧ εd j * Qd j ≤ b / 4) →
    (∀ j, 0 < dN j ∧ dN j = dgd j + dbd j ∧ 0 ≤ dbd j ∧ dbd j ≤ 3 * δd j * dN j ∧ 0 ≤ δd j ∧
      δd j ≤ 1 / 12) →
    (∀ j, dN j * muN j ≤ dgd j * muG j + dbd j * (mmax j + Gd j)) →
    (∀ j, |muN j| ≤ Qd j ∧ mmax j ≤ Qd j ∧ Gd j ≤ Qd j) →
    (∀ j, muG j - P9 j ≤ Formalism.HN.muDef (Pi.basisFun K (Fin D)) (XW j) (M j)) →
    (∀ j, Pd j + 12 * δd j * Qd j + P9 j ≤ b) →
    (∀ j τ, |c1 j τ + pq j * logOm / 2| ≤ Cc * q' j * (Real.log rd + Lchi)) →
    (∀ j τ, m * w j τ / 2 ≤ ua j τ ∧ ua j τ ≤ 2 * (m * w j τ + k * S + k * η)) →
    (∀ j, 1 ≤ ∑ τ, ua j τ) → (∀ j, 0 ≤ q' j ∧ q' j ≤ m) →
    0 ≤ Lchi → Lchi ≤ L → 1 ≤ llx → llx ≤ xe →
    LL0 = Real.log (b * rd) * llx + Lchi + Real.log x →
    0 ≤ C1 → 0 ≤ Cf → 0 ≤ Cc →

    LG ≤ lam0 + logDG + Cb * f * N ^ 2 * logg →
    logDG ≤ Cb * f * N * Real.log (f * N) →
    (∀ j, (EA j + 2 * Rb j / (δq * (D : ℝ)) + EJ j) ≤ Cb * xe * (B0 + Nc) + logDG + Cb * f * N ^ 2 * logg) →
    (∀ j, E2 j ≤ Cb * xe * (B0 + Nc)) →
    0 ≤ Cb → N ^ 2 * logg ≤ b → N * Real.log (f * N) ≤ b →

    hu = hP + ∑ j, hK j - mlam - logκ →
    ∑ j, ∑ ρ, fa j ρ - e6 ≤ mlam →
    e6 ≤ C0 * m * f * N ^ 2 * La →

    (∀ j s, logK j s ≤
      (∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOmτ τ s)) +
      (Fintype.card Pl : ℝ) * g0 j * logth0 s +
      ((Fintype.card Pl : ℝ) * g0 j * Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) +
        2 * MainNotions j s + (∑ τ, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2))) +
        (logh j + logh' j))) →
    (∀ j, hK j = (∑ s, logK j s) / (Fintype.card Emb : ℝ)) →
    (∀ τ, (∑ s, logOmτ τ s) / (Fintype.card Emb : ℝ) = logOm) →
    (∀ j s, MainNotions j s ≤ C2 * f * m ^ 2 * N ^ 2 * (logg + logT)) →
    (∑ s, logth0 s) / (Fintype.card Emb : ℝ) ≤ Cth * L →
    (∀ j, logh j ≤ C4 * f * N ^ 2 * (L + logT + logg)) →
    (∀ j, logh' j ≤ C4 * f * N ^ 2 * (L + logT + logg)) →
    (∀ j, 0 ≤ g0 j ∧ g0 j ≤ N ^ 2) →
    (∀ j, Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) ≤ c5 * La) →
    (∀ j τ, Real.log (2 * (∑ i, ν j τ i) + 2) ≤ c6 * La) →
    logg ≤ C8 * L →
    0 ≤ C2 → 0 ≤ Cth → 0 ≤ C4 → 0 ≤ c5 → 0 ≤ c6 → 0 ≤ C8 →

    hP ≤ -(∑ τ, nτ τ * logT) + ∑ τ, (2 * logc τ + logxi τ) + ev →
    (∀ τ, logc τ ≤ (N - 1) * D1 τ * Real.log (2 * a)) →
    (∀ τ, logxi τ ≤ N * (N - 1) / 2 * Real.log (2 * a)) →
    (∀ τ, nτ τ = lam1 τ - D0 τ) →
    (∀ τ ∈ TT, lam1 τ = aT τ - (N - k) / 2) → (∀ τ, τ ∉ TT → S - (N - 1) / 2 ≤ lam1 τ) →
    (∀ τ, D0 τ ≤ S + m * η + (if τ ∈ TT then bT τ else 0)) →
    (∀ τ, D1 τ ≤ 3 * D0 τ + S + η) →
    (∀ τ ∈ TT, bT τ ≤ b') →
    0 ≤ logT → logT ≤ CT * m * L → 0 ≤ CT → 0 ≤ b' →
    ev ≤ Cev * f * N ^ 2 * La → 0 ≤ Cev →

    (∀ j ρ, (∑ i, ph (ν j ρ i)) - fa j ρ ≤ (if ρ ∈ TT then ph (aT ρ) else 0) + eE j ρ) →
    (∀ j ρ, (∑ i, ν j ρ i) = (if ρ ∈ TT then aT ρ else 0) + k * w j ρ + δ j ρ) →
    (∀ j ρ, eE j ρ ≤ C0 * (w j ρ + S + N ^ 2 + m * (tt + 1) * η) * La) →
    (∀ j ρ, |δ j ρ| ≤
      C0 * (w j ρ + k * (N + S) + m * (tt + 1) * η + (if ρ ∈ TT then k * b' else 0))) →

    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → a = x * b →
    1 ≤ rd → Real.log rd ≤ L → Real.log x ≤ L → La = Real.log (a * rd) →
    B0 = f * m * b * x ^ eps → 0 ≤ Nc → x ^ eps ≤ xe →

    (Fintype.card J : ℝ) = m → (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f →
    1 ≤ k → k + m ≤ N → 0 ≤ S → 0 ≤ tt → 0 ≤ η →

    (∀ j ρ, 0 ≤ w j ρ ∧ w j ρ ≤ 2 * b) → (∀ j, |pq j - k| ≤ m) → |logOm| ≤ La →

    lam0 ≤ b → m ^ 3 * N ^ 2 * L ≤ b → m * η * N * L ≤ b → k * N ≤ b →
    k * S ≤ w'' → m * (tt + 1) * η ≤ w'' → N * w'' ≤ b → b' * N ≤ a → m * k * b' ≤ a →

    25 / 2 ≤ C0 → 16 + CT + Cev ≤ C0 →
    Cth + c5 + 2 * c6 + 1 + 2 * C2 * (CT + C8) + 2 * C4 * (1 + CT + C8) ≤ C0 →
    (64 * (C1 + 3 * Cf) + 8 * Cc + 2) + (6 * Cb + 2) ≤ C0 →
      muC + hu - 2 * Fo ≤
        ∑ t ∈ TT, (m * (ph (aT t) - aT t * logOm) - aT t * logT) +
        (50 * C0 + 10) * ((TT.card : ℝ) * a * La + m * (B0 + Nc) * xe)
end Formalism.DivisorInequality


