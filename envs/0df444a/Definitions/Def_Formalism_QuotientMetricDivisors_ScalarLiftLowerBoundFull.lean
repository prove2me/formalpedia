-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_ScalarLiftLowerBoundFull
-- name    : Formalism_QuotientMetricDivisors_ScalarLiftLowerBoundFull
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:31:36.145798+00:00
-- url     : https://prove2.me/theorems/ef848dbb-22bb-495e-8fd2-deb48a7a2112
-- title:
--   Scalar Lift Lower Bound Full
-- statement:
--   Definitions and structural lemmas for Scalar Lift Lower Bound Full, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/ScalarLiftLowerBoundFull.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_StatementK
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualLe
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualGeF
import Definitions.Def_Formalism_QuotientMetricDivisors_UntwistedChoice
import Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_QuotientMetricDivisors_ScalarLiftLowerBoundRows
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
namespace Formalism.DivisionValues
def HeightRecord : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n D m : ℕ) (c : Fin (m + 1) → ℕ)
    (Xc : ∀ i, InfinitePlace K → Matrix (Fin (c i)) (Fin (c i)) ℂ), (∀ i v, IsUnit (Xc i v).det) →
    ∀ (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K)
      (H : Matrix (Fin n) (Fin n) K) (X0 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ),
    (∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = H.map v.embedding) →
    ∀ P : Matrix (Fin D) (Fin n) K, Function.Surjective P.mulVec →
    ∀ XQ : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, IsQuotMetric P H XQ →
    ∀ XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, (∀ v, IsUnit (XE v).det) →
    ∀ ι : Matrix (Fin D) (Fin D) K, IsUnit ι.det →
    ∀ (Ix J : Type) [Fintype Ix] [Nonempty Ix] [Fintype J] (Qp : Ix → Submodule K (Fin D → K)),
    (⨆ p, Qp p) = ⊤ →
    ∀ (lam : J → Ix → InfinitePlace K → ℝ),
    (∀ v p, ∀ x ∈ Qp p, ∀ y : Fin D → K,
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin D)) XE v (ι.mulVec x) (ι.mulVec y) =
        ((∏ j, lam j p v : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin D)) XQ v x y) →
    ∀ (Pt : (Fin (c (Fin.last m)) → K) →ₗ[K] Module.Dual K (Fin n → K))
      (B : (Fin (c 0) → K) →ₗ[K] Module.Dual K (Fin D → K)),
    (∀ φ F, B φ (ι.mulVec (P.mulVec F)) = Pt ((chainMat Kj (Fin.last m)).mulVec φ) F) → B ≠ 0 →
    ∀ (hP : ℝ) (hK : Fin m → InfinitePlace K → ℝ) (hKm : Fin m → ℝ) (hlam : J → ℝ),
    (∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c (Fin.last m)))) (Xc (Fin.last m))
      (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame X0) v Pt ^ 2 ≤ Real.exp hP) →
    (∀ j v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
      (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) ^ 2 ≤ Real.exp (hK j v)) →
    (∀ j p v, Real.exp (hlam j) ≤ lam j p v) →
    (∀ j, (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, hK j v ≤ hKm j) →
    ∃ cu : InfinitePlace K → ℝ, (∀ v, 0 < cu v) ∧
      (∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0)
          (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) v B ^ 2 ≤ cu v) ∧
      (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (cu v) = hP + ∑ j, hKm j - ∑ j, hlam j ∧
      Formalism.HN.htMap (Pi.basisFun K (Fin (c 0))) (Xc 0) (Pi.basisFun K (Fin D)).dualBasis
                (Formalism.HN.dualFrame XE) B ≤ hP + ∑ j, hKm j - ∑ j, hlam j
def DivIneqRecord : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
    (muC mu0 Fo hu hP mlam logT : ℝ) (hK : J → ℝ) (aT : Pl → ℝ) (phν nν fa : J → Pl → ℝ)
    (x eps L b a rd La B0 Nc m f k N S tt η w'' b' lam0 C0 ce : ℝ)
    (Lpass Eb e6 eP logOm : ℝ) (eK pq : J → ℝ) (w eE δ : J → Pl → ℝ),
    muC ≤ mu0 + Lpass →
    mu0 ≤ ∑ j, ∑ ρ, pq j * w j ρ * logOm + 2 * Fo + Eb →
    hu = hP + ∑ j, hK j - mlam →
    (∀ j, hK j ≤ ∑ ρ, (phν j ρ - nν j ρ * logOm) + eK j) →
    ∑ j, ∑ ρ, fa j ρ - e6 ≤ mlam →
    hP ≤ -(∑ t ∈ TT, aT t * logT) + eP →
    (∀ j ρ, phν j ρ - fa j ρ ≤ (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (aT ρ) else 0) + eE j ρ) →
    (∀ j ρ, nν j ρ = (if ρ ∈ TT then aT ρ else 0) + k * w j ρ + δ j ρ) →
    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → a = x * b →
    1 ≤ rd → Real.log rd ≤ L → Real.log x ≤ L → La = Real.log (a * rd) →
    B0 = f * m * b * x ^ eps → 0 ≤ Nc →
    (Fintype.card J : ℝ) = m → (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f →
    1 ≤ k → 1 ≤ N → 0 ≤ S → 0 ≤ tt → 0 ≤ η →
    (∀ j ρ, 0 ≤ w j ρ ∧ w j ρ ≤ 2 * b) →
    (∀ j, |pq j - k| ≤ m) → |logOm| ≤ La →
    m * lam0 ≤ b → N ^ 2 ≤ b → m ^ 3 * N ^ 2 * L ≤ b → m * η * N * L ≤ b → k * N ≤ b →
    k * S ≤ w'' → m * (tt + 1) * η ≤ w'' → N * w'' ≤ b → b' * N ≤ a → m * k * b' ≤ a →

    1 ≤ C0 → C0 ≤ ce →
    Lpass ≤ 1 + C0 * (m * lam0) →
    Eb ≤ ce * m * (x ^ eps * B0 + (Real.log x) ^ 2 * Nc) →
    (∀ j, eK j ≤ C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L)) →
    e6 ≤ C0 * m * f * N ^ 2 * La →
    eP ≤ C0 * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La →
    (∀ j ρ, eE j ρ ≤ C0 * (w j ρ + S + N ^ 2 + m * (tt + 1) * η) * La) →
    (∀ j ρ, |δ j ρ| ≤
      C0 * (w j ρ + k * (N + S) + m * (tt + 1) * η + (if ρ ∈ TT then k * b' else 0))) →
      muC + hu - 2 * Fo ≤
        ∑ t ∈ TT, (m * (Formalism.LatticeIndexTer.ph (aT t) - aT t * logOm) - aT t * logT) +
        ((50 * C0 + 10) * ((TT.card : ℝ) * a * La) +
          60 * ce * (m * (x ^ eps * B0 + (Real.log x) ^ 2 * Nc)))
def DivIneqUniform : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
    (muC mu0 Fo hu hP mlam logT : ℝ) (hK : J → ℝ) (aT : Pl → ℝ) (phν nν fa : J → Pl → ℝ)
    (x eps L b a rd La B0 Nc m f k N S tt η w'' b' lam0 C0 ce : ℝ)
    (Lpass Eb e6 eP logOm : ℝ) (eK pq : J → ℝ) (w eE δ : J → Pl → ℝ),
    muC ≤ mu0 + Lpass →
    mu0 ≤ ∑ j, ∑ ρ, pq j * w j ρ * logOm + 2 * Fo + Eb →
    hu = hP + ∑ j, hK j - mlam →
    (∀ j, hK j ≤ ∑ ρ, (phν j ρ - nν j ρ * logOm) + eK j) →
    ∑ j, ∑ ρ, fa j ρ - e6 ≤ mlam →
    hP ≤ -(∑ t ∈ TT, aT t * logT) + eP →
    (∀ j ρ, phν j ρ - fa j ρ ≤ (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (aT ρ) else 0) + eE j ρ) →
    (∀ j ρ, nν j ρ = (if ρ ∈ TT then aT ρ else 0) + k * w j ρ + δ j ρ) →
    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → a = x * b →
    1 ≤ rd → Real.log rd ≤ L → Real.log x ≤ L → La = Real.log (a * rd) →
    B0 = f * m * b * x ^ eps → 0 ≤ Nc →
    (Fintype.card J : ℝ) = m → (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f →
    1 ≤ k → 1 ≤ N → 0 ≤ S → 0 ≤ tt → 0 ≤ η →
    (∀ j ρ, 0 ≤ w j ρ ∧ w j ρ ≤ 2 * b) →
    (∀ j, |pq j - k| ≤ m) → |logOm| ≤ La →
    m * lam0 ≤ b → N ^ 2 ≤ b → m ^ 3 * N ^ 2 * L ≤ b → m * η * N * L ≤ b → k * N ≤ b →
    k * S ≤ w'' → m * (tt + 1) * η ≤ w'' → N * w'' ≤ b → b' * N ≤ a → m * k * b' ≤ a →

    1 ≤ C0 → 0 ≤ ce → (Real.log x) ^ 2 ≤ x ^ eps → 50 * C0 + 10 ≤ x ^ eps →
    ce * (50 * C0 + 10) ≤ C0 * x ^ eps →
    Lpass ≤ 1 + C0 * (m * lam0) →
    Eb ≤ ce * m * (x ^ eps * B0 + (Real.log x) ^ 2 * Nc) →
    (∀ j, eK j ≤ C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L)) →
    e6 ≤ C0 * m * f * N ^ 2 * La →
    eP ≤ C0 * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La →
    (∀ j ρ, eE j ρ ≤ C0 * (w j ρ + S + N ^ 2 + m * (tt + 1) * η) * La) →
    (∀ j ρ, |δ j ρ| ≤
      C0 * (w j ρ + k * (N + S) + m * (tt + 1) * η + (if ρ ∈ TT then k * b' else 0))) →
      muC + hu - 2 * Fo ≤
        ∑ t ∈ TT, (m * (Formalism.LatticeIndexTer.ph (aT t) - aT t * logOm) - aT t * logT) +
        ((50 * C0 + 10) * ((TT.card : ℝ) * a * La) + m * (B0 + Nc) * (x ^ eps) ^ 2)
def AbsorbBRecord : Prop :=
    ∀ (J Pl : Type) [Fintype J] [Fintype Pl]
    (x eps L b B0 Nc ce l2 m f N lam0 logg logDG C0 LG E3 logOm : ℝ)
    (pq Lj E1 E2 : J → ℝ) (w : J → Pl → ℝ),
    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → Real.log x ≤ L →
    B0 = f * m * b * x ^ eps → 0 ≤ Nc → 1 ≤ ce → 0 ≤ l2 →
    (Fintype.card J : ℝ) = m → 1 ≤ m → 1 ≤ f →
    lam0 ≤ b → N ^ 2 * logg ≤ b → N * Real.log (f * N) ≤ b →
    0 ≤ C0 →
    (∀ j, Lj j ≤ (∑ ρ, pq j * w j ρ * logOm) + C0 * B0 * Real.log (Real.log x)) →
    LG ≤ lam0 + C0 * f * N ^ 2 * logg →
    logDG ≤ C0 * f * N * Real.log (f * N) →
    (∀ j, E1 j ≤ C0 * (ce * (x ^ eps * B0 + l2 * Nc)) + logDG + C0 * f * N ^ 2 * logg) →
    (∀ j, E2 j ≤ C0 * (ce * (x ^ eps * B0 + l2 * Nc))) →
    E3 ≤ 1 →
      (∑ j, Lj j) + LG + (∑ j, (E1 j + E2 j)) + E3 ≤
        (∑ j, ∑ ρ, pq j * w j ρ * logOm) + (6 * C0 + 2) * m * (ce * (x ^ eps * B0 + l2 * Nc))
def DivIneqWithBRecord : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
    (muC mu0 Fo hu hP mlam logT : ℝ) (hK : J → ℝ) (aT : Pl → ℝ) (phν nν fa : J → Pl → ℝ)
    (x eps L b a rd La B0 Nc ce l2 m f k N S tt η w'' b' lam C0 : ℝ)
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
    B0 = f * m * b * x ^ eps → 0 ≤ Nc → 1 ≤ ce → 0 ≤ l2 →
    (Fintype.card J : ℝ) = m → (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f →
    1 ≤ k → 1 ≤ N → 0 ≤ S → 0 ≤ tt → 0 ≤ η → 0 ≤ lam → 0 ≤ b' →
    (∀ j ρ, 0 ≤ w j ρ ∧ w j ρ ≤ 2 * b) →
    (∀ j, |pq j - k| ≤ m) → |logOm| ≤ La →
    m * lam ≤ b → N ^ 2 ≤ b → m ^ 3 * N ^ 2 * L ≤ b → m * η * N * L ≤ b → k * N ≤ b →
    k * S ≤ w'' → m * (tt + 1) * η ≤ w'' → N * w'' ≤ b → b' * N ≤ a → m * k * b' ≤ a →
    N ^ 2 * logg ≤ b → N * Real.log (f * N) ≤ b →
    0 ≤ C0 →
    Lpass ≤ 1 + C0 * (m * lam) →
    (∀ j, Lj j ≤ (∑ ρ, pq j * w j ρ * logOm) + C0 * B0 * Real.log (Real.log x)) →
    LG ≤ lam + C0 * f * N ^ 2 * logg →
    logDG ≤ C0 * f * N * Real.log (f * N) →
    (∀ j, E1 j ≤ C0 * (ce * (x ^ eps * B0 + l2 * Nc)) + logDG + C0 * f * N ^ 2 * logg) →
    (∀ j, E2 j ≤ C0 * (ce * (x ^ eps * B0 + l2 * Nc))) →
    E3 ≤ 1 →
    (∀ j, eK j ≤ C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L)) →
    e6 ≤ C0 * m * f * N ^ 2 * La →
    eP ≤ C0 * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La →
    (∀ j ρ, eE j ρ ≤ C0 * (w j ρ + S + N ^ 2 + m * (tt + 1) * η) * La) →
    (∀ j ρ, |δ j ρ| ≤
      C0 * (w j ρ + k * (N + S) + m * (tt + 1) * η + (if ρ ∈ TT then k * b' else 0))) →
      muC + hu - 2 * Fo ≤
        ∑ t ∈ TT, (m * (Formalism.LatticeIndexTer.ph (aT t) - aT t * logOm) - aT t * logT) +
        (50 * (6 * C0 + 2) + 10) * ((TT.card : ℝ) * a * La + m * (ce * (x ^ eps * B0 + l2 * Nc)))
def StepBWRho : Prop :=
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
    ∀ (ρD : Tup → K) (ρr : Tup → ℝ), (∀ t, v0.embedding (ρD t) = ((ρr t ^ D : ℝ) : ℂ)) →
    (∀ t, 0 < ρr t) → (∀ w, vw w (ρD (μ w)) = 0) →
    (∀ v, detRatio (XQ μ0) XE (ι μ0) v = κ v ^ D * ∏ j, detRatio (XT j μ0) (XW j) (θ j μ0) v) →
    (∀ t, detRatio (XQ t) XE (ι t) v0 =
      (κ v0 * ρr t) ^ D * ∏ j, detRatio (XT j t) (XW j) (θ j t) v0) →
    ∀ (G : Tup → HeightOneSpectrum (𝓞 K) → K)
      (e : Tup → HeightOneSpectrum (𝓞 K) → Fin D → Fin D → K),
    (∀ t w, IsLocBasis (abelian₂ t) w (e t w)) →
    (∀ t w, v0.embedding (G t w) = (gram (XQ t) v0 (e t w)).det) →
    (lcv (XQ μ0) (abelian₂ μ0) ≤ ∑ᶠ w, lw w * (vw w (G μ0 w) : ℝ)) →
    ∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsLattice K R →
    (∀ w, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι (μ w)) (abelian₂ (μ w)))) →
      (Function.support fun w => lw w * ((vw w (G (μ w) w) : ℝ) + ∑ j,
        ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (jw (HT j (μ w)) w (T j (μ w)) : ℝ)))).Finite ∧
      lcv XE R ≤ (D : ℝ) * meanLog κ + ∑ j, lcv (XW j) (M j) +
        ∑ᶠ w, lw w * ((vw w (G (μ w) w) : ℝ) + ∑ j,
          ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
           (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
           (jw (HT j (μ w)) w (T j (μ w)) : ℝ)))
def StepBRWRho : Prop :=
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
    ∀ (ρD : Tup → K) (ρr : Tup → ℝ), (∀ t, v0.embedding (ρD t) = ((ρr t ^ D : ℝ) : ℂ)) →
    (∀ t, 0 < ρr t) → (∀ w, vw w (ρD (μ w)) = 0) →
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
      (Function.support fun w => lw w * ((vw w (G (μ w) w) : ℝ) + ∑ j,
        ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (jw (HT j (μ w)) w (T j (μ w)) : ℝ)))).Finite ∧
      lcv XE R ≤ (D : ℝ) * meanLog κ + ∑ j, lcv (XW j) (M j) +
        ∑ᶠ w, lw w * ((vw w (G (μ w) w) : ℝ) + ∑ j,
          ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
           (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
           (jw (HT j (μ w)) w (T j (μ w)) : ℝ)))
def BoundsChainWRho : Prop :=
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
    ∀ (ρD : Tup → K) (ρr : Tup → ℝ), (∀ t, v0.embedding (ρD t) = ((ρr t ^ D : ℝ) : ℂ)) →
    (∀ t, 0 < ρr t) → (∀ w, vw w (ρD (μ w)) = 0) →
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
    ∀ (LG E3 : ℝ) (L E1 E2 : J → ℝ) (ell g : HeightOneSpectrum (𝓞 K) → ℝ)
      (F err Jx η : HeightOneSpectrum (𝓞 K) → J → ℝ),
    0 < D →
    (∀ w ∈ S, (vw w (G (μ w) w) : ℝ) ≤ (D : ℝ) * g w) → ∑ w ∈ S, lw w * g w ≤ LG →
    (∀ j, lcv (XW j) (M j) / D ≤ L j) →
    (∀ w ∈ S, ∑ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
        (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ)) ≤
      (∑ j, (2 * F w j + err w j) + 2 / ell w ^ 2) * D) →
    (∀ w ∈ S, ∀ j, (jw (HT j (μ w)) w (T j (μ w)) : ℝ) ≤ Jx w j * D + η w j) →
    (∀ j, ∑ w ∈ S, lw w * (err w j + Jx w j) ≤ E1 j) →
    (∀ j, ∑ w ∈ S, lw w * η w j / D ≤ E2 j) →
    ∑ w ∈ S, lw w * (2 / ell w ^ 2) ≤ E3 →
      lcv XE R / D ≤ meanLog κ + ∑ j, L j + 2 * ∑ j, ∑ w ∈ S, lw w * F w j + LG +
        ∑ j, (E1 j + E2 j) + E3
def StepBRWRhoSq : Prop :=
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
    ∀ (r : Tup → K) (ρr : Tup → ℝ), (∀ t, v0.embedding (r t) = ((ρr t ^ D : ℝ) : ℂ)) → ρr μ0 = 1 →
    (∀ t, 0 < ρr t) →
    ∀ (q : Tup → ℚ), (∀ t, ρr t ^ 2 = (q t : ℝ)) → (∀ w, vw w ((q (μ w) : ℚ) : K) = 0) →
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
      (Function.support fun w => lw w * ((vw w (G (μ w) w) : ℝ) + ∑ j,
        ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (jw (HT j (μ w)) w (T j (μ w)) : ℝ)))).Finite ∧
      lcv XE R ≤ (D : ℝ) * meanLog κ + ∑ j, lcv (XW j) (M j) +
        ∑ᶠ w, lw w * ((vw w (G (μ w) w) : ℝ) + ∑ j,
          ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
           (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
           (jw (HT j (μ w)) w (T j (μ w)) : ℝ)))
def GoodTwist : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (K0 : Subfield K), IsCMSub K0 →
    ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ i j, H i j ∈ K0) →
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ 𝒯 : Set (Matrix (Fin n) (Fin n) K), (∀ T ∈ 𝒯, ∀ i j, T i j ∈ K0) →
    (∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T * T' = T' * T) → IsAdjStable H 𝒯 →
    ∀ e : Matrix (Fin n) (Fin n) K, (∀ i j, e i j ∈ K0) → e * e = e → (∀ T ∈ 𝒯, e * T = T * e) →
    (∀ x y : Fin n → K, hform H (e.mulVec x) y = hform H x (e.mulVec y)) →
    ∀ (Z : Submodule K (Fin n → K)) (Ω : Type) [Field Ω] (j : K →+* Ω)
      (S : Set (Matrix (Fin n) (Fin n) K → Ω)),
    extSpan j Z = ⨆ χ ∈ S, (simEig j 𝒯 χ).map (e.map j).mulVecLin →
    ∀ σ : K →+* ℂ, embSpan σ Z = embSpan (twist σ) Z
def GoodRatHerm : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) K) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ),
    IsRatHerm K0 H X →
    ∀ 𝒯 : Set (Matrix (Fin n) (Fin n) K), (∀ T ∈ 𝒯, ∀ i j, T i j ∈ K0) →
    (∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T * T' = T' * T) → IsAdjStable H 𝒯 →
    ∀ e : Matrix (Fin n) (Fin n) K, (∀ i j, e i j ∈ K0) → e * e = e → (∀ T ∈ 𝒯, e * T = T * e) →
    (∀ x y : Fin n → K, hform H (e.mulVec x) y = hform H x (e.mulVec y)) →
    ∀ (Z : Submodule K (Fin n → K)) (Ω : Type) [Field Ω] (j : K →+* Ω)
      (S : Set (Matrix (Fin n) (Fin n) K → Ω)),
    extSpan j Z = ⨆ χ ∈ S, (simEig j 𝒯 χ).map (e.map j).mulVecLin →
    ∃ (d : ℕ) (z : Fin d → Fin n → K) (XT : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ),
      LinearIndependent K z ∧ Submodule.span K (Set.range z) = Z ∧
      (∀ a i, z a i ∈ cmMax K) ∧
      IsRatHerm (cmMax K) (gramMat H z) XT ∧
      (∀ (v : InfinitePlace K) (x y : Fin d → K),
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) XT v x y =
          Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v (comb z x) (comb z y)) ∧
      (∀ x y : Fin d → K, hform (gramMat H z) x y = hform H (comb z x) (comb z y)) ∧
      ∀ T : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K T →
        (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
          lw w * (jw (gramMat H z) w T : ℝ)).Finite ∧
        lcv XT T = - ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (jw (gramMat H z) w T : ℝ)
def TwistOrth : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (K0 : Subfield K), IsCMSub K0 →
    ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ i j, H i j ∈ K0) →
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ Z U : Submodule K (Fin n → K), (∀ u, u ∈ U ↔ ∀ z ∈ Z, hform H z u = 0) →
    (∀ σ : K →+* ℂ, embSpan σ Z = embSpan (twist σ) Z) →
    ∀ (σ : K →+* ℂ) (x : Fin n → ℂ),
      x ∈ embSpan σ Z ↔ ∀ u ∈ embSpan σ U, star u ⬝ᵥ (H.map σ) *ᵥ x = 0
def ProvisoQuot : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (K0 : Subfield K), IsCMSub K0 →
    ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ i j, H i j ∈ K0) →
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ Z U : Submodule K (Fin n → K), (∀ u, u ∈ U ↔ ∀ z ∈ Z, hform H z u = 0) →
    (∀ σ : K →+* ℂ, embSpan σ Z = embSpan (twist σ) Z) →
    ∀ (d : ℕ) (E : Matrix (Fin n) (Fin d) K) (P : Matrix (Fin d) (Fin n) K), P * E = 1 →
    LinearMap.range E.mulVecLin = Z → LinearMap.ker P.mulVecLin = U →
    ∀ σ : K →+* ℂ,
      ((P.map σ) * (H.map σ)⁻¹ * (P.map σ)ᴴ)⁻¹ = (E.map σ)ᴴ * H.map σ * E.map σ
def ProvisoAdj : Prop :=
  ∀ (n r : ℕ) (Hc : Matrix (Fin n) (Fin n) ℂ) (Mc : Matrix (Fin r) (Fin r) ℂ), Hc.PosDef → Mc.PosDef →
    ∀ Th : Matrix (Fin r) (Fin n) ℂ,
      (∀ (x : Fin n → ℂ) (y : Fin r → ℂ),
        star (Th *ᵥ x) ⬝ᵥ Mc *ᵥ y = star x ⬝ᵥ Hc *ᵥ ((Hc⁻¹ * Thᴴ * Mc) *ᵥ y)) ∧
      ∀ Uc : Submodule ℂ (Fin n → ℂ), (∀ u, Th *ᵥ u = 0 → u ∈ Uc) →
      ∀ (Mp : Submodule ℂ (Fin r → ℂ)) (lam : ℂ),
      (∀ y ∈ Mp, Th *ᵥ ((Hc⁻¹ * Thᴴ * Mc) *ᵥ y) = lam • y) →
      ∀ x : Fin n → ℂ, (∀ u ∈ Uc, star u ⬝ᵥ Hc *ᵥ x = 0) → Th *ᵥ x ∈ Mp →
        (Hc⁻¹ * Thᴴ * Mc) *ᵥ (Th *ᵥ x) = lam • x
def LevelsPreserve : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (A : Submodule (𝓞 K) (Fin n → K))
    (Gi : Type) [Fintype Gi] (r : Gi → Matrix (Fin n) (Fin n) K) (c c' : Gi → K) (G : ℕ),
    (∀ g, ∀ x ∈ A, (r g).mulVec x ∈ A) → (∀ g, ∃ a : 𝓞 K, (G : K) * c g = (a : K)) →
    ∀ e ε : Matrix (Fin n) (Fin n) K, e = ∑ g, c g • r g → (∀ g, e * r g = r g * e) →
    ε = ∑ g, c' g • r g →
      e * ε = ε * e ∧
      (∀ x ∈ A, (G : 𝓞 K) • (e.mulVec x) ∈ A) ∧
      ∀ x ∈ A, ε.mulVec x = x →
        (G : 𝓞 K) • (e.mulVec x) ∈ A ∧ ε.mulVec ((G : 𝓞 K) • (e.mulVec x)) = (G : 𝓞 K) • (e.mulVec x)
def BoundsILevel : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n0 n' n : ℕ) (H0 : Matrix (Fin n0) (Fin n0) K)
    (Eε : Matrix (Fin n0) (Fin n') K) (Prε : Matrix (Fin n') (Fin n0) K), Prε * Eε = 1 →
    (Eεᴴ * H0 * Eε)ᴴ = Eεᴴ * H0 * Eε → IsUnit (Eεᴴ * H0 * Eε).det →
    ∀ (E : Matrix (Fin n') (Fin n) K) (Pr : Matrix (Fin n) (Fin n') K),
    IsOrthProj (Eεᴴ * H0 * Eε) E Pr →
    ∀ A0 B0 : Submodule (𝓞 K) (Fin n0 → K), Submodule.IsLattice K A0 → B0 ≤ A0 →
    ∀ s : ℕ, (∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform (Eεᴴ * H0 * Eε)) (cutLat Eε A0), (s : 𝓞 K) • x ∈ cutLat Eε B0) →
    ∀ (e0 : Matrix (Fin n0) (Fin n0) K) (G : ℕ), (∀ x ∈ B0, (G : 𝓞 K) • (e0.mulVec x) ∈ B0) →
    e0 * (Eε * Prε) = (Eε * Prε) * e0 → E * Pr = Prε * e0 * Eε →
      Submodule.IsLattice K (cutLat Eε A0) ∧
      Submodule.IsLattice K (cutLat E (cutLat Eε A0)) ∧
      ∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform (Eᴴ * (Eεᴴ * H0 * Eε) * E)) (cutLat E (cutLat Eε A0)),
        ((G * s : ℕ) : 𝓞 K) • x ∈ cutLat E (cutLat Eε A0)
def BoundsITwoCuts : Prop :=
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n' n : ℕ) (H' : Matrix (Fin n') (Fin n') K),
    H'ᴴ = H' → IsUnit H'.det →
    ∀ (E : Matrix (Fin n') (Fin n) K) (Pr : Matrix (Fin n) (Fin n') K), IsOrthProj H' E Pr →
    ∀ A B : Submodule (𝓞 K) (Fin n' → K), Submodule.IsLattice K A → B ≤ A →
    ∀ s : ℕ, (∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform H') A, (s : 𝓞 K) • x ∈ B) →
    ∀ (e ε : Matrix (Fin n') (Fin n') K), E * Pr = e * ε →
    ∀ G1 G2 : ℕ, (∀ x ∈ B, (G1 : 𝓞 K) • e.mulVec x ∈ B) → (∀ x ∈ B, (G2 : 𝓞 K) • ε.mulVec x ∈ B) →
      Submodule.IsLattice K (cutLat E A) ∧
      ∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform (Eᴴ * H' * E)) (cutLat E A),
        (((G1 * G2) * s : ℕ) : 𝓞 K) • x ∈ cutLat E A
def BoundsIClassFOne : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n' n : ℕ) (H' : Matrix (Fin n') (Fin n') K),
    H'ᴴ = H' → IsUnit H'.det →
    ∀ (E : Matrix (Fin n') (Fin n) K) (Pr : Matrix (Fin n) (Fin n') K), IsOrthProj H' E Pr →
    ∀ (Cl : Type) [Fintype Cl] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] (pair : V →ₗ⋆[K] V →ₗ[K] K),
    pair.IsSymm → pair.Nondegenerate →
    ∀ (Gam : Cl → Type) [∀ c, Group (Gam c)] [∀ c, Fintype (Gam c)]
      (ρ : ∀ c, Gam c →* Module.End K V),
    (∀ c γ x y, pair (ρ c γ x) (ρ c γ y) = pair x y) →
    ∀ I : (Fin n' → K) →ₗ[K] (Cl → V), Function.Injective I →
    (∀ f : Cl → V, (∃ x, I x = f) ↔ ∀ c γ, ρ c γ (f c) = f c) →
    IsClassSum H' I pair (fun c => Fintype.card (Gam c)) →
    ∀ Nab Del : Cl → Submodule (𝓞 K) V, (∀ c, Submodule.IsLattice K (Nab c)) →
    ∀ s : ℕ, (∀ c, ∀ y ∈ Formalism.HermitianLatticesTheory.dual pair (Nab c), (s : 𝓞 K) • y ∈ Del c) →
    (∀ c, Del c ≤ Nab c) → (∀ c γ, ∀ y ∈ Del c, ρ c γ y ∈ Del c) →
    ∀ (G : ℕ), 0 < G →
    (∀ x ∈ valLatF I Del, (G : 𝓞 K) • (E * Pr).mulVec x ∈ valLatF I Del) →
      Submodule.IsLattice K (valLatF I Nab) ∧ Submodule.IsLattice K (cutLat E (valLatF I Nab)) ∧
      ∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform (Eᴴ * H' * E)) (cutLat E (valLatF I Nab)),
        ((G * s : ℕ) : 𝓞 K) • x ∈ cutLat E (valLatF I Nab)
def Complement2Later : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (g : Fin 2 → ℕ),
    (∀ i, 0 < g i) → Nat.Coprime (g 0) (g 1) →
    ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
      (E F : J → HeightOneSpectrum (𝓞 K) → ℝ), (∀ j, (Function.support (E j)).Finite) →
    ∀ (nn : J → Fin 2 → K) (Dpi Dp Dm Eels : J → ℝ)
      (aT : Pl → ℝ) (w nν δν δpm : J → Pl → ℝ)
      (x eps L b B0 m f k N S tt η w'' b' X'' logd C0 CE : ℝ),
    (∀ j i w, PlOver (g i) w →
      E j w = F j w + (vw w (nn j i) : ℝ) + CE * f * (N ^ 2 + m ^ 2 * η) * (vw w (g i : K) : ℝ)) →
    0 ≤ CE → CE ≤ C0 →
    (∀ j i w, PlOver (g i) w → F j w = -((Dp j + Dm j) / 2) * (vw w (g i : K) : ℝ)) →
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
    (∀ j ρ, |δν j ρ| ≤ C0 * (k * S + m * tt * η + (if ρ ∈ TT then b' / x else 0))) →
    (∀ j ρ, |δpm j ρ| ≤ C0 * (k * S + m * η)) →
    (∀ j, Eels j ≤ C0 * B0 + ((TT.card : ℝ) * (2 * b + 4 * k * b') + 4 * f * k * b') * logd +
      C0 * (f * k * N * X'')) →
      (∀ j, |2 * (∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * E j w) -
        (∑ t ∈ TT, aT t) * Real.log ((g 0 : ℝ) * (g 1 : ℝ))| ≤ (9 * C0 ^ 2 + 6 * C0 + 20) * B0)
def Complement3Record : Prop :=
  ∀ (U J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)] (n : ℕ)
    (hu logT : U → ℝ) (aT : Pl → ℝ) (phν nν : U → J → Pl → ℝ) (c : U → J → Pl → Fin n → ℝ)
    (mlam cP e6 logOm : ℝ) (cK : J → ℝ) (w fa pr nr : J → Pl → ℝ)
    (x eps L b a rd La B0 m f k N S Sc tt η w'' b' Δ C0 : ℝ),
    (∀ u, hu u = (-(∑ t ∈ TT, aT t) * logT u + cP) +
      ∑ j, (∑ ρ, (phν u j ρ - nν u j ρ * logOm) + cK j) - mlam) →
    mlam = ∑ j, ∑ ρ, fa j ρ - e6 →
    (∀ u j ρ, phν u j ρ = ∑ i, Formalism.LatticeIndexTer.ph (w j ρ + c u j ρ i) +
      (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (aT ρ + w j ρ) else 0) + pr j ρ) →
    (∀ u j ρ, nν u j ρ = ∑ i, (w j ρ + c u j ρ i) +
      (if ρ ∈ TT then aT ρ + w j ρ else 0) + nr j ρ) →
    (∀ u j ρ i, 0 ≤ c u j ρ i ∧ c u j ρ i ≤ Sc) → 0 ≤ Sc → Sc ≤ 3 * S → (n : ℝ) ≤ k →
    (∀ ρ ∈ TT, a ≤ aT ρ ∧ aT ρ ≤ a + Δ) → m * Δ ≤ a →
    (∀ j ρ, 1 ≤ w j ρ ∧ w j ρ + Sc ≤ a * rd) → (∀ j, ∀ ρ ∈ TT, aT ρ + w j ρ ≤ a * rd) →
    (∀ u, 0 ≤ logT u ∧ logT u ≤ C0 * m * L) →
    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → a = x * b →
    1 ≤ rd → Real.log rd ≤ L → Real.log x ≤ L → La = Real.log (a * rd) →
    B0 = f * m * b * x ^ eps →
    (Fintype.card J : ℝ) = m → (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f →
    1 ≤ k → 1 ≤ N → 0 ≤ S → 0 ≤ tt → 0 ≤ η → 0 ≤ b' → 0 ≤ C0 → |logOm| ≤ La →
    m ^ 3 * N ^ 2 * L ≤ b → k * N ≤ b → k * S ≤ w'' → m * (tt + 1) * η ≤ w'' → N * w'' ≤ b →
    m * k * b' ≤ a →
      ∀ u u', |(hu u + ∑ t ∈ TT, aT t * logT u) - (hu u' + ∑ t ∈ TT, aT t * logT u')| ≤
        (7 * C0 ^ 2 + 18) * ((TT.card : ℝ) * a * La + m * B0)
def ReduceDiRecord : Prop :=
  ∀ (J Pl Emb : Type) [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb]
    (logK mid : J → Emb → ℝ) (logOmτ : Pl → Emb → ℝ) (hK : J → ℝ) (phν nν : J → Pl → ℝ)
    (logOm f m N L La logg logT C1 C2 C3 C4 : ℝ)
    (h1 : ∀ j s, logK j s ≤ (∑ ρ, (phν j ρ - nν j ρ * logOmτ ρ s)) + mid j s +
      C1 * f * m ^ 2 * N ^ 2 * (L + (logg + logT)))
    (h2 : ∀ j, hK j = (∑ s, logK j s) / (Fintype.card Emb : ℝ))
    (h3 : ∀ ρ, (∑ s, logOmτ ρ s) / (Fintype.card Emb : ℝ) = logOm)
    (h4 : ∀ j, (∑ s, mid j s) / (Fintype.card Emb : ℝ) ≤ C2 * f * N ^ 2 * L)
    (h5 : logg ≤ C3 * L) (h6 : logT ≤ C4 * m * L) (hf : 0 ≤ f) (hm : 1 ≤ m) (hL : 0 ≤ L) (hLa : L ≤ La)
    (c1 : 0 ≤ C1) (c2 : 0 ≤ C2) (c3 : 0 ≤ C3) (c4 : 0 ≤ C4),
    ∀ j, hK j ≤ (∑ ρ, (phν j ρ - nν j ρ * logOm)) +
      (C2 + C1 * (1 + C3 + C4)) * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L)
def ScalarLiftLowerBoundFull : Prop :=
  ∀ (J Pl Emb Frm : Type) [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb]
    [Fintype Frm] [Nonempty Frm]
    (loglam : J → Frm → Emb → ℝ) (Hp Hm : J → Pl → ℕ) (mlam f m nV L' C1 : ℝ)
    (hq : ∀ j π s, (∑ ρ, Real.log ((Hp j ρ : ℝ) * (Hm j ρ : ℝ))) - C1 * f * nV ^ 2 * L' ≤ loglam j π s)
    (hp : ∀ j ρ, 0 < Hp j ρ) (hm : ∀ j ρ, 0 < Hm j ρ) (hn : 0 ≤ nV) (hL : 0 ≤ L') (hf : 0 ≤ f) (hC : 0 ≤ C1)
    (hJ : (Fintype.card J : ℝ) = m)
    (hml : mlam = (∑ s, Finset.univ.inf' Finset.univ_nonempty (fun π : Frm => ∑ j, loglam j π s)) /
      (Fintype.card Emb : ℝ)),
    (∀ j π s, (∑ ρ, Real.log (Hp j ρ : ℝ)) - C1 * f * nV ^ 2 * L' ≤ loglam j π s) ∧
    (∑ j, ((∑ ρ, Real.log (Hp j ρ : ℝ)) - C1 * f * nV ^ 2 * L')) =
      (∑ j, ∑ ρ, Real.log (Hp j ρ : ℝ)) - C1 * m * f * nV ^ 2 * L' ∧
    (∑ j, ∑ ρ, Real.log (Hp j ρ : ℝ)) - C1 * m * f * nV ^ 2 * L' ≤ mlam
end Formalism.DivisionValues


