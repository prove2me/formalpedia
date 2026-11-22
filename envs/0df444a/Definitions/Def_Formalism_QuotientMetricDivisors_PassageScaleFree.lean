-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_PassageScaleFree
-- name    : Formalism_QuotientMetricDivisors_PassageScaleFree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:21:59.072635+00:00
-- url     : https://prove2.me/theorems/88c9699c-6679-4178-9d7f-d5ed0dec575f
-- title:
--   Passage Scale Free
-- statement:
--   Definitions and structural lemmas for Passage Scale Free, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/PassageScaleFree.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_StatementK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
namespace Formalism.DivisionValues
def PassageArith : Prop :=
  ∀ (muC mu0 HH0 lam0 logκ de c1 c2 c3 Cd f r g k b p1 p2 C0 : ℝ),
    0 ≤ c1 → 0 ≤ c2 → 0 ≤ Cd → 0 ≤ f → 0 ≤ r → 1 ≤ k → 1 ≤ b →

    de = Cd * f * r / g → (k * b) ^ 8 ≤ g →

    0 ≤ lam0 → lam0 ≤ b → mu0 ≤ logκ + p1 * b → HH0 ≤ -logκ + p2 * b →

    c1 * Cd * f * r * (p1 + p2 + c2) ≤ (k * b) ^ 7 → 3 * Cd * f * r ≤ (k * b) ^ 8 →

    (de ≤ 1 / 3 → muC ≤ mu0 + c1 * de * (mu0 + HH0 + c2 * lam0) + c3 * lam0) →
    c3 ≤ C0 →
      0 ≤ de ∧ de ≤ 1 / 3 ∧
      muC ≤ mu0 + (c1 * de * (mu0 + HH0 + c2 * lam0) + c3 * lam0) ∧
      c1 * de * (mu0 + HH0 + c2 * lam0) ≤ 1 ∧
      c1 * de * (mu0 + HH0 + c2 * lam0) + c3 * lam0 ≤ 1 + C0 * lam0
def PassageScaleFree : Prop :=
  ∀ (muC mu0 HH0 lam0 de c1 c2 c3 τ0 τs : ℝ),
    (mu0 + τ0) + (HH0 - τ0) + c2 * lam0 = mu0 + HH0 + c2 * lam0 ∧
    (muC + τs ≤ (mu0 + τ0) + c1 * de * ((mu0 + τ0) + (HH0 - τ0) + c2 * lam0) + c3 * lam0 ↔
      muC + (τs - τ0) ≤ mu0 + c1 * de * (mu0 + HH0 + c2 * lam0) + c3 * lam0)
def PassageQ : Prop :=
  ∀ (mu0 HH0 lam0 logκ c2 cq f r g k b p1 p2 : ℝ),
    0 ≤ c2 → 1 ≤ k → 1 ≤ b → (k * b) ^ 8 ≤ g →
    lam0 ≤ b → mu0 ≤ logκ + p1 * b → HH0 ≤ -logκ + p2 * b →
      mu0 + HH0 + c2 * lam0 ≤ (p1 + p2 + c2) * b ∧
      (1 ≤ p1 + p2 + c2 → 1 ≤ (p1 + p2 + c2) * b) ∧
      (cq * f * r * (p1 + p2 + c2) ≤ (k * b) ^ 7 → cq * f * r * ((p1 + p2 + c2) * b) ≤ g)
def PassageSize : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl]
    (mu0 logκ Fo Fabs Eb logOm La W b N m f C0 xe B0 Nc pF pN x eps : ℝ) (pq : J → ℝ) (w : J → Pl → ℝ),
    mu0 ≤ logκ + ∑ j, ∑ ρ, pq j * w j ρ * logOm + 2 * Fo + Eb →
    (Fintype.card J : ℝ) = m → (Fintype.card Pl : ℝ) ≤ f →
    (∀ j, |pq j| ≤ N) → 0 ≤ W → (∀ j ρ, 0 ≤ w j ρ ∧ w j ρ ≤ W) → |logOm| ≤ La →
    Fo ≤ Fabs → 0 ≤ C0 → Eb ≤ C0 * m * xe * (B0 + Nc) →
      mu0 ≤ logκ + m * f * N * W * La + 2 * Fabs + C0 * m * xe * (B0 + Nc) ∧
      (W ≤ 2 * b → 0 ≤ b → Fabs ≤ pF * b → Nc ≤ pN * b → B0 = f * m * b * x ^ eps → x ^ eps ≤ xe →
        0 ≤ xe →
        mu0 ≤ logκ + (2 * m * f * N * La + 2 * pF + C0 * m * xe * (f * m * xe + pN)) * b)
def PassageLam : Prop :=
  ∀ (lam0 f r g Cg L b : ℝ), 0 ≤ f →
    lam0 ≤ 2 * f * r ^ 2 * Real.log g → Real.log g ≤ Cg * L →
      28 * lam0 ≤ 56 * f * r ^ 2 * Real.log g ∧ 28 * lam0 ≤ 56 * Cg * f * r ^ 2 * L ∧
      (2 * Cg * f * r ^ 2 * L ≤ b → lam0 ≤ b)
def PassageChain : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl]
    (muC mu0 HH0 lam0 logκ de Cd r g k p2 : ℝ)
    (Fo Fabs Eb logOm La W b N m f C0 xe B0 Nc pF pN x eps : ℝ) (pq : J → ℝ) (w : J → Pl → ℝ),

    mu0 ≤ logκ + ∑ j, ∑ ρ, pq j * w j ρ * logOm + 2 * Fo + Eb →
    (Fintype.card J : ℝ) = m → (Fintype.card Pl : ℝ) ≤ f →
    (∀ j, |pq j| ≤ N) → 0 ≤ W → (∀ j ρ, 0 ≤ w j ρ ∧ w j ρ ≤ W) → |logOm| ≤ La →
    Fo ≤ Fabs → 0 ≤ C0 → Eb ≤ C0 * m * xe * (B0 + Nc) →
    W ≤ 2 * b → Fabs ≤ pF * b → Nc ≤ pN * b → B0 = f * m * b * x ^ eps → x ^ eps ≤ xe → 0 ≤ xe →

    HH0 ≤ -logκ + p2 * b →

    0 ≤ Cd → 0 ≤ r → 1 ≤ k → 1 ≤ b → de = Cd * f * r / g → (k * b) ^ 8 ≤ g →
    0 ≤ lam0 → lam0 ≤ b →

    3 * Cd * f * r *
      ((2 * m * f * N * La + 2 * pF + C0 * m * xe * (f * m * xe + pN)) + p2 + 28) ≤ (k * b) ^ 7 →
    3 * Cd * f * r ≤ (k * b) ^ 8 →

    (de ≤ 1 / 3 → muC ≤ mu0 + 3 * de * (mu0 + HH0 + 28 * lam0) + 28 * lam0) →
      muC ≤ mu0 + (3 * de * (mu0 + HH0 + 28 * lam0) + 28 * lam0) ∧
      3 * de * (mu0 + HH0 + 28 * lam0) + 28 * lam0 ≤ 1 + 28 * lam0 ∧
      muC - 2 * Fo ≤ logκ + ∑ j, ∑ ρ, pq j * w j ρ * logOm + Eb + 1 + 28 * lam0
def DivIneqPassage : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
    (muC mu0 Fo hu hP mlam logT : ℝ) (hK : J → ℝ) (aT : Pl → ℝ) (phν nν fa : J → Pl → ℝ)
    (x eps L b a rd La B0 Nc xe m f k N S tt η w'' b' dC lam0 C0 : ℝ)
    (Eb e6 eP logOm : ℝ) (eK pq : J → ℝ) (w eE δ : J → Pl → ℝ)

    (logκ HH0 de c1 c2 c3 Cd r g p2 pF pN : ℝ),

    0 ≤ c1 → 0 ≤ c2 → c3 ≤ C0 → 0 ≤ Cd → 0 ≤ r → de = Cd * f * r / g → (k * b) ^ 8 ≤ g → 0 ≤ lam0 →
    (de ≤ 1 / 3 → muC ≤ mu0 + c1 * de * (mu0 + HH0 + c2 * lam0) + c3 * lam0) →

    HH0 ≤ -logκ + p2 * b → (∀ j, |pq j| ≤ N) → Fo ≤ pF * b → Nc ≤ pN * b →
    c1 * Cd * f * r *
      ((2 * m * f * N * La + 2 * pF + C0 * m * xe * (f * m * xe + pN)) + p2 + c2) ≤ (k * b) ^ 7 →
    3 * Cd * f * r ≤ (k * b) ^ 8 →

    mu0 ≤ logκ + ∑ j, ∑ ρ, pq j * w j ρ * logOm + 2 * Fo + Eb →
    hu = hP + ∑ j, hK j - mlam - logκ →

    (∀ j, hK j ≤ ∑ ρ, (phν j ρ - nν j ρ * logOm) + eK j) →
    ∑ j, ∑ ρ, fa j ρ - e6 ≤ mlam →
    hP ≤ -(∑ t ∈ TT, aT t * logT) + eP →
    (∀ j ρ, phν j ρ - fa j ρ ≤ (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (aT ρ) else 0) + eE j ρ) →
    (∀ j ρ, nν j ρ = (if ρ ∈ TT then aT ρ else 0) + k * w j ρ + δ j ρ) →
    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → a = x * b →
    1 ≤ rd → Real.log rd ≤ L → Real.log x ≤ L → La = Real.log (a * rd) →
    B0 = f * m * b * x ^ eps → 0 ≤ Nc → x ^ eps ≤ xe →
    (Fintype.card J : ℝ) = m → (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f →
    1 ≤ k → 1 ≤ N → 0 ≤ S → 0 ≤ tt → 0 ≤ η → 1 ≤ dC →
    (∀ j ρ, 0 ≤ w j ρ ∧ w j ρ ≤ 2 * b) →
    (∀ j, |pq j - k| ≤ m) → |logOm| ≤ La →
    lam0 ≤ b → N ^ 2 * dC ≤ b → m ^ 3 * N ^ 2 * L ≤ b → m * η * N * L ≤ b → k * N ≤ b →
    k * S ≤ w'' → m * (tt + 1) * η ≤ w'' → N * w'' ≤ b → b' * N ≤ a → m * k * b' ≤ a →
    0 ≤ C0 →
    Eb ≤ C0 * m * xe * (B0 + Nc) →
    (∀ j, eK j ≤ C0 * (f * N ^ 2 * (La + dC) + f * m ^ 3 * N ^ 2 * L)) →
    e6 ≤ C0 * m * f * N ^ 2 * La →
    eP ≤ C0 * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La →
    (∀ j ρ, eE j ρ ≤ C0 * (w j ρ + S + N ^ 2 + m * (tt + 1) * η) * La) →
    (∀ j ρ, |δ j ρ| ≤
      C0 * (w j ρ + k * (N + S) + m * (tt + 1) * η + (if ρ ∈ TT then k * b' else 0))) →
      muC + hu - 2 * Fo ≤
        ∑ t ∈ TT, (m * (Formalism.LatticeIndexTer.ph (aT t) - aT t * logOm) - aT t * logT) +
        (50 * C0 + 10) * ((TT.card : ℝ) * a * La + m * (B0 + Nc) * xe)
section Defs
variable {K : Type} [Field K] [NumberField K]
def scaleFrame {d : ℕ} (t : InfinitePlace K → ℝ) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) :
    InfinitePlace K → Matrix (Fin d) (Fin d) ℂ :=
  fun v => (((Real.sqrt (t v))⁻¹ : ℝ) : ℂ) • X v
end Defs
def KappaInvariance : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (D : ℕ), 0 < D →
    ∀ XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, (∀ v, IsUnit (XE v).det) →
    ∀ t : InfinitePlace K → ℝ, (∀ v, 0 < t v) →

      (∀ v, IsUnit (scaleFrame t XE v).det ∧
        ((scaleFrame t XE v)⁻¹).conjTranspose * (scaleFrame t XE v)⁻¹ =
          (t v : ℂ) • (((XE v)⁻¹).conjTranspose * (XE v)⁻¹)) ∧

      (∀ (d : ℕ) (XS : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (φ : Matrix (Fin D) (Fin d) K)
        (v : InfinitePlace K),
        detRatio XS (scaleFrame t XE) φ v = t v ^ d * detRatio XS XE φ v) ∧
      (∀ κ : InfinitePlace K → ℝ, (∀ v, 0 < κ v) →
        meanLog (fun v => t v * κ v) = meanLog t + meanLog κ) ∧

      (∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsLattice K R →
        lcv (scaleFrame t XE) R = lcv XE R + (D : ℝ) * meanLog t ∧
        Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame (scaleFrame t XE))
                  (Formalism.HN.dualLat R) =
          Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat R) +
            meanLog t ∧
        Formalism.HN.muDef (Pi.basisFun K (Fin D)) (scaleFrame t XE) R =
          Formalism.HN.muDef (Pi.basisFun K (Fin D)) XE R - meanLog t ∧
        Formalism.HN.muMaxDef (Pi.basisFun K (Fin D)) (scaleFrame t XE) R =
          Formalism.HN.muMaxDef (Pi.basisFun K (Fin D)) XE R - meanLog t) ∧

      (∀ (n : ℕ) (XN : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (XN v).det) →
        ∀ φ : (Fin n → K) →ₗ[K] Module.Dual K (Fin D → K), φ ≠ 0 →
        Formalism.HN.htMap (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis
                  (Formalism.HN.dualFrame (scaleFrame t XE)) φ =
          Formalism.HN.htMap (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis
            (Formalism.HN.dualFrame XE) φ - meanLog t)
def KappaNormalise : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (D : ℕ), 0 < D →
    ∀ XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, (∀ v, IsUnit (XE v).det) →
    ∀ κ : InfinitePlace K → ℝ, (∀ v, 0 < κ v) →
      (∀ v, IsUnit (scaleFrame (fun v => (κ v)⁻¹) XE v).det) ∧

      (∀ (XS : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (φ : Matrix (Fin D) (Fin D) K)
        (v : InfinitePlace K) (ρ P : ℝ), detRatio XS XE φ v = (κ v * ρ) ^ D * P →
        detRatio XS (scaleFrame (fun v => (κ v)⁻¹) XE) φ v = (1 * ρ) ^ D * P) ∧
      (∀ (XS : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (φ : Matrix (Fin D) (Fin D) K)
        (v : InfinitePlace K) (P : ℝ), detRatio XS XE φ v = κ v ^ D * P →
        detRatio XS (scaleFrame (fun v => (κ v)⁻¹) XE) φ v = (1 : ℝ) ^ D * P) ∧
      meanLog (fun _ : InfinitePlace K => (1 : ℝ)) = 0 ∧
      (∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsLattice K R →
        Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat R) =
          Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis
            (Formalism.HN.dualFrame (scaleFrame (fun v => (κ v)⁻¹) XE)) (Formalism.HN.dualLat R) + meanLog κ ∧
        Formalism.HN.muMaxDef (Pi.basisFun K (Fin D)) XE R =
          Formalism.HN.muMaxDef (Pi.basisFun K (Fin D)) (scaleFrame (fun v => (κ v)⁻¹) XE) R - meanLog κ ∧
        Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat R) +
                  Formalism.HN.muMaxDef (Pi.basisFun K (Fin D)) XE R =
          Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis
                    (Formalism.HN.dualFrame (scaleFrame (fun v => (κ v)⁻¹) XE)) (Formalism.HN.dualLat R) +
            Formalism.HN.muMaxDef (Pi.basisFun K (Fin D)) (scaleFrame (fun v => (κ v)⁻¹) XE) R ∧
        ∀ (n : ℕ) (XN : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (XN v).det) →
          ∀ φ : (Fin n → K) →ₗ[K] Module.Dual K (Fin D → K), φ ≠ 0 →
          Formalism.HN.htMap (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis
                    (Formalism.HN.dualFrame XE) φ =
            Formalism.HN.htMap (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis
              (Formalism.HN.dualFrame (scaleFrame (fun v => (κ v)⁻¹) XE)) φ - meanLog κ ∧
          Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat R) +
                    Formalism.HN.htMap (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis
                      (Formalism.HN.dualFrame XE) φ =
            Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis
                      (Formalism.HN.dualFrame (scaleFrame (fun v => (κ v)⁻¹) XE)) (Formalism.HN.dualLat R) +
              Formalism.HN.htMap (Pi.basisFun K (Fin n)) XN (Pi.basisFun K (Fin D)).dualBasis
                (Formalism.HN.dualFrame (scaleFrame (fun v => (κ v)⁻¹) XE)) φ)
end Formalism.DivisionValues


