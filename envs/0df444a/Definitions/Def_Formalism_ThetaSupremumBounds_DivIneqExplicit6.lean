-- Prove2me | Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqExplicit6
-- name    : Formalism_ThetaSupremumBounds_DivIneqExplicit6
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:04:32.668747+00:00
-- url     : https://prove2.me/theorems/214d816a-082f-460d-a4ee-8870f84db80e
-- title:
--   Div Ineq Explicit6
-- statement:
--   Definitions and structural lemmas for Div Ineq Explicit6, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/DivIneqExplicit6.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_StatementK
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementC
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped Real
noncomputable section
namespace Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
def liftedMapLogSize {J Pl Emb : Type} [Fintype Pl] {r : ℕ} (ν : J → Pl → Fin r → ℝ) (g0 : J → ℝ)
    (MainNotions : J → Emb → ℝ) (logOmτ : Pl → Emb → ℝ) (logth0 : Emb → ℝ) (logh logh' : J → ℝ) (v : ℝ)
    (j : J) (s : Emb) : ℝ :=
  (∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOmτ τ s)) +
      (Fintype.card Pl : ℝ) * g0 j * logth0 s +
      ((Fintype.card Pl : ℝ) * g0 j * Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) +
        2 * MainNotions j s + (∑ τ, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2))) +
        (logh j + logh' j))
def sizeB {J Pl : Type} [Fintype Pl] {r : ℕ} (ν : J → Pl → Fin r → ℝ)
    (logOm f m N L La C0 : ℝ) (j : J) : ℝ :=
  (∑ ρ, ((∑ i, ph (ν j ρ i)) - (∑ i, ν j ρ i) * logOm)) +
    C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L)
def DiHyp6 (J Pl : Type) [Fintype J] [Fintype Pl] (hK eK : J → ℝ) (phν nν : J → Pl → ℝ)
    (logOm f m N L La C0 : ℝ) : Prop :=
  (∀ j, hK j ≤ (∑ ρ, (phν j ρ - nν j ρ * logOm)) + eK j) ∧
  (∀ j, eK j ≤ C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L))
def StepDi6 : Prop :=
  ∀ (J Pl Emb : Type) [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb] (r : ℕ)
    (ν : J → Pl → Fin r → ℝ) (g0 : J → ℝ)
    (logK MainNotions : J → Emb → ℝ) (logOmτ : Pl → Emb → ℝ) (logth0 : Emb → ℝ) (logh logh' hK : J → ℝ)
    (logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0 : ℝ),

    (∀ j s, logK j s ≤ liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s) →

    (∀ j, hK j = (∑ s, logK j s) / (Fintype.card Emb : ℝ)) →

    (∀ τ, (∑ s, logOmτ τ s) / (Fintype.card Emb : ℝ) = logOm) →

    (∀ j s, MainNotions j s ≤ C2 * f * m ^ 2 * N ^ 2 * (logg + logT)) →
    (∑ s, logth0 s) / (Fintype.card Emb : ℝ) ≤ C3 * L →
    (∀ j, logh j ≤ C4 * f * N ^ 2 * (L + logT + logg)) →
    (∀ j, logh' j ≤ C4 * f * N ^ 2 * (L + logT + logg)) →

    (Fintype.card Pl : ℝ) ≤ f → (∀ j, 0 ≤ g0 j ∧ g0 j ≤ N ^ 2) →
    1 ≤ m → 1 ≤ N → 0 ≤ L → L ≤ La → 1 ≤ La →
    (∀ j, Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) ≤ c5 * La) →
    (∀ j τ, Real.log (2 * (∑ i, ν j τ i) + 2) ≤ c6 * La) →
    logT ≤ C7 * m * L → logg ≤ C8 * L →
    0 ≤ C2 → 0 ≤ C3 → 0 ≤ C4 → 0 ≤ c5 → 0 ≤ c6 → 0 ≤ C7 → 0 ≤ C8 →
    C3 + c5 + 2 * c6 + 1 + 2 * C2 * (C7 + C8) + 2 * C4 * (1 + C7 + C8) ≤ C0 →
    (∀ j, hK j ≤ sizeB ν logOm f m N L La C0 j) ∧
    ∃ eK : J → ℝ,
      DiHyp6 J Pl hK eK (fun j ρ => ∑ i, ph (ν j ρ i)) (fun j ρ => ∑ i, ν j ρ i) logOm f m N L La C0
def PerEmbedding6 : Prop :=
  ∀ (J Pl Emb : Type) [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb] (r : ℕ)
    (ν : J → Pl → Fin r → ℝ) (g0 : J → ℝ)
    (logK MainNotions : J → Emb → ℝ) (logOmτ : Pl → Emb → ℝ) (logth0 : Emb → ℝ) (logh logh' : J → ℝ)
    (logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0 : ℝ),
    (∀ j s, logK j s ≤ liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s) →
    (∀ τ, (∑ s, logOmτ τ s) / (Fintype.card Emb : ℝ) = logOm) →
    (∀ j s, MainNotions j s ≤ C2 * f * m ^ 2 * N ^ 2 * (logg + logT)) →
    (∑ s, logth0 s) / (Fintype.card Emb : ℝ) ≤ C3 * L →
    (∀ j, logh j ≤ C4 * f * N ^ 2 * (L + logT + logg)) →
    (∀ j, logh' j ≤ C4 * f * N ^ 2 * (L + logT + logg)) →
    (Fintype.card Pl : ℝ) ≤ f → (∀ j, 0 ≤ g0 j ∧ g0 j ≤ N ^ 2) →
    1 ≤ m → 1 ≤ N → 0 ≤ L → L ≤ La → 1 ≤ La →
    (∀ j, Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) ≤ c5 * La) →
    (∀ j τ, Real.log (2 * (∑ i, ν j τ i) + 2) ≤ c6 * La) →
    logT ≤ C7 * m * L → logg ≤ C8 * L →
    0 ≤ C2 → 0 ≤ C3 → 0 ≤ C4 → 0 ≤ c5 → 0 ≤ c6 → 0 ≤ C7 → 0 ≤ C8 →
    C3 + c5 + 2 * c6 + 1 + 2 * C2 * (C7 + C8) + 2 * C4 * (1 + C7 + C8) ≤ C0 →
    ∃ cst : J → ℝ, (∀ j, 0 ≤ cst j) ∧
      (∀ j s, logK j s ≤ liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + cst j) ∧
      (∀ j, (∑ s, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + cst j)) / (Fintype.card Emb : ℝ) =
        sizeB ν logOm f m N L La C0 j)
def HeightBound6 : Prop :=
  ∀ (J Pl Emb Frm : Type) [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb] [Fintype Frm]
    [Nonempty Frm] (r : ℕ)
    (ν : J → Pl → Fin r → ℝ) (g0 : J → ℝ) (logB logP : Emb → ℝ)
    (logK MainNotions : J → Emb → ℝ) (loglam : J → Frm → Emb → ℝ)
    (logOmτ : Pl → Emb → ℝ) (logth0 : Emb → ℝ) (logh logh' hlam : J → ℝ)
    (hP logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0 : ℝ),

    (∀ s, logB s ≤ logP s + (∑ j, logK j s) -
      Finset.univ.inf' Finset.univ_nonempty (fun y : Frm => ∑ j, loglam j y s)) →

    (∀ s, logP s ≤ hP) →
    (∀ j s, logK j s ≤ liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s) →
    (∀ j y s, hlam j ≤ loglam j y s) →

    (∀ τ, (∑ s, logOmτ τ s) / (Fintype.card Emb : ℝ) = logOm) →
    (∀ j s, MainNotions j s ≤ C2 * f * m ^ 2 * N ^ 2 * (logg + logT)) →
    (∑ s, logth0 s) / (Fintype.card Emb : ℝ) ≤ C3 * L →
    (∀ j, logh j ≤ C4 * f * N ^ 2 * (L + logT + logg)) →
    (∀ j, logh' j ≤ C4 * f * N ^ 2 * (L + logT + logg)) →
    (Fintype.card Pl : ℝ) ≤ f → (∀ j, 0 ≤ g0 j ∧ g0 j ≤ N ^ 2) →
    1 ≤ m → 1 ≤ N → 0 ≤ L → L ≤ La → 1 ≤ La →
    (∀ j, Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) ≤ c5 * La) →
    (∀ j τ, Real.log (2 * (∑ i, ν j τ i) + 2) ≤ c6 * La) →
    logT ≤ C7 * m * L → logg ≤ C8 * L →
    0 ≤ C2 → 0 ≤ C3 → 0 ≤ C4 → 0 ≤ c5 → 0 ≤ c6 → 0 ≤ C7 → 0 ≤ C8 →
    C3 + c5 + 2 * c6 + 1 + 2 * C2 * (C7 + C8) + 2 * C4 * (1 + C7 + C8) ≤ C0 →
    ∃ cst : J → ℝ, (∀ j, 0 ≤ cst j) ∧
      (∀ j, (∑ s, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + cst j)) / (Fintype.card Emb : ℝ) =
        sizeB ν logOm f m N L La C0 j) ∧
      (∀ s, logB s ≤
        hP + ∑ j, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + cst j - hlam j)) ∧
      ((∑ s, (hP + ∑ j, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + cst j - hlam j))) /
          (Fintype.card Emb : ℝ) =
        hP + ∑ j, (sizeB ν logOm f m N L La C0 j - hlam j)) ∧
      ((∑ s, logB s) / (Fintype.card Emb : ℝ) ≤ hP + ∑ j, (sizeB ν logOm f m N L La C0 j - hlam j))
def DivIneqExplicit6 : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)] (r : ℕ)
    (ν : J → Pl → Fin r → ℝ)
    (muC mu0 Fo hu hP mlam logT : ℝ) (aT : Pl → ℝ) (fa : J → Pl → ℝ)
    (x eps L b a rd La B0 Nc xe m f k N S tt η w'' b' lam0 C0 : ℝ)
    (Lpass Eb e6 eP logOm : ℝ) (pq : J → ℝ) (w eE δ : J → Pl → ℝ),
    muC ≤ mu0 + Lpass →
    mu0 ≤ (∑ j, ∑ ρ, pq j * w j ρ * logOm) + 2 * Fo + Eb →
    hu = hP + (∑ j, sizeB ν logOm f m N L La C0 j) - mlam →
    (∑ j, ∑ ρ, fa j ρ) - e6 ≤ mlam →
    hP ≤ -(∑ t ∈ TT, aT t * logT) + eP →
    (∀ j ρ, (∑ i, ph (ν j ρ i)) - fa j ρ ≤ (if ρ ∈ TT then ph (aT ρ) else 0) + eE j ρ) →
    (∀ j ρ, (∑ i, ν j ρ i) = (if ρ ∈ TT then aT ρ else 0) + k * w j ρ + δ j ρ) →
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
    Eb ≤ C0 * m * xe * (B0 + Nc) →
    e6 ≤ C0 * m * f * N ^ 2 * La →
    eP ≤ C0 * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La →
    (∀ j ρ, eE j ρ ≤ C0 * (w j ρ + S + N ^ 2 + m * (tt + 1) * η) * La) →
    (∀ j ρ, |δ j ρ| ≤
      C0 * (w j ρ + k * (N + S) + m * (tt + 1) * η + (if ρ ∈ TT then k * b' else 0))) →
      muC + hu - 2 * Fo ≤
        (∑ t ∈ TT, (m * (ph (aT t) - aT t * logOm) - aT t * logT)) +
        (50 * C0 + 10) * ((TT.card : ℝ) * a * La + m * (B0 + Nc) * xe)
def DivIneqTwoConst6 : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)] (r : ℕ)
    (ν : J → Pl → Fin r → ℝ)
    (muC mu0 Fo hu hP mlam logT : ℝ) (aT : Pl → ℝ) (fa : J → Pl → ℝ)
    (x eps L b a rd La B0 Nc m f k N S tt η w'' b' lam0 C0 c : ℝ)
    (Lpass Eb e6 eP logOm : ℝ) (pq : J → ℝ) (w eE δ : J → Pl → ℝ),
    muC ≤ mu0 + Lpass →
    mu0 ≤ (∑ j, ∑ ρ, pq j * w j ρ * logOm) + 2 * Fo + Eb →
    hu = hP + (∑ j, sizeB ν logOm f m N L La C0 j) - mlam →
    (∑ j, ∑ ρ, fa j ρ) - e6 ≤ mlam →
    hP ≤ -(∑ t ∈ TT, aT t * logT) + eP →
    (∀ j ρ, (∑ i, ph (ν j ρ i)) - fa j ρ ≤ (if ρ ∈ TT then ph (aT ρ) else 0) + eE j ρ) →
    (∀ j ρ, (∑ i, ν j ρ i) = (if ρ ∈ TT then aT ρ else 0) + k * w j ρ + δ j ρ) →
    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → a = x * b →
    1 ≤ rd → Real.log rd ≤ L → Real.log x ≤ L → La = Real.log (a * rd) →
    B0 = f * m * b * x ^ eps → 0 ≤ Nc →
    (Fintype.card J : ℝ) = m → (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f →
    1 ≤ k → 1 ≤ N → 0 ≤ S → 0 ≤ tt → 0 ≤ η →
    (∀ j ρ, 0 ≤ w j ρ ∧ w j ρ ≤ 2 * b) →
    (∀ j, |pq j - k| ≤ m) → |logOm| ≤ La →
    lam0 ≤ b → N ^ 2 ≤ b → m ^ 3 * N ^ 2 * L ≤ b → m * η * N * L ≤ b → k * N ≤ b →
    k * S ≤ w'' → m * (tt + 1) * η ≤ w'' → N * w'' ≤ b → b' * N ≤ a → m * k * b' ≤ a →
    1 ≤ C0 → C0 ≤ c →
    Lpass ≤ 1 + C0 * lam0 →
    Eb ≤ c * m * x ^ eps * (B0 + Nc) →
    e6 ≤ C0 * m * f * N ^ 2 * La →
    eP ≤ C0 * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La →
    (∀ j ρ, eE j ρ ≤ C0 * (w j ρ + S + N ^ 2 + m * (tt + 1) * η) * La) →
    (∀ j ρ, |δ j ρ| ≤
      C0 * (w j ρ + k * (N + S) + m * (tt + 1) * η + (if ρ ∈ TT then k * b' else 0))) →
      muC + hu - 2 * Fo ≤
        (∑ t ∈ TT, (m * (ph (aT t) - aT t * logOm) - aT t * logT)) +
        (50 * C0 + 10) * ((TT.card : ℝ) * a * La) + 60 * c * (m * (B0 + Nc) * x ^ eps)
def StepDiProd6 : Prop :=
  ∀ (J Pl Emb : Type) [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb] (r : ℕ)
    (ν : J → Pl → Fin r → ℝ) (n : J → Pl → ℕ) (g0 : J → ℕ)
    (Ksq kc : J → Emb → ℝ) (Om : Pl → Emb → ℝ) (th0sq : Emb → ℝ) (hcl hcl' hK : J → ℝ)
    (logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0 : ℝ),
    (∀ j τ, ∑ i, ν j τ i = (n j τ : ℝ)) →
    (∀ j s, 0 < Ksq j s) → (∀ j s, 0 < kc j s) → (∀ τ s, 0 < Om τ s) → (∀ s, 0 < th0sq s) →
    (∀ j, 0 < hcl j) → (∀ j, 0 < hcl' j) → 0 < v →

    (∀ j s, Ksq j s ≤ (hcl j * hcl' j) *
      ((kc j s ^ 2 * (8 + 32 * ((Fintype.card Pl * g0 j : ℕ) : ℝ) * v) ^ (Fintype.card Pl * g0 j) *
          th0sq s ^ (Fintype.card Pl * g0 j)) *
        ∏ τ, ((Om τ s)⁻¹ ^ n j τ *
          (Real.exp 1 * (2 * (n j τ : ℝ) + 2) ^ (2 * g0 j) * Real.exp (∑ i, ph (ν j τ i)))))) →
    (∀ j, hK j = (∑ s, Real.log (Ksq j s)) / (Fintype.card Emb : ℝ)) →
    (∀ τ, (∑ s, Real.log (Om τ s)) / (Fintype.card Emb : ℝ) = logOm) →
    (∀ j s, Real.log (kc j s) ≤ C2 * f * m ^ 2 * N ^ 2 * (logg + logT)) →
    (∑ s, Real.log (th0sq s)) / (Fintype.card Emb : ℝ) ≤ C3 * L →
    (∀ j, Real.log (hcl j) ≤ C4 * f * N ^ 2 * (L + logT + logg)) →
    (∀ j, Real.log (hcl' j) ≤ C4 * f * N ^ 2 * (L + logT + logg)) →
    (Fintype.card Pl : ℝ) ≤ f → (∀ j, (g0 j : ℝ) ≤ N ^ 2) →
    1 ≤ m → 1 ≤ N → 0 ≤ L → L ≤ La → 1 ≤ La →
    (∀ j, Real.log (8 + 32 * ((Fintype.card Pl * g0 j : ℕ) : ℝ) * v) ≤ c5 * La) →
    (∀ j τ, Real.log (2 * (n j τ : ℝ) + 2) ≤ c6 * La) →
    logT ≤ C7 * m * L → logg ≤ C8 * L →
    0 ≤ C2 → 0 ≤ C3 → 0 ≤ C4 → 0 ≤ c5 → 0 ≤ c6 → 0 ≤ C7 → 0 ≤ C8 →
    C3 + c5 + 2 * c6 + 1 + 2 * C2 * (C7 + C8) + 2 * C4 * (1 + C7 + C8) ≤ C0 →
    (∀ j, hK j ≤ sizeB ν logOm f m N L La C0 j) ∧
    ∃ eK : J → ℝ,
      DiHyp6 J Pl hK eK (fun j ρ => ∑ i, ph (ν j ρ i)) (fun j ρ => ∑ i, ν j ρ i) logOm f m N L La C0
def LiftStepDi6 : Prop :=
  ∀ (J Pl Emb : Type) [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb]
    (ι Cl Cl' : J → Type) [∀ j, Fintype (ι j)] [∀ j, Fintype (Cl j)] [∀ j, Fintype (Cl' j)]
    [∀ j, Nonempty (Cl j)] [∀ j, Nonempty (Cl' j)]
    (A B : J → Emb → Type)
    [∀ j σ, NormedAddCommGroup (A j σ)] [∀ j σ, NormedSpace ℂ (A j σ)]
    [∀ j σ, NormedAddCommGroup (B j σ)] [∀ j σ, NormedSpace ℂ (B j σ)] [∀ j σ, CompleteSpace (B j σ)]
    (r : ℕ) (ν : J → Pl → Fin r → ℝ) (n : J → Pl → ℕ)
    (s : ∀ j, Emb → Pl → (ι j → ℂ) → Fin r → ℝ)
    (Th : ∀ j, Emb → Cl j → Cl' j → (Pl × ι j → ℂ) → ℂ)
    (c : ∀ j, Emb → Cl j → Cl' j → (Pl × ι j → ℕ) → ℂ)
    (Rc : ∀ j σ, (Pl × ι j → ℕ) →₀ (A j σ →L[ℂ] B j σ))
    (lam : Pl → Emb → ℂ) (Om : Pl → Emb → ℝ) (S kc : J → Emb → ℝ) (th0sq : Emb → ℝ)
    (γ : ∀ j, Cl j → ℝ) (γ' : ∀ j, Cl' j → ℝ) (ε : ∀ j, Emb → Cl j → Cl' j → ℂ) (hK : J → ℝ)
    (logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0 : ℝ),

    (∀ j τ i, 0 ≤ ν j τ i) → (∀ j τ, ∑ i, ν j τ i = (n j τ : ℝ)) →
    (∀ j σ τ u i, 0 ≤ s j σ τ u i) → (∀ j σ τ u, ∑ i, s j σ τ u i ^ 2 = nsq u) →
    (∀ j σ L L', Continuous (Th j σ L L')) →
    (∀ j σ L L' u, HasSum (fun e => c j σ L L' e * mono u e) (Th j σ L L' u)) →
    (∀ j σ L L' u, ‖Th j σ L L' u‖ ≤ S j σ * Real.exp (nsq u / 2)) →
    (∀ j σ, ∀ e ∈ (Rc j σ).support, ∀ τ, ∑ x, e (τ, x) = n j τ) →
    (∀ j σ u, ‖(Rc j σ).sum (fun e X => mono (cj u) e • X)‖ ≤
      ∏ τ, ∏ i, s j σ τ (fun x => u (τ, x)) i ^ ν j τ i) →
    (∀ τ σ, 0 < Om τ σ) → (∀ τ σ, ‖lam τ σ‖ ^ 2 = (Om τ σ)⁻¹) →
    (∀ j L, 0 < γ j L ∧ γ j L ≤ 1) → (∀ j L', 0 < γ' j L' ∧ γ' j L' ≤ 1) →
    (∀ j σ L L', ‖ε j σ L L'‖ = 1) →
    (∀ j σ, S j σ ^ 2 = kc j σ ^ 2 *
      (8 + 32 * ((Fintype.card Pl * Fintype.card (ι j) : ℕ) : ℝ) * v) ^ (Fintype.card Pl * Fintype.card (ι j)) *
      th0sq σ ^ (Fintype.card Pl * Fintype.card (ι j))) →

    (∀ j σ, 0 < liftNormSq (γ j) (γ' j) (ε j σ)
      (fun L L' => liftBlock (c j σ L L') (Rc j σ) (fun τ => lam τ σ))) →
    (∀ j σ, 0 < kc j σ) → (∀ σ, 0 < th0sq σ) → 0 < v →
    (∀ j, hK j = (∑ σ, Real.log (liftNormSq (γ j) (γ' j) (ε j σ)
      (fun L L' => liftBlock (c j σ L L') (Rc j σ) (fun τ => lam τ σ)))) / (Fintype.card Emb : ℝ)) →
    (∀ τ, (∑ σ, Real.log (Om τ σ)) / (Fintype.card Emb : ℝ) = logOm) →
    (∀ j σ, Real.log (kc j σ) ≤ C2 * f * m ^ 2 * N ^ 2 * (logg + logT)) →
    (∑ σ, Real.log (th0sq σ)) / (Fintype.card Emb : ℝ) ≤ C3 * L →
    (∀ j, Real.log (Fintype.card (Cl j) : ℝ) ≤ C4 * f * N ^ 2 * (L + logT + logg)) →
    (∀ j, Real.log (Fintype.card (Cl' j) : ℝ) ≤ C4 * f * N ^ 2 * (L + logT + logg)) →
    (Fintype.card Pl : ℝ) ≤ f → (∀ j, (Fintype.card (ι j) : ℝ) ≤ N ^ 2) →
    1 ≤ m → 1 ≤ N → 0 ≤ L → L ≤ La → 1 ≤ La →
    (∀ j, Real.log (8 + 32 * ((Fintype.card Pl * Fintype.card (ι j) : ℕ) : ℝ) * v) ≤ c5 * La) →
    (∀ j τ, Real.log (2 * (n j τ : ℝ) + 2) ≤ c6 * La) →
    logT ≤ C7 * m * L → logg ≤ C8 * L →
    0 ≤ C2 → 0 ≤ C3 → 0 ≤ C4 → 0 ≤ c5 → 0 ≤ c6 → 0 ≤ C7 → 0 ≤ C8 →
    C3 + c5 + 2 * c6 + 1 + 2 * C2 * (C7 + C8) + 2 * C4 * (1 + C7 + C8) ≤ C0 →
    ∀ j, hK j ≤ sizeB ν logOm f m N L La C0 j
def TopNet6 : Prop :=
  ∀ k m j p q' : ℝ, 1 ≤ j → j ≤ m → p = k + j - 1 → q' = m - j →
    (-k + p - q' = 2 * j - 1 - m ∧ |2 * j - 1 - m| ≤ m) ∧
    (-(k - 1) + p - q' = 2 * j - m ∧ |2 * j - m| ≤ m)
def FlatLineDegree6 : Prop :=
  ∀ p q' logOm lrdK lrdE dfl c1 : ℝ, 0 ≤ q' → 0 ≤ lrdK → lrdK ≤ lrdE →
    dfl = p / 2 * logOm + q' * (-(1 / 2) * logOm + 2 * lrdK - lrdE) → c1 = -dfl →
    2 * dfl = (p - q') * logOm + 2 * q' * (2 * lrdK - lrdE) ∧
    c1 + (p - q') * logOm / 2 = -(q' * (2 * lrdK - lrdE)) ∧
    |2 * lrdK - lrdE| ≤ lrdE ∧
    |c1 + (p - q') * logOm / 2| ≤ q' * lrdE
def MeanDev6 : Prop :=
  ∀ (Emb : Type) [Fintype Emb] [Nonempty Emb] (φ : Emb → ℝ) (C0 M : ℝ),
    (∀ s, -C0 ≤ φ s) → M = (∑ s, φ s) / (Fintype.card Emb : ℝ) →
    (∑ s, |φ s - M|) / (Fintype.card Emb : ℝ) ≤ 2 * (M + C0)
def recordA {Pl : Type} (TT : Finset Pl) (aT : Pl → ℝ) (logT f m N S η b' La C : ℝ) : ℝ :=
  -(∑ t ∈ TT, aT t * logT) + C * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La
def recordX {J Pl : Type} [Fintype Pl] (logH : J → Pl → ℝ) (f nV L' C : ℝ) (j : J) : ℝ :=
  (∑ ρ, logH j ρ) - C * f * nV ^ 2 * L'
def recordHu {J Pl : Type} [Fintype J] [Fintype Pl] (TT : Finset Pl) {r : ℕ}
    (ν : J → Pl → Fin r → ℝ) (aT : Pl → ℝ) (logH : J → Pl → ℝ)
    (logT logOm f m N S η b' nV L La L' C : ℝ) : ℝ :=
  recordA TT aT logT f m N S η b' La C + (∑ j, sizeB ν logOm f m N L La C j) -
    (∑ j, recordX logH f nV L' C j)
def HeightRecord6 : Prop :=
  ∀ (J Pl Emb Frm : Type) [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb] [Fintype Frm]
    [Nonempty Frm] (TT : Finset Pl) (r : ℕ)
    (ν : J → Pl → Fin r → ℝ) (g0 : J → ℝ) (logB logP : Emb → ℝ)
    (logK MainNotions : J → Emb → ℝ) (loglam : J → Frm → Emb → ℝ)
    (logOmτ : Pl → Emb → ℝ) (logth0 : Emb → ℝ) (logh logh' : J → ℝ) (aT : Pl → ℝ) (logH : J → Pl → ℝ)
    (logOm v f m N S η b' nV L La L' logT logg C2 C3 C4 c5 c6 C7 C8 C : ℝ),
    (∀ s, logB s ≤ logP s + (∑ j, logK j s) -
      Finset.univ.inf' Finset.univ_nonempty (fun y : Frm => ∑ j, loglam j y s)) →
    (∀ s, logP s ≤ recordA TT aT logT f m N S η b' La C) →
    (∀ j s, logK j s ≤ liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s) →
    (∀ j y s, recordX logH f nV L' C j ≤ loglam j y s) →
    (∀ τ, (∑ s, logOmτ τ s) / (Fintype.card Emb : ℝ) = logOm) →
    (∀ j s, MainNotions j s ≤ C2 * f * m ^ 2 * N ^ 2 * (logg + logT)) →
    (∑ s, logth0 s) / (Fintype.card Emb : ℝ) ≤ C3 * L →
    (∀ j, logh j ≤ C4 * f * N ^ 2 * (L + logT + logg)) →
    (∀ j, logh' j ≤ C4 * f * N ^ 2 * (L + logT + logg)) →
    (Fintype.card Pl : ℝ) ≤ f → (∀ j, 0 ≤ g0 j ∧ g0 j ≤ N ^ 2) →
    1 ≤ m → 1 ≤ N → 0 ≤ L → L ≤ La → 1 ≤ La →
    (∀ j, Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) ≤ c5 * La) →
    (∀ j τ, Real.log (2 * (∑ i, ν j τ i) + 2) ≤ c6 * La) →
    logT ≤ C7 * m * L → logg ≤ C8 * L →
    0 ≤ C2 → 0 ≤ C3 → 0 ≤ C4 → 0 ≤ c5 → 0 ≤ c6 → 0 ≤ C7 → 0 ≤ C8 →
    C3 + c5 + 2 * c6 + 1 + 2 * C2 * (C7 + C8) + 2 * C4 * (1 + C7 + C8) ≤ C →
    ∃ logc : Emb → ℝ, (∀ s, logB s ≤ logc s) ∧
      ((∑ s, logc s) / (Fintype.card Emb : ℝ) =
        recordHu TT ν aT logH logT logOm f m N S η b' nV L La L' C) ∧
      ((∑ s, logB s) / (Fintype.card Emb : ℝ) ≤
        recordHu TT ν aT logH logT logOm f m N S η b' nV L La L' C)
def DivIneqRecord6 : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)] (r : ℕ)
    (ν : J → Pl → Fin r → ℝ)
    (muC mu0 Fo logT : ℝ) (aT : Pl → ℝ) (logH : J → Pl → ℝ)
    (x eps L b a rd La L' B0 Nc xe m f k N nV S tt η w'' b' lam0 C C0 : ℝ)
    (Lpass Eb logOm : ℝ) (pq : J → ℝ) (w eE δ : J → Pl → ℝ),
    muC ≤ mu0 + Lpass →
    mu0 ≤ (∑ j, ∑ ρ, pq j * w j ρ * logOm) + 2 * Fo + Eb →
    (∀ j ρ, (∑ i, ph (ν j ρ i)) - logH j ρ ≤ (if ρ ∈ TT then ph (aT ρ) else 0) + eE j ρ) →
    (∀ j ρ, (∑ i, ν j ρ i) = (if ρ ∈ TT then aT ρ else 0) + k * w j ρ + δ j ρ) →
    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → a = x * b →
    1 ≤ rd → Real.log rd ≤ L → Real.log x ≤ L → La = Real.log (a * rd) →
    B0 = f * m * b * x ^ eps → 0 ≤ Nc → x ^ eps ≤ xe →
    (Fintype.card J : ℝ) = m → (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f →
    1 ≤ k → 1 ≤ N → 0 ≤ S → 0 ≤ tt → 0 ≤ η → 0 ≤ b' →
    (∀ j ρ, 0 ≤ w j ρ ∧ w j ρ ≤ 2 * b) →
    (∀ j, |pq j - k| ≤ m) → |logOm| ≤ La →
    lam0 ≤ b → N ^ 2 ≤ b → m ^ 3 * N ^ 2 * L ≤ b → m * η * N * L ≤ b → k * N ≤ b →
    k * S ≤ w'' → m * (tt + 1) * η ≤ w'' → N * w'' ≤ b → b' * N ≤ a → m * k * b' ≤ a →
    0 ≤ C → C ≤ C0 → 0 ≤ nV → nV ≤ N → 0 ≤ L' → C * L' ≤ C0 * La →
    Lpass ≤ 1 + C0 * lam0 →
    Eb ≤ C0 * m * xe * (B0 + Nc) →
    (∀ j ρ, eE j ρ ≤ C0 * (w j ρ + S + N ^ 2 + m * (tt + 1) * η) * La) →
    (∀ j ρ, |δ j ρ| ≤
      C0 * (w j ρ + k * (N + S) + m * (tt + 1) * η + (if ρ ∈ TT then k * b' else 0))) →
      muC + recordHu TT ν aT logH logT logOm f m N S η b' nV L La L' C - 2 * Fo ≤
        (∑ t ∈ TT, (m * (ph (aT t) - aT t * logOm) - aT t * logT)) +
        (50 * C0 + 10) * ((TT.card : ℝ) * a * La + m * (B0 + Nc) * xe)
def WeightSize6 : Prop :=
  ∀ k m t N S Sc w η : ℝ, 1 ≤ k → 0 ≤ m → 0 ≤ t → N = k + m * (t + 1) → 0 ≤ S → S ≤ Sc →
    (k - 1) * (S + N + t + 1) + m * (w + η + 1) ≤ m * w + m * η + k * Sc + (N + t) ^ 2 + m
def DivIneqFine6 : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)] (r : ℕ)
    (ν : J → Pl → Fin r → ℝ)
    (muC mu0 Fo hu hP mlam logT : ℝ) (aT : Pl → ℝ) (fa : J → Pl → ℝ)
    (x eps L b a rd La B0 Nc m f k N S tt η w'' b' lam0 C0 c : ℝ)
    (Lpass Eb e6 eP logOm : ℝ) (pq : J → ℝ) (w eE δ : J → Pl → ℝ),
    muC ≤ mu0 + Lpass →
    mu0 ≤ (∑ j, ∑ ρ, pq j * w j ρ * logOm) + 2 * Fo + Eb →
    hu = hP + (∑ j, sizeB ν logOm f m N L La C0 j) - mlam →
    (∑ j, ∑ ρ, fa j ρ) - e6 ≤ mlam →
    hP ≤ -(∑ t ∈ TT, aT t * logT) + eP →
    (∀ j ρ, (∑ i, ph (ν j ρ i)) - fa j ρ ≤ (if ρ ∈ TT then ph (aT ρ) else 0) + eE j ρ) →
    (∀ j ρ, (∑ i, ν j ρ i) = (if ρ ∈ TT then aT ρ else 0) + k * w j ρ + δ j ρ) →
    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → a = x * b →
    1 ≤ rd → Real.log rd ≤ L → Real.log x ≤ L → La = Real.log (a * rd) →
    B0 = f * m * b * x ^ eps → 0 ≤ Nc →
    (Fintype.card J : ℝ) = m → (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f →
    1 ≤ k → 1 ≤ N → 0 ≤ S → 0 ≤ tt → 0 ≤ η →
    (∀ j ρ, 0 ≤ w j ρ ∧ w j ρ ≤ 2 * b) →
    (∀ j, |pq j - k| ≤ m) → |logOm| ≤ La →
    lam0 ≤ b → N ^ 2 ≤ b → m ^ 3 * N ^ 2 * L ≤ b → m * η * N * L ≤ b → k * N ≤ b →
    k * S ≤ w'' → m * (tt + 1) * η ≤ w'' → N * w'' ≤ b → b' * N ≤ a → m * k * b' ≤ a →
    0 ≤ C0 →
    Lpass ≤ 1 + C0 * lam0 →
    Eb ≤ c * (m * (x ^ eps * B0 + Real.log x ^ 2 * Nc)) →
    e6 ≤ C0 * m * f * N ^ 2 * La →
    eP ≤ C0 * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La →
    (∀ j ρ, eE j ρ ≤ C0 * (w j ρ + S + N ^ 2 + m * (tt + 1) * η) * La) →
    (∀ j ρ, |δ j ρ| ≤
      C0 * (w j ρ + k * (N + S) + m * (tt + 1) * η + (if ρ ∈ TT then k * b' else 0))) →
      muC + hu - 2 * Fo ≤
        (∑ t ∈ TT, (m * (ph (aT t) - aT t * logOm) - aT t * logT)) +
        (50 * C0 + 10) * ((TT.card : ℝ) * a * La) +
        (50 * C0 + 10 + c) * (m * (x ^ eps * B0 + Real.log x ^ 2 * Nc))
end Formalism.DimensionVariation


