-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRowsShift
-- name    : Formalism_QuotientMetricDivisors_TheoremDivIneqRowsShift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:10:07.455297+00:00
-- url     : https://prove2.me/theorems/08e53ff1-a0bb-41fe-a526-af980a4ca7a2
-- title:
--   Theorem Div Ineq Rows Shift
-- statement:
--   Definitions and structural lemmas for Theorem Div Ineq Rows Shift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/TheoremDivIneqRowsShift.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRows
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.DivisionValues
def RowsTopExactRow : Prop :=
  ∀ (n aT w s : ℕ) (S Bl sh : ℝ) (ν ap : Multiset ℕ),
    0 < s → s ≤ aT + w → (∀ y ∈ ν, y ≤ aT + w - s) → ¬ IsRowsTop n aT w S Bl sh ν ap
def RowsOffLongRows : Prop :=
  ∀ (n w : ℕ) (S Bl sh : ℝ) (ν ap : Multiset ℕ),
    IsRowsOff n w S Bl sh ν ap → n + 1 ≤ Multiset.card (ν.filter (w ≤ ·))
def RowsStepEShift : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
    (n : ℕ) (aT : Pl → ℕ) (w wr : J → Pl → ℕ) (ν ap : J → Pl → Multiset ℕ) (fa : J → Pl → ℝ)
    (a rd La k N S Sc t η m b' cs C1 C0 : ℝ),

    La = Real.log (a * rd) → 1 ≤ La → k = (n : ℝ) + 2 → k ≤ N → 0 ≤ b' → 0 ≤ cs → 0 ≤ S →

    2 ≤ C1 → cs + 1 ≤ C1 → 2 * Sc ≤ C1 * S → C1 + cs ≤ C0 →

    (∀ j ρ, wr j ρ ≤ w j ρ) → (∀ j ρ, (w j ρ : ℝ) - (wr j ρ : ℝ) ≤ cs * N) →

    (∀ j ρ, (w j ρ : ℝ) + Sc ≤ a * rd) → m * (t + 1) * η ≤ a * rd → 0 ≤ m * (t + 1) * η →
    (∀ j, ∀ ρ ∈ TT, (aT ρ : ℝ) + (w j ρ : ℝ) ≤ a * rd) →

    (∀ j ρ, logFactRows (ap j ρ) ≤ fa j ρ) →

    (∀ j, ∀ ρ, ρ ∉ TT →
      IsRowsOff (n + 1) (wr j ρ) Sc (m * (t + 1) * η) (cs * N) (ν j ρ) (ap j ρ)) →
    (∀ j, ∀ ρ ∈ TT,
      IsRowsTop n (aT ρ) (wr j ρ) Sc (m * (t + 1) * η) (cs * N) (ν j ρ) (ap j ρ)) →
    ∃ eE δ : J → Pl → ℝ,
      (∀ j ρ, phRows (ν j ρ) - fa j ρ ≤
        (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (aT ρ : ℝ) else 0) + eE j ρ) ∧
      (∀ j ρ, ((ν j ρ).sum : ℝ) = (if ρ ∈ TT then (aT ρ : ℝ) else 0) + k * (w j ρ : ℝ) + δ j ρ) ∧
      (∀ j ρ, eE j ρ ≤ C0 * ((w j ρ : ℝ) + S + N ^ 2 + m * (t + 1) * η) * La) ∧
      (∀ j ρ, |δ j ρ| ≤
        C0 * ((w j ρ : ℝ) + k * (N + S) + m * (t + 1) * η + (if ρ ∈ TT then k * b' else 0)))
def TheoremDivIneqRowsShift : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]

    (muC mu0 Fo hu hP mlam logT : ℝ) (hK : J → ℝ) (fa : J → Pl → ℝ)

    (n : ℕ) (aT : Pl → ℕ) (w wr : J → Pl → ℕ) (ν ap : J → Pl → Multiset ℕ)

    (x eps L b a rd La B0 Nc xe m f k N S Sc cs tt η w'' b' dC lam0 C1 C0 : ℝ)

    (Lpass Eb e6 eP logOm : ℝ) (eK pq : J → ℝ),

    muC ≤ mu0 + Lpass →
    mu0 ≤ ∑ j, ∑ ρ, pq j * (w j ρ : ℝ) * logOm + 2 * Fo + Eb →
    hu = hP + ∑ j, hK j - mlam →
    (∀ j, hK j ≤ ∑ ρ, (phRows (ν j ρ) - ((ν j ρ).sum : ℝ) * logOm) + eK j) →
    ∑ j, ∑ ρ, fa j ρ - e6 ≤ mlam →
    hP ≤ -(∑ t ∈ TT, (aT t : ℝ) * logT) + eP →

    k = (n : ℝ) + 2 → k ≤ N → 0 ≤ b' → 0 ≤ cs → 2 ≤ C1 → cs + 1 ≤ C1 → 2 * Sc ≤ C1 * S → C1 + cs ≤ C0 →
    (∀ j ρ, wr j ρ ≤ w j ρ) → (∀ j ρ, (w j ρ : ℝ) - (wr j ρ : ℝ) ≤ cs * N) →
    (∀ j ρ, (w j ρ : ℝ) + Sc ≤ a * rd) →
    (∀ j, ∀ ρ ∈ TT, (aT ρ : ℝ) + (w j ρ : ℝ) ≤ a * rd) →
    (∀ j ρ, logFactRows (ap j ρ) ≤ fa j ρ) →
    (∀ j, ∀ ρ, ρ ∉ TT →
      IsRowsOff (n + 1) (wr j ρ) Sc (m * (tt + 1) * η) (cs * N) (ν j ρ) (ap j ρ)) →
    (∀ j, ∀ ρ ∈ TT,
      IsRowsTop n (aT ρ) (wr j ρ) Sc (m * (tt + 1) * η) (cs * N) (ν j ρ) (ap j ρ)) →

    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → a = x * b →

    1 ≤ rd → Real.log rd ≤ L → Real.log x ≤ L → La = Real.log (a * rd) →

    B0 = f * m * b * x ^ eps → 0 ≤ Nc → x ^ eps ≤ xe →

    (Fintype.card J : ℝ) = m → (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f →

    0 ≤ S → 0 ≤ tt → 0 ≤ η → 1 ≤ dC →

    (∀ j ρ, (w j ρ : ℝ) ≤ 2 * b) →

    (∀ j, |pq j - k| ≤ m) → |logOm| ≤ La →

    lam0 ≤ b → N ^ 2 * dC ≤ b → m ^ 3 * N ^ 2 * L ≤ b → m * η * N * L ≤ b → k * N ≤ b →
    k * S ≤ w'' → m * (tt + 1) * η ≤ w'' → N * w'' ≤ b → b' * N ≤ a → m * k * b' ≤ a →

    Lpass ≤ 1 + C0 * lam0 →
    Eb ≤ C0 * m * xe * (B0 + Nc) →
    (∀ j, eK j ≤ C0 * (f * N ^ 2 * (La + dC) + f * m ^ 3 * N ^ 2 * L)) →
    e6 ≤ C0 * m * f * N ^ 2 * La →
    eP ≤ C0 * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La →
      muC + hu - 2 * Fo ≤
        ∑ t ∈ TT, (m * (Formalism.LatticeIndexTer.ph (aT t : ℝ) - (aT t : ℝ) * logOm) - (aT t : ℝ) * logT) +
        (50 * C0 + 10) * ((TT.card : ℝ) * a * La + m * (B0 + Nc) * xe)
def originRow (k t j w u i : ℝ) : ℝ :=
  (u + w) - ((k + (j - 1) * (t + 1)) + (k + j * (t + 1)) + 1 - 2 * i) / 2
def originBig (k m t j w v i : ℝ) : ℝ :=
  (v + w) - (((k - 1 + m) + t) + 1 - 2 * i) / 2 - ((k - 1 + j) - (m - j)) / 2
def RowsOriginOff : Prop :=
  ∀ (n j t w s wr : ℕ) (m Sc Bl sh : ℝ) (u : Fin (n + 2) → ℝ) (v : Fin (n + 1) → ℝ)
    (νr : Fin (n + 2) → ℕ) (ar : Fin (n + 1) → ℕ) (blk sm : Multiset ℕ),
    1 ≤ j → (s : ℝ) = (((n : ℝ) + 2) + (2 * (j : ℝ) - 1) * ((t : ℝ) + 1)) / 2 → wr + s = w →
    (∀ i, (νr i : ℝ) = originRow ((n : ℝ) + 2) t j w (u i) ((i : ℕ) + 1)) →
    (∀ i, (ar i : ℝ) = originBig ((n : ℝ) + 2) m t j w (v i) ((i : ℕ) + 1)) →
    (∀ i : Fin (n + 1), v i < u i.castSucc ∧ u i.succ < v i) →
    0 ≤ u (Fin.last (n + 1)) + (((n : ℝ) + 2) - 1) / 2 → u 0 - (((n : ℝ) + 2) - 1) / 2 ≤ Sc →
    ((j : ℝ) - 1) * (t : ℝ) ≤ sh → (blk.sum : ℝ) ≤ Bl →
      IsRowsOff (n + 1) wr Sc Bl sh (Finset.univ.val.map νr + blk) (Finset.univ.val.map ar + sm)
def RowsOriginTop : Prop :=
  ∀ (n j t w s wr aT bT : ℕ) (m Sc Bl sh : ℝ) (u : Fin (n + 2) → ℝ) (v : Fin (n + 1) → ℝ)
    (νr : Fin (n + 2) → ℕ) (ar : Fin (n + 1) → ℕ) (blk sm : Multiset ℕ),
    1 ≤ j → (s : ℝ) = (((n : ℝ) + 2) + (2 * (j : ℝ) - 1) * ((t : ℝ) + 1)) / 2 → wr + s = w →
    (∀ i, (νr i : ℝ) = originRow ((n : ℝ) + 2) t j w (u i) ((i : ℕ) + 1)) →
    (∀ i, (ar i : ℝ) = originBig ((n : ℝ) + 2) m t j w (v i) ((i : ℕ) + 1)) →
    (∀ i : Fin (n + 1), v i < u i.castSucc ∧ u i.succ < v i) →
    u 0 = (aT : ℝ) + (((n : ℝ) + 2) - 1) / 2 → u (Fin.last (n + 1)) = -(bT : ℝ) - (((n : ℝ) + 2) - 1) / 2 →
    0 ≤ v (Fin.last n) + (((n : ℝ) + 2) - 2) / 2 → v 0 - (((n : ℝ) + 2) - 2) / 2 ≤ Sc →
    ((j : ℝ) - 1) * (t : ℝ) ≤ sh → (blk.sum : ℝ) ≤ Bl →
      IsRowsTop n aT wr Sc Bl sh (Finset.univ.val.map νr + blk) (Finset.univ.val.map ar + sm)
def RowsStepEOrigin : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
    (n t : ℕ) (jj s : J → ℕ) (aT bT : Pl → ℕ) (w : J → Pl → ℕ)
    (u : Pl → Fin (n + 2) → ℝ) (v : Pl → Fin (n + 1) → ℝ)
    (νr : J → Pl → Fin (n + 2) → ℕ) (ar : J → Pl → Fin (n + 1) → ℕ) (blk sm : J → Pl → Multiset ℕ)
    (ν ap : J → Pl → Multiset ℕ) (fa : J → Pl → ℝ)
    (a rd La k N S Sc η m b' C1 C0 : ℝ),

    La = Real.log (a * rd) → 1 ≤ La → k = (n : ℝ) + 2 → 0 ≤ m → k + m * ((t : ℝ) + 1) ≤ N →
    0 ≤ b' → 0 ≤ S →

    2 ≤ C1 → 2 * Sc ≤ C1 * S → C1 + 1 ≤ C0 →

    (∀ j, 1 ≤ jj j) → (∀ j, (jj j : ℝ) ≤ m) →
    (∀ j, (s j : ℝ) = (k + (2 * (jj j : ℝ) - 1) * ((t : ℝ) + 1)) / 2) → (∀ j ρ, s j ≤ w j ρ) →

    (∀ j ρ, (w j ρ : ℝ) + Sc ≤ a * rd) → m * ((t : ℝ) + 1) * η ≤ a * rd → 0 ≤ m * ((t : ℝ) + 1) * η →
    (∀ j, ∀ ρ ∈ TT, (aT ρ : ℝ) + (w j ρ : ℝ) ≤ a * rd) →

    (∀ j ρ, logFactRows (ap j ρ) ≤ fa j ρ) →

    (∀ j ρ, ν j ρ = Finset.univ.val.map (νr j ρ) + blk j ρ) →
    (∀ j ρ, ap j ρ = Finset.univ.val.map (ar j ρ) + sm j ρ) →
    (∀ j ρ i, (νr j ρ i : ℝ) = originRow k t (jj j) (w j ρ) (u ρ i) ((i : ℕ) + 1)) →
    (∀ j ρ i, (ar j ρ i : ℝ) = originBig k m t (jj j) (w j ρ) (v ρ i) ((i : ℕ) + 1)) →
    (∀ j ρ, ((blk j ρ).sum : ℝ) ≤ m * ((t : ℝ) + 1) * η) →

    (∀ ρ, ∀ i : Fin (n + 1), v ρ i < u ρ i.castSucc ∧ u ρ i.succ < v ρ i) →
    (∀ ρ, ρ ∉ TT → 0 ≤ u ρ (Fin.last (n + 1)) + (k - 1) / 2 ∧ u ρ 0 - (k - 1) / 2 ≤ Sc) →
    (∀ ρ ∈ TT, u ρ 0 = (aT ρ : ℝ) + (k - 1) / 2 ∧ u ρ (Fin.last (n + 1)) = -(bT ρ : ℝ) - (k - 1) / 2 ∧
      0 ≤ v ρ (Fin.last n) + (k - 2) / 2 ∧ v ρ 0 - (k - 2) / 2 ≤ Sc) →
    ∃ eE δ : J → Pl → ℝ,
      (∀ j ρ, phRows (ν j ρ) - fa j ρ ≤
        (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (aT ρ : ℝ) else 0) + eE j ρ) ∧
      (∀ j ρ, ((ν j ρ).sum : ℝ) = (if ρ ∈ TT then (aT ρ : ℝ) else 0) + k * (w j ρ : ℝ) + δ j ρ) ∧
      (∀ j ρ, eE j ρ ≤ C0 * ((w j ρ : ℝ) + S + N ^ 2 + m * ((t : ℝ) + 1) * η) * La) ∧
      (∀ j ρ, |δ j ρ| ≤
        C0 * ((w j ρ : ℝ) + k * (N + S) + m * ((t : ℝ) + 1) * η + (if ρ ∈ TT then k * b' else 0)))
def TheoremDivIneqOrigin : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]

    (muC mu0 Fo hu hP mlam logT : ℝ) (hK : J → ℝ) (fa : J → Pl → ℝ)

    (n tt : ℕ) (jj s : J → ℕ) (aT bT : Pl → ℕ) (w : J → Pl → ℕ)
    (u : Pl → Fin (n + 2) → ℝ) (v : Pl → Fin (n + 1) → ℝ)
    (νr : J → Pl → Fin (n + 2) → ℕ) (ar : J → Pl → Fin (n + 1) → ℕ) (blk sm : J → Pl → Multiset ℕ)
    (ν ap : J → Pl → Multiset ℕ)

    (x eps L b a rd La B0 Nc xe m f k N S Sc η w'' b' dC lam0 C1 C0 : ℝ)

    (Lpass Eb e6 eP logOm : ℝ) (eK pq : J → ℝ),

    muC ≤ mu0 + Lpass →
    mu0 ≤ ∑ j, ∑ ρ, pq j * (w j ρ : ℝ) * logOm + 2 * Fo + Eb →
    hu = hP + ∑ j, hK j - mlam →
    (∀ j, hK j ≤ ∑ ρ, (phRows (ν j ρ) - ((ν j ρ).sum : ℝ) * logOm) + eK j) →
    ∑ j, ∑ ρ, fa j ρ - e6 ≤ mlam →
    hP ≤ -(∑ t ∈ TT, (aT t : ℝ) * logT) + eP →

    k = (n : ℝ) + 2 → k + m * ((tt : ℝ) + 1) ≤ N → 0 ≤ b' →
    2 ≤ C1 → 2 * Sc ≤ C1 * S → C1 + 1 ≤ C0 →
    (∀ j, 1 ≤ jj j) → (∀ j, (jj j : ℝ) ≤ m) →
    (∀ j, (s j : ℝ) = (k + (2 * (jj j : ℝ) - 1) * ((tt : ℝ) + 1)) / 2) → (∀ j ρ, s j ≤ w j ρ) →
    (∀ j ρ, (w j ρ : ℝ) + Sc ≤ a * rd) →
    (∀ j, ∀ ρ ∈ TT, (aT ρ : ℝ) + (w j ρ : ℝ) ≤ a * rd) →
    (∀ j ρ, logFactRows (ap j ρ) ≤ fa j ρ) →

    (∀ j ρ, ν j ρ = Finset.univ.val.map (νr j ρ) + blk j ρ) →
    (∀ j ρ, ap j ρ = Finset.univ.val.map (ar j ρ) + sm j ρ) →
    (∀ j ρ i, (νr j ρ i : ℝ) = originRow k tt (jj j) (w j ρ) (u ρ i) ((i : ℕ) + 1)) →
    (∀ j ρ i, (ar j ρ i : ℝ) = originBig k m tt (jj j) (w j ρ) (v ρ i) ((i : ℕ) + 1)) →
    (∀ j ρ, ((blk j ρ).sum : ℝ) ≤ m * ((tt : ℝ) + 1) * η) →

    (∀ ρ, ∀ i : Fin (n + 1), v ρ i < u ρ i.castSucc ∧ u ρ i.succ < v ρ i) →
    (∀ ρ, ρ ∉ TT → 0 ≤ u ρ (Fin.last (n + 1)) + (k - 1) / 2 ∧ u ρ 0 - (k - 1) / 2 ≤ Sc) →
    (∀ ρ ∈ TT, u ρ 0 = (aT ρ : ℝ) + (k - 1) / 2 ∧ u ρ (Fin.last (n + 1)) = -(bT ρ : ℝ) - (k - 1) / 2 ∧
      0 ≤ v ρ (Fin.last n) + (k - 2) / 2 ∧ v ρ 0 - (k - 2) / 2 ≤ Sc) →

    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → a = x * b →

    1 ≤ rd → Real.log rd ≤ L → Real.log x ≤ L → La = Real.log (a * rd) →

    B0 = f * m * b * x ^ eps → 0 ≤ Nc → x ^ eps ≤ xe →

    (Fintype.card J : ℝ) = m → (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f →

    0 ≤ S → 0 ≤ η → 1 ≤ dC →

    (∀ j ρ, (w j ρ : ℝ) ≤ 2 * b) →

    (∀ j, |pq j - k| ≤ m) → |logOm| ≤ La →

    lam0 ≤ b → N ^ 2 * dC ≤ b → m ^ 3 * N ^ 2 * L ≤ b → m * η * N * L ≤ b → k * N ≤ b →
    k * S ≤ w'' → m * ((tt : ℝ) + 1) * η ≤ w'' → N * w'' ≤ b → b' * N ≤ a → m * k * b' ≤ a →

    Lpass ≤ 1 + C0 * lam0 →
    Eb ≤ C0 * m * xe * (B0 + Nc) →
    (∀ j, eK j ≤ C0 * (f * N ^ 2 * (La + dC) + f * m ^ 3 * N ^ 2 * L)) →
    e6 ≤ C0 * m * f * N ^ 2 * La →
    eP ≤ C0 * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La →
      muC + hu - 2 * Fo ≤
        ∑ t ∈ TT, (m * (Formalism.LatticeIndexTer.ph (aT t : ℝ) - (aT t : ℝ) * logOm) - (aT t : ℝ) * logT) +
        (50 * C0 + 10) * ((TT.card : ℝ) * a * La + m * (B0 + Nc) * xe)
end Formalism.DivisionValues


