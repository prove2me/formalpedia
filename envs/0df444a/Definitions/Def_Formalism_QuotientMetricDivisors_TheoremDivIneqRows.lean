-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRows
-- name    : Formalism_QuotientMetricDivisors_TheoremDivIneqRows
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:04:38.148792+00:00
-- url     : https://prove2.me/theorems/e49989aa-a4e3-4e59-b8be-ecee8e04efa9
-- title:
--   Theorem Div Ineq Rows
-- statement:
--   Definitions and structural lemmas for Theorem Div Ineq Rows, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/TheoremDivIneqRows.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_StatementE
import Definitions.Def_Formalism_QuotientMetricDivisors_StatementJ
import Definitions.Def_Formalism_QuotientMetricDivisors_StatementK
import Definitions.Def_Formalism_LogFactorialIndices_StatementSize
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
def phRows (lam : Multiset ℕ) : ℝ := (lam.map fun r : ℕ => Formalism.LatticeIndexTer.ph (r : ℝ)).sum
def logFactRows (lam : Multiset ℕ) : ℝ := (lam.map fun r : ℕ => Real.log (r.factorial : ℝ)).sum
def IsRowsOff (n w : ℕ) (S Bl sh : ℝ) (ν ap : Multiset ℕ) : Prop :=
  ∃ (c : Fin (n + 1) → ℕ) (c' r : Fin n → ℕ) (blk sm : Multiset ℕ),
    Formalism.LatticeIndexTer.Interlaced n (fun i => (c i : ℝ)) (fun i => (c' i : ℝ)) S ∧
    (∀ i, |(r i : ℝ) - ((w : ℝ) + (c' i : ℝ))| ≤ sh) ∧
    (blk.sum : ℝ) ≤ Bl ∧
    ν = (Finset.univ.val.map fun i => w + c i) + blk ∧
    ap = Finset.univ.val.map r + sm
def IsRowsTop (n aT w : ℕ) (S Bl sh : ℝ) (ν ap : Multiset ℕ) : Prop :=
  ∃ (c : Fin n → ℕ) (c' r : Fin (n + 1) → ℕ) (r0 : ℕ) (blk sm : Multiset ℕ),
    Formalism.LatticeIndexTer.Interlaced n (fun i => (c' i : ℝ)) (fun i => (c i : ℝ)) S ∧
    (∀ i, |(r i : ℝ) - ((w : ℝ) + (c' i : ℝ))| ≤ sh) ∧
    r0 ≤ w ∧
    (blk.sum : ℝ) ≤ Bl ∧
    ν = (aT + w) ::ₘ r0 ::ₘ ((Finset.univ.val.map fun i => w + c i) + blk) ∧
    ap = Finset.univ.val.map r + sm
def RowsFactorial : Prop :=
  ∀ (n w : ℕ) (S Bl sh A La fa : ℝ) (ν ap : Multiset ℕ),
    La = Real.log A → 1 ≤ La → (w : ℝ) + S ≤ A → Bl ≤ A → logFactRows ap ≤ fa →
    (IsRowsOff n w S Bl sh ν ap →
      phRows ν - fa ≤ ((w : ℝ) + 2 * S + (n : ℝ) * sh + Bl) * La) ∧
    (∀ aT : ℕ, (aT : ℝ) + (w : ℝ) ≤ A → IsRowsTop n aT w S Bl sh ν ap →
      phRows ν - fa ≤
        Formalism.LatticeIndexTer.ph (aT : ℝ) + ((2 * (w : ℝ) + S + (n : ℝ) * sh + Bl) * La + 1))
def RowsPeriod : Prop :=
  ∀ (n w : ℕ) (S Bl sh : ℝ) (ν ap : Multiset ℕ),
    (IsRowsOff n w S Bl sh ν ap →
      0 ≤ (ν.sum : ℝ) - ((n : ℝ) + 1) * (w : ℝ) ∧
      (ν.sum : ℝ) - ((n : ℝ) + 1) * (w : ℝ) ≤ ((n : ℝ) + 1) * S + Bl) ∧
    (∀ aT : ℕ, IsRowsTop n aT w S Bl sh ν ap →
      -(w : ℝ) ≤ (ν.sum : ℝ) - ((aT : ℝ) + ((n : ℝ) + 2) * (w : ℝ)) ∧
      (ν.sum : ℝ) - ((aT : ℝ) + ((n : ℝ) + 2) * (w : ℝ)) ≤ (n : ℝ) * S + Bl)
def RowsHook : Prop :=
  ∀ μ : YoungDiagram,
    logFactRows (μ.rowLens : Multiset ℕ) ≤ Real.log (Formalism.LatticeIndexTer.hookProd μ : ℝ)
def RowsStepE : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
    (n : ℕ) (aT : Pl → ℕ) (w : J → Pl → ℕ) (ν ap : J → Pl → Multiset ℕ) (fa : J → Pl → ℝ)
    (a rd La k N S Sc t η m b' cs C0 : ℝ),

    La = Real.log (a * rd) → 1 ≤ La → k = (n : ℝ) + 2 → k ≤ N → 0 ≤ b' → 0 ≤ cs →

    2 ≤ C0 → cs + 1 ≤ C0 → 2 * Sc ≤ C0 * S →

    (∀ j ρ, (w j ρ : ℝ) + Sc ≤ a * rd) → m * (t + 1) * η ≤ a * rd →
    (∀ j, ∀ ρ ∈ TT, (aT ρ : ℝ) + (w j ρ : ℝ) ≤ a * rd) →

    (∀ j ρ, logFactRows (ap j ρ) ≤ fa j ρ) →

    (∀ j, ∀ ρ, ρ ∉ TT →
      IsRowsOff (n + 1) (w j ρ) Sc (m * (t + 1) * η) (cs * N) (ν j ρ) (ap j ρ)) →
    (∀ j, ∀ ρ ∈ TT,
      IsRowsTop n (aT ρ) (w j ρ) Sc (m * (t + 1) * η) (cs * N) (ν j ρ) (ap j ρ)) →
    ∃ eE δ : J → Pl → ℝ,
      (∀ j ρ, phRows (ν j ρ) - fa j ρ ≤
        (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (aT ρ : ℝ) else 0) + eE j ρ) ∧
      (∀ j ρ, ((ν j ρ).sum : ℝ) = (if ρ ∈ TT then (aT ρ : ℝ) else 0) + k * (w j ρ : ℝ) + δ j ρ) ∧
      (∀ j ρ, eE j ρ ≤ C0 * ((w j ρ : ℝ) + S + N ^ 2 + m * (t + 1) * η) * La) ∧
      (∀ j ρ, |δ j ρ| ≤
        C0 * ((w j ρ : ℝ) + k * (N + S) + m * (t + 1) * η + (if ρ ∈ TT then k * b' else 0)))
def IsRowsTopLow (n aT w : ℕ) (S Bl sh : ℝ) (ν ap : Multiset ℕ) : Prop :=
  ∃ (c : Fin n → ℕ) (c' r : Fin (n + 1) → ℕ) (r0 : ℕ) (blk sm : Multiset ℕ),
    Formalism.LatticeIndexTer.Interlaced n (fun i => (c' i : ℝ)) (fun i => (c i : ℝ)) S ∧
    (∀ i, |(r i : ℝ) - ((w : ℝ) + (c' i : ℝ))| ≤ sh) ∧
    r0 ≤ w ∧
    (blk.sum : ℝ) ≤ Bl ∧
    ν = (aT + w) ::ₘ r0 ::ₘ (Finset.univ.val.map c + blk) ∧
    ap = Finset.univ.val.map r + sm
def RowsTopLow : Prop :=
  ∀ (n aT w : ℕ) (S Bl sh A La fa : ℝ) (ν ap : Multiset ℕ),
    La = Real.log A → 1 ≤ La → (w : ℝ) + S ≤ A → Bl ≤ A → (aT : ℝ) + (w : ℝ) ≤ A →
    logFactRows ap ≤ fa → IsRowsTopLow n aT w S Bl sh ν ap →
      phRows ν - fa ≤
        Formalism.LatticeIndexTer.ph (aT : ℝ) + ((2 * (w : ℝ) + S + (n : ℝ) * (sh + 1) + Bl) * La + 1) ∧
      -(((n : ℝ) + 1) * (w : ℝ)) ≤ (ν.sum : ℝ) - ((aT : ℝ) + ((n : ℝ) + 2) * (w : ℝ)) ∧
      (ν.sum : ℝ) - ((aT : ℝ) + ((n : ℝ) + 2) * (w : ℝ)) ≤ (n : ℝ) * S + Bl
def TheoremDivIneqRows : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]

    (muC mu0 Fo hu hP mlam logT : ℝ) (hK : J → ℝ) (fa : J → Pl → ℝ)

    (n : ℕ) (aT : Pl → ℕ) (w : J → Pl → ℕ) (ν ap : J → Pl → Multiset ℕ)

    (x eps L b a rd La B0 Nc xe m f k N S Sc cs tt η w'' b' dC lam0 C0 : ℝ)

    (Lpass Eb e6 eP logOm : ℝ) (eK pq : J → ℝ),

    muC ≤ mu0 + Lpass →
    mu0 ≤ ∑ j, ∑ ρ, pq j * (w j ρ : ℝ) * logOm + 2 * Fo + Eb →
    hu = hP + ∑ j, hK j - mlam →
    (∀ j, hK j ≤ ∑ ρ, (phRows (ν j ρ) - ((ν j ρ).sum : ℝ) * logOm) + eK j) →
    ∑ j, ∑ ρ, fa j ρ - e6 ≤ mlam →
    hP ≤ -(∑ t ∈ TT, (aT t : ℝ) * logT) + eP →

    k = (n : ℝ) + 2 → k ≤ N → 0 ≤ b' → 0 ≤ cs → 2 ≤ C0 → cs + 1 ≤ C0 → 2 * Sc ≤ C0 * S →
    (∀ j ρ, (w j ρ : ℝ) + Sc ≤ a * rd) →
    (∀ j, ∀ ρ ∈ TT, (aT ρ : ℝ) + (w j ρ : ℝ) ≤ a * rd) →
    (∀ j ρ, logFactRows (ap j ρ) ≤ fa j ρ) →
    (∀ j, ∀ ρ, ρ ∉ TT →
      IsRowsOff (n + 1) (w j ρ) Sc (m * (tt + 1) * η) (cs * N) (ν j ρ) (ap j ρ)) →
    (∀ j, ∀ ρ ∈ TT,
      IsRowsTop n (aT ρ) (w j ρ) Sc (m * (tt + 1) * η) (cs * N) (ν j ρ) (ap j ρ)) →

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
def IsRowsTopFree (n aT w : ℕ) (S Bl sh : ℝ) (ν ap : Multiset ℕ) : Prop :=
  ∃ (c : Fin n → ℕ) (c' r : Fin (n + 1) → ℕ) (r0 : ℕ) (blk sm : Multiset ℕ),
    (∀ i, (c i : ℝ) ≤ S) ∧ (∀ i, (c' i : ℝ) ≤ S) ∧
    (∀ i, |(r i : ℝ) - ((w : ℝ) + (c' i : ℝ))| ≤ sh) ∧
    r0 ≤ w ∧
    (blk.sum : ℝ) ≤ Bl ∧
    ν = (aT + w) ::ₘ r0 ::ₘ ((Finset.univ.val.map fun i => w + c i) + blk) ∧
    ap = Finset.univ.val.map r + sm
def RowsTopFree : Prop :=
  ∀ (n aT w : ℕ) (S Bl sh A La fa : ℝ) (ν ap : Multiset ℕ),
    La = Real.log A → 1 ≤ La → (w : ℝ) + S ≤ A → Bl ≤ A → (aT : ℝ) + (w : ℝ) ≤ A →
    logFactRows ap ≤ fa → IsRowsTopFree n aT w S Bl sh ν ap →
      phRows ν - fa ≤
        Formalism.LatticeIndexTer.ph (aT : ℝ) + ((2 * (w : ℝ) + (n : ℝ) * (S + sh) + Bl) * La + 1) ∧
      -(w : ℝ) ≤ (ν.sum : ℝ) - ((aT : ℝ) + ((n : ℝ) + 2) * (w : ℝ)) ∧
      (ν.sum : ℝ) - ((aT : ℝ) + ((n : ℝ) + 2) * (w : ℝ)) ≤ (n : ℝ) * S + Bl
end Formalism.DivisionValues


