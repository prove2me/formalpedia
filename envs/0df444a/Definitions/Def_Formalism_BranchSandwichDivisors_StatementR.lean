-- Prove2me | Definitions.Def_Formalism_BranchSandwichDivisors_StatementR
-- name    : Formalism_BranchSandwichDivisors_StatementR
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:44:16.710336+00:00
-- url     : https://prove2.me/theorems/f8b9d993-4a15-4bd7-ba02-149e5edc9518
-- title:
--   Statement R
-- statement:
--   Definitions and structural lemmas for Statement R, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/StatementR.lean

import Mathlib
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
namespace Formalism.BranchingDeterminantCap
def MultPlace : Prop :=
  ∀ (q k r : ℕ) (Nn : ℕ → ℕ), 2 ≤ q → 1 ≤ k → k ≤ r → r ≤ q → Nn 0 = 1 →
    (∀ j, Nn j ≤ r.choose j) →
    ∀ gam : ℕ → ℝ, gam 0 = 1 → (∀ l, gam (l + 1) = (q : ℝ) ^ (l + 1) - (q : ℝ) ^ l) →
      (q : ℝ) ^ k * (1 - 1 / (q : ℝ)) ≤ ∑ j ∈ range (k + 1), (Nn j : ℝ) * gam (k - j) ∧
      ∑ j ∈ range (k + 1), (Nn j : ℝ) * gam (k - j) ≤
        (q : ℝ) ^ k * (1 + (2 * (r : ℝ) - 1) / (q : ℝ))
def MultProd : Prop :=
  ∀ (Pv : Type) [Fintype Pv] (q nn : Pv → ℝ) (k : ℕ) (f r g : ℝ),
    (Fintype.card Pv : ℝ) = 2 * f → 1 ≤ r → 0 < g → (∀ v, g ≤ q v) → 4 * f * r ≤ g →
    (∀ v, q v ^ k * (1 - 1 / q v) ≤ nn v ∧ nn v ≤ q v ^ k * (1 + (2 * r - 1) / q v)) →
      (1 - 8 * f * r / g) * ∏ v, q v ^ k ≤ ∏ v, nn v ∧
      ∏ v, nn v ≤ (1 + 8 * f * r / g) * ∏ v, q v ^ k
def TransferDeg : Prop :=
  ∀ (S : Type) [Fintype S] (rk nS dgA dgB : S → ℝ) (la degP : ℝ),
    (∀ s, |dgB s - nS s * dgA s| ≤ 13 / 2 * la * (nS s * rk s)) →
    ∑ s, dgB s ≤ degP → degP ≤ (∑ s, dgB s) + 2 * la * (∑ s, nS s * rk s) →
    0 ≤ la → (∀ s, 0 ≤ nS s * rk s) →
      |degP - ∑ s, nS s * dgA s| ≤ 17 / 2 * la * (∑ s, nS s * rk s)
def TransferMean : Prop :=
  ∀ (S : Type) [Fintype S] (rk nS dg : S → ℝ) (nbar de la ka HH0 muP0 muPs muR0 muRs : ℝ),
    0 < nbar → 0 ≤ de → de ≤ 1 / 3 → 0 ≤ la → 0 ≤ ka → (∀ s, 0 ≤ rk s) → 0 < ∑ s, rk s →
    (∀ s, (1 - de) * nbar ≤ nS s ∧ nS s ≤ (1 + de) * nbar) →
    |muR0 - muP0| ≤ ka * la → |muRs - muPs| ≤ ka * la →
    (∀ s, dg s ≤ rk s * (HH0 + ka * la)) →
    (∑ s, nS s * dg s) - 17 / 2 * la * (∑ s, nS s * rk s) ≤ muPs * (∑ s, nS s * rk s) →
    muP0 * (∑ s, rk s) ≤ (∑ s, dg s) + 2 * la * (∑ s, rk s) →
      0 ≤ -muR0 + HH0 + (2 * ka + 2) * la ∧
      -muRs ≤ -muR0 + 3 * de * (-muR0 + HH0 + (2 * ka + 2) * la) + (2 * ka + 21 / 2) * la
def PassageAssembly : Prop :=
  ∀ (S : Type) [Fintype S] (rk nS dg : S → ℝ)
    (nbar lam0 HH0 muP0 muPs mu0 muC f r g Q C0 : ℝ),
    0 < nbar → 0 ≤ lam0 → (∀ s, 0 ≤ rk s) → 0 < ∑ s, rk s → 0 ≤ f → 0 ≤ r → 0 < g →
    (∀ s, (1 - 8 * f * r / g) * nbar ≤ nS s ∧ nS s ≤ (1 + 8 * f * r / g) * nbar) →
    |(-mu0) - muP0| ≤ lam0 → |(-muC) - muPs| ≤ lam0 →
    (∀ s, dg s ≤ rk s * (HH0 + lam0)) →
    (∑ s, nS s * dg s) - 17 / 2 * lam0 * (∑ s, nS s * rk s) ≤ muPs * (∑ s, nS s * rk s) →
    muP0 * (∑ s, rk s) ≤ (∑ s, dg s) + 2 * lam0 * (∑ s, rk s) →
    mu0 + HH0 + 4 * lam0 ≤ Q → 1 ≤ Q → 24 * f * r * Q ≤ g → 25 / 2 ≤ C0 →
      muC ≤ mu0 + (3 * (8 * f * r / g) * (mu0 + HH0 + 4 * lam0) + 25 / 2 * lam0) ∧
      3 * (8 * f * r / g) * (mu0 + HH0 + 4 * lam0) + 25 / 2 * lam0 ≤ 1 + C0 * lam0
def Interlace {n : ℕ} (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ) : Prop :=
  ∀ i : Fin n, sg i ≤ lam i.castSucc ∧ lam i.succ ≤ sg i
def d0 {n : ℕ} (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ) : ℤ := ∑ i : Fin n, (sg i - lam i.succ)
def d1 {n : ℕ} (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ) : ℤ :=
  ∑ i : Fin n, min (lam i.castSucc - lam i.succ) (d0 lam sg)
def rset {n : ℕ} (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ) (i : Fin n) : Finset ℤ :=
  Finset.Icc (lam i.succ) (min (lam i.castSucc) (lam i.succ + d0 lam sg))
def capEig {n : ℕ} (lam : Fin (n + 1) → ℤ) (sg mu : Fin n → ℤ) : ℤ :=
  ∏ i : Fin n, ∏ v ∈ (rset lam sg i).erase (sg i), ∏ j : Fin n, ((v - (i : ℤ)) - (mu j - (j : ℤ)))
def cCap {n : ℕ} (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ) : ℤ := capEig lam sg sg
def InterlaceIdent : Prop :=
  ∀ (n : ℕ) (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ), Interlace lam sg →
    (∑ i, lam i) - (∑ i, sg i) = lam 0 - d0 lam sg ∧
    (∑ i : Fin n, (lam i.castSucc - sg i)) = lam 0 - lam (Fin.last n) - d0 lam sg ∧
    0 ≤ d0 lam sg ∧ 0 ≤ d1 lam sg ∧ (∀ i, sg i ∈ rset lam sg i) ∧
    (∀ i, (((rset lam sg i).erase (sg i)).card : ℤ) = min (lam i.castSucc - lam i.succ) (d0 lam sg))
def InterlaceTelescope : Prop :=
  ∀ (n : ℕ) (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ), Interlace lam sg →
    ∀ p q : Fin n, p ≤ q → ∑ i ∈ Finset.Icc p q, (sg i - lam i.succ) ≤ sg p - lam q.succ
def ConstituentRange : Prop :=
  ∀ (n : ℕ) (lam : Fin (n + 1) → ℤ) (sg mu : Fin n → ℤ), Interlace lam sg → Interlace lam mu →
    d0 lam mu = d0 lam sg → ∀ i, mu i ∈ rset lam sg i
def CapKills : Prop :=
  ∀ (n : ℕ) (lam : Fin (n + 1) → ℤ) (sg mu : Fin n → ℤ),
    (∀ i, mu i ∈ rset lam sg i) → mu ≠ sg → capEig lam sg mu = 0
def CapConst : Prop :=
  ∀ (n : ℕ) (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ), Interlace lam sg →
    cCap lam sg ≠ 0 ∧
    |cCap lam sg| ≤ (lam 0 - lam (Fin.last n) + (n : ℤ) - 1) ^ (n * (d1 lam sg).toNat)
def TruncatedDefectBound : Prop :=
  ∀ (n : ℕ) (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ), Interlace lam sg →
    ∀ I : Finset (Fin n), I.card ≤ 3 →
      d1 lam sg ≤ 3 * d0 lam sg + ∑ i ∈ Iᶜ, (lam i.castSucc - lam i.succ)
def WeylDimBound : Prop :=
  ∀ (n : ℕ) (nu : Fin (n + 1) → ℤ), Antitone nu →
    1 ≤ ∏ p ∈ (Finset.univ : Finset (Fin (n + 1) × Fin (n + 1))).filter (fun p => p.1 < p.2),
        (((nu p.1 - nu p.2 : ℤ) : ℝ) + ((p.2 : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ)) /
          (((p.2 : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ)) ∧
    ∏ p ∈ (Finset.univ : Finset (Fin (n + 1) × Fin (n + 1))).filter (fun p => p.1 < p.2),
        (((nu p.1 - nu p.2 : ℤ) : ℝ) + ((p.2 : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ)) /
          (((p.2 : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ)) ≤
      (((nu 0 - nu (Fin.last n) : ℤ) : ℝ) + (n : ℝ)) ^ ((n + 1) * n / 2)
def WeightScale : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (P : E →L[ℂ] F) (Sc : E ≃L[ℂ] E)
    (U : Submodule ℂ E) (t : ℝ), 0 < t → (∀ x ∈ U, Sc x = (t : ℂ) • x) → (∀ x ∈ Uᗮ, Sc x ∈ Uᗮ) →
    (∀ x ∈ Uᗮ, P x = 0) →
      ‖P.comp (Sc.symm : E →L[ℂ] E)‖ = t⁻¹ * ‖P‖
def BranchSandwichDiii : Prop :=
  ∀ (Pl : Type) [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
    (hP logT ev : ℝ) (aT bT nτ lam1 D0 D1 logc logxi : Pl → ℝ)
    (a La L m f k N S η b' CT Cev : ℝ),

    hP ≤ -(∑ τ, nτ τ * logT) + ∑ τ, (2 * logc τ + logxi τ) + ev →
    (∀ τ, logc τ ≤ (N - 1) * D1 τ * Real.log (2 * a)) →
    (∀ τ, logxi τ ≤ N * (N - 1) / 2 * Real.log (2 * a)) →

    (∀ τ, nτ τ = lam1 τ - D0 τ) →
    (∀ τ ∈ TT, lam1 τ = aT τ - (N - k) / 2) → (∀ τ, τ ∉ TT → S - (N - 1) / 2 ≤ lam1 τ) →
    (∀ τ, D0 τ ≤ S + m * η + (if τ ∈ TT then bT τ else 0)) →
    (∀ τ, D1 τ ≤ 3 * D0 τ + S + η) →
    (∀ τ ∈ TT, bT τ ≤ b') →

    0 ≤ logT → logT ≤ CT * m * L → 0 ≤ CT → L ≤ La → 0 ≤ La →
    0 ≤ Real.log (2 * a) → Real.log (2 * a) ≤ 2 * La →
    1 ≤ m → m ≤ N → 0 ≤ k → 0 ≤ S → 0 ≤ η → 0 ≤ b' → (Fintype.card Pl : ℝ) ≤ f →
    ev ≤ Cev * f * N ^ 2 * La → 0 ≤ Cev →
      hP ≤ -(∑ t ∈ TT, aT t * logT) +
        (16 + CT + Cev) * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La
end Formalism.BranchingDeterminantCap


