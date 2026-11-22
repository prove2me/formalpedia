-- Prove2me | Definitions.Def_Formalism_BranchSandwichDivisors_DualLevelType
-- name    : Formalism_BranchSandwichDivisors_DualLevelType
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:23:31.818253+00:00
-- url     : https://prove2.me/theorems/9d3300e1-b910-4a88-8b8e-17e0696a4953
-- title:
--   Dual Level Type
-- statement:
--   Definitions and structural lemmas for Dual Level Type, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/DualLevelType.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_StatementK
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementR
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module NumberField IsDedekindDomain
noncomputable section
namespace Formalism.BranchingDeterminantCap
def DivRecord : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
    (muC mu0 Fo hu mlam logT : ℝ) (hK : J → ℝ) (aT : Pl → ℝ) (phν nν fa : J → Pl → ℝ)
    (x eps L b a rd La B0 Nc xe m f k N S tt η w'' b' dC lam0 C0 C : ℝ)
    (Eb e6 logOm : ℝ) (eK pq : J → ℝ) (w eE δ : J → Pl → ℝ)
    (Sg : Type) [Fintype Sg] (rk nS dg : Sg → ℝ) (nbar HH0 muP0 muPs r g Q : ℝ),
    0 < nbar → 0 ≤ lam0 → (∀ s, 0 ≤ rk s) → 0 < ∑ s, rk s → 0 ≤ r → 0 < g →
    (∀ s, (1 - 8 * f * r / g) * nbar ≤ nS s ∧ nS s ≤ (1 + 8 * f * r / g) * nbar) →
    |(-mu0) - muP0| ≤ lam0 → |(-muC) - muPs| ≤ lam0 →
    (∀ s, dg s ≤ rk s * (HH0 + lam0)) →
    (∑ s, nS s * dg s) - 17 / 2 * lam0 * (∑ s, nS s * rk s) ≤ muPs * (∑ s, nS s * rk s) →
    muP0 * (∑ s, rk s) ≤ (∑ s, dg s) + 2 * lam0 * (∑ s, rk s) →
    mu0 + HH0 + 4 * lam0 ≤ Q → 1 ≤ Q → 24 * f * r * Q ≤ g → 25 / 2 ≤ C0 →
    C ≤ C0 → 0 ≤ b' →
    mu0 ≤ (∑ j, ∑ ρ, pq j * w j ρ * logOm) + 2 * Fo + Eb →
    hu = (-(∑ t ∈ TT, aT t * logT) +
        C * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La) + (∑ j, hK j) - mlam →
    (∀ j, hK j ≤ (∑ ρ, (phν j ρ - nν j ρ * logOm)) + eK j) →
    (∑ j, ∑ ρ, fa j ρ) - e6 ≤ mlam →
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
    Eb ≤ C0 * m * xe * (B0 + Nc) →
    (∀ j, eK j ≤ C0 * (f * N ^ 2 * (La + dC) + f * m ^ 3 * N ^ 2 * L)) →
    e6 ≤ C0 * m * f * N ^ 2 * La →
    (∀ j ρ, eE j ρ ≤ C0 * (w j ρ + S + N ^ 2 + m * (tt + 1) * η) * La) →
    (∀ j ρ, |δ j ρ| ≤
      C0 * (w j ρ + k * (N + S) + m * (tt + 1) * η + (if ρ ∈ TT then k * b' else 0))) →
      muC + hu - 2 * Fo ≤
        (∑ t ∈ TT, (m * (Formalism.LatticeIndexTer.ph (aT t) - aT t * logOm) - aT t * logT)) +
        (50 * C0 + 10) * ((TT.card : ℝ) * a * La + m * (B0 + Nc) * xe)
def DivRecordFull : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)] (nr : ℕ)
    (muC mu0 Fo hu logT : ℝ) (aT : Pl → ℝ) (ν : J → Pl → Fin nr → ℝ) (logH : J → Pl → ℝ)
    (x eps L b a rd La B0 Nc xe m f k N S tt η w'' b' lam0 C0 C nV L' CL : ℝ)
    (Eb logOm : ℝ) (pq : J → ℝ) (w eE δ : J → Pl → ℝ)
    (Sg : Type) [Fintype Sg] (rk nS dg : Sg → ℝ) (nbar HH0 muP0 muPs r g Q : ℝ),
    0 < nbar → 0 ≤ lam0 → (∀ s, 0 ≤ rk s) → 0 < ∑ s, rk s → 0 ≤ r → 0 < g →
    (∀ s, (1 - 8 * f * r / g) * nbar ≤ nS s ∧ nS s ≤ (1 + 8 * f * r / g) * nbar) →
    |(-mu0) - muP0| ≤ lam0 → |(-muC) - muPs| ≤ lam0 →
    (∀ s, dg s ≤ rk s * (HH0 + lam0)) →
    (∑ s, nS s * dg s) - 17 / 2 * lam0 * (∑ s, nS s * rk s) ≤ muPs * (∑ s, nS s * rk s) →
    muP0 * (∑ s, rk s) ≤ (∑ s, dg s) + 2 * lam0 * (∑ s, rk s) →
    mu0 + HH0 + 4 * lam0 ≤ Q → 1 ≤ Q → 24 * f * r * Q ≤ g → 25 / 2 ≤ C0 →
    0 ≤ C → C ≤ C0 → 0 ≤ b' → 0 ≤ nV → nV ≤ N → L' ≤ CL * La → 0 ≤ CL → C * CL ≤ C0 →
    mu0 ≤ (∑ j, ∑ ρ, pq j * w j ρ * logOm) + 2 * Fo + Eb →
    hu = (-(∑ t ∈ TT, aT t * logT) +
          C * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La) +
        (∑ j, ((∑ ρ, ((∑ i, Formalism.LatticeIndexTer.ph (ν j ρ i)) - (∑ i, ν j ρ i) * logOm)) +
          C * f * N ^ 2 * (La + m ^ 3 * L))) -
        (∑ j, ((∑ ρ, logH j ρ) - C * f * nV ^ 2 * L')) →
    (∀ j ρ, (∑ i, Formalism.LatticeIndexTer.ph (ν j ρ i)) - logH j ρ ≤
      (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (aT ρ) else 0) + eE j ρ) →
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
    Eb ≤ C0 * m * xe * (B0 + Nc) →
    (∀ j ρ, eE j ρ ≤ C0 * (w j ρ + S + N ^ 2 + m * (tt + 1) * η) * La) →
    (∀ j ρ, |δ j ρ| ≤
      C0 * (w j ρ + k * (N + S) + m * (tt + 1) * η + (if ρ ∈ TT then k * b' else 0))) →
      muC + hu - 2 * Fo ≤
        (∑ t ∈ TT, (m * (Formalism.LatticeIndexTer.ph (aT t) - aT t * logOm) - aT t * logT)) +
        (50 * C0 + 10) * ((TT.card : ℝ) * a * La + m * (B0 + Nc) * xe)
def StepDiiiRecord : Prop :=
  ∀ (Pl : Type) [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
    (hP logT ev : ℝ) (aT bT nτ lam1 D0 D1 logc logxi : Pl → ℝ)
    (a La L m f k N S η b' CT Cev C : ℝ),
    hP ≤ -(∑ τ, nτ τ * logT) + (∑ τ, (2 * logc τ + logxi τ)) + ev →
    (∀ τ, logc τ ≤ (N - 1) * D1 τ * Real.log (2 * a)) →
    (∀ τ, logxi τ ≤ N * (N - 1) / 2 * Real.log (2 * a)) →
    (∀ τ, nτ τ = lam1 τ - D0 τ) →
    (∀ τ ∈ TT, lam1 τ = aT τ - (N - k) / 2) → (∀ τ, τ ∉ TT → S - (N - 1) / 2 ≤ lam1 τ) →
    (∀ τ, D0 τ ≤ S + m * η + (if τ ∈ TT then bT τ else 0)) →
    (∀ τ, D1 τ ≤ 3 * D0 τ + S + η) →
    (∀ τ ∈ TT, bT τ ≤ 2 * b') →
    0 ≤ logT → logT ≤ CT * m * L → 0 ≤ CT → L ≤ La → 0 ≤ La →
    0 ≤ Real.log (2 * a) → Real.log (2 * a) ≤ 2 * La →
    1 ≤ m → m ≤ N → 0 ≤ k → 0 ≤ S → 0 ≤ η → 0 ≤ b' → (Fintype.card Pl : ℝ) ≤ f →
    ev ≤ Cev * f * N ^ 2 * La → 0 ≤ Cev → 2 * (16 + CT + Cev) ≤ C →
      hP ≤ -(∑ t ∈ TT, aT t * logT) +
        C * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La
def ChainFirstEntry : Prop :=
  ∀ (l e : ℕ → ℝ) (u1 aT k t : ℝ) (m : ℕ),
    l 0 = u1 - (k + 1) / 2 + 1 →
    (∀ j, l (j + 1) = l j + (e (j + 1) - (k + ((j : ℝ) + 1) * (t + 1)) / 2) -
      (e (j + 1) - (k + (j : ℝ) * (t + 1)) / 2)) →
    u1 = aT + (k - 1) / 2 →
      l m = u1 - ((k + (m : ℝ) * (t + 1)) - 1) / 2 ∧
      l m = aT - ((k + (m : ℝ) * (t + 1)) - k) / 2
def ChainWeights : Prop :=
  ∀ (top e : ℕ → ℝ) (blk : ℕ → ℕ → ℝ) (u i k t : ℝ) (m : ℕ),
    top 0 = u - (k + 1) / 2 + i →
    (∀ j, top (j + 1) = top j + (e (j + 1) - (k + ((j : ℝ) + 1) * (t + 1)) / 2) -
      (e (j + 1) - (k + (j : ℝ) * (t + 1)) / 2)) →
    (∀ j, blk (j + 1) (j + 1) = 0 - (e (j + 1) - (k + (j : ℝ) * (t + 1)) / 2)) →
    (∀ j j', j + 1 ≤ j' → blk (j + 1) (j' + 1) =
      blk (j + 1) j' + (e (j' + 1) - (k + ((j' : ℝ) + 1) * (t + 1)) / 2) -
        (e (j' + 1) - (k + (j' : ℝ) * (t + 1)) / 2)) →
      top m = u - ((k + (m : ℝ) * (t + 1)) + 1) / 2 + i ∧
      ∀ j, j + 1 ≤ m → blk (j + 1) m =
        -e (j + 1) + k / 2 + (2 * ((j : ℝ) + 1) - 1 - (m : ℝ)) * (t + 1) / 2
def DescentListsInequality : Prop :=
  ∀ (K mm : ℕ) (u v e bb : ℕ → ℝ) (S η t bT : ℝ),
    (∀ i, i < K + 1 → u (i + 1) + 1 / 2 ≤ v i ∧ v i + 1 / 2 ≤ u i) →
    (∀ j, j < mm → (t + 1) / 2 ≤ e j - bb j ∧ e j - bb j ≤ η) → 0 ≤ t → 0 ≤ S → v 0 ≤ S →
      0 ≤ (∑ i ∈ range (K + 1), (v i - u (i + 1) - 1 / 2)) +
          (∑ j ∈ range mm, (e j - bb j - (t + 1) / 2)) ∧
      (u (K + 1) = -bT - ((K : ℝ) + 1) / 2 →
        (∑ i ∈ range (K + 1), (v i - u (i + 1) - 1 / 2)) +
          (∑ j ∈ range mm, (e j - bb j - (t + 1) / 2)) ≤ S + (mm : ℝ) * η + bT) ∧
      (u (K + 1) = v K - 1 / 2 → 0 ≤ u K →
        (∑ i ∈ range (K + 1), (v i - u (i + 1) - 1 / 2)) +
          (∑ j ∈ range mm, (e j - bb j - (t + 1) / 2)) ≤ S + (mm : ℝ) * η)
def NtauTwoSided : Prop :=
  ∀ (Pl : Type) [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
    (aT bT nτ lam1 D0 : Pl → ℝ) (m f k N S cS η b' : ℝ),
    (∀ τ, nτ τ = lam1 τ - D0 τ) →
    (∀ τ ∈ TT, lam1 τ = aT τ - (N - k) / 2) →
    (∀ τ, τ ∉ TT → S - (N - 1) / 2 ≤ lam1 τ ∧ lam1 τ ≤ cS - (N - 1) / 2) →
    (∀ τ, 0 ≤ D0 τ ∧ D0 τ ≤ S + m * η + (if τ ∈ TT then bT τ else 0)) →
    (∀ τ ∈ TT, bT τ ≤ 2 * b') → k ≤ N → 0 ≤ k → 1 ≤ N → 0 ≤ S → S ≤ cS → 0 ≤ m * η → 0 ≤ b' →
    (Fintype.card Pl : ℝ) ≤ f →
      (∀ τ ∈ TT, aT τ - (N - k) / 2 - S - m * η - bT τ ≤ nτ τ ∧ nτ τ ≤ aT τ) ∧
      (∀ τ, τ ∉ TT → -((N - 1) / 2 + m * η) ≤ nτ τ ∧ nτ τ ≤ cS) ∧
      |(∑ τ, nτ τ) - (∑ t ∈ TT, aT t)| ≤ 2 * (TT.card : ℝ) * b' + f * (cS + m * η + N / 2)
def GainRecord : Prop :=
  ∀ (Pl : Type) [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
    (aT bT nτ lam1 D0 : Pl → ℝ) (m f k N S cS η b' logT CT L : ℝ),
    (∀ τ, nτ τ = lam1 τ - D0 τ) →
    (∀ τ ∈ TT, lam1 τ = aT τ - (N - k) / 2) →
    (∀ τ, τ ∉ TT → S - (N - 1) / 2 ≤ lam1 τ ∧ lam1 τ ≤ cS - (N - 1) / 2) →
    (∀ τ, 0 ≤ D0 τ ∧ D0 τ ≤ S + m * η + (if τ ∈ TT then bT τ else 0)) →
    (∀ τ ∈ TT, bT τ ≤ 2 * b') → k ≤ N → 0 ≤ k → 1 ≤ N → 0 ≤ S → S ≤ cS → 0 ≤ m * η → 0 ≤ b' →
    (Fintype.card Pl : ℝ) ≤ f → 0 ≤ logT → logT ≤ CT * m * L →
      |(-(∑ τ, nτ τ * logT)) - (-(∑ t ∈ TT, aT t * logT))| ≤
        CT * (2 * (TT.card : ℝ) * b' + f * (cS + m * η + N / 2)) * m * L
def chainProd {F : Type} [Field F] {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
    (K : ∀ j, V j →ₗ[F] V (j + 1)) : ∀ j, V 0 →ₗ[F] V j
  | 0 => LinearMap.id
  | j + 1 => (K j).comp (chainProd K j)
def matOp {F : Type} [Field F] {A A' W W' : Type} [Fintype A] [AddCommGroup W] [Module F W]
    [AddCommGroup W'] [Module F W'] (E : A' → A → (W →ₗ[F] W')) : (A → W) →ₗ[F] (A' → W') :=
  LinearMap.pi fun α => ∑ β, (E α β).comp (LinearMap.proj β)
def ChainCommute : Prop :=
  ∀ (F : Type) [Field F] (V : ℕ → Type) [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
    (K : ∀ j, V j →ₗ[F] V (j + 1)) (U : ∀ j, V j →ₗ[F] V j) (c : ℕ → F) (m : ℕ),
    (∀ j, j < m → c j ≠ 0) →
    (∀ j, j < m → (U (j + 1)).comp (K j) = c j • (K j).comp (U j)) →
      (chainProd K m).comp ((U 0) ^ m) =
        (∏ j ∈ range m, ((c j)⁻¹) ^ (m - j)) • chainProd (fun j => (U (j + 1)).comp (K j)) m
def MatrixCommute : Prop :=
  ∀ (F : Type) [Field F] (A A' W W' : Type) [Fintype A] [AddCommGroup W] [Module F W]
    [AddCommGroup W'] [Module F W'] (E : A' → A → (W →ₗ[F] W')) (u : W →ₗ[F] W) (u' : W' →ₗ[F] W')
    (c : F), (∀ α β, u'.comp (E α β) = c • (E α β).comp u) →
      (u'.compLeft A').comp (matOp E) = c • (matOp E).comp (u.compLeft A)
def ChainCommuteMatrix : Prop :=
  ∀ (F : Type) [Field F] (AA : ℕ → Type) [∀ j, Fintype (AA j)] (W : ℕ → Type)
    [∀ j, AddCommGroup (W j)] [∀ j, Module F (W j)]
    (E : ∀ j, AA (j + 1) → AA j → (W j →ₗ[F] W (j + 1))) (u : ∀ j, W j →ₗ[F] W j) (c : ℕ → F) (m : ℕ),
    (∀ j, j < m → c j ≠ 0) →
    (∀ j, j < m → ∀ α β, (u (j + 1)).comp (E j α β) = c j • (E j α β).comp (u j)) →
      (chainProd (V := fun j => AA j → W j) (fun j => matOp (E j)) m).comp
          (((u 0).compLeft (AA 0)) ^ m) =
        (∏ j ∈ range m, ((c j)⁻¹) ^ (m - j)) •
          chainProd (V := fun j => AA j → W j)
            (fun j => ((u (j + 1)).compLeft (AA (j + 1))).comp (matOp (E j))) m
def ChainCommuteCoupled : Prop :=
  ∀ (F : Type) [Field F] (AA : ℕ → Type) [∀ j, Fintype (AA j)] (W : ℕ → Type)
    [∀ j, AddCommGroup (W j)] [∀ j, Module F (W j)]
    (E : ∀ j, AA (j + 1) → AA j → (W j →ₗ[F] W (j + 1))) (u : ∀ j, W j →ₗ[F] W j) (c : ℕ → F) (n : ℕ)
    (Vc Vl : Type) [AddCommGroup Vc] [Module F Vc] [AddCommGroup Vl] [Module F Vl]
    (A : (AA n → W n) →ₗ[F] Vc) (B : Vc →ₗ[F] Vl) (Uc : Vc →ₗ[F] Vc) (Ul : Vl →ₗ[F] Vl),
    (∀ j, j < n + 2 → c j ≠ 0) →
    (∀ j, j < n → ∀ α β, (u (j + 1)).comp (E j α β) = c j • (E j α β).comp (u j)) →
    Uc.comp A = c n • A.comp ((u n).compLeft (AA n)) →
    Ul.comp B = c (n + 1) • B.comp Uc →
      (B.comp (A.comp (chainProd (V := fun j => AA j → W j) (fun j => matOp (E j)) n))).comp
          (((u 0).compLeft (AA 0)) ^ (n + 2)) =
        (∏ j ∈ range (n + 2), ((c j)⁻¹) ^ (n + 2 - j)) •
          (Ul.comp B).comp ((Uc.comp A).comp
            (chainProd (V := fun j => AA j → W j)
              (fun j => ((u (j + 1)).compLeft (AA (j + 1))).comp (matOp (E j))) n))
def ChainDenominator : Prop :=
  ∀ (R F : Type) [CommRing R] [Field F] [Algebra R F] (V : ℕ → Type) [∀ j, AddCommGroup (V j)]
    [∀ j, Module F (V j)] [∀ j, Module R (V j)] [∀ j, IsScalarTower R F (V j)]
    (K : ∀ j, V j →ₗ[F] V (j + 1)) (U : ∀ j, V j →ₗ[F] V j) (S : ∀ j, Submodule R (V j)) (T : R)
    (VV : Type) [Fintype VV] (cv : ℕ → VV → F) (gam : VV → ℕ) (e1 m : ℕ),
    (∀ j, j < m → ∀ v, cv j v ≠ 0) →
    (∀ j, j < m → (U (j + 1)).comp (K j) = (∏ v, cv j v) • (K j).comp (U j)) →
    (∀ j, j < m → ∀ x ∈ S j, T ^ e1 • U (j + 1) (K j x) ∈ S (j + 1)) →
    (∀ j, j < m → ∀ v, ∃ r : R, algebraMap R F r = algebraMap R F T ^ gam v * (cv j v)⁻¹) →
      ∀ x ∈ S 0,
        T ^ (m * e1 + (∑ v, gam v) * (m * (m + 1) / 2)) • chainProd K m (((U 0) ^ m) x) ∈ S m
def ChainDenominatorCoupled : Prop :=
  ∀ (R F : Type) [CommRing R] [Field F] [Algebra R F] (AA : ℕ → Type) [∀ j, Fintype (AA j)] (W : ℕ → Type)
    [∀ j, AddCommGroup (W j)] [∀ j, Module F (W j)] [∀ j, Module R (W j)] [∀ j, IsScalarTower R F (W j)]
    (E : ∀ j, AA (j + 1) → AA j → (W j →ₗ[F] W (j + 1))) (u : ∀ j, W j →ₗ[F] W j) (n : ℕ)
    (Vc Vl : Type) [AddCommGroup Vc] [Module F Vc] [Module R Vc] [IsScalarTower R F Vc]
    [AddCommGroup Vl] [Module F Vl] [Module R Vl] [IsScalarTower R F Vl]
    (A : (AA n → W n) →ₗ[F] Vc) (B : Vc →ₗ[F] Vl) (Uc : Vc →ₗ[F] Vc) (Ul : Vl →ₗ[F] Vl)
    (S : ∀ j, Submodule R (AA j → W j)) (Sc : Submodule R Vc) (Sl : Submodule R Vl) (T : R)
    (VV : Type) [Fintype VV] (cv : ℕ → VV → F) (gam : VV → ℕ) (e1 : ℕ),
    (∀ j, j < n + 2 → ∀ v, cv j v ≠ 0) →
    (∀ j, j < n → ∀ α β, (u (j + 1)).comp (E j α β) = (∏ v, cv j v) • (E j α β).comp (u j)) →
    Uc.comp A = (∏ v, cv n v) • A.comp ((u n).compLeft (AA n)) →
    Ul.comp B = (∏ v, cv (n + 1) v) • B.comp Uc →
    (∀ j, j < n → ∀ x ∈ S j, T ^ e1 • ((u (j + 1)).compLeft (AA (j + 1))) (matOp (E j) x) ∈ S (j + 1)) →
    (∀ x ∈ S n, T ^ e1 • Uc (A x) ∈ Sc) →
    (∀ x ∈ Sc, T ^ e1 • Ul (B x) ∈ Sl) →
    (∀ j, j < n + 2 → ∀ v, ∃ r : R, algebraMap R F r = algebraMap R F T ^ gam v * (cv j v)⁻¹) →
      ∀ x ∈ S 0,
        T ^ ((n + 2) * e1 + (∑ v, gam v) * ((n + 2) * (n + 2 + 1) / 2)) •
          B (A (chainProd (V := fun j => AA j → W j) (fun j => matOp (E j)) n
            ((((u 0).compLeft (AA 0)) ^ (n + 2)) x))) ∈ Sl
def RamIndexCount : Prop :=
  ∀ (VV : Type) [Fintype VV] (n : ℕ) (lam : VV → Fin (n + 1) → ℝ) (aT W b' i1 i2 : VV → ℝ)
    (len m d aMax : ℝ), 0 ≤ m → 0 ≤ d →
    (∀ v, lam v 0 = aT v) → (∀ v i, i ≠ 0 → lam v i ≤ W v) → (∀ v, 0 ≤ b' v ∧ b' v ≤ W v) →
    len ≤ m * ∑ v, (i1 v + i2 v) →
    (∀ v, i1 v ≤ (((n : ℝ) + 1) - 1) * d) →
    (∀ v, i2 v ≤ d * (∑ i, (lam v i + b' v)) / ((n : ℝ) + 1)) →
    (∀ v, aT v ≤ aMax) →
      len ≤ m * d * ∑ v, (aT v / ((n : ℝ) + 1) + 2 * W v + ((n : ℝ) + 1)) ∧
      m * d * ∑ v, (aT v / ((n : ℝ) + 1) + 2 * W v + ((n : ℝ) + 1)) ≤
        m * d * ∑ v, (aMax / ((n : ℝ) + 1) + 3 * W v + ((n : ℝ) + 1))
def RamSublattice : Prop :=
  ∀ (R F : Type) [CommRing R] [Field F] [Algebra R F] (V : ℕ → Type) [∀ j, AddCommGroup (V j)]
    [∀ j, Module F (V j)] [∀ j, Module R (V j)] [∀ j, IsScalarTower R F (V j)]
    (K : ∀ j, V j →ₗ[F] V (j + 1)) (U : ∀ j, V j →ₗ[F] V j) (S : ∀ j, Submodule R (V j)) (T : R)
    (VV : Type) [Fintype VV] (cv : ℕ → VV → F) (gam : VV → ℕ) (e1 m : ℕ)
    (l : List VV) (Uv : VV → (V 0 →ₗ[F] V 0)) (Bv : VV → Submodule R (V 0))
    (MF : Submodule F (V 0)) (M : Submodule R (V 0)) (b' : VV → ℕ),
    (∀ j, j < m → ∀ v, cv j v ≠ 0) →
    (∀ j, j < m → (U (j + 1)).comp (K j) = (∏ v, cv j v) • (K j).comp (U j)) →
    (∀ j, j < m → ∀ x ∈ S j, T ^ e1 • U (j + 1) (K j x) ∈ S (j + 1)) →
    (∀ j, j < m → ∀ v, ∃ r : R, algebraMap R F r = algebraMap R F T ^ gam v * (cv j v)⁻¹) →
    l.Nodup → (∀ v, v ∈ l) → U 0 = (l.map Uv).prod →
    (∀ x, x ∈ M ↔ x ∈ S 0 ∧ x ∈ MF) →
    (∀ v, ∀ x ∈ MF, Uv v x ∈ MF) →
    (∀ v, ∀ x ∈ S 0, T ^ b' v • x ∈ Bv v) →
    (∀ v, ∀ x ∈ Bv v, Uv v x ∈ S 0) →
      ∀ x ∈ M,
        T ^ (m * ∑ v, b' v) • ((U 0) ^ m) x ∈ M ∧
        T ^ (m * e1 + (∑ v, gam v) * (m * (m + 1) / 2)) •
          chainProd K m (T ^ (m * ∑ v, b' v) • ((U 0) ^ m) x) ∈ S m
def DenominatorPayment : Prop :=
  ∀ (Lm : Type) [Fintype Lm] (Pi : Finset Lm) [DecidablePred (· ∈ Pi)] (wt e : Lm → ℝ)
    (logT m e1 G : ℝ),
    ∑ lam, wt lam = logT → ∑ lam ∈ Pi, wt lam = logT / 2 →
    (∀ lam, e lam = m * e1 + (if lam ∈ Pi then G * (m * (m + 1) / 2) else 0)) →
      2 * ∑ lam, wt lam * e lam = (2 * m * e1 + G * (m * (m + 1) / 2)) * logT ∧
      ∀ E : Lm → ℝ, (∀ lam, 0 ≤ wt lam) → (∀ lam, E lam ≤ e lam) →
        2 * ∑ lam, wt lam * E lam ≤ (2 * m * e1 + G * (m * (m + 1) / 2)) * logT
def CapOne : Prop :=
  ∀ (n : ℕ) (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ), Interlace lam sg → d0 lam sg = 0 →
    cCap lam sg = 1
def CapConstSharp : Prop :=
  ∀ (n : ℕ) (lam : Fin (n + 2) → ℤ) (sg : Fin (n + 1) → ℤ), Interlace lam sg →
    (∀ (i j : Fin (n + 1)), ∀ v ∈ (rset lam sg i).erase (sg i),
      |((v - (i : ℤ)) - (sg j - (j : ℤ)))| ≤
        min (lam 0) (lam 1 + d0 lam sg) - lam (Fin.last (n + 1)) + (n : ℤ)) ∧
    |cCap lam sg| ≤ (min (lam 0) (lam 1 + d0 lam sg) - lam (Fin.last (n + 1)) + (n : ℤ)) ^
        ((n + 1) * (d1 lam sg).toNat) ∧
    min (lam 0) (lam 1 + d0 lam sg) - lam (Fin.last (n + 1)) + (n : ℤ) ≤
      2 * (sg 0 - lam (Fin.last (n + 1))) + (n : ℤ) ∧
    |cCap lam sg| ≤ (2 * (sg 0 - lam (Fin.last (n + 1))) + (n : ℤ) + 2) ^
        ((n + 1) * (d1 lam sg).toNat)
def CapIndep : Prop :=
  ∀ (n : ℕ) (lam lam' : Fin (n + 2) → ℤ) (sg : Fin (n + 1) → ℤ), Interlace lam sg →
    (∀ i : Fin (n + 1), lam' i.succ = lam i.succ) →
    lam 1 + d0 lam sg ≤ lam 0 → lam 1 + d0 lam sg ≤ lam' 0 →
      Interlace lam' sg ∧ d0 lam' sg = d0 lam sg ∧ d1 lam' sg = d1 lam sg ∧
      cCap lam' sg = cCap lam sg
def PassageMuMaxLat : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (S : Type) [Fintype S] (Rs Bs : S → Submodule (𝓞 K) V)
      (latticeAtBaseLevel RPs R0 R1 : Submodule (𝓞 K) V) (G h0 h1 : ℕ) (HH0 : ℝ)
      (n : S → ℕ) (xs : ∀ s, Fin (n s) → V →ₗ[K] V),
      latticeAtBaseLevel.FG → RPs.FG → R0 ≠ ⊥ → R1 ≠ ⊥ → 0 < h0 → h0 ≤ G → 0 < h1 → h1 ≤ G →
      R0 ≤ latticeAtBaseLevel → (∀ x ∈ latticeAtBaseLevel, (h0 : 𝓞 K) • x ∈ R0) → R1 ≤ RPs → (∀ x ∈ RPs, (h1 : 𝓞 K) • x ∈ R1) →
      (∀ s, n s ^ 2 ≤ G) →
      (∀ s t, s ≠ t → OrthAt b X (Bs s) (Bs t)) → (∀ s, Bs s ≤ RPs) →
      (∀ x ∈ RPs, (G : 𝓞 K) • x ∈ ⨆ s, Bs s) → (∀ s, Rs s ≤ latticeAtBaseLevel) →
      (∀ s i, ∀ c ∈ Bs s, ((G : 𝓞 K) ^ 3) • xs s i c ∈ Rs s) →
      (∀ s i v, Formalism.HN.opNormAt b X b X v (xs s i) ≤ 1) →
      (∀ s, ∀ c ∈ Bs s, (∀ i, xs s i c = 0) → c = 0) →
      Formalism.HN.muMaxDef b (scaleFrame (Real.sqrt h0) X) R0 ≤ HH0 →
        Formalism.HN.muMaxDef b (scaleFrame (Real.sqrt h1) X) R1 ≤ HH0 + 21 / 2 * Real.log G
def typeSpace {K V Γ : Type} [Field K] [AddCommGroup V] [Module K V] [Group Γ]
    (ρ : Γ →* Module.End K V) (chi : Γ → K) : Submodule K V :=
  ⨅ γ : Γ, Module.End.eigenspace (ρ γ) (chi γ)
def LevelIncl : Prop :=
  ∀ (O K V0 EE : Type) [CommRing O] [IsNoetherianRing O] [Field K] [Algebra O K] [AddCommGroup V0] [Module K V0] [Module O V0]
    [IsScalarTower O K V0] [AddCommGroup EE] [Module K EE] [Module O EE]
    [IsScalarTower O K EE]
    (io : V0 →ₗ[K] EE) (e0 : V0 →ₗ[K] V0) (e1 : EE →ₗ[K] EE),
    e1 ∘ₗ e1 = e1 → io ∘ₗ e0 = e1 ∘ₗ io →
    ∀ (A : Submodule O V0) (h : ℕ), (∀ a ∈ A, (h : O) • e0 a ∈ A) →
      (A ⊓ (LinearMap.range e0).restrictScalars O).map (io.restrictScalars O) ≤
        A.map (io.restrictScalars O) ⊓ (LinearMap.range e1).restrictScalars O ∧
      (∀ x ∈ A.map (io.restrictScalars O) ⊓ (LinearMap.range e1).restrictScalars O,
        (h : O) • x ∈
          (A ⊓ (LinearMap.range e0).restrictScalars O).map (io.restrictScalars O)) ∧
      (A.FG → (A.map (io.restrictScalars O) ⊓ (LinearMap.range e1).restrictScalars O).FG)
def LevelInclType : Prop :=
  ∀ (O K V0 EE : Type) [CommRing O] [Field K] [Algebra O K] [AddCommGroup V0] [Module K V0] [Module O V0]
    [IsScalarTower O K V0] [AddCommGroup EE] [Module K EE] [Module O EE]
    [IsScalarTower O K EE]
    (Γ : Type) [Group Γ] [Fintype Γ] (ρ0 : Γ →* Module.End K V0) (ρ1 : Γ →* Module.End K EE)
    (chi : Γ →* Oˣ) (io : V0 →ₗ[K] EE), (∀ γ x, io (ρ0 γ x) = ρ1 γ (io x)) →
    ∀ A : Submodule O V0, (∀ γ, ∀ a ∈ A, ρ0 γ a ∈ A) →
      (A ⊓ (typeSpace ρ0 fun γ => algebraMap O K (chi γ)).restrictScalars O).map
          (io.restrictScalars O) ≤
        A.map (io.restrictScalars O) ⊓
          (typeSpace ρ1 fun γ => algebraMap O K (chi γ)).restrictScalars O ∧
      ∀ x ∈ A.map (io.restrictScalars O) ⊓
          (typeSpace ρ1 fun γ => algebraMap O K (chi γ)).restrictScalars O,
        ((Fintype.card Γ : ℕ) : O) • x ∈
          (A ⊓ (typeSpace ρ0 fun γ => algebraMap O K (chi γ)).restrictScalars O).map
            (io.restrictScalars O)
def LocalGlobalIncl : Prop :=
  ∀ (O V : Type) [CommRing O] [AddCommGroup V] [Module O V] (M N : Submodule O V),
    (∀ p : Ideal O, p.IsMaximal → ∀ x ∈ M, ∃ s : O, s ∉ p ∧ s • x ∈ N) → M ≤ N
def LevelInclLocal : Prop :=
  ∀ (O K V0 EE : Type) [CommRing O] [Field K] [Algebra O K] [AddCommGroup V0] [Module K V0] [Module O V0]
    [IsScalarTower O K V0] [AddCommGroup EE] [Module K EE] [Module O EE]
    [IsScalarTower O K EE]
    (Γ : Type) [Group Γ] [Fintype Γ] (ρ0 : Γ →* Module.End K V0) (ρ1 : Γ →* Module.End K EE)
    (chi : Γ →* Oˣ) (R R' : Submodule O EE),
    (∀ p : Ideal O, p.IsMaximal → ∃ (io : V0 →ₗ[K] EE) (A : Submodule O V0),
      (∀ γ x, io (ρ0 γ x) = ρ1 γ (io x)) ∧ (∀ γ, ∀ a ∈ A, ρ0 γ a ∈ A) ∧
      (∀ x, (∃ s : O, s ∉ p ∧ s • x ∈ R) ↔
        x ∈ A.map (io.restrictScalars O) ⊓
          (typeSpace ρ1 fun γ => algebraMap O K (chi γ)).restrictScalars O) ∧
      (∀ x, (∃ s : O, s ∉ p ∧ s • x ∈ R') ↔
        x ∈ (A ⊓ (typeSpace ρ0 fun γ => algebraMap O K (chi γ)).restrictScalars O).map
          (io.restrictScalars O))) →
      R' ≤ R ∧ ∀ x ∈ R, ((Fintype.card Γ : ℕ) : O) • x ∈ R'
def CentralLevel : Prop :=
  ∀ (O K V : Type) [CommRing O] [Field K] [CharZero K] [Algebra O K] [AddCommGroup V] [Module K V] [Module O V]
    [IsScalarTower O K V] (G0 : Type) [Group G0] [Fintype G0] (ρ : G0 →* Module.End K V)
    (c : G0 → O) (e : V →ₗ[K] V), (∀ x y, c (y * x * y⁻¹) = c x) →
    (Fintype.card G0 : K) • e = ∑ x, algebraMap O K (c x) • ρ x →
    ∀ (H : Subgroup G0) (chi : H → K) (A B : Submodule O V),
      (∀ x, ∀ a ∈ B, ρ x a ∈ B) → B ≤ A →
      (∀ y v, e (ρ y v) = ρ y (e v)) ∧
      (∀ v ∈ typeSpace (ρ.comp H.subtype) chi, e v ∈ typeSpace (ρ.comp H.subtype) chi) ∧
      (∀ a ∈ B, ((Fintype.card G0 : ℕ) : O) • e a ∈ B) ∧
      (∀ a ∈ B ⊓ (typeSpace (ρ.comp H.subtype) chi).restrictScalars O,
        ((Fintype.card G0 : ℕ) : O) • e a ∈
          B ⊓ (typeSpace (ρ.comp H.subtype) chi).restrictScalars O) ∧
      (∀ a ∈ B ⊓ (typeSpace (ρ.comp H.subtype) chi).restrictScalars O,
        ((Fintype.card G0 : ℕ) : O) • e a ∈
          A ⊓ (typeSpace (ρ.comp H.subtype) chi).restrictScalars O)
def DualLevel : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), (∀ x, (∀ y, h y x = 0) → x = 0) →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (ρ : Γ →* Module.End K V),
    (∀ γ x y, h (ρ γ x) (ρ γ y) = h x y) →
    ∀ A : Submodule (𝓞 K) V, A.FG → Submodule.span K (A : Set V) = ⊤ →
      (∀ γ, ∀ a ∈ A, ρ γ a ∈ A) →
      Formalism.HermitianLatticesTheory.dual (((Fintype.card Γ : K)⁻¹) • h)
                  (A ⊓ (LinearMap.range (∑ γ, ρ γ : Module.End K V)).restrictScalars (𝓞 K)) ⊓
                (LinearMap.range (∑ γ, ρ γ : Module.End K V)).restrictScalars (𝓞 K) ≤
        Formalism.HermitianLatticesTheory.dual h A ⊓ (LinearMap.range (∑ γ, ρ γ : Module.End K V)).restrictScalars (𝓞 K) ∧
      ∀ (B : Submodule (𝓞 K) V) (d : ℕ), (∀ x ∈ Formalism.HermitianLatticesTheory.dual h A, (d : 𝓞 K) • x ∈ B) →
        ∀ x ∈ Formalism.HermitianLatticesTheory.dual (((Fintype.card Γ : K)⁻¹) • h)
              (A ⊓ (LinearMap.range (∑ γ, ρ γ : Module.End K V)).restrictScalars (𝓞 K)) ⊓
            (LinearMap.range (∑ γ, ρ γ : Module.End K V)).restrictScalars (𝓞 K),
          (d : 𝓞 K) • x ∈
            B ⊓ (LinearMap.range (∑ γ, ρ γ : Module.End K V)).restrictScalars (𝓞 K)
def LevelCompareType : Prop :=
  ∀ (K V0 EE ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V0] [Module K V0] [Module (𝓞 K) V0] [IsScalarTower (𝓞 K) K V0]
    [AddCommGroup EE] [Module K EE] [Module (𝓞 K) EE] [IsScalarTower (𝓞 K) K EE]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K EE) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (ρ0 : Γ →* Module.End K V0) (ρ1 : Γ →* Module.End K EE)
    (chi : Γ →* (𝓞 K)ˣ) (io : V0 →ₗ[K] EE), (∀ γ x, io (ρ0 γ x) = ρ1 γ (io x)) →
    ∀ A : Submodule (𝓞 K) V0, A.FG → (∀ γ, ∀ a ∈ A, ρ0 γ a ∈ A) →
      (A ⊓ (typeSpace ρ0 fun γ => algebraMap (𝓞 K) K (chi γ)).restrictScalars (𝓞 K)).map
          (io.restrictScalars (𝓞 K)) ≠ ⊥ →
      |Formalism.HN.muDef b (scaleFrame (Real.sqrt (Fintype.card Γ : ℕ)) X)
                  ((A ⊓ (typeSpace ρ0 fun γ => algebraMap (𝓞 K) K (chi γ)).restrictScalars (𝓞 K)).map
                    (io.restrictScalars (𝓞 K))) -
                Formalism.HN.muDef b X (A.map (io.restrictScalars (𝓞 K)) ⊓
                  (typeSpace ρ1 fun γ => algebraMap (𝓞 K) K (chi γ)).restrictScalars (𝓞 K))| ≤
        Real.log (Fintype.card Γ : ℕ) ∧
      |Formalism.HN.muMaxDef b (scaleFrame (Real.sqrt (Fintype.card Γ : ℕ)) X)
                  ((A ⊓ (typeSpace ρ0 fun γ => algebraMap (𝓞 K) K (chi γ)).restrictScalars (𝓞 K)).map
                    (io.restrictScalars (𝓞 K))) -
                Formalism.HN.muMaxDef b X (A.map (io.restrictScalars (𝓞 K)) ⊓
                  (typeSpace ρ1 fun γ => algebraMap (𝓞 K) K (chi γ)).restrictScalars (𝓞 K))| ≤
        Real.log (Fintype.card Γ : ℕ)
def LevelCompareLocal : Prop :=
  ∀ (K V0 EE ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V0] [Module K V0] [Module (𝓞 K) V0] [IsScalarTower (𝓞 K) K V0]
    [AddCommGroup EE] [Module K EE] [Module (𝓞 K) EE] [IsScalarTower (𝓞 K) K EE]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K EE) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (ρ0 : Γ →* Module.End K V0) (ρ1 : Γ →* Module.End K EE)
    (chi : Γ →* (𝓞 K)ˣ) (R R' : Submodule (𝓞 K) EE), R.FG → R' ≠ ⊥ →
    (∀ p : Ideal (𝓞 K), p.IsMaximal → ∃ (io : V0 →ₗ[K] EE) (A : Submodule (𝓞 K) V0),
      (∀ γ x, io (ρ0 γ x) = ρ1 γ (io x)) ∧ (∀ γ, ∀ a ∈ A, ρ0 γ a ∈ A) ∧
      (∀ x, (∃ s : 𝓞 K, s ∉ p ∧ s • x ∈ R) ↔
        x ∈ A.map (io.restrictScalars (𝓞 K)) ⊓
          (typeSpace ρ1 fun γ => algebraMap (𝓞 K) K (chi γ)).restrictScalars (𝓞 K)) ∧
      (∀ x, (∃ s : 𝓞 K, s ∉ p ∧ s • x ∈ R') ↔
        x ∈ (A ⊓ (typeSpace ρ0 fun γ => algebraMap (𝓞 K) K (chi γ)).restrictScalars (𝓞 K)).map
          (io.restrictScalars (𝓞 K)))) →
      |Formalism.HN.muDef b (scaleFrame (Real.sqrt (Fintype.card Γ : ℕ)) X) R' - Formalism.HN.muDef b X R| ≤
        Real.log (Fintype.card Γ : ℕ) ∧
      |Formalism.HN.muMaxDef b (scaleFrame (Real.sqrt (Fintype.card Γ : ℕ)) X) R' - Formalism.HN.muMaxDef b X R| ≤
        Real.log (Fintype.card Γ : ℕ)
def DualLevelType : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), (∀ x, (∀ y, h y x = 0) → x = 0) →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (ρ : Γ →* Module.End K V) (chi : Γ →* (𝓞 K)ˣ),
    (∀ γ x y, h (ρ γ x) (ρ γ y) = h x y) →
    (∀ γ, star (algebraMap (𝓞 K) K (chi γ)) * algebraMap (𝓞 K) K (chi γ) = 1) →
    ∀ A : Submodule (𝓞 K) V, A.FG → Submodule.span K (A : Set V) = ⊤ →
      (∀ γ, ∀ a ∈ A, ρ γ a ∈ A) →
      Formalism.HermitianLatticesTheory.dual (((Fintype.card Γ : K)⁻¹) • h)
                  (A ⊓ (typeSpace ρ fun γ => algebraMap (𝓞 K) K (chi γ)).restrictScalars (𝓞 K)) ⊓
                (typeSpace ρ fun γ => algebraMap (𝓞 K) K (chi γ)).restrictScalars (𝓞 K) ≤
        Formalism.HermitianLatticesTheory.dual h A ⊓
          (typeSpace ρ fun γ => algebraMap (𝓞 K) K (chi γ)).restrictScalars (𝓞 K) ∧
      ∀ (B : Submodule (𝓞 K) V) (d : ℕ), (∀ x ∈ Formalism.HermitianLatticesTheory.dual h A, (d : 𝓞 K) • x ∈ B) →
        ∀ x ∈ Formalism.HermitianLatticesTheory.dual (((Fintype.card Γ : K)⁻¹) • h)
              (A ⊓ (typeSpace ρ fun γ => algebraMap (𝓞 K) K (chi γ)).restrictScalars (𝓞 K)) ⊓
            (typeSpace ρ fun γ => algebraMap (𝓞 K) K (chi γ)).restrictScalars (𝓞 K),
          (d : 𝓞 K) • x ∈
            B ⊓ (typeSpace ρ fun γ => algebraMap (𝓞 K) K (chi γ)).restrictScalars (𝓞 K)
end Formalism.BranchingDeterminantCap


