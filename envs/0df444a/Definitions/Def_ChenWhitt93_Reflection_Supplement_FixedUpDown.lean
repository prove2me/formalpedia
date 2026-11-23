-- Prove2me | Definitions.Def_ChenWhitt93_Reflection_Supplement_FixedUpDown
-- name    : ChenWhitt93_Reflection_Supplement_FixedUpDown
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T06:54:13.62996+00:00
-- url     : https://prove2.me/theorems/1a18dbbf-f268-470f-b1d5-a1fedbc7aeb9
-- title:
--   Section 5 — heavy-traffic assumptions with fixed up and down times: (4.1)–(4.4), (4.6)–(4.7), (5.1)–(5.2), (5.10)–(5.13)
-- statement:
--   This file fixes the heavy-traffic setting of Section 5 of Chen and Whitt (1993), where up and down times are of order one rather than growing with $n$. All assumptions of Section 4(A) are kept except (4.5) and (4.8): (4.5) is replaced by (5.1)–(5.2), and (4.8) by (5.10).
--
--   1. **Primitive data.** For network $n$ with arrival rates $\lambda^n$, service rates $\mu^n$, up fractions $\nu^n$ and routing matrix $P$, the scaled primitives are
--   $$
--   \tfrac{1}{\sqrt n}Z^n(0),\quad \tfrac{1}{\sqrt n}[A^n(nt)-\lambda^nnt],\quad \tfrac{1}{\sqrt n}[S^n(nt)-\mu^nnt],\quad \tfrac{1}{\sqrt n}[R(\lfloor nt\rfloor)-Pnt],\quad \tfrac{1}{\sqrt n}[D^n(nt)-(1-\nu^n)nt],
--   $$
--   the left sides of (4.1)–(4.4) and (5.1). Their limits are $\hat Z(0)$, $\hat A$, $\hat S$, $\hat R$, $\hat D$; the four limit paths are continuous on $[0,\infty)$, so the convergence is uniform on compact sets.
--   2. **Parameters.** (4.6) $\sqrt n(\lambda^n-\lambda)\to c_\lambda$, $\lambda\ge0$; (4.7) $\sqrt n(\mu^n-\mu)\to c_\mu$, $\mu>0$; (5.2) $\sqrt n(\nu^n-\nu)\to c_\nu$, $0\le\nu\le1$; (5.10)
--   $$
--   \lambda_j+\sum_{k=1}^JP_{kj}\mu_k\nu_k=\mu_j\nu_j\quad\text{for each }j;
--   $$
--   and $P$ is substochastic with $P^k\to0$.
--   3. **Limit netput.** (5.12) $\hat\xi_j(t)=\hat A_j(t)+\sum_k[\hat R_{kj}(\mu_k\nu_kt)+P_{kj}\hat S_k(\nu_kt)]-\hat S_j(\nu_jt)$; (5.13) $\hat\eta_j(t)=[c_{\lambda j}-(\mu_jc_{\nu j}+\nu_jc_{\mu j})+\sum_kP_{kj}(\mu_kc_{\nu k}+\nu_kc_{\mu k})]t+\mu_j\hat D_j(t)-\sum_k\mu_kP_{kj}\hat D_k(t)$; and $\hat X=\hat Z(0)+\hat\xi+\hat\eta$.
--   4. **Scaled processes.** $\hat Z^n(t)=n^{-1/2}Z^n(nt)$, $\hat Y^n(t)=n^{-1/2}Y^n(nt)$, $\hat B^n(t)=n^{-1/2}[B^n(nt)-\nu^nnt]$ (5.11), $\hat D^n(t)=n^{-1/2}[D^n(nt)-(1-\nu^n)nt]$, stacked in $\mathbb R^{4J}$; the limit is $(\hat Z,-\hat D-\hat Y,\hat Y,\hat D)$.
--
--   These definitions state Lemma 5.1 and Theorem 5.2.
--
--   **Formalization Note** The deterministic bundle `PathwiseHyp5` is the almost-sure form of the assumptions used after a Skorohod representation, as in the published proof of Theorem 4.1. Paths are functions on $\mathbb R$ set to $0$ for $t<0$. The Section 4 objects `ParamHyp`, `PrimConv`, `LimitRegular`, `xiHat`, `etaHat`, `XHat` and `jointScaled` are not reused: they contain (4.8), (4.5), $\sum_ku_k^j\to\infty$, the time changes for $\nu=1$, or the uncentred $\hat D^n$ of (4.10).
-- source:
--   Chen and Whitt, Diffusion approximations for open queueing networks with service interruptions, Queueing Systems 13 (1993), pp. 347–348 (Section 4(A)), p. 354 ((5.1)–(5.2)), p. 356 ((5.10)–(5.13))

import Mathlib
import Definitions.Def_ChenWhitt93_JumpDiffusion_HeavyTraffic
import Definitions.Def_ChenWhitt93_Reflection_Supplement_AltRenewal

namespace ChenWhitt93.Reflection.Supplement

open MeasureTheory Filter Topology Matrix
open ChenWhitt93.JumpDiffusion

/-!
Chen and Whitt (1993), Section 5, pp. 354–356: the heavy-traffic setting with fixed up and down
times. All assumptions of Section 4(A) are kept except (4.5) and (4.8): (4.5) is replaced by
(5.1)–(5.2) and (4.8) by (5.10). The network index is `n : ℕ`; only the tail `n → ∞` matters
(at `n = 0` the scalings divide by `0`, which Lean evaluates to `0`).
-/

/-- The scaled primitive data of one network in Section 5, a point of
`ℝᴶ × Dᴶ × Dᴶ × D^{J²} × Dᴶ`: the left sides of (4.1)–(4.4) (as in the published
`scaledPrimitives`) and of (5.1). -/
abbrev PrimTuple5 (J : ℕ) : Type :=
  (Fin J → ℝ) × (ℝ → Fin J → ℝ) × (ℝ → Fin J → ℝ) × (ℝ → Fin J → Fin J → ℝ) × (ℝ → Fin J → ℝ)

/-- `n^{-1/2} Zⁿ(0)`, `n^{-1/2}[Aⁿ(nt) − λⁿnt]`, `n^{-1/2}[Sⁿ(nt) − μⁿnt]`,
`n^{-1/2}[R_{kj}(⌊nt⌋) − P_{kj}nt]` and `n^{-1/2}[Dⁿ(nt) − (1 − νⁿ)nt]` for network `n`
(paths extended by `0` to `t < 0`). -/
noncomputable def scaledPrimitives5 {J : ℕ} (χ : Fin J → Fin J → ℕ → Bool) (N : NetworkData J)
    (lamn mun nun : Fin J → ℝ) (P : Matrix (Fin J) (Fin J) ℝ) (n : ℕ) : PrimTuple5 J :=
  ((scaledPrimitives χ N lamn mun P n).1, (scaledPrimitives χ N lamn mun P n).2.1,
    (scaledPrimitives χ N lamn mun P n).2.2.1, (scaledPrimitives χ N lamn mun P n).2.2.2.1,
    centredDown N.toInterruptions nun n)

/-- The limit primitive data of Section 5: `Ẑ(0)`, `Â`, `Ŝ`, `R̂` (with `R t k j = R̂_{kj}(t)`)
and the limit `D̂` of (5.1). -/
structure LimitData5 (J : ℕ) where
  Z0 : Fin J → ℝ
  A : ℝ → Fin J → ℝ
  S : ℝ → Fin J → ℝ
  R : ℝ → Fin J → Fin J → ℝ
  D : ℝ → Fin J → ℝ

/-- The right sides of (4.1)–(4.4) and (5.1) as a point of `PrimTuple5 J` (paths extended by `0`
to `t < 0`). -/
noncomputable def LimitData5.toPrim5 {J : ℕ} (L : LimitData5 J) : PrimTuple5 J :=
  (L.Z0, fun t => if t < 0 then 0 else L.A t, fun t => if t < 0 then 0 else L.S t,
    fun t => if t < 0 then 0 else L.R t, fun t => if t < 0 then 0 else L.D t)

/-- The mode of convergence of (4.1)–(4.4) and (5.1) for continuous limits: the initial vector
converges and the four families of paths converge uniformly on compact subsets of `[0, ∞)`. -/
def PrimConv5 {J : ℕ} (w : ℕ → PrimTuple5 J) (w' : PrimTuple5 J) : Prop :=
  Tendsto (fun n => (w n).1) atTop (𝓝 w'.1) ∧
  UocTendsto (fun n => (w n).2.1) w'.2.1 ∧
  UocTendsto (fun n => (w n).2.2.1) w'.2.2.1 ∧
  UocTendsto (fun n => (w n).2.2.2.1) w'.2.2.2.1 ∧
  UocTendsto (fun n => (w n).2.2.2.2) w'.2.2.2.2

/-- Section 4(A) and (5.1) on one sample path of the limit: `Â`, `Ŝ`, `R̂` and `D̂` are
continuous on `[0, ∞)`. -/
def LimitRegular5 {J : ℕ} (L : LimitData5 J) : Prop :=
  ContinuousOn L.A (Set.Ici 0) ∧ ContinuousOn L.S (Set.Ici 0) ∧ ContinuousOn L.R (Set.Ici 0) ∧
  ContinuousOn L.D (Set.Ici 0)

/-- The parameter assumptions of Section 5: (4.6) `√n(λⁿ − λ) → c_λ`, `λ ≥ 0`;
(4.7) `√n(μⁿ − μ) → c_μ`, `μ > 0`; (5.2) `√n(νⁿ − ν) → c_ν`, `0 ≤ ν ≤ 1`;
(5.10) `λⱼ + Σₖ P_{kj}μₖνₖ = μⱼνⱼ` for each `j`; and `P` substochastic with `Pᵏ → 0`. -/
def ParamHyp5 {J : ℕ} (lamn mun nun : ℕ → Fin J → ℝ) (lam mu nu clam cmu cnu : Fin J → ℝ)
    (P : Matrix (Fin J) (Fin J) ℝ) : Prop :=
  Tendsto (fun n : ℕ => Real.sqrt n • (lamn n - lam)) atTop (𝓝 clam) ∧ (∀ j, 0 ≤ lam j) ∧
  Tendsto (fun n : ℕ => Real.sqrt n • (mun n - mu)) atTop (𝓝 cmu) ∧ (∀ j, 0 < mu j) ∧
  Tendsto (fun n : ℕ => Real.sqrt n • (nun n - nu)) atTop (𝓝 cnu) ∧
  (∀ j, 0 ≤ nu j ∧ nu j ≤ 1) ∧
  (∀ j, lam j + ∑ k, P k j * mu k * nu k = mu j * nu j) ∧
  IsTransientSubstochastic P

/-- The deterministic ("almost sure", Skorohod-represented) form of the assumptions of Section 5
on a sequence of networks with fixed routing `χ`: each network satisfies Section 3's standing
assumptions; (4.6), (4.7), (5.2), (5.10) hold; (4.1)–(4.4) and (5.1) hold u.o.c.; and the limits
`Â`, `Ŝ`, `R̂`, `D̂` are continuous. -/
def PathwiseHyp5 {J : ℕ} (χ : Fin J → Fin J → ℕ → Bool) (net : ℕ → NetworkData J)
    (lamn mun nun : ℕ → Fin J → ℝ) (lam mu nu clam cmu cnu : Fin J → ℝ)
    (P : Matrix (Fin J) (Fin J) ℝ) (L : LimitData5 J) : Prop :=
  (∀ n, (net n).IsValid χ) ∧ ParamHyp5 lamn mun nun lam mu nu clam cmu cnu P ∧
  PrimConv5 (fun n => scaledPrimitives5 χ (net n) (lamn n) (mun n) (nun n) P n) L.toPrim5 ∧
  LimitRegular5 L

/-- (5.12) `ξ̂ⱼ(t) = Âⱼ(t) + Σₖ [R̂_{kj}(μₖνₖt) + P_{kj}Ŝₖ(νₖt)] − Ŝⱼ(νⱼt)`. -/
noncomputable def xiHat5 {J : ℕ} (L : LimitData5 J) (mu nu : Fin J → ℝ)
    (P : Matrix (Fin J) (Fin J) ℝ) (t : ℝ) : Fin J → ℝ :=
  fun j => L.A t j + ∑ k, (L.R (mu k * nu k * t) k j + P k j * L.S (nu k * t) k)
    - L.S (nu j * t) j

/-- (5.13) `η̂ⱼ(t) = [c_{λj} − (μⱼc_{νj} + νⱼc_{μj}) + Σₖ P_{kj}(μₖc_{νk} + νₖc_{μk})] t
  + μⱼD̂ⱼ(t) − Σₖ μₖP_{kj}D̂ₖ(t)`. -/
noncomputable def etaHat5 {J : ℕ} (L : LimitData5 J) (mu nu clam cmu cnu : Fin J → ℝ)
    (P : Matrix (Fin J) (Fin J) ℝ) (t : ℝ) : Fin J → ℝ :=
  fun j => (clam j - (mu j * cnu j + nu j * cmu j)
      + ∑ k, P k j * (mu k * cnu k + nu k * cmu k)) * t
    + mu j * L.D t j - ∑ k, mu k * P k j * L.D t k

/-- (4.14) with (5.12)–(5.13): `X̂(t) = Ẑ(0) + ξ̂(t) + η̂(t)`. -/
noncomputable def XHat5 {J : ℕ} (L : LimitData5 J) (mu nu clam cmu cnu : Fin J → ℝ)
    (P : Matrix (Fin J) (Fin J) ℝ) (t : ℝ) : Fin J → ℝ :=
  L.Z0 + xiHat5 L mu nu P t + etaHat5 L mu nu clam cmu cnu P t

/-- The scaled prelimit processes of Theorem 5.2 stacked as a path in `(ℝᴶ)⁴ = ℝ^{4J}`:
`Ẑⁿ(t) = n^{-1/2}Zⁿ(nt)` and `Ŷⁿ(t) = n^{-1/2}Yⁿ(nt)` as in (4.12),
`B̂ⁿ(t) = n^{-1/2}[Bⁿ(nt) − νⁿnt]` (5.11), and `D̂ⁿ(t) = n^{-1/2}[Dⁿ(nt) − (1 − νⁿ)nt]` (the left
side of (5.1)), for `t ≥ 0`, extended by `0` to `t < 0`. -/
noncomputable def jointScaled5 {J : ℕ} (N : NetworkData J) (Z : ℝ → Fin J → ℤ)
    (B : ℝ → Fin J → ℝ) (nun : Fin J → ℝ) (n : ℕ) (t : ℝ) : Fin 4 → Fin J → ℝ :=
  if t < 0 then 0 else
    ![fun j => (Z (n * t) j : ℝ) / Real.sqrt n,
      fun j => (B (n * t) j - nun j * n * t) / Real.sqrt n,
      fun j => idleTime N B (n * t) j / Real.sqrt n,
      centredDown N.toInterruptions nun n t]

/-- The limit `(Ẑ(t), B̂(t), Ŷ(t), D̂(t))` in `(ℝᴶ)⁴`, with `B̂ = −D̂ − Ŷ` (4.17) and `D̂` the
limit in (5.1), for given paths `Ẑ`, `Ŷ`, for `t ≥ 0`, extended by `0` to `t < 0`. -/
noncomputable def jointLimit5 {J : ℕ} (L : LimitData5 J) (Zh Yh : ℝ → Fin J → ℝ) (t : ℝ) :
    Fin 4 → Fin J → ℝ :=
  if t < 0 then 0 else ![Zh t, -L.D t - Yh t, Yh t, L.D t]

end ChenWhitt93.Reflection.Supplement


