-- Prove2me | Definitions.Def_LuoSunLiu_DIP_Policy
-- name    : LuoSunLiu_DIP_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T19:15:33.095407+00:00
-- url     : https://prove2.me/theorems/7755e4f1-8fba-4be4-bd89-180627c4f33a
-- title:
--   Algorithm 4, p. 16 — the DIP policy: doubling episodes, d_k = C⌈(2^{k−2}ℓ₂)^{1/6}⌉, δ_k, admissible estimators θ̂_{k−1}
-- statement:
--   This file defines the DIP policy (Algorithm 4) of Luo, Sun and Liu.
--
--   The inputs are episode lengths $\alpha_1, \alpha_2 \ge 1$, a discretization constant $C$, a regularization $\lambda > 0$, and the known bounds $p_{\max}$ and $W$. Time is cut into episodes: episode $1$ has length $\ell_1 = \alpha_1$ and episode $k \ge 2$ has length $\ell_k = 2^{k-2}\ell_2$ with $\ell_2 = \alpha_2$, so it ends at period $\alpha_1 + \alpha_2(2^{k-1} - 1)$.
--
--   1. The **number of episodes** up to horizon $T$, $n(T, \alpha_1, \alpha_2)$, is the index of the episode containing $T$; for $T > \alpha_1$ it equals $\lceil\log_2((T - \alpha_1)/\alpha_2 + 1)\rceil + 1$, from (6), p. 54.
--   2. Episode $k \ge 2$ uses
--   $$d_k = C\bigl\lceil(2^{k-2}\ell_2)^{1/6}\bigr\rceil, \qquad \delta_k = \frac{1}{2^{k-2}\ell_2}.$$
--   3. An **admissible Inner Algorithm A** is, for each episode $k$, a measurable map from the episode's data $(x_t, p_t, y_t)$ to an estimate in $\Theta = \{\theta : \|\theta\|_1 \le W\}$. The estimate built from episode $k-1$ is $\hat\theta_{k-1}$.
--   4. A **run of DIP** on a sample path: every price of episode $1$ lies in $(0, p_{\max})$, and in every episode $k \ge 2$ the prices are a run of Inner Algorithm B with estimate $\hat\theta_{k-1}$, $d = d_k$, $\delta = \delta_k$, $\beta_\tau = \beta^*_\tau$ at local time $\tau$, and regularization $\lambda$.
--
--   DIP alternates estimation of $\theta_0$ (from the previous episode) with UCB pricing on a grid (in the current episode); Theorem 1 bounds its expected regret.
--
--   **Formalization Note** Inner Algorithm A is not fixed to Algorithm 2 (logistic regression followed by the projection onto $\Theta$, p. 10): any measurable $\Theta$-valued estimator of the previous episode's data is admissible, and Algorithm 2 is one instance. The paper allows other linear classifiers (p. 10). The proof of Theorem 1 uses only that $\hat\theta_{k-1}$ is a function of the previous episode's data with $\|\hat\theta_{k-1}\|_1 \le W$. The first episode's prices are any predictable prices in $(0, p_{\max})$, which includes the paper's random prices. The run predicate covers the full nominal length of every episode; Algorithm 4's truncation of the last episode at $T$ only drops periods after $T$, which do not enter $R_T$.
-- source:
--   Luo, Sun and Liu, arXiv:2109.07340v2, p. 16, Algorithm 4; p. 9, Algorithm 1; p. 10, Algorithm 2; pp. 54–55, (6) and episode lengths

import Mathlib
import Definitions.Def_LuoSunLiu_DIP_Model
import Definitions.Def_LuoSunLiu_DIP_InnerB

open MeasureTheory

namespace LuoSunLiu.DIP

/-- The last period `α₁ + α₂(2^{k-1} - 1)` of episode `k ≥ 1` of the DIP policy (Algorithm 4,
p. 16; proof of Theorem 1, p. 54): episode `1` has length `ℓ₁ = α₁` and episode `k ≥ 2` has
length `ℓ_k = 2^{k-2} α₂`. -/
def epEnd (α1 α2 k : ℕ) : ℕ := α1 + α2 * (2 ^ (k - 1) - 1)

/-- The first period of episode `k ≥ 1`: `1` for `k = 1`, and `epEnd (k-1) + 1` for `k ≥ 2`. -/
def epStart (α1 α2 k : ℕ) : ℕ := if k ≤ 1 then 1 else epEnd α1 α2 (k - 1) + 1

/-- The nominal length of episode `k ≥ 1`: `ℓ₁ = α₁`, and `ℓ_k = 2^{k-2} α₂` for `k ≥ 2`. -/
def epLen (α1 α2 k : ℕ) : ℕ := if k ≤ 1 then α1 else 2 ^ (k - 2) * α2

/-- The number of episodes `n = n(T, α₁, α₂)` up to horizon `T`: the episode containing period
`T`, i.e. the least `k ≥ 1` with `T ≤ epEnd k`. For `T > α₁` it equals
`⌈log₂((T - α₁)/α₂ + 1)⌉ + 1` of (6), p. 54; for `T ≤ α₁` it is `1`. -/
noncomputable def nEp (α1 α2 T : ℕ) : ℕ := sInf {k : ℕ | 1 ≤ k ∧ T ≤ epEnd α1 α2 k}

/-- The discretization number `d_k = C ⌈(2^{k-2} ℓ₂)^{1/6}⌉` of episode `k ≥ 2` (Algorithm 4,
line 7), with `ℓ₂ = α₂` and `C = Cdisc`. -/
noncomputable def dEp (Cdisc α2 k : ℕ) : ℕ :=
  Cdisc * ⌈(((2 ^ (k - 2) * α2 : ℕ) : ℝ)) ^ ((1 : ℝ) / 6)⌉₊

/-- The confidence level `δ = 1/(2^{k-2} ℓ₂)` of episode `k ≥ 2` (Algorithm 4, line 7). -/
noncomputable def deltaEp (α2 k : ℕ) : ℝ := 1 / ((2 ^ (k - 2) * α2 : ℕ) : ℝ)

/-- An admissible Inner Algorithm A: for every episode `k`, a measurable map from the data
`(x_t, p_t, y_t)` of the `epLen k` periods of episode `k` to an estimate in
`Θ = {θ : ‖θ‖₁ ≤ W}`. Algorithm 2 (logistic regression followed by the projection `Proj_Θ`,
p. 10) is one such estimator. -/
def IsAdmissibleEstimator {d0 : ℕ} (M : PricingModel d0) (α1 α2 : ℕ)
    (est : (k : ℕ) → (Fin (epLen α1 α2 k) → (Fin d0 → ℝ) × ℝ × ℝ) → (Fin d0 → ℝ)) : Prop :=
  ∀ k, Measurable (est k) ∧ ∀ h, l1 (est k h) ≤ M.W

/-- The estimate `θ̂_k` computed by the estimator from the data of episode `k`; DIP uses
`θ̂_{k-1}` in episode `k`. -/
noncomputable def thetaHat {d0 : ℕ} (M : PricingModel d0) (α1 α2 : ℕ)
    (est : (k : ℕ) → (Fin (epLen α1 α2 k) → (Fin d0 → ℝ) × ℝ × ℝ) → (Fin d0 → ℝ))
    {Ω : Type*} (x : ℕ → Ω → Fin d0 → ℝ) (z p : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : Fin d0 → ℝ :=
  est k (fun i => (x (epStart α1 α2 k + i) ω, p (epStart α1 α2 k + i) ω,
    response M x z p (epStart α1 α2 k + i) ω))

/-- On the sample path `ω`, the prices are a run of the DIP policy (Algorithm 4, p. 16) with
inputs `α₁, α₂, p_max, C = Cdisc, λ, W` and Inner Algorithm A given by `est`, for every
tie-breaking rule: in episode `1` (periods `1, …, α₁`) every price lies in `(0, p_max)`; in every
episode `k ≥ 2` the prices are a run of Inner Algorithm B (`IsInnerBRun`) with estimate
`θ̂_{k-1}`, `d = d_k`, `δ = 1/(2^{k-2} ℓ₂)`, `β_τ = β*_τ` at local time `τ`, and regularization `λ`;
the UCB of episode `k` uses only that episode's data. -/
def IsDIPRun {d0 : ℕ} (M : PricingModel d0) (α1 α2 Cdisc : ℕ) (lam : ℝ)
    (est : (k : ℕ) → (Fin (epLen α1 α2 k) → (Fin d0 → ℝ) × ℝ × ℝ) → (Fin d0 → ℝ))
    {Ω : Type*} (x : ℕ → Ω → Fin d0 → ℝ) (z p : ℕ → Ω → ℝ) (ω : Ω) : Prop :=
  (∀ t ∈ Finset.Icc 1 α1, p t ω ∈ Set.Ioo 0 M.pmax) ∧
  ∀ k : ℕ, 2 ≤ k → ∃ j : ℕ → Fin (dEp Cdisc α2 k),
    IsInnerBRun M.pmax (thetaHat M α1 α2 est x z p (k - 1) ω) lam
      (fun τ => betaStar M.pmax lam (dEp Cdisc α2 k) (deltaEp α2 k) τ)
      (epEnd α1 α2 (k - 1)) (epLen α1 α2 k)
      (fun t => x t ω) j (fun t => p t ω) (fun t => response M x z p t ω)

end LuoSunLiu.DIP


