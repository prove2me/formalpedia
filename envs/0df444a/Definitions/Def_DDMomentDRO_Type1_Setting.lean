-- Prove2me | Definitions.Def_DDMomentDRO_Type1_Setting
-- name    : DDMomentDRO_Type1_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T12:44:36.095521+00:00
-- url     : https://prove2.me/theorems/cb4ae3de-1b70-45fb-8559-096e7fb5dc60
-- title:
--   (2), (3), (4), (C-17), pp. 5–8, 36 — stage data, the Type 1 moment-bound ambiguity set, stage values and LP-dual values
-- statement:
--   This file fixes the objects of one stage $t$ of the Bellman equation (2) of Yu and Shen under the discrete Type 1 ambiguity set (3).
--
--   **Stage data.** The state is $x\in\mathbb R^I$ (binary on the page), the stage variable is $y\in\mathbb R^{I\times J}$, the stage feasible set is $S=X_t(x_{t-1},\xi_t)$, a set of pairs $(x,y)$, and $g(x,y)$ is the stage cost. The next-stage uncertainty has the finite, decision-independent support $\{\xi^1,\dots,\xi^K\}\subset\mathbb R^J$ (Assumption 3), and $Q^k(x)=Q_{t+1}(x,\xi^k)$ is the next-stage value at scenario $k$.
--
--   **Moment functions.** For an exponent matrix $e=(k_{sj})\in\mathbb N^{m\times J}$, the $s$-th moment function is
--   $$f_s(z)=\prod_{j=1}^J z_j^{\,k_{sj}},\qquad s=1,\dots,m.$$
--
--   **Type 1 ambiguity set.** Given decision-dependent bounds $l(x),u(x)\in\mathbb R^m$ and $\underline p(x),\bar p(x)\in\mathbb R^K$,
--   $$\mathcal P^{D_1}(x)=\Big\{p\in\mathbb R^K\ :\ \underline p(x)\le p\le \bar p(x),\ \ l(x)\le \sum_{k=1}^K p_k f(\xi^k)\le u(x),\ \ p\ge 0\Big\},$$
--   with all inequalities componentwise.
--
--   **Inner and outer values.** The inner values at $x$ are $\{\sum_k p_kQ^k(x) : p\in\mathcal P(x)\}$ for an ambiguity map $\mathcal P$; its greatest element, when it exists, is the worst-case expectation $w(x)$. The stage values are $g(x,y)+w(x)$ over $(x,y)\in S$ at which this maximum is attained. The stage value $Q_t$ of (2) is the least stage value.
--
--   **Dual values (4).** A point $(\alpha,\beta,\underline\gamma,\bar\gamma)\in\mathbb R^m\times\mathbb R^m\times\mathbb R^K\times\mathbb R^K$ is dual feasible at $x$ when $\alpha,\beta,\underline\gamma,\bar\gamma\ge0$ and
--   $$(-\alpha+\beta)^{\mathsf T} f(\xi^k)-\underline\gamma_k+\bar\gamma_k\ \ge\ Q^k(x)\qquad\text{for every }k.$$
--   The dual values are
--   $$g(x,y)-\alpha^{\mathsf T}l(x)+\beta^{\mathsf T}u(x)-\underline\gamma^{\mathsf T}\underline p(x)+\bar\gamma^{\mathsf T}\bar p(x)$$
--   over $(x,y)\in S$ and dual feasible points at $x$: the objective values of the joint program (4).
--
--   These are the objects of Theorem 1 and of the weak and strong duality statements for the inner LP (C-17).
--
--   **Formalization Note** Indices are $0$-based (`Fin K`, `Fin m`). The set (3) as printed has no $p\ge0$; the definition includes it, as the proof's (C-17f) does and as Assumption 3 (probabilities) requires. No $\sum_k p_k=1$ is imposed: the page obtains it by taking one moment function $\equiv 1$ with bounds $1$. The next-stage values $Q^k$ are an arbitrary real function of $(x,k)$, because Theorem 1 uses nothing about them. Minima and maxima are encoded by `IsLeast` / `IsGreatest`, so they include attainment and never default to a junk value. $(-\alpha+\beta)^{\mathsf T}f$ is written `(β - α) ⬝ᵥ f`.
-- source:
--   Yu & Shen, Multistage distributionally robust mixed-integer programming with decision-dependent moment-based ambiguity sets, arXiv:2002.12518v3, pp. 5–8, 36, (2), Assumption 3, (3), (4), (C-17)

import Mathlib

namespace DDMomentDRO.Type1

open Matrix

/-- The moment functions of p. 7: `momentFn e z s = ∏ⱼ (z j) ^ (e s j)`, i.e.
`f_s(ξ) = (ξ₁)^{k_{s1}} ⋯ (ξ_J)^{k_{sJ}}` with exponent matrix `e s j = k_{sj}`. -/
def momentFn {J m : ℕ} (e : Fin m → Fin J → ℕ) (z : Fin J → ℝ) : Fin m → ℝ :=
  fun s => ∏ j, z j ^ e s j

/-- The discrete Type 1 ambiguity set (3) at the state `x`, in the form (C-17b)–(C-17f) used by
the proof of Theorem 1: probability vectors `p ∈ ℝ^K` with `p̲(x) ≤ p ≤ p̄(x)`,
`l(x) ≤ ∑ₖ pₖ f(ξᵏ) ≤ u(x)` (componentwise) and `p ≥ 0`. -/
def amb1 {I J K m : ℕ} (ξ : Fin K → Fin J → ℝ) (e : Fin m → Fin J → ℕ)
    (l u : (Fin I → ℝ) → Fin m → ℝ) (pl pu : (Fin I → ℝ) → Fin K → ℝ)
    (x : Fin I → ℝ) : Set (Fin K → ℝ) :=
  {p | pl x ≤ p ∧ p ≤ pu x ∧
    l x ≤ ∑ k, p k • momentFn e (ξ k) ∧ ∑ k, p k • momentFn e (ξ k) ≤ u x ∧
    ∀ k, 0 ≤ p k}

/-- The values of the inner problem of (2) at the state `x`: `∑ₖ pₖ Q_{t+1}(x, ξᵏ)` over
`p ∈ amb x`. Its greatest element (if any) is the worst-case expectation. -/
def wcVal {I K : ℕ} (amb : (Fin I → ℝ) → Set (Fin K → ℝ))
    (Qn : (Fin I → ℝ) → Fin K → ℝ) (x : Fin I → ℝ) : Set ℝ :=
  {v | ∃ p, p ∈ amb x ∧ v = ∑ k, p k * Qn x k}

/-- The values of the outer problem of the Bellman equation (2): `g(x, y) + w` over
`(x, y) ∈ S`, where `w` is the (attained) maximum of `wcVal amb Qn x`. The stage value
`Q_t = q` is `IsLeast (stageVals S g amb Qn) q`. -/
def stageVals {I J K : ℕ} (S : Set ((Fin I → ℝ) × (Fin I → Fin J → ℝ)))
    (g : (Fin I → ℝ) → (Fin I → Fin J → ℝ) → ℝ)
    (amb : (Fin I → ℝ) → Set (Fin K → ℝ)) (Qn : (Fin I → ℝ) → Fin K → ℝ) : Set ℝ :=
  {v | ∃ x y w, (x, y) ∈ S ∧ IsGreatest (wcVal amb Qn x) w ∧ v = g x y + w}

/-- The dual part of the objective (4a): `−αᵀl(x) + βᵀu(x) − γ̲ᵀp̲(x) + γ̄ᵀp̄(x)`. -/
def dualObj1 {I K m : ℕ} (l u : (Fin I → ℝ) → Fin m → ℝ) (pl pu : (Fin I → ℝ) → Fin K → ℝ)
    (x : Fin I → ℝ) (α β : Fin m → ℝ) (γl γu : Fin K → ℝ) : ℝ :=
  -(α ⬝ᵥ l x) + β ⬝ᵥ u x - γl ⬝ᵥ pl x + γu ⬝ᵥ pu x

/-- Dual feasibility (4b), (4d) at the state `x`: `α, β, γ̲, γ̄ ≥ 0` and
`(−α + β)ᵀf(ξᵏ) − γ̲ₖ + γ̄ₖ ≥ Q_{t+1}(x, ξᵏ)` for every `k`. -/
def DualFeas1 {I J K m : ℕ} (Qn : (Fin I → ℝ) → Fin K → ℝ) (ξ : Fin K → Fin J → ℝ)
    (e : Fin m → Fin J → ℕ) (x : Fin I → ℝ) (α β : Fin m → ℝ) (γl γu : Fin K → ℝ) : Prop :=
  0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γl ∧ 0 ≤ γu ∧
    ∀ k, Qn x k ≤ (β - α) ⬝ᵥ momentFn e (ξ k) - γl k + γu k

/-- The objective values (4a) of the joint program (4) at its feasible points (4b)–(4d). -/
def dualVals1 {I J K m : ℕ} (S : Set ((Fin I → ℝ) × (Fin I → Fin J → ℝ)))
    (g : (Fin I → ℝ) → (Fin I → Fin J → ℝ) → ℝ) (Qn : (Fin I → ℝ) → Fin K → ℝ)
    (ξ : Fin K → Fin J → ℝ) (e : Fin m → Fin J → ℕ)
    (l u : (Fin I → ℝ) → Fin m → ℝ) (pl pu : (Fin I → ℝ) → Fin K → ℝ) : Set ℝ :=
  {v | ∃ x y α β γl γu, (x, y) ∈ S ∧ DualFeas1 Qn ξ e x α β γl γu ∧
    v = g x y + dualObj1 l u pl pu x α β γl γu}

end DDMomentDRO.Type1


