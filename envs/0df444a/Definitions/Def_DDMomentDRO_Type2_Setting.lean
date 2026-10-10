-- Prove2me | Definitions.Def_DDMomentDRO_Type2_Setting
-- name    : DDMomentDRO_Type2_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T12:44:39.263494+00:00
-- url     : https://prove2.me/theorems/a6e86c41-268d-42b2-aa95-730ecc7bad98
-- title:
--   (2), (10), (11), pp. 6, 10–11 — the stage data, the Type 2 mean–covariance ambiguity set, the stage values and the values of (11)
-- statement:
--   This module fixes one stage $t$ of the Bellman equations (2) of Yu and Shen under the Type 2 (mean and covariance) ambiguity set, and names the two sets of values that Theorem 2 compares.
--
--   **Stage data.** The state is $x_t\in\mathbb R^I$ and the stage variable is $y_t\in\mathbb R^{I\times J}$. The stage feasible set is $S=X_t(x_{t-1},\xi_t)$, a set of pairs $(x_t,y_t)$, and $g_t(x_t,y_t)$ is the stage cost. The next-stage uncertainty has the finite support $\Xi_{t+1}=\{\xi^1_{t+1},\dots,\xi^K_{t+1}\}\subset\mathbb R^J$ (Assumption 3), and $Q^k_{t+1}=Q_{t+1}(x_t,\xi^k_{t+1})$ is the next-stage value in scenario $k$. Finally $\mu(x_t)\in\mathbb R^J$ and $\Sigma(x_t)\in\mathbb R^{J\times J}$ are the decision-dependent mean and covariance.
--
--   **Type 2 ambiguity set** ((10) together with (C-18e)). For a state $x$,
--   $$
--   \mathcal P^{D_2}_{t+1}(x)=\Big\{p\in\mathbb R^K:\ \sum_{k=1}^K p_k=1,\ \ \sum_{k=1}^K p_k\xi^k_{t+1}=\mu(x),\ \ \sum_{k=1}^K p_k(\xi^k_{t+1}-\mu(x))(\xi^k_{t+1}-\mu(x))^\top=\Sigma(x),\ \ p\ge 0\Big\}.
--   $$
--
--   **Values of the Bellman equation (2).** The worst-case values at $x$ are the numbers $\sum_k p_kQ^k_{t+1}(x)$ with $p\in\mathcal P^{D_2}_{t+1}(x)$. The stage values are the numbers $g_t(x,y)+w$ with $(x,y)\in S$ such that the inner maximum $w=\max_{p\in\mathcal P^{D_2}_{t+1}(x)}\sum_kp_kQ^k_{t+1}(x)$ exists. The Bellman value $Q_t(x_{t-1},\xi_t)$ is the least of them, when one exists.
--
--   **Values of the joint program (11).** These are the numbers
--   $$
--   g_t(x,y)+s+u^\top\mu(x)+\Sigma(x)\bullet Y
--   $$
--   over $(x,y)\in S$, $s\in\mathbb R$, $u\in\mathbb R^J$ and $Y\in\mathbb R^{J\times J}$ satisfying (11b): $s+u^\top\xi^k_{t+1}+(\xi^k_{t+1}-\mu(x))(\xi^k_{t+1}-\mu(x))^\top\bullet Y\ge Q^k_{t+1}(x)$ for every $k$. Here $A\bullet B=\operatorname{trace}(A^\top B)$ is the Frobenius inner product (p. 5).
--
--   These objects are the vocabulary of Theorem 2 and of the two duality steps of its proof.
--
--   **Formalization Note** Indices are 0-based (`Fin K`, `Fin J`, `Fin I`). The covariance map is named `Sig`, because `Σ` is Lean's sum notation. The next-stage values are an arbitrary function `Qn x k` of the state and the scenario, because the stage theorem uses nothing about the recursion. Minima and maxima are expressed as least and greatest elements (`IsLeast`, `IsGreatest`), never as `sInf`/`sSup`. The constraint $p\ge0$ is not printed in (10), which also writes "$p\in\mathbb R^k$". It is the constraint (C-18e) of the paper's own proof, and Assumption 3 calls $p$ a probability, so it is part of the set here. $Y$ is a free real matrix with no sign or symmetry constraint, because (C-18d) is an equality. No symmetry or semidefiniteness is assumed of $\Sigma(x)$; where $\Sigma(x)$ is not symmetric the ambiguity set is empty.
-- source:
--   Yu & Shen, Multistage distributionally robust mixed-integer programming with decision-dependent moment-based ambiguity sets, arXiv:2002.12518v3, pp. 5–6, 10–11, 37, (2), Assumption 3, (10), (11), (C-18)

import Mathlib

namespace DDMomentDRO.Type2

open Matrix

/-- The Type 2 ambiguity set at the state `x`, (10) on p. 10 together with the nonnegativity
constraint (C-18e) on p. 37: the probability vectors `p` on the `K` support points `ξ k` whose
mean is `μ x` and whose covariance about `μ x` is `Sig x`. -/
def amb2 {I J K : ℕ} (ξ : Fin K → Fin J → ℝ) (μ : (Fin I → ℝ) → Fin J → ℝ)
    (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ) (x : Fin I → ℝ) : Set (Fin K → ℝ) :=
  {p | ∑ k, p k = 1 ∧
       ∑ k, p k • ξ k = μ x ∧
       ∑ k, p k • vecMulVec (ξ k - μ x) (ξ k - μ x) = Sig x ∧
       ∀ k, 0 ≤ p k}

/-- The objective values of the inner maximization of (2) at the state `x`:
`∑ₖ pₖ Q_{t+1}(x, ξᵏ)` for `p` in the Type 2 ambiguity set. -/
def wcVal {I J K : ℕ} (Qn : (Fin I → ℝ) → Fin K → ℝ) (ξ : Fin K → Fin J → ℝ)
    (μ : (Fin I → ℝ) → Fin J → ℝ) (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ)
    (x : Fin I → ℝ) : Set ℝ :=
  {v | ∃ p, p ∈ amb2 ξ μ Sig x ∧ v = ∑ k, p k * Qn x k}

/-- The values of the outer minimization of the Bellman equation (2): `g x y + w` over the
stage-feasible `(x, y) ∈ S` at which the inner maximum `w` (a greatest element of
`wcVal … x`) exists. -/
def stageVals {I J K : ℕ} (S : Set ((Fin I → ℝ) × (Fin I → Fin J → ℝ)))
    (g : (Fin I → ℝ) → (Fin I → Fin J → ℝ) → ℝ) (Qn : (Fin I → ℝ) → Fin K → ℝ)
    (ξ : Fin K → Fin J → ℝ) (μ : (Fin I → ℝ) → Fin J → ℝ)
    (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ) : Set ℝ :=
  {v | ∃ x y w, (x, y) ∈ S ∧ IsGreatest (wcVal Qn ξ μ Sig x) w ∧ v = g x y + w}

/-- The objective values (11a) of the joint minimization (11) on p. 11 at its feasible points:
`(x, y) ∈ S`, `s : ℝ`, `u : ℝʲ`, `Y : ℝ^{J×J}` (free), subject to (11b) for every `k`.
The Frobenius product `A • B = trace(AᵀB)` is written `(Aᵀ * B).trace`. -/
def dualVals2 {I J K : ℕ} (S : Set ((Fin I → ℝ) × (Fin I → Fin J → ℝ)))
    (g : (Fin I → ℝ) → (Fin I → Fin J → ℝ) → ℝ) (Qn : (Fin I → ℝ) → Fin K → ℝ)
    (ξ : Fin K → Fin J → ℝ) (μ : (Fin I → ℝ) → Fin J → ℝ)
    (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ) : Set ℝ :=
  {v | ∃ x y, ∃ s : ℝ, ∃ u : Fin J → ℝ, ∃ Y : Matrix (Fin J) (Fin J) ℝ,
       (x, y) ∈ S ∧
       (∀ k, Qn x k ≤ s + u ⬝ᵥ ξ k + ((vecMulVec (ξ k - μ x) (ξ k - μ x))ᵀ * Y).trace) ∧
       v = g x y + s + u ⬝ᵥ μ x + ((Sig x)ᵀ * Y).trace}

end DDMomentDRO.Type2


