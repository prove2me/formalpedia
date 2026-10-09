-- Prove2me | Definitions.Def_NonconvexAG_StochComposite_ProxMap
-- name    : NonconvexAG_StochComposite_ProxMap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:22:33.075168+00:00
-- url     : https://prove2.me/theorems/d48e9890-bb77-4113-a7a1-91dd0ab2c2e2
-- title:
--   (2.37), Assumption 2 and (2.38) — the prox map 𝒫, its boundedness, and the gradient mapping 𝒢
-- statement:
--   This file fixes the objects attached to the convex, possibly non-smooth term $\mathcal X$ of the composite problem
--   $$\min_{x\in\mathbb R^n}\ \Psi(x)+\mathcal X(x)$$
--   of Ghadimi and Lan, §2.2 and §3.2.
--
--   **The convex term on its domain.** The paper takes $\mathcal X$ to be a simple convex function with bounded domain, such as the indicator $\mathcal I_X$ of a convex compact set $X$, or $\mathcal I_X+\|\cdot\|_1$. Here $\mathcal X$ is described by its domain $K=\operatorname{dom}\mathcal X\subseteq\mathbb R^n$ and by its finite values $\mathcal X(u)$ for $u\in K$; off $K$ the paper's $\mathcal X$ is $+\infty$.
--
--   **The prox map (2.37).** For $x,y\in\mathbb R^n$ and $c>0$,
--   $$\mathcal P(x,y,c)\in\operatorname*{argmin}_{u\in\mathbb R^n}\Big\{\langle y,u\rangle+\frac1{2c}\|u-x\|^2+\mathcal X(u)\Big\}.$$
--   A map $P$ is a prox map for $(K,\mathcal X)$ when, for every $x,y$ and every $c>0$, the point $P(x,y,c)$ lies in $K$ and attains this minimum over $K$ (points outside $K$ have value $+\infty$ and never compete).
--
--   **Assumption 2.** There is a constant $M$ with $\|\mathcal P(x,y,c)\|\le M$ for every $c\in(0,+\infty)$ and all $x,y\in\mathbb R^n$.
--
--   **The gradient mapping (2.38).**
--   $$\mathcal G(x,y,c)=\frac1c\big[x-\mathcal P(x,y,c)\big].$$
--   With $y=\nabla\Psi(x)$ it is the gradient mapping at $x$; with $y=\bar G_k$, a stochastic estimate of $\nabla\Psi(x)$, it is the approximate stochastic gradient mapping of §3.2.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The space is `GhadimiLan.RSG.E n = EuclideanSpace ℝ (Fin n)` (published). The paper's extended-valued $\mathcal X$ is the pair `K : Set (E n)`, `X : E n → ℝ`; a real-valued $\mathcal X$ on all of $\mathbb R^n$ cannot satisfy Assumption 2 (as $c\to0$, $\mathcal P(x,y,c)\to x$ for every $x$), so the domain is essential. The prox map is a function `P x y c` together with the predicate `IsProxMap K X P`, which states membership in `K` and minimality over `K` for every `c > 0`; its values at `c ≤ 0` are unconstrained and never used. `Assumption2 P M` and `gradMap P x y c` are Assumption 2 and (2.38). Restated from mission 2 of this series, because drafts cannot import one another.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 2, (1.3); p. 9, Assumption 2 and (2.37); p. 10, (2.38)

import Mathlib
import Definitions.Def_GhadimiLan_RSG_Model

namespace NonconvexAG.StochComposite

open GhadimiLan.RSG (E)

/-- The prox map `𝒫` of (2.37), p. 9 (Ghadimi–Lan, arXiv:1310.3787v1), for the convex term `𝒳`.
`𝒳` is modelled on its domain: `K = dom 𝒳` and `X : E n → ℝ` gives the (finite) values of `𝒳`
on `K` (`𝒳 = +∞` off `K`). `IsProxMap K X P` says that for every `c > 0` and all `x, y`,
`P x y c` lies in `K` and is a minimizer over `K` (hence over `ℝⁿ`) of
`u ↦ ⟨y, u⟩ + ‖u − x‖² / (2c) + 𝒳(u)`. The values of `P` at `c ≤ 0` are unconstrained and never
used. -/
def IsProxMap {n : ℕ} (K : Set (E n)) (X : E n → ℝ) (P : E n → E n → ℝ → E n) : Prop :=
  ∀ x y : E n, ∀ c : ℝ, 0 < c →
    P x y c ∈ K ∧
      ∀ u ∈ K, inner ℝ y (P x y c) + ‖P x y c - x‖ ^ 2 / (2 * c) + X (P x y c) ≤
        inner ℝ y u + ‖u - x‖ ^ 2 / (2 * c) + X u

/-- Assumption 2, p. 9: `‖𝒫(x, y, c)‖ ≤ M` for every `c ∈ (0, +∞)` and all `x, y ∈ ℝⁿ`. -/
def Assumption2 {n : ℕ} (P : E n → E n → ℝ → E n) (M : ℝ) : Prop :=
  ∀ x y : E n, ∀ c : ℝ, 0 < c → ‖P x y c‖ ≤ M

/-- The gradient mapping `𝒢(x, y, c) := (1/c)[x − 𝒫(x, y, c)]` of (2.38), p. 10. -/
noncomputable def gradMap {n : ℕ} (P : E n → E n → ℝ → E n) (x y : E n) (c : ℝ) : E n :=
  (1 / c) • (x - P x y c)

end NonconvexAG.StochComposite


