-- Prove2me | Definitions.Def_StochModelWC_ProjSubgrad_Algorithm31Proj
-- name    : StochModelWC_ProjSubgrad_Algorithm31Proj
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T00:34:12.786577+00:00
-- url     : https://prove2.me/theorems/8634782a-3166-4bbf-bf1a-009e81be3669
-- title:
--   Algorithm 3.1 with r = δ_X — nearest-point projection and the projected stochastic subgradient iterates
-- statement:
--   Let $X \subseteq \mathbb R^d$ be nonempty, closed and convex. For every $z$ there is a unique nearest point $\operatorname{proj}_X(z)$ of $X$ to $z$; it is the proximal map $\operatorname{prox}_{\alpha r}$ of the indicator $r = \delta_X$ for every $\alpha \ge 0$ (p. 13).
--
--   **Algorithm 3.1** (proximal stochastic subgradient method) with $r = \delta_X$ is the **projected stochastic subgradient method**: from $x_0 \in X$, with stepsizes $\alpha_t \ge 0$, at step $t$ sample $\xi_t \sim P$ and set
--   $$x_{t+1} = \operatorname{proj}_X\big(x_t - \alpha_t G(x_t, \xi_t)\big).$$
--
--   This definition records the iterates along a finite sample path $(\xi_0, \dots, \xi_{N-1})$: $x_0$ is the starting point, $x_{t+1}$ is given by the update above for $t < N$, and the sequence is frozen afterwards. The projection enters as a function $\mathrm{proj}(z)$; every theorem that uses the iterates requires that $\mathrm{proj}(z)$ is a nearest point of $X$ to $z$ for every $z$ (the published predicate `SpectralProjGrad.Shared.IsProjOnto`), which determines it uniquely.
--
--   The output step of Algorithm 3.1 (sample $t^* \in \{0,\dots,T\}$ with $P(t^* = t) = \alpha_t / \sum_{i=0}^T \alpha_i$ and return $x_{t^*}$) is not part of this definition; the theorems express $\mathbb E[\cdot(x_{t^*})]$ as the corresponding $\alpha$-weighted average.
--
--   **Formalization Note.** The projection is constrained by the nearest-point predicate rather than by the proximal-point predicate of $\alpha_t\delta_X$, because Algorithm 3.1 allows $\alpha_t = 0$, where the weight $1/(2\alpha_t)$ of the proximal subproblem is not defined (in Lean $1/0 = 0$, which would accept any point of $X$).
-- source:
--   Davis–Drusvyatskiy, Stochastic Model-Based Minimization of Weakly Convex Functions, arXiv:1803.06523v3, p. 12, Algorithm 3.1; p. 13, §3.1 (r the indicator of X, prox becomes proj_X)

import Mathlib
import Definitions.Def_StochModelWC_ProjSubgrad_Basic

open MeasureTheory Filter Topology

namespace StochModelWC.ProjSubgrad

/-- Algorithm 3.1 (p. 12) with `r = δ_X` (§3.1, p. 13), the projected stochastic subgradient method, along a
finite sample path `ω = (ξ₀, …, ξ_{N-1})`: `x₀ = x0` and `x_{t+1} = proj (x_t − α t • G(x_t, ξ_t))` for `t < N`.
`proj z` is a selection of `proj_X(z)`; every theorem ties it to `X` by the published
`SpectralProjGrad.Shared.IsProjOnto X proj` (nearest-point projection). -/
noncomputable def projSGIter {d : ℕ} {Ω : Type*}
    (proj : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (G : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d)) (α : ℕ → ℝ)
    (x0 : EuclideanSpace ℝ (Fin d)) {N : ℕ} (ω : Fin N → Ω) : ℕ → EuclideanSpace ℝ (Fin d) :=
  run (fun t x ξ => proj (x - α t • G x ξ)) x0 ω

end StochModelWC.ProjSubgrad


