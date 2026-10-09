-- Prove2me | Definitions.Def_StochModelWC_ProxSubgrad_Algorithm31
-- name    : StochModelWC_ProxSubgrad_Algorithm31
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:46:01.09541+00:00
-- url     : https://prove2.me/theorems/b8bd1ffb-39ba-4fc6-a1ee-0a6e08d6c329
-- title:
--   Algorithm 3.1 — the proximal stochastic subgradient iterates
-- statement:
--   **Algorithm 3.1** (proximal stochastic subgradient method). Input: $x_0 \in \operatorname{dom} r$, stepsizes $\alpha_t \ge 0$ and an iteration count. At step $t$, sample $\xi_t \sim P$ and set
--   $$x_{t+1} = \operatorname{prox}_{\alpha_t r}\big(x_t - \alpha_t G(x_t, \xi_t)\big).$$
--
--   This definition records the iterates along a finite sample path $(\xi_0, \dots, \xi_{N-1})$: $x_0$ is the starting point, $x_{t+1}$ is given by the update above for $t < N$, and the sequence is frozen afterwards. The proximal map enters as a function $\mathrm{prox}(a, z)$; every theorem that uses the iterates requires that $\mathrm{prox}(a, z)$ is a proximal point of $a\,r$ at $z$ for every $a > 0$, which determines it uniquely because $r$ is closed and convex.
--
--   The output step of Algorithm 3.1 (sample $t^* \in \{0,\dots,T\}$ with $P(t^* = t) = \alpha_t / \sum_{i=0}^T \alpha_i$ and return $x_{t^*}$) is not part of this definition; the theorems express $\mathbb E[\cdot(x_{t^*})]$ as the corresponding $\alpha$-weighted average.
-- source:
--   Davis–Drusvyatskiy, Stochastic Model-Based Minimization of Weakly Convex Functions, arXiv:1803.06523v3, p. 12, Algorithm 3.1

import Mathlib
import Definitions.Def_StochModelWC_ProxSubgrad_Basic

open MeasureTheory Filter Topology

namespace StochModelWC.ProxSubgrad

/-- Algorithm 3.1 (p. 12), the proximal stochastic subgradient method, along a finite sample path
`ω = (ξ₀, …, ξ_{N-1})`: `x₀ = x0` and `x_{t+1} = prox (α t) (x_t − α t • G(x_t, ξ_t))` for `t < N`.
`prox a z` is a selection of `prox_{a r}(z)`; every theorem ties it to `r` by `IsProxPt`. -/
noncomputable def proxSGIter {d : ℕ} {Ω : Type*}
    (prox : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (G : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d)) (α : ℕ → ℝ)
    (x0 : EuclideanSpace ℝ (Fin d)) {N : ℕ} (ω : Fin N → Ω) : ℕ → EuclideanSpace ℝ (Fin d) :=
  StochModelWC.ModelBased.run (fun t x ξ => prox (α t) (x - α t • G x ξ)) x0 ω

end StochModelWC.ProxSubgrad


