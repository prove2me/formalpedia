-- Prove2me | Definitions.Def_GhostPenalty_posMax
-- name    : GhostPenalty_posMax
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:33:58.046546+00:00
-- url     : https://prove2.me/theorems/e6c7fafd-fc8e-4513-81cd-84ad67fba384
-- title:
--   Maximal constraint violation $\max_i\{g_i(x)_+\}$
-- statement:
--   For constraint functions $g_1,\dots,g_m:\mathbb R^n\to\mathbb R$ and a point $x\in\mathbb R^n$, the **maximal constraint violation** is
--   $$\max_i\{g_i(x)_+\}=\max_{1\le i\le m}\max\{g_i(x),0\},\qquad \alpha_+\triangleq\max\{0,\alpha\}.$$
--   It is zero exactly at the points satisfying $g(x)\le 0$, and it is the objective of the violation problem (4) and the penalty term of the ghost penalty $W$.
--
--   **Formalization Note** The maximum over $i$ is a real supremum over `Fin m`; for $m=0$ it equals $0$, the violation of a problem without constraints.
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, §1, p.2; (4), p.5

import Mathlib

namespace GhostPenalty

/-- **Maximal constraint violation** `max_i {g_i(x)₊}`.
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, §1, p.2 ("`W(x;ε) ≜ f(x) + (1/ε) max_i {g_i(x)+}`, where
`α+ ≜ max{0,α}`") and problem (4), p.5.

For constraint functions `g₁, …, g_m : ℝⁿ → ℝ` and a point `x`, `posMax g x` is the largest
positive part `max_i max{g_i(x), 0}`.

**Formalization Note.** The maximum over `i ∈ {1,…,m}` is the real supremum `⨆ i : Fin m`,
which over a finite index type is the maximum. For `m = 0` it is `0`, the value of
`max_i {g_i(x)₊}` when there are no constraints (every point is feasible). -/
noncomputable def posMax {n m : ℕ} (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⨆ i, max (g i x) 0

end GhostPenalty


