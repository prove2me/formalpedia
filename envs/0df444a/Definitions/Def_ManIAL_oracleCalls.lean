-- Prove2me | Definitions.Def_ManIAL_oracleCalls
-- name    : ManIAL_oracleCalls
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:03.835596+00:00
-- url     : https://prove2.me/theorems/b0141c16-2f17-4f99-90cd-fbda4d7c4446
-- title:
--   First-order oracle calls of ManIAL through outer iteration $K$
-- statement:
--   A **first-order oracle call** (Definition 3.7) computes the Euclidean gradient $\nabla f(x)$, the proximal operator of $h$ and the retraction. If outer iteration $k$ of ManIAL uses $N_k$ gradient evaluations in its subroutine plus one proximal step for $y^{k+1}$, the number of oracle calls through outer iteration $K$ is
--
--   $$
--   \sum_{k=0}^{K}(N_k+1).
--   $$
--
--   This is the quantity bounded in Theorem 3.8.
--
--   **Formalization Note** The count is at least the number $\sum_k T_k$ of inner RGD iterations counted in the proof of Theorem 3.8, so a bound on it implies the paper's.
-- source:
--   Deng, Hu, Wu & Wen, Oracle complexities of augmented Lagrangian methods for nonsmooth manifold optimization, arXiv:2404.05121v2, Definition 3.7, p.14; proof of Theorem 3.8, p.14

import Mathlib

namespace ManIAL

/-- The number of first-order oracle calls (Definition 3.7, Deng–Hu–Wu–Wen,
arXiv:2404.05121v2, p.14: one call computes `∇f(x)`, `prox_h(x)` and the retraction) of outer
iterations `0, …, K` of ManIAL: `Σ_{k=0}^{K} (N_k + 1)`, where `N_k` is the number of gradient
evaluations of the subroutine in outer iteration `k` and the `+1` is the proximal step that
computes `y^{k+1}`.

**Formalization Note.** This count is at least the paper's count `Σ_k T_k` of inner RGD
iterations (proof of Theorem 3.8), so a bound on it is the stronger statement. -/
def oracleCalls (N : ℕ → ℕ) (K : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (K + 1), (N k + 1)

end ManIAL


