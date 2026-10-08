-- Prove2me | Definitions.Def_BoydADMM_Constrained_Run
-- name    : BoydADMM_Constrained_Run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T02:06:58.735832+00:00
-- url     : https://prove2.me/theorems/cf00af92-d5ce-42de-9c90-836ac1a7799d
-- title:
--   Parallel projection ADMM iteration of §5.1.2
-- statement:
--   Given $N$ sets $\mathcal A_i\subseteq\mathbb R^n$, a parallel projection run consists of block vectors $x^k=(x_i^k)$ and $u^k=(u_i^k)$ and common vectors $z^k$ satisfying, for every $k\ge0$ and every $i$,
--
--   $$x_i^{k+1}=\Pi_{\mathcal A_i}(z^k-u_i^k),\qquad z^{k+1}=\frac1N\sum_{i=1}^N(x_i^{k+1}+u_i^k),\qquad u_i^{k+1}=u_i^k+x_i^{k+1}-z^{k+1}.$$
--
--   This is the iteration used to find a common point of the sets through product-space feasibility. Its initial $z^0$ and $u^0$ may be arbitrary.
--
--   **Formalization Note** Projection is the published nearest-point relation `RandomGradFree.Nonsmooth.IsMetricProjection`; the definition requires $N\ge1$ and each displayed update but does not assert that a run exists. The value $x^0$ is unused, as on the page.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 35, §5.1.2, parallel-projection iteration; https://doi.org/10.1561/2200000016

import Mathlib
import Definitions.Def_BoydADMM_Constrained_Geometry

namespace BoydADMM.Constrained

/-- The three displayed updates of parallel projection ADMM in §5.1.2, p. 35.
The starting values `z 0` and `u 0` are arbitrary; `x 0` is unused. -/
structure IsParallelRun {N n : ℕ} (A : Fin N → Set (Vec n))
    (x : ℕ → Blocks N n) (z : ℕ → Vec n) (u : ℕ → Blocks N n) : Prop where
  Npos : 0 < N
  x_project : ∀ k i, RandomGradFree.Nonsmooth.IsMetricProjection
    (A i) (z k - u k i) (x (k + 1) i)
  z_average : ∀ k, z (k + 1) = avg (fun i => x (k + 1) i + u k i)
  u_update : ∀ k i, u (k + 1) i = u k i + x (k + 1) i - z (k + 1)

end BoydADMM.Constrained


