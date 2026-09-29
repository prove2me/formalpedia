-- Prove2me | Definitions.Def_CubicNewton_Shared_IsCubicNewtonRun
-- name    : CubicNewton_Shared_IsCubicNewtonRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:15:36.984268+00:00
-- url     : https://prove2.me/theorems/5db3c3b8-1db9-4377-bb6e-e7b289eee029
-- title:
--   A run of the cubic regularization of Newton method (3.3)
-- statement:
--   Let $f$ be twice differentiable with gradient $f'$ and Hessian $f''$, and let $0 < L_0 \le L$. A pair of sequences $\{x_k\}_{k \ge 0} \subseteq \mathbb{R}^n$ and $\{M_k\}_{k \ge 0} \subseteq \mathbb{R}$ is a **run of method (3.3)** from $x_0$ if $x_0$ is the first iterate and, for every $k \ge 0$,
--
--   1. $M_k \in [L_0, 2L]$;
--   2. $x_{k+1} = T_{M_k}(x_k)$ is a global minimizer of the cubic model at $x_k$ with parameter $M_k$;
--   3. the acceptance test holds:
--   $$f(x_{k+1}) \le \bar f_{M_k}(x_k), \qquad \bar f_{M}(x) = f(x) + \min_y \Big[\langle f'(x), y - x\rangle + \tfrac12\langle f''(x)(y - x), y - x\rangle + \tfrac{M}{6}\|y - x\|^3\Big].$$
--
--   Since $\bar f_M(x) \le f(x)$, every run is monotone: $f(x_{k+1}) \le f(x_k)$. If $L$ is known one may take $M_k \equiv L$.
--
--   Used by three missions of this paper, all of which analyse method (3.3), p. 184: 01-nonconvex (Theorem 1, Section 3, pp. 184–185), 02-star-convex (Theorem 4, Section 4.1, pp. 188–189) and 03-gradient-dominated (Theorem 7, Section 4.2, p. 194).
--
--   **Formalization Note** The iteration index is 0-based, as in the paper. Because $x_{k+1}$ is a global minimizer of the cubic model, $\bar f_{M_k}(x_k)$ is written as $f(x_k)$ plus the model value at $x_{k+1}$, so no infimum over an unbounded set is taken.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 184, Section 3, method (3.3)

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

namespace CubicNewton.Shared

/-- A run of the cubic regularization of Newton method (3.3) (Nesterov–Polyak 2006, p. 184) with
parameters `0 < L₀ ≤ L`, started at `x₀`: iterates `x 0 = x₀, x 1, …` (0-based, as in the paper)
and regularization parameters `M 0, M 1, …` such that at every iteration `k ≥ 0`
1. `M k ∈ [L₀, 2L]`;
2. `x (k+1)` is a global minimizer of the cubic model at `x k` with parameter `M k`, i.e. the
   paper's `T_{M_k}(x_k)` (any choice among the global minima);
3. the acceptance test `f(T_{M_k}(x_k)) ≤ f̄_{M_k}(x_k)` holds, where
   `f̄_{M_k}(x_k) = f(x_k) + min_y cubicModel = f(x_k) + cubicModel … (x k) (x (k+1))` because
   `x (k+1)` attains the minimum. -/
structure IsCubicNewtonRun {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L₀ L : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (M : ℕ → ℝ) : Prop where
  init : x 0 = x₀
  param_mem : ∀ k, M k ∈ Set.Icc L₀ (2 * L)
  step : ∀ k, IsCubicStep g H (M k) (x k) (x (k + 1))
  accept : ∀ k, f (x (k + 1)) ≤ f (x k) + cubicModel g H (M k) (x k) (x (k + 1))

end CubicNewton.Shared


