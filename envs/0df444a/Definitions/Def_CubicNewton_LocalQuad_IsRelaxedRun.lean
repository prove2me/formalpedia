-- Prove2me | Definitions.Def_CubicNewton_LocalQuad_IsRelaxedRun
-- name    : CubicNewton_LocalQuad_IsRelaxedRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:33:00.181429+00:00
-- url     : https://prove2.me/theorems/6ca9af65-5149-419b-8358-b2adbfd3b346
-- title:
--   A run of the relaxed cubic regularization of Newton method (3.5)
-- statement:
--   Let $f$ be twice differentiable on $\mathbb{R}^n$ with gradient $f'$ and Hessian $f''$, and let $L > 0$. A pair of sequences $\{x_k\}_{k \ge 0} \subseteq \mathbb{R}^n$ and $\{M_k\}_{k \ge 0} \subseteq \mathbb{R}$ is a **run of the relaxed method (3.5)** if for every $k \ge 0$
--
--   1. $M_k \in (0, 2L]$;
--   2. $x_{k+1} = T_{M_k}(x_k)$, i.e. $x_{k+1}$ is a global minimizer of the cubic model of $f$ at $x_k$ with parameter $M_k$:
--   $$x_{k+1} \in \operatorname{Arg\,min}_y \Big[\langle f'(x_k), y - x_k\rangle + \tfrac12\langle f''(x_k)(y - x_k), y - x_k\rangle + \tfrac{M_k}{6}\|y - x_k\|^3\Big].$$
--
--   The starting point is $x_0$. In contrast with method (3.3) there is no positive lower bound $L_0$ on $M_k$ and no acceptance test $f(x_{k+1}) \le \bar f_{M_k}(x_k)$, so the method need not decrease $f$; it is analyzed only near a non-degenerate local minimum.
--
--   **Formalization Note** The iteration index is 0-based, as in the paper. The run is given by the two sequences; $x_0$ is `x 0`.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 186, Section 3, relaxed method (3.5)

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

namespace CubicNewton.LocalQuad

/-- A run of the relaxed cubic regularization of Newton method (3.5) (Nesterov–Polyak 2006,
Section 3, p. 186): iterates `x 0, x 1, …` (0-based, as in the paper; `x 0` is the starting point)
and parameters `M 0, M 1, …` such that for every `k ≥ 0`
1. `M k ∈ (0, 2L]`;
2. `x (k+1) = T_{M k}(x k)` is a global minimizer of the cubic model at `x k` with parameter
   `M k` (any choice among the global minima).
Unlike method (3.3) there is no lower bound `L₀` on `M k` and no acceptance test. -/
def IsRelaxedRun {n : ℕ} (L : ℝ) (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (M : ℕ → ℝ) : Prop :=
  ∀ k, M k ∈ Set.Ioc 0 (2 * L) ∧ CubicNewton.Shared.IsCubicStep g H (M k) (x k) (x (k + 1))

end CubicNewton.LocalQuad


