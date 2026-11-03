-- Prove2me | Definitions.Def_NearestDSM_newtonStep
-- name    : NearestDSM_newtonStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:19:48.675937+00:00
-- url     : https://prove2.me/theorems/50741ba3-7804-4299-81a7-389ead0509df
-- title:
--   One step of Algorithm 3.1 (modified semismooth Newton method)
-- statement:
--   Algorithm 3.1 (A Modified Semismooth Newton Method) runs, from an initial point $y^0$ and a tolerance $\mathrm{tol}$:
--
--   1. while $\|F(y^k)\|>\mathrm{tol}$:
--   2. find a vertex $\tilde y^k$ of $[y^k]$;
--   3. compute the maximal $\tilde V_k\in\partial F(\tilde y^k)$;
--   4. update $y^{k+1}=\tilde y^k-\tilde V_k^{-1}F(\tilde y^k)$.
--
--   With $\mathrm{tol}=0$ and a vertex selector $\sigma$, one step is
--   $$
--   y\ \mapsto\ \begin{cases} y, & F(y)=0,\\ \sigma(y)-V(M_{\max}(\sigma(y)))^{-1}F(\sigma(y)), & F(y)\ne 0,\end{cases}
--   $$
--   so that a run of the algorithm is a sequence with $y^{k+1}=\text{step}(y^k)$ that stays put once it reaches a solution.
--
--   **Formalization Note** The inverse is Mathlib's matrix inverse, which is $0$ for a singular matrix. That value never occurs: $\sigma(y)$ is a vertex of its class, so the maximal $V$ there is nonsingular (Corollary 3.11).
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, Algorithm 3.1, p.20

import Mathlib
import Definitions.Def_NearestDSM_Fres
import Definitions.Def_NearestDSM_Vmat
import Definitions.Def_NearestDSM_Mmax
open Matrix

namespace NearestDSM

/-- One pass of the while-loop of Algorithm 3.1 (A Modified Semismooth Newton Method),
Hu, Im, Li & Wolkowicz, *A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem*, arXiv:2107.09631v1, p.20, with tolerance `tol = 0` and vertex selector `σ`:
if `F(y) = 0` the loop has stopped and the iterate stays `y`; otherwise `ỹ = σ(y)` is a vertex of
`[y]`, `Ṽ = V(M)` with `M` the maximal matrix at `ỹ`, and the next iterate is `ỹ − Ṽ⁻¹ F(ỹ)`.

**Formalization Note.** `while ‖F(y^k)‖ > tol` with `tol = 0` stops exactly when `F(y^k) = 0`; a
run of the algorithm is a sequence with `y (k+1) = newtonStep Xh σ (y k)`. `⁻¹` is `Matrix.inv`,
which returns `0` on a singular matrix. That value never occurs in a run: `σ y` is a vertex of its
class, so `V(Mmax)` there is nonsingular (Corollary 3.11). -/
noncomputable def newtonStep {n : ℕ} (Xh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (σ : Dual n → Dual n) (y : Dual n) : Dual n :=
  if Fres Xh y = 0 then y
  else σ y - WithLp.toLp 2 ((Vmat (Mmax Xh (σ y)))⁻¹ *ᵥ WithLp.ofLp (Fres Xh (σ y)))

end NearestDSM


