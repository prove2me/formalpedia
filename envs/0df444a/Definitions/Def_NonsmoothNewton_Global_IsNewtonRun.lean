-- Prove2me | Definitions.Def_NonsmoothNewton_Global_IsNewtonRun
-- name    : NonsmoothNewton_Global_IsNewtonRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T00:07:27.920519+00:00
-- url     : https://prove2.me/theorems/1ff9bb6b-ef0d-41f3-9a1f-bdd66e70c2e8
-- title:
--   A run of the nonsmooth Newton iteration $x^{k+1}=x^k-V_k^{-1}F(x^k)$, $V_k\in\partial F(x^k)$ (3.2)
-- statement:
--   Let $E$ be a finite-dimensional real normed space and $F : E \to E$. A **run of the nonsmooth Newton method** (3.2) is a sequence of points $x^0, x^1, x^2, \dots$ in $E$ together with a sequence of linear maps $V_0, V_1, \dots$ such that for every $k \ge 0$
--
--   $$
--   V_k \in \partial F(x^k), \qquad V_k\,(x^{k+1} - x^k) = -F(x^k),
--   $$
--
--   where $\partial F$ is Clarke's generalized Jacobian. When $V_k$ is nonsingular the second condition is exactly $x^{k+1} = x^k - V_k^{-1}F(x^k)$. Any element of $\partial F(x^k)$ may be chosen at each step; convergence theorems for (3.2) hold for every such choice.
--
--   **Formalization Note** The iteration is encoded as a relation on sequences rather than as a function, because the choice of $V_k$ is free. Well-definedness (nonsingularity of each $V_k$) is a conclusion of the convergence theorems, not part of this definition.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), p. 358, Section 3, Eq. (3.2)

import Mathlib
import Definitions.Def_NonsmoothNewton_Global_clarkeJac

namespace NonsmoothNewton.Global

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A run of the nonsmooth Newton iteration (3.2), `x^{k+1} = x^k - V_k^{-1} F(x^k)` with
`V_k ∈ ∂F(x^k)` (Qi–Sun 1993, p. 358): at every step `V k ∈ ∂F(x k)` and the step solves the
Newton equation `V k (x (k+1) - x k) = - F (x k)`. Every choice of `V k` is allowed. -/
def IsNewtonRun (F : E → E) (x : ℕ → E) (V : ℕ → (E →L[ℝ] E)) : Prop :=
  ∀ k, V k ∈ clarkeJac F (x k) ∧ V k (x (k + 1) - x k) = -F (x k)

end NonsmoothNewton.Global


