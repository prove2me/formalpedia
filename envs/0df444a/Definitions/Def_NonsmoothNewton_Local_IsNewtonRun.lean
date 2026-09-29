-- Prove2me | Definitions.Def_NonsmoothNewton_Local_IsNewtonRun
-- name    : NonsmoothNewton_Local_IsNewtonRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T00:00:51.333978+00:00
-- url     : https://prove2.me/theorems/ae88e003-30b9-4e69-8aa5-8c5e2051a690
-- title:
--   A run of the nonsmooth Newton iteration $x^{k+1}=x^k-V_k^{-1}F(x^k)$, $V_k\in\partial F(x^k)$ (3.2)
-- statement:
--   Let $E$ be a real normed space and $F : E \to E$. A **run of the nonsmooth Newton method** (3.2) is a sequence of points $(x^k)_{k \ge 0}$ in $E$ together with a sequence of linear maps $(V_k)_{k \ge 0}$ such that, for every $k$,
--
--   $$
--   V_k \in \partial F(x^k) \qquad\text{and}\qquad V_k\,(x^{k+1} - x^k) = -F(x^k).
--   $$
--
--   When $V_k$ is nonsingular the second condition is exactly the update $x^{k+1} = x^k - V_k^{-1} F(x^k)$. Every choice of $V_k$ in the generalized Jacobian is allowed; theorems about the method are statements about all runs.
--
--   **Formalization Note** The update is written as a linear equation rather than with an inverse, so that no junk value of a "generalized inverse" can make a singular step look well defined. Nonsingularity of the $V_k$ ("the iteration is well defined") is then a conclusion of the convergence theorem, not part of the definition.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), p. 358, Section 3, Eq. (3.2)

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac

namespace NonsmoothNewton.Local

/-- A run of the nonsmooth Newton iteration (3.2) of Qi–Sun (1993), p. 358:
`x^{k+1} = x^k - V_k⁻¹ F(x^k)` with `V_k ∈ ∂F(x^k)`, written without an inverse as the linear
equation `V_k (x^{k+1} - x^k) = -F(x^k)`. Every choice of `V_k ∈ ∂F(x^k)` is allowed. -/
def IsNewtonRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (x : ℕ → E) (V : ℕ → E →L[ℝ] E) : Prop :=
  ∀ k, V k ∈ NonsmoothNewton.Shared.clarkeJac F (x k) ∧ V k (x (k + 1) - x k) = - F (x k)

end NonsmoothNewton.Local


