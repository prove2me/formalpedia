-- Prove2me | Definitions.Def_EkelandVP_Constraints_IsRegular
-- name    : EkelandVP_Constraints_IsRegular
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T10:51:39.610439+00:00
-- url     : https://prove2.me/theorems/777f3a42-8e10-4f2a-8e26-1ca23ee35ee2
-- title:
--   Regularity assumption (3.4): derivatives of the saturated constraints are linearly independent at every feasible point
-- statement:
--   Let $V$ be a real normed space and $G_1,\dots,G_m:V\to\mathbb R$ with $p$ equality constraints and $m-p$ inequality constraints, feasible set $\mathcal C$ as in (3.2). For a feasible point $v\in\mathcal C$, the set of **saturated constraints** is
--   $$I(v)=\{i \mid G_i(v)=0\}. \tag{3.3}$$
--   The constraints are **regular** if
--   $$\forall v\in\mathcal C,\quad \text{the family } \big(G_i'(v)\big)_{i\in I(v)} \text{ is linearly independent in } V^*, \tag{3.4}$$
--   where $G_i'(v)\in V^*$ is the Fréchet derivative of $G_i$ at $v$.
--
--   This is the linear independence constraint qualification under which Theorem 3.1 delivers approximate Lagrange multipliers.
--
--   **Formalization Note.** $G_i'(v)$ is `fderiv ℝ (G i) v : V →L[ℝ] ℝ`. The family is indexed by the subtype of saturated indices, so two distinct saturated constraints with the same derivative count as linearly dependent. Every equality constraint is saturated at a feasible point, so $I(v)$ contains all of them.
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), p. 330, §3, (3.3)–(3.4)

import Mathlib
import Definitions.Def_EkelandVP_Constraints_feasibleSet

namespace EkelandVP.Constraints

/-- Ekeland (1974), §3, (3.3)–(3.4): the regularity assumption. At every feasible point `v`, the
Fréchet derivatives `G_i'(v)` of the saturated constraints `i ∈ I(v) = {i | G_i(v) = 0}` form a
linearly independent family in `V* = V →L[ℝ] ℝ`. The family is indexed by the saturated indices, so
two saturated constraints with equal derivatives make it dependent. -/
def IsRegular {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {m : ℕ}
    (p : ℕ) (G : Fin m → V → ℝ) : Prop :=
  ∀ v ∈ feasibleSet p G,
    LinearIndependent ℝ (fun i : {i : Fin m // G i v = 0} => fderiv ℝ (G i) v)

end EkelandVP.Constraints


