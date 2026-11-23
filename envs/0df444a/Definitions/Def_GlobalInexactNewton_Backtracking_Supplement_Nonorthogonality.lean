-- Prove2me | Definitions.Def_GlobalInexactNewton_Backtracking_Supplement_Nonorthogonality
-- name    : GlobalInexactNewton_Backtracking_Supplement_Nonorthogonality
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:47:45.957317+00:00
-- url     : https://prove2.me/theorems/ee3cd23d-b96d-44e5-a0f4-2764d74111c8
-- title:
--   The neighborhood nonorthogonality condition of p. 417
-- statement:
--   Let $K_1(x)$ be the first residual-minimizing subspace chosen by the method at $x$. Nonorthogonality near $x_*$ means that some $\delta,\lambda>0$ satisfy: for every $x\in N_\delta(x_*)$ with $F(x)\ne0$, there is a direction $z\in K_1(x)$ such that
--
--   $$F'(x)z\ne0,\qquad\frac{|\langle F(x),F'(x)z\rangle|}{\|F(x)\|\|F'(x)z\|}\ge\lambda.$$
--
--   This gives the source's lower bound on the maximum cosine over the nonzero image of the first subspace. **Formalization Note** In finite dimensions that maximum is attained after normalizing image directions. The existential direction is therefore equivalent to the displayed maximum condition, including $\lambda=1$. The neighborhood quantifier ranges over every point, rather than only the iterates.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), p. 417, Nonorthogonality condition; DOI 10.1137/0804022

import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method
import Definitions.Def_GlobalInexactNewton_Backtracking_Supplement_EqualityCurves

namespace GlobalInexactNewton.Backtracking.Supplement

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- p. 417: full neighborhood condition, with an attained direction in the first subspace.
The maximum exists on normalized nonzero image directions in finite dimensions. -/
def Nonorthogonality (F : E → E) (xstar : E) (firstSpace : E → Submodule ℝ E) : Prop :=
  ∃ δ > 0, ∃ lam > 0, ∀ x ∈ Metric.ball xstar δ, F x ≠ 0 →
    ∃ z ∈ firstSpace x, fderiv ℝ F x z ≠ 0 ∧ lam ≤ residualAngle F x z

end GlobalInexactNewton.Backtracking.Supplement


