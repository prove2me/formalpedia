-- Prove2me | Definitions.Def_ALAVI_IsSubproblemSol
-- name    : ALAVI_IsSubproblemSol
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:38:35.674972+00:00
-- url     : https://prove2.me/theorems/0c6bdf16-b1c6-4b29-8df3-f92e238836a8
-- title:
--   Solutions of the primal subproblem (27) of ALAVI
-- statement:
--   For $g,v\in E$, $q\in F$ and $\alpha>0$, a point $x$ **solves the primal subproblem** if $x\in U$ and
--
--   $$
--   x\in\operatorname*{arg\,min}_{w\in U}\ \langle g,w\rangle+J(w)+\langle q,\Theta(w)\rangle+\frac1{2\alpha}\|w-v\|^2 .
--   $$
--
--   In ALAVI, $g=G(u^k)$, $q=q^k$, $v=v^k$ and $x=u^{k+1}$.
--
--   **Formalization Note.** The objective is a real number plus $J(w)\in(-\infty,+\infty]$, compared in `EReal`. If $U\cap\operatorname{dom}J=\emptyset$ every point of $U$ is a minimizer; the theorems that use this predicate assume a point of $U\cap\operatorname{dom}J$.
-- source:
--   Zhao, Zhu & Zhang, An Augmented Lagrangian Approach to Conically Constrained Non-monotone Variational Inequality Problems, arXiv:2306.01214v1, subproblem (27), p.12

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_CalamaiMore_Convergence_proj

namespace ALAVI

/-- **The primal subproblem (27)** as an argmin predicate: `x ∈ U` minimizes
`⟨g, w⟩ + J(w) + ⟨q, Θ(w)⟩ + (1/(2α))‖w - v‖²` over `w ∈ U`. In ALAVI, `g = G(uᵏ)`, `q = qᵏ`,
`v = vᵏ` and `x = uᵏ⁺¹`.

Zhao, Zhu & Zhang, arXiv:2306.01214v1, (27), p.12.

Formalization Note: the objective is computed in `EReal` as a real number plus `J(w)`, so no
`⊤ - ⊤` arises. If `U ∩ dom J` is empty every point of `U` is a minimizer; every statement that
uses this predicate carries a point of `U ∩ dom J`. -/
def IsSubproblemSol {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (U : Set E) (J : E → EReal) (Θ : E → F) (α : ℝ) (g : E) (q : F) (v x : E) : Prop :=
  x ∈ U ∧ ∀ w ∈ U,
    ((inner ℝ g x + inner ℝ q (Θ x) + ‖x - v‖ ^ 2 / (2 * α) : ℝ) : EReal) + J x ≤
      ((inner ℝ g w + inner ℝ q (Θ w) + ‖w - v‖ ^ 2 / (2 * α) : ℝ) : EReal) + J w

end ALAVI


