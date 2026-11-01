-- Prove2me | Definitions.Def_HomotopyProxVM_IsSmoothParam
-- name    : HomotopyProxVM_IsSmoothParam
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:35:53.610198+00:00
-- url     : https://prove2.me/theorems/6c154bf3-a1a2-4512-9603-c8a319500e86
-- title:
--   $L_f$-smoothness of $f$
-- statement:
--   A function $f:\mathbb R^p\to\mathbb R$ is **$L_f$-smooth** if $L_f\in[0,+\infty)$, $f$ is differentiable, and its gradient is Lipschitz continuous with constant $L_f$:
--
--   $$
--   \|\nabla f(x)-\nabla f(y)\|_2\le L_f\|x-y\|_2\qquad\text{for all }x,y\in\mathbb R^p .
--   $$
--
--   This is the other half of the assumption on $f$ in Assumption 2.
--
--   **Formalization Note** The paper has $f:\mathbb R^p\to\mathbb R\cup\{+\infty\}$ closed and asks for differentiability and the bound on $\operatorname{dom}(f)$. Differentiability makes $\operatorname{dom}(f)$ open, and a Lipschitz gradient keeps $f$ bounded near a finite boundary point, which closedness would put into $\operatorname{dom}(f)$. Hence $\operatorname{dom}(f)=\mathbb R^p$, and $f$ is written as a real-valued function on all of $\mathbb R^p$.
-- source:
--   Tran-Dinh, Liang & Toh, A New Homotopy Proximal Variable-Metric Framework for Composite Convex Minimization, arXiv:1812.05243v1, §2.1, p.5

import Mathlib

namespace HomotopyProxVM

/-- `f` is `Lf`-smooth: `f` is differentiable and `∇f` is Lipschitz with a constant `Lf ∈ [0,+∞)`,
`‖∇f(x) − ∇f(y)‖₂ ≤ Lf‖x − y‖₂` (Tran-Dinh, Liang & Toh, arXiv:1812.05243v1, §2.1, p.5).

**Formalization Note.** The paper has `f : ℝᵖ → ℝ ∪ {+∞}` closed, and asks for differentiability
and the Lipschitz bound on `dom(f)`. Differentiability makes `dom(f)` open; a Lipschitz gradient
keeps `f` bounded near a finite boundary point, and closedness would put that point into `dom(f)`.
So `dom(f) = ℝᵖ`, and `f` is written as a real-valued function on all of `ℝᵖ`. -/
def IsSmoothParam {p : ℕ} (f : EuclideanSpace ℝ (Fin p) → ℝ) (Lf : ℝ) : Prop :=
  0 ≤ Lf ∧ Differentiable ℝ f ∧ ∀ x y, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖

end HomotopyProxVM


