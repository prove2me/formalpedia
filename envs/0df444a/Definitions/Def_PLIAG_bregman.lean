-- Prove2me | Definitions.Def_PLIAG_bregman
-- name    : PLIAG_bregman
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:31.790631+00:00
-- url     : https://prove2.me/theorems/02167543-c65e-4b1d-a7ff-37b54c078d96
-- title:
--   Bregman distance $D_w(y,x)$
-- statement:
--   Let $w$ be a Legendre function. The **Bregman distance** associated with $w$ is
--
--   $$
--   D_w(y,x)=w(y)-w(x)-\langle\nabla w(x),\,y-x\rangle,\qquad y\in\operatorname{dom}w,\ x\in\operatorname{int}\operatorname{dom}w .
--   $$
--
--   For $w=\tfrac12\|x\|^2$ it is $\tfrac12\|y-x\|^2$. It replaces the squared Euclidean distance in the proximal subproblem (3.1), in the growth condition B3 and in the Lyapunov function (4.6).
--
--   **Formalization Note** The value is an extended real: $w(y)$ enters as an element of `EReal`, so $D_w(y,x)=+\infty$ when $y\notin\operatorname{dom}w$, as the paper's extended arithmetic gives. The second argument is only used at points of $\operatorname{int}\operatorname{dom}w$, where $w$ is finite and $\nabla w(x)$ is the gradient of the real function `(w ·).toReal`.
-- source:
--   Zhang, Dai, Guo, Peng, Proximal-Like Incremental Aggregated Gradient Method with Linear Convergence under Bregman Distance Growth Conditions, arXiv:1711.01136v3, §2, p.5 (definition of D_w)

import Mathlib

namespace PLIAG

/-- **Bregman distance** (Zhang–Dai–Guo–Peng, arXiv:1711.01136v3, §2, p.5):
`D_w(y, x) = w(y) − w(x) − ⟨∇w(x), y − x⟩` for `y ∈ dom w`, `x ∈ int dom w`.

**Formalization Note.** Valued in `EReal`: `w(y)` enters as an extended real, so
`D_w(y, x) = +∞` when `y ∉ dom w` (the paper's extended arithmetic), and the infimum
`inf_{z ∈ X} D_w(z, ·)` and the subproblem (3.1) mean what the page says. The second argument is
used only at points of `int dom w`, where `w` is finite and `∇w(x)` is the gradient of the real
function `x ↦ (w x).toReal`. -/
noncomputable def bregman {d : ℕ} (w : EuclideanSpace ℝ (Fin d) → EReal)
    (y x : EuclideanSpace ℝ (Fin d)) : EReal :=
  w y - (((w x).toReal + inner ℝ (gradient (fun z => (w z).toReal) x) (y - x) : ℝ) : EReal)

end PLIAG


