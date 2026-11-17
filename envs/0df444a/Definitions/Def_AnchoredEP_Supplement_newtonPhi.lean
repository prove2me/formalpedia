-- Prove2me | Definitions.Def_AnchoredEP_Supplement_newtonPhi
-- name    : AnchoredEP_Supplement_newtonPhi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:04:54.015446+00:00
-- url     : https://prove2.me/theorems/054b1b11-761d-4b00-891b-2d90510b9cb7
-- title:
--   Merit function $\varphi_k$ of AEP Newton, Eq. (22)
-- statement:
--   At an outer iteration $k$ of the AEP Newton method, the quality of a trial step $a$ is measured by the **merit function**
--   $$
--   \varphi_k(a):=L_2\,a\,\big\|z_{k+1}(a)-z_{k+\frac12}(a)\big\|\quad(a>0),\qquad \varphi_k(0):=0,
--   $$
--   where $L_2$ is the Lipschitz constant of the Jacobian, $z_{k+\frac12}(a)$ is the extrapolated point (10) and $z_{k+1}(a)$ is the solution of the affine-model subproblem with step $a$.
--
--   A trial with $\varphi_k(a)\le\sqrt2$ satisfies the AEP relative-error condition with $\rho=1/\sqrt2$, and $\varphi_k(a)\ge1$ guarantees a step large enough for acceleration; the line search looks for $a$ with $1\le\varphi_k(a)\le\sqrt2$.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Eq. (22), p.9

import Mathlib
import Definitions.Def_AnchoredEP_IterState
import Definitions.Def_AnchoredEP_trialMid
import Definitions.Def_AnchoredEP_trialZ

namespace AnchoredEP.Supplement

/-- **The merit function `φ_k` of AEP Newton.** Jiang–Yoon, arXiv:2609.30212, Eq. (22), p.9:
`φ_k(a) := L₂ a ‖z_{k+1}(a) − z_{k+½}(a)‖`, `φ_k(0) := 0`.

**Formalization Note.** Defined by cases at `a = 0`, as in (22). `z_{k+1}(a)` is the published
`trialZ F sol z0 s a` and `z_{k+½}(a)` the published `trialMid F z0 s a` (formula (10) with
`a_k = a`, which is Algorithm 1 line 8). -/
noncomputable def newtonPhi {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : ℝ)
    (sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (z0 : EuclideanSpace ℝ (Fin d)) (s : IterState d) (a : ℝ) : ℝ :=
  if a = 0 then 0 else L * a * ‖trialZ F sol z0 s a - trialMid F z0 s a‖

end AnchoredEP.Supplement


