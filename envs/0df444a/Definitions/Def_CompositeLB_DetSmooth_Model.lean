-- Prove2me | Definitions.Def_CompositeLB_DetSmooth_Model
-- name    : CompositeLB_DetSmooth_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T06:30:21.081562+00:00
-- url     : https://prove2.me/theorems/6aacf3e7-59c0-44eb-954d-c6424eac7b29
-- title:
--   Equations (1)–(3), pp. 1, 3 — finite sums and the exact gradient and prox oracle
-- statement:
--   Let $m\ge2$ smooth convex components $f_i$ be indexed by $i=1,\dots,m$ on a Euclidean space $\mathbb R^d$. Their average is
--
--   $$F(x)=\frac1m\sum_{i=1}^m f_i(x).$$
--
--   A query $(i,x,\beta)$ asks for $f_i(x)$, a gradient $\nabla f_i(x)$, and a point minimizing $f_i(u)+\frac\beta2\|x-u\|^2$ over the feasible set $\mathcal X$. An exact oracle returns all three. A deterministic algorithm chooses its next query from the ordered list of preceding responses; its first query has index zero. A component is $\gamma$-smooth on $\mathcal X$ when its gradient is $\gamma$-Lipschitz between points of $\mathcal X$.
--
--   This model makes the lower bound apply to adaptive component queries with exact proximal information, including algorithms that use previous prox points to choose later queries.
--
--   **Formalization Note** Prox queries require $\beta>0$, the only case the paper's lemmas treat. The prox is the published minimizer predicate `BoydADMM.Prox.IsProx` (a point of $\mathcal X$ minimizing $f_i(u)+\frac\beta2\|u-x\|^2$ over $\mathcal X$), so no choice of minimizer is made. The oracle is a fixed function of the query. Components and gradients are defined on all of $\mathbb R^d$, so queries may lie outside $\mathcal X$. Lean uses `Fin m` for the components, with index zero corresponding to the paper's component 1.
-- source:
--   Woodworth & Srebro, arXiv:1605.08003v3, Eqs. (1)–(3), p. 1; §1 Notation and Definitions, p. 3

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic
import Definitions.Def_CompositeLB_DetLip_Model

namespace CompositeLB.DetSmooth

/-- Every answer gives the component's value, a genuine gradient, and an exact
constrained prox point (3), for every positive prox parameter. The prox is the
published minimizer predicate `BoydADMM.Prox.IsProx X g β x u`: `u ∈ X` and `u`
minimizes `g u + (β/2)‖u - x‖²` over `X`. -/
def IsValidOracle {m d : ℕ} (f : Fin m → CompositeLB.DetLip.E d → ℝ)
    (X : Set (CompositeLB.DetLip.E d)) (O : CompositeLB.DetLip.Oracle m d) : Prop :=
  ∀ q, (O q).val = f q.comp q.pt ∧
    HasGradientAt (f q.comp) (O q).grad q.pt ∧
    BoydADMM.Prox.IsProx X (f q.comp) q.beta q.pt (O q).prox

/-- The paper's `γ`-smoothness: a globally defined gradient map that is
`γ`-Lipschitz when both arguments are in the domain. -/
def IsSmoothOn {d : ℕ} (γ : ℝ) (g : CompositeLB.DetLip.E d → ℝ) (X : Set (CompositeLB.DetLip.E d)) : Prop :=
  ∃ G : CompositeLB.DetLip.E d → CompositeLB.DetLip.E d,
    (∀ x, HasGradientAt g (G x) x) ∧
    ∀ x ∈ X, ∀ y ∈ X, ‖G x - G y‖ ≤ γ * ‖x - y‖

end CompositeLB.DetSmooth


