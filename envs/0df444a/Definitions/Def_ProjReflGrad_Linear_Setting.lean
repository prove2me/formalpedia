-- Prove2me | Definitions.Def_ProjReflGrad_Linear_Setting
-- name    : ProjReflGrad_Linear_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T09:13:27.152998+00:00
-- url     : https://prove2.me/theorems/a9c2b8d7-1f23-41e0-bfe0-879077e97a3f
-- title:
--   (C2*), p. 6 — strongly monotone maps with modulus m
-- statement:
--   Let $H$ be a real inner product space with inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$, let $F : H\to H$ and $m\in\mathbb R$. The map $F$ is *strongly monotone with modulus $m$* (condition (C2\*) of the paper) if
--   $$\langle F(x)-F(y),\, x-y\rangle\ \ge\ m\,\|x-y\|^2\qquad\text{for all } x,y\in H.$$
--
--   This is the hypothesis under which the projected reflected gradient method converges R-linearly (Theorem 3.3). The other objects of the mission (the projection $P_C$, the solution set $S$ of (1.1), Lipschitz maps (C3), runs of Algorithm 3.1) are those of the shared definitions module `ProjReflGrad.Weak.Setting`.
--
--   **Formalization Note.** The paper requires $m>0$; the sign is not built into the predicate, and every theorem that uses it adds the hypothesis $0<m$.
-- source:
--   Malitsky, Projected Reflected Gradient Methods for Monotone Variational Inequalities, arXiv:1502.04968v1, p. 6, (C2*)

import Mathlib
import Definitions.Def_ProjReflGrad_Weak_Setting

namespace ProjReflGrad.Linear

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- (C2*): `F` is strongly monotone on all of `H` with modulus `m`:
`⟨F(x) - F(y), x - y⟩ ≥ m‖x - y‖²` for all `x, y`. Theorems add `0 < m`. -/
def IsStronglyMonotoneMap (F : H → H) (m : ℝ) : Prop :=
  ∀ x y : H, m * ‖x - y‖ ^ 2 ≤ inner ℝ (F x - F y) (x - y)

end ProjReflGrad.Linear


