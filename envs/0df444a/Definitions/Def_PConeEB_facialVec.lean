-- Prove2me | Definitions.Def_PConeEB_facialVec
-- name    : PConeEB_facialVec
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:32:35.431766+00:00
-- url     : https://prove2.me/theorems/f787c8d8-7377-46b6-8d69-edf738a38ef4
-- title:
--   The generator $f$ of the face $\mathcal F_z$
-- statement:
--   For $z=(z_0,\bar z)$ with $z_0>0$ and $q\in(1,\infty)$,
--   $$
--   f:=\begin{bmatrix}1\\-\operatorname{sgn}(\bar z)\circ|z_0^{-1}\bar z|^{q-1}\end{bmatrix}.
--   $$
--   For $z\in\partial\mathcal K_q^{n+1}\setminus\{0\}$, this vector generates the face $\{z\}^\perp\cap\mathcal K_p^{n+1}$.
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, (4.5), p.18

import Mathlib
import Definitions.Def_PConeEB_RR

namespace PConeEB

/-- The generator `f := (1, -sgn(z̄) ∘ |z₀⁻¹ z̄|^{q-1})` of the face `F_z` in (4.5).
Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, (4.5), p.18. -/
noncomputable def facialVec {n : ℕ} (q : ℝ) (z : RR n) : RR n :=
  WithLp.toLp 2 (Fin.cons 1 fun i : Fin n =>
    -Real.sign (z i.succ) * |(z 0)⁻¹ * z i.succ| ^ (q - 1))

end PConeEB


