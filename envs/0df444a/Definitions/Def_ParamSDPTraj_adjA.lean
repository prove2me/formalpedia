-- Prove2me | Definitions.Def_ParamSDPTraj_adjA
-- name    : ParamSDPTraj_adjA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:11:47.312146+00:00
-- url     : https://prove2.me/theorems/9c9cf0aa-5a36-45fd-9e13-8876bbc9b10d
-- title:
--   The adjoint operator $\mathcal A^*(t)$
-- statement:
--   For $y\in\mathbb R^m$, the **adjoint operator** of $\mathcal A(t)$ is
--
--   $$\mathcal A^*(t)[y]=\sum_{i=1}^m y_i\,A_i(t).$$
--
--   It carries the equality constraint of the dual problem $(D_t)$.
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, §2.1, p.5, and (Dt), p.7

import Mathlib

namespace ParamSDPTraj

/-- **The adjoint operator 𝒜*(t).**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, §2.1, p.5: "A∗[y] = ∑_{i=1}^m Aiyi is the linear operator adjoint to A", with the
parameter t of (Dt), p.7. -/
noncomputable def adjA {n m : ℕ} (A : Fin m → ℝ → Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (y : Fin m → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i, y i • A i t

end ParamSDPTraj


