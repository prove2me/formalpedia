-- Prove2me | Definitions.Def_RobustToDynamics_LinSys
-- name    : RobustToDynamics_LinSys
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:39.688898+00:00
-- url     : https://prove2.me/theorems/cefd0f40-7a3f-4365-a7d5-fbe46cec439a
-- title:
--   A rational system of linear equations $Ax=b$
-- statement:
--   A system of $p$ rational linear equations in $q$ unknowns: $A\in\mathbb Q^{p\times q}$ and $b\in\mathbb Q^p$, asking for $x$ with $Ax=b$.
--
--   The paper uses the classical fact that such a system, if solvable, has a solution of polynomial size computable in polynomial time; it computes the Lyapunov solution $M$ that way.
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, p.13

import Mathlib

namespace RobustToDynamics

/-- **A rational system of linear equations `Ax = b`.**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, p.13: "any system of
rational linear equations has a solution of size polynomially bounded by the size of the data
defining the equality system [47]".

A `LinSys` is `p` equations in `q` unknowns: `A ∈ ℚ^{p×q}` and `b ∈ ℚ^p`.

**Formalization Note.** Any `p, q`, including `0`. -/
structure LinSys where
  /-- the number of equations -/
  p : ℕ
  /-- the number of unknowns -/
  q : ℕ
  /-- the coefficient matrix `A ∈ ℚ^{p×q}` -/
  A : Matrix (Fin p) (Fin q) ℚ
  /-- the right-hand side `b ∈ ℚ^p` -/
  b : Fin p → ℚ

end RobustToDynamics


