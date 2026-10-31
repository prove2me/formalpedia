-- Prove2me | Definitions.Def_RobustToDynamics_LPInst
-- name    : RobustToDynamics_LPInst
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:39.075985+00:00
-- url     : https://prove2.me/theorems/f831eb50-2ff3-485e-bb7c-619d9d08e2d9
-- title:
--   A rational linear program $\min\{c^Tx : Ax\le b\}$
-- statement:
--   A linear program with $p$ inequality constraints in $q$ variables and rational data: $A\in\mathbb Q^{p\times q}$, $b\in\mathbb Q^p$, $c\in\mathbb Q^q$, posed as
--   $$
--   \min\{c^Tx : x\in\mathbb R^q,\ Ax\le b\}.
--   $$
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, p.13 and p.16

import Mathlib

namespace RobustToDynamics

/-- **A rational linear program `min {cᵀx : Ax ≤ b}`.**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, p.13 ("a linear program
defined by rational data") and p.16 ("any linear function cT x can be optimized over a polyhedron
in polynomial time").

An `LPInst` has `p` inequality constraints in `q` variables: `A ∈ ℚ^{p×q}`, `b ∈ ℚ^p`, and the
objective `c ∈ ℚ^q`.

**Formalization Note.** Any `p, q`, including `0`. The LP is posed over `ℝ^q`
(`RobustToDynamics.polyhedron` of the cast data). -/
structure LPInst where
  /-- the number of inequalities -/
  p : ℕ
  /-- the number of variables -/
  q : ℕ
  /-- the constraint matrix `A ∈ ℚ^{p×q}` -/
  A : Matrix (Fin p) (Fin q) ℚ
  /-- the right-hand side `b ∈ ℚ^p` -/
  b : Fin p → ℚ
  /-- the objective `c ∈ ℚ^q` -/
  c : Fin q → ℚ

end RobustToDynamics


