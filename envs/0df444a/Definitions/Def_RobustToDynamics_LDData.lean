-- Prove2me | Definitions.Def_RobustToDynamics_LDData
-- name    : RobustToDynamics_LDData
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:35.007013+00:00
-- url     : https://prove2.me/theorems/ab5210e4-2455-4641-8d71-eb4c9e36bbd9
-- title:
--   Rational data $(A,b,G)$ of the robust-to-dynamics constraints
-- statement:
--   An instance of the constraint data consists of a dimension $n$, a number $m$ of inequalities, a matrix $A\in\mathbb Q^{m\times n}$, a vector $b\in\mathbb Q^m$ and a dynamics matrix $G\in\mathbb Q^{n\times n}$. Together they define $P=\{x: Ax\le b\}$ and the dynamics $x_{k+1}=Gx_k$.
--
--   The first claim of Theorem 2.7 is about these data alone: its running time is polynomial in $\sigma(A,b,G)$, which does not involve the objective $c$.
--
--   **Formalization Note** Any $n$ and $m$ are allowed, including $0$.
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, §2, p.5 and footnote 3; Theorem 2.7, p.13

import Mathlib

namespace RobustToDynamics

/-- **Rational data `(A, b, G)` of the robust-to-dynamics constraints.**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, §2, p.5 ("The input to an
R-LD-LP is fully defined by c ∈ Rn, A ∈ Rm×n, b ∈ Rm, G ∈ Rn×n", rational in complexity questions,
footnote 3) and Theorem 2.7, p.13 ("σ(A, b, G)").

An `LDData` is a dimension `n`, a number of constraints `m`, `A ∈ ℚ^{m×n}`, `b ∈ ℚ^m` and
`G ∈ ℚ^{n×n}`; it carries no objective `c`, because the first claim of Theorem 2.7 is polynomial
in `σ(A, b, G)`.

**Formalization Note.** Any `n, m` are allowed, including `0`. -/
structure LDData where
  /-- the dimension `n` of the state space `ℝⁿ` -/
  n : ℕ
  /-- the number `m` of linear inequalities defining `P` -/
  m : ℕ
  /-- the constraint matrix `A ∈ ℚ^{m×n}` -/
  A : Matrix (Fin m) (Fin n) ℚ
  /-- the right-hand side `b ∈ ℚ^m` -/
  b : Fin m → ℚ
  /-- the dynamics matrix `G ∈ ℚ^{n×n}` of `x_{k+1} = G x_k` -/
  G : Matrix (Fin n) (Fin n) ℚ

end RobustToDynamics


