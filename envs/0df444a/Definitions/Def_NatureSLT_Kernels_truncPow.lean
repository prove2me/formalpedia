-- Prove2me | Definitions.Def_NatureSLT_Kernels_truncPow
-- name    : NatureSLT_Kernels_truncPow
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:52:08.199854+00:00
-- url     : https://prove2.me/theorems/8403a5b4-5585-4c66-9b4f-ecefbccca6b0
-- title:
--   Truncated power $(x - t)^d_+$
-- statement:
--   For an integer $d \ge 0$ and real numbers $x$, $t$, the **truncated power** is
--
--   $$(x - t)^d_+ = \begin{cases} 0 & \text{if } x \le t, \\ (x - t)^d & \text{if } x > t. \end{cases}$$
--
--   It is the basis function attached to a node $t$ in a spline of order $d$; in §6.4 it generates both the finite-node spline kernel (6.29) and the infinite-node kernel (6.30).
--
--   **Formalization Note** The case split is the book's: for $d = 0$ the function is the indicator of $x > t$ (value $0$ at $x = t$).
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 195, Section 6.4.1

import Mathlib

namespace NatureSLT.Kernels

/-- The truncated power `(x - t)^d_+` (Vapnik, *The Nature of Statistical Learning Theory*,
2nd ed., §6.4.1, p. 195): `0` if `x ≤ t`, and `(x - t)^d` if `x > t`.
For `d = 0` it is the indicator of `x > t` (the book's case split, not `0^0`). -/
noncomputable def truncPow (d : ℕ) (x t : ℝ) : ℝ :=
  if x ≤ t then 0 else (x - t) ^ d

end NatureSLT.Kernels


