-- Prove2me | Definitions.Def_BinaryQueryLB_supNorm
-- name    : BinaryQueryLB_supNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:42:53.330895+00:00
-- url     : https://prove2.me/theorems/d0c656db-a978-4063-a884-cf3acc04c6c6
-- title:
--   Maximum norm $\|v\|_\infty$ on $\mathbb R^d$
-- statement:
--   For $v\in\mathbb R^d$, the **maximum norm** is
--   $$
--   \|v\|_\infty=\max_{i}|v_i|.
--   $$
--   It is the norm in which the problem class $F(d,R,M)$ measures Lipschitz continuity.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`, whose built-in norm is the Euclidean norm; the maximum norm is written out as a supremum over the finite coordinate set (it is $0$ for $d=0$).
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), §2.1, p.11

import Mathlib

namespace BinaryQueryLB

/-- **Maximum norm on ℝ^d.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), §2.1, p.11: "`∥·∥∞` for the maximum norm".

`supNorm v = max_i |v_i|`.

**Formalization Note.** ℝ^d is `EuclideanSpace ℝ (Fin d)`, whose own norm `‖·‖` is the Euclidean
norm `∥·∥₂`; the maximum norm is written out here as a real supremum over the finite index set
`Fin d` (for `d = 0` it is `0`, the supremum of the empty family of nonnegative numbers). -/
noncomputable def supNorm {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ⨆ i, |v i|

end BinaryQueryLB


