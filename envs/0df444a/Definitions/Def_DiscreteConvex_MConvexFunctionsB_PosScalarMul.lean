-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsB_PosScalarMul
-- name    : DiscreteConvex_MConvexFunctionsB_PosScalarMul
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:06:40.460882+00:00
-- url     : https://prove2.me/theorems/d697ba8e-06cd-4b31-ae60-f384fece853d
-- title:
--   PosScalarMul
-- statement:
--   The scalar multiple $c \bullet x$ of $x \in \mathbb R \cup \{+\infty\}$ by $c>0$, with $c\bullet\top=\top$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting Theorem 6.13(1).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting Theorem 6.13(1)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, supporting Theorem 6.13(1), in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- Scalar multiple of an extended real by a positive real, with the convention `c • ⊤ = ⊤`
for `c ≠ 0` and `0 • ⊤ = 0`. -/
noncomputable def PosScalarMul (c : ℝ) (x : WithTop ℝ) : WithTop ℝ :=
  match x with
  | ⊤ => if c = 0 then (0 : WithTop ℝ) else ⊤
  | (r : ℝ) => ((c * r : ℝ) : WithTop ℝ)

end DiscreteConvex.MConvexFunctionsB


