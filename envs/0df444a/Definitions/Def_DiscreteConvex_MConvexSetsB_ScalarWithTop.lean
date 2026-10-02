-- Prove2me | Definitions.Def_DiscreteConvex_MConvexSetsB_ScalarWithTop
-- name    : DiscreteConvex_MConvexSetsB_ScalarWithTop
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:26:38.262828+00:00
-- url     : https://prove2.me/theorems/a45c2948-3bf5-4281-94e9-3ab603c1066d
-- title:
--   ScalarWithTop
-- statement:
--   The scalar multiple $c \bullet x$ of $x \in \mathbb R \cup \{+\infty\}$ by $c \in \mathbb R$, with the convention $c\bullet\top=\top$ for $c \ne 0$ and $0\bullet\top=0$. Every use of this operation in this mission has $c \ge 0$ (a difference of consecutive sorted values, or a convex-combination weight in $[0,1]$), so the convention on negative $c$ is never exercised.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting Eq. (4.6) and Theorem 4.16.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting Eq. (4.6) and Theorem 4.16

import Mathlib

/-!
Scalar multiplication of an `R ∪ {+∞}`-value by a nonnegative real, used to state the Lovász
extension (Eq. (4.6)) and convexity of an extended-real-valued function (Theorem 4.16), in
`DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- The scalar multiple `c • x` of `x ∈ R ∪ \{+∞\}` by `c ∈ R`, with the convention `c • ⊤ = ⊤`
for `c ≠ 0` and `0 • ⊤ = 0`. Every use of this operation in this mission has `c ≥ 0` (a
difference of consecutive sorted values, or a convex-combination weight in `[0,1]`). -/
noncomputable def ScalarWithTop (c : ℝ) (x : WithTop ℝ) : WithTop ℝ :=
  match x with
  | ⊤ => if c = 0 then (0 : WithTop ℝ) else ⊤
  | (r : ℝ) => ((c * r : ℝ) : WithTop ℝ)

end DiscreteConvex.MConvexSetsB


