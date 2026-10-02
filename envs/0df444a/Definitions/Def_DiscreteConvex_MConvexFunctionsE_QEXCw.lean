-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_QEXCw
-- name    : DiscreteConvex_MConvexFunctionsE_QEXCw
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:04:49.70841+00:00
-- url     : https://prove2.me/theorems/421791ff-5bd7-4532-95f1-9f84e62132eb
-- title:
--   QEXCw
-- statement:
--   Axiom (Q-EXCw), the weaker variant of (Q-EXC).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.171, axiom (Q-EXCw).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.171, axiom (Q-EXCw)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SuppNeg

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (Q-EXCw), the weaker variant of (Q-EXC). -/
def QEXCw (B : Set (V → ℤ)) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, x ≠ y → ∃ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    (fun w => x w - CharVec u w + CharVec v w) ∈ B ∨
      (fun w => y w + CharVec u w - CharVec v w) ∈ B

end DiscreteConvex.MConvexFunctionsE


