-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsB_Restriction
-- name    : DiscreteConvex_MConvexFunctionsB_Restriction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:06:41.345977+00:00
-- url     : https://prove2.me/theorems/a9c0380a-4e1b-4e75-a78a-c71419d3410d
-- title:
--   Restriction
-- statement:
--   The restriction $f_U$ of $f$ to $U \subseteq V$ (Eq. (6.40)), represented as vectors vanishing outside $U$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.143, Eq. (6.40).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.143, Eq. (6.40)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.143, Eq. (6.40), in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- The restriction `f_U` of `f` to `U ⊆ V` (Eq. (6.40)), represented as vectors vanishing
outside `U`. -/
def Restriction {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ) (U : Finset V) :
    (V → ℤ) → WithTop ℝ :=
  fun y => if (∀ v ∉ U, y v = 0) then f y else ⊤

end DiscreteConvex.MConvexFunctionsB


