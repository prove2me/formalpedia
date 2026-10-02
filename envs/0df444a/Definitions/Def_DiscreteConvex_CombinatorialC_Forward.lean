-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_Forward
-- name    : DiscreteConvex_CombinatorialC_Forward
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:40:02.407006+00:00
-- url     : https://prove2.me/theorems/f2bfea27-1eee-44f3-88bd-5bca65f26baa
-- title:
--   Forward orientation of an arc on a cycle
-- statement:
--   Arc $\mathrm{arcs}_i$ is forward if it points from $v_i$ to $v_{i+1}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.83.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.83

import Mathlib

/-!
Orientation of an arc relative to a simple-cycle traversal, used for the parallel/series arc
relation (Murota, *Discrete Convex Analysis*, SIAM 2003, p.83), in
`DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- Arc `arcs i` is **forward** relative to the cycle traversal `v` if it points from `v i` to
`v (i+1)` (as opposed to the reverse). Meaningful once `{∂⁺(arcs i), ∂⁻(arcs i)} = {v i, v
(i+1)}` holds (`IsSimpleCycle`), in which case exactly one of forward/reverse holds. -/
def Forward {V A : Type*} {k : ℕ} (src : A → V) (v : Fin k → V) (arcs : Fin k → A)
    (i : Fin k) : Prop :=
  src (arcs i) = v i

end DiscreteConvex.CombinatorialC


