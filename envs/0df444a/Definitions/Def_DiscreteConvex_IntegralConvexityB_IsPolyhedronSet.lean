-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityB_IsPolyhedronSet
-- name    : DiscreteConvex_IntegralConvexityB_IsPolyhedronSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:02:02.346283+00:00
-- url     : https://prove2.me/theorems/0244dbe3-289b-4f16-af0b-f2fdd185b67a
-- title:
--   Convex polyhedron
-- statement:
--   A finite intersection of half-spaces.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.10).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.10)

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_LinFunc

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.98, Eq. (3.10): a convex polyhedron, in
`DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `S` is a **convex polyhedron** (Eq. (3.10)): a finite intersection of half-spaces
`\{p | LinFunc (w i) (c i) p ≤ b i\}`. -/
def IsPolyhedronSet {V : Type*} [Fintype V] (S : Set ((V → ℝ) × ℝ)) : Prop :=
  ∃ (m : ℕ) (w : Fin m → V → ℝ) (c b : Fin m → ℝ),
    S = {p | ∀ i, LinFunc (w i) (c i) p ≤ b i}

end DiscreteConvex.IntegralConvexityB


