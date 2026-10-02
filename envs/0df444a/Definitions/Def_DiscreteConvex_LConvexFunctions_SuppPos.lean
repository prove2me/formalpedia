-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctions_SuppPos
-- name    : DiscreteConvex_LConvexFunctions_SuppPos
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:13:22.570194+00:00
-- url     : https://prove2.me/theorems/dcd89053-671b-499a-b834-64cd606ffa68
-- title:
--   Positive support of a vector difference
-- statement:
--   The positive support $\operatorname{supp}^+(p-q) = \{v : p(v) > q(v)\}$, as a `Finset` ($V$ is finite).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.180, citing Eq. (1.19).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.180, citing Eq. (1.19)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.180, citing Eq. (1.19): the positive support
of a difference of integer vectors, in `DiscreteConvex.LConvexFunctions`.
-/

namespace DiscreteConvex.LConvexFunctions

/-- The positive support `supp⁺(p - q) = \{v : p(v) > q(v)\}`, as a `Finset` (`V` is finite). -/
def SuppPos {V : Type*} [Fintype V] [DecidableEq V] (p q : V → ℤ) : Finset V :=
  Finset.univ.filter (fun v => q v < p v)

end DiscreteConvex.LConvexFunctions


