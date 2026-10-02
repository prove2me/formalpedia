-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctions_SuppPos
-- name    : DiscreteConvex_MConvexFunctions_SuppPos
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:51:46.787961+00:00
-- url     : https://prove2.me/theorems/b3a19434-e180-43d6-be5c-c80223b2256e
-- title:
--   Positive support of a vector difference
-- statement:
--   The positive support $\operatorname{supp}^+(x-y) = \{v : x(v) > y(v)\}$, as a `Finset` ($V$ is finite).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, citing Eq. (1.19).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, citing Eq. (1.19)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.133, citing Eq. (1.19): the positive support
of a difference of integer vectors, in `DiscreteConvex.MConvexFunctions`.
-/

namespace DiscreteConvex.MConvexFunctions

/-- The positive support `supp⁺(x - y) = \{v : x(v) > y(v)\}`, as a `Finset` (`V` is finite). -/
def SuppPos {V : Type*} [Fintype V] [DecidableEq V] (x y : V → ℤ) : Finset V :=
  Finset.univ.filter (fun v => y v < x v)

end DiscreteConvex.MConvexFunctions


