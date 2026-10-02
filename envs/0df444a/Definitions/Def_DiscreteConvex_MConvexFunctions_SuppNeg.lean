-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctions_SuppNeg
-- name    : DiscreteConvex_MConvexFunctions_SuppNeg
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:51:54.194635+00:00
-- url     : https://prove2.me/theorems/7bfedca8-4d9b-4a6a-9e62-63c18a0d3e85
-- title:
--   Negative support of a vector difference
-- statement:
--   The negative support $\operatorname{supp}^-(x-y) = \{v : x(v) < y(v)\}$, as a `Finset` ($V$ is finite).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, citing Eq. (1.19).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, citing Eq. (1.19)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.133, citing Eq. (1.19): the negative support
of a difference of integer vectors, in `DiscreteConvex.MConvexFunctions`.
-/

namespace DiscreteConvex.MConvexFunctions

/-- The negative support `supp⁻(x - y) = \{v : x(v) < y(v)\}`, as a `Finset` (`V` is finite). -/
def SuppNeg {V : Type*} [Fintype V] [DecidableEq V] (x y : V → ℤ) : Finset V :=
  Finset.univ.filter (fun v => x v < y v)

end DiscreteConvex.MConvexFunctions


