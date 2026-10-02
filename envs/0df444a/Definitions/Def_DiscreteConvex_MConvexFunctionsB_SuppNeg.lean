-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsB_SuppNeg
-- name    : DiscreteConvex_MConvexFunctionsB_SuppNeg
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:05:50.175311+00:00
-- url     : https://prove2.me/theorems/721223e6-b52b-4e26-901d-18db35904c9e
-- title:
--   SuppNeg
-- statement:
--   The negative support $\operatorname{supp}^-(x-y)$, as a finite set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, citing Eq. (1.19).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, citing Eq. (1.19)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.133, citing Eq. (1.19), in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- The negative support `supp⁻(x - y)`, as a `Finset` (`V` is finite). -/
def SuppNeg {V : Type*} [Fintype V] [DecidableEq V] (x y : V → ℤ) : Finset V :=
  Finset.univ.filter (fun v => x v < y v)

end DiscreteConvex.MConvexFunctionsB


