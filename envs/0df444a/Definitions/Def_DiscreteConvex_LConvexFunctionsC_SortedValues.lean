-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsC_SortedValues
-- name    : DiscreteConvex_LConvexFunctionsC_SortedValues
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:31:55.667997+00:00
-- url     : https://prove2.me/theorems/a1f1ac31-c888-49f5-9f69-218910df4d58
-- title:
--   SortedValues
-- statement:
--   The distinct values of $p:V\to\mathbb R$, sorted in decreasing order, Eq. (4.4).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.103, Eq. (4.4).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.103, Eq. (4.4)

import Mathlib

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The distinct values of `p : V → R`, sorted in decreasing order, Eq. (4.4). -/
noncomputable def SortedValues (p : V → ℝ) : List ℝ :=
  (Finset.image p Finset.univ).sort (· ≥ ·)

end DiscreteConvex.LConvexFunctionsC


