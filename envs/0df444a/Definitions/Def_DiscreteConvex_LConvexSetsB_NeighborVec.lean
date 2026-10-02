-- Prove2me | Definitions.Def_DiscreteConvex_LConvexSetsB_NeighborVec
-- name    : DiscreteConvex_LConvexSetsB_NeighborVec
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:48:35.276641+00:00
-- url     : https://prove2.me/theorems/3566cf8e-04ee-4895-9147-2721bdb25a47
-- title:
--   NeighborVec
-- statement:
--   The integral-neighborhood point $\lfloor p\rfloor + \chi_{U_i(p)}$ (preceding Eq. (5.11)), one of the $m+1$ points whose convex combination represents $p$ (Eq. (5.11)).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.127, preceding Eq. (5.11).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.127, preceding Eq. (5.11)

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexSetsB_FracLevelSet

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.127, preceding Eq. (5.11): the
integral-neighborhood points `⌊p⌋ + χ_{Uᵢ(p)}`, in `DiscreteConvex.LConvexSetsB`.
-/

namespace DiscreteConvex.LConvexSetsB

open Classical in
/-- The integral-neighborhood point `⌊p⌋ + χ_{Uᵢ(p)}` (preceding Eq. (5.11)), one of the
`m+1` points whose convex combination represents `p` (Eq. (5.11)). -/
noncomputable def NeighborVec {V : Type*} [Fintype V] [DecidableEq V] (p : V → ℝ) (i : ℕ) :
    V → ℤ :=
  fun v => ⌊p v⌋ + (if v ∈ FracLevelSet p i then 1 else 0)

end DiscreteConvex.LConvexSetsB


