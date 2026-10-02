-- Prove2me | Definitions.Def_DiscreteConvex_LConvexSetsB_FracLevelSet
-- name    : DiscreteConvex_LConvexSetsB_FracLevelSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:47:22.607986+00:00
-- url     : https://prove2.me/theorems/897bd3a3-8cae-451e-b24f-f3a3935fd105
-- title:
--   FracLevelSet
-- statement:
--   The $i$-th level set $U_i(p) = \{v \in V : a(v) \ge \alpha_i\}$ (1-indexed, preceding Eq. (5.11)); $U_0(p)=\emptyset$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.127, preceding Eq. (5.11).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.127, preceding Eq. (5.11)

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexSetsB_FracVec
import Definitions.Def_DiscreteConvex_LConvexSetsB_FracSortedValues

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.127, preceding Eq. (5.11): the level
sets `Uᵢ(p)`, in `DiscreteConvex.LConvexSetsB`.
-/

namespace DiscreteConvex.LConvexSetsB

open Classical in
/-- The `i`-th level set `Uᵢ(p) = \{v ∈ V : a(v) ≥ αᵢ\}` (1-indexed, preceding Eq. (5.11));
`U₀(p) = ∅`. -/
noncomputable def FracLevelSet {V : Type*} [Fintype V] [DecidableEq V] (p : V → ℝ) (i : ℕ) :
    Finset V :=
  if i = 0 then ∅ else Finset.univ.filter (fun v => (FracSortedValues p).getD (i - 1) 0 ≤ FracVec p v)

end DiscreteConvex.LConvexSetsB


