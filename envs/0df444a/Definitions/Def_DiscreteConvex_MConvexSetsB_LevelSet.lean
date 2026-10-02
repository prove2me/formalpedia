-- Prove2me | Definitions.Def_DiscreteConvex_MConvexSetsB_LevelSet
-- name    : DiscreteConvex_MConvexSetsB_LevelSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:29:16.409472+00:00
-- url     : https://prove2.me/theorems/0017c82f-730e-4596-ad3c-a82b1c1cb6b1
-- title:
--   LevelSet
-- statement:
--   The $i$-th level set $U_i = \{v \in V : p(v) \ge \hat p_i\}$ (1-indexed, Eq. (4.4)), the threshold sets whose indicators represent $p$ as $p = \sum_{i=1}^{m-1}(\hat p_i-\hat p_{i+1})\chi_{U_i} + \hat p_m \chi_{U_m}$ (Eq. (4.5)).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.103, Eq. (4.4).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.103, Eq. (4.4)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_SortedValues

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.103, Eq. (4.4): the level sets `Uᵢ` used in
the Lovász extension, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

open Classical in
/-- The `i`-th level set `Uᵢ = \{v ∈ V : p(v) ≥ p̂ᵢ\}` (1-indexed, Eq. (4.4)); `i = 0` is unused
and returns `∅` by the `getD` default. -/
noncomputable def LevelSet {V : Type*} [Fintype V] [DecidableEq V] (p : V → ℝ) (i : ℕ) :
    Finset V :=
  Finset.univ.filter (fun v => (SortedValues p).getD (i - 1) 0 ≤ p v)

end DiscreteConvex.MConvexSetsB


