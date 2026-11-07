-- Prove2me | Definitions.Def_AggCG_pdimClass
-- name    : AggCG_pdimClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:08:14.370208+00:00
-- url     : https://prove2.me/theorems/e6fdd915-b2c2-4f57-b024-503b6ac1d075
-- title:
--   The tree-size loss family on $X_m$
-- statement:
--   The function class of Proposition I.4 on the domain $X_m$:
--   $$\{I\mapsto\mathrm{TreeSize}_u(I):u\in[0,1]^m\}.$$
--   Its pseudo-dimension is the statistical capacity bounded in Theorem 2.1.
-- source:
--   Sharma, Computational Complexity of Data-Driven Configuration for Integer Programming, Clustering, and Learning Algorithms, STOC 2027 submission (manuscript sha256 f7ea0248…), Proposition I.4, p.52 (PDF p.53)

import Mathlib
import Definitions.Def_AggCG_BBSize
import Definitions.Def_AggCG_Gadget

namespace AggCG

/-- The tree-size loss family of Proposition I.4, p.52 (PDF p.53; Sharma, *Computational Complexity of Data-Driven Configuration for Integer Programming, Clustering, and Learning Algorithms*, STOC 2027 submission (manuscript sha256 f7ea0248…)): `{I ↦ TreeSize_u(I) : u ∈ [0, 1]^m}` on the family `X_m`. -/
def pdimClass (m : ℕ) : Set ({G : Gadget m // G.Valid} → ℝ) :=
  {g | ∃ u : Fin m → ℝ, InUnitBox u ∧ ∀ G, g G = ((treeSize G.1.toIP u : ℕ) : ℝ)}

end AggCG


