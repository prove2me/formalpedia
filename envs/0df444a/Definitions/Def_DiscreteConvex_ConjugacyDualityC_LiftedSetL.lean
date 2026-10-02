-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_LiftedSetL
-- name    : DiscreteConvex_ConjugacyDualityC_LiftedSetL
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:41:10.863901+00:00
-- url     : https://prove2.me/theorems/b704490a-ea51-4310-8da0-03cd0312c2ee
-- title:
--   LiftedSetL
-- statement:
--   The lift of a set $D\subseteq\mathbb Z^V$ to $\mathbb Z^{\tilde V}$, L-side convention.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, set analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, set analogue

import Mathlib

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The lift of a set `D ⊆ Zⱽ` to `Z^Ṽ`, L-side convention. -/
def LiftedSetL (D : Set (V → ℤ)) : Set (Option V → ℤ) :=
  {p : Option V → ℤ | (fun v => p (some v) - p none) ∈ D}

end DiscreteConvex.ConjugacyDualityC


