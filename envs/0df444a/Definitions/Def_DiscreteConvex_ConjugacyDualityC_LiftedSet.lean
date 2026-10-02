-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_LiftedSet
-- name    : DiscreteConvex_ConjugacyDualityC_LiftedSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:41:05.536359+00:00
-- url     : https://prove2.me/theorems/2cb369d0-a8e5-4b7a-96cf-809c6ded53e0
-- title:
--   LiftedSet
-- statement:
--   The lift of a set $D\subseteq\mathbb Z^V$ to $\mathbb Z^{\tilde V}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, set analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, set analogue

import Mathlib

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The lift of a set `D ⊆ Zⱽ` to `Z^Ṽ`. -/
def LiftedSet (D : Set (V → ℤ)) : Set (Option V → ℤ) :=
  {x | x none = -(∑ v : V, x (some v)) ∧ (fun v => x (some v)) ∈ D}

end DiscreteConvex.ConjugacyDualityC


