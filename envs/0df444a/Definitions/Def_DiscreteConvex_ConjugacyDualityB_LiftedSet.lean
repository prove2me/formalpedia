-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_LiftedSet
-- name    : DiscreteConvex_ConjugacyDualityB_LiftedSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:27:03.420946+00:00
-- url     : https://prove2.me/theorems/38ab009f-bce9-4de7-89a5-2a2b991c1f7b
-- title:
--   LiftedSet
-- statement:
--   The lift of a set $D\subseteq\mathbb Z^V$ to $\mathbb Z^{\tilde V}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, set analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, set analogue

import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The lift of a set `D ⊆ Zⱽ` to `Z^Ṽ`. -/
def LiftedSet (D : Set (V → ℤ)) : Set (Option V → ℤ) :=
  {x | x none = -(∑ v : V, x (some v)) ∧ (fun v => x (some v)) ∈ D}

end DiscreteConvex.ConjugacyDualityB


