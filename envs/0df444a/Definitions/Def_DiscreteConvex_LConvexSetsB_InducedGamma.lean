-- Prove2me | Definitions.Def_DiscreteConvex_LConvexSetsB_InducedGamma
-- name    : DiscreteConvex_LConvexSetsB_InducedGamma
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:41:57.600232+00:00
-- url     : https://prove2.me/theorems/21fd86e4-45cc-470c-8939-96ef14319b6c
-- title:
--   InducedGamma
-- statement:
--   The distance function $\gamma(u,v) = \sup\{p(v)-p(u) : p \in D\}$ induced by a set $D \subseteq \mathbb Z^V$ of integer vectors, Eq. (5.8).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.124, Eq. (5.8).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.124, Eq. (5.8)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.124, Eq. (5.8): the distance function
induced by a set of integer vectors, in `DiscreteConvex.LConvexSetsB`.
-/

namespace DiscreteConvex.LConvexSetsB

open Classical in
/-- The distance function `γ(u,v) = sup\{p(v)-p(u) : p ∈ D\}` induced by a set `D ⊆ Zⱽ` of
integer vectors, Eq. (5.8). -/
noncomputable def InducedGamma {V : Type*} [Fintype V] (D : Set (V → ℤ)) (u v : V) : WithTop ℝ :=
  sSup ((fun p : V → ℤ => (((p v - p u : ℤ) : ℝ) : WithTop ℝ)) '' D)

end DiscreteConvex.LConvexSetsB


