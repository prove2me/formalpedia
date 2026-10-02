-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsB_LiftedSet
-- name    : DiscreteConvex_MConvexFunctionsB_LiftedSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:06:07.232416+00:00
-- url     : https://prove2.me/theorems/86957a3c-00c4-4753-9a31-a9488ae2e115
-- title:
--   LiftedSet
-- statement:
--   The lift of a set $D \subseteq \mathbb Z^V$ to $\tilde V = \{0\} \cup V$, matching the lift of a function (Eq. (6.4)).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.121, supporting Proposition 6.7.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.121, supporting Proposition 6.7

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.121, supporting Proposition 6.7, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- The lift of a set `D ⊆ Zⱽ` to `Ṽ = \{0\} ∪ V`, matching the lift `f̃` of a function
(Eq. (6.4)). -/
def LiftedSet {V : Type*} [Fintype V] (D : Set (V → ℤ)) : Set (Option V → ℤ) :=
  {x | x none = -(∑ v : V, x (some v)) ∧ (fun v => x (some v)) ∈ D}

end DiscreteConvex.MConvexFunctionsB


