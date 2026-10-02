-- Prove2me | Definitions.Def_DiscreteConvex_LConvexSetsB_IntEmbed
-- name    : DiscreteConvex_LConvexSetsB_IntEmbed
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:41:52.880736+00:00
-- url     : https://prove2.me/theorems/0c6c8b5f-fccd-4b75-9c97-b0290032b271
-- title:
--   IntEmbed
-- statement:
--   The real embedding $\{(x(v):\mathbb R) : x \in D\} \subseteq \mathbb R^V$ of a set $D \subseteq \mathbb Z^V$ of integer vectors.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.122-128 (supporting several results).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.122-128 (supporting several results)

import Mathlib

/-!
The real embedding `Zⱽ ↪ Rⱽ` of a set of integer vectors, used throughout this mission
(Murota, *Discrete Convex Analysis*, SIAM 2003, pp.122-128), in
`DiscreteConvex.LConvexSetsB`.
-/

namespace DiscreteConvex.LConvexSetsB

/-- The real embedding `\{(x(v):ℝ) : x ∈ D\}` of a set `D ⊆ Zⱽ` of integer vectors. -/
def IntEmbed {V : Type*} (D : Set (V → ℤ)) : Set (V → ℝ) :=
  (fun x : V → ℤ => fun v => (x v : ℝ)) '' D

end DiscreteConvex.LConvexSetsB


