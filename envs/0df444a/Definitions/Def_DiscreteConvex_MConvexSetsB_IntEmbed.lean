-- Prove2me | Definitions.Def_DiscreteConvex_MConvexSetsB_IntEmbed
-- name    : DiscreteConvex_MConvexSetsB_IntEmbed
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:26:27.960041+00:00
-- url     : https://prove2.me/theorems/25b3f703-ae96-4924-9578-02e19f76006a
-- title:
--   IntEmbed
-- statement:
--   The real embedding $\{(x(v):\mathbb R) : x \in B\} \subseteq \mathbb R^V$ of a set $B \subseteq \mathbb Z^V$ of integer vectors, used to state closure identities such as the hole-free property.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.107-116 (supporting Theorems 4.12, 4.22, 4.23).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.107-116 (supporting Theorems 4.12, 4.22, 4.23)

import Mathlib

/-!
The real embedding `Zⱽ ↪ Rⱽ` of a set of integer vectors, used to state the hole-free
property (Theorem 4.12) and related closure identities (Murota, *Discrete Convex Analysis*,
SIAM 2003, pp.107-116), in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- The real embedding `\{(x(v):ℝ) : x ∈ B\}` of a set `B ⊆ Zⱽ` of integer vectors. -/
def IntEmbed {V : Type*} (B : Set (V → ℤ)) : Set (V → ℝ) :=
  (fun x : V → ℤ => fun v => (x v : ℝ)) '' B

end DiscreteConvex.MConvexSetsB


