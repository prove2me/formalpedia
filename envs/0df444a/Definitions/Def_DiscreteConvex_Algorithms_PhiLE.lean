-- Prove2me | Definitions.Def_DiscreteConvex_Algorithms_PhiLE
-- name    : DiscreteConvex_Algorithms_PhiLE
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:23:44.608731+00:00
-- url     : https://prove2.me/theorems/3519f92a-b71f-4f41-8a74-32a1b6cbef7f
-- title:
--   Lexicographic order on tie-breaking keys
-- statement:
--   The lexicographic order on $\mathbb Z \times \mathbb Z \times \mathbb Z$ used to compare tie-breaking keys $\Phi(u,v)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.282, Eq. (10.2).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.282, Eq. (10.2)

import Mathlib

namespace DiscreteConvex.Algorithms

/-- The lexicographic order on `ℤ × ℤ × ℤ` used to compare tie-breaking keys `Φ(u,v)`. -/
def PhiLE (a b : ℤ × ℤ × ℤ) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧ a.2.2 ≤ b.2.2)))

end DiscreteConvex.Algorithms


