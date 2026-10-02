-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctions_DiscreteMidpointConvexity
-- name    : DiscreteConvex_LConvexFunctions_DiscreteMidpointConvexity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:14:17.00623+00:00
-- url     : https://prove2.me/theorems/bdf3270e-b3ff-44c9-898d-5f092bd6d44b
-- title:
--   Discrete midpoint convexity (Eq. 7.7)
-- statement:
--   **Discrete midpoint convexity**: $g(p)+g(q) \ge g(\lceil (p+q)/2 \rceil) + g(\lfloor (p+q)/2 \rfloor)$ for all $p,q \in \mathbb Z^V$ — the direct discrete analogue of ordinary midpoint convexity, and a distinctively L-convex phenomenon with no M-convex counterpart.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.180, Eq. (7.7).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.180, Eq. (7.7)

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctions_MidpointFloor
import Definitions.Def_DiscreteConvex_LConvexFunctions_MidpointCeil

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.180, Eq. (7.7): discrete midpoint convexity,
in `DiscreteConvex.LConvexFunctions`.
-/

namespace DiscreteConvex.LConvexFunctions

/-- **Discrete midpoint convexity** (Eq. (7.7)): `g(p) + g(q) ≥ g(⌈(p+q)/2⌉) + g(⌊(p+q)/2⌋)`
for all `p, q ∈ Zⱽ`. -/
noncomputable def DiscreteMidpointConvexity {V : Type*} (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p q : V → ℤ, g p + g q ≥ g (MidpointCeil p q) + g (MidpointFloor p q)

end DiscreteConvex.LConvexFunctions


