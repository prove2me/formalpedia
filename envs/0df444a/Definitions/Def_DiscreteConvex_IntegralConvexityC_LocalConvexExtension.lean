-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityC_LocalConvexExtension
-- name    : DiscreteConvex_IntegralConvexityC_LocalConvexExtension
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:10:20.469985+00:00
-- url     : https://prove2.me/theorems/4c3dbf7b-4da6-4c25-a7b4-cecfc7a0ff22
-- title:
--   Local convex extension
-- statement:
--   As $\bar f$ but with the affine-minorant condition imposed only on $N(x)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93, Eq. (3.61).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93, Eq. (3.61)

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegralNeighborhood

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.93, Eq. (3.61): the local convex extension, in
`DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- The local convex extension `f̃ : Rⁿ → R ∪ {±∞}` (Eq. (3.61)). -/
noncomputable def LocalConvexExtension {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) (x : Fin n → ℝ) :
    EReal :=
  sSup {v : EReal | ∃ (p : Fin n → ℝ) (a : ℝ),
    (∀ y ∈ IntegralNeighborhood x, ((a + ∑ i, p i * (y i : ℝ) : ℝ) : EReal) ≤
      WithBot.some (f y)) ∧
    v = ((a + ∑ i, p i * x i : ℝ) : EReal)}

end DiscreteConvex.IntegralConvexityC


