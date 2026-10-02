-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexity_LocalConvexExtension
-- name    : DiscreteConvex_IntegralConvexity_LocalConvexExtension
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:49:28.084617+00:00
-- url     : https://prove2.me/theorems/fc52d8f8-ca29-4a7e-8bac-c62b66963338
-- title:
--   Local convex extension (Eq. 3.61)
-- statement:
--   The **local convex extension** $\tilde f : \mathbb R^n \to \mathbb R \cup \{\pm\infty\}$ of $f$ (Eq. (3.61)) is the same supremum as the convex closure, but with the affine minorant condition $\langle p,y\rangle + \alpha \le f(y)$ imposed only for $y \in N(x)$ rather than for all $y \in \mathbb Z^n$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93, Eq. (3.61).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93, Eq. (3.61)

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexity_IntegralNeighborhood

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.93, Eq. (3.61): the local convex extension of
a function on the integer lattice, in `DiscreteConvex.IntegralConvexity`.
-/

namespace DiscreteConvex.IntegralConvexity

/-- The local convex extension `f̃ : Rⁿ → R ∪ {±∞}` of `f : Zⁿ → R ∪ {+∞}` (Eq. (3.61)):
the same supremum as the convex closure, but with the affine minorant condition imposed only
on the integral neighborhood `N(x)` rather than on all of `Zⁿ`. -/
noncomputable def LocalConvexExtension {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) (x : Fin n → ℝ) :
    EReal :=
  sSup {v : EReal | ∃ (p : Fin n → ℝ) (α : ℝ),
    (∀ y ∈ IntegralNeighborhood x, ((α + ∑ i, p i * (y i : ℝ) : ℝ) : EReal) ≤ WithBot.some (f y)) ∧
    v = ((α + ∑ i, p i * x i : ℝ) : EReal)}

end DiscreteConvex.IntegralConvexity


