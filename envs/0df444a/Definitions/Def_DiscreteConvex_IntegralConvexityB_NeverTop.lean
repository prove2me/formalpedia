-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityB_NeverTop
-- name    : DiscreteConvex_IntegralConvexityB_NeverTop
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:58:01.611661+00:00
-- url     : https://prove2.me/theorems/4a54db99-2687-4209-acb3-05f6c67fe61b
-- title:
--   Never +infinity (h : Rn -> R cup {-infty})
-- statement:
--   $h$ never takes the value $+\infty$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.98: the typing constraint `h : Rⁿ → R ∪ {-∞}`
(never `+∞`), in `DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `h` never takes the value `+∞` (the book's typing `h : Rⁿ → R ∪ \{-∞\}`). -/
def NeverTop {V : Type*} (h : (V → ℝ) → EReal) : Prop :=
  ∀ x, h x ≠ ⊤

end DiscreteConvex.IntegralConvexityB


