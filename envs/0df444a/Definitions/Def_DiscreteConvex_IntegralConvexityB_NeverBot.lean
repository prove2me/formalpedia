-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityB_NeverBot
-- name    : DiscreteConvex_IntegralConvexityB_NeverBot
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:58:00.443076+00:00
-- url     : https://prove2.me/theorems/97679b64-93e3-4493-a599-2ddd30ee9107
-- title:
--   Never -infinity (f : Rn -> R cup {+infty})
-- statement:
--   $f$ never takes the value $-\infty$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.79.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.79

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.79: the typing constraint `f : Rⁿ → R ∪ {+∞}`
(never `-∞`), in `DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `f` never takes the value `-∞` (the book's typing `f : Rⁿ → R ∪ \{+∞\}`). -/
def NeverBot {V : Type*} (f : (V → ℝ) → EReal) : Prop :=
  ∀ x, f x ≠ ⊥

end DiscreteConvex.IntegralConvexityB


