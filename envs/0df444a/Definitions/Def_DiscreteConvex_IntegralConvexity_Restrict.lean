-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexity_Restrict
-- name    : DiscreteConvex_IntegralConvexity_Restrict
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:49:29.257262+00:00
-- url     : https://prove2.me/theorems/0193ffd2-32de-4f9e-be51-168678a565f2
-- title:
--   Restriction of a function to an integer interval (Eq. 3.55)
-- statement:
--   The **restriction** $f_{[a,b]} : \mathbb Z^n \to \mathbb R \cup \{+\infty\}$ of $f$ to the integer interval $[a,b]$ (Eq. (3.55)): agrees with $f$ on $[a,b]$ and is $+\infty$ outside it.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.92, Eq. (3.55).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.92, Eq. (3.55)

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexity_IntegerInterval

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.92, Eq. (3.55): the restriction of a function
to an integer interval, in `DiscreteConvex.IntegralConvexity`.
-/

namespace DiscreteConvex.IntegralConvexity

open Classical in
/-- The restriction `f_{[a,b]} : Zⁿ → R ∪ {+∞}` of `f` to the integer interval `[a,b]`
(Eq. (3.55)): agrees with `f` on `[a,b]` and is `+∞` outside it. -/
noncomputable def Restrict {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) (a b : Fin n → ℤ) :
    (Fin n → ℤ) → WithTop ℝ :=
  fun x => if x ∈ IntegerInterval a b then f x else ⊤

end DiscreteConvex.IntegralConvexity


