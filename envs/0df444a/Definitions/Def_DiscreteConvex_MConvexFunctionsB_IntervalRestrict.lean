-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsB_IntervalRestrict
-- name    : DiscreteConvex_MConvexFunctionsB_IntervalRestrict
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:06:40.320985+00:00
-- url     : https://prove2.me/theorems/92795764-c863-41ad-96cc-c203278e76ca
-- title:
--   IntervalRestrict
-- statement:
--   The restriction of $f$ to the integer interval $[a,b]$ with $a,b \in (\mathbb Z \cup \{\pm\infty\})^V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.55), reused p.143.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.55), reused p.143

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.98, Eq. (3.55), reused p.143, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- The restriction of `f` to the integer interval `[a,b]` with `a, b : V → Z ∪ {±∞}`
(represented as `WithBot (WithTop ℤ)`). -/
noncomputable def IntervalRestrict {V : Type*} [Fintype V] (f : (V → ℤ) → WithTop ℝ) (a b : V → WithBot (WithTop ℤ)) :
    (V → ℤ) → WithTop ℝ :=
  fun x => if (∀ v, a v ≤ ((x v : WithTop ℤ) : WithBot (WithTop ℤ)) ∧
      ((x v : WithTop ℤ) : WithBot (WithTop ℤ)) ≤ b v) then f x else ⊤

end DiscreteConvex.MConvexFunctionsB


