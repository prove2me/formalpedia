-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctions_ArgMin
-- name    : DiscreteConvex_LConvexFunctions_ArgMin
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:13:34.07323+00:00
-- url     : https://prove2.me/theorems/f623d57b-5425-454f-8ff7-aa412102957f
-- title:
--   Minimizer set on the integer lattice
-- statement:
--   The minimizer set $\arg\min g = \{p \in \mathbb Z^V : g(p) \le g(q)\ \forall q \in \mathbb Z^V\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.186.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.186

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.186: the minimizer set of a function on the
integer lattice, in `DiscreteConvex.LConvexFunctions`.
-/

namespace DiscreteConvex.LConvexFunctions

/-- The minimizer set `arg min g = \{p ∈ Zⱽ : g(p) ≤ g(q)\ ∀q ∈ Zⱽ\}`. -/
def ArgMin {V : Type*} (g : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) :=
  {p | ∀ q, g p ≤ g q}

end DiscreteConvex.LConvexFunctions


