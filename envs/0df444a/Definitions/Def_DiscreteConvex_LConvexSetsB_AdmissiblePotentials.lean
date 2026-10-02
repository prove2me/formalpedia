-- Prove2me | Definitions.Def_DiscreteConvex_LConvexSetsB_AdmissiblePotentials
-- name    : DiscreteConvex_LConvexSetsB_AdmissiblePotentials
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:41:33.600432+00:00
-- url     : https://prove2.me/theorems/c4dcb259-e7b2-481f-acca-45f58bcc86a0
-- title:
--   AdmissiblePotentials
-- statement:
--   The set $D(\gamma) = \{p \in \mathbb R^V : p(v)-p(u) \le \gamma(u,v)\ (\forall u \ne v)\}$ of **admissible (feasible) potentials** of a distance function $\gamma$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122, Eq. (5.3)-(5.4).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122, Eq. (5.3)-(5.4)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.122, Eq. (5.3)-(5.4): the set of
admissible potentials of a distance function, in `DiscreteConvex.LConvexSetsB`.
-/

namespace DiscreteConvex.LConvexSetsB

/-- The set `D(γ)` of **admissible (feasible) potentials** of a distance function `γ`,
Eq. (5.3)-(5.4). -/
def AdmissiblePotentials {V : Type*} (γ : V → V → WithTop ℝ) : Set (V → ℝ) :=
  {p : V → ℝ | ∀ u v, u ≠ v → ((p v - p u : ℝ) : WithTop ℝ) ≤ γ u v}

end DiscreteConvex.LConvexSetsB


