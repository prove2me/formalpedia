-- Prove2me | Definitions.Def_DiscreteConvex_LConvexSets_AdmissiblePotentials
-- name    : DiscreteConvex_LConvexSets_AdmissiblePotentials
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:35:19.105992+00:00
-- url     : https://prove2.me/theorems/f6a0823d-d2a9-4c0d-a1dc-392a72528799
-- title:
--   Admissible-potential polyhedron D(gamma) (Eq. 5.3-5.4)
-- statement:
--   The polyhedron of **admissible (feasible) potentials** of a distance function $\gamma$: $$D(\gamma) = \{p \in \mathbb R^V : p(v) - p(u) \le \gamma(u,v)\ (\forall u \ne v)\}.$$
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122, Eq. (5.3)-(5.4).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122, Eq. (5.3)-(5.4)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.122, Eq. (5.3)-(5.4): the polyhedron of
admissible potentials of a distance function, in `DiscreteConvex.LConvexSets`.
-/

namespace DiscreteConvex.LConvexSets

/-- The polyhedron of **admissible (feasible) potentials** of a distance function `γ`
(Eq. (5.4)): `D(γ) = \{p ∈ Rⱽ : p(v) - p(u) ≤ γ(u,v)\ (∀u ≠ v)\}`. -/
def AdmissiblePotentials {V : Type*} [DecidableEq V] (γ : V → V → WithTop ℝ) : Set (V → ℝ) :=
  {p | ∀ u v : V, u ≠ v → ((p v - p u : ℝ) : WithTop ℝ) ≤ γ u v}

end DiscreteConvex.LConvexSets


