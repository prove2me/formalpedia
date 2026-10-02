-- Prove2me | Definitions.Def_DiscreteConvex_MConvexSets_SubmodularPolyhedron
-- name    : DiscreteConvex_MConvexSets_SubmodularPolyhedron
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:16:27.523227+00:00
-- url     : https://prove2.me/theorems/9e2b32e0-7ff3-4778-a645-c58047ff8c2c
-- title:
--   Submodular polyhedron (Eq. 4.28)
-- statement:
--   The **submodular polyhedron** $P(\rho) = \{x \in \mathbb R^V : x(X) \le \rho(X)\ (\forall X \subseteq V)\}$ of a submodular set function $\rho$; unlike the base polyhedron $B(\rho)$, no equality constraint at $V$ is imposed.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.111, Eq. (4.28).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.111, Eq. (4.28)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.111, Eq. (4.28): the submodular polyhedron of
a submodular set function, in `DiscreteConvex.MConvexSets`.
-/

namespace DiscreteConvex.MConvexSets

/-- The **submodular polyhedron** `P(ρ) = \{x ∈ Rⱽ : x(X) ≤ ρ(X)\ (∀X ⊆ V)\}` of a submodular
set function `ρ` (Eq. (4.28)); unlike the base polyhedron `B(ρ)`, no equality constraint at
`V` is imposed. -/
def SubmodularPolyhedron {V : Type*} [Fintype V] [DecidableEq V] (ρ : Finset V → WithTop ℝ) :
    Set (V → ℝ) :=
  {x | ∀ X : Finset V, ((∑ v ∈ X, x v : ℝ) : WithTop ℝ) ≤ ρ X}

end DiscreteConvex.MConvexSets


