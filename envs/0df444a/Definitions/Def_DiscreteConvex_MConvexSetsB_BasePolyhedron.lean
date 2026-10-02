-- Prove2me | Definitions.Def_DiscreteConvex_MConvexSetsB_BasePolyhedron
-- name    : DiscreteConvex_MConvexSetsB_BasePolyhedron
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:26:25.120871+00:00
-- url     : https://prove2.me/theorems/83063205-185b-4570-b3ab-d6256b891113
-- title:
--   BasePolyhedron
-- statement:
--   The **base polyhedron** $B(\rho) = \{x \in \mathbb R^V : x(X) \le \rho(X)\ (\forall X \subseteq V),\ x(V)=\rho(V)\}$ of a submodular set function $\rho$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.104, Eq. (4.13).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.104, Eq. (4.13)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.104, Eq. (4.13): the base polyhedron of a
submodular set function, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- The **base polyhedron** `B(ρ) = \{x ∈ Rⱽ : x(X) ≤ ρ(X)\ (∀X ⊆ V),\ x(V) = ρ(V)\}` of a
submodular set function `ρ` (Eq. (4.13)). -/
def BasePolyhedron {V : Type*} [Fintype V] [DecidableEq V] (ρ : Finset V → WithTop ℝ) :
    Set (V → ℝ) :=
  {x | (∀ X : Finset V, ((∑ v ∈ X, x v : ℝ) : WithTop ℝ) ≤ ρ X) ∧
    ((∑ v : V, x v : ℝ) : WithTop ℝ) = ρ Finset.univ}

end DiscreteConvex.MConvexSetsB


