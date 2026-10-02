-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_BasePolyhedron
-- name    : DiscreteConvex_LConvexFunctionsD_BasePolyhedron
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:59:31.094537+00:00
-- url     : https://prove2.me/theorems/3822f41a-7d69-4921-b7de-44b055c2c3dc
-- title:
--   BasePolyhedron
-- statement:
--   The base polyhedron $B(\rho)=\{x\in\mathbb R^V: x(X)\le\rho(X)\ (\forall X),\ x(V)=\rho(V)\}$ of a submodular set function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.104, Eq. (4.13).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.104, Eq. (4.13)

import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The base polyhedron `B(ρ) = {x ∈ Rⱽ : x(X) ≤ ρ(X)\ (∀X), x(V) = ρ(V)}` of a submodular set
function. -/
def BasePolyhedron (rho : Finset V → WithTop ℝ) : Set (V → ℝ) :=
  {x | (∀ X : Finset V, ((∑ v ∈ X, x v : ℝ) : WithTop ℝ) ≤ rho X) ∧
    ((∑ v : V, x v : ℝ) : WithTop ℝ) = rho Finset.univ}

end DiscreteConvex.LConvexFunctionsD


