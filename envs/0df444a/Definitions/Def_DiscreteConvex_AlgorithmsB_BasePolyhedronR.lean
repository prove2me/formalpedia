-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_BasePolyhedronR
-- name    : DiscreteConvex_AlgorithmsB_BasePolyhedronR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:49:51.965421+00:00
-- url     : https://prove2.me/theorems/c0dc7530-fe0f-4ad4-b3f4-0e4f9a746091
-- title:
--   BasePolyhedronR
-- statement:
--   $x\in B(\rho)$, the base polyhedron.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.288, Eq. (10.9).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.288, Eq. (10.9)

import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `x ∈ B(ρ)`, the base polyhedron. -/
def BasePolyhedronR (rho : Finset V → ℤ) (x : V → ℝ) : Prop :=
  (∀ X : Finset V, ∑ v ∈ X, x v ≤ (rho X : ℝ)) ∧ (∑ v, x v = (rho Finset.univ : ℝ))

end DiscreteConvex.AlgorithmsB


