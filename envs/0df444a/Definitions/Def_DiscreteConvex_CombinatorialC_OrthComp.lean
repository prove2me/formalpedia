-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_OrthComp
-- name    : DiscreteConvex_CombinatorialC_OrthComp
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:40:19.102732+00:00
-- url     : https://prove2.me/theorems/3dadd830-1cb3-46c0-a41c-3a082bcf983e
-- title:
--   Orthogonal complement of a set
-- statement:
--   $X^\perp=\{p : \langle p,x\rangle=0\ \forall x\in X\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.73, Eq. (2.26).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.73, Eq. (2.26)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.73, Eq. (2.26): the orthogonal complement of a
set, in `DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- `X⊥ = \{p ∈ Rⁿ | ⟨p,x⟩ = 0\ (∀x ∈ X)\}` (Eq. (2.26)). -/
def OrthComp {V : Type*} [Fintype V] (X : Set (V → ℝ)) : Set (V → ℝ) :=
  {p | ∀ x ∈ X, dotProduct p x = 0}

end DiscreteConvex.CombinatorialC


