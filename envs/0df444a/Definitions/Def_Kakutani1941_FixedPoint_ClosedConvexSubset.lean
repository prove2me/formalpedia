-- Prove2me | Definitions.Def_Kakutani1941_FixedPoint_ClosedConvexSubset
-- name    : Kakutani1941_FixedPoint_ClosedConvexSubset
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:02:51.730667+00:00
-- url     : https://prove2.me/theorems/ead0d822-b31d-4afb-bdf9-9d2c6a4d84cc
-- title:
--   Section 1 — the family of closed convex subsets of S
-- statement:
--   Let $S$ be a subset of a real normed vector space. A set $A$ belongs to Kakutani's family $\mathfrak R(S)$ precisely when it is a closed, convex subset of $S$:
--
--   $$A\subseteq S,\qquad A\text{ is closed},\qquad A\text{ is convex}. $$
--
--   The family specifies the possible values of the point-to-set mapping in Theorem 1 and its Corollary. The empty set belongs to $\mathfrak R(S)$; nonemptiness is imposed separately where the fixed-point assertions need it.
-- source:
--   Kakutani, A generalization of Brouwer's fixed point theorem, Duke Math. J. 8 (1941), p. 457, Section 1, https://doi.org/10.1215/s0012-7094-41-00838-4

import Mathlib

namespace Kakutani1941.FixedPoint

/-- The members of Kakutani's family ℜ(S), including the empty set. -/
def IsClosedConvexSubset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S A : Set E) : Prop :=
  A ⊆ S ∧ IsClosed A ∧ Convex ℝ A

end Kakutani1941.FixedPoint


