-- Prove2me | Definitions.Def_PertComp_IsReflexive
-- name    : PertComp_IsReflexive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:18.338726+00:00
-- url     : https://prove2.me/theorems/ec5421d4-0103-463c-85c1-0bd625d3efe3
-- title:
--   Reflexive real Banach space
-- statement:
--   A real normed space $X$ is **reflexive** when the canonical embedding $J\colon X\to X^{**}$, $(Jx)(x^*)=\langle x,x^*\rangle$, is onto. Problem 1.1 and every result of §2–§3 used in this mission take place in reflexive real Banach spaces; reflexivity is what identifies $X^{**}$ with $X$, so that subgradients of functions on a dual space can be read as points of the original space.
--
--   **Formalization Note** Mathlib has no reflexivity class at the pinned revision, so reflexivity is the predicate "`NormedSpace.inclusionInDoubleDual ℝ X` is surjective", assumed explicitly; completeness is the separate instance `[CompleteSpace X]`.
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, Problem 1.1, p.2

import Mathlib

namespace PertComp

/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, Problem 1.1, p.2 (and Definition 2.10, p.9):
a real Banach space `X` is *reflexive* when the canonical embedding `J : X → X**`,
`J x = (x* ↦ ⟨x, x*⟩)`, is onto.

**Formalization Note.** Mathlib (rev 0df444a3) has no reflexivity class, so reflexivity is this
predicate on `NormedSpace.inclusionInDoubleDual ℝ X`, taken as an explicit hypothesis. -/
def IsReflexive (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X)

end PertComp


