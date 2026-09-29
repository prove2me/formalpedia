-- Prove2me | Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
-- name    : Supermodularity_Monotonicity_SupermodularOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T05:26:03.506158+00:00
-- url     : https://prove2.me/theorems/c18de795-dbd1-4c1d-a8c3-841f0b199d2b
-- title:
--   A supermodular function, possibly relativized to a subset of a lattice
-- statement:
--   Let $X$ be a **lattice** with join $\vee$ and meet $\wedge$, and let $f : X \to \mathbb{R}$
--   be a real-valued function. For a subset $S \subseteq X$, $f$ is **supermodular on $S$** if
--
--   $$
--   f(x) + f(y) \;\le\; f(x \vee y) + f(x \wedge y) \qquad \text{for all } x, y \in S.
--   $$
--
--   Taking $S = X$ (the whole lattice) recovers Topkis's plain notion "$f$ is supermodular on
--   $X$," used, for instance, in Theorem 2.7.1. The relativized form with $S$ a proper subset
--   is needed to express "$f(x,t)$ is supermodular in $(x,t)$ **jointly** on a sublattice $S$
--   of $X \times T$" (Theorem 2.8.2), which is a strictly stronger hypothesis than "$f(x,t)$ is
--   supermodular in $x$ alone, for each fixed $t$."
--
--   **Formalization Note** A single relativized definition is used throughout this mission
--   (with `S := Set.univ` for the plain, unrelativized notion) so that the same declaration
--   captures both "$f$ supermodular on the whole lattice $X$" (Theorem 2.7.1, Theorem 2.8.1)
--   and "$f$ jointly supermodular on a sublattice $S$ of a product lattice $X \times T$"
--   (Theorem 2.8.2), exactly as the book itself states the same defining inequality in both
--   cases, with the domain being the only thing that changes.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 43, Section 2.6.1 (definition of a supermodular function)

import Mathlib

namespace Supermodularity.Monotonicity

/-- `SupermodularOn f S` says the real-valued function `f` on a lattice `X` is
supermodular on `S ⊆ X`: `f x + f y ≤ f (x ⊔ y) + f (x ⊓ y)` for all `x y ∈ S`. Taking
`S = Set.univ` recovers Topkis's plain "`f` is supermodular on `X`". -/
def SupermodularOn {X : Type*} [Lattice X] (f : X → ℝ) (S : Set X) : Prop :=
  ∀ ⦃x : X⦄, x ∈ S → ∀ ⦃y : X⦄, y ∈ S → f x + f y ≤ f (x ⊔ y) + f (x ⊓ y)

end Supermodularity.Monotonicity


