-- Prove2me | Definitions.Def_Supermodularity_Matching_StrictlySupermodularOn
-- name    : Supermodularity_Matching_StrictlySupermodularOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:20:56.889763+00:00
-- url     : https://prove2.me/theorems/29c006a5-ea09-4ce6-aa31-8e3a8963afd4
-- title:
--   A strictly supermodular function on a set (§2.6.1)
-- statement:
--   Let $X$ be a lattice and $f : X \to \mathbb{R}$. Restricted to a subset $S \subseteq X$,
--   $f$ is **strictly supermodular on $S$** if
--   $$f(x') + f(x'') < f(x' \vee x'') + f(x' \wedge x'')$$
--   for every pair of *unordered* (mutually incomparable) $x', x'' \in S$. Taking $S$ to be the
--   whole lattice recovers Topkis's plain "$f$ is strictly supermodular on $X$."
--
--   Topkis (p. 43): "If $f(x') + f(x'') < f(x' \vee x'') + f(x' \wedge x'')$ for all unordered
--   $x'$ and $x''$ in $X$, then $f(x)$ is strictly supermodular on $X$." Comparable pairs are
--   excluded because for them $x' \vee x'' $ and $x' \wedge x''$ equal $\{x',x''\}$ in some
--   order and the inequality would reduce to a false strict inequality between equal sums.
--
--   **Formalization Note.** This mission applies `StrictlySupermodularOn` both to $f$ as a
--   function of $x$ alone, for each fixed firm $j$ (Theorem 3.2.4), and to $f$ as a function of
--   the joint pair $(x,j)$ on the product lattice $\bigl(\prod_i X_i\bigr) \times \{1,\dots,m\}$
--   (Theorem 3.2.5, with $\mathrm{Fin}\,m$ ordered as a chain) — these are genuinely different
--   hypotheses, kept as separate applications of the same definition rather than merged.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 43, Section 2.6.1

import Mathlib

/-!
Topkis, *Supermodularity and Complementarity*, Princeton University Press, 2011,
p. 44, Section 2.6.1 (definition of a strictly supermodular function).
-/

namespace Supermodularity.Matching

/-- `StrictlySupermodularOn f S` says the real-valued function `f` on a lattice `X` is
*strictly* supermodular on `S ⊆ X`: `f x + f y < f (x ⊔ y) + f (x ⊓ y)` for every pair of
*unordered* (incomparable) `x y ∈ S`. Taking `S = Set.univ` recovers Topkis's plain "`f` is
strictly supermodular on `X`". -/
def StrictlySupermodularOn {X : Type*} [Lattice X] (f : X → ℝ) (S : Set X) : Prop :=
  ∀ ⦃x : X⦄, x ∈ S → ∀ ⦃y : X⦄, y ∈ S → ¬ x ≤ y → ¬ y ≤ x →
    f x + f y < f (x ⊔ y) + f (x ⊓ y)

end Supermodularity.Matching


