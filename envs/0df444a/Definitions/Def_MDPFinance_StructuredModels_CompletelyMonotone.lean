-- Prove2me | Definitions.Def_MDPFinance_StructuredModels_CompletelyMonotone
-- name    : MDPFinance_StructuredModels_CompletelyMonotone
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T20:32:06.018044+00:00
-- url     : https://prove2.me/theorems/0a2bb93c-f8c6-4ed4-907d-8a85b03f5563
-- title:
--   Completely monotone sets (Definition 2.4.15)
-- statement:
--   A subset $D \subseteq E \times A$ of a product of preordered sets is **completely monotone**
--   if, whenever $(x,a')$ and $(x',a)$ both lie in $D$ with $x \leq x'$ and $a \leq a'$, both
--   $(x,a)$ and $(x',a')$ also lie in $D$.
--
--   $$
--   D \text{ completely monotone} :\iff \forall x \leq x',\, a \leq a':\ (x,a'), (x',a) \in D \implies (x,a), (x',a') \in D.
--   $$
--
--   A leading special case (noted by the source but not separately formalized here) is $D(x)$
--   independent of $x$; for $A = \mathbb{R}$ and $D(x) = [\underline d(x), \overline d(x)]$, $D$ is
--   completely monotone iff $\underline d, \overline d$ are both increasing.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 35, Definition 2.4.15

import Mathlib

namespace MDPFinance.StructuredModels

variable {E A : Type*} [Preorder E] [Preorder A]

/-- A set `D ⊂ E × A` is called completely monotone (Bäuerle–Rieder, Definition 2.4.15, p. 35,
PDF 50) if for all points `(x,a'), (x',a) ∈ D` with `x ≤ x'` and `a ≤ a'` it follows that
`(x,a), (x',a') ∈ D`. -/
def CompletelyMonotone (D : Set (E × A)) : Prop :=
  ∀ x x' a a', x ≤ x' → a ≤ a' → (x, a') ∈ D → (x', a) ∈ D → (x, a) ∈ D ∧ (x', a') ∈ D

end MDPFinance.StructuredModels


