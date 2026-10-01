-- Prove2me | Definitions.Def_LiouvilleDiffAlg_Form
-- name    : LiouvilleDiffAlg_Form
-- status  : Definition
-- author  : @vebis
-- created : 2026-10-01T10:19:51.868681+00:00
-- url     : https://prove2.me/theorems/1597029c-8df4-4003-a10a-f53624abcdd1
-- title:
--   Liouville form of an element relative to a subset
-- statement:
--   Let $G$ be a differential field with derivation $D$ and let $S\subseteq G$ be a subset. An element $h\in G$ has **Liouville form in $S$** if there exist an integer $n\ge 0$, constants $c_1,\dots,c_n\in\operatorname{Con}(G)$, nonzero elements $u_1,\dots,u_n\in S$ and an element $v\in S$ such that
--
--   $$h = c_1\frac{Du_1}{u_1}+\cdots+c_n\frac{Du_n}{u_n}+Dv.$$
--
--   For $n=0$ the sum is empty and the condition reads $h=Dv$. This is the shape of the conclusion of Liouville's theorem on elementary antiderivatives; the predicate packages it so that the one-step descent lemmas of the inductive proof (from an intermediate field of a tower to the next smaller one) can be stated without repeating the existential quantifiers.
--
--   **Formalization Note** The constants $c_i$ range over all of $\operatorname{Con}(G)$, not over the constants of a smaller field; the descent lemmas assume $\operatorname{Con}(G)\subseteq K$ for the field $K$ they descend to.
-- source:
--   Wikipedia, "Liouville's theorem (differential algebra)", revision oldid=1349223559, section "Basic theorem"; proof: Geddes–Czapor–Labahn, Algorithms for Computer Algebra (Kluwer, 1992), §12.4; Rosenlicht, Integration in finite terms, Amer. Math. Monthly 79 (1972), 963–972

import Mathlib
import Definitions.Def_LiouvilleDiffAlg_Basic

namespace LiouvilleDiffAlg

open scoped Differential

/-- `h ∈ G` has *Liouville form in `S`* if
`h = c₁ · Du₁/u₁ + ⋯ + cₙ · Duₙ/uₙ + Dv` for some `n ≥ 0`, constants `cᵢ ∈ Con(G)`,
nonzero elements `uᵢ ∈ S` and an element `v ∈ S`. -/
def LiouvilleFormIn {G : Type*} [Field G] [Differential G] (S : Set G) (h : G) : Prop :=
  ∃ (n : ℕ) (c u : Fin n → G) (v : G),
    (∀ i, c i ∈ constants G) ∧ (∀ i, u i ∈ S ∧ u i ≠ 0) ∧ v ∈ S ∧
      h = ∑ i, c i * ((u i)′ / u i) + v′

end LiouvilleDiffAlg


