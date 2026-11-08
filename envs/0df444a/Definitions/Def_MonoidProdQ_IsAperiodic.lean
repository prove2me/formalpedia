-- Prove2me | Definitions.Def_MonoidProdQ_IsAperiodic
-- name    : MonoidProdQ_IsAperiodic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:40:10.14203+00:00
-- url     : https://prove2.me/theorems/5c61d1ee-e9d6-4814-8b7d-84ad658de8fd
-- title:
--   Aperiodic monoid
-- statement:
--   A monoid $M$ is **aperiodic** if every element eventually stops changing under powers: for every $a\in M$ there is an integer $k\ge 1$ with
--
--   $$a^k=a^{k+1}.$$
--
--   Finite aperiodic monoids are exactly the finite monoids with no nontrivial subgroup; they recognize the star-free languages. Every statement of this mission is about finite aperiodic monoids.
--
--   **Formalization Note** The predicate is defined for an arbitrary monoid; finiteness and commutativity are separate hypotheses wherever they are needed.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §1, p.4

import Mathlib

namespace MonoidProdQ

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §1, p.4: "A monoid (M, ⊗) is aperiodic if for every element a ∈ M, there is a
k ≥ 1 such that a^k = a^{k+1}."

**Formalization Note.** Defined for an arbitrary `Monoid`; finiteness and commutativity are
separate hypotheses of the statements that use them. -/
def IsAperiodic (M : Type*) [Monoid M] : Prop :=
  ∀ a : M, ∃ k : ℕ, 1 ≤ k ∧ a ^ k = a ^ (k + 1)

end MonoidProdQ


