-- Prove2me | Definitions.Def_UniqueOptScores_ceOpen
-- name    : UniqueOptScores_ceOpen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:27:09.18008+00:00
-- url     : https://prove2.me/theorems/85e99e45-e503-4479-a7e4-7f9a6bdd5aa7
-- title:
--   Open sets of a uniformly c.e. family
-- statement:
--   Let $W \subseteq \mathbb N \times \{0,1\}^*$ be a relation. For each $i$, $V_i$ is the union of the prefix cylinders of the strings $\sigma$ with $(i, \sigma) \in W$:
--   $$
--   V_i = \{\chi : \text{some initial segment } \sigma \text{ of } \chi \text{ has } (i,\sigma) \in W\}.
--   $$
--   Each $V_i$ is open, and when $W$ is computably enumerable, $(V_i)_i$ is a **uniformly computably enumerable family of open sets** (every finite-coordinate cylinder is effectively a finite union of prefix cylinders, p.30).
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Lemma 8.1, p.29; Section 8, p.30

import Mathlib
import Definitions.Def_UniqueOptScores_IsPrefixOf

namespace UniqueOptScores

/-- **The open sets of a uniformly c.e. family.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), Lemma 8.1, p.29: "a uniformly computably enumerable family of dense open sets (V_i) in
oracle Cantor space"; p.30: "Each finite-coordinate cylinder is effectively a finite union of
prefix cylinders."

For `W : ℕ × List Bool → Prop`, `ceOpen W i` is the union of the prefix cylinders of the strings
`σ` with `W (i, σ)`. When `W` is c.e. (`REPred W`), `(ceOpen W i)ᵢ` is a uniformly c.e. family of
open sets. -/
def ceOpen (W : ℕ × List Bool → Prop) (i : ℕ) : Set (List Bool → Bool) :=
  {χ | ∃ σ : List Bool, W (i, σ) ∧ IsPrefixOf σ χ}

end UniqueOptScores


