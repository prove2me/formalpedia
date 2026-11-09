-- Prove2me | Definitions.Def_PhyloCSP_TreeTransformation
-- name    : PhyloCSP_TreeTransformation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:23:54.640052+00:00
-- url     : https://prove2.me/theorems/5f2b2565-da56-4069-9dad-cb0200f3284d
-- title:
--   Tree transformations $F$
-- statement:
--   A **tree transformation** $F$ assigns to every finite rooted binary tree $T$ a probability distribution $F[T]$ on trees with the same leaf set, and relabeling the leaves of $T$ induces the corresponding relabeling of the output distribution:
--   $$
--   F[\sigma T]=\sigma_*F[T]\qquad\text{for every bijection }\sigma\text{ of leaf sets.}
--   $$
--
--   Tree transformations are the rounding schemes of the paper's framework: the algorithm solves the canonical relaxation, obtaining a tree $T$, and outputs a sample of $F[T]$.
--
--   **Formalization Note** Leaf labels are natural numbers: an input is a pattern on a finite set $S\subseteq\mathbb N$, and $F[T]$ is a probability mass function on patterns on $S$. By the relabeling requirement, the law on any finite labeled tree is determined by a copy labeled in $\mathbb N$. The empty leaf set is included; it carries one pattern, so its law is forced.
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Definition 1.5, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_PhyloCSP_Pattern

set_option autoImplicit false

namespace PhyloCSP

/-- **Tree transformations (Definition 1.5).**

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Definition 1.5, p.3 (PDF p.5): "A tree transformation F
assigns to every finite rooted binary tree T a probability distribution on trees F[T] with the
same leaf set. We require that relabeling the leaves of T induce the corresponding relabeling of
the output distribution."

`law S T` is the distribution `F[T]` of the output for an input `T` on the finite leaf set `S`;
`equivariant` is the relabeling requirement, for every bijection of leaf sets.

**Formalization Note.** Leaf labels are natural numbers: finite leaf sets are `S : Finset ℕ` and
trees on them are `Pattern ↥S`. By the relabeling requirement, the law on any finite labeled tree
is determined by the law on a copy labeled in `ℕ`, so nothing is lost. The empty leaf set `S = ∅`
is included; it carries a single pattern, so its law is forced and adds no constraint. -/
structure TreeTransformation where
  /-- The output distribution `F[T]` for an input `T` on the leaf set `S`. -/
  law : ∀ S : Finset ℕ, Pattern ↥S → PMF (Pattern ↥S)
  /-- Relabeling the input relabels the output distribution. -/
  equivariant : ∀ (S S' : Finset ℕ) (σ : ↥S ≃ ↥S') (T : Pattern ↥S),
    law S' (T.relabel σ) = (law S T).map (Pattern.relabel σ)

end PhyloCSP


