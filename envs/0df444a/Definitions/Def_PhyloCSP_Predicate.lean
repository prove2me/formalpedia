-- Prove2me | Definitions.Def_PhyloCSP_Predicate
-- name    : PhyloCSP_Predicate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:23:50.264684+00:00
-- url     : https://prove2.me/theorems/5194bb41-4bbe-40fe-8a5e-a6e91c479d41
-- title:
--   Phylogenetic predicates, by their satisfying patterns
-- statement:
--   A phylogenetic predicate $\varphi(x_1,\dots,x_k)$ (Definition 1.1: a Boolean formula in atoms $x_p\mid x_qx_r$; the always-true and always-false predicates are allowed) is identified with its set of satisfying patterns
--   $$
--   \mathrm{Sat}(\varphi)=\{P\in\mathcal P(\{x_1,\dots,x_k\}) : P\text{ satisfies }\varphi\}.
--   $$
--   By the paper, every subset of $\mathcal P(\{x_1,\dots,x_k\})$ arises this way, so a predicate of arity $k$ is simply a set of patterns on $k$ labeled variables.
--
--   **Formalization Note** The variables $x_1,\dots,x_k$ are `Fin k`, so $x_i$ is the index $i-1$. Always-true is the full set and always-false is the empty set.
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Definition 1.1 and the paragraph on Sat(φ), p.1 (PDF p.3)

import Mathlib
import Definitions.Def_PhyloCSP_Pattern

set_option autoImplicit false

namespace PhyloCSP

/-- **Phylogenetic predicates, by their satisfying patterns.**

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Definition 1.1 and the paragraph after it, p.1 (PDF p.3):
"We can characterize a phylogenetic predicate φ(x1, . . . , xk) by its set of satisfying patterns
Sat(φ) = {P ∈ P(S) : P satisfies φ}. … Conversely, every subset of P(S) defines a phylogenetic
predicate".

**Formalization Note.** A predicate of arity `k` is its satisfying set `Sat(φ)`, a set of patterns
on the variables `x₁, …, x_k`, which are `Fin k` (0-based: `xᵢ` is `i - 1`). The always-true and
always-false predicates (allowed by Definition 1.1) are `Set.univ` and `∅`. -/
abbrev Predicate (k : ℕ) : Type := Set (Pattern (Fin k))

end PhyloCSP


