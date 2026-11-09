-- Prove2me | Definitions.Def_PhyloCSP_canonRelax
-- name    : PhyloCSP_canonRelax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:25:00.198076+00:00
-- url     : https://prove2.me/theorems/fdba6589-c2cd-4b86-847c-15d40c4cefc5
-- title:
--   The canonical relaxation $\varphi'$
-- statement:
--   The **canonical relaxation** $\varphi'$ of a predicate $\varphi(x_1,\dots,x_k)$ is the conjunction of all split predicates on subsets of $x_1,\dots,x_k$ that are implied by $\varphi$; an empty conjunction is the always-true predicate. In terms of satisfying sets,
--   $$
--   \mathrm{Sat}(\varphi')=\bigl\{P : P\models \mathrm{split}_V(S)\ \text{for every admissible }(S,V)\text{ with }\mathrm{Sat}(\varphi)\subseteq\mathrm{Sat}(\mathrm{split}_V(S))\bigr\}.
--   $$
--
--   The algorithm of the paper solves the relaxed instance (a polynomially tractable CSP) and then applies a random tree transformation; the guarantee $p(\varphi,F)$ is measured over inputs satisfying $\varphi'$.
--
--   **Formalization Note** For the always-false predicate and $k\ge2$ the relaxation is again empty, because the arity-2 split is always false and is implied.
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Definition 5.3, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_PhyloCSP_Predicate
import Definitions.Def_PhyloCSP_splitHolds

set_option autoImplicit false

namespace PhyloCSP

/-- **The canonical relaxation φ′ (Definition 5.3).**

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Definition 5.3, p.13 (PDF p.15): "The canonical relaxation φ′
of φ(x1, . . . , xk) is the conjunction of all split predicates on subsets of x1, . . . , xk that are
implied by φ. An empty conjunction is the always-true predicate."

A pattern satisfies `φ′` iff it satisfies every split predicate (`splitHolds P S V` with
`IsSplitIndex S V`) that every satisfying pattern of `φ` satisfies.

**Formalization Note.** "Implied by φ" is `Sat(φ) ⊆ Sat(split)`. For the always-false predicate
`∅` and `k ≥ 2` the result is `∅` (the arity-2 split is always false and implied); when no split
predicate is implied it is `Set.univ`. -/
def canonRelax {k : ℕ} (φ : Predicate k) : Predicate k :=
  {P | ∀ S V : Finset (Fin k), IsSplitIndex S V → (∀ Q ∈ φ, splitHolds Q S V) → splitHolds P S V}

end PhyloCSP


