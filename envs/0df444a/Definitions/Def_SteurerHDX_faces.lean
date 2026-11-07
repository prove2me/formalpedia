-- Prove2me | Definitions.Def_SteurerHDX_faces
-- name    : SteurerHDX_faces
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:29:42.344427+00:00
-- url     : https://prove2.me/theorems/4af23f9b-7f03-4699-a563-17ee0a224f26
-- title:
--   The faces $\mathcal X(i)$ of dimension $i$ (= cardinality $i$)
-- statement:
--   For a complex $\mathcal X$ and $i\in\mathbb N$,
--   $$\mathcal X(i)=\{\tau\in\mathcal X : |\tau| = i\}.$$
--   In this paper the **dimension** of a face is its number of elements (not the topological dimension $|\tau|-1$). Thus $\mathcal X(1)$ is the vertex set (as singletons) and $\mathcal X(d)$ the set of facets of a pure $d$-dimensional complex.
-- source:
--   Ebrahimnejad–Oveis Gharan, High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture, arXiv:2606.00292, Section 2.2, p.3

import Mathlib

namespace SteurerHDX

/-- **The faces of dimension i, X(i).** Ebrahimnejad–Oveis Gharan, *High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture*, arXiv:2606.00292, Section 2.2, p.3: "We say that a face τ is of
dimension k if |τ| = k" and "X(i) = {τ ∈ X | dim(τ) = i}".

**Formalization Note.** The paper's dimension of a face is its cardinality (footnote 2: this
differs from the topological convention), so `faces X i` is the set of faces with exactly `i`
elements; `faces X 1` is the vertex set X(1) (as singletons) and `faces X d` is the set of
facets X(d) of a pure d-dimensional complex. -/
def faces {V : Type*} (X : Finset (Finset V)) (i : ℕ) : Finset (Finset V) :=
  X.filter (fun τ => τ.card = i)

end SteurerHDX


