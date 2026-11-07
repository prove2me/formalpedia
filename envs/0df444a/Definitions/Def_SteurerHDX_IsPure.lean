-- Prove2me | Definitions.Def_SteurerHDX_IsPure
-- name    : SteurerHDX_IsPure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:30:35.440838+00:00
-- url     : https://prove2.me/theorems/b269396a-8d50-4549-a7dd-fa633492e78d
-- title:
--   Pure $d$-dimensional complex
-- statement:
--   A simplicial complex $\mathcal X$ is a **pure $d$-dimensional complex** if every **facet** (inclusion-maximal face) has exactly $d$ elements:
--   $$\sigma\in\mathcal X \text{ maximal}\ \Longrightarrow\ |\sigma| = d .$$
--   Dimension is cardinality, so a pure $d$-dimensional complex has facets of $d$ vertices; its faces of codimension $2$ have $d-2$ vertices.
--
--   **Formalization Note** The empty collection satisfies the definition vacuously; the theorems that need facets assume $|\mathcal X(d)|\ge 2$.
-- source:
--   Ebrahimnejad–Oveis Gharan, High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture, arXiv:2606.00292, Section 2.2, p.3

import Mathlib
import Definitions.Def_SteurerHDX_IsSimplicialComplex

namespace SteurerHDX

/-- **Pure d-dimensional complex.** Ebrahimnejad–Oveis Gharan, *High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture*, arXiv:2606.00292, Section 2.2, p.3: "The elements of X are called
faces, and the maximal faces are called facets. … A simplicial complex X is a pure d-dimensional
complex if every facet has dimension d."

**Formalization Note.** Dimension = cardinality (footnote 2), so every maximal face (facet) has
exactly `d` elements. The empty collection satisfies the definition vacuously; the theorems that
need facets assume `2 ≤ (faces X d).card`. -/
def IsPure {V : Type*} (X : Finset (Finset V)) (d : ℕ) : Prop :=
  IsSimplicialComplex X ∧ ∀ σ ∈ X, (∀ ρ ∈ X, σ ⊆ ρ → ρ = σ) → σ.card = d

end SteurerHDX


