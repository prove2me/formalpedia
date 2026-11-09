-- Prove2me | Definitions.Def_ManipPotential_IsSpernerLabelling
-- name    : ManipPotential_IsSpernerLabelling
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:43:31.055854+00:00
-- url     : https://prove2.me/theorems/34502318-972f-44a3-9785-8c401f01c075
-- title:
--   Sperner labelling of a triangulation
-- statement:
--   Index the facets of the $d$-simplex $S = \mathrm{conv}\{p_0, \dots, p_d\}$ by $[d+1]$, facet $j$ being the face spanned by the $d$ vertices other than $p_j$. A labelling of the vertices of a triangulation of $S$ by $[d+1]$ is a **Sperner labelling** if, for every $j$, no vertex lying on facet $j$ is labelled $j$.
--
--   **Formalization Note** Facets are indexed by their opposite vertex; any other bijection between facets and labels is obtained by relabelling the $p_j$. The labelling is a function on the ambient space, read on the vertices of the triangulation.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, p.30 (before Lemma 6.8)

import Mathlib

namespace ManipPotential

/-- A Sperner labelling (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, p.30, before Lemma 6.8): for every `j`, no vertex of the
triangulation lying on facet `j` is labelled `j`.

**Formalization Note** Facet `j` is the face of `S` spanned by the `d` vertices other than `p_j`
(facets indexed by the opposite vertex); the labelling is a function `E → Fin (d + 1)` read on the
vertices of `K`. -/
def IsSpernerLabelling {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) {d : ℕ} (p : Fin (d + 1) → E) (lab : E → Fin (d + 1)) :
    Prop :=
  ∀ v ∈ K.vertices, ∀ j : Fin (d + 1), v ∈ convexHull ℝ (p '' {i | i ≠ j}) → lab v ≠ j

end ManipPotential


