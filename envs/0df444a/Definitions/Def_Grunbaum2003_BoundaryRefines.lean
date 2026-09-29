-- Prove2me | Definitions.Def_Grunbaum2003_BoundaryRefines
-- name    : Grunbaum2003_BoundaryRefines
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:38:46.393387+00:00
-- url     : https://prove2.me/theorems/a0769e76-be48-4b3f-9431-05d5525ca012
-- title:
--   Refinement of polytope boundary complexes
-- statement:
--   There is one homeomorphism between the two boundary carriers such that the inverse image of every target face is exactly the union of a finite face-closed subfamily of source boundary faces.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §11.1, refinement definition, printed p. 199 / PDF p. 239; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Definitions.Def_Grunbaum2003_boundaryFaces
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Topology.Homeomorph.Defs

set_option autoImplicit false

namespace Grunbaum2003

/-- The boundary of P refines the boundary of Q, in the precise sense of
p.199 / PDF239. Carriers are unions of cells, with their subspace topology.
Each target face has inverse image equal to a finite union of source faces
closed under taking faces. For polytopes, the intersection and polytopality
conditions of a subcomplex are inherited from the boundary complex.
This local predicate is used only with polytopes; no general complex or
triangulation theory is introduced. -/
def BoundaryRefines {d : ℕ} (P Q : Set (Fin d → ℝ)) : Prop :=
  ∃ ψ : (⋃₀ boundaryFaces P) ≃ₜ (⋃₀ boundaryFaces Q),
    ∀ K ∈ boundaryFaces Q,
      ∃ C : Set (Set (Fin d → ℝ)),
        C.Finite ∧ C ⊆ boundaryFaces P ∧
        (∀ F ∈ C, ∀ G : Set (Fin d → ℝ), IsExposed ℝ F G → G ∈ C) ∧
        ∀ x : (⋃₀ boundaryFaces P), (ψ x).val ∈ K ↔ x.val ∈ ⋃₀ C

end Grunbaum2003


