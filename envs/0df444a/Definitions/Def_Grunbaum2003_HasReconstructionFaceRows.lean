-- Prove2me | Definitions.Def_Grunbaum2003_HasReconstructionFaceRows
-- name    : Grunbaum2003_HasReconstructionFaceRows
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T07:04:53.055396+00:00
-- url     : https://prove2.me/theorems/a1c6102c-81c5-4652-a163-ca233d496c8c
-- title:
--   Complete labelled face rows in selected dimensions
-- statement:
--   A duplicate-free row list contains exactly the nonempty exposed faces in the selected dimensions, represented by their labelled vertex sets.
-- source:
--   Expression-essential vertex–face incidence model for Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §12.4 algorithmic reconstruction, printed p. 234a / PDF p. 277; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false

namespace Grunbaum2003

/-- A complete, duplicate-free list of the nonempty faces in the specified
dimensions, recorded by their vertex labels. The theorem separately requires
that `v` enumerates exactly the vertices. For a polytope every face is the
convex hull of its vertices, so subset inclusion recovers the face order.
The empty face is implicit and never encoded as an extra row. -/
def HasReconstructionFaceRows {d n : ℕ} (P : Set (Fin d → ℝ))
    (v : Fin n → Fin d → ℝ) (dimensions : Set ℕ)
    (rows : List (Finset (Fin n))) : Prop :=
  rows.Nodup ∧ ∀ F : Finset (Fin n),
    F ∈ rows ↔ F.Nonempty ∧
      IsExposed ℝ P (convexHull ℝ (v '' (F : Set (Fin n)))) ∧
      Module.finrank ℝ
        (affineSpan ℝ (convexHull ℝ (v '' (F : Set (Fin n))))).direction ∈ dimensions

end Grunbaum2003


