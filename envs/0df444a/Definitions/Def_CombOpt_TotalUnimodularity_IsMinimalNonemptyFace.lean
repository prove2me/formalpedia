-- Prove2me | Definitions.Def_CombOpt_TotalUnimodularity_IsMinimalNonemptyFace
-- name    : CombOpt_TotalUnimodularity_IsMinimalNonemptyFace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:04:53.291471+00:00
-- url     : https://prove2.me/theorems/7ddf1e13-7b2d-4cf6-a736-8912b34f73e1
-- title:
--   Minimal nonempty face of a polyhedron
-- statement:
--   Let $P\subseteq\mathbb R^n$ be a polyhedron. A set $F$ is a **minimal nonempty face** of $P$ if $F$ is a nonempty face of $P$ and no nonempty face of $P$ is a proper subset of $F$; that is, $F$ is minimal by inclusion among the nonempty faces of $P$.
--
--   Minimal nonempty faces are the faces at which a linear objective over $P$ attains its optimum in its "simplest" form; for a pointed polyhedron they are exactly the vertices.
--
--   **Formalization Note** Faces are those of `IsFace` (supporting-hyperplane sections, together with $\emptyset$ and $P$). The empty face is excluded from the comparison, as "minimal nonempty" says.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.2, p. 205 (PDF p. 213)

import Mathlib
import Definitions.Def_CombOpt_TotalUnimodularity_IsFace

namespace CombOpt.TotalUnimodularity

/-- **Minimal nonempty face of a polyhedron.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.2,
p. 205 (PDF p. 213): "The minimal (by inclusion) faces of a polyhedron have a special
structure. … Let F be a minimal nonempty face of P".

`IsMinimalNonemptyFace P F` holds when `F` is a nonempty face of `P` (in the sense of p. 204,
`IsFace`) and no nonempty face of `P` is a proper subset of `F`.

**Formalization Note.** "Minimal" is minimality by inclusion among the *nonempty* faces (the
empty face is excluded, as the book's phrase "minimal nonempty face" says). -/
def IsMinimalNonemptyFace {n : ℕ} (P F : Set (Fin n → ℝ)) : Prop :=
  IsFace P F ∧ F.Nonempty ∧ ∀ G : Set (Fin n → ℝ), IsFace P G → G.Nonempty → G ⊆ F → G = F

end CombOpt.TotalUnimodularity


