-- Prove2me | Definitions.Def_CombOpt_MatchingPolytope_IsFace
-- name    : CombOpt_MatchingPolytope_IsFace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:14.264543+00:00
-- url     : https://prove2.me/theorems/5f4a6541-3d88-40e7-bafa-c7dab39264b4
-- title:
--   A face of a polyhedron
-- statement:
--   A **face** of a polyhedron $P$ is the intersection $P\cap\{x:\ w^\top x=t\}$ of $P$ with one of its supporting hyperplanes; by convention $\emptyset$ and $P$ itself are also faces.
--
--   **Formalization Note** The space $\mathbb R^n$ is the coordinate space $\mathbb R^\iota$ of functions $\iota\to\mathbb R$ on a finite index type $\iota$ (take $\iota=\{1,\dots,n\}$ for $\mathbb R^n$, or $\iota=E$ for $\mathbb R^E$), and $w^\top x$ is the dot product. The definition is stated for any set $P$; the theorems using it assume that $P$ is a polyhedron.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.2, p. 204 (PDF p. 212)

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_IsSupportingHyperplane

namespace CombOpt.MatchingPolytope

/-- **A face of a polyhedron.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.2, p. 204 (PDF p. 212): "the intersection of a polyhedron with one of its supporting
hyperplanes … we call the intersection a face of the polyhedron. By convention, we also call the
null set and the polyhedron itself faces".

`IsFace P F` says `F = ∅`, or `F = P`, or `F = P ∩ {x | w ⬝ᵥ x = t}` for a supporting hyperplane.

**Formalization Note.** `ℝ^n` is the coordinate space `ι → ℝ` over a finite index type `ι`
(`Fin n` for the book's `ℝ^n`, `E` for `ℝ^E`); `w ⬝ᵥ x` is `w^T x`. The book defines faces of a polyhedron; the definition is stated for any set `P`, and every
theorem using it assumes `IsPolyhedron P`. -/
def IsFace {ι : Type*} [Fintype ι] (P F : Set (ι → ℝ)) : Prop :=
  F = ∅ ∨ F = P ∨ ∃ (w : ι → ℝ) (t : ℝ), IsSupportingHyperplane P w t ∧ F = P ∩ {x | w ⬝ᵥ x = t}

end CombOpt.MatchingPolytope


