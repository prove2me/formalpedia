-- Prove2me | Definitions.Def_SteurerHDX_skeleton1
-- name    : SteurerHDX_skeleton1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:30:36.852916+00:00
-- url     : https://prove2.me/theorems/f2492a21-26d3-41dd-9bf3-531ea16303e3
-- title:
--   The 1-skeleton of a complex
-- statement:
--   The **1-skeleton** of a complex $\mathcal Y$ is the simple graph with vertex set $\mathcal Y(1)$ and edge set $\mathcal Y(2)$: two distinct vertices $x,y$ are adjacent iff $\{x,y\}\in\mathcal Y$.
--
--   **Formalization Note** The vertices are the singleton faces $\{x\}\in\mathcal Y(1)$; $\{x\}$ and $\{y\}$ are adjacent iff they are distinct and $\{x\}\cup\{y\}\in\mathcal Y$.
-- source:
--   Ebrahimnejad–Oveis Gharan, High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture, arXiv:2606.00292, Definition 2.2, p.3

import Mathlib
import Definitions.Def_SteurerHDX_faces

namespace SteurerHDX

/-- **The 1-skeleton of a complex.** Ebrahimnejad–Oveis Gharan, *High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture*, arXiv:2606.00292, Definition 2.2, p.3: "The 1-skeleton of X_τ is a
simple graph with vertex set X_τ(1) and edge set X_τ(2)."

**Formalization Note.** For a complex `Y` the vertex type is `faces Y 1` (the singleton faces
`{x}`); two distinct singletons `{x}`, `{y}` are adjacent iff `{x} ∪ {y} = {x, y}` is a face of
`Y`, i.e. iff `{x, y} ∈ Y(2)`. -/
def skeleton1 {V : Type*} [DecidableEq V] (Y : Finset (Finset V)) :
    SimpleGraph (faces Y 1) where
  Adj s t := s ≠ t ∧ s.1 ∪ t.1 ∈ Y
  symm := ⟨fun s t h => ⟨h.1.symm, by rw [Finset.union_comm]; exact h.2⟩⟩
  loopless := ⟨fun s h => h.1 rfl⟩

end SteurerHDX


