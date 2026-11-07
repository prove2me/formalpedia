-- Prove2me | Definitions.Def_SteurerHDX_IsPartite
-- name    : SteurerHDX_IsPartite
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:30:38.231576+00:00
-- url     : https://prove2.me/theorems/1a96a7d8-e3d9-4ca5-8c43-9ed144c6d4cf
-- title:
--   $d$-partite complex
-- statement:
--   A $d$-dimensional complex is **$d$-partite** if its vertices can be partitioned into $d$ parts $P_1,\dots,P_d$ such that every facet has exactly one vertex from each part.
--
--   **Formalization Note** The partition is given by a colouring $c:V\to\{1,\dots,d\}$ (as `Fin d`).
-- source:
--   Ebrahimnejad–Oveis Gharan, High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture, arXiv:2606.00292, Section 2.3, p.4

import Mathlib
import Definitions.Def_SteurerHDX_faces

namespace SteurerHDX

/-- **d-partite complex.** Ebrahimnejad–Oveis Gharan, *High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture*, arXiv:2606.00292, Section 2.3, p.4: "A d-dimensional complex X is d-partite if
its vertices X can be partitioned into d sets, P₁, …, P_d such that every facet has exactly one
vertex from each part."

**Formalization Note.** The partition is a colouring `c : V → Fin d` (part `i` is `c⁻¹(i)`);
every facet has exactly one element of each colour. -/
def IsPartite {V : Type*} (X : Finset (Finset V)) (d : ℕ) : Prop :=
  ∃ c : V → Fin d, ∀ σ ∈ faces X d, ∀ i : Fin d, ∃! x, x ∈ σ ∧ c x = i

end SteurerHDX


