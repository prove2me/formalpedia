-- Prove2me | Definitions.Def_Menger27_Curves_Ordinary
-- name    : Menger27_Curves_Ordinary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:14:26.930242+00:00
-- url     : https://prove2.me/theorems/31b6d664-b5aa-45b9-a1aa-b8296714ca8e
-- title:
--   p. 101 — gewöhnlich-eindimensionaler Raum
-- statement:
--   A **gewöhnlich-eindimensionaler Raum** is a subset $K$ that is the union of finitely many topological arcs. Distinct arcs meet, if at all, only at endpoints of both arcs:
--   $$K=\bigcup_{i=1}^{m}\gamma_i([0,1]),\qquad \gamma_i([0,1])\cap\gamma_j([0,1])\subseteq\{\gamma_i(0),\gamma_i(1)\}\cap\{\gamma_j(0),\gamma_j(1)\}\quad(i\ne j).$$
--
--   This is the finite arc-complex class to which Satz δ reduces Satz β. The empty union is allowed as the zero-arc case.
-- source:
--   Menger, Zur allgemeinen Kurventheorie, Fund. Math. 10 (1927), p. 101, definition immediately before Satz δ

import Mathlib
import Definitions.Def_Menger27_Curves_Basic

namespace Menger27.Curves

/-- A finite union of arcs, with distinct arcs meeting only at endpoints. -/
def OrdinaryOneDimensional {X : Type*} [TopologicalSpace X]
    (K : Set X) : Prop :=
  ∃ (m : ℕ) (α : Fin m → unitInterval → X),
    K = ⋃ i : Fin m, Set.range (α i) ∧
    (∀ i, IsArc (α i)) ∧
    ∀ i j, i ≠ j →
      Set.range (α i) ∩ Set.range (α j) ⊆
        ({α i 0, α i 1} : Set X) ∩ ({α j 0, α j 1} : Set X)

end Menger27.Curves


