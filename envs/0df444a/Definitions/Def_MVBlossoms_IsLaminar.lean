-- Prove2me | Definitions.Def_MVBlossoms_IsLaminar
-- name    : MVBlossoms_IsLaminar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:37:07.010148+00:00
-- url     : https://prove2.me/theorems/d3818b7e-eeda-4cc4-80a2-860c28b96d8b
-- title:
--   Laminar family
-- statement:
--   A family $\mathcal F$ of sets is **laminar** if any two members $X,Y\in\mathcal F$ are disjoint or one contains the other:
--
--   $$
--   X\cap Y=\emptyset \ \text{ or }\ X\subseteq Y\ \text{ or }\ Y\subseteq X .
--   $$
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Corollary 5, p.2037; Theorem 3, Statement 4, p.2034

import Mathlib

namespace MVBlossoms

/-- **Laminar family of sets.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Corollary 5 and Theorem 3, Statement 4 (pp.2034,
2037): a family of sets is laminar when any two of its members are disjoint or one contains the
other. -/
def IsLaminar {α : Type} (F : Set (Set α)) : Prop :=
  ∀ X ∈ F, ∀ Y ∈ F, Disjoint X Y ∨ X ⊆ Y ∨ Y ⊆ X

end MVBlossoms


